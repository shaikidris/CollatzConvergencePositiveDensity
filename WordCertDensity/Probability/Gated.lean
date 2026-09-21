/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The option-valued gate construction is adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The original LICENSE
and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
Finite partitions below are proved directly on the original ENNReal sums.
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Original probability mass selected by a gate

Rejected outcomes are retained as `none`. Disjoint gates partition the
original PMF without any normalization by acceptance probability.
-/

@[expose] public section

namespace WordCertDensity
namespace Gated

open scoped Classical ENNReal

/-- The original outcome on acceptance, with a separate rejection outcome. -/
noncomputable def key {α β : Type*} (G : α → Prop) (f : α → β) (a : α) : Option β :=
  if G a then some (f a) else none

/-- Pushforward of the original PMF, retaining rejected outcomes. -/
noncomputable def law {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β) : PMF (Option β) :=
  p.map (key G f)

/-- Accepted real mass at a specified output. -/
noncomputable def mass {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β) (y : β) : ℝ :=
  (law p G f (some y)).toReal

/-- Probability of an event under the original PMF. -/
noncomputable def probability {α : Type*} (p : PMF α) (G : α → Prop) : ℝ :=
  (∑' a, if G a then p a else 0).toReal

/-- The accepted option atom is the exact gated sum over source atoms. -/
theorem law_some_apply {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β) (y : β) :
    law p G f (some y) = ∑' a, if G a ∧ f a = y then p a else 0 := by
  rw [law, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases h : G a <;> simp [key, h, eq_comm]

/-- A gated original event always has finite ENNReal probability. -/
theorem event_ne_top {α : Type*} (p : PMF α) (G : α → Prop) :
    (∑' a, if G a then p a else 0) ≠ ⊤ := by
  have h : (∑' a, if G a then p a else 0) ≤ 1 := by
    calc
      _ ≤ ∑' a, p a := ENNReal.tsum_le_tsum (fun a => by split_ifs <;> simp)
      _ = 1 := p.tsum_coe
  exact ne_of_lt (h.trans_lt (by simp))

/-- Only implications on the actual support are needed for event probability monotonicity. -/
theorem probability_mono_on_support {α : Type*} (p : PMF α) (G H : α → Prop)
    (h : ∀ a, p a ≠ 0 → G a → H a) : probability p G ≤ probability p H := by
  apply ENNReal.toReal_mono (event_ne_top p H)
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases hp : p a = 0
  · simp [hp]
  · by_cases hG : G a
    · simp [hG, h a hp hG]
    · simp [hG]

/-- Accepted real mass is nonnegative. -/
theorem mass_nonneg {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β) (y : β) :
    0 ≤ mass p G f y := ENNReal.toReal_nonneg

private theorem tsum_sum {α ι : Type*} [Fintype ι] (f : α → ι → ℝ≥0∞) :
    (∑' a, ∑ i, f a i) = ∑ i, ∑' a, f a i := by
  calc
    _ = ∑' a, ∑' i, f a i := tsum_congr (fun a => (tsum_fintype (fun i => f a i)).symm)
    _ = ∑' i, ∑' a, f a i := ENNReal.tsum_comm
    _ = _ := tsum_fintype _

/-- Summing accepted output masses recovers the original event probability. -/
theorem mass_sum {α β : Type*} [Fintype β] (p : PMF α) (G : α → Prop) (f : α → β) :
    (∑ y, mass p G f y) = probability p G := by
  have h : (∑ y, law p G f (some y)) = ∑' a, if G a then p a else 0 := by
    simp_rw [law_some_apply]
    rw [← tsum_sum]
    apply tsum_congr
    intro a
    by_cases hG : G a <;> simp [hG]
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun y _ => PMF.apply_ne_top _ _)] at hr
  exact hr

/-- A gate and its complement recover every original pushed-forward atom. -/
theorem mass_add_compl {α β : Type*} (p : PMF α) (G : α → Prop) (f : α → β) (y : β) :
    mass p G f y + mass p (fun a => ¬ G a) f y = ((p.map f) y).toReal := by
  have h : law p G f (some y) + law p (fun a => ¬ G a) f (some y) = (p.map f) y := by
    rw [law_some_apply, law_some_apply, PMF.map_apply, ← ENNReal.tsum_add]
    apply tsum_congr
    intro a
    by_cases hG : G a <;> simp [hG, eq_comm]
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)] at hr
  exact hr

/-- A finite family of disjoint gates partitions the original accepted mass exactly. -/
theorem mass_union {α β ι : Type*} [Fintype ι] (p : PMF α)
    (G : ι → α → Prop) (f : α → β)
    (hunique : ∀ i j a, G i a → G j a → i = j) (y : β) :
    mass p (fun a => ∃ i, G i a) f y = ∑ i, mass p (G i) f y := by
  classical
  have hp (a : α) :
      (if (∃ i, G i a) ∧ f a = y then p a else 0) =
        ∑ i, if G i a ∧ f a = y then p a else 0 := by
    by_cases hf : f a = y
    · by_cases hG : ∃ i, G i a
      · obtain ⟨i, hi⟩ := hG
        rw [if_pos ⟨⟨i, hi⟩, hf⟩, Finset.sum_eq_single i]
        · simp [hi, hf]
        · intro j _ hji
          exact if_neg (fun hj => hji (hunique j i a hj.1 hi))
        · simp
      · have hn (i : ι) : ¬ G i a := fun hi => hG ⟨i, hi⟩
        simp [hn]
    · simp [hf]
  have h : law p (fun a => ∃ i, G i a) f (some y) = ∑ i, law p (G i) f (some y) := by
    simp_rw [law_some_apply]
    calc
      _ = ∑' a, ∑ i, if G i a ∧ f a = y then p a else 0 := by
        apply tsum_congr
        intro a
        by_cases hf : f a = y
        · by_cases hg : ∃ i, G i a <;> simpa [hg, hf] using hp a
        · simp [hf]
      _ = _ := tsum_sum _
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun i _ => PMF.apply_ne_top _ _)] at hr
  exact hr

end Gated
end WordCertDensity
