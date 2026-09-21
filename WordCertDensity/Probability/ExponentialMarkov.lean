/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The raw PMF sum identities and Markov argument are adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The original LICENSE
and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
The local event API uses non-strict thresholds and retains original mass.
-/
module

public import WordCertDensity.Probability.Gated
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

/-!
# Exponential Markov for original PMF events

Nonnegative sums are transported before taking real values. The event
probability is the existing original-mass quantity, without conditioning.
-/

@[expose] public section

namespace WordCertDensity
namespace PMFMoment

open scoped Classical ENNReal

/-- A deterministic map transports every nonnegative PMF sum exactly. -/
theorem sum_map {α β : Type*} (p : PMF α) (f : α → β) (F : β → ℝ≥0∞) :
    (∑' b, (p.map f) b * F b) = ∑' a, p a * F (f a) := by
  simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  rw [tsum_eq_single (f a)]
  · simp
  · intro b hb
    simp [hb]

/-- PMF binding gives an iterated nonnegative expectation without summability hypotheses. -/
theorem sum_bind {α β : Type*} (p : PMF α) (q : α → PMF β) (F : β → ℝ≥0∞) :
    (∑' b, (p.bind q) b * F b) = ∑' a, p a * ∑' b, q a b * F b := by
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  simp_rw [mul_assoc]
  exact ENNReal.tsum_mul_left

end PMFMoment

namespace Gated

open scoped Classical ENNReal

/-- Original event probability is preserved by deterministic pushforward. -/
theorem probability_map {α β : Type*} (p : PMF α) (f : α → β) (G : β → Prop) :
    probability (p.map f) G = probability p (fun a => G (f a)) := by
  unfold probability
  congr 1
  simpa only [mul_ite, mul_one, mul_zero] using
    PMFMoment.sum_map p f (fun b => if G b then 1 else 0)

/-- Events agreeing on the actual support have the same original probability. -/
theorem probability_congr_on_support {α : Type*} (p : PMF α) (G H : α → Prop)
    (h : ∀ a, p a ≠ 0 → (G a ↔ H a)) : probability p G = probability p H := by
  exact le_antisymm
    (probability_mono_on_support p G H (fun a ha => (h a ha).mp))
    (probability_mono_on_support p H G (fun a ha => (h a ha).mpr))

/-- The original probability of a union is at most the sum of its two probabilities. -/
theorem probability_or_le {α : Type*} (p : PMF α) (G H : α → Prop) :
    probability p (fun a => G a ∨ H a) ≤ probability p G + probability p H := by
  have h : (∑' a, if G a ∨ H a then p a else 0) ≤
      (∑' a, if G a then p a else 0) + ∑' a, if H a then p a else 0 := by
    rw [← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro a
    by_cases hG : G a <;> by_cases hH : H a <;> simp [hG, hH]
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨event_ne_top p G, event_ne_top p H⟩) h
  rw [ENNReal.toReal_add (event_ne_top p G) (event_ne_top p H)] at hr
  convert! hr using 1
  unfold probability
  congr 1
  apply tsum_congr
  intro a
  by_cases hG : G a <;> by_cases hH : H a <;> simp [hG, hH]

/-- An exponential moment bounds a non-strict upper tail, including threshold equality. -/
theorem probability_le_exp {α : Type*} (p : PMF α) (X : α → ℝ)
    {t cutoff b : ℝ} (ht : 0 ≤ t)
    (hm : (∑' a, p a * ENNReal.ofReal (Real.exp (t * X a))) ≤ ENNReal.ofReal (Real.exp b)) :
    probability p (fun a => cutoff ≤ X a) ≤ Real.exp (-t * cutoff + b) := by
  have h : (∑' a, if cutoff ≤ X a then p a else 0) *
      ENNReal.ofReal (Real.exp (t * cutoff)) ≤ ENNReal.ofReal (Real.exp b) := by
    apply le_trans _ hm
    rw [← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro a
    by_cases ha : cutoff ≤ X a
    · rw [if_pos ha]
      exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha ht))) _
    · simp [ha]
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at hr
  calc
    probability p (fun a => cutoff ≤ X a) ≤ Real.exp b / Real.exp (t * cutoff) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr hr
    _ = Real.exp (-t * cutoff + b) := by
      rw [← Real.exp_sub]
      congr 1
      ring

end Gated
end WordCertDensity
