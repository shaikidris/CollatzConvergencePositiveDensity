/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Probability.ExponentialMarkov

/-! # Finite unions of original PMF events -/

@[expose] public section

namespace WordCertDensity
namespace Gated

/-- Original event probability is subadditive over any finite family, with overlaps allowed. -/
theorem probability_biUnion_le {α ι : Type*} (p : PMF α) (s : Finset ι) (G : ι → α → Prop) :
    probability p (fun a => ∃ i ∈ s, G i a) ≤ ∑ i ∈ s, probability p (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [probability]
  | @insert i s hi ih =>
      have he := probability_congr_on_support p
        (fun a => ∃ j ∈ insert i s, G j a)
        (fun a => G i a ∨ ∃ j ∈ s, G j a) (fun a _ => by simp)
      rw [he, Finset.sum_insert hi]
      exact (probability_or_le p (G i) (fun a => ∃ j ∈ s, G j a)).trans
        (add_le_add le_rfl ih)

/-- Every original PMF event has probability at most one. -/
theorem probability_le_one {α : Type*} (p : PMF α) (G : α → Prop) :
    probability p G ≤ 1 := by
  have h := probability_mono_on_support p G (fun _ => True) (fun _ _ _ => trivial)
  simpa [probability, p.tsum_coe] using h

/-- A finite disjoint family has exactly the sum of its original probabilities. -/
theorem probability_union {α ι : Type*} [Fintype ι] (p : PMF α)
    (G : ι → α → Prop) (hunique : ∀ i j a, G i a → G j a → i = j) :
    probability p (fun a => ∃ i, G i a) = ∑ i, probability p (G i) := by
  have hmass (H : α → Prop) : mass p H (fun _ => ()) () = probability p H := by
    simpa using mass_sum p H (fun _ => ())
  simpa only [hmass] using mass_union p G (fun _ => ()) hunique ()

/-- Rejected probability is the exact complement of the original selected mass. -/
theorem probability_compl {α : Type*} (p : PMF α) (G : α → Prop) :
    probability p (fun a => ¬ G a) = 1 - probability p G := by
  have hmass (H : α → Prop) : mass p H (fun _ => ()) () = probability p H := by
    simpa using mass_sum p H (fun _ => ())
  have h := mass_add_compl p G (fun _ => ()) ()
  rw [hmass, hmass] at h
  have hunit : ((p.map (fun _ => ())) ()).toReal = 1 := by simp
  rw [hunit] at h
  linarith

end Gated
end WordCertDensity
