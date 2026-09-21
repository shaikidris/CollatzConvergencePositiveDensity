/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.StoppedTail
import Mathlib.Tactic

/-! # Prefix-weighted original-law tail factorization

Weights depend only on the selected prefix. The double-sum statement remains
valid for arbitrary bounded prefix families; prefix-freeness is needed when
identifying that sum with the weight of a unique stopping prefix.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- Retain any nonnegative prefix weight through original-law factorization. -/
theorem weightedStoppedTail_factor (S : Set ValuationWord) (N : ℕ)
    (a : S → ℝ≥0∞) (B : ValuationWord → ValuationWord → Prop)
    (hlen : ∀ u ∈ S, u.length ≤ N) :
    (∑' w : ValuationWord, ∑' u : S,
      if (u : ValuationWord) <+: w ∧ B u (w.drop (u : ValuationWord).length)
      then a u * Reference.wordPMF N w else 0) =
    ∑' u : S, a u * Reference.wordPMF (u : ValuationWord).length u *
      ∑' v : ValuationWord,
        if B u v then Reference.wordPMF (N - (u : ValuationWord).length) v else 0 := by
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro u
  have he : (∑' w : ValuationWord,
      if (u : ValuationWord) <+: w ∧ B u (w.drop (u : ValuationWord).length)
      then a u * Reference.wordPMF N w else 0) =
      a u * ∑' w : ValuationWord,
        if (u : ValuationWord) <+: w ∧ B u (w.drop (u : ValuationWord).length)
        then Reference.wordPMF N w else 0 := by
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro w
    split_ifs <;> simp
  rw [he, prefix_tail_eventMass u N (hlen u u.property) (B u), mul_assoc]

/-- Split a two-valued discount into its selected and complementary masses. -/
theorem tsum_discount_split {α : Type*} (m : α → ℝ≥0∞) (P : α → Prop) (z : ℝ≥0∞) :
    (∑' x, m x * (if P x then z else 1)) =
      z * (∑' x, if P x then m x else 0) + (∑' x, if ¬ P x then m x else 0) := by
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply tsum_congr
  intro x
  by_cases hx : P x <;> simp [hx, mul_comm]

/-- The literal discounted source mass factors at a prescribed prefix. -/
theorem prefix_tail_discount_factor (u : ValuationWord) (N : ℕ)
    (hu : u.length ≤ N) (B : ValuationWord → Prop) (z : ℝ≥0∞) :
    (∑' w : ValuationWord, if u <+: w then
      Reference.wordPMF N w * (if B (w.drop u.length) then z else 1) else 0) =
    Reference.wordPMF u.length u *
      ∑' v : ValuationWord, Reference.wordPMF (N - u.length) v * (if B v then z else 1) := by
  have he : (∑' w : ValuationWord, if u <+: w then
      Reference.wordPMF N w * (if B (w.drop u.length) then z else 1) else 0) =
      z * (∑' w : ValuationWord,
        if u <+: w ∧ B (w.drop u.length) then Reference.wordPMF N w else 0) +
      (∑' w : ValuationWord,
        if u <+: w ∧ ¬ B (w.drop u.length) then Reference.wordPMF N w else 0) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    apply tsum_congr
    intro w
    by_cases hp : u <+: w <;> by_cases hb : B (w.drop u.length) <;> simp [hp, hb, mul_comm]
  rw [he, prefix_tail_eventMass u N hu B, tsum_discount_split]
  have hc := prefix_tail_eventMass u N hu (fun v => ¬ B v)
  have hnot (P : Prop) (x y : ℝ≥0∞) :
      @ite ℝ≥0∞ (¬ P) (Classical.propDecidable _) x y = if P then y else x := by
    by_cases hp : P <;> simp [hp]
  simp only [ite_and, hnot, ite_not] at hc ⊢
  rw [hc]
  ring

/-- Prefix weights and the literal tail discount both survive the stopping
decomposition under the common original law. -/
theorem weightedStoppedDiscount_factor (S : Set ValuationWord) (N : ℕ)
    (a : S → ℝ≥0∞) (B : ValuationWord → ValuationWord → Prop) (z : ℝ≥0∞)
    (hlen : ∀ u ∈ S, u.length ≤ N) :
    (∑' w : ValuationWord, ∑' u : S, if (u : ValuationWord) <+: w then
      a u * (Reference.wordPMF N w *
        (if B u (w.drop (u : ValuationWord).length) then z else 1)) else 0) =
    ∑' u : S, a u * Reference.wordPMF (u : ValuationWord).length u *
      ∑' v : ValuationWord, Reference.wordPMF (N - (u : ValuationWord).length) v *
        (if B u v then z else 1) := by
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro u
  rw [mul_assoc, ← prefix_tail_discount_factor u N (hlen u u.property) (B u) z,
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro w
  by_cases hp : (u : ValuationWord) <+: w <;> simp [hp]

end WordCertDensity.LocalPrimitive
