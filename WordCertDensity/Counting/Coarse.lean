/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.Harmonic
import WordCertDensity.Reference.FanMixing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Finite coarse-fan replacement on actual physical source weights -/

namespace WordCertDensity.Counting

open scoped BigOperators

/-- The finite source replacement pays both the full mean discrepancy and modulus boundary. -/
theorem coarse_fan_mass (m k : ℕ) (X R : ℝ) (S : Finset ℕ) (a : ℕ → ℝ)
    (hm : 2 ≤ m) (hmk : m ≤ k) (hX : 0 < X) (hR : 1 < R)
    (hdata : ∀ x ∈ S, Odd x ∧ X ≤ (x : ℝ) ∧ (x : ℝ) < R * X ∧
      0 ≤ a x ∧ a x ≤ (x : ℝ)⁻¹) :
    (∑ x ∈ S, a x * Reference.fan k (x : ZMod (3 ^ k))) ≤
      (∑ x ∈ S, a x * Reference.fan m (x : ZMod (3 ^ m))) +
        (8 / 9 : ℝ) * ((3 : ℝ) ^ k / X + Real.log R / 2) * Analytic.mixingError m := by
  classical
  let ψ : ZMod (3 ^ k) → ℝ := fun x =>
    |Reference.fan k x - Reference.fan m (Reference.project hmk x)|
  have htest := odd_harmonic_test (3 ^ k) X R S a (by positivity)
    ((by decide : Odd (3 : ℕ)).pow (n := k)) hX hR hdata ψ (fun x => abs_nonneg _)
  have hT : 0 ≤ (3 : ℝ) ^ k / X + Real.log R / 2 :=
    add_nonneg (div_nonneg (by positivity) hX.le)
      (div_nonneg (Real.log_nonneg hR.le) (by norm_num))
  have hcost : (∑ x ∈ S, a x * ψ (x : ZMod (3 ^ k))) ≤
      (8 / 9 : ℝ) * ((3 : ℝ) ^ k / X + Real.log R / 2) * Analytic.mixingError m := by
    calc
      _ ≤ ((3 : ℝ) ^ k / X + Real.log R / 2) * Reference.mean k ψ := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat, Reference.mean] using htest
      _ ≤ ((3 : ℝ) ^ k / X + Real.log R / 2) * ((8 / 9 : ℝ) * Analytic.mixingError m) :=
        mul_le_mul_of_nonneg_left (Reference.fan_mean_le_mixingError (by omega) hmk) hT
      _ = _ := by ring
  have hpoint (x : ℕ) (hx : x ∈ S) :
      a x * Reference.fan k (x : ZMod (3 ^ k)) ≤
        a x * Reference.fan m (x : ZMod (3 ^ m)) + a x * ψ (x : ZMod (3 ^ k)) := by
    have he : Reference.fan k (x : ZMod (3 ^ k)) ≤
        Reference.fan m (x : ZMod (3 ^ m)) + ψ (x : ZMod (3 ^ k)) := by
      dsimp [ψ]
      rw [Reference.project_natCast]
      linarith [le_abs_self (Reference.fan k (x : ZMod (3 ^ k)) -
        Reference.fan m (x : ZMod (3 ^ m)))]
    simpa only [mul_add] using mul_le_mul_of_nonneg_left he (hdata x hx).2.2.2.1
  calc
    _ ≤ ∑ x ∈ S, (a x * Reference.fan m (x : ZMod (3 ^ m)) +
        a x * ψ (x : ZMod (3 ^ k))) := Finset.sum_le_sum hpoint
    _ = (∑ x ∈ S, a x * Reference.fan m (x : ZMod (3 ^ m))) +
        ∑ x ∈ S, a x * ψ (x : ZMod (3 ^ k)) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add le_rfl hcost

end WordCertDensity.Counting
