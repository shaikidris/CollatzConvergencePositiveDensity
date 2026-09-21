/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

Finite Fourier collision arguments adapted from Lech Mazur, Copyright 2026 Lech Mazur,
under Apache License 2.0. The original LICENSE and NOTICE are retained at
research/sources/mazur_830b9d3f38f2/. This proof uses the actual local fiber average
and the original real vectors, with the manuscript's positive Fourier sign.
-/
module

public import WordCertDensity.Analytic.FiberFourier
public import WordCertDensity.Analytic.Convolution
public import WordCertDensity.Analytic.Parseval
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Ring

/-!
# The finite squared collision bound

No mass-one or nonnegativity hypothesis is imposed on the real vectors.
The squared unhalved L1 error is bounded using the original head second moment.
The final statement uses the manuscript's positive character convention.
-/

@[expose] public section

namespace WordCertDensity
namespace FiniteFourier

/-- The positive finite Fourier sum is Mathlib's negative-sign DFT at the opposite frequency. -/
theorem fourier_positive_eq_dft_neg {N : ℕ} [NeZero N] (p : ZMod N → ℝ) (ξ : ZMod N) :
    (∑ x, (p x : ℂ) * ZMod.stdAddChar (ξ * x)) =
      ZMod.dft (fun x => (p x : ℂ)) (-ξ) := by
  simp only [ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg]
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm ξ x, mul_comm (p x : ℂ)]

/-- The collision bound in the native DFT convention, on the actual local average. -/
theorem oscillation_convolution_sq_le_dft {m n : ℕ} (h : m ≤ n)
    (p t : ZMod (3 ^ n) → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ht : ∀ ξ : ZMod (3 ^ n), ¬ (3 : ZMod (3 ^ n)) ^ (n - m) ∣ ξ →
      ‖ZMod.dft (fun x => (t x : ℂ)) ξ‖ ≤ δ) :
    oscillation h (convolution p t) ^ 2 ≤ δ ^ 2 * (3 : ℝ) ^ n * ∑ x, p x ^ 2 := by
  let d : ZMod (3 ^ n) → ℝ := fun x =>
    convolution p t x - fiberAverage h (convolution p t) x
  have hd (ξ : ZMod (3 ^ n)) :
      ZMod.dft (fun x => (d x : ℂ)) ξ =
        if ((3 ^ m : ℕ) : ZMod (3 ^ n)) * ξ = 0 then 0
          else ZMod.dft (fun x => (p x : ℂ)) ξ * ZMod.dft (fun x => (t x : ℂ)) ξ := by
    simpa only [d, dft_convolution_ofReal] using
      dft_fiberDifference h (convolution p t) ξ
  have hspectral : (∑ ξ, Complex.normSq (ZMod.dft (fun x => (d x : ℂ)) ξ)) ≤
      δ ^ 2 * (3 : ℝ) ^ n * ∑ x, p x ^ 2 := by
    calc
      _ ≤ ∑ ξ, δ ^ 2 * Complex.normSq (ZMod.dft (fun x => (p x : ℂ)) ξ) := by
        apply Finset.sum_le_sum
        intro ξ _
        rw [hd]
        by_cases hret : ((3 ^ m : ℕ) : ZMod (3 ^ n)) * ξ = 0
        · rw [if_pos hret, Complex.normSq_zero]
          exact mul_nonneg (sq_nonneg δ) (Complex.normSq_nonneg _)
        · rw [if_neg hret, Complex.normSq_mul]
          have htξ := ht ξ (mt (retained_frequency_iff h ξ).mpr hret)
          have hsq : Complex.normSq (ZMod.dft (fun x => (t x : ℂ)) ξ) ≤ δ ^ 2 := by
            rw [Complex.normSq_eq_norm_sq]
            exact (sq_le_sq₀ (norm_nonneg _) hδ).2 htξ
          calc
            _ ≤ Complex.normSq (ZMod.dft (fun x => (p x : ℂ)) ξ) * δ ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (Complex.normSq_nonneg _)
            _ = _ := mul_comm _ _
      _ = _ := by
        rw [← Finset.mul_sum, dft_real_normSq_parseval]
        simp only [Nat.cast_pow, Nat.cast_ofNat]
        ring
  have hcauchy : (∑ x, |d x|) ^ 2 ≤ (3 : ℝ) ^ n * ∑ x, d x ^ 2 := by
    simpa [ZMod.card, sq_abs] using
      sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ZMod (3 ^ n))))
        (f := fun x => |d x|)
  have hparseval : (3 : ℝ) ^ n * ∑ x, d x ^ 2 =
      ∑ ξ, Complex.normSq (ZMod.dft (fun x => (d x : ℂ)) ξ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (dft_real_normSq_parseval d).symm
  change (∑ x, |d x|) ^ 2 ≤ _
  exact hcauchy.trans (hparseval.trans_le hspectral)

/-- The manuscript collision estimate with positive Fourier sign and original real second moment. -/
theorem oscillation_convolution_sq_le {m n : ℕ} (h : m ≤ n)
    (p t : ZMod (3 ^ n) → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ht : ∀ ξ : ZMod (3 ^ n), ¬ (3 : ZMod (3 ^ n)) ^ (n - m) ∣ ξ →
      ‖∑ x, (t x : ℂ) * ZMod.stdAddChar (ξ * x)‖ ≤ δ) :
    oscillation h (convolution p t) ^ 2 ≤
      δ ^ 2 * (3 : ℝ) ^ n * ∑ x, |p x| ^ 2 := by
  have ht' (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ^ (n - m) ∣ ξ) :
      ‖ZMod.dft (fun x => (t x : ℂ)) ξ‖ ≤ δ := by
    have hneg : ¬ (3 : ZMod (3 ^ n)) ^ (n - m) ∣ -ξ := by
      simpa only [dvd_neg] using hξ
    simpa only [fourier_positive_eq_dft_neg, neg_neg] using ht (-ξ) hneg
  simpa only [sq_abs] using oscillation_convolution_sq_le_dft h p t hδ ht'

end FiniteFourier
end WordCertDensity
