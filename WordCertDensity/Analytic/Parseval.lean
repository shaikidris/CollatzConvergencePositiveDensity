/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

Finite Fourier arguments adapted from Lech Mazur, Copyright 2026 Lech Mazur,
under Apache License 2.0. The original LICENSE and NOTICE are retained at
research/sources/mazur_830b9d3f38f2/. This version uses the local finite API,
explicit Mathlib imports and the pinned module format.
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Finite Parseval identities in probability-mass normalization

The DFT has no factor of the group cardinality. Its squared norm is therefore
multiplied by that cardinality. Real-vector specializations keep the exact
second moment consumed by the finite collision bound.
-/

@[expose] public section

open scoped ComplexConjugate

namespace WordCertDensity

namespace FiniteFourier

/-- Opposite Fourier frequencies give the finite bilinear Parseval identity. -/
theorem dft_bilinear_parseval
    {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    (∑ k : ZMod N, ZMod.dft f k * ZMod.dft g (-k)) =
      (N : ℂ) * ∑ x : ZMod N, f x * g x := by
  calc
    (∑ k : ZMod N, ZMod.dft f k * ZMod.dft g (-k)) =
      ∑ k : ZMod N, ZMod.dft f k *
        (∑ x : ZMod N,
          ZMod.stdAddChar (-(x * (-k))) * g x) := by
            apply Finset.sum_congr rfl
            intro k _hk
            congr 1
    _ = ∑ k : ZMod N, ∑ x : ZMod N,
        ZMod.dft f k *
          (ZMod.stdAddChar (-(x * (-k))) * g x) := by
            simp only [Finset.mul_sum]
    _ = ∑ x : ZMod N, ∑ k : ZMod N,
        ZMod.dft f k *
          (ZMod.stdAddChar (-(x * (-k))) * g x) := by
            rw [Finset.sum_comm]
    _ = ∑ x : ZMod N,
        ZMod.dft (ZMod.dft f) (-x) * g x := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [ZMod.dft_apply]
            simp only [smul_eq_mul, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _hk
            have hphase : -(x * (-k)) = -(k * (-x)) := by ring
            rw [hphase]
            ring
    _ = ∑ x : ZMod N, ((N : ℂ) * f x) * g x := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [congrFun (ZMod.dft_dft f) (-x)]
            simp [smul_eq_mul]
    _ = (N : ℂ) * ∑ x : ZMod N, f x * g x := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _hx
            ring

private theorem conj_stdAddChar_neg
    {N : ℕ} [NeZero N] (x : ZMod N) :
    conj (ZMod.stdAddChar (-x)) = ZMod.stdAddChar x := by
  change conj ((ZMod.toCircle (-x) : Circle) : ℂ) =
    ((ZMod.toCircle x : Circle) : ℂ)
  rw [show ZMod.toCircle (-x) = (ZMod.toCircle x)⁻¹ by
    exact AddChar.map_neg_eq_inv (ZMod.toCircle (N := N)) x]
  rw [Circle.coe_inv_eq_conj]
  simp

/-- Complex conjugation of a vector conjugates its DFT at the opposite frequency. -/
theorem dft_conj_apply_neg
    {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun x => conj (f x)) (-k) =
      conj (ZMod.dft f k) := by
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp only [smul_eq_mul, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro x _hx
  have hphase : -(x * (-k)) = -(-(x * k)) := by ring
  rw [hphase, conj_stdAddChar_neg]
  simp only [neg_neg]

/-- The unnormalized DFT multiplies the squared Euclidean norm by the group size. -/
theorem dft_norm_sq_parseval
    {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    (∑ k : ZMod N, ‖ZMod.dft f k‖ ^ 2) =
      (N : ℝ) * ∑ x : ZMod N, ‖f x‖ ^ 2 := by
  have h := dft_bilinear_parseval f (fun x => conj (f x))
  simp_rw [dft_conj_apply_neg] at h
  have hcomplex :
      (((∑ k : ZMod N, ‖ZMod.dft f k‖ ^ 2) : ℝ) : ℂ) =
        (((N : ℝ) * ∑ x : ZMod N, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    simpa [Complex.mul_conj'] using h
  exact_mod_cast hcomplex

/-- Parseval expressed with the algebraic complex squared norm. -/
theorem dft_normSq_parseval
    {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    (∑ k : ZMod N, Complex.normSq (ZMod.dft f k)) =
      (N : ℝ) * ∑ x : ZMod N, Complex.normSq (f x) := by
  simpa [Complex.normSq_eq_norm_sq] using dft_norm_sq_parseval f


/-- Real submasses have the exact finite second-moment normalization used in collision bounds. -/
theorem dft_real_normSq_parseval {N : ℕ} [NeZero N] (p : ZMod N → ℝ) :
    (∑ ξ, Complex.normSq (ZMod.dft (fun x => (p x : ℂ)) ξ)) =
      (N : ℝ) * ∑ x, p x ^ 2 := by
  simpa only [Complex.normSq_ofReal, pow_two] using
    dft_normSq_parseval (fun x => (p x : ℂ))

end FiniteFourier

end WordCertDensity
