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
import Mathlib.Tactic.Ring

/-!
# Unnormalized finite convolution

Real submasses and complex Fourier vectors use the same raw finite sum.
There is no factor of the group cardinality in this convolution or its DFT.
The index group includes the one-point case but excludes modulus zero.
-/

@[expose] public section

namespace WordCertDensity

namespace FiniteFourier

/-- Raw finite convolution on a nonzero cyclic group, with no normalization factor. -/
noncomputable def convolution {N : ℕ} [NeZero N] {R : Type*} [CommSemiring R]
    (p t : ZMod N → R) (x : ZMod N) : R := ∑ y, p y * t (x - y)

/-- A zero left vector has zero convolution. -/
theorem convolution_zero_left {N : ℕ} [NeZero N] {R : Type*} [CommSemiring R]
    (t : ZMod N → R) (x : ZMod N) : convolution (fun _ => 0) t x = 0 := by
  simp [convolution]

/-- A zero right vector has zero convolution. -/
theorem convolution_zero_right {N : ℕ} [NeZero N] {R : Type*} [CommSemiring R]
    (p : ZMod N → R) (x : ZMod N) : convolution p (fun _ => 0) x = 0 := by
  simp [convolution]

/-- Convolution of nonnegative real vectors is nonnegative. -/
theorem convolution_nonneg {N : ℕ} [NeZero N] (p t : ZMod N → ℝ)
    (hp : ∀ x, 0 ≤ p x) (ht : ∀ x, 0 ≤ t x) (x : ZMod N) :
    0 ≤ convolution p t x :=
  Finset.sum_nonneg fun y _ => mul_nonneg (hp y) (ht (x - y))

/-- The total mass of a raw convolution is the product of the original masses. -/
theorem sum_convolution {N : ℕ} [NeZero N] {R : Type*} [CommSemiring R]
    (p t : ZMod N → R) : (∑ x, convolution p t x) = (∑ x, p x) * ∑ x, t x := by
  have htranslate (y : ZMod N) : (∑ x, t (x - y)) = ∑ x, t x := by
    exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun _ => rfl)
  simp only [convolution, Finset.sum_comm, ← Finset.mul_sum, htranslate, Finset.sum_mul]

/-- Casting real convolution into the complex numbers preserves the finite sum. -/
theorem convolution_ofReal {N : ℕ} [NeZero N] (p t : ZMod N → ℝ) (x : ZMod N) :
    ((convolution p t x : ℝ) : ℂ) =
      convolution (fun y => (p y : ℂ)) (fun y => (t y : ℂ)) x := by
  simp [convolution]

private noncomputable def kernel {N : ℕ} [NeZero N] (x ξ : ZMod N) : ℂ :=
  ZMod.stdAddChar (-(x * ξ))

private theorem kernel_add {N : ℕ} [NeZero N] (x y ξ : ZMod N) :
    kernel (x + y) ξ = kernel x ξ * kernel y ξ := by
  unfold kernel
  rw [show -((x + y) * ξ) = -(x * ξ) + -(y * ξ) by ring]
  exact AddChar.map_add_eq_mul _ _ _

private theorem convolution_inner_reindex {N : ℕ} [NeZero N]
    (p t : ZMod N → ℂ) (ξ y : ZMod N) :
    (∑ x, kernel x ξ * (p y * t (x - y))) =
      (p y * kernel y ξ) * ∑ z, kernel z ξ * t z := by
  calc
    (∑ x, kernel x ξ * (p y * t (x - y))) =
        ∑ z, kernel (y + z) ξ * (p y * t ((y + z) - y)) := by
          apply Fintype.sum_equiv (Equiv.subRight y)
          intro x
          simp
    _ = ∑ z, (p y * kernel y ξ) * (kernel z ξ * t z) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [kernel_add]
      simp only [add_sub_cancel_left]
      ring
    _ = (p y * kernel y ξ) * ∑ z, kernel z ξ * t z := by rw [Finset.mul_sum]

/-- The unnormalized DFT turns raw finite convolution into a pointwise product. -/
theorem dft_convolution {N : ℕ} [NeZero N] (p t : ZMod N → ℂ) (ξ : ZMod N) :
    ZMod.dft (convolution p t) ξ = ZMod.dft p ξ * ZMod.dft t ξ := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, convolution, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ y, ∑ x, kernel x ξ * (p y * t (x - y))) =
        ∑ y, (p y * kernel y ξ) * ∑ z, kernel z ξ * t z := by
          apply Finset.sum_congr rfl
          intro y _
          exact convolution_inner_reindex p t ξ y
    _ = (∑ y, kernel y ξ * p y) * ∑ z, kernel z ξ * t z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ZMod.dft p ξ * ZMod.dft t ξ := by
      rw [ZMod.dft_apply, ZMod.dft_apply]
      simp only [smul_eq_mul, kernel]

/-- The DFT product identity applies to the original real submass vectors. -/
theorem dft_convolution_ofReal {N : ℕ} [NeZero N]
    (p t : ZMod N → ℝ) (ξ : ZMod N) :
    ZMod.dft (fun x => ((convolution p t x : ℝ) : ℂ)) ξ =
      ZMod.dft (fun x => (p x : ℂ)) ξ * ZMod.dft (fun x => (t x : ℂ)) ξ := by
  have hcast : (fun x => ((convolution p t x : ℝ) : ℂ)) =
      convolution (fun x => (p x : ℂ)) (fun x => (t x : ℂ)) := by
    funext x
    exact convolution_ofReal p t x
  rw [hcast, dft_convolution]

end FiniteFourier

end WordCertDensity
