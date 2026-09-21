/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

Finite fiber/Fourier arguments adapted from Lech Mazur, Copyright 2026 Lech Mazur,
under Apache License 2.0. The original LICENSE and NOTICE are retained at
research/sources/mazur_830b9d3f38f2/. This version uses the actual local projection,
explicit Mathlib imports and the pinned module format.
-/
module

public import WordCertDensity.Reference.Projectivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The actual ternary fiber average

The operator divides the sum on the actual projection fiber by its cardinality.
It preserves mass, is positive and contracts the unhalved finite L1 norm.
The reference-law specialization agrees with the existing density oscillation.
-/

@[expose] public section

namespace WordCertDensity
namespace FiniteFourier

open Reference

/-- Average a real vector on its actual ternary projection fiber. -/
noncomputable def fiberAverage {m n : ℕ} (h : m ≤ n)
    (p : ZMod (3 ^ n) → ℝ) (x : ZMod (3 ^ n)) : ℝ :=
  (∑ y ∈ fiber h (project h x), p y) / (3 : ℝ) ^ (n - m)

/-- The projection fibers partition the whole finite group. -/
theorem sum_fibers {m n : ℕ} (h : m ≤ n) (p : ZMod (3 ^ n) → ℝ) :
    (∑ z, ∑ y ∈ fiber h z, p y) = ∑ y, p y := by
  classical
  exact Finset.sum_fiberwise Finset.univ (project h) p

/-- The zero vector averages to zero. -/
@[simp] theorem fiberAverage_zero {m n : ℕ} (h : m ≤ n) (x : ZMod (3 ^ n)) :
    fiberAverage h (fun _ => 0) x = 0 := by
  simp [fiberAverage]

/-- Fiber averaging preserves addition of real vectors. -/
theorem fiberAverage_add {m n : ℕ} (h : m ≤ n) (p q : ZMod (3 ^ n) → ℝ)
    (x : ZMod (3 ^ n)) :
    fiberAverage h (fun y => p y + q y) x = fiberAverage h p x + fiberAverage h q x := by
  simp only [fiberAverage, Finset.sum_add_distrib, add_div]

/-- Fiber averaging preserves subtraction of real vectors. -/
theorem fiberAverage_sub {m n : ℕ} (h : m ≤ n) (p q : ZMod (3 ^ n) → ℝ)
    (x : ZMod (3 ^ n)) :
    fiberAverage h (fun y => p y - q y) x = fiberAverage h p x - fiberAverage h q x := by
  simp only [fiberAverage, Finset.sum_sub_distrib, sub_div]

/-- Fiber averaging preserves multiplication by a real scalar. -/
theorem fiberAverage_mul {m n : ℕ} (h : m ≤ n) (a : ℝ) (p : ZMod (3 ^ n) → ℝ)
    (x : ZMod (3 ^ n)) :
    fiberAverage h (fun y => a * p y) x = a * fiberAverage h p x := by
  simp only [fiberAverage, ← Finset.mul_sum, mul_div_assoc]

/-- Averaging a nonnegative vector is nonnegative at every point. -/
theorem fiberAverage_nonneg {m n : ℕ} (h : m ≤ n) (p : ZMod (3 ^ n) → ℝ)
    (hp : ∀ y, 0 ≤ p y) (x : ZMod (3 ^ n)) : 0 ≤ fiberAverage h p x :=
  div_nonneg (Finset.sum_nonneg fun y _ => hp y) (by positivity)

/-- A vector pulled back from the lower level is fixed by averaging. -/
theorem fiberAverage_project {m n : ℕ} (h : m ≤ n) (p : ZMod (3 ^ m) → ℝ)
    (x : ZMod (3 ^ n)) : fiberAverage h (fun y => p (project h y)) x = p (project h x) := by
  unfold fiberAverage
  have hf : (∑ y ∈ fiber h (project h x), p (project h y)) =
      (3 : ℝ) ^ (n - m) * p (project h x) := by
    calc
      _ = ∑ _y ∈ fiber h (project h x), p (project h x) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [(mem_fiber h _ y).mp hy]
      _ = _ := by simp [card_fiber]
  rw [hf]
  field_simp

/-- Once a vector is constant on every fiber, averaging has no further effect. -/
theorem fiberAverage_idem {m n : ℕ} (h : m ≤ n) (p : ZMod (3 ^ n) → ℝ)
    (x : ZMod (3 ^ n)) : fiberAverage h (fiberAverage h p) x = fiberAverage h p x := by
  exact fiberAverage_project h
    (fun z => (∑ y ∈ fiber h z, p y) / (3 : ℝ) ^ (n - m)) x

/-- Equal-level averaging is the identity, including level zero. -/
@[simp] theorem fiberAverage_self (n : ℕ) (p : ZMod (3 ^ n) → ℝ)
    (x : ZMod (3 ^ n)) : fiberAverage (le_refl n) p x = p x := by
  classical
  simp [fiberAverage, fiber, project_self, Finset.sum_filter]

/-- Averaging preserves the original real total mass. -/
theorem sum_fiberAverage {m n : ℕ} (h : m ≤ n) (p : ZMod (3 ^ n) → ℝ) :
    (∑ x, fiberAverage h p x) = ∑ x, p x := by
  unfold fiberAverage
  rw [sum_project h (fun z => (∑ y ∈ fiber h z, p y) / (3 : ℝ) ^ (n - m))]
  rw [← Finset.sum_div, sum_fibers h]
  field_simp

/-- The absolute value of an average is bounded by the average of absolute values. -/
theorem abs_fiberAverage_le {m n : ℕ} (h : m ≤ n) (p : ZMod (3 ^ n) → ℝ)
    (x : ZMod (3 ^ n)) :
    |fiberAverage h p x| ≤ fiberAverage h (fun y => |p y|) x := by
  unfold fiberAverage
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ (n - m))]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)

/-- The unhalved finite L1 norm contracts under averaging. -/
theorem sum_abs_fiberAverage_le {m n : ℕ} (h : m ≤ n) (p : ZMod (3 ^ n) → ℝ) :
    (∑ x, |fiberAverage h p x|) ≤ ∑ x, |p x| := by
  calc
    _ ≤ ∑ x, fiberAverage h (fun y => |p y|) x :=
      Finset.sum_le_sum fun x _ => abs_fiberAverage_le h p x
    _ = _ := sum_fiberAverage h _

/-- Averaging the actual reference mass gives its uniform lower-level lift. -/
theorem fiberAverage_mass {m n : ℕ} (h : m ≤ n) (x : ZMod (3 ^ n)) :
    fiberAverage h (mass n) x = liftMass h x := by
  simp only [fiberAverage, mass_fiber, liftMass]

/-- The unhalved L1 distance from a vector to its own fiber average. -/
noncomputable def oscillation {m n : ℕ} (h : m ≤ n) (p : ZMod (3 ^ n) → ℝ) : ℝ :=
  ∑ x, |p x - fiberAverage h p x|

/-- Oscillation is nonnegative for every real vector. -/
theorem oscillation_nonneg {m n : ℕ} (h : m ≤ n) (p : ZMod (3 ^ n) → ℝ) :
    0 ≤ oscillation h p := Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The zero vector has zero oscillation. -/
@[simp] theorem oscillation_zero {m n : ℕ} (h : m ≤ n) :
    oscillation h (fun _ => 0) = 0 := by
  simp [oscillation]

/-- Equal levels have zero oscillation for every real vector. -/
@[simp] theorem oscillation_self (n : ℕ) (p : ZMod (3 ^ n) → ℝ) :
    oscillation (le_refl n) p = 0 := by
  simp [oscillation]

/-- Oscillation is subadditive on the original real vectors. -/
theorem oscillation_add_le {m n : ℕ} (h : m ≤ n) (p q : ZMod (3 ^ n) → ℝ) :
    oscillation h (fun x => p x + q x) ≤ oscillation h p + oscillation h q := by
  simp only [oscillation, fiberAverage_add, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  rw [show p x + q x - (fiberAverage h p x + fiberAverage h q x) =
    (p x - fiberAverage h p x) + (q x - fiberAverage h q x) by ring]
  exact abs_add_le _ _

/-- Scaling a vector scales its oscillation by the absolute scalar. -/
theorem oscillation_mul {m n : ℕ} (h : m ≤ n) (a : ℝ) (p : ZMod (3 ^ n) → ℝ) :
    oscillation h (fun x => a * p x) = |a| * oscillation h p := by
  simp only [oscillation, fiberAverage_mul, ← mul_sub, abs_mul, ← Finset.mul_sum]

/-- A nonnegative rejected submass pays at most twice its original mass. -/
theorem oscillation_le_two_mul_sum {m n : ℕ} (h : m ≤ n) (p : ZMod (3 ^ n) → ℝ)
    (hp : ∀ x, 0 ≤ p x) : oscillation h p ≤ 2 * ∑ x, p x := by
  calc
    _ ≤ ∑ x, (p x + fiberAverage h p x) := by
      apply Finset.sum_le_sum
      intro x _
      apply abs_le.mpr
      constructor <;> linarith [hp x, fiberAverage_nonneg h p hp x]
    _ = _ := by rw [Finset.sum_add_distrib, sum_fiberAverage]; ring

/-- Actual reference oscillation equals the existing full-group density L1 error. -/
theorem oscillation_mass {m n : ℕ} (h : m ≤ n) :
    oscillation h (mass n) =
      mean n (fun x => |density n x - density m (project h x)|) := by
  simp only [oscillation, fiberAverage_mass]
  exact (fullL1_eq_sum_mass h).symm

end FiniteFourier
end WordCertDensity
