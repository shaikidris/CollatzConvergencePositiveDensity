/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sharp capacity of a finite set in one residue class

Taking the quotient by the modulus is injective inside a residue class.
The interval count retains one point, even if the affine offset window has
zero width. Physical word histories will supply the affine inputs per tag.
-/

@[expose] public section

namespace WordCertDensity.Transfer

/-- Quotients distinguish natural numbers with the same remainder. -/
theorem residue_quotient_injOn (s : Finset ℕ) (N r : ℕ)
    (hres : ∀ x ∈ s, x % N = r) : Set.InjOn (fun x => x / N) (s : Set ℕ) := by
  intro x hx y hy hxy
  change x / N = y / N at hxy
  have hx' := Nat.mod_add_div x N
  have hy' := Nat.mod_add_div y N
  rw [hres x hx] at hx'
  rw [hres y hy, ← hxy] at hy'
  omega

/-- One residue class has at most one point plus its quotient span. -/
theorem residue_card_span (s : Finset ℕ) (hs : s.Nonempty) (N r : ℕ)
    (hres : ∀ x ∈ s, x % N = r) :
    s.card * N + s.min' hs ≤ N + s.max' hs := by
  have hsub : s.image (fun x => x / N) ⊆
      Finset.Icc (s.min' hs / N) (s.max' hs / N) := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_Icc.mpr
      ⟨Nat.div_le_div_right (s.min'_le x hx), Nat.div_le_div_right (s.le_max' x hx)⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (residue_quotient_injOn s N r hres), Nat.card_Icc] at hcard
  have hquot : s.min' hs / N ≤ s.max' hs / N :=
    Nat.div_le_div_right (s.min'_le_max' hs)
  have hc : s.card + s.min' hs / N ≤ s.max' hs / N + 1 := by omega
  have hpaid := Nat.mul_le_mul_right N hc
  have hmin := Nat.mod_add_div (s.min' hs) N
  have hmax := Nat.mod_add_div (s.max' hs) N
  rw [hres _ (s.min'_mem hs)] at hmin
  rw [hres _ (s.max'_mem hs)] at hmax
  nlinarith

/-- The sharp weighted count pays the offset width and one residual point. -/
theorem residue_weight_capacity (s : Finset ℕ) (N r : ℕ) {omega sigma C : ℝ}
    (hres : ∀ x ∈ s, x % N = r) (homega : 0 ≤ omega) (hsigma : omega ≤ sigma)
    (hC : 0 ≤ C) (hwindow : ∀ x ∈ s, ∀ y ∈ s, omega * ((x : ℝ) - y) ≤ C) :
    (N : ℝ) * s.card * omega ≤ C + (N : ℝ) * sigma := by
  by_cases hs : s.Nonempty
  · have hspan : (s.card : ℝ) * N + (s.min' hs : ℝ) ≤
        (N : ℝ) + (s.max' hs : ℝ) := by
      exact_mod_cast residue_card_span s hs N r hres
    have hw := hwindow _ (s.max'_mem hs) _ (s.min'_mem hs)
    calc
      (N : ℝ) * s.card * omega = omega * ((s.card : ℝ) * N) := by ring
      _ ≤ omega * ((N : ℝ) + (s.max' hs : ℝ) - (s.min' hs : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) homega
      _ = omega * N + omega * ((s.max' hs : ℝ) - (s.min' hs : ℝ)) := by ring
      _ ≤ sigma * N + C :=
        add_le_add (mul_le_mul_of_nonneg_right hsigma (by positivity)) hw
      _ = C + (N : ℝ) * sigma := by ring
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hsigma0 : 0 ≤ sigma := homega.trans hsigma
    simp only [he, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul]
    positivity

/-- The same count applies to distinctly indexed sources in a finite family. -/
theorem residue_family_capacity {α : Type*} (s : Finset α) (source : α → ℕ)
    (N r : ℕ) {omega sigma C : ℝ}
    (hinj : Set.InjOn source (s : Set α)) (hres : ∀ i ∈ s, source i % N = r)
    (homega : 0 ≤ omega) (hsigma : omega ≤ sigma) (hC : 0 ≤ C)
    (hwindow : ∀ i ∈ s, ∀ j ∈ s, omega * ((source i : ℝ) - source j) ≤ C) :
    (N : ℝ) * s.card * omega ≤ C + (N : ℝ) * sigma := by
  have hr : ∀ x ∈ s.image source, x % N = r := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hres i hi
  have hw : ∀ x ∈ s.image source, ∀ y ∈ s.image source,
      omega * ((x : ℝ) - y) ≤ C := by
    intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact hwindow i hi j hj
  have h := residue_weight_capacity (s.image source) N r hr homega hsigma hC hw
  simpa only [Finset.card_image_of_injOn hinj] using h

/-- An affine offset window supplies the exact one-tag weighted capacity. -/
theorem affine_family_capacity {α : Type*} (s : Finset α) (source : α → ℕ)
    (offset : α → ℝ) (N r : ℕ) {omega sigma M cmin cmax : ℝ}
    (hinj : Set.InjOn source (s : Set α)) (hres : ∀ i ∈ s, source i % N = r)
    (homega : 0 ≤ omega) (hsigma : omega ≤ sigma) (horder : cmin ≤ cmax)
    (haffine : ∀ i ∈ s, M = omega * source i + offset i)
    (hoffset : ∀ i ∈ s, cmin ≤ offset i ∧ offset i ≤ cmax) :
    (N : ℝ) * s.card * omega ≤ (cmax - cmin) + (N : ℝ) * sigma := by
  apply residue_family_capacity s source N r hinj hres homega hsigma (sub_nonneg.mpr horder)
  intro i hi j hj
  have hi' := haffine i hi
  have hj' := haffine j hj
  have hbi := hoffset i hi
  have hbj := hoffset j hj
  nlinarith

end WordCertDensity.Transfer
