/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.MassLimit
import WordCertDensity.Counting.Harmonic

/-! # Three-branch extraction from the actual odd-source residue histogram -/

namespace WordCertDensity.Counting

/-- Transfer finite capacity inversion to the cyclic residue group without changing normalization. -/
theorem residue_threeBranch_mass (Q : ℕ) [NeZero Q] (h w : ZMod Q → ℝ)
    (μ V T S B p : ℝ) (hμ : 0 < μ) (hV : 0 < V) (hT : 0 < T)
    (hS : 0 < S) (hB : 0 < B) (hp : 0 ≤ p) (hpaid : p ≤ μ*T)
    (hh : ∀ r, 0 ≤ h r) (hw : ∀ r, 0 ≤ w r) (hcap : ∀ r, w r ≤ T/Q)
    (hmean : (∑ r, h r)/Q = μ) (hvar : (∑ r, (h r-μ)^2)/Q ≤ V)
    (hmax : ∀ r, h r ≤ S) (hmoment : (∑ r, h r^(3/2 : ℝ))/Q ≤ B)
    (hmarked : p ≤ ∑ r, w r*h r) :
    threeBranchMass μ V S B T p ≤ ∑ r, w r := by
  let e : Fin Q ≃ ZMod Q := (ZMod.finEquiv Q).toEquiv
  have hsum (f : ZMod Q → ℝ) : (∑ i, f (e i)) = ∑ r, f r := e.sum_comp f
  have hc := finite_threeBranch_mass Q (fun i => h (e i)) (fun i => w (e i))
    μ V T S B p (Nat.pos_of_ne_zero (NeZero.ne Q)) hμ hV hT hS hB hp hpaid
    (fun i => hh (e i)) (fun i => hw (e i)) (fun i => hcap (e i))
    (by simpa only [hsum] using hmean)
    (by rw [hsum (fun r => (h r-μ)^2)]; exact hvar)
    (fun i => hmax (e i))
    (by rw [hsum (fun r => h r^(3/2 : ℝ))]; exact hmoment)
    (by rw [hsum (fun r => w r*h r)]; exact hmarked)
  simpa only [threeBranchMass, hsum] using hc

/-- Actual physical weights satisfy the joint inverse with the finite modulus boundary retained. -/
theorem physical_threeBranch_mass (Q : ℕ) [NeZero Q] (X R : ℝ)
    (A : Finset ℕ) (a : ℕ → ℝ) (h : ZMod Q → ℝ) (μ V S B p : ℝ)
    (hodd : Odd Q) (hX : 0 < X) (hR : 1 < R)
    (hdata : ∀ x ∈ A, Odd x ∧ X ≤ (x : ℝ) ∧ (x : ℝ) < R*X ∧
      0 ≤ a x ∧ a x ≤ (x : ℝ)⁻¹)
    (hμ : 0 < μ) (hV : 0 < V) (hS : 0 < S) (hB : 0 < B) (hp : 0 ≤ p)
    (hpaid : p ≤ μ*((Q : ℝ)/X+Real.log R/2))
    (hh : ∀ r, 0 ≤ h r) (hmean : (∑ r, h r)/Q = μ)
    (hvar : (∑ r, (h r-μ)^2)/Q ≤ V) (hmax : ∀ r, h r ≤ S)
    (hmoment : (∑ r, h r^(3/2 : ℝ))/Q ≤ B)
    (hmarked : p ≤ ∑ x ∈ A, a x*h (x : ZMod Q)) :
    threeBranchMass μ V S B ((Q : ℝ)/X+Real.log R/2) p ≤ ∑ x ∈ A, a x := by
  classical
  let w : ZMod Q → ℝ := fun r => ∑ x ∈ A.filter (fun x : ℕ => (x : ZMod Q) = r), a x
  have hQ : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have hc := odd_residue_capacity_coefficient Q X R A a hQ hodd hX hR hdata
  have hsum : (∑ r, w r) = ∑ x ∈ A, a x := by
    simpa only [mul_one] using (sum_residue_test A a (fun _ => (1 : ℝ))).symm
  have hmark : p ≤ ∑ r, w r*h r := by
    simpa only [sum_residue_test A a h] using hmarked
  have hT : 0 < (Q : ℝ)/X+Real.log R/2 := by
    have hq : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
    have hl := Real.log_pos hR
    positivity
  have hm := residue_threeBranch_mass Q h w μ V _ S B p hμ hV hT hS hB hp hpaid
    hh (fun r => (hc r).1) (fun r => (hc r).2) hmean hvar hmax hmoment hmark
  simpa only [hsum] using hm

end WordCertDensity.Counting
