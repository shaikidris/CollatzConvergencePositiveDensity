/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.ProfileValue
import WordCertDensity.Counting.Harmonic

/-! # Finite hinge bounds for actual source weights

The modulus boundary remains in the capacity coefficient. The marked lower
bound may be negative; the positive part in the conclusion handles that case.
-/

namespace WordCertDensity.Counting

/-- Every capped residue histogram satisfies the finite hinge bound. -/
theorem residue_hinge_mass (Q : ℕ) [NeZero Q] (h w : ZMod Q → ℝ) (T p t : ℝ)
    (ht : 0 < t) (hw : ∀ r, 0 ≤ w r) (hcap : ∀ r, w r ≤ T / Q)
    (hmarked : p ≤ ∑ r, w r * h r) :
    max (p - T * ((∑ r, max (h r - t) 0) / Q)) 0 / t ≤ ∑ r, w r := by
  let e : Fin Q ≃ ZMod Q := (ZMod.finEquiv Q).toEquiv
  have hsum (f : ZMod Q → ℝ) : (∑ i, f (e i)) = ∑ r, f r := e.sum_comp f
  have hc := feasibleAllocation_hinge Q (fun i => h (e i)) (fun i => w (e i))
    T p t ht ⟨fun i => ⟨hw (e i), hcap (e i)⟩, by
      rw [hsum (fun r => w r * h r)]
      exact hmarked⟩
  have he : (T / (Q : ℝ)) * (∑ r, max (h r - t) 0) =
      T * ((∑ r, max (h r - t) 0) / Q) := by ring
  rw [hsum (fun r => max (h r - t) 0), hsum w, he] at hc
  exact hc

/-- Odd physical sources retain the exact finite harmonic capacity in the hinge bound. -/
theorem physical_hinge_mass (Q : ℕ) [NeZero Q] (X R : ℝ)
    (A : Finset ℕ) (a : ℕ → ℝ) (h : ZMod Q → ℝ) (p t : ℝ)
    (hodd : Odd Q) (hX : 0 < X) (hR : 1 < R)
    (hdata : ∀ x ∈ A, Odd x ∧ X ≤ (x : ℝ) ∧ (x : ℝ) < R * X ∧
      0 ≤ a x ∧ a x ≤ (x : ℝ)⁻¹)
    (ht : 0 < t) (hmarked : p ≤ ∑ x ∈ A, a x * h (x : ZMod Q)) :
    max (p - ((Q : ℝ) / X + Real.log R / 2) *
      ((∑ r, max (h r - t) 0) / Q)) 0 / t ≤ ∑ x ∈ A, a x := by
  classical
  let w : ZMod Q → ℝ := fun r => ∑ x ∈ A.filter (fun x : ℕ => (x : ZMod Q) = r), a x
  have hc := odd_residue_capacity_coefficient Q X R A a
    (Nat.pos_of_ne_zero (NeZero.ne Q)) hodd hX hR hdata
  have hsum : (∑ r, w r) = ∑ x ∈ A, a x := by
    simpa only [mul_one] using (sum_residue_test A a (fun _ => (1 : ℝ))).symm
  have hmark : p ≤ ∑ r, w r * h r := by
    simpa only [sum_residue_test A a h] using hmarked
  have hb := residue_hinge_mass Q h w ((Q : ℝ) / X + Real.log R / 2) p t ht
    (fun r => (hc r).1) (fun r => (hc r).2) hmark
  simpa only [hsum] using hb

end WordCertDensity.Counting
