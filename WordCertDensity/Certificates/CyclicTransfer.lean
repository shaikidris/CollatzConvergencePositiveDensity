/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.UnitCycle
public import WordCertDensity.Certificates.ReferenceRecursion
public import WordCertDensity.Reference.TransferRecurrence
public import Mathlib.Data.PNat.Equiv

/-! # The cyclic certificate input is the actual compatible reference transfer -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Compatible natural numerators give the same quotient at the lower ternary level. -/
theorem compatible_quotient_congr (n A B : ℕ)
    (h : Nat.ModEq (3 ^ (n + 1)) A B) (hA : A % 3 = 1) (hB : B % 3 = 1) :
    (((A - 1) / 3 : ℕ) : ZMod (3 ^ n)) = (((B - 1) / 3 : ℕ) : ZMod (3 ^ n)) := by
  have ha : 3 * ((A - 1) / 3) + 1 = A := by omega
  have hb : 3 * ((B - 1) / 3) + 1 = B := by omega
  have hc : Nat.ModEq (3 ^ (n + 1)) (3 * ((A - 1) / 3) + 1)
      (3 * ((B - 1) / 3) + 1) := by simpa only [ha, hb] using h
  have hs := Nat.ModEq.add_right_cancel' 1 hc
  rw [pow_succ, mul_comm (3 ^ n) 3] at hs
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (Nat.ModEq.mul_left_cancel' (by decide : 3 ≠ 0) hs)

/-- One-coset input, with the literal natural quotient and zero on the other cosets. -/
noncomputable def compatibleInput (n : ℕ) (f : ZMod (3 ^ n) → ℝ)
    (y : ZMod (3 ^ (n + 1))) : ℝ :=
  if y.val % 3 = 1 then f (((y.val - 1) / 3 : ℕ) : ZMod (3 ^ n)) else 0

/-- Reducing a numerator before its compatible quotient preserves the original transfer input. -/
theorem compatibleInput_mul_two_pow (n a : ℕ) (f : ZMod (3 ^ n) → ℝ)
    (y : ZMod (3 ^ (n + 1))) :
    compatibleInput n f ((2 : ZMod (3 ^ (n + 1))) ^ a * y) =
      if (2 ^ a * y.val) % 3 = 1 then f (Reference.transferInput n y a) else 0 := by
  let z : ZMod (3 ^ (n + 1)) := 2 ^ a * y
  have hc : ((2 ^ a * y.val : ℕ) : ZMod (3 ^ (n + 1))) = z := by
    simp only [z, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_zmod_val]
  have hm : Nat.ModEq (3 ^ (n + 1)) (2 ^ a * y.val) z.val :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (hc.trans (ZMod.natCast_zmod_val z).symm)
  have hd : 3 ∣ 3 ^ (n + 1) := by simpa only [pow_one] using
    (Nat.pow_dvd_pow 3 (show 1 ≤ n + 1 by omega))
  have h3 := hm.of_dvd hd
  change (2 ^ a * y.val) % 3 = z.val % 3 at h3
  change compatibleInput n f z = _
  unfold compatibleInput
  rw [← h3]
  split_ifs with ha
  · congr 1
    exact (compatible_quotient_congr n _ _ hm ha (h3.symm.trans ha)).symm
  · rfl

/-- The cyclic sequence uses the original binary residue powers as its indices. -/
noncomputable def cycleEntry (n : ℕ) (f : ZMod (3 ^ n) → ℝ) (i : ℕ) : ℝ :=
  compatibleInput n f ((2 : ZMod (3 ^ (n + 1))) ^ i)

/-- The exact unit period also preserves the whole cyclic input sequence. -/
theorem cycleEntry_periodic (n : ℕ) (f : ZMod (3 ^ n) → ℝ) (i : ℕ) :
    cycleEntry n f (i + 2 * 3 ^ n) = cycleEntry n f i := by
  unfold cycleEntry
  rw [pow_add, (two_pow_eq_one_iff n _).mpr dvd_rfl, mul_one]

/-- The bounds on an input array hold uniformly around the full binary cycle. -/
theorem cycleEntry_bounds (n : ℕ) (f : ZMod (3 ^ n) → ℝ) (M : ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (i : ℕ) :
    0 ≤ cycleEntry n f i ∧ cycleEntry n f i ≤ M := by
  unfold cycleEntry compatibleInput
  split_ifs
  · exact hf _
  · exact ⟨le_rfl, (hf 0).1.trans (hf 0).2⟩

/-- The complete cyclic convolution equals the actual full-group density at every unit power. -/
theorem cyclic_density_transfer (n i : ℕ) :
    Reference.density (n + 1) ((2 : ZMod (3 ^ (n + 1))) ^ i) =
      3 * cyclicSum (cycleEntry n (Reference.density n)) i := by
  rw [Reference.referenceTransfer]
  let F : ℕ+ → ℝ := fun a =>
    if (2 ^ (a : ℕ) * ((2 : ZMod (3 ^ (n + 1))) ^ i).val) % 3 = 1 then
      (2 : ℝ) ^ (-((a : ℕ) : ℤ)) *
        Reference.density n (Reference.transferInput n ((2 : ZMod (3 ^ (n + 1))) ^ i) a)
    else 0
  change 3 * (∑' a, F a) = _
  rw [← Equiv.pnatEquivNat.symm.tsum_eq F]
  unfold cyclicSum
  congr 1
  apply tsum_congr
  intro j
  change (if (2 ^ (j + 1) * ((2 : ZMod (3 ^ (n + 1))) ^ i).val) % 3 = 1 then
      (2 : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) * Reference.density n
        (Reference.transferInput n ((2 : ZMod (3 ^ (n + 1))) ^ i) (j + 1)) else 0) =
    (2 : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) * cycleEntry n (Reference.density n) (i + j + 1)
  rw [cycleEntry, show (2 : ZMod (3 ^ (n + 1))) ^ (i + j + 1) =
      2 ^ (j + 1) * 2 ^ i by
        rw [show i + j + 1 = (j + 1) + i by omega]
        exact pow_add (2 : ZMod (3 ^ (n + 1))) (j + 1) i,
    compatibleInput_mul_two_pow]
  split_ifs <;> simp only [mul_zero]

end WordCertDensity.Certificates
