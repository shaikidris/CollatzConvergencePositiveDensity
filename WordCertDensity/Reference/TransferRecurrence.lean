/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Transfer.LetterParity

/-! # The exact rational-input recurrence for the full reference density -/

@[expose] public section

namespace WordCertDensity.Reference

open scoped Classical

/-- The literal natural quotient in the manuscript's compatible one-letter recursion. -/
def transferInput (n : ℕ) (y : ZMod (3 ^ (n + 1))) (a : ℕ) : ZMod (3 ^ n) :=
  (((2 ^ a * y.val - 1) / 3 : ℕ) : ZMod (3 ^ n))

/-- Compatibility makes the integer quotient an exact inverse of the one-letter map. -/
theorem wordMap_transferInput (n : ℕ) (y : ZMod (3 ^ (n + 1))) (a : ℕ+)
    (ha : (2 ^ (a : ℕ) * y.val) % 3 = 1) :
    Transfer.wordMap [a] (n + 1) (transferInput n y a) = y := by
  have hn : 3 * ((2 ^ (a : ℕ) * y.val - 1) / 3) + 1 = 2 ^ (a : ℕ) * y.val := by omega
  have hz : (3 : ZMod (3 ^ (n + 1))) *
      (((2 ^ (a : ℕ) * y.val - 1) / 3 : ℕ) : ZMod (3 ^ (n + 1))) + 1 =
      (2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ) * y := by
    have h := congrArg (fun k : ℕ => (k : ZMod (3 ^ (n + 1)))) hn
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow,
      ZMod.natCast_zmod_val] using h
  rw [transferInput, Transfer.wordMap_natCast [a] (by simp)]
  simp only [ValuationWord.residueOffset, List.length_singleton, pow_one,
    ValuationWord.total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, mul_zero, mul_one]
  have hc := two_pow_mul_inverseTwoPow (n + 1) a
  linear_combination inverseTwoPow (n + 1) a * hz + y * hc

/-- The pushed-forward atom is the unique compatible input mass, or zero off its image. -/
theorem singleton_map_mass (n : ℕ) (y : ZMod (3 ^ (n + 1))) (a : ℕ+) :
    (((law n).map (Transfer.wordMap [a] (n + 1))) y).toReal =
      if (2 ^ (a : ℕ) * y.val) % 3 = 1 then mass n (transferInput n y a) else 0 := by
  by_cases ha : (2 ^ (a : ℕ) * y.val) % 3 = 1
  · rw [if_pos ha]
    conv_lhs => rw [← wordMap_transferInput n y a ha]
    simp [PMF.map_apply, (Transfer.wordMap_injective [a] (q := n + 1) (by simp)).eq_iff,
      mass, tsum_fintype]
  · rw [if_neg ha]
    have hr : y ∉ Set.range (Transfer.wordMap [a] (n + 1)) := by
      intro h
      have hcast : (y.val : ZMod (3 ^ (n + 1))) ∈
          Set.range (Transfer.wordMap [a] (n + 1)) := by simpa using h
      exact ha ((Transfer.mem_range_singleton_nat a n y.val).mp hcast)
    have hne (z : ZMod (3 ^ n)) : y ≠ Transfer.wordMap [a] (n + 1) z :=
      fun h => hr ⟨z, h.symm⟩
    simp [PMF.map_apply, hne]

/-- The exact full-group density recursion, including n=0 and every incompatible residue. -/
theorem referenceTransfer (n : ℕ) (y : ZMod (3 ^ (n + 1))) :
    density (n + 1) y = 3 * ∑' a : ℕ+,
      if (2 ^ (a : ℕ) * y.val) % 3 = 1 then
        (2 : ℝ) ^ (-((a : ℕ) : ℤ)) * density n (transferInput n y a) else 0 := by
  rw [density, mass_succ, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro a
  rw [singleton_map_mass]
  by_cases ha : (2 ^ (a : ℕ) * y.val) % 3 = 1
  · simp only [if_pos ha, density, geometricLetter_toReal, zpow_neg, zpow_natCast,
      one_div_pow, pow_succ]
    ring
  · simp [ha]

end WordCertDensity.Reference
