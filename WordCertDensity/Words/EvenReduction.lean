/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Words.Physical
import WordCertDensity.Reference.PrefixTail
import WordCertDensity.Roots.Basic

/-! # Physical reduction of an even excess in one inverse step

Modulo three, an even exponent excess contributes a power of four and hence
does not change admissibility. The reduced positive valuation gives a positive
odd integer source. The existing exact root recurrence supplies the fan offset.
-/

namespace WordCertDensity

/-- Natural affine fan source, with its offset encoded by the exact root recurrence. -/
def fanSource (j x : ℕ) : ℕ := 4^j*x+Roots.value j

/-- The fan offset is exactly the printed integer quotient. -/
theorem fanSource_eq (j x : ℕ) : fanSource j x = 4^j*x+(4^j-1)/3 := by
  rw [fanSource, Roots.value_eq_quotient]

/-- The fan scales the odd-step numerator by exactly a power of four. -/
theorem fanSource_numerator (j x : ℕ) : 3*fanSource j x+1 = 4^j*(3*x+1) := by
  have h := Roots.three_mul_value_add_one j
  unfold fanSource
  nlinarith

/-- Removing a specified even excess preserves a positive odd physical inverse step. -/
theorem inverseBlock_even_reduce (a : ℕ+) (j : ℕ) {p x : ℕ}
    (hp : 0 < p) (hodd : Odd p)
    (hblock : 3*x+1 = 2^((a : ℕ)+2*j)*p) :
    ∃ z, PhysicalHistory [a] p z ∧ x = fanSource j z := by
  have he : 3*x+1 = 4^j*(2^(a : ℕ)*p) := by
    rw [hblock, pow_add, pow_mul]
    norm_num
    ring
  have hfour : 4^j%3=1 := by norm_num [Nat.pow_mod]
  have hmod : (2^(a : ℕ)*p)%3=1 := by
    have h : (4^j*(2^(a : ℕ)*p))%3=1 := by rw [← he]; omega
    simpa only [Nat.mul_mod, hfour, one_mul, Nat.mod_mod] using h
  let z := (2^(a : ℕ)*p)/3
  have hzEq : 3*z+1=2^(a : ℕ)*p := by
    have h := Nat.mod_add_div (2^(a : ℕ)*p) 3
    dsimp only [z]
    omega
  have ha : 1 ≤ (a : ℕ) := a.property
  have hpow : 2 ≤ 2^(a : ℕ) := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) ha
  have hN : 2 ≤ 2^(a : ℕ)*p := by
    have h := Nat.mul_le_mul_left (2^(a : ℕ)) (show 1 ≤ p by omega)
    simp only [mul_one] at h
    omega
  have hzpos : 0 < z := by omega
  have heven : (2^(a : ℕ)*p)%2=0 := by
    have heq : 2^(a : ℕ)*p = (2^((a : ℕ)-1)*p)*2 := by
      conv_lhs => rw [show (a : ℕ) = ((a : ℕ)-1)+1 by omega, pow_succ]
      ring
    rw [heq]
    omega
  have hzodd : Odd z := by
    apply Nat.odd_iff.mpr
    omega
  refine ⟨z, PhysicalHistory.cons hp hodd hzEq (PhysicalHistory.nil z hzpos hzodd), ?_⟩
  have hx : 3*x+1=4^j*(3*z+1) := by rw [hzEq]; exact he
  have hf := fanSource_numerator j z
  have hEq := hx.trans hf.symm
  omega

namespace PhysicalHistory

/-- An actual raised final step has a reduced physical step and the exact fan source. -/
theorem raisedLetter_even_reduce {a : ℕ+} {j p x : ℕ}
    (h : PhysicalHistory [Reference.raisedLetter a (2*j)] p x) :
    ∃ z, PhysicalHistory [a] p z ∧ x = fanSource j z := by
  have he : 3*x+1=2^((a : ℕ)+2*j)*p := by
    cases h with
    | cons hpos hodd hblock tail =>
        cases tail
        simpa only [Reference.raisedLetter_val] using hblock
  exact inverseBlock_even_reduce a j h.root_pos h.root_odd he

end PhysicalHistory
end WordCertDensity
