/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Words.Certificate
public import WordCertDensity.Reference.Residues
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integer cleared inverse offsets

The inverse-prefix numerator is the existing chronological numerator of the
reversed word. Its injectivity at fixed length and total follows from the
already proved physical word cylinders, including the empty-word boundary.
-/

@[expose] public section

namespace WordCertDensity
namespace ValuationWord

/-- The integer numerator of the inverse-prefix offset after clearing its binary denominator. -/
def clearedOffset (w : ValuationWord) : ℕ := forwardNumerator w.reverse

/-- The empty word has zero cleared offset. -/
@[simp] theorem clearedOffset_nil : clearedOffset [] = 0 := rfl

/-- Adding the first inverse letter gives the exact numerator recurrence. -/
theorem clearedOffset_cons (a : ℕ+) (w : ValuationWord) :
    clearedOffset (a :: w) = 3 * clearedOffset w + 2 ^ w.total := by
  simp [clearedOffset, forwardNumerator_append_singleton]

/-- Every nonempty inverse word has a strictly positive cleared offset. -/
theorem clearedOffset_pos {w : ValuationWord} (hw : w ≠ []) : 0 < w.clearedOffset := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w => rw [clearedOffset_cons]; positivity

/-- The natural prefix-sum formula uses subtraction only within the total valuation. -/
theorem clearedOffset_eq_sum (w : ValuationWord) :
    w.clearedOffset = ∑ j ∈ Finset.range w.length,
      3 ^ j * 2 ^ (w.total - total (w.take (j + 1))) := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [clearedOffset_cons, ih, List.length_cons, Finset.sum_range_succ']
      simp only [List.take_succ_cons, total, List.map_cons, List.sum_cons,
        Nat.add_sub_add_left, List.take_zero, List.map_nil, List.sum_nil, add_zero,
        pow_zero, one_mul, Nat.add_sub_cancel_left]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring

/-- The rational offset and the cleared numerator agree with the exact total denominator. -/
theorem offset_eq_clearedOffset (w : ValuationWord) :
    w.offset = (w.clearedOffset : ℚ) / 2 ^ w.total := offset_eq_reverseNumerator w

/-- Clearing the binary unit in the residue group gives the natural numerator. -/
theorem two_pow_mul_residueOffset (q : ℕ) (w : ValuationWord) :
    (2 : ZMod (3 ^ q)) ^ w.total * w.residueOffset q = w.clearedOffset := by
  rw [residueOffset_eq_reverseNumerator, ← mul_assoc,
    Reference.two_pow_mul_inverseTwoPow, one_mul]
  rfl

/-- Length, total and chronological numerator determine the actual finite word. -/
theorem eq_of_forwardNumerator_eq {u w : ValuationWord}
    (hlen : u.length = w.length) (htotal : u.total = w.total)
    (hnum : u.forwardNumerator = w.forwardNumerator) : u = w := by
  obtain ⟨x, hx, _⟩ := ForwardRealizes.exists_unique_residue u
  have hw : ForwardRealizes w x := by
    apply (ForwardRealizes.iff_affine_modEq w x).mpr
    rw [← hlen, ← htotal, ← hnum]
    exact (ForwardRealizes.iff_affine_modEq u x).mp hx.2
  apply List.map_injective_iff.mpr PNat.coe_injective
  exact hx.2.2.2.symm.trans (hlen ▸ hw.2.2)

/-- Length and total together with the cleared inverse numerator determine the word. -/
theorem eq_of_clearedOffset_eq {u w : ValuationWord}
    (hlen : u.length = w.length) (htotal : u.total = w.total)
    (hnum : u.clearedOffset = w.clearedOffset) : u = w := by
  apply List.reverse_injective
  apply eq_of_forwardNumerator_eq
  · simpa using hlen
  · simpa using htotal
  · exact hnum

/-- Small cleared numerators turn modular offset equality into word equality. -/
theorem eq_of_residueOffset_eq_of_lt {q : ℕ} {u w : ValuationWord}
    (hlen : u.length = w.length) (htotal : u.total = w.total)
    (hu : u.clearedOffset < 3 ^ q) (hw : w.clearedOffset < 3 ^ q)
    (heq : u.residueOffset q = w.residueOffset q) : u = w := by
  apply eq_of_clearedOffset_eq hlen htotal
  have hm := congrArg (fun z : ZMod (3 ^ q) => (2 : ZMod (3 ^ q)) ^ u.total * z) heq
  rw [two_pow_mul_residueOffset, htotal, two_pow_mul_residueOffset] at hm
  have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mp hm
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hw] using hc

end ValuationWord
end WordCertDensity
