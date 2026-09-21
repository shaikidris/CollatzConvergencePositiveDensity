/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.Residues
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integral and positive inverse endpoints

The rational inverse endpoint has a single explicit numerator. Its
integrality is equivalent to the ternary offset congruence, and the same
congruence gives integral endpoints for every prefix. Under the strict
offset guard, the accepted chronological affine theorem constructs the
actual positive odd inverse history in the correct word order.
-/

@[expose] public section

namespace WordCertDensity

namespace ValuationWord

/-- The rational endpoint obtained by solving the word's affine root equation. -/
def inverseEndpoint (w : ValuationWord) (root : ℚ) : ℚ := (root - w.offset) / w.slope

/-- The empty inverse word leaves its endpoint unchanged. -/
@[simp] theorem inverseEndpoint_nil (root : ℚ) : inverseEndpoint [] root = root := by
  simp [inverseEndpoint, slope, offset, total]

/-- The inverse endpoint evaluates back to its original root. -/
theorem evaluate_inverseEndpoint (w : ValuationWord) (root : ℚ) :
    w.evaluate (w.inverseEndpoint root) = root := by
  rw [evaluate_eq, inverseEndpoint]
  field_simp [ne_of_gt w.slope_pos]
  ring

/-- Solving the affine equation recovers any rational source. -/
theorem inverseEndpoint_evaluate (w : ValuationWord) (source : ℚ) :
    w.inverseEndpoint (w.evaluate source) = source := by
  rw [inverseEndpoint, evaluate_eq]
  field_simp [ne_of_gt w.slope_pos]
  ring

/-- The inverse endpoint has the reversed chronological integral numerator. -/
theorem inverseEndpoint_eq_reverseNumerator (w : ValuationWord) (root : ℚ) :
    w.inverseEndpoint root =
      ((2 : ℚ) ^ w.total * root - forwardNumerator w.reverse) / 3 ^ w.length := by
  rw [inverseEndpoint, offset_eq_reverseNumerator, slope]
  field_simp

/-- Positivity is exactly the strict root-above-offset condition. -/
theorem inverseEndpoint_pos_iff (w : ValuationWord) (root : ℚ) :
    0 < w.inverseEndpoint root ↔ w.offset < root := by
  rw [inverseEndpoint, div_pos_iff_of_pos_right w.slope_pos, sub_pos]

/-- Appending positive valuation letters can only increase the inverse offset. -/
theorem offset_le_append (u v : ValuationWord) : u.offset ≤ offset (u ++ v) := by
  rw [offset_append]
  exact le_add_of_nonneg_right (mul_nonneg u.slope_pos.le v.offset_nonneg)

/-- The strict full-word offset guard makes every rational prefix endpoint positive. -/
theorem inverseEndpoint_take_pos (w : ValuationWord) (root : ℚ) (h : w.offset < root)
    (i : ℕ) : 0 < inverseEndpoint (w.take i) root := by
  apply (inverseEndpoint_pos_iff _ _).mpr
  have hle : offset (w.take i) ≤ w.offset := by
    simpa only [List.take_append_drop] using offset_le_append (w.take i) (w.drop i)
  exact lt_of_le_of_lt hle h

/-- The root offset congruence is the integer divisibility criterion for the full numerator. -/
theorem root_residue_iff_dvd (w : ValuationWord) (root : ℤ) :
    (root : ZMod (3 ^ w.length)) = residueOffset w.length w ↔
      (3 : ℤ) ^ w.length ∣ (2 : ℤ) ^ w.total * root - forwardNumerator w.reverse := by
  rw [residueOffset_eq_reverseNumerator]
  have hd : ((3 ^ w.length : ℕ) : ℤ) = (3 : ℤ) ^ w.length := by norm_cast
  rw [← hd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero]
  have hc := Reference.two_pow_mul_inverseTwoPow w.length w.total
  constructor
  · intro h
    rw [h, ← mul_assoc, hc, one_mul]
  · intro h
    have hr := congrArg (fun z : ZMod (3 ^ w.length) =>
      Reference.inverseTwoPow w.length w.total * z) h
    have hi : Reference.inverseTwoPow w.length w.total *
        (2 : ZMod (3 ^ w.length)) ^ w.total = 1 := by rw [mul_comm, hc]
    simpa only [← mul_assoc, hi, one_mul] using hr

/-- An integer root has an integral inverse endpoint exactly on its ternary offset class. -/
theorem inverseEndpoint_integral_iff (w : ValuationWord) (root : ℤ) :
    (∃ z : ℤ, w.inverseEndpoint root = (z : ℚ)) ↔
      (root : ZMod (3 ^ w.length)) = residueOffset w.length w := by
  rw [root_residue_iff_dvd]
  constructor
  · rintro ⟨z, hz⟩
    rw [inverseEndpoint_eq_reverseNumerator] at hz
    have hr := (div_eq_iff (by positivity : (3 : ℚ) ^ w.length ≠ 0)).mp hz
    have hi : (2 : ℤ) ^ w.total * root - forwardNumerator w.reverse =
        z * (3 : ℤ) ^ w.length := by exact_mod_cast hr
    exact ⟨z, by simpa [mul_comm] using hi⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [inverseEndpoint_eq_reverseNumerator]
    apply (div_eq_iff (by positivity : (3 : ℚ) ^ w.length ≠ 0)).mpr
    have hr : (2 : ℚ) ^ w.total * (root : ℚ) - forwardNumerator w.reverse =
        (3 : ℚ) ^ w.length * (z : ℚ) := by exact_mod_cast hz
    simpa [mul_comm] using hr

/-- Full-word integrality implies the integrality of every earlier prefix endpoint. -/
theorem inverseEndpoint_prefix_integral (u v : ValuationWord) (root : ℤ)
    (h : ∃ z : ℤ, inverseEndpoint (u ++ v) root = (z : ℚ)) :
    ∃ z : ℤ, u.inverseEndpoint root = (z : ℚ) := by
  have hm := (inverseEndpoint_integral_iff (u ++ v) root).mp h
  have hle : u.length ≤ (u ++ v).length := by simp
  have hp := congrArg (Reference.project hle) hm
  rw [map_intCast, project_residueOffset,
    residueOffset_append_of_level_le _ _ _ (le_refl u.length)] at hp
  exact (inverseEndpoint_integral_iff u root).mpr hp

/-- Full-word integrality covers every prefix length, including zero and lengths past the end. -/
theorem inverseEndpoint_take_integral (w : ValuationWord) (root : ℤ)
    (h : ∃ z : ℤ, w.inverseEndpoint root = (z : ℚ)) (i : ℕ) :
    ∃ z : ℤ, inverseEndpoint (w.take i) root = (z : ℚ) := by
  apply inverseEndpoint_prefix_integral (w.take i) (w.drop i) root
  simpa only [List.take_append_drop] using h

end ValuationWord

namespace PhysicalHistory

/-- The rational inverse endpoint of a physical history is its actual natural source. -/
theorem inverseEndpoint_eq {w : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory w root source) : w.inverseEndpoint root = (source : ℚ) := by
  rw [h.evaluate_eq, ValuationWord.inverseEndpoint_evaluate]

/-- Every physical history satisfies the strict root-above-offset guard. -/
theorem root_gt_offset {w : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory w root source) : w.offset < (root : ℚ) := by
  apply (ValuationWord.inverseEndpoint_pos_iff w root).mp
  rw [h.inverseEndpoint_eq]
  exact_mod_cast h.source_pos

/-- An exact natural affine identity gives the full inverse physical history. -/
theorem of_affine_eq {w : ValuationWord} {root source : ℕ} (hroot : Odd root)
    (h : 2 ^ w.total * root = 3 ^ w.length * source +
      ValuationWord.forwardNumerator w.reverse) : PhysicalHistory w root source := by
  have hf : ForwardRealizes w.reverse source := ForwardRealizes.of_affine_eq hroot (by
    simpa only [ValuationWord.total_reverse, List.length_reverse] using h)
  have ha : 2 ^ w.total * (acceleratedStep^[w.length]) source =
      3 ^ w.length * source + ValuationWord.forwardNumerator w.reverse := by
    simpa only [ValuationWord.total_reverse, List.length_reverse] using hf.affine_eq
  have he : (acceleratedStep^[w.length]) source = root :=
    Nat.eq_of_mul_eq_mul_left (by positivity) (ha.trans h.symm)
  simpa only [List.reverse_reverse, List.length_reverse, he] using hf.physical

end PhysicalHistory

namespace ValuationWord

/-- On an odd root above the offset, the residue criterion constructs an actual positive history. -/
theorem exists_physical_iff_residue (w : ValuationWord) (root : ℕ) (hroot : Odd root)
    (hlarge : w.offset < (root : ℚ)) :
    (∃ source : ℕ, PhysicalHistory w root source) ↔
      (root : ZMod (3 ^ w.length)) = residueOffset w.length w := by
  constructor
  · rintro ⟨source, hs⟩
    have hi : ∃ z : ℤ, w.inverseEndpoint (root : ℤ) = (z : ℚ) :=
      ⟨(source : ℤ), by simpa only [Int.cast_natCast] using hs.inverseEndpoint_eq⟩
    simpa only [Int.cast_natCast] using (inverseEndpoint_integral_iff w (root : ℤ)).mp hi
  · intro hm
    obtain ⟨z, hz⟩ := (inverseEndpoint_integral_iff w (root : ℤ)).mpr (by
      simpa only [Int.cast_natCast] using hm)
    have hzpos : 0 < z := by
      have hp := (inverseEndpoint_pos_iff w (root : ℚ)).mpr hlarge
      have he : (z : ℚ) = w.inverseEndpoint (root : ℚ) := by
        simpa only [Int.cast_natCast] using hz.symm
      rw [← he] at hp
      exact_mod_cast hp
    have hnat : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hzpos.le
    have he : w.inverseEndpoint (root : ℚ) = (z.toNat : ℚ) := by
      calc
        w.inverseEndpoint (root : ℚ) = (z : ℚ) := by
          simpa only [Int.cast_natCast] using hz
        _ = (z.toNat : ℚ) := by exact_mod_cast hnat.symm
    refine ⟨z.toNat, PhysicalHistory.of_affine_eq hroot ?_⟩
    rw [inverseEndpoint_eq_reverseNumerator] at he
    have hc := (div_eq_iff (by positivity : (3 : ℚ) ^ w.length ≠ 0)).mp he
    have hr : (2 : ℚ) ^ w.total * root =
        (3 : ℚ) ^ w.length * z.toNat + forwardNumerator w.reverse := by
      linear_combination hc
    exact_mod_cast hr

end ValuationWord

end WordCertDensity
