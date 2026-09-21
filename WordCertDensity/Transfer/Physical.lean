/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Transfer.Affine
public import WordCertDensity.Words.Inverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# From affine residues to actual integer histories

Affine image membership is the integral endpoint criterion. At an odd
natural root above the word offset it is equivalent to an actual positive
history. For any such history the finite operator evaluates to the physical
word coefficient times the function at its actual source residue.
-/

@[expose] public section

namespace WordCertDensity

namespace Transfer

/-- Image membership is precisely integrality of the signed inverse endpoint. -/
theorem mem_range_wordMap_iff_integral (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q)
    (root : ℤ) : (root : ZMod (3 ^ q)) ∈ Set.range (wordMap w q) ↔
      ∃ z : ℤ, w.inverseEndpoint root = (z : ℚ) := by
  rw [mem_range_wordMap w hq, map_intCast]
  exact (ValuationWord.inverseEndpoint_integral_iff w root).symm

/-- Affine image membership gives integral endpoints for every prefix. -/
theorem integral_prefix_of_mem_range (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q)
    (root : ℤ) (h : (root : ZMod (3 ^ q)) ∈ Set.range (wordMap w q)) (i : ℕ) :
    ∃ z : ℤ, ValuationWord.inverseEndpoint (w.take i) root = (z : ℚ) :=
  ValuationWord.inverseEndpoint_take_integral w root
    ((mem_range_wordMap_iff_integral w hq root).mp h) i

/-- At a guarded odd natural root the affine image is exactly the set of physical words. -/
theorem mem_range_wordMap_iff_physical (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q)
    (root : ℕ) (hroot : Odd root) (hlarge : w.offset < (root : ℚ)) :
    (root : ZMod (3 ^ q)) ∈ Set.range (wordMap w q) ↔
      ∃ source : ℕ, PhysicalHistory w root source := by
  rw [mem_range_wordMap w hq, Reference.project_natCast]
  exact (ValuationWord.exists_physical_iff_residue w root hroot hlarge).symm

/-- A physical history's actual source maps to its root in every valid ternary modulus. -/
theorem wordMap_of_physical {w : ValuationWord} {q root source : ℕ} (hq : w.length ≤ q)
    (h : PhysicalHistory w root source) :
    wordMap w q (source : ZMod (3 ^ (q - w.length))) = (root : ZMod (3 ^ q)) := by
  rw [wordMap_natCast w hq, ValuationWord.residueOffset_eq_reverseNumerator]
  have hn : 2 ^ w.total * root = 3 ^ w.length * source +
      ValuationWord.forwardNumerator w.reverse := by
    simpa only [ValuationWord.total_reverse, List.length_reverse, h.accelerated_iterate] using
      h.forwardRealizes.affine_eq
  have hz : (2 : ZMod (3 ^ q)) ^ w.total * (root : ZMod (3 ^ q)) =
      (3 : ZMod (3 ^ q)) ^ w.length * (source : ZMod (3 ^ q)) +
        (ValuationWord.forwardNumerator w.reverse : ZMod (3 ^ q)) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using
      congrArg (fun a : ℕ => (a : ZMod (3 ^ q))) hn
  have hc := Reference.two_pow_mul_inverseTwoPow q w.total
  linear_combination -Reference.inverseTwoPow q w.total * hz + (root : ZMod (3 ^ q)) * hc

/-- The transfer value at a physical root uses the actual source, with its exact word weight. -/
theorem wordOperator_of_physical {w : ValuationWord} {q root source : ℕ} (hq : w.length ≤ q)
    (h : PhysicalHistory w root source) (g : ZMod (3 ^ (q - w.length)) → ℝ) :
    wordOperator w q g (root : ZMod (3 ^ q)) =
      weight w * g (source : ZMod (3 ^ (q - w.length))) := by
  rw [← wordMap_of_physical hq h, wordOperator_image w hq]

/-- In particular, the operator marks the actual inverse source with exactly one marker. -/
theorem wordOperator_physical_marker {w : ValuationWord} {q root source : ℕ}
    (hq : w.length ≤ q) (h : PhysicalHistory w root source) :
    wordOperator w q (Reference.marker (q - w.length)) (root : ZMod (3 ^ q)) =
      (w.slope : ℝ) * Reference.marker (q - w.length)
        (source : ZMod (3 ^ (q - w.length))) :=
  wordOperator_of_physical hq h _

/-- A guarded odd root without a physical realization receives no transferred value. -/
theorem wordOperator_eq_zero_of_no_physical (w : ValuationWord) {q : ℕ}
    (hq : w.length ≤ q) (root : ℕ) (hroot : Odd root) (hlarge : w.offset < (root : ℚ))
    (hno : ¬ ∃ source : ℕ, PhysicalHistory w root source)
    (g : ZMod (3 ^ (q - w.length)) → ℝ) : wordOperator w q g (root : ZMod (3 ^ q)) = 0 := by
  apply wordOperator_off_image
  exact fun h => hno ((mem_range_wordMap_iff_physical w hq root hroot hlarge).mp h)

end Transfer

end WordCertDensity
