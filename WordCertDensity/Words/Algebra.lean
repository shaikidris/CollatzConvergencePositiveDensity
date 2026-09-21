/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Inverse-prefix word algebra

A word is listed from its root outward. Its affine evaluator maps the final
source back to the root: the first listed letter is the outermost affine map.
These rational identities do not assert integral or positive realization.
-/

@[expose] public section

namespace WordCertDensity

/-- Positive valuations; each consuming API specifies its word orientation. -/
abbrev ValuationWord := List ℕ+

namespace ValuationWord

/-- Total valuation, independent of the orientation of the word. -/
def total (w : ValuationWord) : ℕ := (w.map (fun k : ℕ+ => (k : ℕ))).sum

/-- Ordinary cost: one odd step and all its halvings per letter. -/
def ordinaryCost (w : ValuationWord) : ℕ := w.total + w.length

/-- Multiplicative slope of a word. -/
def slope (w : ValuationWord) : ℚ := 3 ^ w.length / 2 ^ w.total

/-- Inverse-prefix additive offset, with the first letter outermost. -/
def offset : ValuationWord → ℚ
  | [] => 0
  | k :: w => 1 / 2 ^ (k : ℕ) + 3 / 2 ^ (k : ℕ) * offset w

/-- Affine evaluator from a rational source to its root. -/
def evaluate : ValuationWord → ℚ → ℚ
  | [], x => x
  | k :: w, x => (3 * evaluate w x + 1) / 2 ^ (k : ℕ)

/-- An outer letter pays its odd step and its positive number of halvings. -/
@[simp] theorem ordinaryCost_cons (k : ℕ+) (w : ValuationWord) :
    ordinaryCost (k :: w) = (k : ℕ) + 1 + w.ordinaryCost := by
  simp [ordinaryCost, total]
  omega

/-- Concatenation adds valuation totals. -/
@[simp] theorem total_append (u v : ValuationWord) : total (u ++ v) = u.total + v.total := by
  simp [total]

/-- Reversal preserves the total valuation. -/
@[simp] theorem total_reverse (w : ValuationWord) : total w.reverse = w.total := by
  simp [total]

/-- Concatenation adds the ordinary costs. -/
@[simp] theorem ordinaryCost_append (u v : ValuationWord) :
    ordinaryCost (u ++ v) = u.ordinaryCost + v.ordinaryCost := by
  simp [ordinaryCost]
  omega

/-- Reversal preserves the ordinary cost, but need not preserve the offset. -/
@[simp] theorem ordinaryCost_reverse (w : ValuationWord) :
    ordinaryCost w.reverse = w.ordinaryCost := by
  simp [ordinaryCost]

/-- Adding an outer letter multiplies the slope by its one-letter slope. -/
theorem slope_cons (k : ℕ+) (w : ValuationWord) :
    slope (k :: w) = 3 / 2 ^ (k : ℕ) * w.slope := by
  simp [slope, total, pow_add, pow_succ]
  ring

/-- All word slopes are strictly positive. -/
theorem slope_pos (w : ValuationWord) : 0 < w.slope := by
  unfold slope
  positivity

/-- Offsets are nonnegative, including the empty word. -/
theorem offset_nonneg (w : ValuationWord) : 0 ≤ w.offset := by
  induction w with
  | nil => simp [offset]
  | cons k w ih =>
      simp only [offset]
      positivity

/-- Exact affine source-to-root expression. -/
theorem evaluate_eq (w : ValuationWord) (x : ℚ) :
    w.evaluate x = w.slope * x + w.offset := by
  induction w with
  | nil => simp [evaluate, slope, total, offset]
  | cons k w ih =>
      rw [evaluate, ih, slope_cons, offset]
      ring

/-- Appending inner letters composes in inverse-prefix order. -/
theorem evaluate_append (u v : ValuationWord) (x : ℚ) :
    evaluate (u ++ v) x = u.evaluate (v.evaluate x) := by
  induction u with
  | nil => rfl
  | cons k u ih => simp only [List.cons_append, evaluate, ih]

/-- Slopes multiply under ordered concatenation. -/
theorem slope_append (u v : ValuationWord) : slope (u ++ v) = u.slope * v.slope := by
  simp [slope, pow_add]
  ring

/-- The offset composition retains the outer slope and the block order. -/
theorem offset_append (u v : ValuationWord) :
    offset (u ++ v) = u.offset + u.slope * v.offset := by
  have h := evaluate_append u v 0
  simpa [evaluate_eq, add_comm] using h

/-- The affine identity bounds the unnormalized source charge. -/
theorem affine_charge {w : ValuationWord} {x root : ℚ}
    (hroot : root = w.evaluate x) : x * w.slope ≤ root := by
  rw [hroot, evaluate_eq, mul_comm x]
  exact le_add_of_nonneg_right (offset_nonneg w)

/-- Positive physical realizations will consume this normalized charge inequality. -/
theorem normalized_affine_charge {w : ValuationWord} {x root : ℚ}
    (hx : 0 < x) (hroot : 0 < root) (hidentity : root = w.evaluate x) :
    w.slope / root ≤ 1 / x := by
  apply (div_le_div_iff₀ hroot hx).2
  simpa [mul_comm] using affine_charge hidentity

end ValuationWord

end WordCertDensity
