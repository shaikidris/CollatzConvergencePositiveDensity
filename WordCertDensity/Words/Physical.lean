/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Dynamics.Accelerated
public import WordCertDensity.Words.Algebra
import Mathlib.Tactic.NormNum

/-!
# Physical inverse histories

A word is listed from the root outward. Each link has positive odd integer
endpoints and the exact equation `3 * child + 1 = 2 ^ k * parent`.
The chronological forward path traverses the letters in reverse order.
Single-history charge does not assert uniqueness after grouping histories.
-/

@[expose] public section

namespace WordCertDensity

/-- Actual positive odd inverse trajectories, in root-to-source prefix order. -/
inductive PhysicalHistory : ValuationWord → ℕ → ℕ → Prop
  /-- The empty history stays at its positive odd root. -/
  | nil (root : ℕ) (hpos : 0 < root) (hodd : Odd root) : PhysicalHistory [] root root
  /-- An outer inverse block followed by its remaining inner history. -/
  | cons {k : ℕ+} {w : ValuationWord} {root child source : ℕ}
      (hpos : 0 < root) (hodd : Odd root)
      (hblock : 3 * child + 1 = 2 ^ (k : ℕ) * root)
      (tail : PhysicalHistory w child source) : PhysicalHistory (k :: w) root source

namespace PhysicalHistory

/-- A physical history has a positive root. -/
theorem root_pos {w : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory w root source) : 0 < root := by
  cases h with
  | nil _ hpos _ => exact hpos
  | cons hpos _ _ _ => exact hpos

/-- A physical history has an odd root. -/
theorem root_odd {w : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory w root source) : Odd root := by
  cases h with
  | nil _ _ hodd => exact hodd
  | cons _ hodd _ _ => exact hodd

/-- A physical history has a positive source. -/
theorem source_pos {w : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory w root source) : 0 < source := by
  induction h with
  | nil _ hpos _ => exact hpos
  | cons _ _ _ _ ih => exact ih

/-- A physical history has an odd source. -/
theorem source_odd {w : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory w root source) : Odd source := by
  induction h with
  | nil _ _ hodd => exact hodd
  | cons _ _ _ _ ih => exact ih

/-- Appending inverse histories matches the order of their physical endpoints. -/
theorem append {u v : ValuationWord} {root middle source : ℕ}
    (hu : PhysicalHistory u root middle) (hv : PhysicalHistory v middle source) :
    PhysicalHistory (u ++ v) root source := by
  induction hu with
  | nil => exact hv
  | cons hpos hodd hblock _ ih => exact cons hpos hodd hblock (ih hv)

/-- The actual forward accelerated orbit reaches the root after one step per letter. -/
theorem accelerated_iterate {w : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory w root source) : (acceleratedStep^[w.length]) source = root := by
  induction h with
  | nil => rfl
  | cons _ hodd hblock _ ih =>
      rw [List.length_cons, Function.iterate_succ_apply', ih]
      exact acceleratedStep_eq_of_odd_quotient hodd hblock

/-- Actual chronological valuations are exactly the displayed inverse word reversed. -/
theorem valuations_eq_reverse {w : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory w root source) :
    acceleratedValuations source w.length = w.reverse.map (fun k : ℕ+ => (k : ℕ)) := by
  induction h with
  | nil => rfl
  | cons _ hodd hblock tail ih =>
      rw [List.length_cons, acceleratedValuations_succ, tail.accelerated_iterate,
        acceleratedExponent_eq_of_odd_quotient hodd hblock, ih]
      simp

/-- The stated ordinary cost gives an iterate witness, which need not be a first hit. -/
theorem reachesIn {w : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory w root source) : ReachesIn source root w.ordinaryCost := by
  induction h with
  | nil => rfl
  | cons _ hodd hblock tail ih =>
      have hstep := reachesIn_acceleratedStep_of_odd tail.root_odd
      rw [acceleratedExponent_eq_of_odd_quotient hodd hblock,
        acceleratedStep_eq_of_odd_quotient hodd hblock] at hstep
      simpa [ValuationWord.ordinaryCost_cons, Nat.add_comm] using ih.trans hstep

/-- The rational evaluator agrees with the physical integer root. -/
theorem evaluate_eq {w : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory w root source) : (root : ℚ) = w.evaluate source := by
  induction h with
  | nil => rfl
  | @cons k _ root child _ _ _ hblock _ ih =>
      rw [ValuationWord.evaluate, ← ih]
      have hrat : (3 : ℚ) * child + 1 = 2 ^ (k : ℕ) * (root : ℚ) := by
        exact_mod_cast hblock
      apply (eq_div_iff (by positivity : (2 : ℚ) ^ (k : ℕ) ≠ 0)).2
      simpa [mul_comm] using hrat.symm

/-- The root equals the slope times the actual source plus the inverse offset. -/
theorem affine_eq {w : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory w root source) : (root : ℚ) = w.slope * source + w.offset := by
  rw [h.evaluate_eq, ValuationWord.evaluate_eq]

/-- A fixed physical word and source have a unique root. -/
theorem root_unique {w : ValuationWord} {root₁ root₂ source : ℕ}
    (h₁ : PhysicalHistory w root₁ source) (h₂ : PhysicalHistory w root₂ source) :
    root₁ = root₂ := by
  exact_mod_cast h₁.evaluate_eq.trans h₂.evaluate_eq.symm

/-- A fixed physical word and root have a unique source. -/
theorem source_unique {w : ValuationWord} {root source₁ source₂ : ℕ}
    (h₁ : PhysicalHistory w root source₁) (h₂ : PhysicalHistory w root source₂) :
    source₁ = source₂ := by
  have hmul : w.slope * (source₁ : ℚ) = w.slope * (source₂ : ℚ) := by
    exact add_right_cancel (h₁.affine_eq.symm.trans h₂.affine_eq)
  exact_mod_cast mul_left_cancel₀ (ne_of_gt w.slope_pos) hmul

/-- One physical history pays no more than its root in unnormalized charge. -/
theorem charge {w : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory w root source) : (source : ℚ) * w.slope ≤ root :=
  ValuationWord.affine_charge h.evaluate_eq

/-- Normalizing one physical history by its root gives charge at most `1 / source`. -/
theorem normalized_charge {w : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory w root source) : w.slope / root ≤ 1 / (source : ℚ) :=
  ValuationWord.normalized_affine_charge (by exact_mod_cast h.source_pos)
    (by exact_mod_cast h.root_pos) h.evaluate_eq

end PhysicalHistory

end WordCertDensity
