/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.PrefixTail

/-! # Changing only the final positive valuation

The mapIdx definition matches the prepared compression interface. Its
append identity makes the unchanged prefix and final-letter operation explicit.
-/

namespace WordCertDensity.ValuationWord

/-- Apply one positive-valuation map only at the final index. -/
def changeLast (w : ValuationWord) (f : ℕ+ → ℕ+) : ValuationWord :=
  w.mapIdx fun i a => if i+1=w.length then f a else a

/-- The operation preserves the exact inverse depth. -/
@[simp] theorem changeLast_length (w : ValuationWord) (f : ℕ+ → ℕ+) :
    (changeLast w f).length = w.length := by simp [changeLast]

/-- Every earlier valuation is unchanged and only the last letter is mapped. -/
theorem changeLast_append (v : ValuationWord) (a : ℕ+) (f : ℕ+ → ℕ+) :
    changeLast (v ++ [a]) f = v ++ [f a] := by
  unfold changeLast
  rw [List.mapIdx_concat]
  simp only [List.length_append, List.length_cons, List.length_nil, ite_true]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_mapIdx]
    rw [if_neg (by omega)]

/-- Remove an even amount from the last letter; totalization is irrelevant on valid compression. -/
def reduceLast (w : ValuationWord) (j : ℕ) : ValuationWord :=
  changeLast w (fun a => ⟨max 1 ((a : ℕ)-2*j), by omega⟩)

/-- Restore the removed even amount to the final letter. -/
def raiseLast (w : ValuationWord) (j : ℕ) : ValuationWord :=
  changeLast w (fun a => Reference.raisedLetter a (2*j))

/-- Literal reduction on a nonempty word. -/
theorem reduceLast_append (v : ValuationWord) (a : ℕ+) (j : ℕ) :
    reduceLast (v ++ [a]) j =
      v ++ ([⟨max 1 ((a : ℕ)-2*j), by omega⟩] : ValuationWord) :=
  changeLast_append v a _

/-- Restoration retains the prefix and raises exactly the last letter. -/
theorem raiseLast_append (v : ValuationWord) (a : ℕ+) (j : ℕ) :
    raiseLast (v ++ [a]) j = v ++ [Reference.raisedLetter a (2*j)] :=
  changeLast_append v a _

/-- The reduced word has exactly the original number of inverse steps. -/
@[simp] theorem reduceLast_length (w : ValuationWord) (j : ℕ) :
    (reduceLast w j).length = w.length := changeLast_length w _

end WordCertDensity.ValuationWord
