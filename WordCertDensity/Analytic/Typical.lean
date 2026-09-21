/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

Head-selection and scalar arguments adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The original LICENSE
and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
This version uses the local positive valuation words and the full manuscript width range.
-/
module

public import WordCertDensity.Words.Algebra
public import WordCertDensity.Analytic.HeadScalars
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Contiguous typicality and the unique first crossing

Typicality is imposed on every nonempty contiguous interval of the actual
positive valuation word. Prefixes inherit it. The crossing predicate uses
original prefix totals and has at most one index for any real threshold.
-/

@[expose] public section

namespace WordCertDensity
namespace ValuationWord

/-- A prefix has no greater valuation total than its whole word. -/
theorem total_take_le (w : ValuationWord) (i : ℕ) : (ValuationWord.total (w.take i)) ≤ w.total := by
  have h := total_append (w.take i) (w.drop i)
  rw [List.take_append_drop] at h
  omega

/-- Prefix valuation totals are monotone in the prefix length. -/
theorem total_take_mono (w : ValuationWord) {i j : ℕ} (hij : i ≤ j) :
    (ValuationWord.total (w.take i)) ≤ (ValuationWord.total (w.take j)) := by
  simpa only [List.take_take, Nat.min_eq_left hij] using total_take_le (w.take j) i

end ValuationWord

namespace Head

/-- Total valuation on the half-open interval [i,j) of a word. -/
def intervalSum (w : ValuationWord) (i j : ℕ) : ℕ := (ValuationWord.total ((w.drop i).take (j - i)))

/-- The interval beginning at zero is the corresponding prefix. -/
@[simp] theorem intervalSum_zero (w : ValuationWord) (j : ℕ) :
    intervalSum w 0 j = (ValuationWord.total (w.take j)) := by simp [intervalSum]

/-- The full interval has the original word total. -/
theorem intervalSum_full (w : ValuationWord) : intervalSum w 0 w.length = w.total := by
  simp

/-- Taking a sufficiently long prefix preserves an interval's valuation total. -/
theorem intervalSum_take (w : ValuationWord) {r i j : ℕ} (hj : j ≤ r) :
    intervalSum (w.take r) i j = intervalSum w i j := by
  unfold intervalSum
  rw [List.drop_take, List.take_take, Nat.min_eq_left (Nat.sub_le_sub_right hj i)]

/-- Adjacent prefix and singleton intervals add to the next prefix. -/
theorem total_take_succ (w : ValuationWord) (k : ℕ) :
    ValuationWord.total (w.take (k + 1)) =
      ValuationWord.total (w.take k) + intervalSum w k (k + 1) := by
  rw [intervalSum, Nat.add_sub_cancel_left, List.take_add, ValuationWord.total_append]

/-- Every nonempty contiguous interval satisfies the manuscript's width bound. -/
def Typical (v : ℝ) (n : ℕ) (w : ValuationWord) : Prop :=
  ∀ i j : ℕ, i < j → j ≤ w.length →
    |(intervalSum w i j : ℝ) - 2 * ((j - i : ℕ) : ℝ)| ≤
      v * (Real.sqrt (((j - i : ℕ) : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ))

/-- Every prefix of a typical word is typical at the same ambient scale and width. -/
theorem Typical.take {v : ℝ} {n : ℕ} {w : ValuationWord} (h : Typical v n w) (r : ℕ) :
    Typical v n (w.take r) := by
  intro i j hij hj
  have hjr := hj.trans (List.length_take_le r w)
  have hjw := hj.trans (List.length_take_le' r w)
  simpa only [intervalSum_take w hjr] using h i j hij hjw

/-- A typical nonempty prefix has the required lower valuation sum. -/
theorem Typical.prefix_lower {v : ℝ} {n : ℕ} {w : ValuationWord} (h : Typical v n w)
    {j : ℕ} (hj : 0 < j) (hjw : j ≤ w.length) :
    2 * (j : ℝ) - v * (Real.sqrt ((j : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ)) ≤
      ((ValuationWord.total (w.take j)) : ℝ) := by
  have ha := h 0 j hj hjw
  simp only [intervalSum_zero, Nat.sub_zero] at ha
  linarith [(abs_le.mp ha).1]

/-- A crossing index lies before the word end and brackets the threshold. -/
def Crossing (q : ℝ) (w : ValuationWord) (k : ℕ) : Prop :=
  k < w.length ∧ (ValuationWord.total (w.take k) : ℝ) ≤ q ∧
    q < (ValuationWord.total (w.take (k + 1)) : ℝ)

/-- Two crossing indices of the same word and threshold must agree. -/
theorem Crossing.eq {q : ℝ} {w : ValuationWord} {i j : ℕ}
    (hi : Crossing q w i) (hj : Crossing q w j) : i = j := by
  have hnot (a b : ℕ) (ha : Crossing q w a) (hb : Crossing q w b) : ¬ a < b := by
    intro hab
    have hm : (ValuationWord.total (w.take (a + 1)) : ℝ) ≤
        (ValuationWord.total (w.take b) : ℝ) := by
      exact_mod_cast ValuationWord.total_take_mono w (Nat.succ_le_of_lt hab)
    linarith [ha.2.2, hb.2.1]
  have := hnot i j hi hj
  have := hnot j i hj hi
  omega

/-- Every nonnegative threshold below the total has a unique first crossing. -/
theorem existsUnique_crossing {q : ℝ} {w : ValuationWord}
    (hq : 0 ≤ q) (hw : q < (w.total : ℝ)) : ∃! k : ℕ, Crossing q w k := by
  classical
  have hlen : 0 < w.length := by
    by_contra h
    have he : w = [] := List.length_eq_zero_iff.mp (by omega)
    simp [he, ValuationWord.total] at hw
    linarith
  let P : ℕ → Prop := fun k => k < w.length ∧ q < ((ValuationWord.total (w.take (k + 1))) : ℝ)
  have hex : ∃ k, P k := by
    refine ⟨w.length - 1, by omega, ?_⟩
    simpa only [show w.length - 1 + 1 = w.length by omega, List.take_length] using hw
  let K := Nat.find hex
  have hK : P K := Nat.find_spec hex
  have hlow : ((ValuationWord.total (w.take K)) : ℝ) ≤ q := by
    by_cases hzero : K = 0
    · simpa [hzero, ValuationWord.total] using hq
    · by_contra h
      have hpred : P (K - 1) := by
        refine ⟨by omega, ?_⟩
        simpa only [show K - 1 + 1 = K by omega] using lt_of_not_ge h
      exact Nat.find_min hex (by omega : K - 1 < K) hpred
  refine ⟨K, ⟨hK.1, hlow, hK.2⟩, ?_⟩
  intro k hk
  exact hk.eq ⟨hK.1, hlow, hK.2⟩

end Head
end WordCertDensity
