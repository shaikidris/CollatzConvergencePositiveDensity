/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalBarrier
import WordCertDensity.Reference.PrefixTail

/-! # Finite prefixes just before an eligible terminal hit

Every tested prefix still misses its barrier. This bounds its total and makes
the next-letter threshold strictly positive, including the first eligible hit.
-/

namespace WordCertDensity.Construction

/-- An eligible incoming prefix, including its current miss. -/
def TerminalBefore (b u : ℕ) (v : ValuationWord) : Prop :=
  terminalLow b ≤ v.length ∧ v.length < terminalHigh b ∧
    ∀ s ∈ Finset.Icc (terminalLow b) v.length,
      (ValuationWord.total (v.take s) : ℤ) < terminalBarrier b u s

instance (b u : ℕ) (v : ValuationWord) : Decidable (TerminalBefore b u v) := by
  unfold TerminalBefore
  infer_instance

/-- A before-hit prefix misses at its own last depth. -/
theorem terminalBefore_miss {b u : ℕ} {v : ValuationWord} (hv : TerminalBefore b u v) :
    (v.total : ℤ) < terminalBarrier b u v.length := by
  simpa using hv.2.2 v.length (Finset.mem_Icc.mpr ⟨hv.1, le_refl _⟩)

/-- The total of a before-hit prefix has a uniform strict finite bound. -/
theorem terminalBefore_total_lt {b u : ℕ} {v : ValuationWord}
    (hv : TerminalBefore b u v) :
    v.total < (terminalBarrier b u (terminalHigh b)).toNat := by
  have h := (terminalBefore_miss hv).trans_le (terminalBarrier_mono b u hv.2.1.le)
  omega

/-- Complete finite enumeration of prefixes before their next eligible hit. -/
def terminalBefores (b u : ℕ) : Finset ValuationWord :=
  (wordsBelow (terminalBarrier b u (terminalHigh b)).toNat).filter (TerminalBefore b u)

/-- The enumeration includes every before-hit prefix and no other word. -/
theorem mem_terminalBefores (b u : ℕ) (v : ValuationWord) :
    v ∈ terminalBefores b u ↔ TerminalBefore b u v := by
  rw [terminalBefores, Finset.mem_filter, mem_wordsBelow]
  exact ⟨And.right, fun hv => ⟨terminalBefore_total_lt hv, hv⟩⟩

/-- Positive next-letter threshold; the maximum is inactive on before-hit prefixes. -/
def terminalGap (b u : ℕ) (v : ValuationWord) : ℕ+ :=
  ⟨max 1 (terminalBarrier b u (v.length + 1) - (v.total : ℤ)).toNat, by omega⟩

/-- On every eligible prefix the positive threshold equals the literal integer difference. -/
theorem terminalGap_eq {b u : ℕ} {v : ValuationWord} (hv : TerminalBefore b u v) :
    ((terminalGap b u v : ℕ) : ℤ) = terminalBarrier b u (v.length + 1) - v.total := by
  have h := (terminalBefore_miss hv).trans_le
    (terminalBarrier_mono b u (Nat.le_succ v.length))
  change (v.total : ℤ) < terminalBarrier b u (v.length + 1) at h
  unfold terminalGap
  simp only [PNat.mk_coe]
  omega

/-- Append the unique next valuation with prescribed nonnegative overshoot. -/
def terminalLanding (b u : ℕ) (v : ValuationWord) (j : ℕ) : ValuationWord :=
  v ++ [Reference.raisedLetter (terminalGap b u v) j]

/-- The next-letter construction retains the exact integer overshoot. -/
theorem terminalLanding_overshoot {b u : ℕ} {v : ValuationWord}
    (hv : TerminalBefore b u v) (j : ℕ) :
    (ValuationWord.total (terminalLanding b u v j) : ℤ) -
      terminalBarrier b u (terminalLanding b u v j).length = j := by
  have hg := terminalGap_eq hv
  rw [terminalLanding, ValuationWord.total_append]
  simp only [List.length_append, List.length_cons, List.length_nil]
  change ((v.total + (Reference.raisedLetter (terminalGap b u v) j : ℕ) : ℕ) : ℤ) -
    terminalBarrier b u (v.length + 1) = j
  rw [Reference.raisedLetter_val]
  push_cast
  omega

/-- A constructed landing is retained exactly when its overshoot is within the cap. -/
theorem terminalLanding_mem_iff {b u : ℕ} {v : ValuationWord}
    (hv : TerminalBefore b u v) (j K : ℕ) :
    TerminalWord b u K (terminalLanding b u v j) ↔ j ≤ K := by
  have hl : (terminalLanding b u v j).length = v.length + 1 := by simp [terminalLanding]
  have ho := terminalLanding_overshoot hv j
  have hvl := hv.1
  have hvh := hv.2.1
  rw [terminalWord_iff]
  constructor
  · intro h
    have hcap := h.2.2.2.2
    rw [ho] at hcap
    exact_mod_cast hcap
  · intro hj
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro s hs hsd
      have hsl : s ≤ v.length := by omega
      simp only [terminalLanding, List.take_append, Nat.sub_eq_zero_of_le hsl,
        List.take_zero, List.append_nil]
      exact hv.2.2 s (Finset.mem_Icc.mpr ⟨hs, hsl⟩)
    · rw [ho]
      exact Nat.cast_nonneg _
    · rw [ho]
      exact_mod_cast hj

end WordCertDensity.Construction
