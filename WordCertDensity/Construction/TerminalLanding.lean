/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalBefore
import WordCertDensity.Construction.TerminalDeficit
import WordCertDensity.Reference.PrefixTail

/-! # Exact decomposition of terminal first-hit words

The last letter is the positive barrier gap plus its nonnegative overshoot.
Different caps select the same first eligible hit, not different crossings.
-/

namespace WordCertDensity.Construction

/-- Removing the last letter of a retained word gives an eligible before-hit prefix. -/
theorem terminalWord_before {b u K : ℕ} {v : ValuationWord} {a : ℕ+}
    (hw : TerminalWord b u K (v ++ [a])) : TerminalBefore b u v := by
  have hlen : (v ++ [a]).length = v.length + 1 := by simp
  refine ⟨by have h := hw.1; omega, by have h := hw.2.1; omega, ?_⟩
  intro s hs
  obtain ⟨hls, hsl⟩ := Finset.mem_Icc.mp hs
  have h := hw.2.2.1 s (Finset.mem_Ico.mpr ⟨hls, by omega⟩)
  simpa only [List.take_append, Nat.sub_eq_zero_of_le hsl,
    List.take_zero, List.append_nil] using h

/-- A retained last letter has exactly one nonnegative overshoot within its cap. -/
theorem terminalWord_append_decompose {b u K : ℕ} {v : ValuationWord} {a : ℕ+}
    (hw : TerminalWord b u K (v ++ [a])) :
    ∃ j ≤ K, v ++ [a] = terminalLanding b u v j := by
  have hv := terminalWord_before hw
  have hg := terminalGap_eq hv
  have htotal : (ValuationWord.total (v ++ [a]) : ℤ) = (v.total : ℤ) + (a : ℕ) := by
    simp [ValuationWord.total]
  have hlen : (v ++ [a]).length = v.length + 1 := by simp
  have hlo := hw.2.2.2.1
  have hhi := hw.2.2.2.2
  rw [htotal, hlen] at hlo hhi
  let j := (a : ℕ) - (terminalGap b u v : ℕ)
  have ha : (a : ℕ) = (terminalGap b u v : ℕ) + j := by dsimp [j]; omega
  refine ⟨j, by omega, ?_⟩
  unfold terminalLanding
  exact congrArg (fun k : ℕ+ => v ++ [k]) (Subtype.ext ha)

/-- First-hit words at different caps still cannot properly extend each other. -/
theorem terminalWord_prefix_eq_caps {b u K L : ℕ} {v w : ValuationWord}
    (hv : TerminalWord b u K v) (hw : TerminalWord b u L w) (hp : v <+: w) : v = w := by
  have widen {M : ℕ} {z : ValuationWord} (hz : TerminalWord b u M z)
      (hM : M ≤ K + L) : TerminalWord b u (K + L) z :=
    (mem_terminalWords b u (K + L) z).mp
      (terminalWords_mono_cap b u hM ((mem_terminalWords b u M z).mpr hz))
  exact terminalWord_prefix_eq (widen hv (by omega)) (widen hw (by omega)) hp

/-- Uncapped crossing is exactly a union of next-letter tails over the finite incoming prefixes. -/
theorem terminalCrossing_iff_befores (b u : ℕ) (w : ValuationWord) :
    TerminalCrossing b u w ↔ ∃ v ∈ terminalBefores b u,
      Reference.PrefixTail v (terminalGap b u v) w := by
  constructor
  · rintro ⟨K, z, hz, hzw⟩
    have hz' := (mem_terminalWords b u K z).mp hz
    have he := List.dropLast_append_getLast (terminalWord_nonempty hz')
    rw [← he] at hz' hzw
    obtain ⟨j, _, hj⟩ := terminalWord_append_decompose hz'
    refine ⟨z.dropLast, (mem_terminalBefores b u _).mpr (terminalWord_before hz'), j, ?_⟩
    change terminalLanding b u z.dropLast j <+: w
    rw [← hj]
    exact hzw
  · rintro ⟨v, hv, j, hj⟩
    have hv' := (mem_terminalBefores b u v).mp hv
    refine ⟨j, terminalLanding b u v j, ?_, hj⟩
    exact (mem_terminalWords b u j _).mpr ((terminalLanding_mem_iff hv' j j).mpr le_rfl)

/-- The finite incoming-prefix events are disjoint, because they specify the first eligible hit. -/
theorem terminalBefore_events_unique {b u : ℕ} {v z w : ValuationWord}
    (hv : TerminalBefore b u v) (hz : TerminalBefore b u z)
    (hvw : Reference.PrefixTail v (terminalGap b u v) w)
    (hzw : Reference.PrefixTail z (terminalGap b u z) w) : v = z := by
  obtain ⟨i, hi⟩ := hvw
  obtain ⟨j, hj⟩ := hzw
  have hvi := (terminalLanding_mem_iff hv i i).mpr le_rfl
  have hzj := (terminalLanding_mem_iff hz j j).mpr le_rfl
  have he : terminalLanding b u v i = terminalLanding b u z j := by
    rcases List.prefix_or_prefix_of_prefix hi hj with h | h
    · exact terminalWord_prefix_eq_caps hvi hzj h
    · exact (terminalWord_prefix_eq_caps hzj hvi h).symm
  have hd := congrArg List.dropLast he
  simpa [terminalLanding] using hd

end WordCertDensity.Construction
