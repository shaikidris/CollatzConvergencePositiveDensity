/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalBarrier
import WordCertDensity.Construction.TerminalTails

/-! # Uncapped terminal crossing and its original probability

A lower-endpoint miss followed by an upper-endpoint hit supplies a first
eligible prefix with some finite cap. Failure of this event costs only the
two endpoint tails. The loss from imposing a specified cap is separate.
-/

namespace WordCertDensity.Construction

/-- A genuine eligible crossing with no prescribed overshoot cap. -/
def TerminalCrossing (b u : ℕ) (w : ValuationWord) : Prop :=
  ∃ K, Reference.prefixFamilyEvent (terminalWords b u K) w

/-- Opposite endpoint positions produce a retained first-hit prefix at some finite cap. -/
theorem exists_terminalWord_prefix {b u : ℕ} {w : ValuationWord}
    (hlen : terminalHigh b ≤ w.length)
    (hmiss : (ValuationWord.total (w.take (terminalLow b)) : ℤ) <
      terminalBarrier b u (terminalLow b))
    (hhit : terminalBarrier b u (terminalHigh b) ≤
      (ValuationWord.total (w.take (terminalHigh b)) : ℤ)) : TerminalCrossing b u w := by
  classical
  have hlh : terminalLow b ≤ terminalHigh b := by
    unfold terminalLow terminalHigh
    omega
  have hex : ∃ d : ℕ, terminalLow b ≤ d ∧ d ≤ terminalHigh b ∧
      terminalBarrier b u d ≤ (ValuationWord.total (w.take d) : ℤ) :=
    ⟨terminalHigh b, hlh, le_refl _, hhit⟩
  let d := Nat.find hex
  have hd := Nat.find_spec hex
  have hdl : terminalLow b < d := by
    change terminalLow b < Nat.find hex
    by_contra h
    have he : Nat.find hex = terminalLow b := by omega
    rw [he] at hd
    omega
  have hdlen : (w.take d).length = d := List.length_take_of_le (hd.2.1.trans hlen)
  let K := ((ValuationWord.total (w.take d) : ℤ) - terminalBarrier b u d).toNat
  refine ⟨K, w.take d, (mem_terminalWords b u K _).mpr ?_, List.take_prefix _ _⟩
  rw [terminalWord_iff, hdlen]
  refine ⟨hdl, hd.2.1, ?_, sub_nonneg.mpr hd.2.2, ?_⟩
  · intro s hls hsd
    rw [List.take_take, Nat.min_eq_left hsd.le]
    apply lt_of_not_ge
    intro hs
    exact Nat.find_min hex hsd ⟨hls, hsd.le.trans hd.2.1, hs⟩
  · dsimp [K]
    omega

/-- Failure of an uncapped eligible crossing forces one of the two endpoint deviations. -/
theorem terminalCrossing_failure {b u : ℕ} (hb : 200 ≤ b)
    (hu : u ≤ 2 * terminalRadius b) {w : ValuationWord}
    (hlen : terminalHigh b ≤ w.length) (hw : ¬ TerminalCrossing b u w) :
    2 * (terminalPrecision b : ℤ) ≤
        (ValuationWord.total (w.take (terminalLow b)) : ℤ) - 2 * terminalLow b ∨
      (ValuationWord.total (w.take (terminalHigh b)) : ℤ) - 2 * terminalHigh b <
        -2 * (terminalPrecision b : ℤ) := by
  have he := terminalBarrier_endpoints hb u
  by_cases hl : (ValuationWord.total (w.take (terminalLow b)) : ℤ) <
      terminalBarrier b u (terminalLow b)
  · right
    have hh : (ValuationWord.total (w.take (terminalHigh b)) : ℤ) <
        terminalBarrier b u (terminalHigh b) := by
      apply lt_of_not_ge
      intro hh
      exact hw (exists_terminalWord_prefix hlen hl hh)
    omega
  · left
    omega

/-- Original-law uncapped failure pays exactly the two exponential endpoint bounds. -/
theorem terminalCrossing_failure_probability {b u n : ℕ} (hb : 200 ≤ b)
    (hu : u ≤ 2 * terminalRadius b) (hn : terminalHigh b ≤ n) :
    Gated.probability (Reference.wordPMF n) (fun w => ¬ TerminalCrossing b u w) ≤
      2 * Real.exp (-(b : ℝ) / 64000) := by
  let A : ValuationWord → Prop := fun w =>
    2 * (terminalPrecision b : ℤ) ≤ (w.total : ℤ) - 2 * terminalLow b
  let B : ValuationWord → Prop := fun w =>
    (w.total : ℤ) - 2 * terminalHigh b < -2 * (terminalPrecision b : ℤ)
  have hl : terminalLow b ≤ n := by
    have h : terminalLow b ≤ terminalHigh b := by unfold terminalLow terminalHigh; omega
    exact h.trans hn
  have hm := Gated.probability_mono_on_support (Reference.wordPMF n)
    (fun w => ¬ TerminalCrossing b u w)
    (fun w => A (w.take (terminalLow b)) ∨ B (w.take (terminalHigh b)))
    (fun w hp hw => by
      have hlen := (Reference.wordPMF_mem_support_iff n w).mp
        ((PMF.mem_support_iff _ _).mpr hp)
      exact terminalCrossing_failure hb hu (by simpa only [hlen] using hn) hw)
  have hs := Gated.probability_or_le (Reference.wordPMF n)
    (fun w => A (w.take (terminalLow b))) (fun w => B (w.take (terminalHigh b)))
  have hA := Gated.probability_map (Reference.wordPMF n) (fun w => w.take (terminalLow b)) A
  have hB := Gated.probability_map (Reference.wordPMF n) (fun w => w.take (terminalHigh b)) B
  rw [Reference.wordPMF_map_take_of_le hl] at hA
  rw [Reference.wordPMF_map_take_of_le hn] at hB
  rw [← hA, ← hB] at hs
  have ha := terminalLower_tail hb
  have hb' := terminalUpper_tail hb
  change Gated.probability (Reference.wordPMF (terminalLow b)) A ≤ _ at ha
  change Gated.probability (Reference.wordPMF (terminalHigh b)) B ≤ _ at hb'
  linarith

end WordCertDensity.Construction
