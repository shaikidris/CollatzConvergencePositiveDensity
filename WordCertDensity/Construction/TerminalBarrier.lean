/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalParameters

/-! # Finite terminal words at the first eligible barrier crossing

The lower-endpoint miss is retained. All comparisons are between integers,
and the finite family is enumerated by the existing positive compositions.
Original reference weights are never normalized after selection.
-/

namespace WordCertDensity.Construction

/-- Literal terminal first-crossing conditions with a bounded integer test. -/
def TerminalWord (b u K : ℕ) (w : ValuationWord) : Prop :=
  terminalLow b < w.length ∧ w.length ≤ terminalHigh b ∧
    (∀ s ∈ Finset.Ico (terminalLow b) w.length,
      (ValuationWord.total (w.take s) : ℤ) < terminalBarrier b u s) ∧
    0 ≤ (w.total : ℤ) - terminalBarrier b u w.length ∧
    (w.total : ℤ) - terminalBarrier b u w.length ≤ K

instance (b u K : ℕ) (w : ValuationWord) : Decidable (TerminalWord b u K w) := by
  unfold TerminalWord
  infer_instance

/-- The bounded test is exactly the manuscript's quantified interval of misses. -/
theorem terminalWord_iff (b u K : ℕ) (w : ValuationWord) :
    TerminalWord b u K w ↔
      terminalLow b < w.length ∧ w.length ≤ terminalHigh b ∧
      (∀ s : ℕ, terminalLow b ≤ s → s < w.length →
        (ValuationWord.total (w.take s) : ℤ) < terminalBarrier b u s) ∧
      0 ≤ (w.total : ℤ) - terminalBarrier b u w.length ∧
      (w.total : ℤ) - terminalBarrier b u w.length ≤ K := by
  simp only [TerminalWord, Finset.mem_Ico, and_imp]

/-- Every selected word includes the required miss at the lower endpoint. -/
theorem terminalWord_miss_low {b u K : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) :
    (ValuationWord.total (w.take (terminalLow b)) : ℤ) < terminalBarrier b u (terminalLow b) :=
  hw.2.2.1 _ (Finset.mem_Ico.mpr ⟨le_refl _, hw.1⟩)

/-- A selected crossing has positive depth. -/
theorem terminalWord_nonempty {b u K : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) : w ≠ [] := by
  intro he
  subst w
  have h := hw.1
  simp at h

/-- A proper extension of a selected word has already had an eligible crossing. -/
theorem terminalWord_prefix_eq {b u K : ℕ} {v w : ValuationWord}
    (hv : TerminalWord b u K v) (hw : TerminalWord b u K w) (hp : v <+: w) : v = w := by
  by_cases he : v.length = w.length
  · exact hp.eq_of_length he
  · have hlt : v.length < w.length := lt_of_le_of_ne hp.length_le he
    have hmiss := hw.2.2.1 v.length (Finset.mem_Ico.mpr ⟨hv.1.le, hlt⟩)
    have ht : w.take v.length = v := (List.prefix_iff_eq_take.mp hp).symm
    rw [ht] at hmiss
    have hhit := hv.2.2.2.1
    omega

/-- A finite integer cap on the total valuation of every selected word. -/
def terminalTotalBound (b u K : ℕ) : ℕ :=
  (terminalBarrier b u (terminalHigh b) + K).toNat

/-- Barrier monotonicity and capped overshoot bound the total, including empty-family cases. -/
theorem terminalWord_total_le {b u K : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) : w.total ≤ terminalTotalBound b u K := by
  have hb := terminalBarrier_mono b u hw.2.1
  have hc := hw.2.2.2.2
  have h : (w.total : ℤ) ≤ terminalBarrier b u (terminalHigh b) + K := by omega
  simpa only [Int.toNat_natCast, terminalTotalBound] using Int.toNat_le_toNat h

/-- Computable complete enumeration of the terminal family. -/
def terminalWords (b u K : ℕ) : Finset ValuationWord :=
  (wordsBelow (terminalTotalBound b u K + 1)).filter (TerminalWord b u K)

/-- The finite enumeration omits no word satisfying the literal crossing rule. -/
theorem mem_terminalWords (b u K : ℕ) (w : ValuationWord) :
    w ∈ terminalWords b u K ↔ TerminalWord b u K w := by
  rw [terminalWords, Finset.mem_filter, mem_wordsBelow]
  exact ⟨And.right, fun hw => ⟨Nat.lt_succ_of_le (terminalWord_total_le hw), hw⟩⟩

/-- The full manuscript-defined set is finite, for every finite overshoot cap. -/
theorem terminalWords_finite (b u K : ℕ) : Set.Finite {w | TerminalWord b u K w} := by
  apply (terminalWords b u K).finite_toSet.subset
  intro w hw
  exact (mem_terminalWords b u K w).mpr hw

/-- The actual finite family is prefix-free, without discarding its lower miss. -/
theorem terminalWords_prefixFree (b u K : ℕ) :
    (terminalWords b u K : Set ValuationWord).Pairwise (fun v w => ¬ v <+: w) := by
  intro v hv w hw hne hp
  exact hne (terminalWord_prefix_eq ((mem_terminalWords b u K v).mp hv)
    ((mem_terminalWords b u K w).mp hw) hp)

/-- Every enumerated word respects the upper terminal depth. -/
theorem terminalWords_depth {b u K : ℕ} {w : ValuationWord}
    (hw : w ∈ terminalWords b u K) : w.length ≤ terminalHigh b :=
  ((mem_terminalWords b u K w).mp hw).2.1

/-- Increasing the cap keeps all original selected words and their original weights. -/
theorem terminalWords_mono_cap (b u : ℕ) {K M : ℕ} (hKM : K ≤ M) :
    terminalWords b u K ⊆ terminalWords b u M := by
  intro w hw
  rw [mem_terminalWords] at hw ⊢
  refine ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, ?_⟩
  exact hw.2.2.2.2.trans (Int.ofNat_le.mpr hKM)

/-- Unnormalized mass of the original terminal words. -/
noncomputable def terminalMass (b u K : ℕ) : ℝ :=
  Reference.stoppingMass (terminalWords b u K)

/-- Original terminal mass is a subprobability, also when no word is selected. -/
theorem terminalMass_bounds (b u K : ℕ) : 0 ≤ terminalMass b u K ∧ terminalMass b u K ≤ 1 :=
  ⟨Reference.stoppingMass_nonneg _,
    Reference.stoppingMass_le_one _ (terminalWords_prefixFree b u K)⟩

/-- The finite mass is exactly the reference event of having a selected prefix. -/
theorem terminalWords_probability (b u K n : ℕ) (hn : terminalHigh b ≤ n) :
    Gated.probability (Reference.wordPMF n) (Reference.prefixFamilyEvent (terminalWords b u K)) =
      terminalMass b u K := by
  apply Reference.prefixFamily_probability _ _ (terminalWords_prefixFree b u K)
  intro w hw
  exact (terminalWords_depth hw).trans hn

end WordCertDensity.Construction
