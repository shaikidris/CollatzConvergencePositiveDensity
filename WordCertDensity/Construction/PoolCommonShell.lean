/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.CommonShell
import WordCertDensity.Construction.TerminalState
import WordCertDensity.Construction.TerminalPrecisionLimit

/-! # One common interval for all parents in a fixed root pool -/

namespace WordCertDensity.Construction
open Filter
open scoped Topology

/-- Deterministic pool bounds discharge every parent's terminal shell premises at late stages. -/
theorem finitePool_commonParents_eventually {θ L : ℝ} {b t target : ℕ}
    (hθ : 0 < θ) (hcap : θ ≤ 1/1000) (hL : 0 < L)
    (hb : 32^5 ≤ b) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (pool : Finset ℕ) (hne : pool.Nonempty) (clock : ℕ → ℕ)
    (hheight : ∀ root ∈ pool, 16^b ≤ root)
    (hpath : ∀ root ∈ pool, ReachesIn root target (clock root)) :
    ∀ᶠ j : ℕ in atTop,
      let B := macroCount L (graftInitialCount b t) j
      let d := ⌊θ*B⌋₊
      ∀ X : ℝ,
      (2 : ℝ)^commonLowExponent θ (stoppedExpectation displacement)
        (terminalPoolUpper b t pool) B < X →
      X ≤ (2 : ℝ)^commonHighExponent θ (stoppedExpectation displacement)
        (terminalPoolLower b pool hne) B →
      ∀ root ∈ pool, ∀ r ∈ physicalGraftRecords L (θ/20) b t j root,
        16^d ≤ graftRecordSource root r ∧
        terminalShellLow d (graftRecordSource root r) < X ∧
        X ≤ (2 : ℝ)^(2*terminalRadius d)*terminalShellLow d (graftRecordSource root r) := by
  have hcount := macroCount_tendsto hL (graftInitialCount b t)
  have hlarge := commonParent_height_eventually hθ.le hcap stoppedExpectation_displacement_lower
    (terminalPoolLower b pool hne)
  have hstate := finitePool_terminal_state (L := L) (δ := θ/20) hb hpaid pool hne clock hheight hpath
  filter_upwards [hcount.eventually hlarge,
    ((terminalDepth_tendsto hθ).comp hcount).eventually (eventually_ge_atTop 1)] with j hguard hd
  dsimp only at hguard hd ⊢
  change 1 ≤ ⌊θ*macroCount L (graftInitialCount b t) j⌋₊ at hd
  have hdpos : 0 < ⌊θ*macroCount L (graftInitialCount b t) j⌋₊ := by omega
  intro X hXlo hXhi root hroot r hr
  obtain ⟨hlo,hhi,_⟩ := hstate j root hroot r hr
  have hyp : (0 : ℝ)<graftRecordSource root r := by
    exact_mod_cast ((mem_physicalGraftRecords L (θ/20) b t j root r).mp hr).2.source_pos
  have hh := hguard _ hyp hlo
  exact ⟨by exact_mod_cast hh, commonParent_shell hdpos hyp hlo hhi hXlo hXhi⟩

end WordCertDensity.Construction
