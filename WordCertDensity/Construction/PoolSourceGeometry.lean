/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.PoolCommonShell
import WordCertDensity.Construction.TerminalClock
import WordCertDensity.Construction.FanCharge

/-! # Actual pooled reduced sources satisfy the complete physical source conditions -/

namespace WordCertDensity.Construction
open Filter
open scoped Topology Classical

/-- Every member of the literal source set has a retained root and a retained reduced record. -/
theorem reducedSourceSet_witness {L δ X : ℝ} {b t j d x : ℕ} {pool : Finset ℕ}
    (hx : x ∈ reducedSourceSet L δ X b t j d pool) :
    ∃ root ∈ pool, ∃ r ∈ selectedTerminalRecords L δ X b t j root d 1,
      terminalRecordSource root r = x := by
  obtain ⟨root,hroot,hr⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hr
  exact ⟨root,hroot,r,hr,he⟩

/-- A selected full history retains its physical terminal parent exactly. -/
theorem selectedTerminalRecord_child {L δ X : ℝ} {b t j root d K : ℕ}
    {r : GraftRecord × ValuationWord}
    (hr : r ∈ selectedTerminalRecords L δ X b t j root d K) :
    PhysicalHistory r.2 (graftRecordSource root r.1) (terminalRecordSource root r) := by
  have hm := (mem_selectedTerminalRecords L δ X b t j root d K r.1 r.2).mp hr
  obtain ⟨middle,hpre,hchild⟩ := hm.2.2.append_split
  have he := hpre.source_unique ((mem_physicalGraftRecords L δ b t j root r.1).mp hm.1).2
  simpa only [he] using hchild

/-- At one fixed graft, every later common cutoff has the original finite physical source data. -/
theorem finitePool_reducedSources_eventually {θ L c : ℝ} {b t target : ℕ}
    (hθ : 0 < θ) (hcap : θ ≤ 1/1000) (hL : 0 < L)
    (hc : criticalClock+3*θ ≤ c) (hb : 32^5 ≤ b)
    (hpaid : graftOffsetAbsorption b t ≤ 1)
    (pool : Finset ℕ) (hne : pool.Nonempty) (clock : ℕ → ℕ)
    (hP : NonrecurrentPool acceleratedStep (pool : Set ℕ))
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
      ∀ x ∈ reducedSourceSet L (θ/20) X b t j d pool,
        Odd x ∧ x ∈ goodTarget target c ∧ X ≤ (x : ℝ) ∧
        (x : ℝ)<terminalShellRadius d*X ∧
        0 ≤ reducedSourceCharge L (θ/20) X b t j d x pool ∧
        reducedSourceCharge L (θ/20) X b t j d x pool ≤ (x : ℝ)⁻¹ := by
  have hcount := macroCount_tendsto hL (graftInitialCount b t)
  have hstate := finitePool_terminal_state (L := L) (δ := θ/20) hb hpaid pool hne clock hheight hpath
  have hclocks := stoppedMean_terminalPhysical_clock hθ hcap hc
    (terminalPoolLower b pool hne) (terminalPoolClock b t pool clock) target
  filter_upwards [finitePool_commonParents_eventually hθ hcap hL hb hpaid pool hne clock hheight hpath,
    hcount.eventually hclocks,
    ((terminalDepth_tendsto hθ).comp hcount).eventually (eventually_ge_atTop 200)] with j hparents hclock hd
  dsimp only at hparents hclock hd ⊢
  change 200 ≤ ⌊θ*macroCount L (graftInitialCount b t) j⌋₊ at hd
  have hdpos : 0 < ⌊θ*macroCount L (graftInitialCount b t) j⌋₊ := by omega
  intro X hXlo hXhi x hx
  obtain ⟨root,hroot,r,hr,rfl⟩ := reducedSourceSet_witness hx
  have hm := (mem_selectedTerminalRecords L (θ/20) X b t j root _ 1 r.1 r.2).mp hr
  have hshell := hparents X hXlo hXhi root hroot r.1 hm.1
  have hterm := (mem_terminalWords _ _ _ _).mp hm.2.1
  have hchild := selectedTerminalRecord_child hr
  have hbounds := terminalPhysical_selected hdpos hshell.1 hshell.2.1 hshell.2.2 hterm hchild
  have hshift := (terminalSelector_spec _ _ X hshell.2.1 hshell.2.2).2.1
  have hparent := hstate j root hroot r.1 hm.1
  have hreach := hclock _ _ _ _ hshift hterm hshell.1 hchild hparent.1 hparent.2.2
  exact ⟨hm.2.2.source_odd, ⟨hm.2.2.source_pos,hreach⟩, hbounds.1, hbounds.2,
    reducedSourceCharge_nonneg _ _ _ _ _ _ _ _ _, reducedSourceCharge_le (by omega) hP⟩

end WordCertDensity.Construction
