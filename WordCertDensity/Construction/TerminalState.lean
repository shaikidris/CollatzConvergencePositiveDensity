/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftLogBounds

/-! # One terminal input state for a fixed finite root pool

The constants use the pool's minimum, maximum and specified target paths.
They are fixed before the continuation stage and require no nonemptiness
assumption on an individual retained physical family.
-/

namespace WordCertDensity.Construction

/-- Uniform terminal-state estimates from any certified fixed pool bounds. -/
theorem fixedPool_terminal_bounds {L δ lo hi : ℝ} {b t target T : ℕ}
    (hb : 32 ^ 5 ≤ b) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hlo : (2 : ℝ)^(b+1)+1 < lo) (pool : Finset ℕ) (clock : ℕ → ℕ)
    (hpool : ∀ root ∈ pool, lo ≤ root ∧ (root : ℝ) ≤ hi ∧ clock root ≤ T ∧
      ReachesIn root target (clock root)) :
    ∀ j root, root ∈ pool → ∀ r ∈ physicalGraftRecords L δ b t j root,
      let B := macroCount L (graftInitialCount b t) j
      let x := graftRecordSource root r
      (stoppedExpectation displacement-δ)*B + binaryLog (lo-((2 : ℝ)^(b+1)+1)) ≤
          binaryLog x ∧
        binaryLog x ≤ (stoppedExpectation displacement+δ)*B + binaryLog hi +
          seedPrefixValuationBound b t ∧
        ReachesWithin x target
          ((stoppedExpectation (fun w => (w.ordinaryCost : ℝ))+δ)*B + seedPrefixClockBound b t + T) := by
  intro j root hroot r hr
  obtain ⟨hmin, hmax, hclock, hpath⟩ := hpool root hroot
  obtain ⟨hlo', hhi', ht⟩ :=
    physicalGraftRecord_terminal_bounds hb hpaid hlo hmin hmax hpath hr
  refine ⟨hlo', hhi', ht.mono ?_⟩
  have hc : (clock root : ℝ) ≤ T := by exact_mod_cast hclock
  linarith

/-- The lower additive height constant of the fixed nonempty pool. -/
noncomputable def terminalPoolLower (b : ℕ) (pool : Finset ℕ) (hpool : pool.Nonempty) : ℝ :=
  binaryLog ((pool.min' hpool : ℝ)-((2 : ℝ)^(b+1)+1))

/-- The upper additive height constant uses the fixed pool maximum and prefix budget. -/
noncomputable def terminalPoolUpper (b t : ℕ) (pool : Finset ℕ) : ℝ :=
  binaryLog (pool.sup id : ℕ) + seedPrefixValuationBound b t

/-- The fixed ordinary overhead contains the prefix and the specified root-to-target paths. -/
noncomputable def terminalPoolClock (b t : ℕ) (pool : Finset ℕ) (clock : ℕ → ℕ) : ℝ :=
  seedPrefixClockBound b t + pool.sup clock

/-- Literal deterministic constants work over the whole pool at every retained record. -/
theorem finitePool_terminal_state {L δ : ℝ} {b t target : ℕ}
    (hb : 32 ^ 5 ≤ b) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (pool : Finset ℕ) (hne : pool.Nonempty) (clock : ℕ → ℕ)
    (hheight : ∀ root ∈ pool, 16^b ≤ root)
    (hpath : ∀ root ∈ pool, ReachesIn root target (clock root)) :
    ∀ j root, root ∈ pool → ∀ r ∈ physicalGraftRecords L δ b t j root,
      let B := macroCount L (graftInitialCount b t) j
      let x := graftRecordSource root r
      (stoppedExpectation displacement-δ)*B + terminalPoolLower b pool hne ≤ binaryLog x ∧
      binaryLog x ≤ (stoppedExpectation displacement+δ)*B + terminalPoolUpper b t pool ∧
      ReachesWithin x target
        ((stoppedExpectation (fun w => (w.ordinaryCost : ℝ))+δ)*B + terminalPoolClock b t pool clock) := by
  have hmin : (16 : ℝ)^b ≤ (pool.min' hne : ℝ) := by
    exact_mod_cast hheight _ (pool.min'_mem hne)
  have hlo := (graftOffset_ceiling_lt (by omega : 1 ≤ b)).trans_le hmin
  have hp : ∀ root ∈ pool,
      (pool.min' hne : ℝ) ≤ root ∧ (root : ℝ) ≤ pool.sup id ∧ clock root ≤ pool.sup clock ∧
        ReachesIn root target (clock root) := by
    intro root hr
    refine ⟨?_, ?_, Finset.le_sup hr, hpath root hr⟩
    · exact_mod_cast pool.min'_le root hr
    · exact_mod_cast (Finset.le_sup (f := id) hr)
  intro j root hroot r hr
  have h := fixedPool_terminal_bounds (L := L) (δ := δ) hb hpaid hlo pool clock hp j root hroot r hr
  simpa only [terminalPoolLower, terminalPoolUpper, terminalPoolClock, add_assoc] using h

end WordCertDensity.Construction
