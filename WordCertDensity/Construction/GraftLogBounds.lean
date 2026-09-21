/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedPrefixBounds
import WordCertDensity.Construction.GraftRecords

/-! # Actual graft-source heights and specified target clocks

Physical affine identities, the paid total offset and the appended corridors
supply the terminal input at every retained record, without selecting extrema
from a possibly empty retained family.
-/

namespace WordCertDensity.Construction

/-- Binary logarithm used for physical height coordinates. -/
noncomputable def binaryLog (x : ℝ) : ℝ := Real.log x / Real.log 2

theorem binaryLog_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    binaryLog x ≤ binaryLog y := by
  exact div_le_div_of_nonneg_right
    ((Real.log_le_log_iff hx (hx.trans_le hxy)).mpr hxy)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- The surviving parent height is positive on a physical history. -/
theorem physical_surviving_height {w : ValuationWord} {root x : ℕ}
    (hp : PhysicalHistory w root x) : 0 < (root : ℝ) - (w.offset : ℝ) := by
  have ha : (root : ℝ) = Transfer.weight w * x + (w.offset : ℝ) := by
    have h := congrArg (fun a : ℚ => (a : ℝ)) hp.affine_eq
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Transfer.weight] using h
  have hx : (0 : ℝ) < x := by exact_mod_cast hp.source_pos
  nlinarith [mul_pos (Transfer.weight_pos w) hx]

/-- Exact source height in binary displacement coordinates. -/
theorem physical_binaryLog {w : ValuationWord} {root x : ℕ}
    (hp : PhysicalHistory w root x) :
    binaryLog x = displacement w + binaryLog ((root : ℝ) - (w.offset : ℝ)) := by
  have ha : (root : ℝ) - (w.offset : ℝ) = Transfer.weight w * x := by
    have h := congrArg (fun a : ℚ => (a : ℝ)) hp.affine_eq
    have he : (root : ℝ) = Transfer.weight w * x + (w.offset : ℝ) := by
      simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Transfer.weight] using h
    linarith
  have hx : (0 : ℝ) < x := by exact_mod_cast hp.source_pos
  have hl : Real.log ((root : ℝ) - (w.offset : ℝ)) =
      -displacement w * Real.log 2 + Real.log x := by
    rw [ha, Real.log_mul (ne_of_gt (Transfer.weight_pos w)) (ne_of_gt hx), log_weight_eq]
  have htwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold binaryLog
  field_simp
  nlinarith

/-- One record satisfies the three terminal-state estimates with fixed external bounds. -/
theorem physicalGraftRecord_terminal_bounds {L δ lo hi : ℝ} {b t j root target T : ℕ}
    (hb : 32 ^ 5 ≤ b) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hlo : (2 : ℝ)^(b+1)+1 < lo) (hrootlo : lo ≤ root) (hroothi : (root : ℝ) ≤ hi)
    (hpath : ReachesIn root target T) {r : GraftRecord}
    (hr : r ∈ physicalGraftRecords L δ b t j root) :
    let B := macroCount L (graftInitialCount b t) j
    let x := graftRecordSource root r
    (stoppedExpectation displacement-δ)*B + binaryLog (lo-((2 : ℝ)^(b+1)+1)) ≤
        binaryLog x ∧
      binaryLog x ≤ (stoppedExpectation displacement+δ)*B + binaryLog hi +
        seedPrefixValuationBound b t ∧
      ReachesWithin x target
        ((stoppedExpectation (fun w => (w.ordinaryCost : ℝ))+δ)*B + seedPrefixClockBound b t + T) := by
  obtain ⟨hrecord, hp⟩ := (mem_physicalGraftRecords L δ b t j root r).mp hr
  obtain ⟨hlen, hpre, hw, hmlen, hmacro⟩ := (mem_graftRecords L δ b t j r).mp hrecord
  have hc : MacroCorridor δ (macroCount L (graftInitialCount b t) j)
      (r.2.1 ++ r.2.2.flatten) := by
    simpa only [hmlen] using graftAppended_corridor hw hmacro
  have hprefix := seedBlocks_displacement_bounds hb hpre
  rw [hlen] at hprefix
  have hoff : (ValuationWord.offset (graftRecordWord r) : ℝ) < (2 : ℝ)^(b+1)+1 :=
    graftTotal_offset hb hpre hlen hw hmacro hpaid
  have hoff0 : (0 : ℝ) ≤ (ValuationWord.offset (graftRecordWord r) : ℝ) :=
    Rat.cast_nonneg.mpr (ValuationWord.offset_nonneg _)
  have hlower := binaryLog_mono (sub_pos.mpr hlo)
    (show lo-((2 : ℝ)^(b+1)+1) ≤ (root : ℝ)-(ValuationWord.offset (graftRecordWord r) : ℝ)
      by linarith)
  have hupper := binaryLog_mono (physical_surviving_height hp)
    (show (root : ℝ)-(ValuationWord.offset (graftRecordWord r) : ℝ) ≤ hi by linarith)
  have hlog := physical_binaryLog hp
  have hd : displacement (graftRecordWord r) = displacement r.1.flatten +
      displacement (r.2.1 ++ r.2.2.flatten) := by
    simpa [graftRecordWord] using
      displacement_flatten [r.1.flatten, r.2.1 ++ r.2.2.flatten]
  rw [hd] at hlog
  obtain ⟨hylo, hyhi⟩ := abs_le.mp hc.1
  obtain ⟨_, hclock⟩ := abs_le.mp hc.2
  dsimp only
  refine ⟨by nlinarith [hprefix.1], by nlinarith [hprefix.2], ?_⟩
  refine ⟨(graftRecordWord r).ordinaryCost+T, hp.reachesIn.trans hpath, ?_⟩
  have ht := (seedBlocks_prefix_bounds hpre).2
  rw [hlen] at ht
  have htR : ((ValuationWord.ordinaryCost r.1.flatten) : ℝ) ≤ seedPrefixClockBound b t := by exact_mod_cast ht
  simp only [graftRecordWord, ValuationWord.ordinaryCost_append, Nat.cast_add]
  simp only [ValuationWord.ordinaryCost_append, Nat.cast_add] at hclock
  nlinarith

end WordCertDensity.Construction
