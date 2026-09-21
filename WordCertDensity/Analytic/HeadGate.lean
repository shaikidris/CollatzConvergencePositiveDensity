/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

Head-selection and scalar arguments adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The original LICENSE
and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
This version uses the local positive valuation words and the full manuscript width range.
-/
module

public import WordCertDensity.Analytic.Typical
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The actual typical-head gate and finite ranges

A head is the first crossing of Q, is itself typical, and has its original
length and total. Every globally typical word supplies exactly one such head.
These facts do not impose any conditioning on the remaining independent tail.
-/

@[expose] public section

namespace WordCertDensity
namespace Head

/-- A typical head with fixed crossing index k and original total l. -/
structure Gate (v : ℝ) (n k l : ℕ) (w : ValuationWord) : Prop where
  /-- The head includes its first crossing letter. -/
  length_eq : w.length = k + 1
  /-- The head itself obeys the ambient interval bounds. -/
  typical : Typical v n w
  /-- The preceding prefix has not crossed the threshold. -/
  prefix_le : ((ValuationWord.total (w.take k)) : ℝ) ≤ gateLevel v n
  /-- The full head is beyond the threshold. -/
  lt_total : gateLevel v n < (w.total : ℝ)
  /-- The original valuation total is the slice parameter. -/
  total_eq : w.total = l

/-- Prefix typicality and the first crossing give the actual head gate. -/
theorem Gate.of_crossing {v : ℝ} {n k : ℕ} {w : ValuationWord}
    (h : Typical v n w) (hc : Crossing (gateLevel v n) w k) :
    Gate v n k (ValuationWord.total (w.take (k + 1))) (w.take (k + 1)) := by
  refine ⟨List.length_take_of_le (Nat.succ_le_of_lt hc.1), h.take (k + 1), ?_, hc.2.2, rfl⟩
  simpa only [List.take_take, Nat.min_eq_left (Nat.le_succ k)] using hc.2.1

/-- The first scalar budget forces every nonempty head into the conductor-compatible index range. -/
theorem Gate.index_le {v : ℝ} {n k l : ℕ} {w : ValuationWord}
    (hlog : 0 < Real.log (n : ℝ))
    (hb : ((3 / 2 : ℝ) * v ^ 2 + v) * Real.log (n : ℝ) ≤ (3 / 200 : ℝ) * n)
    (h : Gate v n k l w) : 20 * k ≤ 17 * n := by
  by_cases hk : k = 0
  · omega
  have hp := h.typical.prefix_lower (Nat.pos_of_ne_zero hk) (by rw [h.length_eq]; omega)
  have hy := young_index (v := v) (s := (k : ℝ)) hlog (by positivity)
  have hmain : (19 / 10 : ℝ) * k ≤ (n : ℝ) * logRatio +
      ((3 / 2 : ℝ) * v ^ 2 + v) * Real.log (n : ℝ) := by
    have hc := h.prefix_le
    unfold gateLevel at hc
    nlinarith
  have hn : 0 < n := by
    by_contra hzero
    have : n = 0 := by omega
    simp [this] at hlog
  have hratio := mul_lt_mul_of_pos_left logRatio_lt_eight_fifths
    (by exact_mod_cast hn : (0 : ℝ) < n)
  have hstrict : (20 : ℝ) * k < 17 * n := by nlinarith
  exact_mod_cast hstrict.le

/-- The last typical singleton gives the original total's exact overshoot window. -/
theorem Gate.total_range {v : ℝ} {n k l : ℕ} {w : ValuationWord}
    (hv : 17 ≤ v) (hlog : 4 ≤ Real.log (n : ℝ)) (h : Gate v n k l w) :
    gateLevel v n < (l : ℝ) ∧ (l : ℝ) ≤ gateLevel v n + 2 * v * Real.log (n : ℝ) := by
  have hsingle := h.typical k (k + 1) (by omega) (by rw [h.length_eq])
  have hs : |(intervalSum w k (k + 1) : ℝ) - 2| ≤
      v * (Real.sqrt (Real.log (n : ℝ)) + Real.log (n : ℝ)) := by simpa using hsingle
  have hsplit : (l : ℝ) = (ValuationWord.total (w.take k) : ℝ) +
      (intervalSum w k (k + 1) : ℝ) := by
    have hh := total_take_succ w k
    rw [← h.length_eq, List.take_length, h.total_eq] at hh
    rw [h.length_eq] at hh
    exact_mod_cast hh
  have hscalar := singleton_error_le hv hlog
  exact ⟨by simpa only [h.total_eq] using h.lt_total,
    by linarith [(abs_le.mp hs).2, h.prefix_le]⟩

/-- The entire overshoot window stays below twice the ambient length. -/
theorem Gate.total_lt_two_mul {v : ℝ} {n k l : ℕ} {w : ValuationWord}
    (hv : 17 ≤ v) (hn : 1 ≤ n) (hlog : 4 ≤ Real.log (n : ℝ))
    (h : Gate v n k l w) : l < 2 * n := by
  have hr := h.total_range hv hlog
  have hcoeff : -v ^ 2 + 2 * v ≤ 0 := by nlinarith
  have hrem := mul_nonpos_of_nonpos_of_nonneg hcoeff (by linarith : 0 ≤ Real.log (n : ℝ))
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hratio := mul_lt_mul_of_pos_left logRatio_lt_eight_fifths hnreal
  have hl : (l : ℝ) < 2 * (n : ℝ) := by
    unfold gateLevel at hr
    nlinarith [hr.2]
  exact_mod_cast hl

/-- The second scalar budget puts Q strictly between zero and every global typical total. -/
theorem gateLevel_between {v : ℝ} {n : ℕ} {w : ValuationWord}
    (hv : 17 ≤ v) (hn : 2 ≤ n)
    (hb : ((5 / 2 : ℝ) * v ^ 2 + v) * Real.log (n : ℝ) ≤ (3 / 10 : ℝ) * n)
    (hlen : w.length = n) (ht : Typical v n w) :
    0 ≤ gateLevel v n ∧ gateLevel v n < (w.total : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hv0 : 0 ≤ v := by linarith
  have hcoeff : v ^ 2 ≤ (5 / 2 : ℝ) * v ^ 2 + v := by nlinarith [sq_nonneg v]
  have hmul := mul_le_mul_of_nonneg_right hcoeff hlog.le
  have hbudget : v ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) := by nlinarith
  have hlower := mul_lt_mul_of_pos_left one_lt_logRatio hnreal
  have hq : 0 ≤ gateLevel v n := by unfold gateLevel; nlinarith
  have hy := young_index (v := v) (s := (n : ℝ)) hlog hnreal.le
  have hp := ht.prefix_lower (by omega : 0 < n) (by omega : n ≤ w.length)
  rw [← hlen, List.take_length] at hp
  rw [hlen] at hp
  have htotal : (8 / 5 : ℝ) * n ≤ (w.total : ℝ) := by nlinarith
  have hupper := mul_lt_mul_of_pos_left logRatio_lt_eight_fifths hnreal
  have hsub := mul_nonneg (sq_nonneg v) hlog.le
  refine ⟨hq, ?_⟩
  unfold gateLevel
  nlinarith

/-- A head at the common cutoff satisfies all finite index and total guards simultaneously. -/
theorem Gate.ranges {v : ℝ} {n k l : ℕ} {w : ValuationWord}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n) (h : Gate v n k l w) :
    20 * k ≤ 17 * n ∧ gateLevel v n < (l : ℝ) ∧
      (l : ℝ) ≤ gateLevel v n + 2 * v * Real.log (n : ℝ) ∧ l < 2 * n := by
  obtain ⟨hlog, hb, _⟩ := common_margins hv hv' hn
  have hv17 : 17 ≤ v := by linarith
  have hr := h.total_range hv17 hlog.le
  exact ⟨h.index_le (by linarith) hb, hr.1, hr.2,
    h.total_lt_two_mul hv17 (by omega) hlog.le⟩

/-- Every globally typical word has exactly one head in the literal finite head families. -/
theorem existsUnique_head {v : ℝ} {n : ℕ} {w : ValuationWord}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n)
    (hlen : w.length = n) (ht : Typical v n w) :
    ∃! k : ℕ, k < n ∧ Gate v n k (ValuationWord.total (w.take (k + 1))) (w.take (k + 1)) := by
  obtain ⟨_hlog, _hb, hb'⟩ := common_margins hv hv' hn
  obtain ⟨hq, htotal⟩ := gateLevel_between (by linarith : 17 ≤ v) (by omega) hb' hlen ht
  obtain ⟨k, hk, _⟩ := existsUnique_crossing hq htotal
  refine ⟨k, ⟨by simpa only [hlen] using hk.1, Gate.of_crossing ht hk⟩, ?_⟩
  intro j hj
  have hc : Crossing (gateLevel v n) w j := by
    refine ⟨by simpa only [hlen] using hj.1, ?_, hj.2.lt_total⟩
    simpa only [List.take_take, Nat.min_eq_left (Nat.le_succ j)] using hj.2.prefix_le
  exact hc.eq hk

end Head
end WordCertDensity
