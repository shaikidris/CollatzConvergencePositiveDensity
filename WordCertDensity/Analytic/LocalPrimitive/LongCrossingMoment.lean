/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingLaw

/-! # Post-passage moments on one original-word horizon -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The realized post-passage height moment restricted to one exact joint
crossing. The height uses the actual longer word, not a replacement law. -/
noncomputable def longCrossingJointPower (s i h p : ℕ) (w : ValuationWord) : ENNReal := by
  classical
  exact if horizonJointEvent s h i w then
    ENNReal.ofReal ((4 / 3 : ℝ) ^ (ValuationWord.total (w.take (2 * (i + 1 + p))) - s))
  else 0

/-- The exact-joint moment on a deterministic common word horizon. -/
noncomputable def horizonJointPostPassageMoment (L s i h p : ℕ) : ENNReal :=
  ∑' w, Reference.wordPMF (2 * L) w * longCrossingJointPower s i h p w

/-- Unused future letters leave the realized exact-joint moment unchanged. -/
theorem longCrossingJointPower_take (s i h p L : ℕ) (hL : i + 1 + p ≤ L)
    (w : ValuationWord) :
    longCrossingJointPower s i h p (w.take (2 * L)) = longCrossingJointPower s i h p w := by
  have hi : 2 * i ≤ 2 * L := by omega
  have hq : 2 * (i + 1) ≤ 2 * L := by omega
  have hp : 2 * (i + 1 + p) ≤ 2 * L := by omega
  simp only [longCrossingJointPower, horizonJointEvent, List.take_take,
    Nat.min_eq_left hi, Nat.min_eq_left hq, Nat.min_eq_left hp]
  congr 1

private theorem jointPower_eq_prefix (s i h p : ℕ) (w : ValuationWord)
    (hlen : w.length = 2 * (i + 1 + p)) :
    longCrossingJointPower s i h p w =
      if pairFirstPassageEvent s (i + 1) h (w.take (2 * (i + 1))) then
        ENNReal.ofReal ((4 / 3 : ℝ) ^ (h + ValuationWord.total (w.drop (2 * (i + 1)))))
      else 0 := by
  classical
  have he := pairFirstPassageEvent_take_iff (s := s) (h := h) (i := i)
    (w := w) (by omega)
  have htake : w.take (2 * (i + 1 + p)) = w := List.take_of_length_le (by omega)
  by_cases hjoint : horizonJointEvent s h i w
  · rw [longCrossingJointPower, if_pos hjoint, if_pos (he.mpr hjoint), htake]
    have hsplit : w.total = ValuationWord.total (w.take (2 * (i + 1))) +
        ValuationWord.total (w.drop (2 * (i + 1))) := by
      rw [← ValuationWord.total_append, List.take_append_drop]
    have htotal := hjoint.2.2
    congr 2
    omega
  · rw [longCrossingJointPower, if_neg hjoint, if_neg (fun hbad => hjoint (he.mp hbad))]

/-- Projecting the longer word identifies its joint moment with E-L3's exact
first-passage-prefix/fresh-suffix moment. This discharges the fixed-index law
transport before any stopped-index or overshoot aggregation. -/
theorem horizonJointPostPassageMoment_eq (L s i h p : ℕ) (hL : i + 1 + p ≤ L) :
    horizonJointPostPassageMoment L s i h p = pairFirstPassagePostStopMoment s (i + 1) h p := by
  classical
  have hmap := PMFMoment.sum_map (Reference.wordPMF (2 * L))
    (fun w => w.take (2 * (i + 1 + p))) (longCrossingJointPower s i h p)
  rw [Reference.wordPMF_map_take_of_le (show 2 * (i + 1 + p) ≤ 2 * L by omega)] at hmap
  simp_rw [longCrossingJointPower_take s i h p (i + 1 + p) le_rfl] at hmap
  calc
    horizonJointPostPassageMoment L s i h p =
        ∑' w, Reference.wordPMF (2 * (i + 1 + p)) w * longCrossingJointPower s i h p w :=
      hmap.symm
    _ = pairFirstPassagePostStopMoment s (i + 1) h p := by
      unfold pairFirstPassagePostStopMoment prefixSuffixMoment
      rw [show 2 * (i + 1) + 2 * p = 2 * (i + 1 + p) by omega]
      apply tsum_congr
      intro w
      by_cases hz : Reference.wordPMF (2 * (i + 1 + p)) w = 0
      · simp [hz]
      · have hlen := (Reference.wordPMF_mem_support_iff (2 * (i + 1 + p)) w).mp hz
        rw [jointPower_eq_prefix s i h p w hlen]

/-- The common-horizon joint moment has exactly the original first-passage
probability times the overshoot and fresh-pair factors. -/
theorem horizonJointPostPassageMoment_toReal (L s i h p : ℕ) (hL : i + 1 + p ≤ L) :
    (horizonJointPostPassageMoment L s i h p).toReal =
      pairFirstPassageProbability s (i + 1) h * (4 / 3 : ℝ) ^ h * (4 : ℝ) ^ p := by
  rw [horizonJointPostPassageMoment_eq L s i h p hL,
    pairFirstPassagePostStopMoment_toReal]

private theorem prefixEventMass_ne_top (m : ℕ) (G : ValuationWord → Prop) :
    prefixEventMass m G ≠ ⊤ := by
  simpa only [prefixEventMass, mul_ite, mul_one, mul_zero] using
    Gated.event_ne_top (Reference.wordPMF m) G

/-- The joint moment is finite and equals the real original-law factor,
embedded back into ENNReal before exchanging nonnegative sums. -/
theorem horizonJointPostPassageMoment_eq_ofReal (L s i h p : ℕ) (hL : i + 1 + p ≤ L) :
    horizonJointPostPassageMoment L s i h p =
      ENNReal.ofReal (pairFirstPassageProbability s (i + 1) h * (4 / 3 : ℝ) ^ h * 4 ^ p) := by
  have hfinite : pairFirstPassagePostStopMoment s (i + 1) h p ≠ ⊤ := by
    rw [pairFirstPassagePostStopMoment_factor]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (prefixEventMass_ne_top _ _) ENNReal.ofReal_ne_top) (by simp)
  rw [horizonJointPostPassageMoment_eq L s i h p hL]
  calc
    _ = ENNReal.ofReal (pairFirstPassagePostStopMoment s (i + 1) h p).toReal :=
      (ENNReal.ofReal_toReal hfinite).symm
    _ = _ := by rw [pairFirstPassagePostStopMoment_toReal]

/-- The concrete common-horizon moment selects the realized strict crossing.
On supported sufficiently long words there is exactly one such index. -/
noncomputable def horizonPostPassageMoment (L s p : ℕ) : ENNReal :=
  ∑' w, Reference.wordPMF (2 * L) w * ∑' i : Fin (s / 2 + 1),
    if horizonTailEvent s 0 i w then
      ENNReal.ofReal ((4 / 3 : ℝ) ^
        (ValuationWord.total (w.take (2 * ((i : ℕ) + 1 + p))) - s))
    else 0

private theorem tailPower_eq_joint_sum (s i p : ℕ) (w : ValuationWord) :
    (if horizonTailEvent s 0 i w then
      ENNReal.ofReal ((4 / 3 : ℝ) ^
        (ValuationWord.total (w.take (2 * (i + 1 + p))) - s)) else 0) =
      ∑' k : ℕ, longCrossingJointPower s i (k + 1) p w := by
  by_cases hcross : horizonTailEvent s 0 i w
  · let k₀ := ValuationWord.total (w.take (2 * (i + 1))) - s - 1
    have htotal : ValuationWord.total (w.take (2 * (i + 1))) = s + (k₀ + 1) := by
      have hc := hcross.2
      dsimp [k₀]
      omega
    have hevent (k : ℕ) : horizonJointEvent s (k + 1) i w ↔ k = k₀ := by
      constructor
      · intro hk
        have ht := hk.2.2
        omega
      · rintro rfl
        exact ⟨by omega, hcross.1, htotal⟩
    rw [if_pos hcross, tsum_eq_single k₀]
    · simp [longCrossingJointPower, hevent]
    · intro k hk
      simp [longCrossingJointPower, hevent, hk]
  · have hevent (k : ℕ) : ¬ horizonJointEvent s (k + 1) i w := by
      intro hk
      apply hcross
      refine ⟨hk.2.1, ?_⟩
      have ht := hk.2.2
      omega
    simp [hcross, longCrossingJointPower, hevent]

/-- Exact decomposition of the actual word moment, using only nonnegative
sums. No conditional law or independence premise is introduced. -/
theorem horizonPostPassageMoment_eq_joint_sum (L s p : ℕ) :
    horizonPostPassageMoment L s p =
      ∑' k : ℕ, ∑' i : Fin (s / 2 + 1), horizonJointPostPassageMoment L s i (k + 1) p := by
  unfold horizonPostPassageMoment
  simp_rw [tailPower_eq_joint_sum, ← ENNReal.tsum_mul_left]
  calc
    _ = ∑' i : Fin (s / 2 + 1), ∑' w, ∑' k : ℕ,
        Reference.wordPMF (2 * L) w * longCrossingJointPower s i (k + 1) p w :=
      ENNReal.tsum_comm
    _ = ∑' i : Fin (s / 2 + 1), ∑' k : ℕ,
        horizonJointPostPassageMoment L s i (k + 1) p := by
      apply tsum_congr
      intro i
      exact ENNReal.tsum_comm
    _ = _ := ENNReal.tsum_comm

private theorem overshoot_weight_zero (k : ℕ) :
    stoppedJointProbability 0 (k + 1) * (4 / 3 : ℝ) ^ (k + 1) =
      (2 / 3 : ℝ) * ((k : ℝ) * (2 / 3 : ℝ) ^ k) := by
  rw [stoppedJointProbability_zero_mass]
  have hp : (1 / 2 : ℝ) ^ k * (4 / 3 : ℝ) ^ k = (2 / 3 : ℝ) ^ k := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (2 / 3 : ℝ) * ((k : ℝ) * ((1 / 2 : ℝ) ^ k * (4 / 3 : ℝ) ^ k)) := by
      simp only [pow_succ]
      ring
    _ = _ := by rw [hp]

private theorem overshoot_weight_pos {s : ℕ} (hs : 0 < s) (k : ℕ) :
    stoppedJointProbability s (k + 1) * (4 / 3 : ℝ) ^ (k + 1) =
      (1 / 3 : ℝ) * (((k : ℝ) + 1) * (2 / 3 : ℝ) ^ k) := by
  rw [stoppedJointProbability_eq_overshoot_mass hs (by omega)]
  have hp : (1 / 2 : ℝ) ^ k * (4 / 3 : ℝ) ^ k = (2 / 3 : ℝ) ^ k := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (1 / 3 : ℝ) * (((k : ℝ) + 1) * ((1 / 2 : ℝ) ^ k * (4 / 3 : ℝ) ^ k)) := by
      simp only [pow_succ, Nat.cast_add, Nat.cast_one]
      ring
    _ = _ := by rw [hp]

private theorem summable_overshoot_weight (s : ℕ) :
    Summable (fun k : ℕ => stoppedJointProbability s (k + 1) * (4 / 3 : ℝ) ^ (k + 1)) := by
  have hlinear := (hasSum_coe_mul_geometric_of_norm_lt_one (r := (2 / 3 : ℝ))
    (by norm_num)).summable
  have hgeom : Summable (fun k : ℕ => (2 / 3 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  by_cases hs : s = 0
  · subst s
    exact (hlinear.mul_left (2 / 3 : ℝ)).congr (fun k => (overshoot_weight_zero k).symm)
  · apply ((hlinear.add hgeom).mul_left (1 / 3 : ℝ)).congr
    intro k
    rw [overshoot_weight_pos (by omega : 0 < s)]
    ring

private theorem jointMoment_index_sum (L s h p : ℕ) (hL : s / 2 + 1 + p ≤ L) :
    (∑ i : Fin (s / 2 + 1), horizonJointPostPassageMoment L s i h p) =
      ENNReal.ofReal (stoppedJointProbability s h * (4 / 3 : ℝ) ^ h * (4 : ℝ) ^ p) := by
  calc
    _ = ∑ i : Fin (s / 2 + 1), ENNReal.ofReal
        (pairFirstPassageProbability s ((i : ℕ) + 1) h * (4 / 3 : ℝ) ^ h * (4 : ℝ) ^ p) := by
      apply Finset.sum_congr rfl
      intro i _
      exact horizonJointPostPassageMoment_eq_ofReal L s i h p (by have := i.isLt; omega)
    _ = ENNReal.ofReal (∑ i : Fin (s / 2 + 1),
        pairFirstPassageProbability s ((i : ℕ) + 1) h * (4 / 3 : ℝ) ^ h * (4 : ℝ) ^ p) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i _
      unfold pairFirstPassageProbability Gated.probability
      positivity
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← stoppedJointProbability_eq_sum]

/-- The actual common-horizon moment equals the accepted E-L3 aggregate.
Summability is established before converting the nonnegative sum to real values. -/
theorem horizonPostPassageMoment_eq (L s p : ℕ) (hL : s / 2 + 1 + p ≤ L) :
    horizonPostPassageMoment L s p = ENNReal.ofReal (stoppedPostPassagePairMoment s p) := by
  rw [horizonPostPassageMoment_eq_joint_sum]
  simp only [tsum_fintype]
  simp_rw [jointMoment_index_sum L s _ p hL]
  have hnonneg (k : ℕ) : 0 ≤
      stoppedJointProbability s (k + 1) * (4 / 3 : ℝ) ^ (k + 1) * (4 : ℝ) ^ p := by
    unfold stoppedJointProbability Gated.probability
    positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg ((summable_overshoot_weight s).mul_right (4 ^ p))]
  rw [tsum_mul_right, stoppedPostPassagePairMoment_factor]
  rfl

/-- E.5's moment bound for the concrete positions on one common original-word law. -/
theorem horizonPostPassageMoment_le (L s p : ℕ) (hL : s / 2 + 1 + p ≤ L) :
    horizonPostPassageMoment L s p ≤ ENNReal.ofReal ((4 : ℝ) ^ (p + 1)) := by
  rw [horizonPostPassageMoment_eq L s p hL]
  exact ENNReal.ofReal_le_ofReal (stoppedPostPassagePairMoment_le s p)

/-- Any two sufficiently long deterministic word horizons give the same
stopped moment, as required when all offsets share a single horizon. -/
theorem horizonPostPassageMoment_extend (L L' s p : ℕ)
    (hL : s / 2 + 1 + p ≤ L) (hL' : s / 2 + 1 + p ≤ L') :
    horizonPostPassageMoment L' s p = horizonPostPassageMoment L s p := by
  rw [horizonPostPassageMoment_eq L' s p hL', horizonPostPassageMoment_eq L s p hL]

end WordCertDensity.LocalPrimitive
