/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.StoppingTail
import Mathlib.Tactic.NormNum

/-!
# The original probability law of complete stopped blocks

Only first-crossing words have mass, and each keeps its original geometric
weight. Normalization follows from finite prefix exclusion and exhaustion.
Precision and fixed-depth restrictions are proved for this actual law.
-/

@[expose] public section

namespace WordCertDensity.Construction

open Filter
open scoped Classical ENNReal Topology

/-- Original geometric weight at a first crossing, zero at every other word. -/
noncomputable def stoppedWeight (w : ValuationWord) : ℝ≥0∞ :=
  if FirstCrossing w then ENNReal.ofReal (1 / (2 : ℝ) ^ w.total) else 0

/-- A finite sum of stopped weights is exactly its original first-crossing submass. -/
theorem sum_stoppedWeight (V : Finset ValuationWord) :
    ∑ w ∈ V, stoppedWeight w =
      ENNReal.ofReal (Reference.stoppingMass (V.filter FirstCrossing)) := by
  rw [Reference.stoppingMass, ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  simp only [stoppedWeight, Finset.sum_filter]

/-- Every finite set of complete stopped words has original mass at most one. -/
theorem sum_stoppedWeight_le_one (V : Finset ValuationWord) :
    ∑ w ∈ V, stoppedWeight w ≤ 1 := by
  have hf : (V.filter FirstCrossing : Set ValuationWord).Pairwise
      (fun u v => ¬ u <+: v) := by
    intro u hu v hv hne hp
    exact hne (firstCrossing_prefix_eq (Finset.mem_filter.mp hu).2
      (Finset.mem_filter.mp hv).2 hp)
  rw [sum_stoppedWeight]
  exact (ENNReal.ofReal_le_ofReal (Reference.stoppingMass_le_one _ hf)).trans_eq
    (by simp)

/-- The finite precision family retains its original mass under these countable weights. -/
theorem sum_stoppedWeight_precision (E : ℕ) :
    ∑ w ∈ stoppedWords E, stoppedWeight w =
      ENNReal.ofReal (Reference.stoppingMass (stoppedWords E)) := by
  rw [sum_stoppedWeight]
  congr 2
  apply Finset.filter_eq_self.mpr
  intro w hw
  exact (mem_stoppedWords w E).mp hw |>.1

/-- All complete first-crossing weights sum to one, without conditioning or rescaling. -/
theorem tsum_stoppedWeight : ∑' w, stoppedWeight w = 1 := by
  apply le_antisymm
  · rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le sum_stoppedWeight_le_one
  · have ht : Tendsto
        (fun E => ENNReal.ofReal (Reference.stoppingMass (stoppedWords E)))
        atTop (𝓝 (ENNReal.ofReal 1)) :=
      (ENNReal.continuous_ofReal.tendsto 1).comp tendsto_stoppedWords_mass
    have h := le_of_tendsto' ht (fun E => by
      rw [← sum_stoppedWeight_precision E]
      exact ENNReal.sum_le_tsum _)
    simpa using h

/-- The normalized law of a complete first-crossing block, on the original word type. -/
noncomputable def stoppedPMF : PMF ValuationWord :=
  ⟨stoppedWeight, by simpa only [tsum_stoppedWeight] using
    (ENNReal.summable : Summable stoppedWeight).hasSum⟩

/-- The PMF constructor leaves every original weight unchanged. -/
theorem stoppedPMF_apply (w : ValuationWord) : stoppedPMF w = stoppedWeight w := rfl

/-- A genuine first crossing keeps its exact geometric atom. -/
theorem stoppedPMF_apply_of_firstCrossing {w : ValuationWord} (hw : FirstCrossing w) :
    stoppedPMF w = ENNReal.ofReal (1 / (2 : ℝ) ^ w.total) := by
  simp only [stoppedPMF_apply, stoppedWeight, if_pos hw]

/-- A non-crossing or later-crossing word is absent from the stopped law. -/
theorem stoppedPMF_apply_of_not_firstCrossing {w : ValuationWord} (hw : ¬ FirstCrossing w) :
    stoppedPMF w = 0 := by
  simp only [stoppedPMF_apply, stoppedWeight, if_neg hw]

/-- The support consists of exactly the genuine first-crossing words. -/
theorem stoppedPMF_mem_support_iff (w : ValuationWord) :
    w ∈ stoppedPMF.support ↔ FirstCrossing w := by
  rw [PMF.mem_support_iff]
  by_cases hw : FirstCrossing w
  · rw [stoppedPMF_apply_of_firstCrossing hw]
    simp only [hw, iff_true]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  · simp [stoppedPMF_apply_of_not_firstCrossing hw, hw]

/-- The original real atom is available directly to expectation calculations. -/
theorem stoppedPMF_toReal {w : ValuationWord} (hw : FirstCrossing w) :
    (stoppedPMF w).toReal = 1 / (2 : ℝ) ^ w.total := by
  rw [stoppedPMF_apply_of_firstCrossing hw, ENNReal.toReal_ofReal (by positivity)]

/-- At its stopping depth, a complete block has the same atom as the original iid word. -/
theorem stoppedPMF_eq_wordPMF {w : ValuationWord} (hw : FirstCrossing w) :
    stoppedPMF w = Reference.wordPMF w.length w := by
  rw [stoppedPMF_apply_of_firstCrossing hw,
    ← Reference.wordPMF_toReal_length_eq_inv_pow w]
  exact ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)

/-- The total-valuation cutoff has precisely the original finite survival probability. -/
theorem stoppedPMF_precision_probability (E : ℕ) :
    Gated.probability stoppedPMF (fun w => w.total < E) =
      Reference.stoppingMass (stoppedWords E) := by
  have he : (∑' w, if w.total < E then stoppedPMF w else 0) =
      ∑ w ∈ stoppedWords E, stoppedPMF w := by
    rw [tsum_eq_sum (s := stoppedWords E) (fun w hw => by
      by_cases ht : w.total < E
      · have hc : ¬ FirstCrossing w := fun hc => hw ((mem_stoppedWords w E).mpr ⟨hc, ht⟩)
        simp [ht, stoppedPMF_apply_of_not_firstCrossing hc]
      · simp [ht])]
    apply Finset.sum_congr rfl
    intro w hw
    exact if_pos ((mem_stoppedWords w E).mp hw).2
  calc
    Gated.probability stoppedPMF (fun w => w.total < E) =
        (∑ w ∈ stoppedWords E, stoppedPMF w).toReal := by
      rw [← he]
      unfold Gated.probability
      congr 1
      apply tsum_congr
      intro w
      by_cases hw : w.total < E <;> simp only [hw, if_true, if_false]
    _ = Reference.stoppingMass (stoppedWords E) := by
      simp_rw [stoppedPMF_apply]
      rw [sum_stoppedWeight_precision, ENNReal.toReal_ofReal
        (Reference.stoppingMass_nonneg _)]

/-- The rejected precision probability is exactly the finite survival deficit. -/
theorem stoppedPMF_precision_tail (E : ℕ) :
    Gated.probability stoppedPMF (fun w => E ≤ w.total) =
      1 - Reference.stoppingMass (stoppedWords E) := by
  have h := Gated.probability_compl stoppedPMF (fun w => w.total < E)
  simpa only [not_lt, stoppedPMF_precision_probability] using h

/-- Pointwise identity between a stopped-depth slice and first crossings in the iid word law. -/
theorem stoppedPMF_length_atom (n : ℕ) (w : ValuationWord) :
    (if w.length = n then stoppedPMF w else 0) =
      if FirstCrossing w then Reference.wordPMF n w else 0 := by
  by_cases hn : w.length = n
  · by_cases hc : FirstCrossing w
    · simp only [hn, if_true, hc]
      simpa only [← hn] using stoppedPMF_eq_wordPMF hc
    · simp [hn, hc, stoppedPMF_apply_of_not_firstCrossing hc]
  · simp [hn, Reference.wordPMF_eq_zero_of_length_ne n w hn]

/-- Fixed-depth stopped moments are the original iid moments restricted to first crossings. -/
theorem stoppedPMF_length_moment (n : ℕ) (F : ValuationWord → ℝ≥0∞) :
    (∑' w, if w.length = n then stoppedPMF w * F w else 0) =
      ∑' w, if FirstCrossing w then Reference.wordPMF n w * F w else 0 := by
  apply tsum_congr
  intro w
  simpa only [ite_mul, zero_mul] using congrArg (fun x => x * F w)
    (stoppedPMF_length_atom n w)

/-- The distribution of stopping depth is its literal first-crossing event at each depth. -/
theorem stoppedPMF_length_probability (n : ℕ) :
    Gated.probability stoppedPMF (fun w => w.length = n) =
      Gated.probability (Reference.wordPMF n) FirstCrossing := by
  unfold Gated.probability
  congr 1
  apply tsum_congr
  intro w
  have h := stoppedPMF_length_atom n w
  by_cases hn : w.length = n <;> by_cases hc : FirstCrossing w
  all_goals simp only [hn, hc, if_true, if_false] at h
  all_goals simp only [hn, hc, if_true, if_false]
  all_goals exact h

/-- A strict prefix of a first-crossing block has not crossed earlier. -/
theorem firstCrossing_prefix_noCrossing {u w : ValuationWord} (hw : FirstCrossing w)
    (hp : u <+: w) (hlen : u.length < w.length) : NoCrossing u := by
  rintro ⟨v, hvu, hvc⟩
  have he := firstCrossing_prefix_eq hvc hw (hvu.trans hp)
  have hl := hvu.length_le
  rw [he] at hl
  omega


/-- Stopping at depth n+1 requires that its preceding n letters had not yet stopped. -/
theorem stoppedPMF_succ_length_probability_le (n : ℕ) :
    Gated.probability stoppedPMF (fun w => w.length = n + 1) ≤ noCrossingProbability n := by
  rw [stoppedPMF_length_probability]
  have he := Gated.probability_mono_on_support (Reference.wordPMF (n + 1))
    FirstCrossing (fun w => NoCrossing (w.take n)) (fun w hp hw => by
      have hn := (Reference.wordPMF_mem_support_iff (n + 1) w).mp
        ((PMF.mem_support_iff _ _).mpr hp)
      apply firstCrossing_prefix_noCrossing hw (List.take_prefix _ _)
      rw [List.length_take, hn, Nat.min_eq_left (Nat.le_succ n)]
      omega)
  refine he.trans_eq ?_
  have hm := Gated.probability_map (Reference.wordPMF (n + 1))
    (fun w : ValuationWord => w.take n) NoCrossing
  rw [Reference.wordPMF_map_take_of_le (Nat.le_succ n)] at hm
  exact hm.symm

/-- The stopped-depth atom has the explicit preceding-depth exponential majorant. -/
theorem stoppedPMF_succ_length_exp_bound (n : ℕ) :
    Gated.probability stoppedPMF (fun w => w.length = n + 1) ≤
      Real.exp (3 / 5 - (n : ℝ) / 25) :=
  (stoppedPMF_succ_length_probability_le n).trans (noCrossingProbability_exp_bound n)

end WordCertDensity.Construction
