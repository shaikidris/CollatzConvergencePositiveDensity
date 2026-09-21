/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.FirstCrossing
public import WordCertDensity.Reference.WordMoment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Termination tails and exhaustion of finite stopped mass

The no-crossing event refers to all prefixes of the actual iid valuation word.
The explicit exponential bound supplies normalization of the stopped law. It
is separate from the sharper two-binomial precision certificate.
-/

@[expose] public section

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- No first crossing has occurred in the observed finite word. -/
def NoCrossing (w : ValuationWord) : Prop :=
  ¬ ∃ u : ValuationWord, u <+: w ∧ FirstCrossing u

/-- Original probability that the stopping depth is greater than n. -/
noncomputable def noCrossingProbability (n : ℕ) : ℝ :=
  Gated.probability (Reference.wordPMF n) NoCrossing

/-- Absence of a first crossing forces terminal displacement strictly below three. -/
theorem noCrossing_displacement_lt {w : ValuationWord} (hw : NoCrossing w) :
    displacement w < 3 := by
  apply lt_of_not_ge
  intro h
  exact hw (exists_firstCrossing_prefix w ((slope_le_eighth_iff w).mpr h))

/-- The original no-crossing event has a probability between zero and one. -/
theorem noCrossingProbability_bounds (n : ℕ) :
    0 ≤ noCrossingProbability n ∧ noCrossingProbability n ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, Gated.probability_le_one _ _⟩

/-- Negative centered moments bound the actual finite-depth stopping tail. -/
theorem noCrossingProbability_le (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    noCrossingProbability n ≤
      Real.exp (3 * s + (n : ℝ) * (s ^ 2 - s * (2 - Head.logRatio))) := by
  have he := Gated.probability_mono_on_support (Reference.wordPMF n) NoCrossing
    (fun w => ValuationWord.centeredTotal w ≤ -((2 - Head.logRatio) * n - 3))
    (fun w hp hw => by
      have hn := (Reference.wordPMF_mem_support_iff n w).mp ((PMF.mem_support_iff _ _).mpr hp)
      have h := noCrossing_displacement_lt hw
      simp only [displacement, hn] at h
      simp only [ValuationWord.centeredTotal, hn]
      linarith)
  refine he.trans ((Reference.word_lowerTail_le n hs).trans_eq ?_)
  congr 1
  ring

/-- One fixed choice s=1/5 gives a summable tail, including depth zero. -/
theorem noCrossingProbability_exp_bound (n : ℕ) :
    noCrossingProbability n ≤ Real.exp (3 / 5 - (n : ℝ) / 25) := by
  refine (noCrossingProbability_le n (s := 1 / 5) (by norm_num)).trans ?_
  apply Real.exp_le_exp.mpr
  have h := Head.logRatio_lt_eight_fifths
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

private theorem summable_tail_bound :
    Summable (fun n : ℕ => Real.exp (3 / 5 - (n : ℝ) / 25)) := by
  have h := (Real.summable_exp_nat_mul_iff.mpr (by norm_num : (-1 / 25 : ℝ) < 0))
  have hm := h.mul_left (Real.exp (3 / 5))
  apply hm.congr
  intro n
  rw [← Real.exp_add]
  congr 1
  ring

/-- The sum of the actual survival probabilities is finite. -/
theorem summable_noCrossingProbability : Summable noCrossingProbability :=
  summable_tail_bound.of_nonneg_of_le (fun n => (noCrossingProbability_bounds n).1)
    noCrossingProbability_exp_bound

/-- The original probability of not yet stopping tends to zero. -/
theorem tendsto_noCrossingProbability : Tendsto noCrossingProbability atTop (𝓝 0) :=
  summable_noCrossingProbability.tendsto_atTop_zero

private theorem total_le_of_prefix {u w : ValuationWord} (h : u <+: w) :
    u.total ≤ w.total := by
  obtain ⟨v, rfl⟩ := h
  rw [ValuationWord.total_append]
  omega

/-- Finite precision loses only a depth tail and a total-valuation tail at any chosen depth. -/
theorem stoppedWords_deficit_le (E n : ℕ) :
    1 - Reference.stoppingMass (stoppedWords E) ≤ noCrossingProbability n +
      Gated.probability (Reference.wordPMF n) (fun w => E ≤ w.total) := by
  classical
  let V := (stoppedWords E).filter (fun w => w.length ≤ n)
  have hsub : V ⊆ stoppedWords E := Finset.filter_subset _ _
  have hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v) := by
    intro u hu v hv hne
    exact stoppedWords_prefixFree E (hsub hu) (hsub hv) hne
  have hlen : ∀ w ∈ V, w.length ≤ n := fun w hw => (Finset.mem_filter.mp hw).2
  have he := Gated.probability_mono_on_support (Reference.wordPMF n)
    (fun w => ¬ Reference.prefixFamilyEvent V w)
    (fun w => NoCrossing w ∨ E ≤ w.total) (fun w hp hw => by
      have hn := (Reference.wordPMF_mem_support_iff n w).mp ((PMF.mem_support_iff _ _).mpr hp)
      by_cases h : NoCrossing w
      · exact Or.inl h
      · apply Or.inr
        by_contra ht
        obtain ⟨u, hup, huc⟩ := not_not.mp h
        have huE : u.total < E := (total_le_of_prefix hup).trans_lt (lt_of_not_ge ht)
        exact hw ⟨u, Finset.mem_filter.mpr
          ⟨(mem_stoppedWords u E).mpr ⟨huc, huE⟩, hn ▸ hup.length_le⟩, hup⟩)
  rw [Reference.prefixFamily_compl_probability V hlen hfree] at he
  have hm := Reference.stoppingMass_mono hsub
  have hu := Gated.probability_or_le (Reference.wordPMF n) NoCrossing
    (fun w => E ≤ w.total)
  change _ ≤ noCrossingProbability n + _ at hu
  linarith

/-- A fixed positive moment controls the total-valuation truncation at precision 4n. -/
theorem word_total_four_mul_tail (n : ℕ) :
    Gated.probability (Reference.wordPMF n) (fun w => 4 * n ≤ w.total) ≤
      Real.exp (-(n : ℝ) / 10) := by
  have he := Gated.probability_mono_on_support (Reference.wordPMF n)
    (fun w => 4 * n ≤ w.total) (fun w => 2 * (n : ℝ) ≤ ValuationWord.centeredTotal w)
    (fun w hp hw => by
      have hn := (Reference.wordPMF_mem_support_iff n w).mp ((PMF.mem_support_iff _ _).mpr hp)
      have hc : (4 : ℝ) * n ≤ w.total := by exact_mod_cast hw
      simp only [ValuationWord.centeredTotal, hn]
      linarith)
  have hl : (1 / 10 : ℝ) < Real.log 2 := by linarith [Head.log_two_lower]
  have hm := Reference.word_upperTail_le n (cutoff := 2 * n)
    (s := 1 / 10) (by norm_num) hl
  refine he.trans (hm.trans ?_)
  apply Real.exp_le_exp.mpr
  have hi : (Real.log 2)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ (by linarith [Head.log_two_lower])).mpr
    linarith [Head.log_two_lower]
  have hd : 0 < 1 - (Real.log 2)⁻¹ * (1 / 10) := by linarith
  have hq : (1 / 10 : ℝ) ^ 2 / (1 - (Real.log 2)⁻¹ * (1 / 10)) ≤ 1 / 10 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- The original finite stopped mass has an explicit vanishing error along precision 4n. -/
theorem stoppedWords_deficit_four_mul (n : ℕ) :
    1 - Reference.stoppingMass (stoppedWords (4 * n)) ≤
      Real.exp (3 / 5 - (n : ℝ) / 25) + Real.exp (-(n : ℝ) / 10) :=
  (stoppedWords_deficit_le (4 * n) n).trans
    (add_le_add (noCrossingProbability_exp_bound n) (word_total_four_mul_tail n))

/-- Increasing the total cutoff increases the original finite stopping mass. -/
theorem stoppedWords_mass_monotone :
    Monotone (fun E => Reference.stoppingMass (stoppedWords E)) :=
  fun _ _ h => Reference.stoppingMass_mono (stoppedWords_mono h)

/-- The original finite first-crossing weights exhaust total probability one. -/
theorem tendsto_stoppedWords_mass :
    Tendsto (fun E => Reference.stoppingMass (stoppedWords E)) atTop (𝓝 1) := by
  have hs : Summable (fun n : ℕ => Real.exp (-(n : ℝ) / 10)) := by
    convert Real.summable_exp_nat_mul_iff.mpr (by norm_num : (-1 / 10 : ℝ) < 0) using 1
    funext n
    congr 1
    ring
  have ht := (summable_tail_bound.add hs).tendsto_atTop_zero
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 (1 - a) (by linarith))
    have hb := stoppedWords_deficit_four_mul N
    have hsmall := hN N le_rfl
    apply eventually_atTop.mpr
    refine ⟨4 * N, fun E hE => ?_⟩
    have hm := stoppedWords_mass_monotone hE
    linarith
  · intro a ha
    exact Filter.Eventually.of_forall (fun E => (stoppedWords_mass_bounds E).2.trans_lt ha)

end WordCertDensity.Construction
