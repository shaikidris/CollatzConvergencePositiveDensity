/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PassageExpectation
public import WordCertDensity.Analytic.LocalPrimitive.PassageWhiteLaw
public import WordCertDensity.Analytic.LocalPrimitive.WhiteLayerEstimate
import Mathlib.Tactic

/-! # The original-law short-exit comparison -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- A selected short triangle supplies the exact three witnesses consumed by
`LayerEstimates.short_exit`.  The event mass is measured under the original
first-passage law, and the two contributions retain that same mass. -/
theorem selected_triangle_short_exit_estimate {n a j N m : ℕ}
    (hn : 0 < n) (ha : 2 * a < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (top l : ℤ)
    (hsel : isSelectedPhaseTriangle n ξ a top)
    (hstart : inPhaseTriangleIntMul n ξ a top j l)
    (hcolumn : j = N - m) (hmN : m ≤ N) (B : ℕ) (hB : 0 < B)
    (hm : localPrimitiveM B ≤ m)
    (hshort : ((top - l).toNat : ℝ) ≤
      (m : ℝ) / (localPrimitiveEtaDenom B : ℝ))
    (D : ℝ) (hD : 1 ≤ D)
    (hfuture : ∀ r, r < m → ∀ l',
      layerWeight B r * phaseRemainingPotential n ξ N r l' ≤ D) :
    ∃ p cw cb : ℝ, 15 / 16 ≤ p ∧ p ≤ 1 ∧
      layerWeight B m * phaseRemainingPotential n ξ N m l ≤
        (1 + pairLoss localEpsilon / 8) * (cw + cb) ∧
      cw ≤ D * (1 - pairLoss localEpsilon / 2) * p ∧ cb ≤ D * (1 - p) := by
  let s := (top - l).toNat
  let W : passagePrefixFamily s → Prop := fun u => passageWhiteExit n ξ j l u
  let q : passagePrefixFamily s → ℕ := fun u => (u : ValuationWord).length / 2
  let U : passagePrefixFamily s → ℝ := fun u =>
    integerPairPotential localEpsilon (phaseWhiteAtInt n ξ) (m - q u)
      (j + q u) (l + (u : ValuationWord).total)
  let F : passagePrefixFamily s → ℝ := fun u => layerWeight B (m - q u) * U u
  let p := Gated.probability (passagePMF s) W
  let cw := D * (1 - pairLoss localEpsilon / 2) * p
  let cb := D * (1 - p)
  have hstoplt : s / 2 + 1 < m := by
    have hb := short_exit_recipe_bounds B m s (s / 2 + 1) hB hm hshort le_rfl
    exact hb.1
  have hstop : s / 2 + 1 ≤ m := hstoplt.le
  have hqpos (u : passagePrefixFamily s) : 0 < q u := by
    obtain ⟨i, hi, _⟩ := u.property
    simp only [q, hi]
    omega
  have hqbound (u : passagePrefixFamily s) : q u ≤ s / 2 + 1 := by
    obtain ⟨i, hi, _⟩ := u.property
    have hidx := i.isLt
    simp only [q, hi]
    omega
  have hqlt (u : passagePrefixFamily s) : q u < m :=
    lt_of_le_of_lt (hqbound u) hstoplt
  have hcolumn_u (u : passagePrefixFamily s) : N - (m - q u) = j + q u := by
    have hq := hqlt u
    omega
  have hUeq (u : passagePrefixFamily s) :
      U u = phaseRemainingPotential n ξ N (m - q u) (l + (u : ValuationWord).total) := by
    unfold U phaseRemainingPotential phasePairPotential
    rw [hcolumn_u]
  have hinitial :
      integerPairPotential localEpsilon (phaseWhiteAtInt n ξ) m j l =
        phaseRemainingPotential n ξ N m l := by
    unfold phaseRemainingPotential phasePairPotential
    rw [hcolumn]
  have hpass := integerPairPotential_passage_expectation_le localEpsilon_guard
    (phaseWhiteAtInt n ξ) s m j l hstop
  change integerPairPotential localEpsilon (phaseWhiteAtInt n ξ) m j l ≤
    ∑' u : passagePrefixFamily s, (passagePMF s u).toReal * U u at hpass
  rw [hinitial] at hpass
  have hpSumm : Summable (fun u : passagePrefixFamily s => (passagePMF s u).toReal) :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  have hU0 (u : passagePrefixFamily s) : 0 ≤ U u := by
    exact integerPairPotential_nonneg localEpsilon_guard (phaseWhiteAtInt n ξ) _ _ _
  have hU1 (u : passagePrefixFamily s) : U u ≤ 1 := by
    exact integerPairPotential_le_one localEpsilon_guard (phaseWhiteAtInt n ξ) _ _ _
  have hg : Summable (fun u : passagePrefixFamily s => (passagePMF s u).toReal * U u) := by
    refine Summable.of_nonneg_of_le (fun u => mul_nonneg ENNReal.toReal_nonneg (hU0 u)) ?_ hpSumm
    intro u
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hU1 u) ENNReal.toReal_nonneg
  have hF0 (u : passagePrefixFamily s) : 0 ≤ F u := by
    exact mul_nonneg (layerWeight_pos B _).le (hU0 u)
  have hFbound (u : passagePrefixFamily s) : F u ≤ D := by
    change layerWeight B (m - q u) * U u ≤ D
    rw [hUeq]
    exact hfuture (m - q u) (Nat.sub_lt (by omega) (hqpos u)) _
  have hD0 : 0 ≤ D := by linarith
  have hFsum : Summable (fun u : passagePrefixFamily s => (passagePMF s u).toReal * F u) := by
    refine Summable.of_nonneg_of_le
      (fun u => mul_nonneg ENNReal.toReal_nonneg (hF0 u)) ?_ (hpSumm.mul_right D)
    intro u
    exact mul_le_mul_of_nonneg_left (hFbound u) ENNReal.toReal_nonneg
  have hratio (u : passagePrefixFamily s) :
      layerWeight B m ≤
        (1 + pairLoss localEpsilon / 8) * layerWeight B (m - q u) :=
    short_exit_weight_ratio B m s (q u) hB hm hshort (hqbound u)
  have hweighted :
      layerWeight B m * phaseRemainingPotential n ξ N m l ≤
        (1 + pairLoss localEpsilon / 8) *
          (∑' u : passagePrefixFamily s, (passagePMF s u).toReal * F u) := by
    calc
      _ ≤ layerWeight B m *
          (∑' u : passagePrefixFamily s, (passagePMF s u).toReal * U u) :=
        mul_le_mul_of_nonneg_left hpass (layerWeight_pos B m).le
      _ = ∑' u : passagePrefixFamily s,
          layerWeight B m * ((passagePMF s u).toReal * U u) := by
        rw [tsum_mul_left]
      _ ≤ ∑' u : passagePrefixFamily s,
          (1 + pairLoss localEpsilon / 8) * ((passagePMF s u).toReal * F u) := by
        apply (hg.mul_left (layerWeight B m)).tsum_le_tsum
        · intro u
          have hu := mul_le_mul_of_nonneg_right (hratio u) (hU0 u)
          have hp : (passagePMF s u).toReal * (layerWeight B m * U u) ≤
              (passagePMF s u).toReal *
                ((1 + pairLoss localEpsilon / 8) * layerWeight B (m - q u) * U u) :=
            mul_le_mul_of_nonneg_left hu (by positivity)
          simpa only [F] using (show
            layerWeight B m * ((passagePMF s u).toReal * U u) ≤
              (1 + pairLoss localEpsilon / 8) *
                ((passagePMF s u).toReal * (layerWeight B (m - q u) * U u)) by
            nlinarith)
        · exact hFsum.mul_left (1 + pairLoss localEpsilon / 8)
      _ = _ := tsum_mul_left
  have hd := localPairLoss_mem_unitInterval
  have hcap0 : 0 ≤ D * (1 - pairLoss localEpsilon / 2) := by nlinarith
  have hwhite (u : passagePrefixFamily s) (hu : W u) :
      F u ≤ D * (1 - pairLoss localEpsilon / 2) := by
    have hwu : phaseWhiteAtInt n ξ (N - (m - q u))
        (l + (u : ValuationWord).total) := by
      rw [hcolumn_u]
      exact hu.1
    change layerWeight B (m - q u) * U u ≤ D * (1 - pairLoss localEpsilon / 2)
    rw [hUeq]
    exact short_white_exit_weighted_le B n N m s (q u) ξ
      (l + (u : ValuationWord).total) hB hm hmN hshort (hqbound u) (hqpos u)
      D hD0 hfuture hwu
  have hsplit := pmf_expectation_le_event_split (passagePMF s) W F
    (D * (1 - pairLoss localEpsilon / 2)) D hcap0 hD0 hF0 hwhite
    (fun u _ => hFbound u)
  have hpwhite : (15 / 16 : ℝ) ≤ p := by
    have hw := passagePMF_white_gt_fifteen_sixteenths hn ha ξ hξ top l hsel hstart
    exact hw.le
  have hpone : p ≤ 1 := Gated.probability_le_one (passagePMF s) W
  refine ⟨p, cw, cb, hpwhite, hpone, ?_, le_rfl, le_rfl⟩
  exact hweighted.trans (mul_le_mul_of_nonneg_left hsplit (by nlinarith [hd.1]))

end WordCertDensity.LocalPrimitive
