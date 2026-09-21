/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ParametricMixing

/-! # Actual histogram transfer with parameterized marker levels

The same physical histories and retained macroblocks supply the transfer.
The full tag multiplicity, offset window and finite-modulus boundary remain
present. Paying that boundary leaves the required inverse-fourth-power debit.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- The actual stopped-transfer discrepancy at the two parameterized levels. -/
noncomputable def parametricVariationTest (θ L δ : ℝ) (B : ℕ) (hθ : 0 < θ) (hB : 1 ≤ B) :
    ZMod (3 ^ parametricConductor θ L δ B) → ℝ := fun a =>
  Transfer.coarseSelected (macroblocks L δ B) (parametricConductor θ L δ B)
      (parametricLevel θ (B + macroLength L B))
      (fun _ hw => (parametricConductor_word_guards θ hw).2) a -
    Reference.marker (parametricLevel θ B)
      (Reference.project (parametricConductor_guards hθ L δ hB).2.2.2 a)

/-- Physical histograms, rather than reference frequencies, pay every transfer cost. -/
theorem parametric_stopped_variation {α : Type*} (H : Finset α)
    (word : α → ValuationWord) (source : α → ℕ) {M B : ℕ} {θ L δ T C : ℝ}
    (hθ : 0 < θ) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hphysical : ∀ i ∈ H, PhysicalHistory (word i) M (source i))
    (hinj : ∀ i ∈ H, ∀ j ∈ H, Transfer.historyTag (word i) =
      Transfer.historyTag (word j) → source i = source j → i = j)
    (hweight : ∀ i ∈ H, Transfer.weight (word i) ≤ (1 / 8 : ℝ) ^ B)
    (hoffset : ∀ i ∈ H, (0 : ℝ) ≤ ((word i).offset : ℝ) ∧ ((word i).offset : ℝ) ≤ C)
    (htags : ((H.image (fun i => Transfer.historyTag (word i))).card : ℝ) ≤ T) :
    (∑ a, Transfer.historyHistogram H word source (parametricConductor θ L δ B) a *
      |parametricVariationTest θ L δ B hθ hB a|) ≤
        (2 / 3 : ℝ) * T * (C + parametricBoundary θ L δ B) * parametricError θ L δ B := by
  have hg := parametricConductor_guards hθ L δ hB
  have h := Transfer.history_stopped_variation H word source (macroblocks L δ B)
    hphysical hinj hweight (by positivity) hC hoffset htags
    (fun _ hw => (parametricConductor_word_guards θ hw).1)
    (fun _ hw => (parametricConductor_word_guards θ hw).2)
    (hg.1.trans hg.2.1) hg.1 hg.2.2.2 (macroblocks_prefixFree L δ B)
  simpa only [parametricVariationTest, parametricBoundary, parametricError, macroblockMass,
    sub_zero] using h

/-- The full incoming-weighted debit with the parameterized two-marker error. -/
noncomputable def parametricGraftDebit (θ L δ : ℝ) (b t B : ℕ) : ℝ :=
  (2 / 3 : ℝ) * (seedCapacity b t * ((B : ℝ) + 1) ^ 2) *
    ((2 : ℝ) ^ (b + 1) + 1 + parametricBoundary θ L δ B) * parametricError θ L δ B

/-- Exact retained continuation coefficient, including the sixth inverse power of theta. -/
noncomputable def parametricGraftVariationConstant (θ L : ℝ) (b : ℕ) : ℝ :=
  (8 / 3 : ℝ) * ((2 : ℝ) ^ (b + 1) + 2) *
    (2 * (Analytic.mixingCoefficient : ℝ) * (θ⁻¹) ^ 6 + L + 5)

/-- The new coefficient agrees exactly with the previously built specialization. -/
theorem parametricGraftVariationConstant_fixed (L : ℝ) (b : ℕ) :
    parametricGraftVariationConstant (1 / 1000) L b = graftVariationConstant L b := by
  norm_num [parametricGraftVariationConstant, graftVariationConstant]

/-- Paying the actual boundary leaves the unchanged incoming factor and inverse fourth power. -/
theorem parametricGraftDebit_polynomial {θ L δ : ℝ} (hθ : 0 < θ) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hpay : 10 ≤ stoppedCorridorRate δ * L) (b t : ℕ) {B : ℕ} (hB : 1 ≤ B)
    (hboundary : parametricBoundary θ L δ B ≤ 1) :
    parametricGraftDebit θ L δ b t B ≤
      parametricGraftVariationConstant θ L b * seedCapacity b t / (B : ℝ) ^ 4 := by
  have hb : (1 : ℝ) ≤ B := Nat.one_le_cast.mpr hB
  have hbpos : (0 : ℝ) < B := by linarith
  have hP := (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  have htags : ((B : ℝ) + 1) ^ 2 ≤ 4 * (B : ℝ) ^ 2 := by nlinarith
  have hC : (0 : ℝ) ≤ (2 : ℝ) ^ (b + 1) + 1 + parametricBoundary θ L δ B := by
    have := (parametricBoundary_pos θ L δ B).le
    positivity
  have hbound : (2 : ℝ) ^ (b + 1) + 1 + parametricBoundary θ L δ B ≤
      (2 : ℝ) ^ (b + 1) + 2 := by linarith
  have he := parametricError_le hθ hL hδ hpay hB
  have hcoef : 0 ≤ 2 * (Analytic.mixingCoefficient : ℝ) * (θ⁻¹) ^ 6 + L + 5 := by
    have := Analytic.mixingCoefficient_pos.le
    positivity
  unfold parametricGraftDebit
  calc
    _ ≤ (2 / 3 : ℝ) * (seedCapacity b t * (4 * (B : ℝ) ^ 2)) *
        ((2 : ℝ) ^ (b + 1) + 2) *
        ((2 * (Analytic.mixingCoefficient : ℝ) * (θ⁻¹) ^ 6 + L + 5) / (B : ℝ) ^ 6) := by
      apply mul_le_mul _ he (parametricError_nonneg hθ L δ hB) (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htags hP) (by norm_num)) hbound hC (by positivity)
    _ = _ := by
      unfold parametricGraftVariationConstant
      field_simp
      ring

/-- The complete scalar continuation budget keeps the unchanged varying-start factor. -/
noncomputable def parametricContinuationTail (θ L : ℝ) (b t : ℕ) : ℝ :=
  3 * parametricGraftVariationConstant θ L b * graftTailWeight b t

/-- At each fixed parameter, the entire incoming-weighted continuation budget vanishes. -/
theorem parametricContinuationTail_tendsto (θ L : ℝ) {b : ℕ} (hb : 256 ^ 2 ≤ b) :
    Tendsto (parametricContinuationTail θ L b) atTop (𝓝 0) := by
  change Tendsto (fun t => 3 * parametricGraftVariationConstant θ L b * graftTailWeight b t)
    atTop (𝓝 0)
  simpa only [mul_zero] using
    (graftTailWeight_tendsto hb).const_mul (3 * parametricGraftVariationConstant θ L b)

/-- The scalar tail specializes to the already built complete continuation budget. -/
theorem parametricContinuationTail_fixed (L : ℝ) (b t : ℕ) :
    parametricContinuationTail (1 / 1000) L b t = graftContinuationTail L b t := by
  simp only [parametricContinuationTail, graftContinuationTail, parametricGraftVariationConstant_fixed]

end WordCertDensity.Construction
