/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftCutoffScalars
import WordCertDensity.Construction.GraftError

/-! # The manuscript's explicit conductor boundary cutoff

The threshold [400000(L+1)]^2 bounds the scheduled-budget conductor by
96448 B/400000, hence by B/2. It therefore pays the actual physical
boundary at every later macro count, including the first one.
-/

namespace WordCertDensity.Construction

/-- The retained explicit real threshold for the actual natural original count. -/
noncomputable def graftBoundaryCutoff (L : ℝ) : ℝ := (400000 * (L + 1)) ^ 2

/-- The exact cutoff implies the positive-count and square-root guards used below. -/
theorem graftBoundaryCutoff_guards {L : ℝ} (hL : 0 ≤ L) {B : ℕ}
    (hB : graftBoundaryCutoff L ≤ (B : ℝ)) :
    2 ≤ B ∧ 400000 * (L + 1) ≤ Real.sqrt (B : ℝ) := by
  change (400000 * (L + 1)) ^ 2 ≤ (B : ℝ) at hB
  have hlarge := (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 400000)
    (by linarith : (400000 : ℝ) ≤ 400000 * (L + 1)) 2).trans hB
  have hs := Real.sqrt_le_sqrt hB
  rw [Real.sqrt_sq (by positivity)] at hs
  exact ⟨by exact_mod_cast (show (2 : ℝ) ≤ B by linarith), hs⟩

/-- At the printed cutoff the next macro uses at most the current original count. -/
theorem graft_macroLength_le_count {L : ℝ} (hL : 0 ≤ L) {B : ℕ}
    (hB : graftBoundaryCutoff L ≤ (B : ℝ)) : macroLength L B ≤ B := by
  obtain ⟨hB2, hs⟩ := graftBoundaryCutoff_guards hL hB
  have hlen := graft_macroLength_le_log hL hB2
  have hlog := mul_le_mul_of_nonneg_left (graft_log_count_le_sqrt hB2)
    (by positivity : 0 ≤ L + 1)
  have hm := mul_le_mul_of_nonneg_right
    (show 3 * (L + 1) ≤ Real.sqrt (B : ℝ) by linarith) (Real.sqrt_nonneg (B : ℝ))
  have hsq := Real.sq_sqrt (Nat.cast_nonneg B)
  have hle : (macroLength L B : ℝ) ≤ B := by nlinarith
  exact Nat.cast_le.mp hle

/-- The full scheduled conductor satisfies the exact rational margin printed in the manuscript. -/
theorem graftBudgetConductor_cutoff {L : ℝ} (hL : 0 ≤ L) {B : ℕ}
    (hB : graftBoundaryCutoff L ≤ (B : ℝ)) :
    (graftBudgetConductor L B : ℝ) ≤ (96448 / 400000 : ℝ) * B ∧
      (graftBudgetConductor L B : ℝ) < (B : ℝ) / 2 := by
  obtain ⟨hB2, hs⟩ := graftBoundaryCutoff_guards hL hB
  have hq := graftBudgetConductor_le_log hL hB2 (graft_macroLength_le_count hL hB)
  have hl := mul_le_mul_of_nonneg_left (graft_log_count_sq_le_sqrt hB2)
    (by positivity : 0 ≤ 4002 * (L + 1))
  have hm := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (B : ℝ))
  have hsq := Real.sq_sqrt (Nat.cast_nonneg B)
  have hprod : (L + 1) * Real.sqrt (B : ℝ) ≤ (B : ℝ) / 400000 := by nlinarith
  have hfirst : (graftBudgetConductor L B : ℝ) ≤ (96448 / 400000 : ℝ) * B := by nlinarith
  have hbR : (2 : ℝ) ≤ B := by exact_mod_cast hB2
  exact ⟨hfirst, by nlinarith⟩

/-- The printed threshold pays the actual conductor boundary without discarding a modulus term. -/
theorem macroBoundary_le_one_of_graftCutoff {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) {B : ℕ}
    (hB : graftBoundaryCutoff L ≤ (B : ℝ)) : macroBoundary L δ B ≤ 1 := by
  have hq := (graftBudgetConductor_cutoff hL hB).2
  have hactual : (macroConductor L δ B : ℝ) ≤ graftBudgetConductor L B :=
    Nat.cast_le.mpr (macroConductor_le_graftBudget L δ B)
  have hn : macroConductor L δ B ≤ B := by
    exact_mod_cast (show (macroConductor L δ B : ℝ) ≤ B by
      have := Nat.cast_nonneg (α := ℝ) B
      linarith)
  unfold macroBoundary
  calc
    _ ≤ (3 : ℝ) ^ B * (1 / 8 : ℝ) ^ B :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) (by positivity)
    _ = (3 / 8 : ℝ) ^ B := by rw [← mul_pow]; norm_num
    _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

/-- Paying the initial count by the explicit threshold pays every later macro boundary. -/
theorem graftMacroBoundary_of_cutoff {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) {b t : ℕ}
    (hB : graftBoundaryCutoff L ≤ (graftInitialCount b t : ℝ)) (j : ℕ) :
    macroBoundary L δ (macroCount L (graftInitialCount b t) j) ≤ 1 :=
  macroBoundary_le_one_of_graftCutoff hL δ
    (hB.trans (Nat.cast_le.mpr (macroCount_ge_start L (graftInitialCount b t) j)))

/-- Explicit boundary payment and offset absorption give the full physical graft estimate. -/
theorem physicalGraftMark_error_of_cutoff {L δ : ℝ} {b t root : ℕ}
    (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2 * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) (hroot : 16 ^ b ≤ root)
    (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hB : graftBoundaryCutoff L ≤ (graftInitialCount b t : ℝ)) (j : ℕ) :
    |physicalGraftMark L δ b t j root - physicalSeedMark b t root| ≤ graftTotalError L δ b t := by
  have hcont := physicalGraftMark_continuation_bound hb hL hδ hsmall hpay hroot hpaid
    (graftMacroBoundary_of_cutoff hL.le δ hB) j
  have htrans := physicalGraftMark_transition_debit L hδ hb hroot hpaid
  calc
    _ ≤ |physicalGraftMark L δ b t j root - physicalGraftMark L δ b t 0 root| +
        |physicalGraftMark L δ b t 0 root - physicalSeedMark b t root| := abs_sub_le _ _ _
    _ ≤ graftContinuationTail L b t + graftTransitionDebit δ b t := add_le_add hcont htrans
    _ = _ := by rw [graftTotalError, add_comm]

end WordCertDensity.Construction
