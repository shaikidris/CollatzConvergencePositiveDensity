/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.MacroCapacity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Literal positive levels and the actual conductor ratio

The old level is ceil(B/1000), the new level uses B+ell(B), and the
conductor adds the actual finite macroblock maximum depth. The log and
log-squared corrections vanish after division by the original count.
The zero-count stage is kept separate from positive-level mixing guards.
-/

@[expose] public section

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- Literal level used at original block count B. -/
noncomputable def macroLevel (B : ℕ) : ℕ := ⌈(B : ℝ) / 1000⌉₊

/-- The actual conductor uses the next level and the actual finite-family maximum depth. -/
noncomputable def macroConductor (L δ : ℝ) (B : ℕ) : ℕ :=
  macroLevel (B + macroLength L B) + macroblockDepth L δ B

/-- Count zero has level zero and is not a positive-level mixing stage. -/
@[simp] theorem macroLevel_zero : macroLevel 0 = 0 := by norm_num [macroLevel]

/-- Exact lower and strict upper rounding bounds hold at every original count. -/
theorem macroLevel_bounds (B : ℕ) :
    (B : ℝ) / 1000 ≤ macroLevel B ∧ (macroLevel B : ℝ) < (B : ℝ) / 1000 + 1 :=
  ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (by positivity)⟩

/-- Levels are monotone in the actual original count. -/
theorem macroLevel_mono : Monotone macroLevel := by
  intro B C hBC
  exact Nat.ceil_mono (div_le_div_of_nonneg_right (Nat.cast_le.mpr hBC) (by norm_num))

/-- Every positive original count supplies a positive old level. -/
theorem macroLevel_pos {B : ℕ} (hB : 1 ≤ B) : 1 ≤ macroLevel B := by
  apply Nat.one_le_ceil_iff.mpr
  have h : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  positivity

/-- Literal old/new levels satisfy all order and positivity guards at B>=1. -/
theorem macroConductor_guards (L δ : ℝ) {B : ℕ} (hB : 1 ≤ B) :
    1 ≤ macroLevel B ∧ macroLevel B ≤ macroLevel (B + macroLength L B) ∧
      macroLevel (B + macroLength L B) ≤ macroConductor L δ B ∧
      macroLevel B ≤ macroConductor L δ B := by
  have hm := macroLevel_mono (Nat.le_add_right B (macroLength L B))
  have hq : macroLevel (B + macroLength L B) ≤ macroConductor L δ B :=
    Nat.le_add_right _ _
  exact ⟨macroLevel_pos hB, hm, hq, hm.trans hq⟩

/-- Every retained word leaves the literal new level inside the actual conductor. -/
theorem macroConductor_word_guards {L δ : ℝ} {B : ℕ} {w : ValuationWord}
    (hw : w ∈ macroblocks L δ B) :
    w.length ≤ macroConductor L δ B ∧
      macroLevel (B + macroLength L B) ≤ macroConductor L δ B - w.length := by
  have hd : w.length ≤ macroblockDepth L δ B := Finset.le_sup hw
  change w.length ≤ macroLevel (B + macroLength L B) + macroblockDepth L δ B ∧
    macroLevel (B + macroLength L B) ≤
      macroLevel (B + macroLength L B) + macroblockDepth L δ B - w.length
  omega

/-- Unnormalized conductor bounds retain both the ceiling error and actual depth. -/
theorem macroConductor_bounds (L δ : ℝ) (B : ℕ) :
    (B : ℝ) / 1000 ≤ macroConductor L δ B ∧
      (macroConductor L δ B : ℝ) ≤
        ((B : ℝ) + macroLength L B) / 1000 + 1 + macroblockDepth L δ B := by
  have h := macroLevel_bounds (B + macroLength L B)
  rw [Nat.cast_add] at h
  have he : (macroConductor L δ B : ℝ) =
      (macroLevel (B + macroLength L B) : ℝ) + macroblockDepth L δ B := by
    simp only [macroConductor, Nat.cast_add]
  have hn : (0 : ℝ) ≤ macroLength L B := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ macroblockDepth L δ B := Nat.cast_nonneg _
  constructor <;> linarith [h.1, h.2]

/-- Every fixed power of log(B+2) is negligible compared with the original count. -/
theorem logpow_div_count_tendsto (n : ℕ) :
    Tendsto (fun B : ℕ => Real.log ((B : ℝ) + 2) ^ n / B) atTop (𝓝 0) := by
  have hn : Tendsto (fun B : ℕ => (B : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hx : Tendsto (fun B : ℕ => (B : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun B => by linarith) hn
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) n one_ne_zero).comp hx
  simpa only [Function.comp_def, one_mul, add_neg_cancel_right] using h

/-- The actual number of original blocks in one macroblock is sublinear in B. -/
theorem macroLength_div_count_tendsto {L : ℝ} (hL : 0 ≤ L) :
    Tendsto (fun B : ℕ => (macroLength L B : ℝ) / B) atTop (𝓝 0) := by
  have ht : Tendsto (fun B : ℕ => (L + 2) * Real.log ((B : ℝ) + 2) / B)
      atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero, mul_div_assoc] using
      (logpow_div_count_tendsto 1).const_mul (L + 2)
  exact squeeze_zero (fun B => by positivity)
    (fun B => div_le_div_of_nonneg_right (macroLength_le_log hL B) (Nat.cast_nonneg B)) ht

/-- The actual finite-family maximum depth, not just its budget, is sublinear in B. -/
theorem macroblockDepth_div_count_tendsto {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) :
    Tendsto (fun B : ℕ => (macroblockDepth L δ B : ℝ) / B) atTop (𝓝 0) := by
  have ht : Tendsto (fun B : ℕ => (2000 * (L + 2) * (2 * L + 5)) *
      Real.log ((B : ℝ) + 2) ^ 2 / B) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (logpow_div_count_tendsto 2).const_mul (2000 * (L + 2) * (2 * L + 5))
  exact squeeze_zero (fun B => by positivity)
    (fun B => div_le_div_of_nonneg_right (macroblockDepth_le_log_sq hL δ B)
      (Nat.cast_nonneg B)) ht

/-- Normalizing by a positive original count leaves precisely the three vanishing errors. -/
theorem macroConductor_ratio_bounds (L δ : ℝ) {B : ℕ} (hB : 1 ≤ B) :
    (1 / 1000 : ℝ) ≤ (macroConductor L δ B : ℝ) / B ∧
      (macroConductor L δ B : ℝ) / B ≤ 1 / 1000 +
        ((macroLength L B : ℝ) / B) / 1000 + 1 / B + (macroblockDepth L δ B : ℝ) / B := by
  have hb : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have h := macroConductor_bounds L δ B
  constructor
  · apply (le_div_iff₀ hb).mpr
    linarith [h.1]
  · have he : (((B : ℝ) + macroLength L B) / 1000 + 1 +
        macroblockDepth L δ B) / B = 1 / 1000 +
        ((macroLength L B : ℝ) / B) / 1000 + 1 / B + (macroblockDepth L δ B : ℝ) / B := by
      field_simp
    exact (div_le_div_of_nonneg_right h.2 hb.le).trans_eq he

/-- The literal conductor ratio tends to 1/1000, with the actual depth retained. -/
theorem macroConductor_ratio_tendsto {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) :
    Tendsto (fun B : ℕ => (macroConductor L δ B : ℝ) / B) atTop (𝓝 (1 / 1000)) := by
  have hc : Tendsto (fun _ : ℕ => (1 / 1000 : ℝ)) atTop (𝓝 (1 / 1000)) := tendsto_const_nhds
  have hi : Tendsto (fun B : ℕ => (1 : ℝ) / B) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hu : Tendsto (fun B : ℕ => (1 / 1000 : ℝ) +
      ((macroLength L B : ℝ) / B) / 1000 + 1 / B + (macroblockDepth L δ B : ℝ) / B)
      atTop (𝓝 (1 / 1000)) := by
    simpa only [zero_div, add_zero] using
      ((hc.add ((macroLength_div_count_tendsto hL).div_const 1000)).add hi).add
        (macroblockDepth_div_count_tendsto hL δ)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with B hB
    exact ha.trans_le (macroConductor_ratio_bounds L δ hB).1
  · intro a ha
    filter_upwards [(tendsto_order.mp hu).2 a ha, eventually_ge_atTop (1 : ℕ)] with B huB hB
    exact (macroConductor_ratio_bounds L δ hB).2.trans_lt huB

/-- Eventually the actual conductor is below the original count, a usable boundary guard. -/
theorem eventually_macroConductor_le_count {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) :
    ∀ᶠ B in atTop, macroConductor L δ B ≤ B := by
  have h := (tendsto_order.mp (macroConductor_ratio_tendsto hL δ)).2 1 (by norm_num)
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with B hq hB
  have hb : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hlt : (macroConductor L δ B : ℝ) < B := by
    have he := (div_lt_iff₀ hb).mp hq
    simpa only [one_mul] using he
  exact Nat.le_of_lt (Nat.cast_lt.mp hlt)

end WordCertDensity.Construction
