/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftAppended
import WordCertDensity.Construction.SeedHistories

/-! # Uniform offset absorption and physical graft realization

One splice threshold absorbs every appended offset, uniformly in the root and
continuation stage. The resulting strict offset margin turns actual modular
compatibility into a unique physical branch; no further selection loss occurs.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- The manuscript's root-independent bound on the seed-scaled appended offset. -/
noncomputable def graftOffsetAbsorption (b t : ℕ) : ℝ :=
  (16 : ℝ) ^ b * ((8 / 7 : ℝ) * (1 / 8 : ℝ) ^ seedSize b t +
    (graftOffsetConstant : ℝ) * (1 / 16 : ℝ) ^ seedSize b t)

/-- The seed schedule tends to infinity with its actual integer rounding. -/
theorem seedSize_tendsto {b : ℕ} (hb : 100 ≤ b) : Tendsto (seedSize b) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [eventually_ge_atTop K] with t ht
  have hs := seedSize_ge_add hb t
  omega

/-- The literal scaled appended envelope has the displayed geometric absorption bound. -/
theorem graftAppendedOffset_scaled (b t : ℕ) :
    ((16 : ℝ) ^ b / 16 ^ seedSize b t) * graftAppendedOffset b t ≤
      graftOffsetAbsorption b t := by
  have hE : graftPrecision b t ≤ seedSize b t := Nat.sqrt_le_self _
  have hp : (3 / 2 : ℝ) ^ (graftPrecision b t - 1) ≤ (2 : ℝ) ^ seedSize b t :=
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num) _).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 8 / 7)
  have hs := mul_le_mul_of_nonneg_left
    (add_le_add hm (le_refl (graftOffsetConstant : ℝ)))
    (show 0 ≤ (16 : ℝ) ^ b / 16 ^ seedSize b t by positivity)
  refine hs.trans_eq ?_
  have h8 : ((16 : ℝ) ^ seedSize b t)⁻¹ * 2 ^ seedSize b t =
      (1 / 8 : ℝ) ^ seedSize b t := by
    rw [← inv_pow, ← mul_pow]
    norm_num
  have h16 : ((16 : ℝ) ^ seedSize b t)⁻¹ = (1 / 16 : ℝ) ^ seedSize b t := by
    rw [← inv_pow]
    norm_num
  calc
    _ = (16 : ℝ) ^ b * ((8 / 7 : ℝ) *
        (((16 : ℝ) ^ seedSize b t)⁻¹ * 2 ^ seedSize b t) +
        (graftOffsetConstant : ℝ) * ((16 : ℝ) ^ seedSize b t)⁻¹) := by
      simp only [div_eq_mul_inv]
      ring
    _ = graftOffsetAbsorption b t := by rw [h8, h16]; rfl

/-- The complete seed-scaled appended envelope vanishes as the splice moves later. -/
theorem graftOffsetAbsorption_tendsto {b : ℕ} (hb : 100 ≤ b) :
    Tendsto (graftOffsetAbsorption b) atTop (𝓝 0) := by
  have h8 := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1)).comp (seedSize_tendsto hb)
  have h16 := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1)).comp (seedSize_tendsto hb)
  change Tendsto (fun t => (16 : ℝ) ^ b *
    ((8 / 7 : ℝ) * (1 / 8 : ℝ) ^ seedSize b t +
      (graftOffsetConstant : ℝ) * (1 / 16 : ℝ) ^ seedSize b t)) atTop (𝓝 0)
  simpa only [Function.comp_apply, mul_zero, add_zero] using
    ((h8.const_mul (8 / 7 : ℝ)).add (h16.const_mul (graftOffsetConstant : ℝ))).const_mul
      ((16 : ℝ) ^ b)

/-- One eventual threshold pays the offset uniformly in every root and continuation stage. -/
theorem graftOffsetAbsorption_eventually {b : ℕ} (hb : 100 ≤ b) :
    ∀ᶠ t in atTop, graftOffsetAbsorption b t ≤ 1 :=
  ((graftOffsetAbsorption_tendsto hb).eventually_lt_const (by norm_num : (0 : ℝ) < 1)).mono
    (fun _ h => h.le)

/-- The total seed-plus-appended offset is below C_* once the one uniform absorption is paid. -/
theorem graftTotal_offset {b t : ℕ} (hb : 32 ^ 5 ≤ b) {pre : List ValuationWord}
    (hpre : SeedBlocks b 0 pre) (hlen : pre.length = t)
    {L δ : ℝ} {w : ValuationWord} (hw : w ∈ graftTransitionWords δ b t)
    {ws : List ValuationWord} (hws : MacroHistory L δ (graftInitialCount b t) ws)
    (hpaid : graftOffsetAbsorption b t ≤ 1) :
    (ValuationWord.offset (pre.flatten ++ (w ++ ws.flatten)) : ℝ) < (2 : ℝ) ^ (b + 1) + 1 := by
  have hsQ := seedBlocks_slope_le hb hpre
  have hsR : Transfer.weight pre.flatten ≤ (16 : ℝ) ^ b / 16 ^ seedSize b t := by
    have hs := Rat.cast_le (K := ℝ) |>.mpr hsQ
    simpa only [Transfer.weight, seedSize, Nat.zero_add, hlen, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat] using hs
  have hoQ := seedBlocks_offset_lt hb hpre
  have hoR : (ValuationWord.offset pre.flatten : ℝ) < (2 : ℝ) ^ (b + 1) := by
    have ho := Rat.cast_lt (K := ℝ) |>.mpr hoQ
    simpa only [seedSize, Rat.cast_pow, Rat.cast_ofNat] using ho
  have hm := mul_le_mul hsR (graftAppended_offset hw hws)
    (Rat.cast_nonneg.mpr (ValuationWord.offset_nonneg (w ++ ws.flatten)))
    (show 0 ≤ (16 : ℝ) ^ b / 16 ^ seedSize b t by positivity)
  have ha := hm.trans ((graftAppendedOffset_scaled b t).trans hpaid)
  rw [ValuationWord.offset_append, Rat.cast_add, Rat.cast_mul]
  change (ValuationWord.offset pre.flatten : ℝ) +
    Transfer.weight pre.flatten * (ValuationWord.offset (w ++ ws.flatten) : ℝ) < _
  linarith

/-- The fixed offset ceiling lies strictly below every allowed root height. -/
theorem graftOffset_ceiling_lt {b : ℕ} (hb : 1 ≤ b) :
    (2 : ℝ) ^ (b + 1) + 1 < (16 : ℝ) ^ b := by
  have hpow : (1 : ℝ) < 2 ^ (b + 1) := one_lt_pow₀ (by norm_num) (by omega)
  have hstep : (2 : ℝ) ^ (b + 2) ≤ (16 : ℝ) ^ b := by
    calc
      _ ≤ (2 : ℝ) ^ (4 * b) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := by rw [pow_mul]; norm_num
  have he : (2 : ℝ) ^ (b + 2) = (2 : ℝ) ^ (b + 1) * 2 := by rw [← pow_succ]
  rw [he] at hstep
  linarith

/-- Every compatible total word has a unique physical source, with no additional rejection. -/
theorem graftTotal_realizes {b t root q : ℕ} (hb : 32 ^ 5 ≤ b)
    {pre : List ValuationWord} (hpre : SeedBlocks b 0 pre) (hlen : pre.length = t)
    {L δ : ℝ} {w : ValuationWord} (hw : w ∈ graftTransitionWords δ b t)
    {ws : List ValuationWord} (hws : MacroHistory L δ (graftInitialCount b t) ws)
    (hpaid : graftOffsetAbsorption b t ≤ 1) (hroot : 16 ^ b ≤ root) (hodd : Odd root)
    (hq : (pre.flatten ++ (w ++ ws.flatten)).length ≤ q)
    (hc : (root : ZMod (3 ^ q)) ∈
      Set.range (Transfer.wordMap (pre.flatten ++ (w ++ ws.flatten)) q)) :
    ∃! source : ℕ, PhysicalHistory (pre.flatten ++ (w ++ ws.flatten)) root source := by
  have hlarge : ValuationWord.offset (pre.flatten ++ (w ++ ws.flatten)) < (root : ℚ) := by
    apply Rat.cast_lt (K := ℝ) |>.mp
    have hr : (16 : ℝ) ^ b ≤ (root : ℝ) := by exact_mod_cast hroot
    have h := (graftTotal_offset hb hpre hlen hw hws hpaid).trans
      ((graftOffset_ceiling_lt (by omega : 1 ≤ b)).trans_le hr)
    simpa only [Rat.cast_natCast] using h
  obtain ⟨source, hp⟩ := (Transfer.mem_range_wordMap_iff_physical _ hq root hodd hlarge).mp hc
  exact ⟨source, hp, fun _ h => h.source_unique hp⟩

end WordCertDensity.Construction
