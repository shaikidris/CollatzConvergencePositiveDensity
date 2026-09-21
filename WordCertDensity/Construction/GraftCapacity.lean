/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftRecords
import WordCertDensity.Construction.CorridorTags
import WordCertDensity.Construction.SeedCapacity

/-! # Fresh capacity at every level for physical hybrid histories

The exceptional transition belongs to the appended corridor. Its tags are
counted together with the later macro words, separately from the incoming
seed tags. Full-record uniqueness permits one physical source per total tag.
The spacing estimate retains its boundary term at every modulus.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- The incoming seed contraction is at most one, so every appended block is paid. -/
theorem graftRecords_weight {L δ : ℝ} {b t j : ℕ} (hb : 32 ^ 5 ≤ b)
    {r : GraftRecord} (hr : r ∈ graftRecords L δ b t j) :
    Transfer.weight (graftRecordWord r) ≤
      (1 / 8 : ℝ) ^ macroCount L (graftInitialCount b t) j := by
  obtain ⟨hlen, hpre, hw, hmlen, hmacro⟩ := (mem_graftRecords L δ b t j r).mp hr
  have hsQ : ValuationWord.slope r.1.flatten ≤ (16 : ℚ) ^ b / 16 ^ seedSize b t := by
    simpa only [seedSize, Nat.zero_add, hlen] using seedBlocks_slope_le hb hpre
  have hsR := Rat.cast_le (K := ℝ) |>.mpr hsQ
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at hsR
  have hpreone : Transfer.weight r.1.flatten ≤ 1 := by
    apply hsR.trans
    exact (div_le_one (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 16) (seedSize_ge b t))
  have happ := graftAppended_weight hw hmacro
  rw [hmlen] at happ
  calc
    _ = Transfer.weight r.1.flatten * Transfer.weight (r.2.1 ++ r.2.2.flatten) := by
      simp only [graftRecordWord, Transfer.weight, ValuationWord.slope_append, Rat.cast_mul]
    _ ≤ 1 * (1 / 8 : ℝ) ^ macroCount L (graftInitialCount b t) j :=
      mul_le_mul hpreone happ (Transfer.weight_pos _).le zero_le_one
    _ = _ := one_mul _

/-- A restriction of hybrid records keeps the full appended corridor's quadratic tag bound. -/
theorem graftRecords_appended_tag_card (H : Finset GraftRecord) {L δ : ℝ} {b t j : ℕ}
    (hδ : 0 ≤ δ) (hH : H ⊆ graftRecords L δ b t j) :
    ((H.image fun r => Transfer.historyTag (r.2.1 ++ r.2.2.flatten)).card : ℝ) ≤
      (2 * δ * macroCount L (graftInitialCount b t) j + 1) ^ 2 := by
  have h := natPair_window_card_le
    (H.image fun r => Transfer.historyTag (r.2.1 ++ r.2.2.flatten))
    (show 0 ≤ δ * macroCount L (graftInitialCount b t) j by positivity)
    (show 0 ≤ δ * macroCount L (graftInitialCount b t) j by positivity) (by
      intro tag htag
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp htag
      obtain ⟨_, _, hw, hlen, hmacro⟩ := (mem_graftRecords L δ b t j r).mp (hH hr)
      simpa only [Transfer.historyTag, hlen] using
        macroCorridor_tag_windows hδ (graftAppended_corridor hw hmacro))
  simpa only [pow_two, mul_assoc] using h

/-- The total tag count pays incoming growth once, even when tag sums coincide. -/
theorem graftRecords_tag_card (H : Finset GraftRecord) {L δ : ℝ} {b t j : ℕ}
    (hb : 200 ≤ b) (hδ : 0 ≤ δ) (hsmall : 2 * δ ≤ 1)
    (hH : H ⊆ graftRecords L δ b t j) :
    ((H.image fun r => Transfer.historyTag (graftRecordWord r)).card : ℝ) ≤
      seedCapacity b t * ((macroCount L (graftInitialCount b t) j : ℝ) + 1) ^ 2 := by
  have hseed := seedHistory_tag_budget (H.image Prod.fst) hb (by
    intro pre hpre
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hpre
    obtain ⟨hlen, hs, _, _, _⟩ := (mem_graftRecords L δ b t j r).mp (hH hr)
    exact (mem_seedBlockLists b 0 t r.1).mpr ⟨hlen, hs⟩)
  have hin : ((H.image fun r => Transfer.historyTag r.1.flatten).card : ℝ) ≤
      seedCapacity b t := by
    simpa only [Finset.image_image, Function.comp_def] using
      hseed.trans (seedTagBudget_le_capacity b t)
  have happ := graftRecords_appended_tag_card H hδ hH
  have hbase : 2 * δ * macroCount L (graftInitialCount b t) j + 1 ≤
      (macroCount L (graftInitialCount b t) j : ℝ) + 1 := by
    have h := mul_le_mul_of_nonneg_right hsmall
      (Nat.cast_nonneg (macroCount L (graftInitialCount b t) j) :
        (0 : ℝ) ≤ macroCount L (graftInitialCount b t) j)
    linarith
  have hsquare := (sq_le_sq₀ (by positivity) (by positivity)).mpr hbase
  have hc : ((H.image fun r => Transfer.historyTag (graftRecordWord r)).card : ℝ) ≤
      ((H.image fun r => Transfer.historyTag r.1.flatten).card : ℝ) *
        (H.image fun r => Transfer.historyTag (r.2.1 ++ r.2.2.flatten)).card := by
    exact_mod_cast historyTag_append_card_le H (fun r => r.1.flatten)
      (fun r => r.2.1 ++ r.2.2.flatten)
  exact hc.trans (mul_le_mul hin (happ.trans hsquare) (Nat.cast_nonneg _)
    ((seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)))

/-- Every modulus has the fresh physical capacity bound, including its residual point term. -/
theorem physicalGraftRecords_capacity (H : Finset GraftRecord) {L δ : ℝ}
    {b t j root : ℕ} (hb : 32 ^ 5 ≤ b) (hδ : 0 ≤ δ) (hsmall : 2 * δ ≤ 1)
    (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hH : H ⊆ physicalGraftRecords L δ b t j root)
    (q : ℕ) (a : ZMod (3 ^ q)) :
    (3 : ℝ) ^ q * Transfer.historyHistogram H graftRecordWord (graftRecordSource root) q a ≤
      (seedCapacity b t * ((macroCount L (graftInitialCount b t) j : ℝ) + 1) ^ 2) *
        ((2 : ℝ) ^ (b + 1) + 1 +
          (3 : ℝ) ^ q * (1 / 8 : ℝ) ^ macroCount L (graftInitialCount b t) j) := by
  have member r (hr : r ∈ H) :=
    (mem_physicalGraftRecords L δ b t j root r).mp (hH hr)
  have hoff r (hr : r ∈ H) : (0 : ℝ) ≤ ((graftRecordWord r).offset : ℝ) ∧
      ((graftRecordWord r).offset : ℝ) ≤ (2 : ℝ) ^ (b + 1) + 1 := by
    obtain ⟨hlen, hpre, hw, _, hmacro⟩ := (mem_graftRecords L δ b t j r).mp (member r hr).1
    exact ⟨Rat.cast_nonneg.mpr (ValuationWord.offset_nonneg _),
      (graftTotal_offset hb hpre hlen hw hmacro hpaid).le⟩
  have h := Transfer.history_capacity H graftRecordWord (graftRecordSource root) q a
    (fun r hr => (member r hr).2)
    (fun r hr s hs ht he => physicalGraftRecords_source_injective
      (by omega : 0 < b) (hH hr) (hH hs) ht he)
    (fun r hr => graftRecords_weight hb (member r hr).1)
    (by positivity) (by positivity) hoff
    (graftRecords_tag_card H (by omega : 200 ≤ b) hδ hsmall
      (fun r hr => (member r hr).1))
  simpa only [sub_zero] using h

end WordCertDensity.Construction
