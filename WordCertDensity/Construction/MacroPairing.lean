/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.MacroBoundary
import WordCertDensity.Construction.MacroCapacity
import WordCertDensity.Transfer.CapacityPairing

/-!
# Actual macroblock pairing and summability

Both corridor and unrestricted tag budgets fit a cubic summable envelope.
The physical-history consumer keeps the incoming tags and offset. Physicality
and within-tag uniqueness are supplied by the later source construction.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- The literal stopped-transfer test at the next macroblock and the old positive level. -/
noncomputable def macroVariationTest (L δ : ℝ) (B : ℕ) (hB : 1 ≤ B) :
    ZMod (3 ^ macroConductor L δ B) → ℝ := fun a =>
  Transfer.coarseSelected (macroblocks L δ B) (macroConductor L δ B)
      (macroLevel (B + macroLength L B))
      (fun _ hw => (macroConductor_word_guards hw).2) a -
    Reference.marker (macroLevel B)
      (Reference.project (macroConductor_guards L δ hB).2.2.2 a)

/-- The actual macroblock pairing retains all tags, the offset window, and all three errors. -/
theorem macro_stopped_variation {α : Type*} (H : Finset α)
    (word : α → ValuationWord) (source : α → ℕ) {M B : ℕ} {L δ T C : ℝ}
    (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hphysical : ∀ i ∈ H, PhysicalHistory (word i) M (source i))
    (hinj : ∀ i ∈ H, ∀ j ∈ H, Transfer.historyTag (word i) =
      Transfer.historyTag (word j) → source i = source j → i = j)
    (hweight : ∀ i ∈ H, Transfer.weight (word i) ≤ (1 / 8 : ℝ) ^ B)
    (hoffset : ∀ i ∈ H, (0 : ℝ) ≤ ((word i).offset : ℝ) ∧ ((word i).offset : ℝ) ≤ C)
    (htags : ((H.image (fun i => Transfer.historyTag (word i))).card : ℝ) ≤ T) :
    (∑ a, Transfer.historyHistogram H word source (macroConductor L δ B) a *
      |macroVariationTest L δ B hB a|) ≤
        (2 / 3 : ℝ) * T * (C + macroBoundary L δ B) * macroError L δ B := by
  have hg := macroConductor_guards L δ hB
  have h := Transfer.history_stopped_variation H word source (macroblocks L δ B)
    hphysical hinj hweight (by positivity) hC hoffset htags
    (fun _ hw => (macroConductor_word_guards hw).1)
    (fun _ hw => (macroConductor_word_guards hw).2)
    (hg.1.trans hg.2.1) hg.1 hg.2.2.2 (macroblocks_prefixFree L δ B)
  simpa only [macroVariationTest, macroBoundary, macroError, macroblockMass, sub_zero] using h

/-- Retained histories supply contraction, offset and literal incoming-tag multiplicity. -/
theorem macroHistory_stopped_variation {α : Type*} (H : Finset α)
    (incoming : α → ValuationWord) (history : α → List ValuationWord) (source : α → ℕ)
    {L δ C : ℝ} {B j M : ℕ} (hB : 1 ≤ macroCount L B j) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hh : ∀ i ∈ H, MacroHistory L δ B (history i))
    (hj : ∀ i ∈ H, (history i).length = j)
    (hpre : ∀ i ∈ H, Transfer.weight (incoming i) ≤ (1 / 8 : ℝ) ^ B)
    (hoff : ∀ i ∈ H, ((incoming i).offset : ℝ) ≤ C)
    (hphysical : ∀ i ∈ H, PhysicalHistory (incoming i ++ (history i).flatten) M (source i))
    (hinj : ∀ i ∈ H, ∀ k ∈ H,
      Transfer.historyTag (incoming i ++ (history i).flatten) =
        Transfer.historyTag (incoming k ++ (history k).flatten) →
      source i = source k → i = k) :
    (∑ a, Transfer.historyHistogram H (fun i => incoming i ++ (history i).flatten)
      source (macroConductor L δ (macroCount L B j)) a *
        |macroVariationTest L δ (macroCount L B j) hB a|) ≤
      (2 / 3 : ℝ) *
        (((H.image (fun i => Transfer.historyTag (incoming i))).card : ℝ) *
          (2 * δ * (macroCount L B j - B : ℕ) + 1) ^ 2) *
        ((C + continuationOffsetBound) + macroBoundary L δ (macroCount L B j)) *
        macroError L δ (macroCount L B j) := by
  apply macro_stopped_variation H (fun i => incoming i ++ (history i).flatten) source hB
    (add_nonneg hC continuationOffsetBound_bounds.1) hphysical hinj
  · intro i hi
    simpa only [hj i hi] using macroHistory_incoming_weight_le (hh i hi) (incoming i) (hpre i hi)
  · intro i hi
    refine ⟨Rat.cast_nonneg.mpr (ValuationWord.offset_nonneg _), ?_⟩
    exact (macroHistory_incoming_offset_le (hh i hi) (incoming i) (hpre i hi)).trans
      (add_le_add (hoff i hi) (le_refl continuationOffsetBound))
  · exact macroHistory_incoming_tag_card H history incoming hδ hh hj

/-- Any eventually cubic tag budget gives a summable actual error, including its boundary. -/
theorem summable_tag_macroError {L δ P C : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) (hP : 0 ≤ P) (hC : 0 ≤ C)
    (T : ℕ → ℝ) (hT : ∀ B, 0 ≤ T B)
    (hbound : ∀ᶠ B in atTop, T B ≤ P * ((B : ℝ) + 2) ^ 3) :
    Summable (fun B => T B * (C + macroBoundary L δ B) * macroError L δ B) := by
  have hs := (summable_cube_macroError hL hδ hpay).mul_left (P * (C + 1))
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hbound, eventually_macroBoundary_le_one hL δ,
    eventually_ge_atTop (1 : ℕ)] with B ht hb hB
  have he := macroError_nonneg L δ hB
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (hT B) (add_nonneg hC (macroBoundary_pos L δ B).le)) he)]
  calc
    _ ≤ (P * ((B : ℝ) + 2) ^ 3) * (C + 1) * macroError L δ B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul ht (add_le_add le_rfl hb)
          (add_nonneg hC (macroBoundary_pos L δ B).le) (by positivity)) he
    _ = _ := by ring

/-- The summed corridor tag budget is square-polynomial, hence summable with all error costs. -/
theorem summable_corridor_macroError {L δ C : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) (hC : 0 ≤ C) :
    Summable (fun B : ℕ => ((B : ℝ) + 1) ^ 2 *
      (C + macroBoundary L δ B) * macroError L δ B) := by
  apply summable_tag_macroError hL hδ hpay (P := 1) (by norm_num) hC _ (fun B => by positivity)
  apply Eventually.of_forall
  intro B
  have hb := Nat.cast_nonneg (α := ℝ) B
  nlinarith [sq_nonneg (B : ℝ), mul_nonneg hb (sq_nonneg (B : ℝ))]

/-- The unrestricted quadratic-log-squared tag budget is also summable over every count. -/
theorem summable_unrestricted_macroError {L δ C : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) (hC : 0 ≤ C) :
    Summable (fun B : ℕ => (((B : ℝ) + 1) ^ 2 * Real.log ((B : ℝ) + 2) ^ 2) *
      (C + macroBoundary L δ B) * macroError L δ B) := by
  apply summable_tag_macroError hL hδ hpay (P := 1) (by norm_num) hC _ (fun B => by positivity)
  have hl := (tendsto_order.mp (logpow_div_count_tendsto 2)).2 1 (by norm_num)
  filter_upwards [hl, eventually_ge_atTop (1 : ℕ)] with B hlB hB
  have hb : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hlog : Real.log ((B : ℝ) + 2) ^ 2 ≤ (B : ℝ) + 2 := by
    have h := (div_lt_iff₀ hb).mp hlB
    linarith
  have hs : ((B : ℝ) + 1) ^ 2 ≤ ((B : ℝ) + 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc
    _ ≤ ((B : ℝ) + 2) ^ 2 * ((B : ℝ) + 2) :=
      mul_le_mul hs hlog (sq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

/-- Restricting the summable corridor envelope to actual macrocounts preserves summability. -/
theorem summable_corridor_macroError_schedule {L δ C : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) (hC : 0 ≤ C) (B : ℕ) :
    Summable (fun j : ℕ => ((macroCount L B j : ℝ) + 1) ^ 2 *
      (C + macroBoundary L δ (macroCount L B j)) * macroError L δ (macroCount L B j)) :=
  (summable_corridor_macroError hL.le hδ hpay hC).comp_injective
    (macroCount_strictMono hL B).injective


/-- Actual retained-history variation is summable along the complete macro schedule.
The zero-level initial stage is omitted explicitly; incoming multiplicity is uniformly paid. -/
theorem summable_macroHistory_variation {α : Type*} (H : ℕ → Finset α)
    (incoming : ℕ → α → ValuationWord) (history : ℕ → α → List ValuationWord)
    (source : ℕ → α → ℕ) {L δ C P : ℝ} {B M : ℕ}
    (hL : 0 < L) (hδ : 0 < δ) (hpay : 10 ≤ stoppedCorridorRate δ * L)
    (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hh : ∀ j, ∀ i ∈ H j, MacroHistory L δ B (history j i))
    (hj : ∀ j, ∀ i ∈ H j, (history j i).length = j)
    (hpre : ∀ j, ∀ i ∈ H j, Transfer.weight (incoming j i) ≤ (1 / 8 : ℝ) ^ B)
    (hoff : ∀ j, ∀ i ∈ H j, ((incoming j i).offset : ℝ) ≤ C)
    (hphysical : ∀ j, ∀ i ∈ H j,
      PhysicalHistory (incoming j i ++ (history j i).flatten) M (source j i))
    (hinj : ∀ j, ∀ i ∈ H j, ∀ k ∈ H j,
      Transfer.historyTag (incoming j i ++ (history j i).flatten) =
        Transfer.historyTag (incoming j k ++ (history j k).flatten) →
      source j i = source j k → i = k)
    (htags : ∀ j, (((H j).image (fun i => Transfer.historyTag (incoming j i))).card : ℝ) ≤ P) :
    Summable (fun j : ℕ => if hB : 1 ≤ macroCount L B j then
      ∑ a, Transfer.historyHistogram (H j)
        (fun i => incoming j i ++ (history j i).flatten) (source j)
        (macroConductor L δ (macroCount L B j)) a *
          |macroVariationTest L δ (macroCount L B j) hB a| else 0) := by
  have hc := add_nonneg hC continuationOffsetBound_bounds.1
  have hs := (summable_corridor_macroError_schedule hL hδ hpay hc B).mul_left
    ((2 / 3 : ℝ) * P * (2 * δ + 1) ^ 2)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hjpos
  have hB : 1 ≤ macroCount L B j := by
    have h := macroCount_lower hL B j
    omega
  rw [dif_pos hB]
  have he := macroError_nonneg L δ hB
  have ho := add_nonneg hc (macroBoundary_pos L δ (macroCount L B j)).le
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun a _ =>
    mul_nonneg (Transfer.historyHistogram_nonneg _ _ _ _ a) (abs_nonneg _)))]
  have hv := macroHistory_stopped_variation (H j) (incoming j) (history j) (source j)
    hB hδ.le hC (hh j) (hj j) (hpre j) (hoff j) (hphysical j) (hinj j)
  have ht := mul_le_mul (htags j) (corridorTagBudget_le hδ.le (macroCount L B j) B)
    (sq_nonneg _) hP
  calc
    _ ≤ _ := hv
    _ ≤ (2 / 3 : ℝ) *
        (P * ((2 * δ + 1) ^ 2 * ((macroCount L B j : ℝ) + 1) ^ 2)) *
        ((C + continuationOffsetBound) + macroBoundary L δ (macroCount L B j)) *
        macroError L δ (macroCount L B j) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num)) ho) he
    _ = _ := by ring


/-- Full histories from block one have one incoming tag and zero incoming offset. -/
theorem summable_full_macroHistory_variation {α : Type*} (H : ℕ → Finset α)
    (history : ℕ → α → List ValuationWord) (source : ℕ → α → ℕ) {L δ : ℝ} {M : ℕ}
    (hL : 0 < L) (hδ : 0 < δ) (hpay : 10 ≤ stoppedCorridorRate δ * L)
    (hh : ∀ j, ∀ i ∈ H j, MacroHistory L δ 0 (history j i))
    (hj : ∀ j, ∀ i ∈ H j, (history j i).length = j)
    (hphysical : ∀ j, ∀ i ∈ H j, PhysicalHistory (history j i).flatten M (source j i))
    (hinj : ∀ j, ∀ i ∈ H j, ∀ k ∈ H j,
      Transfer.historyTag (history j i).flatten = Transfer.historyTag (history j k).flatten →
      source j i = source j k → i = k) :
    Summable (fun j : ℕ => if hB : 1 ≤ macroCount L 0 j then
      ∑ a, Transfer.historyHistogram (H j) (fun i => (history j i).flatten) (source j)
        (macroConductor L δ (macroCount L 0 j)) a *
          |macroVariationTest L δ (macroCount L 0 j) hB a| else 0) := by
  classical
  have htags : ∀ j, (((H j).image (fun _ => Transfer.historyTag [])).card : ℝ) ≤ 1 := by
    intro j
    have hs : (H j).image (fun _ => Transfer.historyTag []) ⊆ {Transfer.historyTag []} := by
      intro x hx
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hx
      exact Finset.mem_singleton.mpr he.symm
    have hc := Finset.card_le_card hs
    simpa only [Finset.card_singleton, Nat.cast_le, Nat.cast_one] using
      (Nat.cast_le (α := ℝ)).mpr hc
  have h := summable_macroHistory_variation H (fun _ _ => []) history source
    (C := 0) (P := 1) hL hδ hpay (by norm_num) (by norm_num) hh hj
    (by intro j i hi; simp only [Transfer.weight_nil, pow_zero, le_refl])
    (by intro j i hi; norm_num [ValuationWord.offset])
    (by simpa only [List.nil_append] using hphysical)
    (by simpa only [List.nil_append] using hinj) htags
  simpa only [List.nil_append] using h

end WordCertDensity.Construction
