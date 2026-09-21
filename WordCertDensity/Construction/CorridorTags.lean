/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.MacroHistories
public import WordCertDensity.Transfer.Capacity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer tags inside actual cumulative corridors

Both depth and total valuation lie in translated windows of radius delta*n.
Counting integers retains one point per coordinate, including zero-width windows.
Incoming prefix tags are counted separately and are not absorbed into a constant.
-/

@[expose] public section

namespace WordCertDensity.Construction

open scoped Classical

/-- Depth center obtained from the exact two-coordinate inversion. -/
noncomputable def corridorDepthCenter (n : ℕ) : ℝ :=
  ((n : ℝ) * stoppedExpectation (fun w => w.ordinaryCost) -
    (n : ℝ) * stoppedExpectation displacement) / (1 + Head.logRatio)

/-- Total-valuation center obtained from the same inversion. -/
noncomputable def corridorTotalCenter (n : ℕ) : ℝ :=
  (Head.logRatio * ((n : ℝ) * stoppedExpectation (fun w => w.ordinaryCost)) +
    (n : ℝ) * stoppedExpectation displacement) / (1 + Head.logRatio)

/-- Both actual integer coordinates have radius at most delta*n about their exact centers. -/
theorem macroCorridor_tag_windows {δ : ℝ} {n : ℕ} {w : ValuationWord}
    (hδ : 0 ≤ δ) (h : MacroCorridor δ n w) :
    |(w.length : ℝ) - corridorDepthCenter n| ≤ δ * n ∧
      |(w.total : ℝ) - corridorTotalCenter n| ≤ δ * n := by
  have hratio : 0 < Head.logRatio := lt_trans (by norm_num) Head.one_lt_logRatio
  have hd : 0 < 1 + Head.logRatio := by linarith
  have hr : 0 ≤ δ * (n : ℝ) := mul_nonneg hδ (Nat.cast_nonneg n)
  have hdepth : |((w.ordinaryCost : ℝ) - displacement w) -
      ((n : ℝ) * stoppedExpectation (fun v => v.ordinaryCost) -
        (n : ℝ) * stoppedExpectation displacement)| ≤ 2 * (δ * n) := by
    calc
      _ = |((w.ordinaryCost : ℝ) - (n : ℝ) *
          stoppedExpectation (fun v => v.ordinaryCost)) -
          (displacement w - (n : ℝ) * stoppedExpectation displacement)| := by congr 1; ring
      _ ≤ |(w.ordinaryCost : ℝ) - (n : ℝ) *
          stoppedExpectation (fun v => v.ordinaryCost)| +
          |displacement w - (n : ℝ) * stoppedExpectation displacement| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              abs_sub_le ((w.ordinaryCost : ℝ) - (n : ℝ) *
                stoppedExpectation (fun v => v.ordinaryCost)) 0
                (displacement w - (n : ℝ) * stoppedExpectation displacement)
      _ ≤ δ * n + δ * n := add_le_add h.2 h.1
      _ = _ := by ring
  have htotal : |(Head.logRatio * (w.ordinaryCost : ℝ) + displacement w) -
      (Head.logRatio * ((n : ℝ) * stoppedExpectation (fun v => v.ordinaryCost)) +
        (n : ℝ) * stoppedExpectation displacement)| ≤ (δ * n) * (1 + Head.logRatio) := by
    calc
      _ = |Head.logRatio * ((w.ordinaryCost : ℝ) -
          (n : ℝ) * stoppedExpectation (fun v => v.ordinaryCost)) +
          (displacement w - (n : ℝ) * stoppedExpectation displacement)| := by congr 1; ring
      _ ≤ |Head.logRatio * ((w.ordinaryCost : ℝ) -
          (n : ℝ) * stoppedExpectation (fun v => v.ordinaryCost))| +
          |displacement w - (n : ℝ) * stoppedExpectation displacement| := abs_add_le _ _
      _ = Head.logRatio * |(w.ordinaryCost : ℝ) -
          (n : ℝ) * stoppedExpectation (fun v => v.ordinaryCost)| +
          |displacement w - (n : ℝ) * stoppedExpectation displacement| := by
            rw [abs_mul, abs_of_pos hratio]
      _ ≤ Head.logRatio * (δ * n) + δ * n :=
        add_le_add (mul_le_mul_of_nonneg_left h.2 hratio.le) h.1
      _ = _ := by ring
  constructor
  · rw [word_depth_coordinates, corridorDepthCenter, ← sub_div, abs_div, abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    have hp := mul_nonneg hr (sub_nonneg.mpr Head.one_lt_logRatio.le)
    nlinarith
  · rw [word_total_coordinates, corridorTotalCenter, ← sub_div, abs_div, abs_of_pos hd]
    exact (div_le_iff₀ hd).mpr htotal

/-- Translating by the actual incoming prefix changes the centers, not the corridor widths. -/
theorem macroHistory_tag_windows {L δ : ℝ} {B : ℕ} {ws : List ValuationWord}
    (hδ : 0 ≤ δ) (h : MacroHistory L δ B ws) (incoming : ValuationWord) :
    let n := macroCount L B ws.length - B
    |((incoming ++ ws.flatten).length : ℝ) -
      ((incoming.length : ℝ) + corridorDepthCenter n)| ≤ δ * n ∧
    |(ValuationWord.total (incoming ++ ws.flatten) : ℝ) -
      ((incoming.total : ℝ) + corridorTotalCenter n)| ≤ δ * n := by
  have hw := macroCorridor_tag_windows hδ (macroHistory_corridor h)
  constructor
  · simpa only [List.length_append, Nat.cast_add, add_sub_add_left_eq_sub] using hw.1
  · simpa only [ValuationWord.total_append, Nat.cast_add, add_sub_add_left_eq_sub] using hw.2

/-- A translated closed natural-number window retains the sharp one-point term. -/
theorem nat_window_card_le (S : Finset ℕ) {c r : ℝ} (hr : 0 ≤ r)
    (hw : ∀ x ∈ S, |(x : ℝ) - c| ≤ r) : (S.card : ℝ) ≤ 2 * r + 1 := by
  have h := Transfer.residue_weight_capacity S 1 0
    (fun x _ => Nat.mod_one x) (by norm_num : (0 : ℝ) ≤ 1) (le_refl (1 : ℝ))
    (show 0 ≤ 2 * r by positivity) (fun x hx y hy => by
      have hxb := abs_le.mp (hw x hx)
      have hyb := abs_le.mp (hw y hy)
      linarith)
  simpa using h

/-- Counting both coordinate projections bounds all distinct natural pairs. -/
theorem natPair_window_card_le (S : Finset (ℕ × ℕ)) {cd ca rd ra : ℝ}
    (hd : 0 ≤ rd) (ha : 0 ≤ ra)
    (hw : ∀ t ∈ S, |(t.1 : ℝ) - cd| ≤ rd ∧ |(t.2 : ℝ) - ca| ≤ ra) :
    (S.card : ℝ) ≤ (2 * rd + 1) * (2 * ra + 1) := by
  have hsub : S ⊆ (S.image Prod.fst).product (S.image Prod.snd) := by
    intro t ht
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨t, ht, rfl⟩,
      Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩
  have hdcard := nat_window_card_le (S.image Prod.fst) hd (by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact (hw t ht).1)
  have hacard := nat_window_card_le (S.image Prod.snd) ha (by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact (hw t ht).2)
  have hc : (S.card : ℝ) ≤ ((S.image Prod.fst).card : ℝ) * (S.image Prod.snd).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (by simp)
  exact hc.trans (mul_le_mul hdcard hacard (Nat.cast_nonneg _) (by positivity))

/-- The actual history tags have a quadratic bound independent of the incoming translation. -/
theorem macroHistory_tag_card {α : Type*} (H : Finset α)
    (history : α → List ValuationWord) (incoming : ValuationWord) {L δ : ℝ} {B j : ℕ}
    (hδ : 0 ≤ δ) (hh : ∀ i ∈ H, MacroHistory L δ B (history i))
    (hj : ∀ i ∈ H, (history i).length = j) :
    ((H.image (fun i => Transfer.historyTag (incoming ++ (history i).flatten))).card : ℝ) ≤
      (2 * δ * (macroCount L B j - B : ℕ) + 1) ^ 2 := by
  have h := natPair_window_card_le
    (H.image (fun i => Transfer.historyTag (incoming ++ (history i).flatten)))
    (show 0 ≤ δ * (macroCount L B j - B : ℕ) by positivity)
    (show 0 ≤ δ * (macroCount L B j - B : ℕ) by positivity) (by
      intro t ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      simpa only [Transfer.historyTag, hj i hi] using
        macroHistory_tag_windows hδ (hh i hi) incoming)
  simpa only [pow_two, mul_assoc] using h

/-- Appended tags are covered by all pairs of incoming and continuation tags. -/
theorem historyTag_append_card_le {α : Type*} (H : Finset α)
    (incoming continuation : α → ValuationWord) :
    (H.image (fun i => Transfer.historyTag (incoming i ++ continuation i))).card ≤
      (H.image (fun i => Transfer.historyTag (incoming i))).card *
        (H.image (fun i => Transfer.historyTag (continuation i))).card := by
  let P := H.image (fun i => Transfer.historyTag (incoming i))
  let C := H.image (fun i => Transfer.historyTag (continuation i))
  let addTags : (ℕ × ℕ) × (ℕ × ℕ) → ℕ × ℕ := fun t => (t.1.1 + t.2.1, t.1.2 + t.2.2)
  have hsub : H.image (fun i => Transfer.historyTag (incoming i ++ continuation i)) ⊆
      (P.product C).image addTags := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    refine Finset.mem_image.mpr ⟨(Transfer.historyTag (incoming i),
      Transfer.historyTag (continuation i)), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩,
        Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
    · simp [addTags, Transfer.historyTag]
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans_eq (by simp [P, C]))

/-- A variable incoming family pays its actual number of distinct incoming tags. -/
theorem macroHistory_incoming_tag_card {α : Type*} (H : Finset α)
    (history : α → List ValuationWord) (incoming : α → ValuationWord) {L δ : ℝ} {B j : ℕ}
    (hδ : 0 ≤ δ) (hh : ∀ i ∈ H, MacroHistory L δ B (history i))
    (hj : ∀ i ∈ H, (history i).length = j) :
    ((H.image (fun i => Transfer.historyTag (incoming i ++ (history i).flatten))).card : ℝ) ≤
      ((H.image (fun i => Transfer.historyTag (incoming i))).card : ℝ) *
        (2 * δ * (macroCount L B j - B : ℕ) + 1) ^ 2 := by
  have hc := historyTag_append_card_le H incoming (fun i => (history i).flatten)
  have ht := macroHistory_tag_card H history [] hδ hh hj
  simp only [List.nil_append] at ht
  have hcr : ((H.image (fun i => Transfer.historyTag (incoming i ++
      (history i).flatten))).card : ℝ) ≤
      ((H.image (fun i => Transfer.historyTag (incoming i))).card : ℝ) *
        (H.image (fun i => Transfer.historyTag (history i).flatten)).card := by
    exact_mod_cast hc
  exact hcr.trans (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _))

/-- The actual-count tag budget is bounded by a fixed multiple of (B+1)^2. -/
theorem corridorTagBudget_le {δ : ℝ} (hδ : 0 ≤ δ) (B B₀ : ℕ) :
    (2 * δ * (B - B₀ : ℕ) + 1) ^ 2 ≤ (2 * δ + 1) ^ 2 * ((B : ℝ) + 1) ^ 2 := by
  have hn : ((B - B₀ : ℕ) : ℝ) ≤ B := Nat.cast_le.mpr (Nat.sub_le B B₀)
  have hp := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2 * δ by positivity)
  have hbase : 2 * δ * (B - B₀ : ℕ) + 1 ≤ (2 * δ + 1) * ((B : ℝ) + 1) := by
    have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    nlinarith
  exact ((sq_le_sq₀ (by positivity) (by positivity)).mpr hbase).trans_eq (mul_pow _ _ 2)

end WordCertDensity.Construction
