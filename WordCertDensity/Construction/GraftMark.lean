/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftRecords
import WordCertDensity.Construction.SeedExtension

/-! # Actual hybrid marks and their transition-stage decomposition

The zero-stage hybrid family consists exactly of actual seed parents and
their physical transition children. Its marked sum retains the original
product weights and counts each such pair once.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- The actual physical hybrid mark at its cumulative original-block marker level. -/
noncomputable def physicalGraftMark (L δ : ℝ) (b t j root : ℕ) : ℝ :=
  ∑ r ∈ physicalGraftRecords L δ b t j root, Transfer.weight (graftRecordWord r) *
    Reference.marker (macroLevel (macroCount L (graftInitialCount b t) j))
      (graftRecordSource root r : ZMod (3 ^ macroLevel (macroCount L (graftInitialCount b t) j)))

/-- A zero-stage physical record is precisely an actual seed parent and physical transition. -/
theorem mem_physicalGraftRecords_zero (L δ : ℝ) (b t root : ℕ)
    (pre : List ValuationWord) (w : ValuationWord) :
    (pre, w, []) ∈ physicalGraftRecords L δ b t 0 root ↔
      pre ∈ physicalSeedHistories b t root ∧ w ∈ graftTransitionWords δ b t ∧
        ∃ source, PhysicalHistory w (seedHistorySource root pre) source := by
  have hform : (pre, w, []) ∈ graftRecords L δ b t 0 ↔
      pre ∈ seedBlockLists b 0 t ∧ w ∈ graftTransitionWords δ b t := by
    simp only [mem_graftRecords, mem_seedBlockLists, List.length_nil, MacroHistory, and_true,
      and_assoc]
  constructor
  · intro hr
    obtain ⟨hf, hp⟩ := (mem_physicalGraftRecords L δ b t 0 root _).mp hr
    obtain ⟨hpre, hw⟩ := hform.mp hf
    have hfull : PhysicalHistory (pre.flatten ++ w) root (graftRecordSource root (pre, w, [])) := by
      simpa only [graftRecordWord, List.flatten_nil, List.append_nil] using hp
    obtain ⟨middle, hparent, hchild⟩ := hfull.append_split
    have he := seedHistorySource_eq hparent
    refine ⟨(mem_physicalSeedHistories b t root pre).mpr ⟨hpre, ?_⟩, hw, ?_⟩
    · simpa only [he] using hparent
    · exact ⟨_, by simpa only [he] using hchild⟩
  · rintro ⟨hp, hw, source, hc⟩
    obtain ⟨hpre, hparent⟩ := (mem_physicalSeedHistories b t root pre).mp hp
    have hfull : PhysicalHistory (graftRecordWord (pre, w, [])) root source := by
      simpa only [graftRecordWord, List.flatten_nil, List.append_nil] using hparent.append hc
    exact (mem_physicalGraftRecords L δ b t 0 root _).mpr
      ⟨hform.mpr ⟨hpre, hw⟩, by simpa only [graftRecordSource_eq hfull] using hfull⟩

/-- The zero-stage source is the transition's actual source at the incoming parent. -/
theorem graftRecordSource_zero {root source : ℕ} {pre : List ValuationWord} {w : ValuationWord}
    (hp : PhysicalHistory pre.flatten root (seedHistorySource root pre))
    (hc : PhysicalHistory w (seedHistorySource root pre) source) :
    graftRecordSource root (pre, w, []) = source := by
  apply graftRecordSource_eq
  simpa only [graftRecordWord, List.flatten_nil, List.append_nil] using hp.append hc

/-- The original hybrid weight factors into its seed and transition weights. -/
theorem graftRecordWeight_zero (pre : List ValuationWord) (w : ValuationWord) :
    Transfer.weight (graftRecordWord (pre, w, [])) = Transfer.weight pre.flatten * Transfer.weight w := by
  simp only [graftRecordWord, List.flatten_nil, List.append_nil, Transfer.weight_append]

/-- The actual zero-stage family is exactly the compatible parent/transition product. -/
theorem physicalGraftRecords_zero_eq (L δ : ℝ) (b t root : ℕ) :
    physicalGraftRecords L δ b t 0 root =
      (((physicalSeedHistories b t root).product (graftTransitionWords δ b t)).filter
        (fun p => ∃ source, PhysicalHistory p.2 (seedHistorySource root p.1) source)).image
          (fun p => (p.1, p.2, [])) := by
  ext r
  rcases r with ⟨pre, w, ws⟩
  constructor
  · intro hr
    have hform := (mem_physicalGraftRecords L δ b t 0 root _).mp hr |>.1
    have hlen : ws.length = 0 := ((mem_graftRecords L δ b t 0 _).mp hform).2.2.2.1
    have he : ws = [] := List.length_eq_zero_iff.mp hlen
    subst ws
    obtain ⟨hp, hw, hc⟩ := (mem_physicalGraftRecords_zero L δ b t root pre w).mp hr
    exact Finset.mem_image.mpr ⟨(pre, w), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hp, hw⟩, hc⟩, rfl⟩
  · intro hr
    obtain ⟨⟨other, v⟩, hm, he⟩ := Finset.mem_image.mp hr
    obtain ⟨hprod, hc⟩ := Finset.mem_filter.mp hm
    obtain ⟨hp, hv⟩ := Finset.mem_product.mp hprod
    rw [← he]
    exact (mem_physicalGraftRecords_zero L δ b t root other v).mpr ⟨hp, hv, hc⟩

/-- Summation over actual transition histories retains each compatible parent/child pair once. -/
theorem physicalGraftRecords_sum_zero (L δ : ℝ) (b t root : ℕ) (F : GraftRecord → ℝ) :
    (∑ r ∈ physicalGraftRecords L δ b t 0 root, F r) =
      ∑ pre ∈ physicalSeedHistories b t root, ∑ w ∈ graftTransitionWords δ b t,
        if ∃ source, PhysicalHistory w (seedHistorySource root pre) source then
          F (pre, w, []) else 0 := by
  rw [physicalGraftRecords_zero_eq, Finset.sum_image]
  · rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  · intro p _ q _ he
    exact Prod.ext (congrArg (fun r : GraftRecord => r.1) he)
      (congrArg (fun r : GraftRecord => r.2.1) he)

/-- The initial hybrid mark is the original weighted sum over physical transition children. -/
theorem physicalGraftMark_zero (L δ : ℝ) (b t root : ℕ) :
    physicalGraftMark L δ b t 0 root =
      ∑ pre ∈ physicalSeedHistories b t root, Transfer.weight pre.flatten *
        ∑ w ∈ graftTransitionWords δ b t,
          if ∃ source, PhysicalHistory w (seedHistorySource root pre) source then
            Transfer.weight w * Reference.marker (macroLevel (graftInitialCount b t))
              (graftRecordSource root (pre, w, []) : ZMod (3 ^ macroLevel (graftInitialCount b t)))
          else 0 := by
  rw [physicalGraftMark, physicalGraftRecords_sum_zero]
  apply Finset.sum_congr rfl
  intro pre _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs
  · rw [graftRecordWeight_zero, mul_assoc]
    rfl
  · rw [mul_zero]

end WordCertDensity.Construction
