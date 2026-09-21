/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftMark

/-! # Exact final-macro decomposition of physical hybrid records

The last macro word is appended at the actual count reached by its parent.
The seed and transition components remain fixed. Physical splitting identifies
the intermediate endpoint with the parent's prescribed source function.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- Append one macro word, preserving the seed and exceptional transition components. -/
def graftRecordSnoc (r : GraftRecord) (w : ValuationWord) : GraftRecord :=
  (r.1, r.2.1, r.2.2 ++ [w])

/-- The complete word extends by exactly the final macro word. -/
theorem graftRecordWord_snoc (r : GraftRecord) (w : ValuationWord) :
    graftRecordWord (graftRecordSnoc r w) = graftRecordWord r ++ w := by
  simp only [graftRecordSnoc, graftRecordWord, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.append_assoc]

/-- The next formal family uses the actual parent count as its last macro start. -/
theorem mem_graftRecords_snoc (L δ : ℝ) (b t j : ℕ) (r : GraftRecord) (w : ValuationWord) :
    graftRecordSnoc r w ∈ graftRecords L δ b t (j + 1) ↔
      r ∈ graftRecords L δ b t j ∧ w ∈ macroblocks L δ (macroCount L (graftInitialCount b t) j) := by
  simp only [mem_graftRecords, graftRecordSnoc, List.length_append, List.length_singleton,
    Nat.add_left_inj, macroHistory_append, MacroHistory, and_true]
  constructor
  · rintro ⟨hlen, hp, ht, hm, hs, hw⟩
    exact ⟨⟨hlen, hp, ht, hm, hs⟩, by simpa only [hm] using hw⟩
  · rintro ⟨⟨hlen, hp, ht, hm, hs⟩, hw⟩
    exact ⟨hlen, hp, ht, hm, hs, by simpa only [hm] using hw⟩

/-- Appending a final macro word loses neither its parent record nor its identity. -/
theorem graftRecordSnoc_injective :
    Function.Injective (fun p : GraftRecord × ValuationWord => graftRecordSnoc p.1 p.2) := by
  rintro ⟨r, w⟩ ⟨s, v⟩ he
  have hpre := congrArg (fun x : GraftRecord => x.1) he
  have htr := congrArg (fun x : GraftRecord => x.2.1) he
  change r.1 = s.1 at hpre
  change r.2.1 = s.2.1 at htr
  have hmacro : r.2.2 ++ [w] = s.2.2 ++ [v] :=
    congrArg (fun x : GraftRecord => x.2.2) he
  obtain ⟨hm, hw⟩ := List.append_inj' hmacro (by simp)
  exact Prod.ext (Prod.ext hpre (Prod.ext htr hm)) (List.singleton_inj.mp hw)

/-- A next-stage physical record is precisely an actual parent and a physical final child. -/
theorem mem_physicalGraftRecords_snoc (L δ : ℝ) (b t j root : ℕ)
    (r : GraftRecord) (w : ValuationWord) :
    graftRecordSnoc r w ∈ physicalGraftRecords L δ b t (j + 1) root ↔
      r ∈ physicalGraftRecords L δ b t j root ∧
        w ∈ macroblocks L δ (macroCount L (graftInitialCount b t) j) ∧
          ∃ source, PhysicalHistory w (graftRecordSource root r) source := by
  constructor
  · intro hr
    obtain ⟨hf, hp⟩ := (mem_physicalGraftRecords L δ b t (j + 1) root _).mp hr
    obtain ⟨hf, hw⟩ := (mem_graftRecords_snoc L δ b t j r w).mp hf
    rw [graftRecordWord_snoc] at hp
    obtain ⟨middle, hparent, hchild⟩ := hp.append_split
    have he := graftRecordSource_eq hparent
    exact ⟨(mem_physicalGraftRecords L δ b t j root r).mpr
      ⟨hf, by simpa only [he] using hparent⟩, hw, _, by simpa only [he] using hchild⟩
  · rintro ⟨hr, hw, source, hc⟩
    obtain ⟨hf, hp⟩ := (mem_physicalGraftRecords L δ b t j root r).mp hr
    have hfull : PhysicalHistory (graftRecordWord (graftRecordSnoc r w)) root source := by
      rw [graftRecordWord_snoc]
      exact hp.append hc
    exact (mem_physicalGraftRecords L δ b t (j + 1) root _).mpr
      ⟨(mem_graftRecords_snoc L δ b t j r w).mpr ⟨hf, hw⟩,
        by simpa only [graftRecordSource_eq hfull] using hfull⟩

/-- The endpoint of a physical final child is the prescribed extended-record source. -/
theorem graftRecordSource_snoc {root source : ℕ} {r : GraftRecord} {w : ValuationWord}
    (hp : PhysicalHistory (graftRecordWord r) root (graftRecordSource root r))
    (hc : PhysicalHistory w (graftRecordSource root r) source) :
    graftRecordSource root (graftRecordSnoc r w) = source := by
  apply graftRecordSource_eq
  rw [graftRecordWord_snoc]
  exact hp.append hc

/-- Original weights factor without renormalizing the retained children. -/
theorem graftRecordWeight_snoc (r : GraftRecord) (w : ValuationWord) :
    Transfer.weight (graftRecordWord (graftRecordSnoc r w)) =
      Transfer.weight (graftRecordWord r) * Transfer.weight w := by
  rw [graftRecordWord_snoc, Transfer.weight_append]

/-- The next physical family is exactly the filtered parent/macro product. -/
theorem physicalGraftRecords_snoc_eq (L δ : ℝ) (b t j root : ℕ) :
    physicalGraftRecords L δ b t (j + 1) root =
      (((physicalGraftRecords L δ b t j root).product
        (macroblocks L δ (macroCount L (graftInitialCount b t) j))).filter
          (fun p => ∃ source, PhysicalHistory p.2 (graftRecordSource root p.1) source)).image
            (fun p => graftRecordSnoc p.1 p.2) := by
  ext r
  constructor
  · intro hr
    rcases r with ⟨pre, v, ws⟩
    induction ws using List.reverseRecOn with
    | nil =>
        have hf := (mem_physicalGraftRecords L δ b t (j + 1) root _).mp hr |>.1
        have hl := (mem_graftRecords L δ b t (j + 1) _).mp hf |>.2.2.2.1
        simp at hl
    | append_singleton ws w _ =>
        obtain ⟨hp, hw, hc⟩ := (mem_physicalGraftRecords_snoc L δ b t j root (pre, v, ws) w).mp hr
        exact Finset.mem_image.mpr ⟨((pre, v, ws), w), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hp, hw⟩, hc⟩, rfl⟩
  · intro hr
    obtain ⟨⟨s, w⟩, hm, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hprod, hc⟩ := Finset.mem_filter.mp hm
    obtain ⟨hp, hw⟩ := Finset.mem_product.mp hprod
    exact (mem_physicalGraftRecords_snoc L δ b t j root s w).mpr ⟨hp, hw, hc⟩

/-- Summing the next stage counts each compatible physical parent/macro pair exactly once. -/
theorem physicalGraftRecords_sum_snoc (L δ : ℝ) (b t j root : ℕ) (F : GraftRecord → ℝ) :
    (∑ r ∈ physicalGraftRecords L δ b t (j + 1) root, F r) =
      ∑ r ∈ physicalGraftRecords L δ b t j root,
        ∑ w ∈ macroblocks L δ (macroCount L (graftInitialCount b t) j),
          if ∃ source, PhysicalHistory w (graftRecordSource root r) source then
            F (graftRecordSnoc r w) else 0 := by
  rw [physicalGraftRecords_snoc_eq, Finset.sum_image]
  · rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  · intro p _ q _ he
    exact graftRecordSnoc_injective he

/-- The next actual mark is the original weighted sum of its physical macro children. -/
theorem physicalGraftMark_snoc (L δ : ℝ) (b t j root : ℕ) :
    physicalGraftMark L δ b t (j + 1) root =
      ∑ r ∈ physicalGraftRecords L δ b t j root, Transfer.weight (graftRecordWord r) *
        ∑ w ∈ macroblocks L δ (macroCount L (graftInitialCount b t) j),
          if ∃ source, PhysicalHistory w (graftRecordSource root r) source then
            Transfer.weight w *
              Reference.marker (macroLevel (macroCount L (graftInitialCount b t) (j + 1)))
                (graftRecordSource root (graftRecordSnoc r w) :
                  ZMod (3 ^ macroLevel (macroCount L (graftInitialCount b t) (j + 1))))
          else 0 := by
  rw [physicalGraftMark, physicalGraftRecords_sum_snoc]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs
  · rw [graftRecordWeight_snoc, mul_assoc]
  · rw [mul_zero]

end WordCertDensity.Construction
