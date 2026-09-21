/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.SeedPhysical
public import WordCertDensity.Transfer.Composition
import Mathlib.Data.List.Induction

/-! # Exact final-block decomposition of physical seed histories -/

@[expose] public section

namespace WordCertDensity.Construction

open scoped Classical

/-- Appending seed blocks advances the schedule by the actual parent block count. -/
theorem seedBlocks_append (b t : ℕ) (ws vs : List ValuationWord) :
    SeedBlocks b t (ws ++ vs) ↔ SeedBlocks b t ws ∧ SeedBlocks b (t + ws.length) vs := by
  induction ws generalizing t with
  | nil => simp [SeedBlocks]
  | cons w ws ih => simp [SeedBlocks, ih, Nat.add_comm, Nat.add_left_comm, and_assoc]

/-- A final seed block uses precisely the next stage of the incoming history. -/
theorem mem_seedBlockLists_snoc (b t n : ℕ) (ws : List ValuationWord) (w : ValuationWord) :
    ws ++ [w] ∈ seedBlockLists b t (n + 1) ↔
      ws ∈ seedBlockLists b t n ∧ w ∈ seedWords (seedSize b (t + n)) := by
  simp only [mem_seedBlockLists, List.length_append, List.length_singleton,
    Nat.add_left_inj, seedBlocks_append, SeedBlocks, and_true]
  constructor
  · rintro ⟨hlen, hs, hw⟩
    exact ⟨⟨hlen, hs⟩, by simpa only [hlen] using hw⟩
  · rintro ⟨⟨hlen, hs⟩, hw⟩
    exact ⟨hlen, hs, by simpa only [hlen] using hw⟩

/-- A physical final block begins at the exact source of the parent history. -/
theorem mem_physicalSeedHistories_snoc (b n root : ℕ)
    (ws : List ValuationWord) (w : ValuationWord) :
    ws ++ [w] ∈ physicalSeedHistories b (n + 1) root ↔
      ws ∈ physicalSeedHistories b n root ∧ w ∈ seedWords (seedSize b n) ∧
        ∃ source, PhysicalHistory w (seedHistorySource root ws) source := by
  constructor
  · intro h
    obtain ⟨hs, hp⟩ := (mem_physicalSeedHistories b (n + 1) root _).mp h
    obtain ⟨hw, hv⟩ := (mem_seedBlockLists_snoc b 0 n ws w).mp hs
    have hp' : PhysicalHistory (ws.flatten ++ w) root
        (seedHistorySource root (ws ++ [w])) := by simpa only [List.flatten_append, List.flatten_cons,
          List.flatten_nil, List.append_nil] using hp
    obtain ⟨middle, hparent, hchild⟩ := hp'.append_split
    have he := seedHistorySource_eq hparent
    refine ⟨(mem_physicalSeedHistories b n root ws).mpr ⟨hw, ?_⟩, by simpa using hv, ?_⟩
    · simpa only [he] using hparent
    · exact ⟨_, by simpa only [he] using hchild⟩
  · rintro ⟨hs, hw, source, hp⟩
    obtain ⟨hblocks, hparent⟩ := (mem_physicalSeedHistories b n root ws).mp hs
    have hfull : PhysicalHistory (ws ++ [w]).flatten root source := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
        using hparent.append hp
    apply (mem_physicalSeedHistories b (n + 1) root _).mpr
    exact ⟨(mem_seedBlockLists_snoc b 0 n ws w).mpr ⟨hblocks, by simpa using hw⟩,
      by simpa only [seedHistorySource_eq hfull] using hfull⟩

/-- The final source is the child's exact source, with the parent source as its root. -/
theorem seedHistorySource_snoc {root source : ℕ} {ws : List ValuationWord} {w : ValuationWord}
    (hparent : PhysicalHistory ws.flatten root (seedHistorySource root ws))
    (hchild : PhysicalHistory w (seedHistorySource root ws) source) :
    seedHistorySource root (ws ++ [w]) = source := by
  apply seedHistorySource_eq
  simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
    using hparent.append hchild

/-- Final-block decomposition preserves the original, unnormalized slope weight. -/
theorem seedHistory_weight_snoc (ws : List ValuationWord) (w : ValuationWord) :
    Transfer.weight (ws ++ [w]).flatten = Transfer.weight ws.flatten * Transfer.weight w := by
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    Transfer.weight_append]

/-- Every nonempty physical seed history has exactly one parent and final block. -/
theorem physicalSeedHistories_decompose {b n root : ℕ} {vs : List ValuationWord}
    (hv : vs ∈ physicalSeedHistories b (n + 1) root) :
    ∃! p : List ValuationWord × ValuationWord,
      p.1 ∈ physicalSeedHistories b n root ∧ p.2 ∈ seedWords (seedSize b n) ∧
        (∃ source, PhysicalHistory p.2 (seedHistorySource root p.1) source) ∧
          p.1 ++ [p.2] = vs := by
  induction vs using List.reverseRecOn with
  | nil =>
    have hl := ((mem_seedBlockLists b 0 (n + 1) []).mp
      ((mem_physicalSeedHistories b (n + 1) root []).mp hv).1).1
    simp at hl
  | append_singleton ws w _ =>
    obtain ⟨hp, hw, hc⟩ := (mem_physicalSeedHistories_snoc b n root ws w).mp hv
    refine ⟨(ws, w), ⟨hp, hw, hc, rfl⟩, ?_⟩
    rintro ⟨us, u⟩ ⟨_, _, _, he⟩
    obtain ⟨hu, hv⟩ := List.append_inj' he (by simp)
    exact Prod.ext hu (List.singleton_inj.mp hv)

/-- The next physical family is exactly the compatible parent/block product. -/
theorem physicalSeedHistories_snoc_eq (b n root : ℕ) :
    physicalSeedHistories b (n + 1) root =
      (((physicalSeedHistories b n root).product (seedWords (seedSize b n))).filter
        (fun p : List ValuationWord × ValuationWord => ∃ source, PhysicalHistory p.2 (seedHistorySource root p.1) source)).image
          (fun p => p.1 ++ [p.2]) := by
  classical
  ext vs
  constructor
  · intro hv
    obtain ⟨⟨ws, w⟩, ⟨hp, hw, hc, he⟩, _⟩ := physicalSeedHistories_decompose hv
    exact Finset.mem_image.mpr ⟨(ws, w), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hp, hw⟩, hc⟩, he⟩
  · intro hv
    obtain ⟨⟨ws, w⟩, hm, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hm, hc⟩ := Finset.mem_filter.mp hm
    obtain ⟨hp, hw⟩ := Finset.mem_product.mp hm
    exact (mem_physicalSeedHistories_snoc b n root ws w).mpr ⟨hp, hw, hc⟩

/-- Summation over next histories keeps every compatible child exactly once. -/
theorem physicalSeedHistories_sum_snoc (b n root : ℕ) (F : List ValuationWord → ℝ) :
    (∑ vs ∈ physicalSeedHistories b (n + 1) root, F vs) =
      ∑ ws ∈ physicalSeedHistories b n root, ∑ w ∈ seedWords (seedSize b n),
        if ∃ source, PhysicalHistory w (seedHistorySource root ws) source then
          F (ws ++ [w]) else 0 := by
  classical
  rw [physicalSeedHistories_snoc_eq, Finset.sum_image]
  · rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  · intro p _ q _ he
    obtain ⟨hp, hq⟩ := List.append_inj' he (by simp)
    exact Prod.ext hp (List.singleton_inj.mp hq)

/-- The next physical mark is the original weighted sum over parent/child continuations. -/
theorem physicalSeedMark_snoc (b n root : ℕ) :
    physicalSeedMark b (n + 1) root =
      ∑ ws ∈ physicalSeedHistories b n root, Transfer.weight ws.flatten *
        ∑ w ∈ seedWords (seedSize b n),
          if ∃ source, PhysicalHistory w (seedHistorySource root ws) source then
            Transfer.weight w * Reference.marker (seedTailDepth b (n + 1))
              (seedHistorySource root (ws ++ [w]) : ZMod (3 ^ seedTailDepth b (n + 1)))
          else 0 := by
  classical
  rw [physicalSeedMark, physicalSeedHistories_sum_snoc]
  apply Finset.sum_congr rfl
  intro ws _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs
  · rw [seedHistory_weight_snoc, mul_assoc]
  · rw [mul_zero]

end WordCertDensity.Construction
