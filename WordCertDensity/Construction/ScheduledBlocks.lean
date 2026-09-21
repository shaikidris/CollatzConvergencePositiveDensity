/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.OffsetEnvelope
public import WordCertDensity.Construction.StoppedCopies
public import WordCertDensity.Words.ParsingPrefix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual scheduled concatenations

The starting index B counts original blocks already consumed. Finite lists
use precisions E_(B+1), E_(B+2), ...; flattening preserves unique cuts and
fixed-count prefix-freeness. Ordered affine composition retains the incoming
contraction when comparing offsets with the one global series.
-/

@[expose] public section

namespace WordCertDensity.Construction

open scoped Classical

/-- A stage B admits the next original block with precision E_(B+1). -/
noncomputable def continuationBlockRule : BlockRule :=
  stoppedBlockRule (fun B => continuationPrecision (B + 1))

/-- An actual list of stopped blocks at its original starting count. -/
def ScheduledBlocks (B : ℕ) (ws : List ValuationWord) : Prop :=
  continuationBlockRule.Parses B ws

/-- Scheduled lists have the exact next-block and current-count recursion. -/
theorem scheduledBlocks_cons (B : ℕ) (w : ValuationWord) (ws : List ValuationWord) :
    ScheduledBlocks B (w :: ws) ↔
      w ∈ stoppedWords (continuationPrecision (B + 1)) ∧ ScheduledBlocks (B + 1) ws :=
  Iff.rfl

/-- Joining histories uses the incoming list's actual length as the new stage. -/
theorem scheduledBlocks_append (B : ℕ) (ws vs : List ValuationWord) :
    ScheduledBlocks B (ws ++ vs) ↔
      ScheduledBlocks B ws ∧ ScheduledBlocks (B + ws.length) vs :=
  BlockRule.parses_append_iff _ _ _ _

/-- The finite list family retains each component and its prescribed precision. -/
noncomputable def scheduledBlockLists : ℕ → ℕ → Finset (List ValuationWord)
  | _, 0 => {[]}
  | B, n + 1 =>
      ((stoppedWords (continuationPrecision (B + 1))).product
        (scheduledBlockLists (B + 1) n)).image (fun p => p.1 :: p.2)

/-- Enumeration matches precisely the prescribed count and actual schedule. -/
theorem mem_scheduledBlockLists (B n : ℕ) (ws : List ValuationWord) :
    ws ∈ scheduledBlockLists B n ↔ ws.length = n ∧ ScheduledBlocks B ws := by
  induction n generalizing B ws with
  | zero => cases ws <;> simp [scheduledBlockLists, ScheduledBlocks]
  | succ n ih =>
      cases ws with
      | nil => simp [scheduledBlockLists]
      | cons w ws =>
          constructor
          · intro h
            obtain ⟨⟨v, vs⟩, hmem, he⟩ := Finset.mem_image.mp h
            have hv : v = w := (List.cons.inj he).1
            have hvs : vs = ws := (List.cons.inj he).2
            subst v
            subst vs
            obtain ⟨hw, hws⟩ := Finset.mem_product.mp hmem
            obtain ⟨hlen, hp⟩ := (ih (B + 1) ws).mp hws
            exact ⟨by simpa using hlen, (scheduledBlocks_cons B w ws).mpr ⟨hw, hp⟩⟩
          · rintro ⟨hlen, hp⟩
            obtain ⟨hw, hws⟩ := (scheduledBlocks_cons B w ws).mp hp
            exact Finset.mem_image.mpr ⟨(w, ws), Finset.mem_product.mpr
              ⟨hw, (ih (B + 1) ws).mpr ⟨by simpa using hlen, hws⟩⟩, rfl⟩

/-- The actual finite concatenation family, before any corridor restriction. -/
noncomputable def scheduledWords (B n : ℕ) : Finset ValuationWord :=
  (scheduledBlockLists B n).image List.flatten

/-- A concatenation has exactly the scheduled finite-list witnesses. -/
theorem mem_scheduledWords (B n : ℕ) (w : ValuationWord) :
    w ∈ scheduledWords B n ↔
      ∃ ws : List ValuationWord, ws.length = n ∧ ScheduledBlocks B ws ∧ ws.flatten = w := by
  simp only [scheduledWords, Finset.mem_image, mem_scheduledBlockLists]
  simp only [and_assoc]

/-- Prescribed-count concatenations form a prefix-free family at every starting count. -/
theorem scheduledWords_prefixFree (B n : ℕ) :
    (scheduledWords B n : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v) := by
  intro u hu v hv hne hp
  obtain ⟨us, hul, hup, rfl⟩ := (mem_scheduledWords B n u).mp hu
  obtain ⟨vs, hvl, hvp, rfl⟩ := (mem_scheduledWords B n v).mp hv
  exact hne (congrArg List.flatten
    (BlockRule.eq_of_flatten_prefix_of_length_eq hup hvp hp (hul.trans hvl.symm)))

/-- Every subset, including a corridor filter, retains prefix-freeness. -/
theorem scheduledWords_subset_prefixFree {B n : ℕ} {V : Finset ValuationWord}
    (hV : V ⊆ scheduledWords B n) :
    (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v) := by
  intro u hu v hv hne hp
  exact scheduledWords_prefixFree B n (hV hu) (hV hv) hne hp

/-- Concatenation adds exactly the component valuations. -/
theorem total_flatten (ws : List ValuationWord) :
    ValuationWord.total ws.flatten = (ws.map ValuationWord.total).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [ih]

/-- Concatenation preserves the actual summed ordinary cost used by the corridor. -/
theorem ordinaryCost_flatten (ws : List ValuationWord) :
    (ValuationWord.ordinaryCost ws.flatten : ℝ) = blockSum (fun w => (w.ordinaryCost : ℝ)) ws := by
  induction ws with
  | nil => simp [ValuationWord.ordinaryCost, ValuationWord.total]
  | cons w ws ih => simp [ih]

private theorem displacement_append (u v : ValuationWord) :
    displacement (u ++ v) = displacement u + displacement v := by
  simp only [displacement, ValuationWord.total_append, List.length_append, Nat.cast_add]
  ring

/-- Concatenation preserves the exact displacement sum used by the corridor. -/
theorem displacement_flatten (ws : List ValuationWord) :
    displacement ws.flatten = blockSum displacement ws := by
  induction ws with
  | nil => simp [displacement, ValuationWord.total]
  | cons w ws ih => simp only [List.flatten_cons, displacement_append, ih, blockSum_cons]

/-- Literal integer total/depth budget at the actual count. -/
noncomputable def scheduledDepthBudget (B n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, (continuationPrecision (B + j + 1) - 1)

private theorem scheduledDepthBudget_succ (B n : ℕ) :
    scheduledDepthBudget B (n + 1) =
      continuationPrecision (B + 1) - 1 + scheduledDepthBudget (B + 1) n := by
  simp [scheduledDepthBudget, Finset.sum_range_succ', Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm]

/-- Strict component total cutoffs add to the literal integer budget. -/
theorem scheduledBlocks_total_le {B : ℕ} {ws : List ValuationWord}
    (hp : ScheduledBlocks B ws) :
    ValuationWord.total ws.flatten ≤ scheduledDepthBudget B ws.length := by
  induction ws generalizing B with
  | nil => simp [ValuationWord.total, scheduledDepthBudget]
  | cons w ws ih =>
      obtain ⟨hw, hws⟩ := (scheduledBlocks_cons B w ws).mp hp
      have ht := (mem_stoppedWords w _).mp hw |>.2
      have hi := ih hws
      simp only [List.flatten_cons, ValuationWord.total_append, List.length_cons,
        scheduledDepthBudget_succ]
      omega

/-- Actual concatenation depth obeys the same prescribed precision budget. -/
theorem scheduledBlocks_depth_le {B : ℕ} {ws : List ValuationWord}
    (hp : ScheduledBlocks B ws) : ws.flatten.length ≤ scheduledDepthBudget B ws.length :=
  (word_length_le_total ws.flatten).trans (scheduledBlocks_total_le hp)

private theorem weight_append (u v : ValuationWord) :
    Transfer.weight (u ++ v) = Transfer.weight u * Transfer.weight v := by
  simp [Transfer.weight, ValuationWord.slope_append]

/-- Each original block pays one full factor of the fixed contraction. -/
theorem scheduledBlocks_weight_le {B : ℕ} {ws : List ValuationWord}
    (hp : ScheduledBlocks B ws) : Transfer.weight ws.flatten ≤ (1 / 8 : ℝ) ^ ws.length := by
  induction ws generalizing B with
  | nil => simp [Transfer.weight, ValuationWord.slope, ValuationWord.total]
  | cons w ws ih =>
      obtain ⟨hw, hws⟩ := (scheduledBlocks_cons B w ws).mp hp
      rw [List.flatten_cons, weight_append, List.length_cons, pow_succ]
      have h := mul_le_mul (stoppedWords_weight_le hw) (ih hws)
        (Transfer.weight_pos ws.flatten).le (by norm_num : (0 : ℝ) ≤ 1 / 8)
      simpa only [mul_comm] using h

/-- The literal finite portion of the global offset series paid by this continuation. -/
noncomputable def scheduledOffsetBudget (B n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, continuationOffsetTerm (B + j)

private theorem scheduledOffsetBudget_succ (B n : ℕ) :
    scheduledOffsetBudget B (n + 1) =
      continuationOffsetTerm B + scheduledOffsetBudget (B + 1) n := by
  simp [scheduledOffsetBudget, Finset.sum_range_succ', Nat.add_left_comm, add_comm]

/-- A finite tail portion lies below the same global offset envelope. -/
theorem scheduledOffsetBudget_le (B n : ℕ) : scheduledOffsetBudget B n ≤
    continuationOffsetBound := by
  have hs := (summable_nat_add_iff B).mpr summable_continuationOffsetTerm
  have hp := hs.sum_le_tsum (Finset.range n)
    (fun j _ => continuationOffsetTerm_nonneg (j + B))
  have he := summable_continuationOffsetTerm.sum_add_tsum_nat_add B
  have hn : 0 ≤ ∑ j ∈ Finset.range B, continuationOffsetTerm j :=
    Finset.sum_nonneg (fun j _ => continuationOffsetTerm_nonneg j)
  have hbudget : scheduledOffsetBudget B n ≤ ∑' j, continuationOffsetTerm (j + B) := by
    simpa only [scheduledOffsetBudget, Nat.add_comm] using hp
  change _ + _ = continuationOffsetBound at he
  linarith

/-- Incoming contraction is retained before comparing actual concatenation offsets. -/
theorem scheduledBlocks_scaled_offset_le {B : ℕ} {ws : List ValuationWord}
    (hp : ScheduledBlocks B ws) :
    (1 / 8 : ℝ) ^ B * (ValuationWord.offset ws.flatten : ℝ) ≤
      scheduledOffsetBudget B ws.length := by
  induction ws generalizing B with
  | nil => simp [ValuationWord.offset, scheduledOffsetBudget]
  | cons w ws ih =>
      obtain ⟨hw, hws⟩ := (scheduledBlocks_cons B w ws).mp hp
      have hfirst := mul_le_mul_of_nonneg_left (scheduledWord_offset_bounds (B + 1) hw).2
        (show (0 : ℝ) ≤ (1 / 8 : ℝ) ^ B by positivity)
      have hm := mul_le_mul_of_nonneg_right (stoppedWords_weight_le hw)
        (show 0 ≤ (ValuationWord.offset ws.flatten : ℝ) from
          Rat.cast_nonneg.mpr (ValuationWord.offset_nonneg _))
      have hscaled := mul_le_mul_of_nonneg_left hm
        (show (0 : ℝ) ≤ (1 / 8 : ℝ) ^ B by positivity)
      have hi := ih hws
      rw [pow_succ] at hi
      rw [List.flatten_cons, ValuationWord.offset_append, Rat.cast_add, Rat.cast_mul,
        List.length_cons, scheduledOffsetBudget_succ]
      change _ ≤ (1 / 8 : ℝ) ^ B *
        ((3 / 2 : ℝ) ^ (continuationPrecision (B + 1) - 1) - 1) + _
      change (1 / 8 : ℝ) ^ B *
        ((w.offset : ℝ) + Transfer.weight w * (ValuationWord.offset ws.flatten : ℝ)) ≤ _
      nlinarith

/-- A full history starting at original block one has one uniform offset bound. -/
theorem scheduledBlocks_offset_le {ws : List ValuationWord} (hp : ScheduledBlocks 0 ws) :
    (ValuationWord.offset ws.flatten : ℝ) ≤ continuationOffsetBound := by
  have h := (scheduledBlocks_scaled_offset_le hp).trans (scheduledOffsetBudget_le 0 ws.length)
  simpa using h

/-- A late continuation attaches to any incoming word that pays the original-count contraction. -/
theorem incoming_scheduled_offset_le (B : ℕ) (incoming : ValuationWord)
    {ws : List ValuationWord} (hp : ScheduledBlocks B ws)
    (hprefix : Transfer.weight incoming ≤ (1 / 8 : ℝ) ^ B) :
    (ValuationWord.offset (incoming ++ ws.flatten) : ℝ) ≤
      (incoming.offset : ℝ) + continuationOffsetBound := by
  have hm := mul_le_mul_of_nonneg_right hprefix
    (show 0 ≤ (ValuationWord.offset ws.flatten : ℝ) from
      Rat.cast_nonneg.mpr (ValuationWord.offset_nonneg _))
  have hs := (scheduledBlocks_scaled_offset_le hp).trans
    (scheduledOffsetBudget_le B ws.length)
  rw [ValuationWord.offset_append, Rat.cast_add, Rat.cast_mul]
  change (incoming.offset : ℝ) +
    Transfer.weight incoming * (ValuationWord.offset ws.flatten : ℝ) ≤ _
  linarith

end WordCertDensity.Construction
