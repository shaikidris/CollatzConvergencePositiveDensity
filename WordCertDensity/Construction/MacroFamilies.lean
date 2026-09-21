/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.MacroHistories

/-! # Finite retained macro histories and their actual parsing

Enumeration advances the original count by each prescribed macro length.
At a fixed number of macro stages, prefix compatibility determines the entire
list of macro words, including all boundaries.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- The finite macro histories at the actual starting count and fixed stage count. -/
noncomputable def macroHistoryLists (L δ : ℝ) : ℕ → ℕ → Finset (List ValuationWord)
  | _, 0 => {[]}
  | B, j + 1 => ((macroblocks L δ B).product
      (macroHistoryLists L δ (B + macroLength L B) j)).image (fun p => p.1 :: p.2)

/-- Finite enumeration is exactly the retained macro predicate and the prescribed stage count. -/
theorem mem_macroHistoryLists (L δ : ℝ) (B j : ℕ) (ws : List ValuationWord) :
    ws ∈ macroHistoryLists L δ B j ↔ ws.length = j ∧ MacroHistory L δ B ws := by
  induction j generalizing B ws with
  | zero => cases ws <;> simp [macroHistoryLists, MacroHistory]
  | succ j ih =>
      cases ws with
      | nil => simp [macroHistoryLists]
      | cons w ws =>
          constructor
          · intro h
            obtain ⟨⟨v, vs⟩, hm, he⟩ := Finset.mem_image.mp h
            obtain ⟨rfl, rfl⟩ := List.cons.inj he
            obtain ⟨hv, hvs⟩ := Finset.mem_product.mp hm
            obtain ⟨hlen, hp⟩ := (ih _ vs).mp hvs
            exact ⟨by simpa using hlen, hv, hp⟩
          · rintro ⟨hlen, hw, hws⟩
            exact Finset.mem_image.mpr ⟨(w, ws), Finset.mem_product.mpr
              ⟨hw, (ih _ ws).mpr ⟨by simpa using hlen, hws⟩⟩, rfl⟩

/-- A prefix of equal-stage retained macro histories fixes every macro boundary. -/
theorem macroHistory_eq_of_prefix {L δ : ℝ} {B : ℕ} {ws vs : List ValuationWord}
    (hw : MacroHistory L δ B ws) (hv : MacroHistory L δ B vs)
    (hlen : ws.length = vs.length) (hp : ws.flatten <+: vs.flatten) : ws = vs := by
  induction ws generalizing B vs with
  | nil => cases vs <;> simp_all
  | cons w ws ih =>
      cases vs with
      | nil => simp at hlen
      | cons v vs =>
          have hpw : w <+: v ++ vs.flatten := (List.prefix_append w ws.flatten).trans hp
          have hpv : v <+: v ++ vs.flatten := List.prefix_append _ _
          have he : w = v := by
            rcases List.prefix_or_prefix_of_prefix hpw hpv with h | h
            · by_contra hne
              exact macroblocks_prefixFree L δ B hw.1 hv.1 hne h
            · by_contra hne
              exact macroblocks_prefixFree L δ B hv.1 hw.1 (fun he => hne he.symm) h
          subst v
          have ht : ws.flatten <+: vs.flatten := (List.prefix_append_right_inj w).mp hp
          exact congrArg (List.cons w) (ih hw.2 hv.2 (by simpa using hlen) ht)

/-- At a fixed stage count, the full word determines the retained macro list. -/
theorem macroHistory_flatten_injective {L δ : ℝ} {B : ℕ} {ws vs : List ValuationWord}
    (hw : MacroHistory L δ B ws) (hv : MacroHistory L δ B vs)
    (hlen : ws.length = vs.length) (he : ws.flatten = vs.flatten) : ws = vs :=
  macroHistory_eq_of_prefix hw hv hlen (by rw [he])

/-- The finite macro-word family before adjoining a seed and transition. -/
noncomputable def macroHistoryWords (L δ : ℝ) (B j : ℕ) : Finset ValuationWord :=
  (macroHistoryLists L δ B j).image List.flatten

/-- Macro-word membership retains the actual list witnesses and current-count schedule. -/
theorem mem_macroHistoryWords (L δ : ℝ) (B j : ℕ) (w : ValuationWord) :
    w ∈ macroHistoryWords L δ B j ↔ ∃ ws : List ValuationWord,
      ws.length = j ∧ MacroHistory L δ B ws ∧ ws.flatten = w := by
  simp only [macroHistoryWords, Finset.mem_image, mem_macroHistoryLists, and_assoc]

/-- The complete fixed-stage macro-word family is prefix-free. -/
theorem macroHistoryWords_prefixFree (L δ : ℝ) (B j : ℕ) :
    (macroHistoryWords L δ B j : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v) := by
  intro u hu v hv hne hp
  obtain ⟨ws, hwl, hwp, rfl⟩ := (mem_macroHistoryWords L δ B j u).mp hu
  obtain ⟨vs, hvl, hvp, rfl⟩ := (mem_macroHistoryWords L δ B j v).mp hv
  exact hne (congrArg List.flatten (macroHistory_eq_of_prefix hwp hvp (hwl.trans hvl.symm) hp))

end WordCertDensity.Construction
