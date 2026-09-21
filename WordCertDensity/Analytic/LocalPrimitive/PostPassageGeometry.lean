/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryDurationRecipe
public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingLaw
import Mathlib.Tactic

/-! # Literal post-passage entry states in the large-union event -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The suffix walk and E-L4's original-word position have the same height. -/
theorem postPassage_height_eq (l : ℤ) (w : ValuationWord) (q p : ℕ)
    (hsample : 2 * (q + p) ≤ w.length) :
    entryWordHeight (l + ValuationWord.total (w.take (2 * q))) (w.drop (2 * q)) p =
      l + ValuationWord.total (w.take (2 * (q + p))) := by
  rw [entryWordHeight_of_sampled _ _ p (by rw [List.length_drop]; omega)]
  rw [Nat.mul_add, List.take_add, ValuationWord.total_append, Nat.cast_add]
  omega

/-- Outside the simultaneous large-triangle event, every actual selected
triangle entered by the post-passage suffix is smaller than its threshold. -/
theorem postPassage_selected_triangle_small {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (s j : ℕ) (l : ℤ) (H P : ℕ) (w : ValuationWord) (i : Fin (s / 2 + 1))
    (hpass : horizonTailEvent s 0 i w)
    (hsample : 2 * ((i : ℕ) + 1 + P) ≤ w.length)
    (hnot : ¬ longCrossingLargeUnionEvent n ξ s j l H P w)
    (p : ℕ) (hp : p < P)
    (hb : entryWordBlack n ξ (j + ((i : ℕ) + 1))
      (l + ValuationWord.total (w.take (2 * ((i : ℕ) + 1))))
      (w.drop (2 * ((i : ℕ) + 1))) p) :
    phaseTriangleLogSize n
      (entryWordTriangle hn ξ hξ (j + ((i : ℕ) + 1))
        (l + ValuationWord.total (w.take (2 * ((i : ℕ) + 1))))
        (w.drop (2 * ((i : ℕ) + 1))) p).1
      (entryWordTriangle hn ξ hξ (j + ((i : ℕ) + 1))
        (l + ValuationWord.total (w.take (2 * ((i : ℕ) + 1))))
        (w.drop (2 * ((i : ℕ) + 1))) p).2 ξ < (H * (p + 1) ^ 4 : ℕ) := by
  obtain ⟨hsel, hpoint⟩ := entryWordTriangle_spec hn ξ hξ _ _ _ p hb
  by_contra hlarge
  apply hnot
  refine ⟨p, Finset.mem_range.mpr hp, i, hpass, ?_⟩
  refine ⟨_, _, ?_, hsel, le_of_not_gt hlarge, ?_⟩
  · have := hpoint.1
    have := hb.2.1
    omega
  · have hh := postPassage_height_eq l w ((i : ℕ) + 1) p (by omega)
    simpa only [longCrossingPosition, hh] using hpoint

/-- A post-passage white shortage outside E-L4's exceptional union forces
the prescribed entry in the literal suffix of the original word. -/
theorem postPassage_entry_of_shortage {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (s j : ℕ) (l : ℤ) (B : ℕ) (w : ValuationWord) (i : Fin (s / 2 + 1))
    (hpass : horizonTailEvent s 0 i w)
    (hsample : 2 * ((i : ℕ) + 1 + localPrimitiveP B) ≤ w.length)
    (hnot : ¬ longCrossingLargeUnionEvent n ξ s j l
      (localPrimitiveH B) (localPrimitiveP B) w)
    (hshort : sampledWhiteStateCount n ξ (j + ((i : ℕ) + 1))
      (l + ValuationWord.total (w.take (2 * ((i : ℕ) + 1))))
      (w.drop (2 * ((i : ℕ) + 1))) (localPrimitiveP B) < localPrimitiveK B) :
    ∃ t, t < localPrimitiveP B ∧
      wordBlackEntryTime hn ξ hξ (j + ((i : ℕ) + 1))
        (l + ValuationWord.total (w.take (2 * ((i : ℕ) + 1))))
        (w.drop (2 * ((i : ℕ) + 1))) (localPrimitiveR B - 1) = some t := by
  apply recipe_entry_of_shortage_small_triangles hn ξ hξ _ _ _ B
    (by rw [List.length_drop]; omega) hshort
  intro p hp hb
  exact postPassage_selected_triangle_small hn ξ hξ s j l
    (localPrimitiveH B) (localPrimitiveP B) w i hpass hsample hnot p hp hb

end WordCertDensity.LocalPrimitive
