/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PostPassageWhiteBound
public import WordCertDensity.Analytic.LocalPrimitive.WordEntryPrefix
import Mathlib.Tactic

/-! # Removing unused future samples from the post-passage estimate -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

/-- The white-state count only sees the observed pair window. -/
theorem sampledWhiteStateCount_prefix_congr (n : ℕ) (ξ : ZMod (3 ^ n))
    (j : ℕ) (l : ℤ) {u v : ValuationWord} {P : ℕ}
    (hu : 2 * P ≤ u.length) (hv : 2 * P ≤ v.length)
    (he : u.take (2 * P) = v.take (2 * P)) :
    sampledWhiteStateCount n ξ j l u P = sampledWhiteStateCount n ξ j l v P := by
  unfold sampledWhiteStateCount
  congr 1
  apply Finset.filter_congr
  intro p hp
  have hpP := (Finset.mem_range.mp hp).le
  rw [entryWordHeight_prefix_congr l (by omega) (by omega)
    (word_take_pair_prefix he hpP)]

/-- Truncation after the complete post-passage window preserves shortage. -/
theorem postPassageShortageEvent_take_iff (n : ℕ) (ξ : ZMod (3 ^ n))
    (s j : ℕ) (l : ℤ) (B L : ℕ)
    (hL : s / 2 + 1 + localPrimitiveP B ≤ L) (w : ValuationWord)
    (hw : 2 * L ≤ w.length) :
    postPassageShortageEvent n ξ s j l B (w.take (2 * L)) ↔
      postPassageShortageEvent n ξ s j l B w := by
  unfold postPassageShortageEvent
  apply exists_congr
  intro i
  have hi := i.isLt
  have htlen : (w.take (2 * L)).length = 2 * L := List.length_take_of_le hw
  have hpass := horizonTailEvent_prefix_iff (s := s) (H := 0) (i := (i : ℕ))
    (List.take_prefix (2 * L) w) (by omega)
  have hq : 2 * ((i : ℕ) + 1) ≤ 2 * L := by omega
  rw [hpass, List.take_take, Nat.min_eq_left hq]
  have hc := sampledWhiteStateCount_prefix_congr n ξ (j + ((i : ℕ) + 1))
    (l + ValuationWord.total (w.take (2 * ((i : ℕ) + 1))))
    (u := (w.take (2 * L)).drop (2 * ((i : ℕ) + 1)))
    (v := w.drop (2 * ((i : ℕ) + 1))) (P := localPrimitiveP B)
    (by rw [List.length_drop, htlen]; omega)
    (by rw [List.length_drop]; omega)
    (by rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)])
  rw [hc]

/-- The shortage probability is invariant under unused future sampling. -/
theorem postPassageShortage_probability_extend (n : ℕ) (ξ : ZMod (3 ^ n))
    (s j : ℕ) (l : ℤ) (B L L' : ℕ)
    (hL : s / 2 + 1 + localPrimitiveP B ≤ L) (hLL' : L ≤ L') :
    Gated.probability (Reference.wordPMF (2 * L'))
      (postPassageShortageEvent n ξ s j l B) =
    Gated.probability (Reference.wordPMF (2 * L))
      (postPassageShortageEvent n ξ s j l B) := by
  have hmap := Gated.probability_map (Reference.wordPMF (2 * L'))
    (fun w => w.take (2 * L)) (postPassageShortageEvent n ξ s j l B)
  rw [Reference.wordPMF_map_take_of_le (show 2 * L ≤ 2 * L' by omega)] at hmap
  rw [hmap]
  apply Gated.probability_congr_on_support
  intro w hw
  have hlen : w.length = 2 * L' := by
    by_contra hne
    exact hw (Reference.wordPMF_eq_zero_of_length_ne (2 * L') w hne)
  exact (postPassageShortageEvent_take_iff n ξ s j l B L hL w (by omega)).symm

/-- The white-shortage bound uses exactly the original first-passage plus
P-window horizon; additional samples used in its proof are removed. -/
theorem postPassage_white_shortage_probability_lt_window {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (a j : ℕ) (top l : ℤ) (B L : ℕ)
    (hadm : longCrossingAdmissible n ξ a j top l B (localPrimitiveA B)
      (localPrimitiveH B) (localPrimitiveP B) (localPrimitiveZ B))
    (hL : (top - l).toNat / 2 + 1 + localPrimitiveP B ≤ L) :
    Gated.probability (Reference.wordPMF (2 * L))
      (postPassageShortageEvent n ξ (top - l).toNat j l B) <
        2 / (localPrimitiveDeltaDenom B : ℝ) := by
  have h := postPassage_white_shortage_probability_lt hn ξ hξ a j top l B
    (L + (8 * n + 8)) hadm (by omega)
  rw [postPassageShortage_probability_extend n ξ (top - l).toNat j l B L
    (L + (8 * n + 8)) hL (by omega)] at h
  exact h

end WordCertDensity.LocalPrimitive
