/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.Stopping
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Countable prefix stopping mass

Appendix E.6 uses first-entry families whose valuation words are not finite:
even at a fixed pair time, the positive valuations are unbounded.  This module
therefore keeps their mass as a `tsum` over a prefix set. Prefix-dependent
tail events are decomposed here; `LocalPrimitive.StoppedTail` supplies their
original-law factorization.
-/

@[expose] public section

namespace WordCertDensity.Reference

open scoped Classical ENNReal

/-- Disjoint events may be summed over an arbitrary index type in the
extended nonnegative source mass, without a finite-family restriction. -/
theorem stoppingEventMass_union {α ι : Type*} (p : PMF α)
    (G : ι → α → Prop)
    (hunique : ∀ i j a, G i a → G j a → i = j) :
    (∑' a, if ∃ i, G i a then p a else 0) =
      ∑' i, ∑' a, if G i a then p a else 0 := by
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  by_cases hex : ∃ i, G i a
  · obtain ⟨i, hi⟩ := hex
    rw [if_pos ⟨i, hi⟩, tsum_eq_single i]
    · simp [hi]
    · intro j hji
      have hj : ¬ G j a := fun hj => hji (hunique j i a hj hi)
      simp [hj]
  · have hnone : ∀ i, ¬ G i a := by simpa using hex
    simp [hnone]

/-- Geometric source mass of an arbitrary, hence countably indexed, family of
positive valuation-word prefixes.  The extended-nonnegative codomain avoids
silently assigning a real `tsum` value before summability is established. -/
noncomputable def countableStoppingMass (S : Set ValuationWord) : ℝ≥0∞ :=
  ∑' u : S, (1 / 2 : ℝ≥0∞) ^ (u : ValuationWord).total

/-- A real stopping mass is available only after its extended mass is known
finite; consumers should retain that witness rather than assume summability. -/
noncomputable def countableStoppingMassReal (S : Set ValuationWord) : ℝ :=
  (countableStoppingMass S).toReal

/-- Every countable stopping mass is nonnegative in its native mass codomain. -/
theorem countableStoppingMass_nonneg (S : Set ValuationWord) :
    0 ≤ countableStoppingMass S := bot_le

/-- A prescribed prefix has its geometric mass in the native ENNReal
codomain of the original word law. -/
theorem prefix_eventMass (u : ValuationWord) {N : ℕ} (hu : u.length ≤ N) :
    (∑' w : ValuationWord, if u <+: w then wordPMF N w else 0) =
      (1 / 2 : ℝ≥0∞) ^ u.total := by
  classical
  have hne : (∑' w : ValuationWord, if u <+: w then wordPMF N w else 0) ≠ ⊤ := by
    exact ne_of_lt ((ENNReal.tsum_le_tsum (fun w =>
      show (if u <+: w then wordPMF N w else 0) ≤ wordPMF N w by
        split_ifs <;> simp)).trans_lt (by rw [PMF.tsum_coe]; simp))
  apply (ENNReal.toReal_eq_toReal_iff' hne (by finiteness)).mp
  have hp := prefix_probability u hu
  simp only [Gated.probability] at hp
  have he : (∑' w : ValuationWord, if u <+: w then wordPMF N w else 0) =
      (∑' w : ValuationWord, @ite ℝ≥0∞ (u <+: w)
        (Classical.propDecidable _) (wordPMF N w) 0) := by
    apply tsum_congr
    intro w
    by_cases hw : u <+: w <;> simp [hw]
  rw [he, hp]
  simp [ENNReal.toReal_pow]

/-- A bounded countable prefix-free family has exactly its geometric source
mass as selection probability, with no truncation of valuation letters. -/
theorem countableStoppingMass_eq_event (S : Set ValuationWord) (N : ℕ)
    (hlen : ∀ u ∈ S, u.length ≤ N)
    (hfree : S.Pairwise (fun u v => ¬ u <+: v)) :
    countableStoppingMass S =
      ∑' w : ValuationWord, if ∃ u ∈ S, u <+: w then wordPMF N w else 0 := by
  have hunique : ∀ i j : S, ∀ w : ValuationWord,
      (i : ValuationWord) <+: w → (j : ValuationWord) <+: w → i = j := by
    intro i j w hi hj
    apply Subtype.ext
    by_contra hne
    rcases List.prefix_or_prefix_of_prefix hi hj with h | h
    · exact hfree i.property j.property hne h
    · exact hfree j.property i.property (Ne.symm hne) h
  have h := stoppingEventMass_union (wordPMF N)
    (fun i : S => fun w => (i : ValuationWord) <+: w) hunique
  calc
    countableStoppingMass S = ∑' i : S, ∑' w : ValuationWord,
        if (i : ValuationWord) <+: w then wordPMF N w else 0 := by
      apply tsum_congr
      intro i
      exact (prefix_eventMass i (hlen i i.property)).symm
    _ = _ := by
      trans ∑' i : S, ∑' w : ValuationWord,
        @ite ℝ≥0∞ ((i : ValuationWord) <+: w)
          (Classical.propDecidable _) (wordPMF N w) 0
      · apply tsum_congr
        intro i
        apply tsum_congr
        intro w
        by_cases hi : (i : ValuationWord) <+: w <;> simp [hi]
      · simpa using h.symm

/-- Prefix-freeness and a common finite horizon ensure countable mass is
finite before any conversion to real probability. -/
theorem countableStoppingMass_ne_top (S : Set ValuationWord) (N : ℕ)
    (hlen : ∀ u ∈ S, u.length ≤ N)
    (hfree : S.Pairwise (fun u v => ¬ u <+: v)) :
    countableStoppingMass S ≠ ⊤ := by
  rw [countableStoppingMass_eq_event S N hlen hfree]
  exact Gated.event_ne_top _ _

/-- Prefixes of a countable stopping family that can occur before a fixed
word horizon. -/
def boundedStoppingPrefix (S : Set ValuationWord) (N : ℕ) :=
  {u : ValuationWord // u ∈ S ∧ u.length ≤ N}

/-- The dependent tail type after a bounded stopping prefix. -/
def boundedStoppingTail {S : Set ValuationWord} {N : ℕ}
    (u : boundedStoppingPrefix S N) :=
  {v : ValuationWord // v.length = N - u.1.length}

/-- Rejoining a bounded stopping prefix with its dependent tail. -/
def boundedStoppingJoin {S : Set ValuationWord} {N : ℕ}
    (u : boundedStoppingPrefix S N) (v : boundedStoppingTail u) : ValuationWord :=
  u.1 ++ v.1

/-- The joined word has exactly the prescribed common horizon. -/
theorem boundedStoppingJoin_length {S : Set ValuationWord} {N : ℕ}
    (u : boundedStoppingPrefix S N) (v : boundedStoppingTail u) :
    (boundedStoppingJoin u v).length = N := by
  unfold boundedStoppingJoin
  rw [List.length_append, v.2]
  simpa [Nat.add_comm] using Nat.sub_add_cancel u.2.2

/-- Splitting a common-horizon word at a known bounded prefix produces the
dependent tail used by the countable sigma decomposition. -/
def boundedStoppingSplit {S : Set ValuationWord} {N : ℕ}
    (u : boundedStoppingPrefix S N) (w : ValuationWord)
    (hlen : w.length = N) : boundedStoppingTail u :=
  ⟨w.drop u.1.length, by rw [List.length_drop, hlen]⟩

/-- Split and join recover the original word exactly. -/
theorem boundedStoppingJoin_split {S : Set ValuationWord} {N : ℕ}
    (u : boundedStoppingPrefix S N) (w : ValuationWord)
    (hprefix : u.1 <+: w) (hlen : w.length = N) :
    boundedStoppingJoin u (boundedStoppingSplit u w hlen) = w := by
  change u.1 ++ w.drop u.1.length = w
  have hle : u.1.length ≤ w.length := by
    rw [List.prefix_iff_eq_take.mp hprefix]
    rw [List.length_take]
    exact min_le_right _ _
  rw [List.prefix_iff_eq_take.mp hprefix, List.length_take_of_le hle]
  exact List.take_append_drop u.1.length w

/-- Disjoint countable stopping prefixes decompose arbitrary post-stop tail
events on the original word law.  Tail events may depend on the selected
prefix; no independence or finite-family hypothesis is assumed here. -/
theorem countableStopping_tail_event_decomposition
    (S : Set ValuationWord) (N : ℕ) (B : ValuationWord → ValuationWord → Prop)
    (hfree : S.Pairwise (fun u v => ¬ u <+: v)) :
    (∑' w : ValuationWord,
      if ∃ u : S, (u : ValuationWord) <+: w ∧ B u (w.drop (u : ValuationWord).length)
      then wordPMF N w else 0) =
    ∑' u : S, ∑' w : ValuationWord,
      if (u : ValuationWord) <+: w ∧ B u (w.drop (u : ValuationWord).length)
      then wordPMF N w else 0 := by
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro w
  by_cases hex : ∃ u : S, (u : ValuationWord) <+: w ∧
      B u (w.drop (u : ValuationWord).length)
  · obtain ⟨i, hi⟩ := hex
    rw [if_pos ⟨i, hi⟩, tsum_eq_single i]
    · simp [hi]
    · intro j hji
      have hj : ¬ ((j : ValuationWord) <+: w ∧
          B j (w.drop (j : ValuationWord).length)) := by
        intro hj
        have hne : (j : ValuationWord) ≠ i := fun h => hji (Subtype.ext h)
        rcases List.prefix_or_prefix_of_prefix hj.1 hi.1 with h | h
        · exact hfree j.property i.property hne h
        · exact hfree i.property j.property (Ne.symm hne) h
      simp [hj]
  · have hn : ∀ u : S, ¬ ((u : ValuationWord) <+: w ∧
        B u (w.drop (u : ValuationWord).length)) := fun u hu => hex ⟨u, hu⟩
    simp [hn]

end WordCertDensity.Reference
