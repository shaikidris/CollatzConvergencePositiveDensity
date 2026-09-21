/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.FirstPassage
public import WordCertDensity.Analytic.LocalPrimitive.StoppedTail
import Mathlib.Tactic

/-! # Original-law stopping at the first pair passage -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The passage event only reads the prefix through its crossing pair. -/
theorem horizonTailEvent_prefix_iff {s H i : ℕ} {u w : ValuationWord}
    (hup : u <+: w) (hlen : 2 * (i + 1) ≤ u.length) :
    horizonTailEvent s H i u ↔ horizonTailEvent s H i w := by
  have he := List.prefix_iff_eq_take.mp hup
  have hbefore : u.take (2 * i) = w.take (2 * i) := by
    conv_lhs => rw [he]
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have hafter : u.take (2 * (i + 1)) = w.take (2 * (i + 1)) := by
    conv_lhs => rw [he]
    rw [List.take_take, Nat.min_eq_left hlen]
  simp only [horizonTailEvent, hbefore, hafter]

/-- Exact complete prefixes ending at the first pair crossing of level s. -/
def passagePrefixFamily (s : ℕ) : Set ValuationWord :=
  {u | ∃ i : Fin (s / 2 + 1), u.length = 2 * ((i : ℕ) + 1) ∧
    horizonTailEvent s 0 i u}

/-- The stopping family retains the deterministic first-passage horizon. -/
theorem passagePrefixFamily_length (s : ℕ) (u : ValuationWord)
    (hu : u ∈ passagePrefixFamily s) : u.length ≤ 2 * (s / 2 + 1) := by
  obtain ⟨i, hlen, _⟩ := hu
  have := i.isLt
  omega

/-- Uniqueness of crossing makes its exact prefixes prefix-free. -/
theorem passagePrefixFamily_prefix_free (s : ℕ) :
    (passagePrefixFamily s).Pairwise (fun u v => ¬ u <+: v) := by
  intro u hu v hv hne huv
  obtain ⟨i, hlenU, hi⟩ := hu
  obtain ⟨k, hlenV, hk⟩ := hv
  have hiV := (horizonTailEvent_prefix_iff huv (by omega)).mp hi
  have hik := horizonTailEvent_unique hiV hk
  exact hne (huv.eq_of_length (by omega))

/-- The observed crossing selects its exact sampled prefix. -/
theorem passagePrefixFamily_take (s : ℕ) (w : ValuationWord)
    (i : Fin (s / 2 + 1)) (hi : horizonTailEvent s 0 i w)
    (hlen : 2 * ((i : ℕ) + 1) ≤ w.length) :
    w.take (2 * ((i : ℕ) + 1)) ∈ passagePrefixFamily s := by
  have ht := List.length_take_of_le hlen
  exact ⟨i, ht, (horizonTailEvent_prefix_iff (List.take_prefix _ _) (by omega)).mpr hi⟩

/-- A uniform fresh-tail bound survives selection by any bounded prefix-free
stopping family, without conditioning or renormalization. -/
theorem countableStoppedTail_le
    (S : Set ValuationWord) (N : ℕ) (B : ValuationWord → ValuationWord → Prop)
    (hlen : ∀ u ∈ S, u.length ≤ N)
    (hfree : S.Pairwise (fun u v => ¬ u <+: v)) (c : ℝ≥0∞)
    (hB : ∀ u : S, (∑' v : ValuationWord,
      if B u v then Reference.wordPMF (N - (u : ValuationWord).length) v else 0) ≤ c) :
    (∑' w : ValuationWord,
      if ∃ u : S, (u : ValuationWord) <+: w ∧ B u (w.drop (u : ValuationWord).length)
      then Reference.wordPMF N w else 0) ≤ c := by
  rw [countableStoppedTail_factor S N B hlen hfree]
  calc
    _ ≤ ∑' u : S, Reference.wordPMF (u : ValuationWord).length u * c :=
      ENNReal.tsum_le_tsum (fun u => mul_le_mul_right (hB u) _)
    _ = Reference.countableStoppingMass S * c := by
      simp_rw [wordPMF_length_eventMass]
      exact ENNReal.tsum_mul_right
    _ ≤ 1 * c := by
      apply mul_le_mul_left
      rw [Reference.countableStoppingMass_eq_event S N hlen hfree]
      calc
        _ ≤ ∑' w : ValuationWord, Reference.wordPMF N w :=
          ENNReal.tsum_le_tsum (fun w => by split_ifs <;> simp)
        _ = 1 := PMF.tsum_coe _
    _ = c := one_mul c

end WordCertDensity.LocalPrimitive
