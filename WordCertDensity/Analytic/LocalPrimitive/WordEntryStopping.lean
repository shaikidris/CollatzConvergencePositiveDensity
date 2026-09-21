/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.WordEntryPrefix
public import WordCertDensity.Reference.CountableStopping
public import WordCertDensity.Analytic.LocalPrimitive.StoppedTail

/-! # Countable stopping families of actual black entries

Every family member is the exact complete prefix ending at the r-th entry.
Valuations remain unbounded. Prefix stability, rather than a finite alphabet,
makes this family prefix-free and identifies its mass with the original event.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- Exact prefixes ending at entry r no later than pair time H. -/
def wordEntryPrefixFamily {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ) (r H : ℕ) : Set ValuationWord :=
  {u | ∃ t, t ≤ H ∧ u.length = 2 * t ∧ wordBlackEntryTime hn ξ hξ j l u r = some t}

/-- The actual entry family has the required bounded word horizon. -/
theorem wordEntryPrefixFamily_length {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ) (r H : ℕ)
    (u : ValuationWord) (hu : u ∈ wordEntryPrefixFamily hn ξ hξ j l r H) :
    u.length ≤ 2 * H := by
  obtain ⟨t, ht, hlen, _⟩ := hu
  omega

/-- Two distinct prefixes cannot both be the same numbered actual entry. -/
theorem wordEntryPrefixFamily_prefix_free {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ) (r H : ℕ) :
    (wordEntryPrefixFamily hn ξ hξ j l r H).Pairwise (fun u v => ¬ u <+: v) := by
  intro u hu v hv hne huv
  obtain ⟨t, _, hlenU, ht⟩ := hu
  obtain ⟨s, _, hlenV, hs⟩ := hv
  have hlen := huv.length_le
  have he : u.take (2 * t) = v.take (2 * t) := by
    rw [← hlenU, List.take_length]
    exact List.prefix_iff_eq_take.mp huv
  have htV := (wordBlackEntryTime_prefix_congr hn ξ hξ j l
    (by omega) (by omega) he r).mp ht
  have hts : t = s := Option.some.inj (htV.symm.trans hs)
  apply hne
  apply huv.eq_of_length
  omega

/-- A full word has one of these stopping prefixes exactly when its actual
entry r occurs by H. This equivalence is pointwise, before taking probability. -/
theorem wordEntryPrefixFamily_event_iff {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ) (r H : ℕ)
    (w : ValuationWord) :
    (∃ u ∈ wordEntryPrefixFamily hn ξ hξ j l r H, u <+: w) ↔
      ∃ t, t ≤ H ∧ wordBlackEntryTime hn ξ hξ j l w r = some t := by
  constructor
  · rintro ⟨u, ⟨t, htH, hlen, ht⟩, hup⟩
    have he : u.take (2 * t) = w.take (2 * t) := by
      rw [← hlen, List.take_length]
      exact List.prefix_iff_eq_take.mp hup
    refine ⟨t, htH, ?_⟩
    exact (wordBlackEntryTime_prefix_congr hn ξ hξ j l
      (by omega) (by have := hup.length_le; omega) he r).mp ht
  · rintro ⟨t, htH, ht⟩
    have hsample := (wordBlackEntryTime_spec hn ξ hξ j l w r t ht).1
    have hlen : (w.take (2 * t)).length = 2 * t := List.length_take_of_le hsample
    have he : w.take (2 * t) = (w.take (2 * t)).take (2 * t) := by simp
    have htPrefix := (wordBlackEntryTime_prefix_congr hn ξ hξ j l hsample
      (by omega) he r).mp ht
    exact ⟨w.take (2 * t), ⟨t, htH, hlen, htPrefix⟩, List.take_prefix _ _⟩

/-- The actual entry event has exactly its countable stopping-family mass
under the original common word law. There is no conditioning on the entry. -/
theorem wordEntryPrefixFamily_probability {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ) (r H Q : ℕ) (hHQ : H ≤ Q) :
    Gated.probability (Reference.wordPMF (2 * Q))
      (fun w => ∃ t, t ≤ H ∧ wordBlackEntryTime hn ξ hξ j l w r = some t) =
      Reference.countableStoppingMassReal (wordEntryPrefixFamily hn ξ hξ j l r H) := by
  have hlen : ∀ u ∈ wordEntryPrefixFamily hn ξ hξ j l r H, u.length ≤ 2 * Q := by
    intro u hu
    have := wordEntryPrefixFamily_length hn ξ hξ j l r H u hu
    omega
  rw [Reference.countableStoppingMassReal,
    Reference.countableStoppingMass_eq_event _ (2 * Q) hlen
      (wordEntryPrefixFamily_prefix_free hn ξ hξ j l r H)]
  unfold Gated.probability
  congr 1
  apply tsum_congr
  intro w
  have he := wordEntryPrefixFamily_event_iff hn ξ hξ j l r H w
  by_cases ht : ∃ t, t ≤ H ∧ wordBlackEntryTime hn ξ hξ j l w r = some t
  · have hp := he.mpr ht
    simp [ht, hp]
  · have hp : ¬ ∃ u ∈ wordEntryPrefixFamily hn ξ hξ j l r H, u <+: w :=
      fun h => ht (he.mp h)
    simp [ht, hp]

/-- Prefix-dependent future events at the actual r-th entry retain the exact
original tail law, with no renormalization by the entry probability. -/
theorem wordEntryPrefixFamily_tail_factor {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ) (r H Q : ℕ) (hHQ : H ≤ Q)
    (B : ValuationWord → ValuationWord → Prop) :
    (∑' w : ValuationWord,
      if ∃ u : wordEntryPrefixFamily hn ξ hξ j l r H,
        (u : ValuationWord) <+: w ∧ B u (w.drop (u : ValuationWord).length)
      then Reference.wordPMF (2 * Q) w else 0) =
    ∑' u : wordEntryPrefixFamily hn ξ hξ j l r H,
      Reference.wordPMF (u : ValuationWord).length u *
        ∑' v : ValuationWord,
          if B u v then Reference.wordPMF (2 * Q - (u : ValuationWord).length) v
          else 0 := by
  apply countableStoppedTail_factor
  · intro u hu
    have := wordEntryPrefixFamily_length hn ξ hξ j l r H u hu
    omega
  · exact wordEntryPrefixFamily_prefix_free hn ξ hξ j l r H

end WordCertDensity.LocalPrimitive
