/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryPrefix
public import WordCertDensity.Analytic.LocalPrimitive.WordEntries

/-! # Actual entry and exit selections depend only on sampled prefixes

The two words may have different future lengths and values. Agreement is
required only through the observed event time, where both have complete pairs.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

/-- Agreement through T pairs implies agreement through every earlier pair. -/
theorem word_take_pair_prefix {u v : ValuationWord} {q T : ℕ}
    (he : u.take (2 * T) = v.take (2 * T)) (hq : q ≤ T) :
    u.take (2 * q) = v.take (2 * q) := by
  have hh := congrArg (fun w : ValuationWord => w.take (2 * q)) he
  simpa only [List.take_take, min_eq_left (Nat.mul_le_mul_left 2 hq)] using hh

/-- Prefix agreement determines the actual sampled height. -/
theorem entryWordHeight_prefix_congr (l : ℤ) {u v : ValuationWord} {T : ℕ}
    (hu : 2 * T ≤ u.length) (hv : 2 * T ≤ v.length)
    (he : u.take (2 * T) = v.take (2 * T)) :
    entryWordHeight l u T = entryWordHeight l v T := by
  rw [entryWordHeight_of_sampled l u T hu, entryWordHeight_of_sampled l v T hv, he]

/-- Entry blackness at a sampled time does not inspect the next pair. -/
theorem entryWordBlack_prefix_congr (n : ℕ) (ξ : ZMod (3 ^ n)) (j : ℕ) (l : ℤ)
    {u v : ValuationWord} {T : ℕ} (hu : 2 * T ≤ u.length) (hv : 2 * T ≤ v.length)
    (he : u.take (2 * T) = v.take (2 * T)) :
    entryWordBlack n ξ j l u T ↔ entryWordBlack n ξ j l v T := by
  simp only [entryWordBlack, hu, hv, true_and, entryWordHeight_prefix_congr l hu hv he]

private theorem entryTriangle_val_congr {n j : ℕ} {a b : ℤ}
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (hab : a = b)
    (ha : phaseBlackAtInt n ξ j a) (hb : phaseBlackAtInt n ξ j b) :
    (entryTriangle hn hj ξ hξ ha).val = (entryTriangle hn hj ξ hξ hb).val := by
  subst b
  rfl

/-- Even the chosen triangle, not merely its membership predicate, is fixed
by the current prefix. Proof arguments do not change its choice. -/
theorem entryWordTriangle_prefix_congr {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    {u v : ValuationWord} {T : ℕ} (hu : 2 * T ≤ u.length) (hv : 2 * T ≤ v.length)
    (he : u.take (2 * T) = v.take (2 * T)) :
    entryWordTriangle hn ξ hξ j l u T = entryWordTriangle hn ξ hξ j l v T := by
  have hh := entryWordHeight_prefix_congr l hu hv he
  have hb := entryWordBlack_prefix_congr n ξ j l hu hv he
  by_cases hbU : entryWordBlack n ξ j l u T
  · have hbV := hb.mp hbU
    simp only [entryWordTriangle, dif_pos hbU, dif_pos hbV]
    exact entryTriangle_val_congr hn (by have := hbU.2.1; omega) ξ hξ hh hbU.2.2 hbV.2.2
  · have hbV : ¬ entryWordBlack n ξ j l v T := fun h => hbU (hb.mpr h)
    simp only [entryWordTriangle, dif_neg hbU, dif_neg hbV, hh]

/-- An actual recorded entry is unchanged by arbitrary fresh continuation. -/
theorem wordBlackEntryTime_prefix_congr {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    {u v : ValuationWord} {T : ℕ} (hu : 2 * T ≤ u.length) (hv : 2 * T ≤ v.length)
    (he : u.take (2 * T) = v.take (2 * T)) (r : ℕ) :
    wordBlackEntryTime hn ξ hξ j l u r = some T ↔
      wordBlackEntryTime hn ξ hξ j l v r = some T := by
  apply blackEntryTime_prefix_congr _ _ _ _ _ _ T
  · intro q hq
    exact entryWordBlack_prefix_congr n ξ j l (by omega) (by omega)
      (word_take_pair_prefix he hq)
  · intro q hq
    exact entryWordHeight_prefix_congr l (by omega) (by omega) (word_take_pair_prefix he hq)
  · intro q hq
    exact congrArg Prod.snd (entryWordTriangle_prefix_congr hn ξ hξ j l
      (by omega) (by omega) (word_take_pair_prefix he hq))
  · exact le_rfl

/-- An actual recorded fixed-top exit is also a prefix event. -/
theorem wordBlackExitTime_prefix_congr {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    {u v : ValuationWord} {T : ℕ} (hu : 2 * T ≤ u.length) (hv : 2 * T ≤ v.length)
    (he : u.take (2 * T) = v.take (2 * T)) (r : ℕ) :
    wordBlackExitTime hn ξ hξ j l u r = some T ↔
      wordBlackExitTime hn ξ hξ j l v r = some T := by
  apply blackExitTime_prefix_congr _ _ _ _ _ _ T
  · intro q hq
    exact entryWordBlack_prefix_congr n ξ j l (by omega) (by omega)
      (word_take_pair_prefix he hq)
  · intro q hq
    exact entryWordHeight_prefix_congr l (by omega) (by omega) (word_take_pair_prefix he hq)
  · intro q hq
    exact congrArg Prod.snd (entryWordTriangle_prefix_congr hn ξ hξ j l
      (by omega) (by omega) (word_take_pair_prefix he hq))
  · exact le_rfl

end WordCertDensity.LocalPrimitive
