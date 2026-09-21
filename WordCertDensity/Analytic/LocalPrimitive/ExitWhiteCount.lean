/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryDiscountHistory
import Mathlib.Tactic

/-! # Distinct white exits inject into the observed white states -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

/-- All existing exits are strictly ordered, not just consecutive ones. -/
theorem blackExitTime_strict_of_lt (black : ℕ → Prop) (height top : ℕ → ℤ)
    (i r t v : ℕ) (hir : i < r)
    (ht : blackExitTime black height top i = some t)
    (hv : blackExitTime black height top r = some v) : t < v := by
  obtain ⟨s, hs, _⟩ := Option.bind_eq_some_iff.mp hv
  obtain ⟨q, hq, hqs⟩ := blackEntryTime_earlier_exit black height top r s hs i hir
  have htq : t = q := Option.some.inj (ht.symm.trans hq)
  have hsv := (blackExitTime_spec black height top r s v hs hv).1
  omega

/-- A recorded exit time determines its exit index uniquely. -/
theorem blackExitTime_index_unique (black : ℕ → Prop) (height top : ℕ → ℤ)
    (i r t : ℕ) (hi : blackExitTime black height top i = some t)
    (hr : blackExitTime black height top r = some t) : i = r := by
  rcases lt_trichotomy i r with h | h | h
  · exact False.elim (Nat.lt_irrefl t (blackExitTime_strict_of_lt black height top i r t t h hi hr))
  · exact h
  · exact False.elim (Nat.lt_irrefl t (blackExitTime_strict_of_lt black height top r i t t h hr hi))

/-- Literal number of white sampled state times before P. -/
noncomputable def sampledWhiteStateCount (n : ℕ) (ξ : ZMod (3 ^ n)) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (P : ℕ) : ℕ :=
  ((Finset.range P).filter (fun t =>
    extendedPhaseWhite n ξ (j + t) (entryWordHeight l w t))).card

/-- Every counted past white exit is a distinct white state in the window. -/
theorem pastWhiteExitCount_le_states {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r T P : ℕ) (hTP : T ≤ P) :
    pastWhiteExitCount hn ξ hξ j l w T r ≤ sampledWhiteStateCount n ξ j l w P := by
  unfold pastWhiteExitCount sampledWhiteStateCount
  apply Finset.card_le_card_of_injOn (fun i => (wordBlackExitTime hn ξ hξ j l w i).getD 0)
  · intro i hi
    obtain ⟨t, htT, ht, hw⟩ := (Finset.mem_filter.mp hi).2
    simp only [ht, Option.getD_some]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hw⟩
  · intro i hi k hk he
    obtain ⟨t, _, ht, _⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨v, _, hv, _⟩ := (Finset.mem_filter.mp hk).2
    simp only [ht, hv, Option.getD_some] at he
    rw [← he] at hv
    exact blackExitTime_index_unique (entryWordBlack n ξ j l w) (entryWordHeight l w)
      (fun q => (entryWordTriangle hn ξ hξ j l w q).2) i k t ht hv

end WordCertDensity.LocalPrimitive
