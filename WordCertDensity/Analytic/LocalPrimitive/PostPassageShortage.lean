/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PassageStopping
public import WordCertDensity.Analytic.LocalPrimitive.PostPassageGeometry
public import WordCertDensity.Analytic.LocalPrimitive.ShortageSmallTriangles
import Mathlib.Tactic

/-! # White-shortage probability after the original first passage -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- White shortage in the literal suffix following the first crossing. -/
def postPassageShortageEvent (n : ℕ) (ξ : ZMod (3 ^ n))
    (s j : ℕ) (l : ℤ) (B : ℕ) (w : ValuationWord) : Prop :=
  ∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w ∧
    sampledWhiteStateCount n ξ (j + ((i : ℕ) + 1))
      (l + ValuationWord.total (w.take (2 * ((i : ℕ) + 1))))
      (w.drop (2 * ((i : ℕ) + 1))) (localPrimitiveP B) < localPrimitiveK B

/-- Outside the E-L4 union, the original-word post-passage shortage has
mass at most delta. The proof averages over the exact passage prefixes. -/
theorem postPassage_shortage_outside_union_mass_le {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (s j : ℕ) (l : ℤ) (B L : ℕ)
    (hL : s / 2 + 1 + localPrimitiveP B + (8 * n + 8) ≤ L) :
    (∑' w : ValuationWord,
      if postPassageShortageEvent n ξ s j l B w ∧
        ¬ longCrossingLargeUnionEvent n ξ s j l (localPrimitiveH B) (localPrimitiveP B) w
      then Reference.wordPMF (2 * L) w else 0) ≤
        ENNReal.ofReal (1 / (localPrimitiveDeltaDenom B : ℝ)) := by
  let E : ValuationWord → ValuationWord → Prop := fun u v =>
    (∃ t, t ≤ localPrimitiveP B ∧
      wordBlackEntryTime hn ξ hξ (j + u.length / 2) (l + u.total) v
        (localPrimitiveR B - 1) = some t) ∧
    sampledWhiteStateCount n ξ (j + u.length / 2) (l + u.total) v
      (localPrimitiveP B) < localPrimitiveK B
  have hlen : ∀ u ∈ passagePrefixFamily s, u.length ≤ 2 * L := by
    intro u hu
    have := passagePrefixFamily_length s u hu
    omega
  have htail : ∀ u : passagePrefixFamily s, (∑' v : ValuationWord,
      if E u v then Reference.wordPMF (2 * L - (u : ValuationWord).length) v else 0) ≤
        ENNReal.ofReal (1 / (localPrimitiveDeltaDenom B : ℝ)) := by
    intro u
    obtain ⟨i, hi, _⟩ := u.property
    have hiL := i.isLt
    have hrem : 2 * L - (u : ValuationWord).length = 2 * (L - ((i : ℕ) + 1)) := by
      omega
    rw [hrem]
    exact (entry_white_shortage_mass_le hn ξ hξ
      (j + (u : ValuationWord).length / 2) (l + (u : ValuationWord).total)
      (localPrimitiveR B - 1) (localPrimitiveP B) (localPrimitiveP B)
      (L - ((i : ℕ) + 1)) (localPrimitiveK B) le_rfl (by omega)).trans
        (entry_recipe_mass_le_delta B)
  have hstopped := countableStoppedTail_le (passagePrefixFamily s) (2 * L) E
    hlen (passagePrefixFamily_prefix_free s)
    (ENNReal.ofReal (1 / (localPrimitiveDeltaDenom B : ℝ)))
  have hb : (∑' w : ValuationWord,
      if ∃ u : passagePrefixFamily s,
        (u : ValuationWord) <+: w ∧ E u (w.drop (u : ValuationWord).length)
      then Reference.wordPMF (2 * L) w else 0) ≤
        ENNReal.ofReal (1 / (localPrimitiveDeltaDenom B : ℝ)) := by
    apply hstopped
    intro u
    convert htail u using 1
    apply tsum_congr
    intro v
    by_cases hv : E u v <;> simp [hv]
  apply le_trans _ hb
  apply ENNReal.tsum_le_tsum
  intro w
  by_cases hw : w.length = 2 * L
  · by_cases he : postPassageShortageEvent n ξ s j l B w ∧
        ¬ longCrossingLargeUnionEvent n ξ s j l (localPrimitiveH B) (localPrimitiveP B) w
    · have hevent := he
      obtain ⟨⟨i, hi, hshort⟩, hnot⟩ := he
      have hidx := i.isLt
      have hsample : 2 * ((i : ℕ) + 1 + localPrimitiveP B) ≤ w.length := by omega
      obtain ⟨t, ht, hent⟩ := postPassage_entry_of_shortage hn ξ hξ s j l B w i
        hi hsample hnot hshort
      have hp := passagePrefixFamily_take s w i hi (by omega)
      have hpl : (w.take (2 * ((i : ℕ) + 1))).length = 2 * ((i : ℕ) + 1) :=
        List.length_take_of_le (by omega)
      have hselected : ∃ u : passagePrefixFamily s,
          (u : ValuationWord) <+: w ∧ E u (w.drop (u : ValuationWord).length) := by
        refine ⟨⟨w.take (2 * ((i : ℕ) + 1)), hp⟩, List.take_prefix _ _, ?_⟩
        dsimp [E]
        rw [hpl]
        have hd : 2 * ((i : ℕ) + 1) / 2 = (i : ℕ) + 1 := by omega
        rw [hd]
        exact ⟨⟨t, ht.le, hent⟩, hshort⟩
      rw [if_pos hevent, if_pos hselected]
    · rw [if_neg he]
      exact zero_le
  · have hz := Reference.wordPMF_eq_zero_of_length_ne (2 * L) w hw
    simp only [hz, ite_self]
    exact le_rfl

end WordCertDensity.LocalPrimitive
