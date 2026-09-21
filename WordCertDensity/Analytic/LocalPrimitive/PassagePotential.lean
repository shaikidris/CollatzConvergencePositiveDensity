/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.StoppedPotential
import Mathlib.Tactic

/-! # The actual integer potential at an original-law first passage -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- Native nonnegative form of the exact product representation of U. -/
theorem integerPairPotential_ofReal {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : ℕ → ℤ → Prop) (h j : ℕ) (l : ℤ) :
    ENNReal.ofReal (integerPairPotential ε white h j l) =
      ∑' w : ValuationWord, Reference.wordPMF (2 * h) w *
        whiteWindowProduct white (ENNReal.ofReal (1 - 2 * ε ^ 2)) h j l w := by
  rw [← whiteWindowProduct_eq_integerPairPotential hε]
  apply ENNReal.ofReal_toReal
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  apply whiteWindowProduct_mass_le_one
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg ε]

/-- The original integer potential is bounded by the actual remaining
potential averaged at any covering bounded pair stopping family. -/
theorem integerPairPotential_stopping_le {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : ℕ → ℤ → Prop) (m j : ℕ) (l : ℤ) (S : Set ValuationWord)
    (hpair : ∀ u ∈ S, ∃ q, q ≤ m ∧ u.length = 2 * q)
    (hcover : ∀ w : ValuationWord, w.length = 2 * m → ∃ u : S, (u : ValuationWord) <+: w) :
    ENNReal.ofReal (integerPairPotential ε white m j l) ≤
      ∑' u : S, Reference.wordPMF (u : ValuationWord).length u *
        ENNReal.ofReal (integerPairPotential ε white (m - (u : ValuationWord).length / 2)
          (j + (u : ValuationWord).length / 2) (l + (u : ValuationWord).total)) := by
  have hz : ENNReal.ofReal (1 - 2 * ε ^ 2) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg ε]
  have hp := whiteWindowProduct_stopping_le white hz m j l S hpair hcover
  rw [← integerPairPotential_ofReal hε] at hp
  convert hp using 1
  apply tsum_congr
  intro u
  rw [integerPairPotential_ofReal hε]
  have he : 2 * (m - (u : ValuationWord).length / 2) =
      2 * m - (u : ValuationWord).length := by
    obtain ⟨q, hq, hlen⟩ := hpair u u.property
    omega
  rw [he]

/-- The exact first-passage family covers every sufficiently long source
word, before any probability or expectation is taken. -/
theorem passagePrefixFamily_covers (s m : ℕ) (hm : s / 2 + 1 ≤ m)
    (w : ValuationWord) (hw : w.length = 2 * m) :
    ∃ u : passagePrefixFamily s, (u : ValuationWord) <+: w := by
  have htlen : (w.take (2 * (s / 2 + 1))).length = 2 * (s / 2 + 1) :=
    List.length_take_of_le (by omega)
  obtain ⟨i, hi⟩ := exists_horizonTailEvent_zero_of_length htlen
  have hidx := i.isLt
  have hip := (horizonTailEvent_prefix_iff (List.take_prefix _ _) (by omega)).mp hi
  exact ⟨⟨w.take (2 * ((i : ℕ) + 1)), passagePrefixFamily_take s w i hip (by omega)⟩,
    List.take_prefix _ _⟩

/-- Discarding pre-passage factors bounds the actual U by the original-law
average of the remaining U at the actual first crossing. -/
theorem integerPairPotential_passage_le {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : ℕ → ℤ → Prop) (s m j : ℕ) (l : ℤ) (hm : s / 2 + 1 ≤ m) :
    ENNReal.ofReal (integerPairPotential ε white m j l) ≤
      ∑' u : passagePrefixFamily s, Reference.wordPMF (u : ValuationWord).length u *
        ENNReal.ofReal (integerPairPotential ε white (m - (u : ValuationWord).length / 2)
          (j + (u : ValuationWord).length / 2) (l + (u : ValuationWord).total)) := by
  apply integerPairPotential_stopping_le hε white m j l (passagePrefixFamily s)
  · intro u hu
    obtain ⟨i, hi, _⟩ := hu
    have hidx := i.isLt
    exact ⟨(i : ℕ) + 1, by omega, hi⟩
  · exact passagePrefixFamily_covers s m hm

end WordCertDensity.LocalPrimitive
