/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PotentialProductBridge
import Mathlib.Tactic

/-! # Exact deterministic-time splitting of product moments -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The original word law and the literal product split simultaneously after
an arbitrary deterministic number of pairs. -/
theorem whiteWindowProduct_moment_add (white : ℕ → ℤ → Prop) (z : ℝ≥0∞)
    (h k j : ℕ) (l : ℤ) :
    (∑' w : ValuationWord, Reference.wordPMF (2 * (h + k)) w *
      whiteWindowProduct white z (h + k) j l w) =
    ∑' u : ValuationWord, Reference.wordPMF (2 * h) u *
      whiteWindowProduct white z h j l u *
        ∑' v : ValuationWord, Reference.wordPMF (2 * k) v *
          whiteWindowProduct white z k (j + h) (l + u.total) v := by
  rw [show 2 * (h + k) = 2 * h + 2 * k by omega,
    ← Reference.wordPMF_append (2 * h) (2 * k), PMFMoment.sum_bind]
  simp_rw [PMFMoment.sum_map]
  apply tsum_congr
  intro u
  by_cases hu : u.length = 2 * h
  · simp_rw [whiteWindowProduct_add]
    calc
      _ = ∑' v : ValuationWord,
          (Reference.wordPMF (2 * h) u) *
            ((Reference.wordPMF (2 * k) v) *
              (whiteWindowProduct white z h j l (u ++ v) *
                whiteWindowProduct white z k (j + h)
                  (l + ValuationWord.total ((u ++ v).take (2 * h)))
                  ((u ++ v).drop (2 * h)))) := by
        rw [ENNReal.tsum_mul_left]
      _ = ∑' v : ValuationWord,
          (Reference.wordPMF (2 * h) u *
            whiteWindowProduct white z h j l u) *
            (Reference.wordPMF (2 * k) v *
              whiteWindowProduct white z k (j + h) (l + u.total) v) := by
        apply tsum_congr
        intro v
        have hprod : whiteWindowProduct white z h j l (u ++ v) =
            whiteWindowProduct white z h j l u := by
          rw [← whiteWindowProduct_take white z h j l (u ++ v)]
          congr 1
          rw [List.take_append]
          simp [hu]
        rw [hprod]
        simp only [List.take_left' hu, List.drop_left' hu,
          ValuationWord.total_append, mul_assoc]
        ac_rfl
      _ = _ := by rw [ENNReal.tsum_mul_left]
  · simp [Reference.wordPMF_eq_zero_of_length_ne (2 * h) u hu]

/-- The recursive real potential satisfies the same exact semigroup law. -/
theorem integerPairPotential_add {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : ℕ → ℤ → Prop) (h k j : ℕ) (l : ℤ) :
    integerPairPotential ε white (h + k) j l =
      ∑' u : ValuationWord, (Reference.wordPMF (2 * h) u).toReal *
        (whiteWindowProduct white (ENNReal.ofReal (1 - 2 * ε ^ 2)) h j l u).toReal *
          integerPairPotential ε white k (j + h) (l + u.total) := by
  have hz : ENNReal.ofReal (1 - 2 * ε ^ 2) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg ε]
  rw [← whiteWindowProduct_eq_integerPairPotential hε,
    whiteWindowProduct_moment_add]
  have hinner (u : ValuationWord) :
      (∑' v : ValuationWord, Reference.wordPMF (2 * k) v *
        whiteWindowProduct white (ENNReal.ofReal (1 - 2 * ε ^ 2)) k
          (j + h) (l + u.total) v) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (whiteWindowProduct_mass_le_one white hz k (j + h) (l + u.total))
  have hprefix (u : ValuationWord) :
      whiteWindowProduct white (ENNReal.ofReal (1 - 2 * ε ^ 2)) h j l u ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (whiteWindowProduct_le_one white hz h j l u)
  rw [ENNReal.tsum_toReal_eq (fun u => ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hprefix u)) (hinner u))]
  apply tsum_congr
  intro u
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    whiteWindowProduct_eq_integerPairPotential hε]

end WordCertDensity.LocalPrimitive
