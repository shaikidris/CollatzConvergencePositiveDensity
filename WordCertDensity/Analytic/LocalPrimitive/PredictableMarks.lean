/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.WhiteVisits
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Moments of the first selected white marks

The state is tested before reading its next pair. Once the quota of white
states has been sampled, the remaining word contributes weight one.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The generating-function factor of a total-three pair mark. -/
noncomputable def pairMarkFactor (z : ℝ≥0∞) (u : ValuationWord) : ℝ≥0∞ :=
  if u.total = 3 then z else 1

/-- The original pair law has the Bernoulli-quarter generating function. -/
theorem pairMarkFactor_moment (z : ℝ≥0∞) :
    (∑' u : ValuationWord, Reference.wordPMF 2 u * pairMarkFactor z u) =
      (1 / 4 : ℝ≥0∞) * z + 3 / 4 := by
  let A : ValuationWord → Prop := fun u => u.total = 3
  have ha : (∑' u : ValuationWord, @ite ℝ≥0∞ (A u) (Classical.propDecidable _)
      (Reference.wordPMF 2 u) 0) =
      (1 / 4 : ℝ≥0∞) := by
    apply (ENNReal.toReal_eq_toReal_iff' (Gated.event_ne_top _ A) (by finiteness)).mp
    change Gated.probability (Reference.wordPMF 2) A = (1 / 4 : ℝ≥0∞).toReal
    rw [freshPair_total_three_probability]
    norm_num
  have hb : (∑' u : ValuationWord, @ite ℝ≥0∞ (¬ A u) (Classical.propDecidable _)
      (Reference.wordPMF 2 u) 0) =
      (3 / 4 : ℝ≥0∞) := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (Gated.event_ne_top _ (fun u => ¬ A u)) (by finiteness)).mp
    change Gated.probability (Reference.wordPMF 2) (fun u => ¬ A u) =
      (3 / 4 : ℝ≥0∞).toReal
    rw [Gated.probability_compl, freshPair_total_three_probability]
    norm_num
  calc
    _ = ∑' u : ValuationWord,
        ((@ite ℝ≥0∞ (A u) (Classical.propDecidable _) (Reference.wordPMF 2 u) 0) * z +
          (@ite ℝ≥0∞ (¬ A u) (Classical.propDecidable _) (Reference.wordPMF 2 u) 0)) := by
      apply tsum_congr
      intro u
      by_cases h : A u <;> simp [pairMarkFactor, A] at h ⊢ <;> simp [h]
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ha, hb]

/-- Product of the generating-function factors at the first k white states
in h pair steps, evaluated directly on a reference valuation word. -/
noncomputable def predictableMarkWeight (white : ℕ → ℤ → Prop) (z : ℝ≥0∞) :
    ℕ → ℕ → ℕ → ℤ → ValuationWord → ℝ≥0∞
  | 0, _, _, _, _ => 1
  | _ + 1, 0, _, _, _ => 1
  | h + 1, k + 1, j, l, w =>
      if white j l then
        pairMarkFactor z (w.take 2) *
          predictableMarkWeight white z h k (j + 1)
            (l + ValuationWord.total (w.take 2)) (w.drop 2)
      else
        predictableMarkWeight white z h (k + 1) (j + 1)
          (l + ValuationWord.total (w.take 2)) (w.drop 2)

/-- The moment is computed on the unconditioned original word PMF. -/
noncomputable def predictableMarkMoment (white : ℕ → ℤ → Prop) (z : ℝ≥0∞)
    (h k j : ℕ) (l : ℤ) : ℝ≥0∞ :=
  ∑' w : ValuationWord, Reference.wordPMF (2 * h) w *
    predictableMarkWeight white z h k j l w

/-- With no requested samples the moment is one. -/
theorem predictableMarkMoment_zero_quota (white : ℕ → ℤ → Prop) (z : ℝ≥0∞)
    (h j : ℕ) (l : ℤ) : predictableMarkMoment white z h 0 j l = 1 := by
  cases h <;> simp [predictableMarkMoment, predictableMarkWeight, PMF.tsum_coe]

/-- Exact one-pair moment recursion, obtained by splitting the original
word law. Whiteness is decided before the pair variable is integrated. -/
theorem predictableMarkMoment_succ (white : ℕ → ℤ → Prop) (z : ℝ≥0∞)
    (h k j : ℕ) (l : ℤ) :
    predictableMarkMoment white z (h + 1) (k + 1) j l =
      ∑' u : ValuationWord, Reference.wordPMF 2 u *
        (if white j l then pairMarkFactor z u *
          predictableMarkMoment white z h k (j + 1) (l + u.total)
        else predictableMarkMoment white z h (k + 1) (j + 1) (l + u.total)) := by
  rw [predictableMarkMoment, show 2 * (h + 1) = 2 + 2 * h by omega,
    ← Reference.wordPMF_append 2 (2 * h), PMFMoment.sum_bind]
  simp_rw [PMFMoment.sum_map]
  apply tsum_congr
  intro u
  by_cases hu : u.length = 2
  · simp only [predictableMarkWeight, List.take_left' hu, List.drop_left' hu]
    by_cases hw : white j l
    · simp only [if_pos hw]
      congr 1
      rw [predictableMarkMoment, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro v
      ac_rfl
    · simp only [if_neg hw]
      rfl
  · simp [Reference.wordPMF_eq_zero_of_length_ne 2 u hu]

/-- The first k white samples have the exact Bernoulli-quarter moment on
the original word law. The white extension supplies a deterministic horizon
even when every earlier state is black. -/
theorem predictableMarkMoment_eq (white : ℕ → ℤ → Prop) (z : ℝ≥0∞) (N : ℕ)
    (hext : ∀ j, N ≤ j → ∀ l, white j l) (h k j : ℕ) (l : ℤ)
    (hh : k + (N - j) ≤ h) :
    predictableMarkMoment white z h k j l = ((1 / 4 : ℝ≥0∞) * z + 3 / 4) ^ k := by
  induction h generalizing k j l with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      rw [predictableMarkMoment_zero_quota, pow_zero]
  | succ h ih =>
      cases k with
      | zero => rw [predictableMarkMoment_zero_quota, pow_zero]
      | succ k =>
          rw [predictableMarkMoment_succ]
          by_cases hw : white j l
          · have ht (u : ValuationWord) :
                predictableMarkMoment white z h k (j + 1) (l + u.total) =
                  ((1 / 4 : ℝ≥0∞) * z + 3 / 4) ^ k :=
              ih k (j + 1) (l + u.total) (by omega)
            simp_rw [if_pos hw, ht, ← mul_assoc]
            rw [ENNReal.tsum_mul_right, pairMarkFactor_moment, pow_succ]
            exact mul_comm _ _
          · have hj : j < N := by
              by_contra hn
              exact hw (hext j (by omega) l)
            have ht (u : ValuationWord) :
                predictableMarkMoment white z h (k + 1) (j + 1) (l + u.total) =
                  ((1 / 4 : ℝ≥0∞) * z + 3 / 4) ^ (k + 1) :=
              ih (k + 1) (j + 1) (l + u.total) (by omega)
            simp_rw [if_neg hw, ht]
            rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Number of total-three marks among the first k white states encountered
in h steps. The history is advanced by one pair on every step. -/
noncomputable def predictableMarkCount (white : ℕ → ℤ → Prop) :
    ℕ → ℕ → ℕ → ℤ → ValuationWord → ℕ
  | 0, _, _, _, _ => 0
  | _ + 1, 0, _, _, _ => 0
  | h + 1, k + 1, j, l, w =>
      if white j l then
        (if ValuationWord.total (w.take 2) = 3 then 1 else 0) +
          predictableMarkCount white h k (j + 1)
            (l + ValuationWord.total (w.take 2)) (w.drop 2)
      else
        predictableMarkCount white h (k + 1) (j + 1)
          (l + ValuationWord.total (w.take 2)) (w.drop 2)

/-- The scan weight is exactly the generating function of its literal mark
count, including incomplete horizons. -/
theorem predictableMarkWeight_eq_pow (white : ℕ → ℤ → Prop) (z : ℝ≥0∞)
    (h k j : ℕ) (l : ℤ) (w : ValuationWord) :
    predictableMarkWeight white z h k j l w =
      z ^ predictableMarkCount white h k j l w := by
  induction h generalizing k j l w with
  | zero => simp [predictableMarkWeight, predictableMarkCount]
  | succ h ih =>
      cases k with
      | zero => simp [predictableMarkWeight, predictableMarkCount]
      | succ k =>
          by_cases hw : white j l
          · by_cases hm : ValuationWord.total (w.take 2) = 3
            · simp [predictableMarkWeight, predictableMarkCount, pairMarkFactor,
                hw, hm, ih, pow_add]
            · simp [predictableMarkWeight, predictableMarkCount, pairMarkFactor,
                hw, hm, ih]
          · simp [predictableMarkWeight, predictableMarkCount, hw, ih]

/-- Source-law generating function for the first k predictable marks. -/
theorem predictableMarkCount_moment (white : ℕ → ℤ → Prop) (z : ℝ≥0∞) (N : ℕ)
    (hext : ∀ j, N ≤ j → ∀ l, white j l) (h k j : ℕ) (l : ℤ)
    (hh : k + (N - j) ≤ h) :
    (∑' w : ValuationWord, Reference.wordPMF (2 * h) w *
      z ^ predictableMarkCount white h k j l w) =
      ((1 / 4 : ℝ≥0∞) * z + 3 / 4) ^ k := by
  simp_rw [← predictableMarkWeight_eq_pow]
  exact predictableMarkMoment_eq white z N hext h k j l hh

end WordCertDensity.LocalPrimitive
