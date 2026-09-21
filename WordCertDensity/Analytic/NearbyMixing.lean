/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Analytic.HeadEntropy
import WordCertDensity.Analytic.FailureBound
import WordCertDensity.Analytic.Collision
import WordCertDensity.Analytic.TailDecay
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# General-width mixing for nearby conductors

The original head/tail convolution and the audited primitive decay discharge
all analytic inputs. Each slice takes its collision square root before the
2n² candidate slices are summed; rejected mass keeps its original weight.
-/

namespace WordCertDensity

namespace FiniteFourier

/-- Finite families pay the sum of their individual unhalved oscillations. -/
theorem oscillation_sum_le {m n : ℕ} (h : m ≤ n) {ι : Type*}
    (s : Finset ι) (p : ι → ZMod (3 ^ n) → ℝ) :
    oscillation h (fun x => ∑ i ∈ s, p i x) ≤ ∑ i ∈ s, oscillation h (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (oscillation_add_le h (p i) (fun x => ∑ j ∈ s, p j x)).trans
      (add_le_add le_rfl ih)

end FiniteFourier

namespace HeadSlice

/-- A slice with no admitted head is zero under the original full-word law. -/
theorem mass_eq_zero_of_no_head {v : ℝ} {n k l : ℕ} (hk : k < n)
    (hempty : ¬ ∃ w : ValuationWord, Head.Gate v n k l w) :
    mass v n k l = fun _ => 0 := by
  obtain ⟨T, rfl⟩ : ∃ T, n = T + (k + 1) :=
    ⟨n - (k + 1), (Nat.sub_add_cancel (Nat.succ_le_of_lt hk)).symm⟩
  have hp : Head.mass v (T + (k + 1)) k l = fun _ => 0 := by
    funext y
    apply Head.mass_eq_zero_of_no_head
    rintro ⟨w, hw, _⟩
    exact hempty ⟨w, hw⟩
  funext x
  rw [mass_eq_convolution, hp, FiniteFourier.convolution_zero_left]

/-- Every candidate slice has the half-entropy decay, including empty slices. -/
theorem oscillation_mass_le {v : ℝ} {m n k l : ℕ}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n)
    (hmn : m ≤ n) (hm : 9 * n ≤ 10 * m) (hk : k < n) :
    FiniteFourier.oscillation hmn (mass v n k l) ≤
      Analytic.tailCoefficient * (n : ℝ) ^ (-6409 + Real.log 2 * v ^ 2 / 2) := by
  by_cases hex : ∃ w : ValuationWord, Head.Gate v n k l w
  · obtain ⟨w, hw⟩ := hex
    have hr := hw.ranges hv hv' hn
    have hhead : k + 1 ≤ m := by omega
    obtain ⟨T, rfl⟩ : ∃ T, n = T + (k + 1) :=
      ⟨n - (k + 1), (Nat.sub_add_cancel (Nat.succ_le_of_lt hk)).symm⟩
    have hn0 : (0 : ℝ) < (T + (k + 1) : ℕ) := by positivity
    have hδ : 0 ≤ Analytic.tailCoefficient / ((T + (k + 1) : ℕ) : ℝ) ^ 6409 :=
      div_nonneg Analytic.tailCoefficient_pos.le (pow_nonneg hn0.le _)
    have hc := FiniteFourier.oscillation_convolution_sq_le hmn
      (Head.mass v (T + (k + 1)) k l) (AffineTail.mass (k + 1) T l) hδ
      (fun _ hξ => Analytic.affineTailDecay hhead hm hr.1 hξ)
    simp only [sq_abs] at hc
    have hL2 := Head.mass_second_moment_le hv hv' hn (k := k) (l := l)
    have hent := Head.entropy_lt (by omega : 0 < T + (k + 1)) hr.2.1
    have hs : FiniteFourier.oscillation hmn (mass v (T + (k + 1)) k l) ^ 2 ≤
        (Analytic.tailCoefficient * ((T + (k + 1) : ℕ) : ℝ) ^
          (-6409 + Real.log 2 * v ^ 2 / 2)) ^ 2 := by
      rw [show mass v (T + (k + 1)) k l =
        FiniteFourier.convolution (Head.mass v (T + (k + 1)) k l)
          (AffineTail.mass (k + 1) T l) from funext (mass_eq_convolution v T k l)]
      rw [Head.slice_rate_sq hn0]
      calc
        _ ≤ _ := hc
        _ ≤ (Analytic.tailCoefficient / ((T + (k + 1) : ℕ) : ℝ) ^ 6409) ^ 2 *
            ((3 : ℝ) ^ (T + (k + 1)) / (2 : ℝ) ^ l) := by
          have hcoef : 0 ≤
              (Analytic.tailCoefficient / ((T + (k + 1) : ℕ) : ℝ) ^ 6409) ^ 2 *
                (3 : ℝ) ^ (T + (k + 1)) :=
            mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _)
          simpa only [div_eq_mul_inv, one_mul, mul_assoc] using
            mul_le_mul_of_nonneg_left hL2 hcoef
        _ ≤ _ := mul_le_mul_of_nonneg_left hent.le (sq_nonneg _)
    exact (sq_le_sq₀ (FiniteFourier.oscillation_nonneg _ _)
      (mul_nonneg Analytic.tailCoefficient_pos.le (Real.rpow_nonneg hn0.le _))).mp hs
  · rw [mass_eq_zero_of_no_head hk hex, FiniteFourier.oscillation_zero]
    exact mul_nonneg Analytic.tailCoefficient_pos.le (Real.rpow_nonneg (Nat.cast_nonneg n) _)

end HeadSlice

namespace Analytic

/-- The nearby-conductor envelope, with the exact collision and rejection debits. -/
noncomputable def mixingEnvelope (v x : ℝ) : ℝ :=
  2 * tailCoefficient * x ^ (-6407 + Real.log 2 * v ^ 2 / 2) +
    2 * Head.failureEnvelope v x

private theorem sum_slice_rate {v : ℝ} {n : ℕ} (hn : 0 < n) :
    (∑ _i : HeadSlice.Index n,
      tailCoefficient * (n : ℝ) ^ (-6409 + Real.log 2 * v ^ 2 / 2)) =
      2 * tailCoefficient * (n : ℝ) ^ (-6407 + Real.log 2 * v ^ 2 / 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Finset.sum_const, Finset.card_univ, HeadSlice.card_index, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [show (-6407 + Real.log 2 * v ^ 2 / 2 : ℝ) =
    2 + (-6409 + Real.log 2 * v ^ 2 / 2) by ring,
    Real.rpow_add hn' 2 (-6409 + Real.log 2 * v ^ 2 / 2), Real.rpow_two]
  ring

/-- Nearby conductors mix with the actual atypical-word probability (M.high). -/
theorem nearby_oscillation_le_failure {v : ℝ} {m n : ℕ}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n)
    (hmn : m ≤ n) (hm : 9 * n ≤ 10 * m) :
    FiniteFourier.oscillation hmn (Reference.mass n) ≤
      2 * tailCoefficient * (n : ℝ) ^ (-6407 + Real.log 2 * v ^ 2 / 2) +
        2 * HeadSlice.failureProbability v n := by
  have hdec : Reference.mass n = fun x =>
      (∑ i : HeadSlice.Index n, HeadSlice.mass v n i.1 i.2 x) +
        HeadSlice.rejectedMass v n x := funext (HeadSlice.reference_mass_decomposition v n)
  rw [hdec]
  calc
    _ ≤ FiniteFourier.oscillation hmn
        (fun x => ∑ i : HeadSlice.Index n, HeadSlice.mass v n i.1 i.2 x) +
        FiniteFourier.oscillation hmn (HeadSlice.rejectedMass v n) :=
      FiniteFourier.oscillation_add_le _ _ _
    _ ≤ (∑ i : HeadSlice.Index n,
        FiniteFourier.oscillation hmn (HeadSlice.mass v n i.1 i.2)) +
        2 * HeadSlice.failureProbability v n := by
      apply add_le_add (FiniteFourier.oscillation_sum_le _ _ _)
      exact (FiniteFourier.oscillation_le_two_mul_sum hmn _
        (HeadSlice.rejectedMass_nonneg v n)).trans
        (mul_le_mul_of_nonneg_left (HeadSlice.rejectedMass_sum_le_failure hv hv' hn)
          (by norm_num))
    _ ≤ (∑ _i : HeadSlice.Index n,
        tailCoefficient * (n : ℝ) ^ (-6409 + Real.log 2 * v ^ 2 / 2)) +
        2 * HeadSlice.failureProbability v n := by
      apply add_le_add _ le_rfl
      exact Finset.sum_le_sum fun i _ =>
        HeadSlice.oscillation_mass_le hv hv' hn hmn hm i.1.isLt
    _ = _ := by rw [sum_slice_rate (by omega)]

/-- The full general-width nearby-conductor estimate with every input discharged. -/
theorem nearby_oscillation_le {v : ℝ} {m n : ℕ}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n)
    (hmn : m ≤ n) (hm : 9 * n ≤ 10 * m) :
    FiniteFourier.oscillation hmn (Reference.mass n) ≤ mixingEnvelope v n := by
  exact (nearby_oscillation_le_failure hv hv' hn hmn hm).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (HeadSlice.failureProbability_le (n := n) hv (by omega)) (by norm_num)))

/-- The same bound in the full-group reference-density normalization. -/
theorem nearby_mean_le {v : ℝ} {m n : ℕ}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n)
    (hmn : m ≤ n) (hm : 9 * n ≤ 10 * m) :
    Reference.mean n (fun x =>
      |Reference.density n x - Reference.density m (Reference.project hmn x)|) ≤
        mixingEnvelope v n := by
  rw [← FiniteFourier.oscillation_mass hmn]
  exact nearby_oscillation_le hv hv' hn hmn hm

end Analytic
end WordCertDensity
