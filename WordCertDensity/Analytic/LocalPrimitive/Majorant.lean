/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.Pairing
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith

/-!
# Discounted majorant for the original pair process

This file defines the finite-horizon potential used in Appendix E directly
from the original two-letter word PMF. The white-state predicate is a
parameter here; its phase-geometric characterization belongs to E-L2.
-/

@[expose] public section

namespace WordCertDensity
namespace LocalPrimitive

open scoped Classical

private theorem pairWordWeights_summable :
    Summable (fun w : ValuationWord => (Reference.wordPMF 2 w).toReal) :=
  ENNReal.summable_toReal (by
    rw [PMF.tsum_coe]
    exact ENNReal.one_ne_top)

/-- Real weights of the original two-letter law sum to one. -/
theorem pairWordWeights_tsum_eq_one :
    (∑' w : ValuationWord, (Reference.wordPMF 2 w).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq]
  · rw [PMF.tsum_coe]
    norm_num
  · intro w
    exact PMF.apply_ne_top _ _

/-- The original pair has total valuation three with probability exactly one quarter. -/
theorem pairTotalThree_weight_sum :
    (∑' w : ValuationWord,
      if w.total = 3 then (Reference.wordPMF 2 w).toReal else 0) = 1 / 4 := by
  have h := Reference.pair_probability_eq_pairMass (b := 3) (by omega)
  rw [Gated.probability, ENNReal.tsum_toReal_eq] at h
  · rw [Reference.pairMass_eq (b := 3) (by omega)] at h
    norm_num at h ⊢
    convert h using 1
    apply tsum_congr
    intro w
    by_cases hw : w.total = 3 <;> simp [hw]
  · intro w
    split_ifs
    · exact PMF.apply_ne_top _ _
    · simp

/-- The one-step discount: only a marked pair of total three loses mass. -/
noncomputable def pairDiscount (ε : ℝ) (white : Prop) (w : ValuationWord) : ℝ :=
  if white ∧ w.total = 3 then 1 - 2 * ε ^ 2 else 1

/-- The paper's averaged one-step loss. -/
noncomputable def pairLoss (ε : ℝ) : ℝ := ε ^ 2 / 2

/-- The dyadic phase width fixed in Appendix E. -/
noncomputable def localEpsilon : ℝ := (1 / 2 : ℝ) ^ 78

/-- The fixed dyadic width is nonnegative. -/
theorem localEpsilon_nonneg : 0 ≤ localEpsilon := by
  unfold localEpsilon
  positivity

/-- The fixed dyadic width makes the polynomial discount nonnegative. -/
theorem localEpsilon_guard : 2 * localEpsilon ^ 2 ≤ 1 := by
  unfold localEpsilon
  norm_num

/-- Discount written on the pair-total state space. -/
noncomputable def totalDiscount (ε : ℝ) (white : Prop) (b : ℕ) : ℝ :=
  if white ∧ b = 3 then 1 - 2 * ε ^ 2 else 1

private theorem totalDiscount_nonneg {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : Prop) (b : ℕ) : 0 ≤ totalDiscount ε white b := by
  unfold totalDiscount
  split_ifs <;> linarith

private theorem totalDiscount_le_one (ε : ℝ) (white : Prop) (b : ℕ) :
    totalDiscount ε white b ≤ 1 := by
  unfold totalDiscount
  split_ifs
  · nlinarith [sq_nonneg ε]
  · exact le_rfl

/-- Pair masses over all possible totals form a probability distribution. -/
theorem pairMass_tsum_eq_one :
    (∑' b : {b : ℕ // 2 ≤ b}, Reference.pairMass b.1) = 1 := by
  let g : Reference.PairIndex → ℝ := fun p =>
    (Reference.wordPMF 2 (Reference.pairIndexWord p)).toReal
  have hg : Summable g := pairWordWeights_summable.comp_injective
    Reference.pairIndexWord_injective
  calc
    (∑' b : {b : ℕ // 2 ≤ b}, Reference.pairMass b.1) =
        ∑' b : {b : ℕ // 2 ≤ b}, ∑' i : Fin (b.1 - 1),
          (Reference.wordPMF 2 (Reference.pairWord b.1 i)).toReal := by
            apply tsum_congr
            intro b
            rw [tsum_fintype]
            rfl
    _ = ∑' p : Reference.PairIndex,
          (Reference.wordPMF 2 (Reference.pairIndexWord p)).toReal := by
            exact hg.tsum_sigma.symm
    _ = ∑' w : ValuationWord, (Reference.wordPMF 2 w).toReal := by
            symm
            apply Reference.tsum_eq_tsum_pairIndex
            intro w hw
            rw [Reference.wordPMF_eq_zero_of_length_ne 2 w hw, ENNReal.toReal_zero]
    _ = 1 := pairWordWeights_tsum_eq_one

private theorem pairMass_summable :
    Summable (fun b : {b : ℕ // 2 ≤ b} => Reference.pairMass b.1) := by
  let g : Reference.PairIndex → ℝ := fun p =>
    (Reference.wordPMF 2 (Reference.pairIndexWord p)).toReal
  have hg : Summable g := pairWordWeights_summable.comp_injective
    Reference.pairIndexWord_injective
  have hgs := hg.sigma
  exact hgs.congr fun b => by
    rw [tsum_fintype]
    rfl

private theorem pairDiscount_nonneg {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : Prop) (w : ValuationWord) : 0 ≤ pairDiscount ε white w := by
  unfold pairDiscount
  split_ifs <;> linarith

private theorem pairDiscount_le_one {ε : ℝ} (white : Prop) (w : ValuationWord) :
    pairDiscount ε white w ≤ 1 := by
  unfold pairDiscount
  split_ifs
  · nlinarith [sq_nonneg ε]
  · exact le_rfl

private theorem discountedRow_summable {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : Prop) (V : ValuationWord → ℝ) (hV0 : ∀ w, 0 ≤ V w)
    (hV1 : ∀ w, V w ≤ 1) :
    Summable (fun w : ValuationWord =>
      (Reference.wordPMF 2 w).toReal * pairDiscount ε white w * V w) := by
  refine Summable.of_norm_bounded pairWordWeights_summable ?_
  intro w
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      (Reference.wordPMF 2 w).toReal * pairDiscount ε white w * V w
          ≤ (Reference.wordPMF 2 w).toReal * 1 * 1 := by
            calc
              _ ≤ (Reference.wordPMF 2 w).toReal * 1 * V w :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (pairDiscount_le_one white w)
                    ENNReal.toReal_nonneg) (hV0 w)
              _ ≤ (Reference.wordPMF 2 w).toReal * 1 * 1 :=
                mul_le_mul_of_nonneg_left (hV1 w)
                  (mul_nonneg ENNReal.toReal_nonneg zero_le_one)
      _ = (Reference.wordPMF 2 w).toReal := by ring
  · exact mul_nonneg
      (mul_nonneg ENNReal.toReal_nonneg (pairDiscount_nonneg hε white w))
      (hV0 w)

/-- Finite-horizon discounted potential from pair column j and total l. -/
noncomputable def pairPotential (ε : ℝ) (white : ℕ → ℕ → Prop) :
    ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 1
  | h + 1, j, l =>
      ∑' w : ValuationWord,
        (Reference.wordPMF 2 w).toReal * pairDiscount ε (white j l) w *
          pairPotential ε white h (j + 1) (l + w.total)

/-- The discounted potential is nonnegative at every finite horizon. -/
theorem pairPotential_nonneg {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : ℕ → ℕ → Prop) :
    ∀ h j l, 0 ≤ pairPotential ε white h j l := by
  intro h
  induction h with
  | zero => simp [pairPotential]
  | succ h ih =>
      intro j l
      rw [pairPotential]
      exact tsum_nonneg fun w => mul_nonneg
        (mul_nonneg ENNReal.toReal_nonneg (pairDiscount_nonneg hε _ w))
        (ih (j + 1) (l + w.total))

/-- The discounted potential never exceeds one. -/
theorem pairPotential_le_one {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : ℕ → ℕ → Prop) :
    ∀ h j l, pairPotential ε white h j l ≤ 1 := by
  intro h
  induction h with
  | zero => simp [pairPotential]
  | succ h ih =>
      intro j l
      rw [pairPotential]
      calc
        _ ≤ ∑' w : ValuationWord, (Reference.wordPMF 2 w).toReal := by
          apply Summable.tsum_le_tsum
          · intro w
            calc
              (Reference.wordPMF 2 w).toReal * pairDiscount ε (white j l) w *
                    pairPotential ε white h (j + 1) (l + w.total)
                  ≤ (Reference.wordPMF 2 w).toReal * 1 * 1 := by
                    calc
                      _ ≤ (Reference.wordPMF 2 w).toReal * 1 *
                            pairPotential ε white h (j + 1) (l + w.total) :=
                        mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left (pairDiscount_le_one _ w)
                            ENNReal.toReal_nonneg)
                          (pairPotential_nonneg hε white h (j + 1) (l + w.total))
                      _ ≤ (Reference.wordPMF 2 w).toReal * 1 * 1 :=
                        mul_le_mul_of_nonneg_left (ih (j + 1) (l + w.total))
                          (mul_nonneg ENNReal.toReal_nonneg zero_le_one)
              _ = (Reference.wordPMF 2 w).toReal := by ring
          · exact discountedRow_summable hε _ _
              (fun w => pairPotential_nonneg hε white h (j + 1) (l + w.total))
              (fun w => ih (j + 1) (l + w.total))
          · exact pairWordWeights_summable
        _ = 1 := pairWordWeights_tsum_eq_one

/-- At a white state the one-step discounted kernel has mass exactly 1-d. -/
theorem white_pairKernel_mass {ε : ℝ} (white : Prop) (hwhite : white) :
    (∑' w : ValuationWord,
      (Reference.wordPMF 2 w).toReal * pairDiscount ε white w) =
        1 - pairLoss ε := by
  have hs : Summable (fun w : ValuationWord => (Reference.wordPMF 2 w).toReal) :=
    pairWordWeights_summable
  have he : Summable (fun w : ValuationWord =>
      if w.total = 3 then (Reference.wordPMF 2 w).toReal else 0) := by
    refine Summable.of_nonneg_of_le (fun w => by positivity) ?_ hs
    intro w
    split_ifs <;> simp
  rw [show (fun w : ValuationWord =>
      (Reference.wordPMF 2 w).toReal * pairDiscount ε white w) =
      fun w => (Reference.wordPMF 2 w).toReal -
        (2 * ε ^ 2) *
          (if w.total = 3 then (Reference.wordPMF 2 w).toReal else 0) by
    funext w
    simp only [pairDiscount, hwhite, true_and]
    split_ifs <;> ring]
  rw [hs.tsum_sub (he.mul_left (2 * ε ^ 2)), tsum_mul_left,
    pairWordWeights_tsum_eq_one, pairTotalThree_weight_sum]
  unfold pairLoss
  ring

/-- The same white-kernel normalization on the total/splitting state space
used by the Fourier recurrence. -/
theorem white_totalKernel_mass {ε : ℝ} (white : Prop) (hwhite : white) :
    (∑' b : {b : ℕ // 2 ≤ b},
      Reference.pairMass b.1 * totalDiscount ε white b.1) =
        1 - pairLoss ε := by
  have he : Summable (fun b : {b : ℕ // 2 ≤ b} =>
      if b.1 = 3 then Reference.pairMass b.1 else 0) := by
    refine Summable.of_nonneg_of_le (fun b => by
      split_ifs
      · exact Reference.pairMass_nonneg b.1
      · exact le_rfl) ?_ pairMass_summable
    intro b
    split_ifs <;> simp [Reference.pairMass_nonneg]
  have hsingle : (∑' b : {b : ℕ // 2 ≤ b},
      if b.1 = 3 then Reference.pairMass b.1 else 0) = Reference.pairMass 3 := by
    rw [tsum_eq_single (⟨3, by omega⟩ : {b : ℕ // 2 ≤ b})]
    · simp
    · intro b hb
      have hne : b.1 ≠ 3 := by
        intro h
        apply hb
        exact Subtype.ext h
      simp [hne]
  rw [show (fun b : {b : ℕ // 2 ≤ b} =>
      Reference.pairMass b.1 * totalDiscount ε white b.1) =
      fun b => Reference.pairMass b.1 -
        (2 * ε ^ 2) * (if b.1 = 3 then Reference.pairMass b.1 else 0) by
    funext b
    simp only [totalDiscount, hwhite, true_and]
    split_ifs <;> ring]
  rw [pairMass_summable.tsum_sub (he.mul_left (2 * ε ^ 2)),
    tsum_mul_left, pairMass_tsum_eq_one, hsingle,
    Reference.pairMass_eq (b := 3) (by omega)]
  unfold pairLoss
  norm_num
  ring

/-- Both endpoint inequalities for the potential, bundled for later consumers. -/
theorem pairPotential_mem_unitInterval {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : ℕ → ℕ → Prop) (h j l : ℕ) :
    0 ≤ pairPotential ε white h j l ∧ pairPotential ε white h j l ≤ 1 :=
  ⟨pairPotential_nonneg hε white h j l, pairPotential_le_one hε white h j l⟩

/-- A state is analytically white when its total-three conditional factor has
the exact polynomial discount required by Appendix E. E-L2 identifies this
predicate with the balanced-phase condition away from the black set. -/
def analyticWhite (ε : ℝ) (u : ℕ) (ξ : ZMod (3 ^ (u + 2))) : Prop :=
  ‖reversePairFactor u 3 ξ‖ ≤ 1 - 2 * ε ^ 2

/-- The paper's local cosine estimate: once the balanced phase identifies the
total-three factor with `cos (πt)`, every phase outside width `ε` is
analytically white. Establishing the phase identity and its lattice geometry
is the separate E-L2 obligation. -/
theorem analyticWhite_of_balancedPhase {ε t : ℝ} (hε : 0 ≤ ε)
    (ht : |t| ≤ 1 / 2) (hwhite : ε ≤ |t|) (u : ℕ)
    (ξ : ZMod (3 ^ (u + 2)))
    (hfactor : ‖reversePairFactor u 3 ξ‖ = Real.cos (Real.pi * t)) :
    analyticWhite ε u ξ := by
  unfold analyticWhite
  rw [hfactor]
  have harg : |Real.pi * t| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hcos := Real.cos_le_one_sub_mul_cos_sq harg
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hscale : 2 / Real.pi ^ 2 * (Real.pi * t) ^ 2 = 2 * t ^ 2 := by
    field_simp [hpi]
  rw [hscale] at hcos
  have hsquares : ε ^ 2 ≤ t ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hε] using hwhite
  nlinarith

/-- The finite-level Fourier potential obtained by iterating the discounted
conditional pair recurrence. The two base cases encode both parities. -/
noncomputable def fourierPotential (ε : ℝ) :
    (n : ℕ) → ZMod (3 ^ n) → ℝ
  | 0, _ => 1
  | 1, _ => 1
  | u + 2, ξ =>
      ∑' b : {b : ℕ // 2 ≤ b},
        Reference.pairMass b.1 * totalDiscount ε (analyticWhite ε u ξ) b.1 *
          fourierPotential ε u
            (Reference.project (Nat.le_add_right u 2) ξ *
              Reference.inverseTwoPow u b.1)

private theorem fourierPotentialRow_summable {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (u : ℕ) (ξ : ZMod (3 ^ (u + 2)))
    (hV0 : ∀ η : ZMod (3 ^ u), 0 ≤ fourierPotential ε u η)
    (hV1 : ∀ η : ZMod (3 ^ u), fourierPotential ε u η ≤ 1) :
    Summable (fun b : {b : ℕ // 2 ≤ b} =>
      Reference.pairMass b.1 * totalDiscount ε (analyticWhite ε u ξ) b.1 *
        fourierPotential ε u
          (Reference.project (Nat.le_add_right u 2) ξ *
            Reference.inverseTwoPow u b.1)) := by
  refine Summable.of_norm_bounded pairMass_summable ?_
  intro b
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      _ ≤ Reference.pairMass b.1 * 1 * 1 := by
        calc
          _ ≤ Reference.pairMass b.1 * 1 * fourierPotential ε u
                (Reference.project (Nat.le_add_right u 2) ξ *
                  Reference.inverseTwoPow u b.1) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (totalDiscount_le_one ε _ b.1) (by
                unfold Reference.pairMass
                positivity)) (hV0 _)
          _ ≤ Reference.pairMass b.1 * 1 * 1 :=
            mul_le_mul_of_nonneg_left (hV1 _)
              (mul_nonneg (by unfold Reference.pairMass; positivity) zero_le_one)
      _ = Reference.pairMass b.1 := by ring
  · exact mul_nonneg
      (mul_nonneg (by unfold Reference.pairMass; positivity)
        (totalDiscount_nonneg hε _ b.1)) (hV0 _)

/-- The Fourier potential is nonnegative and at most one at every level,
including both parity base cases. -/
theorem fourierPotential_mem_unitInterval {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1) :
    ∀ n (ξ : ZMod (3 ^ n)),
      0 ≤ fourierPotential ε n ξ ∧ fourierPotential ε n ξ ≤ 1 := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro ξ; simp [fourierPotential]
  | one => intro ξ; simp [fourierPotential]
  | more u ih0 _ih1 =>
      intro ξ
      constructor
      · rw [fourierPotential]
        exact tsum_nonneg fun b => mul_nonneg
          (mul_nonneg (by unfold Reference.pairMass; positivity)
            (totalDiscount_nonneg hε _ b.1)) (ih0 _).1
      · rw [fourierPotential]
        calc
          _ ≤ ∑' b : {b : ℕ // 2 ≤ b}, Reference.pairMass b.1 := by
            apply Summable.tsum_le_tsum
            · intro b
              calc
                _ ≤ Reference.pairMass b.1 * 1 * 1 := by
                  calc
                    _ ≤ Reference.pairMass b.1 * 1 * fourierPotential ε u
                          (Reference.project (Nat.le_add_right u 2) ξ *
                            Reference.inverseTwoPow u b.1) :=
                      mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_left (totalDiscount_le_one ε _ b.1) (by
                          unfold Reference.pairMass
                          positivity)) (ih0 _).1
                    _ ≤ Reference.pairMass b.1 * 1 * 1 :=
                      mul_le_mul_of_nonneg_left (ih0 _).2
                        (mul_nonneg (by unfold Reference.pairMass; positivity) zero_le_one)
                _ = Reference.pairMass b.1 := by ring
            · exact fourierPotentialRow_summable hε u ξ
                (fun η => (ih0 η).1) (fun η => (ih0 η).2)
            · exact pairMass_summable
          _ = 1 := pairMass_tsum_eq_one

/-- The even base potential is one. -/
theorem fourierPotential_zero (ε : ℝ) (ξ : ZMod (3 ^ 0)) :
    fourierPotential ε 0 ξ = 1 := rfl

/-- The odd base potential is one. -/
theorem fourierPotential_one (ε : ℝ) (ξ : ZMod (3 ^ 1)) :
    fourierPotential ε 1 ξ = 1 := rfl

/-- The possible final odd letter costs at most one. -/
theorem oddTerminal_fourier_le_one (ξ : ZMod (3 ^ 1)) :
    ‖Reference.fourierMass 1 ξ‖ ≤ 1 := norm_fourierMass_le_one 1 ξ

private theorem norm_reversePairFactor_le_discount (ε : ℝ) (u : ℕ)
    (ξ : ZMod (3 ^ (u + 2))) (b : {b : ℕ // 2 ≤ b}) :
    ‖reversePairFactor u b.1 ξ‖ ≤
      totalDiscount ε (analyticWhite ε u ξ) b.1 := by
  by_cases hw : analyticWhite ε u ξ
  · by_cases hb3 : b.1 = 3
    · simp only [totalDiscount, hw, hb3, and_self, if_pos]
      simpa only [analyticWhite] using hw
    · rw [totalDiscount, if_neg]
      · exact norm_reversePairFactor_le_one u b.2 ξ
      · exact fun h => hb3 h.2
  · rw [totalDiscount, if_neg]
    · exact norm_reversePairFactor_le_one u b.2 ξ
    · exact fun h => hw h.1

/-- The actual reference Fourier coefficient is bounded by the iterated
discounted pair potential. This includes level zero, level one, and every
even or odd higher level. -/
theorem norm_fourierMass_le_fourierPotential {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1) :
    ∀ n (ξ : ZMod (3 ^ n)),
      ‖Reference.fourierMass n ξ‖ ≤ fourierPotential ε n ξ := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro ξ
      simpa [fourierPotential] using norm_fourierMass_le_one 0 ξ
  | one =>
      intro ξ
      simpa [fourierPotential] using norm_fourierMass_le_one 1 ξ
  | more u ih0 _ih1 =>
      intro ξ
      let lowerFrequency : {b : ℕ // 2 ≤ b} → ZMod (3 ^ u) := fun b =>
        Reference.project (Nat.le_add_right u 2) ξ *
          Reference.inverseTwoPow u b.1
      let actualTerm : {b : ℕ // 2 ≤ b} → ℂ := fun b =>
        (Reference.pairMass b.1 : ℂ) * reversePairFactor u b.1 ξ *
          Reference.fourierMass u (lowerFrequency b)
      let boundTerm : {b : ℕ // 2 ≤ b} → ℝ := fun b =>
        Reference.pairMass b.1 * totalDiscount ε (analyticWhite ε u ξ) b.1 *
          fourierPotential ε u (lowerFrequency b)
      have hrec : Reference.fourierMass (u + 2) ξ = ∑' b, actualTerm b := by
        rw [fourierMass_pair_recurrence_grouped]
        apply tsum_congr
        intro b
        change Reference.pairWeightedSum b.1 (fun i =>
          reversePairCharacter u b.1 ξ i *
            Reference.fourierMass u (lowerFrequency b)) = actualTerm b
        exact pairWeightedTail_eq u b.2 ξ
      have hactual : Summable (fun b => ‖actualTerm b‖) := by
        refine Summable.of_nonneg_of_le (fun b => norm_nonneg _) ?_ pairMass_summable
        intro b
        simp only [actualTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Reference.pairMass_nonneg b.1)]
        calc
          Reference.pairMass b.1 * ‖reversePairFactor u b.1 ξ‖ *
                ‖Reference.fourierMass u (lowerFrequency b)‖
              ≤ Reference.pairMass b.1 * 1 * 1 := by
                calc
                  _ ≤ Reference.pairMass b.1 * 1 *
                        ‖Reference.fourierMass u (lowerFrequency b)‖ :=
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left
                        (norm_reversePairFactor_le_one u b.2 ξ)
                        (Reference.pairMass_nonneg b.1)) (norm_nonneg _)
                  _ ≤ Reference.pairMass b.1 * 1 * 1 :=
                    mul_le_mul_of_nonneg_left
                      (norm_fourierMass_le_one u (lowerFrequency b))
                      (mul_nonneg (Reference.pairMass_nonneg b.1) zero_le_one)
          _ = Reference.pairMass b.1 := by ring
      have hbound : Summable boundTerm := by
        exact fourierPotentialRow_summable hε u ξ
          (fun η => (fourierPotential_mem_unitInterval hε u η).1)
          (fun η => (fourierPotential_mem_unitInterval hε u η).2)
      rw [hrec]
      calc
        ‖∑' b, actualTerm b‖ ≤ ∑' b, ‖actualTerm b‖ :=
          norm_tsum_le_tsum_norm hactual
        _ ≤ ∑' b, boundTerm b := by
          apply Summable.tsum_le_tsum
          · intro b
            simp only [actualTerm, boundTerm, norm_mul, Complex.norm_real,
              Real.norm_eq_abs,
              abs_of_nonneg (Reference.pairMass_nonneg b.1)]
            calc
              Reference.pairMass b.1 * ‖reversePairFactor u b.1 ξ‖ *
                    ‖Reference.fourierMass u (lowerFrequency b)‖
                  ≤ Reference.pairMass b.1 *
                      totalDiscount ε (analyticWhite ε u ξ) b.1 *
                        ‖Reference.fourierMass u (lowerFrequency b)‖ :=
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left
                        (norm_reversePairFactor_le_discount ε u ξ b)
                        (Reference.pairMass_nonneg b.1)) (norm_nonneg _)
              _ ≤ Reference.pairMass b.1 *
                    totalDiscount ε (analyticWhite ε u ξ) b.1 *
                      fourierPotential ε u (lowerFrequency b) :=
                    mul_le_mul_of_nonneg_left (ih0 (lowerFrequency b))
                      (mul_nonneg (Reference.pairMass_nonneg b.1)
                        (totalDiscount_nonneg hε _ b.1))
          · exact hactual
          · exact hbound
        _ = fourierPotential ε (u + 2) ξ := by
          rfl

/-- E-L1's concrete Appendix-E majorant at the fixed dyadic width. -/
theorem norm_fourierMass_le_localPotential (n : ℕ) (ξ : ZMod (3 ^ n)) :
    ‖Reference.fourierMass n ξ‖ ≤ fourierPotential localEpsilon n ξ :=
  norm_fourierMass_le_fourierPotential localEpsilon_guard n ξ

end LocalPrimitive
end WordCertDensity
