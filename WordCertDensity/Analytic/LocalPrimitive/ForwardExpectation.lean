/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.ForwardExpansion
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Original-law forward character expectations

The definition here remains on `Reference.wordPMF`.  It is the countable-sum
object whose exact Fourier identification and pair-total disintegration form
the remaining E-L6 law bridge.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

private theorem jointPMFMass_summable {α β : Type*} (p : PMF α) (q : α → PMF β) :
    Summable (fun x : α × β => (p x.1).toReal * (q x.1 x.2).toReal) := by
  have hfinite : (∑' x : α × β, p x.1 * q x.1 x.2) ≠ ⊤ := by
    rw [ENNReal.tsum_prod']
    simp only [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
    exact ENNReal.one_ne_top
  simpa only [ENNReal.toReal_mul] using ENNReal.summable_toReal hfinite

private theorem jointPMFCharacter_summable {α β : Type*}
    (p : PMF α) (q : α → PMF β) (f : β → ℂ) (hf : ∀ b, ‖f b‖ ≤ 1) :
    Summable (fun x : α × β =>
      ((p x.1).toReal : ℂ) * (q x.1 x.2).toReal * f x.2) := by
  refine Summable.of_norm_bounded (jointPMFMass_summable p q) ?_
  intro x
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_of_le_one_right
    (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (hf x.2)

private theorem complexPMFBind_atom {α β : Type*} (p : PMF α) (q : α → PMF β)
    (b : β) :
    (((p.bind q) b).toReal : ℂ) =
      ∑' a, ((p a).toReal : ℂ) * (q a b).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq (fun a =>
    ENNReal.mul_ne_top (PMF.apply_ne_top p a) (PMF.apply_ne_top (q a) b)),
    Complex.ofReal_tsum]
  simp only [ENNReal.toReal_mul, Complex.ofReal_mul]

/-- A bounded complex expectation respects probability-mass binding. -/
private theorem complexPMFBind_tsum {α β : Type*} (p : PMF α) (q : α → PMF β)
    (f : β → ℂ) (hf : ∀ b, ‖f b‖ ≤ 1) :
    (∑' b, (((p.bind q) b).toReal : ℂ) * f b) =
      ∑' a, (p a).toReal * ∑' b, ((q a b).toReal : ℂ) * f b := by
  calc
    _ = ∑' b, ∑' a, ((p a).toReal : ℂ) * (q a b).toReal * f b := by
      apply tsum_congr
      intro b
      rw [complexPMFBind_atom, tsum_mul_right]
    _ = ∑' a, ∑' b, ((p a).toReal : ℂ) * (q a b).toReal * f b :=
      Summable.tsum_comm (jointPMFCharacter_summable p q f hf)
    _ = _ := by
      apply tsum_congr
      intro a
      simp only [mul_assoc, tsum_mul_left]

private theorem complexPMFMap_tsum {α β : Type*} (p : PMF α) (g : α → β)
    (f : β → ℂ) (hf : ∀ b, ‖f b‖ ≤ 1) :
    (∑' b, (((p.map g) b).toReal : ℂ) * f b) =
      ∑' a, ((p a).toReal : ℂ) * f (g a) := by
  rw [← PMF.bind_pure_comp, complexPMFBind_tsum p (PMF.pure ∘ g) f hf]
  apply tsum_congr
  intro a
  rw [tsum_eq_single (g a)]
  · simp [PMF.pure_apply]
  · intro b hba
    simp [PMF.pure_apply, hba]

private def valuationWordReverseEquiv : ValuationWord ≃ ValuationWord where
  toFun := List.reverse
  invFun := List.reverse
  left_inv w := List.reverse_reverse w
  right_inv w := List.reverse_reverse w

/-- The original-law expectation of an ordered product of `h` pair characters. -/
noncomputable def forwardCharacterExpectation (n : ℕ) (ξ : ZMod (3 ^ n))
    (h j l : ℕ) : ℂ :=
  ∑' w : ValuationWord,
    ((Reference.wordPMF (2 * h) w).toReal : ℂ) *
      forwardCharacterProduct n ξ h j l w

/-- The empty forward pair expectation is one on the original law. -/
theorem forwardCharacterExpectation_zero (n : ℕ) (ξ : ZMod (3 ^ n))
    (j l : ℕ) : forwardCharacterExpectation n ξ 0 j l = 1 := by
  unfold forwardCharacterExpectation
  rw [Reference.wordPMF_zero]
  rw [tsum_eq_single []]
  · simp [PMF.pure_apply, forwardCharacterProduct]
  · intro w hw
    simp [PMF.pure_apply, hw]

private theorem wordWeights_summable (n : ℕ) :
    Summable (fun w : ValuationWord => (Reference.wordPMF n w).toReal) :=
  ENNReal.summable_toReal (by
    rw [PMF.tsum_coe]
    exact ENNReal.one_ne_top)

/-- The forward original-law character expectation is absolutely summable. -/
theorem forwardCharacterExpectation_summable (n : ℕ) (ξ : ZMod (3 ^ n))
    (h j l : ℕ) :
    Summable (fun w : ValuationWord =>
      ((Reference.wordPMF (2 * h) w).toReal : ℂ) *
        forwardCharacterProduct n ξ h j l w) := by
  refine Summable.of_norm_bounded (wordWeights_summable (2 * h)) ?_
  intro w
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg,
    norm_forwardCharacterProduct_eq_one, mul_one]

/-- An original-law forward character expectation has norm at most one. -/
theorem norm_forwardCharacterExpectation_le_one (n : ℕ) (ξ : ZMod (3 ^ n))
    (h j l : ℕ) : ‖forwardCharacterExpectation n ξ h j l‖ ≤ 1 := by
  unfold forwardCharacterExpectation
  calc
    ‖∑' w : ValuationWord,
        ((Reference.wordPMF (2 * h) w).toReal : ℂ) *
          forwardCharacterProduct n ξ h j l w‖ ≤
        ∑' w : ValuationWord,
          ‖((Reference.wordPMF (2 * h) w).toReal : ℂ) *
            forwardCharacterProduct n ξ h j l w‖ :=
      norm_tsum_le_tsum_norm (forwardCharacterExpectation_summable n ξ h j l).norm
    _ = ∑' w : ValuationWord, (Reference.wordPMF (2 * h) w).toReal := by
      apply tsum_congr
      intro w
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ENNReal.toReal_nonneg,
        norm_forwardCharacterProduct_eq_one, mul_one]
    _ = 1 := by
      rw [← ENNReal.tsum_toReal_eq]
      · exact congrArg ENNReal.toReal (PMF.tsum_coe _)
      · intro w
        exact PMF.apply_ne_top _ _

/-- Splitting the original word law at its first pair gives the exact forward
character recurrence before conditional averaging by the pair total. -/
theorem forwardCharacterExpectation_succ (n h j l : ℕ) (ξ : ZMod (3 ^ n)) :
    forwardCharacterExpectation n ξ (h + 1) j l =
      ∑' u : ValuationWord,
        ((Reference.wordPMF 2 u).toReal : ℂ) *
          ZMod.stdAddChar (ξ * forwardPairOffset n j l u) *
          forwardCharacterExpectation n ξ h (j + 1) (l + u.total) := by
  unfold forwardCharacterExpectation
  rw [show 2 * (h + 1) = 2 + 2 * h by omega, ← Reference.wordPMF_append]
  rw [complexPMFBind_tsum]
  · apply tsum_congr
    intro u
    rw [complexPMFMap_tsum]
    · by_cases hu : u.length = 2
      · calc
          ((Reference.wordPMF 2 u).toReal : ℂ) *
              ∑' v : ValuationWord,
                ((Reference.wordPMF (2 * h) v).toReal : ℂ) *
                  forwardCharacterProduct n ξ (h + 1) j l (u ++ v) =
              ((Reference.wordPMF 2 u).toReal : ℂ) *
                (ZMod.stdAddChar (ξ * forwardPairOffset n j l u) *
                  ∑' v : ValuationWord,
                    ((Reference.wordPMF (2 * h) v).toReal : ℂ) *
                      forwardCharacterProduct n ξ h (j + 1) (l + u.total) v) := by
              congr 1
              rw [← tsum_mul_left]
              apply tsum_congr
              intro v
              rw [forwardCharacterProduct_succ_append_pair n ξ h j l u v hu]
              ring
          _ = _ := by ring
      · rw [Reference.wordPMF_eq_zero_of_length_ne 2 u hu, ENNReal.toReal_zero,
          Complex.ofReal_zero, zero_mul]
        simp
    · intro w
      rw [norm_forwardCharacterProduct_eq_one]
  · intro w
    rw [norm_forwardCharacterProduct_eq_one]

private theorem forwardRecurrence_summable (n h j l : ℕ) (ξ : ZMod (3 ^ n)) :
    Summable (fun u : ValuationWord =>
      ((Reference.wordPMF 2 u).toReal : ℂ) *
        ZMod.stdAddChar (ξ * forwardPairOffset n j l u) *
        forwardCharacterExpectation n ξ h (j + 1) (l + u.total)) := by
  refine Summable.of_norm_bounded (wordWeights_summable 2) ?_
  intro u
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg, AddChar.norm_apply, mul_one]
  simpa only [mul_one] using mul_le_of_le_one_right ENNReal.toReal_nonneg
    (norm_forwardCharacterExpectation_le_one n ξ h (j + 1) (l + u.total))

private theorem forwardPairMass_summable :
    Summable (fun b : {b : ℕ // 2 ≤ b} => Reference.pairMass b.1) := by
  let g : Reference.PairIndex → ℝ := fun p =>
    (Reference.wordPMF 2 (Reference.pairIndexWord p)).toReal
  have hg : Summable g := (wordWeights_summable 2).comp_injective
    Reference.pairIndexWord_injective
  exact hg.sigma.congr fun b => by
    rw [tsum_fintype]
    rfl

private theorem forwardTotalDiscount_nonneg (white : Prop) (b : ℕ) :
    0 ≤ totalDiscount localEpsilon white b := by
  unfold totalDiscount
  split_ifs <;> linarith [localEpsilon_guard]

private theorem forwardTotalDiscount_le_one (white : Prop) (b : ℕ) :
    totalDiscount localEpsilon white b ≤ 1 := by
  unfold totalDiscount
  split_ifs
  · nlinarith [sq_nonneg localEpsilon]
  · exact le_rfl

/-- Grouping the first pair by its total gives the exact conditional forward
factor, while the continuation advances only through that total. -/
theorem forwardCharacterExpectation_succ_eq_pairMass (n h j l : ℕ)
    (ξ : ZMod (3 ^ n)) :
    forwardCharacterExpectation n ξ (h + 1) j l =
      ∑' b : {b : ℕ // 2 ≤ b},
        (Reference.pairMass b.1 : ℂ) * forwardPairFactor n j l b.1 ξ *
          forwardCharacterExpectation n ξ h (j + 1) (l + b.1) := by
  let f : ValuationWord → ℂ := fun u =>
    ((Reference.wordPMF 2 u).toReal : ℂ) *
      ZMod.stdAddChar (ξ * forwardPairOffset n j l u) *
      forwardCharacterExpectation n ξ h (j + 1) (l + u.total)
  have hf : Summable f := forwardRecurrence_summable n h j l ξ
  rw [forwardCharacterExpectation_succ, Reference.tsum_eq_tsum_pairIndex f]
  · have hfi : Summable (f ∘ Reference.pairIndexWord) :=
      hf.comp_injective Reference.pairIndexWord_injective
    change (∑' p : (b : {b : ℕ // 2 ≤ b}) × Fin (b.1 - 1),
      (f ∘ Reference.pairIndexWord) p) = _
    rw [hfi.tsum_sigma]
    apply tsum_congr
    intro b
    rw [tsum_fintype]
    change (∑ i : Fin (b.1 - 1),
      ((Reference.wordPMF 2 (Reference.pairWord b.1 i)).toReal : ℂ) *
        ZMod.stdAddChar (ξ * forwardPairOffset n j l (Reference.pairWord b.1 i)) *
        forwardCharacterExpectation n ξ h (j + 1)
          (l + (Reference.pairWord b.1 i).total)) = _
    simp_rw [Reference.pairWord_total b.2]
    rw [← Finset.sum_mul]
    change Reference.pairWeightedSum b.1 (fun i =>
      ZMod.stdAddChar (ξ * forwardPairOffset n j l (Reference.pairWord b.1 i))) *
        forwardCharacterExpectation n ξ h (j + 1) (l + b.1) = _
    rw [show (fun i => ZMod.stdAddChar
      (ξ * forwardPairOffset n j l (Reference.pairWord b.1 i))) =
        pairCharacter n j l b.1 ξ by
      funext i
      rw [forwardPairOffset_pairWord ξ b.2 i]
      rfl]
    rw [pairWeightedCharacter_eq n j l b.2 ξ]
    rfl
  · intro u hu
    unfold f
    rw [Reference.wordPMF_eq_zero_of_length_ne 2 u hu, ENNReal.toReal_zero,
      Complex.ofReal_zero, zero_mul, zero_mul]

private theorem phasePotentialRecurrence_summable (n h j l : ℕ)
    (ξ : ZMod (3 ^ n)) :
    Summable (fun w : ValuationWord =>
      (Reference.wordPMF 2 w).toReal *
        pairDiscount localEpsilon (phaseWhiteAtInt n ξ j (l : ℤ)) w *
          phasePairPotential n ξ h (j + 1) ((l : ℤ) + w.total)) := by
  refine Summable.of_norm_bounded (wordWeights_summable 2) ?_
  intro w
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      (Reference.wordPMF 2 w).toReal *
          pairDiscount localEpsilon (phaseWhiteAtInt n ξ j (l : ℤ)) w *
            phasePairPotential n ξ h (j + 1) ((l : ℤ) + w.total) ≤
          (Reference.wordPMF 2 w).toReal * 1 * 1 := by
            calc
              _ ≤ ((Reference.wordPMF 2 w).toReal * 1) *
                  phasePairPotential n ξ h (j + 1) ((l : ℤ) + w.total) := by
                    apply mul_le_mul_of_nonneg_right
                    · apply mul_le_mul_of_nonneg_left
                      · unfold pairDiscount
                        split_ifs <;> nlinarith [sq_nonneg localEpsilon]
                      · exact ENNReal.toReal_nonneg
                    · exact (phasePairPotential_mem_unitInterval n ξ h (j + 1)
                        ((l : ℤ) + w.total)).1
              _ ≤ (Reference.wordPMF 2 w).toReal * 1 * 1 := by
                    exact mul_le_mul_of_nonneg_left
                      (phasePairPotential_mem_unitInterval n ξ h (j + 1)
                        ((l : ℤ) + w.total)).2
                      (mul_nonneg ENNReal.toReal_nonneg zero_le_one)
      _ = (Reference.wordPMF 2 w).toReal := by ring
  · exact mul_nonneg
      (mul_nonneg ENNReal.toReal_nonneg (by
        unfold pairDiscount
        split_ifs <;> linarith [localEpsilon_guard]))
      (phasePairPotential_mem_unitInterval n ξ h (j + 1) ((l : ℤ) + w.total)).1

private theorem phasePairPotential_succ_eq_pairMass (n h j l : ℕ)
    (ξ : ZMod (3 ^ n)) :
    phasePairPotential n ξ (h + 1) j (l : ℤ) =
      ∑' b : {b : ℕ // 2 ≤ b},
        Reference.pairMass b.1 *
          totalDiscount localEpsilon (phaseWhiteAtInt n ξ j (l : ℤ)) b.1 *
            phasePairPotential n ξ h (j + 1) ((l + b.1 : ℕ) : ℤ) := by
  let f : ValuationWord → ℝ := fun w =>
    (Reference.wordPMF 2 w).toReal *
      pairDiscount localEpsilon (phaseWhiteAtInt n ξ j (l : ℤ)) w *
        phasePairPotential n ξ h (j + 1) ((l : ℤ) + w.total)
  have hf : Summable f := phasePotentialRecurrence_summable n h j l ξ
  unfold phasePairPotential
  rw [integerPairPotential_succ]
  change (∑' w : ValuationWord, f w) = _
  rw [Reference.tsum_eq_tsum_pairIndex f]
  · have hfi : Summable (f ∘ Reference.pairIndexWord) :=
      hf.comp_injective Reference.pairIndexWord_injective
    change (∑' p : (b : {b : ℕ // 2 ≤ b}) × Fin (b.1 - 1),
      (f ∘ Reference.pairIndexWord) p) = _
    rw [hfi.tsum_sigma]
    apply tsum_congr
    intro b
    rw [tsum_fintype]
    change (∑ i : Fin (b.1 - 1),
      (Reference.wordPMF 2 (Reference.pairWord b.1 i)).toReal *
        pairDiscount localEpsilon (phaseWhiteAtInt n ξ j (l : ℤ))
          (Reference.pairWord b.1 i) *
          phasePairPotential n ξ h (j + 1)
            ((l : ℤ) + (Reference.pairWord b.1 i).total)) = _
    simp_rw [Reference.pairWord_total b.2,
      pairDiscount_pairWord_eq_totalDiscount localEpsilon
        (phaseWhiteAtInt n ξ j (l : ℤ)) b.2]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    rfl
  · intro w hw
    unfold f
    rw [Reference.wordPMF_eq_zero_of_length_ne 2 w hw, ENNReal.toReal_zero,
      zero_mul, zero_mul]

/-- A unit-bounded solution of the exact grouped forward recurrence is
controlled by the literal phase potential, including a nonconstant terminal value. -/
private theorem norm_forwardRecurrence_le_phasePairPotential
    (n : ℕ) (ξ : ZMod (3 ^ n)) (F : ℕ → ℕ → ℕ → ℂ)
    (hunit : ∀ h j l, ‖F h j l‖ ≤ 1)
    (hrec : ∀ h j l, F (h + 1) j l =
      ∑' b : {b : ℕ // 2 ≤ b},
        (Reference.pairMass b.1 : ℂ) * forwardPairFactor n j l b.1 ξ *
          F h (j + 1) (l + b.1)) (h j l : ℕ) :
    ‖F h j l‖ ≤ phasePairPotential n ξ h j (l : ℤ) := by
  induction h generalizing j l with
  | zero =>
      rw [phasePairPotential_zero]
      exact hunit 0 j l
  | succ h ih =>
      let actualTerm : {b : ℕ // 2 ≤ b} → ℂ := fun b =>
        (Reference.pairMass b.1 : ℂ) * forwardPairFactor n j l b.1 ξ *
          F h (j + 1) (l + b.1)
      let boundTerm : {b : ℕ // 2 ≤ b} → ℝ := fun b =>
        Reference.pairMass b.1 *
          totalDiscount localEpsilon (phaseWhiteAtInt n ξ j (l : ℤ)) b.1 *
            phasePairPotential n ξ h (j + 1) ((l + b.1 : ℕ) : ℤ)
      have hactual : Summable (fun b => ‖actualTerm b‖) := by
        refine Summable.of_nonneg_of_le (fun b => norm_nonneg _) ?_
          forwardPairMass_summable
        intro b
        simp only [actualTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Reference.pairMass_nonneg b.1)]
        calc
          Reference.pairMass b.1 * ‖forwardPairFactor n j l b.1 ξ‖ *
                ‖F h (j + 1) (l + b.1)‖ ≤
              Reference.pairMass b.1 * 1 * 1 := by
                calc
                  _ ≤ Reference.pairMass b.1 * 1 *
                      ‖F h (j + 1) (l + b.1)‖ := by
                        exact mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left
                            (norm_forwardPairFactor_le_one n j l b.2 ξ)
                            (Reference.pairMass_nonneg b.1))
                          (norm_nonneg _)
                  _ ≤ Reference.pairMass b.1 * 1 * 1 := by
                        exact mul_le_mul_of_nonneg_left
                          (hunit h (j + 1)
                            (l + b.1))
                          (mul_nonneg (Reference.pairMass_nonneg b.1) zero_le_one)
          _ = Reference.pairMass b.1 := by ring
      have hbound : Summable boundTerm := by
        refine Summable.of_nonneg_of_le (fun b => ?_) ?_ forwardPairMass_summable
        · exact mul_nonneg
            (mul_nonneg (Reference.pairMass_nonneg b.1)
              (forwardTotalDiscount_nonneg _ _))
            (phasePairPotential_mem_unitInterval n ξ h (j + 1)
              ((l + b.1 : ℕ) : ℤ)).1
        · intro b
          calc
            Reference.pairMass b.1 *
                totalDiscount localEpsilon (phaseWhiteAtInt n ξ j (l : ℤ)) b.1 *
                  phasePairPotential n ξ h (j + 1) ((l + b.1 : ℕ) : ℤ) ≤
                Reference.pairMass b.1 * 1 * 1 := by
                  calc
                    _ ≤ (Reference.pairMass b.1 * 1) *
                        phasePairPotential n ξ h (j + 1) ((l + b.1 : ℕ) : ℤ) := by
                          apply mul_le_mul_of_nonneg_right
                          · apply mul_le_mul_of_nonneg_left
                            · exact forwardTotalDiscount_le_one _ _
                            · exact Reference.pairMass_nonneg b.1
                          · exact (phasePairPotential_mem_unitInterval n ξ h (j + 1)
                            ((l + b.1 : ℕ) : ℤ)).1
                    _ ≤ Reference.pairMass b.1 * 1 * 1 := by
                          exact mul_le_mul_of_nonneg_left
                            (phasePairPotential_mem_unitInterval n ξ h (j + 1)
                              ((l + b.1 : ℕ) : ℤ)).2
                            (mul_nonneg (Reference.pairMass_nonneg b.1) zero_le_one)
            _ = Reference.pairMass b.1 := by ring
      rw [hrec,
        phasePairPotential_succ_eq_pairMass]
      calc
        ‖∑' b, actualTerm b‖ ≤ ∑' b, ‖actualTerm b‖ :=
          norm_tsum_le_tsum_norm hactual
        _ ≤ ∑' b, boundTerm b := by
          apply Summable.tsum_le_tsum
          · intro b
            simp only [actualTerm, boundTerm, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg (Reference.pairMass_nonneg b.1)]
            calc
              Reference.pairMass b.1 * ‖forwardPairFactor n j l b.1 ξ‖ *
                    ‖F h (j + 1) (l + b.1)‖ ≤
                  Reference.pairMass b.1 *
                    totalDiscount localEpsilon (phaseWhiteAtInt n ξ j (l : ℤ)) b.1 *
                      ‖F h (j + 1) (l + b.1)‖ := by
                        exact mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left
                            (norm_forwardPairFactor_le_totalDiscount n j l ξ b)
                            (Reference.pairMass_nonneg b.1))
                          (norm_nonneg _)
              _ ≤ Reference.pairMass b.1 *
                    totalDiscount localEpsilon (phaseWhiteAtInt n ξ j (l : ℤ)) b.1 *
                      phasePairPotential n ξ h (j + 1) ((l + b.1 : ℕ) : ℤ) := by
                        exact mul_le_mul_of_nonneg_left (ih (j + 1) (l + b.1))
                          (mul_nonneg (Reference.pairMass_nonneg b.1)
                            (forwardTotalDiscount_nonneg _ _))
          · exact hactual
          · exact hbound

/-- The original-law forward character expectation is dominated by the literal
phase pair potential. -/
theorem norm_forwardCharacterExpectation_le_phasePairPotential
    (n h j l : ℕ) (ξ : ZMod (3 ^ n)) :
    ‖forwardCharacterExpectation n ξ h j l‖ ≤
      phasePairPotential n ξ h j (l : ℤ) :=
  norm_forwardRecurrence_le_phasePairPotential n ξ (forwardCharacterExpectation n ξ)
    (norm_forwardCharacterExpectation_le_one n ξ)
    (fun h j l => forwardCharacterExpectation_succ_eq_pairMass n h j l ξ) h j l

/-- The one-pair forward expectation is exactly the original pair law,
grouped by its total and uniform splitting index. -/
theorem forwardCharacterExpectation_one_eq_pairWeightedSum
    (n j l : ℕ) (ξ : ZMod (3 ^ n)) :
    forwardCharacterExpectation n ξ 1 j l =
      ∑' b : {b : ℕ // 2 ≤ b},
        Reference.pairWeightedSum b.1 (fun i => pairCharacter n j l b.1 ξ i) := by
  let f : ValuationWord → ℂ := fun w =>
    ((Reference.wordPMF 2 w).toReal : ℂ) * forwardCharacterProduct n ξ 1 j l w
  change (∑' w : ValuationWord, f w) = _
  have hf : Summable f := by
    exact forwardCharacterExpectation_summable n ξ 1 j l
  rw [Reference.tsum_eq_tsum_pairIndex f]
  · have hfi : Summable (f ∘ Reference.pairIndexWord) :=
      hf.comp_injective Reference.pairIndexWord_injective
    change (∑' p : (b : {b : ℕ // 2 ≤ b}) × Fin (b.1 - 1),
      (f ∘ Reference.pairIndexWord) p) = _
    rw [hfi.tsum_sigma]
    apply tsum_congr
    intro b
    rw [tsum_fintype]
    unfold Reference.pairWeightedSum
    apply Finset.sum_congr rfl
    intro i _
    change ((Reference.wordPMF 2 (Reference.pairWord b.1 i)).toReal : ℂ) *
        forwardCharacterProduct n ξ 1 j l (Reference.pairWord b.1 i) =
      ((Reference.wordPMF 2 (Reference.pairWord b.1 i)).toReal : ℂ) *
        pairCharacter n j l b.1 ξ i
    simp only [forwardCharacterProduct, mul_one]
    rw [forwardPairOffset_pairWord ξ b.2 i]
    rfl
  · intro w hw
    unfold f
    rw [Reference.wordPMF_eq_zero_of_length_ne 2 w hw, ENNReal.toReal_zero,
      Complex.ofReal_zero, zero_mul]

/-- The one-pair forward expectation is the original pair-total mass times
its exact conditional forward character factor. -/
theorem forwardCharacterExpectation_one_eq_pairMass_factor
    (n j l : ℕ) (ξ : ZMod (3 ^ n)) :
    forwardCharacterExpectation n ξ 1 j l =
      ∑' b : {b : ℕ // 2 ≤ b},
        (Reference.pairMass b.1 : ℂ) * forwardPairFactor n j l b.1 ξ := by
  rw [forwardCharacterExpectation_one_eq_pairWeightedSum]
  apply tsum_congr
  intro b
  simpa [forwardPairFactor] using
    (pairWeightedCharacter_eq n j l b.2 ξ)

private theorem reversedCharacterFiber_summable (n : ℕ) (ξ x : ZMod (3 ^ n)) :
    Summable (fun w : ValuationWord =>
      (((if ValuationWord.residueOffset n w.reverse = x then
        Reference.wordPMF n w else 0).toReal : ℂ) * ZMod.stdAddChar (ξ * x))) := by
  refine Summable.of_norm_bounded (wordWeights_summable n) ?_
  intro w
  rw [norm_mul, AddChar.norm_apply, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg]
  · split_ifs <;> simp [ENNReal.toReal_nonneg]
  · split_ifs <;> exact ENNReal.toReal_nonneg

/-- The Fourier mass is the exact original iid-word character sum, first in
the reversed-word coordinates supplied by the reference-law atom formula. -/
theorem fourierMass_eq_reversed_word_character_expectation
    (n : ℕ) (ξ : ZMod (3 ^ n)) :
    Reference.fourierMass n ξ =
      ∑' w : ValuationWord,
        ((Reference.wordPMF n w).toReal : ℂ) *
          ZMod.stdAddChar (ξ * ValuationWord.residueOffset n w.reverse) := by
  rw [Reference.fourierMass]
  simp only [Reference.mass, Reference.law_reverse_atom]
  have htoReal (x : ZMod (3 ^ n)) :
      ((∑' w : ValuationWord,
        if ValuationWord.residueOffset n w.reverse = x then
          Reference.wordPMF n w else 0).toReal : ℂ) =
        ∑' w : ValuationWord,
          ((if ValuationWord.residueOffset n w.reverse = x then
            Reference.wordPMF n w else 0).toReal : ℂ) := by
    rw [ENNReal.tsum_toReal_eq]
    · rw [Complex.ofReal_tsum]
    · intro w
      split_ifs <;> simp [PMF.apply_ne_top]
  simp_rw [htoReal]
  simp_rw [← tsum_mul_right]
  rw [← Summable.tsum_finsetSum
    (s := (Finset.univ : Finset (ZMod (3 ^ n))))
    (f := fun x w =>
      (((if ValuationWord.residueOffset n w.reverse = x then
        Reference.wordPMF n w else 0).toReal : ℂ) * ZMod.stdAddChar (ξ * x)))
    (fun x _ => reversedCharacterFiber_summable n ξ x)]
  apply tsum_congr
  intro w
  rw [Finset.sum_eq_single (ValuationWord.residueOffset n w.reverse)]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

/-- Reversal invariance of the iid word law gives the forward ordered-word
form of the exact Fourier expectation. -/
theorem fourierMass_eq_word_character_expectation (n : ℕ) (ξ : ZMod (3 ^ n)) :
    Reference.fourierMass n ξ =
      ∑' w : ValuationWord,
        ((Reference.wordPMF n w).toReal : ℂ) *
          ZMod.stdAddChar (ξ * ValuationWord.residueOffset n w) := by
  rw [fourierMass_eq_reversed_word_character_expectation]
  rw [← valuationWordReverseEquiv.tsum_eq]
  apply tsum_congr
  intro w
  change ((Reference.wordPMF n w.reverse).toReal : ℂ) *
      ZMod.stdAddChar (ξ * ValuationWord.residueOffset n w.reverse.reverse) = _
  rw [Reference.wordPMF_reverse_apply, List.reverse_reverse]

/-- At an even conductor, the exact Fourier expectation is the forward ordered
pair-character expectation with initial state `(0,0)`. -/
theorem fourierMass_even_eq_forwardCharacterExpectation (h : ℕ)
    (ξ : ZMod (3 ^ (2 * h))) :
    Reference.fourierMass (2 * h) ξ =
      forwardCharacterExpectation (2 * h) ξ h 0 0 := by
  rw [fourierMass_eq_word_character_expectation]
  unfold forwardCharacterExpectation
  apply tsum_congr
  intro w
  by_cases hw : w.length = 2 * h
  · rw [forwardCharacterProduct_even_eq_character (2 * h) ξ h 0 0 w hw]
    simp
  · have hzero : (Reference.wordPMF (2 * h) w).toReal = 0 := by
      rw [Reference.wordPMF_eq_zero_of_length_ne (2 * h) w hw]
      rfl
    rw [hzero]
    simp

/-- The exact even-conductor Fourier mass is bounded by the literal forward
phase potential at its initial pair state. -/
theorem norm_fourierMass_even_le_phasePairPotential (h : ℕ)
    (ξ : ZMod (3 ^ (2 * h))) :
    ‖Reference.fourierMass (2 * h) ξ‖ ≤
      phasePairPotential (2 * h) ξ h 0 0 := by
  rw [fourierMass_even_eq_forwardCharacterExpectation]
  exact norm_forwardCharacterExpectation_le_phasePairPotential (2 * h) h 0 0 ξ

/-- At an odd conductor, the forward pair expectation retains the one-letter
terminal character required by the exact Fourier identity. -/
theorem fourierMass_odd_eq_forwardCharacterExpectation (h : ℕ)
    (ξ : ZMod (3 ^ (2 * h + 1))) :
    Reference.fourierMass (2 * h + 1) ξ =
      ∑' w : ValuationWord,
        ((Reference.wordPMF (2 * h + 1) w).toReal : ℂ) *
          (forwardCharacterProduct (2 * h + 1) ξ h 0 0 w *
            ZMod.stdAddChar
              (ξ * (3 : ZMod (3 ^ (2 * h + 1))) ^ (2 * h) *
                Reference.inverseTwoPow (2 * h + 1)
                  (ValuationWord.total (w.take (2 * h))) *
                ValuationWord.residueOffset (2 * h + 1) (w.drop (2 * h)))) := by
  rw [fourierMass_eq_word_character_expectation]
  apply tsum_congr
  intro w
  by_cases hw : w.length = 2 * h + 1
  · have hchar :
        forwardCharacterProduct (2 * h + 1) ξ h 0 0 w *
          ZMod.stdAddChar
            (ξ * (3 : ZMod (3 ^ (2 * h + 1))) ^ (2 * h) *
              Reference.inverseTwoPow (2 * h + 1)
                (ValuationWord.total (w.take (2 * h))) *
              ValuationWord.residueOffset (2 * h + 1) (w.drop (2 * h))) =
          ZMod.stdAddChar (ξ * ValuationWord.residueOffset (2 * h + 1) w) := by
      simpa using
        (forwardCharacterProduct_odd_with_terminal (2 * h + 1) ξ h 0 0 w hw)
    rw [← hchar]
  · have hzero : (Reference.wordPMF (2 * h + 1) w).toReal = 0 := by
      rw [Reference.wordPMF_eq_zero_of_length_ne (2 * h + 1) w hw]
      rfl
    rw [hzero]
    simp

/- The full-character expectation retains any terminal letters. Its pair
recurrence therefore handles both parities without deleting a random factor. -/
private noncomputable def forwardResidueExpectation (n : ℕ) (ξ : ZMod (3 ^ n))
    (k j l : ℕ) : ℂ :=
  ∑' w : ValuationWord, ((Reference.wordPMF k w).toReal : ℂ) *
    ZMod.stdAddChar (ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) *
      Reference.inverseTwoPow n l * ValuationWord.residueOffset n w)

private theorem norm_forwardResidueExpectation_le_one (n : ℕ) (ξ : ZMod (3 ^ n))
    (k j l : ℕ) : ‖forwardResidueExpectation n ξ k j l‖ ≤ 1 := by
  have hs : Summable (fun w : ValuationWord =>
      ((Reference.wordPMF k w).toReal : ℂ) *
        ZMod.stdAddChar (ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) *
          Reference.inverseTwoPow n l * ValuationWord.residueOffset n w)) := by
    refine Summable.of_norm_bounded (wordWeights_summable k) ?_
    intro w
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, AddChar.norm_apply, mul_one, le_refl]
  unfold forwardResidueExpectation
  calc
    _ ≤ ∑' w : ValuationWord, (Reference.wordPMF k w).toReal := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ENNReal.toReal_nonneg, AddChar.norm_apply, mul_one] using
        norm_tsum_le_tsum_norm hs.norm
    _ = 1 := by
      rw [← ENNReal.tsum_toReal_eq (fun w => PMF.apply_ne_top _ w), PMF.tsum_coe]
      rfl

private theorem forwardResidueCharacter_append_pair (n j l : ℕ)
    (ξ : ZMod (3 ^ n)) (u v : ValuationWord) (hu : u.length = 2) :
    ZMod.stdAddChar (ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) *
      Reference.inverseTwoPow n l * ValuationWord.residueOffset n (u ++ v)) =
    ZMod.stdAddChar (ξ * forwardPairOffset n j l u) *
      ZMod.stdAddChar (ξ * (3 : ZMod (3 ^ n)) ^ (2 * (j + 1)) *
        Reference.inverseTwoPow n (l + u.total) * ValuationWord.residueOffset n v) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  unfold forwardPairOffset
  rw [List.take_of_length_le hu.le, ValuationWord.residueOffset_append, hu,
    show 2 * (j + 1) = 2 * j + 2 by omega, pow_add, Reference.inverseTwoPow_add]
  ring

private theorem forwardResidueExpectation_add_two (n k j l : ℕ)
    (ξ : ZMod (3 ^ n)) :
    forwardResidueExpectation n ξ (2 + k) j l =
      ∑' u : ValuationWord, ((Reference.wordPMF 2 u).toReal : ℂ) *
        ZMod.stdAddChar (ξ * forwardPairOffset n j l u) *
          forwardResidueExpectation n ξ k (j + 1) (l + u.total) := by
  unfold forwardResidueExpectation
  rw [← Reference.wordPMF_append, complexPMFBind_tsum]
  · apply tsum_congr
    intro u
    rw [complexPMFMap_tsum]
    · by_cases hu : u.length = 2
      · simp_rw [forwardResidueCharacter_append_pair n j l ξ u _ hu]
        conv_rhs => rw [mul_assoc]
        congr 1
        rw [← tsum_mul_left]
        apply tsum_congr
        intro v
        ring
      · simp only [Reference.wordPMF_eq_zero_of_length_ne 2 u hu,
          ENNReal.toReal_zero, Complex.ofReal_zero, zero_mul]
    · intro w
      exact le_of_eq (AddChar.norm_apply _ _)
  · intro w
    exact le_of_eq (AddChar.norm_apply _ _)

private theorem forwardResidueExpectation_add_two_eq_pairMass (n k j l : ℕ)
    (ξ : ZMod (3 ^ n)) :
    forwardResidueExpectation n ξ (2 + k) j l =
      ∑' b : {b : ℕ // 2 ≤ b},
        (Reference.pairMass b.1 : ℂ) * forwardPairFactor n j l b.1 ξ *
          forwardResidueExpectation n ξ k (j + 1) (l + b.1) := by
  let f : ValuationWord → ℂ := fun u =>
    ((Reference.wordPMF 2 u).toReal : ℂ) *
      ZMod.stdAddChar (ξ * forwardPairOffset n j l u) *
      forwardResidueExpectation n ξ k (j + 1) (l + u.total)
  have hf : Summable f := by
    refine Summable.of_norm_bounded (wordWeights_summable 2) ?_
    intro u
    dsimp [f]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, AddChar.norm_apply, mul_one]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg
      (norm_forwardResidueExpectation_le_one n ξ k (j + 1) (l + u.total))
  rw [forwardResidueExpectation_add_two, Reference.tsum_eq_tsum_pairIndex f]
  · have hfi : Summable (f ∘ Reference.pairIndexWord) :=
      hf.comp_injective Reference.pairIndexWord_injective
    change (∑' p : (b : {b : ℕ // 2 ≤ b}) × Fin (b.1 - 1),
      (f ∘ Reference.pairIndexWord) p) = _
    rw [hfi.tsum_sigma]
    apply tsum_congr
    intro b
    rw [tsum_fintype]
    change (∑ i : Fin (b.1 - 1),
      ((Reference.wordPMF 2 (Reference.pairWord b.1 i)).toReal : ℂ) *
        ZMod.stdAddChar (ξ * forwardPairOffset n j l (Reference.pairWord b.1 i)) *
        forwardResidueExpectation n ξ k (j + 1)
          (l + (Reference.pairWord b.1 i).total)) = _
    simp_rw [Reference.pairWord_total b.2]
    rw [← Finset.sum_mul]
    change Reference.pairWeightedSum b.1 (fun i =>
      ZMod.stdAddChar (ξ * forwardPairOffset n j l (Reference.pairWord b.1 i))) *
        forwardResidueExpectation n ξ k (j + 1) (l + b.1) = _
    rw [show (fun i => ZMod.stdAddChar
      (ξ * forwardPairOffset n j l (Reference.pairWord b.1 i))) =
        pairCharacter n j l b.1 ξ by
      funext i
      rw [forwardPairOffset_pairWord ξ b.2 i]
      rfl]
    rw [pairWeightedCharacter_eq n j l b.2 ξ]
    rfl
  · intro u hu
    unfold f
    rw [Reference.wordPMF_eq_zero_of_length_ne 2 u hu, ENNReal.toReal_zero,
      Complex.ofReal_zero, zero_mul, zero_mul]


private theorem norm_forwardResidueExpectation_pairs_le_phasePairPotential
    (n t h j l : ℕ) (ξ : ZMod (3 ^ n)) :
    ‖forwardResidueExpectation n ξ (2 * h + t) j l‖ ≤
      phasePairPotential n ξ h j (l : ℤ) := by
  apply norm_forwardRecurrence_le_phasePairPotential n ξ
    (fun h j l => forwardResidueExpectation n ξ (2 * h + t) j l)
  · intro h j l
    exact norm_forwardResidueExpectation_le_one n ξ _ j l
  · intro h j l
    rw [show 2 * (h + 1) + t = 2 + (2 * h + t) by omega]
    exact forwardResidueExpectation_add_two_eq_pairMass n (2 * h + t) j l ξ

/-- The odd-conductor bound retains the last letter in the original-law
continuation. Its unit norm supplies the induction's terminal bound. -/
theorem norm_fourierMass_odd_le_phasePairPotential (h : ℕ)
    (ξ : ZMod (3 ^ (2 * h + 1))) :
    ‖Reference.fourierMass (2 * h + 1) ξ‖ ≤
      phasePairPotential (2 * h + 1) ξ h 0 0 := by
  have heq : Reference.fourierMass (2 * h + 1) ξ =
      forwardResidueExpectation (2 * h + 1) ξ (2 * h + 1) 0 0 := by
    rw [fourierMass_eq_word_character_expectation]
    simp [forwardResidueExpectation]
  rw [heq]
  exact norm_forwardResidueExpectation_pairs_le_phasePairPotential
    (2 * h + 1) 1 h 0 0 ξ

/-- Both conductor parities satisfy the literal Appendix-E finite-horizon bound. -/
theorem norm_fourierMass_le_phasePairPotential (n : ℕ) (ξ : ZMod (3 ^ n)) :
    ‖Reference.fourierMass n ξ‖ ≤ phasePairPotential n ξ (n / 2) 0 0 := by
  have heq : Reference.fourierMass n ξ = forwardResidueExpectation n ξ n 0 0 := by
    rw [fourierMass_eq_word_character_expectation]
    simp [forwardResidueExpectation]
  rw [heq]
  have h := norm_forwardResidueExpectation_pairs_le_phasePairPotential
    n (n % 2) (n / 2) 0 0 ξ
  simpa only [Nat.div_add_mod, Nat.cast_zero] using h

end WordCertDensity.LocalPrimitive
