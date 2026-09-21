/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.IntegerPotential
public import WordCertDensity.Analytic.LocalPrimitive.LayerInduction

/-! # Remaining-distance bridge for the E-L5 layer induction

The E.7 maximum is indexed by remaining distance, while the literal pair
potential is indexed by its initial column.  This module records the exact
change of coordinates.  It contains no stopped-exit or post-exit estimate.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

private theorem layerBridge_pairWordWeights_summable :
    Summable (fun w : ValuationWord => (Reference.wordPMF 2 w).toReal) :=
  ENNReal.summable_toReal (by
    rw [PMF.tsum_coe]
    exact ENNReal.one_ne_top)

private theorem layerBridge_discount_nonneg {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : Prop) (w : ValuationWord) : 0 ≤ pairDiscount ε white w := by
  unfold pairDiscount
  split_ifs <;> linarith

private theorem layerBridge_discount_le_one (ε : ℝ) (white : Prop)
    (w : ValuationWord) : pairDiscount ε white w ≤ 1 := by
  unfold pairDiscount
  split_ifs <;> nlinarith [sq_nonneg ε]

private theorem layerBridge_kernel_summable {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : Prop) :
    Summable (fun w : ValuationWord =>
      (Reference.wordPMF 2 w).toReal * pairDiscount ε white w) := by
  refine Summable.of_norm_bounded layerBridge_pairWordWeights_summable ?_
  intro w
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      (Reference.wordPMF 2 w).toReal * pairDiscount ε white w ≤
          (Reference.wordPMF 2 w).toReal * 1 := by
        exact mul_le_mul_of_nonneg_left
          (layerBridge_discount_le_one ε white w) ENNReal.toReal_nonneg
      _ = (Reference.wordPMF 2 w).toReal := by ring
  · exact mul_nonneg ENNReal.toReal_nonneg (layerBridge_discount_nonneg hε white w)

/-- The literal phase potential at column `N-r`, with `r` remaining pair steps. -/
noncomputable def phaseRemainingPotential (n : ℕ) (ξ : ZMod (3 ^ n))
    (N r : ℕ) (l : ℤ) : ℝ :=
  phasePairPotential n ξ r (N - r) l

/-- At zero remaining distance the potential has its literal terminal value. -/
theorem phaseRemainingPotential_zero (n N : ℕ) (ξ : ZMod (3 ^ n)) (l : ℤ) :
    phaseRemainingPotential n ξ N 0 l = 1 := by
  exact phasePairPotential_zero n ξ N l

/-- The remaining-distance potential stays in the unit interval. -/
theorem phaseRemainingPotential_mem_unitInterval (n N r : ℕ) (ξ : ZMod (3 ^ n))
    (l : ℤ) :
    0 ≤ phaseRemainingPotential n ξ N r l ∧ phaseRemainingPotential n ξ N r l ≤ 1 :=
  phasePairPotential_mem_unitInterval n ξ r (N - r) l

/-- The original finite phase period survives the change to remaining distance. -/
theorem phaseRemainingPotential_phasePeriod {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (N r : ℕ) :
    Function.Periodic (phaseRemainingPotential n ξ N r)
      (2 * 3 ^ (n - 1) : ℤ) :=
  phasePairPotential_phasePeriod hn ξ r (N - r)

/-- The one-step recursion becomes a recursion from `r + 1` to `r` as long
as the starting column is before the terminal column. -/
theorem phaseRemainingPotential_succ (n N r : ℕ) (ξ : ZMod (3 ^ n)) (l : ℤ)
    (hr : r < N) :
    phaseRemainingPotential n ξ N (r + 1) l =
      ∑' w : ValuationWord,
        (Reference.wordPMF 2 w).toReal *
          pairDiscount localEpsilon (phaseWhiteAtInt n ξ (N - (r + 1)) l) w *
            phaseRemainingPotential n ξ N r (l + w.total) := by
  unfold phaseRemainingPotential
  unfold phasePairPotential
  rw [integerPairPotential_succ]
  congr 1
  funext w
  have hcolumn : N - (r + 1) + 1 = N - r := by omega
  rw [hcolumn]

private theorem layerBridge_discountedPotential_summable {n N r : ℕ}
    (ξ : ZMod (3 ^ n)) (l : ℤ) :
    Summable (fun w : ValuationWord =>
      (Reference.wordPMF 2 w).toReal *
        pairDiscount localEpsilon (phaseWhiteAtInt n ξ (N - (r + 1)) l) w *
          phaseRemainingPotential n ξ N r (l + w.total)) := by
  refine Summable.of_norm_bounded layerBridge_pairWordWeights_summable ?_
  intro w
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      (Reference.wordPMF 2 w).toReal *
          pairDiscount localEpsilon (phaseWhiteAtInt n ξ (N - (r + 1)) l) w *
          phaseRemainingPotential n ξ N r (l + w.total) ≤
          (Reference.wordPMF 2 w).toReal * 1 * 1 := by
        calc
          _ ≤ (Reference.wordPMF 2 w).toReal * 1 *
              phaseRemainingPotential n ξ N r (l + w.total) := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left
                (layerBridge_discount_le_one localEpsilon
                  (phaseWhiteAtInt n ξ (N - (r + 1)) l) w) ENNReal.toReal_nonneg
            · exact (phaseRemainingPotential_mem_unitInterval n N r ξ (l + w.total)).1
          _ ≤ (Reference.wordPMF 2 w).toReal * 1 * 1 := by
            exact mul_le_mul_of_nonneg_left
              (phaseRemainingPotential_mem_unitInterval n N r ξ (l + w.total)).2
              (mul_nonneg ENNReal.toReal_nonneg zero_le_one)
      _ = (Reference.wordPMF 2 w).toReal := by ring
  · exact mul_nonneg
      (mul_nonneg ENNReal.toReal_nonneg
        (layerBridge_discount_nonneg localEpsilon_guard
          (phaseWhiteAtInt n ξ (N - (r + 1)) l) w))
      (phaseRemainingPotential_mem_unitInterval n N r ξ (l + w.total)).1

/-- At a white state, the original pair potential contracts by the exact
discounted kernel mass once every next state is bounded by the same value. -/
theorem phaseRemainingPotential_white_step_le (n N r : ℕ) (ξ : ZMod (3 ^ n))
    (l : ℤ) (hr : r < N) (D : ℝ)
    (hfuture : ∀ l', phaseRemainingPotential n ξ N r l' ≤ D)
    (hwhite : phaseWhiteAtInt n ξ (N - (r + 1)) l) :
    phaseRemainingPotential n ξ N (r + 1) l ≤ (1 - pairLoss localEpsilon) * D := by
  rw [phaseRemainingPotential_succ n N r ξ l hr]
  calc
    _ ≤ ∑' w : ValuationWord,
        (Reference.wordPMF 2 w).toReal *
          pairDiscount localEpsilon (phaseWhiteAtInt n ξ (N - (r + 1)) l) w * D := by
      apply Summable.tsum_le_tsum
      · intro w
        exact mul_le_mul_of_nonneg_left (hfuture (l + w.total))
          (mul_nonneg ENNReal.toReal_nonneg
            (layerBridge_discount_nonneg localEpsilon_guard
              (phaseWhiteAtInt n ξ (N - (r + 1)) l) w))
      · exact layerBridge_discountedPotential_summable (n := n) (N := N) (r := r) ξ l
      · exact (layerBridge_kernel_summable localEpsilon_guard
          (phaseWhiteAtInt n ξ (N - (r + 1)) l)).mul_right D
    _ = (∑' w : ValuationWord,
        (Reference.wordPMF 2 w).toReal *
          pairDiscount localEpsilon (phaseWhiteAtInt n ξ (N - (r + 1)) l) w) * D := by
      rw [← tsum_mul_right]
    _ = _ := by rw [phaseWhite_pairKernel_mass n ξ (N - (r + 1)) l hwhite]

/-- The exact white-kernel contraction in the weighted form consumed by E.7.
The later finite-residue adapter only has to transport its future-layer bound. -/
theorem phaseRemainingPotential_white_weighted_le (B n N m : ℕ)
    (ξ : ZMod (3 ^ n)) (l : ℤ) (hm : 0 < m) (hmN : m ≤ N) (D : ℝ)
    (hfuture : ∀ l', layerWeight B (m - 1) *
      phaseRemainingPotential n ξ N (m - 1) l' ≤ D)
    (hwhite : phaseWhiteAtInt n ξ (N - m) l) :
    phaseRemainingPotential n ξ N m l ≤
      (1 - pairLoss localEpsilon) * D / layerWeight B (m - 1) := by
  have hweight : 0 < layerWeight B (m - 1) := layerWeight_pos B (m - 1)
  have hr : m - 1 < N := by omega
  have hmsucc : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  have hfuture' : ∀ l', phaseRemainingPotential n ξ N (m - 1) l' ≤
      D / layerWeight B (m - 1) := by
    intro l'
    apply (le_div_iff₀ hweight).mpr
    simpa [mul_comm] using hfuture l'
  have hstep := phaseRemainingPotential_white_step_le n N (m - 1) ξ l hr
    (D / layerWeight B (m - 1)) hfuture' (by simpa only [hmsucc] using hwhite)
  simpa only [hmsucc, mul_div_assoc] using hstep

/-- Transport the literal white-kernel bound to the finite residue field used
by the layer maximum.  Periodicity is an explicit input: this theorem does
not identify integer heights with residues by definition. -/
theorem phaseRemainingPotential_residue_white_weighted_le {P B n N m : ℕ}
    (ξ : ZMod (3 ^ n))
    (hperiod : ∀ r, Function.Periodic
      (phaseRemainingPotential n ξ N r) (P + 1 : ℕ))
    (white : ℕ → Fin (P + 1) → Prop)
    (hwhite : ∀ l : ℤ, white m (layerHeightResidue P l) →
      phaseWhiteAtInt n ξ (N - m) l)
    (hm : 0 < m) (hmN : m ≤ N) (D : ℝ)
    (hfuture : ∀ r, r < m → ∀ a,
      layerWeight B r * residuePotential P
        (phaseRemainingPotential n ξ N) r a ≤ D) :
    ∀ a, white m a → residuePotential P
      (phaseRemainingPotential n ξ N) m a ≤
        (1 - pairLoss localEpsilon) * D / layerWeight B (m - 1) := by
  intro a ha
  let l : ℤ := a
  have hres : layerHeightResidue P l = a := by
    apply Fin.ext
    change ((↑(a : ℕ) : ℤ) % (P + 1 : ℕ)).toNat = a
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    simp
  have hfutureInt : ∀ l' : ℤ, layerWeight B (m - 1) *
      phaseRemainingPotential n ξ N (m - 1) l' ≤ D := by
    intro l'
    rw [← residuePotential_eq (phaseRemainingPotential n ξ N) hperiod (m - 1) l']
    exact hfuture (m - 1) (by omega) _
  have hkernel := phaseRemainingPotential_white_weighted_le B n N m ξ l hm hmN D
    hfutureInt (hwhite l (by simpa only [hres] using ha))
  rw [← hres]
  rw [residuePotential_eq (phaseRemainingPotential n ξ N) hperiod m l]
  exact hkernel

end WordCertDensity.LocalPrimitive
