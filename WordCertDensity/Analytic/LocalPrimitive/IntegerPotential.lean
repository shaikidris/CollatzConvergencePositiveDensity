/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.Geometry
import Mathlib.Data.Nat.Totient
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! # Integer-height original pair potential for Appendix E

This is the literal pair-sum law of E.kill, with its valuation coordinate in
`Int`. It is deliberately separate from the finite-residue layer induction:
the latter consumes a proved periodicity witness instead of treating the
period as definitional.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

private theorem integerPairWordWeights_summable :
    Summable (fun w : ValuationWord => (Reference.wordPMF 2 w).toReal) :=
  ENNReal.summable_toReal (by
    rw [PMF.tsum_coe]
    exact ENNReal.one_ne_top)

private theorem integerPairDiscount_nonneg {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : Prop) (w : ValuationWord) : 0 ≤ pairDiscount ε white w := by
  unfold pairDiscount
  split_ifs <;> linarith

private theorem integerPairDiscount_le_one (ε : ℝ) (white : Prop)
    (w : ValuationWord) : pairDiscount ε white w ≤ 1 := by
  unfold pairDiscount
  split_ifs
  · nlinarith [sq_nonneg ε]
  · exact le_rfl

private theorem integerDiscountedRow_summable {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : Prop) (V : ValuationWord → ℝ) (hV0 : ∀ w, 0 ≤ V w)
    (hV1 : ∀ w, V w ≤ 1) :
    Summable (fun w : ValuationWord =>
      (Reference.wordPMF 2 w).toReal * pairDiscount ε white w * V w) := by
  refine Summable.of_norm_bounded integerPairWordWeights_summable ?_
  intro w
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      (Reference.wordPMF 2 w).toReal * pairDiscount ε white w * V w
          ≤ (Reference.wordPMF 2 w).toReal * 1 * 1 := by
            calc
              _ ≤ (Reference.wordPMF 2 w).toReal * 1 * V w := by
                apply mul_le_mul_of_nonneg_right
                · exact mul_le_mul_of_nonneg_left
                    (integerPairDiscount_le_one ε white w) ENNReal.toReal_nonneg
                · exact hV0 w
              _ ≤ (Reference.wordPMF 2 w).toReal * 1 * 1 := by
                apply mul_le_mul_of_nonneg_left (hV1 w)
                positivity
      _ = (Reference.wordPMF 2 w).toReal := by ring
  · exact mul_nonneg
      (mul_nonneg ENNReal.toReal_nonneg (integerPairDiscount_nonneg hε white w))
      (hV0 w)

/-- E.kill's finite-horizon pair potential at an integer valuation height. -/
noncomputable def integerPairPotential (ε : ℝ) (white : ℕ → ℤ → Prop) :
    ℕ → ℕ → ℤ → ℝ
  | 0, _, _ => 1
  | h + 1, j, l =>
      ∑' w : ValuationWord,
        (Reference.wordPMF 2 w).toReal * pairDiscount ε (white j l) w *
          integerPairPotential ε white h (j + 1) (l + w.total)

/-- The defining one-step recursion, stated separately for E-L5 consumers. -/
theorem integerPairPotential_succ (ε : ℝ) (white : ℕ → ℤ → Prop)
    (h j : ℕ) (l : ℤ) :
    integerPairPotential ε white (h + 1) j l =
      ∑' w : ValuationWord,
        (Reference.wordPMF 2 w).toReal * pairDiscount ε (white j l) w *
          integerPairPotential ε white h (j + 1) (l + w.total) := rfl

/-- The original potential is nonnegative. -/
theorem integerPairPotential_nonneg {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : ℕ → ℤ → Prop) : ∀ h j l, 0 ≤ integerPairPotential ε white h j l := by
  intro h
  induction h with
  | zero => simp [integerPairPotential]
  | succ h ih =>
      intro j l
      rw [integerPairPotential_succ]
      exact tsum_nonneg fun w => mul_nonneg
        (mul_nonneg ENNReal.toReal_nonneg
          (integerPairDiscount_nonneg hε (white j l) w))
        (ih (j + 1) (l + w.total))

/-- The original potential never exceeds one. -/
theorem integerPairPotential_le_one {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : ℕ → ℤ → Prop) : ∀ h j l, integerPairPotential ε white h j l ≤ 1 := by
  intro h
  induction h with
  | zero => simp [integerPairPotential]
  | succ h ih =>
      intro j l
      rw [integerPairPotential_succ]
      calc
        _ ≤ ∑' w : ValuationWord, (Reference.wordPMF 2 w).toReal := by
          apply Summable.tsum_le_tsum
          · intro w
            calc
              (Reference.wordPMF 2 w).toReal * pairDiscount ε (white j l) w *
                    integerPairPotential ε white h (j + 1) (l + w.total)
                  ≤ (Reference.wordPMF 2 w).toReal * 1 * 1 := by
                    calc
                      _ ≤ (Reference.wordPMF 2 w).toReal * 1 *
                          integerPairPotential ε white h (j + 1) (l + w.total) := by
                            apply mul_le_mul_of_nonneg_right
                            · exact mul_le_mul_of_nonneg_left
                                (integerPairDiscount_le_one ε (white j l) w)
                                ENNReal.toReal_nonneg
                            · exact integerPairPotential_nonneg hε white h (j + 1)
                                (l + w.total)
                      _ ≤ (Reference.wordPMF 2 w).toReal * 1 * 1 := by
                            apply mul_le_mul_of_nonneg_left (ih (j + 1) (l + w.total))
                            positivity
              _ = (Reference.wordPMF 2 w).toReal := by ring
          · exact integerDiscountedRow_summable hε (white j l) _
              (fun w => integerPairPotential_nonneg hε white h (j + 1) (l + w.total))
              (fun w => ih (j + 1) (l + w.total))
          · exact integerPairWordWeights_summable
        _ = 1 := pairWordWeights_tsum_eq_one

/-- A period of the state predicate is a period of the original potential. -/
theorem integerPairPotential_periodic {ε : ℝ} {white : ℕ → ℤ → Prop}
    {q : ℤ} (hwhite : ∀ j, Function.Periodic (white j) q) :
    ∀ h j, Function.Periodic (integerPairPotential ε white h j) q := by
  intro h
  induction h with
  | zero =>
      intro j l
      simp [integerPairPotential]
  | succ h ih =>
      intro j l
      rw [integerPairPotential_succ, integerPairPotential_succ]
      apply tsum_congr
      intro w
      rw [hwhite j l]
      have hp := ih (j + 1) (l + w.total)
      convert congrArg (fun x =>
        (Reference.wordPMF 2 w).toReal * pairDiscount ε (white j l) w * x) hp using 1
      ring

/-- The geometric white predicate appearing in E.phase/E.kill. -/
def phaseWhiteAtInt (n : ℕ) (ξ : ZMod (3 ^ n)) (j : ℕ) (l : ℤ) : Prop :=
  ¬ phaseBlackAtInt n ξ j l

/-- The inverse-two unit has the Euler period used by the phase coordinate. -/
private theorem twoUnit_inv_pow_phasePeriod (n : ℕ) (hn : 0 < n) :
    ((Reference.twoUnit n)⁻¹ : (ZMod (3 ^ n))ˣ) ^ (2 * 3 ^ (n - 1)) = 1 := by
  have hcard : Fintype.card (ZMod (3 ^ n))ˣ = 2 * 3 ^ (n - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_three hn]
    ring
  rw [← hcard]
  exact pow_card_eq_one

/-- For positive conductor level, integer-height phase residues have the
finite period `2 * 3^(n-1)` prescribed by the unit group. -/
theorem phaseResidueInt_periodic {n : ℕ} (hn : 0 < n) (j : ℕ)
    (ξ : ZMod (3 ^ n)) :
    Function.Periodic (fun l : ℤ => phaseResidueInt n j l ξ)
      (2 * 3 ^ (n - 1) : ℤ) := by
  intro l
  let q : ℕ := 2 * 3 ^ (n - 1)
  let u : (ZMod (3 ^ n))ˣ := (Reference.twoUnit n)⁻¹
  have hu : u ^ q = 1 := twoUnit_inv_pow_phasePeriod n hn
  unfold phaseResidueInt
  change ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) * ↑(u ^ (l + (q : ℤ) + 2)) =
    ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) * ↑(u ^ (l + 2))
  rw [show l + (q : ℤ) + 2 = (l + 2) + (q : ℤ) by ring]
  rw [zpow_add, zpow_natCast, hu, Units.val_mul]
  simp

/-- The phase-black predicate, and hence its white complement, is periodic
at the finite unit-group period. -/
theorem phaseWhiteAtInt_periodic {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n)) :
    ∀ j, Function.Periodic (phaseWhiteAtInt n ξ j) (2 * 3 ^ (n - 1) : ℤ) := by
  intro j l
  have hres : phaseResidueInt n j (l + (2 * 3 ^ (n - 1) : ℤ)) ξ =
      phaseResidueInt n j l ξ :=
    phaseResidueInt_periodic hn j ξ l
  simp only [phaseWhiteAtInt, phaseBlackAtInt, balancedPhaseInt, hres]

/-- Appendix E's literal potential with phase-geometric white states. -/
noncomputable def phasePairPotential (n : ℕ) (ξ : ZMod (3 ^ n)) :
    ℕ → ℕ → ℤ → ℝ :=
  integerPairPotential localEpsilon (phaseWhiteAtInt n ξ)

/-- At every phase-white state, the original pair kernel loses exactly d. -/
theorem phaseWhite_pairKernel_mass (n : ℕ) (ξ : ZMod (3 ^ n)) (j : ℕ) (l : ℤ)
    (hwhite : phaseWhiteAtInt n ξ j l) :
    (∑' w : ValuationWord,
      (Reference.wordPMF 2 w).toReal *
        pairDiscount localEpsilon (phaseWhiteAtInt n ξ j l) w) =
        1 - pairLoss localEpsilon :=
  white_pairKernel_mass (phaseWhiteAtInt n ξ j l) hwhite

/-- The geometric original potential has the terminal value required by E.7. -/
theorem phasePairPotential_zero (n : ℕ) (ξ : ZMod (3 ^ n)) (j : ℕ) (l : ℤ) :
    phasePairPotential n ξ 0 j l = 1 := rfl

/-- Once the phase predicate is shown periodic at a positive integer period,
the literal E.kill potential has that same finite state reduction. The
specific period `2 * 3^(n-1)` is a separate order-of-two producer; this
theorem makes that missing number-theory input explicit. -/
theorem phasePairPotential_periodic {n : ℕ} {ξ : ZMod (3 ^ n)} {q : ℤ}
    (hphase : ∀ j, Function.Periodic (phaseWhiteAtInt n ξ j) q) :
    ∀ h j, Function.Periodic (phasePairPotential n ξ h j) q :=
  integerPairPotential_periodic hphase

/-- The literal phase potential therefore reduces to the finite height state
space of period `2 * 3^(n-1)` at every positive conductor level. -/
theorem phasePairPotential_phasePeriod {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) :
    ∀ h j, Function.Periodic (phasePairPotential n ξ h j)
      (2 * 3 ^ (n - 1) : ℤ) :=
  phasePairPotential_periodic (phaseWhiteAtInt_periodic hn ξ)

/-- The geometric original potential is in the unit interval. -/
theorem phasePairPotential_mem_unitInterval (n : ℕ) (ξ : ZMod (3 ^ n))
    (h j : ℕ) (l : ℤ) :
    0 ≤ phasePairPotential n ξ h j l ∧ phasePairPotential n ξ h j l ≤ 1 :=
  ⟨integerPairPotential_nonneg localEpsilon_guard _ _ _ _,
    integerPairPotential_le_one localEpsilon_guard _ _ _ _⟩

end WordCertDensity.LocalPrimitive
