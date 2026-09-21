/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PassageLaw
public import WordCertDensity.Probability.FiniteUnion
import Mathlib.Tactic

/-! # Exact expectation bounds on the original first-passage law -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- Split a nonnegative real expectation over an event while retaining the
original PMF atoms.  No conditional or survivor-normalized law is introduced. -/
theorem pmf_expectation_le_event_split {α : Type*} (p : PMF α) (W : α → Prop)
    (f : α → ℝ) (cw cb : ℝ) (hcw : 0 ≤ cw) (hcb : 0 ≤ cb) (hf : ∀ x, 0 ≤ f x)
    (hw : ∀ x, W x → f x ≤ cw) (hb : ∀ x, ¬ W x → f x ≤ cb) :
    (∑' x, (p x).toReal * f x) ≤
      cw * Gated.probability p W + cb * (1 - Gated.probability p W) := by
  have hnative :
      (∑' x, p x * ENNReal.ofReal (f x)) ≤
        ENNReal.ofReal cw * (∑' x, if W x then p x else 0) +
          ENNReal.ofReal cb * (∑' x,
            @ite ℝ≥0∞ (¬ W x) (Classical.propDecidable _) (p x) 0) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro x
    by_cases hx : W x
    · simpa only [hx, if_true, not_true_eq_false, if_false, mul_zero, add_zero, mul_comm]
        using mul_le_mul_left (ENNReal.ofReal_le_ofReal (hw x hx)) (p x)
    · simpa only [hx, if_false, not_false_eq_true, if_true, mul_zero, zero_add, mul_comm]
        using mul_le_mul_left (ENNReal.ofReal_le_ofReal (hb x hx)) (p x)
  have hr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Gated.event_ne_top p W),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Gated.event_ne_top p (fun x => ¬ W x))⟩)
    hnative
  rw [ENNReal.tsum_toReal_eq (fun x =>
    ENNReal.mul_ne_top (PMF.apply_ne_top p x) ENNReal.ofReal_ne_top)] at hr
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf _)] at hr
  rw [ENNReal.toReal_add,
    ENNReal.toReal_mul, ENNReal.toReal_mul] at hr
  rotate_left
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Gated.event_ne_top p W)
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (Gated.event_ne_top p (fun x => ¬ W x))
  change _ ≤ ENNReal.toReal (ENNReal.ofReal cw) * Gated.probability p W +
    ENNReal.toReal (ENNReal.ofReal cb) *
      Gated.probability p (fun x => ¬ W x) at hr
  rw [Gated.probability_compl] at hr
  simpa only [ENNReal.toReal_ofReal hcw, ENNReal.toReal_ofReal hcb] using hr

/-- The native stopped-potential bound converted to an expectation under the
exact first-passage PMF. -/
theorem integerPairPotential_passage_expectation_le {ε : ℝ}
    (hε : 2 * ε ^ 2 ≤ 1) (white : ℕ → ℤ → Prop) (s m j : ℕ) (l : ℤ)
    (hm : s / 2 + 1 ≤ m) :
    integerPairPotential ε white m j l ≤
      ∑' u : passagePrefixFamily s, (passagePMF s u).toReal *
        integerPairPotential ε white (m - (u : ValuationWord).length / 2)
          (j + (u : ValuationWord).length / 2) (l + (u : ValuationWord).total) := by
  have hp := integerPairPotential_passage_le hε white s m j l hm
  have hfinite :
      (∑' u : passagePrefixFamily s,
        Reference.wordPMF (u : ValuationWord).length u *
          ENNReal.ofReal (integerPairPotential ε white
            (m - (u : ValuationWord).length / 2)
            (j + (u : ValuationWord).length / 2) (l + (u : ValuationWord).total))) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      _ ≤ ∑' u : passagePrefixFamily s,
          Reference.wordPMF (u : ValuationWord).length u := by
        apply ENNReal.tsum_le_tsum
        intro u
        calc
          _ ≤ Reference.wordPMF (u : ValuationWord).length u * 1 := by
            apply mul_le_mul_right
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (integerPairPotential_le_one hε white _ _ _)
          _ = _ := mul_one _
      _ = 1 := by simpa only [← passagePMF_apply] using PMF.tsum_coe (passagePMF s)
  have hr := ENNReal.toReal_mono hfinite hp
  rw [ENNReal.toReal_ofReal (integerPairPotential_nonneg hε white m j l)] at hr
  have hterm (u : passagePrefixFamily s) :
      Reference.wordPMF (u : ValuationWord).length u *
        ENNReal.ofReal (integerPairPotential ε white
          (m - (u : ValuationWord).length / 2)
          (j + (u : ValuationWord).length / 2) (l + (u : ValuationWord).total)) ≠ ⊤ :=
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top
  rw [ENNReal.tsum_toReal_eq hterm] at hr
  simp_rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (integerPairPotential_nonneg hε white _ _ _),
    ← passagePMF_apply] at hr
  exact hr

end WordCertDensity.LocalPrimitive
