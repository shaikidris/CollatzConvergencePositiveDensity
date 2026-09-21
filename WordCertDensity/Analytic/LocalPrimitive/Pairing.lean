/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.PairLaw
public import WordCertDensity.Reference.Fourier
public import WordCertDensity.Reference.AffineMixture
public import WordCertDensity.Analytic.ConductorFourier
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Local pair characters for primitive Fourier decay

This module specializes the exact original pair fiber to the additive
character used by `Reference.fourierMass`. It remains separate from the
accepted external primitive-decay producer while E-L1 is in progress.
-/

@[expose] public section

namespace WordCertDensity
namespace LocalPrimitive

/-- The exact dyadic contribution of one pair after preceding state `(j,l)`. -/
noncomputable def pairContribution (n j l b : ℕ) (i : Fin (b - 1)) : ZMod (3 ^ n) :=
  (3 : ZMod (3 ^ n)) ^ (2 * j) * Reference.inverseTwoPow n l *
    (Reference.inverseTwoPow n ((i : ℕ) + 1) +
      3 * Reference.inverseTwoPow n b)

/-- The additive character contributed by a fixed splitting of one pair. -/
noncomputable def pairCharacter (n j l b : ℕ) (ξ : ZMod (3 ^ n))
    (i : Fin (b - 1)) : ℂ :=
  ZMod.stdAddChar (ξ * pairContribution n j l b i)

/-- The canonical fixed-sum pair has the dyadic offset used in Appendix E. -/
theorem pairWord_residueOffset {n b : ℕ} (hb : 2 ≤ b) (i : Fin (b - 1)) :
    ValuationWord.residueOffset n (Reference.pairWord b i) =
      Reference.inverseTwoPow n ((i : ℕ) + 1) +
        3 * Reference.inverseTwoPow n b := by
  simp only [Reference.pairWord, ValuationWord.residueOffset, Nat.succPNat_coe]
  change Reference.inverseTwoPow n ((i : ℕ) + 1) *
      (1 + 3 * (Reference.inverseTwoPow n (b - 2 - (i : ℕ) + 1) * (1 + 3 * 0))) =
    Reference.inverseTwoPow n ((i : ℕ) + 1) + 3 * Reference.inverseTwoPow n b
  have hi : i.val ≤ b - 2 := by omega
  have hsum : (i : ℕ) + 1 + (b - 2 - (i : ℕ) + 1) = b := by omega
  simp only [mul_zero, add_zero, mul_one, mul_add]
  rw [show Reference.inverseTwoPow n ((i : ℕ) + 1) *
      (3 * Reference.inverseTwoPow n (b - 2 - (i : ℕ) + 1)) =
      3 * (Reference.inverseTwoPow n ((i : ℕ) + 1) *
        Reference.inverseTwoPow n (b - 2 - (i : ℕ) + 1)) by ring,
    ← Reference.inverseTwoPow_add, hsum]

/-- Every fixed splitting contributes a unit-modulus additive character. -/
theorem norm_pairCharacter (n j l : ℕ) {b : ℕ} (ξ : ZMod (3 ^ n))
    (i : Fin (b - 1)) : ‖pairCharacter n j l b ξ i‖ = 1 := by
  simp [pairCharacter]

/-- The conditional character of a fixed pair sum has modulus at most one. -/
theorem norm_pairConditionalCharacter_le_one (n j l : ℕ) {b : ℕ} (hb : 2 ≤ b)
    (ξ : ZMod (3 ^ n)) :
    ‖Reference.pairConditionalAverage b (pairCharacter n j l b ξ)‖ ≤ 1 := by
  exact Reference.norm_pairConditionalAverage_le_one hb _
    (fun i => (norm_pairCharacter n j l ξ i).le)

/-- Every reference Fourier coefficient has modulus at most one. -/
theorem norm_fourierMass_le_one (n : ℕ) (ξ : ZMod (3 ^ n)) :
    ‖Reference.fourierMass n ξ‖ ≤ 1 := by
  rw [Reference.fourierMass]
  calc
    ‖∑ x, (Reference.mass n x : ℂ) * ZMod.stdAddChar (ξ * x)‖
        ≤ ∑ x, ‖(Reference.mass n x : ℂ) * ZMod.stdAddChar (ξ * x)‖ :=
      norm_sum_le _ _
    _ = ∑ x, Reference.mass n x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [norm_mul, AddChar.norm_apply, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Reference.mass_nonneg n x)]
    _ = 1 := Reference.mass_sum n

/-- Fixed-sum weighted character mass is its pair mass times the conditional character. -/
theorem pairWeightedCharacter_eq (n j l : ℕ) {b : ℕ} (hb : 2 ≤ b)
    (ξ : ZMod (3 ^ n)) :
    Reference.pairWeightedSum b (pairCharacter n j l b ξ) =
      Reference.pairMass b *
        Reference.pairConditionalAverage b (pairCharacter n j l b ξ) := by
  exact Reference.pairWeightedSum_eq_mass_mul_average hb _

private theorem wordWeights_summable (v : ℕ) :
    Summable (fun w : ValuationWord => (Reference.wordPMF v w).toReal) :=
  ENNReal.summable_toReal (by
    rw [PMF.tsum_coe]
    exact ENNReal.one_ne_top)

private theorem blockFourierRow_summable (u v : ℕ)
    (ξ y : ZMod (3 ^ (u + v))) :
    Summable (fun w : ValuationWord =>
      ((Reference.wordPMF v w).toReal : ℂ) *
        ((((Reference.law u).map (Reference.blockMap u v w) y).toReal : ℂ) *
          ZMod.stdAddChar (ξ * y))) := by
  refine Summable.of_norm_bounded (wordWeights_summable v) ?_
  intro w
  rw [norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg]
  rw [AddChar.norm_apply]
  simp only [mul_one]
  have hprob : ((Reference.law u).map (Reference.blockMap u v w) y).toReal ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one ((Reference.law u).map (Reference.blockMap u v w)) y)
  simpa only [mul_one] using
    mul_le_of_le_one_right ENNReal.toReal_nonneg hprob

private theorem blockMassRow_summable (u v : ℕ) (y : ZMod (3 ^ (u + v))) :
    Summable (fun w : ValuationWord =>
      (Reference.wordPMF v w).toReal *
        ((Reference.law u).map (Reference.blockMap u v w) y).toReal) := by
  refine Summable.of_norm_bounded (wordWeights_summable v) ?_
  intro w
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
  have hprob : ((Reference.law u).map (Reference.blockMap u v w) y).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one ((Reference.law u).map (Reference.blockMap u v w)) y)
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg hprob

/-- Exact Fourier recurrence across an arbitrary independent terminal block.
The block is reversed because `Reference.law_blocks` peels the original word
from its high-index end; this convention is made explicit in the character. -/
theorem fourierMass_block_recurrence (u v : ℕ) (ξ : ZMod (3 ^ (u + v))) :
    Reference.fourierMass (u + v) ξ =
      ∑' w : ValuationWord,
        ((Reference.wordPMF v w).toReal : ℂ) *
          ZMod.stdAddChar
            (ξ * ValuationWord.residueOffset (u + v) w.reverse) *
          Reference.fourierMass u
            (Reference.project (Nat.le_add_right u v) ξ *
              Reference.inverseTwoPow u w.total) := by
  classical
  rw [Reference.fourierMass]
  simp only [Reference.mass_blocks]
  simp_rw [Complex.ofReal_tsum (fun w : ValuationWord =>
    (Reference.wordPMF v w).toReal *
      (((Reference.law u).map (Reference.blockMap u v w)) _).toReal)]
  simp only [Complex.ofReal_mul]
  simp_rw [← tsum_mul_right]
  simp only [mul_assoc]
  rw [← Summable.tsum_finsetSum
    (s := (Finset.univ : Finset (ZMod (3 ^ (u + v)))))
    (f := fun y w =>
      ((Reference.wordPMF v w).toReal : ℂ) *
        ((((Reference.law u).map (Reference.blockMap u v w) y).toReal : ℂ) *
          ZMod.stdAddChar (ξ * y)))
    (fun y _ => blockFourierRow_summable u v ξ y)]
  apply tsum_congr
  intro w
  rw [← Finset.mul_sum]
  congr 1
  rw [FiniteFourier.sum_pmf_map_mul]
  simp only [Reference.blockMap, mul_add]
  simp_rw [AddChar.map_add_eq_mul]
  calc
    _ = ∑ x, ZMod.stdAddChar
          (ξ * ValuationWord.residueOffset (u + v) w.reverse) *
        (((Reference.law u x).toReal : ℂ) *
          ZMod.stdAddChar
            (ξ * ((3 : ZMod (3 ^ (u + v))) ^ v *
              Reference.inverseTwoPow (u + v) w.total *
                (x.val : ZMod (3 ^ (u + v)))))) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ZMod.stdAddChar
          (ξ * ValuationWord.residueOffset (u + v) w.reverse) *
        ∑ x, (((Reference.law u x).toReal : ℂ) *
          ZMod.stdAddChar
            (ξ * ((3 : ZMod (3 ^ (u + v))) ^ v *
              Reference.inverseTwoPow (u + v) w.total *
                (x.val : ZMod (3 ^ (u + v)))))) := by
      rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      rw [Reference.fourierMass]
      apply Finset.sum_congr rfl
      intro x _
      simp only [Reference.mass]
      rw [show ξ * (((3 : ZMod (3 ^ (u + v))) ^ v *
          Reference.inverseTwoPow (u + v) w.total *
            (x.val : ZMod (3 ^ (u + v))))) =
          (ξ * Reference.inverseTwoPow (u + v) w.total) *
            ((3 : ZMod (3 ^ (u + v))) ^ v *
              (x.val : ZMod (3 ^ (u + v)))) by ring,
        FiniteFourier.character_three_pow_mul]
      simp only [Reference.project_inverseTwoPow, map_mul]
      simp only [Reference.project_natCast, ZMod.natCast_zmod_val]

/-- The exact two-step recurrence for the original pair process. -/
theorem fourierMass_pair_recurrence (u : ℕ) (ξ : ZMod (3 ^ (u + 2))) :
    Reference.fourierMass (u + 2) ξ =
      ∑' w : ValuationWord,
        ((Reference.wordPMF 2 w).toReal : ℂ) *
          ZMod.stdAddChar
            (ξ * ValuationWord.residueOffset (u + 2) w.reverse) *
          Reference.fourierMass u
            (Reference.project (Nat.le_add_right u 2) ξ *
              Reference.inverseTwoPow u w.total) :=
  fourierMass_block_recurrence u 2 ξ

/-- Character of a canonical pair in the orientation used by the exact
two-step recurrence. -/
noncomputable def reversePairCharacter (u b : ℕ) (ξ : ZMod (3 ^ (u + 2)))
    (i : Fin (b - 1)) : ℂ :=
  ZMod.stdAddChar
    (ξ * ValuationWord.residueOffset (u + 2) (Reference.pairWord b i).reverse)

/-- Conditional pair factor in the orientation of the exact recurrence. -/
noncomputable def reversePairFactor (u b : ℕ) (ξ : ZMod (3 ^ (u + 2))) : ℂ :=
  Reference.pairConditionalAverage b (reversePairCharacter u b ξ)

/-- Every reverse-oriented conditional pair factor has modulus at most one. -/
theorem norm_reversePairFactor_le_one (u : ℕ) {b : ℕ} (hb : 2 ≤ b)
    (ξ : ZMod (3 ^ (u + 2))) : ‖reversePairFactor u b ξ‖ ≤ 1 := by
  apply Reference.norm_pairConditionalAverage_le_one hb
  intro i
  simp [reversePairCharacter]

/-- A fixed-total recurrence term factors into pair mass, conditional
character, and the lower-level Fourier coefficient. -/
theorem pairWeightedTail_eq (u : ℕ) {b : ℕ} (hb : 2 ≤ b)
    (ξ : ZMod (3 ^ (u + 2))) :
    Reference.pairWeightedSum b (fun i =>
      reversePairCharacter u b ξ i *
        Reference.fourierMass u
          (Reference.project (Nat.le_add_right u 2) ξ *
            Reference.inverseTwoPow u b)) =
      Reference.pairMass b * reversePairFactor u b ξ *
        Reference.fourierMass u
          (Reference.project (Nat.le_add_right u 2) ξ *
            Reference.inverseTwoPow u b) := by
  rw [Reference.pairWeightedSum_eq_mass_mul_average hb]
  unfold reversePairFactor Reference.pairConditionalAverage
  simp only
  rw [← Finset.sum_mul]
  ring

private theorem pairRecurrence_summable (u : ℕ) (ξ : ZMod (3 ^ (u + 2))) :
    Summable (fun w : ValuationWord =>
      ((Reference.wordPMF 2 w).toReal : ℂ) *
        ZMod.stdAddChar
          (ξ * ValuationWord.residueOffset (u + 2) w.reverse) *
        Reference.fourierMass u
          (Reference.project (Nat.le_add_right u 2) ξ *
            Reference.inverseTwoPow u w.total)) := by
  refine Summable.of_norm_bounded (wordWeights_summable 2) ?_
  intro w
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg, AddChar.norm_apply, mul_one]
  simpa only [mul_one] using mul_le_of_le_one_right ENNReal.toReal_nonneg
    (norm_fourierMass_le_one u _)

/-- The two-step recurrence regrouped by the pair total and its uniform
splitting. This is the conditional form used by the discounted majorant. -/
theorem fourierMass_pair_recurrence_grouped (u : ℕ) (ξ : ZMod (3 ^ (u + 2))) :
    Reference.fourierMass (u + 2) ξ =
      ∑' b : {b : ℕ // 2 ≤ b},
        Reference.pairWeightedSum b.1 (fun i =>
          ZMod.stdAddChar
            (ξ * ValuationWord.residueOffset (u + 2)
              (Reference.pairWord b.1 i).reverse) *
          Reference.fourierMass u
            (Reference.project (Nat.le_add_right u 2) ξ *
              Reference.inverseTwoPow u b.1)) := by
  let f : ValuationWord → ℂ := fun w =>
    ((Reference.wordPMF 2 w).toReal : ℂ) *
      ZMod.stdAddChar
        (ξ * ValuationWord.residueOffset (u + 2) w.reverse) *
      Reference.fourierMass u
        (Reference.project (Nat.le_add_right u 2) ξ *
          Reference.inverseTwoPow u w.total)
  have hf : Summable f := pairRecurrence_summable u ξ
  rw [fourierMass_pair_recurrence, Reference.tsum_eq_tsum_pairIndex f]
  · have hfi : Summable (f ∘ Reference.pairIndexWord) :=
      hf.comp_injective Reference.pairIndexWord_injective
    change (∑' p : (b : {b : ℕ // 2 ≤ b}) × Fin (b.1 - 1),
      (f ∘ Reference.pairIndexWord) p) = _
    rw [hfi.tsum_sigma]
    apply tsum_congr
    intro b
    rw [tsum_fintype]
    rw [Reference.pairWeightedSum]
    apply Finset.sum_congr rfl
    intro i _
    change ((Reference.wordPMF 2 (Reference.pairWord b.1 i)).toReal : ℂ) *
        ZMod.stdAddChar
          (ξ * ValuationWord.residueOffset (u + 2)
            (Reference.pairWord b.1 i).reverse) *
        Reference.fourierMass u
          (Reference.project (Nat.le_add_right u 2) ξ *
            Reference.inverseTwoPow u (Reference.pairWord b.1 i).total) = _
    rw [Reference.pairWord_total b.2]
    ring
  · intro w hw
    simp only [f]
    rw [Reference.wordPMF_eq_zero_of_length_ne 2 w hw, ENNReal.toReal_zero,
      Complex.ofReal_zero, zero_mul, zero_mul]

end LocalPrimitive
end WordCertDensity
