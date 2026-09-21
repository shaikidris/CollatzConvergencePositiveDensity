/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.Geometry
public import WordCertDensity.Analytic.LocalPrimitive.IntegerPotential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Forward pair character at the Appendix E phase state

The E.2 potential processes the original pair word from left to right.  This
file isolates its conditional total-three character before any full-word
Fourier expansion is attempted.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- Conditional character factor for a pair read at the forward state `(j,l)`. -/
noncomputable def forwardPairFactor (n j l b : ℕ) (ξ : ZMod (3 ^ n)) : ℂ :=
  Reference.pairConditionalAverage b (pairCharacter n j l b ξ)

/-- A canonical pair contributes its ordinary residue offset, scaled by the
preceding pair column and valuation total.  This is the deterministic E.2
state update before conditioning on the pair sum. -/
theorem pairContribution_eq_forwardOffset {n j l b : ℕ} (ξ : ZMod (3 ^ n))
    (hb : 2 ≤ b) (i : Fin (b - 1)) :
    ξ * pairContribution n j l b i =
      ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) * Reference.inverseTwoPow n l *
        ValuationWord.residueOffset n (Reference.pairWord b i) := by
  rw [pairContribution, pairWord_residueOffset hb]
  ring

/-- The total-three forward factor is the average of its two exact characters. -/
theorem forwardPairFactor_three_eq_average (n j l : ℕ) (ξ : ZMod (3 ^ n)) :
    forwardPairFactor n j l 3 ξ =
      (pairCharacter n j l 3 ξ ⟨0, by omega⟩ +
        pairCharacter n j l 3 ξ ⟨1, by omega⟩) / 2 := by
  unfold forwardPairFactor Reference.pairConditionalAverage
  norm_num
  rw [Fin.sum_univ_two]
  ring

/-- Every conditional forward pair factor has norm at most one. -/
theorem norm_forwardPairFactor_le_one (n j l : ℕ) {b : ℕ} (hb : 2 ≤ b)
    (ξ : ZMod (3 ^ n)) : ‖forwardPairFactor n j l b ξ‖ ≤ 1 := by
  exact norm_pairConditionalCharacter_le_one n j l hb ξ

/-- The two forward total-three characters differ by the literal E.2 phase. -/
theorem forwardPairCharacter_three_difference (n j l : ℕ) (ξ : ZMod (3 ^ n)) :
    ξ * (pairContribution n j l 3 ⟨0, by omega⟩ -
      pairContribution n j l 3 ⟨1, by omega⟩) =
      phaseResidue n j l ξ := by
  unfold pairContribution phaseResidue
  have h12 : Reference.inverseTwoPow n 1 * Reference.inverseTwoPow n 1 =
      Reference.inverseTwoPow n 2 := by
    simpa using (Reference.inverseTwoPow_add n 1 1).symm
  have hc : (2 : ZMod (3 ^ n)) * Reference.inverseTwoPow n 1 = 1 := by
    simpa using Reference.two_pow_mul_inverseTwoPow n 1
  have h21 : (2 : ZMod (3 ^ n)) * Reference.inverseTwoPow n 2 =
      Reference.inverseTwoPow n 1 := by
    rw [← h12]
    calc
      2 * (Reference.inverseTwoPow n 1 * Reference.inverseTwoPow n 1) =
          Reference.inverseTwoPow n 1 * (2 * Reference.inverseTwoPow n 1) := by ring
      _ = Reference.inverseTwoPow n 1 := by rw [hc, mul_one]
  have hdiff : Reference.inverseTwoPow n 1 - Reference.inverseTwoPow n 2 =
      Reference.inverseTwoPow n 2 := by
    rw [← h21]
    ring
  change ξ * ((3 : ZMod (3 ^ n)) ^ (2 * j) * Reference.inverseTwoPow n l *
    (Reference.inverseTwoPow n 1 + 3 * Reference.inverseTwoPow n 3) -
    (3 : ZMod (3 ^ n)) ^ (2 * j) * Reference.inverseTwoPow n l *
    (Reference.inverseTwoPow n 2 + 3 * Reference.inverseTwoPow n 3)) = _
  calc
    _ = ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) * Reference.inverseTwoPow n l *
        (Reference.inverseTwoPow n 1 - Reference.inverseTwoPow n 2) := by ring
    _ = ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) * Reference.inverseTwoPow n l *
        Reference.inverseTwoPow n 2 := by
      rw [hdiff]
    _ = ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) *
        (Reference.inverseTwoPow n l * Reference.inverseTwoPow n 2) := by ring
    _ = _ := by rw [← Reference.inverseTwoPow_add n l 2]

/-- The first forward total-three character is the second times the phase character. -/
theorem forwardPairCharacter_three_zero_eq (n j l : ℕ) (ξ : ZMod (3 ^ n)) :
    pairCharacter n j l 3 ξ ⟨0, by omega⟩ =
      pairCharacter n j l 3 ξ ⟨1, by omega⟩ *
        ZMod.stdAddChar (phaseResidue n j l ξ) := by
  unfold pairCharacter
  rw [← AddChar.map_add_eq_mul]
  congr 1
  have hd := forwardPairCharacter_three_difference n j l ξ
  rw [mul_sub] at hd
  linear_combination hd

/-- The forward total-three conditional factor has the exact E.2 cosine norm. -/
theorem norm_forwardPairFactor_three_eq_cos (n j l : ℕ) (ξ : ZMod (3 ^ n)) :
    ‖forwardPairFactor n j l 3 ξ‖ =
      Real.cos (Real.pi * balancedPhase n j l ξ) := by
  rw [forwardPairFactor_three_eq_average,
    forwardPairCharacter_three_zero_eq]
  let a := pairCharacter n j l 3 ξ ⟨1, by omega⟩
  let z := ZMod.stdAddChar (phaseResidue n j l ξ)
  change ‖(a * z + a) / 2‖ = _
  rw [show (a * z + a) / 2 = a * ((z + 1) / 2) by ring, norm_mul]
  rw [show ‖a‖ = 1 by simp [a, pairCharacter], one_mul]
  rw [show (z + 1) / 2 = (1 + z) / 2 by ring]
  dsimp only [z]
  rw [stdAddChar_phaseResidue]
  apply norm_one_add_exp_two_pi_div_two
  have h := balancedPhase_mem n j l ξ
  rw [Set.mem_Ioc] at h
  rw [abs_le]
  constructor <;> linarith

/-- At a forward phase-white state, the total-three conditional factor has
the literal E.2 loss.  This is the local conditional estimate consumed by
the original-word forward expansion. -/
theorem norm_forwardPairFactor_three_le_white_discount (n j l : ℕ)
    (ξ : ZMod (3 ^ n))
    (hwhite : phaseWhiteAtInt n ξ j (l : ℤ)) :
    ‖forwardPairFactor n j l 3 ξ‖ ≤ 1 - 2 * localEpsilon ^ 2 := by
  rw [norm_forwardPairFactor_three_eq_cos]
  have hphase : localEpsilon ≤ |balancedPhase n j l ξ| := by
    unfold phaseWhiteAtInt phaseBlackAtInt at hwhite
    rw [balancedPhaseInt_ofNat] at hwhite
    exact le_of_lt (lt_of_not_ge hwhite)
  have hmem := balancedPhase_mem n j l ξ
  rw [Set.mem_Ioc] at hmem
  have hbound : |balancedPhase n j l ξ| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hcos := Real.cos_le_one_sub_mul_cos_sq (show
      |Real.pi * balancedPhase n j l ξ| ≤ Real.pi by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        nlinarith [Real.pi_pos])
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hscale : 2 / Real.pi ^ 2 * (Real.pi * balancedPhase n j l ξ) ^ 2 =
      2 * (balancedPhase n j l ξ) ^ 2 := by
    field_simp [hpi]
  rw [hscale] at hcos
  have hsquare : localEpsilon ^ 2 ≤ (balancedPhase n j l ξ) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg localEpsilon_nonneg] using hphase
  nlinarith

/-- The forward conditional factor is bounded by the literal total-discount
kernel: only a white total-three pair incurs the strict loss. -/
theorem norm_forwardPairFactor_le_totalDiscount (n j l : ℕ)
    (ξ : ZMod (3 ^ n)) (b : {b : ℕ // 2 ≤ b}) :
    ‖forwardPairFactor n j l b.1 ξ‖ ≤
      totalDiscount localEpsilon (phaseWhiteAtInt n ξ j (l : ℤ)) b.1 := by
  by_cases hw : phaseWhiteAtInt n ξ j (l : ℤ)
  · by_cases hb3 : b.1 = 3
    · simp only [totalDiscount, hw, hb3, and_self, if_pos]
      simpa [hb3] using norm_forwardPairFactor_three_le_white_discount n j l ξ hw
    · rw [totalDiscount, if_neg]
      · exact norm_forwardPairFactor_le_one n j l b.2 ξ
      · exact fun h => hb3 h.2
  · rw [totalDiscount, if_neg]
    · exact norm_forwardPairFactor_le_one n j l b.2 ξ
    · exact fun h => hw h.1

/-- On a canonical pair with total `b`, the word discount is exactly the
total-state discount. -/
theorem pairDiscount_pairWord_eq_totalDiscount (ε : ℝ) (white : Prop)
    {b : ℕ} (hb : 2 ≤ b) (i : Fin (b - 1)) :
    pairDiscount ε white (Reference.pairWord b i) = totalDiscount ε white b := by
  unfold pairDiscount totalDiscount
  rw [Reference.pairWord_total hb i]

end WordCertDensity.LocalPrimitive
