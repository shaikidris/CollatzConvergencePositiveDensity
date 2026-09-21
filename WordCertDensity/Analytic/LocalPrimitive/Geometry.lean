/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.Majorant
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Data.Nat.Dist

/-!
# Balanced-phase geometry for local primitive decay

This file formalizes the phase coordinates used in Appendix E.  It starts
with the exact modular step laws and the canonical balanced representative.
The triangle decomposition and its white collar are the remaining E-L2 work.
-/

@[expose] public section

namespace WordCertDensity
namespace LocalPrimitive

/-- Residue whose balanced representative is the Appendix E phase. -/
noncomputable def phaseResidue (n j l : ℕ) (ξ : ZMod (3 ^ n)) : ZMod (3 ^ n) :=
  ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) * Reference.inverseTwoPow n (l + 2)

/-- The Appendix E balanced phase, normalized modulo one. -/
noncomputable def balancedPhase (n j l : ℕ) (ξ : ZMod (3 ^ n)) : ℝ :=
  (phaseResidue n j l ξ).valMinAbs / (3 ^ n : ℝ)

/-- Residue whose balanced representative is the Appendix E phase at an
arbitrary integer valuation height. -/
noncomputable def phaseResidueInt (n j : ℕ) (l : ℤ) (ξ : ZMod (3 ^ n)) :
    ZMod (3 ^ n) :=
  ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) *
    ↑((Reference.twoUnit n)⁻¹ ^ (l + 2))

/-- The Appendix E balanced phase at an arbitrary integer valuation height. -/
noncomputable def balancedPhaseInt (n j : ℕ) (l : ℤ) (ξ : ZMod (3 ^ n)) : ℝ :=
  (phaseResidueInt n j l ξ).valMinAbs / (3 ^ n : ℝ)

/-- The integer-height residue agrees with the existing nonnegative phase
coordinate. -/
theorem phaseResidueInt_ofNat (n j l : ℕ) (ξ : ZMod (3 ^ n)) :
    phaseResidueInt n j (l : ℤ) ξ = phaseResidue n j l ξ := by
  unfold phaseResidueInt phaseResidue Reference.inverseTwoPow
  norm_cast

/-- The integer-height balanced phase agrees with the existing nonnegative
phase coordinate. -/
theorem balancedPhaseInt_ofNat (n j l : ℕ) (ξ : ZMod (3 ^ n)) :
    balancedPhaseInt n j (l : ℤ) ξ = balancedPhase n j l ξ := by
  unfold balancedPhaseInt balancedPhase
  rw [phaseResidueInt_ofNat]

/-- Moving one pair-column east multiplies the integer-height phase residue by
nine. -/
theorem phaseResidueInt_east (n j : ℕ) (l : ℤ) (ξ : ZMod (3 ^ n)) :
    phaseResidueInt n (j + 1) l ξ = 9 * phaseResidueInt n j l ξ := by
  unfold phaseResidueInt
  rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
  ring

/-- Moving one valuation unit north multiplies the integer-height phase
residue by two. -/
theorem phaseResidueInt_south (n j : ℕ) (l : ℤ) (ξ : ZMod (3 ^ n)) :
    phaseResidueInt n j (l - 1) ξ = 2 * phaseResidueInt n j l ξ := by
  unfold phaseResidueInt
  rw [show l - 1 + 2 = (l + 2) + (-1 : ℤ) by ring]
  let u : (ZMod (3 ^ n))ˣ := (Reference.twoUnit n)⁻¹
  change ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) * ↑(u ^ (l + 2 + (-1 : ℤ))) = _
  have hpow : u ^ (l + 2 + (-1 : ℤ)) = u ^ (l + 2) * u ^ (-1 : ℤ) := by
    exact zpow_add u (l + 2) (-1)
  rw [hpow, Units.val_mul]
  have htwo : (↑(u ^ (-1 : ℤ)) : ZMod (3 ^ n)) = 2 := by
    simp [u, Reference.twoUnit_val]
  rw [htwo]
  ring

/-- The integer-height balanced phase lies in the paper's interval
`(-1/2, 1/2]`. -/
theorem balancedPhaseInt_mem (n j : ℕ) (l : ℤ) (ξ : ZMod (3 ^ n)) :
    balancedPhaseInt n j l ξ * 2 ∈ Set.Ioc (-1 : ℝ) 1 := by
  have hn : (0 : ℝ) < 3 ^ n := by positivity
  have h := (phaseResidueInt n j l ξ).valMinAbs_mem_Ioc
  have hleft : (-(3 ^ n : ℤ) : ℝ) <
      (((phaseResidueInt n j l ξ).valMinAbs * 2 : ℤ) : ℝ) := by
    exact_mod_cast h.1
  have hright : (((phaseResidueInt n j l ξ).valMinAbs * 2 : ℤ) : ℝ) ≤
      ((3 ^ n : ℤ) : ℝ) := by
    exact_mod_cast h.2
  dsimp [balancedPhaseInt]
  constructor
  · rw [div_mul_eq_mul_div, lt_div_iff₀ hn]
    norm_num at hleft ⊢
    exact hleft
  · rw [div_mul_eq_mul_div, div_le_iff₀ hn]
    norm_num at hright ⊢
    exact hright

/-- Blackness at an arbitrary integer-height Appendix E lattice point. -/
def phaseBlackAtInt (n : ℕ) (ξ : ZMod (3 ^ n)) (j : ℕ) (l : ℤ) : Prop :=
  |balancedPhaseInt n j l ξ| ≤ localEpsilon

/-- The weak-black range at an arbitrary integer-height lattice point. -/
def phaseWeakBlackAtInt (n : ℕ) (ξ : ZMod (3 ^ n)) (j : ℕ) (l : ℤ) : Prop :=
  |balancedPhaseInt n j l ξ| ≤ 1 / 100

/-- Moving one pair-column east multiplies the phase residue by nine. -/
theorem phaseResidue_east (n j l : ℕ) (ξ : ZMod (3 ^ n)) :
    phaseResidue n (j + 1) l ξ = 9 * phaseResidue n j l ξ := by
  unfold phaseResidue
  rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
  norm_num
  ring

/-- Moving one valuation-unit south multiplies the phase residue by two. -/
theorem phaseResidue_south (n j l : ℕ) (ξ : ZMod (3 ^ n)) :
    phaseResidue n j l ξ = 2 * phaseResidue n j (l + 1) ξ := by
  have hcancel := Reference.two_pow_mul_inverseTwoPow n 1
  simp only [pow_one] at hcancel
  have hs : (2 : ZMod (3 ^ n)) * Reference.inverseTwoPow n ((l + 2) + 1) =
      Reference.inverseTwoPow n (l + 2) := by
    rw [Reference.inverseTwoPow_add]
    calc
      2 * (Reference.inverseTwoPow n (l + 2) * Reference.inverseTwoPow n 1) =
          Reference.inverseTwoPow n (l + 2) *
            (2 * Reference.inverseTwoPow n 1) := by ring
      _ = _ := by rw [hcancel, mul_one]
  unfold phaseResidue
  rw [show l + 1 + 2 = (l + 2) + 1 by omega, ← hs]
  ring

/-- The canonical balanced phase lies in the paper's interval `(-1/2, 1/2]`. -/
theorem balancedPhase_mem (n j l : ℕ) (ξ : ZMod (3 ^ n)) :
    balancedPhase n j l ξ * 2 ∈ Set.Ioc (-1 : ℝ) 1 := by
  have hn : (0 : ℝ) < 3 ^ n := by positivity
  have h := (phaseResidue n j l ξ).valMinAbs_mem_Ioc
  have hleft : (-(3 ^ n : ℤ) : ℝ) <
      (((phaseResidue n j l ξ).valMinAbs * 2 : ℤ) : ℝ) := by
    exact_mod_cast h.1
  have hright : (((phaseResidue n j l ξ).valMinAbs * 2 : ℤ) : ℝ) ≤
      ((3 ^ n : ℤ) : ℝ) := by
    exact_mod_cast h.2
  dsimp [balancedPhase]
  constructor
  · rw [div_mul_eq_mul_div, lt_div_iff₀ hn]
    norm_num at hleft ⊢
    exact hleft
  · rw [div_mul_eq_mul_div, div_le_iff₀ hn]
    norm_num at hright ⊢
    exact hright

/-- The total-three conditional factor is the average of its two exact pair
characters. This is the algebraic starting point for the cosine identity. -/
theorem reversePairFactor_three_eq_average (u : ℕ) (ξ : ZMod (3 ^ (u + 2))) :
    reversePairFactor u 3 ξ =
      (reversePairCharacter u 3 ξ ⟨0, by omega⟩ +
        reversePairCharacter u 3 ξ ⟨1, by omega⟩) / 2 := by
  unfold reversePairFactor Reference.pairConditionalAverage
  norm_num
  rw [Fin.sum_univ_two]
  ring

/-- The first reversed total-three pair has offset `5/8`. -/
theorem reversePairOffset_three_zero (n : ℕ) :
    ValuationWord.residueOffset n
      (Reference.pairWord 3 (⟨0, by omega⟩ : Fin 2)).reverse =
      Reference.inverseTwoPow n 2 + 3 * Reference.inverseTwoPow n 3 := by
  norm_num [Reference.pairWord, ValuationWord.residueOffset]
  have h3 : Reference.inverseTwoPow n 3 =
      Reference.inverseTwoPow n 2 * Reference.inverseTwoPow n 1 := by
    simpa using Reference.inverseTwoPow_add n 2 1
  rw [h3]
  ring

/-- The second reversed total-three pair has offset `7/8`. -/
theorem reversePairOffset_three_one (n : ℕ) :
    ValuationWord.residueOffset n
      (Reference.pairWord 3 (⟨1, by omega⟩ : Fin 2)).reverse =
      Reference.inverseTwoPow n 1 + 3 * Reference.inverseTwoPow n 3 := by
  norm_num [Reference.pairWord, ValuationWord.residueOffset]
  have h3 : Reference.inverseTwoPow n 3 =
      Reference.inverseTwoPow n 1 * Reference.inverseTwoPow n 2 := by
    simpa using Reference.inverseTwoPow_add n 1 2
  rw [h3]
  ring

/-- The separation of the two total-three characters is the actual balanced
phase residue at the current pair state. -/
theorem reversePairOffset_three_difference (u : ℕ)
    (ξ : ZMod (3 ^ (u + 2))) :
    ξ * (ValuationWord.residueOffset (u + 2)
      (Reference.pairWord 3 (⟨1, by omega⟩ : Fin 2)).reverse -
      ValuationWord.residueOffset (u + 2)
      (Reference.pairWord 3 (⟨0, by omega⟩ : Fin 2)).reverse) =
      phaseResidue (u + 2) 0 0 ξ := by
  rw [reversePairOffset_three_one, reversePairOffset_three_zero]
  have hcancel := Reference.two_pow_mul_inverseTwoPow (u + 2) 1
  simp only [pow_one] at hcancel
  have hs : (2 : ZMod (3 ^ (u + 2))) * Reference.inverseTwoPow (u + 2) 2 =
      Reference.inverseTwoPow (u + 2) 1 := by
    have h2 : Reference.inverseTwoPow (u + 2) 2 =
        Reference.inverseTwoPow (u + 2) 1 *
          Reference.inverseTwoPow (u + 2) 1 := by
      simpa using Reference.inverseTwoPow_add (u + 2) 1 1
    rw [h2]
    calc
      2 * (Reference.inverseTwoPow (u + 2) 1 *
          Reference.inverseTwoPow (u + 2) 1) =
          Reference.inverseTwoPow (u + 2) 1 *
            (2 * Reference.inverseTwoPow (u + 2) 1) := by ring
      _ = _ := by rw [hcancel, mul_one]
  simp only [phaseResidue, zero_add]
  rw [← hs]
  ring

/-- The elementary two-character norm identity on the balanced interval. -/
theorem norm_one_add_exp_two_pi_div_two (t : ℝ) (ht : |t| ≤ 1 / 2) :
    ‖((1 : ℂ) + Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)) / 2‖ =
      Real.cos (Real.pi * t) := by
  let x : ℝ := 2 * Real.pi * t
  change ‖((1 : ℂ) + Complex.exp ((x : ℂ) * Complex.I)) / 2‖ =
    Real.cos (Real.pi * t)
  have harg : Real.pi * t ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    have habs : |Real.pi * t| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos]
    exact abs_le.mp habs
  have hcos : 0 ≤ Real.cos (Real.pi * t) :=
    Real.cos_nonneg_of_mem_Icc harg
  rw [norm_div]
  norm_num
  rw [div_eq_iff (show (2 : ℝ) ≠ 0 by norm_num)]
  rw [Complex.norm_def]
  apply (Real.sqrt_eq_iff_eq_sq (Complex.normSq_nonneg _)
    (mul_nonneg hcos (by norm_num))).2
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
  rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  dsimp only [x]
  rw [show (2 : ℝ) * Real.pi * t = 2 * (Real.pi * t) by ring,
    Real.cos_two_mul, Real.sin_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t)]

/-- The standard character of the phase residue uses the balanced real phase. -/
theorem stdAddChar_phaseResidue (n j l : ℕ) (ξ : ZMod (3 ^ n)) :
    ZMod.stdAddChar (phaseResidue n j l ξ) =
      Complex.exp (((2 * Real.pi * balancedPhase n j l ξ : ℝ) : ℂ) * Complex.I) := by
  rw [← (phaseResidue n j l ξ).coe_valMinAbs, ZMod.stdAddChar_coe]
  unfold balancedPhase
  congr 1
  push_cast
  ring

/-- The second total-three character is the first multiplied by the phase
character. -/
theorem reversePairCharacter_three_one_eq (u : ℕ)
    (ξ : ZMod (3 ^ (u + 2))) :
    reversePairCharacter u 3 ξ ⟨1, by omega⟩ =
      reversePairCharacter u 3 ξ ⟨0, by omega⟩ *
        ZMod.stdAddChar (phaseResidue (u + 2) 0 0 ξ) := by
  unfold reversePairCharacter
  rw [← AddChar.map_add_eq_mul]
  congr 1
  have hd := reversePairOffset_three_difference u ξ
  rw [mul_sub] at hd
  linear_combination hd

/-- The actual total-three conditional factor is exactly the cosine of its
balanced phase. -/
theorem norm_reversePairFactor_three_eq_cos (u : ℕ)
    (ξ : ZMod (3 ^ (u + 2))) :
    ‖reversePairFactor u 3 ξ‖ =
      Real.cos (Real.pi * balancedPhase (u + 2) 0 0 ξ) := by
  rw [reversePairFactor_three_eq_average,
    reversePairCharacter_three_one_eq]
  let a := reversePairCharacter u 3 ξ ⟨0, by omega⟩
  let z := ZMod.stdAddChar (phaseResidue (u + 2) 0 0 ξ)
  change ‖(a + a * z) / 2‖ = _
  rw [show (a + a * z) / 2 = a * ((1 + z) / 2) by ring, norm_mul]
  rw [show ‖a‖ = 1 by simp [a, reversePairCharacter], one_mul]
  dsimp only [z]
  rw [stdAddChar_phaseResidue]
  apply norm_one_add_exp_two_pi_div_two
  have h := balancedPhase_mem (u + 2) 0 0 ξ
  rw [Set.mem_Ioc] at h
  rw [abs_le]
  constructor <;> linarith

/-- Black states use the exact dyadic phase width from Appendix E. -/
def phaseBlack (u : ℕ) (ξ : ZMod (3 ^ (u + 2))) : Prop :=
  |balancedPhase (u + 2) 0 0 ξ| ≤ localEpsilon

/-- Blackness at an arbitrary Appendix E lattice point. -/
def phaseBlackAt (n : ℕ) (ξ : ZMod (3 ^ n)) (j l : ℕ) : Prop :=
  |balancedPhase n j l ξ| ≤ localEpsilon

/-- The auxiliary weak-black threshold used to propagate the collar. -/
def phaseWeakBlackAt (n : ℕ) (ξ : ZMod (3 ^ n)) (j l : ℕ) : Prop :=
  |balancedPhase n j l ξ| ≤ 1 / 100

/-- Lattice points in a logarithmic Appendix E triangle. -/
def inPhaseTriangle (j₀ l₀ : ℕ) (t : ℝ) (j l : ℕ) : Prop :=
  j₀ ≤ j ∧ l ≤ l₀ ∧
    ((j - j₀ : ℕ) : ℝ) * Real.log 9 +
      ((l₀ - l : ℕ) : ℝ) * Real.log 2 ≤ t

/-- Squared lattice distance, avoiding square roots in collar bookkeeping. -/
def latticeDistSq (p q : ℕ × ℕ) : ℕ :=
  Nat.dist p.1 q.1 ^ 2 + Nat.dist p.2 q.2 ^ 2

/-- Distance at most the sixteen-unit collar width. -/
def withinPhaseCollar (p q : ℕ × ℕ) : Prop := latticeDistSq p q ≤ 16 ^ 2

/-- The printed logarithmic Appendix E triangle on the integer-height lattice. -/
def inPhaseTriangleInt (j₀ : ℕ) (l₀ : ℤ) (t : ℝ) (j : ℕ) (l : ℤ) : Prop :=
  j₀ ≤ j ∧ l ≤ l₀ ∧
    (j - j₀ : ℝ) * Real.log 9 +
      ((l₀ - l).toNat : ℝ) * Real.log 2 ≤ t

/-- Squared Euclidean lattice distance for Appendix E's integer-height states. -/
def latticeDistSqInt (p q : ℕ × ℤ) : ℕ :=
  Nat.dist p.1 q.1 ^ 2 + (p.2 - q.2).natAbs ^ 2

/-- The width-sixteen collar on the integer-height Appendix E lattice. -/
def withinPhaseCollarInt (p q : ℕ × ℤ) : Prop :=
  latticeDistSqInt p q ≤ 16 ^ 2

/-- A point in the sixteen-unit collar differs by at most sixteen columns. -/
theorem columnDist_le_sixteen_of_withinPhaseCollarInt {p q : ℕ × ℤ}
    (h : withinPhaseCollarInt p q) : Nat.dist p.1 q.1 ≤ 16 := by
  unfold withinPhaseCollarInt latticeDistSqInt at h
  nlinarith [Nat.zero_le ((p.2 - q.2).natAbs)]

/-- A point in the sixteen-unit collar differs by at most sixteen heights. -/
theorem heightDist_le_sixteen_of_withinPhaseCollarInt {p q : ℕ × ℤ}
    (h : withinPhaseCollarInt p q) : (p.2 - q.2).natAbs ≤ 16 := by
  unfold withinPhaseCollarInt latticeDistSqInt at h
  nlinarith [Nat.zero_le (Nat.dist p.1 q.1)]

/-- The conservative logarithmic excess allowed by a sixteen-unit collar. -/
theorem weightedLog_le_sixteen_of_sq_le (x y : ℕ)
    (h : x ^ 2 + y ^ 2 ≤ 16 ^ 2) :
    (x : ℝ) * Real.log 9 + (y : ℝ) * Real.log 2 ≤
      16 * (Real.log 9 + Real.log 2) := by
  have hx : x ≤ 16 := by nlinarith
  have hy : y ≤ 16 := by nlinarith
  have hlog9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hx' : (x : ℝ) * Real.log 9 ≤ 16 * Real.log 9 := by
    gcongr
    exact_mod_cast hx
  have hy' : (y : ℝ) * Real.log 2 ≤ 16 * Real.log 2 := by
    gcongr
    exact_mod_cast hy
  nlinarith

/-- The manuscript's southeast collar coordinates satisfy the conservative
logarithmic-excess bound. -/
theorem southeastExcessLog_le_sixteen (j₀ j : ℕ) (l₀ l : ℤ)
    (hj : j₀ ≤ j) (hl : l ≤ l₀)
    (hcollar : withinPhaseCollarInt (j, l) (j₀, l₀)) :
    (j - j₀ : ℝ) * Real.log 9 + ((l₀ - l).toNat : ℝ) * Real.log 2 ≤
      16 * (Real.log 9 + Real.log 2) := by
  rw [← Nat.cast_sub hj]
  apply weightedLog_le_sixteen_of_sq_le
  unfold withinPhaseCollarInt latticeDistSqInt at hcollar
  change Nat.dist j j₀ ^ 2 + (l - l₀).natAbs ^ 2 ≤ 16 ^ 2 at hcollar
  rw [Nat.dist_eq_sub_of_le_right hj] at hcollar
  have hheight : (l - l₀).natAbs = (l₀ - l).toNat := by
    have hnonneg : 0 ≤ l₀ - l := by omega
    calc
      (l - l₀).natAbs = (-(l - l₀)).natAbs := (Int.natAbs_neg _).symm
      _ = (l₀ - l).natAbs := by
        congr 1
        ring
      _ = (l₀ - l).toNat := by
        rw [← Int.ofNat_inj]
        exact (Int.natAbs_of_nonneg hnonneg).trans
          (Int.toNat_of_nonneg hnonneg).symm
  rw [hheight] at hcollar
  exact hcollar

/-- The numerical epsilon guard keeps every coordinatewise sixteen-step
amplification of a black phase in the weak-black no-wrap range. -/
theorem collarAmplification_lt_weak (a b : ℕ) (x : ℝ)
    (ha : a ≤ 16) (hb : b ≤ 16) (hx : 0 ≤ x) (hxe : x ≤ localEpsilon) :
    (9 ^ a * 2 ^ b : ℝ) * x < 1 / 100 := by
  have h9 : (9 : ℝ) ^ a ≤ 9 ^ 16 :=
    pow_le_pow_right₀ (by norm_num) ha
  have h2 : (2 : ℝ) ^ b ≤ 2 ^ 16 :=
    pow_le_pow_right₀ (by norm_num) hb
  have hK : (9 ^ a * 2 ^ b : ℝ) ≤ 18 ^ 16 := by
    calc
      (9 ^ a * 2 ^ b : ℝ) ≤ 9 ^ 16 * 2 ^ 16 :=
        mul_le_mul h9 h2 (by positivity) (by positivity)
      _ = 18 ^ 16 := by norm_num
  calc
    (9 ^ a * 2 ^ b : ℝ) * x ≤ 18 ^ 16 * localEpsilon :=
      mul_le_mul hK hxe hx (by positivity)
    _ < 1 / 100 := by norm_num [localEpsilon]

/-- The exact arithmetic guard behind the width-sixteen collar. -/
theorem localEpsilon_collar_guard :
    (100 : ℕ) * 18 ^ 17 < 2 ^ 78 := by norm_num

/-- The terminal-column arithmetic guard used in Appendix E. -/
theorem terminal_separation_guard : (9 : ℕ) ^ 17 < 2 ^ 78 := by norm_num

/-- A small integral representative remains the balanced representative after
multiplication by a natural scalar. -/
theorem valMinAbs_nat_mul_of_small {M k : ℕ} [NeZero M] (p : ZMod M)
    (hsmall : |((k : ℤ) * p.valMinAbs : ℤ)| * 2 < M) :
    ((k : ZMod M) * p).valMinAbs = (k : ℤ) * p.valMinAbs := by
  apply (ZMod.valMinAbs_spec _ _).2
  constructor
  · push_cast
    rfl
  · have habs : |((k : ℤ) * p.valMinAbs) * 2| < (M : ℤ) := by
      simpa [abs_mul] using hsmall
    have hlower : -(M : ℤ) < ((k : ℤ) * p.valMinAbs) * 2 := by
      have := neg_lt_of_abs_lt habs
      nlinarith
    have hupper : ((k : ℤ) * p.valMinAbs) * 2 ≤ (M : ℤ) := by
      exact le_of_lt (lt_of_le_of_lt (le_abs_self _) habs)
    exact ⟨hlower, hupper⟩

/-- On the weak-black range the integer-height east phase recurrence has no
wraparound. -/
theorem balancedPhaseInt_east_of_weak (n j : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n))
    (hweak : |balancedPhaseInt n j l ξ| ≤ 1 / 100) :
    balancedPhaseInt n (j + 1) l ξ = 9 * balancedPhaseInt n j l ξ := by
  unfold balancedPhaseInt
  rw [phaseResidueInt_east]
  have hval : ((9 : ZMod (3 ^ n)) * phaseResidueInt n j l ξ).valMinAbs =
      (9 : ℤ) * (phaseResidueInt n j l ξ).valMinAbs := by
    apply valMinAbs_nat_mul_of_small
    have hpow : (0 : ℝ) < 3 ^ n := by positivity
    have hscaled : |((9 : ℤ) * (phaseResidueInt n j l ξ).valMinAbs : ℤ)| * 2 <
        (3 ^ n : ℤ) := by
      have hw := hweak
      unfold balancedPhaseInt at hw
      simp only [abs_div, abs_of_pos hpow] at hw
      have hw' := (div_le_iff₀ hpow).mp hw
      have hcast : |(((phaseResidueInt n j l ξ).valMinAbs : ℤ) : ℝ)| * 9 * 2 <
          (3 ^ n : ℝ) := by
        norm_num at hw' ⊢
        nlinarith
      have hz : |(phaseResidueInt n j l ξ).valMinAbs| * 9 * 2 <
          (3 ^ n : ℤ) := by exact_mod_cast hcast
      simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hz
    exact hscaled
  rw [hval]
  push_cast
  ring

/-- On the weak-black range the integer-height north phase recurrence has no
wraparound. -/
theorem balancedPhaseInt_south_of_weak (n j : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n))
    (hweak : |balancedPhaseInt n j l ξ| ≤ 1 / 100) :
    balancedPhaseInt n j (l - 1) ξ = 2 * balancedPhaseInt n j l ξ := by
  unfold balancedPhaseInt
  rw [phaseResidueInt_south]
  have hval : ((2 : ZMod (3 ^ n)) * phaseResidueInt n j l ξ).valMinAbs =
      (2 : ℤ) * (phaseResidueInt n j l ξ).valMinAbs := by
    apply valMinAbs_nat_mul_of_small
    have hpow : (0 : ℝ) < 3 ^ n := by positivity
    have hscaled : |((2 : ℤ) * (phaseResidueInt n j l ξ).valMinAbs : ℤ)| * 2 <
        (3 ^ n : ℤ) := by
      have hw := hweak
      unfold balancedPhaseInt at hw
      simp only [abs_div, abs_of_pos hpow] at hw
      have hw' := (div_le_iff₀ hpow).mp hw
      have hcast : |(((phaseResidueInt n j l ξ).valMinAbs : ℤ) : ℝ)| * 2 * 2 <
          (3 ^ n : ℝ) := by
        norm_num at hw' ⊢
        nlinarith
      have hz : |(phaseResidueInt n j l ξ).valMinAbs| * 2 * 2 <
          (3 ^ n : ℤ) := by exact_mod_cast hcast
      simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hz
    exact hscaled
  rw [hval]
  push_cast
  ring

/-- The integer-height phase residue is determined by its east and north
neighbors. -/
theorem phaseResidueInt_parent_identity (n j : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n)) :
    phaseResidueInt n j l ξ = phaseResidueInt n (j + 1) l ξ -
      4 * phaseResidueInt n j (l - 1) ξ := by
  have he := phaseResidueInt_east n j l ξ
  have hs := phaseResidueInt_south n j l ξ
  rw [he, hs]
  ring

/-- The integer-height north phase recurrence has no wraparound at the
five-percent intermediate bound used in the parent propagation rule. -/
theorem balancedPhaseInt_south_of_fivePercent (n j : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n))
    (hbound : |balancedPhaseInt n j l ξ| ≤ 5 / 100) :
    balancedPhaseInt n j (l - 1) ξ = 2 * balancedPhaseInt n j l ξ := by
  unfold balancedPhaseInt
  rw [phaseResidueInt_south]
  have hval : ((2 : ZMod (3 ^ n)) * phaseResidueInt n j l ξ).valMinAbs =
      (2 : ℤ) * (phaseResidueInt n j l ξ).valMinAbs := by
    apply valMinAbs_nat_mul_of_small
    have hpow : (0 : ℝ) < 3 ^ n := by positivity
    have hw := hbound
    unfold balancedPhaseInt at hw
    simp only [abs_div, abs_of_pos hpow] at hw
    have hw' := (div_le_iff₀ hpow).mp hw
    have hcast : |(((phaseResidueInt n j l ξ).valMinAbs : ℤ) : ℝ)| * 2 * 2 <
        (3 ^ n : ℝ) := by
      norm_num at hw' ⊢
      nlinarith
    have hz : |(phaseResidueInt n j l ξ).valMinAbs| * 2 * 2 <
        (3 ^ n : ℤ) := by exact_mod_cast hcast
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hz
  rw [hval]
  push_cast
  ring

/-- A weak integer-height point with a black east neighbor is black. -/
theorem phaseBlackAtInt_of_weak_of_east (n j : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n))
    (hweak : phaseWeakBlackAtInt n ξ j l)
    (heast : phaseBlackAtInt n ξ (j + 1) l) : phaseBlackAtInt n ξ j l := by
  unfold phaseWeakBlackAtInt at hweak
  unfold phaseBlackAtInt at heast ⊢
  rw [balancedPhaseInt_east_of_weak n j l ξ hweak, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9)] at heast
  have hε := localEpsilon_nonneg
  nlinarith [abs_nonneg (balancedPhaseInt n j l ξ)]

/-- A weak integer-height point with a black north neighbor is black. -/
theorem phaseBlackAtInt_of_weak_of_north (n j : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n))
    (hweak : phaseWeakBlackAtInt n ξ j l)
    (hnorth : phaseBlackAtInt n ξ j (l - 1)) : phaseBlackAtInt n ξ j l := by
  unfold phaseWeakBlackAtInt at hweak
  unfold phaseBlackAtInt at hnorth ⊢
  rw [balancedPhaseInt_south_of_weak n j l ξ hweak, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hnorth
  have hε := localEpsilon_nonneg
  nlinarith [abs_nonneg (balancedPhaseInt n j l ξ)]

/-- Weak blackness propagates from the east and north integer neighbors. -/
theorem phaseWeakBlackAtInt_of_east_of_north (n j : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n))
    (heast : phaseWeakBlackAtInt n ξ (j + 1) l)
    (hnorth : phaseWeakBlackAtInt n ξ j (l - 1)) :
    phaseWeakBlackAtInt n ξ j l := by
  let x := phaseResidueInt n j l ξ
  let e := phaseResidueInt n (j + 1) l ξ
  let s := phaseResidueInt n j (l - 1) ξ
  have hid : x = e - 4 * s := by
    exact phaseResidueInt_parent_identity n j l ξ
  have hpow : (0 : ℝ) < 3 ^ n := by positivity
  have hs4small : |((4 : ℤ) * s.valMinAbs : ℤ)| * 2 < (3 ^ n : ℤ) := by
    have hw := hnorth
    unfold phaseWeakBlackAtInt balancedPhaseInt at hw
    simp only [abs_div, abs_of_pos hpow] at hw
    have hw' := (div_le_iff₀ hpow).mp hw
    have hcast : |((s.valMinAbs : ℤ) : ℝ)| * 4 * 2 < (3 ^ n : ℝ) := by
      norm_num at hw' ⊢
      nlinarith
    have hz : |s.valMinAbs| * 4 * 2 < (3 ^ n : ℤ) := by exact_mod_cast hcast
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hz
  have hs4 : ((4 : ZMod (3 ^ n)) * s).valMinAbs = (4 : ℤ) * s.valMinAbs :=
    valMinAbs_nat_mul_of_small s hs4small
  have hsum := ZMod.natAbs_valMinAbs_add_le e (-(4 : ZMod (3 ^ n)) * s)
  have hneg : (-(4 : ZMod (3 ^ n))) * s = -((4 : ZMod (3 ^ n)) * s) := by ring
  rw [hneg] at hsum
  have hxle : x.valMinAbs.natAbs ≤ e.valMinAbs.natAbs + 4 * s.valMinAbs.natAbs := by
    rw [hid, sub_eq_add_neg]
    calc
      _ ≤ (e.valMinAbs + (-(4 : ZMod (3 ^ n)) * s).valMinAbs).natAbs := by
        simpa [hneg] using hsum
      _ ≤ e.valMinAbs.natAbs + (-(4 : ZMod (3 ^ n)) * s).valMinAbs.natAbs :=
        Int.natAbs_add_le _ _
      _ = _ := by
        rw [hneg, ZMod.natAbs_valMinAbs_neg, hs4]
        simp [Int.natAbs_mul]
  have he := heast
  have hs := hnorth
  unfold phaseWeakBlackAtInt balancedPhaseInt at he hs
  simp only [abs_div, abs_of_pos hpow] at he hs
  have he' := (div_le_iff₀ hpow).mp he
  have hs' := (div_le_iff₀ hpow).mp hs
  have hxreal : |((x.valMinAbs : ℤ) : ℝ)| ≤
      |((e.valMinAbs : ℤ) : ℝ)| + 4 * |((s.valMinAbs : ℤ) : ℝ)| := by
    have hcast : (x.valMinAbs.natAbs : ℝ) ≤
        (e.valMinAbs.natAbs : ℝ) + 4 * (s.valMinAbs.natAbs : ℝ) := by
      exact_mod_cast hxle
    simpa using hcast
  change |((e.valMinAbs : ℤ) : ℝ)| ≤ 1 / 100 * (3 ^ n : ℝ) at he'
  change |((s.valMinAbs : ℤ) : ℝ)| ≤ 1 / 100 * (3 ^ n : ℝ) at hs'
  have hx5 : |balancedPhaseInt n j l ξ| ≤ 5 / 100 := by
    unfold balancedPhaseInt
    simp only [abs_div, abs_of_pos hpow]
    apply (div_le_iff₀ hpow).2
    change |((x.valMinAbs : ℤ) : ℝ)| ≤ 5 / 100 * (3 ^ n : ℝ)
    norm_num at he' hs' ⊢
    nlinarith
  have hreal := balancedPhaseInt_south_of_fivePercent n j l ξ hx5
  unfold phaseWeakBlackAtInt at hnorth ⊢
  rw [hreal, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hnorth
  nlinarith [abs_nonneg (balancedPhaseInt n j l ξ)]

/-- The integer-height north phase recurrence has no wraparound at the
nine-percent intermediate bound used in the west propagation rule. -/
theorem balancedPhaseInt_south_of_ninePercent (n j : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n))
    (hbound : |balancedPhaseInt n j l ξ| ≤ 9 / 100) :
    balancedPhaseInt n j (l - 1) ξ = 2 * balancedPhaseInt n j l ξ := by
  unfold balancedPhaseInt
  rw [phaseResidueInt_south]
  have hval : ((2 : ZMod (3 ^ n)) * phaseResidueInt n j l ξ).valMinAbs =
      (2 : ℤ) * (phaseResidueInt n j l ξ).valMinAbs := by
    apply valMinAbs_nat_mul_of_small
    have hpow : (0 : ℝ) < 3 ^ n := by positivity
    have hw := hbound
    unfold balancedPhaseInt at hw
    simp only [abs_div, abs_of_pos hpow] at hw
    have hw' := (div_le_iff₀ hpow).mp hw
    have hcast : |(((phaseResidueInt n j l ξ).valMinAbs : ℤ) : ℝ)| * 2 * 2 <
        (3 ^ n : ℝ) := by
      norm_num at hw' ⊢
      nlinarith
    have hz : |(phaseResidueInt n j l ξ).valMinAbs| * 2 * 2 <
        (3 ^ n : ℤ) := by exact_mod_cast hcast
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hz
  rw [hval]
  push_cast
  ring

/-- Weak blackness propagates from the west and north integer neighbors. -/
theorem phaseWeakBlackAtInt_of_west_of_north (n j : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n))
    (hj : 0 < j)
    (hwest : phaseWeakBlackAtInt n ξ (j - 1) l)
    (hnorth : phaseWeakBlackAtInt n ξ j (l - 1)) :
    phaseWeakBlackAtInt n ξ j l := by
  have hjadd : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have heast := balancedPhaseInt_east_of_weak n (j - 1) l ξ hwest
  rw [hjadd] at heast
  have hx9 : |balancedPhaseInt n j l ξ| ≤ 9 / 100 := by
    rw [heast, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9)]
    unfold phaseWeakBlackAtInt at hwest
    nlinarith [abs_nonneg (balancedPhaseInt n (j - 1) l ξ)]
  have hsouth := balancedPhaseInt_south_of_ninePercent n j l ξ hx9
  unfold phaseWeakBlackAtInt at hnorth ⊢
  rw [hsouth, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hnorth
  nlinarith [abs_nonneg (balancedPhaseInt n j l ξ)]

/-- Propagate weak blackness leftward above a black horizontal segment. This
is the local induction used by the northeast collar case. -/
theorem weakBlack_left_of_east_and_lower_segment (n j a : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n))
    (heast : phaseWeakBlackAtInt n ξ (j + a) (l + 1))
    (hlower : ∀ r ≤ a, phaseBlackAtInt n ξ (j + r) l) :
    phaseWeakBlackAtInt n ξ j (l + 1) := by
  induction a with
  | zero => simpa using heast
  | succ a ih =>
      have hmiddle : phaseWeakBlackAtInt n ξ (j + a) (l + 1) := by
        apply phaseWeakBlackAtInt_of_east_of_north n (j + a) (l + 1) ξ
        · simpa [Nat.add_assoc] using heast
        · have hblack := hlower a (by omega)
          unfold phaseBlackAtInt at hblack
          unfold phaseWeakBlackAtInt
          have hε : localEpsilon ≤ (1 / 100 : ℝ) := by
            norm_num [localEpsilon]
          simpa using hblack.trans hε
      apply ih hmiddle
      intro r hr
      exact hlower r (by omega)

/-- Propagate weak blackness leftward when the lower row is itself only weakly
black. This handles bounded collar extensions beyond a selected top edge. -/
theorem weakBlack_left_of_east_and_weak_lower_segment (n j a : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n))
    (heast : phaseWeakBlackAtInt n ξ (j + a) (l + 1))
    (hlower : ∀ r ≤ a, phaseWeakBlackAtInt n ξ (j + r) l) :
    phaseWeakBlackAtInt n ξ j (l + 1) := by
  induction a with
  | zero => simpa using heast
  | succ a ih =>
      have hmiddle : phaseWeakBlackAtInt n ξ (j + a) (l + 1) := by
        apply phaseWeakBlackAtInt_of_east_of_north n (j + a) (l + 1) ξ
        · simpa [Nat.add_assoc] using heast
        · simpa using hlower a (by omega)
      apply ih hmiddle
      intro r hr
      exact hlower r (by omega)

/-- Propagate weak blackness upward along a column from its lower endpoint,
using weak east neighbors. This is the west collar induction. -/
theorem weakBlack_up_of_east_and_lower_segment (n j a : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n))
    (hbase : phaseWeakBlackAtInt n ξ j l)
    (heast : ∀ s ≤ a, phaseWeakBlackAtInt n ξ (j + 1) (l + s)) :
    phaseWeakBlackAtInt n ξ j (l + a) := by
  induction a with
  | zero => simpa using hbase
  | succ a ih =>
      have hprev := ih (fun s hs => heast s (by omega))
      have hheight : l + (a + 1) - 1 = l + a := by ring
      apply phaseWeakBlackAtInt_of_east_of_north n j (l + (a + 1)) ξ
      · exact heast (a + 1) (by omega)
      · simpa [hheight] using hprev

/-- The below-top branch of the west collar: weak propagation up the west
column contradicts the selected left boundary. -/
theorem west_below_top_contradiction (n j₀ a : ℕ) (l₀ l : ℤ)
    (ξ : ZMod (3 ^ n)) (hj₀ : 0 < j₀)
    (hleft : ¬ phaseBlackAtInt n ξ (j₀ - 1) l₀)
    (hcorner : phaseBlackAtInt n ξ j₀ l₀)
    (hbase : phaseWeakBlackAtInt n ξ (j₀ - 1) l)
    (heast : ∀ s ≤ a, phaseWeakBlackAtInt n ξ j₀ (l + s))
    (hheight : l + a = l₀) : False := by
  have hup := weakBlack_up_of_east_and_lower_segment n (j₀ - 1) a l ξ hbase
    (by simpa [Nat.sub_add_cancel hj₀] using heast)
  rw [hheight] at hup
  apply hleft
  apply phaseBlackAtInt_of_weak_of_east n (j₀ - 1) l₀ ξ hup
  simpa [Nat.sub_add_cancel hj₀] using hcorner

/-- Propagate weak blackness rightward above a black horizontal segment. This
is the complementary branch of the northeast collar case. -/
theorem weakBlack_right_of_west_and_lower_segment (n j a : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n))
    (hwest : phaseWeakBlackAtInt n ξ j (l + 1))
    (hlower : ∀ r ≤ a, phaseBlackAtInt n ξ (j + r) l) :
    phaseWeakBlackAtInt n ξ (j + a) (l + 1) := by
  induction a with
  | zero => simpa using hwest
  | succ a ih =>
      apply phaseWeakBlackAtInt_of_west_of_north n (j + (a + 1)) (l + 1) ξ
      · omega
      · have hprev := ih (fun r hr => hlower r (by omega))
        simpa [Nat.add_assoc] using hprev
      · have hblack := hlower (a + 1) (by omega)
        unfold phaseBlackAtInt at hblack
        unfold phaseWeakBlackAtInt
        have hε : localEpsilon ≤ (1 / 100 : ℝ) := by norm_num [localEpsilon]
        simpa using hblack.trans hε

/-- A white point above the right end of a black top-row segment forces the
whole segment's north boundary to be white. -/
theorem no_black_above_top_segment (n j₀ j₁ : ℕ) (l : ℤ)
    (ξ : ZMod (3 ^ n)) (hj : j₀ ≤ j₁)
    (hrow : ∀ r, j₀ ≤ r → r ≤ j₁ → phaseBlackAtInt n ξ r l)
    (htop : ¬ phaseBlackAtInt n ξ j₁ (l + 1)) :
    ∀ r, j₀ ≤ r → r ≤ j₁ → ¬ phaseBlackAtInt n ξ r (l + 1) := by
  intro r hr₀ hr₁ hblack
  have hweak : phaseWeakBlackAtInt n ξ r (l + 1) := by
    unfold phaseBlackAtInt at hblack
    unfold phaseWeakBlackAtInt
    have hε : localEpsilon ≤ (1 / 100 : ℝ) := by norm_num [localEpsilon]
    exact hblack.trans hε
  have hprop := weakBlack_right_of_west_and_lower_segment n r (j₁ - r) l ξ
    hweak (fun s hs => hrow (r + s) (by omega) (by omega))
  have hradd : r + (j₁ - r) = j₁ := Nat.add_sub_of_le hr₁
  rw [hradd] at hprop
  apply htop
  apply phaseBlackAtInt_of_weak_of_north n j₁ (l + 1) ξ hprop
  simpa using hrow j₁ (by omega) le_rfl

/-- On the weak-black range the east phase recurrence is an equality of real
balanced representatives, not merely a congruence. -/
theorem balancedPhase_east_of_weak (n j l : ℕ) (ξ : ZMod (3 ^ n))
    (hweak : |balancedPhase n j l ξ| ≤ 1 / 100) :
    balancedPhase n (j + 1) l ξ = 9 * balancedPhase n j l ξ := by
  unfold balancedPhase
  rw [phaseResidue_east]
  have hval : ((9 : ZMod (3 ^ n)) * phaseResidue n j l ξ).valMinAbs =
      (9 : ℤ) * (phaseResidue n j l ξ).valMinAbs := by
    apply valMinAbs_nat_mul_of_small
    have hpow : (0 : ℝ) < 3 ^ n := by positivity
    have hscaled : |((9 : ℤ) * (phaseResidue n j l ξ).valMinAbs : ℤ)| * 2 <
        (3 ^ n : ℤ) := by
      have hw := hweak
      unfold balancedPhase at hw
      simp only [abs_div, abs_of_pos hpow] at hw
      have hw' := (div_le_iff₀ hpow).mp hw
      have hcast : |(((phaseResidue n j l ξ).valMinAbs : ℤ) : ℝ)| * 9 * 2 <
          (3 ^ n : ℝ) := by
        norm_num at hw' ⊢
        nlinarith
      have hz : |(phaseResidue n j l ξ).valMinAbs| * 9 * 2 <
          (3 ^ n : ℤ) := by exact_mod_cast hcast
      simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hz
    exact hscaled
  rw [hval]
  push_cast
  ring

/-- On the weak-black range the south phase recurrence is an equality of real
balanced representatives. -/
theorem balancedPhase_south_of_weak (n j l : ℕ) (ξ : ZMod (3 ^ n))
    (hweak : |balancedPhase n j (l + 1) ξ| ≤ 1 / 100) :
    balancedPhase n j l ξ = 2 * balancedPhase n j (l + 1) ξ := by
  unfold balancedPhase
  rw [phaseResidue_south]
  have hval : ((2 : ZMod (3 ^ n)) * phaseResidue n j (l + 1) ξ).valMinAbs =
      (2 : ℤ) * (phaseResidue n j (l + 1) ξ).valMinAbs := by
    apply valMinAbs_nat_mul_of_small
    have hpow : (0 : ℝ) < 3 ^ n := by positivity
    have hscaled : |((2 : ℤ) * (phaseResidue n j (l + 1) ξ).valMinAbs : ℤ)| * 2 <
        (3 ^ n : ℤ) := by
      have hw := hweak
      unfold balancedPhase at hw
      simp only [abs_div, abs_of_pos hpow] at hw
      have hw' := (div_le_iff₀ hpow).mp hw
      have hcast : |(((phaseResidue n j (l + 1) ξ).valMinAbs : ℤ) : ℝ)| * 2 * 2 <
          (3 ^ n : ℝ) := by
        norm_num at hw' ⊢
        nlinarith
      have hz : |(phaseResidue n j (l + 1) ξ).valMinAbs| * 2 * 2 <
          (3 ^ n : ℤ) := by exact_mod_cast hcast
      simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hz
    exact hscaled
  rw [hval]
  push_cast
  ring

/-- A weak-black point with a black east neighbor is black. -/
theorem phaseBlackAt_of_weak_of_east (n j l : ℕ) (ξ : ZMod (3 ^ n))
    (hweak : phaseWeakBlackAt n ξ j l)
    (heast : phaseBlackAt n ξ (j + 1) l) : phaseBlackAt n ξ j l := by
  unfold phaseWeakBlackAt at hweak
  unfold phaseBlackAt at heast ⊢
  rw [balancedPhase_east_of_weak n j l ξ hweak, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9)] at heast
  have hε := localEpsilon_nonneg
  nlinarith [abs_nonneg (balancedPhase n j l ξ)]

/-- A weak-black point with its lower (`l-1`) neighbor black is black. -/
theorem phaseBlackAt_of_weak_of_lower (n j l : ℕ) (ξ : ZMod (3 ^ n))
    (hl : 0 < l) (hweak : phaseWeakBlackAt n ξ j l)
    (hlower : phaseBlackAt n ξ j (l - 1)) : phaseBlackAt n ξ j l := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  unfold phaseWeakBlackAt at hweak
  unfold phaseBlackAt at hlower ⊢
  simp only [Nat.succ_sub_one] at hlower
  rw [balancedPhase_south_of_weak n j l ξ hweak, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hlower
  have hε := localEpsilon_nonneg
  nlinarith [abs_nonneg (balancedPhase n j (l + 1) ξ)]

theorem phaseResidue_parent_identity (n j l : ℕ) (ξ : ZMod (3 ^ n))
    (hl : 0 < l) :
    phaseResidue n j l ξ = phaseResidue n (j + 1) l ξ -
      4 * phaseResidue n j (l - 1) ξ := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  simp only [Nat.succ_sub_one]
  have he := phaseResidue_east n j (l + 1) ξ
  have hs := phaseResidue_south n j l ξ
  rw [he, hs]
  ring

theorem balancedPhase_south_of_fivePercent (n j l : ℕ) (ξ : ZMod (3 ^ n))
    (hbound : |balancedPhase n j (l + 1) ξ| ≤ 5 / 100) :
    balancedPhase n j l ξ = 2 * balancedPhase n j (l + 1) ξ := by
  unfold balancedPhase
  rw [phaseResidue_south]
  have hval : ((2 : ZMod (3 ^ n)) * phaseResidue n j (l + 1) ξ).valMinAbs =
      (2 : ℤ) * (phaseResidue n j (l + 1) ξ).valMinAbs := by
    apply valMinAbs_nat_mul_of_small
    have hpow : (0 : ℝ) < 3 ^ n := by positivity
    have hw := hbound
    unfold balancedPhase at hw
    simp only [abs_div, abs_of_pos hpow] at hw
    have hw' := (div_le_iff₀ hpow).mp hw
    have hcast : |(((phaseResidue n j (l + 1) ξ).valMinAbs : ℤ) : ℝ)| * 2 * 2 <
        (3 ^ n : ℝ) := by
      norm_num at hw' ⊢
      nlinarith
    have hz : |(phaseResidue n j (l + 1) ξ).valMinAbs| * 2 * 2 <
        (3 ^ n : ℤ) := by exact_mod_cast hcast
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hz
  rw [hval]
  push_cast
  ring

theorem phaseWeakBlackAt_of_east_of_lower (n j l : ℕ) (ξ : ZMod (3 ^ n))
    (hl : 0 < l)
    (heast : phaseWeakBlackAt n ξ (j + 1) l)
    (hlower : phaseWeakBlackAt n ξ j (l - 1)) :
    phaseWeakBlackAt n ξ j l := by
  let x := phaseResidue n j l ξ
  let e := phaseResidue n (j + 1) l ξ
  let s := phaseResidue n j (l - 1) ξ
  have hid : x = e - 4 * s := by
    exact phaseResidue_parent_identity n j l ξ hl
  have hpow : (0 : ℝ) < 3 ^ n := by positivity
  have hs4small : |((4 : ℤ) * s.valMinAbs : ℤ)| * 2 < (3 ^ n : ℤ) := by
    have hw := hlower
    unfold phaseWeakBlackAt balancedPhase at hw
    simp only [abs_div, abs_of_pos hpow] at hw
    have hw' := (div_le_iff₀ hpow).mp hw
    have hcast : |((s.valMinAbs : ℤ) : ℝ)| * 4 * 2 < (3 ^ n : ℝ) := by
      norm_num at hw' ⊢
      nlinarith
    have hz : |s.valMinAbs| * 4 * 2 < (3 ^ n : ℤ) := by exact_mod_cast hcast
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hz
  have hs4 : ((4 : ZMod (3 ^ n)) * s).valMinAbs = (4 : ℤ) * s.valMinAbs :=
    valMinAbs_nat_mul_of_small s hs4small
  have hsum := ZMod.natAbs_valMinAbs_add_le e (-(4 : ZMod (3 ^ n)) * s)
  have hneg : (-(4 : ZMod (3 ^ n))) * s = -((4 : ZMod (3 ^ n)) * s) := by ring
  rw [hneg] at hsum
  have hxle : x.valMinAbs.natAbs ≤ e.valMinAbs.natAbs + 4 * s.valMinAbs.natAbs := by
    rw [hid]
    rw [sub_eq_add_neg]
    calc
      _ ≤ (e.valMinAbs + (-(4 : ZMod (3 ^ n)) * s).valMinAbs).natAbs := by
        simpa [hneg] using hsum
      _ ≤ e.valMinAbs.natAbs + (-(4 : ZMod (3 ^ n)) * s).valMinAbs.natAbs :=
        Int.natAbs_add_le _ _
      _ = _ := by
        rw [hneg, ZMod.natAbs_valMinAbs_neg, hs4]
        simp [Int.natAbs_mul]
  have he := heast
  have hs := hlower
  unfold phaseWeakBlackAt balancedPhase at he hs
  simp only [abs_div, abs_of_pos hpow] at he hs
  have he' := (div_le_iff₀ hpow).mp he
  have hs' := (div_le_iff₀ hpow).mp hs
  have hxreal : |((x.valMinAbs : ℤ) : ℝ)| ≤
      |((e.valMinAbs : ℤ) : ℝ)| + 4 * |((s.valMinAbs : ℤ) : ℝ)| := by
    have hcast : (x.valMinAbs.natAbs : ℝ) ≤
        (e.valMinAbs.natAbs : ℝ) + 4 * (s.valMinAbs.natAbs : ℝ) := by
      exact_mod_cast hxle
    simpa using hcast
  change |((e.valMinAbs : ℤ) : ℝ)| ≤ 1 / 100 * (3 ^ n : ℝ) at he'
  change |((s.valMinAbs : ℤ) : ℝ)| ≤ 1 / 100 * (3 ^ n : ℝ) at hs'
  have hx5 : |balancedPhase n j l ξ| ≤ 5 / 100 := by
    unfold balancedPhase
    simp only [abs_div, abs_of_pos hpow]
    apply (div_le_iff₀ hpow).2
    change |((x.valMinAbs : ℤ) : ℝ)| ≤ 5 / 100 * (3 ^ n : ℝ)
    norm_num at he' hs' ⊢
    nlinarith
  have hadd : l - 1 + 1 = l := Nat.sub_add_cancel hl
  have hreal := balancedPhase_south_of_fivePercent n j (l - 1) ξ
    (by simpa [hadd] using hx5)
  rw [hadd] at hreal
  unfold phaseWeakBlackAt at hlower ⊢
  rw [hreal, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hlower
  nlinarith [abs_nonneg (balancedPhase n j l ξ)]

theorem balancedPhase_south_of_ninePercent (n j l : ℕ) (ξ : ZMod (3 ^ n))
    (hbound : |balancedPhase n j (l + 1) ξ| ≤ 9 / 100) :
    balancedPhase n j l ξ = 2 * balancedPhase n j (l + 1) ξ := by
  unfold balancedPhase
  rw [phaseResidue_south]
  have hval : ((2 : ZMod (3 ^ n)) * phaseResidue n j (l + 1) ξ).valMinAbs =
      (2 : ℤ) * (phaseResidue n j (l + 1) ξ).valMinAbs := by
    apply valMinAbs_nat_mul_of_small
    have hpow : (0 : ℝ) < 3 ^ n := by positivity
    have hw := hbound
    unfold balancedPhase at hw
    simp only [abs_div, abs_of_pos hpow] at hw
    have hw' := (div_le_iff₀ hpow).mp hw
    have hcast : |(((phaseResidue n j (l + 1) ξ).valMinAbs : ℤ) : ℝ)| * 2 * 2 <
        (3 ^ n : ℝ) := by
      norm_num at hw' ⊢
      nlinarith
    have hz : |(phaseResidue n j (l + 1) ξ).valMinAbs| * 2 * 2 <
        (3 ^ n : ℤ) := by exact_mod_cast hcast
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hz
  rw [hval]
  push_cast
  ring

theorem phaseWeakBlackAt_of_west_of_lower (n j l : ℕ) (ξ : ZMod (3 ^ n))
    (hj : 0 < j) (hl : 0 < l)
    (hwest : phaseWeakBlackAt n ξ (j - 1) l)
    (hlower : phaseWeakBlackAt n ξ j (l - 1)) :
    phaseWeakBlackAt n ξ j l := by
  have hjadd : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have heast := balancedPhase_east_of_weak n (j - 1) l ξ hwest
  rw [hjadd] at heast
  have hx9 : |balancedPhase n j l ξ| ≤ 9 / 100 := by
    rw [heast, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9)]
    unfold phaseWeakBlackAt at hwest
    nlinarith [abs_nonneg (balancedPhase n (j - 1) l ξ)]
  have hladd : l - 1 + 1 = l := Nat.sub_add_cancel hl
  have hsouth := balancedPhase_south_of_ninePercent n j (l - 1) ξ
    (by simpa [hladd] using hx9)
  rw [hladd] at hsouth
  unfold phaseWeakBlackAt at hlower ⊢
  rw [hsouth, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hlower
  nlinarith [abs_nonneg (balancedPhase n j l ξ)]

theorem isUnit_of_not_three_dvd {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) : IsUnit ξ := by
  rw [← ZMod.natCast_zmod_val ξ]
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_three hn).2
  intro hval
  obtain ⟨a, ha⟩ := hval
  apply hξ
  refine ⟨(a : ZMod (3 ^ n)), ?_⟩
  rw [← ZMod.natCast_zmod_val ξ, ha, Nat.cast_mul]
  norm_num

theorem three_pow_ne_zero_zmod {n k : ℕ} (hk : k < n) :
    (3 : ZMod (3 ^ n)) ^ k ≠ 0 := by
  rw [show (3 : ZMod (3 ^ n)) ^ k = ((3 ^ k : ℕ) : ZMod (3 ^ n)) by
    norm_num]
  intro hzero
  have hd : 3 ^ n ∣ 3 ^ k :=
    (ZMod.natCast_eq_zero_iff (3 ^ k) (3 ^ n)).mp hzero
  rw [Nat.pow_dvd_pow_iff_le_right (by omega : 1 < 3)] at hd
  omega

theorem phaseResidue_ne_zero_of_primitive {n j l : ℕ} (hn : 0 < n)
    (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) : phaseResidue n j l ξ ≠ 0 := by
  have hunitξ := isUnit_of_not_three_dvd hn ξ hξ
  have hunit2 : IsUnit (Reference.inverseTwoPow n (l + 2)) := by
    unfold Reference.inverseTwoPow
    exact Units.isUnit _
  intro hzero
  have hpowzero : (3 : ZMod (3 ^ n)) ^ (2 * j) = 0 := by
    apply hunitξ.mul_left_cancel
    apply hunit2.mul_right_cancel
    simpa [phaseResidue, mul_assoc] using hzero
  exact three_pow_ne_zero_zmod hj hpowzero

theorem abs_balancedPhase_pos_of_primitive {n j l : ℕ} (hn : 0 < n)
    (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    0 < |balancedPhase n j l ξ| := by
  have hne := phaseResidue_ne_zero_of_primitive (l := l) hn hj ξ hξ
  have hvm : (phaseResidue n j l ξ).valMinAbs ≠ 0 :=
    mt (ZMod.valMinAbs_eq_zero _).mp hne
  unfold balancedPhase
  positivity

theorem one_div_three_pow_le_abs_balancedPhase_of_primitive {n j l : ℕ}
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    1 / (3 ^ n : ℝ) ≤ |balancedPhase n j l ξ| := by
  have hne := phaseResidue_ne_zero_of_primitive (l := l) hn hj ξ hξ
  have hvm : (phaseResidue n j l ξ).valMinAbs ≠ 0 :=
    mt (ZMod.valMinAbs_eq_zero _).mp hne
  have hone : (1 : ℝ) ≤ |(((phaseResidue n j l ξ).valMinAbs : ℤ) : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hvm)
  unfold balancedPhase
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ n)]
  exact div_le_div_of_nonneg_right hone (by positivity)

/-- A primitive frequency has nonzero integer-height phase residue before the
terminal pair column. -/
theorem phaseResidueInt_ne_zero_of_primitive {n j : ℕ} (l : ℤ)
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) : phaseResidueInt n j l ξ ≠ 0 := by
  have hunitξ := isUnit_of_not_three_dvd hn ξ hξ
  have hunit2 : IsUnit (↑((Reference.twoUnit n)⁻¹ ^ (l + 2)) : ZMod (3 ^ n)) := by
    exact Units.isUnit _
  intro hzero
  have hpowzero : (3 : ZMod (3 ^ n)) ^ (2 * j) = 0 := by
    apply hunitξ.mul_left_cancel
    apply hunit2.mul_right_cancel
    simpa [phaseResidueInt, mul_assoc] using hzero
  exact three_pow_ne_zero_zmod hj hpowzero

/-- A primitive integer-height balanced phase is nonzero before the terminal
pair column. -/
theorem abs_balancedPhaseInt_pos_of_primitive {n j : ℕ} (l : ℤ)
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    0 < |balancedPhaseInt n j l ξ| := by
  have hne := phaseResidueInt_ne_zero_of_primitive l hn hj ξ hξ
  have hvm : (phaseResidueInt n j l ξ).valMinAbs ≠ 0 :=
    mt (ZMod.valMinAbs_eq_zero _).mp hne
  unfold balancedPhaseInt
  positivity

/-- The least nonzero integer-height primitive phase is at least one ternary
modulus unit. -/
theorem one_div_three_pow_le_abs_balancedPhaseInt_of_primitive {n j : ℕ}
    (l : ℤ) (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    1 / (3 ^ n : ℝ) ≤ |balancedPhaseInt n j l ξ| := by
  have hne := phaseResidueInt_ne_zero_of_primitive l hn hj ξ hξ
  have hvm : (phaseResidueInt n j l ξ).valMinAbs ≠ 0 :=
    mt (ZMod.valMinAbs_eq_zero _).mp hne
  have hone : (1 : ℝ) ≤ |(((phaseResidueInt n j l ξ).valMinAbs : ℤ) : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hvm)
  unfold balancedPhaseInt
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ n)]
  exact div_le_div_of_nonneg_right hone (by positivity)

/-- Before the terminal column, the integer representative of the phase has
the forced ternary factor contributed by its horizontal coordinate. -/
theorem three_pow_two_j_dvd_phaseRepresentative {n j : ℕ} (l : ℤ)
    (hj : 2 * j ≤ n) (ξ : ZMod (3 ^ n)) :
    ((3 : ℤ) ^ (2 * j)) ∣ (phaseResidueInt n j l ξ).valMinAbs := by
  let u : ZMod (3 ^ n) := ξ * ↑((Reference.twoUnit n)⁻¹ ^ (l + 2))
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective u
  let d : ℤ := (3 : ℤ) ^ (2 * j)
  have hphase : phaseResidueInt n j l ξ =
      (a : ZMod (3 ^ n)) * (d : ZMod (3 ^ n)) := by
    unfold phaseResidueInt
    dsimp only [d]
    have hu : ξ * ↑((Reference.twoUnit n)⁻¹ ^ (l + 2)) =
        (a : ZMod (3 ^ n)) := by
      simpa [u] using ha.symm
    rw [show ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) *
        ↑((Reference.twoUnit n)⁻¹ ^ (l + 2)) =
        (ξ * ↑((Reference.twoUnit n)⁻¹ ^ (l + 2))) *
          (3 : ZMod (3 ^ n)) ^ (2 * j) by ring, hu]
    push_cast
    ring
  have hrep : ((phaseResidueInt n j l ξ).valMinAbs : ZMod (3 ^ n)) =
      ((a * d : ℤ) : ZMod (3 ^ n)) := by
    rw [ZMod.coe_valMinAbs, hphase]
    push_cast
    rfl
  have hmod : (3 ^ n : ℤ) ∣
      a * d - (phaseResidueInt n j l ξ).valMinAbs :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hrep
  have hdn : d ∣ (3 ^ n : ℤ) := by
    dsimp [d]
    refine ⟨(3 : ℤ) ^ (n - 2 * j), ?_⟩
    rw [← pow_add]
    congr 1
    omega
  have hdprod : d ∣ a * d := dvd_mul_left _ _
  have hneg : d ∣ (a * d - (phaseResidueInt n j l ξ).valMinAbs) - a * d :=
    Int.dvd_sub (dvd_trans hdn hmod) hdprod
  have hzneg : d ∣ -(phaseResidueInt n j l ξ).valMinAbs := by
    simpa using hneg
  exact dvd_neg.mp hzneg

/-- A primitive phase at column `j` has the stronger lower bound forced by
its nonzero multiple of `3^(2*j)`. -/
theorem scaled_primitive_phase_lower {n j : ℕ} (l : ℤ)
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    ((3 : ℝ) ^ (2 * j)) / (3 ^ n : ℝ) ≤
      |balancedPhaseInt n j l ξ| := by
  have hd := three_pow_two_j_dvd_phaseRepresentative l
    (show 2 * j ≤ n by omega) ξ
  obtain ⟨a, ha⟩ := hd
  have hne := phaseResidueInt_ne_zero_of_primitive l hn hj ξ hξ
  have hvm : (phaseResidueInt n j l ξ).valMinAbs ≠ 0 :=
    mt (ZMod.valMinAbs_eq_zero _).mp hne
  have hane : a ≠ 0 := by
    intro hz
    apply hvm
    rw [ha, hz, mul_zero]
  have haone : (1 : ℝ) ≤ |(a : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hane)
  have hdnonneg : 0 ≤ (3 : ℝ) ^ (2 * j) := by positivity
  have hrep : ((phaseResidueInt n j l ξ).valMinAbs : ℝ) =
      (3 : ℝ) ^ (2 * j) * (a : ℝ) := by
    norm_cast
  have habs : (3 : ℝ) ^ (2 * j) ≤
      |((phaseResidueInt n j l ξ).valMinAbs : ℝ)| := by
    rw [hrep, abs_mul, abs_of_nonneg hdnonneg]
    simpa using mul_le_mul_of_nonneg_left haone hdnonneg
  unfold balancedPhaseInt
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ n)]
  exact div_le_div_of_nonneg_right habs (by positivity)

/-- Integer-height blackness is contained in the weak-black range. -/
theorem phaseBlackAtInt_implies_weak (n : ℕ) (ξ : ZMod (3 ^ n))
    (j : ℕ) (l : ℤ) (hblack : phaseBlackAtInt n ξ j l) :
    phaseWeakBlackAtInt n ξ j l := by
  unfold phaseBlackAtInt at hblack
  unfold phaseWeakBlackAtInt
  have hε : localEpsilon ≤ (1 / 100 : ℝ) := by
    norm_num [localEpsilon]
  exact hblack.trans hε

/-- A primitive integer-height black run reaches a white point within twice
the conductor exponent. -/
theorem exists_nonblack_above_of_primitive_int {n j : ℕ} (l : ℤ)
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    ∃ k ≤ 2 * n, ¬ phaseBlackAtInt n ξ j (l + k) := by
  by_contra hnone
  push Not at hnone
  have hscale : ∀ k ≤ 2 * n,
      balancedPhaseInt n j l ξ = (2 : ℝ) ^ k * balancedPhaseInt n j (l + k) ξ := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : k ≤ 2 * n := by omega
        have hweak := phaseBlackAtInt_implies_weak n ξ j (l + (k + 1))
          (hnone (k + 1) (by omega))
        unfold phaseWeakBlackAtInt at hweak
        have hstep := balancedPhaseInt_south_of_weak n j (l + (k + 1)) ξ hweak
        have hheight : l + (k + 1) - 1 = l + k := by ring
        rw [hheight] at hstep
        rw [ih hk', hstep, pow_succ]
        norm_num [Nat.cast_add]
        ring
  have hblack0 := hnone 0 (by omega)
  have hlower := one_div_three_pow_le_abs_balancedPhaseInt_of_primitive
    (l + 2 * n) hn hj ξ hξ
  have hscaled := congrArg abs (hscale (2 * n) le_rfl)
  rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hscaled
  unfold phaseBlackAtInt at hblack0
  norm_num at hblack0
  have hpowpos : (0 : ℝ) < 3 ^ n := by positivity
  have htwo : (2 : ℝ) ^ (2 * n) ≤ localEpsilon * (3 ^ n : ℝ) := by
    rw [hscaled] at hblack0
    have hprod := mul_le_mul_of_nonneg_left hlower
      (by positivity : 0 ≤ (2 : ℝ) ^ (2 * n))
    apply (div_le_iff₀ hpowpos).mp
    simpa [div_eq_mul_inv] using hprod.trans hblack0
  have hεlt : localEpsilon < 1 := by norm_num [localEpsilon]
  have h34nat : 3 ^ n < 4 ^ n := Nat.pow_lt_pow_left (by omega) (by omega)
  have h34 : (3 : ℝ) ^ n < 4 ^ n := by exact_mod_cast h34nat
  have htwoeq : (2 : ℝ) ^ (2 * n) = 4 ^ n := by
    rw [pow_mul]
    norm_num
  rw [htwoeq] at htwo
  have : localEpsilon * (3 : ℝ) ^ n < 4 ^ n := by
    calc
      localEpsilon * (3 : ℝ) ^ n < 1 * (3 ^ n : ℝ) := by gcongr
      _ < 4 ^ n := by simpa using h34
  exact (not_lt_of_ge htwo) this

/-- A primitive integer-height black horizontal run reaches a nonblack point
within twice the conductor exponent. -/
theorem exists_nonblack_east_of_primitive_int {n j : ℕ} (l : ℤ)
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    ∃ k ≤ 2 * n, ¬ phaseBlackAtInt n ξ (j + k) l := by
  by_contra hnone
  push Not at hnone
  have hscale : ∀ k ≤ 2 * n,
      balancedPhaseInt n (j + k) l ξ =
        (9 : ℝ) ^ k * balancedPhaseInt n j l ξ := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : k ≤ 2 * n := by omega
        have hweak := phaseBlackAtInt_implies_weak n ξ (j + k) l
          (hnone k (by omega))
        unfold phaseWeakBlackAtInt at hweak
        have hstep := balancedPhaseInt_east_of_weak n (j + k) l ξ hweak
        rw [Nat.add_succ, hstep, ih hk', pow_succ]
        ring
  have hblackK := hnone (2 * n) le_rfl
  have hlower := one_div_three_pow_le_abs_balancedPhaseInt_of_primitive
    l hn hj ξ hξ
  have hscaled := congrArg abs (hscale (2 * n) le_rfl)
  rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9)] at hscaled
  unfold phaseBlackAtInt at hblackK
  have hpowpos : (0 : ℝ) < 3 ^ n := by positivity
  have hnine : (9 : ℝ) ^ (2 * n) ≤ localEpsilon * (3 ^ n : ℝ) := by
    rw [hscaled] at hblackK
    have hprod := mul_le_mul_of_nonneg_left hlower
      (by positivity : 0 ≤ (9 : ℝ) ^ (2 * n))
    apply (div_le_iff₀ hpowpos).mp
    simpa [div_eq_mul_inv] using hprod.trans hblackK
  have hεlt : localEpsilon < 1 := by norm_num [localEpsilon]
  have h39nat : 3 ^ n < 9 ^ (2 * n) := by
    calc
      3 ^ n < 9 ^ n := Nat.pow_lt_pow_left (by omega) (Nat.ne_of_gt hn)
      _ ≤ 9 ^ (2 * n) := pow_le_pow_right' (by omega) (by omega)
  have h39 : (3 : ℝ) ^ n < 9 ^ (2 * n) := by exact_mod_cast h39nat
  have : localEpsilon * (3 : ℝ) ^ n < 9 ^ (2 * n) := by
    calc
      localEpsilon * (3 : ℝ) ^ n < 1 * (3 ^ n : ℝ) := by gcongr
      _ < 9 ^ (2 * n) := by simpa using h39
  exact (not_lt_of_ge hnine) this

theorem phaseBlackAt_implies_weak (n : ℕ) (ξ : ZMod (3 ^ n)) (j l : ℕ)
    (hblack : phaseBlackAt n ξ j l) : phaseWeakBlackAt n ξ j l := by
  unfold phaseBlackAt at hblack
  unfold phaseWeakBlackAt
  have hε : localEpsilon ≤ (1 / 100 : ℝ) := by
    norm_num [localEpsilon]
  exact hblack.trans hε

theorem exists_nonblack_above_of_primitive {n j l : ℕ} (hn : 0 < n)
    (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    ∃ k ≤ 2 * n, ¬ phaseBlackAt n ξ j (l + k) := by
  by_contra hnone
  push Not at hnone
  have hscale : ∀ k ≤ 2 * n,
      balancedPhase n j l ξ = (2 : ℝ) ^ k * balancedPhase n j (l + k) ξ := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : k ≤ 2 * n := by omega
        have hweak := phaseBlackAt_implies_weak n ξ j (l + (k + 1))
          (hnone (k + 1) (by omega))
        unfold phaseWeakBlackAt at hweak
        have hstep := balancedPhase_south_of_weak n j (l + k) ξ
          (by simpa [Nat.add_assoc] using hweak)
        rw [ih hk', hstep, pow_succ]
        ring_nf
  have hblack0 := hnone 0 (by omega)
  have hblackK := hnone (2 * n) (le_rfl)
  have hlower := one_div_three_pow_le_abs_balancedPhase_of_primitive
    (l := l + 2 * n) hn hj ξ hξ
  have hscaled := congrArg abs (hscale (2 * n) le_rfl)
  rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hscaled
  unfold phaseBlackAt at hblack0 hblackK
  simp only [Nat.add_zero] at hblack0
  have hpowpos : (0 : ℝ) < 3 ^ n := by positivity
  have htwo : (2 : ℝ) ^ (2 * n) ≤ localEpsilon * (3 ^ n : ℝ) := by
    rw [hscaled] at hblack0
    have hprod := mul_le_mul_of_nonneg_left hlower
      (by positivity : 0 ≤ (2 : ℝ) ^ (2 * n))
    apply (div_le_iff₀ hpowpos).mp
    simpa [div_eq_mul_inv] using hprod.trans hblack0
  have hεlt : localEpsilon < 1 := by norm_num [localEpsilon]
  have h34nat : 3 ^ n < 4 ^ n := Nat.pow_lt_pow_left (by omega) (by omega)
  have h34 : (3 : ℝ) ^ n < 4 ^ n := by exact_mod_cast h34nat
  have htwoeq : (2 : ℝ) ^ (2 * n) = 4 ^ n := by
    rw [pow_mul]
    norm_num
  rw [htwoeq] at htwo
  have : localEpsilon * (3 : ℝ) ^ n < 4 ^ n := by
    calc
      localEpsilon * (3 : ℝ) ^ n < 1 * (3 : ℝ) ^ n := by
        gcongr
      _ < 4 ^ n := by simpa using h34
  exact (not_lt_of_ge htwo) this

/-- A primitive integer-height black state has a last black point in its
vertical run. -/
theorem exists_black_top_of_primitive_int {n j : ℕ} (l : ℤ)
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hblack : phaseBlackAtInt n ξ j l) :
    ∃ l₀ : ℤ, l ≤ l₀ ∧ phaseBlackAtInt n ξ j l₀ ∧
      (∀ r : ℤ, l ≤ r → r ≤ l₀ → phaseBlackAtInt n ξ j r) ∧
      ¬ phaseBlackAtInt n ξ j (l₀ + 1) ∧ l₀ < l + 2 * n := by
  classical
  obtain ⟨k, hk, hkwhite⟩ := exists_nonblack_above_of_primitive_int l hn hj ξ hξ
  let P : ℕ → Prop := fun r => ¬ phaseBlackAtInt n ξ j (l + r)
  have hP : ∃ r, P r := ⟨k, hkwhite⟩
  let k₀ := Nat.find hP
  have hk₀P : P k₀ := Nat.find_spec hP
  have hk₀pos : 0 < k₀ := by
    by_contra hz
    have : k₀ = 0 := by omega
    apply hk₀P
    simpa [P, this] using hblack
  have hk₀le : k₀ ≤ k := Nat.find_min' hP hkwhite
  refine ⟨l + ((k₀ - 1 : ℕ) : ℤ), ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Nat.cast_sub, Nat.cast_one]
  · have hprev : ¬ P (k₀ - 1) := Nat.find_min hP (by omega : k₀ - 1 < k₀)
    simpa [P] using hprev
  · intro r hlr hrl
    have hrnat : (r - l).toNat < k₀ := by
      have : r - l < k₀ := by omega
      exact (Int.toNat_lt_of_ne_zero (by omega : k₀ ≠ 0)).mpr this
    have hprev : ¬ P (r - l).toNat := Nat.find_min hP hrnat
    have hnonneg : 0 ≤ r - l := by omega
    have hcast : ((r - l).toNat : ℤ) = r - l := Int.toNat_of_nonneg hnonneg
    unfold P at hprev
    rw [hcast] at hprev
    have hrform : l + (r - l) = r := by omega
    rw [hrform] at hprev
    push Not at hprev
    exact hprev
  · have hadd : l + ((k₀ - 1 : ℕ) : ℤ) + 1 = l + k₀ := by omega
    change ¬ phaseBlackAtInt n ξ j (l + (k₀ : ℤ)) at hk₀P
    rw [hadd]
    exact hk₀P
  · omega

/-- A primitive integer-height black state has a last black point in its
horizontal run. -/
theorem exists_black_rightmost_of_primitive_int {n j : ℕ} (l : ℤ)
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hblack : phaseBlackAtInt n ξ j l) :
    ∃ j₁, j ≤ j₁ ∧ phaseBlackAtInt n ξ j₁ l ∧
      (∀ r, j ≤ r → r ≤ j₁ → phaseBlackAtInt n ξ r l) ∧
      ¬ phaseBlackAtInt n ξ (j₁ + 1) l ∧ j₁ < j + 2 * n := by
  classical
  obtain ⟨k, hk, hkwhite⟩ := exists_nonblack_east_of_primitive_int l hn hj ξ hξ
  let P : ℕ → Prop := fun r => ¬ phaseBlackAtInt n ξ (j + r) l
  have hP : ∃ r, P r := ⟨k, hkwhite⟩
  let k₀ := Nat.find hP
  have hk₀P : P k₀ := Nat.find_spec hP
  have hk₀pos : 0 < k₀ := by
    by_contra hz
    have : k₀ = 0 := by omega
    apply hk₀P
    simpa [P, this] using hblack
  have hk₀le : k₀ ≤ k := Nat.find_min' hP hkwhite
  refine ⟨j + k₀ - 1, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · have hprev : ¬ P (k₀ - 1) := Nat.find_min hP (by omega : k₀ - 1 < k₀)
    have heq : j + (k₀ - 1) = j + k₀ - 1 := by omega
    simpa [P, heq] using hprev
  · intro r hjr hrj
    have hrform : j + (r - j) = r := Nat.add_sub_of_le hjr
    have hrlt : r - j < k₀ := by omega
    have hprev : ¬ P (r - j) := Nat.find_min hP hrlt
    simpa [P, hrform] using hprev
  · have hadd : j + k₀ - 1 + 1 = j + k₀ := by omega
    simpa [hadd, P] using hk₀P
  · omega

/-- The left edge of a contiguous integer-height black top row is canonical. -/
theorem exists_black_row_start_int (n j : ℕ) (l₀ : ℤ)
    (ξ : ZMod (3 ^ n)) (hblack : phaseBlackAtInt n ξ j l₀) :
    ∃ j₀, j₀ ≤ j ∧
      (∀ r, j₀ ≤ r → r ≤ j → phaseBlackAtInt n ξ r l₀) ∧
      (j₀ = 0 ∨ ¬ phaseBlackAtInt n ξ (j₀ - 1) l₀) := by
  classical
  let P : ℕ → Prop := fun k => k ≤ j ∧
    ∀ r, k ≤ r → r ≤ j → phaseBlackAtInt n ξ r l₀
  have hP : ∃ k, P k := ⟨j, le_rfl, fun r hr₁ hr₂ => by
    have : r = j := Nat.le_antisymm hr₂ hr₁
    simpa [this] using hblack⟩
  let j₀ := Nat.find hP
  have hj₀P : P j₀ := Nat.find_spec hP
  refine ⟨j₀, hj₀P.1, hj₀P.2, ?_⟩
  by_cases hz : j₀ = 0
  · exact Or.inl hz
  · right
    intro hwest
    have hprev : P (j₀ - 1) := by
      constructor
      · omega
      · intro r hr₁ hr₂
        by_cases hr : r = j₀ - 1
        · simpa [hr] using hwest
        · apply hj₀P.2 r
          omega
          exact hr₂
    exact (Nat.find_min hP (by omega : j₀ - 1 < j₀)) hprev

/-- Iterate the integer-height east residue recurrence. -/
theorem phaseResidueInt_east_iter (n j : ℕ) (l : ℤ) (a : ℕ)
    (ξ : ZMod (3 ^ n)) :
    phaseResidueInt n (j + a) l ξ =
      (9 : ZMod (3 ^ n)) ^ a * phaseResidueInt n j l ξ := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Nat.add_succ, phaseResidueInt_east, ih, pow_succ]
      ring

/-- Iterate the integer-height north residue recurrence. -/
theorem phaseResidueInt_north_iter (n j : ℕ) (l : ℤ) (b : ℕ)
    (ξ : ZMod (3 ^ n)) :
    phaseResidueInt n j (l - b) ξ =
      (2 : ZMod (3 ^ n)) ^ b * phaseResidueInt n j l ξ := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hheight : l - (b + 1) = (l - b) - 1 := by ring
      norm_num [Nat.cast_add]
      rw [hheight, phaseResidueInt_south, ih, pow_succ]
      ring

/-- Express an integer-height phase residue from a northwest triangle corner. -/
theorem phaseResidueInt_from_corner (n j₀ : ℕ) (l₀ : ℤ) (j : ℕ)
    (l : ℤ) (ξ : ZMod (3 ^ n)) (hj : j₀ ≤ j) (hl : l ≤ l₀) :
    phaseResidueInt n j l ξ =
      ((9 ^ (j - j₀) * 2 ^ (l₀ - l).toNat : ℕ) : ZMod (3 ^ n)) *
        phaseResidueInt n j₀ l₀ ξ := by
  have hjeq : j₀ + (j - j₀) = j := Nat.add_sub_of_le hj
  have hnonneg : 0 ≤ l₀ - l := by omega
  have hleq : l₀ - (l₀ - l).toNat = l := by
    rw [Int.toNat_of_nonneg hnonneg]
    ring
  calc
    phaseResidueInt n j l ξ =
        phaseResidueInt n (j₀ + (j - j₀)) (l₀ - (l₀ - l).toNat) ξ := by
          rw [hjeq, hleq]
    _ = (9 : ZMod (3 ^ n)) ^ (j - j₀) *
        phaseResidueInt n j₀ (l₀ - (l₀ - l).toNat) ξ :=
      phaseResidueInt_east_iter n j₀ (l₀ - (l₀ - l).toNat) (j - j₀) ξ
    _ = (9 : ZMod (3 ^ n)) ^ (j - j₀) *
        ((2 : ZMod (3 ^ n)) ^ (l₀ - l).toNat * phaseResidueInt n j₀ l₀ ξ) := by
      rw [phaseResidueInt_north_iter n j₀ l₀ (l₀ - l).toNat ξ]
    _ = _ := by push_cast; ring

/-- Exact integer-height phase scaling under the explicit no-wrap threshold.
This is the phase bridge used both inside a black triangle and in its collar. -/
theorem balancedPhaseInt_from_corner_of_small (n : ℕ)
    (ξ : ZMod (3 ^ n)) (j₀ : ℕ) (l₀ : ℤ) (j : ℕ) (l : ℤ)
    (hj : j₀ ≤ j) (hl : l ≤ l₀)
    (hsmall :
      (9 ^ (j - j₀) * 2 ^ (l₀ - l).toNat : ℝ) *
        |balancedPhaseInt n j₀ l₀ ξ| < 1 / 2) :
    balancedPhaseInt n j l ξ =
      (9 ^ (j - j₀) * 2 ^ (l₀ - l).toNat : ℝ) *
        balancedPhaseInt n j₀ l₀ ξ := by
  let k : ℕ := 9 ^ (j - j₀) * 2 ^ (l₀ - l).toNat
  have hres := phaseResidueInt_from_corner n j₀ l₀ j l ξ hj hl
  have hpow : (0 : ℝ) < 3 ^ n := by positivity
  have hsmallZ : |((k : ℤ) * (phaseResidueInt n j₀ l₀ ξ).valMinAbs : ℤ)| * 2 <
      (3 ^ n : ℤ) := by
    have hreal : (k : ℝ) *
        |(((phaseResidueInt n j₀ l₀ ξ).valMinAbs : ℤ) : ℝ)| /
          (3 ^ n : ℝ) < 1 / 2 := by
      simpa [balancedPhaseInt, k, abs_div, abs_of_pos hpow, mul_div_assoc] using hsmall
    have hreal' : (k : ℝ) *
        |(((phaseResidueInt n j₀ l₀ ξ).valMinAbs : ℤ) : ℝ)| * 2 <
          (3 ^ n : ℝ) := by
      have hcleared := (div_lt_iff₀ hpow).mp hreal
      nlinarith
    have hz : (k : ℤ) * |(phaseResidueInt n j₀ l₀ ξ).valMinAbs| * 2 <
        (3 ^ n : ℤ) := by exact_mod_cast hreal'
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hz
  unfold balancedPhaseInt
  rw [hres]
  have hval := valMinAbs_nat_mul_of_small (phaseResidueInt n j₀ l₀ ξ) hsmallZ
  change (((k : ZMod (3 ^ n)) * phaseResidueInt n j₀ l₀ ξ).valMinAbs : ℝ) /
      (3 ^ n : ℝ) = _
  rw [hval]
  push_cast
  dsimp only [k]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring_nf

/-- A black point descends to weak blackness across at most sixteen heights,
with exact no-wrap phase scaling. -/
theorem weak_below_of_black_of_height_gap_le_sixteen (n j : ℕ)
    (lUpper lLower : ℤ) (ξ : ZMod (3 ^ n))
    (hl : lLower ≤ lUpper) (hgap : (lUpper - lLower).toNat ≤ 16)
    (hblack : phaseBlackAtInt n ξ j lUpper) :
    phaseWeakBlackAtInt n ξ j lLower := by
  have hsmall : (9 ^ (j - j) * 2 ^ (lUpper - lLower).toNat : ℝ) *
      |balancedPhaseInt n j lUpper ξ| < 1 / 2 := by
    have hweak := collarAmplification_lt_weak 0 (lUpper - lLower).toNat
      |balancedPhaseInt n j lUpper ξ| (by omega) hgap (abs_nonneg _) hblack
    simpa using (lt_trans hweak (by norm_num : (1 / 100 : ℝ) < 1 / 2))
  have hscale := balancedPhaseInt_from_corner_of_small n ξ j lUpper j lLower
    le_rfl hl hsmall
  unfold phaseWeakBlackAtInt
  rw [hscale, abs_mul]
  have hK : 0 ≤ (9 ^ (j - j) * 2 ^ (lUpper - lLower).toNat : ℝ) := by
    positivity
  rw [abs_of_nonneg hK]
  have hweak := collarAmplification_lt_weak 0 (lUpper - lLower).toNat
    |balancedPhaseInt n j lUpper ξ| (by omega) hgap (abs_nonneg _) hblack
  simpa using hweak.le

/-- Every southeast transport from a black corner with both coordinate
exponents at most sixteen is weakly black, with exact no-wrap scaling. -/
theorem weak_of_black_bounded_transport (n : ℕ) (ξ : ZMod (3 ^ n))
    (j₀ j : ℕ) (l₀ l : ℤ) (hj : j₀ ≤ j) (hl : l ≤ l₀)
    (ha : j - j₀ ≤ 16) (hb : (l₀ - l).toNat ≤ 16)
    (hblack : phaseBlackAtInt n ξ j₀ l₀) :
    phaseWeakBlackAtInt n ξ j l := by
  have hsmall : (9 ^ (j - j₀) * 2 ^ (l₀ - l).toNat : ℝ) *
      |balancedPhaseInt n j₀ l₀ ξ| < 1 / 2 := by
    have hweak := collarAmplification_lt_weak (j - j₀) (l₀ - l).toNat
      |balancedPhaseInt n j₀ l₀ ξ| ha hb (abs_nonneg _) hblack
    exact lt_trans hweak (by norm_num)
  have hscale := balancedPhaseInt_from_corner_of_small n ξ j₀ l₀ j l hj hl hsmall
  unfold phaseWeakBlackAtInt
  rw [hscale, abs_mul]
  have hK : 0 ≤ (9 ^ (j - j₀) * 2 ^ (l₀ - l).toNat : ℝ) := by positivity
  rw [abs_of_nonneg hK]
  have hweak := collarAmplification_lt_weak (j - j₀) (l₀ - l).toNat
    |balancedPhaseInt n j₀ l₀ ξ| ha hb (abs_nonneg _) hblack
  exact hweak.le

/-- A west collar point at or above the corner height is white after bounded
southeast transport to the corner's west neighbor. -/
theorem west_at_or_above_top_white (n j₀ j' : ℕ) (l₀ l' : ℤ)
    (ξ : ZMod (3 ^ n)) (hj₀ : 0 < j₀)
    (hleft : ¬ phaseBlackAtInt n ξ (j₀ - 1) l₀)
    (hcorner : phaseBlackAtInt n ξ j₀ l₀)
    (hj' : j' < j₀) (hl : l₀ ≤ l')
    (ha : j₀ - 1 - j' ≤ 16) (hb : (l' - l₀).toNat ≤ 16) :
    ¬ phaseBlackAtInt n ξ j' l' := by
  intro hblack
  have hweak := weak_of_black_bounded_transport n ξ j' (j₀ - 1) l' l₀
    (by omega) hl ha hb hblack
  apply hleft
  apply phaseBlackAtInt_of_weak_of_east n (j₀ - 1) l₀ ξ hweak
  simpa [Nat.sub_add_cancel hj₀] using hcorner

/-- A west collar point below the corner is white: bounded transports provide
the east weak-neighbor strip needed to propagate up the west column. -/
theorem west_below_top_white (n j₀ j' : ℕ) (l₀ l' : ℤ)
    (ξ : ZMod (3 ^ n)) (hj₀ : 0 < j₀)
    (hleft : ¬ phaseBlackAtInt n ξ (j₀ - 1) l₀)
    (hcorner : phaseBlackAtInt n ξ j₀ l₀)
    (hj' : j' < j₀) (hl : l' < l₀)
    (ha : j₀ - 1 - j' ≤ 16) (hb : (l₀ - l').toNat ≤ 16) :
    ¬ phaseBlackAtInt n ξ j' l' := by
  intro hblack
  have hbase := weak_of_black_bounded_transport n ξ j' (j₀ - 1) l' l'
    (by omega) le_rfl ha (by simp) hblack
  let a : ℕ := (l₀ - l').toNat
  have hheight : l' + a = l₀ := by
    dsimp [a]
    have hnonneg : 0 ≤ l₀ - l' := by omega
    rw [Int.toNat_of_nonneg hnonneg]
    ring
  have heast : ∀ s ≤ a, phaseWeakBlackAtInt n ξ j₀ (l' + s) := by
    intro s hs
    apply weak_of_black_bounded_transport n ξ j₀ j₀ l₀ (l' + s)
      le_rfl
    · have : l' + s ≤ l₀ := by omega
      exact this
    · simp
    · have hnonneg : 0 ≤ l₀ - (l' + s) := by omega
      have hbaseNonneg : 0 ≤ l₀ - l' := by omega
      have hle : l₀ - (l' + s) ≤ l₀ - l' := by omega
      have hcast : ((l₀ - (l' + s)).toNat : ℤ) ≤ ((l₀ - l').toNat : ℤ) := by
        rw [Int.toNat_of_nonneg hnonneg, Int.toNat_of_nonneg hbaseNonneg]
        exact hle
      have hnat : (l₀ - (l' + s)).toNat ≤ (l₀ - l').toNat := by
        exact_mod_cast hcast
      exact hnat.trans hb
    · exact hcorner
  exact west_below_top_contradiction n j₀ a l₀ l' ξ hj₀ hleft hcorner hbase heast hheight

/-- Both west height cases under the coordinate bounds supplied by a
sixteen-unit collar. -/
theorem west_white_of_coordinate_bounds (n j₀ j' : ℕ) (l₀ l' : ℤ)
    (ξ : ZMod (3 ^ n)) (hj₀ : 0 < j₀)
    (hleft : ¬ phaseBlackAtInt n ξ (j₀ - 1) l₀)
    (hcorner : phaseBlackAtInt n ξ j₀ l₀)
    (hj' : j' < j₀) (hcol : j₀ - j' ≤ 16)
    (hheight : (l' - l₀).natAbs ≤ 16) :
    ¬ phaseBlackAtInt n ξ j' l' := by
  have ha : j₀ - 1 - j' ≤ 16 := by omega
  by_cases hl : l₀ ≤ l'
  · apply west_at_or_above_top_white n j₀ j' l₀ l' ξ hj₀ hleft hcorner hj' hl ha
    have hnonneg : 0 ≤ l' - l₀ := by omega
    calc
      (l' - l₀).toNat = (l' - l₀).natAbs := by
        rw [← Int.ofNat_inj]
        exact (Int.toNat_of_nonneg hnonneg).trans (Int.natAbs_of_nonneg hnonneg).symm
      _ ≤ 16 := hheight
  · have hbelow : l' < l₀ := by omega
    apply west_below_top_white n j₀ j' l₀ l' ξ hj₀ hleft hcorner hj' hbelow ha
    have hnonneg : 0 ≤ l₀ - l' := by omega
    calc
      (l₀ - l').toNat = (l₀ - l').natAbs := by
        rw [← Int.ofNat_inj]
        exact (Int.toNat_of_nonneg hnonneg).trans (Int.natAbs_of_nonneg hnonneg).symm
      _ = (l' - l₀).natAbs := by
        calc
          (l₀ - l').natAbs = (-(l₀ - l')).natAbs := (Int.natAbs_neg _).symm
          _ = (l' - l₀).natAbs := by
            congr 1
            ring
      _ ≤ 16 := hheight

/-- Multiplicative form of an Appendix E triangle on the integer-height
lattice. -/
def inPhaseTriangleIntMul (n : ℕ) (ξ : ZMod (3 ^ n))
    (j₀ : ℕ) (l₀ : ℤ) (j : ℕ) (l : ℤ) : Prop :=
  j₀ ≤ j ∧ l ≤ l₀ ∧
    (9 ^ (j - j₀) * 2 ^ (l₀ - l).toNat : ℝ) *
      |balancedPhaseInt n j₀ l₀ ξ| ≤ localEpsilon

/-- A point lies in the literal Appendix E collar of a multiplicative triangle
when it is within sixteen Euclidean lattice units of one of its lattice
points. -/
def withinPhaseTriangleCollarInt (n : ℕ) (ξ : ZMod (3 ^ n))
    (j₀ : ℕ) (l₀ : ℤ) (p : ℕ × ℤ) : Prop :=
  ∃ q, inPhaseTriangleIntMul n ξ j₀ l₀ q.1 q.2 ∧ withinPhaseCollarInt p q

/-- A triangle point at vertical depth `s` extends to every top-row point
whose horizontal `9`-power is bounded by its vertical `2`-power. -/
theorem inPhaseTriangleIntMul_top_extend
    (n j₀ j r s : ℕ) (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (htri : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (hjr : j ≤ r)
    (hs : (l₀ - l).toNat = s)
    (hpow : (9 : ℝ) ^ (r - j) ≤ 2 ^ s) :
    inPhaseTriangleIntMul n ξ j₀ l₀ r l₀ := by
  rcases htri with ⟨hj₀, hl, hsize⟩
  refine ⟨le_trans hj₀ hjr, le_rfl, ?_⟩
  rw [show r - j₀ = (r - j) + (j - j₀) by omega, pow_add]
  simp only [Int.sub_self, Int.toNat_zero, pow_zero, mul_one]
  rw [hs] at hsize
  have hnonneg : 0 ≤ (9 : ℝ) ^ (j - j₀) * |balancedPhaseInt n j₀ l₀ ξ| := by
    positivity
  calc
    (9 : ℝ) ^ (r - j) * (9 : ℝ) ^ (j - j₀) *
        |balancedPhaseInt n j₀ l₀ ξ| =
        ((9 : ℝ) ^ (r - j)) *
          ((9 : ℝ) ^ (j - j₀) * |balancedPhaseInt n j₀ l₀ ξ|) := by ring
    _ ≤ (2 : ℝ) ^ s *
          ((9 : ℝ) ^ (j - j₀) * |balancedPhaseInt n j₀ l₀ ξ|) :=
      mul_le_mul_of_nonneg_right hpow hnonneg
    _ = ((9 : ℝ) ^ (j - j₀) * (2 : ℝ) ^ s) *
          |balancedPhaseInt n j₀ l₀ ξ| := by ring
    _ ≤ localEpsilon := hsize

/-- Integer form of `log 2 / log 9 > 5 / 16`, used without logarithms in
the first-passage top-row comparison. -/
theorem pow_nine_five_div_sixteen_le_two (s : ℕ) :
    (9 : ℝ) ^ (5 * (s / 16)) ≤ 2 ^ s := by
  have hbase : (9 : ℝ) ^ 5 ≤ 2 ^ 16 := by norm_num
  have hpow : ((9 : ℝ) ^ 5) ^ (s / 16) ≤ (2 ^ 16 : ℝ) ^ (s / 16) := by
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hindex : 16 * (s / 16) ≤ s := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self s 16
  calc
    (9 : ℝ) ^ (5 * (s / 16)) = ((9 : ℝ) ^ 5) ^ (s / 16) := by
      rw [pow_mul]
    _ ≤ (2 ^ 16 : ℝ) ^ (s / 16) := hpow
    _ = (2 : ℝ) ^ (16 * (s / 16)) := by rw [pow_mul]
    _ ≤ 2 ^ s := by
      exact pow_le_pow_right₀ (by norm_num) hindex

/-- The integer top-row witness obtained from a triangle point `s` rows
below its top. -/
theorem inPhaseTriangleIntMul_top_five_div_sixteen
    (n j₀ j s : ℕ) (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (htri : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (hs : (l₀ - l).toNat = s) :
    inPhaseTriangleIntMul n ξ j₀ l₀ (j + 5 * (s / 16)) l₀ := by
  apply inPhaseTriangleIntMul_top_extend n j₀ j (j + 5 * (s / 16)) s l₀ l ξ
    htri (by omega) hs
  simpa using pow_nine_five_div_sixteen_le_two s

/-- The multiplicative and logarithmic descriptions of an integer-height
Appendix E triangle agree whenever its corner phase is nonzero. -/
theorem inPhaseTriangleIntMul_iff_log (n : ℕ)
    (ξ : ZMod (3 ^ n)) (j₀ : ℕ) (l₀ : ℤ) (j : ℕ) (l : ℤ)
    (hcorner : 0 < |balancedPhaseInt n j₀ l₀ ξ|) :
    inPhaseTriangleIntMul n ξ j₀ l₀ j l ↔
      inPhaseTriangleInt j₀ l₀
        (Real.log (localEpsilon / |balancedPhaseInt n j₀ l₀ ξ|)) j l := by
  let a : ℕ := j - j₀
  let b : ℕ := (l₀ - l).toNat
  let K : ℝ := 9 ^ a * 2 ^ b
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hε : 0 < localEpsilon := by norm_num [localEpsilon]
  have hlogK : Real.log K =
      (a : ℝ) * Real.log 9 + (b : ℝ) * Real.log 2 := by
    dsimp [K]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow]
  have hsize : K * |balancedPhaseInt n j₀ l₀ ξ| ≤ localEpsilon ↔
      Real.log K ≤ Real.log (localEpsilon / |balancedPhaseInt n j₀ l₀ ξ|) := by
    calc
      K * |balancedPhaseInt n j₀ l₀ ξ| ≤ localEpsilon ↔
          K ≤ localEpsilon / |balancedPhaseInt n j₀ l₀ ξ| :=
        (le_div_iff₀ hcorner).symm
      _ ↔ Real.log K ≤ Real.log
          (localEpsilon / |balancedPhaseInt n j₀ l₀ ξ|) :=
        (Real.log_le_log_iff hK (div_pos hε hcorner)).symm
  unfold inPhaseTriangleIntMul inPhaseTriangleInt
  constructor
  · rintro ⟨hj, hl, htriangle⟩
    refine ⟨hj, hl, ?_⟩
    have hjReal : (j : ℝ) - (j₀ : ℝ) = (a : ℝ) := by
      dsimp [a]
      exact (Nat.cast_sub hj).symm
    rw [hjReal, ← hlogK]
    apply hsize.mp
    simpa only [K, a, b] using htriangle
  · rintro ⟨hj, hl, htriangle⟩
    refine ⟨hj, hl, ?_⟩
    have hjReal : (j : ℝ) - (j₀ : ℝ) = (a : ℝ) := by
      dsimp [a]
      exact (Nat.cast_sub hj).symm
    apply hsize.mpr
    rw [hlogK]
    simpa only [hjReal, a, b] using htriangle

/-- A point on the corner column and below the corner is weakly black when it
is at most sixteen heights below any point of the same multiplicative
triangle. This is the discrete form of Appendix E.3's logarithmic west-strip
estimate. -/
theorem weak_corner_column_below_near_triangle_point (n : ℕ)
    (ξ : ZMod (3 ^ n)) (j₀ jq : ℕ) (l₀ lq lp : ℤ)
    (htri : inPhaseTriangleIntMul n ξ j₀ l₀ jq lq)
    (hlp : lp ≤ l₀) (hgap : lq - lp ≤ 16) :
    phaseWeakBlackAtInt n ξ j₀ lp := by
  let dq : ℕ := (l₀ - lq).toNat
  let dp : ℕ := (l₀ - lp).toNat
  have hq : lq ≤ l₀ := htri.2.1
  have hdq : ((dq : ℕ) : ℤ) = l₀ - lq := by
    dsimp [dq]
    rw [Int.toNat_of_nonneg (by omega)]
  have hdp : ((dp : ℕ) : ℤ) = l₀ - lp := by
    dsimp [dp]
    rw [Int.toNat_of_nonneg (by omega)]
  have hdle : dp ≤ dq + 16 := by
    have : (dp : ℤ) ≤ (dq : ℤ) + 16 := by rw [hdp, hdq]; omega
    exact_mod_cast this
  have hpow : (2 : ℝ) ^ dp ≤ 2 ^ dq * 2 ^ 16 := by
    calc
      (2 : ℝ) ^ dp ≤ 2 ^ (dq + 16) := pow_le_pow_right₀ (by norm_num) hdle
      _ = 2 ^ dq * 2 ^ 16 := by rw [pow_add]
  have htwodq : (2 : ℝ) ^ dq * |balancedPhaseInt n j₀ l₀ ξ| ≤ localEpsilon := by
    have hK : (2 : ℝ) ^ dq ≤ 9 ^ (jq - j₀) * 2 ^ dq := by
      have hone : (1 : ℝ) ≤ (9 : ℝ) ^ (jq - j₀) := by
        exact one_le_pow₀ (by norm_num)
      calc
        (2 : ℝ) ^ dq = 1 * 2 ^ dq := by ring
        _ ≤ 9 ^ (jq - j₀) * 2 ^ dq :=
          mul_le_mul_of_nonneg_right hone (by positivity)
    have hmul : (2 : ℝ) ^ dq * |balancedPhaseInt n j₀ l₀ ξ| ≤
        (9 : ℝ) ^ (jq - j₀) * 2 ^ dq * |balancedPhaseInt n j₀ l₀ ξ| :=
      mul_le_mul_of_nonneg_right hK (abs_nonneg (balancedPhaseInt n j₀ l₀ ξ))
    exact hmul.trans (by simpa [dq] using htri.2.2)
  have hbound : (2 : ℝ) ^ dp * |balancedPhaseInt n j₀ l₀ ξ| < 1 / 100 := by
    calc
      (2 : ℝ) ^ dp * |balancedPhaseInt n j₀ l₀ ξ| ≤
          (2 : ℝ) ^ 16 * ((2 : ℝ) ^ dq * |balancedPhaseInt n j₀ l₀ ξ|) := by
        calc
          (2 : ℝ) ^ dp * |balancedPhaseInt n j₀ l₀ ξ| ≤
              ((2 : ℝ) ^ dq * 2 ^ 16) * |balancedPhaseInt n j₀ l₀ ξ| :=
            mul_le_mul_of_nonneg_right hpow (abs_nonneg (balancedPhaseInt n j₀ l₀ ξ))
          _ = (2 : ℝ) ^ 16 * ((2 : ℝ) ^ dq * |balancedPhaseInt n j₀ l₀ ξ|) := by
            ring
      _ ≤ (2 : ℝ) ^ 16 * localEpsilon :=
        mul_le_mul_of_nonneg_left htwodq (by positivity : 0 ≤ (2 : ℝ) ^ 16)
      _ < 1 / 100 := by norm_num [localEpsilon]
  have hsmall : (9 ^ (j₀ - j₀) * 2 ^ dp : ℝ) *
      |balancedPhaseInt n j₀ l₀ ξ| < 1 / 2 := by
    simpa [dp] using (lt_trans hbound (by norm_num : (1 / 100 : ℝ) < 1 / 2))
  have hscale := balancedPhaseInt_from_corner_of_small n ξ j₀ l₀ j₀ lp
    le_rfl hlp hsmall
  unfold phaseWeakBlackAtInt
  rw [hscale, abs_mul]
  have hnonneg : 0 ≤ (9 ^ (j₀ - j₀) * 2 ^ dp : ℝ) := by positivity
  rw [abs_of_nonneg hnonneg]
  simpa [dp] using hbound.le

/-- The below-corner west collar case relative to an arbitrary nearby point of
the multiplicative triangle. -/
theorem west_below_top_white_of_triangle_witness (n j₀ j' jq : ℕ)
    (l₀ lq lp : ℤ) (ξ : ZMod (3 ^ n)) (hj₀ : 0 < j₀)
    (hleft : ¬ phaseBlackAtInt n ξ (j₀ - 1) l₀)
    (hcorner : phaseBlackAtInt n ξ j₀ l₀)
    (htri : inPhaseTriangleIntMul n ξ j₀ l₀ jq lq)
    (hj' : j' < j₀) (hlp : lp < l₀)
    (ha : j₀ - 1 - j' ≤ 16) (hnear : lq - lp ≤ 16) :
    ¬ phaseBlackAtInt n ξ j' lp := by
  intro hblack
  have hbase := weak_of_black_bounded_transport n ξ j' (j₀ - 1) lp lp
    (by omega) le_rfl ha (by simp) hblack
  let a : ℕ := (l₀ - lp).toNat
  have hheight : lp + a = l₀ := by
    dsimp [a]
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ l₀ - lp)]
    ring
  have heast : ∀ s ≤ a, phaseWeakBlackAtInt n ξ j₀ (lp + s) := by
    intro s hs
    apply weak_corner_column_below_near_triangle_point n ξ j₀ jq l₀ lq (lp + s)
      htri
    · omega
    · omega
  exact west_below_top_contradiction n j₀ a l₀ lp ξ hj₀ hleft hcorner hbase heast hheight

/-- The literal triangle collar is white on the west of a nonzero corner. -/
theorem west_white_of_triangle_collar (n j₀ jp : ℕ) (l₀ lp : ℤ)
    (ξ : ZMod (3 ^ n)) (hj₀ : 0 < j₀)
    (hleft : ¬ phaseBlackAtInt n ξ (j₀ - 1) l₀)
    (hcorner : phaseBlackAtInt n ξ j₀ l₀)
    (hwest : jp < j₀)
    (hnear : withinPhaseTriangleCollarInt n ξ j₀ l₀ (jp, lp)) :
    ¬ phaseBlackAtInt n ξ jp lp := by
  rcases hnear with ⟨⟨jq, lq⟩, htri, hmetric⟩
  have hjq : j₀ ≤ jq := htri.1
  have hcolDist := columnDist_le_sixteen_of_withinPhaseCollarInt hmetric
  have hjp : jp ≤ jq := by omega
  have hcol : j₀ - jp ≤ 16 := by
    change Nat.dist jp jq ≤ 16 at hcolDist
    have hdist : Nat.dist jp jq = jq - jp := Nat.dist_eq_sub_of_le hjp
    rw [hdist] at hcolDist
    omega
  have hheightDist := heightDist_le_sixteen_of_withinPhaseCollarInt hmetric
  by_cases htop : l₀ ≤ lp
  · apply west_at_or_above_top_white n j₀ jp l₀ lp ξ hj₀ hleft hcorner hwest htop
    · omega
    · have hq : lq ≤ l₀ := htri.2.1
      have hnonneg : 0 ≤ lp - l₀ := by omega
      have hbase : 0 ≤ lp - lq := by omega
      have hle : lp - l₀ ≤ lp - lq := by omega
      have hcast : ((lp - l₀).toNat : ℤ) ≤ ((lp - lq).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg hnonneg, Int.toNat_of_nonneg hbase]
        exact hle
      have hnat : (lp - l₀).toNat ≤ (lp - lq).toNat := by exact_mod_cast hcast
      have hdistEq : (lp - lq).toNat = (lp - lq).natAbs := by
        rw [← Int.ofNat_inj]
        exact (Int.toNat_of_nonneg hbase).trans (Int.natAbs_of_nonneg hbase).symm
      exact hnat.trans (by simpa [hdistEq] using hheightDist)
  · have hbelow : lp < l₀ := by omega
    apply west_below_top_white_of_triangle_witness n j₀ jp jq l₀ lq lp ξ hj₀
      hleft hcorner htri hwest hbelow
    · omega
    · have hcast : lq - lp ≤ ((lp - lq).natAbs : ℤ) := by
        calc
          lq - lp ≤ ((lq - lp).natAbs : ℤ) := Int.le_natAbs (a := lq - lp)
          _ = ((lp - lq).natAbs : ℤ) := by
            congr 1
            calc
              (lq - lp).natAbs = (-(lq - lp)).natAbs := (Int.natAbs_neg _).symm
              _ = (lp - lq).natAbs := by
                congr 1
                ring
      have hdistCast : ((lp - lq).natAbs : ℤ) ≤ 16 := by exact_mod_cast hheightDist
      omega

/-- Exact integer-height phase scaling throughout a multiplicative triangle. -/
theorem balancedPhaseInt_from_corner_of_triangle (n : ℕ)
    (ξ : ZMod (3 ^ n)) (j₀ : ℕ) (l₀ : ℤ) (j : ℕ) (l : ℤ)
    (htri : inPhaseTriangleIntMul n ξ j₀ l₀ j l) :
    balancedPhaseInt n j l ξ =
      (9 ^ (j - j₀) * 2 ^ (l₀ - l).toNat : ℝ) *
        balancedPhaseInt n j₀ l₀ ξ := by
  rcases htri with ⟨hj, hl, hsize⟩
  have hεhalf : localEpsilon < (1 / 2 : ℝ) := by norm_num [localEpsilon]
  apply balancedPhaseInt_from_corner_of_small n ξ j₀ l₀ j l hj hl
  exact lt_of_le_of_lt hsize hεhalf

/-- Every integer-height lattice point of a multiplicative triangle is black. -/
theorem phaseBlackAtInt_of_inPhaseTriangleIntMul (n : ℕ)
    (ξ : ZMod (3 ^ n)) (j₀ : ℕ) (l₀ : ℤ) (j : ℕ) (l : ℤ)
    (htri : inPhaseTriangleIntMul n ξ j₀ l₀ j l) : phaseBlackAtInt n ξ j l := by
  unfold phaseBlackAtInt
  rw [balancedPhaseInt_from_corner_of_triangle n ξ j₀ l₀ j l htri, abs_mul]
  have hk : 0 ≤ (9 ^ (j - j₀) * 2 ^ (l₀ - l).toNat : ℝ) := by positivity
  rw [abs_of_nonneg hk]
  exact htri.2.2

/-- Appendix E.3 southeast collar case: an exterior southeast point within
sixteen Euclidean lattice units of a black corner is white. -/
theorem southeast_white_of_outside_triangle_in_collar (n : ℕ)
    (ξ : ZMod (3 ^ n)) (j₀ : ℕ) (l₀ : ℤ) (j : ℕ) (l : ℤ)
    (hcorner : phaseBlackAtInt n ξ j₀ l₀)
    (hj : j₀ ≤ j) (hl : l ≤ l₀)
    (hcollar : withinPhaseCollarInt (j, l) (j₀, l₀))
    (hout : ¬ inPhaseTriangleIntMul n ξ j₀ l₀ j l) :
    ¬ phaseBlackAtInt n ξ j l := by
  have ha : j - j₀ ≤ 16 := by
    have hdist := columnDist_le_sixteen_of_withinPhaseCollarInt hcollar
    rw [Nat.dist_eq_sub_of_le_right hj] at hdist
    exact hdist
  have hb : (l₀ - l).toNat ≤ 16 := by
    have hdist := heightDist_le_sixteen_of_withinPhaseCollarInt hcollar
    have hheight : (l - l₀).natAbs = (l₀ - l).toNat := by
      have hnonneg : 0 ≤ l₀ - l := by omega
      calc
        (l - l₀).natAbs = (-(l - l₀)).natAbs := (Int.natAbs_neg _).symm
        _ = (l₀ - l).natAbs := by
          congr 1
          ring
        _ = (l₀ - l).toNat := by
          rw [← Int.ofNat_inj]
          exact (Int.natAbs_of_nonneg hnonneg).trans
            (Int.toNat_of_nonneg hnonneg).symm
    rw [hheight] at hdist
    exact hdist
  have hsmall :
      (9 ^ (j - j₀) * 2 ^ (l₀ - l).toNat : ℝ) *
        |balancedPhaseInt n j₀ l₀ ξ| < 1 / 2 := by
    have hweak := collarAmplification_lt_weak (j - j₀) (l₀ - l).toNat
      |balancedPhaseInt n j₀ l₀ ξ| ha hb (abs_nonneg _) hcorner
    linarith
  intro hblack
  unfold phaseBlackAtInt at hblack
  rw [balancedPhaseInt_from_corner_of_small n ξ j₀ l₀ j l hj hl hsmall,
    abs_mul] at hblack
  have hK : 0 ≤ (9 ^ (j - j₀) * 2 ^ (l₀ - l).toNat : ℝ) := by positivity
  rw [abs_of_nonneg hK] at hblack
  apply hout
  exact ⟨hj, hl, hblack⟩

/-- The literal triangle collar is white at every southeast exterior point.
The nearby triangle witness supplies the extra at-most-sixteen exponents. -/
theorem southeast_white_of_triangle_collar (n j₀ jp : ℕ) (l₀ lp : ℤ)
    (ξ : ZMod (3 ^ n))
    (hj : j₀ ≤ jp) (hl : lp ≤ l₀)
    (hout : ¬ inPhaseTriangleIntMul n ξ j₀ l₀ jp lp)
    (hnear : withinPhaseTriangleCollarInt n ξ j₀ l₀ (jp, lp)) :
    ¬ phaseBlackAtInt n ξ jp lp := by
  rcases hnear with ⟨⟨jq, lq⟩, htri, hmetric⟩
  have hjq : j₀ ≤ jq := htri.1
  have hq : lq ≤ l₀ := htri.2.1
  have hcolDist := columnDist_le_sixteen_of_withinPhaseCollarInt hmetric
  change Nat.dist jp jq ≤ 16 at hcolDist
  have hjp : jp ≤ jq + 16 := by
    rcases le_total jp jq with hpq | hqp
    · omega
    · have heq : Nat.dist jp jq = jp - jq := by
        simpa [Nat.dist_comm] using Nat.dist_eq_sub_of_le hqp
      rw [heq] at hcolDist
      omega
  have hheightDist := heightDist_le_sixteen_of_withinPhaseCollarInt hmetric
  have hgap : lq - lp ≤ 16 := by
    have hcast : lq - lp ≤ ((lp - lq).natAbs : ℤ) := by
      calc
        lq - lp ≤ ((lq - lp).natAbs : ℤ) := Int.le_natAbs (a := lq - lp)
        _ = ((lp - lq).natAbs : ℤ) := by
          congr 1
          calc
            (lq - lp).natAbs = (-(lq - lp)).natAbs := (Int.natAbs_neg _).symm
            _ = (lp - lq).natAbs := by
              congr 1
              ring
    have hdistCast : ((lp - lq).natAbs : ℤ) ≤ 16 := by
      exact_mod_cast hheightDist
    omega
  let aq : ℕ := jq - j₀
  let ap : ℕ := jp - j₀
  let bq : ℕ := (l₀ - lq).toNat
  let bp : ℕ := (l₀ - lp).toNat
  have hap : ap ≤ aq + 16 := by
    dsimp [ap, aq]
    omega
  have hbp : bp ≤ bq + 16 := by
    have hcast : (bp : ℤ) ≤ (bq : ℤ) + 16 := by
      dsimp [bp, bq]
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
      omega
    exact_mod_cast hcast
  have hpow9 : (9 : ℝ) ^ ap ≤ 9 ^ aq * 9 ^ 16 := by
    calc
      (9 : ℝ) ^ ap ≤ 9 ^ (aq + 16) := pow_le_pow_right₀ (by norm_num) hap
      _ = 9 ^ aq * 9 ^ 16 := by rw [pow_add]
  have hpow2 : (2 : ℝ) ^ bp ≤ 2 ^ bq * 2 ^ 16 := by
    calc
      (2 : ℝ) ^ bp ≤ 2 ^ (bq + 16) := pow_le_pow_right₀ (by norm_num) hbp
      _ = 2 ^ bq * 2 ^ 16 := by rw [pow_add]
  have hK : (9 : ℝ) ^ ap * 2 ^ bp ≤
      (9 ^ aq * 2 ^ bq : ℝ) * (18 : ℝ) ^ 16 := by
    calc
      (9 : ℝ) ^ ap * 2 ^ bp ≤ (9 ^ aq * 9 ^ 16) * (2 ^ bq * 2 ^ 16) :=
        mul_le_mul hpow9 hpow2 (by positivity) (by positivity)
      _ = (9 ^ aq * 2 ^ bq : ℝ) * 18 ^ 16 := by
        rw [show (18 : ℝ) = 9 * 2 by norm_num, mul_pow]
        ring
  have hsmall : (9 ^ ap * 2 ^ bp : ℝ) *
      |balancedPhaseInt n j₀ l₀ ξ| < 1 / 2 := by
    have htri' : (9 ^ aq * 2 ^ bq : ℝ) *
        |balancedPhaseInt n j₀ l₀ ξ| ≤ localEpsilon := by
      simpa [aq, bq] using htri.2.2
    calc
      (9 ^ ap * 2 ^ bp : ℝ) * |balancedPhaseInt n j₀ l₀ ξ| ≤
          ((9 ^ aq * 2 ^ bq : ℝ) * 18 ^ 16) *
            |balancedPhaseInt n j₀ l₀ ξ| :=
        mul_le_mul_of_nonneg_right hK (abs_nonneg _)
      _ = (18 : ℝ) ^ 16 * ((9 ^ aq * 2 ^ bq : ℝ) *
            |balancedPhaseInt n j₀ l₀ ξ|) := by ring
      _ ≤ (18 : ℝ) ^ 16 * localEpsilon :=
        mul_le_mul_of_nonneg_left htri' (by positivity)
      _ < 1 / 2 := by norm_num [localEpsilon]
  intro hblack
  unfold phaseBlackAtInt at hblack
  rw [balancedPhaseInt_from_corner_of_small n ξ j₀ l₀ jp lp hj hl
    (by simpa [ap, bp] using hsmall), abs_mul] at hblack
  have hnonneg : 0 ≤ (9 ^ ap * 2 ^ bp : ℝ) := by positivity
  rw [abs_of_nonneg hnonneg] at hblack
  apply hout
  exact ⟨hj, hl, by simpa [ap, bp] using hblack⟩

/-- Iterate the no-wrap integer-height east recurrence along a weak-black
row. -/
theorem balancedPhaseInt_east_iter_of_weak (n j : ℕ) (l : ℤ) (a : ℕ)
    (ξ : ZMod (3 ^ n))
    (hweak : ∀ r < a, phaseWeakBlackAtInt n ξ (j + r) l) :
    balancedPhaseInt n (j + a) l ξ =
      (9 : ℝ) ^ a * balancedPhaseInt n j l ξ := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hprev := ih (fun r hr => hweak r (by omega))
      have hstep := balancedPhaseInt_east_of_weak n (j + a) l ξ
        (hweak a (by omega))
      rw [Nat.add_succ, hstep, hprev, pow_succ]
      ring

/-- Iterate the no-wrap integer-height north recurrence through a weak-black
vertical segment. -/
theorem balancedPhaseInt_north_iter_of_weak (n j : ℕ) (l : ℤ) (b : ℕ)
    (ξ : ZMod (3 ^ n))
    (hweak : ∀ s : ℤ, l - b < s → s ≤ l → phaseWeakBlackAtInt n ξ j s) :
    balancedPhaseInt n j (l - b) ξ =
      (2 : ℝ) ^ b * balancedPhaseInt n j l ξ := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hcurrent : phaseWeakBlackAtInt n ξ j (l - b) := by
        apply hweak
        · norm_num [Nat.cast_add]
        · omega
      unfold phaseWeakBlackAtInt at hcurrent
      have hstep := balancedPhaseInt_south_of_weak n j (l - b) ξ hcurrent
      have hprev := ih (fun s hs₁ hs₂ => hweak s (by omega) hs₂)
      have hheight : l - (b + 1) = (l - b) - 1 := by ring
      norm_num [Nat.cast_add]
      rw [hheight, hstep, hprev, pow_succ]
      ring

/-- The canonical integer top-row and vertical black paths put the originating
black point in their triangle. -/
theorem canonical_corner_contains_point_int {n j : ℕ} {l : ℤ}
    {j₀ : ℕ} {l₀ : ℤ} (ξ : ZMod (3 ^ n))
    (hj : j₀ ≤ j) (hl : l ≤ l₀)
    (hrow : ∀ r, j₀ ≤ r → r ≤ j → phaseBlackAtInt n ξ r l₀)
    (hvertical : ∀ s : ℤ, l ≤ s → s ≤ l₀ → phaseBlackAtInt n ξ j s)
    (hblack : phaseBlackAtInt n ξ j l) :
    inPhaseTriangleIntMul n ξ j₀ l₀ j l := by
  have heast := balancedPhaseInt_east_iter_of_weak n j₀ l₀ (j - j₀) ξ
    (fun r hr => phaseBlackAtInt_implies_weak n ξ (j₀ + r) l₀
      (hrow (j₀ + r) (by omega) (by omega)))
  have hjeq : j₀ + (j - j₀) = j := Nat.add_sub_of_le hj
  rw [hjeq] at heast
  have hlower := balancedPhaseInt_north_iter_of_weak n j l₀
    (l₀ - l).toNat ξ (fun s hs₁ hs₂ =>
      phaseBlackAtInt_implies_weak n ξ j s
        (hvertical s (by
          have hnonneg : 0 ≤ l₀ - l := by omega
          have hcast : ((l₀ - l).toNat : ℤ) = l₀ - l := Int.toNat_of_nonneg hnonneg
          rw [hcast] at hs₁
          omega) hs₂))
  have hleq : l₀ - (l₀ - l).toNat = l := by
    have hnonneg : 0 ≤ l₀ - l := by omega
    rw [Int.toNat_of_nonneg hnonneg]
    ring
  rw [hleq, heast] at hlower
  refine ⟨hj, hl, ?_⟩
  unfold phaseBlackAtInt at hblack
  rw [hlower, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ (l₀ - l).toNat),
    abs_of_nonneg (by positivity : 0 ≤ (9 : ℝ) ^ (j - j₀))] at hblack
  nlinarith

/-- Every primitive integer-height black point belongs to a canonical filled
triangle with white immediate north and west boundaries. -/
theorem black_point_has_filled_triangle_int {n j : ℕ} {l : ℤ}
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hblack : phaseBlackAtInt n ξ j l) :
    ∃ j₀ l₀,
      inPhaseTriangleIntMul n ξ j₀ l₀ j l ∧
      (∀ j' l', inPhaseTriangleIntMul n ξ j₀ l₀ j' l' →
        phaseBlackAtInt n ξ j' l') ∧
      (j₀ = 0 ∨ ¬ phaseBlackAtInt n ξ (j₀ - 1) l₀) ∧
      ¬ phaseBlackAtInt n ξ j (l₀ + 1) := by
  obtain ⟨l₀, hll₀, htop, hvertical, habove, _⟩ :=
    exists_black_top_of_primitive_int l hn hj ξ hξ hblack
  obtain ⟨j₀, hj₀j, hrow, hleft⟩ := exists_black_row_start_int n j l₀ ξ htop
  refine ⟨j₀, l₀,
    canonical_corner_contains_point_int ξ hj₀j hll₀ hrow hvertical hblack,
    ?_, hleft, habove⟩
  intro j' l' htri
  exact phaseBlackAtInt_of_inPhaseTriangleIntMul n ξ j₀ l₀ j' l' htri

/-- A primitive black point has a filled triangle whose selected full top row
is black and has a white north boundary at every column. -/
theorem black_point_has_full_top_triangle_int {n j : ℕ} {l : ℤ}
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hblack : phaseBlackAtInt n ξ j l) :
    ∃ j₀ j₁ l₀,
      inPhaseTriangleIntMul n ξ j₀ l₀ j l ∧
      inPhaseTriangleIntMul n ξ j₀ l₀ j₁ l₀ ∧
      (∀ r, j₀ ≤ r → r ≤ j₁ →
        phaseBlackAtInt n ξ r l₀ ∧ ¬ phaseBlackAtInt n ξ r (l₀ + 1)) ∧
      (∀ j' l', inPhaseTriangleIntMul n ξ j₀ l₀ j' l' →
        phaseBlackAtInt n ξ j' l') ∧
      (j₀ = 0 ∨ ¬ phaseBlackAtInt n ξ (j₀ - 1) l₀) := by
  obtain ⟨l₀, hll₀, htop, hvertical, habove, _⟩ :=
    exists_black_top_of_primitive_int l hn hj ξ hξ hblack
  obtain ⟨j₁, hjj₁, hrightBlack, hright, hrightwhite, _⟩ :=
    exists_black_rightmost_of_primitive_int l₀ hn hj ξ hξ htop
  obtain ⟨j₀, hj₀j, hleft, hleftedge⟩ :=
    exists_black_row_start_int n j l₀ ξ htop
  have hrow : ∀ r, j₀ ≤ r → r ≤ j₁ → phaseBlackAtInt n ξ r l₀ := by
    intro r hr₀ hr₁
    by_cases hr : r ≤ j
    · exact hleft r hr₀ hr
    · exact hright r (by omega) hr₁
  have hrightAbove : ¬ phaseBlackAtInt n ξ j₁ (l₀ + 1) := by
    intro hblackAbove
    have hweak := phaseBlackAtInt_implies_weak n ξ j₁ (l₀ + 1) hblackAbove
    have hjadd : j + (j₁ - j) = j₁ := Nat.add_sub_of_le hjj₁
    have hweak' : phaseWeakBlackAtInt n ξ (j + (j₁ - j)) (l₀ + 1) := by
      simpa [hjadd] using hweak
    have hprop := weakBlack_left_of_east_and_lower_segment n j (j₁ - j) l₀ ξ
      hweak' (fun r hr => hright (j + r) (by omega) (by omega))
    apply habove
    apply phaseBlackAtInt_of_weak_of_north n j (l₀ + 1) ξ hprop
    simpa using htop
  have haboveRow := no_black_above_top_segment n j₀ j₁ l₀ ξ (by omega) hrow hrightAbove
  have htri : inPhaseTriangleIntMul n ξ j₀ l₀ j l :=
    canonical_corner_contains_point_int ξ hj₀j hll₀ hleft hvertical hblack
  have htriRight : inPhaseTriangleIntMul n ξ j₀ l₀ j₁ l₀ := by
    apply canonical_corner_contains_point_int ξ (by omega) le_rfl hrow
    · intro s hs₀ hs₁
      have : s = l₀ := by omega
      simpa [this] using hrightBlack
    · exact hrightBlack
  refine ⟨j₀, j₁, l₀, htri, htriRight, ?_, ?_, hleftedge⟩
  · intro r hr₀ hr₁
    exact ⟨hrow r hr₀ hr₁, haboveRow r hr₀ hr₁⟩
  · intro j' l' htriangle
    exact phaseBlackAtInt_of_inPhaseTriangleIntMul n ξ j₀ l₀ j' l' htriangle

/-- A selected right endpoint is the literal right endpoint of the associated
multiplicative triangle's top row. -/
theorem triangle_top_le_rightmost (n j₀ j₁ jq : ℕ) (l₀ : ℤ)
    (ξ : ZMod (3 ^ n))
    (htriRight : inPhaseTriangleIntMul n ξ j₀ l₀ j₁ l₀)
    (hfill : ∀ j' l', inPhaseTriangleIntMul n ξ j₀ l₀ j' l' →
      phaseBlackAtInt n ξ j' l')
    (hright : ¬ phaseBlackAtInt n ξ (j₁ + 1) l₀)
    (htop : inPhaseTriangleIntMul n ξ j₀ l₀ jq l₀) :
    jq ≤ j₁ := by
  by_contra hnot
  have hbase : j₀ ≤ j₁ := htriRight.1
  have hj₀ : j₀ ≤ j₁ + 1 := by omega
  have hjq : j₁ + 1 ≤ jq := by omega
  apply hright
  apply hfill (j₁ + 1) l₀
  refine ⟨hj₀, le_rfl, ?_⟩
  have hpow : (9 : ℝ) ^ (j₁ + 1 - j₀) ≤ 9 ^ (jq - j₀) := by
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right hjq j₀)
  have htopBound : (9 : ℝ) ^ (jq - j₀) * 2 ^ (l₀ - l₀).toNat *
      |balancedPhaseInt n j₀ l₀ ξ| ≤ localEpsilon := htop.2.2
  have hpow' : (9 : ℝ) ^ (j₁ + 1 - j₀) * 2 ^ (l₀ - l₀).toNat ≤
      9 ^ (jq - j₀) * 2 ^ (l₀ - l₀).toNat :=
    mul_le_mul_of_nonneg_right hpow (by positivity)
  calc
    (9 : ℝ) ^ (j₁ + 1 - j₀) * 2 ^ (l₀ - l₀).toNat *
        |balancedPhaseInt n j₀ l₀ ξ| ≤
        (9 : ℝ) ^ (jq - j₀) * 2 ^ (l₀ - l₀).toNat *
          |balancedPhaseInt n j₀ l₀ ξ| := by
      exact mul_le_mul_of_nonneg_right hpow' (abs_nonneg _)
    _ ≤ localEpsilon := htopBound

/-- Every triangle point projects vertically to a point of its top row. -/
theorem triangle_top_of_triangle (n j₀ jq : ℕ) (l₀ lq : ℤ)
    (ξ : ZMod (3 ^ n))
    (htri : inPhaseTriangleIntMul n ξ j₀ l₀ jq lq) :
    inPhaseTriangleIntMul n ξ j₀ l₀ jq l₀ := by
  refine ⟨htri.1, le_rfl, ?_⟩
  have hpow : (1 : ℝ) ≤ 2 ^ (l₀ - lq).toNat := one_le_pow₀ (by norm_num)
  have hnonneg : 0 ≤ (9 : ℝ) ^ (jq - j₀) *
      |balancedPhaseInt n j₀ l₀ ξ| := by positivity
  have hle : (9 : ℝ) ^ (jq - j₀) *
      |balancedPhaseInt n j₀ l₀ ξ| ≤
      ((9 : ℝ) ^ (jq - j₀) * 2 ^ (l₀ - lq).toNat) *
        |balancedPhaseInt n j₀ l₀ ξ| := by
    calc
      (9 : ℝ) ^ (jq - j₀) * |balancedPhaseInt n j₀ l₀ ξ| =
          1 * ((9 : ℝ) ^ (jq - j₀) *
            |balancedPhaseInt n j₀ l₀ ξ|) := by ring
      _ ≤ 2 ^ (l₀ - lq).toNat * ((9 : ℝ) ^ (jq - j₀) *
            |balancedPhaseInt n j₀ l₀ ξ|) :=
        mul_le_mul_of_nonneg_right hpow hnonneg
      _ = ((9 : ℝ) ^ (jq - j₀) * 2 ^ (l₀ - lq).toNat) *
            |balancedPhaseInt n j₀ l₀ ξ| := by ring
  simpa using hle.trans htri.2.2

/-- A northeast point above the selected full top segment is white when its
descent to that segment has height at most sixteen. -/
theorem northeast_inside_top_segment_white (n j₀ j₁ j' : ℕ)
    (l₀ l' : ℤ) (ξ : ZMod (3 ^ n))
    (hrow : ∀ r, j₀ ≤ r → r ≤ j₁ → phaseBlackAtInt n ξ r l₀)
    (habove : ∀ r, j₀ ≤ r → r ≤ j₁ → ¬ phaseBlackAtInt n ξ r (l₀ + 1))
    (hj₀ : j₀ ≤ j') (hj₁ : j' ≤ j₁) (hl : l₀ < l')
    (hgap : (l' - (l₀ + 1)).toNat ≤ 16) :
    ¬ phaseBlackAtInt n ξ j' l' := by
  intro hblack
  have hweak := weak_below_of_black_of_height_gap_le_sixteen n j' l' (l₀ + 1)
    ξ (by omega) hgap hblack
  have hblackBelow := phaseBlackAtInt_of_weak_of_north n j' (l₀ + 1) ξ hweak
    (by simpa using hrow j' hj₀ hj₁)
  exact habove j' hj₀ hj₁ hblackBelow

/-- A northeast collar point lying at most sixteen columns to the right of
the selected top endpoint is white. -/
theorem northeast_right_extension_white (n j₁ j' : ℕ)
    (l₀ l' : ℤ) (ξ : ZMod (3 ^ n))
    (hendpoint : phaseBlackAtInt n ξ j₁ l₀)
    (habove : ¬ phaseBlackAtInt n ξ j₁ (l₀ + 1))
    (hj : j₁ ≤ j') (hl : l₀ < l')
    (ha : j' - j₁ ≤ 16) (hb : (l' - (l₀ + 1)).toNat ≤ 16) :
    ¬ phaseBlackAtInt n ξ j' l' := by
  intro hblack
  have hupper := weak_of_black_bounded_transport n ξ j' j' l' (l₀ + 1)
    le_rfl (by omega) (by omega) hb hblack
  have hlower : ∀ r ≤ j' - j₁, phaseWeakBlackAtInt n ξ (j₁ + r) l₀ := by
    intro r hr
    apply weak_of_black_bounded_transport n ξ j₁ (j₁ + r) l₀ l₀
      (by omega) le_rfl
    · simpa using hr.trans ha
    · simp
    · exact hendpoint
  have hupper' : phaseWeakBlackAtInt n ξ (j₁ + (j' - j₁)) (l₀ + 1) := by
    have hjadd : j₁ + (j' - j₁) = j' := Nat.add_sub_of_le hj
    simpa [hjadd] using hupper
  have hprop := weakBlack_left_of_east_and_weak_lower_segment n j₁ (j' - j₁) l₀ ξ
    hupper' hlower
  apply habove
  apply phaseBlackAtInt_of_weak_of_north n j₁ (l₀ + 1) ξ hprop
  simpa using hendpoint

/-- The literal triangle collar is white at every northeast point that is not
west of its selected corner. -/
theorem northeast_white_of_triangle_collar (n j₀ j₁ jp : ℕ)
    (l₀ lp : ℤ) (ξ : ZMod (3 ^ n))
    (htriRight : inPhaseTriangleIntMul n ξ j₀ l₀ j₁ l₀)
    (hrow : ∀ r, j₀ ≤ r → r ≤ j₁ → phaseBlackAtInt n ξ r l₀)
    (habove : ∀ r, j₀ ≤ r → r ≤ j₁ → ¬ phaseBlackAtInt n ξ r (l₀ + 1))
    (hfill : ∀ j' l', inPhaseTriangleIntMul n ξ j₀ l₀ j' l' →
      phaseBlackAtInt n ξ j' l')
    (hright : ¬ phaseBlackAtInt n ξ (j₁ + 1) l₀)
    (hj : j₀ ≤ jp) (hl : l₀ < lp)
    (hnear : withinPhaseTriangleCollarInt n ξ j₀ l₀ (jp, lp)) :
    ¬ phaseBlackAtInt n ξ jp lp := by
  rcases hnear with ⟨⟨jq, lq⟩, htri, hmetric⟩
  have htop := triangle_top_of_triangle n j₀ jq l₀ lq ξ htri
  have hjq : jq ≤ j₁ :=
    triangle_top_le_rightmost n j₀ j₁ jq l₀ ξ htriRight hfill hright htop
  have hcol := columnDist_le_sixteen_of_withinPhaseCollarInt hmetric
  change Nat.dist jp jq ≤ 16 at hcol
  have hjp : jp ≤ j₁ + 16 := by
    rcases le_total jp jq with hpq | hqp
    · omega
    · have heq : Nat.dist jp jq = jp - jq := by
        simpa [Nat.dist_comm] using Nat.dist_eq_sub_of_le hqp
      rw [heq] at hcol
      omega
  have hheight := heightDist_le_sixteen_of_withinPhaseCollarInt hmetric
  have hgap : (lp - (l₀ + 1)).toNat ≤ 16 := by
    have hq : lq ≤ l₀ := htri.2.1
    have hnonneg : 0 ≤ lp - (l₀ + 1) := by omega
    have hbase : 0 ≤ lp - lq := by omega
    have hle : lp - (l₀ + 1) ≤ lp - lq := by omega
    have hcast : ((lp - (l₀ + 1)).toNat : ℤ) ≤ ((lp - lq).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hnonneg, Int.toNat_of_nonneg hbase]
      exact hle
    have hnat : (lp - (l₀ + 1)).toNat ≤ (lp - lq).toNat := by
      exact_mod_cast hcast
    have heq : (lp - lq).toNat = (lp - lq).natAbs := by
      rw [← Int.ofNat_inj]
      exact (Int.toNat_of_nonneg hbase).trans (Int.natAbs_of_nonneg hbase).symm
    exact hnat.trans (by simpa [heq] using hheight)
  by_cases hinside : jp ≤ j₁
  · exact northeast_inside_top_segment_white n j₀ j₁ jp l₀ lp ξ hrow habove
      hj hinside hl hgap
  · have hjright : j₁ ≤ jp := by omega
    have ha : jp - j₁ ≤ 16 := by omega
    exact northeast_right_extension_white n j₁ jp l₀ lp ξ
      (hrow j₁ htriRight.1 le_rfl) (habove j₁ htriRight.1 le_rfl)
      hjright hl ha hgap

/-- The literal width-sixteen collar of one selected triangle is white outside
that triangle. -/
theorem selected_triangle_collar_white (n j₀ j₁ jp : ℕ)
    (l₀ lp : ℤ) (ξ : ZMod (3 ^ n))
    (htriRight : inPhaseTriangleIntMul n ξ j₀ l₀ j₁ l₀)
    (hrow : ∀ r, j₀ ≤ r → r ≤ j₁ → phaseBlackAtInt n ξ r l₀)
    (habove : ∀ r, j₀ ≤ r → r ≤ j₁ → ¬ phaseBlackAtInt n ξ r (l₀ + 1))
    (hfill : ∀ j' l', inPhaseTriangleIntMul n ξ j₀ l₀ j' l' →
      phaseBlackAtInt n ξ j' l')
    (hright : ¬ phaseBlackAtInt n ξ (j₁ + 1) l₀)
    (hleft : j₀ = 0 ∨ ¬ phaseBlackAtInt n ξ (j₀ - 1) l₀)
    (hout : ¬ inPhaseTriangleIntMul n ξ j₀ l₀ jp lp)
    (hnear : withinPhaseTriangleCollarInt n ξ j₀ l₀ (jp, lp)) :
    ¬ phaseBlackAtInt n ξ jp lp := by
  by_cases hwest : jp < j₀
  · rcases hleft with hz | hleft
    · omega
    · exact west_white_of_triangle_collar n j₀ jp l₀ lp ξ (by omega)
        hleft (hrow j₀ le_rfl htriRight.1) hwest hnear
  · have hj : j₀ ≤ jp := by omega
    by_cases hl : lp ≤ l₀
    · exact southeast_white_of_triangle_collar n j₀ jp l₀ lp ξ hj hl hout hnear
    · exact northeast_white_of_triangle_collar n j₀ j₁ jp l₀ lp ξ
        htriRight hrow habove hfill hright hj (by omega) hnear

/-- A black point one lattice step from a selected triangle cannot lie outside
it, because that step is in the literal white collar. -/
theorem selected_triangle_black_neighbor_mem (n j₀ j₁ : ℕ)
    (l₀ : ℤ) (ξ : ZMod (3 ^ n)) (p q : ℕ × ℤ)
    (htriRight : inPhaseTriangleIntMul n ξ j₀ l₀ j₁ l₀)
    (hrow : ∀ r, j₀ ≤ r → r ≤ j₁ → phaseBlackAtInt n ξ r l₀)
    (habove : ∀ r, j₀ ≤ r → r ≤ j₁ → ¬ phaseBlackAtInt n ξ r (l₀ + 1))
    (hfill : ∀ j' l', inPhaseTriangleIntMul n ξ j₀ l₀ j' l' →
      phaseBlackAtInt n ξ j' l')
    (hright : ¬ phaseBlackAtInt n ξ (j₁ + 1) l₀)
    (hleft : j₀ = 0 ∨ ¬ phaseBlackAtInt n ξ (j₀ - 1) l₀)
    (hp : inPhaseTriangleIntMul n ξ j₀ l₀ p.1 p.2)
    (hqblack : phaseBlackAtInt n ξ q.1 q.2)
    (hstep : latticeDistSqInt q p ≤ 1) :
    inPhaseTriangleIntMul n ξ j₀ l₀ q.1 q.2 := by
  by_contra hout
  exact (selected_triangle_collar_white n j₀ j₁ q.1 l₀ q.2 ξ
    htriRight hrow habove hfill hright hleft hout
    ⟨p, hp, by
      unfold withinPhaseCollarInt
      exact hstep.trans (by norm_num)⟩) hqblack

/-- A unit lattice step whose endpoints are both black. -/
def phaseBlackNeighbor (n : ℕ) (ξ : ZMod (3 ^ n)) (p q : ℕ × ℤ) : Prop :=
  phaseBlackAtInt n ξ p.1 p.2 ∧ phaseBlackAtInt n ξ q.1 q.2 ∧
    latticeDistSqInt q p ≤ 1

/-- Finite paths through black unit-neighbor lattice points. -/
inductive phaseBlackPath (n : ℕ) (ξ : ZMod (3 ^ n)) (p : ℕ × ℤ) :
    ℕ × ℤ → Prop where
  | nil : phaseBlackPath n ξ p p
  | cons {q r} : phaseBlackPath n ξ p q → phaseBlackNeighbor n ξ q r →
      phaseBlackPath n ξ p r

/-- A black path beginning in a selected triangle remains in that triangle. -/
theorem selected_triangle_blackPath_mem (n j₀ j₁ : ℕ)
    (l₀ : ℤ) (ξ : ZMod (3 ^ n)) (p q : ℕ × ℤ)
    (htriRight : inPhaseTriangleIntMul n ξ j₀ l₀ j₁ l₀)
    (hrow : ∀ r, j₀ ≤ r → r ≤ j₁ → phaseBlackAtInt n ξ r l₀)
    (habove : ∀ r, j₀ ≤ r → r ≤ j₁ → ¬ phaseBlackAtInt n ξ r (l₀ + 1))
    (hfill : ∀ j' l', inPhaseTriangleIntMul n ξ j₀ l₀ j' l' →
      phaseBlackAtInt n ξ j' l')
    (hright : ¬ phaseBlackAtInt n ξ (j₁ + 1) l₀)
    (hleft : j₀ = 0 ∨ ¬ phaseBlackAtInt n ξ (j₀ - 1) l₀)
    (hp : inPhaseTriangleIntMul n ξ j₀ l₀ p.1 p.2)
    (hpath : phaseBlackPath n ξ p q) :
    inPhaseTriangleIntMul n ξ j₀ l₀ q.1 q.2 := by
  induction hpath with
  | nil => exact hp
  | cons hpath hstep ih =>
      exact selected_triangle_black_neighbor_mem n j₀ j₁ l₀ ξ _ _
        htriRight hrow habove hfill hright hleft ih hstep.2.1 hstep.2.2

/-- Black paths compose. -/
theorem phaseBlackPath_trans {n : ℕ} {ξ : ZMod (3 ^ n)} {p q r : ℕ × ℤ}
    (hpq : phaseBlackPath n ξ p q) (hqr : phaseBlackPath n ξ q r) :
    phaseBlackPath n ξ p r := by
  induction hqr with
  | nil => exact hpq
  | cons hqr hstep ih => exact .cons ih hstep

theorem east_unit_step (j : ℕ) (l : ℤ) :
    latticeDistSqInt (j + 1, l) (j, l) = 1 := by
  unfold latticeDistSqInt
  simp [Nat.dist_eq_sub_of_le_right]

theorem south_unit_step (j : ℕ) (l : ℤ) :
    latticeDistSqInt (j, l - 1) (j, l) = 1 := by
  unfold latticeDistSqInt
  norm_num

/-- Triangle membership is monotone to the northwest. -/
theorem inPhaseTriangleIntMul_northwest (n j₀ j jp : ℕ)
    (l₀ l lp : ℤ) (ξ : ZMod (3 ^ n))
    (htri : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (hjp₀ : j₀ ≤ jp) (hjp : jp ≤ j)
    (hlp : l ≤ lp) (hl₀ : lp ≤ l₀) :
    inPhaseTriangleIntMul n ξ j₀ l₀ jp lp := by
  refine ⟨hjp₀, hl₀, ?_⟩
  have ha : jp - j₀ ≤ j - j₀ := Nat.sub_le_sub_right hjp j₀
  have hb : (l₀ - lp).toNat ≤ (l₀ - l).toNat := by
    have hcast : ((l₀ - lp).toNat : ℤ) ≤ ((l₀ - l).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
      omega
    exact_mod_cast hcast
  have h9 : (9 : ℝ) ^ (jp - j₀) ≤ 9 ^ (j - j₀) :=
    pow_le_pow_right₀ (by norm_num) ha
  have h2 : (2 : ℝ) ^ (l₀ - lp).toNat ≤ 2 ^ (l₀ - l).toNat :=
    pow_le_pow_right₀ (by norm_num) hb
  have hK : (9 : ℝ) ^ (jp - j₀) * 2 ^ (l₀ - lp).toNat ≤
      9 ^ (j - j₀) * 2 ^ (l₀ - l).toNat :=
    mul_le_mul h9 h2 (by positivity) (by positivity)
  exact (mul_le_mul_of_nonneg_right hK (abs_nonneg _)).trans htri.2.2

/-- The top-row segment from a triangle corner to any of its columns is a
black unit-neighbor path. -/
theorem triangle_top_path (n j₀ j : ℕ) (l₀ l : ℤ)
    (ξ : ZMod (3 ^ n)) (htri : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (a : ℕ) (ha : a ≤ j - j₀) :
    phaseBlackPath n ξ (j₀, l₀) (j₀ + a, l₀) := by
  induction a with
  | zero => exact .nil
  | succ a ih =>
      have ha' : a ≤ j - j₀ := by omega
      have hlj : l ≤ l₀ := htri.2.1
      have hleft : inPhaseTriangleIntMul n ξ j₀ l₀ (j₀ + a) l₀ :=
        inPhaseTriangleIntMul_northwest n j₀ j (j₀ + a) l₀ l l₀ ξ
          htri (by omega) (by omega) hlj le_rfl
      have hright : inPhaseTriangleIntMul n ξ j₀ l₀ (j₀ + (a + 1)) l₀ :=
        inPhaseTriangleIntMul_northwest n j₀ j (j₀ + (a + 1)) l₀ l l₀ ξ
          htri (by omega) (by omega) hlj le_rfl
      refine .cons (ih ha') ⟨phaseBlackAtInt_of_inPhaseTriangleIntMul n ξ j₀ l₀
        (j₀ + a) l₀ hleft, phaseBlackAtInt_of_inPhaseTriangleIntMul n ξ j₀ l₀
        (j₀ + (a + 1)) l₀ hright, ?_⟩
      have hstep := east_unit_step (j₀ + a) l₀
      exact (by simpa [Nat.add_assoc] using hstep.le)

/-- The vertical segment from a triangle top-row point to a triangle point is
a black unit-neighbor path. -/
theorem triangle_down_path (n j₀ j : ℕ) (l₀ l : ℤ)
    (ξ : ZMod (3 ^ n)) (htri : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (b : ℕ) (hb : b ≤ (l₀ - l).toNat) :
    phaseBlackPath n ξ (j, l₀) (j, l₀ - b) := by
  induction b with
  | zero => simpa using (.nil : phaseBlackPath n ξ (j, l₀) (j, l₀))
  | succ b ih =>
      have hb' : b ≤ (l₀ - l).toNat := by omega
      have hdiff : (b : ℤ) ≤ l₀ - l := by
        have hcast : (b : ℤ) ≤ ((l₀ - l).toNat : ℤ) := by exact_mod_cast hb'
        calc
          (b : ℤ) ≤ ((l₀ - l).toNat : ℤ) := hcast
          _ = l₀ - l := Int.toNat_of_nonneg (by omega)
      have hdiffSucc : ((b + 1 : ℕ) : ℤ) ≤ l₀ - l := by
        have hcast : ((b + 1 : ℕ) : ℤ) ≤ ((l₀ - l).toNat : ℤ) := by
          exact_mod_cast hb
        calc
          ((b + 1 : ℕ) : ℤ) ≤ ((l₀ - l).toNat : ℤ) := hcast
          _ = l₀ - l := Int.toNat_of_nonneg (by omega)
      have hlleft : l ≤ l₀ - b := by omega
      have hlright : l ≤ l₀ - (b + 1) := by omega
      have htopLeft : l₀ - b ≤ l₀ := by omega
      have htopRight : l₀ - (b + 1) ≤ l₀ := by omega
      have hleft : inPhaseTriangleIntMul n ξ j₀ l₀ j (l₀ - b) :=
        inPhaseTriangleIntMul_northwest n j₀ j j l₀ l (l₀ - b) ξ
          htri htri.1 le_rfl hlleft htopLeft
      have hright : inPhaseTriangleIntMul n ξ j₀ l₀ j (l₀ - (b + 1)) :=
        inPhaseTriangleIntMul_northwest n j₀ j j l₀ l (l₀ - (b + 1)) ξ
          htri htri.1 le_rfl hlright htopRight
      have hblackLeft : phaseBlackAtInt n ξ j (l₀ - b) :=
        phaseBlackAtInt_of_inPhaseTriangleIntMul n ξ j₀ l₀ j (l₀ - b) hleft
      have hblackRight : phaseBlackAtInt n ξ j (l₀ - (b + 1)) :=
        phaseBlackAtInt_of_inPhaseTriangleIntMul n ξ j₀ l₀ j (l₀ - (b + 1)) hright
      refine .cons (ih hb') ⟨hblackLeft, hblackRight, ?_⟩
      have hstep := south_unit_step j (l₀ - b)
      have hcoord : l₀ - ((b + 1 : ℕ) : ℤ) = (l₀ - (b : ℤ)) - 1 := by
        norm_num [Nat.cast_add]
        ring
      rw [hcoord]
      exact hstep.le

/-- Every triangle point is connected to its corner by an explicit black
east-then-south lattice path. -/
theorem triangle_corner_path (n j₀ j : ℕ) (l₀ l : ℤ)
    (ξ : ZMod (3 ^ n)) (htri : inPhaseTriangleIntMul n ξ j₀ l₀ j l) :
    phaseBlackPath n ξ (j₀, l₀) (j, l) := by
  have htop := triangle_top_path n j₀ j l₀ l ξ htri (j - j₀) le_rfl
  have hdown := triangle_down_path n j₀ j l₀ l ξ htri (l₀ - l).toNat le_rfl
  have htop' : phaseBlackPath n ξ (j₀, l₀) (j, l₀) := by
    simpa [Nat.add_sub_of_le htri.1] using htop
  have hpath := phaseBlackPath_trans htop' hdown
  have hheight : l₀ - (l₀ - l).toNat = l := by
    have hnonneg : 0 ≤ l₀ - l := sub_nonneg.mpr htri.2.1
    rw [Int.toNat_of_nonneg hnonneg]
    ring
  rw [hheight] at hpath
  exact hpath

theorem latticeDistSqInt_comm (p q : ℕ × ℤ) :
    latticeDistSqInt p q = latticeDistSqInt q p := by
  unfold latticeDistSqInt
  rw [Nat.dist_comm]
  have habs : (p.2 - q.2).natAbs = (q.2 - p.2).natAbs := by
    calc
      (p.2 - q.2).natAbs = (-(p.2 - q.2)).natAbs := (Int.natAbs_neg _).symm
      _ = (q.2 - p.2).natAbs := by congr 1; ring
  rw [habs]

theorem phaseBlackNeighbor_symm {n : ℕ} {ξ : ZMod (3 ^ n)} {p q : ℕ × ℤ}
    (h : phaseBlackNeighbor n ξ p q) : phaseBlackNeighbor n ξ q p := by
  refine ⟨h.2.1, h.1, ?_⟩
  rw [latticeDistSqInt_comm]
  exact h.2.2

theorem phaseBlackPath_symm {n : ℕ} {ξ : ZMod (3 ^ n)} {p q : ℕ × ℤ}
    (h : phaseBlackPath n ξ p q) : phaseBlackPath n ξ q p := by
  induction h with
  | nil => exact .nil
  | cons hpq hqr ih =>
      exact phaseBlackPath_trans (.cons .nil (phaseBlackNeighbor_symm hqr)) ih

/-- A selected triangle that meets another multiplicative triangle contains
the whole of that other triangle. -/
theorem selected_triangle_contains_other_of_overlap
    (n ja ja1 : ℕ) (la : ℤ) (ξ : ZMod (3 ^ n)) (p q : ℕ × ℤ)
    (htriRight : inPhaseTriangleIntMul n ξ ja la ja1 la)
    (hrow : ∀ r, ja ≤ r → r ≤ ja1 → phaseBlackAtInt n ξ r la)
    (habove : ∀ r, ja ≤ r → r ≤ ja1 → ¬ phaseBlackAtInt n ξ r (la + 1))
    (hfill : ∀ j' l', inPhaseTriangleIntMul n ξ ja la j' l' →
      phaseBlackAtInt n ξ j' l')
    (hright : ¬ phaseBlackAtInt n ξ (ja1 + 1) la)
    (hleft : ja = 0 ∨ ¬ phaseBlackAtInt n ξ (ja - 1) la)
    {jb : ℕ} {lb : ℤ}
    (hpa : inPhaseTriangleIntMul n ξ ja la p.1 p.2)
    (hpb : inPhaseTriangleIntMul n ξ jb lb p.1 p.2)
    (hqb : inPhaseTriangleIntMul n ξ jb lb q.1 q.2) :
    inPhaseTriangleIntMul n ξ ja la q.1 q.2 := by
  have hpFromCorner := triangle_corner_path n jb p.1 lb p.2 ξ hpb
  have hqFromCorner := triangle_corner_path n jb q.1 lb q.2 ξ hqb
  have hpToCorner := phaseBlackPath_symm hpFromCorner
  have hpq := phaseBlackPath_trans hpToCorner hqFromCorner
  exact selected_triangle_blackPath_mem n ja ja1 la ξ p q
    htriRight hrow habove hfill hright hleft hpa hpq

/-- The data selecting the canonical top row and both white boundaries of a
filled phase triangle. -/
def isSelectedPhaseTriangle (n : ℕ) (ξ : ZMod (3 ^ n)) (j₀ : ℕ) (l₀ : ℤ) : Prop :=
  ∃ j₁, inPhaseTriangleIntMul n ξ j₀ l₀ j₁ l₀ ∧
    (∀ r, j₀ ≤ r → r ≤ j₁ → phaseBlackAtInt n ξ r l₀) ∧
    (∀ r, j₀ ≤ r → r ≤ j₁ → ¬ phaseBlackAtInt n ξ r (l₀ + 1)) ∧
    (∀ j l, inPhaseTriangleIntMul n ξ j₀ l₀ j l → phaseBlackAtInt n ξ j l) ∧
    ¬ phaseBlackAtInt n ξ (j₁ + 1) l₀ ∧
    (j₀ = 0 ∨ ¬ phaseBlackAtInt n ξ (j₀ - 1) l₀)

/-- Intersecting selected triangles have the same lattice set. -/
theorem selected_phase_triangles_equal_of_overlap
    (n ja jb : ℕ) (la lb : ℤ) (ξ : ZMod (3 ^ n)) (p : ℕ × ℤ)
    (ha : isSelectedPhaseTriangle n ξ ja la)
    (hb : isSelectedPhaseTriangle n ξ jb lb)
    (hpa : inPhaseTriangleIntMul n ξ ja la p.1 p.2)
    (hpb : inPhaseTriangleIntMul n ξ jb lb p.1 p.2) :
    ∀ q : ℕ × ℤ, inPhaseTriangleIntMul n ξ ja la q.1 q.2 ↔
      inPhaseTriangleIntMul n ξ jb lb q.1 q.2 := by
  rcases ha with ⟨ja1, haRight, haRow, haAbove, haFill, haRightWhite, haLeft⟩
  rcases hb with ⟨jb1, hbRight, hbRow, hbAbove, hbFill, hbRightWhite, hbLeft⟩
  intro q
  constructor
  · intro hqa
    exact selected_triangle_contains_other_of_overlap n jb jb1 lb ξ p q
      hbRight hbRow hbAbove hbFill hbRightWhite hbLeft hpb hpa hqa
  · intro hqb
    exact selected_triangle_contains_other_of_overlap n ja ja1 la ξ p q
      haRight haRow haAbove haFill haRightWhite haLeft hpa hpb hqb

/-- Distinct selected triangle lattice sets are disjoint. -/
theorem selected_phase_triangles_disjoint_of_not_equal
    (n ja jb : ℕ) (la lb : ℤ) (ξ : ZMod (3 ^ n))
    (ha : isSelectedPhaseTriangle n ξ ja la)
    (hb : isSelectedPhaseTriangle n ξ jb lb)
    (hne : ¬ ∀ q : ℕ × ℤ, inPhaseTriangleIntMul n ξ ja la q.1 q.2 ↔
      inPhaseTriangleIntMul n ξ jb lb q.1 q.2) :
    Disjoint {q : ℕ × ℤ | inPhaseTriangleIntMul n ξ ja la q.1 q.2}
      {q : ℕ × ℤ | inPhaseTriangleIntMul n ξ jb lb q.1 q.2} := by
  rw [Set.disjoint_left]
  intro p hpa hpb
  exact hne (selected_phase_triangles_equal_of_overlap n ja jb la lb ξ p ha hb hpa hpb)

/-- Every point of a primitive multiplicative triangle lies at least sixteen
columns before the terminal column. -/
theorem triangle_column_before_terminal {n j₀ j : ℕ} (l₀ l : ℤ)
    (ξ : ZMod (3 ^ n)) (hn : 0 < n) (hj₀ : 2 * j₀ < n)
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (htri : inPhaseTriangleIntMul n ξ j₀ l₀ j l) :
    2 * (j + 17) < n := by
  have hj : j₀ ≤ j := htri.1
  have hdrop : (9 : ℝ) ^ (j - j₀) *
      |balancedPhaseInt n j₀ l₀ ξ| ≤ localEpsilon := by
    have htwo : (1 : ℝ) ≤ 2 ^ (l₀ - l).toNat := one_le_pow₀ (by norm_num)
    have hnonneg : 0 ≤ (9 : ℝ) ^ (j - j₀) *
        |balancedPhaseInt n j₀ l₀ ξ| := by positivity
    calc
      (9 : ℝ) ^ (j - j₀) * |balancedPhaseInt n j₀ l₀ ξ| =
          1 * ((9 : ℝ) ^ (j - j₀) * |balancedPhaseInt n j₀ l₀ ξ|) := by ring
      _ ≤ 2 ^ (l₀ - l).toNat * ((9 : ℝ) ^ (j - j₀) *
          |balancedPhaseInt n j₀ l₀ ξ|) :=
        mul_le_mul_of_nonneg_right htwo hnonneg
      _ = (9 ^ (j - j₀) * 2 ^ (l₀ - l).toNat : ℝ) *
          |balancedPhaseInt n j₀ l₀ ξ| := by ring
      _ ≤ localEpsilon := htri.2.2
  have hlower := scaled_primitive_phase_lower l₀ hn hj₀ ξ hξ
  have hratio : (9 : ℝ) ^ (j - j₀) *
      ((3 : ℝ) ^ (2 * j₀) / (3 ^ n : ℝ)) ≤ localEpsilon := by
    exact (mul_le_mul_of_nonneg_left hlower (by positivity)).trans hdrop
  have hpow : (3 : ℝ) ^ (2 * j) / (3 ^ n : ℝ) ≤ localEpsilon := by
    have hnum : (9 : ℝ) ^ (j - j₀) * (3 : ℝ) ^ (2 * j₀) =
        (3 : ℝ) ^ (2 * j) := by
      calc
        (9 : ℝ) ^ (j - j₀) * (3 : ℝ) ^ (2 * j₀) =
            ((3 : ℝ) ^ 2) ^ (j - j₀) * (3 : ℝ) ^ (2 * j₀) := by norm_num
        _ = ((3 : ℝ) ^ 2) ^ (j - j₀) * ((3 : ℝ) ^ 2) ^ j₀ := by
          congr 1
          rw [pow_mul]
        _ = ((3 : ℝ) ^ 2) ^ ((j - j₀) + j₀) := by rw [← pow_add]
        _ = ((3 : ℝ) ^ 2) ^ j := by
          congr 1
          exact Nat.sub_add_cancel hj
        _ = (3 : ℝ) ^ (2 * j) := by rw [pow_mul]
    rw [← hnum]
    simpa [mul_div_assoc] using hratio
  have hcleared : (2 : ℝ) ^ 78 * (3 : ℝ) ^ (2 * j) ≤ (3 : ℝ) ^ n := by
    have hpos : (0 : ℝ) < 3 ^ n := by positivity
    have h := (div_le_iff₀ hpos).mp hpow
    norm_num [localEpsilon] at h ⊢
    nlinarith
  have hstrict : (9 : ℝ) ^ (j + 17) < (3 : ℝ) ^ n := by
    have hguard : (9 : ℝ) ^ 17 < (2 : ℝ) ^ 78 := by
      exact_mod_cast terminal_separation_guard
    calc
      (9 : ℝ) ^ (j + 17) = (9 : ℝ) ^ 17 * (3 : ℝ) ^ (2 * j) := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, pow_mul, pow_add]
        ring
      _ < 2 ^ 78 * (3 : ℝ) ^ (2 * j) :=
        mul_lt_mul_of_pos_right hguard (by positivity)
      _ ≤ 3 ^ n := hcleared
  rw [show (9 : ℝ) ^ (j + 17) = 3 ^ (2 * (j + 17)) by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, pow_mul]] at hstrict
  exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp hstrict

/-- The terminal form of `triangle_column_before_terminal` with
`N = floor (n / 2)`. -/
theorem triangle_column_le_half_sub_sixteen {n j₀ j : ℕ} (l₀ l : ℤ)
    (ξ : ZMod (3 ^ n)) (hn : 0 < n) (hj₀ : 2 * j₀ < n)
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (htri : inPhaseTriangleIntMul n ξ j₀ l₀ j l) :
    j ≤ n / 2 - 16 := by
  have h := triangle_column_before_terminal l₀ l ξ hn hj₀ hξ htri
  omega

theorem exists_black_top_of_primitive {n j l : ℕ} (hn : 0 < n)
    (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hblack : phaseBlackAt n ξ j l) :
    ∃ l₀, l ≤ l₀ ∧ phaseBlackAt n ξ j l₀ ∧
      (∀ r, l ≤ r → r ≤ l₀ → phaseBlackAt n ξ j r) ∧
      ¬ phaseBlackAt n ξ j (l₀ + 1) ∧ l₀ < l + 2 * n := by
  classical
  obtain ⟨k, hk, hkwhite⟩ := exists_nonblack_above_of_primitive hn hj ξ hξ
  let P : ℕ → Prop := fun r => ¬ phaseBlackAt n ξ j (l + r)
  have hP : ∃ r, P r := ⟨k, hkwhite⟩
  let k₀ := Nat.find hP
  have hk₀P : P k₀ := Nat.find_spec hP
  have hk₀pos : 0 < k₀ := by
    by_contra hz
    have : k₀ = 0 := by omega
    apply hk₀P
    simpa [P, this] using hblack
  have hk₀le : k₀ ≤ k := Nat.find_min' hP hkwhite
  refine ⟨l + k₀ - 1, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · have hprev : ¬ P (k₀ - 1) := Nat.find_min hP (by omega : k₀ - 1 < k₀)
    have heq : l + (k₀ - 1) = l + k₀ - 1 := by omega
    simpa [P, heq] using hprev
  · intro r hlr hrl
    have hrform : l + (r - l) = r := Nat.add_sub_of_le hlr
    have hrlt : r - l < k₀ := by omega
    have hprev : ¬ P (r - l) := Nat.find_min hP hrlt
    simpa [P, hrform] using hprev
  · have hadd : l + k₀ - 1 + 1 = l + k₀ := by omega
    simpa [hadd, P] using hk₀P
  · omega

theorem exists_black_leftmost (n j l₀ : ℕ) (ξ : ZMod (3 ^ n))
    (hblack : phaseBlackAt n ξ j l₀) :
    ∃ j₀, j₀ ≤ j ∧ phaseBlackAt n ξ j₀ l₀ ∧
      (j₀ = 0 ∨ ¬ phaseBlackAt n ξ (j₀ - 1) l₀) := by
  classical
  let P : ℕ → Prop := fun r => phaseBlackAt n ξ r l₀
  have hP : ∃ r, P r := ⟨j, hblack⟩
  let j₀ := Nat.find hP
  have hj₀P : P j₀ := Nat.find_spec hP
  have hj₀le : j₀ ≤ j := Nat.find_min' hP hblack
  refine ⟨j₀, hj₀le, hj₀P, ?_⟩
  by_cases hz : j₀ = 0
  · exact Or.inl hz
  · right
    exact Nat.find_min hP (by omega : j₀ - 1 < j₀)

theorem exists_black_row_start (n j l₀ : ℕ) (ξ : ZMod (3 ^ n))
    (hblack : phaseBlackAt n ξ j l₀) :
    ∃ j₀, j₀ ≤ j ∧
      (∀ r, j₀ ≤ r → r ≤ j → phaseBlackAt n ξ r l₀) ∧
      (j₀ = 0 ∨ ¬ phaseBlackAt n ξ (j₀ - 1) l₀) := by
  classical
  let P : ℕ → Prop := fun k => k ≤ j ∧
    ∀ r, k ≤ r → r ≤ j → phaseBlackAt n ξ r l₀
  have hP : ∃ k, P k := ⟨j, le_rfl, fun r hr₁ hr₂ => by
    have : r = j := Nat.le_antisymm hr₂ hr₁
    simpa [this] using hblack⟩
  let j₀ := Nat.find hP
  have hj₀P : P j₀ := Nat.find_spec hP
  refine ⟨j₀, hj₀P.1, hj₀P.2, ?_⟩
  by_cases hz : j₀ = 0
  · exact Or.inl hz
  · right
    intro hwest
    have hprev : P (j₀ - 1) := by
      constructor
      · omega
      · intro r hr₁ hr₂
        by_cases hr : r = j₀ - 1
        · simpa [hr] using hwest
        · apply hj₀P.2 r
          omega
          exact hr₂
    exact (Nat.find_min hP (by omega : j₀ - 1 < j₀)) hprev

theorem phaseResidue_east_iter (n j l a : ℕ) (ξ : ZMod (3 ^ n)) :
    phaseResidue n (j + a) l ξ =
      (9 : ZMod (3 ^ n)) ^ a * phaseResidue n j l ξ := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Nat.add_succ, phaseResidue_east, ih, pow_succ]
      ring

theorem phaseResidue_lower_iter (n j l b : ℕ) (ξ : ZMod (3 ^ n))
    (hb : b ≤ l) :
    phaseResidue n j (l - b) ξ =
      (2 : ZMod (3 ^ n)) ^ b * phaseResidue n j l ξ := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hb' : b ≤ l := by omega
      have hadd : l - (b + 1) + 1 = l - b := by omega
      have hs := phaseResidue_south n j (l - (b + 1)) ξ
      rw [hadd] at hs
      rw [hs, ih hb', pow_succ]
      ring

theorem phaseResidue_from_corner (n j₀ l₀ j l : ℕ) (ξ : ZMod (3 ^ n))
    (hj : j₀ ≤ j) (hl : l ≤ l₀) :
    phaseResidue n j l ξ =
      ((9 ^ (j - j₀) * 2 ^ (l₀ - l) : ℕ) : ZMod (3 ^ n)) *
        phaseResidue n j₀ l₀ ξ := by
  have hjeq : j₀ + (j - j₀) = j := Nat.add_sub_of_le hj
  have hleq : l₀ - (l₀ - l) = l := Nat.sub_sub_self hl
  calc
    phaseResidue n j l ξ =
        phaseResidue n (j₀ + (j - j₀)) (l₀ - (l₀ - l)) ξ := by rw [hjeq, hleq]
    _ = (9 : ZMod (3 ^ n)) ^ (j - j₀) *
        phaseResidue n j₀ (l₀ - (l₀ - l)) ξ :=
      phaseResidue_east_iter n j₀ (l₀ - (l₀ - l)) (j - j₀) ξ
    _ = (9 : ZMod (3 ^ n)) ^ (j - j₀) *
        ((2 : ZMod (3 ^ n)) ^ (l₀ - l) * phaseResidue n j₀ l₀ ξ) := by
      rw [phaseResidue_lower_iter _ _ _ _ _ (Nat.sub_le _ _)]
    _ = _ := by push_cast; ring

/-- Multiplicative form of the Appendix E triangle. -/
def inPhaseTriangleMul (n : ℕ) (ξ : ZMod (3 ^ n))
    (j₀ l₀ j l : ℕ) : Prop :=
  j₀ ≤ j ∧ l ≤ l₀ ∧
    (9 ^ (j - j₀) * 2 ^ (l₀ - l) : ℝ) *
      |balancedPhase n j₀ l₀ ξ| ≤ localEpsilon

theorem balancedPhase_from_corner_of_triangle (n : ℕ) (ξ : ZMod (3 ^ n))
    (j₀ l₀ j l : ℕ) (htri : inPhaseTriangleMul n ξ j₀ l₀ j l) :
    balancedPhase n j l ξ =
      (9 ^ (j - j₀) * 2 ^ (l₀ - l) : ℝ) * balancedPhase n j₀ l₀ ξ := by
  rcases htri with ⟨hj, hl, hsize⟩
  let k : ℕ := 9 ^ (j - j₀) * 2 ^ (l₀ - l)
  have hres := phaseResidue_from_corner n j₀ l₀ j l ξ hj hl
  have hεhalf : localEpsilon < (1 / 2 : ℝ) := by norm_num [localEpsilon]
  have hpow : (0 : ℝ) < 3 ^ n := by positivity
  have hsmall : |((k : ℤ) * (phaseResidue n j₀ l₀ ξ).valMinAbs : ℤ)| * 2 <
      (3 ^ n : ℤ) := by
    have hreal : (k : ℝ) *
        |(((phaseResidue n j₀ l₀ ξ).valMinAbs : ℤ) : ℝ)| /
          (3 ^ n : ℝ) ≤ localEpsilon := by
      simpa [inPhaseTriangleMul, balancedPhase, k, abs_div,
        abs_of_pos hpow, mul_div_assoc] using hsize
    have hreal' : (k : ℝ) *
        |(((phaseResidue n j₀ l₀ ξ).valMinAbs : ℤ) : ℝ)| * 2 <
          (3 ^ n : ℝ) := by
      have := (div_le_iff₀ hpow).mp hreal
      nlinarith
    have hz : (k : ℤ) * |(phaseResidue n j₀ l₀ ξ).valMinAbs| * 2 <
        (3 ^ n : ℤ) := by exact_mod_cast hreal'
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hz
  unfold balancedPhase
  rw [hres]
  have hval := valMinAbs_nat_mul_of_small (phaseResidue n j₀ l₀ ξ) hsmall
  change (((k : ZMod (3 ^ n)) * phaseResidue n j₀ l₀ ξ).valMinAbs : ℝ) /
      (3 ^ n : ℝ) = _
  rw [hval]
  push_cast
  dsimp only [k]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring_nf

theorem phaseBlackAt_of_inPhaseTriangleMul (n : ℕ) (ξ : ZMod (3 ^ n))
    (j₀ l₀ j l : ℕ) (htri : inPhaseTriangleMul n ξ j₀ l₀ j l) :
    phaseBlackAt n ξ j l := by
  unfold phaseBlackAt
  rw [balancedPhase_from_corner_of_triangle n ξ j₀ l₀ j l htri, abs_mul]
  have hk : 0 ≤ (9 ^ (j - j₀) * 2 ^ (l₀ - l) : ℝ) := by positivity
  rw [abs_of_nonneg hk]
  exact htri.2.2

theorem exists_canonical_black_corner {n j l : ℕ} (hn : 0 < n)
    (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hblack : phaseBlackAt n ξ j l) :
    ∃ j₀ l₀,
      j₀ ≤ j ∧ l ≤ l₀ ∧
      (∀ r, j₀ ≤ r → r ≤ j → phaseBlackAt n ξ r l₀) ∧
      (∀ s, l ≤ s → s ≤ l₀ → phaseBlackAt n ξ j s) ∧
      (j₀ = 0 ∨ ¬ phaseBlackAt n ξ (j₀ - 1) l₀) ∧
      ¬ phaseBlackAt n ξ j (l₀ + 1) ∧
      l₀ < l + 2 * n := by
  obtain ⟨l₀, hll₀, htop, hvertical, habove, hlbound⟩ :=
    exists_black_top_of_primitive hn hj ξ hξ hblack
  obtain ⟨j₀, hj₀j, hrow, hleft⟩ := exists_black_row_start n j l₀ ξ htop
  exact ⟨j₀, l₀, hj₀j, hll₀, hrow, hvertical, hleft, habove, hlbound⟩

theorem balancedPhase_east_iter_of_weak (n j l a : ℕ) (ξ : ZMod (3 ^ n))
    (hweak : ∀ r < a, phaseWeakBlackAt n ξ (j + r) l) :
    balancedPhase n (j + a) l ξ =
      (9 : ℝ) ^ a * balancedPhase n j l ξ := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hprev := ih (fun r hr => hweak r (by omega))
      have hstep := balancedPhase_east_of_weak n (j + a) l ξ
        (hweak a (by omega))
      rw [Nat.add_succ, hstep, hprev, pow_succ]
      ring

theorem balancedPhase_lower_iter_of_weak (n j l b : ℕ) (ξ : ZMod (3 ^ n))
    (hb : b ≤ l)
    (hweak : ∀ s, l - b < s → s ≤ l → phaseWeakBlackAt n ξ j s) :
    balancedPhase n j (l - b) ξ =
      (2 : ℝ) ^ b * balancedPhase n j l ξ := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hb' : b ≤ l := by omega
      have hadd : l - (b + 1) + 1 = l - b := by omega
      have hcurrent : phaseWeakBlackAt n ξ j (l - b) := by
        apply hweak
        · omega
        · omega
      unfold phaseWeakBlackAt at hcurrent
      have hstep := balancedPhase_south_of_weak n j (l - (b + 1)) ξ
        (by simpa [hadd] using hcurrent)
      have hprev := ih hb' (fun s hs₁ hs₂ => hweak s (by omega) hs₂)
      rw [hadd] at hstep
      rw [hstep, hprev, pow_succ]
      ring

theorem canonical_corner_contains_point {n j l j₀ l₀ : ℕ}
    (ξ : ZMod (3 ^ n))
    (hj : j₀ ≤ j) (hl : l ≤ l₀)
    (hrow : ∀ r, j₀ ≤ r → r ≤ j → phaseBlackAt n ξ r l₀)
    (hvertical : ∀ s, l ≤ s → s ≤ l₀ → phaseBlackAt n ξ j s)
    (hblack : phaseBlackAt n ξ j l) :
    inPhaseTriangleMul n ξ j₀ l₀ j l := by
  have heast := balancedPhase_east_iter_of_weak n j₀ l₀ (j - j₀) ξ
    (fun r hr => phaseBlackAt_implies_weak n ξ (j₀ + r) l₀
      (hrow (j₀ + r) (by omega) (by omega)))
  have hjeq : j₀ + (j - j₀) = j := Nat.add_sub_of_le hj
  rw [hjeq] at heast
  have hlower := balancedPhase_lower_iter_of_weak n j l₀ (l₀ - l) ξ
    (Nat.sub_le _ _)
    (fun s hs₁ hs₂ => phaseBlackAt_implies_weak n ξ j s
      (hvertical s (by omega) hs₂))
  have hleq : l₀ - (l₀ - l) = l := Nat.sub_sub_self hl
  rw [hleq, heast] at hlower
  refine ⟨hj, hl, ?_⟩
  unfold phaseBlackAt at hblack
  rw [hlower, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ (l₀ - l)),
    abs_of_nonneg (by positivity : 0 ≤ (9 : ℝ) ^ (j - j₀))] at hblack
  nlinarith

theorem black_point_has_filled_triangle {n j l : ℕ} (hn : 0 < n)
    (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hblack : phaseBlackAt n ξ j l) :
    ∃ j₀ l₀,
      inPhaseTriangleMul n ξ j₀ l₀ j l ∧
      (∀ j' l', inPhaseTriangleMul n ξ j₀ l₀ j' l' →
        phaseBlackAt n ξ j' l') ∧
      (j₀ = 0 ∨ ¬ phaseBlackAt n ξ (j₀ - 1) l₀) ∧
      ¬ phaseBlackAt n ξ j (l₀ + 1) := by
  obtain ⟨j₀, l₀, hj₀j, hll₀, hrow, hvertical, hleft, habove, _⟩ :=
    exists_canonical_black_corner hn hj ξ hξ hblack
  refine ⟨j₀, l₀,
    canonical_corner_contains_point ξ hj₀j hll₀ hrow hvertical hblack,
    ?_, hleft, habove⟩
  intro j' l' htri
  exact phaseBlackAt_of_inPhaseTriangleMul n ξ j₀ l₀ j' l' htri

/-- Every state outside the actual balanced-phase black set satisfies F250's
analytic white predicate. -/
theorem analyticWhite_of_not_phaseBlack (u : ℕ) (ξ : ZMod (3 ^ (u + 2)))
    (hwhite : ¬ phaseBlack u ξ) : analyticWhite localEpsilon u ξ := by
  apply analyticWhite_of_balancedPhase (t := balancedPhase (u + 2) 0 0 ξ)
    localEpsilon_nonneg
  · have h := balancedPhase_mem (u + 2) 0 0 ξ
    rw [Set.mem_Ioc] at h
    rw [abs_le]
    constructor <;> linarith
  · unfold phaseBlack at hwhite
    exact le_of_lt (lt_of_not_ge hwhite)
  · exact norm_reversePairFactor_three_eq_cos u ξ

end LocalPrimitive
end WordCertDensity
