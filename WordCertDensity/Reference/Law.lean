/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.Words
public import WordCertDensity.Reference.Residues
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The normalized ternary reference law

The distribution is the actual pushforward of independent geometric words
under their inverse-prefix offset. All means use the whole ternary group.
The marker is two thirds of the mean-one density, including at level zero.
-/

@[expose] public section

namespace WordCertDensity

namespace Reference

/-- The probability distribution of the inverse-prefix offset at its word length. -/
noncomputable def law (n : ℕ) : PMF (ZMod (3 ^ n)) :=
  (wordPMF n).map (ValuationWord.residueOffset n)

/-- The real-valued reference probability mass of a residue. -/
noncomputable def mass (n : ℕ) (x : ZMod (3 ^ n)) : ℝ := (law n x).toReal

/-- Reference density relative to the uniform law on the whole group. -/
noncomputable def density (n : ℕ) (x : ZMod (3 ^ n)) : ℝ :=
  (3 : ℝ) ^ n * mass n x

/-- The manuscript's marker applies its factor two thirds exactly once. -/
noncomputable def marker (n : ℕ) (x : ZMod (3 ^ n)) : ℝ := (2 / 3 : ℝ) * density n x

/-- Full-group uniform mean, also defined on the one-point group at level zero. -/
noncomputable def mean (n : ℕ) (f : ZMod (3 ^ n) → ℝ) : ℝ :=
  (∑ x, f x) / (3 : ℝ) ^ n

/-- The mean of a constant is that constant, with no exceptional level. -/
theorem mean_const (n : ℕ) (c : ℝ) : mean n (fun _ => c) = c := by
  simp [mean, ZMod.card, nsmul_eq_mul]

/-- Full-group means preserve addition. -/
theorem mean_add (n : ℕ) (f g : ZMod (3 ^ n) → ℝ) :
    mean n (fun x => f x + g x) = mean n f + mean n g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

/-- Full-group means preserve subtraction. -/
theorem mean_sub (n : ℕ) (f g : ZMod (3 ^ n) → ℝ) :
    mean n (fun x => f x - g x) = mean n f - mean n g := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

/-- A constant scalar factors out of a full-group mean. -/
theorem mean_mul (n : ℕ) (c : ℝ) (f : ZMod (3 ^ n) → ℝ) :
    mean n (fun x => c * f x) = c * mean n f := by
  simp only [mean, ← Finset.mul_sum, mul_div_assoc]

/-- Nonnegative functions have nonnegative full-group mean. -/
theorem mean_nonneg (n : ℕ) (f : ZMod (3 ^ n) → ℝ) (h : ∀ x, 0 ≤ f x) :
    0 ≤ mean n f := by
  exact div_nonneg (Finset.sum_nonneg fun x _ => h x) (by positivity)

/-- Pointwise order is preserved by the full-group mean. -/
theorem mean_mono (n : ℕ) (f g : ZMod (3 ^ n) → ℝ) (h : ∀ x, f x ≤ g x) :
    mean n f ≤ mean n g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (by positivity)

/-- Reference masses are nonnegative. -/
theorem mass_nonneg (n : ℕ) (x : ZMod (3 ^ n)) : 0 ≤ mass n x := ENNReal.toReal_nonneg

/-- The real-valued reference masses sum to one. -/
theorem mass_sum (n : ℕ) : ∑ x, mass n x = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe (law n))
  rw [tsum_fintype, ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top _ x),
    ENNReal.toReal_one] at h
  exact h

/-- The normalized reference density is nonnegative. -/
theorem density_nonneg (n : ℕ) (x : ZMod (3 ^ n)) : 0 ≤ density n x :=
  mul_nonneg (by positivity) (mass_nonneg n x)

/-- The marker is nonnegative. -/
theorem marker_nonneg (n : ℕ) (x : ZMod (3 ^ n)) : 0 ≤ marker n x :=
  mul_nonneg (by positivity) (density_nonneg n x)

/-- The reference density has full-group mean one. -/
theorem mean_density (n : ℕ) : mean n (density n) = 1 := by
  change mean n (fun x => (3 : ℝ) ^ n * mass n x) = 1
  rw [mean_mul]
  simp [mean, mass_sum]

/-- The marker has full-group mean two thirds. -/
theorem mean_marker (n : ℕ) : mean n (marker n) = 2 / 3 := by
  change mean n (fun x => (2 / 3 : ℝ) * density n x) = 2 / 3
  rw [mean_mul, mean_density, mul_one]

/-- The zero-level reference law is concentrated at the unique residue. -/
theorem law_zero : law 0 = PMF.pure 0 := by
  rw [law, wordPMF_zero, PMF.pure_map]
  rfl

/-- At level zero the unique residue has probability one. -/
theorem mass_zero (x : ZMod (3 ^ 0)) : mass 0 x = 1 := by
  let : Subsingleton (ZMod (3 ^ 0)) := ZMod.subsingleton_iff.mpr (by decide)
  rw [mass, law_zero, show x = 0 from Subsingleton.elim _ _]
  simp

/-- The zero-level density is one. -/
theorem density_zero (x : ZMod (3 ^ 0)) : density 0 x = 1 := by
  simp [density, mass_zero]

/-- The zero-level marker retains its single factor two thirds. -/
theorem marker_zero (x : ZMod (3 ^ 0)) : marker 0 x = 2 / 3 := by
  simp [marker, density_zero]

/-- A nonempty inverse offset is a unit at every ternary level. -/
theorem residueOffset_cons_isUnit (n : ℕ) (a : ℕ+) (w : ValuationWord) :
    IsUnit (ValuationWord.residueOffset n (a :: w)) := by
  have hnil : IsNilpotent (3 * ValuationWord.residueOffset n w) := by
    refine ⟨n, ?_⟩
    rw [mul_pow]
    have hzero : (3 : ZMod (3 ^ n)) ^ n = 0 := by
      exact_mod_cast ZMod.natCast_self (3 ^ n)
    rw [hzero, zero_mul]
  exact (((twoUnit n)⁻¹ ^ (a : ℕ)).isUnit).mul hnil.isUnit_one_add

/-- At positive levels every supported reference residue is a unit. -/
theorem law_support_isUnit {n : ℕ} (hn : 0 < n) {x : ZMod (3 ^ n)}
    (hx : x ∈ (law n).support) : IsUnit x := by
  obtain ⟨w, hw, rfl⟩ :=
    (PMF.mem_support_map_iff (ValuationWord.residueOffset n) (wordPMF n) x).mp hx
  have hlength := (wordPMF_mem_support_iff n w).mp hw
  cases w with
  | nil => exact (Nat.ne_of_gt hn hlength.symm).elim
  | cons a w => exact residueOffset_cons_isUnit n a w

/-- The positive-level reference PMF vanishes on nonunits. -/
theorem law_eq_zero_of_not_isUnit {n : ℕ} (hn : 0 < n) (x : ZMod (3 ^ n))
    (hx : ¬ IsUnit x) : law n x = 0 := by
  apply (PMF.apply_eq_zero_iff _ _).mpr
  exact fun h => hx (law_support_isUnit hn h)

/-- The real reference mass vanishes on nonunits at positive levels. -/
theorem mass_eq_zero_of_not_isUnit {n : ℕ} (hn : 0 < n) (x : ZMod (3 ^ n))
    (hx : ¬ IsUnit x) : mass n x = 0 := by
  simp [mass, law_eq_zero_of_not_isUnit hn x hx]

/-- The normalized density vanishes on nonunits at positive levels. -/
theorem density_eq_zero_of_not_isUnit {n : ℕ} (hn : 0 < n) (x : ZMod (3 ^ n))
    (hx : ¬ IsUnit x) : density n x = 0 := by
  simp [density, mass_eq_zero_of_not_isUnit hn x hx]

/-- The marker vanishes on nonunits at positive levels. -/
theorem marker_eq_zero_of_not_isUnit {n : ℕ} (hn : 0 < n) (x : ZMod (3 ^ n))
    (hx : ¬ IsUnit x) : marker n x = 0 := by
  simp [marker, density_eq_zero_of_not_isUnit hn x hx]

end Reference

end WordCertDensity
