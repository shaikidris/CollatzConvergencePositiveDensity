/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

Conductor factorization and decay arguments adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The original LICENSE
and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
This version uses the actual local PMF and positive Fourier convention.
-/
module

public import WordCertDensity.Analytic.AffineTail
public import WordCertDensity.Analytic.FiberFourier
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.GCongr
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# Discarded frequencies of the unrestricted tail

Projection and binary units preserve divisibility at every retained depth.
A discarded frequency therefore has a primitive conductor at least n/20
under the literal head guards. The polynomial-decay conversion stays symbolic
in its coefficient and exponent; the numerical primitive is applied separately.
-/

@[expose] public section

namespace WordCertDensity
namespace FiniteFourier

/-- Projection preserves ternary-power divisibility below the projected level. -/
theorem three_pow_dvd_project_iff {q r n : ℕ} (hqr : q ≤ r) (hrn : r ≤ n)
    (ξ : ZMod (3 ^ n)) :
    (3 : ZMod (3 ^ n)) ^ q ∣ ξ ↔
      (3 : ZMod (3 ^ r)) ^ q ∣ Reference.project hrn ξ := by
  rw [three_pow_dvd_iff_dvd_val (hqr.trans hrn), three_pow_dvd_iff_dvd_val hqr]
  have he : (ξ.val : ZMod (3 ^ r)) = ((Reference.project hrn ξ).val : ZMod (3 ^ r)) := by
    rw [ZMod.natCast_zmod_val, ← Reference.project_natCast hrn ξ.val,
      ZMod.natCast_zmod_val]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp he).dvd_iff (Nat.pow_dvd_pow 3 hqr)

/-- A natural integer prime to three stays primitive at every positive ternary level. -/
theorem not_three_dvd_natCast {r η : ℕ} (hr : 1 ≤ r) (hη : ¬ 3 ∣ η) :
    ¬ (3 : ZMod (3 ^ r)) ∣ (η : ZMod (3 ^ r)) := by
  intro h
  have hv := (three_pow_dvd_iff_dvd_val hr (η : ZMod (3 ^ r))).mp (by simpa using h)
  simp only [ZMod.val_natCast, pow_one] at hv
  have hmod : 3 ∣ 3 ^ r := by simpa using Nat.pow_dvd_pow 3 hr
  exact hη (((Nat.mod_modEq η (3 ^ r)).dvd_iff hmod).mp hv)

/-- A frequency outside a ternary-power ideal has a smaller exact natural power factor. -/
theorem exists_three_pow_mul_of_not_dvd {T q : ℕ} {ξ : ZMod (3 ^ T)}
    (hξ : ¬ (3 : ZMod (3 ^ T)) ^ q ∣ ξ) :
    ∃ j η : ℕ, j < q ∧ ¬ 3 ∣ η ∧ ξ = (3 : ZMod (3 ^ T)) ^ j * (η : ZMod (3 ^ T)) := by
  have hne : ξ ≠ 0 := by
    intro hz
    exact hξ (hz ▸ dvd_zero _)
  obtain ⟨j, η, hη, hv⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd ((ZMod.val_ne_zero ξ).mpr hne) 3 (by decide)
  have hf : ξ = (3 : ZMod (3 ^ T)) ^ j * (η : ZMod (3 ^ T)) := by
    rw [← ZMod.natCast_zmod_val ξ, hv]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hj : j < q := by
    by_contra hn
    have hqj : q ≤ j := by omega
    apply hξ
    refine ⟨(3 : ZMod (3 ^ T)) ^ (j - q) * (η : ZMod (3 ^ T)), ?_⟩
    rw [hf, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hqj]
  exact ⟨j, η, hj, hη, hf⟩

/-- A naturally represented frequency factor has precisely the projected Fourier value. -/
theorem fourierMass_three_pow_mul_natCast {r j T : ℕ} (h : r + j = T) (η : ℕ) :
    Reference.fourierMass T ((3 : ZMod (3 ^ T)) ^ j * (η : ZMod (3 ^ T))) =
      Reference.fourierMass r (η : ZMod (3 ^ r)) := by
  subst T
  rw [fourierMass_three_pow_mul, Reference.project_natCast]

end FiniteFourier

namespace AffineTail

/-- The binary unit and projection preserve exclusion from each permitted ternary-power ideal. -/
theorem scaledFrequency_not_dvd {q T n l : ℕ} (hqT : q ≤ T) (hTn : T ≤ n)
    {ξ : ZMod (3 ^ n)} (hξ : ¬ (3 : ZMod (3 ^ n)) ^ q ∣ ξ) :
    ¬ (3 : ZMod (3 ^ T)) ^ q ∣ scaledFrequency hTn l ξ := by
  simp only [scaledFrequency, Reference.inverseTwoPow, Units.dvd_mul_left]
  exact mt (FiniteFourier.three_pow_dvd_project_iff hqT hTn ξ).mpr hξ

/-- The exact head and frequency ranges force a positive conductor at least n/20. -/
theorem conductor_bounds {n m k T j r : ℕ}
    (htail : k + 1 + T = n) (hconductor : j + r = T)
    (hhead : k + 1 ≤ m) (hfrequency : j < n - m)
    (hm : 9 * n ≤ 10 * m) (hk : 20 * k ≤ 17 * n) :
    r + j = T ∧ 1 ≤ r ∧ m - k ≤ r ∧ n ≤ 20 * r := by
  omega

/-- A discarded ambient frequency has an actual primitive reference conductor with all guards. -/
theorem exists_scaled_conductor {n m k T l : ℕ}
    (htail : k + 1 + T = n) (hhead : k + 1 ≤ m)
    (hm : 9 * n ≤ 10 * m) (hk : 20 * k ≤ 17 * n)
    {ξ : ZMod (3 ^ n)} (hξ : ¬ (3 : ZMod (3 ^ n)) ^ (n - m) ∣ ξ) :
    ∃ r j η : ℕ, j < n - m ∧ r + j = T ∧ k + j + 1 + r = n ∧
      1 ≤ r ∧ m - k ≤ r ∧ n ≤ 20 * r ∧
      ¬ (3 : ZMod (3 ^ r)) ∣ (η : ZMod (3 ^ r)) ∧
      Reference.fourierMass T (scaledFrequency (by omega : T ≤ n) l ξ) =
        Reference.fourierMass r (η : ZMod (3 ^ r)) := by
  have hTn : T ≤ n := by omega
  have hqT : n - m ≤ T := by omega
  obtain ⟨j, η, hj, hη, hf⟩ := FiniteFourier.exists_three_pow_mul_of_not_dvd
    (scaledFrequency_not_dvd hqT hTn hξ)
  have hjT : j < T := by omega
  let r := T - j
  have hsum : j + r = T := by dsimp [r]; omega
  obtain ⟨hrj, hr, hmr, hnr⟩ := conductor_bounds htail hsum hhead hj hm hk
  refine ⟨r, j, η, hj, hrj, by omega, hr, hmr, hnr,
    FiniteFourier.not_three_dvd_natCast hr hη, ?_⟩
  rw [hf]
  exact FiniteFourier.fourierMass_three_pow_mul_natCast hrj η

/-- The conductor lower bound converts a symbolic polynomial coefficient without renormalization. -/
theorem div_conductor_pow_le {C : ℝ} (hC : 0 ≤ C) (B : ℕ) {n r : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hnr : n ≤ 20 * r) :
    C / (r : ℝ) ^ B ≤ C * (20 : ℝ) ^ B / (n : ℝ) ^ B := by
  have hnp : 0 < (n : ℝ) ^ B := pow_pos (by exact_mod_cast (by omega : 0 < n)) B
  have hrp : 0 < (r : ℝ) ^ B := pow_pos (by exact_mod_cast (by omega : 0 < r)) B
  have hreal : (n : ℝ) ≤ 20 * (r : ℝ) := by exact_mod_cast hnr
  have hpow : (n : ℝ) ^ B ≤ (20 : ℝ) ^ B * (r : ℝ) ^ B := by
    rw [← mul_pow]
    gcongr
  apply (div_le_div_iff₀ hrp hnp).mpr
  calc
    C * (n : ℝ) ^ B ≤ C * ((20 : ℝ) ^ B * (r : ℝ) ^ B) := mul_le_mul_of_nonneg_left hpow hC
    _ = C * (20 : ℝ) ^ B * (r : ℝ) ^ B := by rw [mul_assoc]

/-- Primitive decay gives the literal positive Fourier bound for the unrestricted affine tail. -/
theorem fourier_mass_le {B m k T l : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ r : ℕ, 1 ≤ r → ∀ η : ZMod (3 ^ r),
      ¬ (3 : ZMod (3 ^ r)) ∣ η → ‖Reference.fourierMass r η‖ ≤ C / (r : ℝ) ^ B)
    (hhead : k + 1 ≤ m) (hm : 9 * (T + (k + 1)) ≤ 10 * m)
    (hk : 20 * k ≤ 17 * (T + (k + 1))) {ξ : ZMod (3 ^ (T + (k + 1)))}
    (hξ : ¬ (3 : ZMod (3 ^ (T + (k + 1)))) ^ (T + (k + 1) - m) ∣ ξ) :
    ‖∑ x, (mass (k + 1) T l x : ℂ) * ZMod.stdAddChar (ξ * x)‖ ≤
      C * (20 : ℝ) ^ B / ((T + (k + 1) : ℕ) : ℝ) ^ B := by
  obtain ⟨r, j, η, _hj, _hrj, _hadd, hr, _hmr, hnr, hη, hf⟩ :=
    exists_scaled_conductor (l := l) (by omega : k + 1 + T = T + (k + 1))
      hhead hm hk hξ
  rw [fourier_mass, hf]
  exact (hdecay r hr η hη).trans (div_conductor_pow_le hC B (by omega) hr hnr)

end AffineTail
end WordCertDensity
