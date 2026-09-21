/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Transfer.Prefix

/-!
# Exact one-letter recursion of the reference marker

The actual independent-word law splits at its first letter. The recursion
retains the geometric coefficient and the full residual reference marker.
-/

@[expose] public section

namespace WordCertDensity.Reference

/-- Splitting the first letter gives the actual affine pushforward of the remaining law. -/
theorem law_succ (n : ℕ) : law (n + 1) = geometricLetter.bind
    (fun a => (law n).map (Transfer.wordMap [a] (n + 1))) := by
  rw [law, wordPMF, PMF.map_bind]
  congr 1
  funext a
  rw [PMF.map_comp, law, PMF.map_comp]
  congr 1
  funext w
  exact Transfer.wordMap_offset_append [a] w (show [a].length ≤ n + 1 by simp)

/-- Each real atom is the original geometric mixture of affine tail atoms. -/
theorem mass_succ (n : ℕ) (y : ZMod (3 ^ (n + 1))) :
    mass (n + 1) y = ∑' a : ℕ+, (geometricLetter a).toReal *
      (((law n).map (Transfer.wordMap [a] (n + 1))) y).toReal := by
  rw [mass, law_succ, PMF.bind_apply, ENNReal.tsum_toReal_eq]
  · simp only [ENNReal.toReal_mul]
  · intro a
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

/-- The marker is the sum of all one-letter transfers of its preceding level. -/
theorem marker_succ (n : ℕ) (y : ZMod (3 ^ (n + 1))) :
    marker (n + 1) y = ∑' a : ℕ+,
      Transfer.wordOperator [a] (n + 1) (marker n) y := by
  rw [marker, density, mass_succ, ← mul_assoc, ← tsum_mul_left]
  apply tsum_congr
  intro a
  have h := Transfer.wordOperator_marker_eq_prefix [a]
    (show [a].length ≤ n + 1 by simp) y
  rw [Transfer.prefix_mass [a] (show [a].length ≤ n + 1 by simp)] at h
  change Transfer.wordOperator [a] (n + 1) (marker n) y =
    ((2 / 3 : ℝ) * 3 ^ (n + 1)) * ((1 / (2 : ℝ) ^ (a : ℕ)) *
      (((law n).map (Transfer.wordMap [a] (n + 1))) y).toReal) at h
  rw [h, geometricLetter_toReal, one_div_pow]

private theorem quarterSeries : HasSum (fun k : ℕ => (1 / 4 : ℝ) ^ k) (4 / 3) := by
  convert! hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) using 1
  norm_num

/-- All positive odd letters carry total transfer coefficient two. -/
theorem oddLetterCoefficient_hasSum :
    HasSum (fun k : ℕ => 3 / (2 : ℝ) ^ (2 * k + 1)) 2 := by
  convert! quarterSeries.mul_left (3 / 2 : ℝ) using 1
  · funext k
    rw [pow_add, pow_mul]
    norm_num
    rw [one_div_pow]
    ring
  · norm_num

/-- All positive even letters carry total transfer coefficient one. -/
theorem evenLetterCoefficient_hasSum :
    HasSum (fun k : ℕ => 3 / (2 : ℝ) ^ (2 * k + 2)) 1 := by
  convert! quarterSeries.mul_left (3 / 4 : ℝ) using 1
  · funext k
    rw [pow_add, pow_mul]
    norm_num
    rw [one_div_pow]
    ring
  · norm_num

end WordCertDensity.Reference
