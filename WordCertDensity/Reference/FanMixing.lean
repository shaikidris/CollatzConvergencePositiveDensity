/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.Fan
import WordCertDensity.Analytic.FullMixing
import Mathlib.Tactic.Ring

/-! # Full-group fine-to-coarse discrepancy of the actual affine fan -/

namespace WordCertDensity.Reference

/-- The literal affine fan commutes with ternary reduction. -/
theorem project_fanMap {m k : ℕ} (h : m ≤ k) (j : ℕ) (x : ZMod (3 ^ k)) :
    project h (fanMap k j x) = fanMap m j (project h x) := by
  simp [fanMap, map_add, map_mul, map_pow, map_natCast, map_ofNat]

/-- The full fan pays its geometric total times the marker mixing error. -/
theorem fan_mean_le_mixingError {m k : ℕ} (hm : 1 ≤ m) (h : m ≤ k) :
    mean k (fun x => |fan k x - fan m (project h x)|) ≤
      (8 / 9 : ℝ) * Analytic.mixingError m := by
  let d : ℕ → ZMod (3 ^ k) → ℝ := fun j x =>
    (4 : ℝ) ^ (-(j : ℤ)) *
      (marker k (fanMap k j x) - marker m (fanMap m j (project h x)))
  have hs (x : ZMod (3 ^ k)) : Summable (fun j => d j x) := by
    simpa only [d, mul_sub] using (fan_summable k x).sub (fan_summable m (project h x))
  have habs (x : ZMod (3 ^ k)) : Summable (fun j => |d j x|) := (hs x).abs
  have heq (x : ZMod (3 ^ k)) : fan k x - fan m (project h x) = ∑' j, d j x := by
    simp only [fan, d, mul_sub,
      (fan_summable k x).tsum_sub (fan_summable m (project h x))]
  have hpoint (x : ZMod (3 ^ k)) :
      |fan k x - fan m (project h x)| ≤ ∑' j, |d j x| := by
    rw [heq]
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun j => d j x)
        (by simpa only [Real.norm_eq_abs] using habs x)
  have hd (j : ℕ) (x : ZMod (3 ^ k)) : |d j x| =
      (4 : ℝ) ^ (-(j : ℤ)) *
        |marker k (fanMap k j x) - marker m (project h (fanMap k j x))| := by
    rw [project_fanMap]
    dsimp [d]
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num) _)]
  calc
    _ ≤ mean k (fun x => ∑' j, |d j x|) := mean_mono k _ _ hpoint
    _ = ∑' j, mean k (fun x => |d j x|) := mean_tsum k _ habs
    _ = ∑' j : ℕ, (4 : ℝ) ^ (-(j : ℤ)) *
        mean k (fun x => |marker k x - marker m (project h x)|) := by
      apply tsum_congr
      intro j
      calc
        _ = mean k (fun x => (4 : ℝ) ^ (-(j : ℤ)) *
            |marker k (fanMap k j x) - marker m (project h (fanMap k j x))|) :=
          congrArg (mean k) (funext (hd j))
        _ = (4 : ℝ) ^ (-(j : ℤ)) * mean k (fun x =>
            |marker k (fanMap k j x) - marker m (project h (fanMap k j x))|) :=
          mean_mul k _ _
        _ = _ := congrArg (fun z => (4 : ℝ) ^ (-(j : ℤ)) * z)
          (mean_fanMap k j (fun x => |marker k x - marker m (project h x)|))
    _ = (4 / 3 : ℝ) * mean k (fun x => |marker k x - marker m (project h x)|) := by
      rw [tsum_mul_right, fanCoefficient_hasSum.tsum_eq]
    _ ≤ (4 / 3 : ℝ) * ((2 / 3 : ℝ) * Analytic.mixingError m) :=
      mul_le_mul_of_nonneg_left (Analytic.marker_mean_le_mixingError hm h) (by norm_num)
    _ = _ := by ring

end WordCertDensity.Reference
