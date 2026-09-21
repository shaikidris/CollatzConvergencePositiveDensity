/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingGeometry
public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingNumerics

/-! # Rounded rectangle and old top-row guards -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The outward-rounded left endpoint of the E.5 rectangle. -/
noncomputable def longCrossingRectangleLo (s j p : ℕ) (W : ℝ) : ℕ :=
  ⌊(j : ℝ) + (s : ℝ) / 4 + p - W⌋₊

/-- The outward-rounded right endpoint of the E.5 rectangle. -/
noncomputable def longCrossingRectangleHi (s j p : ℕ) (W : ℝ) : ℕ :=
  ⌈(j : ℝ) + (s : ℝ) / 4 + p + W⌉₊

/-- Rounding loses at most two columns and preserves the old-top horizontal
budget. Every hypothesis here is a scalar budget, not a geometry assumption. -/
theorem longCrossing_rectangle_rounding (s j p Y : ℕ) (W : ℝ)
    (hs : 64 ≤ s) (hW0 : 0 ≤ W)
    (hW : W ≤ (s : ℝ) / 64) (hY : (Y : ℝ) ≤ (s : ℝ) / 64)
    (hp : (p : ℝ) ≤ (s : ℝ) / 64) :
    Y ≤ longCrossingRectangleLo s j p W ∧
    j ≤ longCrossingRectangleLo s j p W - Y ∧
    longCrossingRectangleLo s j p W - Y ≤ longCrossingRectangleHi s j p W ∧
    ((longCrossingRectangleHi s j p W : ℕ) : ℝ) - j ≤ 5 * (s : ℝ) / 16 ∧
    ((longCrossingRectangleHi s j p W : ℕ) : ℝ) -
      (longCrossingRectangleLo s j p W - Y : ℕ) ≤ 2 * W + Y + 2 := by
  let c : ℝ := (j : ℝ) + (s : ℝ) / 4 + p
  have hsR : (64 : ℝ) ≤ s := by exact_mod_cast hs
  have hjR := Nat.cast_nonneg (α := ℝ) j
  have hpR := Nat.cast_nonneg (α := ℝ) p
  have hleft : (j : ℝ) + Y ≤ c - W := by dsimp [c]; linarith
  have hleft0 : 0 ≤ c - W := by linarith [Nat.cast_nonneg (α := ℝ) Y]
  have hright0 : 0 ≤ c + W := by linarith
  have hlo : j + Y ≤ longCrossingRectangleLo s j p W := by
    apply Nat.le_floor
    push_cast
    exact hleft
  have hYlo : Y ≤ longCrossingRectangleLo s j p W := by omega
  have hfloor : ((longCrossingRectangleLo s j p W : ℕ) : ℝ) ≤ c - W :=
    Nat.floor_le hleft0
  have hfloor' : c - W < ((longCrossingRectangleLo s j p W : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one (c - W)
  have hceil : c + W ≤ ((longCrossingRectangleHi s j p W : ℕ) : ℝ) := Nat.le_ceil _
  have hceil' : ((longCrossingRectangleHi s j p W : ℕ) : ℝ) < c + W + 1 :=
    Nat.ceil_lt_add_one hright0
  have hlohi : longCrossingRectangleLo s j p W ≤ longCrossingRectangleHi s j p W := by
    have hr : ((longCrossingRectangleLo s j p W : ℕ) : ℝ) ≤
        ((longCrossingRectangleHi s j p W : ℕ) : ℝ) := by linarith
    exact_mod_cast hr
  refine ⟨hYlo, by omega, (Nat.sub_le _ _).trans hlohi, ?_, ?_⟩
  · dsimp [c] at hceil'
    linarith
  · rw [Nat.cast_sub hYlo]
    linarith

/-- The outward-rounded rectangle contains every point in the real window. -/
theorem longCrossing_rectangle_contains_window (s j p x : ℕ) (W : ℝ)
    (hx : |(x : ℝ) - ((j : ℝ) + (s : ℝ) / 4 + p)| ≤ W) :
    longCrossingRectangleLo s j p W ≤ x ∧ x ≤ longCrossingRectangleHi s j p W := by
  have habs := abs_le.mp hx
  constructor
  · apply Nat.floor_le_of_le
    linarith
  · have hh := Nat.le_ceil ((j : ℝ) + (s : ℝ) / 4 + p + W)
    have hr : (x : ℝ) ≤ ((longCrossingRectangleHi s j p W : ℕ) : ℝ) := by
      change _ ≤ (⌈(j : ℝ) + (s : ℝ) / 4 + p + W⌉₊ : ℝ)
      linarith
    exact_mod_cast hr

/-- The exact logarithmic slope needed by the old top-row budget. -/
theorem longCrossing_log_slope : 5 * Real.log 9 ≤ 16 * Real.log 2 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 9 ^ 5)
    (by norm_num : (9 : ℝ) ^ 5 ≤ 2 ^ 16)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  exact h

/-- Rounded endpoints and scalar budgets produce the actual old top row. -/
theorem longCrossing_rectangle_old_top
    (n : ℕ) (ξ : ZMod (3 ^ n)) (old j p Y : ℕ) (top l : ℤ) (W : ℝ)
    (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (hold : 2 * old < n)
    (hstart : inPhaseTriangleIntMul n ξ old top j l)
    (hs : 64 ≤ (top - l).toNat) (hW0 : 0 ≤ W)
    (hW : W ≤ ((top - l).toNat : ℝ) / 64)
    (hY : (Y : ℝ) ≤ ((top - l).toNat : ℝ) / 64)
    (hp : (p : ℝ) ≤ ((top - l).toNat : ℝ) / 64) :
    ∀ r ∈ Finset.Icc (longCrossingRectangleLo (top - l).toNat j p W - Y)
        (longCrossingRectangleHi (top - l).toNat j p W),
      inPhaseTriangleIntMul n ξ old top r top := by
  have hb := longCrossing_rectangle_rounding (top - l).toNat j p Y W hs hW0 hW hY hp
  apply rectangle_oldTop_contains n ξ old j _ _ Y top l hn hξ hold hstart
    (hstart.1.trans hb.2.1)
  have hlog9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hbound := mul_le_mul_of_nonneg_right hb.2.2.2.1 hlog9
  have hslope := mul_le_mul_of_nonneg_left longCrossing_log_slope
    (Nat.cast_nonneg (α := ℝ) (top - l).toNat)
  nlinarith

end WordCertDensity.LocalPrimitive
