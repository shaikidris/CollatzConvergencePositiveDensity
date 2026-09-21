/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Exact enumeration of the manuscript's open odd band -/

@[expose] public section

namespace WordCertDensity.Counting

noncomputable section

/-- Odd integers strictly between the two real endpoints, with a finite enumeration bound. -/
def oddOpenBand (X s : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌈s * X⌉₊ + 1)).filter
    (fun x => Odd x ∧ X < (x : ℝ) ∧ (x : ℝ) < s * X)

/-- The first possible index in the odd parametrization, respecting a strict lower endpoint. -/
def oddBandLowerIndex (X : ℝ) : ℕ := ⌊(X - 1) / 2⌋₊ + 1

/-- The excluded upper index in the odd parametrization. -/
def oddBandUpperIndex (X s : ℝ) : ℕ := ⌈(s * X - 1) / 2⌉₊

/-- The finite enumeration imposes exactly the intended open interval and parity conditions. -/
theorem mem_oddOpenBand (X s : ℝ) (x : ℕ) :
    x ∈ oddOpenBand X s ↔ Odd x ∧ X < (x : ℝ) ∧ (x : ℝ) < s * X := by
  classical
  simp only [oddOpenBand, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    have := Nat.lt_ceil.mpr h.2.2
    exact ⟨by omega, h⟩

/-- The first odd value is above X and at most X+2, including odd integer boundaries. -/
theorem oddBand_lower_bounds {X : ℝ} (hX : 1 ≤ X) :
    X < (2 * oddBandLowerIndex X + 1 : ℕ) ∧
      ((2 * oddBandLowerIndex X + 1 : ℕ) : ℝ) ≤ X + 2 := by
  have hf := Nat.floor_le (by linarith : 0 ≤ (X - 1) / 2)
  have hl := Nat.lt_floor_add_one ((X - 1) / 2)
  simp only [oddBandLowerIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  constructor <;> linarith

/-- The excluded odd value is at least sX and strictly below sX+2. -/
theorem oddBand_upper_bounds {X s : ℝ} (hX : 1 ≤ X) (hs : 1 < s) :
    s * X ≤ ((2 * oddBandUpperIndex X s + 1 : ℕ) : ℝ) ∧
      ((2 * oddBandUpperIndex X s + 1 : ℕ) : ℝ) < s * X + 2 := by
  have hpos : 0 ≤ (s * X - 1) / 2 := by nlinarith
  have hc := Nat.le_ceil ((s * X - 1) / 2)
  have hu := Nat.ceil_lt_add_one hpos
  simp only [oddBandUpperIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  constructor <;> linarith

/-- The half-open index interval is correctly ordered even when the odd band is empty. -/
theorem oddBand_indices_le {X s : ℝ} (hX : 1 ≤ X) (hs : 1 < s) :
    oddBandLowerIndex X ≤ oddBandUpperIndex X s := by
  have hf := Nat.floor_le (by linarith : 0 ≤ (X - 1) / 2)
  have hlt : ((⌊(X - 1) / 2⌋₊ : ℕ) : ℝ) < (s * X - 1) / 2 := by nlinarith
  exact Nat.succ_le_of_lt (Nat.lt_ceil.mpr hlt)

/-- Consecutive odd indices describe the exact open band. -/
theorem oddOpenBand_eq_image {X s : ℝ} (hX : 1 ≤ X) :
    oddOpenBand X s =
      (Finset.Ico (oddBandLowerIndex X) (oddBandUpperIndex X s)).image (fun n => 2 * n + 1) := by
  classical
  have hnonneg : 0 ≤ (X - 1) / 2 := by linarith
  ext x
  rw [mem_oddOpenBand, Finset.mem_image]
  constructor
  · rintro ⟨hxodd, hxL, hxU⟩
    obtain ⟨n, rfl⟩ := (odd_iff_exists_bit1.mp hxodd)
    refine ⟨n, Finset.mem_Ico.mpr ⟨?_, ?_⟩, rfl⟩
    · apply Nat.succ_le_of_lt
      apply (Nat.floor_lt hnonneg).mpr
      push_cast at hxL
      linarith
    · apply Nat.lt_ceil.mpr
      push_cast at hxU
      linarith
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨hnL, hnU⟩ := Finset.mem_Ico.mp hn
    have hl : (X - 1) / 2 < (n : ℝ) :=
      (Nat.floor_lt hnonneg).mp (Nat.lt_of_succ_le hnL)
    have hu : (n : ℝ) < (s * X - 1) / 2 := Nat.lt_ceil.mp hnU
    refine ⟨odd_iff_exists_bit1.mpr ⟨n, rfl⟩, ?_, ?_⟩ <;> push_cast <;> linarith

/-- The exact count is the difference of the two boundary indices. -/
theorem card_oddOpenBand {X s : ℝ} (hX : 1 ≤ X) :
    (oddOpenBand X s).card = oddBandUpperIndex X s - oddBandLowerIndex X := by
  rw [oddOpenBand_eq_image hX, Finset.card_image_of_injective]
  · exact Nat.card_Ico _ _
  · intro a b hab
    dsimp at hab
    omega

/-- The odd count has an absolute error at most one at every admitted cutoff. -/
theorem card_oddOpenBand_error {X s : ℝ} (hX : 1 ≤ X) (hs : 1 < s) :
    |((oddOpenBand X s).card : ℝ) - (s - 1) * X / 2| ≤ 1 := by
  have hidx := oddBand_indices_le hX hs
  have hl := oddBand_lower_bounds hX
  have hu := oddBand_upper_bounds hX hs
  rw [card_oddOpenBand hX, Nat.cast_sub hidx, abs_le]
  push_cast at hl hu
  constructor <;> nlinarith

end

end WordCertDensity.Counting
