/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.FirstCrossing
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The fixed-depth seed family

The family contains all positive valuation words at the prescribed depth in
the symmetric total-valuation window. Its reference mass is unconditioned.
The stage schedule uses natural division, and the width is the literal ceiling.
-/

@[expose] public section

namespace WordCertDensity.Construction

/-- The seed depths grow by the floor of one percent of the current depth. -/
def seedSize (b : ℕ) : ℕ → ℕ
  | 0 => b
  | t + 1 => seedSize b t + seedSize b t / 100

/-- The manuscript's symmetric window radius. -/
noncomputable def seedWidth (b : ℕ) : ℕ := ⌈(b : ℝ) ^ (3 / 5 : ℝ)⌉₊

/-- A finite, exactly enumerated depth and valuation window with integer radius. -/
def seedWindow (b m : ℕ) : Finset ValuationWord :=
  (wordsBelow (2 * b + m + 1)).filter fun w => w.length = b ∧ 2 * b ≤ w.total + m

/-- The exact seed at a given depth uses its prescribed ceiling radius. -/
noncomputable def seedWords (b : ℕ) : Finset ValuationWord := seedWindow b (seedWidth b)

/-- Integer inequalities retain both sides of the symmetric window without truncation. -/
theorem mem_seedWindow_bounds (w : ValuationWord) (b m : ℕ) :
    w ∈ seedWindow b m ↔ w.length = b ∧ 2 * b ≤ w.total + m ∧ w.total ≤ 2 * b + m := by
  simp only [seedWindow, Finset.mem_filter, mem_wordsBelow]
  omega

/-- The finite enumeration is exactly the displayed absolute-value window. -/
theorem mem_seedWindow (w : ValuationWord) (b m : ℕ) :
    w ∈ seedWindow b m ↔ w.length = b ∧ |(w.total : ℤ) - 2 * b| ≤ (m : ℤ) := by
  rw [mem_seedWindow_bounds, abs_le]
  omega

/-- The manuscript family fixes the depth and uses its literal ceiling width. -/
theorem mem_seedWords (w : ValuationWord) (b : ℕ) :
    w ∈ seedWords b ↔ w.length = b ∧ |(w.total : ℤ) - 2 * b| ≤ (seedWidth b : ℤ) :=
  mem_seedWindow w b (seedWidth b)

/-- Fixed depth prevents any selected word from properly extending another. -/
theorem seedWindow_prefixFree (b m : ℕ) :
    (seedWindow b m : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v) := by
  intro u hu v hv hne hp
  have hlen := ((mem_seedWindow_bounds u b m).mp hu).1.trans
    ((mem_seedWindow_bounds v b m).mp hv).1.symm
  exact hne (hp.eq_of_length hlen)

/-- Every fixed-depth seed is prefix-free, including its zero-depth boundary. -/
theorem seedWords_prefixFree (b : ℕ) :
    (seedWords b : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v) :=
  seedWindow_prefixFree b (seedWidth b)

/-- The original geometric mass lies in the unit interval without renormalization. -/
theorem seedWords_mass_bounds (b : ℕ) :
    0 ≤ Reference.stoppingMass (seedWords b) ∧ Reference.stoppingMass (seedWords b) ≤ 1 :=
  ⟨Reference.stoppingMass_nonneg _, Reference.stoppingMass_le_one _ (seedWords_prefixFree b)⟩

/-- Seed depths never decrease below their initial depth. -/
theorem seedSize_ge (b t : ℕ) : b ≤ seedSize b t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => simp only [seedSize]; omega

/-- At a positive one-percent increment, depth grows by at least one per stage. -/
theorem seedSize_ge_add {b : ℕ} (hb : 100 ≤ b) (t : ℕ) : b + t ≤ seedSize b t := by
  induction t with
  | zero => simp [seedSize]
  | succ t ih =>
    have h := seedSize_ge b t
    simp only [seedSize]
    omega

/-- Both geometric schedule bounds retain the floor debit at every stage. -/
theorem seedSize_geometric {b : ℕ} (hb : 200 ≤ b) (t : ℕ) :
    (b : ℚ) * (201 / 200 : ℚ) ^ t ≤ seedSize b t ∧
      (seedSize b t : ℚ) ≤ b * (101 / 100 : ℚ) ^ t := by
  induction t with
  | zero => simp [seedSize]
  | succ t ih =>
    have hn := seedSize_ge b t
    have hlo : seedSize b t ≤ 200 * (seedSize b t / 100) := by omega
    have hhi : 100 * (seedSize b t / 100) ≤ seedSize b t := by omega
    have hloQ : (seedSize b t : ℚ) ≤ 200 * (seedSize b t / 100 : ℕ) := by
      exact_mod_cast hlo
    have hhiQ : (100 : ℚ) * (seedSize b t / 100 : ℕ) ≤ seedSize b t := by
      exact_mod_cast hhi
    simp only [seedSize, Nat.cast_add, pow_succ]
    constructor <;> nlinarith [ih.1, ih.2]

/-- The literal ceiling is bounded by twice its power for every positive depth. -/
theorem seedWidth_le_twice {b : ℕ} (hb : 1 ≤ b) :
    (seedWidth b : ℝ) ≤ 2 * (b : ℝ) ^ (3 / 5 : ℝ) := by
  have hbase : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hpow := Real.one_le_rpow hbase (by norm_num : (0 : ℝ) ≤ 3 / 5)
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg b) (3 / 5 : ℝ))
  unfold seedWidth
  linarith

/-- At the specified startup depth the complementary power is at least 1024. -/
theorem seed_complementary_power {b : ℕ} (hb : 32 ^ 5 ≤ b) :
    (1024 : ℝ) ≤ (b : ℝ) ^ (2 / 5 : ℝ) := by
  have hbase : (32 : ℝ) ^ 5 ≤ b := by exact_mod_cast hb
  have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 32 ^ 5) hbase
    (by norm_num : (0 : ℝ) ≤ 2 / 5)
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 32)] at h
  norm_num at h
  exact h

/-- The ceiling width is at most one part in 512 at every allowed seed depth. -/
theorem seedWidth_small {b : ℕ} (hb : 32 ^ 5 ≤ b) : (seedWidth b : ℝ) ≤ b / 512 := by
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hpow := seed_complementary_power hb
  have hid : (b : ℝ) ^ (3 / 5 : ℝ) * (b : ℝ) ^ (2 / 5 : ℝ) = b := by
    rw [← Real.rpow_add (by exact_mod_cast hbpos)]
    norm_num
  have hmul := mul_le_mul_of_nonneg_left hpow
    (Real.rpow_nonneg (Nat.cast_nonneg b) (3 / 5 : ℝ))
  have hw := seedWidth_le_twice (Nat.succ_le_of_lt hbpos)
  nlinarith

/-- The selected valuation gives the strict displacement needed by physical geometry. -/
theorem seedWords_displacement {b : ℕ} (hb : 32 ^ 5 ≤ b) {w : ValuationWord}
    (hw : w ∈ seedWords b) : (b : ℝ) / 3 < displacement w := by
  obtain ⟨hlen, hlo, _⟩ := (mem_seedWindow_bounds w b (seedWidth b)).mp hw
  have hl : (2 : ℝ) * b ≤ w.total + seedWidth b := by exact_mod_cast hlo
  have hwidth := seedWidth_small hb
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hb : 0 < b)
  have hlog := mul_lt_mul_of_pos_right Head.logRatio_lt_eight_fifths hbpos
  unfold displacement
  rw [hlen]
  nlinarith

end WordCertDensity.Construction
