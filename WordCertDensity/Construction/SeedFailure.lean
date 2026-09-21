/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.Seed
public import WordCertDensity.Reference.FixedTime

/-! # The exact seed-window probability and its original failure mass -/

@[expose] public section

namespace WordCertDensity.Construction

/-- On its fixed depth the finite window is exactly the real centered valuation event. -/
theorem mem_seedWindow_centered {w : ValuationWord} {b : ℕ} (hw : w.length = b) (m : ℕ) :
    w ∈ seedWindow b m ↔ |ValuationWord.centeredTotal w| ≤ (m : ℝ) := by
  rw [mem_seedWindow_bounds, and_iff_right hw, ValuationWord.centeredTotal, hw, abs_le]
  constructor
  · rintro ⟨hl, hu⟩
    have hl' : 2 * (b : ℝ) ≤ (w.total : ℝ) + m := by exact_mod_cast hl
    have hu' : (w.total : ℝ) ≤ 2 * b + m := by exact_mod_cast hu
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    have hl' : 2 * (b : ℝ) ≤ (w.total : ℝ) + m := by linarith
    have hu' : (w.total : ℝ) ≤ 2 * b + m := by linarith
    constructor
    · exact_mod_cast hl'
    · exact_mod_cast hu'

/-- Original fixed-depth word probability equals the literal finite geometric mass. -/
theorem seedWindow_probability (b m : ℕ) :
    Gated.probability (Reference.wordPMF b) (fun w => w ∈ seedWindow b m) =
      Reference.stoppingMass (seedWindow b m) := by
  have he := Gated.probability_congr_on_support (Reference.wordPMF b)
    (fun w => w ∈ seedWindow b m) (Reference.prefixFamilyEvent (seedWindow b m))
    (fun w hw => by
      have hlen := (Reference.wordPMF_mem_support_iff b w).mp hw
      constructor
      · intro h
        exact ⟨w, h, List.prefix_rfl⟩
      · rintro ⟨u, hu, hp⟩
        have he := hp.eq_of_length (((mem_seedWindow_bounds u b m).mp hu).1.trans hlen.symm)
        subst u
        exact hu)
  exact he.trans (Reference.prefixFamily_probability _
    (fun w hw => ((mem_seedWindow_bounds w b m).mp hw).1.le) (seedWindow_prefixFree b m))

/-- The centered window event has the unconditioned finite seed mass. -/
theorem seedWindow_centered_probability (b m : ℕ) :
    Gated.probability (Reference.wordPMF b)
      (fun w => |ValuationWord.centeredTotal w| ≤ (m : ℝ)) =
      Reference.stoppingMass (seedWindow b m) := by
  have he := Gated.probability_congr_on_support (Reference.wordPMF b)
    (fun w => |ValuationWord.centeredTotal w| ≤ (m : ℝ)) (fun w => w ∈ seedWindow b m)
    (fun w hw => (mem_seedWindow_centered ((Reference.wordPMF_mem_support_iff b w).mp hw) m).symm)
  exact he.trans (seedWindow_probability b m)

/-- Seed rejection is exactly the strict complement of the valuation window. -/
theorem seedWindow_failure_probability (b m : ℕ) :
    Gated.probability (Reference.wordPMF b)
      (fun w => (m : ℝ) < |ValuationWord.centeredTotal w|) =
      1 - Reference.stoppingMass (seedWindow b m) := by
  have h := Gated.probability_compl (Reference.wordPMF b)
    (fun w => |ValuationWord.centeredTotal w| ≤ (m : ℝ))
  simpa only [not_le, seedWindow_centered_probability] using h

/-- Every positive-depth finite seed window has the corrected exponential failure bound. -/
theorem seedWindow_failure_le {b : ℕ} (hb : 0 < b) (m : ℕ) :
    1 - Reference.stoppingMass (seedWindow b m) ≤
      2 * Real.exp (-((m : ℝ) ^ 2 / (4 * (b : ℝ) + 3 * m))) := by
  rw [← seedWindow_failure_probability]
  exact (Gated.probability_mono_on_support (Reference.wordPMF b)
    (fun w => (m : ℝ) < |ValuationWord.centeredTotal w|)
    (fun w => (m : ℝ) ≤ |ValuationWord.centeredTotal w|)
    (fun _ _ hw => hw.le)).trans (Reference.word_absTail_fixedTime hb (Nat.cast_nonneg m))

/-- The actual ceiling-width seed retains its original exponentially small failure mass. -/
theorem seedWords_failure_le {b : ℕ} (hb : 0 < b) :
    1 - Reference.stoppingMass (seedWords b) ≤
      2 * Real.exp (-((seedWidth b : ℝ) ^ 2 / (4 * (b : ℝ) + 3 * seedWidth b))) :=
  seedWindow_failure_le hb (seedWidth b)

/-- The ceiling width is at least 32 cubed at the prescribed startup depth. -/
theorem seedWidth_lower {b : ℕ} (hb : 32 ^ 5 ≤ b) : (32 : ℝ) ^ 3 ≤ seedWidth b := by
  have hbase : (32 : ℝ) ^ 5 ≤ b := by exact_mod_cast hb
  have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 32 ^ 5) hbase
    (by norm_num : (0 : ℝ) ≤ 3 / 5)
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 32)] at h
  norm_num at h
  simpa only [seedWidth, show (32 : ℝ) ^ 3 = 32768 by norm_num] using
    h.trans (Nat.le_ceil _)

/-- Squaring the actual ceiling radius pays the fifth-power decay scale. -/
theorem seedWidth_square_ge {b : ℕ} (hb : 0 < b) :
    (b : ℝ) * (b : ℝ) ^ (1 / 5 : ℝ) ≤ (seedWidth b : ℝ) ^ 2 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hm : (b : ℝ) ^ (3 / 5 : ℝ) ≤ seedWidth b := Nat.le_ceil _
  have hs := (sq_le_sq₀ (Real.rpow_nonneg hb'.le _) (Nat.cast_nonneg (seedWidth b))).mpr hm
  have he : ((b : ℝ) ^ (3 / 5 : ℝ)) ^ 2 = (b : ℝ) * (b : ℝ) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_mul_natCast hb'.le]
    rw [show (3 / 5 : ℝ) * (2 : ℕ) = 1 + 1 / 5 by norm_num,
      Real.rpow_add hb', Real.rpow_one]
  rw [he] at hs
  exact hs

/-- The exact radius and small-width guard imply the uniform fifth-power exponent. -/
theorem seedWidth_failure_exponent {b : ℕ} (hb : 32 ^ 5 ≤ b) :
    (b : ℝ) ^ (1 / 5 : ℝ) / (4 + 3 / 512) ≤
      (seedWidth b : ℝ) ^ 2 / (4 * (b : ℝ) + 3 * seedWidth b) := by
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hm := seedWidth_small hb
  have hs := seedWidth_square_ge hbpos
  have hd : 4 * (b : ℝ) + 3 * seedWidth b ≤ (4 + 3 / 512 : ℝ) * b := by linarith
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4 + 3 / 512) (by positivity)).mpr
  have h1 := mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg hb'.le (1 / 5 : ℝ))
  have h2 := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4 + 3 / 512)
  nlinarith

/-- The actual seed failure has the manuscript's uniform fifth-power exponential envelope. -/
theorem seedWords_failure_power_le {b : ℕ} (hb : 32 ^ 5 ≤ b) :
    1 - Reference.stoppingMass (seedWords b) ≤
      2 * Real.exp (-((b : ℝ) ^ (1 / 5 : ℝ) / (4 + 3 / 512))) := by
  exact (seedWords_failure_le (lt_of_lt_of_le (by norm_num) hb)).trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg (seedWidth_failure_exponent hb))) (by norm_num))

end WordCertDensity.Construction
