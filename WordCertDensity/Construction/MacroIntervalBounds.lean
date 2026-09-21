/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.MacroLevels

/-! # Logarithmic endpoint changes and positive linear overlap room -/

namespace WordCertDensity.Construction

open Filter Asymptotics
open scoped Topology

/-- A bounded error about a linear endpoint controls every finite increment. -/
theorem linearEndpoint_increment {H : ℕ → ℝ} {c offset K : ℝ} {B d : ℕ}
    (hB : |H B-(c*B+offset)| ≤ K) (hnext : |H (B+d)-(c*((B+d : ℕ) : ℝ)+offset)| ≤ K) :
    |H (B+d)-H B| ≤ |c| * d+2*K := by
  have hb := abs_le.mp hB
  have hn := abs_le.mp hnext
  have hc1 := mul_le_mul_of_nonneg_right (neg_abs_le c) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hc2 := mul_le_mul_of_nonneg_right (le_abs_self c) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  simp only [Nat.cast_add] at hn
  rw [abs_le]
  constructor <;> nlinarith

/-- The actual macro schedule gives logarithmic endpoint increments. -/
theorem linearEndpoint_macro_isBigO {L : ℝ} (hL : 0 ≤ L) {H : ℕ → ℝ} {c offset K : ℝ}
    (hK : 0 ≤ K) (h : ∀ᶠ B : ℕ in atTop, |H B-(c*B+offset)| ≤ K) :
    (fun B : ℕ => H (B+macroLength L B)-H B) =O[atTop]
      (fun B : ℕ => Real.log ((B : ℝ)+2)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 h
  apply IsBigO.of_bound (|c| * (L+2)+4*K)
  filter_upwards [eventually_ge_atTop N] with B hB
  have hlog : 0 < Real.log ((B : ℝ)+2) := by linarith [log_count_add_two_lower B]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog]
  have hinc := linearEndpoint_increment (hN B hB) (hN (B+macroLength L B) (by omega))
  have hm := mul_le_mul_of_nonneg_left (macroLength_le_log hL B) (abs_nonneg c)
  have hk := mul_le_mul_of_nonneg_left (le_of_lt (log_count_add_two_lower B)) hK
  nlinarith

/-- A positive linear lower envelope makes an endpoint diverge. -/
theorem linearEndpoint_tendsto {H : ℕ → ℝ} {c offset K : ℝ} (hc : 0 < c)
    (h : ∀ᶠ B : ℕ in atTop, |H B-(c*B+offset)| ≤ K) : Tendsto H atTop atTop := by
  apply tendsto_atTop.2
  intro T
  filter_upwards [h, eventually_ge_atTop ⌈(T-offset+K)/c⌉₊] with B hB hcut
  have hh : (T-offset+K)/c ≤ (B : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hcut)
  have hmul := (div_le_iff₀ hc).mp hh
  have hb := abs_le.mp hB
  nlinarith

/-- Distinct linear rates dominate the exact logarithmic macro increment and all bounded errors. -/
theorem linearEndpoints_macro_overlap {L : ℝ} (hL : 0 ≤ L)
    {A D : ℕ → ℝ} {a d pa pd Ka Kd : ℝ} (hgap : a < d)
    (hA : ∀ᶠ B : ℕ in atTop, |A B-(a*B+pa)| ≤ Ka)
    (hD : ∀ᶠ B : ℕ in atTop, |D B-(d*B+pd)| ≤ Kd) :
    ∀ᶠ B : ℕ in atTop, A (B+macroLength L B) ≤ D B := by
  let C := pa-pd+Ka+Kd
  have ht : Tendsto (fun B : ℕ => a*((macroLength L B : ℝ)/B)+C*(1/(B : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((macroLength_div_count_tendsto hL).const_mul a).add
        ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C)
  have hsmall := (tendsto_order.1 ht).2 (d-a) (by linarith)
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hA.and hD)
  filter_upwards [hsmall, eventually_ge_atTop N, eventually_ge_atTop 1] with B hs hB hpos
  have hBR : (0 : ℝ) < B := by
    have h : (1 : ℝ) ≤ B := by exact_mod_cast hpos
    linarith
  have hm := mul_lt_mul_of_pos_right hs hBR
  have he : (a*((macroLength L B : ℝ)/B)+C*(1/(B : ℝ)))*(B : ℝ) =
      a*(macroLength L B : ℝ)+C := by field_simp [ne_of_gt hBR]
  rw [he] at hm
  have ha := abs_le.mp (hN (B+macroLength L B) (by omega)).1
  have hd := abs_le.mp (hN B hB).2
  simp only [Nat.cast_add] at ha
  dsimp only [C] at hm
  nlinarith

end WordCertDensity.Construction
