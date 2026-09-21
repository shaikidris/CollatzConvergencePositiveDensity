/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.Coarse
import WordCertDensity.Sources.Objects
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Coarse marked mass at every sufficiently large physical cutoff -/

namespace WordCertDensity.Counting

open Filter
open scoped Topology BigOperators

/-- The actual radius and vanishing modulus boundary give the sharp harmonic limit. -/
theorem harmonic_coefficient_tendsto {k : ℝ → ℕ} {R : ℝ → ℝ}
    (hk : Tendsto (fun X => (3 : ℝ) ^ k X / X) atTop (𝓝 0))
    (hR : Tendsto R atTop (𝓝 16)) :
    Tendsto (fun X => (3 : ℝ) ^ k X / X + Real.log (R X) / 2)
      atTop (𝓝 (2 * Real.log 2)) := by
  have hl : Tendsto (fun X => Real.log (R X)) atTop (𝓝 (Real.log 16)) :=
    (Real.continuousAt_log (by norm_num : (16 : ℝ) ≠ 0)).tendsto.comp hR
  have he : Real.log (16 : ℝ) / 2 = 2 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
    ring
  simpa only [zero_add, he] using hk.add (hl.div_const 2)

/-- A fixed coarse modulus has the same limiting capacity at the actual source radius. -/
theorem fixed_harmonic_coefficient_tendsto (m : ℕ) {R : ℝ → ℝ}
    (hR : Tendsto R atTop (𝓝 16)) :
    Tendsto (fun X => (3 : ℝ) ^ m / X + Real.log (R X) / 2)
      atTop (𝓝 (2 * Real.log 2)) := by
  apply harmonic_coefficient_tendsto (k := fun _ => m) _ hR
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_inv_atTop_zero.const_mul ((3 : ℝ) ^ m))

/-- Choose the graft loss before the cutoff and retain the exact coarse error at all large scales. -/
theorem exists_coarse_sources (target : ℕ) (W : ℝ)
    (hsrc : Sources.AllScaleSources target W) (c : ℝ) (hc : criticalClock < c)
    (m : ℕ) (hm : 2 ≤ m) (η : ℝ) (hη : 0 < η) (Λ : ℝ) (hΛ : 16 < Λ) :
    ∃ (S : ℝ → Finset ℕ) (a : ℝ → ℕ → ℝ) (R : ℝ → ℝ),
      Tendsto R atTop (𝓝 16) ∧
      ∀ᶠ X in atTop, Sources.SourceAt target c X (R X) (S X) (a X) ∧ R X < Λ ∧
        W - (16 * Real.log 2 / 9) * Analytic.mixingError m - η ≤
          ∑ x ∈ S X, a X x * Reference.fan m (x : ZMod (3 ^ m)) := by
  obtain ⟨S, a, k, R, hR, hk, hprec, hfin⟩ := hsrc c hc (η / 2) (by positivity) Λ hΛ
  refine ⟨S, a, R, hR, ?_⟩
  have hpay : Tendsto (fun X => (8 / 9 : ℝ) *
      ((3 : ℝ) ^ k X / X + Real.log (R X) / 2) * Analytic.mixingError m)
      atTop (𝓝 ((16 * Real.log 2 / 9) * Analytic.mixingError m)) := by
    convert ((harmonic_coefficient_tendsto hprec hR).const_mul (8 / 9 : ℝ)).mul_const
      (Analytic.mixingError m) using 1
    ring
  have hpaid := hpay.eventually (gt_mem_nhds
    (show (16 * Real.log 2 / 9) * Analytic.mixingError m <
      (16 * Real.log 2 / 9) * Analytic.mixingError m + η / 2 by linarith))
  have hrad := hR.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) < 16))
  filter_upwards [hfin, hk.eventually (eventually_ge_atTop m), hpaid, hrad,
    eventually_gt_atTop (0 : ℝ)] with X hX hmk hcost hRX hpos
  refine ⟨hX.1, hX.2.1, ?_⟩
  have hdata : ∀ x ∈ S X, Odd x ∧ X ≤ (x : ℝ) ∧ (x : ℝ) < R X * X ∧
      0 ≤ a X x ∧ a X x ≤ (x : ℝ)⁻¹ := by
    intro x hx
    obtain ⟨ho, _, hl, hu, hn, hw⟩ := hX.1 x hx
    exact ⟨ho, hl, hu, hn, hw⟩
  have hcoarse := coarse_fan_mass m (k X) X (R X) (S X) (a X) hm hmk hpos hRX hdata
  have hmark := hX.2.2
  linarith

end WordCertDensity.Counting
