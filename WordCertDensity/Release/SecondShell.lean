/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Release.PhysicalSecond
import WordCertDensity.Release.SecondLimit
import WordCertDensity.Density.Elementary

/-! # All-scale shell mass from the depth-eleven second-moment ceiling -/

namespace WordCertDensity.Density
open Filter
open scoped Topology BigOperators

/-- Every strict sub-bound is present at all large cutoffs for each fixed larger clock. -/
theorem secondEleven_shellMass (target : ℕ) (W : ℝ) (hW : 0 < W)
    (hsrc : Sources.AllScaleSources target W) (c : ℝ) (hc : criticalClock < c)
    (m : ℕ) (hm : 2 ≤ m) (hpaid : kappa * Analytic.mixingError m < W / 2)
    (u : ℝ) (hu : u < secondElevenMass W m) :
    Counting.ShellMass (goodTarget target c) u := by
  intro Λ hΛ
  let η := (W / 2 - kappa * Analytic.mixingError m) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨S, a, R, hR, hfin⟩ :=
    Counting.exists_coarse_sources target W hsrc c hc m hm η hη Λ hΛ
  have hk : 16 * Real.log 2 / 9 = kappa := by dsimp [kappa]; ring
  have hlim := secondElevenMass_tendsto W m hR
  have hmass := hlim.eventually (lt_mem_nhds hu)
  have hrad := hR.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) < 16))
  filter_upwards [hfin, hmass, hrad, eventually_gt_atTop (0 : ℝ)] with X hX hmassX hRX hpos
  refine ⟨S X, a X, ?_, ?_⟩
  · intro x hx
    obtain ⟨ho, hG, hl, hr, ha, hau⟩ := hX.1 x hx
    exact ⟨ho, hG, hl, hr.trans (mul_lt_mul_of_pos_right hX.2.1 hpos), ha, hau⟩
  · have hmark : W / 2 ≤ ∑ x ∈ S X, a X x * Reference.fan m (x : ZMod (3 ^ m)) := by
      have h := hX.2.2
      rw [hk] at h
      dsimp [η] at h
      linarith
    apply hmassX.le.trans
    apply Counting.physical_fan_mass_lower m X (R X) (W / 2) (S X) (a X)
      hpos hRX (half_pos hW).le _ hmark
    intro x hx
    obtain ⟨ho, _, hl, hr, ha, hau⟩ := hX.1 x hx
    exact ⟨ho, hl, hr, ha, hau⟩

end WordCertDensity.Density
