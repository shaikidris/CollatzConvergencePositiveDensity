/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Release.CanonicalSecond

/-! # A depth-eleven density formula for every clock above the threshold -/

namespace WordCertDensity.Density

/-- A strict sub-bound clipped to the radial conversion domain. -/
noncomputable def secondElevenRadialMass (W : ℝ) (m : ℕ) : ℝ :=
  min (secondElevenMass W m / 2) (Real.log (3 / 2) / 2)

/-- The separately named depth-eleven density formula at one paid coarse level. -/
noncomputable def secondElevenDensity (W : ℝ) (m : ℕ) : ℝ :=
  Counting.radial (secondElevenRadialMass W m)

/-- Positive scores give positive radial mass within both required bounds. -/
theorem secondElevenRadialMass_bounds {W : ℝ} (hW : 0 < W) (m : ℕ) :
    0 < secondElevenRadialMass W m ∧
      secondElevenRadialMass W m < secondElevenMass W m ∧
      secondElevenRadialMass W m ≤ Real.log (3 / 2) / 2 := by
  have hp := secondElevenMass_pos hW m
  have hl : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨lt_min (half_pos hp) (half_pos hl), ?_, min_le_right _ _⟩
  exact (min_le_left _ _).trans_lt (by linarith)

/-- Actual all-scale sources give the same positive formula at every fixed larger clock. -/
theorem secondElevenDensity_target (target : ℕ) (W : ℝ) (hW : 0 < W)
    (hsrc : Sources.AllScaleSources target W) (m : ℕ) (hm : 2 ≤ m)
    (hpaid : kappa * Analytic.mixingError m < W / 2) :
    TargetBound target (secondElevenDensity W m) := by
  obtain ⟨hp, hs, hd⟩ := secondElevenRadialMass_bounds hW m
  refine ⟨Counting.radial_pos hp, ?_⟩
  intro c hc
  exact Counting.radialConversion (goodTarget target c) (secondElevenRadialMass W m)
    (goodTarget_dyadicallyClosed hc) hp.le hd
    (secondEleven_shellMass target W hW hsrc c hc m hm hpaid _ hs)

/-- All canonical source premises are discharged for the depth-eleven density formula. -/
theorem canonicalSecondDensity (m : ℕ) (hm : 2 ≤ m)
    (hpaid : kappa * Analytic.mixingError m < Construction.persistentRootScore / 2) :
    EveryClockDensityBound (secondElevenDensity Construction.persistentRootScore m) :=
  secondElevenDensity_target 1 Construction.persistentRootScore
    Construction.persistentRootScore_domain.1 Sources.canonicalSources m hm hpaid

/-- One paid level gives a positive canonical density formula before every clock. -/
theorem exists_canonicalSecondDensity :
    ∃ m : ℕ, 2 ≤ m ∧
      kappa * Analytic.mixingError m < Construction.persistentRootScore / 2 ∧
      EveryClockDensityBound (secondElevenDensity Construction.persistentRootScore m) := by
  obtain ⟨m, hm, hpaid⟩ := exists_coarseLevel Construction.persistentRootScore_domain.1
  exact ⟨m, hm, hpaid, canonicalSecondDensity m hm hpaid⟩

end WordCertDensity.Density
