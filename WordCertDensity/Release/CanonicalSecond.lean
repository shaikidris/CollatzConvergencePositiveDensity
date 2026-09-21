/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Release.SecondShell
import WordCertDensity.Density.Qualitative

/-! # Canonical score and a clock-independent second-moment shell bound -/

namespace WordCertDensity.Density

/-- The actual canonical score gives the displayed shell bound at every paid level. -/
theorem canonicalSecondShell (m : ℕ) (hm : 2 ≤ m)
    (hpaid : kappa * Analytic.mixingError m < Construction.persistentRootScore / 2)
    (c : ℝ) (hc : criticalClock < c) (u : ℝ)
    (hu : u < secondElevenMass Construction.persistentRootScore m) :
    Counting.ShellMass (goodTarget 1 c) u :=
  secondEleven_shellMass 1 Construction.persistentRootScore
    Construction.persistentRootScore_domain.1 Sources.canonicalSources c hc m hm hpaid u hu

/-- A single paid level and positive mass work for every fixed clock above the threshold. -/
theorem exists_canonicalSecondShell :
    ∃ m : ℕ, 2 ≤ m ∧
      kappa * Analytic.mixingError m < Construction.persistentRootScore / 2 ∧
      0 < secondElevenMass Construction.persistentRootScore m ∧
      ∀ c : ℝ, criticalClock < c → ∀ u : ℝ,
        u < secondElevenMass Construction.persistentRootScore m →
        Counting.ShellMass (goodTarget 1 c) u := by
  obtain ⟨m, hm, hpaid⟩ := exists_coarseLevel Construction.persistentRootScore_domain.1
  exact ⟨m, hm, hpaid, secondElevenMass_pos Construction.persistentRootScore_domain.1 m,
    fun c hc u hu => canonicalSecondShell m hm hpaid c hc u hu⟩

end WordCertDensity.Density
