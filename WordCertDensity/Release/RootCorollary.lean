/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Release.TargetDensity
import WordCertDensity.Sources.Main

/-! # One positive persistent root

The canonical finite pool has positive total persistent mass. A positive
coordinate supplies a singleton nonrecurrent pool and its own fixed score.
-/

namespace WordCertDensity.Release

open Construction
open scoped BigOperators

/-- Some canonical root has a strictly positive persistent mark. -/
theorem exists_positive_persistent_root :
    ∃ r ∈ seedRootPool survivalSeedSize
      (seedConductor survivalSeedSize (seedStartupIndex survivalSeedSize (by rfl))),
      0 < persistentSeedMark survivalSeedSize (by rfl) r := by
  classical
  let b := survivalSeedSize
  have hb : 32 ^ 5 ≤ b := by rfl
  let q := seedConductor b (seedStartupIndex b hb)
  have hmass := seedRootPool_persistent_mass
  have hres : 0 < seedStartupResidual b hb := (seedStartup_spec b hb).2.2
  have hsum : 0 < ∑ r ∈ seedRootPool b q, persistentSeedMark b hb r := by
    exact lt_trans (by positivity : (0 : ℝ) <
      (2 * (3 : ℝ) ^ (q - 1)) * seedStartupResidual b hb) hmass
  by_contra h
  push Not at h
  have hnonpos : (∑ r ∈ seedRootPool b q,
      persistentSeedMark b hb r) ≤ 0 := by
    apply Finset.sum_nonpos
    intro r hr
    exact h r hr
  exact (not_lt_of_ge hnonpos) hsum

/-- A selected root admits actual singleton sources at every scale. -/
theorem singleton_root_sources {r : ℕ}
    (hr : r ∈ seedRootPool survivalSeedSize
      (seedConductor survivalSeedSize (seedStartupIndex survivalSeedSize (by rfl))))
    {W : ℝ} (hW : 0 < W)
    (hscore : W ≤ persistentSeedMark survivalSeedSize (by rfl) r / r) :
    Sources.AllScaleSources r W := by
  let b := survivalSeedSize
  have hb : 32 ^ 5 ≤ b := by rfl
  have hb1 : 1 ≤ b := by norm_num [b, survivalSeedSize]
  have hpool := Sources.seedRootPool_nonrecurrent hb1
    (seedConductor b (seedStartupIndex b hb))
  have hsingleton : NonrecurrentPool acceleratedStep ({r} : Set ℕ) :=
    hpool.mono (by
      intro x hx
      have heq : x = r := hx
      subst x
      exact hr)
  apply Sources.targetPoolSources (b := b) (N := seedStartupIndex b hb)
    (pool := {r}) (z := persistentSeedMark b hb) hb hW
    (by simpa only [Finset.coe_singleton] using hsingleton)
  · intro root hroot
    have heq : root = r := Finset.mem_singleton.mp hroot
    subst root
    exact (seedRootPool_height hb1 hr).2.le
  · intro root hroot
    have heq : root = r := Finset.mem_singleton.mp hroot
    subst root
    exact ⟨0, rfl⟩
  · intro j hj root hroot
    have heq : root = r := Finset.mem_singleton.mp hroot
    subst root
    have hh := seedRootPool_height hb1 hr
    exact persistentSeedMark_le_later hb hh.2.le hh.1 hj
  · simpa using hscore

/-- One actual canonical root has a positive singleton score and a fixed
positive lower-density constant at every admitted clock. -/
theorem positive_individual_root :
    ∃ r ∈ seedRootPool survivalSeedSize
      (seedConductor survivalSeedSize (seedStartupIndex survivalSeedSize (by rfl))),
      ∃ W : ℝ, Density.SmallScore W ∧
        W ≤ persistentSeedMark survivalSeedSize (by rfl) r / r ∧
        ∃ d : ℝ, Density.TargetBound r d := by
  obtain ⟨r, hr, hz⟩ := exists_positive_persistent_root
  have hb : 1 ≤ survivalSeedSize := by norm_num [survivalSeedSize]
  have hrpos : 0 < r := by
    have hh := seedRootPool_height hb hr
    exact lt_of_le_of_lt (Nat.zero_le _) hh.2
  have hquot : 0 < persistentSeedMark survivalSeedSize (by rfl) r / (r : ℝ) := by
    positivity
  let W : ℝ := min (persistentSeedMark survivalSeedSize (by rfl) r / r)
    (27 / 2 ^ 27)
  have hW : Density.SmallScore W := by
    exact ⟨lt_min hquot (by positivity), min_le_right _ _⟩
  have hscore : W ≤ persistentSeedMark survivalSeedSize (by rfl) r / r :=
    min_le_left _ _
  have hsrc := singleton_root_sources hr hW.1 hscore
  obtain ⟨m, hm, hpaid⟩ := Density.exists_coarseLevel hW.1
  exact ⟨r, hr, W, hW, hscore, _,
    Density.elementaryDensity r W hW hsrc m hm hpaid⟩

end WordCertDensity.Release
