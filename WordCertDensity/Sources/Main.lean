/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Sources.Target
import WordCertDensity.Construction.SeedScore

/-! # Canonical every-clock sources with the actual persistent allocation score

Every input to the generic pool theorem is discharged by the canonical
residue-complete root pool and its actual persistent marks. The score is fixed
before the clock and cutoff; no source-family hypothesis remains.
-/

namespace WordCertDensity.Sources
open Construction

/-- The canonical roots above one form a nonrecurrent pool. -/
theorem seedRootPool_nonrecurrent {b : ℕ} (hb : 1 ≤ b) (q : ℕ) :
    NonrecurrentPool acceleratedStep (seedRootPool b q : Set ℕ) := by
  apply nonrecurrentPool_oneStepRoots.mono
  intro x hx
  obtain ⟨_,i,rfl⟩ := mem_seedRootPool.mp hx
  exact Roots.oneStepRoot (by omega)

/-- The actual canonical allocation score gives every-clock sources at every sufficiently large cutoff. -/
theorem canonicalSources : AllScaleSources 1 persistentRootScore := by
  let b := survivalSeedSize
  have hb : 32^5 ≤ b := by rfl
  have hb1 : 1 ≤ b := by norm_num [b,survivalSeedSize]
  let N := seedStartupIndex b hb
  let q := seedConductor b N
  let pool := seedRootPool b q
  let z := persistentSeedMark b hb
  have hheight : ∀ root ∈ pool, 16^b ≤ root :=
    fun root hr => (seedRootPool_height hb1 hr).2.le
  have hpath : ∀ root ∈ pool, ∃ T, ReachesIn root 1 T := by
    intro root hr
    obtain ⟨i,_,hi⟩ := seedRootPool_reaches_one hb1 hr
    exact ⟨_,hi⟩
  have hmark : ∀ j ≥ N, ∀ root ∈ pool, z root ≤ physicalSeedMark b j root := by
    intro j hj root hr
    exact persistentSeedMark_le_later hb (hheight root hr) (seedRootPool_height hb1 hr).1 hj
  have hscore : persistentRootScore ≤ ∑ root ∈ pool, z root/root := persistentRootScore_le_marks
  exact targetPoolSources hb persistentRootScore_pos (seedRootPool_nonrecurrent hb1 q)
    hheight hpath hmark hscore

end WordCertDensity.Sources
