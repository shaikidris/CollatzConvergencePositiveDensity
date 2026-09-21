/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Sources.FixedGraft
import WordCertDensity.Construction.SourceParameters

/-! # Generic every-clock sources from a fixed persistent target pool

Pool, target paths and score are supplied before the clock. The construction
then chooses one parameter, macro scale and paid splice before every cutoff.
No hypothesis that the target reaches one is used.
-/

namespace WordCertDensity.Sources
open Filter Construction
open scoped Topology

/-- Every fixed positive persistent nonrecurrent pool supplies the complete every-clock source theorem. -/
theorem targetPoolSources {b N target : ℕ} {pool : Finset ℕ} {z : ℕ → ℝ} {W : ℝ}
    (hb : 32^5 ≤ b) (hW : 0 < W)
    (hP : NonrecurrentPool acceleratedStep (pool : Set ℕ))
    (hheight : ∀ root ∈ pool, 16^b ≤ root)
    (hpath : ∀ root ∈ pool, ∃ T, ReachesIn root target T)
    (hmark : ∀ j ≥ N, ∀ root ∈ pool, z root ≤ physicalSeedMark b j root)
    (hscore : W ≤ ∑ root ∈ pool, z root/root) : AllScaleSources target W := by
  classical
  have hne : pool.Nonempty := by
    by_contra h
    have he : pool = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.sum_empty] at hscore
    linarith
  have hpaths : ∀ root : ℕ, ∃ T : ℕ, root ∈ pool → ReachesIn root target T := by
    intro root
    by_cases hr : root ∈ pool
    · obtain ⟨T,hT⟩ := hpath root hr
      exact ⟨T,fun _ => hT⟩
    · exact ⟨0,fun h => (hr h).elim⟩
  choose clock hclock using hpaths
  intro c hc ε hε Λ hΛ
  obtain ⟨θ,hθ,hcap,hclockMargin⟩ := exists_sourceParameter hc
  obtain ⟨L,hL,hpay⟩ := exists_sourceMacroScale hθ
  have hLreal : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  obtain ⟨t,_ht,hpaid,hfinite⟩ := exists_sourceSplice hθ hcap hLreal hpay hb pool z hε
    hheight hmark hscore
  exact fixedGraftSources hθ hcap hLreal hclockMargin hb hpaid hε hΛ
    pool hne clock hP hheight hclock hfinite

end WordCertDensity.Sources
