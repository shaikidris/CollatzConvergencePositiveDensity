/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Sources.Objects
import WordCertDensity.Construction.CommonPrecision
import WordCertDensity.Construction.PoolSourceGeometry
import WordCertDensity.Construction.PooledTerminalScore

/-! # All-real-cutoff source witnesses from one fixed graft

The witness functions are the literal reduced source set, pooled charge,
marker level and finite shell radius at the selected common stage.
-/

namespace WordCertDensity.Sources
open Filter Construction
open scoped Topology

/-- One fixed graft produces the full physical family and all three limits at every late cutoff. -/
theorem fixedGraftSources {θ L c W ε Λ : ℝ} {b t target : ℕ}
    (hθ : 0 < θ) (hcap : θ ≤ 1/1000) (hL : 0 < L)
    (hc : criticalClock+3*θ ≤ c) (hb : 32^5 ≤ b)
    (hpaid : graftOffsetAbsorption b t ≤ 1) (hε : 0 < ε) (hΛ : 16 < Λ)
    (pool : Finset ℕ) (hne : pool.Nonempty) (clock : ℕ → ℕ)
    (hP : NonrecurrentPool acceleratedStep (pool : Set ℕ))
    (hheight : ∀ root ∈ pool, 16^b ≤ root)
    (hpath : ∀ root ∈ pool, ReachesIn root target (clock root))
    (hscore : ∀ j, W-ε/2 ≤ ∑ root ∈ pool,
      physicalParametricGraftMark θ L (θ/20) b t j root/root) :
    ∃ (S : ℝ → Finset ℕ) (a : ℝ → ℕ → ℝ) (k : ℝ → ℕ) (R : ℝ → ℝ),
      Tendsto R atTop (𝓝 16) ∧ Tendsto k atTop atTop ∧
      Tendsto (fun X => (3 : ℝ)^k X/X) atTop (𝓝 0) ∧
      ∀ᶠ X in atTop, SourceAt target c X (R X) (S X) (a X) ∧ R X < Λ ∧
        W-ε ≤ ∑ x ∈ S X, a X x*Reference.fan (k X) (x : ZMod (3^k X)) := by
  obtain ⟨stage,hstage,hcover⟩ := commonIntervalCoverage θ L (stoppedExpectation displacement)
    (terminalPoolLower b pool hne) (terminalPoolUpper b t pool) (graftInitialCount b t)
    hθ hcap hL stoppedExpectation_displacement_lower
  let B : ℝ → ℕ := fun X => macroCount L (graftInitialCount b t) (stage X)
  have hB : Tendsto B atTop atTop := (macroCount_tendsto hL (graftInitialCount b t)).comp hstage
  let S : ℝ → Finset ℕ := fun X => reducedSourceSet L (θ/20) X b t (stage X) ⌊θ*B X⌋₊ pool
  let a : ℝ → ℕ → ℝ := fun X x => reducedSourceCharge L (θ/20) X b t (stage X) ⌊θ*B X⌋₊ x pool
  let k : ℝ → ℕ := fun X => parametricLevel θ (B X)
  let R : ℝ → ℝ := fun X => terminalShellRadius ⌊θ*B X⌋₊
  have hscales := terminalSelected_scales hB hθ
  have hlo : ∀ᶠ X : ℝ in atTop,
      (2 : ℝ)^commonLowExponent θ (stoppedExpectation displacement)
        (terminalPoolUpper b t pool) (B X) < X := hcover.mono fun _ h => h.1
  have hprecision := commonCutoff_precision hB hθ hcap stoppedExpectation_displacement_lower hlo
  refine ⟨S,a,k,R,hscales.1,hscales.2,hprecision,?_⟩
  have hgeometry := finitePool_reducedSources_eventually hθ hcap hL hc hb hpaid
    pool hne clock hP hheight hpath
  have hmass := finitePool_commonFan_eventually hb hL hθ hcap hpaid hε
    pool hne clock hheight hpath hscore
  have hr : ∀ᶠ X in atTop, R X < Λ := hscales.1.eventually_lt_const hΛ
  filter_upwards [hstage.eventually hgeometry,hstage.eventually hmass,hcover,hr] with X hg hm hi hR
  have hAt : SourceAt target c X (R X) (S X) (a X) := hg X hi.1 hi.2
  exact ⟨hAt,hR,hm X hi.1 hi.2⟩

end WordCertDensity.Sources
