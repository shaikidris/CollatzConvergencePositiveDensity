/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ParametricPool
import WordCertDensity.Construction.ClockMargin

/-! # Common clock parameter, macro scale and paid splice for a fixed pool -/

namespace WordCertDensity.Construction
open Filter
open scoped Topology

/-- A positive parameter can be chosen strictly inside every larger ordinary clock. -/
theorem exists_sourceParameter {c : ℝ} (hc : criticalClock < c) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1/1000 ∧ criticalClock+3*θ ≤ c := by
  let θ : ℝ := min (1/1000) ((c-criticalClock)/6)
  have hp : 0 < θ := lt_min (by norm_num) (by linarith)
  have hh : θ ≤ (c-criticalClock)/6 := min_le_right _ _
  exact ⟨θ,hp,min_le_left _ _,by linarith⟩

/-- One integer macro scale pays the concentration requirement at the selected parameter. -/
theorem exists_sourceMacroScale {θ : ℝ} (hθ : 0 < θ) :
    ∃ L : ℕ, 0 < L ∧ 10 ≤ stoppedCorridorRate (θ/20)*(L : ℝ) := by
  have hp := stoppedCorridorRate_pos (by positivity : 0 < θ/20)
  let L : ℕ := ⌈10/stoppedCorridorRate (θ/20)⌉₊+1
  have hL : 0 < L := by dsimp [L]; omega
  have hr : 10/stoppedCorridorRate (θ/20) ≤ (L : ℝ) := by
    dsimp [L]
    push_cast
    linarith [Nat.le_ceil (10/stoppedCorridorRate (θ/20))]
  refine ⟨L,hL,?_⟩
  have h := (div_le_iff₀ hp).mp hr
  nlinarith

/-- One late splice simultaneously retains the pooled score and pays the physical offset. -/
theorem exists_sourceSplice {θ L W η : ℝ} {b N : ℕ}
    (hθ : 0 < θ) (hcap : θ ≤ 1/1000) (hL : 0 < L)
    (hpay : 10 ≤ stoppedCorridorRate (θ/20)*L) (hb : 32^5 ≤ b)
    (pool : Finset ℕ) (z : ℕ → ℝ) (hη : 0 < η)
    (hroot : ∀ root ∈ pool, 16^b ≤ root)
    (hmark : ∀ j ≥ N, ∀ root ∈ pool, z root ≤ physicalSeedMark b j root)
    (hscore : W ≤ ∑ root ∈ pool, z root/root) :
    ∃ t ≥ N, graftOffsetAbsorption b t ≤ 1 ∧
      ∀ j, W-η/2 ≤ ∑ root ∈ pool, physicalParametricGraftMark θ L (θ/20) b t j root/root := by
  have hp := eventually_physicalParametricGraftMark_pool hθ hcap hb hL
    (by positivity : 0 < θ/20) (by linarith : 2*(θ/20) ≤ 1) hpay pool z hroot hmark hscore
    (by linarith : 0 < η/2)
  obtain ⟨t,ht,hoff⟩ := (hp.and (graftOffsetAbsorption_eventually (by omega : 100 ≤ b))).exists
  exact ⟨t,ht.1,hoff,ht.2⟩

end WordCertDensity.Construction
