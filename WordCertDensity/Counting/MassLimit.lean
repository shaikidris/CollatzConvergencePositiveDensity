/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.FiniteMass

/-! # Strict finite-capacity limits for the common mass recipe -/

namespace WordCertDensity.Counting

open Filter
open scoped Topology

/-- All three inverse branches with the finite capacity and marked residual explicit. -/
noncomputable def threeBranchMass (μ V S B T p : ℝ) : ℝ :=
  max (max (capacitySmallRoot (μ^2+V) (2*μ*p+V*T) (p^2)) (p/S))
    (p^3/(T^2*B^2))

/-- The mass recipe is continuous at every positive-capacity nonnegative-residual point. -/
theorem threeBranchMass_continuousAt {μ V S B T p : ℝ}
    (hμ : 0 < μ) (hV : 0 < V) (hB : 0 < B) (hT : 0 < T) (hp : 0 ≤ p) :
    ContinuousAt (fun z : ℝ × ℝ => threeBranchMass μ V S B z.1 z.2) (T,p) := by
  have hd : 2*μ*p+V*T + Real.sqrt ((2*μ*p+V*T)^2-4*(μ^2+V)*p^2) ≠ 0 := by
    have hh := Real.sqrt_nonneg ((2*μ*p+V*T)^2-4*(μ^2+V)*p^2)
    have ht : 0 < V*T := mul_pos hV hT
    have hpp : 0 ≤ 2*μ*p := by positivity
    linarith
  have hf : T^2*B^2 ≠ 0 := by positivity
  unfold threeBranchMass capacitySmallRoot
  fun_prop (disch := first | exact hd | exact hf)

/-- Any strict target below the limiting recipe eventually lies below the finite recipe. -/
theorem threeBranchMass_eventually_gt {α : Type*} {l : Filter α}
    {μ V S B T p u : ℝ} (hμ : 0 < μ) (hV : 0 < V) (hB : 0 < B)
    (hT : 0 < T) (hp : 0 ≤ p) (hu : u < threeBranchMass μ V S B T p)
    {t a : α → ℝ} (ht : Tendsto t l (𝓝 T)) (ha : Tendsto a l (𝓝 p)) :
    ∀ᶠ x in l, u < threeBranchMass μ V S B (t x) (a x) := by
  have hc := (threeBranchMass_continuousAt (S := S) hμ hV hB hT hp).tendsto
  have hlim := hc.comp (ht.prodMk_nhds ha)
  exact hlim.eventually_const_lt hu

end WordCertDensity.Counting
