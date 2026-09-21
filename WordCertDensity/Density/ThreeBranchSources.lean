/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.PhysicalMass
import WordCertDensity.Counting.ResidualTolerance
import WordCertDensity.Density.CapacityDomain

/-! # All-scale unmarked mass with explicit certified fan inputs -/

namespace WordCertDensity.Density

open Filter
open scoped Topology

/-- One positive graft loss gives every strict three-branch mass target at all large cutoffs. -/
theorem threeBranch_sources (target : ℕ) (W : ℝ) (hW : SmallScore W)
    (hsrc : Sources.AllScaleSources target W) (c : ℝ) (hc : criticalClock < c)
    (m : ℕ) (hm : 2 ≤ m) (V S B : ℝ) (hV : 0 < V) (hS : 0 < S) (hB : 0 < B)
    (hvar : Reference.mean m (fun r => (Reference.fan m r-(8/9 : ℝ))^2) ≤ V)
    (hmax : ∀ r, Reference.fan m r ≤ S)
    (hmoment : Reference.mean m (fun r => Reference.fan m r^(3/2 : ℝ)) ≤ B)
    (u : ℝ) (hu : 0 ≤ u)
    (hlt : u < Counting.threeBranchMass (8/9) V S B (2*Real.log 2) (residual W m))
    (Λ : ℝ) (hΛ : 16 < Λ) :
    ∃ (A : ℝ → Finset ℕ) (a : ℝ → ℕ → ℝ) (R : ℝ → ℝ),
      Tendsto R atTop (𝓝 16) ∧ ∀ᶠ X in atTop,
        Sources.SourceAt target c X (R X) (A X) (a X) ∧ R X < Λ ∧
        u < ∑ x ∈ A X, a X x := by
  let E := (16*Real.log 2/9)*Analytic.mixingError m
  have heq : kappa*Analytic.mixingError m = E := by dsimp [kappa, E]; ring
  have he : 0 ≤ E := by
    have hmix := (Analytic.mixingError_pos (show 1 ≤ m by omega)).le
    dsimp [E]
    positivity
  have htarget : u < Counting.threeBranchMass (8/9) V S B (2*Real.log 2) (max (W-E) 0) := by
    simpa only [residual, heq] using hlt
  obtain ⟨η, hη, hp, hmass⟩ := Counting.threeBranchMass_raw_tolerance
    (by norm_num : (0 : ℝ) < 8/9) hV hB (by positivity) hu htarget
  obtain ⟨A, a, R, hR, hsource⟩ := Counting.exists_coarse_sources target W hsrc c hc m hm η hη Λ hΛ
  let t : ℝ → ℝ := fun X => (3 : ℝ)^m/X + Real.log (R X)/2
  have ht : Tendsto t atTop (𝓝 (2*Real.log 2)) := Counting.fixed_harmonic_coefficient_tendsto m hR
  have hlarge := Counting.threeBranchMass_eventually_gt (by norm_num : (0 : ℝ) < 8/9)
    hV hB (by positivity) hp.le hmass ht tendsto_const_nhds
  have hpaid : W-E-η < (8/9 : ℝ)*(2*Real.log 2) := by
    have hw := smallScore_paid hW
    linarith
  have hcap := (ht.const_mul (8/9 : ℝ)).eventually_const_lt hpaid
  have hrad := hR.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) < 16))
  refine ⟨A, a, R, hR, ?_⟩
  filter_upwards [hsource, hlarge, hcap, hrad, eventually_gt_atTop (0 : ℝ)] with X hX hlargeX hcapX hradX hpos
  refine ⟨hX.1, hX.2.1, ?_⟩
  have hdata : ∀ x ∈ A X, Odd x ∧ X ≤ (x : ℝ) ∧ (x : ℝ) < R X*X ∧
      0 ≤ a X x ∧ a X x ≤ (x : ℝ)⁻¹ := by
    intro x hx
    obtain ⟨ho, _, hl, hu', hn, hw⟩ := hX.1 x hx
    exact ⟨ho, hl, hu', hn, hw⟩
  have hbound := Counting.physical_threeBranch_mass (3^m) X (R X) (A X) (a X)
    (Reference.fan m) (8/9) V S B (W-E-η) ((by decide : Odd (3 : ℕ)).pow)
    hpos hradX hdata (by norm_num) hV hS hB hp.le
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcapX.le)
    (Reference.fan_nonneg m)
    (by simpa only [Reference.mean, Nat.cast_pow, Nat.cast_ofNat] using Reference.mean_fan m)
    (by simpa only [Reference.mean, Nat.cast_pow, Nat.cast_ofNat] using hvar)
    hmax (by simpa only [Reference.mean, Nat.cast_pow, Nat.cast_ofNat] using hmoment) hX.2.2
  apply hlargeX.trans_le
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hbound

end WordCertDensity.Density
