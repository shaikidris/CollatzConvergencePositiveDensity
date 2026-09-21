/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.Profile
import WordCertDensity.Counting.ProfilePhysical
import WordCertDensity.Density.CapacityDomain
import WordCertDensity.Counting.MomentCapacity
import WordCertDensity.Release.FractionalDensity
import WordCertDensity.Release.SecondDensity

/-! # Fixed-level profile density from actual sources

Choose a positive hinge threshold first, then a fixed positive graft tolerance,
then the physical cutoff. The exact profile endpoint follows by continuity of
the radial conversion, without realizing an optimal allocation by trajectories.
-/

namespace WordCertDensity.Density

open Filter
open scoped Topology

private theorem profile_strict_threshold (m : ℕ) (p u : ℝ) (hp : 0 ≤ p)
    (hpaid : p ≤ (2 * Real.log 2) * (8 / 9)) (hu : 0 ≤ u)
    (hlt : u < Counting.profile m p) :
    ∃ t : ℝ, 0 < t ∧ u * t < p - (2 * Real.log 2) *
      Reference.mean m (fun r => max (Reference.fan m r - t) 0) := by
  rw [(Counting.profile_hinge m p hp hpaid).2.1] at hlt
  have hne : Set.Nonempty {a : ℝ | ∃ t : ℝ, 0 < t ∧
      a = max (p - (2 * Real.log 2) * Reference.mean m
        (fun r => max (Reference.fan m r - t) 0)) 0 / t} :=
    ⟨_, 1, by norm_num, rfl⟩
  obtain ⟨_, ⟨t, ht, rfl⟩, hh⟩ := exists_lt_of_lt_csSup hne hlt
  have hh' := (lt_div_iff₀ ht).mp hh
  have hn : 0 < p - (2 * Real.log 2) *
      Reference.mean m (fun r => max (Reference.fan m r - t) 0) := by
    by_contra! hn
    rw [max_eq_right hn] at hh'
    exact (not_lt_of_ge (mul_nonneg hu ht.le)) hh'
  exact ⟨t, ht, by simpa only [max_eq_left hn.le] using hh'⟩

/-- Each strict profile sub-bound is supplied at all sufficiently large cutoffs. -/
theorem profile_sources (target : ℕ) (W : ℝ) (hW : SmallScore W)
    (hsrc : Sources.AllScaleSources target W) (c : ℝ) (hc : criticalClock < c)
    (m : ℕ) (hm : 2 ≤ m) (u : ℝ) (hu : 0 ≤ u)
    (hlt : u < Counting.profile m (residual W m)) (Λ : ℝ) (hΛ : 16 < Λ) :
    ∃ (A : ℝ → Finset ℕ) (a : ℝ → ℕ → ℝ) (R : ℝ → ℝ),
      Tendsto R atTop (𝓝 16) ∧ ∀ᶠ X in atTop,
        Sources.SourceAt target c X (R X) (A X) (a X) ∧ R X < Λ ∧
        u < ∑ x ∈ A X, a X x := by
  have hp := residual_domain hW.1.le hm
  have hpaid : residual W m ≤ (2 * Real.log 2) * (8 / 9) := by
    simpa only [mul_comm] using hp.2.trans (smallScore_paid hW)
  obtain ⟨t, ht, hgap⟩ := profile_strict_threshold m (residual W m) u hp.1 hpaid hu hlt
  let H := Reference.mean m (fun r => max (Reference.fan m r - t) 0)
  have hH : 0 ≤ H := Reference.mean_nonneg m _ (fun _ => le_max_right _ _)
  have hL : 0 < 2 * Real.log 2 := by positivity
  have hp0 : 0 < residual W m := by
    have := mul_nonneg hL.le hH
    have := mul_nonneg hu ht.le
    dsimp [H] at *
    linarith
  have hraw : residual W m = W - kappa * Analytic.mixingError m := by
    unfold residual at hp0 ⊢
    rcases lt_max_iff.mp hp0 with h | h
    · exact max_eq_left h.le
    · exact (lt_irrefl _ h).elim
  let η := (residual W m - (2 * Real.log 2) * H - u * t) / 2
  have hη : 0 < η := by dsimp [η, H]; linarith
  have hmargin : u < (W - kappa * Analytic.mixingError m - η -
      (2 * Real.log 2) * H) / t := by
    apply (lt_div_iff₀ ht).2
    rw [← hraw]
    dsimp [η, H]
    linarith
  obtain ⟨A, a, R, hR, hfin⟩ :=
    Counting.exists_coarse_sources target W hsrc c hc m hm η hη Λ hΛ
  let T : ℝ → ℝ := fun X => (3 : ℝ) ^ m / X + Real.log (R X) / 2
  have hT : Tendsto T atTop (𝓝 (2 * Real.log 2)) :=
    Counting.fixed_harmonic_coefficient_tendsto m hR
  have hlim : Tendsto (fun X => (W - kappa * Analytic.mixingError m - η - T X * H) / t)
      atTop (𝓝 ((W - kappa * Analytic.mixingError m - η - (2 * Real.log 2) * H) / t)) :=
    (tendsto_const_nhds.sub (hT.mul_const H)).div_const t
  have hlarge := hlim.eventually_const_lt hmargin
  have hrad := hR.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) < 16))
  have he : (16 * Real.log 2 / 9) * Analytic.mixingError m =
      kappa * Analytic.mixingError m := by unfold kappa; ring
  refine ⟨A, a, R, hR, ?_⟩
  filter_upwards [hfin, hlarge, hrad, eventually_gt_atTop (0 : ℝ)] with X hX hlargeX hradX hpos
  refine ⟨hX.1, hX.2.1, ?_⟩
  have hdata : ∀ x ∈ A X, Odd x ∧ X ≤ (x : ℝ) ∧ (x : ℝ) < R X * X ∧
      0 ≤ a X x ∧ a X x ≤ (x : ℝ)⁻¹ := by
    intro x hx
    obtain ⟨ho, _, hl, hh, hn, hw⟩ := hX.1 x hx
    exact ⟨ho, hl, hh, hn, hw⟩
  have hmark : W - kappa * Analytic.mixingError m - η ≤
      ∑ x ∈ A X, a X x * Reference.fan m (x : ZMod (3 ^ m)) := by
    simpa only [he] using hX.2.2
  have hb := Counting.physical_hinge_mass (3 ^ m) X (R X) (A X) (a X)
    (Reference.fan m) (W - kappa * Analytic.mixingError m - η) t
    ((by decide : Odd (3 : ℕ)).pow) hpos hradX hdata ht hmark
  have hb' : max (W - kappa * Analytic.mixingError m - η - T X * H) 0 / t ≤
      ∑ x ∈ A X, a X x := by
    simpa only [T, H, Reference.mean, Nat.cast_pow, Nat.cast_ofNat] using hb
  exact (hlargeX.trans_le (div_le_div_of_nonneg_right (le_max_left _ _) ht.le)).trans_le hb'

/-- The full profile value gives the fixed-level radial density bound. -/
theorem profile_density_target (target : ℕ) (W : ℝ) (hW : SmallScore W)
    (hsrc : Sources.AllScaleSources target W) (m : ℕ) (hm : 2 ≤ m)
    (c : ℝ) (hc : criticalClock < c) :
    Counting.radial (Counting.profile m (residual W m)) ≤
      lowerNaturalDensity (goodTarget target c) := by
  have hp := residual_domain hW.1.le hm
  have hpaid : residual W m ≤ (2 * Real.log 2) * (8 / 9) := by
    simpa only [mul_comm] using hp.2.trans (smallScore_paid hW)
  have hd := (Counting.profile_hinge m (residual W m) hp.1 hpaid).2.2
  have hdom : Counting.profile m (residual W m) ≤ Real.log (3 / 2) / 2 :=
    (hd.2.trans (div_le_div_of_nonneg_right hp.2 (by norm_num))).trans
      (smallScore_capacity_domain hW).1.le
  by_cases hz : Counting.profile m (residual W m) = 0
  · simpa only [hz, Counting.radial, mul_zero, Real.exp_zero, sub_self] using
      lowerNaturalDensity_nonneg (goodTarget target c)
  have hpos := lt_of_le_of_ne hd.1 (Ne.symm hz)
  have hcont : Continuous Counting.radial := by unfold Counting.radial; fun_prop
  apply le_of_tendsto (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
    Tendsto Counting.radial (𝓝[<] (Counting.profile m (residual W m)))
      (𝓝 (Counting.radial (Counting.profile m (residual W m)))))
  filter_upwards [mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hpos), self_mem_nhdsWithin]
    with u hu hlt
  apply Counting.radialConversion (goodTarget target c) u
    (goodTarget_dyadicallyClosed hc) hu.le (hlt.le.trans hdom)
  intro Λ hΛ
  obtain ⟨A, a, R, _, hfin⟩ := profile_sources target W hW hsrc c hc m hm u hu.le hlt Λ hΛ
  filter_upwards [hfin, eventually_gt_atTop (0 : ℝ)] with X hX hXpos
  refine ⟨A X, a X, ?_, hX.2.2.le⟩
  intro x hx
  obtain ⟨ho, hG, hl, hh, hn, hw⟩ := hX.1 x hx
  exact ⟨ho, hG, hl, hh.trans (mul_lt_mul_of_pos_right hX.2.1 hXpos), hn, hw⟩

/-- Every admissible real moment bounds the exact allocation profile from below. -/
theorem profile_moment_bound (m : ℕ) (p s B : ℝ) (_hm : 2 ≤ m)
    (hp : 0 ≤ p) (hpaid : p ≤ (2 * Real.log 2) * (8 / 9))
    (hs : 1 < s) (hB : 0 < B)
    (hmoment : Reference.mean m (fun r => Reference.fan m r ^ s) ≤ B) :
    p ^ (s / (s - 1)) / ((2 * Real.log 2 * B) ^ (1 / (s - 1))) ≤
      Counting.profile m p := by
  obtain ⟨w, hw, heq⟩ := (Counting.profile_hinge m p hp hpaid).1
  let e : Fin (3 ^ m) ≃ ZMod (3 ^ m) := ZMod.finEquiv (3 ^ m)
  have hL : 0 < 2 * Real.log 2 := by positivity
  have hLB := mul_pos hL hB
  have hU : 0 ≤ Counting.profile m p :=
    heq ▸ Finset.sum_nonneg (fun r _ => (hw.1 r).1)
  have hcap := Counting.finite_moment_capacity (3 ^ m)
    (fun i => Reference.fan m (e i)) (fun i => w (e i)) (2 * Real.log 2) s B
    hL.le hs.le (fun i => Reference.fan_nonneg m (e i))
    (fun i => (hw.1 (e i)).1)
    (fun i => by simpa only [Nat.cast_pow, Nat.cast_ofNat] using (hw.1 (e i)).2)
    (by
      rw [e.sum_comp (fun r => Reference.fan m r ^ s)]
      simpa only [Reference.mean, Nat.cast_pow, Nat.cast_ofNat] using hmoment)
  rw [e.sum_comp (fun r => w r * Reference.fan m r), e.sum_comp w, heq] at hcap
  have hs0 : 0 < s := by linarith
  have hs1 : 0 < s - 1 := by linarith
  have hexp1 : (1 - 1 / s) * (s / (s - 1)) = 1 := by field_simp
  have hexp2 : (1 / s) * (s / (s - 1)) = 1 / (s - 1) := by field_simp
  have hpow := Real.rpow_le_rpow hp (hw.2.trans hcap) (div_pos hs0 hs1).le
  rw [Real.mul_rpow (Real.rpow_nonneg hU _) (Real.rpow_nonneg hLB.le _),
    ← Real.rpow_mul hU, ← Real.rpow_mul hLB.le, hexp1, hexp2, Real.rpow_one] at hpow
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hLB _)).2 hpow

private theorem profile_radial_mono {u v : ℝ} (h : u ≤ v) :
    Counting.radial u ≤ Counting.radial v := by
  unfold Counting.radial
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h (by norm_num))) le_rfl)
    (by norm_num)

/-- At a paid level the exact profile dominates the released second-moment density. -/
theorem profile_secondEleven_bound (W : ℝ) (hW : SmallScore W) (m : ℕ) (hm : 2 ≤ m)
    (hpaid : kappa * Analytic.mixingError m < W / 2) :
    secondElevenDensity W m ≤ Counting.radial (Counting.profile m (residual W m)) := by
  have hp := residual_domain hW.1.le hm
  have hcap : residual W m ≤ (2 * Real.log 2) * (8 / 9) := by
    simpa only [mul_comm] using hp.2.trans (smallScore_paid hW)
  have hb := profile_moment_bound m (residual W m) 2
    (Reference.fanEnergyElevenCeiling m) hm hp.1 hcap (by norm_num)
    (Reference.fanEnergyElevenCeiling_pos m)
    (by simpa only [Real.rpow_two] using Reference.fan_second_le_elevenCeiling m)
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, div_one, Real.rpow_two,
    Real.rpow_one] at hb
  have hhalf : W / 2 ≤ residual W m := by
    have := le_max_left (W - kappa * Analytic.mixingError m) 0
    change W / 2 ≤ max (W - kappa * Analytic.mixingError m) 0
    linarith
  have hmass : secondElevenMass W m ≤ Counting.profile m (residual W m) := by
    apply le_trans _ hb
    have hB := (Reference.fanEnergyElevenCeiling_pos m).le
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [pow_two] using mul_self_le_mul_self (half_pos hW.1).le hhalf
  apply profile_radial_mono
  exact ((min_le_left _ _).trans (half_le_self (secondElevenMass_pos hW.1 m).le)).trans
    hmass

/-- At a paid level the exact profile dominates the released fractional density. -/
theorem profile_fractionalEleven_bound (W : ℝ) (hW : SmallScore W) (m : ℕ) (hm : 2 ≤ m)
    (hpaid : kappa * Analytic.mixingError m < W / 2) :
    fractionalElevenDensity W m ≤ Counting.radial (Counting.profile m (residual W m)) := by
  have hp := residual_domain hW.1.le hm
  have hcap : residual W m ≤ (2 * Real.log 2) * (8 / 9) := by
    simpa only [mul_comm] using hp.2.trans (smallScore_paid hW)
  have hb := profile_moment_bound m (residual W m) (3 / 2)
    (Reference.fanFractionalElevenCeiling m) hm hp.1 hcap (by norm_num)
    (Reference.fanFractionalElevenCeiling_pos m)
    (Reference.fan_fractional_le_elevenCeiling m)
  have hmass : fractionalElevenMass W m ≤ Counting.profile m (residual W m) := by
    norm_num [fractionalElevenMass, Real.rpow_natCast, mul_pow] at hb ⊢
    exact hb
  apply profile_radial_mono
  exact ((min_le_left _ _).trans
    (half_le_self (fractionalElevenMass_pos hW.1 hpaid).le)).trans hmass

/-- Actual canonical sources give the exact profile formula before every larger clock. -/
theorem canonical_profile_density :
    ∃ W : ℝ, SmallScore W ∧ ∃ m : ℕ, 2 ≤ m ∧ 0 < residual W m ∧
      ∀ c : ℝ, criticalClock < c → Counting.radial (Counting.profile m (residual W m)) ≤
        lowerNaturalDensity (goodTarget 1 c) := by
  obtain ⟨m, hm, hpaid⟩ := exists_coarseLevel Construction.persistentRootScore_domain.1
  exact ⟨Construction.persistentRootScore, canonicalSmallScore, m, hm,
    residual_pos canonicalSmallScore.1 hpaid,
    profile_density_target 1 _ canonicalSmallScore Sources.canonicalSources m hm⟩

/-- Each positive target not divisible by three has one profile level for all larger clocks. -/
theorem admissibleTarget_profile_density {target : ℕ}
    (htarget : 0 < target) (hnotthree : ¬ 3 ∣ target) :
    ∃ W : ℝ, SmallScore W ∧ ∃ m : ℕ, 2 ≤ m ∧ 0 < residual W m ∧
      ∀ c : ℝ, criticalClock < c → Counting.radial (Counting.profile m (residual W m)) ≤
        lowerNaturalDensity (goodTarget target c) := by
  obtain ⟨W, hW, hWle, hsrc⟩ := Sources.admissibleTargetSources htarget hnotthree
  obtain ⟨m, hm, hpaid⟩ := exists_coarseLevel hW
  exact ⟨W, ⟨hW, hWle⟩, m, hm, residual_pos hW hpaid,
    profile_density_target target W ⟨hW, hWle⟩ hsrc m hm⟩

end WordCertDensity.Density
