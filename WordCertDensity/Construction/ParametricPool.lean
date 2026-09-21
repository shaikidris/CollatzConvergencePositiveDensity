/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ParametricLimit

/-! # One parameterized graft for the same fixed persistent pool

The pool and its score precede theta, the error tolerance and the splice.
The same splice retains that score at every stage and in the limiting marks.
No new root pool is selected as the parameter or counting scale changes.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- Every sufficiently late splice preserves the fixed pool score up to any
given positive loss, simultaneously for all continuation stages. -/
theorem eventually_physicalParametricGraftMark_pool {θ L δ W : ℝ} {b N : ℕ}
    (hθ : 0 < θ) (hθcap : θ ≤ 1 / 1000) (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2
      * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) (pool : Finset ℕ) (z : ℕ → ℝ)
    (hroot : ∀ r ∈ pool, 16 ^ b ≤ r)
    (hmark : ∀ j ≥ N, ∀ r ∈ pool, z r ≤ physicalSeedMark b j r)
    (hscore : W ≤ ∑ r ∈ pool, z r / r) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in atTop, N ≤ t ∧ ∀ j,
      W - η ≤ ∑ r ∈ pool, physicalParametricGraftMark θ L δ b t j r / r := by
  let C : ℝ := ∑ r ∈ pool, (r : ℝ)⁻¹
  have hlimit : Tendsto (fun t => parametricTotalError θ L δ b t * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (parametricTotalError_tendsto L hθ hδ (by omega : 256 ^ 2 ≤ b)).mul_const C
  filter_upwards [eventually_physicalParametricGraftMark_error hθ hθcap hb hL hδ hsmall hpay,
    hlimit.eventually_lt_const hη, eventually_ge_atTop N] with t herr hbudget ht
  refine ⟨ht, fun j => ?_⟩
  have hsum : (∑ r ∈ pool, z r / r) ≤
      (∑ r ∈ pool, physicalParametricGraftMark θ L δ b t j r / r) + parametricTotalError θ L δ b
        t * C := by
    calc
      _ ≤ ∑ r ∈ pool, (physicalParametricGraftMark θ L δ b t j r + parametricTotalError θ L δ b
        t) / r := by
        apply Finset.sum_le_sum
        intro r hr
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg r)
        have he := (abs_sub_le_iff.mp (herr r (hroot r hr) j)).2
        linarith [hmark t ht r hr]
      _ = _ := by
        simp only [div_eq_mul_inv, add_mul, Finset.sum_add_distrib, C, Finset.mul_sum]
  linarith

/-- Choose one splice for the entire fixed pool and all future stages. -/
theorem exists_physicalParametricGraftMark_pool {θ L δ W : ℝ} {b N : ℕ}
    (hθ : 0 < θ) (hθcap : θ ≤ 1 / 1000) (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2
      * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) (pool : Finset ℕ) (z : ℕ → ℝ)
    (hroot : ∀ r ∈ pool, 16 ^ b ≤ r)
    (hmark : ∀ j ≥ N, ∀ r ∈ pool, z r ≤ physicalSeedMark b j r)
    (hscore : W ≤ ∑ r ∈ pool, z r / r) {η : ℝ} (hη : 0 < η) :
    ∃ t ≥ N, ∀ j, W - η ≤ ∑ r ∈ pool, physicalParametricGraftMark θ L δ b t j r / r := by
  obtain ⟨t, ht, hsum⟩ :=
    (eventually_physicalParametricGraftMark_pool hθ hθcap hb hL hδ hsmall hpay pool z hroot
      hmark hscore hη).exists
  exact ⟨t, ht, hsum⟩

/-- At a common splice, both every finite pooled mark and the sum of the
nonnegative limiting root marks retain the same fixed score. -/
theorem exists_physicalParametricGraftMark_pool_limit {θ L δ W : ℝ} {b N : ℕ}
    (hθ : 0 < θ) (hθcap : θ ≤ 1 / 1000) (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2
      * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) (pool : Finset ℕ) (z : ℕ → ℝ)
    (hroot : ∀ r ∈ pool, 16 ^ b ≤ r)
    (hmark : ∀ j ≥ N, ∀ r ∈ pool, z r ≤ physicalSeedMark b j r)
    (hscore : W ≤ ∑ r ∈ pool, z r / r) {η : ℝ} (hη : 0 < η) :
    ∃ t ≥ N, ∃ v : ℕ → ℝ,
      (∀ r ∈ pool, 0 ≤ v r ∧
        Tendsto (fun j => physicalParametricGraftMark θ L δ b t j r) atTop (𝓝 (v r))) ∧
      W - η ≤ (∑ r ∈ pool, v r / r) ∧
      ∀ j, W - η ≤ ∑ r ∈ pool, physicalParametricGraftMark θ L δ b t j r / r := by
  classical
  obtain ⟨t, hp, hl⟩ :=
    ((eventually_physicalParametricGraftMark_pool hθ hθcap hb hL hδ hsmall hpay pool z hroot
      hmark hscore hη).and
      (eventually_physicalParametricGraftMark_limit hθ hθcap hb hL hδ hsmall hpay)).exists
  have hex (r : ℕ) : ∃ v : ℝ, r ∈ pool → 0 ≤ v ∧
      Tendsto (fun j => physicalParametricGraftMark θ L δ b t j r) atTop (𝓝 v) := by
    by_cases hr : r ∈ pool
    · obtain ⟨v, hv, hlim, _⟩ := hl r (hroot r hr)
      exact ⟨v, fun _ => ⟨hv, hlim⟩⟩
    · exact ⟨0, fun h => (hr h).elim⟩
  choose v hv using hex
  refine ⟨t, hp.1, v, hv, ?_, hp.2⟩
  have hsum : Tendsto (fun j => ∑ r ∈ pool, physicalParametricGraftMark θ L δ b t j r / r)
      atTop (𝓝 (∑ r ∈ pool, v r / r)) :=
    tendsto_finsetSum pool fun r hr => (hv r hr).2.div_const (r : ℝ)
  exact ge_of_tendsto hsum (Eventually.of_forall hp.2)

/-- One fixed persistent pool admits every permitted positive parameter: the
integer macro scale and splice are chosen afterwards, before all later stages. -/
theorem exists_parameterizedGraft_for_fixed_pool {W : ℝ} {b N : ℕ}
    (hb : 32 ^ 5 ≤ b) (pool : Finset ℕ) (z : ℕ → ℝ)
    (hroot : ∀ r ∈ pool, 16 ^ b ≤ r)
    (hmark : ∀ j ≥ N, ∀ r ∈ pool, z r ≤ physicalSeedMark b j r)
    (hscore : W ≤ ∑ r ∈ pool, z r / r) :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 1000 → ∀ η : ℝ, 0 < η →
      ∃ L : ℕ, 1 ≤ L ∧ ∃ t ≥ N, ∃ v : ℕ → ℝ,
        (∀ r ∈ pool, 0 ≤ v r ∧
          Tendsto (fun j => physicalParametricGraftMark θ L (θ / 20) b t j r)
            atTop (𝓝 (v r))) ∧
        W - η ≤ (∑ r ∈ pool, v r / r) ∧
        ∀ j, W - η ≤ ∑ r ∈ pool, physicalParametricGraftMark θ L (θ / 20) b t j r / r := by
  intro θ hθ hθcap η hη
  have hδ : 0 < θ / 20 := by positivity
  have hsmall : 2 * (θ / 20) ≤ 1 := by linarith
  have hc := stoppedCorridorRate_pos hδ
  let L : ℕ := ⌈10 / stoppedCorridorRate (θ / 20)⌉₊ + 1
  have hLnat : 1 ≤ L := Nat.succ_le_succ (Nat.zero_le _)
  have hL : 0 < (L : ℝ) := Nat.cast_pos.mpr hLnat
  have hround : 10 / stoppedCorridorRate (θ / 20) ≤ (L : ℝ) := by
    dsimp [L]
    push_cast
    linarith [Nat.le_ceil (10 / stoppedCorridorRate (θ / 20))]
  have hpay : 10 ≤ stoppedCorridorRate (θ / 20) * (L : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hround
  obtain ⟨t, ht, v, hv, hsum, hall⟩ := exists_physicalParametricGraftMark_pool_limit
    hθ hθcap hb hL hδ hsmall hpay pool z hroot hmark hscore hη
  exact ⟨L, hLnat, t, ht, v, hv, hsum, hall⟩

end WordCertDensity.Construction
