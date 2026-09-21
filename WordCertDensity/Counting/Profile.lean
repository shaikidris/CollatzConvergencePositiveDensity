/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.ProfileDuality
import WordCertDensity.Reference.Fan

/-! # Exact allocation for the manuscript residue fan -/

namespace WordCertDensity.Counting

/-- The manuscript feasible region retains the full-group capacity normalization. -/
def feasibleProfile (m : ℕ) (p : ℝ) (w : ZMod (3^m) → ℝ) : Prop :=
  (∀ r, 0 ≤ w r ∧ w r ≤ (2*Real.log 2)/(3 : ℝ)^m) ∧
    p ≤ ∑ r, w r*Reference.fan m r

/-- The exact residue profile is the infimum of feasible occupied masses. -/
noncomputable def profile (m : ℕ) (p : ℝ) : ℝ :=
  sInf {u | ∃ w, feasibleProfile m p w ∧ u = ∑ r, w r}

/-- Reindexing by the canonical finite equivalence preserves every capacity constraint. -/
theorem feasibleProfile_reindex (m : ℕ) (p : ℝ) (w : ZMod (3^m) → ℝ) :
    feasibleProfile m p w ↔ feasibleAllocation (3^m)
      (fun i => Reference.fan m (ZMod.finEquiv (3^m) i)) (2*Real.log 2) p
      (fun i => w (ZMod.finEquiv (3^m) i)) := by
  let e : Fin (3^m) ≃ ZMod (3^m) := ZMod.finEquiv (3^m)
  have hs := e.sum_comp (fun r => w r*Reference.fan m r)
  constructor
  · rintro ⟨hw, hp⟩
    refine ⟨fun i => ?_, ?_⟩
    · simpa [e] using hw (e i)
    · exact hs.symm ▸ hp
  · rintro ⟨hw, hp⟩
    refine ⟨fun r => ?_, ?_⟩
    · simpa [e] using hw (e.symm r)
    · exact hs ▸ hp

/-- The residue infimum is exactly the finite allocation value, with no relaxation. -/
theorem profile_reindex (m : ℕ) (p : ℝ) :
    profile m p = allocationValue (3^m)
      (fun i => Reference.fan m (ZMod.finEquiv (3^m) i)) (2*Real.log 2) p := by
  let e : Fin (3^m) ≃ ZMod (3^m) := ZMod.finEquiv (3^m)
  unfold profile allocationValue
  congr 1
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨fun i => w (e i), (feasibleProfile_reindex m p w).1 hw,
      (e.sum_comp w).symm⟩
  · rintro ⟨v, hv, rfl⟩
    let w : ZMod (3^m) → ℝ := fun r => v (e.symm r)
    have he : (fun i => w (e i)) = v := by funext i; simp [w]
    have hw : feasibleProfile m p w := (feasibleProfile_reindex m p w).2 (he ▸ hv)
    refine ⟨w, hw, ?_⟩
    simpa only [he] using e.sum_comp w

/-- The manuscript profile attains its minimum and equals its hinge dual on the full feasible range. -/
theorem profile_hinge (m : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hpaid : p ≤ (2*Real.log 2)*(8/9)) :
    (∃ w, feasibleProfile m p w ∧ (∑ r, w r) = profile m p) ∧
    profile m p = sSup {a | ∃ t : ℝ, 0 < t ∧
      a = max (p-(2*Real.log 2)*Reference.mean m
        (fun r => max (Reference.fan m r-t) 0)) 0/t} ∧
    0 ≤ profile m p ∧ profile m p ≤ p/(8/9) := by
  let e : Fin (3^m) ≃ ZMod (3^m) := ZMod.finEquiv (3^m)
  let h : Fin (3^m) → ℝ := fun i => Reference.fan m (e i)
  have hQ : 0 < 3^m := pow_pos (by decide) m
  have hμ : (0 : ℝ) < 8/9 := by norm_num
  have hT : 0 < 2*Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hmean : (∑ i, h i)/(3^m : ℕ) = (8/9 : ℝ) := by
    rw [show (∑ i, h i) = ∑ r, Reference.fan m r by
      change (∑ i, Reference.fan m (e i)) = ∑ r, Reference.fan m r
      exact e.sum_comp _]
    simpa only [Reference.mean, Nat.cast_pow, Nat.cast_ofNat] using Reference.mean_fan m
  have hu := feasibleAllocation_uniform (3^m) h (8/9) (2*Real.log 2) p hQ hμ hp hpaid hmean
  obtain ⟨v, hv, heq⟩ := allocationValue_attained (3^m) h (2*Real.log 2) p ⟨_, hu.1⟩
  let w : ZMod (3^m) → ℝ := fun r => v (e.symm r)
  have he : (fun i => w (e i)) = v := by funext i; simp [w]
  have hw : feasibleProfile m p w := (feasibleProfile_reindex m p w).2 (he ▸ hv)
  have hmass : (∑ r, w r) = ∑ i, v i := by simpa only [he] using (e.sum_comp w).symm
  refine ⟨⟨w, hw, ?_⟩, ?_, ?_⟩
  · rw [hmass, profile_reindex]
    exact heq
  · rw [profile_reindex]
    change allocationValue (3^m) h (2*Real.log 2) p = _
    rw [allocationValue_duality (3^m) h (8/9) (2*Real.log 2) p
      hQ hμ hT hp hpaid hmean]
    congr 1
    ext a
    have hh (t : ℝ) :
        ((2*Real.log 2)/(3^m : ℕ))*∑ i, max (h i-t) 0 =
          (2*Real.log 2)*Reference.mean m (fun r => max (Reference.fan m r-t) 0) := by
      rw [show (∑ i, max (h i-t) 0) = ∑ r, max (Reference.fan m r-t) 0 by
        change (∑ i, max (Reference.fan m (e i)-t) 0) =
          ∑ r, max (Reference.fan m r-t) 0
        exact e.sum_comp (fun r : ZMod (3^m) =>
          max (Reference.fan m r-t) 0)]
      simp only [Reference.mean, Nat.cast_pow, Nat.cast_ofNat]
      ring
    simp only [hh]
  · rw [profile_reindex]
    exact allocationValue_domain (3^m) h (8/9) (2*Real.log 2) p hQ hμ hp hpaid hmean

/-- Every positive feasible manuscript demand has a threshold-optimal residue profile.
The marked mass is exact and at most one residue is partially occupied. -/
theorem profile_greedy (m : ℕ) (p : ℝ) (hp : 0 < p)
    (hpaid : p ≤ (2*Real.log 2)*(8/9)) :
    ∃ w : ZMod (3^m) → ℝ, ∃ t : ℝ, 0 < t ∧ feasibleProfile m p w ∧
      (∀ r, t < Reference.fan m r → w r = (2*Real.log 2)/(3 : ℝ)^m) ∧
      (∀ r, Reference.fan m r < t → w r = 0) ∧
      (∑ r, w r*Reference.fan m r) = p ∧
      profile m p = ∑ r, w r ∧
      profile m p = max (p-(2*Real.log 2)*Reference.mean m
        (fun r => max (Reference.fan m r-t) 0)) 0/t ∧
      (∀ i j, 0 < w i → w i < (2*Real.log 2)/(3 : ℝ)^m →
        0 < w j → w j < (2*Real.log 2)/(3 : ℝ)^m → i = j) := by
  let e : Fin (3^m) ≃ ZMod (3^m) := ZMod.finEquiv (3^m)
  let h : Fin (3^m) → ℝ := fun i => Reference.fan m (e i)
  have hQ : 0 < 3^m := pow_pos (by decide) m
  have hT : 0 < 2*Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hmean : (∑ i, h i)/(3^m : ℕ) = (8/9 : ℝ) := by
    rw [show (∑ i, h i) = ∑ r, Reference.fan m r by
      change (∑ i, Reference.fan m (e i)) = ∑ r, Reference.fan m r
      exact e.sum_comp _]
    simpa only [Reference.mean, Nat.cast_pow, Nat.cast_ofNat] using Reference.mean_fan m
  obtain ⟨v, t, ht, hv, hvthreshold, hvmark, hvvalue, hvhinge, hvpartial⟩ :=
    allocationValue_greedy (3^m) h (8/9) (2*Real.log 2) p hQ hT hp hpaid hmean
  let w : ZMod (3^m) → ℝ := fun r => v (e.symm r)
  have he : (fun i => w (e i)) = v := by funext i; simp [w]
  have hw : feasibleProfile m p w := (feasibleProfile_reindex m p w).2 (he ▸ hv)
  refine ⟨w, t, ht, hw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [show w r = v (e.symm r) by simp [w]]
    have := hvthreshold.1 (e.symm r) (by simpa [h] using hr)
    simpa [e] using this
  · intro r hr
    rw [show w r = v (e.symm r) by simp [w]]
    exact hvthreshold.2 (e.symm r) (by simpa [h] using hr)
  · rw [show (∑ r, w r*Reference.fan m r) = ∑ i, v i*h i by
      change (∑ r, w r*Reference.fan m r) = ∑ i, v i * Reference.fan m (e i)
      rw [← he]
      exact (e.sum_comp (fun r => w r*Reference.fan m r)).symm]
    exact hvmark
  · rw [profile_reindex]
    calc
      allocationValue (3^m) h (2*Real.log 2) p = ∑ i, v i := hvvalue
      _ = ∑ r, w r := by simpa only [he] using e.sum_comp w
  · rw [profile_reindex]
    change allocationValue (3^m) h (2*Real.log 2) p = _
    rw [hvhinge]
    congr 2
    rw [show (∑ i, max (h i-t) 0) = ∑ r, max (Reference.fan m r-t) 0 by
      change (∑ i, max (Reference.fan m (e i)-t) 0) =
        ∑ r, max (Reference.fan m r-t) 0
      exact e.sum_comp (fun r : ZMod (3^m) => max (Reference.fan m r-t) 0)]
    simp only [Reference.mean, Nat.cast_pow, Nat.cast_ofNat]
    ring
  · intro i j hi0 hiC hj0 hjC
    apply e.symm.injective
    apply hvpartial (e.symm i) (e.symm j)
    · simpa [w] using hi0
    · simpa [w] using hiC
    · simpa [w] using hj0
    · simpa [w] using hjC

/-- A nonnegative manuscript demand is feasible exactly up to the full fan capacity. -/
theorem feasibleProfile_iff (m : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    (∃ w, feasibleProfile m p w) ↔ p ≤ (2*Real.log 2)*(8/9) := by
  constructor
  · rintro ⟨w, hw⟩
    calc
      p ≤ ∑ r, w r*Reference.fan m r := hw.2
      _ ≤ ∑ r, ((2*Real.log 2)/(3 : ℝ)^m)*Reference.fan m r :=
        Finset.sum_le_sum (fun r _ =>
          mul_le_mul_of_nonneg_right (hw.1 r).2 (Reference.fan_nonneg m r))
      _ = (2*Real.log 2)*Reference.mean m (Reference.fan m) := by
        unfold Reference.mean
        rw [← Finset.mul_sum]
        ring
      _ = (2*Real.log 2)*(8/9) := by rw [Reference.mean_fan]
  · intro hpaid
    exact ⟨(profile_hinge m p hp hpaid).1.choose, (profile_hinge m p hp hpaid).1.choose_spec.1⟩

/-- Above full capacity, the positive-threshold hinge values are unbounded. -/
theorem profile_hinge_unbounded (m : ℕ) (p : ℝ)
    (hp : (2*Real.log 2)*(8/9) < p) :
    ¬ BddAbove {a : ℝ | ∃ t : ℝ, 0 < t ∧
      a = max (p-(2*Real.log 2)*Reference.mean m
        (fun r => max (Reference.fan m r-t) 0)) 0/t} := by
  apply not_bddAbove_iff.mpr
  intro B
  let d := p-(2*Real.log 2)*(8/9)
  have hd : 0 < d := sub_pos.mpr hp
  let t := d/(max B 0+1)
  have hb : 0 < max B 0+1 := by linarith [le_max_right B 0]
  have ht : 0 < t := div_pos hd hb
  have hm : Reference.mean m (fun r => max (Reference.fan m r-t) 0) ≤ 8/9 := by
    rw [← Reference.mean_fan m]
    unfold Reference.mean
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Finset.sum_le_sum (fun r _ => max_le
      (sub_le_self _ ht.le) (Reference.fan_nonneg m r))
  have hL : 0 ≤ 2*Real.log 2 := by positivity
  have hn : d ≤ max (p-(2*Real.log 2)*Reference.mean m
      (fun r => max (Reference.fan m r-t) 0)) 0 :=
    (sub_le_sub_left (mul_le_mul_of_nonneg_left hm hL) p).trans (le_max_left _ _)
  refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
  have he : d/t = max B 0+1 := by dsimp [t]; field_simp
  calc
    B < max B 0+1 := by linarith [le_max_left B 0]
    _ = d/t := he.symm
    _ ≤ _ := div_le_div_of_nonneg_right hn ht.le

end WordCertDensity.Counting
