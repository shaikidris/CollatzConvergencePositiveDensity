/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The PMF projection and real-sum bridge follow the short map-composition
arguments of Lech Mazur, Copyright 2026 Lech Mazur, under Apache License 2.0.
The source LICENSE and NOTICE are retained at
research/sources/mazur_830b9d3f38f2/. The finite normalization proofs are local.
-/
module

public import WordCertDensity.Reference.Law
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Projectivity and full-group normalization

The geometric reference law projects exactly between ternary levels.
Counting each projection fiber gives the density average identity and the
uniform lifting of probability masses. The L1 identities contain no factor
one half, and the marker factor two thirds is paid once.
-/

@[expose] public section

namespace WordCertDensity

namespace Reference

/-- Ternary projection is onto at all levels, including level zero. -/
theorem project_surjective {m n : ℕ} (h : m ≤ n) : Function.Surjective (project h) :=
  ZMod.castHom_surjective (Nat.pow_dvd_pow 3 h)

/-- Projection to the same level fixes every residue. -/
theorem project_self (n : ℕ) (x : ZMod (3 ^ n)) : project (le_refl n) x = x := by
  simpa only [ZMod.natCast_zmod_val] using project_natCast (le_refl n) x.val

/-- The actual reference PMF projects to the lower-level reference PMF. -/
theorem law_map_project {m n : ℕ} (h : m ≤ n) : (law n).map (project h) = law m := by
  simp only [law, PMF.map_comp]
  have hfun : project h ∘ ValuationWord.residueOffset n =
      ValuationWord.residueOffset m ∘ (fun w : ValuationWord => w.take m) := by
    funext w
    exact ValuationWord.project_residueOffset_take h w
  rw [hfun, ← PMF.map_comp, wordPMF_map_take_of_le h]

/-- The finite set of upper-level residues over one lower-level residue. -/
noncomputable def fiber {m n : ℕ} (h : m ≤ n) (y : ZMod (3 ^ m)) : Finset (ZMod (3 ^ n)) :=
  Finset.univ.filter (fun x => project h x = y)

/-- Membership in a projection fiber is exactly its projection equation. -/
@[simp] theorem mem_fiber {m n : ℕ} (h : m ≤ n) (y : ZMod (3 ^ m)) (x : ZMod (3 ^ n)) :
    x ∈ fiber h y ↔ project h x = y := by
  simp [fiber]

/-- Every ternary projection fiber has exactly the modulus-ratio cardinality. -/
theorem card_fiber {m n : ℕ} (h : m ≤ n) (y : ZMod (3 ^ m)) :
    (fiber h y).card = 3 ^ (n - m) := by
  have heq (z : ZMod (3 ^ m)) : (fiber h z).card = (fiber h y).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range (project h)
      (project_surjective h z) (project_surjective h y)
  have htotal : (∑ z : ZMod (3 ^ m), (fiber h z).card) = 3 ^ n := by
    simpa [fiber, ZMod.card] using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (ZMod (3 ^ n))) Finset.univ (project h)
  have hmul : 3 ^ m * (fiber h y).card = 3 ^ n := by
    calc
      3 ^ m * (fiber h y).card = ∑ _z : ZMod (3 ^ m), (fiber h y).card := by
        simp [ZMod.card]
      _ = ∑ z : ZMod (3 ^ m), (fiber h z).card :=
        Finset.sum_congr rfl (fun z _ => (heq z).symm)
      _ = 3 ^ n := htotal
  apply mul_left_cancel₀ (pow_ne_zero m (by decide : (3 : ℕ) ≠ 0))
  calc
    3 ^ m * (fiber h y).card = 3 ^ n := hmul
    _ = 3 ^ m * 3 ^ (n - m) := by rw [← pow_add, Nat.add_sub_of_le h]

/-- The real reference mass of a fiber is precisely its projected atom. -/
theorem mass_fiber {m n : ℕ} (h : m ≤ n) (y : ZMod (3 ^ m)) :
    (∑ x ∈ fiber h y, mass n x) = mass m y := by
  classical
  have hp := congrArg (fun p : PMF (ZMod (3 ^ m)) => p y) (law_map_project h)
  rw [PMF.map_apply, tsum_fintype] at hp
  have hf : (∑ x ∈ fiber h y, law n x) = law m y := by
    calc
      (∑ x ∈ fiber h y, law n x) =
          ∑ x, @ite ENNReal (y = project h x) (Classical.propDecidable _) (law n x) 0 := by
        rw [fiber, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : project h x = y
        · rw [if_pos hx, if_pos hx.symm]
        · rw [if_neg hx, if_neg (Ne.symm hx)]
      _ = law m y := hp
  change (∑ x ∈ fiber h y, (law n x).toReal) = (law m y).toReal
  rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top _ x), hf]

/-- Real ternary scales factor by a projection's depth difference. -/
theorem scale_eq {m n : ℕ} (h : m ≤ n) :
    (3 : ℝ) ^ n = (3 : ℝ) ^ (n - m) * (3 : ℝ) ^ m := by
  rw [← pow_add, Nat.sub_add_cancel h]

/-- The density sum on a fiber is its size times the lower-level density. -/
theorem density_fiber {m n : ℕ} (h : m ≤ n) (y : ZMod (3 ^ m)) :
    (∑ x ∈ fiber h y, density n x) = (3 : ℝ) ^ (n - m) * density m y := by
  simp only [density, ← Finset.mul_sum, mass_fiber h y]
  rw [scale_eq h, mul_assoc]

/-- Projectivity is exactly the full finite fiber average identity for density. -/
theorem density_fiber_average {m n : ℕ} (h : m ≤ n) (y : ZMod (3 ^ m)) :
    (∑ x ∈ fiber h y, density n x) / (3 : ℝ) ^ (n - m) = density m y := by
  rw [density_fiber h y]
  simp

/-- The marker obeys the same finite fiber sum identity. -/
theorem marker_fiber {m n : ℕ} (h : m ≤ n) (y : ZMod (3 ^ m)) :
    (∑ x ∈ fiber h y, marker n x) = (3 : ℝ) ^ (n - m) * marker m y := by
  simp only [marker, ← Finset.mul_sum, density_fiber h y]
  ring

/-- Each upper density is bounded by the nonnegative density sum on its fiber. -/
theorem density_le_fiber {m n : ℕ} (h : m ≤ n) (x : ZMod (3 ^ n)) :
    density n x ≤ (3 : ℝ) ^ (n - m) * density m (project h x) := by
  rw [← density_fiber h]
  exact Finset.single_le_sum (fun z _ => density_nonneg n z) (by simp)

/-- A zero lower-level density forces zero throughout its fiber. -/
theorem density_eq_zero_of_project_eq_zero {m n : ℕ} (h : m ≤ n) (x : ZMod (3 ^ n))
    (hx : density m (project h x) = 0) : density n x = 0 := by
  exact le_antisymm (by simpa [hx] using density_le_fiber h x) (density_nonneg n x)

/-- Summing a pullback multiplies its lower-level sum by the exact fiber size. -/
theorem sum_project {m n : ℕ} (h : m ≤ n) (f : ZMod (3 ^ m) → ℝ) :
    (∑ x : ZMod (3 ^ n), f (project h x)) = (3 : ℝ) ^ (n - m) * ∑ y, f y := by
  have hf := Finset.sum_fiberwise' (Finset.univ : Finset (ZMod (3 ^ n))) (project h) f
  change (∑ y, ∑ _x ∈ fiber h y, f y) = ∑ x, f (project h x) at hf
  simp only [Finset.sum_const, card_fiber, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hf
  simpa only [← Finset.mul_sum] using hf.symm

/-- Full-group uniform means are unchanged by ternary pullback. -/
theorem mean_project {m n : ℕ} (h : m ≤ n) (f : ZMod (3 ^ m) → ℝ) :
    mean n (fun x => f (project h x)) = mean m f := by
  simp only [mean]
  rw [sum_project h, scale_eq h]
  field_simp

/-- Uniform lifting divides a lower probability mass equally among its fiber. -/
noncomputable def liftMass {m n : ℕ} (h : m ≤ n) (x : ZMod (3 ^ n)) : ℝ :=
  mass m (project h x) / (3 : ℝ) ^ (n - m)

/-- The uniformly lifted probability masses are nonnegative. -/
theorem liftMass_nonneg {m n : ℕ} (h : m ≤ n) (x : ZMod (3 ^ n)) : 0 ≤ liftMass h x :=
  div_nonneg (mass_nonneg _ _) (by positivity)

/-- Uniform lifting preserves total probability mass one. -/
theorem liftMass_sum {m n : ℕ} (h : m ≤ n) : ∑ x, liftMass h x = 1 := by
  change (∑ x, mass m (project h x) / (3 : ℝ) ^ (n - m)) = 1
  rw [← Finset.sum_div, sum_project h, mass_sum]
  simp

/-- The upper-level density of the uniform lift is the lower density pulled back. -/
theorem density_liftMass {m n : ℕ} (h : m ≤ n) (x : ZMod (3 ^ n)) :
    (3 : ℝ) ^ n * liftMass h x = density m (project h x) := by
  simp only [liftMass, density]
  rw [scale_eq h]
  field_simp

/-- Full-group density L1 is the unhalved L1 distance of the two probability masses. -/
theorem fullL1_eq_sum_mass {m n : ℕ} (h : m ≤ n) :
    mean n (fun x => |density n x - density m (project h x)|) =
      ∑ x, |mass n x - liftMass h x| := by
  have heq (x : ZMod (3 ^ n)) : |density n x - density m (project h x)| =
      (3 : ℝ) ^ n * |mass n x - liftMass h x| := by
    rw [← density_liftMass h x]
    simp only [density, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ n)]
  simp only [mean, heq, ← Finset.mul_sum]
  simp

/-- The full, unhalved reference oscillation is nonnegative. -/
theorem fullL1_nonneg {m n : ℕ} (h : m ≤ n) :
    0 ≤ mean n (fun x => |density n x - density m (project h x)|) :=
  mean_nonneg n _ (fun _ => abs_nonneg _)

/-- Two probability masses have unhalved L1 distance at most two. -/
theorem fullL1_le_two {m n : ℕ} (h : m ≤ n) :
    mean n (fun x => |density n x - density m (project h x)|) ≤ 2 := by
  rw [fullL1_eq_sum_mass h]
  calc
    (∑ x, |mass n x - liftMass h x|) ≤ ∑ x, (mass n x + liftMass h x) := by
      apply Finset.sum_le_sum
      intro x _
      apply abs_le.mpr
      constructor <;> linarith [mass_nonneg n x, liftMass_nonneg h x]
    _ = 2 := by rw [Finset.sum_add_distrib, mass_sum, liftMass_sum]; norm_num

/-- Marker L1 pays exactly one factor two thirds relative to density L1. -/
theorem marker_fullL1 {m n : ℕ} (h : m ≤ n) :
    mean n (fun x => |marker n x - marker m (project h x)|) =
      (2 / 3 : ℝ) * mean n (fun x => |density n x - density m (project h x)|) := by
  have heq (x : ZMod (3 ^ n)) : |marker n x - marker m (project h x)| =
      (2 / 3 : ℝ) * |density n x - density m (project h x)| := by
    simp only [marker, ← mul_sub, abs_mul]
    norm_num
  simp_rw [heq]
  exact mean_mul n (2 / 3) _

/-- Equal levels have zero reference oscillation. -/
theorem fullL1_self (n : ℕ) :
    mean n (fun x => |density n x - density n (project (le_refl n) x)|) = 0 := by
  simp only [project_self, sub_self, abs_zero]
  exact mean_const n 0

end Reference

end WordCertDensity
