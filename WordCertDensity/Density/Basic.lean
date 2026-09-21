/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Positive-prefix counts and lower natural density

The finite profile counts $S$ in $[1,N]$ and divides by $N$. The value at
$N=0$ is zero. All lower-density assertions use this same profile, including
both parities; no logarithmic weighting or density-one surrogate is used.
-/

@[expose] public section

namespace WordCertDensity

open Filter
open scoped Finset

noncomputable section

/-- Count members of a set in the positive prefix `[1,N]`. -/
def prefixCount (S : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact #{x ∈ Finset.Icc 1 N | x ∈ S}

/-- The concrete finite profile used by natural density. -/
def partialDensity (S : Set ℕ) (N : ℕ) : ℝ := (prefixCount S N : ℝ) / N

/-- Lower natural density along positive integer cutoffs. -/
def lowerNaturalDensity (S : Set ℕ) : ℝ := liminf (partialDensity S) atTop

/-- Empty prefixes have zero count. -/
@[simp] theorem prefixCount_zero (S : Set ℕ) : prefixCount S 0 = 0 := by
  simp [prefixCount]

/-- The empty set has zero count in every prefix. -/
@[simp] theorem prefixCount_empty (N : ℕ) : prefixCount ∅ N = 0 := by
  simp [prefixCount]

/-- The full set has exactly `N` members in the positive prefix. -/
@[simp] theorem prefixCount_univ (N : ℕ) : prefixCount Set.univ N = N := by
  simp [prefixCount, Nat.card_Icc]

/-- Inclusion preserves each finite positive-prefix count. -/
theorem prefixCount_mono {S T : Set ℕ} (hST : S ⊆ T) (N : ℕ) :
    prefixCount S N ≤ prefixCount T N := by
  classical
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hST hx.2⟩

/-- Counts never exceed the size of the positive prefix. -/
theorem prefixCount_le (S : Set ℕ) (N : ℕ) : prefixCount S N ≤ N := by
  simpa using prefixCount_mono (Set.subset_univ S) N

/-- The finite density profile is nonnegative, including at zero. -/
theorem partialDensity_nonneg (S : Set ℕ) (N : ℕ) : 0 ≤ partialDensity S N := by
  unfold partialDensity
  positivity

/-- The finite density profile is at most one. -/
theorem partialDensity_le_one (S : Set ℕ) (N : ℕ) : partialDensity S N ≤ 1 := by
  by_cases hN : N = 0
  · simp [partialDensity, hN]
  · have hpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    apply (div_le_one hpos).2
    exact_mod_cast prefixCount_le S N

/-- Inclusion preserves the finite density profile. -/
theorem partialDensity_mono {S T : Set ℕ} (hST : S ⊆ T) (N : ℕ) :
    partialDensity S N ≤ partialDensity T N := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast prefixCount_mono hST N

/-- The universal finite density is one at every positive cutoff. -/
theorem partialDensity_univ {N : ℕ} (hN : 0 < N) : partialDensity Set.univ N = 1 := by
  simp [partialDensity, ne_of_gt hN]

/-- Lower natural density is nonnegative. -/
theorem lowerNaturalDensity_nonneg (S : Set ℕ) : 0 ≤ lowerNaturalDensity S := by
  have hupper : atTop.IsBoundedUnder (· ≤ ·) (partialDensity S) :=
    ⟨1, by
      change ∀ᶠ N : ℕ in atTop, partialDensity S N ≤ 1
      exact Eventually.of_forall (partialDensity_le_one S)⟩
  exact le_liminf_of_le hupper.isCoboundedUnder_ge
    (Eventually.of_forall (partialDensity_nonneg S))

/-- Inclusion preserves lower natural density. -/
theorem lowerNaturalDensity_mono {S T : Set ℕ} (hST : S ⊆ T) :
    lowerNaturalDensity S ≤ lowerNaturalDensity T := by
  have hlower : atTop.IsBoundedUnder (· ≥ ·) (partialDensity S) :=
    ⟨0, by
      change ∀ᶠ N : ℕ in atTop, 0 ≤ partialDensity S N
      exact Eventually.of_forall (partialDensity_nonneg S)⟩
  have hupper : atTop.IsBoundedUnder (· ≤ ·) (partialDensity T) :=
    ⟨1, by
      change ∀ᶠ N : ℕ in atTop, partialDensity T N ≤ 1
      exact Eventually.of_forall (partialDensity_le_one T)⟩
  exact liminf_le_liminf (Eventually.of_forall (partialDensity_mono hST))
    hlower hupper.isCoboundedUnder_ge

/-- The full set has lower natural density one. -/
@[simp] theorem lowerNaturalDensity_univ : lowerNaturalDensity Set.univ = 1 := by
  have heq : partialDensity Set.univ =ᶠ[atTop] (fun _ => (1 : ℝ)) :=
    eventually_atTop.2 ⟨1, fun N hN => partialDensity_univ (by omega)⟩
  unfold lowerNaturalDensity
  rw [liminf_congr heq, liminf_const]

/-- Lower natural density never exceeds one. -/
theorem lowerNaturalDensity_le_one (S : Set ℕ) : lowerNaturalDensity S ≤ 1 := by
  simpa using lowerNaturalDensity_mono (Set.subset_univ S)

/-- A liminf lower bound means every strictly smaller constant is eventual. -/
theorem le_lowerNaturalDensity_iff (S : Set ℕ) (d : ℝ) :
    d ≤ lowerNaturalDensity S ↔ ∀ e < d, ∀ᶠ N in atTop, e ≤ partialDensity S N := by
  have hlower : atTop.IsBoundedUnder (· ≥ ·) (partialDensity S) :=
    ⟨0, by
      change ∀ᶠ N : ℕ in atTop, 0 ≤ partialDensity S N
      exact Eventually.of_forall (partialDensity_nonneg S)⟩
  have hupper : atTop.IsBoundedUnder (· ≤ ·) (partialDensity S) :=
    ⟨1, by
      change ∀ᶠ N : ℕ in atTop, partialDensity S N ≤ 1
      exact Eventually.of_forall (partialDensity_le_one S)⟩
  exact le_liminf_iff' hupper.isCoboundedUnder_ge hlower

/-- The empty set has lower natural density zero. -/
@[simp] theorem lowerNaturalDensity_empty : lowerNaturalDensity ∅ = 0 := by
  have heq : partialDensity ∅ = (fun _ => (0 : ℝ)) := by
    funext N
    simp [partialDensity]
  rw [lowerNaturalDensity, heq, liminf_const]

end

end WordCertDensity
