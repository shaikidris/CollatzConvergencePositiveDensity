/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Roots.Basins
public import WordCertDensity.Roots.Predecessors
public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Nonrecurrent pools and predecessor fibers

The pool condition excludes every positive-time connection, including a
return to the same point. It supplies unique orbit visits without assuming
convergence. Mathlib's periodic points give the precise exceptional subset
of a predecessor fiber. Pooled weights and parsing are separate consumers.
-/

@[expose] public section

namespace WordCertDensity

variable {α : Type*} {f : α → α} {P Q : Set α}

/-- No positive iterate of a point of the pool is again in the pool. -/
def NonrecurrentPool (f : α → α) (P : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ P → ∀ ⦃y⦄, y ∈ P → ∀ ⦃n : ℕ⦄, 0 < n → (f^[n]) x ≠ y

/-- The empty pool has no orbit connections. -/
theorem nonrecurrentPool_empty (f : α → α) : NonrecurrentPool f ∅ := by
  intro x hx
  exact False.elim hx

namespace NonrecurrentPool

/-- Restricting a nonrecurrent pool preserves its orbit condition. -/
theorem mono (hP : NonrecurrentPool f P) (hQP : Q ⊆ P) : NonrecurrentPool f Q := by
  intro x hx y hy n hn
  exact hP (hQP hx) (hQP hy) hn

/-- Every member of a nonrecurrent pool is nonperiodic. -/
theorem not_mem_periodicPts (hP : NonrecurrentPool f P) {x : α} (hx : x ∈ P) :
    x ∉ Function.periodicPts f := by
  rintro ⟨n, hn, hperiod⟩
  exact hP hx hx hn hperiod.eq

/-- Two visits to a nonrecurrent pool have equal times and equal endpoints. -/
theorem visit_unique (hP : NonrecurrentPool f P) {x y z : α} {i j : ℕ}
    (hy : y ∈ P) (hz : z ∈ P) (hi : (f^[i]) x = y) (hj : (f^[j]) x = z) :
    i = j ∧ y = z := by
  have no_later {a b : ℕ} {u v : α} (hu : u ∈ P) (hv : v ∈ P)
      (ha : (f^[a]) x = u) (hb : (f^[b]) x = v) : ¬ a < b := by
    intro hab
    apply hP hu hv (Nat.sub_pos_of_lt hab)
    rw [← ha, ← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hab)]
    exact hb
  have heq : i = j := Nat.le_antisymm (Nat.le_of_not_gt (no_later hz hy hj hi))
    (Nat.le_of_not_gt (no_later hy hz hi hj))
  exact ⟨heq, hi.symm.trans (heq ▸ hj)⟩

end NonrecurrentPool

/-- For a singleton the pool condition is exactly absence of a positive period. -/
theorem nonrecurrentPool_singleton_iff (x : α) :
    NonrecurrentPool f {x} ↔ x ∉ Function.periodicPts f := by
  constructor
  · intro h
    exact h.not_mem_periodicPts (Set.mem_singleton x)
  · intro h y hy z hz n hn heq
    have hyx : y = x := hy
    have hzx : z = x := hz
    subst y
    subst z
    exact h ⟨n, hn, heq⟩

/-- A positive-time connection between two points of one fiber makes its endpoint periodic. -/
theorem periodic_of_fiber_visit {x z : α} {n : ℕ} (hn : 0 < n)
    (hf : f x = f z) (hvisit : (f^[n]) x = z) : z ∈ Function.periodicPts f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  refine ⟨k + 1, Nat.succ_pos k, ?_⟩
  change (f^[k + 1]) z = z
  rw [Function.iterate_succ_apply, ← hf, ← Function.iterate_succ_apply]
  exact hvisit

/-- A fiber contains at most one periodic point, even when its target lies on a cycle. -/
theorem periodic_fiber_subsingleton (f : α → α) (y : α) :
    Set.Subsingleton {x | f x = y ∧ x ∈ Function.periodicPts f} := by
  rintro x ⟨hx, m, hm, hxm⟩ z ⟨hz, n, hn, hzn⟩
  exact hxm.eq_of_apply_eq hzn hm hn (hx.trans hz.symm)

/-- Removing periodic points from a fiber excludes all positive-time connections. -/
theorem nonrecurrentPool_nonperiodic_fiber (f : α → α) (y : α) :
    NonrecurrentPool f {x | f x = y ∧ x ∉ Function.periodicPts f} := by
  intro x hx z hz n hn hvisit
  exact hz.2 (periodic_of_fiber_visit hn (hx.1.trans hz.1.symm) hvisit)

/-- The original roots above one form a pool in the general sense. -/
theorem nonrecurrentPool_oneStepRoots :
    NonrecurrentPool acceleratedStep {x | OneStepRoot x} := by
  intro x hx y hy n hn hvisit
  have heq := (OneStepRoot.visit_unique hx hy (d₁ := 0) rfl hvisit).1
  omega

namespace Roots

/-- At most one inverse-constructor index is periodic for a fixed odd unit target. -/
theorem inverseRoot_periodic_index_unique {y s t : ℕ} (hy : ¬ 3 ∣ y) (hodd : Odd y)
    (hs : inverseRoot y s ∈ Function.periodicPts acceleratedStep)
    (ht : inverseRoot y t ∈ Function.periodicPts acceleratedStep) : s = t := by
  apply inverseRoot_injective hy
  exact periodic_fiber_subsingleton acceleratedStep y
    ⟨inverseRoot_acceleratedStep hy hodd s, hs⟩
    ⟨inverseRoot_acceleratedStep hy hodd t, ht⟩

/-- The nonperiodic indexed predecessors form a pool without a convergence premise on the target. -/
theorem inverseRoot_nonrecurrentPool {y : ℕ} (hy : ¬ 3 ∣ y) (hodd : Odd y) :
    NonrecurrentPool acceleratedStep
      {x | (∃ t, inverseRoot y t = x) ∧ x ∉ Function.periodicPts acceleratedStep} := by
  apply (nonrecurrentPool_nonperiodic_fiber acceleratedStep y).mono
  rintro x ⟨⟨t, rfl⟩, hx⟩
  exact ⟨inverseRoot_acceleratedStep hy hodd t, hx⟩

end Roots

end WordCertDensity
