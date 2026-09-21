/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Roots.Basic
public import WordCertDensity.Words.Physical
public import Mathlib.Data.List.Basic

/-!
# Unique pre-one root visits and complete words

The accelerated map fixes one. A root strictly larger than one whose next
odd value is one can therefore occur at most once in any accelerated orbit.
This proves both basin disjointness and uniqueness of complete physical words.
-/

@[expose] public section

namespace WordCertDensity

/-- An odd root above one whose next accelerated value is one. -/
def OneStepRoot (root : ℕ) : Prop := 1 < root ∧ Odd root ∧ acceleratedStep root = 1

/-- Odd positive sources visiting the root without having reached one. -/
def preOneBasin (root : ℕ) : Set ℕ :=
  {x | 0 < x ∧ Odd x ∧ ∃ d : ℕ, (acceleratedStep^[d]) x = root ∧
    ∀ j ≤ d, (acceleratedStep^[j]) x ≠ 1}

/-- A later visit to a value other than one excludes every earlier hit of one. -/
theorem not_one_before_visit {x root d : ℕ} (hroot : root ≠ 1)
    (hvisit : (acceleratedStep^[d]) x = root) :
    ∀ j ≤ d, (acceleratedStep^[j]) x ≠ 1 := by
  intro j hj hone
  have hlater : (acceleratedStep^[d]) x = 1 := by
    rw [show d = (d - j) + j by omega, Function.iterate_add_apply, hone]
    exact Function.iterate_fixed acceleratedStep_one (d - j)
  exact hroot (hvisit.symm.trans hlater)

namespace OneStepRoot

/-- A root in this class is never one itself. -/
theorem ne_one {root : ℕ} (h : OneStepRoot root) : root ≠ 1 := ne_of_gt h.1

/-- Every accelerated time after visiting such a root has value one. -/
theorem later_eq_one {root x d n : ℕ} (h : OneStepRoot root)
    (hvisit : (acceleratedStep^[d]) x = root) (hn : d < n) :
    (acceleratedStep^[n]) x = 1 := by
  have hone : (acceleratedStep^[d + 1]) x = 1 := by
    rw [Function.iterate_succ_apply', hvisit]
    exact h.2.2
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (by omega : d + 1 ≤ n)
  rw [hk, Nat.add_comm, Function.iterate_add_apply, hone]
  exact Function.iterate_fixed acceleratedStep_one k

/-- Two visits to roots with next odd value one have the same time and root. -/
theorem visit_unique {root₁ root₂ x d₁ d₂ : ℕ}
    (h₁ : OneStepRoot root₁) (h₂ : OneStepRoot root₂)
    (hv₁ : (acceleratedStep^[d₁]) x = root₁)
    (hv₂ : (acceleratedStep^[d₂]) x = root₂) : d₁ = d₂ ∧ root₁ = root₂ := by
  have hle₁ : d₁ ≤ d₂ := by
    by_contra hlt
    exact h₁.ne_one (hv₁.symm.trans (h₂.later_eq_one hv₂ (Nat.lt_of_not_ge hlt)))
  have hle₂ : d₂ ≤ d₁ := by
    by_contra hlt
    exact h₂.ne_one (hv₂.symm.trans (h₁.later_eq_one hv₁ (Nat.lt_of_not_ge hlt)))
  have heq := Nat.le_antisymm hle₁ hle₂
  exact ⟨heq, hv₁.symm.trans (heq ▸ hv₂)⟩

/-- Distinct such roots have disjoint pre-one odd basins. -/
theorem disjoint_basins {root₁ root₂ : ℕ} (h₁ : OneStepRoot root₁)
    (h₂ : OneStepRoot root₂) (hne : root₁ ≠ root₂) :
    Disjoint (preOneBasin root₁) (preOneBasin root₂) := by
  rw [Set.disjoint_left]
  rintro x ⟨_, _, d₁, hv₁, _⟩ ⟨_, _, d₂, hv₂, _⟩
  exact hne (h₁.visit_unique h₂ hv₁ hv₂).2

end OneStepRoot

namespace Roots

/-- Every root after the first belongs to the nontrivial root class. -/
theorem oneStepRoot {s : ℕ} (hs : 1 < s) : OneStepRoot (value s) :=
  ⟨one_lt_value hs, value_odd (by omega), acceleratedStep_value s⟩

/-- Distinct indices after the first give disjoint pre-one basins. -/
theorem disjoint_basins {s t : ℕ} (hs : 1 < s) (ht : 1 < t) (hne : s ≠ t) :
    Disjoint (preOneBasin (value s)) (preOneBasin (value t)) :=
  (oneStepRoot hs).disjoint_basins (oneStepRoot ht) (fun heq => hne (value_injective heq))

end Roots

namespace PhysicalHistory

/-- A physical history ending above one belongs to that root's pre-one basin. -/
theorem mem_preOneBasin {w : ValuationWord} {root x : ℕ} (h : PhysicalHistory w root x)
    (hroot : root ≠ 1) : x ∈ preOneBasin root :=
  ⟨h.source_pos, h.source_odd, w.length, h.accelerated_iterate,
    not_one_before_visit hroot h.accelerated_iterate⟩

/-- Equal-length complete physical histories from one source have the same word. -/
theorem word_eq_of_length_eq {u v : ValuationWord} {root₁ root₂ x : ℕ}
    (hu : PhysicalHistory u root₁ x) (hv : PhysicalHistory v root₂ x)
    (hlen : u.length = v.length) : u = v := by
  apply List.reverse_injective
  apply List.map_injective_iff.mpr PNat.coe_injective
  rw [← hu.valuations_eq_reverse, ← hv.valuations_eq_reverse, hlen]

/-- Complete histories ending in the nontrivial root class have one root and one full word. -/
theorem complete_unique {u v : ValuationWord} {root₁ root₂ x : ℕ}
    (hu : PhysicalHistory u root₁ x) (hv : PhysicalHistory v root₂ x)
    (h₁ : OneStepRoot root₁) (h₂ : OneStepRoot root₂) : root₁ = root₂ ∧ u = v := by
  obtain ⟨hlen, hroot⟩ := h₁.visit_unique h₂ hu.accelerated_iterate hv.accelerated_iterate
  exact ⟨hroot, hu.word_eq_of_length_eq hv hlen⟩

/-- For the manuscript's root family, the source also determines the root index. -/
theorem root_index_word_unique {u v : ValuationWord} {s t x : ℕ}
    (hu : PhysicalHistory u (Roots.value s) x) (hv : PhysicalHistory v (Roots.value t) x)
    (hs : 1 < s) (ht : 1 < t) : s = t ∧ u = v := by
  obtain ⟨hroot, hword⟩ := hu.complete_unique hv (Roots.oneStepRoot hs) (Roots.oneStepRoot ht)
  exact ⟨Roots.value_injective hroot, hword⟩

end PhysicalHistory

end WordCertDensity
