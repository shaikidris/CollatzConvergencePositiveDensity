/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.Data.Summaries

/-! # Exact composition of bounded integer sum certificates -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Sum a natural-valued function over a consecutive finite interval. -/
def rangeSum (f : Nat → Nat) (start count : Nat) : Nat :=
  ((List.range count).map (fun i => f (start + i))).sum

/-- Adjacent intervals account for the complete sum, including empty intervals. -/
theorem rangeSum_add (f : Nat → Nat) (start a b : Nat) :
    rangeSum f start (a + b) = rangeSum f start a + rangeSum f (start + a) b := by
  simp [rangeSum, List.range_add, List.map_append, List.sum_append,
    List.map_map, Function.comp_def, Nat.add_assoc]

/-- Join exact partial-sum certificates without re-evaluating their entries. -/
theorem rangeSum_join (f : Nat → Nat) (start a b u v : Nat)
    (ha : rangeSum f start a = u) (hb : rangeSum f (start + a) b = v) :
    rangeSum f start (a + b) = u + v := by
  rw [rangeSum_add, ha, hb]

/-- Adjacent finite pointwise certificates cover the full interval. -/
theorem forallInterval_join (P : Nat → Prop) (start a b : Nat)
    (ha : ∀ i : Fin a, P (start + i.val))
    (hb : ∀ i : Fin b, P (start + a + i.val)) :
    ∀ i : Fin (a + b), P (start + i.val) := by
  intro i
  by_cases h : i.val < a
  · exact ha ⟨i.val, h⟩
  · have hi : i.val - a < b := by omega
    have hp := hb ⟨i.val - a, hi⟩
    have he : start + a + (i.val - a) = start + i.val := by omega
    exact he ▸ hp

/-- The energy numerator is the complete zero-based interval sum. -/
theorem energySum_range (z : Entries) (n : Nat) :
    z.energySum n = rangeSum (fun i => z.lookup i ^ 2) 0 n := by
  simp [Entries.energySum, rangeSum]

/-- The fractional numerator is the complete zero-based interval sum. -/
theorem fractionalSum_range (z r : Entries) (n : Nat) :
    z.fractionalSum r n = rangeSum (fun i => z.lookup i * r.lookup i) 0 n := by
  simp [Entries.fractionalSum, rangeSum]

end WordCertDensity.Certificates
