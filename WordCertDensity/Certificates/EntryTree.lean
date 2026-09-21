/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Init

/-! # Binary lookup trees and kernel-checkable range certificates -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Finite natural data, addressed by successive low bits of the index. -/
inductive Entries where
  | empty
  | leaf (value : Nat)
  | node (even odd : Entries)

/-- Missing positions read as zero, including indices beyond a leaf. -/
def Entries.lookup : Entries → Nat → Nat
  | .empty, _ => 0
  | .leaf value, i => if i == 0 then value else 0
  | .node even odd, i =>
      if i % 2 == 0 then even.lookup (i / 2) else odd.lookup (i / 2)

/-- Number of stored leaves; this alone does not assert contiguous index coverage. -/
def Entries.size : Entries → Nat
  | .empty => 0
  | .leaf _ => 1
  | .node even odd => even.size + odd.size

/-- A structural natural maximum check on all stored values. -/
def Entries.allLE (cap : Nat) : Entries → Bool
  | .empty => true
  | .leaf value => value <= cap
  | .node even odd => even.allLE cap && odd.allLE cap

/-- A successful structural maximum check bounds every lookup, including missing positions. -/
theorem Entries.lookup_le (tree : Entries) (cap : Nat) (h : tree.allLE cap = true)
    (i : Nat) : tree.lookup i ≤ cap := by
  induction tree generalizing i with
  | empty => simp [Entries.lookup]
  | leaf value =>
    have hv : value ≤ cap := by simpa [Entries.allLE] using h
    simp only [Entries.lookup]
    split <;> omega
  | node even odd he ho =>
    have hs : even.allLE cap = true ∧ odd.allLE cap = true := by
      simpa only [Entries.allLE, Bool.and_eq_true] using h
    simp only [Entries.lookup]
    split
    · exact he hs.1 _
    · exact ho hs.2 _

/-- Check a contiguous range against any computable integer right-hand side. -/
def Entries.checkRange (tree : Entries) (rhs : Nat → Nat) (start count : Nat) : Bool :=
  (List.range count).all (fun offset => tree.lookup (start + offset) == rhs (start + offset))

/-- A Boolean range check is exactly the stated family of natural equalities. -/
theorem Entries.checkRange_iff (tree : Entries) (rhs : Nat → Nat) (start count : Nat) :
    tree.checkRange rhs start count = true ↔
      ∀ i < count, tree.lookup (start + i) = rhs (start + i) := by
  simp [Entries.checkRange, List.all_eq_true]

/-- Adjacent checked chunks combine without overlaps, omissions or another arithmetic replay. -/
theorem Entries.checkRange_append (tree : Entries) (rhs : Nat → Nat) (start a b : Nat)
    (ha : tree.checkRange rhs start a = true)
    (hb : tree.checkRange rhs (start + a) b = true) :
    tree.checkRange rhs start (a + b) = true := by
  rw [Entries.checkRange_iff] at ha hb ⊢
  intro i hi
  by_cases hia : i < a
  · exact ha i hia
  · have h := hb (i - a) (by omega)
    have he : start + a + (i - a) = start + i := by omega
    rw [he] at h
    exact h

end WordCertDensity.Certificates
