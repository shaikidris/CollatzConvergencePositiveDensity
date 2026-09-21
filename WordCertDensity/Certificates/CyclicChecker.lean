/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.EntryTree

/-! # Local integer checks for binary supersolutions -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Compatible input after doubling, using only natural representatives. -/
def Entries.cyclicInput (previous : Entries) (depth y : Nat) : Nat :=
  let t := (2 * y) % 3 ^ depth
  if t % 3 = 1 then previous.lookup (((t - 1) / 3) % 3 ^ (depth - 1)) else 0

/-- Check every local supersolution inequality on the specified interval. -/
def Entries.cyclicCheck (previous current : Entries) (depth start count : Nat) : Bool :=
  (List.range count).all fun i =>
    decide (3 * previous.cyclicInput depth (start + i) +
      current.lookup ((2 * (start + i)) % 3 ^ depth) ≤ 2 * current.lookup (start + i))

/-- The Boolean check is exactly the finite family of integer inequalities. -/
theorem Entries.cyclicCheck_iff (previous current : Entries) (depth start count : Nat) :
    previous.cyclicCheck current depth start count = true ↔
      ∀ i < count, 3 * previous.cyclicInput depth (start + i) +
        current.lookup ((2 * (start + i)) % 3 ^ depth) ≤ 2 * current.lookup (start + i) := by
  simp [Entries.cyclicCheck, List.all_eq_true]

/-- Adjacent certificates assemble without re-evaluating their local inequalities. -/
theorem Entries.cyclicCheck_append (previous current : Entries) (depth start a b : Nat)
    (ha : previous.cyclicCheck current depth start a = true)
    (hb : previous.cyclicCheck current depth (start + a) b = true) :
    previous.cyclicCheck current depth start (a + b) = true := by
  rw [Entries.cyclicCheck_iff] at ha hb ⊢
  intro i hi
  by_cases hia : i < a
  · exact ha i hia
  · have h := hb (i - a) (by omega)
    have he : start + a + (i - a) = start + i := by omega
    rw [he] at h
    exact h

/-- A Boolean cap check keeps finite data out of dependent function elaboration. -/
def Entries.capCheck (current : Entries) (cap start count : Nat) : Bool :=
  (List.range count).all fun i => decide (current.lookup (start + i) ≤ cap)

/-- The cap check is exactly the corresponding pointwise bound. -/
theorem Entries.capCheck_iff (current : Entries) (cap start count : Nat) :
    current.capCheck cap start count = true ↔
      ∀ i < count, current.lookup (start + i) ≤ cap := by
  simp [Entries.capCheck, List.all_eq_true]

/-- Adjacent cap checks give a complete cap check. -/
theorem Entries.capCheck_append (current : Entries) (cap start a b : Nat)
    (ha : current.capCheck cap start a = true)
    (hb : current.capCheck cap (start + a) b = true) :
    current.capCheck cap start (a + b) = true := by
  rw [Entries.capCheck_iff] at ha hb ⊢
  intro i hi
  by_cases hia : i < a
  · exact ha i hia
  · have h := hb (i - a) (by omega)
    have he : start + a + (i - a) = start + i := by omega
    rw [he] at h
    exact h

end WordCertDensity.Certificates
