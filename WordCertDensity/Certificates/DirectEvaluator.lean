/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.EntryTree

/-! # Core-only executable direct certificate evaluator -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Horner accumulation and the simultaneous reduced affine orbit. -/
def Entries.directState (previous : Entries) (modulus terms x : Nat) : Nat × Nat :=
  (List.range terms).foldl (fun (v : Nat × Nat) _ =>
    (4 * v.1 + previous.lookup v.2, (4 * v.2 + 1) % modulus)) (0, x)

/-- The literal direct evaluator, including nonunit zeros and upward division. -/
def Entries.directEntry (previous : Entries) (cap depth terms y : Nat) : Nat :=
  if y % 3 == 0 then 0 else
    let e := if y % 3 == 2 then 1 else 2
    let q := 3 ^ (depth - 1)
    let x := ((2 ^ e * y - 1) / 3) % q
    let state := previous.directState q terms x
    (3 * state.1 + cap + 2 ^ (e + 2 * terms - 2) - 1) / 2 ^ (e + 2 * terms - 2)

/-- Appending one loop iteration is exactly one affine/Horner update. -/
theorem Entries.directState_succ (previous : Entries) (modulus terms x : Nat) :
    previous.directState modulus (terms + 1) x =
      (4 * (previous.directState modulus terms x).1 +
        previous.lookup (previous.directState modulus terms x).2,
        (4 * (previous.directState modulus terms x).2 + 1) % modulus) := by
  simp [Entries.directState, List.range_succ, List.foldl_append]

end WordCertDensity.Certificates
