/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.EntryTree

/-! # Core integer summaries with stable interfaces -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Complete integer energy numerator. -/
def Entries.energySum (z : Entries) (n : Nat) : Nat :=
  ((List.range n).map (fun i => z.lookup i ^ 2)).sum

/-- Complete integer fractional numerator from square enclosures. -/
def Entries.fractionalSum (z r : Entries) (n : Nat) : Nat :=
  ((List.range n).map (fun i => z.lookup i * r.lookup i)).sum

end WordCertDensity.Certificates
