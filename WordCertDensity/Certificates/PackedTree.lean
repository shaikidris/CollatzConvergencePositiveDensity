/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.EntryTree

/-! # Packed natural payloads decoded through the existing lookup interface -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Decode fixed-width words in tree leaf order; higher unused bits are ignored. -/
def packedTree (width : Nat) : Nat → Nat → Entries
  | 0, payload => .leaf (payload % 2 ^ width)
  | depth + 1, payload =>
    .node (packedTree width depth (payload % 2 ^ (width * 2 ^ depth)))
      (packedTree width depth (payload / 2 ^ (width * 2 ^ depth)))

/-- The decoder has exactly the specified power-of-two leaf count. -/
theorem packedTree_size (width depth payload : Nat) :
    (packedTree width depth payload).size = 2 ^ depth := by
  induction depth generalizing payload with
  | zero => rfl
  | succ depth ih => simp [packedTree, Entries.size, ih, Nat.pow_succ, Nat.mul_two]

/-- Every decoded word fits its specified bit width, including width zero. -/
theorem packedTree_allLE (width depth payload : Nat) :
    (packedTree width depth payload).allLE (2 ^ width - 1) = true := by
  induction depth generalizing payload with
  | zero =>
    have h := Nat.mod_lt payload (Nat.two_pow_pos width)
    have hb : payload % 2 ^ width ≤ 2 ^ width - 1 := by omega
    simpa [packedTree, Entries.allLE] using hb
  | succ depth ih => simp [packedTree, Entries.allLE, ih]

/-- Decoded lookup values satisfy the width bound at every index. -/
theorem packedTree_lookup_le (width depth payload i : Nat) :
    (packedTree width depth payload).lookup i ≤ 2 ^ width - 1 :=
  Entries.lookup_le _ _ (packedTree_allLE width depth payload) i

/-- Indices outside the decoded block read as zero. -/
theorem packedTree_lookup_outside (width depth payload i : Nat) (hi : 2 ^ depth ≤ i) :
    (packedTree width depth payload).lookup i = 0 := by
  induction depth generalizing payload i with
  | zero =>
    simp only [packedTree, Entries.lookup]
    split <;> simp_all
  | succ depth ih =>
    have hh : 2 ^ depth ≤ i / 2 := by
      rw [Nat.pow_succ] at hi
      omega
    simp only [packedTree, Entries.lookup]
    split <;> exact ih _ _ hh

/-- A zero-width block has only zero lookup values. -/
theorem packedTree_zero_width (depth payload i : Nat) :
    (packedTree 0 depth payload).lookup i = 0 := by
  have h := packedTree_lookup_le 0 depth payload i
  simpa using Nat.eq_zero_of_le_zero h

end WordCertDensity.Certificates
