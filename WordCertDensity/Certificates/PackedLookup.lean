/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.PackedTree

/-! # Direct packed lookup with an exact decoding equivalence -/

@[expose] public section
namespace WordCertDensity.Certificates.FastPacked

def reverseBits : Nat → Nat → Nat
  | 0, _ => 0
  | d + 1, i => reverseBits d (i / 2) + (i % 2) * 2 ^ d

def directWord (width depth payload i : Nat) : Nat :=
  if i < 2 ^ depth then (payload / 2 ^ (width * reverseBits depth i)) % 2 ^ width else 0

theorem reverseBits_lt (d i : Nat) : reverseBits d i < 2 ^ d := by
  induction d generalizing i with
  | zero => simp [reverseBits]
  | succ d ih =>
    have h := ih (i / 2)
    have hm := Nat.mod_lt i (by decide : 0 < 2)
    simp only [reverseBits, Nat.pow_succ]
    have : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases this with he | he <;> simp only [he, Nat.zero_mul, Nat.one_mul] <;> omega

theorem slice_mod (p h w H : Nat) (hh : h + w ≤ H) :
    (p % 2 ^ H / 2 ^ h) % 2 ^ w = (p / 2 ^ h) % 2 ^ w := by
  have he : 2 ^ H = 2 ^ h * 2 ^ (H - h) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [he, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))

theorem lookup_in_range (w d p i : Nat) (hi : i < 2 ^ d) :
    (packedTree w d p).lookup i = (p / 2 ^ (w * reverseBits d i)) % 2 ^ w := by
  induction d generalizing p i with
  | zero =>
    have : i = 0 := by simpa using hi
    subst i
    simp [packedTree, Entries.lookup, reverseBits]
  | succ d ih =>
    have hhalf : i / 2 < 2 ^ d := by
      rw [Nat.pow_succ] at hi
      omega
    have hr := reverseBits_lt d (i / 2)
    simp only [packedTree, Entries.lookup]
    split
    next he =>
      have hm : i % 2 = 0 := by simpa using he
      rw [ih _ _ hhalf]
      simp only [reverseBits, hm, Nat.zero_mul, Nat.add_zero]
      apply slice_mod
      have := Nat.mul_le_mul_left w (show reverseBits d (i / 2) + 1 ≤ 2 ^ d by omega)
      simpa [Nat.mul_add] using this
    next he =>
      have hm : i % 2 = 1 := by
        have hn : i % 2 ≠ 0 := by simpa using he
        have := Nat.mod_lt i (by decide : 0 < 2)
        omega
      rw [ih _ _ hhalf]
      simp only [reverseBits, hm, Nat.one_mul, Nat.mul_add, Nat.pow_add]
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ (w * 2 ^ d))]

theorem directWord_eq_lookup (w d p i : Nat) :
    directWord w d p i = (packedTree w d p).lookup i := by
  unfold directWord
  split
  next h => exact (lookup_in_range w d p i h).symm
  next h => exact (packedTree_lookup_outside w d p i (by omega)).symm

inductive FastTree where
  | packed (w d p : Nat)
  | node (a b : FastTree)
def FastTree.realize : FastTree → Entries
  | .packed w d p => packedTree w d p
  | .node a b => .node a.realize b.realize
def FastTree.lookup : FastTree → Nat → Nat
  | .packed w d p, i => directWord w d p i
  | .node a b, i => if i % 2 == 0 then a.lookup (i / 2) else b.lookup (i / 2)
theorem FastTree.lookup_eq (t : FastTree) (i : Nat) : t.lookup i = t.realize.lookup i := by
  induction t generalizing i with
  | packed w d p => exact directWord_eq_lookup w d p i
  | node a b ha hb =>
    simp only [FastTree.lookup, FastTree.realize, Entries.lookup]
    split <;> simp_all

end WordCertDensity.Certificates.FastPacked
