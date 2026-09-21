/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.DirectEvaluator
import WordCertDensity.Certificates.IntegerEvaluators

/-! # The executable Horner loop equals the exact finite direct sum -/

namespace WordCertDensity.Certificates

/-- The loop state has the full coefficient sum and the specified affine orbit endpoint. -/
theorem directState_eq_sum (previous : Entries) (q J : ℕ) (x : ℕ → ℕ)
    (hx : ∀ j, x (j + 1) = (4 * x j + 1) % q) :
    previous.directState q J (x 0) =
      (∑ j ∈ Finset.range J, 4 ^ (J - 1 - j) * previous.lookup (x j), x J) := by
  induction J with
  | zero => simp [Entries.directState]
  | succ J ih =>
    rw [Entries.directState_succ, ih]
    have hs : (∑ j ∈ Finset.range J, 4 ^ (J - j) * previous.lookup (x j)) =
        4 * ∑ j ∈ Finset.range J, 4 ^ (J - 1 - j) * previous.lookup (x j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have he : J - j = J - 1 - j + 1 := by
        have := Finset.mem_range.mp hj
        omega
      rw [he, pow_succ]
      ring
    simp only [Finset.sum_range_succ, Nat.add_sub_cancel,
      Nat.sub_self, pow_zero, one_mul, hs, hx]

/-- The residue-valued fan iteration has exactly the natural reduced affine update. -/
theorem fanMap_val_step (n j : ℕ) (x : ZMod (3 ^ n)) :
    (Reference.fanMap n (j + 1) x).val =
      (4 * (Reference.fanMap n j x).val + 1) % (3 ^ n) := by
  rw [fanMap_step]
  have hc : (((4 * (Reference.fanMap n j x).val + 1 : ℕ) : ZMod (3 ^ n))) =
      4 * Reference.fanMap n j x + 1 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      ZMod.natCast_zmod_val]
  rw [← hc, ZMod.val_natCast]

/-- The executable accumulated numerator is the manuscript's exact direct finite head. -/
theorem directState_fan_sum (previous : Entries) (n J : ℕ) (x : ZMod (3 ^ n)) :
    (previous.directState (3 ^ n) J x.val).1 =
      ∑ j ∈ Finset.range J, 4 ^ (J - 1 - j) *
        previous.lookup (Reference.fanMap n j x).val := by
  have h := directState_eq_sum previous (3 ^ n) J
    (fun j => (Reference.fanMap n j x).val) (fun j => fanMap_val_step n j x)
  simp only [Reference.fanMap_zero] at h
  exact congrArg Prod.fst h

/-- The executable Horner numerator bounds actual density on the odd incoming coset. -/
theorem directState_fan_upper (previous : Entries) (n A J : ℕ) (hJ : 1 ≤ J)
    (S : ℝ) (hS : 0 ≤ S) (hcap : previous.allLE A = true)
    (hupper : ∀ x : ZMod (3 ^ n), S * Reference.density n x ≤ previous.lookup x.val)
    (x : ZMod (3 ^ n)) :
    S * Reference.density (n + 1) (Reference.fanEmbedding n x) ≤
      (ceilDiv (3 * (previous.directState (3 ^ n) J x.val).1 + A)
        (2 ^ (1 + 2 * J - 2)) : ℝ) := by
  rw [directState_fan_sum]
  exact integer_fan_direct_upper n S hS (fun x => previous.lookup x.val) A J hJ
    (fun x => previous.lookup_le A hcap x.val) hupper x

/-- The executable Horner numerator also bounds actual density on the even incoming coset. -/
theorem directState_even_upper (previous : Entries) (n A J : ℕ) (hJ : 1 ≤ J)
    (S : ℝ) (hS : 0 ≤ S) (hcap : previous.allLE A = true)
    (hupper : ∀ x : ZMod (3 ^ n), S * Reference.density n x ≤ previous.lookup x.val)
    (x : ZMod (3 ^ n)) :
    S * Reference.density (n + 1) (Reference.evenEmbedding n x) ≤
      (ceilDiv (3 * (previous.directState (3 ^ n) J x.val).1 + A)
        (2 ^ (2 + 2 * J - 2)) : ℝ) := by
  rw [directState_fan_sum]
  exact integer_even_direct_upper n S hS (fun x => previous.lookup x.val) A J hJ
    (fun x => previous.lookup_le A hcap x.val) hupper x

end WordCertDensity.Certificates
