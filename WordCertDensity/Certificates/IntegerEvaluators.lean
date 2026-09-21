/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.DirectTransfer
import WordCertDensity.Certificates.Rounding

/-! # Finite integer initialization and direct parity ceilings -/

namespace WordCertDensity.Certificates

/-- Clear the binary denominator in the finite cyclic head, including an empty head. -/
theorem binary_head (g : ℕ → ℝ) (T : ℕ) :
    (∑ j ∈ Finset.range T, (2 : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) * g (j + 1)) =
      (∑ j ∈ Finset.range T, (2 : ℝ) ^ (T - 1 - j) * g (j + 1)) / (2 : ℝ) ^ T := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjT : j + 1 ≤ T := by have := Finset.mem_range.mp hj; omega
  rw [show T - 1 - j = T - (j + 1) by omega,
    pow_sub₀ (2 : ℝ) (by norm_num) hjT, zpow_neg, zpow_natCast]
  field_simp

/-- The paid finite binary numerator gives a rounded upper seed for the entire series. -/
theorem integer_cyclic_seed (a : ℕ → ℕ) (A T : ℕ) (ha : ∀ j, a j ≤ A) :
    cyclicSum (fun j => (a j : ℝ)) 0 ≤
      ceilDiv (A + ∑ j ∈ Finset.range T, 2 ^ (T - 1 - j) * a (j + 1)) (2 ^ T) := by
  have ht := cyclicSum_tail_le (g := fun j => (a j : ℝ)) (M := (A : ℝ))
    (fun j => ⟨Nat.cast_nonneg _, by exact_mod_cast ha j⟩) T
  rw [binary_head (fun j => (a j : ℝ)) T, ← add_div] at ht
  have hc := div_le_ceilDiv
    (A + ∑ j ∈ Finset.range T, 2 ^ (T - 1 - j) * a (j + 1)) (2 ^ T)
    (by positivity)
  push_cast at hc
  exact ht.trans (by simpa only [add_comm] using hc)

/-- Multiplying the input scales the exact infinite cyclic sum. -/
theorem cyclicSum_mul (S : ℝ) (g : ℕ → ℝ) (i : ℕ) :
    cyclicSum (fun j => S * g j) i = S * cyclicSum g i := by
  unfold cyclicSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  ring

/-- Scaled true inputs may be replaced by integer upper inputs before rounding the seed. -/
theorem scaled_integer_cyclic_seed (g : ℕ → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hg : ∀ j, 0 ≤ g j) (a : ℕ → ℕ) (A T : ℕ)
    (ha : ∀ j, a j ≤ A) (hupper : ∀ j, S * g j ≤ a j) :
    S * cyclicSum g 0 ≤
      ceilDiv (A + ∑ j ∈ Finset.range T, 2 ^ (T - 1 - j) * a (j + 1)) (2 ^ T) := by
  rw [← cyclicSum_mul]
  exact (cyclicSum_mono_of_bounds (M := (A : ℝ)) (fun j => mul_nonneg hS (hg j))
    (fun j => ⟨Nat.cast_nonneg _, by exact_mod_cast ha j⟩) hupper 0).trans
    (integer_cyclic_seed a A T ha)

/-- The direct evaluator's integer numerator bounds a scaled actual parity series. -/
theorem scaled_integer_direct (g : ℕ → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hg : ∀ j, 0 ≤ g j) (a : ℕ → ℕ) (A e J : ℕ)
    (he : 1 ≤ e) (hJ : 1 ≤ J) (ha : ∀ j, a j ≤ A)
    (hupper : ∀ j, S * g j ≤ a j) :
    S * (3 * (2 : ℝ) ^ (-(e : ℤ)) * ∑' j : ℕ, (4 : ℝ) ^ (-(j : ℤ)) * g j) ≤
      ceilDiv (3 * (∑ j ∈ Finset.range J, 4 ^ (J - 1 - j) * a j) + A)
        (2 ^ (e + 2 * J - 2)) := by
  have ht := direct_bound_of_upper_sequence (fun j => S * g j) (fun j => (a j : ℝ))
    (A : ℝ) e J he hJ (fun j => mul_nonneg hS (hg j))
    (fun j => by exact_mod_cast ha j) hupper
  have hs : (∑' j : ℕ, (4 : ℝ) ^ (-(j : ℤ)) * (S * g j)) =
      S * ∑' j : ℕ, (4 : ℝ) ^ (-(j : ℤ)) * g j := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    ring
  rw [hs] at ht
  have hc := div_le_ceilDiv
    (3 * (∑ j ∈ Finset.range J, 4 ^ (J - 1 - j) * a j) + A)
    (2 ^ (e + 2 * J - 2)) (by positivity)
  push_cast at hc
  simpa only [mul_assoc, mul_left_comm, mul_comm] using ht.trans hc

/-- The integer direct ceiling applies to the actual odd incoming coset. -/
theorem integer_fan_direct_upper (n : ℕ) (S : ℝ) (hS : 0 ≤ S)
    (a : ZMod (3 ^ n) → ℕ) (A J : ℕ) (hJ : 1 ≤ J)
    (ha : ∀ x, a x ≤ A) (hupper : ∀ x, S * Reference.density n x ≤ a x)
    (x : ZMod (3 ^ n)) :
    S * Reference.density (n + 1) (Reference.fanEmbedding n x) ≤
      ceilDiv (3 * (∑ j ∈ Finset.range J, 4 ^ (J - 1 - j) * a (Reference.fanMap n j x))
        + A) (2 ^ (1 + 2 * J - 2)) := by
  rw [density_fan_series]
  exact scaled_integer_direct _ S hS (fun j => Reference.density_nonneg n _)
    _ A 1 J (by decide) hJ (fun j => ha _) (fun j => hupper _)

/-- The same integer direct ceiling applies to the actual even incoming coset. -/
theorem integer_even_direct_upper (n : ℕ) (S : ℝ) (hS : 0 ≤ S)
    (a : ZMod (3 ^ n) → ℕ) (A J : ℕ) (hJ : 1 ≤ J)
    (ha : ∀ x, a x ≤ A) (hupper : ∀ x, S * Reference.density n x ≤ a x)
    (x : ZMod (3 ^ n)) :
    S * Reference.density (n + 1) (Reference.evenEmbedding n x) ≤
      ceilDiv (3 * (∑ j ∈ Finset.range J, 4 ^ (J - 1 - j) * a (Reference.fanMap n j x))
        + A) (2 ^ (2 + 2 * J - 2)) := by
  rw [density_even_series]
  exact scaled_integer_direct _ S hS (fun j => Reference.density_nonneg n _)
    _ A 2 J (by decide) hJ (fun j => ha _) (fun j => hupper _)

/-- The cyclic driver's compatible input, expressed entirely as a natural integer. -/
def integerCycleEntry (n : ℕ) (a : ZMod (3 ^ n) → ℕ) (i : ℕ) : ℕ :=
  let y := (2 : ZMod (3 ^ (n + 1))) ^ i
  if y.val % 3 = 1 then a ((((y.val - 1) / 3 : ℕ) : ZMod (3 ^ n))) else 0

/-- Casting the integer input recovers precisely the real compatibility filter. -/
theorem integerCycleEntry_cast (n : ℕ) (a : ZMod (3 ^ n) → ℕ) (i : ℕ) :
    (integerCycleEntry n a i : ℝ) = cycleEntry n (fun x => (a x : ℝ)) i := by
  dsimp only [integerCycleEntry, cycleEntry, compatibleInput]
  split_ifs <;> simp_all

/-- The previous array maximum bounds every cyclic input, including incompatible zeros. -/
theorem integerCycleEntry_le (n : ℕ) (a : ZMod (3 ^ n) → ℕ) (A : ℕ)
    (ha : ∀ x, a x ≤ A) (i : ℕ) : integerCycleEntry n a i ≤ A := by
  dsimp only [integerCycleEntry]
  split_ifs
  · exact ha _
  · exact Nat.zero_le _

/-- The literal finite seed numerator certifies the actual residue-one density. -/
theorem integer_cyclic_density_seed (n : ℕ) (S : ℝ) (hS : 0 ≤ S)
    (a : ZMod (3 ^ n) → ℕ) (A T : ℕ) (ha : ∀ x, a x ≤ A)
    (hupper : ∀ x, S * Reference.density n x ≤ a x) :
    S * Reference.density (n + 1) 1 ≤
      3 * (ceilDiv (A + ∑ j ∈ Finset.range T,
        2 ^ (T - 1 - j) * integerCycleEntry n a (j + 1)) (2 ^ T) : ℝ) := by
  have hg (i : ℕ) : 0 ≤ cycleEntry n (Reference.density n) i := by
    unfold cycleEntry compatibleInput
    split_ifs
    · exact Reference.density_nonneg n _
    · exact le_refl _
  have hb := scaled_integer_cyclic_seed _ S hS hg (integerCycleEntry n a) A T
    (integerCycleEntry_le n a A ha) (fun i => by
      rw [integerCycleEntry_cast]
      exact scaled_cycleEntry_upper n S a hupper i)
  have ht := cyclic_density_transfer n 0
  simp only [pow_zero] at ht
  rw [ht]
  nlinarith [hb]

/-- Exact upward seed and interior updates suffice for every stored cyclic density value. -/
theorem integer_cyclic_rounded_upper (n : ℕ) (S : ℝ) (hS : 0 ≤ S)
    (a : ZMod (3 ^ n) → ℕ) (A T : ℕ) (ha : ∀ x, a x ≤ A)
    (hupper : ∀ x, S * Reference.density n x ≤ a x) (h : ℕ → ℕ)
    (hzero : h 0 = ceilDiv (A + ∑ j ∈ Finset.range T,
      2 ^ (T - 1 - j) * integerCycleEntry n a (j + 1)) (2 ^ T))
    (hwrap : h (2 * 3 ^ n) = h 0)
    (hstep : ∀ i, 0 < i → i < 2 * 3 ^ n →
      h i = ceilDiv (integerCycleEntry n a (i + 1) + h (i + 1)) 2) :
    ∀ i < 2 * 3 ^ n,
      S * Reference.density (n + 1) ((2 : ZMod (3 ^ (n + 1))) ^ i) ≤ 3 * h i := by
  apply scaled_cyclic_auxiliary_upper n S a hupper h
  · rw [hzero]
    exact integer_cyclic_density_seed n S hS a A T ha hupper
  · exact hwrap
  · intro i hi hip
    rw [hstep i hi hip, ← integerCycleEntry_cast]
    exact_mod_cast le_mul_ceilDiv (integerCycleEntry n a (i + 1) + h (i + 1)) 2
      (by decide)

end WordCertDensity.Certificates
