/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.CyclicUpper
public import WordCertDensity.Reference.Moments

/-! # Integer upward division and scaled cyclic propagation -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- The natural-number expression used by the certificate drivers for upward division. -/
def ceilDiv (a d : ℕ) : ℕ := (a + d - 1) / d

/-- Upward division bounds the numerator for every positive denominator. -/
theorem le_mul_ceilDiv (a d : ℕ) (hd : 0 < d) : a ≤ d * ceilDiv a d := by
  have hm := Nat.mod_lt (a + d - 1) hd
  have he := Nat.mod_add_div (a + d - 1) d
  unfold ceilDiv
  omega

/-- Integer upward division is also a sound upper bound on the real quotient. -/
theorem div_le_ceilDiv (a d : ℕ) (hd : 0 < d) :
    (a : ℝ) / d ≤ ceilDiv a d := by
  apply (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  have h := le_mul_ceilDiv a d hd
  have hr : (a : ℝ) ≤ (d : ℝ) * ceilDiv a d := by exact_mod_cast h
  simpa only [mul_comm] using hr

/-- Upward binary updates dominate the scaled recurrence, with its factor three retained. -/
theorem rounded_cyclic_step (a z : ℕ) :
    3 * (a : ℝ) + z ≤ 2 * (ceilDiv (3 * a + z) 2 : ℝ) := by
  exact_mod_cast le_mul_ceilDiv (3 * a + z) 2 (by decide)

/-- A scaled input upper bound is preserved by the compatibility filter on the full cycle. -/
theorem scaled_cycleEntry_upper (n : ℕ) (S : ℝ) (a : ZMod (3 ^ n) → ℕ)
    (ha : ∀ x, S * Reference.density n x ≤ a x) (i : ℕ) :
    S * cycleEntry n (Reference.density n) i ≤
      cycleEntry n (fun x => (a x : ℝ)) i := by
  unfold cycleEntry compatibleInput
  split_ifs
  · exact ha _
  · simp only [mul_zero, le_refl]

/-- Scaled backward updates certify actual density at every position of a complete cycle.
The seed is retained at zero, and the wrap is copied from it before interior updates. -/
theorem scaled_cyclic_density_upper (n : ℕ) (S : ℝ)
    (a : ZMod (3 ^ n) → ℕ) (ha : ∀ x, S * Reference.density n x ≤ a x)
    (z : ℕ → ℕ)
    (hseed : S * Reference.density (n + 1) 1 ≤ z 0)
    (hwrap : z (2 * 3 ^ n) = z 0)
    (hstep : ∀ i, 0 < i → i < 2 * 3 ^ n →
      3 * cycleEntry n (fun x => (a x : ℝ)) (i + 1) + z (i + 1) ≤ 2 * z i) :
    ∀ i < 2 * 3 ^ n,
      S * Reference.density (n + 1) ((2 : ZMod (3 ^ (n + 1))) ^ i) ≤ z i := by
  let g := cycleEntry n (Reference.density n)
  have hg : ∀ j, 0 ≤ g j ∧ g j ≤ Reference.maximum n :=
    cycleEntry_bounds n _ _ (fun x =>
      ⟨Reference.density_nonneg n x, Reference.density_le_maximum n x⟩)
  have hrec (i : ℕ) :
      3 * S * cyclicSum g i = (3 * S * g (i + 1) + 3 * S * cyclicSum g (i + 1)) / 2 := by
    rw [cyclicSum_recurrence hg]
    ring
  have hs : 3 * S * cyclicSum g 0 ≤ z 0 := by
    have ht := cyclic_density_transfer n 0
    simp only [pow_zero] at ht
    rw [ht] at hseed
    dsimp [g]
    nlinarith [hseed]
  have hn : 3 * S * cyclicSum g (2 * 3 ^ n) ≤ z (2 * 3 ^ n) := by
    have hp := cyclicSum_periodic (cycleEntry_periodic n (Reference.density n)) 0
    simp only [Nat.zero_add] at hp
    change cyclicSum g (2 * 3 ^ n) = cyclicSum g 0 at hp
    rw [hp, hwrap]
    exact hs
  have hp : 0 < 2 * 3 ^ n := by positivity
  have hb := cyclicUpperInduction (fun i => 3 * S * cyclicSum g (i + 1))
    (fun i => 3 * S * g (i + 1)) (fun i => z (i + 1)) (2 * 3 ^ n - 1)
    (fun i _ => hrec (i + 1))
    (by simpa only [show 2 * 3 ^ n - 1 + 1 = 2 * 3 ^ n by omega] using hn)
    (by
      intro i hi
      have hu := scaled_cycleEntry_upper n S a ha (i + 1 + 1)
      have ht := hstep (i + 1) (by omega) (by omega)
      change S * g (i + 1 + 1) ≤ _ at hu
      nlinarith)
  intro i hi
  have ht := cyclic_density_transfer n i
  rw [ht]
  by_cases hi0 : i = 0
  · subst i
    dsimp [g] at hs
    nlinarith [hs]
  · have hh := hb (i - 1) (by omega)
    simp only [Nat.sub_add_cancel (by omega : 1 ≤ i)] at hh
    dsimp [g] at hh
    nlinarith [hh]

/-- The retained driver rounds auxiliary values and stores three times each value. -/
theorem scaled_cyclic_auxiliary_upper (n : ℕ) (S : ℝ)
    (a : ZMod (3 ^ n) → ℕ) (ha : ∀ x, S * Reference.density n x ≤ a x)
    (h : ℕ → ℕ) (hseed : S * Reference.density (n + 1) 1 ≤ 3 * h 0)
    (hwrap : h (2 * 3 ^ n) = h 0)
    (hstep : ∀ i, 0 < i → i < 2 * 3 ^ n →
      cycleEntry n (fun x => (a x : ℝ)) (i + 1) + h (i + 1) ≤ 2 * h i) :
    ∀ i < 2 * 3 ^ n,
      S * Reference.density (n + 1) ((2 : ZMod (3 ^ (n + 1))) ^ i) ≤ 3 * h i := by
  have hb := scaled_cyclic_density_upper n S a ha (fun i => 3 * h i)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hseed)
    (by rw [hwrap]) (by
      intro i hi hip
      have ht := hstep i hi hip
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      linarith)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hb

end WordCertDensity.Certificates
