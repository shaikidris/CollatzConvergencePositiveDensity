/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.Data.LevelThree
import WordCertDensity.Certificates.DirectEntrySoundness
import WordCertDensity.Certificates.TableSoundness

/-! # The first complete new maximum, energy and fractional table row -/

namespace WordCertDensity.Certificates

/-- Natural list summaries cover the complete residue group with its original normalization. -/
theorem sum_zmod_succ_list (n : ℕ) (f : ℕ → ℕ) :
    (∑ x : ZMod (n + 1), f x.val) = ((List.range (n + 1)).map f).sum := by
  change (∑ x : Fin (n + 1), f x.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  have hr : (List.range (n + 1)).toFinset = Finset.range (n + 1) := by
    ext i
    simp
  simpa only [hr] using List.sum_toFinset f (List.nodup_range (n := n + 1))

/-- At even binary precision the fractional ceiling is a natural rational comparison. -/
theorem integer_fractional_even_certificate (d k p q : ℕ) (hq : 0 < q)
    (z r : ZMod (3 ^ d) → ℕ)
    (hz : ∀ x, (2 : ℝ) ^ (2 * k) * Reference.density d x ≤ z x)
    (hr : ∀ x, z x ≤ r x ^ 2)
    (hs : q * (∑ x, z x * r x) ≤ p * 3 ^ d * 2 ^ (3 * k)) :
    Reference.moment (3 / 2) d ≤ (p : ℝ) / q := by
  have h := integerFractionalCertificate d (2 * k) z r hz hr
  have he : (3 / 2 : ℝ) * (2 * k : ℕ) = ((3 * k : ℕ) : ℝ) := by
    push_cast
    ring
  rw [he, Real.rpow_natCast] at h
  apply h.trans
  apply (div_le_div_iff₀ (by positivity : 0 < (3 : ℝ) ^ d * 2 ^ (3 * k))
    (by exact_mod_cast hq : (0 : ℝ) < q)).mpr
  have hc : (q : ℝ) * (∑ x, (z x : ℝ) * r x) ≤
      (p : ℝ) * (3 : ℝ) ^ d * 2 ^ (3 * k) := by exact_mod_cast hs
  nlinarith [hc]

/-- The complete stored level-three tree bounds the actual reference density. -/
theorem levelThree_upper (x : ZMod (3 ^ 3)) :
    (2 : ℝ) ^ 48 * Reference.density 3 x ≤ levelThree.lookup x.val := by
  exact checked_direct_upper seedTwo48 levelThree 2 884635641090634 16 (by decide)
    ((2 : ℝ) ^ 48) (by positivity) seedTwo48_cap seedTwo48_upper levelThree_transfer x

/-- The retained level-three maximum inequality concerns the actual law. -/
theorem maximum_three : Reference.maximum 3 ≤ 24 / 5 := by
  apply integer_maximum_certificate 3 (2 ^ 48) 24 5 (by positivity) (by decide)
    (fun x => levelThree.lookup x.val)
  · intro x
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using levelThree_upper x
  · intro x
    exact (Nat.mul_le_mul_left 5 (levelThree.lookup_le _ levelThree_cap x.val)).trans
      levelThree_max_comparison

/-- The retained level-three second-moment inequality uses every residue. -/
theorem energy_three : Reference.moment 2 3 ≤ 521 / 200 := by
  apply integer_energy_certificate 3 (2 ^ 48) 521 200 (by positivity) (by decide)
    (fun x => levelThree.lookup x.val)
  · intro x
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using levelThree_upper x
  · change 200 * (∑ x : ZMod (26 + 1), levelThree.lookup x.val ^ 2) ≤ _
    rw [sum_zmod_succ_list 26 (fun i => levelThree.lookup i ^ 2)]
    exact levelThree_energy_comparison

/-- Direct integer square enclosures prove the retained level-three fractional row. -/
theorem fractional_three : Reference.moment (3 / 2) 3 ≤ 769803 / 500000 := by
  apply integer_fractional_even_certificate 3 24 769803 500000 (by decide)
    (fun x => levelThree.lookup x.val) (fun x => levelThreeRoots.lookup x.val)
  · exact levelThree_upper
  · intro x
    exact levelThree_square_enclosures x
  · change 500000 * (∑ x : ZMod (26 + 1),
      levelThree.lookup x.val * levelThreeRoots.lookup x.val) ≤ _
    rw [sum_zmod_succ_list 26 (fun i => levelThree.lookup i * levelThreeRoots.lookup i)]
    exact levelThree_fractional_comparison

end WordCertDensity.Certificates
