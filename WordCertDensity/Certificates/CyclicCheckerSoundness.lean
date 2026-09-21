/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.CyclicChecker
import WordCertDensity.Certificates.CyclicSupersolution

/-! # Checked local supersolutions bound the full actual reference law -/

namespace WordCertDensity.Certificates

/-- Natural modular doubling is the actual doubled residue representative. -/
theorem cyclic_double_val (n : ℕ) (y : ZMod (3 ^ (n + 1))) :
    (2 * y).val = (2 * y.val) % 3 ^ (n + 1) := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using
    (ZMod.val_natCast (3 ^ (n + 1)) (2 * y.val))

/-- The integer selector is exactly the compatible actual-law input. -/
theorem cyclicInput_cast (previous : Entries) (n : ℕ) (y : ZMod (3 ^ (n + 1))) :
    (previous.cyclicInput (n + 1) y.val : ℝ) =
      compatibleInput n (fun x => (previous.lookup x.val : ℝ)) (2 * y) := by
  simp only [Entries.cyclicInput, Nat.add_sub_cancel, compatibleInput,
    cyclic_double_val, ZMod.val_natCast]
  split_ifs <;> simp only [Nat.cast_zero]

/-- A complete checked range transports an actual upper tree to the next level. -/
theorem checked_cyclic_upper (previous current : Entries) (n : ℕ) (S : ℝ)
    (hupper : ∀ x : ZMod (3 ^ n), S * Reference.density n x ≤ previous.lookup x.val)
    (hcheck : previous.cyclicCheck current (n + 1) 0 (3 ^ (n + 1)) = true)
    (y : ZMod (3 ^ (n + 1))) :
    S * Reference.density (n + 1) y ≤ current.lookup y.val := by
  apply integer_cyclic_supersolution n S (fun x => previous.lookup x.val) hupper
    (fun x => current.lookup x.val) ?_ y
  intro u
  have h := (Entries.cyclicCheck_iff previous current (n + 1) 0 (3 ^ (n + 1))).mp
    hcheck (u : ZMod (3 ^ (n + 1))).val (ZMod.val_lt _)
  simp only [Nat.zero_add] at h
  have hr : 3 * (previous.cyclicInput (n + 1) (u : ZMod (3 ^ (n + 1))).val : ℝ) +
      current.lookup ((2 * (u : ZMod (3 ^ (n + 1))).val) % 3 ^ (n + 1)) ≤
        2 * (current.lookup (u : ZMod (3 ^ (n + 1))).val : ℝ) := by
    exact_mod_cast h
  rw [cyclicInput_cast, ← cyclic_double_val] at hr
  exact hr

end WordCertDensity.Certificates
