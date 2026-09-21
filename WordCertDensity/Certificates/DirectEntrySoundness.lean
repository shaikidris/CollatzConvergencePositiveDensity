/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.DirectEvaluatorSemantics
import WordCertDensity.Certificates.SeedTwo

/-! # Incoming selection and checked-tree transfer for the actual reference density -/

namespace WordCertDensity.Certificates

/-- Residue representatives determine the literal level-one projection. -/
theorem project_one_of_val_mod (n : ℕ) (y : ZMod (3 ^ (n + 1))) (r : ℕ)
    (hr : r < 3) (hy : y.val % 3 = r) :
    Reference.project (show 1 ≤ n + 1 by omega) y = (r : ZMod (3 ^ 1)) := by
  rw [← ZMod.natCast_zmod_val y, Reference.project_natCast]
  apply (ZMod.natCast_eq_natCast_iff y.val r 3).mpr
  exact hy.trans (Nat.mod_eq_of_lt hr).symm

/-- The executable odd selector starts at the exact fan predecessor. -/
theorem directEntry_fan (previous : Entries) (n A J : ℕ) (x : ZMod (3 ^ n)) :
    previous.directEntry A (n + 1) J (Reference.fanEmbedding n x).val =
      ceilDiv (3 * (previous.directState (3 ^ n) J x.val).1 + A)
        (2 ^ (1 + 2 * J - 2)) := by
  have hi : Reference.transferInput n (Reference.fanEmbedding n x) 1 = x := by
    simpa [Reference.oddLetter] using Reference.transferInput_fanEmbedding n 0 x
  have hq := congrArg ZMod.val hi
  rw [Reference.transferInput, ZMod.val_natCast] at hq
  norm_num only [pow_one] at hq
  simp [Entries.directEntry, Reference.fanEmbedding_val_mod, ceilDiv, hq]

/-- The executable even selector starts at the exact even-coset predecessor. -/
theorem directEntry_even (previous : Entries) (n A J : ℕ) (x : ZMod (3 ^ n)) :
    previous.directEntry A (n + 1) J (Reference.evenEmbedding n x).val =
      ceilDiv (3 * (previous.directState (3 ^ n) J x.val).1 + A)
        (2 ^ (2 + 2 * J - 2)) := by
  have hi : Reference.transferInput n (Reference.evenEmbedding n x) 2 = x := by
    simpa [Reference.evenLetter] using Reference.transferInput_evenEmbedding n 0 x
  have hq := congrArg ZMod.val hi
  rw [Reference.transferInput, ZMod.val_natCast] at hq
  norm_num only [Nat.reducePow] at hq
  simp [Entries.directEntry, Reference.evenEmbedding_val_mod, ceilDiv, hq]

/-- Every executable entry bounds the actual next density, including nonunit zeros. -/
theorem directEntry_upper (previous : Entries) (n A J : ℕ) (hJ : 1 ≤ J)
    (S : ℝ) (hS : 0 ≤ S) (hcap : previous.allLE A = true)
    (hupper : ∀ x : ZMod (3 ^ n), S * Reference.density n x ≤ previous.lookup x.val)
    (y : ZMod (3 ^ (n + 1))) :
    S * Reference.density (n + 1) y ≤ previous.directEntry A (n + 1) J y.val := by
  by_cases hy0 : y.val % 3 = 0
  · have hp := project_one_of_val_mod n y 0 (by decide) hy0
    rw [Reference.density_zero_coset n y hp]
    simp [Entries.directEntry, hy0]
  · have hlt : y.val % 3 < 3 := Nat.mod_lt _ (by decide)
    have hc : y.val % 3 = 1 ∨ y.val % 3 = 2 := by omega
    rcases hc with hy1 | hy2
    · have hm : y ∈ Finset.univ.image (Reference.evenEmbedding n) := by
        rw [Reference.image_evenEmbedding]
        exact (Reference.mem_fiber _ _ _).mpr
          (project_one_of_val_mod n y 1 (by decide) hy1)
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hm
      rw [directEntry_even]
      exact directState_even_upper previous n A J hJ S hS hcap hupper x
    · have hm : y ∈ Finset.univ.image (Reference.fanEmbedding n) := by
        rw [Reference.image_fanEmbedding]
        exact (Reference.mem_fiber _ _ _).mpr
          (project_one_of_val_mod n y 2 (by decide) hy2)
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hm
      rw [directEntry_fan]
      exact directState_fan_upper previous n A J hJ S hS hcap hupper x

/-- A complete kernel-checked range transports an actual upper tree to the next level. -/
theorem checked_direct_upper (previous current : Entries) (n A J : ℕ) (hJ : 1 ≤ J)
    (S : ℝ) (hS : 0 ≤ S) (hcap : previous.allLE A = true)
    (hupper : ∀ x : ZMod (3 ^ n), S * Reference.density n x ≤ previous.lookup x.val)
    (hcheck : current.checkRange (previous.directEntry A (n + 1) J) 0 (3 ^ (n + 1)) = true)
    (y : ZMod (3 ^ (n + 1))) :
    S * Reference.density (n + 1) y ≤ current.lookup y.val := by
  have hc := (Entries.checkRange_iff _ _ _ _).mp hcheck y.val (ZMod.val_lt y)
  simp only [Nat.zero_add] at hc
  rw [hc]
  exact directEntry_upper previous n A J hJ S hS hcap hupper y

/-- The literal starting tree bounds the complete actual depth-two reference law. -/
theorem seedTwo48_upper (x : ZMod (3 ^ 2)) :
    (2 : ℝ) ^ 48 * Reference.density 2 x ≤ seedTwo48.lookup x.val := by
  rw [Reference.density_two_vector]
  have h (i : Fin 9) :
      (2 : ℝ) ^ 48 *
        (([0, 8/7, 16/7, 0, 11/7, 4/7, 0, 2/7, 22/7] : List ℝ)[i.val]?.getD 0) ≤
          seedTwo48.lookup i.val := by
    fin_cases i <;> norm_num [seedTwo48, Entries.lookup]
  exact h x

end WordCertDensity.Certificates
