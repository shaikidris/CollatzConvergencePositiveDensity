/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.CyclicUpper
import WordCertDensity.Reference.Moments

/-! # Finite supersolutions for the actual binary density recurrence -/

namespace WordCertDensity.Certificates

/-- A supersolution dominates a finite binary recurrence, without a chosen seed. -/
theorem finite_binary_supersolution {α : Type*} [Fintype α] (next : α → α)
    (f g z : α → ℝ) (hrec : ∀ x, 2 * f x = g x + f (next x))
    (hbound : ∀ x, g x + z (next x) ≤ 2 * z x) : ∀ x, f x ≤ z x := by
  classical
  intro x
  letI : Nonempty α := ⟨x⟩
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun y => f y - z y) Finset.univ_nonempty
  have hn := hm (next m) (Finset.mem_univ _)
  have hx := hm x (Finset.mem_univ _)
  nlinarith [hrec m, hbound m]

/-- The actual density obeys one exact binary update at every ternary unit. -/
theorem density_binary_update (n : ℕ) (u : (ZMod (3 ^ (n + 1)))ˣ) :
    2 * Reference.density (n + 1) (u : ZMod (3 ^ (n + 1))) =
      3 * compatibleInput n (Reference.density n) (2 * (u : ZMod (3 ^ (n + 1)))) +
        Reference.density (n + 1) (2 * (u : ZMod (3 ^ (n + 1)))) := by
  obtain ⟨i, hi⟩ := (unitCycle_bijective n).surjective u
  have hu : (2 : ZMod (3 ^ (n + 1))) ^ (i : ℕ) = u := by
    rw [← unitCycle_val, hi]
  have hv : (2 : ZMod (3 ^ (n + 1))) ^ ((i : ℕ) + 1) = 2 * u := by
    rw [pow_succ (2 : ZMod (3 ^ (n + 1))) (i : ℕ), hu, mul_comm]
  have h0 := cyclic_density_transfer n (i : ℕ)
  have h1 := cyclic_density_transfer n ((i : ℕ) + 1)
  have hr := cyclicSum_recurrence (cycleEntry_bounds n (Reference.density n)
    (Reference.maximum n) (fun x =>
      ⟨Reference.density_nonneg n x, Reference.density_le_maximum n x⟩)) (i : ℕ)
  rw [hu] at h0
  rw [hv] at h1
  have hg : cycleEntry n (Reference.density n) ((i : ℕ) + 1) =
      compatibleInput n (Reference.density n) (2 * u) := by
    unfold cycleEntry
    rw [hv]
  rw [hg] at hr
  nlinarith

/-- Integer supersolutions bound the actual next density at every unit. -/
theorem integer_cyclic_supersolution_units (n : ℕ) (S : ℝ)
    (a : ZMod (3 ^ n) → ℕ)
    (ha : ∀ x, S * Reference.density n x ≤ a x)
    (z : ZMod (3 ^ (n + 1)) → ℕ)
    (hstep : ∀ u : (ZMod (3 ^ (n + 1)))ˣ,
      3 * compatibleInput n (fun x => (a x : ℝ)) (2 * (u : ZMod (3 ^ (n + 1)))) +
        z (2 * (u : ZMod (3 ^ (n + 1)))) ≤ 2 * z u)
    (u : (ZMod (3 ^ (n + 1)))ˣ) :
    S * Reference.density (n + 1) (u : ZMod (3 ^ (n + 1))) ≤ z u := by
  apply finite_binary_supersolution
    (fun v => Reference.twoUnit (n + 1) * v)
    (fun v : (ZMod (3 ^ (n + 1)))ˣ => S * Reference.density (n + 1) v)
    (fun v => 3 * S * compatibleInput n (Reference.density n)
      (2 * (v : ZMod (3 ^ (n + 1)))))
    (fun v => (z (v : ZMod (3 ^ (n + 1))) : ℝ)) ?_ ?_ u
  · intro v
    simp only [Units.val_mul, Reference.twoUnit_val]
    have h := congrArg (fun t : ℝ => S * t) (density_binary_update n v)
    nlinarith [h]
  · intro v
    simp only [Units.val_mul, Reference.twoUnit_val]
    have h : S * compatibleInput n (Reference.density n)
        (2 * (v : ZMod (3 ^ (n + 1)))) ≤
        compatibleInput n (fun x => (a x : ℝ)) (2 * (v : ZMod (3 ^ (n + 1)))) := by
      unfold compatibleInput
      split_ifs
      · exact ha _
      · simp only [mul_zero, le_refl]
    nlinarith [h, hstep v]

/-- A complete local inequality certificate also covers the zero-density nonunits. -/
theorem integer_cyclic_supersolution (n : ℕ) (S : ℝ)
    (a : ZMod (3 ^ n) → ℕ)
    (ha : ∀ x, S * Reference.density n x ≤ a x)
    (z : ZMod (3 ^ (n + 1)) → ℕ)
    (hstep : ∀ u : (ZMod (3 ^ (n + 1)))ˣ,
      3 * compatibleInput n (fun x => (a x : ℝ)) (2 * (u : ZMod (3 ^ (n + 1)))) +
        z (2 * (u : ZMod (3 ^ (n + 1)))) ≤ 2 * z u)
    (y : ZMod (3 ^ (n + 1))) :
    S * Reference.density (n + 1) y ≤ z y := by
  by_cases hy : IsUnit y
  · obtain ⟨u, rfl⟩ := hy
    exact integer_cyclic_supersolution_units n S a ha z hstep u
  · rw [Reference.density_eq_zero_of_not_isUnit (by omega) y hy, mul_zero]
    exact Nat.cast_nonneg _

end WordCertDensity.Certificates
