/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PassagePotential
import Mathlib.Tactic

/-! # The exact countable first-passage law, with no rescaling of source mass -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The first-passage prefix family has full original mass. -/
theorem passagePrefixFamily_mass_one (s : ℕ) :
    Reference.countableStoppingMass (passagePrefixFamily s) = 1 := by
  rw [Reference.countableStoppingMass_eq_event _ (2 * (s / 2 + 1))
    (passagePrefixFamily_length s) (passagePrefixFamily_prefix_free s)]
  calc
    _ = ∑' w : ValuationWord, Reference.wordPMF (2 * (s / 2 + 1)) w := by
      apply tsum_congr
      intro w
      by_cases hw : w.length = 2 * (s / 2 + 1)
      · obtain ⟨u, hup⟩ := passagePrefixFamily_covers s (s / 2 + 1) le_rfl w hw
        rw [if_pos ⟨u, u.property, hup⟩]
      · rw [Reference.wordPMF_eq_zero_of_length_ne _ _ hw]
        simp
    _ = 1 := PMF.tsum_coe _

/-- The actual stopped law assigns each first-crossing prefix its original
word atom. Its total mass is proved one; no conditioning or rescaling occurs. -/
noncomputable def passagePMF (s : ℕ) : PMF (passagePrefixFamily s) :=
  ⟨fun u => Reference.wordPMF (u : ValuationWord).length u, by
    have hsum : (∑' u : passagePrefixFamily s,
        Reference.wordPMF (u : ValuationWord).length u) = 1 := by
      simp_rw [wordPMF_length_eventMass]
      exact passagePrefixFamily_mass_one s
    rw [← hsum]
    exact ENNReal.summable.hasSum⟩

/-- The exact atom of the stopped law is the original finite-prefix atom. -/
theorem passagePMF_apply (s : ℕ) (u : passagePrefixFamily s) :
    passagePMF s u = Reference.wordPMF (u : ValuationWord).length u := rfl

/-- An event on the stopped prefix has exactly its original common-word
probability at every horizon covering the crossing. -/
theorem passagePMF_probability (s L : ℕ) (hL : s / 2 + 1 ≤ L)
    (B : ValuationWord → Prop) :
    Gated.probability (passagePMF s) (fun u => B u) =
      Gated.probability (Reference.wordPMF (2 * L))
        (fun w => ∃ u : passagePrefixFamily s, (u : ValuationWord) <+: w ∧ B u) := by
  have hlen : ∀ u ∈ passagePrefixFamily s, u.length ≤ 2 * L := by
    intro u hu
    have := passagePrefixFamily_length s u hu
    omega
  have he := countableStoppedTail_factor (passagePrefixFamily s) (2 * L)
    (fun u _ => B u) hlen (passagePrefixFamily_prefix_free s)
  unfold Gated.probability
  congr 1
  rw [he]
  apply tsum_congr
  intro u
  by_cases hu : B u <;> simp [hu, passagePMF_apply, PMF.tsum_coe]

end WordCertDensity.LocalPrimitive
