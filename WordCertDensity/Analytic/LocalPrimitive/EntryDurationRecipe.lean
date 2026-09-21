/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryDurationRecurrence
public import WordCertDensity.Analytic.LocalPrimitive.Parameters
import Mathlib.Tactic

/-! # The fixed manuscript recipe in the deterministic entry recurrence -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The fixed quartic crossing threshold is monotone. -/
theorem localPrimitiveThreshold_monotone (B : ℕ) :
    Monotone (fun p : ℕ => localPrimitiveH B * (p + 1) ^ 4) := by
  intro a b hab
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hab 1) 4)

/-- The recipe's entry cutoffs are monotone. -/
theorem localPrimitiveV_monotone (B : ℕ) : Monotone (localPrimitiveV B) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [localPrimitiveV]
  omega

/-- Outside large entered triangles, the fixed recipe forces the R-th entry
before P whenever fewer than K white states occur. -/
theorem recipe_entry_of_shortage_small_triangles {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (j : ℕ) (l : ℤ) (w : ValuationWord) (B : ℕ)
    (hsample : 2 * localPrimitiveP B ≤ w.length)
    (hshort : sampledWhiteStateCount n ξ j l w (localPrimitiveP B) < localPrimitiveK B)
    (hsmall : ∀ s, s < localPrimitiveP B → entryWordBlack n ξ j l w s →
      phaseTriangleLogSize n (entryWordTriangle hn ξ hξ j l w s).1
        (entryWordTriangle hn ξ hξ j l w s).2 ξ <
          (localPrimitiveH B * (s + 1) ^ 4 : ℕ)) :
    ∃ s, s < localPrimitiveP B ∧
      wordBlackEntryTime hn ξ hξ j l w (localPrimitiveR B - 1) = some s := by
  have he := entries_of_shortage_small_triangles hn ξ hξ j l w
    (localPrimitiveK B) (localPrimitiveP B) (localPrimitiveR B)
    (fun p => localPrimitiveH B * (p + 1) ^ 4) (localPrimitiveV B)
    (localPrimitiveThreshold_monotone B) (localPrimitiveV_monotone B) rfl
    (fun _ => rfl) (by unfold localPrimitiveP; omega) hsample hshort hsmall
  obtain ⟨s, hs, hentry⟩ := he (localPrimitiveR B - 1) (by omega)
  have hv := localPrimitiveV_monotone B (show localPrimitiveR B - 1 ≤ localPrimitiveR B by omega)
  refine ⟨s, ?_, hentry⟩
  unfold localPrimitiveP
  omega

end WordCertDensity.LocalPrimitive
