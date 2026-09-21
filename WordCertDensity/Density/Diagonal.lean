/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Density.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith

/-! # Diagonalization preserving a common lower natural density -/

namespace WordCertDensity

open Filter
open scoped Topology

/-- Decreasing sets with a common density bound admit a slowly advancing diagonal with that bound. -/
theorem lowerNaturalDensity_diagonal (A : ℕ → Set ℕ) (d : ℝ)
    (hA : Antitone A) (hd : ∀ j, d ≤ lowerNaturalDensity (A j)) :
    ∃ k : ℕ → ℕ, Monotone k ∧ Tendsto k atTop atTop ∧
      d ≤ lowerNaturalDensity {x | x ∈ A (k x)} := by
  classical
  have hcut (j : ℕ) : ∃ X : ℕ, ∀ N ≥ X,
      d-1/((j : ℝ)+1) ≤ partialDensity (A j) N := by
    apply eventually_atTop.1
    apply (le_lowerNaturalDensity_iff (A j) d).1 (hd j)
    have hp : (0 : ℝ) < 1/((j : ℝ)+1) := by positivity
    linarith
  choose X hX using hcut
  let k : ℕ → ℕ := fun N => Nat.findGreatest (fun j => X j ≤ N) N
  have hkmono : Monotone k := by
    intro M N hMN
    exact Nat.findGreatest_mono (fun _ h => h.trans hMN) hMN
  have hktend : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro j
    exact eventually_atTop.2 ⟨max j (X j), fun N hN =>
      Nat.le_findGreatest ((le_max_left _ _).trans hN) ((le_max_right _ _).trans hN)⟩
  have hspec (N : ℕ) (hN : X 0 ≤ N) : X (k N) ≤ N :=
    Nat.findGreatest_spec (P := fun j => X j ≤ N) (Nat.zero_le N) hN
  have hcount (N : ℕ) : prefixCount (A (k N)) N ≤ prefixCount {x | x ∈ A (k x)} N := by
    unfold prefixCount
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hx ⊢
    exact ⟨hx.1, hA (hkmono hx.1.2) hx.2⟩
  have hdensity (N : ℕ) :
      partialDensity (A (k N)) N ≤ partialDensity {x | x ∈ A (k x)} N := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    exact_mod_cast hcount N
  have hlim : Tendsto (fun N => d-1/((k N : ℝ)+1)) atTop (𝓝 d) := by
    simpa using (tendsto_const_nhds (x := d)).sub
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hktend)
  refine ⟨k, hkmono, hktend, (le_lowerNaturalDensity_iff _ d).2 ?_⟩
  intro e he
  filter_upwards [hlim.eventually (Ioi_mem_nhds he), eventually_ge_atTop (X 0)] with N heN hN
  exact heN.le.trans ((hX (k N) N (hspec N hN)).trans (hdensity N))

end WordCertDensity
