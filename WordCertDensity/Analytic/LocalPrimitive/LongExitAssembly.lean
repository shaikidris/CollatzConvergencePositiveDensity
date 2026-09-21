/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.LongExitBound
public import WordCertDensity.Analytic.LocalPrimitive.LongExitGeometry
import Mathlib.Tactic

/-! # Selected-triangle long-exit assembly -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped ENNReal

/-- A selected long triangle supplies the exact original-law expectation and
terminal-tail witnesses required by the long field of `LayerEstimates`. This
is an assembly result: the geometric, post-exit, and terminal producers remain
separate and every layer guard remains an explicit premise. -/
theorem selected_triangle_long_exit_estimate {n a j : ℕ}
    (ξ : ZMod (3 ^ n)) (top l : ℤ) (B L : ℕ) (D : ℝ)
    (hn : 0 < n) (ha : 2 * a < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hsel : isSelectedPhaseTriangle n ξ a top)
    (hstart : inPhaseTriangleIntMul n ξ a top j l) (hB : 0 < B)
    (hjm : j + (n / 2 - j) = n / 2) (hm : localPrimitiveM B ≤ n / 2 - j)
    (hmL : n / 2 - j ≤ L)
    (hlong : ((n / 2 - j : ℕ) : ℝ) / (localPrimitiveEtaDenom B : ℝ) <
      (top - l).toNat)
    (hL : (top - l).toNat / 2 + 1 + localPrimitiveP B ≤ L)
    (hfuture : ∀ r, r < n / 2 - j → ∀ l',
      layerWeight B r * phaseRemainingPotential n ξ (n / 2) r l' ≤ D) :
    ∃ e t : ℝ, 0 ≤ e ∧ 0 ≤ t ∧
      layerWeight B (n / 2 - j) * phaseRemainingPotential n ξ (n / 2)
          (n / 2 - j) l ≤ D * (10 : ℝ) ^ B * e + layerWeight B (n / 2 - j) * t ∧
      e ≤ 1 / (4 * (10 : ℝ) ^ B) ∧ t ≤ Real.exp (-((n / 2 - j : ℕ) : ℝ) / 640) := by
  let s := (top - l).toNat
  let m := n / 2 - j
  let e := (postPassageProductMoment n ξ s j l B L
    (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))).toReal
  let t := Gated.probability (Reference.wordPMF (2 * L))
    (terminalPassageEvent s m (localPrimitiveP B))
  have hmpos : 0 < m := lt_of_lt_of_le (localPrimitiveM_pos B) hm
  have hs : 0 < s := by
    by_contra hnot
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hnot
    have hnonneg : 0 ≤ (m : ℝ) / (localPrimitiveEtaDenom B : ℝ) := by positivity
    have hlong' : (m : ℝ) / (localPrimitiveEtaDenom B : ℝ) < (s : ℝ) := by
      simpa only [m, s] using hlong
    rw [hs0] at hlong'
    norm_num at hlong'
    exact (not_lt_of_ge hnonneg hlong').elim
  refine ⟨e, t, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · have hpass := phaseRemainingPotential_passage_long_le (n := n) (m := m)
      (s := s) (j := j) (L := L) (B := B) ξ l D hjm hmpos (by simpa only [m] using hmL)
        hL hfuture
    have hw : 0 < layerWeight B m := layerWeight_pos B m
    calc
      layerWeight B m * phaseRemainingPotential n ξ (n / 2) m l ≤
          layerWeight B m *
            ((D * (10 : ℝ) ^ B / layerWeight B m) * e + t) :=
        mul_le_mul_of_nonneg_left hpass hw.le
      _ = D * (10 : ℝ) ^ B * e + layerWeight B m * t := by
        field_simp
  · exact selected_triangle_long_postexit hn ha ξ hξ top l hsel hstart B L hB hm
      (by simpa only [m, s] using hlong) (by simpa only [s] using hL)
  · exact terminal_recipe_probability_le s m B L hs hm
      (by simpa only [m, s] using
        selected_triangle_depth_size hn ha ξ hξ top l hsel hstart)
      (by omega)

end WordCertDensity.LocalPrimitive
