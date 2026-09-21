/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.Geometry

/-! # Selected triangles at actual black entry states

The existing filled-triangle witness does not expose a white right boundary.
This module supplies the full selected-triangle interface required to freeze
the top at an entry and invoke the original-law white-exit estimate.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- Every primitive black state before the terminal range lies in a selected
triangle with both horizontal boundaries and its full north boundary white. -/
theorem black_point_has_selected_triangle {n j : ℕ} {l : ℤ}
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (hb : phaseBlackAtInt n ξ j l) :
    ∃ a top, isSelectedPhaseTriangle n ξ a top ∧
      inPhaseTriangleIntMul n ξ a top j l := by
  obtain ⟨a, b, top, hpoint, hrightPoint, hrow, hfill, hleft⟩ :=
    black_point_has_full_top_triangle_int hn hj ξ hξ hb
  have hab : a ≤ b := hrightPoint.1
  have hatop := (hrow a le_rfl hab).1
  have hanorth := (hrow a le_rfl hab).2
  have ha : 2 * a < n := by have := hpoint.1; omega
  obtain ⟨c, hac, hcblack, hcrow, hcwhite, _⟩ :=
    exists_black_rightmost_of_primitive_int top hn ha ξ hξ hatop
  have hcnorth : ¬ phaseBlackAtInt n ξ c (top + 1) := by
    intro hc
    have hweak := phaseBlackAtInt_implies_weak n ξ c (top + 1) hc
    have he : a + (c - a) = c := Nat.add_sub_of_le hac
    have hweak' : phaseWeakBlackAtInt n ξ (a + (c - a)) (top + 1) := by
      simpa only [he] using hweak
    have hprop := weakBlack_left_of_east_and_lower_segment n a (c - a) top ξ
      hweak' (fun r hr => hcrow (a + r) (by omega) (by omega))
    exact hanorth (phaseBlackAtInt_of_weak_of_north n a (top + 1) ξ hprop
      (by simpa using hatop))
  have habove := no_black_above_top_segment n a c top ξ hac hcrow hcnorth
  have hctri : inPhaseTriangleIntMul n ξ a top c top := by
    apply canonical_corner_contains_point_int ξ hac le_rfl hcrow
    · intro s hs₀ hs₁
      have : s = top := by omega
      simpa only [this] using hcblack
    · exact hcblack
  exact ⟨a, top, ⟨c, hctri, hcrow, habove, hfill, hcwhite, hleft⟩, hpoint⟩

/-- A selected triangle attached to an actual black state. Its top coordinate
is fixed once this state has been sampled. -/
noncomputable def entryTriangle {n j : ℕ} {l : ℤ}
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (hb : phaseBlackAtInt n ξ j l) :
    {p : ℕ × ℤ // isSelectedPhaseTriangle n ξ p.1 p.2 ∧
      inPhaseTriangleIntMul n ξ p.1 p.2 j l} := by
  have he : ∃ p : ℕ × ℤ, isSelectedPhaseTriangle n ξ p.1 p.2 ∧
      inPhaseTriangleIntMul n ξ p.1 p.2 j l := by
    obtain ⟨a, top, hsel, hpoint⟩ := black_point_has_selected_triangle hn hj ξ hξ hb
    exact ⟨(a, top), hsel, hpoint⟩
  exact ⟨Classical.choose he, Classical.choose_spec he⟩

/-- The chosen entry top is at or above the actual starting height. -/
theorem entryTriangle_height_le {n j : ℕ} {l : ℤ}
    (hn : 0 < n) (hj : 2 * j < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (hb : phaseBlackAtInt n ξ j l) :
    l ≤ (entryTriangle hn hj ξ hξ hb).val.2 :=
  (entryTriangle hn hj ξ hξ hb).property.2.2.1

end WordCertDensity.LocalPrimitive
