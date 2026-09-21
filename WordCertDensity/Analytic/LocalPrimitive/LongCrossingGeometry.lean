/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingLaw

/-!
# Actual rectangle-meeting triangles

The finite anchor family is filtered by witnesses in the original selected
phase triangles. It is independent of any random word or realized height.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- An integer rectangle lying strictly above the old triangle's top. -/
def inLongCrossingRectangle (lo hi : ℕ) (top : ℤ) (Y : ℕ) (point : ℕ × ℤ) : Prop :=
  lo ≤ point.1 ∧ point.1 ≤ hi ∧ top < point.2 ∧ point.2 ≤ top + Y

private theorem triangle_height_cast {b y : ℤ} (h : y ≤ b) :
    ((b - y).toNat : ℝ) = (b : ℝ) - y := by
  have hc : ((b - y).toNat : ℤ) = b - y := Int.toNat_of_nonneg (sub_nonneg.mpr h)
  exact_mod_cast hc

/-- A numerical horizontal budget produces the required old top-row segment
from the actual starting point; no top-row geometry is assumed as an axiom. -/
theorem rectangle_oldTop_contains
    (n : ℕ) (ξ : ZMod (3 ^ n)) (old j lo hi Y : ℕ) (top l : ℤ)
    (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (hold : 2 * old < n)
    (hstart : inPhaseTriangleIntMul n ξ old top j l) (hlo : old ≤ lo - Y)
    (hmargin : ((hi : ℝ) - j) * Real.log 9 ≤ ((top - l).toNat : ℝ) * Real.log 2) :
    ∀ r ∈ Finset.Icc (lo - Y) hi, inPhaseTriangleIntMul n ξ old top r top := by
  intro r hr
  have hrBounds := Finset.mem_Icc.mp hr
  have hlog := (primitive_inPhaseTriangleIntMul_iff_logSize top l ξ hn hold hξ).mp hstart
  apply (primitive_inPhaseTriangleIntMul_iff_logSize top top ξ hn hold hξ).mpr
  refine ⟨hlo.trans hrBounds.1, le_rfl, ?_⟩
  have hrHi : (r : ℝ) ≤ hi := by exact_mod_cast hrBounds.2
  have hstep := mul_le_mul_of_nonneg_right (sub_le_sub_right hrHi (j : ℝ))
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 9))
  have hw := hlog.2.2
  simp only [sub_self, Int.toNat_zero, Nat.cast_zero, zero_mul, add_zero]
  linarith

/-- Moving left by `Y` permits moving down by at most `Y` in a logarithmic
triangle. The natural subtraction is guarded explicitly. -/
theorem phaseTriangle_left_down_window {a x Y : ℕ} {b y top : ℤ} {t : ℝ}
    (htri : inPhaseTriangleInt a b t x y)
    (hY : Y ≤ x) (ha : a ≤ x - Y) (htop : top ≤ y) (hy : y ≤ top + Y) :
    inPhaseTriangleInt a b t (x - Y) top := by
  have htopb : top ≤ b := htop.trans htri.2.1
  refine ⟨ha, htopb, ?_⟩
  have hweight := htri.2.2
  rw [triangle_height_cast htri.2.1] at hweight
  rw [triangle_height_cast htopb, Nat.cast_sub hY]
  have hy' : (y : ℝ) ≤ (top : ℝ) + Y := by exact_mod_cast hy
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogs : Real.log 2 ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
  have hY' : (0 : ℝ) ≤ Y := Nat.cast_nonneg Y
  nlinarith

/-- A rectangle point of another selected triangle forces its anchor into
the next `Y` columns. The overlap contradiction uses actual lattice sets. -/
theorem rectangle_largeTriangle_anchor_bounds
    (n : ℕ) (ξ : ZMod (3 ^ n)) (old a x lo hi Y : ℕ) (top b y : ℤ)
    (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (ha : 2 * a < n)
    (hold : isSelectedPhaseTriangle n ξ old top)
    (hnew : isSelectedPhaseTriangle n ξ a b)
    (hrect : inLongCrossingRectangle lo hi top Y (x, y))
    (hY : Y ≤ lo)
    (hrow : ∀ r ∈ Finset.Icc (lo - Y) hi, inPhaseTriangleIntMul n ξ old top r top)
    (hpoint : inPhaseTriangleIntMul n ξ a b x y) :
    x - Y < a ∧ a ≤ x := by
  have hxY : Y ≤ x := hY.trans hrect.1
  have hdis := selected_phase_triangles_disjoint_of_not_equal n old a top b ξ hold hnew
    (by
      intro heq
      have hbad := (heq (x, y)).mpr hpoint
      have := hbad.2.1
      have := hrect.2.2.1
      omega)
  refine ⟨?_, hpoint.1⟩
  by_contra hnot
  have hax : a ≤ x - Y := by omega
  have hlog := (primitive_inPhaseTriangleIntMul_iff_logSize b y ξ hn ha hξ).mp hpoint
  have hdown := phaseTriangle_left_down_window hlog hxY hax hrect.2.2.1.le hrect.2.2.2
  have hnewDown := (primitive_inPhaseTriangleIntMul_iff_logSize b top ξ hn ha hξ).mpr hdown
  have hmem : x - Y ∈ Finset.Icc (lo - Y) hi :=
    Finset.mem_Icc.mpr ⟨Nat.sub_le_sub_right hrect.1 Y, (Nat.sub_le x Y).trans hrect.2.1⟩
  have hpOld : (x - Y, top) ∈
      {q : ℕ × ℤ | inPhaseTriangleIntMul n ξ old top q.1 q.2} := hrow (x - Y) hmem
  have hpNew : (x - Y, top) ∈
      {q : ℕ × ℤ | inPhaseTriangleIntMul n ξ a b q.1 q.2} := hnewDown
  exact Set.disjoint_left.mp hdis hpOld hpNew

/-- The real lower tip at a selected triangle's left column. -/
noncomputable def phaseTriangleLowerTip (n : ℕ) (ξ : ZMod (3 ^ n))
    (a : ℕ) (b : ℤ) : ℝ :=
  b - phaseTriangleLogSize n a b ξ / Real.log 2

/-- The real lower tip of any rectangle-meeting selected triangle lies
strictly above the old top and below the rectangle's upper edge. -/
theorem rectangle_largeTriangle_lowerTip_bounds
    (n : ℕ) (ξ : ZMod (3 ^ n)) (old a x lo hi Y : ℕ) (top b y : ℤ)
    (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (ha : 2 * a < n)
    (hold : isSelectedPhaseTriangle n ξ old top)
    (hnew : isSelectedPhaseTriangle n ξ a b)
    (hrect : inLongCrossingRectangle lo hi top Y (x, y)) (hY : Y ≤ lo)
    (hrow : ∀ r ∈ Finset.Icc (lo - Y) hi, inPhaseTriangleIntMul n ξ old top r top)
    (hpoint : inPhaseTriangleIntMul n ξ a b x y) :
    (top : ℝ) < phaseTriangleLowerTip n ξ a b ∧
      phaseTriangleLowerTip n ξ a b ≤ (top : ℝ) + Y := by
  have hab := rectangle_largeTriangle_anchor_bounds n ξ old a x lo hi Y
    top b y hn hξ ha hold hnew hrect hY hrow hpoint
  have hlog := (primitive_inPhaseTriangleIntMul_iff_logSize b y ξ hn ha hξ).mp hpoint
  have hweight := hlog.2.2
  rw [triangle_height_cast hlog.2.1] at hweight
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hax : (a : ℝ) ≤ x := by exact_mod_cast hpoint.1
  have hhorizontal := mul_nonneg (sub_nonneg.mpr hax) hlog9.le
  have hvert : ((b : ℝ) - y) * Real.log 2 ≤ phaseTriangleLogSize n a b ξ := by
    linarith
  have htip_y : phaseTriangleLowerTip n ξ a b ≤ y := by
    have hd := (le_div_iff₀ hlog2).mpr hvert
    dsimp [phaseTriangleLowerTip]
    linarith
  refine ⟨?_, htip_y.trans (by exact_mod_cast hrect.2.2.2)⟩
  by_contra hnot
  have htip : phaseTriangleLowerTip n ξ a b ≤ top := le_of_not_gt hnot
  have htopb : top ≤ b := hrect.2.2.1.le.trans hpoint.2.1
  have hnewTop : inPhaseTriangleIntMul n ξ a b a top := by
    apply (primitive_inPhaseTriangleIntMul_iff_logSize b top ξ hn ha hξ).mpr
    refine ⟨le_rfl, htopb, ?_⟩
    rw [triangle_height_cast htopb]
    have hd : (b : ℝ) - top ≤ phaseTriangleLogSize n a b ξ / Real.log 2 := by
      dsimp [phaseTriangleLowerTip] at htip
      linarith
    have hm := (le_div_iff₀ hlog2).mp hd
    simpa using hm
  have haRow : a ∈ Finset.Icc (lo - Y) hi := by
    have hlo := Nat.sub_le_sub_right hrect.1 Y
    exact Finset.mem_Icc.mpr ⟨by omega, hab.2.trans hrect.2.1⟩
  have heq := selected_phase_triangles_equal_of_overlap n old a top b ξ (a, top)
    hold hnew (hrow a haRow) hnewTop
  have hbad := (heq (x, y)).mpr hpoint
  have := hbad.2.1
  have := hrect.2.2.1
  omega

/-- The finite deterministic anchor family, selected by actual large-triangle
and rectangle witnesses. No sampled vertical coordinate occurs in it. -/
noncomputable def rectangleLargeAnchors (n : ℕ) (ξ : ZMod (3 ^ n))
    (lo hi : ℕ) (top : ℤ) (Y u : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (lo - Y) hi).filter fun a =>
    ∃ b, 2 * a < n ∧ isSelectedPhaseTriangle n ξ a b ∧
      (u : ℝ) ≤ phaseTriangleLogSize n a b ξ ∧
      ∃ point, inLongCrossingRectangle lo hi top Y point ∧
        inPhaseTriangleIntMul n ξ a b point.1 point.2

/-- Every large-triangle point in the entire rectangle is covered by the
deterministic bad-column set. This is the event-containment producer for E-L4.5. -/
theorem rectangle_largeTriangle_badColumn_cover
    (n : ℕ) (ξ : ZMod (3 ^ n)) (old lo hi Y u : ℕ) (top : ℤ)
    (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hold : isSelectedPhaseTriangle n ξ old top) (hY : Y ≤ lo)
    (hrow : ∀ r ∈ Finset.Icc (lo - Y) hi, inPhaseTriangleIntMul n ξ old top r top)
    (point : ℕ × ℤ) (hrect : inLongCrossingRectangle lo hi top Y point)
    (hlarge : inLargeSelectedTriangle n ξ u point) :
    point.1 ∈ longCrossingBadColumns (rectangleLargeAnchors n ξ lo hi top Y u) Y := by
  classical
  rcases hlarge with ⟨a, b, ha, hnew, hsize, hpoint⟩
  have hab := rectangle_largeTriangle_anchor_bounds n ξ old a point.1 lo hi Y
    top b point.2 hn hξ ha hold hnew hrect hY hrow hpoint
  have haMem : a ∈ rectangleLargeAnchors n ξ lo hi top Y u := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, hab.2.trans hrect.2.1⟩,
      ⟨b, ha, hnew, hsize, point, hrect, hpoint⟩⟩
    have hlow := Nat.sub_le_sub_right hrect.1 Y
    omega
  apply Finset.mem_biUnion.mpr
  refine ⟨a, haMem, Finset.mem_Icc.mpr ⟨hab.2, ?_⟩⟩
  have hxY := hY.trans hrect.1
  omega

end WordCertDensity.LocalPrimitive
