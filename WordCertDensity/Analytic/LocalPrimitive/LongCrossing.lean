/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.WhiteExit

/-!
# Long-crossing packing for Appendix E

The E.5 long-crossing argument first produces a finite, deterministic set of
horizontal columns from the possible left columns of large triangles.  This
module keeps that covering set separate from the random walk, so its later
consumer can use the unconditional passage-index atom bound without
conditioning on a realized vertical coordinate.
-/

@[expose] public section

namespace WordCertDensity
namespace LocalPrimitive

/-- The columns that can be spoiled by a family of left anchors when every
anchor affects its next `Y + 1` lattice columns. -/
def longCrossingBadColumns (anchors : Finset ℕ) (Y : ℕ) : Finset ℕ :=
  anchors.biUnion fun a => Finset.Icc a (a + Y)

/-- Each left anchor affects exactly `Y + 1` columns.  Thus the deterministic
bad-column cover has cardinality at most the number of anchors times that
local multiplicity. -/
theorem card_longCrossingBadColumns_le (anchors : Finset ℕ) (Y : ℕ) :
    (longCrossingBadColumns anchors Y).card ≤ anchors.card * (Y + 1) := by
  unfold longCrossingBadColumns
  calc
    (anchors.biUnion fun a => Finset.Icc a (a + Y)).card ≤
        ∑ a ∈ anchors, (Finset.Icc a (a + Y)).card := Finset.card_biUnion_le
    _ = anchors.card * (Y + 1) := by
      have hcard : ∀ a : ℕ, (Finset.Icc a (a + Y)).card = Y + 1 := by
        intro a
        rw [Nat.card_Icc]
        omega
      simp_rw [hcard]
      simp

/-- The deterministic bad-column count once common-height geometry bounds the
number of possible left anchors. -/
theorem card_longCrossingBadColumns_le_of_anchor_bound
    (anchors : Finset ℕ) (Y Q : ℕ) (hanchors : anchors.card ≤ Q) :
    (longCrossingBadColumns anchors Y).card ≤ Q * (Y + 1) := by
  exact (card_longCrossingBadColumns_le anchors Y).trans
    (Nat.mul_le_mul_right (Y + 1) hanchors)

/-- The real logarithmic size of a phase triangle, measured from its corner.
For primitive nonterminal corners the denominator is positive by E-L2. -/
noncomputable def phaseTriangleLogSize (n j₀ : ℕ) (l₀ : ℤ)
    (ξ : ZMod (3 ^ n)) : ℝ :=
  Real.log (localEpsilon / |balancedPhaseInt n j₀ l₀ ξ|)

/-- The multiplicative phase-triangle predicate is exactly the logarithmic
triangle of `phaseTriangleLogSize` whenever its corner phase is nonzero. -/
theorem inPhaseTriangleIntMul_iff_logSize (n j₀ j : ℕ)
    (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (hcorner : 0 < |balancedPhaseInt n j₀ l₀ ξ|) :
    inPhaseTriangleIntMul n ξ j₀ l₀ j l ↔
      inPhaseTriangleInt j₀ l₀ (phaseTriangleLogSize n j₀ l₀ ξ) j l := by
  simpa [phaseTriangleLogSize] using
    (inPhaseTriangleIntMul_iff_log n ξ j₀ l₀ j l hcorner)

/-- The logarithmic triangle interface for primitive nonterminal corners. -/
theorem primitive_inPhaseTriangleIntMul_iff_logSize {n j₀ j : ℕ}
    (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (hn : 0 < n) (hj₀ : 2 * j₀ < n)
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    inPhaseTriangleIntMul n ξ j₀ l₀ j l ↔
      inPhaseTriangleInt j₀ l₀ (phaseTriangleLogSize n j₀ l₀ ξ) j l := by
  apply inPhaseTriangleIntMul_iff_logSize
  exact abs_balancedPhaseInt_pos_of_primitive l₀ hn hj₀ ξ hξ

/-- A black nonzero corner has nonnegative real triangle size. -/
theorem phaseTriangleLogSize_nonneg (n j₀ : ℕ) (l₀ : ℤ)
    (ξ : ZMod (3 ^ n))
    (hcorner : 0 < |balancedPhaseInt n j₀ l₀ ξ|)
    (hblack : phaseBlackAtInt n ξ j₀ l₀) :
    0 ≤ phaseTriangleLogSize n j₀ l₀ ξ := by
  apply Real.log_nonneg
  apply (le_div_iff₀ hcorner).2
  simpa [phaseBlackAtInt] using hblack

/-- The real common-height section estimate of Appendix E.5.  A height that
has spent at least `u / 2` vertical log-budget above `l₀`, together with a
lower endpoint at most `Y` above `l₀` and `u ≥ 4 Y log 2`, has horizontal
section length at least `u / (4 log 9)`. -/
theorem commonHeight_realSection_lower (u Y L l₀ b : ℝ)
    (hheight : u / 2 ≤ (L - l₀) * Real.log 2)
    (hbottom : b ≤ l₀ + Y)
    (hbudget : 4 * Y * Real.log 2 ≤ u) :
    u / (4 * Real.log 9) ≤ ((L - b) * Real.log 2) / Real.log 9 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * Real.log 9) hlog9).2
  have hmain : u / 4 ≤ (L - b) * Real.log 2 := by
    nlinarith
  nlinarith

/-- The lattice rounding in E.5 loses less than one column.  Hence a real
common-height section longer than `u / 10` has floor length strictly greater
than `u / 12` for the printed guard `u ≥ 64`. -/
theorem commonHeight_floorSection_gt_div_twelve (u : ℕ) (r : ℝ)
    (hu : 64 ≤ u) (hr : (u : ℝ) / 10 < r) :
    (u : ℝ) / 12 < (⌊r⌋₊ : ℕ) := by
  have hfloor : r < (⌊r⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one r
  have hu' : (64 : ℝ) ≤ u := by exact_mod_cast hu
  nlinarith

/-- E-L2 disjointness of full lattice triangles restricts to disjoint finite
horizontal sections at any common integer height. -/
theorem commonHeight_sections_disjoint_of_triangleDisjoint
    (n : ℕ) (ξ : ZMod (3 ^ n)) (ja jb : ℕ) (la lb L : ℤ)
    (A B : Finset ℕ)
    (hA : ∀ r ∈ A, inPhaseTriangleIntMul n ξ ja la r L)
    (hB : ∀ r ∈ B, inPhaseTriangleIntMul n ξ jb lb r L)
    (hdisjoint : Disjoint {q : ℕ × ℤ | inPhaseTriangleIntMul n ξ ja la q.1 q.2}
      {q : ℕ × ℤ | inPhaseTriangleIntMul n ξ jb lb q.1 q.2}) :
    Disjoint A B := by
  rw [Finset.disjoint_left]
  intro r hrA hrB
  have hpA : (r, L) ∈ {q : ℕ × ℤ | inPhaseTriangleIntMul n ξ ja la q.1 q.2} :=
    hA r hrA
  have hpB : (r, L) ∈ {q : ℕ × ℤ | inPhaseTriangleIntMul n ξ jb lb q.1 q.2} :=
    hB r hrB
  exact Set.disjoint_left.mp hdisjoint hpA hpB

/-- The finite horizontal universe in which E.5's possible large-triangle
left anchors lie after the rectangle geometry bounds them by `lo` and `hi`. -/
def longCrossingAnchorUniverse (lo hi : ℕ) : Finset ℕ := Finset.Icc lo hi

/-- Exact cardinality of the finite horizontal anchor universe. -/
theorem card_longCrossingAnchorUniverse (lo hi : ℕ) :
    (longCrossingAnchorUniverse lo hi).card = hi + 1 - lo :=
  Nat.card_Icc lo hi

/-- Any established interval bound places an anchor in the finite candidate
universe, before it is filtered by the large-triangle predicate. -/
theorem mem_longCrossingAnchorUniverse {lo hi a : ℕ}
    (hlo : lo ≤ a) (hhi : a ≤ hi) : a ∈ longCrossingAnchorUniverse lo hi :=
  Finset.mem_Icc.mpr ⟨hlo, hhi⟩

/-- One finite candidate in the E.5 rectangle argument: its left anchor,
triangle corner, and verified finite common-height slice.  Rectangle geometry
will construct these records before the packing argument counts them. -/
structure LongCrossingCandidate (n : ℕ) (ξ : ZMod (3 ^ n)) (L : ℤ) where
  /-- The candidate triangle's leftmost column. -/
  anchor : ℕ
  /-- The candidate triangle's top corner height. -/
  cornerHeight : ℤ
  /-- Its finite horizontal slice at the common height. -/
  slice : Finset ℕ
  slice_mem : ∀ r ∈ slice, inPhaseTriangleIntMul n ξ anchor cornerHeight r L

/-- Membership in a candidate's finite slice gives membership in its actual
E-L2 multiplicative triangle at the common height. -/
theorem LongCrossingCandidate.slice_mem_triangle
    {n : ℕ} {ξ : ZMod (3 ^ n)} {L : ℤ}
    (c : LongCrossingCandidate n ξ L) {r : ℕ} (hr : r ∈ c.slice) :
    inPhaseTriangleIntMul n ξ c.anchor c.cornerHeight r L := c.slice_mem r hr

/-- Appendix E's linear vertical-window parameter. -/
def longCrossingVerticalWindow (A p : ℕ) : ℕ := A * (p + 1)

/-- The vertical window grows linearly by exactly `A` per future pair step. -/
theorem longCrossingVerticalWindow_succ (A p : ℕ) :
    longCrossingVerticalWindow A (p + 1) = longCrossingVerticalWindow A p + A := by
  unfold longCrossingVerticalWindow
  ring

/-- A disjoint family of common-height lattice sections packs into its common
horizontal interval.  The geometric E.5 consumer will instantiate `slice` by
the sections of distinct large phase triangles at the chosen common height. -/
theorem commonHeightPacking_bound {α : Type*}
    (anchors : Finset α) (slice : α → Finset ℕ) (q lo hi : ℕ)
    (hdisjoint : (anchors : Set α).PairwiseDisjoint slice)
    (hcard : ∀ a ∈ anchors, q ≤ (slice a).card)
    (hsubset : ∀ a ∈ anchors, slice a ⊆ Finset.Icc lo hi) :
    anchors.card * q ≤ hi + 1 - lo := by
  calc
    anchors.card * q = ∑ a ∈ anchors, q := by simp [mul_comm]
    _ ≤ ∑ a ∈ anchors, (slice a).card := by
      gcongr with a ha
      exact hcard a ha
    _ = (anchors.biUnion slice).card := (Finset.card_biUnion hdisjoint).symm
    _ ≤ (Finset.Icc lo hi).card := Finset.card_le_card (by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hxa⟩
      exact hsubset a ha hxa)
    _ = hi + 1 - lo := Nat.card_Icc lo hi

/-- Every lattice point of a multiplicative phase triangle supplies the full
horizontal interval from its left corner to that point at the same height.
This is the concrete E-L2 section used in the common-height packing argument. -/
theorem phaseTriangle_commonHeight_interval (n j₀ j : ℕ)
    (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (htri : inPhaseTriangleIntMul n ξ j₀ l₀ j l) :
    ∀ r ∈ Finset.Icc j₀ j, inPhaseTriangleIntMul n ξ j₀ l₀ r l := by
  intro r hr
  exact inPhaseTriangleIntMul_northwest n j₀ j r l₀ l l ξ htri
    (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2 le_rfl htri.2.1

/-- Appendix E's degree-four long-crossing threshold. -/
def longCrossingThreshold (H p : ℕ) : ℕ := H * (p + 1) ^ 4

/-- The degree-four threshold supplies the two quadratic factors used in the
fixed-time bad-column estimate and its summation over times. -/
theorem longCrossingThreshold_factor (H p : ℕ) :
    longCrossingThreshold H p = H * (p + 1) ^ 2 * (p + 1) ^ 2 := by
  unfold longCrossingThreshold
  rw [show 4 = 2 + 2 by omega, pow_add]
  ring

end LocalPrimitive
end WordCertDensity
