/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingGeometry
public import Mathlib.Data.Finset.Max

/-! # Common-height separation and counting actual rectangle anchors -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The common integer row used for all triangles of size at least `u`. -/
noncomputable def longCrossingCommonHeight (top : ℤ) (u : ℕ) : ℤ :=
  top + ⌈(u : ℝ) / (2 * Real.log 2)⌉

private theorem commonHeight_le_top {top b : ℤ} {u : ℕ} {t : ℝ}
    (hsize : (u : ℝ) ≤ t) (hbottom : (top : ℝ) < (b : ℝ) - t / Real.log 2) :
    longCrossingCommonHeight top u ≤ b := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : (u : ℝ) / (2 * Real.log 2) ≤ (u : ℝ) / Real.log 2 := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg u) hlog2
    linarith
  have hdiv := div_le_div_of_nonneg_right hsize hlog2.le
  have hbound : (u : ℝ) / (2 * Real.log 2) ≤ ((b - top : ℤ) : ℝ) := by
    push_cast
    linarith
  have hc := Int.ceil_le.mpr hbound
  unfold longCrossingCommonHeight
  omega

/-- A uniform initial section at the common row belongs to the actual
triangle. A coarse logarithm bound suffices for the required `u/32` spacing. -/
theorem commonHeight_smallSection_mem
    (n : ℕ) (ξ : ZMod (3 ^ n)) (a r u Y : ℕ) (b top : ℤ)
    (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (ha : 2 * a < n)
    (hsize : (u : ℝ) ≤ phaseTriangleLogSize n a b ξ)
    (hbottom : (top : ℝ) < phaseTriangleLowerTip n ξ a b)
    (hupper : phaseTriangleLowerTip n ξ a b ≤ (top : ℝ) + Y)
    (hbudget : 4 * (Y : ℝ) * Real.log 2 ≤ u)
    (har : a ≤ r) (hr : (r : ℝ) - a ≤ (u : ℝ) / 32) :
    inPhaseTriangleIntMul n ξ a b r (longCrossingCommonHeight top u) := by
  let L := longCrossingCommonHeight top u
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hlog9upper : Real.log 9 ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
    linarith
  have hLb : L ≤ b := commonHeight_le_top hsize hbottom
  have hheight : (u : ℝ) / 2 ≤ ((L : ℝ) - top) * Real.log 2 := by
    have hc := Int.le_ceil ((u : ℝ) / (2 * Real.log 2))
    have hm := (div_le_iff₀ (by positivity : 0 < 2 * Real.log 2)).mp hc
    dsimp [L, longCrossingCommonHeight]
    push_cast
    nlinarith
  have hwidth := commonHeight_realSection_lower (u : ℝ) Y L top
    (phaseTriangleLowerTip n ξ a b) hheight hupper hbudget
  have hwidth' : (u : ℝ) / 4 ≤
      ((L : ℝ) - phaseTriangleLowerTip n ξ a b) * Real.log 2 := by
    have hw := (div_le_div_iff₀ (by positivity : 0 < 4 * Real.log 9) hlog9).mp hwidth
    nlinarith
  have hweight : ((r : ℝ) - a) * Real.log 9 ≤ (u : ℝ) / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hr hlog9.le
    have hlog := mul_le_mul_of_nonneg_left hlog9upper (by positivity : 0 ≤ (u : ℝ) / 32)
    nlinarith
  have hid : ((L : ℝ) - phaseTriangleLowerTip n ξ a b) * Real.log 2 =
      phaseTriangleLogSize n a b ξ - ((b : ℝ) - L) * Real.log 2 := by
    unfold phaseTriangleLowerTip
    field_simp [ne_of_gt hlog2]
    ring
  apply (primitive_inPhaseTriangleIntMul_iff_logSize b L ξ hn ha hξ).mpr
  refine ⟨har, hLb, ?_⟩
  have hc : ((b - L).toNat : ℝ) = (b : ℝ) - L := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hLb)
  rw [hc]
  rw [hid] at hwidth'
  linarith

/-- Distinct ordered selected anchors are separated at the common height.
There is no assumption that their full sections fit the anchor interval. -/
theorem commonHeight_selected_anchors_separated
    (n : ℕ) (ξ : ZMod (3 ^ n)) (a c u Y : ℕ) (b d top : ℤ)
    (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (ha : 2 * a < n) (hc : 2 * c < n)
    (hselA : isSelectedPhaseTriangle n ξ a b)
    (hselC : isSelectedPhaseTriangle n ξ c d)
    (hsizeA : (u : ℝ) ≤ phaseTriangleLogSize n a b ξ)
    (hsizeC : (u : ℝ) ≤ phaseTriangleLogSize n c d ξ)
    (hbottomA : (top : ℝ) < phaseTriangleLowerTip n ξ a b)
    (hbottomC : (top : ℝ) < phaseTriangleLowerTip n ξ c d)
    (hupperA : phaseTriangleLowerTip n ξ a b ≤ (top : ℝ) + Y)
    (hupperC : phaseTriangleLowerTip n ξ c d ≤ (top : ℝ) + Y)
    (hbudget : 4 * (Y : ℝ) * Real.log 2 ≤ u) (hac : a < c) :
    (u : ℝ) / 32 ≤ (c : ℝ) - a := by
  by_contra hnot
  have hgap : (c : ℝ) - a ≤ (u : ℝ) / 32 := (lt_of_not_ge hnot).le
  have hAtC := commonHeight_smallSection_mem n ξ a c u Y b top hn hξ ha
    hsizeA hbottomA hupperA hbudget hac.le hgap
  have hAtA := commonHeight_smallSection_mem n ξ a a u Y b top hn hξ ha
    hsizeA hbottomA hupperA hbudget le_rfl (by simp; positivity)
  have hCtC := commonHeight_smallSection_mem n ξ c c u Y d top hn hξ hc
    hsizeC hbottomC hupperC hbudget le_rfl (by simp; positivity)
  have heq := selected_phase_triangles_equal_of_overlap n a c b d ξ
    (c, longCrossingCommonHeight top u) hselA hselC hAtC hCtC
  have hca := ((heq (a, longCrossingCommonHeight top u)).mp hAtA).1
  omega

/-- Ordered separated anchors occupy at least one gap per additional anchor. -/
theorem separatedAnchors_card_mul_le (anchors : Finset ℕ) (lo hi gap : ℝ)
    (hlohi : lo ≤ hi) (hgap : 0 ≤ gap)
    (hlo : ∀ a ∈ anchors, lo ≤ (a : ℝ)) (hhi : ∀ a ∈ anchors, (a : ℝ) ≤ hi)
    (hsep : ∀ a ∈ anchors, ∀ b ∈ anchors, a < b → gap ≤ (b : ℝ) - a) :
    (anchors.card : ℝ) * gap ≤ hi - lo + gap := by
  induction anchors using Finset.induction_on_max generalizing hi with
  | empty => simp; linarith
  | insert a s hmax ih =>
    have haNot : a ∉ s := by
      intro ha
      exact (Nat.lt_irrefl a) (hmax a ha)
    have haLo := hlo a (Finset.mem_insert_self a s)
    have haHi := hhi a (Finset.mem_insert_self a s)
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
      linarith
    · have hbMem := Finset.max'_mem s hs
      have hbLo := hlo (s.max' hs) (Finset.mem_insert_of_mem hbMem)
      have hbound := ih (hi := (s.max' hs : ℝ)) hbLo
        (fun x hx => hlo x (Finset.mem_insert_of_mem hx))
        (fun x hx => by exact_mod_cast Finset.le_max' s x hx)
        (fun x hx y hy hxy => hsep x (Finset.mem_insert_of_mem hx)
          y (Finset.mem_insert_of_mem hy) hxy)
      have hstep := hsep (s.max' hs) (Finset.mem_insert_of_mem hbMem)
        a (Finset.mem_insert_self a s) (hmax _ hbMem)
      rw [Finset.card_insert_of_notMem haNot]
      push_cast
      nlinarith

/-- The actual finite candidate family has the common-height separation. -/
theorem rectangleLargeAnchors_separated
    (n : ℕ) (ξ : ZMod (3 ^ n)) (old lo hi Y u : ℕ) (top : ℤ)
    (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hold : isSelectedPhaseTriangle n ξ old top) (hY : Y ≤ lo)
    (hrow : ∀ r ∈ Finset.Icc (lo - Y) hi, inPhaseTriangleIntMul n ξ old top r top)
    (hbudget : 4 * (Y : ℝ) * Real.log 2 ≤ u) :
    ∀ a ∈ rectangleLargeAnchors n ξ lo hi top Y u,
      ∀ c ∈ rectangleLargeAnchors n ξ lo hi top Y u,
        a < c → (u : ℝ) / 32 ≤ (c : ℝ) - a := by
  classical
  intro a ha c hc hac
  rcases (Finset.mem_filter.mp ha).2 with ⟨b, haN, haSel, haSize, pointA, haRect, haPoint⟩
  rcases (Finset.mem_filter.mp hc).2 with ⟨d, hcN, hcSel, hcSize, pointC, hcRect, hcPoint⟩
  have htipA := rectangle_largeTriangle_lowerTip_bounds n ξ old a pointA.1 lo hi Y
    top b pointA.2 hn hξ haN hold haSel haRect hY hrow haPoint
  have htipC := rectangle_largeTriangle_lowerTip_bounds n ξ old c pointC.1 lo hi Y
    top d pointC.2 hn hξ hcN hold hcSel hcRect hY hrow hcPoint
  exact commonHeight_selected_anchors_separated n ξ a c u Y b d top hn hξ haN hcN
    haSel hcSel haSize hcSize htipA.1 htipC.1 htipA.2 htipC.2 hbudget hac

/-- The actual rectangle anchors satisfy the division-free packing count.
This counts the anchors themselves, not an unproved containing interval for
their potentially longer full horizontal sections. -/
theorem rectangleLargeAnchors_card_mul_le
    (n : ℕ) (ξ : ZMod (3 ^ n)) (old lo hi Y u : ℕ) (top : ℤ)
    (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hold : isSelectedPhaseTriangle n ξ old top) (hY : Y ≤ lo) (hlohi : lo - Y ≤ hi)
    (hrow : ∀ r ∈ Finset.Icc (lo - Y) hi, inPhaseTriangleIntMul n ξ old top r top)
    (hbudget : 4 * (Y : ℝ) * Real.log 2 ≤ u) :
    ((rectangleLargeAnchors n ξ lo hi top Y u).card : ℝ) * u ≤
      32 * ((hi : ℝ) - (lo - Y : ℕ)) + u := by
  classical
  have hsep := rectangleLargeAnchors_separated n ξ old lo hi Y u top hn hξ hold hY hrow hbudget
  have hcount := separatedAnchors_card_mul_le (rectangleLargeAnchors n ξ lo hi top Y u)
    (lo - Y : ℕ) hi ((u : ℝ) / 32) (by exact_mod_cast hlohi) (by positivity)
    (fun a ha => by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1)
    (fun a ha => by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2) hsep
  nlinarith

/-- The printed deterministic bad-column count for the actual rectangle
family. Scalar rectangle budgets are explicit inputs, owned by E-L4.4. -/
theorem rectangle_badColumns_card_le
    (n : ℕ) (ξ : ZMod (3 ^ n)) (old lo hi Y u : ℕ) (top : ℤ) (W : ℝ)
    (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hold : isSelectedPhaseTriangle n ξ old top) (hY : Y ≤ lo) (hlohi : lo - Y ≤ hi)
    (hrow : ∀ r ∈ Finset.Icc (lo - Y) hi, inPhaseTriangleIntMul n ξ old top r top)
    (hbudget : 4 * (Y : ℝ) * Real.log 2 ≤ u) (hu : 0 < u)
    (hYone : 1 ≤ Y) (hWone : 1 ≤ W) (hYW : (Y : ℝ) ≤ W)
    (hdiam : (hi : ℝ) - (lo - Y : ℕ) ≤ 2 * W + Y + 2) :
    ((longCrossingBadColumns (rectangleLargeAnchors n ξ lo hi top Y u) Y).card : ℝ) ≤
      2 * Y + 320 * Y * W / u := by
  let anchors := rectangleLargeAnchors n ξ lo hi top Y u
  let bad := longCrossingBadColumns anchors Y
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hcard : (bad.card : ℝ) ≤ (anchors.card : ℝ) * ((Y : ℝ) + 1) := by
    exact_mod_cast card_longCrossingBadColumns_le anchors Y
  have hpacking := rectangleLargeAnchors_card_mul_le n ξ old lo hi Y u top
    hn hξ hold hY hlohi hrow hbudget
  change (anchors.card : ℝ) * u ≤ 32 * ((hi : ℝ) - (lo - Y : ℕ)) + u at hpacking
  have hD : (hi : ℝ) - (lo - Y : ℕ) ≤ 5 * W := by linarith
  have hYtwo : (Y : ℝ) + 1 ≤ 2 * Y := by exact_mod_cast (show Y + 1 ≤ 2 * Y by omega)
  have hpack : (anchors.card : ℝ) * u ≤ 160 * W + u := by linarith
  have hbound : (bad.card : ℝ) * u ≤ 2 * Y * u + 320 * Y * W := by
    calc
      (bad.card : ℝ) * u ≤ ((anchors.card : ℝ) * ((Y : ℝ) + 1)) * u :=
        mul_le_mul_of_nonneg_right hcard huR.le
      _ = ((anchors.card : ℝ) * u) * ((Y : ℝ) + 1) := by ring
      _ ≤ (160 * W + u) * (2 * Y) :=
        mul_le_mul hpack hYtwo (by positivity) (by linarith)
      _ = _ := by ring
  calc
    (bad.card : ℝ) ≤ (2 * Y * u + 320 * Y * W) / u := (le_div_iff₀ huR).mpr hbound
    _ = 2 * Y + 320 * Y * W / u := by field_simp

end WordCertDensity.LocalPrimitive
