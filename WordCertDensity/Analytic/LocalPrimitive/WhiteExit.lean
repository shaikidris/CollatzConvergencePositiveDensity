/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.FirstPassage
public import WordCertDensity.Analytic.LocalPrimitive.Geometry

/-! # Deterministic white exits from Appendix E first passage -/

@[expose] public section

namespace WordCertDensity
namespace LocalPrimitive

/-- The Appendix E first-passage exit coordinate over an integer top height. -/
def firstPassageExitPoint (j : ℕ) (l₀ : ℤ) (J H : ℕ) : ℕ × ℤ :=
  (j + J, l₀ + H)

/-- A bounded first-passage exit is white once its coordinate lies outside,
but within the verified collar of, a selected triangle. -/
theorem selected_triangle_firstPassageExit_white
    (n j₀ : ℕ) (l₀ : ℤ) (ξ : ZMod (3 ^ n))
    (hsel : isSelectedPhaseTriangle n ξ j₀ l₀)
    (j J H : ℕ)
    (hout : ¬ inPhaseTriangleIntMul n ξ j₀ l₀
      (firstPassageExitPoint j l₀ J H).1 (firstPassageExitPoint j l₀ J H).2)
    (hnear : withinPhaseTriangleCollarInt n ξ j₀ l₀ (firstPassageExitPoint j l₀ J H)) :
    ¬ phaseBlackAtInt n ξ (j + J) (l₀ + H) := by
  rcases hsel with ⟨j₁, htriRight, hrow, habove, hfill, hright, hleft⟩
  simpa [firstPassageExitPoint] using
    selected_triangle_collar_white n j₀ j₁ (j + J) l₀ (l₀ + H) ξ
      htriRight hrow habove hfill hright hleft hout hnear

/-- A strict positive overshoot puts the exit strictly above the triangle's
top row, hence outside its literal triangle. -/
theorem firstPassageExit_not_in_triangle_of_pos
    (n j₀ j J H : ℕ) (l₀ : ℤ) (ξ : ZMod (3 ^ n)) (hH : 0 < H) :
    ¬ inPhaseTriangleIntMul n ξ j₀ l₀
      (firstPassageExitPoint j l₀ J H).1 (firstPassageExitPoint j l₀ J H).2 := by
  intro htri
  rcases htri with ⟨_, hrow, _⟩
  simp [firstPassageExitPoint] at hrow
  have hH' : (0 : ℤ) < H := by exact_mod_cast hH
  omega

/-- A collar-contained strict first-passage exit is white. -/
theorem selected_triangle_firstPassageExit_white_of_pos
    (n j₀ : ℕ) (l₀ : ℤ) (ξ : ZMod (3 ^ n))
    (hsel : isSelectedPhaseTriangle n ξ j₀ l₀)
    (j J H : ℕ) (hH : 0 < H)
    (hnear : withinPhaseTriangleCollarInt n ξ j₀ l₀
      (firstPassageExitPoint j l₀ J H)) :
    ¬ phaseBlackAtInt n ξ (j + J) (l₀ + H) := by
  apply selected_triangle_firstPassageExit_white n j₀ l₀ ξ hsel j J H
  · exact firstPassageExit_not_in_triangle_of_pos n j₀ j J H l₀ ξ hH
  · exact hnear

/-- The original-word first-passage event supplies the strictness required by
the deterministic collar white-exit consumer. -/
theorem selected_triangle_firstPassageExit_white_of_event
    (n j₀ : ℕ) (l₀ : ℤ) (ξ : ZMod (3 ^ n))
    (hsel : isSelectedPhaseTriangle n ξ j₀ l₀)
    (j s J H : ℕ) {w : ValuationWord}
    (hpass : pairFirstPassageEvent s J H w)
    (hnear : withinPhaseTriangleCollarInt n ξ j₀ l₀
      (firstPassageExitPoint j l₀ J H)) :
    ¬ phaseBlackAtInt n ξ (j + J) (l₀ + H) := by
  exact selected_triangle_firstPassageExit_white_of_pos n j₀ l₀ ξ hsel j J H
    hpass.2.1 hnear

/-- Under the nonexceptional Appendix E index bound and `H ≤ 8`, a
first-passage exit lies in the literal collar of its selected triangle. -/
theorem firstPassageExit_within_collar
    (n j₀ j J H s : ℕ) (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (hsel : isSelectedPhaseTriangle n ξ j₀ l₀)
    (hstart : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (hs : (l₀ - l).toNat = s)
    (hJ : J ≤ 5 * (s / 16) + 9)
    (hH : H ≤ 8) :
    withinPhaseTriangleCollarInt n ξ j₀ l₀ (firstPassageExitPoint j l₀ J H) := by
  rcases hsel with ⟨j₁, htriRight, hrow, habove, hfill, hright, hleft⟩
  let r := j + 5 * (s / 16)
  have htop : inPhaseTriangleIntMul n ξ j₀ l₀ r l₀ := by
    dsimp [r]
    exact inPhaseTriangleIntMul_top_five_div_sixteen n j₀ j s l₀ l ξ hstart hs
  have hr : r ≤ j₁ :=
    triangle_top_le_rightmost n j₀ j₁ r l₀ ξ htriRight hfill hright htop
  let qj := min (j + J) j₁
  have hj₀j : j₀ ≤ j := hstart.1
  have hj₀q : j₀ ≤ qj := by
    dsimp [qj]
    exact le_min (by omega) htriRight.1
  have hqj : qj ≤ j₁ := by exact min_le_right _ _
  have hqtri : inPhaseTriangleIntMul n ξ j₀ l₀ qj l₀ :=
    inPhaseTriangleIntMul_northwest n j₀ j₁ qj l₀ l₀ l₀ ξ htriRight hj₀q hqj le_rfl le_rfl
  refine ⟨(qj, l₀), hqtri, ?_⟩
  unfold withinPhaseCollarInt latticeDistSqInt firstPassageExitPoint
  have hrightBound : j + J ≤ j₁ + 9 := by
    dsimp [r] at hr
    omega
  have hdist : Nat.dist (j + J) qj ≤ 9 := by
    dsimp [qj]
    by_cases hle : j + J ≤ j₁
    · rw [min_eq_left hle, Nat.dist_self]
      omega
    · have hge : j₁ ≤ j + J := by omega
      rw [min_eq_right hge, Nat.dist_comm, Nat.dist_eq_sub_of_le hge]
      omega
  have hheight : ((l₀ + H) - l₀).natAbs ≤ 8 := by
    have heq : l₀ + (H : ℤ) - l₀ = (H : ℤ) := by ring
    simpa [heq] using hH
  change Nat.dist (j + J) qj ^ 2 + ((l₀ + (H : ℤ)) - l₀).natAbs ^ 2 ≤ 16 ^ 2
  calc
    Nat.dist (j + J) qj ^ 2 + ((l₀ + (H : ℤ)) - l₀).natAbs ^ 2 ≤ 9 ^ 2 + 8 ^ 2 :=
      Nat.add_le_add (Nat.pow_le_pow_left hdist 2) (Nat.pow_le_pow_left hheight 2)
    _ ≤ 16 ^ 2 := by norm_num

/-- The controlled first-passage column stays strictly before the original
terminal column.  This uses the sixteen-column primitive triangle margin. -/
theorem firstPassageExit_before_terminal
    (n j₀ j J s : ℕ) (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (hsel : isSelectedPhaseTriangle n ξ j₀ l₀)
    (hstart : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (hs : (l₀ - l).toNat = s)
    (hJ : J ≤ 5 * (s / 16) + 9)
    (hn : 0 < n) (hj₀ : 2 * j₀ < n)
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    j + J < n / 2 := by
  rcases hsel with ⟨j₁, htriRight, hrow, habove, hfill, hright, hleft⟩
  let r := j + 5 * (s / 16)
  have htop : inPhaseTriangleIntMul n ξ j₀ l₀ r l₀ := by
    dsimp [r]
    exact inPhaseTriangleIntMul_top_five_div_sixteen n j₀ j s l₀ l ξ hstart hs
  have hr : r ≤ j₁ :=
    triangle_top_le_rightmost n j₀ j₁ r l₀ ξ htriRight hfill hright htop
  have hrightBound : j + J ≤ j₁ + 9 := by
    dsimp [r] at hr
    omega
  have hj₁ : 2 * (j₁ + 17) < n :=
    triangle_column_before_terminal l₀ l₀ ξ hn hj₀ hξ htriRight
  omega

/-- The geometric Appendix E bounds give a white strict first-passage exit. -/
theorem selected_triangle_firstPassageExit_white_of_bounds
    (n j₀ j J H s : ℕ) (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (hsel : isSelectedPhaseTriangle n ξ j₀ l₀)
    (hstart : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (hs : (l₀ - l).toNat = s)
    (hJ : J ≤ 5 * (s / 16) + 9)
    (hH : H ≤ 8) (hHpos : 0 < H) :
    ¬ phaseBlackAtInt n ξ (j + J) (l₀ + H) := by
  exact selected_triangle_firstPassageExit_white_of_pos n j₀ l₀ ξ hsel j J H hHpos
    (firstPassageExit_within_collar n j₀ j J H s l₀ l ξ hsel hstart hs hJ hH)

/-- A concrete common-horizon word which avoids both Appendix E exceptional
events has a white strict-passage exit. -/
theorem selected_triangle_horizonGoodExit_white
    (n j₀ j s : ℕ) (i : Fin (s / 2 + 1)) (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (w : ValuationWord)
    (hsel : isSelectedPhaseTriangle n ξ j₀ l₀)
    (hstart : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (hs : (l₀ - l).toNat = s)
    (hpass : horizonTailEvent s 0 i w)
    (hhigh : ¬ stoppedPassageIndexHighEvent s w)
    (htail : ¬ stoppedTailEvent s 8 w) :
    ¬ phaseBlackAtInt n ξ (j + ((i : ℕ) + 1))
      (l₀ + ((ValuationWord.total (w.take (2 * ((i : ℕ) + 1))) - s : ℕ) : ℤ)) := by
  let J := (i : ℕ) + 1
  let H := ValuationWord.total (w.take (2 * J)) - s
  have hHpos : 0 < H := by
    dsimp [H, J]
    exact Nat.sub_pos_of_lt hpass.2
  have hHle : H ≤ 8 := by
    by_contra hnot
    have htail' : horizonTailEvent s 8 i w := by
      rcases hpass with ⟨hbefore, hcross⟩
      refine ⟨hbefore, ?_⟩
      dsimp [H, J] at hnot
      omega
    exact htail ⟨i, htail'⟩
  have hnotHigh : ¬ ((s : ℝ) / 4 + Real.sqrt (s : ℝ) + 1 < J) := by
    intro h
    apply hhigh
    refine ⟨i, hpass, ?_⟩
    dsimp [J] at h
    norm_num at h ⊢
    exact h
  have hJ : J ≤ 5 * (s / 16) + 9 :=
    passageIndex_le_five_div_sixteen_add_nine s J hnotHigh
  simpa only [J, H] using
    (selected_triangle_firstPassageExit_white_of_bounds n j₀ j J H s l₀ l ξ
      hsel hstart hs hJ hHle hHpos)

/-- The same good common-horizon word exits before the terminal column. -/
theorem selected_triangle_horizonGoodExit_before_terminal
    (n j₀ j s : ℕ) (i : Fin (s / 2 + 1)) (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (w : ValuationWord)
    (hsel : isSelectedPhaseTriangle n ξ j₀ l₀)
    (hstart : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (hs : (l₀ - l).toNat = s)
    (hn : 0 < n) (hj₀ : 2 * j₀ < n)
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hpass : horizonTailEvent s 0 i w)
    (hhigh : ¬ stoppedPassageIndexHighEvent s w) :
    j + ((i : ℕ) + 1) < n / 2 := by
  let J := (i : ℕ) + 1
  have hnotHigh : ¬ ((s : ℝ) / 4 + Real.sqrt (s : ℝ) + 1 < J) := by
    intro h
    apply hhigh
    refine ⟨i, hpass, ?_⟩
    dsimp [J] at h
    norm_num at h ⊢
    exact h
  have hJ : J ≤ 5 * (s / 16) + 9 :=
    passageIndex_le_five_div_sixteen_add_nine s J hnotHigh
  simpa only [J] using
    (firstPassageExit_before_terminal n j₀ j J s l₀ l ξ hsel hstart hs hJ hn hj₀ hξ)

/-- The concrete common-horizon event that records a white first-passage
exit from a fixed selected triangle start. -/
def stoppedWhiteExitEvent (n _j₀ j s : ℕ) (l₀ _l : ℤ) (ξ : ZMod (3 ^ n))
    (w : ValuationWord) : Prop :=
  ∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w ∧
    ¬ phaseBlackAtInt n ξ (j + ((i : ℕ) + 1))
      (l₀ + ((ValuationWord.total (w.take (2 * ((i : ℕ) + 1))) - s : ℕ) : ℤ)) ∧
    j + ((i : ℕ) + 1) < n / 2

/-- Original probability of the common-horizon white-exit event. -/
noncomputable def stoppedWhiteExitProbability (n j₀ j s : ℕ) (l₀ l : ℤ)
    (ξ : ZMod (3 ^ n)) : ℝ :=
  Gated.probability (Reference.wordPMF (2 * (s / 2 + 1)))
    (stoppedWhiteExitEvent n j₀ j s l₀ l ξ)

/-- On the actual reference-word support, the simultaneous good event is a
subset of the white-exit event. -/
theorem stoppedExitGoodEvent_subset_whiteExit
    (n j₀ j s : ℕ) (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (hsel : isSelectedPhaseTriangle n ξ j₀ l₀)
    (hstart : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (hs : (l₀ - l).toNat = s)
    (hn : 0 < n) (hj₀ : 2 * j₀ < n)
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) {w : ValuationWord}
    (hw : Reference.wordPMF (2 * (s / 2 + 1)) w ≠ 0)
    (hgood : stoppedExitGoodEvent s w) :
    stoppedWhiteExitEvent n j₀ j s l₀ l ξ w := by
  have hlen : w.length = 2 * (s / 2 + 1) :=
    (Reference.wordPMF_mem_support_iff (2 * (s / 2 + 1)) w).mp hw
  obtain ⟨i, hpass⟩ := exists_horizonTailEvent_zero_of_length hlen
  refine ⟨i, hpass, ?_, ?_⟩
  · exact selected_triangle_horizonGoodExit_white n j₀ j s i l₀ l ξ w
      hsel hstart hs hpass hgood.1 hgood.2
  · exact selected_triangle_horizonGoodExit_before_terminal n j₀ j s i l₀ l ξ w
      hsel hstart hs hn hj₀ hξ hpass hgood.1

/-- The original common-horizon white-exit probability dominates the
simultaneous good-event probability. -/
theorem stoppedExitGoodProbability_le_whiteExitProbability
    (n j₀ j s : ℕ) (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (hsel : isSelectedPhaseTriangle n ξ j₀ l₀)
    (hstart : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (hs : (l₀ - l).toNat = s)
    (hn : 0 < n) (hj₀ : 2 * j₀ < n)
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    stoppedExitGoodProbability s ≤ stoppedWhiteExitProbability n j₀ j s l₀ l ξ := by
  apply Gated.probability_mono_on_support
    (Reference.wordPMF (2 * (s / 2 + 1)))
  intro w hw hgood
  exact stoppedExitGoodEvent_subset_whiteExit n j₀ j s l₀ l ξ
    hsel hstart hs hn hj₀ hξ hw hgood

/-- At every positive vertical distance, the original-word white-exit event
has probability strictly greater than `15 / 16`. -/
theorem stoppedWhiteExitProbability_gt_fifteen_sixteenths {s : ℕ} (hspos : 0 < s)
    (n j₀ j : ℕ) (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (hsel : isSelectedPhaseTriangle n ξ j₀ l₀)
    (hstart : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (hs : (l₀ - l).toNat = s)
    (hn : 0 < n) (hj₀ : 2 * j₀ < n)
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    (15 / 16 : ℝ) < stoppedWhiteExitProbability n j₀ j s l₀ l ξ := by
  exact lt_of_lt_of_le exitGood_numeric_lower
    ((stoppedExitGoodProbability_lower hspos).trans
      (stoppedExitGoodProbability_le_whiteExitProbability n j₀ j s l₀ l ξ
        hsel hstart hs hn hj₀ hξ))

/-- The level-zero numerical good-event lower bound also exceeds `15 / 16`. -/
theorem exitGood_zero_numeric_lower :
    (15 / 16 : ℝ) < 1 - (9 / 256 : ℝ) := by norm_num

/-- The level-zero original-word white-exit event has probability strictly
greater than `15 / 16`. -/
theorem stoppedWhiteExitProbability_zero_gt_fifteen_sixteenths
    (n j₀ j : ℕ) (l₀ l : ℤ) (ξ : ZMod (3 ^ n))
    (hsel : isSelectedPhaseTriangle n ξ j₀ l₀)
    (hstart : inPhaseTriangleIntMul n ξ j₀ l₀ j l)
    (hs : (l₀ - l).toNat = 0)
    (hn : 0 < n) (hj₀ : 2 * j₀ < n)
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    (15 / 16 : ℝ) < stoppedWhiteExitProbability n j₀ j 0 l₀ l ξ := by
  exact lt_of_lt_of_le exitGood_zero_numeric_lower
    (stoppedExitGoodProbability_zero_lower.trans
      (stoppedExitGoodProbability_le_whiteExitProbability n j₀ j 0 l₀ l ξ
        hsel hstart hs hn hj₀ hξ))

end LocalPrimitive
end WordCertDensity
