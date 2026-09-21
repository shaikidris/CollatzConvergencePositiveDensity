/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.Pairing
public import WordCertDensity.Reference.WaitingTime
public import WordCertDensity.Reference.WordMoment
public import WordCertDensity.Probability.FairBinomialTail
public import Mathlib.Data.Nat.Choose.Central
import WordCertDensity.Probability.FiniteUnion
import WordCertDensity.Probability.DisjointUnion
import WordCertDensity.Analytic.Typical

/-!
# First-passage coordinates for the original pair process

This module fixes the integer conventions in Appendix E.4, derives the exact
original-pair strict first-passage atom, and retains the fair-success index as
the intended coupling target. A fair-success count selects the next pair index
by division by two, and the displayed joint-law right hand side uses a natural
(hence truncated) overshoot coefficient. The direct fair-toss coupling and
the overshoot, passage-index, and exit estimates remain subsequent E-L3
obligations.
-/

@[expose] public section

namespace WordCertDensity
namespace LocalPrimitive

/-- The pair index selected by a fair-success count before the strict level
`s` crossing. This is the right-hand side of `(E.passage)`. -/
def passageIndex (successes : ℕ) : ℕ := successes / 2 + 1

/-- The Appendix E joint first-passage atom, with its overshoot coefficient
formed in `ℕ` before coercion to `ℝ`. The printed identity is restricted to
positive `j` and `h`; the natural subtraction keeps the formula total. -/
noncomputable def passageJointAtom (s j h : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (s + h) *
    ((s.choose (2 * j - 2) : ℝ) * ((h - 1 : ℕ) : ℝ) + s.choose (2 * j - 1))

/-- `(E.passage)` always selects a positive pair index. -/
theorem passageIndex_pos (successes : ℕ) : 0 < passageIndex successes := by
  simp [passageIndex]

/-- A success count observed in the first `s` tosses gives the deterministic
upper bound used in `(E.overshoot)`. -/
theorem passageIndex_le_of_le {successes s : ℕ} (h : successes ≤ s) :
    passageIndex successes ≤ s / 2 + 1 := by
  unfold passageIndex
  omega

/-- The even success count giving the `(j,h)` atom has pair index `q + 1`. -/
theorem passageIndex_even (q : ℕ) : passageIndex (2 * q) = q + 1 := by
  simp [passageIndex]

/-- The odd success count giving the `(j,h)` atom has the same pair index. -/
theorem passageIndex_odd (q : ℕ) : passageIndex (2 * q + 1) = q + 1 := by
  unfold passageIndex
  omega

/-- At a positive pair index, the fair-success count has exactly the two
parities displayed in `(E.passage)`. -/
theorem passageIndex_eq_iff {j k : ℕ} (hj : 0 < j) :
    passageIndex k = j ↔ k = 2 * (j - 1) ∨ k = 2 * (j - 1) + 1 := by
  constructor
  · intro h
    unfold passageIndex at h
    omega
  · rintro (rfl | rfl)
    · rw [passageIndex_even]
      omega
    · rw [passageIndex_odd]
      omega

/-- The displayed joint atom is nonnegative at every natural input. -/
theorem passageJointAtom_nonneg (s j h : ℕ) : 0 ≤ passageJointAtom s j h := by
  unfold passageJointAtom
  apply mul_nonneg
  · positivity
  · apply add_nonneg
    · exact mul_nonneg (by positivity) (by positivity)
    · positivity

/-- Original probability that `j` complete pairs have total valuation `k`. -/
noncomputable def pairSumProbability (j k : ℕ) : ℝ :=
  Gated.probability (Reference.wordPMF (2 * j)) (fun w => w.total = k)

/-- The original-word event that the `j`-th pair is the strict first passage
above level `s`, with the overshoot left existential. -/
def pairPassageIndexEvent (s j : ℕ) (w : ValuationWord) : Prop :=
  w.length = 2 * j ∧
    ValuationWord.total (w.take (2 * (j - 1))) ≤ s ∧ s < w.total

private theorem gatedProbability_eq_point {α : Type*} (p : PMF α) (x : α) :
    Gated.probability p (fun y => y = x) = (p x).toReal := by
  unfold Gated.probability
  rw [tsum_eq_single x]
  · simp
  · intro y hy
    simp [hy]

/-- The original law of the total valuation after `j` complete pairs. -/
noncomputable def pairTotalPMF (j : ℕ) : PMF ℕ :=
  (Reference.wordPMF (2 * j)).map ValuationWord.total

/-- Its literal PMF atom is exactly the original pair-total event probability. -/
theorem pairTotalPMF_toReal (j k : ℕ) :
    (pairTotalPMF j k).toReal = pairSumProbability j k := by
  rw [← gatedProbability_eq_point]
  exact Gated.probability_map (Reference.wordPMF (2 * j)) ValuationWord.total
    (fun total => total = k)

/-- The total valuation after `j + 1` pairs is the convolution of the first
`j` pair total and the final-pair total, under the original word law. -/
theorem pairTotalPMF_succ (j : ℕ) :
    pairTotalPMF (j + 1) =
      (pairTotalPMF j).bind
        (fun r => (pairTotalPMF 1).map (fun b => r + b)) := by
  have hsplit := congrArg (fun p : PMF (ValuationWord × ValuationWord) =>
    p.map (fun uv => uv.1.total + uv.2.total))
    (Reference.wordPMF_map_take_drop (2 * j) 2)
  have hleft :
      (Reference.wordPMF (2 * j + 2)).map
          (fun w => ValuationWord.total (w.take (2 * j)) +
            ValuationWord.total (w.drop (2 * j))) =
        (Reference.wordPMF (2 * j + 2)).map ValuationWord.total := by
    rw [PMF.ext_iff]
    intro k
    rw [PMF.map_apply, PMF.map_apply]
    apply tsum_congr
    intro w
    have hsplitw := List.take_append_drop (2 * j) w
    have htotal : w.total = ValuationWord.total (w.take (2 * j)) +
        ValuationWord.total (w.drop (2 * j)) := by
      calc
        w.total = ValuationWord.total (w.take (2 * j) ++ w.drop (2 * j)) :=
          congrArg ValuationWord.total hsplitw.symm
        _ = _ := ValuationWord.total_append _ _
    simp [htotal]
  simp only [PMF.map_comp, Function.comp_def] at hsplit
  rw [hleft] at hsplit
  rw [PMF.map_bind] at hsplit
  simp only [PMF.map_comp, Function.comp_def] at hsplit
  simp only [pairTotalPMF]
  rw [show 2 * (j + 1) = 2 * j + 2 by omega]
  rw [hsplit]
  simp only [PMF.bind_map, PMF.map_comp, Function.comp_def]

/-- The independent prefix/final-pair product law pushes forward to the joint
law of its two total valuations. -/
theorem pairProductTotalPMF (j : ℕ) :
    ((Reference.wordPMF (2 * j)).bind
        (fun u => (Reference.wordPMF 2).map (fun v => (u, v)))).map
      (fun uv => (uv.1.total, uv.2.total)) =
      (pairTotalPMF j).bind
        (fun r => (pairTotalPMF 1).map (fun b => (r, b))) := by
  simp only [pairTotalPMF, PMF.map_bind, PMF.bind_map, PMF.map_comp,
    Function.comp_def]

/-- An atom of a sequentially sampled pair of natural-valued PMFs factors as
the product of its two marginal atoms. -/
theorem bind_map_pair_apply (p q : PMF ℕ) (r b : ℕ) :
    (p.bind fun a => q.map (fun c => (a, c))) (r, b) = p r * q b := by
  rw [PMF.bind_apply]
  have hmap (a : ℕ) :
      (q.map (fun c => (a, c))) (r, b) = if a = r then q b else 0 := by
    rw [PMF.map_apply]
    by_cases har : a = r
    · subst a
      rw [tsum_eq_single b]
      · simp
      · intro c hc
        simp [Ne.symm hc]
    · rw [if_neg har]
      apply ENNReal.tsum_eq_zero.2
      intro c
      by_cases hp : (r, b) = (a, c)
      · have hfirst : r = a := congrArg Prod.fst hp
        exact (har hfirst.symm).elim
      · simp [hp]
  simp_rw [hmap]
  rw [tsum_eq_single r]
  · simp
  · intro a ha
    simp [ha]

/-- Under a sequential product PMF, fixing the first coordinate and imposing
an arbitrary event on the second coordinate factors its original probability. -/
theorem bind_map_pair_first_probability (p q : PMF ℕ) (r : ℕ)
    (B : ℕ → Prop) :
    Gated.probability (p.bind fun a => q.map (fun b => (a, b)))
      (fun ab => ab.1 = r ∧ B ab.2) =
      (p r).toReal * Gated.probability q B := by
  classical
  unfold Gated.probability
  have hsum :
      (∑' ab, (p.bind fun a => q.map (fun b => (a, b))) ab *
        if ab.1 = r ∧ B ab.2 then 1 else 0) =
      p r * ∑' b, if B b then q b else 0 := by
    rw [PMFMoment.sum_bind]
    have hmap (a : ℕ) :
        (∑' ab, (q.map (fun b => (a, b))) ab *
          if ab.1 = r ∧ B ab.2 then 1 else 0) =
          ∑' b, q b * if a = r ∧ B b then 1 else 0 :=
      PMFMoment.sum_map q (fun b => (a, b))
        (fun ab => if ab.1 = r ∧ B ab.2 then 1 else 0)
    simp_rw [hmap]
    have hinner (a : ℕ) :
        (∑' b, q b * if a = r ∧ B b then 1 else 0) =
          if a = r then ∑' b, if B b then q b else 0 else 0 := by
      by_cases har : a = r
      · subst a
        simp [mul_ite]
      · simp [har]
    simp_rw [hinner]
    rw [tsum_eq_single r]
    · simp
    · intro a har
      simp [har]
  simp only [mul_ite, mul_one, mul_zero] at hsum
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_mul] at hr
  refine (congrArg ENNReal.toReal ?_).trans hr
  apply tsum_congr
  intro ab
  by_cases hab : ab.1 = r ∧ B ab.2 <;> simp [hab]

/-- The even-indexed part of the `s`-th Pascal row. -/
def evenChooseSum (s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (s + 1), if Even i then s.choose i else 0

/-- The odd-indexed part of the `s`-th Pascal row. -/
def oddChooseSum (s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (s + 1), if Odd i then s.choose i else 0

/-- The even and odd parts partition the full Pascal row. -/
theorem parity_choose_partition (s : ℕ) :
    evenChooseSum s + oddChooseSum s = 2 ^ s := by
  unfold evenChooseSum oddChooseSum
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i ∈ Finset.range (s + 1),
        ((if Even i then s.choose i else 0) + if Odd i then s.choose i else 0)) =
        ∑ i ∈ Finset.range (s + 1), s.choose i := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases he : Even i
      · have ho : ¬ Odd i := by
          intro h
          exact (Nat.not_even_iff_odd.mpr h) he
        simp [he, ho]
      · have ho : Odd i := Nat.not_even_iff_odd.mp he
        simp [he, ho]
    _ = 2 ^ s := Nat.sum_range_choose s

/-- The alternating Pascal sum is the difference of its even and odd parts. -/
theorem parity_choose_alternating (s : ℕ) :
    ((evenChooseSum s : ℤ) - oddChooseSum s) =
      ∑ i ∈ Finset.range (s + 1), ((-1) ^ i * s.choose i : ℤ) := by
  unfold evenChooseSum oddChooseSum
  rw [Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases he : Even i
  · have hepow : (-1 : ℤ) ^ i = 1 := Even.neg_one_pow he
    have ho : ¬ Odd i := by
      intro h
      exact (Nat.not_even_iff_odd.mpr h) he
    simp [he, ho, hepow]
  · have ho : Odd i := Nat.not_even_iff_odd.mp he
    have hopow : (-1 : ℤ) ^ i = -1 := Odd.neg_one_pow ho
    simp [he, ho, hopow]

/-- At a positive row index, the even and odd Pascal masses are equal. -/
theorem evenChooseSum_eq_oddChooseSum {s : ℕ} (hs : 0 < s) :
    evenChooseSum s = oddChooseSum s := by
  have halt := parity_choose_alternating s
  rw [Int.alternating_sum_range_choose_of_ne (by omega : s ≠ 0)] at halt
  exact_mod_cast Int.sub_eq_zero.mp halt

/-- The even Pascal mass is the finite sum over the possible pair indices. -/
theorem evenChooseSum_eq_pairIndexSum (s : ℕ) :
    evenChooseSum s = ∑ i ∈ Finset.range (s / 2 + 1), s.choose (2 * i) := by
  classical
  unfold evenChooseSum
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun k _ => k / 2)
  · intro k hk
    exact Finset.mem_range.mpr (by
      rcases Finset.mem_filter.mp hk with ⟨hkRange, hkEven⟩
      rcases hkEven with ⟨i, rfl⟩
      have hdiv : (i + i) / 2 = i := by
        rw [show i + i = 2 * i by omega, Nat.mul_div_cancel_left _ zero_lt_two]
      rw [hdiv]
      have hsum : i + i < s + 1 := by simpa using hkRange
      have hsum' : i + i ≤ s := by omega
      have htwo : i * 2 ≤ s := by
        calc i * 2 = i + i := by omega
          _ ≤ s := hsum'
      have hi_le : i ≤ s / 2 :=
        (Nat.le_div_iff_mul_le zero_lt_two).mpr htwo
      omega)
  · intro k hk l hl hkl
    rcases Finset.mem_filter.mp hk with ⟨_, hkEven⟩
    rcases Finset.mem_filter.mp hl with ⟨_, hlEven⟩
    rcases hkEven with ⟨i, rfl⟩
    rcases hlEven with ⟨j, rfl⟩
    omega
  · intro i hi
    refine ⟨2 * i, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ⟨i, by omega⟩⟩
      have hi_le : i ≤ s / 2 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have htwo : i * 2 ≤ s :=
        (Nat.le_div_iff_mul_le zero_lt_two).mp hi_le
      omega
    · rw [Nat.mul_div_cancel_left _ zero_lt_two]
  · intro i hi
    rcases Finset.mem_filter.mp hi with ⟨_, hiEven⟩
    rcases hiEven with ⟨j, rfl⟩
    have hdiv : (j + j) / 2 = j := by
      rw [show j + j = 2 * j by omega, Nat.mul_div_cancel_left _ zero_lt_two]
    rw [hdiv]
    rw [show j + j = 2 * j by omega]

/-- The odd Pascal mass reindexed by the possible pair-passage indices.
The shorter range omits the final zero that occurs at an even level. -/
theorem oddChooseSum_eq_pairIndexSum_short (s : ℕ) :
    oddChooseSum s = ∑ i ∈ Finset.range ((s + 1) / 2), s.choose (2 * i + 1) := by
  classical
  unfold oddChooseSum
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun k _ => (k - 1) / 2)
  · intro k hk
    exact Finset.mem_range.mpr (by
      rcases Finset.mem_filter.mp hk with ⟨hkRange, hkOdd⟩
      rcases hkOdd with ⟨i, rfl⟩
      have hdiv : (2 * i + 1 - 1) / 2 = i := by
        rw [show 2 * i + 1 - 1 = 2 * i by omega,
          Nat.mul_div_cancel_left _ zero_lt_two]
      rw [hdiv]
      rw [Nat.lt_div_iff_mul_lt zero_lt_two]
      have hlt : 2 * i < s := by simpa using hkRange
      simpa [Nat.mul_comm] using hlt)
  · intro k hk l hl hkl
    rcases Finset.mem_filter.mp hk with ⟨_, hkOdd⟩
    rcases Finset.mem_filter.mp hl with ⟨_, hlOdd⟩
    rcases hkOdd with ⟨i, rfl⟩
    rcases hlOdd with ⟨j, rfl⟩
    omega
  · intro i hi
    refine ⟨2 * i + 1, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ⟨i, by omega⟩⟩
      have hi' : i < (s + 1) / 2 := Finset.mem_range.mp hi
      rw [Nat.lt_div_iff_mul_lt zero_lt_two] at hi'
      omega
    · rw [show 2 * i + 1 - 1 = 2 * i by omega,
        Nat.mul_div_cancel_left _ zero_lt_two]
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨_, hkOdd⟩
    rcases hkOdd with ⟨i, rfl⟩
    have hdiv : (2 * i + 1 - 1) / 2 = i := by
      rw [show 2 * i + 1 - 1 = 2 * i by omega,
        Nat.mul_div_cancel_left _ zero_lt_two]
    rw [hdiv]

/-- The odd Pascal mass on the same pair-index range as the even mass.
At an even level this range has one extra, zero, binomial coefficient. -/
theorem oddChooseSum_eq_pairIndexSum (s : ℕ) :
    oddChooseSum s = ∑ i ∈ Finset.range (s / 2 + 1), s.choose (2 * i + 1) := by
  rw [oddChooseSum_eq_pairIndexSum_short]
  rcases Nat.even_or_odd' s with ⟨k, rfl | rfl⟩
  · rw [show (2 * k + 1) / 2 = k by omega, Finset.sum_range_succ]
    simp
  · congr
    omega

/-- At positive level and positive overshoot, the finite sum of the two
Pascal coefficients in the joint atom is `h` times the even Pascal mass. -/
theorem pairIndexJointCoefficient_sum {s h : ℕ} (hs : 0 < s) (hh : 0 < h) :
    ∑ i ∈ Finset.range (s / 2 + 1),
      ((s.choose (2 * i) : ℝ) * ((h - 1 : ℕ) : ℝ) + s.choose (2 * i + 1)) =
        (h : ℝ) * evenChooseSum s := by
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [← Nat.cast_sum, ← Nat.cast_sum,
    ← evenChooseSum_eq_pairIndexSum,
    ← oddChooseSum_eq_pairIndexSum,
    evenChooseSum_eq_oddChooseSum hs]
  cases h with
  | zero => omega
  | succ h =>
      push_cast
      ring

/-- At positive level, twice the pair-indexed even Pascal mass is the full
Pascal mass. -/
theorem two_mul_evenChooseSum_eq_pow {s : ℕ} (hs : 0 < s) :
    2 * evenChooseSum s = 2 ^ s := by
  rw [← parity_choose_partition s, evenChooseSum_eq_oddChooseSum hs]
  omega

/-- The unweighted hockey-stick identity on a finite initial range. -/
theorem sum_range_choose (s k : ℕ) :
    ∑ i ∈ Finset.range s, i.choose k = s.choose (k + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ']
      omega

/-- The weighted hockey-stick identity used to collapse the strict
first-passage sum. -/
theorem weighted_hockey (s k : ℕ) :
    ∑ i ∈ Finset.range s, (s - (i + 1)) * i.choose k = s.choose (k + 2) := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self, zero_mul]
      calc
        (∑ i ∈ Finset.range s, (s + 1 - (i + 1)) * i.choose k) =
            ∑ i ∈ Finset.range s,
              ((s - (i + 1)) * i.choose k + i.choose k) := by
                apply Finset.sum_congr rfl
                intro i hi
                have his : i < s := Finset.mem_range.mp hi
                have hsub : s + 1 - (i + 1) = (s - (i + 1)) + 1 := by omega
                rw [hsub, Nat.add_mul, one_mul]
        _ = (∑ i ∈ Finset.range s, (s - (i + 1)) * i.choose k) +
              ∑ i ∈ Finset.range s, i.choose k := by
                rw [Finset.sum_add_distrib]
        _ = s.choose (k + 2) + s.choose (k + 1) := by rw [ih, sum_range_choose]
        _ = (s + 1).choose (k + 2) := by
              rw [Nat.choose_succ_succ' s (k + 1)]
              have hidx : k + 1 + 1 = k + 2 := by omega
              rw [hidx]
              exact Nat.add_comm _ _

/-- The combined unweighted and weighted hockey-stick identity matching the
two coefficients in the strict first-passage formula. -/
theorem joint_coefficient_sum (s k h : ℕ) :
    ∑ i ∈ Finset.range s,
        ((h - 1) * i.choose k + (s - (i + 1)) * i.choose k) =
      (h - 1) * s.choose (k + 1) + s.choose (k + 2) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_range_choose, weighted_hockey]

/-- Shifted hockey-stick form for a nonzero completed-pair prefix. -/
theorem shifted_hockey (s k : ℕ) (hk : 0 < k) :
    ∑ r ∈ Finset.range (s + 1), (r - 1).choose k = s.choose (k + 1) := by
  induction s with
  | zero => simp [Nat.choose_eq_zero_of_lt hk]
  | succ s ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_sub_cancel]
      rw [Nat.choose_succ_succ']
      ac_rfl

/-- The shifted coefficient sum arising from the product of a positive
completed-pair prefix atom and the final-pair atom. -/
theorem shifted_joint_coefficient_sum (s k h : ℕ) (hk : 0 < k) (hh : 0 < h) :
    ∑ r ∈ Finset.range (s + 1),
        (r - 1).choose k * (s + h - r - 1) =
      (h - 1) * s.choose (k + 1) + s.choose (k + 2) := by
  induction s with
  | zero => simp [Nat.choose_eq_zero_of_lt hk]
  | succ s ih =>
      rw [Finset.sum_range_succ]
      have hsplit :
          (∑ r ∈ Finset.range (s + 1),
            (r - 1).choose k * (s + 1 + h - r - 1)) =
          (∑ r ∈ Finset.range (s + 1),
            ((r - 1).choose k * (s + h - r - 1) + (r - 1).choose k)) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrs : r < s + 1 := Finset.mem_range.mp hr
          have hrs' : r ≤ s := by omega
          have hsub : s + 1 + h - r - 1 = (s + h - r - 1) + 1 := by omega
          rw [hsub, Nat.mul_add, Nat.mul_one]
      rw [hsplit, Finset.sum_add_distrib, ih, shifted_hockey s k hk]
      simp only [Nat.add_sub_cancel]
      have hlast : s + 1 + h - (s + 1) - 1 = h - 1 := by omega
      rw [hlast]
      rw [Nat.choose_succ_succ' s k, Nat.choose_succ_succ' s (k + 1)]
      have hidx : k + 1 + 1 = k + 2 := by omega
      rw [hidx]
      ring

/-- Original CDF for the total valuation after `j` complete pairs. -/
noncomputable def pairSumCdf (j k : ℕ) : ℝ :=
  Gated.probability (Reference.wordPMF (2 * j)) (fun w => w.total ≤ k)

/-- Original probability that the `j`-th pair is the strict passage above
level `s`, with the terminal overshoot marginalized. -/
noncomputable def pairPassageIndexProbability (s j : ℕ) : ℝ :=
  Gated.probability (Reference.wordPMF (2 * j)) (pairPassageIndexEvent s j)

/-- The original strict-passage event is the exact CDF increment between the
completed prefix and the completed final pair. -/
theorem pairPassageIndexProbability_eq_cdf_sub {s j : ℕ} (hj : 0 < j) :
    pairPassageIndexProbability s j =
      pairSumCdf (j - 1) s - pairSumCdf j s := by
  let p := Reference.wordPMF (2 * j)
  let P : ValuationWord → Prop := fun w =>
    ValuationWord.total (w.take (2 * (j - 1))) ≤ s
  let G : Bool → ValuationWord → Prop := fun b w =>
    if b then w.total ≤ s else pairPassageIndexEvent s j w
  have hunique : ∀ i k w, G i w → G k w → i = k := by
    intro i k w hi hk
    cases i <;> cases k <;> try rfl
    · simp [G] at hi hk
      exact False.elim ((not_lt_of_ge hk) hi.2.2)
    · simp [G] at hi hk
      exact False.elim ((not_lt_of_ge hi) hk.2.2)
  have hunion := Gated.probability_union p G hunique
  have hUnion :
      Gated.probability p (fun w => ∃ b, G b w) = Gated.probability p P := by
    apply Gated.probability_congr_on_support
    intro w hw
    have hlen : w.length = 2 * j := by
      apply (Reference.wordPMF_mem_support_iff (2 * j) w).mp
      exact hw
    simp only [G, P]
    constructor
    · rintro ⟨b, hb⟩
      cases b <;> simp at hb
      · exact hb.2.1
      · exact le_trans (ValuationWord.total_take_le w (2 * (j - 1))) hb
    · intro hp
      by_cases htotal : w.total ≤ s
      · exact ⟨true, htotal⟩
      · exact ⟨false, hlen, hp, by omega⟩
  rw [hUnion, Fintype.sum_bool] at hunion
  have hprefix : Gated.probability p P = pairSumCdf (j - 1) s := by
    have hmap := Gated.probability_map p (fun w => w.take (2 * (j - 1)))
      (fun u => ValuationWord.total u ≤ s)
    rw [Reference.wordPMF_map_take_of_le (show 2 * (j - 1) ≤ 2 * j by omega)] at hmap
    simpa [p, P, pairSumCdf] using hmap.symm
  dsimp [pairPassageIndexProbability]
  rw [show Reference.wordPMF (2 * j) = p by rfl]
  have hfull : Gated.probability p (G true) = pairSumCdf j s := by
    simp [p, G, pairSumCdf]
  have hpassage : Gated.probability p (G false) =
      pairPassageIndexProbability s j := by
    simp [p, G, pairPassageIndexProbability]
  rw [hfull, hpassage] at hunion
  change Gated.probability p (G false) =
    pairSumCdf (j - 1) s - pairSumCdf j s
  rw [hpassage]
  rw [← hprefix]
  linarith

/-- The original pair-total CDF is the fair-binomial upper tail supplied by
the waiting-time representation. This is the source-faithful general bridge
used to extract the negative-binomial atoms. -/
theorem pairSumCdf_eq_binomial (j k : ℕ) :
    pairSumCdf j k =
      Gated.probability (Probability.fairBinomial k) (fun successes => 2 * j ≤ successes) := by
  exact Reference.word_total_le_binomial_probability (2 * j) k

/-- The fair-binomial upper-tail probability, retained as a real quantity. -/
noncomputable def fairUpperProbability (trials successes : ℕ) : ℝ :=
  Gated.probability (Probability.fairBinomial trials) (fun k => successes ≤ k)

private theorem fairBinomialUpperMass_ne_top (trials successes : ℕ) :
    Probability.fairBinomialUpperMass trials successes ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  unfold Probability.fairBinomialUpperMass
  calc
    (∑' k, Probability.fairBinomial trials k * if successes ≤ k then 1 else 0) ≤
        ∑' k, Probability.fairBinomial trials k := by
          apply ENNReal.tsum_le_tsum
          intro k
          split_ifs <;> simp
    _ = 1 := (Probability.fairBinomial trials).tsum_coe

/-- Pascal's recurrence for the real upper-tail probabilities. This finite
recurrence is the atom-extraction interface following the waiting-time CDF. -/
theorem fairUpperProbability_succ_succ (trials successes : ℕ) :
    fairUpperProbability (trials + 1) (successes + 1) =
      (1 / 2 : ℝ) * fairUpperProbability trials successes +
        (1 / 2 : ℝ) * fairUpperProbability trials (successes + 1) := by
  unfold fairUpperProbability
  rw [← Probability.fairBinomialUpperMass_toReal,
    ← Probability.fairBinomialUpperMass_toReal,
    ← Probability.fairBinomialUpperMass_toReal,
    Probability.fairBinomialUpperMass_succ_succ]
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top (by simp) (fairBinomialUpperMass_ne_top trials successes))
    (ENNReal.mul_ne_top (by simp) (fairBinomialUpperMass_ne_top trials (successes + 1))),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  norm_num

/-- The point mass of a fair-binomial count, viewed in `ℝ`. -/
noncomputable def fairPointProbability (trials successes : ℕ) : ℝ :=
  (Probability.fairBinomial trials successes).toReal

/-- The exact binomial point-mass formula used in `(E.joint)`. -/
theorem fairPointProbability_eq (trials successes : ℕ) :
    fairPointProbability trials successes =
      (trials.choose successes : ℝ) * (1 / 2 : ℝ) ^ trials := by
  unfold fairPointProbability
  rw [Probability.fairBinomial_apply, ENNReal.toReal_mul, ENNReal.toReal_pow]
  norm_num

/-- The original pair-total CDF is the upper-tail recurrence in its local
real-valued interface. -/
theorem pairSumCdf_eq_fairUpper (j k : ℕ) :
    pairSumCdf j k = fairUpperProbability k (2 * j) := by
  exact pairSumCdf_eq_binomial j k

/-- Fair-binomial probability that the success count selects pair index `j`. -/
noncomputable def fairPassageIndexProbability (s j : ℕ) : ℝ :=
  Gated.probability (Probability.fairBinomial s) (fun k => passageIndex k = j)

/-- The fair `(E.passage)` event is the difference of its adjacent upper
tails, with the two admissible success parities kept explicit. -/
theorem fairPassageIndexProbability_eq_cdf_sub {s j : ℕ} (hj : 0 < j) :
    fairPassageIndexProbability s j =
      fairUpperProbability s (2 * (j - 1)) - fairUpperProbability s (2 * j) := by
  let p := Probability.fairBinomial s
  let P : ℕ → Prop := fun k => 2 * (j - 1) ≤ k
  let G : Bool → ℕ → Prop := fun b k =>
    if b then 2 * j ≤ k else passageIndex k = j
  have hunique : ∀ i k x, G i x → G k x → i = k := by
    intro i k x hi hk
    cases i <;> cases k <;> try rfl
    · simp [G] at hi hk
      rw [passageIndex_eq_iff hj] at hi
      omega
    · simp [G] at hi hk
      rw [passageIndex_eq_iff hj] at hk
      omega
  have hunion := Gated.probability_union p G hunique
  have hUnion :
      Gated.probability p (fun k => ∃ b, G b k) = Gated.probability p P := by
    apply Gated.probability_congr_on_support
    intro k _
    simp only [G, P]
    constructor
    · rintro ⟨b, hb⟩
      cases b <;> simp at hb
      · rw [passageIndex_eq_iff hj] at hb
        omega
      · omega
    · intro hp
      by_cases hlarge : 2 * j ≤ k
      · exact ⟨true, hlarge⟩
      · exact ⟨false, (passageIndex_eq_iff hj).mpr (by omega)⟩
  rw [hUnion, Fintype.sum_bool] at hunion
  have hprefix : Gated.probability p P = fairUpperProbability s (2 * (j - 1)) := by
    simp [p, P, fairUpperProbability]
  have hfull : Gated.probability p (G true) = fairUpperProbability s (2 * j) := by
    simp [p, G, fairUpperProbability]
  have hpassage : Gated.probability p (G false) =
      fairPassageIndexProbability s j := by
    simp [p, G, fairPassageIndexProbability]
  rw [hfull, hpassage] at hunion
  change Gated.probability p (G false) =
    fairUpperProbability s (2 * (j - 1)) - fairUpperProbability s (2 * j)
  rw [hpassage]
  rw [← hprefix]
  linarith

/-- The original strict-passage index and the fair-success index have the
same law at every positive pair index. This is the distributional coupling
interface for `(E.passage)`. -/
theorem pairPassageIndexProbability_eq_fairPassageIndexProbability {s j : ℕ}
    (hj : 0 < j) :
    pairPassageIndexProbability s j = fairPassageIndexProbability s j := by
  rw [pairPassageIndexProbability_eq_cdf_sub hj, pairSumCdf_eq_fairUpper,
    pairSumCdf_eq_fairUpper, fairPassageIndexProbability_eq_cdf_sub hj]

/-- A fair-binomial count cannot exceed its number of trials. -/
theorem fairBinomial_eq_zero_of_lt (s k : ℕ) (hk : s < k) :
    Probability.fairBinomial s k = 0 := by
  rw [Probability.fairBinomial_apply, Nat.choose_eq_zero_of_lt hk]
  simp

/-- The fair passage-index law is supported on the Appendix E bound. -/
theorem fairPassageIndexProbability_eq_zero_of_gt {s j : ℕ}
    (hj : s / 2 + 1 < j) : fairPassageIndexProbability s j = 0 := by
  unfold fairPassageIndexProbability
  calc
    _ = Gated.probability (Probability.fairBinomial s) (fun _ => False) := by
      apply Gated.probability_congr_on_support
      intro k hk
      have hks : k ≤ s := by
        by_contra hnot
        have hlt : s < k := by omega
        exact hk (fairBinomial_eq_zero_of_lt s k hlt)
      have hne : passageIndex k ≠ j := by
        intro heq
        have hbound := passageIndex_le_of_le hks
        rw [heq] at hbound
        omega
      simp [hne]
    _ = 0 := by simp [Gated.probability]

/-- The original strict-passage index law is supported on
`floor(s / 2) + 1`. -/
theorem pairPassageIndexProbability_eq_zero_of_gt {s j : ℕ}
    (hj : s / 2 + 1 < j) : pairPassageIndexProbability s j = 0 := by
  rw [pairPassageIndexProbability_eq_fairPassageIndexProbability (by omega),
    fairPassageIndexProbability_eq_zero_of_gt hj]

/-- A consecutive original pair-total CDF increment is exactly its total atom.
This is the source-side difference identity used to derive the
negative-binomial mass formula. -/
theorem pairSumCdf_succ (j k : ℕ) :
    pairSumCdf j (k + 1) = pairSumCdf j k + pairSumProbability j (k + 1) := by
  let G : Bool → ValuationWord → Prop := fun b w =>
    if b then w.total = k + 1 else w.total ≤ k
  have hunique : ∀ i l w, G i w → G l w → i = l := by
    intro i l w hi hl
    cases i <;> cases l <;> try rfl
    · simp [G] at hi hl
      omega
    · simp [G] at hi hl
      omega
  have h := Gated.probability_union (Reference.wordPMF (2 * j)) G hunique
  have hUnion : (fun w => ∃ b, G b w) = (fun w => w.total ≤ k + 1) := by
    funext w
    apply propext
    simp only [G]
    constructor
    · rintro ⟨b, hb⟩
      cases b <;> simp at hb ⊢ <;> omega
    · intro hw
      by_cases he : w.total = k + 1
      · exact ⟨true, he⟩
      · exact ⟨false, Nat.le_of_lt_succ (lt_of_le_of_ne hw he)⟩
  rw [hUnion, Fintype.sum_bool] at h
  simpa [pairSumCdf, pairSumProbability, G, add_comm] using h

/-- The exact pair-total atom is the consecutive original-CDF difference. -/
theorem pairSumProbability_eq_cdf_sub (j k : ℕ) :
    pairSumProbability j (k + 1) = pairSumCdf j (k + 1) - pairSumCdf j k := by
  linarith [pairSumCdf_succ j k]

private theorem fairBinomial_event_eq_point (trials successes : ℕ) :
    Gated.probability (Probability.fairBinomial trials) (fun k => k = successes) =
      fairPointProbability trials successes := by
  unfold Gated.probability fairPointProbability
  rw [tsum_eq_single successes]
  · simp
  · intro k hk
    simp [hk]

/-- The fair-binomial mass of zero or one successes has its exact closed
form. -/
theorem fairBinomial_at_most_one_probability (m : ℕ) :
    Gated.probability (Probability.fairBinomial m) (fun k => k ≤ 1) =
      ((m + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ m := by
  let G : Bool → ℕ → Prop := fun b k => if b then k = 0 else k = 1
  have hunique : ∀ i j k, G i k → G j k → i = j := by
    intro i j k hi hj
    cases i <;> cases j <;> try rfl
    · simp [G] at hi hj
      exfalso
      omega
    · simp [G] at hi hj
      exfalso
      omega
  have h := Gated.probability_union (Probability.fairBinomial m) G hunique
  have hUnion : (fun k => ∃ b, G b k) = (fun k => k ≤ 1) := by
    funext k
    apply propext
    constructor
    · rintro ⟨b, hb⟩
      cases b <;> simp [G] at hb <;> omega
    · intro hk
      interval_cases k <;> simp [G] at hk ⊢
  rw [hUnion, Fintype.sum_bool] at h
  simp [G] at h
  rw [fairBinomial_event_eq_point, fairBinomial_event_eq_point] at h
  rw [fairPointProbability_eq, fairPointProbability_eq] at h
  calc
    _ = (1 / 2 : ℝ) ^ m + (m : ℝ) * (1 / 2 : ℝ) ^ m := by
      simpa [Nat.choose_zero_right, Nat.choose_one_right] using h
    _ = ((m + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ m := by
      push_cast
      ring

/-- Original probability that one complete pair has total strictly above
`m`. -/
noncomputable def pairTailProbability (m : ℕ) : ℝ :=
  Gated.probability (Reference.wordPMF 2) (fun w => m < w.total)

/-- The exact original-law tail of one complete pair. -/
theorem pairTailProbability_eq (m : ℕ) :
    pairTailProbability m = ((m + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ m := by
  have hword := Gated.probability_compl (Reference.wordPMF 2)
    (fun w => w.total ≤ m)
  have hword' : pairTailProbability m = 1 - pairSumCdf 1 m := by
    calc
      pairTailProbability m =
          Gated.probability (Reference.wordPMF 2) (fun w => ¬ w.total ≤ m) := by
        unfold pairTailProbability
        apply Gated.probability_congr_on_support
        intro w _
        omega
      _ = 1 - Gated.probability (Reference.wordPMF 2) (fun w => w.total ≤ m) := hword
      _ = 1 - pairSumCdf 1 m := rfl
  have hfair := Gated.probability_compl (Probability.fairBinomial m)
    (fun k => 2 ≤ k)
  rw [hword', pairSumCdf_eq_binomial]
  rw [← hfair]
  have hrewrite :
      Gated.probability (Probability.fairBinomial m) (fun k => ¬ 2 ≤ k) =
        Gated.probability (Probability.fairBinomial m) (fun k => k ≤ 1) := by
    apply Gated.probability_congr_on_support
    intro k _
    omega
  rw [hrewrite, fairBinomial_at_most_one_probability]

/-- An upper tail is its first binomial atom plus the next upper tail. -/
theorem fairUpperProbability_split (trials successes : ℕ) :
    fairUpperProbability trials successes =
      fairPointProbability trials successes + fairUpperProbability trials (successes + 1) := by
  let G : Bool → ℕ → Prop := fun b k => if b then k = successes else successes + 1 ≤ k
  have hunique : ∀ i l k, G i k → G l k → i = l := by
    intro i l k hi hl
    cases i <;> cases l <;> try rfl
    · simp [G] at hi hl
      omega
    · simp [G] at hi hl
      omega
  have h := Gated.probability_union (Probability.fairBinomial trials) G hunique
  have hUnion : (fun k => ∃ b, G b k) = (fun k => successes ≤ k) := by
    funext k
    apply propext
    simp only [G]
    constructor
    · rintro ⟨b, hb⟩
      cases b <;> simp at hb ⊢ <;> omega
    · intro hk
      by_cases he : k = successes
      · exact ⟨true, he⟩
      · exact ⟨false, Nat.succ_le_iff.mpr (lt_of_le_of_ne hk (Ne.symm he))⟩
  rw [hUnion, Fintype.sum_bool] at h
  simp [G] at h
  rw [fairBinomial_event_eq_point] at h
  simpa [fairUpperProbability, add_comm] using h

 /-- The negative-binomial atom expected for a fixed number of original pairs.
The zero branch records the impossible support range. -/
noncomputable def pairSumAtom (j k : ℕ) : ℝ :=
  if 2 * j ≤ k then ((k - 1).choose (2 * j - 1) : ℝ) * (1 / 2 : ℝ) ^ k else 0

/-- The original total after a positive number of pairs has its exact
negative-binomial atom on the supported range. -/
theorem pairSumProbability_eq_pairSumAtom_succ {j k : ℕ} (hj : 0 < j)
    (hsupport : 2 * j ≤ k + 1) :
    pairSumProbability j (k + 1) = pairSumAtom j (k + 1) := by
  rw [pairSumProbability_eq_cdf_sub, pairSumCdf_eq_fairUpper,
    pairSumCdf_eq_fairUpper]
  have htwo : 2 * j = (2 * j - 1) + 1 := by omega
  rw [htwo, fairUpperProbability_succ_succ]
  rw [fairUpperProbability_split]
  ring_nf
  rw [fairPointProbability_eq]
  unfold pairSumAtom
  have hsupport' : 2 * j ≤ 1 + k := by omega
  rw [if_pos hsupport']
  simp only [Nat.add_sub_cancel, Nat.add_comm]
  rw [pow_succ]
  ring_nf

/-- At one pair, the new original-law event is precisely the already verified
pair-total event. -/
theorem pairSumProbability_one {k : ℕ} (hk : 2 ≤ k) :
    pairSumProbability 1 k = Reference.pairMass k := by
  unfold pairSumProbability
  simpa using Reference.pair_probability_eq_pairMass hk

/-- At one pair, the negative-binomial atom agrees with the original pair mass. -/
theorem pairSumAtom_one {k : ℕ} (hk : 2 ≤ k) :
    pairSumAtom 1 k = Reference.pairMass k := by
  rw [Reference.pairMass_eq hk]
  simp [pairSumAtom, hk, Nat.choose_one_right]

/-- The one-pair atom is totalized by the factor `b - 1`, which also records
the zero mass below the minimum two-letter total. -/
theorem pairSumAtom_one_total (b : ℕ) :
    pairSumAtom 1 b = ((b - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ b := by
  by_cases hb : 2 ≤ b
  · rw [pairSumAtom_one hb, Reference.pairMass_eq hb]
  · have hb' : b ≤ 1 := by omega
    unfold pairSumAtom
    simp [show ¬ 2 ≤ b by omega, hb']

/-- For a positive completed-pair prefix, the negative-binomial atom is
totalized by its binomial coefficient, including the out-of-support range. -/
theorem pairSumAtom_prefix_total {j r : ℕ} (hj : 1 < j) :
    pairSumAtom (j - 1) r =
      ((r - 1).choose (2 * j - 3) : ℝ) * (1 / 2 : ℝ) ^ r := by
  by_cases hr : 2 * (j - 1) ≤ r
  · unfold pairSumAtom
    rw [if_pos hr]
    congr 2
    have hidx : 2 * (j - 1) - 1 = 2 * j - 3 := by omega
    rw [hidx]
  · have hr' : r < 2 * (j - 1) := by omega
    unfold pairSumAtom
    rw [if_neg hr]
    have hchoose : (r - 1).choose (2 * j - 3) = 0 := by
      apply Nat.choose_eq_zero_of_lt
      omega
    rw [hchoose]
    simp

/-- The exact original-word event for a first crossing after `j` pairs with
overshoot `h`. The strict endpoint is expressed by the positive overshoot;
the preceding complete pair prefix remains at or below `s`. -/
def pairFirstPassageEvent (s j h : ℕ) (w : ValuationWord) : Prop :=
  w.length = 2 * j ∧ 0 < h ∧
    ValuationWord.total (w.take (2 * (j - 1))) ≤ s ∧ w.total = s + h

/-- Original probability of the strict first-passage event after `j` pairs. -/
noncomputable def pairFirstPassageProbability (s j h : ℕ) : ℝ :=
  Gated.probability (Reference.wordPMF (2 * j)) (pairFirstPassageEvent s j h)

/-- Original-word event that first passage after `j` pairs exceeds level `s`
by more than `H`. -/
def pairFirstPassageTailEvent (s j H : ℕ) (w : ValuationWord) : Prop :=
  w.length = 2 * j ∧
    ValuationWord.total (w.take (2 * (j - 1))) ≤ s ∧ s + H < w.total

/-- Original probability of a first-passage overshoot larger than `H` at a
fixed positive pair index. -/
noncomputable def pairFirstPassageTailProbability (s j H : ℕ) : ℝ :=
  Gated.probability (Reference.wordPMF (2 * j)) (pairFirstPassageTailEvent s j H)

/-- At a fixed positive first-passage index, a large overshoot is bounded by
the original tail of the final independent pair. -/
theorem pairFirstPassageTailProbability_le_pairTail {s j H : ℕ} (hj : 0 < j) :
    pairFirstPassageTailProbability s j H ≤ pairTailProbability H := by
  have hlen : 2 * j = 2 * (j - 1) + 2 := by omega
  have hmono :
      Gated.probability (Reference.wordPMF (2 * j)) (pairFirstPassageTailEvent s j H) ≤
        Gated.probability (Reference.wordPMF (2 * j))
          (fun w => H < ValuationWord.total (w.drop (2 * (j - 1)))) := by
    apply Gated.probability_mono_on_support
    intro w _ hw
    rcases hw with ⟨_, hprefix, hcross⟩
    have hsplit := List.take_append_drop (2 * (j - 1)) w
    have htotal : w.total = ValuationWord.total (w.take (2 * (j - 1))) +
        ValuationWord.total (w.drop (2 * (j - 1))) := by
      calc
        w.total = ValuationWord.total (w.take (2 * (j - 1)) ++
          w.drop (2 * (j - 1))) :=
          congrArg ValuationWord.total hsplit.symm
        _ = _ := ValuationWord.total_append _ _
    omega
  calc
    pairFirstPassageTailProbability s j H ≤
        Gated.probability (Reference.wordPMF (2 * j))
          (fun w => H < ValuationWord.total (w.drop (2 * (j - 1)))) := hmono
    _ = Gated.probability (Reference.wordPMF 2) (fun w => H < w.total) := by
      have hmap := Gated.probability_map
        (Reference.wordPMF (2 * (j - 1) + 2))
        (fun w => w.drop (2 * (j - 1))) (fun w => H < ValuationWord.total w)
      rw [Reference.wordPMF_map_drop] at hmap
      rw [hlen]
      exact hmap.symm
    _ = pairTailProbability H := rfl

/-- The level-`s` overshoot event viewed on a common word horizon. -/
def horizonTailEvent (s H i : ℕ) (w : ValuationWord) : Prop :=
  ValuationWord.total (w.take (2 * i)) ≤ s ∧
    s + H < ValuationWord.total (w.take (2 * (i + 1)))

/-- A word cannot have two distinct pair indices at which it first exceeds
the same level; this uses only monotonicity of prefix totals. -/
theorem horizonTailEvent_unique {s H i k : ℕ} {w : ValuationWord}
    (hi : horizonTailEvent s H i w) (hk : horizonTailEvent s H k w) : i = k := by
  rcases hi with ⟨hbefore_i, hcross_i⟩
  rcases hk with ⟨hbefore_k, hcross_k⟩
  rcases le_total i k with hik | hki
  · by_contra hne
    have hlt : i < k := lt_of_le_of_ne hik hne
    have hidx : 2 * (i + 1) ≤ 2 * k := by omega
    have hmono := ValuationWord.total_take_mono w hidx
    omega
  · by_contra hne
    have hlt : k < i := lt_of_le_of_ne hki (Ne.symm hne)
    have hidx : 2 * (k + 1) ≤ 2 * i := by omega
    have hmono := ValuationWord.total_take_mono w hidx
    omega

/-- On a sufficiently long common word, the lifted event is precisely the
fixed-index first-passage overshoot event on its corresponding prefix. -/
theorem pairFirstPassageTailEvent_take_iff {s H i : ℕ} {w : ValuationWord}
    (hlen : 2 * (i + 1) ≤ w.length) :
    pairFirstPassageTailEvent s (i + 1) H (w.take (2 * (i + 1))) ↔
      horizonTailEvent s H i w := by
  simp [pairFirstPassageTailEvent, horizonTailEvent, List.length_take,
    Nat.min_eq_left hlen, List.take_take]

/-- Projecting a common horizon to a positive pair index gives exactly its
original fixed-index overshoot-tail probability. -/
theorem horizonTailEvent_probability_eq {s H j N : ℕ} (hj : 0 < j)
    (hjN : j ≤ N) :
    Gated.probability (Reference.wordPMF (2 * N))
      (horizonTailEvent s H (j - 1)) = pairFirstPassageTailProbability s j H := by
  have hmap := Gated.probability_map (Reference.wordPMF (2 * N))
    (fun w => w.take (2 * j)) (pairFirstPassageTailEvent s j H)
  rw [Reference.wordPMF_map_take_of_le (show 2 * j ≤ 2 * N by omega)] at hmap
  unfold pairFirstPassageTailProbability
  rw [hmap]
  apply Gated.probability_congr_on_support
  intro w hw
  have hlen : w.length = 2 * N :=
    (Reference.wordPMF_mem_support_iff (2 * N) w).mp hw
  have hlong : 2 * ((j - 1) + 1) ≤ w.length := by omega
  have he := pairFirstPassageTailEvent_take_iff (s := s) (H := H)
    (i := j - 1) hlong
  have hj' : j - 1 + 1 = j := Nat.sub_add_cancel (by omega)
  simpa [hj'] using he.symm

/-- On a sufficiently long common word, the lifted strict-passage event is
the fixed-index original passage event on its corresponding prefix. -/
theorem pairPassageIndexEvent_take_iff {s i : ℕ} {w : ValuationWord}
    (hlen : 2 * (i + 1) ≤ w.length) :
    pairPassageIndexEvent s (i + 1) (w.take (2 * (i + 1))) ↔
      horizonTailEvent s 0 i w := by
  simp [pairPassageIndexEvent, horizonTailEvent, List.length_take,
    Nat.min_eq_left hlen, List.take_take]

/-- Projecting the common-horizon strict-passage event gives exactly its
original fixed-index passage probability. -/
theorem horizonPassageIndexEvent_probability_eq {s j N : ℕ} (hj : 0 < j)
    (hjN : j ≤ N) :
    Gated.probability (Reference.wordPMF (2 * N))
      (horizonTailEvent s 0 (j - 1)) = pairPassageIndexProbability s j := by
  have hmap := Gated.probability_map (Reference.wordPMF (2 * N))
    (fun w => w.take (2 * j)) (pairPassageIndexEvent s j)
  rw [Reference.wordPMF_map_take_of_le (show 2 * j ≤ 2 * N by omega)] at hmap
  unfold pairPassageIndexProbability
  rw [hmap]
  apply Gated.probability_congr_on_support
  intro w hw
  have hlen : w.length = 2 * N :=
    (Reference.wordPMF_mem_support_iff (2 * N) w).mp hw
  have hlong : 2 * ((j - 1) + 1) ≤ w.length := by omega
  have he := pairPassageIndexEvent_take_iff (s := s) (i := j - 1) hlong
  have hj' : j - 1 + 1 = j := Nat.sub_add_cancel (by omega)
  simpa [hj'] using he.symm

/-- The original-word horizontal exceptional event, evaluated at the
deterministic common first-passage horizon. -/
def stoppedPassageIndexHighEvent (s : ℕ) (w : ValuationWord) : Prop :=
  ∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w ∧
    (s : ℝ) / 4 + Real.sqrt (s : ℝ) + 1 < (i : ℕ) + 1

/-- Original probability of the common-horizon horizontal exceptional event. -/
noncomputable def stoppedPassageIndexHighProbability (s : ℕ) : ℝ :=
  Gated.probability (Reference.wordPMF (2 * (s / 2 + 1)))
    (stoppedPassageIndexHighEvent s)

/-- The original horizontal exception is the finite disjoint sum of its
fixed-index original probabilities. -/
theorem stoppedPassageIndexHighProbability_eq_sum (s : ℕ) :
    stoppedPassageIndexHighProbability s =
      ∑ i : Fin (s / 2 + 1), if
        (s : ℝ) / 4 + Real.sqrt (s : ℝ) + 1 < (i : ℕ) + 1 then
          pairPassageIndexProbability s (i + 1) else 0 := by
  let N := s / 2 + 1
  let G : Fin N → ValuationWord → Prop := fun i w =>
    horizonTailEvent s 0 i w ∧
      (s : ℝ) / 4 + Real.sqrt (s : ℝ) + 1 < (i : ℕ) + 1
  have hunique : ∀ i k w, G i w → G k w → i = k := by
    intro i k w hi hk
    apply Fin.ext
    exact horizonTailEvent_unique hi.1 hk.1
  calc
    stoppedPassageIndexHighProbability s =
        Gated.probability (Reference.wordPMF (2 * N)) (fun w => ∃ i, G i w) := by
          rfl
    _ = ∑ i, Gated.probability (Reference.wordPMF (2 * N)) (G i) :=
      Gated.probability_union _ G hunique
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (s : ℝ) / 4 + Real.sqrt (s : ℝ) + 1 < (i : ℕ) + 1
      · simp only [G, hi, and_true]
        exact horizonPassageIndexEvent_probability_eq (s := s)
          (j := i + 1) (N := N) (by omega) (by omega)
      · have hlow : ¬ (s : ℝ) / 4 + Real.sqrt (s : ℝ) < (i : ℕ) := by
          intro hlow
          apply hi
          norm_num at hlow ⊢
          linarith
        simp [G, hlow, Gated.probability]

/-- The stopped overshoot tail on its deterministic finite pair horizon. -/
def stoppedTailEvent (s H : ℕ) (w : ValuationWord) : Prop :=
  ∃ i : Fin (s / 2 + 1), horizonTailEvent s H i w

/-- Original probability of the finite-horizon stopped overshoot tail. -/
noncomputable def stoppedTailProbability (s H : ℕ) : ℝ :=
  Gated.probability (Reference.wordPMF (2 * (s / 2 + 1))) (stoppedTailEvent s H)

/-- The stopped overshoot-tail probability is the finite disjoint sum of its
fixed-index original probabilities. -/
theorem stoppedTailProbability_eq_sum (s H : ℕ) :
    stoppedTailProbability s H =
      ∑ i : Fin (s / 2 + 1), pairFirstPassageTailProbability s (i + 1) H := by
  let N := s / 2 + 1
  let G : Fin N → ValuationWord → Prop := fun i w => horizonTailEvent s H i w
  have hunique : ∀ i k w, G i w → G k w → i = k := by
    intro i k w hi hk
    apply Fin.ext
    exact horizonTailEvent_unique hi hk
  calc
    stoppedTailProbability s H =
        Gated.probability (Reference.wordPMF (2 * N)) (fun w => ∃ i, G i w) := by
          rfl
    _ = ∑ i, Gated.probability (Reference.wordPMF (2 * N)) (G i) :=
      Gated.probability_union _ G hunique
    _ = ∑ i : Fin N, pairFirstPassageTailProbability s (i + 1) H := by
      apply Finset.sum_congr rfl
      intro i _
      exact horizonTailEvent_probability_eq (s := s) (H := H) (j := i + 1)
        (N := N) (by omega) (by omega)

/-- At level zero the only stopped pair is the first pair, so its tail is the
original one-pair tail. -/
theorem pairFirstPassageTailProbability_zero_one_eq_pairTail (H : ℕ) :
    pairFirstPassageTailProbability 0 1 H = pairTailProbability H := by
  unfold pairFirstPassageTailProbability pairTailProbability
  apply Gated.probability_congr_on_support
  intro w hw
  have hlen : w.length = 2 :=
    (Reference.wordPMF_mem_support_iff 2 w).mp hw
  simp [pairFirstPassageTailEvent, hlen, ValuationWord.total]

/-- The level-zero stopped tail is the original one-pair tail. -/
theorem stoppedTailProbability_zero_eq_pairTail (H : ℕ) :
    stoppedTailProbability 0 H = pairTailProbability H := by
  rw [stoppedTailProbability_eq_sum]
  simp [pairFirstPassageTailProbability_zero_one_eq_pairTail]

/-- The exact `(j,h)` first-passage event viewed at a common finite horizon. -/
def horizonJointEvent (s h i : ℕ) (w : ValuationWord) : Prop :=
  0 < h ∧
    ValuationWord.total (w.take (2 * i)) ≤ s ∧
    ValuationWord.total (w.take (2 * (i + 1))) = s + h

/-- Two exact joint crossings on one word have the same pair index. -/
theorem horizonJointEvent_unique {s h i k : ℕ} {w : ValuationWord}
    (hi : horizonJointEvent s h i w) (hk : horizonJointEvent s h k w) : i = k := by
  apply horizonTailEvent_unique (s := s) (H := 0)
  · rcases hi with ⟨hh, hbefore, htotal⟩
    exact ⟨hbefore, by omega⟩
  · rcases hk with ⟨hh, hbefore, htotal⟩
    exact ⟨hbefore, by omega⟩

/-- On a sufficiently long common word, an exact joint crossing is precisely
the fixed-index first-passage event on its corresponding prefix. -/
theorem pairFirstPassageEvent_take_iff {s h i : ℕ} {w : ValuationWord}
    (hlen : 2 * (i + 1) ≤ w.length) :
    pairFirstPassageEvent s (i + 1) h (w.take (2 * (i + 1))) ↔
      horizonJointEvent s h i w := by
  simp [pairFirstPassageEvent, horizonJointEvent, List.length_take,
    Nat.min_eq_left hlen, List.take_take]

/-- Projecting a common horizon to a positive pair index gives exactly its
original exact-joint first-passage probability. -/
theorem horizonJointEvent_probability_eq {s h j N : ℕ} (hj : 0 < j)
    (hjN : j ≤ N) :
    Gated.probability (Reference.wordPMF (2 * N))
      (horizonJointEvent s h (j - 1)) = pairFirstPassageProbability s j h := by
  have hmap := Gated.probability_map (Reference.wordPMF (2 * N))
    (fun w => w.take (2 * j)) (pairFirstPassageEvent s j h)
  rw [Reference.wordPMF_map_take_of_le (show 2 * j ≤ 2 * N by omega)] at hmap
  unfold pairFirstPassageProbability
  rw [hmap]
  apply Gated.probability_congr_on_support
  intro w hw
  have hlen : w.length = 2 * N :=
    (Reference.wordPMF_mem_support_iff (2 * N) w).mp hw
  have hlong : 2 * ((j - 1) + 1) ≤ w.length := by omega
  have he := pairFirstPassageEvent_take_iff (s := s) (h := h)
    (i := j - 1) hlong
  have hj' : j - 1 + 1 = j := Nat.sub_add_cancel (by omega)
  simpa [hj'] using he.symm

/-- The exact stopped joint event at its deterministic finite pair horizon. -/
def stoppedJointEvent (s h : ℕ) (w : ValuationWord) : Prop :=
  ∃ i : Fin (s / 2 + 1), horizonJointEvent s h i w

/-- Original probability of the finite-horizon stopped exact-joint event. -/
noncomputable def stoppedJointProbability (s h : ℕ) : ℝ :=
  Gated.probability (Reference.wordPMF (2 * (s / 2 + 1))) (stoppedJointEvent s h)

/-- The stopped exact-joint probability is the finite disjoint sum of its
fixed-index original probabilities. -/
theorem stoppedJointProbability_eq_sum (s h : ℕ) :
    stoppedJointProbability s h =
      ∑ i : Fin (s / 2 + 1), pairFirstPassageProbability s (i + 1) h := by
  let N := s / 2 + 1
  let G : Fin N → ValuationWord → Prop := fun i w => horizonJointEvent s h i w
  have hunique : ∀ i k w, G i w → G k w → i = k := by
    intro i k w hi hk
    apply Fin.ext
    exact horizonJointEvent_unique hi hk
  calc
    stoppedJointProbability s h =
        Gated.probability (Reference.wordPMF (2 * N)) (fun w => ∃ i, G i w) := by
          rfl
    _ = ∑ i, Gated.probability (Reference.wordPMF (2 * N)) (G i) :=
      Gated.probability_union _ G hunique
    _ = ∑ i : Fin N, pairFirstPassageProbability s (i + 1) h := by
      apply Finset.sum_congr rfl
      intro i _
      exact horizonJointEvent_probability_eq (s := s) (h := h) (j := i + 1)
        (N := N) (by omega) (by omega)

/-- A stopped-tail word has a unique exact overshoot excess above its tail
threshold. -/
theorem stoppedTailEvent_iff_exists_joint {s H : ℕ} {w : ValuationWord} :
    stoppedTailEvent s H w ↔ ∃ k : ℕ, stoppedJointEvent s (H + 1 + k) w := by
  constructor
  · rintro ⟨i, hbefore, hcross⟩
    let k := ValuationWord.total (w.take (2 * (i + 1))) - (s + H + 1)
    refine ⟨k, i, ?_, hbefore, ?_⟩
    · dsimp [k]
      omega
    · dsimp [k]
      omega
  · rintro ⟨k, i, hh, hbefore, htotal⟩
    exact ⟨i, hbefore, by omega⟩

/-- Two stopped-joint events lying above the same tail threshold have the
same overshoot excess. -/
theorem stoppedJointEvent_tail_unique {s H k l : ℕ} {w : ValuationWord}
    (hk : stoppedJointEvent s (H + 1 + k) w)
    (hl : stoppedJointEvent s (H + 1 + l) w) : k = l := by
  rcases hk with ⟨i, hki, hbefore_i, htotal_i⟩
  rcases hl with ⟨j, hlj, hbefore_j, htotal_j⟩
  have hi : horizonTailEvent s H i w := ⟨hbefore_i, by omega⟩
  have hj : horizonTailEvent s H j w := ⟨hbefore_j, by omega⟩
  have hij : i = j := by
    apply Fin.ext
    exact horizonTailEvent_unique hi hj
  subst j
  omega

/-- The stopped tail is the countable disjoint union of exact stopped-joint
events with overshoot `H + 1 + k`. -/
theorem stoppedTailProbability_eq_tsum_joint (s H : ℕ) :
    stoppedTailProbability s H = ∑' k : ℕ, stoppedJointProbability s (H + 1 + k) := by
  unfold stoppedTailProbability stoppedJointProbability
  have he :
      Gated.probability (Reference.wordPMF (2 * (s / 2 + 1))) (stoppedTailEvent s H) =
        Gated.probability (Reference.wordPMF (2 * (s / 2 + 1)))
          (fun w => ∃ k : ℕ, stoppedJointEvent s (H + 1 + k) w) := by
    apply Gated.probability_congr_on_support
    intro w _
    exact stoppedTailEvent_iff_exists_joint
  rw [he, Gated.probability_iUnion]
  intro k l w hk hl
  exact stoppedJointEvent_tail_unique hk hl

/-- A strict-passage word has exactly the positive overshoot determined by
its terminal total. -/
theorem pairPassageIndexEvent_iff_exists_overshoot {s j : ℕ} {w : ValuationWord} :
    pairPassageIndexEvent s j w ↔ ∃ h : ℕ, pairFirstPassageEvent s j h w := by
  constructor
  · rintro ⟨hlen, hprefix, hcross⟩
    let h : ℕ := w.total - s
    refine ⟨h, hlen, ?_, hprefix, ?_⟩
    · dsimp [h]
      omega
    · dsimp [h]
      omega
  · rintro ⟨h, hlen, hh, hprefix, htotal⟩
    exact ⟨hlen, hprefix, by omega⟩

/-- At height zero, a strict passage is exactly the first pair's total event. -/
theorem pairFirstPassageProbability_zero_one (h : ℕ) (hh : 0 < h) :
    pairFirstPassageProbability 0 1 h = pairSumProbability 1 h := by
  unfold pairFirstPassageProbability pairSumProbability
  apply Gated.probability_congr_on_support
  intro w hw
  have hlen : w.length = 2 := by
    by_contra hne
    exact hw (Reference.wordPMF_eq_zero_of_length_ne 2 w hne)
  simp [pairFirstPassageEvent, hlen, hh, ValuationWord.total]

/-- The zero-height, first-pair branch agrees with `(E.joint)` on its
nonempty support. -/
theorem pairFirstPassageProbability_zero_one_joint {h : ℕ} (hh : 2 ≤ h) :
    pairFirstPassageProbability 0 1 h = passageJointAtom 0 1 h := by
  rw [pairFirstPassageProbability_zero_one h (by omega)]
  calc
    pairSumProbability 1 h = pairSumAtom 1 h := by
      have hatom := pairSumProbability_eq_pairSumAtom_succ (j := 1) (k := h - 1)
        (by omega) (by omega)
      have hcancel : h - 1 + 1 = h := Nat.sub_add_cancel (by omega)
      simpa [hcancel] using hatom
    _ = passageJointAtom 0 1 h := by
      unfold pairSumAtom passageJointAtom
      simp [hh]
      ring

/-- For one pair, the strict-passage event is precisely its final total event. -/
theorem pairFirstPassageProbability_one_eq_pairSum (s h : ℕ) (hh : 0 < h) :
    pairFirstPassageProbability s 1 h = pairSumProbability 1 (s + h) := by
  unfold pairFirstPassageProbability pairSumProbability
  apply Gated.probability_congr_on_support
  intro w hw
  have hlen : w.length = 2 := by
    by_contra hne
    exact hw (Reference.wordPMF_eq_zero_of_length_ne 2 w hne)
  simp [pairFirstPassageEvent, hlen, hh, ValuationWord.total]

/-- At one pair, the strict-passage probability has the full `(E.joint)`
formula for every height and every supported positive overshoot. -/
theorem pairFirstPassageProbability_one_joint {s h : ℕ} (hh : 0 < h)
    (hsupport : 2 ≤ s + h) :
    pairFirstPassageProbability s 1 h = passageJointAtom s 1 h := by
  rw [pairFirstPassageProbability_one_eq_pairSum s h hh]
  have hatom := pairSumProbability_eq_pairSumAtom_succ (j := 1) (k := s + h - 1)
    (by omega) (by omega)
  have hcancel : s + h - 1 + 1 = s + h := Nat.sub_add_cancel (by omega)
  rw [← hcancel]
  rw [hatom]
  unfold pairSumAtom passageJointAtom
  simp
  have hsub : s + h - 1 = s + (h - 1) := by omega
  rw [hsub]
  have hinner : 1 ≤ s + (h - 1) := by omega
  rw [if_pos hinner]
  norm_num [Nat.choose_one_right]
  have hh' : h = (h - 1) + 1 := by omega
  rw [hh', pow_add]
  have hminus : h - 1 + 1 - 1 = h - 1 := by omega
  rw [hminus]
  norm_num [← pow_add]
  ring

/-- At a positive pair index, the strict event splits into the total of its
completed prefix and the total of its final independent pair. -/
theorem pairFirstPassageEvent_take_drop {s j h : ℕ} {w : ValuationWord}
    (hj : 0 < j) (hlen : w.length = 2 * j) :
    pairFirstPassageEvent s j h w ↔
      0 < h ∧ ValuationWord.total (w.take (2 * (j - 1))) ≤ s ∧
        (w.drop (2 * (j - 1))).length = 2 ∧
        ValuationWord.total (w.take (2 * (j - 1))) +
          ValuationWord.total (w.drop (2 * (j - 1))) = s + h := by
  rw [pairFirstPassageEvent]
  have hprefix : 2 * (j - 1) ≤ w.length := by omega
  have hsplit := List.take_append_drop (2 * (j - 1)) w
  have htotal : ValuationWord.total w =
      ValuationWord.total (w.take (2 * (j - 1))) +
        ValuationWord.total (w.drop (2 * (j - 1))) := by
    calc
      ValuationWord.total w =
          ValuationWord.total (w.take (2 * (j - 1)) ++ w.drop (2 * (j - 1))) :=
        congrArg ValuationWord.total hsplit.symm
      _ = _ := ValuationWord.total_append _ _
  have hdrop : (w.drop (2 * (j - 1))).length = 2 := by
    rw [List.length_drop, hlen]
    omega
  constructor
  · rintro ⟨_, hh, hp, ht⟩
    exact ⟨hh, hp, hdrop, by simpa [htotal] using ht⟩
  · rintro ⟨hh, hp, _, ht⟩
    exact ⟨hlen, hh, hp, by rw [htotal]; exact ht⟩

/-- The event on the independent prefix/final-pair product law. -/
def pairFirstPassageSplit (s h : ℕ) (uv : ValuationWord × ValuationWord) : Prop :=
  0 < h ∧ uv.1.total ≤ s ∧ uv.2.length = 2 ∧ uv.1.total + uv.2.total = s + h

/-- The strict event transports through the actual independent take/drop
factorization of the original word law. -/
theorem pairFirstPassageProbability_eq_product {s j h : ℕ} (hj : 0 < j) :
    pairFirstPassageProbability s j h =
      Gated.probability
        ((Reference.wordPMF (2 * (j - 1))).bind
          (fun u => (Reference.wordPMF 2).map (fun v => (u, v))))
        (pairFirstPassageSplit s h) := by
  have hlen : 2 * j = 2 * (j - 1) + 2 := by omega
  rw [pairFirstPassageProbability, hlen]
  have hmap := Gated.probability_map (Reference.wordPMF (2 * (j - 1) + 2))
    (fun w => (w.take (2 * (j - 1)), w.drop (2 * (j - 1))))
    (pairFirstPassageSplit s h)
  rw [Reference.wordPMF_map_take_drop] at hmap
  rw [hmap]
  apply Gated.probability_congr_on_support
  intro w hw
  have hwlen : w.length = 2 * (j - 1) + 2 := by
    by_contra hne
    exact hw (Reference.wordPMF_eq_zero_of_length_ne _ w hne)
  have hwlen' : w.length = 2 * j := by omega
  simpa [pairFirstPassageSplit] using
    (pairFirstPassageEvent_take_drop (s := s) (h := h) hj hwlen')

/-- The total-level version of the strict first-passage condition. -/
def pairFirstPassageTotals (s h : ℕ) (rb : ℕ × ℕ) : Prop :=
  0 < h ∧ rb.1 ≤ s ∧ rb.1 + rb.2 = s + h

/-- The `r`-th finite component of the total-level strict-passage event. -/
def pairFirstPassageComponent (s h : ℕ) (r : Fin (s + 1))
    (rb : ℕ × ℕ) : Prop :=
  0 < h ∧ rb.1 = r ∧ rb.2 = s + h - r

/-- The total-level strict-passage event is a disjoint finite union indexed
by the completed-prefix total. -/
theorem pairFirstPassageTotals_eq_finite_sum (s h : ℕ) (p : PMF (ℕ × ℕ)) :
    Gated.probability p (pairFirstPassageTotals s h) =
      ∑ r : Fin (s + 1),
        Gated.probability p (pairFirstPassageComponent s h r) := by
  let G : Fin (s + 1) → ℕ × ℕ → Prop := pairFirstPassageComponent s h
  have hunique : ∀ i j rb, G i rb → G j rb → i = j := by
    intro i j rb hi hj
    simp only [G, pairFirstPassageComponent] at hi hj
    omega
  have hprob := Gated.probability_union p G hunique
  have hUnion : (fun rb => ∃ r, G r rb) = pairFirstPassageTotals s h := by
    funext rb
    apply propext
    constructor
    · rintro ⟨r, hh, hr, hb⟩
      simp only [pairFirstPassageTotals]
      constructor
      · exact hh
      constructor
      · omega
      · omega
    · rintro ⟨hh, hr, htotal⟩
      let r : Fin (s + 1) := ⟨rb.1, by omega⟩
      refine ⟨r, hh, rfl, ?_⟩
      change rb.2 = s + h - rb.1
      omega
  rw [hUnion] at hprob
  exact hprob

/-- Each finite strict-passage component is the product of the selected
prefix-total atom and the selected final-pair atom. -/
theorem pairFirstPassageComponent_eq_product (p q : PMF ℕ)
    {s h : ℕ} (r : Fin (s + 1)) (hh : 0 < h) :
    Gated.probability (p.bind fun a => q.map (fun b => (a, b)))
        (pairFirstPassageComponent s h r) =
      (p r).toReal * (q (s + h - r)).toReal := by
  let b := s + h - r
  have hevent : pairFirstPassageComponent s h r =
      (fun rb => rb = (r.val, b)) := by
    funext rb
    apply propext
    simp only [pairFirstPassageComponent]
    constructor
    · rintro ⟨_, hr, hb⟩
      exact Prod.ext hr hb
    · intro hpoint
      subst rb
      exact ⟨hh, rfl, rfl⟩
  rw [hevent, gatedProbability_eq_point, bind_map_pair_apply]
  rw [ENNReal.toReal_mul]

/-- The `r`-component is the product of its two original pair-total
probabilities. -/
theorem pairFirstPassageComponent_eq_pairSumProduct {s j h : ℕ}
    (r : Fin (s + 1)) (hh : 0 < h) :
    Gated.probability
        ((pairTotalPMF (j - 1)).bind
          (fun a => (pairTotalPMF 1).map (fun b => (a, b))))
        (pairFirstPassageComponent s h r) =
      pairSumProbability (j - 1) r * pairSumProbability 1 (s + h - r) := by
  rw [pairFirstPassageComponent_eq_product _ _ r hh]
  rw [pairTotalPMF_toReal, pairTotalPMF_toReal]

/-- Under the independent prefix/final-pair law, the strict event depends
only on the two total valuations. -/
theorem pairFirstPassage_product_totals {s j h : ℕ} :
    Gated.probability
        ((Reference.wordPMF (2 * (j - 1))).bind
          (fun u => (Reference.wordPMF 2).map (fun v => (u, v))))
        (pairFirstPassageSplit s h) =
      Gated.probability
        ((pairTotalPMF (j - 1)).bind
          (fun r => (pairTotalPMF 1).map (fun b => (r, b))))
        (pairFirstPassageTotals s h) := by
  rw [← pairProductTotalPMF]
  rw [Gated.probability_map]
  apply Gated.probability_congr_on_support
  intro uv huv
  have hlen : uv.2.length = 2 := by
    change uv ∈ ((Reference.wordPMF (2 * (j - 1))).bind
      (fun u => (Reference.wordPMF 2).map (fun v => (u, v)))).support at huv
    rw [PMF.mem_support_bind_iff] at huv
    obtain ⟨u, hu, huv⟩ := huv
    rw [PMF.mem_support_map_iff] at huv
    obtain ⟨w, hw, hwv⟩ := huv
    subst uv
    simpa using (Reference.wordPMF_mem_support_iff 2 w).mp hw
  simp [pairFirstPassageSplit, pairFirstPassageTotals, hlen]

/-- The strict first-passage probability is exactly a predicate on the
prefix and final-pair totals under their original-law product PMF. -/
theorem pairFirstPassageProbability_eq_totals {s j h : ℕ} (hj : 0 < j) :
    pairFirstPassageProbability s j h =
      Gated.probability
        ((pairTotalPMF (j - 1)).bind
          (fun r => (pairTotalPMF 1).map (fun b => (r, b))))
        (pairFirstPassageTotals s h) := by
  rw [pairFirstPassageProbability_eq_product hj]
  exact pairFirstPassage_product_totals

/-- The original-law strict-passage probability is an exact finite sum over
the total valuation of the completed prefix. -/
theorem pairFirstPassageProbability_eq_finite_sum {s j h : ℕ} (hj : 0 < j) :
    pairFirstPassageProbability s j h =
      ∑ r : Fin (s + 1),
        Gated.probability
          ((pairTotalPMF (j - 1)).bind
            (fun a => (pairTotalPMF 1).map (fun b => (a, b))))
          (pairFirstPassageComponent s h r) := by
  rw [pairFirstPassageProbability_eq_totals hj]
  exact pairFirstPassageTotals_eq_finite_sum s h _

theorem valuationWord_length_le_total (w : ValuationWord) : w.length ≤ w.total := by
  induction w with
  | nil => simp [ValuationWord.total]
  | cons a w ih =>
      change w.length + 1 ≤ (a : ℕ) + ValuationWord.total w
      have ha : 1 ≤ (a : ℕ) := a.property
      omega

/-- Every word at the deterministic `floor(s / 2) + 1` pair horizon has a
strict first-passage pair, provided it has the reference horizon length. -/
theorem exists_horizonTailEvent_zero_of_length {s : ℕ} {w : ValuationWord}
    (hlen : w.length = 2 * (s / 2 + 1)) :
    ∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w := by
  let N := s / 2 + 1
  let P : ℕ → Prop := fun k => s < ValuationWord.total (w.take (2 * k))
  have hfinal : P N := by
    have htake : w.take (2 * N) = w := by
      exact List.take_of_length_le (by dsimp [N]; omega)
    have htotal := valuationWord_length_le_total w
    rw [hlen] at htotal
    dsimp [P]
    rw [htake]
    omega
  let k := Nat.find ⟨N, hfinal⟩
  have hk : P k := Nat.find_spec ⟨N, hfinal⟩
  have hkN : k ≤ N := Nat.find_min' ⟨N, hfinal⟩ hfinal
  have hkpos : 0 < k := by
    by_contra hnot
    have hkzero : k = 0 := by omega
    have hk' := hk
    rw [hkzero] at hk'
    simp [P, ValuationWord.total] at hk'
  let i : Fin N := ⟨k - 1, by omega⟩
  refine ⟨i, ?_⟩
  refine ⟨?_, ?_⟩
  · change ValuationWord.total (w.take (2 * (k - 1))) ≤ s
    by_contra hnot
    have hprev : P (k - 1) := by
      dsimp [P]
      omega
    have hmin := Nat.find_min' ⟨N, hfinal⟩ hprev
    omega
  · have hkeq : k - 1 + 1 = k := by omega
    simpa [i, hkeq] using hk

/-- A pair-total event below the minimum possible valuation has zero original
probability. -/
theorem pairSumProbability_eq_zero_of_lt (j k : ℕ) (hk : k < 2 * j) :
    pairSumProbability j k = 0 := by
  unfold pairSumProbability
  have hzero : Gated.probability (Reference.wordPMF (2 * j))
      (fun w => w.total = k) =
      Gated.probability (Reference.wordPMF (2 * j)) (fun _ => False) := by
    apply Gated.probability_congr_on_support
    intro w hw
    have hlen : w.length = 2 * j := by
      apply (Reference.wordPMF_mem_support_iff (2 * j) w).mp
      exact hw
    have htotal := valuationWord_length_le_total w
    rw [hlen] at htotal
    constructor
    · intro heq
      omega
    · intro hf
      exact False.elim hf
  rw [hzero]
  simp [Gated.probability]

/-- The exact negative-binomial atom formula holds at every total; the
out-of-support branch is explicitly zero. -/
theorem pairSumProbability_eq_pairSumAtom {j k : ℕ} (hj : 0 < j) :
    pairSumProbability j k = pairSumAtom j k := by
  by_cases hsupport : 2 * j ≤ k
  · have hsucc : k = (k - 1) + 1 := by omega
    calc
      pairSumProbability j k = pairSumProbability j ((k - 1) + 1) := by rw [← hsucc]
      _ = pairSumAtom j ((k - 1) + 1) :=
        pairSumProbability_eq_pairSumAtom_succ hj (by omega)
      _ = pairSumAtom j k := by rw [← hsucc]
  · have hk : k < 2 * j := by omega
    rw [pairSumProbability_eq_zero_of_lt j k hk]
    simp [pairSumAtom, hsupport]

/-- For a non-initial pair index, strict first-passage probability is the
finite convolution of the two exact original pair-total atoms. -/
theorem pairFirstPassageProbability_eq_pairSumAtom_sum {s j h : ℕ}
    (hj : 1 < j) (hh : 0 < h) :
    pairFirstPassageProbability s j h =
      ∑ r : Fin (s + 1),
        pairSumAtom (j - 1) r * pairSumAtom 1 (s + h - r) := by
  rw [pairFirstPassageProbability_eq_finite_sum (by omega)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [pairFirstPassageComponent_eq_pairSumProduct r hh,
    pairSumProbability_eq_pairSumAtom (by omega),
    pairSumProbability_eq_pairSumAtom (by omega)]

/-- The exact atom convolution collapses to the Appendix E coefficient for a
positive completed-pair prefix. -/
theorem pairSumAtom_convolution {s j h : ℕ} (hj : 1 < j) (hh : 0 < h) :
    ∑ r : Fin (s + 1),
        pairSumAtom (j - 1) r * pairSumAtom 1 (s + h - r) =
      (1 / 2 : ℝ) ^ (s + h) *
        (((h - 1) * s.choose (2 * j - 2) + s.choose (2 * j - 1) : ℕ) : ℝ) := by
  have hterm (r : Fin (s + 1)) :
      pairSumAtom (j - 1) r * pairSumAtom 1 (s + h - r) =
        (((r.val - 1).choose (2 * j - 3) * (s + h - r - 1) : ℕ) : ℝ) *
          (1 / 2 : ℝ) ^ (s + h) := by
    rw [pairSumAtom_prefix_total hj, pairSumAtom_one_total]
    have hrs : (r : ℕ) ≤ s := by omega
    have hexp : r + (s + h - r) = s + h := by omega
    calc
      ((r.val - 1).choose (2 * j - 3) : ℝ) * (1 / 2 : ℝ) ^ r.val *
          (((s + h - r - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (s + h - r)) =
          (((r.val - 1).choose (2 * j - 3) : ℝ) * ((s + h - r - 1 : ℕ) : ℝ)) *
            ((1 / 2 : ℝ) ^ r.val * (1 / 2 : ℝ) ^ (s + h - r)) := by ring
      _ = (((r.val - 1).choose (2 * j - 3) : ℝ) * ((s + h - r - 1 : ℕ) : ℝ)) *
            (1 / 2 : ℝ) ^ (s + h) := by rw [← pow_add, hexp]
      _ = (((r.val - 1).choose (2 * j - 3) * (s + h - r - 1) : ℕ) : ℝ) *
            (1 / 2 : ℝ) ^ (s + h) := by norm_cast
  rw [Finset.sum_congr rfl (fun r _ => hterm r)]
  rw [← Finset.sum_mul]
  rw [← Nat.cast_sum]
  have hsum :
      (∑ x : Fin (s + 1),
          (x.val - 1).choose (2 * j - 3) * (s + h - x.val - 1)) =
        ∑ r ∈ Finset.range (s + 1),
          (r - 1).choose (2 * j - 3) * (s + h - r - 1) :=
    Fin.sum_univ_eq_sum_range
      (fun r : ℕ => (r - 1).choose (2 * j - 3) * (s + h - r - 1)) (s + 1)
  rw [hsum]
  rw [shifted_joint_coefficient_sum s (2 * j - 3) h (by omega) hh]
  norm_num
  have hidx1 : 2 * j - 3 + 1 = 2 * j - 2 := by omega
  have hidx2 : 2 * j - 3 + 2 = 2 * j - 1 := by omega
  rw [hidx1, hidx2]
  ring

/-- The exact Appendix E joint first-passage atom for every positive
overshoot after at least two pairs. -/
theorem pairFirstPassageProbability_joint {s j h : ℕ} (hj : 1 < j)
    (hh : 0 < h) :
    pairFirstPassageProbability s j h = passageJointAtom s j h := by
  rw [pairFirstPassageProbability_eq_pairSumAtom_sum hj hh,
    pairSumAtom_convolution hj hh]
  unfold passageJointAtom
  rw [Nat.mul_comm (h - 1) (s.choose (2 * j - 2))]
  norm_cast

/-- The one-pair joint atom, including its unique unsupported boundary. -/
theorem pairFirstPassageProbability_one_joint_total {s h : ℕ} (hh : 0 < h) :
    pairFirstPassageProbability s 1 h = passageJointAtom s 1 h := by
  by_cases hsupport : 2 ≤ s + h
  · exact pairFirstPassageProbability_one_joint hh hsupport
  · have hsmall : s + h < 2 := by omega
    have hs : s = 0 := by omega
    have hh1 : h = 1 := by omega
    subst s
    subst h
    rw [pairFirstPassageProbability_one_eq_pairSum 0 1 (by omega)]
    rw [pairSumProbability_eq_zero_of_lt 1 1 (by omega)]
    norm_num [passageJointAtom]

/-- The exact Appendix E joint first-passage atom at every positive pair
index and positive overshoot. -/
theorem pairFirstPassageProbability_joint_total {s j h : ℕ} (hj : 0 < j)
    (hh : 0 < h) :
    pairFirstPassageProbability s j h = passageJointAtom s j h := by
  rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (by omega : j ≠ 0)) with rfl | hj'
  · exact pairFirstPassageProbability_one_joint_total hh
  · exact pairFirstPassageProbability_joint hj' hh

/-- At a positive overshoot, the stopped probability is the finite sum of the
exact Appendix E joint atoms. -/
theorem stoppedJointProbability_eq_atom_sum {s h : ℕ} (hh : 0 < h) :
    stoppedJointProbability s h =
      ∑ i : Fin (s / 2 + 1), passageJointAtom s (i + 1) h := by
  rw [stoppedJointProbability_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact pairFirstPassageProbability_joint_total (by omega) hh

/-- At a positive level and overshoot, summing the exact stopped joint atoms
leaves the common geometric factor times the normalized even Pascal mass. -/
theorem passageJointAtom_sum {s h : ℕ} (hs : 0 < s) (hh : 0 < h) :
    (∑ i : Fin (s / 2 + 1), passageJointAtom s (i + 1) h) =
      (1 / 2 : ℝ) ^ (s + h) * ((h : ℝ) * evenChooseSum s) := by
  rw [show (∑ i : Fin (s / 2 + 1), passageJointAtom s (i + 1) h) =
      ∑ i ∈ Finset.range (s / 2 + 1), passageJointAtom s (i + 1) h by
    exact Fin.sum_univ_eq_sum_range
      (fun i : ℕ => passageJointAtom s (i + 1) h) (s / 2 + 1)]
  have hterm (i : ℕ) :
      passageJointAtom s (i + 1) h =
        (1 / 2 : ℝ) ^ (s + h) *
          ((s.choose (2 * i) : ℝ) * ((h - 1 : ℕ) : ℝ) + s.choose (2 * i + 1)) := by
    unfold passageJointAtom
    congr 3
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [← Finset.mul_sum, pairIndexJointCoefficient_sum hs hh]

/-- The normalized even Pascal mass cancels the level part of the common
geometric factor. -/
theorem evenChooseSum_geometric_normalization {s h : ℕ} (hs : 0 < s) :
    (1 / 2 : ℝ) ^ (s + h) * ((h : ℝ) * evenChooseSum s) =
      (h : ℝ) * (1 / 2 : ℝ) ^ (h + 1) := by
  have hmassNat := two_mul_evenChooseSum_eq_pow hs
  have hmass : (2 : ℝ) * evenChooseSum s = (2 : ℝ) ^ s := by
    exact_mod_cast hmassNat
  have hmul : (1 / 2 : ℝ) ^ s * ((2 : ℝ) * evenChooseSum s) = 1 := by
    rw [hmass, ← mul_pow]
    norm_num
  have hC : (1 / 2 : ℝ) ^ s * evenChooseSum s = 1 / 2 := by
    linarith
  rw [pow_add]
  calc
    (1 / 2 : ℝ) ^ s * (1 / 2 : ℝ) ^ h * ((h : ℝ) * evenChooseSum s) =
        (h : ℝ) * (1 / 2 : ℝ) ^ h * ((1 / 2 : ℝ) ^ s * evenChooseSum s) := by ring
    _ = (h : ℝ) * (1 / 2 : ℝ) ^ h * (1 / 2 : ℝ) := by rw [hC]
    _ = (h : ℝ) * (1 / 2 : ℝ) ^ (h + 1) := by
      rw [pow_succ]
      ring

/-- The positive-level stopped overshoot has its exact Appendix E marginal. -/
theorem stoppedJointProbability_eq_overshoot_mass {s h : ℕ}
    (hs : 0 < s) (hh : 0 < h) :
    stoppedJointProbability s h = (h : ℝ) * (1 / 2 : ℝ) ^ (h + 1) := by
  rw [stoppedJointProbability_eq_atom_sum hh, passageJointAtom_sum hs hh,
    evenChooseSum_geometric_normalization hs]

/-- The weighted geometric series used for the stopped-overshoot tail. -/
theorem tsum_add_one_mul_geometric_two :
    (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) = 4 := by
  have hlinear := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
  have hgeom := hasSum_geometric_two
  have hsum := hlinear.add hgeom
  calc
    (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) =
        ∑' k : ℕ, ((k : ℝ) * (1 / 2 : ℝ) ^ k + (1 / 2 : ℝ) ^ k) := by
          apply tsum_congr
          intro k
          push_cast
          ring
    _ = 1 / 2 / (1 - 1 / 2 : ℝ) ^ 2 + 2 := hsum.tsum_eq
    _ = 4 := by norm_num

/-- Each exact stopped-overshoot mass is dominated by the weighted geometric
term that preserves the sharp Appendix E tail constant. -/
theorem overshoot_mass_le_weighted (H k : ℕ) :
    ((H + 1 + k : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (H + 1 + k + 1) ≤
      ((H + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (H + 2) *
        (((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) := by
  have hprod : 0 ≤ (H : ℝ) * (k : ℝ) := mul_nonneg (by positivity) (by positivity)
  have hcoef : ((H + 1 + k : ℕ) : ℝ) ≤ ((H + 1 : ℕ) : ℝ) * (k + 1 : ℕ) := by
    push_cast
    nlinarith
  rw [show H + 1 + k + 1 = H + k + 2 by omega, show H + k + 2 = H + (k + 2) by omega,
    pow_add, show (k + 2 : ℕ) = k + 2 by omega, pow_add]
  rw [show (1 / 2 : ℝ) ^ (H + 2) = (1 / 2 : ℝ) ^ H * (1 / 2 : ℝ) ^ 2 by
    rw [pow_add]]
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ H * (1 / 2 : ℝ) ^ k := by positivity
  nlinarith [mul_nonneg hpow (by norm_num : 0 ≤ (1 / 2 : ℝ) ^ 2)]

/-- The shifted exact masses have the required sharp weighted-geometric
majorant. -/
theorem tsum_overshoot_mass_le (H : ℕ) :
    (∑' k : ℕ, ((H + 1 + k : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (H + 1 + k + 1)) ≤
      ((H + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (H + 2) * 4 := by
  have hlinear := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
  have hgeom := hasSum_geometric_two
  have hweight : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) := by
    have hsum := hlinear.add hgeom
    rw [show (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) =
      fun k : ℕ => ((k : ℝ) * (1 / 2 : ℝ) ^ k + (1 / 2 : ℝ) ^ k) by
      funext k
      push_cast
      ring]
    exact hsum.summable
  have hmajor := hweight.mul_left (((H + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (H + 2))
  have hleft : Summable (fun k : ℕ =>
      ((H + 1 + k : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (H + 1 + k + 1)) :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => overshoot_mass_le_weighted H k) hmajor
  calc
    (∑' k : ℕ, ((H + 1 + k : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (H + 1 + k + 1)) ≤
        ∑' k : ℕ, (((H + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (H + 2) *
          (((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k)) :=
      hleft.tsum_le_tsum (fun k => overshoot_mass_le_weighted H k) hmajor
    _ = ((H + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (H + 2) * 4 := by
      rw [tsum_mul_left, tsum_add_one_mul_geometric_two]

/-- The stopped overshoot satisfies the Appendix E tail bound at every
positive level. -/
theorem stoppedTailProbability_le_overshoot_bound {s H : ℕ} (hs : 0 < s) :
    stoppedTailProbability s H ≤ ((H + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ H := by
  rw [stoppedTailProbability_eq_tsum_joint]
  have hmass (k : ℕ) :
      stoppedJointProbability s (H + 1 + k) =
        ((H + 1 + k : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (H + 1 + k + 1) :=
    stoppedJointProbability_eq_overshoot_mass hs (by omega)
  simp_rw [hmass]
  calc
    (∑' k : ℕ, ((H + 1 + k : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (H + 1 + k + 1)) ≤
        ((H + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (H + 2) * 4 :=
      tsum_overshoot_mass_le H
    _ = ((H + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ H := by
      rw [show (1 / 2 : ℝ) ^ (H + 2) = (1 / 2 : ℝ) ^ H * (1 / 2 : ℝ) ^ 2 by
        rw [pow_add]]
      ring

/-- The Appendix E stopped-overshoot tail bound, including the level-zero
one-pair branch. -/
theorem stoppedTailProbability_le_overshoot_bound_all (s H : ℕ) :
    stoppedTailProbability s H ≤ ((H + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ H := by
  cases s with
  | zero =>
      rw [stoppedTailProbability_zero_eq_pairTail, pairTailProbability_eq]
  | succ s =>
      exact stoppedTailProbability_le_overshoot_bound (by omega)

/-- The explicit overshoot exception used by Appendix E's white-exit step. -/
theorem stoppedTailProbability_eight_le (s : ℕ) :
    stoppedTailProbability s 8 ≤ (9 / 256 : ℝ) := by
  calc
    stoppedTailProbability s 8 ≤ ((8 + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 8 :=
      stoppedTailProbability_le_overshoot_bound_all s 8
    _ = 9 / 256 := by norm_num

/-- The fair-toss exceptional event for the Appendix E horizontal exit bound. -/
noncomputable def fairPassageIndexHighProbability (s : ℕ) : ℝ :=
  Gated.probability (Probability.fairBinomial s)
    (fun k => (s : ℝ) / 4 + Real.sqrt (s : ℝ) + 1 < passageIndex k)

/-- Hoeffding's fair-binomial tail gives the `e^{-8}` horizontal exception
in Appendix E. This is stated on the fair-toss coupling side; transporting
the event back to the common original-word horizon remains part of the
stochastic white-exit consumer. -/
theorem fairPassageIndexHighProbability_le_exp_neg_eight {s : ℕ} (hs : 0 < s) :
    fairPassageIndexHighProbability s ≤ Real.exp (-8) := by
  unfold fairPassageIndexHighProbability
  calc
    _ ≤ Gated.probability (Probability.fairBinomial s)
        (fun k => 2 * Real.sqrt (s : ℝ) ≤ Probability.fairCenteredCount s k) := by
      apply Gated.probability_mono_on_support
      intro k _ hk
      unfold passageIndex at hk
      unfold Probability.fairCenteredCount
      norm_num at hk ⊢
      have hfloor_nat : 2 * (k / 2) ≤ k := by omega
      have hfloor : (2 : ℝ) * ((k / 2 : ℕ) : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast hfloor_nat
      linarith
    _ ≤ Real.exp (-2 * (2 * Real.sqrt (s : ℝ)) ^ 2 / s) := by
      apply Probability.fairBinomial_centeredUpperTail_le s hs
      positivity
    _ = Real.exp (-8) := by
      congr 1
      have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
      have hsq : Real.sqrt (s : ℝ) ^ 2 = (s : ℝ) :=
        Real.sq_sqrt (Nat.cast_nonneg s)
      field_simp
      nlinarith

/-- At level zero, the fair passage index is deterministically one, so the
horizontal exceptional event is empty. -/
theorem fairPassageIndexHighProbability_zero :
    fairPassageIndexHighProbability 0 = 0 := by
  unfold fairPassageIndexHighProbability
  calc
    _ = Gated.probability (Probability.fairBinomial 0) (fun _ => False) := by
      apply Gated.probability_congr_on_support
      intro k hk
      have hk0 : k = 0 := by
        by_contra hne
        have hkpos : 0 < k := by omega
        exact hk (fairBinomial_eq_zero_of_lt 0 k hkpos)
      subst k
      simp [passageIndex]
    _ = 0 := by simp [Gated.probability]

/-- The fair horizontal exception has the same finite passage-index
partition as the original-word exception. -/
theorem fairPassageIndexHighProbability_eq_sum (s : ℕ) :
    fairPassageIndexHighProbability s =
      ∑ i : Fin (s / 2 + 1), if
        (s : ℝ) / 4 + Real.sqrt (s : ℝ) + 1 < (i : ℕ) + 1 then
          fairPassageIndexProbability s (i + 1) else 0 := by
  let N := s / 2 + 1
  let G : Fin N → ℕ → Prop := fun i k =>
    passageIndex k = i + 1 ∧
      (s : ℝ) / 4 + Real.sqrt (s : ℝ) + 1 < (i : ℕ) + 1
  have hunique : ∀ i k x, G i x → G k x → i = k := by
    intro i k x hi hk
    apply Fin.ext
    omega
  have hUnion :
      Gated.probability (Probability.fairBinomial s)
        (fun k => ∃ i, G i k) = fairPassageIndexHighProbability s := by
    unfold fairPassageIndexHighProbability
    apply Gated.probability_congr_on_support
    intro k hk
    constructor
    · rintro ⟨i, hindex, hhigh⟩
      have hindex' : (passageIndex k : ℝ) = (i : ℕ) + 1 := by
        exact_mod_cast hindex
      norm_num at hhigh ⊢
      linarith
    · intro hhigh
      have hks : k ≤ s := by
        by_contra hnot
        have hlt : s < k := by omega
        exact hk (fairBinomial_eq_zero_of_lt s k hlt)
      let j := passageIndex k
      have hjpos : 0 < j := passageIndex_pos k
      have hjle : j ≤ N := passageIndex_le_of_le hks
      let i : Fin N := ⟨j - 1, by omega⟩
      refine ⟨i, ?_, ?_⟩
      · change j = j - 1 + 1
        omega
      · change (s : ℝ) / 4 + Real.sqrt (s : ℝ) + 1 < ((j - 1 : ℕ) : ℝ) + 1
        rw [Nat.cast_sub (by omega : 1 ≤ j)]
        norm_num
        exact hhigh
  calc
    fairPassageIndexHighProbability s =
        Gated.probability (Probability.fairBinomial s) (fun k => ∃ i, G i k) :=
      hUnion.symm
    _ = ∑ i, Gated.probability (Probability.fairBinomial s) (G i) :=
      Gated.probability_union _ G hunique
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (s : ℝ) / 4 + Real.sqrt (s : ℝ) + 1 < (i : ℕ) + 1
      · simp only [G, hi, and_true]
        rfl
      · have hlow : ¬ (s : ℝ) / 4 + Real.sqrt (s : ℝ) < (i : ℕ) := by
          intro hlow
          apply hi
          norm_num at hlow ⊢
          linarith
        simp [G, hlow, Gated.probability]

/-- The original-word and fair-toss horizontal exceptional probabilities
are exactly equal. -/
theorem stoppedPassageIndexHighProbability_eq_fair (s : ℕ) :
    stoppedPassageIndexHighProbability s = fairPassageIndexHighProbability s := by
  rw [stoppedPassageIndexHighProbability_eq_sum,
    fairPassageIndexHighProbability_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · exact pairPassageIndexProbability_eq_fairPassageIndexProbability (by omega)
  · rfl

/-- Hoeffding's `e^{-8}` horizontal exception holds for the original-word
passage event at every positive level. -/
theorem stoppedPassageIndexHighProbability_le_exp_neg_eight {s : ℕ} (hs : 0 < s) :
    stoppedPassageIndexHighProbability s ≤ Real.exp (-8) := by
  rw [stoppedPassageIndexHighProbability_eq_fair]
  exact fairPassageIndexHighProbability_le_exp_neg_eight hs

/-- The simultaneous common-horizon good event: neither the horizontal
exception nor the stopped overshoot above eight occurs. -/
def stoppedExitGoodEvent (s : ℕ) (w : ValuationWord) : Prop :=
  ¬ stoppedPassageIndexHighEvent s w ∧ ¬ stoppedTailEvent s 8 w

/-- Original probability of the simultaneous common-horizon good event. -/
noncomputable def stoppedExitGoodProbability (s : ℕ) : ℝ :=
  Gated.probability (Reference.wordPMF (2 * (s / 2 + 1)))
    (stoppedExitGoodEvent s)

/-- At a positive level, the simultaneous original-word horizontal and
overshoot good event has the Appendix E union-bound lower estimate. -/
theorem stoppedExitGoodProbability_lower {s : ℕ} (hs : 0 < s) :
    1 - (Real.exp (-8) + 9 / 256 : ℝ) ≤ stoppedExitGoodProbability s := by
  let p := Reference.wordPMF (2 * (s / 2 + 1))
  let A : ValuationWord → Prop := stoppedPassageIndexHighEvent s
  let B : ValuationWord → Prop := stoppedTailEvent s 8
  have hgood : stoppedExitGoodProbability s =
      1 - Gated.probability p (fun w => A w ∨ B w) := by
    unfold stoppedExitGoodProbability stoppedExitGoodEvent
    change Gated.probability p (fun w => ¬ A w ∧ ¬ B w) = _
    rw [show (fun w => ¬ A w ∧ ¬ B w) = (fun w => ¬ (A w ∨ B w)) by
      funext w
      simp]
    rw [Gated.probability_compl]
  have hunion := Gated.probability_or_le p A B
  have hhigh : Gated.probability p A ≤ Real.exp (-8) := by
    exact stoppedPassageIndexHighProbability_le_exp_neg_eight hs
  have htail : Gated.probability p B ≤ (9 / 256 : ℝ) := by
    exact stoppedTailProbability_eight_le s
  calc
    1 - (Real.exp (-8) + 9 / 256 : ℝ) ≤
        1 - (Gated.probability p A + Gated.probability p B) :=
      sub_le_sub_left (add_le_add hhigh htail) 1
    _ ≤ 1 - Gated.probability p (fun w => A w ∨ B w) :=
      sub_le_sub_left hunion 1
    _ = stoppedExitGoodProbability s := hgood.symm

/-- At level zero the original horizontal exception is empty. -/
theorem stoppedPassageIndexHighProbability_zero :
    stoppedPassageIndexHighProbability 0 = 0 := by
  rw [stoppedPassageIndexHighProbability_eq_fair,
    fairPassageIndexHighProbability_zero]

/-- The level-zero simultaneous original-word good event only pays the
stopped overshoot exception. -/
theorem stoppedExitGoodProbability_zero_lower :
    1 - (9 / 256 : ℝ) ≤ stoppedExitGoodProbability 0 := by
  let p := Reference.wordPMF (2 * (0 / 2 + 1))
  let A : ValuationWord → Prop := stoppedPassageIndexHighEvent 0
  let B : ValuationWord → Prop := stoppedTailEvent 0 8
  have hgood : stoppedExitGoodProbability 0 =
      1 - Gated.probability p (fun w => A w ∨ B w) := by
    unfold stoppedExitGoodProbability stoppedExitGoodEvent
    change Gated.probability p (fun w => ¬ A w ∧ ¬ B w) = _
    rw [show (fun w => ¬ A w ∧ ¬ B w) = (fun w => ¬ (A w ∨ B w)) by
      funext w
      simp]
    rw [Gated.probability_compl]
  have hunion := Gated.probability_or_le p A B
  have hhigh : Gated.probability p A = 0 := by
    exact stoppedPassageIndexHighProbability_zero
  have htail : Gated.probability p B ≤ (9 / 256 : ℝ) := by
    exact stoppedTailProbability_eight_le 0
  calc
    1 - (9 / 256 : ℝ) = 1 - (Gated.probability p A + 9 / 256) := by rw [hhigh]; ring
    _ ≤ 1 - (Gated.probability p A + Gated.probability p B) :=
      by
        simpa [add_comm] using
          (sub_le_sub_left (add_le_add_left htail (Gated.probability p A)) 1)
    _ ≤ 1 - Gated.probability p (fun w => A w ∨ B w) :=
      sub_le_sub_left hunion 1
    _ = stoppedExitGoodProbability 0 := hgood.symm

/-- The elementary exponential estimate used to simplify Appendix E's
Hoeffding exception numerically. -/
theorem exp_neg_eight_le_one_div_256 :
    Real.exp (-8) ≤ (1 / 256 : ℝ) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    norm_num at h ⊢
    exact h
  have hpow : (2 : ℝ) ^ 8 ≤ (Real.exp 1) ^ 8 := by
    exact pow_le_pow_left₀ (by norm_num) htwo 8
  have hexp : (Real.exp 1) ^ 8 = Real.exp 8 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have height : (256 : ℝ) ≤ Real.exp 8 := by
    calc
      (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ (Real.exp 1) ^ 8 := hpow
      _ = Real.exp 8 := hexp
  rw [show (-8 : ℝ) = - (8 : ℝ) by norm_num, Real.exp_neg]
  simpa [one_div] using one_div_le_one_div_of_le (by positivity) height

/-- The positive-level common-horizon good-event lower expression already
strictly exceeds the manuscript's `15 / 16` target. -/
theorem exitGood_numeric_lower :
    (15 / 16 : ℝ) < 1 - (Real.exp (-8) + 9 / 256 : ℝ) := by
  have h := exp_neg_eight_le_one_div_256
  linarith

/-- The elementary square comparison used in the first-passage horizontal
exit estimate. -/
theorem sqrt_le_sixteenth_add_four (s : ℕ) :
    Real.sqrt (s : ℝ) ≤ (s : ℝ) / 16 + 4 := by
  have hs : 0 ≤ (s : ℝ) := by positivity
  have hright : 0 ≤ (s : ℝ) / 16 + 4 := by positivity
  have hsq : Real.sqrt (s : ℝ) ^ 2 = (s : ℝ) := Real.sq_sqrt hs
  nlinarith [sq_nonneg ((s : ℝ) - 64)]

/-- Outside the horizontal exceptional event, the passage pair index lies
within nine columns of the integer top-row witness. -/
theorem passageIndex_le_five_div_sixteen_add_nine
    (s J : ℕ)
    (hgood : ¬ ((s : ℝ) / 4 + Real.sqrt (s : ℝ) + 1 < J)) :
    J ≤ 5 * (s / 16) + 9 := by
  have hJ : (J : ℝ) ≤ (s : ℝ) / 4 + Real.sqrt (s : ℝ) + 1 :=
    le_of_not_gt hgood
  have hsqrt := sqrt_le_sixteenth_add_four s
  have hmod : s % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hdecomp : s = 16 * (s / 16) + s % 16 := by omega
  have hdecompR : (s : ℝ) = 16 * ((s / 16 : ℕ) : ℝ) + ((s % 16 : ℕ) : ℝ) := by
    exact_mod_cast hdecomp
  have hmodR : ((s % 16 : ℕ) : ℝ) < 16 := by exact_mod_cast hmod
  have hstrict : (J : ℝ) < (5 * (s / 16) + 10 : ℕ) := by
    norm_num at hJ hsqrt ⊢
    rw [hdecompR] at hJ hsqrt
    linarith
  have hJnat : J < 5 * (s / 16) + 10 := by exact_mod_cast hstrict
  omega

/-- A positive fair passage-index atom is the sum of its two adjacent
fair-binomial atoms. This is the exact reduction used for the Appendix E
unconditional square-root atom estimate. -/
theorem fairPassageIndexProbability_eq_two_points {s j : ℕ} (hj : 0 < j) :
    fairPassageIndexProbability s j =
      fairPointProbability s (2 * (j - 1)) +
        fairPointProbability s (2 * (j - 1) + 1) := by
  rw [fairPassageIndexProbability_eq_cdf_sub hj]
  rw [fairUpperProbability_split s (2 * (j - 1))]
  have hstep : 2 * (j - 1) + 1 + 1 = 2 * j := by omega
  rw [fairUpperProbability_split s (2 * (j - 1) + 1), hstep]
  ring

/-- The squared central-binomial bound used to control every fair-binomial
atom. This is the paper's elementary induction written without division. -/
theorem centralBinom_sq_bound (n : ℕ) :
    (Nat.centralBinom n : ℝ) ^ 2 * (n + 1 : ℝ) ≤ (16 : ℝ) ^ n := by
  induction n with
  | zero => norm_num [Nat.centralBinom]
  | succ n ih =>
      have hrecNat := Nat.succ_mul_centralBinom_succ n
      have hrec : (n + 1 : ℝ) * (Nat.centralBinom (n + 1) : ℝ) =
          2 * (2 * n + 1 : ℝ) * (Nat.centralBinom n : ℝ) := by
        exact_mod_cast hrecNat
      have hpoly : (2 * n + 1 : ℝ) ^ 2 * (n + 2 : ℝ) ≤ 4 * (n + 1 : ℝ) ^ 3 := by
        nlinarith [sq_nonneg (n : ℝ)]
      have hn : 0 < (n + 1 : ℝ) := by positivity
      have hpolyC := mul_le_mul_of_nonneg_right hpoly
        (sq_nonneg (Nat.centralBinom n : ℝ))
      have hrecSq := congrArg (fun x : ℝ => x ^ 2) hrec
      have hrecSq' : (n + 1 : ℝ) ^ 2 * (Nat.centralBinom (n + 1) : ℝ) ^ 2 =
          4 * (2 * n + 1 : ℝ) ^ 2 * (Nat.centralBinom n : ℝ) ^ 2 := by
        calc
          _ = ((n + 1 : ℝ) * (Nat.centralBinom (n + 1) : ℝ)) ^ 2 := by ring
          _ = (2 * (2 * n + 1 : ℝ) * (Nat.centralBinom n : ℝ)) ^ 2 := hrecSq
          _ = _ := by ring
      have hscaled1 : 4 * (2 * n + 1 : ℝ) ^ 2 *
          (Nat.centralBinom n : ℝ) ^ 2 * (n + 2 : ℝ) ≤
          16 * (n + 1 : ℝ) ^ 3 * (Nat.centralBinom n : ℝ) ^ 2 := by
        calc
          _ = 4 * ((2 * n + 1 : ℝ) ^ 2 * (n + 2 : ℝ) *
              (Nat.centralBinom n : ℝ) ^ 2) := by ring
          _ ≤ 4 * (4 * (n + 1 : ℝ) ^ 3 * (Nat.centralBinom n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hpolyC (by norm_num)
          _ = _ := by ring
      have hscaled2 : 16 * (n + 1 : ℝ) ^ 3 * (Nat.centralBinom n : ℝ) ^ 2 ≤
          16 * (n + 1 : ℝ) ^ 2 * (16 : ℝ) ^ n := by
        calc
          _ = 16 * (n + 1 : ℝ) ^ 2 *
              ((Nat.centralBinom n : ℝ) ^ 2 * (n + 1 : ℝ)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left ih (by positivity)
      have hmain : (n + 1 : ℝ) ^ 2 *
          ((Nat.centralBinom (n + 1) : ℝ) ^ 2 * (n + 2 : ℝ)) ≤
          (n + 1 : ℝ) ^ 2 * ((16 : ℝ) ^ n * 16) := by
        calc
          _ = 4 * (2 * n + 1 : ℝ) ^ 2 * (Nat.centralBinom n : ℝ) ^ 2 *
              (n + 2 : ℝ) := by
                calc
                  _ = ((n + 1 : ℝ) ^ 2 * (Nat.centralBinom (n + 1) : ℝ) ^ 2) *
                      (n + 2 : ℝ) := by ring
                  _ = _ := by rw [hrecSq']
          _ ≤ 16 * (n + 1 : ℝ) ^ 3 * (Nat.centralBinom n : ℝ) ^ 2 := hscaled1
          _ ≤ 16 * (n + 1 : ℝ) ^ 2 * (16 : ℝ) ^ n := hscaled2
          _ = (n + 1 : ℝ) ^ 2 * ((16 : ℝ) ^ n * 16) := by ring
      have hcancel := le_of_mul_le_mul_left hmain (sq_pos_of_pos hn)
      have hheight : (n + 1 : ℝ) + 1 = (n : ℝ) + 2 := by ring
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
      calc
        (Nat.centralBinom (n + 1) : ℝ) ^ 2 * ((n + 1 : ℕ) + 1 : ℝ) =
            (Nat.centralBinom (n + 1) : ℝ) ^ 2 * (n + 2 : ℝ) := by rw [hcast, hheight]
        _ ≤ (16 : ℝ) ^ n * 16 := hcancel
        _ = (16 : ℝ) ^ (n + 1) := by rw [pow_succ]

/-- The normalized central fair-binomial atom is at most the reciprocal
square root of its half-length. -/
theorem centralBinom_probability_le (n : ℕ) :
    (Nat.centralBinom n : ℝ) * (1 / 4 : ℝ) ^ n ≤ 1 / Real.sqrt (n + 1 : ℝ) := by
  have hcentral := centralBinom_sq_bound n
  have hunit : (16 : ℝ) ^ n * ((1 / 4 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul]
    have hpow : (16 : ℝ) ^ n = 4 ^ (2 * n) := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, ← pow_mul]
    rw [hpow, show n * 2 = 2 * n by omega, ← mul_pow]
    norm_num
  have hsq : ((Nat.centralBinom n : ℝ) * (1 / 4 : ℝ) ^ n) ^ 2 *
      (n + 1 : ℝ) ≤ 1 := by
    calc
      _ = ((Nat.centralBinom n : ℝ) ^ 2 * (n + 1 : ℝ)) *
          ((1 / 4 : ℝ) ^ n) ^ 2 := by ring
      _ ≤ (16 : ℝ) ^ n * ((1 / 4 : ℝ) ^ n) ^ 2 :=
        mul_le_mul_of_nonneg_right hcentral (by positivity)
      _ = 1 := hunit
  have hnon : 0 ≤ (Nat.centralBinom n : ℝ) * (1 / 4 : ℝ) ^ n := by positivity
  have hsqrt : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
  apply (le_div_iff₀ hsqrt).2
  have hroot : Real.sqrt (n + 1 : ℝ) ^ 2 = (n + 1 : ℝ) :=
    Real.sq_sqrt (by positivity)
  nlinarith

/-- An odd binomial coefficient is at most twice the preceding central one. -/
theorem choose_odd_le_two_central (n k : ℕ) :
    (2 * n + 1).choose k ≤ 2 * Nat.centralBinom n := by
  cases n with
  | zero =>
      have h := Nat.choose_le_two_pow 1 k
      norm_num at h ⊢
      exact h
  | succ n =>
      have hhalf : (2 * (n + 1) + 1) / 2 = n + 1 := by omega
      calc
        (2 * (n + 1) + 1).choose k ≤ (2 * (n + 1) + 1).choose (n + 1) := by
          simpa [hhalf] using Nat.choose_le_middle k (2 * (n + 1) + 1)
        _ = (2 * (n + 1)).choose n + (2 * (n + 1)).choose (n + 1) := by
          rw [Nat.choose_succ_succ']
        _ ≤ Nat.centralBinom (n + 1) + Nat.centralBinom (n + 1) := by
          gcongr
          exact Nat.choose_le_centralBinom n (n + 1)
          simp [Nat.centralBinom]
        _ = 2 * Nat.centralBinom (n + 1) := by omega

/-- Every even-length fair-binomial point mass is bounded by the normalized
central coefficient at half its length. -/
theorem fairPoint_even_le_central (n k : ℕ) :
    fairPointProbability (2 * n) k ≤
      (Nat.centralBinom n : ℝ) * (1 / 4 : ℝ) ^ n := by
  rw [fairPointProbability_eq]
  have hchoose : (2 * n).choose k ≤ Nat.centralBinom n := Nat.choose_le_centralBinom k n
  have hpow : (1 / 2 : ℝ) ^ (2 * n) = (1 / 4 : ℝ) ^ n := by
    rw [show (2 * n : ℕ) = 2 * n by rfl, pow_mul]
    norm_num
  rw [hpow]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hchoose) (by positivity)

/-- The same normalized central bound controls odd-length fair-binomial
point masses, with Pascal's factor of two canceled by the final fair toss. -/
theorem fairPoint_odd_le_central (n k : ℕ) :
    fairPointProbability (2 * n + 1) k ≤
      (Nat.centralBinom n : ℝ) * (1 / 4 : ℝ) ^ n := by
  rw [fairPointProbability_eq]
  have hchoose : (2 * n + 1).choose k ≤ 2 * Nat.centralBinom n :=
    choose_odd_le_two_central n k
  have hpow : (1 / 2 : ℝ) ^ (2 * n + 1) = (1 / 4 : ℝ) ^ n * (1 / 2) := by
    rw [show 2 * n + 1 = 2 * n + 1 by rfl, pow_add, show (1 / 2 : ℝ) ^ (2 * n) =
      (1 / 4 : ℝ) ^ n by
        rw [show (2 * n : ℕ) = 2 * n by rfl, pow_mul]
        norm_num]
    norm_num
  rw [hpow]
  calc
    _ ≤ ((2 * Nat.centralBinom n : ℕ) : ℝ) * ((1 / 4 : ℝ) ^ n * (1 / 2)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hchoose) (by positivity)
    _ = _ := by push_cast; ring

/-- The normalized central mass has the even-length square-root bound needed
for the uniform fair-binomial atom estimate. -/
theorem central_probability_le_even_sqrt (n : ℕ) :
    (Nat.centralBinom n : ℝ) * (1 / 4 : ℝ) ^ n ≤
      2 / Real.sqrt (2 * n + 1 : ℝ) := by
  calc
    _ ≤ 1 / Real.sqrt (n + 1 : ℝ) := centralBinom_probability_le n
    _ ≤ 2 / Real.sqrt (2 * n + 1 : ℝ) := by
      have hn : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
      have hs : 0 < Real.sqrt (2 * n + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
      apply (div_le_div_iff₀ hn hs).2
      have hleft : Real.sqrt (2 * n + 1 : ℝ) ^ 2 = (2 * n + 1 : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hright : Real.sqrt (n + 1 : ℝ) ^ 2 = (n + 1 : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hrightnon : 0 ≤ Real.sqrt (n + 1 : ℝ) := Real.sqrt_nonneg _
      nlinarith

/-- The corresponding odd-length square-root comparison. -/
theorem central_probability_le_odd_sqrt (n : ℕ) :
    (Nat.centralBinom n : ℝ) * (1 / 4 : ℝ) ^ n ≤
      2 / Real.sqrt (2 * n + 2 : ℝ) := by
  calc
    _ ≤ 1 / Real.sqrt (n + 1 : ℝ) := centralBinom_probability_le n
    _ ≤ 2 / Real.sqrt (2 * n + 2 : ℝ) := by
      have hn : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
      have hs : 0 < Real.sqrt (2 * n + 2 : ℝ) := Real.sqrt_pos.2 (by positivity)
      apply (div_le_div_iff₀ hn hs).2
      have hleft : Real.sqrt (2 * n + 2 : ℝ) ^ 2 = (2 * n + 2 : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hright : Real.sqrt (n + 1 : ℝ) ^ 2 = (n + 1 : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hrightnon : 0 ≤ Real.sqrt (n + 1 : ℝ) := Real.sqrt_nonneg _
      nlinarith

/-- Every fair-binomial point mass has the uniform square-root bound. -/
theorem fairPointProbability_le_sqrt (s k : ℕ) :
    fairPointProbability s k ≤ 2 / Real.sqrt (s + 1 : ℝ) := by
  rcases Nat.even_or_odd' s with ⟨n, rfl | rfl⟩
  · simpa [Nat.cast_add, Nat.cast_mul] using
      (le_trans (fairPoint_even_le_central n k) (central_probability_le_even_sqrt n))
  · have h := le_trans (fairPoint_odd_le_central n k) (central_probability_le_odd_sqrt n)
    have hshift : (2 * n + 2 : ℝ) = 2 * (n : ℝ) + 1 + 1 := by ring
    rw [hshift] at h
    simpa [Nat.cast_add, Nat.cast_mul] using h

/-- The Appendix E unconditional passage-index atom bound. Each passage atom
is the sum of two controlled fair-binomial atoms. -/
theorem fairPassageIndexProbability_le_four_div_sqrt {s j : ℕ} (hs : 0 < s) (hj : 0 < j) :
    fairPassageIndexProbability s j ≤ 4 / Real.sqrt (s : ℝ) := by
  rw [fairPassageIndexProbability_eq_two_points hj]
  calc
    _ ≤ 2 / Real.sqrt (s + 1 : ℝ) + 2 / Real.sqrt (s + 1 : ℝ) :=
      add_le_add (fairPointProbability_le_sqrt s (2 * (j - 1)))
        (fairPointProbability_le_sqrt s (2 * (j - 1) + 1))
    _ = 4 / Real.sqrt (s + 1 : ℝ) := by ring
    _ ≤ 4 / Real.sqrt (s : ℝ) := by
      have hleft : 0 < Real.sqrt (s + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
      have hright : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hs)
      apply (div_le_div_iff₀ hleft hright).2
      apply mul_le_mul_of_nonneg_left
      · apply Real.sqrt_le_sqrt
        linarith
      · norm_num

/-- The tail-series half of the Appendix E overshoot first-moment estimate.
The separate tail-sum identity connecting this series to the stopped random
overshoot remains an explicit subsequent step. -/
noncomputable def stoppedOvershootTailSum (s : ℕ) : ℝ :=
  ∑' H : ℕ, stoppedTailProbability s H

theorem stoppedOvershootTailSum_le_four (s : ℕ) : stoppedOvershootTailSum s ≤ 4 := by
  unfold stoppedOvershootTailSum
  have hlinear := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
  have hgeom := hasSum_geometric_two
  have hweight : Summable (fun H : ℕ => ((H + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ H) := by
    have hsum := hlinear.add hgeom
    rw [show (fun H : ℕ => ((H + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ H) =
      fun H : ℕ => ((H : ℝ) * (1 / 2 : ℝ) ^ H + (1 / 2 : ℝ) ^ H) by
        funext H
        push_cast
        ring]
    exact hsum.summable
  have htail : Summable (fun H : ℕ => stoppedTailProbability s H) :=
    Summable.of_nonneg_of_le (fun H => ENNReal.toReal_nonneg)
      (fun H => stoppedTailProbability_le_overshoot_bound_all s H) hweight
  calc
    (∑' H : ℕ, stoppedTailProbability s H) ≤
        ∑' H : ℕ, ((H + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ H :=
      htail.tsum_le_tsum (fun H => stoppedTailProbability_le_overshoot_bound_all s H) hweight
    _ = 4 := tsum_add_one_mul_geometric_two

/-- A fresh geometric letter has exact exponential moment two at base `4 / 3`. -/
theorem geometricLetter_powerMoment_four_thirds :
    (∑' a : ℕ+, Reference.geometricLetter a *
      ENNReal.ofReal ((4 / 3 : ℝ) ^ (a : ℕ))) = 2 := by
  have hreal : HasSum (fun n : ℕ => (2 / 3 : ℝ) ^ (n + 1)) 2 := by
    have h := (hasSum_geometric_of_norm_lt_one (ξ := (2 / 3 : ℝ))
      (by norm_num)).mul_left (2 / 3)
    have hsum : (2 / 3 : ℝ) * (1 - 2 / 3 : ℝ)⁻¹ = 2 := by norm_num
    rw [hsum] at h
    simpa [pow_succ, mul_comm] using h
  have henn : HasSum (fun n : ℕ => ENNReal.ofReal ((2 / 3 : ℝ) ^ (n + 1))) 2 :=
    ENNReal.hasSum_coe.mpr (by simpa using hreal.toNNReal (fun n => by positivity))
  rw [← Equiv.pnatEquivNat.symm.tsum_eq]
  calc
    _ = ∑' n : ℕ, ENNReal.ofReal ((2 / 3 : ℝ) ^ (n + 1)) := by
      apply tsum_congr
      intro n
      rw [Equiv.pnatEquivNat_symm_apply, Reference.geometricLetter_apply]
      change ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) *
          ENNReal.ofReal ((4 / 3 : ℝ) ^ (n + 1)) = _
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← mul_pow]
      norm_num
    _ = 2 := henn.tsum_eq

/-- The `4 / 3` exponential moment of a fixed fresh word. -/
noncomputable def freshWordPowerMomentFourThirds (n : ℕ) : ENNReal :=
  ∑' w, Reference.wordPMF n w * ENNReal.ofReal ((4 / 3 : ℝ) ^ w.total)

/-- Appending one fresh geometric letter doubles its `4 / 3` moment. -/
theorem freshWordPowerMomentFourThirds_succ (n : ℕ) :
    freshWordPowerMomentFourThirds (n + 1) = 2 * freshWordPowerMomentFourThirds n := by
  unfold freshWordPowerMomentFourThirds
  change (∑' w, (Reference.geometricLetter.bind
    (fun a => (Reference.wordPMF n).map (fun w => a :: w))) w *
    ENNReal.ofReal ((4 / 3 : ℝ) ^ ValuationWord.total w)) = _
  rw [PMFMoment.sum_bind]
  have hfactor (a : ℕ+) :
      (∑' w, Reference.wordPMF n w *
        ENNReal.ofReal ((4 / 3 : ℝ) ^ ValuationWord.total (a :: w))) =
        ENNReal.ofReal ((4 / 3 : ℝ) ^ (a : ℕ)) *
          ∑' w, Reference.wordPMF n w *
            ENNReal.ofReal ((4 / 3 : ℝ) ^ w.total) := by
    calc
      _ = ∑' w, Reference.wordPMF n w *
          (ENNReal.ofReal ((4 / 3 : ℝ) ^ (a : ℕ)) *
            ENNReal.ofReal ((4 / 3 : ℝ) ^ w.total)) := by
          apply tsum_congr
          intro w
          simp only [ValuationWord.total, List.map_cons, List.sum_cons]
          rw [pow_add, ← ENNReal.ofReal_mul (by positivity)]
      _ = _ := by
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro w
          ac_rfl
  calc
    _ = ∑' a : ℕ+, Reference.geometricLetter a *
        (ENNReal.ofReal ((4 / 3 : ℝ) ^ (a : ℕ)) *
          ∑' w, Reference.wordPMF n w *
            ENNReal.ofReal ((4 / 3 : ℝ) ^ ValuationWord.total w)) := by
      apply tsum_congr
      intro a
      rw [PMFMoment.sum_map, hfactor]
    _ = (∑' a : ℕ+, Reference.geometricLetter a *
        ENNReal.ofReal ((4 / 3 : ℝ) ^ (a : ℕ))) *
          ∑' w, Reference.wordPMF n w *
            ENNReal.ofReal ((4 / 3 : ℝ) ^ ValuationWord.total w) := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro a
      ac_rfl
    _ = _ := by rw [geometricLetter_powerMoment_four_thirds]

/-- Every fixed fresh word of length `n` has `4 / 3` exponential moment `2^n`. -/
theorem freshWordPowerMomentFourThirds_eq (n : ℕ) :
    freshWordPowerMomentFourThirds n = 2 ^ n := by
  induction n with
  | zero => simp [freshWordPowerMomentFourThirds, Reference.wordPMF, ValuationWord.total]
  | succ n ih =>
      rw [freshWordPowerMomentFourThirds_succ, ih, pow_succ]
      ac_rfl

/-- The nonnegative suffix moment of a word selected by a decidable prefix event. -/
noncomputable def prefixSuffixMoment (m n : ℕ) (G : ValuationWord → Prop)
    [DecidablePred G] (F : ValuationWord → ENNReal) : ENNReal :=
  ∑' w, Reference.wordPMF (m + n) w * if G (w.take m) then F (w.drop m) else 0

/-- A fixed prefix event factors from every nonnegative moment of its fresh suffix. -/
theorem prefixSuffixMoment_factor (m n : ℕ) (G : ValuationWord → Prop)
    [DecidablePred G] (F : ValuationWord → ENNReal) :
    prefixSuffixMoment m n G F =
      (∑' u, Reference.wordPMF m u * if G u then 1 else 0) *
        ∑' v, Reference.wordPMF n v * F v := by
  unfold prefixSuffixMoment
  calc
    _ = ∑' uv, ((Reference.wordPMF (m + n)).map (fun w => (w.take m, w.drop m))) uv *
        if G uv.1 then F uv.2 else 0 := by
      symm
      simpa using PMFMoment.sum_map (Reference.wordPMF (m + n))
        (fun w => (w.take m, w.drop m)) (fun uv => if G uv.1 then F uv.2 else 0)
    _ = ∑' u, Reference.wordPMF m u * ∑' v, Reference.wordPMF n v *
        if G u then F v else 0 := by
      rw [Reference.wordPMF_map_take_drop, PMFMoment.sum_bind]
      apply tsum_congr
      intro u
      rw [PMFMoment.sum_map]
    _ = ∑' u, (Reference.wordPMF m u * if G u then 1 else 0) *
        ∑' v, Reference.wordPMF n v * F v := by
      apply tsum_congr
      intro u
      by_cases hu : G u <;> simp [hu]
    _ = _ := by rw [ENNReal.tsum_mul_right]

/-- The ENNReal mass of an original word-law event, with its classical
decision procedure encapsulated. -/
noncomputable def prefixEventMass (m : ℕ) (G : ValuationWord → Prop) : ENNReal := by
  classical
  exact ∑' u, Reference.wordPMF m u * if G u then 1 else 0

/-- The real value of `prefixEventMass` is the existing original event probability. -/
theorem prefixEventMass_toReal (m : ℕ) (G : ValuationWord → Prop) :
    (prefixEventMass m G).toReal = Gated.probability (Reference.wordPMF m) G := by
  classical
  unfold prefixEventMass Gated.probability
  congr 1
  apply tsum_congr
  intro u
  by_cases hu : G u <;> simp [hu]

/-- The fresh `p`-pair suffix moment attached to a fixed first-passage prefix. -/
noncomputable def pairFirstPassageSuffixMoment (s j h p : ℕ) : ENNReal := by
  classical
  exact @prefixSuffixMoment (2 * j) (2 * p) (pairFirstPassageEvent s j h)
    (Classical.decPred _) (fun v => ENNReal.ofReal ((4 / 3 : ℝ) ^ v.total))

/-- A fixed first-passage event factors from its `p` fresh post-passage pairs. -/
theorem pairFirstPassageSuffixMoment_factor (s j h p : ℕ) :
    pairFirstPassageSuffixMoment s j h p =
      prefixEventMass (2 * j) (pairFirstPassageEvent s j h) * 4 ^ p := by
  classical
  unfold pairFirstPassageSuffixMoment
  rw [prefixSuffixMoment_factor]
  change prefixEventMass (2 * j) (pairFirstPassageEvent s j h) *
      freshWordPowerMomentFourThirds (2 * p) = _
  rw [freshWordPowerMomentFourThirds_eq]
  congr 1
  calc
    (2 : ENNReal) ^ (2 * p) = 2 ^ (p * 2) := by rw [show 2 * p = p * 2 by omega]
    _ = 2 ^ (2 * p) := by rw [show p * 2 = 2 * p by omega]
    _ = (2 ^ 2 : ENNReal) ^ p := pow_mul (2 : ENNReal) 2 p
    _ = 4 ^ p := by norm_num

/-- In real form, a fixed first-passage prefix and its `p` fresh post-passage
pairs have exactly the product probability-moment law. -/
theorem pairFirstPassageSuffixMoment_toReal (s j h p : ℕ) :
    (pairFirstPassageSuffixMoment s j h p).toReal =
      pairFirstPassageProbability s j h * (4 : ℝ) ^ p := by
  rw [pairFirstPassageSuffixMoment_factor, ENNReal.toReal_mul,
    prefixEventMass_toReal]
  change pairFirstPassageProbability s j h * (4 : ℝ) ^ p = _
  norm_num

/-- The exact `4 / 3` moment of the realized first-passage overshoot followed
by `p` full fresh pairs.  The prefix event is still evaluated under the
original word law. -/
noncomputable def pairFirstPassagePostStopMoment (s j h p : ℕ) : ENNReal := by
  classical
  exact @prefixSuffixMoment (2 * j) (2 * p) (pairFirstPassageEvent s j h)
    (Classical.decPred _)
    (fun v => ENNReal.ofReal ((4 / 3 : ℝ) ^ (h + v.total)))

/-- A first-passage prefix factors from the literal overshoot-plus-fresh-pair
post-stop moment. -/
theorem pairFirstPassagePostStopMoment_factor (s j h p : ℕ) :
    pairFirstPassagePostStopMoment s j h p =
      prefixEventMass (2 * j) (pairFirstPassageEvent s j h) *
        ENNReal.ofReal ((4 / 3 : ℝ) ^ h) * 4 ^ p := by
  classical
  unfold pairFirstPassagePostStopMoment
  rw [prefixSuffixMoment_factor]
  have hsuffix :
      (∑' v, Reference.wordPMF (2 * p) v *
        ENNReal.ofReal ((4 / 3 : ℝ) ^ (h + v.total))) =
        ENNReal.ofReal ((4 / 3 : ℝ) ^ h) * 4 ^ p := by
    calc
      _ = ENNReal.ofReal ((4 / 3 : ℝ) ^ h) *
          ∑' v, Reference.wordPMF (2 * p) v *
            ENNReal.ofReal ((4 / 3 : ℝ) ^ v.total) := by
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro v
        rw [pow_add, ENNReal.ofReal_mul (by positivity)]
        ac_rfl
      _ = _ := by
        change ENNReal.ofReal ((4 / 3 : ℝ) ^ h) *
          freshWordPowerMomentFourThirds (2 * p) = _
        rw [freshWordPowerMomentFourThirds_eq]
        norm_num
        rw [show (2 : ENNReal) ^ (2 * p) = 4 ^ p by
          calc
            (2 : ENNReal) ^ (2 * p) = (2 ^ 2 : ENNReal) ^ p := by rw [pow_mul]
            _ = 4 ^ p := by norm_num]
  rw [hsuffix]
  unfold prefixEventMass
  ac_rfl

/-- In real form, the literal post-stop word moment has the first-passage
mass times the realized overshoot factor and the fresh-pair factor. -/
theorem pairFirstPassagePostStopMoment_toReal (s j h p : ℕ) :
    (pairFirstPassagePostStopMoment s j h p).toReal =
      pairFirstPassageProbability s j h * (4 / 3 : ℝ) ^ h * (4 : ℝ) ^ p := by
  rw [pairFirstPassagePostStopMoment_factor, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow,
    prefixEventMass_toReal]
  change pairFirstPassageProbability s j h * (4 / 3 : ℝ) ^ h * (4 : ℝ) ^ p = _
  norm_num

/-- The fair-toss realization of Appendix E's fresh suffix.  An even success
count before the level needs two letters, while an odd count needs one. -/
noncomputable def fairParityFutureMoment (s p : ℕ) : ENNReal :=
  ∑' k, Probability.fairBinomial s k *
    freshWordPowerMomentFourThirds (2 * p + if Even k then 2 else 1)

/-- The parity-selected fair fresh suffix has the Appendix E bound
`4^(p + 1)`.  This is a fair-side moment statement; the original-word
stopped-prefix relation is supplied separately by
`pairFirstPassagePostStopMoment_toReal`. -/
theorem fairParityFutureMoment_le (s p : ℕ) :
    fairParityFutureMoment s p ≤ (4 : ENNReal) ^ (p + 1) := by
  unfold fairParityFutureMoment
  calc
    _ ≤ ∑' k, Probability.fairBinomial s k * (4 : ENNReal) ^ (p + 1) := by
      apply ENNReal.tsum_le_tsum
      intro k
      rw [freshWordPowerMomentFourThirds_eq]
      by_cases he : Even k
      · rw [if_pos he]
        have hpow : (2 : ENNReal) ^ (2 * p + 2) ≤ 4 ^ (p + 1) := by
          rw [show 2 * p + 2 = 2 * (p + 1) by omega, pow_mul]
          norm_num
        exact mul_le_mul_of_nonneg_left hpow bot_le
      · rw [if_neg he]
        have hpow : (2 : ENNReal) ^ (2 * p + 1) ≤ 4 ^ (p + 1) := by
          calc
            (2 : ENNReal) ^ (2 * p + 1) = 2 * 4 ^ p := by
              rw [show 2 * p + 1 = 1 + 2 * p by omega, pow_add, pow_mul]
              norm_num
            _ ≤ 4 ^ (p + 1) := by
              rw [pow_succ]
              calc
                (2 : ENNReal) * 4 ^ p ≤ (4 : ENNReal) * 4 ^ p :=
                  mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
                _ = 4 ^ p * (4 : ENNReal) := by ac_rfl
        exact mul_le_mul_of_nonneg_left hpow bot_le
    _ = _ := by
      rw [ENNReal.tsum_mul_right, (Probability.fairBinomial s).tsum_coe, one_mul]

/-- The finite original-law sum of post-passage suffix moments, indexed by
the realized first-passage pair. -/
noncomputable def stoppedJointSuffixMoment (s h p : ℕ) : ℝ :=
  ∑ i : Fin (s / 2 + 1),
    (pairFirstPassageSuffixMoment s (i + 1) h p).toReal

/-- The finite stopped-index post-passage suffix moment is the stopped joint
probability times the exact fresh-pair factor. -/
theorem stoppedJointSuffixMoment_factor (s h p : ℕ) :
    stoppedJointSuffixMoment s h p =
      stoppedJointProbability s h * (4 : ℝ) ^ p := by
  unfold stoppedJointSuffixMoment
  simp_rw [pairFirstPassageSuffixMoment_toReal]
  rw [← Finset.sum_mul, ← stoppedJointProbability_eq_sum]

/-- The weighted geometric sum at ratio `2 / 3` used by the stopped
overshoot moment. -/
theorem tsum_add_one_mul_geometric_two_thirds :
    (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (2 / 3 : ℝ) ^ k) = 9 := by
  have hlinear := hasSum_coe_mul_geometric_of_norm_lt_one (r := (2 / 3 : ℝ)) (by norm_num)
  have hgeom := hasSum_geometric_of_norm_lt_one (ξ := (2 / 3 : ℝ)) (by norm_num)
  have hsum := hlinear.add hgeom
  calc
    _ = ∑' k : ℕ, ((k : ℝ) * (2 / 3 : ℝ) ^ k + (2 / 3 : ℝ) ^ k) := by
      apply tsum_congr
      intro k
      push_cast
      ring
    _ = (2 / 3 : ℝ) / (1 - 2 / 3 : ℝ) ^ 2 + (1 - 2 / 3 : ℝ)⁻¹ := hsum.tsum_eq
    _ = 9 := by norm_num

/-- The positive stopped overshoot moment at base `4 / 3`. The index `k + 1`
records the strict-passage fact that the overshoot is positive. -/
noncomputable def stoppedPositiveOvershootPowerMoment (s : ℕ) : ℝ :=
  ∑' k : ℕ, stoppedJointProbability s (k + 1) * (4 / 3 : ℝ) ^ (k + 1)

/-- At every positive level, the stopped overshoot has exact `4 / 3` moment three. -/
theorem stoppedPositiveOvershootPowerMoment_eq_three {s : ℕ} (hs : 0 < s) :
    stoppedPositiveOvershootPowerMoment s = 3 := by
  unfold stoppedPositiveOvershootPowerMoment
  have hmass (k : ℕ) :
      stoppedJointProbability s (k + 1) = ((k + 1 : ℕ) : ℝ) *
        (1 / 2 : ℝ) ^ (k + 1 + 1) :=
    stoppedJointProbability_eq_overshoot_mass hs (by omega)
  simp_rw [hmass]
  calc
    _ = (1 / 2 : ℝ) * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (2 / 3 : ℝ) ^ (k + 1) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ]
      calc
        _ = (1 / 2 : ℝ) * (((k + 1 : ℕ) : ℝ) *
            ((1 / 2 : ℝ) ^ (k + 1) * (4 / 3 : ℝ) ^ (k + 1))) := by ring
        _ = _ := by rw [← mul_pow]; norm_num
    _ = (1 / 2 : ℝ) * ((2 / 3 : ℝ) *
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (2 / 3 : ℝ) ^ k) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [pow_succ]
      ring
    _ = 3 := by rw [tsum_add_one_mul_geometric_two_thirds]; norm_num

/-- At level zero, the stopped positive-overshoot mass is the first-pair mass. -/
theorem stoppedJointProbability_zero_mass (k : ℕ) :
    stoppedJointProbability 0 (k + 1) = (k : ℝ) * (1 / 2 : ℝ) ^ (k + 1) := by
  rw [stoppedJointProbability_eq_sum]
  rw [show 0 / 2 + 1 = 1 by norm_num, Fin.sum_univ_one]
  change pairFirstPassageProbability 0 1 (k + 1) = _
  rw [pairFirstPassageProbability_zero_one (k + 1) (by omega),
    pairSumProbability_eq_pairSumAtom (by omega), pairSumAtom_one_total]
  norm_num

/-- The level-zero stopped overshoot has exact `4 / 3` moment four. -/
theorem stoppedPositiveOvershootPowerMoment_zero_eq_four :
    stoppedPositiveOvershootPowerMoment 0 = 4 := by
  unfold stoppedPositiveOvershootPowerMoment
  simp_rw [stoppedJointProbability_zero_mass]
  calc
    _ = (2 / 3 : ℝ) * ∑' k : ℕ, (k : ℝ) * (2 / 3 : ℝ) ^ k := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [pow_succ]
      calc
        _ = (2 / 3 : ℝ) * ((k : ℝ) *
            ((1 / 2 : ℝ) ^ k * (4 / 3 : ℝ) ^ k)) := by ring
        _ = _ := by rw [← mul_pow]; norm_num
    _ = 4 := by
      have h := hasSum_coe_mul_geometric_of_norm_lt_one (r := (2 / 3 : ℝ))
        (by norm_num)
      calc
        (2 / 3 : ℝ) * ∑' k : ℕ, (k : ℝ) * (2 / 3 : ℝ) ^ k =
            (2 / 3 : ℝ) * ((2 / 3 : ℝ) / (1 - 2 / 3 : ℝ) ^ 2) := by rw [h.tsum_eq]
        _ = 4 := by norm_num

/-- The stopped overshoot `4 / 3` moment is at most four at every level. -/
theorem stoppedPositiveOvershootPowerMoment_le_four (s : ℕ) :
    stoppedPositiveOvershootPowerMoment s ≤ 4 := by
  cases s with
  | zero => rw [stoppedPositiveOvershootPowerMoment_zero_eq_four]
  | succ s =>
      rw [stoppedPositiveOvershootPowerMoment_eq_three (by omega)]
      norm_num

/-- The aggregate `4 / 3` moment for `p` fresh pairs after a first-passage
pair, summed over positive stopped overshoots. -/
noncomputable def stoppedPostPassagePairMoment (s p : ℕ) : ℝ :=
  ∑' k : ℕ,
    stoppedJointSuffixMoment s (k + 1) p * (4 / 3 : ℝ) ^ (k + 1)

/-- The stopped post-passage pair moment factors through the stopped
overshoot moment and the exact `p`-pair fresh-word factor. -/
theorem stoppedPostPassagePairMoment_factor (s p : ℕ) :
    stoppedPostPassagePairMoment s p =
      stoppedPositiveOvershootPowerMoment s * (4 : ℝ) ^ p := by
  unfold stoppedPostPassagePairMoment stoppedPositiveOvershootPowerMoment
  simp_rw [stoppedJointSuffixMoment_factor]
  calc
    (∑' k : ℕ, (stoppedJointProbability s (k + 1) * 4 ^ p) *
        (4 / 3 : ℝ) ^ (k + 1)) =
        ∑' k : ℕ, (stoppedJointProbability s (k + 1) *
          (4 / 3 : ℝ) ^ (k + 1)) * 4 ^ p := by
      apply tsum_congr
      intro k
      ring
    _ = _ := by rw [tsum_mul_right]

/-- Uniformly in the passage level, `p` fresh post-passage pairs have the
Appendix E stopped-moment bound `4^(p + 1)`. -/
theorem stoppedPostPassagePairMoment_le (s p : ℕ) :
    stoppedPostPassagePairMoment s p ≤ (4 : ℝ) ^ (p + 1) := by
  rw [stoppedPostPassagePairMoment_factor]
  calc
    stoppedPositiveOvershootPowerMoment s * 4 ^ p ≤ 4 * 4 ^ p :=
      mul_le_mul_of_nonneg_right (stoppedPositiveOvershootPowerMoment_le_four s)
        (by positivity)
    _ = 4 ^ (p + 1) := by
      rw [pow_succ]
      ring

/-- A word in the first-passage event has a positive pair index. -/
theorem pairFirstPassageEvent_index_pos {s j h : ℕ} {w : ValuationWord}
    (hw : pairFirstPassageEvent s j h w) : 0 < j := by
  rcases hw with ⟨hlen, hh, _, htotal⟩
  by_contra hj
  have hj0 : j = 0 := by omega
  subst j
  have hw_nil : w = [] := by
    simpa [List.length_eq_zero_iff] using hlen
  subst w
  simp [ValuationWord.total] at htotal
  omega

/-- Every realized strict passage has the deterministic Appendix E index
bound `J_s ≤ s/2 + 1`. -/
theorem pairFirstPassageEvent_index_le {s j h : ℕ} {w : ValuationWord}
    (hw : pairFirstPassageEvent s j h w) : j ≤ s / 2 + 1 := by
  have hj := pairFirstPassageEvent_index_pos hw
  rcases hw with ⟨_, _, hprefix, _⟩
  have hlen := valuationWord_length_le_total (w.take (2 * (j - 1)))
  have htakeLen : (w.take (2 * (j - 1))).length = 2 * (j - 1) := by
    rw [List.length_take]
    omega
  rw [htakeLen] at hlen
  omega

/-- Every earlier complete pair prefix of a first-passage word remains below
the strict threshold. -/
theorem pairFirstPassageEvent_prior_total_le {s j h r : ℕ} {w : ValuationWord}
    (hw : pairFirstPassageEvent s j h w) (hr : r < j) :
    ValuationWord.total (w.take (2 * r)) ≤ s := by
  rcases hw with ⟨_, _, hprior, _⟩
  have hidx : 2 * r ≤ 2 * (j - 1) := by omega
  exact le_trans (ValuationWord.total_take_mono w hidx) hprior

/-- The terminal total in a first-passage event is strictly above its level. -/
theorem pairFirstPassageEvent_crosses {s j h : ℕ} {w : ValuationWord}
    (hw : pairFirstPassageEvent s j h w) : s < w.total := by
  rcases hw with ⟨_, hh, _, htotal⟩
  omega

end LocalPrimitive
end WordCertDensity
