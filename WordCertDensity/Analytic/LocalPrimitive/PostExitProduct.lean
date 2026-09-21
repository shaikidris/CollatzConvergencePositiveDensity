/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.WhiteVisitScan

/-! # Original-word post-exit product and predictable-sample comparison

The product discounts precisely a white state whose next pair has total three.
The geometric white-visit probability is retained as an explicit remaining
input, while the selected-mark contribution is evaluated on the original law.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- Literal product of marked-white discounts over a finite pair window. -/
noncomputable def whiteWindowProduct (white : ℕ → ℤ → Prop) (z : ℝ≥0∞) :
    ℕ → ℕ → ℤ → ValuationWord → ℝ≥0∞
  | 0, _, _, _ => 1
  | h + 1, j, l, w =>
      (if white j l ∧ ValuationWord.total (w.take 2) = 3 then z else 1) *
        whiteWindowProduct white z h (j + 1)
          (l + ValuationWord.total (w.take 2)) (w.drop 2)

/-- The literal product is the discount raised to the actual number of
marked white states, without any independence assertion. -/
theorem whiteWindowProduct_eq_pow (white : ℕ → ℤ → Prop) (z : ℝ≥0∞)
    (h j : ℕ) (l : ℤ) (w : ValuationWord) :
    whiteWindowProduct white z h j l w = z ^ whiteMarkCount white h j l w := by
  induction h generalizing j l w with
  | zero => simp [whiteWindowProduct, whiteMarkCount]
  | succ h ih =>
      by_cases hm : white j l ∧ ValuationWord.total (w.take 2) = 3
      · simp [whiteWindowProduct, whiteMarkCount, hm, ih, pow_add]
      · simp [whiteWindowProduct, whiteMarkCount, hm, ih]

/-- A product of discounts in the unit interval never exceeds one. -/
theorem whiteWindowProduct_le_one (white : ℕ → ℤ → Prop) {z : ℝ≥0∞}
    (hz : z ≤ 1) (h j : ℕ) (l : ℤ) (w : ValuationWord) :
    whiteWindowProduct white z h j l w ≤ 1 := by
  rw [whiteWindowProduct_eq_pow]
  exact pow_le_one₀ bot_le hz

/-- Outside the shortage of white visits, the full window product is at
most the weight of the first k predictable samples. -/
theorem whiteWindowProduct_le_selected (white : ℕ → ℤ → Prop) {z : ℝ≥0∞}
    (hz : z ≤ 1) (h H k j : ℕ) (l : ℤ) (w : ValuationWord) (hH : h ≤ H)
    (hk : k ≤ whiteVisitCount white h j l w) :
    whiteWindowProduct white z h j l w ≤ z ^ predictableMarkCount white H k j l w := by
  rw [whiteWindowProduct_eq_pow]
  exact pow_le_pow_of_le_one bot_le hz
    (predictableMarkCount_le_window_marks white h H k j l w hH hk)

/-- The original post-window expectation is bounded by the white-visit
shortage mass plus the exact predictable quarter-mark moment. This isolates
the geometric obligation needed for the post-exit estimate. -/
theorem whiteWindowProduct_moment_le (white : ℕ → ℤ → Prop) {z : ℝ≥0∞}
    (hz : z ≤ 1) (N : ℕ) (hext : ∀ j, N ≤ j → ∀ l, white j l)
    (h H k j : ℕ) (l : ℤ) (hH : h ≤ H) (hquota : k + (N - j) ≤ H) :
    (∑' w : ValuationWord, Reference.wordPMF (2 * H) w *
      whiteWindowProduct white z h j l w) ≤
      (∑' w : ValuationWord,
        @ite ℝ≥0∞ (whiteVisitCount white h j l w < k) (Classical.propDecidable _)
          (Reference.wordPMF (2 * H) w) 0) +
        ((1 / 4 : ℝ≥0∞) * z + 3 / 4) ^ k := by
  have hp (w : ValuationWord) :
      whiteWindowProduct white z h j l w ≤
        (if whiteVisitCount white h j l w < k then 1 else 0) +
          z ^ predictableMarkCount white H k j l w := by
    by_cases hw : whiteVisitCount white h j l w < k
    · rw [if_pos hw]
      exact (whiteWindowProduct_le_one white hz h j l w).trans (le_self_add)
    · rw [if_neg hw, zero_add]
      exact whiteWindowProduct_le_selected white hz h H k j l w hH (by omega)
  calc
    _ ≤ ∑' w : ValuationWord,
        ((@ite ℝ≥0∞ (whiteVisitCount white h j l w < k) (Classical.propDecidable _)
          (Reference.wordPMF (2 * H) w) 0) +
            Reference.wordPMF (2 * H) w * z ^ predictableMarkCount white H k j l w) := by
      apply ENNReal.tsum_le_tsum
      intro w
      have ht := mul_le_mul_right (hp w) (Reference.wordPMF (2 * H) w)
      by_cases hw : whiteVisitCount white h j l w < k <;>
        simpa [hw, mul_add] using ht
    _ = _ := by
      rw [ENNReal.tsum_add, predictableMarkCount_moment white z N hext H k j l hquota]

/-- White visits in a window depend only on its sampled prefix. -/
theorem whiteVisitCount_take (white : ℕ → ℤ → Prop) (h j : ℕ) (l : ℤ)
    (w : ValuationWord) :
    whiteVisitCount white h j l (w.take (2 * h)) = whiteVisitCount white h j l w := by
  induction h generalizing j l w with
  | zero => rfl
  | succ h ih =>
      simp only [whiteVisitCount, List.take_take, List.drop_take]
      rw [min_eq_left (by omega : 2 ≤ 2 * (h + 1)),
        show 2 * (h + 1) - 2 = 2 * h by omega, ih]

/-- The window product does not inspect the appended future. -/
theorem whiteWindowProduct_take (white : ℕ → ℤ → Prop) (z : ℝ≥0∞)
    (h j : ℕ) (l : ℤ) (w : ValuationWord) :
    whiteWindowProduct white z h j l (w.take (2 * h)) =
      whiteWindowProduct white z h j l w := by
  induction h generalizing j l w with
  | zero => rfl
  | succ h ih =>
      simp only [whiteWindowProduct, List.take_take, List.drop_take]
      rw [min_eq_left (by omega : 2 ≤ 2 * (h + 1)),
        show 2 * (h + 1) - 2 = 2 * h by omega, ih]

/-- Appending fresh letters leaves the original window expectation unchanged. -/
theorem whiteWindowProduct_moment_horizon (white : ℕ → ℤ → Prop) (z : ℝ≥0∞)
    (h H j : ℕ) (l : ℤ) (hH : h ≤ H) :
    (∑' w : ValuationWord, Reference.wordPMF (2 * h) w *
      whiteWindowProduct white z h j l w) =
    ∑' w : ValuationWord, Reference.wordPMF (2 * H) w *
      whiteWindowProduct white z h j l w := by
  have hm := PMFMoment.sum_map (Reference.wordPMF (2 * H))
    (fun w => w.take (2 * h)) (whiteWindowProduct white z h j l)
  rw [Reference.wordPMF_map_take_of_le (Nat.mul_le_mul_left 2 hH)] at hm
  simpa only [whiteWindowProduct_take] using hm

/-- The shortage of white visits is also unchanged by a fresh extension. -/
theorem whiteVisitCount_probability_horizon (white : ℕ → ℤ → Prop)
    (h H k j : ℕ) (l : ℤ) (hH : h ≤ H) :
    Gated.probability (Reference.wordPMF (2 * h))
      (fun w => whiteVisitCount white h j l w < k) =
    Gated.probability (Reference.wordPMF (2 * H))
      (fun w => whiteVisitCount white h j l w < k) := by
  have hm := Gated.probability_map (Reference.wordPMF (2 * H))
    (fun w => w.take (2 * h)) (fun w => whiteVisitCount white h j l w < k)
  rw [Reference.wordPMF_map_take_of_le (Nat.mul_le_mul_left 2 hH)] at hm
  simpa only [whiteVisitCount_take] using hm

/-- Real-valued window estimate on its own original horizon. The only
unevaluated probability is the geometric shortage of white visits. -/
theorem whiteWindowProduct_expectation_le (white : ℕ → ℤ → Prop) {z : ℝ≥0∞}
    (hz : z ≤ 1) (N : ℕ) (hext : ∀ j, N ≤ j → ∀ l, white j l)
    (h k j : ℕ) (l : ℤ) :
    (∑' w : ValuationWord, Reference.wordPMF (2 * h) w *
      whiteWindowProduct white z h j l w).toReal ≤
      Gated.probability (Reference.wordPMF (2 * h))
        (fun w => whiteVisitCount white h j l w < k) +
        ((1 / 4 : ℝ) * z.toReal + 3 / 4) ^ k := by
  let H := h + k + N
  have hH : h ≤ H := by dsimp [H]; omega
  have hquota : k + (N - j) ≤ H := by dsimp [H]; omega
  have hzfin : z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hz
  have hcfin : ((1 / 4 : ℝ≥0∞) * z + 3 / 4) ^ k ≠ ⊤ := by finiteness
  have hbad := Gated.event_ne_top (Reference.wordPMF (2 * H))
    (fun w => whiteVisitCount white h j l w < k)
  have he := whiteWindowProduct_moment_le white hz N hext h H k j l hH hquota
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hbad, hcfin⟩) he
  rw [ENNReal.toReal_add hbad hcfin] at hr
  change (∑' w : ValuationWord, Reference.wordPMF (2 * H) w *
    whiteWindowProduct white z h j l w).toReal ≤
    Gated.probability (Reference.wordPMF (2 * H))
      (fun w => whiteVisitCount white h j l w < k) +
      (((1 / 4 : ℝ≥0∞) * z + 3 / 4) ^ k).toReal at hr
  rw [← whiteWindowProduct_moment_horizon white z h H j l hH,
    ← whiteVisitCount_probability_horizon white h H k j l hH] at hr
  rw [ENNReal.toReal_pow,
    ENNReal.toReal_add (a := (1 / 4 : ℝ≥0∞) * z) (b := 3 / 4)
      (by finiteness) (by finiteness), ENNReal.toReal_mul] at hr
  simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hr

/-- Exponential form of the finite-window product estimate. For the paper's
discount a = 2 epsilon squared, the selected-sample term is exp(-a k / 4). -/
theorem whiteWindowProduct_expectation_le_exp (white : ℕ → ℤ → Prop)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (N : ℕ)
    (hext : ∀ j, N ≤ j → ∀ l, white j l) (h k j : ℕ) (l : ℤ) :
    (∑' w : ValuationWord, Reference.wordPMF (2 * h) w *
      whiteWindowProduct white (ENNReal.ofReal (1 - a)) h j l w).toReal ≤
      Gated.probability (Reference.wordPMF (2 * h))
        (fun w => whiteVisitCount white h j l w < k) +
        Real.exp (-(a * (k : ℝ) / 4)) := by
  have hz : ENNReal.ofReal (1 - a) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hm := whiteWindowProduct_expectation_le white hz N hext h k j l
  have hb : (1 / 4 : ℝ) * (ENNReal.ofReal (1 - a)).toReal + 3 / 4 = 1 - a / 4 := by
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hb] at hm
  apply hm.trans
  apply add_le_add_right
  calc
    (1 - a / 4) ^ k ≤ Real.exp (-a / 4) ^ k := by
      apply pow_le_pow_left₀ (by linarith)
      have he := Real.add_one_le_exp (-a / 4)
      linarith
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The original nonnegative product expectation is finite and at most one. -/
theorem whiteWindowProduct_mass_le_one (white : ℕ → ℤ → Prop) {z : ℝ≥0∞}
    (hz : z ≤ 1) (h j : ℕ) (l : ℤ) :
    (∑' w : ValuationWord, Reference.wordPMF (2 * h) w *
      whiteWindowProduct white z h j l w) ≤ 1 := by
  calc
    _ ≤ ∑' w : ValuationWord, Reference.wordPMF (2 * h) w := by
      apply ENNReal.tsum_le_tsum
      intro w
      simpa using mul_le_mul_right (whiteWindowProduct_le_one white hz h j l w)
        (Reference.wordPMF (2 * h) w)
    _ = 1 := PMF.tsum_coe _

/-- Exact source-law one-step recursion for the full window product. -/
theorem whiteWindowProduct_moment_succ (white : ℕ → ℤ → Prop) (z : ℝ≥0∞)
    (h j : ℕ) (l : ℤ) :
    (∑' w : ValuationWord, Reference.wordPMF (2 * (h + 1)) w *
      whiteWindowProduct white z (h + 1) j l w) =
    ∑' u : ValuationWord, Reference.wordPMF 2 u *
      (if white j l ∧ u.total = 3 then z else 1) *
        ∑' v : ValuationWord, Reference.wordPMF (2 * h) v *
          whiteWindowProduct white z h (j + 1) (l + u.total) v := by
  rw [show 2 * (h + 1) = 2 + 2 * h by omega,
    ← Reference.wordPMF_append 2 (2 * h), PMFMoment.sum_bind]
  simp_rw [PMFMoment.sum_map]
  apply tsum_congr
  intro u
  by_cases hu : u.length = 2
  · simp only [whiteWindowProduct, List.take_left' hu, List.drop_left' hu]
    rw [mul_assoc]
    congr 1
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro v
    ac_rfl
  · simp [Reference.wordPMF_eq_zero_of_length_ne 2 u hu]

end WordCertDensity.LocalPrimitive
