/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalLogScale
import WordCertDensity.Construction.ParametricLevels

/-! # Fine precision and parent growth for reduced terminal sources -/

namespace WordCertDensity.Construction
open Filter
open scoped Topology

/-- The coarsest radius bound is valid even outside the eventual sharp domain. -/
theorem terminalRadius_le_twice (b : ℕ) : terminalRadius b ≤ 2*b := by
  have hw := terminalWidth_le b
  unfold terminalRadius
  omega

/-- The lower shell keeps the physical parent's full height. -/
theorem terminalShellLow_coarse {b : ℕ} (hb : 0 < b) {y : ℝ} (hy : 0 ≤ y) :
    (1-terminalEta b)*y/(2*(3 : ℝ)^b) ≤ terminalShellLow b y := by
  have hr : (2 : ℝ)^terminalRadius b ≤ 4^b := by
    calc
      _ ≤ (2 : ℝ)^(2*b) := pow_le_pow_right₀ (by norm_num) (terminalRadius_le_twice b)
      _ = 4^b := by rw [pow_mul]; norm_num
  have hs : 1/(3 : ℝ)^b ≤ terminalScale b 0 := by
    unfold terminalScale
    simp only [pow_zero, mul_one]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hr (by positivity : (0 : ℝ) ≤ 3^b)]
  have he := (terminalEta_bounds hb).2.le
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg (sub_nonneg.mpr he) hy)
  unfold terminalShellLow
  calc
    _ = ((1-terminalEta b)*y*(1/(3 : ℝ)^b))/2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hm (by norm_num)

/-- The exact printed precision envelope, with g_b=2(1-eta_b). -/
noncomputable def terminalPrecisionEnvelope (b : ℕ) : ℝ :=
  6/(1-terminalEta b)*(9/16 : ℝ)^b

/-- The ceiling case k=b+1 is paid uniformly for every permitted cutoff. -/
theorem terminalPrecision_bound {b k : ℕ} (hb : 0 < b) (hk : k ≤ b+1)
    {y X : ℝ} (hy : (16 : ℝ)^b ≤ y) (hX : terminalShellLow b y < X) :
    (3 : ℝ)^k/X ≤ terminalPrecisionEnvelope b := by
  have hyp : 0 < y := (by positivity : (0 : ℝ)<16^b).trans_le hy
  have hXp := (terminalShellLow_pos hb hyp).trans hX
  have he : 0 < 1-terminalEta b := sub_pos.mpr (terminalEta_bounds hb).2
  have hsmall : (1-terminalEta b)*(16 : ℝ)^b/(2*3^b) < X :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hy he.le)
      (by positivity)).trans_lt ((terminalShellLow_coarse hb hyp.le).trans_lt hX)
  have hp : (3 : ℝ)^k ≤ 3*3^b := by
    simpa only [pow_succ, mul_comm] using
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤3) hk)
  have hid : terminalPrecisionEnvelope b*((1-terminalEta b)*16^b/(2*3^b)) = 3*3^b := by
    unfold terminalPrecisionEnvelope
    rw [div_pow]
    have h9 : (9 : ℝ)^b = (3^b)^2 := by
      calc
        _ = ((3 : ℝ)^2)^b := by norm_num
        _ = (3^b)^2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [h9]
    field_simp
    ring
  have hen : 0 ≤ terminalPrecisionEnvelope b := by unfold terminalPrecisionEnvelope; positivity
  apply (div_le_iff₀ hXp).mpr
  calc
    _ ≤ 3*3^b := hp
    _ = _ := hid.symm
    _ ≤ terminalPrecisionEnvelope b*X := mul_le_mul_of_nonneg_left hsmall.le hen

/-- The full precision envelope tends to zero. -/
theorem terminalPrecisionEnvelope_tendsto : Tendsto terminalPrecisionEnvelope atTop (𝓝 0) := by
  have hc : Tendsto (fun b => (6 : ℝ)/(1-terminalEta b)) atTop (𝓝 6) := by
    have h : Tendsto (fun b : ℕ => (6 : ℝ)/(1-terminalEta b)) atTop (𝓝 (6/(1-0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.sub terminalEta_tendsto)
        (by norm_num : (1 : ℝ)-0 ≠ 0)
    simpa only [sub_zero, div_one] using h
  have h : Tendsto (fun b : ℕ => (6 : ℝ)/(1-terminalEta b)*(9/16 : ℝ)^b) atTop (𝓝 (6*0)) :=
    hc.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤9/16)
      (by norm_num : (9/16 : ℝ)<1))
  unfold terminalPrecisionEnvelope
  simpa only [mul_zero] using h

/-- The actual floored terminal depth diverges for each fixed positive theta. -/
theorem terminalDepth_tendsto {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun B : ℕ => ⌊θ*B⌋₊) atTop atTop := tendsto_nat_floor_mul_atTop θ hθ

/-- Uniform precision along any diverging original-count selector. -/
theorem terminalSelected_precision {α : Type*} {l : Filter α} {B : α → ℕ}
    (hB : Tendsto B l atTop) {θ : ℝ} (hθ : 0 < θ) {y X : α → ℝ}
    (hy : ∀ᶠ a in l, (16 : ℝ)^⌊θ*B a⌋₊ ≤ y a)
    (hX : ∀ᶠ a in l, terminalShellLow ⌊θ*B a⌋₊ (y a) < X a) :
    Tendsto (fun a => (3 : ℝ)^parametricLevel θ (B a)/X a) l (𝓝 0) := by
  have hd := (terminalDepth_tendsto hθ).comp hB
  apply squeeze_zero' ?_ ?_ (terminalPrecisionEnvelope_tendsto.comp hd)
  · filter_upwards [hd.eventually (eventually_ge_atTop 1), hy, hX] with a ha hay hax
    change 1 ≤ ⌊θ*B a⌋₊ at ha
    have hp : 0 < y a := (by positivity : (0 : ℝ)<16^⌊θ*B a⌋₊).trans_le hay
    exact div_nonneg (by positivity) ((terminalShellLow_pos (by omega) hp).trans hax).le
  · filter_upwards [hd.eventually (eventually_ge_atTop 1), hy, hX] with a ha hay hax
    change 1 ≤ ⌊θ*B a⌋₊ at ha
    exact terminalPrecision_bound (by omega) (Nat.ceil_le_floor_add_one _) hay hax

/-- On the sharp terminal domain, the lower shell multiplier already exceeds one. -/
theorem terminalShellLow_one_gt {b : ℕ} (hb : 200 ≤ b) : 1 < terminalShellLow b 1 := by
  have hbp : 0 < b := by omega
  have hr := (terminalRadius_bounds hb).2
  have he := (terminalCorrection_log_bounds hbp).1
  have hbR : (200 : ℝ) ≤ b := by exact_mod_cast hb
  have hRatio := mul_lt_mul_of_pos_right Head.logRatio_lt_eight_fifths
    (Nat.cast_pos.mpr hbp : (0 : ℝ)<b)
  have hlog : 0 < binaryLog (terminalShellLow b 1) := by
    rw [terminalShellLow_binaryLog hbp]
    nlinarith
  have hn : 0 < Real.log (terminalShellLow b 1) := by
    have ht := (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ)<2))).mp hlog
    simpa only [zero_mul] using ht
  exact (Real.log_pos_iff (terminalShellLow_pos hbp (by norm_num)).le).mp hn

/-- Reduced physical sources are at least their own physical parents. -/
theorem terminalPhysical_parent_le {b u y x : ℕ} (hb : 200 ≤ b) {w : ValuationWord}
    (hw : TerminalWord b u 1 w) (hy : 16^b ≤ y) (hp : PhysicalHistory w y x) : y ≤ x := by
  have hyp : (0 : ℝ)<y := by exact_mod_cast hp.root_pos
  have hlo := (terminalPhysical_shell (by omega) hw hy hp).1
  have hscale : terminalShellLow b y = (y : ℝ)*terminalShellLow b 1 := by
    unfold terminalShellLow
    ring
  have hmul : (y : ℝ) ≤ terminalShellLow b y := by
    rw [hscale]
    nlinarith [terminalShellLow_one_gt hb]
  have htwo : (1 : ℝ) ≤ 2^u := one_le_pow₀ (by norm_num)
  have hs := mul_le_mul_of_nonneg_right htwo
    (terminalShellLow_pos (b := b) (by omega) hyp).le
  have hstep : terminalShellLow b y ≤ 2^u*terminalShellLow b y := by simpa only [one_mul] using hs
  exact_mod_cast hmul.trans (hstep.trans hlo)

end WordCertDensity.Construction
