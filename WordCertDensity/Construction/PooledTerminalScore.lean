/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.PoolCommonShell
import WordCertDensity.Construction.TerminalPaymentLimit
import WordCertDensity.Construction.FanCharge

/-! # Persistent pooled score after terminal payment and actual fan grouping -/

namespace WordCertDensity.Construction
open Filter
open scoped Topology

/-- A single rootwise error costs the fixed reciprocal pool sum, before fan enlargement. -/
theorem pooledTerminal_fan_lower (L θ X : ℝ) (b t j d K k : ℕ) (pool : Finset ℕ)
    {W loss error : ℝ}
    (hscore : W-loss ≤ ∑ root ∈ pool, physicalParametricGraftMark θ L (θ/20) b t j root/root)
    (herr : ∀ root ∈ pool,
      |selectedTerminalMark L (θ/20) X b t j root d K k-
        physicalParametricGraftMark θ L (θ/20) b t j root| ≤ error) :
    W-loss-error*(∑ root ∈ pool, (root : ℝ)⁻¹) ≤
      ∑ x ∈ reducedSourceSet L (θ/20) X b t j d pool,
        reducedSourceCharge L (θ/20) X b t j d x pool*Reference.fan k (x : ZMod (3^k)) := by
  have hs : (∑ root ∈ pool, physicalParametricGraftMark θ L (θ/20) b t j root/root) ≤
      (∑ root ∈ pool, selectedTerminalMark L (θ/20) X b t j root d K k/root)+
        error*(∑ root ∈ pool, (root : ℝ)⁻¹) := by
    calc
      _ ≤ ∑ root ∈ pool, (selectedTerminalMark L (θ/20) X b t j root d K k+error)/root := by
        apply Finset.sum_le_sum
        intro root hroot
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg root)
        have h := (abs_sub_le_iff.mp (herr root hroot)).2
        linarith
      _ = _ := by simp only [div_eq_mul_inv, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  have hfan := selectedTerminalFanCharge L (θ/20) X b t j d K k pool
  linarith

/-- For one fixed graft, the terminal loss is paid uniformly over all later permitted cutoffs. -/
theorem finitePool_terminalFan_eventually {L θ W η : ℝ} {b t : ℕ}
    (hb : 32^5 ≤ b) (hL : 0 < L) (hθ : 0 < θ) (hcap : θ ≤ 1/1000)
    (hpaid : graftOffsetAbsorption b t ≤ 1) (hη : 0 < η) (pool : Finset ℕ)
    (hroot : ∀ root ∈ pool, 16^b ≤ root)
    (hscore : ∀ j, W-η/2 ≤ ∑ root ∈ pool, physicalParametricGraftMark θ L (θ/20) b t j root/root) :
    ∀ᶠ j : ℕ in atTop,
      let B := macroCount L (graftInitialCount b t) j
      let d := ⌊θ*B⌋₊
      let k := parametricLevel θ B
      ∀ X : ℝ,
      (∀ root ∈ pool, ∀ r ∈ physicalGraftRecords L (θ/20) b t j root,
        16^d ≤ graftRecordSource root r ∧ terminalShellLow d (graftRecordSource root r) < X ∧
        X ≤ (2 : ℝ)^(2*terminalRadius d)*terminalShellLow d (graftRecordSource root r)) →
      W-η ≤ ∑ x ∈ reducedSourceSet L (θ/20) X b t j d pool,
        reducedSourceCharge L (θ/20) X b t j d x pool*Reference.fan k (x : ZMod (3^k)) := by
  have hp := selectedTerminalPayment L θ b t hb hL hθ hcap hpaid
  have he : Tendsto (fun j => terminalPaymentError b t θ (macroCount L (graftInitialCount b t) j)*
      (∑ root ∈ pool, (root : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hp.2.1.mul_const (∑ root ∈ pool, (root : ℝ)⁻¹)
  filter_upwards [hp.2.2, he.eventually_lt_const (by linarith : 0 < η/2)] with j hpay herror
  dsimp only at hpay herror ⊢
  intro X hparents
  have h := pooledTerminal_fan_lower L θ X b t j _ _ _ pool (hscore j)
    (fun root hr => hpay root (hroot root hr) X (hparents root hr))
  linarith

/-- Common deterministic endpoints discharge every root's premises in the pooled fan bound. -/
theorem finitePool_commonFan_eventually {L θ W η : ℝ} {b t target : ℕ}
    (hb : 32^5 ≤ b) (hL : 0 < L) (hθ : 0 < θ) (hcap : θ ≤ 1/1000)
    (hpaid : graftOffsetAbsorption b t ≤ 1) (hη : 0 < η)
    (pool : Finset ℕ) (hne : pool.Nonempty) (clock : ℕ → ℕ)
    (hheight : ∀ root ∈ pool, 16^b ≤ root)
    (hpath : ∀ root ∈ pool, ReachesIn root target (clock root))
    (hscore : ∀ j, W-η/2 ≤ ∑ root ∈ pool, physicalParametricGraftMark θ L (θ/20) b t j root/root) :
    ∀ᶠ j : ℕ in atTop,
      let B := macroCount L (graftInitialCount b t) j
      let d := ⌊θ*B⌋₊
      let k := parametricLevel θ B
      ∀ X : ℝ,
      (2 : ℝ)^commonLowExponent θ (stoppedExpectation displacement)
        (terminalPoolUpper b t pool) B < X →
      X ≤ (2 : ℝ)^commonHighExponent θ (stoppedExpectation displacement)
        (terminalPoolLower b pool hne) B →
      W-η ≤ ∑ x ∈ reducedSourceSet L (θ/20) X b t j d pool,
        reducedSourceCharge L (θ/20) X b t j d x pool*Reference.fan k (x : ZMod (3^k)) := by
  filter_upwards [finitePool_commonParents_eventually hθ hcap hL hb hpaid pool hne clock hheight hpath,
    finitePool_terminalFan_eventually hb hL hθ hcap hpaid hη pool hheight hscore] with j hparents hfan
  dsimp only at hparents hfan ⊢
  intro X hlo hhi
  exact hfan X (hparents X hlo hhi)

end WordCertDensity.Construction
