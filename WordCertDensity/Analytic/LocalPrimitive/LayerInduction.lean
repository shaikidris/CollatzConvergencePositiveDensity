/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # Conditional weighted layer induction for Appendix E.7

The height coordinate is a residue in a positive period. The distance coordinate
is the remaining number of pair steps. Probability estimates and stopped
comparisons must be supplied separately; this module is not a primitive-decay
producer. In particular, no statement here discharges E-L4 or E-L5a.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- Canonical residue of any integer height, including negative heights. -/
def layerHeightResidue (P : ℕ) (l : ℤ) : Fin (P + 1) :=
  ⟨(l % (P + 1 : ℕ)).toNat, by
    have hpos : (0 : ℤ) < (P + 1 : ℕ) := by omega
    have hn := Int.emod_nonneg l (ne_of_gt hpos)
    have hl := Int.emod_lt_of_pos l hpos
    omega⟩

/-- Restrict an integer-height potential to representatives of its period. -/
def residuePotential (P : ℕ) (U : ℕ → ℤ → ℝ) : ℕ → Fin (P + 1) → ℝ :=
  fun r l => U r l

/-- A periodic potential on all integer heights is exactly recovered from
its finite residue representation; no quadrant restriction is imposed. -/
theorem residuePotential_eq {P : ℕ} (U : ℕ → ℤ → ℝ)
    (hperiod : ∀ r, Function.Periodic (U r) (P + 1 : ℕ)) (r : ℕ) (l : ℤ) :
    residuePotential P U r (layerHeightResidue P l) = U r l := by
  have hpos : (0 : ℤ) < (P + 1 : ℕ) := by omega
  have hn := Int.emod_nonneg l (ne_of_gt hpos)
  change U r (Int.toNat (l % (P + 1 : ℕ))) = U r l
  rw [Int.toNat_of_nonneg hn, Int.emod_def]
  simpa [mul_comm] using (hperiod r).sub_int_mul_eq (l / (P + 1 : ℕ)) (x := l)

/-- E.7's weight, including the terminal distance zero. -/
def layerWeight (B r : ℕ) : ℝ := (max (r : ℝ) 1) ^ B

/-- The terminal convention makes every layer weight strictly positive. -/
theorem layerWeight_pos (B r : ℕ) : 0 < layerWeight B r := by
  unfold layerWeight
  positivity

/-- The finite maximum over all layers up to m and all height residues.
The actual positive period is P + 1. -/
noncomputable def layerMaximum {P : ℕ} (V : ℕ → Fin (P + 1) → ℝ)
    (B m : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun x : Fin (m + 1) × Fin (P + 1) => layerWeight B x.1 * V x.1 x.2)

/-- A bound on the finite maximum is exactly a bound on its displayed entries. -/
theorem layerMaximum_le_iff {P B m : ℕ} {V : ℕ → Fin (P + 1) → ℝ} {D : ℝ} :
    layerMaximum V B m ≤ D ↔
      ∀ r, r ≤ m → ∀ l, layerWeight B r * V r l ≤ D := by
  unfold layerMaximum
  rw [Finset.sup'_le_iff]
  constructor
  · intro h r hr l
    exact h (⟨r, by omega⟩, l) (Finset.mem_univ _)
  · intro h x _
    exact h x.1 (by omega) x.2

/-- Every displayed entry is at most the layer maximum. -/
theorem weighted_le_layerMaximum {P B m r : ℕ} (V : ℕ → Fin (P + 1) → ℝ)
    (hr : r ≤ m) (l : Fin (P + 1)) :
    layerWeight B r * V r l ≤ layerMaximum V B m :=
  layerMaximum_le_iff.mp le_rfl r hr l

/-- Adding layers cannot decrease their maximum. -/
theorem layerMaximum_mono {P B m k : ℕ} (V : ℕ → Fin (P + 1) → ℝ)
    (hmk : m ≤ k) : layerMaximum V B m ≤ layerMaximum V B k := by
  apply layerMaximum_le_iff.mpr
  intro r hr l
  exact weighted_le_layerMaximum V (hr.trans hmk) l

/-- Terminal potential one gives exactly D₀ = 1. -/
theorem layerMaximum_zero {P B : ℕ} (V : ℕ → Fin (P + 1) → ℝ)
    (hzero : ∀ l, V 0 l = 1) : layerMaximum V B 0 = 1 := by
  apply le_antisymm
  · apply layerMaximum_le_iff.mpr
    intro r hr l
    have : r = 0 := by omega
    subst r
    simp [layerWeight, hzero]
  · simpa [layerWeight, hzero] using
      weighted_le_layerMaximum (B := B) V (m := 0) (r := 0) (by omega) 0

/-- Every layer maximum retains the terminal contribution. -/
theorem one_le_layerMaximum {P B m : ℕ} (V : ℕ → Fin (P + 1) → ℝ)
    (hzero : ∀ l, V 0 l = 1) : 1 ≤ layerMaximum V B m := by
  rw [← layerMaximum_zero (B := B) V hzero]
  exact layerMaximum_mono V (Nat.zero_le m)

/-- Only the newly added layer is needed to prove stabilization. -/
theorem layerMaximum_succ_eq {P B m : ℕ} (V : ℕ → Fin (P + 1) → ℝ)
    (hnew : ∀ l, layerWeight B (m + 1) * V (m + 1) l ≤ layerMaximum V B m) :
    layerMaximum V B (m + 1) = layerMaximum V B m := by
  apply le_antisymm
  · apply layerMaximum_le_iff.mpr
    intro r hr l
    by_cases h : r ≤ m
    · exact weighted_le_layerMaximum V h l
    · have : r = m + 1 := by omega
      subst r
      exact hnew l
  · exact layerMaximum_mono V (Nat.le_succ m)

/-- Below a positive threshold the unit potential bound pays all weights. -/
theorem layerMaximum_base {P B M m : ℕ} (V : ℕ → Fin (P + 1) → ℝ)
    (hM : 0 < M) (hm : m < M) (hV : ∀ r, r ≤ m → ∀ l, V r l ≤ 1) :
    layerMaximum V B m ≤ (M : ℝ) ^ B := by
  apply layerMaximum_le_iff.mpr
  intro r hr l
  have hw : layerWeight B r ≤ (M : ℝ) ^ B := by
    apply pow_le_pow_left₀ (by positivity)
    apply max_le
    · exact_mod_cast (show r ≤ M by omega)
    · exact_mod_cast hM
  exact (mul_le_of_le_one_right (layerWeight_pos B r).le
    (hV r hr l)).trans hw

/-- White-exit probability and the short-crossing distortion close E.short. -/
theorem shortExit_budget {d p : ℝ} (hd : 0 ≤ d)
    (hp : 15 / 16 ≤ p) : (1 + d / 8) * (1 - p * d / 2) ≤ 1 := by
  have hpd : (15 / 16 : ℝ) * d ≤ p * d := mul_le_mul_of_nonneg_right hp hd
  have hmul : (1 + d / 8) * (1 - p * d / 2) ≤
      (1 + d / 8) * (1 - 15 * d / 32) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  nlinarith [sq_nonneg d]

/-- The two long-crossing payments are each one quarter of the layer budget.
The exceptional event is paid using the unit bound, hence D ≥ 1 is essential. -/
theorem longExit_budget {D a t : ℝ} (hD : 1 ≤ D)
    (ha : a ≤ 1 / 4) (ht : t ≤ 1 / 4) : D * a + t ≤ D := by
  have ha' := mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ D)
  linarith

/-- Combine the white and nonwhite stopped contributions. The probability p
is a mass under the original stopped law; the two contributions must be
bounded under that same law. The first inequality retains the stopping and
weight-distortion obligation explicitly. -/
theorem shortExit_comparison {u D d p cw cb : ℝ} (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hp : 15 / 16 ≤ p)
    (hstop : u ≤ (1 + d / 8) * (cw + cb))
    (hcw : cw ≤ D * (1 - d / 2) * p) (hcb : cb ≤ D * (1 - p)) : u ≤ D := by
  calc
    u ≤ (1 + d / 8) * (cw + cb) := hstop
    _ ≤ (1 + d / 8) * (D * (1 - d / 2) * p + D * (1 - p)) :=
      mul_le_mul_of_nonneg_left (add_le_add hcw hcb) (by positivity)
    _ = D * ((1 + d / 8) * (1 - p * d / 2)) := by ring
    _ ≤ D * 1 := mul_le_mul_of_nonneg_left (shortExit_budget hd hp) hD
    _ = D := mul_one D

/-- Short-exit assembly for one normalized countable stopped law. Here f is
the weighted potential at the exit and W is the white-exit event. This avoids
replacing the law of a stopped word by an independent fresh process. The
stopping/distortion comparison remains an explicit hypothesis. -/
theorem shortExit_stopped_sum {Ω : Type*} (μ f : Ω → ℝ) (W : Ω → Prop)
    [DecidablePred W] {u D d : ℝ} (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hμ : ∀ i, 0 ≤ μ i) (hμs : Summable μ) (hnorm : ∑' i, μ i = 1)
    (hmask : Summable (fun i => if W i then μ i else 0))
    (hfs : Summable (fun i => μ i * f i))
    (hprob : 15 / 16 ≤ ∑' i, if W i then μ i else 0)
    (hwhite : ∀ i, W i → f i ≤ D * (1 - d / 2))
    (hblack : ∀ i, ¬ W i → f i ≤ D)
    (hstop : u ≤ (1 + d / 8) * ∑' i, μ i * f i) : u ≤ D := by
  let p := ∑' i, if W i then μ i else 0
  have hbound : (∑' i, μ i * f i) ≤ D * (1 - p * d / 2) := by
    calc
      (∑' i, μ i * f i) ≤
          ∑' i, (μ i * D - (if W i then μ i else 0) * (D * d / 2)) := by
        apply Summable.tsum_le_tsum _ hfs ((hμs.mul_right D).sub (hmask.mul_right _))
        intro i
        by_cases hi : W i
        · simp only [if_pos hi]
          calc
            μ i * f i ≤ μ i * (D * (1 - d / 2)) :=
              mul_le_mul_of_nonneg_left (hwhite i hi) (hμ i)
            _ = μ i * D - μ i * (D * d / 2) := by ring
        · simp only [if_neg hi, zero_mul, sub_zero]
          exact mul_le_mul_of_nonneg_left (hblack i hi) (hμ i)
      _ = D * (1 - p * d / 2) := by
        rw [(hμs.mul_right D).tsum_sub (hmask.mul_right _),
          tsum_mul_right, tsum_mul_right, hnorm]
        dsimp [p]
        ring
  calc
    u ≤ (1 + d / 8) * ∑' i, μ i * f i := hstop
    _ ≤ (1 + d / 8) * (D * (1 - p * d / 2)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = D * ((1 + d / 8) * (1 - p * d / 2)) := by ring
    _ ≤ D * 1 := mul_le_mul_of_nonneg_left (shortExit_budget hd hprob) hD
    _ = D := mul_one D

/-- The manuscript's quadratic threshold pays the terminal exponential tail.
The standard bound log x ≤ 2√x suffices with the printed constant 2560. -/
theorem terminalPayment_le_quarter {B m : ℕ}
    (hm : (2560 * ((B : ℝ) + 1)) ^ 2 ≤ (m : ℝ)) :
    layerWeight B m * Real.exp (-(m : ℝ) / 640) ≤ 1 / 4 := by
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs := Real.sq_sqrt hm0
  have hs0 := Real.sqrt_nonneg (m : ℝ)
  have hroot : 2560 * ((B : ℝ) + 1) ≤ Real.sqrt m := by nlinarith
  have hm1 : (1 : ℝ) ≤ m := by nlinarith
  have hm3840 : (3840 : ℝ) ≤ m := by nlinarith
  have hlog : Real.log m ≤ 2 * Real.sqrt m := by
    have h := Real.log_le_rpow_div hm0 (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hprod := mul_nonneg (by linarith : 0 ≤ Real.sqrt m - 2560 * (B : ℝ)) hs0
  have hlogB := mul_le_mul_of_nonneg_left hlog hB
  have hexponent : (B : ℝ) * Real.log m - (m : ℝ) / 640 ≤ -(m : ℝ) / 1280 := by
    nlinarith
  have hfour : (4 : ℝ) ≤ Real.exp ((m : ℝ) / 1280) := by
    have h := Real.add_one_le_exp ((m : ℝ) / 1280)
    linarith
  calc
    layerWeight B m * Real.exp (-(m : ℝ) / 640) =
        Real.exp ((B : ℝ) * Real.log m - (m : ℝ) / 640) := by
      rw [layerWeight, max_eq_left hm1, sub_eq_add_neg, Real.exp_add,
        Real.exp_nat_mul, Real.exp_log (by linarith : (0 : ℝ) < m)]
      congr 2
      ring
    _ ≤ Real.exp (-(m : ℝ) / 1280) := Real.exp_le_exp.mpr hexponent
    _ ≤ 1 / 4 := by
      rw [neg_div, Real.exp_neg]
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hfour

/-- E.postexit and the separately paid terminal event close the long case. -/
theorem longExit_comparison {B m : ℕ} {u D e t : ℝ} (hD : 1 ≤ D)
    (hstop : u ≤ D * (10 : ℝ) ^ B * e + layerWeight B m * t)
    (hpost : e ≤ 1 / (4 * (10 : ℝ) ^ B))
    (htail : layerWeight B m * t ≤ 1 / 4) : u ≤ D := by
  have hten : (0 : ℝ) < 10 ^ B := by positivity
  have he : (10 : ℝ) ^ B * e ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * 10 ^ B)).mp hpost
    nlinarith
  exact hstop.trans (by
    simpa [mul_assoc] using longExit_budget hD he htail)

/-- The white-kernel mass and the weight-ratio estimate yield contraction. -/
theorem whiteLayer_comparison {B m : ℕ} {u D d : ℝ} (hD : 0 ≤ D)
    (hd : 0 ≤ d)
    (hkernel : u ≤ (1 - d) * D / layerWeight B (m - 1))
    (hratio : (1 - d) * layerWeight B m ≤
      (1 - d / 2) * layerWeight B (m - 1)) : layerWeight B m * u ≤ D := by
  have hw := layerWeight_pos B m
  have hp := layerWeight_pos B (m - 1)
  have hu := (le_div_iff₀ hp).mp hkernel
  have hratioD := mul_le_mul_of_nonneg_right hratio hD
  have huW := mul_le_mul_of_nonneg_right hu hw.le
  have hcontract : layerWeight B m * u ≤ (1 - d / 2) * D := by
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith
  exact hcontract.trans (by nlinarith)

/-- Explicit conditional interfaces for E.7. The white predicate and depth
must eventually be instantiated from the primitive geometry. Short stopped
comparisons, their two contributions, and long stopped comparisons are open
producer obligations in addition to the exit, post-exit and tail estimates.
None of these fields assumes the final layer bound or labels a stopping
comparison as a geometric property. -/
structure LayerEstimates {P : ℕ} (V : ℕ → Fin (P + 1) → ℝ)
    (white : ℕ → Fin (P + 1) → Prop) (depth : ℕ → Fin (P + 1) → ℕ)
    (B M N : ℕ) (d η : ℝ) : Prop where
  /-- One-step kernel estimate under control of all later states. -/
  white_kernel : ∀ m, M ≤ m → m ≤ N → ∀ D : ℝ, 1 ≤ D →
    (∀ r, r < m → ∀ l, layerWeight B r * V r l ≤ D) →
    ∀ l, white m l → V m l ≤ (1 - d) * D / layerWeight B (m - 1)
  /-- Short exits include depth zero; p and both contributions share one law. -/
  short_exit : ∀ m, M ≤ m → m ≤ N → ∀ D : ℝ, 1 ≤ D →
    (∀ r, r < m → ∀ l, layerWeight B r * V r l ≤ D) →
    ∀ l, ¬ white m l → (depth m l : ℝ) ≤ η * m →
    ∃ p cw cb : ℝ, 15 / 16 ≤ p ∧ p ≤ 1 ∧
      layerWeight B m * V m l ≤ (1 + d / 8) * (cw + cb) ∧
      cw ≤ D * (1 - d / 2) * p ∧ cb ≤ D * (1 - p)
  /-- Long exits keep the expectation and terminal probability separate. -/
  long_exit : ∀ m, M ≤ m → m ≤ N → ∀ D : ℝ, 1 ≤ D →
    (∀ r, r < m → ∀ l, layerWeight B r * V r l ≤ D) →
    ∀ l, ¬ white m l → η * m < (depth m l : ℝ) →
    ∃ e t : ℝ, 0 ≤ e ∧ 0 ≤ t ∧
      layerWeight B m * V m l ≤ D * (10 : ℝ) ^ B * e + layerWeight B m * t ∧
      e ≤ 1 / (4 * (10 : ℝ) ^ B) ∧ t ≤ Real.exp (-(m : ℝ) / 640)

/-- Eliminate all three local cases against the preceding finite maximum. -/
theorem LayerEstimates.new_layer_le {P B M N : ℕ}
    {V : ℕ → Fin (P + 1) → ℝ} {white : ℕ → Fin (P + 1) → Prop}
    {depth : ℕ → Fin (P + 1) → ℕ} {d η : ℝ}
    (h : LayerEstimates V white depth B M N d η)
    (hzero : ∀ l, V 0 l = 1) (hd : 0 ≤ d)
    (hratio : ∀ m, M ≤ m → m ≤ N → (1 - d) * layerWeight B m ≤
      (1 - d / 2) * layerWeight B (m - 1))
    (hlarge : ∀ m, M ≤ m → m ≤ N → (2560 * ((B : ℝ) + 1)) ^ 2 ≤ (m : ℝ))
    (m : ℕ) (hm : M ≤ m) (hmN : m ≤ N) (l : Fin (P + 1)) :
    layerWeight B m * V m l ≤ layerMaximum V B (m - 1) := by
  classical
  let D := layerMaximum V B (m - 1)
  have hD : 1 ≤ D := one_le_layerMaximum V hzero
  have hlater : ∀ r, r < m → ∀ k, layerWeight B r * V r k ≤ D := by
    intro r hr k
    exact weighted_le_layerMaximum V (by omega) k
  by_cases hw : white m l
  · exact whiteLayer_comparison (by linarith) hd
      (h.white_kernel m hm hmN D hD hlater l hw) (hratio m hm hmN)
  · by_cases hs : (depth m l : ℝ) ≤ η * m
    · obtain ⟨p, cw, cb, hp, _, hstop, hcw, hcb⟩ :=
        h.short_exit m hm hmN D hD hlater l hw hs
      exact shortExit_comparison (by linarith) hd hp hstop hcw hcb
    · obtain ⟨e, t, _, _, hstop, hpost, htail⟩ :=
        h.long_exit m hm hmN D hD hlater l hw (lt_of_not_ge hs)
      apply longExit_comparison hD hstop hpost
      exact (mul_le_mul_of_nonneg_left htail (layerWeight_pos B m).le).trans
        (terminalPayment_le_quarter (hlarge m hm hmN))

/-- Once each new layer is controlled by the preceding maximum, all layers
are bounded by the startup cost. This is an induction engine, not a source of
the local crossing estimates. -/
theorem layerMaximum_le_startup {P B M N : ℕ}
    (V : ℕ → Fin (P + 1) → ℝ) (hM : 0 < M)
    (hV : ∀ r, r ≤ N → ∀ l, V r l ≤ 1)
    (hstep : ∀ m, M ≤ m → m ≤ N → ∀ l,
      layerWeight B m * V m l ≤ layerMaximum V B (m - 1)) :
    layerMaximum V B N ≤ (M : ℝ) ^ B := by
  have hall : ∀ m, m ≤ N → layerMaximum V B m ≤ (M : ℝ) ^ B := by
    intro m
    induction m with
    | zero =>
        intro _
        exact layerMaximum_base V hM hM (fun r hr l => hV r (by omega) l)
    | succ m ih =>
        intro hmN
        by_cases hsmall : m + 1 < M
        · exact layerMaximum_base V hM hsmall (fun r hr l => hV r (by omega) l)
        · have heq := layerMaximum_succ_eq (B := B) V
            (fun l => by simpa using hstep (m + 1) (by omega) hmN l)
          rw [heq]
          exact ih (by omega)
  exact hall N le_rfl

/-- The startup bound expressed in the potential's original units. -/
theorem potential_le_startup {P B M N : ℕ}
    (V : ℕ → Fin (P + 1) → ℝ) (hM : 0 < M)
    (hV : ∀ r, r ≤ N → ∀ l, V r l ≤ 1)
    (hstep : ∀ m, M ≤ m → m ≤ N → ∀ l,
      layerWeight B m * V m l ≤ layerMaximum V B (m - 1))
    (l : Fin (P + 1)) : V N l ≤ (M : ℝ) ^ B / layerWeight B N := by
  apply (le_div_iff₀ (layerWeight_pos B N)).mpr
  rw [mul_comm]
  exact (weighted_le_layerMaximum V le_rfl l).trans
    (layerMaximum_le_startup V hM hV hstep)

/-- Conditional E.7 conclusion, with every local estimate and scalar guard
visible. Instantiating this theorem with the original potential remains a
separate producer and source-matching obligation. -/
theorem LayerEstimates.potential_le {P B M N : ℕ}
    {V : ℕ → Fin (P + 1) → ℝ} {white : ℕ → Fin (P + 1) → Prop}
    {depth : ℕ → Fin (P + 1) → ℕ} {d η : ℝ}
    (h : LayerEstimates V white depth B M N d η)
    (hM : 0 < M) (hzero : ∀ l, V 0 l = 1)
    (hV : ∀ r, r ≤ N → ∀ l, V r l ≤ 1) (hd : 0 ≤ d)
    (hratio : ∀ m, M ≤ m → m ≤ N → (1 - d) * layerWeight B m ≤
      (1 - d / 2) * layerWeight B (m - 1))
    (hlarge : ∀ m, M ≤ m → m ≤ N → (2560 * ((B : ℝ) + 1)) ^ 2 ≤ (m : ℝ))
    (l : Fin (P + 1)) :
    V N l ≤ (M : ℝ) ^ B / layerWeight B N := by
  exact potential_le_startup V hM hV (h.new_layer_le hzero hd hratio hlarge) l

/-- The conditional bound transported back to every integer height. U is
indexed by remaining distance, so U N 0 is the initial state of the horizon. -/
theorem LayerEstimates.integer_potential_le {P B M N : ℕ}
    {U : ℕ → ℤ → ℝ} {white : ℕ → Fin (P + 1) → Prop}
    {depth : ℕ → Fin (P + 1) → ℕ} {d η : ℝ}
    (h : LayerEstimates (residuePotential P U) white depth B M N d η)
    (hperiod : ∀ r, Function.Periodic (U r) (P + 1 : ℕ))
    (hM : 0 < M) (hzero : ∀ l, U 0 l = 1)
    (hU : ∀ r, r ≤ N → ∀ l, U r l ≤ 1) (hd : 0 ≤ d)
    (hratio : ∀ m, M ≤ m → m ≤ N → (1 - d) * layerWeight B m ≤
      (1 - d / 2) * layerWeight B (m - 1))
    (hlarge : ∀ m, M ≤ m → m ≤ N → (2560 * ((B : ℝ) + 1)) ^ 2 ≤ (m : ℝ))
    (l : ℤ) : U N l ≤ (M : ℝ) ^ B / layerWeight B N := by
  rw [← residuePotential_eq U hperiod N l]
  exact h.potential_le hM (fun k => hzero k) (fun r hr k => hU r hr k)
    hd hratio hlarge (layerHeightResidue P l)

end WordCertDensity.LocalPrimitive
