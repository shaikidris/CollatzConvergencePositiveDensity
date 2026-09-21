/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryGeometry
public import WordCertDensity.Analytic.LocalPrimitive.LayerBridge
public import WordCertDensity.Analytic.LocalPrimitive.ShortExitBound
public import WordCertDensity.Analytic.LocalPrimitive.LongExitAssembly

/-! # Concrete selected-triangle data for the layer assembly -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- A periodic predicate is recovered from the canonical finite height
representative used by the layer maximum. -/
theorem periodic_at_layerHeightResidue {P : ℕ} {α : Type*} (f : ℤ → α)
    (hperiod : Function.Periodic f (P + 1 : ℕ)) (l : ℤ) :
    f (layerHeightResidue P l) = f l := by
  have hpos : (0 : ℤ) < (P + 1 : ℕ) := by omega
  have hnonneg := Int.emod_nonneg l (ne_of_gt hpos)
  change f (Int.toNat (l % (P + 1 : ℕ))) = f l
  rw [Int.toNat_of_nonneg hnonneg, Int.emod_def]
  simpa [mul_comm] using (hperiod.sub_int_mul_eq (l / (P + 1 : ℕ)) (x := l))

/-- The finite representative is white exactly when its literal phase state
is white at the corresponding pair column. -/
def phaseLayerWhite {P : ℕ} (n : ℕ) (ξ : ZMod (3 ^ n)) (N m : ℕ)
    (a : Fin (P + 1)) : Prop :=
  phaseWhiteAtInt n ξ (N - m) (a : ℤ)

/-- The depth of a black representative is taken from a selected triangle
through that point. It is zero when no such triangle exists; the range lemmas
below prove existence before this fallback is ever used by the layer engine. -/
noncomputable def phaseLayerDepth {P : ℕ} (n : ℕ) (ξ : ZMod (3 ^ n)) (N m : ℕ)
    (a : Fin (P + 1)) : ℕ := by
  classical
  exact if h : ∃ p : ℕ × ℤ, isSelectedPhaseTriangle n ξ p.1 p.2 ∧
      inPhaseTriangleIntMul n ξ p.1 p.2 (N - m) (a : ℤ) then
    ((Classical.choose h).2 - (a : ℤ)).toNat
  else 0

/-- A nonwhite representative in the nonterminal layer range has a concrete
selected triangle, and `phaseLayerDepth` records exactly its vertical depth. -/
theorem phaseLayerDepth_selected {P n N m : ℕ} (ξ : ZMod (3 ^ n))
    (a : Fin (P + 1)) (hn : 0 < n) (hm : 0 < m) (hmN : m ≤ N)
    (hN : N = n / 2) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hblack : ¬ phaseLayerWhite (P := P) n ξ N m a) :
    ∃ topWidth top, isSelectedPhaseTriangle n ξ topWidth top ∧
      inPhaseTriangleIntMul n ξ topWidth top (N - m) (a : ℤ) ∧
      phaseLayerDepth (P := P) n ξ N m a = (top - (a : ℤ)).toNat := by
  have hj : 2 * (N - m) < n := by omega
  have hb : phaseBlackAtInt n ξ (N - m) (a : ℤ) := by
    simpa only [phaseLayerWhite, phaseWhiteAtInt, not_not] using hblack
  obtain ⟨width, top, hsel, hstart⟩ :=
    black_point_has_selected_triangle hn hj ξ hξ hb
  let h : ∃ p : ℕ × ℤ, isSelectedPhaseTriangle n ξ p.1 p.2 ∧
      inPhaseTriangleIntMul n ξ p.1 p.2 (N - m) (a : ℤ) :=
    ⟨(width, top), hsel, hstart⟩
  let p := Classical.choose h
  have hp : isSelectedPhaseTriangle n ξ p.1 p.2 ∧
      inPhaseTriangleIntMul n ξ p.1 p.2 (N - m) (a : ℤ) := Classical.choose_spec h
  refine ⟨p.1, p.2, hp.1, hp.2, ?_⟩
  rw [phaseLayerDepth, dif_pos h]

/-- The literal white-kernel estimate transported to the concrete finite
white datum. This is the white field required by `LayerEstimates`; the two
black fields are assembled separately from the selected-triangle witness. -/
theorem phaseLayerWhite_weighted_le {P B n N M m : ℕ} (ξ : ZMod (3 ^ n))
    (hpotentialPeriod : ∀ r, Function.Periodic
      (phaseRemainingPotential n ξ N r) (P + 1 : ℕ))
    (hwhitePeriod : ∀ j, Function.Periodic (phaseWhiteAtInt n ξ j) (P + 1 : ℕ))
    (hMpos : 0 < M) (hMm : M ≤ m) (hmN : m ≤ N) (D : ℝ)
    (hfuture : ∀ r, r < m → ∀ a,
      layerWeight B r * residuePotential P (phaseRemainingPotential n ξ N) r a ≤ D) :
    ∀ a, phaseLayerWhite (P := P) n ξ N m a →
      residuePotential P (phaseRemainingPotential n ξ N) m a ≤
        (1 - pairLoss localEpsilon) * D / layerWeight B (m - 1) := by
  apply phaseRemainingPotential_residue_white_weighted_le ξ hpotentialPeriod
    (phaseLayerWhite (P := P) n ξ N)
  · intro l hl
    unfold phaseLayerWhite at hl
    rw [← periodic_at_layerHeightResidue
      (phaseWhiteAtInt n ξ (N - m)) (hwhitePeriod (N - m)) l]
    exact hl
  · exact lt_of_lt_of_le hMpos hMm
  · exact hmN
  · exact hfuture

/-- The original-law short-exit comparison transported from a concrete finite
black representative. The depth hypothesis is stated with the literal recipe
denominator, so the layer-instance specialization can set `eta = 1 / denom`. -/
theorem phaseLayerShort_exit {P B n M m : ℕ} (ξ : ZMod (3 ^ n))
    (a : Fin (P + 1)) (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hB : 0 < B) (hMpos : 0 < M) (hMm : M ≤ m) (hmN : m ≤ n / 2)
    (hmRecipe : localPrimitiveM B ≤ m)
    (hpotentialPeriod : ∀ r, Function.Periodic
      (phaseRemainingPotential n ξ (n / 2) r) (P + 1 : ℕ))
    (hblack : ¬ phaseLayerWhite (P := P) n ξ (n / 2) m a)
    (hshort : (phaseLayerDepth (P := P) n ξ (n / 2) m a : ℝ) ≤
      (m : ℝ) / (localPrimitiveEtaDenom B : ℝ))
    (D : ℝ) (hD : 1 ≤ D)
    (hfuture : ∀ r, r < m → ∀ b,
      layerWeight B r * residuePotential P
        (phaseRemainingPotential n ξ (n / 2)) r b ≤ D) :
    ∃ p cw cb : ℝ, 15 / 16 ≤ p ∧ p ≤ 1 ∧
      layerWeight B m * residuePotential P
          (phaseRemainingPotential n ξ (n / 2)) m a ≤
        (1 + pairLoss localEpsilon / 8) * (cw + cb) ∧
      cw ≤ D * (1 - pairLoss localEpsilon / 2) * p ∧ cb ≤ D * (1 - p) := by
  obtain ⟨width, top, hsel, hstart, hdepth⟩ :=
    phaseLayerDepth_selected ξ a hn (lt_of_lt_of_le hMpos hMm) hmN rfl hξ hblack
  have hwidth : 2 * width < n := by
    have hleft := hstart.1
    omega
  have hfutureInt : ∀ r, r < m → ∀ l',
      layerWeight B r * phaseRemainingPotential n ξ (n / 2) r l' ≤ D := by
    intro r hr l'
    rw [← residuePotential_eq (phaseRemainingPotential n ξ (n / 2)) hpotentialPeriod r l']
    exact hfuture r hr _
  have hshort' : ((top - (a : ℤ)).toNat : ℝ) ≤
      (m : ℝ) / (localPrimitiveEtaDenom B : ℝ) := by
    simpa only [hdepth] using hshort
  obtain ⟨p, cw, cb, hp, hp1, hmain, hcw, hcb⟩ :=
    selected_triangle_short_exit_estimate hn hwidth ξ hξ top (a : ℤ) hsel hstart
      rfl hmN B hB hmRecipe hshort' D hD hfutureInt
  exact ⟨p, cw, cb, hp, hp1, hmain, hcw, hcb⟩

/-- The original-law long-exit comparison transported from a concrete finite
black representative. The fixed cutoff horizon is explicit because it is used
by the neutral post-terminal extension in the passage proof. -/
theorem phaseLayerLong_exit {P B n M m L : ℕ} (ξ : ZMod (3 ^ n))
    (a : Fin (P + 1)) (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hB : 0 < B) (hMpos : 0 < M) (hMm : M ≤ m) (hmN : m ≤ n / 2)
    (hmRecipe : localPrimitiveM B ≤ m) (hmL : m ≤ L)
    (hpotentialPeriod : ∀ r, Function.Periodic
      (phaseRemainingPotential n ξ (n / 2) r) (P + 1 : ℕ))
    (hblack : ¬ phaseLayerWhite (P := P) n ξ (n / 2) m a)
    (hlong : (m : ℝ) / (localPrimitiveEtaDenom B : ℝ) <
      (phaseLayerDepth (P := P) n ξ (n / 2) m a : ℝ))
    (hL : phaseLayerDepth (P := P) n ξ (n / 2) m a / 2 + 1 +
      localPrimitiveP B ≤ L)
    (D : ℝ) (hfuture : ∀ r, r < m → ∀ b,
      layerWeight B r * residuePotential P
        (phaseRemainingPotential n ξ (n / 2)) r b ≤ D) :
    ∃ e t : ℝ, 0 ≤ e ∧ 0 ≤ t ∧
      layerWeight B m * residuePotential P
          (phaseRemainingPotential n ξ (n / 2)) m a ≤
        D * (10 : ℝ) ^ B * e + layerWeight B m * t ∧
      e ≤ 1 / (4 * (10 : ℝ) ^ B) ∧ t ≤ Real.exp (-(m : ℝ) / 640) := by
  obtain ⟨width, top, hsel, hstart, hdepth⟩ :=
    phaseLayerDepth_selected ξ a hn (lt_of_lt_of_le hMpos hMm) hmN rfl hξ hblack
  have hwidth : 2 * width < n := by
    have hleft := hstart.1
    omega
  have hfutureInt : ∀ r, r < m → ∀ l',
      layerWeight B r * phaseRemainingPotential n ξ (n / 2) r l' ≤ D := by
    intro r hr l'
    rw [← residuePotential_eq (phaseRemainingPotential n ξ (n / 2)) hpotentialPeriod r l']
    exact hfuture r hr _
  have hlong' : (m : ℝ) / (localPrimitiveEtaDenom B : ℝ) <
      ((top - (a : ℤ)).toNat : ℝ) := by simpa only [hdepth] using hlong
  have hL' : (top - (a : ℤ)).toNat / 2 + 1 + localPrimitiveP B ≤ L := by
    simpa only [hdepth] using hL
  have hmcol : n / 2 - (n / 2 - m) = m := by omega
  have hfuture' : ∀ r, r < n / 2 - (n / 2 - m) → ∀ l',
      layerWeight B r * phaseRemainingPotential n ξ (n / 2) r l' ≤ D := by
    simpa only [hmcol] using hfutureInt
  obtain ⟨e, t, he, ht, hmain, hecap, htcap⟩ :=
    selected_triangle_long_exit_estimate ξ top (a : ℤ) B L D hn hwidth hξ hsel hstart hB
      (by omega) (by simpa only [hmcol] using hmRecipe)
      (by simpa only [hmcol] using hmL) (by simpa only [hmcol] using hlong') hL' hfuture'
  refine ⟨e, t, he, ht, ?_, hecap, ?_⟩
  · simpa only [residuePotential, hmcol] using hmain
  · simpa only [hmcol] using htcap

/-- The three original-law local comparisons assembled into the conditional
E.7 layer interface. The long branch chooses the smallest horizon meeting both
the neutral-cutoff and post-passage-window requirements. -/
theorem phaseLayerEstimates {P B n M : ℕ} (ξ : ZMod (3 ^ n))
    (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (hB : 0 < B)
    (hMpos : 0 < M) (hRecipe : localPrimitiveM B ≤ M)
    (hpotentialPeriod : ∀ r, Function.Periodic
      (phaseRemainingPotential n ξ (n / 2) r) (P + 1 : ℕ))
    (hwhitePeriod : ∀ j, Function.Periodic (phaseWhiteAtInt n ξ j) (P + 1 : ℕ)) :
    LayerEstimates (residuePotential P (phaseRemainingPotential n ξ (n / 2)))
      (phaseLayerWhite (P := P) n ξ (n / 2))
      (phaseLayerDepth (P := P) n ξ (n / 2)) B M (n / 2)
      (pairLoss localEpsilon) (1 / (localPrimitiveEtaDenom B : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm hmN D _ hfuture a ha
    simpa only using phaseLayerWhite_weighted_le ξ hpotentialPeriod hwhitePeriod
      hMpos hm hmN D hfuture a ha
  · intro m hm hmN D hD hfuture a hblack hshort
    have hmRecipe : localPrimitiveM B ≤ m := hRecipe.trans hm
    have hshort' : (phaseLayerDepth (P := P) n ξ (n / 2) m a : ℝ) ≤
        (m : ℝ) / (localPrimitiveEtaDenom B : ℝ) := by
      simpa only [one_div, one_mul, div_eq_mul_inv, mul_comm] using hshort
    exact phaseLayerShort_exit ξ a hn hξ hB hMpos hm hmN hmRecipe
      hpotentialPeriod hblack hshort' D hD hfuture
  · intro m hm hmN D _ hfuture a hblack hlong
    have hmRecipe : localPrimitiveM B ≤ m := hRecipe.trans hm
    have hlong' : (m : ℝ) / (localPrimitiveEtaDenom B : ℝ) <
        (phaseLayerDepth (P := P) n ξ (n / 2) m a : ℝ) := by
      simpa only [one_div, one_mul, div_eq_mul_inv, mul_comm] using hlong
    let L := max m (phaseLayerDepth (P := P) n ξ (n / 2) m a / 2 + 1 + localPrimitiveP B)
    exact phaseLayerLong_exit ξ a hn hξ hB hMpos hm hmN hmRecipe
      (le_max_left _ _) hpotentialPeriod hblack hlong'
      (by exact le_max_right _ _) D hfuture

/-- The concrete finite-layer induction for the original integer-height phase
potential. The input period may be any positive finite period carrying both
the potential and white-predicate periodicity witnesses. -/
theorem phaseRemainingPotential_layer_le {P B n M : ℕ} (ξ : ZMod (3 ^ n))
    (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (hB : 0 < B)
    (hRecipe : localPrimitiveM B ≤ M)
    (hpotentialPeriod : ∀ r, Function.Periodic
      (phaseRemainingPotential n ξ (n / 2) r) (P + 1 : ℕ))
    (hwhitePeriod : ∀ j, Function.Periodic (phaseWhiteAtInt n ξ j) (P + 1 : ℕ))
    (l : ℤ) :
    phaseRemainingPotential n ξ (n / 2) (n / 2) l ≤
      (M : ℝ) ^ B / layerWeight B (n / 2) := by
  have hMpos : 0 < M := lt_of_lt_of_le (localPrimitiveM_pos B) hRecipe
  have hratio : ∀ m, M ≤ m → m ≤ n / 2 →
      (1 - pairLoss localEpsilon) * layerWeight B m ≤
        (1 - pairLoss localEpsilon / 2) * layerWeight B (m - 1) := by
    intro m hm _
    apply white_layer_weight_ratio B m
    · have hfloor := (localPrimitiveM_ge_floor B).trans hRecipe |>.trans hm
      omega
    · have hentropy := (localPrimitiveM_ge_entropy B).trans hRecipe |>.trans hm
      have hfactor : 8 * B * localPrimitiveDDenom ≤ 64 * B * localPrimitiveDDenom := by
        convert Nat.mul_le_mul_right (B * localPrimitiveDDenom) (by norm_num : 8 ≤ 64) using 1 <;>
          ring
      have hsmall : 8 * B * localPrimitiveDDenom ≤ m := hfactor.trans hentropy
      exact_mod_cast hsmall
  have hlarge : ∀ m, M ≤ m → m ≤ n / 2 →
      (2560 * ((B : ℝ) + 1)) ^ 2 ≤ (m : ℝ) := by
    intro m hm _
    have htail := (localPrimitiveM_ge_tail B).trans hRecipe |>.trans hm
    exact_mod_cast htail
  apply LayerEstimates.integer_potential_le
    (phaseLayerEstimates ξ hn hξ hB hMpos hRecipe hpotentialPeriod hwhitePeriod)
    hpotentialPeriod hMpos
  · intro l'
    exact phaseRemainingPotential_zero n (n / 2) ξ l'
  · intro r _ l'
    exact (phaseRemainingPotential_mem_unitInterval n (n / 2) r ξ l').2
  · exact (localPairLoss_mem_unitInterval).1
  · exact hratio
  · exact hlarge

/-- The finite layer induction at the literal Euler phase period. This is the
fully instantiated E-L5 local-potential conclusion; it does not assert the
separate all-level primitive-decay consumer. -/
theorem phaseRemainingPotential_layer_le_phasePeriod {B n M : ℕ}
    (ξ : ZMod (3 ^ n)) (hn : 0 < n) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (hB : 0 < B) (hRecipe : localPrimitiveM B ≤ M) (l : ℤ) :
    phaseRemainingPotential n ξ (n / 2) (n / 2) l ≤
      (M : ℝ) ^ B / layerWeight B (n / 2) := by
  let q := 2 * 3 ^ (n - 1)
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hindex : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  apply phaseRemainingPotential_layer_le (P := q - 1) ξ hn hξ hB hRecipe
  · intro r
    rw [hindex]
    exact phaseRemainingPotential_phasePeriod hn ξ (n / 2) r
  · intro j
    rw [hindex]
    exact phaseWhiteAtInt_periodic hn ξ j

end WordCertDensity.LocalPrimitive
