/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalShell

/-! # Least binary shift into the terminal shell

The lower cutoff endpoint is strict. The selected shift is therefore positive,
and minimality gives a strict upper edge below twice the cutoff.
-/

namespace WordCertDensity.Construction

/-- Least permitted shift whose lower shell edge reaches the cutoff, or zero off its domain. -/
noncomputable def terminalSelector (b : ℕ) (y X : ℝ) : ℕ := by
  classical
  exact if h : ∃ u : ℕ, u ≤ 2 * terminalRadius b ∧ X ≤ 2 ^ u * terminalShellLow b y then
    Nat.find h else 0

/-- The selector has the exact positive shift, endpoint and minimality conventions. -/
theorem terminalSelector_spec (b : ℕ) (y X : ℝ)
    (hlo : terminalShellLow b y < X)
    (hhi : X ≤ 2 ^ (2 * terminalRadius b) * terminalShellLow b y) :
    1 ≤ terminalSelector b y X ∧ terminalSelector b y X ≤ 2 * terminalRadius b ∧
      X ≤ 2 ^ terminalSelector b y X * terminalShellLow b y ∧
      2 ^ terminalSelector b y X * terminalShellLow b y < 2 * X ∧
      ∀ v < terminalSelector b y X, 2 ^ v * terminalShellLow b y < X := by
  classical
  have hex : ∃ u : ℕ, u ≤ 2 * terminalRadius b ∧ X ≤ 2 ^ u * terminalShellLow b y :=
    ⟨2 * terminalRadius b, le_refl _, hhi⟩
  have hs := Nat.find_spec hex
  have hu : 1 ≤ Nat.find hex := by
    by_contra h
    have hz : Nat.find hex = 0 := by omega
    rw [hz, pow_zero, one_mul] at hs
    exact (not_le_of_gt hlo) hs.2
  have hmin : ∀ v < Nat.find hex, 2 ^ v * terminalShellLow b y < X := by
    intro v hv
    apply lt_of_not_ge
    intro he
    exact Nat.find_min hex hv ⟨by omega, he⟩
  have hprev := hmin (Nat.find hex - 1) (by omega)
  have hp : (2 : ℝ) ^ Nat.find hex * terminalShellLow b y =
      2 * (2 ^ (Nat.find hex - 1) * terminalShellLow b y) := by
    conv_lhs => rw [show Nat.find hex = (Nat.find hex - 1) + 1 by omega, pow_succ]
    ring
  unfold terminalSelector
  rw [dif_pos hex]
  refine ⟨hu, hs.1, hs.2, ?_, hmin⟩
  rw [hp]
  exact mul_lt_mul_of_pos_left hprev (by norm_num)

/-- The selected reduced physical source lies between X and the strict finite-radius upper edge. -/
theorem terminalPhysical_selected {b y x : ℕ} (hb : 0 < b) {X : ℝ}
    (hy : 16 ^ b ≤ y) (hlo : terminalShellLow b y < X)
    (hhi : X ≤ 2 ^ (2 * terminalRadius b) * terminalShellLow b y)
    {w : ValuationWord} (hw : TerminalWord b (terminalSelector b y X) 1 w)
    (hp : PhysicalHistory w y x) :
    X ≤ (x : ℝ) ∧ (x : ℝ) < terminalShellRadius b * X := by
  have hs := terminalSelector_spec b y X hlo hhi
  have hx := terminalPhysical_shell hb hw hy hp
  have hc : (0 : ℝ) < 8 / (1 - terminalEta b) :=
    div_pos (by norm_num) (sub_pos.mpr (terminalEta_bounds hb).2)
  refine ⟨hs.2.2.1.trans hx.1, ?_⟩
  calc
    (x : ℝ) ≤ _ := hx.2
    _ < 8 / (1 - terminalEta b) * (2 * X) :=
      mul_lt_mul_of_pos_left hs.2.2.2.1 hc
    _ = terminalShellRadius b * X := by unfold terminalShellRadius; ring

end WordCertDensity.Construction
