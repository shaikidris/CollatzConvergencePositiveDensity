/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalOvershoot
import WordCertDensity.Transfer.Stopped

/-! # The two-marker terminal transfer estimate

The ambient level is the upper terminal depth plus the child marker level.
Both coarse replacements and the original unnormalized terminal deficit
remain in the error; the same estimate holds at every permitted shift.
-/

namespace WordCertDensity.Construction

/-- Ambient conductor for an original terminal word and its child marker. -/
def terminalConductor (b k : ℕ) : ℕ := terminalHigh b + k

/-- Every original terminal word fits with its full child-marker precision. -/
theorem terminalConductor_word_guards {b u K : ℕ} (k : ℕ) {w : ValuationWord}
    (hw : w ∈ terminalWords b u K) :
    w.length ≤ terminalConductor b k ∧ k ≤ terminalConductor b k - w.length := by
  have := terminalWords_depth hw
  unfold terminalConductor
  omega

/-- The old marker also projects from the same ambient conductor. -/
theorem terminalConductor_marker (b k : ℕ) : k ≤ terminalConductor b k := by
  unfold terminalConductor
  omega

/-- Original terminal transfer with the full remaining child precision. -/
noncomputable def terminalCoarse (b u K k : ℕ) : ZMod (3^terminalConductor b k) → ℝ :=
  Transfer.coarseSelected (terminalWords b u K) (terminalConductor b k) k
    (fun _ hw => (terminalConductor_word_guards k hw).2)

/-- The signed discrepancy compares the actual old and new marker levels. -/
noncomputable def terminalVariationTest (b u K k : ℕ)
    (a : ZMod (3^terminalConductor b k)) : ℝ :=
  terminalCoarse b u K k a - Reference.marker k
    (Reference.project (terminalConductor_marker b k) a)

/-- Uniform finite reference cost, retaining both copies of the mixing error. -/
noncomputable def terminalTransferError (b K k : ℕ) : ℝ :=
  2 * Analytic.mixingError k + 2 * Real.exp (-(b : ℝ)/64000) + (1/2 : ℝ)^(K+1)

/-- Every permitted shift pays its own original terminal deficit. -/
theorem terminalVariationTest_mean {b u k : ℕ} (hb : 200 ≤ b)
    (hu : u ≤ 2 * terminalRadius b) (hk : 1 ≤ k) (K : ℕ) :
    Reference.mean (terminalConductor b k) (fun a => |terminalVariationTest b u K k a|) ≤
      (2/3 : ℝ) * terminalTransferError b K k := by
  have h := Transfer.stopped_transfer_le (terminalWords b u K)
    (fun _ hw => (terminalConductor_word_guards k hw).1)
    (fun _ hw => (terminalConductor_word_guards k hw).2)
    hk hk (terminalConductor_marker b k) (terminalWords_prefixFree b u K)
  have hd := terminalMass_deficit hb hu K
  change Reference.mean (terminalConductor b k)
    (fun a => |terminalVariationTest b u K k a|) ≤
      (2/3 : ℝ) * (Analytic.mixingError k + Analytic.mixingError k +
        1 - terminalMass b u K) at h
  unfold terminalTransferError
  linarith

/-- The terminal error is nonnegative on every positive marker level. -/
theorem terminalTransferError_nonneg (b K : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ terminalTransferError b K k := by
  have := (Analytic.mixingError_pos hk).le
  unfold terminalTransferError
  positivity

/-- Sixth-order mixing suffices for the same finite terminal error. -/
theorem terminalTransferError_order6 (b K : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    terminalTransferError b K k ≤
      2 * (Analytic.mixingCoefficient : ℝ)/(k : ℝ)^6 +
        2 * Real.exp (-(b : ℝ)/64000) + (1/2 : ℝ)^(K+1) := by
  have h : Analytic.mixingError k ≤ (Analytic.mixingCoefficient : ℝ)/(k : ℝ)^6 := by
    simpa only [Real.rpow_neg (Nat.cast_nonneg k), Real.rpow_natCast, Real.rpow_ofNat,
      div_eq_mul_inv] using Analytic.mixingError_le_order6 hk
  unfold terminalTransferError
  calc
    _ ≤ 2 * ((Analytic.mixingCoefficient : ℝ)/(k : ℝ)^6) +
        2 * Real.exp (-(b : ℝ)/64000) + (1/2 : ℝ)^(K+1) := by linarith
    _ = _ := by ring

end WordCertDensity.Construction
