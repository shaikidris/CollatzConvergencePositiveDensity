/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The independent-list recursion and atom/moment induction follow the local
Reference.Words and Reference.WordMoment modules, adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The source LICENSE and
NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
This construction samples complete stopped blocks under their original law.
-/
module

public import WordCertDensity.Construction.StoppedCenteredMoment
public import WordCertDensity.Probability.ExponentialMarkov
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Independent copies of the actual stopped block

The finite list law samples the normalized original stopped PMF independently.
Its support fixes both the number of blocks and every block's first-crossing
property. Nonnegative moments factor before any finiteness restriction.
-/

@[expose] public section

namespace WordCertDensity.Construction

open scoped Classical ENNReal

/-- Independent complete stopped blocks, with no finite-precision conditioning. -/
noncomputable def stoppedCopiesPMF : ℕ → PMF (List ValuationWord)
  | 0 => PMF.pure []
  | n + 1 => stoppedPMF.bind (fun w => (stoppedCopiesPMF n).map (fun ws => w :: ws))

/-- Zero stopped copies give the empty list with unit mass. -/
theorem stoppedCopiesPMF_zero : stoppedCopiesPMF 0 = PMF.pure [] := rfl

/-- Each nonempty list atom is the product of its first block and independent remainder. -/
theorem stoppedCopiesPMF_cons (n : ℕ) (w : ValuationWord) (ws : List ValuationWord) :
    stoppedCopiesPMF (n + 1) (w :: ws) = stoppedPMF w * stoppedCopiesPMF n ws := by
  rw [stoppedCopiesPMF, PMF.bind_apply]
  have hmap (v : ValuationWord) :
      ((stoppedCopiesPMF n).map (fun vs => v :: vs)) (w :: ws) =
        if w = v then stoppedCopiesPMF n ws else 0 := by
    rw [PMF.map_apply]
    by_cases h : w = v
    · subst v
      rw [tsum_eq_single ws]
      · simp
      · intro vs hvs
        have hne : ¬ w :: ws = w :: vs := fun he => hvs (List.cons.inj he).2.symm
        simp [hne]
    · have hne (vs : List ValuationWord) : ¬ w :: ws = v :: vs :=
        fun he => h (List.cons.inj he).1
      simp [h, hne]
  simp_rw [hmap]
  rw [tsum_eq_single w]
  · simp
  · intro v hv
    simp [hv.symm]

/-- A positive number of copies cannot produce an empty list. -/
theorem stoppedCopiesPMF_succ_nil (n : ℕ) : stoppedCopiesPMF (n + 1) [] = 0 := by
  rw [stoppedCopiesPMF, PMF.bind_apply]
  simp [PMF.map_apply]

/-- The exact support fixes the copy count and requires a genuine first crossing in every block. -/
theorem stoppedCopiesPMF_mem_support_iff (n : ℕ) (ws : List ValuationWord) :
    ws ∈ (stoppedCopiesPMF n).support ↔
      ws.length = n ∧ ∀ w ∈ ws, FirstCrossing w := by
  induction n generalizing ws with
  | zero => cases ws <;> simp [stoppedCopiesPMF]
  | succ n ih =>
      cases ws with
      | nil => simp [PMF.mem_support_iff, stoppedCopiesPMF_succ_nil]
      | cons w ws =>
          rw [PMF.mem_support_iff, stoppedCopiesPMF_cons, mul_ne_zero_iff,
            ← PMF.mem_support_iff stoppedPMF w, stoppedPMF_mem_support_iff,
            ← PMF.mem_support_iff (stoppedCopiesPMF n) ws, ih]
          simp [and_left_comm]

/-- Sum an observable over the finite list of complete blocks. -/
def blockSum (F : ValuationWord → ℝ) (ws : List ValuationWord) : ℝ := (ws.map F).sum

/-- The empty block list contributes zero. -/
@[simp] theorem blockSum_nil (F : ValuationWord → ℝ) : blockSum F [] = 0 := rfl

/-- Adding a block adds its observable value. -/
@[simp] theorem blockSum_cons (F : ValuationWord → ℝ) (w : ValuationWord)
    (ws : List ValuationWord) : blockSum F (w :: ws) = F w + blockSum F ws := rfl

/-- Finite centering subtracts exactly one full-law mean per block. -/
theorem blockSum_centered (F : ValuationWord → ℝ) (ws : List ValuationWord) :
    blockSum (stoppedCentered F) ws =
      blockSum F ws - (ws.length : ℝ) * stoppedExpectation F := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      simp only [blockSum_cons, stoppedCentered, ih, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      ring

private theorem exp_blockSum_cons (F : ValuationWord → ℝ) (t : ℝ)
    (w : ValuationWord) (ws : List ValuationWord) :
    ENNReal.ofReal (Real.exp (t * blockSum F (w :: ws))) =
      ENNReal.ofReal (Real.exp (t * F w)) *
        ENNReal.ofReal (Real.exp (t * blockSum F ws)) := by
  rw [blockSum_cons, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- Independent stopped-copy exponential moments are exact powers before finiteness is known. -/
theorem stoppedCopies_expMoment (n : ℕ) (F : ValuationWord → ℝ) (t : ℝ) :
    (∑' ws, stoppedCopiesPMF n ws * ENNReal.ofReal (Real.exp (t * blockSum F ws))) =
      (∑' w, stoppedPMF w * ENNReal.ofReal (Real.exp (t * F w))) ^ n := by
  induction n with
  | zero => simp [stoppedCopiesPMF, PMF.pure_apply]
  | succ n ih =>
      rw [stoppedCopiesPMF, PMFMoment.sum_bind]
      simp_rw [PMFMoment.sum_map, exp_blockSum_cons]
      have hin (w : ValuationWord) :
          (∑' ws, stoppedCopiesPMF n ws *
            (ENNReal.ofReal (Real.exp (t * F w)) *
              ENNReal.ofReal (Real.exp (t * blockSum F ws)))) =
          ENNReal.ofReal (Real.exp (t * F w)) *
            (∑' v, stoppedPMF v * ENNReal.ofReal (Real.exp (t * F v))) ^ n := by
        calc
          _ = ENNReal.ofReal (Real.exp (t * F w)) *
              ∑' ws, stoppedCopiesPMF n ws *
                ENNReal.ofReal (Real.exp (t * blockSum F ws)) := by
            rw [← ENNReal.tsum_mul_left]
            apply tsum_congr
            intro ws
            ac_rfl
          _ = _ := by rw [ih]
      simp_rw [hin, ← mul_assoc]
      rw [ENNReal.tsum_mul_right, pow_succ']

/-- The actual centered sum has the quadratic moment bound for either parameter sign. -/
theorem stoppedCopies_centered_expMoment_le (n : ℕ) {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) {t : ℝ} (ht : |t| ≤ 1 / 8000) :
    (∑' ws, stoppedCopiesPMF n ws * ENNReal.ofReal
      (Real.exp (t * blockSum (stoppedCentered F) ws))) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * (stoppedQuadraticBound * t ^ 2))) := by
  rw [stoppedCopies_expMoment]
  have h := pow_le_pow_left' (stopped_centered_exp_ennreal_le hF ht) n
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul] at h
  exact h

end WordCertDensity.Construction
