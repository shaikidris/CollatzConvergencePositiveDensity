/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Transfer.Affine
public import WordCertDensity.Reference.Stopping
import Mathlib.Tactic.Ring

/-!
# One original prefix and its affine marker transfer

Selection is under the original iid word PMF. The prefix probability is
paid once; the remaining tail keeps its unrestricted reference law.
-/

@[expose] public section

namespace WordCertDensity.Transfer

open scoped Classical ENNReal

private theorem prefix_append_iff (w u t : ValuationWord) (hu : u.length = w.length) :
    w <+: u ++ t ↔ u = w := by
  rw [List.prefix_iff_eq_take, ← hu, List.take_left]
  exact eq_comm

/-- A selected prefix atom is its original word probability times the affine tail atom. -/
theorem prefix_law_atom (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q)
    (y : ZMod (3 ^ q)) :
    Gated.law (Reference.wordPMF q) (fun a => w <+: a)
      (ValuationWord.residueOffset q) (some y) =
      Reference.wordPMF w.length w *
        (((Reference.law (q - w.length)).map (wordMap w q)) y) := by
  let F (a : ValuationWord) : ℝ≥0∞ :=
    if w <+: a ∧ ValuationWord.residueOffset q a = y then 1 else 0
  have hs : Reference.wordPMF q = (Reference.wordPMF w.length).bind
      (fun u => (Reference.wordPMF (q - w.length)).map (fun t => u ++ t)) := by
    rw [Reference.wordPMF_append, Nat.add_sub_of_le hq]
  rw [Gated.law_some_apply]
  trans ∑' a, Reference.wordPMF q a * F a
  · apply tsum_congr
    intro a
    by_cases h : w <+: a ∧ ValuationWord.residueOffset q a = y <;> simp [F, h]
  rw [hs, PMFMoment.sum_bind]
  simp_rw [PMFMoment.sum_map]
  rw [tsum_eq_single w]
  · apply congrArg (fun z => Reference.wordPMF w.length w * z)
    rw [Reference.law, PMF.map_comp, PMF.map_apply]
    apply tsum_congr
    intro t
    simp only [F, List.prefix_append, true_and, wordMap_offset_append w t hq,
      mul_ite, mul_one, mul_zero, Function.comp_apply]
    by_cases h : wordMap w q (ValuationWord.residueOffset (q - w.length) t) = y
    · simp [h]
    · have h' : y ≠ wordMap w q (ValuationWord.residueOffset (q - w.length) t) :=
        fun he => h he.symm
      simp [h, h']
  · intro u hne
    by_cases hp : Reference.wordPMF w.length u = 0
    · simp [hp]
    · have hu : u.length = w.length :=
        (Reference.wordPMF_mem_support_iff _ _).mp hp
      have hn (t : ValuationWord) : ¬ w <+: u ++ t := by
        rw [prefix_append_iff w u t hu]
        exact hne
      simp [F, hn]

/-- The real original prefix submass has the exact geometric prefix coefficient. -/
theorem prefix_mass (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q)
    (y : ZMod (3 ^ q)) :
    Gated.mass (Reference.wordPMF q) (fun a => w <+: a)
      (ValuationWord.residueOffset q) y =
      (1 / (2 : ℝ) ^ w.total) *
        (((Reference.law (q - w.length)).map (wordMap w q)) y).toReal := by
  rw [Gated.mass, prefix_law_atom w hq, ENNReal.toReal_mul,
    Reference.wordPMF_toReal_length_eq_inv_pow]

private theorem mapped_tail_toReal (w : ValuationWord) (q : ℕ) (y : ZMod (3 ^ q)) :
    (((Reference.law (q - w.length)).map (wordMap w q)) y).toReal =
      ∑ z, if wordMap w q z = y then Reference.mass (q - w.length) z else 0 := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro z _
    by_cases h : wordMap w q z = y
    · simp [h, Reference.mass]
    · have h' : y ≠ wordMap w q z := fun he => h he.symm
      simp [h, h']
  · intro z _
    split_ifs <;> simp [PMF.apply_ne_top]

/-- Scaling the original prefix mass by the full marker factor is exactly affine transfer. -/
theorem wordOperator_marker_eq_prefix (w : ValuationWord) {q : ℕ}
    (hq : w.length ≤ q) (y : ZMod (3 ^ q)) :
    wordOperator w q (Reference.marker (q - w.length)) y =
      ((2 / 3 : ℝ) * (3 : ℝ) ^ q) *
        Gated.mass (Reference.wordPMF q) (fun a => w <+: a)
          (ValuationWord.residueOffset q) y := by
  rw [prefix_mass w hq, mapped_tail_toReal]
  simp only [wordOperator, Reference.marker, Reference.density]
  trans weight w * (((2 / 3 : ℝ) * (3 : ℝ) ^ (q - w.length)) *
    ∑ z, if wordMap w q z = y then Reference.mass (q - w.length) z else 0)
  · apply congrArg (fun z => weight w * z)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : wordMap w q z = y
    · simp only [if_pos h]
      ring
    · simp [h]
  · rw [weight_eq, Reference.scale_eq hq]
    ring

end WordCertDensity.Transfer
