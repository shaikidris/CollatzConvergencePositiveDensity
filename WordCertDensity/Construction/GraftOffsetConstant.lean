/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.OffsetEnvelope

/-! # The literal finite rational graft offset constant

The polynomial envelope is summed through original index 1997. Its remaining
terms decrease by a factor at most one quarter, yielding the exact rational
constant in G.offsetconstant rather than an unspecified finite bound.
-/

namespace WordCertDensity.Construction

/-- Zero-based polynomial envelope: j=0 is original block i=1. -/
noncomputable def graftOffsetTerm (j : ℕ) : ℝ :=
  (1 / 8 : ℝ) ^ j * ((j : ℝ) + 3) ^ 1000

/-- The manuscript's finite rational offset envelope with the first geometric tail term. -/
def graftOffsetConstant : ℚ :=
  (∑ j ∈ Finset.range 1997, (1 / 8 : ℚ) ^ j * ((j : ℚ) + 3) ^ 1000) +
    (4 / 3 : ℚ) * (1 / 8 : ℚ) ^ 1997 * 2000 ^ 1000

/-- Every original scheduled offset term is bounded by its polynomial envelope. -/
theorem continuationOffsetTerm_le_graftOffsetTerm (j : ℕ) :
    continuationOffsetTerm j ≤ graftOffsetTerm j := by
  have hp := continuationPrecision_offset_polynomial (j + 1)
  have he : ((j + 1 : ℕ) : ℝ) + 2 = (j : ℝ) + 3 := by push_cast; ring
  rw [he] at hp
  unfold continuationOffsetTerm graftOffsetTerm
  exact mul_le_mul_of_nonneg_left ((sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)).trans hp)
    (by positivity)

/-- The polynomial envelope terms are nonnegative. -/
theorem graftOffsetTerm_nonneg (j : ℕ) : 0 ≤ graftOffsetTerm j := by
  unfold graftOffsetTerm
  positivity

private theorem polynomial_step {x : ℝ} (hx : 2000 ≤ x) :
    x ^ 1000 ≤ 2 * (x - 1) ^ 1000 := by
  have h := pow_add_mul_le_add_pow (a := x) (b := (-1 : ℝ))
    (by linarith : 0 ≤ x) (by linarith : 0 ≤ 2 * x + -1) 1000
  norm_num only [Nat.cast_ofNat, show 1000 - 1 = 999 by decide, mul_neg_one,
    ← sub_eq_add_neg] at h
  rw [show x ^ 1000 = x ^ 999 * x by rw [← pow_succ]] at h ⊢
  have hn := pow_nonneg (by linarith : 0 ≤ x) 999
  generalize x ^ 999 = y at h hn ⊢
  generalize (x - 1) ^ 1000 = z at h ⊢
  nlinarith

/-- After the displayed cutoff, the next envelope term is at most one quarter. -/
theorem graftOffsetTerm_succ_le {j : ℕ} (hj : 1997 ≤ j) :
    graftOffsetTerm (j + 1) ≤ (1 / 4 : ℝ) * graftOffsetTerm j := by
  have hx : (2000 : ℝ) ≤ (j : ℝ) + 4 := by exact_mod_cast (show 2000 ≤ j + 4 by omega)
  have hp := polynomial_step hx
  have he : (j : ℝ) + 4 - 1 = (j : ℝ) + 3 := by ring
  rw [he] at hp
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ (1 / 8 : ℝ) ^ (j + 1) by positivity)
  have hc : ((j + 1 : ℕ) : ℝ) + 3 = (j : ℝ) + 4 := by push_cast; ring
  unfold graftOffsetTerm
  rw [hc]
  calc
    _ ≤ (1 / 8 : ℝ) ^ (j + 1) * (2 * ((j : ℝ) + 3) ^ 1000) := hm
    _ = _ := by
      rw [pow_succ]
      generalize ((j : ℝ) + 3) ^ 1000 = z
      ring

/-- The whole tail retains its actual first term at original index 1998. -/
theorem graftOffsetTerm_tail_majorant (n : ℕ) :
    graftOffsetTerm (n + 1997) ≤ graftOffsetTerm 1997 * (1 / 4 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := graftOffsetTerm_succ_le (j := n + 1997) (by omega)
      have hm := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 4)
      have he : n + 1 + 1997 = (n + 1997) + 1 := by omega
      rw [he]
      exact h.trans (hm.trans_eq (by rw [pow_succ]; ring))

private theorem summable_graftOffsetTail : Summable (fun n => graftOffsetTerm (n + 1997)) :=
  ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (graftOffsetTerm 1997)).of_nonneg_of_le
    (fun n => graftOffsetTerm_nonneg (n + 1997)) graftOffsetTerm_tail_majorant

/-- The polynomial envelope has the stated finite geometric tail bound. -/
theorem graftOffsetTerm_tail_sum :
    (∑' n : ℕ, graftOffsetTerm (n + 1997)) ≤ (4 / 3 : ℝ) * graftOffsetTerm 1997 := by
  have hs := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (graftOffsetTerm 1997)
  refine (summable_graftOffsetTail.tsum_le_tsum graftOffsetTerm_tail_majorant hs).trans_eq ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)]
  ring

/-- Casting the finite recipe gives exactly the initial envelope sum and its paid tail. -/
theorem graftOffsetConstant_cast :
    (graftOffsetConstant : ℝ) = (∑ j ∈ Finset.range 1997, graftOffsetTerm j) +
      (4 / 3 : ℝ) * graftOffsetTerm 1997 := by
  unfold graftOffsetConstant graftOffsetTerm
  push_cast
  simp only [show (1997 : ℝ) + 3 = 2000 by norm_num, mul_assoc]

/-- The literal infinite continuation envelope is bounded by the manuscript's rational recipe. -/
theorem continuationOffsetBound_le_graftOffsetConstant :
    continuationOffsetBound ≤ (graftOffsetConstant : ℝ) := by
  have hsplit := summable_continuationOffsetTerm.sum_add_tsum_nat_add 1997
  have hhead := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range 1997) =>
    continuationOffsetTerm_le_graftOffsetTerm j)
  have htail := ((summable_nat_add_iff 1997).mpr summable_continuationOffsetTerm).tsum_le_tsum
    (fun j => continuationOffsetTerm_le_graftOffsetTerm (j + 1997)) summable_graftOffsetTail
  rw [graftOffsetConstant_cast]
  change _ + _ = continuationOffsetBound at hsplit
  linarith [graftOffsetTerm_tail_sum]

/-- The finite rational envelope is nonnegative. -/
theorem graftOffsetConstant_nonneg : (0 : ℝ) ≤ graftOffsetConstant :=
  continuationOffsetBound_bounds.1.trans continuationOffsetBound_le_graftOffsetConstant

end WordCertDensity.Construction
