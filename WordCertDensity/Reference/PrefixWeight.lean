/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.Stopping
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Weighted mass of a finite prefix-free family

The letters may have any nonnegative weights whose finite sums are at most
one. Induction on the maximum word length gives the same bound for a finite
prefix-free family. Geometric perturbations provide the stopped-mean consumer.
-/

@[expose] public section

namespace WordCertDensity.Reference

open scoped Classical

/-- Product of independent letter weights on the existing positive-word type. -/
def prefixWeight (p : ℕ+ → ℝ) : ValuationWord → ℝ
  | [] => 1
  | a :: w => p a * prefixWeight p w

/-- Nonnegative letter weights give nonnegative word weights. -/
theorem prefixWeight_nonneg {p : ℕ+ → ℝ} (hp : ∀ a, 0 ≤ p a) (w : ValuationWord) :
    0 ≤ prefixWeight p w := by
  induction w with
  | nil => exact zero_le_one
  | cons a w ih => exact mul_nonneg (hp a) ih

private def branchTails (V : Finset ValuationWord) (a : ℕ+) : Finset ValuationWord :=
  (V.filter (fun w => w.headD 1 = a)).image List.tail

private theorem word_eq_cons_tail {V : Finset ValuationWord} (hnil : [] ∉ V)
    {a : ℕ+} {w : ValuationWord} (hw : w ∈ V.filter (fun w => w.headD 1 = a)) :
    w = a :: w.tail := by
  obtain ⟨hv, hh⟩ := Finset.mem_filter.mp hw
  cases w with
  | nil => exact (hnil hv).elim
  | cons b w =>
      have hb : b = a := hh
      subst b
      rfl

private theorem mem_branchTails {V : Finset ValuationWord} (hnil : [] ∉ V)
    (a : ℕ+) (w : ValuationWord) : w ∈ branchTails V a ↔ a :: w ∈ V := by
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rw [← word_eq_cons_tail hnil hv]
    exact (Finset.mem_filter.mp hv).1
  · intro hw
    apply Finset.mem_image.mpr
    exact ⟨a :: w, Finset.mem_filter.mpr ⟨hw, rfl⟩, rfl⟩

private theorem branch_sum {p : ℕ+ → ℝ} {V : Finset ValuationWord} (hnil : [] ∉ V)
    (a : ℕ+) :
    (∑ w ∈ V.filter (fun w => w.headD 1 = a), prefixWeight p w) =
      p a * ∑ w ∈ branchTails V a, prefixWeight p w := by
  have hinj : Set.InjOn List.tail (↑(V.filter (fun w => w.headD 1 = a)) : Set ValuationWord) := by
    intro u hu v hv h
    rw [word_eq_cons_tail hnil hu, word_eq_cons_tail hnil hv, h]
  rw [branchTails, Finset.sum_image hinj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  conv_lhs => rw [word_eq_cons_tail hnil hw]
  rfl

private theorem prefixWeight_sum_le_one_depth {p : ℕ+ → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hpsum : ∀ A : Finset ℕ+, ∑ a ∈ A, p a ≤ 1)
    (n : ℕ) (V : Finset ValuationWord)
    (hlen : ∀ w ∈ V, w.length ≤ n)
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v)) :
    ∑ w ∈ V, prefixWeight p w ≤ 1 := by
  induction n generalizing V with
  | zero =>
      have hs : V ⊆ {[]} := by
        intro w hw
        rw [Finset.mem_singleton]
        exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (hlen w hw))
      refine (Finset.sum_le_sum_of_subset_of_nonneg hs
        (fun w _ _ => prefixWeight_nonneg hp w)).trans_eq ?_
      simp [prefixWeight]
  | succ n ih =>
      by_cases hnil : [] ∈ V
      · have hs : V ⊆ {[]} := by
          intro w hw
          rw [Finset.mem_singleton]
          by_contra hne
          exact hfree hnil hw (Ne.symm hne) ⟨w, rfl⟩
        refine (Finset.sum_le_sum_of_subset_of_nonneg hs
          (fun w _ _ => prefixWeight_nonneg hp w)).trans_eq ?_
        simp [prefixWeight]
      · let A := V.image (fun w => w.headD 1)
        have hmaps : ∀ w ∈ V, w.headD 1 ∈ A :=
          fun w hw => Finset.mem_image_of_mem _ hw
        rw [← Finset.sum_fiberwise_of_maps_to hmaps (prefixWeight p)]
        refine (Finset.sum_le_sum (fun a _ => ?_)).trans (hpsum A)
        rw [branch_sum hnil a]
        have hl : ∀ w ∈ branchTails V a, w.length ≤ n := by
          intro w hw
          have h := hlen (a :: w) ((mem_branchTails hnil a w).mp hw)
          simpa using h
        have hf : (branchTails V a : Set ValuationWord).Pairwise
            (fun u v => ¬ u <+: v) := by
          intro u hu v hv hne huv
          apply hfree ((mem_branchTails hnil a u).mp hu)
            ((mem_branchTails hnil a v).mp hv)
            (fun he => hne (List.cons.inj he).2)
          obtain ⟨t, rfl⟩ := huv
          exact ⟨t, rfl⟩
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (ih (branchTails V a) hl hf) (hp a)

/-- A finite prefix-free family's product weights have total mass at most one. -/
theorem prefixWeight_sum_le_one {p : ℕ+ → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hpsum : ∀ A : Finset ℕ+, ∑ a ∈ A, p a ≤ 1)
    (V : Finset ValuationWord)
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v)) :
    ∑ w ∈ V, prefixWeight p w ≤ 1 :=
  prefixWeight_sum_le_one_depth hp hpsum (V.sup List.length) V
    (fun _ hw => Finset.le_sup hw) hfree

/-- A geometric perturbation assigns the letter k mass (1-q) q^(k-1). -/
noncomputable def biasedLetter (q : ℝ) (a : ℕ+) : ℝ := (1 - q) / q * q ^ (a : ℕ)

/-- Perturbed letters have positive mass throughout the open parameter interval. -/
theorem biasedLetter_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (a : ℕ+) :
    0 < biasedLetter q a := by
  unfold biasedLetter
  exact mul_pos (div_pos (sub_pos.mpr hq1) hq0) (pow_pos hq0 _)

/-- The perturbed letter law sums exactly to one, using its positive-natural indexing. -/
theorem hasSum_biasedLetter {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (biasedLetter q) 1 := by
  have h := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left (1 - q)
  rw [mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hq1))] at h
  apply (Equiv.pnatEquivNat.symm.hasSum_iff).mp
  apply h.congr_fun
  intro n
  change (1 - q) / q * q ^ (n + 1) = (1 - q) * q ^ n
  rw [pow_succ]
  field_simp

/-- The original geometric letter weight occurs at parameter one half. -/
theorem biasedLetter_half (a : ℕ+) : biasedLetter (1 / 2) a = (1 / 2 : ℝ) ^ (a : ℕ) := by
  norm_num [biasedLetter]

/-- The perturbed weight depends only on total valuation and depth. -/
theorem prefixWeight_biased (q : ℝ) (w : ValuationWord) :
    prefixWeight (biasedLetter q) w = ((1 - q) / q) ^ w.length * q ^ w.total := by
  induction w with
  | nil => simp [prefixWeight, ValuationWord.total]
  | cons a w ih =>
      simp only [prefixWeight, biasedLetter, ih, List.length_cons,
        ValuationWord.total, List.map_cons, List.sum_cons, pow_succ, pow_add]
      ring

/-- Every fixed prefix-free family has perturbed geometric mass at most one. -/
theorem biased_prefixWeight_sum_le_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (V : Finset ValuationWord)
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v)) :
    ∑ w ∈ V, prefixWeight (biasedLetter q) w ≤ 1 := by
  apply prefixWeight_sum_le_one (fun a => (biasedLetter_pos hq0 hq1 a).le) _ V hfree
  intro A
  have h := hasSum_biasedLetter hq0 hq1
  exact (h.summable.sum_le_tsum A (fun a _ => (biasedLetter_pos hq0 hq1 a).le)).trans_eq
    h.tsum_eq

end WordCertDensity.Reference
