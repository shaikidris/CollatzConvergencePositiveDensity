/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Transfer.Selected
import WordCertDensity.Analytic.FullMixing

/-!
# Finite stopping transfer with three distinct costs

One fixed prefix-free family is compared using original weights. Coarse
replacement, the exact missing selected mass, and final reference mixing
are paid separately. A parent-dependent family still needs its own grouping
or coupling argument.
-/

namespace WordCertDensity.Transfer

private theorem mean_sum {α : Type*} [Fintype α] (q : ℕ)
    (f : α → ZMod (3 ^ q) → ℝ) :
    Reference.mean q (fun y => ∑ i, f i y) = ∑ i, Reference.mean q (f i) := by
  simp only [Reference.mean]
  rw [Finset.sum_comm, Finset.sum_div]

private theorem mean_abs_sum_le {α : Type*} [Fintype α] (q : ℕ)
    (f : α → ZMod (3 ^ q) → ℝ) :
    Reference.mean q (fun y => |∑ i, f i y|) ≤
      ∑ i, Reference.mean q (fun y => |f i y|) := by
  calc
    _ ≤ Reference.mean q (fun y => ∑ i, |f i y|) :=
      Reference.mean_mono q _ _ (fun _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := mean_sum q _

private theorem mean_abs_sub_triangle (q : ℕ) (f g h : ZMod (3 ^ q) → ℝ) :
    Reference.mean q (fun y => |f y - h y|) ≤
      Reference.mean q (fun y => |f y - g y|) + Reference.mean q (fun y => |g y - h y|) := by
  calc
    _ ≤ Reference.mean q (fun y => |f y - g y| + |g y - h y|) :=
      Reference.mean_mono q _ _ (fun y => abs_sub_le (f y) (g y) (h y))
    _ = _ := Reference.mean_add q _ _

/-- Coarse replacement subtracts inside each original affine word transfer. -/
theorem coarseSelected_sub_selected (V : Finset ValuationWord) (q k : ℕ)
    (hk : ∀ w ∈ V, k ≤ q - w.length) (y : ZMod (3 ^ q)) :
    coarseSelected V q k hk y - selected V q y =
      ∑ w : V, wordOperator w q
        (fun z => Reference.marker k (Reference.project (hk w w.property) z) -
          Reference.marker (q - w.val.length) z) y := by
  classical
  have hs : selected V q y =
      ∑ w : V, wordOperator w q (Reference.marker (q - w.val.length)) y :=
    (Finset.sum_attach V (fun w => wordOperator w q (Reference.marker (q - w.length)) y)).symm
  rw [coarseSelected, hs, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  exact (wordOperator_sub w q _ _ y).symm

/-- The first stopping cost pays epsilon_k times the original total family weight. -/
theorem coarseSelected_error_le (V : Finset ValuationWord) {q k : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ q) (hk : ∀ w ∈ V, k ≤ q - w.length)
    (hkpos : 1 ≤ k) :
    Reference.mean q (fun y => |coarseSelected V q k hk y - selected V q y|) ≤
      (2 / 3 : ℝ) * Reference.stoppingMass V * Analytic.mixingError k := by
  classical
  simp_rw [coarseSelected_sub_selected]
  calc
    _ ≤ ∑ w : V, Reference.mean q (fun y => |wordOperator w q
        (fun z => Reference.marker k (Reference.project (hk w w.property) z) -
          Reference.marker (q - w.val.length) z) y|) := mean_abs_sum_le q _
    _ ≤ ∑ w : V, (1 / (2 : ℝ) ^ w.val.total) *
        ((2 / 3 : ℝ) * Analytic.mixingError k) := by
      apply Finset.sum_le_sum
      intro w _
      rw [mean_abs_wordOperator w (hlen w w.property)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [abs_sub_comm] using
        Analytic.marker_mean_le_mixingError hkpos (hk w w.property)
    _ = _ := by
      have hp : (∑ w : V, 1 / (2 : ℝ) ^ w.val.total) = Reference.stoppingMass V :=
        Finset.sum_attach V (fun w => 1 / (2 : ℝ) ^ w.total)
      rw [← Finset.sum_mul, hp]
      ring

/-- Prefix exclusion turns the exact missing mean into the exact unhalved L1 deficit. -/
theorem selected_abs_deficit (V : Finset ValuationWord) {q : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ q)
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v)) :
    Reference.mean q (fun y => |selected V q y - Reference.marker q y|) =
      (2 / 3 : ℝ) * (1 - Reference.stoppingMass V) := by
  calc
    _ = Reference.mean q (fun y => Reference.marker q y - selected V q y) := by
      apply congrArg (Reference.mean q)
      funext y
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (selected_le_marker V hlen hfree y))]
    _ = _ := mean_selected_deficit V hlen

/-- Finite stopping transfer retains the three manuscript costs and original survival mass. -/
theorem stopped_transfer (V : Finset ValuationWord) {q k ell : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ q) (hk : ∀ w ∈ V, k ≤ q - w.length)
    (hkpos : 1 ≤ k) (hellpos : 1 ≤ ell) (hellq : ell ≤ q)
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v)) :
    Reference.mean q (fun y => |coarseSelected V q k hk y -
      Reference.marker ell (Reference.project hellq y)|) ≤
      (2 / 3 : ℝ) * (Reference.stoppingMass V * Analytic.mixingError k +
        Analytic.mixingError ell + 1 - Reference.stoppingMass V) := by
  have hc := coarseSelected_error_le V hlen hk hkpos
  have hd := selected_abs_deficit V hlen hfree
  have hm := Analytic.marker_mean_le_mixingError hellpos hellq
  have hfirst := mean_abs_sub_triangle q (coarseSelected V q k hk)
    (selected V q) (Reference.marker q)
  have hlast := mean_abs_sub_triangle q (coarseSelected V q k hk)
    (Reference.marker q) (fun y => Reference.marker ell (Reference.project hellq y))
  linarith

/-- The coarser bound uses p(V)<=1, without dividing by that probability. -/
theorem stopped_transfer_le (V : Finset ValuationWord) {q k ell : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ q) (hk : ∀ w ∈ V, k ≤ q - w.length)
    (hkpos : 1 ≤ k) (hellpos : 1 ≤ ell) (hellq : ell ≤ q)
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v)) :
    Reference.mean q (fun y => |coarseSelected V q k hk y -
      Reference.marker ell (Reference.project hellq y)|) ≤
      (2 / 3 : ℝ) * (Analytic.mixingError k + Analytic.mixingError ell +
        1 - Reference.stoppingMass V) := by
  apply (stopped_transfer V hlen hk hkpos hellpos hellq hfree).trans
  have hp := mul_le_mul_of_nonneg_right (Reference.stoppingMass_le_one V hfree)
    (Analytic.mixingError_pos hkpos).le
  nlinarith

end WordCertDensity.Transfer
