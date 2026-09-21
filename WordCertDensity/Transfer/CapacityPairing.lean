/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Transfer.Capacity
import WordCertDensity.Transfer.Stopped

/-!
# Physical histogram pairing and stopped marked variation

The residue capacity is paired with the full-group mean. Its conductor factor
cancels exactly once. These estimates do not identify selected residues with
positive integer orbit extensions or justify parent-dependent family choices.
-/

namespace WordCertDensity.Transfer

/-- A scaled pointwise capacity bounds the weighted absolute test function. -/
theorem capacity_abs_sum_le (q : ℕ) (h psi : ZMod (3 ^ q) → ℝ) {B : ℝ}
    (hcapacity : ∀ a, (3 : ℝ) ^ q * h a ≤ B) :
    (∑ a, h a * |psi a|) ≤ B * Reference.mean q (fun a => |psi a|) := by
  rw [Reference.mean, ← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < (3 : ℝ) ^ q)).mpr
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  calc
    h a * |psi a| * (3 : ℝ) ^ q = ((3 : ℝ) ^ q * h a) * |psi a| := by ring
    _ ≤ B * |psi a| := mul_le_mul_of_nonneg_right (hcapacity a) (abs_nonneg _)

/-- A nonnegative histogram pairs against arbitrary signed test functions. -/
theorem capacity_pairing (q : ℕ) (h psi : ZMod (3 ^ q) → ℝ) {B : ℝ}
    (hnonneg : ∀ a, 0 ≤ h a) (hcapacity : ∀ a, (3 : ℝ) ^ q * h a ≤ B) :
    |∑ a, h a * psi a| ≤ B * Reference.mean q (fun a => |psi a|) := by
  calc
    |∑ a, h a * psi a| ≤ ∑ a, |h a * psi a| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, h a * |psi a| := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul, abs_of_nonneg (hnonneg a)]
    _ ≤ _ := capacity_abs_sum_le q h psi hcapacity

/-- Pairing the histogram is exactly the original weighted sum over integer sources. -/
theorem historyHistogram_pair_eq {α : Type*} (H : Finset α)
    (word : α → ValuationWord) (source : α → ℕ) (q : ℕ)
    (psi : ZMod (3 ^ q) → ℝ) :
    (∑ a, historyHistogram H word source q a * psi a) =
      ∑ i ∈ H, weight (word i) * psi (source i) := by
  classical
  simp only [historyHistogram, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [eq_comm]

/-- The literal signed pairing bound for an actual finite family of histories. -/
theorem history_capacity_pairing {α : Type*} (H : Finset α)
    (word : α → ValuationWord) (source : α → ℕ) {M : ℕ} (q : ℕ)
    (psi : ZMod (3 ^ q) → ℝ) {T sigma cmin cmax : ℝ}
    (hphysical : ∀ i ∈ H, PhysicalHistory (word i) M (source i))
    (hinj : ∀ i ∈ H, ∀ j ∈ H, historyTag (word i) = historyTag (word j) →
      source i = source j → i = j)
    (hweight : ∀ i ∈ H, weight (word i) ≤ sigma)
    (hsigma : 0 ≤ sigma) (horder : cmin ≤ cmax)
    (hoffset : ∀ i ∈ H, cmin ≤ ((word i).offset : ℝ) ∧
      ((word i).offset : ℝ) ≤ cmax)
    (htags : ((H.image fun i => historyTag (word i)).card : ℝ) ≤ T) :
    |∑ a, historyHistogram H word source q a * psi a| ≤
      T * ((cmax - cmin) + (3 : ℝ) ^ q * sigma) *
        Reference.mean q (fun a => |psi a|) := by
  exact capacity_pairing q (historyHistogram H word source q) psi
    (historyHistogram_nonneg H word source q)
    (fun a => history_capacity H word source q a hphysical hinj hweight
      hsigma horder hoffset htags)

/-- Capacity and finite stopping give the physical marked variation bound. -/
theorem history_stopped_variation {α : Type*} (H : Finset α)
    (word : α → ValuationWord) (source : α → ℕ) {M : ℕ}
    (V : Finset ValuationWord) {q k ell : ℕ} {T sigma cmin cmax : ℝ}
    (hphysical : ∀ i ∈ H, PhysicalHistory (word i) M (source i))
    (hinj : ∀ i ∈ H, ∀ j ∈ H, historyTag (word i) = historyTag (word j) →
      source i = source j → i = j)
    (hweight : ∀ i ∈ H, weight (word i) ≤ sigma)
    (hsigma : 0 ≤ sigma) (horder : cmin ≤ cmax)
    (hoffset : ∀ i ∈ H, cmin ≤ ((word i).offset : ℝ) ∧
      ((word i).offset : ℝ) ≤ cmax)
    (htags : ((H.image fun i => historyTag (word i)).card : ℝ) ≤ T)
    (hlen : ∀ w ∈ V, w.length ≤ q) (hk : ∀ w ∈ V, k ≤ q - w.length)
    (hkpos : 1 ≤ k) (hellpos : 1 ≤ ell) (hellq : ell ≤ q)
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v)) :
    (∑ a, historyHistogram H word source q a *
      |coarseSelected V q k hk a - Reference.marker ell (Reference.project hellq a)|) ≤
      (2 / 3 : ℝ) * T * ((cmax - cmin) + (3 : ℝ) ^ q * sigma) *
        (Analytic.mixingError k + Analytic.mixingError ell +
          1 - Reference.stoppingMass V) := by
  have hT : 0 ≤ T := (Nat.cast_nonneg _).trans htags
  have hB : 0 ≤ T * ((cmax - cmin) + (3 : ℝ) ^ q * sigma) :=
    mul_nonneg hT (add_nonneg (sub_nonneg.mpr horder) (by positivity))
  have hp := capacity_abs_sum_le q (historyHistogram H word source q)
    (fun a => coarseSelected V q k hk a -
      Reference.marker ell (Reference.project hellq a))
    (fun a => history_capacity H word source q a hphysical hinj hweight
      hsigma horder hoffset htags)
  have hm := mul_le_mul_of_nonneg_left
    (stopped_transfer_le V hlen hk hkpos hellpos hellq hfree) hB
  apply hp.trans
  convert hm using 1
  ring

end WordCertDensity.Transfer
