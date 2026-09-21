/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Transfer.CapacityPairing

/-! # Paying for a parent-dependent choice of test function

Each actual history is assigned one label. Restriction preserves its original
weight and inherits the full histogram capacity; summing the separate estimates
pays the number of permitted labels.
-/

namespace WordCertDensity.Transfer

/-- Restricting to any selected label keeps the full original capacity. -/
theorem historyHistogram_restricted_capacity {α : Type*} (H : Finset α)
    (word : α → ValuationWord) (source : α → ℕ) (q : ℕ) {B : ℝ}
    (hcapacity : ∀ a, (3 : ℝ)^q * historyHistogram H word source q a ≤ B)
    {K : Finset α} (hK : K ⊆ H) (a : ZMod (3^q)) :
    (3 : ℝ)^q * historyHistogram K word source q a ≤ B :=
  (mul_le_mul_of_nonneg_left (historyHistogram_mono hK word source q a)
    (by positivity)).trans (hcapacity a)

/-- The absolute selected discrepancy is paid separately on every actual label fiber. -/
theorem history_selected_abs_sum_le {α β : Type*} [DecidableEq β]
    (H : Finset α) (labels : Finset β) (select : α → β)
    (word : α → ValuationWord) (source : α → ℕ) (q : ℕ)
    (psi : β → ZMod (3^q) → ℝ) {B E : ℝ} (hB : 0 ≤ B)
    (hselect : ∀ i ∈ H, select i ∈ labels)
    (hcapacity : ∀ a, (3 : ℝ)^q * historyHistogram H word source q a ≤ B)
    (hmean : ∀ u ∈ labels, Reference.mean q (fun a => |psi u a|) ≤ E) :
    (∑ i ∈ H, weight (word i) * |psi (select i) (source i)|) ≤
      (labels.card : ℝ) * B * E := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hselect
    (fun i => weight (word i) * |psi (select i) (source i)|)]
  calc
    _ ≤ ∑ u ∈ labels, B * E := by
      apply Finset.sum_le_sum
      intro u hu
      have he : (∑ i ∈ H.filter (fun i => select i = u),
          weight (word i) * |psi (select i) (source i)|) =
          ∑ a, historyHistogram (H.filter (fun i => select i = u)) word source q a *
            |psi u a| := by
        rw [historyHistogram_pair_eq]
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      rw [he]
      exact (capacity_abs_sum_le q _ (psi u)
        (historyHistogram_restricted_capacity H word source q hcapacity
          (Finset.filter_subset _ _))).trans
        (mul_le_mul_of_nonneg_left (hmean u hu) hB)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The signed selected pairing obeys the same paid label count. -/
theorem history_selected_pairing {α β : Type*} [DecidableEq β]
    (H : Finset α) (labels : Finset β) (select : α → β)
    (word : α → ValuationWord) (source : α → ℕ) (q : ℕ)
    (psi : β → ZMod (3^q) → ℝ) {B E : ℝ} (hB : 0 ≤ B)
    (hselect : ∀ i ∈ H, select i ∈ labels)
    (hcapacity : ∀ a, (3 : ℝ)^q * historyHistogram H word source q a ≤ B)
    (hmean : ∀ u ∈ labels, Reference.mean q (fun a => |psi u a|) ≤ E) :
    |∑ i ∈ H, weight (word i) * psi (select i) (source i)| ≤
      (labels.card : ℝ) * B * E := by
  calc
    _ ≤ ∑ i ∈ H, |weight (word i) * psi (select i) (source i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ H, weight (word i) * |psi (select i) (source i)| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (weight_pos _).le]
    _ ≤ _ := history_selected_abs_sum_le H labels select word source q psi
      hB hselect hcapacity hmean

end WordCertDensity.Transfer
