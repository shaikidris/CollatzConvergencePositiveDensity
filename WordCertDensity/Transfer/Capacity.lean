/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Transfer.ResidueCapacity
public import WordCertDensity.Transfer.AffineMap
public import WordCertDensity.Words.Physical
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Capacity of actual inverse histories

A finite indexed family retains every length/valuation tag. Source uniqueness
is required only within a tag. No normalization by the surviving mass occurs.
-/

@[expose] public section

namespace WordCertDensity.Transfer

/-- The length and total valuation determine a history's slope. -/
def historyTag (w : ValuationWord) : ℕ × ℕ := (w.length, w.total)

/-- Equal tags give equal real physical weights. -/
theorem weight_eq_of_historyTag {u v : ValuationWord}
    (h : historyTag u = historyTag v) : weight u = weight v := by
  have hd := congrArg Prod.fst h
  have ha := congrArg Prod.snd h
  change u.length = v.length at hd
  change u.total = v.total at ha
  simp only [weight_eq, hd, ha]

/-- Actual physical endpoints satisfy the real affine equation used in counting. -/
theorem physical_affine_eq {w : ValuationWord} {M x : ℕ}
    (h : PhysicalHistory w M x) : (M : ℝ) = weight w * x + (w.offset : ℝ) := by
  have he := congrArg (fun z : ℚ => (z : ℝ)) h.affine_eq
  simpa only [Rat.cast_natCast, Rat.cast_add, Rat.cast_mul, weight] using he

/-- The unnormalized weight of histories whose actual source is in one ternary class. -/
noncomputable def historyHistogram {α : Type*} (H : Finset α)
    (word : α → ValuationWord) (source : α → ℕ) (q : ℕ) (a : ZMod (3 ^ q)) : ℝ := by
  classical
  exact ∑ i ∈ H with (source i : ZMod (3 ^ q)) = a, weight (word i)

/-- Every history histogram has nonnegative mass. -/
theorem historyHistogram_nonneg {α : Type*} (H : Finset α)
    (word : α → ValuationWord) (source : α → ℕ) (q : ℕ) (a : ZMod (3 ^ q)) :
    0 ≤ historyHistogram H word source q a := by
  classical
  exact Finset.sum_nonneg fun i _ => (weight_pos (word i)).le

/-- A fixed tag in a physical family pays the offset width and one residual point. -/
theorem physical_tag_capacity {α : Type*} (H : Finset α)
    (word : α → ValuationWord) (source : α → ℕ) {M : ℕ} (q : ℕ)
    (a : ZMod (3 ^ q)) (v : ValuationWord) {sigma cmin cmax : ℝ}
    (hphysical : ∀ i ∈ H, PhysicalHistory (word i) M (source i))
    (htag : ∀ i ∈ H, historyTag (word i) = historyTag v)
    (hinj : Set.InjOn source (H : Set α))
    (hsigma : weight v ≤ sigma) (horder : cmin ≤ cmax)
    (hoffset : ∀ i ∈ H, cmin ≤ ((word i).offset : ℝ) ∧
      ((word i).offset : ℝ) ≤ cmax) :
    (3 : ℝ) ^ q * historyHistogram H word source q a ≤
      (cmax - cmin) + (3 : ℝ) ^ q * sigma := by
  classical
  let F := H.filter fun i => (source i : ZMod (3 ^ q)) = a
  have hFH : F ⊆ H := Finset.filter_subset _ _
  have hw (i : α) (hi : i ∈ F) : weight (word i) = weight v :=
    weight_eq_of_historyTag (htag i (hFH hi))
  have hc := affine_family_capacity F source (fun i => ((word i).offset : ℝ))
    (3 ^ q) a.val (M := (M : ℝ)) (hinj.mono hFH)
    (fun i hi => by
      have he := congrArg ZMod.val (Finset.mem_filter.mp hi).2
      simpa only [ZMod.val_natCast] using he)
    (weight_pos v).le hsigma horder
    (fun i hi => by rw [← hw i hi]; exact physical_affine_eq (hphysical i (hFH hi)))
    (fun i hi => hoffset i (hFH hi))
  have hm : historyHistogram H word source q a = (F.card : ℝ) * weight v := by
    change (∑ i ∈ F, weight (word i)) = _
    rw [Finset.sum_congr rfl hw]
    simp
  rw [hm]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using hc

/-- All tags of an actual finite family contribute to its pointwise capacity. -/
theorem history_capacity {α : Type*} (H : Finset α)
    (word : α → ValuationWord) (source : α → ℕ) {M : ℕ} (q : ℕ)
    (a : ZMod (3 ^ q)) {T sigma cmin cmax : ℝ}
    (hphysical : ∀ i ∈ H, PhysicalHistory (word i) M (source i))
    (hinj : ∀ i ∈ H, ∀ j ∈ H, historyTag (word i) = historyTag (word j) →
      source i = source j → i = j)
    (hweight : ∀ i ∈ H, weight (word i) ≤ sigma)
    (hsigma : 0 ≤ sigma) (horder : cmin ≤ cmax)
    (hoffset : ∀ i ∈ H, cmin ≤ ((word i).offset : ℝ) ∧
      ((word i).offset : ℝ) ≤ cmax)
    (htags : ((H.image fun i => historyTag (word i)).card : ℝ) ≤ T) :
    (3 : ℝ) ^ q * historyHistogram H word source q a ≤
      T * ((cmax - cmin) + (3 : ℝ) ^ q * sigma) := by
  classical
  let tags := H.image fun i => historyTag (word i)
  let F := H.filter fun i => (source i : ZMod (3 ^ q)) = a
  have hsum : (∑ t ∈ tags, historyHistogram
      (H.filter fun i => historyTag (word i) = t) word source q a) =
      historyHistogram H word source q a := by
    have hf := Finset.sum_fiberwise_of_maps_to
      (s := F) (t := tags) (g := fun i => historyTag (word i))
      (fun i hi => Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩)
      (fun i => weight (word i))
    simpa only [historyHistogram, F, Finset.filter_filter, and_comm] using hf
  have htagbound (t : ℕ × ℕ) (ht : t ∈ tags) :
      (3 : ℝ) ^ q * historyHistogram
        (H.filter fun i => historyTag (word i) = t) word source q a ≤
        (cmax - cmin) + (3 : ℝ) ^ q * sigma := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    apply physical_tag_capacity _ word source q a (word j)
      (fun i hi => hphysical i (Finset.mem_filter.mp hi).1)
      (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun i hi k hk he => hinj i (Finset.mem_filter.mp hi).1 k
        (Finset.mem_filter.mp hk).1
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm) he)
      (hweight j hj) horder
      (fun i hi => hoffset i (Finset.mem_filter.mp hi).1)
  calc
    (3 : ℝ) ^ q * historyHistogram H word source q a =
        ∑ t ∈ tags, (3 : ℝ) ^ q * historyHistogram
          (H.filter fun i => historyTag (word i) = t) word source q a := by
      rw [← Finset.mul_sum, hsum]
    _ ≤ ∑ _t ∈ tags, ((cmax - cmin) + (3 : ℝ) ^ q * sigma) :=
      Finset.sum_le_sum htagbound
    _ = (tags.card : ℝ) * ((cmax - cmin) + (3 : ℝ) ^ q * sigma) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ T * ((cmax - cmin) + (3 : ℝ) ^ q * sigma) :=
      mul_le_mul_of_nonneg_right htags
        (add_nonneg (sub_nonneg.mpr horder) (by positivity))

/-- Restriction only removes original weights; it never renormalizes the histogram. -/
theorem historyHistogram_mono {α : Type*} {H K : Finset α} (hKH : K ⊆ H)
    (word : α → ValuationWord) (source : α → ℕ) (q : ℕ) (a : ZMod (3 ^ q)) :
    historyHistogram K word source q a ≤ historyHistogram H word source q a := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hKH)
    (fun i _ _ => (weight_pos (word i)).le)

/-- Bounding both tag coordinates bounds every occurring tag, including depth zero. -/
theorem historyTag_card_le {α : Type*} (H : Finset α) (word : α → ValuationWord)
    (S : ℕ) (hdepth : ∀ i ∈ H, (word i).length ≤ S)
    (htotal : ∀ i ∈ H, (word i).total ≤ S) :
    (H.image fun i => historyTag (word i)).card ≤ (S + 1) ^ 2 := by
  classical
  have hsub : (H.image fun i => historyTag (word i)) ⊆
      (Finset.range (S + 1)).product (Finset.range (S + 1)) := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hdepth i hi)),
        Finset.mem_range.mpr (Nat.lt_succ_of_le (htotal i hi))⟩
  simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_range, pow_two]
    using Finset.card_le_card hsub

/-- Concatenating blocks bounded by one slope envelope multiplies that envelope. -/
theorem weight_flatten_le (blocks : List ValuationWord) {beta : ℝ}
    (hbeta : 0 ≤ beta) (hblocks : ∀ w ∈ blocks, weight w ≤ beta) :
    weight blocks.flatten ≤ beta ^ blocks.length := by
  induction blocks with
  | nil => simp [weight_nil]
  | cons w blocks ih =>
      have hw := hblocks w (by simp)
      have ht := ih (fun v hv => hblocks v (by simp [hv]))
      have he : weight (w ++ blocks.flatten) = weight w * weight blocks.flatten := by
        simp only [weight, ValuationWord.slope_append, Rat.cast_mul]
      simp only [List.flatten_cons, List.length_cons, he, pow_succ]
      calc
        weight w * weight blocks.flatten ≤ beta * beta ^ blocks.length :=
          mul_le_mul hw ht (weight_pos _).le hbeta
        _ = beta ^ blocks.length * beta := mul_comm _ _

end WordCertDensity.Transfer
