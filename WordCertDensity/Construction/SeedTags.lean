/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.SeedHistories
public import WordCertDensity.Transfer.Capacity

/-! # Exact seed tag counts and the retained growth budget -/

@[expose] public section

namespace WordCertDensity.Construction

/-- The manuscript's conservative tag-growth base. -/
noncomputable def seedTagGrowth : ℝ := 2013 / 2000

/-- The retained initial tag coefficient. -/
noncomputable def seedTagConstant (b : ℕ) : ℝ := 20 * (4 * b + 1)

/-- The tag budget retained by all later variation and graft estimates. -/
noncomputable def seedTagBudget (b n : ℕ) : ℝ :=
  seedTagConstant b * ((n : ℝ) + 1) ^ 3 * seedTagGrowth ^ n

/-- The growth base is greater than one. -/
theorem seedTagGrowth_one_le : 1 ≤ seedTagGrowth := by norm_num [seedTagGrowth]

/-- The exact fifth-power comparison pays the fractional growth of the seed width. -/
theorem seedTagGrowth_rpow : (101 / 100 : ℝ) ^ (3 / 5 : ℝ) ≤ seedTagGrowth := by
  apply (Real.rpow_le_rpow_iff (by positivity)
    (by norm_num [seedTagGrowth]) (by norm_num : (0 : ℝ) < 5)).mp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 101 / 100)]
  norm_num [seedTagGrowth]

/-- The fractional seed-size power has the retained geometric growth base. -/
theorem seedSize_power_le {b : ℕ} (hb : 200 ≤ b) (n : ℕ) :
    (seedSize b n : ℝ) ^ (3 / 5 : ℝ) ≤ (b : ℝ) ^ (3 / 5 : ℝ) * seedTagGrowth ^ n := by
  have hupperQ := (seedSize_geometric hb n).2
  have hupper : (seedSize b n : ℝ) ≤ b * (101 / 100 : ℝ) ^ n := by
    have h : ((seedSize b n : ℚ) : ℝ) ≤ (((b : ℚ) * (101 / 100 : ℚ) ^ n : ℚ) : ℝ) :=
      Rat.cast_le.mpr hupperQ
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using h
  have h := Real.rpow_le_rpow (Nat.cast_nonneg _) hupper (by norm_num : (0 : ℝ) ≤ 3 / 5)
  rw [Real.mul_rpow (Nat.cast_nonneg b) (by positivity),
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 101 / 100),
    mul_comm (n : ℝ) (3 / 5 : ℝ), Real.rpow_mul_natCast (by norm_num)] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) seedTagGrowth_rpow n) (by positivity))

/-- Summing the actual ceiling radii gives the manuscript's finite radius bound. -/
theorem seedRadius_le {b : ℕ} (hb : 200 ≤ b) (n : ℕ) :
    (seedRadius b 0 n : ℝ) ≤ 2 * n * (b : ℝ) ^ (3 / 5 : ℝ) * seedTagGrowth ^ n := by
  simp only [seedRadius, Nat.zero_add, Nat.cast_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range n, 2 * (b : ℝ) ^ (3 / 5 : ℝ) * seedTagGrowth ^ n := by
      apply Finset.sum_le_sum
      intro j hj
      have hs := seedSize_ge b j
      have hw := seedWidth_le_twice (by omega : 1 ≤ seedSize b j)
      have hg := seedSize_power_le hb j
      have hn := pow_le_pow_right₀ seedTagGrowth_one_le (Nat.le_of_lt (Finset.mem_range.mp hj))
      have hfirst : (seedWidth (seedSize b j) : ℝ) ≤
          2 * (b : ℝ) ^ (3 / 5 : ℝ) * seedTagGrowth ^ j := by
        simpa only [mul_assoc] using hw.trans (mul_le_mul_of_nonneg_left hg (by norm_num))
      exact hfirst.trans (mul_le_mul_of_nonneg_left hn
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg b) _)))
    _ = _ := by simp; ring

/-- The exact fixed-depth tag count is at most twice the accumulated radius plus one. -/
theorem seedHistory_tag_card (H : Finset (List ValuationWord)) {b n : ℕ}
    (hH : ∀ ws ∈ H, ws ∈ seedBlockLists b 0 n) :
    (H.image (fun ws => Transfer.historyTag ws.flatten)).card ≤ 2 * seedRadius b 0 n + 1 := by
  have hsub : H.image (fun ws => Transfer.historyTag ws.flatten) ⊆
      Finset.product ({seedDepth b 0 n} : Finset ℕ)
        (Finset.Icc (2 * seedDepth b 0 n - seedRadius b 0 n)
          (2 * seedDepth b 0 n + seedRadius b 0 n)) := by
    intro tag ht
    obtain ⟨ws, hw, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hlen, hs⟩ := (mem_seedBlockLists b 0 n ws).mp (hH ws hw)
    have hd := seedBlocks_depth hs
    have hv := seedBlocks_total_bounds hs
    rw [hlen] at hd hv
    apply Finset.mem_product.mpr
    have hlo : 2 * seedDepth b 0 n - seedRadius b 0 n ≤ ValuationWord.total ws.flatten := by omega
    have hhi : ValuationWord.total ws.flatten ≤ 2 * seedDepth b 0 n + seedRadius b 0 n := hv.2
    exact ⟨Finset.mem_singleton.mpr hd, Finset.mem_Icc.mpr ⟨hlo, hhi⟩⟩
  have hc : (H.image (fun ws => Transfer.historyTag ws.flatten)).card ≤
      (Finset.product ({seedDepth b 0 n} : Finset ℕ)
        (Finset.Icc (2 * seedDepth b 0 n - seedRadius b 0 n)
          (2 * seedDepth b 0 n + seedRadius b 0 n))).card := Finset.card_le_card hsub
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton,
    one_mul, Nat.card_Icc] at hc
  omega

/-- The sharper linear-in-stage count fits the retained cubic tag budget. -/
theorem seedRadius_tag_budget {b : ℕ} (hb : 200 ≤ b) (n : ℕ) :
    (2 * seedRadius b 0 n + 1 : ℕ) ≤ seedTagBudget b n := by
  have hg0 : 0 ≤ seedTagGrowth := zero_le_one.trans seedTagGrowth_one_le
  have hr := seedRadius_le hb n
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hpow : (b : ℝ) ^ (3 / 5 : ℝ) ≤ b := by
    simpa using Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num : (3 / 5 : ℝ) ≤ 1)
  have hgp : 1 ≤ seedTagGrowth ^ n := one_le_pow₀ seedTagGrowth_one_le
  have hm := mul_le_mul_of_nonneg_right hpow
    (by positivity : (0 : ℝ) ≤ 2 * n * seedTagGrowth ^ n)
  have hlinear : (2 * seedRadius b 0 n + 1 : ℕ) ≤
      (4 * (b : ℝ) + 1) * ((n : ℝ) + 1) * seedTagGrowth ^ n := by
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg b) (pow_nonneg hg0 n),
      mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hg0 n)]
  have hcube : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 3 := by
    nlinarith [sq_nonneg (n : ℝ), pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) 3]
  apply hlinear.trans
  unfold seedTagBudget seedTagConstant
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have h := mul_le_mul_of_nonneg_left hcube (by positivity : (0 : ℝ) ≤ 4 * b + 1)
  have hp : (0 : ℝ) ≤ (4 * b + 1) * ((n : ℝ) + 1) ^ 3 := by positivity
  nlinarith

/-- Every restriction of the actual finite seed family has the same tag budget. -/
theorem seedHistory_tag_budget (H : Finset (List ValuationWord)) {b n : ℕ}
    (hb : 200 ≤ b) (hH : ∀ ws ∈ H, ws ∈ seedBlockLists b 0 n) :
    ((H.image (fun ws => Transfer.historyTag ws.flatten)).card : ℝ) ≤ seedTagBudget b n := by
  have h : ((H.image (fun ws => Transfer.historyTag ws.flatten)).card : ℝ) ≤
      (2 * seedRadius b 0 n + 1 : ℕ) := by exact_mod_cast seedHistory_tag_card H hH
  exact h.trans (seedRadius_tag_budget hb n)

end WordCertDensity.Construction
