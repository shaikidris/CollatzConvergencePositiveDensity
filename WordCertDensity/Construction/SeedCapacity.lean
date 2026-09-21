/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.SeedTags

/-! # Capacity of actual seed histories, including the finite-modulus boundary -/

@[expose] public section

namespace WordCertDensity.Construction

/-- A computable endpoint candidate; physical membership certifies that the floor is exact. -/
def seedHistorySource (root : ℕ) (ws : List ValuationWord) : ℕ :=
  ⌊ValuationWord.inverseEndpoint ws.flatten root⌋₊

/-- On an actual history the endpoint candidate is its exact positive source. -/
theorem seedHistorySource_eq {root source : ℕ} {ws : List ValuationWord}
    (hp : PhysicalHistory ws.flatten root source) : seedHistorySource root ws = source := by
  rw [seedHistorySource, hp.inverseEndpoint_eq, Nat.floor_natCast]

/-- The actual finite history family retains all positive odd physical sources. -/
noncomputable def physicalSeedHistories (b n root : ℕ) : Finset (List ValuationWord) := by
  classical
  exact (seedBlockLists b 0 n).filter fun ws => ∃ source, PhysicalHistory ws.flatten root source

/-- Physical membership certifies the explicit source function, without choosing a new source. -/
theorem mem_physicalSeedHistories (b n root : ℕ) (ws : List ValuationWord) :
    ws ∈ physicalSeedHistories b n root ↔ ws ∈ seedBlockLists b 0 n ∧
      PhysicalHistory ws.flatten root (seedHistorySource root ws) := by
  classical
  simp only [physicalSeedHistories, Finset.mem_filter]
  constructor
  · rintro ⟨hw, source, hp⟩
    exact ⟨hw, by simpa only [seedHistorySource_eq hp] using hp⟩
  · rintro ⟨hw, hp⟩
    exact ⟨hw, _, hp⟩

/-- The retained coefficient pays the offset and the finite-conductor boundary. -/
noncomputable def seedCapacityConstant (b : ℕ) : ℝ :=
  seedTagConstant b * ((2 : ℝ) ^ (b + 1) + 16 ^ b)

/-- The manuscript's actual incoming capacity P_n. -/
noncomputable def seedCapacity (b n : ℕ) : ℝ :=
  seedCapacityConstant b * ((n : ℝ) + 1) ^ 3 * seedTagGrowth ^ n

/-- The tag budget is nonnegative at every stage. -/
theorem seedTagBudget_nonneg (b n : ℕ) : 0 ≤ seedTagBudget b n := by
  unfold seedTagBudget seedTagConstant seedTagGrowth
  positivity

/-- The tag budget is itself included in the larger incoming capacity. -/
theorem seedTagBudget_le_capacity (b n : ℕ) : seedTagBudget b n ≤ seedCapacity b n := by
  have hp : (1 : ℝ) ≤ 2 ^ (b + 1) + 16 ^ b := by
    have h := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := b + 1)
    have h16 : (0 : ℝ) ≤ 16 ^ b := by positivity
    linarith
  have h := mul_le_mul_of_nonneg_left hp (seedTagBudget_nonneg b n)
  simpa only [mul_one, one_mul, seedCapacity, seedCapacityConstant, seedTagBudget, mul_assoc,
    mul_left_comm, mul_comm] using h

/-- The boundary term is bounded at every conductor allowed by the seed construction. -/
theorem seed_boundary_le (b B q : ℕ) (hq : q ≤ 2 * B) :
    (3 : ℝ) ^ q * ((16 : ℝ) ^ b / 16 ^ B) ≤ 16 ^ b := by
  have hp : (3 : ℝ) ^ q ≤ 16 ^ B := by
    calc
      _ ≤ (3 : ℝ) ^ (2 * B) := pow_le_pow_right₀ (by norm_num) hq
      _ = (9 : ℝ) ^ B := by rw [pow_mul]; norm_num
      _ ≤ (16 : ℝ) ^ B := pow_le_pow_left₀ (by norm_num) (by norm_num) B
  have hd : (3 : ℝ) ^ q / 16 ^ B ≤ 1 := (div_le_one (by positivity)).mpr hp
  calc
    _ = ((3 : ℝ) ^ q / 16 ^ B) * 16 ^ b := by ring
    _ ≤ 1 * (16 : ℝ) ^ b := mul_le_mul_of_nonneg_right hd (by positivity)
    _ = _ := one_mul _

/-- Every restriction of actual seed histories has the retained incoming capacity. -/
theorem physicalSeedHistories_capacity (H : Finset (List ValuationWord)) {b n root : ℕ}
    (hb : 32 ^ 5 ≤ b) (hH : H ⊆ physicalSeedHistories b n root)
    (q : ℕ) (hq : q ≤ 2 * seedSize b n) (a : ZMod (3 ^ q)) :
    (3 : ℝ) ^ q * Transfer.historyHistogram H List.flatten (seedHistorySource root) q a ≤
      seedCapacity b n := by
  have member ws (hw : ws ∈ H) := (mem_physicalSeedHistories b n root ws).mp (hH hw)
  have parsed ws (hw : ws ∈ H) := (mem_seedBlockLists b 0 n ws).mp (member ws hw).1
  have hweight ws (hw : ws ∈ H) : Transfer.weight ws.flatten ≤
      (16 : ℝ) ^ b / 16 ^ seedSize b n := by
    have hsQ : ValuationWord.slope ws.flatten ≤ (16 : ℚ) ^ b / 16 ^ seedSize b n := by
      simpa only [seedSize, Nat.zero_add, (parsed ws hw).1] using
        seedBlocks_slope_le hb (parsed ws hw).2
    have hsR : (ValuationWord.slope ws.flatten : ℝ) ≤
        (((16 : ℚ) ^ b / 16 ^ seedSize b n : ℚ) : ℝ) := Rat.cast_le.mpr hsQ
    simpa only [Transfer.weight, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hsR
  have hoff ws (hw : ws ∈ H) : (0 : ℝ) ≤ (ValuationWord.offset ws.flatten : ℝ) ∧
      (ValuationWord.offset ws.flatten : ℝ) ≤ 2 ^ (b + 1) := by
    have hoQ : ValuationWord.offset ws.flatten ≤ (2 : ℚ) ^ (b + 1) := by
      simpa only [seedSize] using (seedBlocks_offset_lt hb (parsed ws hw).2).le
    have hoR : (ValuationWord.offset ws.flatten : ℝ) ≤ (((2 : ℚ) ^ (b + 1) : ℚ) : ℝ) :=
      Rat.cast_le.mpr hoQ
    exact ⟨Rat.cast_nonneg.mpr (ValuationWord.offset_nonneg _),
      by simpa only [Rat.cast_pow, Rat.cast_ofNat] using hoR⟩
  have hc := Transfer.history_capacity H List.flatten (seedHistorySource root) q a
    (T := seedTagBudget b n) (sigma := (16 : ℝ) ^ b / 16 ^ seedSize b n)
    (cmin := 0) (cmax := (2 : ℝ) ^ (b + 1))
    (fun ws hw => (member ws hw).2)
    (by
      intro ws hw vs hv _ he
      have hpv := (member vs hv).2
      rw [← he] at hpv
      exact seedBlocks_unique_of_source (by omega : 0 < b)
        (parsed ws hw).2 (parsed vs hv).2 ((parsed ws hw).1.trans (parsed vs hv).1.symm)
        (member ws hw).2 hpv)
    hweight (by positivity) (by positivity) hoff
    (seedHistory_tag_budget H (by omega : 200 ≤ b) (fun ws hw => (member ws hw).1))
  apply hc.trans
  have hbound := seed_boundary_le b (seedSize b n) q hq
  calc
    _ ≤ seedTagBudget b n * ((2 : ℝ) ^ (b + 1) + 16 ^ b) := by
      simpa only [sub_zero, add_comm] using mul_le_mul_of_nonneg_left
        (add_le_add_left hbound ((2 : ℝ) ^ (b + 1))) (seedTagBudget_nonneg b n)
    _ = seedCapacity b n := by
      unfold seedTagBudget seedCapacity seedCapacityConstant
      ring

end WordCertDensity.Construction
