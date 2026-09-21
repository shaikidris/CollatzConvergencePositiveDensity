/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.SeedGeometry
public import WordCertDensity.Words.ParsingPrefix
public import WordCertDensity.Roots.Basins

/-!
# Cumulative seed histories

Actual words retain their fixed stage cuts. Height and contraction telescope
in the original order, and the paid half-slope bounds the entire offset.
All statements allow a starting stage and the empty history.
-/

@[expose] public section

namespace WordCertDensity

namespace PhysicalHistory

/-- Splitting an actual inverse word exposes its actual intermediate endpoint. -/
theorem append_split {u v : ValuationWord} {root source : ℕ}
    (h : PhysicalHistory (u ++ v) root source) :
    ∃ middle, PhysicalHistory u root middle ∧ PhysicalHistory v middle source := by
  induction u generalizing root with
  | nil => exact ⟨root, .nil root h.root_pos h.root_odd, h⟩
  | cons k u ih =>
    cases h with
    | cons hpos hodd hblock htail =>
      obtain ⟨middle, hu, hv⟩ := ih htail
      exact ⟨middle, .cons hpos hodd hblock hu, hv⟩

end PhysicalHistory

namespace Construction

/-- Literal seed blocks at consecutive stages, before physical compatibility is imposed. -/
def SeedBlocks (b : ℕ) : ℕ → List ValuationWord → Prop
  | _, [] => True
  | t, w :: ws => w ∈ seedWords (seedSize b t) ∧ SeedBlocks b (t + 1) ws

/-- Positive initial depth makes the seed a deterministic nonempty block rule. -/
noncomputable def seedBlockRule (b : ℕ) (hb : 0 < b) : BlockRule where
  allowed t w := w ∈ seedWords (seedSize b t)
  nonempty t w hw := by
    have hlen := ((mem_seedWords w (seedSize b t)).mp hw).1
    have hs := seedSize_ge b t
    intro he
    subst w
    simp only [List.length_nil] at hlen
    omega
  prefix_eq t u v hu hv hp := by
    have hlen := ((mem_seedWords u (seedSize b t)).mp hu).1.trans
      ((mem_seedWords v (seedSize b t)).mp hv).1.symm
    exact hp.eq_of_length hlen

/-- The literal seed predicate supplies the existing deterministic parser. -/
theorem seedBlocks_parses {b t : ℕ} (hb : 0 < b) {ws : List ValuationWord}
    (h : SeedBlocks b t ws) : (seedBlockRule b hb).Parses t ws := by
  induction ws generalizing t with
  | nil => trivial
  | cons w ws ih => exact ⟨h.1, ih h.2⟩

/-- The full word uniquely determines the seed cuts at a fixed starting stage. -/
theorem seedBlocks_flatten_injective {b t : ℕ} (hb : 0 < b)
    {ws vs : List ValuationWord} (hw : SeedBlocks b t ws) (hv : SeedBlocks b t vs)
    (he : ws.flatten = vs.flatten) : ws = vs :=
  BlockRule.flatten_injective (seedBlocks_parses hb hw) (seedBlocks_parses hb hv) he

/-- The finite list family retains exactly one selected word at each stage. -/
noncomputable def seedBlockLists (b : ℕ) : ℕ → ℕ → Finset (List ValuationWord)
  | _, 0 => {[]}
  | t, n + 1 => ((seedWords (seedSize b t)).product
      (seedBlockLists b (t + 1) n)).image (fun p => p.1 :: p.2)

/-- Enumeration matches the literal schedule and its exact number of blocks. -/
theorem mem_seedBlockLists (b t n : ℕ) (ws : List ValuationWord) :
    ws ∈ seedBlockLists b t n ↔ ws.length = n ∧ SeedBlocks b t ws := by
  induction n generalizing t ws with
  | zero => cases ws <;> simp [seedBlockLists, SeedBlocks]
  | succ n ih =>
    cases ws with
    | nil => simp [seedBlockLists]
    | cons w ws =>
      constructor
      · intro h
        obtain ⟨⟨v, vs⟩, hm, he⟩ := Finset.mem_image.mp h
        obtain ⟨rfl, rfl⟩ := List.cons.inj he
        obtain ⟨hw, ht⟩ := Finset.mem_product.mp hm
        obtain ⟨hlen, hs⟩ := (ih (t + 1) _).mp ht
        exact ⟨by simpa using hlen, hw, hs⟩
      · rintro ⟨hlen, hw, hs⟩
        exact Finset.mem_image.mpr ⟨(w, ws), Finset.mem_product.mpr
          ⟨hw, (ih (t + 1) ws).mpr ⟨by simpa using hlen, hs⟩⟩, rfl⟩

/-- The finite complete-word family identifies descriptions with identical words. -/
noncomputable def seedHistoryWords (b t n : ℕ) : Finset ValuationWord :=
  (seedBlockLists b t n).image List.flatten

/-- A complete word belongs exactly when its prescribed seed cuts exist. -/
theorem mem_seedHistoryWords (b t n : ℕ) (w : ValuationWord) :
    w ∈ seedHistoryWords b t n ↔
      ∃ ws : List ValuationWord, ws.length = n ∧ SeedBlocks b t ws ∧ ws.flatten = w := by
  simp only [seedHistoryWords, Finset.mem_image, mem_seedBlockLists, and_assoc]

/-- The exact cumulative depth of a prescribed number of seed blocks. -/
def seedDepth (b t n : ℕ) : ℕ := ∑ j ∈ Finset.range n, seedSize b (t + j)

/-- The sum of the actual ceiling radii is the cumulative valuation radius. -/
noncomputable def seedRadius (b t n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, seedWidth (seedSize b (t + j))

/-- Removing the first block leaves the depth sum at the next stage. -/
theorem seedDepth_succ (b t n : ℕ) :
    seedDepth b t (n + 1) = seedSize b t + seedDepth b (t + 1) n := by
  simp [seedDepth, Finset.sum_range_succ', Nat.add_comm, Nat.add_left_comm]

/-- Removing the first block leaves the radius sum at the next stage. -/
theorem seedRadius_succ (b t n : ℕ) :
    seedRadius b t (n + 1) = seedWidth (seedSize b t) + seedRadius b (t + 1) n := by
  simp [seedRadius, Finset.sum_range_succ', Nat.add_comm, Nat.add_left_comm]

/-- Every seed history has exactly the cumulative depth, independently of its valuations. -/
theorem seedBlocks_depth {b t : ℕ} {ws : List ValuationWord} (h : SeedBlocks b t ws) :
    ws.flatten.length = seedDepth b t ws.length := by
  induction ws generalizing t with
  | nil => simp [seedDepth]
  | cons w ws ih =>
    rw [List.flatten_cons, List.length_append, List.length_cons, seedDepth_succ,
      ((mem_seedWords w (seedSize b t)).mp h.1).1, ih h.2]

/-- Every word in the finite complete family has the same exact depth. -/
theorem seedHistoryWords_depth {b t n : ℕ} {w : ValuationWord}
    (h : w ∈ seedHistoryWords b t n) : w.length = seedDepth b t n := by
  obtain ⟨ws, hlen, hs, rfl⟩ := (mem_seedHistoryWords b t n w).mp h
  simpa only [hlen] using seedBlocks_depth hs

/-- The fixed total depth makes the complete seed family prefix-free. -/
theorem seedHistoryWords_prefixFree (b t n : ℕ) :
    (seedHistoryWords b t n : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v) := by
  intro u hu v hv hne hp
  exact hne (hp.eq_of_length ((seedHistoryWords_depth hu).trans (seedHistoryWords_depth hv).symm))

/-- At a fixed block count, an actual source determines its complete seed history. -/
theorem seedBlocks_unique_of_source {b t root source : ℕ} (hb : 0 < b)
    {ws vs : List ValuationWord} (hw : SeedBlocks b t ws) (hv : SeedBlocks b t vs)
    (hlen : ws.length = vs.length)
    (hp : PhysicalHistory ws.flatten root source) (hq : PhysicalHistory vs.flatten root source) :
    ws = vs := by
  apply seedBlocks_flatten_injective hb hw hv
  apply hp.word_eq_of_length_eq hq
  rw [seedBlocks_depth hw, seedBlocks_depth hv, hlen]

/-- Both signed sides of the total-valuation window survive concatenation. -/
theorem seedBlocks_total_bounds {b t : ℕ} {ws : List ValuationWord} (h : SeedBlocks b t ws) :
    2 * seedDepth b t ws.length ≤ (ValuationWord.total ws.flatten) + seedRadius b t ws.length ∧
      (ValuationWord.total ws.flatten) ≤ 2 * seedDepth b t ws.length + seedRadius b t ws.length := by
  induction ws generalizing t with
  | nil => simp [seedDepth, seedRadius, ValuationWord.total]
  | cons w ws ih =>
    have hw := (mem_seedWindow_bounds w (seedSize b t) (seedWidth (seedSize b t))).mp h.1
    have ht := ih h.2
    simp only [List.flatten_cons, ValuationWord.total_append, List.length_cons,
      seedDepth_succ, seedRadius_succ]
    omega

/-- Actual histories telescope the seed height through every intermediate parent. -/
theorem seedBlocks_source_height {b t root source : ℕ} (hb : 32 ^ 5 ≤ b)
    {ws : List ValuationWord} (h : SeedBlocks b t ws)
    (hroot : 16 ^ seedSize b t ≤ root) (hp : PhysicalHistory ws.flatten root source) :
    16 ^ seedSize b (t + ws.length) ≤ source := by
  induction ws generalizing t root with
  | nil =>
    cases hp
    simpa using hroot
  | cons w ws ih =>
    obtain ⟨middle, hw, ht⟩ := hp.append_split
    have hb' := hb.trans (seedSize_ge b t)
    have hm := seedWords_source_height hb' hroot h.1 hw
    have htail := ih h.2 hm ht
    simpa only [List.length_cons, Nat.add_right_comm, Nat.add_assoc, seedSize] using htail

/-- The product form of cumulative contraction avoids any truncated negative exponent. -/
theorem seedBlocks_slope_scaled {b t : ℕ} (hb : 32 ^ 5 ≤ b)
    {ws : List ValuationWord} (h : SeedBlocks b t ws) :
    (ValuationWord.slope ws.flatten) * (16 : ℚ) ^ seedSize b (t + ws.length) ≤ 16 ^ seedSize b t := by
  induction ws generalizing t with
  | nil => simp [ValuationWord.slope, ValuationWord.total]
  | cons w ws ih =>
    have hs := seedWords_slope_le (hb.trans (seedSize_ge b t)) h.1
    have ht := ih h.2
    have hp : (16 : ℚ) ^ seedSize b (t + 1) =
        16 ^ seedSize b t * 16 ^ (seedSize b t / 100) := by rw [seedSize, pow_add]
    have he : t + (w :: ws).length = (t + 1) + ws.length := by simp; omega
    rw [he, List.flatten_cons, ValuationWord.slope_append, mul_assoc]
    calc
      _ ≤ w.slope * 16 ^ seedSize b (t + 1) :=
        mul_le_mul_of_nonneg_left ht w.slope_pos.le
      _ ≤ ((16 : ℚ) ^ (seedSize b t / 100))⁻¹ * 16 ^ seedSize b (t + 1) :=
        mul_le_mul_of_nonneg_right hs (by positivity)
      _ = 16 ^ seedSize b t := by rw [hp]; field_simp

/-- The exact ratio is the manuscript's cumulative negative-power slope bound. -/
theorem seedBlocks_slope_le {b t : ℕ} (hb : 32 ^ 5 ≤ b)
    {ws : List ValuationWord} (h : SeedBlocks b t ws) :
    (ValuationWord.slope ws.flatten) ≤ (16 : ℚ) ^ seedSize b t / 16 ^ seedSize b (t + ws.length) :=
  (le_div_iff₀ (by positivity)).mpr (seedBlocks_slope_scaled hb h)

/-- The paid half-slope controls the entire remaining offset at each starting stage. -/
theorem seedBlocks_offset_lt {b t : ℕ} (hb : 32 ^ 5 ≤ b)
    {ws : List ValuationWord} (h : SeedBlocks b t ws) :
    (ValuationWord.offset ws.flatten) < (2 : ℚ) ^ (seedSize b t + 1) := by
  induction ws generalizing t with
  | nil => simp only [List.flatten_nil, ValuationWord.offset]; positivity
  | cons w ws ih =>
    have hs := (seedWords_slope_half (hb.trans (seedSize_ge b t)) h.1).le
    have ho := seedWords_offset_lt h.1
    have ht := (ih h.2).le
    have hpower : (2 : ℚ) ^ (seedSize b (t + 1) + 1) ≤
        (2 * 16 ^ (seedSize b t / 100)) * 2 ^ seedSize b t := by
      have hd := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2)
        (by norm_num : (2 : ℚ) ≤ 16) (seedSize b t / 100)
      rw [seedSize, pow_add, pow_add]
      norm_num only [pow_one]
      nlinarith [mul_le_mul_of_nonneg_right hd (by positivity : (0 : ℚ) ≤ 2 ^ seedSize b t)]
    have htail : w.slope * (ValuationWord.offset ws.flatten) ≤ (2 : ℚ) ^ seedSize b t := by
      calc
        _ ≤ (1 / (2 * (16 : ℚ) ^ (seedSize b t / 100))) *
            2 ^ (seedSize b (t + 1) + 1) :=
          mul_le_mul hs ht (ValuationWord.offset_nonneg _) (by positivity)
        _ ≤ (1 / (2 * (16 : ℚ) ^ (seedSize b t / 100))) *
            ((2 * 16 ^ (seedSize b t / 100)) * 2 ^ seedSize b t) :=
          mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = _ := by field_simp
    rw [List.flatten_cons, ValuationWord.offset_append, pow_succ]
    linarith

/-- At stage zero every compatible full word has a unique actual endpoint at the current height. -/
theorem seedBlocks_realizes {b root q : ℕ} (hb : 32 ^ 5 ≤ b)
    {ws : List ValuationWord} (h : SeedBlocks b 0 ws)
    (hroot : 16 ^ b ≤ root) (hodd : Odd root) (hq : seedDepth b 0 ws.length ≤ q)
    (hc : (root : ZMod (3 ^ q)) ∈ Set.range (Transfer.wordMap ws.flatten q)) :
    ∃! source : ℕ, PhysicalHistory ws.flatten root source ∧ 16 ^ seedSize b ws.length ≤ source := by
  have hoff : (ValuationWord.offset ws.flatten) < (root : ℚ) := by
    have ho := seedBlocks_offset_lt hb h
    have hg : (2 : ℚ) ^ (b + 1) ≤ 16 ^ b := by
      calc
        _ ≤ (2 : ℚ) ^ (4 * b) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = _ := by rw [pow_mul]; norm_num
    have hr : (16 : ℚ) ^ b ≤ root := by exact_mod_cast hroot
    simpa only [seedSize] using ho.trans_le (hg.trans hr)
  obtain ⟨source, hp⟩ := (Transfer.mem_range_wordMap_iff_physical ws.flatten
    ((seedBlocks_depth h).trans_le hq) root hodd hoff).mp hc
  have hs := seedBlocks_source_height hb h (by simpa [seedSize] using hroot) hp
  exact ⟨source, ⟨hp, by simpa using hs⟩, fun _ hk => hk.1.source_unique hp⟩

end Construction
end WordCertDensity
