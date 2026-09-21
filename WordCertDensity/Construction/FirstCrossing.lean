/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.Stopping
public import WordCertDensity.Transfer.AffineMap
public import WordCertDensity.Words.Parsing
public import WordCertDensity.Analytic.HeadScalars
public import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite first-crossing blocks

The precision cutoff is strict in total valuation. Enumeration uses positive
integer compositions, and the first-crossing test uses exact rational slopes.
Its logarithmic characterization is proved separately, without evaluating logs.
-/

@[expose] public section

namespace WordCertDensity.Construction

/-- A positive composition as the existing positive-valuation word type. -/
def compositionWord {n : ℕ} (c : Composition n) : ValuationWord :=
  c.blocks.attach.map fun k => ⟨k.val, c.blocks_pos k.property⟩

private theorem compositionWord_values {n : ℕ} (c : Composition n) :
    (compositionWord c).map (fun k : ℕ+ => (k : ℕ)) = c.blocks := by
  exact (List.map_map (l := c.blocks.attach)
    (f := fun k => (⟨k.val, c.blocks_pos k.property⟩ : ℕ+))
    (g := fun k : ℕ+ => (k : ℕ))).trans (List.attach_map_subtype_val _)

private def wordComposition (w : ValuationWord) : Composition w.total where
  blocks := w.map (fun k : ℕ+ => (k : ℕ))
  blocks_pos := by
    intro k hk
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hk
    exact j.property
  blocks_sum := rfl

private theorem compositionWord_wordComposition (w : ValuationWord) :
    compositionWord (wordComposition w) = w := by
  apply List.map_injective_iff.mpr (show Function.Injective (fun k : ℕ+ => (k : ℕ))
    from Subtype.val_injective)
  simpa only [wordComposition] using compositionWord_values (wordComposition w)

/-- All positive valuation words of one exact total, enumerated by compositions. -/
def wordsAtTotal (n : ℕ) : Finset ValuationWord :=
  Finset.univ.image (compositionWord (n := n))

/-- The enumeration contains exactly the words of its stated total. -/
theorem mem_wordsAtTotal (w : ValuationWord) (n : ℕ) :
    w ∈ wordsAtTotal n ↔ w.total = n := by
  constructor
  · intro hw
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hw
    simp only [ValuationWord.total, compositionWord_values, Composition.blocks_sum]
  · intro hw
    subst n
    exact Finset.mem_image.mpr
      ⟨wordComposition w, Finset.mem_univ _, compositionWord_wordComposition w⟩

/-- The finite set of all words below the strict total-valuation precision. -/
def wordsBelow (E : ℕ) : Finset ValuationWord :=
  (Finset.range E).biUnion wordsAtTotal

/-- No word or valuation below the precision is omitted by the finite enumeration. -/
theorem mem_wordsBelow (w : ValuationWord) (E : ℕ) :
    w ∈ wordsBelow E ↔ w.total < E := by
  simp only [wordsBelow, Finset.mem_biUnion, Finset.mem_range, mem_wordsAtTotal]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact hn
  · intro h
    exact ⟨w.total, h, rfl⟩

/-- Positive letters force the depth to be no larger than the total valuation. -/
theorem word_length_le_total (w : ValuationWord) : w.length ≤ w.total := by
  have h := (wordComposition w).length_le
  simpa [Composition.length, wordComposition] using h

/-- The first slope at most one eighth occurs at the end of the word. -/
def FirstCrossing (w : ValuationWord) : Prop :=
  w.slope ≤ 1 / 8 ∧ ∀ i : Fin w.length, 1 / 8 < ValuationWord.slope (w.take i)

instance (w : ValuationWord) : Decidable (FirstCrossing w) :=
  inferInstanceAs (Decidable (w.slope ≤ 1 / 8 ∧
    ∀ i : Fin w.length, 1 / 8 < ValuationWord.slope (w.take i)))

/-- The empty word has slope one and cannot be a first-crossing block. -/
theorem firstCrossing_nonempty {w : ValuationWord} (hw : FirstCrossing w) : w ≠ [] := by
  intro he
  subst w
  norm_num [FirstCrossing, ValuationWord.slope, ValuationWord.total] at hw

/-- Two first crossings cannot properly extend one another. -/
theorem firstCrossing_prefix_eq {u v : ValuationWord}
    (hu : FirstCrossing u) (hv : FirstCrossing v) (hp : u <+: v) : u = v := by
  by_cases he : u.length = v.length
  · exact hp.eq_of_length he
  · have hlt : u.length < v.length := lt_of_le_of_ne hp.length_le he
    have hc := hv.2 ⟨u.length, hlt⟩
    have ht : v.take u.length = u := (List.prefix_iff_eq_take.mp hp).symm
    rw [ht] at hc
    exact (not_lt_of_ge hu.1 hc).elim

/-- Displacement is the stopped valuation less the binary ternary displacement. -/
noncomputable def displacement (w : ValuationWord) : ℝ :=
  (w.total : ℝ) - Head.logRatio * w.length

/-- The logarithm of the physical slope is the negative binary displacement. -/
theorem log_weight_eq (w : ValuationWord) :
    Real.log (Transfer.weight w) = -displacement w * Real.log 2 := by
  rw [Transfer.weight_eq, Real.log_div (by positivity) (by positivity), Real.log_pow,
    Real.log_pow]
  unfold displacement Head.logRatio
  field_simp
  ring

/-- The exact rational stopping threshold is precisely displacement at least three. -/
theorem slope_le_eighth_iff (w : ValuationWord) :
    w.slope ≤ (1 / 8 : ℚ) ↔ 3 ≤ displacement w := by
  have hcast : w.slope ≤ (1 / 8 : ℚ) ↔ Transfer.weight w ≤ (1 / 8 : ℝ) := by
    have hc : ((w.slope : ℝ) ≤ ((1 / 8 : ℚ) : ℝ)) ↔ w.slope ≤ 1 / 8 :=
      Rat.cast_le
    simpa only [Transfer.weight, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc.symm
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : Real.log (1 / 8 : ℝ) = -3 * Real.log 2 := by
    have hn : (1 / 8 : ℝ) = (2 ^ 3)⁻¹ := by norm_num
    rw [hn, Real.log_inv, Real.log_pow]
    norm_num
  rw [hcast, ← Real.log_le_log_iff (Transfer.weight_pos w) (by norm_num),
    log_weight_eq, he, mul_le_mul_iff_left₀ hl]
  constructor <;> intro h <;> linarith

/-- The rational first-crossing rule equals the manuscript's displacement rule. -/
theorem firstCrossing_iff (w : ValuationWord) : FirstCrossing w ↔
    3 ≤ displacement w ∧ ∀ i : Fin w.length, displacement (w.take i) < 3 := by
  constructor
  · intro hw
    refine ⟨(slope_le_eighth_iff w).mp hw.1, fun i => ?_⟩
    exact lt_of_not_ge (fun hi => not_le_of_gt (hw.2 i)
      ((slope_le_eighth_iff _).mpr hi))
  · intro hw
    refine ⟨(slope_le_eighth_iff w).mpr hw.1, fun i => ?_⟩
    exact lt_of_not_ge (fun hi => not_le_of_gt (hw.2 i)
      ((slope_le_eighth_iff _).mp hi))

/-- Any word reaching the slope threshold contains a genuine first-crossing prefix. -/
theorem exists_firstCrossing_prefix (w : ValuationWord) (hw : w.slope ≤ 1 / 8) :
    ∃ u : ValuationWord, u <+: w ∧ FirstCrossing u := by
  have hex : ∃ i : ℕ, i ≤ w.length ∧ ValuationWord.slope (w.take i) ≤ 1 / 8 :=
    ⟨w.length, le_refl _, by simpa using hw⟩
  let i := Nat.find hex
  have hi := Nat.find_spec hex
  refine ⟨w.take i, List.take_prefix _ _, hi.2, ?_⟩
  intro j
  have hj : (j : ℕ) < i := by
    have hj' : (j : ℕ) < min i w.length := by
      simpa only [List.length_take] using j.isLt
    exact hj'.trans_le (Nat.min_le_left _ _)
  rw [List.take_take, Nat.min_eq_left hj.le]
  exact lt_of_not_ge (fun h => Nat.find_min hex hj ⟨hj.le.trans hi.1, h⟩)

/-- The manuscript's truncated first-crossing family V(E), with a computable predicate. -/
def stoppedWords (E : ℕ) : Finset ValuationWord :=
  (wordsBelow E).filter FirstCrossing

/-- The stopped family has exactly the first-crossing and strict precision conditions. -/
theorem mem_stoppedWords (w : ValuationWord) (E : ℕ) :
    w ∈ stoppedWords E ↔ FirstCrossing w ∧ w.total < E := by
  simp only [stoppedWords, Finset.mem_filter, mem_wordsBelow, and_comm]

/-- Every finite stopped family is prefix-free. -/
theorem stoppedWords_prefixFree (E : ℕ) :
    (stoppedWords E : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v) := by
  intro u hu v hv hne hp
  exact hne (firstCrossing_prefix_eq (mem_stoppedWords u E |>.mp hu).1
    (mem_stoppedWords v E |>.mp hv).1 hp)

/-- Increasing the precision only adds original first-crossing words. -/
theorem stoppedWords_mono {E F : ℕ} (hEF : E ≤ F) : stoppedWords E ⊆ stoppedWords F := by
  intro w hw
  rw [mem_stoppedWords] at hw ⊢
  exact ⟨hw.1, hw.2.trans_le hEF⟩

/-- Every admitted block has slope at most the fixed contraction one eighth. -/
theorem stoppedWords_weight_le {w : ValuationWord} {E : ℕ} (hw : w ∈ stoppedWords E) :
    Transfer.weight w ≤ 1 / 8 := by
  have h := (mem_stoppedWords w E |>.mp hw).1.1
  have hc : (w.slope : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) := Rat.cast_le.mpr h
  simpa only [Transfer.weight, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc

/-- The strict total precision also bounds the block depth. -/
theorem stoppedWords_length_lt {w : ValuationWord} {E : ℕ} (hw : w ∈ stoppedWords E) :
    w.length < E := (word_length_le_total w).trans_lt (mem_stoppedWords w E |>.mp hw).2

/-- These concrete families instantiate the existing unique-parsing block rule. -/
def stoppedBlockRule (precision : ℕ → ℕ) : BlockRule where
  allowed stage w := w ∈ stoppedWords (precision stage)
  nonempty stage w hw := firstCrossing_nonempty
    (mem_stoppedWords w (precision stage) |>.mp hw).1
  prefix_eq stage u v hu hv hp := firstCrossing_prefix_eq
    (mem_stoppedWords u (precision stage) |>.mp hu).1
    (mem_stoppedWords v (precision stage) |>.mp hv).1 hp

/-- The original truncated stopping mass is between zero and one. -/
theorem stoppedWords_mass_bounds (E : ℕ) :
    0 ≤ Reference.stoppingMass (stoppedWords E) ∧
      Reference.stoppingMass (stoppedWords E) ≤ 1 :=
  ⟨Reference.stoppingMass_nonneg _,
    Reference.stoppingMass_le_one _ (stoppedWords_prefixFree E)⟩

/-- The finite family mass is its actual iid prefix-selection probability. -/
theorem stoppedWords_probability (E n : ℕ) (hEn : E ≤ n) :
    Gated.probability (Reference.wordPMF n) (Reference.prefixFamilyEvent (stoppedWords E)) =
      Reference.stoppingMass (stoppedWords E) := by
  apply Reference.prefixFamily_probability _ _ (stoppedWords_prefixFree E)
  intro w hw
  exact (stoppedWords_length_lt hw).le.trans hEn

end WordCertDensity.Construction
