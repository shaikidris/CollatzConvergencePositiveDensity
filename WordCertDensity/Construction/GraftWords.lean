/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ScheduledMass

/-! # Fixed-precision stopped words for the graft transition

Every component uses the same precision E. The finite enumeration preserves
unique block cuts and the original stopped-copy probability, including after
an arbitrary word gate. No surviving mass is used as a normalization.
-/

namespace WordCertDensity.Construction

open scoped Classical ENNReal

/-- The transition's finite lists of n stopped blocks at one common precision. -/
def graftBlockLists (E : ℕ) : ℕ → Finset (List ValuationWord)
  | 0 => {[]}
  | n + 1 => ((stoppedWords E).product (graftBlockLists E n)).image (fun p => p.1 :: p.2)

/-- The enumeration retains exactly the prescribed count and every precision constraint. -/
theorem mem_graftBlockLists (E n : ℕ) (ws : List ValuationWord) :
    ws ∈ graftBlockLists E n ↔ ws.length = n ∧ ∀ w ∈ ws, w ∈ stoppedWords E := by
  induction n generalizing ws with
  | zero => cases ws <;> simp [graftBlockLists]
  | succ n ih =>
      cases ws with
      | nil => simp [graftBlockLists]
      | cons w ws =>
          constructor
          · intro h
            obtain ⟨⟨v, vs⟩, hmem, he⟩ := Finset.mem_image.mp h
            obtain ⟨rfl, rfl⟩ := List.cons.inj he
            obtain ⟨hw, hws⟩ := Finset.mem_product.mp hmem
            obtain ⟨hlen, hp⟩ := (ih vs).mp hws
            exact ⟨by simpa using hlen, List.forall_mem_cons.mpr ⟨hw, hp⟩⟩
          · rintro ⟨hlen, hp⟩
            obtain ⟨hw, hws⟩ := List.forall_mem_cons.mp hp
            exact Finset.mem_image.mpr ⟨(w, ws), Finset.mem_product.mpr
              ⟨hw, (ih ws).mpr ⟨by simpa using hlen, hws⟩⟩, rfl⟩

private theorem graftBlocks_parse {E : ℕ} {ws : List ValuationWord}
    (hw : ∀ w ∈ ws, w ∈ stoppedWords E) (stage : ℕ) :
    (stoppedBlockRule (fun _ => E)).Parses stage ws := by
  induction ws generalizing stage with
  | nil => trivial
  | cons w ws ih =>
      exact ⟨hw w (by simp), ih (fun v hv => hw v (by simp [hv])) (stage + 1)⟩

/-- Fixed-precision block lists have unique cuts after concatenation. -/
theorem graftBlockLists_flatten_injective (E n : ℕ) :
    Set.InjOn List.flatten (graftBlockLists E n : Set (List ValuationWord)) := by
  intro us hu vs hv he
  exact BlockRule.flatten_injective
    (graftBlocks_parse ((mem_graftBlockLists E n us).mp hu).2 0)
    (graftBlocks_parse ((mem_graftBlockLists E n vs).mp hv).2 0) he

/-- The transition concatenations before applying the two corridors. -/
def graftWords (E n : ℕ) : Finset ValuationWord :=
  (graftBlockLists E n).image List.flatten

/-- Word membership supplies the actual retained stopped-block list. -/
theorem mem_graftWords (E n : ℕ) (w : ValuationWord) :
    w ∈ graftWords E n ↔ ∃ ws : List ValuationWord,
      ws.length = n ∧ (∀ v ∈ ws, v ∈ stoppedWords E) ∧ ws.flatten = w := by
  simp only [graftWords, Finset.mem_image, mem_graftBlockLists, and_assoc]

/-- The common block count and unique first-crossing cuts give prefix-freeness. -/
theorem graftWords_prefixFree (E n : ℕ) :
    (graftWords E n : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v) := by
  intro u hu v hv hne hp
  obtain ⟨us, hul, hup, rfl⟩ := (mem_graftWords E n u).mp hu
  obtain ⟨vs, hvl, hvp, rfl⟩ := (mem_graftWords E n v).mp hv
  exact hne (congrArg List.flatten
    (BlockRule.eq_of_flatten_prefix_of_length_eq
      (graftBlocks_parse hup 0) (graftBlocks_parse hvp 0) hp (hul.trans hvl.symm)))

/-- Original finite concatenation mass remains in the probability interval. -/
theorem graftWords_mass_bounds (E n : ℕ) :
    0 ≤ Reference.stoppingMass (graftWords E n) ∧
      Reference.stoppingMass (graftWords E n) ≤ 1 :=
  ⟨Reference.stoppingMass_nonneg _, Reference.stoppingMass_le_one _ (graftWords_prefixFree E n)⟩

private theorem graftBlocks_total_le {E : ℕ} {ws : List ValuationWord}
    (hw : ∀ w ∈ ws, w ∈ stoppedWords E) :
    ValuationWord.total ws.flatten ≤ ws.length * (E - 1) := by
  induction ws with
  | nil => simp [ValuationWord.total]
  | cons w ws ih =>
      have hv := ((mem_stoppedWords w E).mp (hw w (by simp))).2
      have ht := ih (fun v hv => hw v (by simp [hv]))
      simp only [List.flatten_cons, ValuationWord.total_append, List.length_cons, Nat.add_mul,
        Nat.one_mul]
      omega

/-- The strict total cutoffs add to the literal transition valuation budget. -/
theorem graftWords_total_le {E n : ℕ} {w : ValuationWord} (hw : w ∈ graftWords E n) :
    w.total ≤ n * (E - 1) := by
  obtain ⟨ws, hlen, hws, rfl⟩ := (mem_graftWords E n w).mp hw
  simpa only [hlen] using graftBlocks_total_le hws

/-- The actual word depth is bounded by the same integer budget. -/
theorem graftWords_depth_le {E n : ℕ} {w : ValuationWord} (hw : w ∈ graftWords E n) :
    w.length ≤ n * (E - 1) :=
  (word_length_le_total w).trans (graftWords_total_le hw)

private theorem graftBlocks_weight_le {E : ℕ} {ws : List ValuationWord}
    (hw : ∀ w ∈ ws, w ∈ stoppedWords E) :
    Transfer.weight ws.flatten ≤ (1 / 8 : ℝ) ^ ws.length := by
  induction ws with
  | nil => simp [Transfer.weight, ValuationWord.slope, ValuationWord.total]
  | cons w ws ih =>
      have ht := ih (fun v hv => hw v (by simp [hv]))
      have h := mul_le_mul (stoppedWords_weight_le (hw w (by simp))) ht
        (Transfer.weight_pos ws.flatten).le (by norm_num : (0 : ℝ) ≤ 1 / 8)
      simpa only [List.flatten_cons, List.length_cons, Transfer.weight,
        ValuationWord.slope_append, Rat.cast_mul, pow_succ, mul_comm] using h

/-- Every stopped component pays the full contraction needed by the hybrid history. -/
theorem graftWords_weight_le {E n : ℕ} {w : ValuationWord} (hw : w ∈ graftWords E n) :
    Transfer.weight w ≤ (1 / 8 : ℝ) ^ n := by
  obtain ⟨ws, hlen, hws, rfl⟩ := (mem_graftWords E n w).mp hw
  simpa only [hlen] using graftBlocks_weight_le hws

private theorem graftMass_image {E n : ℕ} {V : Finset (List ValuationWord)}
    (hV : V ⊆ graftBlockLists E n) :
    Reference.stoppingMass (V.image List.flatten) =
      ∑ ws ∈ V, 1 / (2 : ℝ) ^ (ValuationWord.total ws.flatten) := by
  unfold Reference.stoppingMass
  rw [Finset.sum_image]
  exact fun us hu vs hv he => graftBlockLists_flatten_injective E n (hV hu) (hV hv) he

private theorem graftLists_probability {E n : ℕ} {V : Finset (List ValuationWord)}
    (hV : V ⊆ graftBlockLists E n) :
    Gated.probability (stoppedCopiesPMF n) (fun ws => ws ∈ V) =
      Reference.stoppingMass (V.image List.flatten) := by
  have hfinite : Gated.probability (stoppedCopiesPMF n) (fun ws => ws ∈ V) =
      ∑ ws ∈ V, (stoppedCopiesPMF n ws).toReal := by
    unfold Gated.probability
    rw [tsum_eq_sum (s := V) (fun a ha => by simp [ha])]
    rw [ENNReal.toReal_sum (fun a ha => by rw [if_pos ha]; exact PMF.apply_ne_top _ _)]
    apply Finset.sum_congr rfl
    intro a ha
    rw [if_pos ha]
  rw [hfinite, graftMass_image hV]
  apply Finset.sum_congr rfl
  intro ws hws
  obtain ⟨hlen, hp⟩ := (mem_graftBlockLists E n ws).mp (hV hws)
  have hs := stoppedCopiesPMF_toReal ws
    (fun v hv => ((mem_stoppedWords v E).mp (hp v hv)).1)
  simpa only [hlen] using hs

/-- Any word gate retains exactly its original probability under complete stopped copies. -/
theorem graftWords_gate_probability (E n : ℕ) (G : ValuationWord → Prop) :
    Gated.probability (stoppedCopiesPMF n)
      (fun ws => (∀ w ∈ ws, w ∈ stoppedWords E) ∧ G ws.flatten) =
      Reference.stoppingMass ((graftWords E n).filter G) := by
  let V := (graftBlockLists E n).filter (fun ws => G ws.flatten)
  have he := Gated.probability_congr_on_support (stoppedCopiesPMF n)
    (fun ws => (∀ w ∈ ws, w ∈ stoppedWords E) ∧ G ws.flatten) (fun ws => ws ∈ V)
    (fun ws hp => by
      have hlen := ((stoppedCopiesPMF_mem_support_iff n ws).mp
        ((PMF.mem_support_iff _ _).mpr hp)).1
      simp only [V, Finset.mem_filter, mem_graftBlockLists, hlen, true_and])
  rw [he, graftLists_probability (Finset.filter_subset _ _)]
  congr 1
  ext w
  simp only [graftWords, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨ws, ⟨hws, hG⟩, rfl⟩
    exact ⟨⟨ws, hws, rfl⟩, hG⟩
  · rintro ⟨⟨ws, hws, rfl⟩, hG⟩
    exact ⟨ws, ⟨hws, hG⟩, rfl⟩

/-- Original probability of all precision constraints equals the finite unconditioned mass. -/
theorem graftWords_probability (E n : ℕ) :
    Gated.probability (stoppedCopiesPMF n) (fun ws => ∀ w ∈ ws, w ∈ stoppedWords E) =
      Reference.stoppingMass (graftWords E n) := by
  simpa using graftWords_gate_probability E n (fun _ => True)

private theorem graftMass_sum (E n : ℕ) :
    Reference.stoppingMass (graftWords E n) =
      ∑ ws ∈ graftBlockLists E n, 1 / (2 : ℝ) ^ (ValuationWord.total ws.flatten) :=
  graftMass_image (Finset.Subset.refl _)

/-- The original mass factors at the next stopped block without renormalization. -/
theorem graftWords_mass_succ (E n : ℕ) :
    Reference.stoppingMass (graftWords E (n + 1)) =
      Reference.stoppingMass (stoppedWords E) * Reference.stoppingMass (graftWords E n) := by
  rw [graftMass_sum, graftBlockLists, Finset.sum_image]
  · rw [Finset.product_eq_sprod, Finset.sum_product]
    simp_rw [List.flatten_cons, ValuationWord.total_append, pow_add, ← one_div_mul_one_div]
    rw [← Finset.sum_mul_sum, ← graftMass_sum]
    rfl
  · intro a ha b hb he
    exact Prod.ext (List.cons.inj he).1 (List.cons.inj he).2

/-- The fixed-precision family has the exact nth power of the original block mass. -/
theorem graftWords_mass_pow (E n : ℕ) :
    Reference.stoppingMass (graftWords E n) =
      Reference.stoppingMass (stoppedWords E) ^ n := by
  induction n with
  | zero => simp [graftWords, graftBlockLists, Reference.stoppingMass, ValuationWord.total]
  | succ n ih => rw [graftWords_mass_succ, ih, pow_succ, mul_comm]

/-- Precision rejection costs at most n times the original single-block deficit. -/
theorem graftWords_deficit_le (E n : ℕ) :
    1 - Reference.stoppingMass (graftWords E n) ≤
      (n : ℝ) * (1 - Reference.stoppingMass (stoppedWords E)) := by
  induction n with
  | zero => simp [graftWords, graftBlockLists, Reference.stoppingMass, ValuationWord.total]
  | succ n ih =>
      have hp := (stoppedWords_mass_bounds E).2
      have hq := (graftWords_mass_bounds E n).2
      have hu := mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq)
      rw [graftWords_mass_succ, Nat.cast_add, Nat.cast_one]
      nlinarith

/-- The same precision loss is paid under the full stopped-copy law. -/
theorem graftBlocks_rejection_le (E n : ℕ) :
    Gated.probability (stoppedCopiesPMF n) (fun ws => ¬ (∀ w ∈ ws, w ∈ stoppedWords E)) ≤
      (n : ℝ) * (1 - Reference.stoppingMass (stoppedWords E)) := by
  rw [Gated.probability_compl, graftWords_probability]
  exact graftWords_deficit_le E n

end WordCertDensity.Construction
