/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.MacroBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Original probability mass of scheduled finite families

The complete stopped-copy law retains the product of original geometric
atoms. Unique parsing identifies finite list sums with the mass of their
flattened word images. Arbitrary finite gates retain this identity. The
precision deficit is bounded at the original starting count, without any
normalization by surviving mass.
-/

@[expose] public section

namespace WordCertDensity.Construction

open scoped Classical ENNReal

/-- A supported complete stopped list has exactly its original concatenated geometric atom. -/
theorem stoppedCopiesPMF_toReal (ws : List ValuationWord)
    (hws : ∀ w ∈ ws, FirstCrossing w) :
    (stoppedCopiesPMF ws.length ws).toReal =
      1 / (2 : ℝ) ^ (ValuationWord.total ws.flatten) := by
  induction ws with
  | nil => simp [stoppedCopiesPMF, ValuationWord.total]
  | cons w ws ih =>
      have hw := hws w (by simp)
      have ht : ∀ v ∈ ws, FirstCrossing v := fun v hv => hws v (by simp [hv])
      rw [List.length_cons, stoppedCopiesPMF_cons, ENNReal.toReal_mul,
        stoppedPMF_toReal hw, ih ht, List.flatten_cons, ValuationWord.total_append, pow_add]
      simp only [div_mul_div_comm, one_mul]

/-- Every actual scheduled component lies in the full first-crossing support. -/
theorem scheduledBlocks_firstCrossing {B : ℕ} {ws : List ValuationWord}
    (hp : ScheduledBlocks B ws) : ∀ w ∈ ws, FirstCrossing w := by
  induction ws generalizing B with
  | nil => simp
  | cons v vs ih =>
      obtain ⟨hv, hvs⟩ := (scheduledBlocks_cons B v vs).mp hp
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact (mem_stoppedWords _ _).mp hv |>.1
      · exact ih hvs w hw

private theorem probability_finset {α : Type*} (p : PMF α) (V : Finset α) :
    Gated.probability p (fun a => a ∈ V) = ∑ a ∈ V, (p a).toReal := by
  unfold Gated.probability
  rw [tsum_eq_sum (s := V) (fun a ha => by simp [ha])]
  rw [ENNReal.toReal_sum (fun a ha => by rw [if_pos ha]; exact PMF.apply_ne_top _ _)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [if_pos ha]

private theorem stoppingMass_image {B n : ℕ} {V : Finset (List ValuationWord)}
    (hV : V ⊆ scheduledBlockLists B n) :
    Reference.stoppingMass (V.image List.flatten) =
      ∑ ws ∈ V, 1 / (2 : ℝ) ^ (ValuationWord.total ws.flatten) := by
  unfold Reference.stoppingMass
  rw [Finset.sum_image]
  intro us hu vs hv he
  exact BlockRule.flatten_injective ((mem_scheduledBlockLists B n us).mp (hV hu)).2
    ((mem_scheduledBlockLists B n vs).mp (hV hv)).2 he

/-- Every finite scheduled-list restriction has its exact unconditioned flattened-word mass. -/
theorem scheduledLists_probability {B n : ℕ} {V : Finset (List ValuationWord)}
    (hV : V ⊆ scheduledBlockLists B n) :
    Gated.probability (stoppedCopiesPMF n) (fun ws => ws ∈ V) =
      Reference.stoppingMass (V.image List.flatten) := by
  rw [probability_finset, stoppingMass_image hV]
  apply Finset.sum_congr rfl
  intro ws hws
  obtain ⟨hlen, hp⟩ := (mem_scheduledBlockLists B n ws).mp (hV hws)
  have h := stoppedCopiesPMF_toReal ws (scheduledBlocks_firstCrossing hp)
  simpa only [hlen] using h

/-- Any word gate, including a corridor, retains exactly the original finite-family mass. -/
theorem scheduledWords_gate_probability (B n : ℕ) (G : ValuationWord → Prop) :
    Gated.probability (stoppedCopiesPMF n) (fun ws => ScheduledBlocks B ws ∧ G ws.flatten) =
      Reference.stoppingMass ((scheduledWords B n).filter G) := by
  let V := (scheduledBlockLists B n).filter (fun ws => G ws.flatten)
  have he := Gated.probability_congr_on_support (stoppedCopiesPMF n)
    (fun ws => ScheduledBlocks B ws ∧ G ws.flatten) (fun ws => ws ∈ V)
    (fun ws hp => by
      have hlen := ((stoppedCopiesPMF_mem_support_iff n ws).mp
        ((PMF.mem_support_iff _ _).mpr hp)).1
      simp only [V, Finset.mem_filter, mem_scheduledBlockLists, hlen, true_and])
  rw [he, scheduledLists_probability (Finset.filter_subset _ _)]
  congr 1
  ext w
  simp only [scheduledWords, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨ws, ⟨hws, hG⟩, rfl⟩
    exact ⟨⟨ws, hws, rfl⟩, hG⟩
  · rintro ⟨⟨ws, hws, rfl⟩, hG⟩
    exact ⟨ws, ⟨hws, hG⟩, rfl⟩

/-- The unrestricted scheduled-family mass is its probability under complete stopped copies. -/
theorem scheduledWords_probability (B n : ℕ) :
    Gated.probability (stoppedCopiesPMF n) (ScheduledBlocks B) =
      Reference.stoppingMass (scheduledWords B n) := by
  simpa using scheduledWords_gate_probability B n (fun _ => True)

private theorem scheduledMass_eq_sum (B n : ℕ) :
    Reference.stoppingMass (scheduledWords B n) =
      ∑ ws ∈ scheduledBlockLists B n, 1 / (2 : ℝ) ^ (ValuationWord.total ws.flatten) :=
  stoppingMass_image (Finset.Subset.refl _)

private theorem geometric_cons (w : ValuationWord) (ws : List ValuationWord) :
    1 / (2 : ℝ) ^ (ValuationWord.total (w :: ws).flatten) =
      (1 / (2 : ℝ) ^ w.total) * (1 / (2 : ℝ) ^ (ValuationWord.total ws.flatten)) := by
  simp only [List.flatten_cons, ValuationWord.total_append, pow_add, div_mul_div_comm, one_mul]

/-- Surviving scheduled mass factors by the original next-block mass, with no conditioning. -/
theorem scheduledWords_mass_succ (B n : ℕ) :
    Reference.stoppingMass (scheduledWords B (n + 1)) =
      Reference.stoppingMass (stoppedWords (continuationPrecision (B + 1))) *
        Reference.stoppingMass (scheduledWords (B + 1) n) := by
  rw [scheduledMass_eq_sum, scheduledBlockLists, Finset.sum_image]
  · rw [Finset.product_eq_sprod, Finset.sum_product]
    simp_rw [geometric_cons]
    rw [← Finset.sum_mul_sum, ← scheduledMass_eq_sum]
    rfl
  · intro a ha b hb he
    exact Prod.ext (List.cons.inj he).1 (List.cons.inj he).2

/-- The complete finite schedule loses at most the original-count precision union bound. -/
theorem scheduledWords_deficit_le (B n : ℕ) :
    1 - Reference.stoppingMass (scheduledWords B n) ≤
      (n : ℝ) * ((B : ℝ) + 3) ^ (-10 : ℝ) := by
  induction n generalizing B with
  | zero => simp [scheduledWords, scheduledBlockLists, Reference.stoppingMass, ValuationWord.total]
  | succ n ih =>
      have hp := (stoppedWords_mass_bounds (continuationPrecision (B + 1))).2
      have hq := Reference.stoppingMass_le_one (scheduledWords (B + 1) n)
        (scheduledWords_prefixFree (B + 1) n)
      have hblock := (continuationLoss_bound (B + 1)).2
      change 1 - Reference.stoppingMass (stoppedWords (continuationPrecision (B + 1))) ≤
        (((B + 1 : ℕ) : ℝ) + 2) ^ (-10 : ℝ) at hblock
      have heq : ((B + 1 : ℕ) : ℝ) + 2 = (B : ℝ) + 3 := by push_cast; ring
      rw [heq] at hblock
      have ht := ih (B + 1)
      have hpow : (((B + 1 : ℕ) : ℝ) + 3) ^ (-10 : ℝ) ≤
          ((B : ℝ) + 3) ^ (-10 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by norm_num)
      have hm := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      have hu := mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq)
      rw [scheduledWords_mass_succ, Nat.cast_add, Nat.cast_one]
      nlinarith

/-- Rejection by prescribed precisions has the same bound under the original stopped-copy law. -/
theorem scheduledBlocks_rejection_le (B n : ℕ) :
    Gated.probability (stoppedCopiesPMF n) (fun ws => ¬ ScheduledBlocks B ws) ≤
      (n : ℝ) * ((B : ℝ) + 3) ^ (-10 : ℝ) := by
  rw [Gated.probability_compl, scheduledWords_probability]
  exact scheduledWords_deficit_le B n

end WordCertDensity.Construction
