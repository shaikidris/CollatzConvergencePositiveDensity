/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ReducedRecords

/-! # One reciprocal charge across the complete root pool

The literal finite sum retains the actual selected records. Its conversion
to the existing pooled word charge uses proved record identification and
physical realization, before any grouping or inequality is applied.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- The actual complete-record charge at one source, after terminal reduction. -/
noncomputable def reducedSourceCharge (L δ X : ℝ) (b t j d x : ℕ) (pool : Finset ℕ) : ℝ :=
  ∑ root ∈ pool, (∑ r ∈ (selectedTerminalRecords L δ X b t j root d 1).filter
    (fun r => terminalRecordSource root r = x), Transfer.weight (terminalRecordWord r)) / root

/-- Actual physical word charge agrees with its existing rational pooled charge. -/
theorem terminalRecord_charge_eq {root x : ℕ} {r : GraftRecord × ValuationWord}
    (hp : PhysicalHistory (terminalRecordWord r) root x) :
    (Roots.poolWordCharge (root, terminalRecordWord r) x : ℝ) =
      Transfer.weight (terminalRecordWord r) / root := by
  rw [Roots.poolWordCharge_eq hp]
  push_cast
  rfl

/-- Every summand in the literal reduced-source charge is nonnegative. -/
theorem reducedSourceCharge_nonneg (L δ X : ℝ) (b t j d x : ℕ) (pool : Finset ℕ) :
    0 ≤ reducedSourceCharge L δ X b t j d x pool := by
  apply Finset.sum_nonneg
  intro root _
  exact div_nonneg (Finset.sum_nonneg fun r _ => (Transfer.weight_pos _).le) (Nat.cast_nonneg _)

/-- All actual reduced records in a nonrecurrent pool pay one total reciprocal charge. -/
theorem reducedSourceCharge_le {L δ X : ℝ} {b t j d x : ℕ} {pool : Finset ℕ}
    (hb : 0 < b) (hP : NonrecurrentPool acceleratedStep (pool : Set ℕ)) :
    reducedSourceCharge L δ X b t j d x pool ≤ (x : ℝ)⁻¹ := by
  let records := fun root => (selectedTerminalRecords L δ X b t j root d 1).filter
    (fun r => terminalRecordSource root r = x)
  let catalogue := pool.sigma records
  let code : (Σ _ : ℕ, GraftRecord × ValuationWord) → ℕ × ValuationWord :=
    fun a => (a.1, terminalRecordWord a.2)
  have hmem (a : Σ _ : ℕ, GraftRecord × ValuationWord) (ha : a ∈ catalogue) :
      a.1 ∈ pool ∧ a.2 ∈ selectedTerminalRecords L δ X b t j a.1 d 1 ∧
        terminalRecordSource a.1 a.2 = x := by
    obtain ⟨hroot, hr⟩ := Finset.mem_sigma.mp ha
    exact ⟨hroot, (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2⟩
  have hphysical (a : Σ _ : ℕ, GraftRecord × ValuationWord) (ha : a ∈ catalogue) :
      PhysicalHistory (terminalRecordWord a.2) a.1 x := by
    have h := selectedTerminalRecords_physical (hmem a ha).2.1
    simpa only [(hmem a ha).2.2] using h
  have hinj : Set.InjOn code (catalogue : Set _) := by
    intro a ha z hz he
    have hroot : a.1 = z.1 := congrArg Prod.fst he
    have hword : terminalRecordWord a.2 = terminalRecordWord z.2 := congrArg Prod.snd he
    rcases a with ⟨root, r⟩
    rcases z with ⟨other, s⟩
    dsimp only at hroot hword
    subst other
    have hrs : r = s := selectedTerminalRecords_word_injective hb
      (hmem ⟨root,r⟩ ha).2.1 (hmem ⟨root,s⟩ hz).2.1 hword
    subst s
    rfl
  have hs := Roots.sum_poolWordCharge_le_of_injOn hP catalogue code x
    (fun a ha => (hmem a ha).1) hinj
  have hreal : (∑ a ∈ catalogue, Transfer.weight (terminalRecordWord a.2) / (a.1 : ℝ)) ≤
      1 / (x : ℝ) := by
    calc
      _ = ∑ a ∈ catalogue, (Roots.poolWordCharge (code a) x : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact (terminalRecord_charge_eq (hphysical a ha)).symm
      _ ≤ 1 / (x : ℝ) := by
        have hcast := Rat.cast_le (K := ℝ) |>.mpr hs
        push_cast at hcast
        exact hcast
  unfold reducedSourceCharge
  simp_rw [Finset.sum_div]
  rw [Finset.sum_sigma']
  exact hreal.trans_eq (one_div _)

/-- The prepared reduced-record handoff, with no multiplicity per root or preimage. -/
theorem reducedRecordCharge (L δ X : ℝ) (b t j d : ℕ) (pool : Finset ℕ)
    (hb : 0 < b) (hP : NonrecurrentPool acceleratedStep (pool : Set ℕ))
    (_hroot : ∀ root ∈ pool, 0 < root) :
    (∀ root ∈ pool, Set.InjOn terminalRecordWord
      (selectedTerminalRecords L δ X b t j root d 1 : Set _)) ∧
    ∀ x : ℕ, 0 < x → 0 ≤ reducedSourceCharge L δ X b t j d x pool ∧
      reducedSourceCharge L δ X b t j d x pool ≤ (x : ℝ)⁻¹ := by
  exact ⟨fun _ _ => selectedTerminalRecords_word_injective hb,
    fun x _ => ⟨reducedSourceCharge_nonneg L δ X b t j d x pool, reducedSourceCharge_le hb hP⟩⟩

end WordCertDensity.Construction
