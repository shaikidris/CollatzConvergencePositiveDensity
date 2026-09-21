/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.Words
public import WordCertDensity.Probability.Gated

/-!
# Exact law of a pair of geometric letters

The two-letter reference law is partitioned by its total valuation. A total
`b ≥ 2` has exactly `b - 1` splittings, all with atom `2⁻ᵇ`; consequently the
conditional first letter is uniform. These statements use the original
`wordPMF`, not a replacement stochastic model.
-/

@[expose] public section

open scoped BigOperators

namespace WordCertDensity.Reference

/-- The two positive letters with total `b`, indexed by the first letter. -/
def pairWord (b : ℕ) (i : Fin (b - 1)) : ValuationWord :=
  [Nat.succPNat i, Nat.succPNat (b - 2 - i)]

theorem pairWord_length (b : ℕ) (i : Fin (b - 1)) : (pairWord b i).length = 2 := by
  simp [pairWord]

theorem pairWord_total {b : ℕ} (hb : 2 ≤ b) (i : Fin (b - 1)) :
    (pairWord b i).total = b := by
  simp only [pairWord, ValuationWord.total, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  change i.val + 1 + (b - 2 - i.val + 1) = b
  have hi : i.val ≤ b - 2 := by omega
  omega

theorem exists_unique_pairWord {b : ℕ} (hb : 2 ≤ b) (w : ValuationWord)
    (hlength : w.length = 2) (htotal : w.total = b) :
    ∃! i : Fin (b - 1), pairWord b i = w := by
  rcases w with _ | ⟨a, _ | ⟨c, tail⟩⟩
  · simp at hlength
  · simp at hlength
  · have htail : tail = [] := by simpa using hlength
    subst tail
    have hac : (a : ℕ) + (c : ℕ) = b := by
      simpa [ValuationWord.total] using htotal
    have ha : a.natPred < b - 1 := by
      have haVal : (a : ℕ) = a.natPred + 1 := by
        exact (congrArg PNat.val (PNat.succPNat_natPred a)).symm
      have hc : 1 ≤ (c : ℕ) := c.prop
      omega
    let i : Fin (b - 1) := ⟨a.natPred, ha⟩
    refine ⟨i, ?_, ?_⟩
    · have hfirst : Nat.succPNat i = a := PNat.succPNat_natPred a
      have hsecond : Nat.succPNat (b - 2 - i) = c := by
        apply PNat.eq
        change b - 2 - a.natPred + 1 = (c : ℕ)
        have haVal : (a : ℕ) = a.natPred + 1 := by
          exact (congrArg PNat.val (PNat.succPNat_natPred a)).symm
        have hc : 1 ≤ (c : ℕ) := c.prop
        omega
      simp [pairWord, hfirst, hsecond]
    · intro j hj
      have hhead : Nat.succPNat j = a := by
        exact (List.cons.inj hj).1
      apply Fin.ext
      have := congrArg PNat.val hhead
      change (j : ℕ) + 1 = (a : ℕ) at this
      have haVal : (a : ℕ) = a.natPred + 1 := by
        exact (congrArg PNat.val (PNat.succPNat_natPred a)).symm
      simp only [i]
      omega

theorem pairWord_atom {b : ℕ} (hb : 2 ≤ b) (i : Fin (b - 1)) :
    (wordPMF 2 (pairWord b i)).toReal = (1 / 2 : ℝ) ^ b := by
  rw [wordPMF_toReal]
  simp [pairWord_length, pairWord_total hb]

/-- Total mass of the two-letter fiber with valuation sum `b`. -/
noncomputable def pairMass (b : ℕ) : ℝ :=
  ∑ i : Fin (b - 1), (wordPMF 2 (pairWord b i)).toReal

/-- Pair mass is nonnegative for every total, including empty fibers. -/
theorem pairMass_nonneg (b : ℕ) : 0 ≤ pairMass b := by
  unfold pairMass
  exact Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg

theorem pairMass_eq {b : ℕ} (hb : 2 ≤ b) :
    pairMass b = (b - 1 : ℕ) * (1 / 2 : ℝ) ^ b := by
  simp [pairMass, pairWord_atom hb]

/-- The finite fiber of two-letter words with total valuation `b`. -/
def pairWords (b : ℕ) : Finset ValuationWord :=
  Finset.univ.image (pairWord b)

theorem mem_pairWords_iff {b : ℕ} (hb : 2 ≤ b) (w : ValuationWord) :
    w ∈ pairWords b ↔ w.length = 2 ∧ w.total = b := by
  constructor
  · intro hw
    rw [pairWords, Finset.mem_image] at hw
    obtain ⟨i, _, rfl⟩ := hw
    exact ⟨pairWord_length b i, pairWord_total hb i⟩
  · rintro ⟨hlength, htotal⟩
    obtain ⟨i, hi, _⟩ := exists_unique_pairWord hb w hlength htotal
    rw [pairWords, Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, hi⟩

theorem pair_probability_eq_pairMass {b : ℕ} (hb : 2 ≤ b) :
    Gated.probability (wordPMF 2) (fun w => w.total = b) = pairMass b := by
  unfold Gated.probability
  rw [tsum_eq_sum (s := pairWords b)]
  · rw [ENNReal.toReal_sum]
    · rw [pairMass, pairWords, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i _
        rw [if_pos (pairWord_total hb i)]
      · intro i _ j _ hij
        apply Fin.ext
        have hhead := congrArg PNat.val (List.cons.inj hij).1
        change (i : ℕ) + 1 = (j : ℕ) + 1 at hhead
        omega
    · intro w _
      split_ifs
      · exact PMF.apply_ne_top _ _
      · simp
  · intro w hw
    by_cases htotal : w.total = b
    · have hlength : w.length ≠ 2 := by
        intro hlength
        exact hw ((mem_pairWords_iff hb w).mpr ⟨hlength, htotal⟩)
      simp [htotal, wordPMF_eq_zero_of_length_ne 2 w hlength]
    · simp [htotal]

/-- Conditional averaging on a fixed pair sum is uniform over its `b-1` splittings. -/
noncomputable def pairConditionalAverage {α : Type*} [DivisionRing α]
    (b : ℕ) (f : Fin (b - 1) → α) : α :=
  ((b - 1 : ℕ) : α)⁻¹ * ∑ i, f i

theorem pairConditionalAverage_const {α : Type*} [DivisionRing α] [CharZero α]
  {b : ℕ} (hb : 2 ≤ b) (c : α) :
    pairConditionalAverage b (fun _ => c) = c := by
  have hn : b - 1 ≠ 0 := by omega
  have hne : ((b - 1 : ℕ) : α) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [pairConditionalAverage, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- Original two-letter mass weighted by a function of the fixed-sum splitting. -/
noncomputable def pairWeightedSum (b : ℕ) (f : Fin (b - 1) → ℂ) : ℂ :=
  ∑ i, ((wordPMF 2 (pairWord b i)).toReal : ℂ) * f i

/-- Conditioning the original pair on its sum gives the uniform splitting average. -/
theorem pairWeightedSum_div_mass {b : ℕ} (hb : 2 ≤ b) (f : Fin (b - 1) → ℂ) :
    pairWeightedSum b f / pairMass b = pairConditionalAverage b f := by
  have hn : b - 1 ≠ 0 := by omega
  simp only [pairWeightedSum, pairWord_atom hb, ← Finset.mul_sum,
    pairMass_eq hb, pairConditionalAverage]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hn]

/-- The unnormalized fixed-sum expectation is its event mass times its
uniform conditional average. -/
theorem pairWeightedSum_eq_mass_mul_average {b : ℕ} (hb : 2 ≤ b)
    (f : Fin (b - 1) → ℂ) :
    pairWeightedSum b f = pairMass b * pairConditionalAverage b f := by
  have hmass : pairMass b ≠ 0 := by
    rw [pairMass_eq hb]
    exact mul_ne_zero (by exact_mod_cast (show b - 1 ≠ 0 by omega))
      (pow_ne_zero _ (by norm_num))
  have hmassC : (pairMass b : ℂ) ≠ 0 := by exact_mod_cast hmass
  simpa [mul_comm] using
    (div_eq_iff hmassC).mp (pairWeightedSum_div_mass hb f)

theorem norm_pairConditionalAverage_le_one {b : ℕ} (hb : 2 ≤ b)
    (f : Fin (b - 1) → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ‖pairConditionalAverage b f‖ ≤ 1 := by
  have hn : 0 < b - 1 := by omega
  rw [pairConditionalAverage, norm_mul, norm_inv]
  calc
    ‖((b - 1 : ℕ) : ℂ)‖⁻¹ * ‖∑ i, f i‖ ≤
        ‖((b - 1 : ℕ) : ℂ)‖⁻¹ * ∑ i, ‖f i‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ ‖((b - 1 : ℕ) : ℂ)‖⁻¹ * ∑ _i : Fin (b - 1), 1 := by
          gcongr with i
          exact hf i
    _ = 1 := by
      simp [hn.ne']

/-- Indices for every possible total and splitting of a two-letter word. -/
def PairIndex := Σ b : {b : ℕ // 2 ≤ b}, Fin (b.1 - 1)

/-- The canonical two-letter word associated with a total and splitting. -/
def pairIndexWord (p : PairIndex) : ValuationWord := pairWord p.1.1 p.2

/-- The total/splitting index determines its canonical pair uniquely. -/
theorem pairIndexWord_injective : Function.Injective pairIndexWord := by
  rintro ⟨⟨b, hb⟩, i⟩ ⟨⟨c, hc⟩, k⟩ h
  have htotal := congrArg ValuationWord.total h
  simp only [pairIndexWord] at h htotal
  rw [pairWord_total hb i, pairWord_total hc k] at htotal
  subst c
  have hik : i = k := by
    apply Fin.ext
    have hhead := congrArg PNat.val (List.cons.inj h).1
    change (i : ℕ) + 1 = (k : ℕ) + 1 at hhead
    omega
  subst k
  rfl

private theorem twoLetter_total_ge_two (w : ValuationWord) (hw : w.length = 2) :
    2 ≤ w.total := by
  rcases w with _ | ⟨a, _ | ⟨c, tail⟩⟩
  · simp at hw
  · simp at hw
  · have htail : tail = [] := by simpa using hw
    subst tail
    simp only [ValuationWord.total, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    have ha : 1 ≤ (a : ℕ) := a.prop
    have hc : 1 ≤ (c : ℕ) := c.prop
    omega

/-- Every function supported on two-letter words can be regrouped exactly by
the pair total and its canonical splitting. -/
theorem tsum_eq_tsum_pairIndex {α : Type*} [AddCommMonoid α]
    [TopologicalSpace α] (f : ValuationWord → α)
    (hf : ∀ w, w.length ≠ 2 → f w = 0) :
    (∑' w : ValuationWord, f w) = ∑' p : PairIndex, f (pairIndexWord p) := by
  have hsupp : Function.support f ⊆ Set.range pairIndexWord := by
    intro w hw
    have hlength : w.length = 2 := by
      by_contra hne
      exact hw (hf w hne)
    have htotal : 2 ≤ w.total := twoLetter_total_ge_two w hlength
    obtain ⟨i, hi, _⟩ := exists_unique_pairWord htotal w hlength rfl
    exact ⟨⟨⟨w.total, htotal⟩, i⟩, hi⟩
  exact (pairIndexWord_injective.tsum_eq hsupp).symm

end WordCertDensity.Reference
