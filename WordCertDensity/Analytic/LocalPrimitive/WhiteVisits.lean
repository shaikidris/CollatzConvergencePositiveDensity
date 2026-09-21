/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.Words
public import WordCertDensity.Reference.PairLaw
public import WordCertDensity.Reference.Stopping
public import WordCertDensity.Probability.ExponentialMarkov

/-! # Fixed-cut source-law factorization for Appendix E.6

This module deliberately proves only the deterministic prefix/tail product
law.  A predictable selected mark additionally requires a finite stopping
construction showing that its cut is measurable before the next pair is
sampled; that construction is not present here.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

/-- Under an arbitrary sequential product PMF, fixing the first coordinate
and imposing an event on the second coordinate factors its real probability. -/
theorem fixedCut_bind_map_pair_probability {α β : Type*} (p : PMF α)
    (q : PMF β) (u : α) (B : β → Prop) :
    Gated.probability (p.bind fun a => q.map (fun b => (a, b)))
      (fun ab => ab.1 = u ∧ B ab.2) =
      (p u).toReal * Gated.probability q B := by
  unfold Gated.probability
  have hsum :
      (∑' ab, (p.bind fun a => q.map (fun b => (a, b))) ab *
        if ab.1 = u ∧ B ab.2 then 1 else 0) =
      p u * ∑' b, if B b then q b else 0 := by
    rw [PMFMoment.sum_bind]
    have hmap (a : α) :
        (∑' ab, (q.map (fun b => (a, b))) ab *
          if ab.1 = u ∧ B ab.2 then 1 else 0) =
          ∑' b, q b * if a = u ∧ B b then 1 else 0 :=
      PMFMoment.sum_map q (fun b => (a, b))
        (fun ab => if ab.1 = u ∧ B ab.2 then 1 else 0)
    simp_rw [hmap]
    have hinner (a : α) :
        (∑' b, q b * if a = u ∧ B b then 1 else 0) =
          if a = u then ∑' b, if B b then q b else 0 else 0 := by
      by_cases hau : a = u
      · subst a
        simp [mul_ite]
      · simp [hau]
    simp_rw [hinner]
    rw [tsum_eq_single u]
    · simp
    · intro a hau
      simp [hau]
  simp only [mul_ite, mul_one, mul_zero] at hsum
  have hu := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_mul] at hu
  refine (congrArg ENNReal.toReal ?_).trans hu
  apply tsum_congr
  intro ab
  by_cases hab : ab.1 = u ∧ B ab.2 <;> simp [hab]

/-- A fixed prefix of the original reference word and its fresh tail factor
exactly.  The statement has a deterministic cut `m`; it is a source-law input
for, but not yet a proof of, predictable selected marks. -/
theorem wordPMF_fixedCut_tail_probability (m n : ℕ) (u : ValuationWord)
    (B : ValuationWord → Prop) :
    Gated.probability (Reference.wordPMF (m + n))
      (fun w => w.take m = u ∧ B (w.drop m)) =
      (Reference.wordPMF m u).toReal *
        Gated.probability (Reference.wordPMF n) B := by
  rw [← Gated.probability_map (Reference.wordPMF (m + n))
    (fun w => (w.take m, w.drop m)) (fun uv => uv.1 = u ∧ B uv.2)]
  rw [Reference.wordPMF_map_take_drop]
  exact fixedCut_bind_map_pair_probability _ _ u B

/-- A fresh original-law pair has total valuation three with probability one
quarter.  This is the mark law later used only after a predictable cut has
been proved. -/
theorem freshPair_total_three_probability :
    Gated.probability (Reference.wordPMF 2) (fun w => w.total = 3) = 1 / 4 := by
  rw [Reference.pair_probability_eq_pairMass (by norm_num : 2 ≤ 3)]
  rw [Reference.pairMass_eq (by norm_num : 2 ≤ 3)]
  norm_num

/-- At a deterministic cut, a prescribed prefix and a fresh total-three mark
have the exact original-law product probability. -/
theorem wordPMF_fixedCut_total_three_probability (m : ℕ) (u : ValuationWord) :
    Gated.probability (Reference.wordPMF (m + 2))
      (fun w => w.take m = u ∧ ValuationWord.total (w.drop m) = 3) =
      (Reference.wordPMF m u).toReal * (1 / 4 : ℝ) := by
  calc
    _ = (Reference.wordPMF m u).toReal *
        Gated.probability (Reference.wordPMF 2)
          (fun v => ValuationWord.total v = 3) :=
      wordPMF_fixedCut_tail_probability m 2 u _
    _ = _ := by rw [freshPair_total_three_probability]

/-- The first fresh pair retains its total-three mark probability when an
arbitrary deterministic tail follows it. -/
theorem freshPairMark_tail_probability (q : ℕ) :
    Gated.probability (Reference.wordPMF (2 + q))
      (fun v => ValuationWord.total (v.take 2) = 3) = 1 / 4 := by
  have h := Gated.probability_map (Reference.wordPMF (2 + q))
    (fun v => v.take 2) (fun a => ValuationWord.total a = 3)
  rw [Reference.wordPMF_map_take] at h
  exact h.symm.trans freshPair_total_three_probability

/-- At any deterministic cut with a remaining horizon of at least one pair,
the first post-cut pair is a fresh total-three mark. -/
theorem wordPMF_fixedCut_mark_probability (m q : ℕ) (u : ValuationWord) :
    Gated.probability (Reference.wordPMF (m + (2 + q)))
      (fun w => w.take m = u ∧
        ValuationWord.total ((w.drop m).take 2) = 3) =
      (Reference.wordPMF m u).toReal * (1 / 4 : ℝ) := by
  calc
    _ = (Reference.wordPMF m u).toReal *
        Gated.probability (Reference.wordPMF (2 + q))
          (fun v => ValuationWord.total (v.take 2) = 3) :=
      wordPMF_fixedCut_tail_probability m (2 + q) u _
    _ = _ := by rw [freshPairMark_tail_probability]

/-- The mark examined immediately after a selected stopping prefix.  The
prefix family is supplied explicitly so that selection cannot inspect this
post-prefix pair. -/
def prefixFamilyMarkEvent (V : Finset ValuationWord) (w : ValuationWord) : Prop :=
  ∃ u ∈ V, u <+: w ∧ ValuationWord.total ((w.drop u.length).take 2) = 3

/-- Prefix-freeness makes the selected stopping prefix unique, independently
of the value of the next-pair mark. -/
theorem prefixFamilyMark_unique {V : Finset ValuationWord}
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v))
    {u v w : ValuationWord} (hu : u ∈ V) (hv : v ∈ V)
    (huw : u <+: w) (hvw : v <+: w) : u = v :=
  Reference.prefixFamily_unique hfree hu hv huw hvw

/-- A finite prefix-free stopping family has an exactly fair post-stop
total-three mark on the original word law.  The horizon condition leaves one
full pair after every selected prefix. -/
theorem prefixFamilyMark_probability (V : Finset ValuationWord) (N : ℕ)
    (hlen : ∀ u ∈ V, u.length + 2 ≤ N)
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v)) :
    Gated.probability (Reference.wordPMF N) (prefixFamilyMarkEvent V) =
      (1 / 4 : ℝ) * Reference.stoppingMass V := by
  let G : V → ValuationWord → Prop := fun u w =>
    (u : ValuationWord) <+: w ∧
      ValuationWord.total ((w.drop (u : ValuationWord).length).take 2) = 3
  have hunique : ∀ i j w, G i w → G j w → i = j := by
    intro i j w hi hj
    apply Subtype.ext
    exact prefixFamilyMark_unique hfree i.property j.property hi.1 hj.1
  have hUnion := Gated.probability_union (Reference.wordPMF N) G hunique
  have hEvent : prefixFamilyMarkEvent V = (fun w => ∃ i : V, G i w) := by
    funext w
    apply propext
    simp only [prefixFamilyMarkEvent, G]
    constructor
    · rintro ⟨u, hu, hprefix, hmark⟩
      exact ⟨⟨u, hu⟩, hprefix, hmark⟩
    · rintro ⟨u, hprefix, hmark⟩
      exact ⟨u, u.property, hprefix, hmark⟩
  rw [hEvent, hUnion]
  have hterm (u : V) : Gated.probability (Reference.wordPMF N) (G u) =
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (u : ValuationWord).total := by
    have hN : N = (u : ValuationWord).length +
        (2 + (N - (u : ValuationWord).length - 2)) := by
      have := hlen u u.property
      omega
    rw [hN]
    have hcongr := Gated.probability_congr_on_support
      (Reference.wordPMF ((u : ValuationWord).length +
        (2 + (N - (u : ValuationWord).length - 2))))
      (G u)
      (fun w => w.take (u : ValuationWord).length = u ∧
        ValuationWord.total ((w.drop (u : ValuationWord).length).take 2) = 3)
      (fun w _ => by
        change ((u : ValuationWord) <+: w ∧
          ValuationWord.total ((w.drop (u : ValuationWord).length).take 2) = 3) ↔
            w.take (u : ValuationWord).length = u ∧
              ValuationWord.total ((w.drop (u : ValuationWord).length).take 2) = 3
        rw [List.prefix_iff_eq_take]
        exact and_congr eq_comm Iff.rfl)
    rw [hcongr, wordPMF_fixedCut_mark_probability]
    rw [Reference.wordPMF_toReal_length]
    ring
  simp_rw [hterm]
  unfold Reference.stoppingMass
  rw [Finset.mul_sum]
  convert Finset.sum_attach V (fun w =>
    (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ w.total) using 1 <;> simp

end WordCertDensity.LocalPrimitive
