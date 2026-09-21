/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The iid list construction, atom and take/drop proofs are adapted from
Lech Mazur, Copyright 2026 Lech Mazur, under Apache License 2.0. The source
LICENSE and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
Modifications use the local geometric law and valuation-word totals.
-/
module

public import WordCertDensity.Reference.Geometric
public import WordCertDensity.Words.Algebra
import Mathlib.Tactic.NormNum

/-!
# Independent geometric words

A word of the specified length has probability two to the negative total
valuation. The head and tail of a reference word are independent, expressed
as an equality of probability mass functions. No physical-source sampling
assumption is part of these identities.
-/

@[expose] public section

namespace WordCertDensity

namespace Reference

/-- Independent positive geometric words of a fixed length. -/
noncomputable def wordPMF : ℕ → PMF ValuationWord
  | 0 => PMF.pure []
  | n + 1 => geometricLetter.bind (fun a => (wordPMF n).map (fun w => a :: w))

/-- The zero-length reference word is deterministically empty. -/
theorem wordPMF_zero : wordPMF 0 = PMF.pure [] := rfl

/-- A nonempty atom factors into the first letter and the remaining word. -/
theorem wordPMF_cons (n : ℕ) (a : ℕ+) (w : ValuationWord) :
    wordPMF (n + 1) (a :: w) = geometricLetter a * wordPMF n w := by
  classical
  rw [wordPMF, PMF.bind_apply]
  have hmap (b : ℕ+) :
      ((wordPMF n).map (fun v => b :: v)) (a :: w) =
        if a = b then wordPMF n w else 0 := by
    rw [PMF.map_apply]
    by_cases h : a = b
    · subst b
      rw [tsum_eq_single w]
      · simp
      · intro v hv
        have hne : ¬ a :: w = a :: v := fun he => hv (List.cons.inj he).2.symm
        simp [hne]
    · have hne (v : ValuationWord) : ¬ a :: w = b :: v :=
        fun he => h (List.cons.inj he).1
      simp [h, hne]
  simp_rw [hmap]
  rw [tsum_eq_single a]
  · simp
  · intro b hb
    simp [hb.symm]

/-- A positive-length word cannot be empty. -/
theorem wordPMF_succ_nil (n : ℕ) : wordPMF (n + 1) [] = 0 := by
  classical
  rw [wordPMF, PMF.bind_apply]
  simp [PMF.map_apply]

/-- Words of the wrong length have zero mass. -/
theorem wordPMF_eq_zero_of_length_ne (n : ℕ) (w : ValuationWord) (h : w.length ≠ n) :
    wordPMF n w = 0 := by
  induction n generalizing w with
  | zero =>
      cases w with
      | nil => exact (h rfl).elim
      | cons a w => simp [wordPMF]
  | succ n ih =>
      cases w with
      | nil => exact wordPMF_succ_nil n
      | cons a w =>
          rw [wordPMF_cons, ih w (by simpa using h), mul_zero]

/-- The probability of a word at its own length is exactly its geometric weight. -/
theorem wordPMF_toReal_length (w : ValuationWord) :
    (wordPMF w.length w).toReal = (1 / 2 : ℝ) ^ w.total := by
  induction w with
  | nil => simp [wordPMF, ValuationWord.total]
  | cons a w ih =>
      rw [List.length_cons, wordPMF_cons, ENNReal.toReal_mul, geometricLetter_toReal, ih]
      simp [ValuationWord.total, pow_add]

/-- The same atom in the reciprocal-power notation used in the manuscript. -/
theorem wordPMF_toReal_length_eq_inv_pow (w : ValuationWord) :
    (wordPMF w.length w).toReal = 1 / (2 : ℝ) ^ w.total := by
  rw [wordPMF_toReal_length, div_pow, one_pow]

/-- The support is exactly all positive-letter words of the specified length. -/
theorem wordPMF_mem_support_iff (n : ℕ) (w : ValuationWord) :
    w ∈ (wordPMF n).support ↔ w.length = n := by
  rw [PMF.mem_support_iff]
  constructor
  · intro hne
    by_contra hlength
    exact hne (wordPMF_eq_zero_of_length_ne n w hlength)
  · rintro rfl hzero
    have hpos : 0 < (wordPMF w.length w).toReal := by
      rw [wordPMF_toReal_length]
      positivity
    simp [hzero] at hpos

/-- The atom formula includes its exact length-support condition. -/
theorem wordPMF_toReal (n : ℕ) (w : ValuationWord) :
    (wordPMF n w).toReal = if w.length = n then 1 / (2 : ℝ) ^ w.total else 0 := by
  by_cases h : w.length = n
  · subst n
    simp [wordPMF_toReal_length_eq_inv_pow]
  · rw [wordPMF_eq_zero_of_length_ne n w h, if_neg h, ENNReal.toReal_zero]

/-- A reference prefix and its remaining tail have the product law. -/
theorem wordPMF_map_take_drop (m n : ℕ) :
    (wordPMF (m + n)).map (fun w => (w.take m, w.drop m)) =
      (wordPMF m).bind (fun u => (wordPMF n).map (fun v => (u, v))) := by
  induction m with
  | zero =>
      rw [Nat.zero_add]
      change (wordPMF n).map (fun w => (w.take 0, w.drop 0)) =
        (PMF.pure []).bind (fun u => (wordPMF n).map (fun v => (u, v)))
      rw [PMF.pure_bind]
      congr 1
  | succ m ih =>
      rw [Nat.succ_add]
      change (geometricLetter.bind (fun a =>
          (wordPMF (m + n)).map (fun w => a :: w))).map
          (fun w => (w.take (m + 1), w.drop (m + 1))) =
        (geometricLetter.bind (fun a => (wordPMF m).map (fun w => a :: w))).bind
          (fun u => (wordPMF n).map (fun v => (u, v)))
      rw [PMF.map_bind, PMF.bind_bind]
      congr 1
      funext a
      calc
        ((wordPMF (m + n)).map (fun w => a :: w)).map
            (fun w => (w.take (m + 1), w.drop (m + 1))) =
          ((wordPMF (m + n)).map (fun w => (w.take m, w.drop m))).map
            (fun pair => (a :: pair.1, pair.2)) := by
          rw [PMF.map_comp, PMF.map_comp]
          congr 1
        _ = ((wordPMF m).bind (fun u => (wordPMF n).map (fun v => (u, v)))).map
            (fun pair => (a :: pair.1, pair.2)) := by rw [ih]
        _ = ((wordPMF m).map (fun u => a :: u)).bind
            (fun u => (wordPMF n).map (fun v => (u, v))) := by
          rw [PMF.map_bind, PMF.bind_map]
          congr 1
          funext u
          rw [PMF.map_comp]
          rfl

/-- Taking the prefix of a longer independent word gives the shorter word law. -/
theorem wordPMF_map_take (m n : ℕ) :
    (wordPMF (m + n)).map (fun w => w.take m) = wordPMF m := by
  have h := congrArg (fun p => p.map Prod.fst) (wordPMF_map_take_drop m n)
  rw [PMF.map_comp, PMF.map_bind] at h
  have hconst (u : ValuationWord) :
      ((wordPMF n).map (fun v => (u, v))).map Prod.fst = PMF.pure u := by
    rw [PMF.map_comp]
    exact PMF.map_const (wordPMF n) u
  simp_rw [hconst] at h
  simpa [Function.comp_def, PMF.bind_pure] using h

/-- Dropping a fixed reference prefix leaves the independent tail law. -/
theorem wordPMF_map_drop (m n : ℕ) :
    (wordPMF (m + n)).map (fun w => w.drop m) = wordPMF n := by
  have h := congrArg (fun p => p.map Prod.snd) (wordPMF_map_take_drop m n)
  rw [PMF.map_comp, PMF.map_bind] at h
  have htail (u : ValuationWord) :
      ((wordPMF n).map (fun v => (u, v))).map Prod.snd = wordPMF n := by
    rw [PMF.map_comp]
    exact PMF.map_id (wordPMF n)
  simp_rw [htail] at h
  simpa [Function.comp_def, PMF.bind_const] using h

/-- Projecting to any shorter reference length gives the corresponding word law. -/
theorem wordPMF_map_take_of_le {m n : ℕ} (h : m ≤ n) :
    (wordPMF n).map (fun w => w.take m) = wordPMF m := by
  simpa [Nat.add_sub_of_le h] using wordPMF_map_take m (n - m)

/-- Concatenating the independent prefix and tail recovers the whole word law. -/
theorem wordPMF_append (m n : ℕ) :
    (wordPMF m).bind (fun u => (wordPMF n).map (fun v => u ++ v)) = wordPMF (m + n) := by
  let join : ValuationWord × ValuationWord → ValuationWord := fun pair => pair.1 ++ pair.2
  have h := congrArg (fun p : PMF (ValuationWord × ValuationWord) => p.map join)
    (wordPMF_map_take_drop m n)
  rw [PMF.map_comp, PMF.map_bind] at h
  simp_rw [PMF.map_comp] at h
  have heq : (wordPMF (m + n)).map id =
      (wordPMF m).bind (fun u => (wordPMF n).map (fun v => u ++ v)) := by
    convert h using 1 <;> simp [join, Function.comp_def]
    rfl
  rw [PMF.map_id] at heq
  exact heq.symm

/-- Reversing a word preserves its atom, since length and total are unchanged. -/
theorem wordPMF_reverse_apply (n : ℕ) (w : ValuationWord) :
    wordPMF n w.reverse = wordPMF n w := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [wordPMF_toReal, List.length_reverse, ValuationWord.total_reverse]

/-- Reversal preserves the entire iid word law. -/
theorem wordPMF_map_reverse (n : ℕ) : (wordPMF n).map List.reverse = wordPMF n := by
  classical
  apply PMF.ext
  intro w
  rw [PMF.map_apply, tsum_eq_single w.reverse]
  · rw [if_pos (List.reverse_reverse w).symm, wordPMF_reverse_apply]
  · intro v hv
    have hne : w ≠ v.reverse := by
      intro h
      exact hv (by simpa using (congrArg List.reverse h).symm)
    simp [hne]

end Reference

end WordCertDensity
