/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Words.Physical
import Mathlib.Tactic.Ring

/-!
# Chronological words and their integer affine numerator

`ForwardRealizes` is exactly a positive odd source with its finite list of
actual valuations. The natural numerator is the chronological (W.data)
numerator, distinct from the rational inverse-prefix offset.
-/

@[expose] public section

namespace WordCertDensity

namespace ValuationWord

/-- Natural additive numerator for a word read in chronological forward order. -/
def forwardNumerator : ValuationWord → ℕ
  | [] => 0
  | k :: w => 3 ^ w.length + 2 ^ (k : ℕ) * forwardNumerator w

/-- Every nonempty positive word has positive total valuation. -/
theorem total_pos_of_ne_nil {w : ValuationWord} (hw : w ≠ []) : 0 < (ValuationWord.total w) := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons k w =>
      simp only [total, List.map_cons, List.sum_cons]
      exact Nat.add_pos_left k.pos _

/-- Every nonempty chronological numerator is odd. -/
theorem forwardNumerator_odd {w : ValuationWord} (hw : w ≠ []) :
    Odd (ValuationWord.forwardNumerator w) := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons k w =>
      apply Nat.odd_iff.mpr
      simp [forwardNumerator, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, ne_of_gt k.pos]

/-- Concatenation gives the exact chronological numerator composition. -/
theorem forwardNumerator_append (u v : ValuationWord) :
    forwardNumerator (u ++ v) =
      3 ^ v.length * u.forwardNumerator + 2 ^ u.total * v.forwardNumerator := by
  induction u with
  | nil => simp [forwardNumerator, total]
  | cons k u ih =>
      simp only [List.cons_append, forwardNumerator, List.length_append, ih]
      simp only [total, List.map_cons, List.sum_cons, pow_add]
      ring

/-- Adding the last chronological letter is precisely recurrence (W.data). -/
theorem forwardNumerator_append_singleton (w : ValuationWord) (k : ℕ+) :
    forwardNumerator (w ++ [k]) =
      3 * ValuationWord.forwardNumerator w + 2 ^ ValuationWord.total w := by
  simp [forwardNumerator_append, forwardNumerator]

end ValuationWord

/-- A positive odd source realizing exactly the given chronological valuations. -/
def ForwardRealizes (w : ValuationWord) (source : ℕ) : Prop :=
  0 < source ∧ Odd source ∧
    acceleratedValuations source w.length = w.map (fun k : ℕ+ => (k : ℕ))

/-- The finite chronological valuation checks are decidable. -/
instance (w : ValuationWord) (x : ℕ) : Decidable (ForwardRealizes w x) :=
  inferInstanceAs (Decidable (0 < x ∧ Odd x ∧
    acceleratedValuations x w.length = w.map (fun k : ℕ+ => (k : ℕ))))

namespace ForwardRealizes

/-- A forward realization is a positive source. -/
theorem source_pos {w : ValuationWord} {x : ℕ} (h : ForwardRealizes w x) : 0 < x := h.1

/-- A forward realization is an odd source. -/
theorem source_odd {w : ValuationWord} {x : ℕ} (h : ForwardRealizes w x) : Odd x := h.2.1

/-- The empty word imposes only the physical source domain. -/
@[simp] theorem nil_iff (x : ℕ) : ForwardRealizes [] x ↔ 0 < x ∧ Odd x := by
  simp [ForwardRealizes, acceleratedValuations]

/-- The first exact valuation and the actual accelerated tail determine a word. -/
theorem cons_iff (k : ℕ+) (w : ValuationWord) (x : ℕ) :
    ForwardRealizes (k :: w) x ↔ 0 < x ∧ Odd x ∧ acceleratedExponent x = (k : ℕ) ∧
      ForwardRealizes w (acceleratedStep x) := by
  constructor
  · rintro ⟨hpos, hodd, hvals⟩
    simp only [List.length_cons, acceleratedValuations_cons, List.map_cons,
      List.cons.injEq] at hvals
    exact ⟨hpos, hodd, hvals.1, acceleratedStep_pos x, acceleratedStep_odd x, hvals.2⟩
  · rintro ⟨hpos, hodd, hexp, _, _, hvals⟩
    refine ⟨hpos, hodd, ?_⟩
    simp only [List.length_cons, acceleratedValuations_cons, List.map_cons]
    rw [hexp, hvals]

/-- Every finite prefix is realized by the same actual source. -/
theorem take {w : ValuationWord} {x : ℕ} (h : ForwardRealizes w x) (j : ℕ) :
    ForwardRealizes (w.take j) x := by
  induction w generalizing x j with
  | nil => simpa using h
  | cons k w ih =>
      cases j with
      | zero => exact (nil_iff x).2 ⟨h.source_pos, h.source_odd⟩
      | succ j =>
          obtain ⟨hpos, hodd, hexp, htail⟩ := (cons_iff k w x).1 h
          exact (cons_iff k (w.take j) x).2 ⟨hpos, hodd, hexp, ih htail j⟩

/-- Chronological realizations give the corresponding reversed physical inverse history. -/
theorem physical {w : ValuationWord} {x : ℕ} (h : ForwardRealizes w x) :
    PhysicalHistory w.reverse ((acceleratedStep^[w.length]) x) x := by
  induction w generalizing x with
  | nil => exact .nil x h.source_pos h.source_odd
  | cons k w ih =>
      obtain ⟨hpos, hodd, hexp, htail⟩ := (cons_iff k w x).1 h
      have hblock : PhysicalHistory [k] (acceleratedStep x) x := by
        refine .cons (acceleratedStep_pos x) (acceleratedStep_odd x) ?_ (.nil x hpos hodd)
        rw [← hexp]
        exact (pow_acceleratedExponent_mul x).symm
      simpa [Function.iterate_succ_apply] using (ih htail).append hblock

/-- The stated chronological ordinary cost is an exact iterate witness. -/
theorem reachesIn {w : ValuationWord} {x : ℕ} (h : ForwardRealizes w x) :
    ReachesIn x ((acceleratedStep^[w.length]) x) w.ordinaryCost := by
  simpa using h.physical.reachesIn

/-- The endpoint of a realized forward word is positive. -/
theorem endpoint_pos {w : ValuationWord} {x : ℕ} (h : ForwardRealizes w x) :
    0 < (acceleratedStep^[w.length]) x := h.physical.root_pos

/-- The endpoint of a realized forward word is odd. -/
theorem endpoint_odd {w : ValuationWord} {x : ℕ} (h : ForwardRealizes w x) :
    Odd ((acceleratedStep^[w.length]) x) := h.physical.root_odd

/-- Exact natural affine endpoint identity for the chronological numerator. -/
theorem affine_eq {w : ValuationWord} {x : ℕ} (h : ForwardRealizes w x) :
    2 ^ ValuationWord.total w * (acceleratedStep^[w.length]) x =
      3 ^ w.length * x + ValuationWord.forwardNumerator w := by
  induction w generalizing x with
  | nil => simp [ValuationWord.total, ValuationWord.forwardNumerator]
  | cons k w ih =>
      obtain ⟨_, _, hexp, htail⟩ := (cons_iff k w x).1 h
      have hblock : 2 ^ (k : ℕ) * acceleratedStep x = 3 * x + 1 := by
        rw [← hexp]
        exact pow_acceleratedExponent_mul x
      change 2 ^ ((k : ℕ) + (ValuationWord.total w)) *
        (acceleratedStep^[w.length + 1]) x =
          3 ^ (w.length + 1) * x + (3 ^ w.length + 2 ^ (k : ℕ) * (ValuationWord.forwardNumerator w))
      rw [pow_add, Function.iterate_succ_apply, mul_assoc, ih htail]
      calc
        2 ^ (k : ℕ) * (3 ^ w.length * acceleratedStep x + (ValuationWord.forwardNumerator w)) =
            3 ^ w.length * (2 ^ (k : ℕ) * acceleratedStep x) +
              2 ^ (k : ℕ) * (ValuationWord.forwardNumerator w) := by ring
        _ = _ := by rw [hblock, pow_succ]; ring

/-- An odd affine quotient forces the source itself to be odd. -/
theorem odd_of_affine_eq {w : ValuationWord} {x root : ℕ} (hroot : Odd root)
    (hidentity : 2 ^ w.total * root = 3 ^ w.length * x + w.forwardNumerator) : Odd x := by
  cases w with
  | nil =>
      simp only [ValuationWord.total, List.map_nil, List.sum_nil, List.length_nil,
        pow_zero, one_mul, ValuationWord.forwardNumerator, add_zero] at hidentity
      exact hidentity ▸ hroot
  | cons k w =>
      have ht := ValuationWord.total_pos_of_ne_nil (w := k :: w) (by simp)
      have hb := Nat.odd_iff.mp (ValuationWord.forwardNumerator_odd (w := k :: w) (by simp))
      have htwo : 2 ^ ValuationWord.total (k :: w) % 2 = 0 := by
        simp [Nat.pow_mod, ne_of_gt ht]
      have hthree : 3 ^ (k :: w).length % 2 = 1 := by simp [Nat.pow_mod]
      have hmod := congrArg (fun n : ℕ => n % 2) hidentity
      rw [Nat.mul_mod, htwo, zero_mul, Nat.zero_mod, Nat.add_mod,
        Nat.mul_mod, hthree, one_mul, hb] at hmod
      apply Nat.odd_iff.mpr
      omega

/-- An odd natural affine quotient realizes every intermediate valuation of the word. -/
theorem of_affine_eq {w : ValuationWord} {x root : ℕ} (hroot : Odd root)
    (hidentity : 2 ^ w.total * root = 3 ^ w.length * x + w.forwardNumerator) :
    ForwardRealizes w x := by
  have hxodd := odd_of_affine_eq hroot hidentity
  have hxpos : 0 < x := by obtain ⟨a, ha⟩ := hxodd; omega
  induction w generalizing x root with
  | nil => exact (nil_iff x).2 ⟨hxpos, hxodd⟩
  | cons k w ih =>
      have hwhole : 2 ^ (k : ℕ) * (2 ^ ValuationWord.total w * root) =
          3 ^ w.length * (3 * x + 1) + 2 ^ (k : ℕ) * ValuationWord.forwardNumerator w := by
        change 2 ^ ((k : ℕ) + ValuationWord.total w) * root =
          3 ^ (w.length + 1) * x +
            (3 ^ w.length + 2 ^ (k : ℕ) * ValuationWord.forwardNumerator w) at hidentity
        rw [pow_add, pow_succ] at hidentity
        calc
          _ = (2 ^ (k : ℕ) * 2 ^ ValuationWord.total w) * root := by ring
          _ = _ := hidentity.trans (by ring)
      have hdivproduct : 2 ^ (k : ℕ) ∣ 3 ^ w.length * (3 * x + 1) := by
        apply (Nat.dvd_add_iff_left (Nat.dvd_mul_right (2 ^ (k : ℕ))
          (ValuationWord.forwardNumerator w))).2
        rw [← hwhole]
        exact Nat.dvd_mul_right _ _
      have hcop : Nat.Coprime (2 ^ (k : ℕ)) (3 ^ w.length) :=
        (show Nat.Coprime 2 3 by decide).pow (k : ℕ) w.length
      have hdiv := hcop.dvd_of_dvd_mul_left hdivproduct
      let y := (3 * x + 1) / 2 ^ (k : ℕ)
      have hblock : 2 ^ (k : ℕ) * y = 3 * x + 1 := Nat.mul_div_cancel' hdiv
      have htail : 2 ^ ValuationWord.total w * root =
          3 ^ w.length * y + ValuationWord.forwardNumerator w := by
        apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (k : ℕ))
        calc
          _ = _ := hwhole
          _ = 3 ^ w.length * (2 ^ (k : ℕ) * y) +
              2 ^ (k : ℕ) * ValuationWord.forwardNumerator w := by rw [hblock]
          _ = _ := by ring
      have hyodd := odd_of_affine_eq hroot htail
      have hypos : 0 < y := by obtain ⟨a, ha⟩ := hyodd; omega
      refine (cons_iff k w x).2 ⟨hxpos, hxodd,
        acceleratedExponent_eq_of_odd_quotient hyodd hblock.symm, ?_⟩
      rw [acceleratedStep_eq_of_odd_quotient hyodd hblock.symm]
      exact ih hroot htail hyodd hypos

end ForwardRealizes

/-- A physical inverse history also realizes its reversed chronological word. -/
theorem PhysicalHistory.forwardRealizes {w : ValuationWord} {root x : ℕ}
    (h : PhysicalHistory w root x) : ForwardRealizes w.reverse x := by
  exact ⟨h.source_pos, h.source_odd, by simpa using h.valuations_eq_reverse⟩

end WordCertDensity
