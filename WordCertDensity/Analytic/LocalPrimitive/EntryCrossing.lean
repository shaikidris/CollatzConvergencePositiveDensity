/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.WordEntries
public import WordCertDensity.Analytic.LocalPrimitive.LongCrossing

/-! # Deterministic duration of a fixed-top crossing

Each complete reference pair increases height by at least two. This gives
an actual exit in the observed word whenever the available pairs clear the
fixed entry top, rather than assuming the exit as additional data.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

/-- A witnessed future event guarantees a first event no later than it. -/
theorem firstEventFrom_exists_le (P : ℕ → Prop) (start T : ℕ)
    (hstart : start ≤ T) (hT : P T) :
    ∃ t, t ≤ T ∧ firstEventFrom P start = some t := by
  have he : ∃ t, start ≤ t ∧ P t := ⟨T, hstart, hT⟩
  refine ⟨Nat.find he, Nat.find_min' he ⟨hstart, hT⟩, ?_⟩
  simp only [firstEventFrom, dif_pos he]

/-- Every d complete pairs contribute at least 2d to the sampled height. -/
theorem entryWordHeight_growth (l : ℤ) (w : ValuationWord) (s d : ℕ)
    (hd : 2 * (s + d) ≤ w.length) :
    entryWordHeight l w s + 2 * (d : ℤ) ≤ entryWordHeight l w (s + d) := by
  have hs : 2 * s ≤ w.length := by omega
  rw [entryWordHeight_of_sampled l w s hs, entryWordHeight_of_sampled l w (s + d) hd]
  have he : ValuationWord.total (w.take (2 * (s + d))) =
      ValuationWord.total (w.take (2 * s)) +
        ValuationWord.total ((w.drop (2 * s)).take (2 * d)) := by
    rw [Nat.mul_add, List.take_add, ValuationWord.total_append]
  have hlen : ((w.drop (2 * s)).take (2 * d)).length = 2 * d := by
    rw [List.length_take, List.length_drop]
    omega
  have htotal := valuationWord_length_le_total ((w.drop (2 * s)).take (2 * d))
  rw [hlen] at htotal
  rw [he]
  omega

/-- A fixed entry top is crossed within d sampled pairs whenever its
vertical gap is strictly less than 2d. -/
theorem wordBlackExitTime_exists_le {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r s d : ℕ)
    (hs : wordBlackEntryTime hn ξ hξ j l w r = some s)
    (hd : 0 < d) (hsample : 2 * (s + d) ≤ w.length)
    (hgap : (entryWordTriangle hn ξ hξ j l w s).2 <
      entryWordHeight l w s + 2 * (d : ℤ)) :
    ∃ t, t ≤ s + d ∧ wordBlackExitTime hn ξ hξ j l w r = some t := by
  have hgrowth := entryWordHeight_growth l w s d hsample
  have hcross : (entryWordTriangle hn ξ hξ j l w s).2 <
      entryWordHeight l w (s + d) := lt_of_lt_of_le hgap hgrowth
  obtain ⟨t, ht, he⟩ := firstEventFrom_exists_le
    (fun t => (entryWordTriangle hn ξ hξ j l w s).2 < entryWordHeight l w t)
    (s + 1) (s + d) (by omega) hcross
  refine ⟨t, ht, ?_⟩
  change (wordBlackEntryTime hn ξ hξ j l w r).bind
    (fun q => firstEventFrom
      (fun t => (entryWordTriangle hn ξ hξ j l w q).2 < entryWordHeight l w t)
      (q + 1)) = some t
  rw [hs, Option.bind_some]
  exact he

/-- The E.5 size threshold bounds the actual chosen entry's vertical gap. -/
theorem entryWordTriangle_gap_lt_twice {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (s u : ℕ) (hb : entryWordBlack n ξ j l w s)
    (hsize : phaseTriangleLogSize n (entryWordTriangle hn ξ hξ j l w s).1
      (entryWordTriangle hn ξ hξ j l w s).2 ξ < (u : ℝ)) :
    (entryWordTriangle hn ξ hξ j l w s).2 < entryWordHeight l w s + 2 * (u : ℤ) := by
  have hp := (entryWordTriangle_spec hn ξ hξ j l w s hb).2
  have ha : 2 * (entryWordTriangle hn ξ hξ j l w s).1 < n := by
    have := hp.1
    have := hb.2.1
    omega
  have hlog := (primitive_inPhaseTriangleIntMul_iff_logSize _ _ ξ hn ha hξ).mp hp
  have hhoriz : 0 ≤ ((j + s : ℕ) - (entryWordTriangle hn ξ hξ j l w s).1 : ℝ) *
      Real.log 9 := by
    apply mul_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast hp.1)
    · exact (Real.log_pos (by norm_num)).le
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hgapnonneg : 0 ≤ (entryWordTriangle hn ξ hξ j l w s).2 - entryWordHeight l w s :=
    sub_nonneg.mpr hp.2.1
  have hnat : ((entryWordTriangle hn ξ hξ j l w s).2 - entryWordHeight l w s).toNat <
      2 * u := by
    have hc := Nat.cast_nonneg
      ((entryWordTriangle hn ξ hξ j l w s).2 - entryWordHeight l w s).toNat (α := ℝ)
    have hd := hlog.2.2
    have hreal : (((entryWordTriangle hn ξ hξ j l w s).2 -
        entryWordHeight l w s).toNat : ℝ) < 2 * (u : ℝ) := by nlinarith
    exact_mod_cast hreal
  have he := Int.toNat_of_nonneg hgapnonneg
  omega

/-- Outside the large-triangle event, the actual fixed-top crossing takes
at most u+1 pairs, provided those pairs are observed in the common word. -/
theorem wordBlackExitTime_le_of_small_triangle {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r s u : ℕ)
    (hs : wordBlackEntryTime hn ξ hξ j l w r = some s)
    (hsample : 2 * (s + (u + 1)) ≤ w.length)
    (hsize : phaseTriangleLogSize n (entryWordTriangle hn ξ hξ j l w s).1
      (entryWordTriangle hn ξ hξ j l w s).2 ξ < (u : ℝ)) :
    ∃ t, t ≤ s + (u + 1) ∧ wordBlackExitTime hn ξ hξ j l w r = some t := by
  have hgap := entryWordTriangle_gap_lt_twice hn ξ hξ j l w s u
    (wordBlackEntryTime_spec hn ξ hξ j l w r s hs) hsize
  apply wordBlackExitTime_exists_le hn ξ hξ j l w r s (u + 1) hs (by omega) hsample
  omega

end WordCertDensity.LocalPrimitive
