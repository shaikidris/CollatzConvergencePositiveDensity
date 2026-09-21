/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalLanding

/-! # Geometric overshoot of the actual terminal first hit

Finite disjoint incoming-prefix events preserve their original probabilities.
Raising each next-letter threshold by K+1 gives exactly the cap-failure event.
-/

namespace WordCertDensity.Construction

/-- A specified eligible landing fails the cap exactly when its own overshoot exceeds it. -/
theorem terminalLanding_overshoot_iff {b u : ℕ} {v w : ValuationWord}
    (hv : TerminalBefore b u v) (j K : ℕ) (hp : terminalLanding b u v j <+: w) :
    TerminalOvershoot b u K w ↔ K < j := by
  have hj := (terminalLanding_mem_iff hv j j).mpr le_rfl
  constructor
  · intro h
    by_contra hle
    exact h.2 ⟨terminalLanding b u v j, (mem_terminalWords b u K _).mpr
      ((terminalLanding_mem_iff hv j K).mpr (by omega)), hp⟩
  · intro hK
    refine ⟨⟨j, terminalLanding b u v j, (mem_terminalWords b u j _).mpr hj, hp⟩, ?_⟩
    rintro ⟨z, hz, hzw⟩
    have hz' := (mem_terminalWords b u K z).mp hz
    have he : z = terminalLanding b u v j := by
      rcases List.prefix_or_prefix_of_prefix hzw hp with h | h
      · exact terminalWord_prefix_eq_caps hz' hj h
      · exact (terminalWord_prefix_eq_caps hj hz' h).symm
    rw [he] at hz'
    have hle := (terminalLanding_mem_iff hv j K).mp hz'
    omega

private theorem landing_raised (b u : ℕ) (v : ValuationWord) (K i : ℕ) :
    terminalLanding b u v (K + 1 + i) =
      v ++ [Reference.raisedLetter (Reference.raisedLetter (terminalGap b u v) (K + 1)) i] := by
  unfold terminalLanding
  apply congrArg (fun a : ℕ+ => v ++ [a])
  apply Subtype.ext
  change (terminalGap b u v : ℕ) + (K + 1 + i) =
    ((terminalGap b u v : ℕ) + (K + 1)) + i
  omega

/-- Actual cap failure is precisely the finite union of the raised next-letter tails. -/
theorem terminalOvershoot_iff_befores (b u K : ℕ) (w : ValuationWord) :
    TerminalOvershoot b u K w ↔ ∃ v ∈ terminalBefores b u,
      Reference.PrefixTail v (Reference.raisedLetter (terminalGap b u v) (K + 1)) w := by
  constructor
  · intro h
    obtain ⟨v, hv, j, hj⟩ := (terminalCrossing_iff_befores b u w).mp h.1
    have hv' := (mem_terminalBefores b u v).mp hv
    have hK := (terminalLanding_overshoot_iff hv' j K hj).mp h
    refine ⟨v, hv, j - (K + 1), ?_⟩
    rw [← landing_raised, show K + 1 + (j - (K + 1)) = j by omega]
    exact hj
  · rintro ⟨v, hv, i, hi⟩
    rw [← landing_raised] at hi
    exact (terminalLanding_overshoot_iff ((mem_terminalBefores b u v).mp hv)
      (K + 1 + i) K hi).mpr (by omega)

private theorem raised_tail_subset (v : ValuationWord) (a : ℕ+) (K : ℕ)
    {w : ValuationWord} (h : Reference.PrefixTail v (Reference.raisedLetter a (K + 1)) w) :
    Reference.PrefixTail v a w := by
  obtain ⟨i, hi⟩ := h
  refine ⟨K + 1 + i, ?_⟩
  have he : Reference.raisedLetter a (K + 1 + i) =
      Reference.raisedLetter (Reference.raisedLetter a (K + 1)) i := by
    apply Subtype.ext
    change (a : ℕ) + (K + 1 + i) = ((a : ℕ) + (K + 1)) + i
    omega
  rw [he]
  exact hi

/-- The original overshoot mass is exactly the geometric factor times uncapped crossing mass. -/
theorem terminalOvershoot_probability {b u K n : ℕ} (hn : terminalHigh b ≤ n) :
    Gated.probability (Reference.wordPMF n) (TerminalOvershoot b u K) =
      (1 / 2 : ℝ) ^ (K + 1) *
        Gated.probability (Reference.wordPMF n) (TerminalCrossing b u) := by
  classical
  let I := {v // v ∈ terminalBefores b u}
  let A (v : I) := Reference.PrefixTail v.val (terminalGap b u v.val)
  let B (v : I) := Reference.PrefixTail v.val
    (Reference.raisedLetter (terminalGap b u v.val) (K + 1))
  have hA : Gated.probability (Reference.wordPMF n) (TerminalCrossing b u) =
      ∑ v : I, Gated.probability (Reference.wordPMF n) (A v) := by
    have he : TerminalCrossing b u = fun w => ∃ v : I, A v w := by
      funext w
      apply propext
      simpa only [I, A, Subtype.exists, exists_prop] using terminalCrossing_iff_befores b u w
    rw [he]
    apply Gated.probability_union
    intro v z w hv hz
    apply Subtype.ext
    exact terminalBefore_events_unique ((mem_terminalBefores b u v.val).mp v.property)
      ((mem_terminalBefores b u z.val).mp z.property) hv hz
  have hB : Gated.probability (Reference.wordPMF n) (TerminalOvershoot b u K) =
      ∑ v : I, Gated.probability (Reference.wordPMF n) (B v) := by
    have he : TerminalOvershoot b u K = fun w => ∃ v : I, B v w := by
      funext w
      apply propext
      simpa only [I, B, Subtype.exists, exists_prop] using terminalOvershoot_iff_befores b u K w
    rw [he]
    apply Gated.probability_union
    intro v z w hv hz
    apply Subtype.ext
    exact terminalBefore_events_unique ((mem_terminalBefores b u v.val).mp v.property)
      ((mem_terminalBefores b u z.val).mp z.property)
      (raised_tail_subset _ _ K hv) (raised_tail_subset _ _ K hz)
  rw [hA, hB, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hv := (mem_terminalBefores b u v.val).mp v.property
  have hlen := hv.2.1
  exact Reference.prefixTail_probability_ratio v.val (terminalGap b u v.val) K
    (by omega)

/-- Disjoint first-hit events pay at most one geometric overshoot factor. -/
theorem terminalOvershoot_probability_le {b u K n : ℕ} (hn : terminalHigh b ≤ n) :
    Gated.probability (Reference.wordPMF n) (TerminalOvershoot b u K) ≤
      (1 / 2 : ℝ) ^ (K + 1) := by
  rw [terminalOvershoot_probability hn]
  exact mul_le_of_le_one_right (by positivity) (Gated.probability_le_one _ _)

/-- The manuscript's complete terminal deficit, with the original finite unnormalized mass. -/
theorem terminalMass_deficit {b u : ℕ} (hb : 200 ≤ b)
    (hu : u ≤ 2 * terminalRadius b) (K : ℕ) :
    1 - terminalMass b u K ≤
      2 * Real.exp (-(b : ℝ) / 64000) + (1 / 2 : ℝ) ^ (K + 1) :=
  (terminalMass_deficit_le_overshoot hb hu (le_refl (terminalHigh b))).trans
    (add_le_add le_rfl (terminalOvershoot_probability_le (u := u) (K := K)
      (le_refl (terminalHigh b))))

end WordCertDensity.Construction
