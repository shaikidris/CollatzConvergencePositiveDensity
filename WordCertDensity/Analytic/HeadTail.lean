/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

Option head/tail convolution and the split-PMF argument are adapted from
Lech Mazur, Copyright 2026 Lech Mazur, under Apache License 2.0. The original
LICENSE and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
The offsets, gates, iid words and raw convolution are the local definitions.
-/
module

public import WordCertDensity.Probability.Gated
public import WordCertDensity.Analytic.HeadMass
public import WordCertDensity.Analytic.AffineTail
public import WordCertDensity.Analytic.Convolution

/-!
# Exact original-word head/tail convolution

A gate inspects only the first k+1 letters. The remaining T letters keep
the unrestricted iid law, and the selected full-word mass is its raw
convolution with the original head submass.
-/

@[expose] public section

namespace WordCertDensity
namespace HeadTail

/-- Rejection stays rejected; an accepted head receives an independent additive tail. -/
noncomputable def kernel {N : ℕ} (t : PMF (ZMod N)) :
    Option (ZMod N) → PMF (Option (ZMod N))
  | none => PMF.pure none
  | some y => t.map (fun z => some (y + z))

/-- Combine an original head law with an independent, unrestricted tail. -/
noncomputable def combine {N : ℕ}
    (h : PMF (Option (ZMod N))) (t : PMF (ZMod N)) : PMF (Option (ZMod N)) :=
  h.bind (kernel t)

/-- An accepted additive-tail kernel has the literal translated tail atom. -/
theorem kernel_some {N : ℕ} (t : PMF (ZMod N)) (x y : ZMod N) :
    kernel t (some y) (some x) = t (x - y) := by
  classical
  rw [kernel, PMF.map_apply, tsum_eq_single (x - y)]
  · simp
  · intro z hz
    have hne : some x ≠ some (y + z) := by
      intro h
      apply hz
      simpa [eq_sub_iff_add_eq, add_comm] using (Option.some.inj h).symm
    simp [hne]

/-- Combining the laws gives the finite convolution in ENNReal before any conversion. -/
theorem combine_some {N : ℕ} [NeZero N]
    (h : PMF (Option (ZMod N))) (t : PMF (ZMod N)) (x : ZMod N) :
    combine h t (some x) = ∑ y, h (some y) * t (x - y) := by
  rw [combine, PMF.bind_apply, tsum_fintype, Fintype.sum_option]
  simp only [kernel, PMF.pure_apply, Option.some_ne_none, ↓reduceIte, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro y _
  rw [← kernel, kernel_some]

/-- Real-valued conversion gives the existing raw convolution, with no cardinality factor. -/
theorem combine_toReal {N : ℕ} [NeZero N]
    (h : PMF (Option (ZMod N))) (t : PMF (ZMod N)) (x : ZMod N) :
    (combine h t (some x)).toReal = FiniteFourier.convolution
      (fun y => (h (some y)).toReal) (fun z => (t z).toReal) x := by
  rw [combine_some, ENNReal.toReal_sum
    (fun y _ => ENNReal.mul_ne_top (h.apply_ne_top _) (t.apply_ne_top _))]
  simp only [ENNReal.toReal_mul, FiniteFourier.convolution]

end HeadTail
namespace HeadSlice

open scoped Classical

/-- Select a head family by inspecting only its prefix in the full word. -/
def gate (v : ℝ) (n k l : ℕ) (w : ValuationWord) : Prop :=
  Head.Gate v n k l (w.take (k + 1))

/-- The actual full iid word law, mapped to its residue when its prefix passes the gate. -/
noncomputable def law (v : ℝ) (n k l : ℕ) : PMF (Option (ZMod (3 ^ n))) :=
  Gated.law (Reference.wordPMF n) (gate v n k l) (ValuationWord.residueOffset n)

/-- Original selected full-word submass. -/
noncomputable def mass (v : ℝ) (n k l : ℕ) (x : ZMod (3 ^ n)) : ℝ :=
  (law v n k l (some x)).toReal

private noncomputable def pairKey (v : ℝ) (T k l : ℕ)
    (pair : ValuationWord × ValuationWord) : Option (ZMod (3 ^ (T + (k + 1)))) :=
  if Head.Gate v (T + (k + 1)) k l pair.1 then
    some (pair.1.residueOffset (T + (k + 1)) +
      AffineTail.embed (k + 1) T l (pair.2.residueOffset T)) else none

private theorem key_eq_pairKey (v : ℝ) (T k l : ℕ) (w : ValuationWord) :
    Gated.key (gate v (T + (k + 1)) k l) (ValuationWord.residueOffset (T + (k + 1))) w =
      pairKey v T k l (w.take (k + 1), w.drop (k + 1)) := by
  unfold Gated.key gate pairKey
  by_cases h : Head.Gate v (T + (k + 1)) k l (w.take (k + 1))
  · rw [if_pos h, if_pos h]
    apply congrArg some
    have ho := AffineTail.offset_append (w.take (k + 1)) (w.drop (k + 1)) T
    rw [h.length_eq, h.total_eq, List.take_append_drop] at ho
    exact ho
  · rw [if_neg h, if_neg h]

private theorem law_eq_pairMap (v : ℝ) (T k l : ℕ) :
    law v (T + (k + 1)) k l =
      ((Reference.wordPMF (k + 1)).bind fun h =>
        (Reference.wordPMF T).map fun t => (h, t)).map (pairKey v T k l) := by
  unfold law Gated.law
  have hkey : Gated.key (gate v (T + (k + 1)) k l)
      (ValuationWord.residueOffset (T + (k + 1))) =
      pairKey v T k l ∘ (fun w => (w.take (k + 1), w.drop (k + 1))) := by
    funext w
    exact key_eq_pairKey v T k l w
  rw [hkey, ← PMF.map_comp]
  have hsplit := Reference.wordPMF_map_take_drop (k + 1) T
  rw [Nat.add_comm (k + 1) T] at hsplit
  rw [hsplit]

private theorem pairMap_eq_kernel (v : ℝ) (T k l : ℕ) (h : ValuationWord) :
    (Reference.wordPMF T).map (fun t => pairKey v T k l (h, t)) =
      HeadTail.kernel (AffineTail.law (k + 1) T l)
        (Gated.key (Head.Gate v (T + (k + 1)) k l)
          (ValuationWord.residueOffset (T + (k + 1))) h) := by
  by_cases hg : Head.Gate v (T + (k + 1)) k l h
  · simp only [pairKey, Gated.key, hg, ↓reduceIte, HeadTail.kernel]
    rw [AffineTail.law_eq_wordPMF, PMF.map_comp]
    rfl
  · simp only [pairKey, Gated.key, hg, ↓reduceIte, HeadTail.kernel]
    exact PMF.map_const _ none

/-- The actual selected full-word PMF factors into the original head and unrestricted tail. -/
theorem law_eq_headTail (v : ℝ) (T k l : ℕ) :
    law v (T + (k + 1)) k l =
      HeadTail.combine (Head.law v (T + (k + 1)) k l) (AffineTail.law (k + 1) T l) := by
  rw [law_eq_pairMap, PMF.map_bind]
  unfold HeadTail.combine Head.law
  rw [PMF.bind_map]
  apply congrArg (PMF.bind (Reference.wordPMF (k + 1)))
  funext h
  rw [PMF.map_comp]
  exact pairMap_eq_kernel v T k l h

/-- The manuscript's exact convolution identity holds with the original full-word submass. -/
theorem mass_eq_convolution (v : ℝ) (T k l : ℕ) (x : ZMod (3 ^ (T + (k + 1)))) :
    mass v (T + (k + 1)) k l x =
      FiniteFourier.convolution (Head.mass v (T + (k + 1)) k l)
        (AffineTail.mass (k + 1) T l) x := by
  rw [mass, law_eq_headTail, HeadTail.combine_toReal]
  rfl

/-- A selected full-word submass is nonnegative. -/
theorem mass_nonneg (v : ℝ) (n k l : ℕ) (x : ZMod (3 ^ n)) :
    0 ≤ mass v n k l x := ENNReal.toReal_nonneg

end HeadSlice
end WordCertDensity
