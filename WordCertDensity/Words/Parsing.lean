/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Words.Algebra
public import Mathlib.Data.List.Basic

/-!
# Deterministic parsing of valuation blocks

The allowed blocks may depend on the stage. Nonempty, prefix-free choices at
each stage give unique parsing of a whole word, even when the number of blocks
is not specified. Concrete stopping rules must establish these hypotheses.
-/

@[expose] public section

namespace WordCertDensity

/-- A stage-dependent family of nonempty prefix-free inverse blocks. -/
structure BlockRule where
  /-- Blocks admitted at a particular construction stage. -/
  allowed : ℕ → ValuationWord → Prop
  /-- Empty blocks cannot introduce invisible extra cuts. -/
  nonempty : ∀ stage b, allowed stage b → b ≠ []
  /-- Two admitted blocks at the same stage cannot properly extend one another. -/
  prefix_eq : ∀ stage u v, allowed stage u → allowed stage v → u <+: v → u = v

namespace BlockRule

/-- A list of blocks follows the rule from its specified initial stage. -/
def Parses (rule : BlockRule) : ℕ → List ValuationWord → Prop
  | _, [] => True
  | stage, b :: bs => rule.allowed stage b ∧ rule.Parses (stage + 1) bs

/-- An empty block list is a valid completed parse. -/
@[simp] theorem parses_nil (rule : BlockRule) (stage : ℕ) : rule.Parses stage [] := trivial

/-- Parsing checks the next block and then advances the stage. -/
@[simp] theorem parses_cons (rule : BlockRule) (stage : ℕ) (b : ValuationWord)
    (bs : List ValuationWord) :
    rule.Parses stage (b :: bs) ↔ rule.allowed stage b ∧ rule.Parses (stage + 1) bs := Iff.rfl

/-- A valid parse of the empty word has no blocks. -/
theorem eq_nil_of_flatten_eq_nil {rule : BlockRule} {stage : ℕ}
    {blocks : List ValuationWord} (hp : rule.Parses stage blocks)
    (he : blocks.flatten = []) : blocks = [] := by
  cases blocks with
  | nil => rfl
  | cons b bs =>
      have hprefix : b <+: ([] : ValuationWord) := by
        rw [← he, List.flatten_cons]
        exact List.prefix_append _ _
      exact (rule.nonempty stage b hp.1 (List.eq_nil_of_prefix_nil hprefix)).elim

/-- At a fixed starting stage, the complete word determines every block boundary. -/
theorem flatten_injective {rule : BlockRule} {stage : ℕ}
    {blocks other : List ValuationWord} (hp : rule.Parses stage blocks)
    (hq : rule.Parses stage other) (he : blocks.flatten = other.flatten) :
    blocks = other := by
  induction blocks generalizing stage other with
  | nil => exact (eq_nil_of_flatten_eq_nil hq he.symm).symm
  | cons b bs ih =>
      cases other with
      | nil => exact eq_nil_of_flatten_eq_nil hp he
      | cons c cs =>
          change b ++ bs.flatten = c ++ cs.flatten at he
          have hb : b <+: c ++ cs.flatten := by
            rw [← he]
            exact List.prefix_append _ _
          have hc : c <+: c ++ cs.flatten := List.prefix_append _ _
          have hbc : b = c := by
            rcases List.prefix_or_prefix_of_prefix hb hc with h | h
            · exact rule.prefix_eq stage b c hp.1 hq.1 h
            · exact (rule.prefix_eq stage c b hq.1 hp.1 h).symm
          subst c
          exact congrArg (List.cons b) (ih hp.2 hq.2 (List.append_cancel_left he))

end BlockRule

end WordCertDensity
