/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Words.Parsing

/-! # Prefix compatibility and concatenation of actual block parses -/

@[expose] public section

namespace WordCertDensity.BlockRule

/-- A prefix between complete parsed words also respects every block boundary. -/
theorem prefix_of_flatten_prefix {rule : BlockRule} {stage : ℕ}
    {blocks other : List ValuationWord} (hp : rule.Parses stage blocks)
    (hq : rule.Parses stage other) (he : blocks.flatten <+: other.flatten) :
    blocks <+: other := by
  induction blocks generalizing stage other with
  | nil => exact List.nil_prefix
  | cons b bs ih =>
      cases other with
      | nil =>
          have hz : (b :: bs).flatten = [] := List.eq_nil_of_prefix_nil he
          exact (rule.nonempty stage b hp.1
            (List.eq_nil_of_prefix_nil (by
              rw [← hz, List.flatten_cons]
              exact List.prefix_append _ _))).elim
      | cons c cs =>
          change b ++ bs.flatten <+: c ++ cs.flatten at he
          have hb : b <+: c ++ cs.flatten := (List.prefix_append _ _).trans he
          have hc : c <+: c ++ cs.flatten := List.prefix_append _ _
          have hbc : b = c := by
            rcases List.prefix_or_prefix_of_prefix hb hc with h | h
            · exact rule.prefix_eq stage b c hp.1 hq.1 h
            · exact (rule.prefix_eq stage c b hq.1 hp.1 h).symm
          subst c
          have ht := (List.prefix_append_right_inj b).mp he
          obtain ⟨tail, htail⟩ := ih hp.2 hq.2 ht
          exact ⟨tail, by simpa using congrArg (List.cons b) htail⟩

/-- A prescribed common number of prefix-free blocks excludes proper extension. -/
theorem eq_of_flatten_prefix_of_length_eq {rule : BlockRule} {stage : ℕ}
    {blocks other : List ValuationWord} (hp : rule.Parses stage blocks)
    (hq : rule.Parses stage other) (he : blocks.flatten <+: other.flatten)
    (hlen : blocks.length = other.length) : blocks = other :=
  (prefix_of_flatten_prefix hp hq he).eq_of_length hlen

/-- Concatenating valid block lists advances by the actual number of incoming blocks. -/
theorem parses_append_iff (rule : BlockRule) (stage : ℕ)
    (blocks other : List ValuationWord) :
    rule.Parses stage (blocks ++ other) ↔
      rule.Parses stage blocks ∧ rule.Parses (stage + blocks.length) other := by
  induction blocks generalizing stage with
  | nil => simp
  | cons b bs ih =>
      simp only [List.cons_append, parses_cons, ih, List.length_cons]
      have he : stage + (bs.length + 1) = stage + 1 + bs.length := by omega
      rw [he]
      exact and_assoc.symm

end WordCertDensity.BlockRule
