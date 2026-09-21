/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftRecords

/-! # Identifying a graft before an arbitrary terminal suffix

The seed length, transition stopping rule and macro stopping rules determine
all boundaries even when the complete word has a further suffix.
-/

namespace WordCertDensity.Construction

/-- Appending arbitrary terminal words does not conceal any graft boundary. -/
theorem graftRecords_append_injective {L δ : ℝ} {b t j : ℕ} (hb : 0 < b)
    {r s : GraftRecord} {u v : ValuationWord}
    (hr : r ∈ graftRecords L δ b t j) (hs : s ∈ graftRecords L δ b t j)
    (he : graftRecordWord r ++ u = graftRecordWord s ++ v) : r = s ∧ u = v := by
  rcases r with ⟨pre, w, ws⟩
  rcases s with ⟨other, z, zs⟩
  obtain ⟨hpl, hpre, hw, hwl, hws⟩ := (mem_graftRecords L δ b t j _).mp hr
  obtain ⟨hol, hother, hz, hzl, hzs⟩ := (mem_graftRecords L δ b t j _).mp hs
  change (pre.flatten ++ (w ++ ws.flatten)) ++ u =
    (other.flatten ++ (z ++ zs.flatten)) ++ v at he
  simp only [List.append_assoc] at he
  have hlen : pre.flatten.length = other.flatten.length := by
    rw [seedBlocks_depth hpre, seedBlocks_depth hother, hpl, hol]
  have hp : pre.flatten <+: other.flatten ++ (z ++ (zs.flatten ++ v)) := by
    rw [← he]
    exact List.prefix_append _ _
  have hq : other.flatten <+: other.flatten ++ (z ++ (zs.flatten ++ v)) :=
    List.prefix_append _ _
  have hpreword : pre.flatten = other.flatten := by
    rcases List.prefix_or_prefix_of_prefix hp hq with h | h
    · exact h.eq_of_length hlen
    · exact (h.eq_of_length hlen.symm).symm
  have hprecuts : pre = other := seedBlocks_flatten_injective hb hpre hother hpreword
  subst other
  have ht : w ++ (ws.flatten ++ u) = z ++ (zs.flatten ++ v) :=
    List.append_cancel_left he
  have hpw : w <+: z ++ (zs.flatten ++ v) := by rw [← ht]; exact List.prefix_append _ _
  have hpz : z <+: z ++ (zs.flatten ++ v) := List.prefix_append _ _
  have hwz : w = z := by
    rcases List.prefix_or_prefix_of_prefix hpw hpz with h | h
    · by_contra hne
      exact graftTransitionWords_prefixFree δ b t hw hz hne h
    · by_contra hne
      exact graftTransitionWords_prefixFree δ b t hz hw (fun he => hne he.symm) h
  subst z
  have hm : ws.flatten ++ u = zs.flatten ++ v := List.append_cancel_left ht
  have hpws : ws.flatten <+: zs.flatten ++ v := by rw [← hm]; exact List.prefix_append _ _
  have hpzs : zs.flatten <+: zs.flatten ++ v := List.prefix_append _ _
  have hmacro : ws = zs := by
    rcases List.prefix_or_prefix_of_prefix hpws hpzs with h | h
    · exact macroHistory_eq_of_prefix hws hzs (hwl.trans hzl.symm) h
    · exact (macroHistory_eq_of_prefix hzs hws (hzl.trans hwl.symm) h).symm
  subst zs
  exact ⟨rfl, List.append_cancel_left hm⟩

end WordCertDensity.Construction
