/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.MacroFamilies
import WordCertDensity.Construction.GraftRealization
import WordCertDensity.Transfer.Capacity

/-! # Finite hybrid records and unique physical source charging

A record retains seed cuts, one transition word and the subsequent macro cuts.
At fixed seed and macro stage counts its full word determines the whole record.
Physical compatibility then selects exactly the actual positive histories.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- A literal seed/transition/macro record; the two lists retain their distinct cuts. -/
abbrev GraftRecord := List ValuationWord × ValuationWord × List ValuationWord

/-- The full inverse word in its original concatenation order. -/
def graftRecordWord (r : GraftRecord) : ValuationWord :=
  r.1.flatten ++ (r.2.1 ++ r.2.2.flatten)

/-- All formal hybrid histories through the given continuation stage. -/
noncomputable def graftRecords (L δ : ℝ) (b t j : ℕ) : Finset GraftRecord :=
  (seedBlockLists b 0 t).product ((graftTransitionWords δ b t).product
    (macroHistoryLists L δ (graftInitialCount b t) j))

/-- Record membership retains the actual counts, seed schedule, transition and macro schedule. -/
theorem mem_graftRecords (L δ : ℝ) (b t j : ℕ) (r : GraftRecord) :
    r ∈ graftRecords L δ b t j ↔ r.1.length = t ∧ SeedBlocks b 0 r.1 ∧
      r.2.1 ∈ graftTransitionWords δ b t ∧ r.2.2.length = j ∧
        MacroHistory L δ (graftInitialCount b t) r.2.2 := by
  rcases r with ⟨pre, w, ws⟩
  constructor
  · intro hr
    obtain ⟨hp, ht⟩ := Finset.mem_product.mp hr
    obtain ⟨hw, hm⟩ := Finset.mem_product.mp ht
    obtain ⟨hpl, hpre⟩ := (mem_seedBlockLists b 0 t pre).mp hp
    obtain ⟨hml, hmacro⟩ := (mem_macroHistoryLists L δ _ j ws).mp hm
    exact ⟨hpl, hpre, hw, hml, hmacro⟩
  · rintro ⟨hpl, hpre, hw, hml, hmacro⟩
    exact Finset.mem_product.mpr ⟨(mem_seedBlockLists b 0 t pre).mpr ⟨hpl, hpre⟩,
      Finset.mem_product.mpr ⟨hw, (mem_macroHistoryLists L δ _ j ws).mpr ⟨hml, hmacro⟩⟩⟩

/-- The complete word fixes seed cuts, the transition boundary and every later macro cut. -/
theorem graftRecords_word_injective {L δ : ℝ} {b t j : ℕ} (hb : 0 < b)
    {r s : GraftRecord} (hr : r ∈ graftRecords L δ b t j)
    (hs : s ∈ graftRecords L δ b t j) (he : graftRecordWord r = graftRecordWord s) : r = s := by
  rcases r with ⟨pre, w, ws⟩
  rcases s with ⟨other, v, vs⟩
  obtain ⟨hpl, hpre, hw, hwl, hws⟩ := (mem_graftRecords L δ b t j _).mp hr
  obtain ⟨hol, hother, hv, hvl, hvs⟩ := (mem_graftRecords L δ b t j _).mp hs
  change pre.flatten ++ (w ++ ws.flatten) = other.flatten ++ (v ++ vs.flatten) at he
  have hlen : pre.flatten.length = other.flatten.length := by
    rw [seedBlocks_depth hpre, seedBlocks_depth hother, hpl, hol]
  have hprefix : pre.flatten <+: other.flatten ++ (v ++ vs.flatten) := by
    rw [← he]
    exact List.prefix_append _ _
  have hotherprefix : other.flatten <+: other.flatten ++ (v ++ vs.flatten) :=
    List.prefix_append _ _
  have hpreword : pre.flatten = other.flatten := by
    rcases List.prefix_or_prefix_of_prefix hprefix hotherprefix with h | h
    · exact h.eq_of_length hlen
    · exact (h.eq_of_length hlen.symm).symm
  have hprecuts : pre = other := seedBlocks_flatten_injective hb hpre hother hpreword
  subst other
  have htail : w ++ ws.flatten = v ++ vs.flatten := List.append_cancel_left he
  have hpw : w <+: v ++ vs.flatten := by rw [← htail]; exact List.prefix_append _ _
  have hpv : v <+: v ++ vs.flatten := List.prefix_append _ _
  have hwv : w = v := by
    rcases List.prefix_or_prefix_of_prefix hpw hpv with h | h
    · by_contra hne
      exact graftTransitionWords_prefixFree δ b t hw hv hne h
    · by_contra hne
      exact graftTransitionWords_prefixFree δ b t hv hw (fun he => hne he.symm) h
  subst v
  have hmacro : ws = vs := macroHistory_flatten_injective hws hvs (hwl.trans hvl.symm)
    (List.append_cancel_left htail)
  subst vs
  rfl

/-- At a fixed source and total tag, two physical hybrid records are identical. -/
theorem graftRecords_unique_of_source {L δ : ℝ} {b t j root source : ℕ} (hb : 0 < b)
    {r s : GraftRecord} (hr : r ∈ graftRecords L δ b t j)
    (hs : s ∈ graftRecords L δ b t j)
    (hp : PhysicalHistory (graftRecordWord r) root source)
    (hq : PhysicalHistory (graftRecordWord s) root source)
    (htag : Transfer.historyTag (graftRecordWord r) = Transfer.historyTag (graftRecordWord s)) :
    r = s := by
  apply graftRecords_word_injective hb hr hs
  exact hp.word_eq_of_length_eq hq (congrArg Prod.fst htag)

/-- The explicit endpoint candidate is certified by physical membership. -/
def graftRecordSource (root : ℕ) (r : GraftRecord) : ℕ :=
  ⌊ValuationWord.inverseEndpoint (graftRecordWord r) root⌋₊

/-- A physical record's endpoint candidate equals its actual positive source. -/
theorem graftRecordSource_eq {root source : ℕ} {r : GraftRecord}
    (hp : PhysicalHistory (graftRecordWord r) root source) : graftRecordSource root r = source := by
  rw [graftRecordSource, hp.inverseEndpoint_eq, Nat.floor_natCast]

/-- The actual finite family retains exactly the positive physical hybrid histories. -/
noncomputable def physicalGraftRecords (L δ : ℝ) (b t j root : ℕ) : Finset GraftRecord :=
  (graftRecords L δ b t j).filter fun r => ∃ source, PhysicalHistory (graftRecordWord r) root source

/-- Physical filtering certifies the fixed source function, without selecting an arbitrary witness. -/
theorem mem_physicalGraftRecords (L δ : ℝ) (b t j root : ℕ) (r : GraftRecord) :
    r ∈ physicalGraftRecords L δ b t j root ↔ r ∈ graftRecords L δ b t j ∧
      PhysicalHistory (graftRecordWord r) root (graftRecordSource root r) := by
  simp only [physicalGraftRecords, Finset.mem_filter]
  constructor
  · rintro ⟨hr, source, hp⟩
    exact ⟨hr, by simpa only [graftRecordSource_eq hp] using hp⟩
  · rintro ⟨hr, hp⟩
    exact ⟨hr, _, hp⟩

/-- Every restriction of the actual family satisfies the within-tag uniqueness needed by capacity. -/
theorem physicalGraftRecords_source_injective {L δ : ℝ} {b t j root : ℕ} (hb : 0 < b)
    {r s : GraftRecord} (hr : r ∈ physicalGraftRecords L δ b t j root)
    (hs : s ∈ physicalGraftRecords L δ b t j root)
    (htag : Transfer.historyTag (graftRecordWord r) = Transfer.historyTag (graftRecordWord s))
    (hsource : graftRecordSource root r = graftRecordSource root s) : r = s := by
  obtain ⟨hr, hp⟩ := (mem_physicalGraftRecords L δ b t j root r).mp hr
  obtain ⟨hs, hq⟩ := (mem_physicalGraftRecords L δ b t j root s).mp hs
  rw [← hsource] at hq
  exact graftRecords_unique_of_source hb hr hs hp hq htag

/-- The actual record enumeration inherits unique physical realization after offset absorption. -/
theorem graftRecords_realizes {L δ : ℝ} {b t j root q : ℕ} (hb : 32 ^ 5 ≤ b)
    {r : GraftRecord} (hr : r ∈ graftRecords L δ b t j)
    (hpaid : graftOffsetAbsorption b t ≤ 1) (hroot : 16 ^ b ≤ root) (hodd : Odd root)
    (hq : (graftRecordWord r).length ≤ q)
    (hc : (root : ZMod (3 ^ q)) ∈ Set.range (Transfer.wordMap (graftRecordWord r) q)) :
    ∃! source : ℕ, PhysicalHistory (graftRecordWord r) root source := by
  obtain ⟨hlen, hpre, hw, _, hws⟩ := (mem_graftRecords L δ b t j r).mp hr
  exact graftTotal_realizes hb hpre hlen hw hws hpaid hroot hodd hq hc

/-- Compatibility and physical filtering agree exactly; no extra branch loss occurs. -/
theorem physicalGraftRecords_iff_compatible {L δ : ℝ} {b t j root q : ℕ}
    (hb : 32 ^ 5 ≤ b) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hroot : 16 ^ b ≤ root) (hodd : Odd root) (r : GraftRecord)
    (hq : (graftRecordWord r).length ≤ q) :
    r ∈ physicalGraftRecords L δ b t j root ↔ r ∈ graftRecords L δ b t j ∧
      (root : ZMod (3 ^ q)) ∈ Set.range (Transfer.wordMap (graftRecordWord r) q) := by
  rw [mem_physicalGraftRecords]
  constructor
  · rintro ⟨hr, hp⟩
    exact ⟨hr, ⟨(graftRecordSource root r : ZMod (3 ^ (q - (graftRecordWord r).length))),
      Transfer.wordMap_of_physical hq hp⟩⟩
  · rintro ⟨hr, hc⟩
    obtain ⟨source, hp, _⟩ := graftRecords_realizes hb hr hpaid hroot hodd hq hc
    exact ⟨hr, by simpa only [graftRecordSource_eq hp] using hp⟩

end WordCertDensity.Construction
