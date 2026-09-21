/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryTimes

/-! # Prefix stability of the inclusive entry process

A recorded event at time t depends only on blackness, height, and entry tops
through t. No agreement of the future, or future existence of events, is used.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- A first event at t is unchanged when predicates agree only through t. -/
theorem firstEventFrom_prefix_congr (P Q : ℕ → Prop) (start t : ℕ)
    (hPQ : ∀ s, s ≤ t → (P s ↔ Q s)) :
    firstEventFrom P start = some t ↔ firstEventFrom Q start = some t := by
  rw [firstEventFrom_eq_some_iff, firstEventFrom_eq_some_iff]
  constructor
  · rintro ⟨hst, ht, hmin⟩
    refine ⟨hst, (hPQ t le_rfl).mp ht, ?_⟩
    intro s hs hst' hq
    exact hmin s hs hst' ((hPQ s (Nat.le_of_lt hst')).mpr hq)
  · rintro ⟨hst, ht, hmin⟩
    refine ⟨hst, (hPQ t le_rfl).mpr ht, ?_⟩
    intro s hs hst' hp
    exact hmin s hs hst' ((hPQ s (Nat.le_of_lt hst')).mp hp)

/-- Transfer a recorded entry using agreement up to a fixed horizon only. -/
theorem blackEntryTime_transfer_prefix (black black' : ℕ → Prop)
    (height height' top top' : ℕ → ℤ) (T : ℕ)
    (hb : ∀ q, q ≤ T → (black q ↔ black' q))
    (hh : ∀ q, q ≤ T → height q = height' q)
    (hp : ∀ q, q ≤ T → top q = top' q) (r s : ℕ) (hsT : s ≤ T)
    (hs : blackEntryTime black height top r = some s) :
    blackEntryTime black' height' top' r = some s := by
  induction r generalizing s with
  | zero =>
      exact (firstEventFrom_prefix_congr black black' 0 s
        (fun q hq => hb q (Nat.le_trans hq hsT))).mp hs
  | succ r ih =>
      rw [blackEntryTime_succ] at hs ⊢
      obtain ⟨t, ht, hlast⟩ := Option.bind_eq_some_iff.mp hs
      obtain ⟨a, ha, hcross⟩ := Option.bind_eq_some_iff.mp ht
      have hts := ((firstEventFrom_eq_some_iff _ _ _).mp hlast).1
      have hat := ((firstEventFrom_eq_some_iff _ _ _).mp hcross).1
      have haT : a ≤ T := by omega
      have htT : t ≤ T := by omega
      have ha' := ih a haT ha
      have hcross' : firstEventFrom (fun q => top' a < height' q) (a + 1) = some t := by
        apply (firstEventFrom_prefix_congr _ _ (a + 1) t ?_).mp hcross
        intro q hq
        rw [hp a haT, hh q (Nat.le_trans hq htT)]
      have hlast' := (firstEventFrom_prefix_congr black black' t s
        (fun q hq => hb q (Nat.le_trans hq hsT))).mp hlast
      apply Option.bind_eq_some_iff.mpr
      refine ⟨t, ?_, hlast'⟩
      exact Option.bind_eq_some_iff.mpr ⟨a, ha', hcross'⟩

/-- Recorded entries are determined by the observed prefix. -/
theorem blackEntryTime_prefix_congr (black black' : ℕ → Prop)
    (height height' top top' : ℕ → ℤ) (T : ℕ)
    (hb : ∀ q, q ≤ T → (black q ↔ black' q))
    (hh : ∀ q, q ≤ T → height q = height' q)
    (hp : ∀ q, q ≤ T → top q = top' q) (r s : ℕ) (hsT : s ≤ T) :
    blackEntryTime black height top r = some s ↔
      blackEntryTime black' height' top' r = some s :=
  ⟨blackEntryTime_transfer_prefix black black' height height' top top' T hb hh hp r s hsT,
    blackEntryTime_transfer_prefix black' black height' height top' top T
      (fun q hq => (hb q hq).symm) (fun q hq => (hh q hq).symm)
      (fun q hq => (hp q hq).symm) r s hsT⟩

/-- Transfer a strict fixed-top exit using only the prefix through that exit. -/
theorem blackExitTime_transfer_prefix (black black' : ℕ → Prop)
    (height height' top top' : ℕ → ℤ) (T : ℕ)
    (hb : ∀ q, q ≤ T → (black q ↔ black' q))
    (hh : ∀ q, q ≤ T → height q = height' q)
    (hp : ∀ q, q ≤ T → top q = top' q) (r t : ℕ) (htT : t ≤ T)
    (ht : blackExitTime black height top r = some t) :
    blackExitTime black' height' top' r = some t := by
  obtain ⟨a, ha, hcross⟩ := Option.bind_eq_some_iff.mp ht
  have hat := ((firstEventFrom_eq_some_iff _ _ _).mp hcross).1
  have haT : a ≤ T := by omega
  have ha' := blackEntryTime_transfer_prefix black black' height height' top top'
    T hb hh hp r a haT ha
  apply Option.bind_eq_some_iff.mpr
  refine ⟨a, ha', ?_⟩
  apply (firstEventFrom_prefix_congr _ _ (a + 1) t ?_).mp hcross
  intro q hq
  rw [hp a haT, hh q (Nat.le_trans hq htT)]

/-- Recorded exits, as well as entries, are prefix determined. -/
theorem blackExitTime_prefix_congr (black black' : ℕ → Prop)
    (height height' top top' : ℕ → ℤ) (T : ℕ)
    (hb : ∀ q, q ≤ T → (black q ↔ black' q))
    (hh : ∀ q, q ≤ T → height q = height' q)
    (hp : ∀ q, q ≤ T → top q = top' q) (r t : ℕ) (htT : t ≤ T) :
    blackExitTime black height top r = some t ↔
      blackExitTime black' height' top' r = some t :=
  ⟨blackExitTime_transfer_prefix black black' height height' top top' T hb hh hp r t htT,
    blackExitTime_transfer_prefix black' black height' height top' top T
      (fun q hq => (hb q hq).symm) (fun q hq => (hh q hq).symm)
      (fun q hq => (hp q hq).symm) r t htT⟩

end WordCertDensity.LocalPrimitive
