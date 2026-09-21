/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.WhiteGap
import Mathlib.Tactic

/-! # Deterministic entry recurrence outside large triangles -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- Short crossings and fewer than K whites force all the recursively
bounded entries. The size hypothesis is pointwise on actual selected triangles. -/
theorem entries_of_shortage_small_triangles {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (j : ℕ) (l : ℤ) (w : ValuationWord) (K P R : ℕ) (u v : ℕ → ℕ)
    (hu : Monotone u) (hv : Monotone v) (hv0 : v 0 = K)
    (hstep : ∀ i, v (i + 1) = v i + u (v i) + K + 2)
    (hroom : v R + K + 2 ≤ P) (hsample : 2 * P ≤ w.length)
    (hshort : sampledWhiteStateCount n ξ j l w P < K)
    (hsmall : ∀ s, s < P → entryWordBlack n ξ j l w s →
      phaseTriangleLogSize n (entryWordTriangle hn ξ hξ j l w s).1
        (entryWordTriangle hn ξ hξ j l w s).2 ξ < (u s : ℝ)) :
    ∀ r, r ≤ R → ∃ s, s ≤ v r ∧ wordBlackEntryTime hn ξ hξ j l w r = some s := by
  intro r
  induction r with
  | zero =>
      intro _
      have hvR := hv (show 0 ≤ R by omega)
      obtain ⟨s, hs, he⟩ := first_black_soon_of_shortage n ξ j l w 0 K P
        hsample (by omega) hshort
      exact ⟨s, by omega, he⟩
  | succ r ih =>
      intro hr
      obtain ⟨s, hsv, hs⟩ := ih (by omega)
      have hvR := hv hr
      have hnext := hstep r
      have hus := hu hsv
      have hsP : s < P := by omega
      have hb := wordBlackEntryTime_spec hn ξ hξ j l w r s hs
      obtain ⟨q, hq, he⟩ := wordBlackExitTime_le_of_small_triangle hn ξ hξ j l w r s
        (u s) hs (by omega) (hsmall s hsP hb)
      obtain ⟨t, ht, hfirst⟩ := first_black_soon_of_shortage n ξ j l w q K P
        hsample (by omega) hshort
      refine ⟨t, by omega, ?_⟩
      change blackEntryTime (entryWordBlack n ξ j l w) (entryWordHeight l w)
        (fun k => (entryWordTriangle hn ξ hξ j l w k).2) (r + 1) = some t
      unfold wordBlackExitTime at he
      rw [blackEntryTime_succ, he, Option.bind_some]
      exact hfirst

end WordCertDensity.LocalPrimitive
