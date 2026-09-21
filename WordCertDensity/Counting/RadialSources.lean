/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Counting.ShellPacking
public import WordCertDensity.Density.RealCutoff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # All-scale source families and finite radial packing -/

@[expose] public section

namespace WordCertDensity.Counting

open Filter
open scoped BigOperators Topology

/-- Actual reciprocal-bounded odd source mass in every sufficiently large containing shell. -/
def ShellMass (G : Set ℕ) (u : ℝ) : Prop :=
  ∀ R : ℝ, 16 < R → ∀ᶠ X : ℝ in atTop,
    ∃ (S : Finset ℕ) (a : ℕ → ℝ),
      (∀ x ∈ S, Odd x ∧ x ∈ G ∧ X ≤ (x : ℝ) ∧ (x : ℝ) < R * X ∧
        0 ≤ a x ∧ a x ≤ (x : ℝ)⁻¹) ∧ u ≤ ∑ x ∈ S, a x

/-- Closure under every nonnegative number of doublings. -/
def DyadicallyClosed (G : Set ℕ) : Prop := ∀ x ∈ G, ∀ n : ℕ, 2 ^ n * x ∈ G

/-- At a fixed containing radius, each trimmed shell retains any strictly smaller limiting mass. -/
theorem eventually_trimmed_shell {G : Set ℕ} {u R v : ℝ} (h : ShellMass G u)
    (hR : 16 < R) (j : ℕ) (hj : 1 ≤ j)
    (hv : v < u - j / 2 * Real.log (R / 16)) :
    ∀ᶠ Y : ℝ in atTop, ∃ (S : Finset ℕ) (a : ℕ → ℝ),
      (∀ x ∈ S, x ∈ oddOpenBand (Y / (16 : ℝ) ^ j) 16 ∧
        x ∈ G ∧ Y / R ^ j ≤ (x : ℝ) ∧ (x : ℝ) < R * (Y / R ^ j) ∧
        0 ≤ a x ∧ a x ≤ (x : ℝ)⁻¹) ∧ v ≤ ∑ x ∈ S, a x := by
  classical
  have hRp : 0 < R := by linarith
  have hsource := (tendsto_id.atTop_div_const (by positivity : 0 < R ^ j)).eventually (h R hR)
  have hsmall : ∀ᶠ Y : ℝ in atTop, R ^ j / Y < u - j / 2 * Real.log (R / 16) - v := by
    have ht : Tendsto (fun Y : ℝ => R ^ j / Y) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (R ^ j)
    exact ht.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hsource, hsmall, eventually_gt_atTop (0 : ℝ)] with Y hsource hsmall hY
  obtain ⟨S, a, hS, hm⟩ := hsource
  refine ⟨S.filter (fun x : ℕ => Y / (16 : ℝ) ^ j < (x : ℝ)), a, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxS, hlow⟩ := Finset.mem_filter.mp hx
    obtain ⟨ho, hG, hl, hu, ha, hau⟩ := hS x hxS
    exact ⟨retained_mem_oddOpenBand hY hR.le hj ho hlow hu, hG, hl, hu, ha, hau⟩
  · have hd := radial_strip_debit S a j hY hR.le
      (fun x hx => ⟨(hS x hx).1, (hS x hx).2.2.1, (hS x hx).2.2.2.2.2⟩) hm
    linarith

/-- Finitely many trimmed shells simultaneously supply one all-cutoff integer-count lower bound. -/
theorem eventually_packed_source_count {G : Set ℕ} {u R s : ℝ} (h : ShellMass G u)
    (hclosed : DyadicallyClosed G) (hR : 16 < R) (I : Finset ℕ)
    (hI : ∀ j ∈ I, 1 ≤ j) (hs : 1 < s) (hsu : s ≤ 3 / 2)
    (hmargin : ∀ j ∈ I, Real.log s / 2 < u - j / 2 * Real.log (R / 16)) :
    ∀ᶠ Y : ℝ in atTop,
      (∑ j ∈ I, (2 * (j : ℝ) * (s - 1) * (Y / (16 : ℝ) ^ j) - 4 * j * (s + 1))) ≤
        (prefixCount G ⌊Y⌋₊ : ℝ) := by
  classical
  have hfamilies := (eventually_all_finset I).mpr
    (fun j hj => eventually_trimmed_shell h hR j (hI j hj) (hmargin j hj))
  have hscales : ∀ᶠ Y : ℝ in atTop, ∀ j ∈ I, (16 : ℝ) ^ j ≤ Y :=
    (eventually_all_finset I).mpr (fun j _ => eventually_ge_atTop ((16 : ℝ) ^ j))
  filter_upwards [hfamilies, hscales, eventually_gt_atTop (0 : ℝ)] with Y hf hscale hY
  have hex : ∀ j : ℕ, ∃ (S : Finset ℕ) (a : ℕ → ℝ), j ∈ I →
      (∀ x ∈ S, x ∈ oddOpenBand (Y / (16 : ℝ) ^ j) 16 ∧
        x ∈ G ∧ Y / R ^ j ≤ (x : ℝ) ∧ (x : ℝ) < R * (Y / R ^ j) ∧
        0 ≤ a x ∧ a x ≤ (x : ℝ)⁻¹) ∧ Real.log s / 2 ≤ ∑ x ∈ S, a x := by
    intro j
    by_cases hj : j ∈ I
    · obtain ⟨S, a, hS⟩ := hf j hj
      exact ⟨S, a, fun _ => hS⟩
    · exact ⟨∅, fun _ => 0, fun hji => (hj hji).elim⟩
  choose S a hSa using hex
  have hd := geometric_shells_disjoint I S hY (by linarith : 1 < R)
    (fun j hj x hx => ⟨((hSa j hj).1 x hx).2.2.1, ((hSa j hj).1 x hx).2.2.2.1⟩)
  exact packed_source_band_cost G I S a (fun _ => s) hclosed hd
    (fun j hj => ⟨hI j hj, hscale j hj⟩) (fun _ _ => ⟨hs, hsu⟩)
    (fun j hj x hx => ⟨((hSa j hj).1 x hx).1, ((hSa j hj).1 x hx).2.1,
      ((hSa j hj).1 x hx).2.2.2.2⟩)
    (fun j hj => (hSa j hj).2)

end WordCertDensity.Counting
