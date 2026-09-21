/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Analytic.MixingEnvelope
import WordCertDensity.Analytic.OscillationTriangle

/-!
# Mixing at every high conductor

The induction jumps from m to floor(10m/9). Both errors after this jump
fit inside the contracted envelope, so no adjacent-level telescoping loss
is introduced.
-/

namespace WordCertDensity.Analytic

/-- The integer jump stays in the nearby regime and exceeds the 11/10 scale. -/
theorem conductor_jump {m : ℕ} (hm : 90 ≤ m) :
    m < 10 * m / 9 ∧ 9 * (10 * m / 9) ≤ 10 * m ∧
      (11 / 10 : ℝ) * m ≤ ((10 * m / 9 : ℕ) : ℝ) := by
  have hf : 10 * m < 9 * (10 * m / 9 + 1) := by omega
  have hf' : (10 : ℝ) * m < 9 * (((10 * m / 9 : ℕ) : ℝ) + 1) := by
    exact_mod_cast hf
  have hm' : (90 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨by omega, by omega, ?_⟩
  nlinarith only [hf', hm']

/-- Every pair of high conductors satisfies the full width envelope (M.allhigh). -/
theorem all_high_oscillation_le {v : ℝ} {m n : ℕ}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hm : 2 ^ 80 ≤ m) (hmn : m ≤ n) :
    FiniteFourier.oscillation hmn (Reference.mass n) ≤ mixingEnvelope v m := by
  suffices h : ∀ d m n : ℕ, n - m = d → 2 ^ 80 ≤ m → (hmn : m ≤ n) →
      FiniteFourier.oscillation hmn (Reference.mass n) ≤ mixingEnvelope v m from
    h (n - m) m n rfl hm hmn
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro m n hd hm hmn
    have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
    by_cases heq : m = n
    · subst n
      simpa using (mixingEnvelope_pos hv hm1).le
    have hmn' : m < n := by omega
    let r := 10 * m / 9
    obtain ⟨hmr, hrnear, hrwide⟩ := conductor_jump (m := m) (by omega)
    change m < r at hmr
    change 9 * r ≤ 10 * m at hrnear
    change (11 / 10 : ℝ) * m ≤ (r : ℝ) at hrwide
    by_cases hnr : n ≤ r
    · have hnear := nearby_oscillation_le hv hv' (hm.trans hmn) hmn
        (by omega : 9 * n ≤ 10 * m)
      exact hnear.trans (mixingEnvelope_antitone hv hv' hm1 (by exact_mod_cast hmn))
    · have hrn : r < n := by omega
      have hrem : n - r < d := by omega
      have hupper := ih (n - r) hrem r n rfl (hm.trans hmr.le) hrn.le
      have hlower := nearby_oscillation_le hv hv' (hm.trans hmr.le) hmr.le hrnear
      have htriangle := FiniteFourier.oscillation_mass_triangle hmr.le hrn.le
      have hscale := mixingEnvelope_antitone hv hv'
        (by nlinarith : (1 : ℝ) < (11 / 10 : ℝ) * m) hrwide
      have hcontract := mixingEnvelope_contraction hv hv' hm1
      exact htriangle.trans (by linarith)

/-- The all-high theorem in the manuscript's full-group density normalization. -/
theorem all_high_mean_le {v : ℝ} {m n : ℕ}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hm : 2 ^ 80 ≤ m) (hmn : m ≤ n) :
    Reference.mean n (fun x =>
      |Reference.density n x - Reference.density m (Reference.project hmn x)|) ≤
        mixingEnvelope v m := by
  rw [← FiniteFourier.oscillation_mass hmn]
  exact all_high_oscillation_le hv hv' hm hmn

end WordCertDensity.Analytic
