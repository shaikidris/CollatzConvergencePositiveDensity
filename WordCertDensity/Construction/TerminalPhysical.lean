/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalOffset
import WordCertDensity.Transfer.Physical

/-! # Physical realization of compatible terminal words

The explicit offset guard makes residue compatibility sufficient for a unique
positive physical history. This applies before overshoot compression, at all caps.
-/

namespace WordCertDensity.Construction

/-- Every compatible terminal word has a unique positive physical source at an allowed odd parent. -/
theorem terminalWord_realizes {b u K q y : ℕ} (hb : 0 < b) {w : ValuationWord}
    (hw : TerminalWord b u K w) (hy : 16 ^ b ≤ y) (hodd : Odd y) (hq : w.length ≤ q)
    (hc : (y : ZMod (3 ^ q)) ∈ Set.range (Transfer.wordMap w q)) :
    ∃! x : ℕ, PhysicalHistory w y x := by
  have hyR : (16 : ℝ) ^ b ≤ (y : ℝ) := by exact_mod_cast hy
  have hp : (2 : ℝ) ^ b ≤ 16 ^ b := pow_le_pow_left₀ (by norm_num) (by norm_num) b
  have hoff : w.offset < (y : ℚ) := by
    apply Rat.cast_lt (K := ℝ) |>.mp
    simpa only [Rat.cast_natCast] using (terminalWord_offset hb hw).2.2.trans_le
      (hp.trans hyR)
  obtain ⟨x, hx⟩ := (Transfer.mem_range_wordMap_iff_physical w hq y hodd hoff).mp hc
  exact ⟨x, hx, fun _ hz => hz.source_unique hx⟩

/-- The actual source equals the surviving parent height times the inverse slope. -/
theorem terminalPhysical_source_eq {w : ValuationWord} {y x : ℕ}
    (h : PhysicalHistory w y x) :
    (x : ℝ) = ((y : ℝ) - (w.offset : ℝ)) / Transfer.weight w := by
  have ha : (y : ℝ) = Transfer.weight w * x + (w.offset : ℝ) := by
    have hc := congrArg (fun t : ℚ => (t : ℝ)) h.affine_eq
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Transfer.weight] using hc
  apply (eq_div_iff (ne_of_gt (Transfer.weight_pos w))).mpr
  linarith

end WordCertDensity.Construction
