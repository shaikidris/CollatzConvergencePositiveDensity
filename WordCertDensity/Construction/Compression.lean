/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.CompressionWord
import WordCertDensity.Construction.SeedHistories
import WordCertDensity.Words.EvenReduction
import WordCertDensity.Transfer.Composition

/-! # Physical overshoot compression with its recovery index

The earlier physical prefix is reused unchanged. The final even reduction
preserves admissibility, positive odd endpoints, exact source and both weight
conventions. The reduced terminal word and fan index recover the original.
-/

namespace WordCertDensity.Construction

/-- Every compression preserves the exact inverse depth. -/
theorem compression_length (w : ValuationWord) (j : ℕ) :
    (compressWord w j).length = w.length := ValuationWord.reduceLast_length w j

/-- The entire earlier word, before its final valuation, is unchanged. -/
theorem compression_dropLast {b u K : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) :
    (compressWord w (compressionIndex b u w)).dropLast = w.dropLast := by
  obtain ⟨v, O, hv, _, rfl⟩ := terminalWord_landing_decompose hw
  rw [compressionIndex_landing hv, compressWord_landing]
  simp [terminalLanding]

/-- The reduced physical word retains the old parent and has the exact affine fan source. -/
theorem compressWord_physical {b u K y x : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) (hp : PhysicalHistory w y x) :
    ∃ z, PhysicalHistory (compressWord w (compressionIndex b u w)) y z ∧
      x = fanSource (compressionIndex b u w) z := by
  obtain ⟨v, O, hv, _, rfl⟩ := terminalWord_landing_decompose hw
  rw [compressionIndex_landing hv, compressWord_landing]
  have hp' : PhysicalHistory (v ++ [Reference.raisedLetter (terminalGap b u v) O]) y x := hp
  obtain ⟨middle, hprefix, hlast⟩ := hp'.append_split
  have he : Reference.raisedLetter (terminalGap b u v) O =
      Reference.raisedLetter (Reference.raisedLetter (terminalGap b u v) (O%2))
        (2*(O/2)) := by
    apply Subtype.ext
    change (terminalGap b u v : ℕ)+O =
      ((terminalGap b u v : ℕ)+O%2)+2*(O/2)
    omega
  rw [he] at hlast
  obtain ⟨z, hz, hx⟩ := hlast.raisedLetter_even_reduce
  exact ⟨z, hprefix.append hz, hx⟩

/-- Compression changes the complete physical word weight by precisely four to the index. -/
theorem compression_physical_weight {b u K : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) :
    Transfer.weight w = (4 : ℝ)^(-(compressionIndex b u w : ℤ))*
      Transfer.weight (compressWord w (compressionIndex b u w)) := by
  have h := compression_reference_weight hw
  simp only [zpow_neg, zpow_natCast] at h ⊢
  rw [Transfer.weight_eq, Transfer.weight_eq, compression_length]
  simp only [div_eq_mul_inv]
  rw [h]
  ring

/-- Removing the even excess also removes exactly that many ordinary steps. -/
theorem compression_clock {b u K : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) :
    w.ordinaryCost = (compressWord w (compressionIndex b u w)).ordinaryCost +
      2*compressionIndex b u w := by
  have ht := compression_total hw
  have hl := compression_length w (compressionIndex b u w)
  unfold ValuationWord.ordinaryCost
  omega

/-- Full physical compression, with the literal quotient source and original reference weight. -/
theorem terminal_physical_compression {b u K y x : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) (hp : PhysicalHistory w y x) :
    let j := compressionIndex b u w
    let v := compressWord w j
    TerminalWord b u 1 v ∧ ∃ z : ℕ, PhysicalHistory v y z ∧
      x=4^j*z+(4^j-1)/3 ∧
      (2 : ℝ)^(-(w.total : ℤ)) = (4 : ℝ)^(-(j : ℤ))*(2 : ℝ)^(-(v.total : ℤ)) := by
  obtain ⟨z, hz, hx⟩ := compressWord_physical hw hp
  exact ⟨compressWord_terminal hw, z, hz, (hx.trans (fanSource_eq _ _)),
    compression_reference_weight hw⟩

end WordCertDensity.Construction
