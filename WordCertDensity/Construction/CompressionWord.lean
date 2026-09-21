/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalLanding
import WordCertDensity.Words.LastValuation

/-! # Exact even-overshoot compression of terminal words

The landing decomposition supplies a strictly positive barrier gap. Reduction
therefore never activates the artificial lower clamp. Overshoot modulo two
is retained, and the removed quotient is the recovery index.
-/

namespace WordCertDensity.Construction

/-- Half the original nonnegative overshoot, rounded down. -/
def compressionIndex (b u : ℕ) (w : ValuationWord) : ℕ :=
  ((w.total : ℤ)-terminalBarrier b u w.length).toNat/2

/-- The literal last-valuation reduction in the prepared target. -/
def compressWord (w : ValuationWord) (j : ℕ) : ValuationWord :=
  ValuationWord.reduceLast w j

/-- Every retained word has an eligible prefix and a unique displayed overshoot. -/
theorem terminalWord_landing_decompose {b u K : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) :
    ∃ v O, TerminalBefore b u v ∧ O ≤ K ∧ w = terminalLanding b u v O := by
  have hn := terminalWord_nonempty hw
  have he := List.dropLast_append_getLast hn
  have hw' : TerminalWord b u K (w.dropLast ++ [w.getLast hn]) := by rw [he]; exact hw
  obtain ⟨O, hO, hlanding⟩ := terminalWord_append_decompose hw'
  exact ⟨w.dropLast, O, terminalWord_before hw', hO, he.symm.trans hlanding⟩

/-- On a landing the index is exactly the ordinary quotient of its overshoot. -/
theorem compressionIndex_landing {b u : ℕ} {v : ValuationWord}
    (hv : TerminalBefore b u v) (O : ℕ) :
    compressionIndex b u (terminalLanding b u v O) = O/2 := by
  rw [compressionIndex, terminalLanding_overshoot hv, Int.toNat_natCast]

/-- The final positive gap survives subtraction and the overshoot becomes its parity. -/
theorem compressWord_landing (b u : ℕ) (v : ValuationWord) (O : ℕ) :
    compressWord (terminalLanding b u v O) (O/2) = terminalLanding b u v (O%2) := by
  rw [compressWord, terminalLanding, ValuationWord.reduceLast_append]
  apply congrArg (fun a : ℕ+ => v ++ [a])
  apply Subtype.ext
  change max 1 (((terminalGap b u v : ℕ)+O)-2*(O/2)) = (terminalGap b u v : ℕ)+O%2
  have hg : 1 ≤ (terminalGap b u v : ℕ) := (terminalGap b u v).property
  have hO := Nat.mod_add_div O 2
  omega

/-- Raising a landing's last valuation adds precisely twice the retained index. -/
theorem raiseLast_landing (b u : ℕ) (v : ValuationWord) (O j : ℕ) :
    ValuationWord.raiseLast (terminalLanding b u v O) j = terminalLanding b u v (O+2*j) := by
  rw [terminalLanding, ValuationWord.raiseLast_append]
  apply congrArg (fun a : ℕ+ => v ++ [a])
  apply Subtype.ext
  change (terminalGap b u v : ℕ)+O+2*j = (terminalGap b u v : ℕ)+(O+2*j)
  omega

/-- Every retained word compresses to the same terminal event with overshoot at most one. -/
theorem compressWord_terminal {b u K : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) :
    TerminalWord b u 1 (compressWord w (compressionIndex b u w)) := by
  obtain ⟨v, O, hv, _, rfl⟩ := terminalWord_landing_decompose hw
  rw [compressionIndex_landing hv, compressWord_landing]
  exact (terminalLanding_mem_iff hv (O%2) 1).mpr (by omega)

/-- The reduced word and fan index recover the complete original word. -/
theorem compressWord_recover {b u K : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) :
    ValuationWord.raiseLast (compressWord w (compressionIndex b u w))
      (compressionIndex b u w) = w := by
  obtain ⟨v, O, hv, _, rfl⟩ := terminalWord_landing_decompose hw
  rw [compressionIndex_landing hv, compressWord_landing, raiseLast_landing]
  congr 1
  omega

/-- Compression is injective while its fan index is retained, even across different caps. -/
theorem compression_injective {b u K M : ℕ} {v w : ValuationWord}
    (hv : TerminalWord b u K v) (hw : TerminalWord b u M w)
    (he : (compressWord v (compressionIndex b u v), compressionIndex b u v) =
      (compressWord w (compressionIndex b u w), compressionIndex b u w)) : v = w := by
  have h := congrArg (fun p : ValuationWord × ℕ => ValuationWord.raiseLast p.1 p.2) he
  simpa only [compressWord_recover hv, compressWord_recover hw] using h

/-- The exact total reduction pays two valuation units for each fan index. -/
theorem compression_total {b u K : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) :
    w.total = (compressWord w (compressionIndex b u w)).total + 2*compressionIndex b u w := by
  obtain ⟨v, O, hv, _, rfl⟩ := terminalWord_landing_decompose hw
  rw [compressionIndex_landing hv, compressWord_landing]
  simp only [terminalLanding, ValuationWord.total_append]
  change v.total+((terminalGap b u v : ℕ)+O) =
    v.total+((terminalGap b u v : ℕ)+O%2)+2*(O/2)
  omega

/-- Original reference weights retain exactly the factor four to the negative fan index. -/
theorem compression_reference_weight {b u K : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) :
    (2 : ℝ)^(-(w.total : ℤ)) = (4 : ℝ)^(-(compressionIndex b u w : ℤ))*
      (2 : ℝ)^(-((compressWord w (compressionIndex b u w)).total : ℤ)) := by
  simp only [zpow_neg, zpow_natCast]
  rw [compression_total hw, pow_add, pow_mul, mul_inv_rev]
  norm_num

end WordCertDensity.Construction
