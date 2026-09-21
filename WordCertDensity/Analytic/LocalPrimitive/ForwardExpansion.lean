/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.ForwardPair

/-! # Ordered forward character expansion

This module records the deterministic ordered-pair character product used in
Appendix E.  The subsequent law bridge will average this identity under the
original `Reference.wordPMF`.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The residue contribution of the next two letters at a forward state. -/
noncomputable def forwardPairOffset (n j l : ℕ) (w : ValuationWord) :
    ZMod (3 ^ n) :=
  (3 : ZMod (3 ^ n)) ^ (2 * j) * Reference.inverseTwoPow n l *
    ValuationWord.residueOffset n (w.take 2)

/-- The ordered product of the first `h` pair characters of a word. -/
noncomputable def forwardCharacterProduct (n : ℕ) (ξ : ZMod (3 ^ n)) :
    ℕ → ℕ → ℕ → ValuationWord → ℂ
  | 0, _, _, _ => 1
  | h + 1, j, l, w =>
      ZMod.stdAddChar (ξ * forwardPairOffset n j l w) *
        forwardCharacterProduct n ξ h (j + 1)
          (l + ValuationWord.total (w.take 2)) (w.drop 2)

/-- At zero pairs the ordered product is the empty character. -/
theorem forwardCharacterProduct_zero (n : ℕ) (ξ : ZMod (3 ^ n))
    (j l : ℕ) (w : ValuationWord) :
    forwardCharacterProduct n ξ 0 j l w = 1 := rfl

/-- Reading a known two-letter prefix exposes exactly its forward character
and advances the deterministic state to the remaining suffix. -/
theorem forwardCharacterProduct_succ_append_pair (n : ℕ) (ξ : ZMod (3 ^ n))
    (h j l : ℕ) (u v : ValuationWord) (hu : u.length = 2) :
    forwardCharacterProduct n ξ (h + 1) j l (u ++ v) =
      ZMod.stdAddChar (ξ * forwardPairOffset n j l u) *
        forwardCharacterProduct n ξ h (j + 1) (l + u.total) v := by
  rw [forwardCharacterProduct]
  simp only [List.take_left' hu, List.drop_left' hu]
  congr 1
  unfold forwardPairOffset
  rw [List.take_left' hu]
  rw [List.take_of_length_le hu.le]

/-- Every finite ordered forward-character product has unit norm. -/
theorem norm_forwardCharacterProduct_eq_one (n : ℕ) (ξ : ZMod (3 ^ n)) :
    ∀ (h j l : ℕ) (w : ValuationWord),
      ‖forwardCharacterProduct n ξ h j l w‖ = 1 := by
  intro h
  induction h with
  | zero => simp [forwardCharacterProduct]
  | succ h ih =>
      intro j l w
      rw [forwardCharacterProduct, norm_mul, AddChar.norm_apply,
        ih (j + 1) (l + ValuationWord.total (w.take 2)) (w.drop 2), mul_one]

/-- A canonical two-letter word has exactly its E.2 forward contribution. -/
theorem forwardPairOffset_pairWord {n j l b : ℕ} (ξ : ZMod (3 ^ n))
    (hb : 2 ≤ b) (i : Fin (b - 1)) :
    ξ * forwardPairOffset n j l (Reference.pairWord b i) =
      ξ * pairContribution n j l b i := by
  unfold forwardPairOffset
  rw [List.take_of_length_le (by simpa using (Reference.pairWord_length b i).le)]
  rw [pairContribution_eq_forwardOffset ξ hb i]
  ring

/-- For an even-length word, the ordered forward product is exactly the
additive character of its residue offset, scaled by the incoming state. -/
theorem forwardCharacterProduct_even_eq_character (n : ℕ) (ξ : ZMod (3 ^ n)) :
    ∀ (h j l : ℕ) (w : ValuationWord), w.length = 2 * h →
      forwardCharacterProduct n ξ h j l w =
        ZMod.stdAddChar
          (ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) * Reference.inverseTwoPow n l *
            ValuationWord.residueOffset n w) := by
  intro h
  induction h with
  | zero =>
      intro j l w hw
      cases w with
      | nil => simp [forwardCharacterProduct, ValuationWord.residueOffset]
      | cons a w => simp at hw
  | succ h ih =>
      intro j l w hw
      let u := w.take 2
      let v := w.drop 2
      have huv : u ++ v = w := by
        simp [u, v, List.take_append_drop]
      have hu : u.length = 2 := by
        dsimp [u]
        rw [List.length_take]
        omega
      have hv : v.length = 2 * h := by
        dsimp [v]
        rw [List.length_drop]
        omega
      rw [forwardCharacterProduct]
      rw [ih (j + 1) (l + ValuationWord.total (w.take 2)) (w.drop 2) (by simpa [v] using hv)]
      rw [← AddChar.map_add_eq_mul]
      have hres := ValuationWord.residueOffset_append n (w.take 2) (w.drop 2)
      have hresw : ValuationWord.residueOffset n w =
          ValuationWord.residueOffset n (w.take 2) +
            (3 : ZMod (3 ^ n)) ^ (w.take 2).length *
              Reference.inverseTwoPow n (ValuationWord.total (w.take 2)) *
                ValuationWord.residueOffset n (w.drop 2) := by
        simpa [u, v] using hres
      have hinv := Reference.inverseTwoPow_add n l (ValuationWord.total (w.take 2))
      rw [hresw]
      unfold forwardPairOffset
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add, hinv, hu]
      ring

/-- For an odd word, the pair product followed by its one-letter terminal
character is the fixed-conductor character of the full residue offset. -/
theorem forwardCharacterProduct_odd_with_terminal (n : ℕ) (ξ : ZMod (3 ^ n)) :
    ∀ (h j l : ℕ) (w : ValuationWord), w.length = 2 * h + 1 →
      forwardCharacterProduct n ξ h j l w *
        ZMod.stdAddChar
          (ξ * (3 : ZMod (3 ^ n)) ^ (2 * (j + h)) *
            Reference.inverseTwoPow n
              (l + ValuationWord.total (w.take (2 * h))) *
            ValuationWord.residueOffset n (w.drop (2 * h))) =
        ZMod.stdAddChar
          (ξ * (3 : ZMod (3 ^ n)) ^ (2 * j) * Reference.inverseTwoPow n l *
            ValuationWord.residueOffset n w) := by
  intro h
  induction h with
  | zero =>
      intro j l w hw
      simp [forwardCharacterProduct, ValuationWord.total]
  | succ h ih =>
      intro j l w hw
      let u := w.take 2
      let v := w.drop 2
      have hu : u.length = 2 := by
        dsimp [u]
        rw [List.length_take]
        omega
      have hv : v.length = 2 * h + 1 := by
        dsimp [v]
        rw [List.length_drop]
        omega
      rw [forwardCharacterProduct]
      have hterminal :
          ZMod.stdAddChar
              (ξ * (3 : ZMod (3 ^ n)) ^ (2 * (j + (h + 1))) *
                Reference.inverseTwoPow n
                  (l + ValuationWord.total (w.take (2 * (h + 1)))) *
                ValuationWord.residueOffset n (w.drop (2 * (h + 1))) ) =
            ZMod.stdAddChar
              (ξ * (3 : ZMod (3 ^ n)) ^ (2 * ((j + 1) + h)) *
                Reference.inverseTwoPow n
                  (l + ValuationWord.total (w.take 2) +
                    ValuationWord.total ((w.drop 2).take (2 * h))) *
                ValuationWord.residueOffset n ((w.drop 2).drop (2 * h))) := by
        congr 1
        simp only [show 2 * (h + 1) = 2 + 2 * h by omega,
          List.take_add, ValuationWord.total_append, List.drop_drop]
        ring
      rw [hterminal, mul_assoc]
      rw [ih (j + 1) (l + ValuationWord.total (w.take 2)) (w.drop 2)
        (by simpa [v] using hv)]
      rw [← AddChar.map_add_eq_mul]
      have hres := ValuationWord.residueOffset_append n (w.take 2) (w.drop 2)
      have hresw : ValuationWord.residueOffset n w =
          ValuationWord.residueOffset n (w.take 2) +
            (3 : ZMod (3 ^ n)) ^ (w.take 2).length *
              Reference.inverseTwoPow n (ValuationWord.total (w.take 2)) *
                ValuationWord.residueOffset n (w.drop 2) := by
        simpa [u, v] using hres
      have hinv := Reference.inverseTwoPow_add n l (ValuationWord.total (w.take 2))
      rw [hresw]
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add, hinv, hu]
      unfold forwardPairOffset
      ring

end WordCertDensity.LocalPrimitive
