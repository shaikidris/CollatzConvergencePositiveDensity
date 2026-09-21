/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.ProductMomentSplit
public import WordCertDensity.Analytic.LocalPrimitive.TerminalGeometry
public import WordCertDensity.Analytic.LocalPrimitive.PostPassageProduct
public import WordCertDensity.Analytic.LocalPrimitive.PassageLaw
public import WordCertDensity.Analytic.LocalPrimitive.PassageExpectation
import Mathlib.Tactic

/-! # The original-law long-exit comparison -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- White states cut off at the terminal column; all later pair factors are
neutral, so a short potential can be represented on any longer source horizon. -/
def cutoffWhite (N : ℕ) (white : ℕ → ℤ → Prop) (j : ℕ) (l : ℤ) : Prop :=
  j < N ∧ white j l

private theorem cutoffProduct_tail_one (N r j : ℕ) (white : ℕ → ℤ → Prop)
    (z : ℝ≥0∞) (l : ℤ) (hN : N ≤ j) (w : ValuationWord) :
    whiteWindowProduct (cutoffWhite N white) z r j l w = 1 := by
  induction r generalizing j l w with
  | zero => rfl
  | succ r ih =>
      rw [whiteWindowProduct]
      have hfalse : ¬ cutoffWhite N white j l := by
        intro h
        exact (Nat.not_lt_of_ge hN h.1)
      rw [if_neg (by simp [hfalse]), ih (j + 1)
        (l + ValuationWord.total (w.take 2)) (by omega) (w.drop 2)]
      simp

/-- The cutoff product agrees with the actual product through the terminal
column and contributes no later factors. -/
theorem cutoffProduct_eq (N m L j : ℕ) (white : ℕ → ℤ → Prop)
    (z : ℝ≥0∞) (l : ℤ) (w : ValuationWord)
    (hjm : j + m = N) (hmL : m ≤ L) :
    whiteWindowProduct (cutoffWhite N white) z L j l w =
      whiteWindowProduct white z m j l w := by
  rw [← Nat.add_sub_of_le hmL, whiteWindowProduct_add]
  have hfirst : whiteWindowProduct (cutoffWhite N white) z m j l w =
      whiteWindowProduct white z m j l w := by
    apply whiteWindowProduct_congr_columns
    intro t ht b
    have hbefore : j + t < N := by omega
    simp only [cutoffWhite, hbefore, true_and]
  rw [hfirst]
  rw [cutoffProduct_tail_one N (L - m) (j + m) white z
    (l + ValuationWord.total (w.take (2 * m))) (by omega) (w.drop (2 * m))]
  simp

/-- The cutoff potential is exactly the literal phase potential at every
longer horizon. -/
theorem cutoffPotential_eq_phase {n m L j : ℕ}
    (ξ : ZMod (3 ^ n)) (l : ℤ) (hjm : j + m = n / 2)
    (hmL : m ≤ L) :
    integerPairPotential localEpsilon (cutoffWhite (n / 2)
      (phaseWhiteAtInt n ξ)) L j l =
      phaseRemainingPotential n ξ (n / 2) m l := by
  have hmN : m ≤ n / 2 := by omega
  rw [← whiteWindowProduct_eq_integerPairPotential localEpsilon_guard,
    phaseRemainingPotential_eq_product n m ξ l hmN]
  congr 1
  have hcut :
      (∑' w : ValuationWord, Reference.wordPMF (2 * L) w *
        whiteWindowProduct (cutoffWhite (n / 2) (phaseWhiteAtInt n ξ))
          (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) L j l w) =
      ∑' w : ValuationWord, Reference.wordPMF (2 * L) w *
        whiteWindowProduct (phaseWhiteAtInt n ξ)
          (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) m j l w := by
    apply tsum_congr
    intro w
    rw [cutoffProduct_eq (n / 2) m L j (phaseWhiteAtInt n ξ)
      (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) l w hjm hmL]
  rw [hcut]
  rw [← whiteWindowProduct_moment_horizon (phaseWhiteAtInt n ξ)
    (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) m L j l hmL]
  have hj' : j = n / 2 - m := by omega
  rw [hj']
  apply tsum_congr
  intro w
  rw [phaseProduct_eq_extended n ξ _ m (n / 2 - m) l w (by omega)]

/- The exact prefix factorization used below keeps the original source law and
reduces the unused tail horizon to the fixed P-window. -/
theorem postPassageProductMoment_prefix_factor (n : ℕ) (ξ : ZMod (3 ^ n))
    (s j : ℕ) (l : ℤ) (B L : ℕ)
    (hL : s / 2 + 1 + localPrimitiveP B ≤ L) :
    postPassageProductMoment n ξ s j l B L
      (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) =
      ∑' u : passagePrefixFamily s,
        Reference.wordPMF (u : ValuationWord).length u *
          (∑' v : ValuationWord,
            Reference.wordPMF (2 * (L - (u : ValuationWord).length / 2)) v *
              whiteWindowProduct (extendedPhaseWhite n ξ)
                (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))
                (localPrimitiveP B)
                (j + (u : ValuationWord).length / 2)
                (l + (u : ValuationWord).total) v) := by
  unfold postPassageProductMoment
  rw [countableStoppedMoment_factor (passagePrefixFamily s) (2 * L)
    (fun u v => whiteWindowProduct (extendedPhaseWhite n ξ)
      (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) (localPrimitiveP B)
      (j + u.length / 2) (l + u.total) v)
    (fun u hu => by have := passagePrefixFamily_length s u hu; omega)]
  apply tsum_congr
  intro u
  obtain ⟨i, hlen, hi⟩ := u.property
  have hidx := i.isLt
  have hq : (u : ValuationWord).length / 2 = (i : ℕ) + 1 := by omega
  have hrem : 2 * L - (u : ValuationWord).length =
      2 * (L - (u : ValuationWord).length / 2) := by omega
  rw [hrem]

end WordCertDensity.LocalPrimitive

namespace WordCertDensity.LocalPrimitive

/-- After a nonterminal passage, the cutoff potential is paid by the first
P-pair product and the preceding-layer bound. -/
theorem cutoffPotential_nonterminal_le {n m L j q P : ℕ}
    (ξ : ZMod (3 ^ n)) (l : ℤ) (B : ℕ) (D : ℝ)
    (hjm : j + m = n / 2) (hm : 0 < m) (hP : 0 < P) (hmL : m ≤ L)
    (hnotlate : 10 * (q + P) ≤ 9 * m)
    (hfuture : ∀ r, r < m → ∀ l',
      layerWeight B r * phaseRemainingPotential n ξ (n / 2) r l' ≤ D) :
    integerPairPotential localEpsilon (cutoffWhite (n / 2)
      (phaseWhiteAtInt n ξ)) (L - q) (j + q) l ≤
      (D * (10 : ℝ) ^ B / layerWeight B m) *
        (∑' v : ValuationWord, Reference.wordPMF (2 * P) v *
          whiteWindowProduct (extendedPhaseWhite n ξ)
            (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) P (j + q) l v).toReal := by
  have hqP : q + P ≤ m := by omega
  have hr : m - q - P < m := by
    omega
  have hrem : L - q = P + (L - q - P) := by omega
  have hweight : layerWeight B m ≤ (10 : ℝ) ^ B * layerWeight B (m - q - P) := by
    have hbase : (m : ℝ) ≤ 10 * (m - q - P : ℕ) := by
      have : m ≤ 10 * (m - q - P) := by omega
      exact_mod_cast this
    have hrmax : ((m - q - P : ℕ) : ℝ) ≤ max ((m - q - P : ℕ) : ℝ) 1 :=
      le_max_left _ _
    have h1max : (1 : ℝ) ≤ max ((m - q - P : ℕ) : ℝ) 1 := le_max_right _ _
    have hmax : max (m : ℝ) 1 ≤ 10 * max ((m - q - P : ℕ) : ℝ) 1 := by
      apply max_le
      · have h10 := mul_le_mul_of_nonneg_left hrmax (by norm_num : (0 : ℝ) ≤ 10)
        exact hbase.trans h10
      · nlinarith
    have hp := pow_le_pow_left₀ (by positivity :
      0 ≤ max (m : ℝ) 1) hmax B
    unfold layerWeight
    simpa only [mul_pow] using hp
  have hwm : 0 < layerWeight B m := layerWeight_pos B m
  have hUbound (v : ValuationWord) :
      integerPairPotential localEpsilon (cutoffWhite (n / 2)
        (phaseWhiteAtInt n ξ)) (L - q - P)
        (j + q + P) (l + v.total) ≤
        D * (10 : ℝ) ^ B / layerWeight B m := by
    have hphase := cutoffPotential_eq_phase (n := n) (m := m - q - P)
      (L := L - q - P) (j := j + q + P) ξ (l + v.total)
      (by omega) (by omega)
    rw [hphase]
    have hf := hfuture (m - q - P) hr (l + v.total)
    have hp10 : 0 ≤ (10 : ℝ) ^ B := by positivity
    apply (le_div_iff₀ hwm).mpr
    have hscaled := mul_le_mul_of_nonneg_right hf hp10
    have hu0 := (phaseRemainingPotential_mem_unitInterval n (n / 2)
      (m - q - P) ξ (l + v.total)).1
    have hprod := mul_le_mul_of_nonneg_right hweight hu0
    nlinarith
  have hD : 0 ≤ D := by
    have hf := hfuture 0 hm 0
    rw [phaseRemainingPotential_zero] at hf
    have hw := layerWeight_pos B 0
    nlinarith
  rw [hrem, integerPairPotential_add localEpsilon_guard
    (cutoffWhite (n / 2) (phaseWhiteAtInt n ξ)) P (L - q - P)
    (j + q) l]
  have hsum : Summable (fun v : ValuationWord =>
      (Reference.wordPMF (2 * P) v).toReal) :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  have hleft : Summable (fun v : ValuationWord =>
      (Reference.wordPMF (2 * P) v).toReal *
        (whiteWindowProduct (cutoffWhite (n / 2) (phaseWhiteAtInt n ξ))
          (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) P (j + q) l v).toReal *
        integerPairPotential localEpsilon (cutoffWhite (n / 2)
          (phaseWhiteAtInt n ξ)) (L - q - P) (j + q + P)
          (l + v.total)) := by
    refine Summable.of_nonneg_of_le (fun v =>
      mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
        (ENNReal.toReal_nonneg))
        (integerPairPotential_nonneg localEpsilon_guard
          (cutoffWhite (n / 2) (phaseWhiteAtInt n ξ)) _ _ _)) ?_ hsum
    intro v
    have hprod : (whiteWindowProduct (cutoffWhite (n / 2)
        (phaseWhiteAtInt n ξ)) (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))
        P (j + q) l v).toReal ≤ 1 :=
      by
        have hh := whiteWindowProduct_le_one (cutoffWhite (n / 2)
          (phaseWhiteAtInt n ξ))
          (z := ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))
          (ENNReal.ofReal_le_one.mpr (by nlinarith [sq_nonneg localEpsilon]))
          P (j + q) l v
        have hh' := ENNReal.toReal_mono (by simp) hh
        simpa using hh'
    have hu := integerPairPotential_le_one localEpsilon_guard
      (cutoffWhite (n / 2) (phaseWhiteAtInt n ξ))
      (L - q - P) (j + q + P) (l + v.total)
    have hp0 : 0 ≤ (Reference.wordPMF (2 * P) v).toReal := ENNReal.toReal_nonneg
    have hprod0 : 0 ≤ (whiteWindowProduct (cutoffWhite (n / 2)
        (phaseWhiteAtInt n ξ)) (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))
        P (j + q) l v).toReal := ENNReal.toReal_nonneg
    have hu0 := integerPairPotential_nonneg localEpsilon_guard
      (cutoffWhite (n / 2) (phaseWhiteAtInt n ξ))
      (L - q - P) (j + q + P) (l + v.total)
    calc
      _ ≤ (Reference.wordPMF (2 * P) v).toReal *
          ((whiteWindowProduct (cutoffWhite (n / 2) (phaseWhiteAtInt n ξ))
            (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) P (j + q) l v).toReal * 1) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hu hprod0) hp0
      _ ≤ (Reference.wordPMF (2 * P) v).toReal * 1 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod hp0
      _ = _ := by ring
  have hright : Summable (fun v : ValuationWord =>
      (D * (10 : ℝ) ^ B / layerWeight B m) *
        ((Reference.wordPMF (2 * P) v).toReal *
          (whiteWindowProduct (extendedPhaseWhite n ξ)
            (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) P (j + q) l v).toReal)) := by
    have hcoef : 0 ≤ D * (10 : ℝ) ^ B / layerWeight B m := by positivity
    refine Summable.of_nonneg_of_le (fun v =>
      mul_nonneg hcoef (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)) ?_
      (hsum.mul_left (D * (10 : ℝ) ^ B / layerWeight B m))
    intro v
    have hprod : (whiteWindowProduct (extendedPhaseWhite n ξ)
        (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) P (j + q) l v).toReal ≤ 1 :=
      by
        have hh := whiteWindowProduct_le_one (extendedPhaseWhite n ξ)
          (z := ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))
          (ENNReal.ofReal_le_one.mpr (by nlinarith [sq_nonneg localEpsilon]))
          P (j + q) l v
        have hh' := ENNReal.toReal_mono (by simp) hh
        simpa using hh'
    have hp := mul_le_mul_of_nonneg_left hprod
      (by positivity : 0 ≤ (Reference.wordPMF (2 * P) v).toReal)
    calc
      _ ≤ (D * (10 : ℝ) ^ B / layerWeight B m) *
          ((Reference.wordPMF (2 * P) v).toReal * 1) :=
        mul_le_mul_of_nonneg_left hp hcoef
      _ = _ := by ring
  have hmoment_toReal :
      (∑' v : ValuationWord, Reference.wordPMF (2 * P) v *
        whiteWindowProduct (extendedPhaseWhite n ξ)
          (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) P (j + q) l v).toReal =
      ∑' v : ValuationWord, (Reference.wordPMF (2 * P) v).toReal *
        (whiteWindowProduct (extendedPhaseWhite n ξ)
          (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) P (j + q) l v).toReal := by
    rw [ENNReal.tsum_toReal_eq (fun v => ENNReal.mul_ne_top
      (PMF.apply_ne_top _ _) (by
        have hh := whiteWindowProduct_le_one (extendedPhaseWhite n ξ)
          (z := ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))
          (ENNReal.ofReal_le_one.mpr (by nlinarith [sq_nonneg localEpsilon]))
          P (j + q) l v
        exact ne_top_of_le_ne_top ENNReal.one_ne_top hh))]
    simp_rw [ENNReal.toReal_mul]
  rw [hmoment_toReal, ← tsum_mul_left]
  change (∑' v : ValuationWord, _ ) ≤
    ∑' v : ValuationWord,
      (D * (10 : ℝ) ^ B / layerWeight B m) *
        ((Reference.wordPMF (2 * P) v).toReal *
          (whiteWindowProduct (extendedPhaseWhite n ξ)
            (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) P (j + q) l v).toReal)
  apply hleft.tsum_le_tsum
  · intro v
    have hcut :
        whiteWindowProduct (cutoffWhite (n / 2) (phaseWhiteAtInt n ξ))
          (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) P (j + q) l v =
        whiteWindowProduct (extendedPhaseWhite n ξ)
          (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) P (j + q) l v := by
      apply whiteWindowProduct_congr_columns
      intro t ht b
      have hbefore : j + q + t < n / 2 := by omega
      simp [cutoffWhite, hbefore, phaseWhiteAtInt, extendedPhaseWhite]
    rw [hcut]
    have hnonneg := (integerPairPotential_nonneg localEpsilon_guard
      (cutoffWhite (n / 2) (phaseWhiteAtInt n ξ))
      (L - q - P) (j + q + P) (l + v.total))
    have hbound := hUbound v
    have hprod0 : 0 ≤ (whiteWindowProduct (extendedPhaseWhite n ξ)
        (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) P (j + q) l v).toReal :=
      ENNReal.toReal_nonneg
    have hp0 : 0 ≤ (Reference.wordPMF (2 * P) v).toReal := ENNReal.toReal_nonneg
    calc
      _ = ((Reference.wordPMF (2 * P) v).toReal *
          (whiteWindowProduct (extendedPhaseWhite n ξ)
            (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) P (j + q) l v).toReal) *
          integerPairPotential localEpsilon (cutoffWhite (n / 2)
            (phaseWhiteAtInt n ξ)) (L - q - P) (j + q + P) (l + v.total) := by ring
      _ ≤ ((Reference.wordPMF (2 * P) v).toReal *
          (whiteWindowProduct (extendedPhaseWhite n ξ)
            (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) P (j + q) l v).toReal) *
          (D * (10 : ℝ) ^ B / layerWeight B m) :=
        mul_le_mul_of_nonneg_left hbound (mul_nonneg hp0 hprod0)
      _ = _ := by ring
  · exact hright

/- The passage-prefix predicate for which the first crossing leaves too little
   room for the fixed P-window. -/
/-- A first-passage prefix is late when its crossing plus the fixed window
    occupies more than nine tenths of the current layer. -/
def latePassageWord (m P : ℕ) (u : ValuationWord) : Prop :=
  9 * m < 10 * (u.length / 2 + P)

/-- The late-prefix predicate on the typed first-passage family. -/
def latePassagePrefix (s m P : ℕ) (u : passagePrefixFamily s) : Prop :=
  latePassageWord m P (u : ValuationWord)

theorem latePassagePrefix_probability_eq_terminal {s m P L : ℕ}
    (hL : s / 2 + 1 ≤ L) :
    Gated.probability (passagePMF s) (latePassagePrefix s m P) =
      Gated.probability (Reference.wordPMF (2 * L))
        (terminalPassageEvent s m P) := by
  change Gated.probability (passagePMF s)
      (fun u => latePassageWord m P (u : ValuationWord)) = _
  rw [passagePMF_probability s L hL]
  apply Gated.probability_congr_on_support
  intro w hw
  have hlen : w.length = 2 * L := by
    by_contra hne
    exact hw (Reference.wordPMF_eq_zero_of_length_ne _ _ hne)
  constructor
  · rintro ⟨u, hup, hu⟩
    obtain ⟨i, hi, hcross⟩ := u.property
    have hidx := i.isLt
    have huf : (u : ValuationWord) = w.take (2 * ((i : ℕ) + 1)) := by
      simpa only [hi] using List.prefix_iff_eq_take.mp hup
    have hip := (horizonTailEvent_prefix_iff hup (by omega)).mp hcross
    refine ⟨i, hip, ?_⟩
    change 9 * m < 10 * ((u : ValuationWord).length / 2 + P) at hu
    rw [hi] at hu
    omega
  · rintro ⟨i, hi, hu⟩
    have hidx := i.isLt
    have hp := passagePrefixFamily_take s w i hi (by omega)
    have huf : (w.take (2 * ((i : ℕ) + 1))).length = 2 * ((i : ℕ) + 1) :=
      List.length_take_of_le (by omega)
    refine ⟨⟨_, hp⟩, List.take_prefix _ _, ?_⟩
    change 9 * m < 10 * ((w.take (2 * ((i : ℕ) + 1))).length / 2 + P)
    rw [huf]
    omega

theorem postPassageProductMoment_toReal_prefix_sum
    (n : ℕ) (ξ : ZMod (3 ^ n)) (s j : ℕ) (l : ℤ) (B L : ℕ)
    (hL : s / 2 + 1 + localPrimitiveP B ≤ L) :
    (postPassageProductMoment n ξ s j l B L
      (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))).toReal =
      ∑' u : passagePrefixFamily s,
        (passagePMF s u).toReal *
          (∑' v : ValuationWord,
            Reference.wordPMF (2 * localPrimitiveP B) v *
              whiteWindowProduct (extendedPhaseWhite n ξ)
                (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))
                (localPrimitiveP B)
                (j + (u : ValuationWord).length / 2)
                (l + (u : ValuationWord).total) v).toReal := by
  rw [postPassageProductMoment_prefix_factor n ξ s j l B L hL]
  have hP (u : passagePrefixFamily s) :
      localPrimitiveP B ≤ L - (u : ValuationWord).length / 2 := by
    have hu := passagePrefixFamily_length s (u : ValuationWord) u.property
    omega
  have hinner (u : passagePrefixFamily s) :
      (∑' v : ValuationWord,
        Reference.wordPMF (2 * (L - (u : ValuationWord).length / 2)) v *
          whiteWindowProduct (extendedPhaseWhite n ξ)
            (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))
            (localPrimitiveP B)
            (j + (u : ValuationWord).length / 2)
            (l + (u : ValuationWord).total) v) =
      ∑' v : ValuationWord,
        Reference.wordPMF (2 * localPrimitiveP B) v *
          whiteWindowProduct (extendedPhaseWhite n ξ)
            (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))
            (localPrimitiveP B)
            (j + (u : ValuationWord).length / 2)
            (l + (u : ValuationWord).total) v := by
    symm
    exact whiteWindowProduct_moment_horizon (extendedPhaseWhite n ξ)
      (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))
      (localPrimitiveP B) (L - (u : ValuationWord).length / 2)
      (j + (u : ValuationWord).length / 2)
      (l + (u : ValuationWord).total) (hP u)
  simp_rw [hinner]
  have hterm (u : passagePrefixFamily s) :
      Reference.wordPMF (u : ValuationWord).length u *
        (∑' v : ValuationWord,
          Reference.wordPMF (2 * localPrimitiveP B) v *
            whiteWindowProduct (extendedPhaseWhite n ξ)
              (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))
              (localPrimitiveP B)
              (j + (u : ValuationWord).length / 2)
              (l + (u : ValuationWord).total) v) ≠ ⊤ := by
    apply ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact whiteWindowProduct_mass_le_one _ (by
      exact ENNReal.ofReal_le_one.mpr (by nlinarith [sq_nonneg localEpsilon])) _ _ _
  rw [ENNReal.tsum_toReal_eq hterm]
  simp_rw [ENNReal.toReal_mul, ← passagePMF_apply]

theorem phaseRemainingPotential_passage_long_le
    {n m s j L B : ℕ} (ξ : ZMod (3 ^ n)) (l : ℤ)
    (D : ℝ) (hjm : j + m = n / 2) (hm : 0 < m)
    (hmL : m ≤ L)
    (hL : s / 2 + 1 + localPrimitiveP B ≤ L)
    (hfuture : ∀ r, r < m → ∀ l',
      layerWeight B r * phaseRemainingPotential n ξ (n / 2) r l' ≤ D) :
    phaseRemainingPotential n ξ (n / 2) m l ≤
      (D * (10 : ℝ) ^ B / layerWeight B m) *
          (postPassageProductMoment n ξ s j l B L
            (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))).toReal +
    Gated.probability (Reference.wordPMF (2 * L))
          (terminalPassageEvent s m (localPrimitiveP B)) := by
  classical
  let U : passagePrefixFamily s → ℝ := fun u =>
    integerPairPotential localEpsilon
      (cutoffWhite (n / 2) (phaseWhiteAtInt n ξ))
      (L - (u : ValuationWord).length / 2)
      (j + (u : ValuationWord).length / 2)
      (l + (u : ValuationWord).total)
  let M : passagePrefixFamily s → ℝ := fun u =>
    (∑' v : ValuationWord,
      Reference.wordPMF (2 * localPrimitiveP B) v *
        whiteWindowProduct (extendedPhaseWhite n ξ)
          (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))
          (localPrimitiveP B)
          (j + (u : ValuationWord).length / 2)
          (l + (u : ValuationWord).total) v).toReal
  let p : passagePrefixFamily s → ℝ := fun u => (passagePMF s u).toReal
  let late : passagePrefixFamily s → Prop := latePassagePrefix s m (localPrimitiveP B)
  let C : ℝ := D * (10 : ℝ) ^ B / layerWeight B m
  have hL' : s / 2 + 1 ≤ L := by omega
  have hpass := integerPairPotential_passage_expectation_le localEpsilon_guard
    (cutoffWhite (n / 2) (phaseWhiteAtInt n ξ)) s L j l hL'
  have hphase := cutoffPotential_eq_phase (n := n) (m := m) (L := L)
    (j := j) ξ l hjm hmL
  have hp0 (u : passagePrefixFamily s) : 0 ≤ p u := ENNReal.toReal_nonneg
  have hU0 (u : passagePrefixFamily s) : 0 ≤ U u := by
    exact integerPairPotential_nonneg localEpsilon_guard _ _ _ _
  have hU1 (u : passagePrefixFamily s) : U u ≤ 1 := by
    exact integerPairPotential_le_one localEpsilon_guard _ _ _ _
  have hM0 (u : passagePrefixFamily s) : 0 ≤ M u := ENNReal.toReal_nonneg
  have hM1 (u : passagePrefixFamily s) : M u ≤ 1 := by
    have hmass := whiteWindowProduct_mass_le_one (extendedPhaseWhite n ξ)
      (ENNReal.ofReal_le_one (r := 1 - 2 * localEpsilon ^ 2) |>.mpr
        (by nlinarith [sq_nonneg localEpsilon]))
      (localPrimitiveP B) (j + (u : ValuationWord).length / 2)
      (l + (u : ValuationWord).total)
    have htop : (∑' v : ValuationWord,
        Reference.wordPMF (2 * localPrimitiveP B) v *
          whiteWindowProduct (extendedPhaseWhite n ξ)
            (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))
            (localPrimitiveP B)
            (j + (u : ValuationWord).length / 2)
            (l + (u : ValuationWord).total) v) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hmass
    have hreal := ENNReal.toReal_mono ENNReal.one_ne_top hmass
    simpa [M] using hreal
  have hsumP : Summable p := by
    exact ENNReal.summable_toReal (by
      rw [PMF.tsum_coe]
      exact ENNReal.one_ne_top)
  have hsumU : Summable (fun u => p u * U u) := by
    refine Summable.of_nonneg_of_le (fun u => mul_nonneg (hp0 u) (hU0 u)) ?_ hsumP
    intro u
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hU1 u) (hp0 u)
  have hsumM : Summable (fun u => p u * M u) := by
    refine Summable.of_nonneg_of_le (fun u => mul_nonneg (hp0 u) (hM0 u)) ?_ hsumP
    intro u
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hM1 u) (hp0 u)
  have hD : 0 ≤ D := by
    have hf := hfuture 0 hm 0
    rw [phaseRemainingPotential_zero] at hf
    have hw := layerWeight_pos B 0
    nlinarith
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg hD (by positivity)) (layerWeight_pos B m).le
  have hlateU (u : passagePrefixFamily s) (hu : late u) : U u ≤ 1 := hU1 u
  have hnotlateU (u : passagePrefixFamily s) (hu : ¬ late u) : U u ≤ C * M u := by
    have hcut := cutoffPotential_nonterminal_le (n := n) (m := m) (L := L)
      (j := j) (q := (u : ValuationWord).length / 2)
      (P := localPrimitiveP B) ξ (l + (u : ValuationWord).total) B D
      hjm hm (localPrimitiveP_pos B) hmL
      (by
        change ¬ 9 * m < 10 *
          ((u : ValuationWord).length / 2 + localPrimitiveP B) at hu
        omega)
      hfuture
    simpa [U, M, C] using hcut
  have hpassU : integerPairPotential localEpsilon
      (cutoffWhite (n / 2) (phaseWhiteAtInt n ξ)) L j l ≤
      ∑' u, p u * U u := by
    apply hpass
  have hsumLate : Summable (fun u => if late u then p u * U u else 0) := by
    refine Summable.of_nonneg_of_le (fun u => by
      by_cases hu : late u
      · rw [if_pos hu]
        exact mul_nonneg (hp0 u) (hU0 u)
      · simp [hu]) ?_ hsumP
    intro u
    by_cases hu : late u
    · rw [if_pos hu]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hU1 u) (hp0 u)
    · rw [if_neg hu]
      exact hp0 u
  have hsumEarly : Summable (fun u => if late u then 0 else p u * U u) := by
    refine Summable.of_nonneg_of_le (fun u => by
      by_cases hu : late u
      · simp [hu]
      · rw [if_neg hu]
        exact mul_nonneg (hp0 u) (hU0 u)) ?_ hsumP
    intro u
    by_cases hu : late u
    · rw [if_pos hu]
      exact hp0 u
    · rw [if_neg hu]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hU1 u) (hp0 u)
  have hdecomp : (∑' u, p u * U u) =
      (∑' u, if late u then p u * U u else 0) +
        (∑' u, if late u then 0 else p u * U u) := by
    rw [← hsumLate.tsum_add hsumEarly]
    apply tsum_congr
    intro u
    by_cases hu : late u <;> simp [hu]
  have hlateBound :
      (∑' u, if late u then p u * U u else 0) ≤
        ∑' u, if late u then p u else 0 := by
    apply hsumLate.tsum_le_tsum
    · intro u
      by_cases hu : late u
      · rw [if_pos hu, if_pos hu]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (hU1 u) (hp0 u)
      · rw [if_neg hu, if_neg hu]
    · exact Summable.of_nonneg_of_le (fun u => by split_ifs <;> positivity) (by
        intro u
        split_ifs <;> simp [hp0 u]) hsumP
  have hEarlyBound :
      (∑' u, if late u then 0 else p u * U u) ≤
        C * (∑' u, p u * M u) := by
    rw [← tsum_mul_left]
    apply hsumEarly.tsum_le_tsum
    · intro u
      by_cases hu : late u
      · rw [if_pos hu]
        exact mul_nonneg hC (mul_nonneg (hp0 u) (hM0 u))
      · rw [show C * (p u * M u) = p u * (C * M u) by ring]
        rw [if_neg hu]
        exact mul_le_mul_of_nonneg_left (hnotlateU u hu) (hp0 u)
    · exact hsumM.mul_left C
  have hlateProb :
      (∑' u, if late u then p u else 0) =
        Gated.probability (Reference.wordPMF (2 * L))
          (terminalPassageEvent s m (localPrimitiveP B)) := by
    have hprob := latePassagePrefix_probability_eq_terminal
      (s := s) (m := m) (P := localPrimitiveP B) (L := L) hL'
    unfold Gated.probability at hprob
    rw [ENNReal.tsum_toReal_eq (fun u => by
      by_cases hu : latePassagePrefix s m (localPrimitiveP B) u
      · simpa [hu] using PMF.apply_ne_top (passagePMF s) u
      · simp [hu])] at hprob
    have hleft :
        (∑' u : passagePrefixFamily s,
          (if latePassagePrefix s m (localPrimitiveP B) u then
            passagePMF s u else 0).toReal) =
          ∑' u : passagePrefixFamily s,
            if latePassagePrefix s m (localPrimitiveP B) u then
              (passagePMF s u).toReal else 0 := by
      apply tsum_congr
      intro u
      by_cases hu : latePassagePrefix s m (localPrimitiveP B) u <;> simp [hu]
    rw [hleft] at hprob
    change (∑' u : passagePrefixFamily s,
      if latePassagePrefix s m (localPrimitiveP B) u then
        (passagePMF s u).toReal else 0) =
      (∑' w : ValuationWord,
        if terminalPassageEvent s m (localPrimitiveP B) w then
          Reference.wordPMF (2 * L) w else 0).toReal
    exact hprob
  calc
    phaseRemainingPotential n ξ (n / 2) m l =
        integerPairPotential localEpsilon
          (cutoffWhite (n / 2) (phaseWhiteAtInt n ξ)) L j l := hphase.symm
    _ ≤ ∑' u, p u * U u := hpassU
    _ = (∑' u, if late u then p u * U u else 0) +
          (∑' u, if late u then 0 else p u * U u) := hdecomp
    _ ≤ (∑' u, if late u then p u else 0) + C * (∑' u, p u * M u) :=
      add_le_add hlateBound hEarlyBound
    _ = C * (postPassageProductMoment n ξ s j l B L
          (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))).toReal +
        Gated.probability (Reference.wordPMF (2 * L))
          (terminalPassageEvent s m (localPrimitiveP B)) := by
      rw [hlateProb, ← postPassageProductMoment_toReal_prefix_sum n ξ s j l B L hL]
      ring

end WordCertDensity.LocalPrimitive
