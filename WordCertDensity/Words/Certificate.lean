/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Words.Forward
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact forward word cylinders

The finite certificate stores only the actual valuation checks and the input
precision. A single affine congruence characterizes those checks; invariance
and the unique source cylinder are consequences, not certificate assumptions.
-/

@[expose] public section

namespace WordCertDensity

/-- A congruence at one additional bit is equivalent to having an odd quotient. -/
theorem odd_quotient_iff_modEq (S n : ℕ) :
    (∃ q : ℕ, Odd q ∧ 2 ^ S * q = n) ↔ n ≡ 2 ^ S [MOD 2 ^ (S + 1)] := by
  constructor
  · rintro ⟨q, hodd, rfl⟩
    have hmod : q ≡ 1 [MOD 2] := by simpa [Nat.ModEq] using Nat.odd_iff.mp hodd
    simpa [pow_succ] using hmod.mul_left' (2 ^ S)
  · intro hmod
    have hdivpow : 2 ^ S ∣ 2 ^ (S + 1) := by
      rw [pow_succ]
      exact Nat.dvd_mul_right _ _
    have hsmall : n ≡ 0 [MOD 2 ^ S] := by
      simpa [Nat.ModEq] using hmod.of_dvd hdivpow
    have hdiv := Nat.modEq_zero_iff_dvd.mp hsmall
    let q := n / 2 ^ S
    have heq : 2 ^ S * q = n := Nat.mul_div_cancel' hdiv
    have hscaled : 2 ^ S * q ≡ 2 ^ S * 1 [MOD 2 ^ S * 2] := by
      simpa [pow_succ, heq] using hmod
    have hodd : Odd q := Nat.odd_iff.mpr (by
      simpa [Nat.ModEq] using
        Nat.ModEq.mul_left_cancel' (by positivity : 2 ^ S ≠ 0) hscaled)
    exact ⟨q, hodd, heq⟩

namespace ForwardRealizes

/-- The affine numerator congruence is equivalent to all actual valuation checks. -/
theorem iff_affine_modEq (w : ValuationWord) (x : ℕ) :
    ForwardRealizes w x ↔
      3 ^ w.length * x + w.forwardNumerator ≡ 2 ^ w.total [MOD 2 ^ (w.total + 1)] := by
  rw [← odd_quotient_iff_modEq]
  exact ⟨fun h => ⟨_, h.endpoint_odd, h.affine_eq⟩,
    fun ⟨_, hodd, heq⟩ => of_affine_eq hodd heq⟩

/-- Sources with the same word are congruent at the full input precision. -/
theorem modEq {w : ValuationWord} {x r : ℕ}
    (hx : ForwardRealizes w x) (hr : ForwardRealizes w r) :
    x ≡ r [MOD 2 ^ (w.total + 1)] := by
  have hnum := ((iff_affine_modEq w x).1 hx).trans ((iff_affine_modEq w r).1 hr).symm
  have hprod := Nat.ModEq.add_right_cancel' w.forwardNumerator hnum
  exact Nat.ModEq.cancel_left_of_coprime
    ((show Nat.Coprime 2 3 by decide).pow (w.total + 1) w.length) hprod

/-- The full input congruence preserves every actual valuation of a realized word. -/
theorem of_modEq {w : ValuationWord} {x r : ℕ}
    (hr : ForwardRealizes w r) (hmod : x ≡ r [MOD 2 ^ (w.total + 1)]) :
    ForwardRealizes w x := by
  apply (iff_affine_modEq w x).2
  exact ((hmod.mul_left (3 ^ w.length)).add_right w.forwardNumerator).trans
    ((iff_affine_modEq w r).1 hr)

/-- The exact realization set is a single odd cylinder once one source is known. -/
theorem iff_modEq {w : ValuationWord} {r : ℕ} (hr : ForwardRealizes w r) (x : ℕ) :
    ForwardRealizes w x ↔ x ≡ r [MOD 2 ^ (w.total + 1)] :=
  ⟨fun hx => hx.modEq hr, hr.of_modEq⟩

/-- Every positive valuation word has exactly one representative below its binary modulus. -/
theorem exists_unique_residue (w : ValuationWord) :
    ∃! r : ℕ, r < 2 ^ (w.total + 1) ∧ ForwardRealizes w r := by
  let M := 2 ^ (w.total + 1)
  let : NeZero M := ⟨by dsimp [M]; positivity⟩
  have hcop : Nat.Coprime (3 ^ w.length) M :=
    (show Nat.Coprime 3 2 by decide).pow w.length (w.total + 1)
  let z : ZMod M := (3 ^ w.length : ZMod M)⁻¹ *
    ((2 ^ w.total : ZMod M) - (w.forwardNumerator : ZMod M))
  have hcong : 3 ^ w.length * z.val + w.forwardNumerator ≡ 2 ^ w.total [MOD M] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).1
    push_cast
    rw [ZMod.natCast_zmod_val]
    change (3 ^ w.length : ZMod M) *
      ((3 ^ w.length : ZMod M)⁻¹ * (2 ^ w.total - w.forwardNumerator)) +
        w.forwardNumerator = 2 ^ w.total
    have hinv := ZMod.coe_mul_inv_eq_one (3 ^ w.length) hcop
    push_cast at hinv
    rw [← mul_assoc, hinv, one_mul, sub_add_cancel]
  have hz : ForwardRealizes w z.val := (iff_affine_modEq w z.val).2 hcong
  refine ⟨z.val, ⟨z.val_lt, hz⟩, ?_⟩
  intro r hr
  have hmod := hr.2.modEq hz
  change r % M = z.val % M at hmod
  rwa [Nat.mod_eq_of_lt hr.1, Nat.mod_eq_of_lt z.val_lt] at hmod

/-- Exactly one residue below the binary modulus realizes a given positive word. -/
theorem card_residues (w : ValuationWord) :
    ((Finset.range (2 ^ (w.total + 1))).filter (ForwardRealizes w)).card = 1 := by
  obtain ⟨r, hr, hunique⟩ := exists_unique_residue w
  have hset : (Finset.range (2 ^ (w.total + 1))).filter (ForwardRealizes w) = {r} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    exact ⟨fun hx => hunique x hx, fun hx => hx ▸ hr⟩
  rw [hset, Finset.card_singleton]

end ForwardRealizes

/-- Half of the residues modulo `2^(S+1)` are odd, with an explicit index map. -/
theorem card_odd_residues (S : ℕ) :
    ((Finset.range (2 ^ (S + 1))).filter Odd).card = 2 ^ S := by
  have hset : (Finset.range (2 ^ (S + 1))).filter Odd =
      (Finset.range (2 ^ S)).image (fun j => 2 * j + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hlt, j, hj⟩
      refine ⟨j, ?_, by omega⟩
      rw [pow_succ] at hlt
      omega
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, ⟨j, by omega⟩⟩
      rw [pow_succ]
      omega
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro a b hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega
  rw [hset, Finset.card_image_of_injective _ hinj]
  exact Finset.card_range _

/-- Equal weighting of odd residues gives precisely the finite word probability `2^(-S)`. -/
theorem forwardWord_odd_probability (w : ValuationWord) :
    (((Finset.range (2 ^ (w.total + 1))).filter (ForwardRealizes w)).card : ℚ) /
      ((Finset.range (2 ^ (w.total + 1))).filter Odd).card = 1 / (2 : ℚ) ^ w.total := by
  simp [ForwardRealizes.card_residues, card_odd_residues]

/-- Finite chronological checks with enough binary precision, as in (W.data). -/
def WordCert (r E : ℕ) (w : ValuationWord) : Prop :=
  w.total + 1 ≤ E ∧ ForwardRealizes w r

/-- Certificate precision and actual finite valuation checks are decidable. -/
instance (r E : ℕ) (w : ValuationWord) : Decidable (WordCert r E w) :=
  inferInstanceAs (Decidable (w.total + 1 ≤ E ∧ ForwardRealizes w r))

namespace WordCert

/-- A certificate's representative lies in the physical source domain. -/
theorem realizes {r E : ℕ} {w : ValuationWord} (h : WordCert r E w) :
    ForwardRealizes w r := h.2

/-- Every integer in a certified cylinder realizes the same chronological word. -/
theorem invariant {r E x : ℕ} {w : ValuationWord} (h : WordCert r E w)
    (hx : x ≡ r [MOD 2 ^ E]) : ForwardRealizes w x := by
  apply h.realizes.of_modEq
  exact hx.of_dvd (pow_dvd_pow 2 h.1)

/-- The affine endpoint identity holds at every prefix of every certified source. -/
theorem affine_prefix {r E x j : ℕ} {w : ValuationWord} (h : WordCert r E w)
    (hx : x ≡ r [MOD 2 ^ E]) (hj : j ≤ w.length) :
    2 ^ ValuationWord.total (w.take j) * (acceleratedStep^[j]) x =
      3 ^ j * x + ValuationWord.forwardNumerator (w.take j) := by
  simpa [List.length_take, Nat.min_eq_left hj] using ((h.invariant hx).take j).affine_eq

/-- Dividing the exact prefix identity gives the displayed affine quotient (W.affine). -/
theorem affine_prefix_div {r E x j : ℕ} {w : ValuationWord} (h : WordCert r E w)
    (hx : x ≡ r [MOD 2 ^ E]) (hj : j ≤ w.length) :
    (acceleratedStep^[j]) x =
      (3 ^ j * x + ValuationWord.forwardNumerator (w.take j)) /
        2 ^ ValuationWord.total (w.take j) := by
  rw [← h.affine_prefix hx hj]
  exact (Nat.mul_div_right _ (by positivity)).symm

/-- A certified cylinder pays the ordinary cost of its actual chronological word. -/
theorem reachesIn {r E x : ℕ} {w : ValuationWord} (h : WordCert r E w)
    (hx : x ≡ r [MOD 2 ^ E]) :
    ReachesIn x ((acceleratedStep^[w.length]) x) w.ordinaryCost :=
  (h.invariant hx).reachesIn

end WordCert

end WordCertDensity
