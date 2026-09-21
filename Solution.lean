/-
Copyright (c) 2026 Idris Ali Shaik.
SPDX-License-Identifier: Apache-2.0
Authors: Idris Ali Shaik
-/
import WordCertDensity.Release.PhaseOne
import WordCertDensity.Density.Qualitative
import WordCertDensity.Construction.SeedScoreDomain
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.LiminfLimsup
import WordCertDensity.Release.AnalyticExtensions

/-! Proved wrappers for the Phase 1 Palomar statement surface. -/

namespace CollatzWordCert

open WordCertDensity
open Filter Construction
open scoped Topology Finset

/-- Ordinary Collatz map on naturals (zero is totalized and excluded from good sets). -/
def ordinaryStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/-- Reaching a target in exactly the specified number of ordinary steps. -/
def ReachesIn (x target steps : ℕ) : Prop :=
  (ordinaryStep^[steps]) x = target

/-- Existence of a finite ordinary hitting time within a real budget. -/
def ReachesWithin (x target : ℕ) (budget : ℝ) : Prop :=
  ∃ steps : ℕ, ReachesIn x target steps ∧ (steps : ℝ) ≤ budget

/-- Positive sources reaching a target within the specified logarithmic clock. -/
def goodTarget (target : ℕ) (c : ℝ) : Set ℕ :=
  {x | 0 < x ∧ ReachesWithin x target (c * Real.log x)}

/-- Positive integers reaching one within a fixed clock. -/
def good (c : ℝ) : Set ℕ := goodTarget 1 c

/-- Count members of a set in the positive prefix `[1,N]`. -/
noncomputable def prefixCount (S : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact #{x ∈ Finset.Icc 1 N | x ∈ S}

/-- Finite natural-density profile. -/
noncomputable def partialDensity (S : Set ℕ) (N : ℕ) : ℝ :=
  (prefixCount S N : ℝ) / N

/-- Lower natural density along positive integer cutoffs. -/
noncomputable def lowerNaturalDensity (S : Set ℕ) : ℝ :=
  liminf (partialDensity S) atTop

/-- Reference-model threshold in the ordinary-step convention. -/
noncomputable def criticalClock : ℝ := 3 / Real.log (4 / 3)

/-- One lower-density constant chosen before every strictly larger clock. -/
def CommonClockDensity : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ c : ℝ, criticalClock < c → d ≤ lowerNaturalDensity (good c)

/-- Universal clock statement for a specified density constant. -/
def EveryClockDensityBound (d : ℝ) : Prop :=
  0 < d ∧ ∀ c : ℝ, criticalClock < c → d ≤ lowerNaturalDensity (good c)

/-- Small-score domain of the counting conversion. -/
def SmallScore (W : ℝ) : Prop := 0 < W ∧ W ≤ 27 / (2 : ℝ) ^ 27

/-- Positive bound fixed before every permitted clock for a specified target. -/
def TargetBound (target : ℕ) (d : ℝ) : Prop :=
  0 < d ∧ ∀ c : ℝ, criticalClock < c → d ≤ lowerNaturalDensity (goodTarget target c)

/-- Harmonic capacity times the fan mean. -/
noncomputable def kappa : ℝ := (8 / 9) * (2 * Real.log 2)

/-- Radial conversion of a harmonic mass into a density constant. -/
noncomputable def radial (u : ℝ) : ℝ := (32 / 225) * (Real.exp (2 * u) - 1)

/-- Fully numerical depth-eleven second-moment ceiling. -/
noncomputable def energyElevenCeiling (n : ℕ) : ℝ :=
  (3167 / 500) ^ (n / 11) * (5 / 3) ^ (n % 11)

/-- Fan energy denominator used by the depth-eleven formula. -/
noncomputable def fanEnergyElevenCeiling (m : ℕ) : ℝ :=
  (64 / 135) * energyElevenCeiling (m + 1)

/-- Fixed-score second-moment mass ceiling (not an optimizer recipe). -/
noncomputable def secondElevenMass (W : ℝ) (m : ℕ) : ℝ :=
  (W / 2) ^ 2 / ((2 * Real.log 2) * fanEnergyElevenCeiling m)

/-- Strict sub-bound clipped to the radial conversion domain. -/
noncomputable def secondElevenRadialMass (W : ℝ) (m : ℕ) : ℝ :=
  min (secondElevenMass W m / 2) (Real.log (3 / 2) / 2)

/-- Named depth-eleven density formula at one paid coarse level. -/
noncomputable def secondElevenDensity (W : ℝ) (m : ℕ) : ℝ :=
  radial (secondElevenRadialMass W m)

/-- Fully numerical fractional ceiling. -/
noncomputable def fractionalElevenCeiling (n : ℕ) : ℝ :=
  (259093 / 125000) ^ (n / 11) * (1276143 / 1000000) ^ (n % 11)

/-- Fan fractional ceiling used by the order-three-halves formula. -/
noncomputable def fanFractionalElevenCeiling (m : ℕ) : ℝ :=
  (3 * (8 / 9 : ℝ) ^ (3 / 2 : ℝ) / (1 + (2 : ℝ) ^ (3 / 2 : ℝ))) *
    fractionalElevenCeiling (m + 1)

/-- Order-three-halves mass at an explicit paid residual score `p`.

`p` is witnessed in Solution by the score surviving the coarse-level mixing
charge. The public inequalities `W/2 < p` and `p ≤ W` do not uniquely
characterize that score. -/
noncomputable def fractionalMassAt (p : ℝ) (m : ℕ) : ℝ :=
  p ^ 3 / ((2 * Real.log 2) ^ 2 * fanFractionalElevenCeiling m ^ 2)

/-- Fractional radial mass at paid residual `p`, clipped to the conversion domain. -/
noncomputable def fractionalRadialMassAt (p : ℝ) (m : ℕ) : ℝ :=
  min (fractionalMassAt p m / 2) (Real.log (3 / 2) / 2)

/-- Named depth-eleven fractional density formula at paid residual `p`. -/
noncomputable def fractionalDensityAt (p : ℝ) (m : ℕ) : ℝ :=
  radial (fractionalRadialMassAt p m)

private theorem lowerNaturalDensity_eq :
    lowerNaturalDensity = WordCertDensity.lowerNaturalDensity := by
  funext S
  rfl

private theorem goodTarget_eq : goodTarget = WordCertDensity.goodTarget := by
  funext target c; rfl

private theorem good_eq : good = WordCertDensity.good := by
  funext c; rfl

private theorem criticalClock_eq : criticalClock = WordCertDensity.criticalClock := rfl

private theorem EveryClockDensityBound_mono {d d' : ℝ}
    (hle : d ≤ d') (hd : 0 < d) (h : WordCertDensity.EveryClockDensityBound d') :
    EveryClockDensityBound d := by
  refine ⟨hd, ?_⟩
  intro c hc
  have := h.2 c (by simpa [criticalClock_eq] using hc)
  simp only [lowerNaturalDensity_eq, good_eq] at this ⊢
  exact hle.trans this

private theorem TargetBound_mono {target : ℕ} {d d' : ℝ}
    (hle : d ≤ d') (hd : 0 < d) (h : Density.TargetBound target d') :
    TargetBound target d := by
  refine ⟨hd, ?_⟩
  intro c hc
  have := h.2 c (by simpa [criticalClock_eq] using hc)
  simp only [lowerNaturalDensity_eq, goodTarget_eq] at this ⊢
  exact hle.trans this

private theorem secondElevenDensity_eq (W : ℝ) (m : ℕ) :
    secondElevenDensity W m = Density.secondElevenDensity W m := by
  rfl

/-- The advertised fractional density at the paid residual IS the production
constant; no weakening bridge is used. -/
private theorem fractionalDensityAt_eq (W : ℝ) (m : ℕ) :
    fractionalDensityAt (Density.residual W m) m =
      Density.fractionalElevenDensity W m := rfl

private theorem ReachesIn_eq : ReachesIn = WordCertDensity.ReachesIn := by
  funext x target steps; rfl

private theorem residual_gt_half {W : ℝ} {m : ℕ}
    (hpaid : Density.kappa * Analytic.mixingError m < W / 2) :
    W / 2 < Density.residual W m := by
  unfold Density.residual
  exact lt_of_lt_of_le (by linarith) (le_max_left _ _)

private theorem residual_le {W : ℝ} {m : ℕ} (hW : 0 < W) (hm : 2 ≤ m) :
    Density.residual W m ≤ W := by
  have hk : 0 < Density.kappa := by
    unfold Density.kappa
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have he : 0 < Analytic.mixingError m := Analytic.mixingError_pos (by omega)
  unfold Density.residual
  exact max_le (by nlinarith) hW.le

theorem common_density : CommonClockDensity := by
  simpa [CommonClockDensity, WordCertDensity.CommonClockDensity, criticalClock_eq,
    lowerNaturalDensity_eq, good_eq] using Release.PhaseOne.common_density

theorem depthEleven_density :
    ∃ (W : ℝ) (m : ℕ), SmallScore W ∧ 2 ≤ m ∧
      EveryClockDensityBound (secondElevenDensity W m) := by
  obtain ⟨m, hm, _, h⟩ := Release.PhaseOne.depthEleven_density
  refine ⟨persistentRootScore, m, Density.canonicalSmallScore, hm, ?_⟩
  simpa [EveryClockDensityBound, WordCertDensity.EveryClockDensityBound,
    criticalClock_eq, lowerNaturalDensity_eq, good_eq, secondElevenDensity_eq] using h

theorem numerical_clock : criticalClock < 10431 / 1000 := by
  simpa [criticalClock_eq] using Release.PhaseOne.numerical_clock

theorem every_admissible_target {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ d : ℝ, 0 < d ∧ TargetBound n d := by
  obtain ⟨d, hd, h⟩ := Release.PhaseOne.every_admissible_target hn h3
  exact ⟨d, hd, by
    simpa [TargetBound, Density.TargetBound, criticalClock_eq, lowerNaturalDensity_eq,
      goodTarget_eq] using h⟩

theorem every_admissible_target_depthEleven {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ (W : ℝ) (m : ℕ), 0 < W ∧ 2 ≤ m ∧
      TargetBound n (secondElevenDensity W m) := by
  obtain ⟨W, m, hW, hm, h⟩ :=
    Release.PhaseOne.every_admissible_target_depthEleven hn h3
  refine ⟨W, m, hW, hm, ?_⟩
  simpa [TargetBound, Density.TargetBound, criticalClock_eq, lowerNaturalDensity_eq,
    goodTarget_eq, secondElevenDensity_eq] using h

theorem target_criterion (target : ℕ) (htarget : 0 < target) (c : ℝ)
    (hc : criticalClock < c) :
    0 < lowerNaturalDensity (goodTarget target c) ↔ ¬ 3 ∣ target := by
  simpa [lowerNaturalDensity_eq, goodTarget_eq, criticalClock_eq] using
    Release.PhaseOne.target_criterion target htarget c (by simpa [criticalClock_eq] using hc)

theorem individual_root :
    ∃ r s : ℕ, 2 ≤ s ∧ 3 * r + 1 = 4 ^ s ∧ ReachesIn r 1 (2 * s + 1) ∧
      ∃ d : ℝ, TargetBound r d := by
  obtain ⟨r, hr, _, _, _, d, hd⟩ := Release.PhaseOne.individual_root
  obtain ⟨_, i, hi⟩ := Construction.mem_seedRootPool.mp hr
  have hb : 1 ≤ survivalSeedSize := by norm_num [survivalSeedSize]
  refine ⟨r, 2 * survivalSeedSize + 1 + i.val, by omega, ?_, ?_, d, ?_⟩
  · rw [← hi]
    exact Roots.three_mul_value_add_one _
  · rw [← hi, ReachesIn_eq]
    exact Roots.reachesIn_one (by omega)
  · simpa [TargetBound, Density.TargetBound, criticalClock_eq, lowerNaturalDensity_eq,
      goodTarget_eq] using hd

theorem common_vanishing_clock :
    ∃ d : ℝ, 0 < d ∧ ∃ η : ℕ → ℝ,
      (∀ x, 0 < η x) ∧ Antitone η ∧ Tendsto η atTop (𝓝 0) ∧
      d ≤ lowerNaturalDensity {x : ℕ | 0 < x ∧
        ReachesWithin x 1 ((criticalClock + η x) * Real.log x)} := by
  obtain ⟨d, hd, η, hη, hanti, htend, hden⟩ := Release.PhaseOne.common_vanishing_clock
  refine ⟨d, hd, η, hη, hanti, htend, ?_⟩
  simpa [lowerNaturalDensity_eq, ReachesWithin, WordCertDensity.ReachesWithin,
    ReachesIn_eq, criticalClock_eq] using hden

theorem target_vanishing_clock {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ d : ℝ, 0 < d ∧ ∃ η : ℕ → ℝ,
      (∀ x, 0 < η x) ∧ Antitone η ∧ Tendsto η atTop (𝓝 0) ∧
      d ≤ lowerNaturalDensity {x : ℕ | 0 < x ∧
        ReachesWithin x n ((criticalClock + η x) * Real.log x)} := by
  obtain ⟨d, hd, η, hη, hanti, htend, hden⟩ :=
    Release.PhaseOne.target_vanishing_clock hn h3
  refine ⟨d, hd, η, hη, hanti, htend, ?_⟩
  simpa [lowerNaturalDensity_eq, ReachesWithin, WordCertDensity.ReachesWithin,
    ReachesIn_eq, criticalClock_eq] using hden

theorem fractional_density :
    ∃ (W p : ℝ) (m : ℕ), SmallScore W ∧ 2 ≤ m ∧ W / 2 < p ∧ p ≤ W ∧
      EveryClockDensityBound (fractionalDensityAt p m) := by
  obtain ⟨m, hm, hpaid⟩ := Density.exists_coarseLevel persistentRootScore_domain.1
  have hproj := Density.fractionalElevenDensity_target 1 persistentRootScore
    Density.canonicalSmallScore Sources.canonicalSources m hm hpaid
  exact ⟨persistentRootScore, Density.residual persistentRootScore m, m,
    Density.canonicalSmallScore, hm, residual_gt_half hpaid,
    residual_le persistentRootScore_domain.1 hm,
    EveryClockDensityBound_mono (le_of_eq (fractionalDensityAt_eq _ _)) hproj.1 hproj⟩

theorem every_admissible_target_fractional {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ (W p : ℝ) (m : ℕ), 0 < W ∧ 2 ≤ m ∧ W / 2 < p ∧ p ≤ W ∧
      TargetBound n (fractionalDensityAt p m) := by
  obtain ⟨W, hWpos, hWle, hsrc⟩ := Sources.admissibleTargetSources hn h3
  obtain ⟨m, hm, hpaid⟩ := Density.exists_coarseLevel hWpos
  have hproj := Density.fractionalElevenDensity_target n W ⟨hWpos, hWle⟩ hsrc m hm hpaid
  exact ⟨W, Density.residual W m, m, hWpos, hm, residual_gt_half hpaid,
    residual_le hWpos hm,
    TargetBound_mono (le_of_eq (fractionalDensityAt_eq _ _)) hproj.1 hproj⟩

end CollatzWordCert

namespace CollatzWordCert
open Filter
open scoped Topology BigOperators

/-- A finite word of positive geometric valuations. -/
abbrev ValuationWord := List ℕ+

namespace Reference
/-- The geometric distribution assigning mass 2^(-(n+1)) to each natural n. -/
noncomputable def geometricNat : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)), by
    have h : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) 1 := by
      simpa [pow_succ] using hasSum_geometric_two.mul_right (1 / 2 : ℝ)
    exact ENNReal.hasSum_coe.mpr (by
      simpa using h.toNNReal (fun n => by positivity))⟩

/-- The positive valuation obtained by shifting the geometric natural by one. -/
noncomputable def geometricLetter : PMF ℕ+ :=
  geometricNat.map Nat.succPNat

/-- The law of a word of independent positive geometric valuations of the given length. -/
noncomputable def wordPMF : ℕ → PMF ValuationWord
  | 0 => PMF.pure []
  | n + 1 => geometricLetter.bind (fun a => (wordPMF n).map (fun w => a :: w))

/-- The invertible residue of two modulo a power of three. -/
noncomputable def twoUnit (q : ℕ) : (ZMod (3 ^ q))ˣ :=
  ZMod.unitOfCoprime 2 ((show Nat.Coprime 2 3 by decide).pow_right q)

/-- The residue of the indicated inverse power of two modulo 3^q. -/
noncomputable def inverseTwoPow (q k : ℕ) : ZMod (3 ^ q) :=
  ↑((twoUnit q)⁻¹ ^ k)

/-- The recursively evaluated inverse affine offset of a valuation word. -/
noncomputable def residueOffset (q : ℕ) : ValuationWord → ZMod (3 ^ q)
  | [] => 0
  | k :: w => Reference.inverseTwoPow q k * (1 + 3 * residueOffset q w)

/-- The actual reference law: push forward geometric words by their residue offset. -/
noncomputable def law (n : ℕ) : PMF (ZMod (3 ^ n)) :=
  (wordPMF n).map (residueOffset n)

/-- Real probability mass of a residue under the actual reference law. -/
noncomputable def mass (n : ℕ) (x : ZMod (3 ^ n)) : ℝ := (law n x).toReal

/-- Density of the actual reference law relative to the uniform residue measure. -/
noncomputable def density (n : ℕ) (x : ZMod (3 ^ n)) : ℝ :=
  (3 : ℝ) ^ n * mass n x

/-- The normalized reference marker, equal to two thirds of the reference density. -/
noncomputable def marker (n : ℕ) (x : ZMod (3 ^ n)) : ℝ := (2 / 3 : ℝ) * density n x

/-- The normalized mean over every residue modulo 3^n. -/
noncomputable def mean (n : ℕ) (f : ZMod (3 ^ n) → ℝ) : ℝ :=
  (∑ x, f x) / (3 : ℝ) ^ n

/-- The affine residue map for the j-th fan branch. -/
def fanMap (m j : ℕ) (x : ZMod (3^m)) : ZMod (3^m) :=
  4^j*x+((4^j-1)/3 : ℕ)

/-- The full geometrically weighted fan of the actual reference marker. -/
noncomputable def fan (m : ℕ) (x : ZMod (3^m)) : ℝ :=
  ∑' j : ℕ, (4 : ℝ)^(-(j : ℤ))*marker m (fanMap m j x)

/-- Relative entropy of the actual reference law against uniform residue measure. -/
noncomputable def entropy (n : ℕ) : ℝ :=
  mean n (fun x => density n x * Real.log (density n x))

end Reference
namespace LocalPrimitive
/-- The explicit reciprocal collar parameter in the local primitive recipe. -/
def localPrimitiveDeltaDenom (B : ℕ) : ℕ := 16 * 10 ^ B

/-- The fixed reciprocal geometric separation parameter. -/
def localPrimitiveDDenom : ℕ := 2 ^ 157

/-- The reciprocal first-passage parameter at primitive order B. -/
def localPrimitiveEtaDenom (B : ℕ) : ℕ := 32 * B * localPrimitiveDDenom

/-- The initial layer parameter of the local primitive recipe. -/
def localPrimitiveK (B : ℕ) : ℕ := 16 * (B + 1) * 2 ^ 156

/-- The number of growth layers in the local primitive recipe. -/
def localPrimitiveR (B : ℕ) : ℕ := 4 * (localPrimitiveK B + 16 * (B + 1)) + 1

/-- The explicit collar growth multiplier. -/
def localPrimitiveA (B : ℕ) : ℕ := 64 * localPrimitiveDeltaDenom B

/-- The polynomial layer-growth coefficient. -/
def localPrimitiveH (B : ℕ) : ℕ :=
  2 ^ 17 * localPrimitiveA B ^ 2 * localPrimitiveDeltaDenom B

/-- The finite polynomial recurrence defining successive layer thresholds. -/
def localPrimitiveV (B : ℕ) : ℕ → ℕ
  | 0 => localPrimitiveK B
  | i + 1 =>
      localPrimitiveV B i + localPrimitiveH B * (localPrimitiveV B i + 1) ^ 4 +
        localPrimitiveK B + 2

/-- The terminal layer threshold with its prescribed margin. -/
def localPrimitiveP (B : ℕ) : ℕ :=
  localPrimitiveV B (localPrimitiveR B) + localPrimitiveK B + 2

/-- The terminal collar threshold used by the primitive cutoff. -/
def localPrimitiveZ (B : ℕ) : ℕ :=
  128 * localPrimitiveA B * (localPrimitiveP B + 1) ^ 2 * localPrimitiveDeltaDenom B

/-- The maximum of the explicit cutoff requirements in the primitive proof. -/
def localPrimitiveM (B : ℕ) : ℕ :=
  max (64 * B * localPrimitiveDDenom)
    (max (20 * (localPrimitiveP B + 1))
      (max ((2560 * (B + 1)) ^ 2)
        (max (localPrimitiveZ B ^ 2 * localPrimitiveEtaDenom B) 4096)))

/-- The locally derived primitive coefficient at the given order. -/
def localPrimitiveCoefficient (B : ℕ) : ℕ := (3 * localPrimitiveM B) ^ B

end LocalPrimitive
namespace Analytic
/-- The local primitive coefficient specialized to order 6409. -/
noncomputable def primitiveCoefficient : ℕ :=
  LocalPrimitive.localPrimitiveCoefficient 6409

/-- The primitive coefficient after the explicit order-6409 tail conversion. -/
noncomputable def tailCoefficient : ℝ := (primitiveCoefficient : ℝ) * (20 : ℝ) ^ 6409

/-- The rational power exponent of the fixed-width mixing estimate. -/
noncomputable def mixingExponent : ℝ := 2314 / 25

/-- The coefficient of the fixed-width power majorant. -/
noncomputable def mixingCoefficient : ℝ := 2 * tailCoefficient + 2

/-- The explicit first-passage failure terms at width v and level x. -/
noncomputable def failureEnvelope (v x : ℝ) : ℝ :=
  16 / ((v * Real.log 2) ^ 2 * Real.log x) * x ^ (1 - v * Real.log 2) +
    x ^ (-(v * Real.log 2)) + x ^ (-(v * Real.log 2) - 1)

/-- The sum of the Fourier-tail and first-passage failure envelopes. -/
noncomputable def mixingEnvelope (v x : ℝ) : ℝ :=
  2 * tailCoefficient * x ^ (-6407 + Real.log 2 * v ^ 2 / 2) +
    2 * failureEnvelope v x

/-- The infimum of the explicit mixing envelope over the fixed compact width interval. -/
noncomputable def widthMinimum (x : ℝ) : ℝ :=
  sInf ((fun v => mixingEnvelope v x) '' Set.Icc (80 : ℝ) (679 / 5))

/-- The compact mixing bound, using the power majorant below the width threshold. -/
noncomputable def mixingError (m : ℕ) : ℝ :=
  if m < 2 ^ 80 then min 2 ((mixingCoefficient : ℝ) * (m : ℝ) ^ (-mixingExponent))
  else min (min 2 ((mixingCoefficient : ℝ) * (m : ℝ) ^ (-mixingExponent)))
    (widthMinimum m)

end Analytic
namespace Reference
/-- The entropy increment majorant, clipped by log 3. -/
noncomputable def entropyError (n : ℕ) : ℝ :=
  min (Real.log 3) (Analytic.mixingError n)

end Reference
namespace Counting
/-- The same explicit radial conversion used by the baseline density statements. -/
noncomputable abbrev radial := CollatzWordCert.radial

/-- Full-group allocations bounded by harmonic capacity and paying the demanded fan mass. -/
def feasibleProfile (m : ℕ) (p : ℝ) (w : ZMod (3^m) → ℝ) : Prop :=
  (∀ r, 0 ≤ w r ∧ w r ≤ (2*Real.log 2)/(3 : ℝ)^m) ∧
    p ≤ ∑ r, w r*Reference.fan m r

/-- The infimum total allocation mass among feasible full-group fan allocations. -/
noncomputable def profile (m : ℕ) (p : ℝ) : ℝ :=
  sInf {u | ∃ w, feasibleProfile m p w ∧ u = ∑ r, w r}

end Counting
namespace Density
/-- The baseline positive small-score domain, reused for the profile conversion. -/
abbrev SmallScore := CollatzWordCert.SmallScore
/-- The nonnegative score remaining after the explicit mixing charge. -/
noncomputable def residual (W : ℝ) (m : ℕ) : ℝ :=
  max (W - kappa * Analytic.mixingError m) 0

end Density


private theorem wordPMF_eq (n : ℕ) :
    Reference.wordPMF n = WordCertDensity.Reference.wordPMF n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Reference.wordPMF, WordCertDensity.Reference.wordPMF, ih]
    rfl

private theorem residueOffset_eq (q : ℕ) (w : ValuationWord) :
    Reference.residueOffset q w = WordCertDensity.ValuationWord.residueOffset q w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [Reference.residueOffset, WordCertDensity.ValuationWord.residueOffset, ih]
    rfl

private theorem referenceLaw_eq (n : ℕ) :
    Reference.law n = WordCertDensity.Reference.law n := by
  have he : Reference.residueOffset n = WordCertDensity.ValuationWord.residueOffset n :=
    funext (residueOffset_eq n)
  rw [Reference.law, WordCertDensity.Reference.law, wordPMF_eq, he]

private theorem density_eq (n : ℕ) :
    Reference.density n = WordCertDensity.Reference.density n := by
  funext x
  unfold Reference.density WordCertDensity.Reference.density
    Reference.mass WordCertDensity.Reference.mass
  rw [referenceLaw_eq]

private theorem mean_eq (n : ℕ) :
    Reference.mean n = WordCertDensity.Reference.mean n := rfl

private theorem fan_eq (m : ℕ) :
    Reference.fan m = WordCertDensity.Reference.fan m := by
  funext x
  unfold Reference.fan WordCertDensity.Reference.fan
  congr 1
  funext j
  rw [Reference.marker, WordCertDensity.Reference.marker, density_eq]
  rfl

private theorem feasibleProfile_eq (m : ℕ) (p : ℝ) (w : ZMod (3 ^ m) → ℝ) :
    Counting.feasibleProfile m p w = WordCertDensity.Counting.feasibleProfile m p w := by
  unfold Counting.feasibleProfile WordCertDensity.Counting.feasibleProfile
  rw [fan_eq]

private theorem profile_eq (m : ℕ) (p : ℝ) :
    Counting.profile m p = WordCertDensity.Counting.profile m p := by
  unfold Counting.profile WordCertDensity.Counting.profile
  simp only [feasibleProfile_eq]

private theorem primitiveV_eq (B i : ℕ) :
    LocalPrimitive.localPrimitiveV B i = WordCertDensity.LocalPrimitive.localPrimitiveV B i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [LocalPrimitive.localPrimitiveV, WordCertDensity.LocalPrimitive.localPrimitiveV, ih]
    rfl

private theorem primitiveCoefficient_eq (B : ℕ) :
    LocalPrimitive.localPrimitiveCoefficient B =
      WordCertDensity.LocalPrimitive.localPrimitiveCoefficient B := by
  simp only [LocalPrimitive.localPrimitiveCoefficient,
    WordCertDensity.LocalPrimitive.localPrimitiveCoefficient,
    LocalPrimitive.localPrimitiveM, WordCertDensity.LocalPrimitive.localPrimitiveM,
    LocalPrimitive.localPrimitiveZ, WordCertDensity.LocalPrimitive.localPrimitiveZ,
    LocalPrimitive.localPrimitiveP, WordCertDensity.LocalPrimitive.localPrimitiveP,
    primitiveV_eq]
  rfl

private theorem tailCoefficient_eq :
    Analytic.tailCoefficient = WordCertDensity.Analytic.tailCoefficient := by
  unfold Analytic.tailCoefficient WordCertDensity.Analytic.tailCoefficient
    Analytic.primitiveCoefficient WordCertDensity.Analytic.primitiveCoefficient
  rw [primitiveCoefficient_eq]

private theorem mixingCoefficient_eq :
    Analytic.mixingCoefficient = WordCertDensity.Analytic.mixingCoefficient := by
  unfold Analytic.mixingCoefficient WordCertDensity.Analytic.mixingCoefficient
  rw [tailCoefficient_eq]

private theorem mixingEnvelope_eq (v x : ℝ) :
    Analytic.mixingEnvelope v x = WordCertDensity.Analytic.mixingEnvelope v x := by
  unfold Analytic.mixingEnvelope WordCertDensity.Analytic.mixingEnvelope
  rw [tailCoefficient_eq]
  rfl

private theorem widthMinimum_eq (x : ℝ) :
    Analytic.widthMinimum x = WordCertDensity.Analytic.widthMinimum x := by
  unfold Analytic.widthMinimum WordCertDensity.Analytic.widthMinimum
  simp only [mixingEnvelope_eq]

private theorem mixingError_eq (m : ℕ) :
    Analytic.mixingError m = WordCertDensity.Analytic.mixingError m := by
  unfold Analytic.mixingError WordCertDensity.Analytic.mixingError
  rw [mixingCoefficient_eq, widthMinimum_eq]
  rfl

private theorem residual_eq (W : ℝ) (m : ℕ) :
    Density.residual W m = WordCertDensity.Density.residual W m := by
  unfold Density.residual WordCertDensity.Density.residual
  rw [mixingError_eq]
  rfl

private theorem entropy_eq :
    Reference.entropy = WordCertDensity.Reference.entropy := by
  funext n
  unfold Reference.entropy WordCertDensity.Reference.entropy
  rw [mean_eq, density_eq]

private theorem entropyError_eq (n : ℕ) :
    Reference.entropyError n = WordCertDensity.Reference.entropyError n := by
  unfold Reference.entropyError WordCertDensity.Reference.entropyError
  rw [mixingError_eq]

/-- The exact full-group fan profile attains its hinge-dual allocation value, including zero and
full demand. -/
theorem profile_allocation (m : Nat) (p : Real) (hp : 0 <= p)
    (hpaid : p <= (2 * Real.log 2) * (8 / 9)) :
    (Exists fun w => Counting.feasibleProfile m p w /\
      (Finset.univ.sum fun r => w r) = Counting.profile m p) /\
    Counting.profile m p = sSup {a | Exists fun t : Real => 0 < t /\
      a = max (p - (2 * Real.log 2) * Reference.mean m
        (fun r => max (Reference.fan m r - t) 0)) 0 / t} /\
    0 <= Counting.profile m p /\
      Counting.profile m p <= p / (8 / 9) :=
  by
    simpa only [feasibleProfile_eq, profile_eq, mean_eq, fan_eq] using
      WordCertDensity.Release.AnalyticExtensions.profile_allocation m p hp hpaid

/-- Every real fan moment of order greater than one bounds the exact profile from below. -/
theorem profile_moment_bound (m : Nat) (p s B : Real) (hm : 2 <= m)
    (hp : 0 <= p) (hpaid : p <= (2 * Real.log 2) * (8 / 9))
    (hs : 1 < s) (hB : 0 < B)
    (hmoment : Reference.mean m (fun r => (Reference.fan m r) ^ s) <= B) :
    p ^ (s / (s - 1)) / ((2 * Real.log 2 * B) ^ (1 / (s - 1))) <=
      Counting.profile m p :=
  by
    have hmoment' := hmoment
    rw [mean_eq, fan_eq] at hmoment'
    simpa only [profile_eq] using
      WordCertDensity.Release.AnalyticExtensions.profile_moment_bound
        m p s B hm hp hpaid hs hB hmoment'

/-- One positive canonical residual and one level supply the exact profile bound for every
larger clock. -/
theorem profile_density :
    Exists fun W : Real => Density.SmallScore W /\
      Exists fun m : Nat => 2 <= m /\
        0 < Density.residual W m /\
        ∀ c : Real, criticalClock < c ->
          Counting.radial (Counting.profile m (Density.residual W m)) <=
            lowerNaturalDensity (goodTarget 1 c) :=
  by
    simpa only [Density.SmallScore, SmallScore, WordCertDensity.Density.SmallScore,
      residual_eq, profile_eq, Counting.radial, radial, WordCertDensity.Counting.radial,
      criticalClock_eq, goodTarget_eq, lowerNaturalDensity_eq] using
      WordCertDensity.Release.AnalyticExtensions.profile_density

/-- Every positive target not divisible by three has a positive residual and one profile level
for all larger clocks. -/
theorem target_profile_density {target : Nat} (htarget : 0 < target)
    (hnotthree : Not (3 ∣ target)) :
    Exists fun W : Real => Density.SmallScore W /\
      Exists fun m : Nat => 2 <= m /\
        0 < Density.residual W m /\
        ∀ c : Real, criticalClock < c ->
          Counting.radial (Counting.profile m (Density.residual W m)) <=
            lowerNaturalDensity (goodTarget target c) :=
  by
    simpa only [Density.SmallScore, SmallScore, WordCertDensity.Density.SmallScore,
      residual_eq, profile_eq, Counting.radial, radial, WordCertDensity.Counting.radial,
      criticalClock_eq, goodTarget_eq, lowerNaturalDensity_eq] using
      WordCertDensity.Release.AnalyticExtensions.target_profile_density htarget hnotthree

/-- The actual reference-law entropy increment obeys the compact mixing envelope at each
positive index. -/
theorem entropy_increment (n : Nat) (hn : 1 <= n) :
    0 <= Reference.entropy (n + 1) - Reference.entropy n /\
    Reference.entropy (n + 1) - Reference.entropy n <=
      min (Real.log 3) (Analytic.mixingError n) :=
  by
    simpa only [entropy_eq, mixingError_eq] using
      WordCertDensity.Release.AnalyticExtensions.entropy_increment n hn

/-- The actual full-group entropy has a finite monotone limit with an explicit summable tail. -/
theorem entropy_limit :
    Exists fun z : Real => Tendsto Reference.entropy atTop (nhds z) /\
      (∀ n, Reference.entropy n <= z) /\
      z <= (2 / 3) * Real.log 2 +
        tsum (fun j : Nat => Reference.entropyError (j + 1)) /\
      (∀ n, 1 <= n -> 0 <= z - Reference.entropy n /\
        z - Reference.entropy n <=
          tsum (fun j : Nat => Reference.entropyError (n + j)) ) :=
  by
    simpa only [entropy_eq, entropyError_eq] using
      WordCertDensity.Release.AnalyticExtensions.entropy_limit

/-- The normalized actual entropy and its positive-index normalized infimum both vanish. -/
theorem entropy_zero_rate :
    Tendsto (fun n : Nat => Reference.entropy n / n) atTop (nhds 0) /\
    (iInf fun n : Nat => Reference.entropy (n + 1) / (n + 1 : Real)) = 0 :=
  by
    simpa only [entropy_eq] using
      WordCertDensity.Release.AnalyticExtensions.entropy_zero_rate

end CollatzWordCert
