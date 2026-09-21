/-
Copyright (c) 2026 Idris Ali Shaik.
SPDX-License-Identifier: Apache-2.0
Authors: Idris Ali Shaik
-/
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Phase 1 WordCertDensity Challenge surface

This Mathlib-only Challenge advertises eighteen selected Phase 1 statements and
corollaries: common positive lower density above the reference clock, the named
depth-eleven and fractional formulas, the numerical clock, every admissible
fixed target with the exact multiple-of-three criterion, an explicit canonical
root, and vanishing clock-loss variants. The seven companions add exact
fan allocation, real-moment comparison, profile density for canonical and
admissible targets, entropy increments, its finite limit and tail, and zero
normalized entropy growth. The Renyi-order right limit and complementary
capacity comparison remain outside this surface.

Every density formula is written out here in full. The fractional formula takes
an existential paid residual `p` constrained by `W/2 < p ≤ W`. These bounds do
not uniquely specify the production residual; Solution supplies that witness.

The scores `W` are existential and the densities are not evaluated. The surface
does not claim effective cutoffs, optimizer recipes (`fmDensity`, `cFM`,
`cFM16`, `ccomp`), the Renyi-order right limit, complementary capacity,
amplified roots, or pointwise Collatz convergence. `individual_root` is a
concrete witness whose density conclusion follows from `every_admissible_target`.
-/

namespace CollatzWordCert

open Filter
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

/-- One positive lower density before every clock above the threshold. -/
theorem common_density : CommonClockDensity := by
  sorry

/-- A positive small score and coarse level give the depth-eleven formula. -/
theorem depthEleven_density :
    ∃ (W : ℝ) (m : ℕ), SmallScore W ∧ 2 ≤ m ∧
      EveryClockDensityBound (secondElevenDensity W m) := by
  sorry

/-- The reference threshold lies strictly below the printed rational clock. -/
theorem numerical_clock : criticalClock < 10431 / 1000 := by
  sorry

/-- Every positive target not divisible by three has its own positive density. -/
theorem every_admissible_target {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ d : ℝ, 0 < d ∧ TargetBound n d := by
  sorry

/-- The same targets also carry the depth-eleven formula. -/
theorem every_admissible_target_depthEleven {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ (W : ℝ) (m : ℕ), 0 < W ∧ 2 ≤ m ∧
      TargetBound n (secondElevenDensity W m) := by
  sorry

/-- Positive density holds precisely off the multiples of three. -/
theorem target_criterion (target : ℕ) (htarget : 0 < target) (c : ℝ)
    (hc : criticalClock < c) :
    0 < lowerNaturalDensity (goodTarget target c) ↔ ¬ 3 ∣ target := by
  sorry

/-- An explicit canonical root `r = (4^s-1)/3`, with `s ≥ 2` (starting at 5),
visits one at ordinary step `2s+1` and has its own positive density.

This is a concrete-witness corollary. Its density conclusion follows from
`every_admissible_target`; no independent content is claimed. -/
theorem individual_root :
    ∃ r s : ℕ, 2 ≤ s ∧ 3 * r + 1 = 4 ^ s ∧ ReachesIn r 1 (2 * s + 1) ∧
      ∃ d : ℝ, TargetBound r d := by
  sorry

/-- Convergence to one survives a positive antitone loss tending to zero. -/
theorem common_vanishing_clock :
    ∃ d : ℝ, 0 < d ∧ ∃ η : ℕ → ℝ,
      (∀ x, 0 < η x) ∧ Antitone η ∧ Tendsto η atTop (𝓝 0) ∧
      d ≤ lowerNaturalDensity {x : ℕ | 0 < x ∧
        ReachesWithin x 1 ((criticalClock + η x) * Real.log x)} := by
  sorry

/-- Each admissible target keeps its constant under a vanishing loss. -/
theorem target_vanishing_clock {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ d : ℝ, 0 < d ∧ ∃ η : ℕ → ℝ,
      (∀ x, 0 < η x) ∧ Antitone η ∧ Tendsto η atTop (𝓝 0) ∧
      d ≤ lowerNaturalDensity {x : ℕ | 0 < x ∧
        ReachesWithin x n ((criticalClock + η x) * Real.log x)} := by
  sorry

/-- A positive small score carries the order-three-halves formula at a paid level,
with the paid residual `p` strictly above `W/2` and at most `W`. -/
theorem fractional_density :
    ∃ (W p : ℝ) (m : ℕ), SmallScore W ∧ 2 ≤ m ∧ W / 2 < p ∧ p ≤ W ∧
      EveryClockDensityBound (fractionalDensityAt p m) := by
  sorry

/-- Every admissible fixed target carries the fractional formula, at a paid
residual `p` strictly above `W/2` and at most `W`. -/
theorem every_admissible_target_fractional {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ (W p : ℝ) (m : ℕ), 0 < W ∧ 2 ≤ m ∧ W / 2 < p ∧ p ≤ W ∧
      TargetBound n (fractionalDensityAt p m) := by
  sorry

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
      Counting.profile m p <= p / (8 / 9) := by
  sorry

/-- Every real fan moment of order greater than one bounds the exact profile from below. -/
theorem profile_moment_bound (m : Nat) (p s B : Real) (hm : 2 <= m)
    (hp : 0 <= p) (hpaid : p <= (2 * Real.log 2) * (8 / 9))
    (hs : 1 < s) (hB : 0 < B)
    (hmoment : Reference.mean m (fun r => (Reference.fan m r) ^ s) <= B) :
    p ^ (s / (s - 1)) / ((2 * Real.log 2 * B) ^ (1 / (s - 1))) <=
      Counting.profile m p := by
  sorry

/-- One positive canonical residual and one level supply the exact profile bound for every
larger clock. -/
theorem profile_density :
    Exists fun W : Real => Density.SmallScore W /\
      Exists fun m : Nat => 2 <= m /\
        0 < Density.residual W m /\
        ∀ c : Real, criticalClock < c ->
          Counting.radial (Counting.profile m (Density.residual W m)) <=
            lowerNaturalDensity (goodTarget 1 c) := by
  sorry

/-- Every positive target not divisible by three has a positive residual and one profile level
for all larger clocks. -/
theorem target_profile_density {target : Nat} (htarget : 0 < target)
    (hnotthree : Not (3 ∣ target)) :
    Exists fun W : Real => Density.SmallScore W /\
      Exists fun m : Nat => 2 <= m /\
        0 < Density.residual W m /\
        ∀ c : Real, criticalClock < c ->
          Counting.radial (Counting.profile m (Density.residual W m)) <=
            lowerNaturalDensity (goodTarget target c) := by
  sorry

/-- The actual reference-law entropy increment obeys the compact mixing envelope at each
positive index. -/
theorem entropy_increment (n : Nat) (hn : 1 <= n) :
    0 <= Reference.entropy (n + 1) - Reference.entropy n /\
    Reference.entropy (n + 1) - Reference.entropy n <=
      min (Real.log 3) (Analytic.mixingError n) := by
  sorry

/-- The actual full-group entropy has a finite monotone limit with an explicit summable tail. -/
theorem entropy_limit :
    Exists fun z : Real => Tendsto Reference.entropy atTop (nhds z) /\
      (∀ n, Reference.entropy n <= z) /\
      z <= (2 / 3) * Real.log 2 +
        tsum (fun j : Nat => Reference.entropyError (j + 1)) /\
      (∀ n, 1 <= n -> 0 <= z - Reference.entropy n /\
        z - Reference.entropy n <=
          tsum (fun j : Nat => Reference.entropyError (n + j)) ) := by
  sorry

/-- The normalized actual entropy and its positive-index normalized infimum both vanish. -/
theorem entropy_zero_rate :
    Tendsto (fun n : Nat => Reference.entropy n / n) atTop (nhds 0) /\
    (iInf fun n : Nat => Reference.entropy (n + 1) / (n + 1 : Real)) = 0 := by
  sorry


end CollatzWordCert
