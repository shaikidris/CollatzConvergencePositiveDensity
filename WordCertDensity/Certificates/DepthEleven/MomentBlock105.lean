/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.Data.LevelElevenRoots

/-! # Bounded depth-eleven moment certificates -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_53760 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 53760 128 =
      49751166892295275012665078489648 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_53760 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53760 128 =
      1216961861811209006722251 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_53760 : ∀ i : Fin 128,
    levelEleven.lookup (53760 + i.val) ≤ levelElevenRoots.lookup (53760 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_53888 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 53888 128 =
      106504152811334322445524735300589 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_53888 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53888 128 =
      1719494219514713160801455 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_53888 : ∀ i : Fin 128,
    levelEleven.lookup (53888 + i.val) ≤ levelElevenRoots.lookup (53888 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_54016 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 54016 128 =
      73831252973954110818420114600805 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_54016 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54016 128 =
      1492604765688709970406961 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_54016 : ∀ i : Fin 128,
    levelEleven.lookup (54016 + i.val) ≤ levelElevenRoots.lookup (54016 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_54144 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 54144 128 =
      30234759688355733945174571163745 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_54144 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54144 128 =
      913528884240360083119079 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_54144 : ∀ i : Fin 128,
    levelEleven.lookup (54144 + i.val) ≤ levelElevenRoots.lookup (54144 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_105 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 53760 512 =
      260321332365939442221784499554787 := by
  have h0 := levelEleven_energy_53760
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 53760 256 =
      156255319703629597458189813790237 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 53760 128 128
      49751166892295275012665078489648 106504152811334322445524735300589 h0 levelEleven_energy_53888
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 53760 384 =
      230086572677583708276609928391042 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 53760 256 128
      156255319703629597458189813790237 73831252973954110818420114600805 h1 levelEleven_energy_54016
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 53760 512 =
      260321332365939442221784499554787 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 53760 384 128
      230086572677583708276609928391042 30234759688355733945174571163745 h2 levelEleven_energy_54144
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_105 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53760 512 =
      5342589731254992221049746 := by
  have h0 := levelEleven_fractional_53760
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53760 256 =
      2936456081325922167523706 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53760 128 128
      1216961861811209006722251 1719494219514713160801455 h0 levelEleven_fractional_53888
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53760 384 =
      4429060847014632137930667 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53760 256 128
      2936456081325922167523706 1492604765688709970406961 h1 levelEleven_fractional_54016
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53760 512 =
      5342589731254992221049746 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53760 384 128
      4429060847014632137930667 913528884240360083119079 h2 levelEleven_fractional_54144
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_105 : ∀ i : Fin 512,
    levelEleven.lookup (53760 + i.val) ≤ levelElevenRoots.lookup (53760 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_53760
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 53760 128 128
    h0 levelEleven_squares_53888
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 53760 256 128
    h1 levelEleven_squares_54016
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 53760 384 128
    h2 levelEleven_squares_54144
  exact h3

end WordCertDensity.Certificates
