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
theorem levelEleven_energy_125440 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 125440 128 =
      57470015252967015987447616649833 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_125440 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125440 128 =
      1238406547284679237225274 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_125440 : ∀ i : Fin 128,
    levelEleven.lookup (125440 + i.val) ≤ levelElevenRoots.lookup (125440 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_125568 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 125568 128 =
      28605163431600126074465069455994 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_125568 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125568 128 =
      872430600325756400526992 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_125568 : ∀ i : Fin 128,
    levelEleven.lookup (125568 + i.val) ≤ levelElevenRoots.lookup (125568 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_125696 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 125696 128 =
      63172757824368597648591817961627 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_125696 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125696 128 =
      1368744252269445199103505 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_125696 : ∀ i : Fin 128,
    levelEleven.lookup (125696 + i.val) ≤ levelElevenRoots.lookup (125696 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_125824 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 125824 128 =
      33681426195974456646070475973449 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_125824 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125824 128 =
      945690917508043840341887 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_125824 : ∀ i : Fin 128,
    levelEleven.lookup (125824 + i.val) ≤ levelElevenRoots.lookup (125824 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_245 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 125440 512 =
      182929362704910196356574980040903 := by
  have h0 := levelEleven_energy_125440
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 125440 256 =
      86075178684567142061912686105827 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 125440 128 128
      57470015252967015987447616649833 28605163431600126074465069455994 h0 levelEleven_energy_125568
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 125440 384 =
      149247936508935739710504504067454 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 125440 256 128
      86075178684567142061912686105827 63172757824368597648591817961627 h1 levelEleven_energy_125696
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 125440 512 =
      182929362704910196356574980040903 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 125440 384 128
      149247936508935739710504504067454 33681426195974456646070475973449 h2 levelEleven_energy_125824
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_245 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125440 512 =
      4425272317387924677197658 := by
  have h0 := levelEleven_fractional_125440
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125440 256 =
      2110837147610435637752266 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125440 128 128
      1238406547284679237225274 872430600325756400526992 h0 levelEleven_fractional_125568
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125440 384 =
      3479581399879880836855771 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125440 256 128
      2110837147610435637752266 1368744252269445199103505 h1 levelEleven_fractional_125696
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125440 512 =
      4425272317387924677197658 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125440 384 128
      3479581399879880836855771 945690917508043840341887 h2 levelEleven_fractional_125824
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_245 : ∀ i : Fin 512,
    levelEleven.lookup (125440 + i.val) ≤ levelElevenRoots.lookup (125440 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_125440
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 125440 128 128
    h0 levelEleven_squares_125568
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 125440 256 128
    h1 levelEleven_squares_125696
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 125440 384 128
    h2 levelEleven_squares_125824
  exact h3

end WordCertDensity.Certificates
