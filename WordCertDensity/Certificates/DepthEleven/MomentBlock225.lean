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
theorem levelEleven_energy_115200 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 115200 128 =
      18919680287258822634610271831922 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_115200 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115200 128 =
      661982418722635499639614 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_115200 : ∀ i : Fin 128,
    levelEleven.lookup (115200 + i.val) ≤ levelElevenRoots.lookup (115200 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_115328 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 115328 128 =
      56705201618482710096803528419214 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_115328 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115328 128 =
      1370583552277474956060078 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_115328 : ∀ i : Fin 128,
    levelEleven.lookup (115328 + i.val) ≤ levelElevenRoots.lookup (115328 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_115456 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 115456 128 =
      86022197867658699552184822888072 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_115456 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115456 128 =
      1569554565830307113349078 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_115456 : ∀ i : Fin 128,
    levelEleven.lookup (115456 + i.val) ≤ levelElevenRoots.lookup (115456 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_115584 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 115584 128 =
      26884671228617029235579815457901 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_115584 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115584 128 =
      880831700102003636371896 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_115584 : ∀ i : Fin 128,
    levelEleven.lookup (115584 + i.val) ≤ levelElevenRoots.lookup (115584 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_225 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 115200 512 =
      188531751002017261519178438597109 := by
  have h0 := levelEleven_energy_115200
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 115200 256 =
      75624881905741532731413800251136 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 115200 128 128
      18919680287258822634610271831922 56705201618482710096803528419214 h0 levelEleven_energy_115328
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 115200 384 =
      161647079773400232283598623139208 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 115200 256 128
      75624881905741532731413800251136 86022197867658699552184822888072 h1 levelEleven_energy_115456
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 115200 512 =
      188531751002017261519178438597109 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 115200 384 128
      161647079773400232283598623139208 26884671228617029235579815457901 h2 levelEleven_energy_115584
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_225 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115200 512 =
      4482952236932421205420666 := by
  have h0 := levelEleven_fractional_115200
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115200 256 =
      2032565971000110455699692 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115200 128 128
      661982418722635499639614 1370583552277474956060078 h0 levelEleven_fractional_115328
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115200 384 =
      3602120536830417569048770 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115200 256 128
      2032565971000110455699692 1569554565830307113349078 h1 levelEleven_fractional_115456
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115200 512 =
      4482952236932421205420666 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115200 384 128
      3602120536830417569048770 880831700102003636371896 h2 levelEleven_fractional_115584
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_225 : ∀ i : Fin 512,
    levelEleven.lookup (115200 + i.val) ≤ levelElevenRoots.lookup (115200 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_115200
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 115200 128 128
    h0 levelEleven_squares_115328
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 115200 256 128
    h1 levelEleven_squares_115456
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 115200 384 128
    h2 levelEleven_squares_115584
  exact h3

end WordCertDensity.Certificates
