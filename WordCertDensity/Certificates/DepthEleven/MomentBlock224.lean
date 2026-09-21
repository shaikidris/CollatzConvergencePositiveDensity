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
theorem levelEleven_energy_114688 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 114688 128 =
      53681508577990577649405075359290 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_114688 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114688 128 =
      1195015375978160970189373 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_114688 : ∀ i : Fin 128,
    levelEleven.lookup (114688 + i.val) ≤ levelElevenRoots.lookup (114688 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_114816 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 114816 128 =
      89705257608793832486720593406568 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_114816 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114816 128 =
      1566684628091926669419554 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_114816 : ∀ i : Fin 128,
    levelEleven.lookup (114816 + i.val) ≤ levelElevenRoots.lookup (114816 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_114944 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 114944 128 =
      37001862620748474597644390154256 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_114944 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114944 128 =
      980970320984945400568030 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_114944 : ∀ i : Fin 128,
    levelEleven.lookup (114944 + i.val) ≤ levelElevenRoots.lookup (114944 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_115072 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 115072 128 =
      126446100335921278208837532343086 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_115072 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115072 128 =
      2007410306004255716281111 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_115072 : ∀ i : Fin 128,
    levelEleven.lookup (115072 + i.val) ≤ levelElevenRoots.lookup (115072 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_224 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 114688 512 =
      306834729143454162942607591263200 := by
  have h0 := levelEleven_energy_114688
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 114688 256 =
      143386766186784410136125668765858 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 114688 128 128
      53681508577990577649405075359290 89705257608793832486720593406568 h0 levelEleven_energy_114816
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 114688 384 =
      180388628807532884733770058920114 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 114688 256 128
      143386766186784410136125668765858 37001862620748474597644390154256 h1 levelEleven_energy_114944
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 114688 512 =
      306834729143454162942607591263200 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 114688 384 128
      180388628807532884733770058920114 126446100335921278208837532343086 h2 levelEleven_energy_115072
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_224 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114688 512 =
      5750080631059288756458068 := by
  have h0 := levelEleven_fractional_114688
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114688 256 =
      2761700004070087639608927 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114688 128 128
      1195015375978160970189373 1566684628091926669419554 h0 levelEleven_fractional_114816
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114688 384 =
      3742670325055033040176957 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114688 256 128
      2761700004070087639608927 980970320984945400568030 h1 levelEleven_fractional_114944
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114688 512 =
      5750080631059288756458068 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114688 384 128
      3742670325055033040176957 2007410306004255716281111 h2 levelEleven_fractional_115072
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_224 : ∀ i : Fin 512,
    levelEleven.lookup (114688 + i.val) ≤ levelElevenRoots.lookup (114688 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_114688
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 114688 128 128
    h0 levelEleven_squares_114816
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 114688 256 128
    h1 levelEleven_squares_114944
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 114688 384 128
    h2 levelEleven_squares_115072
  exact h3

end WordCertDensity.Certificates
