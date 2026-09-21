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
theorem levelEleven_energy_21504 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 21504 128 =
      28482147648386124060139610013153 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_21504 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21504 128 =
      893031017599448914994376 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_21504 : ∀ i : Fin 128,
    levelEleven.lookup (21504 + i.val) ≤ levelElevenRoots.lookup (21504 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_21632 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 21632 128 =
      45756069522811288419605094475730 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_21632 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21632 128 =
      1103247892330275252054052 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_21632 : ∀ i : Fin 128,
    levelEleven.lookup (21632 + i.val) ≤ levelElevenRoots.lookup (21632 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_21760 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 21760 128 =
      90967042695619157195108523501006 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_21760 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21760 128 =
      1640068897986863473887343 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_21760 : ∀ i : Fin 128,
    levelEleven.lookup (21760 + i.val) ≤ levelElevenRoots.lookup (21760 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_21888 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 21888 128 =
      42958675672706485198845846372937 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_21888 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21888 128 =
      984624871080516807716969 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_21888 : ∀ i : Fin 128,
    levelEleven.lookup (21888 + i.val) ≤ levelElevenRoots.lookup (21888 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_42 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 21504 512 =
      208163935539523054873699074362826 := by
  have h0 := levelEleven_energy_21504
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 21504 256 =
      74238217171197412479744704488883 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 21504 128 128
      28482147648386124060139610013153 45756069522811288419605094475730 h0 levelEleven_energy_21632
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 21504 384 =
      165205259866816569674853227989889 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 21504 256 128
      74238217171197412479744704488883 90967042695619157195108523501006 h1 levelEleven_energy_21760
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 21504 512 =
      208163935539523054873699074362826 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 21504 384 128
      165205259866816569674853227989889 42958675672706485198845846372937 h2 levelEleven_energy_21888
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_42 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21504 512 =
      4620972678997104448652740 := by
  have h0 := levelEleven_fractional_21504
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21504 256 =
      1996278909929724167048428 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21504 128 128
      893031017599448914994376 1103247892330275252054052 h0 levelEleven_fractional_21632
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21504 384 =
      3636347807916587640935771 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21504 256 128
      1996278909929724167048428 1640068897986863473887343 h1 levelEleven_fractional_21760
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21504 512 =
      4620972678997104448652740 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21504 384 128
      3636347807916587640935771 984624871080516807716969 h2 levelEleven_fractional_21888
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_42 : ∀ i : Fin 512,
    levelEleven.lookup (21504 + i.val) ≤ levelElevenRoots.lookup (21504 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_21504
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 21504 128 128
    h0 levelEleven_squares_21632
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 21504 256 128
    h1 levelEleven_squares_21760
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 21504 384 128
    h2 levelEleven_squares_21888
  exact h3

end WordCertDensity.Certificates
