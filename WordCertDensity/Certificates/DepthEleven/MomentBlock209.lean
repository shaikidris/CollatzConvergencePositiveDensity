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
theorem levelEleven_energy_107008 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 107008 128 =
      167980599055996568602405219822643 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_107008 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107008 128 =
      2297032914310993578301615 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_107008 : ∀ i : Fin 128,
    levelEleven.lookup (107008 + i.val) ≤ levelElevenRoots.lookup (107008 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_107136 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 107136 128 =
      38031157241971844009841173219603 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_107136 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107136 128 =
      906887402510489923675933 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_107136 : ∀ i : Fin 128,
    levelEleven.lookup (107136 + i.val) ≤ levelElevenRoots.lookup (107136 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_107264 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 107264 128 =
      43210952845178648383187470128773 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_107264 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107264 128 =
      1145870190233112726012324 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_107264 : ∀ i : Fin 128,
    levelEleven.lookup (107264 + i.val) ≤ levelElevenRoots.lookup (107264 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_107392 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 107392 128 =
      39588714755905422063183624252172 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_107392 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107392 128 =
      1066673415395821115443788 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_107392 : ∀ i : Fin 128,
    levelEleven.lookup (107392 + i.val) ≤ levelElevenRoots.lookup (107392 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_209 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 107008 512 =
      288811423899052483058617487423191 := by
  have h0 := levelEleven_energy_107008
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 107008 256 =
      206011756297968412612246393042246 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 107008 128 128
      167980599055996568602405219822643 38031157241971844009841173219603 h0 levelEleven_energy_107136
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 107008 384 =
      249222709143147060995433863171019 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 107008 256 128
      206011756297968412612246393042246 43210952845178648383187470128773 h1 levelEleven_energy_107264
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 107008 512 =
      288811423899052483058617487423191 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 107008 384 128
      249222709143147060995433863171019 39588714755905422063183624252172 h2 levelEleven_energy_107392
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_209 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107008 512 =
      5416463922450417343433660 := by
  have h0 := levelEleven_fractional_107008
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107008 256 =
      3203920316821483501977548 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107008 128 128
      2297032914310993578301615 906887402510489923675933 h0 levelEleven_fractional_107136
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107008 384 =
      4349790507054596227989872 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107008 256 128
      3203920316821483501977548 1145870190233112726012324 h1 levelEleven_fractional_107264
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107008 512 =
      5416463922450417343433660 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107008 384 128
      4349790507054596227989872 1066673415395821115443788 h2 levelEleven_fractional_107392
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_209 : ∀ i : Fin 512,
    levelEleven.lookup (107008 + i.val) ≤ levelElevenRoots.lookup (107008 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_107008
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 107008 128 128
    h0 levelEleven_squares_107136
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 107008 256 128
    h1 levelEleven_squares_107264
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 107008 384 128
    h2 levelEleven_squares_107392
  exact h3

end WordCertDensity.Certificates
