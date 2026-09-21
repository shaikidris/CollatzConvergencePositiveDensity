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
theorem levelEleven_energy_132608 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 132608 128 =
      49829768048483139228686425914822 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_132608 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132608 128 =
      1103634202278914612255425 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_132608 : ∀ i : Fin 128,
    levelEleven.lookup (132608 + i.val) ≤ levelElevenRoots.lookup (132608 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_132736 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 132736 128 =
      768834198996786404043600619241700 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_132736 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132736 128 =
      5694655331620722778722717 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_132736 : ∀ i : Fin 128,
    levelEleven.lookup (132736 + i.val) ≤ levelElevenRoots.lookup (132736 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_132864 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 132864 128 =
      28872851117854685043500390902858 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_132864 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132864 128 =
      910248206482811465315612 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_132864 : ∀ i : Fin 128,
    levelEleven.lookup (132864 + i.val) ≤ levelElevenRoots.lookup (132864 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_132992 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 132992 128 =
      57129892465073657579191725702410 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_132992 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132992 128 =
      1391537886184395391922573 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_132992 : ∀ i : Fin 128,
    levelEleven.lookup (132992 + i.val) ≤ levelElevenRoots.lookup (132992 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_259 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 132608 512 =
      904666710628197885894979161761790 := by
  have h0 := levelEleven_energy_132608
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 132608 256 =
      818663967045269543272287045156522 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 132608 128 128
      49829768048483139228686425914822 768834198996786404043600619241700 h0 levelEleven_energy_132736
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 132608 384 =
      847536818163124228315787436059380 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 132608 256 128
      818663967045269543272287045156522 28872851117854685043500390902858 h1 levelEleven_energy_132864
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 132608 512 =
      904666710628197885894979161761790 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 132608 384 128
      847536818163124228315787436059380 57129892465073657579191725702410 h2 levelEleven_energy_132992
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_259 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132608 512 =
      9100075626566844248216327 := by
  have h0 := levelEleven_fractional_132608
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132608 256 =
      6798289533899637390978142 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132608 128 128
      1103634202278914612255425 5694655331620722778722717 h0 levelEleven_fractional_132736
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132608 384 =
      7708537740382448856293754 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132608 256 128
      6798289533899637390978142 910248206482811465315612 h1 levelEleven_fractional_132864
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132608 512 =
      9100075626566844248216327 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132608 384 128
      7708537740382448856293754 1391537886184395391922573 h2 levelEleven_fractional_132992
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_259 : ∀ i : Fin 512,
    levelEleven.lookup (132608 + i.val) ≤ levelElevenRoots.lookup (132608 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_132608
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 132608 128 128
    h0 levelEleven_squares_132736
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 132608 256 128
    h1 levelEleven_squares_132864
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 132608 384 128
    h2 levelEleven_squares_132992
  exact h3

end WordCertDensity.Certificates
