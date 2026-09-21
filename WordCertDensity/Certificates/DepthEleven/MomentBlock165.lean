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
theorem levelEleven_energy_84480 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 84480 128 =
      37341738415251758006324180407330 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_84480 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84480 128 =
      1045296636456516960143556 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_84480 : ∀ i : Fin 128,
    levelEleven.lookup (84480 + i.val) ≤ levelElevenRoots.lookup (84480 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_84608 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 84608 128 =
      31362843102251726677285099922470 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_84608 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84608 128 =
      871632651833536572962759 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_84608 : ∀ i : Fin 128,
    levelEleven.lookup (84608 + i.val) ≤ levelElevenRoots.lookup (84608 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_84736 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 84736 128 =
      99887247159478472765896225681454 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_84736 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84736 128 =
      1766599360582746458764918 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_84736 : ∀ i : Fin 128,
    levelEleven.lookup (84736 + i.val) ≤ levelElevenRoots.lookup (84736 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_84864 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 84864 128 =
      96252986452020363414565685306190 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_84864 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84864 128 =
      1671704766343242353859136 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_84864 : ∀ i : Fin 128,
    levelEleven.lookup (84864 + i.val) ≤ levelElevenRoots.lookup (84864 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_165 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 84480 512 =
      264844815129002320864071191317444 := by
  have h0 := levelEleven_energy_84480
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 84480 256 =
      68704581517503484683609280329800 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 84480 128 128
      37341738415251758006324180407330 31362843102251726677285099922470 h0 levelEleven_energy_84608
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 84480 384 =
      168591828676981957449505506011254 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 84480 256 128
      68704581517503484683609280329800 99887247159478472765896225681454 h1 levelEleven_energy_84736
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 84480 512 =
      264844815129002320864071191317444 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 84480 384 128
      168591828676981957449505506011254 96252986452020363414565685306190 h2 levelEleven_energy_84864
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_165 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84480 512 =
      5355233415216042345730369 := by
  have h0 := levelEleven_fractional_84480
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84480 256 =
      1916929288290053533106315 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84480 128 128
      1045296636456516960143556 871632651833536572962759 h0 levelEleven_fractional_84608
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84480 384 =
      3683528648872799991871233 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84480 256 128
      1916929288290053533106315 1766599360582746458764918 h1 levelEleven_fractional_84736
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84480 512 =
      5355233415216042345730369 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84480 384 128
      3683528648872799991871233 1671704766343242353859136 h2 levelEleven_fractional_84864
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_165 : ∀ i : Fin 512,
    levelEleven.lookup (84480 + i.val) ≤ levelElevenRoots.lookup (84480 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_84480
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 84480 128 128
    h0 levelEleven_squares_84608
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 84480 256 128
    h1 levelEleven_squares_84736
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 84480 384 128
    h2 levelEleven_squares_84864
  exact h3

end WordCertDensity.Certificates
