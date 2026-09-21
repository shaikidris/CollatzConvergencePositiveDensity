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
theorem levelEleven_energy_156160 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 156160 128 =
      40189063149561456594332178473650 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_156160 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156160 128 =
      1111681497920419642083010 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_156160 : ∀ i : Fin 128,
    levelEleven.lookup (156160 + i.val) ≤ levelElevenRoots.lookup (156160 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_156288 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 156288 128 =
      24517687238703817450079204212489 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_156288 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156288 128 =
      778342571996605895987281 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_156288 : ∀ i : Fin 128,
    levelEleven.lookup (156288 + i.val) ≤ levelElevenRoots.lookup (156288 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_156416 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 156416 128 =
      18330316487698970303631593660114 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_156416 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156416 128 =
      701491304965949808081888 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_156416 : ∀ i : Fin 128,
    levelEleven.lookup (156416 + i.val) ≤ levelElevenRoots.lookup (156416 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_156544 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 156544 128 =
      55023838951265635508287945242882 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_156544 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156544 128 =
      1223698070984562289534372 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_156544 : ∀ i : Fin 128,
    levelEleven.lookup (156544 + i.val) ≤ levelElevenRoots.lookup (156544 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_305 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 156160 512 =
      138060905827229879856330921589135 := by
  have h0 := levelEleven_energy_156160
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 156160 256 =
      64706750388265274044411382686139 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 156160 128 128
      40189063149561456594332178473650 24517687238703817450079204212489 h0 levelEleven_energy_156288
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 156160 384 =
      83037066875964244348042976346253 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 156160 256 128
      64706750388265274044411382686139 18330316487698970303631593660114 h1 levelEleven_energy_156416
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 156160 512 =
      138060905827229879856330921589135 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 156160 384 128
      83037066875964244348042976346253 55023838951265635508287945242882 h2 levelEleven_energy_156544
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_305 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156160 512 =
      3815213445867537635686551 := by
  have h0 := levelEleven_fractional_156160
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156160 256 =
      1890024069917025538070291 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156160 128 128
      1111681497920419642083010 778342571996605895987281 h0 levelEleven_fractional_156288
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156160 384 =
      2591515374882975346152179 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156160 256 128
      1890024069917025538070291 701491304965949808081888 h1 levelEleven_fractional_156416
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156160 512 =
      3815213445867537635686551 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156160 384 128
      2591515374882975346152179 1223698070984562289534372 h2 levelEleven_fractional_156544
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_305 : ∀ i : Fin 512,
    levelEleven.lookup (156160 + i.val) ≤ levelElevenRoots.lookup (156160 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_156160
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 156160 128 128
    h0 levelEleven_squares_156288
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 156160 256 128
    h1 levelEleven_squares_156416
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 156160 384 128
    h2 levelEleven_squares_156544
  exact h3

end WordCertDensity.Certificates
