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
theorem levelEleven_energy_172032 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 172032 128 =
      36137246878863815617308097791299 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_172032 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172032 128 =
      962903952894585637810909 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_172032 : ∀ i : Fin 128,
    levelEleven.lookup (172032 + i.val) ≤ levelElevenRoots.lookup (172032 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_172160 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 172160 128 =
      279651332312558912631398437031004 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_172160 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172160 128 =
      3153998421291136060396776 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_172160 : ∀ i : Fin 128,
    levelEleven.lookup (172160 + i.val) ≤ levelElevenRoots.lookup (172160 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_172288 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 172288 128 =
      64574515578100611224444642280451 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_172288 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172288 128 =
      1484200651670629300457501 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_172288 : ∀ i : Fin 128,
    levelEleven.lookup (172288 + i.val) ≤ levelElevenRoots.lookup (172288 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_172416 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 172416 128 =
      49770937353717277418216415631048 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_172416 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172416 128 =
      1202967439660741121370526 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_172416 : ∀ i : Fin 128,
    levelEleven.lookup (172416 + i.val) ≤ levelElevenRoots.lookup (172416 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_336 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 172032 512 =
      430134032123240616891367592733802 := by
  have h0 := levelEleven_energy_172032
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 172032 256 =
      315788579191422728248706534822303 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 172032 128 128
      36137246878863815617308097791299 279651332312558912631398437031004 h0 levelEleven_energy_172160
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 172032 384 =
      380363094769523339473151177102754 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 172032 256 128
      315788579191422728248706534822303 64574515578100611224444642280451 h1 levelEleven_energy_172288
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 172032 512 =
      430134032123240616891367592733802 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 172032 384 128
      380363094769523339473151177102754 49770937353717277418216415631048 h2 levelEleven_energy_172416
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_336 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172032 512 =
      6804070465517092120035712 := by
  have h0 := levelEleven_fractional_172032
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172032 256 =
      4116902374185721698207685 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172032 128 128
      962903952894585637810909 3153998421291136060396776 h0 levelEleven_fractional_172160
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172032 384 =
      5601103025856350998665186 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172032 256 128
      4116902374185721698207685 1484200651670629300457501 h1 levelEleven_fractional_172288
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172032 512 =
      6804070465517092120035712 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172032 384 128
      5601103025856350998665186 1202967439660741121370526 h2 levelEleven_fractional_172416
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_336 : ∀ i : Fin 512,
    levelEleven.lookup (172032 + i.val) ≤ levelElevenRoots.lookup (172032 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_172032
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 172032 128 128
    h0 levelEleven_squares_172160
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 172032 256 128
    h1 levelEleven_squares_172288
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 172032 384 128
    h2 levelEleven_squares_172416
  exact h3

end WordCertDensity.Certificates
