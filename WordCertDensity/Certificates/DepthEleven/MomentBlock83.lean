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
theorem levelEleven_energy_42496 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 42496 128 =
      96212375093476416857499093219567 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_42496 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42496 128 =
      1628585174078061996583894 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_42496 : ∀ i : Fin 128,
    levelEleven.lookup (42496 + i.val) ≤ levelElevenRoots.lookup (42496 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_42624 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 42624 128 =
      31192821388761052192647920304119 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_42624 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42624 128 =
      984760650773062153325471 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_42624 : ∀ i : Fin 128,
    levelEleven.lookup (42624 + i.val) ≤ levelElevenRoots.lookup (42624 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_42752 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 42752 128 =
      25167957757771233305101792570824 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_42752 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42752 128 =
      831294314395613310337307 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_42752 : ∀ i : Fin 128,
    levelEleven.lookup (42752 + i.val) ≤ levelElevenRoots.lookup (42752 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_42880 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 42880 128 =
      46727482492944690662966030530056 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_42880 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42880 128 =
      1162495676784799024811560 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_42880 : ∀ i : Fin 128,
    levelEleven.lookup (42880 + i.val) ≤ levelElevenRoots.lookup (42880 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_83 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 42496 512 =
      199300636732953393018214836624566 := by
  have h0 := levelEleven_energy_42496
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 42496 256 =
      127405196482237469050147013523686 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 42496 128 128
      96212375093476416857499093219567 31192821388761052192647920304119 h0 levelEleven_energy_42624
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 42496 384 =
      152573154240008702355248806094510 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 42496 256 128
      127405196482237469050147013523686 25167957757771233305101792570824 h1 levelEleven_energy_42752
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 42496 512 =
      199300636732953393018214836624566 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 42496 384 128
      152573154240008702355248806094510 46727482492944690662966030530056 h2 levelEleven_energy_42880
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_83 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42496 512 =
      4607135816031536485058232 := by
  have h0 := levelEleven_fractional_42496
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42496 256 =
      2613345824851124149909365 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42496 128 128
      1628585174078061996583894 984760650773062153325471 h0 levelEleven_fractional_42624
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42496 384 =
      3444640139246737460246672 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42496 256 128
      2613345824851124149909365 831294314395613310337307 h1 levelEleven_fractional_42752
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42496 512 =
      4607135816031536485058232 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42496 384 128
      3444640139246737460246672 1162495676784799024811560 h2 levelEleven_fractional_42880
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_83 : ∀ i : Fin 512,
    levelEleven.lookup (42496 + i.val) ≤ levelElevenRoots.lookup (42496 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_42496
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 42496 128 128
    h0 levelEleven_squares_42624
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 42496 256 128
    h1 levelEleven_squares_42752
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 42496 384 128
    h2 levelEleven_squares_42880
  exact h3

end WordCertDensity.Certificates
