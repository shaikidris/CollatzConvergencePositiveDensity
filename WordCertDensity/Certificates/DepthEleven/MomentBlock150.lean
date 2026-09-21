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
theorem levelEleven_energy_76800 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 76800 128 =
      21912491887541657499163209702207 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_76800 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76800 128 =
      769069118612417940169855 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_76800 : ∀ i : Fin 128,
    levelEleven.lookup (76800 + i.val) ≤ levelElevenRoots.lookup (76800 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_76928 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 76928 128 =
      49000196091062063881050762630055 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_76928 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76928 128 =
      1228747624925393642926702 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_76928 : ∀ i : Fin 128,
    levelEleven.lookup (76928 + i.val) ≤ levelElevenRoots.lookup (76928 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_77056 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 77056 128 =
      15558914974956635374183782525083 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_77056 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77056 128 =
      579860007535971624380250 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_77056 : ∀ i : Fin 128,
    levelEleven.lookup (77056 + i.val) ≤ levelElevenRoots.lookup (77056 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_77184 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 77184 128 =
      26228862381891950100332180095823 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_77184 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77184 128 =
      846786956638972444019416 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_77184 : ∀ i : Fin 128,
    levelEleven.lookup (77184 + i.val) ≤ levelElevenRoots.lookup (77184 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_150 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 76800 512 =
      112700465335452306854729934953168 := by
  have h0 := levelEleven_energy_76800
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 76800 256 =
      70912687978603721380213972332262 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 76800 128 128
      21912491887541657499163209702207 49000196091062063881050762630055 h0 levelEleven_energy_76928
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 76800 384 =
      86471602953560356754397754857345 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 76800 256 128
      70912687978603721380213972332262 15558914974956635374183782525083 h1 levelEleven_energy_77056
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 76800 512 =
      112700465335452306854729934953168 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 76800 384 128
      86471602953560356754397754857345 26228862381891950100332180095823 h2 levelEleven_energy_77184
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_150 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76800 512 =
      3424463707712755651496223 := by
  have h0 := levelEleven_fractional_76800
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76800 256 =
      1997816743537811583096557 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76800 128 128
      769069118612417940169855 1228747624925393642926702 h0 levelEleven_fractional_76928
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76800 384 =
      2577676751073783207476807 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76800 256 128
      1997816743537811583096557 579860007535971624380250 h1 levelEleven_fractional_77056
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76800 512 =
      3424463707712755651496223 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76800 384 128
      2577676751073783207476807 846786956638972444019416 h2 levelEleven_fractional_77184
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_150 : ∀ i : Fin 512,
    levelEleven.lookup (76800 + i.val) ≤ levelElevenRoots.lookup (76800 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_76800
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 76800 128 128
    h0 levelEleven_squares_76928
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 76800 256 128
    h1 levelEleven_squares_77056
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 76800 384 128
    h2 levelEleven_squares_77184
  exact h3

end WordCertDensity.Certificates
