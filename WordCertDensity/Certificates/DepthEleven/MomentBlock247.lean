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
theorem levelEleven_energy_126464 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 126464 128 =
      48917667022130507770836174673365 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_126464 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126464 128 =
      1148294409972091621815100 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_126464 : ∀ i : Fin 128,
    levelEleven.lookup (126464 + i.val) ≤ levelElevenRoots.lookup (126464 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_126592 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 126592 128 =
      65279869559478230241211204783460 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_126592 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126592 128 =
      1317685945664032457647430 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_126592 : ∀ i : Fin 128,
    levelEleven.lookup (126592 + i.val) ≤ levelElevenRoots.lookup (126592 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_126720 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 126720 128 =
      50307513304855434996481874634857 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_126720 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126720 128 =
      1271492696993223057335720 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_126720 : ∀ i : Fin 128,
    levelEleven.lookup (126720 + i.val) ≤ levelElevenRoots.lookup (126720 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_126848 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 126848 128 =
      24039928125130563363045646358704 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_126848 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126848 128 =
      752598190629880533083771 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_126848 : ∀ i : Fin 128,
    levelEleven.lookup (126848 + i.val) ≤ levelElevenRoots.lookup (126848 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_247 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 126464 512 =
      188544978011594736371574900450386 := by
  have h0 := levelEleven_energy_126464
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 126464 256 =
      114197536581608738012047379456825 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 126464 128 128
      48917667022130507770836174673365 65279869559478230241211204783460 h0 levelEleven_energy_126592
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 126464 384 =
      164505049886464173008529254091682 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 126464 256 128
      114197536581608738012047379456825 50307513304855434996481874634857 h1 levelEleven_energy_126720
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 126464 512 =
      188544978011594736371574900450386 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 126464 384 128
      164505049886464173008529254091682 24039928125130563363045646358704 h2 levelEleven_energy_126848
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_247 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126464 512 =
      4490071243259227669882021 := by
  have h0 := levelEleven_fractional_126464
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126464 256 =
      2465980355636124079462530 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126464 128 128
      1148294409972091621815100 1317685945664032457647430 h0 levelEleven_fractional_126592
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126464 384 =
      3737473052629347136798250 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126464 256 128
      2465980355636124079462530 1271492696993223057335720 h1 levelEleven_fractional_126720
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126464 512 =
      4490071243259227669882021 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126464 384 128
      3737473052629347136798250 752598190629880533083771 h2 levelEleven_fractional_126848
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_247 : ∀ i : Fin 512,
    levelEleven.lookup (126464 + i.val) ≤ levelElevenRoots.lookup (126464 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_126464
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 126464 128 128
    h0 levelEleven_squares_126592
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 126464 256 128
    h1 levelEleven_squares_126720
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 126464 384 128
    h2 levelEleven_squares_126848
  exact h3

end WordCertDensity.Certificates
