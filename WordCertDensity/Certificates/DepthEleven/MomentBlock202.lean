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
theorem levelEleven_energy_103424 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 103424 128 =
      33915207985354101658230911042075 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_103424 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103424 128 =
      1018576648902404692403343 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_103424 : ∀ i : Fin 128,
    levelEleven.lookup (103424 + i.val) ≤ levelElevenRoots.lookup (103424 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_103552 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 103552 128 =
      42743129809685982492821345994387 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_103552 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103552 128 =
      1033444532917617770020782 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_103552 : ∀ i : Fin 128,
    levelEleven.lookup (103552 + i.val) ≤ levelElevenRoots.lookup (103552 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_103680 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 103680 128 =
      38745539073082126578250995628189 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_103680 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103680 128 =
      1011773085226254512306876 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_103680 : ∀ i : Fin 128,
    levelEleven.lookup (103680 + i.val) ≤ levelElevenRoots.lookup (103680 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_103808 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 103808 128 =
      26255871577940492214208456569410 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_103808 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103808 128 =
      827168227176440800304381 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_103808 : ∀ i : Fin 128,
    levelEleven.lookup (103808 + i.val) ≤ levelElevenRoots.lookup (103808 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_202 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 103424 512 =
      141659748446062702943511709234061 := by
  have h0 := levelEleven_energy_103424
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 103424 256 =
      76658337795040084151052257036462 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 103424 128 128
      33915207985354101658230911042075 42743129809685982492821345994387 h0 levelEleven_energy_103552
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 103424 384 =
      115403876868122210729303252664651 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 103424 256 128
      76658337795040084151052257036462 38745539073082126578250995628189 h1 levelEleven_energy_103680
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 103424 512 =
      141659748446062702943511709234061 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 103424 384 128
      115403876868122210729303252664651 26255871577940492214208456569410 h2 levelEleven_energy_103808
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_202 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103424 512 =
      3890962494222717775035382 := by
  have h0 := levelEleven_fractional_103424
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103424 256 =
      2052021181820022462424125 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103424 128 128
      1018576648902404692403343 1033444532917617770020782 h0 levelEleven_fractional_103552
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103424 384 =
      3063794267046276974731001 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103424 256 128
      2052021181820022462424125 1011773085226254512306876 h1 levelEleven_fractional_103680
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103424 512 =
      3890962494222717775035382 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103424 384 128
      3063794267046276974731001 827168227176440800304381 h2 levelEleven_fractional_103808
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_202 : ∀ i : Fin 512,
    levelEleven.lookup (103424 + i.val) ≤ levelElevenRoots.lookup (103424 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_103424
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 103424 128 128
    h0 levelEleven_squares_103552
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 103424 256 128
    h1 levelEleven_squares_103680
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 103424 384 128
    h2 levelEleven_squares_103808
  exact h3

end WordCertDensity.Certificates
