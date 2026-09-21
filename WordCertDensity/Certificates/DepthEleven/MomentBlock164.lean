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
theorem levelEleven_energy_83968 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 83968 128 =
      46023557660398842779830837089850 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_83968 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83968 128 =
      1129784144787998579878309 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_83968 : ∀ i : Fin 128,
    levelEleven.lookup (83968 + i.val) ≤ levelElevenRoots.lookup (83968 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_84096 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 84096 128 =
      29564206829780929226194889594938 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_84096 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84096 128 =
      894801290150535805071869 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_84096 : ∀ i : Fin 128,
    levelEleven.lookup (84096 + i.val) ≤ levelElevenRoots.lookup (84096 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_84224 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 84224 128 =
      25617807636684152116141113987286 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_84224 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84224 128 =
      872617592452037847175722 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_84224 : ∀ i : Fin 128,
    levelEleven.lookup (84224 + i.val) ≤ levelElevenRoots.lookup (84224 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_84352 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 84352 128 =
      93703129965995860940103963541915 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_84352 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84352 128 =
      1561572925628661499042694 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_84352 : ∀ i : Fin 128,
    levelEleven.lookup (84352 + i.val) ≤ levelElevenRoots.lookup (84352 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_164 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 83968 512 =
      194908702092859785062270804213989 := by
  have h0 := levelEleven_energy_83968
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 83968 256 =
      75587764490179772006025726684788 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 83968 128 128
      46023557660398842779830837089850 29564206829780929226194889594938 h0 levelEleven_energy_84096
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 83968 384 =
      101205572126863924122166840672074 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 83968 256 128
      75587764490179772006025726684788 25617807636684152116141113987286 h1 levelEleven_energy_84224
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 83968 512 =
      194908702092859785062270804213989 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 83968 384 128
      101205572126863924122166840672074 93703129965995860940103963541915 h2 levelEleven_energy_84352
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_164 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83968 512 =
      4458775953019233731168594 := by
  have h0 := levelEleven_fractional_83968
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83968 256 =
      2024585434938534384950178 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83968 128 128
      1129784144787998579878309 894801290150535805071869 h0 levelEleven_fractional_84096
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83968 384 =
      2897203027390572232125900 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83968 256 128
      2024585434938534384950178 872617592452037847175722 h1 levelEleven_fractional_84224
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83968 512 =
      4458775953019233731168594 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83968 384 128
      2897203027390572232125900 1561572925628661499042694 h2 levelEleven_fractional_84352
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_164 : ∀ i : Fin 512,
    levelEleven.lookup (83968 + i.val) ≤ levelElevenRoots.lookup (83968 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_83968
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 83968 128 128
    h0 levelEleven_squares_84096
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 83968 256 128
    h1 levelEleven_squares_84224
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 83968 384 128
    h2 levelEleven_squares_84352
  exact h3

end WordCertDensity.Certificates
