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
theorem levelEleven_energy_142336 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 142336 128 =
      73253575665565855294912628705418 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_142336 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142336 128 =
      1349888596775602297083924 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_142336 : ∀ i : Fin 128,
    levelEleven.lookup (142336 + i.val) ≤ levelElevenRoots.lookup (142336 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_142464 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 142464 128 =
      207006973521780757564566932716160 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_142464 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142464 128 =
      2366970365542990361894301 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_142464 : ∀ i : Fin 128,
    levelEleven.lookup (142464 + i.val) ≤ levelElevenRoots.lookup (142464 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_142592 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 142592 128 =
      28828383563824426191769481340486 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_142592 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142592 128 =
      882682628199643757805218 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_142592 : ∀ i : Fin 128,
    levelEleven.lookup (142592 + i.val) ≤ levelElevenRoots.lookup (142592 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_142720 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 142720 128 =
      34159560542549247050098470455230 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_142720 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142720 128 =
      982152531559251671891145 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_142720 : ∀ i : Fin 128,
    levelEleven.lookup (142720 + i.val) ≤ levelElevenRoots.lookup (142720 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_278 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 142336 512 =
      343248493293720286101347513217294 := by
  have h0 := levelEleven_energy_142336
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 142336 256 =
      280260549187346612859479561421578 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 142336 128 128
      73253575665565855294912628705418 207006973521780757564566932716160 h0 levelEleven_energy_142464
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 142336 384 =
      309088932751171039051249042762064 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 142336 256 128
      280260549187346612859479561421578 28828383563824426191769481340486 h1 levelEleven_energy_142592
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 142336 512 =
      343248493293720286101347513217294 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 142336 384 128
      309088932751171039051249042762064 34159560542549247050098470455230 h2 levelEleven_energy_142720
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_278 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142336 512 =
      5581694122077488088674588 := by
  have h0 := levelEleven_fractional_142336
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142336 256 =
      3716858962318592658978225 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142336 128 128
      1349888596775602297083924 2366970365542990361894301 h0 levelEleven_fractional_142464
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142336 384 =
      4599541590518236416783443 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142336 256 128
      3716858962318592658978225 882682628199643757805218 h1 levelEleven_fractional_142592
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142336 512 =
      5581694122077488088674588 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142336 384 128
      4599541590518236416783443 982152531559251671891145 h2 levelEleven_fractional_142720
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_278 : ∀ i : Fin 512,
    levelEleven.lookup (142336 + i.val) ≤ levelElevenRoots.lookup (142336 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_142336
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 142336 128 128
    h0 levelEleven_squares_142464
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 142336 256 128
    h1 levelEleven_squares_142592
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 142336 384 128
    h2 levelEleven_squares_142720
  exact h3

end WordCertDensity.Certificates
