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
theorem levelEleven_energy_51712 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 51712 128 =
      29060200184665043384318463412516 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_51712 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51712 128 =
      860407484162622149045253 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_51712 : ∀ i : Fin 128,
    levelEleven.lookup (51712 + i.val) ≤ levelElevenRoots.lookup (51712 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_51840 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 51840 128 =
      42460723119966980047205588609894 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_51840 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51840 128 =
      1117733967200581945681843 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_51840 : ∀ i : Fin 128,
    levelEleven.lookup (51840 + i.val) ≤ levelElevenRoots.lookup (51840 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_51968 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 51968 128 =
      34810240343066560114660307858189 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_51968 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51968 128 =
      929664531709002549390814 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_51968 : ∀ i : Fin 128,
    levelEleven.lookup (51968 + i.val) ≤ levelElevenRoots.lookup (51968 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_52096 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 52096 128 =
      40199466309530007062650532372692 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_52096 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52096 128 =
      1142092042438674368027858 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_52096 : ∀ i : Fin 128,
    levelEleven.lookup (52096 + i.val) ≤ levelElevenRoots.lookup (52096 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_101 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 51712 512 =
      146530629957228590608834892253291 := by
  have h0 := levelEleven_energy_51712
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 51712 256 =
      71520923304632023431524052022410 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 51712 128 128
      29060200184665043384318463412516 42460723119966980047205588609894 h0 levelEleven_energy_51840
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 51712 384 =
      106331163647698583546184359880599 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 51712 256 128
      71520923304632023431524052022410 34810240343066560114660307858189 h1 levelEleven_energy_51968
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 51712 512 =
      146530629957228590608834892253291 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 51712 384 128
      106331163647698583546184359880599 40199466309530007062650532372692 h2 levelEleven_energy_52096
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_101 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51712 512 =
      4049898025510881012145768 := by
  have h0 := levelEleven_fractional_51712
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51712 256 =
      1978141451363204094727096 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51712 128 128
      860407484162622149045253 1117733967200581945681843 h0 levelEleven_fractional_51840
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51712 384 =
      2907805983072206644117910 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51712 256 128
      1978141451363204094727096 929664531709002549390814 h1 levelEleven_fractional_51968
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51712 512 =
      4049898025510881012145768 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51712 384 128
      2907805983072206644117910 1142092042438674368027858 h2 levelEleven_fractional_52096
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_101 : ∀ i : Fin 512,
    levelEleven.lookup (51712 + i.val) ≤ levelElevenRoots.lookup (51712 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_51712
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 51712 128 128
    h0 levelEleven_squares_51840
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 51712 256 128
    h1 levelEleven_squares_51968
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 51712 384 128
    h2 levelEleven_squares_52096
  exact h3

end WordCertDensity.Certificates
