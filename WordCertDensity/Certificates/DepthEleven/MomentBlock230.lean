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
theorem levelEleven_energy_117760 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 117760 128 =
      37171868630054522711112402224882 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_117760 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117760 128 =
      1024867952686988818336303 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_117760 : ∀ i : Fin 128,
    levelEleven.lookup (117760 + i.val) ≤ levelElevenRoots.lookup (117760 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_117888 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 117888 128 =
      50872548061026220585726073380202 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_117888 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117888 128 =
      1141582070696216639960940 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_117888 : ∀ i : Fin 128,
    levelEleven.lookup (117888 + i.val) ≤ levelElevenRoots.lookup (117888 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_118016 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 118016 128 =
      757192496939157960005503048373842 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_118016 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118016 128 =
      5612522535512091342935457 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_118016 : ∀ i : Fin 128,
    levelEleven.lookup (118016 + i.val) ≤ levelElevenRoots.lookup (118016 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_118144 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 118144 128 =
      47380834338529323546727949418911 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_118144 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118144 128 =
      1170027268076038192387427 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_118144 : ∀ i : Fin 128,
    levelEleven.lookup (118144 + i.val) ≤ levelElevenRoots.lookup (118144 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_230 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 117760 512 =
      892617747968768026849069473397837 := by
  have h0 := levelEleven_energy_117760
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 117760 256 =
      88044416691080743296838475605084 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 117760 128 128
      37171868630054522711112402224882 50872548061026220585726073380202 h0 levelEleven_energy_117888
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 117760 384 =
      845236913630238703302341523978926 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 117760 256 128
      88044416691080743296838475605084 757192496939157960005503048373842 h1 levelEleven_energy_118016
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 117760 512 =
      892617747968768026849069473397837 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 117760 384 128
      845236913630238703302341523978926 47380834338529323546727949418911 h2 levelEleven_energy_118144
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_230 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117760 512 =
      8948999826971334993620127 := by
  have h0 := levelEleven_fractional_117760
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117760 256 =
      2166450023383205458297243 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117760 128 128
      1024867952686988818336303 1141582070696216639960940 h0 levelEleven_fractional_117888
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117760 384 =
      7778972558895296801232700 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117760 256 128
      2166450023383205458297243 5612522535512091342935457 h1 levelEleven_fractional_118016
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117760 512 =
      8948999826971334993620127 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117760 384 128
      7778972558895296801232700 1170027268076038192387427 h2 levelEleven_fractional_118144
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_230 : ∀ i : Fin 512,
    levelEleven.lookup (117760 + i.val) ≤ levelElevenRoots.lookup (117760 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_117760
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 117760 128 128
    h0 levelEleven_squares_117888
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 117760 256 128
    h1 levelEleven_squares_118016
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 117760 384 128
    h2 levelEleven_squares_118144
  exact h3

end WordCertDensity.Certificates
