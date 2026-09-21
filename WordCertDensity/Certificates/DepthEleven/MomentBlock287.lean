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
theorem levelEleven_energy_146944 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 146944 128 =
      84239788688606421570334104742558 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_146944 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146944 128 =
      1481487923687904663659786 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_146944 : ∀ i : Fin 128,
    levelEleven.lookup (146944 + i.val) ≤ levelElevenRoots.lookup (146944 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_147072 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 147072 128 =
      27146372676441145904507185279061 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_147072 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147072 128 =
      863381550533724053110674 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_147072 : ∀ i : Fin 128,
    levelEleven.lookup (147072 + i.val) ≤ levelElevenRoots.lookup (147072 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_147200 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 147200 128 =
      38436024869820365324463274323036 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_147200 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147200 128 =
      961476377544184952391830 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_147200 : ∀ i : Fin 128,
    levelEleven.lookup (147200 + i.val) ≤ levelElevenRoots.lookup (147200 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_147328 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 147328 128 =
      72637436799653476314714032593652 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_147328 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147328 128 =
      1420874742872915214155038 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_147328 : ∀ i : Fin 128,
    levelEleven.lookup (147328 + i.val) ≤ levelElevenRoots.lookup (147328 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_287 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 146944 512 =
      222459623034521409114018596938307 := by
  have h0 := levelEleven_energy_146944
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 146944 256 =
      111386161365047567474841290021619 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 146944 128 128
      84239788688606421570334104742558 27146372676441145904507185279061 h0 levelEleven_energy_147072
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 146944 384 =
      149822186234867932799304564344655 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 146944 256 128
      111386161365047567474841290021619 38436024869820365324463274323036 h1 levelEleven_energy_147200
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 146944 512 =
      222459623034521409114018596938307 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 146944 384 128
      149822186234867932799304564344655 72637436799653476314714032593652 h2 levelEleven_energy_147328
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_287 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146944 512 =
      4727220594638728883317328 := by
  have h0 := levelEleven_fractional_146944
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146944 256 =
      2344869474221628716770460 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146944 128 128
      1481487923687904663659786 863381550533724053110674 h0 levelEleven_fractional_147072
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146944 384 =
      3306345851765813669162290 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146944 256 128
      2344869474221628716770460 961476377544184952391830 h1 levelEleven_fractional_147200
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146944 512 =
      4727220594638728883317328 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146944 384 128
      3306345851765813669162290 1420874742872915214155038 h2 levelEleven_fractional_147328
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_287 : ∀ i : Fin 512,
    levelEleven.lookup (146944 + i.val) ≤ levelElevenRoots.lookup (146944 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_146944
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 146944 128 128
    h0 levelEleven_squares_147072
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 146944 256 128
    h1 levelEleven_squares_147200
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 146944 384 128
    h2 levelEleven_squares_147328
  exact h3

end WordCertDensity.Certificates
