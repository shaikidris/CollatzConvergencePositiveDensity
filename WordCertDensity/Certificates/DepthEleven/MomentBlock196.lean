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
theorem levelEleven_energy_100352 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 100352 128 =
      35794711749178043620620258224970 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_100352 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100352 128 =
      938210087316354056944706 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_100352 : ∀ i : Fin 128,
    levelEleven.lookup (100352 + i.val) ≤ levelElevenRoots.lookup (100352 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_100480 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 100480 128 =
      75476396869840132994743049238625 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_100480 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100480 128 =
      1613189352609067941592212 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_100480 : ∀ i : Fin 128,
    levelEleven.lookup (100480 + i.val) ≤ levelElevenRoots.lookup (100480 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_100608 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 100608 128 =
      23062288339440532200840473349059 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_100608 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100608 128 =
      692907124052923931608144 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_100608 : ∀ i : Fin 128,
    levelEleven.lookup (100608 + i.val) ≤ levelElevenRoots.lookup (100608 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_100736 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 100736 128 =
      71892318079056645154001229127697 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_100736 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100736 128 =
      1528853028956492350459394 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_100736 : ∀ i : Fin 128,
    levelEleven.lookup (100736 + i.val) ≤ levelElevenRoots.lookup (100736 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_196 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 100352 512 =
      206225715037515353970205009940351 := by
  have h0 := levelEleven_energy_100352
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 100352 256 =
      111271108619018176615363307463595 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 100352 128 128
      35794711749178043620620258224970 75476396869840132994743049238625 h0 levelEleven_energy_100480
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 100352 384 =
      134333396958458708816203780812654 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 100352 256 128
      111271108619018176615363307463595 23062288339440532200840473349059 h1 levelEleven_energy_100608
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 100352 512 =
      206225715037515353970205009940351 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 100352 384 128
      134333396958458708816203780812654 71892318079056645154001229127697 h2 levelEleven_energy_100736
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_196 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100352 512 =
      4773159592934838280604456 := by
  have h0 := levelEleven_fractional_100352
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100352 256 =
      2551399439925421998536918 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100352 128 128
      938210087316354056944706 1613189352609067941592212 h0 levelEleven_fractional_100480
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100352 384 =
      3244306563978345930145062 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100352 256 128
      2551399439925421998536918 692907124052923931608144 h1 levelEleven_fractional_100608
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100352 512 =
      4773159592934838280604456 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100352 384 128
      3244306563978345930145062 1528853028956492350459394 h2 levelEleven_fractional_100736
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_196 : ∀ i : Fin 512,
    levelEleven.lookup (100352 + i.val) ≤ levelElevenRoots.lookup (100352 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_100352
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 100352 128 128
    h0 levelEleven_squares_100480
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 100352 256 128
    h1 levelEleven_squares_100608
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 100352 384 128
    h2 levelEleven_squares_100736
  exact h3

end WordCertDensity.Certificates
