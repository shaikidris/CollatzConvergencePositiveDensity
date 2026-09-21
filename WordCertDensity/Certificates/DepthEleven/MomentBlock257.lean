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
theorem levelEleven_energy_131584 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 131584 128 =
      46005401147438845397334395843615 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_131584 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131584 128 =
      1190467028059306819188224 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_131584 : ∀ i : Fin 128,
    levelEleven.lookup (131584 + i.val) ≤ levelElevenRoots.lookup (131584 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_131712 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 131712 128 =
      29012269898421198913560320025169 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_131712 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131712 128 =
      867327508317982604096922 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_131712 : ∀ i : Fin 128,
    levelEleven.lookup (131712 + i.val) ≤ levelElevenRoots.lookup (131712 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_131840 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 131840 128 =
      87746015152562855147406182847874 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_131840 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131840 128 =
      1519019503819515123618896 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_131840 : ∀ i : Fin 128,
    levelEleven.lookup (131840 + i.val) ≤ levelElevenRoots.lookup (131840 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_131968 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 131968 128 =
      36459280796791095726804345324710 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_131968 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131968 128 =
      933676430255937214115800 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_131968 : ∀ i : Fin 128,
    levelEleven.lookup (131968 + i.val) ≤ levelElevenRoots.lookup (131968 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_257 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 131584 512 =
      199222966995213995185105244041368 := by
  have h0 := levelEleven_energy_131584
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 131584 256 =
      75017671045860044310894715868784 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 131584 128 128
      46005401147438845397334395843615 29012269898421198913560320025169 h0 levelEleven_energy_131712
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 131584 384 =
      162763686198422899458300898716658 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 131584 256 128
      75017671045860044310894715868784 87746015152562855147406182847874 h1 levelEleven_energy_131840
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 131584 512 =
      199222966995213995185105244041368 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 131584 384 128
      162763686198422899458300898716658 36459280796791095726804345324710 h2 levelEleven_energy_131968
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_257 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131584 512 =
      4510490470452741761019842 := by
  have h0 := levelEleven_fractional_131584
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131584 256 =
      2057794536377289423285146 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131584 128 128
      1190467028059306819188224 867327508317982604096922 h0 levelEleven_fractional_131712
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131584 384 =
      3576814040196804546904042 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131584 256 128
      2057794536377289423285146 1519019503819515123618896 h1 levelEleven_fractional_131840
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131584 512 =
      4510490470452741761019842 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131584 384 128
      3576814040196804546904042 933676430255937214115800 h2 levelEleven_fractional_131968
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_257 : ∀ i : Fin 512,
    levelEleven.lookup (131584 + i.val) ≤ levelElevenRoots.lookup (131584 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_131584
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 131584 128 128
    h0 levelEleven_squares_131712
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 131584 256 128
    h1 levelEleven_squares_131840
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 131584 384 128
    h2 levelEleven_squares_131968
  exact h3

end WordCertDensity.Certificates
