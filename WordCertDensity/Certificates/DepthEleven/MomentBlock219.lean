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
theorem levelEleven_energy_112128 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 112128 128 =
      33864960133667204165736126576718 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_112128 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112128 128 =
      960095879350532941515614 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_112128 : ∀ i : Fin 128,
    levelEleven.lookup (112128 + i.val) ≤ levelElevenRoots.lookup (112128 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_112256 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 112256 128 =
      41120405704412983052973235285673 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_112256 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112256 128 =
      1012774921325876238860351 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_112256 : ∀ i : Fin 128,
    levelEleven.lookup (112256 + i.val) ≤ levelElevenRoots.lookup (112256 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_112384 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 112384 128 =
      104961778895624874852819101307447 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_112384 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112384 128 =
      1783252815548168008602586 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_112384 : ∀ i : Fin 128,
    levelEleven.lookup (112384 + i.val) ≤ levelElevenRoots.lookup (112384 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_112512 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 112512 128 =
      35119355969179933727346904260201 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_112512 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112512 128 =
      1032091261425090240131235 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_112512 : ∀ i : Fin 128,
    levelEleven.lookup (112512 + i.val) ≤ levelElevenRoots.lookup (112512 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_219 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 112128 512 =
      215066500702884995798875367430039 := by
  have h0 := levelEleven_energy_112128
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 112128 256 =
      74985365838080187218709361862391 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 112128 128 128
      33864960133667204165736126576718 41120405704412983052973235285673 h0 levelEleven_energy_112256
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 112128 384 =
      179947144733705062071528463169838 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 112128 256 128
      74985365838080187218709361862391 104961778895624874852819101307447 h1 levelEleven_energy_112384
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 112128 512 =
      215066500702884995798875367430039 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 112128 384 128
      179947144733705062071528463169838 35119355969179933727346904260201 h2 levelEleven_energy_112512
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_219 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112128 512 =
      4788214877649667429109786 := by
  have h0 := levelEleven_fractional_112128
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112128 256 =
      1972870800676409180375965 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112128 128 128
      960095879350532941515614 1012774921325876238860351 h0 levelEleven_fractional_112256
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112128 384 =
      3756123616224577188978551 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112128 256 128
      1972870800676409180375965 1783252815548168008602586 h1 levelEleven_fractional_112384
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112128 512 =
      4788214877649667429109786 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112128 384 128
      3756123616224577188978551 1032091261425090240131235 h2 levelEleven_fractional_112512
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_219 : ∀ i : Fin 512,
    levelEleven.lookup (112128 + i.val) ≤ levelElevenRoots.lookup (112128 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_112128
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 112128 128 128
    h0 levelEleven_squares_112256
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 112128 256 128
    h1 levelEleven_squares_112384
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 112128 384 128
    h2 levelEleven_squares_112512
  exact h3

end WordCertDensity.Certificates
