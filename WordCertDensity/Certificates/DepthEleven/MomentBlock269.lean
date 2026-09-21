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
theorem levelEleven_energy_137728 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 137728 128 =
      263723364631189008048281477489834 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_137728 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137728 128 =
      2546809978386205766554121 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_137728 : ∀ i : Fin 128,
    levelEleven.lookup (137728 + i.val) ≤ levelElevenRoots.lookup (137728 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_137856 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 137856 128 =
      60993105500392992988707258989207 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_137856 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137856 128 =
      1439588040969599298227770 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_137856 : ∀ i : Fin 128,
    levelEleven.lookup (137856 + i.val) ≤ levelElevenRoots.lookup (137856 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_137984 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 137984 128 =
      39406887669356162408601181664675 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_137984 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137984 128 =
      1110443905785240985643386 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_137984 : ∀ i : Fin 128,
    levelEleven.lookup (137984 + i.val) ≤ levelElevenRoots.lookup (137984 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_138112 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 138112 128 =
      85032422768060491693975171718373 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_138112 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138112 128 =
      1603241193588673788524072 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_138112 : ∀ i : Fin 128,
    levelEleven.lookup (138112 + i.val) ≤ levelElevenRoots.lookup (138112 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_269 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 137728 512 =
      449155780568998655139565089862089 := by
  have h0 := levelEleven_energy_137728
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 137728 256 =
      324716470131582001036988736479041 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 137728 128 128
      263723364631189008048281477489834 60993105500392992988707258989207 h0 levelEleven_energy_137856
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 137728 384 =
      364123357800938163445589918143716 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 137728 256 128
      324716470131582001036988736479041 39406887669356162408601181664675 h1 levelEleven_energy_137984
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 137728 512 =
      449155780568998655139565089862089 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 137728 384 128
      364123357800938163445589918143716 85032422768060491693975171718373 h2 levelEleven_energy_138112
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_269 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137728 512 =
      6700083118729719838949349 := by
  have h0 := levelEleven_fractional_137728
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137728 256 =
      3986398019355805064781891 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137728 128 128
      2546809978386205766554121 1439588040969599298227770 h0 levelEleven_fractional_137856
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137728 384 =
      5096841925141046050425277 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137728 256 128
      3986398019355805064781891 1110443905785240985643386 h1 levelEleven_fractional_137984
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137728 512 =
      6700083118729719838949349 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137728 384 128
      5096841925141046050425277 1603241193588673788524072 h2 levelEleven_fractional_138112
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_269 : ∀ i : Fin 512,
    levelEleven.lookup (137728 + i.val) ≤ levelElevenRoots.lookup (137728 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_137728
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 137728 128 128
    h0 levelEleven_squares_137856
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 137728 256 128
    h1 levelEleven_squares_137984
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 137728 384 128
    h2 levelEleven_squares_138112
  exact h3

end WordCertDensity.Certificates
