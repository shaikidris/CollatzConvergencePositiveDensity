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
theorem levelEleven_energy_68096 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 68096 128 =
      38099303466645615727457602994448 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_68096 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68096 128 =
      1090714735035713018879014 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_68096 : ∀ i : Fin 128,
    levelEleven.lookup (68096 + i.val) ≤ levelElevenRoots.lookup (68096 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_68224 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 68224 128 =
      77763284338446742133203785430480 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_68224 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68224 128 =
      1309865768549293517181317 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_68224 : ∀ i : Fin 128,
    levelEleven.lookup (68224 + i.val) ≤ levelElevenRoots.lookup (68224 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_68352 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 68352 128 =
      28032226468624290297455511552529 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_68352 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68352 128 =
      870013494663761176477871 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_68352 : ∀ i : Fin 128,
    levelEleven.lookup (68352 + i.val) ≤ levelElevenRoots.lookup (68352 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_68480 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 68480 128 =
      23319612078263516426581360675259 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_68480 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68480 128 =
      751530623488004128507134 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_68480 : ∀ i : Fin 128,
    levelEleven.lookup (68480 + i.val) ≤ levelElevenRoots.lookup (68480 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_133 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 68096 512 =
      167214426351980164584698260652716 := by
  have h0 := levelEleven_energy_68096
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 68096 256 =
      115862587805092357860661388424928 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 68096 128 128
      38099303466645615727457602994448 77763284338446742133203785430480 h0 levelEleven_energy_68224
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 68096 384 =
      143894814273716648158116899977457 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 68096 256 128
      115862587805092357860661388424928 28032226468624290297455511552529 h1 levelEleven_energy_68352
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 68096 512 =
      167214426351980164584698260652716 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 68096 384 128
      143894814273716648158116899977457 23319612078263516426581360675259 h2 levelEleven_energy_68480
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_133 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68096 512 =
      4022124621736771841045336 := by
  have h0 := levelEleven_fractional_68096
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68096 256 =
      2400580503585006536060331 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68096 128 128
      1090714735035713018879014 1309865768549293517181317 h0 levelEleven_fractional_68224
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68096 384 =
      3270593998248767712538202 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68096 256 128
      2400580503585006536060331 870013494663761176477871 h1 levelEleven_fractional_68352
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68096 512 =
      4022124621736771841045336 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68096 384 128
      3270593998248767712538202 751530623488004128507134 h2 levelEleven_fractional_68480
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_133 : ∀ i : Fin 512,
    levelEleven.lookup (68096 + i.val) ≤ levelElevenRoots.lookup (68096 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_68096
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 68096 128 128
    h0 levelEleven_squares_68224
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 68096 256 128
    h1 levelEleven_squares_68352
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 68096 384 128
    h2 levelEleven_squares_68480
  exact h3

end WordCertDensity.Certificates
