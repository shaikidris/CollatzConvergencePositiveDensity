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
theorem levelEleven_energy_171008 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 171008 128 =
      26075931093863953920734742317727 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_171008 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171008 128 =
      839830732367257854948222 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_171008 : ∀ i : Fin 128,
    levelEleven.lookup (171008 + i.val) ≤ levelElevenRoots.lookup (171008 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_171136 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 171136 128 =
      59681175892123015579970478807431 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_171136 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171136 128 =
      1385971429459426104775028 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_171136 : ∀ i : Fin 128,
    levelEleven.lookup (171136 + i.val) ≤ levelElevenRoots.lookup (171136 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_171264 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 171264 128 =
      28029304089333345800169305931034 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_171264 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171264 128 =
      807837737168271108795092 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_171264 : ∀ i : Fin 128,
    levelEleven.lookup (171264 + i.val) ≤ levelElevenRoots.lookup (171264 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_171392 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 171392 128 =
      61827886921727230809885865063180 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_171392 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171392 128 =
      1364037662309150503391611 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_171392 : ∀ i : Fin 128,
    levelEleven.lookup (171392 + i.val) ≤ levelElevenRoots.lookup (171392 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_334 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 171008 512 =
      175614297997047546110760392119372 := by
  have h0 := levelEleven_energy_171008
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 171008 256 =
      85757106985986969500705221125158 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 171008 128 128
      26075931093863953920734742317727 59681175892123015579970478807431 h0 levelEleven_energy_171136
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 171008 384 =
      113786411075320315300874527056192 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 171008 256 128
      85757106985986969500705221125158 28029304089333345800169305931034 h1 levelEleven_energy_171264
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 171008 512 =
      175614297997047546110760392119372 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 171008 384 128
      113786411075320315300874527056192 61827886921727230809885865063180 h2 levelEleven_energy_171392
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_334 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171008 512 =
      4397677561304105571909953 := by
  have h0 := levelEleven_fractional_171008
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171008 256 =
      2225802161826683959723250 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171008 128 128
      839830732367257854948222 1385971429459426104775028 h0 levelEleven_fractional_171136
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171008 384 =
      3033639898994955068518342 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171008 256 128
      2225802161826683959723250 807837737168271108795092 h1 levelEleven_fractional_171264
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171008 512 =
      4397677561304105571909953 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171008 384 128
      3033639898994955068518342 1364037662309150503391611 h2 levelEleven_fractional_171392
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_334 : ∀ i : Fin 512,
    levelEleven.lookup (171008 + i.val) ≤ levelElevenRoots.lookup (171008 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_171008
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 171008 128 128
    h0 levelEleven_squares_171136
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 171008 256 128
    h1 levelEleven_squares_171264
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 171008 384 128
    h2 levelEleven_squares_171392
  exact h3

end WordCertDensity.Certificates
