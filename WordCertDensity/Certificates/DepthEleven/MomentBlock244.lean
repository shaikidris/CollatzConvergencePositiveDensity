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
theorem levelEleven_energy_124928 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 124928 128 =
      26658750597740929601014119714039 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_124928 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124928 128 =
      838016577755117511196869 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_124928 : ∀ i : Fin 128,
    levelEleven.lookup (124928 + i.val) ≤ levelElevenRoots.lookup (124928 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_125056 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 125056 128 =
      40664169400146959261696081120011 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_125056 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125056 128 =
      1100889180647313314466375 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_125056 : ∀ i : Fin 128,
    levelEleven.lookup (125056 + i.val) ≤ levelElevenRoots.lookup (125056 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_125184 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 125184 128 =
      206287164998056857682266526259297 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_125184 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125184 128 =
      2283168302161239926444437 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_125184 : ∀ i : Fin 128,
    levelEleven.lookup (125184 + i.val) ≤ levelElevenRoots.lookup (125184 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_125312 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 125312 128 =
      35304747748776565321802533112533 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_125312 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125312 128 =
      951594574176281191925444 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_125312 : ∀ i : Fin 128,
    levelEleven.lookup (125312 + i.val) ≤ levelElevenRoots.lookup (125312 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_244 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 124928 512 =
      308914832744721311866779260205880 := by
  have h0 := levelEleven_energy_124928
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 124928 256 =
      67322919997887888862710200834050 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 124928 128 128
      26658750597740929601014119714039 40664169400146959261696081120011 h0 levelEleven_energy_125056
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 124928 384 =
      273610084995944746544976727093347 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 124928 256 128
      67322919997887888862710200834050 206287164998056857682266526259297 h1 levelEleven_energy_125184
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 124928 512 =
      308914832744721311866779260205880 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 124928 384 128
      273610084995944746544976727093347 35304747748776565321802533112533 h2 levelEleven_energy_125312
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_244 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124928 512 =
      5173668634739951944033125 := by
  have h0 := levelEleven_fractional_124928
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124928 256 =
      1938905758402430825663244 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124928 128 128
      838016577755117511196869 1100889180647313314466375 h0 levelEleven_fractional_125056
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124928 384 =
      4222074060563670752107681 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124928 256 128
      1938905758402430825663244 2283168302161239926444437 h1 levelEleven_fractional_125184
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124928 512 =
      5173668634739951944033125 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124928 384 128
      4222074060563670752107681 951594574176281191925444 h2 levelEleven_fractional_125312
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_244 : ∀ i : Fin 512,
    levelEleven.lookup (124928 + i.val) ≤ levelElevenRoots.lookup (124928 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_124928
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 124928 128 128
    h0 levelEleven_squares_125056
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 124928 256 128
    h1 levelEleven_squares_125184
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 124928 384 128
    h2 levelEleven_squares_125312
  exact h3

end WordCertDensity.Certificates
