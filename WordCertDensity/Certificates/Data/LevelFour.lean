/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.Data.LevelThree

/-! # Complete depth-four integer certificate -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Complete depth-four enclosure tree. -/
def levelFour : Entries :=
  (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 303983353523559)) (.leaf 151991677168583)) (.node (.node (.leaf 75995838584292) (.leaf 2045911758830089)) (.leaf 0))) (.node (.node (.node (.leaf 413375198840314) (.leaf 0)) (.leaf 1022955879415045)) (.node (.leaf 0) (.leaf 826926087393275)))) (.node (.node (.node (.node (.leaf 206687599420157) (.leaf 81580520354492)) (.leaf 0)) (.node (.leaf 1524065977133239) (.leaf 40883589179640))) (.node (.node (.node (.leaf 0) (.leaf 767073551246485)) (.leaf 889410858144951)) (.node (.leaf 413463043696638) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 522207788600920) (.leaf 0)) (.leaf 40790260177246)) (.node (.leaf 0) (.leaf 113257134724485))) (.node (.node (.node (.leaf 762032988566620) (.leaf 870985548000720)) (.leaf 0)) (.node (.leaf 1520385388710645) (.leaf 96710060979524)))) (.node (.node (.node (.node (.leaf 0) (.leaf 108873193648453)) (.leaf 453028537954892)) (.node (.leaf 444705429072476) (.leaf 0))) (.node (.node (.node (.leaf 206731522303662) (.leaf 0)) (.leaf 163534356124746)) (.node (.leaf 0) (.leaf 304686118831532)))))) (.node (.node (.node (.node (.node (.node (.leaf 261103894300460) (.leaf 331770946732230)) (.leaf 0)) (.node (.leaf 576329228286467) (.leaf 288164614143234))) (.node (.node (.node (.leaf 0) (.leaf 165885473366115)) (.leaf 130551947578054)) (.node (.leaf 56628567362243) (.leaf 0)))) (.node (.node (.node (.node (.leaf 381016494657309) (.leaf 0)) (.leaf 435492774000360)) (.node (.leaf 0) (.leaf 484055003013227))) (.node (.node (.node (.leaf 760192694355323) (.leaf 82942737101526)) (.leaf 0)) (.node (.leaf 326322079629397) (.leaf 65275973789027))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 242027501506614)) (.leaf 193420121959047)) (.node (.leaf 226514268977446) (.leaf 0))) (.node (.node (.node (.leaf 327068712249492) (.leaf 0)) (.leaf 190508247328655)) (.node (.leaf 0) (.leaf 217746387296905)))) (.node (.node (.node (.node (.leaf 103365761151831) (.leaf 1534147102492969)) (.leaf 0)) (.node (.leaf 81767178359280) (.leaf 163161039814699))) (.node (.node (.node (.leaf 0) (.leaf 41471368550763)) (.leaf 607966707047117)) (.node (.leaf 152343059415766) (.leaf 0)))))))

/-- Complete depth-four enclosure tree. -/
def levelFourRoots : Entries :=
  (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 17435119)) (.leaf 12328491)) (.node (.node (.leaf 8717560) (.leaf 45231757)) (.leaf 0))) (.node (.node (.node (.leaf 20331631) (.leaf 0)) (.leaf 31983682)) (.node (.leaf 0) (.leaf 28756323)))) (.node (.node (.node (.node (.leaf 14376634) (.leaf 9032194)) (.leaf 0)) (.node (.leaf 39039288) (.leaf 6394028))) (.node (.node (.node (.leaf 0) (.leaf 27696093)) (.leaf 29822993)) (.node (.leaf 20333791) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 22851867) (.leaf 0)) (.leaf 6386726)) (.node (.leaf 0) (.leaf 10642234))) (.node (.node (.node (.leaf 27604946) (.leaf 29512465)) (.leaf 0)) (.node (.leaf 38992120) (.leaf 9834128)))) (.node (.node (.node (.node (.leaf 0) (.leaf 10434232)) (.leaf 21284468)) (.node (.leaf 21088040) (.leaf 0))) (.node (.node (.node (.leaf 14378162) (.leaf 0)) (.leaf 12788056)) (.node (.leaf 0) (.leaf 17455261)))))) (.node (.node (.node (.node (.node (.node (.leaf 16158710) (.leaf 18214581)) (.leaf 0)) (.node (.leaf 24006858) (.leaf 16975413))) (.node (.node (.node (.leaf 0) (.leaf 12879654)) (.leaf 11425934)) (.node (.leaf 7525196) (.leaf 0)))) (.node (.node (.node (.node (.leaf 19519644) (.leaf 0)) (.leaf 20868464)) (.node (.leaf 0) (.leaf 22001251))) (.node (.node (.node (.leaf 27571593) (.leaf 9107291)) (.leaf 0)) (.node (.leaf 18064388) (.leaf 8079355))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 15557234)) (.leaf 13907557)) (.node (.leaf 15050391) (.leaf 0))) (.node (.node (.node (.leaf 18085042) (.leaf 0)) (.leaf 13802473)) (.node (.leaf 0) (.leaf 14756233)))) (.node (.node (.node (.node (.leaf 10166896) (.leaf 39168190)) (.leaf 0)) (.node (.leaf 9042521) (.leaf 12773451))) (.node (.node (.node (.leaf 0) (.leaf 6439827)) (.leaf 24656981)) (.node (.leaf 12342734) (.leaf 0)))))))

/-- Every stored output agrees with the exact direct evaluator. -/
theorem levelFour_transfer :
    levelFour.checkRange (levelThree.directEntry 1350117382722123 4 16) 0 81 = true := by
  decide +kernel

/-- The integer cap covers all residues. -/
theorem levelFour_cap : levelFour.allLE 2045911758830089 = true := by decide +kernel

/-- Scaled maximum comparison. -/
theorem levelFour_max_comparison : 10 * 2045911758830089 ≤ 73 * 2 ^ 48 := by
  decide +kernel

/-- Complete integer energy comparison. -/
theorem levelFour_energy_comparison :
    1000 * ((List.range 81).map (fun i => levelFour.lookup i ^ 2)).sum ≤
      3069 * 81 * (2 ^ 48) ^ 2 := by decide +kernel

/-- Square enclosures include every residue. -/
theorem levelFour_square_enclosures : ∀ i : Fin 81,
    levelFour.lookup i.val ≤ levelFourRoots.lookup i.val ^ 2 := by decide +kernel

/-- Complete fractional numerator comparison. -/
theorem levelFour_fractional_comparison :
    20000 * ((List.range 81).map
      (fun i => levelFour.lookup i * levelFourRoots.lookup i)).sum ≤
        32779 * 81 * 2 ^ 72 := by decide +kernel

end WordCertDensity.Certificates
