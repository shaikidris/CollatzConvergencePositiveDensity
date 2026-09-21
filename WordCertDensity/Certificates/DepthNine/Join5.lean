/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module
public import WordCertDensity.Certificates.DepthNine.Transfer40
public import WordCertDensity.Certificates.DepthNine.Transfer41
public import WordCertDensity.Certificates.DepthNine.Transfer42
public import WordCertDensity.Certificates.DepthNine.Transfer43
public import WordCertDensity.Certificates.DepthNine.Transfer44
public import WordCertDensity.Certificates.DepthNine.Transfer45
public import WordCertDensity.Certificates.DepthNine.Transfer46
public import WordCertDensity.Certificates.DepthNine.Transfer47
/-! # Depth-nine integer certificate component -/

@[expose] public section
namespace WordCertDensity.Certificates
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_40 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 10240 256 = true := by
  have h0 := levelNine_chunk_10240
  have h10256 := Entries.checkRange_append levelNine _ 10240 16 16 h0 levelNine_chunk_10256
  have h10272 := Entries.checkRange_append levelNine _ 10240 32 16 h10256 levelNine_chunk_10272
  have h10288 := Entries.checkRange_append levelNine _ 10240 48 16 h10272 levelNine_chunk_10288
  have h10304 := Entries.checkRange_append levelNine _ 10240 64 16 h10288 levelNine_chunk_10304
  have h10320 := Entries.checkRange_append levelNine _ 10240 80 16 h10304 levelNine_chunk_10320
  have h10336 := Entries.checkRange_append levelNine _ 10240 96 16 h10320 levelNine_chunk_10336
  have h10352 := Entries.checkRange_append levelNine _ 10240 112 16 h10336 levelNine_chunk_10352
  have h10368 := Entries.checkRange_append levelNine _ 10240 128 16 h10352 levelNine_chunk_10368
  have h10384 := Entries.checkRange_append levelNine _ 10240 144 16 h10368 levelNine_chunk_10384
  have h10400 := Entries.checkRange_append levelNine _ 10240 160 16 h10384 levelNine_chunk_10400
  have h10416 := Entries.checkRange_append levelNine _ 10240 176 16 h10400 levelNine_chunk_10416
  have h10432 := Entries.checkRange_append levelNine _ 10240 192 16 h10416 levelNine_chunk_10432
  have h10448 := Entries.checkRange_append levelNine _ 10240 208 16 h10432 levelNine_chunk_10448
  have h10464 := Entries.checkRange_append levelNine _ 10240 224 16 h10448 levelNine_chunk_10464
  have h10480 := Entries.checkRange_append levelNine _ 10240 240 16 h10464 levelNine_chunk_10480
  exact h10480
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_41 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 10496 256 = true := by
  have h0 := levelNine_chunk_10496
  have h10512 := Entries.checkRange_append levelNine _ 10496 16 16 h0 levelNine_chunk_10512
  have h10528 := Entries.checkRange_append levelNine _ 10496 32 16 h10512 levelNine_chunk_10528
  have h10544 := Entries.checkRange_append levelNine _ 10496 48 16 h10528 levelNine_chunk_10544
  have h10560 := Entries.checkRange_append levelNine _ 10496 64 16 h10544 levelNine_chunk_10560
  have h10576 := Entries.checkRange_append levelNine _ 10496 80 16 h10560 levelNine_chunk_10576
  have h10592 := Entries.checkRange_append levelNine _ 10496 96 16 h10576 levelNine_chunk_10592
  have h10608 := Entries.checkRange_append levelNine _ 10496 112 16 h10592 levelNine_chunk_10608
  have h10624 := Entries.checkRange_append levelNine _ 10496 128 16 h10608 levelNine_chunk_10624
  have h10640 := Entries.checkRange_append levelNine _ 10496 144 16 h10624 levelNine_chunk_10640
  have h10656 := Entries.checkRange_append levelNine _ 10496 160 16 h10640 levelNine_chunk_10656
  have h10672 := Entries.checkRange_append levelNine _ 10496 176 16 h10656 levelNine_chunk_10672
  have h10688 := Entries.checkRange_append levelNine _ 10496 192 16 h10672 levelNine_chunk_10688
  have h10704 := Entries.checkRange_append levelNine _ 10496 208 16 h10688 levelNine_chunk_10704
  have h10720 := Entries.checkRange_append levelNine _ 10496 224 16 h10704 levelNine_chunk_10720
  have h10736 := Entries.checkRange_append levelNine _ 10496 240 16 h10720 levelNine_chunk_10736
  exact h10736
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_42 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 10752 256 = true := by
  have h0 := levelNine_chunk_10752
  have h10768 := Entries.checkRange_append levelNine _ 10752 16 16 h0 levelNine_chunk_10768
  have h10784 := Entries.checkRange_append levelNine _ 10752 32 16 h10768 levelNine_chunk_10784
  have h10800 := Entries.checkRange_append levelNine _ 10752 48 16 h10784 levelNine_chunk_10800
  have h10816 := Entries.checkRange_append levelNine _ 10752 64 16 h10800 levelNine_chunk_10816
  have h10832 := Entries.checkRange_append levelNine _ 10752 80 16 h10816 levelNine_chunk_10832
  have h10848 := Entries.checkRange_append levelNine _ 10752 96 16 h10832 levelNine_chunk_10848
  have h10864 := Entries.checkRange_append levelNine _ 10752 112 16 h10848 levelNine_chunk_10864
  have h10880 := Entries.checkRange_append levelNine _ 10752 128 16 h10864 levelNine_chunk_10880
  have h10896 := Entries.checkRange_append levelNine _ 10752 144 16 h10880 levelNine_chunk_10896
  have h10912 := Entries.checkRange_append levelNine _ 10752 160 16 h10896 levelNine_chunk_10912
  have h10928 := Entries.checkRange_append levelNine _ 10752 176 16 h10912 levelNine_chunk_10928
  have h10944 := Entries.checkRange_append levelNine _ 10752 192 16 h10928 levelNine_chunk_10944
  have h10960 := Entries.checkRange_append levelNine _ 10752 208 16 h10944 levelNine_chunk_10960
  have h10976 := Entries.checkRange_append levelNine _ 10752 224 16 h10960 levelNine_chunk_10976
  have h10992 := Entries.checkRange_append levelNine _ 10752 240 16 h10976 levelNine_chunk_10992
  exact h10992
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_43 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 11008 256 = true := by
  have h0 := levelNine_chunk_11008
  have h11024 := Entries.checkRange_append levelNine _ 11008 16 16 h0 levelNine_chunk_11024
  have h11040 := Entries.checkRange_append levelNine _ 11008 32 16 h11024 levelNine_chunk_11040
  have h11056 := Entries.checkRange_append levelNine _ 11008 48 16 h11040 levelNine_chunk_11056
  have h11072 := Entries.checkRange_append levelNine _ 11008 64 16 h11056 levelNine_chunk_11072
  have h11088 := Entries.checkRange_append levelNine _ 11008 80 16 h11072 levelNine_chunk_11088
  have h11104 := Entries.checkRange_append levelNine _ 11008 96 16 h11088 levelNine_chunk_11104
  have h11120 := Entries.checkRange_append levelNine _ 11008 112 16 h11104 levelNine_chunk_11120
  have h11136 := Entries.checkRange_append levelNine _ 11008 128 16 h11120 levelNine_chunk_11136
  have h11152 := Entries.checkRange_append levelNine _ 11008 144 16 h11136 levelNine_chunk_11152
  have h11168 := Entries.checkRange_append levelNine _ 11008 160 16 h11152 levelNine_chunk_11168
  have h11184 := Entries.checkRange_append levelNine _ 11008 176 16 h11168 levelNine_chunk_11184
  have h11200 := Entries.checkRange_append levelNine _ 11008 192 16 h11184 levelNine_chunk_11200
  have h11216 := Entries.checkRange_append levelNine _ 11008 208 16 h11200 levelNine_chunk_11216
  have h11232 := Entries.checkRange_append levelNine _ 11008 224 16 h11216 levelNine_chunk_11232
  have h11248 := Entries.checkRange_append levelNine _ 11008 240 16 h11232 levelNine_chunk_11248
  exact h11248
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_44 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 11264 256 = true := by
  have h0 := levelNine_chunk_11264
  have h11280 := Entries.checkRange_append levelNine _ 11264 16 16 h0 levelNine_chunk_11280
  have h11296 := Entries.checkRange_append levelNine _ 11264 32 16 h11280 levelNine_chunk_11296
  have h11312 := Entries.checkRange_append levelNine _ 11264 48 16 h11296 levelNine_chunk_11312
  have h11328 := Entries.checkRange_append levelNine _ 11264 64 16 h11312 levelNine_chunk_11328
  have h11344 := Entries.checkRange_append levelNine _ 11264 80 16 h11328 levelNine_chunk_11344
  have h11360 := Entries.checkRange_append levelNine _ 11264 96 16 h11344 levelNine_chunk_11360
  have h11376 := Entries.checkRange_append levelNine _ 11264 112 16 h11360 levelNine_chunk_11376
  have h11392 := Entries.checkRange_append levelNine _ 11264 128 16 h11376 levelNine_chunk_11392
  have h11408 := Entries.checkRange_append levelNine _ 11264 144 16 h11392 levelNine_chunk_11408
  have h11424 := Entries.checkRange_append levelNine _ 11264 160 16 h11408 levelNine_chunk_11424
  have h11440 := Entries.checkRange_append levelNine _ 11264 176 16 h11424 levelNine_chunk_11440
  have h11456 := Entries.checkRange_append levelNine _ 11264 192 16 h11440 levelNine_chunk_11456
  have h11472 := Entries.checkRange_append levelNine _ 11264 208 16 h11456 levelNine_chunk_11472
  have h11488 := Entries.checkRange_append levelNine _ 11264 224 16 h11472 levelNine_chunk_11488
  have h11504 := Entries.checkRange_append levelNine _ 11264 240 16 h11488 levelNine_chunk_11504
  exact h11504
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_45 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 11520 256 = true := by
  have h0 := levelNine_chunk_11520
  have h11536 := Entries.checkRange_append levelNine _ 11520 16 16 h0 levelNine_chunk_11536
  have h11552 := Entries.checkRange_append levelNine _ 11520 32 16 h11536 levelNine_chunk_11552
  have h11568 := Entries.checkRange_append levelNine _ 11520 48 16 h11552 levelNine_chunk_11568
  have h11584 := Entries.checkRange_append levelNine _ 11520 64 16 h11568 levelNine_chunk_11584
  have h11600 := Entries.checkRange_append levelNine _ 11520 80 16 h11584 levelNine_chunk_11600
  have h11616 := Entries.checkRange_append levelNine _ 11520 96 16 h11600 levelNine_chunk_11616
  have h11632 := Entries.checkRange_append levelNine _ 11520 112 16 h11616 levelNine_chunk_11632
  have h11648 := Entries.checkRange_append levelNine _ 11520 128 16 h11632 levelNine_chunk_11648
  have h11664 := Entries.checkRange_append levelNine _ 11520 144 16 h11648 levelNine_chunk_11664
  have h11680 := Entries.checkRange_append levelNine _ 11520 160 16 h11664 levelNine_chunk_11680
  have h11696 := Entries.checkRange_append levelNine _ 11520 176 16 h11680 levelNine_chunk_11696
  have h11712 := Entries.checkRange_append levelNine _ 11520 192 16 h11696 levelNine_chunk_11712
  have h11728 := Entries.checkRange_append levelNine _ 11520 208 16 h11712 levelNine_chunk_11728
  have h11744 := Entries.checkRange_append levelNine _ 11520 224 16 h11728 levelNine_chunk_11744
  have h11760 := Entries.checkRange_append levelNine _ 11520 240 16 h11744 levelNine_chunk_11760
  exact h11760
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_46 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 11776 256 = true := by
  have h0 := levelNine_chunk_11776
  have h11792 := Entries.checkRange_append levelNine _ 11776 16 16 h0 levelNine_chunk_11792
  have h11808 := Entries.checkRange_append levelNine _ 11776 32 16 h11792 levelNine_chunk_11808
  have h11824 := Entries.checkRange_append levelNine _ 11776 48 16 h11808 levelNine_chunk_11824
  have h11840 := Entries.checkRange_append levelNine _ 11776 64 16 h11824 levelNine_chunk_11840
  have h11856 := Entries.checkRange_append levelNine _ 11776 80 16 h11840 levelNine_chunk_11856
  have h11872 := Entries.checkRange_append levelNine _ 11776 96 16 h11856 levelNine_chunk_11872
  have h11888 := Entries.checkRange_append levelNine _ 11776 112 16 h11872 levelNine_chunk_11888
  have h11904 := Entries.checkRange_append levelNine _ 11776 128 16 h11888 levelNine_chunk_11904
  have h11920 := Entries.checkRange_append levelNine _ 11776 144 16 h11904 levelNine_chunk_11920
  have h11936 := Entries.checkRange_append levelNine _ 11776 160 16 h11920 levelNine_chunk_11936
  have h11952 := Entries.checkRange_append levelNine _ 11776 176 16 h11936 levelNine_chunk_11952
  have h11968 := Entries.checkRange_append levelNine _ 11776 192 16 h11952 levelNine_chunk_11968
  have h11984 := Entries.checkRange_append levelNine _ 11776 208 16 h11968 levelNine_chunk_11984
  have h12000 := Entries.checkRange_append levelNine _ 11776 224 16 h11984 levelNine_chunk_12000
  have h12016 := Entries.checkRange_append levelNine _ 11776 240 16 h12000 levelNine_chunk_12016
  exact h12016
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_47 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 12032 256 = true := by
  have h0 := levelNine_chunk_12032
  have h12048 := Entries.checkRange_append levelNine _ 12032 16 16 h0 levelNine_chunk_12048
  have h12064 := Entries.checkRange_append levelNine _ 12032 32 16 h12048 levelNine_chunk_12064
  have h12080 := Entries.checkRange_append levelNine _ 12032 48 16 h12064 levelNine_chunk_12080
  have h12096 := Entries.checkRange_append levelNine _ 12032 64 16 h12080 levelNine_chunk_12096
  have h12112 := Entries.checkRange_append levelNine _ 12032 80 16 h12096 levelNine_chunk_12112
  have h12128 := Entries.checkRange_append levelNine _ 12032 96 16 h12112 levelNine_chunk_12128
  have h12144 := Entries.checkRange_append levelNine _ 12032 112 16 h12128 levelNine_chunk_12144
  have h12160 := Entries.checkRange_append levelNine _ 12032 128 16 h12144 levelNine_chunk_12160
  have h12176 := Entries.checkRange_append levelNine _ 12032 144 16 h12160 levelNine_chunk_12176
  have h12192 := Entries.checkRange_append levelNine _ 12032 160 16 h12176 levelNine_chunk_12192
  have h12208 := Entries.checkRange_append levelNine _ 12032 176 16 h12192 levelNine_chunk_12208
  have h12224 := Entries.checkRange_append levelNine _ 12032 192 16 h12208 levelNine_chunk_12224
  have h12240 := Entries.checkRange_append levelNine _ 12032 208 16 h12224 levelNine_chunk_12240
  have h12256 := Entries.checkRange_append levelNine _ 12032 224 16 h12240 levelNine_chunk_12256
  have h12272 := Entries.checkRange_append levelNine _ 12032 240 16 h12256 levelNine_chunk_12272
  exact h12272
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_group_5 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 10240 2048 = true := by
  have h0 := levelNine_block_40
  have h41 := Entries.checkRange_append levelNine _ 10240 256 256 h0 levelNine_block_41
  have h42 := Entries.checkRange_append levelNine _ 10240 512 256 h41 levelNine_block_42
  have h43 := Entries.checkRange_append levelNine _ 10240 768 256 h42 levelNine_block_43
  have h44 := Entries.checkRange_append levelNine _ 10240 1024 256 h43 levelNine_block_44
  have h45 := Entries.checkRange_append levelNine _ 10240 1280 256 h44 levelNine_block_45
  have h46 := Entries.checkRange_append levelNine _ 10240 1536 256 h45 levelNine_block_46
  have h47 := Entries.checkRange_append levelNine _ 10240 1792 256 h46 levelNine_block_47
  exact h47
end WordCertDensity.Certificates
