/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module
public import WordCertDensity.Certificates.DepthNine.Transfer24
public import WordCertDensity.Certificates.DepthNine.Transfer25
public import WordCertDensity.Certificates.DepthNine.Transfer26
public import WordCertDensity.Certificates.DepthNine.Transfer27
public import WordCertDensity.Certificates.DepthNine.Transfer28
public import WordCertDensity.Certificates.DepthNine.Transfer29
public import WordCertDensity.Certificates.DepthNine.Transfer30
public import WordCertDensity.Certificates.DepthNine.Transfer31
/-! # Depth-nine integer certificate component -/

@[expose] public section
namespace WordCertDensity.Certificates
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_24 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 6144 256 = true := by
  have h0 := levelNine_chunk_6144
  have h6160 := Entries.checkRange_append levelNine _ 6144 16 16 h0 levelNine_chunk_6160
  have h6176 := Entries.checkRange_append levelNine _ 6144 32 16 h6160 levelNine_chunk_6176
  have h6192 := Entries.checkRange_append levelNine _ 6144 48 16 h6176 levelNine_chunk_6192
  have h6208 := Entries.checkRange_append levelNine _ 6144 64 16 h6192 levelNine_chunk_6208
  have h6224 := Entries.checkRange_append levelNine _ 6144 80 16 h6208 levelNine_chunk_6224
  have h6240 := Entries.checkRange_append levelNine _ 6144 96 16 h6224 levelNine_chunk_6240
  have h6256 := Entries.checkRange_append levelNine _ 6144 112 16 h6240 levelNine_chunk_6256
  have h6272 := Entries.checkRange_append levelNine _ 6144 128 16 h6256 levelNine_chunk_6272
  have h6288 := Entries.checkRange_append levelNine _ 6144 144 16 h6272 levelNine_chunk_6288
  have h6304 := Entries.checkRange_append levelNine _ 6144 160 16 h6288 levelNine_chunk_6304
  have h6320 := Entries.checkRange_append levelNine _ 6144 176 16 h6304 levelNine_chunk_6320
  have h6336 := Entries.checkRange_append levelNine _ 6144 192 16 h6320 levelNine_chunk_6336
  have h6352 := Entries.checkRange_append levelNine _ 6144 208 16 h6336 levelNine_chunk_6352
  have h6368 := Entries.checkRange_append levelNine _ 6144 224 16 h6352 levelNine_chunk_6368
  have h6384 := Entries.checkRange_append levelNine _ 6144 240 16 h6368 levelNine_chunk_6384
  exact h6384
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_25 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 6400 256 = true := by
  have h0 := levelNine_chunk_6400
  have h6416 := Entries.checkRange_append levelNine _ 6400 16 16 h0 levelNine_chunk_6416
  have h6432 := Entries.checkRange_append levelNine _ 6400 32 16 h6416 levelNine_chunk_6432
  have h6448 := Entries.checkRange_append levelNine _ 6400 48 16 h6432 levelNine_chunk_6448
  have h6464 := Entries.checkRange_append levelNine _ 6400 64 16 h6448 levelNine_chunk_6464
  have h6480 := Entries.checkRange_append levelNine _ 6400 80 16 h6464 levelNine_chunk_6480
  have h6496 := Entries.checkRange_append levelNine _ 6400 96 16 h6480 levelNine_chunk_6496
  have h6512 := Entries.checkRange_append levelNine _ 6400 112 16 h6496 levelNine_chunk_6512
  have h6528 := Entries.checkRange_append levelNine _ 6400 128 16 h6512 levelNine_chunk_6528
  have h6544 := Entries.checkRange_append levelNine _ 6400 144 16 h6528 levelNine_chunk_6544
  have h6560 := Entries.checkRange_append levelNine _ 6400 160 16 h6544 levelNine_chunk_6560
  have h6576 := Entries.checkRange_append levelNine _ 6400 176 16 h6560 levelNine_chunk_6576
  have h6592 := Entries.checkRange_append levelNine _ 6400 192 16 h6576 levelNine_chunk_6592
  have h6608 := Entries.checkRange_append levelNine _ 6400 208 16 h6592 levelNine_chunk_6608
  have h6624 := Entries.checkRange_append levelNine _ 6400 224 16 h6608 levelNine_chunk_6624
  have h6640 := Entries.checkRange_append levelNine _ 6400 240 16 h6624 levelNine_chunk_6640
  exact h6640
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_26 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 6656 256 = true := by
  have h0 := levelNine_chunk_6656
  have h6672 := Entries.checkRange_append levelNine _ 6656 16 16 h0 levelNine_chunk_6672
  have h6688 := Entries.checkRange_append levelNine _ 6656 32 16 h6672 levelNine_chunk_6688
  have h6704 := Entries.checkRange_append levelNine _ 6656 48 16 h6688 levelNine_chunk_6704
  have h6720 := Entries.checkRange_append levelNine _ 6656 64 16 h6704 levelNine_chunk_6720
  have h6736 := Entries.checkRange_append levelNine _ 6656 80 16 h6720 levelNine_chunk_6736
  have h6752 := Entries.checkRange_append levelNine _ 6656 96 16 h6736 levelNine_chunk_6752
  have h6768 := Entries.checkRange_append levelNine _ 6656 112 16 h6752 levelNine_chunk_6768
  have h6784 := Entries.checkRange_append levelNine _ 6656 128 16 h6768 levelNine_chunk_6784
  have h6800 := Entries.checkRange_append levelNine _ 6656 144 16 h6784 levelNine_chunk_6800
  have h6816 := Entries.checkRange_append levelNine _ 6656 160 16 h6800 levelNine_chunk_6816
  have h6832 := Entries.checkRange_append levelNine _ 6656 176 16 h6816 levelNine_chunk_6832
  have h6848 := Entries.checkRange_append levelNine _ 6656 192 16 h6832 levelNine_chunk_6848
  have h6864 := Entries.checkRange_append levelNine _ 6656 208 16 h6848 levelNine_chunk_6864
  have h6880 := Entries.checkRange_append levelNine _ 6656 224 16 h6864 levelNine_chunk_6880
  have h6896 := Entries.checkRange_append levelNine _ 6656 240 16 h6880 levelNine_chunk_6896
  exact h6896
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_27 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 6912 256 = true := by
  have h0 := levelNine_chunk_6912
  have h6928 := Entries.checkRange_append levelNine _ 6912 16 16 h0 levelNine_chunk_6928
  have h6944 := Entries.checkRange_append levelNine _ 6912 32 16 h6928 levelNine_chunk_6944
  have h6960 := Entries.checkRange_append levelNine _ 6912 48 16 h6944 levelNine_chunk_6960
  have h6976 := Entries.checkRange_append levelNine _ 6912 64 16 h6960 levelNine_chunk_6976
  have h6992 := Entries.checkRange_append levelNine _ 6912 80 16 h6976 levelNine_chunk_6992
  have h7008 := Entries.checkRange_append levelNine _ 6912 96 16 h6992 levelNine_chunk_7008
  have h7024 := Entries.checkRange_append levelNine _ 6912 112 16 h7008 levelNine_chunk_7024
  have h7040 := Entries.checkRange_append levelNine _ 6912 128 16 h7024 levelNine_chunk_7040
  have h7056 := Entries.checkRange_append levelNine _ 6912 144 16 h7040 levelNine_chunk_7056
  have h7072 := Entries.checkRange_append levelNine _ 6912 160 16 h7056 levelNine_chunk_7072
  have h7088 := Entries.checkRange_append levelNine _ 6912 176 16 h7072 levelNine_chunk_7088
  have h7104 := Entries.checkRange_append levelNine _ 6912 192 16 h7088 levelNine_chunk_7104
  have h7120 := Entries.checkRange_append levelNine _ 6912 208 16 h7104 levelNine_chunk_7120
  have h7136 := Entries.checkRange_append levelNine _ 6912 224 16 h7120 levelNine_chunk_7136
  have h7152 := Entries.checkRange_append levelNine _ 6912 240 16 h7136 levelNine_chunk_7152
  exact h7152
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_28 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 7168 256 = true := by
  have h0 := levelNine_chunk_7168
  have h7184 := Entries.checkRange_append levelNine _ 7168 16 16 h0 levelNine_chunk_7184
  have h7200 := Entries.checkRange_append levelNine _ 7168 32 16 h7184 levelNine_chunk_7200
  have h7216 := Entries.checkRange_append levelNine _ 7168 48 16 h7200 levelNine_chunk_7216
  have h7232 := Entries.checkRange_append levelNine _ 7168 64 16 h7216 levelNine_chunk_7232
  have h7248 := Entries.checkRange_append levelNine _ 7168 80 16 h7232 levelNine_chunk_7248
  have h7264 := Entries.checkRange_append levelNine _ 7168 96 16 h7248 levelNine_chunk_7264
  have h7280 := Entries.checkRange_append levelNine _ 7168 112 16 h7264 levelNine_chunk_7280
  have h7296 := Entries.checkRange_append levelNine _ 7168 128 16 h7280 levelNine_chunk_7296
  have h7312 := Entries.checkRange_append levelNine _ 7168 144 16 h7296 levelNine_chunk_7312
  have h7328 := Entries.checkRange_append levelNine _ 7168 160 16 h7312 levelNine_chunk_7328
  have h7344 := Entries.checkRange_append levelNine _ 7168 176 16 h7328 levelNine_chunk_7344
  have h7360 := Entries.checkRange_append levelNine _ 7168 192 16 h7344 levelNine_chunk_7360
  have h7376 := Entries.checkRange_append levelNine _ 7168 208 16 h7360 levelNine_chunk_7376
  have h7392 := Entries.checkRange_append levelNine _ 7168 224 16 h7376 levelNine_chunk_7392
  have h7408 := Entries.checkRange_append levelNine _ 7168 240 16 h7392 levelNine_chunk_7408
  exact h7408
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_29 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 7424 256 = true := by
  have h0 := levelNine_chunk_7424
  have h7440 := Entries.checkRange_append levelNine _ 7424 16 16 h0 levelNine_chunk_7440
  have h7456 := Entries.checkRange_append levelNine _ 7424 32 16 h7440 levelNine_chunk_7456
  have h7472 := Entries.checkRange_append levelNine _ 7424 48 16 h7456 levelNine_chunk_7472
  have h7488 := Entries.checkRange_append levelNine _ 7424 64 16 h7472 levelNine_chunk_7488
  have h7504 := Entries.checkRange_append levelNine _ 7424 80 16 h7488 levelNine_chunk_7504
  have h7520 := Entries.checkRange_append levelNine _ 7424 96 16 h7504 levelNine_chunk_7520
  have h7536 := Entries.checkRange_append levelNine _ 7424 112 16 h7520 levelNine_chunk_7536
  have h7552 := Entries.checkRange_append levelNine _ 7424 128 16 h7536 levelNine_chunk_7552
  have h7568 := Entries.checkRange_append levelNine _ 7424 144 16 h7552 levelNine_chunk_7568
  have h7584 := Entries.checkRange_append levelNine _ 7424 160 16 h7568 levelNine_chunk_7584
  have h7600 := Entries.checkRange_append levelNine _ 7424 176 16 h7584 levelNine_chunk_7600
  have h7616 := Entries.checkRange_append levelNine _ 7424 192 16 h7600 levelNine_chunk_7616
  have h7632 := Entries.checkRange_append levelNine _ 7424 208 16 h7616 levelNine_chunk_7632
  have h7648 := Entries.checkRange_append levelNine _ 7424 224 16 h7632 levelNine_chunk_7648
  have h7664 := Entries.checkRange_append levelNine _ 7424 240 16 h7648 levelNine_chunk_7664
  exact h7664
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_30 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 7680 256 = true := by
  have h0 := levelNine_chunk_7680
  have h7696 := Entries.checkRange_append levelNine _ 7680 16 16 h0 levelNine_chunk_7696
  have h7712 := Entries.checkRange_append levelNine _ 7680 32 16 h7696 levelNine_chunk_7712
  have h7728 := Entries.checkRange_append levelNine _ 7680 48 16 h7712 levelNine_chunk_7728
  have h7744 := Entries.checkRange_append levelNine _ 7680 64 16 h7728 levelNine_chunk_7744
  have h7760 := Entries.checkRange_append levelNine _ 7680 80 16 h7744 levelNine_chunk_7760
  have h7776 := Entries.checkRange_append levelNine _ 7680 96 16 h7760 levelNine_chunk_7776
  have h7792 := Entries.checkRange_append levelNine _ 7680 112 16 h7776 levelNine_chunk_7792
  have h7808 := Entries.checkRange_append levelNine _ 7680 128 16 h7792 levelNine_chunk_7808
  have h7824 := Entries.checkRange_append levelNine _ 7680 144 16 h7808 levelNine_chunk_7824
  have h7840 := Entries.checkRange_append levelNine _ 7680 160 16 h7824 levelNine_chunk_7840
  have h7856 := Entries.checkRange_append levelNine _ 7680 176 16 h7840 levelNine_chunk_7856
  have h7872 := Entries.checkRange_append levelNine _ 7680 192 16 h7856 levelNine_chunk_7872
  have h7888 := Entries.checkRange_append levelNine _ 7680 208 16 h7872 levelNine_chunk_7888
  have h7904 := Entries.checkRange_append levelNine _ 7680 224 16 h7888 levelNine_chunk_7904
  have h7920 := Entries.checkRange_append levelNine _ 7680 240 16 h7904 levelNine_chunk_7920
  exact h7920
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_31 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 7936 256 = true := by
  have h0 := levelNine_chunk_7936
  have h7952 := Entries.checkRange_append levelNine _ 7936 16 16 h0 levelNine_chunk_7952
  have h7968 := Entries.checkRange_append levelNine _ 7936 32 16 h7952 levelNine_chunk_7968
  have h7984 := Entries.checkRange_append levelNine _ 7936 48 16 h7968 levelNine_chunk_7984
  have h8000 := Entries.checkRange_append levelNine _ 7936 64 16 h7984 levelNine_chunk_8000
  have h8016 := Entries.checkRange_append levelNine _ 7936 80 16 h8000 levelNine_chunk_8016
  have h8032 := Entries.checkRange_append levelNine _ 7936 96 16 h8016 levelNine_chunk_8032
  have h8048 := Entries.checkRange_append levelNine _ 7936 112 16 h8032 levelNine_chunk_8048
  have h8064 := Entries.checkRange_append levelNine _ 7936 128 16 h8048 levelNine_chunk_8064
  have h8080 := Entries.checkRange_append levelNine _ 7936 144 16 h8064 levelNine_chunk_8080
  have h8096 := Entries.checkRange_append levelNine _ 7936 160 16 h8080 levelNine_chunk_8096
  have h8112 := Entries.checkRange_append levelNine _ 7936 176 16 h8096 levelNine_chunk_8112
  have h8128 := Entries.checkRange_append levelNine _ 7936 192 16 h8112 levelNine_chunk_8128
  have h8144 := Entries.checkRange_append levelNine _ 7936 208 16 h8128 levelNine_chunk_8144
  have h8160 := Entries.checkRange_append levelNine _ 7936 224 16 h8144 levelNine_chunk_8160
  have h8176 := Entries.checkRange_append levelNine _ 7936 240 16 h8160 levelNine_chunk_8176
  exact h8176
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_group_3 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 6144 2048 = true := by
  have h0 := levelNine_block_24
  have h25 := Entries.checkRange_append levelNine _ 6144 256 256 h0 levelNine_block_25
  have h26 := Entries.checkRange_append levelNine _ 6144 512 256 h25 levelNine_block_26
  have h27 := Entries.checkRange_append levelNine _ 6144 768 256 h26 levelNine_block_27
  have h28 := Entries.checkRange_append levelNine _ 6144 1024 256 h27 levelNine_block_28
  have h29 := Entries.checkRange_append levelNine _ 6144 1280 256 h28 levelNine_block_29
  have h30 := Entries.checkRange_append levelNine _ 6144 1536 256 h29 levelNine_block_30
  have h31 := Entries.checkRange_append levelNine _ 6144 1792 256 h30 levelNine_block_31
  exact h31
end WordCertDensity.Certificates
