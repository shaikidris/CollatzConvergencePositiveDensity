/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module
public import WordCertDensity.Certificates.DepthNine.Transfer64
public import WordCertDensity.Certificates.DepthNine.Transfer65
public import WordCertDensity.Certificates.DepthNine.Transfer66
public import WordCertDensity.Certificates.DepthNine.Transfer67
public import WordCertDensity.Certificates.DepthNine.Transfer68
public import WordCertDensity.Certificates.DepthNine.Transfer69
public import WordCertDensity.Certificates.DepthNine.Transfer70
public import WordCertDensity.Certificates.DepthNine.Transfer71
/-! # Depth-nine integer certificate component -/

@[expose] public section
namespace WordCertDensity.Certificates
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_64 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 16384 256 = true := by
  have h0 := levelNine_chunk_16384
  have h16400 := Entries.checkRange_append levelNine _ 16384 16 16 h0 levelNine_chunk_16400
  have h16416 := Entries.checkRange_append levelNine _ 16384 32 16 h16400 levelNine_chunk_16416
  have h16432 := Entries.checkRange_append levelNine _ 16384 48 16 h16416 levelNine_chunk_16432
  have h16448 := Entries.checkRange_append levelNine _ 16384 64 16 h16432 levelNine_chunk_16448
  have h16464 := Entries.checkRange_append levelNine _ 16384 80 16 h16448 levelNine_chunk_16464
  have h16480 := Entries.checkRange_append levelNine _ 16384 96 16 h16464 levelNine_chunk_16480
  have h16496 := Entries.checkRange_append levelNine _ 16384 112 16 h16480 levelNine_chunk_16496
  have h16512 := Entries.checkRange_append levelNine _ 16384 128 16 h16496 levelNine_chunk_16512
  have h16528 := Entries.checkRange_append levelNine _ 16384 144 16 h16512 levelNine_chunk_16528
  have h16544 := Entries.checkRange_append levelNine _ 16384 160 16 h16528 levelNine_chunk_16544
  have h16560 := Entries.checkRange_append levelNine _ 16384 176 16 h16544 levelNine_chunk_16560
  have h16576 := Entries.checkRange_append levelNine _ 16384 192 16 h16560 levelNine_chunk_16576
  have h16592 := Entries.checkRange_append levelNine _ 16384 208 16 h16576 levelNine_chunk_16592
  have h16608 := Entries.checkRange_append levelNine _ 16384 224 16 h16592 levelNine_chunk_16608
  have h16624 := Entries.checkRange_append levelNine _ 16384 240 16 h16608 levelNine_chunk_16624
  exact h16624
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_65 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 16640 256 = true := by
  have h0 := levelNine_chunk_16640
  have h16656 := Entries.checkRange_append levelNine _ 16640 16 16 h0 levelNine_chunk_16656
  have h16672 := Entries.checkRange_append levelNine _ 16640 32 16 h16656 levelNine_chunk_16672
  have h16688 := Entries.checkRange_append levelNine _ 16640 48 16 h16672 levelNine_chunk_16688
  have h16704 := Entries.checkRange_append levelNine _ 16640 64 16 h16688 levelNine_chunk_16704
  have h16720 := Entries.checkRange_append levelNine _ 16640 80 16 h16704 levelNine_chunk_16720
  have h16736 := Entries.checkRange_append levelNine _ 16640 96 16 h16720 levelNine_chunk_16736
  have h16752 := Entries.checkRange_append levelNine _ 16640 112 16 h16736 levelNine_chunk_16752
  have h16768 := Entries.checkRange_append levelNine _ 16640 128 16 h16752 levelNine_chunk_16768
  have h16784 := Entries.checkRange_append levelNine _ 16640 144 16 h16768 levelNine_chunk_16784
  have h16800 := Entries.checkRange_append levelNine _ 16640 160 16 h16784 levelNine_chunk_16800
  have h16816 := Entries.checkRange_append levelNine _ 16640 176 16 h16800 levelNine_chunk_16816
  have h16832 := Entries.checkRange_append levelNine _ 16640 192 16 h16816 levelNine_chunk_16832
  have h16848 := Entries.checkRange_append levelNine _ 16640 208 16 h16832 levelNine_chunk_16848
  have h16864 := Entries.checkRange_append levelNine _ 16640 224 16 h16848 levelNine_chunk_16864
  have h16880 := Entries.checkRange_append levelNine _ 16640 240 16 h16864 levelNine_chunk_16880
  exact h16880
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_66 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 16896 256 = true := by
  have h0 := levelNine_chunk_16896
  have h16912 := Entries.checkRange_append levelNine _ 16896 16 16 h0 levelNine_chunk_16912
  have h16928 := Entries.checkRange_append levelNine _ 16896 32 16 h16912 levelNine_chunk_16928
  have h16944 := Entries.checkRange_append levelNine _ 16896 48 16 h16928 levelNine_chunk_16944
  have h16960 := Entries.checkRange_append levelNine _ 16896 64 16 h16944 levelNine_chunk_16960
  have h16976 := Entries.checkRange_append levelNine _ 16896 80 16 h16960 levelNine_chunk_16976
  have h16992 := Entries.checkRange_append levelNine _ 16896 96 16 h16976 levelNine_chunk_16992
  have h17008 := Entries.checkRange_append levelNine _ 16896 112 16 h16992 levelNine_chunk_17008
  have h17024 := Entries.checkRange_append levelNine _ 16896 128 16 h17008 levelNine_chunk_17024
  have h17040 := Entries.checkRange_append levelNine _ 16896 144 16 h17024 levelNine_chunk_17040
  have h17056 := Entries.checkRange_append levelNine _ 16896 160 16 h17040 levelNine_chunk_17056
  have h17072 := Entries.checkRange_append levelNine _ 16896 176 16 h17056 levelNine_chunk_17072
  have h17088 := Entries.checkRange_append levelNine _ 16896 192 16 h17072 levelNine_chunk_17088
  have h17104 := Entries.checkRange_append levelNine _ 16896 208 16 h17088 levelNine_chunk_17104
  have h17120 := Entries.checkRange_append levelNine _ 16896 224 16 h17104 levelNine_chunk_17120
  have h17136 := Entries.checkRange_append levelNine _ 16896 240 16 h17120 levelNine_chunk_17136
  exact h17136
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_67 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 17152 256 = true := by
  have h0 := levelNine_chunk_17152
  have h17168 := Entries.checkRange_append levelNine _ 17152 16 16 h0 levelNine_chunk_17168
  have h17184 := Entries.checkRange_append levelNine _ 17152 32 16 h17168 levelNine_chunk_17184
  have h17200 := Entries.checkRange_append levelNine _ 17152 48 16 h17184 levelNine_chunk_17200
  have h17216 := Entries.checkRange_append levelNine _ 17152 64 16 h17200 levelNine_chunk_17216
  have h17232 := Entries.checkRange_append levelNine _ 17152 80 16 h17216 levelNine_chunk_17232
  have h17248 := Entries.checkRange_append levelNine _ 17152 96 16 h17232 levelNine_chunk_17248
  have h17264 := Entries.checkRange_append levelNine _ 17152 112 16 h17248 levelNine_chunk_17264
  have h17280 := Entries.checkRange_append levelNine _ 17152 128 16 h17264 levelNine_chunk_17280
  have h17296 := Entries.checkRange_append levelNine _ 17152 144 16 h17280 levelNine_chunk_17296
  have h17312 := Entries.checkRange_append levelNine _ 17152 160 16 h17296 levelNine_chunk_17312
  have h17328 := Entries.checkRange_append levelNine _ 17152 176 16 h17312 levelNine_chunk_17328
  have h17344 := Entries.checkRange_append levelNine _ 17152 192 16 h17328 levelNine_chunk_17344
  have h17360 := Entries.checkRange_append levelNine _ 17152 208 16 h17344 levelNine_chunk_17360
  have h17376 := Entries.checkRange_append levelNine _ 17152 224 16 h17360 levelNine_chunk_17376
  have h17392 := Entries.checkRange_append levelNine _ 17152 240 16 h17376 levelNine_chunk_17392
  exact h17392
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_68 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 17408 256 = true := by
  have h0 := levelNine_chunk_17408
  have h17424 := Entries.checkRange_append levelNine _ 17408 16 16 h0 levelNine_chunk_17424
  have h17440 := Entries.checkRange_append levelNine _ 17408 32 16 h17424 levelNine_chunk_17440
  have h17456 := Entries.checkRange_append levelNine _ 17408 48 16 h17440 levelNine_chunk_17456
  have h17472 := Entries.checkRange_append levelNine _ 17408 64 16 h17456 levelNine_chunk_17472
  have h17488 := Entries.checkRange_append levelNine _ 17408 80 16 h17472 levelNine_chunk_17488
  have h17504 := Entries.checkRange_append levelNine _ 17408 96 16 h17488 levelNine_chunk_17504
  have h17520 := Entries.checkRange_append levelNine _ 17408 112 16 h17504 levelNine_chunk_17520
  have h17536 := Entries.checkRange_append levelNine _ 17408 128 16 h17520 levelNine_chunk_17536
  have h17552 := Entries.checkRange_append levelNine _ 17408 144 16 h17536 levelNine_chunk_17552
  have h17568 := Entries.checkRange_append levelNine _ 17408 160 16 h17552 levelNine_chunk_17568
  have h17584 := Entries.checkRange_append levelNine _ 17408 176 16 h17568 levelNine_chunk_17584
  have h17600 := Entries.checkRange_append levelNine _ 17408 192 16 h17584 levelNine_chunk_17600
  have h17616 := Entries.checkRange_append levelNine _ 17408 208 16 h17600 levelNine_chunk_17616
  have h17632 := Entries.checkRange_append levelNine _ 17408 224 16 h17616 levelNine_chunk_17632
  have h17648 := Entries.checkRange_append levelNine _ 17408 240 16 h17632 levelNine_chunk_17648
  exact h17648
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_69 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 17664 256 = true := by
  have h0 := levelNine_chunk_17664
  have h17680 := Entries.checkRange_append levelNine _ 17664 16 16 h0 levelNine_chunk_17680
  have h17696 := Entries.checkRange_append levelNine _ 17664 32 16 h17680 levelNine_chunk_17696
  have h17712 := Entries.checkRange_append levelNine _ 17664 48 16 h17696 levelNine_chunk_17712
  have h17728 := Entries.checkRange_append levelNine _ 17664 64 16 h17712 levelNine_chunk_17728
  have h17744 := Entries.checkRange_append levelNine _ 17664 80 16 h17728 levelNine_chunk_17744
  have h17760 := Entries.checkRange_append levelNine _ 17664 96 16 h17744 levelNine_chunk_17760
  have h17776 := Entries.checkRange_append levelNine _ 17664 112 16 h17760 levelNine_chunk_17776
  have h17792 := Entries.checkRange_append levelNine _ 17664 128 16 h17776 levelNine_chunk_17792
  have h17808 := Entries.checkRange_append levelNine _ 17664 144 16 h17792 levelNine_chunk_17808
  have h17824 := Entries.checkRange_append levelNine _ 17664 160 16 h17808 levelNine_chunk_17824
  have h17840 := Entries.checkRange_append levelNine _ 17664 176 16 h17824 levelNine_chunk_17840
  have h17856 := Entries.checkRange_append levelNine _ 17664 192 16 h17840 levelNine_chunk_17856
  have h17872 := Entries.checkRange_append levelNine _ 17664 208 16 h17856 levelNine_chunk_17872
  have h17888 := Entries.checkRange_append levelNine _ 17664 224 16 h17872 levelNine_chunk_17888
  have h17904 := Entries.checkRange_append levelNine _ 17664 240 16 h17888 levelNine_chunk_17904
  exact h17904
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_70 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 17920 256 = true := by
  have h0 := levelNine_chunk_17920
  have h17936 := Entries.checkRange_append levelNine _ 17920 16 16 h0 levelNine_chunk_17936
  have h17952 := Entries.checkRange_append levelNine _ 17920 32 16 h17936 levelNine_chunk_17952
  have h17968 := Entries.checkRange_append levelNine _ 17920 48 16 h17952 levelNine_chunk_17968
  have h17984 := Entries.checkRange_append levelNine _ 17920 64 16 h17968 levelNine_chunk_17984
  have h18000 := Entries.checkRange_append levelNine _ 17920 80 16 h17984 levelNine_chunk_18000
  have h18016 := Entries.checkRange_append levelNine _ 17920 96 16 h18000 levelNine_chunk_18016
  have h18032 := Entries.checkRange_append levelNine _ 17920 112 16 h18016 levelNine_chunk_18032
  have h18048 := Entries.checkRange_append levelNine _ 17920 128 16 h18032 levelNine_chunk_18048
  have h18064 := Entries.checkRange_append levelNine _ 17920 144 16 h18048 levelNine_chunk_18064
  have h18080 := Entries.checkRange_append levelNine _ 17920 160 16 h18064 levelNine_chunk_18080
  have h18096 := Entries.checkRange_append levelNine _ 17920 176 16 h18080 levelNine_chunk_18096
  have h18112 := Entries.checkRange_append levelNine _ 17920 192 16 h18096 levelNine_chunk_18112
  have h18128 := Entries.checkRange_append levelNine _ 17920 208 16 h18112 levelNine_chunk_18128
  have h18144 := Entries.checkRange_append levelNine _ 17920 224 16 h18128 levelNine_chunk_18144
  have h18160 := Entries.checkRange_append levelNine _ 17920 240 16 h18144 levelNine_chunk_18160
  exact h18160
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_71 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 18176 256 = true := by
  have h0 := levelNine_chunk_18176
  have h18192 := Entries.checkRange_append levelNine _ 18176 16 16 h0 levelNine_chunk_18192
  have h18208 := Entries.checkRange_append levelNine _ 18176 32 16 h18192 levelNine_chunk_18208
  have h18224 := Entries.checkRange_append levelNine _ 18176 48 16 h18208 levelNine_chunk_18224
  have h18240 := Entries.checkRange_append levelNine _ 18176 64 16 h18224 levelNine_chunk_18240
  have h18256 := Entries.checkRange_append levelNine _ 18176 80 16 h18240 levelNine_chunk_18256
  have h18272 := Entries.checkRange_append levelNine _ 18176 96 16 h18256 levelNine_chunk_18272
  have h18288 := Entries.checkRange_append levelNine _ 18176 112 16 h18272 levelNine_chunk_18288
  have h18304 := Entries.checkRange_append levelNine _ 18176 128 16 h18288 levelNine_chunk_18304
  have h18320 := Entries.checkRange_append levelNine _ 18176 144 16 h18304 levelNine_chunk_18320
  have h18336 := Entries.checkRange_append levelNine _ 18176 160 16 h18320 levelNine_chunk_18336
  have h18352 := Entries.checkRange_append levelNine _ 18176 176 16 h18336 levelNine_chunk_18352
  have h18368 := Entries.checkRange_append levelNine _ 18176 192 16 h18352 levelNine_chunk_18368
  have h18384 := Entries.checkRange_append levelNine _ 18176 208 16 h18368 levelNine_chunk_18384
  have h18400 := Entries.checkRange_append levelNine _ 18176 224 16 h18384 levelNine_chunk_18400
  have h18416 := Entries.checkRange_append levelNine _ 18176 240 16 h18400 levelNine_chunk_18416
  exact h18416
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_group_8 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 16384 2048 = true := by
  have h0 := levelNine_block_64
  have h65 := Entries.checkRange_append levelNine _ 16384 256 256 h0 levelNine_block_65
  have h66 := Entries.checkRange_append levelNine _ 16384 512 256 h65 levelNine_block_66
  have h67 := Entries.checkRange_append levelNine _ 16384 768 256 h66 levelNine_block_67
  have h68 := Entries.checkRange_append levelNine _ 16384 1024 256 h67 levelNine_block_68
  have h69 := Entries.checkRange_append levelNine _ 16384 1280 256 h68 levelNine_block_69
  have h70 := Entries.checkRange_append levelNine _ 16384 1536 256 h69 levelNine_block_70
  have h71 := Entries.checkRange_append levelNine _ 16384 1792 256 h70 levelNine_block_71
  exact h71
end WordCertDensity.Certificates
