/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module
public import WordCertDensity.Certificates.DepthNine.Transfer48
public import WordCertDensity.Certificates.DepthNine.Transfer49
public import WordCertDensity.Certificates.DepthNine.Transfer50
public import WordCertDensity.Certificates.DepthNine.Transfer51
public import WordCertDensity.Certificates.DepthNine.Transfer52
public import WordCertDensity.Certificates.DepthNine.Transfer53
public import WordCertDensity.Certificates.DepthNine.Transfer54
public import WordCertDensity.Certificates.DepthNine.Transfer55
/-! # Depth-nine integer certificate component -/

@[expose] public section
namespace WordCertDensity.Certificates
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_48 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 12288 256 = true := by
  have h0 := levelNine_chunk_12288
  have h12304 := Entries.checkRange_append levelNine _ 12288 16 16 h0 levelNine_chunk_12304
  have h12320 := Entries.checkRange_append levelNine _ 12288 32 16 h12304 levelNine_chunk_12320
  have h12336 := Entries.checkRange_append levelNine _ 12288 48 16 h12320 levelNine_chunk_12336
  have h12352 := Entries.checkRange_append levelNine _ 12288 64 16 h12336 levelNine_chunk_12352
  have h12368 := Entries.checkRange_append levelNine _ 12288 80 16 h12352 levelNine_chunk_12368
  have h12384 := Entries.checkRange_append levelNine _ 12288 96 16 h12368 levelNine_chunk_12384
  have h12400 := Entries.checkRange_append levelNine _ 12288 112 16 h12384 levelNine_chunk_12400
  have h12416 := Entries.checkRange_append levelNine _ 12288 128 16 h12400 levelNine_chunk_12416
  have h12432 := Entries.checkRange_append levelNine _ 12288 144 16 h12416 levelNine_chunk_12432
  have h12448 := Entries.checkRange_append levelNine _ 12288 160 16 h12432 levelNine_chunk_12448
  have h12464 := Entries.checkRange_append levelNine _ 12288 176 16 h12448 levelNine_chunk_12464
  have h12480 := Entries.checkRange_append levelNine _ 12288 192 16 h12464 levelNine_chunk_12480
  have h12496 := Entries.checkRange_append levelNine _ 12288 208 16 h12480 levelNine_chunk_12496
  have h12512 := Entries.checkRange_append levelNine _ 12288 224 16 h12496 levelNine_chunk_12512
  have h12528 := Entries.checkRange_append levelNine _ 12288 240 16 h12512 levelNine_chunk_12528
  exact h12528
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_49 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 12544 256 = true := by
  have h0 := levelNine_chunk_12544
  have h12560 := Entries.checkRange_append levelNine _ 12544 16 16 h0 levelNine_chunk_12560
  have h12576 := Entries.checkRange_append levelNine _ 12544 32 16 h12560 levelNine_chunk_12576
  have h12592 := Entries.checkRange_append levelNine _ 12544 48 16 h12576 levelNine_chunk_12592
  have h12608 := Entries.checkRange_append levelNine _ 12544 64 16 h12592 levelNine_chunk_12608
  have h12624 := Entries.checkRange_append levelNine _ 12544 80 16 h12608 levelNine_chunk_12624
  have h12640 := Entries.checkRange_append levelNine _ 12544 96 16 h12624 levelNine_chunk_12640
  have h12656 := Entries.checkRange_append levelNine _ 12544 112 16 h12640 levelNine_chunk_12656
  have h12672 := Entries.checkRange_append levelNine _ 12544 128 16 h12656 levelNine_chunk_12672
  have h12688 := Entries.checkRange_append levelNine _ 12544 144 16 h12672 levelNine_chunk_12688
  have h12704 := Entries.checkRange_append levelNine _ 12544 160 16 h12688 levelNine_chunk_12704
  have h12720 := Entries.checkRange_append levelNine _ 12544 176 16 h12704 levelNine_chunk_12720
  have h12736 := Entries.checkRange_append levelNine _ 12544 192 16 h12720 levelNine_chunk_12736
  have h12752 := Entries.checkRange_append levelNine _ 12544 208 16 h12736 levelNine_chunk_12752
  have h12768 := Entries.checkRange_append levelNine _ 12544 224 16 h12752 levelNine_chunk_12768
  have h12784 := Entries.checkRange_append levelNine _ 12544 240 16 h12768 levelNine_chunk_12784
  exact h12784
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_50 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 12800 256 = true := by
  have h0 := levelNine_chunk_12800
  have h12816 := Entries.checkRange_append levelNine _ 12800 16 16 h0 levelNine_chunk_12816
  have h12832 := Entries.checkRange_append levelNine _ 12800 32 16 h12816 levelNine_chunk_12832
  have h12848 := Entries.checkRange_append levelNine _ 12800 48 16 h12832 levelNine_chunk_12848
  have h12864 := Entries.checkRange_append levelNine _ 12800 64 16 h12848 levelNine_chunk_12864
  have h12880 := Entries.checkRange_append levelNine _ 12800 80 16 h12864 levelNine_chunk_12880
  have h12896 := Entries.checkRange_append levelNine _ 12800 96 16 h12880 levelNine_chunk_12896
  have h12912 := Entries.checkRange_append levelNine _ 12800 112 16 h12896 levelNine_chunk_12912
  have h12928 := Entries.checkRange_append levelNine _ 12800 128 16 h12912 levelNine_chunk_12928
  have h12944 := Entries.checkRange_append levelNine _ 12800 144 16 h12928 levelNine_chunk_12944
  have h12960 := Entries.checkRange_append levelNine _ 12800 160 16 h12944 levelNine_chunk_12960
  have h12976 := Entries.checkRange_append levelNine _ 12800 176 16 h12960 levelNine_chunk_12976
  have h12992 := Entries.checkRange_append levelNine _ 12800 192 16 h12976 levelNine_chunk_12992
  have h13008 := Entries.checkRange_append levelNine _ 12800 208 16 h12992 levelNine_chunk_13008
  have h13024 := Entries.checkRange_append levelNine _ 12800 224 16 h13008 levelNine_chunk_13024
  have h13040 := Entries.checkRange_append levelNine _ 12800 240 16 h13024 levelNine_chunk_13040
  exact h13040
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_51 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 13056 256 = true := by
  have h0 := levelNine_chunk_13056
  have h13072 := Entries.checkRange_append levelNine _ 13056 16 16 h0 levelNine_chunk_13072
  have h13088 := Entries.checkRange_append levelNine _ 13056 32 16 h13072 levelNine_chunk_13088
  have h13104 := Entries.checkRange_append levelNine _ 13056 48 16 h13088 levelNine_chunk_13104
  have h13120 := Entries.checkRange_append levelNine _ 13056 64 16 h13104 levelNine_chunk_13120
  have h13136 := Entries.checkRange_append levelNine _ 13056 80 16 h13120 levelNine_chunk_13136
  have h13152 := Entries.checkRange_append levelNine _ 13056 96 16 h13136 levelNine_chunk_13152
  have h13168 := Entries.checkRange_append levelNine _ 13056 112 16 h13152 levelNine_chunk_13168
  have h13184 := Entries.checkRange_append levelNine _ 13056 128 16 h13168 levelNine_chunk_13184
  have h13200 := Entries.checkRange_append levelNine _ 13056 144 16 h13184 levelNine_chunk_13200
  have h13216 := Entries.checkRange_append levelNine _ 13056 160 16 h13200 levelNine_chunk_13216
  have h13232 := Entries.checkRange_append levelNine _ 13056 176 16 h13216 levelNine_chunk_13232
  have h13248 := Entries.checkRange_append levelNine _ 13056 192 16 h13232 levelNine_chunk_13248
  have h13264 := Entries.checkRange_append levelNine _ 13056 208 16 h13248 levelNine_chunk_13264
  have h13280 := Entries.checkRange_append levelNine _ 13056 224 16 h13264 levelNine_chunk_13280
  have h13296 := Entries.checkRange_append levelNine _ 13056 240 16 h13280 levelNine_chunk_13296
  exact h13296
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_52 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 13312 256 = true := by
  have h0 := levelNine_chunk_13312
  have h13328 := Entries.checkRange_append levelNine _ 13312 16 16 h0 levelNine_chunk_13328
  have h13344 := Entries.checkRange_append levelNine _ 13312 32 16 h13328 levelNine_chunk_13344
  have h13360 := Entries.checkRange_append levelNine _ 13312 48 16 h13344 levelNine_chunk_13360
  have h13376 := Entries.checkRange_append levelNine _ 13312 64 16 h13360 levelNine_chunk_13376
  have h13392 := Entries.checkRange_append levelNine _ 13312 80 16 h13376 levelNine_chunk_13392
  have h13408 := Entries.checkRange_append levelNine _ 13312 96 16 h13392 levelNine_chunk_13408
  have h13424 := Entries.checkRange_append levelNine _ 13312 112 16 h13408 levelNine_chunk_13424
  have h13440 := Entries.checkRange_append levelNine _ 13312 128 16 h13424 levelNine_chunk_13440
  have h13456 := Entries.checkRange_append levelNine _ 13312 144 16 h13440 levelNine_chunk_13456
  have h13472 := Entries.checkRange_append levelNine _ 13312 160 16 h13456 levelNine_chunk_13472
  have h13488 := Entries.checkRange_append levelNine _ 13312 176 16 h13472 levelNine_chunk_13488
  have h13504 := Entries.checkRange_append levelNine _ 13312 192 16 h13488 levelNine_chunk_13504
  have h13520 := Entries.checkRange_append levelNine _ 13312 208 16 h13504 levelNine_chunk_13520
  have h13536 := Entries.checkRange_append levelNine _ 13312 224 16 h13520 levelNine_chunk_13536
  have h13552 := Entries.checkRange_append levelNine _ 13312 240 16 h13536 levelNine_chunk_13552
  exact h13552
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_53 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 13568 256 = true := by
  have h0 := levelNine_chunk_13568
  have h13584 := Entries.checkRange_append levelNine _ 13568 16 16 h0 levelNine_chunk_13584
  have h13600 := Entries.checkRange_append levelNine _ 13568 32 16 h13584 levelNine_chunk_13600
  have h13616 := Entries.checkRange_append levelNine _ 13568 48 16 h13600 levelNine_chunk_13616
  have h13632 := Entries.checkRange_append levelNine _ 13568 64 16 h13616 levelNine_chunk_13632
  have h13648 := Entries.checkRange_append levelNine _ 13568 80 16 h13632 levelNine_chunk_13648
  have h13664 := Entries.checkRange_append levelNine _ 13568 96 16 h13648 levelNine_chunk_13664
  have h13680 := Entries.checkRange_append levelNine _ 13568 112 16 h13664 levelNine_chunk_13680
  have h13696 := Entries.checkRange_append levelNine _ 13568 128 16 h13680 levelNine_chunk_13696
  have h13712 := Entries.checkRange_append levelNine _ 13568 144 16 h13696 levelNine_chunk_13712
  have h13728 := Entries.checkRange_append levelNine _ 13568 160 16 h13712 levelNine_chunk_13728
  have h13744 := Entries.checkRange_append levelNine _ 13568 176 16 h13728 levelNine_chunk_13744
  have h13760 := Entries.checkRange_append levelNine _ 13568 192 16 h13744 levelNine_chunk_13760
  have h13776 := Entries.checkRange_append levelNine _ 13568 208 16 h13760 levelNine_chunk_13776
  have h13792 := Entries.checkRange_append levelNine _ 13568 224 16 h13776 levelNine_chunk_13792
  have h13808 := Entries.checkRange_append levelNine _ 13568 240 16 h13792 levelNine_chunk_13808
  exact h13808
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_54 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 13824 256 = true := by
  have h0 := levelNine_chunk_13824
  have h13840 := Entries.checkRange_append levelNine _ 13824 16 16 h0 levelNine_chunk_13840
  have h13856 := Entries.checkRange_append levelNine _ 13824 32 16 h13840 levelNine_chunk_13856
  have h13872 := Entries.checkRange_append levelNine _ 13824 48 16 h13856 levelNine_chunk_13872
  have h13888 := Entries.checkRange_append levelNine _ 13824 64 16 h13872 levelNine_chunk_13888
  have h13904 := Entries.checkRange_append levelNine _ 13824 80 16 h13888 levelNine_chunk_13904
  have h13920 := Entries.checkRange_append levelNine _ 13824 96 16 h13904 levelNine_chunk_13920
  have h13936 := Entries.checkRange_append levelNine _ 13824 112 16 h13920 levelNine_chunk_13936
  have h13952 := Entries.checkRange_append levelNine _ 13824 128 16 h13936 levelNine_chunk_13952
  have h13968 := Entries.checkRange_append levelNine _ 13824 144 16 h13952 levelNine_chunk_13968
  have h13984 := Entries.checkRange_append levelNine _ 13824 160 16 h13968 levelNine_chunk_13984
  have h14000 := Entries.checkRange_append levelNine _ 13824 176 16 h13984 levelNine_chunk_14000
  have h14016 := Entries.checkRange_append levelNine _ 13824 192 16 h14000 levelNine_chunk_14016
  have h14032 := Entries.checkRange_append levelNine _ 13824 208 16 h14016 levelNine_chunk_14032
  have h14048 := Entries.checkRange_append levelNine _ 13824 224 16 h14032 levelNine_chunk_14048
  have h14064 := Entries.checkRange_append levelNine _ 13824 240 16 h14048 levelNine_chunk_14064
  exact h14064
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_55 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 14080 256 = true := by
  have h0 := levelNine_chunk_14080
  have h14096 := Entries.checkRange_append levelNine _ 14080 16 16 h0 levelNine_chunk_14096
  have h14112 := Entries.checkRange_append levelNine _ 14080 32 16 h14096 levelNine_chunk_14112
  have h14128 := Entries.checkRange_append levelNine _ 14080 48 16 h14112 levelNine_chunk_14128
  have h14144 := Entries.checkRange_append levelNine _ 14080 64 16 h14128 levelNine_chunk_14144
  have h14160 := Entries.checkRange_append levelNine _ 14080 80 16 h14144 levelNine_chunk_14160
  have h14176 := Entries.checkRange_append levelNine _ 14080 96 16 h14160 levelNine_chunk_14176
  have h14192 := Entries.checkRange_append levelNine _ 14080 112 16 h14176 levelNine_chunk_14192
  have h14208 := Entries.checkRange_append levelNine _ 14080 128 16 h14192 levelNine_chunk_14208
  have h14224 := Entries.checkRange_append levelNine _ 14080 144 16 h14208 levelNine_chunk_14224
  have h14240 := Entries.checkRange_append levelNine _ 14080 160 16 h14224 levelNine_chunk_14240
  have h14256 := Entries.checkRange_append levelNine _ 14080 176 16 h14240 levelNine_chunk_14256
  have h14272 := Entries.checkRange_append levelNine _ 14080 192 16 h14256 levelNine_chunk_14272
  have h14288 := Entries.checkRange_append levelNine _ 14080 208 16 h14272 levelNine_chunk_14288
  have h14304 := Entries.checkRange_append levelNine _ 14080 224 16 h14288 levelNine_chunk_14304
  have h14320 := Entries.checkRange_append levelNine _ 14080 240 16 h14304 levelNine_chunk_14320
  exact h14320
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_group_6 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 12288 2048 = true := by
  have h0 := levelNine_block_48
  have h49 := Entries.checkRange_append levelNine _ 12288 256 256 h0 levelNine_block_49
  have h50 := Entries.checkRange_append levelNine _ 12288 512 256 h49 levelNine_block_50
  have h51 := Entries.checkRange_append levelNine _ 12288 768 256 h50 levelNine_block_51
  have h52 := Entries.checkRange_append levelNine _ 12288 1024 256 h51 levelNine_block_52
  have h53 := Entries.checkRange_append levelNine _ 12288 1280 256 h52 levelNine_block_53
  have h54 := Entries.checkRange_append levelNine _ 12288 1536 256 h53 levelNine_block_54
  have h55 := Entries.checkRange_append levelNine _ 12288 1792 256 h54 levelNine_block_55
  exact h55
end WordCertDensity.Certificates
