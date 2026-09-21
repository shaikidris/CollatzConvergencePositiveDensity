/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module
public import WordCertDensity.Certificates.DepthNine.Transfer16
public import WordCertDensity.Certificates.DepthNine.Transfer17
public import WordCertDensity.Certificates.DepthNine.Transfer18
public import WordCertDensity.Certificates.DepthNine.Transfer19
public import WordCertDensity.Certificates.DepthNine.Transfer20
public import WordCertDensity.Certificates.DepthNine.Transfer21
public import WordCertDensity.Certificates.DepthNine.Transfer22
public import WordCertDensity.Certificates.DepthNine.Transfer23
/-! # Depth-nine integer certificate component -/

@[expose] public section
namespace WordCertDensity.Certificates
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_16 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 4096 256 = true := by
  have h0 := levelNine_chunk_4096
  have h4112 := Entries.checkRange_append levelNine _ 4096 16 16 h0 levelNine_chunk_4112
  have h4128 := Entries.checkRange_append levelNine _ 4096 32 16 h4112 levelNine_chunk_4128
  have h4144 := Entries.checkRange_append levelNine _ 4096 48 16 h4128 levelNine_chunk_4144
  have h4160 := Entries.checkRange_append levelNine _ 4096 64 16 h4144 levelNine_chunk_4160
  have h4176 := Entries.checkRange_append levelNine _ 4096 80 16 h4160 levelNine_chunk_4176
  have h4192 := Entries.checkRange_append levelNine _ 4096 96 16 h4176 levelNine_chunk_4192
  have h4208 := Entries.checkRange_append levelNine _ 4096 112 16 h4192 levelNine_chunk_4208
  have h4224 := Entries.checkRange_append levelNine _ 4096 128 16 h4208 levelNine_chunk_4224
  have h4240 := Entries.checkRange_append levelNine _ 4096 144 16 h4224 levelNine_chunk_4240
  have h4256 := Entries.checkRange_append levelNine _ 4096 160 16 h4240 levelNine_chunk_4256
  have h4272 := Entries.checkRange_append levelNine _ 4096 176 16 h4256 levelNine_chunk_4272
  have h4288 := Entries.checkRange_append levelNine _ 4096 192 16 h4272 levelNine_chunk_4288
  have h4304 := Entries.checkRange_append levelNine _ 4096 208 16 h4288 levelNine_chunk_4304
  have h4320 := Entries.checkRange_append levelNine _ 4096 224 16 h4304 levelNine_chunk_4320
  have h4336 := Entries.checkRange_append levelNine _ 4096 240 16 h4320 levelNine_chunk_4336
  exact h4336
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_17 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 4352 256 = true := by
  have h0 := levelNine_chunk_4352
  have h4368 := Entries.checkRange_append levelNine _ 4352 16 16 h0 levelNine_chunk_4368
  have h4384 := Entries.checkRange_append levelNine _ 4352 32 16 h4368 levelNine_chunk_4384
  have h4400 := Entries.checkRange_append levelNine _ 4352 48 16 h4384 levelNine_chunk_4400
  have h4416 := Entries.checkRange_append levelNine _ 4352 64 16 h4400 levelNine_chunk_4416
  have h4432 := Entries.checkRange_append levelNine _ 4352 80 16 h4416 levelNine_chunk_4432
  have h4448 := Entries.checkRange_append levelNine _ 4352 96 16 h4432 levelNine_chunk_4448
  have h4464 := Entries.checkRange_append levelNine _ 4352 112 16 h4448 levelNine_chunk_4464
  have h4480 := Entries.checkRange_append levelNine _ 4352 128 16 h4464 levelNine_chunk_4480
  have h4496 := Entries.checkRange_append levelNine _ 4352 144 16 h4480 levelNine_chunk_4496
  have h4512 := Entries.checkRange_append levelNine _ 4352 160 16 h4496 levelNine_chunk_4512
  have h4528 := Entries.checkRange_append levelNine _ 4352 176 16 h4512 levelNine_chunk_4528
  have h4544 := Entries.checkRange_append levelNine _ 4352 192 16 h4528 levelNine_chunk_4544
  have h4560 := Entries.checkRange_append levelNine _ 4352 208 16 h4544 levelNine_chunk_4560
  have h4576 := Entries.checkRange_append levelNine _ 4352 224 16 h4560 levelNine_chunk_4576
  have h4592 := Entries.checkRange_append levelNine _ 4352 240 16 h4576 levelNine_chunk_4592
  exact h4592
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_18 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 4608 256 = true := by
  have h0 := levelNine_chunk_4608
  have h4624 := Entries.checkRange_append levelNine _ 4608 16 16 h0 levelNine_chunk_4624
  have h4640 := Entries.checkRange_append levelNine _ 4608 32 16 h4624 levelNine_chunk_4640
  have h4656 := Entries.checkRange_append levelNine _ 4608 48 16 h4640 levelNine_chunk_4656
  have h4672 := Entries.checkRange_append levelNine _ 4608 64 16 h4656 levelNine_chunk_4672
  have h4688 := Entries.checkRange_append levelNine _ 4608 80 16 h4672 levelNine_chunk_4688
  have h4704 := Entries.checkRange_append levelNine _ 4608 96 16 h4688 levelNine_chunk_4704
  have h4720 := Entries.checkRange_append levelNine _ 4608 112 16 h4704 levelNine_chunk_4720
  have h4736 := Entries.checkRange_append levelNine _ 4608 128 16 h4720 levelNine_chunk_4736
  have h4752 := Entries.checkRange_append levelNine _ 4608 144 16 h4736 levelNine_chunk_4752
  have h4768 := Entries.checkRange_append levelNine _ 4608 160 16 h4752 levelNine_chunk_4768
  have h4784 := Entries.checkRange_append levelNine _ 4608 176 16 h4768 levelNine_chunk_4784
  have h4800 := Entries.checkRange_append levelNine _ 4608 192 16 h4784 levelNine_chunk_4800
  have h4816 := Entries.checkRange_append levelNine _ 4608 208 16 h4800 levelNine_chunk_4816
  have h4832 := Entries.checkRange_append levelNine _ 4608 224 16 h4816 levelNine_chunk_4832
  have h4848 := Entries.checkRange_append levelNine _ 4608 240 16 h4832 levelNine_chunk_4848
  exact h4848
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_19 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 4864 256 = true := by
  have h0 := levelNine_chunk_4864
  have h4880 := Entries.checkRange_append levelNine _ 4864 16 16 h0 levelNine_chunk_4880
  have h4896 := Entries.checkRange_append levelNine _ 4864 32 16 h4880 levelNine_chunk_4896
  have h4912 := Entries.checkRange_append levelNine _ 4864 48 16 h4896 levelNine_chunk_4912
  have h4928 := Entries.checkRange_append levelNine _ 4864 64 16 h4912 levelNine_chunk_4928
  have h4944 := Entries.checkRange_append levelNine _ 4864 80 16 h4928 levelNine_chunk_4944
  have h4960 := Entries.checkRange_append levelNine _ 4864 96 16 h4944 levelNine_chunk_4960
  have h4976 := Entries.checkRange_append levelNine _ 4864 112 16 h4960 levelNine_chunk_4976
  have h4992 := Entries.checkRange_append levelNine _ 4864 128 16 h4976 levelNine_chunk_4992
  have h5008 := Entries.checkRange_append levelNine _ 4864 144 16 h4992 levelNine_chunk_5008
  have h5024 := Entries.checkRange_append levelNine _ 4864 160 16 h5008 levelNine_chunk_5024
  have h5040 := Entries.checkRange_append levelNine _ 4864 176 16 h5024 levelNine_chunk_5040
  have h5056 := Entries.checkRange_append levelNine _ 4864 192 16 h5040 levelNine_chunk_5056
  have h5072 := Entries.checkRange_append levelNine _ 4864 208 16 h5056 levelNine_chunk_5072
  have h5088 := Entries.checkRange_append levelNine _ 4864 224 16 h5072 levelNine_chunk_5088
  have h5104 := Entries.checkRange_append levelNine _ 4864 240 16 h5088 levelNine_chunk_5104
  exact h5104
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_20 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 5120 256 = true := by
  have h0 := levelNine_chunk_5120
  have h5136 := Entries.checkRange_append levelNine _ 5120 16 16 h0 levelNine_chunk_5136
  have h5152 := Entries.checkRange_append levelNine _ 5120 32 16 h5136 levelNine_chunk_5152
  have h5168 := Entries.checkRange_append levelNine _ 5120 48 16 h5152 levelNine_chunk_5168
  have h5184 := Entries.checkRange_append levelNine _ 5120 64 16 h5168 levelNine_chunk_5184
  have h5200 := Entries.checkRange_append levelNine _ 5120 80 16 h5184 levelNine_chunk_5200
  have h5216 := Entries.checkRange_append levelNine _ 5120 96 16 h5200 levelNine_chunk_5216
  have h5232 := Entries.checkRange_append levelNine _ 5120 112 16 h5216 levelNine_chunk_5232
  have h5248 := Entries.checkRange_append levelNine _ 5120 128 16 h5232 levelNine_chunk_5248
  have h5264 := Entries.checkRange_append levelNine _ 5120 144 16 h5248 levelNine_chunk_5264
  have h5280 := Entries.checkRange_append levelNine _ 5120 160 16 h5264 levelNine_chunk_5280
  have h5296 := Entries.checkRange_append levelNine _ 5120 176 16 h5280 levelNine_chunk_5296
  have h5312 := Entries.checkRange_append levelNine _ 5120 192 16 h5296 levelNine_chunk_5312
  have h5328 := Entries.checkRange_append levelNine _ 5120 208 16 h5312 levelNine_chunk_5328
  have h5344 := Entries.checkRange_append levelNine _ 5120 224 16 h5328 levelNine_chunk_5344
  have h5360 := Entries.checkRange_append levelNine _ 5120 240 16 h5344 levelNine_chunk_5360
  exact h5360
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_21 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 5376 256 = true := by
  have h0 := levelNine_chunk_5376
  have h5392 := Entries.checkRange_append levelNine _ 5376 16 16 h0 levelNine_chunk_5392
  have h5408 := Entries.checkRange_append levelNine _ 5376 32 16 h5392 levelNine_chunk_5408
  have h5424 := Entries.checkRange_append levelNine _ 5376 48 16 h5408 levelNine_chunk_5424
  have h5440 := Entries.checkRange_append levelNine _ 5376 64 16 h5424 levelNine_chunk_5440
  have h5456 := Entries.checkRange_append levelNine _ 5376 80 16 h5440 levelNine_chunk_5456
  have h5472 := Entries.checkRange_append levelNine _ 5376 96 16 h5456 levelNine_chunk_5472
  have h5488 := Entries.checkRange_append levelNine _ 5376 112 16 h5472 levelNine_chunk_5488
  have h5504 := Entries.checkRange_append levelNine _ 5376 128 16 h5488 levelNine_chunk_5504
  have h5520 := Entries.checkRange_append levelNine _ 5376 144 16 h5504 levelNine_chunk_5520
  have h5536 := Entries.checkRange_append levelNine _ 5376 160 16 h5520 levelNine_chunk_5536
  have h5552 := Entries.checkRange_append levelNine _ 5376 176 16 h5536 levelNine_chunk_5552
  have h5568 := Entries.checkRange_append levelNine _ 5376 192 16 h5552 levelNine_chunk_5568
  have h5584 := Entries.checkRange_append levelNine _ 5376 208 16 h5568 levelNine_chunk_5584
  have h5600 := Entries.checkRange_append levelNine _ 5376 224 16 h5584 levelNine_chunk_5600
  have h5616 := Entries.checkRange_append levelNine _ 5376 240 16 h5600 levelNine_chunk_5616
  exact h5616
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_22 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 5632 256 = true := by
  have h0 := levelNine_chunk_5632
  have h5648 := Entries.checkRange_append levelNine _ 5632 16 16 h0 levelNine_chunk_5648
  have h5664 := Entries.checkRange_append levelNine _ 5632 32 16 h5648 levelNine_chunk_5664
  have h5680 := Entries.checkRange_append levelNine _ 5632 48 16 h5664 levelNine_chunk_5680
  have h5696 := Entries.checkRange_append levelNine _ 5632 64 16 h5680 levelNine_chunk_5696
  have h5712 := Entries.checkRange_append levelNine _ 5632 80 16 h5696 levelNine_chunk_5712
  have h5728 := Entries.checkRange_append levelNine _ 5632 96 16 h5712 levelNine_chunk_5728
  have h5744 := Entries.checkRange_append levelNine _ 5632 112 16 h5728 levelNine_chunk_5744
  have h5760 := Entries.checkRange_append levelNine _ 5632 128 16 h5744 levelNine_chunk_5760
  have h5776 := Entries.checkRange_append levelNine _ 5632 144 16 h5760 levelNine_chunk_5776
  have h5792 := Entries.checkRange_append levelNine _ 5632 160 16 h5776 levelNine_chunk_5792
  have h5808 := Entries.checkRange_append levelNine _ 5632 176 16 h5792 levelNine_chunk_5808
  have h5824 := Entries.checkRange_append levelNine _ 5632 192 16 h5808 levelNine_chunk_5824
  have h5840 := Entries.checkRange_append levelNine _ 5632 208 16 h5824 levelNine_chunk_5840
  have h5856 := Entries.checkRange_append levelNine _ 5632 224 16 h5840 levelNine_chunk_5856
  have h5872 := Entries.checkRange_append levelNine _ 5632 240 16 h5856 levelNine_chunk_5872
  exact h5872
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_23 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 5888 256 = true := by
  have h0 := levelNine_chunk_5888
  have h5904 := Entries.checkRange_append levelNine _ 5888 16 16 h0 levelNine_chunk_5904
  have h5920 := Entries.checkRange_append levelNine _ 5888 32 16 h5904 levelNine_chunk_5920
  have h5936 := Entries.checkRange_append levelNine _ 5888 48 16 h5920 levelNine_chunk_5936
  have h5952 := Entries.checkRange_append levelNine _ 5888 64 16 h5936 levelNine_chunk_5952
  have h5968 := Entries.checkRange_append levelNine _ 5888 80 16 h5952 levelNine_chunk_5968
  have h5984 := Entries.checkRange_append levelNine _ 5888 96 16 h5968 levelNine_chunk_5984
  have h6000 := Entries.checkRange_append levelNine _ 5888 112 16 h5984 levelNine_chunk_6000
  have h6016 := Entries.checkRange_append levelNine _ 5888 128 16 h6000 levelNine_chunk_6016
  have h6032 := Entries.checkRange_append levelNine _ 5888 144 16 h6016 levelNine_chunk_6032
  have h6048 := Entries.checkRange_append levelNine _ 5888 160 16 h6032 levelNine_chunk_6048
  have h6064 := Entries.checkRange_append levelNine _ 5888 176 16 h6048 levelNine_chunk_6064
  have h6080 := Entries.checkRange_append levelNine _ 5888 192 16 h6064 levelNine_chunk_6080
  have h6096 := Entries.checkRange_append levelNine _ 5888 208 16 h6080 levelNine_chunk_6096
  have h6112 := Entries.checkRange_append levelNine _ 5888 224 16 h6096 levelNine_chunk_6112
  have h6128 := Entries.checkRange_append levelNine _ 5888 240 16 h6112 levelNine_chunk_6128
  exact h6128
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_group_2 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 4096 2048 = true := by
  have h0 := levelNine_block_16
  have h17 := Entries.checkRange_append levelNine _ 4096 256 256 h0 levelNine_block_17
  have h18 := Entries.checkRange_append levelNine _ 4096 512 256 h17 levelNine_block_18
  have h19 := Entries.checkRange_append levelNine _ 4096 768 256 h18 levelNine_block_19
  have h20 := Entries.checkRange_append levelNine _ 4096 1024 256 h19 levelNine_block_20
  have h21 := Entries.checkRange_append levelNine _ 4096 1280 256 h20 levelNine_block_21
  have h22 := Entries.checkRange_append levelNine _ 4096 1536 256 h21 levelNine_block_22
  have h23 := Entries.checkRange_append levelNine _ 4096 1792 256 h22 levelNine_block_23
  exact h23
end WordCertDensity.Certificates
