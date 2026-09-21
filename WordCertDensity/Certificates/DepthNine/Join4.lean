/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module
public import WordCertDensity.Certificates.DepthNine.Transfer32
public import WordCertDensity.Certificates.DepthNine.Transfer33
public import WordCertDensity.Certificates.DepthNine.Transfer34
public import WordCertDensity.Certificates.DepthNine.Transfer35
public import WordCertDensity.Certificates.DepthNine.Transfer36
public import WordCertDensity.Certificates.DepthNine.Transfer37
public import WordCertDensity.Certificates.DepthNine.Transfer38
public import WordCertDensity.Certificates.DepthNine.Transfer39
/-! # Depth-nine integer certificate component -/

@[expose] public section
namespace WordCertDensity.Certificates
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_32 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 8192 256 = true := by
  have h0 := levelNine_chunk_8192
  have h8208 := Entries.checkRange_append levelNine _ 8192 16 16 h0 levelNine_chunk_8208
  have h8224 := Entries.checkRange_append levelNine _ 8192 32 16 h8208 levelNine_chunk_8224
  have h8240 := Entries.checkRange_append levelNine _ 8192 48 16 h8224 levelNine_chunk_8240
  have h8256 := Entries.checkRange_append levelNine _ 8192 64 16 h8240 levelNine_chunk_8256
  have h8272 := Entries.checkRange_append levelNine _ 8192 80 16 h8256 levelNine_chunk_8272
  have h8288 := Entries.checkRange_append levelNine _ 8192 96 16 h8272 levelNine_chunk_8288
  have h8304 := Entries.checkRange_append levelNine _ 8192 112 16 h8288 levelNine_chunk_8304
  have h8320 := Entries.checkRange_append levelNine _ 8192 128 16 h8304 levelNine_chunk_8320
  have h8336 := Entries.checkRange_append levelNine _ 8192 144 16 h8320 levelNine_chunk_8336
  have h8352 := Entries.checkRange_append levelNine _ 8192 160 16 h8336 levelNine_chunk_8352
  have h8368 := Entries.checkRange_append levelNine _ 8192 176 16 h8352 levelNine_chunk_8368
  have h8384 := Entries.checkRange_append levelNine _ 8192 192 16 h8368 levelNine_chunk_8384
  have h8400 := Entries.checkRange_append levelNine _ 8192 208 16 h8384 levelNine_chunk_8400
  have h8416 := Entries.checkRange_append levelNine _ 8192 224 16 h8400 levelNine_chunk_8416
  have h8432 := Entries.checkRange_append levelNine _ 8192 240 16 h8416 levelNine_chunk_8432
  exact h8432
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_33 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 8448 256 = true := by
  have h0 := levelNine_chunk_8448
  have h8464 := Entries.checkRange_append levelNine _ 8448 16 16 h0 levelNine_chunk_8464
  have h8480 := Entries.checkRange_append levelNine _ 8448 32 16 h8464 levelNine_chunk_8480
  have h8496 := Entries.checkRange_append levelNine _ 8448 48 16 h8480 levelNine_chunk_8496
  have h8512 := Entries.checkRange_append levelNine _ 8448 64 16 h8496 levelNine_chunk_8512
  have h8528 := Entries.checkRange_append levelNine _ 8448 80 16 h8512 levelNine_chunk_8528
  have h8544 := Entries.checkRange_append levelNine _ 8448 96 16 h8528 levelNine_chunk_8544
  have h8560 := Entries.checkRange_append levelNine _ 8448 112 16 h8544 levelNine_chunk_8560
  have h8576 := Entries.checkRange_append levelNine _ 8448 128 16 h8560 levelNine_chunk_8576
  have h8592 := Entries.checkRange_append levelNine _ 8448 144 16 h8576 levelNine_chunk_8592
  have h8608 := Entries.checkRange_append levelNine _ 8448 160 16 h8592 levelNine_chunk_8608
  have h8624 := Entries.checkRange_append levelNine _ 8448 176 16 h8608 levelNine_chunk_8624
  have h8640 := Entries.checkRange_append levelNine _ 8448 192 16 h8624 levelNine_chunk_8640
  have h8656 := Entries.checkRange_append levelNine _ 8448 208 16 h8640 levelNine_chunk_8656
  have h8672 := Entries.checkRange_append levelNine _ 8448 224 16 h8656 levelNine_chunk_8672
  have h8688 := Entries.checkRange_append levelNine _ 8448 240 16 h8672 levelNine_chunk_8688
  exact h8688
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_34 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 8704 256 = true := by
  have h0 := levelNine_chunk_8704
  have h8720 := Entries.checkRange_append levelNine _ 8704 16 16 h0 levelNine_chunk_8720
  have h8736 := Entries.checkRange_append levelNine _ 8704 32 16 h8720 levelNine_chunk_8736
  have h8752 := Entries.checkRange_append levelNine _ 8704 48 16 h8736 levelNine_chunk_8752
  have h8768 := Entries.checkRange_append levelNine _ 8704 64 16 h8752 levelNine_chunk_8768
  have h8784 := Entries.checkRange_append levelNine _ 8704 80 16 h8768 levelNine_chunk_8784
  have h8800 := Entries.checkRange_append levelNine _ 8704 96 16 h8784 levelNine_chunk_8800
  have h8816 := Entries.checkRange_append levelNine _ 8704 112 16 h8800 levelNine_chunk_8816
  have h8832 := Entries.checkRange_append levelNine _ 8704 128 16 h8816 levelNine_chunk_8832
  have h8848 := Entries.checkRange_append levelNine _ 8704 144 16 h8832 levelNine_chunk_8848
  have h8864 := Entries.checkRange_append levelNine _ 8704 160 16 h8848 levelNine_chunk_8864
  have h8880 := Entries.checkRange_append levelNine _ 8704 176 16 h8864 levelNine_chunk_8880
  have h8896 := Entries.checkRange_append levelNine _ 8704 192 16 h8880 levelNine_chunk_8896
  have h8912 := Entries.checkRange_append levelNine _ 8704 208 16 h8896 levelNine_chunk_8912
  have h8928 := Entries.checkRange_append levelNine _ 8704 224 16 h8912 levelNine_chunk_8928
  have h8944 := Entries.checkRange_append levelNine _ 8704 240 16 h8928 levelNine_chunk_8944
  exact h8944
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_35 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 8960 256 = true := by
  have h0 := levelNine_chunk_8960
  have h8976 := Entries.checkRange_append levelNine _ 8960 16 16 h0 levelNine_chunk_8976
  have h8992 := Entries.checkRange_append levelNine _ 8960 32 16 h8976 levelNine_chunk_8992
  have h9008 := Entries.checkRange_append levelNine _ 8960 48 16 h8992 levelNine_chunk_9008
  have h9024 := Entries.checkRange_append levelNine _ 8960 64 16 h9008 levelNine_chunk_9024
  have h9040 := Entries.checkRange_append levelNine _ 8960 80 16 h9024 levelNine_chunk_9040
  have h9056 := Entries.checkRange_append levelNine _ 8960 96 16 h9040 levelNine_chunk_9056
  have h9072 := Entries.checkRange_append levelNine _ 8960 112 16 h9056 levelNine_chunk_9072
  have h9088 := Entries.checkRange_append levelNine _ 8960 128 16 h9072 levelNine_chunk_9088
  have h9104 := Entries.checkRange_append levelNine _ 8960 144 16 h9088 levelNine_chunk_9104
  have h9120 := Entries.checkRange_append levelNine _ 8960 160 16 h9104 levelNine_chunk_9120
  have h9136 := Entries.checkRange_append levelNine _ 8960 176 16 h9120 levelNine_chunk_9136
  have h9152 := Entries.checkRange_append levelNine _ 8960 192 16 h9136 levelNine_chunk_9152
  have h9168 := Entries.checkRange_append levelNine _ 8960 208 16 h9152 levelNine_chunk_9168
  have h9184 := Entries.checkRange_append levelNine _ 8960 224 16 h9168 levelNine_chunk_9184
  have h9200 := Entries.checkRange_append levelNine _ 8960 240 16 h9184 levelNine_chunk_9200
  exact h9200
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_36 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 9216 256 = true := by
  have h0 := levelNine_chunk_9216
  have h9232 := Entries.checkRange_append levelNine _ 9216 16 16 h0 levelNine_chunk_9232
  have h9248 := Entries.checkRange_append levelNine _ 9216 32 16 h9232 levelNine_chunk_9248
  have h9264 := Entries.checkRange_append levelNine _ 9216 48 16 h9248 levelNine_chunk_9264
  have h9280 := Entries.checkRange_append levelNine _ 9216 64 16 h9264 levelNine_chunk_9280
  have h9296 := Entries.checkRange_append levelNine _ 9216 80 16 h9280 levelNine_chunk_9296
  have h9312 := Entries.checkRange_append levelNine _ 9216 96 16 h9296 levelNine_chunk_9312
  have h9328 := Entries.checkRange_append levelNine _ 9216 112 16 h9312 levelNine_chunk_9328
  have h9344 := Entries.checkRange_append levelNine _ 9216 128 16 h9328 levelNine_chunk_9344
  have h9360 := Entries.checkRange_append levelNine _ 9216 144 16 h9344 levelNine_chunk_9360
  have h9376 := Entries.checkRange_append levelNine _ 9216 160 16 h9360 levelNine_chunk_9376
  have h9392 := Entries.checkRange_append levelNine _ 9216 176 16 h9376 levelNine_chunk_9392
  have h9408 := Entries.checkRange_append levelNine _ 9216 192 16 h9392 levelNine_chunk_9408
  have h9424 := Entries.checkRange_append levelNine _ 9216 208 16 h9408 levelNine_chunk_9424
  have h9440 := Entries.checkRange_append levelNine _ 9216 224 16 h9424 levelNine_chunk_9440
  have h9456 := Entries.checkRange_append levelNine _ 9216 240 16 h9440 levelNine_chunk_9456
  exact h9456
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_37 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 9472 256 = true := by
  have h0 := levelNine_chunk_9472
  have h9488 := Entries.checkRange_append levelNine _ 9472 16 16 h0 levelNine_chunk_9488
  have h9504 := Entries.checkRange_append levelNine _ 9472 32 16 h9488 levelNine_chunk_9504
  have h9520 := Entries.checkRange_append levelNine _ 9472 48 16 h9504 levelNine_chunk_9520
  have h9536 := Entries.checkRange_append levelNine _ 9472 64 16 h9520 levelNine_chunk_9536
  have h9552 := Entries.checkRange_append levelNine _ 9472 80 16 h9536 levelNine_chunk_9552
  have h9568 := Entries.checkRange_append levelNine _ 9472 96 16 h9552 levelNine_chunk_9568
  have h9584 := Entries.checkRange_append levelNine _ 9472 112 16 h9568 levelNine_chunk_9584
  have h9600 := Entries.checkRange_append levelNine _ 9472 128 16 h9584 levelNine_chunk_9600
  have h9616 := Entries.checkRange_append levelNine _ 9472 144 16 h9600 levelNine_chunk_9616
  have h9632 := Entries.checkRange_append levelNine _ 9472 160 16 h9616 levelNine_chunk_9632
  have h9648 := Entries.checkRange_append levelNine _ 9472 176 16 h9632 levelNine_chunk_9648
  have h9664 := Entries.checkRange_append levelNine _ 9472 192 16 h9648 levelNine_chunk_9664
  have h9680 := Entries.checkRange_append levelNine _ 9472 208 16 h9664 levelNine_chunk_9680
  have h9696 := Entries.checkRange_append levelNine _ 9472 224 16 h9680 levelNine_chunk_9696
  have h9712 := Entries.checkRange_append levelNine _ 9472 240 16 h9696 levelNine_chunk_9712
  exact h9712
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_38 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 9728 256 = true := by
  have h0 := levelNine_chunk_9728
  have h9744 := Entries.checkRange_append levelNine _ 9728 16 16 h0 levelNine_chunk_9744
  have h9760 := Entries.checkRange_append levelNine _ 9728 32 16 h9744 levelNine_chunk_9760
  have h9776 := Entries.checkRange_append levelNine _ 9728 48 16 h9760 levelNine_chunk_9776
  have h9792 := Entries.checkRange_append levelNine _ 9728 64 16 h9776 levelNine_chunk_9792
  have h9808 := Entries.checkRange_append levelNine _ 9728 80 16 h9792 levelNine_chunk_9808
  have h9824 := Entries.checkRange_append levelNine _ 9728 96 16 h9808 levelNine_chunk_9824
  have h9840 := Entries.checkRange_append levelNine _ 9728 112 16 h9824 levelNine_chunk_9840
  have h9856 := Entries.checkRange_append levelNine _ 9728 128 16 h9840 levelNine_chunk_9856
  have h9872 := Entries.checkRange_append levelNine _ 9728 144 16 h9856 levelNine_chunk_9872
  have h9888 := Entries.checkRange_append levelNine _ 9728 160 16 h9872 levelNine_chunk_9888
  have h9904 := Entries.checkRange_append levelNine _ 9728 176 16 h9888 levelNine_chunk_9904
  have h9920 := Entries.checkRange_append levelNine _ 9728 192 16 h9904 levelNine_chunk_9920
  have h9936 := Entries.checkRange_append levelNine _ 9728 208 16 h9920 levelNine_chunk_9936
  have h9952 := Entries.checkRange_append levelNine _ 9728 224 16 h9936 levelNine_chunk_9952
  have h9968 := Entries.checkRange_append levelNine _ 9728 240 16 h9952 levelNine_chunk_9968
  exact h9968
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_39 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 9984 256 = true := by
  have h0 := levelNine_chunk_9984
  have h10000 := Entries.checkRange_append levelNine _ 9984 16 16 h0 levelNine_chunk_10000
  have h10016 := Entries.checkRange_append levelNine _ 9984 32 16 h10000 levelNine_chunk_10016
  have h10032 := Entries.checkRange_append levelNine _ 9984 48 16 h10016 levelNine_chunk_10032
  have h10048 := Entries.checkRange_append levelNine _ 9984 64 16 h10032 levelNine_chunk_10048
  have h10064 := Entries.checkRange_append levelNine _ 9984 80 16 h10048 levelNine_chunk_10064
  have h10080 := Entries.checkRange_append levelNine _ 9984 96 16 h10064 levelNine_chunk_10080
  have h10096 := Entries.checkRange_append levelNine _ 9984 112 16 h10080 levelNine_chunk_10096
  have h10112 := Entries.checkRange_append levelNine _ 9984 128 16 h10096 levelNine_chunk_10112
  have h10128 := Entries.checkRange_append levelNine _ 9984 144 16 h10112 levelNine_chunk_10128
  have h10144 := Entries.checkRange_append levelNine _ 9984 160 16 h10128 levelNine_chunk_10144
  have h10160 := Entries.checkRange_append levelNine _ 9984 176 16 h10144 levelNine_chunk_10160
  have h10176 := Entries.checkRange_append levelNine _ 9984 192 16 h10160 levelNine_chunk_10176
  have h10192 := Entries.checkRange_append levelNine _ 9984 208 16 h10176 levelNine_chunk_10192
  have h10208 := Entries.checkRange_append levelNine _ 9984 224 16 h10192 levelNine_chunk_10208
  have h10224 := Entries.checkRange_append levelNine _ 9984 240 16 h10208 levelNine_chunk_10224
  exact h10224
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_group_4 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 8192 2048 = true := by
  have h0 := levelNine_block_32
  have h33 := Entries.checkRange_append levelNine _ 8192 256 256 h0 levelNine_block_33
  have h34 := Entries.checkRange_append levelNine _ 8192 512 256 h33 levelNine_block_34
  have h35 := Entries.checkRange_append levelNine _ 8192 768 256 h34 levelNine_block_35
  have h36 := Entries.checkRange_append levelNine _ 8192 1024 256 h35 levelNine_block_36
  have h37 := Entries.checkRange_append levelNine _ 8192 1280 256 h36 levelNine_block_37
  have h38 := Entries.checkRange_append levelNine _ 8192 1536 256 h37 levelNine_block_38
  have h39 := Entries.checkRange_append levelNine _ 8192 1792 256 h38 levelNine_block_39
  exact h39
end WordCertDensity.Certificates
