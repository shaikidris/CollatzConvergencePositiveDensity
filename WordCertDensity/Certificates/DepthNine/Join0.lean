/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module
public import WordCertDensity.Certificates.DepthNine.Transfer0
public import WordCertDensity.Certificates.DepthNine.Transfer1
public import WordCertDensity.Certificates.DepthNine.Transfer2
public import WordCertDensity.Certificates.DepthNine.Transfer3
public import WordCertDensity.Certificates.DepthNine.Transfer4
public import WordCertDensity.Certificates.DepthNine.Transfer5
public import WordCertDensity.Certificates.DepthNine.Transfer6
public import WordCertDensity.Certificates.DepthNine.Transfer7
/-! # Depth-nine integer certificate component -/

@[expose] public section
namespace WordCertDensity.Certificates
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_0 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 0 256 = true := by
  have h0 := levelNine_chunk_0
  have h16 := Entries.checkRange_append levelNine _ 0 16 16 h0 levelNine_chunk_16
  have h32 := Entries.checkRange_append levelNine _ 0 32 16 h16 levelNine_chunk_32
  have h48 := Entries.checkRange_append levelNine _ 0 48 16 h32 levelNine_chunk_48
  have h64 := Entries.checkRange_append levelNine _ 0 64 16 h48 levelNine_chunk_64
  have h80 := Entries.checkRange_append levelNine _ 0 80 16 h64 levelNine_chunk_80
  have h96 := Entries.checkRange_append levelNine _ 0 96 16 h80 levelNine_chunk_96
  have h112 := Entries.checkRange_append levelNine _ 0 112 16 h96 levelNine_chunk_112
  have h128 := Entries.checkRange_append levelNine _ 0 128 16 h112 levelNine_chunk_128
  have h144 := Entries.checkRange_append levelNine _ 0 144 16 h128 levelNine_chunk_144
  have h160 := Entries.checkRange_append levelNine _ 0 160 16 h144 levelNine_chunk_160
  have h176 := Entries.checkRange_append levelNine _ 0 176 16 h160 levelNine_chunk_176
  have h192 := Entries.checkRange_append levelNine _ 0 192 16 h176 levelNine_chunk_192
  have h208 := Entries.checkRange_append levelNine _ 0 208 16 h192 levelNine_chunk_208
  have h224 := Entries.checkRange_append levelNine _ 0 224 16 h208 levelNine_chunk_224
  have h240 := Entries.checkRange_append levelNine _ 0 240 16 h224 levelNine_chunk_240
  exact h240
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_1 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 256 256 = true := by
  have h0 := levelNine_chunk_256
  have h272 := Entries.checkRange_append levelNine _ 256 16 16 h0 levelNine_chunk_272
  have h288 := Entries.checkRange_append levelNine _ 256 32 16 h272 levelNine_chunk_288
  have h304 := Entries.checkRange_append levelNine _ 256 48 16 h288 levelNine_chunk_304
  have h320 := Entries.checkRange_append levelNine _ 256 64 16 h304 levelNine_chunk_320
  have h336 := Entries.checkRange_append levelNine _ 256 80 16 h320 levelNine_chunk_336
  have h352 := Entries.checkRange_append levelNine _ 256 96 16 h336 levelNine_chunk_352
  have h368 := Entries.checkRange_append levelNine _ 256 112 16 h352 levelNine_chunk_368
  have h384 := Entries.checkRange_append levelNine _ 256 128 16 h368 levelNine_chunk_384
  have h400 := Entries.checkRange_append levelNine _ 256 144 16 h384 levelNine_chunk_400
  have h416 := Entries.checkRange_append levelNine _ 256 160 16 h400 levelNine_chunk_416
  have h432 := Entries.checkRange_append levelNine _ 256 176 16 h416 levelNine_chunk_432
  have h448 := Entries.checkRange_append levelNine _ 256 192 16 h432 levelNine_chunk_448
  have h464 := Entries.checkRange_append levelNine _ 256 208 16 h448 levelNine_chunk_464
  have h480 := Entries.checkRange_append levelNine _ 256 224 16 h464 levelNine_chunk_480
  have h496 := Entries.checkRange_append levelNine _ 256 240 16 h480 levelNine_chunk_496
  exact h496
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_2 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 512 256 = true := by
  have h0 := levelNine_chunk_512
  have h528 := Entries.checkRange_append levelNine _ 512 16 16 h0 levelNine_chunk_528
  have h544 := Entries.checkRange_append levelNine _ 512 32 16 h528 levelNine_chunk_544
  have h560 := Entries.checkRange_append levelNine _ 512 48 16 h544 levelNine_chunk_560
  have h576 := Entries.checkRange_append levelNine _ 512 64 16 h560 levelNine_chunk_576
  have h592 := Entries.checkRange_append levelNine _ 512 80 16 h576 levelNine_chunk_592
  have h608 := Entries.checkRange_append levelNine _ 512 96 16 h592 levelNine_chunk_608
  have h624 := Entries.checkRange_append levelNine _ 512 112 16 h608 levelNine_chunk_624
  have h640 := Entries.checkRange_append levelNine _ 512 128 16 h624 levelNine_chunk_640
  have h656 := Entries.checkRange_append levelNine _ 512 144 16 h640 levelNine_chunk_656
  have h672 := Entries.checkRange_append levelNine _ 512 160 16 h656 levelNine_chunk_672
  have h688 := Entries.checkRange_append levelNine _ 512 176 16 h672 levelNine_chunk_688
  have h704 := Entries.checkRange_append levelNine _ 512 192 16 h688 levelNine_chunk_704
  have h720 := Entries.checkRange_append levelNine _ 512 208 16 h704 levelNine_chunk_720
  have h736 := Entries.checkRange_append levelNine _ 512 224 16 h720 levelNine_chunk_736
  have h752 := Entries.checkRange_append levelNine _ 512 240 16 h736 levelNine_chunk_752
  exact h752
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_3 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 768 256 = true := by
  have h0 := levelNine_chunk_768
  have h784 := Entries.checkRange_append levelNine _ 768 16 16 h0 levelNine_chunk_784
  have h800 := Entries.checkRange_append levelNine _ 768 32 16 h784 levelNine_chunk_800
  have h816 := Entries.checkRange_append levelNine _ 768 48 16 h800 levelNine_chunk_816
  have h832 := Entries.checkRange_append levelNine _ 768 64 16 h816 levelNine_chunk_832
  have h848 := Entries.checkRange_append levelNine _ 768 80 16 h832 levelNine_chunk_848
  have h864 := Entries.checkRange_append levelNine _ 768 96 16 h848 levelNine_chunk_864
  have h880 := Entries.checkRange_append levelNine _ 768 112 16 h864 levelNine_chunk_880
  have h896 := Entries.checkRange_append levelNine _ 768 128 16 h880 levelNine_chunk_896
  have h912 := Entries.checkRange_append levelNine _ 768 144 16 h896 levelNine_chunk_912
  have h928 := Entries.checkRange_append levelNine _ 768 160 16 h912 levelNine_chunk_928
  have h944 := Entries.checkRange_append levelNine _ 768 176 16 h928 levelNine_chunk_944
  have h960 := Entries.checkRange_append levelNine _ 768 192 16 h944 levelNine_chunk_960
  have h976 := Entries.checkRange_append levelNine _ 768 208 16 h960 levelNine_chunk_976
  have h992 := Entries.checkRange_append levelNine _ 768 224 16 h976 levelNine_chunk_992
  have h1008 := Entries.checkRange_append levelNine _ 768 240 16 h992 levelNine_chunk_1008
  exact h1008
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_4 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 1024 256 = true := by
  have h0 := levelNine_chunk_1024
  have h1040 := Entries.checkRange_append levelNine _ 1024 16 16 h0 levelNine_chunk_1040
  have h1056 := Entries.checkRange_append levelNine _ 1024 32 16 h1040 levelNine_chunk_1056
  have h1072 := Entries.checkRange_append levelNine _ 1024 48 16 h1056 levelNine_chunk_1072
  have h1088 := Entries.checkRange_append levelNine _ 1024 64 16 h1072 levelNine_chunk_1088
  have h1104 := Entries.checkRange_append levelNine _ 1024 80 16 h1088 levelNine_chunk_1104
  have h1120 := Entries.checkRange_append levelNine _ 1024 96 16 h1104 levelNine_chunk_1120
  have h1136 := Entries.checkRange_append levelNine _ 1024 112 16 h1120 levelNine_chunk_1136
  have h1152 := Entries.checkRange_append levelNine _ 1024 128 16 h1136 levelNine_chunk_1152
  have h1168 := Entries.checkRange_append levelNine _ 1024 144 16 h1152 levelNine_chunk_1168
  have h1184 := Entries.checkRange_append levelNine _ 1024 160 16 h1168 levelNine_chunk_1184
  have h1200 := Entries.checkRange_append levelNine _ 1024 176 16 h1184 levelNine_chunk_1200
  have h1216 := Entries.checkRange_append levelNine _ 1024 192 16 h1200 levelNine_chunk_1216
  have h1232 := Entries.checkRange_append levelNine _ 1024 208 16 h1216 levelNine_chunk_1232
  have h1248 := Entries.checkRange_append levelNine _ 1024 224 16 h1232 levelNine_chunk_1248
  have h1264 := Entries.checkRange_append levelNine _ 1024 240 16 h1248 levelNine_chunk_1264
  exact h1264
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_5 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 1280 256 = true := by
  have h0 := levelNine_chunk_1280
  have h1296 := Entries.checkRange_append levelNine _ 1280 16 16 h0 levelNine_chunk_1296
  have h1312 := Entries.checkRange_append levelNine _ 1280 32 16 h1296 levelNine_chunk_1312
  have h1328 := Entries.checkRange_append levelNine _ 1280 48 16 h1312 levelNine_chunk_1328
  have h1344 := Entries.checkRange_append levelNine _ 1280 64 16 h1328 levelNine_chunk_1344
  have h1360 := Entries.checkRange_append levelNine _ 1280 80 16 h1344 levelNine_chunk_1360
  have h1376 := Entries.checkRange_append levelNine _ 1280 96 16 h1360 levelNine_chunk_1376
  have h1392 := Entries.checkRange_append levelNine _ 1280 112 16 h1376 levelNine_chunk_1392
  have h1408 := Entries.checkRange_append levelNine _ 1280 128 16 h1392 levelNine_chunk_1408
  have h1424 := Entries.checkRange_append levelNine _ 1280 144 16 h1408 levelNine_chunk_1424
  have h1440 := Entries.checkRange_append levelNine _ 1280 160 16 h1424 levelNine_chunk_1440
  have h1456 := Entries.checkRange_append levelNine _ 1280 176 16 h1440 levelNine_chunk_1456
  have h1472 := Entries.checkRange_append levelNine _ 1280 192 16 h1456 levelNine_chunk_1472
  have h1488 := Entries.checkRange_append levelNine _ 1280 208 16 h1472 levelNine_chunk_1488
  have h1504 := Entries.checkRange_append levelNine _ 1280 224 16 h1488 levelNine_chunk_1504
  have h1520 := Entries.checkRange_append levelNine _ 1280 240 16 h1504 levelNine_chunk_1520
  exact h1520
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_6 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 1536 256 = true := by
  have h0 := levelNine_chunk_1536
  have h1552 := Entries.checkRange_append levelNine _ 1536 16 16 h0 levelNine_chunk_1552
  have h1568 := Entries.checkRange_append levelNine _ 1536 32 16 h1552 levelNine_chunk_1568
  have h1584 := Entries.checkRange_append levelNine _ 1536 48 16 h1568 levelNine_chunk_1584
  have h1600 := Entries.checkRange_append levelNine _ 1536 64 16 h1584 levelNine_chunk_1600
  have h1616 := Entries.checkRange_append levelNine _ 1536 80 16 h1600 levelNine_chunk_1616
  have h1632 := Entries.checkRange_append levelNine _ 1536 96 16 h1616 levelNine_chunk_1632
  have h1648 := Entries.checkRange_append levelNine _ 1536 112 16 h1632 levelNine_chunk_1648
  have h1664 := Entries.checkRange_append levelNine _ 1536 128 16 h1648 levelNine_chunk_1664
  have h1680 := Entries.checkRange_append levelNine _ 1536 144 16 h1664 levelNine_chunk_1680
  have h1696 := Entries.checkRange_append levelNine _ 1536 160 16 h1680 levelNine_chunk_1696
  have h1712 := Entries.checkRange_append levelNine _ 1536 176 16 h1696 levelNine_chunk_1712
  have h1728 := Entries.checkRange_append levelNine _ 1536 192 16 h1712 levelNine_chunk_1728
  have h1744 := Entries.checkRange_append levelNine _ 1536 208 16 h1728 levelNine_chunk_1744
  have h1760 := Entries.checkRange_append levelNine _ 1536 224 16 h1744 levelNine_chunk_1760
  have h1776 := Entries.checkRange_append levelNine _ 1536 240 16 h1760 levelNine_chunk_1776
  exact h1776
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_7 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 1792 256 = true := by
  have h0 := levelNine_chunk_1792
  have h1808 := Entries.checkRange_append levelNine _ 1792 16 16 h0 levelNine_chunk_1808
  have h1824 := Entries.checkRange_append levelNine _ 1792 32 16 h1808 levelNine_chunk_1824
  have h1840 := Entries.checkRange_append levelNine _ 1792 48 16 h1824 levelNine_chunk_1840
  have h1856 := Entries.checkRange_append levelNine _ 1792 64 16 h1840 levelNine_chunk_1856
  have h1872 := Entries.checkRange_append levelNine _ 1792 80 16 h1856 levelNine_chunk_1872
  have h1888 := Entries.checkRange_append levelNine _ 1792 96 16 h1872 levelNine_chunk_1888
  have h1904 := Entries.checkRange_append levelNine _ 1792 112 16 h1888 levelNine_chunk_1904
  have h1920 := Entries.checkRange_append levelNine _ 1792 128 16 h1904 levelNine_chunk_1920
  have h1936 := Entries.checkRange_append levelNine _ 1792 144 16 h1920 levelNine_chunk_1936
  have h1952 := Entries.checkRange_append levelNine _ 1792 160 16 h1936 levelNine_chunk_1952
  have h1968 := Entries.checkRange_append levelNine _ 1792 176 16 h1952 levelNine_chunk_1968
  have h1984 := Entries.checkRange_append levelNine _ 1792 192 16 h1968 levelNine_chunk_1984
  have h2000 := Entries.checkRange_append levelNine _ 1792 208 16 h1984 levelNine_chunk_2000
  have h2016 := Entries.checkRange_append levelNine _ 1792 224 16 h2000 levelNine_chunk_2016
  have h2032 := Entries.checkRange_append levelNine _ 1792 240 16 h2016 levelNine_chunk_2032
  exact h2032
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_group_0 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 0 2048 = true := by
  have h0 := levelNine_block_0
  have h1 := Entries.checkRange_append levelNine _ 0 256 256 h0 levelNine_block_1
  have h2 := Entries.checkRange_append levelNine _ 0 512 256 h1 levelNine_block_2
  have h3 := Entries.checkRange_append levelNine _ 0 768 256 h2 levelNine_block_3
  have h4 := Entries.checkRange_append levelNine _ 0 1024 256 h3 levelNine_block_4
  have h5 := Entries.checkRange_append levelNine _ 0 1280 256 h4 levelNine_block_5
  have h6 := Entries.checkRange_append levelNine _ 0 1536 256 h5 levelNine_block_6
  have h7 := Entries.checkRange_append levelNine _ 0 1792 256 h6 levelNine_block_7
  exact h7
end WordCertDensity.Certificates
