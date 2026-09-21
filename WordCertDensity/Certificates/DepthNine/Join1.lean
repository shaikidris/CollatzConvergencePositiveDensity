/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module
public import WordCertDensity.Certificates.DepthNine.Transfer8
public import WordCertDensity.Certificates.DepthNine.Transfer9
public import WordCertDensity.Certificates.DepthNine.Transfer10
public import WordCertDensity.Certificates.DepthNine.Transfer11
public import WordCertDensity.Certificates.DepthNine.Transfer12
public import WordCertDensity.Certificates.DepthNine.Transfer13
public import WordCertDensity.Certificates.DepthNine.Transfer14
public import WordCertDensity.Certificates.DepthNine.Transfer15
/-! # Depth-nine integer certificate component -/

@[expose] public section
namespace WordCertDensity.Certificates
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_8 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 2048 256 = true := by
  have h0 := levelNine_chunk_2048
  have h2064 := Entries.checkRange_append levelNine _ 2048 16 16 h0 levelNine_chunk_2064
  have h2080 := Entries.checkRange_append levelNine _ 2048 32 16 h2064 levelNine_chunk_2080
  have h2096 := Entries.checkRange_append levelNine _ 2048 48 16 h2080 levelNine_chunk_2096
  have h2112 := Entries.checkRange_append levelNine _ 2048 64 16 h2096 levelNine_chunk_2112
  have h2128 := Entries.checkRange_append levelNine _ 2048 80 16 h2112 levelNine_chunk_2128
  have h2144 := Entries.checkRange_append levelNine _ 2048 96 16 h2128 levelNine_chunk_2144
  have h2160 := Entries.checkRange_append levelNine _ 2048 112 16 h2144 levelNine_chunk_2160
  have h2176 := Entries.checkRange_append levelNine _ 2048 128 16 h2160 levelNine_chunk_2176
  have h2192 := Entries.checkRange_append levelNine _ 2048 144 16 h2176 levelNine_chunk_2192
  have h2208 := Entries.checkRange_append levelNine _ 2048 160 16 h2192 levelNine_chunk_2208
  have h2224 := Entries.checkRange_append levelNine _ 2048 176 16 h2208 levelNine_chunk_2224
  have h2240 := Entries.checkRange_append levelNine _ 2048 192 16 h2224 levelNine_chunk_2240
  have h2256 := Entries.checkRange_append levelNine _ 2048 208 16 h2240 levelNine_chunk_2256
  have h2272 := Entries.checkRange_append levelNine _ 2048 224 16 h2256 levelNine_chunk_2272
  have h2288 := Entries.checkRange_append levelNine _ 2048 240 16 h2272 levelNine_chunk_2288
  exact h2288
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_9 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 2304 256 = true := by
  have h0 := levelNine_chunk_2304
  have h2320 := Entries.checkRange_append levelNine _ 2304 16 16 h0 levelNine_chunk_2320
  have h2336 := Entries.checkRange_append levelNine _ 2304 32 16 h2320 levelNine_chunk_2336
  have h2352 := Entries.checkRange_append levelNine _ 2304 48 16 h2336 levelNine_chunk_2352
  have h2368 := Entries.checkRange_append levelNine _ 2304 64 16 h2352 levelNine_chunk_2368
  have h2384 := Entries.checkRange_append levelNine _ 2304 80 16 h2368 levelNine_chunk_2384
  have h2400 := Entries.checkRange_append levelNine _ 2304 96 16 h2384 levelNine_chunk_2400
  have h2416 := Entries.checkRange_append levelNine _ 2304 112 16 h2400 levelNine_chunk_2416
  have h2432 := Entries.checkRange_append levelNine _ 2304 128 16 h2416 levelNine_chunk_2432
  have h2448 := Entries.checkRange_append levelNine _ 2304 144 16 h2432 levelNine_chunk_2448
  have h2464 := Entries.checkRange_append levelNine _ 2304 160 16 h2448 levelNine_chunk_2464
  have h2480 := Entries.checkRange_append levelNine _ 2304 176 16 h2464 levelNine_chunk_2480
  have h2496 := Entries.checkRange_append levelNine _ 2304 192 16 h2480 levelNine_chunk_2496
  have h2512 := Entries.checkRange_append levelNine _ 2304 208 16 h2496 levelNine_chunk_2512
  have h2528 := Entries.checkRange_append levelNine _ 2304 224 16 h2512 levelNine_chunk_2528
  have h2544 := Entries.checkRange_append levelNine _ 2304 240 16 h2528 levelNine_chunk_2544
  exact h2544
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_10 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 2560 256 = true := by
  have h0 := levelNine_chunk_2560
  have h2576 := Entries.checkRange_append levelNine _ 2560 16 16 h0 levelNine_chunk_2576
  have h2592 := Entries.checkRange_append levelNine _ 2560 32 16 h2576 levelNine_chunk_2592
  have h2608 := Entries.checkRange_append levelNine _ 2560 48 16 h2592 levelNine_chunk_2608
  have h2624 := Entries.checkRange_append levelNine _ 2560 64 16 h2608 levelNine_chunk_2624
  have h2640 := Entries.checkRange_append levelNine _ 2560 80 16 h2624 levelNine_chunk_2640
  have h2656 := Entries.checkRange_append levelNine _ 2560 96 16 h2640 levelNine_chunk_2656
  have h2672 := Entries.checkRange_append levelNine _ 2560 112 16 h2656 levelNine_chunk_2672
  have h2688 := Entries.checkRange_append levelNine _ 2560 128 16 h2672 levelNine_chunk_2688
  have h2704 := Entries.checkRange_append levelNine _ 2560 144 16 h2688 levelNine_chunk_2704
  have h2720 := Entries.checkRange_append levelNine _ 2560 160 16 h2704 levelNine_chunk_2720
  have h2736 := Entries.checkRange_append levelNine _ 2560 176 16 h2720 levelNine_chunk_2736
  have h2752 := Entries.checkRange_append levelNine _ 2560 192 16 h2736 levelNine_chunk_2752
  have h2768 := Entries.checkRange_append levelNine _ 2560 208 16 h2752 levelNine_chunk_2768
  have h2784 := Entries.checkRange_append levelNine _ 2560 224 16 h2768 levelNine_chunk_2784
  have h2800 := Entries.checkRange_append levelNine _ 2560 240 16 h2784 levelNine_chunk_2800
  exact h2800
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_11 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 2816 256 = true := by
  have h0 := levelNine_chunk_2816
  have h2832 := Entries.checkRange_append levelNine _ 2816 16 16 h0 levelNine_chunk_2832
  have h2848 := Entries.checkRange_append levelNine _ 2816 32 16 h2832 levelNine_chunk_2848
  have h2864 := Entries.checkRange_append levelNine _ 2816 48 16 h2848 levelNine_chunk_2864
  have h2880 := Entries.checkRange_append levelNine _ 2816 64 16 h2864 levelNine_chunk_2880
  have h2896 := Entries.checkRange_append levelNine _ 2816 80 16 h2880 levelNine_chunk_2896
  have h2912 := Entries.checkRange_append levelNine _ 2816 96 16 h2896 levelNine_chunk_2912
  have h2928 := Entries.checkRange_append levelNine _ 2816 112 16 h2912 levelNine_chunk_2928
  have h2944 := Entries.checkRange_append levelNine _ 2816 128 16 h2928 levelNine_chunk_2944
  have h2960 := Entries.checkRange_append levelNine _ 2816 144 16 h2944 levelNine_chunk_2960
  have h2976 := Entries.checkRange_append levelNine _ 2816 160 16 h2960 levelNine_chunk_2976
  have h2992 := Entries.checkRange_append levelNine _ 2816 176 16 h2976 levelNine_chunk_2992
  have h3008 := Entries.checkRange_append levelNine _ 2816 192 16 h2992 levelNine_chunk_3008
  have h3024 := Entries.checkRange_append levelNine _ 2816 208 16 h3008 levelNine_chunk_3024
  have h3040 := Entries.checkRange_append levelNine _ 2816 224 16 h3024 levelNine_chunk_3040
  have h3056 := Entries.checkRange_append levelNine _ 2816 240 16 h3040 levelNine_chunk_3056
  exact h3056
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_12 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 3072 256 = true := by
  have h0 := levelNine_chunk_3072
  have h3088 := Entries.checkRange_append levelNine _ 3072 16 16 h0 levelNine_chunk_3088
  have h3104 := Entries.checkRange_append levelNine _ 3072 32 16 h3088 levelNine_chunk_3104
  have h3120 := Entries.checkRange_append levelNine _ 3072 48 16 h3104 levelNine_chunk_3120
  have h3136 := Entries.checkRange_append levelNine _ 3072 64 16 h3120 levelNine_chunk_3136
  have h3152 := Entries.checkRange_append levelNine _ 3072 80 16 h3136 levelNine_chunk_3152
  have h3168 := Entries.checkRange_append levelNine _ 3072 96 16 h3152 levelNine_chunk_3168
  have h3184 := Entries.checkRange_append levelNine _ 3072 112 16 h3168 levelNine_chunk_3184
  have h3200 := Entries.checkRange_append levelNine _ 3072 128 16 h3184 levelNine_chunk_3200
  have h3216 := Entries.checkRange_append levelNine _ 3072 144 16 h3200 levelNine_chunk_3216
  have h3232 := Entries.checkRange_append levelNine _ 3072 160 16 h3216 levelNine_chunk_3232
  have h3248 := Entries.checkRange_append levelNine _ 3072 176 16 h3232 levelNine_chunk_3248
  have h3264 := Entries.checkRange_append levelNine _ 3072 192 16 h3248 levelNine_chunk_3264
  have h3280 := Entries.checkRange_append levelNine _ 3072 208 16 h3264 levelNine_chunk_3280
  have h3296 := Entries.checkRange_append levelNine _ 3072 224 16 h3280 levelNine_chunk_3296
  have h3312 := Entries.checkRange_append levelNine _ 3072 240 16 h3296 levelNine_chunk_3312
  exact h3312
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_13 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 3328 256 = true := by
  have h0 := levelNine_chunk_3328
  have h3344 := Entries.checkRange_append levelNine _ 3328 16 16 h0 levelNine_chunk_3344
  have h3360 := Entries.checkRange_append levelNine _ 3328 32 16 h3344 levelNine_chunk_3360
  have h3376 := Entries.checkRange_append levelNine _ 3328 48 16 h3360 levelNine_chunk_3376
  have h3392 := Entries.checkRange_append levelNine _ 3328 64 16 h3376 levelNine_chunk_3392
  have h3408 := Entries.checkRange_append levelNine _ 3328 80 16 h3392 levelNine_chunk_3408
  have h3424 := Entries.checkRange_append levelNine _ 3328 96 16 h3408 levelNine_chunk_3424
  have h3440 := Entries.checkRange_append levelNine _ 3328 112 16 h3424 levelNine_chunk_3440
  have h3456 := Entries.checkRange_append levelNine _ 3328 128 16 h3440 levelNine_chunk_3456
  have h3472 := Entries.checkRange_append levelNine _ 3328 144 16 h3456 levelNine_chunk_3472
  have h3488 := Entries.checkRange_append levelNine _ 3328 160 16 h3472 levelNine_chunk_3488
  have h3504 := Entries.checkRange_append levelNine _ 3328 176 16 h3488 levelNine_chunk_3504
  have h3520 := Entries.checkRange_append levelNine _ 3328 192 16 h3504 levelNine_chunk_3520
  have h3536 := Entries.checkRange_append levelNine _ 3328 208 16 h3520 levelNine_chunk_3536
  have h3552 := Entries.checkRange_append levelNine _ 3328 224 16 h3536 levelNine_chunk_3552
  have h3568 := Entries.checkRange_append levelNine _ 3328 240 16 h3552 levelNine_chunk_3568
  exact h3568
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_14 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 3584 256 = true := by
  have h0 := levelNine_chunk_3584
  have h3600 := Entries.checkRange_append levelNine _ 3584 16 16 h0 levelNine_chunk_3600
  have h3616 := Entries.checkRange_append levelNine _ 3584 32 16 h3600 levelNine_chunk_3616
  have h3632 := Entries.checkRange_append levelNine _ 3584 48 16 h3616 levelNine_chunk_3632
  have h3648 := Entries.checkRange_append levelNine _ 3584 64 16 h3632 levelNine_chunk_3648
  have h3664 := Entries.checkRange_append levelNine _ 3584 80 16 h3648 levelNine_chunk_3664
  have h3680 := Entries.checkRange_append levelNine _ 3584 96 16 h3664 levelNine_chunk_3680
  have h3696 := Entries.checkRange_append levelNine _ 3584 112 16 h3680 levelNine_chunk_3696
  have h3712 := Entries.checkRange_append levelNine _ 3584 128 16 h3696 levelNine_chunk_3712
  have h3728 := Entries.checkRange_append levelNine _ 3584 144 16 h3712 levelNine_chunk_3728
  have h3744 := Entries.checkRange_append levelNine _ 3584 160 16 h3728 levelNine_chunk_3744
  have h3760 := Entries.checkRange_append levelNine _ 3584 176 16 h3744 levelNine_chunk_3760
  have h3776 := Entries.checkRange_append levelNine _ 3584 192 16 h3760 levelNine_chunk_3776
  have h3792 := Entries.checkRange_append levelNine _ 3584 208 16 h3776 levelNine_chunk_3792
  have h3808 := Entries.checkRange_append levelNine _ 3584 224 16 h3792 levelNine_chunk_3808
  have h3824 := Entries.checkRange_append levelNine _ 3584 240 16 h3808 levelNine_chunk_3824
  exact h3824
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_block_15 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 3840 256 = true := by
  have h0 := levelNine_chunk_3840
  have h3856 := Entries.checkRange_append levelNine _ 3840 16 16 h0 levelNine_chunk_3856
  have h3872 := Entries.checkRange_append levelNine _ 3840 32 16 h3856 levelNine_chunk_3872
  have h3888 := Entries.checkRange_append levelNine _ 3840 48 16 h3872 levelNine_chunk_3888
  have h3904 := Entries.checkRange_append levelNine _ 3840 64 16 h3888 levelNine_chunk_3904
  have h3920 := Entries.checkRange_append levelNine _ 3840 80 16 h3904 levelNine_chunk_3920
  have h3936 := Entries.checkRange_append levelNine _ 3840 96 16 h3920 levelNine_chunk_3936
  have h3952 := Entries.checkRange_append levelNine _ 3840 112 16 h3936 levelNine_chunk_3952
  have h3968 := Entries.checkRange_append levelNine _ 3840 128 16 h3952 levelNine_chunk_3968
  have h3984 := Entries.checkRange_append levelNine _ 3840 144 16 h3968 levelNine_chunk_3984
  have h4000 := Entries.checkRange_append levelNine _ 3840 160 16 h3984 levelNine_chunk_4000
  have h4016 := Entries.checkRange_append levelNine _ 3840 176 16 h4000 levelNine_chunk_4016
  have h4032 := Entries.checkRange_append levelNine _ 3840 192 16 h4016 levelNine_chunk_4032
  have h4048 := Entries.checkRange_append levelNine _ 3840 208 16 h4032 levelNine_chunk_4048
  have h4064 := Entries.checkRange_append levelNine _ 3840 224 16 h4048 levelNine_chunk_4064
  have h4080 := Entries.checkRange_append levelNine _ 3840 240 16 h4064 levelNine_chunk_4080
  exact h4080
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_group_1 : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 2048 2048 = true := by
  have h0 := levelNine_block_8
  have h9 := Entries.checkRange_append levelNine _ 2048 256 256 h0 levelNine_block_9
  have h10 := Entries.checkRange_append levelNine _ 2048 512 256 h9 levelNine_block_10
  have h11 := Entries.checkRange_append levelNine _ 2048 768 256 h10 levelNine_block_11
  have h12 := Entries.checkRange_append levelNine _ 2048 1024 256 h11 levelNine_block_12
  have h13 := Entries.checkRange_append levelNine _ 2048 1280 256 h12 levelNine_block_13
  have h14 := Entries.checkRange_append levelNine _ 2048 1536 256 h13 levelNine_block_14
  have h15 := Entries.checkRange_append levelNine _ 2048 1792 256 h14 levelNine_block_15
  exact h15
end WordCertDensity.Certificates
