/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.Data.Summaries
public import WordCertDensity.Certificates.Data.LevelFour

/-! # Complete depth-5 integer certificate -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Complete enclosure tree, with one leaf per residue. -/
def levelFive : Entries :=
  (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 532252236622997)) (.node (.leaf 266126118311499) (.leaf 0))) (.node (.node (.leaf 133063059791167) (.leaf 51801238537933)) (.node (.leaf 0) (.leaf 266553670927248)))) (.node (.node (.node (.leaf 66531529895584) (.leaf 0)) (.node (.leaf 751983124503334) (.leaf 195116031558205))) (.node (.node (.leaf 0) (.leaf 137034943580030)) (.node (.leaf 133276835463624) (.leaf 0))))) (.node (.node (.node (.node (.leaf 604790507648282) (.leaf 191896542267725)) (.node (.leaf 0) (.leaf 300032396600497))) (.node (.node (.leaf 375991562251667) (.leaf 0)) (.node (.leaf 97558016338318) (.leaf 103345231563430)))) (.node (.node (.node (.leaf 0) (.leaf 2320027308386575)) (.node (.leaf 68517471790015) (.leaf 0))) (.node (.node (.leaf 719877579142691) (.leaf 414152016243668)) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 302395253824141) (.leaf 0)) (.node (.leaf 95948271825592) (.leaf 38903192104133))) (.node (.node (.leaf 0) (.leaf 686047837917074)) (.node (.leaf 150016198300249) (.leaf 0)))) (.node (.node (.node (.leaf 1328284823320262) (.leaf 157380827559685)) (.node (.leaf 0) (.leaf 98525885865090))) (.node (.node (.leaf 48779008169159) (.leaf 0)) (.leaf 176086722148531)))) (.node (.node (.node (.node (.leaf 0) (.leaf 127734334517617)) (.node (.leaf 1160013654193288) (.leaf 0))) (.node (.node (.leaf 523741856053630) (.leaf 468493439746184)) (.node (.leaf 0) (.leaf 1275257461036641)))) (.node (.node (.node (.leaf 359938789571346) (.leaf 0)) (.node (.leaf 304989969452350) (.leaf 124794647114071))) (.node (.node (.leaf 0) (.leaf 1353178161176197)) (.leaf 166035603200096)))))) (.node (.node (.node (.node (.node (.node (.leaf 542853468963060) (.leaf 257295068522582)) (.node (.leaf 0) (.leaf 141702283183330))) (.node (.node (.leaf 47974135912796) (.leaf 0)) (.node (.leaf 517108016864938) (.leaf 362419378723688)))) (.node (.node (.node (.leaf 0) (.leaf 243270762605919)) (.node (.leaf 343023918958537) (.leaf 0))) (.node (.node (.leaf 75008099507388) (.leaf 90604845009218)) (.node (.leaf 0) (.leaf 3089969650018044))))) (.node (.node (.node (.node (.leaf 664142411660131) (.leaf 0)) (.node (.leaf 510937335637020) (.leaf 1147891253301975))) (.node (.node (.leaf 0) (.leaf 263413087263234)) (.node (.leaf 49262942932545) (.leaf 0)))) (.node (.node (.node (.leaf 888883347228807) (.leaf 207204952829089)) (.node (.leaf 0) (.leaf 548139771541123))) (.node (.node (.leaf 88043361074266) (.leaf 0)) (.leaf 135713367888758))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 638814823851845)) (.node (.leaf 63867167258809) (.leaf 0))) (.node (.node (.leaf 664949678685481) (.leaf 185961002082247)) (.node (.leaf 0) (.leaf 70986906368025)))) (.node (.node (.node (.leaf 261870928026815) (.leaf 0)) (.node (.leaf 234246720496429) (.leaf 35748013516974))) (.node (.node (.leaf 0) (.leaf 2306926232265558)) (.leaf 637628730518321)))) (.node (.node (.node (.node (.leaf 179969395485716) (.leaf 85755980077886)) (.node (.leaf 0) (.leaf 1316186689121535))) (.node (.node (.leaf 152494984726175) (.leaf 0)) (.node (.leaf 311225534031934) (.leaf 663792975861359)))) (.node (.node (.node (.leaf 0) (.leaf 60817691293822)) (.node (.leaf 676589080588099) (.leaf 0))) (.node (.node (.leaf 278845723681656) (.leaf 606380457136271)) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 271426734481530) (.leaf 0)) (.node (.leaf 414409905658177) (.leaf 184329482147064))) (.node (.node (.leaf 0) (.leaf 2295782506603950)) (.node (.leaf 70851141591665) (.leaf 0)))) (.node (.node (.node (.leaf 514590137045163) (.leaf 283404565051834)) (.node (.leaf 0) (.leaf 724838757447375))) (.node (.node (.leaf 258554008432469) (.leaf 0)) (.node (.leaf 181209690018436) (.leaf 42204022116767))))) (.node (.node (.node (.node (.leaf 0) (.leaf 1212760914272541)) (.node (.leaf 121635381302960) (.leaf 0))) (.node (.node (.leaf 171511960155772) (.leaf 151595114634192)) (.node (.leaf 0) (.leaf 1327585951722718)))) (.node (.node (.node (.leaf 37504049753694) (.leaf 0)) (.node (.leaf 371922004164493) (.leaf 141973811379196))) (.node (.node (.leaf 0) (.leaf 71496027033947)) (.leaf 1544984825009022))))) (.node (.node (.node (.node (.node (.leaf 332071206400192) (.leaf 38123746488487)) (.node (.leaf 0) (.leaf 249589294228142))) (.node (.node (.leaf 255468667818510) (.leaf 0)) (.node (.leaf 936986879492367) (.leaf 249294266995963)))) (.node (.node (.node (.leaf 0) (.leaf 77806384208265)) (.node (.leaf 131706543631617) (.leaf 0))) (.node (.node (.leaf 314761655119370) (.leaf 197051770470181)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 444441673614404) (.leaf 0)) (.node (.leaf 103602477075866) (.leaf 288365779361967))) (.node (.node (.leaf 0) (.leaf 390232063116410)) (.node (.leaf 274069885770562) (.leaf 0)))) (.node (.node (.node (.leaf 383793084535450) (.leaf 477414025662073)) (.node (.leaf 0) (.leaf 206690463126860))) (.node (.node (.leaf 67856683944379) (.leaf 0)) (.leaf 828304032487336)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 166237420120403)) (.node (.leaf 319407411925923) (.leaf 0))) (.node (.node (.leaf 154584351882851) (.leaf 168861030680915)) (.node (.leaf 0) (.leaf 337632174211129)))) (.node (.node (.node (.leaf 332474839342741) (.leaf 0)) (.node (.leaf 337722061361829) (.leaf 348644767119436))) (.node (.node (.leaf 0) (.leaf 697289534238871)) (.leaf 35493453184013)))) (.node (.node (.node (.node (.leaf 285984106349270) (.leaf 77292175941426)) (.node (.leaf 0) (.leaf 84430516028443))) (.node (.node (.leaf 117123360248215) (.leaf 0)) (.node (.leaf 2319094661212467) (.leaf 168816087105565)))) (.node (.node (.node (.leaf 0) (.leaf 826761850257710)) (.node (.leaf 1153463116132779) (.leaf 0))) (.node (.node (.leaf 318814365707550) (.leaf 83118710060202)) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 89984697742858) (.leaf 0)) (.node (.leaf 954828051324145) (.leaf 413380925128855))) (.node (.node (.leaf 0) (.leaf 576731558723933)) (.node (.leaf 658093344560768) (.leaf 0)))) (.node (.node (.node (.leaf 76247492976974) (.leaf 159407182853775)) (.node (.leaf 0) (.leaf 498588533991925))) (.node (.node (.leaf 155612767015967) (.leaf 0)) (.leaf 394103540940362)))) (.node (.node (.node (.node (.leaf 0) (.leaf 368658964294127)) (.node (.leaf 30408845646911) (.leaf 0))) (.node (.node (.leaf 566809130103668) (.leaf 1159547330606234)) (.node (.leaf 0) (.leaf 84408044233534)))) (.node (.node (.node (.leaf 139422861840828) (.leaf 0)) (.node (.leaf 303190229268384) (.leaf 42215258014222))) (.node (.node (.leaf 0) (.leaf 283947622758392)) (.leaf 142992053174635))))))))

/-- Complete enclosure tree, with one leaf per residue. -/
def levelFiveRoots : Entries :=
  (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 23070593)) (.node (.leaf 16313373) (.leaf 0))) (.node (.node (.leaf 11535297) (.leaf 7197308)) (.node (.leaf 0) (.leaf 16326472)))) (.node (.node (.node (.leaf 8156687) (.leaf 0)) (.node (.leaf 27422311) (.leaf 13968395))) (.node (.node (.leaf 0) (.leaf 11706193)) (.node (.leaf 11544559) (.leaf 0))))) (.node (.node (.node (.node (.leaf 24592489) (.leaf 13852673)) (.node (.leaf 0) (.leaf 17321444))) (.node (.node (.leaf 19390502) (.leaf 0)) (.node (.leaf 9877147) (.leaf 10165886)))) (.node (.node (.node (.leaf 0) (.leaf 48166662)) (.node (.leaf 8277529) (.leaf 0))) (.node (.node (.leaf 26830535) (.leaf 20350726)) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 17389516) (.leaf 0)) (.node (.leaf 9795319) (.leaf 6237243))) (.node (.node (.leaf 0) (.leaf 26192515)) (.node (.leaf 12248110) (.leaf 0)))) (.node (.node (.node (.leaf 36445643) (.leaf 12545152)) (.node (.leaf 0) (.leaf 9926021))) (.node (.node (.leaf 6984198) (.leaf 0)) (.leaf 13269768)))) (.node (.node (.node (.node (.leaf 0) (.leaf 11301962)) (.node (.leaf 34058974) (.leaf 0))) (.node (.node (.leaf 22885408) (.leaf 21644710)) (.node (.leaf 0) (.leaf 35710748)))) (.node (.node (.node (.leaf 18972053) (.leaf 0)) (.node (.leaf 17463963) (.leaf 11171153))) (.node (.node (.leaf 0) (.leaf 36785571)) (.leaf 12885481)))))) (.node (.node (.node (.node (.node (.node (.leaf 23299217) (.leaf 16040420)) (.node (.leaf 0) (.leaf 11903877))) (.node (.node (.leaf 6926337) (.leaf 0)) (.node (.leaf 22740010) (.leaf 19037316)))) (.node (.node (.node (.leaf 0) (.leaf 15597140)) (.node (.leaf 18520905) (.leaf 0))) (.node (.node (.leaf 8660722) (.leaf 9518658)) (.node (.leaf 0) (.leaf 55587496))))) (.node (.node (.node (.node (.leaf 25770961) (.leaf 0)) (.node (.leaf 22603924) (.leaf 33880544))) (.node (.node (.leaf 0) (.leaf 16230006)) (.node (.leaf 7018757) (.leaf 0)))) (.node (.node (.node (.leaf 29814147) (.leaf 14394616)) (.node (.leaf 0) (.leaf 23412386))) (.node (.node (.leaf 9383143) (.leaf 0)) (.leaf 11649609))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 25274787)) (.node (.leaf 7991694) (.leaf 0))) (.node (.node (.leaf 25786619) (.leaf 13636752)) (.node (.leaf 0) (.leaf 8425373)))) (.node (.node (.node (.leaf 16182427) (.leaf 0)) (.node (.leaf 15305121) (.leaf 5978965))) (.node (.node (.leaf 0) (.leaf 48030472)) (.leaf 25251312)))) (.node (.node (.node (.node (.leaf 13415268) (.leaf 9260453)) (.node (.leaf 0) (.leaf 36279288))) (.node (.node (.leaf 12348886) (.leaf 0)) (.node (.leaf 17641586) (.leaf 25764181)))) (.node (.node (.node (.leaf 0) (.leaf 7798570)) (.node (.leaf 26011327) (.leaf 0))) (.node (.node (.leaf 16698675) (.leaf 24624794)) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 16475034) (.leaf 0)) (.node (.leaf 20357061) (.leaf 13576800))) (.node (.node (.leaf 0) (.leaf 47914325)) (.node (.leaf 8417313) (.leaf 0)))) (.node (.node (.node (.leaf 22684580) (.leaf 16834624)) (.node (.leaf 0) (.leaf 26922830))) (.node (.node (.leaf 16079615) (.leaf 0)) (.node (.leaf 13461415) (.leaf 6496463))))) (.node (.node (.node (.node (.leaf 0) (.leaf 34824718)) (.node (.leaf 11028844) (.leaf 0))) (.node (.node (.leaf 13096258) (.leaf 12312397)) (.node (.leaf 0) (.leaf 36436053)))) (.node (.node (.node (.leaf 6124056) (.leaf 0)) (.node (.leaf 19285280) (.leaf 11915277))) (.node (.node (.leaf 0) (.leaf 8455533)) (.leaf 39306295))))) (.node (.node (.node (.node (.node (.leaf 18222822) (.leaf 6174444)) (.node (.leaf 0) (.leaf 15798396))) (.node (.node (.leaf 15983388) (.leaf 0)) (.node (.leaf 30610242) (.leaf 15789056)))) (.node (.node (.node (.leaf 0) (.leaf 8820793)) (.node (.leaf 11476348) (.leaf 0))) (.node (.node (.leaf 17741524) (.leaf 14037513)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 21081786) (.leaf 0)) (.node (.leaf 10178531) (.leaf 16981337))) (.node (.node (.leaf 0) (.leaf 19754293)) (.node (.leaf 16555057) (.leaf 0)))) (.node (.node (.node (.leaf 19590638) (.leaf 21849807)) (.node (.leaf 0) (.leaf 14376734))) (.node (.node (.leaf 8237517) (.leaf 0)) (.leaf 28780272)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 12893310)) (.node (.leaf 17871973) (.leaf 0))) (.node (.node (.leaf 12433196) (.leaf 12994654)) (.node (.leaf 0) (.leaf 18374771)))) (.node (.node (.node (.leaf 18233893) (.leaf 0)) (.node (.leaf 18377216) (.leaf 18672032))) (.node (.node (.leaf 0) (.leaf 26406241)) (.leaf 5957639)))) (.node (.node (.node (.node (.leaf 16911065) (.leaf 8791597)) (.node (.leaf 0) (.leaf 9188608))) (.node (.node (.leaf 10822355) (.leaf 0)) (.node (.leaf 48156980) (.leaf 12992925)))) (.node (.node (.node (.leaf 0) (.leaf 28753467)) (.node (.leaf 33962673) (.leaf 0))) (.node (.node (.leaf 17855374) (.leaf 9116947)) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 9486027) (.leaf 0)) (.node (.leaf 30900293) (.leaf 20331772))) (.node (.node (.leaf 0) (.leaf 24015236)) (.node (.leaf 25653331) (.leaf 0)))) (.node (.node (.node (.leaf 8731982) (.leaf 12625656)) (.node (.leaf 0) (.leaf 22329097))) (.node (.node (.leaf 12474485) (.leaf 0)) (.leaf 19852042)))) (.node (.node (.node (.node (.leaf 0) (.leaf 19200494)) (.node (.leaf 5514422) (.leaf 0))) (.node (.node (.leaf 23807754) (.leaf 34052127)) (.node (.leaf 0) (.leaf 9187386)))) (.node (.node (.node (.leaf 11807746) (.leaf 0)) (.node (.leaf 17412359) (.leaf 6497327))) (.node (.node (.leaf 0) (.leaf 16850746)) (.leaf 11957929))))))))

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_0 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 0 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_16 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 16 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_32 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 32 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_48 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 48 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_64 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 64 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_80 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 80 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_96 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 96 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_112 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 112 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_128 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 128 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_144 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 144 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_160 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 160 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_176 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 176 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_192 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 192 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_208 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 208 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_224 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 224 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelFive_chunk_240 :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 240 3 =
      true := by decide +kernel

/-- All checked chunks cover the complete output group. -/
theorem levelFive_transfer :
    levelFive.checkRange (levelFour.directEntry 2045911758830089 5 16) 0 243 = true := by
  have h0 := levelFive_chunk_0
  have h1 := Entries.checkRange_append levelFive _ 0 16 16 h0 levelFive_chunk_16
  have h2 := Entries.checkRange_append levelFive _ 0 32 16 h1 levelFive_chunk_32
  have h3 := Entries.checkRange_append levelFive _ 0 48 16 h2 levelFive_chunk_48
  have h4 := Entries.checkRange_append levelFive _ 0 64 16 h3 levelFive_chunk_64
  have h5 := Entries.checkRange_append levelFive _ 0 80 16 h4 levelFive_chunk_80
  have h6 := Entries.checkRange_append levelFive _ 0 96 16 h5 levelFive_chunk_96
  have h7 := Entries.checkRange_append levelFive _ 0 112 16 h6 levelFive_chunk_112
  have h8 := Entries.checkRange_append levelFive _ 0 128 16 h7 levelFive_chunk_128
  have h9 := Entries.checkRange_append levelFive _ 0 144 16 h8 levelFive_chunk_144
  have h10 := Entries.checkRange_append levelFive _ 0 160 16 h9 levelFive_chunk_160
  have h11 := Entries.checkRange_append levelFive _ 0 176 16 h10 levelFive_chunk_176
  have h12 := Entries.checkRange_append levelFive _ 0 192 16 h11 levelFive_chunk_192
  have h13 := Entries.checkRange_append levelFive _ 0 208 16 h12 levelFive_chunk_208
  have h14 := Entries.checkRange_append levelFive _ 0 224 16 h13 levelFive_chunk_224
  have h15 := Entries.checkRange_append levelFive _ 0 240 3 h14 levelFive_chunk_240
  exact h15

/-- The integer cap covers all residues. -/
theorem levelFive_cap : levelFive.allLE 3089969650018044 = true := by decide +kernel

/-- Scaled maximum comparison. -/
theorem levelFive_max_comparison : 1 * 3089969650018044 ≤ 11 * 2 ^ 48 := by
  decide +kernel

/-- Complete integer energy comparison. -/
theorem levelFive_energy_comparison :
    200 * levelFive.energySum 243 ≤
      707 * 243 * (2 ^ 48) ^ 2 := by decide +kernel

/-- Square enclosures include every residue. -/
theorem levelFive_square_enclosures : ∀ i : Fin 243,
    levelFive.lookup i.val ≤ levelFiveRoots.lookup i.val ^ 2 := by decide +kernel

/-- Complete fractional numerator comparison. -/
theorem levelFive_fractional_comparison :
    500000 * levelFive.fractionalSum levelFiveRoots 243 ≤
        862279 * 243 * 2 ^ 72 := by decide +kernel

end WordCertDensity.Certificates
