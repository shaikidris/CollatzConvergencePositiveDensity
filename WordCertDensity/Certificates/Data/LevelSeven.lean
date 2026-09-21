/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.Data.Summaries
public import WordCertDensity.Certificates.Data.LevelSix

/-! # Complete depth-7 integer certificate -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Complete enclosure tree, with one leaf per residue. -/
def levelSeven : Entries :=
  (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 79386603168853)) (.leaf 39693301584427)) (.node (.leaf 808342034128665) (.leaf 0))) (.node (.node (.leaf 404171017064333) (.leaf 452559478790183)) (.node (.leaf 0) (.leaf 600986034235385)))) (.node (.node (.node (.node (.leaf 438652012728713) (.leaf 119183409900406)) (.leaf 0)) (.node (.leaf 226279739395092) (.leaf 1700532363798337))) (.node (.node (.leaf 0) (.leaf 154086517549362)) (.node (.leaf 300493018683241) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 219326006364357) (.leaf 0)) (.leaf 161457700699377)) (.node (.leaf 0) (.leaf 73409878168162))) (.node (.node (.leaf 113139871288002) (.leaf 0)) (.node (.leaf 850266181899169) (.leaf 436790213223364)))) (.node (.node (.node (.leaf 0) (.leaf 172679891411537)) (.node (.leaf 436555917252771) (.leaf 0))) (.node (.node (.leaf 150246509341621) (.leaf 100938204021289)) (.node (.leaf 0) (.leaf 341854624078016)))))) (.node (.node (.node (.node (.node (.node (.leaf 109663004711127) (.leaf 153790757637608)) (.leaf 0)) (.node (.leaf 80728850349689) (.leaf 251027935684483))) (.node (.node (.leaf 0) (.leaf 69473402172325)) (.node (.leaf 1083284151138156) (.leaf 0)))) (.node (.node (.node (.leaf 56569935644001) (.leaf 99339932617458)) (.node (.leaf 0) (.leaf 374994252046254))) (.node (.node (.leaf 527497525646056) (.leaf 0)) (.node (.leaf 218395106611682) (.leaf 346548265584313))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 255508530794455)) (.leaf 113815570896478)) (.node (.leaf 86339947281989) (.leaf 0))) (.node (.node (.leaf 218277958626386) (.leaf 1905515300809143)) (.node (.leaf 0) (.leaf 176939873932901)))) (.node (.node (.node (.leaf 220145981572129) (.leaf 0)) (.node (.leaf 50469102010645) (.leaf 680263560110701))) (.node (.node (.leaf 0) (.leaf 154572353828348)) (.node (.leaf 2794479952414330) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 54831502355564) (.leaf 0)) (.leaf 76895380416803)) (.node (.leaf 0) (.leaf 815322410062089))) (.node (.node (.leaf 451478738873923) (.leaf 0)) (.node (.leaf 125513967842242) (.leaf 1190054145688735)))) (.node (.node (.node (.leaf 0) (.leaf 43156251653578)) (.node (.leaf 214016741056893) (.leaf 0))) (.node (.node (.leaf 541642075569078) (.leaf 714602855076499)) (.node (.leaf 0) (.leaf 128750261629810))))) (.node (.node (.node (.node (.node (.leaf 398735267300017) (.leaf 741875742301316)) (.leaf 0)) (.node (.leaf 49669966308729) (.leaf 56371714599000))) (.node (.node (.leaf 0) (.leaf 250907345428769)) (.node (.leaf 225661977469730) (.leaf 0)))) (.node (.node (.node (.leaf 263748762823028) (.leaf 491573644330524)) (.node (.leaf 0) (.leaf 124987964363884))) (.node (.node (.leaf 109197554739901) (.leaf 0)) (.node (.leaf 173274132792157) (.leaf 1438088207638024)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 3044226219724644)) (.leaf 127754265397228)) (.node (.leaf 394603154715315) (.leaf 0))) (.node (.node (.leaf 43169973640995) (.leaf 143742979687652)) (.node (.leaf 0) (.leaf 75465717642140)))) (.node (.node (.node (.leaf 109138980926485) (.leaf 0)) (.node (.leaf 952757650404572) (.leaf 306760060992530))) (.node (.node (.leaf 0) (.leaf 43005121661769)) (.node (.leaf 500840225739867) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 110072990786065) (.leaf 0)) (.leaf 400059011092184)) (.node (.leaf 0) (.leaf 340324089676327))) (.node (.node (.leaf 744936364842022) (.leaf 0)) (.node (.leaf 340131780055351) (.leaf 80808190011367)))) (.node (.node (.node (.leaf 0) (.leaf 301995124081547)) (.node (.leaf 77286178452997) (.leaf 0))) (.node (.node (.leaf 1397239976207165) (.leaf 336696975200996)) (.node (.leaf 0) (.leaf 75451112526680)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 323796412460648) (.leaf 197292138931639)) (.leaf 0)) (.node (.leaf 38447690208402) (.leaf 191304813202237))) (.node (.node (.leaf 0) (.leaf 157173625691623)) (.node (.leaf 561854198706686) (.leaf 0)))) (.node (.node (.node (.node (.leaf 225739369436962) (.leaf 0)) (.leaf 949095198191797)) (.node (.leaf 0) (.leaf 34723903406925))) (.node (.node (.leaf 62756985530923) (.leaf 0)) (.node (.leaf 595027072844368) (.leaf 250794280385100))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 136387167849947)) (.leaf 88010979120185)) (.node (.leaf 409993021792194) (.leaf 0))) (.node (.node (.leaf 107008370528447) (.leaf 723567670901317)) (.node (.leaf 0) (.leaf 173431181627076)))) (.node (.node (.node (.leaf 333013169992139) (.leaf 0)) (.node (.leaf 357301427538250) (.leaf 152778064277907))) (.node (.node (.leaf 0) (.leaf 215780360422595)) (.node (.leaf 64375132414716) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 199367633650009) (.leaf 0)) (.leaf 450435888404247)) (.node (.leaf 0) (.leaf 377951052377360))) (.node (.node (.leaf 480353982814963) (.leaf 0)) (.node (.leaf 28185857299500) (.leaf 123472966735063)))) (.node (.node (.node (.leaf 0) (.leaf 201258639114507)) (.node (.leaf 125453674244095) (.leaf 0))) (.node (.node (.leaf 112830988734865) (.leaf 1327640653621438)) (.node (.leaf 0) (.leaf 65049819712357))))) (.node (.node (.node (.node (.node (.leaf 131874382839392) (.leaf 224141559171717)) (.leaf 0)) (.node (.leaf 245786822165262) (.leaf 5237513839921424))) (.node (.node (.leaf 0) (.leaf 333971295547149)) (.node (.leaf 735032628828205) (.leaf 0)))) (.node (.node (.node (.leaf 54598777369951) (.leaf 353582658775167)) (.node (.leaf 0) (.leaf 251422981762299))) (.node (.node (.leaf 812387050957766) (.leaf 0)) (.node (.leaf 719044103819012) (.leaf 658496616478094))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 556768326699847)) (.leaf 1522113109862322)) (.node (.leaf 63877133717658) (.leaf 0))) (.node (.node (.leaf 197301577357658) (.leaf 206502826367146)) (.node (.leaf 0) (.leaf 58990908227939)))) (.node (.node (.node (.leaf 1246513936777241) (.leaf 0)) (.node (.leaf 71871489843826) (.leaf 72614102302125))) (.node (.node (.leaf 0) (.leaf 127644884590828)) (.node (.leaf 207978046285916) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 54569490463243) (.leaf 0)) (.leaf 149381601224281)) (.node (.leaf 0) (.leaf 173725951508946))) (.node (.node (.leaf 809539159742304) (.leaf 0)) (.node (.leaf 153380030496265) (.leaf 1436830665181149)))) (.node (.node (.node (.leaf 0) (.leaf 37976958217661)) (.node (.leaf 1746189374430919) (.leaf 0))) (.node (.node (.leaf 250420112869934) (.leaf 387459951392245)) (.node (.leaf 0) (.leaf 437776845580091)))))) (.node (.node (.node (.node (.node (.node (.leaf 422530407449773) (.leaf 45105807698890)) (.leaf 0)) (.node (.leaf 200029505546092) (.leaf 523693736217280))) (.node (.node (.leaf 0) (.leaf 586375990824604)) (.node (.leaf 170162046450311) (.leaf 0)))) (.node (.node (.node (.leaf 372468182421011) (.leaf 1161414480501454)) (.node (.leaf 0) (.leaf 295988977360352))) (.node (.node (.leaf 305104457205504) (.leaf 0)) (.node (.leaf 40404095005684) (.leaf 108848087655229))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 211332338958564)) (.leaf 417173393888659)) (.node (.leaf 269770667300507) (.leaf 0))) (.node (.node (.leaf 38643089226499) (.leaf 59658294845477)) (.node (.leaf 0) (.leaf 420128528269160)))) (.node (.node (.node (.leaf 698619989596562) (.leaf 0)) (.node (.leaf 168348487600498) (.leaf 240010892631145))) (.node (.node (.leaf 0) (.leaf 65461885022162)) (.node (.leaf 545561510616483) (.leaf 0))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 161898206230324) (.leaf 0)) (.leaf 737938723730373)) (.node (.leaf 0) (.leaf 208538459089345))) (.node (.node (.leaf 449446404905224) (.leaf 0)) (.node (.leaf 95652406601119) (.leaf 167055747101192)))) (.node (.node (.node (.node (.leaf 0) (.leaf 1542237107995553)) (.leaf 283753699388977)) (.node (.leaf 78586814379178) (.leaf 0))) (.node (.node (.leaf 280927099353343) (.leaf 158455931297015)) (.node (.leaf 0) (.leaf 36368067204769))))) (.node (.node (.node (.node (.node (.leaf 112869686322557) (.leaf 486343557295932)) (.leaf 0)) (.node (.leaf 474547599095899) (.leaf 236155124399553))) (.node (.node (.leaf 0) (.leaf 36731279896210)) (.node (.leaf 1259152599085843) (.leaf 0)))) (.node (.node (.node (.leaf 31378492765462) (.leaf 414509204972866)) (.node (.leaf 0) (.leaf 143120085032206))) (.node (.node (.leaf 417099685435423) (.leaf 0)) (.node (.leaf 125397140192550) (.leaf 603561356901825)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 132717376780190)) (.leaf 68193583924974)) (.node (.leaf 245700604177130) (.leaf 0))) (.node (.node (.leaf 204996510896097) (.leaf 1621391337844263)) (.node (.leaf 0) (.leaf 164774039234876)))) (.node (.node (.node (.leaf 467176332573959) (.leaf 0)) (.node (.leaf 361783835450659) (.leaf 2051133496149453))) (.node (.node (.leaf 0) (.leaf 283179313770112)) (.node (.leaf 86715592391857) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 166506584996070) (.leaf 0)) (.leaf 1236296825612148)) (.node (.leaf 0) (.leaf 184690095573070))) (.node (.node (.leaf 178650715348576) (.leaf 0)) (.node (.leaf 76389032138954) (.leaf 277595226302878)))) (.node (.node (.node (.leaf 0) (.leaf 419372765433977)) (.node (.leaf 241096591741221) (.leaf 0))) (.node (.node (.leaf 32187566207358) (.leaf 65385141101786)) (.node (.leaf 0) (.leaf 961858243613953))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 704087826772776) (.leaf 163167591794407)) (.leaf 0)) (.node (.leaf 225217944202124) (.leaf 848084730429746))) (.node (.node (.leaf 0) (.leaf 138506680724426)) (.node (.leaf 188975527205580) (.leaf 0)))) (.node (.node (.node (.leaf 240176991407482) (.leaf 303815660185598)) (.node (.leaf 0) (.leaf 308969622642581))) (.node (.node (.leaf 1614878036031836) (.leaf 0)) (.node (.leaf 61736483367532) (.leaf 81400763270412))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 1419498846973943)) (.leaf 185120300082795)) (.node (.leaf 345250006773617) (.leaf 0))) (.node (.node (.leaf 62726837122048) (.leaf 62823619830674)) (.node (.leaf 0) (.leaf 874644300774223)))) (.node (.node (.node (.leaf 56415495885197) (.leaf 0)) (.node (.leaf 663820326810719) (.leaf 555787211069205))) (.node (.node (.leaf 0) (.leaf 42413125070785)) (.node (.leaf 569162567988556) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 65937191419696) (.leaf 0)) (.leaf 112070781123762)) (.node (.leaf 0) (.leaf 262671371067390))) (.node (.node (.leaf 775479714667444) (.leaf 0)) (.node (.leaf 2618756919960712) (.leaf 444466940198063)))) (.node (.node (.node (.leaf 0) (.leaf 121365498329013)) (.node (.leaf 887734161225059) (.leaf 0))) (.node (.node (.leaf 367516314414103) (.leaf 644434478445752)) (.node (.leaf 0) (.leaf 438669782973620))))) (.node (.node (.node (.node (.node (.leaf 235593246151362) (.leaf 95124972745436)) (.leaf 0)) (.node (.leaf 176791329387584) (.leaf 125462106255725))) (.node (.node (.leaf 0) (.leaf 259448301996644)) (.node (.leaf 970923980549122) (.leaf 0)))) (.node (.node (.node (.leaf 406193525478883) (.leaf 315819316916968)) (.node (.leaf 0) (.leaf 25059320560332))) (.node (.node (.leaf 359522053519936) (.leaf 0)) (.node (.leaf 329248308239047) (.leaf 293850232996845)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 191314605205980)) (.leaf 278384163349924)) (.node (.leaf 834690213344690) (.leaf 0))) (.node (.node (.leaf 31938566858829) (.leaf 84854754536009)) (.node (.leaf 0) (.leaf 449448251603697)))) (.node (.node (.node (.leaf 98650790234355) (.leaf 0)) (.node (.leaf 103251413183573) (.leaf 508761463768085))) (.node (.node (.leaf 0) (.leaf 157185848940128)) (.node (.leaf 618564704933879) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 623256968388621) (.leaf 0)) (.leaf 569230418372894)) (.node (.leaf 0) (.leaf 188975361865120))) (.node (.node (.leaf 445265697825748) (.leaf 0)) (.node (.leaf 36307051151063) (.leaf 541545112034782)))) (.node (.node (.node (.leaf 0) (.leaf 473245206535262)) (.node (.leaf 63822443872467) (.leaf 0))) (.node (.node (.leaf 103989023142958) (.leaf 925157886340746)) (.node (.leaf 0) (.leaf 43670646641650)))))) (.node (.node (.node (.node (.node (.node (.leaf 846200205925494) (.leaf 131836017532197)) (.leaf 0)) (.node (.leaf 74690800612141) (.leaf 138925029259624))) (.node (.node (.leaf 0) (.leaf 260210501259420)) (.node (.leaf 317446878989475) (.leaf 0)))) (.node (.node (.node (.leaf 404769579871152) (.leaf 455050595028156)) (.node (.leaf 0) (.leaf 110247316451440))) (.node (.node (.leaf 76690016736014) (.leaf 0)) (.node (.leaf 718415332590575) (.leaf 825976742382613))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 66811523614539)) (.leaf 96934965101601)) (.node (.leaf 367564225678766) (.leaf 0))) (.node (.node (.leaf 873094687215460) (.leaf 222628575351108)) (.node (.leaf 0) (.leaf 398170787725525)))) (.node (.node (.node (.leaf 986013035093049) (.leaf 0)) (.node (.leaf 193729975696123) (.leaf 989230950111823))) (.node (.node (.leaf 0) (.leaf 76891909261383)) (.node (.leaf 218888424351832) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 211265203724887) (.leaf 0)) (.leaf 681579630237778)) (.node (.leaf 0) (.leaf 27540578721017))) (.node (.node (.leaf 100014754316905) (.leaf 0)) (.node (.leaf 261846868108640) (.leaf 775533708263876)))) (.node (.node (.node (.leaf 0) (.leaf 134411392305956)) (.node (.leaf 2914307457301967) (.leaf 0))) (.node (.node (.leaf 85081023225156) (.leaf 208196439830174)) (.node (.leaf 0) (.leaf 670374753704407))))) (.node (.node (.node (.node (.node (.leaf 300778888281557) (.leaf 46203615429334)) (.leaf 0)) (.node (.leaf 580707240250727) (.leaf 459542865224960))) (.node (.node (.leaf 0) (.leaf 505894924845628)) (.node (.leaf 147994490118489) (.leaf 0)))) (.node (.node (.node (.leaf 152552228602752) (.leaf 243808534207159)) (.node (.leaf 0) (.leaf 244696825319060))) (.node (.node (.leaf 912905765328772) (.leaf 0)) (.node (.leaf 54424043827615) (.leaf 188724167117015)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 624737979883980)) (.leaf 105666169479282)) (.node (.leaf 208586698400022) (.leaf 0))) (.node (.node (.leaf 134885333650254) (.leaf 762403506435522)) (.node (.leaf 0) (.leaf 108199812817703)))) (.node (.node (.node (.leaf 873454600919941) (.leaf 0)) (.node (.leaf 29829147422739) (.leaf 60342042500395))) (.node (.node (.leaf 0) (.leaf 457204616349025)) (.node (.leaf 417350625851747) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 349309994798281) (.leaf 0)) (.leaf 135579559598314)) (.node (.leaf 0) (.leaf 612834342739548))) (.node (.node (.leaf 1031512813893713) (.leaf 0)) (.node (.leaf 120005446315573) (.leaf 402201330083354)))) (.node (.node (.node (.leaf 0) (.leaf 80554310590483)) (.node (.leaf 134352000664905) (.leaf 0))) (.node (.node (.leaf 272780755308242) (.leaf 389501767292864)) (.node (.leaf 0) (.leaf 237703651133908)))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 484339327560304) (.leaf 58945478530574)) (.leaf 0)) (.node (.leaf 368969361865187) (.leaf 629428955930467))) (.node (.node (.leaf 0) (.leaf 687702126981384)) (.node (.leaf 104269231132130) (.leaf 0)))) (.node (.node (.node (.node (.leaf 224723202452612) (.leaf 0)) (.leaf 1685640909396077)) (.node (.leaf 0) (.leaf 373513381140344))) (.node (.node (.leaf 314239024912432) (.leaf 0)) (.node (.leaf 83527873550596) (.leaf 167170175841455))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 286472918572875)) (.leaf 771118553997777)) (.node (.leaf 230323074730791) (.leaf 0))) (.node (.node (.leaf 39293407189589) (.leaf 149872763877713)) (.node (.leaf 0) (.leaf 385714856958115)))) (.node (.node (.node (.leaf 140463551250967) (.leaf 0)) (.node (.leaf 79227965648508) (.leaf 230864084178277))) (.node (.node (.leaf 0) (.leaf 52150898441095)) (.node (.leaf 1296769341279024) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 56434843161279) (.leaf 0)) (.leaf 243171780225354)) (.node (.leaf 0) (.leaf 117382681412276))) (.node (.node (.leaf 481203291578893) (.leaf 0)) (.node (.leaf 118077562199777) (.leaf 947923560258033)))) (.node (.node (.node (.leaf 0) (.leaf 30137074474920)) (.node (.leaf 1708790617713067) (.leaf 0))) (.node (.node (.leaf 629576299542922) (.leaf 209115563191155)) (.node (.leaf 0) (.leaf 662557256453097))))) (.node (.node (.node (.node (.node (.leaf 504930619526415) (.leaf 1498838174635411)) (.leaf 0)) (.node (.leaf 207254602486433) (.leaf 213204321105568))) (.node (.node (.leaf 0) (.leaf 251054101113510)) (.node (.leaf 1144835353838075) (.leaf 0)))) (.node (.node (.node (.leaf 208549842717712) (.leaf 256342424825473)) (.node (.leaf 0) (.leaf 81647430551897))) (.node (.node (.leaf 62698571689532) (.leaf 0)) (.node (.leaf 301780678450913) (.leaf 424754738694699))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 110216104024826)) (.leaf 66358688390095)) (.node (.leaf 495264597081761) (.leaf 0))) (.node (.node (.leaf 122850302088565) (.leaf 382141396996795)) (.node (.leaf 0) (.leaf 273849580760633)))) (.node (.node (.node (.leaf 200865974443196) (.leaf 0)) (.node (.leaf 810695668922132) (.leaf 271958272326320))) (.node (.node (.leaf 0) (.leaf 278751980905036)) (.node (.leaf 82387020991441) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 233588166286980) (.leaf 0)) (.leaf 805094492272296)) (.node (.leaf 0) (.leaf 46109512861872))) (.node (.node (.leaf 180891919337405) (.leaf 0)) (.node (.leaf 1025566748074727) (.leaf 356842324631141)))) (.node (.node (.node (.leaf 0) (.leaf 193454890062391)) (.node (.leaf 1086622581149704) (.leaf 0))) (.node (.node (.leaf 43357796195929) (.leaf 83002810928180)) (.node (.leaf 0) (.leaf 89540736202874)))))) (.node (.node (.node (.node (.node (.node (.leaf 83253293949314) (.leaf 184438048282770)) (.leaf 0)) (.node (.leaf 618148412806074) (.leaf 332011237382690))) (.node (.node (.leaf 0) (.leaf 34699404084687)) (.node (.leaf 506917770397886) (.leaf 0)))) (.node (.node (.node (.leaf 89325357674288) (.leaf 60359158521109)) (.node (.leaf 0) (.leaf 485838614475130))) (.node (.node (.leaf 241436627761332) (.leaf 0)) (.node (.leaf 138797613151439) (.leaf 600744646433557))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 852817277986480)) (.leaf 185300942523473)) (.node (.leaf 209686384219820) (.leaf 0))) (.node (.node (.leaf 120548295870611) (.leaf 434200631348505)) (.node (.leaf 0) (.leaf 238946817455745)))) (.node (.node (.node (.leaf 5258332705336516) (.leaf 0)) (.node (.leaf 32692570550893) (.leaf 65855005065851))) (.node (.node (.leaf 0) (.leaf 208603590652195)) (.node (.leaf 599491050403024) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 352043913386388) (.leaf 0)) (.leaf 240579828991831)) (.node (.leaf 0) (.leaf 68462395996394))) (.node (.node (.leaf 112608973614569) (.leaf 0)) (.node (.leaf 424042365214873) (.leaf 765219246685959)))) (.node (.node (.node (.node (.leaf 0) (.leaf 6994258928192191)) (.leaf 1335885178966524)) (.node (.leaf 1414330628687556) (.leaf 0))) (.node (.node (.leaf 94487763602790) (.leaf 95535350856582)) (.node (.leaf 0) (.leaf 270013560596310))))) (.node (.node (.node (.node (.node (.leaf 597526398733271) (.leaf 55611147191049)) (.leaf 0)) (.node (.leaf 151907830092799) (.leaf 1354399452145809))) (.node (.node (.leaf 0) (.leaf 80356977112295)) (.node (.leaf 154484812889004) (.leaf 0)))) (.node (.node (.node (.leaf 807439018015918) (.leaf 238633173461488)) (.node (.leaf 0) (.leaf 261847537068086))) (.node (.node (.leaf 339254227464910) (.leaf 0)) (.node (.leaf 40700381635206) (.leaf 54804433642267)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 225486852277709)) (.leaf 709749423486972)) (.node (.leaf 92560151654246) (.leaf 0))) (.node (.node (.leaf 172625003386809) (.leaf 2173798601001693)) (.node (.leaf 0) (.leaf 40867953141104)))) (.node (.node (.node (.leaf 268909627781665) (.leaf 0)) (.node (.leaf 31411809915337) (.leaf 418642358918778))) (.node (.node (.leaf 0) (.leaf 172020483503795)) (.node (.leaf 574971912495751) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 28207747942599) (.leaf 0)) (.leaf 50216495194888)) (.node (.leaf 0) (.leaf 416594299167984))) (.node (.node (.leaf 397359724256591) (.leaf 0)) (.node (.leaf 277893605534603) (.leaf 202142242840380)))) (.node (.node (.node (.leaf 0) (.leaf 202673918015066)) (.node (.leaf 361696936007706) (.leaf 0))) (.node (.node (.leaf 284581283994278) (.leaf 403752809631699)) (.node (.leaf 0) (.leaf 293639509519836))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 708359332743388) (.leaf 219263788132281)) (.leaf 0)) (.node (.leaf 56035390561881) (.leaf 89210582452886))) (.node (.node (.leaf 0) (.leaf 628743392594819)) (.node (.leaf 339419011909378) (.leaf 0)))) (.node (.node (.node (.leaf 387739857333722) (.leaf 710886186777524)) (.node (.leaf 0) (.leaf 62946944945287))) (.node (.node (.leaf 1309378461545557) (.leaf 0)) (.node (.leaf 222233470099032) (.leaf 555700111147590))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 245607171195831)) (.leaf 58397042372372)) (.node (.leaf 137012450996267) (.leaf 0))) (.node (.node (.leaf 443867080612530) (.leaf 832785753429129)) (.node (.leaf 0) (.leaf 110162311789868)))) (.node (.node (.node (.leaf 542318232004998) (.leaf 0)) (.node (.leaf 322217239222876) (.leaf 390777265238151))) (.node (.node (.leaf 0) (.leaf 228033356473048)) (.node (.leaf 219334893094358) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 117796623075681) (.leaf 0)) (.leaf 251294472891552)) (.node (.leaf 0) (.leaf 169652497087825))) (.node (.node (.leaf 807420980643162) (.leaf 0)) (.node (.leaf 62731053127863) (.leaf 59637246107625)))) (.node (.node (.node (.leaf 0) (.leaf 829499349449834)) (.node (.leaf 129724152550064) (.leaf 0))) (.node (.node (.leaf 485461990274561) (.leaf 745021191336487)) (.node (.leaf 0) (.leaf 30408625633673))))) (.node (.node (.node (.node (.node (.leaf 203096764301637) (.leaf 738760379136305)) (.leaf 0)) (.node (.leaf 157909658458484) (.leaf 261540558445099))) (.node (.node (.leaf 0) (.leaf 48363723257529)) (.node (.leaf 5259634939501439) (.leaf 0)))) (.node (.node (.node (.leaf 179761026759968) (.leaf 271655646718302)) (.node (.leaf 0) (.leaf 113405321463244))) (.node (.node (.leaf 1658036813820515) (.leaf 0)) (.node (.leaf 146925116498423) (.leaf 421330883586125))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 325538137709546)) (.leaf 95657302602990)) (.node (.leaf 139192083227141) (.leaf 0))) (.node (.node (.leaf 417345106672345) (.leaf 620002521603690)) (.node (.leaf 0) (.leaf 76114383130072)))) (.node (.node (.node (.node (.leaf 832836877215143) (.leaf 841261647922125)) (.leaf 0)) (.node (.leaf 42427377268005) (.leaf 69587385676977))) (.node (.node (.leaf 0) (.leaf 385458796213406)) (.node (.leaf 274075930212170) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 49325395117178) (.leaf 0)) (.leaf 121084833480242)) (.node (.leaf 0) (.leaf 177399582975909))) (.node (.node (.leaf 249032916855851) (.leaf 0)) (.node (.leaf 254380731884043) (.leaf 1209551450670654)))) (.node (.node (.node (.leaf 0) (.leaf 92242341272702)) (.node (.leaf 177296532031247) (.leaf 0))) (.node (.node (.leaf 309282352466940) (.leaf 752548215415245)) (.node (.leaf 0) (.leaf 151635019091440)))))) (.node (.node (.node (.node (.node (.node (.leaf 364017341327750) (.leaf 107991417080057)) (.leaf 0)) (.node (.leaf 284615209186447) (.leaf 177399495129368))) (.node (.node (.leaf 0) (.leaf 553707605981130)) (.node (.leaf 94487682500435) (.leaf 0)))) (.node (.node (.node (.leaf 222632848912874) (.leaf 375527362735235)) (.node (.leaf 0) (.leaf 232314780318510))) (.node (.node (.leaf 966648939080882) (.leaf 0)) (.node (.leaf 270772556017391) (.leaf 174050636977907))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 1016267642303148)) (.leaf 139108640679773)) (.node (.leaf 645056400944352) (.leaf 0))) (.node (.node (.leaf 31911221936234) (.leaf 421410228920001)) (.node (.leaf 0) (.leaf 160638575430716)))) (.node (.node (.node (.leaf 51994513172069) (.leaf 0)) (.node (.leaf 462578943170373) (.leaf 512920401759248))) (.node (.node (.leaf 0) (.leaf 93378346015846)) (.node (.leaf 721584120399480) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 423100102962747) (.leaf 0)) (.leaf 415792408022529)) (.node (.leaf 0) (.leaf 121833978573876))) (.node (.node (.leaf 145520730363025) (.leaf 0)) (.node (.leaf 69462514629812) (.leaf 248251238661092)))) (.node (.node (.node (.leaf 0) (.leaf 1100059186388467)) (.node (.leaf 130105252243838) (.leaf 0))) (.node (.node (.leaf 158723439494738) (.leaf 400902998097218)) (.node (.leaf 0) (.leaf 62714693231734))))) (.node (.node (.node (.node (.node (.leaf 202384791476461) (.leaf 435311414068979)) (.leaf 0)) (.node (.leaf 227525297514078) (.leaf 530886318663807))) (.node (.node (.leaf 0) (.leaf 192779639234546)) (.node (.leaf 691107779394678) (.leaf 0)))) (.node (.node (.node (.leaf 38345008368007) (.leaf 57580770200442)) (.node (.leaf 0) (.leaf 167952949911121))) (.node (.node (.leaf 470795632906676) (.leaf 0)) (.node (.leaf 412988371191307) (.leaf 226959720060786)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 65501997541670)) (.leaf 33405761807270)) (.node (.leaf 1435440555864133) (.leaf 0))) (.node (.node (.leaf 183782112839383) (.leaf 391995811343882)) (.node (.leaf 0) (.leaf 255090429376364)))) (.node (.node (.node (.leaf 3037686551681273) (.leaf 0)) (.node (.leaf 111314287675554) (.leaf 830921338901004))) (.node (.node (.leaf 0) (.leaf 249872368370088)) (.node (.leaf 199085395409256) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 493006517546525) (.leaf 0)) (.leaf 183599694001918)) (.node (.leaf 0) (.leaf 28616939928723))) (.node (.node (.leaf 96864988861887) (.leaf 0)) (.node (.leaf 494615475055912) (.leaf 865330725162454)))) (.node (.node (.node (.leaf 0) (.leaf 150706111372773)) (.node (.leaf 512693661857748) (.leaf 0))) (.node (.node (.leaf 109444212175916) (.leaf 57716022626994)) (.node (.leaf 0) (.leaf 382129307486160)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 105632603475442) (.leaf 835376536572173)) (.leaf 0)) (.node (.leaf 340789815118889) (.leaf 326943618944657))) (.node (.node (.leaf 0) (.leaf 29519391334739)) (.node (.leaf 289069811995280) (.leaf 0)))) (.node (.node (.node (.leaf 50007377158453) (.leaf 120300824464859)) (.node (.leaf 0) (.leaf 88683059226097))) (.node (.node (.leaf 503575553438256) (.leaf 0)) (.node (.leaf 387766854131938) (.leaf 687091039492206))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 1911574533321956)) (.leaf 230459366445136)) (.node (.leaf 67205697678212) (.leaf 0))) (.node (.node (.leaf 1457153728650984) (.leaf 290426992040941)) (.node (.leaf 0) (.leaf 194995580280743)))) (.node (.node (.node (.leaf 2732695086928555) (.leaf 0)) (.node (.leaf 104098219915087) (.leaf 217238260250906))) (.node (.node (.leaf 0) (.leaf 252521600130156)) (.node (.leaf 653179438059101) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 150389444140779) (.leaf 0)) (.leaf 430565779623900)) (.node (.leaf 0) (.leaf 165639314769021))) (.node (.node (.leaf 290353621529463) (.leaf 0)) (.node (.leaf 229771432612480) (.leaf 1559964635842227)))) (.node (.node (.node (.leaf 0) (.leaf 209094776082218)) (.node (.leaf 307035127052376) (.leaf 0))) (.node (.node (.leaf 73997245059245) (.leaf 52278892382608)) (.node (.leaf 0) (.leaf 213306005485735))))) (.node (.node (.node (.node (.node (.leaf 228935512977363) (.leaf 25170459482809)) (.leaf 0)) (.node (.leaf 121904267103580) (.leaf 1281822940040891))) (.node (.node (.leaf 0) (.leaf 1530490895353349)) (.node (.leaf 122348414272708) (.leaf 0)))) (.node (.node (.node (.leaf 456452882664386) (.leaf 608915058779454)) (.node (.leaf 0) (.leaf 153355990788753))) (.node (.node (.leaf 443378673438240) (.leaf 0)) (.node (.leaf 94362083558508) (.leaf 153901853739057))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 382467997705842)) (.leaf 312368989941990)) (.node (.leaf 881978525209833) (.leaf 0))) (.node (.node (.leaf 104293349200011) (.leaf 286208840069707)) (.node (.leaf 0) (.leaf 2607674068970654)))) (.node (.node (.node (.leaf 67442668390425) (.leaf 0)) (.node (.leaf 381201753217761) (.leaf 865598497042508))) (.node (.node (.leaf 0) (.leaf 62763526078800)) (.node (.leaf 291223762267986) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 436727300459971) (.leaf 0)) (.leaf 200474558616835)) (.node (.leaf 0) (.leaf 539466225577788))) (.node (.node (.leaf 1904980420663276) (.leaf 0)) (.node (.leaf 30171021250198) (.leaf 110730583092661)))) (.node (.node (.node (.leaf 0) (.leaf 111517012691243)) (.node (.leaf 228602309675123) (.leaf 0))) (.node (.node (.leaf 208675312925874) (.leaf 564124987674189)) (.node (.leaf 0) (.leaf 60368436246408)))))) (.node (.node (.node (.node (.node (.node (.leaf 351547445972725) (.leaf 138629551424915)) (.leaf 0)) (.node (.leaf 67789779799157) (.leaf 106188686203045))) (.node (.node (.leaf 0) (.leaf 120491952764466)) (.node (.leaf 999903708741879) (.leaf 0)))) (.node (.node (.node (.leaf 515756406946857) (.leaf 757790107570458)) (.node (.leaf 0) (.leaf 38379391593492))) (.node (.node (.leaf 60002724751996) (.leaf 0)) (.node (.leaf 201100665041677) (.leaf 1415518985518845))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 72113722169671)) (.leaf 52137461460189)) (.node (.leaf 2186827776801868) (.leaf 0))) (.node (.node (.leaf 67176000332453) (.leaf 471927259456526)) (.node (.leaf 0) (.leaf 125896715899204)))) (.node (.node (.node (.leaf 277791222111364) (.leaf 0)) (.node (.leaf 194750883646432) (.leaf 227267657485375))) (.node (.node (.leaf 0) (.leaf 852745155189279)) (.node (.leaf 118851826834957) (.leaf 0))))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 242169663780152) (.leaf 0)) (.leaf 354799165951818)) (.node (.leaf 0) (.leaf 38338998489337))) (.node (.node (.leaf 184484682545404) (.leaf 0)) (.node (.leaf 314714477965234) (.leaf 303270038182880)))) (.node (.node (.node (.node (.leaf 0) (.leaf 1682523295844249)) (.leaf 139174768258058)) (.node (.leaf 770917592426812) (.leaf 0))) (.node (.node (.leaf 52134615566065) (.leaf 152228766260144)) (.node (.leaf 0) (.leaf 108648480615818))))) (.node (.node (.node (.node (.node (.leaf 278217281359545) (.leaf 195462931270226)) (.leaf 0)) (.node (.leaf 842820454698039) (.leaf 321277150861431))) (.node (.node (.leaf 0) (.leaf 272359042953075)) (.node (.leaf 186756692031691) (.leaf 0)))) (.node (.node (.node (.leaf 157119512456216) (.leaf 464629560637019)) (.node (.leaf 0) (.leaf 348101270738050))) (.node (.node (.leaf 1107415211962260) (.leaf 0)) (.node (.leaf 83585087920728) (.leaf 215982834160113)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 870622828137957)) (.leaf 143236459286438)) (.node (.leaf 385559278469092) (.leaf 0))) (.node (.node (.leaf 115161537365396) (.leaf 335905899822241)) (.node (.leaf 0) (.leaf 94068527651455)))) (.node (.node (.node (.leaf 2200118372776934) (.leaf 0)) (.node (.leaf 74936381938857) (.leaf 125429386463468))) (.node (.node (.leaf 0) (.leaf 496502474143934)) (.node (.leaf 243667957147751) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 70231775625484) (.leaf 0)) (.leaf 57233879857446)) (.node (.leaf 0) (.leaf 1460831764092373))) (.node (.node (.leaf 301412222745545) (.leaf 0)) (.node (.leaf 115432042089139) (.leaf 764258614972319)))) (.node (.node (.node (.leaf 0) (.leaf 30476067577757)) (.node (.leaf 499744736740176) (.leaf 0))) (.node (.node (.leaf 648384670639512) (.leaf 510180858752728)) (.node (.leaf 0) (.leaf 131003991968629))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 460918732890271) (.leaf 759415774163182)) (.leaf 0)) (.node (.leaf 121585890112677) (.leaf 389991160561486))) (.node (.node (.leaf 0) (.leaf 434476517328362)) (.node (.leaf 505043200260311) (.leaf 0)))) (.node (.node (.node (.leaf 240601645789447) (.leaf 177366118452194)) (.node (.leaf 0) (.leaf 31129115407865))) (.node (.node (.leaf 59038782669477) (.leaf 0)) (.node (.leaf 473961780129017) (.leaf 1670753073144345))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 50340918965617)) (.leaf 37597361794976)) (.node (.leaf 3060981790706698) (.leaf 0))) (.node (.node (.leaf 854395308856534) (.leaf 306711981577505)) (.node (.leaf 0) (.leaf 307803704444877)))) (.node (.node (.node (.leaf 418189552164435) (.leaf 0)) (.node (.leaf 104557781595578) (.leaf 426612010971470))) (.node (.node (.leaf 0) (.leaf 222847326055146)) (.node (.leaf 331278629538042) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 252465309763208) (.leaf 0)) (.leaf 1078932451155575)) (.node (.leaf 0) (.leaf 221461163376050))) (.node (.node (.leaf 223034025382485) (.leaf 0)) (.node (.leaf 106602160552784) (.leaf 120736872492815)))) (.node (.node (.node (.leaf 0) (.leaf 397867350628705)) (.node (.leaf 125527052157599) (.leaf 0))) (.node (.node (.leaf 572417676919038) (.leaf 5215348137941307)) (.node (.leaf 0) (.leaf 37635695426852))))) (.node (.node (.node (.node (.node (.leaf 104274922920378) (.leaf 144227441246592)) (.leaf 0)) (.node (.leaf 128171212412737) (.leaf 251793431798408))) (.node (.node (.leaf 0) (.leaf 52273694798646)) (.node (.leaf 1705490310378558) (.leaf 0)))) (.node (.node (.node (.leaf 31349285844766) (.leaf 76758783186983)) (.node (.leaf 0) (.leaf 2625480810444684))) (.node (.node (.leaf 240983905528932) (.leaf 0)) (.node (.leaf 212377369347350) (.leaf 277259102849829)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 111222294382098)) (.leaf 55108052012413)) (.node (.leaf 160713954224589) (.leaf 0))) (.node (.node (.leaf 247632298540881) (.leaf 523695074136171)) (.node (.leaf 0) (.leaf 109608865659866)))) (.node (.node (.node (.node (.leaf 2671770357933047) (.leaf 32721427754115)) (.leaf 0)) (.node (.leaf 191070698498398) (.leaf 540027121192620))) (.node (.node (.leaf 0) (.leaf 612137470279329)) (.node (.leaf 136924791992788) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 100432987221598) (.leaf 0)) (.leaf 833188598335968)) (.node (.leaf 0) (.leaf 208844134886371))) (.node (.node (.leaf 405347836030131) (.leaf 0)) (.node (.leaf 135979136163160) (.leaf 587279019039671)))) (.node (.node (.node (.leaf 0) (.leaf 837284714969144)) (.node (.leaf 344040967007589) (.leaf 0))) (.node (.node (.leaf 41193510495721) (.leaf 81735906282207)) (.node (.leaf 0) (.leaf 271217371622300)))))) (.node (.node (.node (.node (.node (.node (.leaf 116794084744744) (.leaf 491214339242493)) (.leaf 0)) (.node (.leaf 402547246136148) (.leaf 220324623579736))) (.node (.node (.leaf 0) (.leaf 96941714323756)) (.node (.leaf 456066712946095) (.leaf 0)))) (.node (.node (.node (.leaf 90445959668703) (.leaf 125893889890574)) (.node (.leaf 0) (.leaf 183254690018368))) (.node (.node (.leaf 1257486785189638) (.leaf 0)) (.node (.leaf 178421162315571) (.leaf 438527576264561))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 1477520758272609)) (.leaf 405972712385496)) (.node (.leaf 96727446515058) (.leaf 0))) (.node (.node (.leaf 543311290574852) (.leaf 226810642926488)) (.node (.leaf 0) (.leaf 40692268018638)))) (.node (.node (.node (.leaf 1658998698899667) (.leaf 0)) (.node (.leaf 41501405464090) (.leaf 60817251267346))) (.node (.node (.leaf 0) (.leaf 119274489013580)) (.node (.leaf 339304994175650) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 41626646974657) (.leaf 0)) (.leaf 92219025723744)) (.node (.leaf 0) (.leaf 614352264286491))) (.node (.node (.leaf 386909780124781) (.leaf 0)) (.node (.leaf 166005618691345) (.leaf 179081472405747)))) (.node (.node (.node (.leaf 0) (.leaf 364288432952099)) (.node (.leaf 557503961810072) (.leaf 0))) (.node (.node (.leaf 253458885198943) (.leaf 547699161521266)) (.node (.leaf 0) (.leaf 220432204877546))))) (.node (.node (.node (.node (.node (.leaf 370601885046945) (.leaf 113070276513535)) (.leaf 0)) (.node (.leaf 30179579260555) (.leaf 477893634911489))) (.node (.node (.leaf 0) (.leaf 131710007008600)) (.node (.leaf 417207181304390) (.leaf 0)))) (.node (.node (.node (.leaf 120718313880666) (.leaf 971677228950260)) (.node (.leaf 0) (.leaf 34259492015338))) (.node (.node (.leaf 69398808169374) (.leaf 0)) (.node (.leaf 300372323216779) (.leaf 368876096565539)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 2997676349270822)) (.leaf 426408638993240)) (.node (.leaf 502108202227019) (.leaf 0))) (.node (.node (.leaf 104843192109910) (.leaf 163294861103794)) (.node (.leaf 0) (.leaf 112099824838122)))) (.node (.node (.node (.leaf 60274148949840) (.leaf 0)) (.node (.leaf 217100315674253) (.leaf 1325114512906194))) (.node (.node (.leaf 0) (.leaf 63130400840431)) (.node (.leaf 234765362824552) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 2629166352668258) (.leaf 0)) (.leaf 747026762280688)) (.node (.leaf 0) (.leaf 334340348731266))) (.node (.node (.leaf 1375404253962768) (.leaf 0)) (.node (.leaf 32927502532926) (.leaf 117890957061147)))) (.node (.node (.node (.leaf 0) (.leaf 99560099277825)) (.node (.leaf 104301796882190) (.leaf 0))) (.node (.node (.leaf 299745525201512) (.leaf 771429713916229)) (.node (.leaf 0) (.leaf 49656225648662))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 176021958240369) (.leaf 272774332484845)) (.leaf 0)) (.node (.leaf 120289914495916) (.leaf 346862363254152))) (.node (.node (.leaf 0) (.leaf 48687721631243)) (.node (.leaf 431560720845189) (.leaf 0)))) (.node (.node (.node (.node (.leaf 56304486807285) (.leaf 0)) (.leaf 69447806813849)) (.node (.leaf 0) (.leaf 317841602126667))) (.node (.node (.leaf 314347251383246) (.leaf 0)) (.node (.leaf 382609623342980) (.leaf 394584277863278))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 448283118343433)) (.leaf 3497129464096096)) (.node (.leaf 667942591094297) (.leaf 0))) (.node (.node (.leaf 707165314343778) (.leaf 502845963524598)) (.node (.leaf 0) (.leaf 64115051008238)))) (.node (.node (.node (.leaf 402517278229014) (.leaf 0)) (.node (.leaf 47767675428291) (.leaf 130099639424714))) (.node (.node (.leaf 0) (.leaf 246945930921224)) (.node (.leaf 755902104754720) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 298763199366636) (.leaf 0)) (.leaf 347451903017891)) (.node (.leaf 0) (.leaf 31474179776647))) (.node (.node (.leaf 75953916435322) (.leaf 0)) (.node (.leaf 677199726072905) (.leaf 875553691160181)))) (.node (.node (.node (.leaf 0) (.leaf 145228201408378)) (.node (.leaf 255289769181655) (.leaf 0))) (.node (.node (.leaf 77242406444502) (.leaf 117981816455878)) (.node (.leaf 0) (.leaf 766747844064979))))) (.node (.node (.node (.node (.node (.leaf 834346787777318) (.leaf 168746695224904)) (.leaf 0)) (.node (.leaf 119316586730744) (.leaf 840257056538319))) (.node (.node (.leaf 0) (.leaf 104907844551802)) (.node (.leaf 130923770044323) (.leaf 0)))) (.node (.node (.node (.leaf 169627113732455) (.leaf 591977954720703)) (.node (.leaf 0) (.leaf 217696172391994))) (.node (.node (.leaf 1172751981649207) (.leaf 0)) (.node (.leaf 27402216821134) (.leaf 90211615397779))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 1483751484602631)) (.leaf 112743426138855)) (.node (.leaf 501814690857538) (.leaf 0))) (.node (.node (.leaf 46280075827123) (.leaf 249975928727767)) (.node (.leaf 0) (.leaf 99565522424742)))) (.node (.node (.node (.leaf 86312503307156) (.leaf 0)) (.node (.leaf 1086899300500847) (.leaf 257500523259620))) (.node (.node (.leaf 0) (.leaf 30122988903241)) (.node (.leaf 1630644820124178) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 134454813890833) (.leaf 0)) (.leaf 680648179352653)) (.node (.leaf 0) (.leaf 161616376815139))) (.node (.node (.leaf 603990248163094) (.leaf 0)) (.node (.leaf 209321179459389) (.leaf 150902225053360)))) (.node (.node (.node (.leaf 0) (.leaf 204504414586061)) (.node (.leaf 86010243323537) (.leaf 0))) (.node (.node (.leaf 287485956247876) (.leaf 150931435284279)) (.node (.leaf 0) (.leaf 60598387249733)))))) (.node (.node (.node (.node (.node (.node (.leaf 227631141792956) (.leaf 425894464812144)) (.leaf 0)) (.node (.leaf 25108247597444) (.leaf 353879747865801))) (.node (.node (.leaf 0) (.leaf 1360527117646594)) (.node (.leaf 309144707656696) (.leaf 0)))) (.node (.node (.node (.leaf 198679862128296) (.leaf 749988504092508)) (.node (.leaf 0) (.leaf 80632050875169))) (.node (.node (.leaf 138946804344649) (.leaf 0)) (.node (.leaf 101071121420190) (.leaf 307581515275215))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 238366819800812)) (.leaf 128939102541625)) (.node (.leaf 308173035098723) (.leaf 0))) (.node (.node (.leaf 180848468003853) (.leaf 1201972068470769)) (.node (.leaf 0) (.leaf 158773203463276)))) (.node (.node (.node (.leaf 345359782823074) (.leaf 0)) (.node (.leaf 201876404815850) (.leaf 683709248156031))) (.node (.node (.leaf 0) (.leaf 182989251801893)) (.node (.leaf 146819756336324) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 354179666371694) (.leaf 0)) (.leaf 377950723730240)) (.node (.leaf 0) (.leaf 1083090221010896))) (.node (.node (.leaf 946490413070524) (.leaf 0)) (.node (.leaf 44605291226443) (.leaf 87341293283299)))) (.node (.node (.node (.leaf 0) (.leaf 230581190271787)) (.node (.leaf 314371697880255) (.leaf 0))) (.node (.node (.leaf 169709505954689) (.leaf 898896503207394)) (.node (.leaf 0) (.leaf 188421757071607))))) (.node (.node (.node (.node (.node (.leaf 193869930203201) (.leaf 133623044302671)) (.leaf 0)) (.node (.leaf 355443093388762) (.leaf 796341575451050))) (.node (.node (.leaf 0) (.leaf 78092248288060)) (.node (.leaf 153783818522766) (.leaf 0)))) (.node (.node (.node (.leaf 654689230772779) (.leaf 220494632902879)) (.node (.leaf 0) (.leaf 442438238340880))) (.node (.node (.leaf 520421002518840) (.leaf 0)) (.node (.leaf 277850055573795) (.leaf 263672035064393)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 92407230858668)) (.leaf 122803585597916)) (.node (.leaf 1011789849691256) (.leaf 0))) (.node (.node (.leaf 68506225498134) (.leaf 489393650638120)) (.node (.leaf 0) (.leaf 377448331012495)))) (.node (.node (.node (.leaf 268822784611911) (.leaf 0)) (.node (.leaf 416392876714565) (.leaf 1340749507408814))) (.node (.node (.leaf 0) (.leaf 1403996327320337)) (.node (.leaf 55081157442033) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 271159116002499) (.leaf 0)) (.leaf 1225668685479095)) (.node (.leaf 0) (.leaf 45502168351383))) (.node (.node (.leaf 161108621180965) (.leaf 0)) (.node (.leaf 195388632619076) (.leaf 475407302267815)))) (.node (.node (.node (.leaf 0) (.leaf 120684081887336)) (.node (.leaf 914409232698049) (.leaf 0))) (.node (.node (.leaf 109667446547179) (.leaf 216399625635405)) (.node (.leaf 0) (.leaf 118269220152358))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 370240600165589) (.leaf 36099393015218)) (.leaf 0)) (.node (.leaf 125647236445776) (.leaf 1749288601548445))) (.node (.node (.leaf 0) (.leaf 352838341845760)) (.node (.leaf 84826250141569) (.leaf 0)))) (.node (.node (.node (.leaf 403710490321581) (.leaf 617939245285162)) (.node (.leaf 0) (.leaf 162801523357469))) (.node (.node (.leaf 277013361448852) (.leaf 0)) (.node (.leaf 29818623053813) (.leaf 326335183588813))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 190249945490871)) (.leaf 250924209341390)) (.node (.leaf 518896603993288) (.leaf 0))) (.node (.node (.leaf 64862076275032) (.leaf 50118641120663)) (.node (.leaf 0) (.leaf 224825469754614)))) (.node (.node (.node (.leaf 242730996658025) (.leaf 0)) (.node (.leaf 372510595668244) (.leaf 877339565947240))) (.node (.node (.leaf 0) (.leaf 134866557153442)) (.node (.leaf 525342742134779) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 101548382150819) (.leaf 0)) (.leaf 369380191146140)) (.node (.leaf 0) (.leaf 57653407039211))) (.node (.node (.leaf 838745530867954) (.leaf 0)) (.node (.leaf 130770279222550) (.leaf 1923716487227905)))) (.node (.node (.node (.leaf 0) (.leaf 52168829027779)) (.node (.leaf 566358627540223) (.leaf 0))) (.node (.node (.leaf 2629817469750720) (.leaf 329548078469752)) (.node (.leaf 0) (.leaf 265434750478010))))) (.node (.node (.node (.node (.node (.leaf 567507398777954) (.leaf 175395915997134)) (.leaf 0)) (.node (.leaf 135827823359151) (.leaf 72736134409538))) (.node (.node (.leaf 0) (.leaf 334111490972866)) (.node (.leaf 417076918178690) (.leaf 0)))) (.node (.node (.node (.leaf 829018406910258) (.leaf 286240170064411)) (.node (.leaf 0) (.leaf 46940921142274))) (.node (.node (.leaf 73462559792419) (.leaf 0)) (.node (.leaf 210665441793063) (.leaf 972687114591863)))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 5259430176559042)) (.leaf 162769068854773)) (.node (.leaf 243268998664632) (.leaf 0))) (.node (.node (.leaf 69596041613571) (.leaf 128173417070596)) (.node (.leaf 0) (.leaf 1422680589493231)))) (.node (.node (.node (.node (.leaf 208672554820118) (.leaf 130885707842866)) (.leaf 0)) (.node (.leaf 310001260801845) (.leaf 444889171219455))) (.node (.node (.leaf 0) (.leaf 37676528648817)) (.node (.leaf 217813523301183) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 416418438607572) (.leaf 0)) (.leaf 471563821947548)) (.node (.leaf 0) (.leaf 198624899461152))) (.node (.node (.leaf 939514710239935) (.leaf 0)) (.node (.leaf 34793692838489) (.leaf 43404125486679)))) (.node (.node (.node (.leaf 0) (.leaf 404101932687884)) (.node (.leaf 192729399538322) (.leaf 0))) (.node (.node (.leaf 137037965106085) (.leaf 528165809547887)) (.node (.leaf 0) (.leaf 91906843705527)))))) (.node (.node (.node (.node (.node (.node (.leaf 141771101865282) (.leaf 66771334227604)) (.leaf 0)) (.node (.leaf 60542416740121) (.leaf 216332682818288))) (.node (.node (.leaf 0) (.leaf 150542779678622)) (.node (.leaf 482947483915050) (.leaf 0)))) (.node (.node (.node (.leaf 124516458427926) (.leaf 591185782554311)) (.node (.leaf 0) (.leaf 58849454911748))) (.node (.node (.leaf 127190367548568) (.leaf 0)) (.node (.leaf 604775725335327) (.leaf 201363669984673))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 96929663064388)) (.leaf 123251630023532)) (.node (.leaf 974266701506627) (.leaf 0))) (.node (.node (.leaf 88648266015624) (.leaf 863931330245702)) (.node (.leaf 0) (.leaf 781851721855226)))) (.node (.node (.node (.leaf 501717539451495) (.leaf 0)) (.node (.leaf 376274107707623) (.leaf 153158119650417))) (.node (.node (.leaf 0) (.leaf 278368131785347)) (.node (.leaf 75817511078596) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 182008670663875) (.leaf 0)) (.leaf 1646559987149954)) (.node (.leaf 0) (.leaf 63772608126522))) (.node (.node (.leaf 142307606169102) (.leaf 0)) (.node (.leaf 88699747564684) (.leaf 369628916977821)))) (.node (.node (.node (.leaf 0) (.leaf 753687025208218)) (.node (.leaf 349365167063367) (.leaf 0))) (.node (.node (.leaf 47243841250218) (.leaf 97998954360376)) (.node (.leaf 0) (.leaf 412181830098785))))) (.node (.node (.node (.node (.node (.leaf 290944531223183) (.leaf 113823750591751)) (.leaf 0)) (.node (.leaf 187763681367618) (.leaf 3024724542587578))) (.node (.node (.leaf 0) (.leaf 143266282810960)) (.node (.leaf 116157391696207) (.leaf 0)))) (.node (.node (.node (.leaf 483324469540441) (.leaf 1305340728241837)) (.node (.leaf 0) (.leaf 144397569165337))) (.node (.node (.leaf 234718661522136) (.leaf 0)) (.node (.leaf 87025318488954) (.leaf 171930520463917)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 953467273997532)) (.leaf 508133821151574)) (.node (.leaf 69554321920381) (.leaf 0))) (.node (.node (.leaf 322528200472176) (.leaf 150017538986338)) (.node (.leaf 0) (.leaf 66360790621484)))) (.node (.node (.node (.leaf 378123678611298) (.leaf 0)) (.node (.leaf 210705114460001) (.leaf 129006067658569))) (.node (.node (.leaf 0) (.leaf 242393545918226)) (.node (.leaf 603608893880200) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 25997256586035) (.leaf 0)) (.leaf 759421639498732)) (.node (.leaf 0) (.leaf 108506001213110))) (.node (.node (.leaf 520398551382198) (.leaf 0)) (.node (.leaf 256460200879624) (.leaf 1562548562405998)))) (.node (.node (.node (.leaf 0) (.leaf 27828572691026)) (.node (.leaf 784098824110101) (.leaf 0))) (.node (.node (.leaf 360792060199740) (.leaf 360846455236044)) (.node (.leaf 0) (.leaf 674986777785340)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 294757954440252) (.leaf 33824624105261)) (.leaf 0)) (.node (.leaf 207896204011265) (.leaf 756215535054909))) (.node (.node (.leaf 0) (.leaf 1465906600827184)) (.node (.leaf 60916990825213) (.leaf 0)))) (.node (.node (.node (.leaf 72760365181513) (.leaf 270596986420904)) (.node (.leaf 0) (.leaf 135298493210452))) (.node (.node (.leaf 2931813201654367) (.leaf 0)) (.node (.leaf 124125619330546) (.leaf 67649248210522))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 407793005529920)) (.leaf 147378977220126)) (.node (.leaf 735254743441693) (.leaf 0))) (.node (.node (.leaf 65052626121919) (.leaf 103948103538689)) (.node (.leaf 0) (.leaf 378107767527455)))) (.node (.node (.node (.leaf 79361721344384) (.leaf 0)) (.node (.leaf 200451499048609) (.leaf 910589999116806))) (.node (.node (.leaf 0) (.leaf 30458495412607)) (.node (.leaf 3095090637557491) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 101192395738231) (.leaf 0)) (.leaf 217655708644207)) (.node (.leaf 0) (.leaf 1547545318778746))) (.node (.node (.leaf 516024264196555) (.leaf 0)) (.node (.leaf 265443159331904) (.leaf 593447405720874)))) (.node (.node (.node (.leaf 0) (.leaf 39680860672192)) (.node (.leaf 301946978871042) (.leaf 0))) (.node (.node (.leaf 345553889697339) (.leaf 687722075927395)) (.node (.leaf 0) (.leaf 455294999558403))))) (.node (.node (.node (.node (.node (.leaf 1352502146122323) (.leaf 203896502764960)) (.leaf 0)) (.node (.leaf 28790385100221) (.leaf 73689489880141))) (.node (.node (.leaf 0) (.leaf 367627371720847)) (.node (.leaf 173616495617377) (.leaf 0)))) (.node (.node (.node (.leaf 235397816453338) (.leaf 391782525213602)) (.node (.leaf 0) (.leaf 51974051769345))) (.node (.node (.leaf 206494187136416) (.leaf 0)) (.node (.leaf 113479860030393) (.leaf 387718645873265))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 227647501183501)) (.leaf 32750998770835)) (.node (.leaf 286532565621920) (.leaf 0))) (.node (.node (.leaf 717720277932067) (.leaf 288795138330673)) (.node (.leaf 0) (.leaf 343861037963698)))) (.node (.node (.node (.leaf 1507374050416436) (.leaf 0)) (.node (.leaf 195997905671941) (.leaf 824363660197569))) (.node (.node (.leaf 0) (.leaf 150973489435521)) (.node (.leaf 127545216253044) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 1518843275840637) (.leaf 0)) (.leaf 217012002426220)) (.node (.leaf 0) (.leaf 108827854322104))) (.node (.node (.leaf 55657145382051) (.leaf 0)) (.node (.leaf 415460669450502) (.leaf 1349973555570680)))) (.node (.node (.node (.leaf 0) (.leaf 258012132098278)) (.node (.leaf 484787091836452) (.leaf 0))) (.node (.node (.leaf 99542697704628) (.leaf 132721581242968)) (.node (.leaf 0) (.leaf 296723702860437)))))) (.node (.node (.node (.node (.node (.node (.leaf 246503260047064) (.leaf 193859322936633)) (.leaf 0)) (.node (.leaf 91799847000959) (.leaf 1563703443710452))) (.node (.node (.leaf 0) (.leaf 103247093568208)) (.node (.leaf 556736263570694) (.leaf 0)))) (.node (.node (.node (.leaf 48432494430944) (.leaf 117698909823495)) (.node (.leaf 0) (.leaf 195891262606801))) (.node (.node (.leaf 301085559357244) (.leaf 0)) (.node (.leaf 432665362581227) (.leaf 133542668455208))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 261771415685731)) (.leaf 676251073061162)) (.node (.leaf 75353057297633) (.leaf 0))) (.node (.node (.leaf 256346830928874) (.leaf 2845361178986461)) (.node (.leaf 0) (.leaf 36844744940071)))) (.node (.node (.node (.leaf 808203865375767) (.leaf 0)) (.node (.leaf 28858011313497) (.leaf 183813687411054))) (.node (.node (.leaf 0) (.leaf 86808247808689)) (.node (.leaf 397249798922303) (.leaf 0))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 52816301737721) (.leaf 0)) (.leaf 417688269772742)) (.node (.leaf 0) (.leaf 108906761650592))) (.node (.node (.leaf 1674569429938288) (.leaf 0)) (.node (.leaf 163471809472329) (.leaf 542434743244600)))) (.node (.node (.node (.node (.leaf 0) (.leaf 65442855508229)) (.leaf 104336277410059)) (.node (.leaf 1224274940558657) (.leaf 0))) (.node (.node (.leaf 144534905997640) (.leaf 219217731319731)) (.node (.leaf 0) (.leaf 222444585609728))))) (.node (.node (.node (.node (.node (.leaf 811945424770992) (.leaf 2629715088279521)) (.leaf 0)) (.node (.leaf 60150412232430) (.leaf 81384536037276))) (.node (.node (.leaf 0) (.leaf 121634499332316)) (.node (.leaf 238548978027160) (.leaf 0)))) (.node (.node (.node (.leaf 251787776719128) (.leaf 366509380036735)) (.node (.leaf 0) (.leaf 64086708535298))) (.node (.node (.leaf 193883428647512) (.leaf 0)) (.node (.leaf 343545519746103) (.leaf 982428678484986)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 226140553027069)) (.leaf 955787266660978)) (.node (.leaf 263420014017199) (.leaf 0))) (.node (.node (.leaf 33602848839106) (.leaf 68518984030676)) (.node (.leaf 0) (.leaf 264082904773944)))) (.node (.node (.node (.leaf 728576865904198) (.leaf 0)) (.node (.leaf 145213496020471) (.leaf 440864409755092))) (.node (.node (.leaf 0) (.leaf 96364699769161)) (.node (.leaf 1228704528572982) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 1366347543464278) (.leaf 0)) (.leaf 668680697462531)) (.node (.leaf 0) (.leaf 235781910973774))) (.node (.node (.leaf 199120198555650) (.leaf 0)) (.node (.leaf 108619130125453) (.leaf 99312451297324)))) (.node (.node (.node (.leaf 0) (.leaf 469757355119968)) (.node (.leaf 126260801680861) (.leaf 0))) (.node (.node (.leaf 326589719029551) (.leaf 224199649676244)) (.node (.leaf 0) (.leaf 21702062743340))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 75194723589952) (.leaf 100681834992337)) (.leaf 0)) (.node (.leaf 215282889811950) (.leaf 615607408889753))) (.node (.node (.leaf 0) (.leaf 63595183774284)) (.node (.leaf 445694652110291) (.leaf 0)))) (.node (.node (.node (.leaf 145176810764732) (.leaf 62258230815729)) (.node (.leaf 0) (.leaf 295592891277156))) (.node (.node (.leaf 868953034656724) (.leaf 0)) (.node (.leaf 779982317921114) (.leaf 1518831548326364))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 288454882493184)) (.leaf 70885550932641)) (.node (.leaf 104547389597292) (.leaf 0))) (.node (.node (.leaf 153517563526188) (.leaf 5250961620889368)) (.node (.leaf 0) (.leaf 108166341409144)))) (.node (.node (.node (.leaf 795734701257410) (.leaf 0)) (.node (.leaf 26139446191304) (.leaf 75271390853703))) (.node (.node (.leaf 0) (.leaf 241473741957525)) (.node (.leaf 442922326752099) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 114467756488682) (.leaf 0)) (.leaf 2921663528184745)) (.node (.leaf 0) (.leaf 37908755539298))) (.node (.node (.leaf 60952135155513) (.leaf 0)) (.node (.leaf 640911470020446) (.leaf 262007983937257)))) (.node (.node (.node (.leaf 0) (.leaf 250858769725748)) (.node (.leaf 993004948287868) (.leaf 0))) (.node (.node (.leaf 61174207136354) (.leaf 188137055302910)) (.node (.leaf 0) (.leaf 76579059825209))))) (.node (.node (.node (.node (.node (.leaf 278349536516115) (.leaf 48464831532194)) (.leaf 0)) (.node (.leaf 304457529389727) (.leaf 217296961231635))) (.node (.node (.leaf 0) (.leaf 487133350753314)) (.node (.leaf 76677996978674) (.leaf 0)))) (.node (.node (.node (.leaf 221689336719120) (.leaf 696202541476099)) (.node (.leaf 0) (.leaf 431965665122851))) (.node (.node (.leaf 544718085906149) (.leaf 0)) (.node (.leaf 76950926869529) (.leaf 390925862540452)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 267246088605341)) (.leaf 191233998852921)) (.node (.leaf 156184496576120) (.leaf 0))) (.node (.node (.leaf 440989262604917) (.leaf 884876476681759)) (.node (.leaf 0) (.leaf 48999477180188)))) (.node (.node (.node (.leaf 461162380543574) (.leaf 0)) (.node (.leaf 143104420034854) (.leaf 376843514143214))) (.node (.node (.leaf 0) (.leaf 174682583531684)) (.node (.leaf 2166180442021791) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 33721334195213) (.leaf 0)) (.leaf 91004336702766)) (.node (.leaf 0) (.leaf 823279993574977))) (.node (.node (.leaf 241368163774672) (.leaf 0)) (.node (.leaf 432799248521254) (.leaf 236538440304715)))) (.node (.node (.node (.leaf 0) (.leaf 71153803084551)) (.node (.leaf 2807992654640674) (.leaf 0))) (.node (.node (.leaf 145611881133993) (.leaf 754896662024989)) (.node (.leaf 0) (.leaf 184814458488911)))))) (.node (.node (.node (.node (.node (.node (.leaf 501848418682779) (.leaf 85965260231959)) (.leaf 0)) (.node (.leaf 100237279308418) (.leaf 449650939509227))) (.node (.node (.leaf 0) (.leaf 117359330761068)) (.node (.leaf 269733114306884) (.leaf 0)))) (.node (.node (.node (.leaf 952490210331638) (.leaf 325603046714937)) (.node (.leaf 0) (.leaf 652670364120919))) (.node (.node (.leaf 705676683691519) (.leaf 0)) (.node (.leaf 55365291546331) (.leaf 72198786030435))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 350791831994268)) (.leaf 145472265611592)) (.node (.leaf 668222981945731) (.leaf 0))) (.node (.node (.leaf 114301154837562) (.leaf 93881842284548)) (.node (.leaf 0) (.leaf 1512362271293789)))) (.node (.node (.node (.leaf 104337658055557) (.leaf 0)) (.node (.leaf 282062493837095) (.leaf 530869500956019))) (.node (.node (.leaf 0) (.leaf 58078695848104)) (.node (.leaf 115306814078422) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 175773722986363) (.leaf 0)) (.leaf 323232753630277)) (.node (.leaf 0) (.leaf 301804446940100))) (.node (.node (.leaf 409008829172121) (.leaf 0)) (.node (.leaf 53094343101523) (.leaf 121196774499466)))) (.node (.node (.node (.leaf 0) (.leaf 189061839305649)) (.node (.leaf 60245977806481) (.leaf 0))) (.node (.node (.leaf 499951854370940) (.leaf 199131044849483)) (.node (.leaf 0) (.leaf 64503033829285))))) (.node (.node (.node (.node (.node (.leaf 257878205083250) (.leaf 476733636998766)) (.leaf 0)) (.node (.leaf 378895053785229) (.leaf 317546406926551))) (.node (.node (.leaf 0) (.leaf 34777160960191)) (.node (.leaf 365978503603786) (.leaf 0)))) (.node (.node (.node (.leaf 30001362375998) (.leaf 161264101750338)) (.node (.leaf 0) (.leaf 75008769493169))) (.node (.node (.leaf 2721054235293188) (.leaf 0)) (.node (.leaf 707759492759423) (.leaf 851788929624287)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 337493390449807)) (.leaf 36056861084836)) (.node (.leaf 209815689103603) (.leaf 0))) (.node (.node (.leaf 1093413888400934) (.leaf 435392344783988)) (.node (.leaf 0) (.leaf 180423227618022)))) (.node (.node (.node (.leaf 290456402816756) (.leaf 0)) (.node (.leaf 235963629728263) (.leaf 1533495688129958))) (.node (.node (.leaf 0) (.leaf 392049412055051)) (.node (.leaf 62948359553294) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 138895611055682) (.leaf 0)) (.leaf 635683204253333)) (.node (.leaf 0) (.leaf 379710819749366))) (.node (.node (.leaf 97375443262486) (.leaf 0)) (.node (.leaf 113633828742688) (.leaf 545548664969690)))) (.node (.node (.node (.leaf 0) (.leaf 260199275691099)) (.node (.leaf 493891861842447) (.leaf 0))) (.node (.node (.leaf 59425913417479) (.leaf 128230102016475)) (.node (.leaf 0) (.leaf 781274281202999))))))))))))

/-- Complete enclosure tree, with one leaf per residue. -/
def levelSevenRoots : Entries :=
  (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 8909917)) (.leaf 6300263)) (.node (.leaf 28431357) (.leaf 0))) (.node (.node (.leaf 20104006) (.leaf 21273446)) (.node (.leaf 0) (.leaf 24515017)))) (.node (.node (.node (.node (.leaf 20944021) (.leaf 10917116)) (.leaf 0)) (.node (.leaf 15042598) (.leaf 41237512))) (.node (.node (.leaf 0) (.leaf 12413160)) (.node (.leaf 17334735) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 14809660) (.leaf 0)) (.leaf 12706601)) (.node (.leaf 0) (.leaf 8567957))) (.node (.node (.leaf 10636723) (.leaf 0)) (.node (.leaf 29159325) (.leaf 20899527)))) (.node (.node (.node (.leaf 0) (.leaf 13140773)) (.node (.leaf 20893921) (.leaf 0))) (.node (.node (.leaf 12257509) (.leaf 10046801)) (.node (.leaf 0) (.leaf 18489312)))))) (.node (.node (.node (.node (.node (.node (.leaf 10472011) (.leaf 12401241)) (.leaf 0)) (.node (.leaf 8984924) (.leaf 15843862))) (.node (.node (.leaf 0) (.leaf 8335071)) (.node (.leaf 32913283) (.leaf 0)))) (.node (.node (.node (.leaf 7521299) (.leaf 9966942)) (.node (.leaf 0) (.leaf 19364769))) (.node (.node (.leaf 22967315) (.leaf 0)) (.node (.leaf 14778198) (.leaf 18615807))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 15984635)) (.leaf 10668439)) (.node (.leaf 9291930) (.leaf 0))) (.node (.node (.leaf 14774233) (.leaf 43652209)) (.node (.leaf 0) (.leaf 13301875)))) (.node (.node (.node (.leaf 14837318) (.leaf 0)) (.node (.leaf 7104161) (.leaf 26081863))) (.node (.node (.leaf 0) (.leaf 12432714)) (.node (.leaf 52862841) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 7404830) (.leaf 0)) (.leaf 8769002)) (.node (.leaf 0) (.leaf 28553852))) (.node (.node (.leaf 21248030) (.leaf 0)) (.node (.leaf 11203302) (.leaf 34497162)))) (.node (.node (.node (.leaf 0) (.leaf 6569342)) (.node (.leaf 14629312) (.leaf 0))) (.node (.node (.leaf 23273206) (.leaf 26732057)) (.node (.leaf 0) (.leaf 11346818))))) (.node (.node (.node (.node (.node (.leaf 19968357) (.leaf 27237397)) (.leaf 0)) (.node (.leaf 7047693) (.leaf 7508110))) (.node (.node (.leaf 0) (.leaf 15840056)) (.node (.leaf 15022050) (.leaf 0)))) (.node (.node (.node (.leaf 16240344) (.leaf 22171461)) (.node (.leaf 0) (.leaf 11179802))) (.node (.node (.leaf 10449764) (.leaf 0)) (.node (.leaf 13163364) (.leaf 37922134)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 55174507)) (.leaf 11302844)) (.node (.leaf 19864621) (.leaf 0))) (.node (.node (.leaf 6570387) (.leaf 11989287)) (.node (.leaf 0) (.leaf 8687101)))) (.node (.node (.node (.leaf 10446961) (.leaf 0)) (.node (.leaf 30866773) (.leaf 17514568))) (.node (.node (.leaf 0) (.leaf 6557830)) (.node (.leaf 22379460) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 10491568) (.leaf 0)) (.leaf 20001476)) (.node (.leaf 0) (.leaf 18447875))) (.node (.node (.leaf 27293523) (.leaf 0)) (.node (.leaf 18442662) (.leaf 8989338)))) (.node (.node (.node (.leaf 0) (.leaf 17378007)) (.node (.leaf 8791256) (.leaf 0))) (.node (.node (.leaf 37379674) (.leaf 18349305)) (.node (.leaf 0) (.leaf 8686260)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 17994344) (.leaf 14046073)) (.leaf 0)) (.node (.leaf 6200621) (.leaf 13831299))) (.node (.node (.leaf 0) (.leaf 12536891)) (.node (.leaf 23703464) (.leaf 0)))) (.node (.node (.node (.node (.leaf 15024626) (.leaf 0)) (.leaf 30807389)) (.node (.leaf 0) (.leaf 5892700))) (.node (.node (.leaf 7921931) (.leaf 0)) (.node (.leaf 24393177) (.leaf 15836486))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 11678492)) (.leaf 9381417)) (.node (.leaf 20248285) (.leaf 0))) (.node (.node (.leaf 10344486) (.leaf 26899214)) (.node (.leaf 0) (.leaf 13169328)))) (.node (.node (.node (.leaf 18248649) (.leaf 0)) (.node (.leaf 18902419) (.leaf 12360343))) (.node (.node (.leaf 0) (.leaf 14689465)) (.node (.leaf 8023412) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 14119761) (.leaf 0)) (.leaf 21223475)) (.node (.leaf 0) (.leaf 19440964))) (.node (.node (.leaf 21916980) (.leaf 0)) (.node (.leaf 5309036) (.leaf 11111840)))) (.node (.node (.node (.leaf 0) (.leaf 14186566)) (.node (.leaf 11200611) (.leaf 0))) (.node (.node (.leaf 10622194) (.leaf 36436804)) (.node (.leaf 0) (.leaf 8065347))))) (.node (.node (.node (.node (.node (.leaf 11483658) (.leaf 14971358)) (.leaf 0)) (.node (.leaf 15677590) (.leaf 72370670))) (.node (.node (.leaf 0) (.leaf 18274882)) (.node (.leaf 27111486) (.leaf 0)))) (.node (.node (.node (.leaf 7389099) (.leaf 18803794)) (.node (.leaf 0) (.leaf 15856324))) (.node (.node (.leaf 28502405) (.leaf 0)) (.node (.leaf 26814998) (.leaf 25661189))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 23595939)) (.leaf 39014269)) (.node (.leaf 7992318) (.leaf 0))) (.node (.node (.leaf 14046408) (.leaf 14370207)) (.node (.leaf 0) (.leaf 7680554)))) (.node (.node (.node (.leaf 35306005) (.leaf 0)) (.node (.leaf 8477706) (.leaf 8521391))) (.node (.node (.leaf 0) (.leaf 11298004)) (.node (.leaf 14421444) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 7387117) (.leaf 0)) (.leaf 12222177)) (.node (.leaf 0) (.leaf 13180515))) (.node (.node (.leaf 28452402) (.leaf 0)) (.node (.leaf 12384670) (.leaf 37905550)))) (.node (.node (.node (.leaf 0) (.leaf 6162545)) (.node (.leaf 41787431) (.leaf 0))) (.node (.node (.leaf 15824668) (.leaf 19684003)) (.node (.leaf 0) (.leaf 20923118)))))) (.node (.node (.node (.node (.node (.node (.leaf 20555545) (.leaf 6716086)) (.leaf 0)) (.node (.leaf 14143179) (.leaf 22884356))) (.node (.node (.leaf 0) (.leaf 24215202)) (.node (.leaf 13044618) (.leaf 0)))) (.node (.node (.node (.leaf 19299435) (.leaf 34079532)) (.node (.leaf 0) (.leaf 17204331))) (.node (.node (.leaf 17467240) (.leaf 0)) (.node (.leaf 6356422) (.leaf 10433029))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 14537275)) (.leaf 20424823)) (.node (.leaf 16424697) (.leaf 0))) (.node (.node (.leaf 6216357) (.leaf 7723879)) (.node (.leaf 0) (.leaf 20497038)))) (.node (.node (.node (.leaf 26431421) (.leaf 0)) (.node (.leaf 12974918) (.leaf 15492285))) (.node (.node (.leaf 0) (.leaf 8090852)) (.node (.leaf 23357259) (.leaf 0))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 12723923) (.leaf 0)) (.leaf 27165028)) (.node (.leaf 0) (.leaf 14440861))) (.node (.node (.leaf 21200152) (.leaf 0)) (.node (.leaf 9780205) (.leaf 12925005)))) (.node (.node (.node (.node (.leaf 0) (.leaf 39271327)) (.leaf 16844991)) (.node (.leaf 8864921) (.leaf 0))) (.node (.node (.leaf 16760881) (.leaf 12587928)) (.node (.leaf 0) (.leaf 6030595))))) (.node (.node (.node (.node (.node (.leaf 10624015) (.leaf 22053199)) (.leaf 0)) (.node (.leaf 21784114) (.leaf 15367340))) (.node (.node (.leaf 0) (.leaf 6060634)) (.node (.leaf 35484541) (.leaf 0)))) (.node (.node (.node (.leaf 5601651) (.leaf 20359500)) (.node (.leaf 0) (.leaf 11963281))) (.node (.node (.leaf 20423019) (.leaf 0)) (.node (.leaf 11198087) (.leaf 24567486)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 11520303)) (.leaf 8257941)) (.node (.leaf 15674840) (.leaf 0))) (.node (.node (.leaf 14317700) (.leaf 40266504)) (.node (.leaf 0) (.leaf 12836435)))) (.node (.node (.node (.leaf 21614263) (.leaf 0)) (.node (.leaf 19020617) (.leaf 45289442))) (.node (.node (.leaf 0) (.leaf 16827933)) (.node (.leaf 9312121) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 12903744) (.leaf 0)) (.leaf 35161013)) (.node (.leaf 0) (.leaf 13590074))) (.node (.node (.leaf 13366029) (.leaf 0)) (.node (.leaf 8740082) (.leaf 16661190)))) (.node (.node (.node (.leaf 0) (.leaf 20478593)) (.node (.leaf 15527286) (.leaf 0))) (.node (.node (.leaf 5673409) (.leaf 8086108)) (.node (.leaf 0) (.leaf 31013840))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 26534654) (.leaf 12773708)) (.leaf 0)) (.node (.leaf 15007264) (.leaf 29121895))) (.node (.node (.leaf 0) (.leaf 11768887)) (.node (.leaf 13746837) (.leaf 0)))) (.node (.node (.node (.leaf 15497645) (.leaf 17430309)) (.node (.leaf 0) (.leaf 17577532))) (.node (.node (.leaf 40185546) (.leaf 0)) (.node (.leaf 7857257) (.leaf 9022238))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 37676238)) (.leaf 13605893)) (.node (.leaf 18580905) (.leaf 0))) (.node (.node (.leaf 7920028) (.leaf 7926136)) (.node (.leaf 0) (.leaf 29574386)))) (.node (.node (.node (.leaf 7511025) (.leaf 0)) (.node (.leaf 25764711) (.leaf 23575140))) (.node (.node (.leaf 0) (.leaf 6512536)) (.node (.leaf 23857129) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 8120172) (.leaf 0)) (.leaf 10586349)) (.node (.leaf 0) (.leaf 16207140))) (.node (.node (.leaf 27847437) (.leaf 0)) (.node (.leaf 51173792) (.leaf 21082385)))) (.node (.node (.node (.leaf 0) (.leaf 11016602)) (.node (.leaf 29794869) (.leaf 0))) (.node (.node (.leaf 19170716) (.leaf 25385715)) (.node (.leaf 0) (.leaf 20944446))))) (.node (.node (.node (.node (.node (.leaf 15349048) (.leaf 9753204)) (.leaf 0)) (.node (.leaf 13296291) (.leaf 11200987))) (.node (.node (.leaf 0) (.leaf 16107399)) (.node (.leaf 31159654) (.leaf 0)))) (.node (.node (.node (.leaf 20154244) (.leaf 17771306)) (.node (.leaf 0) (.leaf 5005929))) (.node (.node (.leaf 18961067) (.leaf 0)) (.node (.leaf 18145201) (.leaf 17142061)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 13831653)) (.leaf 16684849)) (.node (.leaf 28891006) (.leaf 0))) (.node (.node (.leaf 5651422) (.leaf 9211665)) (.node (.leaf 0) (.leaf 21200195)))) (.node (.node (.node (.leaf 9932311) (.leaf 0)) (.node (.leaf 10161271) (.leaf 22555742))) (.node (.node (.leaf 0) (.leaf 12537379)) (.node (.leaf 24870962) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 24965116) (.leaf 0)) (.leaf 23858551)) (.node (.leaf 0) (.leaf 13746831))) (.node (.node (.leaf 21101320) (.leaf 0)) (.node (.leaf 6025534) (.leaf 23271122)))) (.node (.node (.node (.leaf 0) (.leaf 21754200)) (.node (.leaf 7988896) (.leaf 0))) (.node (.node (.leaf 10197501) (.leaf 30416409)) (.node (.leaf 0) (.leaf 6608378)))))) (.node (.node (.node (.node (.node (.node (.leaf 29089521) (.leaf 11481987)) (.leaf 0)) (.node (.leaf 8642384) (.leaf 11786647))) (.node (.node (.leaf 0) (.leaf 16131042)) (.node (.leaf 17817040) (.leaf 0)))) (.node (.node (.node (.leaf 20118887) (.leaf 21331915)) (.node (.leaf 0) (.leaf 10499873))) (.node (.node (.leaf 8757284) (.leaf 0)) (.node (.leaf 26803271) (.leaf 28739812))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 8173832)) (.leaf 9845556)) (.node (.leaf 19171965) (.leaf 0))) (.node (.node (.leaf 29548176) (.leaf 14920744)) (.node (.leaf 0) (.leaf 19954218)))) (.node (.node (.node (.leaf 31400845) (.leaf 0)) (.node (.leaf 13918692) (.leaf 31452043))) (.node (.node (.leaf 0) (.leaf 8768804)) (.node (.leaf 14794879) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 14534965) (.leaf 0)) (.leaf 26107081)) (.node (.leaf 0) (.leaf 5247912))) (.node (.node (.leaf 10000738) (.leaf 0)) (.node (.leaf 16181684) (.leaf 27848406)))) (.node (.node (.node (.leaf 0) (.leaf 11593593)) (.node (.leaf 53984327) (.leaf 0))) (.node (.node (.leaf 9223938) (.leaf 14429014)) (.node (.leaf 0) (.leaf 25891597))))) (.node (.node (.node (.node (.node (.leaf 17342979) (.leaf 6797325)) (.leaf 0)) (.node (.leaf 24097868) (.leaf 21436951))) (.node (.node (.leaf 0) (.leaf 22492109)) (.node (.leaf 12165299) (.leaf 0)))) (.node (.node (.node (.leaf 12351204) (.leaf 15614370)) (.node (.leaf 0) (.leaf 15642789))) (.node (.node (.leaf 30214331) (.leaf 0)) (.node (.leaf 7377266) (.leaf 13737692)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 24994760)) (.leaf 10279406)) (.node (.leaf 14442531) (.leaf 0))) (.node (.node (.leaf 11614015) (.leaf 27611656)) (.node (.leaf 0) (.leaf 10401914)))) (.node (.node (.node (.leaf 29554266) (.leaf 0)) (.node (.leaf 5461607) (.leaf 7768015))) (.node (.node (.leaf 0) (.leaf 21382344)) (.node (.leaf 20429162) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 18689837) (.leaf 0)) (.leaf 11643864)) (.node (.leaf 0) (.leaf 24755492))) (.node (.node (.leaf 32117174) (.leaf 0)) (.node (.leaf 10954700) (.leaf 20054958)))) (.node (.node (.node (.leaf 0) (.leaf 8975206)) (.node (.leaf 11591032) (.leaf 0))) (.node (.node (.leaf 16516076) (.leaf 19735800)) (.node (.leaf 0) (.leaf 15417641)))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 22007711) (.leaf 7677596)) (.leaf 0)) (.node (.leaf 19208576) (.leaf 25088423))) (.node (.node (.leaf 0) (.leaf 26224076)) (.node (.leaf 10211231) (.leaf 0)))) (.node (.node (.node (.node (.leaf 14990771) (.leaf 0)) (.leaf 41056558)) (.node (.leaf 0) (.leaf 19326495))) (.node (.node (.leaf 17726789) (.leaf 0)) (.node (.leaf 9139359) (.leaf 12929431))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 16925511)) (.leaf 27769022)) (.node (.leaf 15176399) (.leaf 0))) (.node (.node (.leaf 6268446) (.leaf 12242254)) (.node (.leaf 0) (.leaf 19639625)))) (.node (.node (.node (.leaf 11851732) (.leaf 0)) (.node (.leaf 8901010) (.leaf 15194213))) (.node (.node (.leaf 0) (.leaf 7221558)) (.node (.leaf 36010684) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 7512313) (.leaf 0)) (.leaf 15593967)) (.node (.leaf 0) (.leaf 10834329))) (.node (.node (.leaf 21936347) (.leaf 0)) (.node (.leaf 10866350) (.leaf 30788368)))) (.node (.node (.node (.leaf 0) (.leaf 5489725)) (.node (.leaf 41337521) (.leaf 0))) (.node (.node (.leaf 25091360) (.leaf 14460829)) (.node (.leaf 0) (.leaf 25740188))))) (.node (.node (.node (.node (.node (.leaf 22470662) (.leaf 38714832)) (.leaf 0)) (.node (.leaf 14396340) (.leaf 14601518))) (.node (.node (.leaf 0) (.leaf 15844687)) (.node (.leaf 33835416) (.leaf 0)))) (.node (.node (.node (.leaf 14441255) (.leaf 16010698)) (.node (.leaf 0) (.leaf 9035897))) (.node (.node (.leaf 7918243) (.leaf 0)) (.node (.leaf 17371836) (.leaf 20609579))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 10498386)) (.leaf 8146085)) (.node (.leaf 22254542) (.leaf 0))) (.node (.node (.leaf 11083786) (.leaf 19548438)) (.node (.leaf 0) (.leaf 16548402)))) (.node (.node (.node (.leaf 14172720) (.leaf 0)) (.node (.leaf 28472718) (.leaf 16491158))) (.node (.node (.leaf 0) (.leaf 16695868)) (.node (.leaf 9076730) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 15283592) (.leaf 0)) (.leaf 28374188)) (.node (.leaf 0) (.leaf 6790399))) (.node (.node (.leaf 13449607) (.leaf 0)) (.node (.leaf 32024472) (.leaf 18890271)))) (.node (.node (.node (.leaf 0) (.leaf 13908807)) (.node (.leaf 32963959) (.leaf 0))) (.node (.node (.leaf 6584664) (.leaf 9110588)) (.node (.leaf 0) (.leaf 9462597)))))) (.node (.node (.node (.node (.node (.node (.leaf 9124325) (.leaf 13580798)) (.leaf 0)) (.node (.leaf 24862591) (.leaf 18221176))) (.node (.node (.leaf 0) (.leaf 5890621)) (.node (.leaf 22514835) (.leaf 0)))) (.node (.node (.node (.leaf 9451210) (.leaf 7769116)) (.node (.leaf 0) (.leaf 22041748))) (.node (.node (.leaf 15538232) (.leaf 0)) (.node (.leaf 11781240) (.leaf 24510093))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 29203036)) (.leaf 13612529)) (.node (.leaf 14480552) (.leaf 0))) (.node (.node (.leaf 10979449) (.leaf 20837482)) (.node (.leaf 0) (.leaf 15457905)))) (.node (.node (.node (.leaf 72514363) (.leaf 0)) (.node (.leaf 5717742) (.leaf 8115110))) (.node (.node (.leaf 0) (.leaf 14443116)) (.node (.leaf 24484507) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 18762834) (.leaf 0)) (.leaf 15510636)) (.node (.leaf 0) (.leaf 8274201))) (.node (.node (.leaf 10611738) (.leaf 0)) (.node (.leaf 20592289) (.leaf 27662597)))) (.node (.node (.node (.node (.leaf 0) (.leaf 83631687)) (.leaf 36549764)) (.node (.leaf 37607588) (.leaf 0))) (.node (.node (.leaf 9720482) (.leaf 9774219)) (.node (.leaf 0) (.leaf 16432090))))) (.node (.node (.node (.node (.node (.leaf 24444354) (.leaf 7457289)) (.leaf 0)) (.node (.leaf 12325090) (.leaf 36802167))) (.node (.node (.leaf 0) (.leaf 8964206)) (.node (.leaf 12429192) (.leaf 0)))) (.node (.node (.node (.leaf 28415472) (.leaf 15447757)) (.node (.leaf 0) (.leaf 16181704))) (.node (.node (.leaf 18418856) (.leaf 0)) (.node (.leaf 6379686) (.leaf 7403002)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 15016220)) (.leaf 26641123)) (.node (.leaf 9620819) (.leaf 0))) (.node (.node (.leaf 13138684) (.leaf 46624014)) (.node (.leaf 0) (.leaf 6392805)))) (.node (.node (.node (.leaf 16398465) (.leaf 0)) (.node (.leaf 5604624) (.leaf 20460752))) (.node (.node (.leaf 0) (.leaf 13115658)) (.node (.leaf 23978572) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 5311097) (.leaf 0)) (.leaf 7086360)) (.node (.leaf 0) (.leaf 20410642))) (.node (.node (.leaf 19933884) (.leaf 0)) (.node (.leaf 16670142) (.leaf 14217674)))) (.node (.node (.node (.leaf 0) (.leaf 14236360)) (.node (.leaf 19018332) (.leaf 0))) (.node (.node (.leaf 16869538) (.leaf 20093602)) (.node (.leaf 0) (.leaf 17135913))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 26615021) (.leaf 14807559)) (.leaf 0)) (.node (.leaf 7485680) (.leaf 9445136))) (.node (.node (.leaf 0) (.leaf 25074757)) (.node (.leaf 18423328) (.leaf 0)))) (.node (.node (.node (.leaf 19691112) (.leaf 26662450)) (.node (.leaf 0) (.leaf 7933912))) (.node (.node (.leaf 36185335) (.leaf 0)) (.node (.leaf 14907498) (.leaf 23573293))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 15671860)) (.leaf 7641796)) (.node (.leaf 11705232) (.leaf 0))) (.node (.node (.leaf 21068154) (.leaf 28858028)) (.node (.leaf 0) (.leaf 10495824)))) (.node (.node (.node (.leaf 23287728) (.leaf 0)) (.node (.leaf 17950411) (.leaf 19768088))) (.node (.node (.leaf 0) (.leaf 15100774)) (.node (.leaf 14809960) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 10853416) (.leaf 0)) (.leaf 15852271)) (.node (.leaf 0) (.leaf 13025072))) (.node (.node (.leaf 28415155) (.leaf 0)) (.node (.leaf 7920294) (.leaf 7722516)))) (.node (.node (.node (.leaf 0) (.leaf 28801031)) (.node (.leaf 11389652) (.leaf 0))) (.node (.node (.leaf 22033202) (.leaf 27295077)) (.node (.leaf 0) (.leaf 5514402))))) (.node (.node (.node (.node (.node (.leaf 14251203) (.leaf 27180147)) (.leaf 0)) (.node (.leaf 12566211) (.leaf 16172216))) (.node (.node (.leaf 0) (.leaf 6954404)) (.node (.leaf 72523341) (.leaf 0)))) (.node (.node (.node (.leaf 13407499) (.leaf 16481980)) (.node (.leaf 0) (.leaf 10649194))) (.node (.node (.leaf 40718999) (.leaf 0)) (.node (.leaf 12121268) (.leaf 20526347))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 18042676)) (.leaf 9780456)) (.node (.leaf 11797970) (.leaf 0))) (.node (.node (.leaf 20429027) (.leaf 24899850)) (.node (.leaf 0) (.leaf 8724356)))) (.node (.node (.node (.node (.leaf 28858914) (.leaf 29004511)) (.leaf 0)) (.node (.leaf 6513631) (.leaf 8341906))) (.node (.node (.leaf 0) (.leaf 19633105)) (.node (.leaf 16555239) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 7023205) (.leaf 0)) (.leaf 11003856)) (.node (.leaf 0) (.leaf 13319144))) (.node (.node (.leaf 15780777) (.leaf 0)) (.node (.leaf 15949318) (.leaf 34778607)))) (.node (.node (.node (.leaf 0) (.leaf 9604288)) (.node (.leaf 13315275) (.leaf 0))) (.node (.node (.leaf 17586426) (.leaf 27432613)) (.node (.leaf 0) (.leaf 12314018)))))) (.node (.node (.node (.node (.node (.node (.leaf 19079239) (.leaf 10391892)) (.leaf 0)) (.node (.leaf 16870543) (.leaf 13319141))) (.node (.node (.leaf 0) (.leaf 23530993)) (.node (.leaf 9720478) (.leaf 0)))) (.node (.node (.node (.leaf 14920887) (.leaf 19378529)) (.node (.leaf 0) (.leaf 15241876))) (.node (.node (.leaf 31090979) (.leaf 0)) (.node (.leaf 16455169) (.leaf 13192826))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 31878953)) (.leaf 11794433)) (.node (.leaf 25397961) (.leaf 0))) (.node (.node (.leaf 5649002) (.leaf 20528279)) (.node (.leaf 0) (.leaf 12674328)))) (.node (.node (.node (.leaf 7210723) (.leaf 0)) (.node (.leaf 21507649) (.leaf 22647747))) (.node (.node (.leaf 0) (.leaf 9663248)) (.node (.leaf 26862318) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 20569398) (.leaf 0)) (.leaf 20390989)) (.node (.leaf 0) (.leaf 11037844))) (.node (.node (.leaf 12063198) (.leaf 0)) (.node (.leaf 8334418) (.leaf 15755991)))) (.node (.node (.node (.leaf 0) (.leaf 33167141)) (.node (.leaf 11406369) (.leaf 0))) (.node (.node (.leaf 12598550) (.leaf 20022563)) (.node (.leaf 0) (.leaf 7919261))))) (.node (.node (.node (.node (.node (.leaf 14226201) (.leaf 20864118)) (.leaf 0)) (.node (.leaf 15083942) (.leaf 23040971))) (.node (.node (.leaf 0) (.leaf 13884511)) (.node (.leaf 26288929) (.leaf 0)))) (.node (.node (.node (.leaf 6192335) (.leaf 7588200)) (.node (.leaf 0) (.leaf 12959667))) (.node (.node (.leaf 21697826) (.leaf 0)) (.node (.leaf 20322116) (.leaf 15065183)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 8093331)) (.leaf 5779772)) (.node (.leaf 37887209) (.leaf 0))) (.node (.node (.leaf 13556627) (.leaf 19798885)) (.node (.leaf 0) (.leaf 15971551)))) (.node (.node (.node (.leaf 55115212) (.leaf 0)) (.node (.leaf 10550559) (.leaf 28825707))) (.node (.node (.leaf 0) (.leaf 15807352)) (.node (.leaf 14109763) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 22203751) (.leaf 0)) (.leaf 13549897)) (.node (.leaf 0) (.leaf 5349481))) (.node (.node (.leaf 9842002) (.leaf 0)) (.node (.leaf 22239953) (.leaf 29416505)))) (.node (.node (.node (.leaf 0) (.leaf 12276242)) (.node (.leaf 22642740) (.leaf 0))) (.node (.node (.leaf 10461559) (.leaf 7597107)) (.node (.leaf 0) (.leaf 19548128)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 10277773) (.leaf 28902882)) (.leaf 0)) (.node (.leaf 18460494) (.leaf 18081583))) (.node (.node (.leaf 0) (.leaf 5433176)) (.node (.leaf 17002054) (.leaf 0)))) (.node (.node (.node (.leaf 7071590) (.leaf 10968174)) (.node (.leaf 0) (.leaf 9417169))) (.node (.node (.leaf 22440490) (.leaf 0)) (.node (.leaf 19691797) (.leaf 26212422))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 43721557)) (.leaf 15180889)) (.node (.leaf 8197909) (.leaf 0))) (.node (.node (.leaf 38172684) (.leaf 17041919)) (.node (.leaf 0) (.leaf 13964082)))) (.node (.node (.node (.leaf 52275187) (.leaf 0)) (.node (.leaf 10202854) (.leaf 14739005))) (.node (.node (.leaf 0) (.leaf 15890929)) (.node (.leaf 25557376) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 12263338) (.leaf 0)) (.leaf 20750080)) (.node (.leaf 0) (.leaf 12870094))) (.node (.node (.leaf 17039766) (.leaf 0)) (.node (.leaf 15158214) (.leaf 39496388)))) (.node (.node (.node (.leaf 0) (.leaf 14460110)) (.node (.leaf 17522418) (.leaf 0))) (.node (.node (.leaf 8602166) (.leaf 7230415)) (.node (.leaf 0) (.leaf 14605000))))) (.node (.node (.node (.node (.node (.leaf 15130616) (.leaf 5017017)) (.leaf 0)) (.node (.leaf 11041027) (.leaf 35802555))) (.node (.node (.leaf 0) (.leaf 39121489)) (.node (.leaf 11061122) (.leaf 0)))) (.node (.node (.node (.leaf 21364758) (.leaf 24676205)) (.node (.leaf 0) (.leaf 12383699))) (.node (.node (.leaf 21056559) (.leaf 0)) (.node (.leaf 9714015) (.leaf 12405719))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 19556790)) (.leaf 17673964)) (.node (.leaf 29698124) (.leaf 0))) (.node (.node (.leaf 10212412) (.leaf 16917708)) (.node (.leaf 0) (.leaf 51065391)))) (.node (.node (.node (.leaf 8212349) (.leaf 0)) (.node (.leaf 19524389) (.leaf 29421056))) (.node (.node (.leaf 0) (.leaf 7922344)) (.node (.leaf 17065280) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 20898022) (.leaf 0)) (.leaf 14158904)) (.node (.leaf 0) (.leaf 23226413))) (.node (.node (.leaf 43646082) (.leaf 0)) (.node (.leaf 5492816) (.leaf 10522861)))) (.node (.node (.node (.leaf 0) (.leaf 10560162)) (.node (.leaf 15119601) (.leaf 0))) (.node (.node (.leaf 14445599) (.leaf 23751316)) (.node (.leaf 0) (.leaf 7769713)))))) (.node (.node (.node (.node (.node (.node (.leaf 18749599) (.leaf 11774106)) (.leaf 0)) (.node (.leaf 8233455) (.leaf 10304790))) (.node (.node (.leaf 0) (.leaf 10976883)) (.node (.leaf 31621255) (.leaf 0)))) (.node (.node (.node (.leaf 22710271) (.leaf 27527988)) (.node (.leaf 0) (.leaf 6195111))) (.node (.node (.leaf 7746143) (.leaf 0)) (.node (.leaf 14180997) (.leaf 37623384))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 8491980)) (.leaf 7220628)) (.node (.leaf 46763531) (.leaf 0))) (.node (.node (.leaf 8196097) (.leaf 21723887)) (.node (.leaf 0) (.leaf 11220371)))) (.node (.node (.node (.leaf 16667070) (.leaf 0)) (.node (.leaf 13955318) (.leaf 15075400))) (.node (.node (.leaf 0) (.leaf 29201801)) (.node (.leaf 10901919) (.leaf 0))))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 15561802) (.leaf 0)) (.leaf 18836114)) (.node (.leaf 0) (.leaf 6191850))) (.node (.node (.leaf 13582514) (.leaf 0)) (.node (.leaf 17740194) (.leaf 17414651)))) (.node (.node (.node (.node (.leaf 0) (.leaf 41018573)) (.leaf 11797236)) (.node (.leaf 27765403) (.leaf 0))) (.node (.node (.leaf 7220431) (.leaf 12338103)) (.node (.leaf 0) (.leaf 10423459))))) (.node (.node (.node (.node (.node (.leaf 16679847) (.leaf 13980806)) (.leaf 0)) (.node (.leaf 29031371) (.leaf 17924206))) (.node (.node (.leaf 0) (.leaf 16503305)) (.node (.leaf 13665896) (.leaf 0)))) (.node (.node (.node (.leaf 12534733) (.leaf 21555268)) (.node (.leaf 0) (.leaf 18657473))) (.node (.node (.leaf 33277849) (.leaf 0)) (.node (.leaf 9142489) (.leaf 14696355)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 29506319)) (.leaf 11968144)) (.node (.leaf 19635664) (.leaf 0))) (.node (.node (.leaf 10731335) (.leaf 18327736)) (.node (.leaf 0) (.leaf 9698894)))) (.node (.node (.node (.leaf 46905420) (.leaf 0)) (.node (.leaf 8656581) (.leaf 11199527))) (.node (.node (.leaf 0) (.leaf 22282336)) (.node (.leaf 15609868) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 8380441) (.leaf 0)) (.leaf 7565308)) (.node (.leaf 0) (.leaf 38220829))) (.node (.node (.leaf 17361228) (.leaf 0)) (.node (.leaf 10743931) (.leaf 27645228)))) (.node (.node (.node (.leaf 0) (.leaf 5520514)) (.node (.leaf 22354972) (.leaf 0))) (.node (.node (.leaf 25463399) (.leaf 22587184)) (.node (.leaf 0) (.leaf 11445698))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 21469018) (.leaf 27557500)) (.leaf 0)) (.node (.leaf 11026600) (.leaf 19748194))) (.node (.node (.leaf 0) (.leaf 20844101)) (.node (.leaf 22473167) (.leaf 0)))) (.node (.node (.node (.leaf 15511340) (.leaf 13317888)) (.node (.leaf 0) (.leaf 5579348))) (.node (.node (.leaf 7683670) (.leaf 0)) (.node (.leaf 21770664) (.leaf 40874847))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 7095134)) (.leaf 6131669)) (.node (.leaf 55326141) (.leaf 0))) (.node (.node (.leaf 29230042) (.leaf 17513195)) (.node (.leaf 0) (.leaf 17544336)))) (.node (.node (.node (.leaf 20449684) (.leaf 0)) (.node (.leaf 10225350) (.leaf 20654589))) (.node (.node (.leaf 0) (.leaf 14928072)) (.node (.leaf 18201062) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 15889157) (.leaf 0)) (.leaf 32847108)) (.node (.leaf 0) (.leaf 14881572))) (.node (.node (.leaf 14934324) (.leaf 0)) (.node (.leaf 10324833) (.leaf 10988034)))) (.node (.node (.node (.leaf 0) (.leaf 19946613)) (.node (.leaf 11203886) (.leaf 0))) (.node (.node (.leaf 23925252) (.leaf 72217368)) (.node (.leaf 0) (.leaf 6134794))))) (.node (.node (.node (.node (.node (.leaf 10211510) (.leaf 12009473)) (.leaf 0)) (.node (.leaf 11321273) (.leaf 15868001))) (.node (.node (.leaf 0) (.leaf 7230055)) (.node (.leaf 41297583) (.leaf 0)))) (.node (.node (.node (.leaf 5599044) (.leaf 8761210)) (.node (.leaf 0) (.leaf 51239446))) (.node (.node (.leaf 15523657) (.leaf 0)) (.node (.leaf 14573173) (.leaf 16651100)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 10546199)) (.leaf 7423480)) (.node (.leaf 12677301) (.leaf 0))) (.node (.node (.leaf 15736337) (.leaf 22884385)) (.node (.leaf 0) (.leaf 10469426)))) (.node (.node (.node (.node (.leaf 51689171) (.leaf 5720265)) (.leaf 0)) (.node (.leaf 13822833) (.leaf 23238484))) (.node (.node (.leaf 0) (.leaf 24741413)) (.node (.leaf 11701487) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 10021626) (.leaf 0)) (.leaf 28865007)) (.node (.leaf 0) (.leaf 14451441))) (.node (.node (.leaf 20133252) (.leaf 0)) (.node (.leaf 11661010) (.leaf 24233841)))) (.node (.node (.node (.leaf 0) (.leaf 28935873)) (.node (.leaf 18548342) (.leaf 0))) (.node (.node (.leaf 6418218) (.leaf 9040792)) (.node (.leaf 0) (.leaf 16468679)))))) (.node (.node (.node (.node (.node (.node (.leaf 10807132) (.leaf 22163356)) (.leaf 0)) (.node (.leaf 20063581) (.leaf 14843336))) (.node (.node (.leaf 0) (.leaf 9845899)) (.node (.leaf 21355719) (.leaf 0)))) (.node (.node (.node (.leaf 9510309) (.leaf 11220245)) (.node (.leaf 0) (.leaf 13537160))) (.node (.node (.leaf 35461061) (.leaf 0)) (.node (.leaf 13357439) (.leaf 20941051))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 38438533)) (.leaf 20148765)) (.node (.leaf 9835012) (.leaf 0))) (.node (.node (.leaf 23309039) (.leaf 15060234)) (.node (.leaf 0) (.leaf 6379050)))) (.node (.node (.node (.leaf 40730808) (.leaf 0)) (.node (.leaf 6442159) (.leaf 7798542))) (.node (.node (.leaf 0) (.leaf 10921287)) (.node (.leaf 18420234) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 6451872) (.leaf 0)) (.leaf 9603074)) (.node (.leaf 0) (.leaf 24786131))) (.node (.node (.leaf 19670023) (.leaf 0)) (.node (.leaf 12884317) (.leaf 13382133)))) (.node (.node (.node (.leaf 0) (.leaf 19086342)) (.node (.leaf 23611522) (.leaf 0))) (.node (.node (.leaf 15920393) (.leaf 23402974)) (.node (.leaf 0) (.leaf 14846960))))) (.node (.node (.node (.node (.node (.leaf 19251023) (.leaf 10633451)) (.leaf 0)) (.node (.leaf 5493595) (.leaf 21860779))) (.node (.node (.leaf 0) (.leaf 11476499)) (.node (.leaf 20425651) (.leaf 0)))) (.node (.node (.node (.leaf 10987189) (.leaf 31171738)) (.node (.leaf 0) (.leaf 5853161))) (.node (.node (.leaf 8330595) (.leaf 0)) (.node (.leaf 17331253) (.leaf 19206148)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 54751040)) (.leaf 20649665)) (.node (.leaf 22407772) (.leaf 0))) (.node (.node (.leaf 10239297) (.leaf 12778688)) (.node (.leaf 0) (.leaf 10587721)))) (.node (.node (.node (.leaf 7763643) (.leaf 0)) (.node (.leaf 14734325) (.leaf 36402123))) (.node (.node (.leaf 0) (.leaf 7945465)) (.node (.leaf 15322055) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 51275398) (.leaf 0)) (.leaf 27331791)) (.node (.leaf 0) (.leaf 18284977))) (.node (.node (.leaf 37086443) (.leaf 0)) (.node (.leaf 5738250) (.leaf 10857761)))) (.node (.node (.node (.leaf 0) (.leaf 9977981)) (.node (.leaf 10212826) (.leaf 0))) (.node (.node (.leaf 17313161) (.leaf 27774624)) (.node (.leaf 0) (.leaf 7046718))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 13267327) (.leaf 16515882)) (.leaf 0)) (.node (.leaf 10967676) (.leaf 18624242))) (.node (.node (.leaf 0) (.leaf 6977659)) (.node (.leaf 20774040) (.leaf 0)))) (.node (.node (.node (.node (.leaf 7503632) (.leaf 0)) (.leaf 8333536)) (.node (.leaf 0) (.leaf 17828113))) (.node (.node (.leaf 17729841) (.leaf 0)) (.node (.leaf 19560410) (.leaf 19864146))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 21172698)) (.leaf 59136533)) (.node (.leaf 25844586) (.leaf 0))) (.node (.node (.leaf 26592581) (.leaf 22424228)) (.node (.leaf 0) (.leaf 8007188)))) (.node (.node (.node (.leaf 20062834) (.leaf 0)) (.node (.leaf 6911417) (.leaf 11406123))) (.node (.node (.leaf 0) (.leaf 15714514)) (.node (.leaf 27493674) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 17284768) (.leaf 0)) (.leaf 18640062)) (.node (.leaf 0) (.leaf 5610186))) (.node (.node (.leaf 8715155) (.leaf 0)) (.node (.leaf 26023062) (.leaf 29589757)))) (.node (.node (.node (.leaf 0) (.leaf 12051067)) (.node (.leaf 15977790) (.leaf 0))) (.node (.node (.leaf 8788766) (.leaf 10861944)) (.node (.leaf 0) (.leaf 27690213))))) (.node (.node (.node (.node (.node (.leaf 28885062) (.leaf 12990254)) (.leaf 0)) (.node (.leaf 10923214) (.leaf 28987188))) (.node (.node (.leaf 0) (.leaf 10242454)) (.node (.leaf 11442193) (.leaf 0)))) (.node (.node (.node (.leaf 13024098) (.leaf 24330598)) (.node (.leaf 0) (.leaf 14754531))) (.node (.node (.leaf 34245467) (.leaf 0)) (.node (.leaf 5234713) (.leaf 9497980))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 38519495)) (.leaf 10618071)) (.node (.leaf 22401221) (.leaf 0))) (.node (.node (.leaf 6802947) (.leaf 15810628)) (.node (.leaf 0) (.leaf 9978253)))) (.node (.node (.node (.leaf 9290453) (.leaf 0)) (.node (.leaf 32968156) (.leaf 16046823))) (.node (.node (.leaf 0) (.leaf 5488442)) (.node (.leaf 40381244) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 11595466) (.leaf 0)) (.leaf 26089235)) (.node (.leaf 0) (.leaf 12712843))) (.node (.node (.leaf 24576214) (.leaf 0)) (.node (.leaf 14467937) (.leaf 12284227)))) (.node (.node (.node (.leaf 0) (.leaf 14300504)) (.node (.leaf 9274171) (.leaf 0))) (.node (.node (.leaf 16955411) (.leaf 12285416)) (.node (.leaf 0) (.leaf 7784497)))))) (.node (.node (.node (.node (.node (.node (.leaf 15087450) (.leaf 20637211)) (.leaf 0)) (.node (.leaf 5010814) (.leaf 18811692))) (.node (.node (.leaf 0) (.leaf 36885324)) (.node (.leaf 17582512) (.leaf 0)))) (.node (.node (.node (.leaf 14095385) (.leaf 27385918)) (.node (.leaf 0) (.leaf 8979536))) (.node (.node (.leaf 11787570) (.leaf 0)) (.node (.leaf 10053414) (.leaf 17538003))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 15439133)) (.leaf 11355136)) (.node (.leaf 17554858) (.leaf 0))) (.node (.node (.leaf 13447992) (.leaf 34669469)) (.node (.leaf 0) (.leaf 12600524)))) (.node (.node (.node (.leaf 18583859) (.leaf 0)) (.node (.leaf 14208322) (.leaf 26147835))) (.node (.node (.leaf 0) (.leaf 13527352)) (.node (.leaf 12116921) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 18819662) (.leaf 0)) (.leaf 19440955)) (.node (.leaf 0) (.leaf 32910337))) (.node (.node (.leaf 30765085) (.leaf 0)) (.node (.leaf 6678720) (.leaf 9345657)))) (.node (.node (.node (.leaf 0) (.leaf 15184901)) (.node (.leaf 17730531) (.leaf 0))) (.node (.node (.leaf 13027261) (.leaf 29981603)) (.node (.leaf 0) (.leaf 13726681))))) (.node (.node (.node (.node (.node (.leaf 13923719) (.leaf 11559544)) (.leaf 0)) (.node (.leaf 18853199) (.leaf 28219525))) (.node (.node (.leaf 0) (.leaf 8836982)) (.node (.leaf 12400961) (.leaf 0)))) (.node (.node (.node (.leaf 25586896) (.leaf 14849062)) (.node (.leaf 0) (.leaf 21034216))) (.node (.node (.leaf 22812738) (.leaf 0)) (.node (.leaf 16668835) (.leaf 16237982)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 9612868)) (.leaf 11081678)) (.node (.leaf 31808645) (.leaf 0))) (.node (.node (.leaf 8276849) (.leaf 22122244)) (.node (.leaf 0) (.leaf 19428030)))) (.node (.node (.node (.leaf 16395817) (.leaf 0)) (.node (.leaf 20405707) (.leaf 36616247))) (.node (.node (.leaf 0) (.leaf 37469939)) (.node (.leaf 7421669) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 16466910) (.leaf 0)) (.leaf 35009552)) (.node (.leaf 0) (.leaf 6745530))) (.node (.node (.leaf 12692858) (.leaf 0)) (.node (.leaf 13978149) (.leaf 21803837)))) (.node (.node (.node (.leaf 0) (.leaf 10985631)) (.node (.leaf 30239201) (.leaf 0))) (.node (.node (.leaf 10472223) (.leaf 14710528)) (.node (.leaf 0) (.leaf 10875166))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 19241638) (.leaf 6008278)) (.leaf 0)) (.node (.leaf 11209248) (.leaf 41824498))) (.node (.node (.leaf 0) (.leaf 18783992)) (.node (.leaf 9210117) (.leaf 0)))) (.node (.node (.node (.leaf 20092549) (.leaf 24858384)) (.node (.leaf 0) (.leaf 12759371))) (.node (.node (.leaf 16643719) (.leaf 0)) (.node (.leaf 5460644) (.leaf 18064750))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 13793113)) (.leaf 15840588)) (.node (.leaf 22779303) (.leaf 0))) (.node (.node (.leaf 8053700) (.leaf 7079453)) (.node (.leaf 0) (.leaf 14994182)))) (.node (.node (.node (.leaf 15579827) (.leaf 0)) (.node (.leaf 19300534) (.leaf 29619919))) (.node (.node (.leaf 0) (.leaf 11613207)) (.node (.leaf 22920357) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 10077122) (.leaf 0)) (.leaf 19219267)) (.node (.leaf 0) (.leaf 7592985))) (.node (.node (.leaf 28961104) (.leaf 0)) (.node (.leaf 11435484) (.leaf 43860193)))) (.node (.node (.node (.leaf 0) (.leaf 7222800)) (.node (.leaf 23798291) (.leaf 0))) (.node (.node (.leaf 51281746) (.leaf 18153460)) (.node (.leaf 0) (.leaf 16292169))))) (.node (.node (.node (.node (.node (.leaf 23822414) (.leaf 13243713)) (.leaf 0)) (.node (.leaf 11654520) (.leaf 8528549))) (.node (.node (.leaf 0) (.leaf 18278717)) (.node (.leaf 20422462) (.leaf 0)))) (.node (.node (.node (.leaf 28792680) (.leaf 16918634)) (.node (.leaf 0) (.leaf 6851345))) (.node (.node (.leaf 8571031) (.leaf 0)) (.node (.leaf 14514319) (.leaf 31187933)))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 72521929)) (.leaf 12758099)) (.node (.leaf 15597084) (.leaf 0))) (.node (.node (.leaf 8342425) (.leaf 11321370)) (.node (.leaf 0) (.leaf 37718439)))) (.node (.node (.node (.node (.leaf 14445503) (.leaf 11440530)) (.leaf 0)) (.node (.leaf 17606853) (.leaf 21092397))) (.node (.node (.leaf 0) (.leaf 6138121)) (.node (.leaf 14758507) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 20406334) (.leaf 0)) (.leaf 21715521)) (.node (.leaf 0) (.leaf 14093435))) (.node (.node (.leaf 30651505) (.leaf 0)) (.node (.leaf 5898618) (.leaf 6588181)))) (.node (.node (.node (.leaf 0) (.leaf 20102287)) (.node (.leaf 13882702) (.leaf 0))) (.node (.node (.leaf 11706322) (.leaf 22981859)) (.node (.leaf 0) (.leaf 9586806)))))) (.node (.node (.node (.node (.node (.node (.leaf 11906768) (.leaf 8171373)) (.leaf 0)) (.node (.leaf 7780901) (.leaf 14708253))) (.node (.node (.leaf 0) (.leaf 12269588)) (.node (.leaf 21976067) (.leaf 0)))) (.node (.node (.node (.leaf 11158695) (.leaf 24314313)) (.node (.leaf 0) (.leaf 7671340))) (.node (.node (.leaf 11277871) (.leaf 0)) (.node (.leaf 24592189) (.leaf 14190267))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 9845287)) (.leaf 11101876)) (.node (.leaf 31213246) (.leaf 0))) (.node (.node (.leaf 9415321) (.leaf 29392709)) (.node (.leaf 0) (.leaf 27961612)))) (.node (.node (.node (.leaf 22399053) (.leaf 0)) (.node (.leaf 19397787) (.leaf 12375707))) (.node (.node (.leaf 0) (.leaf 16684368)) (.node (.leaf 8707326) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 13491059) (.leaf 0)) (.leaf 40577827)) (.node (.leaf 0) (.leaf 7985776))) (.node (.node (.leaf 11929276) (.leaf 0)) (.node (.leaf 9418055) (.leaf 19225736)))) (.node (.node (.node (.leaf 0) (.leaf 27453361)) (.node (.leaf 18691313) (.leaf 0))) (.node (.node (.leaf 6873416) (.leaf 9899443)) (.node (.leaf 0) (.leaf 20302262))))) (.node (.node (.node (.node (.node (.leaf 17057097) (.leaf 10668822)) (.leaf 0)) (.node (.leaf 13702689) (.leaf 54997496))) (.node (.node (.leaf 0) (.leaf 11969390)) (.node (.leaf 10777634) (.leaf 0)))) (.node (.node (.node (.leaf 21984642) (.leaf 36129500)) (.node (.leaf 0) (.leaf 12016554))) (.node (.node (.leaf 15320531) (.leaf 0)) (.node (.leaf 9328737) (.leaf 13112228)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 30878266)) (.leaf 22541824)) (.node (.leaf 8339924) (.leaf 0))) (.node (.node (.leaf 17959071) (.leaf 12248165)) (.node (.leaf 0) (.leaf 8146214)))) (.node (.node (.node (.leaf 19445403) (.leaf 0)) (.node (.leaf 14515686) (.leaf 11358084))) (.node (.node (.leaf 0) (.leaf 15568994)) (.node (.leaf 24568454) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 5098751) (.leaf 0)) (.leaf 27557606)) (.node (.leaf 0) (.leaf 10416622))) (.node (.node (.leaf 22812246) (.leaf 0)) (.node (.leaf 16014375) (.leaf 39529086)))) (.node (.node (.node (.leaf 0) (.leaf 5275280)) (.node (.leaf 28001765) (.leaf 0))) (.node (.node (.leaf 18994528) (.leaf 18995959)) (.node (.leaf 0) (.leaf 25980508)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 17168517) (.leaf 5815895)) (.leaf 0)) (.node (.leaf 14418607) (.leaf 27499374))) (.node (.node (.leaf 0) (.leaf 38287160)) (.node (.leaf 7804934) (.leaf 0)))) (.node (.node (.node (.leaf 8529969) (.leaf 16449833)) (.node (.leaf 0) (.leaf 11631789))) (.node (.node (.leaf 54146221) (.leaf 0)) (.node (.leaf 11141168) (.leaf 8224917))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 20193886)) (.leaf 12139975)) (.node (.leaf 27115582) (.leaf 0))) (.node (.node (.leaf 8065521) (.leaf 10195495)) (.node (.leaf 0) (.leaf 19444994)))) (.node (.node (.node (.leaf 8908520) (.leaf 0)) (.node (.leaf 14158090) (.leaf 30175984))) (.node (.node (.leaf 0) (.leaf 5518922)) (.node (.leaf 55633539) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 10059444) (.leaf 0)) (.leaf 14753160)) (.node (.leaf 0) (.leaf 39338853))) (.node (.node (.leaf 22716168) (.leaf 0)) (.node (.leaf 16292427) (.leaf 24360776)))) (.node (.node (.node (.leaf 0) (.leaf 6299275)) (.node (.leaf 17376622) (.leaf 0))) (.node (.node (.leaf 18589080) (.leaf 26224456)) (.node (.leaf 0) (.leaf 21337643))))) (.node (.node (.node (.node (.node (.leaf 36776381) (.leaf 14279234)) (.leaf 0)) (.node (.leaf 5365668) (.leaf 8584259))) (.node (.node (.leaf 0) (.leaf 19173612)) (.node (.leaf 13176362) (.leaf 0)))) (.node (.node (.node (.leaf 15342680) (.leaf 19793498)) (.node (.leaf 0) (.leaf 7209304))) (.node (.node (.leaf 14369906) (.leaf 0)) (.node (.leaf 10652693) (.leaf 19690573))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 15087992)) (.leaf 5722849)) (.node (.leaf 16927273) (.leaf 0))) (.node (.node (.leaf 26790302) (.leaf 16993974)) (.node (.leaf 0) (.leaf 18543491)))) (.node (.node (.node (.leaf 38824916) (.leaf 0)) (.node (.leaf 13999926) (.leaf 28711734))) (.node (.node (.leaf 0) (.leaf 12287127)) (.node (.leaf 11293592) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 38972340) (.leaf 0)) (.leaf 14731328)) (.node (.leaf 0) (.leaf 10432059))) (.node (.node (.leaf 7460372) (.leaf 0)) (.node (.leaf 20382853) (.leaf 36741987)))) (.node (.node (.node (.leaf 0) (.leaf 16062757)) (.node (.leaf 22017882) (.leaf 0))) (.node (.node (.leaf 9977109) (.leaf 11520486)) (.node (.leaf 0) (.leaf 17225670)))))) (.node (.node (.node (.node (.node (.node (.leaf 15700423) (.leaf 13923338)) (.leaf 0)) (.node (.leaf 9581224) (.leaf 39543691))) (.node (.node (.leaf 0) (.leaf 10161058)) (.node (.leaf 23595260) (.leaf 0)))) (.node (.node (.node (.leaf 6959346) (.leaf 10848913)) (.node (.leaf 0) (.leaf 13996116))) (.node (.node (.leaf 17351818) (.leaf 0)) (.node (.leaf 20800610) (.leaf 11556067))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 16179352)) (.leaf 26004828)) (.node (.leaf 8680614) (.leaf 0))) (.node (.node (.leaf 16010835) (.leaf 53341928)) (.node (.leaf 0) (.leaf 6069988)))) (.node (.node (.node (.leaf 28428927) (.leaf 0)) (.node (.leaf 5371966) (.leaf 13557791))) (.node (.node (.leaf 0) (.leaf 9317095)) (.node (.leaf 19931127) (.leaf 0))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 7267483) (.leaf 0)) (.leaf 20437424)) (.node (.leaf 0) (.leaf 10435841))) (.node (.node (.leaf 40921504) (.leaf 0)) (.node (.leaf 12785610) (.leaf 23290229)))) (.node (.node (.node (.node (.leaf 0) (.leaf 8089676)) (.leaf 10214514)) (.node (.leaf 34989641) (.leaf 0))) (.node (.node (.leaf 12022268) (.leaf 14806004)) (.node (.leaf 0) (.leaf 14914577))))) (.node (.node (.node (.node (.node (.leaf 28494657) (.leaf 51280748)) (.leaf 0)) (.node (.leaf 7755670) (.leaf 9021338))) (.node (.node (.leaf 0) (.leaf 11028804)) (.node (.leaf 15445031) (.leaf 0)))) (.node (.node (.node (.leaf 15867823) (.leaf 19144435)) (.node (.leaf 0) (.leaf 8005418))) (.node (.node (.leaf 13924203) (.leaf 0)) (.node (.leaf 18534981) (.leaf 31343719)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 15037971)) (.leaf 30915810)) (.node (.leaf 16230220) (.leaf 0))) (.node (.node (.leaf 5796797) (.leaf 8277620)) (.node (.leaf 0) (.leaf 16250628)))) (.node (.node (.node (.leaf 26992164) (.leaf 0)) (.node (.leaf 12050457) (.leaf 20996772))) (.node (.node (.leaf 0) (.leaf 9816553)) (.node (.leaf 35052882) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 36964139) (.leaf 0)) (.leaf 25858862)) (.node (.leaf 0) (.leaf 15355192))) (.node (.node (.leaf 14110996) (.leaf 0)) (.node (.leaf 10422051) (.leaf 9965564)))) (.node (.node (.node (.leaf 0) (.leaf 21673887)) (.node (.leaf 11236584) (.leaf 0))) (.node (.node (.leaf 18071794) (.leaf 14973298)) (.node (.leaf 0) (.leaf 4658548))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 8671490) (.leaf 10034034)) (.leaf 0)) (.node (.leaf 14672522) (.leaf 24811438))) (.node (.node (.leaf 0) (.leaf 7974659)) (.node (.leaf 21111482) (.leaf 0)))) (.node (.node (.node (.leaf 12048935) (.leaf 7890389)) (.node (.leaf 0) (.leaf 17192816))) (.node (.node (.leaf 29478010) (.leaf 0)) (.node (.leaf 27928164) (.leaf 38972190))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 16983960)) (.leaf 8419356)) (.node (.leaf 10224842) (.leaf 0))) (.node (.node (.leaf 12390221) (.leaf 72463520)) (.node (.leaf 0) (.leaf 10400305)))) (.node (.node (.node (.leaf 28208770) (.leaf 0)) (.node (.leaf 5112676) (.leaf 8675909))) (.node (.node (.leaf 0) (.leaf 15539426)) (.node (.leaf 21045720) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 10698961) (.leaf 0)) (.leaf 54052415)) (.node (.leaf 0) (.leaf 6157009))) (.node (.node (.leaf 7807185) (.leaf 0)) (.node (.leaf 25316230) (.leaf 16186661)))) (.node (.node (.node (.leaf 0) (.leaf 15838522)) (.node (.leaf 31511982) (.leaf 0))) (.node (.node (.leaf 7821395) (.leaf 13716307)) (.node (.leaf 0) (.leaf 8750947))))) (.node (.node (.node (.node (.node (.leaf 16683811) (.leaf 6961669)) (.leaf 0)) (.node (.leaf 17448712) (.leaf 14740996))) (.node (.node (.leaf 0) (.leaf 22071098)) (.node (.leaf 8756598) (.leaf 0)))) (.node (.node (.node (.leaf 14889236) (.leaf 26385651)) (.node (.leaf 0) (.leaf 20783784))) (.node (.node (.leaf 23339197) (.leaf 0)) (.node (.leaf 8772168) (.leaf 19771846)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 16347664)) (.leaf 13828739)) (.node (.leaf 12497380) (.leaf 0))) (.node (.node (.leaf 20999745) (.leaf 29746874)) (.node (.leaf 0) (.leaf 6999963)))) (.node (.node (.node (.leaf 21474692) (.leaf 0)) (.node (.leaf 11962626) (.leaf 19412458))) (.node (.node (.leaf 0) (.leaf 13216754)) (.node (.leaf 46542244) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 5807008) (.leaf 0)) (.leaf 9539620)) (.node (.leaf 0) (.leaf 28692857))) (.node (.node (.leaf 15536028) (.leaf 0)) (.node (.leaf 20803828) (.leaf 15379807)))) (.node (.node (.node (.leaf 0) (.leaf 8435272)) (.node (.leaf 52990496) (.leaf 0))) (.node (.node (.leaf 12066975) (.leaf 27475383)) (.node (.leaf 0) (.leaf 13594649)))))) (.node (.node (.node (.node (.node (.node (.leaf 22401974) (.leaf 9271746)) (.leaf 0)) (.node (.leaf 10011857) (.leaf 21204975))) (.node (.node (.leaf 0) (.leaf 10833252)) (.node (.leaf 16423554) (.leaf 0)))) (.node (.node (.node (.leaf 30862441) (.leaf 18044475)) (.node (.leaf 0) (.leaf 25547415))) (.node (.node (.leaf 26564576) (.leaf 0)) (.node (.leaf 7440786) (.leaf 8496987))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 18729438)) (.leaf 12061189)) (.node (.leaf 25850010) (.leaf 0))) (.node (.node (.leaf 10691172) (.leaf 9689265)) (.node (.leaf 0) (.leaf 38889103)))) (.node (.node (.node (.leaf 10214581) (.leaf 0)) (.node (.leaf 16794717) (.leaf 23040606))) (.node (.node (.leaf 0) (.leaf 7620938)) (.node (.leaf 10738102) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 13257969) (.leaf 0)) (.leaf 17978675)) (.node (.leaf 0) (.leaf 17372520))) (.node (.node (.leaf 20223967) (.leaf 0)) (.node (.leaf 7286587) (.leaf 11008941)))) (.node (.node (.node (.leaf 0) (.leaf 13749976)) (.node (.leaf 7761829) (.leaf 0))) (.node (.node (.leaf 22359604) (.leaf 14111380)) (.node (.leaf 0) (.leaf 8031379))))) (.node (.node (.node (.node (.node (.leaf 16058587) (.leaf 21834231)) (.leaf 0)) (.node (.leaf 19465227) (.leaf 17819832))) (.node (.node (.leaf 0) (.leaf 5897217)) (.node (.leaf 19130565) (.leaf 0)))) (.node (.node (.node (.leaf 5477350) (.leaf 12698981)) (.node (.leaf 0) (.leaf 8660761))) (.node (.node (.leaf 52163726) (.leaf 0)) (.node (.leaf 26603750) (.leaf 29185424)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 18370994)) (.leaf 6004737)) (.node (.leaf 14485017) (.leaf 0))) (.node (.node (.leaf 33066810) (.leaf 20866058)) (.node (.leaf 0) (.leaf 13432172)))) (.node (.node (.node (.leaf 17042782) (.leaf 0)) (.node (.leaf 15361108) (.leaf 39159874))) (.node (.node (.leaf 0) (.leaf 19800238)) (.node (.leaf 7934001) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 11785399) (.leaf 0)) (.leaf 25212759)) (.node (.leaf 0) (.leaf 19486170))) (.node (.node (.leaf 9867900) (.leaf 0)) (.node (.leaf 10659917) (.leaf 23356984)))) (.node (.node (.node (.leaf 0) (.leaf 16130694)) (.node (.leaf 22223678) (.leaf 0))) (.node (.node (.leaf 7708821) (.leaf 11323874)) (.node (.leaf 0) (.leaf 27951285))))))))))))

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_0 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 0 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_16 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 16 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_32 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 32 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_48 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 48 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_64 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 64 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_80 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 80 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_96 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 96 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_112 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 112 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_128 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 128 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_144 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 144 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_160 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 160 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_176 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 176 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_192 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 192 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_208 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 208 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_224 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 224 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_240 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 240 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_256 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 256 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_272 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 272 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_288 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 288 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_304 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 304 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_320 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 320 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_336 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 336 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_352 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 352 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_368 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 368 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_384 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 384 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_400 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 400 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_416 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 416 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_432 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 432 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_448 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 448 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_464 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 464 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_480 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 480 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_496 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 496 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_512 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 512 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_528 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 528 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_544 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 544 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_560 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 560 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_576 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 576 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_592 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 592 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_608 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 608 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_624 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 624 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_640 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 640 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_656 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 656 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_672 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 672 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_688 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 688 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_704 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 704 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_720 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 720 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_736 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 736 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_752 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 752 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_768 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 768 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_784 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 784 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_800 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 800 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_816 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 816 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_832 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 832 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_848 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 848 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_864 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 864 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_880 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 880 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_896 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 896 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_912 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 912 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_928 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 928 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_944 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 944 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_960 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 960 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_976 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 976 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_992 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 992 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1008 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1008 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1024 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1024 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1040 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1040 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1056 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1056 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1072 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1072 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1088 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1088 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1104 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1104 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1120 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1120 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1136 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1136 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1152 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1152 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1168 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1168 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1184 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1184 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1200 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1200 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1216 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1216 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1232 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1232 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1248 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1248 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1264 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1264 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1280 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1280 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1296 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1296 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1312 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1312 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1328 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1328 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1344 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1344 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1360 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1360 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1376 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1376 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1392 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1392 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1408 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1408 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1424 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1424 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1440 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1440 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1456 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1456 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1472 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1472 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1488 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1488 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1504 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1504 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1520 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1520 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1536 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1536 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1552 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1552 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1568 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1568 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1584 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1584 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1600 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1600 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1616 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1616 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1632 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1632 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1648 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1648 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1664 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1664 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1680 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1680 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1696 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1696 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1712 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1712 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1728 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1728 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1744 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1744 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1760 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1760 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1776 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1776 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1792 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1792 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1808 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1808 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1824 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1824 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1840 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1840 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1856 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1856 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1872 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1872 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1888 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1888 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1904 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1904 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1920 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1920 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1936 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1936 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1952 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1952 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1968 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1968 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_1984 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 1984 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_2000 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 2000 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_2016 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 2016 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_2032 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 2032 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_2048 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 2048 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_2064 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 2064 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_2080 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 2080 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_2096 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 2096 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_2112 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 2112 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_2128 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 2128 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_2144 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 2144 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_2160 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 2160 16 =
      true := by decide +kernel

/-- Exact transfer check on consecutive residues. -/
theorem levelSeven_chunk_2176 :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 2176 11 =
      true := by decide +kernel

/-- Checked chunks cover the complete output group. -/
theorem levelSeven_transfer :
    levelSeven.checkRange (levelSix.directEntry 4651932141793643 7 16) 0 2187 = true := by
  have h0 := levelSeven_chunk_0
  have h1 := Entries.checkRange_append levelSeven _ 0 16 16 h0 levelSeven_chunk_16
  have h2 := Entries.checkRange_append levelSeven _ 0 32 16 h1 levelSeven_chunk_32
  have h3 := Entries.checkRange_append levelSeven _ 0 48 16 h2 levelSeven_chunk_48
  have h4 := Entries.checkRange_append levelSeven _ 0 64 16 h3 levelSeven_chunk_64
  have h5 := Entries.checkRange_append levelSeven _ 0 80 16 h4 levelSeven_chunk_80
  have h6 := Entries.checkRange_append levelSeven _ 0 96 16 h5 levelSeven_chunk_96
  have h7 := Entries.checkRange_append levelSeven _ 0 112 16 h6 levelSeven_chunk_112
  have h8 := Entries.checkRange_append levelSeven _ 0 128 16 h7 levelSeven_chunk_128
  have h9 := Entries.checkRange_append levelSeven _ 0 144 16 h8 levelSeven_chunk_144
  have h10 := Entries.checkRange_append levelSeven _ 0 160 16 h9 levelSeven_chunk_160
  have h11 := Entries.checkRange_append levelSeven _ 0 176 16 h10 levelSeven_chunk_176
  have h12 := Entries.checkRange_append levelSeven _ 0 192 16 h11 levelSeven_chunk_192
  have h13 := Entries.checkRange_append levelSeven _ 0 208 16 h12 levelSeven_chunk_208
  have h14 := Entries.checkRange_append levelSeven _ 0 224 16 h13 levelSeven_chunk_224
  have h15 := Entries.checkRange_append levelSeven _ 0 240 16 h14 levelSeven_chunk_240
  have h16 := Entries.checkRange_append levelSeven _ 0 256 16 h15 levelSeven_chunk_256
  have h17 := Entries.checkRange_append levelSeven _ 0 272 16 h16 levelSeven_chunk_272
  have h18 := Entries.checkRange_append levelSeven _ 0 288 16 h17 levelSeven_chunk_288
  have h19 := Entries.checkRange_append levelSeven _ 0 304 16 h18 levelSeven_chunk_304
  have h20 := Entries.checkRange_append levelSeven _ 0 320 16 h19 levelSeven_chunk_320
  have h21 := Entries.checkRange_append levelSeven _ 0 336 16 h20 levelSeven_chunk_336
  have h22 := Entries.checkRange_append levelSeven _ 0 352 16 h21 levelSeven_chunk_352
  have h23 := Entries.checkRange_append levelSeven _ 0 368 16 h22 levelSeven_chunk_368
  have h24 := Entries.checkRange_append levelSeven _ 0 384 16 h23 levelSeven_chunk_384
  have h25 := Entries.checkRange_append levelSeven _ 0 400 16 h24 levelSeven_chunk_400
  have h26 := Entries.checkRange_append levelSeven _ 0 416 16 h25 levelSeven_chunk_416
  have h27 := Entries.checkRange_append levelSeven _ 0 432 16 h26 levelSeven_chunk_432
  have h28 := Entries.checkRange_append levelSeven _ 0 448 16 h27 levelSeven_chunk_448
  have h29 := Entries.checkRange_append levelSeven _ 0 464 16 h28 levelSeven_chunk_464
  have h30 := Entries.checkRange_append levelSeven _ 0 480 16 h29 levelSeven_chunk_480
  have h31 := Entries.checkRange_append levelSeven _ 0 496 16 h30 levelSeven_chunk_496
  have h32 := Entries.checkRange_append levelSeven _ 0 512 16 h31 levelSeven_chunk_512
  have h33 := Entries.checkRange_append levelSeven _ 0 528 16 h32 levelSeven_chunk_528
  have h34 := Entries.checkRange_append levelSeven _ 0 544 16 h33 levelSeven_chunk_544
  have h35 := Entries.checkRange_append levelSeven _ 0 560 16 h34 levelSeven_chunk_560
  have h36 := Entries.checkRange_append levelSeven _ 0 576 16 h35 levelSeven_chunk_576
  have h37 := Entries.checkRange_append levelSeven _ 0 592 16 h36 levelSeven_chunk_592
  have h38 := Entries.checkRange_append levelSeven _ 0 608 16 h37 levelSeven_chunk_608
  have h39 := Entries.checkRange_append levelSeven _ 0 624 16 h38 levelSeven_chunk_624
  have h40 := Entries.checkRange_append levelSeven _ 0 640 16 h39 levelSeven_chunk_640
  have h41 := Entries.checkRange_append levelSeven _ 0 656 16 h40 levelSeven_chunk_656
  have h42 := Entries.checkRange_append levelSeven _ 0 672 16 h41 levelSeven_chunk_672
  have h43 := Entries.checkRange_append levelSeven _ 0 688 16 h42 levelSeven_chunk_688
  have h44 := Entries.checkRange_append levelSeven _ 0 704 16 h43 levelSeven_chunk_704
  have h45 := Entries.checkRange_append levelSeven _ 0 720 16 h44 levelSeven_chunk_720
  have h46 := Entries.checkRange_append levelSeven _ 0 736 16 h45 levelSeven_chunk_736
  have h47 := Entries.checkRange_append levelSeven _ 0 752 16 h46 levelSeven_chunk_752
  have h48 := Entries.checkRange_append levelSeven _ 0 768 16 h47 levelSeven_chunk_768
  have h49 := Entries.checkRange_append levelSeven _ 0 784 16 h48 levelSeven_chunk_784
  have h50 := Entries.checkRange_append levelSeven _ 0 800 16 h49 levelSeven_chunk_800
  have h51 := Entries.checkRange_append levelSeven _ 0 816 16 h50 levelSeven_chunk_816
  have h52 := Entries.checkRange_append levelSeven _ 0 832 16 h51 levelSeven_chunk_832
  have h53 := Entries.checkRange_append levelSeven _ 0 848 16 h52 levelSeven_chunk_848
  have h54 := Entries.checkRange_append levelSeven _ 0 864 16 h53 levelSeven_chunk_864
  have h55 := Entries.checkRange_append levelSeven _ 0 880 16 h54 levelSeven_chunk_880
  have h56 := Entries.checkRange_append levelSeven _ 0 896 16 h55 levelSeven_chunk_896
  have h57 := Entries.checkRange_append levelSeven _ 0 912 16 h56 levelSeven_chunk_912
  have h58 := Entries.checkRange_append levelSeven _ 0 928 16 h57 levelSeven_chunk_928
  have h59 := Entries.checkRange_append levelSeven _ 0 944 16 h58 levelSeven_chunk_944
  have h60 := Entries.checkRange_append levelSeven _ 0 960 16 h59 levelSeven_chunk_960
  have h61 := Entries.checkRange_append levelSeven _ 0 976 16 h60 levelSeven_chunk_976
  have h62 := Entries.checkRange_append levelSeven _ 0 992 16 h61 levelSeven_chunk_992
  have h63 := Entries.checkRange_append levelSeven _ 0 1008 16 h62 levelSeven_chunk_1008
  have h64 := Entries.checkRange_append levelSeven _ 0 1024 16 h63 levelSeven_chunk_1024
  have h65 := Entries.checkRange_append levelSeven _ 0 1040 16 h64 levelSeven_chunk_1040
  have h66 := Entries.checkRange_append levelSeven _ 0 1056 16 h65 levelSeven_chunk_1056
  have h67 := Entries.checkRange_append levelSeven _ 0 1072 16 h66 levelSeven_chunk_1072
  have h68 := Entries.checkRange_append levelSeven _ 0 1088 16 h67 levelSeven_chunk_1088
  have h69 := Entries.checkRange_append levelSeven _ 0 1104 16 h68 levelSeven_chunk_1104
  have h70 := Entries.checkRange_append levelSeven _ 0 1120 16 h69 levelSeven_chunk_1120
  have h71 := Entries.checkRange_append levelSeven _ 0 1136 16 h70 levelSeven_chunk_1136
  have h72 := Entries.checkRange_append levelSeven _ 0 1152 16 h71 levelSeven_chunk_1152
  have h73 := Entries.checkRange_append levelSeven _ 0 1168 16 h72 levelSeven_chunk_1168
  have h74 := Entries.checkRange_append levelSeven _ 0 1184 16 h73 levelSeven_chunk_1184
  have h75 := Entries.checkRange_append levelSeven _ 0 1200 16 h74 levelSeven_chunk_1200
  have h76 := Entries.checkRange_append levelSeven _ 0 1216 16 h75 levelSeven_chunk_1216
  have h77 := Entries.checkRange_append levelSeven _ 0 1232 16 h76 levelSeven_chunk_1232
  have h78 := Entries.checkRange_append levelSeven _ 0 1248 16 h77 levelSeven_chunk_1248
  have h79 := Entries.checkRange_append levelSeven _ 0 1264 16 h78 levelSeven_chunk_1264
  have h80 := Entries.checkRange_append levelSeven _ 0 1280 16 h79 levelSeven_chunk_1280
  have h81 := Entries.checkRange_append levelSeven _ 0 1296 16 h80 levelSeven_chunk_1296
  have h82 := Entries.checkRange_append levelSeven _ 0 1312 16 h81 levelSeven_chunk_1312
  have h83 := Entries.checkRange_append levelSeven _ 0 1328 16 h82 levelSeven_chunk_1328
  have h84 := Entries.checkRange_append levelSeven _ 0 1344 16 h83 levelSeven_chunk_1344
  have h85 := Entries.checkRange_append levelSeven _ 0 1360 16 h84 levelSeven_chunk_1360
  have h86 := Entries.checkRange_append levelSeven _ 0 1376 16 h85 levelSeven_chunk_1376
  have h87 := Entries.checkRange_append levelSeven _ 0 1392 16 h86 levelSeven_chunk_1392
  have h88 := Entries.checkRange_append levelSeven _ 0 1408 16 h87 levelSeven_chunk_1408
  have h89 := Entries.checkRange_append levelSeven _ 0 1424 16 h88 levelSeven_chunk_1424
  have h90 := Entries.checkRange_append levelSeven _ 0 1440 16 h89 levelSeven_chunk_1440
  have h91 := Entries.checkRange_append levelSeven _ 0 1456 16 h90 levelSeven_chunk_1456
  have h92 := Entries.checkRange_append levelSeven _ 0 1472 16 h91 levelSeven_chunk_1472
  have h93 := Entries.checkRange_append levelSeven _ 0 1488 16 h92 levelSeven_chunk_1488
  have h94 := Entries.checkRange_append levelSeven _ 0 1504 16 h93 levelSeven_chunk_1504
  have h95 := Entries.checkRange_append levelSeven _ 0 1520 16 h94 levelSeven_chunk_1520
  have h96 := Entries.checkRange_append levelSeven _ 0 1536 16 h95 levelSeven_chunk_1536
  have h97 := Entries.checkRange_append levelSeven _ 0 1552 16 h96 levelSeven_chunk_1552
  have h98 := Entries.checkRange_append levelSeven _ 0 1568 16 h97 levelSeven_chunk_1568
  have h99 := Entries.checkRange_append levelSeven _ 0 1584 16 h98 levelSeven_chunk_1584
  have h100 := Entries.checkRange_append levelSeven _ 0 1600 16 h99 levelSeven_chunk_1600
  have h101 := Entries.checkRange_append levelSeven _ 0 1616 16 h100 levelSeven_chunk_1616
  have h102 := Entries.checkRange_append levelSeven _ 0 1632 16 h101 levelSeven_chunk_1632
  have h103 := Entries.checkRange_append levelSeven _ 0 1648 16 h102 levelSeven_chunk_1648
  have h104 := Entries.checkRange_append levelSeven _ 0 1664 16 h103 levelSeven_chunk_1664
  have h105 := Entries.checkRange_append levelSeven _ 0 1680 16 h104 levelSeven_chunk_1680
  have h106 := Entries.checkRange_append levelSeven _ 0 1696 16 h105 levelSeven_chunk_1696
  have h107 := Entries.checkRange_append levelSeven _ 0 1712 16 h106 levelSeven_chunk_1712
  have h108 := Entries.checkRange_append levelSeven _ 0 1728 16 h107 levelSeven_chunk_1728
  have h109 := Entries.checkRange_append levelSeven _ 0 1744 16 h108 levelSeven_chunk_1744
  have h110 := Entries.checkRange_append levelSeven _ 0 1760 16 h109 levelSeven_chunk_1760
  have h111 := Entries.checkRange_append levelSeven _ 0 1776 16 h110 levelSeven_chunk_1776
  have h112 := Entries.checkRange_append levelSeven _ 0 1792 16 h111 levelSeven_chunk_1792
  have h113 := Entries.checkRange_append levelSeven _ 0 1808 16 h112 levelSeven_chunk_1808
  have h114 := Entries.checkRange_append levelSeven _ 0 1824 16 h113 levelSeven_chunk_1824
  have h115 := Entries.checkRange_append levelSeven _ 0 1840 16 h114 levelSeven_chunk_1840
  have h116 := Entries.checkRange_append levelSeven _ 0 1856 16 h115 levelSeven_chunk_1856
  have h117 := Entries.checkRange_append levelSeven _ 0 1872 16 h116 levelSeven_chunk_1872
  have h118 := Entries.checkRange_append levelSeven _ 0 1888 16 h117 levelSeven_chunk_1888
  have h119 := Entries.checkRange_append levelSeven _ 0 1904 16 h118 levelSeven_chunk_1904
  have h120 := Entries.checkRange_append levelSeven _ 0 1920 16 h119 levelSeven_chunk_1920
  have h121 := Entries.checkRange_append levelSeven _ 0 1936 16 h120 levelSeven_chunk_1936
  have h122 := Entries.checkRange_append levelSeven _ 0 1952 16 h121 levelSeven_chunk_1952
  have h123 := Entries.checkRange_append levelSeven _ 0 1968 16 h122 levelSeven_chunk_1968
  have h124 := Entries.checkRange_append levelSeven _ 0 1984 16 h123 levelSeven_chunk_1984
  have h125 := Entries.checkRange_append levelSeven _ 0 2000 16 h124 levelSeven_chunk_2000
  have h126 := Entries.checkRange_append levelSeven _ 0 2016 16 h125 levelSeven_chunk_2016
  have h127 := Entries.checkRange_append levelSeven _ 0 2032 16 h126 levelSeven_chunk_2032
  have h128 := Entries.checkRange_append levelSeven _ 0 2048 16 h127 levelSeven_chunk_2048
  have h129 := Entries.checkRange_append levelSeven _ 0 2064 16 h128 levelSeven_chunk_2064
  have h130 := Entries.checkRange_append levelSeven _ 0 2080 16 h129 levelSeven_chunk_2080
  have h131 := Entries.checkRange_append levelSeven _ 0 2096 16 h130 levelSeven_chunk_2096
  have h132 := Entries.checkRange_append levelSeven _ 0 2112 16 h131 levelSeven_chunk_2112
  have h133 := Entries.checkRange_append levelSeven _ 0 2128 16 h132 levelSeven_chunk_2128
  have h134 := Entries.checkRange_append levelSeven _ 0 2144 16 h133 levelSeven_chunk_2144
  have h135 := Entries.checkRange_append levelSeven _ 0 2160 16 h134 levelSeven_chunk_2160
  have h136 := Entries.checkRange_append levelSeven _ 0 2176 11 h135 levelSeven_chunk_2176
  exact h136

/-- The integer cap covers all residues. -/
theorem levelSeven_cap : levelSeven.allLE 6994258928192191 = true := by decide +kernel

/-- Scaled maximum comparison. -/
theorem levelSeven_max_comparison : 1 * 6994258928192191 ≤ 25 * 2 ^ 48 := by
  decide +kernel

/-- Complete integer energy comparison. -/
theorem levelSeven_energy_comparison :
    500 * levelSeven.energySum 2187 ≤ 2233 * 2187 * (2 ^ 48) ^ 2 := by decide +kernel

/-- Square enclosures include every residue. -/
theorem levelSeven_square_enclosures : ∀ i : Fin 2187,
    levelSeven.lookup i.val ≤ levelSevenRoots.lookup i.val ^ 2 := by decide +kernel

/-- Complete fractional numerator comparison. -/
theorem levelSeven_fractional_comparison :
    62500 * levelSeven.fractionalSum levelSevenRoots 2187 ≤
      116627 * 2187 * 2 ^ 72 := by decide +kernel

end WordCertDensity.Certificates
