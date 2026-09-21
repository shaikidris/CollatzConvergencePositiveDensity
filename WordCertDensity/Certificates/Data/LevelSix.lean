/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.Data.Summaries
public import WordCertDensity.Certificates.Data.LevelFive

/-! # Complete depth-6 integer certificate -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Complete enclosure tree, with one leaf per residue. -/
def levelSix : Entries :=
  (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 793587966534211)) (.leaf 396793983267106)) (.node (.node (.leaf 395956808130659) (.leaf 180809263993888)) (.leaf 0))) (.node (.node (.node (.leaf 197978404065330) (.leaf 0)) (.leaf 90404633029557)) (.node (.node (.leaf 0) (.leaf 612357450028911)) (.leaf 251160585887714)))) (.node (.node (.node (.node (.leaf 98989203043005) (.leaf 89943227697872)) (.leaf 0)) (.node (.node (.leaf 45202316514779) (.leaf 0)) (.leaf 543788868991638))) (.node (.node (.node (.leaf 0) (.leaf 119950303073593)) (.leaf 306178725014456)) (.node (.leaf 242289870335414) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 49494601521503) (.leaf 0)) (.leaf 340549270515419)) (.node (.node (.leaf 0) (.leaf 242433432245165)) (.leaf 444443213437884))) (.node (.node (.node (.leaf 494743642015604) (.leaf 68519052543034)) (.leaf 0)) (.node (.node (.leaf 271894434495819) (.leaf 0)) (.leaf 134087205640922)))) (.node (.node (.node (.node (.leaf 0) (.leaf 447684320109070)) (.leaf 59975151536797)) (.node (.node (.leaf 153089363573289) (.leaf 1021244429772319)) (.leaf 0))) (.node (.node (.node (.leaf 121144935167707) (.leaf 0)) (.leaf 842016171679156)) (.node (.leaf 0) (.leaf 965693980904931)))))) (.node (.node (.node (.node (.node (.node (.leaf 522854111440199) (.leaf 33110793962924)) (.leaf 0)) (.node (.node (.leaf 170274635257710) (.leaf 0)) (.leaf 59876036150401))) (.node (.node (.node (.leaf 0) (.leaf 389076599200813)) (.leaf 121216716122583)) (.node (.node (.leaf 279407226729039) (.leaf 530854758995086)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 247371821007802) (.leaf 0)) (.leaf 408643468692890)) (.node (.node (.leaf 0) (.leaf 174429869415917)) (.leaf 120722688672838))) (.node (.node (.node (.leaf 135947218097233) (.leaf 245803216492503)) (.leaf 0)) (.node (.leaf 67043602820461) (.leaf 610905572142099))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 65146782515017)) (.leaf 223842160054535)) (.node (.node (.leaf 1435467896086109) (.leaf 59918776703826)) (.leaf 0))) (.node (.node (.node (.leaf 76544681786645) (.leaf 0)) (.leaf 884563616343289)) (.node (.node (.leaf 0) (.leaf 4651932141793643)) (.leaf 306100339993755)))) (.node (.node (.node (.node (.leaf 443775470212336) (.leaf 309381843081869)) (.leaf 0)) (.node (.node (.leaf 421008085839578) (.leaf 0)) (.leaf 228204270967736))) (.node (.node (.node (.leaf 0) (.leaf 267323165301425)) (.leaf 39036134227342)) (.node (.leaf 482846991319849) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 261427055720100) (.leaf 0)) (.leaf 601903492735237)) (.node (.node (.leaf 0) (.leaf 64735816697005)) (.leaf 262313911522366))) (.node (.node (.node (.leaf 85137318678065) (.leaf 403171747755540)) (.leaf 0)) (.node (.node (.leaf 29938018075201) (.leaf 0)) (.leaf 633456549562083)))) (.node (.node (.node (.node (.leaf 0) (.leaf 252966829521996)) (.leaf 194538299600407)) (.node (.node (.leaf 471713187691509) (.leaf 377068912269314)) (.leaf 0))) (.node (.node (.node (.leaf 139703613364520) (.leaf 0)) (.leaf 265427380534222)) (.node (.leaf 0) (.leaf 49023695657813))))) (.node (.node (.node (.node (.node (.leaf 790348421941380) (.leaf 165845680834076)) (.leaf 0)) (.node (.node (.leaf 204321734346445) (.leaf 0)) (.leaf 1350032720007263))) (.node (.node (.node (.leaf 0) (.leaf 386727263137346)) (.leaf 87214934707959)) (.node (.node (.leaf 60361345328514) (.leaf 969692765606224)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 67973609048617) (.leaf 0)) (.leaf 555450278185447)) (.node (.node (.leaf 0) (.leaf 934299432561110)) (.leaf 252912025701040))) (.node (.node (.node (.leaf 188925518103189) (.leaf 120958331033704)) (.leaf 0)) (.node (.leaf 305452786071050) (.leaf 251355773331115)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 947395715778771)) (.leaf 32573391257509)) (.node (.node (.leaf 111921081013484) (.leaf 115596268727457)) (.leaf 0))) (.node (.node (.node (.leaf 717733948043055) (.leaf 0)) (.leaf 339995084121363)) (.node (.node (.leaf 0) (.leaf 84639326480962)) (.leaf 125037979215958)))) (.node (.node (.node (.node (.leaf 613961968775657) (.leaf 61248985582947)) (.leaf 0)) (.node (.node (.leaf 442281808171645) (.leaf 0)) (.leaf 85622801225078))) (.node (.node (.node (.leaf 0) (.leaf 417626059566204)) (.leaf 2325966070896822)) (.node (.leaf 869171209521749) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 221887735106168) (.leaf 0)) (.leaf 154690922564422)) (.node (.node (.leaf 0) (.leaf 2009284682983406)) (.leaf 136338568106300))) (.node (.node (.node (.leaf 312289069861529) (.leaf 925536963325535)) (.leaf 0)) (.node (.leaf 114102135483868) (.leaf 783328433074964)))) (.node (.node (.node (.node (.leaf 0) (.leaf 204154825681373)) (.leaf 133661582650713)) (.node (.node (.leaf 1261974116923835) (.leaf 28374198110183)) (.leaf 0))) (.node (.node (.node (.leaf 241423495659925) (.leaf 0)) (.leaf 1090708540601904)) (.node (.leaf 0) (.leaf 230197057147251)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 537853630561626) (.leaf 355217091187431)) (.leaf 0)) (.node (.node (.leaf 300951746367619) (.leaf 0)) (.leaf 325239320575281))) (.node (.node (.node (.leaf 0) (.leaf 270989480248162)) (.leaf 32367908348503)) (.node (.node (.leaf 131156956790403) (.leaf 108442141687288)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 42568659339033) (.leaf 0)) (.leaf 478080098152556)) (.node (.node (.leaf 0) (.leaf 1991216877516322)) (.leaf 726823889185824))) (.node (.node (.node (.leaf 636583868604025) (.leaf 157889761964987)) (.leaf 0)) (.node (.leaf 316728274781042) (.leaf 87266080597665))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 496869490385334)) (.leaf 126483414760998)) (.node (.node (.leaf 203545863086263) (.leaf 554888864492647)) (.leaf 0))) (.node (.node (.node (.leaf 235856593845755) (.leaf 0)) (.leaf 188534457201332)) (.node (.node (.leaf 0) (.leaf 1105527252302322)) (.leaf 39802240838200)))) (.node (.node (.node (.node (.leaf 69851807630106) (.leaf 1015304417281523)) (.leaf 0)) (.node (.node (.leaf 132713690267111) (.leaf 0)) (.leaf 263209611639773))) (.node (.node (.node (.leaf 0) (.leaf 148783953680392)) (.leaf 144233769894988)) (.node (.leaf 3468185608813991) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 395174210970690) (.leaf 0)) (.leaf 82922841405899)) (.node (.node (.leaf 0) (.leaf 967666644042213)) (.leaf 108646401528378))) (.node (.node (.node (.leaf 489991880853227) (.leaf 180051419381020)) (.leaf 0)) (.node (.node (.leaf 675016360003632) (.leaf 0)) (.leaf 444213777367511)))) (.node (.node (.node (.node (.leaf 0) (.leaf 136485910909284)) (.leaf 193363631568673)) (.node (.node (.leaf 315422003460793) (.leaf 38430650824004)) (.leaf 0))) (.node (.node (.node (.leaf 30180672664257) (.leaf 0)) (.leaf 548152416247488)) (.node (.leaf 0) (.leaf 453019322354218))))) (.node (.node (.node (.node (.node (.leaf 805872011171213) (.leaf 42511536134958)) (.leaf 0)) (.node (.node (.leaf 277725139092724) (.leaf 0)) (.leaf 870115069494580))) (.node (.node (.node (.leaf 0) (.leaf 159448196566420)) (.leaf 467149716280555)) (.node (.leaf 551562861043532) (.leaf 0)))) (.node (.node (.node (.node (.leaf 94462759051595) (.leaf 0)) (.leaf 1147737302767074)) (.node (.node (.leaf 0) (.leaf 98178209166815)) (.leaf 545773266392345))) (.node (.node (.node (.leaf 152726394013974) (.leaf 144337318296830)) (.leaf 0)) (.node (.leaf 125677886665558) (.leaf 1263118091786123))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 136434756411190)) (.leaf 473697857889386)) (.node (.node (.leaf 574169702954654) (.leaf 40770114808485)) (.leaf 0))) (.node (.node (.node (.leaf 55960540506742) (.leaf 0)) (.leaf 270758852426721)) (.node (.node (.leaf 0) (.leaf 195919970049149)) (.leaf 306157572054972)))) (.node (.node (.node (.node (.leaf 415123049557098) (.leaf 327530442293467)) (.leaf 0)) (.node (.node (.leaf 169997542060682) (.leaf 0)) (.leaf 1013054266773184))) (.node (.node (.node (.leaf 0) (.leaf 545739021792584)) (.leaf 42319663240481)) (.node (.leaf 62518990663209) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 306980984387829) (.leaf 0)) (.leaf 137868534421554)) (.node (.node (.leaf 0) (.leaf 120124753033091)) (.leaf 159208961257767))) (.node (.node (.node (.leaf 221140905070187) (.leaf 180725588095597)) (.leaf 0)) (.node (.node (.leaf 42811400612539) (.leaf 0)) (.leaf 349064318197015)))) (.node (.node (.node (.node (.leaf 0) (.leaf 992937879497214)) (.leaf 208813029783102)) (.node (.node (.leaf 3480460273929759) (.leaf 170046142564425)) (.leaf 0))) (.node (.node (.node (.leaf 434585604760875) (.leaf 0)) (.leaf 103780763063467)) (.node (.leaf 0) (.leaf 81882611086751)))))) (.node (.node (.node (.node (.node (.node (.leaf 110943868621624) (.leaf 384133929735645)) (.leaf 0)) (.node (.node (.leaf 77345461282211) (.leaf 0)) (.leaf 536348818824536))) (.node (.node (.node (.leaf 0) (.leaf 71703760630578)) (.leaf 1004642341491703)) (.node (.node (.leaf 1887310656541121) (.leaf 106548775932566)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 156144534930765) (.leaf 0)) (.leaf 462768482509978)) (.node (.node (.leaf 0) (.leaf 260587127901747)) (.leaf 118424464934317))) (.node (.node (.node (.leaf 239504140351982) (.leaf 132443173740775)) (.leaf 0)) (.node (.leaf 391664216537482) (.leaf 385478770926601))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 1005423089080185)) (.leaf 102077412840687)) (.node (.node (.leaf 66830792339570) (.leaf 536736947309653)) (.leaf 0))) (.node (.node (.node (.leaf 630987058461918) (.leaf 0)) (.leaf 2005566027718328)) (.node (.leaf 0) (.leaf 196094780526919)))) (.node (.node (.node (.node (.leaf 377979689142780) (.leaf 68945358155507)) (.leaf 0)) (.node (.node (.leaf 545354270300952) (.leaf 0)) (.leaf 67689714161096))) (.node (.node (.node (.leaf 0) (.leaf 3494005201642892)) (.leaf 71175755398996)) (.node (.leaf 342491201510980) (.leaf 0))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 268926815280813) (.leaf 0)) (.leaf 177608546658136)) (.node (.node (.leaf 0) (.leaf 852390204034647)) (.leaf 58964148982972))) (.node (.node (.node (.leaf 326160914346010) (.leaf 715516873293986)) (.leaf 0)) (.node (.node (.leaf 162619660287641) (.leaf 0)) (.leaf 1126949984093529)))) (.node (.node (.node (.node (.leaf 0) (.leaf 276381813991121)) (.leaf 135494740124081)) (.node (.node (.leaf 3494825947072112) (.leaf 79041284744822)) (.leaf 0))) (.node (.node (.node (.leaf 65578478395202) (.leaf 0)) (.leaf 307445202329737)) (.node (.leaf 0) (.leaf 630021948442413))))) (.node (.node (.node (.node (.node (.leaf 450260490272581) (.leaf 138722216633255)) (.leaf 0)) (.node (.node (.leaf 239040049076278) (.leaf 0)) (.leaf 50886466804728))) (.node (.node (.node (.leaf 0) (.leaf 3498070185064403)) (.leaf 995608438758161)) (.node (.node (.leaf 479350209549801) (.leaf 135821323428188)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 318291934302013) (.leaf 0)) (.leaf 205590656104317)) (.node (.node (.leaf 0) (.leaf 105997354313306)) (.leaf 896718191230436))) (.node (.node (.node (.leaf 158364138397315) (.leaf 91766507003368)) (.leaf 0)) (.node (.leaf 43633040298833) (.leaf 226993581231763)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 183533014006735)) (.leaf 248434745192667)) (.node (.node (.leaf 1793436382460872) (.leaf 211994706514763)) (.leaf 0))) (.node (.node (.node (.leaf 101772931543132) (.leaf 0)) (.leaf 277444433266509)) (.node (.node (.leaf 0) (.leaf 271642646856376)) (.leaf 36058442810762)))) (.node (.node (.node (.node (.leaf 117928297965944) (.leaf 462324357229555)) (.leaf 0)) (.node (.node (.leaf 94267228600666) (.leaf 0)) (.leaf 1431033746587972))) (.node (.node (.node (.leaf 0) (.leaf 158082569489644)) (.leaf 552763626151161)) (.node (.leaf 1260043896884825) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 34925903815053) (.leaf 0)) (.leaf 632330274587121)) (.node (.node (.leaf 0) (.leaf 466499196969324)) (.leaf 272289197387020))) (.node (.node (.node (.leaf 544578394774040) (.leaf 32901201978838)) (.leaf 0)) (.node (.leaf 131604805819887) (.leaf 65802403957676)))) (.node (.node (.node (.node (.leaf 0) (.leaf 423989413029526)) (.leaf 74391976840196)) (.node (.node (.leaf 72116885621524) (.leaf 233249598484662)) (.leaf 0))) (.node (.node (.node (.leaf 1734092804406996) (.leaf 0)) (.leaf 924648714459109)) (.node (.leaf 0) (.leaf 316165137293561))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 197587106438798) (.leaf 102795328052159)) (.leaf 0)) (.node (.node (.leaf 41461420702950) (.leaf 0)) (.leaf 258943262893824))) (.node (.node (.node (.leaf 0) (.leaf 448359096681063)) (.leaf 483833322021107)) (.node (.node (.leaf 303679332023953) (.leaf 52998677156653)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 244995940426614) (.leaf 0)) (.leaf 90025710368773)) (.node (.node (.leaf 0) (.leaf 338557301818983)) (.leaf 79182069198658))) (.node (.node (.node (.leaf 816619298888050) (.leaf 113496790615882)) (.leaf 0)) (.node (.leaf 222106888683756) (.leaf 1149791207983577))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 697719473619604)) (.leaf 68242955454642)) (.node (.node (.leaf 96681816851100) (.leaf 1749035092532202)) (.leaf 0))) (.node (.node (.node (.leaf 157711001730397) (.leaf 0)) (.leaf 525663587807855)) (.node (.node (.leaf 0) (.leaf 67910662749670)) (.leaf 239675104774901)))) (.node (.node (.node (.node (.leaf 246966865235565) (.leaf 25443233402364)) (.leaf 0)) (.node (.node (.leaf 274076208123744) (.leaf 0)) (.leaf 119520025564041))) (.node (.node (.node (.leaf 0) (.leaf 274913524765832)) (.leaf 225130245136291)) (.node (.leaf 479801208141354) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 402936005585607) (.leaf 0)) (.leaf 1067190070504945)) (.node (.node (.leaf 0) (.leaf 357758437671806)) (.leaf 163080457173005))) (.node (.node (.node (.leaf 138862570561145) (.leaf 563474992046765)) (.leaf 0)) (.node (.node (.leaf 435057534747290) (.leaf 0)) (.leaf 480499007884544)))) (.node (.node (.node (.node (.leaf 0) (.leaf 827860430505141)) (.leaf 79724098283210)) (.node (.node (.leaf 286815038784236) (.leaf 426195102017324)) (.leaf 0))) (.node (.node (.node (.leaf 275781430521766) (.leaf 0)) (.leaf 134463408661579)) (.node (.leaf 0) (.leaf 88804273329068))))) (.node (.node (.node (.node (.node (.leaf 545943639379469) (.leaf 153722601164869)) (.leaf 0)) (.node (.node (.leaf 573868651383537) (.leaf 0)) (.leaf 232383829963511))) (.node (.node (.node (.leaf 0) (.leaf 392712832796827)) (.leaf 49089104583408)) (.node (.leaf 272886634186111) (.leaf 0)))) (.node (.node (.node (.node (.leaf 76363197006987) (.leaf 0)) (.leaf 595135810800841)) (.node (.node (.leaf 0) (.leaf 439351149842443)) (.leaf 1747412973536056))) (.node (.node (.node (.leaf 569422036454682) (.leaf 138190906995561)) (.leaf 0)) (.node (.leaf 631559045893062) (.leaf 67747371019437)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 264886347481549)) (.leaf 68217378205595)) (.node (.node (.leaf 236848929868633) (.leaf 413930215252571)) (.leaf 0))) (.node (.node (.node (.leaf 287084851477327) (.leaf 0)) (.leaf 768267859471290)) (.node (.node (.leaf 0) (.leaf 213097551865132)) (.leaf 143407519392118)))) (.node (.node (.node (.node (.leaf 142351510797992) (.leaf 67231704330790)) (.leaf 0)) (.node (.node (.leaf 135379426213361) (.leaf 0)) (.leaf 137890716311014))) (.node (.node (.node (.leaf 0) (.leaf 1073473894619305)) (.leaf 97959985024575)) (.node (.leaf 392189561053838) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 207561524778549) (.leaf 0)) (.leaf 163765222173501)) (.node (.node (.leaf 0) (.leaf 340092285128849)) (.leaf 69431285280573))) (.node (.node (.node (.leaf 318417922515534) (.leaf 240249503942272)) (.leaf 0)) (.node (.node (.leaf 506527133386592) (.leaf 0)) (.leaf 361451176191193)))) (.node (.node (.node (.node (.leaf 0) (.leaf 81540229616969)) (.leaf 272869510896292)) (.node (.node (.leaf 612315144109943) (.leaf 178879218835903)) (.leaf 0))) (.node (.node (.node (.leaf 31259495331605) (.leaf 0)) (.leaf 655060884586934)) (.node (.leaf 0) (.leaf 533595035252473)))))) (.node (.node (.node (.node (.node (.node (.leaf 288467539789975) (.leaf 297567905400421)) (.leaf 0)) (.node (.node (.leaf 68934267210777) (.leaf 0)) (.leaf 2030608834563046))) (.node (.node (.node (.leaf 0) (.leaf 1109777728985294)) (.leaf 60062376516546)) (.node (.node (.leaf 79604481676400) (.leaf 219675574921222)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 110570452535094) (.leaf 0)) (.leaf 710434182374862)) (.node (.node (.leaf 0) (.leaf 216884283374575)) (.leaf 284711018227341))) (.node (.node (.node (.leaf 1453647778371647) (.leaf 33873685509719)) (.leaf 0)) (.node (.leaf 174532159098508) (.leaf 315779523929973))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 288674636593660)) (.leaf 496468939748607)) (.node (.node (.leaf 1091546532784689) (.leaf 196356416398414)) (.leaf 0))) (.node (.node (.node (.leaf 1740230136964880) (.leaf 0)) (.leaf 85023072269915)) (.node (.leaf 0) (.leaf 136443317093056)))) (.node (.node (.node (.node (.leaf 217292803056755) (.leaf 116191914981756)) (.leaf 0)) (.node (.node (.leaf 51890381531734) (.leaf 0)) (.leaf 360102838762040))) (.node (.node (.node (.leaf 0) (.leaf 76861301648007)) (.leaf 272971819689735)) (.node (.leaf 906038644708435) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 55471934310812) (.leaf 0)) (.leaf 1931387961809861)) (.node (.node (.leaf 0) (.leaf 2042488859544637)) (.leaf 123483432617783))) (.node (.node (.node (.leaf 888886426875767) (.leaf 59760012782021)) (.leaf 0)) (.node (.node (.leaf 268174409412268) (.leaf 0)) (.leaf 137038105086067)))) (.node (.node (.node (.node (.leaf 0) (.leaf 361618527987776)) (.leaf 35851880315289)) (.node (.node (.leaf 502321171775427) (.leaf 137456762382916)) (.leaf 0))) (.node (.node (.node (.leaf 943655328270561) (.leaf 0)) (.leaf 179886455395744)) (.node (.leaf 0) (.leaf 239900604070677))))) (.node (.node (.node (.node (.node (.leaf 78072268454683) (.leaf 262831793903928)) (.leaf 0)) (.node (.node (.leaf 231384241254989) (.leaf 0)) (.leaf 618763686163738))) (.node (.node (.node (.leaf 0) (.leaf 119837553407652)) (.leaf 130293563950874)) (.node (.node (.leaf 612200679987509) (.leaf 33955331374835)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 119752070175991) (.leaf 0)) (.leaf 66221587925848)) (.node (.node (.leaf 0) (.leaf 1061709517990171)) (.leaf 48340908425550))) (.node (.node (.node (.leaf 241445377345675) (.leaf 348859736809802)) (.leaf 0)) (.node (.leaf 192739385463301) (.leaf 491606432985006)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 241916662067408)) (.leaf 502711544540093)) (.node (.node (.leaf 505824051402079) (.leaf 224179548340532)) (.leaf 0))) (.node (.node (.node (.leaf 33415396169785) (.leaf 0)) (.leaf 331691361668151)) (.node (.node (.leaf 0) (.leaf 1939385531212448)) (.leaf 151839666011977)))) (.node (.node (.node (.node (.leaf 524627823044731) (.leaf 129471631446912)) (.leaf 0)) (.node (.node (.leaf 1002783013859164) (.leaf 0)) (.leaf 806343495511079))) (.node (.node (.node (.leaf 0) (.leaf 754137824538628)) (.leaf 98793553219399)) (.node (.leaf 98047391315625) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 188989844571390) (.leaf 0)) (.leaf 460394114294501)) (.node (.node (.leaf 0) (.leaf 56748396220366)) (.leaf 408309649444025))) (.node (.node (.node (.leaf 272677136212600) (.leaf 574895603991789)) (.leaf 0)) (.node (.leaf 33844857080548) (.leaf 1851073926651070)))) (.node (.node (.node (.node (.leaf 0) (.leaf 231192537454914)) (.leaf 1747002600821446)) (.node (.node (.leaf 250075958431916) (.leaf 169278650909492)) (.leaf 0))) (.node (.node (.node (.leaf 171245600755490) (.leaf 0)) (.leaf 122497971165893)) (.node (.leaf 0) (.leaf 45012855184387))))))))))

/-- Complete enclosure tree, with one leaf per residue. -/
def levelSixRoots : Entries :=
  (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 28170694)) (.leaf 19919689)) (.node (.node (.leaf 19898664) (.leaf 13446534)) (.leaf 0))) (.node (.node (.node (.leaf 14070480) (.leaf 0)) (.leaf 9508136)) (.node (.node (.leaf 0) (.leaf 24745858)) (.leaf 15848047)))) (.node (.node (.node (.node (.leaf 9949332) (.leaf 9483841)) (.leaf 0)) (.node (.node (.leaf 6723267) (.leaf 0)) (.leaf 23319282))) (.node (.node (.node (.leaf 0) (.leaf 10952183)) (.leaf 17497964)) (.node (.leaf 15565664) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 7035240) (.leaf 0)) (.leaf 18453978)) (.node (.node (.leaf 0) (.leaf 15570274)) (.leaf 21081822))) (.node (.node (.node (.leaf 22242834) (.leaf 8277624)) (.leaf 0)) (.node (.node (.leaf 16489222) (.leaf 0)) (.leaf 11579604)))) (.node (.node (.node (.node (.leaf 0) (.leaf 21158552)) (.leaf 7744363)) (.node (.node (.leaf 12372929) (.leaf 31956916)) (.leaf 0))) (.node (.node (.node (.leaf 11006586) (.leaf 0)) (.leaf 29017515)) (.node (.leaf 0) (.leaf 31075618)))))) (.node (.node (.node (.node (.node (.node (.leaf 22866004) (.leaf 5754198)) (.leaf 0)) (.node (.node (.leaf 13048933) (.leaf 0)) (.leaf 7737961))) (.node (.node (.node (.leaf 0) (.leaf 19725025)) (.leaf 11009847)) (.node (.node (.leaf 16715479) (.leaf 23040286)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 15728059) (.leaf 0)) (.leaf 20214932)) (.node (.node (.leaf 0) (.leaf 13207191)) (.leaf 10987388))) (.node (.node (.node (.leaf 11659641) (.leaf 15678113)) (.leaf 0)) (.node (.leaf 8188016) (.leaf 24716505))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 8071356)) (.leaf 14961356)) (.node (.node (.leaf 37887570) (.leaf 7740722)) (.leaf 0))) (.node (.node (.node (.leaf 8748982) (.leaf 0)) (.leaf 29741615)) (.node (.node (.leaf 0) (.leaf 68205075)) (.leaf 17495724)))) (.node (.node (.node (.node (.leaf 21065979) (.leaf 17589254)) (.leaf 0)) (.node (.node (.leaf 20518482) (.leaf 0)) (.leaf 15106432))) (.node (.node (.node (.leaf 0) (.leaf 16350021)) (.leaf 6247891)) (.node (.leaf 21973780) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 16168707) (.leaf 0)) (.leaf 24533722)) (.node (.node (.leaf 0) (.leaf 8045858)) (.leaf 16196108))) (.node (.node (.node (.leaf 9226989) (.leaf 20079138)) (.leaf 0)) (.node (.node (.leaf 5471565) (.leaf 0)) (.leaf 25168563)))) (.node (.node (.node (.node (.leaf 0) (.leaf 15904931)) (.leaf 13947699)) (.node (.node (.leaf 21718960) (.leaf 19418263)) (.leaf 0))) (.node (.node (.node (.leaf 11819629) (.leaf 0)) (.leaf 16291943)) (.node (.leaf 0) (.leaf 7001693))))) (.node (.node (.node (.node (.node (.leaf 28113137) (.leaf 12878109)) (.leaf 0)) (.node (.node (.leaf 14294116) (.leaf 0)) (.leaf 36742792))) (.node (.node (.node (.leaf 0) (.leaf 19665383)) (.leaf 9338894)) (.node (.node (.leaf 7769257) (.leaf 31139891)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 8244611) (.leaf 0)) (.leaf 23567993)) (.node (.node (.leaf 0) (.leaf 30566313)) (.leaf 15903209))) (.node (.node (.node (.leaf 13745018) (.leaf 10998106)) (.leaf 0)) (.node (.leaf 17477208) (.leaf 15854204)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 30779794)) (.leaf 5707311)) (.node (.node (.leaf 10579277) (.leaf 10751571)) (.leaf 0))) (.node (.node (.node (.leaf 26790558) (.leaf 0)) (.leaf 18438956)) (.node (.node (.leaf 0) (.leaf 9199964)) (.leaf 11182039)))) (.node (.node (.node (.node (.leaf 24778256) (.leaf 7826174)) (.leaf 0)) (.node (.node (.leaf 21030498) (.leaf 0)) (.leaf 9253259))) (.node (.node (.node (.leaf 0) (.leaf 20435902)) (.leaf 48228271)) (.node (.leaf 29481710) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 14895897) (.leaf 0)) (.leaf 12437481)) (.node (.node (.leaf 0) (.leaf 44825046)) (.leaf 11676411))) (.node (.node (.node (.leaf 17671703) (.leaf 30422639)) (.leaf 0)) (.node (.leaf 10681861) (.leaf 27988006)))) (.node (.node (.node (.node (.leaf 0) (.leaf 14288276)) (.leaf 11561211)) (.node (.node (.leaf 35524276) (.leaf 5326744)) (.leaf 0))) (.node (.node (.node (.leaf 15537809) (.leaf 0)) (.leaf 33025877)) (.node (.leaf 0) (.leaf 15172247)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 23191672) (.leaf 18847204)) (.leaf 0)) (.node (.node (.leaf 17347961) (.leaf 0)) (.leaf 18034393))) (.node (.node (.node (.leaf 0) (.leaf 16461759)) (.leaf 5689281)) (.node (.node (.leaf 11452378) (.leaf 10413556)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 6524467) (.leaf 0)) (.leaf 21865043)) (.node (.node (.leaf 0) (.leaf 44623054)) (.leaf 26959672))) (.node (.node (.node (.leaf 25230614) (.leaf 12565420)) (.leaf 0)) (.node (.leaf 17796862) (.leaf 9341632))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 22290570)) (.leaf 11246485)) (.node (.node (.leaf 14266951) (.leaf 23556080)) (.leaf 0))) (.node (.node (.node (.leaf 15357624) (.leaf 0)) (.leaf 13730786)) (.node (.node (.leaf 0) (.leaf 33249470)) (.leaf 6308902)))) (.node (.node (.node (.node (.leaf 8357740) (.leaf 31863842)) (.leaf 0)) (.node (.node (.leaf 11520143) (.leaf 0)) (.leaf 16223737))) (.node (.node (.node (.leaf 0) (.leaf 12197703)) (.leaf 12009737)) (.node (.leaf 58891304) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 19878990) (.leaf 0)) (.leaf 9106198)) (.node (.node (.leaf 0) (.leaf 31107341)) (.leaf 10423359))) (.node (.node (.node (.leaf 22135761) (.leaf 13418325)) (.leaf 0)) (.node (.node (.leaf 25981077) (.leaf 0)) (.leaf 21076380)))) (.node (.node (.node (.node (.leaf 0) (.leaf 11682719)) (.leaf 13905526)) (.node (.node (.leaf 17760124) (.leaf 6199246)) (.leaf 0))) (.node (.node (.node (.leaf 5493694) (.leaf 0)) (.leaf 23412656)) (.node (.leaf 0) (.leaf 21284251))))) (.node (.node (.node (.node (.node (.leaf 28387885) (.leaf 6520088)) (.leaf 0)) (.node (.node (.leaf 16665088) (.leaf 0)) (.leaf 29497713))) (.node (.node (.node (.leaf 0) (.leaf 12627280)) (.leaf 21613647)) (.node (.leaf 23485376) (.leaf 0)))) (.node (.node (.node (.node (.leaf 9719196) (.leaf 0)) (.leaf 33878272)) (.node (.node (.leaf 0) (.leaf 9908492)) (.leaf 23361791))) (.node (.node (.node (.leaf 12358253) (.leaf 12014047)) (.leaf 0)) (.node (.leaf 11210615) (.leaf 35540373))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 11680529)) (.leaf 21764602)) (.node (.node (.leaf 23961839) (.leaf 6385148)) (.leaf 0))) (.node (.node (.node (.leaf 7480678) (.leaf 0)) (.leaf 16454752)) (.node (.node (.leaf 0) (.leaf 13997142)) (.leaf 17497360)))) (.node (.node (.node (.node (.leaf 20374569) (.leaf 18097803)) (.leaf 0)) (.node (.node (.leaf 13038311) (.leaf 0)) (.leaf 31828514))) (.node (.node (.node (.leaf 0) (.leaf 23361058)) (.leaf 6505357)) (.node (.leaf 7906896) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 17520873) (.leaf 0)) (.leaf 11741744)) (.node (.node (.leaf 0) (.leaf 10960144)) (.leaf 12617804))) (.node (.node (.node (.leaf 14870808) (.leaf 13443422)) (.leaf 0)) (.node (.node (.leaf 6543043) (.leaf 0)) (.leaf 18683264)))) (.node (.node (.node (.node (.leaf 0) (.leaf 31510917)) (.leaf 14450365)) (.node (.node (.leaf 58995426) (.leaf 13040175)) (.leaf 0))) (.node (.node (.node (.leaf 20846717) (.leaf 0)) (.leaf 10187285)) (.node (.leaf 0) (.leaf 9048902)))))) (.node (.node (.node (.node (.node (.node (.leaf 10532990) (.leaf 19599335)) (.leaf 0)) (.node (.node (.leaf 8794627) (.leaf 0)) (.leaf 23159206))) (.node (.node (.node (.leaf 0) (.leaf 8467808)) (.leaf 31696094)) (.node (.node (.leaf 43443189) (.leaf 10322247)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 12495781) (.leaf 0)) (.leaf 21512055)) (.node (.node (.leaf 0) (.leaf 16142712)) (.leaf 10882301))) (.node (.node (.node (.leaf 15475922) (.leaf 11508396)) (.leaf 0)) (.node (.leaf 19790509) (.leaf 19633614))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 31708408)) (.leaf 10103337)) (.node (.node (.leaf 8175011) (.leaf 23167584)) (.leaf 0))) (.node (.node (.node (.leaf 25119456) (.leaf 0)) (.leaf 44783547)) (.node (.leaf 0) (.leaf 14003385)))) (.node (.node (.node (.node (.leaf 19441700) (.leaf 8303335)) (.leaf 0)) (.node (.node (.leaf 23352822) (.leaf 0)) (.leaf 8227376))) (.node (.node (.node (.leaf 0) (.leaf 59110111)) (.leaf 8436573)) (.node (.leaf 18506518) (.leaf 0))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 16398989) (.leaf 0)) (.leaf 13326986)) (.node (.node (.leaf 0) (.leaf 29195723)) (.leaf 7678812))) (.node (.node (.node (.leaf 18059926) (.leaf 26749148)) (.leaf 0)) (.node (.node (.leaf 12752242) (.leaf 0)) (.leaf 33570076)))) (.node (.node (.node (.node (.leaf 0) (.leaf 16624736)) (.leaf 11640221)) (.node (.node (.leaf 59117053) (.leaf 8890517)) (.leaf 0))) (.node (.node (.node (.leaf 8098054) (.leaf 0)) (.leaf 17534116)) (.node (.leaf 0) (.leaf 25100239))))) (.node (.node (.node (.node (.node (.leaf 21219343) (.leaf 11778040)) (.leaf 0)) (.node (.node (.leaf 15460921) (.leaf 0)) (.leaf 7133476))) (.node (.node (.node (.leaf 0) (.leaf 59144486)) (.leaf 31553264)) (.node (.node (.leaf 21894068) (.leaf 11654241)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 17840739) (.leaf 0)) (.leaf 14338433)) (.node (.node (.leaf 0) (.leaf 10295502)) (.leaf 29945254))) (.node (.node (.node (.leaf 12584282) (.leaf 9579484)) (.leaf 0)) (.node (.leaf 6605532) (.leaf 15066307)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 13547436)) (.leaf 15761813)) (.node (.node (.leaf 42348984) (.leaf 14560038)) (.leaf 0))) (.node (.node (.node (.leaf 10088258) (.leaf 0)) (.leaf 16656664)) (.node (.node (.leaf 0) (.leaf 16481586)) (.leaf 6004869)))) (.node (.node (.node (.node (.leaf 10859480) (.leaf 21501730)) (.leaf 0)) (.node (.node (.leaf 9709132) (.leaf 0)) (.leaf 37829007))) (.node (.node (.node (.leaf 0) (.leaf 12573090)) (.leaf 23510926)) (.node (.leaf 35497098) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 5909815) (.leaf 0)) (.leaf 25146179)) (.node (.node (.leaf 0) (.leaf 21598593)) (.leaf 16501188))) (.node (.node (.node (.leaf 23336204) (.leaf 5735957)) (.leaf 0)) (.node (.leaf 11471914) (.leaf 8111869)))) (.node (.node (.node (.node (.leaf 0) (.leaf 20591004)) (.leaf 8625079)) (.node (.node (.leaf 8492167) (.leaf 15272512)) (.leaf 0))) (.node (.node (.node (.leaf 41642440) (.leaf 0)) (.leaf 30408038)) (.node (.leaf 0) (.leaf 17781034))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 14056569) (.leaf 10138804)) (.leaf 0)) (.node (.node (.leaf 6439055) (.leaf 0)) (.leaf 16091715))) (.node (.node (.node (.leaf 0) (.leaf 21174492)) (.leaf 21996212)) (.node (.node (.leaf 17426398) (.leaf 7280020)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 15652347) (.leaf 0)) (.leaf 9488188)) (.node (.node (.leaf 0) (.leaf 18399927)) (.leaf 8898431))) (.node (.node (.node (.leaf 28576552) (.leaf 10653488)) (.leaf 0)) (.node (.leaf 14903251) (.leaf 33908572))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 26414381)) (.leaf 8260930)) (.node (.node (.leaf 9832692) (.leaf 41821467)) (.leaf 0))) (.node (.node (.node (.leaf 12558305) (.leaf 0)) (.leaf 22927355)) (.node (.node (.leaf 0) (.leaf 8240793)) (.leaf 15481444)))) (.node (.node (.node (.node (.leaf 15715180) (.leaf 5044129)) (.leaf 0)) (.node (.node (.leaf 16555248) (.leaf 0)) (.leaf 10932522))) (.node (.node (.node (.leaf 0) (.leaf 16580517)) (.leaf 15004341)) (.node (.leaf 21904366) (.leaf 0)))))) (.node (.node (.node (.node (.node (.node (.leaf 20073266) (.leaf 0)) (.leaf 32667876)) (.node (.node (.leaf 0) (.leaf 18914504)) (.leaf 12770296))) (.node (.node (.node (.leaf 11783997) (.leaf 23737629)) (.leaf 0)) (.node (.node (.leaf 20858033) (.leaf 0)) (.leaf 21920288)))) (.node (.node (.node (.node (.leaf 0) (.leaf 28772564)) (.leaf 8928836)) (.node (.node (.leaf 16935615) (.leaf 20644494)) (.leaf 0))) (.node (.node (.node (.leaf 16606669) (.leaf 0)) (.leaf 11595836)) (.node (.leaf 0) (.leaf 9423602))))) (.node (.node (.node (.node (.node (.leaf 23365437) (.leaf 12398492)) (.leaf 0)) (.node (.node (.leaf 23955556) (.leaf 0)) (.leaf 15244141))) (.node (.node (.node (.leaf 0) (.leaf 19816984)) (.leaf 7006362)) (.node (.leaf 16519281) (.leaf 0)))) (.node (.node (.node (.node (.leaf 8738604) (.leaf 0)) (.leaf 24395406)) (.node (.node (.leaf 0) (.leaf 20960705)) (.leaf 41802070))) (.node (.node (.node (.leaf 23862566) (.leaf 11755463)) (.leaf 0)) (.node (.leaf 25130839) (.leaf 8230880)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 16275330)) (.leaf 8259382)) (.node (.node (.leaf 15389898) (.leaf 20345276)) (.leaf 0))) (.node (.node (.node (.leaf 16943579) (.leaf 0)) (.leaf 27717646)) (.node (.node (.leaf 0) (.leaf 14597862)) (.leaf 11975288)))) (.node (.node (.node (.node (.leaf 11931116) (.leaf 8199495)) (.leaf 0)) (.node (.node (.leaf 11635267) (.leaf 0)) (.leaf 11742688))) (.node (.node (.node (.leaf 0) (.leaf 32763912)) (.leaf 9897474)) (.node (.leaf 19803777) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 14406996) (.leaf 0)) (.leaf 12797079)) (.node (.node (.leaf 0) (.leaf 18441592)) (.leaf 8332544))) (.node (.node (.node (.leaf 17844269) (.leaf 15499984)) (.leaf 0)) (.node (.node (.leaf 22506158) (.leaf 0)) (.leaf 19011870)))) (.node (.node (.node (.node (.leaf 0) (.leaf 9029963)) (.leaf 16518763)) (.node (.node (.leaf 24745003) (.leaf 13374574)) (.leaf 0))) (.node (.node (.node (.leaf 5591020) (.leaf 0)) (.leaf 25594158)) (.node (.leaf 0) (.leaf 23099677)))))) (.node (.node (.node (.node (.node (.node (.leaf 16984333) (.leaf 17250157)) (.leaf 0)) (.node (.node (.leaf 8302667) (.leaf 0)) (.leaf 45062278))) (.node (.node (.node (.leaf 0) (.leaf 33313327)) (.leaf 7749993)) (.node (.node (.leaf 8922135) (.leaf 14821457)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 10515249) (.leaf 0)) (.leaf 26653972)) (.node (.node (.leaf 0) (.leaf 14726992)) (.leaf 16873382))) (.node (.node (.node (.leaf 38126734) (.leaf 5820111)) (.leaf 0)) (.node (.leaf 13211062) (.leaf 17770187))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 16990428)) (.leaf 22281583)) (.node (.node (.leaf 33038562) (.leaf 14012724)) (.leaf 0))) (.node (.node (.node (.leaf 41716066) (.leaf 0)) (.leaf 9220796)) (.node (.leaf 0) (.leaf 11680896)))) (.node (.node (.node (.node (.leaf 14740855) (.leaf 10779236)) (.leaf 0)) (.node (.node (.leaf 7203498) (.leaf 0)) (.leaf 18976376))) (.node (.node (.node (.leaf 0) (.leaf 8767058)) (.leaf 16521859)) (.node (.leaf 30100476) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 7447949) (.leaf 0)) (.leaf 43947560)) (.node (.node (.leaf 0) (.leaf 45193903)) (.leaf 11112310))) (.node (.node (.node (.leaf 29814199) (.leaf 7730461)) (.leaf 0)) (.node (.node (.leaf 16376032) (.leaf 0)) (.leaf 11706328)))) (.node (.node (.node (.node (.leaf 0) (.leaf 19016271)) (.leaf 5987644)) (.node (.node (.leaf 22412523) (.leaf 11724196)) (.leaf 0))) (.node (.node (.node (.leaf 30718974) (.leaf 0)) (.leaf 13412176)) (.node (.leaf 0) (.leaf 15488726))))) (.node (.node (.node (.node (.node (.leaf 8835852) (.leaf 16212088)) (.leaf 0)) (.node (.node (.leaf 15211320) (.leaf 0)) (.leaf 24874962))) (.node (.node (.node (.leaf 0) (.leaf 10947035)) (.leaf 11414621)) (.node (.node (.leaf 24742690) (.leaf 5827121)) (.leaf 0)))) (.node (.node (.node (.node (.leaf 10943129) (.leaf 0)) (.leaf 8137665)) (.node (.node (.leaf 0) (.leaf 32583885)) (.leaf 6952763))) (.node (.node (.node (.leaf 15538513) (.leaf 18677788)) (.leaf 0)) (.node (.leaf 13883062) (.leaf 22172200)))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 15553671)) (.leaf 22421230)) (.node (.node (.leaf 22490533) (.leaf 14972627)) (.leaf 0))) (.node (.node (.node (.leaf 5780606) (.leaf 0)) (.leaf 18212396)) (.node (.node (.leaf 0) (.leaf 44038456)) (.leaf 12322324)))) (.node (.node (.node (.node (.leaf 22904756) (.leaf 11378561)) (.leaf 0)) (.node (.node (.leaf 31666750) (.leaf 0)) (.leaf 28396189))) (.node (.node (.node (.leaf 0) (.leaf 27461570)) (.leaf 9939495)) (.node (.leaf 9901889) (.leaf 0))))) (.node (.node (.node (.node (.node (.leaf 13747358) (.leaf 0)) (.leaf 21456797)) (.node (.node (.leaf 0) (.leaf 7533154)) (.leaf 20206674))) (.node (.node (.node (.leaf 16512939) (.leaf 23976981)) (.leaf 0)) (.node (.leaf 5817634) (.leaf 43024109)))) (.node (.node (.node (.node (.leaf 0) (.leaf 15205017)) (.leaf 41797161)) (.node (.node (.leaf 15813791) (.leaf 13010713)) (.leaf 0))) (.node (.node (.node (.leaf 13086085) (.leaf 0)) (.leaf 11067881)) (.node (.leaf 0) (.leaf 6709163))))))))))

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_0 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 0 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_16 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 16 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_32 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 32 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_48 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 48 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_64 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 64 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_80 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 80 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_96 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 96 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_112 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 112 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_128 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 128 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_144 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 144 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_160 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 160 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_176 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 176 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_192 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 192 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_208 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 208 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_224 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 224 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_240 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 240 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_256 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 256 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_272 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 272 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_288 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 288 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_304 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 304 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_320 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 320 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_336 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 336 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_352 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 352 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_368 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 368 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_384 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 384 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_400 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 400 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_416 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 416 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_432 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 432 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_448 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 448 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_464 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 464 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_480 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 480 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_496 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 496 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_512 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 512 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_528 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 528 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_544 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 544 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_560 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 560 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_576 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 576 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_592 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 592 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_608 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 608 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_624 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 624 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_640 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 640 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_656 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 656 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_672 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 672 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_688 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 688 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_704 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 704 16 =
      true := by decide +kernel

/-- Exact transfer check on the indicated consecutive residues. -/
theorem levelSix_chunk_720 :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 720 9 =
      true := by decide +kernel

/-- All checked chunks cover the complete output group. -/
theorem levelSix_transfer :
    levelSix.checkRange (levelFive.directEntry 3089969650018044 6 16) 0 729 = true := by
  have h0 := levelSix_chunk_0
  have h1 := Entries.checkRange_append levelSix _ 0 16 16 h0 levelSix_chunk_16
  have h2 := Entries.checkRange_append levelSix _ 0 32 16 h1 levelSix_chunk_32
  have h3 := Entries.checkRange_append levelSix _ 0 48 16 h2 levelSix_chunk_48
  have h4 := Entries.checkRange_append levelSix _ 0 64 16 h3 levelSix_chunk_64
  have h5 := Entries.checkRange_append levelSix _ 0 80 16 h4 levelSix_chunk_80
  have h6 := Entries.checkRange_append levelSix _ 0 96 16 h5 levelSix_chunk_96
  have h7 := Entries.checkRange_append levelSix _ 0 112 16 h6 levelSix_chunk_112
  have h8 := Entries.checkRange_append levelSix _ 0 128 16 h7 levelSix_chunk_128
  have h9 := Entries.checkRange_append levelSix _ 0 144 16 h8 levelSix_chunk_144
  have h10 := Entries.checkRange_append levelSix _ 0 160 16 h9 levelSix_chunk_160
  have h11 := Entries.checkRange_append levelSix _ 0 176 16 h10 levelSix_chunk_176
  have h12 := Entries.checkRange_append levelSix _ 0 192 16 h11 levelSix_chunk_192
  have h13 := Entries.checkRange_append levelSix _ 0 208 16 h12 levelSix_chunk_208
  have h14 := Entries.checkRange_append levelSix _ 0 224 16 h13 levelSix_chunk_224
  have h15 := Entries.checkRange_append levelSix _ 0 240 16 h14 levelSix_chunk_240
  have h16 := Entries.checkRange_append levelSix _ 0 256 16 h15 levelSix_chunk_256
  have h17 := Entries.checkRange_append levelSix _ 0 272 16 h16 levelSix_chunk_272
  have h18 := Entries.checkRange_append levelSix _ 0 288 16 h17 levelSix_chunk_288
  have h19 := Entries.checkRange_append levelSix _ 0 304 16 h18 levelSix_chunk_304
  have h20 := Entries.checkRange_append levelSix _ 0 320 16 h19 levelSix_chunk_320
  have h21 := Entries.checkRange_append levelSix _ 0 336 16 h20 levelSix_chunk_336
  have h22 := Entries.checkRange_append levelSix _ 0 352 16 h21 levelSix_chunk_352
  have h23 := Entries.checkRange_append levelSix _ 0 368 16 h22 levelSix_chunk_368
  have h24 := Entries.checkRange_append levelSix _ 0 384 16 h23 levelSix_chunk_384
  have h25 := Entries.checkRange_append levelSix _ 0 400 16 h24 levelSix_chunk_400
  have h26 := Entries.checkRange_append levelSix _ 0 416 16 h25 levelSix_chunk_416
  have h27 := Entries.checkRange_append levelSix _ 0 432 16 h26 levelSix_chunk_432
  have h28 := Entries.checkRange_append levelSix _ 0 448 16 h27 levelSix_chunk_448
  have h29 := Entries.checkRange_append levelSix _ 0 464 16 h28 levelSix_chunk_464
  have h30 := Entries.checkRange_append levelSix _ 0 480 16 h29 levelSix_chunk_480
  have h31 := Entries.checkRange_append levelSix _ 0 496 16 h30 levelSix_chunk_496
  have h32 := Entries.checkRange_append levelSix _ 0 512 16 h31 levelSix_chunk_512
  have h33 := Entries.checkRange_append levelSix _ 0 528 16 h32 levelSix_chunk_528
  have h34 := Entries.checkRange_append levelSix _ 0 544 16 h33 levelSix_chunk_544
  have h35 := Entries.checkRange_append levelSix _ 0 560 16 h34 levelSix_chunk_560
  have h36 := Entries.checkRange_append levelSix _ 0 576 16 h35 levelSix_chunk_576
  have h37 := Entries.checkRange_append levelSix _ 0 592 16 h36 levelSix_chunk_592
  have h38 := Entries.checkRange_append levelSix _ 0 608 16 h37 levelSix_chunk_608
  have h39 := Entries.checkRange_append levelSix _ 0 624 16 h38 levelSix_chunk_624
  have h40 := Entries.checkRange_append levelSix _ 0 640 16 h39 levelSix_chunk_640
  have h41 := Entries.checkRange_append levelSix _ 0 656 16 h40 levelSix_chunk_656
  have h42 := Entries.checkRange_append levelSix _ 0 672 16 h41 levelSix_chunk_672
  have h43 := Entries.checkRange_append levelSix _ 0 688 16 h42 levelSix_chunk_688
  have h44 := Entries.checkRange_append levelSix _ 0 704 16 h43 levelSix_chunk_704
  have h45 := Entries.checkRange_append levelSix _ 0 720 9 h44 levelSix_chunk_720
  exact h45

/-- The integer cap covers all residues. -/
theorem levelSix_cap : levelSix.allLE 4651932141793643 = true := by decide +kernel

/-- Scaled maximum comparison. -/
theorem levelSix_max_comparison : 1 * 4651932141793643 ≤ 17 * 2 ^ 48 := by
  decide +kernel

/-- Complete integer energy comparison. -/
theorem levelSix_energy_comparison :
    1000 * levelSix.energySum 729 ≤
      4001 * 729 * (2 ^ 48) ^ 2 := by decide +kernel

/-- Square enclosures include every residue. -/
theorem levelSix_square_enclosures : ∀ i : Fin 729,
    levelSix.lookup i.val ≤ levelSixRoots.lookup i.val ^ 2 := by decide +kernel

/-- Complete fractional numerator comparison. -/
theorem levelSix_fractional_comparison :
    250000 * levelSix.fractionalSum levelSixRoots 729 ≤
        449901 * 729 * 2 ^ 72 := by decide +kernel

end WordCertDensity.Certificates
