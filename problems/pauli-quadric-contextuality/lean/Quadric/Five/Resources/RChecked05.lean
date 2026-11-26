import Quadric.Five.Intervals
import Quadric.Five.Resources.System05

namespace Quadric.Five.Census.Block.Case05
set_option maxRecDepth 16384
set_option maxHeartbeats 24000000
set_option Elab.async false
private theorem cachedMinimum : packList system.lowFirst=482434396539786685721028047652911744678027311567245014760430779125841040228795278418744187308066327171014462855458508053325553914708623608991895832248483475760325085222119180013086753309229481217805907900831694546912803114288393684486910235735397143917813928766532267832004836364490472592190622149924546815587624549494548492022887775137200590114955118038859152305539907960642629875638714374916915578090077138541146872183261844120073826521151563474078374861463885085844231470243143320412621535704628859278413077714565572128974166678085943012089051374081505690118255878243390383124670125838454732040415282682096724366353981709881885712617267191456242227588449516748672948287133219471180002945647042682637709134051958269089910267388129564684986094236159447830126625655038433223966727179878974584717486187887104793360106939328939906997210329068034650579426352167635102246949470236584329610241156008704317346792406190618680297919299944542553125217346279722813039358429645910126739428479107189338445401803356721194554161888150093291401764166580431246157204396204400328590630779634279287017427018710514552284629901378488242855197693655733395157206069670666332635723927133326759331106897909358046468684268606620589272265926138996477076605977787570644568325999422321865982027463287382311255844952604784168983822187620981548844240373311815711678851462304578088914621108894582986793465485942372032651424255149354597605494809618212509078004840844892282937567162030206526078303255967440531976956654233390108579273984365222784566748574425027912562569646869514099117194310314809156322545083529829329016635148266460265318619433905219687032611657024116405352602302016044340555553096352510383590877152795267878653580389401180853160284090023306160827238622780715627977079360240270760818472509905971277018497608744177144828038111229835990708473576692951590831683901868464265432429177621181531477309908510706669983985212915695274499231436100437232285911186495569763937479740430575485851087749589350766517830102772714122138107325098447152033387382032317063640123921607821690128500308101078377437076910259436969824353472806828270055997372777046426208556366182171683665077463240979514927607021470983465781675795711597915321412907501018583197086979964658822807399520141174509948719051972217241332029825738360115737988067310716961780623650598174675937677182938024685911828943939817172825307124848954880622655616354026183455652459540618805105440350393373439854136538263976929634302457395788424512861435493564206620681275215719132245067913788751351096010860614645442214326148453211368294713121450192507073993782170097510939112251726894384101000007788470286984389080357249273595725638687548769044249437665547161590058646945753955762146746496412804530770398082864327139747190489186365970622628998128135780314423354067280251046069575846920715841166809619366910095426561910527109973892988238215698062126182012200188921091600987699008582208350643673525563943582076907526611330270564347379094381453137489393688768437591132012402343581941594044370257147947249356466112646521829129465241283152768268471939700910734350 := by decide +kernel
noncomputable def row0 : List Row := blockRows% "28|424/27/26|416|418|424,386,390,450,454|425|426,450|428|430|440|488/26/26/25/24|416|422|424|425|426|428/24/31/31/30/30/30/29/28/28/26|296|297|424,322,330,450,458|425,450|426|428|429/29/25|40|168,322,330,450,458|170|232|234|288,450|289|290|296,320,322,330,386,448,450,458|297,322,450|298,450|300|301|360|392,386,390,450,454|416,322,384,386,390,448,450,454|417,450|418,386,450|420|422|424,194,258,320,322,323,326,328,330,331,338,346,384,386,387,388,390,391,394,402,406,448,450,451,452,454,455,456,458,459,462,466,470,474,482,834,842,850,898,902,962,966,970,978|425,322,323,330,386,390,448,450,451,454,455,458,466|426,322,330,386,390,448,450,451,454,458,466,962|427,450|428,322,330,386,390,448,450,454,458|429,450,454,458|430,450,454,458|440,386,390,450,454|442,450|480|488,322,330,386,390,450,451,454,458,962|489,450|490,386,450,458|492|504|506|728|936,322,330,450,458|937,450/26|424,450|425,450/28/28/25|416,450|424,386,390,450,454,458|425,450,454|426,450|428,450,454|429,450|488/25|424/28|424|425/31/29|168|296|392|416|424,322,330,386,390,402,450,451,454,458,466,962|425,450|426|440|488|936/29|424/31/30/28|424/27"
theorem leaf0 : Segment system t0 t1 t2 0 32 row0 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row32 : List Row := blockRows% "27/29/29/28/29/28/28/27/31/33/33/32/33/32/32/31/26/29/26|424,450|426,450|488/27/28/29/26/27/30/32/30/32/32/34/32/32"
theorem leaf32 : Segment system t0 t1 t2 32 32 row32 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row64 : List Row := blockRows% "26/29/28/28/28/27/26/26/30/33/32/32/32/31/30/30/24|296|301|424|425|426|428/28/25|168|296,450|424,322,330,450,454,458|425,450|426,450,458|428,450,458|430,450|488/26/26/29/25|424,450/26/27/30/28|424/31/29/32/29/29"
theorem leaf64 : Segment system t0 t1 t2 64 32 row64 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row96 : List Row := blockRows% "25/28/28/29/27/29/29/29/29/32/32/34/31/31/33/32/24/27/26/27/26/29/26/27/28/30/29/32/30/31/30/32"
theorem leaf96 : Segment system t0 t1 t2 96 32 row96 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row128 : List Row := blockRows% "30/30/29/29/29/28/27/27/31/33/30/31/32/30/30/29/28/31/29|424,450/28/30/29/27|424/26/29/32/29|424|728,543/30/32/31/29/28"
theorem leaf128 : Segment system t0 t1 t2 128 32 row128 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row160 : List Row := blockRows% "30/33/33/32/32/30/31/29/31/33/32/33/33/30/32/29/29/31/30/32/31/33/31/31/31/33/30/33/33/34/34/32"
theorem leaf160 : Segment system t0 t1 t2 160 32 row160 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row192 : List Row := blockRows% "29/32/31/31/31/29/29/29/32/33/32/33/32/30/32/30/26/29/27|424/30/28/31/28/28/28/31/29/32/30/31/31/30"
theorem leaf192 : Segment system t0 t1 t2 192 32 row192 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row224 : List Row := blockRows% "28/30/31/33/29/30/32/29/29/30/32/33/29/30/32/29/27/29/28/31/29/30/29/31/29/30/30/32/30/30/31/31"
theorem leaf224 : Segment system t0 t1 t2 224 32 row224 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row256 : List Row := blockRows% "28/27/27|424/26/26/25|293|389,388|421,388/25/24|389,388|421/29/31/30/30/30/29/29/28/27|297|424,450|425,450|429|937/29/27|288|296,450|297,450|416,386,448,450|417,450|424,320,322,330,338,384,386,390,402,448,450,451,454,458,466,962|425,322,386,448,450,451,454,458,466|426,450|428,450|429,450|440|488|936,450|937,450/28|424,450|425,450/29/28/27|424,450|425,450/27/29|424|425|936|937/32/30|416|424,386,450,458,466|425,450|936|937/29|416|424|425/33/31/30/29"
theorem leaf256 : Segment system t0 t1 t2 256 32 row256 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row288 : List Row := blockRows% "27/29/29/28/29/28/28/27/30/33/31/31/33/31/32/30/26/29/28/28/28/29/28/28/30/32/30/33/32/34/34/33"
theorem leaf288 : Segment system t0 t1 t2 288 32 row288 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row320 : List Row := blockRows% "26/29/29/28/28/27|293/27/26/30/33/33/32/32/30/31/30/25|296|297|301,328|424|425|428|429|813,328/28/27|424,450,458|425,450/28/27/30/27/28/29|424/31/30|424/33/31/33/31/31"
theorem leaf320 : Segment system t0 t1 t2 320 32 row320 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row352 : List Row := blockRows% "25/28/28/29/27/27|293,480|295,480/30/28/29/31/32/34/30/29/33/30/24|301|813,328/27/27/28/26/28/28/28/28/30/30/33/30/30/32/33"
theorem leaf352 : Segment system t0 t1 t2 352 32 row352 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row384 : List Row := blockRows% "31/30/30/29/29/28/28/27/31/32/31/31/32/30/31/30/30/33/32/32/32/31/30/30/31/33/31|424/32/34/33/32/31"
theorem leaf384 : Segment system t0 t1 t2 384 32 row384 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row416 : List Row := blockRows% "30/33/33/32/32/30/31/29/30/31/32/31/31/30/32/29/29/32/31/33/31/33/33/33/31/32/31/34/34/34/35/32"
theorem leaf416 : Segment system t0 t1 t2 416 32 row416 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row448 : List Row := blockRows% "29/32/32/31/31/29/30/29/32/32/34/34/32/30/33/30/28/31/30/33/30/32/30/31/32/33/32/35/33/33/34/33"
theorem leaf448 : Segment system t0 t1 t2 448 32 row448 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row480 : List Row := blockRows% "28/30/31/32/29/28/31/28/29/30/32/33/29/29/31/29/27/30/30/33/29/29/31/31/30/30/31/32/30/30/32/32"
theorem leaf480 : Segment system t0 t1 t2 480 32 row480 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row512 : List Row := blockRows% "28/27/27|418|424,450|426,450|430|440|442|506/26/26/25/25|416|418|422,388|424|426|428|430|438,388|442|446|498/24|422|438,388/29/31/28|424/28/30/29/28/28/27|424/29/27|168|288|296,322,448,450|298,450|416,450|418,450|424,320,322,330,338,384,386,390,402,448,450,454,458,466,834,962,966,978|425,450|426,322,386,448,450,454,458,466,962|428,450|430,450|440,450|442,450|488,450|490,450|506/28/29/28/27|424,450,454|426,450/27/30/33/29|296|424,450|426/30/33/32/29|424/30"
theorem leaf512 : Segment system t0 t1 t2 512 32 row512 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row544 : List Row := blockRows% "27/29/29/28/29/28/28/27/28/31/29/29/32/29/30/28/26/29/28|424,450|426,450/28/28/29/28/28/28/31/28|424/31/32/34/32/32"
theorem leaf544 : Segment system t0 t1 t2 544 32 row544 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row576 : List Row := blockRows% "26/29/29/28/28/27/27/26/30/33/32/32/32/30/31/29/25/28/27|424,450|426,450/28/27/30/27/28/29/32/29/34/31/33/31/33"
theorem leaf576 : Segment system t0 t1 t2 576 32 row576 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row608 : List Row := blockRows% "25|46,328|294|302,328/28/28/29/27|294/27|294,480|295,480/30/27/28/29/30/32/28/29/31/28/24|46,328|302/27/27/28/26/28/28/28/28/30/28/32/29/30/31/31"
theorem leaf608 : Segment system t0 t1 t2 608 32 row608 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row640 : List Row := blockRows% "31/30/29/29/29/28/28/27/29/31/29/29/30/29/29/28/30/33/30/31/32/31/30/30/31/34/30|424/31/34/34/30/31"
theorem leaf640 : Segment system t0 t1 t2 640 32 row640 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row672 : List Row := blockRows% "30/32/31/30/31/28/29/27/28/29/30/29/29/28/30/27/29/32/29/33/31/32/32/31/29/31/29/33/32/33/33/32"
theorem leaf672 : Segment system t0 t1 t2 672 32 row672 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row704 : List Row := blockRows% "29/32/32/31/31/29/30/28/30/31/32/32/30/29/31/28/28/31/30/33/30/32/30/31/31/34/30/35/33/33/32/33"
theorem leaf704 : Segment system t0 t1 t2 704 32 row704 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row736 : List Row := blockRows% "27/28/29/30/27/27/29/26/27/28/30/31/27/27/29/27/27/29/28/31/28/29/30/29/28/29/29/32/28/29/30/30"
theorem leaf736 : Segment system t0 t1 t2 736 32 row736 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row768 : List Row := blockRows% "27/27/27/26/26/25|293/25/24/27/28/27/26/29/26/27/25/27/29/28|424,450/28/29/28/28/27/28/31/29|424/29/32/31/29/29"
theorem leaf768 : Segment system t0 t1 t2 768 32 row768 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row800 : List Row := blockRows% "27/29/27/27/29/27/28/26/26/27/27/26/28/25/27/24/26/29/27/28/28/28/29/28/26/28/27/29/29/30/31/29"
theorem leaf800 : Segment system t0 t1 t2 800 32 row800 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row832 : List Row := blockRows% "26/29/29/28/28/26|293|295/27/26/29/30/30/29/31/28/30/27/25/28/28/29/27/29/29/29/29/31/29/33/31/31/33/32"
theorem leaf832 : Segment system t0 t1 t2 832 32 row832 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row864 : List Row := blockRows% "25|294/27/28/28/26|294|295/25|293,480,484,488|294,480,484,488|295,352,360,416,420,448,480,484,488|301,480|303,480,488|422,480|423,480,484/28/25|295/24/25/27/28/26/27|293|295/29/26/24/27/27/28/26/26/29/27/25/26/27/29/27/28/30/29"
theorem leaf864 : Segment system t0 t1 t2 864 32 row864 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row896 : List Row := blockRows% "29/29/28/27/29/27/28/26/27/27/28/26/28/25/27/24/30/33/30/30/32/31/30/30/29/32/30/30/32/30/30/29"
theorem leaf896 : Segment system t0 t1 t2 896 32 row896 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row928 : List Row := blockRows% "27/28/29/27/29/26/28/25/25/26/28/25/27/24/26/23/27/29/28/31/30/30/32/29/26/27/28/30/28/29/31/28"
theorem leaf928 : Segment system t0 t1 t2 928 32 row928 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row960 : List Row := blockRows% "29/31/32/30/29/27/29/26/28/29/30/28/28/27/29/26/28/31/30/34/30/30/32/30/29/30/30/33/31/31/32/31"
theorem leaf960 : Segment system t0 t1 t2 960 32 row960 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row992 : List Row := blockRows% "25/26/28/28/25/25|295/27/24/23/24/26/27/25/25|293/27/25/26/27/28/30/26/27/29/27/24/25/27/28/26/27/29/28"
theorem leaf992 : Segment system t0 t1 t2 992 32 row992 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1024 : List Row := blockRows% "28/28/28/27/29/27/26/25/30/30/29/29/31/28/28/27/26/27/25|424,450|425|426/25/28/27/25/24/27/28/26|424/27/30/29/27/26"
theorem leaf1024 : Segment system t0 t1 t2 1024 32 row1024 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1056 : List Row := blockRows% "29/29/30/29/31/29/30/29/32/31/32/32/34/29/33/30/27/27/26/27/29/29/27/27/29/30/29/30/31/31/31/30"
theorem leaf1056 : Segment system t0 t1 t2 1056 32 row1056 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1088 : List Row := blockRows% "29/30/29/29/31/28/28/27/31/32/32/31/32/28/30/28/24/27/25/26/26/28/26/26/26/29/27/29/28/30/29/28"
theorem leaf1088 : Segment system t0 t1 t2 1088 32 row1088 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1120 : List Row := blockRows% "28/29/30/30/29/28|295,480/30/29/30/29/33/33/30/29/34/30/25/27/26/27/27/27/27/26/27/28/28/30/28/28/30/28"
theorem leaf1120 : Segment system t0 t1 t2 1120 32 row1120 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1152 : List Row := blockRows% "31/30/29/28/30/27/27/26/31/31/29/29/31/27/29/27/27/30/28/27/29/28/26/25/28/31/28/29/31/29/28/27"
theorem leaf1152 : Segment system t0 t1 t2 1152 32 row1152 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1184 : List Row := blockRows% "31/32/33/32/32/28/31/28/31/30/32/30/32/28/31/27/28/30/29/30/30/30/31/29/29/30/29/31/31/31/32/29"
theorem leaf1184 : Segment system t0 t1 t2 1184 32 row1184 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1216 : List Row := blockRows% "30/31/31/30/31/27/29/27/31/31/33/31/31/27/30/27/25/28/26/29/27/28/28/27/27/29/28/31/28/29/30/28"
theorem leaf1216 : Segment system t0 t1 t2 1216 32 row1216 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1248 : List Row := blockRows% "28/28/31/32/28/28/31/28/28/28/31/31/28/28/31/27/26/27/27/29/27/27/29/27/27/27/28/29/27/27/28/28"
theorem leaf1248 : Segment system t0 t1 t2 1248 32 row1248 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1280 : List Row := blockRows% "30/29/29/28/29/28|293/28/27/31/30/31/31/33/28/32/29/29/29/28/28/31/30/28/28/29/29/28/29/33/31/31/30"
theorem leaf1280 : Segment system t0 t1 t2 1280 32 row1280 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1312 : List Row := blockRows% "30/30/30/29/31/28|293,480|295,480/30/29/32/30/32/31/34/29/34/30/29/29/29/29/31/29/29/29/31/30/31/31/33/31/34/32"
theorem leaf1312 : Segment system t0 t1 t2 1312 32 row1312 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1344 : List Row := blockRows% "29/31/31/30/31/28|293,480|295,480/30/29/33/32/35/33/33/28|293/33/29/28/30/28/28/30/30/28/28/30/31/31/32/31/31/33/31"
theorem leaf1344 : Segment system t0 t1 t2 1344 32 row1344 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1376 : List Row := blockRows% "28/28|293,480|295,352,448,480/31/29/29/26|39|261,480|263,480|293,224,352,416,448,480,481,484,488|294,480|295,96,160,224,225,320,352,353,360,384,416,420,448,480,481,484,485,488|301,480|303,480|359,480|421,480|423,480,484|599|807/30/27/30/29/34/33/30/29|293,480|295,480/34/30/27/28/29/29/29/27|293,480|295,480/29/28/29/28/31/32/29/28|293/33/30"
theorem leaf1376 : Segment system t0 t1 t2 1376 32 row1376 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1408 : List Row := blockRows% "33/31/33/31/31/27/31/28/32/29/31/29/32/27|389/30/27/31/32/31/31/33/30/30/29/30/32/30/30/34/30/31/28"
theorem leaf1408 : Segment system t0 t1 t2 1408 32 row1408 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1440 : List Row := blockRows% "32/32/33/32/32/28/31/28/29/28/32/29/31/28/31/27/31/31/33/33/32/31/34/31/29/29/30/31/31/31/32/29"
theorem leaf1440 : Segment system t0 t1 t2 1440 32 row1440 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1472 : List Row := blockRows% "31/31/35/32/31/27|293/32/28/32/31/34/31/32/27|261,165|293|389|517|773,165/32/28/29/30/30/32/30/30/32/29/30/30/31/32/30/30/33/30"
theorem leaf1472 : Segment system t0 t1 t2 1472 32 row1472 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1504 : List Row := blockRows% "28/28/31/32/28/28|293,480|295,480|599/31/28/28/28/31/31/28/28|261,165|293|295|517,105|533|581|597,573|599,573|773/31/27/28/27/31/31/28/27/32/29/27/27|813/28/29/28/27|261|293|517,105|581|597|599|773,105/30/30"
theorem leaf1504 : Segment system t0 t1 t2 1504 32 row1504 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1536 : List Row := blockRows% "30/29/29/28/29/28/28/27/32/32/31/31/33/30/31/30/30/30/28/29/31/30/28/29/31/31/30/31/35/33/32/31"
theorem leaf1536 : Segment system t0 t1 t2 1536 32 row1536 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1568 : List Row := blockRows% "30/30/30/29/31/28|294,480|295,416,448,480/30/29/30/29/30/30/32/30/32/29/29/30/29/29/31/29/29/29/31/31/31/31/34/33/34/32"
theorem leaf1568 : Segment system t0 t1 t2 1568 32 row1568 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1600 : List Row := blockRows% "29/31/31/30/31/29/30/29/33/34/35/34/34/30/33/30/28/31/28/29/30/30/28/29/32/33/32/34/33/33/34/33"
theorem leaf1600 : Segment system t0 t1 t2 1600 32 row1600 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1632 : List Row := blockRows% "28|294/28|294,480|295,480/31/29/29|294,480|295,480/26|38,480|39,480|71|86|87|102|103|118|293,480|294,224,352,416,448,480,484,488,992|295,96,160,224,320,352,360,384,416,420,448,480,481,484,488,992|302,480|303,480,488|358,480|359,224,416,480,488|422,480|423,480|599/30/27|294,480|295,480/29/30/32/31/29/30/32/29/27/29/29/29/29/27/29/28/30/30/31/32/30/30/32/30"
theorem leaf1632 : Segment system t0 t1 t2 1632 32 row1632 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1664 : List Row := blockRows% "32/32/31/31/31/28/30/27/30/29/31/29/31/28/29/27/33/34/32/33/35/32/32/31/32/32/30/30/34/31/31/28"
theorem leaf1664 : Segment system t0 t1 t2 1664 32 row1664 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1696 : List Row := blockRows% "30/30/31/30/30/27|599/29/26|86|598/27/28/30/28/29/27/29/26/31/32/32/33/31/32/33/31/29/29/30/31/31/31/32/29"
theorem leaf1696 : Segment system t0 t1 t2 1696 32 row1696 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1728 : List Row := blockRows% "31/32/34/31/31/28/30/27/30/31/33/31/31/28/30/27/31/32/32/34/32/32/33/31/30/31/31/32/32/32/33/30"
theorem leaf1728 : Segment system t0 t1 t2 1728 32 row1728 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1760 : List Row := blockRows% "26|598/27/29/30/26|38|86|102,616|118,616|294|295|598|599|630/27|38|86,676|87|102,616|118|294,480|295,480|598|599|631/29/26|86,676|87|118,676|214|598|599/26/27/29/30/26|598/27|86|295|598,573|599,573/29/26|86|598|599/27/28/30/31/27/28/30/29/27/27/28/29/27/27/30/30"
theorem leaf1760 : Segment system t0 t1 t2 1760 32 row1760 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1792 : List Row := blockRows% "28/29/29/28/29/27|293|295/28/27/30/29/29/28/30/27/29/26/29/30/29/29/31/30/30/29/31/31/30/31/35/32/32/31"
theorem leaf1792 : Segment system t0 t1 t2 1792 32 row1792 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1824 : List Row := blockRows% "29/28|295,480/28/28/29/26|293,416,480|294,480|295,352,384,416,420,448,480,484|423,480/30/27/27/27/28/26/29/26|293|295/28/25/29/29/28/29/30/27/30/28/28/29/29/29/30/30/32/29"
theorem leaf1824 : Segment system t0 t1 t2 1824 32 row1824 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1856 : List Row := blockRows% "29/29/31/30/30/27|293,480|295,416,420,480,484/30/28/30/31/33/30/32/29/31/28/28/30/30/30/30/28/30/29/31/32/32/34/33/32/35/33"
theorem leaf1856 : Segment system t0 t1 t2 1856 32 row1856 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1888 : List Row := blockRows% "27|294|295/26|293,480|294,352,480|295,320,352,360,416,448,480,488|303,480|807/30/27/27|294,480|295,352,360,480,488/24|37|38,480|39,352,360,480,488|71|87|102|103|119|261,480|263,416,420,480,484|279|291,480|292,480|293,224,352,360,416,420,448,480,481,484,488,992|294,224,352,360,416,420,448,480,484,488,864,992,996|295,96,97,104,160,164,224,225,228,232,288,320,328,352,353,356,360,361,384,388,416,417,420,421,424,448,452,456,480,481,482,484,485,488,489,492,496,864,872,928,932,992,996,1000|301,480,488|302,480|303,352,360,480,484,488|311,416,420,480,484|327|343|358,480|359,160,224,352,360,416,420,480,481,484,488,992|367|375|421,480|422,480,484|423,416,420,480,484,488|431,480|439|551|583|598|599|615|631|805|807,352,360,480,488|815|855|871|887/28/25|294,480|295,480/25/26|293|294|295/28/28/27/28|293,416,480,488|294,480|295,352,360,416,420,480,481,484,488,992|599|807/30/27/27/27/30/28/28/25|293,480|295,480/29/26/26/27/29/30/28/29/31/28"
theorem leaf1888 : Segment system t0 t1 t2 1888 32 row1888 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1920 : List Row := blockRows% "31/30/31/29/31/28/30/27/28/27/30/27/29/26/28/25/33/34/33/33/35/32/33/32/31/30/32/30/33/30/31/28"
theorem leaf1920 : Segment system t0 t1 t2 1920 32 row1920 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1952 : List Row := blockRows% "28/28/30/28/30/27/29/26/25/26/28/26/27/25|293|295|597|599/27/24/29/30/31/31/31/30/32/29/27/27/30/29/29/29/32/28"
theorem leaf1952 : Segment system t0 t1 t2 1952 32 row1952 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1984 : List Row := blockRows% "31/32/34/31/31/28/30/27/28/29/31/29/29/28/30/27/31/32/33/34/32/31/33/31/30/30/31/32/32/32/33/30"
theorem leaf1984 : Segment system t0 t1 t2 1984 32 row1984 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row2016 : List Row := blockRows% "26/27/29/28/26|294|295|598|599/26|38|39|86|87|263|293,480,484,488|294,480,484,488,992|295,224,352,360,416,420,480,484,488,992,996|303|311|359|423|535|583|597|598|599|631|807|855/28/25|86|295|598|599/24/25|295|598|599/27/28/26|599/27|87|261|263|293,480|294|295,480,488|517|519|533,573|535,565,573|581|583|597,565,569,573|598,565,569,572,573|599,557,565,568,569,572,573,633,637,693,701|631|773|789|791|805|807|855/29/26|598|599/27/28/30/29/27/28/30/27/25/25/28/28/27/27|293|597|599/30/29"
theorem leaf2016 : Segment system t0 t1 t2 2016 32 row2016 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
end Quadric.Five.Census.Block.Case05
