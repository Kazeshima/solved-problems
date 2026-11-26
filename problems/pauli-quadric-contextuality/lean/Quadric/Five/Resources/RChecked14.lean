import Quadric.Five.Intervals
import Quadric.Five.Resources.System14

namespace Quadric.Five.Census.Block.Case14
set_option maxRecDepth 16384
set_option maxHeartbeats 24000000
set_option Elab.async false
private theorem cachedMinimum : packList system.lowFirst=448010814764561282201849548898397960646486417104644892032377743154508323407940196015261224833200289412400400944623415952334863559069545592711690278991448873868640512071016319798005179907156297563189844185721087033023582966414264726826469423021000841345110892748019802279805744231997942789251432189472204876572813097854742560016035540232397836570398425350306005977253576860845674117536751558318667548420287264060507463657132201611264709282532235455911478498600567505236747782068128841593291968301025048428738982433737405703639242810574438079037574517000603259677266989112509820975455478943089234112444963263838771174843377905640617075385918201764900366607943574270550542403247443157294355887663895663160177038579504202673864145505903478172050354975449488975099386085216689149981516874749637603869794725070612264987595294969762778267930099997984828413781040332607730336721177937727567051916806252908376447081832422828368994095829038235350195820172452153135421132214728578980412239240056805932610974280307679734765078985837168464987189478303675760748902571425146470620573822740887416008102403744764581610916940928187948315834068336109619078257779105709182979806195704293761906162722758372461899157390979833014475308285952566066196428550273836271311595205739806148681886957468589753345809606632165968337016547982249046535284276507835334323898887006144851522307066308933982202427591375217456992341132586063802190720128274506141199238140641417080382551385946831044060767773737267612932235093993130713545691009854635015500189010191215379869371369769418217465204768198801690291075125054158771013161746189399405651650649507138074615257241920360102066026124598850639957963603808229674423279991145691206248469777695881530530193535227618075805602554039953717076338339435617493399452654584625067749072697127933489134478233046838237420023097964041982357074446784031923347052729166088527044750367979695442058312442811799753850590940020897683327006524253312943283927707195292452725981787237762459178117069601247178832280396508748286015745815041547038660138498220877502695533357577064073053961011713410404943529927758349945879595472015084975005740635527023509779492226696820617944492725411119486753047025157355266232930738197069584509730137916331396585107648393006076813254724088661331154113596113656512265694092272854159886969805318759806128435876737772615923723741931513122986131871029761917234905475660101642073048921255252569333225050762777809552530625648950571708091456305285896733184475600373899381192433892471807610915613872043674912133436503379214042496674866785153507421220931080170400481092895703019361180651180286956777599330816955070078494307118993127919915912301249880907359467916361279506533672753416218847329611451527070610746490771644285326985870689891625275445853296224492114173839883011261303352914377346023541622041329862985037472039583991036879034299524955755603855274102129452222378117129197919362235249716336724583192885219272567686571034747241080433389398713248217044140188354933694964907299869762086263783694973134516432429870048505651420584911294750518845588483198552128525 := by decide +kernel
noncomputable def row0 : List Row := blockRows% "29/28/27|424/27/27/26/25/25/30/30/29/29/29/28/27/27/26|424/29/26|0|32|40|136|168,450|232|288,450|290|296,322,450|297,450|392,450|416,386,450|418,450|424,322,323,330,386,390,448,450,451,454,455,458,466,834,962,966|425,450,451|426,450|428,450|440|488,386,450,451,458|490,450/26|416|424,450/28/27/25|168|392|424,450,454|425,450|426/24|424|425/29/32/29|168|296|392|416|424,386,450,458,962/30|424/31/31/28|424/28"
theorem leaf0 : Segment system t0 t1 t2 0 32 row0 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row32 : List Row := blockRows% "28/30/30/29/30/29/29/28/30/32/32/31/32/31/31/30/27/29/27|424,450/27/29/30/27/27/29/32/29/32/31/33/31/32"
theorem leaf32 : Segment system t0 t1 t2 32 32 row32 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row64 : List Row := blockRows% "27/30/29/29/29/28/27/27/29/32/31/31/31/30/29/29/24|424/27/25|168|424,450,458|426,450/26/26/28/26|424,450/25/27/31/28|424/31/29/32/28/30"
theorem leaf64 : Segment system t0 t1 t2 64 32 row64 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row96 : List Row := blockRows% "26/29/29/30/28/30/30/30/28/31/31/33/30/30/32/31/25/27/26|424/27/27/29/27/27/27/30/29/32/29/31/29/32"
theorem leaf96 : Segment system t0 t1 t2 96 32 row96 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row128 : List Row := blockRows% "31/30/29/28/30/28/27/26/30/33/30/31/32/30/30/29/27/30/28|424/27/29/28/26|424/25/30/33/30|424/31/33/32/30/29"
theorem leaf128 : Segment system t0 t1 t2 128 32 row128 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row160 : List Row := blockRows% "31/33/34/32/33/30/32/30/30/32/31/32/32/29/31/28/28/30/29/32/30/32/31/30/31/34/30/34/33/34/34/33"
theorem leaf160 : Segment system t0 t1 t2 160 32 row160 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row192 : List Row := blockRows% "30/32/31/30/31/29/29/28/31/34/32/33/31/30/31/29/25/28/26|424/29/27/30/28/27/29/32/30/33/31/32/31/31"
theorem leaf192 : Segment system t0 t1 t2 192 32 row192 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row224 : List Row := blockRows% "29/30/32/34/30/30/33/30/28/29/31/32/28/29/31/28/26/28/27/30/28/29/29/30/29/30/30/33/29/30/31/32"
theorem leaf224 : Segment system t0 t1 t2 224 32 row224 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row256 : List Row := blockRows% "29/28/28/27/27/26/26/25/28/30/29/29/29/28/28/27/28/30/28|288|416,450|424,450|425,450/28|424/30/28/27|424/26/29/32/29|288|416|424,450|425/30|416|424/32/31/30/30"
theorem leaf256 : Segment system t0 t1 t2 256 32 row256 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row288 : List Row := blockRows% "28/30/30/29/30/29/29/28/29/32/30/30/32/30/31/29/27/29/29/29/29/30/29/29/29/32/29/32/31/33/33/32"
theorem leaf288 : Segment system t0 t1 t2 288 32 row288 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row320 : List Row := blockRows% "27/30/30/29/29/28/28/27/29/32/32/31/31/29/30/29/26/28/27|424,450/28/28/30/28/27/28/31/30|424/33/30/32/30/32"
theorem leaf320 : Segment system t0 t1 t2 320 32 row320 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row352 : List Row := blockRows% "26/29/29/30/28/28/31/29/28/30/31/33/29/28/32/29/25/27/28/29/27/29/29/29/27/30/29/33/29/29/31/32"
theorem leaf352 : Segment system t0 t1 t2 352 32 row352 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row384 : List Row := blockRows% "32/31/31/30/30/29/29/28/30/32/30/30/31/30/30/29/31/33/32/31/33/31/30/29/32/34/31/32/35/34/31/32"
theorem leaf384 : Segment system t0 t1 t2 384 32 row384 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row416 : List Row := blockRows% "31/34/34/33/33/30/32/30/29/30/31/30/30/29/31/28/30/32/32/34/32/33/34/33/30/32/30/34/33/34/34/33"
theorem leaf416 : Segment system t0 t1 t2 416 32 row416 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row448 : List Row := blockRows% "30/33/33/32/32/29/31/30/31/32/33/33/31/30/32/29/29/31/30/32/31/32/31/30/31/34/31/36/33/33/33/34"
theorem leaf448 : Segment system t0 t1 t2 448 32 row448 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row480 : List Row := blockRows% "29/30/32/33/30/29/32/29/28/29/31/32/28/28/30/28/28/29/31/33/30/29/32/32/29/30/30/33/29/30/31/31"
theorem leaf480 : Segment system t0 t1 t2 480 32 row480 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row512 : List Row := blockRows% "29/28/28/27/27/26/26/25/28/30/27/27/29/28/27/27/28/30/28|288|296,450|424,450,962|426,450/29/30/29/28|424,450/28/29/32/28|296|424/29/32/31/28|424/29"
theorem leaf512 : Segment system t0 t1 t2 512 32 row512 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row544 : List Row := blockRows% "28/30/30/29/30/29/29/28/27/30/28/28/31/28/29/27/27/30/29/29/29/30/29/29/27/30/27|424/30/31/33/31/31"
theorem leaf544 : Segment system t0 t1 t2 544 32 row544 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row576 : List Row := blockRows% "27/30/30/29/29/28/28/27/29/32/31/31/31/29/30/28/26/29/28/29/28/31/28/29/28/31/28/33/30/32/30/32"
theorem leaf576 : Segment system t0 t1 t2 576 32 row576 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row608 : List Row := blockRows% "26/29/29/30/28/28/31/28/27/28/29/31/27/28/30/27/25/28/28/29/27/29/29/29/27/29/27/31/28/29/30/30"
theorem leaf608 : Segment system t0 t1 t2 608 32 row608 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row640 : List Row := blockRows% "32/31/30/30/30/29/29/28/28/30/28/28/29/28/28/27/31/34/31/32/33/32/31/31/30/33/29/30/33/33/29/30"
theorem leaf640 : Segment system t0 t1 t2 640 32 row640 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row672 : List Row := blockRows% "31/33/32/31/32/29/30/28/27/28/29/28/28/27/29/26/30/33/30/34/32/33/33/32/28/30/28/32/31/32/32/31"
theorem leaf672 : Segment system t0 t1 t2 672 32 row672 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row704 : List Row := blockRows% "30/33/33/32/32/30/31/29/29/30/31/31/29/28/30/27/29/32/31/34/31/33/31/32/30/33/29/34/32/32/31/32"
theorem leaf704 : Segment system t0 t1 t2 704 32 row704 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row736 : List Row := blockRows% "28/29/30/31/28/28/30/27/26/27/29/30/26/26/28/26/28/30/29/32/29/30/31/30/27/28/28/31/27/28/29/29"
theorem leaf736 : Segment system t0 t1 t2 736 32 row736 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row768 : List Row := blockRows% "28/28/28/27/27/26/26/25/26/27/26/25/28/25/26/24/28/30/29/29/30/29/29/28/27/30/28|424/28/31/30/28/28"
theorem leaf768 : Segment system t0 t1 t2 768 32 row768 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row800 : List Row := blockRows% "28/30/28/28/30/28/29/27/25/26/26/25/27/24/26/23/27/30/28/29/29/29/30/29/25/27/26/28/28/29/30/28"
theorem leaf800 : Segment system t0 t1 t2 800 32 row800 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row832 : List Row := blockRows% "27/30/30/29/29/27/28/27/28/29/29/28/30/27/29/26/26/29/29/30/28/30/30/30/28/30/28/32/30/30/32/31"
theorem leaf832 : Segment system t0 t1 t2 832 32 row832 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row864 : List Row := blockRows% "26/28/29/29/27/26|295,480/29/26/23/24/26/27/25/26/28/25/25/28/28/29/27/27/30/28/24/25/26/28/26/27/29/28"
theorem leaf864 : Segment system t0 t1 t2 864 32 row864 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row896 : List Row := blockRows% "30/30/29/28/30/28/29/27/26/26/27/25/27/24/26/23/31/34/31/31/33/32/31/31/28/31/29/29/31/29/29/28"
theorem leaf896 : Segment system t0 t1 t2 896 32 row896 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row928 : List Row := blockRows% "28/29/30/28/30/27/29/26/24/25/27/24/26/23/25/22/28/30/29/32/31/31/33/30/25/26/27/29/27/28/30/27"
theorem leaf928 : Segment system t0 t1 t2 928 32 row928 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row960 : List Row := blockRows% "30/32/33/31/30/28/30/27/27/28/29/27/27/26/28/25/29/32/31/35/31/31/33/31/28/29/29/32/30/30/31/30"
theorem leaf960 : Segment system t0 t1 t2 960 32 row960 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row992 : List Row := blockRows% "26/27/29/29/26/26/28/25/22/23/25/26/24/24/26/24/27/28/29/31/27/28/30/28/23/24/26/27/25/26/28/27"
theorem leaf992 : Segment system t0 t1 t2 992 32 row992 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1024 : List Row := blockRows% "28/27/27/26/28/26/25/24/31/31/30/30/32/29/29/28/25/26/24|424/24/27/26/24/23/28/29/27/28/31/30/28/27"
theorem leaf1024 : Segment system t0 t1 t2 1024 32 row1024 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1056 : List Row := blockRows% "29/28/30/29/31/28/30/28/32/32/31/32/33/30/33/30/26/26/25/26/28/28/27/26/30/31/30/31/32/32/32/31"
theorem leaf1056 : Segment system t0 t1 t2 1056 32 row1056 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1088 : List Row := blockRows% "28/29/29/28/30/27/27/26/31/33/33/32/33/29/31/29/23/26/24/25/25/27/26/25/27/30/28/30/29/31/30/29"
theorem leaf1088 : Segment system t0 t1 t2 1088 32 row1088 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1120 : List Row := blockRows% "28/28/30/30/29/28/31/28/30/30/33/33/30/30/33/30/24/26/25/26/26/26/27/25/28/29/29/31/29/29/31/29"
theorem leaf1120 : Segment system t0 t1 t2 1120 32 row1120 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1152 : List Row := blockRows% "30/29/28/27/29/26/26/25/32/32/30/30/32/28/30/28/26/29/27/26/28/27/25/24/29/32/29/30/32/30/29/28"
theorem leaf1152 : Segment system t0 t1 t2 1152 32 row1152 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1184 : List Row := blockRows% "31/31/33/31/32/27/31/28/30/31/32/31/31/28/30/27/27/29/28/29/29/29/30/28/30/31/30/32/32/32/33/30"
theorem leaf1184 : Segment system t0 t1 t2 1184 32 row1184 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1216 : List Row := blockRows% "29/30/30/29/30/26/28/26/32/32/34/32/32/28/30/28/24/27/25/28/26/27/27/26/28/30/29/32/29/30/31/29"
theorem leaf1216 : Segment system t0 t1 t2 1216 32 row1216 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1248 : List Row := blockRows% "28/27/31/31/28/27/31/28/27/28/30/31/27/28/30/27/25/26/26/28/26/26/28/26/28/28/29/30/28/28/29/29"
theorem leaf1248 : Segment system t0 t1 t2 1248 32 row1248 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1280 : List Row := blockRows% "30/29/30/29/30/27/29/27/31/31/31/31/32/29/31/30/28/28/27/27/31/29/28/27/30/30/29/30/34/32/32/31"
theorem leaf1280 : Segment system t0 t1 t2 1280 32 row1280 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1312 : List Row := blockRows% "31/30/31/30/32/28/31/29/31/30/31/31/33/30/33/30/29/28/29/28/31/29/29/28/32/31/32/32/34/32/34/33"
theorem leaf1312 : Segment system t0 t1 t2 1312 32 row1312 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1344 : List Row := blockRows% "30/31/32/31/32/27/31/28/32/33/34/33/33/29/33/30/27/29/28/27/29/29/28/27/31/32/32/33/32/32/33/32"
theorem leaf1344 : Segment system t0 t1 t2 1344 32 row1344 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1376 : List Row := blockRows% "29/28|295,480/32/30/29/27|293,480|295,480,481|423,480/31/28/30/30/33/32/30/29/33/30/27/27|295/29/28/28/27/29/27/30/29/32/33/30/29/33/31"
theorem leaf1376 : Segment system t0 t1 t2 1376 32 row1376 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1408 : List Row := blockRows% "32/30/32/30/31/26/30/27/31/30/32/30/32/28/30/28/30/31/30/30/32/29/29/28/31/33/31/31/35/31/32/29"
theorem leaf1408 : Segment system t0 t1 t2 1408 32 row1408 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1440 : List Row := blockRows% "32/31/34/32/32/27/32/28/28/29/31/29/30/28/30/27/30/30/32/32/31/30/33/30/30/30/31/32/32/32/33/30"
theorem leaf1440 : Segment system t0 t1 t2 1440 32 row1440 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1472 : List Row := blockRows% "31/30/34/31/31/26/31/27/31/32/34/32/32/28/31/28/28/29/29/31/29/29/31/28/31/31/32/33/31/31/34/31"
theorem leaf1472 : Segment system t0 t1 t2 1472 32 row1472 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1504 : List Row := blockRows% "28/27/32/32/28/27|599/32/28/27/28/30/31/27/28|599/30/27/27/26/30/30/27/26/31/28/28/28/29/30/28/28/31/31"
theorem leaf1504 : Segment system t0 t1 t2 1504 32 row1504 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1536 : List Row := blockRows% "31/30/30/29/30/29/29/28/31/31/30/30/32/30/30/29/30/30/29/29/32/31/29/29/32/32/30/31/34/33/31/32"
theorem leaf1536 : Segment system t0 t1 t2 1536 32 row1536 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1568 : List Row := blockRows% "31/31/31/30/32/29|295,480/31/30/29/28/29/29/31/29/31/28/30/30/30/30/32/30/30/30/30/31/30/31/33/32/33/31"
theorem leaf1568 : Segment system t0 t1 t2 1568 32 row1568 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1600 : List Row := blockRows% "30/32/32/31/32/29/31/30/32/33/34/33/33/30/32/29/29/31/29/29/31/31/29/29/31/34/31/34/33/33/33/33"
theorem leaf1600 : Segment system t0 t1 t2 1600 32 row1600 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1632 : List Row := blockRows% "29/29/32/30/30/27|294,480|295,480|303,480|359,480/31/28/28/29/31/30/28/29/31/28/28/29/30/30/30/28/30/29/29/30/30/31/29/30/31/29"
theorem leaf1632 : Segment system t0 t1 t2 1632 32 row1632 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1664 : List Row := blockRows% "33/32/32/32/32/28/31/28/29/29/30/28/30/27/28/26/32/33/31/32/34/31/31/30/31/33/31/31/34/32/31/29"
theorem leaf1664 : Segment system t0 t1 t2 1664 32 row1664 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1696 : List Row := blockRows% "31/31/32/31/31/28/30/27/26/27/29/27/28/26/28/25/32/32/32/32/32/32/34/31/28/29/30/31/30/31/32/30"
theorem leaf1696 : Segment system t0 t1 t2 1696 32 row1696 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1728 : List Row := blockRows% "32/32/35/32/32/28/31/28/29/30/32/30/30/27/29/26/30/31/31/33/31/31/33/30/30/32/31/33/31/32/33/31"
theorem leaf1728 : Segment system t0 t1 t2 1728 32 row1728 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1760 : List Row := blockRows% "27/28/30/31/27|598|599/28|599/30/27/25/26/28/29/25/26|598|599/28/25/28/28/31/31/28/28/31/29/26/27/28/30/26/27/29/30"
theorem leaf1760 : Segment system t0 t1 t2 1760 32 row1760 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1792 : List Row := blockRows% "29/30/30/29/30/28/29/28/29/28/28/27/29/26/28/25/30/30/30/30/32/31/31/30/30/31/29/30/34/31/31/30"
theorem leaf1792 : Segment system t0 t1 t2 1792 32 row1792 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1824 : List Row := blockRows% "30/29|295,480/29/29/30/27|293,480|295,416,480/31/28/26/26|295/27/25/28/25|293|295/27/24/30/30/29/30/31/28/31/29/27/28/28/28/29/29/31/28"
theorem leaf1824 : Segment system t0 t1 t2 1824 32 row1824 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1856 : List Row := blockRows% "30/30/32/31/31/28/31/29/29/30/32/29/31/28/30/27/29/31/31/31/31/29/31/30/30/31/31/33/32/31/34/32"
theorem leaf1856 : Segment system t0 t1 t2 1856 32 row1856 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1888 : List Row := blockRows% "28/27|294,480|295,352,480/31/28/28/25|293,480|294,480,992|295,224,352,353,360,416,420,448,480,481,484,485,488,864,992,996|301,480|303,480,488|311,480|359,416,480,481,488|375|422,480|423,480,484|431,480|439|599|631|807,480|815|855|871|887/29/26|295,480/24/25|295|807/27/27/26/27|293,480|295,416,480,488,992/29/26/28/28/31/29/29/26|295,480/30/27/25/26/28/29/27/28/30/27"
theorem leaf1888 : Segment system t0 t1 t2 1888 32 row1888 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1920 : List Row := blockRows% "32/30/32/30/32/28/31/28/27/27/29/26/28/25/27/24/34/33/33/33/36/31/34/31/30/31/32/31/32/30/31/29"
theorem leaf1920 : Segment system t0 t1 t2 1920 32 row1920 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1952 : List Row := blockRows% "29/29/31/29/31/28/30/27/24/25/27/25/26/24|293|597|599|789|853|855/26/23/30/30/32/31/32/31/33/30/26/27/29/29/28/29/31/28"
theorem leaf1952 : Segment system t0 t1 t2 1952 32 row1952 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1984 : List Row := blockRows% "32/32/35/32/32/28/31/28/27/28/30/28/28/27/29/26/32/31/34/35/32/31/34/32/29/30/31/33/31/32/33/31"
theorem leaf1984 : Segment system t0 t1 t2 1984 32 row1984 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row2016 : List Row := blockRows% "27/28/30/29/27/27|295,480|599|631|855|887/29/26/23/24|598|599/26/27/25|599/26|293|295|533|535|597|598|599,573|631|791|807|855|887/28/25/28/28/31/30/28/28/31/28/24/25/27/28/26/27/29/28"
theorem leaf2016 : Segment system t0 t1 t2 2016 32 row2016 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
end Quadric.Five.Census.Block.Case14
