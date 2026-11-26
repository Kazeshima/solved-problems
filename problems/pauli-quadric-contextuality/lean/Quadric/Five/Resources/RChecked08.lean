import Quadric.Five.Intervals
import Quadric.Five.Resources.System08

namespace Quadric.Five.Census.Block.Case08
set_option maxRecDepth 16384
set_option maxHeartbeats 24000000
set_option Elab.async false
private theorem cachedMinimum : packList system.lowFirst=551281560090206154119861940458062418992488413149635821992139777280370367129863446171691679869130367506925097585769976002978537813218460431050969376923792299394556918339802385557299219036864910326496197369462026098342422335226106620685359073498857727392505546263924477352028881061325736650129973059202758706744017267656698268319385321766990205281235850935021903995511809597470410327742807221009489289679405557244057259174840531853845890660256552809178941683991247277735326031304838224857517753476100816834454148730349311171465156361086291602267552953732494755887605800979651571470747819401523096652984740965640436391073217951904560274459988965493120458569293213059489283618896677750641347947368797203451797820649766128460176008447613626573717349187648438105662134559922561701564657225585778427406527234934775027171413131431608364802334188364668472009293803577927518359410297312497267432438343350943427281245410589739134892404528542356412574960501408126129550281879028172772093175600455146193766280365089066110578892181131120062062482447059662237641089290467677601807612767537351836989812204686496501909618374527731929596038795753338619209951503182809607743112218280189128855105589199788157927765265272597449185456576631317401553476400962392285987536220876394438062485794537664219594788070280273281159219893034573321238861995741503661000007812745760973929919135162119395542011644369651833186744111207433969695371045662621519313592868345239434934671872990466667537800915045890923914210920132025079620932632744766577234150969121306377725929004411516936468258760821933266775939584712007803405038927556527541807004578148317738193275604830744502774765757992809775875886670733190674452992442195149809651000462473107253864810212862548608573864709393333808118496692675398912001862282761047731661944027100376130261253374918932442371706363830191428532857262904657565370144790033617966195414991026099742240608455571121997900403904093711037055321950727749828866586974267167927378416395413730273169943034246696381044082572932563748119254162784617843755630942587621566905656896733126709307517816525597173686661513508862153924189428095378584998821377177583227314733457359659217888320940675839550312163560631795285839914082869185887909411749332335273442008854352293475886733998433039535716703010450190402411368741884862417219215730876301018204625316364931398919325579309790508489617786342514347111236658682557925858754260820483460816307618546715578593879758933183428296199238452705455077176806761666526141812682392039204672158541994231114376009634911747834017340274305744849111196877339916154659504280323220787533360043566907619086541567438798616962026970112093822868663750866469100800516265109176962944218118553453410621430383839866646091648846653913530135141834605580923873659279526188470734352206174812014916405620934637165148263172438888083202834368456097662125178816234345012013488239840386085599328486570491090347671053645889690316301594087192318346318216621853137136195925264864170489798681943808689548423880393349979101795027883497292139893631319303890733022968456359315617011611273814621200 := by decide +kernel
noncomputable def row0 : List Row := blockRows% "27/27/28/29/28/29/28/29/30/29/32/32/32/33/30/29/26/27/27|424/28/28/29/29/28/27/30/30/30/29/31/29/28"
theorem leaf0 : Segment system t0 t1 t2 0 32 row0 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row32 : List Row := blockRows% "26/26/29/29/28/28/28/29/29/28/31/31/31/32/30/30/26/27/27/28/28/29/28/28/26/29/29/29/28/31/29/27"
theorem leaf32 : Segment system t0 t1 t2 32 32 row32 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row64 : List Row := blockRows% "26/27/28/29/26/29/28/28/29/31/32/33/30/32/28/29/26/27/27/28/28/29/29/28/27/30/30/30/29/31/27/28"
theorem leaf64 : Segment system t0 t1 t2 64 32 row64 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row96 : List Row := blockRows% "26/26/29/29/27/28/29/29/29/30/32/33/31/32/29/30/26/27/28/29/28/29/29/28/26/29/29/29/28/31/28/27"
theorem leaf96 : Segment system t0 t1 t2 96 32 row96 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row128 : List Row := blockRows% "27/30/29/30/27/30/27/28/27/30/30/32/29/31/27/28/28/30/30/31/30/32/28/27/28/31/30/31/29/30/26|720|728/27"
theorem leaf128 : Segment system t0 t1 t2 128 32 row128 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row160 : List Row := blockRows% "26/29/29/30/28/29/28/28/26/29/29/32/28/31/28/29/27/30/30/31/29/32/29/28/27/30/30/30/29/31/27/28"
theorem leaf160 : Segment system t0 t1 t2 160 32 row160 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row192 : List Row := blockRows% "25/28/29/30/25/28/27/27/27/30/29/30/28/29/25/26/27/30/30/31/28/30/26/27/28/31/28/29/27/28/24|728/25"
theorem leaf192 : Segment system t0 t1 t2 192 32 row192 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row224 : List Row := blockRows% "26/29/29/30/26/29/28/28/26/29/29/31/28/29/26/27/27/30/30/31/29/31/27/28/27/30/29/30/28/29/25/26"
theorem leaf224 : Segment system t0 t1 t2 224 32 row224 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row256 : List Row := blockRows% "27/27/30/30/30/29/30/29/30/29/33/31/32/32/30/29/29/28/31/30/32/31/29/28/31/30/32/30/32/31/29/28"
theorem leaf256 : Segment system t0 t1 t2 256 32 row256 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row288 : List Row := blockRows% "26/26/29/29/30/30/30/29/29/28/31/30/31/32/31/29/28/27/30/30/31/31/29/28/29/29/31/29/32/32/29/27"
theorem leaf288 : Segment system t0 t1 t2 288 32 row288 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row320 : List Row := blockRows% "28/29/32/31/28/29/29/27/30/31/32/31/31/31/28/29/30/30/31/30/32/31/29/28/31/32/31/30/30/31/27/28"
theorem leaf320 : Segment system t0 t1 t2 320 32 row320 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row352 : List Row := blockRows% "28/28/31/31/29/30/30/28/29/30/32/32/31/30/29/29/30/29/31/30/32/31/29/28/30/31/31/29/31/31/28/27"
theorem leaf352 : Segment system t0 t1 t2 352 32 row352 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row384 : List Row := blockRows% "27/30/30/30/29/31/29/28/27/30/30/30/29/30/27/28/32/31/32/31/31/32/28/27/32/33/30/31/29/30/26/27|720"
theorem leaf384 : Segment system t0 t1 t2 384 32 row384 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row416 : List Row := blockRows% "26/29/29/30/28/31/30/28/26/29/29/30/28/29/28/28/31/30/32/31/32/32/29/28/30/31/31/30/30/30/27/28"
theorem leaf416 : Segment system t0 t1 t2 416 32 row416 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row448 : List Row := blockRows% "27/30/30/30/27/29/27/26/27/30/29/30/28/28|517/25/26/31/33/30/31/29/30/26/27/31/32/28/29/27/28|512|517/24/25"
theorem leaf448 : Segment system t0 t1 t2 448 32 row448 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row480 : List Row := blockRows% "26/29/29/31/28/29/28/27/26/29/29/30/28/27|516|517|532|533/26/26/31/32/31/31/30/30/27/28/31/32/29/30/28/28|517/25/26"
theorem leaf480 : Segment system t0 t1 t2 480 32 row480 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row512 : List Row := blockRows% "25/26/28/29/28/27/28/28/28/29/32/31/30/32/30/29/28/28/29/29/30/30/28/27/31/30/32/30/32/31/29/28"
theorem leaf512 : Segment system t0 t1 t2 512 32 row512 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row544 : List Row := blockRows% "24/25/27/28/28/28/29/29/27/28/31/30/31/32/31/29/27/27/28/29/29/29/28/28/28/29/31/29/32/32/29/28"
theorem leaf544 : Segment system t0 t1 t2 544 32 row544 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row576 : List Row := blockRows% "26/28/30/30/26/27/28/27/28/31/32/31/30/31/28/29/30/30/30/29/30/30/28/27/31/32/31/30/30/31/27/28"
theorem leaf576 : Segment system t0 t1 t2 576 32 row576 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row608 : List Row := blockRows% "26/27/29/30/27/28/30/28/28/30/32/32/31/30/29/29/28/29/30/30/30/30/29/28/30/31/31/30/31/31/28/28"
theorem leaf608 : Segment system t0 t1 t2 608 32 row608 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row640 : List Row := blockRows% "25/28/30/30/27/30/29/28/27/30/30/30/29/30/27/28/30/31/32/31/31/32/28/27/32/33/30/31/29/30/26/27"
theorem leaf640 : Segment system t0 t1 t2 640 32 row640 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row672 : List Row := blockRows% "26/28/29/30/28/31/30/28/26/29/29/30/28/29/28/28/30/30/32/31/32/32/29/28/30/31/31/30/30/30/27/28"
theorem leaf672 : Segment system t0 t1 t2 672 32 row672 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row704 : List Row := blockRows% "25/28/30/30/25/28/27/26/27/30/29/30/28/28/25/26/30/33/30/31/29/30/26/27/31/32/28/29/27/28/24/25"
theorem leaf704 : Segment system t0 t1 t2 704 32 row704 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row736 : List Row := blockRows% "26/29/29/31/26|598/29/28/27|86/26/29/29/30/28/27|598/26/26/30/32/31/31/30/30/27/28/31/32/29/30/28/28/25/26"
theorem leaf736 : Segment system t0 t1 t2 736 32 row736 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row768 : List Row := blockRows% "23|288|424/24/26/27/26/27/28/25/26/28/30/27/28/28/28/25/26/27/29/29/30/29/28/27/29/30/30/28/31/30/29/27"
theorem leaf768 : Segment system t0 t1 t2 768 32 row768 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row800 : List Row := blockRows% "22/23/25/26/26/27/28/26/25/27/29/26/29/28/28/25/25/26/28/27/29/28/29/27/26/28/28/25/30/28/28/25"
theorem leaf800 : Segment system t0 t1 t2 800 32 row800 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row832 : List Row := blockRows% "24/26/28/27/26/26/28/25/26/29/30/27/28/28/28/25/28/29/30/29/30/29/28/27/30/30/31/30/30/30/27/28"
theorem leaf832 : Segment system t0 t1 t2 832 32 row832 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row864 : List Row := blockRows% "24/25/27/28/27/28/29/26/26/29/30/28/29/28/28/26/27/28/30/29/30/28/29/27/28/29/30/27/30/29/28/27"
theorem leaf864 : Segment system t0 t1 t2 864 32 row864 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row896 : List Row := blockRows% "25/28/29/26/27/27/27/24/27|528/28/28/26/27/26|528|532|917/26/24|528|720/30/31/32/29/31/30/28/27/30/29/28/28/28/27/26/26"
theorem leaf896 : Segment system t0 t1 t2 896 32 row896 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row928 : List Row := blockRows% "26/28/29/27/28/28/28/25/26/27/27/26/26/25|532|533|596/25/24|596/29/30/31/28/31/30/29/27/28/28/28/26|592/27/26/26/25"
theorem leaf928 : Segment system t0 t1 t2 928 32 row928 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row960 : List Row := blockRows% "25/28/29/26/27/27/27/24/26/27/27/26/26/25|512|516|517|528|532|533|596/25/24/30/32/30/29/29/29/26/27/29/29/28/28/27/27/24/25"
theorem leaf960 : Segment system t0 t1 t2 960 32 row960 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row992 : List Row := blockRows% "26/29/29/27/28/27|598/27/25/26/27|532/27/26/26/25|4|20|512|516|517|528|532|533|534|535|596|597|598|599/25/24|532|596|598/30/32/31/30/29/28/27/27/28/28/28/27/27/26|516|532/25/25"
theorem leaf992 : Segment system t0 t1 t2 992 32 row992 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1024 : List Row := blockRows% "24/24/25/26/26/26/27/28/27/26/29/29/30/30/31/30/23/24/24|64|296|424|425|426|427|488|490|491/25/25/26/26/25/26/27/27/27/28/28/28/25"
theorem leaf1024 : Segment system t0 t1 t2 1024 32 row1024 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1056 : List Row := blockRows% "24/23/26/26/26/25/28/28/26/25/29/28/30/29/31/29/23/24/24/25/25/26/26/25/25/26/26/26/27/28/27/24"
theorem leaf1056 : Segment system t0 t1 t2 1056 32 row1056 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1088 : List Row := blockRows% "24/24/25/26/26/26/27/28/28/28/29/30/30/30/31/30/23/24/24/25/25/26/26/25/26/28/28/27/28/28/28/25"
theorem leaf1088 : Segment system t0 t1 t2 1088 32 row1088 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1120 : List Row := blockRows% "24/23/26/26/26/25/28/28/28/27/30/30/30/29/31/29/24|618/24/25|106|618/26/26/26/27/26/25/28/28/26/27/29/27/24"
theorem leaf1120 : Segment system t0 t1 t2 1120 32 row1120 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1152 : List Row := blockRows% "27/27/28/29/29/29/28/28/30/29/32/31/32/33/30/28/26/27/27/28/28/29/29/26/27/30/29/26/29/29/27/24|720"
theorem leaf1152 : Segment system t0 t1 t2 1152 32 row1152 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1184 : List Row := blockRows% "27/26/29/29/29/28/29/29/29/28/30/29/31/32/31/28/26/27/27/27/28/29/28/25/26/29/28/25/28/28/26/23|592"
theorem leaf1184 : Segment system t0 t1 t2 1184 32 row1184 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1216 : List Row := blockRows% "27/27/28/29/28/29/27/26/29/31/32/31/30/31/28/27/26/27/27/28/28/29/28/26/27/29/29/26/28/28/26/24"
theorem leaf1216 : Segment system t0 t1 t2 1216 32 row1216 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1248 : List Row := blockRows% "27/26/29/29/29/28/29/28/29/30/32/30/31/32/29/28/26/27/28/27/28/29/28/25/26/29/28/25/28/28/26/23|64|576|592|596|598|599"
theorem leaf1248 : Segment system t0 t1 t2 1248 32 row1248 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1280 : List Row := blockRows% "25/24/28/27/29/28/31/30/27/26/30/29/31/30/31/30/26/25/28/27/29/28/28/25/28/27/30/27/31/28/28/25|385"
theorem leaf1280 : Segment system t0 t1 t2 1280 32 row1280 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1312 : List Row := blockRows% "24/23/27/26/28/27/31/29/26/25/29/28/30/29/31/29/25/24/28/27/29/28/28/26/27/26/29/26/31/29/27/24"
theorem leaf1312 : Segment system t0 t1 t2 1312 32 row1312 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1344 : List Row := blockRows% "27/26/29/29/29/28/30/28/29/28/32/31/33/32/31/30/27/27/28/27/29/28/28/25/30/29/30/27/31/28/28/25"
theorem leaf1344 : Segment system t0 t1 t2 1344 32 row1344 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1376 : List Row := blockRows% "26/25/29/28/28/27/31/29/28/27/31/30/32/31/31/29/27/26/29/28/29/28/28/26/29/28/29/26/31/29/27/24"
theorem leaf1376 : Segment system t0 t1 t2 1376 32 row1376 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1408 : List Row := blockRows% "28/27/31/30/32/31/30/29/30/29/33/31/32/32/30/29/29/28/31/30/32/31/29/28/31/30/31/28/32/31/29/26"
theorem leaf1408 : Segment system t0 t1 t2 1408 32 row1408 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1440 : List Row := blockRows% "27/26/29/29/31/30/31/29/29/28/30/29/31/32/31/29/28/27/31/29/32/31/29/27/29/29/30/27/32/30/28/25"
theorem leaf1440 : Segment system t0 t1 t2 1440 32 row1440 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1472 : List Row := blockRows% "30/29/32/31/30/30/29/27/30/31/32/31/31/31/28/29/30/30/31/30/32/31/29/28/30/31/31/28/30/30/27/26"
theorem leaf1472 : Segment system t0 t1 t2 1472 32 row1472 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1504 : List Row := blockRows% "29/28/31/31/31/30/31/28/29/30/32/30/31/30/29/29/30/29/31/29/32/31/29/27/30/29/30/27/31/30/28/25"
theorem leaf1504 : Segment system t0 t1 t2 1504 32 row1504 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1536 : List Row := blockRows% "24/24/27/27/28/28/30/29/27/26/30/29/31/30/31/30/26/25/28/27/29/28/27/25/28/27/30/27/31/28/28/25"
theorem leaf1536 : Segment system t0 t1 t2 1536 32 row1536 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1568 : List Row := blockRows% "23/23/26|114/26/27/27/30/29/26/25/29/28/30/29/31/29/25/24/28/27/29/28/28/26/27/26/30/28/31/29/28/26"
theorem leaf1568 : Segment system t0 t1 t2 1568 32 row1568 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1600 : List Row := blockRows% "26/26/29/29/28/28/30/28/29/28/32/31/33/32/31/30/27/27/28/27/29/28/27/25/30/29/30/27/31/28/28/25"
theorem leaf1600 : Segment system t0 t1 t2 1600 32 row1600 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1632 : List Row := blockRows% "25|106|598|618/25/28/28/27/27/30/29/28/27/31/30/32/31/31/29/27|618/26/29|106|618/28/29/28/28/26/29/28/30/28/31/29/28/26"
theorem leaf1632 : Segment system t0 t1 t2 1632 32 row1632 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1664 : List Row := blockRows% "27/27/30/30/30/31/30/29/30/29/33/31/32/32/30/29/29/28/31/30/32/31/29/28/31/30/32/30/32/31/29/28"
theorem leaf1664 : Segment system t0 t1 t2 1664 32 row1664 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1696 : List Row := blockRows% "26/26/29/29/30/30/31/29/29/28/31/30/31/32/31/29/28/27/31/30/32/31/29/28/29/29/31/29/32/32/29/27"
theorem leaf1696 : Segment system t0 t1 t2 1696 32 row1696 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1728 : List Row := blockRows% "28/29/32/31/28/30/29/27/30/31/32/31/31/31/28/29/30/30/31/30/32/31/29/28/30/31/31/30/30/31/27/28"
theorem leaf1728 : Segment system t0 t1 t2 1728 32 row1728 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1760 : List Row := blockRows% "28/28/31/31/29/30/31/28|86|598/29/30/32/32/31/30/29/29/30/29/31/30/32/31/29/28/30/31/31/29/31/31/28/27"
theorem leaf1760 : Segment system t0 t1 t2 1760 32 row1760 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1792 : List Row := blockRows% "24/24/27/27/28/28/29/26/27/26/30/28/31/29/29/26/26/25/29/27/30/28/27/25/28/27/29/27/31/28/28/25"
theorem leaf1792 : Segment system t0 t1 t2 1792 32 row1792 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1824 : List Row := blockRows% "23/23|295|807/26/26/27/27/30/27/26/25/28/25/30/28/28/25/25/24/28/26/29/27/28/26/27/26/27/24|592/30/27/27/24"
theorem leaf1824 : Segment system t0 t1 t2 1824 32 row1824 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1856 : List Row := blockRows% "26/26/29/28/30/27/29/26/29/28/31/28/32/29/29/26/28/27/29/27/30/28/27/25/30/28/30/27/31/28/28/25"
theorem leaf1856 : Segment system t0 t1 t2 1856 32 row1856 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1888 : List Row := blockRows% "25/25/28/28/29/28/30/27/28/27/30/27/32/30/30/27/27/26/30/28/30/27/28/26/29/28/29/26/31/28/28/26"
theorem leaf1888 : Segment system t0 t1 t2 1888 32 row1888 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1920 : List Row := blockRows% "27/27/30/27/30/28/28/25/30/29/30/27/30/28/28/25/29/28/32/30/33/31/29/28/31/29/30/28/31/30/29/27"
theorem leaf1920 : Segment system t0 t1 t2 1920 32 row1920 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1952 : List Row := blockRows% "26/26/29/28/30/29/29/26/29/28/29/26/29/28/28/25/28/27/30/27/32/30/29/27/29/28/28|592/25|528|592|596/30/28/28/25|592"
theorem leaf1952 : Segment system t0 t1 t2 1952 32 row1952 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1984 : List Row := blockRows% "28/29/30/27/30/28/28/25/29/30/30/27/29/28/28/25/31/29/32/30/32/31/29/28/30/29/31/30/30/30/27/28"
theorem leaf1984 : Segment system t0 t1 t2 1984 32 row1984 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row2016 : List Row := blockRows% "28/28/31/28/31/29/29/26/29/30/30/28/29/28|598|599/28/26|598/30/29/31/29/32/30/29/27/29/29/30/27/30/29/28/27"
theorem leaf2016 : Segment system t0 t1 t2 2016 32 row2016 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
end Quadric.Five.Census.Block.Case08
