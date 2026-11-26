import Quadric.Five.Intervals
import Quadric.Five.Resources.System17

namespace Quadric.Five.Census.Block.Case17
set_option maxRecDepth 16384
set_option maxHeartbeats 24000000
set_option Elab.async false
private theorem cachedMinimum : packList system.lowFirst=413553616210164463601837521537093499071483220465327557651621840472109895007575715319368565232743748087629575503211732124316924360447625440018460771483657593980555778264135434771440063386085934253072217915216325761340652563672442882056665862239718117160782666706155992816415207326810788885220705660116908713775985268536726818040554195894666376553215400943045197873805165567823185631779661274296224146998802393354881307525752452531341663486346083535845806649958135785781347909140044790015383797094953368801119921728926408803346834431762035756599340410972385189893878334627316349381769989849799312214464585776044228745259914839674244337477175469276280007517273208323380099441365635973491710184856959949689951136833875248443285492326321307070331358981314344975066525790634161111609701368714715409839701836227685494343690679800557977764536030562936381561807515786076614509346072088132159334242277638402648334673012712709879318483057703995755716796097099419314755028092613921980196239464979759848970889074347165965023014458872426216098666333217615089286337043677493361052952604000810511278135042588990497284951321504422260003732348811954883921582463029251777085416625060391561427675240418137281036051096724615395059881794537005012074159490771642869937392581046635425986615555803836981549931184802649453198562006870588209227199013988398731606161501209673708679921618905204137090876222700811049689681880524296211110180000403620357695746579687449955456095297044708277788326764289822814884512482394017443856690922278573399932315028647171924803183592034624637659186306491560140314805355543200171032933094251019961994213564538630782387339983715065717502987191540465672371361271288633128180138995507845828064743411480905421848429917597756773376157700278885797319291818367989426898401133117532418429082655813762207535430706433426809319981954334724838324839572720750954932680138720945596303413421177079464120030229461787631146032276145601944760490456241723891309600813994289640178895321805402928272535407335571947578595034626410589974770608341879991835390568672069500859318376691457257095128730972034529538256385934655366349967850095722156851630351051291398598911929303413992500294734328471527516583514341396774291814839466333864561490219108214337480948054050891582087149843516580585142136586345229369607346991111791306819777926941379649737767956405263546578049516029877505432315444760384009677750311475326700997064097996944339495053799948119482231578148007612261855174738851460470821339721912566700414641842752558418416340155842567101858060045507446495004312402701949390214097571417552714524946321200211581389905993702639165441260553620204263338450355126956757270219120418851803134774654491002992079769012678131322382978614417562308751590170638112977769558419433519594816573721040284770526166660820861894970036339985067256236335836144497923016537476859516197277412052796489558796998525796660860430403977710263022126112684595140476159566403660997538426334374070389307399560934068817925066884018191968139329139971744288037013764443242031481013089006117195751887995897898784704491153452593475237900 := by decide +kernel
noncomputable def row0 : List Row := blockRows% "26/26/26/25/25/24/24/23/29/28/28/27/27/26/26/25/28/29/29/28/30/28/27/26/30/32/30/31/32/31/30/30"
theorem leaf0 : Segment system t0 t1 t2 0 32 row0 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row32 : List Row := blockRows% "28/30/29/29/30/29/28/28/30/32/30/31/32/31/30/30/27/30/28/29/29/32/29/29/30/33/29/30/32/32/29/30"
theorem leaf32 : Segment system t0 t1 t2 32 32 row32 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row64 : List Row := blockRows% "25/28/28/27/27/26/26/25/27/30/30/29/29/28/28/27/26/28/27/30/28/30/28/28/28/31/30/31/30/32/30/31"
theorem leaf64 : Segment system t0 t1 t2 64 32 row64 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row96 : List Row := blockRows% "26/29/28/31/28/31/28/30/28/31/30/31/30/32/30/31/25/28/26/29/27/29/27/29/28/31/29/30/29/30/29/29"
theorem leaf96 : Segment system t0 t1 t2 96 32 row96 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row128 : List Row := blockRows% "27/28/29/27/27/26/27/25/30/31/29/30/30/29/29/28/29/30/30/29/30/29/28/27/33/35/32/33/35/32/32/31"
theorem leaf128 : Segment system t0 t1 t2 128 32 row128 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row160 : List Row := blockRows% "30/32/32/31/32/31/30/29/32/34/31/32/34/31/31/30/28/31/29/32/30/32/31/30/30/32/30/33/32/33/32/30"
theorem leaf160 : Segment system t0 t1 t2 160 32 row160 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row192 : List Row := blockRows% "27/28/30/29/27/28/29/27/30/33/33/32/32/30/31/29/27/29/28/31/29/30/30/29/31/32/32/35/32/32/33/31"
theorem leaf192 : Segment system t0 t1 t2 192 32 row192 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row224 : List Row := blockRows% "29/31/30/33/31/32/31/31/30/31/31/34/30/31/31/30/26/28/27/30/27/28/29/29/28/30/29/31/28/30/29/28"
theorem leaf224 : Segment system t0 t1 t2 224 32 row224 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row256 : List Row := blockRows% "26/26/26/25/25/24/24/23/28/28/28/27/27/26/26/25/28/30/30/29/30/28/29/27/30/32/31/31/32/31/31/30"
theorem leaf256 : Segment system t0 t1 t2 256 32 row256 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row288 : List Row := blockRows% "28/30/30/29/30/29/29/28/30/32/30/30/32/31/30/30/29/31/30/31/31/33/31/31/30/33/29/31/33/31/31/31"
theorem leaf288 : Segment system t0 t1 t2 288 32 row288 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row320 : List Row := blockRows% "25/28/28/27/27/26/26/25/27/30/30/29/29/28/28/27/26/28/29/31/28/30/30/29/28/31/31/32/30/30/32/31"
theorem leaf320 : Segment system t0 t1 t2 320 32 row320 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row352 : List Row := blockRows% "26/29/29/31/28/30/30/30/28/31/30/32/30/30/32/30/27/29/28/31/29/29/29/30/29/31/29/31/29/29/30/29"
theorem leaf352 : Segment system t0 t1 t2 352 32 row352 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row384 : List Row := blockRows% "29/29/29/28/28/27/27/26/30/31/29/28/30/29/29/28/31/32/33/32/32/30/32/30/33/34/33/33/35/32/33/32"
theorem leaf384 : Segment system t0 t1 t2 384 32 row384 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row416 : List Row := blockRows% "31/34/33/33/33/32/32/31/31/33/31/31/34/31/31/30/32/33/32/35/33/33/34/33/30/32/30/32/32/33/32/31"
theorem leaf416 : Segment system t0 t1 t2 416 32 row416 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row448 : List Row := blockRows% "28/30/31/30/28/29/29/28/30/33/33/32/32/30/31/29/29/30/32/34/31/30/33/31/31/32/33/35/32/31/33/31"
theorem leaf448 : Segment system t0 t1 t2 448 32 row448 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row480 : List Row := blockRows% "29/32/32/35/31/31/33/32/30/31/31/33/30/30/31/29/29/29/31/33/29/29/31/31/28/30/29/31/29/30/29/29"
theorem leaf480 : Segment system t0 t1 t2 480 32 row480 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row512 : List Row := blockRows% "26/26/26/25/25/24/24/23/27/28/26/25/27/26/26/25/28/30/30/29/30/29/29/28/30/32/30/30/32/31/30/30"
theorem leaf512 : Segment system t0 t1 t2 512 32 row512 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row544 : List Row := blockRows% "28/30/30/29/30/29/29/28/28/30/28/28/32/30/28/28/29/32/29/32/31/33/31/32/28/31/27/29/31/31/30/29"
theorem leaf544 : Segment system t0 t1 t2 544 32 row544 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row576 : List Row := blockRows% "25/28/28/27/27/26/26/25/27/30/30/29/29/28/28/27/26/29/29/31/28/30/30/30/28/31/30/32/30/30/32/30"
theorem leaf576 : Segment system t0 t1 t2 576 32 row576 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row608 : List Row := blockRows% "26/29/29/31/28/30/30/30/28/30/28/31/29/29/30/28/27/30/29/32/29/29/29/31/27/29/27/29/28/29/28/27"
theorem leaf608 : Segment system t0 t1 t2 608 32 row608 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row640 : List Row := blockRows% "28/29/29/28/28/27/27/26/28/29/27/26/30/28/27/26/31/34/33/33/33/32/32/31/31/33/31/31/34/31/31/30"
theorem leaf640 : Segment system t0 t1 t2 640 32 row640 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row672 : List Row := blockRows% "30/33/31/31/33/31/30/29/29/31/29/29/32/29/29/28/31/34/30/35/33/34/33/33/28/30/28/30/30/31/30/29"
theorem leaf672 : Segment system t0 t1 t2 672 32 row672 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row704 : List Row := blockRows% "28/31/31/30/28/29/29/28/30/32/31/30/30/28/29/27/29/32/32/35/31/31/33/32/30/31/31/33/30/30/31/29"
theorem leaf704 : Segment system t0 t1 t2 704 32 row704 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row736 : List Row := blockRows% "29/31/30/33/30/30/31/30/28/29/29/31/28/28/29/27/29/30/30/32/29/30/29/30/26/28/27/30/27/28/27/27"
theorem leaf736 : Segment system t0 t1 t2 736 32 row736 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row768 : List Row := blockRows% "24/26/26/25/25/24/24/23/25/26/24/23/27/25/24/23/27/30/30/29/30/29/29/28/28/30/28/28/31/28/29/27"
theorem leaf768 : Segment system t0 t1 t2 768 32 row768 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row800 : List Row := blockRows% "27/30/28/28/30/29/29/28/26/28/26/26/29/26/27/25/29/31/29/32/31/31/33/32/26/27/27/27/28/29/28/27"
theorem leaf800 : Segment system t0 t1 t2 800 32 row800 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row832 : List Row := blockRows% "25/28/28/27/27/26/26/25/27/29/28/27/29/27/28/26/26/29/29/31/28/28/31/30/27/28/29/31/29/28/31/28"
theorem leaf832 : Segment system t0 t1 t2 832 32 row832 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row864 : List Row := blockRows% "26/29/29/31/28/28/31/29/25/26/27/29/27/27/29/26/27/29/29/32/28/27/30/30/24/25/26/27/26/27/28/26"
theorem leaf864 : Segment system t0 t1 t2 864 32 row864 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row896 : List Row := blockRows% "26/29/27/26/28/27/27/26/26/26/25/24/27/24/25/23/30/33/31/31/33/31/32/30/28/29/30/28/30/27/29/26"
theorem leaf896 : Segment system t0 t1 t2 896 32 row896 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row928 : List Row := blockRows% "28/31/29/29/31/29/30/28/26/27/28/26/28/25/27/24/29/30/30/33/31/32/33/31/25/26/27/28/27/28/28/27"
theorem leaf928 : Segment system t0 t1 t2 928 32 row928 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row960 : List Row := blockRows% "28/31/29/30/28/28/29/27/27/28/29/27/28/26/28/25/29/31/32/34/30/29/32/30/26/27/29/30/28/28/30/27"
theorem leaf960 : Segment system t0 t1 t2 960 32 row960 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row992 : List Row := blockRows% "28/29/30/32/28/28/30/28/24/25/27/28/26/26/28/25/27/28/29/31/27/28/29/29/23/24/25/27/25/26/27/26"
theorem leaf992 : Segment system t0 t1 t2 992 32 row992 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1024 : List Row := blockRows% "26/25/27/25/27/24/25/23/29/29/30/29/30/28/29/27/27/26/27/26/29/27/26/25/30/30/29/30/33/30/30/29"
theorem leaf1024 : Segment system t0 t1 t2 1024 32 row1024 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1056 : List Row := blockRows% "29/28/29/28/31/29/28/27/32/32/30/32/34/32/31/31/26/29/27/27/28/28/28/27/30/30/29/29/31/28/30/27"
theorem leaf1056 : Segment system t0 t1 t2 1056 32 row1056 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1088 : List Row := blockRows% "26/27/29/27/28/26/27/25/30/31/32/31/32/29/31/29/25/27/26/28/27/28/28/27/29/30/30/30/30/29/31/28"
theorem leaf1088 : Segment system t0 t1 t2 1088 32 row1088 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1120 : List Row := blockRows% "27/29/28/30/29/30/30/29/31/32/31/32/32/31/31/30/24/26/25/27/25/26/27/25/27/28/29/27/27/26/28/25"
theorem leaf1120 : Segment system t0 t1 t2 1120 32 row1120 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1152 : List Row := blockRows% "27/27/28/26/28/25/26/24/31/31/30/30/31/28/30/28/28/29/29/28/30/27/27/26/32/33/31/31/33/29/31/29"
theorem leaf1152 : Segment system t0 t1 t2 1152 32 row1152 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1184 : List Row := blockRows% "30/31/31/30/32/29/29/28/32/33/31/31/33/30/31/29/27/29/28/30/28/29/30/28/28/29/29/28/30/29/30/27"
theorem leaf1184 : Segment system t0 t1 t2 1184 32 row1184 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1216 : List Row := blockRows% "27/28/30/28/28/26/28/26/31/32/34/32/32/28/31/28/26/27/27/30/27/27/29/27/29/29/31/31/29/29/31/28"
theorem leaf1216 : Segment system t0 t1 t2 1216 32 row1216 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1248 : List Row := blockRows% "28/29/29/32/29/29/31/29/29/30/31/32/29/30/30/28/24/25/26/28/24/25/27/26/26/27/27/28/26/27/27/25"
theorem leaf1248 : Segment system t0 t1 t2 1248 32 row1248 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1280 : List Row := blockRows% "28/27/28/27/28/26/27/25/29/29/30/29/30/29/29/28/29/28/29/29/31/28/30/28/31/30/31/31/34/30/33/31"
theorem leaf1280 : Segment system t0 t1 t2 1280 32 row1280 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1312 : List Row := blockRows% "31/30/31/30/32/30/31/30/32/32/31/32/34/31/33/32/30/31/30/30/31/30/31/29/31/30/30/29/32/30/31/29"
theorem leaf1312 : Segment system t0 t1 t2 1312 32 row1312 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1344 : List Row := blockRows% "28/29/30/29/30/27/29/27/30/32/32/31/32/29/31/30/28/28/30/31/29/28/32/29/31/30/33/32/31/29/32/30"
theorem leaf1344 : Segment system t0 t1 t2 1344 32 row1344 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1376 : List Row := blockRows% "29/30/32/32/31/30/33/31/31/31/33/32/32/29/32/30/27/27/29/29/27/27/30/27/29/29/30/29/29/28/29/27"
theorem leaf1376 : Segment system t0 t1 t2 1376 32 row1376 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1408 : List Row := blockRows% "29/29/31/28/30/26/29/26/31/30/30/30/32/28/31/28/30/31/32/31/32/27/31/28/33/31/33/31/34/29/32/29"
theorem leaf1408 : Segment system t0 t1 t2 1408 32 row1408 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1440 : List Row := blockRows% "32/33/33/33/34/29/33/30/31/31/32/31/33/30/31/29/30/30/31/32/30/30/33/30/28/29/29/28/30/31/31/28"
theorem leaf1440 : Segment system t0 t1 t2 1440 32 row1440 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1472 : List Row := blockRows% "29/30/32/30/30/26/31/27/32/32/34/32/32/28/31/28/28/27/31/32/28/27/32/28/30/29/32/33/30/29/33/30"
theorem leaf1472 : Segment system t0 t1 t2 1472 32 row1472 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1504 : List Row := blockRows% "30/29/33/34/30/29/34/30/29/30/31/33/29/30/32/29/26/26/29/30/26/26/29/28/26/27/27/28/28/28/29/27"
theorem leaf1504 : Segment system t0 t1 t2 1504 32 row1504 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1536 : List Row := blockRows% "29/28/28/27/28/27/27/26/29/30/28/28/30/29/29/28/31/30/31/30/32/30/31/30/32/32/31/32/34/31/33/32"
theorem leaf1536 : Segment system t0 t1 t2 1536 32 row1536 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1568 : List Row := blockRows% "31/31/31/30/32/31/31/30/30/30/29/30/33/31/31/30/32/33/32/32/33/32/32/31/30/30/28/28/32/30/29/28"
theorem leaf1568 : Segment system t0 t1 t2 1568 32 row1568 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1600 : List Row := blockRows% "28/30/30/29/30/29/29/28/30/32/32/31/32/30/31/29/29/30/32/32/31/30/33/31/31/31/33/32/32/29/32/30"
theorem leaf1600 : Segment system t0 t1 t2 1600 32 row1600 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1632 : List Row := blockRows% "29/32/32/32/31/31/33/32/30/31/31/30/30/29/30/28/29/29/31/31/29/29/31/29/28/30/29/28/29/28/27/26"
theorem leaf1632 : Segment system t0 t1 t2 1632 32 row1632 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1664 : List Row := blockRows% "30/31/30/30/31/28/30/28/29/29/28/28/30/27/29/26/32/33/33/33/34/29/33/30/31/31/32/31/33/30/31/29"
theorem leaf1664 : Segment system t0 t1 t2 1664 32 row1664 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1696 : List Row := blockRows% "31/33/32/33/33/30/32/29/29/29/30/29/31/28/29/27/30/31/31/32/32/32/33/30/27/29/28/28/29/31/30/28"
theorem leaf1696 : Segment system t0 t1 t2 1696 32 row1696 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1728 : List Row := blockRows% "30/32/33/32/32/28/31/28/30/31/32/30/30/27/29/26/30/29/33/34/30/29/34/30/29/30/31/33/29/30/32/29"
theorem leaf1728 : Segment system t0 t1 t2 1728 32 row1728 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1760 : List Row := blockRows% "29/30/32/33/29/30/32/29/27/28/29/31/27/28/30/27/28/28/29/30/28/28/29/29/25/27/26/28/26/27/28/27"
theorem leaf1760 : Segment system t0 t1 t2 1760 32 row1760 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1792 : List Row := blockRows% "27/28/28/27/28/27/27/26/27/28/26/26/29/26/27/25/30/30/31/30/32/30/31/30/30/29/29/29/32/29/31/28"
theorem leaf1792 : Segment system t0 t1 t2 1792 32 row1792 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1824 : List Row := blockRows% "30/31/29/30/32/30/31/30/28/27/27/27/30/27/29/26/31/32/32/32/33/30/33/31/27/26/27/26/29/28/27/26"
theorem leaf1824 : Segment system t0 t1 t2 1824 32 row1824 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1856 : List Row := blockRows% "28/30/30/29/30/28/29/28/29/30/30/29/31/28/30/27/29/30/32/32/30/29/33/30/28/29/31/30/30/27/31/28"
theorem leaf1856 : Segment system t0 t1 t2 1856 32 row1856 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1888 : List Row := blockRows% "29/31/32/32/30/29/33/30/26/27/29/28/28/27/29/26/29/29/31/31/29/28/31/29/25/26/27/26/27/26/27/25"
theorem leaf1888 : Segment system t0 t1 t2 1888 32 row1888 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1920 : List Row := blockRows% "30/30/30/29/31/28/30/28/28/27/28/26/28/25/27/24/32/31/34/32/34/29/34/30/29/29/31/29/31/28/30/27"
theorem leaf1920 : Segment system t0 t1 t2 1920 32 row1920 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1952 : List Row := blockRows% "30/31/32/31/32/30/32/29/27/27/29/27/29/26/28/25/30/30/31/32/32/32/33/30/26/27/28/27/28/29/28/27"
theorem leaf1952 : Segment system t0 t1 t2 1952 32 row1952 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1984 : List Row := blockRows% "31/32/33/32/32/28/31/28/28/29/31/28/30/27/29/26/30/29/34/34/30/29/34/30/27/28/30/31/29/29/31/28"
theorem leaf1984 : Segment system t0 t1 t2 1984 32 row1984 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row2016 : List Row := blockRows% "29/30/32/33/29/30/32/29/25/26/28/29/27/27/29/26/28/28/29/30/28/28/30/30/24/25/26/27/26/27/28/26"
theorem leaf2016 : Segment system t0 t1 t2 2016 32 row2016 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
end Quadric.Five.Census.Block.Case17
