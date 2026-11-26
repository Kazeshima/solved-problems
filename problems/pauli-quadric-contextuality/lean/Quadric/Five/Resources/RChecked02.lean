import Quadric.Five.Intervals
import Quadric.Five.Resources.System02

namespace Quadric.Five.Census.Block.Case02
set_option maxRecDepth 16384
set_option maxHeartbeats 24000000
set_option Elab.async false
private theorem cachedMinimum : packList system.lowFirst=516891595094058149762947798710341666228239385821903391597756694232841056758934815038512850342793706446507804998915857689149793509693293130326675306097791562177785000401115981027600936882716588357787263941615815491730482732129831138836768354224586274995517608915550020389320177365836142015641617730170534704466359468599967994890673855543688645852389000180247794490969532140383274657847570041462909143879806124074104974958834553534687863305977678515796230050880630138250201174861390098136213625897421162472936427292864848717007884403751671700879665066126562280892726778836355447099534141408027107139799155702634478024262718048307654896504171750750563113641868600491203700936776422448820893811289193606084605718243124235188944958297541632971131317550742256525708426336549298555690619809592234880743680043004709601575457533215828975107591878518388968620219026094785297048480595750457068121458958122490198774142944375408163065273746239665355642754860756160251889286451762820586313821151466609006776189053493199954628594355689461897302863141067374534051917069647043624743180561595221594011323011961724579573772048433246854647200045050522567260858932508633148623545449362748488175288181607008305797606104645578732463215062935137974053502310597738699596193059358951223102042018766240455857008490331615467549920434597083119506348863502410219704602635540086982178772782205675176928914966556213245876710092107915328519615415028858019152906047302900976229010910374466144771695896793007733393727896916850451072298622724771218156692237978326432206619679867185107895482532480572795842149298091758075553194828047780304823748682638571198105596578219938748071327823083894536812158399893581182283587489029919777701603356616323237511817990949848586755692333648038701230083285669112034074408344591094166187381006397415808577737657139181090744659661466625630744865369125086554934890700741499229089293395483770818648747224035432527431179591861303136621066811606682385383148476843207045104495342372698532049636705221893732539064585173006139576679344986335838589588371597223828399012942987227802781325945259776243807755242706057978041740579943892218433458976991119106109892456104346423454561940713625385676405925062554852358391440525751195219059565440516688765524327620685367511630877982780176726029204298288167077392965387304861722924360198042942673564436291829812655282062264923115843523363344883170353205247573789559458486449755890662508941147779877735544468817412346744841073807911859385462660260311410058770988656442102772234743222633700283858657553452541167201232848421200891667259260649532152523727306364600306689430844420852640409017367458949834236915579011376844942484690244724613509875165294401550864348600177183983659943739171350220012810055923019905633409731844143592842105219930109414078460722234907729398547933130606018178233347869927220777924569182118961606143571494814312886157440863896404174293516391825094345590043076889045826162217162941561470649803095546714658167192467593754817651307438083180319158659876438575968172495211634996536977582532944912967774875909112248002269542380995624975 := by decide +kernel
noncomputable def row0 : List Row := blockRows% "26/25/24|424|425|426/24/24|429/23|389,388|421|429/22|424|425|428|429/22|389,388/30/31/30/30/30/29/28/28/28|424|425/29/26|40|168|232|296,450|392|416|424,322,330,386,390,402,450,454,458,466|425,386,450,458|426,450|428|429|440|488,386,450|490|936/27/28/28/25|424,450|425,450|429/25/29/32/30|424,450,458/31/31/32/30/29"
theorem leaf0 : Segment system t0 t1 t2 0 32 row0 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row32 : List Row := blockRows% "27/27/27/26/27/26/26/25/29/32/31/32/31/32/32/31/28/30/28/29/30/30/28/29/30/32/30/32/32/33/32/32"
theorem leaf32 : Segment system t0 t1 t2 32 32 row32 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row64 : List Row := blockRows% "26/27/26/26/26/25/24/24/28/31/30/32/30/31/30/30/26/30/27/28/28/30/27/27/27/30/28/31/29/31/29/30"
theorem leaf64 : Segment system t0 t1 t2 64 32 row64 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row96 : List Row := blockRows% "25/28/28/28/27/28/28/27/27/30/30/33/29/31/31/33/26/29/28/29/28/30/28/29/28/29/29/32/29/29/30/31"
theorem leaf96 : Segment system t0 t1 t2 96 32 row96 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row128 : List Row := blockRows% "28/28/27/27/27/26/25/25/31/33/30/31/32/31/30/29/30/31/29/28/30/29/27/26/30/33/31/32/32/32/31/30"
theorem leaf128 : Segment system t0 t1 t2 128 32 row128 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row160 : List Row := blockRows% "29/31/31/30/30/29/29/28/31/34/32/33/33/32/33/31/31/33/32/33/33/32/32/31/30/31/30/32/32/32/33/31"
theorem leaf160 : Segment system t0 t1 t2 160 32 row160 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row192 : List Row := blockRows% "28/30/29/29/29/28/27/27/31/33/32/33/32/32/32/31/28/31/29/30/30/30/29/28/28/30/29/32/29/29/31/30"
theorem leaf192 : Segment system t0 t1 t2 192 32 row192 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row224 : List Row := blockRows% "28/31/31/32/30/30/31/29/29/30/31/33/29/30/32/31/29/30/30/33/30/30/31/31/28/28/29/30/28/28/29/29"
theorem leaf224 : Segment system t0 t1 t2 224 32 row224 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row256 : List Row := blockRows% "26/25/25/24/24|389,388|421,388|425|429/23|261,388|293|389,384,388,389,420|391,388|397|405,388|417|421,384,388|423,388|429|901/23/22|389,388,389|405,388|421,388|429/29/31/30/30/30/29|389,388,389/29/28/29|425/29/28|424,450|425,450/28/29/28/27/27/29|424|425|937,346,347/32/30|424|425/31/33/33/32/31"
theorem leaf256 : Segment system t0 t1 t2 256 32 row256 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row288 : List Row := blockRows% "27/27/27/26/27/26/26/25/29/32/30/31/31/32/32/31/28/30/30/29/30/30/30/29/30/32/30/34/32/32/34/33"
theorem leaf288 : Segment system t0 t1 t2 288 32 row288 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row320 : List Row := blockRows% "26/27/27/26/26|429/25|261,388|293|295|389,388,389,420|391,388|397|421,388|423|429/25/24/28/31/31/32/30/31/31/30/27/30/29/30/29/30/29/29/29/31/30/33/31/31/31/31"
theorem leaf320 : Segment system t0 t1 t2 320 32 row320 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row352 : List Row := blockRows% "25/28/28/28/27/28/28/27/27/30/30/33/29/29/32/31/26/29/29/30/28/28/30/29/28/29/30/33/29/28/31/31"
theorem leaf352 : Segment system t0 t1 t2 352 32 row352 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row384 : List Row := blockRows% "29/28/28/27/27/26/26/25/31/33/31/31/33/32/31/31/32/33/32/32/32/31/30/30/32/34/32/33/34/33/34/31"
theorem leaf384 : Segment system t0 t1 t2 384 32 row384 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row416 : List Row := blockRows% "30/31/31/30/30/29/29/28/30/32/31/32/33/32/33/31/31/34/33/34/33/32/34/32/30/30/31/32/32/32/33/32"
theorem leaf416 : Segment system t0 t1 t2 416 32 row416 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row448 : List Row := blockRows% "29/30/30/29/29/28/28/27/31/34/33/35/33/32/33/32/30/33/32/34/32/31/32/31/31/31/32/33/31/31|909,493,495/32/32"
theorem leaf448 : Segment system t0 t1 t2 448 32 row448 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row480 : List Row := blockRows% "28/31/31/32/30/30/31/29/29/30/31/33/29/29/31/30/29/30/32/34/30/29/32/31/28/28/29/30/28/28|517,105|525,105|909/30/30"
theorem leaf480 : Segment system t0 t1 t2 480 32 row480 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row512 : List Row := blockRows% "26|294|302|424/25/25|114|122|242|250,918|290|296|424|426|430|440|442|490|498,918|506,918/24/24/23/23|114|242|424|498/22/29/31/28/28/30/29/28/28/29/29/28|40|168|296,450|424,386,450,458,466|426,450|488/28/29/28/27/27/30/34/29|424/32/33/34/31/32"
theorem leaf512 : Segment system t0 t1 t2 512 32 row512 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row544 : List Row := blockRows% "27/27/27|114,528,784|118|122/26/27/26/26/25/27/30/28/29/31/31/30/29/28/30/30/29/30/30/30/29/28/30/28/32/31/32/32/31"
theorem leaf544 : Segment system t0 t1 t2 544 32 row544 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row576 : List Row := blockRows% "26|46,328|302,328/27/27/26/26/25/25/24/28/31/30/32/30/31/31/30/27/30/29/30/29/30/29/29/29/32/29/34/31/31/31/32"
theorem leaf576 : Segment system t0 t1 t2 576 32 row576 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row608 : List Row := blockRows% "25|38,328,840|42|44,328|46,328,344,360,456,840,856,872|102|106|110,328,840|114|118|294,328|302,328,456|558,328|638/28/28/28/27|38,328|46,328/28/28/27/27/29/28/31/28/29/30/29/26|42|44,328|46,328,360,840|106|302,328|558,328/29/29/30/28/28/30/29/27/28/28/31/27/28/29/29"
theorem leaf608 : Segment system t0 t1 t2 608 32 row608 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row640 : List Row := blockRows% "29/28/27/27/27/26/26/25/29/32/29/29/31/31/29/29/32/33/30/31/32/31/30/30/31/34/30/33/34/34/32/31"
theorem leaf640 : Segment system t0 t1 t2 640 32 row640 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row672 : List Row := blockRows% "29/31/29/28/30/28/27/26/28/30/29/30/31/30/31/29/31/33/31/33/32/31/32/30/28/29/29/32/30/31/32/31"
theorem leaf672 : Segment system t0 t1 t2 672 32 row672 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row704 : List Row := blockRows% "29/30/30/29/29/28/28/27/31/33/31/33/31/30/31/30/30/33/32/34/32/32/32/31/30/32/30/33/31/31/30/31"
theorem leaf704 : Segment system t0 t1 t2 704 32 row704 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row736 : List Row := blockRows% "28/30/29/30/29/28/29/27/27/28/29/31/27/27/29/28/28/29/30/32/28/29/30/29/26|552,632,888,890/27/28/30/26/27/28/28"
theorem leaf736 : Segment system t0 t1 t2 736 32 row736 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row768 : List Row := blockRows% "25/25/25/24/24/23|421/23/22/27/29/27/26/30/28/27/26/28/29/28/28/29/28/28/27/29/31/29/31/32/31/31/30"
theorem leaf768 : Segment system t0 t1 t2 768 32 row768 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row800 : List Row := blockRows% "26/27/25/25/27/26/26/25/25/27/26/27/28/27/28/26/28/30/28/29/30/28/30/29/25/26/27/29/27/28/30/29"
theorem leaf800 : Segment system t0 t1 t2 800 32 row800 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row832 : List Row := blockRows% "26/27/27/26/26/25/25/24/28/30/29/30/30/30/31/29/27/30/30/30/29/29/30/29/28/29/29/32/30/29/32/31"
theorem leaf832 : Segment system t0 t1 t2 832 32 row832 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row864 : List Row := blockRows% "25|38,328|46,328|294|302,328/28/28/28/27/27|294,480|295,480,488/28/26/24/25/26/28/26/27/29/27/26/28/29/29/27/26/30/27/23|40,888|552,856,888,890|554,888|556,888|557|558|813/24|813/26/27/25/26/28/27"
theorem leaf864 : Segment system t0 t1 t2 864 32 row864 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row896 : List Row := blockRows% "27/28/26/25/27/26/26/25/27/29/28/27/29/27/28/26/31/32/30/30/32/30/30/29/29/30/30/31/31/30/31/29"
theorem leaf896 : Segment system t0 t1 t2 896 32 row896 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row928 : List Row := blockRows% "27/28/27/26/29/26/27/25/25/26/27/27/27/26/28/25/28/29/30/30/30/29/31/28/24/25/27/28/26/27/29/28"
theorem leaf928 : Segment system t0 t1 t2 928 32 row928 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row960 : List Row := blockRows% "29/30/30/29/29/27/28/26/28/29/30/30/29/28/30/28/30/32/32/33/31/30/32/29/27|552,888,890/28/29/31/29/29/30/30"
theorem leaf960 : Segment system t0 t1 t2 960 32 row960 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row992 : List Row := blockRows% "27/28/29/29/27/26/28/25/23/24/26/27/25/25/27/26/26/27/29/30/26/27/29/27/22|40,888|44|520|544|552,632,634,856,872,888,890|553|554,888|556,632,872,888|557|558,888|568,632,888|616|808|812/23|552,888|556,888|557|813/25/26/24/25/27/26"
theorem leaf992 : Segment system t0 t1 t2 992 32 row992 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1024 : List Row := blockRows% "26/26/26/25/27/25/24/23|471,133,135/30/30/29/29/31/29/28/27/27/27/26/25/28/27/25/24/28/30/28/29/30/30/29/28"
theorem leaf1024 : Segment system t0 t1 t2 1024 32 row1024 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1056 : List Row := blockRows% "27/27/28/27/29/28/28/27/31/31/32/32/33/31/33/31/29/28/28/28/31/29/29/28/29/30/30/30/30/29/31/28"
theorem leaf1056 : Segment system t0 t1 t2 1056 32 row1056 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1088 : List Row := blockRows% "28/28/28/27/29/27/26/25/29/31/30/31/31/30/30/29/26/29/27/27/28/28/27/26/26/28/27/29/27/28/29/27"
theorem leaf1088 : Segment system t0 t1 t2 1088 32 row1088 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1120 : List Row := blockRows% "28/29/30/29/30/29/30/29/29/29/31/33/30/29/33/31/27/28/28/28/28/27/29/26/26/26/28/28/26/26/29/26"
theorem leaf1120 : Segment system t0 t1 t2 1120 32 row1120 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1152 : List Row := blockRows% "29/28/27/26/28/26/25/24/31/32/29/30/32/29/29/28/29/30/28/27/29/27/26/25/29/31/30/30/30/29/30/28"
theorem leaf1152 : Segment system t0 t1 t2 1152 32 row1152 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1184 : List Row := blockRows% "30/30/31/30/31/28/30/28/32/32/32/32/32/30/33/29/30/31/31/31/31/29/31/29/27/28/28/29/29/29/30/28"
theorem leaf1184 : Segment system t0 t1 t2 1184 32 row1184 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1216 : List Row := blockRows% "29/30/29/28/30/27/27/26/30/31/31/32/31/29/31/29/27/29/28/29/28/27/28/26/26/27/28/30/26/27/29/27"
theorem leaf1216 : Segment system t0 t1 t2 1216 32 row1216 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1248 : List Row := blockRows% "29/30/32/32/30/28/31/28|86/28/28/31/31/28/28/31/29/27/27/29/29/27/27/30/27/25/25/26/27/25/25/26/26"
theorem leaf1248 : Segment system t0 t1 t2 1248 32 row1248 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1280 : List Row := blockRows% "28/27/27/26/27/26|389,388,389|421/26/25|389,388/31/30/31/31/33/30/32/30/29/29/28/29/31/29/29/28/30/31/30/31/33/31/33/31"
theorem leaf1280 : Segment system t0 t1 t2 1280 32 row1280 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1312 : List Row := blockRows% "29/28/28/27/29/28/28/27/32/31/32/32/34/31/34/32/31/30/31/30/32/29/31/30/30/30/31/30/31/30/33/30"
theorem leaf1312 : Segment system t0 t1 t2 1312 32 row1312 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1344 : List Row := blockRows% "29/29/29/28/29/28/28/27/31/32/34/34/33/30/34/31/30/31/30/30/31/29/30/29/29/29/31/31/29/29/32/29"
theorem leaf1344 : Segment system t0 t1 t2 1344 32 row1344 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1376 : List Row := blockRows% "28/30/30/29/30/28|293,480|295,416,448,480,488|423,480/30/29/30/29/33/33/30/29/34/31/29/28/31/30/29/27/30/28/27/26/29/30/27/26/31/28"
theorem leaf1376 : Segment system t0 t1 t2 1376 32 row1376 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1408 : List Row := blockRows% "31/30/31/29/30/27/29/27/32/31/31/31/34/29/32/29/32/32/31/31/32/28/30/28/30/31/31/30/32/30/31/28"
theorem leaf1408 : Segment system t0 t1 t2 1408 32 row1408 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1440 : List Row := blockRows% "32/32/31/32/32/28/31/28/30/30/33/31/32/30/33/29/32/31/34/33/32/29/34/30/27/27/28/29/29/29/30/29"
theorem leaf1440 : Segment system t0 t1 t2 1440 32 row1440 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1472 : List Row := blockRows% "31/31/33/31/31/27/31/28/32/31/34/33/32/29|389|517/34/30/30/30/32/32/30/28/31/28/28/28/29/30/28/28|517,105|773,105|909/31/29"
theorem leaf1472 : Segment system t0 t1 t2 1472 32 row1472 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1504 : List Row := blockRows% "30/30/33/32/30/28|599/31/28/28/28/31/31/28/28|5,105|261|517,105,109,617|519,105|533|535|581|597|599|773,105/31/29/28/27/32/31/28/27/32/29/25/25|517,105|525,105/26/27/26/25|5,105|261|293|389|513|517,105,109,121,233,617,621,633|519,105|525,105,617|533|549|557|581,105,617|583|597|599|773,105,233|781,105|813|901|909/28/28"
theorem leaf1504 : Segment system t0 t1 t2 1504 32 row1504 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1536 : List Row := blockRows% "28/27/27|114,528,530/26/27/26/26/25/32/32/31/31/33/32/31/31/31/30/29/29/31/30/29/29/32/33/32/33/35/33/34/31"
theorem leaf1536 : Segment system t0 t1 t2 1536 32 row1536 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1568 : List Row := blockRows% "29/28/28|98,528,784|114,512,528,530,532,560,656,658,784,786,912|118,512,528,532,784|122|242|370|626,528/27|86|114,528|118,528/29/28/28|114|118/27|86|114|118/30/31/30/31/33/32/33/31/31/31/31/30/32/29/31/30/30/30/31/30/32/31/32/30"
theorem leaf1568 : Segment system t0 t1 t2 1568 32 row1568 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1600 : List Row := blockRows% "29/29/29/28/29/28/28/27/31/34/33/34/33/32/34/32/30/32/30/31/32/30/30/30/31/31/32/33/31/31/33/31"
theorem leaf1600 : Segment system t0 t1 t2 1600 32 row1600 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1632 : List Row := blockRows% "28|38,328|46,328|102|118/30/30|114|118/29/30/28|294,480|295,480/30/29|86|118/29/30/31/31/29/30/32/29/29/29/31/30/30/27/30/28/28/28/29/30/28/28/30/28"
theorem leaf1632 : Segment system t0 t1 t2 1632 32 row1632 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1664 : List Row := blockRows% "30/31/29/30/30/28/29/27/31/31/31/31/33/30/31/29/34/34/32/32/34/30/32/30/30/31/31/30/32/31/31/28"
theorem leaf1664 : Segment system t0 t1 t2 1664 32 row1664 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1696 : List Row := blockRows% "30/30/29|114,528,530,532,560|118,528|626,528/30/30/27/29|114/26|82|86,644,676,677,692|114|118,676|214,676|598/28/29/31/30/30/29/31/28/31/31/32/32/31/30/32/29/27/27/28/29/29/29/30/29"
theorem leaf1696 : Segment system t0 t1 t2 1696 32 row1696 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1728 : List Row := blockRows% "31/32/33/31/31/28/30/27/31/32/33/33/31/30/32/29/32/32/34/34/32/30/32/30/28/29/29/30/30/30/31/29"
theorem leaf1728 : Segment system t0 t1 t2 1728 32 row1728 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1760 : List Row := blockRows% "28|118|630/29/31|114/30/28|86|118|598/27|38|70,676|86,548,676,677|87|102|118,676|598|599|630/29|86,676|114|118,676/26|70,676|82|86,548,549,644,672,676,677,692|87|102|114|118,672,676,692|214,676|598|599|630/26/27/29/30/26/27|86|598|599/29/28|86,676,677|598/27/28/30/31/27/28/30/29/25/25/26|634,634,635/27/25/25/28/28"
theorem leaf1760 : Segment system t0 t1 t2 1760 32 row1760 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1792 : List Row := blockRows% "26/27/27/26/27/26/26/25/30/31/29/29/32/29/30/28/29/30/29/29/31/29/30/29/31/32/32/32/33/32/33/31"
theorem leaf1792 : Segment system t0 t1 t2 1792 32 row1792 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1824 : List Row := blockRows% "27/28/26/27/29/27|295/28/27/27/28/28/28/29/28/30/27/30/29/29/29/30/27/31/28/26/27/29/28/28/29/30/28"
theorem leaf1824 : Segment system t0 t1 t2 1824 32 row1824 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1856 : List Row := blockRows% "29/29/29/28/29/27/28/27/30/31/32/32/32/31/33/30/30/30/32/31/31/28/31/29/29/30/31/32/31/30/33/31"
theorem leaf1856 : Segment system t0 t1 t2 1856 32 row1856 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1888 : List Row := blockRows% "28/28|294,480|295,480/30/29/29/26|38|39|293,480|294,416,480,488|295,352,360,384,416,420,448,480,484,488|303|359,416,480|423,480|599/30/27/25/26|295/28/29/27/28|295,480,488/30/27/28/27/31/28/28/25/29/26/24/25/27/28/26/27/29/26"
theorem leaf1888 : Segment system t0 t1 t2 1888 32 row1888 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1920 : List Row := blockRows% "30/30/29/28/30/28/29/27/30/29/31/29/31/28/30/27/33/32/33/32/34/30/32/30/30/30/31/30/32/30/31/28"
theorem leaf1920 : Segment system t0 t1 t2 1920 32 row1920 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1952 : List Row := blockRows% "29/28/29/28/30/27/29/26/26/27/29/28/28/27/29/26/29/29/31/30/31/30/32/29/25/25/28/28/27/27/30/28"
theorem leaf1952 : Segment system t0 t1 t2 1952 32 row1952 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1984 : List Row := blockRows% "32/32/33/31/31/28/30/27/29/30/32/31/31/30/32/29/32/32/34/34/32/30/33/30/28/28/29/30/30/30/31/30"
theorem leaf1984 : Segment system t0 t1 t2 1984 32 row1984 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row2016 : List Row := blockRows% "28/29/31/30/28/27|86,676|87|294|295|598|599|631/29/26|86,676|118|598|599/24/25|598|599/27/28/26/27|86|295|517|519|533|534|535|597|598,573|599,565,573/29/27|86|598|599/27/28/30/29/27/28/30/27/23|552,632,888/23|517|557|598|813/26/26/25/25|517|599/28/27"
theorem leaf2016 : Segment system t0 t1 t2 2016 32 row2016 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
end Quadric.Five.Census.Block.Case02
