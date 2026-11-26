import Quadric.Five.Intervals
import Quadric.Five.Resources.System12

namespace Quadric.Five.Census.Block.Case12
set_option maxRecDepth 16384
set_option maxHeartbeats 24000000
set_option Elab.async false
private theorem cachedMinimum : packList system.lowFirst=448010814764498604922803367992970780080968851726906052616278609711993185136269574891042140037805167838017305247102764840076786326751383076352041116217154501529754631758315365782250046978660899800203396674095767425801487406693432470179596577310820457425431850587592709661158700316716864433395928125904217505692187723296949402537926832948574136264570007542187915217584070337316970586803346710237647494440170227810791989674412007239465136669128921152739388642261039451878828163842215582171224707993400823105841147607180149415197648741712200217124550032112833332285916690231045594745492545502101754879765941292764721655602413882648480881903353101518448498914127345497435111756467024771881573509620645967903393124281316497781959862391799320878406612093355997782871260686680285957903797274252358881691370546584829534029195037838466681916980095359354531023960887587177238872037983300663206282133126366011615988852415397135177580553847765692543080676938986117347480672528818286943105406282672992060032329155935693971235419028129055108650090686688762364912968945094036853305569083534464014820423449611723112530162758044433716927608835674472727191900778372393013117740255732526990153040223059041988140353941788360526514758109152958621041132371781319759590745813082502707571189355310030020030395052415612215967259829761065270890389232122532391800366929722795506074454842060434364104325506969984143147935871659529099162544684529485475962063615286802719169914085145438886724572460992671981764517971367359836316376316039577039573280596775669382041952481209603199205660186459711675674198130353066299007810666615390668587735133864738995340630036856266835585269662953667195782632297374681844381437467206447473965805234114146739046002041225423312897762250541582374993239693169161045196625374104077330429050274836923204694112170889055203833763398692256012596700089465754334099723264187893703552242539296252877048098495182284236338015007309782666926054054020967742036444741167269095735455385430747614098338458747122143623656249185339320585239061666749212464815579486734503646692938929811964939834717015683133894833763744786165808256575512887011223456828714838250966082257381792453817187556594403927754181760906534589567083504573621413791925871096172941501352339448531995491586133826692663703692381328067913166300330463359053704670956645570746859165191336902082872259349712152872062020073611091750418417976520251718997900635820160323585798265260757843070768196038267962677710255200657989010569075755794766810517616998896381822631461998317688185842740160350469415917825501458808987153268706730518170452932839919438055136105820657676526116091948209608538341881498549589776538050953840207672144141704289675852271741055227053071764896541448857836356285982005902383214180897313830297721918877142493820019429899550392366224044324075431811367436903274425510783729676384611821255949369376983759676949206200123543198571057618823892439834064334124775115448146279491237839013249004726756279455660343085346805646251687071532273254934534105081802987586948277736324662250076649219894682701467575210804127583832128525 := by decide +kernel
noncomputable def row0 : List Row := blockRows% "26/25/26|0/26/24/23/24/24/28/29/28/29/28/27/28/28/25|0/26/27|0|8|32|40|64,3|136|168|288|424/28/27/28/27/27/27|0/30/30|0/32/29/32/31/32"
theorem leaf0 : Segment system t0 t1 t2 0 32 row0 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row32 : List Row := blockRows% "27/26/30/29/27/26/28/27/27/30/31/31/29/30/30/29/26/27/29/30/28/29/31/30/28/30/31/34/30/32/32/31"
theorem leaf32 : Segment system t0 t1 t2 32 32 row32 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row64 : List Row := blockRows% "26/27/28/28/26/25/26/26/26/29/30/32/28/29/30/30/23|0|40|46|168/26/26|136|168|170|424/29/25/28/28/29/25/28/28/31/27/30/30/30"
theorem leaf64 : Segment system t0 t1 t2 64 32 row64 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row96 : List Row := blockRows% "25/27/30/31/27/28/30/29/25/28/30/33/27/30/31/29/24/26/27/30/26/28/29/29/26/28/29/31/28/29/29/29"
theorem leaf96 : Segment system t0 t1 t2 96 32 row96 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row128 : List Row := blockRows% "27/27/29/29/27/26/27/27/29/32/29/30/29/30/29/28/26/29/29/30/28/29/29/28/28/31/31|0/32/30/33/31/30"
theorem leaf128 : Segment system t0 t1 t2 128 32 row128 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row160 : List Row := blockRows% "28/29/31/30/30/29/29/27/30/32/32/31/32/30/30/27/27/29/30/33/29/31/32/30/29/31/31/32/31/32/31/30"
theorem leaf160 : Segment system t0 t1 t2 160 32 row160 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row192 : List Row := blockRows% "27/28/30/31/27/28/29/28/29/31/32/32/29/31/29/28/24/27/27/30/26|140/29/29|136/29/26|0/29/29|136/31/28|136/30/28|8|136,750,974,998,1002,1006|140,1006/29"
theorem leaf192 : Segment system t0 t1 t2 192 32 row192 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row224 : List Row := blockRows% "27/28/31/31/29/30/30/27/28/30/32/31/30/29/28/27/25/27/28/30/27/28/29/29/27/28/29/30/28/28/27/28"
theorem leaf224 : Segment system t0 t1 t2 224 32 row224 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row256 : List Row := blockRows% "26/25/27/26/24|389,388/23|261,388|293|389,388,389|397|405,388|421,388|429|517|533|901|917/25/24|389,388|421/27/29/28/28/28/27|389,388|917/28/28/27|0/28/29|0/30/29/28/29/29/27|0|256|288|512|513/30/30|0/32/31/32/31/31"
theorem leaf256 : Segment system t0 t1 t2 256 32 row256 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row288 : List Row := blockRows% "27/28/30/29/27/26/28/27/27/30/30/29/29/30/30/28/27/28/31/31/29/30/33/31/28/30/31/32/30/32/32/30"
theorem leaf288 : Segment system t0 t1 t2 288 32 row288 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row320 : List Row := blockRows% "26/27/29/28/26/25|389,388|421|429/27/26/26/29/31/32/28/29/31/29/25/27/28/31/27/29/30/30/27/29/30/33/29/31/31/30"
theorem leaf320 : Segment system t0 t1 t2 320 32 row320 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row352 : List Row := blockRows% "25/27/30/31/27/28/30/28/25/28/30/31/27/30/30/27/25/26/29/31/27/28/31/29/26/28/31/31/28/29/29/28"
theorem leaf352 : Segment system t0 t1 t2 352 32 row352 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row384 : List Row := blockRows% "29/28/29/29/27/26/28/27/29|528,540/30/29/29/31/30|533/29/28/29/31/32/33/32/31/32/31/30|0|512|528/33/32|0/32/34/34/31/30"
theorem leaf384 : Segment system t0 t1 t2 384 32 row384 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row416 : List Row := blockRows% "30/31/31/30/30/29/29/27/30/31/31/29/32/30/30/27/30/31/34/34/32/32/33/30/31/32/31/32/33/32/31/29"
theorem leaf416 : Segment system t0 t1 t2 416 32 row416 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row448 : List Row := blockRows% "29/30/32/31/29/28/30/28/29/32/33/32/30/30|661/29/28/28/30/31/33/30/31/32/31/30/31/32/33/31/31/28|136,1006/29"
theorem leaf448 : Segment system t0 t1 t2 448 32 row448 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row480 : List Row := blockRows% "28/30/33/31/30/30/30/27/28/31/31/30/28/27|517|533/27/26/28/28/31/31/29/28/31/29/29/28/29/30/29/28/27/27"
theorem leaf480 : Segment system t0 t1 t2 480 32 row480 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row512 : List Row := blockRows% "26/25/26|0|32|34|42|64|82|114|288/26/24/23/25/24/27/27/26|0/26/28/27/26/26/29/30/29|0|32|40/30/29/28/29/29/28/32/29|0/30/31/32/29/29"
theorem leaf512 : Segment system t0 t1 t2 512 32 row512 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row544 : List Row := blockRows% "27/28/28/27/27/26/26/25/27/28/28/27/29/28/28/26/28/30/32/32/30/31/31/29/28/31/30/30/30/31/30/28"
theorem leaf544 : Segment system t0 t1 t2 544 32 row544 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row576 : List Row := blockRows% "26|46,328/27/29/28/26|46/25/27/26/26/29/30/30/28/29/29/27/27/29/30/33/29/30/31/30/27/30/31/32/29/32/29/28"
theorem leaf576 : Segment system t0 t1 t2 576 32 row576 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row608 : List Row := blockRows% "25|38,328|42|46,328,840|62|86|102|110,328|118|294|302,328|558,328|574|598|606|638/28/30/29/27|46,328/28/28/26/25/28/30/29/27/28/28/25/26|46,328/28/31/31/28/30/30/28/26/29/29/29/28/28/27/26"
theorem leaf608 : Segment system t0 t1 t2 608 32 row608 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row640 : List Row := blockRows% "29/28/27/27/27/26/26/25/27|528,540/28/27/27/29/28/27/26/31/33/30/31/32/31/30/29/31/33/30|0/30/33/32/29/28"
theorem leaf640 : Segment system t0 t1 t2 640 32 row640 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row672 : List Row := blockRows% "30/29/29/28/28/27/27/25/28/29/29/27/30/28/28/25/31/33/33/32/33/31/31/28/29/31/30/30/31/30/29/27"
theorem leaf672 : Segment system t0 t1 t2 672 32 row672 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row704 : List Row := blockRows% "29/30/30/29/29/28/28/26/29/32/31/30/29/28/27/26/30/32/33/33/32/32/30/29/30/33/30/31/29/29/26|136,1006/27"
theorem leaf704 : Segment system t0 t1 t2 704 32 row704 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row736 : List Row := blockRows% "28|598/31/31/29/30/28/28/25/28/29/29/28/26/25/25/24/29/30/32/31/31/30/29/27/28/29/28/28/27/26/25/25"
theorem leaf736 : Segment system t0 t1 t2 736 32 row736 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row768 : List Row := blockRows% "24|0|32|288|528|532/25/25|288/24/24/23/25/24/25|0|512|528|532/25/25|0/24|288/26/25/25/23/28/28/29/29/29/28/29/28/27|0/30/29|0/28|288/31/29/28/26"
theorem leaf768 : Segment system t0 t1 t2 768 32 row768 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row800 : List Row := blockRows% "26/26/26/25/27/26/26/24/25/26/26/24|288/27/25/25/22/28/29/31/29/30/30/30/27/26/28/28/27|288,1008/29/28/28/25"
theorem leaf800 : Segment system t0 t1 t2 800 32 row800 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row832 : List Row := blockRows% "26/27/29/28/26/25/27/25/26/29/29/27/28/28/28/25/27/29/32/32/29/30/31/28/27/30/30/30/29/30/29/27"
theorem leaf832 : Segment system t0 t1 t2 832 32 row832 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row864 : List Row := blockRows% "25/28/30/28/27/27/27/24/25/27/27/26/27/26/26/23/26/28/31/29/28/29/29/26/25/26/26/27/27/26/26/24"
theorem leaf864 : Segment system t0 t1 t2 864 32 row864 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row896 : List Row := blockRows% "27/26/26/25/27/26/26/24/25|0|16|512|528,532,536,540,572,796|529|532,540|533|560|592|784/26|528|532|533/26|528/24/27/25|532|533/25/22/31/31/30/29/32/30/29/27/30/30/29|0/27/31/28/27/25"
theorem leaf896 : Segment system t0 t1 t2 896 32 row896 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row928 : List Row := blockRows% "28/27/27/25/28/26/26/23/26/26/26/23/27/24|532|533|789/24/21/31/31/31/28/32/29/29/26/26/27/27/26/28/27/27/24"
theorem leaf928 : Segment system t0 t1 t2 928 32 row928 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row960 : List Row := blockRows% "29/30/30/28/29/27/27/24/27/29/29/26/27/26|533/26/24/30/32/33/31/32/30/30/27/29/30/28/29/28/27/26/26"
theorem leaf960 : Segment system t0 t1 t2 960 32 row960 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row992 : List Row := blockRows% "28/30/30/27/28/26/26/23/25/26/26/25/24/23|517|532|533|534|535|597|598|599|661|789|917|959/23/22/29/30/31/29/29/28/28/25/24/25/25/26/25/24/24/23"
theorem leaf992 : Segment system t0 t1 t2 992 32 row992 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1024 : List Row := blockRows% "23/22/25/25/25/24/26/25/28/28/29/30/31/30/31/30/23/23/24|0|32|40|64,1,3,19,67,131|65,3|66,3|80|96|288/25/25/25/26/25/26/28/28|0|64/29/28/31/31/29"
theorem leaf1024 : Segment system t0 t1 t2 1024 32 row1024 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1056 : List Row := blockRows% "24/23/27/26/26/25/29/28/29/29/32/32/31/31/32/29/25/24/26/27/27/26/28/26/27/29/30/30/29/30/31/28"
theorem leaf1056 : Segment system t0 t1 t2 1056 32 row1056 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1088 : List Row := blockRows% "25/24/27/27/27/26/28/27/27/29/30/33/29/31/32/30/22/25/25/26/24/27/27/25/24/27/27/29/26/28/28/27"
theorem leaf1088 : Segment system t0 t1 t2 1088 32 row1088 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1120 : List Row := blockRows% "25/25/29/28/27/27/31/29/27/28/31/32/29/29/32/29/23/25/26/26/25/26/27/24|431|463|494|495,483/25/26/27/28/26/26/27/26"
theorem leaf1120 : Segment system t0 t1 t2 1120 32 row1120 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1152 : List Row := blockRows% "26/25/28/28/27/26/27/26/29/31/30/30/32/30/29/27/25/26/27|0|64,3/28/27/28/28/26/27/30/30|0|64/30/29/31/30/28"
theorem leaf1152 : Segment system t0 t1 t2 1152 32 row1152 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1184 : List Row := blockRows% "27/26/30/29/29/28/29/26/30/31/32/30/32/29/29/26/26/27/29/29/28/29/30/27/28/29/28/29/29/29/30/27"
theorem leaf1184 : Segment system t0 t1 t2 1184 32 row1184 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1216 : List Row := blockRows% "26/27/29/30/28/28/29/27/28/30/31/31/30/30/29/27/23/26/26|64/28/25/27/27/26/25/27/27|0|64/28/26/27/27|0|136/27"
theorem leaf1216 : Segment system t0 t1 t2 1216 32 row1216 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1248 : List Row := blockRows% "26/27/30/30/28/28/29/26/28/28/31/30/29/28/29/26/24/25/26/27/25/25/26/25/25/25/26/27/25/25/26/25|69"
theorem leaf1248 : Segment system t0 t1 t2 1248 32 row1248 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1280 : List Row := blockRows% "25/24/27/27/27/26/28/27/29/28/31/31/31/30/31/30/25/25/26|0|64|288/27/28/27/30/28/28/29/30|0/31/32/33/33/31"
theorem leaf1280 : Segment system t0 t1 t2 1280 32 row1280 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1312 : List Row := blockRows% "26/25/29/28/28/27/31/29/30/29/33/31/32/32/32/29/27/26|293/29/29/29/28/31/28/29/30/31/30/31/30/32/30"
theorem leaf1312 : Segment system t0 t1 t2 1312 32 row1312 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1344 : List Row := blockRows% "27/26/30/29/29/28/30/29/29/31/34/34/31/32/33/30/26/27/29/29/28/29/30/27/28/29/30/31/29/29/30/29"
theorem leaf1344 : Segment system t0 t1 t2 1344 32 row1344 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1376 : List Row := blockRows% "27/27/31/30/29/29/32/29/28/29/33/31/30/29/31/28/26/26/29/27/27/26/29/26/27/26/29/29/27/26/29/28"
theorem leaf1376 : Segment system t0 t1 t2 1376 32 row1376 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1408 : List Row := blockRows% "28/27/30/30/29/28/30/27/30/31/31/29/33/30|533/29/27/28/28/29/30/31/30/31/28/29/31/31|0/30|0/32/32/30/28|0|389"
theorem leaf1408 : Segment system t0 t1 t2 1408 32 row1408 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1440 : List Row := blockRows% "29/28/32/30/31/29/29/26/31/31/31/28/32/29/29/26/29/29/32/30/30/29/32/28/29/29/28/29/30/29/30/29"
theorem leaf1440 : Segment system t0 t1 t2 1440 32 row1440 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1472 : List Row := blockRows% "28/29/33/31/30/29/30/27/31/31/33/31/32/30/30/27/27/28/29/30/28/28/29/28/28/28/29/30/28/28|517,105/29/29"
theorem leaf1472 : Segment system t0 t1 t2 1472 32 row1472 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1504 : List Row := blockRows% "28/28/32/30/29/28/29/26/29/28/31/30/29/28|517,105|533|581|597|599/29/26/26/25/28/28/26/25/28/27/26/25|517,105|581/26/27/26/25|5,105|69|261|293|389|397|517,105,617|525,105|533|581,105|597|773,105|901|909/28/27|389"
theorem leaf1504 : Segment system t0 t1 t2 1504 32 row1504 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1536 : List Row := blockRows% "27/26/29/29/27/26/28/27/30/30/29/29/31/30/29/28/27/27/28|64/29/30/29/32/30/30/31/32/32/34/34/31/30"
theorem leaf1536 : Segment system t0 t1 t2 1536 32 row1536 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1568 : List Row := blockRows% "28/27/31/30/30/29/29/27/30/31/31/29/32/30/30/27/29/28/31/31/31/30/32/30/31/32/30/29/33/31/30/28"
theorem leaf1568 : Segment system t0 t1 t2 1568 32 row1568 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1600 : List Row := blockRows% "29/28/32/31/29/28/30/28/29/32/33/32/31/31/31/28/28/29/31/31/30/31/32/29/30/31/32/32/31/31/30/29"
theorem leaf1600 : Segment system t0 t1 t2 1600 32 row1600 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1632 : List Row := blockRows% "28/29/33/31/30/30/30/27/28/31/32/29/30/29/29/26/28/28/31/29/29/28/30/28/29/28/29/28/29/28/28/26"
theorem leaf1632 : Segment system t0 t1 t2 1632 32 row1632 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1664 : List Row := blockRows% "30/29/30/29/30/28/28/25/30/30/29/27/31/28/27/25/30/30/31/30/33/31/30/28/31/33/30|0/29/33/31/28/27"
theorem leaf1664 : Segment system t0 t1 t2 1664 32 row1664 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1696 : List Row := blockRows% "31/30/31/28/30/27/27/24|86,676|598/30/29/29/26/30/27/27/24/31/31/32/30/32/30/30/27/29/29/28/29/31/30/29/27"
theorem leaf1696 : Segment system t0 t1 t2 1696 32 row1696 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1728 : List Row := blockRows% "30/31/32/29/31/28/28/25/32/32/31/29/31/28/28/25/29/30/31/32/30/30/30/28/30/30/29/30/30/30/29/28"
theorem leaf1728 : Segment system t0 t1 t2 1728 32 row1728 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1760 : List Row := blockRows% "30|598/30/31/28/30/27|86,676|87|598|599/27|70|86,676|598/24|38|46|70,676|71|86,676,677|87|102|110|118,676|214,676|598|599|606/28/29/29/28/28/27|598|599/27/24|70|86,676|598|599/28/27/30/29/28/27/30/27/27/27/26|64/27/27/27/27/26"
theorem leaf1760 : Segment system t0 t1 t2 1760 32 row1760 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1792 : List Row := blockRows% "26/26/28/27/27/26/28/26/28/28/28/26/29/27/27/24/28/27/30/30/32/31/31/29/30/31/31/29/33/30/29/27"
theorem leaf1792 : Segment system t0 t1 t2 1792 32 row1792 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1824 : List Row := blockRows% "27/27|887,17/29/27/30/28/28/25/28/28/28/25/29/26/26/23/29/28/32/29/32/30/31/28/28/29/28/26|288,880,944,992,1008,1010|289,1008|290,1008|293/30/29/28/26"
theorem leaf1824 : Segment system t0 t1 t2 1824 32 row1824 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1856 : List Row := blockRows% "29/30/32/30/29/28/29/26/29/31/31/28/31/29/29/26/29/30/33/31/31/31/32/29/30/31/31/30/31/31/30/28"
theorem leaf1856 : Segment system t0 t1 t2 1856 32 row1856 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1888 : List Row := blockRows% "28/30/32/29/30/28/28/25/27/28/28/27/29/27/27/24/28/28/31/28/29/28/29/26/26/27/27/26/28/27/27/24"
theorem leaf1888 : Segment system t0 t1 t2 1888 32 row1888 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1920 : List Row := blockRows% "30/29/29/27/30/28/28/25/30/28/28/25/29/26|533/26/23/31/30/32/30/34/31/30/28/32/31/30/28/32/29/28/26"
theorem leaf1920 : Segment system t0 t1 t2 1920 32 row1920 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1952 : List Row := blockRows% "31/29/29/26/30/27/27/24/28/27/27/24/28/25|533|597|599|789|853|855/25/22|597|598|599|853/32/30/32/29/32/30/30/27/27/27/28/27|288,1008/29/28/28/25"
theorem leaf1952 : Segment system t0 t1 t2 1952 32 row1952 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1984 : List Row := blockRows% "32/32/32/29/31/28/28/25/31/30/30/27/30/28/28/25/31/30/33/32/31/30/31/28/30/30/29/30/31/30/29/27"
theorem leaf1984 : Segment system t0 t1 t2 1984 32 row1984 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row2016 : List Row := blockRows% "31/30/31/28/30/27|599/27/24/26/27/27/26/27/26|517|533|534|535|597|598|599|855/26/23|598|599/28/27/30/29/28/27/29/26/25/25/26/26/27/26/26/24"
theorem leaf2016 : Segment system t0 t1 t2 2016 32 row2016 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
end Quadric.Five.Census.Block.Case12
