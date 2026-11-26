import Quadric.Five.Intervals
import Quadric.Five.Resources.System03

namespace Quadric.Five.Census.Block.Case03
set_option maxRecDepth 16384
set_option maxHeartbeats 24000000
set_option Elab.async false
private theorem cachedMinimum : packList system.lowFirst=482434396539755347081504971451361457912975863606845381933842595863316665813500505671160365609229479671891423781005527314000022189713514409446857749306725969771591948063066502833900830103541006919893039932611451602547503618537644482473213931507992513239421582346222803676961182479263956262481047516601394680579709034691314039167503426723821431690099678650822268098028408516693715296619382068209070582881741767402694856910153755106579970266611506630805212422586495216550770425991657237466532396848471167772061078241801009632906006169071754777186898164351434496352712406213462171954355522082674377085198758435514109650883183633511376819188905373936710191548499798761817166834781658727030457500698252071005838851246810129806909074583779825777395248830154367422975458584181158265505749541731172508911921542866109267049878506501710206396140300822287386030817797308337206589678305905992861810539774850411483708126372985530073123462447408133179336886081827127602301064529160355701222174834451024539217984429656480921467024645608658713230210142575780139253216472264498740467419639520425277548066882476647298856110351803493835040693333436205980955899832336214609462050296310847085712644556322227318632295914270594497376377456761353745503692155484399357506098540700406959499955391597982473071587733903683079252107291372768983864728115082813814503823927901787447286409927678575016315719989978060980897457438598730543255410334843535265535167306967523588975023521911547414661445056854258508851238867457067770242326731486059658342526540254873714136253093553668858208255948713859182555852486868864594747280234157792789525935920394737518899728340686665533933298840736092170698171469970917633237573551292091883619618516462438759375820013256682689630722587587882517651236282536866152394671854691243640555935729447950917652986679361677699658823999869122980920490526061196945937704631146408329454533437990905440461222896117649847599348878132945540165015979160073263232672125517463532446750599363440330575299087753218445334435102166453196172750868813163862655997551363494567586703487765846603617396295199033192839324918039173894174741540767521380001989762200165963139203725401931711947940237126930893792170579851795280534413837650143624820707104182432745323701496234029455208121664016269402287199956640496985407379947895672773506235029216480142050761204939964673855434784347179271292875203182205049241313024818170082210865171619640266067774088960771393334842689071533761210525907476942393452454585465401457225967343581959305055658499350178417861072432330247117730947809013364548139170326737627519258495592211428548215053119182206573355197796132492655389935615323024109053478619779478184901567483907636929804065850270032891956634484987270405168099854009784829895665750065133123462056836662986359584303065579114294448966120567477871544265732852020827347731349251327571073066184583928618232516954903960575333082556964566416982944732914495164890076444328340643928800892501866819901409349892392159315793686452344819514228722033370168243611290425266664287782208397409718959477802824907937885593844390062734350 := by decide +kernel
noncomputable def row0 : List Row := blockRows% "26/27/23/26/22/24/19|208|210|424|429|430/22/32/31/29/32/28/29/25/28/28/29/25|424/28/25/28/22/25/31/32/30/33/29/32/28/30"
theorem leaf0 : Segment system t0 t1 t2 0 32 row0 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row32 : List Row := blockRows% "29/29/27/29/26/27/24/26/32/32/32/33/31/32/30/31/30/30/27/30/28/30/25/28/32/30/31/34/30/31/29/32"
theorem leaf32 : Segment system t0 t1 t2 32 32 row32 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row64 : List Row := blockRows% "28/29/25/28/24/26/21/24/30/31/29/34/28/31/27/30/27/30/26/29/25/30/24/27/29/29/28/32/27/30/26/31"
theorem leaf64 : Segment system t0 t1 t2 64 32 row64 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row96 : List Row := blockRows% "28/29/28/31/27/29/26/28/30/29/30/33/29/30/28/33/28/28/27/30/26/29/25/28/29/26/29/31/28/28/27/32"
theorem leaf96 : Segment system t0 t1 t2 96 32 row96 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row128 : List Row := blockRows% "29/28/26/29/25/26/22|208/25/33/32/30/31/31/30/28/29/32/31/29/31/28/29/25/27/33/32/33/33/32/33/30/31"
theorem leaf128 : Segment system t0 t1 t2 128 32 row128 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row160 : List Row := blockRows% "32/31/31/32/29/29/27/28/33/32/33/32/34/33/31/32/33/31/32/34/31/32/30/31/30/29/31/31/33/31/32/34"
theorem leaf160 : Segment system t0 t1 t2 160 32 row160 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row192 : List Row := blockRows% "31/30/28/31/27/28/24/27/33/31/32/35/30/30/29/31/30/30/29/33/28/31/27/29/30/28/31/32/30/30/29/33"
theorem leaf192 : Segment system t0 t1 t2 192 32 row192 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row224 : List Row := blockRows% "31/30/31/34/30/31/29/30/30/28/32/31/32/29/30/32/30/27/30/32/29/29/28/33/28/25/29/28/30/27/29/30"
theorem leaf224 : Segment system t0 t1 t2 224 32 row224 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row256 : List Row := blockRows% "27/28/25/27/23/24|389/21/23/32/31/29/32/29/29/27/28/30/31/27/30/27/28/24/27/31/32/31/34/31/32/30/31"
theorem leaf256 : Segment system t0 t1 t2 256 32 row256 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row288 : List Row := blockRows% "29/30/28/29/26/27/25/26/32/32/32/33/32/32/30/31/31/31/29/32/30/31/27/30/31/30/31/33/32/31/31/34"
theorem leaf288 : Segment system t0 t1 t2 288 32 row288 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row320 : List Row := blockRows% "29/30/27/29/25|429/26/23/25/31/31/31/34/30/31/29/30/29/30/28/31/27/30/26/29/30/29/30/33/29/30/28/33"
theorem leaf320 : Segment system t0 t1 t2 320 32 row320 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row352 : List Row := blockRows% "28/29/30/31/28/29/27/28/30/29/32/33/30/30/30/33/29/28/29/31/28/29/27/30/29/26/30/31/29/28/29/32"
theorem leaf352 : Segment system t0 t1 t2 352 32 row352 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row384 : List Row := blockRows% "30/30/28/30/26/27/24/26/33/31/30/31/32/32/28/31/34/33/31/34/30/31/27/30/33/32/33/33/34/34/31/34"
theorem leaf384 : Segment system t0 t1 t2 384 32 row384 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row416 : List Row := blockRows% "33/32/31/32/29/30/28/29/32/30/33/31/34/32/31/32/34/31/34/34/33/33/32/33/30/27/31/30/34/31/33/34"
theorem leaf416 : Segment system t0 t1 t2 416 32 row416 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row448 : List Row := blockRows% "32/32/30/32/28/29/26/28/34/31/34/34/32/32/31/33/31/30/31/35/30/32/29/32/31/28/32/32/31/30/31/34"
theorem leaf448 : Segment system t0 t1 t2 448 32 row448 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row480 : List Row := blockRows% "31/30/33/34/31/32/30/31/30/28/32/31/31/29/31/32/30/27/31/32/30/29/30/33/28/25/29/28/30/27/29/30"
theorem leaf480 : Segment system t0 t1 t2 480 32 row480 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row512 : List Row := blockRows% "27/28/25/27/23/24/21/23/32/32/27/30/29/30/25/28/30/32/27|424/30/27/29/24/27/31/33/30/33/31/34/28/31"
theorem leaf512 : Segment system t0 t1 t2 512 32 row512 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row544 : List Row := blockRows% "29/30/28/29/26/27/25/26/30/30/30/31/32/33/28/30/31/32/29/32/30/31/27/30/29/29/29/31/32/33/31/33"
theorem leaf544 : Segment system t0 t1 t2 544 32 row544 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row576 : List Row := blockRows% "29/30/27/29/25/26/23/25/31/32/31/34/30/32/29/31/29/31/28/31/27/31/26/29/30/31/30/32/29/32/28/33"
theorem leaf576 : Segment system t0 t1 t2 576 32 row576 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row608 : List Row := blockRows% "28/29/30/31/28/29/27/28/29/28/30/31/30/30/30/32/29/29/29|106/31/28/30/27/30/27/27/28/29/29/29/28/31"
theorem leaf608 : Segment system t0 t1 t2 608 32 row608 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row640 : List Row := blockRows% "30/31/26/29/26/27/24/26/32/31/28/31/31/32/26/29/34/34/29/32/30/32/27/30/31/32/31/33/34/34/29/32"
theorem leaf640 : Segment system t0 t1 t2 640 32 row640 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row672 : List Row := blockRows% "32/31/29/31/29/30/26/27/30/29/31/31/33/32/29/31/32/32/32/34/33/34/30/32/28/27/29/30/32/31/31/33"
theorem leaf672 : Segment system t0 t1 t2 672 32 row672 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row704 : List Row := blockRows% "32/33/30/32/28/29/26/28/32/31/32/34/31/32/29/32/31/32/31/34/30/34/29/32/29/30/30/31/30/31/29/32"
theorem leaf704 : Segment system t0 t1 t2 704 32 row704 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row736 : List Row := blockRows% "30/29/32/32/31/31/28/29/28/27/30/30/29/29/29/31/29/28/29/31/30/30/29/31/26/25/27/28/28/27/27/30"
theorem leaf736 : Segment system t0 t1 t2 736 32 row736 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row768 : List Row := blockRows% "27/27/25/27/23/24/22/23/30/30/27/29/29/30/25/27/30/30/27/30/28/29/26/28/30/30/30/32/33/34/28/31"
theorem leaf768 : Segment system t0 t1 t2 768 32 row768 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row800 : List Row := blockRows% "29/28/27/27/26/27/25/26/27/26/29/29/30/30/27/28/30/29/30/30/30/31/29/30/26/25/28/28/30/29/30/31"
theorem leaf800 : Segment system t0 t1 t2 800 32 row800 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row832 : List Row := blockRows% "29/30/28/29/25/26/24/25/30/29/31/32/31/32/29/31/30/30/30/32/29/31/28/30/28/28/29/30/30/31/30/33"
theorem leaf832 : Segment system t0 t1 t2 832 32 row832 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row864 : List Row := blockRows% "28/28/30/31/28/29/27/28/25/24/28/27/29/28/30/30/28/27/30/30/28/29/29/30/24/23|813/26/26/28/27/28/30"
theorem leaf864 : Segment system t0 t1 t2 864 32 row864 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row896 : List Row := blockRows% "30/29/26/28/26/27/24/26/30/29/28/29/30/30/26/28/33/32/29/31/31/32/27/30/29/29/30/31/32/32/29/31"
theorem leaf896 : Segment system t0 t1 t2 896 32 row896 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row928 : List Row := blockRows% "30/29/28/28/29/29/26/27/26/25/29/28/30/29/28/28/29/28/31/31/33/32/30/31/25/24/27/27/29/28/29/31"
theorem leaf928 : Segment system t0 t1 t2 928 32 row928 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row960 : List Row := blockRows% "32/32/30/31/28/29/27/28/29/28/30/31/30/31/30/31/31/31/32/33/31/33/31/32/27/27/28/29/30/31/29/32"
theorem leaf960 : Segment system t0 t1 t2 960 32 row960 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row992 : List Row := blockRows% "28/27/31/30/29/29/28/28/24/23/27/26/27/27/28/29/27/26/29/29/29/28/29/30/23/22/25/25/27/26/27/29"
theorem leaf992 : Segment system t0 t1 t2 992 32 row992 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1024 : List Row := blockRows% "28/25/25/26/25/24/22/23/32/29/31/30/29/28/27/27/29/26/26/27/27/26/24/25/31/30/31/30/31/30/28/29"
theorem leaf1024 : Segment system t0 t1 t2 1024 32 row1024 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1056 : List Row := blockRows% "29/26/28/27/28/26/26/26/32/30/33/31/32/30/31/30/30/27/28/28/29/27/26/28/30/27/32/29/31/29/30/31"
theorem leaf1056 : Segment system t0 t1 t2 1056 32 row1056 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1088 : List Row := blockRows% "30/27/27/28/27/26/24/25/31/29/32/32/31/30/29/29/29/28/27/29/28/28/25/27/28/26/30/30/29/28/29/30"
theorem leaf1088 : Segment system t0 t1 t2 1088 32 row1088 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1120 : List Row := blockRows% "30/28/29/29/30/28/27/28/29/26/33/31/30/28/31/32/28/25/28/28/29/27/26/29/26/23/30/28/28/25/30/29"
theorem leaf1120 : Segment system t0 t1 t2 1120 32 row1120 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1152 : List Row := blockRows% "30/27/27/28/26/25/23|208|210/24/33/30/31/30/30/29/28/28/32/29/29/30/28/28/25/26/31/29/32/31/32/31/29/30"
theorem leaf1152 : Segment system t0 t1 t2 1152 32 row1152 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1184 : List Row := blockRows% "32/29/31/30/29/28/28/27/32/29/33/30/33/31/32/30/31/28/32/31/32/30/30/30/28/26/29/28/31/28/32/31"
theorem leaf1184 : Segment system t0 t1 t2 1184 32 row1184 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1216 : List Row := blockRows% "31/29/29/30/28/27/25/26/31/28/34/33/32/30/30/30/29/27/31/31/30/29/27/28/27/25/30/29/29/27/30/30"
theorem leaf1216 : Segment system t0 t1 t2 1216 32 row1216 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1248 : List Row := blockRows% "30/27/33/32/31/29/30/29/28/25/31/28/30/27/31/30/27/24/30/29/29/26/30/30/25/22/27/25/27/24/28/27"
theorem leaf1248 : Segment system t0 t1 t2 1248 32 row1248 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1280 : List Row := blockRows% "29/27/27/28/26/26/24/25/32/29/31/30/31/30/30/29/31/28/28/29/29/28/26/28/32/29/32/31/34/32/31/32"
theorem leaf1280 : Segment system t0 t1 t2 1280 32 row1280 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1312 : List Row := blockRows% "30/28/29/29/28/28/27/28/33/29/34/30/34/32/33/32/32/27/30/30/31/29/28/30/30/27/31/28/32/29/32/32"
theorem leaf1312 : Segment system t0 t1 t2 1312 32 row1312 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1344 : List Row := blockRows% "31/29/29/30/28/28/26/27/32/29/34/34/33/31/32/31/31/28/29/31/30/30/27/30/29/26/32/31/31/28/31/32"
theorem leaf1344 : Segment system t0 t1 t2 1344 32 row1344 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1376 : List Row := blockRows% "31/28/31/31/30/30|295/29/30/29/26/34/31/31/28/33/33/28/25/29/28/30/27/28/30/26/23/30/28/28/25/31/30"
theorem leaf1376 : Segment system t0 t1 t2 1376 32 row1376 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1408 : List Row := blockRows% "32/29/31/30/28/27/27/26/33/28/32/29/32/30/31/30/34/30/33/32/31/29/29/29/31/29/32/30/34/31/32/31"
theorem leaf1408 : Segment system t0 t1 t2 1408 32 row1408 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1440 : List Row := blockRows% "34/29/33/30/31/29/30/29/30/27/33/28/34/29/33/30/31/28/33/30/33/30/33/31/27/24/29/27/31/28/33/31"
theorem leaf1440 : Segment system t0 t1 t2 1440 32 row1440 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1472 : List Row := blockRows% "33/30/33/31/30/28/29/28/31/28/34/31/33/30/33/31/30/27/33/32/32/29/31/30/28/25/30/29/30/27/32/32"
theorem leaf1472 : Segment system t0 t1 t2 1472 32 row1472 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1504 : List Row := blockRows% "30/27/34/32/32/29/32/30/28/25/31/28/30/27|597|599/33/30/27/24/32/29/29/26/32/31/25/22/27/25/27/24|597/30/27"
theorem leaf1504 : Segment system t0 t1 t2 1504 32 row1504 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1536 : List Row := blockRows% "29/29/27/29/26/27/24/26/34/31/30/31/32/32/28/31/31/30/28/31/29/30/26/29/33/31/32/32/34/34/31/34"
theorem leaf1536 : Segment system t0 t1 t2 1536 32 row1536 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1568 : List Row := blockRows% "30/30/29|114/30/28/29/27/28/32/29/32/30/34/32/31/32/32/29/30/31/31/31/28/31/30/27/29/28/34/31/31/32"
theorem leaf1568 : Segment system t0 t1 t2 1568 32 row1568 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1600 : List Row := blockRows% "31/31/29/31/28/29/26/28/34/31/34/34/33/33/32/33/31/30/29/31/30/32/27/30/31/28/32/32/31/30/31/33"
theorem leaf1600 : Segment system t0 t1 t2 1600 32 row1600 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1632 : List Row := blockRows% "31/30/31/32/30/31/29/30/30/28/32/31/32/30/32/32/30/27/29|106/30/30/29/28/30/28/25/29/28/30/27/29/30"
theorem leaf1632 : Segment system t0 t1 t2 1632 32 row1632 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1664 : List Row := blockRows% "33/30/29/30/29/29/27/28/33/28/30/29/33/30/29/30/34/31/31/32/33/31/30/31/30/29/31/30/34/31/31/31"
theorem leaf1664 : Segment system t0 t1 t2 1664 32 row1664 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1696 : List Row := blockRows% "32/29/31/30/31/30/29/29/29/27/31/28/33/29/31/30/31/29/31/30/34/32/32/31/27/24/28/27/31/28/32/31"
theorem leaf1696 : Segment system t0 t1 t2 1696 32 row1696 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1728 : List Row := blockRows% "34/32/32/32/31/30/29/30/31/30/32/31/34/31/32/31/32/29/33/34/32/31/31/32/28/27/29/29/32/29/31/32"
theorem leaf1728 : Segment system t0 t1 t2 1728 32 row1728 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1760 : List Row := blockRows% "29/28/32/31/31/30/30/29|86/27/25/29/28/29/27/31/30/28/26/30/29/30/28/30/31/25/22/26/25/27/24/28/27"
theorem leaf1760 : Segment system t0 t1 t2 1760 32 row1760 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1792 : List Row := blockRows% "29/28/27/29/26/27/25/26/33/29/30/30/32/31/28/30/31/29/28/31/30/31/28/30/31/29/30/30/35/32/31/33"
theorem leaf1792 : Segment system t0 t1 t2 1792 32 row1792 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1824 : List Row := blockRows% "30/28/29/28/28/29/27/28/28/27/30/28/32/30/30/30/31/28/29/29/31/30/30/31/27/25/27/26/31/29/29/30"
theorem leaf1824 : Segment system t0 t1 t2 1824 32 row1824 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1856 : List Row := blockRows% "31/31/30/31/28/29/27/28/31/30/33/32/33/33/32/33/31/30/30/31/31/31/29/31/29/28/30/31/31/30/32/33"
theorem leaf1856 : Segment system t0 t1 t2 1856 32 row1856 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1888 : List Row := blockRows% "30/29/31/30/30/29|295/29/30/26/25/29/28/30/29/31/30/29/27/29/29/29/28/29/29/25/23/27/26/29/27/29/29"
theorem leaf1888 : Segment system t0 t1 t2 1888 32 row1888 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1920 : List Row := blockRows% "32/28/29/29/29/30/27/29/31/26/30/27/32/28/29/29/34/29/31/30/34/31/30/32/30/27/31/28/34/29/31/30"
theorem leaf1920 : Segment system t0 t1 t2 1920 32 row1920 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1952 : List Row := blockRows% "30/27/30/28/31/29/29/29/27/25/30/26/31/27/30/28/30/27/30/28/34/30/32/31/25/22/28/25|592/29/26/30/29"
theorem leaf1952 : Segment system t0 t1 t2 1952 32 row1952 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1984 : List Row := blockRows% "33/30/32/31/31/30/30/30/30/28/32/29/33/30/32/31/32/29/33/32/32/31/32/32/28/25/29/28/32/29/31/32"
theorem leaf1984 : Segment system t0 t1 t2 1984 32 row1984 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row2016 : List Row := blockRows% "29/28/32/30/31/30/30/29/25/23/28/26/29/27/30/30/28/26/30/29/30/28/30/30/23/20|592|597|598/26/23/27/24/28/27"
theorem leaf2016 : Segment system t0 t1 t2 2016 32 row2016 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
end Quadric.Five.Census.Block.Case03
