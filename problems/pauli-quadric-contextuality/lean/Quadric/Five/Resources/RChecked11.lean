import Quadric.Five.Intervals
import Quadric.Five.Resources.System11

namespace Quadric.Five.Census.Block.Case11
set_option maxRecDepth 16384
set_option maxHeartbeats 24000000
set_option Elab.async false
private theorem cachedMinimum : packList system.lowFirst=585738758644477618161781663013165733559131248021884439434724190973293621031149083560721782933178876544311394571166121128737241251182223784521860108751589744075821624368357516980865070797344482158246074107112741577866017388092756493896800039639066751529324836335387076017916642147325641961270491154459364353341547366983021742851683524463059869246283129475668673366087835515952478145585874755965737669276397426189587838972810897995946920417662599990105285299075252096300400418204416757202589276211290797397046127659035441292012339726388122385647491159191465831970887684793776828987743334486369625531175312896867061253079210097327651505369190662571500220919230680058725587107714772916415690227843262505600516637392643254690051918926845382518794601040502975359148335687083313123138198976939361015005220679153319669061445058002136383581556665144942637841357015765753026454015428895509182221067548034739651629997576810486519588962549235244712491767951893009938758597566243194418165393550686768384036458801288177062129686239165626958020686678093916349056334522299329781571155355528533652367034843871226636069909406367308120405940900996466829180739702674706603385212151555652328379983307301401805433950659410002153139269627596619929566006326213386938369808800417020275110423510192739917917096754111476456802803386271573549431182473667014331006394070673572805907883306439309285102946419521971861249197803242399825221121576884144079291964686602932033742880838812898527680978574462360079227768500838425575096553800587029972821971094253813294413858661543948185039705913663539221712945770248480542541179464070039944519063538785877058373506324138125014627137626704089554631482273579597284561619613304357933180837743663724275601780408611869127637816747055185899204244299554905227313451250257608996192155367269633368527094577459870662715274988243987631499042605263214905527688724463634597682875359491510621703718274339171827654012309798585411923902855228324888563134754074430146463991053193881900676425095924640909116483822988469923767109115310664499958399069791282866085584150583918941346631890550840682867418737642769379365150876140671776819044783429159520217201578720327734485487345114197765012908061484401065510897051706172114596545305329144088421212580677064637013623608893546367915500894087692540104081842475461911673965479949889148153718140608315993199526431370203486172421943560314796760809436426585678112420105469179181122573792780369268137480217932180271702355709635739195909742657294464192942487078130428174274479402734038689414917953456758097072577258646309162050049447018362045509649026902643109567532310410365135863161423829006486242379629492429394454463168794774905820337600027735886696980925942173739497325348050075717360759296948296939740836385510806465098742489424393837170088490410452576196257176494395622677177996708810638166328606267384918825250467963100299752128862033015857251183972913334708927583947456793821220086945636375339026596302703714951849505122238537725582608528480180558361581660048600052078932765707151599757299273398203235735574776725697596498483013773163511825 := by decide +kernel
noncomputable def row0 : List Row := blockRows% "31/32/31/30/30/31/27/26/31/33/29/30/28/29/25/26/28/30/29/27/29/28/26/25/28/30/28/25/27/27/24/23|425"
theorem leaf0 : Segment system t0 t1 t2 0 32 row0 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row32 : List Row := blockRows% "28/27/30/30/30/29/32/31/28/29/33/32/32/33/30/31/27/28/29/28/29/29/29/26/27/30/30/28/29/29/29/26"
theorem leaf32 : Segment system t0 t1 t2 32 32 row32 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row64 : List Row := blockRows% "28/30/30/32/29/31/27/28/29/32/29/30/28/29/25/26/26/29/29/29/28/30/26/27/26/29/28/27/27/27/24/24"
theorem leaf64 : Segment system t0 t1 t2 64 32 row64 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row96 : List Row := blockRows% "24/25/28/28/26/27/30/30/26/27/30/32/28/29/30/31/24/26/27/28/26/28/29/28/25/28/28/30/27/29/29/28"
theorem leaf96 : Segment system t0 t1 t2 96 32 row96 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row128 : List Row := blockRows% "30/32/28/29/27/28/24/25/29/30/26/27/25/26/22/23/29/31/27/28/26/27/23/24/28/28/25|592|656/25/24/24/21|512|528|592|656|664|720|728/21|512|528|592|656|720|976"
theorem leaf128 : Segment system t0 t1 t2 128 32 row128 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row160 : List Row := blockRows% "29/30/32/33/29/31/29/30/29/30/31/32/30/30/27/28/28/31/31/31/30/32/28/29/28/31/30/29/29/29/26/26"
theorem leaf160 : Segment system t0 t1 t2 160 32 row160 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row192 : List Row := blockRows% "28/30/28/29/27/28/24/25/28/30/26/27/25/26/22/23/27/30/27/28/26/27/23/24/27|512|520/28/25/25/24|512|516|520/24|512|516|517/21|136|512|520|576|592|648|656/21|512|516|576|592|656"
theorem leaf192 : Segment system t0 t1 t2 192 32 row192 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row224 : List Row := blockRows% "25/26/29/31/25/27/29/30/27/28/30/32/28/29/27/28/25/27/28/31/27/29/28/29/26/29/29/29/28/29/26/26"
theorem leaf224 : Segment system t0 t1 t2 224 32 row224 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row256 : List Row := blockRows% "31/30/33/32/32/32/29/28/31/32/31/31/30/30/27/28/30/31/31/29/31/30/28/27/30/31/30/27/29/29/26|425/25|385|393|417|425"
theorem leaf256 : Segment system t0 t1 t2 256 32 row256 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row288 : List Row := blockRows% "26/25/29/28/30/29/33/31/26/27/31/30/30/31/32/31/27/26/30/29/31/30/31/28/27/28/32/30/31/31/31/28"
theorem leaf288 : Segment system t0 t1 t2 288 32 row288 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row320 : List Row := blockRows% "29/30/32/33/29/31/29/30/29/30/31/32/30/30/27/28/28/31/31/31/30/32/28/29/28/31/30/29/29/29/26/26"
theorem leaf320 : Segment system t0 t1 t2 320 32 row320 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row352 : List Row := blockRows% "24/25/29/28/26/27/31/30/24/25/29/30/28/29/32/32/25/26/29/29/27/28/31/30/25/26/30/31/29/30/31/30"
theorem leaf352 : Segment system t0 t1 t2 352 32 row352 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row384 : List Row := blockRows% "28/31/30/31/29/29/26/27/28/29/28/28/27/27/24/25|656/31/33/29/30/28/29/25/26/28/28/27|512,635|528|656/27|512|528|656/26/26|512/23|512|528|592|640|656,751|720/23|385|393|425|512|516|528|532|576|592|640,751|656,751,767,1007|657|720|896|897|904|912,751|913|976|977"
theorem leaf384 : Segment system t0 t1 t2 384 32 row384 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row416 : List Row := blockRows% "27/28/30/31/29/31/31/30/27/28/30/31/29/30/29/29/28/29/33/32/32/33/30/31/28/29/30/30/31/31/28/28"
theorem leaf416 : Segment system t0 t1 t2 416 32 row416 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row448 : List Row := blockRows% "26/29/29/31/28/29/26/27/26/28/28/29/27/27/24/25/29/32/29/30/28/29/25/26/29/30/27/27/26/26|512|516|517/23|512/23|512|516|528|656"
theorem leaf448 : Segment system t0 t1 t2 448 32 row448 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row480 : List Row := blockRows% "25/26/28/31/25/27/30/30/25/26/28/30/27/29/29/29/26/27/30/32/28/29/30/31/26/27/31/31/30/31/28/28"
theorem leaf480 : Segment system t0 t1 t2 480 32 row480 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row512 : List Row := blockRows% "27/29/31/31/29/30/29/28/29/31/31/31/30/30/27/28/28/31/30/29/30/30/28/27/28/30/30/29/29/30/26/27"
theorem leaf512 : Segment system t0 t1 t2 512 32 row512 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row544 : List Row := blockRows% "23/24/26/27/26/27/29/28/25/27/30/30/28/31/32/31/26/26/29/29/29/30/29/28/26/27/30/30/29/31/31/28"
theorem leaf544 : Segment system t0 t1 t2 544 32 row544 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row576 : List Row := blockRows% "25/28/30/31/25/28/28/29/27/30/30/32/29/30/27/28/26/29/29/30/28/31/28/29/26/29/29/31/28/30/26/27"
theorem leaf576 : Segment system t0 t1 t2 576 32 row576 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row608 : List Row := blockRows% "21|42|46|47|558|598|630/24/26/27/22/25/27/26/23/25/28/30/26/29/31/32/24/26/28/29/26/28/29/29/25/26/28/31/27/29/30/30"
theorem leaf608 : Segment system t0 t1 t2 608 32 row608 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row640 : List Row := blockRows% "28/31/30/31/29/29/26/27/28/29/28/28/27/27/24/25/31/33/29/30/28/29/25/26/30/30/27/28/26/27/23/24"
theorem leaf640 : Segment system t0 t1 t2 640 32 row640 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row672 : List Row := blockRows% "25/28/30/31/27/30/31/30/27/28/30/31/29/30/29/29/28/29/33/32/32/33/30/31/28/29/32/32/31/31/28/29"
theorem leaf672 : Segment system t0 t1 t2 672 32 row672 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row704 : List Row := blockRows% "26/29/29/31/26/29/26/27/26/29/28/29/27/27/24/25/29/32/29/30/28/29/25/26/29/31/27/28/26/27/23/24"
theorem leaf704 : Segment system t0 t1 t2 704 32 row704 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row736 : List Row := blockRows% "23|46|534|558|582|594|596|598,9|606|626|630|634|638/26|598/28/31/23|598/26|598/28/29/25|598/26|596|598/28/31/27/29/29/29/26/27/30/32/28/29/30/31/26/27/31/32/30/31/28/29"
theorem leaf736 : Segment system t0 t1 t2 736 32 row736 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row768 : List Row := blockRows% "27/28/31/30/29/31/31/28/29/30/30/29/29/28/28/27/30/29/33/31/33/32/30/29/29/29/30/29/30/29/28/28"
theorem leaf768 : Segment system t0 t1 t2 768 32 row768 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row800 : List Row := blockRows% "23/23/26/26/26/27/30/29/24/25/29/28/28/29/31/29/25/24/28/27/29/28/32/30/25/26/30/29/29/30/32/30"
theorem leaf800 : Segment system t0 t1 t2 800 32 row800 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row832 : List Row := blockRows% "25/28/30/31/27/30/31/30/27/28/30/31/29/30/29/29/28/29/33/32/32/33/30/31/28/29/32/32/31/31/28/29"
theorem leaf832 : Segment system t0 t1 t2 832 32 row832 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row864 : List Row := blockRows% "21/23/26/26/24/27/29/28/22/23/27/28/26/27/31/31/23/24/28/27/27/28/32/31/23/24/28/29/27/28/32/32"
theorem leaf864 : Segment system t0 t1 t2 864 32 row864 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row896 : List Row := blockRows% "26/29/29/29/28/29/28/27/26|512|528/27|528|532/27|528|592|656/26|528|592|656/26/25/25/24|656/31/32/31/31/30/30/27/28/29/28/27|528|592|656/27|528|592|656/27/26/25/25|528|656"
theorem leaf896 : Segment system t0 t1 t2 896 32 row896 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row928 : List Row := blockRows% "23/26/28/29/25/28/30/28/25/26|528|532|596/28/29/27/28/28/27/26/27/31/30/30/31/32/31/26/27/31/30/30/29/29/28"
theorem leaf928 : Segment system t0 t1 t2 928 32 row928 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row960 : List Row := blockRows% "24/27/27/30/26/29/28/28/24|512|516|528|532/27/27/28/26/27/26/26/29/30/31/32/30/30/27/28/29/30/29/29/28/28/25/26"
theorem leaf960 : Segment system t0 t1 t2 960 32 row960 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row992 : List Row := blockRows% "21|516|532|596|598/24|596|598/26/29/23/26/28/30/23|512|516,25|528|532|596/24|512,25|516,9,25|528|532,25|534|580|592|596|598/26/29/25/27|516|532/28/28/24/25/29/30/28/29/32/32/24/25|512|516,25/29/30/28/29/30/30"
theorem leaf992 : Segment system t0 t1 t2 992 32 row992 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1024 : List Row := blockRows% "29/29/30/29/31/30/28/27/30/31/30/27/31/30/28/25/27/27/27/24/28/25/25/22/27/27/25/22/28/25/23|425/20|393|425"
theorem leaf1024 : Segment system t0 t1 t2 1024 32 row1024 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1056 : List Row := blockRows% "25/24/27/27/27/26/29/28/27/26/30/29/31/30/31/28/25/25/26/25/27/26/26/23/26/27/28/25/28/26/26/23"
theorem leaf1056 : Segment system t0 t1 t2 1056 32 row1056 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1088 : List Row := blockRows% "27/27/28/29/29/29/30/29/28/31/31/29/30/31/28/27/25/27/27/26/27/27/27/24/25/28/27/24/27/27/25/22"
theorem leaf1088 : Segment system t0 t1 t2 1088 32 row1088 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1120 : List Row := blockRows% "23/22/25/25/25/24|71/27/27/25/26/29/29/27/28/31/30/23/23/24/25/25/25/26/25/24/27/27/27/26/28/28/25"
theorem leaf1120 : Segment system t0 t1 t2 1120 32 row1120 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1152 : List Row := blockRows% "31/32/31/30/30/31/27/26/31/32/29/28/28/28/25/25/28/30/28/25/29/28/26/23/27/28/26|592/23|592/26/25/23|592|720/21|592|720"
theorem leaf1152 : Segment system t0 t1 t2 1152 32 row1152 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1184 : List Row := blockRows% "28/27/30/30/30/29/32/31/28/29/33/31/32/33/30/29/27/28/29/28/29/29/29/26/27/29/29/26/28/29/27/24"
theorem leaf1184 : Segment system t0 t1 t2 1184 32 row1184 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1216 : List Row := blockRows% "28/30/31/32/29/31/27/28/29/31/29/29/28/28/25/25/26/29/29/27/28/29/26/25/26/28/26/25/26/25/23|576|592/22"
theorem leaf1216 : Segment system t0 t1 t2 1216 32 row1216 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1248 : List Row := blockRows% "24|598/25/28/28/26/27/30/30/26/27/30/32/28/29/30/30/24/26/27/28/26/28/29/28/25/28/28/28/27/29/27/26"
theorem leaf1248 : Segment system t0 t1 t2 1248 32 row1248 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1280 : List Row := blockRows% "28/27/31/30/32/31/30/29/30/29/32/29/33/32/30/27/29/28/29/26/30/27/27/24/28/28/27/24/28/27/25|425/22|385|389|393|401|417|425|512|897|913|929|976|977"
theorem leaf1280 : Segment system t0 t1 t2 1280 32 row1280 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1312 : List Row := blockRows% "23/22/26/25/27/26/30/29/25/24/28/27/29/28/32/30/24/23/27/26/28/27/28/25/26/25/29/27/29/28/28/25"
theorem leaf1312 : Segment system t0 t1 t2 1312 32 row1312 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1344 : List Row := blockRows% "28/27/30/30/30/29/32/31/28/29/33/31/32/33/30/29/27/28/29/28/29/29/29/26/27/29/29/26/28/29/27/24"
theorem leaf1344 : Segment system t0 t1 t2 1344 32 row1344 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1376 : List Row := blockRows% "23/22/26/25/25/24/28/27/23/24/28/27/27/28/32/31/24/23/26/26/26/25/28/27/24/25/29/28/28/29/30/27"
theorem leaf1376 : Segment system t0 t1 t2 1376 32 row1376 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1408 : List Row := blockRows% "31/30/33/30/32/31/29/27/29/28/29/28/29/28/26/25/29/30/28/25/29/28/26/23/25|512,635/25/24|512,619,633,635|528,635|576|592|656|720/23|512,635|528|576|592|656|720|848|976/26/25/23|512|528|576|592|656|720/21|385|393|512|516|528|532|576|592|596|640|656,751|657|720|721|832|848|896|897|912|913|976|977"
theorem leaf1408 : Segment system t0 t1 t2 1408 32 row1408 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1440 : List Row := blockRows% "26/25/29/28/30/29/32/29/26/27/30/27/30/29/31/28/27/26/30/28/30/29/29/26/27/26/27/26|592/28/28/27/24|592|596"
theorem leaf1440 : Segment system t0 t1 t2 1440 32 row1440 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1472 : List Row := blockRows% "29/30/32/32/30/31/29/28/28/28/30/29/29/28/26/25/28/30/30/27/29/29/27/25/27/27/26/25/26/25|517/23|512/22|512|516|576|592"
theorem leaf1472 : Segment system t0 t1 t2 1472 32 row1472 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1504 : List Row := blockRows% "24/25/29/28/26/27/31/29/24/25/29/29/28/29/31/30/25/26/29/29/27/28/31/28/25/26/29/28/28/28/27/26"
theorem leaf1504 : Segment system t0 t1 t2 1504 32 row1504 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1536 : List Row := blockRows% "28/27/31/30/32/31/30/29/30/29/33/31/33/32/30/29/29/28/29/26/30/27/27/24/29/29/29/26/30/27/27/24"
theorem leaf1536 : Segment system t0 t1 t2 1536 32 row1536 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1568 : List Row := blockRows% "23|598/22/26/25/27/26/30/29/25/24/28/27/29/28/32/30/24/23/27/26/28/27/28/25/26/25/29/27/30/28/28/25"
theorem leaf1568 : Segment system t0 t1 t2 1568 32 row1568 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1600 : List Row := blockRows% "28/27/30/30/30/29/32/31/28/29/33/32/32/33/30/31/27/28/29/28/29/29/29/26/27/30/30/28/29/29/29/26"
theorem leaf1600 : Segment system t0 t1 t2 1600 32 row1600 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1632 : List Row := blockRows% "23|46|47|367|582|598,9|614|626|630/22|598/26/25/25|598/24|598|599/28/27/23/24/28/27/27/28/32/31/24/23/26/26/26/25/28/27/24/25/29/28/28/29/30/27"
theorem leaf1632 : Segment system t0 t1 t2 1632 32 row1632 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1664 : List Row := blockRows% "31/30/33/32/32/32/29/28/31/32/31/31/30/30/27/28/30/31/31/29/31/30/28/27/30/31/30/27/29/29/26/25"
theorem leaf1664 : Segment system t0 t1 t2 1664 32 row1664 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1696 : List Row := blockRows% "26/25/29/28/30/29/33/31/26/27/31/30/30/31/32/31/27/26/30/29/31/30/31/28/27/28/32/30/31/31/31/28"
theorem leaf1696 : Segment system t0 t1 t2 1696 32 row1696 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1728 : List Row := blockRows% "29/30/32/33/29/31/29/30/29/30/31/32/30/30/27/28/28/31/31/31/30/32/28/29/28/31/30/29/29/29/26/26"
theorem leaf1728 : Segment system t0 t1 t2 1728 32 row1728 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1760 : List Row := blockRows% "24|582,9|594|596|598,9,25|606|626|630,9|638/25|598,9/29/28/26|598/27|598/31/30/24|594|596|598/25|598/29/30/28/29/32/32/25/26/29/29/27/28/31/30/25/26/30/31/29/30/31/30"
theorem leaf1760 : Segment system t0 t1 t2 1760 32 row1760 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1792 : List Row := blockRows% "26/25/29/28/30/29/32/29/28/27/31/29/32/31/31/28/27/26/30/28/31/29/29/26/28/28/29/26/31/29/29/26"
theorem leaf1792 : Segment system t0 t1 t2 1792 32 row1792 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1824 : List Row := blockRows% "21/20|598/24/23/25/24/28/27/23/22/26/25/27/26/30/29/22/21/25/24/26/25/29/27/24/23/27/26/28/27/30/27"
theorem leaf1824 : Segment system t0 t1 t2 1824 32 row1824 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1856 : List Row := blockRows% "26/25/29/28/30/29/33/31/26/27/31/30/30/31/32/31/27/26/30/29/31/30/31/28/27/28/32/30/31/31/31/28"
theorem leaf1856 : Segment system t0 t1 t2 1856 32 row1856 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1888 : List Row := blockRows% "21|598/20|598|599/24/23/25/24/28/27/21/22/26/25/25/26/30/29/22/21/25/24/26/25/29/28/22/23/27/26/26/27/31/29"
theorem leaf1888 : Segment system t0 t1 t2 1888 32 row1888 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1920 : List Row := blockRows% "29/28/32/30/31/31/31/28/29/30/30/29/29/28/28/27/30/29/33/31/33/32/30/29/28/27/28|528|592/27|592/30/29/28/27"
theorem leaf1920 : Segment system t0 t1 t2 1920 32 row1920 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1952 : List Row := blockRows% "24/23/27/26/28/27/31/29/24/25/29/28/28/29/31/29/25/24/28/27/29/28/32/30/25/26/30/28|592/29/28/32/29"
theorem leaf1952 : Segment system t0 t1 t2 1952 32 row1952 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1984 : List Row := blockRows% "27/28/30/31/29/31/31/30/27/28/30/31/29/30/29/29/28/29/33/32/32/33/30/31/28/29/30/30/31/31/28/28"
theorem leaf1984 : Segment system t0 t1 t2 1984 32 row1984 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row2016 : List Row := blockRows% "22|596|598|630/23|598/27/26/26/27/31/30/22|516|532|592|596|598/23|516,25|532|534|596|598|599/27/28/26/27/31/31/23/24/28/27/27/28/32/31/23|512/24|516/28/29/27/28/32/32"
theorem leaf2016 : Segment system t0 t1 t2 2016 32 row2016 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
end Quadric.Five.Census.Block.Case11
