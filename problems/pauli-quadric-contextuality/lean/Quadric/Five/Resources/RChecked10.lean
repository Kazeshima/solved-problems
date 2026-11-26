import Quadric.Five.Intervals
import Quadric.Five.Resources.System10

namespace Quadric.Five.Census.Block.Case10
set_option maxRecDepth 16384
set_option maxHeartbeats 24000000
set_option Elab.async false
private theorem cachedMinimum : packList system.lowFirst=447909964427329084715056420873365652670090616637173860491240708460731440790381217606297566278202249599957080779083139770512520626604895604914741237559426499734877943496492417280884167495722807523638808969724233194193105647990570604310201085775729451574331308607800107576101544866811645198322688360529205911816455949147566946527720600642000996499077289271629801542041409433850273464619115464534898404876726444209469100453661765233602965053074314170401314016879009911118530189910116531574823493305095169534894368650266707783979773990585703391048153227931237534259518743943782146057000742169675215800568005727586671938187637055600869233437306755002334133624618302754545196214888540732359160965936700040932905912532422544282820241676205974003719762197519200627750099630650436688367779400449208556353403244236325574001525504511116900612364338202138159502156851960517280154979828807164832674299328798440250432589027584644319411364530403567335084814951269626786027259129177895457122776834507650433916447290295375931407202601064374840465601034567681597626758134286258205917409393273502541562528060891536828471065215727988867186440375790448818249625803403730054860495318732016366729620650935873837800895537217254085346934764787713204354244940407992301601120611011686968513807119707655540388877744292214217862062332996651097704682446533589416358866907020360610230572356963302601775806466276588113978815930151430407324895516739130882164596241446024878330491458368618949828358730276990453623606591561734831168456680066869887064489501138619916063026244622641791609372918496163634872617745330771207167310219263782835097531157125936552646210261814642165885036443358034404098478776836281801763594497227251843274472749875819136229420806204164099254324199552545736459252244423881132312204429324812086826793602262512665134371731794324238511838810657625790761253269473625498609177533290609980600594668421342252781882849233626672504813610567800611377814136904611611465395111115266476515549816416893478610154393961766993801384089536883099036093451015585065701623130636634467299135109448539551133611073405066374979354662784672189242425377806239855559161395705129081885396593071887203262427937242011979905028080525549980675174860736656585543736752012770279904385155225948471255761202130075726820473939034614388590206484429519395692353522378537292346046407493229583950719076469064726004474120502926361728728428595616064988482537772403657626180551533344877413707405986706299146474916653584245240543327939479466509135199606477732844035306220398084234492440217074519995164941574954306055536464168295354566160965477575433610732855974740612527427020436969328915166628734824852007920528083956873914355186460504848992134947214259259992422954025690537485774798905100080482448894476977374319559938003147837378311454194694270551869389916848437067551835456785163116276044642906141940753541334773495783685158093322277031377566789825227981209752616364895182407502458546450900302472951342646237521318488247091363484110641157331424502320890887855785108863116041009537633418965124436647871855973198285311149325085414797325 := by decide +kernel
noncomputable def row0 : List Row := blockRows% "28/26/29/28/26/26/25|80|208,646/28/29/26/31/29/29/28/29/30/27/26/28/27/27/26/27/27/26/27/28/27/26/27/27/27"
theorem leaf0 : Segment system t0 t1 t2 0 32 row0 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row32 : List Row := blockRows% "28/25/30/28/28/25/26/28/28/25/31/28/30/27/32/30/28/26/28/28/28/26/28/28/29/26/29/28/29/28/29/28"
theorem leaf32 : Segment system t0 t1 t2 32 32 row32 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row64 : List Row := blockRows% "27/26/29/28/25|64|431,462/26|431/25/28/25/26/28/29/25/26/26/29/24/25/27/26/24/25/25/26/22|8|520,75/23/25/26/22/23/25/26"
theorem leaf64 : Segment system t0 t1 t2 64 32 row64 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row96 : List Row := blockRows% "28/25/30/28/28/25|70|71,1|431/26/28/28/27/31/30/28/27/30/30/27/26/28/28/27/26/28/28/25/26/28/28/25/26/28/28"
theorem leaf96 : Segment system t0 t1 t2 96 32 row96 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row128 : List Row := blockRows% "27/27/26|80|208,646/29/25|64|80|208,646/26/22|64|80,646|82|84|88|128|144,646|192,646|208,134,518,642,644,646,647,654,662,678,710,902|209,646|210,646|212,646|216,646|240,646|464,646|592|720,646/25|80|208,646/27/26/31/30/26|80|208/26/27|80|208,646/30/27/27/29/28/27/27/25|80|208,646/28/25|520,75|536|576|592|600/26/28|592/29/25/26/27|208/29"
theorem leaf128 : Segment system t0 t1 t2 128 32 row128 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row160 : List Row := blockRows% "29/26/27/29/26/26/23|80|208,646/26/27/26/32/29/28/27/29/31/29/27/30/29/29/27/26/29/28/27/31/30/28/29/30/31"
theorem leaf160 : Segment system t0 t1 t2 160 32 row160 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row192 : List Row := blockRows% "25|64|80/26/25|80/29/22|64|66|68|80|208/24/21|64|80|192|208,646|212/25/24|8|64|80|520,75|536|576|592|600/25/27/28/22|64|80|520|592/24/23|80|208/27/23|8|64|72|520,75|576|584|600/24/26/27/23/24/22/27/21|0|8,75|40|64|72|80|88|136|512,75|520,11,67,73,74,75,79,91,107,203,331,587|521,75|522,75|524,75|528|536,75|552,75|576|584,75|586|592|600|616|648,75|664|728|776,75|808|904/22|520,75|576/24|8|64|72|80|520,75|536|576|584|592|600/25/21|8|64|520,75|576/22/23/25"
theorem leaf192 : Segment system t0 t1 t2 192 32 row192 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row224 : List Row := blockRows% "27/26/27/29/24/25/23/26/27/26/30/31/26/25/26/30/26/27/29/29/26/27/25/29/24|520,75|576|584|600/25/27/28/24/25/27/28"
theorem leaf224 : Segment system t0 t1 t2 224 32 row224 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row256 : List Row := blockRows% "29/26/31/29/30/28/29/30/29/26/32/29/30/28|385/31/31/30/27/29/29/31/29/28/29/30/27/28/27/30/29/28/27|385,483"
theorem leaf256 : Segment system t0 t1 t2 256 32 row256 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row288 : List Row := blockRows% "28/25/31/28/30/27/29/30/28/25/31/27/30/27/32/30/29/26/28/28/31/28/28/29/29/25/29/26/31/28/29/28"
theorem leaf288 : Segment system t0 t1 t2 288 32 row288 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row320 : List Row := blockRows% "31/28/31/31/27/28/28/30/29/28/31/31/27/29/28/32/28/29/29/29/28/29/28/29/26/27/28/27/26/27/28/27"
theorem leaf320 : Segment system t0 t1 t2 320 32 row320 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row352 : List Row := blockRows% "30/27/31/30/30/27/30/30/28/27/32/30/30/29/30/32/31/28/28/29/31/28/28/29/29/28/29/28/29/29/29/28"
theorem leaf352 : Segment system t0 t1 t2 352 32 row352 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row384 : List Row := blockRows% "29/27/30/30/29/28/26|80|208,646/29/27/26/32/30/27/26|385|389|401|405|913|917,29/30/31/31/28/31/31/31/30/29/30/29/28/31/31/29/29/29/32"
theorem leaf384 : Segment system t0 t1 t2 384 32 row384 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row416 : List Row := blockRows% "29/26/31/29/29/28/27/30/27/26/32/29/28/27/31/31/30/27/31/29/32/29/30/31/28/27/32/29/30/29/30/32"
theorem leaf416 : Segment system t0 t1 t2 416 32 row416 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row448 : List Row := blockRows% "29/28/29/32/26/26/25/29/27/26/30/31/26/26/27/31/27/28/29/31/27/28/26/30/25|520,75/26/28/29/25/26/27/29"
theorem leaf448 : Segment system t0 t1 t2 448 32 row448 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row480 : List Row := blockRows% "29/28/31/31/28/27/27/30/27/26/31/31/28/27/29/32/30/29/30/32/30/29/28/31/28/27/30/31/28/28/28/31"
theorem leaf480 : Segment system t0 t1 t2 480 32 row480 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row512 : List Row := blockRows% "31/28/29/30/30/30/27/28/31/28/31/31/31/30/29/30/32/29/27/28/31/31/26/27/32/29/29/29/31/31/28/29"
theorem leaf512 : Segment system t0 t1 t2 512 32 row512 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row544 : List Row := blockRows% "30/27/29/29/31/29/27/28/30/27/31/29/32/29/30/31/31/28/26/27/31/30/26/27/31/27/28/28/32/30/28/29"
theorem leaf544 : Segment system t0 t1 t2 544 32 row544 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row576 : List Row := blockRows% "31/30/29/30/27/30/26/28/31/30/29/32/27/31/27/30/30/31/27/28/28/31/26/27/28/29/28/29/28/29/26/29"
theorem leaf576 : Segment system t0 t1 t2 576 32 row576 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row608 : List Row := blockRows% "32/29/29/30/30/29/28/29/30/29/30/32/31/31/28/31/31/30/26|106,994/27/30/30/26/27/31/30/28/29/30/31/27/29"
theorem leaf608 : Segment system t0 t1 t2 608 32 row608 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row640 : List Row := blockRows% "28/29/28/30/27/29/24|80|208,646/27/29/28/30/32/29/28/28/31/32/30/29/30/29/32/27/28/31/30/29|592/32/30/31/27/30"
theorem leaf640 : Segment system t0 t1 t2 640 32 row640 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row672 : List Row := blockRows% "27/28/29/29/27/28/25/28/29/28/31/30/29/29/29/32/32/29/29/29/31/31/28/29/30/29/30/29/31/31/28/31"
theorem leaf672 : Segment system t0 t1 t2 672 32 row672 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row704 : List Row := blockRows% "28/29/27/31/24/28/23/27/29/28/28/31/26/28/25/29/29/30/27/30/25/30/24/28/27|520,75|536|600/28/27|600/30/27/28/25/28"
theorem leaf704 : Segment system t0 t1 t2 704 32 row704 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row736 : List Row := blockRows% "27|106|638,540/28/29/31/26/28/25/28/29/28/29/32/29/29/27/30/31/31/28/30/28/31/26/29/30/29/28/31/29/30/26/29"
theorem leaf736 : Segment system t0 t1 t2 736 32 row736 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row768 : List Row := blockRows% "31/28/28/28/31/30/27/28/31/28/29/30/32/30/29/30/32/29/27/28/31/31/26/27/30/27/27/28/31/31/28/29"
theorem leaf768 : Segment system t0 t1 t2 768 32 row768 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row800 : List Row := blockRows% "29/27/26/25/29/28/26/25/30/26/28/27/31/29/28/27/31/27/26/26/31/30/26/27/29/25/26/26/32/29/28/29"
theorem leaf800 : Segment system t0 t1 t2 800 32 row800 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row832 : List Row := blockRows% "32/30/29/30/29/32/27/28/31/30/29/32/29/31/27/30/31/31/27/28/29/32/26/27/30/27/28/29/29/31/26/29"
theorem leaf832 : Segment system t0 t1 t2 832 32 row832 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row864 : List Row := blockRows% "32/29/29/29/31/31/28/29/30/29/30/31/31/31/28/31/31/30/26/27/30/32/26/27/29/26/28/29/30/30/27/29"
theorem leaf864 : Segment system t0 t1 t2 864 32 row864 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row896 : List Row := blockRows% "28/29/29/29/28/29/28/29/29/28/28|592/31/29/28/28/31/32/30/29/30/30/32/27/28/30/30/27|80|208|520|528|536|576|592|600|656|720|952,1022/30|592/30/31/27|592/30"
theorem leaf896 : Segment system t0 t1 t2 896 32 row896 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row928 : List Row := blockRows% "27/28/27/26/27/28/27/26/29/28/29/28/29/29/29/28/32/28/29/27/31/31/28/29/30/28/28|592/27|80|592,561/31/31/28/31"
theorem leaf928 : Segment system t0 t1 t2 928 32 row928 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row960 : List Row := blockRows% "28/29/28/31/26/29/25/29/29/28/28/31/28/28/26/29/30/32/27/30/27/31/25/28/30/29/27|520|592/30/28/31/25/28"
theorem leaf960 : Segment system t0 t1 t2 960 32 row960 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row992 : List Row := blockRows% "27/28/29/30/27/28/27/30/29/28/29/31/29/29/27/30/31/31/28/30/29/32/26/29/30/29/28/30/29/31/26/29"
theorem leaf992 : Segment system t0 t1 t2 992 32 row992 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1024 : List Row := blockRows% "27/25/28/27/27/25/28/27/28/25/28/27/29/27/28/27/26/25/25/24/26/25/25/24/26/25/23/22/26/25/23|64/22|64|80|208|385,483"
theorem leaf1024 : Segment system t0 t1 t2 1024 32 row1024 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1056 : List Row := blockRows% "27/24/28/27/27/24|71,1|487/28/27/27/24/29/26/29/26/29/28/27/25/25/25/27/25/25/25/27/24/24/23/27/26/24/23|64"
theorem leaf1056 : Segment system t0 t1 t2 1056 32 row1056 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1088 : List Row := blockRows% "27/25/28/27/27/25|71,1/26/27/26/27/28/27/26/27/27/27/25/24/25/24/25/24/24/24/23/24/23|64/22/23/24/23/22|64"
theorem leaf1088 : Segment system t0 t1 t2 1088 32 row1088 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1120 : List Row := blockRows% "27/24|70|71,1/28/27/27|70|71,1/24|7,1|66|67,1|68|69,1|70,1|71,0,1,3,5,9,17,33,65,129,257,513|79,1|86|87,1|102|103,1|111|119|199,1|215|231|263|295|303|327,1|359|367|423|431|455|487|495|503|583,1/28/27|70|71,1/29/26/29/28/29/26|71,1/29/28/27/25/25|66|106,994/25/27/25|71,1/25/25|71/26/26/24/23|64/26/26/24/23|64|66"
theorem leaf1120 : Segment system t0 t1 t2 1120 32 row1120 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1152 : List Row := blockRows% "28/26/29/28/28/26/25|80|208,646/28/29/26/31/29/29/28/30/30/27/26/28/27/27/26/27/27/26/27/28|592/27/26/27/27/27"
theorem leaf1152 : Segment system t0 t1 t2 1152 32 row1152 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1184 : List Row := blockRows% "28/25/30/28/28/25/26/28/28/25/31/28/30/27/32/30/28/26/28/28/28/26/28/28/29/26/29/28/29/28/29/28"
theorem leaf1184 : Segment system t0 t1 t2 1184 32 row1184 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1216 : List Row := blockRows% "27/26/29/28/27/26/25/28/25/26/28/29/25/26/27/29/24/25/27/26/24/25/25/26/22|64|520,75|576|584|592|600/23/25|64|592/26/22/23/25/26"
theorem leaf1216 : Segment system t0 t1 t2 1216 32 row1216 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1248 : List Row := blockRows% "28/25/30/28/28/25|70|71,1/26/28/28/27/31/30/28/27/30/30/27/26/28/28/27/26/28/28/25/26/28/28/25/26/28/28"
theorem leaf1248 : Segment system t0 t1 t2 1248 32 row1248 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1280 : List Row := blockRows% "28/25/29/28/30/27/28/29/28/25/28/27/30/27|385/28/27|385,483/28/26/25/24/28/27/25/24|385,483/26/24/23/22|385,483/26/25|385,483/23|385,483/22|64|65|80|81|129,483|192|193|208|209|257,483|321|384,483|385,227,355,419,451,481,482,483,487,491,499,995|387,483|389,483|393,483|401,483|405|417,483|448|449,483|464|465|469|592|721|897,483|905|913|917|977|981"
theorem leaf1280 : Segment system t0 t1 t2 1280 32 row1280 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1312 : List Row := blockRows% "27/24/28/26/29/26/28/29/27/23/29/24/29/26/29/28/28/24/25/25/29/27/25/25/27/22/24/23/27/26/24/23|64|65|80|385,483"
theorem leaf1312 : Segment system t0 t1 t2 1312 32 row1312 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1344 : List Row := blockRows% "30/27/29/29/29/27/28/29/30/27/28/27/30/29/28/27/28/27/25/24/27/27/25/24/26/25/23/22/26/25/23/22|385,483"
theorem leaf1344 : Segment system t0 t1 t2 1344 32 row1344 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1376 : List Row := blockRows% "29/26/28/29/29/26|71,1/28/29/29/26/29/28/31/28/29/28/29/27/25/25/29/27/25/25/27/25/24/23/27/26/24/23|64"
theorem leaf1376 : Segment system t0 t1 t2 1376 32 row1376 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1408 : List Row := blockRows% "29/26/31/29/31/28/29/30/29/26/32/29/30/28/31/31/30/27/29/29/31/29/28/29/30/27/28|592/27|592/30/29/28/27|80|208|385,483|592|720"
theorem leaf1408 : Segment system t0 t1 t2 1408 32 row1408 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1440 : List Row := blockRows% "28/25/31/27/30/27/29/30/28/25/31/27/30/27/32/30/29/26/28/26/31/28/28/28/29/25/29/26|80|576|592,561/31/28/29/28|592"
theorem leaf1440 : Segment system t0 t1 t2 1440 32 row1440 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1472 : List Row := blockRows% "31/28/31/31/29/28/28/30/29/28/31/31/29/29/29/32/28/29/29/29/28/29/28/29/26/27/28/27/26/27/28/27"
theorem leaf1472 : Segment system t0 t1 t2 1472 32 row1472 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1504 : List Row := blockRows% "30/27/31/30/30/27/30/30/28/27/32/30/30/29/30/32/31/28/28/28/31/28/28/28/29/28/29/28/29/29/29/28"
theorem leaf1504 : Segment system t0 t1 t2 1504 32 row1504 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1536 : List Row := blockRows% "30/27/27/28/31/29/26/27/30/27/29/29/32/29/28/29/29/28/24/25/29/29/24/25/28/26/25/24/28/27/25/24"
theorem leaf1536 : Segment system t0 t1 t2 1536 32 row1536 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1568 : List Row := blockRows% "29/26/26/26/31/28/26/27/29/25/28/26/31/28/28/29/28/26/23|66|80|98|106,994|114/24/28/29/23/24/29/24/25/25/29/28/25/25"
theorem leaf1568 : Segment system t0 t1 t2 1568 32 row1568 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1600 : List Row := blockRows% "31/29/27/28/29/29/26/27/32/29/29/29/30/31/28/29/29/29/24|66|106,994/25/28/29/24/25/28/27/25/24/28/27/25/24"
theorem leaf1600 : Segment system t0 t1 t2 1600 32 row1600 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1632 : List Row := blockRows% "31/28/26|66|98|106,994|110|114|118/27/31/28|70|71,1/26/27/31/28/28/29/32/30/28/29/28|106,994|110|618|622/29/23|42,994|64|66|70|74,994|80|82|90|96|98,994|102|104,994|106,482,738,866,930,962,992,994,995,998,1002,1010|107,994|110,994|111|112|114|118|122,994|126|234,994|362,994|366|578|586|602|610|618,994|622|626|630|634|638/24|66|98|106,994|110/28/29/23|66|98|106,994|110/24|66|70|71/29/27/25|66|106,994|618/25|66/29/28/25/25"
theorem leaf1632 : Segment system t0 t1 t2 1632 32 row1632 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1664 : List Row := blockRows% "31/28/29/30/30/30/27/28/31/28/31/31/32/30/29/30/32/29/27|80/28/31/31/26/27/32/29/29|592/29/31/31/28/29"
theorem leaf1664 : Segment system t0 t1 t2 1664 32 row1664 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1696 : List Row := blockRows% "30/27/29/27/31/29/27/28/30/27/31/27/32/29/30/31/31/27/26|80|592/26/31/30/26/27/31/27/28|80|592/26|80|592,561/32/30/28/28"
theorem leaf1696 : Segment system t0 t1 t2 1696 32 row1696 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1728 : List Row := blockRows% "31/30/29/30/27/30/26/28/31/30/29/32/29/31/27/30/30/31/27/28/28/31/26/27/28/29/28/29/28/29/26/29"
theorem leaf1728 : Segment system t0 t1 t2 1728 32 row1728 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1760 : List Row := blockRows% "32/29/29/30/30/29/28/29/30/29/30/31/31/31/28/31/31/30/26|66|80|106,994|618|634|638/27/30/30/26/27/31/30/28|592/28|592/30/31/27/28"
theorem leaf1760 : Segment system t0 t1 t2 1760 32 row1760 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1792 : List Row := blockRows% "30/26/27/27/31/29/26/27/29/24/27/25/32/28/28/29/29/25/24/25/29/29/24/25/27/22/24|592/23|80|592/28/26/25/24|80|385,483"
theorem leaf1792 : Segment system t0 t1 t2 1792 32 row1792 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1824 : List Row := blockRows% "27/23/24/22/28/27/25/24|487|503,948/26/21/26/22/30/25/27/26/27/22/23/21|64|80|592/28/26/23/24/25/20|592/23|80|592/21|64|66|80|576|592,561|593|594|624/29/24/25/24|64|80|592"
theorem leaf1824 : Segment system t0 t1 t2 1824 32 row1824 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1856 : List Row := blockRows% "32/29/27/28/31/31/26/27/30/27/29/28/31/31/28/29/29/28/24/25/29/29/24/25/27/24/25/24/28/27/25/24"
theorem leaf1856 : Segment system t0 t1 t2 1856 32 row1856 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1888 : List Row := blockRows% "31/27/26/26/31/30/26/27/29/25/28/26/32/29/28/29/28/26/23|66|98|106,994|618/24/28/29/23/24/26/23|815,377/25/24|64|66|80|576|592/29/27/25/25"
theorem leaf1888 : Segment system t0 t1 t2 1888 32 row1888 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1920 : List Row := blockRows% "31/28/28/28/31/30/27/28/31/28/29/30/32/30/29/30/32/29/27|592/28/31/31/26/27/30/27/27|80|528|576|592|600|720/27|80|528|576|592,561|720/31/31/28/29|592"
theorem leaf1920 : Segment system t0 t1 t2 1920 32 row1920 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1952 : List Row := blockRows% "29/26/26/25/29/28/26/25|80/30/26/28/25|80|592,561/31/29/28/27|80|592/30/25/26|80|592/24|80|592,561/31/29/26/27/29/25|576|592,561/26|64|80|576|592,561|600|624/24|64|80,561|81|82|112|208|512|528,561|576,561|578|592,49,529,545,560,561,563,565,569,625,689,817|593,561|594,561|596,561|600,561|624,561|720,561|848,561/32/29/28/27|64|80|592,561"
theorem leaf1952 : Segment system t0 t1 t2 1952 32 row1952 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1984 : List Row := blockRows% "32/30/29/30/29/32/27/28/31/30/29/32/30/31/27/30/31/31/27/28/29/32/26/27/30/27/28/29/29/31/26/29"
theorem leaf1984 : Segment system t0 t1 t2 1984 32 row1984 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row2016 : List Row := blockRows% "32/29/29/29/31/31/28/29/30/29/30/29/31/31/28/31/31/29/26/27/30/32/26/27/29/26|576|592/28|592/27|64|80|576|592,561/30/30/27/28"
theorem leaf2016 : Segment system t0 t1 t2 2016 32 row2016 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
end Quadric.Five.Census.Block.Case10
