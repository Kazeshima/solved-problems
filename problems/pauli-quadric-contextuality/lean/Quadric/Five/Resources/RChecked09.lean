import Quadric.Five.Intervals
import Quadric.Five.Resources.System09

namespace Quadric.Five.Census.Block.Case09
set_option maxRecDepth 16384
set_option maxHeartbeats 24000000
set_option Elab.async false
private theorem cachedMinimum : packList system.lowFirst=551281560090206154119861883453409204973504504310310065406457524404818388103093285381355385993885836002530533254314212172553944112910149353908262933026367799635837945284815128544685120147816053794977692629561962131321107485022647087888186446440751999769072311700321616519796101113560015672213839943798303523777123039471347637057775181210193371912298403491841038472989861653890331863881102762893859325861752380749960406580923435785317254239275267453395162967162981630859109828733933074547065903143052215653032212600650260077927507769886931496354180023008554355789388620243286849692900471751658258214576888933531165050353652935575612961566926080624014776431518516463082864238698526189629672843340333539903660577372427421474198327557948195994153968570973361510226196005105579401376838201854107785205588462393716719249116518555708882130678820828875128025086222999042948191121194544059915298442856467898559784469063715898317507446690848716969406243898190827496458211349707839122525620215530963833894486950919818895640624507898185641938295750452007873002369576632984040270236092459985526107665643521329577197473717992994881955686189107468004284539298597544588668927581678048860254054528491826263863587121969213210189264411567707272491722776279523743335257327734783218903952099632626288771374079361776403474515391058418723855829257245662483805224090755858398334486743477193450202773276729431010805280765655188217345917838618588331429237143765365888233183743042541924643139577510080322516853739416026325361308021299940551553985665147554983463111554084639481139113471280928086625416927068109886578294529953452607992191930984961363004286418698039498935285662601733140921777046394347251389060063982414299912322013817098258496804504944276864458913700554641011847528859126636965465314446251151689427752161874309668042247702328493944754213718162084675917324131217045463064985948291532963520874971120596539246884652788238562687974356433116046717516374482864239951418382427992314601734475674444003962414150550554735703991859346496810363780226816693722329750201171475253521981919181525675517731419976051363365377995119042652537364339173045444857735759487314471696555378655494891125914257182503892954108532095515820240373567045763903048941734954128005589085380376051955277833440675659941804323337062999473576926271094037095607414059199222028709024047721128637076286495546654529069539200823700955999985054217175727224126366405051945411426706434646686898816547982490762488994120680001410407030755123044977620298242115192346104762043490407418617335578298357493146701810143823682795002169163250807316389919474601336368370023595108212787547596833663954187242387750712937295579688273808952999944692635679989246548485718907913397210978148712107588756818021410864987868929973057378086051172328074064266285054339330559420685432767443342297356446176432466635576133735863468871379271258372041802660106490976448036692705743875808215673143135281437590017343027956116918762568378178139439068597075754424031865096735662198614441874107653987044043782525400201825822428912168677791428966426440742701184833620566621200 := by decide +kernel
noncomputable def row0 : List Row := blockRows% "28/28/29/30/30/30/29/28/29/30/32/32/31/33/29/28/26/27/27/27/28/28/28/25/26/29/29/27/28/28/28/25"
theorem leaf0 : Segment system t0 t1 t2 0 32 row0 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row32 : List Row := blockRows% "26/25/28/28/28/27/30/30/28/27/31/30/32/31/32/31/26/26/27/28/28/28/29/28/27/28/30/28/29/31/29/26"
theorem leaf32 : Segment system t0 t1 t2 32 32 row32 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row64 : List Row := blockRows% "26/26/27/28/27/28/29/29/27/30/30/32/29/31/29/30/24/26/26/27/26/28/28/27/24/27/27/29/26/29/28/27"
theorem leaf64 : Segment system t0 t1 t2 64 32 row64 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row96 : List Row := blockRows% "24/23/26/26/26/25|431/28/28/26/27/30/30/28/29/31/32/24/24/25/26/26/26/27/28/25/28/28/30/27/30/30/28"
theorem leaf96 : Segment system t0 t1 t2 96 32 row96 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row128 : List Row := blockRows% "30/31/32/31/30/32/28/27/30/32/30/31/29/30/26/27/27/30/30/30/29/31/27/26/27|512|520/30/29/28/28/28/25/25"
theorem leaf128 : Segment system t0 t1 t2 128 32 row128 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row160 : List Row := blockRows% "27/28/30/31/29/30/29/29/27/29/30/31/29/31/29/30/28/29/30/31/30/31/30/29/28/31/31/29/30/31/28/27"
theorem leaf160 : Segment system t0 t1 t2 160 32 row160 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row192 : List Row := blockRows% "26/28/29/31/26/28/28/29/28/30/30/31/28/30/26/27/25|520/28/28/30/27/30/27/28/25|512,75|520,75,91,587,603|536|552|576|584|592|600|648|776|904/28/28/29/27/28/25/25"
theorem leaf192 : Segment system t0 t1 t2 192 32 row192 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row224 : List Row := blockRows% "25/26/28/29/25/27/27/27/25/27/28/30/27/29/29/30/25/27/28/29/27/29/30/30/26|520/29/29/31/28/31/28/28"
theorem leaf224 : Segment system t0 t1 t2 224 32 row224 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row256 : List Row := blockRows% "29/28/32/31/33/32/29/28/31/30/33/31/32/32/29/28/30/29/30/27/31/28/28/25/30/30/30/27/31/28/28/25|385,483|393,483|417|425|897|905"
theorem leaf256 : Segment system t0 t1 t2 256 32 row256 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row288 : List Row := blockRows% "26/25/29/28/30/29/31/29/28/27/31/30/32/31/32/29/27/26/30/29/31/30/30/28/29/28/31/28/33/31/29/26"
theorem leaf288 : Segment system t0 t1 t2 288 32 row288 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row320 : List Row := blockRows% "29/28/31/31/29/30/31/30/29/30/33/33/32/32/29/30/28/29/30/29/30/30/30/27/28/31/31/29/30/30/28/27"
theorem leaf320 : Segment system t0 t1 t2 320 32 row320 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row352 : List Row := blockRows% "26/25/29/28/28/27/29/28/26/27/31/30/30/31/32/31/27/26/29/29/29/28/31/30/27/28/32/30/31/32/31/28"
theorem leaf352 : Segment system t0 t1 t2 352 32 row352 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row384 : List Row := blockRows% "30/31/32/31/31/31/28/27/30/31/30/30/29/29/26/27/31/32/31/30/30/31/27/26/31/32/29|592|904/28|512|528|592|904,1011/28/28/25/25|385|393|512|528|592|656|720|896|897|904|905|912"
theorem leaf384 : Segment system t0 t1 t2 384 32 row384 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row416 : List Row := blockRows% "27/28/30/30/29/31/31/28/27/29/30/30/29/30/29/28/30/29/33/31/33/33/30/29/30/31/32/29/31/31/28/27"
theorem leaf416 : Segment system t0 t1 t2 416 32 row416 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row448 : List Row := blockRows% "28/30/31/33/28/30/28/29/28/30/30/31/29/29/26/27/29/32/31/32/30/31/27/28/29/32/29/29/28/28/25/25"
theorem leaf448 : Segment system t0 t1 t2 448 32 row448 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row480 : List Row := blockRows% "25/28/28/31/27/29/30/28/25/27/28/30/27/29/29/29/28/29/32/32/30/31/30/31/28/29/31/31/31/31/28/28"
theorem leaf480 : Segment system t0 t1 t2 480 32 row480 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row512 : List Row := blockRows% "28/28/31/31/31/30/29/28/31/30/33/31/32/32/29/28/30/29/29/27/30/28/27/25/30/30/30/27/31/28/28/25"
theorem leaf512 : Segment system t0 t1 t2 512 32 row512 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row544 : List Row := blockRows% "25/25/28/28/29/29/31/29/28/27/31/30/32/31/32/29/27/26/30/29/31/30/30/28/29/28/32/30/33/31/30/28"
theorem leaf544 : Segment system t0 t1 t2 544 32 row544 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row576 : List Row := blockRows% "27/28/31/31/27/28/29/29/29/30/33/33/31/32/29/30/28/29/30/29/30/30/29/27/28/31/31/29/30/30/28/27"
theorem leaf576 : Segment system t0 t1 t2 576 32 row576 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row608 : List Row := blockRows% "25/25/28/28/26/27/29/28/26/27/31/30/30/31/32/31/27/26/29/29/29/28/31/30/27/28/32/31/31/32/31/30"
theorem leaf608 : Segment system t0 t1 t2 608 32 row608 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row640 : List Row := blockRows% "28/31/32/31/30/31/28/27/30/31/30/30/29/29/26/27/31/32/31/30/30/31/27/26/31/32/29/30/28/29/25/26"
theorem leaf640 : Segment system t0 t1 t2 640 32 row640 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row672 : List Row := blockRows% "27/28/30/30/29/31/31/28/27/30/30/30/29/30/29/28/30/29/33/32/33/33/30/29/30/31/32/31/31/31/28/29"
theorem leaf672 : Segment system t0 t1 t2 672 32 row672 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row704 : List Row := blockRows% "26/29/31/33/26/29/28/29/28/30/30/31/29/29/26/27/29/32/31/32/30/31/27/28/29/32/29/30/28/29/25/26"
theorem leaf704 : Segment system t0 t1 t2 704 32 row704 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row736 : List Row := blockRows% "25|598|606|630|638/28/28/31/25|598/28|598/30/28/25/28/28/31/27/30/29/29/28/29/32/32/30/31/30/31/28/29/32/33/31/31/28/29"
theorem leaf736 : Segment system t0 t1 t2 736 32 row736 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row768 : List Row := blockRows% "26/27/29/28/29/28/29/26/29/30/30/27/29/28/28/25/29/29/29/27/30/28/27/25/28/27/29/27/30/28/28/25"
theorem leaf768 : Segment system t0 t1 t2 768 32 row768 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row800 : List Row := blockRows% "23/24/26/27/27/28/28/25/27/27/30/27/30/28/28/25/26/26/29/28/30/29/30/28/28/28/29/26/31/29/29/26"
theorem leaf800 : Segment system t0 t1 t2 800 32 row800 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row832 : List Row := blockRows% "25/27/29/30/27/28/30/28/27/30/32/30/29/30/29/28/29/29/31/29/31/30/29/27/29/29/32/29/31/30/28/27"
theorem leaf832 : Segment system t0 t1 t2 832 32 row832 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row864 : List Row := blockRows% "23/24/26/27/26/27/29/27/25/27/29/29/28/30/30/27/26/26/29/29/30/30/32/30/27/28/32/30/31/32/31/30"
theorem leaf864 : Segment system t0 t1 t2 864 32 row864 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row896 : List Row := blockRows% "28/30/30/27/30/28/28/25/28/27|528/27|528|592/26|528|592/26/25/25/24|528|592/32/32/31/29/30/30/27/26/29/28/27|512|528|592|936|952/27|512|528|592/27/26/25/25|592"
theorem leaf896 : Segment system t0 t1 t2 896 32 row896 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row928 : List Row := blockRows% "27/28/29/26/29/27/27/24/27/28/28/26|592/27/26/26/24|592|596/30/29/32/29/32/30/30/27/29/29/29/27|528|592/28/27/27/26"
theorem leaf928 : Segment system t0 t1 t2 928 32 row928 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row960 : List Row := blockRows% "26/29/31/29/28/29/28/27/28/29/29/28/28/27/26/26/31/32/31/32/30/30/27/28/31/30/29/29/28/28/25/26"
theorem leaf960 : Segment system t0 t1 t2 960 32 row960 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row992 : List Row := blockRows% "25/28/28/28/27/29/29/26/25/28/28/28/27/27|596/27/26/28/29/33/31/32/31/30/29/28/29/31/30/30/29/28/28"
theorem leaf992 : Segment system t0 t1 t2 992 32 row992 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1024 : List Row := blockRows% "25/25/26/27/27/27/28/27/28/27/29/29/30/30/30/27/23/24/24|425/24/25/25/25/22/25/26/26/24/27/25/25/22|385"
theorem leaf1024 : Segment system t0 t1 t2 1024 32 row1024 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1056 : List Row := blockRows% "23/22/25/25/25/24/27/27/25/24/28/27/29/28/31/28/23/23/24/25/25/25/26/25/26/25/27/25/28/28/26/23"
theorem leaf1056 : Segment system t0 t1 t2 1056 32 row1056 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1088 : List Row := blockRows% "23/23/24/25/25/25/26/27/26/27/28/29/28/29/30/29/22/23/23/24/24/25/25/24/23/26/26/26/25/27/27/24"
theorem leaf1088 : Segment system t0 t1 t2 1088 32 row1088 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1120 : List Row := blockRows% "21/20/23/23/23|70|71,1,9|87|431|598/22|7|39|69|70|71,1,9|86|87,1|103|119|295|327|423|431|582|583|598|599/25/25/25/24/27/27/27/26/29/29/21|618/21/22|618/23/23/23|71/24/25/24/25/26/27/26/27/28/25"
theorem leaf1120 : Segment system t0 t1 t2 1120 32 row1120 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1152 : List Row := blockRows% "28/28/29/30/30/30/29/27/29/30/31/28/31/30/28/25/26/27/27|592/25/28/26/26/23/26|576|592/28/26|576|592|600/23|576|592/27/26/24|592/21|576|592"
theorem leaf1152 : Segment system t0 t1 t2 1152 32 row1152 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1184 : List Row := blockRows% "26/25/28/28/28/27/30/29/28/27/29/28/31/31/30/27/26/26/27/26/28/28/27/24/27/28/27|592/24|576|592/29/27/25/22|592"
theorem leaf1184 : Segment system t0 t1 t2 1184 32 row1184 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1216 : List Row := blockRows% "26/26/27/28/27/28/29/28/27/30/30/30/29/30/28/27/24|576/26/26/27/26/28/28/25/24|512,75|520,75|576|584|592/27/27|576|592/25/26/27/25/23"
theorem leaf1216 : Segment system t0 t1 t2 1216 32 row1216 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1248 : List Row := blockRows% "24|598/23/26/26/26/25|598/28/28/26/27/29/28/28/29/31/29/24|576/24/25/26/26/26/27/26/25|520|576,537|584|592/28/28/26/27/29/27/24|576|592"
theorem leaf1248 : Segment system t0 t1 t2 1248 32 row1248 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1280 : List Row := blockRows% "26/25/29/28/30/29/30/27/28/27/31/29/32/30/30/27/27/26/27/24/28/25/25/22|385|417|425/29/27/27/24|385|425/28/25|385/25|385|425/22|257|384|385,483,499,995,1011|389|393,483|401|417|421|425|449|576|592|769|896|897|905|929|937"
theorem leaf1280 : Segment system t0 t1 t2 1280 32 row1280 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1312 : List Row := blockRows% "23/22/26/25/27/26/30/29/25/24/28/27/29/28/31/28/24/23/27/26/28/27/28/25/26/25/28/25/30/28/26/23|385"
theorem leaf1312 : Segment system t0 t1 t2 1312 32 row1312 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1344 : List Row := blockRows% "26/25/28/28/28/27/30/29/28/27/31/30/32/31/32/29/26/26/27/26/28/27/27/24/27/28/29/26/29/27/27/24"
theorem leaf1344 : Segment system t0 t1 t2 1344 32 row1344 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1376 : List Row := blockRows% "23/22/26/25/25/24/28/27/25/24/28/27/29/28/32/30/24/23/26/26/26/25/28/27/26/25/29/27/30/29/28/25"
theorem leaf1376 : Segment system t0 t1 t2 1376 32 row1376 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1408 : List Row := blockRows% "29/28/32/31/33/32/29/28/31/30/33/30/32/32/29/27/30/29/30/27/31/28/28/25/29/29/28|512,635|528|576|592/25|512|528|576|592/29/28/26|592/23|385|512|528|576|592|720|897"
theorem leaf1408 : Segment system t0 t1 t2 1408 32 row1408 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1440 : List Row := blockRows% "26/25/29/28/30/29/32/29/28/27/29/27/31/30/32/28/27/26/30/28/31/30/29/26/29/27/29|592/26|576,561|592,561/31/29/27/24|576|592"
theorem leaf1440 : Segment system t0 t1 t2 1440 32 row1440 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1472 : List Row := blockRows% "29/28/31/31/30/30/31/30/29/30/33/32/32/32/29/29/28/29/30/29/30/30/30/27/28/30/30/27/29/29/27/25"
theorem leaf1472 : Segment system t0 t1 t2 1472 32 row1472 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1504 : List Row := blockRows% "26/25/29/28/28/27/31/29/26/27/29/28/29/30/32/30/27/26/29/29/29/28/31/28/27/28/30/28/31/31/29/26"
theorem leaf1504 : Segment system t0 t1 t2 1504 32 row1504 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1536 : List Row := blockRows% "26/25/29/28/30/29/29/27/28/27/31/29/32/30/30/27/27/26/27/24/28/25/25/22/29/27/27/24/28/25/25/22"
theorem leaf1536 : Segment system t0 t1 t2 1536 32 row1536 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1568 : List Row := blockRows% "23|630/22/26/25/27/26/30/29/25/24/28/27/29/28/32/30/24/23/27/26/28/27/28/25/26/25/29/27/30/28/28/25"
theorem leaf1568 : Segment system t0 t1 t2 1568 32 row1568 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1600 : List Row := blockRows% "26/25/28/28/28/27/30/29/28/27/31/30/32/31/32/29/26/26/27/26/28/27/27/24/27/28/29/26/29/27/27/24"
theorem leaf1600 : Segment system t0 t1 t2 1600 32 row1600 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1632 : List Row := blockRows% "23|118|598|618|622|630|638/22|598|630/26/25/25|86|119|598|630/24|70|71,1|86|87,1|119|295|598|599/28/27/25/24/28/27/29/28/32/31/24|618/23/26/26/26/25/28/27/26/25/29/28/30/29/30/27"
theorem leaf1632 : Segment system t0 t1 t2 1632 32 row1632 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1664 : List Row := blockRows% "29/28/32/31/33/32/29/28/31/30/33/31/32/32/29/28/30/29/30/27/31/28/28/25/29/29/30/27/29/28/28/25"
theorem leaf1664 : Segment system t0 t1 t2 1664 32 row1664 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1696 : List Row := blockRows% "26/25/29/28/30/29/32/29/28/27/31/29/32/31/32/29/27/26/30/29/31/30/30/28/29/28/31/28/32/31/29/26"
theorem leaf1696 : Segment system t0 t1 t2 1696 32 row1696 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1728 : List Row := blockRows% "29/28/31/31/29/30/31/30/29/30/33/33/32/32/29/30/28/29/30/29/30/30/30/27/28/30/30/29/29/30/28/27"
theorem leaf1728 : Segment system t0 t1 t2 1728 32 row1728 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1760 : List Row := blockRows% "26|594|598,9|606|630|638/25|598/29/28/28|598/27|598/31/29/26|598/27/31/30/30/31/32/31/27/26/29/29/29/28/31/30/27/28/32/30/31/32/31/28"
theorem leaf1760 : Segment system t0 t1 t2 1760 32 row1760 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1792 : List Row := blockRows% "26/25/29/28/30/28/29/27/28/27/30/27/32/29/29/26/27/26/27/24/28/25/25/22/27/24/27/24|592/28/25/25/22|385"
theorem leaf1792 : Segment system t0 t1 t2 1792 32 row1792 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1824 : List Row := blockRows% "23/22/26/25/27/26/29/26/25/24/28/26/29/28/29/26/24/23/27/26/28/27/28/25/26/25/28/24|576|592/30/27/28/24"
theorem leaf1824 : Segment system t0 t1 t2 1824 32 row1824 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1856 : List Row := blockRows% "26/25/29/28/30/29/31/29/28/27/31/30/32/31/32/29/27/26/29/26/30/27/27/24/29/28/29/26/30/27/27/24"
theorem leaf1856 : Segment system t0 t1 t2 1856 32 row1856 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1888 : List Row := blockRows% "23/22/26/25/27/26/30/28/25/24/28/27/29/28/31/28/24/23/27/26/28/27/30/27/26/25/29/28/30/29/30/27"
theorem leaf1888 : Segment system t0 t1 t2 1888 32 row1888 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1920 : List Row := blockRows% "29/28/31/28/32/29/29/26/31/29/30/27/29/28/28/25/30/28/30/27/31/28/28/25/28/27/28|528|576|592/25|512|528|576|592|848/30/28/28/25|592"
theorem leaf1920 : Segment system t0 t1 t2 1920 32 row1920 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1952 : List Row := blockRows% "26/25/29/27/30/28/28/25/28/27/30/27|592/30/28/28/25|592/27/26/30/28/31/29/30/28/29/27/29|592,561,569/25|512|528|576,561|592,561,569|594|596|848/31/28/29/25|592"
theorem leaf1952 : Segment system t0 t1 t2 1952 32 row1952 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1984 : List Row := blockRows% "29/28/32/30/31/31/31/28/29/30/32/30/31/30/29/28/30/29/32/29/33/30/30/27/30/29/32/29/31/30/28/27"
theorem leaf1984 : Segment system t0 t1 t2 1984 32 row1984 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row2016 : List Row := blockRows% "26/25/29/28/30/29/30/27/26/27/31/29/30/30/30/27/27/26/30/29/31/30/32/30/27/28/31/28|592/31/31/31/28"
theorem leaf2016 : Segment system t0 t1 t2 2016 32 row2016 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
end Quadric.Five.Census.Block.Case09
