import Quadric.Five.Intervals
import Quadric.Five.Resources.System06

namespace Quadric.Five.Census.Block.Case06
set_option maxRecDepth 16384
set_option maxHeartbeats 24000000
set_option Elab.async false
private theorem cachedMinimum : packList system.lowFirst=447977197985421205760539039488504355823168939011701284578517172337500737896221529091602204746050325940869706748933026985474056051778882623508796760842755968124346122876213857772527582651143675105662265904594035474436637574266630324300797847581745775393277930670285107418416241170708907794505522408459092610909127375144755116405017219913932170886800093068385560333024519698942172129945811183393871419559825205437220764285464612491602728624230267304175885266343184720136524278346667217648924133828070736533915430988884232914652580461518833317638868228101448008439357390400134489080908078678659920228444755294717051088000742175766585896178669003058777861447759246763330394406166909525774790718661088707279437319611264469441538231810706220156907995866582263356823561380775806411700063410008357902108466365589212420204585844291011520907341170313241731929666752077980486193410257548072976365093587110537765341746043281979434390081494284026070854638444428858994769118475937278485262644568177023177471515806606401326581304917300982108880507049415089001414551602649994644507408757327062937168933026630813673088979938489436029250153223563881010929148115659534625385593536413628846396773102733729141405177803126678373051497998352154050463563092454293810479174349933322932686605853136564607637010560612455907616563129427392334803113997891107526551719650994483226244089258101625231881578786454100234727632615176033739183502766645019440641476497465475451602785071918024894324761651141632610226981017866721161983262677529286761286762278824357455743756626680924667609002592933710343039141039097432429478803667103189325459907850802256841240353914181628207725960053518077013589084359197139437184985556711357960712925092771483672280478708634667324863923782992993946965104875523962924925639393563694938051008940992949682049092264234678915770013187271530431680649493430315107254447979978469276461354461909117149065200658428926497895237010905266287129513599361810813269480482480028458681656304278307379183228780024869375270367600453410794389953196153215108533192117998410751360390707305394566527034276722027631056780762544360370399482919303018428107658962119726184849940982462971999950113394823923837397202620844117832146185611209265925959625696746953015432614104151380056747085735651363317438884758395891893182172533468651389139733944662519077350001718784847998391442498057017833047536873026563722940932046755620521067820598316458756514001756596522249130976279019184848599871229289340884365439676401220149386986631748799148938371232416842046343989334175669581493407042342169526185852861130362676592534284086915864541901714064850938720170266345245488060347126613002248344403798568656022620177148041902621442647714537902212124141296764492812800200109553179455556526985652620790296242936830403547214030095915355744223895109118575255699754152880759647401240742464501675961817888977987633845126397145307768687316537797868492257626710305823586408219925223789902344609815315644885096454870640459171116757121611558662282757097824668596759973135170456054311443036603772294809499501435185409915432600714137843725 := by decide +kernel
noncomputable def row0 : List Row := blockRows% "28/25/28/28/25/25/24|208/27/28/25/31/28/29/27/28/30/26/24/25|168|424,450|426,450|488|490/26/24/24/23/26/27/24/29/27/28/26/29/28"
theorem leaf0 : Segment system t0 t1 t2 0 32 row0 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row32 : List Row := blockRows% "29/26/29/29/28/26/27/29/29/26/32/29/31/28/31/31/27/25/26/28/25/25/24/27/28/25/31/28/30/27/30/30"
theorem leaf32 : Segment system t0 t1 t2 32 32 row32 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row64 : List Row := blockRows% "28/27/28/30/24/27/25/28/30/29/30/32/28/28/28/31/25/26/25|424,450|426,450/27/23/26/23/26/27/28/30/30/27/28/28/30"
theorem leaf64 : Segment system t0 t1 t2 64 32 row64 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row96 : List Row := blockRows% "30/28/28/29/27/28/27/28/31/30/29/31/30/30/27/30/26/26/26/28/25/26/24/27/28/28/29/30/28/28/28/30"
theorem leaf96 : Segment system t0 t1 t2 96 32 row96 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row128 : List Row := blockRows% "28/28/29|208/31/26/27/25|144|208,646,662|216|400|464|720/28/28/27/31/31/28/27/27|208,646,662|720/30/28/27/30/29/26/27/26|208/29/28/27/32|728/30/28/28/28/31"
theorem leaf128 : Segment system t0 t1 t2 128 32 row128 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row160 : List Row := blockRows% "32/29/30/31/30/29/28/29/30/29/30/31/30/30/28/31/29/28/30/31/29/28/28/30/29/28/31/31/31/30/29/32"
theorem leaf160 : Segment system t0 t1 t2 160 32 row160 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row192 : List Row := blockRows% "28/29/27/30/25/27/25|208/28/30/29/27/30/28/27/25/28/26/27/28/30/24/27/25/29/28/29/28/31/28/28/26/29"
theorem leaf192 : Segment system t0 t1 t2 192 32 row192 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row224 : List Row := blockRows% "29/30/26/29/27/30/24/27/29/31/26/29/27/30/24/27/27/27/27/29/27/27/25/28/29/29/27/30/28/29/25/28"
theorem leaf224 : Segment system t0 t1 t2 224 32 row224 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row256 : List Row := blockRows% "28/25/30/28/27/27/26/29/28/25/31/28/29/27/30/30/27/24/27/27/26/26/25/28/27/24/30/27/29/26/31/29"
theorem leaf256 : Segment system t0 t1 t2 256 32 row256 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row288 : List Row := blockRows% "29/26/30/29/30/28/29/30/29/26/31/29/31/28/31/30/28/25/28/28/27/27/26/29/28/25/31/28/30/27/31/30"
theorem leaf288 : Segment system t0 t1 t2 288 32 row288 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row320 : List Row := blockRows% "30/29/29/30/26/29/27/29/30/29/30/32/30/30/28/31/28/28/27/29/25/28/25/28/29/28/31/31/29/30/29/32"
theorem leaf320 : Segment system t0 t1 t2 320 32 row320 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row352 : List Row := blockRows% "31/30/28/29/29/30/27/28/31/30/29/31/30/32/27/30/29/28/27/28/27/28/26/28/30/29/29/30/31/30/28/30"
theorem leaf352 : Segment system t0 t1 t2 352 32 row352 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row384 : List Row := blockRows% "29/28/31/31/29/29/29/30/28/27/30/30/28/27|917/29/30/30/27/32/30/28/29/29/31/28/27/32/30/29/28/30/32"
theorem leaf384 : Segment system t0 t1 t2 384 32 row384 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row416 : List Row := blockRows% "32/29/30/31/31/31/28/29/30/29/30/29/30/30/28/29/31/28/30/31/31/30/29/30/29/28/31/30/31/30/29/32"
theorem leaf416 : Segment system t0 t1 t2 416 32 row416 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row448 : List Row := blockRows% "30/31/27/30/27/29/25/28/30/29/27/30/28/29/25/28/30/30/28/31/26/30/26/29/30/29/28/31/29/30/26/29"
theorem leaf448 : Segment system t0 t1 t2 448 32 row448 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row480 : List Row := blockRows% "29/31/26/29/27/29/24/27/29/29/26/29/27/29/24/27/30/29/27/29/28/29/25/28/30/30/27/30/28/31/25/28"
theorem leaf480 : Segment system t0 t1 t2 480 32 row480 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row512 : List Row := blockRows% "29/27/30/30/27/29/26/29/30/27/29/29/30/29/28/29/28/26/27/29/26/28/25/28/29/26/31/29/31/28/29/31"
theorem leaf512 : Segment system t0 t1 t2 512 32 row512 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row544 : List Row := blockRows% "30/28/28/29/30/30/27/28/31/28/29/28/31/30/29/28/29/27/27/28/27/29/26/28/30/27/29/30/32/29/29/30"
theorem leaf544 : Segment system t0 t1 t2 544 32 row544 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row576 : List Row := blockRows% "30/31/28/29/26/31/26/27/31/31/28/31/29/32/26/29/28/30/27/29/25/29/25/28/31/30/29/31/29/32/27/30"
theorem leaf576 : Segment system t0 t1 t2 576 32 row576 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row608 : List Row := blockRows% "30/31/26/27/28/30/25/26/30/31/27/29/28/30/25/28/29/30/25|106,994|234,994/26/27/30/25/26/30/31/27/28/29/32/26/28"
theorem leaf608 : Segment system t0 t1 t2 608 32 row608 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row640 : List Row := blockRows% "29/30/29/30/29/30/27|208/28/27/28/28/28/27/28/27/28/32/29/30/31/28/31/27/29/30/29/30/32/30/30/28/31"
theorem leaf640 : Segment system t0 t1 t2 640 32 row640 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row672 : List Row := blockRows% "30/31/28/29/29/31/26/27/28/28/28/27/28/29/26/27/32/30/28/29/29/32/27/28/31/30/29/30/30/31/27/30"
theorem leaf672 : Segment system t0 t1 t2 672 32 row672 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row704 : List Row := blockRows% "28/31/25/28/26/29/23/26/28/29/25/28/26/29/23/26/29/32/26/29/26/30/24/27/29/31/26/29/27/30/24/27"
theorem leaf704 : Segment system t0 t1 t2 704 32 row704 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row736 : List Row := blockRows% "27/29/24/27/25/27/22/25/27/28/24/27/25/27/22/25/28/31/25/27/26/29/23/26/28/30/25/28/26/29/23/26"
theorem leaf736 : Segment system t0 t1 t2 736 32 row736 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row768 : List Row := blockRows% "27/26/28/27/28/27/27/27/28/27/26/25/28/28/26/25/28/26/29/29/28/28/27/30/29/26/30/29/31/28/29/30"
theorem leaf768 : Segment system t0 t1 t2 768 32 row768 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row800 : List Row := blockRows% "28/27/27/26/29/29/27/26/28/26/25/24/28/27/25/24/29/27/27/27/29/29/27/28/30/27/27/27/32/29/29/29"
theorem leaf800 : Segment system t0 t1 t2 800 32 row800 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row832 : List Row := blockRows% "30/30/28/29/28/31/26/27/29/28/28/27/29/30/26/27/30/30/28/29/27/31/27/28/31/30/29/31/30/32/27/30"
theorem leaf832 : Segment system t0 t1 t2 832 32 row832 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row864 : List Row := blockRows% "29/29/26/26/27/28/25/25/27/27/26/26/27/28/25/26/30/29/25/26/29/30/25/26/29/27/27/27/29/31/26/28"
theorem leaf864 : Segment system t0 t1 t2 864 32 row864 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row896 : List Row := blockRows% "29/29/27/26/29/29/27/26/26/25/25/24/26/27/25|208|400,948,950|720/24|144|208|400,948,950|404|464|720|912|976/32/29/30/31/30/31/28/29/30/29/28|720|728|984/29/30/30/28/29"
theorem leaf896 : Segment system t0 t1 t2 896 32 row896 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row928 : List Row := blockRows% "28/28/26/25/28/28/26/25/25/24/24/23/25/26/24/23|208|720/31/30/28/28/30/32/27/28/29/28/27/28/29/30/27/28"
theorem leaf928 : Segment system t0 t1 t2 928 32 row928 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row960 : List Row := blockRows% "28/29/25/28/26/28/23/26/26/25/25/26/26/27/23/26/29/32/26/29/27/30/24/27/29/30/26/29/27/30/24/27"
theorem leaf960 : Segment system t0 t1 t2 960 32 row960 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row992 : List Row := blockRows% "26/27/24/26/24/25/22/24/24/24/23/24/24/25/22/24/28/29/25/27/26/28/23/26/27/26/25/27/26/28/23/26"
theorem leaf992 : Segment system t0 t1 t2 992 32 row992 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1024 : List Row := blockRows% "25/22/27/25/25/22/25/25/25/22/28/25/27/24/29/27/23/21/24/23/23/21/23/23/24/21/26/24/25/23/26/25"
theorem leaf1024 : Segment system t0 t1 t2 1024 32 row1024 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1056 : List Row := blockRows% "26/23/29/26/26/23/28/26/26/23/29/26/28/25/31/28/25/22/26/25/25/22/24/25/25/22/28/25/27/24/28/27"
theorem leaf1056 : Segment system t0 t1 t2 1056 32 row1056 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1088 : List Row := blockRows% "27/24/28/27/27/24|295/27/27/29/26/31/29/29/26/31/29/24/23/25/24/24/23/23/24/26/25/28/27/26/25/27/27"
theorem leaf1088 : Segment system t0 t1 t2 1088 32 row1088 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1120 : List Row := blockRows% "28/25|295|303/27/28/28/25|39|71,1,65|87|103,1,65|295|303|327|359|367|583/27/28/30/27/29/29/30/27/29/30/25/23|303/26|106/25/25/23|71/24/25/27/26/28/28/27/26/28/28"
theorem leaf1120 : Segment system t0 t1 t2 1120 32 row1120 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1152 : List Row := blockRows% "28/25/30/28/27/25/26/28/28/25/31/28/29/27/28/30/26/24/27/26/26/24/26/26/27/24/29/27/28/26/29/28"
theorem leaf1152 : Segment system t0 t1 t2 1152 32 row1152 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1184 : List Row := blockRows% "29/26/30/29/29/26/29/29/29/26/31/26/31/28/30/30/28/25/29/28/28/25/27/28/28/25/30/27/30/27/30/29"
theorem leaf1184 : Segment system t0 t1 t2 1184 32 row1184 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1216 : List Row := blockRows% "30/27/30/30/28/27/28/29/30/29/30/31/29/28/28/30/25/26/28/27/25/26/26/27/27/28/30/30/27/28/29/30"
theorem leaf1216 : Segment system t0 t1 t2 1216 32 row1216 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1248 : List Row := blockRows% "30/28/28/29/30/28/27/28/31/28/29/28/30/30/27/30/26/26/27/27/26/26/27/27/28/27/28/27/28/28/28/27"
theorem leaf1248 : Segment system t0 t1 t2 1248 32 row1248 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1280 : List Row := blockRows% "25/22/28/25/27/24/29/27/25/22/28/25/27/24/30/27/24/21/27/24/26/23/26/26/24/21|257|289|769,17|773|785,17|801|833|849|977/27/24/26/23/29/26"
theorem leaf1280 : Segment system t0 t1 t2 1280 32 row1280 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1312 : List Row := blockRows% "26/23|295/29/26/28/25/29/28/26/23/29/25/28/25/31/28/25/22/28/25/27/24/27/27/25/22/28/25/27/24/30/27"
theorem leaf1312 : Segment system t0 t1 t2 1312 32 row1312 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1344 : List Row := blockRows% "29/26/28/29/29/26/28/29/29/26/32/28/31/28/31/31/28/25/27/27/27/25/26/27/28/25/30/28/30/27/30/29"
theorem leaf1344 : Segment system t0 t1 t2 1344 32 row1344 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1376 : List Row := blockRows% "30/27/27/28/30/27|295/27/28/30/26/29/27/32/29/29/30/28/25/26/26/28/25/26/26/29/26/28/28/30/28/28/28"
theorem leaf1376 : Segment system t0 t1 t2 1376 32 row1376 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1408 : List Row := blockRows% "28/25/31/28/30/27/30/30/28/25/31/27/29/27/31/30/27/24/30/27/29/26/30/29/27/24|769,17|785,17/30/27/29/26/32/29"
theorem leaf1408 : Segment system t0 t1 t2 1408 32 row1408 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1440 : List Row := blockRows% "29/26/30/28/31/28/29/30/29/25/29/24/31/28/31/28/28/25/29/28/30/27/29/30/28/25/30/25/30/27/31/29"
theorem leaf1440 : Segment system t0 t1 t2 1440 32 row1440 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1472 : List Row := blockRows% "32/29/30/31/31/29/28/29/30/28/30/29/31/30/28/31/29/28/30/30/29/28/29/30/29/28/31/30/31/30/29/32"
theorem leaf1472 : Segment system t0 t1 t2 1472 32 row1472 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1504 : List Row := blockRows% "31/28/28/29/30/30/27/28/30/27/29/26/30/30/27/30/29/27/27/28/29/28/27/28/30/27/29/27/31/29/28/29"
theorem leaf1504 : Segment system t0 t1 t2 1504 32 row1504 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1536 : List Row := blockRows% "27/24/30/27/29/26/29/29/27/24/30/27/29/26/30/29/26/23/28/26/27/25/26/28/26/23/29/26/28/25/31/28"
theorem leaf1536 : Segment system t0 t1 t2 1536 32 row1536 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1568 : List Row := blockRows% "28/25/27/28/30/27/27/28/28/25/29/25/30/27/29/29/27/24/26/27/28/26/26/27/27/24/28/26/29/26/28/29"
theorem leaf1568 : Segment system t0 t1 t2 1568 32 row1568 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1600 : List Row := blockRows% "31/28/28/29/30/28/27/28/31/28/30/30/32/30/29/30/29/27/27/28/27/27/26/28/30/27/29/30/32/29/29/30"
theorem leaf1600 : Segment system t0 t1 t2 1600 32 row1600 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1632 : List Row := blockRows% "30/29/25|106/26/30/29|295/25/26/32/28/27/27/31/31/27/28/29/27/24|42|98|106,994|110|234,994|362|618/25/28/27/24|106/25/31/28/26/27/31/30/26/27"
theorem leaf1632 : Segment system t0 t1 t2 1632 32 row1632 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1664 : List Row := blockRows% "30/27/30/30/31/29/28/29/30/27/29/27/30/29/29/29/29/26/30/29/31/28/29/30/29/26/32/28/31/28/31/31"
theorem leaf1664 : Segment system t0 t1 t2 1664 32 row1664 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1696 : List Row := blockRows% "31/28/28/28/32/30/27/28/30/25/29/24/31/29/29/28/30/27/27/28/32/29/27/28/30/26/29/25/32/29/29/29"
theorem leaf1696 : Segment system t0 t1 t2 1696 32 row1696 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1728 : List Row := blockRows% "31/31/28/29/29/31/26/27/31/29/28/29/29/31/26/29/31/30/28/29/30/30/27/28/31/30/29/30/30/32/27/30"
theorem leaf1728 : Segment system t0 t1 t2 1728 32 row1728 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1760 : List Row := blockRows% "30/30/26/27/28/30/25/26/30/27/27/26/28/30/25/28/30/29/25/26/29/30/25/26/30/27/27/27/29/31/26/28"
theorem leaf1760 : Segment system t0 t1 t2 1760 32 row1760 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1792 : List Row := blockRows% "27/24/29/27/29/26/29/28/27/24/27/26/29/26/27/26/26/23/29/26/28/25/28/28/26/23/29/26/28/25/31/28"
theorem leaf1792 : Segment system t0 t1 t2 1792 32 row1792 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1824 : List Row := blockRows% "28/25/26/25/30/27|295/27/27/28/24/25/23/29/27/26/25/27/24/26/26/29/26/26/27/27/24/26/24/29/26/28/27"
theorem leaf1824 : Segment system t0 t1 t2 1824 32 row1824 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1856 : List Row := blockRows% "31/28/28/29/31/30/27/28/31/27/29/28/32/30/29/28/30/27/27/28/29/29/27/28/30/27/29/29/32/29/29/30"
theorem leaf1856 : Segment system t0 t1 t2 1856 32 row1856 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1888 : List Row := blockRows% "29/27|295/25/25/29/28|39|295,352,353,480,481|303|359/25/25/29/26/26/25/30/30/27/27/29/26/24/25/29/28|295/24/25/29/26|815/26/25/31/30/26/27"
theorem leaf1888 : Segment system t0 t1 t2 1888 32 row1888 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1920 : List Row := blockRows% "30/27/28/27/31/29/28/27/29/26/26/25/29/28/26/25/29/26/30/29/31/28/29/30/29/26/30/26/31/28/30/30"
theorem leaf1920 : Segment system t0 t1 t2 1920 32 row1920 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1952 : List Row := blockRows% "30/27/27/26/30/29/27/26/28/23/25/22/28/27/25/24/30/27/27/27/32/29/27/28/29/24|592,561|593,561/27/23|592,561|593,561|720|848|976/32/28/29/27"
theorem leaf1952 : Segment system t0 t1 t2 1952 32 row1952 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row1984 : List Row := blockRows% "31/30/28/29/29/31/26/27/29/27/28/27/29/29/26/27/32/30/28/29/30/32/27/28/31/29/29/28/30/32/27/30"
theorem leaf1984 : Segment system t0 t1 t2 1984 32 row1984 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
noncomputable def row2016 : List Row := blockRows% "29/29/26/26/27/28/25/25/27/25/26/24/27/28/25/26/30/29/25/26/29/30/25/26/28/25/27/25/29/29/26/28"
theorem leaf2016 : Segment system t0 t1 t2 2016 32 row2016 := by
  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel
end Quadric.Five.Census.Block.Case06
