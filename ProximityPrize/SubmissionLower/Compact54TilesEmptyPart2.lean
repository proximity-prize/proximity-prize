import ProximityPrize.SubmissionLower.Compact54EmptyTilt

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableEmpty
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks apply_batches)
open Compact54Packed (unpack)

namespace Top3
private abbrev P := PaidBatch .empty 3
private def cross0 : P := ⟨unpack [55953597941], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross1 : P := ⟨unpack [30518686741], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross2 : P := ⟨unpack [17935905925], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross3 : P := ⟨unpack [30955681085], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross4 : P := ⟨unpack [22181005445], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross5 : P := ⟨unpack [35268086065], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross6 : P := ⟨unpack [47732773917], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross7 : P := ⟨unpack [35049988245], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross8 : P := ⟨unpack [12904455693], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross9 : P := ⟨unpack [17853410621], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross10 : P := ⟨unpack [17384041953], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross11 : P := ⟨unpack [21947384125], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross12 : P := ⟨unpack [17585439153], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross13 : P := ⟨unpack [60752954413], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross14 : P := ⟨unpack [34849064133], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross15 : P := ⟨unpack [13290477885], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross16 : P := ⟨unpack [26175318213], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross17 : P := ⟨unpack [17451297065], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross18 : P := ⟨unpack [30789124161], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross19 : P := ⟨unpack [13089291561], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross20 : P := ⟨unpack [8693661021], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross21 : P := ⟨unpack [25990972657], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross22 : P := ⟨unpack [8743996713], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def p9_0 : List P := [
  ⟨unpack [13287957517,14496572529], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross0]
private def bs9 : List P := p9_0
private theorem row9 : checks (tilesOf bs9) 132 9 4 = true := by decide +kernel
private def p13_0 : List P := [
  cross1,
  cross2,
  cross3,
  cross0]
private def bs13 : List P := p13_0
private theorem row13 : checks (tilesOf bs13) 132 13 4 = true := by decide +kernel
private def p17_0 : List P := [
  cross1,
  cross2,
  cross4,
  cross5,
  cross3,
  cross0]
private def bs17 : List P := p17_0
private theorem row17 : checks (tilesOf bs17) 132 17 4 = true := by decide +kernel
private def p21_0 : List P := [
  cross6,
  cross4,
  cross7,
  cross5,
  cross0,
  cross8]
private def bs21 : List P := p21_0
private theorem row21 : checks (tilesOf bs21) 132 21 4 = true := by decide +kernel
private def p25_0 : List P := [
  cross6,
  cross7,
  cross5,
  cross9,
  cross10,
  cross8]
private def bs25 : List P := p25_0
private theorem row25 : checks (tilesOf bs25) 132 25 4 = true := by decide +kernel
private def p29_0 : List P := [
  cross6,
  cross7,
  cross9,
  cross11,
  cross12,
  cross10]
private def bs29 : List P := p29_0
private theorem row29 : checks (tilesOf bs29) 132 29 4 = true := by decide +kernel
private def p33_0 : List P := [
  cross13,
  cross14,
  cross11,
  cross12]
private def bs33 : List P := p33_0
private theorem row33 : checks (tilesOf bs33) 132 33 4 = true := by decide +kernel
private def p37_0 : List P := [
  cross13,
  cross14,
  cross11,
  cross15,
  ⟨unpack [8878135713,4700607921,4465794537], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs37 : List P := p37_0
private theorem row37 : checks (tilesOf bs37) 132 37 4 = true := by decide +kernel
private def p41_0 : List P := [
  cross13,
  cross14,
  cross16,
  cross17,
  cross15,
  ⟨unpack [8794253677,8760763809,170832289,4432242125,103722445,53391821,3060189,3060193], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3060196,36613609,3060200,3060204,137274865,86944241,3060208,3059189], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3060212,3059193,3060216,3059196,3125756,3059200,3125760,3059204], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p41_1 : List P := [
  ⟨unpack [3125764,19835401,3059208,3125768,3059212,3125772,3058193,19901968], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs41 : List P := p41_0 ++ p41_1
private theorem row41 : checks (tilesOf bs41) 132 41 4 = true := by decide +kernel
private def p45_0 : List P := [
  cross13,
  cross18,
  cross16,
  cross17,
  cross19,
  cross20,
  ⟨unpack [4482577773,4365139321,86949261,36618637,3064217,120501661,86948253,3064221], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3064224,19840421,3064228,3129769,3063212,3129772,3063216,3129776], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p45_1 : List P := [
  ⟨unpack [19839413,3063220,3129780,3063224,3129784,36615613,19839420,3129788], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3062208,19905984,3062212,19905988,3061193,3062216,19905992,3061197], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3062220,19905996,19838416,19906000,3061204,36682196,3061208,36682200], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3061212,36682204,3061216,19904992,149775541108728918558360034,3061220,19904996,151124297458934226095161830], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [36681192,152473053809139533631963626,36681196,153821810159344841168765422,19903984,149209144979846764616990194,155170566509550148705567218,19903988], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [150501301403594551366499830,156519322859755456242369014,19903992,151793457827342339189751290,157868079209960763779170810,19903996,153085614251090125939260926,159216835560166071315972606], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [19904000,154377770674837913762512386,160565591910371378852774402,19904004,155669927098585700512022022,161914348260576686389576198,3126792,150756135385641987660036618], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [156962083522333488335273482,163263104610781993926377994,3126796,151992897154037953441282574,158254239946081275084783118,164611860960987301463179790,3126800,153229658922433919222528530], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p45_2 : List P := [
  ⟨unpack [159546396369829062908034578,165960617311192608999981586], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs45 : List P := p45_0 ++ p45_1 ++ p45_2
private theorem row45 : checks (tilesOf bs45) 132 45 4 = true := by decide +kernel
private def p49_0 : List P := [
  cross18,
  cross21,
  cross19,
  cross22,
  ⟨unpack [4365143377], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross20,
  ⟨unpack [4365142365,53465445,53397873,53464433,3133813,70174073,3133817,3133820], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [36686209,3132801,3133824,19910020,19910024,3065229,3131789,19910028], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p49_1 : List P := [
  ⟨unpack [19907985,36686224,36686228,3130777,36686232,53462428,53462432,36685220], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [166261383243297435629375910,36685224,168054304334261012539625898,36685228,169847225425224590523617710,19908016,165624303026061658830130610,171640146516188168507609522], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [19908020,167346199200638515912101302,173433067607151745417859510,19908024,169068095375215374067813818,175225988698115323401851322,19908028,170789991549792231149784510], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [177018909789078901385843134,3130816,149762837720441830528502210,172511887724369089305497026,178811830880042478296093122,3130820,151228409736879274802006470,174233783898945946387467718], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [180604751971006056280084934,3130824,152693981753316719075510730,175955680073522804543180234,182397673061969634264076746,148558967527801058394883534,154159553769754163349014990,177677576248099661625150926], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [184190594152933211174326734,149965529075569584390522322,155625125786191607622519250,179399472422676519780863442,185983515243896789158318546,151372090623338111459902934,157090697802629051896023510,181121368597253376862834134], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [187776436334860367142310358,152778652171106637388432858,158556269819066496169527770,182843264771830235018546650,189569357425823944052560346,154185213718875164457813470,160021841835503940443032030,184565160946407092100517342], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [191362278516787522036552158,155591775266643690453452258,161487413851941384649427426,186287057120983950256229858,193155199607751100020543970,156998336814412217522832870,181159559478320748339120614,188008953295560807338200550], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p49_2 : List P := [
  ⟨unpack [194948120698714676930793958,158404898362180743518471658,182811865583065288861010410,189730849470137665493913066,196741041789678254914785770,159811459909949270587852270,184464171687809830456642030,191452745644714522508774894], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [198533962880641832898777582,161218021457717796583491058,186116477792554370978531826,193174641819291380664487410,200326883971605409809027570,162624583005486323652871670,187768783897298911500421622,194896537993868237746458102], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [202119805062568987725910518,164031144553254849648510458,189421090002043453096053242,196618434168445095902170618,203912726153532565709902330,165437706101023376717891070,191073396106787993617943038,198340330343021952984141310], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [205705647244496142620152318,166844267648791902713529858,192725702211532534139832834,200062226517598811139853826,207498568335459720604144130,168250829196560429782910470,194378008316277075735464454,201784122692175668221824518], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [209291489426423298588135942,169657390744328955778549258,196030314421021616257354250,203506018866752526377537034,211084410517386875498385930,171063952292097482847929870,197682620525766156779244046,205227915041329383459507726], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [212877331608350453482377742,172470513839866008843568658,199334926630510698374875666,206949811215906241615220242,214670252699314031466369554], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs49 : List P := p49_0 ++ p49_1 ++ p49_2
private theorem row49 : checks (tilesOf bs49) 132 49 4 = true := by decide +kernel
private def p53_0 : List P := [
  cross18,
  cross21,
  cross22,
  ⟨unpack [4683913513,355456337,53467529,19914121,3136912,3136916,19913112,19913116], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [19913120,19913124,36689320,19912108,188078272853040894040858030,19912112,190092877772491052192619954,19912116], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [192107482691941209270640054,3134904,187755137086034924444572090,194122087611391366348660154,3134908,189694412549435151889717694,196136692530841523426680254,3134912], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [191633688012835379334863298,198151297450291680504700354,187051862586713144174826950,193572963476235606780008902,200165902369741837582720454,188917243440617845255296458,195512238939635834225154506,202180507289191995734482378], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [190782624294522546335765966,197451514403036061670300110,204195112208642152812502478,192648005148427247416235474,199390789866436289115445714,206209717128092309890522578,194513386002331948496704982,201330065329836516560591318], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p53_1 : List P := [
  ⟨unpack [208224322047542466968542678,196378766856236648503432666,203269340793236744005736922,210238926966992624046562778,198244147710141349583902174,205208616256636971450882526,212253531886442781124582878,200109528564046050664371682], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [207147891720037198896028130,214268136805892939276344802,201974909417950751744841190,209087167183437426341173734,216282741725343096354364902,203840290271855452825310698,211026442646837653786319338,218297346644793253432385002], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [205705671125760153905780206,212965718110237881231464942,220311951564243410510405102,207571051979664853912507890,214904993573638108676610546,222326556483693567588425202,209436432833569554992977398,216844269037038336121756150], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [224341161403143724666445302,211301813687474256073446906,218783544500438563566901754,226355766322593882818207226,213167194541378957153916414,220722819963838791012047358,249973180720031466095894014,215032575395283658167277058], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [222662095427239018457192962,249602570208262750831894018,216897956249188359247746566,224601370890639245902338566,249986926940029715055959558,218763337103093059254474250,226540646354039473280375306,249622507333707891311959562], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [220628717956997760334943758,249776455113894789743893006,249257664564659487343959566,222494098810902461415413266,249415405122017559151893010,248892398635031986799959570], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs53 : List P := p53_0 ++ p53_1
private theorem row53 : checks (tilesOf bs53) 132 53 3 = true := by decide +kernel

theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤132) (hj : a.j≤55) :
    Covered 3 .empty a := by
  have h9 : 9 ≤ a.j := by simpa only [ht] using ha.2.1
  rcases lt_or_ge a.j 13 with h13 | h13
  · exact apply_batches (batches := bs9) row9 a ha ht hb h9 h13
  rcases lt_or_ge a.j 17 with h17 | h17
  · exact apply_batches (batches := bs13) row13 a ha ht hb h13 h17
  rcases lt_or_ge a.j 21 with h21 | h21
  · exact apply_batches (batches := bs17) row17 a ha ht hb h17 h21
  rcases lt_or_ge a.j 25 with h25 | h25
  · exact apply_batches (batches := bs21) row21 a ha ht hb h21 h25
  rcases lt_or_ge a.j 29 with h29 | h29
  · exact apply_batches (batches := bs25) row25 a ha ht hb h25 h29
  rcases lt_or_ge a.j 33 with h33 | h33
  · exact apply_batches (batches := bs29) row29 a ha ht hb h29 h33
  rcases lt_or_ge a.j 37 with h37 | h37
  · exact apply_batches (batches := bs33) row33 a ha ht hb h33 h37
  rcases lt_or_ge a.j 41 with h41 | h41
  · exact apply_batches (batches := bs37) row37 a ha ht hb h37 h41
  rcases lt_or_ge a.j 45 with h45 | h45
  · exact apply_batches (batches := bs41) row41 a ha ht hb h41 h45
  rcases lt_or_ge a.j 49 with h49 | h49
  · exact apply_batches (batches := bs45) row45 a ha ht hb h45 h49
  rcases lt_or_ge a.j 53 with h53 | h53
  · exact apply_batches (batches := bs49) row49 a ha ht hb h49 h53
  exact apply_batches (batches := bs53) row53 a ha ht hb h53 (Nat.lt_succ_of_le hj)
end Top3

end Compact50PriceTableEmpty
