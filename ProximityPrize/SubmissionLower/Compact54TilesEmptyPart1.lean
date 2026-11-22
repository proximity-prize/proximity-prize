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

namespace Top2
private abbrev P := PaidBatch .empty 2
private def cross0 : P := ⟨unpack [17515815949], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross1 : P := ⟨unpack [18422441057], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross2 : P := ⟨unpack [23036239005], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross3 : P := ⟨unpack [47900334453], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross4 : P := ⟨unpack [39041513493], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross5 : P := ⟨unpack [17885575285], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross6 : P := ⟨unpack [30972459297], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross7 : P := ⟨unpack [22181006453], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross8 : P := ⟨unpack [43036133885], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross9 : P := ⟨unpack [52061364257], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross10 : P := ⟨unpack [39261070497], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross11 : P := ⟨unpack [26678221089], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross12 : P := ⟨unpack [21997450549], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross13 : P := ⟨unpack [26158593461], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross14 : P := ⟨unpack [65081545781], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross15 : P := ⟨unpack [30671473825], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross16 : P := ⟨unpack [21930741045], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross17 : P := ⟨unpack [13307317669], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross18 : P := ⟨unpack [17199698445], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross19 : P := ⟨unpack [9045910837], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross20 : P := ⟨unpack [34681367765], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross21 : P := ⟨unpack [21729488165], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross22 : P := ⟨unpack [13072511333], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross23 : P := ⟨unpack [8861435173], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross24 : P := ⟨unpack [9968735305], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross25 : P := ⟨unpack [4365211029], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def p6_0 : List P := [
  ⟨unpack [4429256713,117514253], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross0,
  ⟨unpack [184621101,83958829,235020333,352459845,1157830749], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross1,
  ⟨unpack [419635305], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross2,
  cross3]
private def bs6 : List P := p6_0
private theorem row6 : checks (tilesOf bs6) 132 6 4 = true := by decide +kernel
private def p10_0 : List P := [
  cross0,
  cross1,
  cross2,
  cross3]
private def bs10 : List P := p10_0
private theorem row10 : checks (tilesOf bs10) 132 10 4 = true := by decide +kernel
private def p14_0 : List P := [
  cross4,
  cross5,
  cross6,
  cross3]
private def bs14 : List P := p14_0
private theorem row14 : checks (tilesOf bs14) 132 14 4 = true := by decide +kernel
private def p18_0 : List P := [
  cross4,
  cross5,
  cross7,
  cross6,
  cross8]
private def bs18 : List P := p18_0
private theorem row18 : checks (tilesOf bs18) 132 18 4 = true := by decide +kernel
private def p22_0 : List P := [
  cross4,
  cross9,
  cross7,
  cross10,
  cross11,
  cross8]
private def bs22 : List P := p22_0
private theorem row22 : checks (tilesOf bs22) 132 22 4 = true := by decide +kernel
private def p26_0 : List P := [
  cross9,
  cross10,
  cross11,
  cross12,
  cross13,
  cross8]
private def bs26 : List P := p26_0
private theorem row26 : checks (tilesOf bs26) 132 26 4 = true := by decide +kernel
private def p30_0 : List P := [
  cross9,
  cross10,
  cross12,
  cross13]
private def bs30 : List P := p30_0
private theorem row30 : checks (tilesOf bs30) 132 30 4 = true := by decide +kernel
private def p34_0 : List P := [
  cross9,
  cross14,
  cross10,
  cross15,
  cross12,
  cross16,
  cross17,
  cross13]
private def p34_1 : List P := [
  cross18]
private def bs34 : List P := p34_0 ++ p34_1
private theorem row34 : checks (tilesOf bs34) 132 34 4 = true := by decide +kernel
private def p38_0 : List P := [
  cross14,
  cross15,
  cross16,
  cross19,
  cross17,
  ⟨unpack [8861359525,8743984617], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross18,
  ⟨unpack [3057169], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs38 : List P := p38_0
private theorem row38 : checks (tilesOf bs38) 132 38 4 = true := by decide +kernel
private def p42_0 : List P := [
  cross14,
  cross15,
  cross20,
  cross21,
  cross19,
  cross22,
  ⟨unpack [4465799573,4532906405,137277889,86947265,19838425,4381911521,3061217,36614629], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3061220,19903977,3060209,3126769,3060213,3126772,103721465,53390841], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p42_1 : List P := [
  ⟨unpack [3060216,3126776,19902973,3126780,3126784,3125765,3126788,3059209], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [19902984,3059213,19902988,3124753,19902992], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs42 : List P := p42_0 ++ p42_1
private theorem row42 : checks (tilesOf bs42) 132 42 4 = true := by decide +kernel
private def p46_0 : List P := [
  cross14,
  cross20,
  cross21,
  cross23,
  cross22,
  ⟨unpack [4449026405,103727501,70174093,4381915541,36685217,53461417,86948269,53394861], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3130797,3130800,3130804,3129785,3130808,3063229,3129789,3130812], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [36683201,19907008,19839429,19907012,19907016,3062221,3128781,19907020], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p46_1 : List P := [
  ⟨unpack [3062224,36683216,19904981,36683220,36683224,3127773,36683228,53459424], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [36682212,166982293937898841955091942,36682216,168566444819365470258841066,36682220,170150595700832097488848366,36682224,171734746582298724718855666], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [19905012,166747433386370920570929654,173318897463765351948862966,19905016,168264863891114037777252858,174903048345231979178870266,19905020,169782294395857154983576062], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [176487199226698606408877566,19905024,171299724900600272189899266,178071350108165234712626690,19905028,172817155405343389396222470,179655500989631861942633990,3127816], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [167529767914835479087791626,174334585910086506602545674,181239651871098489172641290,3127820,168981912889409489538629134,175852016414829623808868878,182823802752565116402648590,3127824], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [170434057863983498915724818,177369446919572741015192082,184407953634031743632655890], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs46 : List P := p46_0 ++ p46_1
private theorem row46 : checks (tilesOf bs46) 132 46 4 = true := by decide +kernel
private def p50_0 : List P := [
  cross14,
  cross24,
  cross20,
  ⟨unpack [523161813], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross23,
  ⟨unpack [170905941,4381919593,103795073,70241665,36688257,3133837,3133840,3132821], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3133844], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross25]
private def p50_1 : List P := [
  ⟨unpack [19910040,19909021,19910044,19910048,36686244,36686248,36689321,36686252], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [36686256,53463476,53463480,19909052,168469314122076134684217790,3134908,19909056,170262235213039711594467778], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3134912,19909060,172055156304003289578459590,3134916,3131848,167791579817849172935036362,173848077394966867562451402,3134920], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3131852,169513475992426031090748878,175640998485930444472701390,3134924,3131856,171235372167002888172719570,177433919576894022456693202,3134928], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [166762834166360788199000534,172957268341579746328432086,179226840667857600440685014,185569398875362745365026262,168415140271105329794632154,174679164516156603410402778,181019761758821177350935002,187434779729267446445495770], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [170067446375849870316521950,176401060690733461566115294,182812682849784755334926814,189300160583172147525965278,171719752480594410771302882,178122956865310318648085986,184605603940748333318918626,191165541437076848606434786], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [173372058585338952635369958,179844853039887176803798502,186398525031711910229168614,193030922290981549686904294,175024364690083493157259754,181566749214464033885769194,188191446122675488213160426,194896303144886250767373802], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [176676670794828033679149550,183288645389040891974372846,189984367213639066197152238,196761683998790950774101486,178328976899572575274781170,185010541563617749056343538,191777288304602643107402226,198627064852695651854570994], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p50_2 : List P := [
  ⟨unpack [179981283004317115796670966,186732437738194607212056054,193570209395566221024285174,200492445706600352935040502,181633589109061656318560762,188454333912771464294026746,195363130486529799008276986,202357826560505054015510010], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [183285895213806197914192382,190176230087348322449739262,197156051577493375918526974,204223207414409755095979518,184938201318550738436082178,191898126261925179531709954,198948972668456953902518786,206088588268314456109340162], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [186590507423295278957971974,193620022436502037687422470,200741893759420531886510598,207953969122219156116067846,188242813528039820553603594,195341918611078894769393162,202534814850384108796760586,209819349976123857196537354], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [189895119632784361075493390,197063814785655752925105678,204327735941347686780752398,211684730830028558277006862,191547425737528901597383186,198785710960232610007076370,206120657032311264764744210,213550111683933259357476370], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs50 : List P := p50_0 ++ p50_1 ++ p50_2
private theorem row50 : checks (tilesOf bs50) 132 50 4 = true := by decide +kernel
private def p54_0 : List P := [
  cross24,
  cross25,
  ⟨unpack [19914133,3136924,3136928,3136932,19913128,19913132,19913136,19913140], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [19913144,3135932,186377234338027548793888190,3135936,188391839257477705871908290,3135940,190406444176927864023670214,186164964304062895474334154], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [192421049096378021101690314,188104239767463122919479758,194435654015828178179710414,190043515230863350364625362,196450258935278335257730514,191982790694263577809770966,198464863854728492335750614,193922066157663805254916570], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [200479468774178649413770714,195861341621064032700062174,202494073693628807565532638,197800617084464260145207778,204508678613078964643552738,199739892547864487590353382,206523283532529121721572838,201679168011264715035498986], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [208537888451979278799592938,203618443474664942480644590,210552493371429435877613038,205557718938065169925790194,212567098290879592955633138,207496994401465397370935798,214581703210329751107395062,209436269864865624816081402], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [216596308129779908185415162,211375545328265852261227006,218610913049230065263435262,213314820791666079706372610,220625517968680222341455362,215254096255066307151518214,222640122888130379419540998,217193371718466534529554954], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p54_1 : List P := [
  ⟨unpack [224654727807580536497561098,219132647181866761974700558,226669332727030694649323022,221071922645266989419846162,247491794814665491055959570], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs54 : List P := p54_0 ++ p54_1
private theorem row54 : checks (tilesOf bs54) 132 54 2 = true := by decide +kernel

theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤132) (hj : a.j≤55) :
    Covered 2 .empty a := by
  have h6 : 6 ≤ a.j := by simpa only [ht] using ha.2.1
  rcases lt_or_ge a.j 10 with h10 | h10
  · exact apply_batches (batches := bs6) row6 a ha ht hb h6 h10
  rcases lt_or_ge a.j 14 with h14 | h14
  · exact apply_batches (batches := bs10) row10 a ha ht hb h10 h14
  rcases lt_or_ge a.j 18 with h18 | h18
  · exact apply_batches (batches := bs14) row14 a ha ht hb h14 h18
  rcases lt_or_ge a.j 22 with h22 | h22
  · exact apply_batches (batches := bs18) row18 a ha ht hb h18 h22
  rcases lt_or_ge a.j 26 with h26 | h26
  · exact apply_batches (batches := bs22) row22 a ha ht hb h22 h26
  rcases lt_or_ge a.j 30 with h30 | h30
  · exact apply_batches (batches := bs26) row26 a ha ht hb h26 h30
  rcases lt_or_ge a.j 34 with h34 | h34
  · exact apply_batches (batches := bs30) row30 a ha ht hb h30 h34
  rcases lt_or_ge a.j 38 with h38 | h38
  · exact apply_batches (batches := bs34) row34 a ha ht hb h34 h38
  rcases lt_or_ge a.j 42 with h42 | h42
  · exact apply_batches (batches := bs38) row38 a ha ht hb h38 h42
  rcases lt_or_ge a.j 46 with h46 | h46
  · exact apply_batches (batches := bs42) row42 a ha ht hb h42 h46
  rcases lt_or_ge a.j 50 with h50 | h50
  · exact apply_batches (batches := bs46) row46 a ha ht hb h46 h50
  rcases lt_or_ge a.j 54 with h54 | h54
  · exact apply_batches (batches := bs50) row50 a ha ht hb h50 h54
  exact apply_batches (batches := bs54) row54 a ha ht hb h54 (Nat.lt_succ_of_le hj)
end Top2

end Compact50PriceTableEmpty
