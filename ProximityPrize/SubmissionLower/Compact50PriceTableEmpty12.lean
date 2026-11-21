import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableEmpty12
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top12
private def batch0 : PaidBatch .empty 12 := ⟨[
  .rectangle 12 36 76 43 37,
  .rectangle 15 44 78 51 44,
  .rectangle 18 52 86 53 44,
  .rectangle 77 36 109 40 44,
  .rectangle 77 41 101 44 44,
  .rectangle 79 45 98 48 47], by decide +kernel⟩
private def batch1 : PaidBatch .empty 12 := ⟨[
  .rectangle 79 49 94 51 47,
  .rectangle 87 52 92 53 47,
  .rectangle 93 52 96 52 47,
  .rectangle 93 53 94 53 47,
  .rectangle 95 49 103 49 47,
  .rectangle 95 50 101 50 47], by decide +kernel⟩
private def batch2 : PaidBatch .empty 12 := ⟨[
  .rectangle 95 51 98 51 47,
  .point 95 53 47,
  .point 96 53 47,
  .point 97 52 47,
  .point 97 53 47,
  .rectangle 98 52 98 52 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 12 := ⟨[
  .point 98 53 48,
  .rectangle 99 45 108 46 47,
  .rectangle 99 47 108 47 47,
  .rectangle 99 48 105 48 47,
  .point 99 51 47,
  .point 99 52 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 12 := ⟨[
  .point 99 53 48,
  .point 100 51 47,
  .point 100 52 48,
  .point 100 53 48,
  .point 101 51 47,
  .point 101 52 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 12 := ⟨[
  .point 101 53 48,
  .rectangle 102 41 117 42 46,
  .rectangle 102 43 111 44 46,
  .point 102 50 47,
  .point 102 51 47,
  .point 102 52 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 12 := ⟨[
  .point 102 53 48,
  .point 103 50 47,
  .point 103 51 47,
  .point 103 52 48,
  .point 103 53 48,
  .point 104 49 47], by decide +kernel⟩
private def batch7 : PaidBatch .empty 12 := ⟨[
  .point 104 50 47,
  .point 104 51 47,
  .point 104 52 48,
  .shared 104 53 48 ⟨.tilted, 1, 2, true, 190073612552839091⟩,
  .point 105 49 47,
  .point 105 50 47], by decide +kernel⟩
private def batch8 : PaidBatch .empty 12 := ⟨[
  .point 105 51 48,
  .point 105 52 48,
  .shared 105 53 48 ⟨.tilted, 1, 2, true, 191740818305834983⟩,
  .point 106 48 47,
  .point 106 49 47,
  .point 106 50 47], by decide +kernel⟩
private def batch9 : PaidBatch .empty 12 := ⟨[
  .point 106 51 48,
  .shared 106 52 48 ⟨.tilted, 1, 2, true, 185791321806428244⟩,
  .shared 106 53 48 ⟨.tilted, 1, 2, false, 191579828077020884⟩,
  .point 107 48 47,
  .point 107 49 47,
  .point 107 50 47], by decide +kernel⟩
private def batch10 : PaidBatch .empty 12 := ⟨[
  .point 107 51 48,
  .shared 107 52 48 ⟨.tilted, 1, 2, true, 187393765806680828⟩,
  .shared 107 53 48 ⟨.tilted, 1, 2, false, 193225651420872800⟩,
  .point 108 48 47,
  .point 108 49 47,
  .shared 108 50 47 ⟨.tilted, 1, 1, false, 172656014243953446⟩], by decide +kernel⟩
private def batch11 : PaidBatch .empty 12 := ⟨[
  .shared 108 51 48 ⟨.tilted, 1, 2, true, 181389481858727081⟩,
  .shared 108 52 48 ⟨.tilted, 1, 2, false, 188097952139208420⟩,
  .shared 108 53 48 ⟨.tilted, 1, 2, false, 194871474764724715⟩,
  .rectangle 109 45 114 45 47,
  .rectangle 109 46 111 46 47,
  .point 109 47 47], by decide +kernel⟩
private def batch12 : PaidBatch .empty 12 := ⟨[
  .point 109 48 47,
  .point 109 49 47,
  .shared 109 50 47 ⟨.tilted, 1, 1, false, 174118532969883736⟩,
  .shared 109 51 48 ⟨.tilted, 1, 2, true, 182928446516970349⟩,
  .shared 109 52 48 ⟨.tilted, 1, 2, false, 188921510653275316⟩,
  .shared 109 53 48 ⟨.tilted, 1, 2, false, 196517298108576631⟩], by decide +kernel⟩
private def batch13 : PaidBatch .empty 12 := ⟨[
  .rectangle 110 36 128 38 46,
  .rectangle 110 39 124 40 46,
  .point 110 47 47,
  .point 110 48 47,
  .point 110 49 47,
  .shared 110 50 47 ⟨.tilted, 1, 1, false, 175581051695814026⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 12 := ⟨[
  .shared 110 51 48 ⟨.tilted, 1, 2, true, 184467411175213617⟩,
  .shared 110 52 48 ⟨.tilted, 1, 2, false, 190505110348427780⟩,
  .shared 110 53 48 ⟨.tilted, 1, 2, false, 198163121452428546⟩,
  .point 111 47 47,
  .point 111 48 47,
  .shared 111 49 47 ⟨.tilted, 1, 1, false, 169722031880785335⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 12 := ⟨[
  .shared 111 50 48 ⟨.tilted, 1, 2, true, 185794062762802300⟩,
  .shared 111 51 48 ⟨.tilted, 1, 2, true, 186006375833456885⟩,
  .shared 111 52 48 ⟨.tilted, 1, 2, false, 192088710043580244⟩,
  .shared 111 53 48 ⟨.tilted, 1, 2, false, 199808944796280462⟩,
  .rectangle 112 43 120 43 47,
  .rectangle 112 44 117 44 47], by decide +kernel⟩
private def batch16 : PaidBatch .empty 12 := ⟨[
  .point 112 46 47,
  .point 112 47 47,
  .point 112 48 47,
  .shared 112 49 47 ⟨.tilted, 1, 1, false, 171125693286192902⟩,
  .shared 112 50 48 ⟨.tilted, 1, 2, true, 179831246244176428⟩,
  .shared 112 51 48 ⟨.tilted, 1, 2, false, 186022189019883997⟩], by decide +kernel⟩
private def batch17 : PaidBatch .empty 12 := ⟨[
  .shared 112 52 48 ⟨.tilted, 1, 2, false, 193672309738732708⟩,
  .shared 112 53 48 ⟨.tilted, 1, 2, false, 201454768140132377⟩,
  .point 113 46 47,
  .point 113 47 47,
  .point 113 48 47,
  .shared 113 49 47 ⟨.tilted, 1, 1, false, 172529354691600470⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 12 := ⟨[
  .shared 113 50 48 ⟨.tilted, 1, 2, true, 181308013971144372⟩,
  .shared 113 51 48 ⟨.tilted, 1, 2, false, 187544687175729252⟩,
  .shared 113 52 48 ⟨.tilted, 1, 2, false, 195255909433885172⟩,
  .shared 113 53 48 ⟨.tilted, 1, 2, false, 203100591483984293⟩,
  .point 114 46 47,
  .point 114 47 47], by decide +kernel⟩
private def batch19 : PaidBatch .empty 12 := ⟨[
  .shared 114 48 47 ⟨.tilted, 1, 1, false, 166574536988081424⟩,
  .shared 114 49 47 ⟨.tilted, 1, 1, false, 173933016097008037⟩,
  .shared 114 50 48 ⟨.tilted, 1, 2, true, 182784781698112316⟩,
  .shared 114 51 48 ⟨.tilted, 1, 2, false, 189067185331574508⟩,
  .shared 114 52 48 ⟨.tilted, 1, 2, false, 196839509129037636⟩,
  .shared 114 53 48 ⟨.tilted, 1, 2, false, 204746414827836208⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 12 := ⟨[
  .point 115 45 47,
  .point 115 46 47,
  .point 115 47 47,
  .shared 115 48 47 ⟨.tilted, 1, 1, false, 167920463182358512⟩,
  .shared 115 49 47 ⟨.tilted, 1, 1, false, 175336677502415605⟩,
  .shared 115 50 48 ⟨.tilted, 1, 2, false, 182893645325465476⟩], by decide +kernel⟩
private def batch21 : PaidBatch .empty 12 := ⟨[
  .shared 115 51 48 ⟨.tilted, 1, 2, false, 190589683487419763⟩,
  .shared 115 52 48 ⟨.tilted, 1, 2, false, 198423108824190100⟩,
  .shared 115 53 48 ⟨.tilted, 1, 2, false, 206392238171688124⟩,
  .point 116 45 47,
  .point 116 46 47,
  .point 116 47 47], by decide +kernel⟩
private def batch22 : PaidBatch .empty 12 := ⟨[
  .shared 116 48 47 ⟨.tilted, 1, 1, false, 169266389376635600⟩,
  .shared 116 49 48 ⟨.tilted, 1, 2, true, 185895517381606783⟩,
  .shared 116 50 48 ⟨.tilted, 1, 2, false, 184356164051395766⟩,
  .shared 116 51 48 ⟨.tilted, 1, 2, false, 192112181643265019⟩,
  .shared 116 52 48 ⟨.tilted, 1, 2, false, 200006708519342564⟩,
  .shared 116 53 48 ⟨.tilted, 1, 2, false, 208038061515540039⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 12 := ⟨[
  .point 117 45 47,
  .point 117 46 47,
  .shared 117 47 47 ⟨.tilted, 1, 1, false, 163225311714460267⟩,
  .shared 117 48 47 ⟨.tilted, 1, 1, false, 170612315570912688⟩,
  .shared 117 49 48 ⟨.tilted, 1, 2, true, 179344892713606623⟩,
  .shared 117 50 48 ⟨.tilted, 1, 2, false, 185818682777326056⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 12 := ⟨[
  .shared 117 51 48 ⟨.tilted, 1, 2, false, 193634679799110274⟩,
  .shared 117 52 48 ⟨.tilted, 1, 2, false, 201590308214495028⟩,
  .shared 117 53 48 ⟨.tilted, 1, 2, false, 209683884859391955⟩,
  .rectangle 118 41 127 41 47,
  .rectangle 118 42 123 42 47,
  .point 118 44 47], by decide +kernel⟩
private def batch25 : PaidBatch .empty 12 := ⟨[
  .point 118 45 47,
  .point 118 46 47,
  .shared 118 47 47 ⟨.tilted, 1, 1, false, 164514624806999119⟩,
  .shared 118 48 47 ⟨.tilted, 1, 1, false, 171958241765189776⟩,
  .shared 118 49 48 ⟨.tilted, 1, 2, true, 180760745920033235⟩,
  .shared 118 50 48 ⟨.tilted, 1, 2, false, 187281201503256346⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 12 := ⟨[
  .shared 118 51 48 ⟨.tilted, 1, 2, false, 195157177954955530⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, false, 203173907909647492⟩,
  .shared 118 53 48 ⟨.tilted, 1, 2, false, 211329708203243870⟩,
  .point 119 44 47,
  .point 119 45 47,
  .point 119 46 47], by decide +kernel⟩
private def batch27 : PaidBatch .empty 12 := ⟨[
  .shared 119 47 47 ⟨.tilted, 1, 1, false, 165803937899537970⟩,
  .shared 119 48 47 ⟨.tilted, 1, 1, false, 173304167959466864⟩,
  .shared 119 49 48 ⟨.tilted, 1, 2, true, 182176599126459847⟩,
  .shared 119 50 48 ⟨.tilted, 1, 2, false, 188743720229186636⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, false, 196679676110800785⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, false, 204757507604799956⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 12 := ⟨[
  .shared 119 53 48 ⟨.tilted, 1, 2, false, 212975531547095786⟩,
  .point 120 44 47,
  .point 120 45 47,
  .shared 120 46 47 ⟨.tilted, 0, 1, false, 159686138208540414⟩,
  .shared 120 47 47 ⟨.tilted, 0, 1, false, 167093250992076822⟩,
  .shared 120 48 47 ⟨.tilted, 1, 1, false, 174650094153743952⟩], by decide +kernel⟩
private def batch29 : PaidBatch .empty 12 := ⟨[
  .shared 120 49 48 ⟨.tilted, 1, 2, false, 182354984529453442⟩,
  .shared 120 50 48 ⟨.tilted, 1, 2, false, 190206238955116926⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, false, 198202174266646041⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, false, 206341107299952420⟩,
  .shared 120 53 48 ⟨.tilted, 1, 2, false, 214621354890947701⟩,
  .point 121 43 47], by decide +kernel⟩
private def batch30 : PaidBatch .empty 12 := ⟨[
  .point 121 44 47,
  .point 121 45 47,
  .shared 121 46 47 ⟨.tilted, 0, 1, false, 160919960308733272⟩,
  .shared 121 47 47 ⟨.tilted, 0, 1, false, 168382564084615673⟩,
  .shared 121 48 47 ⟨.tilted, 1, 1, false, 175996020348021040⟩,
  .shared 121 49 48 ⟨.tilted, 1, 2, false, 183758645934861010⟩], by decide +kernel⟩
private def batch31 : PaidBatch .empty 12 := ⟨[
  .shared 121 50 48 ⟨.tilted, 1, 2, false, 191668757681047216⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, false, 199724672422491296⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, false, 207924706995104884⟩,
  .shared 121 53 48 ⟨.tilted, 1, 2, false, 216267178234799617⟩,
  .point 122 43 47,
  .point 122 44 47], by decide +kernel⟩
private def batch32 : PaidBatch .empty 12 := ⟨[
  .point 122 45 47,
  .shared 122 46 47 ⟨.tilted, 0, 1, false, 162153782408926130⟩,
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 169671877177154525⟩,
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 177341946542298128⟩,
  .shared 122 49 48 ⟨.tilted, 1, 2, false, 185162307340268577⟩,
  .shared 122 50 48 ⟨.tilted, 1, 2, false, 193131276406977506⟩], by decide +kernel⟩
private def batch33 : PaidBatch .empty 12 := ⟨[
  .shared 122 51 48 ⟨.tilted, 1, 2, false, 201247170578336552⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, false, 209508306690257348⟩,
  .shared 122 53 48 ⟨.tilted, 1, 2, false, 217913001578651532⟩,
  .point 123 43 47,
  .point 123 44 47,
  .shared 123 45 47 ⟨.tilted, 0, 1, false, 155968798618940418⟩], by decide +kernel⟩
private def batch34 : PaidBatch .empty 12 := ⟨[
  .shared 123 46 47 ⟨.tilted, 0, 1, false, 163387604509118988⟩,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 170961190269693376⟩,
  .shared 123 48 48 ⟨.tilted, 0, 2, true, 179768837482504536⟩,
  .shared 123 49 48 ⟨.tilted, 1, 2, false, 186565968745676145⟩,
  .shared 123 50 48 ⟨.tilted, 1, 2, false, 194593795132907796⟩,
  .shared 123 51 48 ⟨.tilted, 1, 2, false, 202769668734181807⟩], by decide +kernel⟩
private def batch35 : PaidBatch .empty 12 := ⟨[
  .shared 123 52 48 ⟨.tilted, 1, 2, false, 211091906385409812⟩,
  .shared 123 53 48 ⟨.tilted, 1, 2, false, 219558824922503448⟩,
  .point 124 42 47,
  .point 124 43 47,
  .point 124 44 47,
  .shared 124 45 47 ⟨.tilted, 0, 1, false, 157148251836179525⟩], by decide +kernel⟩
private def batch36 : PaidBatch .empty 12 := ⟨[
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 164621426609311846⟩,
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 172250503362232228⟩,
  .shared 124 48 48 ⟨.tilted, 0, 2, true, 181125058579123808⟩,
  .shared 124 49 48 ⟨.tilted, 1, 2, false, 187969630151083712⟩,
  .shared 124 50 48 ⟨.tilted, 1, 2, false, 196056313858838086⟩,
  .shared 124 51 48 ⟨.tilted, 1, 2, false, 204292166890027063⟩], by decide +kernel⟩
private def batch37 : PaidBatch .empty 12 := ⟨[
  .shared 124 52 48 ⟨.tilted, 1, 2, false, 212675506080562276⟩,
  .shared 124 53 48 ⟨.tilted, 1, 2, false, 221204648266355363⟩,
  .rectangle 125 39 129 39 46,
  .rectangle 125 40 129 40 47,
  .point 125 42 47,
  .point 125 43 47], by decide +kernel⟩
private def batch38 : PaidBatch .empty 12 := ⟨[
  .point 125 44 47,
  .shared 125 45 47 ⟨.tilted, 0, 1, false, 158327705053418633⟩,
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 165855248709504704⟩,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 173539816454771079⟩,
  .shared 125 48 48 ⟨.tilted, 0, 2, true, 182481279675743080⟩,
  .shared 125 49 48 ⟨.tilted, 0, 2, false, 189373291556491280⟩], by decide +kernel⟩
private def batch39 : PaidBatch .empty 12 := ⟨[
  .shared 125 50 48 ⟨.tilted, 1, 2, false, 197518832584768376⟩,
  .shared 125 51 48 ⟨.tilted, 1, 2, false, 205814665045872318⟩,
  .shared 125 52 48 ⟨.tilted, 1, 2, false, 214259105775714740⟩,
  .shared 125 53 48 ⟨.tilted, 1, 2, false, 222850471610207279⟩,
  .point 126 42 47,
  .point 126 43 47], by decide +kernel⟩
private def batch40 : PaidBatch .empty 12 := ⟨[
  .shared 126 44 47 ⟨.tilted, 0, 1, false, 152085075094278828⟩,
  .shared 126 45 47 ⟨.tilted, 0, 1, false, 159507158270657740⟩,
  .shared 126 46 47 ⟨.tilted, 0, 1, false, 167089070809697562⟩,
  .shared 126 47 47 ⟨.tilted, 0, 1, false, 174829129547309931⟩,
  .shared 126 48 48 ⟨.tilted, 0, 2, true, 183837500772362352⟩,
  .shared 126 49 48 ⟨.tilted, 0, 2, false, 190776952961898847⟩], by decide +kernel⟩
private def batch41 : PaidBatch .empty 12 := ⟨[
  .shared 126 50 48 ⟨.tilted, 1, 2, false, 198981351310698666⟩,
  .shared 126 51 48 ⟨.tilted, 1, 2, false, 207337163201717574⟩,
  .shared 126 52 48 ⟨.tilted, 1, 2, false, 215842705470867204⟩,
  .shared 126 53 48 ⟨.tilted, 1, 2, false, 224496294954059194⟩,
  .point 127 42 47,
  .point 127 43 47], by decide +kernel⟩
private def batch42 : PaidBatch .empty 12 := ⟨[
  .shared 127 44 47 ⟨.tilted, 0, 1, false, 153211281537956428⟩,
  .shared 127 45 47 ⟨.tilted, 0, 1, false, 160686611487896848⟩,
  .shared 127 46 47 ⟨.tilted, 0, 1, false, 168322892909890420⟩,
  .shared 127 47 47 ⟨.tilted, 0, 1, false, 176118442639848782⟩,
  .shared 127 48 48 ⟨.tilted, 0, 2, false, 184071577513683568⟩,
  .shared 127 49 48 ⟨.tilted, 0, 2, false, 192180614367306415⟩], by decide +kernel⟩
private def batch43 : PaidBatch .empty 12 := ⟨[
  .shared 127 50 48 ⟨.tilted, 1, 2, false, 200443870036628956⟩,
  .shared 127 51 48 ⟨.tilted, 1, 2, false, 208859661357562829⟩,
  .shared 127 52 48 ⟨.tilted, 1, 2, false, 217426305166019668⟩,
  .shared 127 53 48 ⟨.tilted, 1, 2, false, 226142118297911110⟩,
  .point 128 41 47,
  .point 128 42 47], by decide +kernel⟩
private def batch44 : PaidBatch .empty 12 := ⟨[
  .point 128 43 47,
  .shared 128 44 47 ⟨.tilted, 0, 1, false, 154337487981634028⟩,
  .shared 128 45 47 ⟨.tilted, 0, 1, false, 161866064705135955⟩,
  .shared 128 46 47 ⟨.tilted, 0, 1, false, 169556715010083278⟩,
  .shared 128 47 47 ⟨.tilted, 0, 1, false, 177407755732387634⟩,
  .shared 128 48 48 ⟨.tilted, 0, 2, false, 185417503707960656⟩], by decide +kernel⟩
private def batch45 : PaidBatch .empty 12 := ⟨[
  .shared 128 49 48 ⟨.tilted, 0, 2, false, 193584275772713982⟩,
  .shared 128 50 48 ⟨.tilted, 0, 2, false, 201906388762559246⟩,
  .shared 128 51 48 ⟨.tilted, 1, 2, false, 210382159513408085⟩,
  .shared 128 52 48 ⟨.tilted, 1, 2, false, 219009904861172132⟩,
  .shared 128 53 48 ⟨.tilted, 1, 2, false, 227787941641763025⟩,
  .rectangle 129 36 129 37 46], by decide +kernel⟩
private def batch46 : PaidBatch .empty 12 := ⟨[
  .rectangle 129 38 129 38 46,
  .point 129 41 47,
  .point 129 42 47,
  .point 129 43 47,
  .shared 129 44 47 ⟨.tilted, 0, 1, false, 155463694425311628⟩,
  .shared 129 45 47 ⟨.tilted, 0, 1, false, 163045517922375063⟩], by decide +kernel⟩
private def batch47 : PaidBatch .empty 12 := ⟨[
  .shared 129 46 47 ⟨.tilted, 0, 1, false, 170790537110276136⟩,
  .shared 129 47 47 ⟨.tilted, 0, 1, false, 178697068824926485⟩,
  .shared 129 48 48 ⟨.tilted, 0, 2, false, 186763429902237744⟩,
  .shared 129 49 48 ⟨.tilted, 0, 2, false, 194987937178121550⟩,
  .shared 129 50 48 ⟨.tilted, 0, 2, false, 203368907488489536⟩,
  .shared 129 51 48 ⟨.tilted, 1, 2, false, 211904657669253340⟩], by decide +kernel⟩
private def batch48 : PaidBatch .empty 12 := ⟨[
  .shared 129 52 48 ⟨.tilted, 1, 2, false, 220593504556324596⟩,
  .shared 129 53 49 ⟨.tilted, 1, 2, false, 229433764985614941⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 12) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32, batch33, batch34, batch35, batch36, batch37, batch38, batch39, batch40, batch41, batch42, batch43, batch44, batch45, batch46, batch47, batch48]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 129 36 10 = true := by decide +kernel
private theorem index46 : checks tiles 129 46 8 = true := by decide +kernel
private theorem covers : checks tiles 129 36 18 = true :=
  checks_join (index36) index46

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 129) (hj : a.j ≤ 53) : Covered 12 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

namespace Top13
private def batch0 : PaidBatch .empty 13 := ⟨[
  .rectangle 13 39 86 46 44,
  .rectangle 16 47 76 53 44,
  .rectangle 77 47 94 50 47,
  .rectangle 77 51 90 53 47,
  .rectangle 87 39 106 42 44,
  .rectangle 87 43 106 45 46], by decide +kernel⟩
private def batch1 : PaidBatch .empty 13 := ⟨[
  .rectangle 87 46 101 48 47,
  .rectangle 91 51 98 51 47,
  .rectangle 91 52 96 52 47,
  .rectangle 91 53 94 53 47,
  .rectangle 95 49 103 49 47,
  .rectangle 95 50 101 50 47], by decide +kernel⟩
private def batch2 : PaidBatch .empty 13 := ⟨[
  .point 95 53 47,
  .point 96 53 47,
  .point 97 52 47,
  .point 97 53 47,
  .rectangle 98 52 98 52 48,
  .point 98 53 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 13 := ⟨[
  .point 99 51 47,
  .point 99 52 48,
  .point 99 53 48,
  .point 100 51 47,
  .point 100 52 48,
  .point 100 53 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 13 := ⟨[
  .point 101 51 47,
  .point 101 52 48,
  .point 101 53 48,
  .rectangle 102 46 111 46 47,
  .rectangle 102 47 108 47 47,
  .rectangle 102 48 106 48 47], by decide +kernel⟩
private def batch5 : PaidBatch .empty 13 := ⟨[
  .point 102 50 47,
  .point 102 51 47,
  .point 102 52 48,
  .point 102 53 48,
  .point 103 50 47,
  .point 103 51 47], by decide +kernel⟩
private def batch6 : PaidBatch .empty 13 := ⟨[
  .point 103 52 48,
  .shared 103 53 48 ⟨.tilted, 1, 2, true, 189344267191321884⟩,
  .point 104 49 47,
  .point 104 50 47,
  .point 104 51 47,
  .point 104 52 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 13 := ⟨[
  .shared 104 53 48 ⟨.tilted, 1, 2, false, 189814556857154840⟩,
  .point 105 49 47,
  .point 105 50 47,
  .point 105 51 48,
  .point 105 52 48,
  .shared 105 53 48 ⟨.tilted, 1, 2, false, 191467513609113078⟩], by decide +kernel⟩
private def batch8 : PaidBatch .empty 13 := ⟨[
  .point 106 49 47,
  .point 106 50 47,
  .point 106 51 48,
  .shared 106 52 48 ⟨.tilted, 1, 2, false, 185676608195719157⟩,
  .shared 106 53 48 ⟨.tilted, 1, 2, false, 193120470361071316⟩,
  .rectangle 107 39 124 40 46], by decide +kernel⟩
private def batch9 : PaidBatch .empty 13 := ⟨[
  .rectangle 107 41 118 42 46,
  .rectangle 107 43 114 44 47,
  .rectangle 107 45 114 45 47,
  .point 107 48 47,
  .point 107 49 47,
  .point 107 50 47], by decide +kernel⟩
private def batch10 : PaidBatch .empty 13 := ⟨[
  .point 107 51 48,
  .shared 107 52 48 ⟨.tilted, 1, 2, false, 187143068051337771⟩,
  .shared 107 53 48 ⟨.tilted, 1, 2, false, 194773427113029554⟩,
  .point 108 48 47,
  .point 108 49 47,
  .shared 108 50 47 ⟨.tilted, 1, 1, false, 173756228670022393⟩], by decide +kernel⟩
private def batch11 : PaidBatch .empty 13 := ⟨[
  .shared 108 51 48 ⟨.tilted, 1, 2, true, 182092287106007765⟩,
  .shared 108 52 48 ⟨.tilted, 1, 2, false, 188733320250571311⟩,
  .shared 108 53 48 ⟨.tilted, 1, 2, false, 196426383864987792⟩,
  .point 109 47 47,
  .point 109 48 47,
  .point 109 49 47], by decide +kernel⟩
private def batch12 : PaidBatch .empty 13 := ⟨[
  .shared 109 50 47 ⟨.tilted, 1, 1, false, 175224438091983265⟩,
  .shared 109 51 48 ⟨.tilted, 1, 2, true, 183631251764251033⟩,
  .shared 109 52 48 ⟨.tilted, 1, 2, false, 190323572449804850⟩,
  .shared 109 53 48 ⟨.tilted, 1, 2, false, 198079340616946030⟩,
  .point 110 47 47,
  .point 110 48 47], by decide +kernel⟩
private def batch13 : PaidBatch .empty 13 := ⟨[
  .point 110 49 47,
  .shared 110 50 47 ⟨.tilted, 1, 1, false, 176692647513944136⟩,
  .shared 110 51 48 ⟨.tilted, 1, 2, false, 184233380309355557⟩,
  .shared 110 52 48 ⟨.tilted, 1, 2, false, 191913824649038390⟩,
  .shared 110 53 48 ⟨.tilted, 1, 2, false, 199732297368904268⟩,
  .point 111 47 47], by decide +kernel⟩
private def batch14 : PaidBatch .empty 13 := ⟨[
  .point 111 48 47,
  .shared 111 49 47 ⟨.tilted, 1, 1, false, 170702180624305392⟩,
  .shared 111 50 48 ⟨.tilted, 1, 2, true, 187971764176900240⟩,
  .shared 111 51 48 ⟨.tilted, 1, 2, false, 185762050065256641⟩,
  .shared 111 52 48 ⟨.tilted, 1, 2, false, 193504076848271929⟩,
  .shared 111 53 48 ⟨.tilted, 1, 2, false, 201385254120862506⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 13 := ⟨[
  .point 112 46 47,
  .point 112 47 47,
  .point 112 48 47,
  .shared 112 49 47 ⟨.tilted, 1, 1, false, 172111051821718294⟩,
  .shared 112 50 48 ⟨.tilted, 1, 2, true, 180429267876027158⟩,
  .shared 112 51 48 ⟨.tilted, 1, 2, false, 187290719821157725⟩], by decide +kernel⟩
private def batch16 : PaidBatch .empty 13 := ⟨[
  .shared 112 52 48 ⟨.tilted, 1, 2, false, 195094329047505469⟩,
  .shared 112 53 48 ⟨.tilted, 1, 2, false, 203038210872820744⟩,
  .point 113 46 47,
  .point 113 47 47,
  .point 113 48 47,
  .shared 113 49 47 ⟨.tilted, 1, 1, false, 173519923019131196⟩], by decide +kernel⟩
private def batch17 : PaidBatch .empty 13 := ⟨[
  .shared 113 50 48 ⟨.tilted, 1, 2, false, 181097275779826751⟩,
  .shared 113 51 48 ⟨.tilted, 1, 2, false, 188819389577058809⟩,
  .shared 113 52 48 ⟨.tilted, 1, 2, false, 196684581246739008⟩,
  .shared 113 53 48 ⟨.tilted, 1, 2, false, 204691167624778982⟩,
  .point 114 46 47,
  .point 114 47 47], by decide +kernel⟩
private def batch18 : PaidBatch .empty 13 := ⟨[
  .shared 114 48 47 ⟨.tilted, 1, 1, false, 167439669541317687⟩,
  .shared 114 49 47 ⟨.tilted, 1, 1, false, 174928794216544098⟩,
  .shared 114 50 48 ⟨.tilted, 1, 2, false, 182565485201787622⟩,
  .shared 114 51 48 ⟨.tilted, 1, 2, false, 190348059332959893⟩,
  .shared 114 52 48 ⟨.tilted, 1, 2, false, 198274833445972548⟩,
  .shared 114 53 48 ⟨.tilted, 1, 2, false, 206344124376737220⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 13 := ⟨[
  .rectangle 115 43 120 43 47,
  .rectangle 115 44 117 44 47,
  .point 115 45 47,
  .point 115 46 47,
  .point 115 47 47,
  .shared 115 48 47 ⟨.tilted, 1, 1, false, 168790324623574862⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 13 := ⟨[
  .shared 115 49 47 ⟨.tilted, 1, 1, false, 176337665413957000⟩,
  .shared 115 50 48 ⟨.tilted, 1, 2, false, 184033694623748494⟩,
  .shared 115 51 48 ⟨.tilted, 1, 2, false, 191876729088860977⟩,
  .shared 115 52 48 ⟨.tilted, 1, 2, false, 199865085645206087⟩,
  .shared 115 53 48 ⟨.tilted, 1, 2, false, 207997081128695458⟩,
  .point 116 45 47], by decide +kernel⟩
private def batch21 : PaidBatch .empty 13 := ⟨[
  .point 116 46 47,
  .point 116 47 47,
  .shared 116 48 47 ⟨.tilted, 1, 1, false, 170140979705832038⟩,
  .shared 116 49 48 ⟨.tilted, 1, 2, true, 187836186578670210⟩,
  .shared 116 50 48 ⟨.tilted, 1, 2, false, 185501904045709365⟩,
  .shared 116 51 48 ⟨.tilted, 1, 2, false, 193405398844762061⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 13 := ⟨[
  .shared 116 52 48 ⟨.tilted, 1, 2, false, 201455337844439627⟩,
  .shared 116 53 48 ⟨.tilted, 1, 2, false, 209650037880653696⟩,
  .point 117 45 47,
  .point 117 46 47,
  .shared 117 47 47 ⟨.tilted, 1, 1, false, 163980477569677827⟩,
  .shared 117 48 47 ⟨.tilted, 1, 1, false, 171491634788089213⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 13 := ⟨[
  .shared 117 49 48 ⟨.tilted, 1, 2, true, 179846626701140094⟩,
  .shared 117 50 48 ⟨.tilted, 1, 2, false, 186970113467670237⟩,
  .shared 117 51 48 ⟨.tilted, 1, 2, false, 194934068600663145⟩,
  .shared 117 52 48 ⟨.tilted, 1, 2, false, 203045590043673166⟩,
  .shared 117 53 48 ⟨.tilted, 1, 2, false, 211302994632611934⟩,
  .point 118 44 47], by decide +kernel⟩
private def batch24 : PaidBatch .empty 13 := ⟨[
  .point 118 45 47,
  .point 118 46 47,
  .shared 118 47 47 ⟨.tilted, 1, 1, false, 165274038646171519⟩,
  .shared 118 48 47 ⟨.tilted, 1, 1, false, 172842289870346389⟩,
  .shared 118 49 48 ⟨.tilted, 1, 2, false, 180564279006195706⟩,
  .shared 118 50 48 ⟨.tilted, 1, 2, false, 188438322889631108⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 13 := ⟨[
  .shared 118 51 48 ⟨.tilted, 1, 2, false, 196462738356564229⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, false, 204635842242906706⟩,
  .shared 118 53 48 ⟨.tilted, 1, 2, false, 212955951384570172⟩,
  .rectangle 119 41 127 41 47,
  .rectangle 119 42 123 42 47,
  .point 119 44 47], by decide +kernel⟩
private def batch26 : PaidBatch .empty 13 := ⟨[
  .point 119 45 47,
  .point 119 46 47,
  .shared 119 47 47 ⟨.tilted, 1, 1, false, 166567599722665211⟩,
  .shared 119 48 47 ⟨.tilted, 1, 1, false, 174192944952603564⟩,
  .shared 119 49 48 ⟨.tilted, 1, 2, false, 181973150203608608⟩,
  .shared 119 50 48 ⟨.tilted, 1, 2, false, 189906532311591980⟩], by decide +kernel⟩
private def batch27 : PaidBatch .empty 13 := ⟨[
  .shared 119 51 48 ⟨.tilted, 1, 2, false, 197991408112465313⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, false, 206226094442140245⟩,
  .shared 119 53 48 ⟨.tilted, 1, 2, false, 214608908136528410⟩,
  .point 120 44 47,
  .point 120 45 47,
  .shared 120 46 47 ⟨.tilted, 0, 1, false, 160336386858004366⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 13 := ⟨[
  .shared 120 47 47 ⟨.tilted, 0, 1, false, 167861160799158903⟩,
  .shared 120 48 47 ⟨.tilted, 1, 1, false, 175543600034860740⟩,
  .shared 120 49 48 ⟨.tilted, 1, 2, false, 183382021401021510⟩,
  .shared 120 50 48 ⟨.tilted, 1, 2, false, 191374741733552851⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, false, 199520077868366397⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, false, 207816346641373785⟩], by decide +kernel⟩
private def batch29 : PaidBatch .empty 13 := ⟨[
  .shared 120 53 48 ⟨.tilted, 1, 2, false, 216261864888486648⟩,
  .point 121 43 47,
  .point 121 44 47,
  .point 121 45 47,
  .shared 121 46 47 ⟨.tilted, 0, 1, false, 161573976038126818⟩,
  .shared 121 47 47 ⟨.tilted, 0, 1, false, 169154721875652595⟩], by decide +kernel⟩
private def batch30 : PaidBatch .empty 13 := ⟨[
  .shared 121 48 47 ⟨.tilted, 1, 1, false, 176894255117117915⟩,
  .shared 121 49 48 ⟨.tilted, 1, 2, false, 184790892598434412⟩,
  .shared 121 50 48 ⟨.tilted, 1, 2, false, 192842951155513723⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, false, 201048747624267481⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, false, 209406598840607324⟩,
  .shared 121 53 48 ⟨.tilted, 1, 2, false, 217914821640444886⟩], by decide +kernel⟩
private def batch31 : PaidBatch .empty 13 := ⟨[
  .point 122 43 47,
  .point 122 44 47,
  .point 122 45 47,
  .shared 122 46 47 ⟨.tilted, 0, 1, false, 162811565218249269⟩,
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 170448282952146287⟩,
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 178244910199375091⟩], by decide +kernel⟩
private def batch32 : PaidBatch .empty 13 := ⟨[
  .shared 122 49 48 ⟨.tilted, 1, 2, false, 186199763795847314⟩,
  .shared 122 50 48 ⟨.tilted, 1, 2, false, 194311160577474594⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, false, 202577417380168565⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, false, 210996851039840864⟩,
  .shared 122 53 48 ⟨.tilted, 1, 2, false, 219567778392403124⟩,
  .point 123 43 47], by decide +kernel⟩
private def batch33 : PaidBatch .empty 13 := ⟨[
  .point 123 44 47,
  .shared 123 45 47 ⟨.tilted, 0, 1, false, 156519179554915854⟩,
  .shared 123 46 47 ⟨.tilted, 0, 1, false, 164049154398371721⟩,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 171741844028639979⟩,
  .shared 123 48 48 ⟨.tilted, 0, 2, true, 180182779796833447⟩,
  .shared 123 49 48 ⟨.tilted, 1, 2, false, 187608634993260216⟩], by decide +kernel⟩
private def batch34 : PaidBatch .empty 13 := ⟨[
  .shared 123 50 48 ⟨.tilted, 1, 2, false, 195779369999435466⟩,
  .shared 123 51 48 ⟨.tilted, 1, 2, false, 204106087136069649⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, false, 212587103239074403⟩,
  .shared 123 53 48 ⟨.tilted, 1, 2, false, 221220735144361362⟩,
  .point 124 42 47,
  .point 124 43 47], by decide +kernel⟩
private def batch35 : PaidBatch .empty 13 := ⟨[
  .point 124 44 47,
  .shared 124 45 47 ⟨.tilted, 0, 1, false, 157701918948059308⟩,
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 165286743578494172⟩,
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 173035405105133671⟩,
  .shared 124 48 48 ⟨.tilted, 0, 2, false, 180946220363889442⟩,
  .shared 124 49 48 ⟨.tilted, 1, 2, false, 189017506190673118⟩], by decide +kernel⟩
private def batch36 : PaidBatch .empty 13 := ⟨[
  .shared 124 50 48 ⟨.tilted, 1, 2, false, 197247579421396337⟩,
  .shared 124 51 48 ⟨.tilted, 1, 2, false, 205634756891970733⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, false, 214177355438307943⟩,
  .shared 124 53 48 ⟨.tilted, 1, 2, false, 222873691896319600⟩,
  .rectangle 125 39 129 39 46,
  .rectangle 125 40 129 40 47], by decide +kernel⟩
private def batch37 : PaidBatch .empty 13 := ⟨[
  .point 125 42 47,
  .point 125 43 47,
  .point 125 44 47,
  .shared 125 45 47 ⟨.tilted, 0, 1, false, 158884658341202762⟩,
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 166524332758616624⟩,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 174328966181627363⟩], by decide +kernel⟩
private def batch38 : PaidBatch .empty 13 := ⟨[
  .shared 125 48 48 ⟨.tilted, 0, 2, false, 182296875446146617⟩,
  .shared 125 49 48 ⟨.tilted, 0, 2, false, 190426377388086020⟩,
  .shared 125 50 48 ⟨.tilted, 1, 2, false, 198715788843357209⟩,
  .shared 125 51 48 ⟨.tilted, 1, 2, false, 207163426647871817⟩,
  .shared 125 52 48 ⟨.tilted, 1, 2, false, 215767607637541482⟩,
  .shared 125 53 48 ⟨.tilted, 1, 2, false, 224526648648277838⟩], by decide +kernel⟩
private def batch39 : PaidBatch .empty 13 := ⟨[
  .point 126 42 47,
  .point 126 43 47,
  .point 126 44 47,
  .shared 126 45 47 ⟨.tilted, 0, 1, false, 160067397734346216⟩,
  .shared 126 46 47 ⟨.tilted, 0, 1, false, 167761921938739075⟩,
  .shared 126 47 47 ⟨.tilted, 0, 1, false, 175622527258121055⟩], by decide +kernel⟩
private def batch40 : PaidBatch .empty 13 := ⟨[
  .shared 126 48 48 ⟨.tilted, 0, 2, false, 183647530528403793⟩,
  .shared 126 49 48 ⟨.tilted, 0, 2, false, 191835248585498922⟩,
  .shared 126 50 48 ⟨.tilted, 1, 2, false, 200183998265318080⟩,
  .shared 126 51 48 ⟨.tilted, 1, 2, false, 208692096403772901⟩,
  .shared 126 52 48 ⟨.tilted, 1, 2, false, 217357859836775022⟩,
  .shared 126 53 48 ⟨.tilted, 1, 2, false, 226179605400236076⟩], by decide +kernel⟩
private def batch41 : PaidBatch .empty 13 := ⟨[
  .point 127 42 47,
  .point 127 43 47,
  .shared 127 44 47 ⟨.tilted, 0, 1, false, 153669649524587543⟩,
  .shared 127 45 47 ⟨.tilted, 0, 1, false, 161250137127489670⟩,
  .shared 127 46 47 ⟨.tilted, 0, 1, false, 168999511118861527⟩,
  .shared 127 47 47 ⟨.tilted, 0, 1, false, 176916088334614747⟩], by decide +kernel⟩
private def batch42 : PaidBatch .empty 13 := ⟨[
  .shared 127 48 48 ⟨.tilted, 0, 2, false, 184998185610660968⟩,
  .shared 127 49 48 ⟨.tilted, 0, 2, false, 193244119782911824⟩,
  .shared 127 50 48 ⟨.tilted, 1, 2, false, 201652207687278952⟩,
  .shared 127 51 48 ⟨.tilted, 1, 2, false, 210220766159673985⟩,
  .shared 127 52 48 ⟨.tilted, 1, 2, false, 218948112036008561⟩,
  .shared 127 53 48 ⟨.tilted, 1, 2, false, 227832562152194314⟩], by decide +kernel⟩
private def batch43 : PaidBatch .empty 13 := ⟨[
  .shared 128 41 47 ⟨.ordinary, 0, 1, false, 180587062555747987⟩,
  .point 128 42 47,
  .point 128 43 47,
  .shared 128 44 47 ⟨.tilted, 0, 1, false, 154798661240144243⟩,
  .shared 128 45 47 ⟨.tilted, 0, 1, false, 162432876520633124⟩,
  .shared 128 46 47 ⟨.tilted, 0, 1, false, 170237100298983978⟩], by decide +kernel⟩
private def batch44 : PaidBatch .empty 13 := ⟨[
  .shared 128 47 47 ⟨.tilted, 0, 1, false, 178209649411108439⟩,
  .shared 128 48 48 ⟨.tilted, 0, 2, false, 186348840692918144⟩,
  .shared 128 49 48 ⟨.tilted, 0, 2, false, 194652990980324726⟩,
  .shared 128 50 48 ⟨.tilted, 0, 2, false, 203120417109239823⟩,
  .shared 128 51 48 ⟨.tilted, 1, 2, false, 211749435915575069⟩,
  .shared 128 52 48 ⟨.tilted, 1, 2, false, 220538364235242101⟩], by decide +kernel⟩
private def batch45 : PaidBatch .empty 13 := ⟨[
  .shared 128 53 48 ⟨.tilted, 1, 2, false, 229485518904152552⟩,
  .shared 129 41 47 ⟨.ordinary, 0, 1, false, 181909071622884115⟩,
  .point 129 42 47,
  .point 129 43 47,
  .shared 129 44 47 ⟨.tilted, 0, 1, false, 155927672955700942⟩,
  .shared 129 45 47 ⟨.tilted, 0, 1, false, 163615615913776578⟩], by decide +kernel⟩
private def batch46 : PaidBatch .empty 13 := ⟨[
  .shared 129 46 47 ⟨.tilted, 0, 1, false, 171474689479106430⟩,
  .shared 129 47 47 ⟨.tilted, 0, 1, false, 179503210487602131⟩,
  .shared 129 48 48 ⟨.tilted, 0, 2, false, 187699495775175319⟩,
  .shared 129 49 48 ⟨.tilted, 0, 2, false, 196061862177737628⟩,
  .shared 129 50 48 ⟨.tilted, 0, 2, false, 204588626531200695⟩,
  .shared 129 51 48 ⟨.tilted, 1, 2, false, 213278105671476153⟩], by decide +kernel⟩
private def batch47 : PaidBatch .empty 13 := ⟨[
  .shared 129 52 48 ⟨.tilted, 1, 2, false, 222128616434475640⟩,
  .shared 129 53 49 ⟨.tilted, 1, 2, false, 231138475656110790⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 13) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32, batch33, batch34, batch35, batch36, batch37, batch38, batch39, batch40, batch41, batch42, batch43, batch44, batch45, batch46, batch47]
private abbrev tiles := tilesOf batches

private theorem index39 : checks tiles 129 39 10 = true := by decide +kernel
private theorem index49 : checks tiles 129 49 5 = true := by decide +kernel
private theorem covers : checks tiles 129 39 15 = true :=
  checks_join (index39) index49

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 13)
    (hb : a.b ≤ 129) (hj : a.j ≤ 53) : Covered 13 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top13

end Compact50PriceTableEmpty12
