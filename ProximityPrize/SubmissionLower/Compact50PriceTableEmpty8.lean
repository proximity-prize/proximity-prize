import ProximityPrize.SubmissionLower.LambdaC53TiltedPrice
import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableEmpty8
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top8
private def batch0 : PaidBatch .empty 8 := ⟨[
  .rectangle 8 24 102 31 37,
  .rectangle 11 32 84 39 37,
  .rectangle 14 40 86 47 44,
  .rectangle 16 48 81 53 44,
  .rectangle 82 48 94 51 47,
  .rectangle 82 52 95 53 47], by decide +kernel⟩
private def batch1 : PaidBatch .empty 8 := ⟨[
  .rectangle 85 32 117 36 43,
  .rectangle 85 37 111 40 44,
  .rectangle 87 41 106 43 44,
  .rectangle 87 44 104 46 46,
  .rectangle 87 47 100 49 47,
  .rectangle 95 50 102 50 47], by decide +kernel⟩
private def batch2 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 95 51 100 51 47,
  .rectangle 96 52 98 52 47,
  .rectangle 96 53 97 53 47,
  .rectangle 98 53 99 53 48,
  .rectangle 99 52 101 52 48,
  .point 100 53 48] (by decide +kernel)
private def batch3 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 101 47 109 47 47,
  .rectangle 101 48 107 48 47,
  .rectangle 101 49 104 49 47,
  .point 101 51 47,
  .point 101 53 48,
  .point 102 51 47] (by decide +kernel)
private def batch4 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .point 102 52 48,
  .point 102 53 48,
  .rectangle 103 24 129 29 42,
  .rectangle 103 30 126 34 44,
  .point 103 50 47,
  .point 103 51 47] (by decide +kernel)
private def batch5 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .point 103 52 48,
  .point 103 53 48,
  .point 104 50 47,
  .point 104 51 47,
  .point 104 52 48,
  .point 104 53 48] (by decide +kernel)
private def batch6 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 105 44 111 45 47,
  .rectangle 105 46 111 46 47,
  .point 105 49 47,
  .point 105 50 47,
  .point 105 51 48,
  .point 105 52 48] (by decide +kernel)
private def batch7 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .point 105 53 48,
  .point 106 49 47,
  .point 106 50 47,
  .point 106 51 48,
  .point 106 52 48,
  .shared 106 53 48 ⟨.tilted, 1, 2, true, 184728920096351113⟩] (by decide +kernel)
private def batch8 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 107 41 117 42 46,
  .rectangle 107 43 114 44 47,
  .point 107 49 47,
  .point 107 50 47,
  .point 107 51 48,
  .point 107 52 48] (by decide +kernel)
private def batch9 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 107 53 48 ⟨.tilted, 1, 2, true, 186396125849347005⟩,
  .point 108 48 47,
  .point 108 49 47,
  .point 108 50 47,
  .point 108 51 48,
  .shared 108 52 48 ⟨.tilted, 1, 2, true, 181059087208455956⟩] (by decide +kernel)
private def batch10 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 108 53 48 ⟨.tilted, 1, 2, true, 188063331602342897⟩,
  .point 109 48 47,
  .point 109 49 47,
  .point 109 50 47,
  .point 109 51 48,
  .shared 109 52 48 ⟨.tilted, 1, 2, true, 182661531208708540⟩] (by decide +kernel)
private def batch11 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 109 53 48 ⟨.tilted, 1, 2, true, 189730537355338789⟩,
  .point 110 47 47,
  .point 110 48 47,
  .point 110 49 47,
  .point 110 50 47,
  .point 110 51 48] (by decide +kernel)
private def batch12 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 110 52 48 ⟨.tilted, 1, 2, true, 184263975208961124⟩,
  .shared 110 53 48 ⟨.tilted, 1, 2, true, 191397743108334681⟩,
  .point 111 47 47,
  .point 111 48 47,
  .point 111 49 47,
  .point 111 50 48] (by decide +kernel)
private def batch13 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 111 51 48 ⟨.tilted, 1, 2, true, 178777250714530947⟩,
  .shared 111 52 48 ⟨.tilted, 1, 2, true, 185866419209213708⟩,
  .shared 111 53 48 ⟨.tilted, 1, 2, true, 193064948861330573⟩,
  .rectangle 112 37 129 38 46,
  .rectangle 112 39 123 40 46,
  .rectangle 112 45 114 45 47] (by decide +kernel)
private def batch14 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .point 112 46 47,
  .point 112 47 47,
  .point 112 48 47,
  .point 112 49 47,
  .point 112 50 48,
  .shared 112 51 48 ⟨.tilted, 1, 2, true, 180316215372774215⟩] (by decide +kernel)
private def batch15 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 112 52 48 ⟨.tilted, 1, 2, true, 187468863209466292⟩,
  .shared 112 53 48 ⟨.tilted, 1, 2, true, 194732154614326465⟩,
  .point 113 46 47,
  .point 113 47 47,
  .point 113 48 47,
  .shared 113 49 47 ⟨.tilted, 1, 1, false, 163376524768429103⟩] (by decide +kernel)
private def batch16 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 113 50 48 ⟨.tilted, 1, 2, true, 174752902447319164⟩,
  .shared 113 51 48 ⟨.tilted, 1, 2, true, 181855180031017483⟩,
  .shared 113 52 48 ⟨.tilted, 1, 2, true, 189071307209718876⟩,
  .shared 113 53 48 ⟨.tilted, 1, 2, true, 196399360367322357⟩,
  .point 114 46 47,
  .point 114 47 47] (by decide +kernel)
private def batch17 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .point 114 48 47,
  .shared 114 49 47 ⟨.tilted, 1, 1, false, 164744919885057922⟩,
  .shared 114 50 48 ⟨.tilted, 1, 2, true, 176229670174287108⟩,
  .shared 114 51 48 ⟨.tilted, 1, 2, true, 183394144689260751⟩,
  .shared 114 52 48 ⟨.tilted, 1, 2, true, 190673751209971460⟩,
  .shared 114 53 48 ⟨.tilted, 1, 2, true, 198066566120318249⟩] (by decide +kernel)
private def batch18 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 115 43 120 43 47,
  .rectangle 115 44 117 44 47,
  .point 115 45 47,
  .point 115 46 47,
  .point 115 47 47,
  .shared 115 48 47 ⟨.tilted, 1, 1, false, 159464463095679568⟩] (by decide +kernel)
private def batch19 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 115 49 47 ⟨.tilted, 1, 2, true, 182101277380676361⟩,
  .shared 115 50 48 ⟨.tilted, 1, 2, true, 177706437901255052⟩,
  .shared 115 51 48 ⟨.tilted, 1, 2, true, 184933109347504019⟩,
  .shared 115 52 48 ⟨.tilted, 1, 2, true, 192276195210224044⟩,
  .shared 115 53 48 ⟨.tilted, 1, 2, true, 199733771873314141⟩,
  .point 116 45 47] (by decide +kernel)
private def batch20 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .point 116 46 47,
  .point 116 47 47,
  .shared 116 48 47 ⟨.tilted, 1, 1, false, 160777046617278896⟩,
  .shared 116 49 48 ⟨.tilted, 1, 2, true, 172013957694004745⟩,
  .shared 116 50 48 ⟨.tilted, 1, 2, true, 179183205628222996⟩,
  .shared 116 51 48 ⟨.tilted, 1, 2, true, 186472074005747287⟩] (by decide +kernel)
private def batch21 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 116 52 48 ⟨.tilted, 1, 2, true, 193878639210476628⟩,
  .shared 116 53 48 ⟨.tilted, 1, 2, true, 201400977626310033⟩,
  .point 117 45 47,
  .point 117 46 47,
  .point 117 47 47,
  .shared 117 48 47 ⟨.tilted, 1, 1, false, 162089630138878224⟩] (by decide +kernel)
private def batch22 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 117 49 48 ⟨.tilted, 1, 2, true, 173429810900431357⟩,
  .shared 117 50 48 ⟨.tilted, 1, 2, true, 180659973355190940⟩,
  .shared 117 51 48 ⟨.tilted, 1, 2, true, 188011038663990555⟩,
  .shared 117 52 48 ⟨.tilted, 1, 2, true, 195481083210729212⟩,
  .shared 117 53 48 ⟨.tilted, 1, 2, true, 203068183379305925⟩,
  .rectangle 118 35 127 37 45] (by decide +kernel)
private def batch23 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 118 41 126 41 47,
  .rectangle 118 42 123 42 47,
  .point 118 44 47,
  .point 118 45 47,
  .point 118 46 47,
  .shared 118 47 47 ⟨.tilted, 1, 1, false, 156699990298973476⟩] (by decide +kernel)
private def batch24 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 118 48 47 ⟨.tilted, 1, 1, false, 163402213660477552⟩,
  .shared 118 49 48 ⟨.tilted, 1, 2, true, 174845664106857969⟩,
  .shared 118 50 48 ⟨.tilted, 1, 2, true, 182136741082158884⟩,
  .shared 118 51 48 ⟨.tilted, 1, 2, true, 189550003322233823⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, true, 197083527210981796⟩,
  .shared 118 53 48 ⟨.tilted, 1, 2, true, 204735389132301817⟩] (by decide +kernel)
private def batch25 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .point 119 44 47,
  .point 119 45 47,
  .point 119 46 47,
  .shared 119 47 47 ⟨.tilted, 1, 1, false, 157957884334935555⟩,
  .shared 119 48 47 ⟨.tilted, 1, 1, false, 164714797182076880⟩,
  .shared 119 49 48 ⟨.tilted, 1, 2, true, 176261517313284581⟩] (by decide +kernel)
private def batch26 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 119 50 48 ⟨.tilted, 1, 2, true, 183613508809126828⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, true, 191088967980477091⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, true, 198685971211234380⟩,
  .shared 119 53 48 ⟨.tilted, 1, 2, true, 206402594885297709⟩,
  .point 120 44 47,
  .point 120 45 47] (by decide +kernel)
private def batch27 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .point 120 46 47,
  .shared 120 47 47 ⟨.tilted, 0, 1, false, 159215778370897635⟩,
  .shared 120 48 47 ⟨.tilted, 1, 1, false, 166027380703676208⟩,
  .shared 120 49 48 ⟨.tilted, 1, 2, true, 177677370519711193⟩,
  .shared 120 50 48 ⟨.tilted, 1, 2, true, 185090276536094772⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, true, 192627932638720359⟩] (by decide +kernel)
private def batch28 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 120 52 48 ⟨.tilted, 1, 2, true, 200288415211486964⟩,
  .shared 120 53 48 ⟨.tilted, 1, 2, true, 208069800638293601⟩,
  .point 121 43 47,
  .point 121 44 47,
  .point 121 45 47,
  .shared 121 46 47 ⟨.tilted, 0, 1, false, 153726493410300556⟩] (by decide +kernel)
private def batch29 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 121 47 47 ⟨.tilted, 0, 1, false, 160473672406859714⟩,
  .shared 121 48 47 ⟨.tilted, 1, 1, false, 167339964225275536⟩,
  .shared 121 49 48 ⟨.tilted, 1, 2, true, 179093223726137805⟩,
  .shared 121 50 48 ⟨.tilted, 1, 2, true, 186567044263062716⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, true, 194166897296963627⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, true, 201890859211739548⟩] (by decide +kernel)
private def batch30 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 121 53 48 ⟨.tilted, 1, 2, true, 209737006391289493⟩,
  .point 122 43 47,
  .point 122 44 47,
  .point 122 45 47,
  .shared 122 46 47 ⟨.tilted, 0, 1, false, 154930820070017630⟩,
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 161731566442821794⟩] (by decide +kernel)
private def batch31 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 168652547746874864⟩,
  .shared 122 49 48 ⟨.tilted, 1, 2, true, 180509076932564417⟩,
  .shared 122 50 48 ⟨.tilted, 1, 2, true, 188043811990030660⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, true, 195705861955206895⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, true, 203493303211992132⟩,
  .shared 122 53 48 ⟨.tilted, 1, 2, true, 211404212144285385⟩] (by decide +kernel)
private def batch32 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .point 123 43 47,
  .point 123 44 47,
  .point 123 45 47,
  .shared 123 46 47 ⟨.tilted, 0, 1, false, 156135146729734704⟩,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 162989460478783873⟩,
  .shared 123 48 48 ⟨.tilted, 0, 2, true, 174459801495528424⟩] (by decide +kernel)
private def batch33 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 123 49 48 ⟨.tilted, 1, 2, true, 181924930138991029⟩,
  .shared 123 50 48 ⟨.tilted, 1, 2, true, 189520579716998604⟩,
  .shared 123 51 48 ⟨.tilted, 1, 2, true, 197244826613450163⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, true, 205095747212244716⟩,
  .shared 123 53 48 ⟨.tilted, 1, 2, true, 213071417897281277⟩,
  .rectangle 124 39 129 39 46] (by decide +kernel)
private def batch34 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 124 40 129 40 47,
  .point 124 42 47,
  .point 124 43 47,
  .point 124 44 47,
  .shared 124 45 47 ⟨.tilted, 0, 1, false, 150555754578279362⟩,
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 157339473389451778⟩] (by decide +kernel)
private def batch35 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 164247354514745953⟩,
  .shared 124 48 48 ⟨.tilted, 0, 2, true, 175816022592147696⟩,
  .shared 124 49 48 ⟨.tilted, 1, 2, true, 183340783345417641⟩,
  .shared 124 50 48 ⟨.tilted, 1, 2, true, 190997347443966548⟩,
  .shared 124 51 48 ⟨.tilted, 1, 2, true, 198783791271693431⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, true, 206698191212497300⟩] (by decide +kernel)
private def batch36 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 124 53 48 ⟨.tilted, 1, 2, true, 214738623650277169⟩,
  .point 125 42 47,
  .point 125 43 47,
  .point 125 44 47,
  .shared 125 45 47 ⟨.tilted, 0, 1, false, 151707635971143674⟩,
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 158543800049168852⟩] (by decide +kernel)
private def batch37 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 165505248550708032⟩,
  .shared 125 48 48 ⟨.tilted, 0, 2, true, 177172243688766968⟩,
  .shared 125 49 48 ⟨.tilted, 0, 2, true, 184756636551844253⟩,
  .shared 125 50 48 ⟨.tilted, 1, 2, true, 192474115170934492⟩,
  .shared 125 51 48 ⟨.tilted, 1, 2, true, 200322755929936699⟩,
  .shared 125 52 48 ⟨.tilted, 1, 2, true, 208300635212749884⟩] (by decide +kernel)
private def batch38 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 125 53 48 ⟨.tilted, 1, 2, true, 216405829403273061⟩,
  .point 126 42 47,
  .point 126 43 47,
  .point 126 44 47,
  .shared 126 45 47 ⟨.tilted, 0, 1, false, 152859517364007985⟩,
  .shared 126 46 47 ⟨.tilted, 0, 1, false, 159748126708885926⟩] (by decide +kernel)
private def batch39 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 126 47 47 ⟨.tilted, 0, 1, false, 166763142586670112⟩,
  .shared 126 48 48 ⟨.tilted, 0, 2, true, 178528464785386240⟩,
  .shared 126 49 48 ⟨.tilted, 0, 2, true, 186172489758270865⟩,
  .shared 126 50 48 ⟨.tilted, 1, 2, true, 193950882897902436⟩,
  .shared 126 51 48 ⟨.tilted, 1, 2, true, 201861720588179967⟩,
  .shared 126 52 48 ⟨.tilted, 1, 2, true, 209903079213002468⟩] (by decide +kernel)
private def batch40 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 126 53 48 ⟨.tilted, 1, 2, true, 218073035156268953⟩,
  .rectangle 127 30 129 33 44,
  .rectangle 127 34 129 36 45,
  .point 127 41 47,
  .point 127 42 47,
  .point 127 43 47] (by decide +kernel)
private def batch41 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 127 44 47 ⟨.tilted, 0, 1, false, 147199555951528444⟩,
  .shared 127 45 47 ⟨.tilted, 0, 1, false, 154011398756872297⟩,
  .shared 127 46 47 ⟨.tilted, 0, 1, false, 160952453368603000⟩,
  .shared 127 47 47 ⟨.tilted, 0, 1, false, 168021036622632191⟩,
  .shared 127 48 48 ⟨.tilted, 0, 2, true, 179884685882005512⟩,
  .shared 127 49 48 ⟨.tilted, 0, 2, true, 187588342964697477⟩] (by decide +kernel)
private def batch42 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 127 50 48 ⟨.tilted, 1, 2, true, 195427650624870380⟩,
  .shared 127 51 48 ⟨.tilted, 1, 2, true, 203400685246423235⟩,
  .shared 127 52 48 ⟨.tilted, 1, 2, true, 211505523213255052⟩,
  .shared 127 53 48 ⟨.tilted, 1, 2, true, 219740240909264845⟩,
  .point 128 41 47,
  .point 128 42 47] (by decide +kernel)
private def batch43 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .point 128 43 47,
  .shared 128 44 47 ⟨.tilted, 0, 1, false, 148300114186932236⟩,
  .shared 128 45 47 ⟨.tilted, 0, 1, false, 155163280149736608⟩,
  .shared 128 46 47 ⟨.tilted, 0, 1, false, 162156780028320074⟩,
  .shared 128 47 47 ⟨.tilted, 0, 1, false, 169278930658594271⟩,
  .shared 128 48 48 ⟨.tilted, 0, 2, true, 181240906978624784⟩] (by decide +kernel)
private def batch44 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 128 49 48 ⟨.tilted, 0, 2, true, 189004196171124089⟩,
  .shared 128 50 48 ⟨.tilted, 0, 2, true, 196904418351838324⟩,
  .shared 128 51 48 ⟨.tilted, 1, 2, true, 204939649904666503⟩,
  .shared 128 52 48 ⟨.tilted, 1, 2, true, 213107967213507636⟩,
  .shared 128 53 48 ⟨.tilted, 1, 2, true, 221407446662260737⟩,
  .point 129 41 47] (by decide +kernel)
private def batch45 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .point 129 42 47,
  .point 129 43 47,
  .shared 129 44 47 ⟨.tilted, 0, 1, false, 149400672422336028⟩,
  .shared 129 45 47 ⟨.tilted, 0, 1, false, 156315161542600920⟩,
  .shared 129 46 47 ⟨.tilted, 0, 1, false, 163361106688037148⟩,
  .shared 129 47 47 ⟨.tilted, 0, 1, false, 170536824694556350⟩] (by decide +kernel)
private def batch46 : PaidBatch .empty 8 := LambdaC53TiltedPrice.fastBatch [
  .shared 129 48 48 ⟨.tilted, 0, 2, true, 182597128075244056⟩,
  .shared 129 49 48 ⟨.tilted, 0, 2, true, 190420049377550701⟩,
  .shared 129 50 48 ⟨.tilted, 0, 2, true, 198381186078806268⟩,
  .shared 129 51 48 ⟨.tilted, 1, 2, true, 206478614562909771⟩,
  .shared 129 52 48 ⟨.tilted, 1, 2, true, 214710411213760220⟩,
  .shared 129 53 49 ⟨.tilted, 1, 2, true, 223074652415256629⟩] (by decide +kernel)

private def batches : List (PaidBatch .empty 8) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32, batch33, batch34, batch35, batch36, batch37, batch38, batch39, batch40, batch41, batch42, batch43, batch44, batch45, batch46]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 129 24 10 = true := by decide +kernel
private theorem index34 : checks tiles 129 34 10 = true := by decide +kernel
theorem index44 : checks tiles 129 44 10 = true := by decide +kernel
private theorem covers : checks tiles 129 24 30 = true :=
  checks_join (checks_join (index24) index34) index44

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 129) (hj : a.j ≤ 53) : Covered 8 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9
private def batch0 : PaidBatch .empty 9 := ⟨[
  .rectangle 9 27 94 34 37,
  .rectangle 12 35 78 42 37,
  .rectangle 15 43 80 50 44,
  .rectangle 17 51 85 53 44,
  .rectangle 79 35 111 39 44,
  .rectangle 79 40 103 43 44], by decide +kernel⟩
private def batch1 : PaidBatch .empty 9 := ⟨[
  .rectangle 81 44 99 47 46,
  .rectangle 81 48 93 51 47,
  .rectangle 86 52 94 53 47,
  .rectangle 94 48 101 49 47,
  .rectangle 94 50 101 50 47,
  .rectangle 94 51 99 51 47], by decide +kernel⟩
private def batch2 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 95 27 126 32 43,
  .rectangle 95 33 124 36 44,
  .rectangle 95 52 97 52 47,
  .rectangle 95 53 95 53 47,
  .point 96 53 47,
  .point 97 53 47] (by decide +kernel)
private def batch3 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 98 52 100 52 48,
  .rectangle 98 53 98 53 48,
  .point 99 53 48,
  .rectangle 100 44 111 45 47,
  .rectangle 100 46 106 47 47,
  .point 100 51 47] (by decide +kernel)
private def batch4 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 100 53 48,
  .point 101 51 47,
  .point 101 52 48,
  .point 101 53 48,
  .rectangle 102 48 106 48 47,
  .rectangle 102 49 104 49 47] (by decide +kernel)
private def batch5 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 102 50 47,
  .point 102 51 47,
  .point 102 52 48,
  .point 102 53 48,
  .point 103 50 47,
  .point 103 51 47] (by decide +kernel)
private def batch6 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 103 52 48,
  .point 103 53 48,
  .rectangle 104 40 120 41 46,
  .rectangle 104 42 114 43 46,
  .point 104 50 47,
  .point 104 51 47] (by decide +kernel)
private def batch7 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 104 52 48,
  .point 104 53 48,
  .point 105 49 47,
  .point 105 50 47,
  .point 105 51 48,
  .point 105 52 48] (by decide +kernel)
private def batch8 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 105 53 48 ⟨.tilted, 1, 2, true, 186123567173488460⟩,
  .point 106 49 47,
  .point 106 50 47,
  .point 106 51 48,
  .point 106 52 48,
  .shared 106 53 48 ⟨.tilted, 1, 2, true, 187790772926484352⟩] (by decide +kernel)
private def batch9 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 107 46 111 46 47,
  .rectangle 107 47 108 47 47,
  .point 107 48 47,
  .point 107 49 47,
  .point 107 50 47,
  .point 107 51 48] (by decide +kernel)
private def batch10 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 107 52 48 ⟨.tilted, 1, 2, true, 182294768827328899⟩,
  .shared 107 53 48 ⟨.tilted, 1, 2, true, 189457978679480244⟩,
  .point 108 48 47,
  .point 108 49 47,
  .point 108 50 47,
  .point 108 51 48] (by decide +kernel)
private def batch11 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 108 52 48 ⟨.tilted, 1, 2, true, 183897212827581483⟩,
  .shared 108 53 48 ⟨.tilted, 1, 2, true, 191125184432476136⟩,
  .point 109 47 47,
  .point 109 48 47,
  .point 109 49 47,
  .point 109 50 47] (by decide +kernel)
private def batch12 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 109 51 48,
  .shared 109 52 48 ⟨.tilted, 1, 2, true, 185499656827834067⟩,
  .shared 109 53 48 ⟨.tilted, 1, 2, true, 192792390185472028⟩,
  .point 110 47 47,
  .point 110 48 47,
  .point 110 49 47] (by decide +kernel)
private def batch13 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 110 50 47 ⟨.tilted, 1, 2, true, 181336869653200248⟩,
  .shared 110 51 48 ⟨.tilted, 1, 2, true, 179861180435518189⟩,
  .shared 110 52 48 ⟨.tilted, 1, 2, true, 187102100828086651⟩,
  .shared 110 53 48 ⟨.tilted, 1, 2, true, 194459595938467920⟩,
  .point 111 47 47,
  .point 111 48 47] (by decide +kernel)
private def batch14 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 111 49 47,
  .point 111 50 48,
  .shared 111 51 48 ⟨.tilted, 1, 2, true, 181400145093761457⟩,
  .shared 111 52 48 ⟨.tilted, 1, 2, true, 188704544828339235⟩,
  .shared 111 53 48 ⟨.tilted, 1, 2, true, 196126801691463812⟩,
  .rectangle 112 37 129 38 46] (by decide +kernel)
private def batch15 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 112 39 123 40 46,
  .rectangle 112 44 116 44 47,
  .rectangle 112 45 114 45 47,
  .point 112 46 47,
  .point 112 47 47,
  .point 112 48 47] (by decide +kernel)
private def batch16 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 112 49 47 ⟨.tilted, 1, 1, false, 165212539328043418⟩,
  .shared 112 50 48 ⟨.tilted, 1, 2, true, 175692293830799412⟩,
  .shared 112 51 48 ⟨.tilted, 1, 2, true, 182939109752004725⟩,
  .shared 112 52 48 ⟨.tilted, 1, 2, true, 190306988828591819⟩,
  .shared 112 53 48 ⟨.tilted, 1, 2, true, 197794007444459704⟩,
  .point 113 46 47] (by decide +kernel)
private def batch17 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 113 47 47,
  .point 113 48 47,
  .shared 113 49 47 ⟨.tilted, 1, 1, false, 166591915084980536⟩,
  .shared 113 50 48 ⟨.tilted, 1, 2, true, 177169061557767356⟩,
  .shared 113 51 48 ⟨.tilted, 1, 2, true, 184478074410247993⟩,
  .shared 113 52 48 ⟨.tilted, 1, 2, true, 191909432828844403⟩] (by decide +kernel)
private def batch18 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 113 53 48 ⟨.tilted, 1, 2, true, 199461213197455596⟩,
  .point 114 46 47,
  .point 114 47 47,
  .point 114 48 47,
  .shared 114 49 47 ⟨.tilted, 1, 1, false, 167971290841917654⟩,
  .shared 114 50 48 ⟨.tilted, 1, 2, true, 178645829284735300⟩] (by decide +kernel)
private def batch19 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 114 51 48 ⟨.tilted, 1, 2, true, 186017039068491261⟩,
  .shared 114 52 48 ⟨.tilted, 1, 2, true, 193511876829096987⟩,
  .shared 114 53 48 ⟨.tilted, 1, 2, true, 201128418950451488⟩,
  .rectangle 115 42 122 42 47,
  .rectangle 115 43 119 43 47,
  .point 115 45 47] (by decide +kernel)
private def batch20 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 115 46 47,
  .point 115 47 47,
  .shared 115 48 47 ⟨.tilted, 1, 1, false, 162473545609422659⟩,
  .shared 115 49 47 ⟨.tilted, 1, 1, false, 169350666598854772⟩,
  .shared 115 50 48 ⟨.tilted, 1, 2, true, 180122597011703244⟩,
  .shared 115 51 48 ⟨.tilted, 1, 2, true, 187556003726734529⟩] (by decide +kernel)
private def batch21 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 115 52 48 ⟨.tilted, 1, 2, true, 195114320829349571⟩,
  .shared 115 53 48 ⟨.tilted, 1, 2, true, 202795624703447380⟩,
  .point 116 45 47,
  .point 116 46 47,
  .point 116 47 47,
  .shared 116 48 47 ⟨.tilted, 1, 1, false, 163796628867305039⟩] (by decide +kernel)
private def batch22 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 116 49 48 ⟨.tilted, 1, 2, true, 174231877506783314⟩,
  .shared 116 50 48 ⟨.tilted, 1, 2, true, 181599364738671188⟩,
  .shared 116 51 48 ⟨.tilted, 1, 2, true, 189094968384977797⟩,
  .shared 116 52 48 ⟨.tilted, 1, 2, true, 196716764829602155⟩,
  .shared 116 53 48 ⟨.tilted, 1, 2, true, 204462830456443272⟩,
  .point 117 44 47] (by decide +kernel)
private def batch23 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 117 45 47,
  .point 117 46 47,
  .shared 117 47 47 ⟨.tilted, 1, 1, false, 158250882274261731⟩,
  .shared 117 48 47 ⟨.tilted, 1, 1, false, 165119712125187418⟩,
  .shared 117 49 48 ⟨.tilted, 1, 2, true, 175647730713209926⟩,
  .shared 117 50 48 ⟨.tilted, 1, 2, true, 183076132465639132⟩] (by decide +kernel)
private def batch24 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 117 51 48 ⟨.tilted, 1, 2, true, 190633933043221065⟩,
  .shared 117 52 48 ⟨.tilted, 1, 2, true, 198319208829854739⟩,
  .shared 117 53 48 ⟨.tilted, 1, 2, true, 206130036209439164⟩,
  .point 118 44 47,
  .point 118 45 47,
  .point 118 46 47] (by decide +kernel)
private def batch25 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 118 47 47 ⟨.tilted, 1, 1, false, 159518795142481615⟩,
  .shared 118 48 47 ⟨.tilted, 1, 1, false, 166442795383069798⟩,
  .shared 118 49 48 ⟨.tilted, 1, 2, true, 177063583919636538⟩,
  .shared 118 50 48 ⟨.tilted, 1, 2, true, 184552900192607076⟩,
  .shared 118 51 48 ⟨.tilted, 1, 2, true, 192172897701464333⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, true, 199921652830107323⟩] (by decide +kernel)
private def batch26 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 118 53 48 ⟨.tilted, 1, 2, true, 207797241962435056⟩,
  .point 119 44 47,
  .point 119 45 47,
  .point 119 46 47,
  .shared 119 47 47 ⟨.tilted, 1, 1, false, 160786708010701499⟩,
  .shared 119 48 47 ⟨.tilted, 1, 1, false, 167765878640952177⟩] (by decide +kernel)
private def batch27 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 119 49 48 ⟨.tilted, 1, 2, true, 178479437126063150⟩,
  .shared 119 50 48 ⟨.tilted, 1, 2, true, 186029667919575020⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, true, 193711862359707601⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, true, 201524096830359907⟩,
  .shared 119 53 48 ⟨.tilted, 1, 2, true, 209464447715430948⟩,
  .point 120 43 47] (by decide +kernel)
private def batch28 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 120 44 47,
  .point 120 45 47,
  .shared 120 46 47 ⟨.tilted, 0, 1, false, 155146205487889207⟩,
  .shared 120 47 47 ⟨.tilted, 0, 1, false, 162054620878921383⟩,
  .shared 120 48 47 ⟨.tilted, 1, 1, false, 169088961898834557⟩,
  .shared 120 49 48 ⟨.tilted, 1, 2, true, 179895290332489762⟩] (by decide +kernel)
private def batch29 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 120 50 48 ⟨.tilted, 1, 2, true, 187506435646542964⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, true, 195250827017950869⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, true, 203126540830612491⟩,
  .shared 120 53 48 ⟨.tilted, 1, 2, true, 211131653468426840⟩,
  .rectangle 121 41 126 41 47,
  .point 121 43 47] (by decide +kernel)
private def batch30 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 121 44 47,
  .point 121 45 47,
  .shared 121 46 47 ⟨.tilted, 0, 1, false, 156360070075838839⟩,
  .shared 121 47 47 ⟨.tilted, 0, 1, false, 163322533747141267⟩,
  .shared 121 48 47 ⟨.tilted, 1, 1, false, 170412045156716936⟩,
  .shared 121 49 48 ⟨.tilted, 1, 2, true, 181311143538916374⟩] (by decide +kernel)
private def batch31 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 121 50 48 ⟨.tilted, 1, 2, true, 188983203373510908⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, true, 196789791676194137⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, true, 204728984830865075⟩,
  .shared 121 53 48 ⟨.tilted, 1, 2, true, 212798859221422732⟩,
  .point 122 43 47,
  .point 122 44 47] (by decide +kernel)
private def batch32 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 122 45 47,
  .shared 122 46 47 ⟨.tilted, 0, 1, false, 157573934663788470⟩,
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 164590446615361151⟩,
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 171735128414599316⟩,
  .shared 122 49 48 ⟨.tilted, 1, 2, true, 182726996745342986⟩,
  .shared 122 50 48 ⟨.tilted, 1, 2, true, 190459971100478852⟩] (by decide +kernel)
private def batch33 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 122 51 48 ⟨.tilted, 1, 2, true, 198328756334437405⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, true, 206331428831117659⟩,
  .shared 122 53 48 ⟨.tilted, 1, 2, true, 214466064974418624⟩,
  .point 123 42 47,
  .point 123 43 47,
  .point 123 44 47] (by decide +kernel)
private def batch34 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 123 45 47 ⟨.tilted, 0, 1, false, 151848214141041258⟩,
  .shared 123 46 47 ⟨.tilted, 0, 1, false, 158787799251738102⟩,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 165858359483581035⟩,
  .shared 123 48 48 ⟨.tilted, 0, 2, true, 176487977981750069⟩,
  .shared 123 49 48 ⟨.tilted, 1, 2, true, 184142849951769598⟩,
  .shared 123 50 48 ⟨.tilted, 1, 2, true, 191936738827446796⟩] (by decide +kernel)
private def batch35 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 123 51 48 ⟨.tilted, 1, 2, true, 199867720992680673⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, true, 207933872831370243⟩,
  .shared 123 53 48 ⟨.tilted, 1, 2, true, 216133270727414516⟩,
  .rectangle 124 39 129 39 46,
  .rectangle 124 40 129 40 47,
  .point 124 42 47] (by decide +kernel)
private def batch36 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 124 43 47,
  .point 124 44 47,
  .shared 124 45 47 ⟨.tilted, 0, 1, false, 153009152558112880⟩,
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 160001663839687733⟩,
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 167126272351800919⟩,
  .shared 124 48 48 ⟨.tilted, 0, 2, true, 177844199078369341⟩] (by decide +kernel)
private def batch37 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 124 49 48 ⟨.tilted, 1, 2, true, 185558703158196210⟩,
  .shared 124 50 48 ⟨.tilted, 1, 2, true, 193413506554414740⟩,
  .shared 124 51 48 ⟨.tilted, 1, 2, true, 201406685650923941⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, true, 209536316831622827⟩,
  .shared 124 53 48 ⟨.tilted, 1, 2, false, 215867340168069729⟩,
  .rectangle 125 33 129 35 45] (by decide +kernel)
private def batch38 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 125 36 129 37 46,
  .point 125 42 47,
  .point 125 43 47,
  .point 125 44 47,
  .shared 125 45 47 ⟨.tilted, 0, 1, false, 154170090975184502⟩,
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 161215528427637365⟩] (by decide +kernel)
private def batch39 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 168394185220020803⟩,
  .shared 125 48 48 ⟨.tilted, 0, 2, true, 179200420174988613⟩,
  .shared 125 49 48 ⟨.tilted, 0, 2, true, 186974556364622822⟩,
  .shared 125 50 48 ⟨.tilted, 1, 2, true, 194890274281382684⟩,
  .shared 125 51 48 ⟨.tilted, 1, 2, true, 202945650309167209⟩,
  .shared 125 52 48 ⟨.tilted, 1, 2, true, 211138760831875411⟩] (by decide +kernel)
private def batch40 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 125 53 48 ⟨.tilted, 1, 2, false, 214169474923915130⟩,
  .point 126 42 47,
  .point 126 43 47,
  .shared 126 44 47 ⟨.tilted, 0, 1, false, 148368690382336437⟩,
  .shared 126 45 47 ⟨.tilted, 0, 1, false, 155331029392256124⟩,
  .shared 126 46 47 ⟨.tilted, 0, 1, false, 162429393015586996⟩] (by decide +kernel)
private def batch41 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 126 47 47 ⟨.tilted, 0, 1, false, 169662098088240687⟩,
  .shared 126 48 48 ⟨.tilted, 0, 2, true, 180556641271607885⟩,
  .shared 126 49 48 ⟨.tilted, 0, 2, true, 188390409571049434⟩,
  .shared 126 50 48 ⟨.tilted, 1, 2, true, 196367042008350628⟩,
  .shared 126 51 48 ⟨.tilted, 1, 2, true, 204484614967410477⟩,
  .shared 126 52 48 ⟨.tilted, 1, 2, true, 212741204832127995⟩] (by decide +kernel)
private def batch42 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 126 53 48 ⟨.tilted, 1, 2, false, 215785241770993632⟩,
  .rectangle 127 27 129 31 43,
  .rectangle 127 32 129 35 45,
  .point 127 41 47,
  .point 127 42 47,
  .point 127 43 47] (by decide +kernel)
private def batch43 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 127 44 47 ⟨.tilted, 0, 1, false, 149477824737922292⟩,
  .shared 127 45 47 ⟨.tilted, 0, 1, false, 156491967809327746⟩,
  .shared 127 46 47 ⟨.tilted, 0, 1, false, 163643257603536628⟩,
  .shared 127 47 47 ⟨.tilted, 0, 1, false, 170930010956460571⟩,
  .shared 127 48 48 ⟨.tilted, 0, 2, true, 181912862368227157⟩,
  .shared 127 49 48 ⟨.tilted, 0, 2, true, 189806262777476046⟩] (by decide +kernel)
private def batch44 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 127 50 48 ⟨.tilted, 1, 2, true, 197843809735318572⟩,
  .shared 127 51 48 ⟨.tilted, 1, 2, true, 206023579625653745⟩,
  .shared 127 52 48 ⟨.tilted, 1, 2, true, 214343648832380579⟩,
  .shared 127 53 48 ⟨.tilted, 1, 2, false, 217401008618072134⟩,
  .point 128 41 47,
  .point 128 42 47] (by decide +kernel)
private def batch45 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 128 43 47,
  .shared 128 44 47 ⟨.tilted, 0, 1, false, 150586959093508148⟩,
  .shared 128 45 47 ⟨.tilted, 0, 1, false, 157652906226399368⟩,
  .shared 128 46 47 ⟨.tilted, 0, 1, false, 164857122191486259⟩,
  .shared 128 47 47 ⟨.tilted, 0, 1, false, 172197923824680455⟩,
  .shared 128 48 48 ⟨.tilted, 0, 2, true, 183269083464846429⟩] (by decide +kernel)
private def batch46 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 128 49 48 ⟨.tilted, 0, 2, true, 191222115983902658⟩,
  .shared 128 50 48 ⟨.tilted, 0, 2, true, 199320577462286516⟩,
  .shared 128 51 48 ⟨.tilted, 1, 2, true, 207562544283897013⟩,
  .shared 128 52 48 ⟨.tilted, 1, 2, false, 211601738699274159⟩,
  .shared 128 53 48 ⟨.tilted, 1, 2, false, 219016775465150636⟩,
  .point 129 41 47] (by decide +kernel)
private def batch47 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .point 129 42 47,
  .point 129 43 47,
  .shared 129 44 47 ⟨.tilted, 0, 1, false, 151696093449094003⟩,
  .shared 129 45 47 ⟨.tilted, 0, 1, false, 158813844643470990⟩,
  .shared 129 46 47 ⟨.tilted, 0, 1, false, 166070986779435891⟩,
  .shared 129 47 47 ⟨.tilted, 0, 1, false, 173465836692900339⟩] (by decide +kernel)
private def batch48 : PaidBatch .empty 9 := LambdaC53TiltedPrice.fastBatch [
  .shared 129 48 48 ⟨.tilted, 0, 2, true, 184625304561465701⟩,
  .shared 129 49 48 ⟨.tilted, 0, 2, true, 192637969190329270⟩,
  .shared 129 50 48 ⟨.tilted, 0, 2, true, 200797345189254460⟩,
  .shared 129 51 48 ⟨.tilted, 1, 2, true, 209101508942140281⟩,
  .shared 129 52 48 ⟨.tilted, 1, 2, false, 212446792179623053⟩,
  .shared 129 53 49 ⟨.tilted, 1, 2, false, 220632542312229138⟩] (by decide +kernel)

private def batches : List (PaidBatch .empty 9) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32, batch33, batch34, batch35, batch36, batch37, batch38, batch39, batch40, batch41, batch42, batch43, batch44, batch45, batch46, batch47, batch48]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 129 27 10 = true := by decide +kernel
private theorem index37 : checks tiles 129 37 10 = true := by decide +kernel
theorem index47 : checks tiles 129 47 7 = true := by decide +kernel
private theorem covers : checks tiles 129 27 27 = true :=
  checks_join (checks_join (index27) index37) index47

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 129) (hj : a.j ≤ 53) : Covered 9 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

end Compact50PriceTableEmpty8
