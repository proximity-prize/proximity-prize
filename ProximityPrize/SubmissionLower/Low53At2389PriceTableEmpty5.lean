import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty5
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top5
private def b0 : PaidBatch .empty 5 := ⟨[
  .rectangle 5 15 67 24 24,
  .rectangle 9 25 69 34 30,
  .rectangle 12 35 70 44 35], by decide +kernel⟩
private def b1 : PaidBatch .empty 5 := ⟨[
  .rectangle 15 45 70 53 38,
  .rectangle 68 15 129 19 28,
  .rectangle 68 20 129 24 34], by decide +kernel⟩
private def b2 : PaidBatch .empty 5 := ⟨[
  .rectangle 70 30 99 34 35,
  .rectangle 70 25 129 29 39,
  .rectangle 71 50 85 53 42], by decide +kernel⟩
private def b3 : PaidBatch .empty 5 := ⟨[
  .rectangle 71 35 100 39 40,
  .rectangle 71 40 100 44 44,
  .rectangle 71 45 100 49 47], by decide +kernel⟩
private def b4 : PaidBatch .empty 5 := ⟨[
  .rectangle 86 50 100 51 46,
  .rectangle 86 52 100 53 47,
  .rectangle 100 30 129 34 45], by decide +kernel⟩
private def b5 : PaidBatch .empty 5 := ⟨[
  .rectangle 101 50 104 51 48,
  .rectangle 101 52 104 52 48,
  .rectangle 101 53 104 53 48], by decide +kernel⟩
private def b6 : PaidBatch .empty 5 := ⟨[
  .rectangle 101 45 108 47 47,
  .rectangle 101 48 108 49 48,
  .rectangle 101 40 115 42 46], by decide +kernel⟩
private def b7 : PaidBatch .empty 5 := ⟨[
  .rectangle 101 43 115 44 47,
  .rectangle 101 35 129 37 46,
  .rectangle 101 38 129 39 47], by decide +kernel⟩
private def b8 : PaidBatch .empty 5 := ⟨[
  .rectangle 105 52 105 52 48,
  .rectangle 105 51 106 51 48,
  .rectangle 105 53 106 53 49], by decide +kernel⟩
private def b9 : PaidBatch .empty 5 := ⟨[
  .rectangle 105 50 108 50 48,
  .point 106 52 45,
  .rectangle 107 51 107 51 48], by decide +kernel⟩
private def b10 : PaidBatch .empty 5 := ⟨[
  .point 107 52 46,
  .point 107 53 46,
  .point 108 51 45], by decide +kernel⟩
private def b11 : PaidBatch .empty 5 := ⟨[
  .point 108 52 46,
  .point 108 53 47,
  .rectangle 109 50 109 50 48], by decide +kernel⟩
private def b12 : PaidBatch .empty 5 := ⟨[
  .point 109 51 46,
  .point 109 52 47,
  .point 109 53 47], by decide +kernel⟩
private def b13 : PaidBatch .empty 5 := ⟨[
  .rectangle 109 49 110 49 48,
  .rectangle 109 48 112 48 48,
  .rectangle 109 45 115 46 48], by decide +kernel⟩
private def b14 : PaidBatch .empty 5 := ⟨[
  .rectangle 109 47 115 47 48,
  .point 110 50 45,
  .point 110 51 46], by decide +kernel⟩
private def b15 : PaidBatch .empty 5 := ⟨[
  .point 110 52 47,
  .point 110 53 48,
  .rectangle 111 49 111 49 48], by decide +kernel⟩
private def b16 : PaidBatch .empty 5 := ⟨[
  .point 111 50 46,
  .point 111 51 47,
  .point 111 52 47], by decide +kernel⟩
private def b17 : PaidBatch .empty 5 := ⟨[
  .point 111 53 48,
  .point 112 49 45,
  .point 112 50 46], by decide +kernel⟩
private def b18 : PaidBatch .empty 5 := ⟨[
  .point 112 51 47,
  .point 112 52 48,
  .point 112 53 49], by decide +kernel⟩
private def b19 : PaidBatch .empty 5 := ⟨[
  .rectangle 113 48 113 48 48,
  .point 113 49 46,
  .point 113 50 47], by decide +kernel⟩
private def b20 : PaidBatch .empty 5 := ⟨[
  .point 113 51 48,
  .point 113 52 48,
  .point 113 53 49], by decide +kernel⟩
private def b21 : PaidBatch .empty 5 := ⟨[
  .point 114 48 45,
  .point 114 49 46,
  .point 114 50 47], by decide +kernel⟩
private def b22 : PaidBatch .empty 5 := ⟨[
  .point 114 51 48,
  .point 114 52 49,
  .shared 114 53 33 ⟨.tilted, 1, 2, true, 184239446888339460⟩], by decide +kernel⟩
private def b23 : PaidBatch .empty 5 := ⟨[
  .point 115 48 46,
  .point 115 49 47,
  .point 115 50 48], by decide +kernel⟩
private def b24 : PaidBatch .empty 5 := ⟨[
  .point 115 51 48,
  .point 115 52 49,
  .shared 115 53 34 ⟨.tilted, 1, 2, true, 185906627656863536⟩], by decide +kernel⟩
private def b25 : PaidBatch .empty 5 := ⟨[
  .point 116 47 45,
  .point 116 48 46,
  .point 116 49 47], by decide +kernel⟩
private def b26 : PaidBatch .empty 5 := ⟨[
  .point 116 50 48,
  .point 116 51 49,
  .shared 116 52 33 ⟨.tilted, 1, 2, true, 180875679501171826⟩], by decide +kernel⟩
private def b27 : PaidBatch .empty 5 := ⟨[
  .shared 116 53 34 ⟨.tilted, 1, 2, true, 187573808425387612⟩,
  .rectangle 116 46 117 46 48,
  .rectangle 116 45 119 45 48], by decide +kernel⟩
private def b28 : PaidBatch .empty 5 := ⟨[
  .rectangle 116 40 122 41 46,
  .rectangle 116 42 122 42 46,
  .rectangle 116 43 122 43 47], by decide +kernel⟩
private def b29 : PaidBatch .empty 5 := ⟨[
  .rectangle 116 44 122 44 48,
  .point 117 47 46,
  .point 117 48 47], by decide +kernel⟩
private def b30 : PaidBatch .empty 5 := ⟨[
  .point 117 49 47,
  .point 117 50 48,
  .point 117 51 49], by decide +kernel⟩
private def b31 : PaidBatch .empty 5 := ⟨[
  .shared 117 52 34 ⟨.tilted, 1, 2, true, 182478099487461674⟩,
  .shared 117 53 35 ⟨.tilted, 1, 2, true, 189240989193911688⟩,
  .point 118 46 45], by decide +kernel⟩
private def b32 : PaidBatch .empty 5 := ⟨[
  .point 118 47 46,
  .point 118 48 47,
  .point 118 49 48], by decide +kernel⟩
private def b33 : PaidBatch .empty 5 := ⟨[
  .shared 118 50 32 ⟨.tilted, 1, 2, true, 170705688267048697⟩,
  .shared 118 51 33 ⟨.tilted, 1, 2, true, 177345717712864503⟩,
  .shared 118 52 34 ⟨.tilted, 1, 2, true, 184080519473751522⟩], by decide +kernel⟩
private def b34 : PaidBatch .empty 5 := ⟨[
  .shared 118 53 35 ⟨.tilted, 1, 2, true, 190908169962435764⟩,
  .point 119 46 46,
  .point 119 47 46], by decide +kernel⟩
private def b35 : PaidBatch .empty 5 := ⟨[
  .point 119 48 47,
  .point 119 49 48,
  .shared 119 50 33 ⟨.tilted, 1, 2, true, 172182433863418065⟩], by decide +kernel⟩
private def b36 : PaidBatch .empty 5 := ⟨[
  .shared 119 51 34 ⟨.tilted, 1, 2, true, 178884659308436115⟩,
  .shared 119 52 35 ⟨.tilted, 1, 2, true, 185682939460041370⟩,
  .shared 119 53 36 ⟨.tilted, 1, 2, true, 192575350730959840⟩], by decide +kernel⟩
private def b37 : PaidBatch .empty 5 := ⟨[
  .rectangle 120 45 120 45 48,
  .point 120 46 46,
  .point 120 47 47], by decide +kernel⟩
private def b38 : PaidBatch .empty 5 := ⟨[
  .point 120 48 48,
  .shared 120 49 32 ⟨.tilted, 1, 2, true, 166994018700944322⟩,
  .shared 120 50 33 ⟨.tilted, 1, 2, true, 173659179459787433⟩], by decide +kernel⟩
private def b39 : PaidBatch .empty 5 := ⟨[
  .shared 120 51 34 ⟨.tilted, 1, 2, true, 180423600904007727⟩,
  .shared 120 52 35 ⟨.tilted, 1, 2, true, 187285359446331218⟩,
  .shared 120 53 37 ⟨.tilted, 1, 2, true, 194242531499483916⟩], by decide +kernel⟩
private def b40 : PaidBatch .empty 5 := ⟨[
  .point 121 45 45,
  .point 121 46 46,
  .point 121 47 47], by decide +kernel⟩
private def b41 : PaidBatch .empty 5 := ⟨[
  .point 121 48 48,
  .shared 121 49 32 ⟨.tilted, 1, 2, true, 168409850689627438⟩,
  .shared 121 50 34 ⟨.tilted, 1, 2, true, 175135925056156801⟩], by decide +kernel⟩
private def b42 : PaidBatch .empty 5 := ⟨[
  .shared 121 51 35 ⟨.tilted, 1, 2, true, 181962542499579339⟩,
  .shared 121 52 36 ⟨.tilted, 1, 2, true, 188887779432621066⟩,
  .shared 121 53 37 ⟨.tilted, 1, 2, true, 195909712268007992⟩], by decide +kernel⟩
private def b43 : PaidBatch .empty 5 := ⟨[
  .point 122 45 46,
  .point 122 46 47,
  .point 122 47 48], by decide +kernel⟩
private def b44 : PaidBatch .empty 5 := ⟨[
  .shared 122 48 37 ⟨.tilted, 0, 1, false, 146300291836320780⟩,
  .shared 122 49 33 ⟨.tilted, 1, 2, true, 169825682678310554⟩,
  .shared 122 50 34 ⟨.tilted, 1, 2, true, 176612670652526169⟩], by decide +kernel⟩
private def b45 : PaidBatch .empty 5 := ⟨[
  .shared 122 51 35 ⟨.tilted, 1, 2, true, 183501484095150951⟩,
  .shared 122 52 37 ⟨.tilted, 1, 2, true, 190490199418910914⟩,
  .shared 122 53 38 ⟨.tilted, 1, 2, true, 197576893036532068⟩], by decide +kernel⟩
private def b46 : PaidBatch .empty 5 := ⟨[
  .point 123 44 45,
  .point 123 45 46,
  .point 123 46 47], by decide +kernel⟩
private def b47 : PaidBatch .empty 5 := ⟨[
  .point 123 47 48,
  .shared 123 48 32 ⟨.tilted, 0, 2, true, 164498644532290952⟩,
  .shared 123 49 34 ⟨.tilted, 1, 2, true, 171241514666993670⟩], by decide +kernel⟩
private def b48 : PaidBatch .empty 5 := ⟨[
  .shared 123 50 35 ⟨.tilted, 1, 2, true, 178089416248895537⟩,
  .shared 123 51 36 ⟨.tilted, 1, 2, true, 185040425690722563⟩,
  .shared 123 52 37 ⟨.tilted, 1, 2, true, 192092619405200762⟩], by decide +kernel⟩
private def b49 : PaidBatch .empty 5 := ⟨[
  .shared 123 53 39 ⟨.tilted, 1, 2, true, 199244073805056144⟩,
  .rectangle 123 43 124 43 48,
  .rectangle 123 42 126 42 48], by decide +kernel⟩
private def b50 : PaidBatch .empty 5 := ⟨[
  .rectangle 123 40 129 40 47,
  .rectangle 123 41 129 41 48,
  .point 124 44 45], by decide +kernel⟩
private def b51 : PaidBatch .empty 5 := ⟨[
  .point 124 45 46,
  .point 124 46 47,
  .point 124 47 48], by decide +kernel⟩
private def b52 : PaidBatch .empty 5 := ⟨[
  .shared 124 48 33 ⟨.tilted, 0, 2, true, 165854845304803808⟩,
  .shared 124 49 34 ⟨.tilted, 1, 2, true, 172657346655676786⟩,
  .shared 124 50 35 ⟨.tilted, 1, 2, true, 179566161845264905⟩], by decide +kernel⟩
private def b53 : PaidBatch .empty 5 := ⟨[
  .shared 124 51 37 ⟨.tilted, 1, 2, true, 186579367286294175⟩,
  .shared 124 52 38 ⟨.tilted, 1, 2, true, 193695039391490610⟩,
  .shared 124 53 39 ⟨.tilted, 1, 2, true, 200911254573580220⟩], by decide +kernel⟩
private def b54 : PaidBatch .empty 5 := ⟨[
  .rectangle 125 43 125 43 48,
  .point 125 44 46,
  .point 125 45 47], by decide +kernel⟩
private def b55 : PaidBatch .empty 5 := ⟨[
  .point 125 46 48,
  .shared 125 47 37 ⟨.tilted, 0, 1, false, 144091131400387377⟩,
  .shared 125 48 33 ⟨.tilted, 0, 2, true, 167211046077316664⟩], by decide +kernel⟩
private def b56 : PaidBatch .empty 5 := ⟨[
  .shared 125 49 35 ⟨.tilted, 0, 2, true, 174073178644359902⟩,
  .shared 125 50 36 ⟨.tilted, 1, 2, true, 181042907441634273⟩,
  .shared 125 51 37 ⟨.tilted, 1, 2, true, 188118308881865787⟩], by decide +kernel⟩
private def b57 : PaidBatch .empty 5 := ⟨[
  .shared 125 52 39 ⟨.tilted, 1, 2, true, 195297459377780458⟩,
  .shared 125 53 40 ⟨.tilted, 1, 2, true, 202578435342104296⟩,
  .point 126 43 45], by decide +kernel⟩
private def b58 : PaidBatch .empty 5 := ⟨[
  .point 126 44 46,
  .point 126 45 47,
  .point 126 46 48], by decide +kernel⟩
private def b59 : PaidBatch .empty 5 := ⟨[
  .shared 126 47 37 ⟨.tilted, 0, 1, false, 145231605445097973⟩,
  .shared 126 48 34 ⟨.tilted, 0, 2, true, 168567246849829520⟩,
  .shared 126 49 35 ⟨.tilted, 0, 2, true, 175489010633043018⟩], by decide +kernel⟩
private def b60 : PaidBatch .empty 5 := ⟨[
  .shared 126 50 37 ⟨.tilted, 1, 2, true, 182519653038003641⟩,
  .shared 126 51 38 ⟨.tilted, 1, 2, true, 189657250477437399⟩,
  .shared 126 52 39 ⟨.tilted, 1, 2, true, 196899879364070306⟩], by decide +kernel⟩
private def b61 : PaidBatch .empty 5 := ⟨[
  .shared 126 53 41 ⟨.tilted, 1, 2, true, 204245616110628372⟩,
  .rectangle 127 42 127 42 48,
  .point 127 43 46], by decide +kernel⟩
private def b62 : PaidBatch .empty 5 := ⟨[
  .point 127 44 47,
  .point 127 45 48,
  .shared 127 46 37 ⟨.tilted, 0, 1, false, 140590851498652477⟩], by decide +kernel⟩
private def b63 : PaidBatch .empty 5 := ⟨[
  .shared 127 47 38 ⟨.tilted, 0, 1, false, 146372079489808569⟩,
  .shared 127 48 34 ⟨.tilted, 0, 2, true, 169923447622342376⟩,
  .shared 127 49 36 ⟨.tilted, 0, 2, true, 176904842621726134⟩], by decide +kernel⟩
private def b64 : PaidBatch .empty 5 := ⟨[
  .shared 127 50 37 ⟨.tilted, 1, 2, true, 183996398634373009⟩,
  .shared 127 51 39 ⟨.tilted, 1, 2, true, 191196192073009011⟩,
  .shared 127 52 40 ⟨.tilted, 1, 2, true, 198502299350360154⟩], by decide +kernel⟩
private def b65 : PaidBatch .empty 5 := ⟨[
  .shared 127 53 41 ⟨.tilted, 1, 2, true, 205912796879152448⟩,
  .point 128 42 45,
  .point 128 43 46], by decide +kernel⟩
private def b66 : PaidBatch .empty 5 := ⟨[
  .point 128 44 47,
  .point 128 45 48,
  .shared 128 46 37 ⟨.tilted, 0, 1, false, 141684144210426238⟩], by decide +kernel⟩
private def b67 : PaidBatch .empty 5 := ⟨[
  .shared 128 47 38 ⟨.tilted, 0, 1, false, 147512553534519165⟩,
  .shared 128 48 35 ⟨.tilted, 0, 2, true, 171279648394855232⟩,
  .shared 128 49 36 ⟨.tilted, 0, 2, true, 178320674610409250⟩], by decide +kernel⟩
private def b68 : PaidBatch .empty 5 := ⟨[
  .shared 128 50 38 ⟨.tilted, 0, 2, true, 185473144230742377⟩,
  .shared 128 51 39 ⟨.tilted, 1, 2, true, 192735133668580623⟩,
  .shared 128 52 41 ⟨.tilted, 1, 2, true, 200104719336650002⟩], by decide +kernel⟩
private def b69 : PaidBatch .empty 5 := ⟨[
  .shared 128 53 42 ⟨.tilted, 1, 2, true, 207579977647676524⟩,
  .point 129 42 45,
  .point 129 43 46], by decide +kernel⟩
private def b70 : PaidBatch .empty 5 := ⟨[
  .point 129 44 47,
  .point 129 45 48,
  .shared 129 46 38 ⟨.tilted, 0, 1, false, 142777436922199999⟩], by decide +kernel⟩
private def b71 : PaidBatch .empty 5 := ⟨[
  .shared 129 47 39 ⟨.tilted, 0, 1, false, 148653027579229761⟩,
  .shared 129 48 36 ⟨.tilted, 0, 2, true, 172635849167368088⟩,
  .shared 129 49 37 ⟨.tilted, 0, 2, true, 179736506599092366⟩], by decide +kernel⟩
private def b72 : PaidBatch .empty 5 := ⟨[
  .shared 129 50 38 ⟨.tilted, 0, 2, true, 186949889827111745⟩,
  .shared 129 51 40 ⟨.tilted, 1, 2, true, 194274075264152235⟩,
  .shared 129 52 41 ⟨.tilted, 1, 2, true, 201707139322939850⟩], by decide +kernel⟩
private def b73 : PaidBatch .empty 5 := ⟨[
  .shared 129 53 43 ⟨.tilted, 1, 2, true, 209247158416200600⟩], by decide +kernel⟩
private def batches : List (PaidBatch .empty 5) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 129 15 2 = true := by decide +kernel
private theorem i17 : checks tiles 129 17 2 = true := by decide +kernel
private theorem i19 : checks tiles 129 19 2 = true := by decide +kernel
private theorem i21 : checks tiles 129 21 2 = true := by decide +kernel
private theorem i23 : checks tiles 129 23 2 = true := by decide +kernel
private theorem i25 : checks tiles 129 25 2 = true := by decide +kernel
private theorem i27 : checks tiles 129 27 2 = true := by decide +kernel
private theorem i29 : checks tiles 129 29 2 = true := by decide +kernel
private theorem i31 : checks tiles 129 31 2 = true := by decide +kernel
private theorem i33 : checks tiles 129 33 2 = true := by decide +kernel
private theorem i35 : checks tiles 129 35 2 = true := by decide +kernel
private theorem i37 : checks tiles 129 37 2 = true := by decide +kernel
private theorem i39 : checks tiles 129 39 2 = true := by decide +kernel
private theorem i41 : checks tiles 129 41 2 = true := by decide +kernel
private theorem i43 : checks tiles 129 43 2 = true := by decide +kernel
private theorem i45 : checks tiles 129 45 2 = true := by decide +kernel
private theorem i47 : checks tiles 129 47 2 = true := by decide +kernel
private theorem i49 : checks tiles 129 49 2 = true := by decide +kernel
private theorem i51 : checks tiles 129 51 2 = true := by decide +kernel
private theorem i53 : checks tiles 129 53 1 = true := by decide +kernel
def receipt : Certificate .empty 5 := ⟨batches, checks_join i15 (checks_join i17 (checks_join i19 (checks_join i21 (checks_join i23 (checks_join i25 (checks_join i27 (checks_join i29 (checks_join i31 (checks_join i33 (checks_join i35 (checks_join i37 (checks_join i39 (checks_join i41 (checks_join i43 (checks_join i45 (checks_join i47 (checks_join i49 (checks_join i51 i53))))))))))))))))))⟩
end Top5


end Low53At2389PriceTableEmpty5
