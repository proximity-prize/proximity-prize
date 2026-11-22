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

namespace Top1
private abbrev P := PaidBatch .empty 1
private def cross0 : P := ⟨unpack [10049885345], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross1 : P := ⟨unpack [17549370381], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross2 : P := ⟨unpack [18455995497], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross3 : P := ⟨unpack [47732762013], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross4 : P := ⟨unpack [51909638165], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross5 : P := ⟨unpack [22096656497], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross6 : P := ⟨unpack [26761246985], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross7 : P := ⟨unpack [26408865905], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross8 : P := ⟨unpack [26795595021], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross9 : P := ⟨unpack [25822844421], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross10 : P := ⟨unpack [60684921893], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross11 : P := ⟨unpack [39277915309], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross12 : P := ⟨unpack [22098112837], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross13 : P := ⟨unpack [21695853021], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross14 : P := ⟨unpack [17719527749], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross15 : P := ⟨unpack [17484843465], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross16 : P := ⟨unpack [26443682989], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross17 : P := ⟨unpack [56625965113], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross18 : P := ⟨unpack [17535114577], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross19 : P := ⟨unpack [4583238057], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross20 : P := ⟨unpack [4398688753], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross21 : P := ⟨unpack [4314802701], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross22 : P := ⟨unpack [34681499897], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross23 : P := ⟨unpack [17451364681], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross24 : P := ⟨unpack [13072516425], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def cross25 : P := ⟨unpack [9314424057], Compact54EmptyTilt.paid (by decide +kernel)⟩
private def p3_0 : List P := [
  ⟨unpack [2197883909,704712713,4496364553,402723901,167843901,1191385193], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross0,
  ⟨unpack [10049884341], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs3 : List P := p3_0
private theorem row3 : checks (tilesOf bs3) 132 3 4 = true := by decide +kernel
private def p7_0 : List P := [
  ⟨unpack [4412480525], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross1,
  ⟨unpack [100736045,251797549,688069705], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross2,
  ⟨unpack [1325801581], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross0,
  cross3,
  ⟨unpack [420815277,68492801], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs7 : List P := p7_0
private theorem row7 : checks (tilesOf bs7) 132 7 4 = true := by decide +kernel
private def p11_0 : List P := [
  cross1,
  cross4,
  cross2,
  cross5,
  cross6,
  cross3]
private def bs11 : List P := p11_0
private theorem row11 : checks (tilesOf bs11) 132 11 4 = true := by decide +kernel
private def p15_0 : List P := [
  cross4,
  cross5,
  cross6,
  cross3]
private def bs15 : List P := p15_0
private theorem row15 : checks (tilesOf bs15) 132 15 4 = true := by decide +kernel
private def p19_0 : List P := [
  cross4,
  cross5,
  cross7,
  cross6,
  cross8,
  cross3,
  cross9]
private def bs19 : List P := p19_0
private theorem row19 : checks (tilesOf bs19) 132 19 4 = true := by decide +kernel
private def p23_0 : List P := [
  cross4,
  cross7,
  cross8,
  cross9]
private def bs23 : List P := p23_0
private theorem row23 : checks (tilesOf bs23) 132 23 4 = true := by decide +kernel
private def p27_0 : List P := [
  cross10,
  cross11,
  cross8,
  cross12,
  cross13,
  cross9]
private def bs27 : List P := p27_0
private theorem row27 : checks (tilesOf bs27) 132 27 4 = true := by decide +kernel
private def p31_0 : List P := [
  cross10,
  cross11,
  cross12,
  cross14,
  cross15,
  cross13]
private def bs31 : List P := p31_0
private theorem row31 : checks (tilesOf bs31) 132 31 4 = true := by decide +kernel
private def p35_0 : List P := [
  cross10,
  cross11,
  cross16,
  cross14,
  cross15]
private def bs35 : List P := p35_0
private theorem row35 : checks (tilesOf bs35) 132 35 4 = true := by decide +kernel
private def p39_0 : List P := [
  cross10,
  cross17,
  cross16,
  cross18,
  ⟨unpack [8911691177], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross19,
  cross20,
  ⟨unpack [8693652985], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p39_1 : List P := [
  cross21]
private def bs39 : List P := p39_0 ++ p39_1
private theorem row39 : checks (tilesOf bs39) 132 39 4 = true := by decide +kernel
private def p43_0 : List P := [
  cross17,
  cross16,
  cross22,
  cross23,
  cross18,
  ⟨unpack [8794321293], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross19,
  ⟨unpack [4415467969,103725505,70236637,120500705,53392865], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p43_1 : List P := [
  cross20,
  ⟨unpack [53458417,3127793,3127797,3127800,3127804,70234625,19904001,3127808], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3127812,3126793,3127816], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  cross21,
  ⟨unpack [19904012,19904016], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs43 : List P := p43_0 ++ p43_1
private theorem row43 : checks (tilesOf bs43) 132 43 4 = true := by decide +kernel
private def p47_0 : List P := [
  cross17,
  cross22,
  cross23,
  cross24,
  ⟨unpack [4432250233,4432248205,4365206941,103726513,103793073,53462449,19909041,3131833], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3131836,19908033,3131840,3131844,19908040,53460429,19907021,19908044], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [19908048,3129813,19908052,36684248,19906013,36684252,36684256,53460452], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [53460456,53460460,53460464,53460468,53460472,53460476,53460480,53460484], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p47_1 : List P := [
  ⟨unpack [53460488,53460492,53460496], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs47 : List P := p47_0 ++ p47_1
private theorem row47 : checks (tilesOf bs47) 132 47 4 = true := by decide +kernel
private def p51_0 : List P := [
  cross17,
  cross22,
  cross25,
  cross24,
  ⟨unpack [4398763385,70241685,36688277,3133857,3133861,19910057,3133864,4348433833], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3133868,19910064,19910068,19910072,36689337,3135928,19910076,3135932], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [19910080,3135936,53464516,53464520,53464524,53464528,53464532,53464536], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [53464540,53464544,53464548,53464552,53464556,53464560,53464564,53464568], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def p51_1 : List P := [
  ⟨unpack [53464572,53464576,53464580,53464584,53464588,53464592], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs51 : List P := p51_0 ++ p51_1
private theorem row51 : checks (tilesOf bs51) 132 51 4 = true := by decide +kernel
private def p55_0 : List P := [
  cross17,
  cross25,
  ⟨unpack [3136937,3136940,3136944,3136948,3136952,3136956,3136960,3136964], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3136968,3136972,3136976,3136980,3136984,3136988,3136992,3136996], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3137000,3137004,3137008,3137012,3137016,3137020,3137024,3202564], Compact54EmptyTilt.paid (by decide +kernel)⟩,
  ⟨unpack [3202568,3202572,3202576], Compact54EmptyTilt.paid (by decide +kernel)⟩]
private def bs55 : List P := p55_0
private theorem row55 : checks (tilesOf bs55) 132 55 1 = true := by decide +kernel

theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤132) (hj : a.j≤55) :
    Covered 1 .empty a := by
  have h3 : 3 ≤ a.j := by simpa only [ht] using ha.2.1
  rcases lt_or_ge a.j 7 with h7 | h7
  · exact apply_batches (batches := bs3) row3 a ha ht hb h3 h7
  rcases lt_or_ge a.j 11 with h11 | h11
  · exact apply_batches (batches := bs7) row7 a ha ht hb h7 h11
  rcases lt_or_ge a.j 15 with h15 | h15
  · exact apply_batches (batches := bs11) row11 a ha ht hb h11 h15
  rcases lt_or_ge a.j 19 with h19 | h19
  · exact apply_batches (batches := bs15) row15 a ha ht hb h15 h19
  rcases lt_or_ge a.j 23 with h23 | h23
  · exact apply_batches (batches := bs19) row19 a ha ht hb h19 h23
  rcases lt_or_ge a.j 27 with h27 | h27
  · exact apply_batches (batches := bs23) row23 a ha ht hb h23 h27
  rcases lt_or_ge a.j 31 with h31 | h31
  · exact apply_batches (batches := bs27) row27 a ha ht hb h27 h31
  rcases lt_or_ge a.j 35 with h35 | h35
  · exact apply_batches (batches := bs31) row31 a ha ht hb h31 h35
  rcases lt_or_ge a.j 39 with h39 | h39
  · exact apply_batches (batches := bs35) row35 a ha ht hb h35 h39
  rcases lt_or_ge a.j 43 with h43 | h43
  · exact apply_batches (batches := bs39) row39 a ha ht hb h39 h43
  rcases lt_or_ge a.j 47 with h47 | h47
  · exact apply_batches (batches := bs43) row43 a ha ht hb h43 h47
  rcases lt_or_ge a.j 51 with h51 | h51
  · exact apply_batches (batches := bs47) row47 a ha ht hb h47 h51
  rcases lt_or_ge a.j 55 with h55 | h55
  · exact apply_batches (batches := bs51) row51 a ha ht hb h51 h55
  exact apply_batches (batches := bs55) row55 a ha ht hb h55 (Nat.lt_succ_of_le hj)
end Top1

end Compact50PriceTableEmpty
