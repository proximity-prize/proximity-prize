import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass33

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group33
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [32234408967, 49382173715, 87215201315, 27639525439, 43812609375, 35155708255], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30709820767, 17388711419, 8782004735, 34484194831, 47352525331, 30122543647], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17237715487], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 138 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 138 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 138 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤138) (hj : a.j≤50) :
    Covered orders a ∨ Low6966Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [40909150219, 49348886555, 87064277035, 6265422919, 35340185923, 35071825219], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17959139651, 21733938671, 13144075759, 4487036415, 43057562131, 34467769875], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [57853471, 1099569482271, 42973534759], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i6 : checks (tilesOf batches) 138 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 138 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 138 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤138) (hj : a.j≤50) :
    Covered orders a ∨ Low6966Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [45204513807, 53358710815, 74196223023, 30911071563, 26398008651, 9335652683], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43309289939, 30424530387, 13194405347, 8815556067, 1099703697919, 1099703698943], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099703699967, 12976234007, 4369593883, 74628635, 47251793451, 38662002219], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25777241643, 17187314219], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 138 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 138 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 138 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤138) (hj : a.j≤50) :
    Covered orders a ∨ Low6966Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [49331908627, 61596393507, 48611040311, 17808072063, 17623593343, 4805805439], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39299539331, 26398001539, 4570919403, 4487035371, 1099787583979, 1099720476155], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099720477179, 47402791431, 8681334295, 21549386267, 8664490523, 74627611], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099586256411, 34417435167, 21532608031], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 138 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 138 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 138 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤138) (hj : a.j≤50) :
    Covered orders a ∨ Low6966Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [49332042775, 61495798823, 35793250363, 35105303919, 22170145135, 13345335699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13194410387, 1100156684691, 4487035359, 1099837915615, 1099837916639, 8748444163], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4386371075, 43091115531, 34501323275, 1099636588047, 17271198231, 8681334295], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [74626587, 1099586255387, 17220865571, 7516715], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 138 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 138 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 138 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤138) (hj : a.j≤50) :
    Covered orders a ∨ Low6966Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [45154584603, 61395137579, 27236872255, 30944556379, 22186923355, 17724255579], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8815559071, 1099871470039, 1099871471063, 1099871472087, 8815554015, 4453480927], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13043340807, 8748443143, 1099670141447, 1099670142471, 91402775, 91403799], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [42956966443], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 138 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 138 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 138 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤138) (hj : a.j≤50) :
    Covered orders a ∨ Low6966Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [49198027807, 52855604271, 18697271363, 26515441003, 17757741419, 13345404267], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100039243183, 1100039244207, 4520588763, 1099854691803, 1099854692827, 38896883187], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26012122611, 8815485431, 4520586743, 108181011, 1099619809811, 12942678559], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i21 : checks (tilesOf batches) 138 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 138 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 138 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 138 45 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤138) (hj : a.j≤50) :
    Covered orders a ∨ Low6966Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [49047035939, 52755009587, 5963433031, 22270808407, 17724189015, 13311851863], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099972132287, 1099972133311, 39031169491, 21851376083, 1099871471063, 1099871472087], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8882661851, 4503811547, 124958223, 1099636587023, 8681267735, 4336037411], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i24 : checks (tilesOf batches) 138 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 138 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 138 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 138 48 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤138) (hj : a.j≤50) :
    Covered orders a ∨ Low6966Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [48929664039, 48409713719, 17959066959, 17673924943, 4839359823, 34836868539], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17657074107, 4671582663, 4537366983, 1099938578887, 1099888248275, 1099888249299], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099686918659, 1099686919683, 8731665931, 41071139, 41072163], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤138) (hj : a.j≤50) :
    Covered orders a ∨ Low6966Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [52989818923, 31397620799, 13378956671, 8949775743, 1100240570751, 30760008071], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17808071047, 1099871469015, 1099871470039, 1099871471063, 4520586743, 225621495], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099737250295, 12942678559, 4352813599], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤138) (hj : a.j≤50) :
    Covered orders a ∨ Low6966Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [52855604271, 18663716931, 26582549867, 17808073067, 13345404267, 1100072797607], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100072798631, 4554143195, 1099854691803, 1099854692827, 13026566659, 4453478915], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099586255387, 12909191719, 7516715, 7517739], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤138) (hj : a.j≤50) :
    Covered orders a ∨ Low6966Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [48543928371, 10224844867, 22270808427, 13529885035, 9117546859, 1099921802699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099921803723, 275954155, 1099787582955, 1099787583979, 8748444167, 4386371079], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [57849375, 17187312171, 8597448235], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤138) (hj : a.j≤50) :
    Covered orders a ∨ Low6966Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [48409713719, 18042953039, 17724256591, 4872914255, 8849109459, 1099888246227], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099888247251, 1099854693851, 1099854694875, 4403147283, 108182035, 12942679583], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4352814623], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤138) (hj : a.j≤50) :
    Covered orders a ∨ Low6966Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 33 where
  orders := orders
  covers := by
    intro a ha box
    change 4+a.b≤142 ∧ 8+a.j≤58 ∧ 2+a.t≤15 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    · exact Top1.exact a ha h1 (by omega) (by omega)
    · exact Top2.exact a ha h2 (by omega) (by omega)
    · exact Top3.exact a ha h3 (by omega) (by omega)
    · exact Top4.exact a ha h4 (by omega) (by omega)
    · exact Top5.exact a ha h5 (by omega) (by omega)
    · exact Top6.exact a ha h6 (by omega) (by omega)
    · exact Top7.exact a ha h7 (by omega) (by omega)
    · exact Top8.exact a ha h8 (by omega) (by omega)
    · exact Top9.exact a ha h9 (by omega) (by omega)
    · exact Top10.exact a ha h10 (by omega) (by omega)
    · exact Top11.exact a ha h11 (by omega) (by omega)
    · exact Top12.exact a ha h12 (by omega) (by omega)
    · exact Top13.exact a ha h13 (by omega) (by omega)
end Low6966Allocation.Group33
