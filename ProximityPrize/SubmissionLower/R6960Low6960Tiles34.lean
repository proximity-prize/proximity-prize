import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass34

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group34
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23591848967, 40689738767, 87012363295, 57182887995, 43844848939, 35187947819], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34986695979, 21766324607, 21699206595, 8847865283, 8747205063, 4435463623], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099752854983, 1099601858027, 1099601859051, 4351574511, 73452015, 30121294323], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17236466163, 47284233719, 8612982267, 6275583, 6342143], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i3 : checks (tilesOf batches) 127 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 127 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 127 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 127 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 127 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 127 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 127 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36343846923, 65755429911, 86995926063, 5945413707, 30859427127, 34886032695], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22001205559, 43660295511, 35070503255, 17488125367, 13109277111, 8763982263], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4452240823, 1099685746135, 1099652189663, 1099652190687, 123716067, 1099635344867], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099635345891, 43056372199, 8646537711, 4334796271, 21514653175, 23051771], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4301238783, 4301240831], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 127 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 127 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 127 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 127 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 127 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 127 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40672961551, 74194570271, 69866460215, 43727408443, 30842648891, 30557509963], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26161953099, 1100272883019, 8831089067, 8747206059, 1099870228907, 17437792707], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8831086019, 1099702453715, 1099702454739, 1099702521299, 4351572455, 1099618566631], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [47301010931, 38694376951, 25809550839, 39827959, 39828983, 4301237759], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4301239807], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 127 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 127 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 127 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 127 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 127 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 127 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44850819091, 82650422307, 44247723071, 39549951263, 30842651935, 30624621855], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13159613815, 1100088333687, 13209937319, 8847865255, 4536123815, 1099803118011], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099803119035, 1099803185595, 47401677275, 21632026075, 13042163163, 1099635343843], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099635344867, 4368348647, 1099618565607, 34399478263, 4334792183, 23049723], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [23050747], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 127 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 127 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 127 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 127 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 127 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 127 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44867795991, 82616936487, 31413155907, 35271764251, 30792387867, 30574292251], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8780762503, 13193162135, 8831090071, 8730429847, 1099819963831, 1099803118011], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099803119035, 1099803185595, 21665582539, 8814306763, 1099702451667, 1099702452691], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099702453715, 47368191459, 4418679267, 123714019, 30104514039, 21497875963], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 127 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 127 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 127 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 127 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 127 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53155940379, 86828153903, 5811195979, 30976867599, 34936364303, 22034759951], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8780759447, 1099954113943, 17521679771, 8914973083, 8797535643, 43358374303], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30473614751, 1099819897271, 1099819963831, 1099752786375, 1099719228879, 1099719229903], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099719230927, 17270019563, 4368347627, 1099601787371, 8646535663, 4301236735], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [6271487, 6272511], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 127 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 127 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 127 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 127 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 127 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57299981343, 78255000627, 30809165079, 30557515031, 9200192791, 39197627775], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30540725631, 13209939343, 8831090063, 1099987667343, 1099870227883, 1099870228907], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099870295467, 13109272011, 1099736006091, 1099736007115, 1099736008139, 4435455455], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4368348639, 25826328051, 12941498867, 56604147, 1099568232947], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 127 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 127 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 127 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 127 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 127 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57249718307, 65454053431, 26396760367, 26178729263, 4838117679, 39231250807], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22051457399, 8898196883, 8780759443, 1099970891155, 1099836674483, 1099836741043], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099769561539, 1099769562563, 1099769563587, 13109273031, 4519342535, 1099652119007], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099652120031, 8596201983, 4301237759, 6272511], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 127 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 127 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 127 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 127 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78338812967, 31346047043, 35271765279, 26547753247, 26279324959, 8814315895], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100088333687, 8965303707, 8831089051, 1099937334683, 1099853449647, 1099853450671], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099853451695, 174045655, 1099685674455, 1099685675479, 21615317467, 8747198939], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [39826935, 34382704123, 17186132479, 8596203007], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 127 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 127 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 127 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 127 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74043848747, 22823223363, 30993643811, 26463869219, 26229060899, 1100021223815], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100021224839, 8914974099, 8780759443, 1099970891155, 1099769561539, 1099769562563], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099769563587, 17404238283, 8763977163, 123714019, 1099635342819, 4334792183], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [39826935], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 127 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 127 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 127 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69765727279, 14283622471, 26648347947, 22152126763, 21934094635, 1099954114967], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099954115991, 8831089051, 4502570395, 1099937336731, 13092495823, 4502565327], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099719230927, 1099719231951, 4385126871, 1099685675479, 73382383, 1099585011183], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25775998463], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 127 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 127 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 127 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73960099891, 26631639319, 26329656599, 13444827415, 8982080927, 8831089055], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099920557471, 1099920558495, 1099920559519, 1099920560543, 1099920627103, 4385126875], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099668898267, 21581763047, 8696867303, 56605171, 1099568233971, 6272511], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 127 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 127 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 127 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 34 where
  orders := orders
  covers := by
    intro a ha box
    change 14+a.b≤141 ∧ 6+a.j≤59 ∧ 2+a.t≤14 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
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
end Low6960Allocation.Group34
