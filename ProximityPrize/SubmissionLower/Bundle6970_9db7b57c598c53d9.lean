import ProximityPrize.SubmissionLower.R6970Height2313CompactRoute
import ProximityPrize.SubmissionLower.Bundle6970_748bd2481862afb9
import ProximityPrize.SubmissionLower.R6970Height2313ExplicitCore
import ProximityPrize.SubmissionLower.Bundle6970_7a5e29fe006b0d6e
import ProximityPrize.SubmissionLower.R6970Height2313SmallGrade
import ProximityPrize.SubmissionLower.Bundle6970_f7a7d3fc354358e1
import ProximityPrize.SubmissionLower.Bundle6970_4c2beb30f00b6b5f
import ProximityPrize.SubmissionLower.Bundle6970_2669b3692c4162b7
import ProximityPrize.SubmissionLower.Bundle6970_282d89f7c7f62e8c

section Pack_R6970Height2313Dispatch0939

set_option Elab.async false

section Z6969Source2633
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HardFit1At140
open _root_.Research6970.Height2313.Research6969
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem pack_R6970Height2313Dispatch0939_leaf0:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,25,some 28⟩,0,none,257319,some 302619⟩:=(PairReceipts.route700 6)
private theorem pack_R6970Height2313Dispatch0939_leaf1:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,25,some 28⟩,0,none,302619,none⟩:=(PairReceipts.route708 0)
private theorem pack_R6970Height2313Dispatch0939_weight2:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,25,some 28⟩,0,none,257319,none⟩:=PairRoute.weight 302619 pack_R6970Height2313Dispatch0939_leaf0 pack_R6970Height2313Dispatch0939_leaf1
theorem case140: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,25,some 28⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0939_weight2
private theorem pack_R6970Height2313Dispatch0939_leaf3:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,29,some 32⟩,0,none,257319,none⟩:=(PairReceipts.route700 5)
theorem case141: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,29,some 32⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0939_leaf3
private theorem pack_R6970Height2313Dispatch0939_leaf4:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,33,some 40⟩,0,none,257319,none⟩:=(PairReceipts.route700 4)
theorem case142: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,33,some 40⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0939_leaf4
private theorem pack_R6970Height2313Dispatch0939_leaf5:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,41,some 48⟩,0,none,257319,none⟩:=(PairReceipts.route700 3)
theorem case143: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,41,some 48⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0939_leaf5
private theorem pack_R6970Height2313Dispatch0939_leaf6:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,49,some 56⟩,0,none,257319,some 285209⟩:=(PairReceipts.route700 2)
private theorem pack_R6970Height2313Dispatch0939_leaf7:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,49,some 56⟩,0,none,285209,none⟩:=PaidRows.p703
private theorem weight8:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,49,some 56⟩,0,none,257319,none⟩:=PairRoute.weight 285209 pack_R6970Height2313Dispatch0939_leaf6 pack_R6970Height2313Dispatch0939_leaf7
theorem case144: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,49,some 56⟩:=PairRoute.start _ weight8
private theorem allAxes138:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,57,some 64⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 64 ⟨
    (PairReceipts.route636 1),
    (PairReceipts.route636 2),
    (PairReceipts.route636 3),
    (PairReceipts.route700 12),
    (PairReceipts.route700 13),
    (PairReceipts.route700 14),
    (PairReceipts.route700 15),
    (PairReceipts.route700 16),
    (PairReceipts.route700 17),
    (PairReceipts.route700 18),
    (PairReceipts.route700 19),
    (PairReceipts.route700 20),
    (PairReceipts.route700 21),
    (PairReceipts.route700 22),
    (PairReceipts.route700 23),
    (PairReceipts.route652 0),
    (PairReceipts.route652 1),
    (PairReceipts.route652 2),
    (PairReceipts.route652 3),
    (PairReceipts.route652 4),
    (PairReceipts.route652 5),
    (PairReceipts.route652 6),
    (PairReceipts.route652 7),
    (PairReceipts.route660 0),
    (PairReceipts.route660 1),
    (PairReceipts.route660 2),
    (PairReceipts.route660 3),
    (PairReceipts.route660 4),
    (PairReceipts.route660 5),
    (PairReceipts.route660 6),
    PaidRows.p667,
    PaidRows.p668,
    (PairReceipts.route660 7),
    (PairReceipts.route660 8),
    (PairReceipts.route660 9),
    (PairReceipts.route660 10),
    (PairReceipts.route660 11),
    (PairReceipts.route660 12),
    (PairReceipts.route660 13),
    (PairReceipts.route660 14),
    (PairReceipts.route660 15),
    (PairReceipts.route660 16),
    (PairReceipts.route660 17),
    (PairReceipts.route660 18),
    (PairReceipts.route660 19),
    (PairReceipts.route660 20),
    (PairReceipts.route660 21),
    (PairReceipts.route660 22),
    PaidRows.p685,
    PaidRows.p686,
    PaidRows.p687,
    PaidRows.p688,
    PaidRows.p689,
    PaidRows.p690,
    PaidRows.p691,
    PaidRows.p692,
    (PairReceipts.route660 23),
    (PairReceipts.route694 0),
    (PairReceipts.route694 1),
    (PairReceipts.route694 2),
    (PairReceipts.route694 3),
    (PairReceipts.route694 4),
    (PairReceipts.route694 5),
    (PairReceipts.route700 0),
    (PairReceipts.route700 1),
    trivial⟩)
theorem case145: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,57,some 64⟩:=PairRoute.start _ allAxes138
private theorem leaf139:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,65,some 96⟩,0,none,257319,none⟩:=(PairReceipts.route636 0)
theorem case146: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,65,some 96⟩:=PairRoute.start _ leaf139
private theorem leaf140:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,3,4,some 8⟩,0,none,385979,none⟩:=(PairReceipts.route881 13)
theorem case147: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (0:Fin 18) ⟨41,49,9,3,4,some 8⟩:=PairRoute.start _ leaf140
private theorem leaf141:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,3,9,some 12⟩,0,none,385979,none⟩:=(PairReceipts.route881 12)
theorem case148: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (0:Fin 18) ⟨41,49,9,3,9,some 12⟩:=PairRoute.start _ leaf141
private theorem leaf142:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,3,13,some 14⟩,0,none,385979,none⟩:=(PairReceipts.route881 11)
theorem case149: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (0:Fin 18) ⟨41,49,9,3,13,some 14⟩:=PairRoute.start _ leaf142
end Research6970.Height2313.Research6969.HardFit1At140
end Z6969Source2633
end Pack_R6970Height2313Dispatch0939

section Pack_R6970Height2313Dispatch0945

set_option Elab.async false

section Z6969Source2705
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HardFit2At100
open _root_.Research6970.Height2313.Research6969
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem pack_R6970Height2313Dispatch0945_leaf0:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,2,21,some 24⟩,0,none,257319,none⟩:=(PairReceipts.route1723 22)
theorem case100: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0945_leaf0
private theorem pack_R6970Height2313Dispatch0945_leaf1:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,2,25,some 28⟩,0,none,257319,some 302619⟩:=(PairReceipts.route1723 21)
private theorem leaf2:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,2,25,some 28⟩,0,none,302619,none⟩:=PaidRows.p1850
private theorem weight3:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,2,25,some 28⟩,0,none,257319,none⟩:=PairRoute.weight 302619 pack_R6970Height2313Dispatch0945_leaf1 leaf2
theorem case101: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,25,some 28⟩:=PairRoute.start _ weight3
private theorem pack_R6970Height2313Dispatch0945_leaf4:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,2,29,some 32⟩,0,none,257319,none⟩:=(PairReceipts.route1723 20)
theorem case102: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,29,some 32⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0945_leaf4
private theorem pack_R6970Height2313Dispatch0945_leaf5:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,2,33,some 40⟩,0,none,257319,none⟩:=(PairReceipts.route1723 19)
theorem case103: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,33,some 40⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0945_leaf5
private theorem pack_R6970Height2313Dispatch0945_leaf6:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,2,41,some 48⟩,0,none,257319,none⟩:=(PairReceipts.route1723 18)
theorem case104: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,41,some 48⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0945_leaf6
private theorem allAxes120:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,2,49,some 56⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 56 ⟨
    (PairReceipts.route1780 9),
    (PairReceipts.route1780 10),
    (PairReceipts.route1780 11),
    (PairReceipts.route1780 12),
    (PairReceipts.route1780 13),
    (PairReceipts.route1780 14),
    (PairReceipts.route1780 15),
    (PairReceipts.route1780 16),
    (PairReceipts.route1780 17),
    (PairReceipts.route1780 18),
    (PairReceipts.route1780 19),
    (PairReceipts.route1780 20),
    (PairReceipts.route1780 21),
    (PairReceipts.route1780 22),
    (PairReceipts.route1780 23),
    (PairReceipts.route1804 0),
    (PairReceipts.route1804 1),
    (PairReceipts.route1804 2),
    (PairReceipts.route1804 3),
    (PairReceipts.route1804 4),
    (PairReceipts.route1804 5),
    (PairReceipts.route1804 6),
    (PairReceipts.route1804 7),
    (PairReceipts.route1804 8),
    (PairReceipts.route1804 9),
    (PairReceipts.route1804 10),
    (PairReceipts.route1804 11),
    (PairReceipts.route1804 12),
    (PairReceipts.route1804 13),
    (PairReceipts.route1804 14),
    PaidRows.p1819,
    PaidRows.p1820,
    (PairReceipts.route1804 15),
    (PairReceipts.route1804 16),
    (PairReceipts.route1804 17),
    (PairReceipts.route1804 18),
    (PairReceipts.route1804 19),
    (PairReceipts.route1804 20),
    (PairReceipts.route1804 21),
    (PairReceipts.route1804 22),
    (PairReceipts.route1804 23),
    (PairReceipts.route1830 0),
    (PairReceipts.route1830 1),
    (PairReceipts.route1830 2),
    (PairReceipts.route1830 3),
    (PairReceipts.route1830 4),
    (PairReceipts.route1830 5),
    (PairReceipts.route1830 6),
    PaidRows.p1837,
    PaidRows.p1838,
    PaidRows.p1839,
    PaidRows.p1840,
    PaidRows.p1841,
    PaidRows.p1842,
    PaidRows.p1843,
    PaidRows.p1844,
    (PairReceipts.route1723 17),
    trivial⟩)
theorem case105: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,49,some 56⟩:=PairRoute.start _ allAxes120
private theorem allAxes250:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,2,57,some 64⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 64 ⟨
    (PairReceipts.route1723 1),
    (PairReceipts.route1723 2),
    (PairReceipts.route1723 3),
    (PairReceipts.route1723 4),
    (PairReceipts.route1723 5),
    (PairReceipts.route1723 6),
    (PairReceipts.route1723 7),
    (PairReceipts.route1723 8),
    (PairReceipts.route1723 9),
    (PairReceipts.route1723 10),
    (PairReceipts.route1723 11),
    (PairReceipts.route1723 12),
    (PairReceipts.route1723 13),
    (PairReceipts.route1723 14),
    (PairReceipts.route1723 15),
    (PairReceipts.route1723 16),
    (PairReceipts.route1853 3),
    (PairReceipts.route1853 4),
    (PairReceipts.route1853 5),
    (PairReceipts.route1853 6),
    (PairReceipts.route1853 7),
    (PairReceipts.route1853 8),
    (PairReceipts.route1853 9),
    (PairReceipts.route1853 10),
    (PairReceipts.route1853 11),
    (PairReceipts.route1853 12),
    (PairReceipts.route1853 13),
    (PairReceipts.route1853 14),
    (PairReceipts.route1853 15),
    (PairReceipts.route1853 16),
    PaidRows.p1754,
    PaidRows.p1755,
    (PairReceipts.route1853 17),
    (PairReceipts.route1853 18),
    (PairReceipts.route1853 19),
    (PairReceipts.route1853 20),
    (PairReceipts.route1853 21),
    (PairReceipts.route1853 22),
    (PairReceipts.route1853 23),
    (PairReceipts.route1763 0),
    (PairReceipts.route1763 1),
    (PairReceipts.route1763 2),
    (PairReceipts.route1763 3),
    (PairReceipts.route1763 4),
    (PairReceipts.route1763 5),
    (PairReceipts.route1763 6),
    (PairReceipts.route1763 7),
    (PairReceipts.route1763 8),
    PaidRows.p1772,
    PaidRows.p1773,
    PaidRows.p1774,
    PaidRows.p1775,
    PaidRows.p1776,
    PaidRows.p1777,
    PaidRows.p1778,
    PaidRows.p1779,
    (PairReceipts.route1780 0),
    (PairReceipts.route1780 1),
    (PairReceipts.route1780 2),
    (PairReceipts.route1780 3),
    (PairReceipts.route1780 4),
    (PairReceipts.route1780 5),
    (PairReceipts.route1780 6),
    (PairReceipts.route1780 7),
    (PairReceipts.route1780 8),
    trivial⟩)
theorem case106: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,57,some 64⟩:=PairRoute.start _ allAxes250
private theorem leaf251:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,2,65,some 96⟩,0,none,257319,none⟩:=(PairReceipts.route1723 0)
theorem case107: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,65,some 96⟩:=PairRoute.start _ leaf251
private theorem leaf252:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,4,some 8⟩,0,none,385979,none⟩:=(PairReceipts.route2020 5)
theorem case108: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,4,some 8⟩:=PairRoute.start _ leaf252
private theorem leaf253:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,9,some 12⟩,0,none,385979,none⟩:=(PairReceipts.route2020 4)
theorem case109: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,9,some 12⟩:=PairRoute.start _ leaf253
end Research6970.Height2313.Research6969.HardFit2At100
end Z6969Source2705
end Pack_R6970Height2313Dispatch0945

section Pack_R6970Height2313Dispatch0947

set_option Elab.async false

section Z6969Source2724
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HardFit2At140
open _root_.Research6970.Height2313.Research6969
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem pack_R6970Height2313Dispatch0947_leaf0:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,25,some 28⟩,0,none,257319,some 302619⟩:=(PairReceipts.route2145 6)
private theorem pack_R6970Height2313Dispatch0947_leaf1:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,25,some 28⟩,0,none,302619,none⟩:=PaidRows.p2155
private theorem pack_R6970Height2313Dispatch0947_weight2:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,25,some 28⟩,0,none,257319,none⟩:=PairRoute.weight 302619 pack_R6970Height2313Dispatch0947_leaf0 pack_R6970Height2313Dispatch0947_leaf1
theorem case140: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,25,some 28⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0947_weight2
private theorem pack_R6970Height2313Dispatch0947_leaf3:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,29,some 32⟩,0,none,257319,none⟩:=(PairReceipts.route2145 5)
theorem case141: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,29,some 32⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0947_leaf3
private theorem pack_R6970Height2313Dispatch0947_leaf4:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,33,some 40⟩,0,none,257319,none⟩:=(PairReceipts.route2145 4)
theorem case142: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,33,some 40⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0947_leaf4
private theorem pack_R6970Height2313Dispatch0947_leaf5:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,41,some 48⟩,0,none,257319,some 291368⟩:=(PairReceipts.route2145 3)
private theorem pack_R6970Height2313Dispatch0947_leaf6:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,41,some 48⟩,0,none,291368,none⟩:=(PairReceipts.route2151 0)
private theorem weight7:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,41,some 48⟩,0,none,257319,none⟩:=PairRoute.weight 291368 pack_R6970Height2313Dispatch0947_leaf5 pack_R6970Height2313Dispatch0947_leaf6
theorem case143: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,41,some 48⟩:=PairRoute.start _ weight7
private theorem pack_R6970Height2313Dispatch0947_leaf8:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,49,some 52⟩,0,none,257319,some 288407⟩:=(PairReceipts.route2145 2)
private theorem leaf9:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,49,some 52⟩,0,none,288407,none⟩:=(PairReceipts.route2149 0)
private theorem weight10:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,49,some 52⟩,0,none,257319,none⟩:=PairRoute.weight 288407 pack_R6970Height2313Dispatch0947_leaf8 leaf9
theorem case144: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,49,some 52⟩:=PairRoute.start _ weight10
private theorem pack_R6970Height2313Dispatch0947_leaf11:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,53,some 54⟩,0,none,257319,none⟩:=(PairReceipts.route2145 1)
theorem case145: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,53,some 54⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0947_leaf11
private theorem pack_R6970Height2313Dispatch0947_leaf12:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,55,some 55⟩,0,none,257319,none⟩:=PaidRows.p2146
theorem case146: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,55,some 55⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0947_leaf12
private theorem pack_R6970Height2313Dispatch0947_allAxes126:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,56,some 56⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 56 ⟨
    (PairReceipts.route2059 20),
    (PairReceipts.route2059 21),
    (PairReceipts.route2059 22),
    (PairReceipts.route2059 23),
    (PairReceipts.route2093 0),
    (PairReceipts.route2093 1),
    (PairReceipts.route2093 2),
    (PairReceipts.route2093 3),
    (PairReceipts.route2093 4),
    (PairReceipts.route2093 5),
    (PairReceipts.route2093 6),
    (PairReceipts.route2093 7),
    (PairReceipts.route2093 8),
    (PairReceipts.route2093 9),
    (PairReceipts.route2093 10),
    (PairReceipts.route2093 11),
    (PairReceipts.route2093 12),
    (PairReceipts.route2093 13),
    (PairReceipts.route2093 14),
    (PairReceipts.route2093 15),
    (PairReceipts.route2093 16),
    (PairReceipts.route2093 17),
    (PairReceipts.route2093 18),
    (PairReceipts.route2093 19),
    (PairReceipts.route2093 20),
    (PairReceipts.route2093 21),
    (PairReceipts.route2093 22),
    (PairReceipts.route2093 23),
    (PairReceipts.route2117 0),
    (PairReceipts.route2117 1),
    PaidRows.p2119,
    PaidRows.p2120,
    (PairReceipts.route2117 2),
    (PairReceipts.route2117 3),
    (PairReceipts.route2117 4),
    (PairReceipts.route2117 5),
    (PairReceipts.route2117 6),
    (PairReceipts.route2117 7),
    (PairReceipts.route2117 8),
    (PairReceipts.route2117 9),
    (PairReceipts.route2117 10),
    (PairReceipts.route2117 11),
    (PairReceipts.route2117 12),
    (PairReceipts.route2117 13),
    (PairReceipts.route2117 14),
    (PairReceipts.route2117 15),
    (PairReceipts.route2117 16),
    (PairReceipts.route2117 17),
    PaidRows.p2137,
    PaidRows.p2138,
    PaidRows.p2139,
    PaidRows.p2140,
    PaidRows.p2141,
    PaidRows.p2142,
    PaidRows.p2143,
    PaidRows.p2144,
    (PairReceipts.route2145 0),
    trivial⟩)
theorem case147: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,56,some 56⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0947_allAxes126
private theorem allAxes242:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,57,some 57⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 57 ⟨
    (PairReceipts.route2027 3),
    (PairReceipts.route2027 4),
    (PairReceipts.route2027 5),
    (PairReceipts.route2027 6),
    (PairReceipts.route2027 7),
    (PairReceipts.route2027 8),
    (PairReceipts.route2027 9),
    (PairReceipts.route2027 10),
    (PairReceipts.route2027 11),
    (PairReceipts.route2145 12),
    (PairReceipts.route2145 13),
    (PairReceipts.route2145 14),
    (PairReceipts.route2145 15),
    (PairReceipts.route2145 16),
    (PairReceipts.route2145 17),
    (PairReceipts.route2145 18),
    (PairReceipts.route2145 19),
    (PairReceipts.route2145 20),
    (PairReceipts.route2145 21),
    (PairReceipts.route2145 22),
    (PairReceipts.route2145 23),
    (PairReceipts.route2052 0),
    (PairReceipts.route2052 1),
    (PairReceipts.route2052 2),
    (PairReceipts.route2052 3),
    (PairReceipts.route2052 4),
    (PairReceipts.route2052 5),
    (PairReceipts.route2052 6),
    (PairReceipts.route2059 0),
    (PairReceipts.route2059 1),
    PaidRows.p2061,
    PaidRows.p2062,
    (PairReceipts.route2059 2),
    (PairReceipts.route2059 3),
    (PairReceipts.route2059 4),
    (PairReceipts.route2059 5),
    (PairReceipts.route2059 6),
    (PairReceipts.route2059 7),
    (PairReceipts.route2059 8),
    (PairReceipts.route2059 9),
    (PairReceipts.route2059 10),
    (PairReceipts.route2059 11),
    (PairReceipts.route2059 12),
    (PairReceipts.route2059 13),
    (PairReceipts.route2059 14),
    (PairReceipts.route2059 15),
    (PairReceipts.route2059 16),
    (PairReceipts.route2059 17),
    PaidRows.p2079,
    PaidRows.p2080,
    PaidRows.p2081,
    PaidRows.p2082,
    PaidRows.p2083,
    PaidRows.p2084,
    PaidRows.p2085,
    PaidRows.p2086,
    (PairReceipts.route2059 18),
    (PairReceipts.route2059 19),
    trivial⟩)
theorem case148: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,57,some 57⟩:=PairRoute.start _ allAxes242
private theorem leaf243:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,58,some 58⟩,0,none,257319,some 283522⟩:=(PairReceipts.route2027 2)
private theorem leaf244:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,58,some 58⟩,0,none,283522,none⟩:=(PairReceipts.route2030 0)
private theorem weight245:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,2,58,some 58⟩,0,none,257319,none⟩:=PairRoute.weight 283522 leaf243 leaf244
theorem case149: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,58,some 58⟩:=PairRoute.start _ weight245
end Research6970.Height2313.Research6969.HardFit2At140
end Z6969Source2724
end Pack_R6970Height2313Dispatch0947

section Pack_R6970Height2313Dispatch0953

set_option Elab.async false

section Z6969Source2796
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HardFit3At120
open _root_.Research6970.Height2313.Research6969
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem pack_R6970Height2313Dispatch0953_leaf0:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,25,some 28⟩,0,none,257319,some 304553⟩:=(PairReceipts.route3121 5)
private theorem pack_R6970Height2313Dispatch0953_leaf1:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,25,some 28⟩,0,none,304553,none⟩:=PaidRows.p3133
private theorem pack_R6970Height2313Dispatch0953_weight2:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,25,some 28⟩,0,none,257319,none⟩:=PairRoute.weight 304553 pack_R6970Height2313Dispatch0953_leaf0 pack_R6970Height2313Dispatch0953_leaf1
theorem case120: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,25,some 28⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0953_weight2
private theorem pack_R6970Height2313Dispatch0953_leaf3:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,29,some 32⟩,0,none,257319,none⟩:=(PairReceipts.route3121 4)
theorem case121: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,29,some 32⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0953_leaf3
private theorem pack_R6970Height2313Dispatch0953_leaf4:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,33,some 40⟩,0,none,257319,none⟩:=PaidRows.p3130
theorem case122: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,33,some 40⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0953_leaf4
private theorem pack_R6970Height2313Dispatch0953_leaf5:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,41,some 44⟩,0,none,257319,none⟩:=(PairReceipts.route3121 3)
theorem case123: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,41,some 44⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0953_leaf5
private theorem pack_R6970Height2313Dispatch0953_leaf6:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,45,some 48⟩,0,none,257319,none⟩:=PaidRows.p3128
theorem case124: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,45,some 48⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0953_leaf6
private theorem pack_R6970Height2313Dispatch0953_leaf7:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,49,some 50⟩,0,none,257319,some 289917⟩:=(PairReceipts.route3121 2)
private theorem pack_R6970Height2313Dispatch0953_leaf8:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,49,some 50⟩,0,none,289917,none⟩:=(PairReceipts.route3127 0)
private theorem weight9:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,49,some 50⟩,0,none,257319,none⟩:=PairRoute.weight 289917 pack_R6970Height2313Dispatch0953_leaf7 pack_R6970Height2313Dispatch0953_leaf8
theorem case125: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,49,some 50⟩:=PairRoute.start _ weight9
private theorem leaf10:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,51,some 51⟩,0,none,257319,none⟩:=PaidRows.p3125
theorem case126: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,51,some 51⟩:=PairRoute.start _ leaf10
private theorem pack_R6970Height2313Dispatch0953_leaf11:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,52,some 52⟩,0,none,257319,some 288407⟩:=(PairReceipts.route3121 1)
private theorem pack_R6970Height2313Dispatch0953_leaf12:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,52,some 52⟩,0,none,288407,none⟩:=(PairReceipts.route3124 0)
private theorem weight13:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,52,some 52⟩,0,none,257319,none⟩:=PairRoute.weight 288407 pack_R6970Height2313Dispatch0953_leaf11 pack_R6970Height2313Dispatch0953_leaf12
theorem case127: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,52,some 52⟩:=PairRoute.start _ weight13
private theorem leaf14:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,53,some 53⟩,0,none,257319,some 287630⟩:=(PairReceipts.route3121 0)
private theorem leaf15:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,53,some 53⟩,0,none,287630,none⟩:=PaidRows.p3122
private theorem weight16:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,53,some 53⟩,0,none,257319,none⟩:=PairRoute.weight 287630 leaf14 leaf15
theorem case128: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,53,some 53⟩:=PairRoute.start _ weight16
private theorem pack_R6970Height2313Dispatch0953_allAxes126:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,54,some 54⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 54 ⟨
    (PairReceipts.route3121 12),
    (PairReceipts.route3121 13),
    (PairReceipts.route3121 14),
    (PairReceipts.route3121 15),
    (PairReceipts.route3121 16),
    (PairReceipts.route3121 17),
    (PairReceipts.route3121 18),
    (PairReceipts.route3121 19),
    (PairReceipts.route3121 20),
    (PairReceipts.route3121 21),
    (PairReceipts.route3121 22),
    (PairReceipts.route3121 23),
    (PairReceipts.route3078 0),
    (PairReceipts.route3078 1),
    (PairReceipts.route3078 2),
    (PairReceipts.route3078 3),
    (PairReceipts.route3078 4),
    (PairReceipts.route3078 5),
    (PairReceipts.route3078 6),
    (PairReceipts.route3078 7),
    (PairReceipts.route3078 8),
    (PairReceipts.route3078 9),
    (PairReceipts.route3078 10),
    (PairReceipts.route3078 11),
    (PairReceipts.route3078 12),
    (PairReceipts.route3078 13),
    (PairReceipts.route3078 14),
    (PairReceipts.route3078 15),
    (PairReceipts.route3078 16),
    (PairReceipts.route3078 17),
    PaidRows.p3096,
    PaidRows.p3097,
    (PairReceipts.route3078 18),
    (PairReceipts.route3078 19),
    (PairReceipts.route3078 20),
    (PairReceipts.route3078 21),
    (PairReceipts.route3078 22),
    (PairReceipts.route3078 23),
    (PairReceipts.route3104 0),
    (PairReceipts.route3104 1),
    (PairReceipts.route3104 2),
    (PairReceipts.route3104 3),
    (PairReceipts.route3104 4),
    (PairReceipts.route3104 5),
    (PairReceipts.route3104 6),
    (PairReceipts.route3104 7),
    (PairReceipts.route3104 8),
    (PairReceipts.route3104 9),
    PaidRows.p3114,
    PaidRows.p3115,
    PaidRows.p3116,
    PaidRows.p3117,
    PaidRows.p3118,
    PaidRows.p3119,
    PaidRows.p3120,
    trivial⟩)
theorem case129: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,54,some 54⟩:=PairRoute.start _ pack_R6970Height2313Dispatch0953_allAxes126
end Research6970.Height2313.Research6969.HardFit3At120
end Z6969Source2796
end Pack_R6970Height2313Dispatch0953

section Pack_R6970Height2313Dispatch0954

set_option Elab.async false

section Z6969Source2817
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HardFit3At130
open _root_.Research6970.Height2313.Research6969
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes111:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,55,some 55⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 55 ⟨
    (PairReceipts.route2982 18),
    (PairReceipts.route2982 19),
    (PairReceipts.route2982 20),
    (PairReceipts.route2982 21),
    (PairReceipts.route2982 22),
    (PairReceipts.route2982 23),
    (PairReceipts.route3016 0),
    (PairReceipts.route3016 1),
    (PairReceipts.route3016 2),
    (PairReceipts.route3016 3),
    (PairReceipts.route3016 4),
    (PairReceipts.route3016 5),
    (PairReceipts.route3016 6),
    (PairReceipts.route3016 7),
    (PairReceipts.route3016 8),
    (PairReceipts.route3016 9),
    (PairReceipts.route3016 10),
    (PairReceipts.route3016 11),
    (PairReceipts.route3016 12),
    (PairReceipts.route3016 13),
    (PairReceipts.route3016 14),
    (PairReceipts.route3016 15),
    (PairReceipts.route3016 16),
    (PairReceipts.route3016 17),
    (PairReceipts.route3016 18),
    (PairReceipts.route3016 19),
    (PairReceipts.route3016 20),
    (PairReceipts.route3016 21),
    (PairReceipts.route3016 22),
    (PairReceipts.route3016 23),
    PaidRows.p3040,
    PaidRows.p3041,
    (PairReceipts.route3042 0),
    (PairReceipts.route3042 1),
    (PairReceipts.route3042 2),
    (PairReceipts.route3042 3),
    (PairReceipts.route3042 4),
    (PairReceipts.route3042 5),
    (PairReceipts.route3042 6),
    (PairReceipts.route3042 7),
    (PairReceipts.route3042 8),
    (PairReceipts.route3042 9),
    (PairReceipts.route3042 10),
    (PairReceipts.route3042 11),
    (PairReceipts.route3042 12),
    (PairReceipts.route3042 13),
    (PairReceipts.route3042 14),
    (PairReceipts.route3042 15),
    PaidRows.p3058,
    PaidRows.p3059,
    PaidRows.p3060,
    PaidRows.p3061,
    PaidRows.p3062,
    PaidRows.p3063,
    PaidRows.p3064,
    PaidRows.p3065,
    trivial⟩)
theorem case130: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,55,some 55⟩:=PairRoute.start _ allAxes111
private theorem allAxes225:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,56,some 56⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 56 ⟨
    (PairReceipts.route2940 5),
    (PairReceipts.route2940 6),
    (PairReceipts.route2940 7),
    (PairReceipts.route2940 8),
    (PairReceipts.route2940 9),
    (PairReceipts.route2958 0),
    (PairReceipts.route2958 1),
    (PairReceipts.route2958 2),
    (PairReceipts.route2958 3),
    (PairReceipts.route2958 4),
    (PairReceipts.route2958 5),
    (PairReceipts.route2958 6),
    (PairReceipts.route2958 7),
    (PairReceipts.route2958 8),
    (PairReceipts.route2958 9),
    (PairReceipts.route2958 10),
    (PairReceipts.route2958 11),
    (PairReceipts.route2958 12),
    (PairReceipts.route2958 13),
    (PairReceipts.route2958 14),
    (PairReceipts.route2958 15),
    (PairReceipts.route2958 16),
    (PairReceipts.route2958 17),
    (PairReceipts.route2958 18),
    (PairReceipts.route2958 19),
    (PairReceipts.route2958 20),
    (PairReceipts.route2958 21),
    (PairReceipts.route2958 22),
    (PairReceipts.route2958 23),
    (PairReceipts.route2982 0),
    PaidRows.p2983,
    PaidRows.p2984,
    (PairReceipts.route2982 1),
    (PairReceipts.route2982 2),
    (PairReceipts.route2982 3),
    (PairReceipts.route2982 4),
    (PairReceipts.route2982 5),
    (PairReceipts.route2982 6),
    (PairReceipts.route2982 7),
    (PairReceipts.route2982 8),
    (PairReceipts.route2982 9),
    (PairReceipts.route2982 10),
    (PairReceipts.route2982 11),
    (PairReceipts.route2982 12),
    (PairReceipts.route2982 13),
    (PairReceipts.route2982 14),
    (PairReceipts.route2982 15),
    (PairReceipts.route2982 16),
    PaidRows.p3001,
    PaidRows.p3002,
    PaidRows.p3003,
    PaidRows.p3004,
    PaidRows.p3005,
    PaidRows.p3006,
    PaidRows.p3007,
    PaidRows.p3008,
    (PairReceipts.route2982 17),
    trivial⟩)
theorem case131: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,56,some 56⟩:=PairRoute.start _ allAxes225
private theorem allAxes341:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,57,some 57⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 57 ⟨
    (PairReceipts.route2891 3),
    (PairReceipts.route2891 4),
    (PairReceipts.route2891 5),
    (PairReceipts.route2891 6),
    (PairReceipts.route2891 7),
    (PairReceipts.route3104 10),
    (PairReceipts.route3104 11),
    (PairReceipts.route3104 12),
    (PairReceipts.route3104 13),
    (PairReceipts.route3104 14),
    (PairReceipts.route3104 15),
    (PairReceipts.route3104 16),
    (PairReceipts.route3104 17),
    (PairReceipts.route3104 18),
    (PairReceipts.route3104 19),
    (PairReceipts.route3104 20),
    (PairReceipts.route3104 21),
    (PairReceipts.route3104 22),
    (PairReceipts.route3104 23),
    (PairReceipts.route2914 0),
    (PairReceipts.route2914 1),
    (PairReceipts.route2914 2),
    (PairReceipts.route2914 3),
    (PairReceipts.route2914 4),
    (PairReceipts.route2914 5),
    (PairReceipts.route2914 6),
    (PairReceipts.route2914 7),
    (PairReceipts.route2914 8),
    (PairReceipts.route2914 9),
    (PairReceipts.route2914 10),
    PaidRows.p2925,
    PaidRows.p2926,
    (PairReceipts.route2914 11),
    (PairReceipts.route2914 12),
    (PairReceipts.route2914 13),
    (PairReceipts.route2914 14),
    (PairReceipts.route2914 15),
    (PairReceipts.route2914 16),
    (PairReceipts.route2914 17),
    (PairReceipts.route2914 18),
    (PairReceipts.route2914 19),
    (PairReceipts.route2914 20),
    (PairReceipts.route2914 21),
    (PairReceipts.route2914 22),
    (PairReceipts.route2914 23),
    (PairReceipts.route2940 0),
    (PairReceipts.route2940 1),
    (PairReceipts.route2940 2),
    PaidRows.p2943,
    PaidRows.p2944,
    PaidRows.p2945,
    PaidRows.p2946,
    PaidRows.p2947,
    PaidRows.p2948,
    PaidRows.p2949,
    PaidRows.p2950,
    (PairReceipts.route2940 3),
    (PairReceipts.route2940 4),
    trivial⟩)
theorem case132: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,57,some 57⟩:=PairRoute.start _ allAxes341
private theorem leaf342:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,58,some 58⟩,0,none,257319,some 283522⟩:=(PairReceipts.route2891 2)
private theorem leaf343:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,58,some 58⟩,0,none,283522,none⟩:=(PairReceipts.route2894 0)
private theorem weight344:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,58,some 58⟩,0,none,257319,none⟩:=PairRoute.weight 283522 leaf342 leaf343
theorem case133: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,58,some 58⟩:=PairRoute.start _ weight344
private theorem leaf345:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,59,some 60⟩,0,none,257319,none⟩:=(PairReceipts.route2891 1)
theorem case134: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,59,some 60⟩:=PairRoute.start _ leaf345
private theorem leaf346:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,61,some 64⟩,0,none,257319,none⟩:=(PairReceipts.route2891 0)
theorem case135: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,61,some 64⟩:=PairRoute.start _ leaf346
private theorem leaf347:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,4,some 8⟩,0,none,385979,none⟩:=(PairReceipts.route3381 6)
theorem case136: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,4,some 8⟩:=PairRoute.start _ leaf347
private theorem leaf348:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,9,some 12⟩,0,none,385979,none⟩:=(PairReceipts.route3381 5)
theorem case137: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,9,some 12⟩:=PairRoute.start _ leaf348
private theorem leaf349:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,13,some 13⟩,0,none,385979,none⟩:=(PairReceipts.route3381 4)
theorem case138: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,13,some 13⟩:=PairRoute.start _ leaf349
private theorem allAxes379:PairRoute.Done (2:Fin 18) ⟨⟨50,50,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6650 0),
    (PairReceipts.route6650 1),
    (PairReceipts.route6650 2),
    PaidRows.p6653,
    PaidRows.p6654,
    (PairReceipts.route6650 3),
    PaidRows.p6656,
    PaidRows.p6657,
    (PairReceipts.route6650 4),
    (PairReceipts.route6650 5),
    PaidRows.p6660,
    PaidRows.p6661,
    (PairReceipts.route6650 6),
    (PairReceipts.route6650 7),
    (PairReceipts.route6650 8),
    trivial⟩)
private theorem allAxes409:PairRoute.Done (2:Fin 18) ⟨⟨51,51,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6665 0),
    (PairReceipts.route6665 1),
    (PairReceipts.route6665 2),
    PaidRows.p6668,
    PaidRows.p6669,
    (PairReceipts.route6665 3),
    PaidRows.p6671,
    PaidRows.p6672,
    (PairReceipts.route6665 4),
    (PairReceipts.route6665 5),
    PaidRows.p6675,
    PaidRows.p6676,
    (PairReceipts.route6665 6),
    (PairReceipts.route6665 7),
    (PairReceipts.route6665 8),
    trivial⟩)
private theorem allAxes439:PairRoute.Done (2:Fin 18) ⟨⟨52,52,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6680 0),
    (PairReceipts.route6680 1),
    (PairReceipts.route6680 2),
    PaidRows.p6683,
    PaidRows.p6684,
    (PairReceipts.route6680 3),
    PaidRows.p6686,
    PaidRows.p6687,
    (PairReceipts.route6680 4),
    (PairReceipts.route6680 5),
    PaidRows.p6690,
    PaidRows.p6691,
    (PairReceipts.route6680 6),
    (PairReceipts.route6680 7),
    (PairReceipts.route6680 8),
    trivial⟩)
private theorem allAxes469:PairRoute.Done (2:Fin 18) ⟨⟨53,53,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6695 0),
    (PairReceipts.route6695 1),
    (PairReceipts.route6695 2),
    PaidRows.p6698,
    PaidRows.p6699,
    (PairReceipts.route6695 3),
    PaidRows.p6701,
    PaidRows.p6702,
    (PairReceipts.route6695 4),
    (PairReceipts.route6695 5),
    PaidRows.p6705,
    PaidRows.p6706,
    (PairReceipts.route6695 6),
    (PairReceipts.route6695 7),
    (PairReceipts.route6695 8),
    trivial⟩)
private theorem allAxes499:PairRoute.Done (2:Fin 18) ⟨⟨54,54,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6710 0),
    (PairReceipts.route6710 1),
    (PairReceipts.route6710 2),
    PaidRows.p6713,
    PaidRows.p6714,
    (PairReceipts.route6710 3),
    PaidRows.p6716,
    PaidRows.p6717,
    (PairReceipts.route6718 0),
    (PairReceipts.route6718 1),
    PaidRows.p6720,
    PaidRows.p6721,
    (PairReceipts.route6718 2),
    (PairReceipts.route6718 3),
    (PairReceipts.route6718 4),
    trivial⟩)
private theorem allAxes529:PairRoute.Done (2:Fin 18) ⟨⟨55,55,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6725 0),
    (PairReceipts.route6725 1),
    (PairReceipts.route6725 2),
    PaidRows.p6728,
    PaidRows.p6729,
    (PairReceipts.route6725 3),
    PaidRows.p6731,
    PaidRows.p6732,
    (PairReceipts.route6725 4),
    (PairReceipts.route6725 5),
    PaidRows.p6735,
    PaidRows.p6736,
    (PairReceipts.route6725 6),
    (PairReceipts.route6725 7),
    (PairReceipts.route6725 8),
    trivial⟩)
private theorem allAxes559:PairRoute.Done (2:Fin 18) ⟨⟨56,56,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6740 0),
    (PairReceipts.route6740 1),
    (PairReceipts.route6740 2),
    PaidRows.p6743,
    PaidRows.p6744,
    (PairReceipts.route6740 3),
    PaidRows.p6746,
    PaidRows.p6747,
    (PairReceipts.route6740 4),
    (PairReceipts.route6740 5),
    PaidRows.p6750,
    PaidRows.p6751,
    (PairReceipts.route6740 6),
    (PairReceipts.route6740 7),
    (PairReceipts.route6740 8),
    trivial⟩)
private theorem allAxes589:PairRoute.Done (2:Fin 18) ⟨⟨57,57,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6755 0),
    (PairReceipts.route6755 1),
    (PairReceipts.route6755 2),
    PaidRows.p6758,
    PaidRows.p6759,
    (PairReceipts.route6755 3),
    PaidRows.p6761,
    PaidRows.p6762,
    (PairReceipts.route6755 4),
    (PairReceipts.route6755 5),
    PaidRows.p6765,
    PaidRows.p6766,
    (PairReceipts.route6755 6),
    (PairReceipts.route6755 7),
    (PairReceipts.route6755 8),
    trivial⟩)
private theorem allAxes619:PairRoute.Done (2:Fin 18) ⟨⟨58,58,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6770 0),
    (PairReceipts.route6770 1),
    (PairReceipts.route6770 2),
    PaidRows.p6773,
    PaidRows.p6774,
    (PairReceipts.route6770 3),
    PaidRows.p6776,
    PaidRows.p6777,
    (PairReceipts.route6770 4),
    (PairReceipts.route6770 5),
    PaidRows.p6780,
    PaidRows.p6781,
    (PairReceipts.route6770 6),
    (PairReceipts.route6770 7),
    (PairReceipts.route6770 8),
    trivial⟩)
private theorem allAxes649:PairRoute.Done (2:Fin 18) ⟨⟨59,59,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6785 0),
    (PairReceipts.route6785 1),
    (PairReceipts.route6785 2),
    PaidRows.p6788,
    PaidRows.p6789,
    (PairReceipts.route6785 3),
    PaidRows.p6791,
    PaidRows.p6792,
    (PairReceipts.route6785 4),
    (PairReceipts.route6785 5),
    PaidRows.p6795,
    PaidRows.p6796,
    (PairReceipts.route6785 6),
    (PairReceipts.route6785 7),
    (PairReceipts.route6785 8),
    trivial⟩)
private theorem allAxes679:PairRoute.Done (2:Fin 18) ⟨⟨60,60,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6800 0),
    (PairReceipts.route6800 1),
    (PairReceipts.route6800 2),
    PaidRows.p6803,
    PaidRows.p6804,
    (PairReceipts.route6800 3),
    PaidRows.p6806,
    PaidRows.p6807,
    (PairReceipts.route6800 4),
    (PairReceipts.route6800 5),
    PaidRows.p6810,
    PaidRows.p6811,
    (PairReceipts.route6800 6),
    (PairReceipts.route6800 7),
    (PairReceipts.route6800 8),
    trivial⟩)
private theorem allAxes709:PairRoute.Done (2:Fin 18) ⟨⟨61,61,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6815 0),
    (PairReceipts.route6815 1),
    (PairReceipts.route6815 2),
    PaidRows.p6818,
    PaidRows.p6819,
    (PairReceipts.route6820 0),
    PaidRows.p6821,
    PaidRows.p6822,
    (PairReceipts.route6820 1),
    (PairReceipts.route6820 2),
    PaidRows.p6825,
    PaidRows.p6826,
    (PairReceipts.route6820 3),
    (PairReceipts.route6820 4),
    (PairReceipts.route6820 5),
    trivial⟩)
private theorem allAxes739:PairRoute.Done (2:Fin 18) ⟨⟨62,62,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6830 0),
    (PairReceipts.route6830 1),
    (PairReceipts.route6830 2),
    PaidRows.p6833,
    PaidRows.p6834,
    (PairReceipts.route6830 3),
    PaidRows.p6836,
    PaidRows.p6837,
    (PairReceipts.route6830 4),
    (PairReceipts.route6830 5),
    PaidRows.p6840,
    PaidRows.p6841,
    (PairReceipts.route6830 6),
    (PairReceipts.route6830 7),
    (PairReceipts.route6830 8),
    trivial⟩)
private theorem allAxes769:PairRoute.Done (2:Fin 18) ⟨⟨63,63,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6845 0),
    (PairReceipts.route6845 1),
    (PairReceipts.route6845 2),
    PaidRows.p6848,
    PaidRows.p6849,
    (PairReceipts.route6845 3),
    PaidRows.p6851,
    PaidRows.p6852,
    (PairReceipts.route6845 4),
    (PairReceipts.route6845 5),
    PaidRows.p6855,
    PaidRows.p6856,
    (PairReceipts.route6845 6),
    (PairReceipts.route6845 7),
    (PairReceipts.route6845 8),
    trivial⟩)
private theorem grade770:PairRoute.Done (2:Fin 18) ⟨⟨62,63,10,3,14,some 14⟩,0,none,385979,none⟩:=PairRoute.grade 62 allAxes739 allAxes769
private theorem grade771:PairRoute.Done (2:Fin 18) ⟨⟨61,63,10,3,14,some 14⟩,0,none,385979,none⟩:=PairRoute.grade 61 allAxes709 grade770
private theorem grade772:PairRoute.Done (2:Fin 18) ⟨⟨60,63,10,3,14,some 14⟩,0,none,385979,none⟩:=PairRoute.grade 60 allAxes679 grade771
private theorem grade773:PairRoute.Done (2:Fin 18) ⟨⟨59,63,10,3,14,some 14⟩,0,none,385979,none⟩:=PairRoute.grade 59 allAxes649 grade772
private theorem grade774:PairRoute.Done (2:Fin 18) ⟨⟨58,63,10,3,14,some 14⟩,0,none,385979,none⟩:=PairRoute.grade 58 allAxes619 grade773
private theorem grade775:PairRoute.Done (2:Fin 18) ⟨⟨57,63,10,3,14,some 14⟩,0,none,385979,none⟩:=PairRoute.grade 57 allAxes589 grade774
private theorem grade776:PairRoute.Done (2:Fin 18) ⟨⟨56,63,10,3,14,some 14⟩,0,none,385979,none⟩:=PairRoute.grade 56 allAxes559 grade775
private theorem grade777:PairRoute.Done (2:Fin 18) ⟨⟨55,63,10,3,14,some 14⟩,0,none,385979,none⟩:=PairRoute.grade 55 allAxes529 grade776
private theorem grade778:PairRoute.Done (2:Fin 18) ⟨⟨54,63,10,3,14,some 14⟩,0,none,385979,none⟩:=PairRoute.grade 54 allAxes499 grade777
private theorem grade779:PairRoute.Done (2:Fin 18) ⟨⟨53,63,10,3,14,some 14⟩,0,none,385979,none⟩:=PairRoute.grade 53 allAxes469 grade778
private theorem grade780:PairRoute.Done (2:Fin 18) ⟨⟨52,63,10,3,14,some 14⟩,0,none,385979,none⟩:=PairRoute.grade 52 allAxes439 grade779
private theorem grade781:PairRoute.Done (2:Fin 18) ⟨⟨51,63,10,3,14,some 14⟩,0,none,385979,none⟩:=PairRoute.grade 51 allAxes409 grade780
private theorem grade782:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,14,some 14⟩,0,none,385979,none⟩:=PairRoute.grade 50 allAxes379 grade781
theorem case139: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,14,some 14⟩:=PairRoute.start _ grade782
end Research6970.Height2313.Research6969.HardFit3At130
end Z6969Source2817
end Pack_R6970Height2313Dispatch0954

section Pack_R6970Height2313Dispatch0959

set_option Elab.async false

section StandaloneHardFit3At140
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HardFit3At140
open _root_.Research6970.Height2313.Research6969
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes31:PairRoute.Done (2:Fin 18) ⟨⟨50,50,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6426 0),
    (PairReceipts.route6426 1),
    (PairReceipts.route6426 2),
    PaidRows.p6429,
    PaidRows.p6430,
    (PairReceipts.route6426 3),
    PaidRows.p6432,
    PaidRows.p6433,
    (PairReceipts.route6426 4),
    (PairReceipts.route6426 5),
    PaidRows.p6436,
    PaidRows.p6437,
    (PairReceipts.route6438 0),
    (PairReceipts.route6438 1),
    (PairReceipts.route6438 2),
    (PairReceipts.route6438 3),
    trivial⟩)
private theorem allAxes63:PairRoute.Done (2:Fin 18) ⟨⟨51,51,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6442 0),
    (PairReceipts.route6442 1),
    (PairReceipts.route6442 2),
    PaidRows.p6445,
    PaidRows.p6446,
    (PairReceipts.route6442 3),
    PaidRows.p6448,
    PaidRows.p6449,
    (PairReceipts.route6442 4),
    (PairReceipts.route6442 5),
    PaidRows.p6452,
    PaidRows.p6453,
    (PairReceipts.route6442 6),
    (PairReceipts.route6442 7),
    (PairReceipts.route6442 8),
    (PairReceipts.route6442 9),
    trivial⟩)
private theorem allAxes95:PairRoute.Done (2:Fin 18) ⟨⟨52,52,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6458 0),
    (PairReceipts.route6458 1),
    (PairReceipts.route6458 2),
    PaidRows.p6461,
    PaidRows.p6462,
    (PairReceipts.route6458 3),
    PaidRows.p6464,
    PaidRows.p6465,
    (PairReceipts.route6458 4),
    (PairReceipts.route6458 5),
    PaidRows.p6468,
    PaidRows.p6469,
    (PairReceipts.route6458 6),
    (PairReceipts.route6458 7),
    (PairReceipts.route6458 8),
    (PairReceipts.route6458 9),
    trivial⟩)
private theorem allAxes127:PairRoute.Done (2:Fin 18) ⟨⟨53,53,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6474 0),
    (PairReceipts.route6474 1),
    (PairReceipts.route6474 2),
    PaidRows.p6477,
    PaidRows.p6478,
    (PairReceipts.route6474 3),
    PaidRows.p6480,
    PaidRows.p6481,
    (PairReceipts.route6474 4),
    (PairReceipts.route6474 5),
    PaidRows.p6484,
    PaidRows.p6485,
    (PairReceipts.route6474 6),
    (PairReceipts.route6474 7),
    (PairReceipts.route6474 8),
    (PairReceipts.route6474 9),
    trivial⟩)
private theorem allAxes159:PairRoute.Done (2:Fin 18) ⟨⟨54,54,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6490 0),
    (PairReceipts.route6490 1),
    (PairReceipts.route6490 2),
    PaidRows.p6493,
    PaidRows.p6494,
    (PairReceipts.route6490 3),
    PaidRows.p6496,
    PaidRows.p6497,
    (PairReceipts.route6490 4),
    (PairReceipts.route6490 5),
    PaidRows.p6500,
    PaidRows.p6501,
    (PairReceipts.route6490 6),
    (PairReceipts.route6490 7),
    (PairReceipts.route6490 8),
    (PairReceipts.route6490 9),
    trivial⟩)
private theorem allAxes191:PairRoute.Done (2:Fin 18) ⟨⟨55,55,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6506 0),
    (PairReceipts.route6506 1),
    (PairReceipts.route6506 2),
    PaidRows.p6509,
    PaidRows.p6510,
    (PairReceipts.route6506 3),
    PaidRows.p6512,
    PaidRows.p6513,
    (PairReceipts.route6506 4),
    (PairReceipts.route6506 5),
    PaidRows.p6516,
    PaidRows.p6517,
    (PairReceipts.route6506 6),
    (PairReceipts.route6506 7),
    (PairReceipts.route6506 8),
    (PairReceipts.route6506 9),
    trivial⟩)
private theorem allAxes223:PairRoute.Done (2:Fin 18) ⟨⟨56,56,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6522 0),
    (PairReceipts.route6522 1),
    (PairReceipts.route6522 2),
    PaidRows.p6525,
    PaidRows.p6526,
    (PairReceipts.route6522 3),
    PaidRows.p6528,
    PaidRows.p6529,
    (PairReceipts.route6522 4),
    (PairReceipts.route6522 5),
    PaidRows.p6532,
    PaidRows.p6533,
    (PairReceipts.route6522 6),
    (PairReceipts.route6522 7),
    (PairReceipts.route6522 8),
    (PairReceipts.route6522 9),
    trivial⟩)
private theorem allAxes255:PairRoute.Done (2:Fin 18) ⟨⟨57,57,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6538 0),
    (PairReceipts.route6538 1),
    (PairReceipts.route6538 2),
    PaidRows.p6541,
    PaidRows.p6542,
    (PairReceipts.route6538 3),
    PaidRows.p6544,
    PaidRows.p6545,
    (PairReceipts.route6538 4),
    (PairReceipts.route6538 5),
    PaidRows.p6548,
    PaidRows.p6549,
    (PairReceipts.route6538 6),
    (PairReceipts.route6538 7),
    (PairReceipts.route6538 8),
    (PairReceipts.route6538 9),
    trivial⟩)
private theorem allAxes287:PairRoute.Done (2:Fin 18) ⟨⟨58,58,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6554 0),
    (PairReceipts.route6554 1),
    (PairReceipts.route6554 2),
    PaidRows.p6557,
    PaidRows.p6558,
    (PairReceipts.route6554 3),
    PaidRows.p6560,
    PaidRows.p6561,
    (PairReceipts.route6554 4),
    (PairReceipts.route6554 5),
    PaidRows.p6564,
    PaidRows.p6565,
    (PairReceipts.route6554 6),
    (PairReceipts.route6554 7),
    (PairReceipts.route6554 8),
    (PairReceipts.route6554 9),
    trivial⟩)
private theorem allAxes319:PairRoute.Done (2:Fin 18) ⟨⟨59,59,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6570 0),
    (PairReceipts.route6570 1),
    (PairReceipts.route6570 2),
    PaidRows.p6573,
    PaidRows.p6574,
    (PairReceipts.route6570 3),
    PaidRows.p6576,
    PaidRows.p6577,
    (PairReceipts.route6570 4),
    (PairReceipts.route6570 5),
    PaidRows.p6580,
    PaidRows.p6581,
    (PairReceipts.route6570 6),
    (PairReceipts.route6570 7),
    (PairReceipts.route6570 8),
    (PairReceipts.route6570 9),
    trivial⟩)
private theorem allAxes351:PairRoute.Done (2:Fin 18) ⟨⟨60,60,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6586 0),
    (PairReceipts.route6586 1),
    (PairReceipts.route6586 2),
    PaidRows.p6589,
    PaidRows.p6590,
    (PairReceipts.route6586 3),
    PaidRows.p6592,
    PaidRows.p6593,
    (PairReceipts.route6586 4),
    (PairReceipts.route6586 5),
    PaidRows.p6596,
    PaidRows.p6597,
    (PairReceipts.route6586 6),
    (PairReceipts.route6586 7),
    (PairReceipts.route6586 8),
    (PairReceipts.route6586 9),
    trivial⟩)
private theorem allAxes383:PairRoute.Done (2:Fin 18) ⟨⟨61,61,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6602 0),
    (PairReceipts.route6602 1),
    (PairReceipts.route6602 2),
    PaidRows.p6605,
    PaidRows.p6606,
    (PairReceipts.route6602 3),
    PaidRows.p6608,
    PaidRows.p6609,
    (PairReceipts.route6602 4),
    (PairReceipts.route6602 5),
    PaidRows.p6612,
    PaidRows.p6613,
    (PairReceipts.route6602 6),
    (PairReceipts.route6602 7),
    (PairReceipts.route6602 8),
    (PairReceipts.route6602 9),
    trivial⟩)
private theorem allAxes415:PairRoute.Done (2:Fin 18) ⟨⟨62,62,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6618 0),
    (PairReceipts.route6618 1),
    (PairReceipts.route6618 2),
    PaidRows.p6621,
    PaidRows.p6622,
    (PairReceipts.route6618 3),
    PaidRows.p6624,
    PaidRows.p6625,
    (PairReceipts.route6618 4),
    (PairReceipts.route6618 5),
    PaidRows.p6628,
    PaidRows.p6629,
    (PairReceipts.route6618 6),
    (PairReceipts.route6618 7),
    (PairReceipts.route6618 8),
    (PairReceipts.route6618 9),
    trivial⟩)
private theorem allAxes447:PairRoute.Done (2:Fin 18) ⟨⟨63,63,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route6634 0),
    (PairReceipts.route6634 1),
    (PairReceipts.route6634 2),
    PaidRows.p6637,
    PaidRows.p6638,
    (PairReceipts.route6639 0),
    PaidRows.p6640,
    PaidRows.p6641,
    (PairReceipts.route6642 0),
    (PairReceipts.route6642 1),
    PaidRows.p6644,
    PaidRows.p6645,
    (PairReceipts.route6642 2),
    (PairReceipts.route6642 3),
    (PairReceipts.route6642 4),
    (PairReceipts.route6642 5),
    trivial⟩)
private theorem grade448:PairRoute.Done (2:Fin 18) ⟨⟨62,63,10,3,15,some 15⟩,0,none,385979,none⟩:=PairRoute.grade 62 allAxes415 allAxes447
private theorem grade449:PairRoute.Done (2:Fin 18) ⟨⟨61,63,10,3,15,some 15⟩,0,none,385979,none⟩:=PairRoute.grade 61 allAxes383 grade448
private theorem grade450:PairRoute.Done (2:Fin 18) ⟨⟨60,63,10,3,15,some 15⟩,0,none,385979,none⟩:=PairRoute.grade 60 allAxes351 grade449
private theorem grade451:PairRoute.Done (2:Fin 18) ⟨⟨59,63,10,3,15,some 15⟩,0,none,385979,none⟩:=PairRoute.grade 59 allAxes319 grade450
private theorem grade452:PairRoute.Done (2:Fin 18) ⟨⟨58,63,10,3,15,some 15⟩,0,none,385979,none⟩:=PairRoute.grade 58 allAxes287 grade451
private theorem grade453:PairRoute.Done (2:Fin 18) ⟨⟨57,63,10,3,15,some 15⟩,0,none,385979,none⟩:=PairRoute.grade 57 allAxes255 grade452
private theorem grade454:PairRoute.Done (2:Fin 18) ⟨⟨56,63,10,3,15,some 15⟩,0,none,385979,none⟩:=PairRoute.grade 56 allAxes223 grade453
private theorem grade455:PairRoute.Done (2:Fin 18) ⟨⟨55,63,10,3,15,some 15⟩,0,none,385979,none⟩:=PairRoute.grade 55 allAxes191 grade454
private theorem grade456:PairRoute.Done (2:Fin 18) ⟨⟨54,63,10,3,15,some 15⟩,0,none,385979,none⟩:=PairRoute.grade 54 allAxes159 grade455
private theorem grade457:PairRoute.Done (2:Fin 18) ⟨⟨53,63,10,3,15,some 15⟩,0,none,385979,none⟩:=PairRoute.grade 53 allAxes127 grade456
private theorem grade458:PairRoute.Done (2:Fin 18) ⟨⟨52,63,10,3,15,some 15⟩,0,none,385979,none⟩:=PairRoute.grade 52 allAxes95 grade457
private theorem grade459:PairRoute.Done (2:Fin 18) ⟨⟨51,63,10,3,15,some 15⟩,0,none,385979,none⟩:=PairRoute.grade 51 allAxes63 grade458
private theorem grade460:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,15,some 15⟩,0,none,385979,none⟩:=PairRoute.grade 50 allAxes31 grade459
theorem case140: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,15,some 15⟩:=PairRoute.start _ grade460
private theorem allAxes494:PairRoute.Done (2:Fin 18) ⟨⟨50,50,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6188 0),
    (PairReceipts.route6188 1),
    (PairReceipts.route6188 2),
    PaidRows.p6191,
    PaidRows.p6192,
    (PairReceipts.route6188 3),
    PaidRows.p6194,
    PaidRows.p6195,
    (PairReceipts.route6188 4),
    (PairReceipts.route6188 5),
    PaidRows.p6198,
    PaidRows.p6199,
    (PairReceipts.route6188 6),
    (PairReceipts.route6188 7),
    (PairReceipts.route6188 8),
    (PairReceipts.route6188 9),
    (PairReceipts.route6188 10),
    trivial⟩)
private theorem allAxes528:PairRoute.Done (2:Fin 18) ⟨⟨51,51,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6205 0),
    (PairReceipts.route6205 1),
    (PairReceipts.route6205 2),
    PaidRows.p6208,
    PaidRows.p6209,
    (PairReceipts.route6205 3),
    PaidRows.p6211,
    PaidRows.p6212,
    (PairReceipts.route6205 4),
    (PairReceipts.route6205 5),
    PaidRows.p6215,
    PaidRows.p6216,
    (PairReceipts.route6205 6),
    (PairReceipts.route6205 7),
    (PairReceipts.route6205 8),
    (PairReceipts.route6205 9),
    (PairReceipts.route6205 10),
    trivial⟩)
private theorem allAxes562:PairRoute.Done (2:Fin 18) ⟨⟨52,52,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6222 0),
    (PairReceipts.route6222 1),
    (PairReceipts.route6222 2),
    PaidRows.p6225,
    PaidRows.p6226,
    (PairReceipts.route6222 3),
    PaidRows.p6228,
    PaidRows.p6229,
    (PairReceipts.route6222 4),
    (PairReceipts.route6222 5),
    PaidRows.p6232,
    PaidRows.p6233,
    (PairReceipts.route6222 6),
    (PairReceipts.route6222 7),
    (PairReceipts.route6222 8),
    (PairReceipts.route6222 9),
    (PairReceipts.route6238 0),
    trivial⟩)
private theorem allAxes596:PairRoute.Done (2:Fin 18) ⟨⟨53,53,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6239 0),
    (PairReceipts.route6239 1),
    (PairReceipts.route6239 2),
    PaidRows.p6242,
    PaidRows.p6243,
    (PairReceipts.route6239 3),
    PaidRows.p6245,
    PaidRows.p6246,
    (PairReceipts.route6239 4),
    (PairReceipts.route6239 5),
    PaidRows.p6249,
    PaidRows.p6250,
    (PairReceipts.route6239 6),
    (PairReceipts.route6239 7),
    (PairReceipts.route6239 8),
    (PairReceipts.route6239 9),
    (PairReceipts.route6239 10),
    trivial⟩)
private theorem allAxes630:PairRoute.Done (2:Fin 18) ⟨⟨54,54,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6256 0),
    (PairReceipts.route6256 1),
    (PairReceipts.route6256 2),
    PaidRows.p6259,
    PaidRows.p6260,
    (PairReceipts.route6256 3),
    PaidRows.p6262,
    PaidRows.p6263,
    (PairReceipts.route6256 4),
    (PairReceipts.route6256 5),
    PaidRows.p6266,
    PaidRows.p6267,
    (PairReceipts.route6256 6),
    (PairReceipts.route6256 7),
    (PairReceipts.route6256 8),
    (PairReceipts.route6256 9),
    (PairReceipts.route6256 10),
    trivial⟩)
private theorem allAxes664:PairRoute.Done (2:Fin 18) ⟨⟨55,55,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6273 0),
    (PairReceipts.route6273 1),
    (PairReceipts.route6273 2),
    PaidRows.p6276,
    PaidRows.p6277,
    (PairReceipts.route6273 3),
    PaidRows.p6279,
    PaidRows.p6280,
    (PairReceipts.route6273 4),
    (PairReceipts.route6273 5),
    PaidRows.p6283,
    PaidRows.p6284,
    (PairReceipts.route6273 6),
    (PairReceipts.route6273 7),
    (PairReceipts.route6273 8),
    (PairReceipts.route6273 9),
    (PairReceipts.route6273 10),
    trivial⟩)
private theorem allAxes698:PairRoute.Done (2:Fin 18) ⟨⟨56,56,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6290 0),
    (PairReceipts.route6290 1),
    (PairReceipts.route6290 2),
    PaidRows.p6293,
    PaidRows.p6294,
    (PairReceipts.route6290 3),
    PaidRows.p6296,
    PaidRows.p6297,
    (PairReceipts.route6290 4),
    (PairReceipts.route6290 5),
    PaidRows.p6300,
    PaidRows.p6301,
    (PairReceipts.route6290 6),
    (PairReceipts.route6290 7),
    (PairReceipts.route6290 8),
    (PairReceipts.route6290 9),
    (PairReceipts.route6290 10),
    trivial⟩)
private theorem allAxes732:PairRoute.Done (2:Fin 18) ⟨⟨57,57,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6307 0),
    (PairReceipts.route6307 1),
    (PairReceipts.route6307 2),
    PaidRows.p6310,
    PaidRows.p6311,
    (PairReceipts.route6307 3),
    PaidRows.p6313,
    PaidRows.p6314,
    (PairReceipts.route6307 4),
    (PairReceipts.route6307 5),
    PaidRows.p6317,
    PaidRows.p6318,
    (PairReceipts.route6307 6),
    (PairReceipts.route6307 7),
    (PairReceipts.route6307 8),
    (PairReceipts.route6307 9),
    (PairReceipts.route6307 10),
    trivial⟩)
private theorem allAxes766:PairRoute.Done (2:Fin 18) ⟨⟨58,58,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6324 0),
    (PairReceipts.route6324 1),
    (PairReceipts.route6324 2),
    PaidRows.p6327,
    PaidRows.p6328,
    (PairReceipts.route6324 3),
    PaidRows.p6330,
    PaidRows.p6331,
    (PairReceipts.route6324 4),
    (PairReceipts.route6324 5),
    PaidRows.p6334,
    PaidRows.p6335,
    (PairReceipts.route6324 6),
    (PairReceipts.route6324 7),
    (PairReceipts.route6338 0),
    (PairReceipts.route6338 1),
    (PairReceipts.route6338 2),
    trivial⟩)
private theorem allAxes800:PairRoute.Done (2:Fin 18) ⟨⟨59,59,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6341 0),
    (PairReceipts.route6341 1),
    (PairReceipts.route6341 2),
    PaidRows.p6344,
    PaidRows.p6345,
    (PairReceipts.route6341 3),
    PaidRows.p6347,
    PaidRows.p6348,
    (PairReceipts.route6341 4),
    (PairReceipts.route6341 5),
    PaidRows.p6351,
    PaidRows.p6352,
    (PairReceipts.route6341 6),
    (PairReceipts.route6341 7),
    (PairReceipts.route6341 8),
    (PairReceipts.route6341 9),
    (PairReceipts.route6341 10),
    trivial⟩)
private theorem allAxes834:PairRoute.Done (2:Fin 18) ⟨⟨60,60,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6358 0),
    (PairReceipts.route6358 1),
    (PairReceipts.route6358 2),
    PaidRows.p6361,
    PaidRows.p6362,
    (PairReceipts.route6358 3),
    PaidRows.p6364,
    PaidRows.p6365,
    (PairReceipts.route6358 4),
    (PairReceipts.route6358 5),
    PaidRows.p6368,
    PaidRows.p6369,
    (PairReceipts.route6358 6),
    (PairReceipts.route6358 7),
    (PairReceipts.route6358 8),
    (PairReceipts.route6358 9),
    (PairReceipts.route6358 10),
    trivial⟩)
private theorem allAxes868:PairRoute.Done (2:Fin 18) ⟨⟨61,61,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6375 0),
    (PairReceipts.route6375 1),
    (PairReceipts.route6375 2),
    PaidRows.p6378,
    PaidRows.p6379,
    (PairReceipts.route6375 3),
    PaidRows.p6381,
    PaidRows.p6382,
    (PairReceipts.route6375 4),
    (PairReceipts.route6375 5),
    PaidRows.p6385,
    PaidRows.p6386,
    (PairReceipts.route6375 6),
    (PairReceipts.route6375 7),
    (PairReceipts.route6375 8),
    (PairReceipts.route6375 9),
    (PairReceipts.route6375 10),
    trivial⟩)
private theorem allAxes902:PairRoute.Done (2:Fin 18) ⟨⟨62,62,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6392 0),
    (PairReceipts.route6392 1),
    (PairReceipts.route6392 2),
    PaidRows.p6395,
    PaidRows.p6396,
    (PairReceipts.route6392 3),
    PaidRows.p6398,
    PaidRows.p6399,
    (PairReceipts.route6392 4),
    (PairReceipts.route6392 5),
    PaidRows.p6402,
    PaidRows.p6403,
    (PairReceipts.route6392 6),
    (PairReceipts.route6392 7),
    (PairReceipts.route6392 8),
    (PairReceipts.route6392 9),
    (PairReceipts.route6392 10),
    trivial⟩)
private theorem allAxes936:PairRoute.Done (2:Fin 18) ⟨⟨63,63,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route6409 0),
    (PairReceipts.route6409 1),
    (PairReceipts.route6409 2),
    PaidRows.p6412,
    PaidRows.p6413,
    (PairReceipts.route6409 3),
    PaidRows.p6415,
    PaidRows.p6416,
    (PairReceipts.route6409 4),
    (PairReceipts.route6409 5),
    PaidRows.p6419,
    PaidRows.p6420,
    (PairReceipts.route6409 6),
    (PairReceipts.route6409 7),
    (PairReceipts.route6409 8),
    (PairReceipts.route6409 9),
    (PairReceipts.route6409 10),
    trivial⟩)
private theorem grade937:PairRoute.Done (2:Fin 18) ⟨⟨62,63,10,3,16,some 16⟩,0,none,385979,none⟩:=PairRoute.grade 62 allAxes902 allAxes936
private theorem grade938:PairRoute.Done (2:Fin 18) ⟨⟨61,63,10,3,16,some 16⟩,0,none,385979,none⟩:=PairRoute.grade 61 allAxes868 grade937
private theorem grade939:PairRoute.Done (2:Fin 18) ⟨⟨60,63,10,3,16,some 16⟩,0,none,385979,none⟩:=PairRoute.grade 60 allAxes834 grade938
private theorem grade940:PairRoute.Done (2:Fin 18) ⟨⟨59,63,10,3,16,some 16⟩,0,none,385979,none⟩:=PairRoute.grade 59 allAxes800 grade939
private theorem grade941:PairRoute.Done (2:Fin 18) ⟨⟨58,63,10,3,16,some 16⟩,0,none,385979,none⟩:=PairRoute.grade 58 allAxes766 grade940
private theorem grade942:PairRoute.Done (2:Fin 18) ⟨⟨57,63,10,3,16,some 16⟩,0,none,385979,none⟩:=PairRoute.grade 57 allAxes732 grade941
private theorem grade943:PairRoute.Done (2:Fin 18) ⟨⟨56,63,10,3,16,some 16⟩,0,none,385979,none⟩:=PairRoute.grade 56 allAxes698 grade942
private theorem grade944:PairRoute.Done (2:Fin 18) ⟨⟨55,63,10,3,16,some 16⟩,0,none,385979,none⟩:=PairRoute.grade 55 allAxes664 grade943
private theorem grade945:PairRoute.Done (2:Fin 18) ⟨⟨54,63,10,3,16,some 16⟩,0,none,385979,none⟩:=PairRoute.grade 54 allAxes630 grade944
private theorem grade946:PairRoute.Done (2:Fin 18) ⟨⟨53,63,10,3,16,some 16⟩,0,none,385979,none⟩:=PairRoute.grade 53 allAxes596 grade945
private theorem grade947:PairRoute.Done (2:Fin 18) ⟨⟨52,63,10,3,16,some 16⟩,0,none,385979,none⟩:=PairRoute.grade 52 allAxes562 grade946
private theorem grade948:PairRoute.Done (2:Fin 18) ⟨⟨51,63,10,3,16,some 16⟩,0,none,385979,none⟩:=PairRoute.grade 51 allAxes528 grade947
private theorem grade949:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,16,some 16⟩,0,none,385979,none⟩:=PairRoute.grade 50 allAxes494 grade948
theorem case141: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,16,some 16⟩:=PairRoute.start _ grade949
private theorem allAxes985:PairRoute.Done (2:Fin 18) ⟨⟨50,50,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route5936 0),
    (PairReceipts.route5936 1),
    (PairReceipts.route5938 0),
    PaidRows.p5939,
    PaidRows.p5940,
    (PairReceipts.route5938 1),
    PaidRows.p5942,
    PaidRows.p5943,
    (PairReceipts.route5938 2),
    (PairReceipts.route5938 3),
    PaidRows.p5946,
    PaidRows.p5947,
    (PairReceipts.route5938 4),
    (PairReceipts.route5938 5),
    (PairReceipts.route5938 6),
    (PairReceipts.route5938 7),
    (PairReceipts.route5938 8),
    PaidRows.p5953,
    trivial⟩)
private theorem allAxes1021:PairRoute.Done (2:Fin 18) ⟨⟨51,51,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route5954 0),
    (PairReceipts.route5954 1),
    (PairReceipts.route5954 2),
    PaidRows.p5957,
    PaidRows.p5958,
    (PairReceipts.route5954 3),
    PaidRows.p5960,
    PaidRows.p5961,
    (PairReceipts.route5954 4),
    (PairReceipts.route5954 5),
    PaidRows.p5964,
    PaidRows.p5965,
    (PairReceipts.route5954 6),
    (PairReceipts.route5954 7),
    (PairReceipts.route5954 8),
    (PairReceipts.route5954 9),
    (PairReceipts.route5954 10),
    PaidRows.p5971,
    trivial⟩)
private theorem allAxes1057:PairRoute.Done (2:Fin 18) ⟨⟨52,52,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route5972 0),
    (PairReceipts.route5972 1),
    (PairReceipts.route5972 2),
    PaidRows.p5975,
    PaidRows.p5976,
    (PairReceipts.route5972 3),
    PaidRows.p5978,
    PaidRows.p5979,
    (PairReceipts.route5972 4),
    (PairReceipts.route5972 5),
    PaidRows.p5982,
    PaidRows.p5983,
    (PairReceipts.route5972 6),
    (PairReceipts.route5972 7),
    (PairReceipts.route5972 8),
    (PairReceipts.route5972 9),
    (PairReceipts.route5972 10),
    PaidRows.p5989,
    trivial⟩)
private theorem allAxes1093:PairRoute.Done (2:Fin 18) ⟨⟨53,53,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route5990 0),
    (PairReceipts.route5990 1),
    (PairReceipts.route5990 2),
    PaidRows.p5993,
    PaidRows.p5994,
    (PairReceipts.route5990 3),
    PaidRows.p5996,
    PaidRows.p5997,
    (PairReceipts.route5990 4),
    (PairReceipts.route5990 5),
    PaidRows.p6000,
    PaidRows.p6001,
    (PairReceipts.route5990 6),
    (PairReceipts.route5990 7),
    (PairReceipts.route5990 8),
    (PairReceipts.route5990 9),
    (PairReceipts.route5990 10),
    PaidRows.p6007,
    trivial⟩)
private theorem allAxes1129:PairRoute.Done (2:Fin 18) ⟨⟨54,54,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6008 0),
    (PairReceipts.route6008 1),
    (PairReceipts.route6008 2),
    PaidRows.p6011,
    PaidRows.p6012,
    (PairReceipts.route6008 3),
    PaidRows.p6014,
    PaidRows.p6015,
    (PairReceipts.route6008 4),
    (PairReceipts.route6008 5),
    PaidRows.p6018,
    PaidRows.p6019,
    (PairReceipts.route6008 6),
    (PairReceipts.route6008 7),
    (PairReceipts.route6008 8),
    (PairReceipts.route6008 9),
    (PairReceipts.route6008 10),
    PaidRows.p6025,
    trivial⟩)
private theorem allAxes1165:PairRoute.Done (2:Fin 18) ⟨⟨55,55,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6026 0),
    (PairReceipts.route6026 1),
    (PairReceipts.route6026 2),
    PaidRows.p6029,
    PaidRows.p6030,
    (PairReceipts.route6026 3),
    PaidRows.p6032,
    PaidRows.p6033,
    (PairReceipts.route6026 4),
    (PairReceipts.route6026 5),
    PaidRows.p6036,
    PaidRows.p6037,
    (PairReceipts.route6038 0),
    (PairReceipts.route6038 1),
    (PairReceipts.route6038 2),
    (PairReceipts.route6038 3),
    (PairReceipts.route6038 4),
    PaidRows.p6043,
    trivial⟩)
private theorem allAxes1201:PairRoute.Done (2:Fin 18) ⟨⟨56,56,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6044 0),
    (PairReceipts.route6044 1),
    (PairReceipts.route6044 2),
    PaidRows.p6047,
    PaidRows.p6048,
    (PairReceipts.route6044 3),
    PaidRows.p6050,
    PaidRows.p6051,
    (PairReceipts.route6044 4),
    (PairReceipts.route6044 5),
    PaidRows.p6054,
    PaidRows.p6055,
    (PairReceipts.route6044 6),
    (PairReceipts.route6044 7),
    (PairReceipts.route6044 8),
    (PairReceipts.route6044 9),
    (PairReceipts.route6044 10),
    PaidRows.p6061,
    trivial⟩)
private theorem allAxes1237:PairRoute.Done (2:Fin 18) ⟨⟨57,57,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6062 0),
    (PairReceipts.route6062 1),
    (PairReceipts.route6062 2),
    PaidRows.p6065,
    PaidRows.p6066,
    (PairReceipts.route6062 3),
    PaidRows.p6068,
    PaidRows.p6069,
    (PairReceipts.route6062 4),
    (PairReceipts.route6062 5),
    PaidRows.p6072,
    PaidRows.p6073,
    (PairReceipts.route6062 6),
    (PairReceipts.route6062 7),
    (PairReceipts.route6062 8),
    (PairReceipts.route6062 9),
    (PairReceipts.route6062 10),
    PaidRows.p6079,
    trivial⟩)
private theorem allAxes1273:PairRoute.Done (2:Fin 18) ⟨⟨58,58,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6080 0),
    (PairReceipts.route6080 1),
    (PairReceipts.route6080 2),
    PaidRows.p6083,
    PaidRows.p6084,
    (PairReceipts.route6080 3),
    PaidRows.p6086,
    PaidRows.p6087,
    (PairReceipts.route6080 4),
    (PairReceipts.route6080 5),
    PaidRows.p6090,
    PaidRows.p6091,
    (PairReceipts.route6080 6),
    (PairReceipts.route6080 7),
    (PairReceipts.route6080 8),
    (PairReceipts.route6080 9),
    (PairReceipts.route6080 10),
    PaidRows.p6097,
    trivial⟩)
private theorem allAxes1309:PairRoute.Done (2:Fin 18) ⟨⟨59,59,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6098 0),
    (PairReceipts.route6098 1),
    (PairReceipts.route6098 2),
    PaidRows.p6101,
    PaidRows.p6102,
    (PairReceipts.route6098 3),
    PaidRows.p6104,
    PaidRows.p6105,
    (PairReceipts.route6098 4),
    (PairReceipts.route6098 5),
    PaidRows.p6108,
    PaidRows.p6109,
    (PairReceipts.route6098 6),
    (PairReceipts.route6098 7),
    (PairReceipts.route6098 8),
    (PairReceipts.route6098 9),
    (PairReceipts.route6098 10),
    PaidRows.p6115,
    trivial⟩)
private theorem allAxes1345:PairRoute.Done (2:Fin 18) ⟨⟨60,60,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6116 0),
    (PairReceipts.route6116 1),
    (PairReceipts.route6116 2),
    PaidRows.p6119,
    PaidRows.p6120,
    (PairReceipts.route6116 3),
    PaidRows.p6122,
    PaidRows.p6123,
    (PairReceipts.route6116 4),
    (PairReceipts.route6116 5),
    PaidRows.p6126,
    PaidRows.p6127,
    (PairReceipts.route6116 6),
    (PairReceipts.route6116 7),
    (PairReceipts.route6116 8),
    (PairReceipts.route6116 9),
    (PairReceipts.route6116 10),
    PaidRows.p6133,
    trivial⟩)
private theorem allAxes1381:PairRoute.Done (2:Fin 18) ⟨⟨61,61,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6134 0),
    (PairReceipts.route6134 1),
    (PairReceipts.route6134 2),
    PaidRows.p6137,
    PaidRows.p6138,
    (PairReceipts.route6139 0),
    PaidRows.p6140,
    PaidRows.p6141,
    (PairReceipts.route6139 1),
    (PairReceipts.route6139 2),
    PaidRows.p6144,
    PaidRows.p6145,
    (PairReceipts.route6139 3),
    (PairReceipts.route6139 4),
    (PairReceipts.route6139 5),
    (PairReceipts.route6139 6),
    (PairReceipts.route6139 7),
    PaidRows.p6151,
    trivial⟩)
private theorem allAxes1417:PairRoute.Done (2:Fin 18) ⟨⟨62,62,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6152 0),
    (PairReceipts.route6152 1),
    (PairReceipts.route6152 2),
    PaidRows.p6155,
    PaidRows.p6156,
    (PairReceipts.route6152 3),
    PaidRows.p6158,
    PaidRows.p6159,
    (PairReceipts.route6152 4),
    (PairReceipts.route6152 5),
    PaidRows.p6162,
    PaidRows.p6163,
    (PairReceipts.route6152 6),
    (PairReceipts.route6152 7),
    (PairReceipts.route6152 8),
    (PairReceipts.route6152 9),
    (PairReceipts.route6152 10),
    PaidRows.p6169,
    trivial⟩)
private theorem allAxes1453:PairRoute.Done (2:Fin 18) ⟨⟨63,63,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route6170 0),
    (PairReceipts.route6170 1),
    (PairReceipts.route6170 2),
    PaidRows.p6173,
    PaidRows.p6174,
    (PairReceipts.route6170 3),
    PaidRows.p6176,
    PaidRows.p6177,
    (PairReceipts.route6170 4),
    (PairReceipts.route6170 5),
    PaidRows.p6180,
    PaidRows.p6181,
    (PairReceipts.route6170 6),
    (PairReceipts.route6170 7),
    (PairReceipts.route6170 8),
    (PairReceipts.route6170 9),
    (PairReceipts.route6170 10),
    PaidRows.p6187,
    trivial⟩)
private theorem grade1454:PairRoute.Done (2:Fin 18) ⟨⟨62,63,10,3,17,some 17⟩,0,none,385979,none⟩:=PairRoute.grade 62 allAxes1417 allAxes1453
private theorem grade1455:PairRoute.Done (2:Fin 18) ⟨⟨61,63,10,3,17,some 17⟩,0,none,385979,none⟩:=PairRoute.grade 61 allAxes1381 grade1454
private theorem grade1456:PairRoute.Done (2:Fin 18) ⟨⟨60,63,10,3,17,some 17⟩,0,none,385979,none⟩:=PairRoute.grade 60 allAxes1345 grade1455
private theorem grade1457:PairRoute.Done (2:Fin 18) ⟨⟨59,63,10,3,17,some 17⟩,0,none,385979,none⟩:=PairRoute.grade 59 allAxes1309 grade1456
private theorem grade1458:PairRoute.Done (2:Fin 18) ⟨⟨58,63,10,3,17,some 17⟩,0,none,385979,none⟩:=PairRoute.grade 58 allAxes1273 grade1457
private theorem grade1459:PairRoute.Done (2:Fin 18) ⟨⟨57,63,10,3,17,some 17⟩,0,none,385979,none⟩:=PairRoute.grade 57 allAxes1237 grade1458
private theorem grade1460:PairRoute.Done (2:Fin 18) ⟨⟨56,63,10,3,17,some 17⟩,0,none,385979,none⟩:=PairRoute.grade 56 allAxes1201 grade1459
private theorem grade1461:PairRoute.Done (2:Fin 18) ⟨⟨55,63,10,3,17,some 17⟩,0,none,385979,none⟩:=PairRoute.grade 55 allAxes1165 grade1460
private theorem grade1462:PairRoute.Done (2:Fin 18) ⟨⟨54,63,10,3,17,some 17⟩,0,none,385979,none⟩:=PairRoute.grade 54 allAxes1129 grade1461
private theorem grade1463:PairRoute.Done (2:Fin 18) ⟨⟨53,63,10,3,17,some 17⟩,0,none,385979,none⟩:=PairRoute.grade 53 allAxes1093 grade1462
private theorem grade1464:PairRoute.Done (2:Fin 18) ⟨⟨52,63,10,3,17,some 17⟩,0,none,385979,none⟩:=PairRoute.grade 52 allAxes1057 grade1463
private theorem grade1465:PairRoute.Done (2:Fin 18) ⟨⟨51,63,10,3,17,some 17⟩,0,none,385979,none⟩:=PairRoute.grade 51 allAxes1021 grade1464
private theorem grade1466:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,17,some 17⟩,0,none,385979,none⟩:=PairRoute.grade 50 allAxes985 grade1465
theorem case142: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,17,some 17⟩:=PairRoute.start _ grade1466
private theorem allAxes1504:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,18,some 18⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 18 ⟨
    (PairReceipts.route3340 15),
    (PairReceipts.route3340 16),
    (PairReceipts.route3340 17),
    PaidRows.p3370,
    PaidRows.p3371,
    (PairReceipts.route3340 18),
    PaidRows.p3373,
    PaidRows.p3374,
    (PairReceipts.route3340 19),
    PaidRows.p3376,
    PaidRows.p3377,
    PaidRows.p3378,
    PaidRows.p3379,
    PaidRows.p3380,
    (PairReceipts.route3381 0),
    (PairReceipts.route3381 1),
    (PairReceipts.route3381 2),
    PaidRows.p3384,
    (PairReceipts.route3381 3),
    trivial⟩)
theorem case143: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,18,some 18⟩:=PairRoute.start _ allAxes1504
private theorem allAxes1544:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,19,some 19⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 19 ⟨
    (PairReceipts.route3340 6),
    (PairReceipts.route3340 7),
    (PairReceipts.route3340 8),
    PaidRows.p3350,
    PaidRows.p3351,
    (PairReceipts.route3340 9),
    PaidRows.p3353,
    PaidRows.p3354,
    PaidRows.p3355,
    PaidRows.p3356,
    PaidRows.p3357,
    PaidRows.p3358,
    PaidRows.p3359,
    PaidRows.p3360,
    (PairReceipts.route3340 10),
    (PairReceipts.route3340 11),
    (PairReceipts.route3340 12),
    PaidRows.p3364,
    (PairReceipts.route3340 13),
    (PairReceipts.route3340 14),
    trivial⟩)
theorem case144: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,19,some 19⟩:=PairRoute.start _ allAxes1544
private theorem allAxes1586:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,20,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route3299 20),
    (PairReceipts.route3299 21),
    (PairReceipts.route3299 22),
    PaidRows.p3329,
    PaidRows.p3330,
    (PairReceipts.route3299 23),
    PaidRows.p3332,
    PaidRows.p3333,
    PaidRows.p3334,
    PaidRows.p3335,
    PaidRows.p3336,
    PaidRows.p3337,
    PaidRows.p3338,
    PaidRows.p3339,
    (PairReceipts.route3340 0),
    (PairReceipts.route3340 1),
    (PairReceipts.route3340 2),
    PaidRows.p3343,
    (PairReceipts.route3340 3),
    (PairReceipts.route3340 4),
    (PairReceipts.route3340 5),
    trivial⟩)
theorem case145: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,20,some 20⟩:=PairRoute.start _ allAxes1586
private theorem allAxes1630:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,21,some 21⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 21 ⟨
    (PairReceipts.route3299 5),
    (PairReceipts.route3299 6),
    (PairReceipts.route3299 7),
    PaidRows.p3307,
    PaidRows.p3308,
    (PairReceipts.route3299 8),
    PaidRows.p3310,
    PaidRows.p3311,
    (PairReceipts.route3299 9),
    (PairReceipts.route3299 10),
    PaidRows.p3314,
    PaidRows.p3315,
    (PairReceipts.route3299 11),
    (PairReceipts.route3299 12),
    (PairReceipts.route3299 13),
    (PairReceipts.route3299 14),
    (PairReceipts.route3299 15),
    PaidRows.p3321,
    (PairReceipts.route3299 16),
    (PairReceipts.route3299 17),
    (PairReceipts.route3299 18),
    (PairReceipts.route3299 19),
    trivial⟩)
theorem case146: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,21,some 21⟩:=PairRoute.start _ allAxes1630
private theorem allAxes1676:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,22,some 22⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 22 ⟨
    PaidRows.p3281,
    PaidRows.p3282,
    PaidRows.p3283,
    PaidRows.p3284,
    PaidRows.p3285,
    (PairReceipts.route3242 20),
    PaidRows.p3287,
    PaidRows.p3288,
    (PairReceipts.route3242 21),
    (PairReceipts.route3242 22),
    PaidRows.p3291,
    PaidRows.p3292,
    (PairReceipts.route3242 23),
    (PairReceipts.route3294 0),
    (PairReceipts.route3294 1),
    (PairReceipts.route3294 2),
    (PairReceipts.route3294 3),
    PaidRows.p3298,
    (PairReceipts.route3299 0),
    (PairReceipts.route3299 1),
    (PairReceipts.route3299 2),
    (PairReceipts.route3299 3),
    (PairReceipts.route3299 4),
    trivial⟩)
theorem case147: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,22,some 22⟩:=PairRoute.start _ allAxes1676
private theorem allAxes1724:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,23,some 23⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 23 ⟨
    PaidRows.p3257,
    PaidRows.p3258,
    PaidRows.p3259,
    PaidRows.p3260,
    PaidRows.p3261,
    PaidRows.p3262,
    PaidRows.p3263,
    PaidRows.p3264,
    PaidRows.p3265,
    PaidRows.p3266,
    PaidRows.p3267,
    PaidRows.p3268,
    PaidRows.p3269,
    PaidRows.p3270,
    PaidRows.p3271,
    PaidRows.p3272,
    (PairReceipts.route3242 13),
    PaidRows.p3274,
    (PairReceipts.route3242 14),
    (PairReceipts.route3242 15),
    (PairReceipts.route3242 16),
    (PairReceipts.route3242 17),
    (PairReceipts.route3242 18),
    (PairReceipts.route3242 19),
    trivial⟩)
theorem case148: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,23,some 23⟩:=PairRoute.start _ allAxes1724
private theorem leaf1725:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,24,some 24⟩,0,none,385979,none⟩:=PaidRows.p3256
theorem case149: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,24,some 24⟩:=PairRoute.start _ leaf1725
end Research6970.Height2313.Research6969.HardFit3At140
end StandaloneHardFit3At140
end Pack_R6970Height2313Dispatch0959

section Pack_R6970Height2313Dispatch0960

set_option Elab.async false

section Z6969Source2863
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HardFit3At150
open _root_.Research6970.Height2313.Research6969
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes51:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,25,some 25⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 25 ⟨
    (PairReceipts.route3223 4),
    (PairReceipts.route3223 5),
    PaidRows.p3232,
    PaidRows.p3233,
    PaidRows.p3234,
    PaidRows.p3235,
    PaidRows.p3236,
    PaidRows.p3237,
    (PairReceipts.route3223 6),
    (PairReceipts.route3223 7),
    PaidRows.p3240,
    PaidRows.p3241,
    (PairReceipts.route3242 0),
    (PairReceipts.route3242 1),
    (PairReceipts.route3242 2),
    (PairReceipts.route3242 3),
    (PairReceipts.route3242 4),
    PaidRows.p3247,
    (PairReceipts.route3242 5),
    (PairReceipts.route3242 6),
    (PairReceipts.route3242 7),
    (PairReceipts.route3242 8),
    (PairReceipts.route3242 9),
    (PairReceipts.route3242 10),
    (PairReceipts.route3242 11),
    (PairReceipts.route3242 12),
    trivial⟩)
theorem case150: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,25,some 25⟩:=PairRoute.start _ allAxes51
private theorem leaf52:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,26,some 26⟩,0,none,385979,none⟩:=PaidRows.p3229
theorem case151: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,26,some 26⟩:=PairRoute.start _ leaf52
private theorem leaf53:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,27,some 27⟩,0,none,385979,none⟩:=(PairReceipts.route3223 3)
theorem case152: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,27,some 27⟩:=PairRoute.start _ leaf53
private theorem leaf54:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,28,some 28⟩,0,none,385979,none⟩:=(PairReceipts.route3223 2)
theorem case153: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,28,some 28⟩:=PairRoute.start _ leaf54
private theorem leaf55:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,29,some 29⟩,0,none,385979,none⟩:=(PairReceipts.route3223 1)
theorem case154: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,29,some 29⟩:=PairRoute.start _ leaf55
private theorem leaf56:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,30,some 30⟩,0,none,385979,none⟩:=PaidRows.p3225
theorem case155: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,30,some 30⟩:=PairRoute.start _ leaf56
private theorem leaf57:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,31,some 32⟩,0,none,385979,none⟩:=PaidRows.p3224
theorem case156: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,31,some 32⟩:=PairRoute.start _ leaf57
private theorem leaf58:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,33,some 33⟩,0,none,385979,none⟩:=(PairReceipts.route3223 0)
theorem case157: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,33,some 33⟩:=PairRoute.start _ leaf58
private theorem leaf59:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,34,some 34⟩,0,none,385979,none⟩:=PaidRows.p3222
theorem case158: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,34,some 34⟩:=PairRoute.start _ leaf59
private theorem leaf60:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,35,some 35⟩,0,none,385979,none⟩:=PaidRows.p3221
theorem case159: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,35,some 35⟩:=PairRoute.start _ leaf60
end Research6970.Height2313.Research6969.HardFit3At150
end Z6969Source2863
end Pack_R6970Height2313Dispatch0960
