import ProximityPrize.SubmissionLower.R6960Low6960Rectangle
import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960RetainedCount
import ProximityPrize.SubmissionLower.R6960Low6960Mass0
import ProximityPrize.SubmissionLower.R6960Low6960Mass1
import ProximityPrize.SubmissionLower.R6960Low6960Mass2
import ProximityPrize.SubmissionLower.R6960Low6960Mass3
import ProximityPrize.SubmissionLower.R6960Low6960Mass4
import ProximityPrize.SubmissionLower.R6960Low6960Mass5
import ProximityPrize.SubmissionLower.R6960Low6960Mass6
import ProximityPrize.SubmissionLower.R6960Low6960Mass7
import ProximityPrize.SubmissionLower.R6960Low6960Mass8
import ProximityPrize.SubmissionLower.R6960Low6960Mass9
import ProximityPrize.SubmissionLower.R6960Low6960Mass10
import ProximityPrize.SubmissionLower.R6960Low6960Mass11
import ProximityPrize.SubmissionLower.R6960Low6960Mass12
import ProximityPrize.SubmissionLower.R6960Low6960Mass13
import ProximityPrize.SubmissionLower.R6960Low6960Mass14
import ProximityPrize.SubmissionLower.R6960Low6960Mass15
import ProximityPrize.SubmissionLower.R6960Low6960Mass16
import ProximityPrize.SubmissionLower.R6960Low6960Mass17
import ProximityPrize.SubmissionLower.R6960Low6960Mass18
import ProximityPrize.SubmissionLower.R6960Low6960Mass19
import ProximityPrize.SubmissionLower.R6960Low6960Mass20
import ProximityPrize.SubmissionLower.R6960Low6960Mass21
import ProximityPrize.SubmissionLower.R6960Low6960Mass22
import ProximityPrize.SubmissionLower.R6960Low6960Mass23
import ProximityPrize.SubmissionLower.R6960Low6960Mass24
import ProximityPrize.SubmissionLower.R6960Low6960Mass25
import ProximityPrize.SubmissionLower.R6960Low6960Mass26
import ProximityPrize.SubmissionLower.R6960Low6960Mass27
import ProximityPrize.SubmissionLower.R6960Low6960Mass28
import ProximityPrize.SubmissionLower.R6960Low6960Mass29
import ProximityPrize.SubmissionLower.R6960Low6960Mass30
import ProximityPrize.SubmissionLower.R6960Low6960Mass31
import ProximityPrize.SubmissionLower.R6960Low6960Mass32
import ProximityPrize.SubmissionLower.R6960Low6960Mass33
import ProximityPrize.SubmissionLower.R6960Low6960Mass34
import ProximityPrize.SubmissionLower.R6960Low6960Mass35
import ProximityPrize.SubmissionLower.R6960Low6960Mass36
import ProximityPrize.SubmissionLower.R6960Low6960Mass37
import ProximityPrize.SubmissionLower.R6960Low6960Mass38
import ProximityPrize.SubmissionLower.R6960Low6960Mass39
import ProximityPrize.SubmissionLower.R6960Low6960Mass40
import ProximityPrize.SubmissionLower.R6960Low6960Mass41
import ProximityPrize.SubmissionLower.R6960Low6960Mass42

-- merged module R6960Low6960Mass43
section Merged_R6960Low6960Mass43

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group43

private def m0 : MassCell 43 :=
  ⟨⟨1,3,95⟩,mass_cell 43 1 3 95 244 (by decide)
    (by decide +kernel) [4451345034738, 3680112320386, 3005541912594, 2420639567778, 1918524288562, 1492428323778, 1135697168466, 839970182498, 552889215150, 323502277746, 168831409990, 73856217834, 23767904286, 3969269410, 86416732, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 43 :=
  ⟨⟨5,3,97⟩,mass_cell 43 5 3 97 246 (by decide)
    (by decide +kernel) [4451345034738, 3680112320386, 3005541912594, 2420639567778, 1918524288562, 1492428323778, 1135697168466, 841789563874, 560749793008, 324404845268, 167678961448, 72907620652, 23521086752, 4044408388, 103614912, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 43 :=
  ⟨⟨2,6,107⟩,mass_cell 43 2 6 107 223 (by decide)
    (by decide +kernel) [4451345034738, 3680112320386, 3005541912594, 2420639567778, 1918524288562, 1492428323778, 1135697168466, 841789563874, 601413788842, 340467038404, 147979653020, 46987563892, 7578975820, 142484482, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 43 :=
  ⟨⟨5,6,108⟩,mass_cell 43 5 6 108 224 (by decide)
    (by decide +kernel) [4451345034738, 3680112320386, 3005541912594, 2420639567778, 1918524288562, 1492428323778, 1135697168466, 841789563874, 603284720572, 347013039005, 150303863553, 47899459781, 7928045033, 171714463, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 43) := [m0, m1, m2, m3]

end Low6960Allocation.Group43

end Merged_R6960Low6960Mass43

-- merged module R6960Low6960Gates
section Merged_R6960Low6960Gates
set_option Elab.async false
namespace Low6960Allocation
open K1_13 (Shape)
def bandOrders : ∀ k : Band, List (MassCell k)
  | ⟨0,_⟩ => Low6960Allocation.Group0.orders
  | ⟨1,_⟩ => Low6960Allocation.Group1.orders
  | ⟨2,_⟩ => Low6960Allocation.Group2.orders
  | ⟨3,_⟩ => Low6960Allocation.Group3.orders
  | ⟨4,_⟩ => Low6960Allocation.Group4.orders
  | ⟨5,_⟩ => Low6960Allocation.Group5.orders
  | ⟨6,_⟩ => Low6960Allocation.Group6.orders
  | ⟨7,_⟩ => Low6960Allocation.Group7.orders
  | ⟨8,_⟩ => Low6960Allocation.Group8.orders
  | ⟨9,_⟩ => Low6960Allocation.Group9.orders
  | ⟨10,_⟩ => Low6960Allocation.Group10.orders
  | ⟨11,_⟩ => Low6960Allocation.Group11.orders
  | ⟨12,_⟩ => Low6960Allocation.Group12.orders
  | ⟨13,_⟩ => Low6960Allocation.Group13.orders
  | ⟨14,_⟩ => Low6960Allocation.Group14.orders
  | ⟨15,_⟩ => Low6960Allocation.Group15.orders
  | ⟨16,_⟩ => Low6960Allocation.Group16.orders
  | ⟨17,_⟩ => Low6960Allocation.Group17.orders
  | ⟨18,_⟩ => Low6960Allocation.Group18.orders
  | ⟨19,_⟩ => Low6960Allocation.Group19.orders
  | ⟨20,_⟩ => Low6960Allocation.Group20.orders
  | ⟨21,_⟩ => Low6960Allocation.Group21.orders
  | ⟨22,_⟩ => Low6960Allocation.Group22.orders
  | ⟨23,_⟩ => Low6960Allocation.Group23.orders
  | ⟨24,_⟩ => Low6960Allocation.Group24.orders
  | ⟨25,_⟩ => Low6960Allocation.Group25.orders
  | ⟨26,_⟩ => Low6960Allocation.Group26.orders
  | ⟨27,_⟩ => Low6960Allocation.Group27.orders
  | ⟨28,_⟩ => Low6960Allocation.Group28.orders
  | ⟨29,_⟩ => Low6960Allocation.Group29.orders
  | ⟨30,_⟩ => Low6960Allocation.Group30.orders
  | ⟨31,_⟩ => Low6960Allocation.Group31.orders
  | ⟨32,_⟩ => Low6960Allocation.Group32.orders
  | ⟨33,_⟩ => Low6960Allocation.Group33.orders
  | ⟨34,_⟩ => Low6960Allocation.Group34.orders
  | ⟨35,_⟩ => Low6960Allocation.Group35.orders
  | ⟨36,_⟩ => Low6960Allocation.Group36.orders
  | ⟨37,_⟩ => Low6960Allocation.Group37.orders
  | ⟨38,_⟩ => Low6960Allocation.Group38.orders
  | ⟨39,_⟩ => Low6960Allocation.Group39.orders
  | ⟨40,_⟩ => Low6960Allocation.Group40.orders
  | ⟨41,_⟩ => Low6960Allocation.Group41.orders
  | ⟨42,_⟩ => Low6960Allocation.Group42.orders
  | ⟨43,_⟩ => Low6960Allocation.Group43.orders
  | ⟨n+44,h⟩ => absurd h (by omega)
def Gates : Prop :=
  ∃ G : Shape → ℕ, Low6960RetainedCut.GateBank G ∧ GateTable bandOrders G
end Low6960Allocation

end Merged_R6960Low6960Gates
