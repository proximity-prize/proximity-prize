import ProximityPrize.SubmissionLower.R6970Height2313PowerSheets
import ProximityPrize.SubmissionLower.R6970Height2313CompressedCore

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source1031
set_option autoImplicit true
namespace Research6969.NormalRoute
noncomputable section
open K1 (K I p)
open K1_14 (Equation)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (SeedField)
open _root_.Lower6960.Far6969RescueGeometry (word)
open Research6966
open Research6970.Height2313.Research6969.HighPackets (State)
open Research6970.Height2313.Research6969.BookView (mainBook rescueBook savedMainGrade savedRescueGrade seed)
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 15000
theorem power_at_base {i} (r:Region) (wt:ℕ) {ends:List ℕ} (floor:wt≤r.graph*(131071-2313)-1)
    (cert:PhysicalWindow.Cover (PowerExclusion.Positive (Research6970.Height2313.Research6969.PowerSheets.entry r.gradeLo r.graph (r.content-r.graph)
      r.lowSeed wt)) 2313 2308 ends)
    (pos:0<r.gradeLo) (many:2*r.graph-1<r.gradeLo-(r.content-r.graph)) (fits:r.graph≤r.content):Done i r:=by
  intro s h
  obtain ⟨lo,_,ct,a,seed,_⟩:=h
  have nonempty:(s.pair.main∪s.pair.rescue).Nonempty:=by
    by_contra empty
    have dvd:=NativeOrdinateMass.divides_of_member (D:=1) s.product (fun q h=>False.elim (empty ⟨q,h⟩))
    have zero:=Polynomial.natDegree_le_of_dvd dvd (one_ne_zero:(1:Equation)≠0)
    rw [Polynomial.natDegree_one] at zero
    have high:=s.high;omega
  have geo q (hq:q∈s.pair.main∪s.pair.rescue):K1_14_3.Parent q:=
    (Finset.mem_union.mp hq).elim (fun a=>(s.pair.mainGeo q a).1) (fun a=>(s.pair.rescueGeo q a).1)
  have pass q (hq:q∈s.pair.main∪s.pair.rescue):TerminalBanks.Pass s.crt (word s.model) 179730 SpreadCatalogue.shape q:=
    (Finset.mem_union.mp hq).elim (fun a=>(s.pair.mainGeo q a).2.1) (fun a=>(s.pair.rescueGeo q a).2.1)
  have eq:r.content-r.graph+r.graph=NormalGeometry.content s:=(Nat.sub_add_cancel fits).trans ct.symm
  exact (Research6970.Height2313.Research6969.PowerSheets.prohibit cert pos many s.crt (word s.model) s.lower s.higher _ nonempty geo pass s.product lo
    s.native s.gp a s.physical (floor.trans (a ▸ NormalGeometry.base s)) seed (by rw [eq];exact _root_.Research6970.Height2313.Research6969.NormalGeometry.control s)).elim

theorem power {i} (r:Region) (wt:ℕ) {ends:List ℕ} (floor:wt≤r.graph*(131071-2411)-1)
    (cert:PhysicalWindow.Cover (PowerExclusion.Positive (Research6970.Height2313.Research6969.PowerSheets.entry r.gradeLo r.graph (r.content-r.graph)
      r.lowSeed wt)) 2313 2308 ends)
    (pos:0<r.gradeLo) (many:2*r.graph-1<r.gradeLo-(r.content-r.graph)) (fits:r.graph≤r.content):Done i r:=by
  have stronger : wt ≤ r.graph*(131071-2313)-1 :=
    floor.trans (Nat.sub_le_sub_right (Nat.mul_le_mul_left _ (by decide)) _)
  exact power_at_base r wt stronger cert pos many fits


end
end Research6969.NormalRoute
end Z6969Source1031

end Research6970.Height2313
