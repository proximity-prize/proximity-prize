import ProximityPrize.SubmissionLower.AnchorPivotRank82180

set_option Elab.async false
set_option maxHeartbeats 1500000
namespace AnchorPivot82190
open AnchorPivot82180
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder valueForm)
open MvPolynomial
open AnchorPivot82180 (poly_band poly_order encoded_degree)

def src8 : List Term := [(1,⟨2,3,0,0⟩), (1,⟨0,5,0,0⟩), (-2,⟨1,4,0,0⟩), (-4,⟨2,1,1,1⟩), (-1,⟨0,4,1,0⟩), (1,⟨1,2,2,0⟩), (-2,⟨2,2,0,1⟩), (2,⟨1,3,0,1⟩), (1,⟨2,2,1,0⟩), (2,⟨3,0,1,1⟩), (1,⟨3,0,0,2⟩), (1,⟨3,0,2,0⟩), (1,⟨2,0,3,0⟩), (-1,⟨2,1,2,0⟩)]
private def dst8 : List Term := [(1,⟨2,3,0,0⟩), (-4,⟨0,1,1,3⟩), (-2,⟨1,1,1,2⟩), (1,⟨0,2,0,3⟩), (-1,⟨1,2,0,2⟩), (-2,⟨2,2,0,1⟩), (1,⟨2,2,1,0⟩), (1,⟨0,1,2,2⟩), (4,⟨1,2,1,1⟩), (-1,⟨0,0,4,1⟩), (3,⟨0,0,3,2⟩), (2,⟨1,0,3,1⟩), (-1,⟨0,0,1,4⟩), (-6,⟨1,0,2,2⟩), (-3,⟨2,0,2,1⟩), (2,⟨3,0,1,1⟩), (3,⟨0,1,0,4⟩), (6,⟨1,1,0,3⟩), (1,⟨0,0,0,5⟩), (3,⟨2,1,0,2⟩), (3,⟨1,0,0,4⟩), (3,⟨2,0,0,3⟩), (1,⟨3,0,0,2⟩), (-2,⟨1,1,3,0⟩), (-2,⟨0,0,2,3⟩), (2,⟨2,1,2,0⟩), (-2,⟨2,0,3,0⟩), (1,⟨3,0,2,0⟩), (2,⟨2,1,1,1⟩), (1,⟨1,0,4,0⟩), (3,⟨2,0,1,2⟩)]
def data8 : Data := ⟨5,3,6,2,6,120000⟩
theorem spec8 : Sound data8 (poly src8) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src8) = poly dst8 := by
      simp [src8,dst8,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul]
      ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 110002) ([(1,⟨0,5,0,0⟩), (-2,⟨1,4,0,0⟩), (-4,⟨2,1,1,1⟩), (-1,⟨0,4,1,0⟩), (1,⟨1,2,2,0⟩), (-2,⟨2,2,0,1⟩), (2,⟨1,3,0,1⟩), (1,⟨2,2,1,0⟩), (2,⟨3,0,1,1⟩), (1,⟨3,0,0,2⟩), (1,⟨3,0,2,0⟩), (1,⟨2,0,3,0⟩), (-1,⟨2,1,2,0⟩)]) (by decide) (by decide)

def allData (i : Fin 9) : Data :=
  match i.val with
  | 0 => data0 | 1 => data1 | 2 => data2 | 3 => data3 | 4 => data4
  | 5 => data5 | 6 => data6 | 7 => data7 | _ => data8
noncomputable def allPoly : Fin 9 → Form := ![poly src0, poly src1, poly src2, poly src3, poly src4, poly src5, poly src6, poly src7, poly src8]
theorem all_ok (i : Fin 9) : Sound (allData i) (allPoly i) := by
  fin_cases i
  · exact spec0
  · exact spec1
  · exact spec2
  · exact spec3
  · exact spec4
  · exact spec5
  · exact spec6
  · exact spec7
  · exact spec8

#print axioms all_ok
end AnchorPivot82190
