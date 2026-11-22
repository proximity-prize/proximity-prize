import ProximityPrize.SubmissionLower.AnchorPivotFactors82180

set_option Elab.async false
set_option maxHeartbeats 1500000
namespace AnchorPivot82190
open AnchorPivot82180
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder valueForm)
open MvPolynomial
open private poly_band poly_order encoded_degree from ProximityPrize.SubmissionLower.AnchorPivot82180

def src8 : List Term := [(1,⟨2,3,0,0⟩), (1,⟨0,5,0,0⟩), (-2,⟨1,4,0,0⟩), (-4,⟨2,1,1,1⟩), (-1,⟨0,4,1,0⟩), (1,⟨1,2,2,0⟩), (-2,⟨2,2,0,1⟩), (2,⟨1,3,0,1⟩), (1,⟨2,2,1,0⟩), (2,⟨3,0,1,1⟩), (1,⟨3,0,0,2⟩), (1,⟨3,0,2,0⟩), (1,⟨2,0,3,0⟩), (-1,⟨2,1,2,0⟩)]
def dst8 : List Term := [(1,⟨2,3,0,0⟩), (-4,⟨0,1,1,3⟩), (-2,⟨1,1,1,2⟩), (1,⟨0,2,0,3⟩), (-1,⟨1,2,0,2⟩), (-2,⟨2,2,0,1⟩), (1,⟨2,2,1,0⟩), (1,⟨0,1,2,2⟩), (4,⟨1,2,1,1⟩), (-1,⟨0,0,4,1⟩), (3,⟨0,0,3,2⟩), (2,⟨1,0,3,1⟩), (-1,⟨0,0,1,4⟩), (-6,⟨1,0,2,2⟩), (-3,⟨2,0,2,1⟩), (2,⟨3,0,1,1⟩), (3,⟨0,1,0,4⟩), (6,⟨1,1,0,3⟩), (1,⟨0,0,0,5⟩), (3,⟨2,1,0,2⟩), (3,⟨1,0,0,4⟩), (3,⟨2,0,0,3⟩), (1,⟨3,0,0,2⟩), (-2,⟨1,1,3,0⟩), (-2,⟨0,0,2,3⟩), (2,⟨2,1,2,0⟩), (-2,⟨2,0,3,0⟩), (1,⟨3,0,2,0⟩), (2,⟨2,1,1,1⟩), (1,⟨1,0,4,0⟩), (3,⟨2,0,1,2⟩)]
def data8 : Data := ⟨5,3,6,2,6,120000⟩
theorem spec8 : Sound data8 (poly src8) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src8) = poly dst8 := by
      simp [src8,dst8,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul]
      ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 110002) ([(1,⟨0,5,0,0⟩), (-2,⟨1,4,0,0⟩), (-4,⟨2,1,1,1⟩), (-1,⟨0,4,1,0⟩), (1,⟨1,2,2,0⟩), (-2,⟨2,2,0,1⟩), (2,⟨1,3,0,1⟩), (1,⟨2,2,1,0⟩), (2,⟨3,0,1,1⟩), (1,⟨3,0,0,2⟩), (1,⟨3,0,2,0⟩), (1,⟨2,0,3,0⟩), (-1,⟨2,1,2,0⟩)]) (by decide) (by decide)

def allData : Fin 9 → Data := ![data0, data1, data2, data3, data4, data5, data6, data7, data8]
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

end AnchorPivot82190
