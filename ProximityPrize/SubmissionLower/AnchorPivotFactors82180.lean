import ProximityPrize.SubmissionLower.AnchorPivot82180

set_option Elab.async false
set_option maxHeartbeats 1500000
namespace AnchorPivot82180
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder valueForm)
open MvPolynomial
open AnchorPivot82180 (poly_band poly_order encoded_degree)

def src0 : List Term := [(1,⟨1,0,0,0⟩), (-1,⟨0,1,0,0⟩)]
private def dst0 : List Term := [(-1,⟨0,0,1,0⟩), (1,⟨0,0,0,1⟩), (1,⟨1,0,0,0⟩)]
def data0 : Data := ⟨1,0,1,0,1,30000⟩
theorem spec0 : Sound data0 (poly src0) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src0) = poly dst0 := by
      simp [src0,dst0,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 20000) ([(-1,⟨0,1,0,0⟩)]) (by decide) (by decide)
def src1 : List Term := [(1,⟨1,0,0,0⟩), (-1,⟨0,1,0,0⟩), (1,⟨0,0,1,0⟩)]
private def dst1 : List Term := [(1,⟨0,0,0,1⟩), (1,⟨1,0,0,0⟩)]
def data1 : Data := ⟨1,0,2,0,2,30000⟩
theorem spec1 : Sound data1 (poly src1) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src1) = poly dst1 := by
      simp [src1,dst1,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 20000) ([(-1,⟨0,1,0,0⟩), (1,⟨0,0,1,0⟩)]) (by decide) (by decide)
def src2 : List Term := [(1,⟨1,0,0,0⟩), (-1,⟨0,1,0,0⟩), (1,⟨0,0,1,0⟩), (-1,⟨0,0,0,1⟩)]
private def dst2 : List Term := [(1,⟨1,0,0,0⟩)]
def data2 : Data := ⟨1,0,3,1,3,30000⟩
theorem spec2 : Sound data2 (poly src2) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src2) = poly dst2 := by
      simp [src2,dst2,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 20000) ([(-1,⟨0,1,0,0⟩), (1,⟨0,0,1,0⟩), (-1,⟨0,0,0,1⟩)]) (by decide) (by decide)
def src3 : List Term := [(1,⟨1,1,0,0⟩), (-1,⟨0,2,0,0⟩), (1,⟨1,0,1,0⟩)]
private def dst3 : List Term := [(1,⟨0,1,0,1⟩), (1,⟨1,1,0,0⟩), (-1,⟨0,0,2,0⟩), (1,⟨0,0,1,1⟩), (1,⟨1,0,1,0⟩)]
def data3 : Data := ⟨2,1,2,0,2,50000⟩
theorem spec3 : Sound data3 (poly src3) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src3) = poly dst3 := by
      simp [src3,dst3,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 40001) ([(-1,⟨0,2,0,0⟩), (1,⟨1,0,1,0⟩)]) (by decide) (by decide)
def src4 : List Term := [(1,⟨1,1,0,0⟩), (-1,⟨0,2,0,0⟩), (1,⟨0,1,1,0⟩), (-1,⟨1,0,0,1⟩)]
private def dst4 : List Term := [(1,⟨1,1,0,0⟩), (1,⟨0,0,1,1⟩), (-1,⟨0,0,0,2⟩), (-1,⟨1,0,0,1⟩)]
def data4 : Data := ⟨2,1,3,1,3,50000⟩
theorem spec4 : Sound data4 (poly src4) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src4) = poly dst4 := by
      simp [src4,dst4,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 40000) ([(-1,⟨0,2,0,0⟩), (1,⟨0,1,1,0⟩), (-1,⟨1,0,0,1⟩)]) (by decide) (by decide)
def src5 : List Term := [(1,⟨1,0,1,0⟩), (-1,⟨0,1,1,0⟩), (1,⟨0,0,2,0⟩), (1,⟨1,0,0,1⟩), (-1,⟨0,1,0,1⟩)]
private def dst5 : List Term := [(1,⟨1,0,1,0⟩), (1,⟨0,0,0,2⟩), (1,⟨1,0,0,1⟩)]
def data5 : Data := ⟨2,2,4,1,4,40001⟩
theorem spec5 : Sound data5 (poly src5) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src5) = poly dst5 := by
      simp [src5,dst5,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 30064) ([(-1,⟨0,1,1,0⟩), (1,⟨0,0,2,0⟩), (1,⟨1,0,0,1⟩), (-1,⟨0,1,0,1⟩)]) (by decide) (by decide)
def src6 : List Term := [(1,⟨2,0,1,0⟩), (-2,⟨1,1,1,0⟩), (-1,⟨1,2,0,0⟩), (1,⟨0,3,0,0⟩), (1,⟨2,0,0,1⟩)]
private def dst6 : List Term := [(1,⟨0,0,3,0⟩), (-1,⟨0,0,2,1⟩), (-1,⟨0,0,1,2⟩), (-2,⟨1,0,2,0⟩), (1,⟨2,0,1,0⟩), (-1,⟨1,2,0,0⟩), (-2,⟨0,1,1,1⟩), (2,⟨0,1,0,2⟩), (2,⟨1,1,0,1⟩), (1,⟨0,0,0,3⟩), (2,⟨1,0,0,2⟩), (1,⟨2,0,0,1⟩)]
def data6 : Data := ⟨3,2,3,1,3,70001⟩
theorem spec6 : Sound data6 (poly src6) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src6) = poly dst6 := by
      simp [src6,dst6,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 70000) ([(-2,⟨1,1,1,0⟩), (-1,⟨1,2,0,0⟩), (1,⟨0,3,0,0⟩), (1,⟨2,0,0,1⟩)]) (by decide) (by decide)
def src7 : List Term := [(1,⟨1,3,0,0⟩), (-1,⟨0,4,0,0⟩), (1,⟨1,2,1,0⟩), (1,⟨2,0,2,0⟩), (-1,⟨2,1,0,1⟩)]
private def dst7 : List Term := [(1,⟨1,3,0,0⟩), (3,⟨0,2,1,1⟩), (1,⟨1,2,1,0⟩), (-2,⟨0,1,3,0⟩), (1,⟨0,0,4,0⟩), (1,⟨0,1,2,1⟩), (-2,⟨0,0,3,1⟩), (2,⟨1,1,2,0⟩), (1,⟨0,0,2,2⟩), (-2,⟨1,0,3,0⟩), (2,⟨1,0,2,1⟩), (1,⟨2,0,2,0⟩), (-2,⟨0,2,0,2⟩), (2,⟨0,1,1,2⟩), (-2,⟨1,2,0,1⟩), (-1,⟨0,1,0,3⟩), (2,⟨1,1,1,1⟩), (-2,⟨1,1,0,2⟩), (-1,⟨2,1,0,1⟩)]
def data7 : Data := ⟨4,3,4,1,3,90000⟩
theorem spec7 : Sound data7 (poly src7) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src7) = poly dst7 := by
      simp [src7,dst7,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul] <;> ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 80064) ([(-1,⟨0,4,0,0⟩), (1,⟨1,2,1,0⟩), (1,⟨2,0,2,0⟩), (-1,⟨2,1,0,1⟩)]) (by decide) (by decide)

end AnchorPivot82180
