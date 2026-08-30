import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Y8
namespace ProximityPrize.SubmissionLower.RCN099
open scoped Classical WithZero
open IsDedekindDomain
open RCN187
open RCN344
open RCN264
open RCN075
open RCN093
open RCN097
open RCN002 RCN005 RCN007
open RCN022
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
theorem poleOrder_eq_max_of_valuation_eq_max
   {L:Type*} [Field L]
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x y z:L)
   (h:v x=max (v y) (v z)):
   poleOrder v x=max (poleOrder v y) (poleOrder v z):=by
 unfold poleOrder
 rw [h]
 by_cases hy:v y=0
 · rw [hy]
   simp
 by_cases hz:v z=0
 · rw [hz]
   simp
 rcases le_total (v y) (v z) with hyz | hzy
 · rw [max_eq_right hyz]
   rw [max_eq_right
     (max_le_max_left 0 ((WithZero.log_le_log hy hz).2 hyz))]
 · rw [max_eq_left hzy]
   rw [max_eq_left
     (max_le_max_left 0 ((WithZero.log_le_log hz hy).2 hzy))]
theorem valuation_le_one_of_poleOrder_eq_zero
   {L:Type*} [Field L]
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:L)
   (h:poleOrder v x=0):
   v x ≤ 1:=by
 by_cases hx:v x=0
 · simp [hx]
 by_contra hnot
 have hlt:(1:WithZero (Multiplicative ℤ)) < v x:=
   lt_of_not_ge hnot
 have hlog:0 < (v x).log:=by
   simpa only [WithZero.log_one] using
     ((WithZero.log_lt_log one_ne_zero hx).2 hlt)
 unfold poleOrder at h
 rw [max_eq_right hlog.le] at h
 omega
section RegularComponents
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
variable
   {hseparator:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 2)}
   {hproj:∀ C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1}
theorem nested_u_pole
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1)):
   poleOrder v.val (affineU Omega C.1 D.lam)=
     max (poleOrder v.val (coordinate Omega C.1 0))
       (poleOrder v.val (coordinate Omega C.1 2)):=by
 by_cases hv:v∈componentRelevantPlaces hseparator hproj C
 · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _
     (D.exactU C v hv)
 · have hY:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 0
   have hZ:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 2
   have hYle:v.val (coordinate Omega C.1 0) ≤ 1:=
     valuation_le_one_of_poleOrder_eq_zero v.val _ hY
   have hZle:v.val (coordinate Omega C.1 2) ≤ 1:=
     valuation_le_one_of_poleOrder_eq_zero v.val _ hZ
   letI:v.val.IsTrivialOn Omega:=v.property.2
   have hscalar:
       v.val (D.lam • coordinate Omega C.1 2)=
         v.val (coordinate Omega C.1 2):=by
     rw [Algebra.smul_def,map_mul,
       Valuation.IsTrivialOn.eq_one D.lam D.lam_ne,one_mul]
   have hUle:v.val (affineU Omega C.1 D.lam) ≤ 1:=by
     unfold affineU
     exact (v.val.map_add _ _).trans
       (by rw [hscalar];exact max_le hYle hZle)
   have hU:poleOrder v.val (affineU Omega C.1 D.lam)=0:=
     RCN346.poleOrder_eq_zero_of_le_one
       Omega (CoordinateField Omega C.1) v _ hUle
   rw [hU,hY,hZ]
   simp
theorem nested_v_pole
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1)):
   poleOrder v.val (affineV Omega C.1 D.mu (D.mu*D.lam))=
     max (poleOrder v.val (coordinate Omega C.1 1))
       (max (poleOrder v.val (coordinate Omega C.1 0))
         (poleOrder v.val (coordinate Omega C.1 2))):=by
 rw [←nestedV_eq_affineV D C]
 by_cases hv:v∈componentRelevantPlaces hseparator hproj C
 · calc
     poleOrder v.val
         (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam)=
         max (poleOrder v.val (coordinate Omega C.1 1))
           (poleOrder v.val (affineU Omega C.1 D.lam)):=
       poleOrder_eq_max_of_valuation_eq_max v.val _ _ _
         (D.exactV C v hv)
     _=max (poleOrder v.val (coordinate Omega C.1 1))
         (max (poleOrder v.val (coordinate Omega C.1 0))
           (poleOrder v.val (coordinate Omega C.1 2))):=by
       rw [nested_u_pole D C v]
 · have hS:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 1
   have hY:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 0
   have hZ:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 2
   have hU:poleOrder v.val (affineU Omega C.1 D.lam)=0:=by
     rw [nested_u_pole D C v,hY,hZ]
     simp
   have hSle:v.val (coordinate Omega C.1 1) ≤ 1:=
     valuation_le_one_of_poleOrder_eq_zero v.val _ hS
   have hUle:v.val (affineU Omega C.1 D.lam) ≤ 1:=
     valuation_le_one_of_poleOrder_eq_zero v.val _ hU
   letI:v.val.IsTrivialOn Omega:=v.property.2
   have hscalar:v.val (D.mu • affineU Omega C.1 D.lam)=
       v.val (affineU Omega C.1 D.lam):=by
     rw [Algebra.smul_def,map_mul,
       Valuation.IsTrivialOn.eq_one D.mu D.mu_ne,one_mul]
   have hVle:v.val
       (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam) ≤ 1:=
     (v.val.map_add _ _).trans
       (by rw [hscalar];exact max_le hSle hUle)
   have hV:poleOrder v.val
       (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam)=0:=
     RCN346.poleOrder_eq_zero_of_le_one
       Omega (CoordinateField Omega C.1) v _ hVle
   rw [hV,hS,hY,hZ]
   simp
theorem hAffineV
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H):
   Transcendental Omega (affineV Omega C.1 D.mu (D.mu*D.lam)):=by
 rw [←nestedV_eq_affineV D C]
 exact D.hV C
theorem elementEmbedding_affineV_eq_nested
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H):
   elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 D.mu (D.mu*D.lam)) (hAffineV D C)=
     elementEmbedding Omega (CoordinateField Omega C.1)
       (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam)
       (D.hV C):=by
 apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial Omega))
 ext
 change elementEmbedding Omega (CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam)) (hAffineV D C)
       (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X)=
   elementEmbedding Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam)
       (D.hV C)
       (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X)
 rw [elementEmbedding_variable,elementEmbedding_variable]
 exact (nestedV_eq_affineV D C).symm
theorem finiteAffineV
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H):
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 D.mu (D.mu*D.lam))
       (hAffineV D C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=by
 rw [elementEmbedding_affineV_eq_nested D C]
 exact D.finiteV C
theorem separableAffineV
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H):
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 D.mu (D.mu*D.lam))
       (hAffineV D C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=by
 rw [elementEmbedding_affineV_eq_nested D C]
 exact D.separableV C
end RegularComponents
end
end ProximityPrize.SubmissionLower.RCN099
