import ProximityPrize.SubmissionLower.Zzjdkoa
set_option Elab.async false
namespace qgbTAnb
noncomputable section
open Finset Polynomial
open cu (L FX)
open P5_7_7 (phys)
open qb0hmCe (cLN specialize zD)
open scoped Classical WithZero
def extract {R T:Type*} [Semiring R] [Semiring T] (u:R→T) (f :R[X]) :T[X] :=
 f.sum fun i c=>monomial i (u c)
theorem coeff_extract {R T:Type*} [Semiring R] [Semiring T] {u:R→T}
   (hu:u 0=0) (f :R[X]) (i:ℕ) : (extract u f).coeff i=u (f.coeff i) := by
 by_cases hi:i∈f.support
 · simp [extract,Polynomial.sum,finsetSum_coeff,coeff_monomial,hi]
 · simp [extract,Polynomial.sum,finsetSum_coeff,coeff_monomial,hi,notMem_support_iff.mp hi,hu]
theorem degree_extract {R T:Type*} [Semiring R] [Semiring T] {u:R→T}
  (hu:u 0=0) (f :R[X]) : (extract u f).natDegree≤f.natDegree := by
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro i hi
 rw [coeff_extract hu,coeff_eq_zero_of_natDegree_lt hi,hu]
abbrev slice {E :Type} [Field E] [Algebra L E]
 (ι:E →ₐ[L] LaurentSeries L) (j:ℤ) :=extract fun c=>(ι c).coeff j
def liftSeries {E :Type} [Field E] [Algebra L E]
    (ι:E →ₐ[L] LaurentSeries L) :=extract fun c=>PowerSeries.mk fun j=>(ι c).coeff j
theorem degree_lift {E :Type} [Field E] [Algebra L E] (ι:E →ₐ[L] LaurentSeries L)
  (f :E[X]) : (liftSeries ι f).natDegree≤f.natDegree :=
 degree_extract (by simp [PowerSeries.ext_iff]) f
theorem map_lift {E :Type} [Field E] [Algebra L E] (ι:E →ₐ[L] LaurentSeries L)
  (f :E[X]) (h : ∀ i,Valued.v (ι (f.coeff i))≤(1 :ℤᵐ⁰)) :
  (liftSeries ι f).map (algebraMap _ (LaurentSeries L))=f.map ι.toRingHom:= by
 apply Polynomial.ext
 intro i
 rw [coeff_map,coeff_map,liftSeries,coeff_extract (by simp [PowerSeries.ext_iff])]
 obtain ⟨s,hs⟩:=(LaurentSeries.val_le_one_iff_eq_coe L _).mp (h i)
 have hps :PowerSeries.mk (fun j=>(ι (f.coeff i)).coeff j)=s := by
  ext j
  rw [PowerSeries.coeff_mk,← hs,LaurentSeries.coeff_coe_powerSeries]
 rw [hps]
 exact hs
theorem fWX {E :Type} [Field E] [Algebra L E] (ι:E →ₐ[L] LaurentSeries L)
  (f :E[X]) : (liftSeries ι f).map PowerSeries.constantCoeff=slice ι 0 f := by
 apply Polynomial.ext
 intro i
 rw [coeff_map,liftSeries,coeff_extract (by simp [PowerSeries.ext_iff]),
  coeff_extract (by simp)]
 simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
private theorem expansion_linear {E :Type} [Field E] [Algebra L E]
   (ι:E →ₐ[L] LaurentSeries L) (j:ℤ) {f :E[X][X]} (hd:f.natDegree≤1) :
   cLN ι j f=C (slice ι j (f.coeff 1))*Polynomial.X+C (slice ι j (f.coeff 0)) := by
 change extract (slice ι j) f= _
 apply Polynomial.ext
 intro i
 rw [coeff_extract (by simp [extract]),coeff_add,coeff_C_mul_X,coeff_C]
 rcases i with _ | (_ | i)
 · simp
 · simp
 · simp [coeff_eq_zero_of_natDegree_lt (show f.natDegree< i+1+1 by omega),extract]
theorem linear_root {E :Type} [Field E] [Algebra L E] (ι:E →ₐ[L] LaurentSeries L)
  {f :E[X][X]} {P Q:L[X]} (hd:f.natDegree≤1) (hQ:Q≠0)
  (hr :specialize (cLN ι 0 f) P Q=0) :
  slice ι 0 (f.coeff 1)*P+slice ι 0 (f.coeff 0)*Q=0:= by
 have hQ' : phys Q≠0:=(map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr hQ
 apply (show Function.Injective phys from IsFractionRing.injective L[X] FX)
 simp only [expansion_linear ι 0 hd,specialize,eval₂_add,eval₂_mul,eval₂_C,eval₂_X] at hr
 field_simp [hQ'] at hr
 simpa only [map_add,map_mul,map_zero,mul_zero,zero_mul,mul_comm (phys Q)] using hr
theorem linear_tangent {E :Type} [Field E] [Algebra L E] (ι:E →ₐ[L] LaurentSeries L)
  {f :E[X][X]} {P Q G:L[X]} (hd:f.natDegree≤1) (hQ:Q≠0) (hG:G≠0)
  (ha :slice ι 0 (f.coeff 1)=G*Q) :
  zD ι f P Q=phys (-(slice ι 1 (f.coeff 1)*P+slice ι 1 (f.coeff 0)*Q)) /
    phys G:= by
 have hinj:Function.Injective phys :=IsFractionRing.injective L[X] FX
 have hq:phys Q≠0:=(map_ne_zero_iff _ hinj).mpr hQ
 have hg:phys G≠0:=(map_ne_zero_iff _ hinj).mpr hG
 have hder : (cLN ι 0 f).derivative=C (G*Q) := by
  rw [expansion_linear ι 0 hd,derivative_add,derivative_C_mul_X,derivative_C,add_zero,ha]
 simp only [zD,hder,expansion_linear ι 1 hd,specialize,eval₂_add,eval₂_mul,
  eval₂_C,eval₂_X,map_mul,map_add,map_neg]
 field_simp [hq,hg]
theorem fraction_degrees {N D M G:L[X]} (hD:D ≠0) (hG:G≠0)
   (hc:IsCoprime N D) (h:phys N/phys D =phys M/phys G) :
   D.natDegree≤G.natDegree∧N.natDegree≤M.natDegree := by
 have hinj:Function.Injective phys :=IsFractionRing.injective L[X] FX
 have hD' : phys D ≠0:=(map_ne_zero_iff _ hinj).mpr hD
 have hG' : phys G≠0:=(map_ne_zero_iff _ hinj).mpr hG
 have he :N*G=M*D:=hinj (by simpa only [map_mul] using (div_eq_div_iff hD' hG').mp h)
 have h₁:D ∣G:=hc.symm.dvd_of_dvd_mul_left (by rw [he]; exact dvd_mul_left _ _)
 refine ⟨natDegree_le_of_dvd h₁ hG,?_⟩
 by_cases hm:M=0
 · simp [hm,hG] at he
   simp [hm,he]
 · exact natDegree_le_of_dvd (hc.dvd_of_dvd_mul_right (by rw [← he]; exact dvd_mul_right _ _)) hm
end
end qgbTAnb
