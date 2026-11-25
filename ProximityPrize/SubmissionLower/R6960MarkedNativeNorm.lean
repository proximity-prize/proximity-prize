import ProximityPrize.SubmissionLower.R6960MarkedScalarPlace
import ProximityPrize.SubmissionLower.R6960MarkedMatrixNorm
import ProximityPrize.SubmissionLower.R6960MarkedPhysicalRows
import ProximityPrize.SubmissionLower.R6960MarkedTranslatedEquation

set_option Elab.async false

-- merged module R6960MarkedFamilyFrame
section Merged_R6960MarkedFamilyFrame

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.MarkedEvaluation
open Polynomial Module Matrix Submodule Algebra
open scoped Polynomial Matrix BigOperators
variable {k E J:Type} [Field k] [Field E] [Fintype J]
local notation "F" => FractionRing (Polynomial k)
variable [Algebra (FractionRing (Polynomial k)) E] [Algebra k E] [IsScalarTower k (FractionRing (Polynomial k)) E]
local notation "ι" => algebraMap (Polynomial k) F

/-- The primitive polynomial frame of the actual functions. Both directions
are identities in their field, so they survive every horizontal embedding. -/
theorem function_frame (v:J→E) (li:LinearIndependent k v) :
    ∃ r:ℕ, r=finrank F (span F (Set.range v)) ∧
      ∃ (w:Fin r→E) (Q:Matrix (Fin r) J (Polynomial k)) (T:Matrix J (Fin r) (Polynomial k)) (pick:Fin r↪J),
        LinearIndependent F w ∧
        (∀j,v j=∑i,ι (Q i j) • w i) ∧ (∀i,w i=∑j,ι (T j i) • v j) ∧
        (Q.submatrix _root_.id pick).det≠0 ∧ Fintype.card J≤r+(Q.submatrix _root_.id pick).det.natDegree := by
  classical
  obtain ⟨I,σ,inj,sp,ind⟩:=exists_linearIndependent' F v
  letI : Finite I:=Finite.of_injective σ inj
  letI : Fintype I:=Fintype.ofFinite I
  let r:=Fintype.card I
  let e:Fin r≃I:=(Fintype.equivFin I).symm
  let sel:Fin r↪J:=e.toEmbedding.trans ⟨σ,inj⟩
  have il:LinearIndependent F (fun i=>v (sel i)):=ind.comp e e.injective
  let U:=span F (Set.range (fun i=>v (sel i)))
  have same : U=span F (Set.range v) := by
    rw [←sp];exact congrArg (span F) (e.surjective.range_comp (v ∘ σ))
  let b : Basis (Fin r) F U:=Basis.span il
  let f (j:J):U:=⟨v j,same ▸ subset_span ⟨j,rfl⟩⟩
  let M:Matrix (Fin r) J F:=fun i j=>b.equivFun (f j) i
  let synth:(Fin r→F)→ₗ[F]E:=U.subtype.comp b.equivFun.symm.toLinearMap
  have evaluation (j:J):synth (M.col j)=v j := by
    change ((b.equivFun.symm (b.equivFun (f j)):U):E)=_
    rw [LinearEquiv.symm_apply_apply]
  have base : M.submatrix _root_.id sel=1 := by
    ext i j
    change b.repr (f (sel j)) i=_
    have ej : f (sel j)=b j := Subtype.ext (Basis.coe_span_apply il j).symm
    rw [ej,b.repr_self,Matrix.one_apply,Finsupp.single_apply]
    simp only [eq_comm]
  have liM : LinearIndependent k M.col :=
    LinearIndependent.of_comp (synth.restrictScalars k) (show LinearIndependent k (synth∘M.col) from
      (show synth∘M.col=v from funext evaluation).symm ▸ li)
  obtain ⟨Q,T,B,pick,_,rep,back,nz,sz⟩ := primitive_minor M ⟨sel,by rw [base,Matrix.det_one];exact one_ne_zero⟩ liM
  have detB:B.det≠0 := by
    have eq:1 = B.det*((Q.map ι).submatrix _root_.id sel).det := by
      have h:=congrArg Matrix.det base.symm
      rw [rep,Matrix.submatrix_mul _ _ _root_.id _root_.id sel Function.bijective_id,Matrix.submatrix_id_id,Matrix.det_mul,Matrix.det_one] at h
      exact h
    exact fun h=>one_ne_zero (eq.trans (by rw [h,zero_mul]))
  let w (j:Fin r):E:=synth (B.col j)
  have sx:Function.Injective synth:=Subtype.val_injective.comp b.equivFun.symm.injective
  have ilB:LinearIndependent F B.col:=Matrix.linearIndependent_cols_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr detB))
  have sin {A D C:Type} [Fintype D] (N:Matrix A D F) (U':Matrix D C F) (j:C) :
      (N*U').col j=∑l:D,U' l j • N.col l := by
    ext i;rw [Finset.sum_apply];simp only [Matrix.col_apply,Matrix.mul_apply,Pi.smul_apply,smul_eq_mul,mul_comm]
  refine ⟨r,?_,w,Q,T,pick,ilB.map' synth (LinearMap.ker_eq_bot_of_injective sx),?_,?_,nz,?_⟩
  · rw [←same,finrank_eq_card_basis b,Fintype.card_fin]
  · intro j
    calc v j=synth (M.col j):=(evaluation j).symm
         _ = _ := by rw [rep,sin,map_sum];simp only [map_smul,Matrix.map_apply,w]
  · intro i
    change synth (B.col i)=_
    rw [back,sin,map_sum];simp only [map_smul,Matrix.map_apply,evaluation]
  · simpa only [Fintype.card_fin] using sz

#print axioms function_frame
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedFamilyFrame

-- merged module R6960MarkedNativeNorm
section Merged_R6960MarkedNativeNorm
set_option synthInstance.maxHeartbeats 200000
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (Scalar ChartField)
open MonicFourChartDescent RetainedRestrictionTorus RetainedSurfaceClass CollisionMarked Polynomial Matrix Algebra Finset Module Submodule
open scoped Polynomial Matrix BigOperators Lower6960.MarkedEvaluation Lower6960.RetainedSurfaceClass
local instance : DecidableEq Scalar := Classical.decEq _
local instance : DecidableEq ChartField := Classical.decEq _
local instance (priority:=2200) : SMul (Polynomial Scalar) ChartField := (inferInstance:Algebra (Polynomial Scalar) ChartField).toSMul
variable {E:Type} [Field E] [Algebra ChartField E]
local notation "j" => algebraMap (Polynomial Scalar) ChartField
local notation "aE" => algebraMap ChartField E
def planeFinite : NormalizedFiber.Plane L→+*ChartField :=
  (baseChart (reference true false)).subtype.comp (oriented true false).toRingHom
local notation "πp" => planeFinite
local instance (priority:=2300) : Algebra Scalar ChartField :=
  RatFunc.instAlgebraOfPolynomial Scalar Scalar
scoped instance scalarFieldAlgebra (E:Type) [Field E] [Algebra ChartField E] : Algebra Scalar E :=
  ((algebraMap ChartField E).comp RatFunc.C).toAlgebra
scoped instance scalarFieldTower (E:Type) [Field E] [Algebra ChartField E] : IsScalarTower Scalar ChartField E :=
  IsScalarTower.of_algebraMap_eq (fun r=>rfl)
scoped instance constantScalarTower (E:Type) [Field E] [Algebra ChartField E] : IsScalarTower L Scalar E :=
  IsScalarTower.of_algebraMap_eq (fun r=>rfl)
theorem native_norm {J:Type} [Fintype J] (v:J→E) (li:LinearIndependent L v)
    (i:ℕ) (T:Finset L) (nz:∀z∈T,z≠0) (o:Tor E) (word:L→Tor E)
    (cols:∀h,Column i T o word (v h)) (b:PowerBasis ChartField E) (simple:(minpoly ChartField b.gen).Separable)
    (a:ChartField) (an:a≠0) (ord:(o:E)=aE a*b.gen)
    (q:(Polynomial (NormalizedFiber.Plane L))) (root:q.eval₂ ((algebraMap ChartField E).comp πp) (o:E)=0)
    (sep:∀z∈T,(q.map (genericFibreBase z)).Separable)
    (baseWord:∀z∈T,∃w:ChartField,(word z:E)=aE w) :
    ∃ (r d:ℕ),r=finrank Scalar (span Scalar (Set.range v)) ∧ Fintype.card J≤r+d ∧ b.dim*d≤T.card*r := by
  classical
  have : FiniteDimensional ChartField E:=b.finite
  obtain ⟨r,rank,w,Q,T₀,pick,wli,exp,back,nq,m⟩:=function_frame v li
  obtain ⟨p,ps,c,ev,horizontal,det⟩:=horizontal_frame_over (k:=L) swapBase b simple w wli
  let Ω:=p.SplittingField
  let δ:=algebraMap ChartField Ω
  letI : IsGalois ChartField Ω := IsGalois.of_separable_splitting_field (p:=p) ps
  let jeg:=algebraMap (Polynomial Scalar) Ω
  have extb (n:Fin r) (a:ChartField) : ev n (aE a)=δ (rowBase (c n) a) := horizontal n a
  have cof (n:Fin r) (z:(Polynomial L)) : ev n (algebraMap Scalar E (algebraMap (Polynomial L) Scalar z))=jeg (z.map inner) := by
    change ev n (aE (RatFunc.C _))=_
    rw [extb,row_seed_polynomial];exact (IsScalarTower.algebraMap_apply (Polynomial Scalar) ChartField Ω _).symm
  let A:Matrix (Fin r) J Ω:=fun n t=>ev n (v t)
  let B:Matrix (Fin r) (Fin r) Ω:=fun n t=>ev n (w t)
  let inc:=jeg.comp (Polynomial.mapRingHom inner)
  have eqA:A=B*Q.map inc := by
    ext n t;change ev n (v t)=_
    rw [exp,map_sum,Matrix.mul_apply]
    apply Finset.sum_congr rfl;intro h _
    rw [Algebra.smul_def,map_mul,cof,mul_comm];rfl
  have eqB:B=A*T₀.map inc := by
    ext n t;change ev n (w t)=_
    rw [back,map_sum,Matrix.mul_apply]
    apply Finset.sum_congr rfl;intro h _
    rw [Algebra.smul_def,map_mul,cof,mul_comm];rfl
  let labels:=T.image inner
  let place (z:Scalar):=markPlace Scalar Ω z
  let qs (n:Fin r):=q.map (rowPlane (c n))
  have localRoot (n:Fin r) : (qs n).eval₂ jeg (ev n (o:E))=0 := by
    have mapcoef:jeg.comp (rowPlane (c n))=(ev n).comp ((algebraMap ChartField E).comp πp) :=
      RingHom.ext (fun a=>(IsScalarTower.algebraMap_apply (Polynomial Scalar) ChartField Ω _).trans
        ((congrArg δ (row_plane (c n) a)).symm.trans (extb n _).symm))
    rw [show qs n=q.map (rowPlane (c n)) from rfl,eval₂_map,mapcoef,←Polynomial.hom_eval₂,root,map_zero]
  have deg (n:Fin r) : (minpoly ChartField (ev n (o:E))).natDegree=b.dim := by
    rw [ord];exact scaled_row_degree b (rowBase (c n)) (ev n) (extb n) a an
  have records (z:Scalar) (hz:z∈labels) :
      ∃ (A':SheetNorm.Aut Scalar Ω→Matrix (Fin r) J (place z).V) (rows:SheetNorm.Aut Scalar Ω→Finset (Fin r)),
      (∀g n h,(A' g n h:Ω)=g (jeg (polePolynomial labels)*A n h)) ∧
      (∀g,∀n∈rows g,∀h,(place z).pi∣A' g n h) ∧
      b.dim*(∑g,(rows g).card)=Fintype.card (SheetNorm.Aut Scalar Ω)*((b.dim-1)*Fintype.card (Fin r)) := by
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
    obtain ⟨wx,wordValue⟩:=baseWord x hx
    apply actual_place_rows T i b.dim v o word cols c ev extb deg qs localRoot x hx
      ((map_ne_zero_iff _ inner.injective).mpr (nz x hx)) (place (inner x))
    · intro n
      change ((q.map (rowPlane (c n))).map _).Separable
      rw [Polynomial.map_map,row_specialization,←Polynomial.map_map]
      exact (sep x hx).map
    · intro g n;rw [wordValue,extb,g.commutes]
  choose A' row fetch off freq using records
  let locals (z:Scalar) := if hz:z∈labels then A' z hz else 0
  let rows (z:Scalar) := if hz:z∈labels then row z hz else fun _=>∅
  have cost:=count_from_original_columns inner labels Q T₀ pick nq A B det eqA eqB
    (fun n h=>mapped_finite (c n) (ev n) (extb n) (cols h).1)
    (fun n h=>mapped_infty (c n) (ev n) (extb n) (cols h).1) b.dim (by
      have :=Module.finrank_pos (R:=ChartField) (M:=E); rwa [b.finrank] at this)
    (fun z=>(place z).V) (fun z=>(place z).lift) (fun z=>(place z).V.subtype)
    (fun _=>Subtype.val_injective) (fun z=>RingHom.ext (place z).value) (fun z=>(place z).pi)
    (fun z _=>⟨(place z).pi_ne,(place z).pi_residue,rfl⟩) locals rows
    (fun z hz g n h=>by rw [show locals z=A' z hz from dif_pos hz];exact fetch z hz g n h)
    (fun z hz=>by simpa only [locals,rows,dif_pos hz] using off z hz)
    (fun z hz=>by simpa only [rows,dif_pos hz] using freq z hz)
  exact ⟨r,_,rank,m,by simpa only [labels,card_image_of_injective _ inner.injective,Fintype.card_fin] using cost⟩
#print axioms native_norm
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedNativeNorm
