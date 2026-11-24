import ProximityPrize.SubmissionLower.R6960MarkedPhysicalRows
import ProximityPrize.SubmissionLower.R6960MarkedTranslatedEquation
import ProximityPrize.SubmissionLower.R6960MarkedFamilyFrame
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

/-- The determinant bound applied to the genuine functions and the marked
polynomial equation. The places, row embeddings, primitive basis, and norm
degree are all constructed. The input word values are scalars on each row. -/
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
