import Mathlib.RingTheory.PowerSeries.Derivative
import ProximityPrize.SubmissionLower.ZG9rwXd
import ProximityPrize.SubmissionLower.ZyCQ7Ke
import ProximityPrize.SubmissionLower.ZlPdtnc
import ProximityPrize.SubmissionLower.ZBkbQJc
set_option Elab.async false
open _root_ renaming CommRing → za6, Field → zrb, MvPolynomial.C → znf, MvPolynomial.eval₂Hom → zOD, MvPolynomial.map → zDK, MvPolynomial.ringHom_ext → zXT, Polynomial.X → z7y, Polynomial.map_injective → zTo, RingHom.comp_apply → zQb, RingHom.id → zz4
section
set_option autoImplicit true
section
namespace q2TwyLa
noncomputable section
open Polynomial
open cu (L)
open q1kuFjb (Ua)
open scoped WithZero
abbrev i5 :=PowerSeries L
abbrev aQ:=LaurentSeries L
abbrev PhysicalField:=LaurentSeries aQ
abbrev integral {E :Type} [zrb E] [Algebra L E] (a :E →ₐ[L] aQ)
 (F:E[X][X]) := ∀ i j,(Valued.v :Valuation aQ ℤᵐ⁰) (a ((F.coeff i).coeff j))≤1
def lift {E :Type} [zrb E] [Algebra L E] (a :E →ₐ[L] aQ)
    (F:E[X][X]) (h:integral a F) :i5[X][X] :=
  (Ua a F h).map (mapRingHom (LaurentSeries.powerSeriesEquivSubring L).symm.toRingHom)
def diffPoly (f :i5[X]) :i5[X] :=
 f.sum fun j c=>monomial j (PowerSeries.derivative c)
def diff (f :i5[X][X]) :i5[X][X] :=
 f.sum fun i g=>monomial i (diffPoly g)
def ek:i5[X] →+* PhysicalField :=
 (algebraMap aQ[X] PhysicalField).comp (mapRingHom (algebraMap i5 aQ))
def centre {R:Type} [za6 R] (f :R[X][X]) :R[X] :=
 f.map constantCoeff
def polar {R:Type} [za6 R] (f :R[X][X]) :R[X] :=
 f.resultant f.derivative f.natDegree (f.natDegree-1)
def coeffEmbed {R:Type} [za6 R] :R →+* R[X][X] :=
 (C:R[X] →+* R[X][X]).comp C
def an1 {R:Type} [za6 R] (f g:R[X]) :R[X][X][X] :=
  (C (C (z7y:R[X])) - C (z7y:R[X][X])*z7y) *
    f.derivative.map coeffEmbed+g.map coeffEmbed
def qW {R:Type} [za6 R] (f g:R[X]) (d:ℕ) :R[X][X] :=
 (f.map coeffEmbed).resultant (an1 f g) d d
structure RootData (f :i5[X][X]) where
 S:Type
 [field :zrb S]
 incl:PhysicalField →+* S
 place :ValuationSubring S
 restricts : ∀ z :PhysicalField,incl z∈place ↔
   (Valued.v :Valuation PhysicalField ℤᵐ⁰) z≤1
 splits : (f.map (incl.comp ek)).Splits
 tame : ∀ y∈(f.map (incl.comp ek)).roots,
   place.valuation (-((diff f).eval₂ (incl.comp ek) y /
     f.derivative.eval₂ (incl.comp ek) y))≤place.valuation y
structure ReducedPencil (f :i5[X][X]) where
 T:i5[X][X][X]
 factor :qW f (diff f) f.natDegree =
   C (C ((z7y:i5[X])^(polar f).natTrailingDegree))*T
 bound: (T.coeff 0).natDegree≤f.natDegree
 top: ((T.coeff 0).coeff f.natDegree).coeff 0 =
   f.leadingCoeff.coeff 0*(polar f).trailingCoeff
 edge : ((T.coeff (f.natDegree-(centre f).natTrailingDegree)).map constantCoeff) =
   monomial (centre f).natTrailingDegree ((polar f).trailingCoeff*(centre f).trailingCoeff)
end
end q2TwyLa
end
section
namespace q2TwyLa
noncomputable section
open Polynomial
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
theorem diff_coeff (f :i5[X][X]) (i j:ℕ) :
  ((diff f).coeff i).coeff j=PowerSeries.derivative ((f.coeff i).coeff j) := by
 unfold diff
 rw [sum_coeff _ (by simp [diffPoly])]
 exact sum_coeff _ (map_zero _) _ _
theorem diff_degree (f :i5[X][X]) : (diff f).natDegree≤f.natDegree := by
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro i hi
 apply Polynomial.ext
 intro j
 simp [diff_coeff,coeff_eq_zero_of_natDegree_lt hi]
theorem cutter_degree {R:Type} [za6 R] (f g:R[X]) {d:ℕ}
  (hn:0<f.natDegree) (hf :f.natDegree≤d) (hg:g.natDegree≤d) :
  (an1 f g).natDegree≤d:= by
 have h₁:=natDegree_derivative_lt hn.ne'
 have h₂: (C (C (z7y:R[X])) - C (z7y:R[X][X]) *
    (z7y:R[X][X][X])).natDegree≤1 :=
  (natDegree_sub_le _ _).trans (max_le (by simp)
    ((natDegree_C_mul_le _ _).trans natDegree_X_le))
 exact (natDegree_add_le _ _).trans (max_le
  (natDegree_mul_le.trans ((Nat.add_le_add h₂ natDegree_map_le).trans (by omega)))
  (natDegree_map_le.trans hg))
theorem pencil_map {R S:Type} [za6 R] [za6 S] (c:R →+* S)
  (f g:R[X]) (d:ℕ) :
  (qW f g d).map (mapRingHom c)=qW (f.map c) (g.map c) d:= by
 let M:=mapRingHom (mapRingHom c)
 have hM:M.comp coeffEmbed=coeffEmbed.comp c:= by
  ext r
  simp [M,coeffEmbed]
 have hF (q:R[X]) : (q.map coeffEmbed).map M=(q.map c).map coeffEmbed:= by
  rw [map_map,map_map,hM]
 change M (qW f g d)= _
 unfold qW
 rw [← resultant_map_map _ _ _ _ M,hF]
 congr 1
 simp only [an1,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_sub,map_C,
  map_X,hF,derivative_map,M,coe_mapRingHom]
def evaluatePencil {R E :Type} [za6 R] [za6 E] (c:R →+* E) (u l:E) :
    R[X][X] →+* E :=eval₂RingHom (eval₂RingHom c u) l
theorem pencil_zero {R E :Type} [za6 R] [zrb E] (c:R →+* E) (f g:R[X])
   (y b l:E) {d:ℕ} (hn:0<f.natDegree) (hf :f.natDegree≤d)
   (hg:g.natDegree≤d) (hy :f.eval₂ c y=0)
   (hb:b*f.derivative.eval₂ c y+g.eval₂ c y=0) :
   evaluatePencil c (b+l*y) l (qW f g d)=0:= by
 let e :=evaluatePencil c (b+l*y) l
 have he :e.comp coeffEmbed=c:= by ext r; simp [e,evaluatePencil,coeffEmbed]
 have hu:e (C (z7y:R[X]))=b+l*y := by simp [e,evaluatePencil]
 have hx :e (z7y:R[X][X])=l:=eval₂_X _ _
 have hm (s :R[X]) : (s.map coeffEmbed).eval₂ e y=s.eval₂ c y := by rw [eval₂_map,he]
 have hF: (f.map coeffEmbed).eval₂ e y=0:=(hm _).trans hy
 have hG: (an1 f g).eval₂ e y=0:= by
   simpa only [an1,eval₂_add,eval₂_mul,eval₂_sub,eval₂_C,hu,hx,eval₂_X,hm,
     add_sub_cancel_right] using hb
 obtain ⟨a,k,_,_,heq⟩:=exists_mul_add_mul_eq_C_resultant (f.map coeffEmbed)
   (an1 f g) (natDegree_map_le.trans hf) (cutter_degree f g hn hf hg)
   (Or.inl (hn.trans_le hf).ne')
 have hz :=congrArg (eval₂RingHom e y) heq
 simpa only [map_add,map_mul,coe_eval₂RingHom,eval₂_C,hF,hG,zero_mul,zero_add,qW,e]
   using hz.symm
end
end q2TwyLa
end
end
section
namespace P5_7_3_5_2_1
noncomputable section
open Polynomial

open qkgz7gb (PlaneCurve)
open qb0hmCe (CurveModel)
open q1kuFjb
open cu (L FX)
open Y3 (Dg embed)
open scoped Classical WithZero
open private alV b2f d3R from ProximityPrize.SubmissionLower.G
theorem restrict_ne {q:PlaneCurve} (hq:Irreducible q) (Cq:CurveModel q)
    {Q:Dg} (hQ: (embed Q).IsPrimitive) :restrict Cq Q≠0:= by
  let a :=zOD (algebraMap L Cq.E) Cq.seed
  let r :=zOD (mapRingHom (algebraMap L Cq.E)) (C ∘ Cq.seed)
  have he :r.comp alV.toRingHom=mapRingHom a := by
    apply Polynomial.ringHom_ext'
    · apply zXT
      · intro c
        simp only [zQb,coe_mapRingHom,map_C]
        change r (alV (C (znf c)))=C (a (znf c))
        rw [b2f]
        simp [r,a]
      · intro i
        simp only [zQb,coe_mapRingHom,map_C]
        change r (alV (C (MvPolynomial.X i)))=C (a (MvPolynomial.X i))
        rw [b2f]
        simp [r,a]
    · simp only [zQb,coe_mapRingHom,map_X]
      change r (alV z7y)=(z7y:Cq.E[X])
      rw [d3R]
      simp [r]
  intro hz
  let b:=zDK (algebraMap L FX) q
  have hb : ¬ IsUnit b:= by
    intro hu
    have hd:=(MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    change (zDK (algebraMap L FX) q).totalDegree=0 at hd
    rw [MvPolynomial.totalDegree,MvPolynomial.support_map_of_injective _ (algebraMap L FX).injective] at hd
    change q.totalDegree=0 at hd
    have hc:=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
    have hn:q.coeff 0≠0:= fun h=>hq.ne_zero (by rw [hc,h,map_zero])
    exact hq.not_isUnit (hc.symm ▸ hn.isUnit.map znf)
  apply hb (hQ b ?_)
  rw [C_dvd_iff_dvd_coeff]
  intro i
  have h:r (Q.coeff i)=0:= by
    simpa only [restrict,restrictOver,coe_mapRingHom,coeff_map,coeff_zero] using
      congrArg (fun f :Cq.E[X][X]=>f.coeff i) hz
  have hx :alV.symm (Q.coeff i)∈RingHom.ker (mapRingHom a) := by
    rw [RingHom.mem_ker,← he]
    change r (alV (alV.symm (Q.coeff i)))=0
    rwa [RingEquiv.apply_symm_apply]
  rw [Polynomial.ker_mapRingHom,Cq.equation,Ideal.map_span,Set.image_singleton,
    Ideal.mem_span_singleton] at hx
  have hm:zDK (Polynomial.C:L →+* L[X]) q∣Q.coeff i:= by
    have hm:=map_dvd alV.toRingHom hx
    change alV (C q)∣alV (alV.symm (Q.coeff i)) at hm
    rwa [b2f,RingEquiv.apply_symm_apply] at hm
  rw [embed,coe_mapRingHom,coeff_map]
  have hcomp: (algebraMap L[X] FX).comp (C:L →+* L[X])=algebraMap L FX :=
    RingHom.ext fun c=>(IsScalarTower.algebraMap_apply L L[X] FX c).symm
  simpa only [MvPolynomial.map_map,hcomp] using map_dvd (zDK (algebraMap L[X] FX)) hm
end
end P5_7_3_5_2_1
end
section
namespace P5_7_3_5_2_1
noncomputable section
open Polynomial Finset
open P5 (K)
open qkgz7gb (PlaneCurve rV)
open P5_7_3_5_2 (atPolynomial)
open qb0hmCe (CurveModel cLN specialize)
open q1kuFjb
open P5_7_7 (phys)
open cu (L FX yq qD jz j9)
open Y3 (Dg embed)
open scoped Classical WithZero
open private specialize_phys_ne from ProximityPrize.SubmissionLower.ZyCQ7Ke
private theorem root_restrict (Q:Dg) (z :K→K) (S:K→K[X]) (γ:K)
    (h:yq (embed Q) (z γ) (S γ)=0) :
    atPolynomial (restrictOver (zz4 L) (rV z γ) Q) (S γ)=0:= by
  unfold yq embed at h
  unfold atPolynomial restrictOver
  rw [eval₂_eq_eval_map] at h ⊢
  simp only [coe_mapRingHom,Polynomial.map_map] at h ⊢
  have hm:phys.comp (zOD (mapRingHom (zz4 L)) (C ∘ rV z γ)) =
      (qD (z γ)).comp (zDK phys) := by
    apply zXT
    · intro r
      simp [qD]
    · intro i
      simp only [zQb,MvPolynomial.eval₂Hom_X',Function.comp_apply,
        MvPolynomial.map_X,qD,MvPolynomial.eval_X]
      fin_cases i <;> simp [rV,jz,phys]
  rw [hm]
  exact h
theorem integral_at {q:PlaneCurve} {Cq:CurveModel q} {s :Fin 2→L}
    (A:AtSite Cq s) (Q:Dg) :coeffIntegral A.place.value (restrict Cq Q) := by
  obtain ⟨g,hg,_⟩:=integral_restrict A Q
  intro i j
  rw [A.value,LaurentSeries.val_le_one_iff_eq_coe]
  have he :=congrArg (fun f : (LaurentSeries L)[X][X]=>(f.coeff i).coeff j) hg
  simp only [mapTwice,coe_mapRingHom,coeff_map,Subring.subtype_apply,AlgHom.toRingHom_eq_coe] at he
  change (((g.coeff i).coeff j:IntSeries) :LaurentSeries L) =
    A.map (((restrict Cq Q).coeff i).coeff j) at he
  rw [← he]
  exact ((g.coeff i).coeff j).2.elim (fun z hz=>⟨z,hz.2⟩)
theorem factor_root {q:PlaneCurve} {Cq:CurveModel q}
    {z :K→K} {S:K→K[X]} {γ:K} (A:AtSite Cq (rV z γ))
    {Q:Dg} {D W:ℕ} (B:Factors Cq Q Q.natDegree 0 D W)
    (hr :yq (embed Q) (z γ) (S γ)=0)
    (hs : ¬ A.place.value (headScalar (restrict Cq Q))<1)
    (hp:coeffIntegral A.place.value (C B.amm))
    (hf : ∀ j,coeffIntegral A.place.value (B.f j)) :
    ∃ j,atPolynomial (cLN A.map 0 (B.f j)) (S γ)=0:= by
  obtain ⟨g,hg,hg'⟩:=integral_restrict A Q
  let r :=restrict Cq Q
  let c:=headScalar r
  have hc: (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (A.map c)≤1 := by
    rw [← A.value]
    exact integral_at A Q r.natDegree (r.coeff r.natDegree).natDegree
  have hs' : (A.map c).coeff 0≠0:= by
    intro h
    obtain ⟨v,hv⟩:=(LaurentSeries.val_le_one_iff_eq_coe L (A.map c)).mp hc
    have hlt:=(small_valuation v).mpr ((power_residue _ v hv.symm).symm.trans h)
    exact hs (by rw [A.value,← hv]; exact hlt.trans_lt (WithZero.exp_lt_one_iff.mpr (by decide)))
  let d:=integralSeries (A.map c) hc
  let h₀ i j:=A.value _ ▸ hp i j
  let h₁ (k :Fin B.n) i j:=A.value _ ▸ hf k i j
  let f₀:=Ua A.map (C B.amm) h₀
  let f₁ (k :Fin B.n) :=Ua A.map (B.f k) (h₁ k)
  have hm₀:mapTwice IntSeries.subtype f₀=mapTwice A.map.toRingHom (C B.amm) :=
    map_liftAt _ _ _
  have hm₁ (k :Fin B.n) :mapTwice IntSeries.subtype (f₁ k)=mapTwice A.map.toRingHom (B.f k) :=
    map_liftAt _ _ _
  have hm:mapTwice IntSeries.subtype (C (C d))=mapTwice A.map.toRingHom (C (C c)) := by
    simp only [mapTwice,coe_mapRingHom,map_C]
    rfl
  have hprod:r=C (C c)*C B.amm * ∏ k,B.f k :=
    B.product.trans (congrArg (fun f=>f * ∏ k,B.f k) (map_mul C _ _))
  have he :g=C (C d)*f₀ * ∏ k,f₁ k := by
    apply zTo (mapRingHom IntSeries.subtype)
      (zTo IntSeries.subtype IntSeries.subtype_injective)
    change mapTwice IntSeries.subtype g=mapTwice IntSeries.subtype _
    rw [hg]
    change mapTwice A.map.toRingHom r= _
    rw [hprod]
    simp only [map_mul,map_prod,hm,hm₀,hm₁]
  have he' := congrArg (mapTwice residue) he
  rw [hg',map_mul,map_mul,map_prod] at he'
  have h0:mapTwice residue f₀=cLN A.map 0 (C B.amm) :=liftAt_reduce _ _ _
  have h1 (k :Fin B.n) :mapTwice residue (f₁ k)=cLN A.map 0 (B.f k) :=liftAt_reduce _ _ _
  simp only [h0,h1] at he'
  let ev :=eval₂RingHom phys (phys (j9 (S γ)))
  have hz :ev (restrictOver (zz4 L) (rV z γ) Q)=0 :=
    root_restrict Q z S γ hr
  rw [he',map_mul,map_mul,map_prod,mul_eq_zero] at hz
  have hn:ev (mapTwice residue (C (C d)))*ev (cLN A.map 0 (C B.amm))≠0:= by
    refine mul_ne_zero ?_ ?_
    · simp only [mapTwice,coe_mapRingHom,map_C,ev,coe_eval₂RingHom,eval₂_C]
      rw [fWQ]
      change phys (C ((A.map c).coeff 0))≠0
      exact (map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr (C_ne_zero.mpr hs')
    · simpa only [specialize,ev,coe_eval₂RingHom,map_one,div_one] using
        specialize_phys_ne A.map B.monic (j9 (S γ)) 1
  obtain ⟨j,_,hj⟩:=Finset.prod_eq_zero_iff.mp (hz.resolve_left hn)
  exact ⟨j,hj⟩
end
end P5_7_3_5_2_1
end
section
namespace qziIa4d
noncomputable section
open Polynomial
open P5 (K p)
open cu (L FX)
open P5_7_7 (phys)
open qkgz7gb (PlaneCurve rV)
open P5_7_3_5_2 (Sheet Variation targetHit)
open qb0hmCe (CurveModel SiteTarget)
open qFD8jve (aFA sheetPole seedPole polarResultant)
open E7 (CurvePlace)
open scoped Classical WithZero
def siteGuard {E :Type} [zrb E] (G:E[X][X]) :E :=
  (polarResultant G).trailingCoeff*G.leadingCoeff.coeff 0
def atZeroRegular (y :FX) :Prop :=
  ∃ A B:L[X],B.coeff 0≠0∧y=phys A/phys B
def slope {q:PlaneCurve} {C:CurveModel q} {z :K→K} {S:K→K[X]}
    (F:Sheet C z S) (R:SiteTarget) (γ:K) :L :=
  -(R.det*F.direction γ R.coord)/(R.c+R.d*rV z γ R.coord)^2
def scaledChart {E :Type} [zrb E] (f :E[X][X]) (x c a b:E) :E[X][X] :=
  let τ:E[X] :=z7y
  let W:E[X][X] :=z7y
  f.sum fun i g =>
    C (taylor x g)*(C (C b*τ)+C (C a+C (b*c)*τ)*W)^i *
      (C (C b)*W)^(f.natDegree-i)
structure Chart {q:PlaneCurve} {C:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet C z S} (V:Variation F) (R:SiteTarget) where
  c:L
  n:ℕ
  G:C.E[X][X]
  equation : let a := algebraMap L C.E R.a + algebraMap L C.E R.b * C.seed R.coord
             let b:=algebraMap L C.E R.c+algebraMap L C.E R.d*C.seed R.coord
             scaledChart F.f (algebraMap L C.E R.center) (algebraMap L C.E c) a b =
               Polynomial.C ((z7y:C.E[X])^n)*G
  avoid : ∀ γ∈V.marks,targetHit R z S γ→(cu.j9 (S γ)).derivative.eval R.center≠c
  degree :G.natDegree=F.d
  leading:G.leadingCoeff.coeff 0≠0
  separant:polarResultant G≠0
  bound : ∀ v :CurvePlace L C.E,
    aFA v.value G (sheetPole v.value F.f+F.d*seedPole C R v.value)
  integral : ∀ γ∈V.marks,targetHit R z S γ→aFA (F.place γ).value G 0
abbrev SeedSeries :=LaurentSeries L
def seedDerivative (G:SeedSeries[X][X]) :SeedSeries[X][X] :=
  G.sum fun i g=>monomial i (g.sum fun j a=>monomial j (LaurentSeries.derivative L a))
def TameDerivative :Prop :=
  ∀ {M Γ:Type} [zrb M] [LinearOrderedCommGroupWithZero Γ]
    (v :Valuation M Γ) (ι:SeedSeries[X] →+* M),Function.Injective ι →
    (∀ a :SeedSeries,a≠0→v (ι (C a))=1)→v (ι z7y)<1 →
    ∀ (G:SeedSeries[X][X]) (r :M),0<G.natDegree→G.natDegree<p →
      G.leadingCoeff.coeff 0≠0→G.eval₂ ι r=0→G.derivative.eval₂ ι r≠0 →
      v (-(seedDerivative G).eval₂ ι r/G.derivative.eval₂ ι r)≤1
end
end qziIa4d
end
section
namespace qrezXJe
noncomputable section
open Polynomial
open scoped Classical WithZero
open cu (L FX)
open qb0hmCe (cLN)
open qFD8jve (polarResultant)
open P5_7_7 (phys)
variable {E :Type} [zrb E] [Algebra L E]
def polyBound (w:Valuation E ℤᵐ⁰) (B:E[X]) (h:ℕ) :Prop :=
  ∀ i,w (B.coeff i)≤WithZero.exp (h:ℤ)
def branch (f :E[X][X]) (r :L) :E[X] :=
  polarResultant f*f.eval (C (algebraMap L E r))
def discriminantResultant (G:E[X]) :E :=
  G.resultant G.derivative G.natDegree (G.natDegree-1)
def residuePoly (a :E →ₐ[L] LaurentSeries L) (G:E[X]) :L[X] :=
  G.sum fun i c=>monomial i ((a c).coeff 0)
def rootEval (f :L[X][X]) (P:L[X]) :FX:=f.eval₂ phys (phys P)
def tangentDenom (a :E →ₐ[L] LaurentSeries L) (f :E[X][X]) (P:L[X]) :FX :=
  rootEval (cLN a 0 f).derivative P
def tangentValue (a :E →ₐ[L] LaurentSeries L) (f :E[X][X]) (P:L[X]) :FX :=
  -(rootEval (cLN a 1 f) P/tangentDenom a f P)
structure LocalVariation (a :E →ₐ[L] LaurentSeries L) (f :E[X][X])
    (P:L[X]) (D:ℕ) (G:E[X]) where
  simple :tangentDenom a f P≠0
  num :L[X]
  den:L[X]
  den_ne :den≠0
  reduced:IsCoprime num den
  formula :phys num/phys den=tangentValue a f P
  divides :den∣EuclideanDomain.gcd (residuePoly a G) (residuePoly a G).derivative
  infinity :num.natDegree≤D+den.natDegree
end
end qrezXJe
end
