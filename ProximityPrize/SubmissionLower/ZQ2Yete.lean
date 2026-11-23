import ProximityPrize.SubmissionLower.Zd8LTIa
import ProximityPrize.SubmissionLower.ZsE91Ed
import ProximityPrize.SubmissionLower.ZfWgThc
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZMNM9Ma
import ProximityPrize.SubmissionLower.EA
import ProximityPrize.SubmissionLower.ZjNfeqc
import ProximityPrize.SubmissionLower.Z5cOcra
set_option Elab.async false
open _root_ renaming Algebra.subset_adjoin → zkk, CommRing → za6, Function.Surjective → zpX, Ideal.Quotient.mk → zVv, Ideal.mem_span_singleton → zxV, Ideal.span → zye, Polynomial.X → z7y, Polynomial.ringHom_ext → z86, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs, RingHom.ker → zdq
section
section
namespace qBnMK6c
noncomputable section
open Polynomial qe6nVeb qE3Ebna qps5rle
open P5 (K)
open cu (L)
open qb0hmCe (CurveModel)
variable {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane} {C₀:CurveModel q}
def targetNum (R:SiteTarget) (J:Input) (γ:K) :L :=
 R.a+R.b*dcQ J γ R.coord
def targetDen (R:SiteTarget) (J:Input) (γ:K) :L :=
 R.c+R.d*dcQ J γ R.coord
def targetDetAt (R:SiteTarget) (J:Input) (γ:K) (V:Fin 2→L) :L :=
 targetNum R J γ*V 1 - targetDen R J γ*V 0
def crossNum (R:SiteTarget) (B:DualWord J U) (γ:K) :L[X] :=
 C (targetNum R J γ)*B.Q γ - C (targetDen R J γ)*B.P γ
def crossDen (B:DualWord J U) (γ:K) (V:Fin 2→L) :L[X] :=
 B.P γ*C (V 1) - B.Q γ*C (V 0)
def chartDen (R:SiteTarget) (B:DualWord J U) (γ:K) (V:Fin 2→L) (t:L) :L[X] :=
 crossNum R B γ /ₘ (z7y (R:=L) - C R.center) - C t*crossDen B γ V
def reciprocalMatrix (t:L) :Matrix (Fin 2) (Fin 2) L := !![0,1; 1,t]
structure ChartData (S:Sheet B C₀) (R:SiteTarget) (V:Fin 2→L) where
 t:L
 k :ℕ
 g:C₀.E[X][X]
 transformed:C (physicalParameter R.center^k)*g =
   changeOrdinate S.f (siteMatrix R (C₀.seed R.coord) V (reciprocalMatrix t))
 degree :g.natDegree=S.d
 lead_ne :leadAt R.center g≠0
 finite_den : ∀ γ∈S.marks,matchesTarget R B γ→(chartDen R B γ V t).eval R.center≠0
def correction (S:Sheet B C₀) (R:SiteTarget) (γ:K) (V:Fin 2→L) :L[X] :=
  crossDen B γ V*(C (R.d*S.direction γ R.coord)*B.P γ -
    C (R.b*S.direction γ R.coord)*B.Q γ)
end
end qBnMK6c
end
section
set_option backward.isDefEq.respectTransparency false
namespace qyUzJvd
noncomputable section
open Polynomial
open P5 (K)
open cu (L FX)
open P5_7_7 (Dg seedDerivative)
open qGnV2ac (Sections)
open qrKC9pb
open qqi5QRb (pointVal)
abbrev Chart (J:Input) (r :Bool) :=Algebra.adjoin L (Set.range (aD J r))
def coord (J:Input) (r :Bool) (i:Fin 4) :Chart J r :=
 ⟨aD J r i,zkk ⟨i,rfl⟩⟩
def evalPhysical (J:Input) (r :Bool) :L[X] →+* Chart J r :=
 eval₂RingHom (algebraMap L _) (coord J r 0)
def evalSeed (J:Input) (r :Bool) :L[X][X] →+* Chart J r :=
 eval₂RingHom (evalPhysical J r) (coord J r 1)
def evalChart (J:Input) (r :Bool) :Dg →+* Chart J r :=
 eval₂RingHom (evalSeed J r) (coord J r 2)
theorem coe_evalSeed (J:Input) (r :Bool) :
    (algebraMap (Chart J r) (EC J)).comp (evalSeed J r)=(a7W J).comp C:= by
  have h: (algebraMap (Chart J r) (EC J)).comp (evalPhysical J r) =
      (a7W J).comp (C.comp C) := by
    apply z86
    · intro a
      change ((evalPhysical J r (C a) :Chart J r) :EC J)=constant J a
      simp only [evalPhysical,coe_eval₂RingHom,eval₂_C,Subalgebra.coe_algebraMap,
        qqi5QRb.root_algebraMap]
    · change ((evalPhysical J r z7y:Chart J r) :EC J)=amm J
      rw [evalPhysical,coe_eval₂RingHom,eval₂_X]
      rfl
  apply z86
  · intro a
    change ((evalSeed J r (C a) :Chart J r) :EC J)=a7W J (C (C a))
    rw [evalSeed,coe_eval₂RingHom,eval₂_C]
    exact DFunLike.congr_fun h a
  · change ((evalSeed J r z7y:Chart J r) :EC J)=seed J
    rw [evalSeed,coe_eval₂RingHom,eval₂_X]
    rfl
theorem coe_evalChart (J:Input) (r :Bool) (F:Dg) :
  (evalChart J r F:EC J)=KM J r F:= by
 change (algebraMap (Chart J r) (EC J)) (evalChart J r F)= _
 rw [evalChart,KM,coe_eval₂RingHom,coe_eval₂RingHom,hom_eval₂,coe_evalSeed]
 rfl
def sep (J:Input) (r :Bool) :Chart J r :=evalChart J r (chartEq J r).derivative
def num (J:Input) (r :Bool) :Chart J r := -(evalChart J r (seedDerivative (chartEq J r)))
theorem coe_sep (J:Input) (r :Bool) : (sep J r :EC J)=polar J r :=
 coe_evalChart _ _ _
theorem gK6 (J:Input) (r :Bool) :
  variation J r=(num J r :EC J)/sep J r := by
 rw [variation,coe_sep,num,Subalgebra.coe_neg,coe_evalChart]
def seedDiff (J:Input) (r :Bool) (a :L) :Chart J r :=coord J r 1-algebraMap L _ a
def physDiff (J:Input) (r :Bool) (x :L) :Chart J r :=coord J r 0-algebraMap L _ x
structure MarkChart (J:Input) (S:Sections J.F) (γ:K) (x :L) (r :Bool) where
 map :Chart J r →ₐ[L] FX
 regular : ∀ u,pointVal x (map u)≤1
 physical_eq :map (coord J r 0)=P5_7_7.phys z7y
 seed_eq :map (coord J r 1)=algebraMap L FX (algebraMap K L (S.seed γ))
 simple :map (sep J r)≠0
 gK6 : ∃ u:FX,pointVal x u=1 ∧
  map (num J r)/map (sep J r)=u*(P5_7_7.phys (S.A γ)/P5_7_7.phys (S.B γ))
abbrev Normal (J:Input) (r :Bool) :=integralClosure (Chart J r) (EC J)
def NormalRegular (J:Input) (r :Bool) (P:Ideal (Normal J r)) (u:EC J) :Prop :=
 ∃ a :Normal J r,a∉P ∧ ∃ b:Normal J r,(a :EC J)*u=b
theorem chart_regular {J:Input} {r :Bool} (D:GraphPrime J r) (a :Chart J r) :
   D.val (a :EC J)≤1 := by
 obtain ⟨a,ha⟩:=a
 change D.val a≤1
 induction ha using Algebra.adjoin_induction with
 | mem a ha =>
   obtain ⟨i,rfl⟩:=ha
   exact D.regular i
 | algebraMap a =>
   rw [qqi5QRb.root_algebraMap]
   by_cases h:a=0
   · simp [h,constant]
   · exact (D.constants a h).le
 | add a b _ _ ha hb =>
   exact (D.val.map_add _ _).trans (max_le ha hb)
 | mul a b _ _ ha hb =>
   rw [map_mul]
   exact mul_le_one' ha hb
end
end qyUzJvd
end
section
namespace qj0Yp9c
noncomputable section
open Polynomial qrKC9pb
open cu (L)
open scoped WithZero
structure Chart (J:Input) where
 base :Subfield (EC J)
 scalar :L →+* base
 scalar_eq : ∀ t,(scalar t:EC J)=constant J t
 tilt:L
 ayD:1+constant J tilt*jU J false≠0
variable {J:Input}
def denominator (C:Chart J) :EC J :=
 1+constant J C.tilt*jU J false
def numeratorU (C:Chart J) :EC J:=(denominator C)⁻¹
def numeratorV (C:Chart J) :EC J:=jU J false/denominator C
def relativePolar (C:Chart J) :EC J :=
 polar J false/denominator C ^(J.l - 2)
theorem relativePolar_ne (C:Chart J) :relativePolar C≠0 :=
 div_ne_zero (polar_false_ne_zero J) (pow_ne_zero _ C.ayD)
theorem chart_identity (C:Chart J) :
  numeratorU C+constant J C.tilt*numeratorV C=1 := by
 unfold numeratorU numeratorV
 rw [← one_div,← mul_div_assoc,← add_div]
 exact div_self C.ayD
def aho (C:Chart J) :Subalgebra C.base (EC J) :=
 Algebra.adjoin C.base {amm J,seed J,numeratorU C,numeratorV C}
def nY (C:Chart J) :EC J →ₗ[C.base] EC J :=
 LinearMap.mulLeft C.base (relativePolar C)
def equation (C:Chart J) :C.base[X][X][X] :=
 mapRingHom (mapRingHom (mapRingHom C.scalar)) J.F
def m8 (C:Chart J) :C.base[X][X][X] →+* EC J :=
  eval₂RingHom
    (eval₂RingHom (eval₂RingHom C.base.subtype (amm J)) (seed J)) (jU J false)
def fits {M:Type} [Field M] (s a b c:ℕ) (f :M[X][X][X]) :Prop :=
  f.natDegree≤a∧(∀ k,(f.coeff k).natDegree≤ c) ∧
    ∀ k j,(f.coeff k).coeff j≠0→((f.coeff k).coeff j).natDegree+k*s≤b+a*s
structure Cut (J:Input) extends Chart J where
 an1 :toChart.base[X][X][X]
 fits_cutter :fits J.s J.l (J.b+J.s) J.h an1
 vanish:m8 toChart an1=0
 prime_eq :Prime (equation toChart)
 proper : ¬ equation toChart∣an1
structure qg (C:Chart J) {r :Bool} (D:GraphPrime J r) :Prop where
 base_unit : ∀ z :C.base,z≠0→D.val (z :EC J)=1
 regular : ∀ z∈aho C,D.val z≤1
 polar_val :D.val (relativePolar C)=D.val (polar J r)
abbrev PieceIndex (s a b c:ℕ) :=
 Σ k :Fin (a+1),Fin (b+(a-k.val)*s+1)×Fin (c+1)
def mono (C:Chart J) (i j u v :ℕ) :EC J :=
 amm J^i*seed J^j*numeratorU C ^u*numeratorV C ^v
def pieceMono (C:Chart J) {a b c:ℕ} (m:PieceIndex J.s a b c) :EC J :=
 mono C m.2.1.val m.2.2.val (a-m.1.val) m.1.val
def dO (C:Chart J) (a b c:ℕ) :Submodule C.base (EC J) :=
 Submodule.span C.base (Set.range (pieceMono C (a :=a) (b:=b) (c:=c)))
instance (C:Chart J) (a b c:ℕ) :FiniteDimensional C.base (dO C a b c) :=
 FiniteDimensional.span_of_finite _ (Set.finite_range _)
theorem piece_le_ring (C:Chart J) (a b c:ℕ) :dO C a b c≤(aho C).toSubmodule := by
 apply Submodule.span_le.mpr
 rintro _ ⟨m,rfl⟩
 change pieceMono C m∈aho C
 have hX:amm J∈aho C:=zkk (by simp)
 have hz :seed J∈aho C:=zkk (by simp)
 have hu:numeratorU C∈aho C:=zkk (by simp)
 have hv :numeratorV C∈aho C:=zkk (by simp)
 exact mul_mem (mul_mem (mul_mem (pow_mem hX _) (pow_mem hz _)) (pow_mem hu _)) (pow_mem hv _)
def twiceCount (s a b c:ℤ) :ℤ :=
 (c+1)*(2*(a+1)*(b+1)+s*a*(a+1))
def cutDifference (s l b h b₀ h₀ a x z :ℤ) :ℤ :=
  twiceCount s a x z - twiceCount s (a-l) (x-b₀) (z-h₀) -
    twiceCount s (a-l) (x-b-s) (z-h)+twiceCount s (a-2*l) (x-b₀-b-s) (z-h₀-h)
end
end qj0Yp9c
end
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace q53i3jb
noncomputable section
open Polynomial
open cu (L)
open E7 (CurvePlace)
open qNu3xvc
open qoCymac
open scoped Classical WithZero
open private efc adG aMX b4s bHf from ProximityPrize.SubmissionLower.Y
variable {E :Type} [Field E] [Algebra L E]
abbrev Integers (w:CurvePlace L E) :=w.value.valuationSubring
abbrev inc (w:CurvePlace L E) :Integers w →+* E :=w.value.valuationSubring.toSubring.subtype
abbrev map₂ {R S:Type} [za6 R] [za6 S] (i:R →+* S) :
 R[X][X] →+* S[X][X] :=mapRingHom (mapRingHom i)
private theorem coeff_map₂ {R S:Type} [za6 R] [za6 S]
  (i:R →+* S) (f :R[X][X]) (j k :ℕ) :
  ((map₂ i f).coeff j).coeff k=i ((f.coeff j).coeff k) := by
 simp only [map₂,coe_mapRingHom,coeff_map]
private theorem integral_lifts (w:CurvePlace L E) (f :E[X][X]) :
   (∃ g,map₂ (inc w) g=f) ↔ ∀ j k,w.value ((f.coeff j).coeff k)≤1 := by
 simp only [map₂,coe_mapRingHom]
 rw [← mem_lifts (f :=mapRingHom (inc w)) f,lifts_iff_coeff_lifts]
 constructor
 · intro h j k
   obtain ⟨g,hg⟩:=h j
   rw [← hg,coe_mapRingHom,coeff_map]
   exact (g.coeff k).property
 · intro h j
   have hj:f.coeff j∈lifts (inc w) :=
     (lifts_iff_coeff_lifts _).mpr fun k=>⟨⟨_,h j k⟩,rfl⟩
   exact (mem_lifts _).mp hj
def liftIn (w:CurvePlace L E) (f :E[X][X])
    (h : ∀ j k,w.value ((f.coeff j).coeff k)≤1) : (Integers w)[X][X] :=
  ((integral_lifts w f).mpr h).choose
@[simp] theorem map_liftIn (w:CurvePlace L E) (f :E[X][X]) (h) :
    map₂ (inc w) (liftIn w f h)=f :=
  ((integral_lifts w f).mpr h).choose_spec
theorem coeff_liftIn (w:CurvePlace L E) (f :E[X][X]) (h) (j k :ℕ) :
  (↑(((liftIn w f h).coeff j).coeff k) :E)=(f.coeff j).coeff k := by
 have he :=congrArg (fun q:E[X][X]=>(q.coeff j).coeff k) (map_liftIn w f h)
 rwa [coeff_map₂] at he
private theorem gauss_le_iff {R:Type} [Field R] (v :Valuation R ℤᵐ⁰) (f :R[X]) :
   adG v f≤1 ↔ ∀ i,v (f.coeff i)≤1 := by
 constructor
 · exact fun h i=>(aMX v f i).trans h
 · intro h
   exact Finset.sup_le fun i _=>h i
private theorem dvd_lift (w:CurvePlace L E) (f g: (Integers w)[X][X])
   (hunit : ∃ j k,w.value (((f.coeff j).coeff k :Integers w) :E)=1)
   (h:map₂ (inc w) f∣map₂ (inc w) g) :f∣g:= by
 let m:E[X] →+* RatFunc E :=algebraMap _ _
 let v :=(efc (b4s w.value)).comap (mapRingHom m)
 have vc (a :E[X][X]) :
     v a=adG (b4s w.value) (a.map m) :=rfl
 have bound (a :E[X][X]) :
     v a≤1 ↔ ∀ j k,w.value ((a.coeff j).coeff k)≤1 := by
   simp only [vc,gauss_le_iff,coeff_map,show m=algebraMap E[X] (RatFunc E) from rfl,
     bHf]
 have hbound (a : (Integers w)[X][X]) :v (map₂ (inc w) a)≤1 :=
   (bound _).mpr ((integral_lifts w _).mp ⟨a,rfl⟩)
 obtain ⟨j,k,hjk⟩:=hunit
 have hf :v (map₂ (inc w) f)=1 := by
   refine le_antisymm (hbound f) ?_
   let F:=map₂ (inc w) f
   have hk :=aMX w.value (F.coeff j) k
   have hj:=aMX (b4s w.value) (F.map m) j
   rw [coeff_map,show m=algebraMap E[X] (RatFunc E) from rfl,
     bHf,← vc] at hj
   dsimp only [F] at hk
   rw [coeff_map₂] at hk
   change w.value (↑((f.coeff j).coeff k) :E)≤_ at hk
   exact hjk ▸ hk.trans hj
 obtain ⟨q,hq⟩:=h
 have hqv :=hbound g
 rw [hq,map_mul,hf,one_mul] at hqv
 obtain ⟨b,hb⟩:=(integral_lifts w q).mpr ((bound _).mp hqv)
 exact ⟨b,(map_injective _ (map_injective _ Subtype.val_injective)) (by
   change map₂ (inc w) g=map₂ (inc w) (f*b)
   rw [map_mul,hb,hq])⟩
theorem eval_lift_injective (A:Equation E) (w:CurvePlace L E)
   (f : (Integers w)[X][X]) (hf :map₂ (inc w) f=A.f)
   (hunit : ∃ j k,w.value (((f.coeff j).coeff k :Integers w) :E)=1) :
   ∃ j:AdjoinRoot f →+* EC A,Function.Injective j ∧
     ∀ g,j (AdjoinRoot.mk f g)=a7W A (map₂ (inc w) g) := by
 let i:=(a7W A).comp (map₂ (inc w))
 have hker :zye {f} ≤ zdq i:= by
   rw [Ideal.span_singleton_le_iff_mem]
   change a7W A (map₂ (inc w) f)=0
   rw [hf,a7W,zQb,AdjoinRoot.mk_self,map_zero]
 let j:AdjoinRoot f →+* EC A:=Ideal.Quotient.lift _ i hker
 refine ⟨j,(injective_iff_map_eq_zero j).mpr ?_,fun _=>rfl⟩
 intro q
 induction q using AdjoinRoot.induction_on with
 | _ g =>
   intro hz
   apply AdjoinRoot.mk_eq_zero.mpr
   apply dvd_lift w _ _ hunit
   rw [hf]
   apply AdjoinRoot.mk_eq_zero.mp
   apply IsFractionRing.injective (AdjoinRoot A.f) (EC A)
   rw [map_zero]
   exact hz
end
end q53i3jb
end
section
set_option autoImplicit true
open Polynomial renaming ringHom_ext→qz0,eval₂RingHom→qz1
namespace qhFwyvc
noncomputable section
open Polynomial
open P5 (K)
open cu (L FX)
open E7 (CurvePlace)
open P5_7_7 (phys)
open qNu3xvc
open q1kuFjb (residue integralSeries)
open scoped WithZero
variable {E :Type} [Field E] [Algebra L E]
abbrev Integers (w:CurvePlace L E) :=w.value.valuationSubring
abbrev nC (w:CurvePlace L E) :=(Integers w)[X][X]
abbrev includeCoeffs (w:CurvePlace L E) :nC w →+* E[X][X] :=
 mapRingHom (mapRingHom w.value.valuationSubring.subtype)
def reduceSeed {A:Equation E} (S:Sections A) (γ:K) (hγ:γ∈S.marks) :
    Integers (S.place γ) →+* L :=
  residue.comp (((S.atPlace γ hγ).toRingHom.comp
    (S.place γ).value.valuationSubring.subtype).codRestrict
      (LaurentSeries.powerSeries_as_subring L) fun a =>
        (integralSeries (S.atPlace γ hγ a)
          ((S.value γ hγ a).symm.trans_le a.property)).property)
theorem reduceSeed_eq {A:Equation E} (S:Sections A) (γ:K) (hγ:γ∈S.marks)
  (a :Integers (S.place γ)) :
  reduceSeed S γ hγ a=(S.atPlace γ hγ a).coeff 0 :=
 q1kuFjb.fWQ _
def numerator (P Q:L[X]) (r :Bool) :L[X] :=if r then Q else P
def denominator (P Q:L[X]) (r :Bool) :L[X] :=if r then P else Q
def sectionOrdinate (P Q:L[X]) (r :Bool) :FX :=
 phys (numerator P Q r)/phys (denominator P Q r)
def sectionJet (P Q:L[X]) (r :Bool) :FX :=
 let p:=numerator P Q r
 let q:=denominator P Q r
 phys (p.derivative*q - p*q.derivative)/phys q^2
def aIF (P Q:L[X]) (r :Bool) :FX :=
 if r then -(phys P^2)⁻¹ else (phys Q^2)⁻¹
def ek (A:Equation E) (w:CurvePlace L E) (r :Bool) :
    nC w →+* EC A :=
  (KM A r).comp (includeCoeffs w)
def aJB {A:Equation E} (S:Sections A) (γ:K) (hγ:γ∈S.marks) (r :Bool) :
    nC (S.place γ) →+* FX :=
  (qz1 phys (sectionOrdinate (S.P γ) (S.Q γ) r)).comp
    (mapRingHom (mapRingHom (reduceSeed S γ hγ)))
theorem generic_eq (A:Equation E) (w:CurvePlace L E) (r :Bool) :
    ek A w r=qz1
      (qz1 ((seed A).comp w.value.valuationSubring.subtype) (amm A))
      (jU A r) := by
  apply qz0
  · intro f
    have h: ((a7W A).comp C).comp (mapRingHom w.value.valuationSubring.subtype) =
        qz1 ((seed A).comp w.value.valuationSubring.subtype) (amm A) := by
      apply qz0
      · intro c
        simp [seed]
      · simp [amm]
    simpa only [ek,zQb,coe_mapRingHom,map_C,KM,
      coe_eval₂RingHom,eval₂_C] using zLs h f
  · simp [ek,KM]
theorem specialized_eq {A:Equation E} (S:Sections A) (γ:K) (hγ:γ∈S.marks)
    (r :Bool) :
    aJB S γ hγ r=qz1
      (qz1 (phys.comp (Polynomial.C.comp (reduceSeed S γ hγ))) (phys z7y))
      (sectionOrdinate (S.P γ) (S.Q γ) r) := by
  apply qz0
  · intro f
    have h:phys.comp (mapRingHom (reduceSeed S γ hγ))=qz1
        (phys.comp (Polynomial.C.comp (reduceSeed S γ hγ))) (phys z7y) := by
      apply qz0
      · intro c
        simp
      · simp
    simpa only [aJB,zQb,coe_mapRingHom,map_C,
      coe_eval₂RingHom,eval₂_C] using zLs h f
  · simp [aJB]
@[simp] theorem generic_axis (A:Equation E) (w:CurvePlace L E) (r :Bool) :
   ek A w r (Polynomial.C z7y)=amm A:= by
  simp [ek,KM,amm]
@[simp] theorem generic_ordinate (A:Equation E) (w:CurvePlace L E) (r :Bool) :
   ek A w r z7y=jU A r := by
  simp [ek,KM]
structure EM (A:Equation E) (w:CurvePlace L E) (δ:Derivation L E E) (r :Bool) where
 sep:nC w
 dx :nC w
 num :nC w
 sep_map :includeCoeffs w sep=(chartEq A r).derivative
 dx_map :includeCoeffs w dx = -physicalDerivative (chartEq A r)
 num_map :includeCoeffs w num = -seedDerivative δ (chartEq A r)
end
end qhFwyvc
end
section
set_option backward.isDefEq.respectTransparency false
namespace qrrOjma
noncomputable section
open Polynomial IsLocalRing
open WQ (aWF bKW)
open private a5n from ProximityPrize.SubmissionLower.C
open scoped WithZero
private theorem presentation {k T:Type} [Field k] [za6 T]
   (π:T →+* k) (s :k →+* T) (hs : ∀ c,π (s c)=c)
   (x :T) (hk :zdq π=zye {x}) {n:ℕ} (hn:x^n=0) :
   let ev :=eval₂RingHom s x
   zpX ev ∧ ∃ j:ℕ,zdq ev=zye {(z7y:k[X])^j} := by
 let ev :=eval₂RingHom s x
 have cLN (m:ℕ) (z :T) : ∃ f :k[X],∃ u:T,z=ev f + x^m*u:= by
   induction m generalizing z with
   | zero=>exact ⟨0,z,by simp⟩
   | succ m ih =>
     have h:z - s (π z)∈zdq π:= by rw [RingHom.mem_ker,map_sub,hs,sub_self]
     rw [hk,zxV] at h
     obtain ⟨w,hw⟩:=h
     obtain ⟨f,u,hf⟩:=ih w
     refine ⟨C (π z)+Polynomial.X*f,u,?_⟩
     simp only [ev,map_add,map_mul,coe_eval₂RingHom,eval₂_C,eval₂_X,pow_succ']
     rw [hf] at hw
     simp only [ev,coe_eval₂RingHom] at hw
     linear_combination hw
 refine ⟨fun z => ?_,?_⟩
 · obtain ⟨f,u,h⟩:=cLN n z
   exact ⟨f,by simpa only [hn,zero_mul,add_zero] using h.symm⟩
 let J:=zdq ev
 let g:=Submodule.IsPrincipal.generator J
 have hg:zye {g} = J:=Ideal.span_singleton_generator J
 have hm: (z7y:k[X])^n∈J:=RingHom.mem_ker.mpr (by simp [ev,hn])
 rw [← hg,zxV] at hm
 obtain ⟨j,_,hj⟩:=(dvd_prime_pow Polynomial.prime_X n).mp hm
 exact ⟨j,hg.symm.trans (Ideal.span_singleton_eq_span_singleton.mpr hj)⟩
theorem proof :qypA4Sc.c3:= by
 intro E F _ _ _ v hv i δ a ha hlt hsep
 let R:=v.valuationSubring
 let M:=maximalIdeal R
 let I:Ideal R:=zye {a}
 let T:=R ⧸ I
 let k :=ResidueField R
 let q:R →+* T:=zVv I
 change ∃ D:Derivation ℤ T T,∀ b,D (q (i b))=q (i (δ b))
 obtain ⟨u,hu⟩:=hv (WithZero.exp (-1 :ℤ))
 let t:R:=⟨u,by
   change v u≤1
   rw [hu,WithZero.exp_le_one_iff]
   omega⟩
 have ht:v (t:F)=WithZero.exp (-1 :ℤ) :=hu
 have hpow (m:ℕ) :v (↑(t^m) :F)=WithZero.exp (-(m:ℤ)) := by
   change v ((t:F)^m)= _
   rw [map_pow,ht,← WithZero.exp_nsmul]
   simp
 have hM:M=zye {t} := by
   ext z
   rw [v.mem_maximalIdeal_iff,zxV,
     ← (Valuation.valuationSubring.integers v).le_iff_dvd]
   change v (z :F)<1↔v (z :F)≤v (t:F)
   rw [ht]
   by_cases hz :v (z :F)=0
   · simp [hz]
   rw [← WithZero.exp_log hz,WithZero.exp_lt_one_iff,WithZero.exp_le_exp]
   omega
 have ha0:v (a :F)≠0:=v.ne_zero_iff.mpr (by simpa using ha)
 have hlog:WithZero.log (v (a :F))<0 :=
   WithZero.exp_lt_one_iff.mp ((WithZero.exp_log ha0).trans_lt hlt)
 let n:=(-WithZero.log (v (a :F))).toNat
 have hncast: (n:ℤ) = -WithZero.log (v (a :F)) :=
   Int.toNat_of_nonneg (by omega)
 have heq :v (↑(t^n) :F)=v (a :F) := by
   rw [hpow,hncast,neg_neg,WithZero.exp_log ha0]
 have hI:I=zye {t^n} := by
   let hvO:=Valuation.valuationSubring.integers v
   exact le_antisymm
     (Ideal.span_singleton_le_span_singleton.mpr (hvO.dvd_of_le heq.ge))
     (Ideal.span_singleton_le_span_singleton.mpr (hvO.dvd_of_le heq.le))
 have hIM:I≤M:=Ideal.span_le.mpr
   (Set.singleton_subset_iff.mpr (v.mem_maximalIdeal_iff.mpr hlt))
 have hIMpow:I=M^n:= by rw [hM,Ideal.span_singleton_pow,hI]
 let:Algebra E k :=((residue R).comp i).toAlgebra
 let:Algebra E T:=(q.comp i).toAlgebra
 let:Algebra.IsSeparable E k :=hsep
 let:Algebra.FormallyEtale E k :=Algebra.FormallyEtale.of_isSeparable _ _
 let π:T →ₐ[E] k := { Ideal.Quotient.factor hIM with commutes' := fun _=>rfl }
 have hp (z :R) :π (q z)=residue R z :=rfl
 have hq:zpX q:=Ideal.Quotient.mk_surjective
 have hk :zdq π.toRingHom=M.map q:= by
   have hcomap : (zdq π.toRingHom).comap q=M:= by
     ext z
     rw [Ideal.mem_comap,RingHom.mem_ker]
     exact (congrArg (· = 0) (hp z)).to_iff.trans (residue_eq_zero_iff z)
   rw [← hcomap,Ideal.map_comap_of_surjective _ hq]
 have hnil:IsNilpotent (zdq π.toRingHom) := by
   refine ⟨n,?_⟩
   rw [hk,← Ideal.map_pow,← hIMpow]
   exact Ideal.map_mk_eq_bot_of_le le_rfl
 let s :=Algebra.FormallySmooth.liftOfSurjective (AlgHom.id E k) π
   (Ideal.Quotient.factor_surjective hIM) hnil
 have hs (z :k) :π (s z)=z :=
   Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id E k) π _ hnil z
 let x :=q t
 have hx :x^n=0:= by
   change q t^n=0
   rw [← map_pow q]
   apply Ideal.Quotient.eq_zero_iff_mem.mpr
   rw [hI]
   exact Ideal.subset_span (by simp)
 obtain ⟨hsurj,_,hker⟩:=presentation π.toRingHom s.toRingHom hs x
   (by rw [hk,hM,Ideal.map_span,Set.image_singleton]) hx
 obtain ⟨d,hd⟩:=a5n (B:=k) (δ.restrictScalars ℤ)
 let:Differential k :=⟨d⟩
 let ev :=eval₂RingHom s.toRingHom x
 let Dp:Derivation ℤ k[X] k[X] :=Differential.mapCoeffs
 have stable : ∀ f∈zdq ev,Dp f∈zdq ev := by
   rw [hker]
   intro f hf
   rw [zxV,X_pow_dvd_iff] at hf ⊢
   intro m hm
   change (Differential.mapCoeffs f).coeff m=0
   rw [Differential.coeff_mapCoeffs,hf m hm,map_zero]
 let K:=zdq ev
 let e :k[X] ⧸ K ≃+* T:=ev.quotientKerEquivOfSurjective hsurj
 let:Differential (k[X] ⧸ K) :=⟨aWF K Dp stable⟩
 let:Differential T:=Differential.equiv e.symm
 refine ⟨Differential.deriv,fun b => ?_⟩
 have hc (c:E) :e (zVv K (C (algebraMap E k c)))=q (i c) := by
   rw [show e=ev.quotientKerEquivOfSurjective hsurj from rfl,
     RingHom.quotientKerEquivOfSurjective_apply_mk]
   change (C (algebraMap E k c)).eval₂ s.toRingHom x= _
   rw [eval₂_C]
   exact s.commutes c
 change e (aWF K Dp stable (e.symm (q (i b))))= _
 rw [← hc b,e.symm_apply_apply,bKW]
 change e (zVv K (Differential.mapCoeffs (C (algebraMap E k b))))= _
 rw [Differential.mapCoeffs_C]
 change e (zVv K (C (d (algebraMap E k b))))= _
 rw [hd,Derivation.restrictScalars_apply,hc]
end
end qrrOjma
end
end
