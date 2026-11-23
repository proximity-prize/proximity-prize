import ProximityPrize.SubmissionLower.ZjobcJd
set_option Elab.async false
open _root_ renaming MvPolynomial → z3y, MvPolynomial.eval → zY9, MvPolynomial.eval₂Hom → zOD, MvPolynomial.map → zDK, MvPolynomial.mem_restrictTotalDegree → zpJ, MvPolynomial.rename → zHw, MvPolynomial.restrictTotalDegree → z0U, MvPolynomial.ringHom_ext → zXT, MvPolynomial.zeroLocus → zSD, Polynomial.C → z1z, Polynomial.mapRingHom → zhd, Polynomial.mapRingHom_comp → zPl, Polynomial.map_map → zoi, PowerSeries.C → zMG, PowerSeries.coeff → z2o, PowerSeries.constantCoeff → zbO, RingHom.ker → zdq, Submodule.mul_mem_mul → zKt
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qL2osVa
noncomputable section
open Polynomial
open P5 (K)
open quN7Z4a (Sheet Smooth Z7)
open cu (L j9)
open gT (kM)
open DQ (DT specialize)
open Cu
open scoped BigOperators
abbrev Series :=PowerSeries L
abbrev SeriesField:=FractionRing Series
abbrev Cut (n:ℕ) :=z3y (Fin 2 ⊕ Fin n) L
structure MarkedSheet (C₀:sQ) [Fact (Irreducible C₀)] where
 J:Ideal kM
 T:Finset K
 z :K→K
 s :K→K[X]
 g:ℕ
 H :ℕ
 D:ℕ
 sheet:Sheet C₀ J g H T z s
 injective :Set.InjOn z (T:Set K)
 degree : ∀ γ∈T,(s γ).natDegree≤D
variable {C₀:sQ} [Fact (Irreducible C₀)]
def MarkedSheet.smoothMarks (C:MarkedSheet C₀) :Finset K:= by
 classical exact C.T.filter fun γ=>Smooth C₀ (Z7 (C.z γ))
def MarkedSheet.genericParam (C:MarkedSheet C₀) :
    DT C.sheet.n →+* oO C₀ :=
  zOD (zT C₀) C.sheet.bY.coordinate
def MarkedSheet.bee (C:MarkedSheet C₀) :Cut C.sheet.n →+* oO C₀ :=
  zOD (zT C₀)
    (Sum.elim (Wt C₀) C.sheet.bY.coordinate)
def MarkedSheet.markedCut (C:MarkedSheet C₀) (γ:K) :Cut C.sheet.n →+* L :=
 zY9 (Sum.elim (Z7 (C.z γ)) (C.sheet.parameter γ))
def MarkedSheet.markedEquation (C:MarkedSheet C₀) (γ:K) :=
 specialize C.sheet.bY.equation (C.sheet.parameter γ)
def MarkedSheet.simple (C:MarkedSheet C₀) (γ:K) :Prop :=
 (C.markedEquation γ).derivative.eval (j9 (C.s γ))≠0
structure Arc (C:MarkedSheet C₀) (γ:K) where
 embedding:oO C₀ →+* SeriesField
 seed :Fin 2→Series
 parameter :Fin C.sheet.n→Series
 constant_eq : ∀ u,embedding (zT C₀ u) =
  algebraMap Series SeriesField (zMG u)
 seed_eq : ∀ i,embedding (Wt C₀ i)=algebraMap Series SeriesField (seed i)
 parameter_eq : ∀ i,embedding (C.sheet.bY.coordinate i) =
  algebraMap Series SeriesField (parameter i)
 seed_value : ∀ i,zbO (seed i)=Z7 (C.z γ) i
 parameter_value : ∀ i,zbO (parameter i)=C.sheet.parameter γ i
 zD : ∃ i,z2o 1 (seed i)≠0
abbrev ArcFamily (C:MarkedSheet C₀) :=(γ : ↥C.smoothMarks)→Arc C γ
def firstCoeff (q:Series[X]) :L[X] :=
 ∑ i∈q.support,monomial i (z2o 1 (q.coeff i))
def Arc.variation {C:MarkedSheet C₀} {γ:K} (A:Arc C γ) :RatFunc L :=
  let f :=C.sheet.bY.equation.map
    (zhd (zOD zMG A.parameter))
  let n:=firstCoeff (f.eval ((j9 (C.s γ)).map zMG))
  (-algebraMap L[X] (RatFunc L) n) /
    algebraMap L[X] (RatFunc L) ((C.markedEquation γ).derivative.eval (j9 (C.s γ)))
def ArcFamily.variation {C:MarkedSheet C₀} (A:ArcFamily C) (γ:K) :RatFunc L:= by
 classical exact if h:γ∈C.smoothMarks then (A ⟨γ,h⟩).variation else 0
def ArcFamily.seedJet {C:MarkedSheet C₀} (A:ArcFamily C) (γ:K) (i:Fin 2) :L:= by
 classical exact if h:γ∈C.smoothMarks then z2o 1 ((A ⟨γ,h⟩).seed i) else 0
def ArcFamily.aiq {C:MarkedSheet C₀} (A:ArcFamily C) (γ:K)
    (q:DT C.sheet.n) (v :ℕ) :Prop :=
  ∃ h:γ∈C.smoothMarks,∀ j<v,
    z2o j (zOD zMG (A ⟨γ,h⟩).parameter q)=0
def MarkedSheet.branchEquation (C:MarkedSheet C₀) (a :L) : (DT C.sheet.n)[X] :=
 let f :=C.sheet.bY.equation
 f.resultant f.derivative C.g (C.g-1)*f.eval (z1z (MvPolynomial.C a))
def MarkedSheet.genericBranch (C:MarkedSheet C₀) (a :L) : (oO C₀)[X] :=
 (C.branchEquation a).map C.genericParam
def MarkedSheet.markedBranch (C:MarkedSheet C₀) (a :L) (γ:K) :L[X] :=
 (C.branchEquation a).map (zY9 (C.sheet.parameter γ))
def monicRadical {F:Type} [Field F] (f :F[X]) :F[X] := by
 classical exact UniqueFactorizationMonoid.radical f
def MarkedSheet.radicalBranch (C:MarkedSheet C₀) (a :L) : (oO C₀)[X] :=
 monicRadical (C.genericBranch a)
structure Branch (C:MarkedSheet C₀) (A:ArcFamily C) (m:ℕ) where
 reference :L
 different : ∀ γ∈C.T,j9 (C.s γ)≠z1z reference
 proper :C.genericBranch reference≠0
 degree : (C.genericBranch reference).natDegree≤ m
 monic: (C.radicalBranch reference).Monic
 keep:Finset K
 subset :keep⊆C.smoothMarks
 excluded: (C.smoothMarks \ keep).card≤2*C.g*C.H
 nonzero_at_mark : ∀ γ∈keep,C.markedBranch reference γ≠0
 degree_at_mark : ∀ γ∈keep,
   (C.markedBranch reference γ).natDegree=(C.genericBranch reference).natDegree
 simple_at_mark : ∀ γ∈keep,C.simple γ
 lift:K→Series[X]
 lift_eq : ∀ γ (h:γ∈keep),
   (lift γ).map (algebraMap Series SeriesField) =
     (C.radicalBranch reference).map (A ⟨γ,subset h⟩).embedding
def Branch.yq {C:MarkedSheet C₀} {A:ArcFamily C} {m:ℕ}
    (B:Branch C A m) (γ:K) :L[X] :=
  (B.lift γ).map zbO
def Branch.DG {C:MarkedSheet C₀} {A:ArcFamily C} {m:ℕ}
    (B:Branch C A m) (γ:K) :ℕ:= by
  classical exact (EuclideanDomain.gcd (B.yq γ) (B.yq γ).derivative).natDegree
def ValueAt (v :RatFunc L) (x y :L) :Prop :=
 v.denom.eval x≠0∧v.num.eval x=y*v.denom.eval x
inductive Target where
 | constant (value :L)
 | projective (i:Fin 2) (a b c:L)
def Target.cost:Target→ℕ
 | .constant _=>0
 | .projective .. => 1
def Target.hit {C:MarkedSheet C₀} (x :L) (γ:K) :Target→Prop
 | .constant r=>(j9 (C.s γ)).eval x=r
 | .projective i a b c =>
     let u:=Z7 (C.z γ) i
     a+u*b≠0∧(a+u*b)*(j9 (C.s γ)).eval x=c*u
def Target.slope {C:MarkedSheet C₀} (A:ArcFamily C) (γ:K) :Target→L
 | .constant _=>0
 | .projective i a b c =>
     a*c*A.seedJet γ i/(a+Z7 (C.z γ) i*b)^2
def MixedDegree {n:ℕ} (q:Cut n) (u v :ℕ) :Prop :=
  ∀ e∈q.support,
    (∑ i:Fin 2,e (Sum.inl i))≤u∧(∑ i:Fin n,e (Sum.inr i))≤v
end
end qL2osVa
end
section
set_option backward.isDefEq.respectTransparency false
namespace qBajpRb
noncomputable section
open Polynomial
open P5 (K)
open quN7Z4a (Z7)
open cu (L FX)
open gT (kM)

open Cu
open private b1t from ProximityPrize.SubmissionLower.ZgdIx1d
variable {C₀:sQ} [Fact (Irreducible C₀)] {J:Ideal kM} {g n:ℕ}
 {R:wJ C₀ J g} (A:yI R n)
abbrev Ambient (n:ℕ) :=z3y (Fin 2 ⊕ Fin n) L
def ek :Ambient n →+* oO C₀ :=
 zOD (zT C₀) (Sum.elim (Wt C₀) A.coordinate)
instance : (zdq (ek A)).IsPrime :=RingHom.ker_isPrime _
abbrev CurveRing:=Ambient n ⧸ zdq (ek A)
abbrev cls :Ambient n →ₐ[L] CurveRing A:=Ideal.Quotient.mkₐ L _
def incl:CurveRing A →+* oO C₀:=RingHom.kerLift (ek A)
theorem incl_injective :Function.Injective (incl A) :=RingHom.kerLift_injective _
@[simp] theorem incl_cls (q:Ambient n) :incl A (cls A q)=ek A q:=rfl
private theorem constant_base :
   (W8 A).comp (zDK (algebraMap L FX)) =
     (Mu C₀).comp (ek A) := by
 apply zXT
 · intro a
   simpa [W8,ek] using b1t C₀ a
 · intro i
   cases i <;> simp [W8,ek]
private theorem mark_pair (z :K) (e :ℕ) :
  (![cu.jz z,(cu.jz z)^e] :Fin 2→FX) =
    algebraMap L FX ∘ (![algebraMap K L z,(algebraMap K L z)^e] :Fin 2→L) := by
 have he (a :L) : (algebraMap L[X] FX) (C a)=algebraMap L FX a :=
  (IsScalarTower.algebraMap_apply L L[X] FX a).symm
 funext i
 fin_cases i <;> simp [cu.jz,he]
private theorem mark_eval (z :K) (t:Fin n→L) (q:Ambient n) :
   zY9 (aCn z t) (zDK (algebraMap L FX) q) =
     algebraMap L FX (zY9 (Sum.elim (Z7 z) t) q) := by
 rw [MvPolynomial.eval_map,MvPolynomial.eval₂_comp]
 congr 1
 funext i
 cases i with
 | inr i=>rfl
 | inl i=>exact congrFun (mark_pair z K1.p) i
def yq (z :K) (t:Fin n→L) (h:aCn z t∈zSD FX (EF A)) :
    CurveRing A →ₐ[L] L :=
  ⟨Ideal.Quotient.lift _ (zY9 (Sum.elim (Z7 z) t)) (by
    intro q hq
    apply (algebraMap L FX).injective
    rw [map_zero,← mark_eval]
    exact h _ (RingHom.mem_ker.mpr (by
     change ((W8 A).comp (zDK (algebraMap L FX))) q=0
     rw [constant_base,RingHom.comp_apply,RingHom.mem_ker.mp hq,map_zero]))) ,
    fun a=>MvPolynomial.eval_C a⟩
@[simp] theorem atMark_cls {z :K} {t:Fin n→L} {h:aCn z t ∈
   zSD FX (EF A)} (q:Ambient n) :
   yq A z t h (cls A q)=zY9 (Sum.elim (Z7 z) t) q:=rfl
def Yx :sQ →ₐ[L] CurveRing A:=(cls A).comp (zHw Sum.inl)
def tupleMap:z3y (Fin n) L →ₐ[L] CurveRing A :=
 (cls A).comp (zHw Sum.inr)
abbrev u7 (k :ℕ) :Submodule L (CurveRing A) :=
 (z0U (Fin 2) L k).map (Yx A).toLinearMap
abbrev tuple (j:ℕ) :Submodule L (CurveRing A) :=
 (z0U (Fin n) L j).map (tupleMap A).toLinearMap
def stock (k j:ℕ) :Submodule L (CurveRing A) :=u7 A k*tuple A j
instance (k j:ℕ) :Module.Finite L (stock A k j) :=
 Module.Finite.of_fg ((Submodule.FG.of_finite (N :=u7 A k)).mul
  (Submodule.FG.of_finite (N :=tuple A j)))
theorem block_mul {σ B:Type} [CommRing B] [Algebra L B]
   (f :z3y σ L →ₐ[L] B) (a b:ℕ) :
   (z0U σ L a).map f.toLinearMap *
     (z0U σ L b).map f.toLinearMap ≤
     (z0U σ L (a+b)).map f.toLinearMap:= by
 rw [Submodule.mul_le]
 rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
 refine ⟨x*y,(zpJ _ _ _).mpr ?_,f.map_mul _ _⟩
 exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add
   ((zpJ _ _ _).mp hx) ((zpJ _ _ _).mp hy))
theorem stock_mul (a b c d:ℕ) :
    stock A a b*stock A c d≤ stock A (a+c) (b+d) := by
  unfold stock
  calc
    _=(u7 A a*u7 A c)*(tuple A b*tuple A d) := by
      rw [mul_assoc (u7 A a),← mul_assoc (tuple A b),Submodule.mul_comm (M:=tuple A b),
        mul_assoc (u7 A c),← mul_assoc (u7 A a)]
    _≤_:=mul_le_mul' (block_mul (Yx A) a c) (block_mul (tupleMap A) b d)
theorem tuple_mem_stock {j:ℕ} {q:CurveRing A} (hq:q∈tuple A j) :
  q∈stock A 0 j:= by
 change q∈u7 A 0*tuple A j
 have h: (1 :CurveRing A)∈u7 A 0 :=
  ⟨1,(zpJ _ _ _).mpr (by simp),(Yx A).map_one⟩
 simpa only [one_mul] using zKt h hq
theorem one_mem_stock (k j:ℕ) : (1 :CurveRing A)∈stock A k j:= by
 rw [← mul_one (1 :CurveRing A)]
 exact zKt
  ⟨1,(zpJ _ _ _).mpr (by simp),(Yx A).map_one⟩
  ⟨1,(zpJ _ _ _).mpr (by simp),(tupleMap A).map_one⟩
def equation : (CurveRing A)[X][X] :=
 A.equation.map (zhd (tupleMap A).toRingHom)
theorem equation_generic :
   (equation A).map (zhd (incl A)) =
     z1z (z1z (A.scale :oO C₀))*R.equation := by
 have hm: (incl A).comp (tupleMap A).toRingHom =
     zOD (zT C₀) A.coordinate := by
   apply zXT
   · intro a
     change incl A (cls A (zHw Sum.inr _))= _
     rw [incl_cls]
     simp [ek]
   · intro i
     change incl A (cls A (zHw Sum.inr _))= _
     rw [incl_cls]
     simp [ek]
 rw [equation,zoi,zPl,hm,A.generic_eq]
theorem equation_mark {z :K} {t:Fin n→L}
   (h:aCn z t∈zSD FX (EF A)) :
   (equation A).map (zhd (yq A z t h).toRingHom) =
     DQ.specialize A.equation t:= by
 have hm: (yq A z t h).toRingHom.comp (tupleMap A).toRingHom=zY9 t:= by
   apply zXT
   · intro a
     change yq A z t h (cls A (zHw Sum.inr _))= _
     rw [atMark_cls]
     simp
   · intro i
     change yq A z t h (cls A (zHw Sum.inr _))= _
     rw [atMark_cls]
     simp
 rw [equation,DQ.specialize,zoi,zPl,hm]
theorem equation_coeff (i a :ℕ) : ((equation A).coeff i).coeff a∈tuple A 1 := by
 refine ⟨(A.equation.coeff i).coeff a,(zpJ _ _ _).mpr (A.degree.2 i a),?_⟩
 simp [equation]
def aia (D g:ℕ) :ℕ := ∑ i:Fin (g+1),i.val*D
end
end qBajpRb
end
section
set_option autoImplicit true
namespace qRoCwuc
noncomputable section
open Polynomial
open P5 (K p)
open cu (L)
open DQ (DT)
open Cu
open quN7Z4a (Sheet)
open scoped BigOperators
variable {C₀:sQ} [Fact (Irreducible C₀)] {J g H T z s}
def coord (S:Sheet C₀ J g H T z s) :DT S.n →+* oO C₀ :=
 zOD (zT C₀) S.bY.coordinate
def coeff (S:Sheet C₀ J g H T z s) (j:ℕ) : (DT S.n)[X] :=
 S.bY.equation.coeff j
def disc (S:Sheet C₀ J 2 H T z s) : (DT S.n)[X] :=
 discrim (coeff S 2) (coeff S 1) (coeff S 0)
def genericDisc (S:Sheet C₀ J 2 H T z s) : (oO C₀)[X] :=
 (disc S).map (coord S)
def ConstantOddPart {F:Type*} [Field F] (D:F[X]) :Prop :=
 ∃ (a :F) (Q:F[X]),D =C a*Q^2
def leadCut (S:Sheet C₀ J 2 H T z s) :DT S.n :=
 (disc S).coeff (genericDisc S).natDegree
def goodMarks (S:Sheet C₀ J 2 H T z s) :Finset K:= by
 classical
 exact T.filter fun γ=>zY9 (S.parameter γ) (leadCut S)≠0
structure OddModel {F:Type} [Field F] (D:F[X]) (U:Finset K) (H :ℕ) where
 radical:F[X]
 monic:radical.Monic
 positive :0< radical.natDegree
 tame :radical.natDegree<p
 separable :radical.Separable
 factor : ∃ Q:F[X],Q.Monic∧D =C D.leadingCoeff*Q^2*radical
 ringAt: (γ:U)→Subring F
 residue : (γ:U)→ ringAt γ →+* L
 surjective : ∀ γ,Function.Surjective (residue γ)
 uniformizer : (γ:U)→ ringAt γ
 kernel : ∀ γ,zdq (residue γ)=Ideal.span {uniformizer γ}
 model : (γ:U)→(ringAt γ)[X]
 lift_eq : ∀ γ,(model γ).map (ringAt γ).subtype=radical
 model_monic : ∀ γ,(model γ).Monic
 square : ∀ γ,IsSquare ((model γ).map (residue γ))
 budget : ∀ e :K→ℕ,
  (∀ γ:U,uniformizer γ^e γ.val ∣
    (model γ).resultant (model γ).derivative radical.natDegree (radical.natDegree - 1)) →
  ∑ γ∈U,e γ≤(2*radical.natDegree - 1)*(2*H)
end
end qRoCwuc
end
