import ProximityPrize.SubmissionLower.R6960LineEulerFree
import ProximityPrize.SubmissionLower.R6960HornerNative
import ProximityPrize.SubmissionLower.R6960MonicChartInfinityRing
import ProximityPrize.SubmissionLower.R6960MarkedNativeNorm

set_option Elab.async false

-- merged module R6960LineEulerCrossing
section Merged_R6960LineEulerCrossing
set_option Elab.async false
set_option maxHeartbeats 4300000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.LineEuler
noncomputable section
open LaurentPolynomial Module
open scoped Polynomial BigOperators
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
def crossingEval (G : Matrix ι ι (Laurent k)) : H0 G →ₗ[k] (ι→k) :=
  LinearMap.pi fun i=>(Finsupp.lapply (0:ℤ)).comp ((AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap.comp
    ((LinearMap.proj i).comp (finiteLattice k ι⊓transitionLattice G).subtype))
@[simp] theorem crossingEval_apply (G : Matrix ι ι (Laurent k)) (v : H0 G) (i : ι) :
    crossingEval G v i=(v.1 i).coeff 0 := rfl
def negativeTwist (G : Matrix ι ι (Laurent k)) : Matrix ι ι (Laurent k) :=
  (T (R:=k) (-1)) • G
private def shiftLaurent (m : ℤ) : (ι→Laurent k) →ₗ[k] ι→Laurent k :=
  LinearMap.pi fun i=>(LinearMap.mul k (Laurent k) (T m)).comp (LinearMap.proj i)
omit [Fintype ι] [DecidableEq ι] in
private theorem shiftLaurent_apply (m : ℤ) (w : ι→Laurent k) (i : ι) :
    shiftLaurent m w i=T m*w i := rfl
omit [Fintype ι] [DecidableEq ι] in
private theorem shift_inverse (m : ℤ) (w : ι→Laurent k) :
    shiftLaurent (-m) (shiftLaurent m w)=w := by
  funext i
  rw [shiftLaurent_apply,shiftLaurent_apply,←mul_assoc,←T_add,neg_add_cancel,T_zero,one_mul]
private theorem shift_transition (m : ℤ) (G : Matrix ι ι (Laurent k)) :
    transitionLattice ((T (R:=k) m) • G)=(transitionLattice G).map (shiftLaurent m) := by
  have eval (x : ι→Laurent k) : Matrix.toLin' ((T (R:=k) m) • G) x = shiftLaurent m (Matrix.toLin' G x) := by
    funext i
    rw [Matrix.toLin'_apply,shiftLaurent_apply,Matrix.toLin'_apply]
    change (∑ j,((T (R:=k) m) • G) i j * x j) = T m * ∑ j,G i j*x j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _=>by simp only [Matrix.smul_apply,smul_eq_mul,mul_assoc]
  ext w
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨Matrix.toLin' G x,⟨x,hx,rfl⟩,(eval x).symm⟩
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨x,hx,eval x⟩
omit [Fintype ι] [DecidableEq ι] in
private theorem shift_one_finite {w : ι→Laurent k} (hw : w∈finiteLattice k ι) :
    shiftLaurent 1 w∈finiteLattice k ι := by
  intro i hi
  apply AddMonoidAlgebra.mem_supported'.mpr
  intro n hn
  rw [shiftLaurent_apply,coeff_shift]
  apply (AddMonoidAlgebra.mem_supported'.mp (hw i hi))
  change ¬0≤n at hn
  change ¬0≤n-1
  omega
omit [Fintype ι] [DecidableEq ι] in
private theorem shift_minus_one_finite {w : ι→Laurent k} (hw : w∈finiteLattice k ι)
    (zero : ∀ i,(w i).coeff 0=0) : shiftLaurent (-1) w∈finiteLattice k ι := by
  intro i hi
  apply AddMonoidAlgebra.mem_supported'.mpr
  intro n hn
  rw [shiftLaurent_apply,coeff_shift]
  change ¬0≤n at hn
  by_cases eq : n=-1
  · simpa only [eq,sub_self] using zero i
  · exact (AddMonoidAlgebra.mem_supported'.mp (hw i hi)) _ (by change ¬0≤n-(-1); omega)
def crossingKernel (G : Matrix ι ι (Laurent k)) : H0 (negativeTwist G) ≃ₗ[k] (crossingEval G).ker := by
  have shift : transitionLattice (negativeTwist G)=(transitionLattice G).map (shiftLaurent (-1)) :=
    shift_transition (-1) G
  let mapIn : H0 (negativeTwist G) →ₗ[k] (ι→Laurent k) :=
    (shiftLaurent 1).comp (finiteLattice k ι⊓transitionLattice (negativeTwist G)).subtype
  have inH0 (w : H0 (negativeTwist G)) : mapIn w∈finiteLattice k ι⊓transitionLattice G := by
    refine ⟨shift_one_finite w.property.1,?_⟩
    have hw : (w:ι→Laurent k)∈(transitionLattice G).map (shiftLaurent (-1)) := shift ▸ w.property.2
    obtain ⟨v,hv,h⟩ := hw
    have inverse := shift_inverse (-1) v
    change shiftLaurent 1 (shiftLaurent (-1) v)=v at inverse
    change shiftLaurent 1 (w:ι→Laurent k)∈transitionLattice G
    rw [←h,inverse]
    exact hv
  let toH0 := mapIn.codRestrict (finiteLattice k ι⊓transitionLattice G) inH0
  have toKer (w : H0 (negativeTwist G)) : toH0 w∈(crossingEval G).ker := by
    apply LinearMap.mem_ker.mpr
    funext i
    change (shiftLaurent 1 (w:ι→Laurent k) i).coeff 0=0
    rw [shiftLaurent_apply,coeff_shift]
    exact (AddMonoidAlgebra.mem_supported'.mp (w.property.1 i (Set.mem_univ _))) _ (by decide)
  let toKernel := toH0.codRestrict (crossingEval G).ker toKer
  refine LinearEquiv.ofBijective toKernel ⟨?_,?_⟩
  · intro x y eq
    have same : shiftLaurent 1 (x:ι→Laurent k)=shiftLaurent 1 (y:ι→Laurent k) :=
      congrArg (fun w : (crossingEval G).ker=>(w.1:ι→Laurent k)) eq
    exact Subtype.ext (by simpa only [shift_inverse] using congrArg (shiftLaurent (-1)) same)
  · intro x
    let w : ι→Laurent k := shiftLaurent (-1) (x.1:ι→Laurent k)
    have zero (i : ι) : ((x.1:ι→Laurent k) i).coeff 0=0 :=
      congrFun (LinearMap.mem_ker.mp x.property) i
    have h : w∈finiteLattice k ι⊓transitionLattice (negativeTwist G) := by
      refine ⟨shift_minus_one_finite x.1.property.1 zero,?_⟩
      rw [shift]
      exact ⟨_,x.1.property.2,rfl⟩
    refine ⟨⟨w,h⟩,Subtype.ext (Subtype.ext ?_)⟩
    exact shift_inverse (-1) (x.1:ι→Laurent k)
private theorem negative_degree (G : Matrix ι ι (Laurent k)) (unit : IsUnit G) :
    IsUnit (negativeTwist G) ∧ ∃ d : ℤ,G.det.degree=(d:WithBot ℤ) ∧
      (negativeTwist G).det.degree=((d-Fintype.card ι:ℤ):WithBot ℤ) := by
  have ud := (Matrix.isUnit_iff_isUnit_det G).mp unit
  have ut : IsUnit (T (R:=k) (-1)) := isUnit_of_invertible _
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mpr ?_,?_⟩
  · rw [negativeTwist,Matrix.det_smul]
    exact (ut.pow _).mul ud
  · obtain ⟨c,d,nonzero,eq⟩ := unit_monomial G.det ud
    have twist : (negativeTwist G).det=LaurentPolynomial.C c*T (d-Fintype.card ι) := by
      rw [negativeTwist,Matrix.det_smul,eq,T_pow,mul_left_comm,←T_add]
      congr 2
      omega
    exact ⟨d,by rw [eq,degree_C_mul_T _ _ nonzero],by rw [twist,degree_C_mul_T _ _ nonzero]⟩
theorem crossing_rank (G : Matrix ι ι (Laurent k)) (unit : IsUnit G) :
    (finrank k (H1 (negativeTwist G)):ℤ)-(finrank k (H1 G):ℤ)=
      (Fintype.card ι:ℤ)-(finrank k (crossingEval G).range:ℤ) := by
  obtain ⟨twist_unit,d,deg,ddeg⟩ := negative_degree G unit
  obtain ⟨finite,_,m,hm,chi⟩ := euler_index G unit
  obtain ⟨_,_,n,hn,chi'⟩ := euler_index (negativeTwist G) twist_unit
  have meq : m=d := WithBot.coe_inj.mp (hm.symm.trans deg)
  have neq : n=d-Fintype.card ι := WithBot.coe_inj.mp (hn.symm.trans ddeg)
  have rank := LinearMap.finrank_range_add_finrank_ker (crossingEval G)
  rw [←(crossingKernel G).finrank_eq] at rank
  omega
#print axioms crossingKernel
#print axioms crossing_rank
end
end Lower6960.LineEuler

end Merged_R6960LineEulerCrossing

-- merged module R6960MarkedVerticalRank
section Merged_R6960MarkedVerticalRank
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
namespace Lower6960.MarkedEvaluation
open LineEuler LaurentPolynomial Module Matrix Submodule Polynomial
open scoped Polynomial Matrix BigOperators
variable {k J:Type*} [Field k] [Fintype J] [DecidableEq J]
def twist (i:ℤ) (G:Matrix J J (Laurent k)) := (T (R:=k) i) • G
private theorem unit_twist (i:ℤ) {G:Matrix J J (Laurent k)} (unit:IsUnit G) : IsUnit (twist i G) := by
  rw [Matrix.isUnit_iff_isUnit_det,twist,Matrix.det_smul]
  exact ((isUnit_T i).pow _).mul ((Matrix.isUnit_iff_isUnit_det _).mp unit)
private theorem neg_twist (i:ℤ) (G:Matrix J J (Laurent k)) : negativeTwist (twist i G)=twist (i-1) G := by
  rw [negativeTwist,twist,smul_smul,←T_add]
  rw [show -1+i=i-1 by omega];rfl
private theorem upper_map (A:Matrix J J (Polynomial k)) {v:J→Laurent k} (hv:v∈upperLattice k J 0) :
    (A.map (infinityEmbedding (k:=k)))*ᵥv ∈ upperLattice k J 0 := by
  rw [←range_shiftVector] at hv ⊢
  obtain ⟨p,rfl⟩:=hv
  refine ⟨A*ᵥp,funext (fun i=>?_)⟩
  simp only [shiftVector_apply,Nat.cast_zero,T_zero,one_mul,Matrix.mulVec,dotProduct,map_sum,map_mul,Matrix.map_apply]
private theorem inclusion (G:Matrix J J (Laurent k)) :
    transitionLattice (negativeTwist G)≤transitionLattice G := by
  rintro _ ⟨v,hv,rfl⟩
  let A:Matrix J J (Polynomial k):=(Polynomial.X : (Polynomial k)) • (1:Matrix J J (Polynomial k))
  have mat : A.map (infinityEmbedding (k:=k))=T (R:=k) (-1) • (1:Matrix J J (Laurent k)) := by
    ext i j; by_cases eq:i=j <;> simp [A,Matrix.map_apply,Matrix.one_apply,eq,infinityEmbedding_apply,invert_T,smul_eq_mul]
  have trans : negativeTwist G=G*(A.map (infinityEmbedding (k:=k))) := by rw [mat,mul_smul_comm,mul_one]; rfl
  refine ⟨_,upper_map A hv,?_⟩
  change G*ᵥ(_*ᵥv)=(negativeTwist G)*ᵥv
  rw [Matrix.mulVec_mulVec,trans]
private theorem rank_mono (G:Matrix J J (Laurent k)) :
    finrank k (crossingEval (negativeTwist G)).range ≤ finrank k (crossingEval G).range := by
  have le:(crossingEval (negativeTwist G)).range≤(crossingEval G).range := by
    rintro _ ⟨v,rfl⟩; exact ⟨⟨v,⟨v.property.1,inclusion G v.property.2⟩⟩,rfl⟩
  exact Submodule.finrank_mono le
private theorem high_zero (G:Matrix J J (Laurent k)) (unit:IsUnit G) :
    ∃ N:ℕ,finrank k (H1 (twist (N:ℤ) G))=0 := by
  obtain ⟨g,hg⟩:=unit
  obtain ⟨N,A,clear⟩:=clear_transition (↑g⁻¹:Matrix J J (Laurent k))
  have prod : twist N G * A.map (infinityEmbedding (k:=k))=1 := by
    rw [twist,smul_mul_assoc,←mul_smul_comm,←clear,←hg,Units.mul_inv]
  have le:upperLattice k J 0≤transitionLattice (twist N G) := by
    intro v hv
    refine ⟨_,upper_map A hv,?_⟩
    change (twist (N:ℤ) G)*ᵥ(_*ᵥv)=v
    rw [Matrix.mulVec_mulVec,prod,Matrix.one_mulVec]
  have top:finiteLattice k J⊔transitionLattice (twist N G)=⊤ :=
    top_unique ((finite_sup_upper (k:=k) (ι:=J) 0) ▸ sup_le_sup_left le _)
  refine ⟨N,?_⟩
  change finrank k ((J→Laurent k) ⧸ (finiteLattice k J⊔transitionLattice _))=0
  rw [top];exact Module.finrank_zero_of_subsingleton
private theorem countdown (h q:ℕ→ℕ) (step:∀n,h n=h (n+1)+q n) (decrease:Antitone q)
    (last:∃N,h N=0) : h (h 0)=0 := by
  have mono:Antitone h:=antitone_nat_of_succ_le (fun n=>by have :=step n; omega)
  have positive (n) (hn:0<h n) : 0<q n := by
    by_contra! no
    have stable (m): h (n+m)=h n := by
      induction m with
      | zero=>simp
      | succ m ih=>
        have s:=step (n+m)
        have cut:=decrease (show n≤n+m by omega)
        change h (n+m+1)=h n
        omega
    obtain ⟨N,zero⟩:=last
    have z:=mono (show N≤n+N by omega)
    rw [zero,stable] at z;omega
  have bound (n):h n≤h 0-n := by
    induction n with
    | zero=>simp
    | succ n ih=>
      have st:=step n
      by_cases nz:0<h n
      · have:=positive n nz; omega
      · omega
  have:=bound (h 0);omega
theorem vertical_rank (G:Matrix J J (Laurent k)) (unit:IsUnit G) (s:ℕ)
    (deg:G.det.degree=((-(s:ℤ):ℤ):WithBot ℤ)) (inj:Function.Injective (crossingEval G)) :
    finrank k (H1 (twist ((s:ℤ)-1) G))=0 ∧
      finrank k (H0 (twist ((s:ℤ)-1) G))+s=Fintype.card J*s := by
  let h (n:ℕ):=finrank k (H1 (twist ((n:ℤ)-1) G))
  let q (n:ℕ):=Fintype.card J-finrank k (crossingEval (twist (n:ℤ) G)).range
  have st (n:ℕ) : h n=h (n+1)+q n := by
    have r:=crossing_rank (twist (n:ℤ) G) (unit_twist _ unit)
    rw [neg_twist] at r
    have le:=Submodule.finrank_le (crossingEval (twist (n:ℤ) G)).range
    rw [Module.finrank_pi] at le
    dsimp only [h,q]
    rw [show ((n+1:ℕ):ℤ)-1=(n:ℤ) by omega]
    omega
  have decr:Antitone q:=antitone_nat_of_succ_le (by
    intro (n:ℕ)
    have r:=rank_mono (twist ((n+1:ℕ):ℤ) G)
    rw [neg_twist,show ((n+1:ℕ):ℤ)-1=(n:ℤ) by omega] at r
    exact Nat.sub_le_sub_left r _)
  obtain ⟨N,last⟩:=high_zero G unit
  have z:=countdown h q st decr ⟨N+1,by dsimp only [h]; rwa [show ((N+1:ℕ):ℤ)-1=(N:ℤ) by omega]⟩
  obtain ⟨f0,f1,d,ed,chi⟩:=euler_index G unit
  have old:=crossing_rank G unit
  have rank := LinearMap.finrank_range_of_inj inj
  have g0:twist 0 G=G := by simp [twist]
  have neg:twist (-1) G=negativeTwist G := rfl
  have nd:=WithBot.coe_injective (ed.symm.trans deg)
  have start : h 0=s := by
    change finrank k (H1 (negativeTwist G))=s
    omega
  rw [start] at z
  change finrank k (H1 (twist ((s:ℤ)-1) G))=0 at z
  refine ⟨z,?_⟩
  obtain ⟨_,_,v,ev,idx⟩:=euler_index (twist ((s:ℤ)-1) G) (unit_twist _ unit)
  obtain ⟨c,p,cn,repr⟩:=unit_monomial G.det ((Matrix.isUnit_iff_isUnit_det G).mp unit)
  have pval:p= -(s:ℤ) := WithBot.coe_injective ((degree_C_mul_T _ _ cn).symm.trans (repr ▸ deg))
  have dt:(twist ((s:ℤ)-1) G).det=LaurentPolynomial.C c*T (((s:ℤ)-1)*Fintype.card J+p) := by
    rw [twist,Matrix.det_smul,repr,T_pow,mul_left_comm,←T_add];congr 2 <;> ring
  rw [dt,degree_C_mul_T _ _ cn] at ev
  have ev':((s:ℤ)-1)*Fintype.card J+p=v := WithBot.coe_injective ev
  rw [z,Nat.cast_zero,sub_zero,←ev',pval] at idx
  exact_mod_cast (show (finrank k (H0 (twist ((s:ℤ)-1) G)):ℤ)+s=(Fintype.card J:ℤ)*s by rw [idx];ring)
#print axioms vertical_rank
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedVerticalRank

-- merged module R6960MarkedVerticalCharts
section Merged_R6960MarkedVerticalCharts

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6960.MarkedEvaluation
open LineEuler Horner LaurentPolynomial Polynomial Module Matrix Algebra
open scoped Polynomial Matrix BigOperators Lower6960.Horner
open Lower6960.LineEuler (chartLattice chartLattice_iff)
open Lower6960.Horner (finite_chart_algebra)
variable {k E J:Type} [Field k] [Field E] [Algebra (RatFunc k) E] [Fintype J] [DecidableEq J]
local notation "jF" => algebraMap (RatFunc k) E
local notation "Tr" => torusOrder (k:=k) (E:=E)
local notation "Ord" => chartOrder (k:=k) (E:=E)

private theorem chart_range (s:Bool) (b:Basis J (Polynomial k) (Ord s)) (v:J→Laurent k) :
    v∈Lower6960.LineEuler.chartLattice s ↔ ∃ x:Ord s, (localBasis s b).equivFun (chartOrderMap s x)=v := by
  rw [Lower6960.LineEuler.chartLattice_iff];constructor
  · rintro ⟨p,hp⟩;refine ⟨b.equivFun.symm p,funext fun i=>?_⟩
    rw [Basis.equivFun_apply,localBasis_repr,←Basis.equivFun_apply,LinearEquiv.apply_symm_apply,hp]
  · rintro ⟨x,rfl⟩;exact ⟨b.equivFun x,fun i=>by rw [Basis.equivFun_apply,Basis.equivFun_apply,localBasis_repr]⟩

variable (bf:Basis J (Polynomial k) (chartOrder (k:=k) (E:=E) false)) (bi:Basis J (Polynomial k) (chartOrder (k:=k) (E:=E) true))
def decode (bf:Basis J (Polynomial k) (chartOrder (k:=k) (E:=E) false)) (v:J→Laurent k):E:=
  ((localBasis (k:=k) (E:=E) false bf).equivFun.symm v).val
theorem decode_injective : Function.Injective (decode bf) := Subtype.val_injective.comp (localBasis false bf).equivFun.symm.injective

theorem decode_finite (v:J→Laurent k) : v∈finiteLattice k J ↔ decode bf v∈Ord false := by
  rw [show finiteLattice k J=Lower6960.LineEuler.chartLattice false from rfl,chart_range false bf]
  constructor
  · rintro ⟨x,rfl⟩;unfold decode;rw [LinearEquiv.symm_apply_apply];exact x.property
  · intro h
    refine ⟨⟨decode bf v,h⟩,?_⟩
    exact (congrArg (localBasis false bf).equivFun
      (show chartOrderMap false ⟨decode bf v,h⟩=(localBasis false bf).equivFun.symm v from Subtype.ext rfl)).trans
      ((localBasis false bf).equivFun.apply_symm_apply v)

private theorem signed_T (a:ℤ) : algebraMap (Laurent k) E (T a)=(jF RatFunc.X)^a := by
  change jF (LaurentPolynomial.eval₂ RatFunc.C (Units.mk0 RatFunc.X RatFunc.X_ne_zero) (T a))=_
  rw [LaurentPolynomial.eval₂_T,Units.val_zpow_eq_zpow_val,map_zpow₀];rfl

theorem decode_infinity (a:ℤ) (v:J→Laurent k) :
    v∈transitionLattice (twist a (normalizedTransition bf bi)) ↔
    (jF RatFunc.X)^(-a)*decode bf v∈Ord true := by
  let bf':=(localBasis false bf).equivFun
  let bi':=(localBasis true bi).equivFun
  let G:=normalizedTransition bf bi
  have Xn:(jF RatFunc.X:E)≠0:=(map_ne_zero_iff _ (algebraMap (RatFunc k) E).injective).mpr RatFunc.X_ne_zero
  have trans (w:J→Laurent k) : decode bf (twist a G *ᵥw)=(jF RatFunc.X)^a*((bi'.symm w:Tr):E) := by
    rw [twist,Matrix.smul_mulVec,normalizedTransition_mulVec]
    change ((bf'.symm (T a • bf' (bi'.symm w)):Tr):E)=_
    rw [map_smul,LinearEquiv.symm_apply_apply,Subalgebra.coe_smul,Algebra.smul_def,signed_T]
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨u,eq⟩:=(chart_range true bi w).mp hw
    change (jF RatFunc.X)^(-a)*decode bf (twist a G *ᵥ w)∈_
    rw [trans,←mul_assoc,←zpow_add₀ Xn,neg_add_cancel,zpow_zero,one_mul]
    change ((bi'.symm w:Tr):E)∈_
    rw [←eq,show bi'.symm ((localBasis true bi).equivFun (chartOrderMap true u))=chartOrderMap true u from bi'.symm_apply_apply _]
    exact u.property
  · intro h
    let u:Ord true:=⟨_,h⟩
    let w:=bi' (chartOrderMap true u)
    refine ⟨w,(chart_range true bi w).mpr ⟨u,rfl⟩,decode_injective bf ?_⟩
    change decode bf (twist a G *ᵥw)=_
    rw [trans,show bi'.symm w=chartOrderMap true u from bi'.symm_apply_apply _]
    change (jF RatFunc.X)^a*((jF RatFunc.X)^(-a)*decode bf v)=_
    rw [←mul_assoc,←zpow_add₀ Xn,add_neg_cancel,zpow_zero,one_mul]

theorem negative_section_zero [DecidableEq (RatFunc k)] [FiniteDimensional (RatFunc k) E]
    (v:H0 (negativeTwist (normalizedTransition bf bi))) : v=0 := by
  letI : Algebra (Polynomial k) E := ((algebraMap (RatFunc k) E).comp (algebraMap (Polynomial k) (RatFunc k))).toAlgebra
  letI : IsScalarTower (Polynomial k) (RatFunc k) E := IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  let V:=SheetNorm.Infinity k
  letI : Algebra V E:=((algebraMap (RatFunc k) E).comp V.subtype).toAlgebra
  letI : IsScalarTower V (RatFunc k) E:=IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  have fin:decode bf v.val∈Ord false := (decode_finite bf _).mp v.property.1
  have inf:= (decode_infinity bf bi (-1) v.val).mp v.property.2
  simp only [neg_neg,zpow_one] at inf
  have ifin:IsIntegral (Polynomial k) (decode bf v.val) := by
    obtain ⟨p,mon,eq⟩:=fin
    refine ⟨p,mon,?_⟩
    change p.eval₂ ((algebraMap (RatFunc k) E).comp (algebraMap (Polynomial k) (RatFunc k))) _=0
    change p.eval₂ ((algebraMap (Laurent k) E).comp (chartEmbedding false).toRingHom) _=0 at eq
    exact (show ((algebraMap (Laurent k) E).comp (chartEmbedding false).toRingHom)=
        ((algebraMap (RatFunc k) E).comp (algebraMap (Polynomial k) (RatFunc k))) from
      RingHom.ext (fun r=>congrArg (algebraMap (RatFunc k) E) (RingHom.congr_fun Horner.rationalLaurent_finite r))) ▸ eq
  have iinf:IsIntegral V (jF RatFunc.X*decode bf v.val) := by
    obtain ⟨p,mon,root⟩:=inf
    refine ⟨p.map (MonicChart.inftyRingEval k),mon.map _,?_⟩
    rw [eval₂_map]
    change p.eval₂ ((algebraMap V E).comp (MonicChart.inftyRingEval k)) _=0
    have eq : (algebraMap V E).comp (MonicChart.inftyRingEval k)=
        (algebraMap (Laurent k) E).comp (chartEmbedding true).toRingHom :=
      RingHom.ext (fun r=>(congrArg (algebraMap (RatFunc k) E) (RingHom.congr_fun Horner.rationalLaurent_infinity r)).symm)
    rw [eq];exact root
  have zero:=DifferentialPoles.negative_twist _ ifin iinf
  apply Subtype.ext;apply decode_injective bf
  simpa [decode] using zero

set_option synthInstance.maxHeartbeats 200000 in
theorem normalized_rank [DecidableEq (RatFunc k)] [FiniteDimensional (RatFunc k) E]
    (s:ℕ) (deg:(normalizedTransition bf bi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ)) :
    finrank k (H0 (twist ((s:ℤ)-1) (normalizedTransition bf bi)))+s=Fintype.card J*s := by
  apply (vertical_rank _ (normalizedTransition_unit bf bi) s deg _).2
  apply LinearMap.ker_eq_bot.mp;apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  let w:(crossingEval (normalizedTransition bf bi)).ker:=⟨u,hu⟩
  have e:=crossingKernel (normalizedTransition bf bi)
  have zero:=negative_section_zero bf bi (e.symm w)
  have iz:=congrArg e zero
  rw [LinearEquiv.apply_symm_apply,map_zero] at iz
  exact congrArg Subtype.val iz

#print axioms negative_section_zero
#print axioms normalized_rank
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedVerticalCharts

-- merged module R6960MarkedVerticalFunctions
section Merged_R6960MarkedVerticalFunctions
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
namespace Lower6960.MarkedEvaluation
open LineEuler Horner LaurentPolynomial Polynomial Module Matrix Algebra Submodule
open scoped Polynomial Matrix BigOperators Lower6960.Horner
variable {k E J:Type} [Field k] [Field E] [Algebra (RatFunc k) E] [Algebra k E] [IsScalarTower k (RatFunc k) E]
  [Fintype J] [DecidableEq J]
local notation "Ord" => chartOrder (k:=k) (E:=E)
local notation "jF" => algebraMap (RatFunc k) E

def decodeLinear (bf:Basis J (Polynomial k) (Ord false)) : (J→Laurent k)→ₗ[k]E where
  toFun:=decode bf
  map_add' x y:=congrArg Subtype.val ((localBasis false bf).equivFun.symm.map_add x y)
  map_smul' a v:=by
    rw [show a • v=(LaurentPolynomial.C a) • v from funext (fun i=>LaurentPolynomial.smul_eq_C_mul a (v i))]
    change ((localBasis false bf).equivFun.symm ((LaurentPolynomial.C a) • v)).val=_
    rw [map_smul,Subalgebra.coe_smul,Algebra.smul_def,Algebra.smul_def]
    change jF (rationalLaurent (LaurentPolynomial.C a))*_=(algebraMap k E a)*_
    rw [rationalLaurent,LaurentPolynomial.eval₂_C,IsScalarTower.algebraMap_apply k (RatFunc k) E]
    rfl

/-- The actual rational section space in the root field represented by
the Laurent transition at twist a. -/
theorem decode_range (bf:Basis J (Polynomial k) (Ord false)) (bi:Basis J (Polynomial k) (Ord true))
    (a:ℤ) (v:E) :
    (∃u:H0 (twist a (normalizedTransition bf bi)),decode bf u.val=v) ↔
      v∈Ord false ∧ (jF RatFunc.X)^(-a)*v∈Ord true := by
  constructor
  · rintro ⟨u,rfl⟩;exact ⟨(decode_finite bf _).mp u.property.1,(decode_infinity bf bi a _).mp u.property.2⟩
  · rintro ⟨hf,hi⟩
    let w:Ord false:=⟨v,hf⟩
    let u:=(localBasis false bf).equivFun (chartOrderMap false w)
    have value:decode bf u=v := by unfold decode;rw [show (localBasis false bf).equivFun.symm u=chartOrderMap false w
      from (localBasis false bf).equivFun.symm_apply_apply _];rfl
    exact ⟨⟨u,(decode_finite bf u).mpr (value.symm ▸ hf),(decode_infinity bf bi a u).mpr (value.symm ▸ hi)⟩,value⟩

theorem span_le_global (bf:Basis J (Polynomial k) (Ord false)) (bi:Basis J (Polynomial k) (Ord true))
    (a:ℤ) {I:Type} (v:I→E) (h:∀i,v i∈Ord false ∧ (jF RatFunc.X)^(-a)*v i∈Ord true) :
    finrank k (span k (Set.range v))≤finrank k (H0 (twist a (normalizedTransition bf bi))) := by
  let G:=twist a (normalizedTransition bf bi)
  let U:=finiteLattice k J⊓transitionLattice G
  let d:= (decodeLinear bf).domRestrict U
  have fd:= (euler_index G (by
    rw [Matrix.isUnit_iff_isUnit_det,show G.det=(T (R:=k) a)^Fintype.card J*(normalizedTransition bf bi).det from Matrix.det_smul ..]
    exact ((isUnit_T a).pow _).mul ((Matrix.isUnit_iff_isUnit_det _).mp (normalizedTransition_unit bf bi)))).1
  have : FiniteDimensional k U := fd
  have le:span k (Set.range v)≤d.range := span_le.mpr (fun _ ⟨i,eq⟩=>eq ▸ (decode_range bf bi a _).mpr (h i))
  exact (Submodule.finrank_mono le).trans (LinearMap.finrank_range_le d)

#print axioms span_le_global
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedVerticalFunctions

-- merged module R6960MarkedGenericRuling
section Merged_R6960MarkedGenericRuling
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1550000
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (Scalar ChartField)
open LineEuler Horner MonicFourChartDescent RetainedSurfaceClass RetainedRestrictionTorus RetainedTwistedRestriction
open Polynomial LaurentPolynomial Algebra Module Submodule Finset
open scoped Polynomial BigOperators Lower6960.Horner Lower6960.MarkedEvaluation
local instance rulingScalarDecidable : DecidableEq Scalar := Classical.decEq _
local instance rulingFieldDecidable : DecidableEq ChartField := Classical.decEq _
local instance (priority:=2300) rulingScalarBase : Algebra Scalar ChartField := RatFunc.instAlgebraOfPolynomial Scalar Scalar
variable {E J:Type} [Field E] [Algebra ChartField E]
local notation "λx" => (algebraMap (Laurent Scalar) E)
local notation "aE" => algebraMap ChartField E
local notation "Ord" => chartOrder (k:=Scalar) (E:=E)

private theorem chart_constant_integral (b:Bool) (c:Scalar) :
    aE (RatFunc.C c)∈Ord b := by
  -- The affine abscissa algebra is chosen explicitly for either orientation.
  let j:(Polynomial Scalar)→+*E:= (algebraMap (Laurent Scalar) E).comp (chartEmbedding b).toRingHom
  have co : j (Polynomial.C c)=aE (RatFunc.C c) := by
    have cc:chartEmbedding b (Polynomial.C c)=LaurentPolynomial.C c := by
      cases b <;> simp [chartEmbedding,infinityEmbedding_apply,Polynomial.toLaurent_C,invert_C]
    change aE (rationalLaurent (chartEmbedding b (Polynomial.C c)))=_
    rw [cc,rationalLaurent,LaurentPolynomial.eval₂_C]
  letI := j.toAlgebra
  exact co ▸ (isIntegral_algebraMap (A:=E) (x:=Polynomial.C c))

private theorem chart_generators (b:Bool) (p:baseChart (b,false)) :
    aE (p:ChartField)∈Ord b := by
  letI : Algebra (Polynomial Scalar) E:=((algebraMap (Laurent Scalar) E).comp (chartEmbedding b).toRingHom).toAlgebra
  let A:Subring ChartField:=(Ord b).toSubring.comap (algebraMap ChartField E)
  have le:baseChart (b,false)≤A := by
    apply Subring.closure_le.mpr
    rintro _ (⟨r,rfl⟩ | eq | eq)
    · exact chart_constant_integral (E:=E) b (inner r)
    · change _=chartCoordinate b RatFunc.X at eq;subst_vars
      let j:(Polynomial Scalar)→+*E:= (algebraMap (Laurent Scalar) E).comp (chartEmbedding b).toRingHom
      letI := j.toAlgebra
      have x : j Polynomial.X=aE (chartCoordinate b RatFunc.X) := by
        change aE (rationalLaurent (chartEmbedding b Polynomial.X))=_
        apply congrArg (algebraMap ChartField E)
        cases b
        · exact (RingHom.congr_fun Horner.rationalLaurent_finite _).trans RatFunc.algebraMap_X
        · exact (RingHom.congr_fun Horner.rationalLaurent_infinity _).trans (aeval_X _)
      change aE (chartCoordinate b RatFunc.X)∈Ord b
      rw [←x];exact isIntegral_algebraMap (A:=E) (x:=(Polynomial.X:(Polynomial Scalar)))
    · change _=chartCoordinate false scalarCoordinate at eq;subst_vars
      exact chart_constant_integral (E:=E) b _
  exact le p.property

private theorem enlarge_chart (b:Bool) {v:E} (reg:IsIntegral (baseChart (b,false)) v) :
    v∈Ord b := by
  let j:(Polynomial Scalar)→+*E:=(algebraMap (Laurent Scalar) E).comp (chartEmbedding b).toRingHom
  letI := j.toAlgebra
  let R:=Ord b
  let l:(baseChart (b,false))→+*R:=((algebraMap (baseChart (b,false)) E).codRestrict R.toSubring (chart_generators b))
  obtain ⟨p,mon,root⟩:=reg
  have overR:IsIntegral R v:=⟨p.map l,mon.map _,by rw [eval₂_map];exact root⟩
  exact isIntegral_trans _ overR

private theorem seed_denom (T:Finset L) (b:Bool) :
    chartDenom E T (b,false)=aE (RatFunc.C ((algebraMap (Polynomial L) Scalar) (∏z∈T,(Polynomial.X-Polynomial.C z)))) := by
  classical
  rw [chartDenom,map_prod,map_prod,map_prod]
  apply Finset.prod_congr rfl;intro z _
  change aE (zcut (b,false) z:ChartField)=_
  rw [zcut_value,show localFrame (b,false) true=1 from rfl,div_one]
  change aE (scalarCoordinate-constants z)=_
  simp only [map_sub];rfl

theorem generic_membership (i:ℕ) (T:Finset L) (v:E) (regular:controlled E i T v) :
    v∈Ord false ∧ (aE RatFunc.X)^(-(i:ℤ))*v∈Ord true := by
  classical
  let d:=(algebraMap (Polynomial L) Scalar) (∏z∈T,(Polynomial.X-Polynomial.C z))
  have dn:d≠0 := (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) Scalar)).mpr
    (Finset.prod_ne_zero_iff.mpr (fun z _=>X_sub_C_ne_zero z))
  have both (b:Bool) : (fr (b,false):E)⁻¹^i*v∈Ord b := by
    letI : Algebra (Polynomial Scalar) E:=((algebraMap (Laurent Scalar) E).comp (chartEmbedding b).toRingHom).toAlgebra
    have h:=regular (b,false)
    change IsIntegral _ ((fr (b,false):E)⁻¹^i*(chartDenom E T (b,false)*v)) at h
    rw [seed_denom,mul_left_comm] at h
    have src:=enlarge_chart b h
    have result:=(Ord b).mul_mem (chart_constant_integral b d⁻¹) src
    change aE (RatFunc.C d⁻¹)*(aE (RatFunc.C d)*_ )∈_ at result
    rwa [←mul_assoc,←map_mul,←map_mul,inv_mul_cancel₀ dn,map_one,map_one,one_mul] at result
  constructor
  · simpa [fr,localFrame,axisBit] using both false
  · rw [zpow_neg,zpow_natCast,←inv_pow];exact both true

theorem actual_vertical_rank [FiniteDimensional ChartField E] [Fintype J] [DecidableEq J]
    (bf:Basis J (Polynomial Scalar) (Ord false)) (bi:Basis J (Polynomial Scalar) (Ord true))
    (s:ℕ) (positive:0<s) (deg:(normalizedTransition bf bi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ))
    (U:Finset L) (m:ℕ) (v:Fin m→E) (regular:∀j,controlled E (s-1) U (v j)) :
    finrank Scalar (span Scalar (Set.range v))+s≤Fintype.card J*s := by
  have sub:=span_le_global bf bi ((s-1:ℕ):ℤ) v (fun j=>generic_membership (s-1) U _ (regular j))
  rw [show ((s-1:ℕ):ℤ)=(s:ℤ)-1 by omega] at sub
  exact (Nat.add_le_add_right sub s).trans_eq (normalized_rank bf bi s deg)

#print axioms generic_membership
#print axioms actual_vertical_rank
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedGenericRuling
