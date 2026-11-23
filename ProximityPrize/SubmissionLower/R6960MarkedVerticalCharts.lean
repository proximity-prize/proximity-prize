import ProximityPrize.SubmissionLower.R6960HornerNative
import ProximityPrize.SubmissionLower.R6960MarkedVerticalRank
import ProximityPrize.SubmissionLower.R6960DifferentialPoles
import ProximityPrize.SubmissionLower.R6960MonicChartInfinityRing
import ProximityPrize.SubmissionLower.R6960LineEulerFree

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6960.MarkedEvaluation
open LineEuler Horner LaurentPolynomial Polynomial Module Matrix Algebra
open scoped Polynomial Matrix BigOperators Lower6960.Horner
open private Lower6960.LineEuler.chartLattice Lower6960.LineEuler.chartLattice_iff from ProximityPrize.SubmissionLower.R6960LineEulerFree
open private Lower6960.Horner.finite_chart_algebra from ProximityPrize.SubmissionLower.R6960HornerNative
variable {k E J:Type} [Field k] [Field E] [Algebra (RatFunc k) E] [Fintype J] [DecidableEq J]
local notation "jF" => algebraMap (RatFunc k) E
local notation "Tr" => torusOrder (k:=k) (E:=E)
local notation "Ord" => chartOrder (k:=k) (E:=E)

private theorem chart_range (s:Bool) (b:Basis J k[X] (Ord s)) (v:J→Laurent k) :
    v∈Lower6960.LineEuler.chartLattice s ↔ ∃ x:Ord s, (localBasis s b).equivFun (chartOrderMap s x)=v := by
  rw [Lower6960.LineEuler.chartLattice_iff];constructor
  · rintro ⟨p,hp⟩;refine ⟨b.equivFun.symm p,funext fun i=>?_⟩
    rw [Basis.equivFun_apply,localBasis_repr,←Basis.equivFun_apply,LinearEquiv.apply_symm_apply,hp]
  · rintro ⟨x,rfl⟩;exact ⟨b.equivFun x,fun i=>by rw [Basis.equivFun_apply,Basis.equivFun_apply,localBasis_repr]⟩

variable (bf:Basis J k[X] (chartOrder (k:=k) (E:=E) false)) (bi:Basis J k[X] (chartOrder (k:=k) (E:=E) true))
def decode (bf:Basis J k[X] (chartOrder (k:=k) (E:=E) false)) (v:J→Laurent k):E:=
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
  letI : Algebra k[X] E := ((algebraMap (RatFunc k) E).comp (algebraMap k[X] (RatFunc k))).toAlgebra
  letI : IsScalarTower k[X] (RatFunc k) E := IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  let V:=SheetNorm.Infinity k
  letI : Algebra V E:=((algebraMap (RatFunc k) E).comp V.subtype).toAlgebra
  letI : IsScalarTower V (RatFunc k) E:=IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  have fin:decode bf v.val∈Ord false := (decode_finite bf _).mp v.property.1
  have inf:= (decode_infinity bf bi (-1) v.val).mp v.property.2
  simp only [neg_neg,zpow_one] at inf
  have ifin:IsIntegral k[X] (decode bf v.val) := by
    obtain ⟨p,mon,eq⟩:=fin
    refine ⟨p,mon,?_⟩
    change p.eval₂ ((algebraMap (RatFunc k) E).comp (algebraMap k[X] (RatFunc k))) _=0
    change p.eval₂ ((algebraMap (Laurent k) E).comp (chartEmbedding false).toRingHom) _=0 at eq
    exact (show ((algebraMap (Laurent k) E).comp (chartEmbedding false).toRingHom)=
        ((algebraMap (RatFunc k) E).comp (algebraMap k[X] (RatFunc k))) from
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
