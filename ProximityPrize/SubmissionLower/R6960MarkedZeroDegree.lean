import ProximityPrize.SubmissionLower.R6960MarkedVerticalFunctions
import Mathlib.Algebra.Polynomial.Basis
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
  [Fintype J] [DecidableEq J] [FiniteDimensional (RatFunc k) E] [DecidableEq (RatFunc k)]
local notation "Ord" => chartOrder (k:=k) (E:=E)

private theorem global_is_integral (bf:Basis J (Polynomial k) (Ord false)) (bi:Basis J (Polynomial k) (Ord true))
    {v:E} (f:v∈Ord false) (h:v∈Ord true) : IsIntegral k v := by
  by_contra no
  have tr:Transcendental k v:=fun alg=>no alg.isIntegral
  let G:=twist 0 (normalizedTransition bf bi)
  let N:=finrank k (H0 G)+1
  let powers (n:Fin N):E:=v^n.val
  have poly:LinearIndependent k (fun n:Fin N=>(Polynomial.X:(Polynomial k))^n.val) := by
    have t:LinearIndependent k (fun a:ℕ=>(Polynomial.X:(Polynomial k))^a) :=by
      simpa only [Polynomial.coe_basisMonomials,Polynomial.X_pow_eq_monomial] using (Polynomial.basisMonomials k).linearIndependent
    exact t.comp Fin.val Fin.val_injective
  have inds : LinearIndependent k powers := by
    have I:=poly.map' (aeval v).toLinearMap (LinearMap.ker_eq_bot_of_injective (transcendental_iff_injective.mp tr))
    simpa only [Function.comp_def,AlgHom.toLinearMap_apply,map_pow,aeval_X,powers] using I
  have count:=span_le_global bf bi 0 powers (by
    intro j
    refine ⟨?_,?_⟩
    · letI : Algebra (Polynomial k) E:=((algebraMap (Laurent k) E).comp (chartEmbedding false).toRingHom).toAlgebra
      exact (Ord false).pow_mem f _
    · letI : Algebra (Polynomial k) E:=((algebraMap (Laurent k) E).comp (chartEmbedding true).toRingHom).toAlgebra
      rw [neg_zero,zpow_zero,one_mul];exact (Ord true).pow_mem h _)
  rw [finrank_span_eq_card inds,Fintype.card_fin] at count
  exact Nat.not_succ_le_self _ count

private theorem zero_coeff (f:(Polynomial k)) : f.toLaurent.coeff (0:ℤ)=f.eval 0 := by
  rw [←Polynomial.coeff_zero_eq_eval_zero,LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ 0

/-- When the normalized line has determinant degree zero, its degree-e
function field has e independent functions algebraic over the constants. -/
theorem constant_frame (bf:Basis J (Polynomial k) (Ord false)) (bi:Basis J (Polynomial k) (Ord true))
    (deg:(normalizedTransition bf bi).det.degree=(0:WithBot ℤ)) :
    ∃ w:J→E,LinearIndependent (RatFunc k) w ∧ ∀j,IsIntegral k (w j) := by
  classical
  let G:=normalizedTransition bf bi
  obtain ⟨fd,_,d,ed,chi⟩:=normalized_euler bf bi
  have dz:d=0:=WithBot.coe_injective (ed.symm.trans deg)
  have inj:Function.Injective (crossingEval G) := by
    apply LinearMap.ker_eq_bot.mp;apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    let ker:(crossingEval G).ker:=⟨u,hu⟩
    let eq:=crossingKernel G
    have z:=congrArg eq (negative_section_zero bf bi (eq.symm ker))
    rw [LinearEquiv.apply_symm_apply,map_zero] at z;exact congrArg Subtype.val z
  have bound:=LinearMap.finrank_le_finrank_of_injective inj
  rw [Module.finrank_pi] at bound
  have size:finrank k (H0 G)=Fintype.card J := by
    change (finrank k (H0 G):ℤ)-(finrank k (H1 G):ℤ)=_ at chi;omega
  let B:Basis J k (H0 G):=(Module.finBasisOfFinrankEq k _ size).reindex (Fintype.equivFin J).symm
  let u (i:J):Ord false:=⟨decode bf (B i).val,(decode_finite bf _).mp (B i).property.1⟩
  let M:=chartMatrix bf u
  have coord (i j:J) : (M i j).toLaurent=(B j).val i := by
    have eq: chartOrderMap false (u j)=(localBasis false bf).equivFun.symm (B j).val:=Subtype.ext rfl
    rw [show (M i j).toLaurent=(localBasis false bf).equivFun (chartOrderMap false (u j)) i from
      (localBasis_repr false bf (u j) i).symm,eq,LinearEquiv.apply_symm_apply]
  have cmp:(M.map (evalRingHom 0)).col=(crossingEval G)∘B := by
    funext i j;change (M j i).eval 0=((B i).val j).coeff 0
    rw [←zero_coeff,coord]
  have indep:LinearIndependent k (M.map (evalRingHom 0)).col :=
    cmp ▸ B.linearIndependent.map' _ (LinearMap.ker_eq_bot_of_injective inj)
  have mn:M.det≠0 := by
    have n:=((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp indep)).ne_zero
    intro z;apply n;rw [←show (evalRingHom (0:k)) M.det=(M.map (evalRingHom 0)).det from RingHom.map_det _ _,z,map_zero]
  let jpoly: (Polynomial k)→+*E:=(algebraMap (Laurent k) E).comp (chartEmbedding false).toRingHom
  letI := jpoly.toAlgebra
  letI : IsScalarTower (Polynomial k) (RatFunc k) E:=IsScalarTower.of_algebraMap_eq (fun r=>
    congrArg (algebraMap (RatFunc k) E) (RingHom.congr_fun Horner.rationalLaurent_finite r))
  have iu:LinearIndependent (Polynomial k) u := by
    apply Fintype.linearIndependent_iff.mpr
    intro a h i
    have eq:M*ᵥa=0 := by
      funext t
      have st:=congrArg (fun x:Ord false=>bf.repr x t) h
      simpa only [map_sum,map_smul,map_zero,Finsupp.finsetSum_apply,Finsupp.smul_apply,
        smul_eq_mul,Finsupp.zero_apply,Matrix.mulVec,dotProduct,M,chartMatrix,mul_comm,Pi.zero_apply] using st
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero mn eq) i
  let w (j:J):E:=(u j:E)
  have iw:LinearIndependent (Polynomial k) w:=iu.map' (Ord false).val.toLinearMap
    (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  refine ⟨w,(LinearIndependent.iff_fractionRing (Polynomial k) (RatFunc k)).mp iw,fun i=>?_⟩
  have g0:twist 0 G=G:=by simp [twist]
  have hi: (B i).val∈transitionLattice (twist 0 G):=g0.symm ▸ (B i).property.2
  apply global_is_integral bf bi (u i).property
  simpa only [neg_zero,zpow_zero,one_mul] using (decode_infinity bf bi 0 _).mp hi

#print axioms constant_frame
end Lower6960.MarkedEvaluation
