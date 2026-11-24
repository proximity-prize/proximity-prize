import ProximityPrize.SubmissionLower.R6961MarkedHorizontalRows

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open Polynomial Module Matrix LinearMap
open scoped Polynomial Matrix BigOperators
open P1_7_1_1_2 (exists_full_minor)
variable {k K F E I J:Type} [Field k] [Infinite k] [Field K] [Algebra k K]
  [Field F] [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F] [Algebra K F] [IsScalarTower K (Polynomial K) F]
  [Field E] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def translateField (F:Type) [Field F] [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F] (a:K) : F≃+* F :=
  IsFractionRing.ringEquivOfRingEquiv (K:=F) (L:=F) (taylorEquiv a).toRingEquiv

theorem translate_polynomial (a:K) (p:(Polynomial K)) :
    translateField F a (algebraMap (Polynomial K) F p)=algebraMap (Polynomial K) F (taylor a p) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _

/-- Independent scalar sections of a finite abscissa field have a nonsingular
coordinate minor on actual translates of X. No bound on their polynomial degrees
in X is part of the hypotheses. -/
theorem section_coordinates (b:Basis I F E) (v:J→E) (li:LinearIndependent K v) :
    ∃ N:ℕ,∃ shifts:Fin N↪k,∃ pick:J↪(Fin N×I),
      (Matrix.of (fun i j:J=>translateField F (algebraMap k K (shifts (pick i).1))
        (b.repr (v j) (pick i).2))).det≠0 := by
  classical
  let inc:=algebraMap (Polynomial K) F
  obtain ⟨d,h⟩:=IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (Polynomial K))
    (fun z:I×J=>b.repr (v z.2) z.1)
  choose q eq using h
  let P:Matrix I J (Polynomial K):=fun i j=>q (i,j)
  have poly (i j):inc (P i j)=inc (d:(Polynomial K))*b.repr (v j) i := by
    simpa only [Algebra.smul_def] using eq (i,j)
  have dn:inc (d:(Polynomial K))≠0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
  let lift:(I→(Polynomial K)) →ₗ[K] (I→F) := LinearMap.pi (fun i=>(IsScalarTower.toAlgHom K (Polynomial K) F).toLinearMap.comp (LinearMap.proj i))
  let invert:(I→F) →ₗ[F] E := (inc (d:(Polynomial K)))⁻¹ • b.equivFun.symm.toLinearMap
  let recover:= (invert.restrictScalars K).comp lift
  have coord (j) : lift (P.col j)=inc (d:(Polynomial K)) • b.equivFun (v j) := funext (fun i=>poly i j)
  have vector : recover ∘ P.col =v := by
    funext j
    change (inc (d:(Polynomial K)))⁻¹ • b.equivFun.symm (lift (P.col j))=v j
    rw [coord,map_smul,LinearEquiv.symm_apply_apply,inv_smul_smul₀ dn]
  obtain ⟨N,sh,rows,nonzero⟩:=translated_minor (k:=k) P (LinearIndependent.of_comp recover (vector ▸ li))
  refine ⟨N,sh,rows,?_⟩
  let scale (i:J):=translateField F (algebraMap k K (sh (rows i).1)) (inc (d:(Polynomial K)))
  let V:Matrix J J F:=fun i j=>translateField F (algebraMap k K (sh (rows i).1)) (b.repr (v j) (rows i).2)
  let M:Matrix J J (Polynomial K):=fun i j=>taylor (algebraMap k K (sh (rows i).1)) (P (rows i).2 j)
  have values : inc.mapMatrix M=Matrix.of (fun i j=>scale i*V i j) := by
    ext i j
    change inc (taylor _ _)=_
    rw [←translate_polynomial,poly,map_mul];rfl
  intro vanish
  have zero:=congrArg Matrix.det values
  rw [←RingHom.map_det,Matrix.det_mul_column] at zero
  change V.det=0 at vanish
  exact nonzero ((map_eq_zero_iff _ (IsFractionRing.injective (Polynomial K) F)).mp
    (zero.trans (by rw [vanish,mul_zero])))

/-- Replacing each translated power-basis coordinate block by evaluations on all
distinct sheets preserves full column rank. One ordinary determinant is enough. -/
theorem sheet_minor {H B C : Type} [Field H] [Field B] [Algebra H B] [Fintype C]
    {e:ℕ} (values:Matrix (C×Fin e) J H) (full:∃ pick:J↪(C×Fin e),(values.submatrix pick _root_.id).det≠0)
    (y:C→Fin e→B) (simple:∀c,Function.Injective (y c)) :
    let A:Matrix (C×Fin e) J B:=fun u j=>∑i:Fin e,algebraMap H B (values (u.1,i) j)*(y u.1 u.2)^i.val
    ∃ pick:J↪(C×Fin e),(A.submatrix pick _root_.id).det≠0 := by
  classical
  let A:Matrix (C×Fin e) J B:=fun u j=>∑i:Fin e,algebraMap H B (values (u.1,i) j)*(y u.1 u.2)^i.val
  obtain ⟨sel,sn⟩:=full
  have st: ((algebraMap H B).mapMatrix (values.submatrix sel _root_.id)).det≠0 := by
    rw [←RingHom.map_det];exact (map_ne_zero_iff _ (algebraMap H B).injective).mpr sn
  have inj : Function.Injective A.mulVec := by
    change Function.Injective A.mulVecLin
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    have rows (c:C) (i:Fin e) : ∑ j,algebraMap H B (values (c,i) j)*w j=0 := by
      let coeff (d:Fin e):=∑ j,algebraMap H B (values (c,d) j)*w j
      have atRoot (t:Fin e) : (Matrix.vandermonde (y c)*ᵥcoeff) t=0 := by
        have z:=congrFun hw (c,t)
        change (∑ j,(∑d:Fin e,algebraMap H B (values (c,d) j)*(y c t)^d.val)*w j)=0 at z
        change (∑d:Fin e,(y c t)^d.val*(∑ j,algebraMap H B (values (c,d) j)*w j))=0
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul] at z
        simpa only [mul_left_comm,mul_assoc,mul_comm] using z
      have injV:=Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
        (Matrix.det_vandermonde_ne_zero_iff.mpr (simple c)).isUnit)
      have eq:coeff=0:=injV ((funext atRoot).trans (Matrix.mulVec_zero _).symm)
      exact congrFun eq i
    have vec:(algebraMap H B).mapMatrix (values.submatrix sel _root_.id) *ᵥ w=0 := funext (fun i=>rows _ _)
    apply ((Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr st.isUnit)))
    rwa [Matrix.mulVec_zero]
  have li : LinearIndependent B A.transpose.row := Matrix.mulVec_injective_iff.mp inj
  obtain ⟨pick,good⟩:=P1_7_1_1_2.exists_full_minor A.transpose li
  refine ⟨pick,?_⟩
  change (A.submatrix pick _root_.id).det≠0
  rw [←Matrix.det_transpose];exact good

#print axioms section_coordinates
#print axioms sheet_minor
end Lower6961.MarkedEvaluation
