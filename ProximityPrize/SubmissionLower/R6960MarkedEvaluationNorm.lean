import ProximityPrize.SubmissionLower.R6960MarkedEvaluationDeterminant

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open Polynomial Algebra Module Finset Matrix
open scoped Polynomial BigOperators
variable {K E : Type*} [Field K] [DecidableEq (RatFunc K)] [Field E]
  [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
  [Algebra K[X] E] [IsScalarTower K[X] (RatFunc K) E]
  [Algebra (SheetNorm.Infinity K) E] [IsScalarTower (SheetNorm.Infinity K) (RatFunc K) E]

/-- A determinant with a zero of order d at scalar infinity, after its common
degree-b clearing, pays b-d degrees in the base norm. -/
theorem norm_degree (v:E) (nz:v≠0) (finite:IsIntegral K[X] v) (b d:ℕ)
    (inf:IsIntegral (SheetNorm.Infinity K) ((algebraMap (RatFunc K) E RatFunc.X)^d*v/
      algebraMap (RatFunc K) E (RatFunc.X^b))) :
    ∃ P:K[X],P≠0 ∧ algebraMap K[X] (RatFunc K) P=norm (RatFunc K) v ∧
      P.natDegree+finrank (RatFunc K) E*d≤finrank (RatFunc K) E*b := by
  let ι:=algebraMap (RatFunc K) E
  let j:=algebraMap K[X] (RatFunc K)
  have xi:IsIntegral K[X] (ι RatFunc.X) := by
    rw [←RatFunc.algebraMap_X,←IsScalarTower.algebraMap_apply]; exact isIntegral_algebraMap
  have xn:ι RatFunc.X≠0 := (map_ne_zero_iff _ ι.injective).mpr RatFunc.X_ne_zero
  obtain ⟨Q,qn,hq,degree⟩:=SheetNorm.polynomial_norm ((ι RatFunc.X)^d*v)
    (mul_ne_zero (pow_ne_zero _ xn) nz) ((xi.pow _).mul finite) b inf
  obtain ⟨P,hP⟩:=IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm (RatFunc K) finite)
  have pn:P≠0 := by
    intro zero; apply (Algebra.norm_ne_zero_iff (R:=RatFunc K)).mpr nz; rw [←hP,zero,map_zero]
  have eq : Q=(Polynomial.X:K[X])^(d*finrank (RatFunc K) E)*P := by
    apply IsFractionRing.injective K[X] (RatFunc K)
    simp only [hq,ι,map_mul,map_pow,RatFunc.algebraMap_X,hP,Algebra.norm_algebraMap,←pow_mul,Nat.mul_comm d]
  rw [eq,natDegree_mul (pow_ne_zero _ X_ne_zero) pn,natDegree_pow,natDegree_X,mul_one] at degree
  exact ⟨P,pn,hP,by simpa only [Nat.mul_comm d,Nat.add_comm] using degree⟩

theorem conjugate_bound [IsGalois (RatFunc K) E] {J : Type*} [Fintype J] [DecidableEq J]
    (e d:ℕ) (ep:0<e) (T:Finset K) (B:Matrix J J E)
    (det:B.det≠0) (finite:IsIntegral K[X] B.det)
    (inf:IsIntegral (SheetNorm.Infinity K) ((algebraMap (RatFunc K) E RatFunc.X)^d*B.det/
      algebraMap (RatFunc K) E (RatFunc.X^(T.card*Fintype.card J))))
    (O:K→Type*) [∀ z,CommRing (O z)] [∀ z,IsDomain (O z)] [∀ z,IsLocalRing (O z)]
    (φ:∀z,K[X]→+*O z) (incl:∀z,O z→+*E) (inj:∀z,Function.Injective (incl z))
    (base:∀z,(incl z).comp (φ z)=(algebraMap (RatFunc K) E).comp (algebraMap K[X] (RatFunc K)))
    (π:∀z,O z) (place:∀ z∈T,π z≠0 ∧ IsLocalRing.residue _ (π z)=0 ∧ φ z (Polynomial.X-C z)=π z)
    (A:∀z,SheetNorm.Aut K E→Matrix J J (O z)) (row:K→SheetNorm.Aut K E→Finset J)
    (lift:∀ z∈T,∀g i j,incl z (A z g i j)=g (B i j))
    (outside:∀ z∈T,∀g,∀i∈row z g,∀j,π z∣A z g i j)
    (count:∀ z∈T,e*(∑g:SheetNorm.Aut K E,(row z g).card)=
      Fintype.card (SheetNorm.Aut K E)*((e-1)*Fintype.card J)) :
    e*d≤T.card*Fintype.card J := by
  obtain ⟨P,pn,eq,cap⟩:=norm_degree B.det det finite _ _ inf
  have size:Fintype.card (SheetNorm.Aut K E)=finrank (RatFunc K) E := by
    rw [Fintype.card_eq_nat_card,IsGalois.card_aut_eq_finrank]
  apply pole_degree e d ep T P pn (size ▸ cap) O φ π place A row _ outside count
  intro z hz
  apply inj z
  have mapP := DFunLike.congr_fun (base z) P
  change incl z (φ z P)=algebraMap (RatFunc K) E (algebraMap K[X] (RatFunc K) P) at mapP
  rw [mapP,eq,Algebra.norm_eq_prod_automorphisms,map_prod]
  apply Finset.prod_congr rfl
  intro g _
  rw [RingHom.map_det,AlgEquiv.map_det]
  exact congrArg Matrix.det (Matrix.ext (fun i j=>(lift z hz g i j).symm))

#print axioms norm_degree
#print axioms conjugate_bound
end Lower6960.MarkedEvaluation
