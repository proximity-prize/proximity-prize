import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.G8
namespace ProximityPrize.SubmissionLower.RCN344
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
abbrev Place:=RCN345.NormalizedValuation K L
structure SeparableCoordinate where
 embedding:RatFunc K →ₐ[K] L
 finite:letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
   FiniteDimensional (RatFunc K) L
 separable:letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc K) L
namespace SeparableCoordinate
def value (c:SeparableCoordinate K L):L:=
 c.embedding (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
def degree (c:SeparableCoordinate K L):ℕ:=
 letI:Algebra (RatFunc K) L:=c.embedding.toRingHom.toAlgebra
 Module.finrank (RatFunc K) L
variable [IsAlgClosed K]
theorem finite_sum_pole_le_degree (c:SeparableCoordinate K L)
   (W:Finset (Place K L)):
   (∑ v∈W,RCN346.poleOrder K L v (value K L c)) ≤
     (degree K L c:ℤ):=by
 letI:Algebra (RatFunc K) L:=c.embedding.toRingHom.toAlgebra
 letI:Algebra (Polynomial K) L:=
   (c.embedding.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K))).toAlgebra
 letI:IsScalarTower (Polynomial K) (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq' rfl
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun a↦(c.embedding.commutes a).symm
 letI:IsScalarTower K (Polynomial K) L:=
   IsScalarTower.of_algebraMap_eq fun a↦by
     change algebraMap K L a=
       c.embedding (algebraMap (Polynomial K) (RatFunc K) (algebraMap K (Polynomial K) a))
     rw [←IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
     exact (c.embedding.commutes a).symm
 letI:FiniteDimensional (RatFunc K) L:=c.finite
 letI:Algebra.IsSeparable (RatFunc K) L:=c.separable
 exact RCN346.finite_sum_pole_le_finrank K L W
end SeparableCoordinate
abbrev Coordinate:=K ⊕ SeparableCoordinate K L
def coordinateValue:Coordinate K L → L:=
 Sum.elim (algebraMap K L) (SeparableCoordinate.value K L)
def coordinateDegree:Coordinate K L → ℕ:=
 Sum.elim (fun _↦0) (SeparableCoordinate.degree K L)
theorem constant_value_le_one (v:Place K L) (c:K):
   v.val (algebraMap K L c) ≤ 1:=by
 letI:v.val.IsTrivialOn K:=v.property.2
 exact Valuation.IsTrivialOn.valuation_algebraMap_le_one v.val c
variable [IsAlgClosed K]
theorem finite_sum_coordinate_pole_le_degree (c:Coordinate K L)
   (W:Finset (Place K L)):
   (∑ v∈W,RCN346.poleOrder K L v (coordinateValue K L c)) ≤
     (coordinateDegree K L c:ℤ):=by
 rcases c with a | c
 · have hz:∀ v:Place K L,
       RCN346.poleOrder K L v (algebraMap K L a)=0:=
     fun v↦RCN346.poleOrder_eq_zero_of_le_one K L v _
       (constant_value_le_one K L v a)
   simp only [coordinateValue,coordinateDegree,Sum.elim_inl,hz,Finset.sum_const_zero,
     Nat.cast_zero,le_refl]
 · exact SeparableCoordinate.finite_sum_pole_le_degree K L c W
variable {σ:Type*} [Fintype σ]
theorem finite_sum_polynomial_pole_le_box (W:Finset (Place K L))
   (c:σ → Coordinate K L) (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   (∑ v∈W,RCN346.poleOrder K L v
     (MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦coordinateValue K L (c i)) F)) ≤
     ∑ i,(cap i:ℤ)*(coordinateDegree K L (c i):ℤ):=by
 have hlocal:=RCN187.weighted_poleOrder_eval_le_box
   W (fun _↦1) (fun v↦v.val) (algebraMap K L)
   (fun v _ a↦constant_value_le_one K L v a)
   (fun i↦coordinateValue K L (c i)) cap F hcap
 simp only [Nat.cast_one,one_mul] at hlocal
 calc
   _ ≤ ∑ i,(cap i:ℤ)*
       ∑ v∈W,RCN346.poleOrder K L v (coordinateValue K L (c i)):=hlocal
   _ ≤ _:=by
     apply Finset.sum_le_sum
     intro i _
     exact mul_le_mul_of_nonneg_left
       (finite_sum_coordinate_pole_le_degree K L (c i) W) (Int.natCast_nonneg _)
section FixedSeparator
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place K L):=Classical.decEq _
theorem finite_zero_places_le_box (c:σ → Coordinate K L)
   (cap:σ → ℕ) (F:MvPolynomial σ K) (hcap:∀ i,F.degreeOf i ≤ cap i)
   (hF:MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦coordinateValue K L (c i)) F≠0)
   (U:Finset (Place K L))
   (hU:∀ v∈U,1 ≤ RCN026.order K L v
     (MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦coordinateValue K L (c i)) F)):
   (U.card:ℤ) ≤ ∑ i,(cap i:ℤ)*(coordinateDegree K L (c i):ℤ):=by
 exact (RCN026.finite_zero_places_le_poleMass K L _ hF U hU).trans
   (finite_sum_polynomial_pole_le_box K L _ c cap F hcap)
section AffineModel
variable (A:Type*) [CommRing A] [IsDomain A]
variable [Algebra K A] [Algebra A L] [IsFractionRing A L]
variable [Algebra (Polynomial K) A]
variable [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
variable [IsScalarTower (Polynomial K) A L]
def modelPlace (φ:A →ₐ[K] K):Place K L:=
 RCN345.chartMap K L
   (Sum.inl (RCN000.actualPointPlace K A L φ))
theorem modelPlace_injective:Function.Injective (modelPlace K L A):=by
 intro φ ψ h
 have hchart:=(RCN345.chartMap_bijective K L).1 h
 exact RCN000.actualPointPlace_injective K A L (Sum.inl.inj hchart)
theorem map_model_eval (x:σ → A) (F:MvPolynomial σ K):
   algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F)=
     MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦algebraMap A L (x i)) F:=by
 have hhom:(algebraMap A L).comp (MvPolynomial.eval₂Hom (algebraMap K A) x)=
     MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦algebraMap A L (x i)):=by
   ext a
   · simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_C]
     exact (IsScalarTower.algebraMap_apply K A L a).symm
   · simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_X']
 exact DFunLike.congr_fun hhom F
theorem finite_model_zero_points_le_box
   (x:σ → A) (c:σ → Coordinate K L)
   (hc:∀ i,coordinateValue K L (c i)=algebraMap A L (x i))
   (cap:σ → ℕ) (F:MvPolynomial σ K) (hcap:∀ i,F.degreeOf i ≤ cap i)
   (hF:MvPolynomial.eval₂Hom (algebraMap K A) x F≠0)
   (S:Finset (A →ₐ[K] K))
   (hS:∀ φ∈S,φ (MvPolynomial.eval₂Hom (algebraMap K A) x F)=0):
   (S.card:ℤ) ≤ ∑ i,(cap i:ℤ)*(coordinateDegree K L (c i):ℤ):=by
 classical
 have heval:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦coordinateValue K L (c i)) F=
       algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F):=by
   simp_rw [hc]
   exact (map_model_eval K L A x F).symm
 have hnonzero:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦coordinateValue K L (c i)) F≠0:=by
   rw [heval]
   intro hz
   apply hF
   apply IsFractionRing.injective A L
   simpa only [map_zero] using hz
 let U:=S.image (modelPlace K L A)
 have hU:∀ v∈U,1 ≤ RCN026.order K L v
     (MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦coordinateValue K L (c i)) F):=by
   intro v hv
   obtain ⟨φ,hφ,rfl⟩:=Finset.mem_image.mp hv
   rw [heval]
   exact RCN000.actual_model_zero_order_ge_one K A L φ _ hF (hS φ hφ)
 have h:=finite_zero_places_le_box K L c cap F hcap hnonzero U hU
 have hcard:U.card=S.card:=Finset.card_image_of_injective _ (modelPlace_injective K L A)
 rwa [hcard] at h
end AffineModel
end FixedSeparator
end
end ProximityPrize.SubmissionLower.RCN344
