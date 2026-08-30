import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AH
import ProximityPrize.SubmissionLower.M
namespace ProximityPrize.SubmissionLower.ContactSparsePoleZeroCountResearch
open scoped Classical BigOperators WithZero
open IsDedekindDomain
open ContactSparsePoleSupportResearch
open CoordinateBoxZeroCount
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveScalarTowers
open ActualCurveZeroCount
noncomputable section
variable {K L σ:Type} [Field K] [Field L] [Fintype σ]
variable [Algebra K L] [IsAlgClosed K]
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L]
variable [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L]
variable [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place K L):=Classical.decEq _
variable (A:Type) [CommRing A] [IsDomain A]
variable [Algebra K A] [Algebra A L] [IsFractionRing A L]
variable [Algebra (Polynomial K) A]
variable [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
variable [IsScalarTower (Polynomial K) A L]
theorem finite_model_zero_points_le_exponentSet
   (x:σ → A) (E:Finset (σ →₀ ℕ))
   (F:MvPolynomial σ K) (hFE:F.support ⊆ E)
   (hF:MvPolynomial.eval₂Hom (algebraMap K A) x F≠0)
   (q:ℕ)
   (hpole:∀ W:Finset (Place K L),
     (∑ v∈W,exponentSetPoleWeight v.val
       (fun i↦algebraMap A L (x i)) E) ≤ (q:ℤ))
   (S:Finset (A →ₐ[K] K))
   (hS:∀ ψ∈S,ψ (MvPolynomial.eval₂Hom (algebraMap K A) x F)=0):
   S.card ≤ q:=by
 classical
 have heval:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦algebraMap A L (x i)) F=
       algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F):=
   (map_model_eval K L A x F).symm
 have hnonzero:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦algebraMap A L (x i)) F≠0:=by
   rw [heval]
   intro hz
   apply hF
   apply IsFractionRing.injective A L
   simpa only [map_zero] using hz
 let U:=S.image (modelPlace K L A)
 have hU:∀ v∈U,1 ≤ CommonPlaceBalance.order K L v
     (MvPolynomial.eval₂Hom (algebraMap K L)
       (fun i↦algebraMap A L (x i)) F):=by
   intro v hv
   obtain ⟨ψ,hψ,rfl⟩:=Finset.mem_image.mp hv
   rw [heval]
   exact ActualAffineModelPlaces.actual_model_zero_order_ge_one
     K A L ψ _ hF (hS ψ hψ)
 let W:=CommonPlaceBalance.placesFor K L _ hnonzero
 have hcount:=CommonPlaceBalance.finite_zero_places_le_poleMass
   K L _ hnonzero U hU
 have hsupport:=weighted_poleOrder_eval_le_exponentSet W
   (fun _↦1) (fun v↦v.val) (algebraMap K L)
   (fun v _ c↦constant_value_le_one K L v c)
   (fun i↦algebraMap A L (x i)) E F hFE
 have hcard:U.card=S.card:=
   Finset.card_image_of_injective _ (modelPlace_injective K L A)
 have hq:(S.card:ℤ) ≤ q:=by
   calc
     (S.card:ℤ)=(U.card:ℤ):=by rw [hcard]
     _ ≤ ∑ v∈W,CoordinatePoleMass.poleOrder K L v
         (MvPolynomial.eval₂Hom (algebraMap K L)
           (fun i↦algebraMap A L (x i)) F):=hcount
     _ ≤ ∑ v∈W,exponentSetPoleWeight v.val
         (fun i↦algebraMap A L (x i)) E:=by
       simpa only [CoordinatePoleMass.poleOrder,Nat.cast_one,one_mul] using hsupport
     _ ≤ (q:ℤ):=hpole W
 exact_mod_cast hq
section ActualCurve
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
theorem finite_zero_points_le_exponentSet_of_separator
   (hproj:ProjectionsFiniteSeparable K P)
   (i₀:Fin 3) (hi₀:Transcendental K (coordinate K P i₀))
   (E:Finset (Fin 3 →₀ ℕ)) (q:ℕ)
   (hpole:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P i₀ hi₀
     ∀ W:Finset (Place K (CoordinateField K P)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate K P) E) ≤ (q:ℤ))
   (F:MvPolynomial (Fin 3) K) (hFE:F.support ⊆ E) (hF:F∉P)
   (S:Finset (Fin 3 → K))
   (hSP:∀ v∈S,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hSF:∀ v∈S,MvPolynomial.aeval v F=0):
   S.card ≤ q:=by
 classical
 letI:Algebra (Polynomial K) (CoordinateRing K P):=
   quotientPolynomialAlgebra K P i₀
 letI:Algebra (Polynomial K) (CoordinateField K P):=
   polynomialBaseAlgebra K P i₀
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   rationalBaseAlgebra K P i₀ hi₀
 letI:=quotientBaseScalarTower K P i₀
 letI:=polynomialBaseScalarTower K P i₀
 letI:=quotientFractionScalarTower K P i₀
 letI:=polynomialRationalScalarTower K P i₀ hi₀
 letI:=rationalBaseScalarTower K P i₀ hi₀
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=
   (hproj i₀ hi₀).1
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=
   (hproj i₀ hi₀).2
 let liftPoint:{v:Fin 3 → K//v∈S} →
     (CoordinateRing K P →ₐ[K] K):=
   fun v↦pointHom K P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w hvw
   have h:=pointHom_injective K P hvw
   apply Subtype.ext
   exact congrArg (fun z:PointOn K P↦z.val) h
 let points:=S.attach.image liftPoint
 have hpoints:∀ ψ∈points,ψ (MvPolynomial.eval₂Hom
     (algebraMap K (CoordinateRing K P)) (quotientCoordinate K P) F)=0:=by
   intro ψ hψ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hψ
   rw [quotient_eval_eq_mk]
   exact hSF v.1 v.2
 have hpole':∀ W:Finset (Place K (CoordinateField K P)),
     (∑ v∈W,exponentSetPoleWeight v.val
       (fun i↦algebraMap (CoordinateRing K P) (CoordinateField K P)
         (quotientCoordinate K P i)) E) ≤ (q:ℤ):=by
   intro W
   simpa only [quotientCoordinate_fraction] using hpole W
 have hcount:=finite_model_zero_points_le_exponentSet
   (K:=K) (L:=CoordinateField K P) (σ:=Fin 3)
   (CoordinateRing K P) (quotientCoordinate K P) E F hFE
   (quotient_eval_ne_zero_of_not_mem K P F hF) q hpole' points hpoints
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rwa [hcard] at hcount
end ActualCurve
end
end ProximityPrize.SubmissionLower.ContactSparsePoleZeroCountResearch
