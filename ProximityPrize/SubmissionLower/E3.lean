import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.O3
import ProximityPrize.SubmissionLower.X
namespace ProximityPrize.SubmissionLower.ContactRationalRegularZero6676Research
open scoped Classical BigOperators WithZero
open CoordinateBoxZeroCount ActualAffineModelPlaces
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveScalarTowers
open ActualCurveZeroCount ContactRegularZeroBudget6676Research
open ContactWeakSeparableSeparatorResearch
noncomputable section
variable (K L:Type) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
variable (A:Type) [CommRing A] [IsDomain A]
variable [Algebra K A] [Algebra A L] [IsFractionRing A L]
variable [Algebra (Polynomial K) A]
variable [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
variable [IsScalarTower (Polynomial K) A L]
local instance:DecidableEq K:=Classical.decEq K
theorem model_regular_value_eq_one (ψ:A →ₐ[K] K) (h:A) (hψ:ψ h≠0):
   (modelPlace K L A ψ).val (algebraMap A L h)=1:=by
 apply le_antisymm
 · exact actual_model_value_le_one K A L ψ h
 · apply le_of_not_gt
   intro hlt
   exact hψ ((actual_model_value_lt_one_iff K A L ψ h).mp hlt)
theorem model_regular_quotient_zero_order
   (ψ:A →ₐ[K] K) (a h:A) (k:ℕ) (ha:a≠0)
   (hzero:ψ a=0) (hregular:ψ h≠0):
   1 ≤ CommonPlaceBalance.order K L (modelPlace K L A ψ)
     (algebraMap A L a/(algebraMap A L h)^k):=by
 have hv:=model_regular_value_eq_one K L A ψ h hregular
 change 1 ≤-((modelPlace K L A ψ).val
   (algebraMap A L a/(algebraMap A L h)^k)).log
 simp only [map_div₀,map_pow,hv,one_pow,div_one]
 exact actual_model_zero_order_ge_one K A L ψ a ha hzero
theorem finite_model_regular_zeros_le_poleMass
   (a h:A) (k cost:ℕ) (ha:a≠0) (hh:h≠0)
   (hpole:∀ W:Finset (Place K L),
     (∑ v∈W,CoordinatePoleMass.poleOrder K L v
       (algebraMap A L a/(algebraMap A L h)^k)) ≤ (cost:ℤ))
   (S:Finset (A →ₐ[K] K))
   (hzero:∀ ψ∈S,ψ a=0) (hregular:∀ ψ∈S,ψ h≠0):
   S.card ≤ cost:=by
 classical
 let f:L:=algebraMap A L a/(algebraMap A L h)^k
 have hfa:algebraMap A L a≠0:=by
   simpa only [map_zero] using (IsFractionRing.injective A L).ne ha
 have hfh:algebraMap A L h≠0:=by
   simpa only [map_zero] using (IsFractionRing.injective A L).ne hh
 have hf:f≠0:=div_ne_zero hfa (pow_ne_zero k hfh)
 let U:=S.image (modelPlace K L A)
 have hU:∀ v∈U,1 ≤ CommonPlaceBalance.order K L v f:=by
   intro v hv
   obtain ⟨ψ,hψ,rfl⟩:=Finset.mem_image.mp hv
   exact model_regular_quotient_zero_order K L A ψ a h k ha
     (hzero ψ hψ) (hregular ψ hψ)
 have hcount:=CommonPlaceBalance.finite_zero_places_le_poleMass K L f hf U hU
 have hcard:U.card=S.card:=
   Finset.card_image_of_injective _ (modelPlace_injective K L A)
 have hb:(S.card:ℤ) ≤ cost:=by
   rw [←hcard]
   exact hcount.trans (hpole _)
 exact_mod_cast hb
section ActualCurve
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
theorem quotient_fraction_eq_field_eval (T:MvPolynomial (Fin 3) K):
   algebraMap (CoordinateRing K P) (CoordinateField K P) (Ideal.Quotient.mk P T)=
     MvPolynomial.aeval (coordinate K P) T:=by
 exact (aeval_coordinate_eq_quotient K P T).symm
theorem finite_regular_zero_bound_of_separator
   (base:SeparableLiteralCoordinate P)
   (H F:MvPolynomial (Fin 3) K) (k cost:ℕ) (hF:F∉P) (hH:H∉P)
   (hpole:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P base.index base.transcendental
     ∀ W:Finset (Place K (CoordinateField K P)),
       (∑ v∈W,CoordinatePoleMass.poleOrder K (CoordinateField K P) v
         (MvPolynomial.aeval (coordinate K P) F/
           (MvPolynomial.aeval (coordinate K P) H)^k)) ≤ (cost:ℤ)):
   FiniteRegularZeroSetBound P H F cost:=by
 classical
 let i₀:=base.index
 let hi₀:=base.transcendental
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
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=base.finite
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=base.separable
 intro S hSP hSH hSF
 let liftPoint:{v:Fin 3 → K//v∈S} → (CoordinateRing K P →ₐ[K] K):=
   fun v↦pointHom K P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w hvw
   apply Subtype.ext
   exact congrArg (fun z:PointOn K P↦z.val) (pointHom_injective K P hvw)
 let points:=S.attach.image liftPoint
 have hzero:∀ ψ∈points,ψ (Ideal.Quotient.mk P F)=0:=by
   intro ψ hψ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hψ
   exact hSF v.1 v.2
 have hregular:∀ ψ∈points,ψ (Ideal.Quotient.mk P H)≠0:=by
   intro ψ hψ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hψ
   exact hSH v.1 v.2
 have hFq:Ideal.Quotient.mk P F≠0:=
   fun hz↦hF (Ideal.Quotient.eq_zero_iff_mem.mp hz)
 have hHq:Ideal.Quotient.mk P H≠0:=
   fun hz↦hH (Ideal.Quotient.eq_zero_iff_mem.mp hz)
 have hcount:=finite_model_regular_zeros_le_poleMass K (CoordinateField K P)
   (CoordinateRing K P) (Ideal.Quotient.mk P F) (Ideal.Quotient.mk P H)
   k cost hFq hHq (by simpa only [quotient_fraction_eq_field_eval] using hpole)
   points hzero hregular
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rwa [hcard] at hcount
end ActualCurve
end
end ProximityPrize.SubmissionLower.ContactRationalRegularZero6676Research
