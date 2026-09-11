import ProximityPrize.SubmissionLower.Part.F005_03
section Compact_PackedLegacyCore2
section PackedLegacy_GA
namespace ProximityPrize.SubmissionLower.RCN296
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN295 RCN344 RCN002 RCN005 RCN006 RCN007
noncomputable section
variable {K L σ:Type} [Field K] [Field L] [Fintype σ]
 [Algebra K L] [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L]
 [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place K L):=Classical.decEq _
variable (A:Type) [CommRing A] [IsDomain A]
 [Algebra K A] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) A L]
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
end ProximityPrize.SubmissionLower.RCN296
end PackedLegacy_GA

/-! Packed from ProximityPrize.SubmissionLower.O4. -/
section PackedLegacy_O4
namespace ProximityPrize.SubmissionLower.RCN273
open scoped Classical BigOperators WithZero
open RCN002 RCN007 RCN264 RCN243 RCN295 RCN296 RCN272 RCN344
noncomputable section
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
structure ResidualPoleComponentBudget
   (G T H:MvPolynomial (Fin 3) Ω)
   (E:Finset (Fin 3 →₀ ℕ)) (separator:Fin 3) (wholeCost:ℕ) where
 cost:RegularComponent Ω G T H → ℕ
 separator_transcendental:∀ C:RegularComponent Ω G T H,
   Transcendental Ω (coordinate Ω C.1 separator)
 pole_le:∀ C:RegularComponent Ω G T H,
   let htr:=separator_transcendental C
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     RCN005.rationalBaseAlgebra Ω C.1 separator htr
   ∀ W:Finset (Place Ω (CoordinateField Ω C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1) E) ≤
       (cost C:ℤ)
 sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCost
def ResidualPoleComponentBudget.toResidualComponentBudget
   {G T H:MvPolynomial (Fin 3) Ω}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3} {wholeCost:ℕ}
   (B:ResidualPoleComponentBudget G T H E separator wholeCost)
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1):
   ResidualComponentBudget G T H (fun A↦A.support ⊆ E) wholeCost where
 cost:=B.cost
 zero_le:=by
   intro C A hAE hproper points hpointsP hpointsA
   exact finite_zero_points_le_exponentSet_of_separator C.1 (hproj C)
     separator (B.separator_transcendental C) E (B.cost C) (B.pole_le C)
     A hAE hproper points hpointsP hpointsA
 sum_cost_le:=B.sum_cost_le
end
end ProximityPrize.SubmissionLower.RCN273
end PackedLegacy_O4

/-! Packed from ProximityPrize.SubmissionLower.GU. -/
section PackedLegacy_GU
namespace ProximityPrize.SubmissionLower.RCN323
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN295 RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN273
noncomputable section
variable {K L σ:Type} [Field K] [Field L] [Fintype σ]
 [Algebra K L] [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L]
 [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place K L):=Classical.decEq _
theorem exponentSetPoleWeight_nonneg
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)):
   0 ≤ exponentSetPoleWeight v x E:=by
 unfold exponentSetPoleWeight
 exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
theorem support_sum_le_principal_poleMass_of_exact
   (x:σ → L) (E:Finset (σ →₀ ℕ)) (b:L) (hb:b≠0)
   (hexact:∀ v:Place K L,
     RCN187.poleOrder v.val b=
       exponentSetPoleWeight v.val x E)
   (W:Finset (Place K L)):
   (∑ v∈W,exponentSetPoleWeight v.val x E) ≤
     ∑ v∈RCN026.placesFor K L b hb,
       RCN346.poleOrder K L v b:=by
 classical
 let P:=RCN026.placesFor K L b hb
 have hout:∀ v∈W,v∉P →
     exponentSetPoleWeight v.val x E=0:=by
   intro v hvW hvP
   have hpole:RCN187.poleOrder v.val b=0:=by
     by_contra hpole
     apply hvP
     apply RCN026.placesFor_covers K L b hb v
     unfold RCN026.order RCN187.poleOrder at*
     omega
   rw [←hexact v,hpole]
 calc
   (∑ v∈W,exponentSetPoleWeight v.val x E)=
       ∑ v∈W ∩ P,exponentSetPoleWeight v.val x E:=by
     symm
     apply Finset.sum_subset Finset.inter_subset_left
     intro v hvW hvnot
     apply hout v hvW
     intro hvP
     exact hvnot (Finset.mem_inter.mpr ⟨hvW,hvP⟩)
   _ ≤ ∑ v∈P,exponentSetPoleWeight v.val x E:=by
     apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
     intro v _ _
     exact exponentSetPoleWeight_nonneg v.val x E
   _=∑ v∈P,RCN346.poleOrder K L v b:=by
     apply Finset.sum_congr rfl
     intro v _
     exact (hexact v).symm
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
theorem coordinate_eval_ne_zero_of_not_mem
   (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
   (F:MvPolynomial (Fin 3) Ω) (hF:F∉P):
   MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateField Ω P))
     (coordinate Ω P) F≠0:=by
 intro hz
 apply hF
 rw [←aeval_coordinate_ker Ω P]
 exact hz
structure GenericSparseBKKWitness
   (G T H:MvPolynomial (Fin 3) Ω)
   (E:Finset (Fin 3 →₀ ℕ)) (separator:Fin 3) (wholeCost:ℕ)
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1) where
 polynomial:MvPolynomial (Fin 3) Ω
 support_subset:polynomial.support ⊆ E
 proper:∀ C:RegularComponent Ω G T H,polynomial∉C.1
 cost:RegularComponent Ω G T H → ℕ
 exact_pole:∀ C:RegularComponent Ω G T H,
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
     quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
     polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     rationalBaseAlgebra Ω C.1 separator htr
   letI:=quotientBaseScalarTower Ω C.1 separator
   letI:=polynomialBaseScalarTower Ω C.1 separator
   letI:=quotientFractionScalarTower Ω C.1 separator
   letI:=polynomialRationalScalarTower Ω C.1 separator htr
   letI:=rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).2
   ∀ v:Place Ω (CoordinateField Ω C.1),
     RCN187.poleOrder v.val
         (MvPolynomial.eval₂Hom
           (algebraMap Ω (CoordinateField Ω C.1))
           (coordinate Ω C.1) polynomial)=
       exponentSetPoleWeight v.val (coordinate Ω C.1) E
 cycle_le:∀ C:RegularComponent Ω G T H,
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
     quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
     polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     rationalBaseAlgebra Ω C.1 separator htr
   letI:=quotientBaseScalarTower Ω C.1 separator
   letI:=polynomialBaseScalarTower Ω C.1 separator
   letI:=quotientFractionScalarTower Ω C.1 separator
   letI:=polynomialRationalScalarTower Ω C.1 separator htr
   letI:=rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).2
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) polynomial
   let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem C.1 polynomial (proper C)
   (∑ v∈RCN026.placesFor Ω (CoordinateField Ω C.1) b hb,
     RCN346.poleOrder Ω (CoordinateField Ω C.1) v b) ≤
       (cost C:ℤ)
 sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCost
def GenericSparseBKKWitness.toResidualPoleComponentBudget
   {G T H:MvPolynomial (Fin 3) Ω}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3} {wholeCost:ℕ}
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   (B:GenericSparseBKKWitness G T H E separator wholeCost
     hseparator hproj):
   ResidualPoleComponentBudget G T H E separator wholeCost where
 cost:=B.cost
 separator_transcendental:=hseparator
 pole_le:=by
   intro C
   dsimp only
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
     quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
     polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     rationalBaseAlgebra Ω C.1 separator htr
   letI:=quotientBaseScalarTower Ω C.1 separator
   letI:=polynomialBaseScalarTower Ω C.1 separator
   letI:=quotientFractionScalarTower Ω C.1 separator
   letI:=polynomialRationalScalarTower Ω C.1 separator htr
   letI:=rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).2
   intro W
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) B.polynomial
   have hb:b≠0:=
     coordinate_eval_ne_zero_of_not_mem C.1 B.polynomial (B.proper C)
   exact (support_sum_le_principal_poleMass_of_exact
     (K:=Ω) (L:=CoordinateField Ω C.1)
     (coordinate Ω C.1) E b hb (B.exact_pole C) W).trans
       (B.cycle_le C)
 sum_cost_le:=B.sum_cost_le
end
end ProximityPrize.SubmissionLower.RCN323
end PackedLegacy_GU

/-! Packed from ProximityPrize.SubmissionLower.B4. -/
section PackedLegacy_B4
namespace ProximityPrize.SubmissionLower.RCN075
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN187 RCN133 RCN184 RCN295 RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN273 RCN323
noncomputable section
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
def componentRelevantPlaces
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (C:RegularComponent Ω G T H):
   Finset (Place Ω (CoordinateField Ω C.1)):=by
 classical
 let htr:=hseparator C
 letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
   quotientPolynomialAlgebra Ω C.1 separator
 letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
   polynomialBaseAlgebra Ω C.1 separator
 letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
   rationalBaseAlgebra Ω C.1 separator htr
 letI:=quotientBaseScalarTower Ω C.1 separator
 letI:=polynomialBaseScalarTower Ω C.1 separator
 letI:=quotientFractionScalarTower Ω C.1 separator
 letI:=polynomialRationalScalarTower Ω C.1 separator htr
 letI:=rationalBaseScalarTower Ω C.1 separator htr
 letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
   (hproj C separator htr).1
 letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
   (hproj C separator htr).2
 exact Finset.univ.biUnion (fun i:Fin 3↦
   if hi:coordinate Ω C.1 i≠0 then
     RCN026.placesFor Ω (CoordinateField Ω C.1)
       (coordinate Ω C.1 i) hi
   else ∅)
theorem coordinate_poleOrder_eq_zero_of_not_mem_relevant
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (C:RegularComponent Ω G T H)
   (v:Place Ω (CoordinateField Ω C.1))
   (hv:v∉componentRelevantPlaces hseparator hproj C) (i:Fin 3):
   poleOrder v.val (coordinate Ω C.1 i)=0:=by
 classical
 let htr:=hseparator C
 letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
   quotientPolynomialAlgebra Ω C.1 separator
 letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
   polynomialBaseAlgebra Ω C.1 separator
 letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
   rationalBaseAlgebra Ω C.1 separator htr
 letI:=quotientBaseScalarTower Ω C.1 separator
 letI:=polynomialBaseScalarTower Ω C.1 separator
 letI:=quotientFractionScalarTower Ω C.1 separator
 letI:=polynomialRationalScalarTower Ω C.1 separator htr
 letI:=rationalBaseScalarTower Ω C.1 separator htr
 letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
   (hproj C separator htr).1
 letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
   (hproj C separator htr).2
 by_cases hi:coordinate Ω C.1 i=0
 · simp [hi,poleOrder]
 · have hnot:v∉RCN026.placesFor Ω
       (CoordinateField Ω C.1) (coordinate Ω C.1 i) hi:=by
     intro hmem
     apply hv
     unfold componentRelevantPlaces
     apply Finset.mem_biUnion.mpr
     exact ⟨i,Finset.mem_univ _,by simp [hi,hmem]⟩
   have horder:RCN026.order Ω (CoordinateField Ω C.1) v
       (coordinate Ω C.1 i)=0:=by
     by_contra hne
     exact hnot (RCN026.placesFor_covers Ω
       (CoordinateField Ω C.1) (coordinate Ω C.1 i) hi v hne)
   unfold RCN026.order at horder
   unfold poleOrder
   have hlog:(v.val (coordinate Ω C.1 i)).log=0:=by omega
   rw [hlog]
   simp
theorem exponentSetPoleWeight_eq_zero_of_not_mem_relevant
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (E:Finset (Fin 3 →₀ ℕ))
   (C:RegularComponent Ω G T H)
   (v:Place Ω (CoordinateField Ω C.1))
   (hv:v∉componentRelevantPlaces hseparator hproj C):
   exponentSetPoleWeight v.val (coordinate Ω C.1) E=0:=by
 classical
 have hcoord:∀ i:Fin 3,
     poleOrder v.val (coordinate Ω C.1 i)=0:=
   coordinate_poleOrder_eq_zero_of_not_mem_relevant
     hseparator hproj C v hv
 unfold exponentSetPoleWeight exponentPoleWeight
 apply le_antisymm
 · apply Finset.max'_le
   intro z hz
   obtain rfl | hz:=Finset.mem_insert.mp hz
   · exact le_rfl
   · obtain ⟨d,_,rfl⟩:=Finset.mem_image.mp hz
     simp [hcoord]
 · exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
abbrev RelevantPlaceIndex
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1):=
 Σ C:RegularComponent Ω G T H,
   {v:Place Ω (CoordinateField Ω C.1)//
     v∈componentRelevantPlaces hseparator hproj C}
abbrev DependentGenericityIndex
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1):=
 RegularComponent Ω G T H ⊕ RelevantPlaceIndex hseparator hproj
def dependentBadSubmodule
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (E:Finset (Fin 3 →₀ ℕ)):
   DependentGenericityIndex hseparator hproj → Submodule Ω (E → Ω)
 | Sum.inl C => LinearMap.ker (coefficientEvaluation (coordinate Ω C.1) E)
 | Sum.inr ⟨C,v⟩ => cancellationSubmodule v.1.val
     (fun a↦constant_value_le_one Ω (CoordinateField Ω C.1) v.1 a)
     (coordinate Ω C.1) E
theorem dependentBadSubmodule_ne_top
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (E:Finset (Fin 3 →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
   ∀ j:DependentGenericityIndex hseparator hproj,
     dependentBadSubmodule hseparator hproj E j≠⊤:=by
 classical
 intro j
 rcases j with C | ⟨C,v⟩
 · intro htop
   let e0:E:=⟨0,hzero⟩
   let c0:E → Ω:=deltaCoefficient E e0
   have hc0:c0∈dependentBadSubmodule hseparator hproj E (Sum.inl C):=by
     rw [htop]
     trivial
   have hzeroeval:coefficientEvaluation (coordinate Ω C.1) E c0=0:=by
     exact LinearMap.mem_ker.mp hc0
   have honeeval:coefficientEvaluation (coordinate Ω C.1) E c0=1:=by
     rw [coefficientEvaluation,LinearMap.coe_mk,AddHom.coe_mk,
       polynomialOfSupport_deltaCoefficient]
     simp [e0]
   rw [honeeval] at hzeroeval
   exact one_ne_zero hzeroeval
 · obtain ⟨c,hc⟩:=
     exists_exact_support_evaluation_of_downwardClosed
       (K:=Ω) (L:=CoordinateField Ω C.1) (σ:=Fin 3)
       v.1.val (coordinate Ω C.1) E hdown hzero
   exact cancellationSubmodule_ne_top_of_exact v.1.val
     (fun a↦constant_value_le_one Ω (CoordinateField Ω C.1) v.1 a)
     (coordinate Ω C.1) E c hc
structure GenericExactPolePolynomial
   (G T H:MvPolynomial (Fin 3) Ω)
   (E:Finset (Fin 3 →₀ ℕ)) (separator:Fin 3)
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1) where
 polynomial:MvPolynomial (Fin 3) Ω
 support_subset:polynomial.support ⊆ E
 proper:∀ C:RegularComponent Ω G T H,polynomial∉C.1
 exact_pole:∀ C:RegularComponent Ω G T H,
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
     quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
     polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     rationalBaseAlgebra Ω C.1 separator htr
   letI:=quotientBaseScalarTower Ω C.1 separator
   letI:=polynomialBaseScalarTower Ω C.1 separator
   letI:=quotientFractionScalarTower Ω C.1 separator
   letI:=polynomialRationalScalarTower Ω C.1 separator htr
   letI:=rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).2
   ∀ v:Place Ω (CoordinateField Ω C.1),
     poleOrder v.val
         (MvPolynomial.eval₂Hom
           (algebraMap Ω (CoordinateField Ω C.1))
           (coordinate Ω C.1) polynomial)=
       exponentSetPoleWeight v.val (coordinate Ω C.1) E
theorem exists_genericExactPolePolynomial
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (E:Finset (Fin 3 →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
   Nonempty (GenericExactPolePolynomial G T H E separator
     hseparator hproj):=by
 classical
 let bad:=dependentBadSubmodule hseparator hproj E
 obtain ⟨c,hc⟩:=exists_avoiding_finite_proper_submodules bad
   (dependentBadSubmodule_ne_top hseparator hproj E hdown hzero)
 let B:=polynomialOfSupport E c
 have hsupport:B.support ⊆ E:=support_polynomialOfSupport_subset E c
 have hproper:∀ C:RegularComponent Ω G T H,B∉C.1:=by
   intro C hmem
   apply hc (Sum.inl C)
   change c∈LinearMap.ker
     (coefficientEvaluation (coordinate Ω C.1) E)
   rw [LinearMap.mem_ker]
   have hker:B∈RingHom.ker
       (MvPolynomial.aeval (coordinate Ω C.1)).toRingHom:=by
     rw [aeval_coordinate_ker]
     exact hmem
   have hz:=RingHom.mem_ker.mp hker
   change MvPolynomial.aeval (coordinate Ω C.1) B=0 at hz
   rw [MvPolynomial.aeval_eq_eval₂Hom] at hz
   change MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) B=0
   exact hz
 refine ⟨⟨B,hsupport,hproper,?_⟩⟩
 intro C
 dsimp only
 let htr:=hseparator C
 letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
   quotientPolynomialAlgebra Ω C.1 separator
 letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
   polynomialBaseAlgebra Ω C.1 separator
 letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
   rationalBaseAlgebra Ω C.1 separator htr
 letI:=quotientBaseScalarTower Ω C.1 separator
 letI:=polynomialBaseScalarTower Ω C.1 separator
 letI:=quotientFractionScalarTower Ω C.1 separator
 letI:=polynomialRationalScalarTower Ω C.1 separator htr
 letI:=rationalBaseScalarTower Ω C.1 separator htr
 letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
   (hproj C separator htr).1
 letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
   (hproj C separator htr).2
 intro v
 by_cases hv:v∈componentRelevantPlaces hseparator hproj C
 · have havoid:=hc (Sum.inr ⟨C,⟨v,hv⟩⟩)
   change ¬v.val (coefficientEvaluation (coordinate Ω C.1) E c) <
     WithZero.exp (exponentSetPoleWeight v.val (coordinate Ω C.1) E) at havoid
   have hlower:WithZero.exp
       (exponentSetPoleWeight v.val (coordinate Ω C.1) E) ≤
       v.val (coefficientEvaluation (coordinate Ω C.1) E c):=
     le_of_not_gt havoid
   have hupper:v.val (coefficientEvaluation (coordinate Ω C.1) E c) ≤
       WithZero.exp
         (exponentSetPoleWeight v.val (coordinate Ω C.1) E):=
     valuation_eval_le_exp_exponentSet v.val (algebraMap Ω _)
       (fun a↦constant_value_le_one Ω (CoordinateField Ω C.1) v a)
       (coordinate Ω C.1) E B hsupport
   exact poleOrder_eq_of_valuation_eq_exp v.val _ _
     (RCN184.exponentSetPoleWeight_nonneg
       v.val (coordinate Ω C.1) E)
     (le_antisymm hupper hlower)
 · have hweight:exponentSetPoleWeight v.val (coordinate Ω C.1) E=0:=
     exponentSetPoleWeight_eq_zero_of_not_mem_relevant
       hseparator hproj E C v hv
   have hle:poleOrder v.val
       (MvPolynomial.eval₂Hom
         (algebraMap Ω (CoordinateField Ω C.1))
         (coordinate Ω C.1) B) ≤
       exponentSetPoleWeight v.val (coordinate Ω C.1) E:=
     (poleOrder_eval_le_support v.val (algebraMap Ω _)
       (fun a↦constant_value_le_one Ω (CoordinateField Ω C.1) v a)
       (coordinate Ω C.1) B).trans
     (supportPoleWeight_le_exponentSetPoleWeight v.val
       (coordinate Ω C.1) B E hsupport)
   rw [hweight] at hle ⊢
   exact le_antisymm hle (by unfold poleOrder;exact le_max_left _ _)
def GenericExactPolePolynomial.toGenericSparseBKKWitness
   {G T H:MvPolynomial (Fin 3) Ω}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3} {wholeCost:ℕ}
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   (B:GenericExactPolePolynomial G T H E separator hseparator hproj)
   (cost:RegularComponent Ω G T H → ℕ)
   (cycle_le:∀ C:RegularComponent Ω G T H,
     let htr:=hseparator C
     letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
       quotientPolynomialAlgebra Ω C.1 separator
     letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
       polynomialBaseAlgebra Ω C.1 separator
     letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
       rationalBaseAlgebra Ω C.1 separator htr
     letI:=quotientBaseScalarTower Ω C.1 separator
     letI:=polynomialBaseScalarTower Ω C.1 separator
     letI:=quotientFractionScalarTower Ω C.1 separator
     letI:=polynomialRationalScalarTower Ω C.1 separator htr
     letI:=rationalBaseScalarTower Ω C.1 separator htr
     letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
       (hproj C separator htr).1
     letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
       (hproj C separator htr).2
     let b:=MvPolynomial.eval₂Hom
       (algebraMap Ω (CoordinateField Ω C.1))
       (coordinate Ω C.1) B.polynomial
     let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem
       C.1 B.polynomial (B.proper C)
     (∑ v∈RCN026.placesFor Ω
         (CoordinateField Ω C.1) b hb,
       RCN346.poleOrder Ω (CoordinateField Ω C.1) v b) ≤
         (cost C:ℤ))
   (sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCost):
   GenericSparseBKKWitness G T H E separator wholeCost hseparator hproj where
 polynomial:=B.polynomial
 support_subset:=B.support_subset
 proper:=B.proper
 cost:=cost
 exact_pole:=B.exact_pole
 cycle_le:=cycle_le
 sum_cost_le:=sum_cost_le
end
end ProximityPrize.SubmissionLower.RCN075
end PackedLegacy_B4

/-! Packed from ProximityPrize.SubmissionLower.DO. -/

/-! Packed from ProximityPrize.SubmissionLower.X. -/
section PackedLegacy_X
namespace ProximityPrize.SubmissionLower.RCN341
open scoped Classical
open RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN295 RCN296
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
structure SeparableLiteralCoordinate
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime] where
 index:Fin 3
 transcendental:Transcendental Omega (coordinate Omega P index)
 finite:
   letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
     rationalBaseAlgebra Omega P index transcendental
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)
 separable:
   letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
     rationalBaseAlgebra Omega P index transcendental
   Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P)
theorem rationalBaseEmbedding_surjective_of_other_coordinates_algebraic
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (hS:Transcendental Omega (coordinate Omega P 1))
   (hY:IsAlgebraic Omega (coordinate Omega P 0))
   (hZ:IsAlgebraic Omega (coordinate Omega P 2)):
   Function.Surjective (rationalBaseEmbedding Omega P 1 hS):=by
 letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseAlgebra Omega P 1 hS
 letI:IsScalarTower Omega (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseScalarTower Omega P 1 hS
 obtain ⟨y,hy⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 0 hY
 obtain ⟨z,hz⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 2 hZ
 have hYbot:coordinate Omega P 0∈
     (⊥:IntermediateField (RatFunc Omega) (CoordinateField Omega P)):=by
   rw [IntermediateField.mem_bot]
   refine ⟨algebraMap Omega (RatFunc Omega) y,?_⟩
   rw [←IsScalarTower.algebraMap_apply Omega (RatFunc Omega)
     (CoordinateField Omega P)]
   exact hy
 have hZbot:coordinate Omega P 2∈
     (⊥:IntermediateField (RatFunc Omega) (CoordinateField Omega P)):=by
   rw [IntermediateField.mem_bot]
   refine ⟨algebraMap Omega (RatFunc Omega) z,?_⟩
   rw [←IsScalarTower.algebraMap_apply Omega (RatFunc Omega)
     (CoordinateField Omega P)]
   exact hz
 have hadjoinBot:IntermediateField.adjoin (RatFunc Omega)
     ({coordinate Omega P 2,coordinate Omega P 0}:
       Set (CoordinateField Omega P))=⊥:=by
   rw [IntermediateField.adjoin_eq_bot_iff]
   intro x hx
   rcases hx with (rfl | hx)
   · exact hZbot
   · simpa using hx ▸ hYbot
 have hadjoinTop:IntermediateField.adjoin (RatFunc Omega)
     ({coordinate Omega P 2,coordinate Omega P 0}:
       Set (CoordinateField Omega P))=⊤:=
   adjoin_two_coordinates_over_ratFunc_eq_top Omega P 1 2 0 hS
     (by intro i;fin_cases i <;> simp)
 have htopbot:
     (⊤:IntermediateField (RatFunc Omega) (CoordinateField Omega P))=⊥:=
   hadjoinTop.symm.trans hadjoinBot
 intro x
 obtain ⟨a,ha⟩:=
   IntermediateField.mem_bot.mp (by rw [←htopbot];trivial:
     x∈(⊥:IntermediateField (RatFunc Omega) (CoordinateField Omega P)))
 refine ⟨a,?_⟩
 exact ha
theorem finite_separable_at_S_of_other_coordinates_algebraic
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (hS:Transcendental Omega (coordinate Omega P 1))
   (hY:IsAlgebraic Omega (coordinate Omega P 0))
   (hZ:IsAlgebraic Omega (coordinate Omega P 2)):
   letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
     rationalBaseAlgebra Omega P 1 hS
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=by
 letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseAlgebra Omega P 1 hS
 have hsurj:Function.Surjective
     (algebraMap (RatFunc Omega) (CoordinateField Omega P)):=by
   have hs:=
     rationalBaseEmbedding_surjective_of_other_coordinates_algebraic P hS hY hZ
   exact hs
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=
   FiniteDimensional.of_surjective
     (Algebra.linearMap (RatFunc Omega) (CoordinateField Omega P)) hsurj
 have hsep:Algebra.IsSeparable
     (RatFunc Omega) (CoordinateField Omega P):=by
   constructor
   intro x
   obtain ⟨a,rfl⟩:=hsurj x
   exact isSeparable_algebraMap a
 exact ⟨inferInstance,hsep⟩
theorem finite_zero_points_le_exponentSet_of_literalCoordinate
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (D:SeparableLiteralCoordinate P)
   (E:Finset (Fin 3 →₀ ℕ)) (q:ℕ)
   (hpole:
     letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
       rationalBaseAlgebra Omega P D.index D.transcendental
     ∀ W:Finset (Place Omega (CoordinateField Omega P)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega P) E) ≤
         (q:ℤ))
   (F:MvPolynomial (Fin 3) Omega) (hFE:F.support ⊆ E) (hF:F∉P)
   (S:Finset (Fin 3 → Omega))
   (hSP:∀ v∈S,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hSF:∀ v∈S,MvPolynomial.aeval v F=0):
   S.card ≤ q:=by
 classical
 let i0:=D.index
 let htr:=D.transcendental
 letI:Algebra (Polynomial Omega) (CoordinateRing Omega P):=
   quotientPolynomialAlgebra Omega P i0
 letI:Algebra (Polynomial Omega) (CoordinateField Omega P):=
   polynomialBaseAlgebra Omega P i0
 letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseAlgebra Omega P i0 htr
 letI:=quotientBaseScalarTower Omega P i0
 letI:=polynomialBaseScalarTower Omega P i0
 letI:=quotientFractionScalarTower Omega P i0
 letI:=polynomialRationalScalarTower Omega P i0 htr
 letI:=rationalBaseScalarTower Omega P i0 htr
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=
   D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=
   D.separable
 let liftPoint:{v:Fin 3 → Omega//v∈S} →
     (CoordinateRing Omega P →ₐ[Omega] Omega):=
   fun v↦pointHom Omega P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w hvw
   have h:=pointHom_injective Omega P hvw
   apply Subtype.ext
   exact congrArg (fun z:PointOn Omega P↦z.val) h
 let points:=S.attach.image liftPoint
 have hpoints:∀ psi∈points,psi (MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateRing Omega P))
     (quotientCoordinate Omega P) F)=0:=by
   intro psi hpsi
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hpsi
   rw [quotient_eval_eq_mk]
   exact hSF v.1 v.2
 have hpole':∀ W:Finset (Place Omega (CoordinateField Omega P)),
     (∑ v∈W,exponentSetPoleWeight v.val
       (fun i↦algebraMap (CoordinateRing Omega P) (CoordinateField Omega P)
         (quotientCoordinate Omega P i)) E) ≤ (q:ℤ):=by
   intro W
   simpa only [quotientCoordinate_fraction] using hpole W
 have hcount:=finite_model_zero_points_le_exponentSet
   (K:=Omega) (L:=CoordinateField Omega P) (σ:=Fin 3)
   (CoordinateRing Omega P) (quotientCoordinate Omega P) E F hFE
   (quotient_eval_ne_zero_of_not_mem Omega P F hF) q hpole' points hpoints
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rwa [hcard] at hcount
theorem exists_separableLiteralCoordinate_of_YZ_gates
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hY:∀ h:Transcendental Omega (coordinate Omega P 0),
     letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
       rationalBaseAlgebra Omega P 0 h
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P))
   (hZ:∀ h:Transcendental Omega (coordinate Omega P 2),
     letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
       rationalBaseAlgebra Omega P 2 h
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P)):
   Nonempty (SeparableLiteralCoordinate P):=by
 by_cases hy:Transcendental Omega (coordinate Omega P 0)
 · exact ⟨⟨0,hy,(hY hy).1,(hY hy).2⟩⟩
 by_cases hz:Transcendental Omega (coordinate Omega P 2)
 · exact ⟨⟨2,hz,(hZ hz).1,(hZ hz).2⟩⟩
 have hyalg:IsAlgebraic Omega (coordinate Omega P 0):=not_not.mp hy
 have hzalg:IsAlgebraic Omega (coordinate Omega P 2):=not_not.mp hz
 obtain ⟨i,hi⟩:=
   exists_transcendental_coordinate_of_ne_point_kernel Omega P hnonpoint
 have hi1:i=(1:Fin 3):=by
   fin_cases i <;> simp_all
 subst i
 have hs:=finite_separable_at_S_of_other_coordinates_algebraic
   P hi hyalg hzalg
 exact ⟨⟨1,hi,hs.1,hs.2⟩⟩
end
end ProximityPrize.SubmissionLower.RCN341
end PackedLegacy_X

/-! Packed from ProximityPrize.SubmissionLower.P. -/
section PackedLegacy_P
namespace ProximityPrize.SubmissionLower.RCN114
open scoped Classical BigOperators WithZero
open RCN187 RCN295 RCN095
noncomputable section
theorem exponent_weight_le_flag_bound
   (p:FlagDegree) (d:Fin 3 →₀ ℕ) (q:Fin 3 → ℤ)
   (hd:InFlag p d) (hq:∀ i,0 ≤ q i):
   (∑ i,(d i:ℤ)*q i) ≤
     (p.zOnly:ℤ)*q 2+
       (p.yz:ℤ)*max (q 0) (q 2)+
       (p.all:ℤ)*max (q 1) (max (q 0) (q 2)):=by
 let m₁:ℤ:=max (q 0) (q 2)
 let m₂:ℤ:=max (q 1) m₁
 have hq0m₁:q 0 ≤ m₁:=le_max_left _ _
 have hq2m₁:q 2 ≤ m₁:=le_max_right _ _
 have hq1m₂:q 1 ≤ m₂:=le_max_left _ _
 have hm₁m₂:m₁ ≤ m₂:=le_max_right _ _
 have hreplace0:(d 0:ℤ)*q 0 ≤ (d 0:ℤ)*m₁:=
   mul_le_mul_of_nonneg_left hq0m₁ (by positivity)
 have hreplace1:(d 1:ℤ)*q 1 ≤ (d 1:ℤ)*m₂:=
   mul_le_mul_of_nonneg_left hq1m₂ (by positivity)
 have htotal:((d 0+d 1+d 2:ℕ):ℤ) ≤
     ((p.zOnly+p.yz+p.all:ℕ):ℤ):=by
   exact_mod_cast hd.2.2
 have hys:((d 0+d 1:ℕ):ℤ) ≤
     ((p.yz+p.all:ℕ):ℤ):=by
   exact_mod_cast hd.2.1
 have hs:(d 1:ℤ) ≤ (p.all:ℤ):=by
   exact_mod_cast hd.1
 have hdiff₁:0 ≤ m₁-q 2:=sub_nonneg.mpr hq2m₁
 have hdiff₂:0 ≤ m₂-m₁:=sub_nonneg.mpr hm₁m₂
 have hcap:
     ((d 0+d 1+d 2:ℕ):ℤ)*q 2+
         ((d 0+d 1:ℕ):ℤ)*(m₁-q 2)+
         (d 1:ℤ)*(m₂-m₁) ≤
       ((p.zOnly+p.yz+p.all:ℕ):ℤ)*q 2+
         ((p.yz+p.all:ℕ):ℤ)*(m₁-q 2)+
         (p.all:ℤ)*(m₂-m₁):=by
   exact add_le_add
     (add_le_add (mul_le_mul_of_nonneg_right htotal (hq 2))
       (mul_le_mul_of_nonneg_right hys hdiff₁))
     (mul_le_mul_of_nonneg_right hs hdiff₂)
 calc
   (∑ i,(d i:ℤ)*q i)=
       (d 0:ℤ)*q 0+(d 1:ℤ)*q 1+(d 2:ℤ)*q 2:=by
     simp [Fin.sum_univ_three]
   _ ≤ (d 0:ℤ)*m₁+(d 1:ℤ)*m₂+(d 2:ℤ)*q 2:=
     add_le_add (add_le_add hreplace0 hreplace1) le_rfl
   _=((d 0+d 1+d 2:ℕ):ℤ)*q 2+
         ((d 0+d 1:ℕ):ℤ)*(m₁-q 2)+
         (d 1:ℤ)*(m₂-m₁):=by
     push_cast
     ring
   _ ≤ ((p.zOnly+p.yz+p.all:ℕ):ℤ)*q 2+
         ((p.yz+p.all:ℕ):ℤ)*(m₁-q 2)+
         (p.all:ℤ)*(m₂-m₁):=hcap
   _=(p.zOnly:ℤ)*q 2+(p.yz:ℤ)*m₁+
         (p.all:ℤ)*m₂:=by
     push_cast
     ring
   _=_:=rfl
variable {L:Type*} [Field L]
theorem exponentSetPoleWeight_flagSupport_le
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L)
   (p:FlagDegree):
   exponentSetPoleWeight v x (flagSupport p) ≤
     (p.zOnly:ℤ)*poleOrder v (x 2)+
       (p.yz:ℤ)*max (poleOrder v (x 0)) (poleOrder v (x 2))+
       (p.all:ℤ)*max (poleOrder v (x 1))
         (max (poleOrder v (x 0)) (poleOrder v (x 2))):=by
 classical
 unfold exponentSetPoleWeight
 apply Finset.max'_le
 intro z hz
 obtain rfl | hz:=Finset.mem_insert.mp hz
 · have h0:∀ i:Fin 3,0 ≤ poleOrder v (x i):=fun i↦by
     unfold poleOrder
     exact le_max_left _ _
   exact add_nonneg
     (add_nonneg (mul_nonneg (by positivity) (h0 2))
       (mul_nonneg (by positivity)
         ((h0 0).trans (le_max_left _ _))))
     (mul_nonneg (by positivity)
       ((h0 1).trans (le_max_left _ _)))
 · obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hz
   exact exponent_weight_le_flag_bound p d (fun i↦poleOrder v (x i))
     ((mem_flagSupport_iff p d).mp hd)
     (fun i↦by unfold poleOrder;exact le_max_left _ _)
theorem exponentPoleWeight_single
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L)
   (i:Fin 3):
   exponentPoleWeight v x (Finsupp.single i 1)=poleOrder v (x i):=by
 classical
 fin_cases i <;> simp [exponentPoleWeight,Fin.sum_univ_three]
private theorem poleOrder_le_support_of_mem
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L)
   (p:FlagDegree) (i:Fin 3)
   (hi:Finsupp.single i 1∈flagSupport p):
   poleOrder v (x i) ≤ exponentSetPoleWeight v x (flagSupport p):=by
 rw [←exponentPoleWeight_single v x i]
 unfold exponentSetPoleWeight
 apply Finset.le_max'
 exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
   ⟨Finsupp.single i 1,hi,rfl⟩)
theorem exponentSetPoleWeight_unitZ
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L):
   exponentSetPoleWeight v x (flagSupport unitZFlag)=poleOrder v (x 2):=by
 apply le_antisymm
 · simpa [unitZFlag] using exponentSetPoleWeight_flagSupport_le v x unitZFlag
 · apply poleOrder_le_support_of_mem v x unitZFlag 2
   rw [mem_flagSupport_iff]
   simp [InFlag,unitZFlag]
theorem exponentSetPoleWeight_unitYZ
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L):
   exponentSetPoleWeight v x (flagSupport unitYZFlag)=
     max (poleOrder v (x 0)) (poleOrder v (x 2)):=by
 apply le_antisymm
 · simpa [unitYZFlag] using exponentSetPoleWeight_flagSupport_le v x unitYZFlag
 · apply max_le
   · apply poleOrder_le_support_of_mem v x unitYZFlag 0
     rw [mem_flagSupport_iff]
     simp [InFlag,unitYZFlag]
   · apply poleOrder_le_support_of_mem v x unitYZFlag 2
     rw [mem_flagSupport_iff]
     simp [InFlag,unitYZFlag]
theorem exponentSetPoleWeight_unitAll
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L):
   exponentSetPoleWeight v x (flagSupport unitAllFlag)=
     max (poleOrder v (x 1))
       (max (poleOrder v (x 0)) (poleOrder v (x 2))):=by
 apply le_antisymm
 · simpa [unitAllFlag] using exponentSetPoleWeight_flagSupport_le v x unitAllFlag
 · apply max_le
   · apply poleOrder_le_support_of_mem v x unitAllFlag 1
     rw [mem_flagSupport_iff]
     simp [InFlag,unitAllFlag]
   · apply max_le
     · apply poleOrder_le_support_of_mem v x unitAllFlag 0
       rw [mem_flagSupport_iff]
       simp [InFlag,unitAllFlag]
     · apply poleOrder_le_support_of_mem v x unitAllFlag 2
       rw [mem_flagSupport_iff]
       simp [InFlag,unitAllFlag]
theorem exponentSetPoleWeight_flagSupport_le_three
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L)
   (p:FlagDegree):
   exponentSetPoleWeight v x (flagSupport p) ≤
     (p.zOnly:ℤ)*exponentSetPoleWeight v x (flagSupport unitZFlag)+
     (p.yz:ℤ)*exponentSetPoleWeight v x (flagSupport unitYZFlag)+
     (p.all:ℤ)*exponentSetPoleWeight v x (flagSupport unitAllFlag):=by
 rw [exponentSetPoleWeight_unitZ,exponentSetPoleWeight_unitYZ,
   exponentSetPoleWeight_unitAll]
 exact exponentSetPoleWeight_flagSupport_le v x p
end
end ProximityPrize.SubmissionLower.RCN114
end PackedLegacy_P

/-! Packed from ProximityPrize.SubmissionLower.Q8. -/
section PackedLegacy_Q8
namespace ProximityPrize.SubmissionLower.RCN340
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN002 RCN005
 RCN006
open RCN344 RCN264 RCN095 RCN114 RCN295 RCN341 RCN237 RCN165
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def LiteralSupportPoleBound
   {P:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P)
   (E:Finset (Fin 3 →₀ ℕ)) (cost:ℕ):Prop:=
 let i0:=D.index
 let htr:=D.transcendental
 letI:Algebra (Polynomial Omega) (CoordinateRing Omega P):=
   quotientPolynomialAlgebra Omega P i0
 letI:Algebra (Polynomial Omega) (CoordinateField Omega P):=
   polynomialBaseAlgebra Omega P i0
 letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseAlgebra Omega P i0 htr
 letI:=quotientBaseScalarTower Omega P i0
 letI:=polynomialBaseScalarTower Omega P i0
 letI:=quotientFractionScalarTower Omega P i0
 letI:=polynomialRationalScalarTower Omega P i0 htr
 letI:=rationalBaseScalarTower Omega P i0 htr
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=
   D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=
   D.separable
 ∀ W:Finset (Place Omega (CoordinateField Omega P)),
   (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega P) E) ≤
     (cost:ℤ)
structure AdaptiveUnitPoleBudget
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (p q:FlagDegree) where
 zCost:RegularComponent Omega G T H → ℕ
 yzCost:RegularComponent Omega G T H → ℕ
 allCost:RegularComponent Omega G T H → ℕ
 zPole:∀ C:RegularComponent Omega G T H,
   LiteralSupportPoleBound (base C) (flagSupport unitZFlag) (zCost C)
 yzPole:∀ C:RegularComponent Omega G T H,
   LiteralSupportPoleBound (base C) (flagSupport unitYZFlag) (yzCost C)
 allPole:∀ C:RegularComponent Omega G T H,
   LiteralSupportPoleBound (base C) (flagSupport unitAllFlag) (allCost C)
 sum_zCost_le:(∑ C:RegularComponent Omega G T H,zCost C) ≤
   flagMixed p q unitZFlag
 sum_yzCost_le:(∑ C:RegularComponent Omega G T H,yzCost C) ≤
   flagMixed p q unitYZFlag
 sum_allCost_le:(∑ C:RegularComponent Omega G T H,allCost C) ≤
   flagMixed p q unitAllFlag
def AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (U:AdaptiveUnitPoleBudget base p q):
   PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q where
 zCost:=U.zCost
 yzCost:=U.yzCost
 allCost:=U.allCost
 sum_zCost_le:=U.sum_zCost_le
 sum_yzCost_le:=U.sum_yzCost_le
 sum_allCost_le:=U.sum_allCost_le
 primeBudget:=by
   intro C
   refine ⟨?_⟩
   intro r A hA hproper points hpointsP hpointsA
   let D:=base C
   let i0:=D.index
   let htr:=D.transcendental
   letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
     quotientPolynomialAlgebra Omega C.1 i0
   letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
     polynomialBaseAlgebra Omega C.1 i0
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     rationalBaseAlgebra Omega C.1 i0 htr
   letI:=quotientBaseScalarTower Omega C.1 i0
   letI:=polynomialBaseScalarTower Omega C.1 i0
   letI:=quotientFractionScalarTower Omega C.1 i0
   letI:=polynomialRationalScalarTower Omega C.1 i0 htr
   letI:=rationalBaseScalarTower Omega C.1 i0 htr
   letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
     D.finite
   letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
     D.separable
   have hz:=U.zPole C
   have hyz:=U.yzPole C
   have hall:=U.allPole C
   change ∀ W:Finset (Place Omega (CoordinateField Omega C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitZFlag)) ≤ (U.zCost C:ℤ) at hz
   change ∀ W:Finset (Place Omega (CoordinateField Omega C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitYZFlag)) ≤ (U.yzCost C:ℤ) at hyz
   change ∀ W:Finset (Place Omega (CoordinateField Omega C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitAllFlag)) ≤ (U.allCost C:ℤ) at hall
   have hpole:∀ W:Finset (Place Omega (CoordinateField Omega C.1)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport r)) ≤
       ((r.zOnly*U.zCost C+r.yz*U.yzCost C+
         r.all*U.allCost C:ℕ):ℤ):=by
     intro W
     calc
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
           (flagSupport r)) ≤
           ∑ v∈W,
             ((r.zOnly:ℤ)*exponentSetPoleWeight v.val
                 (coordinate Omega C.1) (flagSupport unitZFlag)+
              (r.yz:ℤ)*exponentSetPoleWeight v.val
                 (coordinate Omega C.1) (flagSupport unitYZFlag)+
              (r.all:ℤ)*exponentSetPoleWeight v.val
                 (coordinate Omega C.1) (flagSupport unitAllFlag)):=by
         apply Finset.sum_le_sum
         intro v _
         exact exponentSetPoleWeight_flagSupport_le_three v.val
           (coordinate Omega C.1) r
       _=(r.zOnly:ℤ)*
             (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
               (flagSupport unitZFlag))+
           (r.yz:ℤ)*
             (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
               (flagSupport unitYZFlag))+
           (r.all:ℤ)*
             (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
               (flagSupport unitAllFlag)):=by
         simp only [Finset.sum_add_distrib,Finset.mul_sum]
       _ ≤ (r.zOnly:ℤ)*(U.zCost C:ℤ)+
           (r.yz:ℤ)*(U.yzCost C:ℤ)+
           (r.all:ℤ)*(U.allCost C:ℤ):=by
         exact add_le_add
           (add_le_add
             (mul_le_mul_of_nonneg_left (hz W) (by positivity))
             (mul_le_mul_of_nonneg_left (hyz W) (by positivity)))
           (mul_le_mul_of_nonneg_left (hall W) (by positivity))
       _=((r.zOnly*U.zCost C+r.yz*U.yzCost C+
           r.all*U.allCost C:ℕ):ℤ):=by
         push_cast
         ring
   exact finite_zero_points_le_exponentSet_of_literalCoordinate C.1 D
     (flagSupport r)
     (r.zOnly*U.zCost C+r.yz*U.yzCost C+r.all*U.allCost C)
     hpole A ((support_subset_flagSupport_iff r A).2 hA) hproper
     points hpointsP hpointsA
end
end ProximityPrize.SubmissionLower.RCN340
end PackedLegacy_Q8

/-! Packed from ProximityPrize.SubmissionLower.G. -/
section PackedLegacy_G
namespace ProximityPrize.SubmissionLower.RCN022
open scoped Classical
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
def elementEmbedding (s:L) (hs:Transcendental K s):RatFunc K →ₐ[K] L:=
 RatFunc.liftAlgHom (Polynomial.aeval s)
   (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
     (Polynomial.aeval s).toRingHom (transcendental_iff_injective.mp hs))
theorem elementEmbedding_variable (s:L) (hs:Transcendental K s):
   elementEmbedding K L s hs
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=s:=by
 change RatFunc.liftAlgHom (Polynomial.aeval s) _
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=s
 calc
   _=Polynomial.aeval s Polynomial.X:=
     RatFunc.liftRingHom_algebraMap _ _ Polynomial.X
   _=s:=Polynomial.aeval_X s
theorem elementEmbedding_eq_adjoin_comp (s:L) (hs:Transcendental K s):
   elementEmbedding K L s hs=
     (IntermediateField.adjoin K ({s}:Set L)).val.comp
       (RatFunc.algEquivOfTranscendental s hs).toAlgHom:=by
 apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
 ext
 change elementEmbedding K L s hs
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=
   ((RatFunc.algEquivOfTranscendental s hs
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X):
       IntermediateField.adjoin K ({s}:Set L)):L)
 rw [elementEmbedding_variable]
 simp
theorem finiteDimensional_elementEmbedding
   (base:RatFunc K →ₐ[K] L)
   (hfinite:
     letI:Algebra (RatFunc K) L:=base.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (s:L) (hs:Transcendental K s):
   letI:Algebra (RatFunc K) L:=
     (elementEmbedding K L s hs).toRingHom.toAlgebra
   FiniteDimensional (RatFunc K) L:=by
 letI:Algebra (RatFunc K) L:=base.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(base.commutes c).symm
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 have hadjoin:FiniteDimensional (IntermediateField.adjoin K ({s}:Set L)) L:=
   FunctionField.finiteDimensional_of_adjoin_transcendental hs
 let e:RatFunc K ≃ₐ[K] (IntermediateField.adjoin K ({s}:Set L)):=
   RatFunc.algEquivOfTranscendental s hs
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L s hs).toRingHom.toAlgebra
 have hsmul:∀ (c:IntermediateField.adjoin K ({s}:Set L)) (x:L),
     e.symm c • x=c • x:=by
   intro c x
   rw [Algebra.smul_def,Algebra.smul_def]
   change elementEmbedding K L s hs (e.symm c)*x=(c:L)*x
   rw [elementEmbedding_eq_adjoin_comp]
   simp [e]
 let b:=Module.finBasis (IntermediateField.adjoin K ({s}:Set L)) L
 exact (b.mapCoeffs e.symm hsmul).finiteDimensional_of_finite
end
end ProximityPrize.SubmissionLower.RCN022
end PackedLegacy_G

/-! Packed from ProximityPrize.SubmissionLower.G7. -/
section PackedLegacy_G7
namespace ProximityPrize.SubmissionLower.RCN369
open scoped Classical
open KaehlerDifferential
noncomputable section
set_option maxHeartbeats 2000000
section RatFuncDifferential
variable (K:Type*) [Field K]
theorem span_singleton_D_ratFunc_X:
   Submodule.span (RatFunc K)
       ({D K (RatFunc K)
         (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)}:
         Set Ω[RatFunc K⁄K])=⊤:=by
 have hall:=span_range_map_derivation_of_isLocalization
   K (Polynomial K) (RatFunc K) (nonZeroDivisors (Polynomial K))
 apply top_unique
 rw [←hall]
 apply Submodule.span_le.mpr
 rintro x ⟨P,rfl⟩
 change map K K (Polynomial K) (RatFunc K) (D K (Polynomial K) P)∈_
 rw [polynomial_D_apply,LinearMap.map_smul_of_tower,map_D]
 exact Submodule.smul_of_tower_mem _ _
   (Submodule.subset_span (Set.mem_singleton _))
end RatFuncDifferential
section ProjectionCriterion
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
def parameterDifferential (embedding:RatFunc K →ₐ[K] L):Ω[L⁄K]:=
 D K L (embedding (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
theorem isSeparable_iff_span_parameterDifferential
   (embedding:RatFunc K →ₐ[K] L):
   letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
   FiniteDimensional (RatFunc K) L →
     (Algebra.IsSeparable (RatFunc K) L ↔
       Submodule.span L ({parameterDifferential K L embedding}:Set Ω[L⁄K])=⊤):=by
 letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(embedding.commutes c).symm
 intro hfinite
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 constructor
 · intro hsep
   letI:Algebra.IsSeparable (RatFunc K) L:=hsep
   letI:Algebra.FormallyUnramified (RatFunc K) L:=
     Algebra.FormallyUnramified.of_isSeparable (RatFunc K) L
   have htarget:Subsingleton Ω[L⁄RatFunc K]:=inferInstance
   have hsurj:Function.Surjective (mapBaseChange K (RatFunc K) L):=by
     rw [←LinearMap.range_eq_top,range_mapBaseChange]
     apply top_unique
     intro x _
     change map K (RatFunc K) L L x=0
     exact Subsingleton.elim _ _
   have hsource:=span_singleton_D_ratFunc_X K
   rw [←LinearMap.range_eq_top] at hsurj
   apply top_unique
   rw [←hsurj]
   rintro x ⟨x,rfl⟩
   induction x with
   | zero => simp
   | add x y hx hy =>
       rw [map_add]
       exact Submodule.add_mem _ hx hy
   | tmul l ω =>
       have hω:ω∈Submodule.span (RatFunc K)
           ({D K (RatFunc K)
             (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)}:
             Set Ω[RatFunc K⁄K]):=by
         rw [hsource]
         trivial
       obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hω
       rw [TensorProduct.tmul_smul]
       change mapBaseChange K (RatFunc K) L
         ((algebraMap (RatFunc K) L a*l) ⊗ₜ
           D K (RatFunc K)
             (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))∈_
       rw [mapBaseChange_tmul,map_D]
       change (algebraMap (RatFunc K) L a*l) •
         parameterDifferential K L embedding∈
           Submodule.span L
             ({parameterDifferential K L embedding}:Set Ω[L⁄K])
       exact Submodule.smul_mem _ _
         (Submodule.subset_span (Set.mem_singleton _))
 · intro hspan
   have hrange:LinearMap.range (mapBaseChange K (RatFunc K) L)=⊤:=by
     apply top_unique
     rw [←hspan]
     apply Submodule.span_le.mpr
     intro η hη
     rw [Set.mem_singleton_iff.mp hη]
     refine ⟨1 ⊗ₜ D K (RatFunc K)
         (algebraMap (Polynomial K) (RatFunc K) Polynomial.X),?_⟩
     rw [mapBaseChange_tmul,one_smul,map_D]
     rfl
   have hker:LinearMap.ker (map K (RatFunc K) L L)=⊤:=by
     rw [←range_mapBaseChange]
     exact hrange
   have hzero:map K (RatFunc K) L L=0:=by
     apply LinearMap.ker_eq_top.mp hker
   have hsub:Subsingleton Ω[L⁄RatFunc K]:=by
     constructor
     intro x y
     obtain ⟨x,rfl⟩:=map_surjective K (RatFunc K) L x
     obtain ⟨y,rfl⟩:=map_surjective K (RatFunc K) L y
     rw [hzero,LinearMap.zero_apply,LinearMap.zero_apply]
   letI:Subsingleton Ω[L⁄RatFunc K]:=hsub
   letI:Algebra.FormallyUnramified (RatFunc K) L:=⟨inferInstance⟩
   exact Algebra.FormallyUnramified.isSeparable (RatFunc K) L
end ProjectionCriterion
end
end ProximityPrize.SubmissionLower.RCN369
end PackedLegacy_G7

/-! Packed from ProximityPrize.SubmissionLower.X1. -/
section PackedLegacy_X1
namespace ProximityPrize.SubmissionLower.RCN370
open scoped Classical
open KaehlerDifferential RCN369
noncomputable section
set_option maxHeartbeats 2000000
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
theorem eq_algebraMap_of_isAlgebraic [IsAlgClosed K]
   (s:L) (hs:IsAlgebraic K s):
   ∃ c:K,algebraMap K L c=s:=by
 let S:IntermediateField K L:=IntermediateField.adjoin K {s}
 letI:Algebra.IsAlgebraic K S:=
   IntermediateField.isAlgebraic_adjoin_simple hs.isIntegral
 obtain ⟨c,hc⟩:=
   (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=K) (K:=S)).2
     (⟨s,IntermediateField.mem_adjoin_simple_self K s⟩:S)
 refine ⟨c,?_⟩
 have hcast:=congrArg (algebraMap S L) hc
 simpa only [IntermediateField.algebraMap_apply,
   IntermediateField.coe_algebraMap_apply] using hcast
end
end ProximityPrize.SubmissionLower.RCN370
end PackedLegacy_X1

/-! Packed from ProximityPrize.SubmissionLower.R7. -/
section PackedLegacy_R7
namespace ProximityPrize.SubmissionLower.RCN351
open scoped Classical TensorProduct
open Polynomial KaehlerDifferential RCN369 RCN370 RCN022
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
theorem formallyEtale_of_finite_isSeparable
   (F E:Type*) [Field F] [Field E] [Algebra F E]
   [FiniteDimensional F E] [Algebra.IsSeparable F E]:
   Algebra.FormallyEtale F E:=by
 have:=Algebra.FormallyUnramified.of_isSeparable F E
 have:=Algebra.FormallyUnramified.finite_of_free (R:=F) (S:=E)
 refine Algebra.FormallyEtale.iff_comp_bijective.mpr fun B _ _ I h↦?_
 refine ⟨Algebra.FormallyUnramified.iff_comp_injective_of_small.mp
   (Algebra.FormallyUnramified.of_isSeparable F E) I h,?_⟩
 intro f
 let pb:=Field.powerBasisOfFiniteOfSeparable F E
 obtain ⟨x,hx⟩:=Ideal.Quotient.mk_surjective (f pb.gen)
 have helper:∀ x,IsScalarTower.toAlgHom F B
     (HasQuotient.Quotient B I) x=
     Ideal.Quotient.mk I x:=fun _↦rfl
 have hx':Ideal.Quotient.mk I (aeval x (minpoly F pb.gen))=0:=by
   rw [←helper, ←aeval_algHom_apply,helper,hx,aeval_algHom_apply,
     minpoly.aeval,map_zero]
 obtain ⟨u,hu⟩:∃ u,
     (aeval x) (derivative (minpoly F pb.gen))*u+1∈I:=by
   have hunit:=(isUnit_iff_ne_zero.mpr
     ((Algebra.IsSeparable.isSeparable F pb.gen).aeval_derivative_ne_zero
       (minpoly.aeval F _))).map f
   rw [←aeval_algHom_apply, ←hx, ←helper,aeval_algHom_apply,
     helper] at hunit
   obtain ⟨u,hu⟩:=Ideal.Quotient.mk_surjective
     (-hunit.unit⁻¹:HasQuotient.Quotient B I)
   use u
   rw [←Ideal.Quotient.eq_zero_iff_mem,map_add,map_mul,map_one,hu,
     mul_neg,IsUnit.mul_val_inv,neg_add_cancel]
 use pb.liftEquiv.symm ⟨x+u*aeval x (minpoly F pb.gen),?_⟩
 · apply pb.algHom_ext
   simp [hx,hx']
 · rw [←eval_map_algebraMap,Polynomial.eval_add_of_sq_eq_zero,
     derivative_map, ←one_mul (eval x _),eval_map_algebraMap,
     eval_map_algebraMap, ←mul_assoc, ←add_mul, ←Ideal.mem_bot,
     ←h,pow_two,add_comm]
   · exact Ideal.mul_mem_mul hu (Ideal.Quotient.eq_zero_iff_mem.mp hx')
   rw [←Ideal.mem_bot, ←h]
   apply Ideal.pow_mem_pow
   rw [←Ideal.Quotient.eq_zero_iff_mem,map_mul,hx',mul_zero]
theorem ratFunc_variableDifferential_ne_zero (K:Type*) [Field K]:
   D K (RatFunc K)
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)≠0:=by
 letI:Algebra.FormallyEtale (Polynomial K) (RatFunc K):=
   Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Polynomial K))
 intro hzero
 have htensor:=congrArg
   (tensorKaehlerEquivOfFormallyEtale
     K (Polynomial K) (RatFunc K)).symm hzero
 have htensor':(1:RatFunc K) ⊗ₜ[Polynomial K]
     D K (Polynomial K) Polynomial.X=0:=by
   simpa only [map_zero,
     tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap] using htensor
 let l:Ω[Polynomial K⁄K] →ₗ[Polynomial K] RatFunc K:=
   (Algebra.linearMap (Polynomial K) (RatFunc K)).comp
     (polynomialEquiv K).toLinearMap
 have himage:=congrArg (l.liftBaseChange (RatFunc K)) htensor'
 have hone:(1:RatFunc K)=0:=by
   rw [LinearMap.liftBaseChange_tmul,one_smul,map_zero] at himage
   change algebraMap (Polynomial K) (RatFunc K)
     (polynomialEquiv K (D K (Polynomial K) Polynomial.X))=0 at himage
   simpa only [polynomialEquiv_D,derivative_X,map_one] using himage
 exact one_ne_zero hone
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
theorem parameterDifferential_ne_zero_of_isSeparable
   (embedding:RatFunc K →ₐ[K] L)
   (hfinite:
     letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hsep:
     letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc K) L):
   parameterDifferential K L embedding≠0:=by
 letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(embedding.commutes c).symm
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 letI:Algebra.IsSeparable (RatFunc K) L:=hsep
 letI:Algebra.FormallyEtale (RatFunc K) L:=
   formallyEtale_of_finite_isSeparable (RatFunc K) L
 intro hzero
 change D K L
   (algebraMap (RatFunc K) L
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))=0 at hzero
 have htensor:=congrArg
   (tensorKaehlerEquivOfFormallyEtale K (RatFunc K) L).symm hzero
 have htensor':(1:L) ⊗ₜ[RatFunc K]
     D K (RatFunc K)
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=0:=by
   simpa only [map_zero,
     tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap] using htensor
 have hsource:D K (RatFunc K)
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=0:=by
   rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at htensor'
   exact htensor'
 exact ratFunc_variableDifferential_ne_zero K hsource
theorem shear_bad_coefficient_subsingleton
   (r z:L) (hdz:D K L z≠0):
   ∀ {a b:K},
     D K L r+a • D K L z=0 →
     D K L r+b • D K L z=0 → a=b:=by
 intro a b ha hb
 apply smul_left_injective K hdz
 exact (eq_neg_of_add_eq_zero_right ha).trans
   (eq_neg_of_add_eq_zero_right hb).symm
theorem shear_transcendental_finite_separable_of_differential_ne_zero
   [IsAlgClosed K]
   (embeddingZ:RatFunc K →ₐ[K] L) (r z:L) (a:K)
   (hvalueZ:embeddingZ
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=z)
   (hfiniteZ:
     letI:Algebra (RatFunc K) L:=embeddingZ.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hsepZ:
     letI:Algebra (RatFunc K) L:=embeddingZ.toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc K) L)
   (hdiff:D K L r+a • D K L z≠0):
   ∃ hs:Transcendental K (r+a • z),
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L (r+a • z) hs).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L (r+a • z) hs).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L):=by
 have hDs:D K L (r+a • z)=D K L r+a • D K L z:=by
   rw [map_add,(D K L).map_smul]
 have hs:Transcendental K (r+a • z):=by
   show ¬ IsAlgebraic K _
   intro halg
   obtain ⟨c,hc⟩:=eq_algebraMap_of_isAlgebraic K L _ halg
   apply hdiff
   rw [←hDs, ←hc]
   exact (D K L).map_algebraMap c
 refine ⟨hs,?_,?_⟩
 · exact finiteDimensional_elementEmbedding K L embeddingZ hfiniteZ
     (r+a • z) hs
 · let embeddingS:=elementEmbedding K L (r+a • z) hs
   have hfiniteS:=finiteDimensional_elementEmbedding K L embeddingZ hfiniteZ
     (r+a • z) hs
   have hcriterionZ:=
     isSeparable_iff_span_parameterDifferential K L embeddingZ hfiniteZ
   have hcriterionS:=
     isSeparable_iff_span_parameterDifferential K L embeddingS hfiniteS
   have hspanZ:Submodule.span L ({D K L z}:Set Ω[L⁄K])=⊤:=by
     have hz:=hcriterionZ.mp hsepZ
     unfold parameterDifferential at hz
     rw [hvalueZ] at hz
     exact hz
   apply hcriterionS.mpr
   have hparamS:parameterDifferential K L embeddingS=
       D K L (r+a • z):=by
     unfold parameterDifferential embeddingS
     rw [elementEmbedding_variable]
   rw [hparamS,hDs]
   apply top_unique
   rw [←hspanZ]
   apply Submodule.span_le.mpr
   intro x hx
   rw [Set.mem_singleton_iff.mp hx]
   have hS_mem:D K L r+a • D K L z∈
       Submodule.span L ({D K L z}:Set Ω[L⁄K]):=by
     rw [hspanZ]
     trivial
   obtain ⟨b,hb⟩:=Submodule.mem_span_singleton.mp hS_mem
   have hb0:b≠0:=by
     intro hzero
     apply hdiff
     rw [←hb,hzero,zero_smul]
   apply Submodule.mem_span_singleton.mpr
   refine ⟨b⁻¹,?_⟩
   rw [←hb,smul_smul,inv_mul_cancel₀ hb0,one_smul]
section FiniteFamily
variable {I:Type*} [Fintype I]
 (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 (r z:∀ i,E i)
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN351
end PackedLegacy_R7
end Compact_PackedLegacyCore2
