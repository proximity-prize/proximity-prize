import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.AW
import ProximityPrize.SubmissionLower.G7
import ProximityPrize.SubmissionLower.X0
import ProximityPrize.SubmissionLower.G
import ProximityPrize.SubmissionLower.I2
namespace ProximityPrize.SubmissionLower.ContactAdaptiveShearConditional
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveScalarTowers
 ActualCurveZeroCount
open ContactGenericSurface ContactPolynomialSolutions ContactPolynomialRecovery
open ContactTaylorNumerators ContactComponentPencils ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactSurfaceSeedCount
open CharacteristicFreeInseparableDichotomyResearch
open ActualCoordinateDegreeSum ActualPlaneCharacteristicFreeDegreeResearch
open SeparableShearKaehlerResearch
open CoordinateBoxZeroCount SeparableShearFieldResearch
open ArbitraryRationalProjectionResearch
open ContactConstantSeedCoordinateResearch
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
variable (φ:Polynomial K →+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
variable [IsAlgClosed Ω]
variable (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
private def adaptiveFamilyFiniteSummary {I:Type} [Fintype I]
   (Q:I → Ideal (MvPolynomial (Fin 3) Ω)) [∀ i,(Q i).IsPrime]
   (A:∀ i,Algebra (RatFunc Ω) (CoordinateField Ω (Q i)))
   (B:ℕ):Prop:=
 letI:=A
 (∀ i,FiniteDimensional (RatFunc Ω) (CoordinateField Ω (Q i)))∧
   (∑ i,Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))) ≤ B
def adaptiveShearCap (cap:Fin 3 → ℕ):Fin 3 → ℕ:=
 ![cap 0,cap 1,cap 2+2*cap 1]
def shearedPolynomialCap (cap:Fin 3 → ℕ):Fin 3 → ℕ:=
 ![cap 0,cap 1,cap 2+cap 1]
def adaptiveShearCost (cap:Fin 3 → ℕ):ℕ:=
 componentCost P (adaptiveShearCap cap)
theorem adaptiveShearCost_eq (cap:Fin 3 → ℕ):
   adaptiveShearCost P cap=componentCost P cap+
     2*cap 1*actualCoordinateDegree Ω P 2:=by
 simp [adaptiveShearCost,adaptiveShearCap,componentCost,Fin.sum_univ_three]
 ring
def AdaptiveShearFiberCertificate
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (w:ℕ) (cap:Fin 3 → ℕ):Prop:=
 ∀ (x u₀ u₁:K),agreementPolynomial φ F w x u₀ u₁∉P →
   (∀ j,(agreementPolynomial φ F w x u₀ u₁).degreeOf j ≤ cap j) →
     (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤
       adaptiveShearCost P cap
def globalShearDegree (dS:ℕ):Fin 3 → ℕ:=
 ![actualCoordinateDegree Ω P 0,dS,actualCoordinateDegree Ω P 2]
def globalShearCost (dS:ℕ) (cap:Fin 3 → ℕ):ℕ:=
 ∑ i,shearedPolynomialCap cap i*globalShearDegree P dS i
theorem globalShearCost_eq (dS:ℕ) (cap:Fin 3 → ℕ):
   globalShearCost P dS cap=
     cap 0*actualCoordinateDegree Ω P 0+cap 1*dS+
       (cap 2+cap 1)*actualCoordinateDegree Ω P 2:=by
 simp [globalShearCost,globalShearDegree,shearedPolynomialCap,
   Fin.sum_univ_three]
def GlobalShearFiberCertificate
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (w dS:ℕ) (cap:Fin 3 → ℕ):Prop:=
 ∀ (x u₀ u₁:K),agreementPolynomial φ F w x u₀ u₁∉P →
   (∀ j,(agreementPolynomial φ F w x u₀ u₁).degreeOf j ≤ cap j) →
     (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤
       globalShearCost P dS cap
theorem globalShearFiberCertificate_of_card_le_one
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (w dS:ℕ) (cap:Fin 3 → ℕ)
   (hcard:Γ.card ≤ 1) (hcost:1 ≤ globalShearCost P dS cap):
   GlobalShearFiberCertificate φ P F selected Γ w dS cap:=by
 intro x u₀ u₁ _ _
 exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
   (hcard.trans hcost)
theorem globalShearFiberCertificate_of_seedCoordinate_isAlgebraic
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (w dS:ℕ) (cap:Fin 3 → ℕ)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (hZ:IsAlgebraic Ω (coordinate Ω P 2))
   (hcost:1 ≤ globalShearCost P dS cap):
   GlobalShearFiberCertificate φ P F selected Γ w dS cap:=by
 apply globalShearFiberCertificate_of_card_le_one φ P F selected Γ w dS cap
 · exact selected_seed_set_card_le_one_of_seedCoordinate_isAlgebraic
     φ P selected Γ hpoint hZ
 · exact hcost
theorem coordinateDegree_pos_of_transcendental_finite
   (hfinite:ProjectionsFinite Ω P) (j:Fin 3)
   (hj:Transcendental Ω (coordinate Ω P j)):
   1 ≤ actualCoordinateDegree Ω P j:=by
 letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
   rationalBaseAlgebra Ω P j hj
 letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω P):=hfinite j hj
 rw [actualCoordinateDegree_of_transcendental Ω P j hj]
 exact Module.finrank_pos
abbrev rationalElementEmbedding
   (k L:Type*) [Field k] [Field L] [Algebra k L]
   (s:L) (hs:Transcendental k s):RatFunc k →ₐ[k] L:=
 elementEmbedding k L s hs
theorem rationalElementEmbedding_variable
   (k L:Type*) [Field k] [Field L] [Algebra k L]
   (s:L) (hs:Transcendental k s):
   rationalElementEmbedding k L s hs
       (algebraMap (Polynomial k) (RatFunc k) Polynomial.X)=s:=by
 exact elementEmbedding_variable k L s hs
def BadRShearCoordinateCertificate (hfinite:ProjectionsFinite Ω P):Prop:=
 ∀ (hR:Transcendental Ω (coordinate Ω P 1))
   (hZ:Transcendental Ω (coordinate Ω P 2)),
   (letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
     rationalBaseAlgebra Ω P 1 hR;
     ¬ Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)) →
   (letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
     rationalBaseAlgebra Ω P 2 hZ;
     Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)) →
   ∃ hS:Transcendental Ω (coordinate Ω P 1+coordinate Ω P 2),
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       (rationalElementEmbedding Ω (CoordinateField Ω P)
         (coordinate Ω P 1+coordinate Ω P 2) hS).toRingHom.toAlgebra;
     Module.finrank (RatFunc Ω) (CoordinateField Ω P) ≤
       actualCoordinateDegree Ω P 1+actualCoordinateDegree Ω P 2
def shearedRingCoordinates:Fin 3 → CoordinateRing Ω P:=
 ![quotientCoordinate Ω P 0,
   quotientCoordinate Ω P 1+quotientCoordinate Ω P 2,
   quotientCoordinate Ω P 2]
def ShearedPolynomialTransport
   (A:MvPolynomial (Fin 3) Ω) (cap:Fin 3 → ℕ):Prop:=
 ∃ B:MvPolynomial (Fin 3) Ω,
   (∀ i,B.degreeOf i ≤ shearedPolynomialCap cap i)∧
     MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateRing Ω P))
       (shearedRingCoordinates P) B=Ideal.Quotient.mk P A
def ShearedAgreementTransportCertificate
   (F:MvPolynomial (Fin 4) K) (w:ℕ) (cap:Fin 3 → ℕ):Prop:=
 ∀ (x u₀ u₁:K),
   (∀ i,(agreementPolynomial φ F w x u₀ u₁).degreeOf i ≤ cap i) →
     ShearedPolynomialTransport P (agreementPolynomial φ F w x u₀ u₁) cap
def actualCoordinateDataAt
   (hfinite:ProjectionsFinite Ω P) (i:Fin 3)
   (hsep:∀ hi:Transcendental Ω (coordinate Ω P i),
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       rationalBaseAlgebra Ω P i hi
     Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)):
   Coordinate Ω (CoordinateField Ω P):=
 if hi:Transcendental Ω (coordinate Ω P i) then
   Sum.inr {
     embedding:=rationalBaseEmbedding Ω P i hi
     finite:=hfinite i hi
     separable:=hsep hi}
 else
   Sum.inl ((coordinate_eq_scalar_of_isAlgebraic Ω P i (not_not.mp hi)).choose)
theorem actualCoordinateDataAt_value
   (hfinite:ProjectionsFinite Ω P) (i:Fin 3)
   (hsep:∀ hi:Transcendental Ω (coordinate Ω P i),
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       rationalBaseAlgebra Ω P i hi
     Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)):
   coordinateValue Ω (CoordinateField Ω P)
     (actualCoordinateDataAt P hfinite i hsep)=coordinate Ω P i:=by
 unfold actualCoordinateDataAt
 split_ifs with hi
 · exact rational_variable_image Ω P i hi
 · exact (coordinate_eq_scalar_of_isAlgebraic Ω P i
     (not_not.mp hi)).choose_spec
theorem actualCoordinateDataAt_degree
   (hfinite:ProjectionsFinite Ω P) (i:Fin 3)
   (hsep:∀ hi:Transcendental Ω (coordinate Ω P i),
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       rationalBaseAlgebra Ω P i hi
     Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)):
   coordinateDegree Ω (CoordinateField Ω P)
     (actualCoordinateDataAt P hfinite i hsep)=actualCoordinateDegree Ω P i:=by
 unfold actualCoordinateDataAt actualCoordinateDegree
 split_ifs <;> rfl
def shearCoordinateData
   (hS:Transcendental Ω (coordinate Ω P 1+coordinate Ω P 2))
   (hfiniteS:
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       (rationalElementEmbedding Ω (CoordinateField Ω P)
         (coordinate Ω P 1+coordinate Ω P 2) hS).toRingHom.toAlgebra
     FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
   (hsepS:
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       (rationalElementEmbedding Ω (CoordinateField Ω P)
         (coordinate Ω P 1+coordinate Ω P 2) hS).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)):
   Coordinate Ω (CoordinateField Ω P):=
 Sum.inr {
   embedding:=rationalElementEmbedding Ω (CoordinateField Ω P)
     (coordinate Ω P 1+coordinate Ω P 2) hS
   finite:=hfiniteS
   separable:=hsepS}
theorem sheared_degree_cost_le_adaptive
   (cap:Fin 3 → ℕ) (dS:ℕ)
   (hdegreeS:dS ≤ actualCoordinateDegree Ω P 1+
     actualCoordinateDegree Ω P 2):
   cap 0*actualCoordinateDegree Ω P 0+cap 1*dS+
       (cap 2+cap 1)*actualCoordinateDegree Ω P 2 ≤
     adaptiveShearCost P cap:=by
 have h:=sheared_box_cost_le_old_add_two_penalty
   (cap 0) (cap 1) (cap 2)
   (actualCoordinateDegree Ω P 0) (actualCoordinateDegree Ω P 1)
   (actualCoordinateDegree Ω P 2) dS hdegreeS
 simpa only [adaptiveShearCost_eq,componentCost,Fin.sum_univ_three] using h
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem prime_seed_incidence_sharp_adaptive_shear
   (hfinite:ProjectionsFinite Ω P)
   (hnonpoint:∀ v:Fin 3 → Ω,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap φ F∈P)
   (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
   (hfiber:AdaptiveShearFiberCertificate φ P F selected Γ w cap):
   Γ.card*(a-w) ≤ (nodes.card-w)*adaptiveShearCost P cap+
     (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
 classical
 let I:=identityNodes φ P F nodes x u₀ u₁ w
 let relation:K → ι → Prop:=
   fun γ i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i
 by_cases hI:I.card ≤ w
 · have hproperFiber:∀ i∈nodes \ I,
       (Γ.filter (fun γ↦relation γ i)).card ≤ adaptiveShearCost P cap:=by
     intro i hi
     obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
     have hproper:agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)∉P:=by
       intro hmem
       apply hnotI
       exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
     exact hfiber (x i) (u₀ i) (u₁ i) hproper (hcap i hinodes)
   have hcount:=ContactIncidence.sharp_incidence_bound relation Γ nodes I a w
     (adaptiveShearCost P cap) (identityNodes_subset φ P F nodes x u₀ u₁ w)
     hI hwa han hagreement hproperFiber
   omega
 · have hc:w < I.card:=Nat.lt_of_not_ge hI
   have hvalues:∀ (t:{γ:K//γ∈Γ}) i,i∈I →
       (selected t.1).eval (x i)=u₀ i+t.1*u₁ i:=by
     intro t
     exact selected_agrees_on_identity_nodes φ P F nodes x u₀ u₁ p w hchar
       (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
       (hregular t.1 t.2) (hpoint t.1 t.2)
   obtain ⟨P₀,P₁,h₀,h₁,_,hpencil⟩:=
     exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w hinj hc
       (fun t:{γ:K//γ∈Γ}↦t.1) (fun t↦selected t.1)
       (fun t↦hdegree t.1 t.2) hvalues
   have hfilter:Γ.filter
       (fun γ↦selected γ=P₀+Polynomial.C γ*P₁)=Γ:=
     Finset.filter_eq_self.mpr (fun γ hγ↦hpencil ⟨γ,hγ⟩)
   have hΓ:Γ.card ≤ e+1:=by
     have h:=hnoPencil P₀ P₁ h₀ h₁
     rwa [hfilter] at h
   have hZ:=seed_transcendental_of_many_identities φ P F hF hH
     nodes x u₀ u₁ w hw hinj hc hnonpoint
   have hδ:=coordinateDegree_pos_of_transcendental_finite P hfinite (2:Fin 3) hZ
   have hcharge:Γ.card*(a-w) ≤
       (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
     calc
       _ ≤ (e+1)*(a-w):=Nat.mul_le_mul_right _ hΓ
       _ ≤ _:=by
         simpa only [Nat.mul_one] using
           Nat.mul_le_mul_left ((e+1)*(a-w)) hδ
   omega
theorem prime_seed_incidence_sharp_global_shear
   (hfinite:ProjectionsFinite Ω P)
   (hnonpoint:∀ v:Fin 3 → Ω,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap φ F∈P)
   (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
   (dS:ℕ)
   (hfiber:GlobalShearFiberCertificate φ P F selected Γ w dS cap):
   Γ.card*(a-w) ≤ (nodes.card-w)*globalShearCost P dS cap+
     (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
 classical
 let I:=identityNodes φ P F nodes x u₀ u₁ w
 let relation:K → ι → Prop:=
   fun γ i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i
 by_cases hI:I.card ≤ w
 · have hproperFiber:∀ i∈nodes \ I,
       (Γ.filter (fun γ↦relation γ i)).card ≤ globalShearCost P dS cap:=by
     intro i hi
     obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
     have hproper:agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)∉P:=by
       intro hmem
       apply hnotI
       exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
     exact hfiber (x i) (u₀ i) (u₁ i) hproper (hcap i hinodes)
   have hcount:=ContactIncidence.sharp_incidence_bound relation Γ nodes I a w
     (globalShearCost P dS cap) (identityNodes_subset φ P F nodes x u₀ u₁ w)
     hI hwa han hagreement hproperFiber
   omega
 · have hc:w < I.card:=Nat.lt_of_not_ge hI
   have hvalues:∀ (t:{γ:K//γ∈Γ}) i,i∈I →
       (selected t.1).eval (x i)=u₀ i+t.1*u₁ i:=by
     intro t
     exact selected_agrees_on_identity_nodes φ P F nodes x u₀ u₁ p w hchar
       (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
       (hregular t.1 t.2) (hpoint t.1 t.2)
   obtain ⟨P₀,P₁,h₀,h₁,_,hpencil⟩:=
     exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w hinj hc
       (fun t:{γ:K//γ∈Γ}↦t.1) (fun t↦selected t.1)
       (fun t↦hdegree t.1 t.2) hvalues
   have hfilter:Γ.filter
       (fun γ↦selected γ=P₀+Polynomial.C γ*P₁)=Γ:=
     Finset.filter_eq_self.mpr (fun γ hγ↦hpencil ⟨γ,hγ⟩)
   have hΓ:Γ.card ≤ e+1:=by
     have h:=hnoPencil P₀ P₁ h₀ h₁
     rwa [hfilter] at h
   have hZ:=seed_transcendental_of_many_identities φ P F hF hH
     nodes x u₀ u₁ w hw hinj hc hnonpoint
   have hδ:=coordinateDegree_pos_of_transcendental_finite P hfinite (2:Fin 3) hZ
   have hcharge:Γ.card*(a-w) ≤
       (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
     calc
       _ ≤ (e+1)*(a-w):=Nat.mul_le_mul_right _ hΓ
       _ ≤ _:=by
         simpa only [Nat.mul_one] using
           Nat.mul_le_mul_left ((e+1)*(a-w)) hδ
   omega
theorem family_finite_and_sum_actualCoordinateDegree_at_le
   {I:Type} [Fintype I]
   (Q:I → Ideal (MvPolynomial (Fin 3) Ω)) [∀ i,(Q i).IsPrime]
   (hinjQ:Function.Injective Q) (j:Fin 3)
   (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hGmem:∀ i,G∈Q i)
   (hTmem:∀ i,T∈Q i) (hproper:¬ G∣T):
   (∀ i (hi:Transcendental Ω (coordinate Ω (Q i) j)),
     letI:Algebra (RatFunc Ω) (CoordinateField Ω (Q i)):=
       rationalBaseAlgebra Ω (Q i) j hi
     FiniteDimensional (RatFunc Ω) (CoordinateField Ω (Q i)))∧
     (∑ i,actualCoordinateDegree Ω (Q i) j) ≤
       coordinateMixedDegree Ω G T j:=by
 classical
 let s:Set I:={i | Transcendental Ω (coordinate Ω (Q i) j)}
 let D:s → ℕ:=fun i↦
   letI:Algebra (RatFunc Ω) (CoordinateField Ω (Q i)):=
     rationalBaseAlgebra Ω (Q i) j i.2
   Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))
 letI:∀ i:s,Algebra (RatFunc Ω) (CoordinateField Ω (Q i)):=
   fun i↦rationalBaseAlgebra Ω (Q i) j i.2
 have hinj':Function.Injective (fun i:s↦Q i):=by
   intro i k h
   apply Subtype.ext
   exact hinjQ h
 have hresult:=original_finite_sum_finrank_bound_without_separability
   Ω (Equiv.swap 0 j) (fun i:s↦Q i) (fun i↦i.2) hinj'
   G T hG (fun i↦hGmem i) (fun i↦hTmem i) hproper
 change adaptiveFamilyFiniteSummary (fun i:s↦Q i)
   (fun i↦rationalBaseAlgebra Ω (Q i) j i.2)
   (coordinateMixedDegree Ω G T j) at hresult
 constructor
 · intro i hi
   exact hresult.1 ⟨i,hi⟩
 · calc
     (∑ i,actualCoordinateDegree Ω (Q i) j)=∑ i:s,D i:=by
       apply Finset.sum_congr_set s
         (fun i↦actualCoordinateDegree Ω (Q i) j) D
       · intro i hi
         exact actualCoordinateDegree_of_transcendental Ω (Q i) j hi
       · intro i hi
         change ¬ Transcendental Ω (coordinate Ω (Q i) j) at hi
         exact dif_neg hi
     _ ≤ coordinateMixedDegree Ω G T j:=by
       exact hresult.2
theorem regularComponents_finite_and_degree_budget_charfree
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hproper:¬ G∣T):
   (∀ C:RegularComponent Ω G T (regularitySurface φ F),
     ProjectionsFinite Ω C.1)∧
     ∀ i,(∑ C:RegularComponent Ω G T (regularitySurface φ F),
       actualCoordinateDegree Ω C.1 i) ≤ coordinateMixedDegree Ω G T i:=by
 classical
 let H:=regularitySurface φ F
 letI:∀ C:RegularComponent Ω G T H,C.1.IsPrime:=
   fun C↦regularComponent_isPrime Ω G T H C
 have hfamily (i:Fin 3):=
   family_finite_and_sum_actualCoordinateDegree_at_le
     (Q:=fun C:RegularComponent Ω G T H↦C.1)
     Subtype.val_injective i G T hG
     (regularComponent_G_mem Ω G T H)
     (regularComponent_T_mem Ω G T H) hproper
 constructor
 · intro C i hi
   exact (hfamily i).1 C hi
 · intro i
   exact (hfamily i).2
theorem proper_cut_seed_bound_of_projection_sum_adaptive_shear
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap budget:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
   (hfinite:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     ProjectionsFinite Ω C.1)
   (hbudget:∀ i,
     (∑ C:RegularComponent Ω G T (regularitySurface φ F),
       actualCoordinateDegree Ω C.1 i) ≤ budget i)
   (hfiber:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     AdaptiveShearFiberCertificate φ C.1 F selected
       (componentSeeds Ω G T (regularitySurface φ F) Γ
         (selectedPoint φ selected) C) w cap):
   Γ.card*(a-w) ≤
     (nodes.card-w)*(∑ i,adaptiveShearCap cap i*budget i)+
       (e+1)*(a-w)*budget 2:=by
 classical
 let H:=regularitySurface φ F
 have hHp:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) H≠0:=by
   intro γ hγ
   change MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular γ hγ
 let degree:RegularComponent Ω G T H → Fin 3 → ℕ:=
   fun C i↦actualCoordinateDegree Ω C.1 i
 have hcomponent:∀ C:RegularComponent Ω G T H,
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C).card*(a-w) ≤
       (nodes.card-w)*(∑ i,adaptiveShearCap cap i*degree C i)+
         (e+1)*(a-w)*degree C 2:=by
   intro C
   have hsub:=componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C
   have hgmem:=regularComponent_G_mem Ω G T H C
   have hFmem:surfaceMap φ F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   have hcount:=prime_seed_incidence_sharp_adaptive_shear φ C.1 (hfinite C)
     (regularComponent_ne_point Ω G T H C) F hFmem
     (regularComponent_H_not_mem Ω G T H C) selected
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C)
     nodes x u₀ u₁ hinj p w a e hw hchar hwa han
     (fun γ hγ↦hdegree γ (hsub hγ))
     (fun γ hγ↦hsolution γ (hsub hγ))
     (fun γ hγ↦hregular γ (hsub hγ))
     (fun γ hγ↦componentSeeds_on_prime Ω G T H Γ
       (selectedPoint φ selected) C γ hγ)
     (fun γ hγ↦hagreement γ (hsub hγ))
     (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil)
     cap hcap (hfiber C)
   simpa only [adaptiveShearCost,componentCost,degree] using hcount
 exact aggregate_component_incidence Ω G T H Γ (selectedPoint φ selected)
   hGpoint hTpoint hHp (a-w) (nodes.card-w) (e+1)
   (adaptiveShearCap cap) budget degree hcomponent hbudget
end
end ProximityPrize.SubmissionLower.ContactAdaptiveShearConditional
