import ProximityPrize.SubmissionLower.Part.F003_01
section Compact_PackedLegacyCore1
section PackedLegacy_BX
namespace ProximityPrize.SubmissionLower.RCN173
section FiniteIncidence
variable {Seed Node:Type*} [DecidableEq Seed] [DecidableEq Node]
 (relation:Seed → Node → Prop)
 [∀ seed node,Decidable (relation seed node)]

theorem sharp_incidence_bound
   (seeds:Finset Seed) (nodes identities:Finset Node) (a w M:ℕ)
   (hidentities:identities ⊆ nodes) (hcard:identities.card ≤ w)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed => relation seed node)).card ≤ M):
   seeds.card*(a-w) ≤ (nodes.card-w)*M:=by
 exact enlarge_exempt_card_bound hcard hwa.le han
   (incidence_after_exempt_nodes relation seeds nodes identities a M
     hidentities hagreement hfiber)
end FiniteIncidence
end ProximityPrize.SubmissionLower.RCN173
end PackedLegacy_BX

/-! Packed from ProximityPrize.SubmissionLower.J. -/
section PackedLegacy_J
namespace ProximityPrize.SubmissionLower.RCN238
open scoped Classical BigOperators
open RCN002 RCN005 RCN007 RCN136 RCN231 RCN229 RCN313 RCN065 RCN319
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
 (φ:Polynomial K →+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def selectedPoint (selected:K → Polynomial K) (γ:K):Fin 3 → Ω:=
 fun i↦polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X) i.succ
theorem selectedPoint_seed (selected:K → Polynomial K) (γ:K):
   selectedPoint φ selected γ (2:Fin 3)=(φ.comp Polynomial.C) γ:=rfl
theorem selectedPoint_injective (selected:K → Polynomial K):
   Function.Injective (selectedPoint φ selected):=by
 intro γ η h
 apply (φ.comp Polynomial.C).injective
 simpa only [selectedPoint_seed] using congrFun h (2:Fin 3)
def agreementPolynomial (F:MvPolynomial (Fin 4) K) (w:ℕ) (x u₀ u₁:K):
   MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (agreementNumerator F w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁)
theorem selected_agreement_zero_iff
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (p w:ℕ) [CharP Ω p] (hchar:w < p)
   (γ:K) (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:specialization K (selected γ) γ F=0)
   (hregular:MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (x u₀ u₁:K):
   MvPolynomial.aeval (selectedPoint φ selected γ)
     (agreementPolynomial φ F w x u₀ u₁)=0 ↔
       (selected γ).eval x=u₀+γ*u₁:=by
 change MvPolynomial.eval (selectedPoint φ selected γ)
   (surfaceMap φ (agreementNumerator F w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁))=0 ↔ _
 rw [eval_surfaceMap]
 have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
     polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv]
 exact factorial_agreement_zero_iff_original_agreement (φ.comp Polynomial.C) F
   (selected γ) γ (φ Polynomial.X) hsolution hregular p w hchar hdegree x u₀ u₁
variable [IsAlgClosed Ω]
variable (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
def componentCost (cap:Fin 3 → ℕ):ℕ:=
 ∑ j,cap j*actualCoordinateDegree Ω P j
theorem agreement_fiber_card_le
   (hproj:ProjectionsFiniteSeparable Ω P)
   (hnonpoint:∀ v:Fin 3 → Ω,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (Γ:Finset K)
   (p w:ℕ) [CharP Ω p] (hchar:w < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (x u₀ u₁:K) (hproper:agreementPolynomial φ F w x u₀ u₁∉P)
   (cap:Fin 3 → ℕ)
   (hcap:∀ j,(agreementPolynomial φ F w x u₀ u₁).degreeOf j ≤ cap j):
   (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤ componentCost P cap:=by
 classical
 let fiber:=Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)
 let points:=fiber.image (selectedPoint φ selected)
 have hpointsP:∀ v∈points,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   exact hpoint γ (Finset.mem_filter.mp hγ).1
 have hpointsF:∀ v∈points,
     MvPolynomial.aeval v (agreementPolynomial φ F w x u₀ u₁)=0:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   obtain ⟨hΓ,hagree⟩:=Finset.mem_filter.mp hγ
   exact (selected_agreement_zero_iff φ F selected p w hchar γ
     (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) x u₀ u₁).mpr hagree
 have hcount:=RCN007.finite_zero_points_le_box Ω P hproj hnonpoint
   (agreementPolynomial φ F w x u₀ u₁) hproper cap hcap points hpointsP hpointsF
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
 rw [hcard] at hcount
 unfold componentCost
 exact_mod_cast hcount
theorem coordinateDegree_pos_of_transcendental
   (hproj:ProjectionsFiniteSeparable Ω P) (j:Fin 3)
   (hj:Transcendental Ω (coordinate Ω P j)):
   1 ≤ actualCoordinateDegree Ω P j:=by
 letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=rationalBaseAlgebra Ω P j hj
 letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω P):=(hproj j hj).1
 rw [actualCoordinateDegree_of_transcendental Ω P j hj]
 exact Module.finrank_pos
def NoLargeSelectedPencil (selected:K → Polynomial K) (Γ:Finset K) (w e:ℕ):Prop:=
 ∀ P₀ P₁:Polynomial K,P₀.natDegree ≤ w → P₁.natDegree ≤ w →
   (Γ.filter (fun γ↦selected γ=P₀+Polynomial.C γ*P₁)).card ≤ e+1
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem prime_seed_incidence_sharp
   (hproj:ProjectionsFiniteSeparable Ω P)
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
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j):
   Γ.card*(a-w) ≤ (nodes.card-w)*componentCost P cap+
     (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
 classical
 let I:=identityNodes φ P F nodes x u₀ u₁ w
 let relation:K → ι → Prop:=fun γ i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i
 by_cases hI:I.card ≤ w
 · have hfiber:∀ i∈nodes \ I,(Γ.filter (fun γ↦relation γ i)).card ≤ componentCost P cap:=by
     intro i hi
     obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
     have hproper:agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)∉P:=by
       intro hmem
       apply hnotI
       exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
     exact agreement_fiber_card_le φ P hproj hnonpoint F selected Γ p w hchar
       hdegree hsolution hregular hpoint (x i) (u₀ i) (u₁ i) hproper cap (hcap i hinodes)
   have hcount:=RCN173.sharp_incidence_bound relation Γ nodes I a w
     (componentCost P cap) (identityNodes_subset φ P F nodes x u₀ u₁ w) hI hwa han
     hagreement hfiber
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
   have hfilter:Γ.filter (fun γ↦selected γ=P₀+Polynomial.C γ*P₁)=Γ:=
     Finset.filter_eq_self.mpr (fun γ hγ↦hpencil ⟨γ,hγ⟩)
   have hΓ:Γ.card ≤ e+1:=by
     have h:=hnoPencil P₀ P₁ h₀ h₁
     rwa [hfilter] at h
   have hZ:=seed_transcendental_of_many_identities φ P F hF hH nodes x u₀ u₁ w hw
     hinj hc hnonpoint
   have hδ:=coordinateDegree_pos_of_transcendental P hproj (2:Fin 3) hZ
   have hcharge:Γ.card*(a-w) ≤
       (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
     calc
       _ ≤ (e+1)*(a-w):=Nat.mul_le_mul_right _ hΓ
       _ ≤ _:=by
         simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((e+1)*(a-w)) hδ
   omega
end
end ProximityPrize.SubmissionLower.RCN238
end PackedLegacy_J

/-! Packed from ProximityPrize.SubmissionLower.X2. -/
section PackedLegacy_X2
namespace ProximityPrize.SubmissionLower.RCN371
open RCN002
noncomputable section
variable (K:Type) [Field K]
abbrev Original:=MvPolynomial (Fin 3) K
abbrev Collected:=MvPolynomial (Fin 2) (Polynomial K)
abbrev RationalPolynomials:=MvPolynomial (Fin 2) (RatFunc K)
def collectFirst:Original K ≃ₐ[K] Collected K:=
 (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 2)).trans
   (MvPolynomial.optionEquivRight K (Fin 2))
def collect (order:Fin 3 ≃ Fin 3):Original K ≃ₐ[K] Collected K:=
 (MvPolynomial.renameEquiv K order.symm).trans (collectFirst K)
@[simp] theorem collect_C (order:Fin 3 ≃ Fin 3) (a:K):
   collect K order (MvPolynomial.C a)=MvPolynomial.C (Polynomial.C a):=by
 simp [collect,collectFirst,MvPolynomial.renameEquiv_apply]
@[simp] theorem collect_X_first (order:Fin 3 ≃ Fin 3):
   collect K order (MvPolynomial.X (order 0))=MvPolynomial.C Polynomial.X:=by
 simp [collect,collectFirst,MvPolynomial.renameEquiv_apply]
@[simp] theorem collect_X_other (order:Fin 3 ≃ Fin 3) (j:Fin 2):
   collect K order (MvPolynomial.X (order j.succ))=MvPolynomial.X j:=by
 simp [collect,collectFirst,MvPolynomial.renameEquiv_apply]
def coefficientLift (order:Fin 3 ≃ Fin 3):Polynomial K →+*Original K:=
 (collect K order).symm.toRingHom.comp MvPolynomial.C
@[simp] theorem coefficientLift_C (order:Fin 3 ≃ Fin 3) (a:K):
   coefficientLift K order (Polynomial.C a)=MvPolynomial.C a:=by
 apply (collect K order).injective
 simp [coefficientLift]
@[simp] theorem coefficientLift_X (order:Fin 3 ≃ Fin 3):
   coefficientLift K order Polynomial.X=MvPolynomial.X (order 0):=by
 apply (collect K order).injective
 simp [coefficientLift]
def rationalMap (order:Fin 3 ≃ Fin 3):Original K →+*RationalPolynomials K:=
 (MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K))).comp
   (collect K order).toRingHom
theorem rationalMap_injective (order:Fin 3 ≃ Fin 3):
   Function.Injective (rationalMap K order):=
 (MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).comp
   (collect K order).injective
theorem rationalMap_ne_zero (order:Fin 3 ≃ Fin 3) (F:Original K) (hF:F≠0):
   rationalMap K order F≠0:=by
 intro h
 apply hF
 apply rationalMap_injective K order
 simpa only [map_zero] using h
attribute [local instance] MvPolynomial.algebraMvPolynomial
def coefficientDenominators:Submonoid (Collected K):=
 (nonZeroDivisors (Polynomial K)).map MvPolynomial.C
local instance:IsLocalization (coefficientDenominators K) (RationalPolynomials K):=
 MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RatFunc K)
theorem rationalMap_eq (order:Fin 3 ≃ Fin 3) (F:Original K):
   rationalMap K order F=
     algebraMap (Collected K) (RationalPolynomials K) (collect K order F):=rfl
theorem collected_principal_isPrime (order:Fin 3 ≃ Fin 3)
   (G:Original K) (hG:Irreducible G):
   (Ideal.span ({collect K order G}:Set (Collected K))).IsPrime:=by
 have hi:Irreducible (collect K order G):=
   (MulEquiv.irreducible_iff (collect K order)).mpr hG
 exact Ideal.isPrime_span_singleton_of_prime hi.prime
section ActualComponent
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
def collectedEvaluation:Collected K →+*CoordinateField K P:=
 (coordinateEvaluation K P).toRingHom.comp (collect K order).symm.toRingHom
@[simp] theorem collectedEvaluation_collect (F:Original K):
   collectedEvaluation K order P (collect K order F)=coordinateEvaluation K P F:=by
 simp [collectedEvaluation]
@[simp] theorem collectedEvaluation_C (H:Polynomial K):
   collectedEvaluation K order P (MvPolynomial.C H)=
     Polynomial.aeval (coordinate K P (order 0)) H:=by
 have hhom:(coordinateEvaluation K P).toRingHom.comp (coefficientLift K order)=
     (Polynomial.aeval (coordinate K P (order 0))).toRingHom:=by
   apply Polynomial.ringHom_ext
   · intro a
     change coordinateEvaluation K P (coefficientLift K order (Polynomial.C a))=
       Polynomial.aeval (coordinate K P (order 0)) (Polynomial.C a)
     rw [coefficientLift_C,Polynomial.aeval_C]
     exact MvPolynomial.algHom_C (coordinateEvaluation K P) a
   · change coordinateEvaluation K P (coefficientLift K order Polynomial.X)=
       Polynomial.aeval (coordinate K P (order 0)) Polynomial.X
     rw [coefficientLift_X,Polynomial.aeval_X]
     rfl
 exact RingHom.congr_fun hhom H
theorem coefficientDenominators_disjoint_of_component
   (G:Original K) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   Disjoint (coefficientDenominators K:Set (Collected K))
     (Ideal.span ({collect K order G}:Set (Collected K)):Set (Collected K)):=by
 have hGzero:coordinateEvaluation K P G=0:=by
   change G∈RingHom.ker (coordinateEvaluation K P).toRingHom
   rw [coordinateEvaluation_ker]
   exact hmem
 rw [Set.disjoint_left]
 intro a ha hI
 obtain ⟨H,hH,rfl⟩:=Submonoid.mem_map.mp ha
 have hH0:H≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hH
 obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hI
 have hroot:Polynomial.aeval (coordinate K P (order 0)) H=0:=by
   have heval:=congrArg (collectedEvaluation K order P) hU
   simpa only [map_mul,collectedEvaluation_collect,collectedEvaluation_C,
     hGzero,zero_mul] using heval
 exact hH0 (transcendental_iff.mp ht H hroot)
theorem localized_principal_isPrime_of_component
   (G:Original K) (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   (Ideal.span ({rationalMap K order G}:Set (RationalPolynomials K))).IsPrime:=by
 have hp:=IsLocalization.isPrime_of_isPrime_disjoint
   (coefficientDenominators K) (RationalPolynomials K)
   (Ideal.span ({collect K order G}:Set (Collected K)))
   (collected_principal_isPrime K order G hG)
   (coefficientDenominators_disjoint_of_component K order P G hmem ht)
 simpa only [Ideal.map_span,Set.image_singleton, ←rationalMap_eq] using hp
theorem rationalMap_irreducible_of_component
   (G:Original K) (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   Irreducible (rationalMap K order G):=by
 exact ((Ideal.span_singleton_prime (rationalMap_ne_zero K order G hG.ne_zero)).mp
   (localized_principal_isPrime_of_component K order P G hG hmem ht)).irreducible
theorem rationalMap_dvd_iff_of_component
   (G H:Original K) (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   rationalMap K order G∣rationalMap K order H ↔ G∣H:=by
 constructor
 · intro hdiv
   have hm:algebraMap (Collected K) (RationalPolynomials K) (collect K order H)∈
       Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collect K order G}:Set (Collected K))):=by
     simpa only [Ideal.map_span,Set.image_singleton,Ideal.mem_span_singleton,
       ←rationalMap_eq] using hdiv
   have hu:collect K order H∈
       (Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collect K order G}:Set (Collected K)))).under (Collected K):=hm
   rw [IsLocalization.under_map_of_isPrime_disjoint (coefficientDenominators K)
     (RationalPolynomials K) (collected_principal_isPrime K order G hG)
     (coefficientDenominators_disjoint_of_component K order P G hmem ht)] at hu
   obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hu
   refine ⟨(collect K order).symm U,?_⟩
   apply (collect K order).injective
   simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
 · intro hdiv
   exact map_dvd (rationalMap K order) hdiv
end ActualComponent
end
end ProximityPrize.SubmissionLower.RCN371
end PackedLegacy_X2

/-! Packed from ProximityPrize.SubmissionLower.AX. -/
section PackedLegacy_AX
namespace ProximityPrize.SubmissionLower.RCN011
open RCN002 RCN005 RCN371
noncomputable section
def bivariateEquiv (A:Type) [Field A]:
   MvPolynomial (Fin 2) A ≃ₐ[A] Polynomial (Polynomial A):=
 (MvPolynomial.finSuccEquiv A 1).trans
   (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv A (Fin 1)))
@[simp] theorem bivariateEquiv_C (A:Type) [Field A] (a:A):
   bivariateEquiv A (MvPolynomial.C a)=Polynomial.C (Polynomial.C a):=by
 simp [bivariateEquiv,MvPolynomial.finSuccEquiv_apply]
@[simp] theorem bivariateEquiv_X_zero (A:Type) [Field A]:
   bivariateEquiv A (MvPolynomial.X (0:Fin 2))=Polynomial.X:=by
 simp [bivariateEquiv,MvPolynomial.finSuccEquiv_apply]
@[simp] theorem bivariateEquiv_X_one (A:Type) [Field A]:
   bivariateEquiv A (MvPolynomial.X (1:Fin 2))=Polynomial.C Polynomial.X:=by
 change Polynomial.map (MvPolynomial.uniqueAlgEquiv A (Fin 1)).toRingHom
   ((MvPolynomial.finSuccEquiv A 1) (MvPolynomial.X (0:Fin 1).succ))=
     Polynomial.C Polynomial.X
 rw [MvPolynomial.finSuccEquiv_X_succ,Polynomial.map_C]
 simp [MvPolynomial.uniqueAlgEquiv]
variable (K:Type) [Field K]
abbrev PlaneRing:=Polynomial (Polynomial (RatFunc K))
def planeMap (order:Fin 3 ≃ Fin 3):Original K →+*PlaneRing K:=
 (bivariateEquiv (RatFunc K)).toRingHom.comp (rationalMap K order)
@[simp] theorem planeMap_C (order:Fin 3 ≃ Fin 3) (a:K):
   planeMap K order (MvPolynomial.C a)=
     Polynomial.C (Polynomial.C
       (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a))):=by
 simp [planeMap,rationalMap]
@[simp] theorem planeMap_X_first (order:Fin 3 ≃ Fin 3):
   planeMap K order (MvPolynomial.X (order 0))=
     Polynomial.C (Polynomial.C
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)):=by
 simp [planeMap,rationalMap]
@[simp] theorem planeMap_X_outer (order:Fin 3 ≃ Fin 3):
   planeMap K order (MvPolynomial.X (order 1))=Polynomial.X:=by
 have h:=collect_X_other K order (0:Fin 2)
 change collect K order (MvPolynomial.X (order 1))=MvPolynomial.X 0 at h
 simp [planeMap,rationalMap,h]
@[simp] theorem planeMap_X_inner (order:Fin 3 ≃ Fin 3):
   planeMap K order (MvPolynomial.X (order 2))=Polynomial.C Polynomial.X:=by
 have h:=collect_X_other K order (1:Fin 2)
 change collect K order (MvPolynomial.X (order 2))=MvPolynomial.X 1 at h
 simp [planeMap,rationalMap,h]
theorem planeMap_injective (order:Fin 3 ≃ Fin 3):
   Function.Injective (planeMap K order):=
 (bivariateEquiv (RatFunc K)).injective.comp (rationalMap_injective K order)
section Component
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
include ht in
theorem planeMap_irreducible_of_component
   (G:Original K) (hG:Irreducible G) (hmem:G∈P):
   Irreducible (planeMap K order G):=by
 exact (MulEquiv.irreducible_iff (bivariateEquiv (RatFunc K))).mpr
   (rationalMap_irreducible_of_component K order P G hG hmem ht)
include ht in
theorem planeMap_dvd_iff_of_component
   (G H:Original K) (hG:Irreducible G) (hmem:G∈P):
   planeMap K order G∣planeMap K order H ↔ G∣H:=by
 constructor
 · rintro ⟨U,hU⟩
   have hrat:rationalMap K order G∣rationalMap K order H:=by
     refine ⟨(bivariateEquiv (RatFunc K)).symm U,?_⟩
     apply (bivariateEquiv (RatFunc K)).injective
     change bivariateEquiv (RatFunc K) (rationalMap K order H)=
       bivariateEquiv (RatFunc K) (rationalMap K order G)*U at hU
     simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
   exact (rationalMap_dvd_iff_of_component K order P G H hG hmem ht).mp hrat
 · intro hdiv
   exact map_dvd (planeMap K order) hdiv
def actualPlaneEvaluation:PlaneRing K →+*CoordinateField K P:=
 (Polynomial.evalRingHom (coordinate K P (order 1))).comp
   (Polynomial.mapRingHom
     (Polynomial.eval₂RingHom (rationalBaseEmbedding K P (order 0) ht).toRingHom
       (coordinate K P (order 2))))
@[simp] theorem actualPlaneEvaluation_C_C (a:RatFunc K):
   actualPlaneEvaluation K order P ht (Polynomial.C (Polynomial.C a))=
     rationalBaseEmbedding K P (order 0) ht a:=by
 simp [actualPlaneEvaluation]
@[simp] theorem actualPlaneEvaluation_X:
   actualPlaneEvaluation K order P ht Polynomial.X=coordinate K P (order 1):=by
 simp [actualPlaneEvaluation]
@[simp] theorem actualPlaneEvaluation_C_X:
   actualPlaneEvaluation K order P ht (Polynomial.C Polynomial.X)=
     coordinate K P (order 2):=by
 simp [actualPlaneEvaluation]
theorem actualPlaneEvaluation_comp_planeMap:
   (actualPlaneEvaluation K order P ht).comp (planeMap K order)=
     (coordinateEvaluation K P).toRingHom:=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp only [RingHom.comp_apply]
   rw [planeMap_C,actualPlaneEvaluation_C_C,
     rationalBaseEmbedding_polynomial,Polynomial.aeval_C]
   exact (MvPolynomial.algHom_C (coordinateEvaluation K P) a).symm
 · intro i
   obtain ⟨j,rfl⟩:=order.surjective i
   by_cases hj:j=0
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_first,actualPlaneEvaluation_C_C,
       rationalBaseEmbedding_polynomial,Polynomial.aeval_X]
     rfl
   by_cases hj':j=1
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_outer,actualPlaneEvaluation_X]
     rfl
   have hjtwo:j=2:=by
     apply Fin.ext
     have hjlt:=j.isLt
     have hjzero:j.val≠0:=fun h => hj (Fin.ext h)
     have hjone:j.val≠1:=fun h => hj' (Fin.ext h)
     omega
   subst j
   simp only [RingHom.comp_apply]
   rw [planeMap_X_inner,actualPlaneEvaluation_C_X]
   rfl
def actualRelationKernel:Ideal (PlaneRing K):=
 RingHom.ker (actualPlaneEvaluation K order P ht)
theorem actualRelationKernel_contract:
   (actualRelationKernel K order P ht).comap (planeMap K order)=P:=by
 rw [actualRelationKernel,RingHom.comap_ker,actualPlaneEvaluation_comp_planeMap]
 exact coordinateEvaluation_ker K P
theorem actualPlane_root_iff (F:Original K):
   actualPlaneEvaluation K order P ht (planeMap K order F)=0 ↔ F∈P:=by
 change ((actualPlaneEvaluation K order P ht).comp (planeMap K order)) F=0 ↔ F∈P
 rw [actualPlaneEvaluation_comp_planeMap]
 change F∈RingHom.ker (coordinateEvaluation K P).toRingHom ↔ F∈P
 rw [coordinateEvaluation_ker]
end Component
theorem prime_eq_of_actualRelationKernel_eq
   (order:Fin 3 ≃ Fin 3) (P Q:Ideal (Original K)) [P.IsPrime] [Q.IsPrime]
   (hP:Transcendental K (coordinate K P (order 0)))
   (hQ:Transcendental K (coordinate K Q (order 0)))
   (heq:actualRelationKernel K order P hP=actualRelationKernel K order Q hQ):
   P=Q:=by
 have h:=congrArg (Ideal.comap (planeMap K order)) heq
 simpa only [actualRelationKernel_contract] using h
theorem actualRelationKernel_family_injective
   (order:Fin 3 ≃ Fin 3) {I:Type} (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime]
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P):
   Function.Injective (fun i => actualRelationKernel K order (P i) (ht i)):=by
 intro i j hij
 apply hinj
 exact prime_eq_of_actualRelationKernel_eq K order (P i) (P j) (ht i) (ht j) hij
end
end ProximityPrize.SubmissionLower.RCN011
end PackedLegacy_AX

/-! Packed from ProximityPrize.SubmissionLower.DA. -/
section PackedLegacy_DA
namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate
open scoped BigOperators
set_option linter.constructorNameAsVariable false
local instance concreteFieldChar:
   CharP ProximityPrize.Benchmark.IRSProfile.Field 2130706433:=
 charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem derivative_ne_zero_of_pos_natDegree_lt_char
   {K:Type} [Field K] (p:ℕ) [CharP K p] (R:K[X])
   (hpos:0 < R.natDegree) (hlt:R.natDegree < p):R.derivative≠0:=by
 intro hzero
 have hc:=congrArg (fun f:K[X] => f.coeff (R.natDegree-1)) hzero
 rw [coeff_derivative] at hc
 have hsucc:R.natDegree-1+1=R.natDegree:=by omega
 rw [hsucc] at hc
 have hcastSucc:((R.natDegree-1:ℕ):K)+1=(R.natDegree:K):=by
   simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun z:ℕ => (z:K)) hsucc
 rw [hcastSucc,coeff_natDegree] at hc
 simp only [coeff_zero] at hc
 have hcast:(R.natDegree:K)≠0:=by
   intro hz
   have hdvd:p∣R.natDegree:=(CharP.cast_eq_zero_iff K p R.natDegree).mp hz
   exact (Nat.not_dvd_of_pos_of_lt hpos hlt) hdvd
 have hR:R≠0:=by
   intro hz
   simp [hz] at hpos
 exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hR) hcast) hc
theorem irreducible_isCoprime_derivative_of_natDegree_lt_char
   {K:Type} [Field K] (p:ℕ) [CharP K p] (R:K[X])
   (hirr:Irreducible R) (hpos:0 < R.natDegree) (hlt:R.natDegree < p):
   IsCoprime R R.derivative:=by
 have hdne:=derivative_ne_zero_of_pos_natDegree_lt_char p R hpos hlt
 have hddeg:R.derivative.natDegree < R.natDegree:=
   natDegree_derivative_lt (ne_of_gt hpos)
 have hnotdvd:¬ R∣R.derivative:=by
   intro hdvd
   have hle:=natDegree_le_of_dvd hdvd hdne
   omega
 by_contra hnot
 exact hnotdvd ((hirr.dvd_iff_not_isCoprime).2 hnot)
end ProximityPrize.SubmissionLower
end PackedLegacy_DA

/-! Packed from ProximityPrize.SubmissionLower.X8. -/
section PackedLegacy_X8
namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate
variable {F:Type} [Field F]
theorem bivariate_resultant_natDegree_le (B H:F[X][Y]) (n m:ℕ):
   (Polynomial.resultant B H n m).natDegree ≤
     m*degreeX B+n*degreeX H:=by
 exact ps_nat_degree_resultant_le H B m n
end ProximityPrize.SubmissionLower
end PackedLegacy_X8

/-! Packed from ProximityPrize.SubmissionLower.W2. -/
section PackedLegacy_W2
namespace ProximityPrize.SubmissionLower.RCN355
open scoped BigOperators
noncomputable section
variable {K:Type*} [Field K] [DecidableEq K]
 {ι:Type*} [Fintype ι] [DecidableEq ι]
theorem pow_card_dvd_det_of_eval_columns_eq_zero
   (M:Matrix ι ι (Polynomial K)) (alpha:K) (columns:Finset ι)
   (hzero:∀ j∈columns,∀ i,(M i j).eval alpha=0):
   (Polynomial.X-Polynomial.C alpha)^columns.card∣M.det:=by
 classical
 rw [Matrix.det_apply']
 apply Finset.dvd_sum
 intro permutation _
 have hpart:
     (∏ j∈columns,(Polynomial.X-Polynomial.C alpha))∣
       ∏ j∈columns,M (permutation j) j:=by
   apply Finset.prod_dvd_prod_of_dvd
   intro j hj
   exact Polynomial.dvd_iff_isRoot.mpr (hzero j hj (permutation j))
 have hfull:
     (∏ j∈columns,M (permutation j) j)∣
       ∏ j:ι,M (permutation j) j:=
   Finset.prod_dvd_prod_of_subset columns Finset.univ
     (fun j => M (permutation j) j) (Finset.subset_univ columns)
 have hproduct:
     (Polynomial.X-Polynomial.C alpha)^columns.card∣
       ∏ j:ι,M (permutation j) j:=by
   simpa using hpart.trans hfull
 exact dvd_mul_of_dvd_right hproduct _
theorem pow_corank_dvd_det
   (M:Matrix ι ι (Polynomial K)) (alpha:K):
   (Polynomial.X-Polynomial.C alpha)^
       (Fintype.card ι-((Polynomial.evalRingHom alpha).mapMatrix M).rank)∣
     M.det:=by
 classical
 let evalMatrix:Matrix ι ι (Polynomial K) →+*Matrix ι ι K:=
   (Polynomial.evalRingHom alpha).mapMatrix
 let constMatrix:Matrix ι ι K →+*Matrix ι ι (Polynomial K):=
   (Polynomial.C:K →+*Polynomial K).mapMatrix
 let evaluated:Matrix ι ι K:=evalMatrix M
 obtain ⟨V,U,e,hV,hU,hnormal⟩:=Matrix.exists_rank_normal_form evaluated
 let transformed:Matrix ι ι (Polynomial K):=constMatrix V*M*constMatrix U
 have heval_const (B:Matrix ι ι K):evalMatrix (constMatrix B)=B:=by
   ext i j
   simp [evalMatrix,constMatrix,RingHom.mapMatrix_apply,Matrix.map_apply]
 have heval:evalMatrix transformed=
     (Matrix.fromBlocks 1 0 0 0).submatrix e e:=by
   change evalMatrix (constMatrix V*M*constMatrix U)=_
   rw [map_mul,map_mul,heval_const,heval_const]
   exact hnormal
 let zeroEmbedding:Fin (Fintype.card ι-evaluated.rank) ↪ ι:={
   toFun:=fun j => e.symm (Sum.inr j)
   inj':=by
     intro i j hij
     exact Sum.inr.inj (e.symm.injective hij)
 }
 let zeroColumns:Finset ι:=Finset.univ.map zeroEmbedding
 have hcard:zeroColumns.card=Fintype.card ι-evaluated.rank:=by
   simp [zeroColumns]
 have hzero:∀ j∈zeroColumns,∀ i,(transformed i j).eval alpha=0:=by
   intro j hj i
   obtain ⟨j0,_,rfl⟩:=Finset.mem_map.mp hj
   change evalMatrix transformed i (e.symm (Sum.inr j0))=0
   rw [heval]
   simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
   cases e i <;> rfl
 have hVdet:IsUnit (constMatrix V).det:=
   (Matrix.isUnit_iff_isUnit_det _).mp (hV.map constMatrix)
 have hUdet:IsUnit (constMatrix U).det:=
   (Matrix.isUnit_iff_isUnit_det _).mp (hU.map constMatrix)
 have hdiv:=pow_card_dvd_det_of_eval_columns_eq_zero
   transformed alpha zeroColumns hzero
 rw [hcard] at hdiv
 change (Polynomial.X-Polynomial.C alpha)^
     (Fintype.card ι-evaluated.rank)∣
       (constMatrix V*M*constMatrix U).det at hdiv
 rw [Matrix.det_mul,Matrix.det_mul] at hdiv
 exact hVdet.dvd_mul_left.mp (hUdet.dvd_mul_right.mp hdiv)
theorem corank_le_rootMultiplicity_det
   (M:Matrix ι ι (Polynomial K)) (alpha:K) (hdet:M.det≠0):
   Fintype.card ι-((Polynomial.evalRingHom alpha).mapMatrix M).rank ≤
     M.det.rootMultiplicity alpha:=by
 exact (Polynomial.le_rootMultiplicity_iff hdet).mpr
   (pow_corank_dvd_det M alpha)
theorem sum_rootMultiplicity_le_natDegree
   (P:Polynomial K) (points:Finset K):
   (∑ alpha∈points,P.rootMultiplicity alpha) ≤ P.natDegree:=by
 classical
 have hselected:
     (∑ alpha∈points,Multiset.count alpha P.roots) ≤ P.roots.card:=by
   let all:=points ∪ P.roots.toFinset
   calc
     (∑ alpha∈points,Multiset.count alpha P.roots) ≤
         ∑ alpha∈all,Multiset.count alpha P.roots:=
       Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
     _=∑ alpha∈P.roots.toFinset,Multiset.count alpha P.roots:=by
       symm
       apply Finset.sum_subset (Finset.subset_union_right)
       intro alpha _ hnot
       exact Multiset.count_eq_zero.mpr (by simpa using hnot)
     _=P.roots.card:=Multiset.toFinset_sum_count_eq P.roots
 calc
   (∑ alpha∈points,P.rootMultiplicity alpha)=
       ∑ alpha∈points,Multiset.count alpha P.roots:=by
     apply Finset.sum_congr rfl
     intro alpha _
     exact (Polynomial.count_roots P).symm
   _ ≤ P.roots.card:=hselected
   _ ≤ P.natDegree:=Polynomial.card_roots' P
theorem sylvester_corank_le_rootMultiplicity_resultant
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (alpha:K)
   (hresultant:Polynomial.resultant P Q m n≠0):
   m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank ≤
     (Polynomial.resultant P Q m n).rootMultiplicity alpha:=by
 simpa only [Fintype.card_fin,Polynomial.resultant,
   ←Polynomial.sylvester_map_map] using
   corank_le_rootMultiplicity_det (Polynomial.sylvester P Q m n) alpha hresultant
theorem sum_sylvester_coranks_le_resultant_natDegree
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (points:Finset K)
   (hresultant:Polynomial.resultant P Q m n≠0):
   (∑ alpha∈points,(m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank)) ≤
     (Polynomial.resultant P Q m n).natDegree:=by
 calc
   _ ≤ ∑ alpha∈points,(Polynomial.resultant P Q m n).rootMultiplicity alpha:=
     Finset.sum_le_sum fun alpha _ =>
       sylvester_corank_le_rootMultiplicity_resultant P Q m n alpha hresultant
   _ ≤ (Polynomial.resultant P Q m n).natDegree:=
     sum_rootMultiplicity_le_natDegree (Polynomial.resultant P Q m n) points
end
end ProximityPrize.SubmissionLower.RCN355
end PackedLegacy_W2

/-! Packed from ProximityPrize.SubmissionLower.G5. -/
section PackedLegacy_G5
namespace ProximityPrize.SubmissionLower.RCN363
open scoped BigOperators
noncomputable section
variable {K:Type} [Field K] [DecidableEq K]
def evaluationOn (N:ℕ) (roots:Finset K):
   Polynomial.degreeLT K N →ₗ[K] (roots → K) where
 toFun P x:=(P:Polynomial K).eval (x:K)
 map_add' _ _:=funext fun _ => Polynomial.eval_add
 map_smul' _ _:=funext <| by simp
theorem evaluationOn_surjective (N:ℕ) (roots:Finset K)
   (hcard:roots.card ≤ N):Function.Surjective (evaluationOn N roots):=by
 let E:=Lagrange.funEquivDegreeLT (s:=roots) (v:=fun x:K => x)
   (Set.injOn_id (roots:Set K))
 intro values
 let small:=E.symm values
 have hsmall:(small:Polynomial K).degree < (roots.card:WithBot ℕ):=
   Polynomial.mem_degreeLT.mp small.property
 have hlarge:(small:Polynomial K).degree < (N:WithBot ℕ):=
   hsmall.trans_le (by exact_mod_cast hcard)
 refine ⟨⟨(small:Polynomial K),Polynomial.mem_degreeLT.mpr hlarge⟩,?_⟩
 change E small=values
 exact E.apply_symm_apply values
theorem finrank_degreeLT (N:ℕ):
   Module.finrank K (Polynomial.degreeLT K N)=N:=by
 simpa using Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K N)
theorem sylvester_rank_eq_finrank_range
   (p q:Polynomial K) (m n:ℕ)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n):
   (Polynomial.sylvester p q m n).rank=
     Module.finrank K (LinearMap.range (Polynomial.sylvesterMap p q hp hq)):=by
 have hmatrix:LinearMap.toMatrix
     (Polynomial.degreeLT.basisProd K m n)
     (Polynomial.degreeLT.basis K (m+n))
     (Polynomial.sylvesterMap p q hp hq)=Polynomial.sylvester p q m n:=
   Polynomial.toMatrix_sylvesterMap' p q hp hq
 rw [Matrix.rank_eq_finrank_range_toLin _
   (Polynomial.degreeLT.basis K (m+n)) (Polynomial.degreeLT.basisProd K m n)]
 rw [←hmatrix,Matrix.toLin_toMatrix]
theorem common_roots_card_le_cap
   (p q:Polynomial K) (m n:ℕ) (roots:Finset K)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n)
   (hnonzero:p≠0∨q≠0)
   (hroots:∀ x∈roots,p.eval x=0∧q.eval x=0):
   roots.card ≤ m+n:=by
 rcases hnonzero with hp0 | hq0
 · have hcard:roots.card ≤ p.natDegree:=by
     apply Polynomial.card_le_degree_of_subset_roots
     intro x hx
     exact (Polynomial.mem_roots hp0).mpr (hroots x hx).1
   omega
 · have hcard:roots.card ≤ q.natDegree:=by
     apply Polynomial.card_le_degree_of_subset_roots
     intro x hx
     exact (Polynomial.mem_roots hq0).mpr (hroots x hx).2
   omega
theorem common_roots_card_le_sylvester_corank
   (p q:Polynomial K) (m n:ℕ) (roots:Finset K)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n)
   (hnonzero:p≠0∨q≠0)
   (hroots:∀ x∈roots,p.eval x=0∧q.eval x=0):
   roots.card ≤ m+n-(Polynomial.sylvester p q m n).rank:=by
 let E:=evaluationOn (m+n) roots
 let L:=Polynomial.sylvesterMap p q hp hq
 have hsurj:Function.Surjective E:=
   evaluationOn_surjective (m+n) roots
     (common_roots_card_le_cap p q m n roots hp hq hnonzero hroots)
 have hcontain:LinearMap.range L ≤ LinearMap.ker E:=by
   rintro P ⟨input,rfl⟩
   rw [LinearMap.mem_ker]
   ext x
   change (p*(input.2:Polynomial K)+q*(input.1:Polynomial K)).eval
     (x:K)=0
   simp only [Polynomial.eval_add,Polynomial.eval_mul,
     (hroots x x.property).1,(hroots x x.property).2,zero_mul,zero_add]
 have hevalrank:Module.finrank K (LinearMap.range E)=roots.card:=by
   rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,
     Module.finrank_fintype_fun_eq_card,Fintype.card_coe]
 have hnull:=LinearMap.finrank_range_add_finrank_ker E
 rw [hevalrank,finrank_degreeLT] at hnull
 have hmono:=Submodule.finrank_mono hcontain
 have hmatrix:=sylvester_rank_eq_finrank_range p q m n hp hq
 change (Polynomial.sylvester p q m n).rank=
   Module.finrank K (LinearMap.range L) at hmatrix
 omega
theorem common_fiber_card_le_sylvester_corank
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (alpha:K) (roots:Finset K)
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hnonzero:P.map (Polynomial.evalRingHom alpha)≠0∨
     Q.map (Polynomial.evalRingHom alpha)≠0)
   (hroots:∀ beta∈roots,
     (P.map (Polynomial.evalRingHom alpha)).eval beta=0∧
     (Q.map (Polynomial.evalRingHom alpha)).eval beta=0):
   roots.card ≤ m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank:=by
 apply common_roots_card_le_sylvester_corank
 · exact Polynomial.natDegree_map_le.trans hP
 · exact Polynomial.natDegree_map_le.trans hQ
 · exact hnonzero
 · exact hroots
theorem sum_common_fiber_cards_le_resultant_natDegree
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (points:Finset K) (fibers:K → Finset K)
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (hnonzero:∀ alpha∈points,
     P.map (Polynomial.evalRingHom alpha)≠0∨
     Q.map (Polynomial.evalRingHom alpha)≠0)
   (hroots:∀ alpha∈points,∀ beta∈fibers alpha,
     (P.map (Polynomial.evalRingHom alpha)).eval beta=0∧
     (Q.map (Polynomial.evalRingHom alpha)).eval beta=0):
   (∑ alpha∈points,(fibers alpha).card) ≤
     (Polynomial.resultant P Q m n).natDegree:=by
 calc
   _ ≤ ∑ alpha∈points,(m+n-(Polynomial.sylvester
       (P.map (Polynomial.evalRingHom alpha))
       (Q.map (Polynomial.evalRingHom alpha)) m n).rank):=by
     apply Finset.sum_le_sum
     intro alpha halpha
     exact common_fiber_card_le_sylvester_corank P Q m n alpha (fibers alpha)
       hP hQ (hnonzero alpha halpha) (hroots alpha halpha)
   _ ≤ _:=RCN355.sum_sylvester_coranks_le_resultant_natDegree
     P Q m n points hresultant
theorem sum_common_fiber_cards_le_bidegree_bound
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (points:Finset K) (fibers:K → Finset K)
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (hnonzero:∀ alpha∈points,
     P.map (Polynomial.evalRingHom alpha)≠0∨
     Q.map (Polynomial.evalRingHom alpha)≠0)
   (hroots:∀ alpha∈points,∀ beta∈fibers alpha,
     (P.map (Polynomial.evalRingHom alpha)).eval beta=0∧
     (Q.map (Polynomial.evalRingHom alpha)).eval beta=0):
   (∑ alpha∈points,(fibers alpha).card) ≤
     n*Polynomial.Bivariate.degreeX P+m*Polynomial.Bivariate.degreeX Q:=by
 exact Nat.le_trans
   (sum_common_fiber_cards_le_resultant_natDegree P Q m n points fibers
     hP hQ hresultant hnonzero hroots)
   (bivariate_resultant_natDegree_le (F:=K) P Q m n)
def pointFiber (points:Finset (K × K)) (alpha:K):Finset K:=
 (points.filter (fun point => point.1=alpha)).image Prod.snd
theorem card_eq_sum_pointFiber (points:Finset (K × K)):
   points.card=∑ alpha∈points.image Prod.fst,(pointFiber points alpha).card:=by
 rw [Finset.card_eq_sum_card_image Prod.fst points]
 apply Finset.sum_congr rfl
 intro alpha _
 change (points.filter (fun point => point.1=alpha)).card=
   ((points.filter (fun point => point.1=alpha)).image Prod.snd).card
 symm
 apply Finset.card_image_of_injOn
 intro u hu v hv huv
 apply Prod.ext
 · exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
 · exact huv
theorem common_points_card_le_bidegree_bound
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (points:Finset (K × K))
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (hnonzero:∀ point∈points,
     P.map (Polynomial.evalRingHom point.1)≠0∨
     Q.map (Polynomial.evalRingHom point.1)≠0)
   (hroots:∀ point∈points,
     (P.map (Polynomial.evalRingHom point.1)).eval point.2=0∧
     (Q.map (Polynomial.evalRingHom point.1)).eval point.2=0):
   points.card ≤
     n*Polynomial.Bivariate.degreeX P+m*Polynomial.Bivariate.degreeX Q:=by
 rw [card_eq_sum_pointFiber points]
 apply sum_common_fiber_cards_le_bidegree_bound P Q m n
   (points.image Prod.fst) (pointFiber points) hP hQ hresultant
 · intro alpha halpha
   obtain ⟨point,hpoint,rfl⟩:=Finset.mem_image.mp halpha
   exact hnonzero point hpoint
 · intro alpha _ beta hbeta
   obtain ⟨point,hpoint,rfl⟩:=Finset.mem_image.mp hbeta
   obtain ⟨hpoint,hfirst⟩:=Finset.mem_filter.mp hpoint
   simpa only [hfirst] using hroots point hpoint
end
end ProximityPrize.SubmissionLower.RCN363
end PackedLegacy_G5

/-! Packed from ProximityPrize.SubmissionLower.W6. -/
section PackedLegacy_W6
namespace ProximityPrize.SubmissionLower.RCN362
noncomputable section
variable {K:Type} [Field K] [DecidableEq K]
theorem inner_linear_C_dvd_of_specialization_eq_zero
   (P:Polynomial (Polynomial K)) (alpha:K)
   (hzero:P.map (Polynomial.evalRingHom alpha)=0):
   Polynomial.C (Polynomial.X-Polynomial.C alpha)∣P:=by
 rw [Polynomial.C_dvd_iff_dvd_coeff]
 intro i
 apply Polynomial.dvd_iff_isRoot.mpr
 have hcoeff:=congrArg (fun Q:Polynomial K => Q.coeff i) hzero
 simpa using hcoeff
theorem primitive_specialization_ne_zero
   (P:Polynomial (Polynomial K)) (hprimitive:P.IsPrimitive) (alpha:K):
   P.map (Polynomial.evalRingHom alpha)≠0:=by
 intro hzero
 exact Polynomial.not_isUnit_X_sub_C alpha
   (hprimitive _ (inner_linear_C_dvd_of_specialization_eq_zero P alpha hzero))
theorem primitive_irreducible_dvd_of_resultant_eq_zero
   (P Q:Polynomial (Polynomial K))
   (hprimitive:P.IsPrimitive) (hirreducible:Irreducible P)
   (hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree=0):P∣Q:=by
 classical
 let F:=FractionRing (Polynomial K)
 let f:Polynomial K →+*F:=algebraMap (Polynomial K) F
 have hf:Function.Injective f:=IsFractionRing.injective (Polynomial K) F
 have hPdegree:(P.map f).natDegree=P.natDegree:=
   Polynomial.natDegree_map_eq_of_injective hf P
 have hQdegree:(Q.map f).natDegree=Q.natDegree:=
   Polynomial.natDegree_map_eq_of_injective hf Q
 have hfixed:Polynomial.resultant (P.map f) (Q.map f)
     P.natDegree Q.natDegree=0:=by
   rw [Polynomial.resultant_map_map,hresultant,map_zero]
 have hresF:Polynomial.resultant (P.map f) (Q.map f)=0:=by
   simpa only [hPdegree,hQdegree] using hfixed
 have hnotCoprime:¬ IsCoprime (P.map f) (Q.map f):=
   (Polynomial.resultant_eq_zero_iff.mp hresF).2
 have hirreducibleF:Irreducible (P.map f):=
   hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hirreducible
 have hdivF:P.map f∣Q.map f:=
   (Irreducible.dvd_iff_not_isCoprime hirreducibleF).mpr hnotCoprime
 exact hprimitive.dvd_of_fraction_map_dvd_fraction_map hdivF
theorem irreducible_resultant_ne_zero_of_not_dvd
   (P Q:Polynomial (Polynomial K)) (hirreducible:Irreducible P)
   (hdegree:0 < P.natDegree) (hproper:¬ P∣Q):
   Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=by
 intro hresultant
 exact hproper (primitive_irreducible_dvd_of_resultant_eq_zero P Q
   (hirreducible.isPrimitive (Nat.ne_of_gt hdegree)) hirreducible hresultant)
end
end ProximityPrize.SubmissionLower.RCN362
end PackedLegacy_W6

/- Library component IT is loaded from Mathlib.RingTheory.Polynomial.ContentIdeal. -/

/-! Packed from ProximityPrize.SubmissionLower.G3. -/
section PackedLegacy_G3
namespace ProximityPrize.SubmissionLower.RCN360
noncomputable section
variable {K L:Type} [Field K] [Field L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq L:=Classical.decEq L
def bimap (f:K →+*L) (P:Polynomial (Polynomial K)):
   Polynomial (Polynomial L):=P.map (Polynomial.mapRingHom f)
theorem bimap_primitive (f:K →+*L)
   (P:Polynomial (Polynomial K)) (hP:P.IsPrimitive):
   (bimap f P).IsPrimitive:=by
 apply Polynomial.isPrimitive_of_contentIdeal_eq_top
 rw [bimap,Polynomial.contentIdeal_map_eq_map_contentIdeal,
   (Polynomial.isPrimitive_iff_contentIdeal_eq_top P).mp hP,Ideal.map_top]
theorem bimap_natDegree_le (f:K →+*L) (P:Polynomial (Polynomial K)):
   (bimap f P).natDegree ≤ P.natDegree:=
 Polynomial.natDegree_map_le
theorem bimap_degreeX_le (f:K →+*L) (P:Polynomial (Polynomial K)):
   Polynomial.Bivariate.degreeX (bimap f P) ≤ Polynomial.Bivariate.degreeX P:=by
 classical
 unfold Polynomial.Bivariate.degreeX
 apply Finset.sup_le
 intro j _
 rw [show (bimap f P).coeff j=(P.coeff j).map f by simp [bimap]]
 exact Polynomial.natDegree_map_le.trans
   (Polynomial.Bivariate.coeff_natDegree_le_degreeX P j)
theorem bimap_specialization (f:K →+*L)
   (P:Polynomial (Polynomial K)) (x:L):
   (bimap f P).map (Polynomial.evalRingHom x)=
     P.map (Polynomial.eval₂RingHom f x):=by
 ext j
 simp [bimap,Polynomial.eval_map]
theorem bimap_eval_natural (f:K →+*L)
   (P:Polynomial (Polynomial K)) (x y:K):
   ((bimap f P).map (Polynomial.evalRingHom (f x))).eval (f y)=
     f ((P.map (Polynomial.evalRingHom x)).eval y):=by
 have h:(bimap f P).map (Polynomial.evalRingHom (f x))=
     (P.map (Polynomial.evalRingHom x)).map f:=by
   ext j
   simp [bimap,Polynomial.eval_map,Polynomial.eval₂_at_apply]
 rw [h,Polynomial.eval_map_apply]
theorem bimap_comp {M:Type} [Field M]
   (f:K →+*L) (g:L →+*M) (P:Polynomial (Polynomial K)):
   bimap g (bimap f P)=bimap (g.comp f) P:=by
 ext j i
 simp [bimap]
theorem bimap_resultant_ne_zero (f:K →+*L)
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (hres:Polynomial.resultant P Q m n≠0):
   Polynomial.resultant (bimap f P) (bimap f Q) m n≠0:=by
 unfold bimap
 rw [Polynomial.resultant_map_map]
 intro hzero
 apply hres
 apply Polynomial.map_injective f f.injective
 simpa only [Polynomial.coe_mapRingHom,Polynomial.map_zero] using hzero
theorem bimap_specialization_ne_zero (f:K →+*L)
   (P:Polynomial (Polynomial K)) (hP:P.IsPrimitive) (x:L):
   (bimap f P).map (Polynomial.evalRingHom x)≠0:=by
 classical
 exact RCN362.primitive_specialization_ne_zero
   (bimap f P) (bimap_primitive f P hP) x
theorem common_points_card_le_after_extension (f:K →+*L)
   (P Q:Polynomial (Polynomial K)) (points:Finset (L × L))
   (hP:Irreducible P) (hdeg:0 < P.natDegree) (hproper:¬ P∣Q)
   (hroots:∀ point∈points,
     ((bimap f P).map (Polynomial.evalRingHom point.1)).eval point.2=0∧
     ((bimap f Q).map (Polynomial.evalRingHom point.1)).eval point.2=0):
   points.card ≤ Q.natDegree*Polynomial.Bivariate.degreeX P+
     P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 have hcount:=RCN363.common_points_card_le_bidegree_bound
   (bimap f P) (bimap f Q) P.natDegree Q.natDegree points
   (bimap_natDegree_le f P) (bimap_natDegree_le f Q)
   (bimap_resultant_ne_zero f P Q P.natDegree Q.natDegree
     (RCN362.irreducible_resultant_ne_zero_of_not_dvd
       P Q hP hdeg hproper))
   (fun point _ => Or.inl (bimap_specialization_ne_zero f P
     (hP.isPrimitive (Nat.ne_of_gt hdeg)) point.1)) hroots
 exact hcount.trans (Nat.add_le_add
   (Nat.mul_le_mul_left _ (bimap_degreeX_le f P))
   (Nat.mul_le_mul_left _ (bimap_degreeX_le f Q)))
end
end ProximityPrize.SubmissionLower.RCN360
end PackedLegacy_G3

/-! Packed from ProximityPrize.SubmissionLower.G6. -/
section PackedLegacy_G6
namespace ProximityPrize.SubmissionLower.RCN364
noncomputable section
variable {K L:Type} [Field K] [Field L] [Algebra K L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq L:=Classical.decEq L
theorem integral_and_separable_of_small_annihilator
   (p:ℕ) [CharP K p] (f:Polynomial K) (x:L)
   (hf:f≠0) (hx:Polynomial.aeval x f=0) (hdegree:f.natDegree < p):
   IsIntegral K x∧IsSeparable K x:=by
 have hint:IsIntegral K x:=IsAlgebraic.isIntegral ⟨f,hf,hx⟩
 have hmin:(minpoly K x).natDegree ≤ f.natDegree:=
   Polynomial.natDegree_le_of_dvd (minpoly.dvd K x hx) hf
 refine ⟨hint,?_⟩
 change (minpoly K x).Separable
 apply (Polynomial.separable_def _).mpr
 exact irreducible_isCoprime_derivative_of_natDegree_lt_char p (minpoly K x)
   (minpoly.irreducible hint) (minpoly.natDegree_pos hint) (hmin.trans_lt hdegree)
theorem resultant_aeval_eq_zero_of_common_root
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (hPdegree:P.natDegree ≤ m) (hQdegree:Q.natDegree ≤ n)
   (hpositive:m≠0∨n≠0) (y r:L)
   (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r P=0)
   (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r Q=0):
   Polynomial.aeval y (Polynomial.resultant P Q m n)=0:=by
 obtain ⟨U,V,_,_,hidentity⟩:=Polynomial.exists_mul_add_mul_eq_C_resultant
   P Q hPdegree hQdegree hpositive
 have heval:=congrArg
   (fun F:Polynomial (Polynomial K) =>
     Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r F) hidentity
 simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,
   hP,hQ,zero_mul,zero_add] at heval
 exact heval.symm
theorem finite_separable_of_two_generators (y r:L)
   (hy:IsSeparable K y) (hr:IsSeparable K r)
   (hgenerate:IntermediateField.adjoin K ({y,r}:Set L)=⊤):
   FiniteDimensional K L∧Algebra.IsSeparable K L:=by
 letI:FiniteDimensional K (IntermediateField.adjoin K ({y,r}:Set L)):=
   IntermediateField.finiteDimensional_adjoin_pair hy.isIntegral hr.isIntegral
 letI:Algebra.IsSeparable K (IntermediateField.adjoin K ({y,r}:Set L)):=
   IntermediateField.isSeparable_adjoin_pair_of_isSeparable K L hy hr
 letI:FiniteDimensional K (⊤:IntermediateField K L):=by
   rw [←hgenerate]
   infer_instance
 have hsepTop:Algebra.IsSeparable K (⊤:IntermediateField K L):=by
   rw [←hgenerate]
   infer_instance
 have hfinite:FiniteDimensional K L:=Module.Finite.of_surjective
   (IntermediateField.topEquiv (F:=K) (E:=L)).toLinearMap
   (IntermediateField.topEquiv (F:=K) (E:=L)).surjective
 exact ⟨hfinite,(IntermediateField.isSeparable_top (F:=K) (E:=L)).mp hsepTop⟩
theorem finite_separable_of_proper_plane_roots
   (p:ℕ) [CharP K p] (P Q:Polynomial (Polynomial K))
   (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q) (hRdegree:P.natDegree < p)
   (hresultantDegree:(Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree < p)
   (y r:L)
   (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r P=0)
   (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r Q=0)
   (hgenerate:IntermediateField.adjoin K ({y,r}:Set L)=⊤):
   FiniteDimensional K L∧Algebra.IsSeparable K L:=by
 classical
 have hresne:=RCN362.irreducible_resultant_ne_zero_of_not_dvd
   P Q hirreducible hpositive hproper
 have hresroot:=resultant_aeval_eq_zero_of_common_root P Q
   P.natDegree Q.natDegree le_rfl le_rfl (Or.inl (Nat.ne_of_gt hpositive)) y r hP hQ
 obtain ⟨_,hySeparable⟩:=integral_and_separable_of_small_annihilator p
   (Polynomial.resultant P Q P.natDegree Q.natDegree) y hresne hresroot hresultantDegree
 let S:IntermediateField K L:=IntermediateField.adjoin K {y}
 let yS:S:=⟨y,IntermediateField.mem_adjoin_simple_self K y⟩
 letI:DecidableEq S:=Classical.decEq S
 letI:CharP S p:=charP_of_injective_algebraMap (algebraMap K S).injective p
 let g:Polynomial K →+*S:=Polynomial.eval₂RingHom (algebraMap K S) yS
 let Py:Polynomial S:=P.map g
 have hPyne:Py≠0:=by
   have h:=RCN360.bimap_specialization_ne_zero
     (algebraMap K S) P (hirreducible.isPrimitive (Nat.ne_of_gt hpositive)) yS
   rw [RCN360.bimap_specialization] at h
   exact h
 have hPydegree:Py.natDegree < p:=Polynomial.natDegree_map_le.trans_lt hRdegree
 have hcoefficient:(algebraMap S L).comp g=
     Polynomial.eval₂RingHom (algebraMap K L) y:=by
   apply Polynomial.ringHom_ext
   · intro c
     change algebraMap S L (Polynomial.eval₂ (algebraMap K S) yS (Polynomial.C c))=
       Polynomial.eval₂ (algebraMap K L) y (Polynomial.C c)
     rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
     exact (IsScalarTower.algebraMap_apply K S L c).symm
   · change algebraMap S L (Polynomial.eval₂ (algebraMap K S) yS Polynomial.X)=
       Polynomial.eval₂ (algebraMap K L) y Polynomial.X
     rw [Polynomial.eval₂_X,Polynomial.eval₂_X]
     rfl
 have hPyroot:Polynomial.aeval r Py=0:=by
   change Polynomial.eval₂ (algebraMap S L) r (P.map g)=0
   rw [Polynomial.eval₂_map,hcoefficient]
   exact hP
 obtain ⟨_,hrSeparable⟩:=integral_and_separable_of_small_annihilator p
   Py r hPyne hPyroot hPydegree
 letI:Algebra.IsSeparable K S:=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L).mpr hySeparable
 have hrOverK:IsSeparable K r:=
   IsSeparable.of_algebra_isSeparable_of_isSeparable K hrSeparable
 exact finite_separable_of_two_generators y r hySeparable hrOverK hgenerate
end
end ProximityPrize.SubmissionLower.RCN364
end PackedLegacy_G6

/-! Packed from ProximityPrize.SubmissionLower.G4. -/
section PackedLegacy_G4
namespace ProximityPrize.SubmissionLower.RCN361
open RCN360
noncomputable section
section Evaluation
variable (K E:Type) [Field K] [Field E] [Algebra K E]
def planeEval (y r:E):Polynomial (Polynomial K) →+*E:=
 (Polynomial.evalRingHom r).comp
   (Polynomial.mapRingHom (Polynomial.eval₂RingHom (algebraMap K E) y))
def relationIdeal (y r:E):Ideal (Polynomial (Polynomial K)):=
 RingHom.ker (planeEval K E y r)
theorem planeEval_eq (y r:E) (P:Polynomial (Polynomial K)):
   planeEval K E y r P=
     ((bimap (algebraMap K E) P).map (Polynomial.evalRingHom y)).eval r:=by
 simp only [planeEval,RingHom.comp_apply,Polynomial.coe_mapRingHom,
   Polynomial.coe_evalRingHom]
 rw [bimap_specialization]
variable (Ω:Type) [Field Ω] [Algebra K Ω]
theorem algHom_planeEval (φ:E →ₐ[K] Ω) (y r:E)
   (P:Polynomial (Polynomial K)):
   φ (planeEval K E y r P)=planeEval K Ω (φ y) (φ r) P:=by
 rw [planeEval_eq,planeEval_eq]
 have h:=bimap_eval_natural φ.toRingHom
   (bimap (algebraMap K E) P) y r
 have hcomp:φ.toRingHom.comp (algebraMap K E)=algebraMap K Ω:=by
   ext a
   exact φ.commutes a
 rw [bimap_comp,hcomp] at h
 exact h.symm
theorem algHom_eq_of_generating_pair (y r:E)
   (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (φ ψ:E →ₐ[K] Ω) (hy:φ y=ψ y) (hr:φ r=ψ r):φ=ψ:=by
 apply AlgHom.ext
 intro x
 have hx:x∈IntermediateField.adjoin K ({y,r}:Set E):=by
   rw [hgen]
   trivial
 exact IntermediateField.adjoin_induction K
   (p:=fun a _ => φ a=ψ a)
   (fun a ha => by
     rcases Set.mem_insert_iff.mp ha with h | h
     · simpa only [h] using hy
     · simpa only [Set.mem_singleton_iff.mp h] using hr)
   (fun a => by rw [φ.commutes,ψ.commutes])
   (fun a b _ _ ha hb => by simp only [map_add,ha,hb])
   (fun a _ ha => by simp only [map_inv₀,ha])
   (fun a b _ _ ha hb => by simp only [map_mul,ha,hb]) hx
theorem embedding_pair_injective (y r:E)
   (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤):
   Function.Injective (fun φ:E →ₐ[K] Ω => (φ y,φ r)):=by
 intro φ ψ h
 exact algHom_eq_of_generating_pair K E Ω y r hgen φ ψ
   (congrArg Prod.fst h) (congrArg Prod.snd h)
variable (E':Type) [Field E'] [Algebra K E']
theorem relationIdeal_eq_of_embedding_pairs_eq
   (y r:E) (y' r':E') (φ:E →ₐ[K] Ω) (ψ:E' →ₐ[K] Ω)
   (hy:φ y=ψ y') (hr:φ r=ψ r'):
   relationIdeal K E y r=relationIdeal K E' y' r':=by
 apply Ideal.ext
 intro P
 change planeEval K E y r P=0 ↔ planeEval K E' y' r' P=0
 have heq:φ (planeEval K E y r P)=ψ (planeEval K E' y' r' P):=by
   rw [algHom_planeEval,algHom_planeEval,hy,hr]
 constructor
 · intro h
   apply ψ.injective
   simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,h,map_zero] using heq.symm
 · intro h
   apply φ.injective
   simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,h,map_zero] using heq
end Evaluation
section SingleField
variable (K E:Type) [Field K] [Field E] [Algebra K E]
 [FiniteDimensional K E] [Algebra.IsSeparable K E]
theorem finrank_le_planar_bound
   (P Q:Polynomial (Polynomial K))
   (hP:Irreducible P) (hdeg:0 < P.natDegree) (hproper:¬ P∣Q)
   (y r:E) (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (hPy:planeEval K E y r P=0) (hQy:planeEval K E y r Q=0):
   Module.finrank K E ≤ Q.natDegree*Polynomial.Bivariate.degreeX P+
     P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 let Ω:=AlgebraicClosure E
 letI:Fintype (E →ₐ[K] Ω):=Fintype.ofFinite _
 let points:Finset (Ω × Ω):=Finset.univ.image (fun φ:E →ₐ[K] Ω => (φ y,φ r))
 have hcard:points.card=Module.finrank K E:=by
   rw [Finset.card_image_of_injective _ (embedding_pair_injective K E Ω y r hgen),
     Finset.card_univ,Fintype.card_eq_nat_card]
   exact Field.finSepDegree_eq_finrank_of_isSeparable K E
 rw [←hcard]
 apply common_points_card_le_after_extension (algebraMap K Ω) P Q points hP hdeg hproper
 intro point hp
 obtain ⟨φ,_,rfl⟩:=Finset.mem_image.mp hp
 constructor
 · rw [←planeEval_eq]
   rw [←algHom_planeEval K E Ω φ y r P,hPy,map_zero]
 · rw [←planeEval_eq]
   rw [←algHom_planeEval K E Ω φ y r Q,hQy,map_zero]
end SingleField
section FiniteFamily
variable (K:Type) [Field K]
 {I:Type} [Fintype I] (E:I → Type)
 [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 [∀ i,FiniteDimensional K (E i)] [∀ i,Algebra.IsSeparable K (E i)]
theorem sum_finrank_le_planar_bound
   (P Q:Polynomial (Polynomial K))
   (hP:Irreducible P) (hdeg:0 < P.natDegree) (hproper:¬ P∣Q)
   (y r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin K ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i => relationIdeal K (E i) (y i) (r i)))
   (hPy:∀ i,planeEval K (E i) (y i) (r i) P=0)
   (hQy:∀ i,planeEval K (E i) (y i) (r i) Q=0):
   (∑ i,Module.finrank K (E i)) ≤
     Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 let Ω:=AlgebraicClosure K
 letI:∀ i,Fintype (E i →ₐ[K] Ω):=fun i => Fintype.ofFinite _
 let pair:(Σ i,E i →ₐ[K] Ω) → Ω × Ω:=
   fun a => (a.2 (y a.1),a.2 (r a.1))
 have hinj:Function.Injective pair:=by
   rintro ⟨i,φ⟩ ⟨j,ψ⟩ h
   have hij:i=j:=hkernels
     (relationIdeal_eq_of_embedding_pairs_eq K (E i) Ω (E j)
       (y i) (r i) (y j) (r j) φ ψ (congrArg Prod.fst h) (congrArg Prod.snd h))
   subst j
   have heq:φ=ψ:=algHom_eq_of_generating_pair K (E i) Ω
     (y i) (r i) (hgen i) φ ψ (congrArg Prod.fst h) (congrArg Prod.snd h)
   exact congrArg (Sigma.mk i) heq
 let points:Finset (Ω × Ω):=Finset.univ.image pair
 have hcard:points.card=∑ i,Module.finrank K (E i):=by
   rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_sigma]
   apply Finset.sum_congr rfl
   intro i _
   rw [Fintype.card_eq_nat_card,
     ←Field.finSepDegree_eq_of_isAlgClosed K (E i) Ω,
     Field.finSepDegree_eq_finrank_of_isSeparable]
 rw [←hcard]
 apply common_points_card_le_after_extension (algebraMap K Ω) P Q points hP hdeg hproper
 intro point hp
 obtain ⟨⟨i,φ⟩,_,rfl⟩:=Finset.mem_image.mp hp
 change
   ((bimap (algebraMap K Ω) P).map (Polynomial.evalRingHom (φ (y i)))).eval (φ (r i))=0∧
   ((bimap (algebraMap K Ω) Q).map (Polynomial.evalRingHom (φ (y i)))).eval (φ (r i))=0
 constructor
 · rw [←planeEval_eq, ←algHom_planeEval K (E i) Ω φ (y i) (r i) P,hPy i,map_zero]
 · rw [←planeEval_eq, ←algHom_planeEval K (E i) Ω φ (y i) (r i) Q,hQy i,map_zero]
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN361
end PackedLegacy_G4

/-! Packed from ProximityPrize.SubmissionLower.W7. -/
section PackedLegacy_W7
namespace ProximityPrize.SubmissionLower.RCN365
open RCN361
noncomputable section
section SingleField
variable (K E:Type) [Field K] [Field E] [Algebra K E]
theorem planeEval_eq_eval₂ (y r:E) (P:Polynomial (Polynomial K)):
   planeEval K E y r P=
     Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K E) y) r P:=by
 change (P.map (Polynomial.eval₂RingHom (algebraMap K E) y)).eval r=_
 rw [Polynomial.eval_map]
theorem finite_separable_finrank_le_planar_bound
   (p:ℕ) [CharP K p] (P Q:Polynomial (Polynomial K))
   (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q) (hRdegree:P.natDegree < p)
   (hresultantDegree:(Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree < p)
   (y r:E)
   (hgenerate:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (hP:planeEval K E y r P=0) (hQ:planeEval K E y r Q=0):
   FiniteDimensional K E∧Algebra.IsSeparable K E∧
     Module.finrank K E ≤ Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 have hPeval:Polynomial.eval₂
     (Polynomial.eval₂RingHom (algebraMap K E) y) r P=0:=by
   rw [←planeEval_eq_eval₂]
   exact hP
 have hQeval:Polynomial.eval₂
     (Polynomial.eval₂RingHom (algebraMap K E) y) r Q=0:=by
   rw [←planeEval_eq_eval₂]
   exact hQ
 have hfields:=RCN364.finite_separable_of_proper_plane_roots
   p P Q hirreducible hpositive hproper hRdegree hresultantDegree y r hPeval hQeval hgenerate
 letI:FiniteDimensional K E:=hfields.1
 letI:Algebra.IsSeparable K E:=hfields.2
 exact ⟨hfields.1,hfields.2,
   RCN361.finrank_le_planar_bound K E P Q
     hirreducible hpositive hproper y r hgenerate hP hQ⟩
end SingleField
section FiniteFamily
variable (K:Type) [Field K]
 {I:Type} [Fintype I] (E:I → Type)
 [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
theorem finite_separable_sum_finrank_le_planar_bound
   (p:ℕ) [CharP K p] (P Q:Polynomial (Polynomial K))
   (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q) (hRdegree:P.natDegree < p)
   (hresultantDegree:(Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree < p)
   (y r:∀ i,E i)
   (hgenerate:∀ i,IntermediateField.adjoin K ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i => relationIdeal K (E i) (y i) (r i)))
   (hP:∀ i,planeEval K (E i) (y i) (r i) P=0)
   (hQ:∀ i,planeEval K (E i) (y i) (r i) Q=0):
   (∀ i,FiniteDimensional K (E i)∧Algebra.IsSeparable K (E i))∧
     (∑ i,Module.finrank K (E i)) ≤
       Q.natDegree*Polynomial.Bivariate.degreeX P+
         P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 have hfields:∀ i,FiniteDimensional K (E i)∧Algebra.IsSeparable K (E i):=by
   intro i
   have h:=finite_separable_finrank_le_planar_bound K (E i)
     p P Q hirreducible hpositive hproper hRdegree hresultantDegree
     (y i) (r i) (hgenerate i) (hP i) (hQ i)
   exact ⟨h.1,h.2.1⟩
 letI:∀ i,FiniteDimensional K (E i):=fun i => (hfields i).1
 letI:∀ i,Algebra.IsSeparable K (E i):=fun i => (hfields i).2
 exact ⟨hfields,
   RCN361.sum_finrank_le_planar_bound K E P Q
     hirreducible hpositive hproper y r hgenerate hkernels hP hQ⟩
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN365
end PackedLegacy_W7

/-! Packed from ProximityPrize.SubmissionLower.X4. -/
section PackedLegacy_X4
namespace ProximityPrize.SubmissionLower.RCN010
open RCN002 RCN005
 RCN371 RCN011
noncomputable section
theorem order_cover (order:Fin 3 ≃ Fin 3) (l:Fin 3):
   l=order 0∨l=order 2∨l=order 1:=by
 have h:∀ i:Fin 3,i=0∨i=2∨i=1:=by decide
 rcases h (order.symm l) with hl | hl | hl
 · exact Or.inl (by simpa only [Equiv.apply_symm_apply] using congrArg order hl)
 · exact Or.inr (Or.inl (by simpa only [Equiv.apply_symm_apply] using congrArg order hl))
 · exact Or.inr (Or.inr (by simpa only [Equiv.apply_symm_apply] using congrArg order hl))
variable (K:Type) [Field K]
section Component
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
theorem actual_generators:
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   IntermediateField.adjoin (RatFunc K)
     ({coordinate K P (order 2),coordinate K P (order 1)}:Set (CoordinateField K P))=⊤:=
 adjoin_two_coordinates_over_ratFunc_eq_top K P (order 0) (order 2) (order 1) ht
   (order_cover order)
theorem actual_finite_separable_finrank_bound
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hpositive:0 < (planeMap K order G).natDegree)
   (hRdegree:(planeMap K order G).natDegree < p)
   (hresultantDegree:(Polynomial.resultant (planeMap K order G) (planeMap K order H)
     (planeMap K order G).natDegree (planeMap K order H).natDegree).natDegree < p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
     Module.finrank (RatFunc K) (CoordinateField K P) ≤
       (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H):=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
 letI:CharP (RatFunc K) p:=
   charP_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
 have hirr:=planeMap_irreducible_of_component
   (K:=K) (order:=order) (P:=P) (ht:=ht) G hG hGmem
 have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
   intro h
   exact hproper ((planeMap_dvd_iff_of_component
     (K:=K) (order:=order) (P:=P) (ht:=ht) G H hG hGmem).mp h)
 have hGroots:RCN361.planeEval (RatFunc K) (CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1)) (planeMap K order G)=0:=by
   change actualPlaneEvaluation K order P ht (planeMap K order G)=0
   exact (actualPlane_root_iff K order P ht G).mpr hGmem
 have hHroots:RCN361.planeEval (RatFunc K) (CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1)) (planeMap K order H)=0:=by
   change actualPlaneEvaluation K order P ht (planeMap K order H)=0
   exact (actualPlane_root_iff K order P ht H).mpr hHmem
 exact RCN365.finite_separable_finrank_le_planar_bound
   (RatFunc K) (CoordinateField K P) p (planeMap K order G) (planeMap K order H)
   hirr hpositive hproperPlane hRdegree hresultantDegree
   (coordinate K P (order 2)) (coordinate K P (order 1))
   (actual_generators K order P ht) hGroots hHroots
end Component
section FiniteFamily
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem actual_finite_separable_sum_finrank_bound
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (hpositive:0 < (planeMap K order G).natDegree)
   (hRdegree:(planeMap K order G).natDegree < p)
   (hresultantDegree:(Polynomial.resultant (planeMap K order G) (planeMap K order H)
     (planeMap K order G).natDegree (planeMap K order H).natDegree).natDegree < p):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H):=by
 classical
 letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
   fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   letI:CharP (RatFunc K) p:=
     charP_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
   have hirr:=planeMap_irreducible_of_component
     (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀) G hG (hGmem i₀)
   have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
     intro h
     exact hproper ((planeMap_dvd_iff_of_component
       (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀) G H hG (hGmem i₀)).mp h)
   have hkernels:Function.Injective (fun i =>
       RCN361.relationIdeal (RatFunc K) (CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))):=by
     change Function.Injective (fun i => actualRelationKernel K order (P i) (ht i))
     exact actualRelationKernel_family_injective K order P ht hinj
   have hGroots:∀ i,
       RCN361.planeEval (RatFunc K) (CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))
           (planeMap K order G)=0:=by
     intro i
     change actualPlaneEvaluation K order (P i) (ht i) (planeMap K order G)=0
     exact (actualPlane_root_iff K order (P i) (ht i) G).mpr (hGmem i)
   have hHroots:∀ i,
       RCN361.planeEval (RatFunc K) (CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))
           (planeMap K order H)=0:=by
     intro i
     change actualPlaneEvaluation K order (P i) (ht i) (planeMap K order H)=0
     exact (actualPlane_root_iff K order (P i) (ht i) H).mpr (hHmem i)
   exact RCN365.finite_separable_sum_finrank_le_planar_bound
     (RatFunc K) (fun i => CoordinateField K (P i)) p
     (planeMap K order G) (planeMap K order H) hirr hpositive hproperPlane
     hRdegree hresultantDegree
     (fun i => coordinate K (P i) (order 2)) (fun i => coordinate K (P i) (order 1))
     (fun i => actual_generators K order (P i) (ht i)) hkernels hGroots hHroots
 · letI:IsEmpty I:=⟨fun i => hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN010
end PackedLegacy_X4

/-! Packed from ProximityPrize.SubmissionLower.H1. -/
section PackedLegacy_H1
namespace ProximityPrize.SubmissionLower.RCN009
open RCN371 RCN011
noncomputable section
variable (K:Type) [Field K]
section FirstCoordinate
variable {A:Type} [Field A]
def firstMap (φ:Polynomial K →+*A):
   MvPolynomial (Fin 3) K →+*MvPolynomial (Fin 2) A:=
 (MvPolynomial.map φ).comp (collectFirst K).toRingHom
@[simp] theorem firstMap_C (φ:Polynomial K →+*A) (a:K):
   firstMap K φ (MvPolynomial.C a)=MvPolynomial.C (φ (Polynomial.C a)):=by
 simp [firstMap,collectFirst,MvPolynomial.renameEquiv_apply]
@[simp] theorem firstMap_X_zero (φ:Polynomial K →+*A):
   firstMap K φ (MvPolynomial.X (0:Fin 3))=MvPolynomial.C (φ Polynomial.X):=by
 simp [firstMap,collectFirst,MvPolynomial.renameEquiv_apply]
@[simp] theorem firstMap_X_succ (φ:Polynomial K →+*A) (i:Fin 2):
   firstMap K φ (MvPolynomial.X i.succ)=MvPolynomial.X i:=by
 simp [firstMap,collectFirst,MvPolynomial.renameEquiv_apply]
theorem firstMap_eq_eval₂Hom (φ:Polynomial K →+*A):
   firstMap K φ=
     MvPolynomial.eval₂Hom (MvPolynomial.C.comp (φ.comp Polynomial.C))
       (Fin.cases (MvPolynomial.C (φ Polynomial.X)) MvPolynomial.X):=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp
 · intro i
   refine Fin.cases ?_ (fun j => ?_) i <;> simp
end FirstCoordinate
end
end ProximityPrize.SubmissionLower.RCN009
end PackedLegacy_H1
end Compact_PackedLegacyCore1
