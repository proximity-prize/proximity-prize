import ProximityPrize.SubmissionLower.Part.F006_01
section Compact_PackedLegacy
section PackedLegacy_CK
namespace ProximityPrize.SubmissionLower.RCN337
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
variable {K:Type} [Field K] [DecidableEq K]

theorem sum_pairwise_power_factor_degrees_le
   {I:Type*} [Fintype I]
   (R:Polynomial K) (q:I → Polynomial K) (multiplicity:I → ℕ)
   (hR:R≠0)
   (hqMonic:∀ i,(q i).Monic)
   (hqCoprime:Pairwise fun i j↦IsCoprime (q i) (q j))
   (hpow:∀ i,q i^multiplicity i∣R):
   (∑ i,multiplicity i*(q i).natDegree) ≤ R.natDegree:=by
 classical
 have hpowersCoprime:Pairwise fun i j↦
     IsCoprime ((q i)^multiplicity i) ((q j)^multiplicity j):=by
   intro i j hij
   exact (hqCoprime hij).pow
 have hprodDvd:(∏ i,(q i)^multiplicity i)∣R:=
   Fintype.prod_dvd_of_coprime hpowersCoprime hpow
 have hdegree:(∏ i,(q i)^multiplicity i).natDegree=
     ∑ i,multiplicity i*(q i).natDegree:=by
   rw [Polynomial.natDegree_prod_of_monic
     (s:=Finset.univ) (f:=fun i↦(q i)^multiplicity i)
     (fun i _↦(hqMonic i).pow _)]
   apply Finset.sum_congr rfl
   intro i _
   exact Polynomial.natDegree_pow (q i) (multiplicity i)
 rw [←hdegree]
 exact Polynomial.natDegree_le_of_dvd hprodDvd hR
theorem sum_power_factor_degrees_le
   {I:Type*} [Fintype I]
   (R:Polynomial K) (q:I → Polynomial K) (multiplicity:I → ℕ)
   (hR:R≠0)
   (hqIrreducible:∀ i,Irreducible (q i))
   (hqMonic:∀ i,(q i).Monic)
   (hqInjective:Function.Injective q)
   (hpow:∀ i,q i^multiplicity i∣R):
   (∑ i,multiplicity i*(q i).natDegree) ≤ R.natDegree:=by
 apply sum_pairwise_power_factor_degrees_le R q multiplicity hR hqMonic
 · intro i j hij
   apply (hqIrreducible i).coprime_iff_not_dvd.mpr
   intro hdvd
   have hassociated:=
     (hqIrreducible i).associated_of_dvd (hqIrreducible j) hdvd
   have heq:q i=q j:=Polynomial.eq_of_monic_of_associated
     (hqMonic i) (hqMonic j) hassociated
   exact hij (hqInjective heq)
 · exact hpow
theorem sum_grouped_power_factor_degrees_le
   {I:Type*} [Fintype I]
   (R:Polynomial K) (q:I → Polynomial K) (multiplicity:I → ℕ)
   (hR:R≠0)
   (hqIrreducible:∀ i,Irreducible (q i))
   (hqMonic:∀ i,(q i).Monic)
   (hpow:∀ f∈Finset.univ.image q,
     f^(∑ i with q i=f,multiplicity i)∣R):
   (∑ i,multiplicity i*(q i).natDegree) ≤ R.natDegree:=by
 classical
 let roots:Finset (Polynomial K):=Finset.univ.image q
 let grouped:roots → ℕ:=fun f↦∑ i with q i=f.1,multiplicity i
 have hrootsMonic:∀ f:roots,f.1.Monic:=by
   intro f
   obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
   simpa only [hi] using hqMonic i
 have hrootsIrreducible:∀ f:roots,Irreducible f.1:=by
   intro f
   obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
   simpa only [hi] using hqIrreducible i
 have hrootsPow:∀ f:roots,f.1^grouped f∣R:=by
   intro f
   exact hpow f.1 f.2
 have hbound:=sum_power_factor_degrees_le R
   (fun f:roots↦f.1) grouped hR hrootsIrreducible hrootsMonic
     Subtype.val_injective hrootsPow
 have hregroup:
     (∑ f:roots,grouped f*f.1.natDegree)=
       ∑ i,multiplicity i*(q i).natDegree:=by
   change (∑ f:roots,
     (∑ i with q i=f.1,multiplicity i)*f.1.natDegree)=_
   have hattach:
       (∑ f:roots,
         (∑ i with q i=f.1,multiplicity i)*f.1.natDegree)=
       ∑ f∈roots,
         (∑ i with q i=f,multiplicity i)*f.natDegree:=by
     rw [show (Finset.univ:Finset roots)=roots.attach from
       Finset.univ_eq_attach roots]
     exact Finset.sum_attach roots (fun f:Polynomial K↦
       (∑ i with q i=f,multiplicity i)*f.natDegree)
   rw [hattach]
   simp_rw [Finset.sum_mul]
   calc
     (∑ f∈roots,∑ i with q i=f,
         multiplicity i*f.natDegree)=
         ∑ f∈roots,∑ i with q i=f,
           multiplicity i*(q i).natDegree:=by
       apply Finset.sum_congr rfl
       intro f _
       apply Finset.sum_congr rfl
       intro i hi
       rw [(Finset.mem_filter.mp hi).2]
     _=∑ i∈(Finset.univ:Finset I),
         multiplicity i*(q i).natDegree:=
       Finset.sum_fiberwise_of_maps_to
         (s:=Finset.univ) (t:=roots) (g:=q)
         (fun i _↦Finset.mem_image_of_mem q (Finset.mem_univ i)) _
     _=_:=by rfl
 rw [←hregroup]
 exact hbound
end
end ProximityPrize.SubmissionLower.RCN337
end PackedLegacy_CK

/-! Packed from ProximityPrize.SubmissionLower.GY. -/
section PackedLegacy_GY
namespace ProximityPrize.SubmissionLower.RCN328
open scoped Classical BigOperators
open RCN264 RCN095 RCN272 RCN237 RCN039 RCN046 RCN037 RCN341 RCN121
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega Seed:Type} [Field Omega]
 {G T1 T2 H:MvPolynomial (Fin 3) Omega}
 {flag tailFlag1 tailFlag2:FlagDegree}
def properSecondTailComponents:
   Finset (RegularComponent Omega G T1 H):=by
 classical
 exact Finset.univ.filter fun C => T2∉C.1
variable [IsAlgClosed Omega]
end
end ProximityPrize.SubmissionLower.RCN328
end PackedLegacy_GY

/-! Packed from ProximityPrize.SubmissionLower.GX. -/
section PackedLegacy_GX
namespace ProximityPrize.SubmissionLower.RCN325
open scoped Classical BigOperators
open RCN264 RCN095 RCN237
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Omega Seed:Type} [Field Omega]
 {G T1 H:MvPolynomial (Fin 3) Omega}
 {flag tailFlag1 tailFlag2:FlagDegree}
def delayedComponents
   (active:RegularComponent Omega G T1 H → Prop):
   Finset (RegularComponent Omega G T1 H):=by
 classical
 exact Finset.univ.filter active
structure DelayedBranchFlagBudget
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (active:RegularComponent Omega G T1 H → Prop) where
 multiplicity:RegularComponent Omega G T1 H → ℕ
 cost:RegularComponent Omega G T1 H → ℕ
 cost_le:∀ C,active C →
   cost C ≤ multiplicity C*B.weightedCost tailFlag2 C
 divisor_le:
   (∑ C∈delayedComponents active,
     multiplicity C*B.weightedCost tailFlag2 C) ≤
       flagMixed flag tailFlag1 tailFlag2
def DelayedBranchFlagBudget.immediate
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (active:RegularComponent Omega G T1 H → Prop):
   DelayedBranchFlagBudget (tailFlag2:=tailFlag2) B active where
 multiplicity:=fun _ => 1
 cost:=fun C => B.weightedCost tailFlag2 C
 cost_le:=by simp
 divisor_le:=by
   calc
     (∑ C∈delayedComponents active,
         1*B.weightedCost tailFlag2 C)=
         ∑ C∈delayedComponents active,
           B.weightedCost tailFlag2 C:=by simp
     _ ≤
         ∑ C:RegularComponent Omega G T1 H,
           B.weightedCost tailFlag2 C:=by
       exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
     _ ≤ flagMixed flag tailFlag1 tailFlag2:=
       B.sum_weightedCost_le tailFlag2
end
end ProximityPrize.SubmissionLower.RCN325
end PackedLegacy_GX

/-! Packed from ProximityPrize.SubmissionLower.P7. -/
section PackedLegacy_P7
namespace ProximityPrize.SubmissionLower.RCN330
open scoped Classical
open RCN313 RCN231 RCN136 RCN238 RCN086 RCN055 RCN264 RCN243
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K Ω:Type} [Field K] [Field Ω]
theorem selected_globalTailCut_zero_of_lt
   (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (γ:K) (w d:ℕ)
   (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0)
   (hwd:w < d):
   MvPolynomial.aeval (selectedPoint φ selected γ)
     (globalTailCut φ F d)=0:=by
 rw [globalTailCut_eq,map_mul]
 have hzero:MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (numerator K F d))=0:=by
   rw [eval_surfaceMap]
   have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
       polynomialPoint (φ.comp Polynomial.C) (selected γ) γ
         (φ Polynomial.X):=by
     funext i
     fin_cases i <;> rfl
   rw [hv]
   exact polynomialPoint_numerator_zero (φ.comp Polynomial.C) F
     (selected γ) γ (φ Polynomial.X) hsolution d
     (hdegree.trans_lt hwd)
 change MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (numerator K F d))*_=0
 rw [hzero,zero_mul]
theorem globalTailCut_mem_iff
   (φ:Polynomial K →+*Ω) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (d:ℕ)
   (P:Ideal (MvPolynomial (Fin 3) Ω)):
   globalTailCut φ F d∈P ↔ surfaceMap φ (numerator K F d)∈P:=by
 rw [globalTailCut_eq]
 have hc:(-φ Polynomial.X)^d≠0:=tail_scalar_ne_zero φ hφ d
 have hu:IsUnit
     (MvPolynomial.C ((-φ Polynomial.X)^d):MvPolynomial (Fin 3) Ω):=
   (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
 exact P.mul_unit_mem_iff_mem hu
end
end ProximityPrize.SubmissionLower.RCN330
end PackedLegacy_P7

/-! Packed from ProximityPrize.SubmissionLower.B3. -/
section PackedLegacy_B3
namespace ProximityPrize.SubmissionLower.RCN074
open scoped Classical BigOperators
open RCN159 RCN136 RCN238 RCN264 RCN243 RCN086 RCN095 RCN237 RCN325
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar errors w:ℕ} [CharP Omega pchar]
 {flag tailFlag1 tailFlag2:FlagDegree}
 {support:RCN275.ResidualSupportParameters}
abbrev FirstTailComponent
   (S:ResidualStage phi Gamma x pchar errors flag w support):=
 RegularComponent Omega S.G (globalTailCut phi S.F (w+1))
   (regularitySurface phi S.F)
structure DelayedTailMultiplicityProvider
   (S:ResidualStage phi Gamma x pchar errors flag w support) where
 budgetFamily:PrimeFlagBudgetFamily
   (G:=S.G) (T:=globalTailCut phi S.F (w+1))
   (H:=regularitySurface phi S.F) flag tailFlag1
 multiplicity:FirstTailComponent S → ℕ
 cost:FirstTailComponent S → ℕ
 one_le_multiplicity:∀ C,1 ≤ multiplicity C
 tangentYZGate:errors+1 ≤ tailFlag2.yz
 cost_le:∀ C,
   cost C ≤ multiplicity C*budgetFamily.weightedCost tailFlag2 C
 divisor_le:
   (∑ C,multiplicity C*budgetFamily.weightedCost tailFlag2 C) ≤
     flagMixed flag tailFlag1 tailFlag2
 componentBound:∀ C,
   (componentSeeds Omega S.G (globalTailCut phi S.F (w+1))
     (regularitySurface phi S.F) Gamma
     (selectedPoint phi S.selected) C).card ≤ cost C
 dichotomy:∀ C,
   (∃ delay,1 ≤ delay∧delay ≤ multiplicity C∧
     globalTailCut phi S.F (w+1+delay)∉C.1)∨
   ((∀ delay,globalTailCut phi S.F (w+1+delay)∈C.1)∧
     (componentSeeds Omega S.G (globalTailCut phi S.F (w+1))
       (regularitySurface phi S.F) Gamma
       (selectedPoint phi S.selected) C).card ≤
         (errors+1)*budgetFamily.yzCost C)
theorem stage_card_le_flagMixed
   (S:ResidualStage phi Gamma x pchar errors flag w support)
   (P:DelayedTailMultiplicityProvider
     (tailFlag1:=tailFlag1) (tailFlag2:=tailFlag2) S):
   Gamma.card ≤ flagMixed flag tailFlag1 tailFlag2:=by
 classical
 let T1:=globalTailCut phi S.F (w+1)
 let H:=regularitySurface phi S.F
 let point:=selectedPoint phi S.selected
 have hG:∀ gamma∈Gamma,
     MvPolynomial.eval (point gamma) S.G=0:=S.on_component
 have hT1:∀ gamma∈Gamma,
     MvPolynomial.eval (point gamma) T1=0:=by
   intro gamma hgamma
   exact selected_globalTailCut_zero phi S.F S.selected gamma w
     (S.degree_le gamma hgamma) (S.solution gamma hgamma)
 have hH:∀ gamma∈Gamma,
     MvPolynomial.eval (point gamma) H≠0:=by
   intro gamma hgamma
   exact selectedPoint_evaluation phi S.selected gamma
     (MvPolynomial.pderiv (2:Fin 4) S.F) |>.symm ▸ S.regular gamma hgamma
 have hcover:Gamma.card ≤
     ∑ C:RegularComponent Omega S.G T1 H,
       (componentSeeds Omega S.G T1 H Gamma point C).card:=
   card_le_sum_componentSeeds Omega S.G T1 H Gamma point hG hT1 hH
 calc
   Gamma.card ≤ ∑ C:RegularComponent Omega S.G T1 H,
       (componentSeeds Omega S.G T1 H Gamma point C).card:=hcover
   _ ≤ ∑ C:RegularComponent Omega S.G T1 H,P.cost C:=
     Finset.sum_le_sum (fun C _↦P.componentBound C)
   _ ≤ ∑ C:RegularComponent Omega S.G T1 H,
       P.multiplicity C*P.budgetFamily.weightedCost tailFlag2 C:=
     Finset.sum_le_sum (fun C _↦P.cost_le C)
   _ ≤ flagMixed flag tailFlag1 tailFlag2:=P.divisor_le
end
end ProximityPrize.SubmissionLower.RCN074
end PackedLegacy_B3

/-! Packed from ProximityPrize.SubmissionLower.AM. -/
section PackedLegacy_AM
namespace ProximityPrize.SubmissionLower.RCN338
open scoped Classical BigOperators
open RCN095 RCN264 RCN237 RCN121 RCN337
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag firstTailFlag secondTailFlag:FlagDegree}
structure RegularComponentWeightedInertiaResultantCertificate
   (B:PrimeFlagBudgetFamily
     (G:=G) (T:=T) (H:=H) surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ) where
 z:(∑ C,multiplicity C*B.zCost C) ≤
   flagMixed surfaceFlag firstTailFlag unitZFlag
 yz:(∑ C,multiplicity C*B.yzCost C) ≤
   flagMixed surfaceFlag firstTailFlag unitYZFlag
 all:(∑ C,multiplicity C*B.allCost C) ≤
   flagMixed surfaceFlag firstTailFlag unitAllFlag
theorem RegularComponentWeightedInertiaResultantCertificate.divisor_le
   (B:PrimeFlagBudgetFamily
     (G:=G) (T:=T) (H:=H) surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ)
   (C:RegularComponentWeightedInertiaResultantCertificate B multiplicity):
   (∑ component,
     multiplicity component*B.weightedCost secondTailFlag component) ≤
       flagMixed surfaceFlag firstTailFlag secondTailFlag:=by
 have hz:=C.z
 have hyz:=C.yz
 have hall:=C.all
 calc
   (∑ component,
       multiplicity component*B.weightedCost secondTailFlag component)=
     secondTailFlag.zOnly*
         (∑ component,multiplicity component*B.zCost component)+
       secondTailFlag.yz*
         (∑ component,multiplicity component*B.yzCost component)+
       secondTailFlag.all*
         (∑ component,multiplicity component*B.allCost component):=by
     simp only [PrimeFlagBudgetFamily.weightedCost,
       Nat.mul_add,Finset.sum_add_distrib,Finset.mul_sum,
       Nat.mul_left_comm]
   _ ≤ secondTailFlag.zOnly*
         flagMixed surfaceFlag firstTailFlag unitZFlag+
       secondTailFlag.yz*
         flagMixed surfaceFlag firstTailFlag unitYZFlag+
       secondTailFlag.all*
         flagMixed surfaceFlag firstTailFlag unitAllFlag:=
     Nat.add_le_add
       (Nat.add_le_add
         (Nat.mul_le_mul_left secondTailFlag.zOnly hz)
         (Nat.mul_le_mul_left secondTailFlag.yz hyz))
       (Nat.mul_le_mul_left secondTailFlag.all hall)
   _=flagMixed surfaceFlag firstTailFlag secondTailFlag:=
     (flagMixed_projection_decomposition
       surfaceFlag firstTailFlag secondTailFlag).symm
end
end ProximityPrize.SubmissionLower.RCN338
end PackedLegacy_AM

/-! Packed from ProximityPrize.SubmissionLower.Q3. -/
section PackedLegacy_Q3
namespace ProximityPrize.SubmissionLower.RCN336
open scoped Classical BigOperators
open RCN264 RCN095 RCN237 RCN066 RCN338
noncomputable section
set_option autoImplicit false
variable {Omega Seed:Type} [Field Omega]
 {G T T' T2 H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag firstTailFlag secondTailFlag:FlagDegree}
theorem component_secondTail_card_le_mod
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H)
     surfaceFlag firstTailFlag)
   (C:RegularComponent Omega G T H)
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hpoint_injective:Function.Injective point)
   (hT2flag:PolynomialInFlagMod C.1 secondTailFlag T2)
   (hproper:T2 ∉ C.1)
   (hzero:∀ gamma ∈ componentSeeds Omega G T H S point C,
     MvPolynomial.aeval (point gamma) T2 = 0) :
   (componentSeeds Omega G T H S point C).card ≤
     B.weightedCost secondTailFlag C:=by
 classical
 let component:=componentSeeds Omega G T H S point C
 let points:=component.image point
 have hpointsPrime:∀ v ∈ points,
     C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
   exact componentSeeds_on_prime Omega G T H S point C gamma hgamma
 have hpointsZero:∀ v ∈ points,MvPolynomial.aeval v T2 = 0:=by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
   exact hzero gamma hgamma
 have hbound :=
   RCN066.PrimeFlagZeroBudget.zero_le_congr
     (B.primeBudget C) secondTailFlag T2 hT2flag hproper
     points hpointsPrime hpointsZero
 have hcard:points.card = component.card :=
   Finset.card_image_of_injective component hpoint_injective
 simpa only [points,component,hcard,
   PrimeFlagBudgetFamily.weightedCost] using hbound
def transportedMultiplicity
   (h:G ∣ T - T')
   (multiplicity:RegularComponent Omega G T H → ℕ) :
   RegularComponent Omega G T' H → ℕ :=
 fun C => multiplicity ((regularComponentEquiv h).symm C)
theorem weightedCertificate_of_congruentCut
   (h:G ∣ T - T')
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T') (H:=H)
     surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ)
   (C:RegularComponentWeightedInertiaResultantCertificate B
     (transportedMultiplicity h multiplicity)) :
   RegularComponentWeightedInertiaResultantCertificate
     (PrimeFlagBudgetFamily.ofCongruentCut h B) multiplicity where
 z:=by
   have hz:=C.z
   dsimp only [transportedMultiplicity] at hz
   rw [← (regularComponentEquiv h).sum_comp] at hz
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hz
 yz:=by
   have hyz:=C.yz
   dsimp only [transportedMultiplicity] at hyz
   rw [← (regularComponentEquiv h).sum_comp] at hyz
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hyz
 all:=by
   have hall:=C.all
   dsimp only [transportedMultiplicity] at hall
   rw [← (regularComponentEquiv h).sum_comp] at hall
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hall
end
end ProximityPrize.SubmissionLower.RCN336
end PackedLegacy_Q3

/-! Packed from ProximityPrize.SubmissionLower.X6. -/
section PackedLegacy_X6
namespace ProximityPrize.SubmissionLower.RCN014
open RCN002 RCN005 RCN011 RCN010
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
theorem planeEvaluation_surjective_of_finite_generatingPair
   {F E:Type} [Field F] [Field E] [Algebra F E]
   [FiniteDimensional F E]
   (y r:E)
   (hgen:IntermediateField.adjoin F ({y,r}:Set E)=⊤):
   Function.Surjective
     (RCN361.planeEval F E y r):=by
 let φ:Polynomial (Polynomial F) →ₐ[F] E:={
   toRingHom:=RCN361.planeEval F E y r
   commutes':=fun a↦by simp [RCN361.planeEval]}
 let A:Subalgebra F E:=φ.range
 let inclusion:A →ₗ[F] E:=A.val
 letI:Module.Finite F A:=
   Module.Finite.of_injective inclusion Subtype.val_injective
 have hAfield:IsField A:=IsField.of_isDomain_of_finite F A
 let L:IntermediateField F E:=A.toIntermediateField' hAfield
 have hy:y∈L:=by
   change y∈A
   refine ⟨Polynomial.C Polynomial.X,?_⟩
   simp [φ,RCN361.planeEval]
 have hr:r∈L:=by
   change r∈A
   refine ⟨Polynomial.X,?_⟩
   simp [φ,RCN361.planeEval]
 have htop:L=⊤:=by
   apply top_unique
   rw [←hgen]
   apply IntermediateField.adjoin_le_iff.mpr
   intro x hx
   rcases hx with hx | hx
   · subst x
     exact hy
   · rw [Set.mem_singleton_iff] at hx
     subst x
     exact hr
 intro x
 have hxL:x∈L:=by rw [htop];trivial
 change x∈A at hxL
 exact hxL
variable (K:Type) [Field K]
 (order:Fin 3 ≃ Fin 3)
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
def mappedPrimaryPiece
   {A B I:Type*} [CommRing A] [CommRing B]
   (f:A →+*B) (relation:I → Ideal A)
   (surface:B) (multiplicity:I → ℕ) (i:I):Ideal B:=
 Ideal.span {surface} ⊔ (Ideal.map f (relation i))^multiplicity i
theorem mappedPrimaryPiece_pairwise_coprime
   {A B I:Type*} [CommRing A] [CommRing B]
   (f:A →+*B) (relation:I → Ideal A)
   (hcoprime:Pairwise fun i j↦IsCoprime (relation i) (relation j))
   (surface:B) (multiplicity:I → ℕ):
   Pairwise fun i j↦IsCoprime
     (mappedPrimaryPiece f relation surface multiplicity i)
     (mappedPrimaryPiece f relation surface multiplicity j):=by
 intro i j hij
 have hmap:IsCoprime (Ideal.map f (relation i)) (Ideal.map f (relation j)):=by
   apply Ideal.isCoprime_iff_sup_eq.mpr
   rw [←Ideal.map_sup,(hcoprime hij).sup_eq,Ideal.map_top]
 have hpows:(Ideal.map f (relation i))^multiplicity i ⊔
     (Ideal.map f (relation j))^multiplicity j=⊤:=
   Ideal.pow_sup_pow_eq_top hmap.sup_eq
 apply Ideal.isCoprime_iff_sup_eq.mpr
 apply top_unique
 rw [←hpows]
 exact sup_le
   ((le_sup_right:(Ideal.map f (relation i))^multiplicity i ≤
     mappedPrimaryPiece f relation surface multiplicity i).trans le_sup_left)
   ((le_sup_right:(Ideal.map f (relation j))^multiplicity j ≤
     mappedPrimaryPiece f relation surface multiplicity j).trans le_sup_right)
theorem span_pair_le_mappedPrimaryPiece
   {A B I:Type*} [CommRing A] [CommRing B]
   (f:A →+*B) (relation:I → Ideal A)
   (surface tail:B) (multiplicity:I → ℕ) (i:I)
   (htail:tail∈mappedPrimaryPiece f relation surface multiplicity i):
   Ideal.span {surface,tail} ≤
     mappedPrimaryPiece f relation surface multiplicity i:=by
 rw [Ideal.span_le]
 intro x hx
 rcases hx with hx | hx
 · rw [hx]
   exact (show Ideal.span {surface} ≤
       mappedPrimaryPiece f relation surface multiplicity i from le_sup_left)
     (Ideal.subset_span (Set.mem_singleton surface))
 · rw [Set.mem_singleton_iff] at hx
   subst x
   exact htail
end
end ProximityPrize.SubmissionLower.RCN014
end PackedLegacy_X6

/-! Packed from ProximityPrize.SubmissionLower.FJ. -/
section PackedLegacy_FJ
namespace ProximityPrize.SubmissionLower.RCN226
open RCN011 RCN021 RCN022 RCN014
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
abbrev CoefficientRing:=Polynomial (RatFunc K)
def projectedFactor:Polynomial (RatFunc K):=
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 minpoly (RatFunc K) (e (MvPolynomial.X (order 2)))
theorem planeEvaluation_comp_C:
   (planeEvaluation K L order e ht).comp
     (Polynomial.C:CoefficientRing K →+*PlaneRing K)=
       Polynomial.eval₂RingHom
         (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom
         (e (MvPolynomial.X (order 2))):=by
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 apply Polynomial.ringHom_ext
 · intro c
   change planeEvaluation K L order e ht
       (Polynomial.C (Polynomial.C c))=
     Polynomial.aeval (e (MvPolynomial.X (order 2))) (Polynomial.C c)
   rw [planeEvaluation_C_C,Polynomial.aeval_C]
   rfl
 · change planeEvaluation K L order e ht (Polynomial.C Polynomial.X)=
     Polynomial.aeval (e (MvPolynomial.X (order 2))) Polynomial.X
   rw [planeEvaluation_C_X,Polynomial.aeval_X]
theorem relationKernel_comap_C:
   (relationKernel K L order e ht).comap
     (Polynomial.C:CoefficientRing K →+*PlaneRing K)=
       Ideal.span {projectedFactor K L order e ht}:=by
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 rw [relationKernel,RingHom.comap_ker,planeEvaluation_comp_C,
   show Polynomial.eval₂RingHom
     (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom
     (e (MvPolynomial.X (order 2)))=
       (Polynomial.aeval (e (MvPolynomial.X (order 2)))).toRingHom from rfl]
 change RingHom.ker (Polynomial.aeval (e (MvPolynomial.X (order 2))))=
   Ideal.span {minpoly (RatFunc K) (e (MvPolynomial.X (order 2)))}
 rw [minpoly.ker_aeval_eq_span_minpoly]
theorem projectedFactor_monic
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (projectedFactor K L order e ht).Monic:=by
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 exact minpoly.monic (IsIntegral.of_finite _ _)
theorem projectedFactor_irreducible
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Irreducible (projectedFactor K L order e ht):=
 by
   letI:Algebra (RatFunc K) L:=
     (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
   letI:FiniteDimensional (RatFunc K) L:=hfinite
   exact minpoly.irreducible (IsIntegral.of_finite _ _)
theorem relationKernel_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   (relationKernel K L order e ht).IsMaximal:=by
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 apply RingHom.ker_isMaximal_of_surjective
 exact planeEvaluation_surjective_of_finite_generatingPair
   (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))) hgen
end
end ProximityPrize.SubmissionLower.RCN226
end PackedLegacy_FJ

/-! Packed from ProximityPrize.SubmissionLower.C7. -/
section PackedLegacy_C7
namespace ProximityPrize.SubmissionLower.RCN191
open RCN011 RCN021 RCN022 RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
abbrev CoeffPrime:Ideal (Polynomial (RatFunc K)):=
 Ideal.span {projectedFactor K L order e ht}
theorem coeffPrime_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (CoeffPrime K L order e ht).IsMaximal:=
 PrincipalIdealRing.isMaximal_of_irreducible
   (projectedFactor_irreducible K L order e ht hfinite)
abbrev LocalCoefficient
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):=
 @Localization.AtPrime (Polynomial (RatFunc K)) _
   (CoeffPrime K L order e ht)
   (coeffPrime_isMaximal K L order e ht hfinite).isPrime
local instance localCoefficientSemiring
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Semiring (LocalCoefficient K L order e ht hfinite):=
 (inferInstance:CommRing
   (LocalCoefficient K L order e ht hfinite)).toSemiring
local instance localizedPlaneSemiring
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Semiring (Polynomial (LocalCoefficient K L order e ht hfinite)):=
 (inferInstance:CommRing
   (Polynomial (LocalCoefficient K L order e ht hfinite))).toSemiring
def localizePlane
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   PlaneRing K →+*Polynomial (LocalCoefficient K L order e ht hfinite):=
 Polynomial.mapRingHom
   (algebraMap (Polynomial (RatFunc K))
     (LocalCoefficient K L order e ht hfinite))
def localizedRelation
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Ideal (Polynomial (LocalCoefficient K L order e ht hfinite)):=
 Ideal.map (localizePlane K L order e ht hfinite)
   (relationKernel K L order e ht)
theorem localizedRelation_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   (localizedRelation K L order e ht hfinite).IsMaximal:=by
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let f:=localizePlane K L order e ht hfinite
 let c:Polynomial (RatFunc K) →+*PlaneRing K:=Polynomial.C
 have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 letI:p.IsPrime:=hpmax.isPrime
 have hJmax:J.IsMaximal:=
   relationKernel_isMaximal K L order e ht hfinite hgen
 letI:J.IsPrime:=hJmax.isPrime
 have hdisjoint:Disjoint
     ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing K))
       (J:Set (PlaneRing K)):=by
   rw [Set.disjoint_left]
   intro a ha haJ
   obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp ha
   apply hr
   have hrJ:r∈J.comap c:=haJ
   have hcomap:J.comap c=p:=by
     simpa only [J,c,p] using
       relationKernel_comap_C K L order e ht
   rwa [hcomap] at hrJ
 letI:Algebra (Polynomial (RatFunc K)) Rp:=inferInstance
 letI:IsLocalization p.primeCompl Rp:=inferInstance
 letI:Algebra (PlaneRing K) (Polynomial Rp):=
   Polynomial.algebra (Polynomial (RatFunc K)) Rp
 have hf:f=algebraMap (PlaneRing K) (Polynomial Rp):=rfl
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom)
     (Polynomial Rp):=by
   exact Polynomial.isLocalization p.primeCompl Rp
 have hunder:(localizedRelation K L order e ht hfinite).under
     (PlaneRing K)=J:=by
   change (Ideal.map f J).under (PlaneRing K)=J
   rw [hf]
   exact IsLocalization.under_map_of_isPrime_disjoint
     (I:=J) (p.primeCompl.map c.toMonoidHom) (Polynomial Rp)
       hJmax.isPrime hdisjoint
 letI:((localizedRelation K L order e ht hfinite).under
     (PlaneRing K)).IsMaximal:=
   hunder ▸ hJmax
 have hunder':(Ideal.map
     (algebraMap (PlaneRing K) (Polynomial Rp)) J).under (PlaneRing K)=J:=by
   rw [←hf]
   exact hunder
 letI:((Ideal.map (algebraMap (PlaneRing K) (Polynomial Rp)) J).under
     (PlaneRing K)).IsMaximal:=hunder'.symm ▸ hJmax
 change (Ideal.map f J).IsMaximal
 rw [hf]
 exact Ideal.IsMaximal.of_isLocalization_of_disjoint
   (p.primeCompl.map c.toMonoidHom)
abbrev LocalizedPlane
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):=
 Polynomial (LocalCoefficient K L order e ht hfinite)
abbrev LocalizedSurfaceQuotient
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (surface:PlaneRing K):=
 Polynomial (LocalCoefficient K L order e ht hfinite) ⧸
   Ideal.span {localizePlane K L order e ht hfinite surface}
def localizedRelationBar
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (surface:PlaneRing K):
   Ideal (LocalizedSurfaceQuotient K L order e ht hfinite surface):=
 Ideal.map (Ideal.Quotient.mk
   (Ideal.span {localizePlane K L order e ht hfinite surface}))
     (localizedRelation K L order e ht hfinite)
end
end ProximityPrize.SubmissionLower.RCN191
end PackedLegacy_C7

/-! Packed from ProximityPrize.SubmissionLower.DM. -/
section PackedLegacy_DM
namespace ProximityPrize.SubmissionLower.RCN034
open RCN002 RCN005 RCN011 RCN010 RCN371
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K:Type) [Field K]
def planeDenominators (order:Fin 3 ≃ Fin 3):Submonoid (Original K):=
 (coefficientDenominators K).comap (collect K order).toMonoidHom
@[reducible] def rationalPolynomialAlgebra (order:Fin 3 ≃ Fin 3):
   Algebra (Original K) (RationalPolynomials K):=
 (rationalMap K order).toAlgebra
@[reducible] def planeAlgebra (order:Fin 3 ≃ Fin 3):
   Algebra (Original K) (PlaneRing K):=
 (planeMap K order).toAlgebra
theorem rationalPolynomialLocalization (order:Fin 3 ≃ Fin 3):
   letI:=rationalPolynomialAlgebra K order
   IsLocalization (planeDenominators K order) (RationalPolynomials K):=by
 letI:=rationalPolynomialAlgebra K order
 letI:Algebra (Collected K) (RationalPolynomials K):=
   MvPolynomial.algebraMvPolynomial
 letI:IsLocalization (coefficientDenominators K) (RationalPolynomials K):=
   MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RatFunc K)
 apply IsLocalization.of_ringEquiv_left
   (R:=Original K) (S:=Collected K) (K:=RationalPolynomials K)
   (M₁:=coefficientDenominators K) (M₂:=planeDenominators K order)
   (collect K order).toRingEquiv
 · exact Submonoid.map_comap_eq_of_surjective
     (collect K order).surjective (coefficientDenominators K)
 · intro F
   rfl
theorem planeRingLocalization (order:Fin 3 ≃ Fin 3):
   letI:=planeAlgebra K order
   IsLocalization (planeDenominators K order) (PlaneRing K):=by
 letI:=rationalPolynomialAlgebra K order
 let aPlane:=planeAlgebra K order
 letI:Algebra (Original K) (PlaneRing K):=aPlane
 letI:SMul (Original K) (PlaneRing K):=aPlane.toSMul
 letI:IsLocalization (planeDenominators K order) (RationalPolynomials K):=
   rationalPolynomialLocalization K order
 let e:RationalPolynomials K ≃ₐ[Original K] PlaneRing K:={
   bivariateEquiv (RatFunc K) with
   commutes':=fun F => rfl}
 exact IsLocalization.isLocalization_of_algEquiv
   (planeDenominators K order) e
end
end ProximityPrize.SubmissionLower.RCN034
end PackedLegacy_DM

/-! Packed from ProximityPrize.SubmissionLower.L7. -/
section PackedLegacy_L7
namespace ProximityPrize.SubmissionLower.RCN189
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {A B:Type*} [CommRing A] [CommRing B]
 (M:Submonoid A) [Algebra A B] [IsLocalization M B]
@[reducible] def quotientAlgebra
   (I:Ideal A) (J:Ideal B) (hIJ:I ≤ J.comap (algebraMap A B)):
   Algebra (A ⧸ I) (B ⧸ J):=
 (Ideal.quotientMap J (algebraMap A B) hIJ).toAlgebra'
   (fun _ _ => mul_comm _ _)
theorem quotient_isLocalization
   (I:Ideal A) (J:Ideal B)
   (hJ:J=I.map (algebraMap A B)):
   let hIJ:I ≤ J.comap (algebraMap A B):=by
     rw [hJ]
     exact Ideal.le_comap_map
   letI:=quotientAlgebra I J hIJ
   IsLocalization (M.map (Ideal.Quotient.mk I)) (B ⧸ J):=by
 let hIJ:I ≤ J.comap (algebraMap A B):=by
   rw [hJ]
   exact Ideal.le_comap_map
 letI:=quotientAlgebra I J hIJ
 let qA:A →+*A ⧸ I:=Ideal.Quotient.mk I
 let qB:B →+*B ⧸ J:=Ideal.Quotient.mk J
 constructor
 constructor
 · rintro ⟨_,⟨m,hm,rfl⟩⟩
   change IsUnit (qB (algebraMap A B m))
   exact (IsLocalization.map_units B ⟨m,hm⟩).map qB
 · intro y
   obtain ⟨b,rfl⟩:=Ideal.Quotient.mk_surjective y
   obtain ⟨⟨a,m⟩,hb⟩:=IsLocalization.surj M b
   let mbar:M.map qA:=⟨qA m,⟨m,m.property,rfl⟩⟩
   refine ⟨⟨qA a,mbar⟩,?_⟩
   change qB b*qB (algebraMap A B m)=qB (algebraMap A B a)
   simpa only [map_mul] using congrArg qB hb
 · intro x y hxy
   obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
   obtain ⟨b,rfl⟩:=Ideal.Quotient.mk_surjective y
   change qB (algebraMap A B a)=qB (algebraMap A B b) at hxy
   have hmem:algebraMap A B (a-b)∈J:=by
     rw [←Ideal.Quotient.eq_zero_iff_mem]
     rw [map_sub]
     change qB (algebraMap A B a-algebraMap A B b)=0
     rw [map_sub,hxy,sub_self]
   rw [hJ,IsLocalization.algebraMap_mem_map_algebraMap_iff M B] at hmem
   obtain ⟨m,hmM,hmI⟩:=hmem
   let mbar:M.map qA:=⟨qA m,⟨m,hmM,rfl⟩⟩
   refine ⟨mbar,?_⟩
   change qA m*qA a=qA m*qA b
   rw [←map_mul, ←map_mul, ←sub_eq_zero, ←map_sub,
     Ideal.Quotient.eq_zero_iff_mem]
   simpa only [mul_sub] using hmI
end
end ProximityPrize.SubmissionLower.RCN189
end PackedLegacy_L7

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.L8. -/
section PackedLegacy_L8
namespace ProximityPrize.SubmissionLower.RCN190
open RCN189
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {A B:Type*} [CommRing A] [CommRing B]
 (M:Submonoid A) [Algebra A B] [IsLocalization M B]
def surfaceMap (I:Ideal A):
   (A ⧸ I) →+*(B ⧸ I.map (algebraMap A B)):=
 Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
   Ideal.le_comap_map
@[reducible] def surfaceAlgebra (I:Ideal A):
   Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)):=
 quotientAlgebra I (I.map (algebraMap A B)) Ideal.le_comap_map
def sourcePrime (I P:Ideal A):Ideal (A ⧸ I):=
 P.map (Ideal.Quotient.mk I)
def targetPrime (I:Ideal A) (J:Ideal B):
   Ideal (B ⧸ I.map (algebraMap A B)):=
 J.map (Ideal.Quotient.mk (I.map (algebraMap A B)))
theorem sourcePrime_isPrime
   (I P:Ideal A) [P.IsPrime] (hIP:I ≤ P):
   (sourcePrime I P).IsPrime:=by
 apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
 simpa only [Ideal.mk_ker] using hIP
theorem map_ideal_le_relation
   (I P:Ideal A) (J:Ideal B)
   (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):
   I.map (algebraMap A B) ≤ J:=by
 rw [Ideal.map_le_iff_le_comap,hcontract]
 exact hIP
theorem targetPrime_isPrime
   (I P:Ideal A) (J:Ideal B) [J.IsPrime]
   (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):
   (targetPrime I J).IsPrime:=by
 apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
 simpa only [Ideal.mk_ker] using
   map_ideal_le_relation I P J hIP hcontract
theorem targetPrime_contract
   (I P:Ideal A) (J:Ideal B)
   (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):
   (targetPrime I J).comap (surfaceMap I)=sourcePrime I P:=by
 let qA:A →+*A ⧸ I:=Ideal.Quotient.mk I
 let qB:B →+*B ⧸ I.map (algebraMap A B):=
   Ideal.Quotient.mk (I.map (algebraMap A B))
 apply Ideal.comap_injective_of_surjective qA Ideal.Quotient.mk_surjective
 change Ideal.comap qA
     (Ideal.comap (surfaceMap I) (Ideal.map qB J))=
   Ideal.comap qA (Ideal.map qA P)
 rw [Ideal.comap_comap]
 have hcomp:(surfaceMap I).comp qA=
     qB.comp (algebraMap A B):=by
   apply DFunLike.ext _ _
   intro a
   rfl
 rw [hcomp, ←Ideal.comap_comap,
   Ideal.comap_map_of_surjective' qB Ideal.Quotient.mk_surjective,
   Ideal.mk_ker,
   sup_eq_left.mpr (map_ideal_le_relation I P J hIP hcontract),
   hcontract,
   Ideal.comap_map_of_surjective' qA Ideal.Quotient.mk_surjective,
   Ideal.mk_ker,sup_eq_left.mpr hIP]
theorem surface_isLocalization (I:Ideal A):
   letI:=surfaceAlgebra (A:=A) (B:=B) I
   IsLocalization (M.map (Ideal.Quotient.mk I))
     (B ⧸ I.map (algebraMap A B)):=by
 letI:=surfaceAlgebra (A:=A) (B:=B) I
 exact quotient_isLocalization M I (I.map (algebraMap A B)) rfl
noncomputable abbrev SourceLocal
   (I P:Ideal A) [P.IsPrime] (hIP:I ≤ P):=
 @Localization.AtPrime (A ⧸ I) _ (sourcePrime I P)
   (sourcePrime_isPrime I P hIP)
noncomputable abbrev TargetLocal
   (I P:Ideal A) (J:Ideal B) [J.IsPrime]
   (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):=
 @Localization.AtPrime (B ⧸ I.map (algebraMap A B)) _ (targetPrime I J)
   (targetPrime_isPrime I P J hIP hcontract)
noncomputable def surfaceLocalEquiv
   (I P:Ideal A) [P.IsPrime] (J:Ideal B) [J.IsPrime]
   (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):
   SourceLocal I P hIP ≃+*TargetLocal I P J hIP hcontract:=by
 let p:=sourcePrime I P
 let q:=targetPrime I J
 letI:p.IsPrime:=sourcePrime_isPrime I P hIP
 letI:q.IsPrime:=targetPrime_isPrime I P J hIP hcontract
 let aSurface:=surfaceAlgebra (A:=A) (B:=B) I
 letI:Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)):=aSurface
 letI:SMul (A ⧸ I) (B ⧸ I.map (algebraMap A B)):=aSurface.toSMul
 letI:IsLocalization (M.map (Ideal.Quotient.mk I))
     (B ⧸ I.map (algebraMap A B)):=surface_isLocalization M I
 let aLocal:Algebra (A ⧸ I) (Localization.AtPrime q):=
   ((algebraMap (B ⧸ I.map (algebraMap A B)) (Localization.AtPrime q)).comp
     (surfaceMap I)).toAlgebra' (fun _ _ => mul_comm _ _)
 letI:Algebra (A ⧸ I) (Localization.AtPrime q):=aLocal
 letI:SMul (A ⧸ I) (Localization.AtPrime q):=aLocal.toSMul
 let targetAlgebra:Algebra (B ⧸ I.map (algebraMap A B))
     (Localization.AtPrime q):=inferInstance
 letI:SMul (B ⧸ I.map (algebraMap A B)) (Localization.AtPrime q):=
   targetAlgebra.toSMul
 letI:IsScalarTower (A ⧸ I) (B ⧸ I.map (algebraMap A B))
     (Localization.AtPrime q):=IsScalarTower.of_algebraMap_eq' rfl
 have hloc:IsLocalization.AtPrime (Localization.AtPrime q) p:=by
   convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
     (M.map (Ideal.Quotient.mk I)) (Localization.AtPrime q) q
   exact (targetPrime_contract I P J hIP hcontract).symm
 letI:IsLocalization.AtPrime (Localization.AtPrime q) p:=hloc
 exact (IsLocalization.algEquiv p.primeCompl _ _).toRingEquiv
end
end ProximityPrize.SubmissionLower.RCN190
end PackedLegacy_L8

/-! Packed from ProximityPrize.SubmissionLower.EC. -/
section PackedLegacy_EC
namespace ProximityPrize.SubmissionLower.RCN113
open RCN002 RCN011 RCN371 RCN021 RCN125 RCN093 RCN034 RCN190
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable (K:Type) [Field K]
def flagPlaneMap (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   Original K →+*PlaneRing K:=
 (planeMap K order).comp (flagAlgHom lam mu nu).toRingHom
def flagPlaneDenominators (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   Submonoid (Original K):=
 (planeDenominators K order).map (flagEquiv lam mu nu).symm.toMonoidHom
@[reducible] def flagPlaneAlgebra
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   Algebra (Original K) (PlaneRing K):=
 (flagPlaneMap K lam mu nu order).toAlgebra
theorem flagPlaneRingLocalization
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   letI:=flagPlaneAlgebra K lam mu nu order
   IsLocalization (flagPlaneDenominators K lam mu nu order) (PlaneRing K):=by
 letI:=planeAlgebra K order
 letI:IsLocalization (planeDenominators K order) (PlaneRing K):=
   planeRingLocalization K order
 exact IsLocalization.isLocalization_of_base_ringEquiv
   (planeDenominators K order) (PlaneRing K)
     (flagEquiv lam mu nu).symm.toRingEquiv
def flagRelationKernel
   (P:Ideal (Original K)) [P.IsPrime]
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   Ideal (PlaneRing K):=
 relationKernel K (CoordinateField K P) order
   (flagEvaluation K P lam mu nu) ht
theorem flagRelationKernel_contract
   (P:Ideal (Original K)) [P.IsPrime]
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   letI:=flagPlaneAlgebra K lam mu nu order
   (flagRelationKernel K P lam mu nu order ht).comap
     (algebraMap (Original K) (PlaneRing K))=P:=by
 letI:=flagPlaneAlgebra K lam mu nu order
 change (flagRelationKernel K P lam mu nu order ht).comap
     ((planeMap K order).comp (flagAlgHom lam mu nu).toRingHom)=P
 rw [←Ideal.comap_comap,flagRelationKernel,relationKernel_contract,
   flagEvaluation_kernel_contract]
noncomputable def flagSurfaceComponentToPlaneLocalEquiv
   (G:Original K) (P:Ideal (Original K)) [P.IsPrime]
   (hGmem:G∈P) (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   letI:=flagPlaneAlgebra K lam mu nu order
   letI:(flagRelationKernel K P lam mu nu order ht).IsPrime:=
     RingHom.ker_isPrime _
   SourceLocal (Ideal.span {G}) P
       (by simpa only [Ideal.span_singleton_le_iff_mem] using hGmem) ≃+*
     TargetLocal (Ideal.span {G}) P
       (flagRelationKernel K P lam mu nu order ht)
       (by simpa only [Ideal.span_singleton_le_iff_mem] using hGmem)
       (flagRelationKernel_contract K P lam mu nu order ht):=by
 letI:=flagPlaneAlgebra K lam mu nu order
 letI:IsLocalization (flagPlaneDenominators K lam mu nu order)
     (PlaneRing K):=flagPlaneRingLocalization K lam mu nu order
 letI:(flagRelationKernel K P lam mu nu order ht).IsPrime:=
   RingHom.ker_isPrime _
 exact surfaceLocalEquiv (flagPlaneDenominators K lam mu nu order)
   (Ideal.span {G}) P (flagRelationKernel K P lam mu nu order ht)
   (by simpa only [Ideal.span_singleton_le_iff_mem] using hGmem)
   (flagRelationKernel_contract K P lam mu nu order ht)
end
end ProximityPrize.SubmissionLower.RCN113
end PackedLegacy_EC

/-! Packed from ProximityPrize.SubmissionLower.Z1. -/
section PackedLegacy_Z1
namespace ProximityPrize.SubmissionLower.RCN120
open RCN002 RCN011 RCN371 RCN021 RCN022 RCN125 RCN093
noncomputable section
set_option autoImplicit false
@[reducible] def residueAlgebra
   {F B:Type*} [Field F] [CommRing B]
   [Algebra F B] [Algebra (Polynomial F) B]
   (q:Polynomial F) (J:Ideal B)
   (hcontract:J.comap (algebraMap (Polynomial F) B)=Ideal.span {q}):
   Algebra (AdjoinRoot q) (B ⧸ J):=
 (Ideal.quotientMap J (algebraMap (Polynomial F) B) (by rw [hcontract])).toAlgebra'
   (fun _ _ => mul_comm _ _)
theorem quotient_finrank_eq_natDegree_mul_residue_finrank
   {F B:Type*} [Field F] [CommRing B]
   [Algebra F B] [Algebra (Polynomial F) B]
   [IsScalarTower F (Polynomial F) B]
   (q:Polynomial F) (hq:Irreducible q)
   (J:Ideal B) [J.IsMaximal]
   (hcontract:J.comap (algebraMap (Polynomial F) B)=Ideal.span {q}):
   letI:=residueAlgebra q J hcontract
   Module.finrank F (B ⧸ J)=
     q.natDegree*Module.finrank (AdjoinRoot q) (B ⧸ J):=by
 letI:Fact (Irreducible q):=⟨hq⟩
 let aResidue:Algebra (AdjoinRoot q) (B ⧸ J):=
   residueAlgebra q J hcontract
 letI:Algebra (AdjoinRoot q) (B ⧸ J):=aResidue
 letI:SMul (AdjoinRoot q) (B ⧸ J):=aResidue.toSMul
 let aBase:Algebra F (AdjoinRoot q):=inferInstance
 letI:SMul F (AdjoinRoot q):=aBase.toSMul
 let aTotal:Algebra F (B ⧸ J):=inferInstance
 letI:SMul F (B ⧸ J):=aTotal.toSMul
 letI:IsScalarTower F (AdjoinRoot q) (B ⧸ J):=
   IsScalarTower.of_algebraMap_eq (R:=F) (S:=AdjoinRoot q)
     (A:=B ⧸ J) fun c => by
       change Ideal.Quotient.mk J (algebraMap F B c)=
         Ideal.Quotient.mk J
           (algebraMap (Polynomial F) B (Polynomial.C c))
       apply congrArg (Ideal.Quotient.mk J)
       change algebraMap F B c=algebraMap (Polynomial F) B
         (algebraMap F (Polynomial F) c)
       exact IsScalarTower.algebraMap_apply F (Polynomial F) B c
 letI:Module.Free F (AdjoinRoot q):=
   Module.Free.of_divisionRing F (AdjoinRoot q)
 letI:Module.Free (AdjoinRoot q) (B ⧸ J):=
   Module.Free.of_divisionRing (AdjoinRoot q) (B ⧸ J)
 calc
   Module.finrank F (B ⧸ J)=
       Module.finrank F (AdjoinRoot q)*
         Module.finrank (AdjoinRoot q) (B ⧸ J):=
     (Module.finrank_mul_finrank F (AdjoinRoot q) (B ⧸ J)).symm
   _=q.natDegree*Module.finrank (AdjoinRoot q) (B ⧸ J):=by
     rw [show Module.finrank F (AdjoinRoot q)=q.natDegree by
       change Module.finrank F (Polynomial F ⧸ Ideal.span {q})=q.natDegree
       exact finrank_quotient_span_eq_natDegree]
variable (K:Type) [Field K]
@[reducible] def flagBaseAlgebra
   (P:Ideal (Original K)) [P.IsPrime]
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   Algebra (RatFunc K) (CoordinateField K P):=
 (elementEmbedding K (CoordinateField K P)
   (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
end
end ProximityPrize.SubmissionLower.RCN120
end PackedLegacy_Z1

/-! Packed from ProximityPrize.SubmissionLower.S. -/
section PackedLegacy_S
namespace ProximityPrize.SubmissionLower.RCN225
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {A:Type*} [CommRing A]
theorem maximalIdeal_pow_succ_lt_pow_of_noetherian_domain
   {S:Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S]
   [IsLocalRing S]
   (hmax:IsLocalRing.maximalIdeal S≠⊥) (n:ℕ):
   IsLocalRing.maximalIdeal S^(n+1) <
     IsLocalRing.maximalIdeal S^n:=by
 let m:=IsLocalRing.maximalIdeal S
 have hle:m^(n+1) ≤ m^n:=Ideal.pow_le_pow_right n.le_succ
 refine lt_of_le_of_ne hle ?_
 intro heq
 have hfg:(m^n).FG:=IsNoetherian.noetherian _
 have hsmul:m^n ≤ m • (m^n):=by
   rw [Ideal.smul_eq_mul, ←pow_succ', ←heq]
 have hzero:m^n=⊥:=
   Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m (m^n) hfg hsmul
     (IsLocalRing.maximalIdeal_le_jacobson ⊥)
 obtain ⟨x,hx,hx0⟩:=SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hmax)
 have hxpow:x^n∈m^n:=Ideal.pow_mem_pow hx n
 rw [hzero,Ideal.mem_bot] at hxpow
 exact pow_ne_zero n (by simpa only [Ideal.mem_bot] using hx0) hxpow
theorem exponent_le_length_local_maximal_pow_of_noetherian_domain
   {S:Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S]
   [IsLocalRing S]
   (hmax:IsLocalRing.maximalIdeal S≠⊥) (n:ℕ):
   (n:ℕ∞) ≤ Module.length S
     (S ⧸ IsLocalRing.maximalIdeal S^n):=by
 rw [Module.length_quotient]
 induction n with
 | zero => simp
 | succ n ih =>
     calc
       ((n+1:ℕ):ℕ∞)=(n:ℕ∞)+1:=by simp
       _ ≤ Order.coheight (IsLocalRing.maximalIdeal S^n)+1:=
         add_le_add_left ih 1
       _ ≤ Order.coheight (IsLocalRing.maximalIdeal S^(n+1)):=
         Order.coheight_add_one_le
           (maximalIdeal_pow_succ_lt_pow_of_noetherian_domain hmax n)
theorem exponent_mul_residueDegree_le_length_quotient_maximal_pow
   {R S:Type*} [CommRing R] [IsLocalRing R]
   [CommRing S] [IsDomain S] [IsNoetherianRing S] [Algebra R S]
   (p:Ideal S) [p.IsMaximal] (hp:p≠⊥)
   [IsLocalHom (algebraMap R (Localization.AtPrime p))]
   [FiniteDimensional (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime p))] (n:ℕ):
   ((n*Module.finrank (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime p)):ℕ):ℕ∞) ≤
       Module.length R (S ⧸ p^n):=by
 let L:=Localization.AtPrime p
 let M:=L ⧸ IsLocalRing.maximalIdeal L^n
 have hmaxL:IsLocalRing.maximalIdeal L≠⊥:=by
   intro hbot
   apply hp
   rw [←IsLocalization.AtPrime.under_maximalIdeal L p,hbot]
   exact Ideal.comap_bot_of_injective (algebraMap S L)
     (IsLocalization.injective L p.primeCompl_le_nonZeroDivisors)
 have hlocal:(n:ℕ∞) ≤ Module.length L M:=
   exponent_le_length_local_maximal_pow_of_noetherian_domain hmaxL n
 have hresidue:Module.length (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField L)=
       Module.finrank (IsLocalRing.ResidueField R)
         (IsLocalRing.ResidueField L):=Module.length_eq_finrank _ _
 have hweighted:((n*Module.finrank (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField L):ℕ):ℕ∞) ≤ Module.length R M:=by
   rw [Nat.cast_mul, ←hresidue,
     IsLocalRing.length_restrictScalars R L M]
   exact mul_le_mul_right' hlocal _
 let e:=IsLocalization.AtPrime.equivQuotMaximalIdealPow p L n
 have heq:Module.length R (S ⧸ p^n)=Module.length R M:=
   (e.toLinearEquiv.restrictScalars R).length_eq
 exact hweighted.trans_eq heq.symm
abbrev SurfaceQuotient (surface:A):=A ⧸ Ideal.span {surface}
theorem exponent_mul_residueDegree_le_length_span_surface_sup_relation_pow
   {R:Type*} [CommRing R] [IsLocalRing R] [Algebra R A]
   (surface:A)
   (relation:Ideal A)
   (relationBar:Ideal (SurfaceQuotient surface)) [relationBar.IsMaximal]
   (hrelationBar:relationBar=
     Ideal.map (Ideal.Quotient.mk (Ideal.span {surface})) relation)
   [IsDomain (SurfaceQuotient surface)]
   [IsNoetherianRing (SurfaceQuotient surface)]
   (hrelationBarNe:relationBar≠⊥)
   [IsLocalHom (algebraMap R (Localization.AtPrime relationBar))]
   [FiniteDimensional (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime relationBar))]
   (n:ℕ):
   ((n*Module.finrank (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime relationBar)):ℕ):ℕ∞) ≤
     Module.length R (A ⧸ (Ideal.span {surface} ⊔ relation^n)):=by
 let I:Ideal A:=Ideal.span {surface}
 let q:A →ₐ[R] A ⧸ I:=Ideal.Quotient.mkₐ R I
 have hpow:relationBar^n=Ideal.map q (relation^n):=by
   rw [hrelationBar,Ideal.map_pow]
   rfl
 let e₁:(SurfaceQuotient surface ⧸ relationBar^n) ≃ₐ[R]
     (SurfaceQuotient surface ⧸ Ideal.map q (relation^n)):=
   Ideal.quotientEquivAlgOfEq R hpow
 let e₂:(SurfaceQuotient surface ⧸ Ideal.map q (relation^n)) ≃ₐ[R]
     (A ⧸ (I ⊔ relation^n)):=
   DoubleQuot.quotQuotEquivQuotSupₐ R I (relation^n)
 have hlocal:=
   exponent_mul_residueDegree_le_length_quotient_maximal_pow
     (R:=R) relationBar hrelationBarNe n
 exact hlocal.trans_eq (e₁.trans e₂).toLinearEquiv.length_eq
end
end ProximityPrize.SubmissionLower.RCN225
end PackedLegacy_S

/-! Packed from ProximityPrize.SubmissionLower.N. -/
section PackedLegacy_N
namespace ProximityPrize.SubmissionLower.RCN102
open RCN011
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
abbrev FiberCoefficient
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):=
 @Localization.AtPrime (Polynomial (RatFunc Omega)) _ (Ideal.span {q})
   (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
@[reducible] instance fiberLocalizedPlaneSemiring
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Semiring (Polynomial (FiberCoefficient q hq)):=
 Polynomial.commSemiring.toSemiring
def fiberLocalizePlane
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   PlaneRing Omega →+*Polynomial (FiberCoefficient q hq):=
 Polynomial.mapRingHom
   (algebraMap (Polynomial (RatFunc Omega)) (FiberCoefficient q hq))
end
end ProximityPrize.SubmissionLower.RCN102
end PackedLegacy_N

/-! Packed from ProximityPrize.SubmissionLower.Y9. -/
section PackedLegacy_Y9
namespace ProximityPrize.SubmissionLower.RCN106
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN022 RCN264 RCN125 RCN093 RCN120 RCN102 RCN014 RCN226 RCN225 RCN191
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (hcomponent:Function.Injective component)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
def indexedComponentFactor (a:A):Polynomial (RatFunc Omega):=
 projectedFactor Omega (CoordinateField Omega (component a).1) order
   (flagEvaluation Omega (component a).1 lam mu nu) (ht a)
abbrev IndexedFactorFiber (q:Polynomial (RatFunc Omega)):=
 {a:A//q=indexedComponentFactor component lam mu nu order ht a}
def indexedFiberRelation
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   Ideal (Polynomial (FiberCoefficient q hq)):=
 Ideal.map (fiberLocalizePlane q hq)
   (relationKernel Omega (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
def indexedFiberRelationBar
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   Ideal (SurfaceQuotient (fiberLocalizePlane q hq surface)):=
 Ideal.map (Ideal.Quotient.mk
   (Ideal.span {fiberLocalizePlane q hq surface}))
     (indexedFiberRelation component lam mu nu order ht q hq a)
theorem indexedFiberRelation_under
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelation component lam mu nu order ht q hq a).comap
     (fiberLocalizePlane q hq)=
       relationKernel Omega (CoordinateField Omega (component a.1).1) order
         (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1):=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let J:=relationKernel Omega (CoordinateField Omega (component a.1).1) order
   (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
 let f:=fiberLocalizePlane q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hJprime:J.IsPrime:=RingHom.ker_isPrime _
 have hcomap:J.comap c=p:=by
   rw [relationKernel_comap_C]
   exact congrArg (fun r => Ideal.span {r}) a.property.symm
 have hdisjoint:Disjoint
     ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing Omega))
       (J:Set (PlaneRing Omega)):=by
   rw [Set.disjoint_left]
   intro x hx hxJ
   obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp hx
   exact hr (hcomap ▸ hxJ)
 change (Ideal.map f J).comap f=J
 change (Ideal.map (algebraMap (PlaneRing Omega) (Polynomial R)) J).comap
   (algebraMap (PlaneRing Omega) (Polynomial R))=J
 exact IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R) hJprime hdisjoint
include hfinite hgen in
theorem indexedFiberRelation_isMaximal
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let J:=relationKernel Omega (CoordinateField Omega (component a.1).1) order
   (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 have hJmax:J.IsMaximal:=relationKernel_isMaximal Omega
   (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
       (hfinite a.1) (hgen a.1)
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hunder:=indexedFiberRelation_under component lam mu nu order ht q hq a
 letI:((indexedFiberRelation component lam mu nu order ht q hq a).under
     (PlaneRing Omega)).IsMaximal:=by
   change ((indexedFiberRelation component lam mu nu order ht q hq a).comap
     (algebraMap (PlaneRing Omega) (Polynomial R))).IsMaximal
   simpa only [fiberLocalizePlane] using hunder ▸ hJmax
 exact Ideal.IsMaximal.of_isLocalization_of_disjoint
   (p.primeCompl.map c.toMonoidHom)
include hcomponent in
theorem indexedFiberRelation_injective
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Function.Injective
     (indexedFiberRelation component lam mu nu order ht q hq):=by
 intro a b hab
 have hunder:=congrArg (Ideal.comap (fiberLocalizePlane q hq)) hab
 rw [indexedFiberRelation_under component lam mu nu order ht q hq a,
   indexedFiberRelation_under component lam mu nu order ht q hq b] at hunder
 have heval:=congrArg (Ideal.comap (planeMap Omega order)) hunder
 rw [relationKernel_contract,relationKernel_contract] at heval
 have hprime:=congrArg (Ideal.comap (flagAlgHom lam mu nu).toRingHom) heval
 rw [flagEvaluation_kernel_contract,flagEvaluation_kernel_contract] at hprime
 have hcomp:component a.1=component b.1:=Subtype.ext hprime
 exact Subtype.ext (hcomponent hcomp)
include hcomponent hfinite hgen in
theorem indexedFiberRelation_pairwise_coprime
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Pairwise fun a b:IndexedFactorFiber component lam mu nu order ht q =>
     IsCoprime (indexedFiberRelation component lam mu nu order ht q hq a)
       (indexedFiberRelation component lam mu nu order ht q hq b):=by
 intro a b hab
 apply Ideal.isCoprime_iff_sup_eq.mpr
 exact (indexedFiberRelation_isMaximal component lam mu nu order ht hfinite hgen
   q hq a).coprime_of_ne
     (indexedFiberRelation_isMaximal component lam mu nu order ht hfinite hgen
       q hq b)
     (fun heq => hab (indexedFiberRelation_injective
       component hcomponent lam mu nu order ht q hq heq))
end
end ProximityPrize.SubmissionLower.RCN106
end PackedLegacy_Y9

/-! Packed from ProximityPrize.SubmissionLower.C8. -/
section PackedLegacy_C8
namespace ProximityPrize.SubmissionLower.RCN193
open RCN011 RCN021 RCN022 RCN226 RCN191 RCN120
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localizedRelation_under
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (localizedRelation K L order e ht hfinite).comap
     (localizePlane K L order e ht hfinite)=
     relationKernel K L order e ht:=by
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let f:=localizePlane K L order e ht hfinite
 let c:Polynomial (RatFunc K) →+*PlaneRing K:=Polynomial.C
 have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 letI:p.IsPrime:=hpmax.isPrime
 letI:Algebra (Polynomial (RatFunc K)) Rp:=inferInstance
 letI:IsLocalization p.primeCompl Rp:=inferInstance
 letI:Algebra (PlaneRing K) (Polynomial Rp):=
   Polynomial.algebra (Polynomial (RatFunc K)) Rp
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom)
     (Polynomial Rp):=Polynomial.isLocalization p.primeCompl Rp
 have hJprime:J.IsPrime:=RingHom.ker_isPrime _
 have hdisjoint:Disjoint
     ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing K)) (J:Set (PlaneRing K)):=by
   rw [Set.disjoint_left]
   intro a ha haJ
   obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp ha
   apply hr
   have hrJ:r∈J.comap c:=haJ
   have hcomap:J.comap c=p:=by
     simpa only [J,c,p] using relationKernel_comap_C K L order e ht
   rwa [hcomap] at hrJ
 change (Ideal.map f J).comap f=J
 change (Ideal.map (algebraMap (PlaneRing K) (Polynomial Rp)) J).comap
   (algebraMap (PlaneRing K) (Polynomial Rp))=J
 exact IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial Rp) hJprime hdisjoint
noncomputable def planeResidueEquiv
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   (PlaneRing K ⧸ relationKernel K L order e ht) ≃+*
     (LocalizedPlane K L order e ht hfinite ⧸
       localizedRelation K L order e ht hfinite):=by
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let S:=PlaneRing K
 let Sp:=LocalizedPlane K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let JP:=localizedRelation K L order e ht hfinite
 let f:=localizePlane K L order e ht hfinite
 let c:Polynomial (RatFunc K) →+*S:=Polynomial.C
 have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 letI:p.IsPrime:=hpmax.isPrime
 have hJmax:J.IsMaximal:=relationKernel_isMaximal K L order e ht hfinite hgen
 letI:J.IsPrime:=hJmax.isPrime
 have hJPmax:JP.IsMaximal:=localizedRelation_isMaximal
   K L order e ht hfinite hgen
 letI:JP.IsPrime:=hJPmax.isPrime
 letI:Algebra (Polynomial (RatFunc K)) Rp:=inferInstance
 letI:IsLocalization p.primeCompl Rp:=inferInstance
 letI:Algebra S Sp:=Polynomial.algebra (Polynomial (RatFunc K)) Rp
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) Sp:=
   Polynomial.isLocalization p.primeCompl Rp
 have hunder:JP.comap f=J:=localizedRelation_under K L order e ht hfinite
 have hf:f=algebraMap S Sp:=rfl
 have hunderAlg:JP.under S=J:=by
   change JP.comap (algebraMap S Sp)=J
   rw [←hf]
   exact hunder
 let g:(S ⧸ J) →+*(Sp ⧸ JP):=
   Ideal.quotientMap JP (algebraMap S Sp) hunderAlg.ge
 refine RingEquiv.ofBijective g ⟨?_,?_⟩
 · exact Ideal.quotientMap_injective' hunderAlg.le
 · exact IsLocalization.surjective_quotientMap_of_maximal_of_localization
     (p.primeCompl.map c.toMonoidHom) Sp (J:=J) (I:=JP)
       (H:=hunderAlg.ge) (hunderAlg ▸ hJmax)
end
end ProximityPrize.SubmissionLower.RCN193
end PackedLegacy_C8
end Compact_PackedLegacy
