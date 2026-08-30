import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.F
namespace ProximityPrize.SubmissionLower.RCN272
open scoped Classical BigOperators
open RCN002 RCN007
open RCN136 RCN231 RCN319
open RCN238 RCN264
open RCN243 RCN065
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable (φ:Polynomial K →+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def FiniteZeroSetBound
   (P:Ideal (MvPolynomial (Fin 3) Ω))
   (A:MvPolynomial (Fin 3) Ω) (cost:ℕ):Prop:=
 ∀ points:Finset (Fin 3 → Ω),
   (∀ v∈points,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) →
   (∀ v∈points,MvPolynomial.aeval v A=0) →
   points.card ≤ cost
structure ResidualComponentBudget
   (G T H:MvPolynomial (Fin 3) Ω)
   (Admissible:MvPolynomial (Fin 3) Ω → Prop) (wholeCost:ℕ) where
 cost:RegularComponent Ω G T H → ℕ
 zero_le:∀ (C:RegularComponent Ω G T H)
     (A:MvPolynomial (Fin 3) Ω),
   Admissible A → A∉C.1 → FiniteZeroSetBound C.1 A (cost C)
 sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCost
theorem agreement_fiber_card_le_of_zero_bound
   (P:Ideal (MvPolynomial (Fin 3) Ω))
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (Γ:Finset K)
   (p w:ℕ) [CharP Ω p] (hchar:w < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (x u₀ u₁:K) (cost:ℕ)
   (hzero:FiniteZeroSetBound P
     (agreementPolynomial φ F w x u₀ u₁) cost):
   (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤ cost:=by
 classical
 let fiber:=Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)
 let points:=fiber.image (selectedPoint φ selected)
 have hpointsP:∀ v∈points,
     P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   exact hpoint γ (Finset.mem_filter.mp hγ).1
 have hpointsA:∀ v∈points,
     MvPolynomial.aeval v (agreementPolynomial φ F w x u₀ u₁)=0:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   obtain ⟨hΓ,hagree⟩:=Finset.mem_filter.mp hγ
   exact (selected_agreement_zero_iff φ F selected p w hchar γ
     (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) x u₀ u₁).mpr hagree
 have hcount:=hzero points hpointsP hpointsA
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
 rwa [hcard] at hcount
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem prime_seed_incidence_sharp_of_residual_cost
   (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
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
     a ≤ (nodes.filter (fun i↦
       (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cost:ℕ)
   (hzero:∀ i∈nodes,
     agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)∉P →
     FiniteZeroSetBound P
       (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) cost):
   Γ.card*(a-w) ≤ (nodes.card-w)*cost+
     (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
 classical
 let I:=identityNodes φ P F nodes x u₀ u₁ w
 let relation:K → ι → Prop:=fun γ i↦
   (selected γ).eval (x i)=u₀ i+γ*u₁ i
 by_cases hI:I.card ≤ w
 · have hfiber:∀ i∈nodes \ I,
       (Γ.filter (fun γ↦relation γ i)).card ≤ cost:=by
     intro i hi
     obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
     have hproper:agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)∉P:=by
       intro hmem
       apply hnotI
       exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
     exact agreement_fiber_card_le_of_zero_bound φ P F selected Γ p w hchar
       hdegree hsolution hregular hpoint (x i) (u₀ i) (u₁ i) cost
       (hzero i hinodes hproper)
   have hcount:=RCN173.sharp_incidence_bound relation Γ nodes I a w
     cost (identityNodes_subset φ P F nodes x u₀ u₁ w) hI hwa han
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
     exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w
       hinj hc (fun t:{γ:K//γ∈Γ}↦t.1)
       (fun t↦selected t.1) (fun t↦hdegree t.1 t.2) hvalues
   have hfilter:Γ.filter
       (fun γ↦selected γ=P₀+Polynomial.C γ*P₁)=Γ:=
     Finset.filter_eq_self.mpr (fun γ hγ↦hpencil ⟨γ,hγ⟩)
   have hΓ:Γ.card ≤ e+1:=by
     have h:=hnoPencil P₀ P₁ h₀ h₁
     rwa [hfilter] at h
   have hZ:=seed_transcendental_of_many_identities φ P F hF hH
     nodes x u₀ u₁ w hw hinj hc hnonpoint
   have hδ:=coordinateDegree_pos_of_transcendental P hproj (2:Fin 3) hZ
   have hcharge:Γ.card*(a-w) ≤
       (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
     calc
       _ ≤ (e+1)*(a-w):=Nat.mul_le_mul_right _ hΓ
       _ ≤ _:=by
         simpa only [Nat.mul_one] using
           Nat.mul_le_mul_left ((e+1)*(a-w)) hδ
   omega
theorem aggregate_component_residual_incidence
   (G T H:MvPolynomial (Fin 3) Ω)
   {Seed:Type*} (S:Finset Seed) (v:Seed → Fin 3 → Ω)
   (hG:∀ γ∈S,MvPolynomial.eval (v γ) G=0)
   (hT:∀ γ∈S,MvPolynomial.eval (v γ) T=0)
   (hH:∀ γ∈S,MvPolynomial.eval (v γ) H≠0)
   (gap nodes pencil wholeCost zBudget:ℕ)
   (cost zDegree:RegularComponent Ω G T H → ℕ)
   (hcomponent:∀ C,
     (componentSeeds Ω G T H S v C).card*gap ≤
       nodes*cost C+pencil*gap*zDegree C)
   (hcost:(∑ C,cost C) ≤ wholeCost)
   (hz:(∑ C,zDegree C) ≤ zBudget):
   S.card*gap ≤ nodes*wholeCost+pencil*gap*zBudget:=by
 classical
 calc
   S.card*gap ≤ (∑ C:RegularComponent Ω G T H,
       (componentSeeds Ω G T H S v C).card)*gap:=
     Nat.mul_le_mul_right gap
       (card_le_sum_componentSeeds Ω G T H S v hG hT hH)
   _=∑ C:RegularComponent Ω G T H,
       (componentSeeds Ω G T H S v C).card*gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ C:RegularComponent Ω G T H,
       (nodes*cost C+pencil*gap*zDegree C):=
     Finset.sum_le_sum (fun C _↦hcomponent C)
   _=nodes*(∑ C:RegularComponent Ω G T H,cost C)+
       pencil*gap*(∑ C:RegularComponent Ω G T H,zDegree C):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum]
   _ ≤ nodes*wholeCost+pencil*gap*zBudget:=
     Nat.add_le_add (Nat.mul_le_mul_left nodes hcost)
       (Nat.mul_le_mul_left (pencil*gap) hz)
theorem proper_cut_seed_bound_of_residual_component_budget
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hdiv:G∣surfaceMap φ F)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i↦
       (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (Admissible:MvPolynomial (Fin 3) Ω → Prop)
   (wholeCost zBudget:ℕ)
   (hsparse:ResidualComponentBudget G T (regularitySurface φ F)
     Admissible wholeCost)
   (hadmissible:∀ i∈nodes,
     Admissible (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)))
   (hproj:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     ProjectionsFiniteSeparable Ω C.1)
   (hzbudget:(∑ C:RegularComponent Ω G T (regularitySurface φ F),
     actualCoordinateDegree Ω C.1 2) ≤ zBudget):
   Γ.card*(a-w) ≤ (nodes.card-w)*wholeCost+
     (e+1)*(a-w)*zBudget:=by
 classical
 let H:=regularitySurface φ F
 have hHp:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) H≠0:=by
   intro γ hγ
   change MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular γ hγ
 let zDegree:RegularComponent Ω G T H → ℕ:=
   fun C↦actualCoordinateDegree Ω C.1 2
 have hcomponent:∀ C:RegularComponent Ω G T H,
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C).card*
         (a-w) ≤
       (nodes.card-w)*hsparse.cost C+
         (e+1)*(a-w)*zDegree C:=by
   intro C
   have hsub:=componentSeeds_subset Ω G T H Γ
     (selectedPoint φ selected) C
   have hgmem:=regularComponent_G_mem Ω G T H C
   have hFmem:surfaceMap φ F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   apply prime_seed_incidence_sharp_of_residual_cost φ C.1 (hproj C)
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
     (hsparse.cost C)
   intro i hi hproper
   exact hsparse.zero_le C _ (hadmissible i hi) hproper
 exact aggregate_component_residual_incidence G T H Γ
   (selectedPoint φ selected) hGpoint hTpoint hHp (a-w)
   (nodes.card-w) (e+1) wholeCost zBudget hsparse.cost zDegree
   hcomponent hsparse.sum_cost_le hzbudget
end
end ProximityPrize.SubmissionLower.RCN272
