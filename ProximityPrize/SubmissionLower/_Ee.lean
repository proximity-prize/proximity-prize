import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.F
import ProximityPrize.SubmissionLower.Y
namespace ProximityPrize.SubmissionLower.ContactJointProperCutSeedCount
open ActualCurveCoordinateField ActualCurveZeroCount ActualCurveProjectionBounds
open ActualCoordinateDegreeSum ActualCurveJointProjectionBounds
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable (φ:Polynomial K →+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
def JointRProvider (G T:MvPolynomial (Fin 3) Ω) (p:ℕ):Prop:=
 ∀ (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime],G∈P →
   Transcendental Ω (coordinate Ω P 1) →
     JointOrderCertificate Ω (Equiv.swap 0 1) G T p
theorem proper_cut_seed_bound_of_projection_sum_joint_R
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree Ω G T 0 < p)
   (hmixedZ:coordinateMixedDegree Ω G T 2 < p)
   (hjoint:JointRProvider G T p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap budget:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
   (hbudget:∀ i,
     (∑ C:RegularComponent Ω G T (regularitySurface φ F),
       actualCoordinateDegree Ω C.1 i) ≤ budget i):
   Γ.card*(a-w) ≤ (nodes.card-w)*(∑ i,cap i*budget i)+
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
   fun C i => actualCoordinateDegree Ω C.1 i
 have hcomponent:∀ C:RegularComponent Ω G T H,
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C).card*(a-w) ≤
       (nodes.card-w)*(∑ i,cap i*degree C i)+
         (e+1)*(a-w)*degree C 2:=by
   intro C
   have hsub:=componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C
   have hgmem:=regularComponent_G_mem Ω G T H C
   have htmem:=regularComponent_T_mem Ω G T H C
   have hFmem:surfaceMap φ F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   have hproj:ProjectionsFiniteSeparable Ω C.1:=
     projectionsFiniteSeparable_of_joint_R_provider Ω C.1 p G T hG hgmem htmem
       hproper hGdegree hmixedY hmixedZ (hjoint C.1 hgmem)
   exact prime_seed_incidence_sharp φ C.1 hproj
     (regularComponent_ne_point Ω G T H C) F hFmem
     (regularComponent_H_not_mem Ω G T H C) selected
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C)
     nodes x u₀ u₁ hinj p w a e hw hchar hwa han
     (fun γ hγ => hdegree γ (hsub hγ))
     (fun γ hγ => hsolution γ (hsub hγ))
     (fun γ hγ => hregular γ (hsub hγ))
     (fun γ hγ => componentSeeds_on_prime Ω G T H Γ
       (selectedPoint φ selected) C γ hγ)
     (fun γ hγ => hagreement γ (hsub hγ))
     (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil) cap hcap
 exact aggregate_component_incidence Ω G T H Γ (selectedPoint φ selected)
   hGpoint hTpoint hHp (a-w) (nodes.card-w) (e+1)
   cap budget degree hcomponent hbudget
theorem regularComponents_degree_budget_joint_R
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (p:ℕ) [CharP Ω p] (hG:Irreducible G) (hproper:¬ G∣T)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree Ω G T 0 < p)
   (hmixedZ:coordinateMixedDegree Ω G T 2 < p)
   (hjoint:JointRProvider G T p):
   ∀ i,(∑ C:RegularComponent Ω G T (regularitySurface φ F),
     actualCoordinateDegree Ω C.1 i) ≤ coordinateMixedDegree Ω G T i:=by
 letI:∀ C:RegularComponent Ω G T (regularitySurface φ F),C.1.IsPrime:=
   fun C => regularComponent_isPrime Ω G T (regularitySurface φ F) C
 exact sum_actualCoordinateDegree_at_le_of_joint_R_provider Ω
   (fun C:RegularComponent Ω G T (regularitySurface φ F) => C.1)
   Subtype.val_injective p G T hG
   (regularComponent_G_mem Ω G T (regularitySurface φ F))
   (regularComponent_T_mem Ω G T (regularitySurface φ F))
   hproper hGdegree hmixedY hmixedZ
   (fun C htr => hjoint C.1
     (regularComponent_G_mem Ω G T (regularitySurface φ F) C) htr)
theorem proper_cut_seed_bound_joint_R
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree Ω G T 0 < p)
   (hmixedZ:coordinateMixedDegree Ω G T 2 < p)
   (hjoint:JointRProvider G T p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j):
   Γ.card*(a-w) ≤
     (nodes.card-w)*(∑ i,cap i*coordinateMixedDegree Ω G T i)+
     (e+1)*(a-w)*coordinateMixedDegree Ω G T 2:=
 proper_cut_seed_bound_of_projection_sum_joint_R φ F G T hG hdiv hproper
   selected Γ nodes x u₀ u₁ hinj p w a e hw hchar hwa han hGdegree
   hmixedY hmixedZ hjoint hdegree hsolution hregular hGpoint hTpoint
   hagreement hnoPencil cap (coordinateMixedDegree Ω G T) hcap
   (regularComponents_degree_budget_joint_R φ F G T p hG hproper
     hGdegree hmixedY hmixedZ hjoint)
end
end ProximityPrize.SubmissionLower.ContactJointProperCutSeedCount
