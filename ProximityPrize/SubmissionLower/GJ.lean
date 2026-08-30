import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AE
import ProximityPrize.SubmissionLower.D6
namespace ProximityPrize.SubmissionLower.ContactStratifiedResidualComponentAdapter6600Research
open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveZeroCount
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils
open ContactResidualSparseComponentAdapterResearch
open ContactNearPencilStratifiedIncidenceResearch
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable (phi:Polynomial K →+*Omega)
variable {Iota:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem prime_seed_incidence_of_stratified_residual_cost
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (hproj:ProjectionsFiniteSeparable Omega P)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap phi F∈P)
   (hH:surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Omega p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegreeSelected:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ w)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ gamma∈Gamma,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w e)
   (degreeCost unitCost U V:ℕ)
   (hfiber:∀ i∈nodes \
       identityNodes phi P F nodes x u0 u1 w,
     (Gamma.filter (fun gamma↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card ≤
       (w-(identityNodes phi P F nodes x u0 u1 w).card)*degreeCost+
         unitCost)
   (hdegree:∀ k ≤ w,
     (nodes.card-k)*(a-w)*(w-k) ≤ U*(a-k))
   (hunit:∀ k ≤ w,
     (nodes.card-k)*(a-w) ≤ V*(a-k)):
   Gamma.card*(a-w) ≤
     U*degreeCost+V*unitCost+
       (e+1)*(a-w)*actualCoordinateDegree Omega P 2:=by
 classical
 let identities:=identityNodes phi P F nodes x u0 u1 w
 let relation:K → Iota → Prop:=fun gamma i↦
   (selected gamma).eval (x i)=u0 i+gamma*u1 i
 by_cases hcard:identities.card ≤ w
 · have hmain:=stratified_incidence_bound relation Gamma nodes identities
     a w degreeCost unitCost U V
     (identityNodes_subset phi P F nodes x u0 u1 w)
     hcard hwa hagreement
     (by
       intro i hi
       exact hfiber i (by simpa only [identities] using hi))
     (hdegree identities.card hcard) (hunit identities.card hcard)
   exact hmain.trans (Nat.le_add_right _ _)
 · have hc:w < identities.card:=Nat.lt_of_not_ge hcard
   have hvalues:∀ (t:{gamma:K//gamma∈Gamma}) i,
       i∈identities →
       (selected t.1).eval (x i)=u0 i+t.1*u1 i:=by
     intro t
     exact selected_agrees_on_identity_nodes phi P F nodes x u0 u1 p w
       hchar (selected t.1) t.1 (hdegreeSelected t.1 t.2)
       (hsolution t.1 t.2) (hregular t.1 t.2) (hpoint t.1 t.2)
   obtain ⟨P0,P1,h0,h1,_,hpencil⟩:=
     exists_common_pencil_of_many_identities phi P F hF hH nodes x u0 u1 w
       hinj hc (fun t:{gamma:K//gamma∈Gamma}↦t.1)
       (fun t↦selected t.1) (fun t↦hdegreeSelected t.1 t.2) hvalues
   have hfilter:Gamma.filter
       (fun gamma↦selected gamma=P0+Polynomial.C gamma*P1)=
       Gamma:=
     Finset.filter_eq_self.mpr (fun gamma hgamma↦hpencil ⟨gamma,hgamma⟩)
   have hGamma:Gamma.card ≤ e+1:=by
     have h:=hnoPencil P0 P1 h0 h1
     rwa [hfilter] at h
   have hZ:=seed_transcendental_of_many_identities phi P F hF hH
     nodes x u0 u1 w hw hinj hc hnonpoint
   have hdelta:=coordinateDegree_pos_of_transcendental P hproj
     (2:Fin 3) hZ
   have htail:Gamma.card*(a-w) ≤
       (e+1)*(a-w)*actualCoordinateDegree Omega P 2:=by
     calc
       Gamma.card*(a-w) ≤ (e+1)*(a-w):=
         Nat.mul_le_mul_right _ hGamma
       _ ≤ (e+1)*(a-w)*actualCoordinateDegree Omega P 2:=by
         simpa only [Nat.mul_one] using
           Nat.mul_le_mul_left ((e+1)*(a-w)) hdelta
   exact htail.trans (Nat.le_add_left _ _)
theorem aggregate_component_stratified_incidence
   (G T H:MvPolynomial (Fin 3) Omega)
   {Seed:Type*} (S:Finset Seed) (v:Seed → Fin 3 → Omega)
   (hG:∀ gamma∈S,MvPolynomial.eval (v gamma) G=0)
   (hT:∀ gamma∈S,MvPolynomial.eval (v gamma) T=0)
   (hH:∀ gamma∈S,MvPolynomial.eval (v gamma) H≠0)
   (gap U V pencil degreeWhole unitWhole zBudget:ℕ)
   (degreeCost unitCost zDegree:RegularComponent Omega G T H → ℕ)
   (hcomponent:∀ C,
     (componentSeeds Omega G T H S v C).card*gap ≤
       U*degreeCost C+V*unitCost C+
         pencil*gap*zDegree C)
   (hdegree:(∑ C,degreeCost C) ≤ degreeWhole)
   (hunit:(∑ C,unitCost C) ≤ unitWhole)
   (hz:(∑ C,zDegree C) ≤ zBudget):
   S.card*gap ≤
     U*degreeWhole+V*unitWhole+pencil*gap*zBudget:=by
 classical
 calc
   S.card*gap ≤
       (∑ C:RegularComponent Omega G T H,
         (componentSeeds Omega G T H S v C).card)*gap:=
     Nat.mul_le_mul_right gap
       (card_le_sum_componentSeeds Omega G T H S v hG hT hH)
   _=∑ C:RegularComponent Omega G T H,
       (componentSeeds Omega G T H S v C).card*gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ C:RegularComponent Omega G T H,
       (U*degreeCost C+V*unitCost C+pencil*gap*zDegree C):=
     Finset.sum_le_sum (fun C _↦hcomponent C)
   _=U*(∑ C:RegularComponent Omega G T H,degreeCost C)+
       V*(∑ C:RegularComponent Omega G T H,unitCost C)+
       pencil*gap*
         (∑ C:RegularComponent Omega G T H,zDegree C):=by
     simp only [Finset.sum_add_distrib,Finset.mul_sum]
   _ ≤ U*degreeWhole+V*unitWhole+pencil*gap*zBudget:=
     Nat.add_le_add
       (Nat.add_le_add (Nat.mul_le_mul_left U hdegree)
         (Nat.mul_le_mul_left V hunit))
       (Nat.mul_le_mul_left (pencil*gap) hz)
end
end ProximityPrize.SubmissionLower.ContactStratifiedResidualComponentAdapter6600Research
