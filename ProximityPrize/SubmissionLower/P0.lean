import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.O9
namespace ProximityPrize.SubmissionLower.ContactSeedlessProperCutResearch
open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveZeroCount ActualCurveProjectionBounds
open ActualCoordinateDegreeSum ActualPlanePositiveOrder
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount
open ContactSeedlessPrimeIncidenceResearch
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable (phi:Polynomial K →+*Omega)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
def seedlessCut:MvPolynomial (Fin 3) Omega:=MvPolynomial.X 2
theorem seedless_proper_cut_bound
   (hphi:Function.Injective phi)
   (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) Omega)
   (hG:Irreducible G) (hdiv:G∣surfaceMap phi F)
   (hproper:¬ G∣seedlessCut)
   (Gamma:Finset (Polynomial K))
   (nodes:Finset Iota) (x u:Iota → K) (hinj:Set.InjOn x nodes)
   (p w a:ℕ) [CharP Omega p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ j k:Fin 3,j≠k →
     (seedlessCut (Omega:=Omega)).degreeOf j*G.degreeOf k+
       G.degreeOf j*(seedlessCut (Omega:=Omega)).degreeOf k < p)
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolution:∀ S∈Gamma,specialization K S 0 F=0)
   (hregular:∀ S∈Gamma,MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ S∈Gamma,
     MvPolynomial.eval (seedlessPoint phi S) G=0)
   (hagreement:∀ S∈Gamma,
     a ≤ (nodes.filter (fun i => S.eval (x i)=u i)).card)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial phi F w (x i) (u i) 0).degreeOf j ≤ cap j):
   Gamma.card*(a-w) ≤
     (nodes.card-w)*
       (∑ i,cap i*coordinateMixedDegree Omega G seedlessCut i):=by
 classical
 let T:MvPolynomial (Fin 3) Omega:=seedlessCut
 let H:=regularitySurface phi F
 have hTpoint:∀ S∈Gamma,
     MvPolynomial.eval (seedlessPoint phi S) T=0:=by
   intro S hS
   simp [T,seedlessCut,seedlessPoint_value]
 have hHp:∀ S∈Gamma,
     MvPolynomial.eval (seedlessPoint phi S) H≠0:=by
   intro S hS
   change MvPolynomial.eval (seedlessPoint phi S)
     (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [seedlessPoint_surface_evaluation]
   exact hregular S hS
 let degree:RegularComponent Omega G T H → Fin 3 → ℕ:=
   fun C i => actualCoordinateDegree Omega C.1 i
 have hcomponent:∀ C:RegularComponent Omega G T H,
     (componentSeeds Omega G T H Gamma (seedlessPoint phi) C).card*
         (a-w) ≤
       (nodes.card-w)*(∑ i,cap i*degree C i):=by
   intro C
   have hsub:=componentSeeds_subset Omega G T H Gamma (seedlessPoint phi) C
   have hgmem:=regularComponent_G_mem Omega G T H C
   have htmem:=regularComponent_T_mem Omega G T H C
   have hFmem:surfaceMap phi F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   have hproj:ProjectionsFiniteSeparable Omega C.1:=
     all_transcendental_coordinates_finite_separable Omega C.1 p G T
       hG hgmem htmem hproper hGdegree hcutDegree
   exact seedless_prime_incidence phi C.1 hphi hproj
     (regularComponent_ne_point Omega G T H C) F hFmem
     (regularComponent_H_not_mem Omega G T H C) htmem
     (componentSeeds Omega G T H Gamma (seedlessPoint phi) C)
     nodes x u hinj p w a hw hchar hwa han
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => hsolution S (hsub hS))
     (fun S hS => hregular S (hsub hS))
     (fun S hS => componentSeeds_on_prime Omega G T H Gamma
       (seedlessPoint phi) C S hS)
     (fun S hS => hagreement S (hsub hS)) cap hcap
 have hbudget:∀ i,
     (∑ C:RegularComponent Omega G T H,
       actualCoordinateDegree Omega C.1 i) ≤
         coordinateMixedDegree Omega G T i:=
   regularComponents_degree_budget phi F G T p hG hproper hGdegree hcutDegree
 have hagg:=aggregate_component_incidence Omega G T H Gamma
   (seedlessPoint phi) hGpoint hTpoint hHp (a-w) (nodes.card-w) 0
   cap (coordinateMixedDegree Omega G T) degree
   (fun C => by simpa only [Nat.zero_mul,Nat.add_zero] using hcomponent C)
   hbudget
 simpa only [T,Nat.zero_mul,Nat.add_zero] using hagg
end
end ProximityPrize.SubmissionLower.ContactSeedlessProperCutResearch
