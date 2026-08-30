import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BV
import ProximityPrize.SubmissionLower.I3
import ProximityPrize.SubmissionLower.CB
namespace ProximityPrize.SubmissionLower.ContactImplicitPairSeedCount6600Research
open scoped Classical BigOperators
open ContactParameters6600Research ContactSingularLedger6600Research ContactCountingCaps6600Research
open ContactCountingCaps ContactGenericSurface ContactGenericInitialPoint
open ContactGeometricFirstTail ContactGeometricFactorCover
open ContactPrimeSeedIncidence ContactProperCutSeedCount ContactFactorCaps
open ContactInterpolation ContactTranslation ActualCoordinateDegreeSum
noncomputable section
variable {K:Type} [Field K]
def pairCost (A G:MvPolynomial (Fin 4) K):ContactParameters6600Research.DegreeVector:=
 ⟨ContactImplicitPairBudgets.pairYCost ⟨A,G⟩,
   ContactImplicitPairBudgets.pairRCost ⟨A,G⟩,
   ContactImplicitPairBudgets.pairZCost ⟨A,G⟩⟩
variable {ι:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq ι:=Classical.decEq ι
theorem implicit_pair_seed_bound_fixed
   (A G:MvPolynomial (Fin 4) K) (hG:Irreducible G)
   (hGR:G.degreeOf 2=1) (hproper:¬ G∣A)
   (hAbox:A∈globalCoefficientBox K implicitWeightedCap w algebraicCap 0)
   (hGbox:G∈globalCoefficientBox K implicitWeightedCap w algebraicCap 1)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=n) [CharP K prime]
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolutionA:∀ γ∈Γ,specialization K (selected γ) γ A=0)
   (hsolutionG:∀ γ∈Γ,specialization K (selected γ) γ G=0)
   (hregular:∀ γ∈Γ,
     specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) G)≠0)
   (hagreement:∀ γ∈Γ,
     agreements ≤ (nodes.filter (fun i =>
       (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w errors):
   Γ.card*gap ≤ (n-w)*dot liftedAgreement (pairCost A G)+
     (errors+1)*gap*ContactImplicitPairBudgets.pairZCost ⟨A,G⟩:=by
 classical
 let φ:=polynomialEmbedding K
 let factors:=surfaceFactors φ G
 let seedsFor:=fun g:MvPolynomial (Fin 3) (GenericField K) =>
   Γ.filter (fun γ => MvPolynomial.eval (selectedPoint φ selected γ) g=0)
 have hsub (g):seedsFor g ⊆ Γ:=Finset.filter_subset _ _
 have hAGcaps:=degree_bounds_of_mem_box A implicitWeightedCap w algebraicCap 0
   (by norm_num [w]) hAbox
 have hGGcaps:=degree_bounds_of_mem_box G implicitWeightedCap w algebraicCap 1
   (by norm_num [w]) hGbox
 have hAR:A.degreeOf 2=0:=Nat.eq_zero_of_le_zero hAGcaps.2.1
 have hAcaps:HasCaps (surfaceMap φ A) (legacyVector implicitCut):=by
   intro i
   fin_cases i
   · simpa [legacyVector,ContactCountingCaps.capAt,implicitCut,implicitYCap] using
       (surfaceMap_degreeOf_le φ A 0).trans hAGcaps.1
   · simpa [legacyVector,ContactCountingCaps.capAt,implicitCut] using
       (surfaceMap_degreeOf_le φ A 1).trans hAGcaps.2.1
   · simpa [legacyVector,ContactCountingCaps.capAt,implicitCut] using
       (surfaceMap_degreeOf_le φ A 2).trans hAGcaps.2.2
 have hFzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ G)=0:=by
   intro γ hγ
   rw [ContactImplicitPairSeedCount.canonical_selectedPoint_surface_evaluation,
     hsolutionG γ hγ,map_zero]
 have hAzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ A)=0:=by
   intro γ hγ
   rw [ContactImplicitPairSeedCount.canonical_selectedPoint_surface_evaluation,
     hsolutionA γ hγ,map_zero]
 have hcover:Γ ⊆ factors.biUnion seedsFor:=by
   intro γ hγ
   obtain ⟨g,hg,hz⟩:=exists_surfaceFactor_zero φ (polynomialEmbedding_injective K)
     G hG.ne_zero (selectedPoint φ selected γ) (hFzero γ hγ)
   exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_filter.mpr ⟨hγ,hz⟩⟩
 have hcard:Γ.card ≤ ∑ g∈factors,(seedsFor g).card:=
   (Finset.card_le_card hcover).trans Finset.card_biUnion_le
 have hsingle (g:MvPolynomial (Fin 3) (GenericField K)) (hg:g∈factors):
     (seedsFor g).card*gap ≤
       (n-w)*(∑ i:Fin 3,
         capAt (legacyVector liftedAgreement) i*
           capAt (ContactImplicitPairSeedCount.geometricPairCost A g) i)+
         (errors+1)*gap*
           capAt (ContactImplicitPairSeedCount.geometricPairCost A g) 2:=by
   obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec φ G g hg
   have hfacdegree (i:Fin 3):g.degreeOf i ≤ G.degreeOf i.succ:=
     (coordinate_degree_le_of_dvd i g (surfaceMap φ G) hdiv
       (surfaceMap_ne_zero φ (polynomialEmbedding_injective K) G hG.ne_zero)).trans
         (surfaceMap_degreeOf_le φ G i)
   have hgcaps:HasCaps g (legacyVector liftedSurface):=by
     intro i
     fin_cases i
     · simpa [legacyVector,ContactCountingCaps.capAt,liftedSurface,implicitYCap] using
         (hfacdegree 0).trans hGGcaps.1
     · simpa [legacyVector,ContactCountingCaps.capAt,liftedSurface] using
         (hfacdegree 1).trans hGGcaps.2.1
     · simpa [legacyVector,ContactCountingCaps.capAt,liftedSurface] using
         (hfacdegree 2).trans hGGcaps.2.2
   have hgates:=fixed_implicit_characteristic_gates g (surfaceMap φ A) hgcaps hAcaps
   have hreg:∀ γ∈seedsFor g,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
       (ContactPolynomialSolutions.polynomialPoint (φ.comp Polynomial.C)
         (selected γ) γ (φ Polynomial.X)) (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
     intro γ hγ
     exact (initialPoint_regular_iff K G (selected γ) γ).mpr (hregular γ (hsub g hγ))
   have hcap (i:ι):HasCaps (agreementPolynomial φ G w (x i) (u₀ i) (u₁ i))
       (legacyVector liftedAgreement):=
     ContactCountingCaps6600Research.fixed_implicit_agreement_caps φ G
       hGGcaps.1 hGGcaps.2.1 hGGcaps.2.2 (x i) (u₀ i) (u₁ i)
   have hcount:=proper_cut_seed_bound φ G g (surfaceMap φ A) hgi hdiv
     (ContactImplicitPairSeedCount.geometric_factor_proper_cut A G hG hGR hproper g hg)
     selected (seedsFor g) nodes x u₀ u₁ hinj prime w agreements errors
     (by norm_num [w]) (by norm_num [w,prime])
     (by norm_num [w,agreements,n,errors])
     (by rw [hnodes];norm_num [agreements,n,errors]) hgates.1 hgates.2
     (fun γ hγ => hdegree γ (hsub g hγ))
     (fun γ hγ => hsolutionG γ (hsub g hγ)) hreg
     (fun γ hγ => (Finset.mem_filter.mp hγ).2)
     (fun γ hγ => hAzero γ (hsub g hγ))
     (fun γ hγ => hagreement γ (hsub g hγ))
     (noLargeSelectedPencil_mono selected Γ (seedsFor g) w errors (hsub g) hnoPencil)
     (capAt (legacyVector liftedAgreement)) (fun i _ => hcap i)
   rw [hnodes] at hcount
   have hδ (i:Fin 3):=
     ContactImplicitPairSeedCount.coordinateMixedDegree_le_geometricPairCost φ A hAR g i
   exact hcount.trans (Nat.add_le_add
     (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt (legacyVector liftedAgreement) i) (hδ i))))
     (Nat.mul_le_mul_left ((errors+1)*gap) (hδ 2)))
 have hbudget (i:Fin 3):
     (∑ g∈factors,
       capAt (ContactImplicitPairSeedCount.geometricPairCost A g) i) ≤
         capAt (ContactImplicitPairSeedCount.pairCost A G) i:=
   ContactImplicitPairSeedCount.sum_geometricPairCost_le φ
     (polynomialEmbedding_injective K) A G hG.ne_zero i
 have hfubini:
     (∑ g∈factors,∑ i:Fin 3,capAt (legacyVector liftedAgreement) i*
         capAt (ContactImplicitPairSeedCount.geometricPairCost A g) i)=
       ∑ i:Fin 3,capAt (legacyVector liftedAgreement) i*
         (∑ g∈factors,
           capAt (ContactImplicitPairSeedCount.geometricPairCost A g) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Γ.card*gap ≤ (∑ g∈factors,(seedsFor g).card)*gap:=
     Nat.mul_le_mul_right gap hcard
   _=∑ g∈factors,(seedsFor g).card*gap:=by rw [Finset.sum_mul]
   _ ≤ ∑ g∈factors,((n-w)*(∑ i:Fin 3,
       capAt (legacyVector liftedAgreement) i*
         capAt (ContactImplicitPairSeedCount.geometricPairCost A g) i)+
       (errors+1)*gap*
         capAt (ContactImplicitPairSeedCount.geometricPairCost A g) 2):=
     Finset.sum_le_sum (fun g hg => hsingle g hg)
   _=(n-w)*(∑ i:Fin 3,capAt (legacyVector liftedAgreement) i*
       (∑ g∈factors,
         capAt (ContactImplicitPairSeedCount.geometricPairCost A g) i))+
       (errors+1)*gap*
         (∑ g∈factors,
           capAt (ContactImplicitPairSeedCount.geometricPairCost A g) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (n-w)*(∑ i:Fin 3,capAt (legacyVector liftedAgreement) i*
       capAt (ContactImplicitPairSeedCount.pairCost A G) i)+
       (errors+1)*gap*capAt (ContactImplicitPairSeedCount.pairCost A G) 2:=
     Nat.add_le_add (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt (legacyVector liftedAgreement) i)
         (hbudget i))))
       (Nat.mul_le_mul_left ((errors+1)*gap) (hbudget 2))
   _=(n-w)*dot liftedAgreement (pairCost A G)+
       (errors+1)*gap*ContactImplicitPairBudgets.pairZCost ⟨A,G⟩:=by
     simp [Fin.sum_univ_three,ContactCountingCaps.capAt,legacyVector,
       ContactImplicitPairSeedCount.pairCost,pairCost,
       ContactImplicitPairBudgets.pairYCost,ContactImplicitPairBudgets.pairRCost,
       ContactImplicitPairBudgets.pairZCost,dot]
end
end ProximityPrize.SubmissionLower.ContactImplicitPairSeedCount6600Research
