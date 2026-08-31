import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProperCutSeedCount
import ProximityPrize.SubmissionLower.ContactCountingCaps
import ProximityPrize.SubmissionLower.ContactImplicitPairBudgets
import ProximityPrize.SubmissionLower.ContactCountingLedger
namespace ProximityPrize.SubmissionLower.ContactImplicitPairSeedCount
open scoped Classical BigOperators
open ContactAlignmentParameters ContactImplicitLiftParameters ContactCountingCaps
open ContactCountingLedger ContactImplicitPairBudgets ContactGenericSurface
open ContactGenericInitialPoint ContactGeometricFirstTail ContactGeometricFactorCover
open ContactPrimeSeedIncidence ContactProperCutSeedCount ContactFactorCaps
open ContactInterpolation ContactTranslation ActualCoordinateDegreeSum
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def pairCost (A G:MvPolynomial (Fin 4) K):DegreeVector:=
  ⟨pairYCost ⟨A,G⟩,pairRCost ⟨A,G⟩,pairZCost ⟨A,G⟩⟩
def geometricPairCost (A:MvPolynomial (Fin 4) K)
    (g:MvPolynomial (Fin 3) Ω):DegreeVector:=
  ⟨g.degreeOf 1*A.degreeOf 3,
    g.degreeOf 0*A.degreeOf 3+g.degreeOf 2*A.degreeOf 1,
    g.degreeOf 1*A.degreeOf 1⟩
theorem capAt_dot (a b:DegreeVector):
    (∑ i:Fin 3,capAt a i*capAt b i)=dot a b:=by
  simp [Fin.sum_univ_three,capAt,dot]
theorem coordinateMixedDegree_le_geometricPairCost
    (φ:Polynomial K →+*Ω) (A:MvPolynomial (Fin 4) K)
    (hAR:A.degreeOf 2=0) (g:MvPolynomial (Fin 3) Ω) (i:Fin 3):
    coordinateMixedDegree Ω g (surfaceMap φ A) i ≤ capAt (geometricPairCost A g) i:=by
  have hTY:(surfaceMap φ A).degreeOf (0:Fin 3) ≤ A.degreeOf (1:Fin 4):=
    surfaceMap_degreeOf_le φ A (0:Fin 3)
  have hTRle:(surfaceMap φ A).degreeOf (1:Fin 3) ≤ A.degreeOf (2:Fin 4):=
    surfaceMap_degreeOf_le φ A (1:Fin 3)
  rw [hAR] at hTRle
  have hTR:(surfaceMap φ A).degreeOf (1:Fin 3)=0:=
    Nat.eq_zero_of_le_zero hTRle
  have hTZ:(surfaceMap φ A).degreeOf (2:Fin 3) ≤ A.degreeOf (3:Fin 4):=
    surfaceMap_degreeOf_le φ A (2:Fin 3)
  fin_cases i
  · simpa [coordinateMixedDegree_zero,hTR,capAt,geometricPairCost] using
      Nat.mul_le_mul_left (g.degreeOf 1) hTZ
  · have h:=Nat.add_le_add
      (Nat.mul_le_mul_right (g.degreeOf 2) hTY)
      (Nat.mul_le_mul_left (g.degreeOf 0) hTZ)
    simpa [coordinateMixedDegree_one,capAt,geometricPairCost,
      Nat.mul_comm,Nat.add_comm] using h
  · simpa [coordinateMixedDegree_two,hTR,capAt,geometricPairCost,Nat.mul_comm] using
      Nat.mul_le_mul_right (g.degreeOf 1) hTY
theorem sum_geometricPairCost_le
    (φ:Polynomial K →+*Ω) (hφ:Function.Injective φ)
    (A G:MvPolynomial (Fin 4) K) (hG:G≠0) (i:Fin 3):
    (∑ g∈surfaceFactors φ G,capAt (geometricPairCost A g) i) ≤ capAt (pairCost A G) i:=by
  have hY:=surfaceFactors_degree_budget φ hφ G hG (0:Fin 3)
  have hR:=surfaceFactors_degree_budget φ hφ G hG (1:Fin 3)
  have hZ:=surfaceFactors_degree_budget φ hφ G hG (2:Fin 3)
  fin_cases i
  · simpa [capAt,geometricPairCost,pairCost,pairYCost, ←Finset.sum_mul] using
      Nat.mul_le_mul_right (A.degreeOf 3) hR
  · simpa [capAt,geometricPairCost,pairCost,pairRCost,
      Finset.sum_add_distrib, ←Finset.sum_mul] using
      Nat.add_le_add (Nat.mul_le_mul_right (A.degreeOf 3) hY)
        (Nat.mul_le_mul_right (A.degreeOf 1) hZ)
  · simpa [capAt,geometricPairCost,pairCost,pairZCost, ←Finset.sum_mul] using
      Nat.mul_le_mul_right (A.degreeOf 1) hR
theorem canonical_selectedPoint_surface_evaluation
    (selected:K → Polynomial K) (γ:K) (F:MvPolynomial (Fin 4) K):
    MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
      (surfaceMap (polynomialEmbedding K) F)=
        polynomialEmbedding K (specialization K (selected γ) γ F):=by
  rw [selectedPoint_evaluation]
  exact evaluation_at_initialPoint K (selected γ) γ F
theorem geometric_factor_proper_cut
    (A G:MvPolynomial (Fin 4) K) (hG:Irreducible G)
    (hGR:G.degreeOf 2=1) (hproper:¬ G∣A)
    (g:MvPolynomial (Fin 3) (GenericField K))
    (hg:g∈surfaceFactors (polynomialEmbedding K) G):
    ¬ g∣surfaceMap (polynomialEmbedding K) A:=by
  obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec (polynomialEmbedding K) G g hg
  have hpos:0 < G.degreeOf 1+G.degreeOf 2+G.degreeOf 3:=by omega
  have hgeo:g∣geometricSurfaceMap K (GenericField K) G:=by
    simpa only [canonical_geometricSurfaceMap] using hdiv
  intro h
  apply hproper
  apply (geometric_factor_dvd_iff K (GenericField K) G A hG hpos g hgi hgeo).mp
  simpa only [canonical_geometricSurfaceMap] using h
variable {ι:Type*}
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
      agreements ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
    (hnoPencil:NoLargeSelectedPencil selected Γ w errors):
    Γ.card*gap ≤ (n-w)*dot liftedAgreement (pairCost A G)+
      (errors+1)*gap*pairZCost ⟨A,G⟩:=by
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
  have hAcaps:HasCaps (surfaceMap φ A) implicitCut:=by
    intro i
    fin_cases i
    · exact (surfaceMap_degreeOf_le φ A 0).trans hAGcaps.1
    · exact (surfaceMap_degreeOf_le φ A 1).trans hAGcaps.2.1
    · exact (surfaceMap_degreeOf_le φ A 2).trans hAGcaps.2.2
  have hFzero:∀ γ∈Γ,
      MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ G)=0:=by
    intro γ hγ
    rw [canonical_selectedPoint_surface_evaluation,hsolutionG γ hγ,map_zero]
  have hAzero:∀ γ∈Γ,
      MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ A)=0:=by
    intro γ hγ
    rw [canonical_selectedPoint_surface_evaluation,hsolutionA γ hγ,map_zero]
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
          capAt liftedAgreement i*capAt (geometricPairCost A g) i)+
          (errors+1)*gap*capAt (geometricPairCost A g) 2:=by
    obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec φ G g hg
    have hfacdegree (i:Fin 3):g.degreeOf i ≤ G.degreeOf i.succ:=
      (coordinate_degree_le_of_dvd i g (surfaceMap φ G) hdiv
        (surfaceMap_ne_zero φ (polynomialEmbedding_injective K) G hG.ne_zero)).trans
          (surfaceMap_degreeOf_le φ G i)
    have hgcaps:HasCaps g liftedSurface:=by
      intro i
      fin_cases i
      · exact (hfacdegree 0).trans hGGcaps.1
      · exact (hfacdegree 1).trans hGGcaps.2.1
      · exact (hfacdegree 2).trans hGGcaps.2.2
    have hgates:=fixed_implicit_characteristic_gates g (surfaceMap φ A) hgcaps hAcaps
    have hreg:∀ γ∈seedsFor g,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
        (ContactPolynomialSolutions.polynomialPoint (φ.comp Polynomial.C)
          (selected γ) γ (φ Polynomial.X)) (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
      intro γ hγ
      exact (initialPoint_regular_iff K G (selected γ) γ).mpr (hregular γ (hsub g hγ))
    have hcap (i:ι):HasCaps (agreementPolynomial φ G w (x i) (u₀ i) (u₁ i))
        liftedAgreement:=
      fixed_implicit_agreement_caps φ G hGGcaps.1 hGGcaps.2.1 hGGcaps.2.2 (x i) (u₀ i) (u₁ i)
    have hcount:=proper_cut_seed_bound φ G g (surfaceMap φ A) hgi hdiv
      (geometric_factor_proper_cut A G hG hGR hproper g hg) selected (seedsFor g)
      nodes x u₀ u₁ hinj prime w agreements errors
      (by norm_num [w]) (by norm_num [w,prime]) (by norm_num [w,agreements])
      (by rw [hnodes];norm_num [agreements,n]) hgates.1 hgates.2
      (fun γ hγ => hdegree γ (hsub g hγ))
      (fun γ hγ => hsolutionG γ (hsub g hγ)) hreg
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
      (fun γ hγ => hAzero γ (hsub g hγ))
      (fun γ hγ => hagreement γ (hsub g hγ))
      (noLargeSelectedPencil_mono selected Γ (seedsFor g) w errors (hsub g) hnoPencil)
      (capAt liftedAgreement) (fun i _ => hcap i)
    rw [hnodes] at hcount
    have hδ (i:Fin 3):=coordinateMixedDegree_le_geometricPairCost φ A hAR g i
    exact hcount.trans (Nat.add_le_add
      (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
        (fun i _ => Nat.mul_le_mul_left (capAt liftedAgreement i) (hδ i))))
      (Nat.mul_le_mul_left ((errors+1)*gap) (hδ 2)))
  have hbudget (i:Fin 3):
      (∑ g∈factors,capAt (geometricPairCost A g) i) ≤ capAt (pairCost A G) i:=
    sum_geometricPairCost_le φ (polynomialEmbedding_injective K) A G hG.ne_zero i
  have hfubini:
      (∑ g∈factors,∑ i:Fin 3,capAt liftedAgreement i*capAt (geometricPairCost A g) i)=
        ∑ i:Fin 3,capAt liftedAgreement i*
          (∑ g∈factors,capAt (geometricPairCost A g) i):=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc
    Γ.card*gap ≤ (∑ g∈factors,(seedsFor g).card)*gap:=Nat.mul_le_mul_right gap hcard
    _=∑ g∈factors,(seedsFor g).card*gap:=by rw [Finset.sum_mul]
    _ ≤ ∑ g∈factors,((n-w)*(∑ i:Fin 3,
        capAt liftedAgreement i*capAt (geometricPairCost A g) i)+
          (errors+1)*gap*capAt (geometricPairCost A g) 2):=
      Finset.sum_le_sum (fun g hg => hsingle g hg)
    _=(n-w)*(∑ i:Fin 3,capAt liftedAgreement i*
        (∑ g∈factors,capAt (geometricPairCost A g) i))+
          (errors+1)*gap*(∑ g∈factors,capAt (geometricPairCost A g) 2):=by
      rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
    _ ≤ (n-w)*
        (∑ i:Fin 3,capAt liftedAgreement i*capAt (pairCost A G) i)+
        (errors+1)*gap*capAt (pairCost A G) 2:=
      Nat.add_le_add (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
        (fun i _ => Nat.mul_le_mul_left (capAt liftedAgreement i) (hbudget i))))
        (Nat.mul_le_mul_left ((errors+1)*gap) (hbudget 2))
    _=(n-w)*dot liftedAgreement (pairCost A G)+
        (errors+1)*gap*pairZCost ⟨A,G⟩:=by
      rw [capAt_dot]
      rfl
end
end ProximityPrize.SubmissionLower.ContactImplicitPairSeedCount
