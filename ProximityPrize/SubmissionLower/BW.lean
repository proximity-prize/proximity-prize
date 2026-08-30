import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BV
namespace ProximityPrize.SubmissionLower.RCN172
open scoped Classical BigOperators
open RCN169 RCN136 RCN135
open RCN138 RCN137
open RCN238 RCN243 RCN081
open RCN174 RCN319 RCN001
open RCN068
noncomputable section
variable {K:Type} [Field K]
variable {ι:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq ι:=Classical.decEq ι
theorem implicit_pair_seed_bound
   (A G:MvPolynomial (Fin 4) K) (hG:Irreducible G)
   (hGR:G.degreeOf 2=1) (hproper:¬ G∣A)
   (implicitD w jY jZ p n a e:ℕ)
   (hAbox:A∈globalCoefficientBox K implicitD w jZ 0)
   (hGbox:G∈globalCoefficientBox K implicitD w jZ 1)
   (hjY:(implicitD-1)/w=jY)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=n) [CharP K p]
   (hw:1 ≤ w) (hchar:w < p) (hwa:w < a) (han:a ≤ n)
   (hjYsmall:jY < p) (hjZsmall:jZ < p)
   (hmixedSmall:2*jY*jZ < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolutionA:∀ γ∈Γ,specialization K (selected γ) γ A=0)
   (hsolutionG:∀ γ∈Γ,specialization K (selected γ) γ G=0)
   (hregular:∀ γ∈Γ,
     specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) G)≠0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i =>
       (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e):
   Γ.card*(a-w) ≤
     (n-w)*
       ((1+2*w*jY)*pairYCost ⟨A,G⟩+
         w*pairRCost ⟨A,G⟩+
         (2*w*jZ+1)*pairZCost ⟨A,G⟩)+
       (e+1)*(a-w)*pairZCost ⟨A,G⟩:=by
 classical
 let φ:=polynomialEmbedding K
 let factors:=surfaceFactors φ G
 let seedsFor:=fun g:MvPolynomial (Fin 3) (GenericField K) =>
   Γ.filter (fun γ => MvPolynomial.eval (selectedPoint φ selected γ) g=0)
 let surfaceCap:RCN051.DegreeVector:=⟨jY,1,jZ⟩
 let cutCap:RCN051.DegreeVector:=⟨jY,0,jZ⟩
 let agreementCap:RCN051.DegreeVector:=
   ⟨1+2*w*jY,w,2*w*jZ+1⟩
 have hsub (g):seedsFor g ⊆ Γ:=Finset.filter_subset _ _
 have hAGcaps:=degree_bounds_of_mem_box A implicitD w jZ 0 hw hAbox
 have hGGcaps:=degree_bounds_of_mem_box G implicitD w jZ 1 hw hGbox
 have hAY:A.degreeOf 1 ≤ jY:=hAGcaps.1.trans_eq hjY
 have hGY:G.degreeOf 1 ≤ jY:=hGGcaps.1.trans_eq hjY
 have hAR:A.degreeOf 2=0:=Nat.eq_zero_of_le_zero hAGcaps.2.1
 have hAcaps:HasCaps (surfaceMap φ A) cutCap:=by
   intro i
   fin_cases i
   · exact (surfaceMap_degreeOf_le φ A 0).trans hAY
   · exact (surfaceMap_degreeOf_le φ A 1).trans hAGcaps.2.1
   · exact (surfaceMap_degreeOf_le φ A 2).trans hAGcaps.2.2
 have hFzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ G)=0:=by
   intro γ hγ
   rw [RCN170.canonical_selectedPoint_surface_evaluation,
     hsolutionG γ hγ,map_zero]
 have hAzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ A)=0:=by
   intro γ hγ
   rw [RCN170.canonical_selectedPoint_surface_evaluation,
     hsolutionA γ hγ,map_zero]
 have hcover:Γ ⊆ factors.biUnion seedsFor:=by
   intro γ hγ
   obtain ⟨g,hg,hz⟩:=exists_surfaceFactor_zero φ
     (polynomialEmbedding_injective K) G hG.ne_zero
     (selectedPoint φ selected γ) (hFzero γ hγ)
   exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_filter.mpr ⟨hγ,hz⟩⟩
 have hcard:Γ.card ≤ ∑ g∈factors,(seedsFor g).card:=
   (Finset.card_le_card hcover).trans Finset.card_biUnion_le
 have hsingle (g:MvPolynomial (Fin 3) (GenericField K)) (hg:g∈factors):
     (seedsFor g).card*(a-w) ≤
       (n-w)*(∑ i:Fin 3,
         capAt agreementCap i*
           capAt (RCN170.geometricPairCost A g) i)+
         (e+1)*(a-w)*
           capAt (RCN170.geometricPairCost A g) 2:=by
   obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec φ G g hg
   have hfacdegree (i:Fin 3):g.degreeOf i ≤ G.degreeOf i.succ:=
     (coordinate_degree_le_of_dvd i g (surfaceMap φ G) hdiv
       (surfaceMap_ne_zero φ (polynomialEmbedding_injective K) G hG.ne_zero)).trans
         (surfaceMap_degreeOf_le φ G i)
   have hgcaps:HasCaps g surfaceCap:=by
     intro i
     fin_cases i
     · exact (hfacdegree 0).trans hGY
     · exact (hfacdegree 1).trans hGGcaps.2.1
     · exact (hfacdegree 2).trans hGGcaps.2.2
   have hsurfaceSmall:∀ j,capAt surfaceCap j < p:=by
     intro j
     fin_cases j
     · simpa [surfaceCap,capAt] using hjYsmall
     · simpa [surfaceCap,capAt] using lt_of_le_of_lt hw hchar
     · simpa [surfaceCap,capAt] using hjZsmall
   have hgates:=actual_characteristic_gates g (surfaceMap φ A)
     surfaceCap cutCap p hgcaps hAcaps hsurfaceSmall
     (by simpa [RCN051.mixed,surfaceCap,cutCap,
       RCN051.unitY] using hjZsmall)
     (by
       simp [RCN051.mixed,surfaceCap,cutCap,
         RCN051.unitR]
       rw [show jY*jZ+jZ*jY=2*jY*jZ by ring]
       exact hmixedSmall)
     (by simpa [RCN051.mixed,surfaceCap,cutCap,
       RCN051.unitZ] using hjYsmall)
   have hreg:∀ γ∈seedsFor g,
       MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
         (RCN231.polynomialPoint (φ.comp Polynomial.C)
           (selected γ) γ (φ Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
     intro γ hγ
     exact (initialPoint_regular_iff K G (selected γ) γ).mpr
       (hregular γ (hsub g hγ))
   have hcap (i:ι):HasCaps
       (agreementPolynomial φ G w (x i) (u₀ i) (u₁ i)) agreementCap:=by
     have h:=surface_agreement_caps φ G jY 1 jZ (by decide)
       hGY hGGcaps.2.1 hGGcaps.2.2 w
       (fun j => (j.factorial:K)⁻¹) (x i) (u₀ i) (u₁ i)
     simpa [agreementPolynomial,agreementCaps,agreementCap] using h
   have hcount:=proper_cut_seed_bound φ G g (surfaceMap φ A) hgi hdiv
     (RCN170.geometric_factor_proper_cut
       A G hG hGR hproper g hg)
     selected (seedsFor g) nodes x u₀ u₁ hinj p w a e hw hchar hwa
     (by simpa [hnodes] using han) hgates.1 hgates.2
     (fun γ hγ => hdegree γ (hsub g hγ))
     (fun γ hγ => hsolutionG γ (hsub g hγ)) hreg
     (fun γ hγ => (Finset.mem_filter.mp hγ).2)
     (fun γ hγ => hAzero γ (hsub g hγ))
     (fun γ hγ => hagreement γ (hsub g hγ))
     (noLargeSelectedPencil_mono selected Γ (seedsFor g) w e (hsub g) hnoPencil)
     (capAt agreementCap) (fun i _ => hcap i)
   rw [hnodes] at hcount
   have hδ (i:Fin 3):=
     RCN170.coordinateMixedDegree_le_geometricPairCost
       φ A hAR g i
   exact hcount.trans (Nat.add_le_add
     (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt agreementCap i) (hδ i))))
     (Nat.mul_le_mul_left ((e+1)*(a-w)) (hδ 2)))
 have hbudget (i:Fin 3):
     (∑ g∈factors,
       capAt (RCN170.geometricPairCost A g) i) ≤
         capAt (RCN170.pairCost A G) i:=
   RCN170.sum_geometricPairCost_le φ
     (polynomialEmbedding_injective K) A G hG.ne_zero i
 have hfubini:
     (∑ g∈factors,∑ i:Fin 3,capAt agreementCap i*
         capAt (RCN170.geometricPairCost A g) i)=
       ∑ i:Fin 3,capAt agreementCap i*
         (∑ g∈factors,
           capAt (RCN170.geometricPairCost A g) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Γ.card*(a-w) ≤ (∑ g∈factors,(seedsFor g).card)*(a-w):=
     Nat.mul_le_mul_right (a-w) hcard
   _=∑ g∈factors,(seedsFor g).card*(a-w):=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g∈factors,((n-w)*(∑ i:Fin 3,
       capAt agreementCap i*
         capAt (RCN170.geometricPairCost A g) i)+
       (e+1)*(a-w)*
         capAt (RCN170.geometricPairCost A g) 2):=
     Finset.sum_le_sum (fun g hg => hsingle g hg)
   _=(n-w)*(∑ i:Fin 3,capAt agreementCap i*
       (∑ g∈factors,
         capAt (RCN170.geometricPairCost A g) i))+
       (e+1)*(a-w)*
         (∑ g∈factors,
           capAt (RCN170.geometricPairCost A g) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (n-w)*(∑ i:Fin 3,capAt agreementCap i*
       capAt (RCN170.pairCost A G) i)+
       (e+1)*(a-w)*
         capAt (RCN170.pairCost A G) 2:=
     Nat.add_le_add (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt agreementCap i) (hbudget i))))
       (Nat.mul_le_mul_left ((e+1)*(a-w)) (hbudget 2))
   _=(n-w)*
       ((1+2*w*jY)*pairYCost ⟨A,G⟩+
         w*pairRCost ⟨A,G⟩+
         (2*w*jZ+1)*pairZCost ⟨A,G⟩)+
       (e+1)*(a-w)*pairZCost ⟨A,G⟩:=by
     simp [Fin.sum_univ_three,capAt,agreementCap,
       RCN170.pairCost]
end
end ProximityPrize.SubmissionLower.RCN172
