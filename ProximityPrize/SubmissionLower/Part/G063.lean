import ProximityPrize.SubmissionLower.Part.G062


section Compact_SecondJetProperCounting
/-! The proper intersection bound stated directly for a regular irreducible
carrier, so it can count one global exceptional set or a proper helper branch. -/

namespace ProximityPrize.SubmissionLower.SecondJetProperCounting
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174
  RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001 RCN052
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K : Type} [Field K] {ι : Type*}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq ι := Classical.decEq ι

theorem regular_seed_bound_left
   (P:UnequalParameters) (F T:MvPolynomial (Fin 4) K)
   (hFirr:Irreducible F) (hFRpos:0 < F.degreeOf 2) (hrel:IsRelPrime F T)
   (p:ℕ) [CharP K p]
   (hFY:F.degreeOf 1 ≤ P.leftY)
   (hFR:F.degreeOf 2 ≤ P.leftR)
   (hFZ:F.degreeOf 3 ≤ P.leftZ)
   (hTY:T.degreeOf 1 ≤ P.rightY)
   (hTR:T.degreeOf 2 ≤ P.rightR)
   (hTZ:T.degreeOf 3 ≤ P.rightZ)
   (hleftR:1 ≤ P.leftR)
   (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
   (hleftZSmall:P.leftZ < p)
   (hmixedYSmall:P.mixedCost.y < p)
   (hmixedRSmall:P.mixedCost.r < p)
   (hmixedZSmall:P.mixedCost.z < p)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=P.n)
   (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a)
   (han:P.a ≤ P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u₀ i+gamma*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors)
   (hsolution:∀ gamma∈Gamma,specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,specialization K (selected gamma) gamma (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hTsolution:∀ gamma∈Gamma,specialization K (selected gamma) gamma T=0):
   Gamma.card*P.gap ≤
     (P.n-P.w)*dot P.leftAgreement (regularVector P F)+
       (P.errors+1)*P.gap*(regularVector P F).z:=by
 classical
 let phi:=polynomialEmbedding K
 let Delta:=Gamma
 let carrierCap:RCN051.DegreeVector:=
   ⟨P.leftY,P.leftR,P.leftZ⟩
 let cutCap:RCN051.DegreeVector:=
   ⟨P.rightY,P.rightR,P.rightZ⟩
 have hFne:F≠0:=hFirr.ne_zero
 have hDeltaSub:Delta ⊆ Gamma:=Finset.Subset.refl _
 have hDeltaData (gamma:K) (hgamma:gamma∈Delta):
     RegularSolution F (selected gamma) gamma∧
       specialization K (selected gamma) gamma T=0:=
   ⟨⟨hsolution gamma hgamma,hregular gamma hgamma⟩,hTsolution gamma hgamma⟩
 have hproper (g:GeometricFactor K F):¬g.1∣surfaceMap phi T:=by
   have hg := surfaceFactors_spec phi F g.1 g.2
   have hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by omega
   have hgeo:g.1∣geometricSurfaceMap K (GenericField K) F:=by
     simpa only [canonical_geometricSurfaceMap] using hg.2
   intro hgT
   apply hFirr.not_isUnit
   apply hrel (dvd_refl F)
   apply (geometric_factor_dvd_iff K (GenericField K) F T hFirr hpos g.1 hg.1 hgeo).mp
   simpa only [canonical_geometricSurfaceMap] using hgT
 have hcover:=card_le_sum_geometricSeeds K F hFne selected Delta
   (fun gamma hgamma => (hDeltaData gamma hgamma).1.1)
 letI:CharP (GenericField K) p:=genericField_charP K p
 have hsingle (g:GeometricFactor K F):
     (geometricSeeds K F selected Delta g).card*P.gap ≤
       (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.leftAgreement i*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) 2:=by
   have hgSpec:=surfaceFactors_spec phi F g.1 g.2
   have hsub:=geometricSeeds_subset K F selected Delta g
   have hgCaps:HasCaps g.1 carrierCap:=by
     intro i
     have hi:=geometricFactor_degree_le K F hFne g i
     fin_cases i
     · exact hi.trans hFY
     · exact hi.trans hFR
     · exact hi.trans hFZ
   have hTCaps:HasCaps (surfaceMap phi T) cutCap:=by
     intro i
     fin_cases i
     · exact (surfaceMap_degreeOf_le phi T 0).trans hTY
     · exact (surfaceMap_degreeOf_le phi T 1).trans hTR
     · exact (surfaceMap_degreeOf_le phi T 2).trans hTZ
   have hcarrierSmall:∀ i,capAt carrierCap i < p:=by
     intro i
     fin_cases i
     · exact hleftYSmall
     · exact hleftRSmall
     · exact hleftZSmall
   have hgates:=actual_characteristic_gates g.1 (surfaceMap phi T)
     carrierCap cutCap p hgCaps hTCaps hcarrierSmall
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitY,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedYSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitR,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedRSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitZ,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedZSmall)
   have hregular:∀ gamma∈geometricSeeds K F selected Delta g,
       MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
         (RCN231.polynomialPoint (phi.comp Polynomial.C)
           (selected gamma) gamma (phi Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4) F)≠0:=by
     intro gamma hgamma
     exact selectedPoint_regular_of_specialization K F selected gamma
       (hDeltaData gamma (hsub hgamma)).1.2
   have hTpoint:∀ gamma∈geometricSeeds K F selected Delta g,
       MvPolynomial.eval (selectedPoint phi selected gamma) (surfaceMap phi T)=0:=by
     intro gamma hgamma
     rw [selectedPoint_surface_evaluation,
       (hDeltaData gamma (hsub hgamma)).2,map_zero]
   have hcap (node:ι):∀ j,
       (agreementPolynomial phi F P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
         regularCapAt P.leftAgreement j:=by
     have h:=surface_agreement_caps phi F P.leftY P.leftR P.leftZ hleftR
       hFY hFR hFZ P.w (fun j => (j.factorial:K)⁻¹)
       (x node) (u₀ node) (u₁ node)
     intro j
     have hj:
         (agreementPolynomial phi F P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
           capAt (agreementCaps P.leftY P.leftR P.leftZ P.w) j:=by
       simpa [agreementPolynomial] using h j
     fin_cases j <;> exact hj
   have hcount:=proper_cut_seed_bound phi F g.1 (surfaceMap phi T)
     hgSpec.1 hgSpec.2 (hproper g)
     selected (geometricSeeds K F selected Delta g) nodes x u₀ u₁ hinj
     p P.w P.a P.errors hw hchar hwa (by simpa [hnodes] using han)
     hgates.1 hgates.2
     (fun gamma hgamma => hdegree gamma (hDeltaSub (hsub hgamma)))
     (fun gamma hgamma => (hDeltaData gamma (hsub hgamma)).1.1)
     hregular (fun gamma hgamma => (Finset.mem_filter.mp hgamma).2)
     hTpoint
     (fun gamma hgamma => hagreement gamma (hDeltaSub (hsub hgamma)))
     (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors
       (fun _ hgamma => hDeltaSub (hsub hgamma)) hnoPencil)
     (regularCapAt P.leftAgreement) (fun node _ => hcap node)
   simpa [hnodes,UnequalParameters.gap] using hcount
 have hbudget (i:Fin 3):=
   sum_coordinateMixedDegree_geometricFactors_le P F T hFne hTY hTR hTZ i
 have hfubini:
     (∑ g:GeometricFactor K F,∑ i:Fin 3,
         regularCapAt P.leftAgreement i*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)=
       ∑ i:Fin 3,regularCapAt P.leftAgreement i*
         (∑ g:GeometricFactor K F,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Delta.card*P.gap ≤
       (∑ g:GeometricFactor K F,
         (geometricSeeds K F selected Delta g).card)*P.gap:=
     Nat.mul_le_mul_right P.gap hcover
   _=∑ g:GeometricFactor K F,
       (geometricSeeds K F selected Delta g).card*P.gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:GeometricFactor K F,
       ((P.n-P.w)*(∑ i:Fin 3,regularCapAt P.leftAgreement i*
         coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=
     Finset.sum_le_sum (fun g _ => hsingle g)
   _=(P.n-P.w)*(∑ i:Fin 3,regularCapAt P.leftAgreement i*
         (∑ g:GeometricFactor K F,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i))+
       (P.errors+1)*P.gap*
         (∑ g:GeometricFactor K F,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.leftAgreement i*regularCapAt (regularVector P F) i)+
       (P.errors+1)*P.gap*regularCapAt (regularVector P F) 2:=
     Nat.add_le_add
       (Nat.mul_le_mul_left _ (Finset.sum_le_sum
         (fun i _ => Nat.mul_le_mul_left _ (hbudget i))))
       (Nat.mul_le_mul_left _ (hbudget 2))
   _=(P.n-P.w)*dot P.leftAgreement (regularVector P F)+
       (P.errors+1)*P.gap*(regularVector P F).z:=by
     simp [Fin.sum_univ_three,regularCapAt,dot]

end
end ProximityPrize.SubmissionLower.SecondJetProperCounting

end Compact_SecondJetProperCounting
