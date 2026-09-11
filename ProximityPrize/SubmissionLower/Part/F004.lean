import ProximityPrize.SubmissionLower.Part.F003


section Compact_AsymmetricHelper
/-!
The proper-cut argument uses agreement polynomials of the regular carrier F.
The auxiliary polynomial T supplies the intersection but does not supply an
agreement polynomial. Consequently, only the carrier's agreement degrees
enter the counting numerator; a maximum with the helper's degrees is unneeded.
The proof below specializes the inherited regular-pair proof at this sharper
agreement vector.
-/

namespace ProximityPrize.SubmissionLower.AsymmetricHelper
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174
  RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001 RCN052
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K : Type} [Field K] {ι : Type*}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq ι := Classical.decEq ι

theorem regularPairSeeds_bound_left
   (P:UnequalParameters) (Q T:MvPolynomial (Fin 4) K)
   (hrel:IsRelPrime Q T) (F:RegularIndex Q)
   (p:ℕ) [CharP K p]
   (hFY:F.1.degreeOf 1 ≤ P.leftY)
   (hFR:F.1.degreeOf 2 ≤ P.leftR)
   (hFZ:F.1.degreeOf 3 ≤ P.leftZ)
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
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
     (P.n-P.w)*dot P.leftAgreement (regularVector P F.1)+
       (P.errors+1)*P.gap*(regularVector P F.1).z:=by
 classical
 let phi:=polynomialEmbedding K
 let Delta:=regularPairSeeds Q T selected Gamma F
 let carrierCap:RCN051.DegreeVector:=
   ⟨P.leftY,P.leftR,P.leftZ⟩
 let cutCap:RCN051.DegreeVector:=
   ⟨P.rightY,P.rightR,P.rightZ⟩
 have hFspec:=positiveRFactors_spec Q F.1 F.2
 have hFne:F.1≠0:=hFspec.1.ne_zero
 have hDeltaSub:Delta ⊆ Gamma:=regularPairSeeds_subset Q T selected Gamma F
 have hDeltaData (gamma:K) (hgamma:gamma∈Delta):
     RegularSolution F.1 (selected gamma) gamma∧
       specialization K (selected gamma) gamma T=0:=
   regularPairSeeds_data Q T selected Gamma F gamma hgamma
 have hcover:=card_le_sum_geometricSeeds K F.1 hFne selected Delta
   (fun gamma hgamma => (hDeltaData gamma hgamma).1.1)
 letI:CharP (GenericField K) p:=genericField_charP K p
 have hsingle (g:GeometricFactor K F.1):
     (geometricSeeds K F.1 selected Delta g).card*P.gap ≤
       (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.leftAgreement i*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) 2:=by
   have hgSpec:=surfaceFactors_spec phi F.1 g.1 g.2
   have hsub:=geometricSeeds_subset K F.1 selected Delta g
   have hgCaps:HasCaps g.1 carrierCap:=by
     intro i
     have hi:=geometricFactor_degree_le K F.1 hFne g i
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
   have hregular:∀ gamma∈geometricSeeds K F.1 selected Delta g,
       MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
         (RCN231.polynomialPoint (phi.comp Polynomial.C)
           (selected gamma) gamma (phi Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4) F.1)≠0:=by
     intro gamma hgamma
     exact selectedPoint_regular_of_specialization K F.1 selected gamma
       (hDeltaData gamma (hsub hgamma)).1.2
   have hTpoint:∀ gamma∈geometricSeeds K F.1 selected Delta g,
       MvPolynomial.eval (selectedPoint phi selected gamma) (surfaceMap phi T)=0:=by
     intro gamma hgamma
     rw [selectedPoint_surface_evaluation,
       (hDeltaData gamma (hsub hgamma)).2,map_zero]
   have hcap (node:ι):∀ j,
       (agreementPolynomial phi F.1 P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
         regularCapAt P.leftAgreement j:=by
     have h:=surface_agreement_caps phi F.1 P.leftY P.leftR P.leftZ hleftR
       hFY hFR hFZ P.w (fun j => (j.factorial:K)⁻¹)
       (x node) (u₀ node) (u₁ node)
     intro j
     have hj:
         (agreementPolynomial phi F.1 P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
           capAt (agreementCaps P.leftY P.leftR P.leftZ P.w) j:=by
       simpa [agreementPolynomial] using h j
     fin_cases j <;> exact hj
   have hcount:=proper_cut_seed_bound phi F.1 g.1 (surfaceMap phi T)
     hgSpec.1 hgSpec.2 (geometricFactor_not_dvd_second Q T hrel F g.1 g.2)
     selected (geometricSeeds K F.1 selected Delta g) nodes x u₀ u₁ hinj
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
   sum_coordinateMixedDegree_geometricFactors_le P F.1 T hFne hTY hTR hTZ i
 have hfubini:
     (∑ g:GeometricFactor K F.1,∑ i:Fin 3,
         regularCapAt P.leftAgreement i*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)=
       ∑ i:Fin 3,regularCapAt P.leftAgreement i*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Delta.card*P.gap ≤
       (∑ g:GeometricFactor K F.1,
         (geometricSeeds K F.1 selected Delta g).card)*P.gap:=
     Nat.mul_le_mul_right P.gap hcover
   _=∑ g:GeometricFactor K F.1,
       (geometricSeeds K F.1 selected Delta g).card*P.gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:GeometricFactor K F.1,
       ((P.n-P.w)*(∑ i:Fin 3,regularCapAt P.leftAgreement i*
         coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=
     Finset.sum_le_sum (fun g _ => hsingle g)
   _=(P.n-P.w)*(∑ i:Fin 3,regularCapAt P.leftAgreement i*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i))+
       (P.errors+1)*P.gap*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.leftAgreement i*regularCapAt (regularVector P F.1) i)+
       (P.errors+1)*P.gap*regularCapAt (regularVector P F.1) 2:=
     Nat.add_le_add
       (Nat.mul_le_mul_left _ (Finset.sum_le_sum
         (fun i _ => Nat.mul_le_mul_left _ (hbudget i))))
       (Nat.mul_le_mul_left _ (hbudget 2))
   _=(P.n-P.w)*dot P.leftAgreement (regularVector P F.1)+
       (P.errors+1)*P.gap*(regularVector P F.1).z:=by
     simp [Fin.sum_univ_three,regularCapAt,dot]

end
end ProximityPrize.SubmissionLower.AsymmetricHelper

end Compact_AsymmetricHelper
