import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R
import ProximityPrize.SubmissionLower.V
import ProximityPrize.SubmissionLower.D4
namespace ProximityPrize.SubmissionLower.RCN266
open scoped BigOperators
open RCN223
open RCN286 RCN167
open RCN174 RCN136
open RCN095
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
abbrev RegularIndex (Q:MvPolynomial (Fin 4) K):=
 ↥(positiveRFactors Q)
def regularFlag (Q:MvPolynomial (Fin 4) K) (F:RegularIndex Q):
   FlagDegree:=
 ⟨F.1.degreeOf (3:Fin 4),F.1.degreeOf (1:Fin 4),
   F.1.degreeOf (2:Fin 4)⟩
theorem surfaceMap_in_regularFlag
   (phi:Polynomial K →+*Omega)
   (Q:MvPolynomial (Fin 4) K) (F:RegularIndex Q):
   PolynomialInFlag (regularFlag Q F) (surfaceMap phi F.1):=by
 intro d hd
 have h0:=MvPolynomial.monomial_le_degreeOf (0:Fin 3) hd
 have h1:=MvPolynomial.monomial_le_degreeOf (1:Fin 3) hd
 have h2:=MvPolynomial.monomial_le_degreeOf (2:Fin 3) hd
 have h0':d 0 ≤ F.1.degreeOf (1:Fin 4):=by
   simpa using h0.trans (surfaceMap_degreeOf_le phi F.1 0)
 have h1':d 1 ≤ F.1.degreeOf (2:Fin 4):=by
   simpa using h1.trans (surfaceMap_degreeOf_le phi F.1 1)
 have h2':d 2 ≤ F.1.degreeOf (3:Fin 4):=by
   simpa using h2.trans (surfaceMap_degreeOf_le phi F.1 2)
 change d 1 ≤ F.1.degreeOf (2:Fin 4)∧
   d 0+d 1 ≤ F.1.degreeOf (1:Fin 4)+F.1.degreeOf (2:Fin 4)∧
   d 0+d 1+d 2 ≤
     F.1.degreeOf (3:Fin 4)+F.1.degreeOf (1:Fin 4)+
       F.1.degreeOf (2:Fin 4)
 omega
theorem regularFlag_budgets
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap):
   (∑ F:RegularIndex Q,(regularFlag Q F).zOnly) ≤ 495∧
     (∑ F:RegularIndex Q,(regularFlag Q F).yz) ≤ 43∧
     (∑ F:RegularIndex Q,(regularFlag Q F).all) ≤ 8:=by
 classical
 have hb:=directFactor_input_budgets Q hQ
   weightedCap w seedTotalCap slopeCap (by norm_num [w]) hbox
 simp only [regularFlag,Finset.sum_coe_sort]
 refine ⟨?_,?_,?_⟩
 · simpa [seedTotalCap] using hb.2.2
 · have hy:(weightedCap-1)/w=43:=by
     norm_num [RCN223.weightedCap,
       RCN223.multiplicity,
       RCN223.agreements,
       RCN223.n,
       RCN223.errors,
       RCN223.w]
   simpa only [hy] using hb.1
 · simpa [slopeCap] using hb.2.1
end
end ProximityPrize.SubmissionLower.RCN266
