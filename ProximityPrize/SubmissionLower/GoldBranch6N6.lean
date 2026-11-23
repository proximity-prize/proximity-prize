import ProximityPrize.SubmissionLower.GoldBranch6
import ProximityPrize.SubmissionLower.PortLow7
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6_6
noncomputable section
open Polynomial
open P3 (K)
open P3_6 ( physicalDegree primaryBox  taylorLength TrueWeightLE)
open K1_13 (Geom Row Shape shape extend InBox OnFactor OrderAt chart mixed32)
open K1_13_6 (HighChart toGeneric markIdeal separant jetNumerator divisorIdeal cycleLength)
def membershipTest (g : Row 4) : Row 4 := jetNumerator g taylorLength
def nextTest (g : Row 4) : Row 4 := jetNumerator g (taylorLength + 1)
end
end P3_6_6
end
section
namespace P3_6_6
noncomputable section
open Polynomial
open P3 (K)
open P3_6 (physicalPrice primaryBox surfaceNumerator32 taylorLength)
open K1_13 (Row Shape Geom extend atJet shape ceilDiv)
open K1_13_6 (Pieces toGeneric
  separant jetNumerator HighMark divisorIdeal cycleLength eval_jetNumerator)
open K1_13_6_1 (mem_markIdeal mark_curve)
open scoped BigOperators
end
end P3_6_6
end
section
namespace P3_6_6_2
noncomputable section
open Polynomial
open P3 (K)
open P3_6 (physicalDegree primaryBox taylorLength)
open P3_6_6 (membershipTest nextTest)
open K1_13 (Row Shape Geom shape extend chart liftedChart mixed32)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength CanonicalChart
  Invariant separant divisorIdeal partialFlow)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint Box4 Box5 graphBox)
open scoped BigOperators
structure Branch (f Q : Row 4) (l : ℕ) where
  surface : Ideal GeoJets
  r : ℕ
  base : (intersectionIdeal f Q).IsMinimalPrime surface
  high : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface base.isPrime
  chart : CanonicalChart f surface r
  invariant : Invariant ((separant^[r]) f) surface
  proper : toGeneric (membershipTest ((separant^[r]) f)) ∉ surface
  curve : Ideal GeoJets
  divisor : (divisorIdeal surface (membershipTest ((separant^[r]) f))).IsMinimalPrime curve
  regularCurve : toGeneric (separant ((separant^[r]) f)) ∉ curve
  terminal :
    cycleLength (divisorIdeal surface (membershipTest ((separant^[r]) f))) curve
      divisor.isPrime ≠ 1 ∨ toGeneric (nextTest ((separant^[r]) f)) ∉ curve
namespace Branch
variable {f Q : Row 4} {l : ℕ} (b : Branch f Q l)
def g : Row 4 := (separant^[b.r]) f
def sigma : GeoJets := toGeneric (separant b.g)
def graph : GeoJets5 :=
  MvPolynomial.rename Fin.castSucc (toGeneric (partialFlow b.g)) +
    MvPolynomial.C (4 : GeoField) * MvPolynomial.rename Fin.castSucc b.sigma *
      MvPolynomial.X (Fin.last 4)
abbrev Local := Localization.Away b.sigma
def localMap : GeoJets →+* b.Local := algebraMap GeoJets b.Local
def onGraph : GeoJets5 →+* b.Local :=
  MvPolynomial.eval₂Hom (b.localMap.comp MvPolynomial.C)
    (Fin.lastCases
      (b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹) * toGeneric (partialFlow b.g)) *
        IsLocalization.Away.invSelf b.sigma)
      (fun i => b.localMap (MvPolynomial.X i)))
end Branch
end
end P3_6_6_2
end
section
namespace P3_6_6_2
noncomputable section
open Polynomial
open P3_6 (physicalDegree)
open K1_13 (Geom Row Shape shape InBox atJet jet indexDegree)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (GeoJets GenericField GeoField genericCoeffs toGeneric separant)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint)
open scoped BigOperators
namespace Branch
variable {f Q : Row 4} {l : ℕ}
end Branch
end
end P3_6_6_2
end
section
namespace P3_6_6_2
noncomputable section
open Polynomial MvPolynomial
open P3 (K)
open P3_6 (physicalDegree  taylorLength)
open K1_13 (Row Shape Geom InBox embed extend shape chart atJet jet)
open K1_13_6 (GeoJets GeoField GenericField genericCoeffs evalGeneric toGeneric
  separant jetNumerator eval_jetNumerator)
open K1_13_6_2_1 (jet_fits oldBox_of_fits three_weights separant_pow_bound jet_bound)
open K1_13_7_1 (Chamber GeoFits shape_chamber weight_X_le weight_const_mul_le)
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
private abbrev TaylorIndex := Fin taylorLength
private structure TaylorChart where
  denom : GeoJets
  numerator : TaylorIndex → GeoJets
end
end P3_6_6_2
end
section
namespace P3_6_6_2_1
noncomputable section
open Polynomial MvPolynomial
open P3_6_6_2 (Branch )
open K1_13 (Geom Row Shape InBox shape indexDegree liftedChart)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (GeoJets GeoField genericCoeffs toGeneric separant partialFlow jetNumerator)
open K1_13_6_2 (GeoJets5 Box5 graphBox)
open K1_13_6_2_2 (lift4 generic5 rawGraph numerator denominator padded)
open K1_13_6_2_2_2 (Chart incl S invS S_mul_invS negQuarter q constants W
  graphMap graphMap_lift graphMap_X_last)
open scoped BigOperators
open private compare_numerators from ProximityPrize.SubmissionLower.Fast072
open private support_bounds topWeight fifthWeight box_of_weights from ProximityPrize.SubmissionLower.Fast074
variable {f Q : Row 4} {l : ℕ}
@[simp] theorem onGraph_C (b : Branch f Q l) (a : GeoField) :
    b.onGraph (MvPolynomial.C a) = b.localMap (MvPolynomial.C a) := by
  simp [Branch.onGraph]
private def toBranch (b : Branch f Q l) : Chart b.g →+* b.Local :=
  IsLocalization.Away.lift (separant b.g)
    (g := b.localMap.comp (MvPolynomial.map genericCoeffs))
    (IsLocalization.Away.algebraMap_isUnit b.sigma)
@[simp] private theorem toBranch_incl (b : Branch f Q l) (P : Row 4) :
    toBranch b (incl b.g P) = b.localMap (toGeneric P) :=
  IsLocalization.Away.lift_eq _ _ _
local notation "wtDegree" => MvPolynomial.weightedTotalDegree
end
end P3_6_6_2_1
end
section
namespace P3_6_6_2_3
noncomputable section
open P3_6 (primaryBox taylorLength)
open P3_6_6_2 (Branch)
open K1_13 (Shape liftedChart)
open K1_13_6 (GeoJets)
open K1_13_6_2 (GeoJets5 graphBox)
open K1_13_6_2_4 (Boxes)
end
end P3_6_6_2_3
end
section
namespace P3_6_6_2_3
noncomputable section
open P3_6_6_2 (Branch)
open K1_13_6 (GeoJets)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (oldEmbedding)
end
end P3_6_6_2_3
end
section
namespace P3_6_6_2_3_2
noncomputable section
open P3_6_6 (membershipTest)
open P3_6_6_2 (Branch)
open K1_13_6 (GeoField GeoJets toGeneric partialFlow divisorIdeal cycleLength)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_3 (localWeight weight_cast weight_pos)
open K1_13_6_2_4 (OfDim LengthAt sectionIdeal oldEmbedding)
open private four_ne_zero from ProximityPrize.SubmissionLower.Fast054
open private length_le_of_surjection dim_after_proper_cut from ProximityPrize.SubmissionLower.Fast072
local notation "memberDiv" b => divisorIdeal (Branch.surface b) (membershipTest (Branch.g b))
end
end P3_6_6_2_3_2
end
section
set_option autoImplicit false
namespace P3_6_6_3
noncomputable section
open K1_13 (Row)
open K1_13_6 (toGeneric divisorIdeal cycleLength)
open K1_13_6_3 (CoeffIdeal JetIdeal)
open P3_6_6 (membershipTest nextTest)
end
end P3_6_6_3
end
section
set_option autoImplicit false
namespace P3_6_6_3
noncomputable section
open K1_13 K1_13_6
open K1_13_6_3 (JetIdeal)
open K1_13_6_3_1
attribute [local instance] MvPolynomial.algebraMvPolynomial
open private flat_sepToGeo map_eq_maximal_of_length_one step_in_sep sep_sq_dvd_jet
  nonvanishing_of_simple_cut stable_of_simple_cut from ProximityPrize.SubmissionLower.PortLow6
end
end P3_6_6_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1600
namespace P3_6_6_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_5 K1_13_6_3_5_3 MvPolynomial
open scoped Polynomial WithZero
attribute [local instance] MvPolynomial.gradedAlgebra
open private tupleHeight_le_of_inclusion finsum_weighted cone_eval_jets jet_zero_nonzero
  from ProximityPrize.SubmissionLower.Fast053
end
end P3_6_6_3_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace P3_6_6_3_2
noncomputable section
open MvPolynomial K1_13_6 K1_13_6_3 K1_13_6_3_5
attribute [local instance] MvPolynomial.gradedAlgebra
end
end P3_6_6_3_2
end
