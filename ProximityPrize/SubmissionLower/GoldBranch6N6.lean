import ProximityPrize.SubmissionLower.GoldBranch6
import ProximityPrize.SubmissionLower.PortLow7
set_option autoImplicit true
section
namespace P3_6_6
noncomputable section
open Polynomial
open P3 (K)
open P3_6 (SmallFactor physicalDegree primaryBox primaryCutoff taylorLength TrueWeightLE)
open K1_13 (Geom Row Shape shape extend InBox OnFactor OrderAt chart mixed32)
open K1_13_6 (HighChart toGeneric markIdeal separant jetNumerator divisorIdeal cycleLength)
def membershipTest (g : Row 4) : Row 4 := jetNumerator g taylorLength
def nextTest (g : Row 4) : Row 4 := jetNumerator g (taylorLength + 1)
def MixedMark (f Q : Row 4) (l : ℕ) (S : Geom[X]) : Prop :=
  ∃ surface r, HighChart f Q l S surface r ∧
    let g := (separant^[r]) f
    toGeneric (membershipTest g) ∉ surface ∧ ∃ C,
      ∃ hc : (divisorIdeal surface (membershipTest g)).IsMinimalPrime C,
        C ≤ markIdeal S ∧
        (cycleLength (divisorIdeal surface (membershipTest g)) C hc.isPrime ≠ 1 ∨
          toGeneric (nextTest g) ∉ C)
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
private theorem eval_jetNumerator_zero (g : Row 4) (S : Geom[X])
    (hg : atJet g S = 0) (n : ℕ) (hS : S.natDegree < n) :
    atJet (jetNumerator g n) S = 0 := by
  rw [eval_jetNumerator _ _ hg, iterate_derivative_eq_zero hS, mul_zero]
theorem eval_membership_tests (g : Row 4) (S : Geom[X])
    (hg : atJet g S = 0) (hS : S.natDegree ≤ 133344) :
    atJet (membershipTest g) S = 0 ∧ atJet (nextTest g) S = 0 :=
  ⟨eval_jetNumerator_zero g S hg taylorLength (Nat.lt_succ_of_le hS),
    eval_jetNumerator_zero g S hg (taylorLength + 1)
      ((Nat.lt_succ_of_le hS).trans (Nat.lt_succ_self _))⟩
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
def member : GeoJets := toGeneric (membershipTest b.g)
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
open P3_6_6 (MixedMark eval_membership_tests)
open K1_13 (Geom Row Shape shape InBox atJet jet indexDegree)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (GeoJets GenericField GeoField genericCoeffs toGeneric separant)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint)
open scoped BigOperators
namespace Branch
variable {f Q : Row 4} {l : ℕ}
end Branch
private theorem iterate_bound (w : Fin 4 → ℕ) (f : Row 4) (r : ℕ) :
    MvPolynomial.weightedTotalDegree w ((separant^[r]) f) ≤
      MvPolynomial.weightedTotalDegree w f := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact (MvPolynomial.weightedTotalDegree_pderiv_le w 3 _).trans ih
open MvPolynomial in
theorem branch_box {f Q l} (b : Branch f Q l) : InBox (shape b.g) (shape f).chamber := by
  refine ⟨?_, ?_, ?_⟩
  · change b.g.totalDegree ≤ max f.totalDegree (indexDegree f)
    exact (by simpa only [Branch.g, weightedTotalDegree_one] using iterate_bound 1 f b.r :
      b.g.totalDegree ≤ f.totalDegree).trans (le_max_left _ _)
  · simpa only [Shape.chamber, shape, indexDegree_eq, Branch.g] using iterate_bound Fin.val f b.r
  · simpa only [Shape.chamber, shape, Branch.g, weightedTotalDegree_piSingle] using
      iterate_bound (Pi.single 3 1) f b.r
end
end P3_6_6_2
end
section
namespace P3_6_6_2
noncomputable section
open Polynomial MvPolynomial
open P3 (K)
open P3_6 (physicalDegree SmallFactor taylorLength)
open K1_13 (Row Shape Geom InBox embed extend shape chart atJet jet)
open K1_13_6 (GeoJets GeoField GenericField genericCoeffs evalGeneric toGeneric
  separant jetNumerator eval_jetNumerator)
open K1_13_6_2_1 (jet_fits oldBox_of_fits three_weights separant_pow_bound jet_bound)
open K1_13_7_1 (Chamber GeoFits shape_chamber weight_X_le weight_const_mul_le)
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
end
end P3_6_6_2
end
section
namespace P3_6_6_2_1
noncomputable section
open Polynomial MvPolynomial
open P3_6 (SmallFactor)
open P3_6_6_2 (Branch branch_box)
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
def graphLift {f Q l} (b : Branch f Q l) (P : Ideal GeoJets) : Ideal GeoJets5 :=
  (P.map b.localMap).comap b.onGraph
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
theorem graph_on_old {f Q l} (b : Branch f Q l) :
    b.onGraph.comp oldEmbedding = b.localMap := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [oldEmbedding, Branch.onGraph]
  · intro i
    simp [oldEmbedding, Branch.onGraph]
theorem graphLift_comap {f Q l} (b : Branch f Q l) (P : Ideal GeoJets)
    (hP : P.IsPrime) (hregular : b.sigma ∉ P) :
    (graphLift b P).comap oldEmbedding = P := by
  rw [graphLift, Ideal.comap_comap, graph_on_old]
  ext D
  change algebraMap GeoJets b.Local D ∈ P.map (algebraMap GeoJets b.Local) ↔ D ∈ P
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers b.sigma) b.Local]
  constructor
  · rintro ⟨m, ⟨n, rfl⟩, hm⟩
    exact (hP.mem_or_mem hm).resolve_left (fun hpow => hregular (hP.mem_of_pow_mem n hpow))
  · intro hD
    exact ⟨1, (Submonoid.powers b.sigma).one_mem, by simpa using hD⟩
theorem member_proper_on_graph {f Q l} (b : Branch f Q l) {E : GeoJets5}
    (hE : Associated (b.onGraph E) (b.localMap b.member)) :
    E ∉ graphLift b b.surface := by
  intro hmem
  have hlocal : b.localMap b.member ∈ b.surface.map b.localMap :=
    (b.surface.map b.localMap).mem_of_dvd hE.dvd hmem
  have hold : oldEmbedding b.member ∈ graphLift b b.surface := by
    change b.onGraph (oldEmbedding b.member) ∈ b.surface.map b.localMap
    rw [show b.onGraph (oldEmbedding b.member) = b.localMap b.member from
      RingHom.congr_fun (graph_on_old b) _]
    exact hlocal
  have hcont := graphLift_comap b b.surface b.base.isPrime b.chart.2.2
  exact b.proper (hcont ▸ hold)
end
end P3_6_6_2_3
end
section
namespace P3_6_6_2_3_2
noncomputable section
open P3_6_6 (membershipTest)
open P3_6_6_2 (Branch)
open P3_6_6_2_3 (graphLift graph_on_old graphLift_comap member_proper_on_graph)
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
def ShortSupport (A : CoeffIdeal) : Prop :=
  ∀ i : Fin K1_13.taylorLength, P3_6.taylorLength ≤ i.val → MvPolynomial.X i ∈ A
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
open P3_6_6_3 (ShortSupport)
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
open P3_6_6_3 (ShortSupport)
attribute [local instance] MvPolynomial.gradedAlgebra
end
end P3_6_6_3_2
end
