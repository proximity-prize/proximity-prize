import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Fat6966Factors
import ProximityPrize.SubmissionLower.R6960Front6960Rank4
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup58
import ProximityPrize.SubmissionLower.Low48BentCycleCap
import ProximityPrize.SubmissionLower.R6960HelperPrefix
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCyclePrice
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_MvPolynomial_Coeff
set_option Elab.async false









set_option Elab.async false

-- merged module Final50FatPad
section Merged_Final50FatPad

set_option Elab.async false
section
namespace Final50FatPad
noncomputable section
open Polynomial Finset
open P3 (K I node)
open Final50Price (Messages taylorLength)
open K1_14_6 (occupancy)
open P0_10 (incidence_arithmetic)
open K1_13_6 (CurveSections SurfaceSections Pieces)
open ProximityPrize.Benchmark
open scoped BigOperators
theorem section_capacity {w Γ s} (h : Messages w Γ s) (d : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) →
      (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ d) :
    46402 * Γ.card ≤ 82258*d + 46402 := by
  classical
  by_cases hm : Γ.card ≤ 1
  · omega
  let hits (γ : K) : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
  let common : Finset I := univ.filter fun i => ∀ γ ∈ Γ, (s γ).eval (node i) = w i
  let nodes : Finset I := univ \ common
  have common_le (γ : K) (hγ : γ ∈ Γ) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K) (hγ : γ ∈ Γ) : 179886 ≤ (hits γ).card := by
    obtain ⟨T, hT, ht⟩ := h.hits γ hγ
    exact hT.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, ht i hi⟩)
  have pair_count (a : K) (ha : a ∈ Γ) (b : K) (hb : b ∈ Γ) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ 133484 := by
    let P := s a - s b
    have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (h.distinct ha hb eq)
    refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
      P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (h.degree a ha) (h.degree b hb)))
    intro i hi
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < Γ.card)
  have hcommon : common.card ≤ 133484 :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := 179886 - common.card
  let t := 133484 - common.card
  have ht : t = x - 46402 := by dsimp [t, x]; omega
  have hx : 46402 ≤ x := by dsimp [x]; omega
  have hnodes : nodes.card = x + 82258 := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    dsimp [x]
    omega
  have exists_trim (γ : K) :
      ∃ T : Finset I, γ ∈ Γ → T ⊆ hits γ \ common ∧ T.card = x := by
    by_cases hγ : γ ∈ Γ
    · have hc := hit_count γ hγ
      have hd : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨T, hT, hcT⟩ := exists_subset_card_eq hd
      exact ⟨T, fun _ => ⟨hT, hcT⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose T hT using exists_trim
  have into_nodes (γ : K) (hγ : γ ∈ Γ) : T γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hT γ hγ).1 hi)).2⟩
  have overlap (a : K) (ha : a ∈ Γ) (b : K) (hb : b ∈ Γ) (hab : a ≠ b) :
      (T a ∩ T b).card ≤ t := by
    have cover : (T a ∩ T b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with ht' | hc
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hT a ha).1 (mem_inter.mp ht').1)).1,
          (mem_sdiff.mp ((hT b hb).1 (mem_inter.mp ht').2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hc, common_le b hb hc⟩
    have disj : Disjoint (T a ∩ T b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : I) (hi : i ∈ nodes) :
      (Γ.filter fun γ => i ∈ T γ).card ≤ d := by
    have proper : ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp (mem_sdiff.mp ((hT γ hγ).1 hi)).1).2⟩
  obtain ⟨sec, first⟩ := occupancy Γ nodes T x t d
    (fun γ hγ => ⟨into_nodes γ hγ, (hT γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at sec
  rw [hnodes] at first
  exact incidence_arithmetic 82258 _ _ 46402 _ (by omega) (by decide) hx (by decide) sec first
theorem curve_capacity {w Γ s d} (h : Messages w Γ s) (hc : CurveSections Γ s d) :
    46402 * Γ.card ≤ 82258*d + 46402 :=
  section_capacity h d (fun i => hc (node i) (w i))
theorem curve_capacity_integral {w Γ s d} (h : Messages w Γ s)
    (hc : CurveSections Γ s d) (hd : 0 < d) : Γ.card ≤ 2*d := by
  have := curve_capacity h hc
  omega
theorem pieces_curve_capacity {w Γ s} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : C.curves s) : 46402 * C.union.card ≤ 82258 * C.total + 46402 * C.n := by
  classical
  have hc' (i : Fin C.n) := Final50FatPad.curve_capacity (Final50Price.Messages.mono h (C.subset i)) (hc i)
  calc
    _ ≤ 46402 * ∑ i, (C.piece i).card :=
      Nat.mul_le_mul_left _ (by exact card_biUnion_le)
    _ = ∑ i, 46402 * (C.piece i).card := by rw [mul_sum]
    _ ≤ ∑ i : Fin C.n, (82258 * C.degree i + 46402) := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, sum_add_distrib, mul_sum, Nat.mul_comm]
theorem pieces_curve_capacity_integral {w Γ s} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : C.curves s) (hd : ∀ i, 0 < C.degree i) : C.union.card ≤ 2*C.total := by
  classical
  have hc' (i : Fin C.n) := Final50FatPad.curve_capacity_integral (Final50Price.Messages.mono h (C.subset i)) (hc i) (hd i)
  calc
    _ ≤ ∑ i, (C.piece i).card := card_biUnion_le
    _ ≤ ∑ i : Fin C.n, 2 * C.degree i := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, mul_sum]
theorem surface_capacity {w Γ s d} (h : Messages w Γ s)
    (hs : SurfaceSections Γ s d) (hd : 0 < d) : Γ.card ≤ 4*d := by
  classical
  have hsection (i : I) (hi : ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) :
      (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ 2*d := by
    obtain ⟨C, hC, hc, hpos, hdeg⟩ := hs (node i) (w i) hi
    have hH := Final50Price.Messages.mono h (filter_subset (fun γ => (s γ).eval (node i) = w i) Γ)
    exact (card_le_card hC).trans ((pieces_curve_capacity_integral C hH hc hpos).trans
      (Nat.mul_le_mul_left 2 hdeg))
  have := section_capacity h (2*d) hsection
  omega
theorem pieces_surface_capacity {w Γ s} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : C.surfaces s) (hd : ∀ i, 0 < C.degree i) : C.union.card ≤ 4*C.total := by
  classical
  have hc' (i : Fin C.n) := Final50FatPad.surface_capacity (Final50Price.Messages.mono h (C.subset i)) (hc i) (hd i)
  calc
    _ ≤ ∑ i, (C.piece i).card := card_biUnion_le
    _ ≤ ∑ i : Fin C.n, 4 * C.degree i := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, mul_sum]
end
end Final50FatPad
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1600
namespace Final50FatPad
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_5 K1_13_6_3_5_3 MvPolynomial
open scoped Polynomial WithZero
attribute [local instance] MvPolynomial.gradedAlgebra
open K1_13_6_3_5_3 (tupleHeight_le_of_inclusion finsum_weighted cone_eval_jets jet_zero_nonzero)

end
end Final50FatPad
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Final50FatPad
noncomputable section
open MvPolynomial K1_13_6 K1_13_6_3 K1_13_6_3_5
attribute [local instance] MvPolynomial.gradedAlgebra
end
end Final50FatPad
end


end Merged_Final50FatPad

-- merged module Final50GeometryCut
section Merged_Final50GeometryCut

set_option Elab.async false
set_option autoImplicit true
section
namespace Final50GeometryCut
noncomputable section
open Polynomial
open P3 (K)
open Final50Price (SmallFactor physicalDegree primaryBox primaryCutoff taylorLength TrueWeightLE)
open K1_13 (Geom Row Shape shape extend InBox OnFactor OrderAt chart mixed32)
open K1_13_6 (HighChart toGeneric markIdeal separant jetNumerator divisorIdeal cycleLength)
structure CutInput (Γ : Finset K) (s : K → (Polynomial K)) (f Q : Row 4) (l : ℕ) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  small : SmallFactor f
  onFactor : ∀ γ ∈ Γ, OnFactor f (extend (s γ))
  positive : 0 < l
  proper : ¬ f ∣ Q
  box : InBox (shape Q) primaryBox
  weight : TrueWeightLE Q primaryCutoff
  order : ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l
def membershipTest (g : Row 4) : Row 4 := jetNumerator g taylorLength
def nextTest (g : Row 4) : Row 4 := jetNumerator g (taylorLength + 1)
def auxCurves32 (x : Shape) : ℕ :=
  let p := x.chamber
  let h := chart taylorLength p
  mixed32 p primaryBox (primaryBox.plus (p.scale 4)) h + 2 * x.t * mixed32 p p p h
def auxPoints32 (x : Shape) : ℕ :=
  let p := x.chamber
  mixed32 p primaryBox (primaryBox.plus (p.scale 4)) p + 2 * x.t * mixed32 p p p p
def membershipDegree (x : Shape) : ℕ :=
  x.b * primaryBox.b * (chart (taylorLength + 1) x.chamber).b
end
end Final50GeometryCut
end
section
namespace Final50GeometryCut_1
noncomputable section
open Polynomial
open scoped Polynomial
open K1_13 (Row Geom Shape shape InBox extend atJet OnFactor)
open K1_13_6 (GeoJets CanonicalChart HighMark Invariant separant toGeneric
  markIdeal intersectionIdeal cycleLength)
open K1_13_6_1 (HasMark anchorBox tangentCut DerivativeWeight
  mem_markIdeal orderAt_vanishes tangentCut_vanishes)
open K1_13_6_1_3 (tangent_box anchor_fits derivative_fits)
open Final50Price (SmallFactor primaryBox)
open Final50GeometryCut (CutInput)
open P0_9_6_1 (SurfaceCut canonicalChart)
open P0_9_6_1 (lowHasse chart_cut derivative_proper box_charge box_cutter_charge)
open K1_13_7_1 (topAt topAt_coeff eval_topAt topView_separant)

end
end Final50GeometryCut_1
end
section
namespace Final50GeometryCut_1
noncomputable section
open K1_13 (Row Shape shape InBox chart mixed32)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength divisorIdeal separant)
open K1_13_6_1 (anchorBox DerivativeWeight CurveOnFactor sectionDegree)
open K1_13_6_1_4 (FullChamber pair_dimension curve_of_proper_cut surfaceDegree)
open K1_13_7_1 (toGeneric_fits proper_generic shape_chamber)
open Final50Price (SmallFactor primaryBox taylorLength)
open Final50GeometryCut (auxCurves32 auxPoints32)
open P0_9_6_1 (SurfaceCut)
open scoped BigOperators
open P0_9_6_1_1 (proper_divisor additive_sections weighted_pair full_chart full_plus chamber_scale full_scale supported_charge sum_biUnion_bound toGeneric_ne_zero)
end
end Final50GeometryCut_1
end
section
namespace Final50GeometryCut_1
noncomputable section
open Polynomial
open P3 (K)
open Final50Price (SmallFactor physicalDegree taylorLength)
open K1_13 (InBox chart extend shape atJet)
open K1_13_6 (CanonicalChart CurveSections evalGeneric markIdeal separant)
open K1_13_6_1 (CurveOnFactor anchorBox sectionDegree mem_markIdeal)
open K1_13_6_1_5 (coordinate_cut)
open K1_13_7 (RegularAt)
open K1_13_7_1 (Chamber GeoFits derivative_in_box shape_chamber toGeneric_fits)
open P0_9_6_1_2 (exists_value_cut)
open P0_9_6_1_2 (count_points count_marks chart_has_simplex)
end
end Final50GeometryCut_1
end
namespace Final50GeometryCut
export Final50FatPad (section_capacity curve_capacity curve_capacity_integral pieces_curve_capacity
  pieces_curve_capacity_integral surface_capacity pieces_surface_capacity)
end Final50GeometryCut

section
namespace Final50GeometryCut
noncomputable section
open Polynomial
open P3 (K)
open Final50Price (Messages SmallFactor ProperCut physicalPrice physicalPriceOld physicalPriceTilted
  tiltedSurface primaryBox surfaceNumerator32 taylorLength)
open K1_13 (Row Shape Geom extend atJet shape ceilDiv)
open K1_13_6 (Pieces toGeneric
  separant jetNumerator HighMark divisorIdeal cycleLength eval_jetNumerator)
open K1_13_6_1 (mem_markIdeal mark_curve)
open scoped BigOperators
def c1 : Prop :=
  ∀ Γ s f Q l, CutInput Γ s f Q l →
    ∃ (C : Pieces Γ) (B : Finset K),
      C.curves s ∧
      (∀ γ ∈ Γ, ¬ HighMark f Q l (extend (s γ)) → γ ∈ C.union ∪ B) ∧
      32 * C.total ≤ auxCurves32 (shape f) ∧
      32 * (B.card + C.n) ≤ 2 * auxPoints32 (shape f)





private theorem eval_jetNumerator_zero (g : Row 4) (S : (Polynomial Geom))
    (hg : atJet g S = 0) (n : ℕ) (hS : S.natDegree < n) :
    atJet (jetNumerator g n) S = 0 := by
  rw [eval_jetNumerator _ _ hg, iterate_derivative_eq_zero hS, mul_zero]
theorem eval_membership_tests (g : Row 4) (S : (Polynomial Geom))
    (hg : atJet g S = 0) (hS : S.natDegree ≤ 133484) :
    atJet (membershipTest g) S = 0 ∧ atJet (nextTest g) S = 0 :=
  ⟨eval_jetNumerator_zero g S hg taylorLength (Nat.lt_succ_of_le hS),
    eval_jetNumerator_zero g S hg (taylorLength + 1)
      ((Nat.lt_succ_of_le hS).trans (Nat.lt_succ_self _))⟩
def chargedPrice (x : Shape) (l scale budget : ℕ) : ℕ :=
  ceilDiv (ceilDiv budget scale +
    ceilDiv ((82258 + 2 * 46402) * membershipDegree x) 46402) l +
  2 * (133484 * x.b * primaryBox.b) +
  ceilDiv (82258 * auxCurves32 x + 2 * 46402 * auxPoints32 x) (32 * 46402)







end
end Final50GeometryCut
end
section
namespace Final50GeometryCut_1
noncomputable section
open P3 (K)
open Final50Price (taylorLength)
open Final50GeometryCut (auxCurves32 auxPoints32)
open K1_13 (Row shape extend chart atJet)
open K1_13_6 (Pieces GeoJets CurveSections HighMark intersectionIdeal markIdeal)
open K1_13_6_1 (HasMark anchorBox sectionDegree mark_surface mark_curve)
open P0_9_6_1 (SurfaceCut canonicalChart)
open scoped BigOperators
end
end Final50GeometryCut_1
end
section
namespace Final50GeometryCut_2
noncomputable section
open Polynomial
open P3 (K)
open Final50Price (physicalDegree primaryBox taylorLength)
open Final50GeometryCut (membershipTest nextTest)
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
def next : GeoJets := toGeneric (nextTest b.g)
def Simple : Prop := cycleLength (divisorIdeal b.surface (membershipTest b.g))
  b.curve b.divisor.isPrime = 1
def Contains (p : JetPoint) : Prop :=
  b.curve ≤ RingHom.ker (MvPolynomial.eval p) ∧ MvPolynomial.eval p b.sigma ≠ 0
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
def Slice4 {f Q l} (b : Branch f Q l) (T : Finset JetPoint) : Prop :=
  T.card ≤ 1 ∨ ∃ D, Box4 (chart (taylorLength + 2) (shape f).chamber) D ∧
    D ∉ b.curve ∧ ∀ p ∈ T, MvPolynomial.eval p D = 0
def Chart4 {f Q l} (b : Branch f Q l) : Prop :=
  let p := (shape f).chamber
  Box4 (chart (taylorLength + 1) p) b.member ∧
    Box4 (chart (taylorLength + 2) p) b.next ∧
    ∀ x a : K, ∃ D, Box4 (chart (taylorLength + 2) p) D ∧
      ∀ S : (Polynomial K), S.natDegree ≤ physicalDegree → b.Contains (actualPoint (extend S)) →
        (MvPolynomial.eval (actualPoint (extend S)) D = 0 ↔ S.eval x = a)
end
end Final50GeometryCut_2
end
section
namespace Final50GeometryCut_2
noncomputable section
open Polynomial
open Final50Price (physicalDegree)
open Final50GeometryCut ( eval_membership_tests)
open K1_13 (Geom Row Shape shape InBox atJet jet indexDegree)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (GeoJets GenericField GeoField genericCoeffs toGeneric separant)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint)
open scoped BigOperators
theorem eval_actualPoint (S : (Polynomial Geom)) (P : Row 4) :
    MvPolynomial.eval (actualPoint S) (toGeneric P) = genericCoeffs (atJet P S) := by
  rw [toGeneric, MvPolynomial.eval_map]
  change MvPolynomial.eval₂ genericCoeffs (⇑genericCoeffs ∘ jet S) P = _
  rw [← MvPolynomial.eval₂_comp]
  rfl
namespace Branch
variable {f Q : Row 4} {l : ℕ}
theorem next_proper (b : Branch f Q l) (h : b.Simple) : b.next ∉ b.curve :=
  b.terminal.resolve_left (fun hne => hne h)
theorem g_actual (b : Branch f Q l) {S : (Polynomial Geom)}
    (h : b.Contains (actualPoint S)) : atJet b.g S = 0 :=
  K1_13_6_1.mem_markIdeal.mp
    (h.1 ((le_trans le_sup_left b.divisor.le) (b.chart.2.1 b.r le_rfl)))
theorem regular_actual (b : Branch f Q l) {S : (Polynomial Geom)}
    (h : b.Contains (actualPoint S)) : atJet (separant b.g) S ≠ 0 := by
  intro hz
  exact h.2 (by rw [Branch.sigma, eval_actualPoint, hz, map_zero])
theorem next_actual (b : Branch f Q l) {S : (Polynomial Geom)} (h : b.Contains (actualPoint S))
    (hd : S.natDegree ≤ physicalDegree) : MvPolynomial.eval (actualPoint S) b.next = 0 := by
  rw [next, eval_actualPoint, (eval_membership_tests _ _ (b.g_actual h) hd).2, map_zero]
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
end Final50GeometryCut_2
end
section
namespace Final50GeometryCut_2
noncomputable section
open Polynomial MvPolynomial
open P3 (K)
open Final50Price (physicalDegree SmallFactor taylorLength)
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
private def TaylorChart.Fits (C : TaylorChart) (h : Shape) : Prop :=
  GeoFits C.denom h ∧ ∀ i, GeoFits (C.numerator i) h
private def TaylorChart.Recovers (C : TaylorChart) (S : (Polynomial Geom)) : Prop :=
  evalGeneric S C.denom ≠ 0 ∧
    ∀ i, evalGeneric S (C.numerator i) =
      evalGeneric S C.denom * genericCoeffs (hasseDeriv i.val S)
private abbrev AffineForm := GeoField × (TaylorIndex → GeoField)
private def TaylorChart.pullback (C : TaylorChart) (a : AffineForm) : GeoJets :=
  MvPolynomial.C a.1 * C.denom + ∑ i, MvPolynomial.C (a.2 i) * C.numerator i
private theorem TaylorChart.pullback_fits (C : TaylorChart) {h : Shape} (hC : C.Fits h) (a : AffineForm) :
    GeoFits (C.pullback a) h := by
  classical
  have hw (w : Fin 4 → ℕ) (d : ℕ) (hD : C.denom.weightedTotalDegree w ≤ d)
      (hN : ∀ i, (C.numerator i).weightedTotalDegree w ≤ d) :
      (C.pullback a).weightedTotalDegree w ≤ d := by
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.add_mem
    · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans hD)
    · apply Submodule.sum_mem
      intro i _
      exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans (hN i))
  refine ⟨?_, hw Fin.val h.j hC.1.2.1 (fun i => (hC.2 i).2.1), ?_⟩
  · simpa only [weightedTotalDegree_one] using hw 1 h.b
      (by simpa only [weightedTotalDegree_one] using hC.1.1)
      (fun i => by simpa only [weightedTotalDegree_one] using (hC.2 i).1)
  · simpa only [weightedTotalDegree_piSingle] using hw (Pi.single (3 : Fin 4) 1) h.t
      (by simpa only [weightedTotalDegree_piSingle] using hC.1.2.2)
      (fun i => by simpa only [weightedTotalDegree_piSingle] using (hC.2 i).2.2)
private def denominator (L : ℕ) (g : Row 4) : Row 4 :=
  separant g ^ (2 * L)
private def numerator (L : ℕ) (g : Row 4) (i : TaylorIndex) : Row 4 :=
  if hi : i.val < 4 then MvPolynomial.X ⟨i.val, hi⟩ * denominator L g
  else
    MvPolynomial.C (Polynomial.C (↑i.val.factorial : Geom)⁻¹) *
      (separant g ^ (2 * (L - i.val)) * jetNumerator g i.val)
private def taylorChart (L : ℕ) (g : Row 4) : TaylorChart where
  denom := toGeneric (denominator L g)
  numerator i := toGeneric (numerator L g i)
private theorem numerator_bound {L : ℕ} (hL : taylorLength ≤ L) (w : Fin 4 → ℕ) (Δ d₀ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) (hw : ∀ i, w i ≤ d₀)
    {g : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (i : TaylorIndex) :
    W w (numerator L g i) ≤ d₀ + 2 * L * (B - w 3) + L * Δ := by
  have hi : i.val ≤ L := i.isLt.le.trans hL
  unfold numerator
  split_ifs
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((weight_X_le w _).trans (hw _)) (separant_pow_bound w hg _)).trans
        (Nat.le_add_right _ _))
  · apply (weight_const_mul_le _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ 2 * (L - i.val) * (B - w 3) + (w 0 + i.val * (2 * (B - w 3) + Δ)) :=
        Nat.add_le_add (separant_pow_bound w hg _) (jet_bound w Δ hshift hB hg i.val)
      _ = w 0 + 2 * (i.val + (L - i.val)) * (B - w 3) + i.val * Δ := by ring
      _ ≤ _ := by
        rw [Nat.add_sub_of_le hi]
        exact Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hi)
private theorem chart_fits {L : ℕ} (hL : taylorLength ≤ L) {g : Row 4} {p : Shape}
    (hg : InBox (shape g) p) (hp : Chamber p) (ht : 0 < p.t) :
    (taylorChart L g).Fits (chart L p) := by
  constructor
  · apply three_weights hg hp ht
    intro w Δ d₀ B _ _ _ hB
    exact (separant_pow_bound w hB (2 * L)).trans (by omega)
  · intro i
    exact three_weights hg hp ht (fun w Δ d₀ _ hs hw hwB hB =>
      numerator_bound hL w Δ d₀ hs hw hwB hB i)
private theorem ordinary_eq_hasse (S : (Polynomial Geom)) (n : ℕ) :
    derivative^[n] S = Polynomial.C (n.factorial : Geom) * hasseDeriv n S := by
  ext m
  rw [coeff_iterate_derivative, Polynomial.coeff_C_mul, hasseDeriv_coeff,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
private theorem eval_generic (S : (Polynomial Geom)) (P : Row 4) :
    evalGeneric S (toGeneric P) = genericCoeffs (atJet P S) :=
  (MvPolynomial.map_eval genericCoeffs (jet S) P).symm
private theorem generic_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericField)
private theorem chart_recovers {L : ℕ} (hL : taylorLength ≤ L) {g : Row 4} {S : (Polynomial Geom)}
    (hg : atJet g S = 0) (hr : atJet (separant g) S ≠ 0) : (taylorChart L g).Recovers S := by
  have hden : atJet (denominator L g) S = atJet (separant g) S ^ (2 * L) :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))) _ _
  constructor
  · change evalGeneric S (toGeneric (denominator L g)) ≠ 0
    rw [eval_generic]
    apply (map_ne_zero_iff _ generic_injective).mpr
    rw [hden]
    exact pow_ne_zero _ hr
  · intro i
    change evalGeneric S (toGeneric (numerator L g i)) =
      evalGeneric S (toGeneric (denominator L g)) * genericCoeffs (hasseDeriv i.val S)
    rw [eval_generic, eval_generic, ← map_mul]
    apply congrArg genericCoeffs
    unfold numerator
    split_ifs with hinit
    · unfold atJet
      rw [map_mul, MvPolynomial.eval_X, mul_comm]
      rfl
    · let E := MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant g) S ^ (2 * (L - i.val)) *
        atJet (jetNumerator g i.val) S) = _
      rw [eval_jetNumerator _ _ hg, ordinary_eq_hasse]
      have hinv : Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ (K1_13_7_1.factorial_cast_ne_zero
          (i.isLt.trans (by decide : taylorLength < K1.p))), map_one]
      have hpow : 2 * (L - i.val) + 2 * i.val = 2 * L := by
        have hi : i.val ≤ L := i.isLt.le.trans hL
        rw [← Nat.mul_add, Nat.sub_add_cancel hi]
      calc
        _ = (Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom)) *
            ((atJet (separant g) S ^ (2 * (L - i.val)) * atJet (separant g) S ^ (2 * i.val)) *
              hasseDeriv i.val S) := by ring
        _ = _ := by rw [hinv, one_mul, ← pow_add, hpow, hden]
private def constants : Geom →+* GeoField :=
  genericCoeffs.comp Polynomial.C
private def center : GeoField :=
  genericCoeffs Polynomial.X
private theorem eval_center (S : (Polynomial Geom)) : (S.map constants).eval center = genericCoeffs S := by
  rw [Polynomial.eval_map]
  change eval₂RingHom constants center S = genericCoeffs S
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [constants]
  · simp [center]
private theorem taylor_sum {S : (Polynomial Geom)} (hS : S.natDegree < taylorLength) (x : Geom) :
    (∑ i : TaylorIndex, (constants x - center) ^ i.val * genericCoeffs (hasseDeriv i.val S)) =
      constants (S.eval x) := by
  let T := (S.map constants).taylor center
  have hT : T.natDegree < taylorLength := by
    change ((S.map constants).taylor center).natDegree < taylorLength
    rw [natDegree_taylor]
    exact Polynomial.natDegree_map_le.trans_lt hS
  have hev : T.eval (constants x - center) = constants (S.eval x) := by
    simp [T, taylor_eval]
  rw [← hev, Polynomial.eval_eq_sum_range' hT, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  change _ = ((S.map constants).taylor center).coeff i.val * _
  rw [taylor_coeff, hasseDeriv_map, eval_center, mul_comm]
private def valueForm (x a : Geom) : AffineForm :=
  (-(constants a), fun i => (constants x - center) ^ i.val)
private theorem eval_value {C : TaylorChart} {S : (Polynomial Geom)}
    (h : C.Recovers S) (hd : S.natDegree < taylorLength) (x a : Geom) :
    evalGeneric S (C.pullback (valueForm x a)) = 0 ↔ S.eval x = a := by
  have evC (c : GeoField) : evalGeneric S (MvPolynomial.C c) = c := MvPolynomial.eval_C _
  have hsum :
      (∑ i : TaylorIndex, (constants x - center) ^ i.val *
        (evalGeneric S C.denom * genericCoeffs (hasseDeriv i.val S))) =
      evalGeneric S C.denom * constants (S.eval x) := by
    rw [← taylor_sum hd x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  have heval : evalGeneric S (C.pullback (valueForm x a)) =
      evalGeneric S C.denom * (constants (S.eval x) - constants a) := by
    simp only [TaylorChart.pullback, valueForm, map_add, map_sum, map_mul, evC, h.2, hsum]
    ring
  have hconst : Function.Injective constants := generic_injective.comp Polynomial.C_injective
  rw [heval, mul_eq_zero, or_iff_right h.1, sub_eq_zero, hconst.eq_iff]
theorem chart4 {f Q l} (hf : SmallFactor f) (b : Branch f Q l) : Chart4 b := by
  have hg := branch_box b
  have hp := shape_chamber f
  have ht : 0 < (shape f).chamber.t := hf.2.1
  refine ⟨oldBox_of_fits (jet_fits hg hp ht (Nat.le_succ _)),
    oldBox_of_fits (jet_fits hg hp ht (Nat.le_succ _)), ?_⟩
  intro x a
  let L := taylorLength + 2
  let C := taylorChart L b.g
  have hL : taylorLength ≤ L := Nat.le_add_right _ _
  have hfit : C.Fits (chart L (shape f).chamber) := chart_fits hL hg hp ht
  refine ⟨C.pullback (valueForm (embed x) (embed a)),
    oldBox_of_fits (C.pullback_fits hfit _), ?_⟩
  intro S hd hpoint
  have hdegree : (extend S).natDegree < taylorLength :=
    Nat.lt_succ_of_le (Polynomial.natDegree_map_le.trans hd)
  change evalGeneric (extend S) (C.pullback (valueForm (embed x) (embed a))) = 0 ↔ _
  rw [eval_value (chart_recovers hL (b.g_actual hpoint) (b.regular_actual hpoint)) hdegree,
    Polynomial.eval_map_apply, embed.injective.eq_iff]
end
end Final50GeometryCut_2
end
section
namespace Final50GeometryCut_2
noncomputable section
open Polynomial
open P3 (K)
open Final50Price (SmallFactor primaryBox taylorLength)
open K1_13 (Row Shape shape extend embed InBox chart liftedChart)
open K1_13_6 (Pieces CurveSections)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective Demand maximal_demand Box4 Box5 graphBox)
open scoped BigOperators
end
end Final50GeometryCut_2
end
section
namespace Final50GeometryCut_2_1
noncomputable section
open Polynomial MvPolynomial
open Final50Price (SmallFactor)
open Final50GeometryCut_2 (Branch branch_box)
open K1_13 (Geom Row Shape InBox shape indexDegree liftedChart)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (GeoJets GeoField genericCoeffs toGeneric separant partialFlow jetNumerator)
open K1_13_6_2 (GeoJets5 Box5 graphBox)
open K1_13_6_2_2 (lift4 generic5 rawGraph numerator denominator padded)
open K1_13_6_2_2_2 (Chart incl S invS S_mul_invS negQuarter q constants W
  graphMap graphMap_lift graphMap_X_last)
open scoped BigOperators
open K1_13_6_2_2_2 (compare_numerators)
open K1_13_6_2_2_1 (support_bounds topWeight fifthWeight box_of_weights)
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
end Final50GeometryCut_2_1
end
section
namespace Final50GeometryCut_2_1
noncomputable section
open Polynomial
open P3 (K)
open Final50Price (taylorLength)
open Final50GeometryCut_2 (Branch)
open K1_13 (Geom Row embed extend atJet jet)
open K1_13_6 (GeoField genericCoeffs toGeneric separant jetNumerator eval_jetNumerator)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint)
open K1_13_6_2_2 (lift4 generic5 numerator denominator padded padded_last)
open scoped BigOperators
open K1_13_6_2_2 (ordinary ordinary_eq_hasse const centre taylorScalar factorial_ne_zero box_C_mul box_sum box_sub)
variable {f Q : Row 4} {l : ℕ}
end
end Final50GeometryCut_2_1
end
section
namespace Final50GeometryCut_2_2
noncomputable section
open Final50Price (SmallFactor primaryBox taylorLength)
open Final50GeometryCut (membershipTest)
open Final50GeometryCut_2 (Branch Slice4 )
open K1_13 (Row Shape shape chart mixed32 volume32 difference)
open K1_13_6 (GeoJets GeoField toGeneric divisorIdeal cycleLength intersectionIdeal separant)
open K1_13_6_2 (JetPoint Box4)
open K1_13_6_2_3 (ChamberBox dimension capCoeff polarize mixedDegree localWeight pointIdeal
  chart_box generic_box regular_cut cut_dimension dimension_bot pair_regular intersection_eq
  surface_dimension weight_cast weight_pos point_injective point_prime point_degree point_proper_section)
open scoped BigOperators
end
end Final50GeometryCut_2_2
end
section
namespace Final50GeometryCut_2_3
noncomputable section
open Final50Price (primaryBox taylorLength)
open Final50GeometryCut_2 (Branch)
open K1_13 (Shape liftedChart)
open K1_13_6 (GeoJets)
open K1_13_6_2 (GeoJets5 graphBox)
open K1_13_6_2_4 (Boxes)
end
end Final50GeometryCut_2_3
end
section
namespace Final50GeometryCut_2_3
noncomputable section
open Final50Price (primaryBox taylorLength)
open K1_13 (Shape liftedChart mixed32)
open K1_13_6 (GeoField)
open K1_13_6_2 (graphBox)
open K1_13_6_2_4 (Boxes Chamber Allowed Admissible allowed_coordinate
  mixedDegree diagonalExponents)
open K1_13_6_2_4_3 (volumeProduct sumCap diagonal)
open MvPolynomial
open scoped BigOperators
open K1_13_6_2_4 (chart_chamber)
open K1_13_6_2_4_3 (diagonal_coeff)
open K1_13_6_2_4_3 (alt alt_insert alt_empty capDiff five_differences signed4_le)
end
end Final50GeometryCut_2_3
end
section
namespace Final50GeometryCut_2_3
noncomputable section
open Final50GeometryCut_2 (Branch)
open K1_13_6 (GeoJets)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (oldEmbedding)
end
end Final50GeometryCut_2_3
end
section
namespace Final50GeometryCut_2_3
noncomputable section
open Final50Price (SmallFactor primaryBox)
open Final50GeometryCut_2 (Branch  )
open P0_9_6_2_3 (cylinder_comparison cycle_comparison divisor_comparison proper_cut_comparison)
open K1_13 (Row Shape shape InBox)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5 Box5)
open K1_13_6_2_4 (Admissible Chamber Component DimLE DivisorBound OfDim LengthAt
  ambient_dim cylinder cylinder_injective dim_le_after_section mixedDegree oldEmbedding
  old_section_box point_bound pointIdeal sectionIdeal)
open scoped BigOperators
end
end Final50GeometryCut_2_3
end
section
namespace Final50GeometryCut_2_3_1
noncomputable section
open Final50GeometryCut_2 (Branch)
open K1_13_6 (GeoField GeoJets partialFlow toGeneric)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (OfDim cylinder oldEmbedding one_le_length sectionIdeal)
open K1_13_6_2_4_5 (four_ne_zero substituteLast substituteLast_old)
open K1_13_6_2_4_5 (dim_after_proper_cut)
end
end Final50GeometryCut_2_3_1
end
section
namespace Final50GeometryCut_2_3_2
noncomputable section
open Final50GeometryCut (membershipTest)
open Final50GeometryCut_2 (Branch)
open K1_13_6 (GeoField GeoJets toGeneric partialFlow divisorIdeal cycleLength)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_3 (localWeight weight_cast weight_pos)
open K1_13_6_2_4 (OfDim LengthAt sectionIdeal oldEmbedding)
open K1_13_6_2_4_5 (four_ne_zero)
open K1_13_6_2_4_5 (length_le_of_surjection dim_after_proper_cut)
local notation "memberDiv" b => divisorIdeal (Branch.surface b) (membershipTest (Branch.g b))
end
end Final50GeometryCut_2_3_2
end
section
set_option autoImplicit false
namespace Final50GeometryCut_3
noncomputable section
open K1_13 (Row)
open K1_13_6 (toGeneric divisorIdeal cycleLength)
open K1_13_6_3 (CoeffIdeal JetIdeal)
open Final50GeometryCut (membershipTest nextTest)
end
end Final50GeometryCut_3
end
section
set_option autoImplicit false
namespace Final50GeometryCut_3
noncomputable section
open K1_13 K1_13_6 MvPolynomial
open P0_9_6_3 (iterate_separant_degree jetNumerator_degree)
end
end Final50GeometryCut_3
end
section
set_option autoImplicit false
namespace Final50GeometryCut_3
noncomputable section
open K1_13 K1_13_6
open K1_13_6_3 (JetIdeal)
open K1_13_6_3_1
attribute [local instance] MvPolynomial.algebraMvPolynomial
open P0_9_6_3 (flat_sepToGeo map_eq_maximal_of_length_one step_in_sep sep_sq_dvd_jet nonvanishing_of_simple_cut stable_of_simple_cut)
end
end Final50GeometryCut_3
end
section
set_option autoImplicit false
namespace Final50GeometryCut_3
noncomputable section
open K1_13 K1_13_6
open K1_13_6_3 (JetIdeal dimension cycleWeight)
open K1_13_6_3_6 MvPolynomial
open P0_9_6_3 (CutCycle)
open scoped BigOperators
open P0_9_6_2_3 (geometric_regular)
open P0_9_6_3 (coefficient_budget)
end
end Final50GeometryCut_3
end
section
set_option autoImplicit false
namespace Final50GeometryCut_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial
open scoped Polynomial
open P0_9_6_3 (fresh_prime fresh_birational dim_fresh_of_recovery dim_lt_of_prime_lt)
end
end Final50GeometryCut_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Final50GeometryCut_3
noncomputable section
open K1 K1_13 K1_13_6 Polynomial MvPolynomial
open K1_13_6_3
open Final50Price (primaryBox)
open P0_9_6_3 (freshImage_injective)
open P0_9_6_3 (curve_degree markPoint_inj canonical_unique cycleWeight_ge surface_sum)
open scoped BigOperators
end
end Final50GeometryCut_3
end
section
set_option autoImplicit false
set_option maxRecDepth 200000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Final50GeometryCut_3_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_2 Polynomial
open P0_9_6_3_1 (iterate_zero_of_le differentialTaylor_degree rowAt_eval initial_dividedIterate chartTaylor_toComponent)
end
end Final50GeometryCut_3_1
end
namespace Final50GeometryCut_3_2
end Final50GeometryCut_3_2

namespace Final50GeometryCut





end Final50GeometryCut


end Merged_Final50GeometryCut

-- merged module Final50ActiveCycleBound
section Merged_Final50ActiveCycleBound

set_option autoImplicit false
set_option Elab.async false

namespace Final50ActiveCycle

noncomputable section

open Low48BentCycle (Family mixedDegree properCut cycleComparison divisorBound diagonalExponents)

open Final50Price (SmallFactor)
open Final50GeometryCut_2 (Branch)
open P0_9_6_2_3 (cylinder_comparison)
open K1_13 (Row)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5)
open K1_13_6_2_4 (Exponent Component DimLE OfDim LengthAt ambient_dim cylinder cylinder_injective
  dim_le_after_section oldEmbedding pointIdeal sectionIdeal)
open K1_13_6_2_4_1 (positiveDiagonal)
open MvPolynomial
open scoped BigOperators Pointwise

open K1_13_6_2_4 (eval_surjective pointIdeal_injective point_component exists_coordinate_cut)











end

end Final50ActiveCycle

end Merged_Final50ActiveCycleBound

-- merged module Final50ActiveCycleCaps
section Merged_Final50ActiveCycleCaps

set_option autoImplicit false
set_option Elab.async false

namespace Final50ActiveCycle
noncomputable section
open K1_13 (Shape InBox Row shape)
open K1_13_6 (GeoField genericCoeffs toGeneric)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (Exponent oldEmbedding)
open Final50Price (primaryBox taylorLength evenClip)
open Low48BentLattice (Cap Allowed Chamber)
open Low48BentSupport (graph lifted)
open Low48BentCycle (Family rawFamily capFamily)
open Low49ActiveLattice (points Active)
open Low49ActiveSupport (Raw)
open MvPolynomial

def caps (p : Shape) : Fin 5 → Cap :=
  ![(p, 0), (primaryBox, 0), graph p, lifted p (taylorLength - 4), lifted p (taylorLength - 3)]




def baseClip (p : Shape) (K : ℕ) : ℕ := evenClip p 0 (p.b + p.j - K)

def graphClip (p : Shape) (K : ℕ) : ℕ :=
  evenClip ⟨p.b, p.j + 1, p.t + 1⟩ 1 (baseClip p K)

def liftClip (p : Shape) (K k : ℕ) : ℕ :=
  evenClip (lifted p k).1 (k + 1) (2 + k * (baseClip p K - 2))

def clips (p : Shape) (K : ℕ) : Fin 5 → ℕ :=
  ![baseClip p K, 498, graphClip p K, liftClip p K (taylorLength - 4),
    liftClip p K (taylorLength - 3)]










def activeFamily (p : Shape) (K : ℕ) : Family := fun i => points (caps p i) (clips p K i)

instance (p : Shape) (K : ℕ) (i : Fin 5) : Finite (activeFamily p K i) :=
  (Low49ActiveLattice.finite _ _).to_subtype



end
end Final50ActiveCycle

end Merged_Final50ActiveCycleCaps

-- merged module Final50ActiveCyclePrice
section Merged_Final50ActiveCyclePrice

set_option autoImplicit false
set_option Elab.async false

namespace Final50ActiveCycle
noncomputable section

open Low48BentLattice (Cap Chamber Scale latticePoints)
open Low49ActiveLattice (Fits points)
open K1_13 (Shape)
open K1_13_6 (GeoField)
open K1_13_6_2_4_1 (Grade Form unitGrade positiveDiagonal positiveDiagonal_apply
  cube_extract line_coeff squarefree squarefree_apply)
open Low48BentCycle (Family capFamily capSum ambient_cap integral mixedDegree diagonalExponents
  diagonal_nsmul diagonal_add)
open MvPolynomial
open scoped BigOperators Pointwise

open Low48BentCycle (diagonal_unit grade_sum diagonal_sum coeff_congr)
open Low48BentCycle (ambient_list)
open Low49ActiveVolume (fits_scale point_scale point_zero)














end
end Final50ActiveCycle

end Merged_Final50ActiveCyclePrice
