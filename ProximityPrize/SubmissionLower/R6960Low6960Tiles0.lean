import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup58
import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.DdCS
import ProximityPrize.SubmissionLower.DdZ1iXjHc
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.KoalaCompression
import ProximityPrize.SubmissionLower.R6960CollisionTameBranchFrame
import ProximityPrize.SubmissionLower.R6960Front6960Rank4
import ProximityPrize.SubmissionLower.R6960Low6960Gates
import ProximityPrize.SubmissionLower.R6960Low6960GeometryCut
import ProximityPrize.SubmissionLower.R6960Low6960Rectangle
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top10
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top11
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top12
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top13
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top14
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top2
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top3
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top4
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top5
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top6
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top7
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top8
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0Top9
import ProximityPrize.SubmissionLower.R6966ProofProtocolProfile

section Merged6967_R6960Low6960Tiles0
set_option Elab.async false















set_option Elab.async false

namespace Low6960Allocation.Group0
open K1_13 (Shape InBox)
open K1_13_8 (Valid)

def receipt : Receipt 0 where
  orders := orders
  covers := by
    intro a ha box
    change 0+a.b≤136 ∧ 0+a.j≤57 ∧ 0+a.t≤14 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 ∨ a.t=14 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
    · exact Top1.exact a ha h1 (by omega) (by omega)
    · exact Top2.exact a ha h2 (by omega) (by omega)
    · exact Top3.exact a ha h3 (by omega) (by omega)
    · exact Top4.exact a ha h4 (by omega) (by omega)
    · exact Top5.exact a ha h5 (by omega) (by omega)
    · exact Top6.exact a ha h6 (by omega) (by omega)
    · exact Top7.exact a ha h7 (by omega) (by omega)
    · exact Top8.exact a ha h8 (by omega) (by omega)
    · exact Top9.exact a ha h9 (by omega) (by omega)
    · exact Top10.exact a ha h10 (by omega) (by omega)
    · exact Top11.exact a ha h11 (by omega) (by omega)
    · exact Top12.exact a ha h12 (by omega) (by omega)
    · exact Top13.exact a ha h13 (by omega) (by omega)
    · exact Top14.exact a ha h14 (by omega) (by omega)
end Low6960Allocation.Group0

end Merged6967_R6960Low6960Tiles0

section Merged6967_R6960Low6960WeightedCut
set_option Elab.async false








set_option Elab.async false

-- merged module R6960Low6960WeightedTally
section Merged_R6960Low6960WeightedTally

-- merged module R6960Low6960SharedThirdCut
section Merged_R6960Low6960SharedThirdCut

set_option Elab.async false
set_option autoImplicit false

namespace Low6960SharedThirdCut
noncomputable section

open Finset Polynomial MvPolynomial
open P3 (I K)

local instance (p : Prop) : Decidable p := Classical.propDecidable p
open scoped BigOperators ENat Polynomial
open K1_13 (Row Geom Shape shape InBox chart atJet extend embed)
open K1_13_6 (GeoJets GeoField HighChart markIdeal evalGeneric toGeneric intersectionIdeal
  cycleLength divisorIdeal separant CurveSections Pieces)
open K1_13_6_1 (mem_markIdeal mark_curve)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective)
open K1_13_6_3 (dimension cycleWeight)
open K1_13_7_1 (derivative_in_box shape_chamber)
open P0_9_6_1_2 (exists_value_cut)
open Low6960Prices (taylorLength primaryBox Messages)
open Low6960GeometryCut (CutInput)
open Low6960GeometryCut_3 (cutCycle)
open P0_9_6_3 (canonical_unique cycleWeight_ge)
open K1_14_6 (curve_degree_nat)

abbrev chartWidth (f : Row 4) : ℕ := (chart (taylorLength+2) (shape f).chamber).b

def Marked (f Q : Row 4) (l : ℕ) (surfaces : Finset (Ideal GeoJets)) (S : (Polynomial Geom)) : Prop :=
  ∃ P ∈ surfaces, ∃ r, HighChart f Q l S P r

private theorem points_of_value {Γ : Finset K} {s : K → (Polynomial K)} {C : Ideal GeoJets}
    (prime : C.IsPrime) (hdim : dimension C = 1)
    (hinj : Set.InjOn s (Γ : Set K))
    (hC : ∀ γ ∈ Γ, C ≤ markIdeal (extend (s γ)))
    (d : ℕ) (cuts : ∀ x a : K, ∃ D : GeoJets, D.totalDegree ≤ d ∧
      ∀ γ ∈ Γ, (evalGeneric (extend (s γ)) D = 0 ↔ (s γ).eval x = a)) :
    CurveSections Γ s ⌊(d : ℚ) * affineDegree C⌋₊ := by
  classical
  let := prime
  intro x a hmiss
  obtain ⟨D, hD, hvalue⟩ := cuts x a
  have hproper : D ∉ C := by
    obtain ⟨γ, hγ, hne⟩ := hmiss
    exact fun hm => hne ((hvalue γ hγ).mp (hC γ hγ hm))
  let J := C ⊔ Ideal.span {D}
  obtain ⟨hJdim, hJdeg⟩ :=
    principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime prime hproper hD
  have hJzero : (affineHilbertPolynomial J).natDegree = 0 := by
    change (affineHilbertPolynomial J).natDegree ≤ dimension C - 1 at hJdim
    omega
  have hdeg : affineDegree J ≤ (d : ℚ) * affineDegree C := by
    have hd : (affineHilbertPolynomial C).natDegree = 1 := hdim
    simpa [J, affineDegree, hd, hJzero, Polynomial.leadingCoeff] using hJdeg
  let T := Γ.filter fun γ => (s γ).eval x = a
  let point (γ : K) := actualPoint (extend (s γ))
  have hpoint : Set.InjOn point (Γ : Set K) := fun _ hγ _ hη he =>
    hinj hγ hη (Polynomial.map_injective embed embed.injective (actualPoint_injective he))
  have hinto : (T.image point : Set JetPoint) ⊆ zeroLocus GeoField J := by
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hy
    obtain ⟨hΓ, hv⟩ := mem_filter.mp hγ
    exact mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hC γ hΓ, (hvalue γ hΓ).mpr hv⟩
  obtain ⟨hfinite, hcount⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K := GeoField) J hJzero
  have hcard := Set.ncard_le_ncard hinto hfinite
  rw [Set.ncard_coe_finset, card_image_of_injOn (hpoint.mono (filter_subset _ _))] at hcard
  exact Nat.le_floor ((Nat.cast_le.mpr hcard).trans (hcount.trans hdeg))

private theorem curve_family {Γ : Finset K} {s : K → (Polynomial K)} {f Q R : Row 4} {l : ℕ}
    (input : CutInput Γ s f Q l) {P C : Ideal GeoJets}
    (hP : (intersectionIdeal f Q).IsMinimalPrime P) (hR : toGeneric R ∉ P)
    (hC : (divisorIdeal P R).IsMinimalPrime C) :
    let part := Γ.filter fun γ => C ≤ markIdeal (extend (s γ)) ∧
      ∃ r, HighChart f Q l (extend (s γ)) P r
    CurveSections part s ⌊(chartWidth f : ℚ) * affineDegree C⌋₊ ∧
      0 < ⌊(chartWidth f : ℚ) * affineDegree C⌋₊ := by
  classical
  let := hP.isPrime
  have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hR hC
  change dimension C + 1 = dimension P at hd
  rw [(cutCycle input.small input.proper input.box).local_bound P hP |>.1] at hd
  have hdim : dimension C = 1 := by omega
  let part := Γ.filter fun γ => C ≤ markIdeal (extend (s γ)) ∧
    ∃ r, HighChart f Q l (extend (s γ)) P r
  have hsub : part ⊆ Γ := filter_subset _ _
  have hposW : 1 ≤ chartWidth f := le_max_of_le_left (Nat.le_add_right 1 _)
  obtain ⟨δ, hδ, hδeq⟩ := K1_14_6.curve_degree_nat C hC.isPrime hdim
  have hdpos : 0 < ⌊(chartWidth f : ℚ) * affineDegree C⌋₊ := by
    change 1 ≤ _
    apply Nat.le_floor
    rw [hδeq]
    exact_mod_cast (Nat.mul_le_mul hposW (Nat.succ_le_of_lt hδ))
  refine ⟨?_, hdpos⟩
  change CurveSections part s _
  by_cases hempty : part = ∅
  · rw [hempty]
    intro x a h
    simpa using h
  obtain ⟨γ₀, hγ₀⟩ := nonempty_iff_ne_empty.mpr hempty
  obtain ⟨r, hγchart⟩ := (mem_filter.mp hγ₀).2.2
  let p := (shape f).chamber
  let g := (separant^[r]) f
  have hgbox : InBox (shape g) p :=
    let hb := derivative_in_box f r
    ⟨hb.1.trans (le_max_left _ _), hb.2.1, hb.2.2⟩
  apply points_of_value hC.isPrime hdim (input.distinct.mono hsub)
    (fun γ hγ => (mem_filter.mp hγ).2.1)
  intro x a
  obtain ⟨D, hD, hv⟩ := exists_value_cut (by decide : taylorLength+2 ≤ K1.p) hgbox
    (shape_chamber f) input.small.2.1 x a
  refine ⟨D, hD.1, fun γ hγ => ?_⟩
  obtain ⟨r', hh⟩ := (mem_filter.mp hγ).2.2
  have heq := P0_9_6_3.canonical_unique hh.chart hγchart.chart
  subst r'
  have hvan := mem_markIdeal.mp (hh.point (hh.chart.2.1 r le_rfl))
  exact hv (s γ) ((input.degree γ (hsub hγ)).trans_lt (by decide)) hvan hh.regular

private theorem cut_degree {f Q R : Row 4} {l : ℕ} {Γ : Finset K} {s : K → (Polynomial K)}
    (input : CutInput Γ s f Q l) (surfaces : Finset (Ideal GeoJets))
    (origin : ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime)
    (hR : ∀ P ∈ surfaces, toGeneric R ∉ P) (hwidth : (shape R).b ≤ primaryBox.b) :
    (l : ℚ) * (∑ P ∈ surfaces, ∑ C ∈ (divisorIdeal P R).minimalPrimesFinset, affineDegree C) ≤
      ((shape f).b * primaryBox.b * primaryBox.b : ℕ) := by
  let pair := intersectionIdeal f Q
  let w := cycleWeight pair
  let B := primaryBox.b
  have hc := cutCycle input.small input.proper input.box
  have sub : surfaces ⊆ pair.minimalPrimesFinset := fun P hP =>
    Ideal.mem_minimalPrimesFinset.mpr (origin P hP).choose
  have hwidth' : (toGeneric R).totalDegree ≤ B :=
    (K1_13_6_3_6.totalDegree_toGeneric R).le.trans hwidth
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ P ∈ surfaces, (B : ℚ) * ((w P : ℚ) * affineDegree P) := by
      apply sum_le_sum
      intro P hP
      obtain ⟨hp, hl⟩ := origin P hP
      let := hp.isPrime
      have hl' : (l : ℚ) ≤ w P := by exact_mod_cast P0_9_6_3.cycleWeight_ge hc hp hl
      have hdeg := principalCut_sum_affineDegree_minimalPrimes_le (hR P hP) hwidth'
      exact (mul_le_mul_of_nonneg_left hdeg (by positivity)).trans (by
        rw [mul_left_comm]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hl' (affineDegree_nonneg P))
    _ = (B : ℚ) * ∑ P ∈ surfaces, (w P : ℚ) * affineDegree P := (Finset.mul_sum ..).symm
    _ ≤ (B : ℚ) * (((shape f).b * B : ℕ) : ℚ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sum_le_sum_of_subset_of_nonneg sub
        (fun P _ _ => mul_nonneg (by positivity) (affineDegree_nonneg P))).trans hc.weighted_degree
    _ = _ := by push_cast; ring

/-- Assign third-cut curves using the old surface and one regular value section. -/
theorem cover {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}
    (input : CutInput Γ s f Q l) (surfaces : Finset (Ideal GeoJets)) (R : Row 4)
    (origin : ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime)
    (hwidth : (shape R).b ≤ primaryBox.b)
    (hproper : ∀ P ∈ surfaces, toGeneric R ∉ P)
    (hzero : ∀ γ ∈ Γ, atJet R (extend (s γ)) = 0) :
    ∃ C : Pieces Γ, C.curves s ∧ (∀ i, 0 < C.degree i) ∧
      (∀ γ ∈ Γ, Marked f Q l surfaces (extend (s γ)) → γ ∈ C.union) ∧
      l * C.total ≤ (shape f).b * primaryBox.b * primaryBox.b * chartWidth f := by
  classical
  let T := surfaces.sigma fun P => (divisorIdeal P R).minimalPrimesFinset
  let e := T.equivFin.symm
  let marks (P C : Ideal GeoJets) := Γ.filter fun γ => C ≤ markIdeal (extend (s γ)) ∧
    ∃ r, HighChart f Q l (extend (s γ)) P r
  let d (C : Ideal GeoJets) := ⌊(chartWidth f : ℚ) * affineDegree C⌋₊
  let blocks : Pieces Γ := ⟨T.card, fun i => marks (e i).val.1 (e i).val.2,
    fun _ => filter_subset _ _, fun i => d (e i).val.2⟩
  have square (i : Fin T.card) : CurveSections (blocks.piece i) s (blocks.degree i) ∧
      0 < blocks.degree i := by
    let a := e i
    obtain ⟨hP,hC⟩ := mem_sigma.mp a.property
    exact curve_family input (origin a.val.1 hP).choose (hproper a.val.1 hP)
      (Ideal.mem_minimalPrimesFinset.mp hC)
  refine ⟨blocks, fun i => (square i).1, fun i => (square i).2, ?_, ?_⟩
  · intro γ hγ hm
    obtain ⟨P, hP, r, hh⟩ := hm
    obtain ⟨C, hC, hγC⟩ := mark_curve hh.point (hzero γ hγ)
    let a : T := ⟨⟨P,C⟩, mem_sigma.mpr ⟨hP, Ideal.mem_minimalPrimesFinset.mpr hC⟩⟩
    apply mem_biUnion.mpr
    refine ⟨T.equivFin a, mem_univ _, ?_⟩
    change γ ∈ marks (e (T.equivFin a)).val.1 (e (T.equivFin a)).val.2
    rw [show e (T.equivFin a) = a from T.equivFin.symm_apply_apply a]
    exact mem_filter.mpr ⟨hγ,hγC,⟨r,hh⟩⟩
  · have htotal : ((blocks.total : ℕ) : ℚ) ≤
        (chartWidth f : ℚ) * ∑ P ∈ surfaces, ∑ C ∈ (divisorIdeal P R).minimalPrimesFinset,
          affineDegree C := by
      unfold Pieces.total
      rw [Nat.cast_sum]
      change (∑ i : Fin T.card, ((d (e i).val.2 : ℕ) : ℚ)) ≤ _
      let value (a : Σ _ : Ideal GeoJets, Ideal GeoJets) : ℚ := (d a.2 : ℚ)
      have eq : (∑ i : Fin T.card, ((d (e i).val.2 : ℕ) : ℚ)) = ∑ a ∈ T, value a := by
        calc
          _ = ∑ a : T, value a.val := Fintype.sum_equiv e _ _ (fun _ => rfl)
          _ = _ := Finset.sum_attach T value
      rw [eq, show T = surfaces.sigma (fun P => (divisorIdeal P R).minimalPrimesFinset) from rfl,
        Finset.sum_sigma, Finset.mul_sum]
      refine sum_le_sum fun P _ => ?_
      rw [Finset.mul_sum]
      exact sum_le_sum fun C _ => Nat.floor_le (mul_nonneg (by positivity) (affineDegree_nonneg C))
    apply (Nat.cast_le (α := ℚ)).mp
    push_cast
    calc
      _ ≤ (l : ℚ) * ((chartWidth f : ℚ) * ∑ P ∈ surfaces,
          ∑ C ∈ (divisorIdeal P R).minimalPrimesFinset, affineDegree C) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ ≤ _ := by
        rw [mul_left_comm]
        have hc := mul_le_mul_of_nonneg_left
          (cut_degree input surfaces origin hproper hwidth) (by positivity : 0 ≤ (chartWidth f : ℚ))
        push_cast at hc
        exact hc.trans_eq (by ring)

/-- The charged nonpersistent labels use the third-cut fee alone. -/
theorem count {Γ : Finset K} {s : K → (Polynomial K)} {w : I → K} {f Q : Row 4} {l : ℕ}
    (hmsg : Messages w Γ s) (input : CutInput Γ s f Q l)
    (surfaces : Finset (Ideal GeoJets)) (R : Row 4)
    (origin : ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime)
    (hwidth : (shape R).b ≤ primaryBox.b)
    (hproper : ∀ P ∈ surfaces, toGeneric R ∉ P)
    (hzero : ∀ γ ∈ Γ, atJet R (extend (s γ)) = 0) :
    let assigned := Γ.filter fun γ => Marked f Q l surfaces (extend (s γ))
    assigned.card ≤ Low6960SharedPrice.nonsharedFee (shape f) l := by
  classical
  obtain ⟨C,hC,hpos,hcover,hdegree⟩ := cover input surfaces R origin hwidth hproper hzero
  have hsub : (Γ.filter fun γ => Marked f Q l surfaces (extend (s γ))) ⊆ C.union :=
    fun γ hγ => hcover _ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2
  apply (card_le_card hsub).trans ((Low6960FatPad.pieces_curve_capacity_integral C hmsg hC hpos).trans ?_)
  unfold Low6960SharedPrice.nonsharedFee K1_13.ceilDiv
  apply (Nat.le_div_iff_mul_le input.positive).mpr
  let numerator := 2 * (shape f).b * primaryBox.b^2 * chartWidth f
  change (2*C.total)*l ≤ numerator+l-1
  have hc : (2*C.total)*l ≤ numerator := by
    simpa only [numerator, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using Nat.mul_le_mul_left 2 hdegree
  have hl := input.positive
  omega

#print axioms cover
#print axioms count
end
end Low6960SharedThirdCut

end Merged_R6960Low6960SharedThirdCut

-- merged module R6960Low6960SharedCount
section Merged_R6960Low6960SharedCount

set_option Elab.async false
set_option maxHeartbeats 1700000
set_option maxRecDepth 20000
namespace Low6960SharedCount
noncomputable section

open P3 (K)
open K1_13 (Row Shape shape chart extend ceilDiv)
open K1_13_6 (GeoJets HighChart HighMark toGeneric intersectionIdeal cycleLength separant)
open K1_13_6_1_2 (VanishesTo pair_height)
open K1_13_6_2 (actualPoint)
open Low6960Prices (Messages SmallFactor ActiveFits physicalDegree primaryBox ProperCut)
open Low6960GeometryCut (CutInput MixedMark highMark_cases)
open Low6960GeometryCut_2 (Branch)
open Low6960SharedPrice (Rate RateFits slope coord)
open Low6960SharedTally (Data hasBranch)
open Low6960SharedTallyNew (tally)
open Low6960SharedTallyNew (tilted_count)
open Low6960SharedTallyOld (orderCost auxiliaryCap continuedCap surfaceCap)
open Low6960SharedPersistent (Persistent)
open Finset
open scoped Polynomial BigOperators
attribute [local instance] Classical.propDecidable
open Low6960GeometryCut (continued_bound le_ceil)
open Low6960GeometryCut_2 (eval_actualPoint genericCoeffs_injective)

theorem shape_valid {f : Row 4} (hf : SmallFactor f) : K1_13_8.Valid (shape f) := by
  refine ⟨hf.2.1,(K1_13_7_1.shape_chamber f).2,?_⟩
  change K1_13.indexDegree f ≤ 3*f.totalDegree
  rw [K1_13_1.indexDegree_eq]
  apply Finset.sup_le
  intro m hm
  have hdeg : (∑ i ∈ m.support,m i)≤f.totalDegree := MvPolynomial.le_totalDegree hm
  have hw : ∀ i : Fin 4, m i*i.val≤3*m i := fun i => by
    rw [Nat.mul_comm (m i)]
    exact Nat.mul_le_mul_right _ (by omega)
  change (∑ i ∈ m.support,m i*i.val) ≤ _
  exact (Finset.sum_le_sum (fun i _ => hw i)).trans
    (by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ hdeg)

private def HighOrder (f : Row 4) (k : ℕ) (P : Ideal GeoJets) : Prop :=
  ∃ h : P.IsPrime, @VanishesTo _ _ P h (toGeneric f) (k+1)

private theorem hasBranch_of_mixed {f Q l g S} (h : MixedMark f Q l g)
    (hs : ∀ P, (∃ r, HighChart f Q l g P r) → P∈S) : hasBranch f Q l S g := by
  obtain ⟨surf,r,hz,hE,C,hC,hP,hterminal⟩ := h
  have hr : MvPolynomial.eval (actualPoint g) (toGeneric (separant ((separant^[r]) f))) ≠ 0 := by
    rw [eval_actualPoint]
    exact fun hzero => hz.regular (genericCoeffs_injective (by simpa using hzero))
  have hc : toGeneric (separant ((separant^[r]) f)) ∉ C := fun hmem => hr (hP hmem)
  let b : Branch f Q l := ⟨surf,r,hz.base,hz.high,hz.chart,hz.invariant,hE,C,hC,hc,hterminal⟩
  exact ⟨b,hs surf ⟨r,hz⟩,hP,hr⟩

private theorem high_weight {Γ s f Q l}
    (data : Data Γ s f Q l {P | Persistent Γ s P}) (input : CutInput Γ s f Q l)
    (k : ℕ) :
    ∀ b ∈ data.branches,
      ((if HighOrder f k b.surface then (k+1)*l else l : ℕ) : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime := by
  classical
  intro b hb
  split_ifs with hh
  · obtain ⟨hP,hf⟩ := hh
    letI := b.base.isPrime
    have hQ := Low6960SharedPersistent.local_order (data.allowed b hb) input.box input.order
    exact Shared50Multiplicity.cycleLength_ge_product_of_minimal b.base
      (K1_13_6_3_6.toGeneric_ne_zero input.small.1.ne_zero)
      (K1_13_7_1.proper_generic f Q input.small.1 input.proper) hf hQ
  · exact b.high

private theorem sum_weights {Γ s f Q l S} (data : Data Γ s f Q l S) (k : ℕ) :
    let high := data.branches.filter (fun b => HighOrder f k b.surface)
    let low := data.branches.filter (fun b => ¬HighOrder f k b.surface)
    orderCost data (fun P => if HighOrder f k P then (k+1)*l else l) =
      l*(tally data low+(k+1)*tally data high) := by
  classical
  let p (b : Branch f Q l) := HighOrder f k b.surface
  let w (b : Branch f Q l) := (if p b then (k+1)*l else l)*(b.weight*(data.points b).card)
  change ∑ b∈data.branches,w b = _
  rw [← Finset.sum_filter_add_sum_filter_not data.branches p w]
  rw [Nat.mul_add,← Nat.mul_assoc]
  unfold tally
  rw [Finset.mul_sum,Finset.mul_sum]
  have hh : ∑ b ∈ data.branches.filter p,w b =
      ∑ b ∈ data.branches.filter p,(l*(k+1))*(b.weight*(data.points b).card) := by
    apply Finset.sum_congr rfl
    intro b hb
    simp only [w,if_pos (Finset.mem_filter.mp hb).2,Nat.mul_comm l (k+1)]
  have hl : ∑ b ∈ data.branches.filter (fun b=>¬p b),w b =
      ∑ b ∈ data.branches.filter (fun b=>¬p b),l*(b.weight*(data.points b).card) := by
    apply Finset.sum_congr rfl
    intro b hb
    simp only [w,if_neg (Finset.mem_filter.mp hb).2]
  rw [hh,hl,Nat.add_comm]

private theorem count_low {w Γ s f Q l}
    (hm : Messages w Γ s) (data : Data Γ s f Q l {P | Persistent Γ s P})
    (input : CutInput Γ s f Q l) (u : Rate) (hu : RateFits (shape f) u) :
    tally data (data.branches.filter (fun b => ¬HighOrder f u.split b.surface)) ≤ u.amount := by
  classical
  let F := data.branches.filter (fun b => ¬HighOrder f u.split b.surface)
  let P := F.image Branch.surface
  have memP (b : Branch f Q l) (hb : b∈F) : b.surface∈P := Finset.mem_image.mpr ⟨b,hb,rfl⟩
  have hp : ∀ p∈P, Persistent Γ s p := by
    intro p hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
    exact data.allowed b (Finset.mem_filter.mp hb).1
  have hs : ∀ p∈P, Low6960SharedChooseCut.SuitableSurface f u.split p := by
    intro p hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨b.base.isPrime, ?_, b.base.le (Ideal.subset_span (by simp)), ?_⟩
    · exact pair_height (K1_13_6_3_6.toGeneric_ne_zero input.small.1.ne_zero)
        (K1_13_7_1.proper_generic f Q input.small.1 input.proper) b.base
    · exact fun hh => (Finset.mem_filter.mp hb).2 ⟨b.base.isPrime,hh⟩
  have hfpos : 0<f.totalDegree := lt_of_lt_of_le input.small.2.1
    (MvPolynomial.degreeOf_le_totalDegree _ _)
  obtain ⟨r,a,hr,hn,G,hG,hproper,hbox,hcut⟩ :=
    Low6960SharedChooseCut.exists_cut hm f input.small.1 hfpos u.split u.pivot hu.2.2.1 P hp hs
  exact Low6960SharedTallyNew.count data input F (Finset.filter_subset _ _) G hproper u hu r a hn
    (shape_valid input.small) hbox (fun b hb=>hcut _ (memP b hb))

/-- A proper cut of all persistent surfaces of the indicated anchor order. -/
def TiltedCut {Γ : Finset K} {s : K → (Polynomial K)} (f : Row 4) (u : Rate) : Prop :=
  ∀ (P : Finset (Ideal GeoJets)), (∀ p ∈ P, Persistent Γ s p) →
    (∀ p ∈ P, Low6960SharedChooseCut.SuitableSurface f u.split p) →
    ∃ (n : ℕ) (G : Row 4), 0 < n ∧ (¬ f ∣ G) ∧
      (∀ p ∈ P, ∃ h : (intersectionIdeal f G).IsMinimalPrime p,
        (n : ℕ∞) ≤ cycleLength (intersectionIdeal f G) p h.isPrime) ∧
      Low6960SharedPrice.surface .tilted (shape f) (shape G).chamber ≤ 1920 * u.amount * n

private theorem count_low_tilted {Γ s f Q l}
    (data : Data Γ s f Q l {P | Persistent Γ s P}) (input : CutInput Γ s f Q l)
    (u : Rate) (ht : Low6960Prices.tiltedFits (shape f)) (cut : TiltedCut (Γ := Γ) (s := s) f u) :
    tally data (data.branches.filter (fun b => ¬ HighOrder f u.split b.surface)) ≤ u.amount := by
  classical
  let F := data.branches.filter (fun b => ¬ HighOrder f u.split b.surface)
  let P := F.image Branch.surface
  have hp : ∀ p ∈ P, Persistent Γ s p := by
    intro p hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
    exact data.allowed b (Finset.mem_filter.mp hb).1
  have hs : ∀ p ∈ P, Low6960SharedChooseCut.SuitableSurface f u.split p := by
    intro p hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨b.base.isPrime, ?_, b.base.le (Ideal.subset_span (by simp)), ?_⟩
    · exact pair_height (K1_13_6_3_6.toGeneric_ne_zero input.small.1.ne_zero)
        (K1_13_7_1.proper_generic f Q input.small.1 input.proper) b.base
    · exact fun hh => (Finset.mem_filter.mp hb).2 ⟨b.base.isPrime,hh⟩
  obtain ⟨n,G,hn,hproper,horder,hrate⟩ := cut P hp hs
  exact tilted_count data input F (Finset.filter_subset _ _) G hproper n u.amount hn ht
    (fun b hb => horder b.surface (Finset.mem_image.mpr ⟨b,hb,rfl⟩)) hrate

private theorem cover_split {w Γ s f Q l}
    (hm : Messages w Γ s) (input : CutInput Γ s f Q l) :
    ∃ U : Finset K, U.card ≤ Low6960SharedPrice.nonsharedFee (shape f) l ∧
      ∀ γ∈Γ, MixedMark f Q l (extend (s γ)) → γ∈U ∨
        hasBranch f Q l {P | Persistent Γ s P} (extend (s γ)) := by
  classical
  let mins := (intersectionIdeal f Q).finite_minimalPrimes_of_isNoetherianRing
  let S := mins.toFinset.filter (fun P => ¬Persistent Γ s P ∧
    ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l : ℕ∞)≤cycleLength (intersectionIdeal f Q) P h.isPrime)
  obtain ⟨R,hR,hAvoid⟩ := Low6960SharedPersistent.common_avoider Γ s S
    (fun P hP => (Finset.mem_filter.mp hP).2.1)
  let U := Γ.filter (fun γ => Low6960SharedThirdCut.Marked f Q l S (extend (s γ)))
  have hU : U.card≤Low6960SharedPrice.nonsharedFee (shape f) l :=
    Low6960SharedThirdCut.count hm input S R (fun P hP=>(Finset.mem_filter.mp hP).2.2)
      hR.1 hAvoid hR.2
  refine ⟨U,hU,?_⟩
  intro γ hγ hMixed
  by_cases h : γ∈U
  · exact Or.inl h
  · refine Or.inr (hasBranch_of_mixed hMixed ?_)
    intro P hP
    obtain ⟨r,hchart⟩ := hP
    by_contra hn
    have hP' : P∈S := Finset.mem_filter.mpr
      ⟨mins.mem_toFinset.mpr hchart.base,hn,hchart.base,hchart.high⟩
    exact h (Finset.mem_filter.mpr ⟨hγ,P,hP',r,hchart⟩)

private theorem final_fee {x : Shape} {l K aux curves surfaces L H : ℕ}
    (u : Rate)
    (hold : aux+curves+surfaces+(L+(u.split+1)*H)≤Low6960Prices.physicalPrice x l K)
    (hbase : aux+curves+surfaces≤Low6960SharedPrice.additiveBase x l)
    (hlow : L≤u.amount) :
    aux+curves+surfaces+(L+H)+Low6960SharedPrice.nonsharedFee x l ≤
      Low6960SharedPrice.price x l K u := by
  unfold Low6960SharedPrice.price
  apply Nat.add_le_add_right
  apply le_ceil (by omega)
  calc
    _ = (aux+curves+surfaces+(L+(u.split+1)*H)) +
        u.split*(aux+curves+surfaces)+u.split*L := by ring
    _ ≤ Low6960Prices.physicalPrice x l K + u.split*Low6960SharedPrice.additiveBase x l +
        u.split*u.amount := Nat.add_le_add
          (Nat.add_le_add hold (Nat.mul_le_mul_left _ hbase)) (Nat.mul_le_mul_left _ hlow)
    _ ≤ _ := Nat.le_add_right _ _

theorem cover_counts {w Γ s f Q l} (hm : Messages w Γ s)
    (input : CutInput Γ s f Q l) (data : Data Γ s f Q l {P | Persistent Γ s P}) :
    ∃ a c d : ℕ,
      Γ.card ≤ a+c+d+tally data data.branches+Low6960SharedPrice.nonsharedFee (shape f) l ∧
      a ≤ auxiliaryCap (shape f) ∧ l*c ≤ continuedCap (shape f) ∧ d ≤ surfaceCap (shape f) := by
  classical
  obtain ⟨U,hU,hUC⟩ := cover_split hm input
  obtain ⟨A,B,hA,hAC,hAB,hAB'⟩ := Low6960GeometryCut_1.proof Γ s f Q l input
  obtain ⟨C,E,hC,hEC,hCP,hCB⟩ := data.pieces input
  obtain ⟨D,F,hD,hF,hDP,hFP,hDF,hDB,hFB⟩ := continued_bound Γ s f Q l input
  let a := A.union.card+B.card
  let c := D.union.card
  let d := F.union.card
  have hCover : Γ ⊆ ((A.union ∪ B) ∪ (C.union ∪ E)) ∪ (D.union ∪ F.union) ∪ U := by
    intro γ hγ
    by_cases hh : HighMark f Q l (extend (s γ))
    · have hdeg : (extend (s γ)).natDegree ≤ physicalDegree := by
        rw [Polynomial.natDegree_map]
        exact hm.degree γ hγ
      rcases highMark_cases hdeg hh with h | h
      · rcases hUC γ hγ h with hU | hP
        · exact Finset.mem_union_right _ hU
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
            (hCP γ hγ hP)))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hDF γ hγ h))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (hAC γ hγ hh)))
  have hM : C.union.card+E.card ≤ tally data data.branches := by
    have hCC := Low6960GeometryCut.pieces_curve_capacity_integral C hm hC hEC
    change 2*C.total+E.card≤tally data data.branches at hCB
    omega
  have hCard : Γ.card ≤ a+c+d+tally data data.branches+Low6960SharedPrice.nonsharedFee (shape f) l := by
    have h0 := Finset.card_le_card hCover
    have h1 := Finset.card_union_le (((A.union∪B)∪(C.union∪E))∪(D.union∪F.union)) U
    have h2 := Finset.card_union_le ((A.union∪B)∪(C.union∪E)) (D.union∪F.union)
    have h3 := Finset.card_union_le (A.union∪B) (C.union∪E)
    have h4 := Finset.card_union_le A.union B
    have h5 := Finset.card_union_le C.union E
    have h6 := Finset.card_union_le D.union F.union
    dsimp only [a,c,d]
    omega
  have hAux : a≤auxiliaryCap (shape f) := by
    unfold auxiliaryCap
    apply le_ceil (by decide)
    have hA' := Low6960GeometryCut.pieces_curve_capacity A hm hA
    dsimp only [a]
    omega
  have hCurve : l*c≤continuedCap (shape f) := by
    unfold continuedCap
    apply le_ceil (by decide)
    have hD' := Nat.mul_le_mul_left l (Low6960GeometryCut.pieces_curve_capacity_integral D hm hD hDP)
    change l*D.total ≤ Low6960GeometryCut.membershipDegree (shape f) at hDB
    have hD'' : l*c ≤ 2*Low6960GeometryCut.membershipDegree (shape f) := by
      rw [Nat.mul_left_comm] at hD'
      dsimp only [c]
      omega
    omega
  have hSurface : d≤surfaceCap (shape f) := by
    change F.union.card≤2*(133429*(shape f).b*primaryBox.b)
    have hF' := Low6960GeometryCut.pieces_surface_capacity F hm hF hFP
    change 2*F.total ≤ 133429*(shape f).b*primaryBox.b at hFB
    exact hF'.trans ((show 4*F.total=2*(2*F.total) by ring).le.trans
      (Nat.mul_le_mul_left 2 hFB))
  exact ⟨a,c,d,hCard,hAux,hCurve,hSurface⟩

private theorem count_of_low {w Γ s} (hm : Messages w Γ s) (f : Row 4)
    (hf : SmallFactor f) (cap : ℕ) (hcap : ActiveFits f cap)
    (hOn : ∀ γ ∈ Γ, K1_13.OnFactor f (extend (s γ)))
    (l : ℕ) (hl : 0 < l) (hCut : ProperCut f Γ s l) (u : Rate)
    (bound : ∀ Q, CutInput Γ s f Q l → ∀ data : Data Γ s f Q l {P | Persistent Γ s P},
      tally data (data.branches.filter (fun b => ¬ HighOrder f u.split b.surface)) ≤ u.amount) :
    Γ.card ≤ Low6960SharedPrice.price (shape f) l cap u := by
  classical
  obtain ⟨Q,hproper,hbox,hweight,hQ,horder⟩ := hCut
  have input : CutInput Γ s f Q l :=
    ⟨hm.distinct,hm.degree,hf,hOn,hl,hproper,hbox,hweight,horder⟩
  let data : Data Γ s f Q l {P | Persistent Γ s P} := Low6960SharedTally.build _
  let low := data.branches.filter (fun b => ¬HighOrder f u.split b.surface)
  let high := data.branches.filter (fun b => HighOrder f u.split b.surface)
  let L := tally data low
  let H := tally data high
  have hLow : L≤u.amount := bound Q input data
  have hSum : tally data data.branches = L+H := by
    unfold L H low high tally
    rw [Nat.add_comm]
    exact (Finset.sum_filter_add_sum_filter_not data.branches
      (fun b => HighOrder f u.split b.surface) _).symm
  obtain ⟨a,c,d,hCard,hAux,hCurve,hSurface⟩ := cover_counts hm input data
  rw [hSum] at hCard
  let weight (P : Ideal GeoJets) := if HighOrder f u.split P then (u.split+1)*l else l
  have hW : l*(L+(u.split+1)*H) ≤ orderCost data weight := (sum_weights data u.split).ge
  have hold := Low6960SharedTallyOld.physical_bound data input cap hcap hQ weight
    (high_weight data input u.split) hAux hCurve hSurface hW
  have hbase := Low6960SharedTallyOld.additive_le hl hAux hCurve hSurface
  exact hCard.trans (final_fee u hold hbase hLow)

/-- Count marks using a separate construction for the common tilted surface cut. -/
theorem tilted_proof {w Γ s} (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f)
    (cap : ℕ) (hcap : ActiveFits f cap) (hOn : ∀ γ ∈ Γ, K1_13.OnFactor f (extend (s γ)))
    (l : ℕ) (hl : 0 < l) (hCut : ProperCut f Γ s l) (u : Rate)
    (ht : Low6960Prices.tiltedFits (shape f)) (cut : TiltedCut (Γ := Γ) (s := s) f u) :
    Γ.card ≤ Low6960SharedPrice.price (shape f) l cap u :=
  count_of_low hm f hf cap hcap hOn l hl hCut u (fun _ input data => count_low_tilted data input u ht cut)

theorem proof : Low6960SharedPrice.cShared := by
  intro w Γ s hm f hf cap hcap hOn l hl hCut u hu
  exact count_of_low hm f hf cap hcap hOn l hl hCut u (fun _ input data => count_low hm data input u hu)

#print axioms tilted_proof
#print axioms proof
end
end Low6960SharedCount

end Merged_R6960Low6960SharedCount

-- merged module R6960Low6960WeightedTally
section Merged_R6960Low6960WeightedTally

set_option Elab.async false
set_option maxHeartbeats 1500000

namespace Low6960WeightedTally
noncomputable section

open P3 (K)
open K1_13 (Row shape ceilDiv)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength)
open K1_13_6_1_2 (VanishesTo pair_height)
open Low6960Prices (Messages SmallFactor ActiveFits ProperCut)
open Low6960GeometryCut (CutInput)
open Low6960GeometryCut_2 (Branch)
open Low6960SharedPrice (Rate surface surfaceScale)
open Low6960SharedTally (Data)
open Low6960SharedTallyNew (tally)
open Low6960SharedTallyOld (orderCost auxiliaryCap continuedCap surfaceCap)
open Low6960SharedPersistent (Persistent)
open Low6960GeometryCut (le_ceil)
open scoped Polynomial BigOperators ENat

variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}
  {S : Set (Ideal GeoJets)}

def weighted (D : Data Γ s f Q l S) (F : Finset (Branch f Q l))
    (w : Ideal GeoJets → ℕ) : ℕ :=
  ∑ b ∈ F, w b.surface * (b.weight * (D.points b).card)

theorem tilted (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (G : Row 4) (hproper : ¬ f ∣ G)
    (w : Ideal GeoJets → ℕ) (n limit : ℕ) (hn : 0 < n) (htilt : Low6960Prices.tiltedFits (shape f))
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal f G).IsMinimalPrime b.surface,
      ((n * w b.surface : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f G) b.surface h.isPrime)
    (hsize : surface .tilted (shape f) (shape G).chamber ≤ 1920 * limit * n) :
    weighted D F w ≤ limit := by
  let p := (shape f).chamber
  let q := (shape G).chamber
  have ht : 1 ≤ p.t := input.small.2.1
  have hq : Low48BentLattice.Chamber (q,0) :=
    ⟨(K1_13_7_1.shape_chamber G).1, (K1_13_7_1.shape_chamber G).2, Nat.zero_le _⟩
  have hfamily := Low6960SharedBentCaps.caps_chamber (K1_13_7_1.shape_chamber f).1 ht htilt.1 hq
  let R := Low48BentCycle.rawFamily (Low6960SharedBentCaps.caps p q)
  let B := Low48BentCycle.capFamily (Low6960SharedBentCaps.caps p q)
  have h := Low6960SharedCycleBound.bound_with_cut (R := R) (B := B)
    Low6960SharedBentCaps.ordinary_doubled f Q G l input.small hproper (fun P => n * w P)
    (Low48BentCycle.old_section ⟨le_max_left _ _, le_rfl, le_rfl⟩)
    (Low48BentCycle.old_section ⟨le_max_left _ _, le_rfl, le_rfl⟩)
    F D.points (fun b hb => D.bent input (Low6960SharedBentCaps.chart q ht) b (hF hb)) hcut
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℚ) ≤ 60 * 32)).trans
    (Low6960SharedBentCaps.ordinary_budget hfamily)
  have hnum : 1920 * n * weighted D F w ≤ surface .tilted (shape f) (shape G).chamber := by
    norm_num only [show (60 : ℚ) * 32 = 1920 by norm_num] at hh
    apply (Nat.cast_le (α := ℚ)).mp
    simpa only [weighted, Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, ← Finset.mul_sum,
      mul_comm, mul_left_comm, mul_assoc, surface] using hh
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos (by decide : 0 < 1920) hn)
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnum.trans hsize

def Relevant (f : Row 4) (u : Rate) (order : Ideal GeoJets → ℕ) (P : Ideal GeoJets) : Prop :=
  P.IsPrime ∧ P.height = 2 ∧ toGeneric f ∈ P ∧ order P ≤ u.split

def Cut {Γ : Finset K} {s : K → (Polynomial K)} (f : Row 4) (u : Rate)
    (order : Ideal GeoJets → ℕ) : Prop :=
  ∀ (P : Finset (Ideal GeoJets)), (∀ p ∈ P, Persistent Γ s p) →
    (∀ p ∈ P, Relevant f u order p) →
    ∃ (n : ℕ) (G : Row 4), 0 < n ∧ (¬ f ∣ G) ∧
      (∀ N > 0, ∀ p ∈ P, ∃ h : (intersectionIdeal f (G^N)).IsMinimalPrime p,
        ((N * n * (u.split + 1 - order p) : ℕ) : ℕ∞) ≤
          cycleLength (intersectionIdeal f (G^N)) p h.isPrime) ∧
      surface u.kind (shape f) (shape G).chamber ≤ surfaceScale u.kind * (u.split * u.amount) * n

private theorem deficit_bound (data : Data Γ s f Q l {P | Persistent Γ s P})
    (input : CutInput Γ s f Q l) (u : Rate)
    (hk : u.kind = .tilted) (ht : Low6960Prices.tiltedFits (shape f))
    (order : Ideal GeoJets → ℕ) (cut : Cut (Γ := Γ) (s := s) f u order) :
    weighted data data.branches (fun p => u.split + 1 - order p) ≤ u.split * u.amount := by
  classical
  let F := data.branches.filter (fun b => order b.surface ≤ u.split)
  let P := F.image Branch.surface
  have hp : ∀ p ∈ P, Persistent Γ s p := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
    exact data.allowed b (Finset.mem_filter.mp hb).1
  have hs : ∀ p ∈ P, Relevant f u order p := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨b.base.isPrime,
      pair_height (K1_13_6_3_6.toGeneric_ne_zero input.small.1.ne_zero)
        (K1_13_7_1.proper_generic f Q input.small.1 input.proper) b.base,
      b.base.le (Ideal.subset_span (by simp)), (Finset.mem_filter.mp hb).2⟩
  obtain ⟨n, G, hn, hproper, hlength, hsize⟩ := cut P hp hs
  let w (p : Ideal GeoJets) := u.split + 1 - order p
  have cutLength (N : ℕ) (hN : 0 < N) (b : Branch f Q l) (hb : b ∈ F) :=
    hlength N hN b.surface (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  have hF : weighted data F w ≤ u.split * u.amount := by
    exact tilted data input F (Finset.filter_subset _ _) G hproper w n (u.split * u.amount) hn ht
      (fun b hb => by simpa only [pow_one, one_mul] using cutLength 1 (by decide) b hb)
      (by simpa only [hk, surfaceScale] using hsize)
  refine le_trans ?_ hF
  unfold weighted F
  rw [Finset.sum_filter]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : order b.surface ≤ u.split
  · simp only [if_pos hb, w]
  · have hz : u.split + 1 - order b.surface = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp only [if_neg hb, hz, Nat.zero_mul]

theorem count {w} (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f)
    (cap : ℕ) (hcap : ActiveFits f cap) (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ)))
    (l : ℕ) (hl : 0 < l) (hproper : ProperCut f Γ s l) (u : Rate)
    (hk : u.kind = .tilted) (ht : Low6960Prices.tiltedFits (shape f)) (order : Ideal GeoJets → ℕ)
    (horder : ∀ p (hp : p.IsPrime), toGeneric f ∈ p → order p ≤ u.split + 1 ∧
      @VanishesTo _ _ p hp (toGeneric f) (order p))
    (cut : Cut (Γ := Γ) (s := s) f u order) :
    Γ.card ≤ Low6960SharedPrice.price (shape f) l cap u := by
  classical
  obtain ⟨Q, hQprop, hbox, hweight, hQ, hcontact⟩ := hproper
  have input : CutInput Γ s f Q l := ⟨hm.distinct, hm.degree, hf, hon, hl, hQprop, hbox, hweight, hcontact⟩
  let data : Data Γ s f Q l {P | Persistent Γ s P} := Low6960SharedTally.build _
  obtain ⟨a, c, d, hCard, ha, hc, hd⟩ := Low6960SharedCount.cover_counts hm input data
  let G := tally data data.branches
  let W := weighted data data.branches order
  let E := weighted data data.branches (fun p => u.split + 1 - order p)
  have hs : ∀ b ∈ data.branches, order b.surface ≤ u.split + 1 ∧
      @VanishesTo _ _ b.surface b.base.isPrime (toGeneric f) (order b.surface) := by
    intro b _
    exact horder _ _ (b.base.le (Ideal.subset_span (by simp)))
  have hsum : (u.split + 1) * G = W + E := by
    unfold G W E tally weighted
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Nat.add_mul, Nat.add_sub_of_le ((hs b hb).1)]
  let weight (p : Ideal GeoJets) := l * order p
  have hweightCharge : l * W ≤ orderCost data weight := by
    unfold W weighted orderCost weight
    rw [Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl (fun _ _ => by ring))
  have hlength : ∀ b ∈ data.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime := by
    intro b hb
    letI := b.base.isPrime
    rw [show weight b.surface = order b.surface * l by simp [weight, Nat.mul_comm]]
    exact Shared50Multiplicity.cycleLength_ge_product_of_minimal b.base
      (K1_13_6_3_6.toGeneric_ne_zero hf.1.ne_zero)
      (K1_13_7_1.proper_generic f Q hf.1 hQprop) (hs b hb).2
      (Low6960SharedPersistent.local_order (data.allowed b hb) input.box input.order)
  have hphys := Low6960SharedTallyOld.physical_bound data input cap hcap hQ weight
    hlength ha hc hd hweightCharge
  have hbase := Low6960SharedTallyOld.additive_le hl ha hc hd
  have hgap : E ≤ u.split * u.amount := deficit_bound data input u hk ht order cut
  refine hCard.trans (Nat.add_le_add_right ?_ _)
  apply le_ceil (by omega)
  calc
    (a + c + d + G) * (u.split + 1) =
        (a + c + d + W) + u.split * (a + c + d) + E := by
      calc
        _ = (a + c + d) + u.split * (a + c + d) + (u.split + 1) * G := by ring
        _ = _ := by rw [hsum]; ring
    _ ≤ Low6960Prices.physicalPrice (shape f) l cap + u.split * Low6960SharedPrice.additiveBase (shape f) l
        + u.split * u.amount := Nat.add_le_add (Nat.add_le_add hphys (Nat.mul_le_mul_left _ hbase)) hgap
    _ ≤ _ := Nat.le_add_right _ _

#print axioms tilted
#print axioms count
end
end Low6960WeightedTally

end Merged_R6960Low6960WeightedTally

end Merged_R6960Low6960WeightedTally

-- merged module R6960Low6960WeightedCut
section Merged_R6960Low6960WeightedCut

-- merged module KoalaSeparantCharge
section Merged_KoalaSeparantCharge
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 750000
namespace KoalaFarBridge
noncomputable section
open K1_13 (Row Geom shape InBox indexDegree)
open K1_13_6 (GeoJets toGeneric genericCoeffs separant cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo)
open MvPolynomial
open scoped Polynomial BigOperators
private theorem deriv_ideal_pow {k : Type*} [Field k] {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) k)) (i : Fin n) (e : ℕ)
    {F : MvPolynomial (Fin n) k} (h : F ∈ P^(e+1)) : pderiv i F ∈ P^e := by
  induction e generalizing F with
  | zero => simp
  | succ e ih =>
    rw [pow_succ] at h
    refine Submodule.mul_induction_on h ?_ ?_
    · intro x hx y hy
      rw [pderiv_mul]
      have h₁ : pderiv i x * y ∈ P^(e+1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul (ih hx) hy
      have h₂ : x * pderiv i y ∈ P^(e+1) := (P^(e+1)).mul_mem_right _ hx
      simpa only [mul_comm, add_comm] using (P^(e+1)).add_mem h₁ h₂
    · intro x y hx hy
      rw [map_add]
      exact (P^(e+1)).add_mem hx hy
theorem deriv_order {k : Type*} [Field k] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) k))
    [P.IsPrime] {F : MvPolynomial (Fin n) k} (i : Fin n) {e : ℕ}
    (h : VanishesTo P F e) : VanishesTo P (pderiv i F) (e-1) := by
  cases e with
  | zero => simp [VanishesTo]
  | succ e =>
    let L := Localization.AtPrime P
    change algebraMap _ L F ∈ IsLocalRing.maximalIdeal L ^ (e+1) at h
    change algebraMap _ L (pderiv i F) ∈ IsLocalRing.maximalIdeal L ^ e
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P L, ← Ideal.map_pow,
      IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl L] at h ⊢
    obtain ⟨u, hu, hF⟩ := h
    refine ⟨u*u, P.primeCompl.mul_mem hu hu, ?_⟩
    have hD := deriv_ideal_pow P i e hF
    have hE : u*F ∈ P^e := Ideal.pow_le_pow_right (by omega) hF
    have hM := (P^e).sub_mem ((P^e).mul_mem_left u hD) ((P^e).mul_mem_left (pderiv i u) hE)
    convert hM using 1
    rw [pderiv_mul]
    ring
theorem separant_box (f : Row 4) : InBox (shape (separant f))
    ⟨(shape f).b-1,(shape f).j-3,(shape f).t-1⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · change ((pderiv 3) f).totalDegree ≤ f.totalDegree - (1 : Fin 4 → ℕ) 3
    simpa only [weightedTotalDegree_one] using
      weightedTotalDegree_pderiv_le_sub (1 : Fin 4 → ℕ) (3 : Fin 4) f
  · change indexDegree ((pderiv 3) f) ≤ indexDegree f - (3 : Fin 4).val
    simpa only [← K1_13_1.indexDegree_eq] using
      weightedTotalDegree_pderiv_le_sub Fin.val (3 : Fin 4) f
  · exact degreeOf_pderiv_le_sub_one 3 f
theorem separant_proper {f : Row 4} (hf : f ≠ 0) (ht : 0 < f.degreeOf 3)
    (hchar : f.degreeOf 3 < K1.p) : ¬ f ∣ separant f := by
  have : CharP Geom K1.p := charP_of_injective_ringHom K1_13.embed.injective K1.p
  have : CharP (Polynomial Geom) K1.p := charP_of_injective_ringHom Polynomial.C_injective K1.p
  have hcast : (f.degreeOf 3 : (Polynomial Geom)) ≠ 0 := fun hz => (not_le_of_gt hchar)
    (Nat.le_of_dvd ht ((CharP.cast_eq_zero_iff (Polynomial Geom) K1.p _).mp hz))
  have hn : separant f ≠ 0 := pderiv_ne_zero_of_natCast_ne_zero 3 f hcast
  rintro ⟨g,hg⟩
  have hgz : g ≠ 0 := fun hz => hn (by simp [hg,hz])
  have hd := degreeOf_pderiv_le_sub_one (3 : Fin 4) f
  change (separant f).degreeOf 3 ≤ _ at hd
  rw [hg,degreeOf_mul_eq hf hgz] at hd
  omega
private theorem order_pow_mul (P : Ideal GeoJets) [P.IsPrime] {x y : GeoJets}
    {u v : ℕ} (hx : VanishesTo P x u) (hy : VanishesTo P y v) (m d : ℕ) :
    VanishesTo P (x^m * y^d) (m*u + d*v) := by
  let L := Localization.AtPrime P
  let I := IsLocalRing.maximalIdeal L
  change algebraMap _ L x ∈ I^u at hx
  change algebraMap _ L y ∈ I^v at hy
  change algebraMap _ L _ ∈ I^(m*u+d*v)
  rw [map_mul,map_pow,map_pow,pow_add,Nat.mul_comm m u,Nat.mul_comm d v,pow_mul,pow_mul]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hx _) (Ideal.pow_mem_pow hy _)
private theorem congruent_cut {f c h S : Row 4} (m d : ℕ) :
    intersectionIdeal f ((c+f*h)^m*S^d) = intersectionIdeal f (c^m*S^d) := by
  have hd : f ∣ (c+f*h)^m*S^d - c^m*S^d := by
    rw [← sub_mul]
    apply dvd_mul_of_dvd_left _
    apply dvd_trans _ (sub_dvd_pow_sub_pow _ _ _)
    simp
  obtain ⟨w,hw⟩ := hd
  have he : (c+f*h)^m*S^d = c^m*S^d + f*w := by linear_combination hw
  rw [he]
  unfold intersectionIdeal toGeneric
  simp only [map_add,map_mul]
  rw [Ideal.span_pair_comm, mul_comm (MvPolynomial.map genericCoeffs f), Ideal.span_pair_add_mul_right,Ideal.span_pair_comm]
private theorem minimal_pair {f G : Row 4} {P : Ideal GeoJets} [P.IsPrime]
    (hf : Irreducible f) (hproper : ¬f∣G) (hP : P.height=2)
    (hF : toGeneric f∈P) (hG : toGeneric G∈P) :
    (intersectionIdeal f G).IsMinimalPrime P := by
  have hsub : intersectionIdeal f G ≤ P := by
    unfold intersectionIdeal
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl|rfl
    · exact hF
    · exact hG
  obtain ⟨P',hmin,hle⟩ := Ideal.exists_minimalPrimes_le hsub
  have hzero := K1_13_6_3_6.toGeneric_ne_zero hf.ne_zero
  have hrel := K1_13_7_1.proper_generic f G hf hproper
  have hht : P'.height=2 := K1_13_6_1_2.pair_height hzero hrel hmin
  let : P'.IsPrime := hmin.isPrime
  have heq : P'=P := by
    by_contra hne
    have hs := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    rw [hht,hP] at hs
    exact (by decide : ¬(2:ℕ∞)+1≤2) hs
  exact heq ▸ hmin
private theorem mem_of_order {P : Ideal GeoJets} [P.IsPrime] {Q : GeoJets} {n : ℕ}
    (hn : 0<n) (hQ : VanishesTo P Q n) : Q∈P := by
  let L := Localization.AtPrime P
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L P _).mp
    ((Ideal.pow_le_self (Nat.ne_of_gt hn)) hQ)
theorem cut_proper {f c : Row 4} (hf : Irreducible f) (hc : ¬ f ∣ c)
    (hs : ¬ f ∣ separant f) (m d k : ℕ) : ¬ f ∣ (c^m * (separant f)^d)^k := by
  intro hd
  rcases hf.prime.dvd_or_dvd (hf.prime.dvd_of_dvd_pow hd) with h | h
  · exact hc (hf.prime.dvd_of_dvd_pow h)
  · exact hs (hf.prime.dvd_of_dvd_pow h)
theorem power_charge {f c h : Row 4} {P : Ideal GeoJets} [P.IsPrime]
    {r a e m d n w : ℕ} (hf : Irreducible f) (hc : ¬ f ∣ c) (hs : ¬ f ∣ separant f)
    (hheight : P.height = 2) (hmem : toGeneric f ∈ P)
    (hl : VanishesTo P (toGeneric f) e) (he : ¬ VanishesTo P (toGeneric f) (e+1))
    (hv : VanishesTo P (toGeneric (f^a*(c+f*h))) r)
    (hn : 0 < n*w) (hpay : n*w ≤ e*(m*(r-e*a)+d*(e-1))) {k : ℕ} (hk : 0 < k) :
    ∃ hp : (intersectionIdeal f ((c^m*(separant f)^d)^k)).IsMinimalPrime P,
      ((k*n*w : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f ((c^m*(separant f)^d)^k)) P hp.isPrime := by
  let b := (m*k)*(r-e*a)+(d*k)*(e-1)
  have hb : k*(e*(m*(r-e*a)+d*(e-1))) = e*b := by dsimp [b]; ring
  have hnk : k*n*w ≤ e*b := by simpa [← hb,Nat.mul_assoc] using Nat.mul_le_mul_left k hpay
  have hbpos : 0 < b := by
    have hh : 0 < k*n*w := by rw [Nat.mul_assoc]; exact Nat.mul_pos hk hn
    exact Nat.pos_of_mul_pos_left (hh.trans_le hnk)
  have hq : VanishesTo P (toGeneric (c+f*h)) (r-e*a) := by
    apply Shared50OrderDivision.vanishesTo_of_pow_mul P he
    simpa only [toGeneric,map_mul,map_pow] using hv
  have hd : VanishesTo P (toGeneric (separant f)) (e-1) := by
    simpa only [toGeneric,separant,pderiv_map] using deriv_order P (3 : Fin 4) hl
  have hg : VanishesTo P (toGeneric ((c+f*h)^(m*k)*(separant f)^(d*k))) b := by
    simpa only [b,toGeneric,map_pow,map_mul] using order_pow_mul P hq hd (m*k) (d*k)
  have hh : ¬ f ∣ c+f*h := by
    rintro ⟨z,hz⟩
    exact hc ⟨z-h,by linear_combination hz⟩
  have hprop := cut_proper hf hh hs (m*k) (d*k) 1
  rw [pow_one] at hprop
  have hmin := minimal_pair hf hprop hheight hmem (mem_of_order hbpos hg)
  have hlen := Shared50Multiplicity.cycleLength_ge_product hheight hl hg
  rw [mul_pow, ← pow_mul, ← pow_mul, ← congruent_cut (h := h)]
  exact ⟨hmin, le_trans (by exact_mod_cast hnk) hlen⟩
#print axioms power_charge
#print axioms separant_proper
#print axioms separant_box
end
end KoalaFarBridge

end Merged_KoalaSeparantCharge

-- merged module R6960Low6960WeightedCut
section Merged_R6960Low6960WeightedCut

set_option Elab.async false
set_option maxHeartbeats 1500000

namespace Low6960WeightedCut
noncomputable section

open K1_13 (Row Shape shape InBox)
open K1_13_6 (GeoJets toGeneric separant)
open K1_13_6_1_2 (VanishesTo)
open Low6960SharedPrice (Rate Surface surface surfaceScale weights coord)
open KoalaFarBridge (separant_box separant_proper power_charge cut_proper)
open Low6960SharedChooseCut (weighted_pow weight_coord)
open Low6960SharedCount (shape_valid)
open scoped ENat

def order (f : Row 4) (cap : ℕ) (P : Ideal GeoJets) : ℕ :=
  @Nat.findGreatest (fun e => ∃ hp : P.IsPrime, @VanishesTo _ _ P hp (toGeneric f) e)
    (Classical.decPred _) cap

theorem order_spec (f : Row 4) (cap : ℕ) (hcap : 0 < cap)
    (P : Ideal GeoJets) (hp : P.IsPrime) (hf : toGeneric f ∈ P) :
    1 ≤ order f cap P ∧ order f cap P ≤ cap ∧
      @VanishesTo _ _ P hp (toGeneric f) (order f cap P) := by
  letI := hp
  let R := Localization.AtPrime P
  have hf1 : VanishesTo P (toGeneric f) 1 := by
    change algebraMap GeoJets R (toGeneric f) ∈ IsLocalRing.maximalIdeal R ^ 1
    rw [pow_one]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R P _).mpr hf
  let P₀ := fun e => ∃ hp' : P.IsPrime, @VanishesTo _ _ P hp' (toGeneric f) e
  letI := Classical.decPred P₀
  have h₁ : 1 ≤ Nat.findGreatest P₀ cap := Nat.le_findGreatest hcap ⟨hp, hf1⟩
  have htop := Nat.findGreatest_le (P := P₀) cap
  obtain ⟨_, hh⟩ := Nat.findGreatest_of_ne_zero (P := P₀) (n := cap) rfl (by omega : Nat.findGreatest P₀ cap ≠ 0)
  exact ⟨h₁, htop, hh⟩

theorem order_exact (f : Row 4) (cap : ℕ) (P : Ideal GeoJets) [P.IsPrime]
    (hl : order f cap P < cap) : ¬ VanishesTo P (toGeneric f) (order f cap P + 1) := by
  let P₀ := fun e => ∃ hp : P.IsPrime, @VanishesTo _ _ P hp (toGeneric f) e
  letI := Classical.decPred P₀
  have h := Nat.findGreatest_is_greatest (P := P₀) (n := cap) (k := order f cap P + 1)
    (by change order f cap P < _; omega) (by omega)
  exact fun hx => h ⟨inferInstance, hx⟩

open Low6960WeightedRate (boxFee sepBox charge)

private theorem weighted_product {C T : Row 4} (hc : C ≠ 0) (ht : T ≠ 0) (m d : ℕ) (i : Fin 3) :
    coord (shape (C^m * T^d)) i = m * coord (shape C) i + d * coord (shape T) i := by
  simp only [weight_coord, MvPolynomial.weightedTotalDegree_mul _ _ _ (pow_ne_zero _ hc) (pow_ne_zero _ ht),
    weighted_pow _ hc, weighted_pow _ ht]

private theorem chamber_cost {C T : Row 4} (hc : C ≠ 0) (ht : T ≠ 0) {x y : Shape}
    (hC : InBox (shape C) x) (hT : InBox (shape T) y) (m d : ℕ) (w : Shape) :
    let q := (shape (C^m * T^d)).chamber
    w.b * q.b + w.j * q.j + w.t * q.t ≤ m * boxFee w x + d * boxFee w y := by
  let q := (shape (C^m * T^d)).chamber
  change w.b * q.b + w.j * q.j + w.t * q.t ≤ _
  have hB := weighted_product hc ht m d 0
  have hJ := weighted_product hc ht m d 1
  have hT' := weighted_product hc ht m d 2
  change (shape (C^m * T^d)).b = _ at hB
  change (shape (C^m * T^d)).j = _ at hJ
  change (shape (C^m * T^d)).t = _ at hT'
  have htC : (shape C).t ≤ min x.t (x.j / 3) := le_min hC.2.2
    (by apply (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
        have hh : 3 * (shape C).t ≤ x.j := (K1_13_7_1.shape_chamber C).2.trans hC.2.1
        rwa [Nat.mul_comm])
  have htT : (shape T).t ≤ min y.t (y.j / 3) := le_min hT.2.2
    (by apply (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
        have hh : 3 * (shape T).t ≤ y.j := (K1_13_7_1.shape_chamber T).2.trans hT.2.1
        rwa [Nat.mul_comm])
  have hb : q.b ≤ m * max x.b x.j + d * max y.b y.j := by
    change max (shape (C^m * T^d)).b (shape (C^m * T^d)).j ≤ _
    rw [hB, hJ]
    exact max_le (Nat.add_le_add (Nat.mul_le_mul_left _ (hC.1.trans (le_max_left _ _)))
      (Nat.mul_le_mul_left _ (hT.1.trans (le_max_left _ _))))
      (Nat.add_le_add (Nat.mul_le_mul_left _ (hC.2.1.trans (le_max_right _ _)))
        (Nat.mul_le_mul_left _ (hT.2.1.trans (le_max_right _ _))))
  have hj : q.j ≤ m * x.j + d * y.j := by
    change (shape (C^m * T^d)).j ≤ _
    rw [hJ]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hC.2.1) (Nat.mul_le_mul_left _ hT.2.1)
  have htq : q.t ≤ m * min x.t (x.j / 3) + d * min y.t (y.j / 3) := by
    change (shape (C^m * T^d)).t ≤ _
    rw [hT']
    exact Nat.add_le_add (Nat.mul_le_mul_left _ htC) (Nat.mul_le_mul_left _ htT)
  calc
    _ ≤ w.b * _ + w.j * _ + w.t * _ := Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hj)) (Nat.mul_le_mul_left _ htq)
    _ = _ := by unfold boxFee; ring

/-- Normalize the two powers using the joint debit, so one row pays all surface orders. -/
theorem of_contact {f C H : Row 4} (hf : Low6960Prices.SmallFactor f) (hproper : ¬ f ∣ C)
    (u : Rate) (hfit : u.kind = .tilted → Low6960Prices.tiltedFits (shape f))
    (r a d : ℕ) (x : Shape) (hC : InBox (shape C) x)
    (surfaces : Finset (Ideal GeoJets))
    (hs : ∀ p ∈ surfaces, Low6960WeightedTally.Relevant f u (order f (u.split + 1)) p)
    (hV : ∀ p (hp : p ∈ surfaces), @VanishesTo _ _ p (hs p hp).1 (toGeneric (f^a*(C+f*H))) r)
    (hM : u.split ≤ surfaceScale u.kind * (u.split * u.amount))
    (hpay : ∀ e, 1 ≤ e → e ≤ u.split → 0 < charge r a d e ∧
      (u.split + 1 - e) * (24 * boxFee (weights u.kind (shape f)) x +
        d * boxFee (weights u.kind (shape f)) (sepBox (shape f))) ≤
        (surfaceScale u.kind * (u.split * u.amount)) * charge r a d e) :
    ∃ (n : ℕ) (G : Row 4), 0 < n ∧ (¬ f ∣ G) ∧
      (∀ N > 0, ∀ p ∈ surfaces, ∃ h : (K1_13_6.intersectionIdeal f (G^N)).IsMinimalPrime p,
        ((N * n * (u.split + 1 - order f (u.split + 1) p) : ℕ) : ℕ∞) ≤
          K1_13_6.cycleLength (K1_13_6.intersectionIdeal f (G^N)) p h.isPrime) ∧
      surface u.kind (shape f) (shape G).chamber ≤ surfaceScale u.kind * (u.split * u.amount) * n := by
  let M := surfaceScale u.kind * (u.split * u.amount)
  let w := weights u.kind (shape f)
  let z := 24 * boxFee w x + d * boxFee w (sepBox (shape f))
  let n := max 1 z
  let G := C^(24*M) * (separant f)^(d*M)
  have hSep : ¬ f ∣ separant f := separant_proper hf.1.ne_zero hf.2.1
    (hf.2.2.1.2.2.trans_lt (by decide))
  have hC0 : C ≠ 0 := fun h => hproper (by simp [h])
  have hS0 : separant f ≠ 0 := fun h => hSep (by simp [h])
  refine ⟨n, G, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), ?_, ?_, ?_⟩
  · simpa only [pow_one] using cut_proper hf.1 hproper hSep (24*M) (d*M) 1
  · intro N hN p hp
    have hP := hs p hp
    letI := hP.1
    let e := order f (u.split+1) p
    have hs' := order_spec f (u.split + 1) (by omega) p hP.1 hP.2.2.1
    have he : e ≤ u.split := hP.2.2.2
    have he' := order_exact f (u.split + 1) p (show e < u.split + 1 by omega)
    obtain ⟨hpos, hineq⟩ := hpay e hs'.1 he
    let v := u.split+1-e
    have hnp : 0 < n*v := Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) (by dsimp [v]; omega)
    have hscaled : n*v ≤ M*charge r a d e := by
      by_cases hz : z = 0
      · unfold n
        rw [hz, max_eq_left (by decide : 0 ≤ 1), one_mul]
        exact (show v ≤ u.split by dsimp [v]; omega).trans
          (hM.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left M hpos))
      · rw [show n = z from max_eq_right (Nat.pos_of_ne_zero hz), Nat.mul_comm z v]
        exact hineq
    have hfinal : n*v ≤ e*((24*M)*(r-e*a)+(d*M)*(e-1)) :=
      hscaled.trans (show M*charge r a d e ≤ _ by unfold charge; apply le_of_eq; ring)
    exact power_charge hf.1 hproper hSep hP.2.1 hP.2.2.1 hs'.2.2 he' (hV p hp) hnp hfinal hN
  · have hbound := chamber_cost hC0 hS0 hC (separant_box f) (24*M) (d*M) w
    have hlin : surface u.kind (shape f) (shape G).chamber =
        w.b * (shape G).chamber.b + w.j * (shape G).chamber.j + w.t * (shape G).chamber.t := by
      cases hu : u.kind with
      | ordinary => simpa only [w, hu] using Low6960SharedPrice.surface_ordinary_eq_weights (shape_valid hf) (shape G).chamber
      | tilted => simpa only [w, hu] using (Low6960SharedPrice.surface_tilted_eq_weights
          (shape_valid hf) (hfit hu) (shape G).chamber)
    rw [hlin]
    calc
      _ ≤ (24*M)*boxFee w x + (d*M)*boxFee w (sepBox (shape f)) := hbound
      _ = M*z := by unfold z; ring
      _ ≤ M*n := Nat.mul_le_mul_left _ (le_max_right _ _)

#print axioms of_contact
end
end Low6960WeightedCut

end Merged_R6960Low6960WeightedCut

end Merged_R6960Low6960WeightedCut

end Merged6967_R6960Low6960WeightedCut

section Merged6967_R6960TerminalSmall
set_option Elab.async false






set_option Elab.async false

-- merged module KoalaNodeTranslation
section Merged_KoalaNodeTranslation

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SplitCut.StableNode
noncomputable section
open Polynomial






end
end SplitCut.StableNode


end Merged_KoalaNodeTranslation

-- merged module KoalaCompressedEquation
section Merged_KoalaCompressedEquation

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace SplitCut.Compression
noncomputable section

open BoxDegree
open scoped Polynomial

variable {F : Type*} [Field F]

abbrev SeedPoly (F : Type*) [CommRing F] := MvPolynomial (Fin 2) F
abbrev FreshEquation (F : Type*) [CommRing F] := Polynomial (Polynomial (SeedPoly F))

def pack {e v w : ℕ} (W : exps e v w → (Polynomial F)) : FreshEquation F :=
  ∑ m : exps e v w,
    (W m).map (Polynomial.C.comp MvPolynomial.C) *
      Polynomial.C (Polynomial.monomial (m.val none) (MvPolynomial.monomial m.val.some 1))

theorem pack_coeff {e v w : ℕ} (W : exps e v w → (Polynomial F)) (i j : ℕ) :
    ((pack W).coeff i).coeff j =
      ∑ m : exps e v w, if m.val none = j then MvPolynomial.monomial m.val.some ((W m).coeff i) else 0 := by
  classical
  rw [pack, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m _
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_map, RingHom.comp_apply, Polynomial.coeff_C_mul,
    Polynomial.coeff_monomial]
  by_cases h : m.val none = j
  · simp [h, MvPolynomial.C_mul_monomial]
  · simp [h, Ne.symm h]

theorem pack_recover {e v w : ℕ} (W : exps e v w → (Polynomial F)) (m : exps e v w) (i : ℕ) :
    (((pack W).coeff i).coeff (m.val none)).coeff m.val.some = (W m).coeff i := by
  classical
  rw [pack_coeff, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single m]
  · simp [MvPolynomial.coeff_monomial]
  · intro n _ hn
    by_cases h : n.val none = m.val none
    · have hs : n.val.some ≠ m.val.some := by
        intro he
        apply hn
        apply Subtype.ext
        ext j
        cases j with
        | none => exact h
        | some k => exact DFunLike.congr_fun he k
      simp [h, MvPolynomial.coeff_monomial, hs, Ne.symm hs]
    · simp [h]
  · intro h
    exact (h (Finset.mem_univ m)).elim

theorem pack_ne_zero {e v w : ℕ} {W : exps e v w → (Polynomial F)} (hW : W ≠ 0) : pack W ≠ 0 := by
  intro h
  apply hW
  funext m
  apply Polynomial.ext
  intro i
  rw [← pack_recover W m, h]
  simp

theorem pack_x_bound {e v w b : ℕ} (W : exps e v w → (Polynomial F))
    (hW : ∀ m, (W m).natDegree ≤ b) : (pack W).natDegree ≤ b := by
  unfold pack
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _
  exact Polynomial.natDegree_mul_le.trans (by
    rw [Polynomial.natDegree_C, add_zero]
    exact Polynomial.natDegree_map_le.trans (hW m))

theorem pack_y_bound {e v w : ℕ} (W : exps e v w → (Polynomial F)) (i : ℕ) :
    ((pack W).coeff i).natDegree ≤ e := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [pack_coeff]
  apply Finset.sum_eq_zero
  intro m _
  simp [show m.val none ≠ j from ne_of_lt (m.property.1.trans_lt hj)]

theorem pack_seed_bound {e v w : ℕ} (W : exps e v w → (Polynomial F)) (i j : ℕ) (a : Fin 2) :
    (((pack W).coeff i).coeff j).degreeOf a ≤ (![v,w] : Fin 2 → ℕ) a := by
  classical
  rw [pack_coeff]
  refine (MvPolynomial.degreeOf_sum_le a _ _).trans (Finset.sup_le ?_)
  intro m _
  split_ifs
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro n hn
    obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hn)
    fin_cases a
    · exact m.property.2.1
    · exact m.property.2.2
  · simp

theorem pack_substitute {A : Type*} [CommRing A] (ι : F →+* A) (z : Fin 2 → A) (S : (Polynomial A))
    {e v w : ℕ} (W : exps e v w → (Polynomial F)) :
    StableNode.substitute S ((pack W).map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom ι z))) =
      ∑ m : exps e v w, (W m).map ι *
        (S^m.val none * Polynomial.C (z 0^m.val (some 0) * z 1^m.val (some 1))) := by
  rw [pack, Polynomial.map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Polynomial.map_mul, Polynomial.map_C, map_mul]
  congr 1
  · rw [Polynomial.map_map]
    change ((W m).map _).eval₂
      (Polynomial.eval₂RingHom Polynomial.C S) (Polynomial.X : (Polynomial A)) = _
    rw [Polynomial.eval₂_map]
    rw [show ((Polynomial.eval₂RingHom Polynomial.C S).comp
      (((Polynomial.mapRingHom (MvPolynomial.eval₂Hom ι z))).comp
        (Polynomial.C.comp MvPolynomial.C))) = Polynomial.C.comp ι by
          apply RingHom.ext
          intro q
          simp [Polynomial.map_C]]
    rw [← Polynomial.eval₂_map, Polynomial.eval₂_C_X]
  · simp only [StableNode.substitute, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.coe_mapRingHom]
    change ((Polynomial.monomial (m.val none) (MvPolynomial.monomial m.val.some 1)).map
        (MvPolynomial.eval₂Hom ι z)).eval₂ Polynomial.C S = _
    rw [Polynomial.map_monomial, Polynomial.eval₂_monomial, MvPolynomial.eval₂Hom_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two, map_one, one_mul]
    exact mul_comm _ _

theorem compressed_polynomial {α : Type*} [Finite α] (S : α → (Polynomial F)) (z : α → Fin 2 → F)
    {f : MvPolynomial Idx (Rational F)} (hf : f ≠ 0) {e v w b d p : ℕ}
    (hfit : f ∈ space (Rational F) e v w) (hS : ∀ g, (S g).natDegree ≤ d)
    (hroot : ∀ g, MvPolynomial.eval (fun i : Idx => i.elim (algebraMap (Polynomial F) (Rational F) (S g))
      (fun j => algebraMap (Polynomial F) (Rational F) (Polynomial.C (z g j)))) f = 0)
    (hguard : Fintype.card (exps e (v+b) (w+b))*(e*d) < ((b+1)*(b+1))*p)
    (hp : e*d < p) :
    ∃ G : FreshEquation F, G ≠ 0 ∧ G.natDegree + e*d < p ∧
      (∀ i, (G.coeff i).natDegree ≤ e) ∧
      (∀ i j, (((G.coeff i).coeff j).degreeOf 0 ≤ v+b) ∧ (((G.coeff i).coeff j).degreeOf 1 ≤ w+b)) ∧
      (∀ g, StableNode.substitute (S g)
        (G.map (Polynomial.mapRingHom (MvPolynomial.eval (z g)))) = 0) := by
  classical
  obtain ⟨W, hW, hWzero⟩ := compress_box S z hf hfit hS hroot hguard
  let U : exps e (v+b) (w+b) → (Polynomial F) := fun m => W m
  have hU : U ≠ 0 := by
    intro h
    apply hW
    funext m
    exact Subtype.ext (congrFun h m)
  have hdeg (m : exps e (v+b) (w+b)) : (U m).natDegree ≤ p-e*d-1 := by
    by_cases hz : U m = 0
    · simp [hz]
    · have h := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
        (Polynomial.mem_degreeLT.mp (W m).property)
      omega
  refine ⟨pack U, pack_ne_zero hU, ?_, pack_y_bound U, ?_, ?_⟩
  · have h := pack_x_bound U hdeg
    omega
  · intro i j
    exact ⟨pack_seed_bound U i j 0, pack_seed_bound U i j 1⟩
  · intro g
    rw [show MvPolynomial.eval (z g) = MvPolynomial.eval₂Hom (RingHom.id F) (z g) from rfl,
      pack_substitute]
    simp only [Polynomial.map_id]
    simpa only [evalRow, U, mul_comm] using hWzero g

end
end SplitCut.Compression

#print axioms SplitCut.Compression.compressed_polynomial

end Merged_KoalaCompressedEquation

-- merged module R6960QuadraticCount
section Merged_R6960QuadraticCount
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
namespace Lower6960
open Polynomial CurvatureSquares K1_14 RetainedShortening CurvatureVotes
open SplitCut.Compression
open scoped Polynomial Classical
private abbrev onSeeds := (K1_10.frobeniusGraph (F := L) K1.p).toRingHom
private def project : FreshEquation L →+* Ordinate :=
  Bivariate.swap.toRingHom.comp (mapRingHom (mapRingHom onSeeds))
private theorem project_coeff (G : FreshEquation L) (i j : ℕ) :
    ((project G).coeff j).coeff i = onSeeds ((G.coeff i).coeff j) := by
  change ((Bivariate.swap _).coeff j).coeff i = _
  rw [coeff_swap]
  simp
private theorem project_ne {G : FreshEquation L} (ne : G≠0)
    (cap : ∀ i j, ((G.coeff i).coeff j).degreeOf 0 < K1.p) : project G≠0 := by
  intro bad
  apply ne
  apply Polynomial.ext
  intro i
  apply Polynomial.ext
  intro j
  by_contra h
  have hzero := project_coeff G i j
  rw [bad] at hzero
  exact K1_10.frobeniusGraph_ne_zero _ (by decide) _ (by simpa using h) (cap i j)
    (by simpa using hzero.symm)
private theorem project_x (G : FreshEquation L) : (xView (project G)).natDegree ≤ G.natDegree := by
  change (Bivariate.swap (Bivariate.swap _)).natDegree ≤ _
  rw [Bivariate.swap_swap_apply]
  exact natDegree_map_le
private theorem project_y {G : FreshEquation L} {e : ℕ} (cap : ∀ i, (G.coeff i).natDegree≤e) :
    (project G).natDegree≤e := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  ext i
  rw [project_coeff,coeff_eq_zero_of_natDegree_lt ((cap i).trans_lt hj)]
  simp
private theorem project_z {G : FreshEquation L} {v w : ℕ}
    (axes : ∀ i j, ((G.coeff i).coeff j).degreeOf 0≤v ∧ ((G.coeff i).coeff j).degreeOf 1≤w) :
    (zView (project G)).natDegree ≤ v+K1.p*w := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  ext j i
  change (((Bivariate.swap ((project G).map Bivariate.swap.toRingHom)).coeff n).coeff j).coeff i = _
  rw [coeff_swap,coeff_map]
  change ((Bivariate.swap ((project G).coeff j)).coeff n).coeff i = _
  rw [coeff_swap,project_coeff]
  simpa using coeff_eq_zero_of_natDegree_lt
    ((K1_10.frobeniusGraph_degree _ _ _ _ (axes i j).1 (axes i j).2).trans_lt hn)
private theorem cover_root (P : Ordinate) (ne : P≠0) {z : L} {S : (Polynomial L)}
    (hit : ordEval z S P=0) :
    ∃ f : Ordinate, Irreducible f ∧ f∣P ∧ f.natDegree≤P.natDegree ∧ ordEval z S f=0 := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (ne rfl).elim
  | unit u hu => exact ((hu.map (ordEval z S)).ne_zero hit).elim
  | mul q f hq hf ih =>
    rw [map_mul,mul_eq_zero] at hit
    rcases hit with h|h
    · exact ⟨f,hf,dvd_mul_right ..,natDegree_le_of_dvd (dvd_mul_right ..) ne,h⟩
    · obtain ⟨g,hg,dv,_,zr⟩ := ih hq h
      have dv' : g∣f*q := dv.trans (show q∣f*q from ⟨f,by rw [mul_comm f q]⟩)
      exact ⟨g,hg,dv',natDegree_le_of_dvd dv' ne,zr⟩
private theorem eval_project (G : FreshEquation L) (z : L) (S : (Polynomial L)) :
    ordEval z S (project G) = SplitCut.StableNode.substitute S
      (G.map (mapRingHom (MvPolynomial.eval ![z,z^K1.p]))) := by
  let left := (ordEval z S).comp project
  let right := (SplitCut.StableNode.substitute S).comp
    (mapRingHom (mapRingHom (MvPolynomial.eval ![z,z^K1.p])))
  have eq : left=right := by
    apply Polynomial.ringHom_ext
    · intro a
      suffices h : left.comp C = right.comp C from RingHom.congr_fun h a
      apply Polynomial.ringHom_ext
      · intro b
        suffices h : (left.comp C).comp C = (right.comp C).comp C from RingHom.congr_fun h b
        apply MvPolynomial.ringHom_ext
        · intro a
          simp [left,right,project,ordEval,SplitCut.StableNode.substitute,onSeeds,
            K1_10.frobeniusGraph,Bivariate.swap_C_C]
        · intro i
          fin_cases i <;> simp [left,right,project,ordEval,SplitCut.StableNode.substitute,
            onSeeds,K1_10.frobeniusGraph,Bivariate.swap_C_C,Polynomial.eval₂_pow]
      · simp [left,right,project,ordEval,SplitCut.StableNode.substitute,Bivariate.swap_X]
    · simp [left,right,project,ordEval,SplitCut.StableNode.substitute,Bivariate.swap_Y]
  exact DFunLike.congr_fun eq G
theorem small_ordinate_count_at_scale {A d k w s T} (W : Word A d w s T)
    (label : K1.K → K1.K) (inj : Set.InjOn label (T : Set K1.K))
    (hd : d<A) (scale : VoteScale A d k)
    (f : Equation) (ne : f≠0) (degree : f.natDegree≤2) {v u b : ℕ}
    (axes : ∀ i, (f.coeff i).degreeOf 0≤v ∧ (f.coeff i).degreeOf 1≤u)
    (small : v+b<K1.p)
    (guard : 3*(v+b+1)*(u+b+1)*(2*d)<(b+1)*(b+1)*(K1.p/2))
    (width : 2*d<K1.p/2)
    (marks : ∀ γ∈T, atMark f (label γ) (s γ)=0) :
    T.card≤max 8 k*((v+b)+K1.p*(u+b))+4 := by
  classical
  let φ := algebraMap K1.K L
  let z (g : K1.K) := φ (label g)
  let S (g : ↥T) := liftPoly (s g)
  let pair (g : ↥T) : Fin 2 → L := ![z g,(z g)^K1.p]
  let f' := K1_14_6_1.flatten f
  have hn : f'≠0 := by
    intro h
    exact ne ((MvPolynomial.optionEquivLeft FX (Fin 2)).symm.injective (h.trans (map_zero _).symm))
  have box : f' ∈ SplitCut.BoxDegree.space FX 2 v u := by
    intro m hm
    change m ∈ f'.support at hm
    have hc : m.some ∈ (f.coeff (m none)).support := by
      rw [MvPolynomial.mem_support_iff] at hm ⊢
      have h := MvPolynomial.optionEquivLeft_coeff_coeff FX f' (m none) m.some
      simp only [f',K1_14_6_1.flatten,AlgEquiv.apply_symm_apply,Finsupp.optionElim_some] at h
      exact h.trans_ne hm
    have hne : f.coeff (m none) ≠ 0 := by intro h; simp [h] at hc
    exact ⟨(Polynomial.le_natDegree_of_ne_zero hne).trans degree,
      (MvPolynomial.le_degreeOf_of_mem_support 0 hc).trans (axes _).1,
      (MvPolynomial.le_degreeOf_of_mem_support 1 hc).trans (axes _).2⟩
  have hit (g : ↥T) : MvPolynomial.eval (fun i : Option (Fin 2) => i.elim
      (algebraMap (Polynomial L) FX (S g)) (fun j => algebraMap (Polynomial L) FX (C (pair g j)))) f'=0 := by
    have eq : (fun i : Option (Fin 2) => i.elim (algebraMap (Polynomial L) FX (S g))
      (fun j => algebraMap (Polynomial L) FX (C (pair g j)))) = K1_14_6.rootPoint (label g) (s g) := by
      funext i
      cases i with
      | none => rfl
      | some j => fin_cases j <;> simp [K1_14_6.rootPoint,pair,z,φ,seedEmbedding]
    rw [eq]
    exact (K1_14_6_1.eval_flatten ..).trans (marks _ g.property)
  have hguard : Fintype.card (SplitCut.BoxDegree.exps 2 (v+b) (u+b)) * (2*d) <
      ((b+1)*(b+1))*(K1.p/2) := by
    rw [Fintype.card_congr (SplitCut.BoxDegree.slots _ _ _),Fintype.card_prod,
      Fintype.card_prod,Fintype.card_fin,Fintype.card_fin,Fintype.card_fin]
    simpa only [Nat.mul_assoc] using guard
  obtain ⟨G,ng,wx,wy,wz,atWords⟩ := compressed_polynomial S pair hn box
    (fun g => Polynomial.natDegree_map_le.trans (W.degree _ g.property)) hit hguard width
  let P := project G
  have pn : P≠0 := project_ne ng (fun i j => ((wz i j).1).trans_lt small)
  have tame : 2*(xView P).natDegree<K1.p := by have := project_x G; dsimp [P]; omega
  have dy := project_y wy
  have hz_inj : Set.InjOn z (T:Set K1.K) := fun _ h _ h' eq => inj h h' (φ.injective eq)
  have count := projected_low_count W φ z hz_inj hd scale P pn tame
    (fun γ mem => by
      have hz := (eval_project G (z γ) ((s γ).map φ)).trans (atWords ⟨γ,mem⟩)
      obtain ⟨q,irr,dv,deg,root⟩ := cover_root P pn hz
      exact ⟨q,irr,dv,deg.trans dy,root⟩)
  have dz := project_z wz
  exact count.trans (Nat.add_le_add (Nat.mul_le_mul_left _ dz) (Nat.mul_le_mul_left 2 dy))
theorem small_ordinate_count {A d w s T} (W : Word A d w s T)
    (label : K1.K → K1.K) (inj : Set.InjOn label (T : Set K1.K))
    (hd : d<A) (scale : VoteScale A d 5)
    (f : Equation) (ne : f≠0) (degree : f.natDegree≤2) {v u b : ℕ}
    (axes : ∀ i, (f.coeff i).degreeOf 0≤v ∧ (f.coeff i).degreeOf 1≤u)
    (small : v+b<K1.p)
    (guard : 3*(v+b+1)*(u+b+1)*(2*d)<(b+1)*(b+1)*(K1.p/2))
    (width : 2*d<K1.p/2)
    (marks : ∀ γ∈T, atMark f (label γ) (s γ)=0) :
    T.card≤8*((v+b)+K1.p*(u+b))+4 :=
  small_ordinate_count_at_scale W label inj hd scale f ne degree axes small guard width marks
theorem first_band_small_ordinate {w s T} (W : Word 179818 133606 w s T)
    (label : K1.K → K1.K) (inj : Set.InjOn label (T : Set K1.K))
    (f : Equation) (ne : f≠0) (degree : f.natDegree≤2)
    (axes : ∀ i, (f.coeff i).degreeOf 0≤2400 ∧ (f.coeff i).degreeOf 1≤2400)
    (marks : ∀ γ∈T, atMark f (label γ) (s γ)=0) :
    T.card≤43091406921220 := by
  have h := small_ordinate_count (v:=2400) (u:=2400) (b:=128) W label inj
    (by decide) (Or.inr (by decide)) f ne degree axes (by decide) (by decide) (by decide) marks
  exact h.trans (by decide)
#print axioms first_band_small_ordinate
abbrev axis (f : Equation) (i : Fin 2) := (K1_14_6_1.flatten f).degreeOf (some i)
private theorem axis_mul {f g : Equation} (hf : f≠0) (hg : g≠0) (i : Fin 2) :
    axis (f*g) i=axis f i+axis g i := by
  unfold axis K1_14_6_1.flatten
  rw [map_mul,MvPolynomial.degreeOf_mul_eq (by simpa using hf) (by simpa using hg)]
private theorem coeff_axis (f : Equation) (i : Fin 2) (j : ℕ) :
    (f.coeff j).degreeOf i≤axis f i := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  let n := m.optionElim j
  have hi : n ∈ (K1_14_6_1.flatten f).support := by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    have h := MvPolynomial.optionEquivLeft_coeff_coeff FX (K1_14_6_1.flatten f) j m
    simp only [K1_14_6_1.flatten,AlgEquiv.apply_symm_apply] at h
    exact h ▸ hm
  simpa [n,axis] using MvPolynomial.le_degreeOf_of_mem_support (some i) hi
private def lowFee (f : Equation) : ℕ :=
  8*(axis f 0+K1.p*axis f 1)+(8*128*(K1.p+1)+4)*f.natDegree
theorem low_component_count {w s T} (W : Word 179818 133606 w s T)
    (label : K1.K → K1.K) (inj : Set.InjOn label (T : Set K1.K)) (f : Equation) :
    f≠0 → (∀ i, axis f i≤2400) →
    (∀ γ∈T, ∃ q : Equation, Irreducible q ∧ q∣f ∧ 0<q.natDegree ∧ q.natDegree≤2 ∧
      atMark q (label γ) (s γ)=0) → T.card≤lowFee f := by
  classical
  induction f using WfDvdMonoid.induction_on_irreducible generalizing T with
  | zero => simp
  | unit f unit =>
    intro _ _ cover
    have empty : T=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro γ mem
      obtain ⟨q,hq,dv,_⟩ := cover γ mem
      exact hq.not_isUnit (isUnit_of_dvd_unit dv unit)
    simp [empty]
  | mul g q ng irr ih =>
    intro ne caps cover
    let U := T.filter (fun γ => ∃ l : Equation, Irreducible l ∧ l∣g ∧ 0<l.natDegree ∧
      l.natDegree≤2 ∧ atMark l (label γ) (s γ)=0)
    let V := T \ U
    have us : U⊆T := Finset.filter_subset _ _
    have vs : V⊆T := Finset.sdiff_subset
    have subword (R) (sub : R⊆T) : Word 179818 133606 w s R :=
      ⟨W.distinct.mono sub,fun γ h => W.degree _ (sub h),fun γ h => W.hits _ (sub h)⟩
    have ax (i : Fin 2) := axis_mul irr.ne_zero ng i
    have upper (i : Fin 2) : axis q i+axis g i≤2400 := (ax i) ▸ caps i
    have uc := ih (subword U us) (inj.mono us) ng (fun i => (Nat.le_add_left ..).trans (upper i))
      (fun γ h => (Finset.mem_filter.mp h).2)
    have rest (γ) (h : γ∈V) : 0<q.natDegree ∧ q.natDegree≤2 ∧ atMark q (label γ) (s γ)=0 := by
      obtain ⟨l,hl,dv,pos,deg,zr⟩ := cover γ (vs h)
      have dl : l∣q := ((UniqueFactorizationMonoid.irreducible_iff_prime.mp hl).dvd_mul.mp dv).resolve_right
        (fun u => (Finset.mem_sdiff.mp h).2 (Finset.mem_filter.mpr ⟨vs h,l,hl,u,pos,deg,zr⟩))
      have assoc := hl.associated_of_dvd irr dl
      refine ⟨pos.trans_le (natDegree_le_of_dvd dl irr.ne_zero),
        (natDegree_le_of_dvd assoc.symm.dvd hl.ne_zero).trans deg,?_⟩
      obtain ⟨b,hb⟩ := dl
      change eval₂ (graphEval (label γ)) (atX (s γ)) l=0 at zr
      rw [hb,atMark,eval₂_mul,zr,zero_mul]
    have vc : V.card≤lowFee q := by
      obtain em|⟨γ,hm⟩ := V.eq_empty_or_nonempty
      · simp [em]
      have hq (i : Fin 2) : axis q i≤2400 := (Nat.le_add_right ..).trans (upper i)
      have fit := small_ordinate_count (b:=128) (subword V vs) label (inj.mono vs)
        (by decide) (Or.inr (by decide)) q irr.ne_zero (rest γ hm).2.1
        (fun j => ⟨coeff_axis q 0 j,coeff_axis q 1 j⟩)
        (by have := hq 0; change _<2130706433; omega)
        (by exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left 3
          (Nat.add_le_add_right (Nat.add_le_add_right (hq 0) 128) 1))
          (Nat.add_le_add_right (Nat.add_le_add_right (hq 1) 128) 1))).trans_lt (by decide))
        (by decide) (fun a h => (rest a h).2.2)
      apply fit.trans
      unfold lowFee
      have pos := (rest γ hm).1
      change _ ≤ 8 * (axis q 0 + 2130706433 * axis q 1) + (8*128*(2130706433+1)+4)*q.natDegree
      change 8*(axis q 0+128+2130706433*(axis q 1+128))+4 ≤ _
      omega
    have card := Finset.card_sdiff_add_card_eq_card us
    change V.card+U.card=T.card at card
    rw [←card]
    apply (Nat.add_le_add vc uc).trans
    unfold lowFee
    rw [ax 0,ax 1,natDegree_mul irr.ne_zero ng]
    exact le_of_eq (by ring)
#print axioms low_component_count
def smallMarks (T : Finset K1.K) (label : K1.K → K1.K) (s : K1.K → (Polynomial K1.K)) (f : Equation) :
    Finset K1.K := T.filter (fun γ => ∃ q : Equation, Irreducible q ∧ q∣f ∧
      0<q.natDegree ∧ q.natDegree≤2 ∧ atMark q (label γ) (s γ)=0)
theorem small_marks_at_first_band {w s T} (W : Word 179818 133606 w s T)
    (label : K1.K → K1.K) (inj : Set.InjOn label (T : Set K1.K))
    (f : Equation) (ne : f≠0) (degree : f.natDegree≤47) (caps : ∀ i, axis f i≤2400) :
    (smallMarks T label s f).card≤8*((2400+47*128)+K1.p*(2400+47*128))+4*47 := by
  let U:=smallMarks T label s f
  have sub : U⊆T := Finset.filter_subset _ _
  have word : Word 179818 133606 w s U :=
    ⟨W.distinct.mono sub,fun γ h => W.degree _ (sub h),fun γ h => W.hits _ (sub h)⟩
  have h:=low_component_count word label (inj.mono sub) f ne caps
    (fun γ h => (Finset.mem_filter.mp h).2)
  apply h.trans
  unfold lowFee
  calc
    _ ≤ 8*(2400+K1.p*2400)+(8*128*(K1.p+1)+4)*47 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add (caps 0) (Nat.mul_le_mul_left _ (caps 1))))
        (Nat.mul_le_mul_left _ degree)
    _ = _ := by ring
#print axioms small_marks_at_first_band
end Lower6960

end
end Merged_R6960QuadraticCount

-- merged module R6960TerminalSmall
section Merged_R6960TerminalSmall
noncomputable section
set_option Elab.async false
namespace Lower6960.TerminalSmall
open Polynomial Finset
open K1 (K)
open K1_14 (Equation atMark atX graphEval)
open RetainedShortening (Word)
open KoalaRect (axisDegree axisDegree_le_iff axisDegree_mul)
open RescueGeometry (Model Family)
def fee (f : Equation) : ℕ :=
  18*(axisDegree f 0+K1.p*axisDegree f 1)+(K1.p+1)*(axisDegree f 0+axisDegree f 1)+4*f.natDegree
private theorem one {w s T} (W : Word 179818 164650 w s T)
    (label : K→K) (inj : Set.InjOn label (T:Set K)) (q : Equation)
    (nq : q≠0) (pos : 0<q.natDegree) (dy : q.natDegree≤2)
    (cap : axisDegree q 0+axisDegree q 1≤2400)
    (roots : ∀ γ∈T,atMark q (label γ) (s γ)=0) : T.card≤fee q := by
  let v:=axisDegree q 0
  let u:=axisDegree q 1
  let b:=(v+u)/18
  have vmax : v+b+1≤19*(b+1) := by dsimp [b]; omega
  have umax : u+b+1≤19*(b+1) := by dsimp [b]; omega
  have shape : 3*(v+b+1)*(u+b+1)*(2*164650) < (b+1)*(b+1)*(K1.p/2) := by
    calc _ ≤ 3*(19*(b+1))*(19*(b+1))*(2*164650) := by gcongr
         _ = (b+1)*(b+1)*(3*19*19*(2*164650)) := by ring
         _ < _ := Nat.mul_lt_mul_of_pos_left (by decide) (by positivity)
  have sz : v+u≤2400 := cap
  have charge := small_ordinate_count_at_scale (k:=18) (b:=b) W label inj (by decide)
    (Or.inl (by decide)) q nq dy
    (fun i=>⟨(axisDegree_le_iff q 0 _).mp le_rfl i,(axisDegree_le_iff q 1 _).mp le_rfl i⟩)
    (by change v+b<2130706433; dsimp [b]; omega) shape (by decide) roots
  have hb : 18*b≤v+u := by dsimp [b]; omega
  have hpay := Nat.mul_le_mul_left (K1.p+1) hb
  change T.card≤18*(v+b+K1.p*(u+b))+4 at charge
  change T.card≤18*(v+K1.p*u)+(K1.p+1)*(v+u)+4*q.natDegree
  calc _ ≤ _ := charge
       _ = 18*(v+K1.p*u)+(K1.p+1)*(18*b)+4 := by ring
       _ ≤ _ := by omega
theorem covered {w s T} (W : Word 179818 164650 w s T) (label : K→K)
    (inj : Set.InjOn label (T:Set K)) (f : Equation) :
    f≠0 → axisDegree f 0+axisDegree f 1≤2400 →
    (∀ γ∈T,∃ q : Equation,Irreducible q ∧ q∣f ∧ 0<q.natDegree ∧ q.natDegree≤2 ∧
      atMark q (label γ) (s γ)=0) → T.card≤fee f := by
  classical
  induction f using WfDvdMonoid.induction_on_irreducible generalizing T with
  | zero => simp
  | unit f hu =>
    intro _ _ cover
    have empty : T=∅ := eq_empty_iff_forall_notMem.mpr (fun γ h=>by
      obtain ⟨q,ir,dv,_⟩ := cover γ h
      exact ir.not_isUnit (isUnit_of_dvd_unit dv hu))
    simp [empty]
  | mul g q ng ir ih =>
    intro nz cap cover
    let U:=smallMarks T label s g
    let V:=T\U
    have us : U⊆T := filter_subset _ _
    have vs : V⊆T := sdiff_subset
    have word (R) (sub : R⊆T) : Word 179818 164650 w s R :=
      ⟨W.distinct.mono sub, fun γ h=>W.degree γ (sub h),fun γ h=>W.hits γ (sub h)⟩
    have a0 := axisDegree_mul ir.ne_zero ng 0
    have a1 := axisDegree_mul ir.ne_zero ng 1
    have ca := ih (word U us) (inj.mono us) ng (by omega) (fun γ h=>(mem_filter.mp h).2)
    have rest (γ) (h : γ∈V) : 0<q.natDegree ∧ q.natDegree≤2 ∧ atMark q (label γ) (s γ)=0 := by
      obtain ⟨l,il,dv,pos,dg,zr⟩ := cover γ (vs h)
      have dl : l∣q := (il.prime.dvd_mul.mp dv).resolve_right
        (fun d=>(mem_sdiff.mp h).2 (mem_filter.mpr ⟨vs h,l,il,d,pos,dg,zr⟩))
      have asso:=il.associated_of_dvd ir dl
      refine ⟨pos.trans_le (natDegree_le_of_dvd dl ir.ne_zero),
        (natDegree_le_of_dvd asso.symm.dvd il.ne_zero).trans dg,?_⟩
      obtain ⟨a,eq⟩ := dl
      change eval₂ (graphEval (label γ)) (atX (s γ)) l=0 at zr
      rw [eq,atMark,eval₂_mul,zr,zero_mul]
    have cb : V.card≤fee q := by
      rcases V.eq_empty_or_nonempty with empty | ⟨γ,hγ⟩
      · simp [empty]
      exact one (word V vs) label (inj.mono vs) q ir.ne_zero (rest γ hγ).1 (rest γ hγ).2.1
        (by omega) (fun t ht=>(rest t ht).2.2)
    have card : V.card+U.card=T.card := card_sdiff_add_card_eq_card us
    calc T.card = V.card+U.card := card.symm
         _ ≤ fee q+fee g := Nat.add_le_add cb ca
         _ = _ := by unfold fee; rw [a0,a1,natDegree_mul ir.ne_zero ng]; ring
def smallCap : ℕ := (19*K1.p+1)*2400+4*47
theorem small_marks {w s T} (W : Word 179818 164650 w s T) (label : K→K)
    (inj : Set.InjOn label (T:Set K)) {f : Equation} (ne : f≠0) (deg : f.natDegree<48)
    (axes : axisDegree f 0+axisDegree f 1≤2400) :
    (smallMarks T label s f).card≤smallCap := by
  classical
  let U:=smallMarks T label s f
  have sub : U⊆T := filter_subset _ _
  have word : Word 179818 164650 w s U :=
    ⟨W.distinct.mono sub,fun γ h=>W.degree γ (sub h),fun γ h=>W.hits γ (sub h)⟩
  have paid:=covered word label (inj.mono sub) f ne axes (fun γ h=>(mem_filter.mp h).2)
  refine paid.trans ?_
  unfold fee smallCap
  change 18*(_+2130706433*_)+2130706434*(_+_)+4*_ ≤ (19*2130706433+1)*2400+4*47
  omega
#print axioms small_marks
private theorem root_factor {f : Equation} (nf : f≠0) (z : K) (S : (Polynomial K))
    (root : atMark f z S=0) : ∃ q : Equation,Irreducible q ∧ q∣f ∧ atMark q z S=0 := by
  let ev := eval₂RingHom (graphEval z) (atX S)
  change ev f=0 at root
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (nf rfl).elim
  | unit u hu => exact ((hu.map ev).ne_zero root).elim
  | mul g q ng ir ih =>
    rw [map_mul,mul_eq_zero] at root
    rcases root with r | r
    · exact ⟨q,ir,dvd_mul_right ..,r⟩
    · obtain ⟨a,ia,dv,hit⟩ := ih ng r
      exact ⟨a,ia,dv.trans (dvd_mul_left ..),hit⟩
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open TerminalReceipts (witness)
theorem higher_remainder {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2359≤M.overhead.toNat)
    (hi : M.overhead.toNat≤33579) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Γ.card≤MainGeometry.prefixCap ∨
      ∃ (T : Finset K) (f : Equation), T⊆Γ ∧ Γ.card≤MainGeometry.prefixCap+smallCap+T.card ∧
        f.IsPrimitive ∧ (f.map (algebraMap K1_14.Seeds K1_14_2.SeedField)).Separable ∧
        f.natDegree<48 ∧ axisDegree f 0+axisDegree f 1≤2400 ∧
        (∀ j : Fin 2,axisDegree f j<(witness f.natDegree).order 1) ∧
        ∀ γ∈T, ∃ q : Equation,Irreducible q ∧ q∣f ∧ 3≤q.natDegree ∧
          atMark q (M.label γ) (F.scalar γ)=0 := by
  classical
  rcases TerminalDegrees.retained_equation F Crt lo hi regular residues with closed |
    ⟨paid,f,cost,primitive,sep,pos,deg,axes,graded,roots⟩
  · exact Or.inl closed
  let U:=Γ\paid
  let L:=smallMarks U M.label F.scalar f
  let T:=U\L
  have us : U⊆Γ := sdiff_subset
  have ls : L⊆U := filter_subset _ _
  have ts : T⊆U := sdiff_subset
  have W : Word 179818 164650 M.word F.scalar U := by
    refine ⟨F.distinct.mono us,?_,?_⟩
    · intro γ hγ
      rcases (F.mark γ (us hγ)).scalar_degree with zero | degree
      · simp [zero]
      · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at degree
        omega
    · intro γ hγ
      let B:=F.mark γ (us hγ)
      exact ⟨B.bad.support,B.bad.agreement,B.scalar_hits⟩
  have lc := small_marks W M.label (fun _ _ _ _ eq=>sub_left_inj.mp eq) primitive.ne_zero deg axes
  have card : T.card+L.card=U.card := card_sdiff_add_card_eq_card ls
  have base : Γ.card≤U.card+paid.card := by
    calc Γ.card ≤ (U∪paid).card := Finset.card_le_card (by
           intro γ hγ; by_cases hit : γ∈paid
           · exact mem_union_right _ hit
           · exact mem_union_left _ (mem_sdiff.mpr ⟨hγ,hit⟩))
         _ ≤ _ := card_union_le ..
  refine Or.inr ⟨T,f,ts.trans us,by change L.card≤_ at lc; omega,primitive,sep,deg,axes,graded,?_⟩
  intro γ hγ
  obtain ⟨q,ir,dv,hit⟩ := root_factor primitive.ne_zero _ _ (roots γ (us (ts hγ)) (mem_sdiff.mp (ts hγ)).2)
  have positive : 0<q.natDegree := by
    by_contra! zero
    have eq := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero zero)
    exact ir.not_isUnit (eq ▸ (primitive _ (eq ▸ dv)).map C)
  refine ⟨q,ir,dv,?_,hit⟩
  by_contra! sm
  exact (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨ts hγ,q,ir,dv,positive,by omega,hit⟩)
#print axioms higher_remainder
end Lower6960.TerminalSmall

end
end Merged_R6960TerminalSmall

end Merged6967_R6960TerminalSmall

section Merged6967_R6966ProofNativeGraphMarks
set_option Elab.async false




set_option Elab.async false

namespace Research6966.NativeGraphMarks
open Polynomial Finset
open K1_14 (Jet Equation Seeds FX graphEval atX)
open K1_14_3 (SeedField SeedClosure Parent Surface OnSeedFibre)
open PadeNativeQuotient (Native)
open scoped Polynomial
open scoped Classical
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

private abbrev f:=algebraMap SeedField SeedClosure

private def evalPair (y v:SeedClosure) : SeedClosure[X][X]→+*SeedClosure :=
  eval₂RingHom (evalRingHom y) v

private theorem eval_fibre (y v:SeedClosure) :
    (evalPair y v).comp (K1_14_1_4.doubleMap K1_14_3.seedGeneric)=K1_14_3.seedFibreEval y v := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro c;simp [evalPair,K1_14_1_4.doubleMap,K1_14_3.seedFibreEval]
    · simp [evalPair,K1_14_1_4.doubleMap,K1_14_3.seedFibreEval]
  · simp [evalPair,K1_14_1_4.doubleMap,K1_14_3.seedFibreEval]

theorem owner_iff {G:Pade.Row SeedField} (N:Native G) {q:Surface} {y v:SeedClosure} (onq:OnSeedFibre q y v) :
    N.poly∈q.asIdeal ↔ (G.map f).a.eval y*v=(G.map f).b.eval y := by
  rw [←onq,RingHom.mem_ker,←eval_fibre]
  change evalPair y v (K1_14_3.fibreRow N.poly)=0 ↔ _
  rw [N.eq,map_mul]
  have c:evalPair y v (K1_14_1.jetConstant N.scalar)=N.scalar:=by
    simp [evalPair,K1_14_1.jetConstant]
  rw [c,mul_eq_zero,or_iff_right N.nonzero,Pade.Row.polynomial]
  simpa only [evalPair,coe_eval₂RingHom,eval₂_sub,eval₂_mul,eval₂_C,eval₂_X,coe_evalRingHom]
    using (sub_eq_zero : (G.map f).a.eval y*v-(G.map f).b.eval y=0 ↔ _)

/-- The partition in the leaf ledger uses actual ideal membership. Its
rejected parents collectively own at most c-a distinct ordinates. -/
theorem off_owner {G:Pade.Row SeedField} (N:Native G) {parents:Finset Surface}
    (geo:∀ q∈parents,Parent q) {c:ℕ}
    (controls:Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets parents) c)
    (nonempty:(parents.filter (fun q=>N.poly∉q.asIdeal)).Nonempty) :
    ∃ P:Equation,K1_14_3.ProjectedProduct (parents.filter (fun q=>N.poly∉q.asIdeal)) P ∧
      P.natDegree+G.graphDegree≤c := by
  classical
  let S:=parents.filter (fun q=>N.poly∉q.asIdeal)
  have sub:S⊆parents:=filter_subset _ _
  apply Pade.Native.off_graph_product sub nonempty (fun q hq=>geo q (sub hq)) G c controls
  intro y v sheet equality
  obtain ⟨q,mem,onq⟩:=(Pade.Native.sheets_iff ..).mp sheet
  let emb:=(separableClosure SeedField SeedClosure).val
  have lift (P:SeedField[X]):(P.map f).eval (y:SeedClosure)=emb ((P.map (algebraMap SeedField Pade.Native.Sep)).eval y) := by
    calc
      _ = aeval (emb y) P := by rw [eval_map];rfl
      _ = emb (aeval y P) := Polynomial.aeval_algHom_apply emb y P
      _ = _ := by rw [eval_map];rfl
  have eq' := congrArg emb equality
  have hit:(G.map f).a.eval (y:SeedClosure)*(v:SeedClosure)=(G.map f).b.eval (y:SeedClosure) := by
    change (G.a.map f).eval _*_=(G.b.map f).eval _
    rw [lift,lift]
    exact (map_mul emb _ _).symm.trans eq'
  exact (mem_filter.mp mem).2 ((owner_iff N onq).mpr hit)

theorem slope_degree {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) : N.poly.natDegree=1 := by
  have mapInj:=map_injective K1_14_3.seedGeneric (f.injective.comp (IsFractionRing.injective Seeds SeedField))
  have top:(K1_14_3.fibreRow N.poly).natDegree=N.poly.natDegree :=
    natDegree_map_eq_of_injective (f:=mapRingHom K1_14_3.seedGeneric) mapInj N.poly
  rw [←top,N.eq]
  change (K1_14_1.jetConstant N.scalar*(G.map f).polynomial).natDegree=1
  rw [natDegree_mul (show (K1_14_1.jetConstant N.scalar:SeedClosure[X][X])≠0 from
    C_ne_zero.mpr (C_ne_zero.mpr N.nonzero)) ((G.map f).polynomial_ne ((G.primitive_map f).mpr gp)),
    (G.map f).slope_degree ((G.primitive_map f).mpr gp)]
  simp [K1_14_1.jetConstant]

theorem mark_law {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) {q:Surface} {label:K1.K}
    {word:Polynomial K1.K} (owns:N.poly∈q.asIdeal) (mark:∀ P∈q.asIdeal,K1_14.jetAt P label word=0) :
    (N.poly.coeff 1).eval₂ (graphEval label) (atX word)*atX word.derivative =
      (-N.poly.coeff 0).eval₂ (graphEval label) (atX word) := by
  have law:=mark N.poly owns
  let z:=graphEval label
  let y:=atX word
  let v:=atX word.derivative
  change eval₂RingHom (eval₂RingHom z y) v N.poly=0 at law
  have eq:=Polynomial.eq_X_add_C_of_natDegree_le_one (slope_degree N gp).le
  have evaluated:=congrArg (eval₂RingHom (eval₂RingHom z y) v) eq
  change _ = _ at evaluated
  simp only [map_add,map_mul,coe_eval₂RingHom,eval₂_C,eval₂_X] at evaluated
  change (N.poly.coeff 1).eval₂ z y*v=(-N.poly.coeff 0).eval₂ z y
  rw [eval₂_neg]
  apply eq_neg_of_add_eq_zero_left
  exact evaluated.symm.trans law

#print axioms owner_iff
#print axioms off_owner
#print axioms mark_law

theorem equation_degrees {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) :
    (N.poly.coeff 1).natDegree≤G.graphDegree-1 ∧ (-N.poly.coeff 0).natDegree≤G.graphDegree := by
  let deg:=G.graphDegree
  have gn:=(G.primitive_map f).mpr gp
  have total:Pade.totalJet (K1_14_3.fibreRow N.poly)=deg := by
    rw [N.eq]
    change Pade.totalJet (K1_14_1.jetConstant N.scalar*(G.map f).polynomial)=deg
    rw [Pade.totalJet_mul (show (K1_14_1.jetConstant N.scalar:SeedClosure[X][X])≠0 from
      C_ne_zero.mpr (C_ne_zero.mpr N.nonzero)) ((G.map f).polynomial_ne gn),
      (G.map f).total_polynomial gn,Pade.Row.degree_map]
    have zero:Pade.totalJet (K1_14_1.jetConstant N.scalar)=0 := Nat.eq_zero_of_le_zero
      ((Pade.totalJet_le _ 0).mpr (by
        intro j i ne
        by_cases j0:j=0
        · subst j;by_cases i0:i=0
          · omega
          · exact False.elim (ne (by simp [K1_14_1.jetConstant,coeff_C,i0]))
        · exact False.elim (ne (by simp [K1_14_1.jetConstant,coeff_C,j0]))))
    rw [zero,zero_add]
  have support (j i:ℕ) (ne:(N.poly.coeff j).coeff i≠0):i+j≤deg := by
    apply (Pade.totalJet_le _ deg).mp total.le
    simp only [K1_14_3.fibreRow,coeff_map,coe_mapRingHom]
    exact (map_ne_zero_iff K1_14_3.seedGeneric (f.injective.comp (IsFractionRing.injective Seeds SeedField))).mpr ne
  have cap (j:ℕ): (N.poly.coeff j).natDegree≤deg-j := by
    by_cases zero:N.poly.coeff j=0
    · simp [zero]
    have spent:=support j _ (show (N.poly.coeff j).coeff (N.poly.coeff j).natDegree≠0 from by
      rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr zero)
    omega
  exact ⟨cap 1,by simpa using cap 0⟩

#print axioms equation_degrees
end
end Research6966.NativeGraphMarks

end Merged6967_R6966ProofNativeGraphMarks

section Merged6967_R6966ProofRegularPhysicalChart
set_option Elab.async false




set_option Elab.async false

-- merged module R6966ProofPhysicalPrimitiveCoeffs
section Merged_R6966ProofPhysicalPrimitiveCoeffs

namespace Research6966.PhysicalPrimitiveCoeffs
open Polynomial Finset
open K1_14 (L FX Jet Seeds)
open K1_14_1 (SeedPoly Source RawSource jetConstant)
open K1_14_1_4 (doubleMap centerBase evalRaw)
open GlobalPrimitive (Clears)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 24
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

abbrev R:=SeedPoly[X]
abbrev k:=K1_14_1.SeedField
def rawCoeff : R→+*k[X]:=mapRingHom (algebraMap SeedPoly k)
def phys : L[X]→+*R:=mapRingHom MvPolynomial.C
def seeds : SeedPoly→+*R:=C

theorem physical_only (P:L[X]) : centerBase (phys P)=MvPolynomial.C (algebraMap L[X] FX P) := by
  have eq:centerBase.comp phys=MvPolynomial.C.comp (algebraMap L[X] FX) := by
    apply Polynomial.ringHom_ext
    · intro c
      change centerBase ((C c).map MvPolynomial.C)=_
      rw [Polynomial.map_C]
      simp only [centerBase,coe_eval₂RingHom,eval₂_C,RingHom.comp_apply]
      change MvPolynomial.map (algebraMap L FX) (MvPolynomial.C c)=_
      rw [MvPolynomial.map_C];rfl
    · change centerBase (Polynomial.X.map MvPolynomial.C)=_
      rw [Polynomial.map_X];simp only [centerBase,coe_eval₂RingHom,eval₂_X,RingHom.comp_apply]
  exact RingHom.congr_fun eq P

theorem seed_only (i:Fin 2) : centerBase (seeds (MvPolynomial.X i))=MvPolynomial.X i := by
  change (eval₂RingHom _ _ (C (MvPolynomial.X i)):Seeds)=_
  rw [coe_eval₂RingHom,eval₂_C]
  exact MvPolynomial.map_X _ _

theorem native_clears : Clears centerBase := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C c=>
    obtain ⟨n,d,nd,id⟩:=IsFractionRing.div_surjective L[X] c
    have nz:algebraMap L[X] FX d≠0:=(map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr (nonZeroDivisors.ne_zero nd)
    refine ⟨phys n,phys d,physical_only d ▸ nz.isUnit.map MvPolynomial.C,?_⟩
    rw [physical_only,physical_only,←map_mul MvPolynomial.C]
    apply congrArg MvPolynomial.C
    rw [←id,mul_comm,div_mul_cancel₀ _ nz]
  | add A B ha hb=>
    obtain ⟨a,d,du,first⟩:=ha
    obtain ⟨b,e,eu,second⟩:=hb
    refine ⟨e*a+d*b,d*e,(map_mul centerBase _ _) ▸ du.mul eu,?_⟩
    rw [map_add,map_mul,map_mul,map_mul,first,second];ring
  | mul_X P i ih=>
    obtain ⟨p,d,du,eq⟩:=ih
    exact ⟨p*seeds (MvPolynomial.X i),d,du,by rw [map_mul,eq,seed_only,mul_assoc]⟩

theorem raw_clears : Clears rawCoeff :=
  GlobalPrimitive.lift_clear _ (GlobalPrimitive.clear_localization (nonZeroDivisors SeedPoly))

theorem global_native {N:Jet} (prime:Prime N) :
    ∃ P:Source,Prime P ∧ Associated (doubleMap centerBase P) N :=
  GlobalPrimitive.global_prime (doubleMap centerBase)
    (map_injective _ (map_injective _ PadeRawField.center_injective))
    (GlobalPrimitive.lift_clear _ (GlobalPrimitive.lift_clear _ native_clears)) prime

theorem global_raw {N:RawSource} (prime:Prime N) :
    ∃ P:Source,Prime P ∧ Associated (doubleMap rawCoeff P) N :=
  GlobalPrimitive.global_prime (doubleMap rawCoeff)
    (map_injective _ (map_injective _ (map_injective _ (IsFractionRing.injective SeedPoly k))))
    (GlobalPrimitive.lift_clear _ (GlobalPrimitive.lift_clear _ raw_clears)) prime

/-- Transpose the abscissa and the two seeds. This permits specialization at
a fixed physical coordinate without evaluating any rational coefficients. -/
def transpose : R≃ₐ[L]MvPolynomial (Fin 2) L[X] :=
  (MvPolynomial.optionEquivLeft L (Fin 2)).symm.trans (MvPolynomial.optionEquivRight L (Fin 2))

theorem transpose_agrees (P:R) :
    MvPolynomial.map (algebraMap L[X] FX) (transpose P)=centerBase P := by
  have eq:(MvPolynomial.map (algebraMap L[X] FX)).comp transpose.toRingHom=centerBase := by
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro c
        have calc₀:(MvPolynomial.optionEquivLeft L (Fin 2)).symm (C (MvPolynomial.C c))=MvPolynomial.C c :=
          (MvPolynomial.optionEquivLeft L (Fin 2)).symm_apply_eq.mpr (MvPolynomial.optionEquivLeft_C L _ c).symm
        change MvPolynomial.map _ ((MvPolynomial.optionEquivRight L _) ((MvPolynomial.optionEquivLeft L _).symm (C (MvPolynomial.C c))))=_
        rw [calc₀,MvPolynomial.optionEquivRight_C,MvPolynomial.map_C]
        change _=centerBase (C (MvPolynomial.C c))
        exact (physical_only (C c)).symm.trans (congrArg centerBase (Polynomial.map_C ..))
      · intro i
        change MvPolynomial.map _ ((MvPolynomial.optionEquivRight L _) ((MvPolynomial.optionEquivLeft L _).symm (C (MvPolynomial.X i))))=_
        rw [MvPolynomial.optionEquivLeft_symm_C_X,MvPolynomial.optionEquivRight_X_some,MvPolynomial.map_X]
        exact (seed_only i).symm
    · change MvPolynomial.map _ ((MvPolynomial.optionEquivRight L _) ((MvPolynomial.optionEquivLeft L _).symm Polynomial.X))=_
      rw [MvPolynomial.optionEquivLeft_symm_X,MvPolynomial.optionEquivRight_X_none,MvPolynomial.map_C]
      simp only [centerBase,coe_eval₂RingHom,eval₂_X]
  exact RingHom.congr_fun eq P

#print axioms global_native
#print axioms global_raw
#print axioms transpose_agrees
end
end Research6966.PhysicalPrimitiveCoeffs

end Merged_R6966ProofPhysicalPrimitiveCoeffs

-- merged module R6966ProofRegularPhysicalChart
section Merged_R6966ProofRegularPhysicalChart

namespace Research6966.RegularPhysicalChart
open Polynomial
open K1_14_1 (jetConstant)
open K1_14_1_4 (substitute doubleMap)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 650000
variable {R:Type*} [CommRing R]

abbrev yVar (R:Type*) [CommRing R] : R[X][X]:=C (Polynomial.X:R[X])
abbrev vVar (R:Type*) [CommRing R] : R[X][X]:=Polynomial.X

def transform (a b u d:R) : R[X][X]→+*R[X][X] :=
  substitute (RingHom.id R) (jetConstant a*yVar R+jetConstant b)
    (jetConstant a*vVar R+jetConstant u*yVar R+jetConstant d)

private theorem onC (a b u d c:R) : transform a b u d (jetConstant c)=jetConstant c := by
  simp [transform,substitute,jetConstant]
private theorem onY (a b u d:R) : transform a b u d (yVar R)=jetConstant a*yVar R+jetConstant b := by
  simp [transform,substitute,yVar]
private theorem onV (a b u d:R) : transform a b u d (vVar R)=jetConstant a*vVar R+jetConstant u*yVar R+jetConstant d := by
  simp [transform,substitute,vVar]

private theorem ext {S:Type*} [CommRing S] {f g:R[X][X]→+*S} (c:∀ r,f (jetConstant r)=g (jetConstant r))
    (y:f (yVar R)=g (yVar R)) (v:f (vVar R)=g (vVar R)) : f=g :=
  Polynomial.ringHom_ext' (Polynomial.ringHom_ext c y) v

theorem comp (a b u d s t v j:R) : (transform a b u d).comp (transform s t v j) =
    transform (s*a) (s*b+t) (s*u+v*a) (s*d+v*b+j) := by
  apply ext
  · intro c;simp only [RingHom.comp_apply,onC]
  · simp only [RingHom.comp_apply,onY,map_add,map_mul,onC,onY]
    ring
  · simp only [RingHom.comp_apply,onV,map_add,map_mul,onC,onV,onY]
    ring

private theorem identity : transform (1:R) 0 0 0=RingHom.id _ := by
  apply ext
  · intro c;rw [onC];rfl
  · rw [onY];simp
  · rw [onV];simp

theorem bijective (a:Rˣ) (b u d:R) : Function.Bijective (transform (↑a:R) b u d) := by
  let s:R:=↑a⁻¹
  let p:R:=↑a
  have ps:p*s=1:=Units.mul_inv a
  have sp:s*p=1:=Units.inv_mul a
  let inv:=transform s (-s*b) (-s^2*u) (s^2*u*b-s*d)
  have li:inv.comp (transform p b u d)=RingHom.id _ := by
    dsimp only [inv];rw [comp,ps]
    have db:p*(-s*b)+b=0:=by linear_combination -b*ps
    have uv:p*(-s^2*u)+u*s=0:=by linear_combination -(s*u)*ps
    have dt:p*(s^2*u*b-s*d)+u*(-s*b)+d=0:=by linear_combination (s*u*b-d)*ps
    rw [db,uv,dt,identity]
  have ri:(transform p b u d).comp inv=RingHom.id _ := by
    dsimp only [inv];rw [comp,sp]
    have db:s*b+-s*b=0:=by ring
    have uv:s*u+-s^2*u*p=0:=by linear_combination -(s*u)*sp
    have dt:s*d+-s^2*u*b+(s^2*u*b-s*d)=0:=by ring
    rw [db,uv,dt,identity]
  exact ⟨(show Function.LeftInverse inv (transform p b u d) from RingHom.congr_fun li).injective,
    (show Function.RightInverse inv (transform p b u d) from RingHom.congr_fun ri).surjective⟩

theorem maps {S:Type*} [CommRing S] (f:R→+*S) (a b u d:R) :
    (doubleMap f).comp (transform a b u d)=
    (transform (f a) (f b) (f u) (f d)).comp (doubleMap f) := by
  have c (v:R):doubleMap f (jetConstant v)=jetConstant (f v):=by simp [doubleMap,jetConstant]
  have y:doubleMap f (yVar R)=yVar S:=by simp [doubleMap,yVar]
  have v:doubleMap f (vVar R)=vVar S:=by simp [doubleMap,vVar]
  apply ext
  · intro j;simp only [RingHom.comp_apply,onC,c]
  · simp only [RingHom.comp_apply,onY,y,map_add,map_mul,c]
  · simp only [RingHom.comp_apply,onV,v,y,map_add,map_mul,c,onV]

theorem comparison {S F:Type*} [IsDomain R] [CommRing S] [IsDomain S] [Field F]
    (inc:R→+*S) (inj:Function.Injective inc) (localizes:GlobalPrimitive.Clears inc)
    (gen:S→+*F) (faithful:Function.Injective gen) (clears:GlobalPrimitive.Clears gen)
    (a:Sˣ) (b u d:S) {P Q:R[X][X]} (pp:Prime P) (qp:Prime Q) (pSlope:0<P.natDegree) (qSlope:0<Q.natDegree)
    (generic:Associated (doubleMap gen (transform (↑a:S) b u d (doubleMap inc P)))
      (doubleMap gen (doubleMap inc Q))) :
    ∃ c:S,IsUnit c ∧ transform (↑a:S) b u d (doubleMap inc P)=jetConstant c*doubleMap inc Q := by
  let φ:=doubleMap inc
  have ij:Function.Injective φ:=map_injective _ (map_injective _ inj)
  have cl:GlobalPrimitive.Clears φ:=GlobalPrimitive.lift_clear _ (GlobalPrimitive.lift_clear _ localizes)
  have degree (g:R[X][X]):(φ g).natDegree=g.natDegree:=natDegree_map_eq_of_injective (map_injective _ inj) _
  have pprime:=GlobalPrimitive.prime_image φ ij cl pp (fun unit=>pSlope.ne' ((degree P).symm.trans (natDegree_eq_zero_of_isUnit unit)))
  have qprime:=GlobalPrimitive.prime_image φ ij cl qp (fun unit=>qSlope.ne' ((degree Q).symm.trans (natDegree_eq_zero_of_isUnit unit)))
  let eqv:=RingEquiv.ofBijective (transform (↑a:S) b u d) (bijective a b u d)
  have ir:Irreducible (eqv (φ P)):=(MulEquiv.irreducible_iff eqv).mpr pprime.irreducible
  have pos:0<(φ Q).natDegree:=(degree Q) ▸ qSlope
  have divides:φ Q∣eqv (φ P):=GlobalPrimitive.descend_jet gen faithful clears qprime pos generic.symm.dvd
  obtain ⟨scalar,assoc⟩:=qprime.irreducible.associated_of_dvd ir divides
  obtain ⟨c,unit,id⟩:=GlobalPrimitive.unit_constant scalar.isUnit
  exact ⟨c,unit,assoc.symm.trans (id ▸ mul_comm _ _)⟩

#print axioms comparison
end
end Research6966.RegularPhysicalChart

end Merged_R6966ProofRegularPhysicalChart

end Merged6967_R6966ProofRegularPhysicalChart
