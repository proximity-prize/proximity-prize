import ProximityPrize.SubmissionLower.RingHomShortcuts
import ProximityPrize.SubmissionLower.R6960Low6960GeometryCut
import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.R6960Low6960SharedTallyOld
import ProximityPrize.SubmissionLower.R6960Low6960SharedTallyNew
import ProximityPrize.SubmissionLower.Shared50OrderDivision
import ProximityPrize.SubmissionLower.R6960Low6960FastPrice

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
