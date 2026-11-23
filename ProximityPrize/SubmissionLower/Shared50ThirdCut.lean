import ProximityPrize.SubmissionLower.Final50GeometryCut
import ProximityPrize.SubmissionLower.Final50SharedPrice

set_option Elab.async false
set_option autoImplicit false

namespace Shared50ThirdCut
noncomputable section

open Finset Polynomial MvPolynomial
open P3 (I K)

local instance (p:Prop):Decidable p:=Classical.propDecidable p
open scoped BigOperators ENat Polynomial
open K1_13 (Row Geom Shape shape InBox chart atJet extend embed)
open K1_13_6 (GeoJets GeoField HighChart markIdeal evalGeneric toGeneric intersectionIdeal
  cycleLength divisorIdeal separant CurveSections Pieces)
open K1_13_6_1 (mem_markIdeal mark_curve)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective)
open K1_13_6_3 (dimension cycleWeight)
open K1_13_7_1 (derivative_in_box shape_chamber)
open P0_9_6_1_2 (exists_value_cut)
open Final50Price (taylorLength primaryBox Messages)
open Final50GeometryCut (CutInput)
open Final50GeometryCut_3 (cutCycle)
open private P0_9_6_3.canonical_unique P0_9_6_3.cycleWeight_ge
  from ProximityPrize.SubmissionLower.PortLow6
open private K1_14_6.curve_degree_nat from ProximityPrize.SubmissionLower.Fast055

abbrev chartWidth (f:Row 4):ℕ:=(chart (taylorLength+2) (shape f).chamber).b

def Marked (f Q : Row 4) (l : ℕ) (surfaces : Finset (Ideal GeoJets)) (S : Geom[X]) : Prop :=
  ∃ P ∈ surfaces, ∃ r,HighChart f Q l S P r

private theorem points_of_value {Γ : Finset K} {s : K → K[X]} {C : Ideal GeoJets}
    (prime:C.IsPrime) (hdim:dimension C=1)
    (hinj:Set.InjOn s (Γ:Set K))
    (hC : ∀ γ ∈ Γ,C≤markIdeal (extend (s γ)))
    (d : ℕ) (cuts : ∀ x a : K, ∃ D : GeoJets, D.totalDegree ≤ d ∧
      ∀ γ ∈ Γ,(evalGeneric (extend (s γ)) D=0↔(s γ).eval x=a)) :
    CurveSections Γ s ⌊(d:ℚ)*affineDegree C⌋₊ := by
  classical
  let:=prime
  intro x a hmiss
  obtain ⟨D,hD,hvalue⟩:=cuts x a
  have hproper : D ∉ C := by
    obtain ⟨γ,hγ,hne⟩:=hmiss
    exact fun hm => hne ((hvalue γ hγ).mp (hC γ hγ hm))
  let J:=C ⊔ Ideal.span {D}
  obtain ⟨hJdim, hJdeg⟩ :=
    principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime prime hproper hD
  have hJzero : (affineHilbertPolynomial J).natDegree = 0 := by
    change (affineHilbertPolynomial J).natDegree≤dimension C - 1 at hJdim
    omega
  have hdeg : affineDegree J ≤ (d : ℚ) * affineDegree C := by
    have hd:(affineHilbertPolynomial C).natDegree=1:=hdim
    simpa [J,affineDegree,hd,hJzero,Polynomial.leadingCoeff] using hJdeg
  let T:=Γ.filter fun γ => (s γ).eval x=a
  let point (γ:K):=actualPoint (extend (s γ))
  have hpoint : Set.InjOn point (Γ : Set K) := fun _ hγ _ hη he =>
    hinj hγ hη (Polynomial.map_injective embed embed.injective (actualPoint_injective he))
  have hinto : (T.image point : Set JetPoint) ⊆ zeroLocus GeoField J := by
    intro y hy
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hy
    obtain ⟨hΓ,hv⟩:=mem_filter.mp hγ
    exact mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hC γ hΓ,(hvalue γ hΓ).mpr hv⟩
  obtain ⟨hfinite,hcount⟩:=finite_zeroLocus_and_ncard_le_affineDegree (K:=GeoField) J hJzero
  have hcard:=Set.ncard_le_ncard hinto hfinite
  rw [Set.ncard_coe_finset,card_image_of_injOn (hpoint.mono (filter_subset _ _))] at hcard
  exact Nat.le_floor ((Nat.cast_le.mpr hcard).trans (hcount.trans hdeg))

private theorem curve_family {Γ : Finset K} {s : K → K[X]} {f Q R : Row 4} {l : ℕ}
    (input:CutInput Γ s f Q l) {P C:Ideal GeoJets}
    (hP:(intersectionIdeal f Q).IsMinimalPrime P) (hR:toGeneric R ∉ P)
    (hC:(divisorIdeal P R).IsMinimalPrime C) :
    let part := Γ.filter fun γ => C ≤ markIdeal (extend (s γ)) ∧
      ∃ r,HighChart f Q l (extend (s γ)) P r
    CurveSections part s ⌊(chartWidth f : ℚ) * affineDegree C⌋₊ ∧
      0 < ⌊(chartWidth f:ℚ)*affineDegree C⌋₊ := by
  classical
  let:=hP.isPrime
  have hd:=principalCut_natDegree_affineHilbertPolynomial_add_one hR hC
  change dimension C+1=dimension P at hd
  rw [(cutCycle input.small input.proper input.box).local_bound P hP |>.1] at hd
  have hdim:dimension C=1:=by omega
  let part := Γ.filter fun γ => C ≤ markIdeal (extend (s γ)) ∧
    ∃ r,HighChart f Q l (extend (s γ)) P r
  have hsub:part ⊆ Γ:=filter_subset _ _
  have hposW:1≤chartWidth f:=le_max_of_le_left (Nat.le_add_right 1 _)
  obtain ⟨δ,hδ,hδeq⟩:=K1_14_6.curve_degree_nat C hC.isPrime hdim
  have hdpos : 0 < ⌊(chartWidth f : ℚ) * affineDegree C⌋₊ := by
    change 1≤_
    apply Nat.le_floor
    rw [hδeq]
    exact_mod_cast (Nat.mul_le_mul hposW (Nat.succ_le_of_lt hδ))
  refine ⟨?_,hdpos⟩
  change CurveSections part s _
  by_cases hempty:part = ∅
  · rw [hempty]
    intro x a h
    simpa using h
  obtain ⟨γ₀,hγ₀⟩:=nonempty_iff_ne_empty.mpr hempty
  obtain ⟨r,hγchart⟩:=(mem_filter.mp hγ₀).2.2
  let p:=(shape f).chamber
  let g:=(separant^[r]) f
  have hgbox : InBox (shape g) p :=
    let hb:=derivative_in_box f r
    ⟨hb.1.trans (le_max_left _ _),hb.2.1,hb.2.2⟩
  apply points_of_value hC.isPrime hdim (input.distinct.mono hsub)
    (fun γ hγ => (mem_filter.mp hγ).2.1)
  intro x a
  obtain ⟨D, hD, hv⟩ := exists_value_cut (by decide : taylorLength+2 ≤ K1.p) hgbox
    (shape_chamber f) input.small.2.1 x a
  refine ⟨D,hD.1,fun γ hγ => ?_⟩
  obtain ⟨r', hh⟩:=(mem_filter.mp hγ).2.2
  have heq:=P0_9_6_3.canonical_unique hh.chart hγchart.chart
  subst r'
  have hvan:=mem_markIdeal.mp (hh.point (hh.chart.2.1 r le_rfl))
  exact hv (s γ) ((input.degree γ (hsub hγ)).trans_lt (by decide)) hvan hh.regular

private theorem cut_degree {f Q R : Row 4} {l : ℕ} {Γ : Finset K} {s : K → K[X]}
    (input:CutInput Γ s f Q l) (surfaces:Finset (Ideal GeoJets))
    (origin : ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l:ℕ∞)≤cycleLength (intersectionIdeal f Q) P h.isPrime)
    (hR : ∀ P ∈ surfaces,toGeneric R ∉ P) (hwidth:(shape R).b≤primaryBox.b) :
    (l : ℚ) * (∑ P ∈ surfaces, ∑ C ∈ (divisorIdeal P R).minimalPrimesFinset, affineDegree C) ≤
      ((shape f).b*primaryBox.b*primaryBox.b:ℕ):=by
  let pair:=intersectionIdeal f Q
  let w:=cycleWeight pair
  let B:=primaryBox.b
  have hc:=cutCycle input.small input.proper input.box
  have sub : surfaces ⊆ pair.minimalPrimesFinset := fun P hP =>
    Ideal.mem_minimalPrimesFinset.mpr (origin P hP).choose
  have hwidth' : (toGeneric R).totalDegree ≤ B :=
    (K1_13_6_3_6.totalDegree_toGeneric R).le.trans hwidth
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ P ∈ surfaces, (B : ℚ) * ((w P : ℚ) * affineDegree P) := by
      apply sum_le_sum
      intro P hP
      obtain ⟨hp,hl⟩:=origin P hP
      let:=hp.isPrime
      have hl' : (l:ℚ)≤w P:=by exact_mod_cast P0_9_6_3.cycleWeight_ge hc hp hl
      have hdeg:=principalCut_sum_affineDegree_minimalPrimes_le (hR P hP) hwidth'
      exact (mul_le_mul_of_nonneg_left hdeg (by positivity)).trans (by
        rw [mul_left_comm]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hl' (affineDegree_nonneg P))
    _=(B:ℚ) * ∑ P ∈ surfaces,(w P:ℚ)*affineDegree P:=(Finset.mul_sum ..).symm
    _ ≤ (B : ℚ) * (((shape f).b * B : ℕ) : ℚ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sum_le_sum_of_subset_of_nonneg sub
        (fun P _ _ => mul_nonneg (by positivity) (affineDegree_nonneg P))).trans hc.weighted_degree
    _=_:=by push_cast; ring

/-- Assign third-cut curves using the old surface and one regular value section. -/
theorem cover {Γ : Finset K} {s : K → K[X]} {f Q : Row 4} {l : ℕ}
    (input:CutInput Γ s f Q l) (surfaces:Finset (Ideal GeoJets)) (R:Row 4)
    (origin : ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l:ℕ∞)≤cycleLength (intersectionIdeal f Q) P h.isPrime)
    (hwidth:(shape R).b≤primaryBox.b)
    (hproper : ∀ P ∈ surfaces,toGeneric R ∉ P)
    (hzero : ∀ γ ∈ Γ,atJet R (extend (s γ))=0) :
    ∃ C : Pieces Γ, C.curves s ∧ (∀ i, 0 < C.degree i) ∧
      (∀ γ ∈ Γ,Marked f Q l surfaces (extend (s γ))→γ ∈ C.union) ∧
      l*C.total≤(shape f).b*primaryBox.b*primaryBox.b*chartWidth f:=by
  classical
  let T:=surfaces.sigma fun P => (divisorIdeal P R).minimalPrimesFinset
  let e:=T.equivFin.symm
  let marks (P C : Ideal GeoJets) := Γ.filter fun γ => C ≤ markIdeal (extend (s γ)) ∧
    ∃ r,HighChart f Q l (extend (s γ)) P r
  let d (C:Ideal GeoJets) := ⌊(chartWidth f:ℚ)*affineDegree C⌋₊
  let blocks : Pieces Γ := ⟨T.card, fun i => marks (e i).val.1 (e i).val.2,
    fun _ => filter_subset _ _,fun i => d (e i).val.2⟩
  have square (i : Fin T.card) : CurveSections (blocks.piece i) s (blocks.degree i) ∧
      0 < blocks.degree i:=by
    let a:=e i
    obtain ⟨hP,hC⟩:=mem_sigma.mp a.property
    exact curve_family input (origin a.val.1 hP).choose (hproper a.val.1 hP)
      (Ideal.mem_minimalPrimesFinset.mp hC)
  refine ⟨blocks,fun i => (square i).1,fun i => (square i).2, ?_, ?_⟩
  · intro γ hγ hm
    obtain ⟨P,hP,r,hh⟩:=hm
    obtain ⟨C,hC,hγC⟩:=mark_curve hh.point (hzero γ hγ)
    let a:T:=⟨⟨P,C⟩,mem_sigma.mpr ⟨hP,Ideal.mem_minimalPrimesFinset.mpr hC⟩⟩
    apply mem_biUnion.mpr
    refine ⟨T.equivFin a,mem_univ _, ?_⟩
    change γ ∈ marks (e (T.equivFin a)).val.1 (e (T.equivFin a)).val.2
    rw [show e (T.equivFin a)=a from T.equivFin.symm_apply_apply a]
    exact mem_filter.mpr ⟨hγ,hγC,⟨r,hh⟩⟩
  · have htotal : ((blocks.total : ℕ) : ℚ) ≤
        (chartWidth f : ℚ) * ∑ P ∈ surfaces, ∑ C ∈ (divisorIdeal P R).minimalPrimesFinset,
          affineDegree C:=by
      unfold Pieces.total
      rw [Nat.cast_sum]
      change (∑ i:Fin T.card,((d (e i).val.2:ℕ):ℚ))≤_
      let value (a:Σ _:Ideal GeoJets,Ideal GeoJets):ℚ:=(d a.2:ℚ)
      have eq : (∑ i : Fin T.card, ((d (e i).val.2 : ℕ) : ℚ)) = ∑ a ∈ T, value a := by
        calc
          _ = ∑ a:T,value a.val:=Fintype.sum_equiv e _ _ (fun _ => rfl)
          _=_:=Finset.sum_attach T value
      rw [eq, show T = surfaces.sigma (fun P => (divisorIdeal P R).minimalPrimesFinset) from rfl,
        Finset.sum_sigma,Finset.mul_sum]
      refine sum_le_sum fun P _ => ?_
      rw [Finset.mul_sum]
      exact sum_le_sum fun C _ => Nat.floor_le (mul_nonneg (by positivity) (affineDegree_nonneg C))
    apply (Nat.cast_le (α:=ℚ)).mp
    push_cast
    calc
      _ ≤ (l : ℚ) * ((chartWidth f : ℚ) * ∑ P ∈ surfaces,
          ∑ C ∈ (divisorIdeal P R).minimalPrimesFinset,affineDegree C) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ ≤ _ := by
        rw [mul_left_comm]
        have hc := mul_le_mul_of_nonneg_left
          (cut_degree input surfaces origin hproper hwidth) (by positivity:0≤(chartWidth f:ℚ))
        push_cast at hc
        simpa only [mul_comm,mul_left_comm,mul_assoc] using hc

/-- The charged nonpersistent labels use the third-cut fee alone. -/
theorem count {Γ : Finset K} {s : K → K[X]} {w : I → K} {f Q : Row 4} {l : ℕ}
    (hmsg:Messages w Γ s) (input:CutInput Γ s f Q l)
    (surfaces:Finset (Ideal GeoJets)) (R:Row 4)
    (origin : ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l:ℕ∞)≤cycleLength (intersectionIdeal f Q) P h.isPrime)
    (hwidth:(shape R).b≤primaryBox.b)
    (hproper : ∀ P ∈ surfaces,toGeneric R ∉ P)
    (hzero : ∀ γ ∈ Γ,atJet R (extend (s γ))=0) :
    let assigned:=Γ.filter fun γ => Marked f Q l surfaces (extend (s γ))
    assigned.card≤Final50SharedPrice.nonsharedFee (shape f) l:=by
  classical
  obtain ⟨C,hC,hpos,hcover,hdegree⟩:=cover input surfaces R origin hwidth hproper hzero
  have hsub : (Γ.filter fun γ => Marked f Q l surfaces (extend (s γ))) ⊆ C.union :=
    fun γ hγ => hcover _ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2
  apply (card_le_card hsub).trans ((Final50FatPad.pieces_curve_capacity_integral C hmsg hC hpos).trans ?_)
  unfold Final50SharedPrice.nonsharedFee K1_13.ceilDiv
  apply (Nat.le_div_iff_mul_le input.positive).mpr
  let numerator:=2*(shape f).b*primaryBox.b^2*chartWidth f
  change (2*C.total)*l≤numerator+l-1
  have hc : (2*C.total)*l ≤ numerator := by
    simpa only [numerator, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using Nat.mul_le_mul_left 2 hdegree
  have hl:=input.positive
  omega

#print axioms cover
#print axioms count
end
end Shared50ThirdCut
