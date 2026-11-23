import ProximityPrize.SubmissionLower.R6960Low6960SharedTallyOld
import ProximityPrize.SubmissionLower.R6960Low6960SharedTallyNew
import ProximityPrize.SubmissionLower.R6960Low6960SharedThirdCut
import ProximityPrize.SubmissionLower.Shared50Multiplicity

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
open private tilted_count from ProximityPrize.SubmissionLower.R6960Low6960SharedTallyNew
open Low6960SharedTallyOld (orderCost auxiliaryCap continuedCap surfaceCap)
open Low6960SharedPersistent (Persistent)
open Finset
open scoped Polynomial BigOperators
attribute [local instance] Classical.propDecidable
open private continued_bound le_ceil from ProximityPrize.SubmissionLower.R6960Low6960GeometryCut
open private eval_actualPoint genericCoeffs_injective from ProximityPrize.SubmissionLower.R6960Low6960GeometryCut

private theorem shape_valid {f : Row 4} (hf : SmallFactor f) : K1_13_8.Valid (shape f) := by
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
def TiltedCut {Γ : Finset K} {s : K → K[X]} (f : Row 4) (u : Rate) : Prop :=
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
    change F.union.card≤2*(133409*(shape f).b*primaryBox.b)
    have hF' := Low6960GeometryCut.pieces_surface_capacity F hm hF hFP
    change 2*F.total ≤ 133409*(shape f).b*primaryBox.b at hFB
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
