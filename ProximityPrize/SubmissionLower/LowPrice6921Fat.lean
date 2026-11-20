import ProximityPrize.SubmissionLower.LowPrice6921Physical
set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace LowPrice6921

noncomputable section

open Polynomial K1 K1_13 K1_13_6 K1_13_7
open scoped BigOperators Polynomial

section Singular
open K1_13_7_1

private theorem box_chamber (f : Row 4) : InBox (shape f) (shape f).chamber :=
  ⟨le_max_left _ _, le_rfl, le_rfl⟩

private theorem derivative_proper {f : Row 4} (hf : SmallFactor f) (j : ℕ)
    (hj : 0 < j) (hg : (separant^[j]) f ≠ 0) : ¬ f ∣ (separant^[j]) f := by
  rintro ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    intro hz
    exact hg (by rw [hq, hz, mul_zero])
  have hd := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.1.ne_zero hq0
  have h := derivative_degree f j
  have ht : 0 < f.degreeOf 3 := hf.2.1
  change ((separant^[j]) f).degreeOf 3 ≤ f.degreeOf 3 - j at h
  rw [hq, hd] at h
  omega

private theorem one_piece (h1 : K1_13_7_1.c1) (h2 : K1_13_7_1.c2)
    {w Γ s} (hm : LowFat6921.Messages w Γ s) (f : Row 4) (hf : SmallFactor f) (j : ℕ)
    (hj : 0 < j)
    (hmarks : ∀ γ ∈ Γ, atJet f (extend (s γ)) = 0 ∧
      atJet ((separant^[j]) f) (extend (s γ)) = 0 ∧
      RegularAt ((separant^[j]) f) (extend (s γ))) :
    let p := (shape f).chamber
    let h := chart (taylorLength + 4) p
    Γ.card ≤ 4 * (mixed32 p p h h / 32) := by
  classical
  dsimp only
  by_cases hΓ : Γ.Nonempty
  · obtain ⟨γ, hγ⟩ := hΓ
    let g := (separant^[j]) f
    let p := (shape f).chamber
    let h := chart (taylorLength + 4) p
    let d := mixed32 p p h h / 32
    have hg0 : g ≠ 0 := by
      intro hz
      exact (hmarks γ hγ).2.2 (by simp [show (separant^[j]) f = 0 from hz, atJet])
    have hpf := box_chamber f
    have hpg : InBox (shape g) p := by
      have hb := derivative_in_box f j
      exact ⟨hb.1.trans hpf.1, hb.2.1.trans hpf.2.1, hb.2.2.trans hpf.2.2⟩
    have hp := shape_chamber f
    have ht : 0 < p.t := hf.2.1
    obtain ⟨C, hC, hrecover⟩ := exists_chart g p hpg hp ht
    have hbound : SliceBound (toGeneric f) (toGeneric g) C d := by
      intro a b points hpts
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 32)).mpr (by
        rw [Nat.mul_comm]
        exact h1 p h hp (chart_chamber _ _) _ _ _ _
          (toGeneric_fits hpf) (toGeneric_fits hpg) (C.pullback_fits hC a)
          (C.pullback_fits hC b) points (fun y hy => (hpts y hy).1))
    obtain ⟨B, hcover, hsurfaces, hpos, hsum⟩ :=
      h2 (toGeneric f) (toGeneric g)
        (fun hz => hf.1.ne_zero (toGeneric_injective (hz.trans (map_zero _).symm)))
        (fun hz => hg0 (toGeneric_injective (hz.trans (map_zero _).symm)))
        (proper_generic f g hf.1 (derivative_proper hf j hj hg0))
        C d hbound Γ s hm.distinct (fun a ha => by
          obtain ⟨hf', hg', hr⟩ := hmarks a ha
          refine ⟨hm.old_degree a ha, ?_, ?_, hrecover _ hg' hr⟩
          · rw [evalGeneric_toGeneric, hf', map_zero]
          · rw [evalGeneric_toGeneric, hg', map_zero])
    exact (Finset.card_le_card hcover).trans
      ((piece_surface_capacity B hm hsurfaces hpos).trans (Nat.mul_le_mul_left 4 hsum))
  · simp [Finset.not_nonempty_iff_eq_empty.mp hΓ]

theorem singular_count (w : I → K) {Γ s} (hm : LowFat6921.Messages w Γ s)
    (f : Row 4) (hf : SmallFactor f) (_ : FatEligible (shape f))
    (hmarks : ∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ ¬ K1_13_7.RegularAt f (extend (s γ))) :
    Γ.card ≤ singularPrice (shape f) := by
  classical
  have h1 := Geometry.K1_13_7_1_1
  have h2 := Geometry.K1_13_7_1_2
  let t := (shape f).t
  have hcover (γ : K) (hγ : γ ∈ Γ) :
      ∃ j, 0 < j ∧ j < t ∧
        atJet ((separant^[j]) f) (extend (s γ)) = 0 ∧
        RegularAt ((separant^[j]) f) (extend (s γ)) :=
    regular_derivative f _ hf (hmarks γ hγ).1 (Classical.not_not.mp (hmarks γ hγ).2)
  by_cases ht : 1 < t
  · let p := (shape f).chamber
    let h := chart (taylorLength + 4) p
    let m := mixed32 p p h h
    let part (j : Fin t) := Γ.filter fun γ =>
      0 < j.val ∧ atJet ((separant^[j.val]) f) (extend (s γ)) = 0 ∧
        RegularAt ((separant^[j.val]) f) (extend (s γ))
    have hall : Γ ⊆ Finset.univ.biUnion part := by
      intro γ hγ
      obtain ⟨j, hj, hjt, hz, hr⟩ := hcover γ hγ
      exact Finset.mem_biUnion.mpr ⟨⟨j, hjt⟩, Finset.mem_univ _, Finset.mem_filter.mpr
        ⟨hγ, hj, hz, hr⟩⟩
    have hpart (j : Fin t) : (part j).card ≤ 4 * (m / 32) := by
      by_cases hj : 0 < j.val
      · apply one_piece h1 h2 (hm.mono (Finset.filter_subset _ _)) f hf j.val hj
        intro γ hγ
        have hp := Finset.mem_filter.mp hγ
        exact ⟨(hmarks γ hp.1).1.1, hp.2.2⟩
      · simp [part, hj]
    have hprice : 4 * t * (m / 32) ≤ ceilDiv (4 * t * m) 32 := by
      unfold ceilDiv
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 32)).mpr
      rw [Nat.mul_assoc]
      exact (Nat.mul_le_mul_left (4 * t) (Nat.div_mul_le_self m 32)).trans (by omega)
    have hchart : K1_13_7.fatChart (shape f) = h := by
      unfold K1_13_7.fatChart
      exact ite_eq_right (by omega : t ≠ 1)
    unfold singularPrice
    rw [ite_eq_left ht, hchart]
    change Γ.card ≤ ceilDiv (4 * t * m) 32 + t * (shape f).b ^ 2 + 1
    calc
      Γ.card ≤ (Finset.univ.biUnion part).card := Finset.card_le_card hall
      _ ≤ ∑ j : Fin t, (part j).card := Finset.card_biUnion_le
      _ ≤ ∑ _ : Fin t, 4 * (m / 32) := Finset.sum_le_sum fun j _ => hpart j
      _ = 4 * t * (m / 32) := by simp [Nat.mul_comm, Nat.mul_assoc]
      _ ≤ ceilDiv (4 * t * m) 32 := hprice
      _ ≤ _ := by omega
  · have hempty : Γ = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨γ, hγ⟩
      obtain ⟨j, hj, hjt, _, _⟩ := hcover γ hγ
      omega
    simp [hempty]

end Singular

section Hypersurface
open K1_13_7_1 K1_13_7_2

private theorem lifted_at_mark {f : Row 4} {q : Row 3} {S : Geom[X]}
    (hf : OnFactor f S) (hr : RegularAt f S) (hq : atJet q S = 0) :
    ∃ surface, LiftedSurface f q surface ∧ surface ≤ markIdeal S := by
  have hl : intersectionIdeal f (liftLower q) ≤ markIdeal S := by
    apply Ideal.span_le.mpr
    intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl
    · exact mem_markIdeal.mpr hf.1
    · exact mem_markIdeal.mpr ((eval_liftLower q S).trans hq)
  have : (markIdeal S).IsPrime := RingHom.ker_isPrime (evalGeneric S)
  obtain ⟨surface, hZ, hle⟩ := Ideal.exists_minimalPrimes_le hl
  refine ⟨surface, ⟨hZ, ?_, ?_⟩, hle⟩
  · intro hz
    have h := mem_markIdeal.mp (hle hz)
    rw [eval_liftLower, K1_13_1.eval_anchorLead] at h
    exact hf.2 h
  · exact fun hz => hr (mem_markIdeal.mp (hle hz))

theorem threefold_capacity {w Γ s d} (h : LowFat6921.Messages w Γ s)
    (hs : ThreefoldSections Γ s d) (hd : 0 < d) : Γ.card ≤ 8 * d := by
  classical
  have hsection (i : I) (hi : ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) :
      (Γ.filter (fun γ => (s γ).eval (node i) = w i)).card ≤ 4 * d := by
    obtain ⟨C, hC, hc, hpos, hdeg⟩ := hs (node i) (w i) hi
    have hH := h.mono (Finset.filter_subset (fun γ => (s γ).eval (node i) = w i) Γ)
    exact (Finset.card_le_card hC).trans ((piece_surface_capacity C hH hc hpos).trans
      (Nat.mul_le_mul_left 4 hdeg))
  have := section_capacity h (4 * d) hsection
  omega

theorem threefold_pieces_capacity {w Γ s} (C : Pieces Γ) (h : LowFat6921.Messages w Γ s)
    (hc : ThreefoldPieces C s) (hd : ∀ i, 0 < C.degree i) : C.union.card ≤ 8 * C.total := by
  classical
  calc
    _ ≤ ∑ i, (C.piece i).card := Finset.card_biUnion_le
    _ ≤ ∑ i, 8 * C.degree i := Finset.sum_le_sum fun i _ =>
      threefold_capacity (h.mono (C.subset i)) (hc i) (hd i)
    _ = _ := by simp [Pieces.total, Finset.mul_sum]

private theorem proper_capacity {w Γ s} {x : Shape} (C : Pieces Γ) (h : LowFat6921.Messages w Γ s)
    (hc : C.curves s) (hb : 32 * C.total ≤ curveMass32 x)
    (hn : 32 * C.n ≤ componentMass32 x) :
    C.union.card ≤ ceilDiv (81879 * curveMass32 x) (32 * 46594) +
      ceilDiv (componentMass32 x) 32 := by
  have hcap := piece_curve_capacity C h hc
  unfold ceilDiv
  omega

theorem hypersurface_count (w : I → K) {Γ s} (hm : LowFat6921.Messages w Γ s)
    (f : Row 4) (hf : SmallFactor f) (helig : FatEligible (shape f))
    (hon : ∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ RegularAt f (extend (s γ)))
    (D : Row 3) (hD : D ≠ 0) (hbox : LowerCaps D 35007 12106)
    (hDmark : ∀ γ ∈ Γ, atJet D (extend (s γ)) = 0) :
    Γ.card ≤ hypersurfacePrice (shape f) := by
  classical
  have h1 := Geometry.K1_13_7_2_1
  have h2 := Geometry.K1_13_7_2_2
  have h3 := Geometry.K1_13_7_2_3
  have h4 := Geometry.K1_13_7_2_4
  have h5 := Geometry.K1_13_7_2_5
  obtain ⟨q, hq⟩ := h1 f hf D hD hbox
  obtain ⟨T⟩ := h2 f hf
  obtain ⟨A, hA, hcoverA, hcurve, hcomp⟩ :=
    h3 Γ s f D q hf helig hq T hm.distinct hm.old_degree hon
  obtain ⟨C, F, hC, hF, hposC, hposF, hcoverI, hdegC, hdegF⟩ :=
    h5 Γ s f hf helig T hm.distinct hm.old_degree hon
  have hcover : Γ ⊆ A.union ∪ (C.union ∪ F.union) := by
    intro γ hγ
    let S := extend (s γ)
    have hfS := (hon γ hγ).1
    have hrS := (hon γ hγ).2
    have hdS : S.natDegree ≤ 133671 := Polynomial.natDegree_map_le.trans (hm.old_degree γ hγ)
    obtain ⟨surface, hZ, hle⟩ := lifted_at_mark hfS hrS (hq.roots S (hDmark γ hγ))
    by_cases hE : toGeneric T.test ∈ surface
    · by_cases hflow : toGeneric (lowerFlow q) ∈ surface
      · have hfZ : toGeneric f ∈ surface := hZ.minimal.le (Ideal.subset_span (by simp))
        have hmem : toGeneric (membershipTest f) ∈ surface :=
          (T.test_iff surface hZ.minimal.isPrime hfZ hZ.regular).mp hE
        have hI : IntegratedMark f S := h4 f hf surface hZ.minimal.isPrime (hq.simple surface hZ).1
          hfZ hZ.regular (hq.invariant surface hZ hflow) hmem S hle hrS hdS
        exact Finset.mem_union_right _ (hcoverI γ hγ hI)
      · exact Finset.mem_union_left _ (hcoverA γ hγ ⟨surface, hZ, hle, Or.inr hflow⟩)
    · exact Finset.mem_union_left _ (hcoverA γ hγ ⟨surface, hZ, hle, Or.inl hE⟩)
  have hAcard := proper_capacity A hm hA hcurve hcomp
  have hCcard := piece_surface_capacity C hm hC hposC
  have hFcard := threefold_pieces_capacity F hm hF hposF
  have hsum := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hsumI := Finset.card_union_le C.union F.union
  let p := (shape f).chamber
  let h := fatChart (shape f)
  change Γ.card ≤ ceilDiv (81879 * curveMass32 (shape f)) (32 * 46594) +
    ceilDiv (componentMass32 (shape f)) 32 + 20 * p.b * h.b ^ 2 +
    5 * 133671 * p.b * h.b + 1
  have hreserveC : C.union.card ≤ 5 * 133671 * p.b * h.b := by
    have ht := Nat.mul_le_mul_left 2 hdegC
    simp only [← Nat.mul_assoc] at ht
    change 4 * C.total ≤ 2 * 133671 * p.b * h.b at ht
    refine hCcard.trans (ht.trans ?_)
    gcongr
    decide
  have hreserveF : F.union.card ≤ 20 * p.b * h.b ^ 2 := by
    have ht := Nat.mul_le_mul_left 8 hdegF
    simp only [← Nat.mul_assoc] at ht
    refine hFcard.trans (ht.trans ?_)
    gcongr
    decide
  omega

end Hypersurface

section HighCurves
open Finset K1_13_7_1 K1_13_7_5

private theorem supported_sub {H : Shape} {F G : Jets}
    (hF : Supported H F) (hG : Supported H G) : Supported H (F - G) := by
  intro m hm
  rcases mem_union.mp (MvPolynomial.support_sub _ _ _ hm) with hm | hm
  · exact hF m hm
  · exact hG m hm

private theorem supported_C_mul {H : Shape} {F : Jets} (hF : Supported H F)
    (a : GeometricX) : Supported H (MvPolynomial.C a * F) := by
  intro m hm
  apply hF m
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  rw [MvPolynomial.coeff_C_mul] at hm
  exact right_ne_zero_of_mul hm

private theorem supported_C (H : Shape) (a : GeometricX) : Supported H (MvPolynomial.C a) := by
  classical
  by_cases ha : a = 0
  · simp [ha, Supported]
  intro m hm
  rw [MvPolynomial.support_C, ite_eq_right (fun h => (ha h).elim), mem_singleton] at hm
  subst m
  simp

private theorem supported_X {H : Shape} (hb : 1 ≤ H.b) (hj : 3 ≤ H.j) (ht : 1 ≤ H.t)
    (i : Fin 4) : Supported H (MvPolynomial.X i) := by
  intro m hm
  rw [MvPolynomial.support_X, mem_singleton] at hm
  subst m
  have hi : i.val ≤ H.j := (show i.val ≤ 3 by omega).trans hj
  refine ⟨by simpa, by simpa, ?_⟩
  simpa only [Finsupp.single_apply] using (show (if i = (3 : Fin 4) then 1 else 0) ≤ H.t by
    split <;> omega)

private theorem chamber_caps {f : Row 4} (hf : SmallFactor f) :
    1 ≤ (shape f).chamber.b ∧ 3 ≤ (shape f).chamber.j ∧ 1 ≤ (shape f).chamber.t := by
  have ht := hf.2.1
  change 0 < f.degreeOf 3 at ht
  obtain ⟨m, hm, htop⟩ : ∃ m ∈ f.support, 0 < m 3 := by
    by_contra! hz
    rw [MvPolynomial.degreeOf_eq_sup] at ht
    have hzero : f.support.sup (fun m : Fin 4 →₀ ℕ => m 3) ≤ 0 := Finset.sup_le_iff.mpr hz
    exact (not_lt_of_ge hzero) ht
  have hm3 : (3 : Fin 4) ∈ m.support := Finsupp.mem_support_iff.mpr (Nat.ne_of_gt htop)
  have hind : 3 ≤ (shape f).j := calc
    3 ≤ 3 * m 3 := by omega
    _ ≤ m.sum (fun i a => i.val * a) :=
      Finset.single_le_sum (f := fun i : Fin 4 => i.val * m i) (fun _ _ => Nat.zero_le _) hm3
    _ ≤ (shape f).j := by
      change _ ≤ f.support.sup (fun m => m.sum (fun i a => i.val * a))
      exact Finset.le_sup (f := fun m : Fin 4 →₀ ℕ => m.sum (fun i a => i.val * a)) hm
  exact ⟨by change 1 ≤ max (shape f).b (shape f).j; omega, hind, hf.2.1⟩

private theorem exists_coordinate_cut {r : PrimeSpectrum Jets} {y : JetPoint}
    (h : r.asIdeal < jetPointIdeal y) :
    ∃ i : Fin 4, MvPolynomial.X i - MvPolynomial.C (y i) ∉ r.asIdeal := by
  by_contra! hmem
  let π := Ideal.Quotient.mk r.asIdeal
  have hmaps : π = π.comp (MvPolynomial.C.comp (MvPolynomial.eval y)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      have heq := Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)
      rw [map_sub, sub_eq_zero] at heq
      simpa using heq
  apply not_le_of_gt h
  intro F hF
  have hz : MvPolynomial.eval y F = 0 := RingHom.mem_ker.mp hF
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π F = 0
  calc
    π F = π (MvPolynomial.C (MvPolynomial.eval y F)) := RingHom.congr_fun hmaps F
    _ = 0 := by rw [hz, map_zero, map_zero]

private theorem jetPoint_injective : Function.Injective jetPoint := by
  intro S T h
  have h0 := congrFun h (0 : Fin 4)
  have hi : Function.Injective genericCoeff :=
    (algebraMap GenericX GeometricX).injective.comp (IsFractionRing.injective Geom[X] GenericX)
  exact hi (by simpa [jetPoint, jet, Polynomial.hasseDeriv_zero'] using h0)

private theorem chart_section {H : Shape} (C : ValueChart H) (i : I) (a : K) :
    Supported H (C.numerator i - MvPolynomial.C (constantCoeff a) * C.denominator) :=
  supported_sub (C.numerator_supported i) (supported_C_mul C.denominator_supported _)

private theorem eval_chart_section {H : Shape} {C : ValueChart H} {S : K[X]}
    (hS : C.recovers S) (i : I) (a : K) :
    MvPolynomial.eval (jetPoint (extend S))
        (C.numerator i - MvPolynomial.C (constantCoeff a) * C.denominator) = 0 ↔
      S.eval (node i) = a := by
  have hinj : Function.Injective constantCoeff := constantCoeff.injective
  rw [map_sub, map_mul, MvPolynomial.eval_C, hS.2 i, sub_eq_zero]
  exact ⟨fun h => hinj (mul_right_cancel₀ hS.1 h), fun h => by rw [h]⟩

/-- One largest proper value section bounds the nonpersistent occupancy of a piece. -/
private theorem choose_section {w Γ s} (hm : LowFat6921.Messages w Γ s) {H : Shape} (C : ValueChart H)
    (hC : ∀ γ ∈ Γ, C.recovers (s γ)) {r : PrimeSpectrum Jets}
    (hr : ∀ γ ∈ Γ, r.asIdeal ≤ jetPointIdeal (jetPoint (extend (s γ)))) :
    ∃ (F : Jets) (selected : Finset JetPoint), Supported H F ∧ F ∉ r.asIdeal ∧
      (∀ y ∈ selected, r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y F = 0) ∧
      46594 * Γ.card ≤ 81879 * selected.card + 46594 := by
  classical
  let proper := (univ : Finset I).filter (fun i => ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i)
  let hits (i : I) := Γ.filter (fun γ => (s γ).eval (node i) = w i)
  by_cases h : proper.Nonempty
  · obtain ⟨i, hi, hmax⟩ := proper.exists_max_image (fun i => (hits i).card) h
    let F : Jets := C.numerator i - MvPolynomial.C (constantCoeff (w i)) * C.denominator
    let toPoint (γ : K) := jetPoint (extend (s γ))
    let selected := (hits i).image toPoint
    have hcard : selected.card = (hits i).card := Finset.card_image_of_injOn (by
      intro a ha b hb hab
      exact hm.distinct (filter_subset _ _ ha) (filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective (jetPoint_injective hab)))
    refine ⟨F, selected, chart_section C i (w i), ?_, ?_, ?_⟩
    · intro hF
      obtain ⟨γ, hγ, hne⟩ := (mem_filter.mp hi).2
      exact hne ((eval_chart_section (hC γ hγ) i (w i)).mp (RingHom.mem_ker.mp (hr γ hγ hF)))
    · intro y hy
      obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hy
      exact ⟨hr γ (mem_filter.mp hγ).1,
        (eval_chart_section (hC γ (mem_filter.mp hγ).1) i (w i)).mpr (mem_filter.mp hγ).2⟩
    · rw [hcard]
      exact LowPrice6921.section_capacity hm _ (fun j hj => hmax j (mem_filter.mpr ⟨mem_univ _, hj⟩))
  · refine ⟨1, ∅, ?_, r.isPrime.one_notMem, by simp, ?_⟩
    · simpa only [map_one] using supported_C H (1 : GeometricX)
    · apply LowPrice6921.section_capacity hm 0
      intro i hi
      exact (h ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩).elim

private theorem choose_linear_cut {f : Row 4} (hf : SmallFactor f)
    {r : PrimeSpectrum Jets} {y : JetPoint} (h : r.asIdeal < jetPointIdeal y) :
    ∃ F : Jets, Supported (shape f).chamber F ∧ F ∉ r.asIdeal ∧
      r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y F = 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_cut h
  obtain ⟨hb, hj, ht⟩ := chamber_caps hf
  exact ⟨MvPolynomial.X i - MvPolynomial.C (y i),
    supported_sub (supported_X hb hj ht i) (supported_C _ _), hi, h.le, by simp⟩

private theorem weighted_ceil (weight gain gap : ℕ) {n a b capA capB : ℕ}
    (hpos : 0 < weight * gap) (h : gap * n ≤ gain * a + gap * b)
    (ha : weight * a ≤ capA) (hb : weight * b ≤ capB) :
    n ≤ ceilDiv (gain * capA + gap * capB) (weight * gap) := by
  have hscaled : n * (weight * gap) ≤ gain * capA + gap * capB := calc
    _ = weight * (gap * n) := by ac_rfl
    _ ≤ weight * (gain * a + gap * b) := Nat.mul_le_mul_left _ h
    _ = gain * (weight * a) + gap * (weight * b) := by
      rw [Nat.mul_add]
      congr 1 <;> ac_rfl
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ ha) (Nat.mul_le_mul_left _ hb)
  unfold ceilDiv
  exact (Nat.le_div_iff_mul_le hpos).mpr (by omega)

theorem high_curve_count (w : I → K) {Γ s} (hm : LowFat6921.Messages w Γ s)
    (f : Row 4) (hf : SmallFactor f) (_ : FatEligible (shape f))
    (hOn : ∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ RegularAt f (extend (s γ)))
    (P Q : Row 3) (hpq : ProperLowerPair P Q)
    (hbP : LowerCaps P 952630000 322000000) (hbQ : LowerCaps Q 952630000 322000000)
    (hHigh : ∀ γ ∈ Γ, HighCurve P Q (lowerPoint (extend (s γ)))) :
    Γ.card ≤ highCurvePrice (shape f) := by
  classical
  have h1 := Geometry.K1_13_7_5_1
  have h2 := Geometry.K1_13_7_5_2
  have h3 := Geometry.K1_13_7_5_3
  have hlift (γ : K) (hγ : γ ∈ Γ) :=
    h1 f P Q (extend (s γ)) hf hpq (hOn γ hγ).1 (hHigh γ hγ)
  choose lift hLift hPoint using hlift
  let R := Γ.attach.image (fun γ : {a // a ∈ Γ} => lift γ.val γ.property)
  let piece (r : PrimeSpectrum Jets) := Γ.filter (fun γ =>
    r.asIdeal ≤ jetPointIdeal (jetPoint (extend (s γ))))
  have hR (r : PrimeSpectrum Jets) (hr : r ∈ R) :
      LiftedCurve f P Q r ∧ ∃ γ ∈ Γ, r.asIdeal < jetPointIdeal (jetPoint (extend (s γ))) := by
    obtain ⟨γ, _, rfl⟩ := mem_image.mp hr
    exact ⟨hLift γ.val γ.property, γ.val, γ.property, hPoint γ.val γ.property⟩
  have hcover : Γ.card ≤ ∑ r ∈ R, (piece r).card := by
    refine (card_le_card (t := R.biUnion piece) ?_).trans card_biUnion_le
    intro γ hγ
    exact mem_biUnion.mpr ⟨lift γ hγ, mem_image.mpr ⟨Subtype.mk γ hγ, mem_attach _ _, rfl⟩,
      mem_filter.mpr ⟨hγ, (hPoint γ hγ).le⟩⟩
  obtain ⟨C, hC⟩ := h2 f hf
  have hsections (r : PrimeSpectrum Jets) :
      ∃ (F : Jets) (selected : Finset JetPoint), Supported (fatChart (shape f)) F ∧ F ∉ r.asIdeal ∧
        (∀ y ∈ selected, r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y F = 0) ∧
        46594 * (piece r).card ≤ 81879 * selected.card + 46594 :=
    choose_section (hm.mono (filter_subset _ _)) C
      (fun γ hγ => hC (s γ) (hm.old_degree γ (mem_filter.mp hγ).1)
        (hOn γ (mem_filter.mp hγ).1).1 (hOn γ (mem_filter.mp hγ).1).2)
      (fun _ hγ => (mem_filter.mp hγ).2)
  choose cut selected hCut hProper hY hFee using hsections
  have hDegree := h3 f P Q hf hpq hbP hbQ R (fun r hr => (hR r hr).1)
    (fatChart (shape f)) (Or.inl rfl) cut selected (fun r _ => ⟨hCut r, hProper r, hY r⟩)
  have hlinear (r : PrimeSpectrum Jets) : ∃ (F : Jets) (singlePoint : Finset JetPoint),
      (r ∈ R → Supported (shape f).chamber F ∧ F ∉ r.asIdeal ∧
        ∀ y ∈ singlePoint, r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y F = 0) ∧
      (r ∈ R → singlePoint.card = 1) := by
    by_cases hr : r ∈ R
    · obtain ⟨γ, _, hpoint⟩ := (hR r hr).2
      obtain ⟨F, hF, hproper, hmem, hzero⟩ := choose_linear_cut hf hpoint
      exact ⟨F, {jetPoint (extend (s γ))}, fun _ => ⟨hF, hproper, by simpa using And.intro hmem hzero⟩, fun _ => by simp⟩
    · exact ⟨0, ∅, fun h => (hr h).elim, fun h => (hr h).elim⟩
  choose linear singlePoint hLinear hOne using hlinear
  have hCount := h3 f P Q hf hpq hbP hbQ R (fun r hr => (hR r hr).1)
    (shape f).chamber (Or.inr rfl) linear singlePoint hLinear
  rw [sum_congr rfl hOne, sum_const, smul_eq_mul, Nat.mul_one] at hCount
  have hsum : 46594 * Γ.card ≤ 81879 * (∑ r ∈ R, (selected r).card) + 46594 * R.card := calc
    _ ≤ 46594 * (∑ r ∈ R, (piece r).card) := Nat.mul_le_mul_left _ hcover
    _ = ∑ r ∈ R, 46594 * (piece r).card := mul_sum ..
    _ ≤ ∑ r ∈ R, (81879 * (selected r).card + 46594) := sum_le_sum fun r _ => hFee r
    _ = _ := by rw [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, Nat.mul_comm R.card]
  change Γ.card ≤ ceilDiv
    (81879 * mixed32 (shape f).chamber lowerBox lowerBox (fatChart (shape f)) +
      46594 * mixed32 (shape f).chamber lowerBox lowerBox (shape f).chamber)
    (32 * 46594 * threshold)
  rw [Nat.mul_right_comm 32 46594 threshold]
  exact weighted_ceil (32 * threshold) 81879 46594 (by decide) hsum hDegree hCount

end HighCurves

theorem fat_count (w : I → K) {Γ s} (hmsg : LowFat6921.Messages w Γ s)
    (f : Row 4) (hf : SmallFactor f) (hon : ∀ γ ∈ Γ, OnFactor f (extend (s γ)))
    (helig : FatEligible (shape f)) (E : FatEquations)
    (hE : ∀ γ ∈ Γ, E.holds (extend (s γ))) :
    Γ.card ≤ fatPrice (shape f) := by
  classical
  have h1 := singular_count
  have h2 := hypersurface_count
  have h3 := Geometry.K1_13_7_3
  have h4 := Geometry.K1_13_7_4
  have h5 := high_curve_count
  have h6 := Geometry.K1_13_7_6
  obtain ⟨D, P, Q, hD, hDb, hPb, hQb, hpq, hres⟩ := h3 E
  obtain ⟨R, hRb, hstrata⟩ := h4 P Q hpq hPb hQb
  let S : K → Geom[X] := fun γ => extend (s γ)
  let singular := Γ.filter (fun γ => ¬ RegularAt f (S γ))
  let divisors := Γ.filter (fun γ => RegularAt f (S γ) ∧ atJet D (S γ) = 0)
  let curves := Γ.filter (fun γ => RegularAt f (S γ) ∧ HighCurve P Q (lowerPoint (S γ)))
  let isolated := Γ.filter (fun γ => IsolatedFat P Q R (lowerPoint (S γ)))
  have hsingular : singular.card ≤ singularPrice (shape f) :=
    h1 w (Γ := singular) (s := s) (hmsg.mono (Finset.filter_subset _ _)) f hf helig
      (fun γ hγ => ⟨hon γ (Finset.mem_filter.mp hγ).1, (Finset.mem_filter.mp hγ).2⟩)
  have hdivisors : divisors.card ≤ hypersurfacePrice (shape f) :=
    h2 w (Γ := divisors) (s := s) (hmsg.mono (Finset.filter_subset _ _)) f hf helig
      (fun γ hγ => ⟨hon γ (Finset.mem_filter.mp hγ).1, (Finset.mem_filter.mp hγ).2.1⟩)
      D hD hDb (fun _ hγ => (Finset.mem_filter.mp hγ).2.2)
  have hcurves : curves.card ≤ highCurvePrice (shape f) :=
    h5 w (Γ := curves) (s := s) (hmsg.mono (Finset.filter_subset _ _)) f hf helig
      (fun γ hγ => ⟨hon γ (Finset.mem_filter.mp hγ).1, (Finset.mem_filter.mp hγ).2.1⟩)
      P Q hpq hPb hQb (fun _ hγ => (Finset.mem_filter.mp hγ).2.2)
  have hisolated : isolated.card ≤ isolatedPrice := by
    let points := isolated.image (fun γ => lowerPoint (S γ))
    have hinj : Set.InjOn (fun γ => lowerPoint (S γ)) (isolated : Set K) := by
      intro a ha b hb hab
      exact hmsg.distinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective (lowerPoint_injective hab))
    have hcard : points.card = isolated.card := Finset.card_image_of_injOn hinj
    rw [← hcard]
    apply h6 P Q R hPb hQb hRb points
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hγ).2
  have hcover : Γ ⊆ singular ∪ divisors ∪ curves ∪ isolated := by
    intro γ hγ
    by_cases hr : RegularAt f (S γ)
    · rcases hres (S γ) (hE γ hγ) with hd | ⟨hp, hq⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hr, hd⟩)))
      · rcases hstrata (S γ) hp hq with hc | hi
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hγ, hr, hc⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hi⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)))
  have hunion := Finset.card_le_card hcover
  have hunion₁ := Finset.card_union_le singular divisors
  have hunion₂ := Finset.card_union_le (singular ∪ divisors) curves
  have hunion₃ := Finset.card_union_le (singular ∪ divisors ∪ curves) isolated
  rw [fat_price_sum]
  omega

end
end LowPrice6921
