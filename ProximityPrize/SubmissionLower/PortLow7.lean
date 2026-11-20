import ProximityPrize.SubmissionLower.PortLow6
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_9_7
noncomputable section
open K1_13 (Shape chart ceilDiv mixed32)
open P0_9 (linearChart taylorLength physicalDegree incidenceGap)
def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
def divisorBox : Shape := ⟨6300 + 952630000 / 33184, 2403 + 322000000 / 33184, 0⟩
theorem divisorBox_eq : divisorBox = ⟨35007, 12106, 0⟩ := by
  have hb : 6300 + 952630000 / 33184 = 35007 := by decide
  have hj : 2403 + 322000000 / 33184 = 12106 := by decide
  unfold divisorBox
  rw [hb, hj]
def hypersurfacePrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := fatChart x
  let big := divisorBox
  let cut : Shape :=
    ⟨max (max h.b big.b) (max h.j (big.j + 1)), max h.j (big.j + 1), max 1 h.t⟩
  ceilDiv (P0.t * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b ^ 2 + 5 * physicalDegree * p.b * h.b + 1
def singularPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := fatChart x
  if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b ^ 2 + 1 else 0
def highCurvePrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := fatChart x
  let q : Shape := ⟨952630000, 322000000, 0⟩
  ceilDiv (P0.t * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * 293711590)
theorem fat_price_sum (x : Shape) : P0_9.fatPrice x =
    hypersurfacePrice x + singularPrice x + highCurvePrice x + K1_13_7.isolatedPrice := rfl
end
end P0_9_7
end
section
namespace P0_9_7
theorem buy_divisors : K1_13_7.c3 :=
  K1_13_7_3.of_children K1_13_7_3_1.proof K1_13_7_3_2.proof
theorem residual_strata : K1_13_7.c4 :=
  K1_13_7_4.of_children K1_13_7_4_1.proof
    (K1_13_7_4_2.of_children K1_13_7_4_2_1.proof K1_13_7_4_2_2.proof)
theorem isolated_bound : K1_13_7.c6 :=
  K1_13_7_6.of_children K1_13_7_6_1.proof
    (K1_13_7_6_2.of_children K1_13_7_6_2_1.proof K1_13_7_6_2_2.proof)
end P0_9_7
end
section
namespace P0_9_7
noncomputable section
open Polynomial
open P0 (K)
open P0_9 (Messages SmallFactor)
open K1_13 (FatEligible Row atJet embed extend OnFactor shape)
open K1_13_7 (RegularAt LowerCaps ProperLowerPair HighCurve IsolatedFat lowerPoint
  lowerPoint_injective isolatedPrice)
def c1 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → FatEligible (shape f) →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ ¬ RegularAt f (extend (s γ))) →
    Γ.card ≤ singularPrice (shape f)
def c2 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → FatEligible (shape f) →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ RegularAt f (extend (s γ))) →
    ∀ D : Row 3, D ≠ 0 → LowerCaps D divisorBox.b divisorBox.j →
      (∀ γ ∈ Γ, atJet D (extend (s γ)) = 0) → Γ.card ≤ hypersurfacePrice (shape f)
def c3 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → FatEligible (shape f) →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ RegularAt f (extend (s γ))) →
    ∀ P Q : Row 3, ProperLowerPair P Q →
      LowerCaps P 952630000 322000000 → LowerCaps Q 952630000 322000000 →
      (∀ γ ∈ Γ, HighCurve P Q (lowerPoint (extend (s γ)))) →
      Γ.card ≤ highCurvePrice (shape f)
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : P0_9.c7 := by
  classical
  intro w Γ s hmsg f hf hon helig E hE
  obtain ⟨D, P, Q, hD, hDb, hPb, hQb, hpq, hres⟩ := buy_divisors E
  obtain ⟨R, hRb, hstrata⟩ := residual_strata P Q hpq hPb hQb
  let S : K → K1_13.Geom[X] := fun γ => extend (s γ)
  let singular := Γ.filter (fun γ => ¬ RegularAt f (S γ))
  let divisors := Γ.filter (fun γ => RegularAt f (S γ) ∧ atJet D (S γ) = 0)
  let curves := Γ.filter (fun γ => RegularAt f (S γ) ∧ HighCurve P Q (lowerPoint (S γ)))
  let isolated := Γ.filter (fun γ => IsolatedFat P Q R (lowerPoint (S γ)))
  have hsingular : singular.card ≤ singularPrice (shape f) :=
    h1 w singular s (hmsg.mono (Finset.filter_subset _ _)) f hf helig
      (fun γ hγ => ⟨hon γ (Finset.mem_filter.mp hγ).1, (Finset.mem_filter.mp hγ).2⟩)
  have hdivisors : divisors.card ≤ hypersurfacePrice (shape f) :=
    h2 w divisors s (hmsg.mono (Finset.filter_subset _ _)) f hf helig
      (fun γ hγ => ⟨hon γ (Finset.mem_filter.mp hγ).1, (Finset.mem_filter.mp hγ).2.1⟩)
      D hD (by simpa only [divisorBox_eq] using hDb) (fun _ hγ => (Finset.mem_filter.mp hγ).2.2)
  have hcurves : curves.card ≤ highCurvePrice (shape f) :=
    h3 w curves s (hmsg.mono (Finset.filter_subset _ _)) f hf helig
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
    apply isolated_bound P Q R hPb hQb hRb points
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hγ).2
  have hcover : Γ ⊆ divisors ∪ singular ∪ curves ∪ isolated := by
    intro γ hγ
    by_cases hr : RegularAt f (S γ)
    · rcases hres (S γ) (hE γ hγ) with hd | ⟨hp, hq⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr, hd⟩)))
      · rcases hstrata (S γ) hp hq with hc | hi
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hγ, hr, hc⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hi⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)))
  rw [fat_price_sum]
  calc
    Γ.card ≤ (divisors ∪ singular ∪ curves ∪ isolated).card := Finset.card_le_card hcover
    _ ≤ (divisors ∪ singular ∪ curves).card + isolated.card := Finset.card_union_le _ _
    _ ≤ (divisors ∪ singular).card + curves.card + isolated.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ divisors.card + singular.card + curves.card + isolated.card :=
      Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hdivisors hsingular) hcurves) hisolated
end
end P0_9_7
end
section
namespace P0_9_7_1
theorem sparse_bound : K1_13_7_1.c1 :=
  K1_13_7_1_1.of_children
    (K1_13_7_1_1_1.of_children
      (K1_13_7_1_1_1_1.of_children K1_13_7_1_1_1_1_1.proof K1_13_7_1_1_1_1_2.proof)
      (K1_13_7_1_1_1_2.of_children K1_13_7_1_1_1_2_1.proof K1_13_7_1_1_1_2_2.proof))
    K1_13_7_1_1_2.proof
theorem surface_sections : K1_13_7_1.c2 :=
  K1_13_7_1_2.of_children K1_13_7_1_2_1.proof
    (K1_13_7_1_2_2.of_children
      (K1_13_7_1_2_2_1.of_children K1_13_7_1_2_2_1_1.proof K1_13_7_1_2_2_1_2.proof)
      (K1_13_7_1_2_2_2.of_children K1_13_7_1_2_2_2_1.proof K1_13_7_1_2_2_2_2.proof))
end P0_9_7_1
end
section
namespace P0_9_7_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6 K1_13_7 K1_13_7_1
open private topAt eval_topAt topAt_coeff topView_separant from ProximityPrize.SubmissionLower.Fast056
theorem regular_derivative (f : Row 4) (S : Geom[X])
    (hf : P0_9.SmallFactor f) (hon : OnFactor f S) (hs : atJet (separant f) S = 0) :
    ∃ j, 0 < j ∧ j < (shape f).t ∧
      atJet ((separant^[j]) f) S = 0 ∧ atJet (separant ((separant^[j]) f)) S ≠ 0 := by
  classical
  let t := (shape f).t
  let P := topAt S f
  have hdeg : P.natDegree ≤ t := Polynomial.natDegree_map_le.trans_eq (topView_degree f)
  have hnz : (derivative^[t] P).coeff 0 ≠ 0 := by
    rw [coeff_iterate_derivative, Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul]
    change (t.factorial : Geom[X]) * P.coeff t ≠ 0
    rw [← map_natCast (Polynomial.C : Geom →+* Geom[X])]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      (factorial_cast_ne_zero (hf.2.2.1.2.2.trans_lt (by decide : 10 < K1.p))))
      (by simpa only [P, t, topAt_coeff] using hon.2)
  have hc : derivative^[t] P = Polynomial.C ((derivative^[t] P).coeff 0) :=
    eq_C_of_natDegree_le_zero ((natDegree_iterate_derivative _ _).trans
      (by omega : P.natDegree - t ≤ 0))
  have he (k : ℕ) : atJet ((separant^[k]) f) S =
      (derivative^[k] P).eval (jet S (3 : Fin 4)) := by
    rw [← eval_topAt]
    congr 1
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Function.iterate_succ_apply']
      change (topView (separant ((separant^[k]) f))).map (MvPolynomial.eval (jet S)) = _
      rw [topView_separant, ← derivative_map]
      exact congrArg derivative ih
  have hex : ∃ k, atJet ((separant^[k]) f) S ≠ 0 := by
    refine ⟨t, ?_⟩
    rw [he, hc, Polynomial.eval_C]
    exact hnz
  let k := Nat.find hex
  have hk : atJet ((separant^[k]) f) S ≠ 0 := Nat.find_spec hex
  have hkt : k ≤ t := Nat.find_min' hex (by
    rw [he, hc, Polynomial.eval_C]
    exact hnz)
  have hk0 : k ≠ 0 := by
    intro h
    apply hk
    simpa only [h, Function.iterate_zero_apply] using hon.1
  have hk1 : k ≠ 1 := by
    intro h
    apply hk
    simpa only [h, Function.iterate_one] using hs
  have hprev : k - 1 + 1 = k := by omega
  refine ⟨k - 1, by omega, by omega, ?_, ?_⟩
  · exact not_ne_iff.mp (Nat.find_min hex (by omega : k - 1 < k))
  · have he' : (separant^[k]) f = separant ((separant^[k - 1]) f) := by
      conv_lhs => rw [← hprev]
      rw [Function.iterate_succ_apply']
    simpa only [he'] using hk
private def derivativeBox (p : Shape) : Shape := ⟨p.b - 1, p.j - 3, p.t - 1⟩
private theorem derivative_box (f : Row 4) {j : ℕ} (hj : 0 < j) :
    InBox (shape ((separant^[j]) f)) (derivativeBox (shape f).chamber) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  rw [Function.iterate_succ_apply]
  have h := derivative_in_box (separant f) k
  have hb : (shape (separant f)).b ≤ (shape f).b - 1 := by
    have hd := weightedTotalDegree_pderiv_le_sub (1 : Fin 4 → ℕ) 3 f
    simpa only [shape, weightedTotalDegree_one, Pi.one_apply, separant] using hd
  have hi : (shape (separant f)).j ≤ (shape f).j - 3 := by
    have hd := weightedTotalDegree_pderiv_le_sub (fun i : Fin 4 => i.val) 3 f
    have hthree : (3 : Fin 4).val = 3 := rfl
    simpa only [shape, indexDegree_eq, separant, hthree] using hd
  have ht : (shape (separant f)).t ≤ (shape f).t - 1 := by
    simpa only [Function.iterate_one] using derivative_degree f 1
  exact ⟨h.1.trans (hb.trans (Nat.sub_le_sub_right (le_max_left _ _) 1)),
    h.2.1.trans hi, h.2.2.trans ht⟩
private theorem chart_le (p : Shape) (hp : Chamber p) (ht : 1 < p.t) (hb : p.b ≤ 60) :
    InBox (chart (K1_13.taylorLength + 4) (derivativeBox p))
      (chart (P0_9.taylorLength + 4) p) := by
  obtain ⟨hjb, htj⟩ := hp
  have hB : 1 + 267352 * (p.b - 1 - 1) ≤ 1 + 267112 * (p.b - 1) := by omega
  have hJ : 267352 * (p.j - 3 - 3) + 133676 + 3 ≤
      267112 * (p.j - 3) + 133556 + 3 := by omega
  have hT : 267352 * (p.t - 1 - 1) + 133676 + 1 ≤
      267112 * (p.t - 1) + 133556 + 1 := by omega
  exact ⟨max_le_max hB hJ, hJ, min_le_min hT (Nat.div_le_div_right hJ)⟩
theorem exists_derivative_chart (f : Row 4) (he : FatEligible (shape f))
    (ht : 1 < (shape f).t) {j : ℕ} (hj : 0 < j) :
    let g := (separant^[j]) f
    ∃ C : TaylorChart, C.Fits (chart (P0_9.taylorLength + 4) (shape f).chamber) ∧
      ∀ S : Geom[X], atJet g S = 0 → RegularAt g S → C.Recovers S := by
  dsimp only
  let p := (shape f).chamber
  let q := derivativeBox p
  have hp : Chamber p := shape_chamber f
  have htp : 1 < p.t := ht
  have hpb : p.b ≤ 60 := max_le he.1 (he.2.trans (by decide))
  have hq : Chamber q := by
    obtain ⟨hjb, htj⟩ := hp
    change p.j - 3 ≤ p.b - 1 ∧ 3 * (p.t - 1) ≤ p.j - 3
    omega
  have htq : 0 < q.t := by
    change 0 < p.t - 1
    omega
  obtain ⟨C, hC, hrecover⟩ := exists_chart ((separant^[j]) f) q (derivative_box f hj) hq htq
  have hbox := chart_le p hp htp hpb
  have widen {P : GeoJets} (hP : GeoFits P (chart (K1_13.taylorLength + 4) q)) :
      GeoFits P (chart (P0_9.taylorLength + 4) p) :=
    ⟨hP.1.trans hbox.1, hP.2.1.trans hbox.2.1, hP.2.2.trans hbox.2.2⟩
  exact ⟨C, ⟨widen hC.1, fun i => widen (hC.2 i)⟩, hrecover⟩
end
end P0_9_7_1
end
section
namespace P0_9_7_2
noncomputable section
open Polynomial
open K1_13 (Geom Row Shape InBox shape mixed32)
open K1_13_6 (GeoJets toGeneric separant)
open K1_13_7_2 (evalTrajectory)
open P0_9 (taylorLength physicalDegree)
open P0_9_7 (fatChart divisorBox)
def cutBox (x : Shape) : Shape :=
  let h := fatChart x
  ⟨max (max h.b divisorBox.b) (max h.j (divisorBox.j + 1)),
    max h.j (divisorBox.j + 1), max 1 h.t⟩
def curveMass32 (x : Shape) : ℕ :=
  mixed32 x.chamber divisorBox (cutBox x) (fatChart x)
def componentMass32 (x : Shape) : ℕ :=
  mixed32 x.chamber divisorBox (cutBox x) x.chamber
structure FatTaylor (f : Row 4) where
  denom : Row 4
  numer : Fin taylorLength → Row 4
  test : Row 4
  denom_box : InBox (shape denom) (fatChart (shape f))
  numer_box : ∀ i, InBox (shape (numer i)) (fatChart (shape f))
  test_box : InBox (shape test) (fatChart (shape f))
  test_iff : ∀ (surface : Ideal GeoJets), surface.IsPrime → toGeneric f ∈ surface →
    toGeneric (separant f) ∉ surface →
    (toGeneric test ∈ surface ↔ toGeneric (P0_9_6.membershipTest f) ∈ surface)
  recovers : ∀ (L : Type) [Field L] [Algebra Geom L] (S : L[X]),
    S.natDegree ≤ physicalDegree → evalTrajectory f S = 0 →
    evalTrajectory (separant f) S ≠ 0 →
    evalTrajectory denom S ≠ 0 ∧ evalTrajectory test S = 0 ∧
      ∀ i, evalTrajectory (numer i) S = evalTrajectory denom S * C (S.coeff i.val)
abbrev CoeffRing := MvPolynomial (Fin taylorLength) Geom
def universalPolynomial : CoeffRing[X] :=
  ∑ i : Fin taylorLength, C (MvPolynomial.X i) * Polynomial.X ^ i.val
def universalEval (f : Row 4) : CoeffRing[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom (MvPolynomial.C : Geom →+* CoeffRing))
    (fun i => hasseDeriv i.val universalPolynomial) f
def coefficientPointIdeal (S : Geom[X]) : Ideal CoeffRing :=
  RingHom.ker (MvPolynomial.eval (fun i : Fin taylorLength => S.coeff i.val))
structure ActualFamily (f : Row 4) (P : Ideal CoeffRing) : Prop where
  prime : P.IsPrime
  dimension : 2 ≤ (MvPolynomial.affineHilbertPolynomial P).natDegree
  solves : ∀ i, (universalEval f).coeff i ∈ P
  regular : ∃ i, (universalEval (separant f)).coeff i ∉ P
def IntegratedMark (f : Row 4) (S : Geom[X]) : Prop :=
  ∃ P, ActualFamily f P ∧ P ≤ coefficientPointIdeal S
end
end P0_9_7_2
end
section
namespace P0_9_7_2
noncomputable section
open K1_13 K1_13_6 K1_13_7 K1_13_7_2 K1_13_7_2_1 K1_13_7_2_1_2
open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial
open private geometric_injective liftLower_ne_zero from ProximityPrize.SubmissionLower.Fast070
open private local_length_one tangent_invariant from ProximityPrize.SubmissionLower.Fast070
open private top top_rename_lower top_map top_derivative from ProximityPrize.SubmissionLower.Fast070
private theorem proper_lift {f : Row 4} (hf : P0_9.SmallFactor f) {q : Row 3} (hq : q ≠ 0) :
    IsRelPrime (toGeneric f) (toGeneric (liftLower q)) := by
  apply (isRelPrime_iff_no_prime_factors (fun hz => hf.1.ne_zero
    (geometric_injective 4 (by simpa [toGeneric] using hz)))).mpr
  intro r hrf hrq hr
  obtain ⟨a, ha, he⟩ := comap_span_prime hr hf.1.ne_zero hrf
  have had {x : Row 4} (h : r ∣ toGeneric x) : a ∣ x := by
    apply Ideal.mem_span_singleton.mp
    rw [← he]
    exact Ideal.mem_span_singleton.mpr h
  have haf : a ∣ f := had hrf
  have hfa : f ∣ a := (ha.irreducible.associated_of_dvd hf.1 haf).dvd'
  obtain ⟨R, hR⟩ := hfa.trans (had hrq)
  have hRn : R ≠ 0 := fun hz => liftLower_ne_zero hq (by simp [hR, hz])
  have hdeg := degreeOf_liftLower q
  rw [hR, ← weightedTotalDegree_piSingle, weightedTotalDegree_mul _ _ _ hf.1.ne_zero hRn,
    weightedTotalDegree_piSingle, weightedTotalDegree_piSingle] at hdeg
  have := hf.2.1
  change 0 < f.degreeOf 3 at this
  omega
private theorem local_generators (f : Row 4) (q : Row 3)
    (hq : Squarefree (genericRow q)) (surface : Ideal GeoJets)
    (h : LiftedSurface f q surface) : LocalGenerators f q surface h.minimal.isPrime := by
  let : surface.IsPrime := h.minimal.isPrime
  let A := Localization.AtPrime surface
  let l : GeoJets →+* A := algebraMap GeoJets A
  let J := intersectionIdeal f (liftLower q)
  let e : GeoJets ≃ₐ[GeoField] Lower[X] := top
  let F := e (toGeneric f)
  have hlower (u : Row 3) : e (toGeneric (liftLower u)) = Polynomial.C (genericRow u) := by
    change top (MvPolynomial.map genericCoeffs (MvPolynomial.rename Fin.castSucc u)) = _
    rw [MvPolynomial.map_rename, top_rename_lower]
    rfl
  have hlead : e (toGeneric (liftLower (K1_13_1.anchorLead f))) = Polynomial.C F.leadingCoeff := by
    rw [hlower]
    congr 1
    change MvPolynomial.map genericCoeffs (top f).leadingCoeff =
      (top (MvPolynomial.map genericCoeffs f)).leadingCoeff
    have hinj : Function.Injective genericCoeffs :=
      (algebraMap GenericField GeoField).injective.comp
        (IsFractionRing.injective (Polynomial Geom) GenericField)
    rw [top_map, Polynomial.leadingCoeff_map_of_injective (MvPolynomial.map_injective _ hinj)]
  have hsep : e (toGeneric (separant f)) = F.derivative := by
    change top (MvPolynomial.map genericCoeffs (MvPolynomial.pderiv 3 f)) =
      (top (MvPolynomial.map genericCoeffs f)).derivative
    rw [← MvPolynomial.pderiv_map, top_derivative]
  have hJ : J.map e.toRingHom = Ideal.span {F, Polynomial.C (genericRow q)} := by
    change (Ideal.span {toGeneric f, toGeneric (liftLower q)}).map e.toRingHom = _
    rw [Ideal.map_span, Set.image_pair]
    change Ideal.span {F, e (toGeneric (liftLower q))} = _
    rw [hlower]
  have hqrad : (Ideal.span ({genericRow q} : Set Lower)).IsRadical :=
    isRadical_iff_span_singleton.mp (isRadical_iff_squarefree_or_zero.mpr (Or.inl hq))
  have hrad : (J.map l).radical ≤ J.map l := by
    rw [← IsLocalization.map_radical surface.primeCompl A J]
    apply Ideal.map_le_iff_le_comap.mpr
    intro g hg
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hg
    have hn' : e g ^ n ∈ Ideal.span {F, Polynomial.C (genericRow q)} := by
      rw [← hJ, ← map_pow]
      exact Ideal.mem_map_of_mem e.toRingHom hn
    obtain ⟨k, hk⟩ := clear_monic_cut F (e g) hqrad hn'
    let u := toGeneric (liftLower (K1_13_1.anchorLead f)) ^ k * toGeneric (separant f)
    have hu : u ∉ surface := h.minimal.isPrime.mul_notMem
      (fun hm => h.leading (h.minimal.isPrime.mem_of_pow_mem _ hm)) h.regular
    have humem : u * g ∈ J := by
      have hc : (J.map e.toRingHom).comap e.toRingHom = J :=
        Ideal.comap_map_of_bijective e.toRingHom e.bijective
      rw [← hc, Ideal.mem_comap, hJ]
      change e (u * g) ∈ _
      simpa only [u, map_mul, map_pow, hlead, hsep, mul_assoc] using hk
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff surface.primeCompl A J g).mpr
      ⟨u, hu, humem⟩
  change J.map l = IsLocalRing.maximalIdeal A
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal surface A,
      ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes A surface J h.minimal]
  exact le_antisymm Ideal.le_radical hrad
theorem reduce (f : Row 4) (hf : P0_9.SmallFactor f)
    (D : Row 3) (hD : D ≠ 0) (hcap : LowerCaps D 35007 12106) :
    ∃ q : Row 3, ReducedCut f D q := by
  obtain ⟨q, hq, hdvd, hqcap, hsq, hroots⟩ := reduced_divisor D hD hcap
  have hgeom := K1_13_7_2_1_1.proof q hsq (hqcap.1.trans_lt (by decide))
  have hproper := proper_lift hf hq
  have hlocal (surface : Ideal GeoJets) (h : LiftedSurface f q surface) :
      LocalGenerators f q surface h.minimal.isPrime := local_generators f q hgeom surface h
  exact ⟨q, hq, hdvd, hqcap, hgeom, hproper, hroots, lowerFlow_box hqcap,
    fun surface h => ⟨lifted_height hf.1.ne_zero hproper h,
      local_length_one h.minimal.isPrime (hlocal surface h)⟩,
    fun surface h => tangent_invariant h (hlocal surface h)⟩
end
end P0_9_7_2
end
section
set_option autoImplicit false
namespace P0_9_7_2_3
noncomputable section
open Polynomial MvPolynomial
open K1_13 (Geom Row)
open K1_13_6 (GeoField GeoJets toGeneric separant)
open K1_13_6_3 (JetIdeal dimension geomConstants genericArgument)
open P0_9 (taylorLength)
open P0_9_7_2 (CoeffRing FatTaylor)
abbrev CoeffIdeal := Ideal CoeffRing
abbrev FreshCoeffRing := MvPolynomial (Fin taylorLength) GeoField
def jetLinear {k : Type*} [Field k] (a : k) (i : ℕ) :
    MvPolynomial (Fin taylorLength) k :=
  ∑ j : Fin taylorLength,
    MvPolynomial.C ((j.val.choose i : k) * a ^ (j.val - i)) * MvPolynomial.X j
def extendIdeal (A : CoeffIdeal) : Ideal FreshCoeffRing :=
  A.map (MvPolynomial.map geomConstants)
def freshJetMap : GeoJets →+* FreshCoeffRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => jetLinear genericArgument i.val)
def freshImage (A : CoeffIdeal) : JetIdeal :=
  (extendIdeal A).comap freshJetMap
def FreshBirational (A : CoeffIdeal) : Prop :=
  ∀ h : FreshCoeffRing, ∃ u v : GeoJets,
    freshJetMap v ∉ extendIdeal A ∧ h * freshJetMap v - freshJetMap u ∈ extendIdeal A
structure FreshChart (f : Row 4) (T : FatTaylor f) (A : CoeffIdeal) : Prop where
  extended_prime : (extendIdeal A).IsPrime
  dimension_eq : dimension (freshImage A) = dimension A
  factor : toGeneric f ∈ freshImage A
  regular : toGeneric (separant f) ∉ freshImage A
  test : toGeneric T.test ∈ freshImage A
  denom : toGeneric T.denom ∉ freshImage A
  recovers : ∀ i, MvPolynomial.X i * freshJetMap (toGeneric T.denom) -
    freshJetMap (toGeneric (T.numer i)) ∈ extendIdeal A
end
end P0_9_7_2_3
end
section
namespace P0_9_7_2_3
noncomputable section
open Polynomial MvPolynomial
open K1_13 (Geom Row shape)
open K1_13_6 (GeoJets GeoField GenericField toGeneric genericCoeffs divisorIdeal)
open K1_13_6_3 (JetIdeal dimension geomConstants)
open K1_13_7_2_5 (wholeComponents properComponents)
open P0_9_7 (fatChart)
open P0_9_7_2 (CoeffRing FatTaylor)
open scoped BigOperators
private theorem common_clearing {f : Row 4} (T : FatTaylor f) (g : FreshCoeffRing) :
    ∃ (u : GeoJets) (n : ℕ), ∀ A : CoeffIdeal, FreshChart f T A →
      g * freshJetMap (toGeneric T.denom) ^ n - freshJetMap u ∈ extendIdeal A := by
  let D := toGeneric T.denom
  let d := freshJetMap D
  induction g using MvPolynomial.induction_on with
  | C c =>
    refine ⟨MvPolynomial.C c, 0, ?_⟩
    intro A _
    simp only [pow_zero, mul_one, freshJetMap, MvPolynomial.eval₂Hom_C, sub_self, Ideal.zero_mem]
  | add p q hp hq =>
    obtain ⟨u, n, hu⟩ := hp
    obtain ⟨v, m, hv⟩ := hq
    refine ⟨u * D ^ m + v * D ^ n, n + m, ?_⟩
    intro A hA
    let J := extendIdeal A
    have hpu := J.mul_mem_right (d ^ m) (hu A hA)
    have hqv := J.mul_mem_right (d ^ n) (hv A hA)
    have he : (p + q) * d ^ (n + m) - freshJetMap (u * D ^ m + v * D ^ n) =
        (p * d ^ n - freshJetMap u) * d ^ m + (q * d ^ m - freshJetMap v) * d ^ n := by
      have hd : freshJetMap D = d := rfl
      simp only [map_add, map_mul, map_pow, hd, pow_add]
      ring
    change (p + q) * d ^ (n + m) - freshJetMap (u * D ^ m + v * D ^ n) ∈ J
    rw [he]
    exact J.add_mem hpu hqv
  | mul_X p i hp =>
    obtain ⟨u, n, hu⟩ := hp
    let v := toGeneric (T.numer i)
    refine ⟨u * v, n + 1, ?_⟩
    intro A hA
    let J := extendIdeal A
    have hpu := J.mul_mem_right (MvPolynomial.X i * d) (hu A hA)
    have hiv := J.mul_mem_left (freshJetMap u) (hA.recovers i)
    have he : p * MvPolynomial.X i * d ^ (n + 1) - freshJetMap (u * v) =
        (p * d ^ n - freshJetMap u) * (MvPolynomial.X i * d) +
          freshJetMap u * (MvPolynomial.X i * d - freshJetMap v) := by
      rw [map_mul, pow_succ]
      ring
    change p * MvPolynomial.X i * d ^ (n + 1) - freshJetMap (u * v) ∈ J
    rw [he]
    exact J.add_mem hpu hiv
theorem fresh_birational {f : Row 4} {T : FatTaylor f} {A : CoeffIdeal}
    (h : FreshChart f T A) : FreshBirational A := by
  intro g
  obtain ⟨u, n, hu⟩ := common_clearing T g
  refine ⟨u, toGeneric T.denom ^ n, ?_, ?_⟩
  · rw [map_pow]
    exact fun hz => h.denom (h.extended_prime.mem_of_pow_mem _ hz)
  · rw [map_pow]
    exact hu A h
private theorem original_mem {B : CoeffIdeal} (hB : B.IsPrime) {g : CoeffRing}
    (hg : MvPolynomial.map geomConstants g ∈ extendIdeal B) : g ∈ B := by
  rw [← hB.radical, ← vanishingIdeal_zeroLocus_eq_radical (K := Geom)]
  intro x hx
  let ψ := MvPolynomial.eval (geomConstants ∘ x)
  have hψ : ψ.comp (MvPolynomial.map geomConstants) = geomConstants.comp (MvPolynomial.eval x) := by
    apply RingHom.ext
    intro q
    exact (eval_map _ _ _).trans (eval₂_comp _ _ _).symm
  have hker : extendIdeal B ≤ RingHom.ker ψ := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro q hq
    change ψ (MvPolynomial.map geomConstants q) = 0
    rw [← RingHom.comp_apply, hψ, RingHom.comp_apply]
    have hq0 : MvPolynomial.eval x q = 0 := hx q hq
    rw [hq0, map_zero]
  have hv := RingHom.mem_ker.mp (hker hg)
  change (ψ.comp (MvPolynomial.map geomConstants)) g = 0 at hv
  rw [hψ, RingHom.comp_apply, ← map_zero geomConstants] at hv
  exact geomConstants.injective hv
theorem le_of_freshImage_le {f : Row 4} {T : FatTaylor f} {A B : CoeffIdeal}
    (hA : FreshChart f T A) (hB : FreshChart f T B) (hp : B.IsPrime)
    (hle : freshImage A ≤ freshImage B) : A ≤ B := by
  intro g hg
  apply original_mem hp
  let q := MvPolynomial.map geomConstants g
  have hq : q ∈ extendIdeal A := Ideal.mem_map_of_mem _ hg
  obtain ⟨u, n, hu⟩ := common_clearing T q
  let d := freshJetMap (toGeneric T.denom)
  have huA : u ∈ freshImage A := by
    change freshJetMap u ∈ extendIdeal A
    have hm := (extendIdeal A).mul_mem_right (d ^ n) hq
    simpa only [d, sub_sub_cancel] using (extendIdeal A).sub_mem hm (hu A hA)
  have hm : q * d ^ n ∈ extendIdeal B := by
    have huB : freshJetMap u ∈ extendIdeal B := hle huA
    simpa only [sub_add_cancel] using (extendIdeal B).add_mem (hu B hB) huB
  exact (hB.extended_prime.mem_or_mem hm).resolve_right
    (fun hz => hB.denom (hB.extended_prime.mem_of_pow_mem _ hz))
private theorem generic_degree_le (g : Row 4) : (toGeneric g).totalDegree ≤ g.totalDegree := by
  rw [toGeneric, MvPolynomial.totalDegree_eq, MvPolynomial.totalDegree_eq]
  exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
theorem generic_ne_zero {f : Row 4} (hf : Irreducible f) : toGeneric f ≠ 0 := by
  have hinj : Function.Injective genericCoeffs :=
    (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective Geom[X] GenericField)
  exact (map_ne_zero_iff (MvPolynomial.map genericCoeffs) (MvPolynomial.map_injective _ hinj)).mpr
    hf.ne_zero
theorem whole_dimension {f : Row 4} {component : JetIdeal} (hf : Irreducible f)
    (hZ : (Ideal.span {toGeneric f}).IsMinimalPrime component) : dimension component = 3 := by
  have h := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton
    (generic_ne_zero hf) hZ
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  change dimension component + 1 = 4 at h
  omega
theorem whole_sum {f : Row 4} (hf : Irreducible f) :
    ∑ component ∈ wholeComponents f, affineDegree component ≤ ((shape f).chamber.b : ℚ) := by
  have hn : toGeneric f ∉ (⊥ : JetIdeal) := fun h => generic_ne_zero hf ((Ideal.mem_bot).mp h)
  have hd : (toGeneric f).totalDegree ≤ (shape f).chamber.b :=
    (generic_degree_le f).trans (Nat.le_max_left _ _)
  simpa only [wholeComponents, bot_sup_eq, affineDegree_bot, mul_one] using (principalCut_sum_affineDegree_minimalPrimes_le (P := (⊥ : JetIdeal)) hn hd)
private theorem sum_biUnion_le {α β : Type} [DecidableEq β] (A : Finset α) (B : α → Finset β)
    (w : β → ℚ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x ∈ A.biUnion B, w x) ≤ ∑ i ∈ A, ∑ x ∈ B i, w x := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have hu := Finset.sum_union_inter (f := w) (s₁ := B i) (s₂ := A.biUnion B)
    have hn : 0 ≤ ∑ x ∈ B i ∩ A.biUnion B, w x := Finset.sum_nonneg fun x _ => hw x
    linarith
theorem proper_sum {f : Row 4} (hf : Irreducible f) (T : FatTaylor f) :
    ∑ P ∈ properComponents f T.test, affineDegree P ≤
      ((shape f).chamber.b : ℚ) * (fatChart (shape f)).b := by
  classical
  let V := (wholeComponents f).filter (fun component => toGeneric T.test ∉ component)
  let b := (fatChart (shape f)).b
  have hdeg : (toGeneric T.test).totalDegree ≤ b := (generic_degree_le _).trans T.test_box.1
  calc
    _ ≤ ∑ component ∈ V, ∑ P ∈ (divisorIdeal component T.test).minimalPrimesFinset, affineDegree P :=
      sum_biUnion_le V _ affineDegree affineDegree_nonneg
    _ ≤ ∑ component ∈ V, (b : ℚ) * affineDegree component := by
      refine Finset.sum_le_sum fun component hZ => ?_
      obtain ⟨hZ, ht⟩ := Finset.mem_filter.mp hZ
      let _ := (Ideal.mem_minimalPrimesFinset.mp hZ).isPrime
      exact principalCut_sum_affineDegree_minimalPrimes_le ht hdeg
    _ = (b : ℚ) * ∑ component ∈ V, affineDegree component := (Finset.mul_sum ..).symm
    _ ≤ (b : ℚ) * (shape f).chamber.b :=
      mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun component _ _ => affineDegree_nonneg component)).trans (whole_sum hf))
        (by positivity)
    _ = _ := mul_comm _ _
end
end P0_9_7_2_3
end
section
namespace P0_9_7_3
noncomputable section
open Polynomial K1_13 K1_13_7 K1_13_7_1 K1_13_7_5 K1_13_7_5_1 K1_13_7_5_3
open scoped BigOperators Pointwise
open private lift_length_ge lift_length_finite from ProximityPrize.SubmissionLower.Fast066
open private supported_anchor supported_lower supported_coordinate mixed_matches from ProximityPrize.SubmissionLower.Fast066
theorem lift_curve (f : Row 4) (P Q : Row 3) (S : Geom[X])
    (hf : OnFactor f S) (hcurve : HighCurve P Q (lowerPoint S)) :
    ∃ r : PrimeSpectrum Jets, LiftedCurve f P Q r ∧
      r.asIdeal < jetPointIdeal (jetPoint S) := by
  obtain ⟨q, hmin, hht, hy, hweight, _⟩ := hcurve
  obtain ⟨p, hover, hr, hry⟩ := exists_ambient_component hf hmin hy
  let r := PrimeSpectrum.comap (chartMap f) p
  have hc : r.asIdeal.comap lowerInclusion = q.asIdeal := by
    change (p.asIdeal.comap (chartMap f)).comap lowerInclusion = _
    rw [Ideal.comap_comap, chartMap_comp_lower]
    exact hover.over.symm
  obtain ⟨ht, hproper⟩ := ambient_component_height_and_strict hf hht hy hr hry hc
  have ha : (upperPolynomial f).leadingCoeff ≠ 0 :=
    fun h => upperPolynomial_lead_nonzero hf (by rw [h, map_zero])
  exact ⟨r, ⟨hr, ht, hweight.trans (lift_length_ge p rfl ha), lift_length_finite hr⟩, hproper⟩
private theorem common_section : K1_13_7_5_3.c1 :=
  K1_13_7_5_3_1.of_children K1_13_7_5_3_1_1.proof K1_13_7_5_3_1_2.proof
private theorem sparse_length : K1_13_7_5_3.c3 :=
  K1_13_7_5_3_3.of_children K1_13_7_5_3_3_1.proof
    (K1_13_7_5_3_3_2.of_children K1_13_7_5_3_3_2_1.proof K1_13_7_5_3_3_2_2.proof)
    (K1_13_7_5_3_3_3.of_children K1_13_7_5_3_3_3_1.proof K1_13_7_5_3_3_3_2.proof)
    K1_13_7_5_3_3_4.proof
theorem sparse_sections (f : Row 4) (P Q : Row 3)
    (hP : LowerCaps P lowerBox.b lowerBox.j) (hQ : LowerCaps Q lowerBox.b lowerBox.j)
    (R : Finset (PrimeSpectrum Jets)) (hR : ∀ r ∈ R, LiftedCurve f P Q r)
    (H : Shape) (hch : Chamber H ∧ 1 ≤ H.t)
    (cut : PrimeSpectrum Jets → Jets) (points : PrimeSpectrum Jets → Finset JetPoint)
    (hpoints : ∀ r ∈ R, Supported H (cut r) ∧ cut r ∉ r.asIdeal ∧
      ∀ y ∈ points r, r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y (cut r) = 0) :
    32 * threshold * (∑ r ∈ R, (points r).card) ≤
      mixed32 (shape f).chamber lowerBox lowerBox H := by
  classical
  let p := (shape f).chamber
  let J := liftIdeal f P Q
  have hp : Chamber p := shape_chamber f
  have hq : Chamber lowerBox := by
    constructor <;> decide
  have hopen (r : PrimeSpectrum Jets) (hr : r ∈ R) : ∃ a, CurveOpen J r a :=
    K1_13_7_5_3_2.proof J r (hR r hr).component (hR r hr).height (hR r hr).finite
  let guard (r : PrimeSpectrum Jets) : Jets :=
    if hr : r ∈ R then Classical.choose (hopen r hr) else 0
  have hguard (r : PrimeSpectrum Jets) (hr : r ∈ R) : CurveOpen J r (guard r) := by
    simpa only [guard, dite_eq_left hr] using Classical.choose_spec (hopen r hr)
  obtain ⟨D, selected, hD, hselected⟩ :=
    common_section H (supported_coordinate hch.1 hch.2) R (fun r hr => (hR r hr).height)
      guard (fun r hr => (hguard r hr).1) cut points (fun r hr => hpoints r hr)
  have hdisjoint : (R : Set (PrimeSpectrum Jets)).PairwiseDisjoint selected := by
    intro r hr s hs hrs
    apply Finset.disjoint_left.mpr
    intro y hyr hys
    have hmem : guard r ∈ s.asIdeal :=
      (hguard r hr).2.1 s.asIdeal (hR s hs).component (fun heq => hrs (PrimeSpectrum.ext heq.symm))
    have hcontains := ((hselected s hs).2.1.2 y hys).1
    have heval : MvPolynomial.eval y (guard r) = 0 := RingHom.mem_ker.mp (hcontains hmem)
    exact (hselected r hr).2.2 y hyr heval
  let all := R.biUnion selected
  have hisolated (y : JetPoint) (hy : y ∈ all) : IsolatedLengthGE (cutIdeal J D) threshold y := by
    obtain ⟨r, hr, hyr⟩ := Finset.mem_biUnion.mp hy
    have h := hselected r hr
    obtain ⟨hcontains, hzero⟩ := h.2.1.2 y hyr
    obtain ⟨hmin, hlen⟩ := (hguard r hr).2.2 D h.2.1.1 y hcontains (h.2.2 y hyr) hzero
    exact ⟨hmin, (hR r hr).heavy.trans hlen⟩
  have hbound :=
    sparse_length p lowerBox H hp hq hch.1 (geometricFactor f) (liftRow P) (liftRow Q) D
      (supported_anchor f) (supported_lower hP) (supported_lower hQ) hD threshold all hisolated
  rw [mixed_matches K1_13_7_5_3_4.proof hp hq hq hch.1] at hbound
  have hbound_int :
      ((32 * threshold * all.card : ℕ) : ℤ) ≤
        difference (difference (difference (difference volume32 p) lowerBox) lowerBox) H
          ⟨0, 0, 0⟩ := by
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [Int.cast_natCast] using hbound
  have hbound_nat : 32 * threshold * all.card ≤ mixed32 p lowerBox lowerBox H := by
    simpa only [mixed32, Int.toNat_natCast] using Int.toNat_le_toNat hbound_int
  apply le_trans _ hbound_nat
  apply Nat.mul_le_mul_left
  rw [show all.card = ∑ r ∈ R, (selected r).card from Finset.card_biUnion hdisjoint]
  exact Finset.sum_le_sum fun r hr => (hselected r hr).1
end
end P0_9_7_3
end
section
namespace P0_9_7_3
noncomputable section
open Polynomial Finset K1 K1_13 K1_13_7 K1_13_7_5 K1_13_7_1
open scoped BigOperators
open private supported_sub supported_C supported_X exists_coordinate_cut jetPoint_injective
  chart_section eval_chart_section weighted_ceil from ProximityPrize.SubmissionLower.Fast066
def c1 : Prop :=
  ∀ f : Row 4, P0_9.SmallFactor f → (shape f).t = 1 →
    ∃ C : ValueChart (P0_9_7.fatChart (shape f)),
      ∀ S : K[X], S.natDegree ≤ P0_9.physicalDegree → OnFactor f (extend S) →
        RegularAt f (extend S) → C.recovers S
def c2 : Prop :=
  ∀ f : Row 4, P0_9.SmallFactor f → (shape f).t ≠ 1 →
    ∃ C : ValueChart (P0_9_7.fatChart (shape f)),
      ∀ S : K[X], S.natDegree ≤ P0_9.physicalDegree → OnFactor f (extend S) →
        RegularAt f (extend S) → C.recovers S
private theorem fat_chamber (p : Shape) : Chamber (P0_9_7.fatChart p) := by
  unfold P0_9_7.fatChart
  split
  · let j := 3 + P0_9.taylorLength * (p.chamber.j - 2)
    refine ⟨le_max_right _ _, ?_⟩
    change 3 * min (P0_9.taylorLength + 1) (j / 3) ≤ j
    have hj := min_le_right (P0_9.taylorLength + 1) (j / 3)
    omega
  · exact chart_chamber _ _
private theorem fat_top (p : Shape) : 1 ≤ (P0_9_7.fatChart p).t := by
  unfold P0_9_7.fatChart
  split
  · change 1 ≤ min (P0_9.taylorLength + 1) ((3 + P0_9.taylorLength * (p.chamber.j - 2)) / 3)
    exact le_min (by omega) (by omega)
  · let L := P0_9.taylorLength + 4
    change 1 ≤ min (2 * L * (p.chamber.t - 1) + L + 1)
      ((2 * L * (p.chamber.j - 3) + L + 3) / 3)
    exact le_min (by omega) (by omega)
private theorem choose_section {w Γ s} (hm : P0_9.Messages w Γ s) {H : Shape} (C : ValueChart H)
    (hC : ∀ γ ∈ Γ, C.recovers (s γ)) {r : PrimeSpectrum Jets}
    (hr : ∀ γ ∈ Γ, r.asIdeal ≤ jetPointIdeal (jetPoint (extend (s γ)))) :
    ∃ (F : Jets) (selected : Finset JetPoint), Supported H F ∧ F ∉ r.asIdeal ∧
      (∀ y ∈ selected, r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y F = 0) ∧
      46666 * Γ.card ≤ 81927 * selected.card + 46666 := by
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
      exact P0_9_6.section_capacity hm _ (fun j hj => hmax j (mem_filter.mpr ⟨mem_univ _, hj⟩))
  · refine ⟨1, ∅, ?_, r.isPrime.one_notMem, by simp, ?_⟩
    · simpa only [map_one] using supported_C H (1 : GeometricX)
    · apply P0_9_6.section_capacity hm 0
      intro i hi
      exact (h ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩).elim
private theorem choose_linear_cut {f : Row 4} (ht : 0 < (shape f).t)
    {r : PrimeSpectrum Jets} {y : JetPoint} (h : r.asIdeal < jetPointIdeal y) :
    ∃ F : Jets, Supported (shape f).chamber F ∧ F ∉ r.asIdeal ∧
      r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y F = 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_cut h
  obtain ⟨hb, hj⟩ := shape_chamber f
  have hj' : 3 ≤ (shape f).chamber.j := by
    have htop : 0 < (shape f).chamber.t := ht
    omega
  have hb' : 1 ≤ (shape f).chamber.b := (by decide : 1 ≤ 3).trans (hj'.trans hb)
  exact ⟨MvPolynomial.X i - MvPolynomial.C (y i),
    supported_sub (supported_X hb' hj' ht i) (supported_C _ _), hi, h.le, by simp⟩
theorem of_children (h1 : c1) (h2 : c2) : P0_9_7.c3 := by
  classical
  intro w Γ s hm f hf _hEligible hOn P Q _hpq hbP hbQ hHigh
  have hlift (γ : K) (hγ : γ ∈ Γ) :=
    lift_curve f P Q (extend (s γ)) (hOn γ hγ).1 (hHigh γ hγ)
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
  obtain ⟨C, hC⟩ : ∃ C : ValueChart (P0_9_7.fatChart (shape f)),
      ∀ S : K[X], S.natDegree ≤ P0_9.physicalDegree → OnFactor f (extend S) →
        RegularAt f (extend S) → C.recovers S := by
    by_cases ht : (shape f).t = 1
    · exact h1 f hf ht
    · exact h2 f hf ht
  have hsections (r : PrimeSpectrum Jets) :
      ∃ (F : Jets) (selected : Finset JetPoint), Supported (P0_9_7.fatChart (shape f)) F ∧ F ∉ r.asIdeal ∧
        (∀ y ∈ selected, r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y F = 0) ∧
        46666 * (piece r).card ≤ 81927 * selected.card + 46666 :=
    choose_section (hm.mono (filter_subset _ _)) C
      (fun γ hγ => hC (s γ) (hm.degree γ (mem_filter.mp hγ).1)
        (hOn γ (mem_filter.mp hγ).1).1 (hOn γ (mem_filter.mp hγ).1).2)
      (fun _ hγ => (mem_filter.mp hγ).2)
  choose cut selected hCut hProper hY hFee using hsections
  have hDegree := sparse_sections f P Q hbP hbQ R (fun r hr => (hR r hr).1)
    (P0_9_7.fatChart (shape f))
      ⟨fat_chamber (shape f), fat_top (shape f)⟩ cut selected (fun r _ => ⟨hCut r, hProper r, hY r⟩)
  have hlinear (r : PrimeSpectrum Jets) : ∃ (F : Jets) (singlePoint : Finset JetPoint),
      (r ∈ R → Supported (shape f).chamber F ∧ F ∉ r.asIdeal ∧
        ∀ y ∈ singlePoint, r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y F = 0) ∧
      (r ∈ R → singlePoint.card = 1) := by
    by_cases hr : r ∈ R
    · obtain ⟨γ, _, hpoint⟩ := (hR r hr).2
      obtain ⟨F, hF, hproper, hmem, hzero⟩ := choose_linear_cut hf.2.1 hpoint
      exact ⟨F, {jetPoint (extend (s γ))}, fun _ => ⟨hF, hproper, by simpa using And.intro hmem hzero⟩, fun _ => by simp⟩
    · exact ⟨0, ∅, fun h => (hr h).elim, fun h => (hr h).elim⟩
  choose linear singlePoint hLinear hOne using hlinear
  have hCount := sparse_sections f P Q hbP hbQ R (fun r hr => (hR r hr).1)
    (shape f).chamber ⟨shape_chamber f, hf.2.1⟩ linear singlePoint hLinear
  rw [sum_congr rfl hOne, sum_const, smul_eq_mul, Nat.mul_one] at hCount
  have hsum : 46666 * Γ.card ≤ 81927 * (∑ r ∈ R, (selected r).card) + 46666 * R.card := calc
    _ ≤ 46666 * (∑ r ∈ R, (piece r).card) := Nat.mul_le_mul_left _ hcover
    _ = ∑ r ∈ R, 46666 * (piece r).card := mul_sum ..
    _ ≤ ∑ r ∈ R, (81927 * (selected r).card + 46666) := sum_le_sum fun r _ => hFee r
    _ = _ := by rw [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, Nat.mul_comm R.card]
  change Γ.card ≤ ceilDiv
    (81927 * mixed32 (shape f).chamber lowerBox lowerBox (P0_9_7.fatChart (shape f)) +
      46666 * mixed32 (shape f).chamber lowerBox lowerBox (shape f).chamber)
    (32 * 46666 * threshold)
  rw [Nat.mul_right_comm 32 46666 threshold]
  exact weighted_ceil (32 * threshold) 81927 46666 (Nat.mul_pos (Nat.mul_pos (by decide) (by decide)) (by decide))
    hsum hDegree hCount
end
end P0_9_7_3
end
section
namespace P0_9_7_3_1
noncomputable section
open Polynomial MvPolynomial K1 K1_13 K1_13_1 K1_13_6 K1_13_7 K1_13_7_1 K1_13_7_5
open scoped BigOperators
open private linearJet eval_linearJet separant_bound linearJet_bound K1_13_7_5_2.denominator ordinary_eq_hasse
  from ProximityPrize.SubmissionLower.Fast072
open private supported_of_fits eval_center from ProximityPrize.SubmissionLower.Fast072
open private supported_C_mul from ProximityPrize.SubmissionLower.Fast066
local notation "W" => MvPolynomial.weightedTotalDegree
private def numerator (L : ℕ) (f : Row 4) (n : ℕ) : Row 4 :=
  if hn : n < 4 then MvPolynomial.X ⟨n, hn⟩ * K1_13_7_5_2.denominator L f
  else
    MvPolynomial.C (Polynomial.C (↑n.factorial : Geom)⁻¹) *
      (separant f ^ (L - n) * linearJet f n)
private theorem denominator_bound (L : ℕ) (w : Fin 4 → ℕ) {f : Row 4} {B : ℕ}
    (hf : W w f ≤ B) : W w (K1_13_7_5_2.denominator L f) ≤ L * (B - w 3) :=
  (weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _ (separant_bound w hf))
private theorem numerator_bound {L n : ℕ} (hn : n ≤ L) (w : Fin 4 → ℕ) (Δ d₀ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) (hw : ∀ i, w i ≤ d₀)
    {f : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hf : W w f ≤ B) :
    W w (numerator L f n) ≤ d₀ + L * (B - w 3 + Δ) := by
  unfold numerator
  split_ifs with hinit
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((weight_X_le w _).trans (hw _)) (denominator_bound L w hf)).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _))
  · have hp := (weightedTotalDegree_pow_le w (separant f) (L - n)).trans
      (Nat.mul_le_mul_left _ (separant_bound w hf))
    apply (weight_const_mul_le _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ (L - n) * (B - w 3) + (w 0 + n * (B - w 3 + Δ)) :=
        Nat.add_le_add hp (linearJet_bound w Δ hshift hB hf n)
      _ = w 0 + ((L - n) + n) * (B - w 3) + n * Δ := by ring
      _ ≤ _ := by
        rw [Nat.sub_add_cancel hn, Nat.mul_add]
        simpa only [Nat.add_assoc] using
          Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hn)
private theorem coefficient_fits (f : Row 4) (ht : (shape f).t = 1) :
    let L := P0_9.taylorLength
    let H := P0_9.linearChart (shape f).chamber
    GeoFits (toGeneric (K1_13_7_5_2.denominator L f)) H ∧
      ∀ i : Fin L, GeoFits (toGeneric (numerator L f i.val)) H := by
  let L := P0_9.taylorLength
  let p := (shape f).chamber
  have hpt : p.t = 1 := ht
  have hj : 3 ≤ p.j := by
    have h := (shape_chamber f).2
    change 3 * p.t ≤ p.j at h
    omega
  have hb : 1 ≤ p.b := (by omega : 1 ≤ p.j).trans (shape_chamber f).1
  have hbF : W 1 f ≤ p.b := by
    rw [weightedTotalDegree_one]
    exact le_max_left _ _
  have hjF : W Fin.val f ≤ p.j := by
    rw [← indexDegree_eq]
    exact le_rfl
  let w : Fin 4 → ℕ := Pi.single 3 1
  have hwF : W w f ≤ 1 := by simpa only [w, weightedTotalDegree_piSingle, shape] using ht.le
  have hw3 : w 3 = 1 := by decide
  have hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + 1 := by
    intro i
    fin_cases i <;> decide
  have hw : ∀ i, w i ≤ 1 := by
    intro i
    fin_cases i <;> decide
  have pack (P : Row 4) (hb' : W 1 P ≤ 1 + L * (p.b - 1))
      (hj' : W Fin.val P ≤ 3 + L * (p.j - 2))
      (ht' : W w P ≤ L + 1) : GeoFits (toGeneric P) (P0_9.linearChart p) := by
    apply toGeneric_fits
    refine ⟨?_, ?_, ?_⟩
    · change P.totalDegree ≤ max _ _
      exact (by simpa only [weightedTotalDegree_one] using hb' :
        P.totalDegree ≤ 1 + L * (p.b - 1)).trans (le_max_left _ _)
    · change indexDegree P ≤ _
      rwa [indexDegree_eq]
    · change P.degreeOf 3 ≤ min _ ((3 + L * (p.j - 2)) / 3)
      apply le_min
      · simpa only [w, weightedTotalDegree_piSingle] using ht'
      · have h := (top_le_index P).trans hj'
        omega
  change GeoFits (toGeneric (K1_13_7_5_2.denominator L f)) (P0_9.linearChart p) ∧
    ∀ i : Fin L, GeoFits (toGeneric (numerator L f i.val)) (P0_9.linearChart p)
  constructor
  · apply pack
    · exact (denominator_bound L 1 hbF).trans (Nat.le_add_left _ _)
    · have h := denominator_bound L Fin.val hjF
      change W Fin.val (K1_13_7_5_2.denominator L f) ≤ L * (p.j - 3) at h
      exact h.trans ((Nat.mul_le_mul_left _ (by omega : p.j - 3 ≤ p.j - 2)).trans
        (Nat.le_add_left _ _))
    · have h := denominator_bound L w hwF
      rw [hw3, Nat.sub_self, Nat.mul_zero] at h
      exact h.trans (Nat.zero_le _)
  · intro i
    apply pack
    · simpa only [Pi.one_apply, add_zero] using
        numerator_bound i.isLt.le 1 0 1 (fun _ => by simp) (fun _ => le_rfl) hb hbF
    · have h := numerator_bound i.isLt.le Fin.val 1 3 (fun _ => by rfl)
        (fun j : Fin 4 => Nat.le_of_lt_succ j.isLt) hj hjF
      change W Fin.val (numerator L f i.val) ≤ 3 + L * (p.j - 3 + 1) at h
      rwa [show p.j - 3 + 1 = p.j - 2 by omega] at h
    · have h := numerator_bound i.isLt.le w 1 1 hshift hw (show w 3 ≤ 1 from hw3.le) hwF
      simpa only [hw3, Nat.sub_self, zero_add, Nat.mul_one, Nat.add_comm] using h
private theorem coefficients_recover {L : ℕ} (hL : L < K1.p) {f : Row 4}
    (hf : (shape f).t = 1) (S : Geom[X]) (hon : atJet f S = 0) (hr : RegularAt f S) :
    evalGeneric S (toGeneric (K1_13_7_5_2.denominator L f)) ≠ 0 ∧
      ∀ i : Fin L, evalGeneric S (toGeneric (numerator L f i.val)) =
        evalGeneric S (toGeneric (K1_13_7_5_2.denominator L f)) * genericCoeffs (hasseDeriv i.val S) := by
  have hp : atJet (separant f) S ≠ 0 := hr
  have hden : atJet (K1_13_7_5_2.denominator L f) S = atJet (separant f) S ^ L :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → Geom[X])) _ _
  constructor
  · rw [evalGeneric_toGeneric, hden]
    exact (map_ne_zero_iff _ genericCoeffs_injective).mpr (pow_ne_zero _ hp)
  · intro i
    rw [evalGeneric_toGeneric, evalGeneric_toGeneric, ← map_mul]
    apply congrArg genericCoeffs
    unfold numerator
    split_ifs with hinit
    · unfold atJet
      rw [map_mul, MvPolynomial.eval_X, mul_comm]
      rfl
    · let E := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant f) S ^ (L - i.val) *
        atJet (linearJet f i.val) S) = _
      rw [eval_linearJet hf S hon hr, ordinary_eq_hasse]
      have hinv : Polynomial.C (↑i.val.factorial : Geom)⁻¹ *
          Polynomial.C (↑i.val.factorial : Geom) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ (factorial_cast_ne_zero (i.isLt.trans hL)), map_one]
      have hpow : L - i.val + i.val = L := Nat.sub_add_cancel i.isLt.le
      calc
        _ = (Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom)) *
            ((atJet (separant f) S ^ (L - i.val) * atJet (separant f) S ^ i.val) *
              hasseDeriv i.val S) := by ring
        _ = _ := by rw [hinv, one_mul, ← pow_add, hpow, hden]
private abbrev constants : Geom →+* GeometricX := genericCoeff.comp Polynomial.C
private abbrev center : GeometricX := genericCoeff Polynomial.X
private theorem eval_taylor {L : ℕ} (S : K[X]) (hS : S.natDegree < L) (x : K) :
    (∑ j : Fin L, (constantCoeff x - center) ^ j.val *
      genericCoeff (hasseDeriv j.val (extend S))) = constantCoeff (S.eval x) := by
  let P := (extend S).map constants
  let u := constantCoeff x - center
  have hcoeff (n : ℕ) : (Polynomial.taylor center P).coeff n =
      genericCoeff (hasseDeriv n (extend S)) := by
    rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_center]
  have hd : (Polynomial.taylor center P).natDegree < L := by
    rw [Polynomial.natDegree_taylor]
    exact (Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le).trans_lt hS
  have hev : P.eval (constantCoeff x) = constantCoeff (S.eval x) := by
    change ((S.map embed).map constants).eval (constantCoeff x) = _
    rw [Polynomial.map_map]
    exact Polynomial.eval_map_apply K1_13_7_5.constantCoeff x
  calc
    _ = (Polynomial.taylor center P).eval u := by
      rw [Polynomial.eval_eq_sum_range' hd, ← Fin.sum_univ_eq_sum_range]
      simp only [hcoeff, u]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = P.eval (constantCoeff x) := Polynomial.taylor_eval_sub _ _ _
    _ = _ := hev
theorem values_of_coefficients {L : ℕ} {H : Shape} (D : GeoJets) (N : Fin L → GeoJets)
    (hD : GeoFits D H) (hN : ∀ j, GeoFits (N j) H) :
    ∃ C : ValueChart H, ∀ S : K[X], S.natDegree < L →
      (evalGeneric (extend S) D ≠ 0 ∧ ∀ j, evalGeneric (extend S) (N j) =
        evalGeneric (extend S) D * genericCoeffs (hasseDeriv j.val (extend S))) →
      C.recovers S := by
  let value (i : I) : Jets :=
    ∑ j : Fin L, MvPolynomial.C ((constantCoeff (node i) - center) ^ j.val) * N j
  have hvalue (i : I) : Supported H (value i) := by
    classical
    intro m hm
    unfold value at hm
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
    exact supported_C_mul (supported_of_fits (hN j)) _ m hj
  refine ⟨⟨D, value, supported_of_fits hD, hvalue⟩, ?_⟩
  intro S hS h
  refine ⟨h.1, fun i => ?_⟩
  let ev := evalGeneric (extend S)
  change ev (value i) = constantCoeff (S.eval (node i)) * ev D
  have hc (a : GeometricX) : ev (MvPolynomial.C a) = a := MvPolynomial.eval_C a
  have he (j : Fin L) : ev (N j) =
      ev D * genericCoeff (hasseDeriv j.val (extend S)) := h.2 j
  simp only [value, map_sum, map_mul, hc, he]
  calc
    _ = ev D * (∑ j : Fin L, (constantCoeff (node i) - center) ^ j.val *
        genericCoeff (hasseDeriv j.val (extend S))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => mul_left_comm _ _ _)
    _ = _ := by rw [eval_taylor S hS, mul_comm]
theorem proof : P0_9_7_3.c1 := by
  intro f _hf ht
  rw [P0_9_7.fatChart, ite_eq_left ht]
  obtain ⟨hD, hN⟩ := coefficient_fits f ht
  obtain ⟨C, hC⟩ := values_of_coefficients _ _ hD hN
  have hlength : P0_9.taylorLength < K1.p := by
    change 133552 < 2130706433
    decide
  exact ⟨C, fun S hS hon hr =>
    hC S (Nat.lt_succ_of_le hS) (coefficients_recover hlength ht (extend S) hon.1 hr)⟩
end
end P0_9_7_3_1
end
section
namespace P0_9_7_3_2
noncomputable section
open Polynomial MvPolynomial K1 K1_13 K1_13_6 K1_13_7 K1_13_7_1 K1_13_7_5
open K1_13_1 (indexDegree_eq)
open scoped BigOperators
open private denominator denominator_bound topPartial_bound jet_bound ordinary_eq_hasse
  from ProximityPrize.SubmissionLower.Fast059
open private supported_of_fits constants center eval_center from ProximityPrize.SubmissionLower.Fast072
open private supported_C_mul from ProximityPrize.SubmissionLower.Fast066
local notation "W" => MvPolynomial.weightedTotalDegree
private def coefficientNumerator (L : ℕ) (g : Row 4) (n : ℕ) : Row 4 :=
  if hn : n < 4 then MvPolynomial.X ⟨n, hn⟩ * denominator L g
  else
    MvPolynomial.C (Polynomial.C (↑n.factorial : Geom)⁻¹) *
      (separant g ^ (2 * (L - n)) * jetNumerator g n)
private theorem numerator_bound {L n : ℕ} (hn : n ≤ L) (w : Fin 4 → ℕ) (Δ d₀ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) (hw : ∀ i, w i ≤ d₀)
    {g : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) :
    W w (coefficientNumerator L g n) ≤ d₀ + 2 * L * (B - w 3) + L * Δ := by
  unfold coefficientNumerator
  split_ifs
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((weight_X_le w _).trans (hw _)) (denominator_bound L w hg)).trans
        (Nat.le_add_right _ _))
  · have hp := (weightedTotalDegree_pow_le w (separant g) (2 * (L - n))).trans
      (Nat.mul_le_mul_left _ ((topPartial_bound w g).trans (Nat.sub_le_sub_right hg _)))
    apply (weight_const_mul_le _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ 2 * (L - n) * (B - w 3) + (w 0 + n * (2 * (B - w 3) + Δ)) :=
        Nat.add_le_add hp (jet_bound w Δ hshift hB hg n)
      _ = w 0 + 2 * (n + (L - n)) * (B - w 3) + n * Δ := by ring
      _ ≤ _ := by
        rw [Nat.add_sub_of_le hn]
        exact Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hn)
private theorem coefficients_fit (L : ℕ) (g : Row 4) (p : Shape) (hB : InBox (shape g) p)
    (hp : Chamber p) (ht : 0 < p.t) :
    GeoFits (toGeneric (denominator L g)) (chart L p) ∧
      ∀ n ≤ L, GeoFits (toGeneric (coefficientNumerator L g n)) (chart L p) := by
  have hb : 1 ≤ p.b := by have := hp.1; have := hp.2; omega
  have hj : 3 ≤ p.j := by have := hp.2; omega
  have h₁ : W 1 g ≤ p.b := by simpa only [shape, weightedTotalDegree_one] using hB.1
  have h₂ : W Fin.val g ≤ p.j := by simpa only [shape, indexDegree_eq] using hB.2.1
  let w : Fin 4 → ℕ := Pi.single 3 1
  have h₃ : W w g ≤ p.t := by simpa only [w, shape, weightedTotalDegree_piSingle] using hB.2.2
  have hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + 1 := by
    intro i
    fin_cases i <;> decide
  have hw : ∀ i, w i ≤ 1 := by
    intro i
    fin_cases i <;> decide
  have hw3 : w 3 = 1 := by decide
  have fits (P : Row 4) (hb' : W 1 P ≤ 1 + 2 * L * (p.b - 1))
      (hj' : W Fin.val P ≤ 2 * L * (p.j - 3) + L + 3)
      (ht' : W w P ≤ 2 * L * (p.t - 1) + L + 1) :
      GeoFits (toGeneric P) (chart L p) := by
    apply toGeneric_fits
    refine ⟨?_, ?_, ?_⟩
    · change P.totalDegree ≤ max _ _
      exact (by simpa only [weightedTotalDegree_one] using hb' :
        P.totalDegree ≤ 1 + 2 * L * (p.b - 1)).trans (le_max_left _ _)
    · change indexDegree P ≤ _
      rwa [indexDegree_eq]
    · change P.degreeOf 3 ≤ min _ _
      apply le_min
      · simpa only [w, weightedTotalDegree_piSingle] using ht'
      · have h := (top_le_index P).trans hj'
        omega
  constructor
  · apply fits
    · exact (denominator_bound L _ h₁).trans (Nat.le_add_left _ _)
    · exact (denominator_bound L _ h₂).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    · have h := denominator_bound L w h₃
      rw [hw3] at h
      exact h.trans (by omega)
  · intro n hn
    apply fits
    · have h := numerator_bound hn 1 0 1 (fun _ => by simp) (fun _ => le_rfl) hb h₁
      change W 1 (coefficientNumerator L g n) ≤ 1 + 2 * L * (p.b - 1) + L * 0 at h
      simpa only [mul_zero, add_zero] using h
    · have h := numerator_bound hn Fin.val 1 3 (fun _ => by rfl)
        (fun j : Fin 4 => Nat.le_of_lt_succ j.isLt) hj h₂
      change W Fin.val (coefficientNumerator L g n) ≤ 3 + 2 * L * (p.j - 3) + L * 1 at h
      simpa only [mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
    · have hwle : w 3 ≤ p.t := hw3.symm ▸ ht
      have h := numerator_bound hn w 1 1 hshift hw hwle h₃
      simpa only [hw3, mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
private theorem coefficients_recover (L : ℕ) (g : Row 4) (S : Geom[X])
    (hg : atJet g S = 0) (hr : RegularAt g S) :
    evalGeneric S (toGeneric (denominator L g)) ≠ 0 ∧
      ∀ n ≤ L, n < K1.p →
        evalGeneric S (toGeneric (coefficientNumerator L g n)) =
          evalGeneric S (toGeneric (denominator L g)) * genericCoeffs (hasseDeriv n S) := by
  have hp : atJet (separant g) S ≠ 0 := hr
  have hden : atJet (denominator L g) S = atJet (separant g) S ^ (2 * L) :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → Geom[X])) _ _
  constructor
  · rw [evalGeneric_toGeneric]
    apply (map_ne_zero_iff _ genericCoeffs_injective).mpr
    rw [hden]
    exact pow_ne_zero _ hp
  · intro n hn hc
    rw [evalGeneric_toGeneric, evalGeneric_toGeneric, ← map_mul]
    apply congrArg genericCoeffs
    unfold coefficientNumerator
    split_ifs
    · unfold atJet
      rw [map_mul, MvPolynomial.eval_X, mul_comm]
      rfl
    · let E := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant g) S ^ (2 * (L - n)) * atJet (jetNumerator g n) S) = _
      rw [eval_jetNumerator _ _ hg, ordinary_eq_hasse]
      have hinv : Polynomial.C (↑n.factorial : Geom)⁻¹ * Polynomial.C (↑n.factorial : Geom) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ (factorial_cast_ne_zero hc), map_one]
      have hpow : 2 * (L - n) + 2 * n = 2 * L := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hn]
      calc
        _ = (Polynomial.C (↑n.factorial : Geom)⁻¹ * Polynomial.C (↑n.factorial : Geom)) *
            ((atJet (separant g) S ^ (2 * (L - n)) * atJet (separant g) S ^ (2 * n)) *
              hasseDeriv n S) := by ring
        _ = _ := by rw [hinv, one_mul, ← pow_add, hpow, hden]
private theorem eval_taylor {M : ℕ} (S : K[X]) (hS : S.natDegree < M) (x : K) :
    (∑ j : Fin M, (K1_13_7_5.constantCoeff x - center) ^ j.val *
      genericCoeff (hasseDeriv j.val (extend S))) = K1_13_7_5.constantCoeff (S.eval x) := by
  let P := (extend S).map constants
  let u := K1_13_7_5.constantCoeff x - center
  have hcoeff (n : ℕ) : (Polynomial.taylor center P).coeff n =
      genericCoeff (hasseDeriv n (extend S)) := by
    rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_center]
  have hd : (Polynomial.taylor center P).natDegree < M := by
    rw [Polynomial.natDegree_taylor]
    exact Polynomial.natDegree_map_le.trans_lt (Polynomial.natDegree_map_le.trans_lt hS)
  have hev : P.eval (K1_13_7_5.constantCoeff x) = K1_13_7_5.constantCoeff (S.eval x) := by
    change ((S.map embed).map constants).eval (K1_13_7_5.constantCoeff x) = _
    rw [Polynomial.map_map]
    exact Polynomial.eval_map_apply K1_13_7_5.constantCoeff x
  calc
    _ = (Polynomial.taylor center P).eval u := by
      rw [Polynomial.eval_eq_sum_range' hd, ← Fin.sum_univ_eq_sum_range]
      simp only [hcoeff, u]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = P.eval (K1_13_7_5.constantCoeff x) := Polynomial.taylor_eval_sub _ _ _
    _ = _ := hev
private theorem values_of_coefficients {M : ℕ} {H : Shape} (D : GeoJets) (N : Fin M → GeoJets)
    (hD : GeoFits D H) (hN : ∀ j, GeoFits (N j) H) :
    ∃ C : ValueChart H, ∀ S : K[X], S.natDegree < M →
      evalGeneric (extend S) D ≠ 0 →
      (∀ j : Fin M, evalGeneric (extend S) (N j) =
        evalGeneric (extend S) D * genericCoeff (hasseDeriv j.val (extend S))) →
      C.recovers S := by
  let weight (i : I) (j : Fin M) := (K1_13_7_5.constantCoeff (node i) - center) ^ j.val
  let value (i : I) : Jets := ∑ j : Fin M, MvPolynomial.C (weight i j) * N j
  have hs (i : I) : Supported H (value i) := by
    intro m hm
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
    exact supported_C_mul (supported_of_fits (hN j)) (weight i j) m hj
  refine ⟨⟨D, value, supported_of_fits hD, hs⟩, ?_⟩
  intro S hS hne he
  refine ⟨hne, fun i => ?_⟩
  let ev := evalGeneric (extend S)
  change ev (value i) = K1_13_7_5.constantCoeff (S.eval (node i)) * ev D
  have hc (a : GeometricX) : ev (MvPolynomial.C a) = a := MvPolynomial.eval_C a
  have heval (j : Fin M) :
      ev (N j) = ev D * genericCoeff (hasseDeriv j.val (extend S)) := he j
  simp only [value, map_mul, map_sum, hc, heval]
  calc
    _ = ev D * (∑ j : Fin M, weight i j * genericCoeff (hasseDeriv j.val (extend S))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => mul_left_comm _ _ _)
    _ = _ := by
      rw [show _ = K1_13_7_5.constantCoeff (S.eval (node i)) from eval_taylor S hS _, mul_comm]
theorem proof : P0_9_7_3.c2 := by
  intro f hf ht
  rw [P0_9_7.fatChart, ite_eq_right (fun h => (ht h).elim)]
  let L := P0_9.taylorLength + 4
  have hchar : P0_9.taylorLength < K1.p := by decide
  have horder (j : Fin P0_9.taylorLength) : j.val ≤ L :=
    j.isLt.le.trans (Nat.le_add_right _ _)
  obtain ⟨hD, hN⟩ := coefficients_fit L f (shape f).chamber
    ⟨le_max_left _ _, le_rfl, le_rfl⟩ (shape_chamber f) hf.2.1
  obtain ⟨C, hC⟩ := values_of_coefficients (toGeneric (denominator L f))
    (fun j : Fin P0_9.taylorLength => toGeneric (coefficientNumerator L f j.val))
    hD (fun j => hN j.val (horder j))
  refine ⟨C, fun S hS hon hr => ?_⟩
  obtain ⟨hne, hcoeff⟩ := coefficients_recover L f (extend S) hon.1 hr
  exact hC S (Nat.lt_succ_of_le hS) hne (fun j => hcoeff j.val (horder j) (j.isLt.trans hchar))
end
end P0_9_7_3_2
end
