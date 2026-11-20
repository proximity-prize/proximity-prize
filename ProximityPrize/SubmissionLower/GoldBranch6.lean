import ProximityPrize.SubmissionLower.FrontBranch12
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
namespace P3_1
noncomputable section
open Polynomial Matrix FrobeniusLocator P3
open ProximityPrize.Benchmark
open private eval_atSlope commonGCD_of_roots lift_dvd_atSlope from ProximityPrize.SubmissionLower.FrontBranch12
private theorem twoBlock_atSlope (u : Words) (γ : K) :
    ((twoBlock u).map (evalRingHom γ)) =
      Strata.conjugateHankel (Strata.twoConjugations (frobenius K p))
        node (fun i => u 0 i + γ * u 1 i) L t := by
  rw [twoBlock, Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval]
  have h : (fun b : Fin 2 => iterateFrobenius K p b.val) =
      Strata.twoConjugations (frobenius K p) := by
    funext b
    fin_cases b
    · exact iterateFrobenius_zero K p
    · exact iterateFrobenius_one K p
  rw [h]
private theorem rank_at_normal {u : Words} (T : TwoActive u) {γ : K} (hγ : Normal u γ) :
    ((twoBlock u).map (evalRingHom γ)).rank = L + T.height := by
  change _ = stackRank u at hγ
  rw [hγ, actual_stackRank]
  have h := relation_height_balance T
  omega
private theorem error_rank {u : Words} {γ : K} (M : BadMark u γ)
    (E : Finset I) (hE : E.card ≤ t)
    (hEagree : ∀ i ∉ E, u 0 i + γ * u 1 i = M.decoder.eval (node i)) :
    ((twoBlock u).map (evalRingHom γ)).rank =
      (Strata.errorTwoMatrix (frobenius K p) (fun i : E => node i.val)
        (fun i : E => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)) L).rank := by
  have hfix : ∀ b i, Strata.twoConjugations (frobenius K p) b (node i) = node i := by
    intro b i
    fin_cases b <;> simp [Strata.twoConjugations, frobenius_def, Native.native_domain_fixed]
  have h := Strata.conjugateHankel_error_rank
    (Strata.twoConjugations (frobenius K p)) node (fun i => u 0 i + γ * u 1 i)
    IRSProfile.domain.injective hfix M.decoder k L t M.degree
    (by rw [IRSProfile.card_index]; decide) E (hE.trans (Nat.le_succ t)) hEagree
  rw [Strata.conjugateErrors_two] at h
  rw [twoBlock_atSlope]
  exact h
private theorem valid_of_saturation {u : Words} {T : TwoActive u} (R : Relation T)
    (γ : K) (S : Finset I)
    (hdegree : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree = T.height)
    (hG : IsCommonGCD (locator node S) (atSlope (leftU R) γ) (atSlope (leftV R) γ)) :
    ¬ InvalidLeft R := by
  intro hinvalid
  rcases hinvalid with hlow | ⟨G, _, hGU, hGV, hbad⟩
  · have hle : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree ≤
        max (leftU R).natDegree (leftV R).natDegree :=
      max_le_max Polynomial.natDegree_map_le Polynomial.natDegree_map_le
    omega
  · have hS : locator node S ∣ locator node Finset.univ :=
      ⟨locator node (Finset.univ \ S),
        (Principal.locator_mul_sdiff node S Finset.univ (Finset.subset_univ S)).symm⟩
    exact hbad ((hG.2.2.2 G (lift_dvd_atSlope γ hGU) (lift_dvd_atSlope γ hGV)).trans hS)
theorem proof : P3.c1 := by
  classical
  intro u hfront T R γ hγ M
  let U := atSlope (leftU R) γ
  let V := atSlope (leftV R) γ
  let E : Finset I := Finset.univ.filter (fun i => M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i)
  let e : E → K := fun i => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)
  let x : E → K := fun i => node i.val
  have hEagree (i : I) (hi : i ∉ E) : u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm h⟩)
  have hEcard : E.card ≤ t := by
    have hsub : E ⊆ Finset.univ \ M.support := by
      intro i hi
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hs => ?_⟩
      exact (Finset.mem_filter.mp hi).2 (M.hits i hs)
    have h := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      IRSProfile.card_index] at h
    exact h.trans (Nat.sub_le_sub_left M.agreement blockLength)
  have hheight : T.height ≤ heightCap := relation_height_le hfront T
  have hH : T.height < L := hheight.trans_lt (by change 33249 < 48911; decide)
  have hfit : k + T.height ≤ M.support.card :=
    have hcap : k + heightCap ≤ agreement := by
      change 164321 ≤ 179983
      decide
    ((Nat.add_le_add_left hheight k).trans hcap).trans M.agreement
  have hfix (i : I) : frobenius K p (node i) = node i := Native.native_domain_fixed i
  obtain ⟨hpair, hrel⟩ :=
    Strata.certificate_specializes p node (u 0) (u 1) k T.height R γ
  have hUle : U.natDegree ≤ T.height := hrel.degree_U
  have hVle : V.natDegree ≤ T.height := hrel.degree_V
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have he (i : E) : e i ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp i.property).2)
  have herror (i : E) : U.eval (x i) * e i + V.eval (x i) * frobenius K p (e i) = 0 :=
    Strata.certificate_error_identity p node (u 0) (u 1) IRSProfile.domain.injective
      Native.native_domain_fixed k T.height R γ M.support hfit M.decoder M.degree M.hits i.val
  have hrank : (Strata.errorTwoMatrix (frobenius K p) x e L).rank = L + T.height :=
    (error_rank M E hEcard hEagree).symm.trans (rank_at_normal T hγ)
  obtain ⟨hU, hV⟩ := Strata.saturated_coefficients_nonzero (frobenius K p) x e hx U V
    T.height L hUle hVle hpair hH he herror hrank
  let G := GCDMonoid.gcd U V
  let C₀ := (Finset.univ : Finset E).filter (fun i => G.eval (x i) = 0)
  let S := C₀.image (fun i : E => i.val)
  obtain ⟨hC, hsum, _⟩ := Strata.normal_error_three_rank (frobenius K p) x e hx
    (fun i => hfix i.val) U V T.height L hUle hVle hpair hH he herror hrank
  have hmax : max U.natDegree V.natDegree = T.height := by
    obtain ⟨hle, hred⟩ := Strata.gcd_reduction_degrees U V hU hV
    change max (U / G).natDegree (V / G).natDegree + G.natDegree = T.height at hsum
    change G.natDegree ≤ max U.natDegree V.natDegree at hle
    change max (U / G).natDegree (V / G).natDegree =
      max U.natDegree V.natDegree - G.natDegree at hred
    omega
  have hS_card : S.card = G.natDegree :=
    (Finset.card_image_of_injective C₀ Subtype.val_injective).trans hC
  have hS_error (i : I) (hi : i ∈ S) : M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp j.property).2
  have hG : IsCommonGCD (locator node S) U V := by
    apply commonGCD_of_roots U V hV S _ hS_card
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hj).2
  refine ⟨hU, hV, hmax, ⟨S, hS_error, hG⟩, ?_, valid_of_saturation R γ S hmax hG⟩
  intro i hi
  have hzero := (Finset.mem_filter.mp hi).2
  have hu0 : U.eval (node i) = 0 := by
    change (atSlope (leftU R) γ).eval (node i) = 0
    rw [eval_atSlope, hzero.1, eval_zero]
  have hv0 : V.eval (node i) = 0 := by
    change (atSlope (leftV R) γ).eval (node i) = 0
    rw [eval_atSlope, hzero.2, eval_zero]
  have hdiv : (Polynomial.X : K[X]) - C (node i) ∣ locator node S :=
    hG.2.2.2 _ (dvd_iff_isRoot.mpr hu0) (dvd_iff_isRoot.mpr hv0)
  have hroot : (locator node S).eval (node i) = 0 :=
    eval_eq_zero_of_dvd_of_eval_eq_zero hdiv (by rw [eval_sub, eval_X, eval_C, sub_self])
  exact hS_error i ((Principal.locator_eval_zero_iff node IRSProfile.domain.injective S i).mp hroot)
end
end P3_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace P3_2
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P3 (Words k agreement t amplitudeDegree)
open K1_9 (K I node pencil CoefficientIdentities)
open private polarData_of_set from ProximityPrize.SubmissionLower.FrontBranch12
open private coefficientsAt pow_eq_twist threeUAt_native relationOnAt_native from ProximityPrize.SubmissionLower.PortFrontA
private theorem coefficients {u : Words} {T : P3.TwoActive u} {R : P3.Relation T}
    {D : P3.Reduction u T R} (B : P3.RankThree u T R D) (hp : P3.Parallel B)
    (i : I) (hi : i ∉ P3.fixedNodes R) :
    CoefficientIdentities u B.a B.b B.α B.output i := by
  have hnodes : P0_5.relationOnAt P0.p u (P3.fixedNodes R) (P0_5.threeUAt P0.p B.a B.β)
      (P0.threeV B.b B.α) B.output := by
    rw [threeUAt_native, relationOnAt_native]
    exact B.nodes
  exact coefficientsAt P0.p (by decide) pow_eq_twist u (P3.fixedNodes R)
    B.a B.b B.α B.β B.output hp hnodes i hi
private theorem polarData_of_parallel {u : Words} {T : P3.TwoActive u} {R : P3.Relation T}
    {D : P3.Reduction u T R} (B : P3.RankThree u T R D)
    (hu : P3.FrontRemainder u) (hp : P3.Parallel B) (hn : ¬ P3.UnitNorm B) :
    Nonempty (P1_2.PolarData u) := by
  have hh : D.height + (P3.fixedNodes R).card ≤ P1_2.heightBound := by
    rw [D.height_eq]
    exact (P3.relation_height_le hu T).trans (by decide)
  have hfirst := (congrArg (fun A : Fin 2 → K[X] =>
    B.a.natDegree + amplitudeDegree (A 0) (A 1) ≤ D.height) hp).mpr B.first_degree
  exact polarData_of_set (P3.fixedNodes R) D.height B.a B.b B.α B.output hh
    B.output_degree hfirst B.second_degree B.a_ne hn B.α_primitive (coefficients B hp)
private theorem pencil_count {u : Words} (Γ : Finset K)
    (M : ∀ z ∈ Γ, P3.BadMark u z) {P Q : K[X]} (hP : P.degree < k)
    (hQ : Q.degree < k) (h : ∀ z (hz : z ∈ Γ), (M z hz).decoder = pencil P Q z) :
    Γ.card ≤ t + 1 := by
  classical
  by_cases hΓ : Γ.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hΓ]
  obtain ⟨r, hr⟩ := hΓ
  let S := (M r hr).support
  let nonjoint (i : I) := P.eval (node i) ≠ u 0 i ∨ Q.eval (node i) ≠ u 1 i
  have hits {z : K} (hz : z ∈ Γ) {i : I} (hi : i ∈ (M z hz).support) :
      P.eval (node i) + z * Q.eval (node i) = u 0 i + z * u 1 i := by
    simpa only [h z hz, pencil, eval_add, eval_mul, eval_C] using (M z hz).hits i hi
  have unique {z t : K} (hz : z ∈ Γ) (ht : t ∈ Γ) {i : I}
      (hi : i ∈ (M z hz).support) (hj : i ∈ (M t ht).support) (hn : nonjoint i) : z = t := by
    by_contra hne
    have h₁ := hits hz hi
    have h₂ := hits ht hj
    have hw : (z-t) * (Q.eval (node i) - u 1 i) = 0 := by linear_combination h₁ - h₂
    have he := sub_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left (sub_ne_zero.mpr hne))
    rw [he, add_right_cancel_iff] at h₁
    exact hn.elim (fun hbad => hbad h₁) (fun hbad => hbad he)
  have witness (z : ↥(Γ.erase r)) :
      ∃ i ∈ (M z.val (Finset.mem_erase.mp z.property).2).support, nonjoint i := by
    let W := M z.val (Finset.mem_erase.mp z.property).2
    by_contra hw
    apply W.nonjoint
    refine ⟨⟨P, hP, ?_⟩, ⟨Q, hQ, ?_⟩⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inl hn⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inr hn⟩
  choose f hf hn using witness
  let g : ↥(Γ.erase r) → ↥((Finset.univ : Finset I) \ S) := fun z =>
    ⟨f z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hi =>
      (Finset.mem_erase.mp z.property).1 (unique (Finset.mem_erase.mp z.property).2 hr (hf z) hi (hn z))⟩⟩
  have hg : Function.Injective g := by
    intro z t hzt
    have he : f z = f t := congrArg Subtype.val hzt
    apply Subtype.ext
    have ht := hf t
    rw [← he] at ht
    exact unique (Finset.mem_erase.mp z.property).2 (Finset.mem_erase.mp t.property).2 (hf z) ht (hn z)
  have hcard := Finset.card_le_card_of_injective hg
  have he := Finset.card_erase_add_one hr
  have hS : agreement ≤ S.card := (M r hr).agreement
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index] at hcard
  change 179983 ≤ S.card at hS
  change Γ.card ≤ 82162
  omega
private def asDonorMark {u : Words} {z : K} (M : P3.BadMark u z) : P1.BadMark u z :=
  ⟨M.support, M.decoder, (show P1.agreement ≤ agreement by decide).trans M.agreement,
    M.degree, M.hits, M.nonjoint⟩
theorem proof : P3.c2 := by
  intro u hu T R D B _ hp hn Γ hΓ _
  classical
  obtain ⟨data⟩ := polarData_of_parallel B hu hp hn
  let M (z : K) (hz : z ∈ Γ) := Classical.choice (P3.bad_mark u Γ hΓ z hz)
  rcases P1_2.pencil_of_marks data Γ (fun z hz => asDonorMark (M z hz)) with
    hsmall | ⟨P, Q, hP, hQ, h⟩
  · exact hsmall.trans (by decide)
  · exact pencil_count Γ M hP hQ h
end
end P3_2
end
section
namespace P3_6
noncomputable section
open Polynomial
open P3 (I K agreement)
open K1_13 (Geom extend Row Shape shape InBox Fits Contact remaining chart liftedChart
  mixed32 ceilDiv atJet OrderAt indexDegree)
open scoped BigOperators
abbrev Messages := P3.Messages
abbrev PoleData := P3.PoleData
abbrev physicalDegree := P3.physicalDegree
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev incidenceGap : ℕ := agreement - physicalDegree
abbrev anchorCutoff : ℕ := 90 * agreement - 1
abbrev primaryCutoff : ℕ := 3000 * agreement - 1
abbrev primaryBox : Shape := P0_9.primaryBox
abbrev sourceRank : ℕ := 0x107f1dec8090fc0a
abbrev layerWidth : ℕ := incidenceGap + 3
abbrev layerNeed : ℕ := 0x172dd72ade84
def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D
abbrev lowerCap : ℕ := 0x417306f5c2a90f
abbrev factorCap : ℕ := 0x32cdf437872295e
abbrev seedFee : ℕ := 140000
abbrev commonBox : Shape := ⟨6245, 2022, 0⟩
abbrev resultantBox : Shape := ⟨0x38c7faf0, 0x13315480, 0⟩
abbrev fatOrder : ℕ := 69360
abbrev divisorOrder : ℕ := 56875
abbrev isolatedOrder : ℕ := 1734
structure FatEquations where
  common : Row 3
  residual : Row 3
  common_ne : common ≠ 0
  residual_ne : residual ≠ 0
  common_total : common.totalDegree ≤ commonBox.b
  common_index : indexDegree common ≤ commonBox.j
  residual_total : residual.totalDegree ≤ resultantBox.b
  residual_index : indexDegree residual ≤ resultantBox.j
def FatEquations.holds (E : FatEquations) (S : Geom[X]) : Prop :=
  atJet E.common S = 0 ∨ OrderAt E.residual S fatOrder
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0 < (shape f).t ∧ InBox (shape f) ⟨120, 48, 10⟩ ∧
    TrueWeightLE f anchorCutoff
def LowerRow (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ 120 ∧ K1_13.indexDegree g ≤ 48 ∧ TrueWeightLE g anchorCutoff
structure Cover {n : ℕ} (Γ : Finset K) (s : K → K[X])
    (g : Row 3) (f : Fin n → Row 4) : Prop where
  lower : LowerRow g
  factors : ∀ i, SmallFactor (f i)
  different : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)
  fits : Fits (fun i => shape (f i))
  covers : ∀ γ ∈ Γ, K1_13.atJet g (extend (s γ)) = 0 ∨
    ∃ i, K1_13.OnFactor (f i) (extend (s γ))
def PrimaryRank (w : I → K) : Prop :=
  ∃ e : Fin sourceRank → Row 4, LinearIndependent Geom e ∧
    ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE (e i) primaryCutoff ∧ Contact w (e i)
def ProperCut (f : Row 4) (Γ : Finset K) (s : K → K[X]) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) primaryBox ∧ TrueWeightLE Q primaryCutoff ∧
    ∀ γ ∈ Γ, K1_13.OrderAt Q (extend (s γ)) l
def LayerBudget {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Prop :=
  layerNeed ≤
    ∑ r ∈ Finset.range (1 + primaryCutoff / layerWidth),
      remaining (∑ i, (r + 1 - l i) * (a i).b) (∑ i, (r + 1 - l i) * (a i).j)
def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
def surfaceNumerator32 (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixed32 p q (chart (L + 1) p) (chart (L + 2) p))
    (mixed32 p q a b + (L + 1) * mixed32 p q g b + (L + 2) * mixed32 p q g a)
def physicalPrice (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((P3.t + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (P3.t * curves + 2 * incidenceGap * points) (32 * incidenceGap)
def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := resultantBox
  let big : Shape := ⟨commonBox.b + q.b / divisorOrder, commonBox.j + q.j / divisorOrder, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j + 1)),
    max h.j (big.j + 1), max 1 h.t⟩
  let divisors := ceilDiv (P3.t * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b^2 + 5 * physicalDegree * p.b * h.b + 1
  let singular := if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b^2 + 1 else 0
  let curveLength := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  let curves := ceilDiv (P3.t * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * curveLength)
  let isolated := ceilDiv (3 * q.j^2 * (2 * q.b - q.j)) (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
  divisors + singular + curves + isolated
end
end P3_6
end
section
namespace P3_6
noncomputable section
open P3 (K)
open K1_13 (extend Row Shape shape Fits atJet OnFactor FatEligible)
open scoped BigOperators
def c1 : Prop :=
  ∀ w Γ s, Messages w Γ s →
    ∃ (n : ℕ) (g : Row 3) (f : Fin n → Row 4), Cover Γ s g f
def c2 : Prop := ∀ w, PrimaryRank w
def c3 : Prop :=
  ∀ w Γ s, Messages w Γ s → PrimaryRank w →
    ∀ n (g : Row 3) (f : Fin n → Row 4), Cover Γ s g f →
      ∃ l : Fin n → ℕ, LayerBudget (fun i => shape (f i)) l ∧
        ∀ i, 0 < l i → ProperCut (f i) Γ s (l i)
def c4 : Prop :=
  ∀ w Γ s, Messages w Γ s → PoleData Γ s →
    ∃ (book : Finset K) (E : FatEquations), book.card ≤ seedFee ∧
      ∀ γ ∈ Γ, γ ∉ book → E.holds (extend (s γ))
def c5 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ lowerCap
def c6 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → Γ.card ≤ physicalPrice (shape f) l
def c7 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) → FatEligible (shape f) →
    ∀ E : FatEquations, (∀ γ ∈ Γ, E.holds (extend (s γ))) → Γ.card ≤ fatPrice (shape f)
def c8 : Prop :=
  ∀ n (a : Fin n → Shape) (l cost : Fin n → ℕ), Fits a → LayerBudget a l →
    (∀ i, 0 < l i → cost i ≤ physicalPrice (a i) (l i)) →
    (∀ i, FatEligible (a i) → cost i ≤ fatPrice (a i)) →
    (∑ i, cost i) ≤ factorCap
theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  ⟨h.distinct.mono hΔ, fun γ hγ => h.degree γ (hΔ hγ), fun γ hγ => h.hits γ (hΔ hγ)⟩
theorem ProperCut.mono {f Γ s l Δ} (h : ProperCut f Γ s l) (hΔ : Δ ⊆ Γ) :
    ProperCut f Δ s l := by
  obtain ⟨Q, hf, hbox, hw, hQ⟩ := h
  exact ⟨Q, hf, hbox, hw, fun γ hγ => hQ γ (hΔ hγ)⟩
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (h5 : c5) (h6 : c6) (h7 : c7) (h8 : c8) : P3.c6 := by
  classical
  intro u D M Γ F lo hi
  let s := F.scalar
  have hmsg : Messages M.word Γ s := P3.messages_of_anchor M F hi
  obtain ⟨pole⟩ := P3.pole_of_anchor M F lo hi
  obtain ⟨n, g, f, cover⟩ := h1 _ _ _ hmsg
  obtain ⟨l, layers, cut⟩ := h3 _ _ _ hmsg (h2 _) _ _ _ cover
  obtain ⟨book, E, booked, hE⟩ := h4 _ _ _ hmsg pole
  let low := Γ.filter (fun γ => atJet g (extend (s γ)) = 0)
  have low_bound : low.card ≤ lowerCap :=
    h5 _ _ _ (hmsg.mono (Finset.filter_subset _ _)) _ cover.lower
      (fun _ h => (Finset.mem_filter.mp h).2)
  let pieces (i : Fin n) := Γ.filter (fun γ => γ ∉ book ∧ OnFactor (f i) (extend (s γ)))
  have part_sub (i) : pieces i ⊆ Γ := Finset.filter_subset _ _
  have on_part i : ∀ γ ∈ pieces i, OnFactor (f i) (extend (s γ)) :=
    fun _ h => (Finset.mem_filter.mp h).2.2
  have total := h8 n (fun i => shape (f i)) l (fun i => (pieces i).card) cover.fits layers
    (fun i h => h6 _ _ _ (hmsg.mono (part_sub i)) _ (cover.factors i) (on_part i) _ h
      ((cut i h).mono (part_sub i)))
    (fun i h => h7 _ _ _ (hmsg.mono (part_sub i)) _ (cover.factors i) (on_part i) h E
      (fun γ hγ => hE γ (part_sub i hγ) (Finset.mem_filter.mp hγ).2.1))
  have covers : Γ ⊆ book ∪ low ∪ Finset.univ.biUnion pieces := by
    intro γ hγ
    by_cases hb : γ ∈ book
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
    rcases cover.covers γ hγ with hg | ⟨i, hfi⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hg⟩))
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, hb, hfi⟩⟩
  calc
    Γ.card ≤ _ := Finset.card_le_card covers
    _ ≤ (book.card + low.card) + ∑ i, (pieces i).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le)
    _ ≤ seedFee + lowerCap + factorCap := Nat.add_le_add (Nat.add_le_add booked low_bound) total
    _ = P3.lowCap := by decide
end
end P3_6
end
