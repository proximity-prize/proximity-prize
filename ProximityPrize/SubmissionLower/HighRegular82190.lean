import ProximityPrize.SubmissionLower.HighFamilyBase82190
import ProximityPrize.SubmissionLower.GoldBranch4
import ProximityPrize.SubmissionLower.UpperBranch8
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace HighFamily82190_5_1
noncomputable section
open K1_14 (Equation)
open P1_7_8 (Input ResidueLift Factors)
open P1_7_8_3 (JetRing ordinate openFactor graphIdeal tangentEquation le_saturate
  proper_mem_graph)
open P1_7_8_3_1 (velocity jetSeparant coefficientDerivative)
open P1_7_8_3_1_2
open Polynomial (C)
open TrivSqZeroExt
open scoped BigOperators Ring
open private flow flow_mul flow_C flow_sep flow_tangentEquation coeffDiff_one
  coeff_coeffDiff dx_nat from ProximityPrize.SubmissionLower.UpperBranch8
theorem cancel_unit {R : Type*} [CommRing R] {a b c : R}
    (ha : IsUnit a) (h : a*b = a*c) : b = c := by
  simpa only [Ring.inverse_mul_cancel_left _ _ ha] using congrArg (fun x => a⁻¹ʳ * x) h
theorem finite_zero (J : Input) (B : ResidueLift J) (D : Factors J B)
    {N : JetRing} (h : N ∈ graphIdeal J B D) : finite J B D N = 0 := by
  simp only [finite, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]
theorem overlap_unit (J : Input) (B : ResidueLift J) (D : Factors J B) :
    IsUnit (finite J B D (ordinate * openFactor J B)) :=
  IsLocalization.Away.algebraMap_isUnit (overlapFactor J B D)
theorem separant_unit (J : Input) (B : ResidueLift J) (D : Factors J B) :
    IsUnit (finite J B D (jetSeparant J.f)) := by
  apply isUnit_of_dvd_unit _ (overlap_unit J B D)
  refine map_dvd (finite J B D) ⟨ordinate * P1_7_8_3.residueInJet B, ?_⟩
  change ordinate * (P1_7_8_3.residueInJet B * jetSeparant J.f) = _
  ring
private def firstJet {R : Type*} [CommRing R] (f : Equation) (ev : JetRing →+* R) :
    JetRing →+* TrivSqZeroExt R R where
  toFun N := ⟨ev N, ev (flow f N)⟩
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one ev
    · change ev (flow f 1) = 0
      rw [← Polynomial.C_1, flow_C, coeffDiff_one, Polynomial.derivative_one]
      simp
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_add' N M := by
    apply TrivSqZeroExt.ext
    · exact map_add ev N M
    · change ev (flow f (N+M)) = ev (flow f N) + ev (flow f M)
      rw [map_add, map_add]
  map_mul' N M := by
    apply TrivSqZeroExt.ext
    · exact map_mul ev N M
    · change ev (flow f (N*M)) = ev N * ev (flow f M) + ev (flow f N) * ev M
      rw [flow_mul, map_add, map_mul, map_mul]
private theorem kills_saturation {R : Type*} [CommRing R] (ev : JetRing →+* R)
    {I : Ideal JetRing} {g : JetRing} (hg : IsUnit (ev g)) (hI : I ≤ RingHom.ker ev)
    {N : JetRing} (hN : N ∈ P1_7_8_3.saturate I g) : ev N = 0 := by
  obtain ⟨n, hn⟩ := hN
  have h : ev (g^n * N) = 0 := hI hn
  rw [map_mul, map_pow, ← mul_zero ((ev g)^n)] at h
  exact cancel_unit (hg.pow n) h
theorem finite_root (J : Input) (B : ResidueLift J) (D : Factors J B) :
    finite J B D (C J.f) = 0 := by
  rw [D.product, map_mul, map_mul, finite_zero J B D (proper_mem_graph J B D), zero_mul]
private theorem firstJet_graph {R : Type*} [CommRing R]
    (J : Input) (B : ResidueLift J) (D : Factors J B) (ev : JetRing →+* R)
    (hP : ev (C D.proper) = 0) (hT : ev (tangentEquation J.f) = 0)
    (hc : IsUnit (ev (jetSeparant J.f))) (hg : IsUnit (ev (openFactor J B))) :
    ∀ N ∈ graphIdeal J B D, firstJet J.f ev N = 0 := by
  let H : Equation := ∏ j, D.flat j
  have hf : J.f = D.proper * H := D.product
  have hC : ev (jetSeparant J.f) = ev (C D.proper.derivative) * ev (C H) := by
    change ev (C J.f.derivative) = _
    rw [hf, Polynomial.derivative_mul]
    simp only [map_add, map_mul, hP, zero_mul, add_zero]
  have hH : IsUnit (ev (C H)) := isUnit_of_dvd_unit
    ⟨ev (C D.proper.derivative), hC.trans (mul_comm _ _)⟩ hc
  have hs : ev (flow J.f (C J.f)) = 0 := by
    rw [flow_C]
    change ev (jetSeparant J.f * tangentEquation J.f) = 0
    rw [map_mul, hT, mul_zero]
  have hflow : flow J.f (C J.f) =
      flow J.f (C D.proper * C H) := by rw [← map_mul, ← hf]
  rw [hflow, flow_mul, map_add, map_mul, map_mul, hP, zero_mul, zero_add, mul_comm,
    ← mul_zero (ev (C H))] at hs
  have hp : ev (flow J.f (C D.proper)) = 0 := cancel_unit hH hs
  intro N hN
  apply kills_saturation (firstJet J.f ev)
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr hg) _ hN
  apply Ideal.span_le.mpr
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact TrivSqZeroExt.ext hP hp
  · apply TrivSqZeroExt.ext
    · exact hT
    · change ev (flow J.f (tangentEquation J.f)) = 0
      rw [flow_tangentEquation, map_zero]
set_option backward.isDefEq.respectTransparency false in
private def derivationOfJet {R : Type*} [CommRing R]
    (j : R →+* TrivSqZeroExt R R) (hj : ∀ x, (j x).fst = x) (a : R) :
    ChartDerivation R := by
  let d : R →+ R :=
    { toFun := fun x => a * (j x).snd
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add] }
  refine Derivation.mk' d.toIntLinearMap (fun x y => ?_)
  change a * (j (x*y)).snd = x * (a * (j y).snd) + y * (a * (j x).snd)
  simp only [map_mul, snd_mul, op_smul_eq_smul, smul_eq_mul, hj]
  ring
theorem coeffDiff_X : coefficientDerivative (Polynomial.X : Equation) = 0 := by
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro m
  have h1 : K1_14_6_1.Dx 1 = 0 := by simpa only [Nat.cast_one] using dx_nat 1
  by_cases hi : 1 = i <;> by_cases hm : (0 : Fin 2 →₀ ℕ) = m <;>
    simp [coeff_coeffDiff, Polynomial.coeff_X, MvPolynomial.coeff_one, hi, hm, h1]
private theorem extendJet {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    (g : A) [IsLocalization.Away g R] (H : A →+* TrivSqZeroExt R R)
    (hH : ∀ n, (H n).fst = algebraMap A R n) {c : R} (hc : IsUnit c) :
    ∃ δ : ChartDerivation R, ∀ n, c * δ (algebraMap A R n) = (H n).snd := by
  have hU : IsUnit (H g) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hH]
    exact IsLocalization.Away.algebraMap_isUnit g
  let j : R →+* TrivSqZeroExt R R := IsLocalization.Away.lift g hU
  let fst' : TrivSqZeroExt R R →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom
  have hproj : fst'.comp j = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    apply RingHom.ext
    intro n
    change (j (algebraMap A R n)).fst = algebraMap A R n
    rw [IsLocalization.Away.lift_eq g hU, hH]
  refine ⟨derivationOfJet j (RingHom.congr_fun hproj) (Ring.inverse c), fun n => ?_⟩
  change c * (Ring.inverse c * (j (algebraMap A R n)).snd) = (H n).snd
  rw [Ring.mul_inverse_cancel_left _ _ hc, IsLocalization.Away.lift_eq g hU]
set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 120000 in
theorem finite_flow : P1_7_8_3_1_2.c1 := by
  intro J B D
  let ev := finite J B D
  have hg : IsUnit (ev (openFactor J B)) :=
    isUnit_of_dvd_unit (map_dvd ev ⟨ordinate, mul_comm _ _⟩) (overlap_unit J B D)
  have ht : ev (tangentEquation J.f) = 0 :=
    finite_zero J B D (le_saturate _ _ (Ideal.subset_span (by simp)))
  have hc := separant_unit J B D
  let H := Ideal.Quotient.lift (graphIdeal J B D) (firstJet J.f ev)
    (firstJet_graph J B D ev (finite_zero J B D (proper_mem_graph J B D)) ht hc hg)
  have hH (n : Graph J B D) : (H n).fst = algebraMap (Graph J B D) (Overlap J B D) n := by
    obtain ⟨N, rfl⟩ := Ideal.Quotient.mk_surjective n
    rfl
  obtain ⟨δ, hδ⟩ := extendJet (overlapFactor J B D) H hH hc
  have hd (N : JetRing) : ev (jetSeparant J.f) * δ (ev N) = ev (flow J.f N) :=
    hδ (Ideal.Quotient.mk _ N)
  refine ⟨δ, ⟨?_, ?_, hd⟩⟩
  · apply cancel_unit hc
    rw [hd]
    change ev (flow J.f (C Polynomial.X)) = _
    simp only [flow_C, Polynomial.derivative_X, coeffDiff_X, map_zero, zero_add, map_one,
      mul_one, map_mul]
    rfl
  · apply cancel_unit hc
    rw [hd, flow_sep, map_mul]
    rfl
end
end HighFamily82190_5_1
end
section
set_option autoImplicit false
namespace HighFamily82190_5
noncomputable section
open Front82190 (agreement blockLength)
open HighFamily82190 (degreeAt quotientOrder gap scale muNum lambdaNum properFee)
open P1_7_8 (Input cutSeed cutVelocity cutOrdinate ratio_le_ceil mu_cross lambda_cross)
def nodeVelocity (J : Input) : ℕ := lambdaNum J.hi * quotientOrder J.lo
def nodeReducedOrdinate (J : Input) : ℕ := muNum J.hi + (J.e-3)*nodeVelocity J
def nodeSeed (J : Input) : ℕ := nodeVelocity J*J.v + 2*J.hi*muNum J.hi
def weightedSection (J : Input) (h t s : ℕ) : ℕ :=
  nodeReducedOrdinate J*h + nodeVelocity J*t + nodeSeed J*s
theorem incidence_weights (J : Input) (hd : degreeAt J.hi < agreement) (s : ℕ) (hs : s ≤ degreeAt J.hi) :
    scale J.hi * (blockLength-s) ≤ (agreement-s) * muNum J.hi ∧
    scale J.hi * (blockLength-s) * (J.ell-s) ≤ (agreement-s) * nodeVelocity J := by
  have hAn : agreement ≤ blockLength := by decide
  have hL : quotientOrder J.lo ≤ agreement :=
    (Nat.sub_le _ _).trans (by decide : 131071 ≤ agreement)
  have hr : J.ell-s ≤ quotientOrder J.lo-s := by
    exact Nat.sub_le_sub_right (Nat.sub_le_sub_left J.lower _) _
  have hMu := Nat.mul_le_mul_left agreement (mu_cross hAn hd.le hs)
  have hLam := Nat.mul_le_mul_left (gap J.hi)
    (lambda_cross hAn hL (hs.trans hd.le))
  constructor
  · unfold scale muNum gap
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hMu
  · calc
      _ ≤ scale J.hi * (blockLength-s) * (quotientOrder J.lo-s) :=
        Nat.mul_le_mul_left _ hr
      _ ≤ _ := by
        unfold scale nodeVelocity lambdaNum
        convert hLam using 1 <;> ring
theorem scale_pos (J : Input) (hd : degreeAt J.hi < agreement) : 0 < scale J.hi :=
  Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hd)
theorem unit_le_weight (J : Input) {h t s : ℕ} (hp : 0 < s) :
    scale J.hi ≤ weightedSection J h t s := by
  have hAn : agreement ≤ blockLength := by decide
  have hm : scale J.hi ≤ muNum J.hi :=
    Nat.mul_le_mul_left agreement (Nat.sub_le_sub_right hAn _)
  have hw : 1 ≤ 2*J.hi := by
    have := J.positive.trans_le J.upper
    omega
  have hn : muNum J.hi ≤ nodeSeed J := by
    have H := Nat.mul_le_mul_right (muNum J.hi) hw
    rw [Nat.one_mul] at H
    exact H.trans (Nat.le_add_left _ _)
  exact (hm.trans hn).trans
    ((by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (nodeSeed J) hp :
      nodeSeed J ≤ nodeSeed J*s).trans (Nat.le_add_left _ _))
theorem mix_to_fee (J : Input) (hd : degreeAt J.hi < agreement) {k : ℕ}
    (h : scale J.hi*k ≤
      weightedSection J (J.v*cutSeed J + J.v^2*cutVelocity J)
        (2*J.e*J.v*cutSeed J + J.v^2*cutOrdinate J)
        (J.e*cutSeed J + J.v*((2*J.e-2)*cutVelocity J + cutOrdinate J))) :
    k ≤ properFee J.lo J.hi J.e J.v := by
  have he : (J.e-3)+2 = J.e-1 := by have h : 3 ≤ J.e := J.sheets; omega
  have he' : (2*J.e-2)+2 = 2*J.e := by have h : 3 ≤ J.e := J.sheets; omega
  have hco : 2*cutVelocity J ≤ cutOrdinate J := by
    have htwo : 2 ≤ J.e-1 := by have h : 3 ≤ J.e := J.sheets; omega
    exact (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (cutVelocity J) htwo :
      2*cutVelocity J ≤ cutVelocity J*(J.e-1)).trans (Nat.le_add_left _ _)
  let nA := muNum J.hi + nodeVelocity J*(J.e-1)
  have hnA : nodeReducedOrdinate J + 2*nodeVelocity J = nA := by
    unfold nodeReducedOrdinate
    dsimp only [nA]
    rw [← he]
    ring
  have hc : cutOrdinate J - 2*cutVelocity J + 2*cutVelocity J = cutOrdinate J :=
    Nat.sub_add_cancel hco
  unfold properFee
  apply ratio_le_ceil (scale_pos J hd)
  refine h.trans_eq ?_
  change weightedSection J _ _ _ =
    J.e*cutSeed J*nodeSeed J +
      J.v*(nodeSeed J*((2*J.e-2)*cutVelocity J + cutOrdinate J) +
        cutSeed J*((2*J.e-2)*nodeVelocity J + nA)) +
      J.v^2*((cutOrdinate J - 2*cutVelocity J)*nodeVelocity J + nA*cutVelocity J)
  generalize 2*J.e-2 = em at he' ⊢
  generalize cutOrdinate J - 2*cutVelocity J = ac0 at hc ⊢
  rw [← hnA, ← he', ← hc]
  unfold weightedSection
  ring
end
end HighFamily82190_5
end
section
namespace HighFamily82190_5
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open Front82190 (K I node agreement)
open HighFamily82190 (FixedWord)
open private occupancy from ProximityPrize.SubmissionLower.Fast055
open private incidence_arithmetic from ProximityPrize.SubmissionLower.PortHighBase
theorem section_capacity {w T s d} (h : FixedWord w T s d) (hd : d < agreement) (cap : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ T, (s γ).eval (node i) ≠ w i) →
      (T.filter fun γ => (s γ).eval (node i) = w i).card ≤ cap) :
    (agreement - d) * T.card ≤ Front82190.t * cap + (agreement - d) := by
  classical
  by_cases hm : T.card ≤ 1
  · have hb := Nat.mul_le_mul_left (agreement - d) hm
    simp only [Nat.mul_one] at hb
    omega
  let hits (γ : K) : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
  let common : Finset I := univ.filter fun i => ∀ γ ∈ T, (s γ).eval (node i) = w i
  let nodes : Finset I := univ \ common
  have common_le (γ : K) (hγ : γ ∈ T) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K) (hγ : γ ∈ T) : agreement ≤ (hits γ).card := by
    obtain ⟨B, hB, hval⟩ := h.hits γ hγ
    exact hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hval i hi⟩)
  have pair_count (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ d := by
    let P := s a - s b
    have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (h.distinct ha hb eq)
    refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
      P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (h.degree a ha) (h.degree b hb)))
    intro i hi
    change ((s a) - (s b)).eval (node i) = 0
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < T.card)
  have hcommon : common.card ≤ d :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := agreement - common.card
  let t := d - common.card
  have ht : t = x - (agreement - d) := by dsimp [t, x]; omega
  have hx : agreement - d ≤ x := by dsimp [x]; omega
  have hnodes : nodes.card = x + Front82190.t := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    change 262144 - common.card = (179954 - common.card) + 82190
    have hbound : common.card ≤ 179954 := hcommon.trans hd.le
    omega
  have exists_trim (γ : K) : ∃ B : Finset I, γ ∈ T → B ⊆ hits γ \ common ∧ B.card = x := by
    by_cases hγ : γ ∈ T
    · have hc := hit_count γ hγ
      have hsize : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨B, hB, hcard⟩ := exists_subset_card_eq hsize
      exact ⟨B, fun _ => ⟨hB, hcard⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose B hB using exists_trim
  have into_nodes (γ : K) (hγ : γ ∈ T) : B γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (B a ∩ B b).card ≤ t := by
    have cover : (B a ∩ B b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with hi | hi
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hB a ha).1 (mem_inter.mp hi).1)).1,
          (mem_sdiff.mp ((hB b hb).1 (mem_inter.mp hi).2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hi, common_le b hb hi⟩
    have disj : Disjoint (B a ∩ B b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : I) (hi : i ∈ nodes) : (T.filter fun γ => i ∈ B γ).card ≤ cap := by
    have proper : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp (mem_sdiff.mp ((hB γ hγ).1 hi)).1).2⟩
  obtain ⟨second, first⟩ := occupancy T nodes B x t cap
    (fun γ hγ => ⟨into_nodes γ hγ, (hB γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at second
  rw [hnodes] at first
  exact incidence_arithmetic Front82190.t _ _ _ _ (by omega) (by omega) hx (by decide) second first
end
end HighFamily82190_5
end
section
set_option autoImplicit false
namespace HighFamily82190_5
noncomputable section
open Polynomial Finset
open Front82190 (K I agreement blockLength node p)
open HighFamily82190 (FixedWord degreeAt gap scale muNum properFee flatFee)
open K1_14 (Equation graphEval)
open K1_14_4 (seedDegree)
open P1_7_8 (Input ResidueLift Factors ProperCurve ProperCover FlatSections
  card_le_cover componentMarks mem_componentMarks root_component
  ratio_le_ceil)
open private persistent_le_degree from ProximityPrize.SubmissionLower.UpperBranch8
open scoped BigOperators
private theorem restrict_word {word U scalar d} (hword : FixedWord word U scalar d)
    {V : Finset K} (hV : V ⊆ U) : FixedWord word V scalar d :=
  ⟨hword.distinct.mono hV, fun γ hγ => hword.degree γ (hV hγ),
    fun γ hγ => hword.hits γ (hV hγ)⟩
theorem proper_curve_count (J : Input) (hd : degreeAt J.hi < agreement)
    (hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi)) {B : ResidueLift J} {D : Factors J B}
    (C : ProperCurve J B D) :
    scale J.hi * C.marks.card ≤ weightedSection J C.fiber C.tangent C.seed := by
  classical
  by_cases hsmall : C.marks.card ≤ 1
  · have hm := Nat.mul_le_mul_left (scale J.hi) hsmall
    rw [Nat.mul_one] at hm
    exact hm.trans (unit_le_weight J C.positive_seed)
  let s := C.persistent.card
  let r := J.ell - s
  let N := (univ : Finset I) \ C.persistent
  let hit (γ : K) (x : I) := (J.family.scalar γ).eval (node x) = J.model.word x
  have hsd : s ≤ degreeAt J.hi := persistent_le_degree J C (by omega)
  have hs : 0 < agreement - s := Nat.sub_pos_of_lt (hsd.trans_lt hd)
  have hN : N.card = blockLength - s := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    exact congrArg (· - s) ProximityPrize.Benchmark.IRSProfile.card_index
  have hagree (γ : K) (hγ : γ ∈ C.marks) : agreement - s ≤ (N.filter (hit γ)).card := by
    obtain ⟨Aγ,hAγ,he⟩ := hword.hits γ (C.sub hγ)
    have hsub : Aγ \ C.persistent ⊆ N.filter (hit γ) := by
      intro x hx
      obtain ⟨hxa,hxp⟩ := mem_sdiff.mp hx
      exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, hxp⟩, he x hxa⟩
    have hbound := card_le_card hsub
    have hpart := card_sdiff_add_card_eq_card (inter_subset_left :
      Aγ ∩ C.persistent ⊆ Aγ)
    have hs' := card_le_card (inter_subset_right : Aγ ∩ C.persistent ⊆ C.persistent)
    have heq : Aγ \ (Aγ ∩ C.persistent) = Aγ \ C.persistent := by
      ext x
      simp only [mem_sdiff, mem_inter]
      tauto
    rw [heq] at hpart
    omega
  let sec := (1+(J.e-3)*r)*C.fiber + r*C.tangent + (r*J.v + 2*J.w)*C.seed
  have hsums :
      (agreement-s)*C.marks.card ≤ (blockLength-s)*sec := by
    calc
      _ = ∑ γ ∈ C.marks, (agreement-s) := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ γ ∈ C.marks, (N.filter (hit γ)).card := sum_le_sum hagree
      _ = ∑ x ∈ N, (C.marks.filter (fun γ => hit γ x)).card := by
        simp only [card_filter]
        rw [sum_comm]
      _ ≤ ∑ _x ∈ N, sec :=
        sum_le_sum fun x hx => C.sections x (mem_sdiff.mp hx).2
      _ = _ := by rw [sum_const, smul_eq_mul, hN]
  obtain ⟨hMu, hLam⟩ := incidence_weights J hd s hsd
  have hw : 2*J.w ≤ 2*J.hi := Nat.mul_le_mul_left 2 J.upper
  have h0 := Nat.mul_le_mul_right C.fiber hMu
  have h1 := Nat.mul_le_mul_right ((J.e-3)*C.fiber+C.tangent+J.v*C.seed) hLam
  have h2 := Nat.mul_le_mul_right C.seed (Nat.mul_le_mul hMu hw)
  apply Nat.le_of_mul_le_mul_left _ hs
  calc
    _ = scale J.hi * ((agreement-s)*C.marks.card) := by ring
    _ ≤ scale J.hi * ((blockLength-s)*sec) := Nat.mul_le_mul_left _ hsums
    _ = scale J.hi*(blockLength-s)*C.fiber +
        scale J.hi*(blockLength-s)*r*((J.e-3)*C.fiber+C.tangent+J.v*C.seed) +
        scale J.hi*(blockLength-s)*(2*J.w)*C.seed := by
      dsimp only [sec]
      ring
    _ ≤ (agreement-s)*muNum J.hi*C.fiber +
        (agreement-s)*nodeVelocity J*((J.e-3)*C.fiber+C.tangent+J.v*C.seed) +
        ((agreement-s)*muNum J.hi)*(2*J.hi)*C.seed :=
      Nat.add_le_add (Nat.add_le_add h0 h1) h2
    _ = _ := by unfold weightedSection nodeReducedOrdinate nodeSeed; ring
theorem proper_count (J : Input) (hd : degreeAt J.hi < agreement)
    (hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi)) {B : ResidueLift J} {D : Factors J B}
    (C : ProperCover J B D) :
    (componentMarks J D.proper).card ≤ properFee J.lo J.hi J.e J.v := by
  classical
  have hcov := card_le_cover (componentMarks J D.proper)
      (fun j => (C.curves j).marks) (fun γ hγ =>
        C.covers γ (mem_componentMarks.mp hγ).1 (mem_componentMarks.mp hγ).2)
  apply mix_to_fee J hd
  calc
    _ ≤ ∑ j, scale J.hi * (C.curves j).marks.card := by
      rw [← mul_sum]
      exact Nat.mul_le_mul_left _ hcov
    _ ≤ ∑ j, weightedSection J (C.curves j).fiber (C.curves j).tangent (C.curves j).seed :=
      sum_le_sum fun j _ => proper_curve_count J hd hword (C.curves j)
    _ = weightedSection J (∑ j, (C.curves j).fiber) (∑ j, (C.curves j).tangent)
          (∑ j, (C.curves j).seed) := by
      simp only [weightedSection, sum_add_distrib, mul_sum]
    _ ≤ _ :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left _ C.fiber) (Nat.mul_le_mul_left _ C.tangent))
        (Nat.mul_le_mul_left _ C.seed)
theorem flat_component_count (J : Input) (hd : degreeAt J.hi < agreement)
    (hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi)) (q : Equation) (hq : seedDegree q < p)
    (B : FlatSections J q) :
    gap J.hi * (componentMarks J q).card ≤ Front82190.t * ((p+1)*seedDegree q) + gap J.hi := by
  classical
  let U := componentMarks J q
  have hU : U ⊆ J.marks := fun _ hz => (mem_componentMarks.mp hz).1
  apply section_capacity (restrict_word hword hU) hd ((p+1)*seedDegree q)
  intro x hx
  obtain ⟨γ,hγ,hval⟩ := hx
  obtain ⟨g,hg,hgd,he⟩ := B x ⟨γ,(mem_componentMarks.mp hγ).1,(mem_componentMarks.mp hγ).2,hval⟩
  let V := U.filter fun γ => (J.family.scalar γ).eval (node x) = J.model.word x
  let C : K1_14_3.SeedCover := ⟨g,hg,∅⟩
  have hcount := K1_14_3.seed_count (T := V) (label := J.model.label)
      (fun _ _ _ _ heq => sub_left_inj.mp heq) C (hgd.trans_lt hq) (by
        intro η hη
        obtain ⟨hm,ht⟩ := mem_filter.mp hη
        exact Or.inl (he η (mem_componentMarks.mp hm).1 (mem_componentMarks.mp hm).2 ht))
  exact (by simpa only [C, card_empty, Nat.add_zero] using hcount :
    V.card ≤ (p+1)*g.totalDegree).trans (Nat.mul_le_mul_left _ hgd)
theorem flat_count (J : Input) (hd : degreeAt J.hi < agreement)
    (hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi)) {B : ResidueLift J} (D : Factors J B)
    (hsections : ∀ j, FlatSections J (D.flat j)) :
    (∑ j, (componentMarks J (D.flat j)).card) ≤ flatFee J.hi J.v + J.e := by
  classical
  let U := fun j => componentMarks J (D.flat j)
  let n := ∑ j, (U j).card
  let g := gap J.hi
  have hg : 0 < g := Nat.sub_pos_of_lt hd
  have hv : J.v < p := (Nat.le_add_left J.v (J.e * degreeAt J.hi)).trans_lt J.flat_guard
  have hsum : g*n ≤ Front82190.t*(p+1)*J.v + g*D.count := by
    calc
      _ = ∑ j, g*(U j).card := mul_sum ..
      _ ≤ ∑ j, (Front82190.t*((p+1)*seedDegree (D.flat j)) + g) := by
        refine sum_le_sum fun j _ => ?_
        have hu : seedDegree (D.flat j) ≤ ∑ i, seedDegree (D.flat i) :=
          single_le_sum (f := fun i => seedDegree (D.flat i)) (fun _ _ => Nat.zero_le _) (mem_univ j)
        exact flat_component_count J hd hword (D.flat j) (hu.trans_lt (D.seed_sum.trans_lt hv)) (hsections j)
      _ = Front82190.t*(p+1)*(∑ j, seedDegree (D.flat j)) + g*D.count := by
        rw [sum_add_distrib, sum_const, smul_eq_mul, card_univ, Fintype.card_fin,
          ← mul_sum, ← mul_sum, mul_assoc, Nat.mul_comm D.count]
      _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left _ D.seed_sum) _
  have hrem : g*(n-D.count) ≤ Front82190.t*(p+1)*J.v := by
    rw [Nat.mul_sub_left_distrib]
    omega
  have hceil := ratio_le_ceil hg hrem
  have hsize : D.count ≤ J.e := D.sheets
  change n ≤ flatFee J.hi J.v + J.e
  change n-D.count ≤ flatFee J.hi J.v at hceil
  omega
theorem count (J : Input) (hd : degreeAt J.hi < agreement)
    (hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi)) {B : ResidueLift J} {D : Factors J B}
    (C : ProperCover J B D) (hsections : ∀ j, FlatSections J (D.flat j)) :
    J.marks.card ≤ HighFamily82190.tangentFee J.lo J.hi J.e J.v := by
  classical
  let T := componentMarks J D.proper
  let U := fun j => componentMarks J (D.flat j)
  have hcov : J.marks ⊆ T ∪ univ.biUnion U := by
    intro γ hγ
    rcases root_component J D hγ with ht | ⟨j, hu⟩
    · exact mem_union.mpr (Or.inl (mem_componentMarks.mpr ⟨hγ,ht⟩))
    · exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨j,mem_univ _,mem_componentMarks.mpr ⟨hγ,hu⟩⟩))
  have hc := (card_le_card hcov).trans (card_union_le _ _)
  have hp := proper_count J hd hword C
  have hf := card_biUnion_le.trans (flat_count J hd hword D hsections)
  change T.card ≤ properFee J.lo J.hi J.e J.v at hp
  change (univ.biUnion U).card ≤ flatFee J.hi J.v + J.e at hf
  change J.marks.card ≤ T.card + (univ.biUnion U).card at hc
  unfold HighFamily82190.tangentFee
  omega
end
end HighFamily82190_5
end
section
set_option autoImplicit false
namespace HighFamily82190_5
open Front82190 (p agreement)
open HighFamily82190 (degreeAt quotientOrder window_nat terminal_guards grade_checked
  asP1Model asP1Family FixedWord)
open P1_7_8 (Input)
def c1 : Prop := P1_7_8_3_1.c2
def c2 : Prop := P1_7_8_3_2.c4
theorem of_children (inverse : c1) (profiles : c2) : HighFamily82190.c5 := by
  intro b u del M Γ F hw hshift H hH i f hred he hlarge hpos hseed T hT hreg
  obtain ⟨hl, hu⟩ := window_nat hw
  obtain ⟨hlo, hhi, -, -, -⟩ := terminal_guards b
  have h : 0 < M.overhead.toNat := hlo.trans_le hl
  have hell : 0 < quotientOrder M.overhead.toNat := by
    change 0 < 131071 - M.overhead.toNat
    omega
  have hd : degreeAt (Front82190.row b).hi ≤ 164378 := Nat.add_le_add_left hhi 131071
  have hgap₁ : degreeAt (Front82190.row b).hi < P1.agreement := hd.trans_lt (by decide)
  have hgap₃ : degreeAt (Front82190.row b).hi < agreement := hd.trans_lt (by decide)
  have hfac : degreeAt (Front82190.row b).hi + 1 < p :=
    (Nat.succ_le_of_lt hgap₁).trans_lt (by decide)
  have hc := grade_checked b i
  rw [← he] at hc
  let J : Input := {
    words := u, deleted := del, model := asP1Model M, labels := Γ, family := asP1Family M F
    shift_out := hshift, block := H, chart := hH, marks := T, marks_sub := hT
    f := f, regular := hreg, reduced := hred, sheets := hlarge, seed_pos := hpos
    v := ((HighFamily82190.grades b).get i).seedCap, seed_bound := hseed
    lo := (Front82190.row b).lo, hi := (Front82190.row b).hi, lower := hl, upper := hu, positive := h
    quotient_pos := hell, agreement_gap := hgap₁, factorial_guard := hfac
    separant_guard := hc.separant, flat_guard := hc.flat }
  have hweak := P1_7_8.fixed_word J (Finset.Subset.refl J.marks)
  have hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi) :=
    ⟨hweak.distinct, hweak.degree, fun γ hγ => by
      let m := F.mark γ (hT hγ)
      exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩⟩
  obtain ⟨B⟩ := P1_7_8_1.proof J
  obtain ⟨D⟩ := P1_7_8_2.proof J B
  have lift := P1_7_8_3_1.of_children P1_7_8_3_1_1.proof inverse
  have mixed := P1_7_8_3_2.of_children P1_7_8_3_2_1.proof P1_7_8_3_2_2.proof
    P1_7_8_3_2_3.proof profiles P1_7_8_3_2_5.proof P1_7_8_3_2_6.proof
  have shorten := P1_7_8_3_3.of_children P1_7_8_3_3_1.proof P1_7_8_3_3_2.proof
  obtain ⟨C⟩ := P1_7_8_3.of_children lift mixed shorten J B D
  apply count J hgap₃ hword C
  intro j
  obtain ⟨E⟩ := P1_7_8_4.of_children P1_7_8_4_1.proof P1_7_8_4_2.proof J B D j
  exact P1_7_8_5.of_children P1_7_8_5_1.proof P1_7_8_5_2.proof J B D j E
end HighFamily82190_5
end
section
set_option autoImplicit false
namespace HighFamily82190_5_1
noncomputable section
open K1_14 (Equation Seeds)
open P1_7_8_3 (JetRing ordinate)
open P1_7_8_3_1 (velocity jetSeparant coefficientDerivative secondAlongVelocity)
open P1_7_8_3_1_2
open Polynomial (C eval₂RingHom)
open private flow flow_mul flow_C flow_X coeffDiff_add coeffDiff_mul coeff_coeffDiff
  coeffDiff_derivative from ProximityPrize.SubmissionLower.UpperBranch8
open private eval_coefficient from ProximityPrize.SubmissionLower.UpperBranch8
private theorem coeffDiff_C (s : Seeds) :
    coefficientDerivative (C s) = C (P1_7_8_4.coeffDx s) := by
  apply Polynomial.ext
  intro n
  apply MvPolynomial.ext
  intro m
  cases n <;> simp [coeff_coeffDiff, P1_7_8_4.coeff_coeffDx]
private theorem deriv_mul {R : Type*} [CommRing R] (δ : ChartDerivation R) (x y : R) :
    δ (x*y) = x*δ y + δ x*y := by
  rw [δ.leibniz, smul_eq_mul, smul_eq_mul, mul_comm y]
private theorem root_chain {R : Type*} [CommRing R] (δ : ChartDerivation R)
    (E : Equation →+* R)
    (hs : ∀ s : Seeds, δ (E (C s)) = E (C (P1_7_8_4.coeffDx s))) (N : Equation) :
    δ (E N) = E (coefficientDerivative N) + δ (E Polynomial.X) * E N.derivative := by
  have hstep (p q : Equation)
      (hp : δ (E p) = E (coefficientDerivative p) + δ (E Polynomial.X) * E p.derivative)
      (hq : δ (E q) = E (coefficientDerivative q) + δ (E Polynomial.X) * E q.derivative) :
      δ (E (p*q)) = E (coefficientDerivative (p*q)) + δ (E Polynomial.X) * E (p*q).derivative := by
    simp only [map_mul, deriv_mul, hp, hq, coeffDiff_mul, Polynomial.derivative_mul, map_add]
    ring
  have hx : δ (E Polynomial.X) =
      E (coefficientDerivative Polynomial.X) + δ (E Polynomial.X) * E Polynomial.X.derivative := by
    simp only [coeffDiff_X, Polynomial.derivative_X, map_zero, zero_add, map_one, mul_one]
  induction N using Polynomial.induction_on with
  | C s => simp only [hs, coeffDiff_C, Polynomial.derivative_C, map_zero, mul_zero, add_zero]
  | add p q hp hq =>
    simp only [map_add, hp, hq, coeffDiff_add, mul_add]
    ring
  | monomial n s ih =>
    rw [pow_succ, ← mul_assoc]
    exact hstep _ _ ih hx
private theorem jet_chain {R : Type*} [CommRing R] (δ : ChartDerivation R)
    (ev : JetRing →+* R) (f : Equation)
    (hC : ∀ q : Equation, δ (ev (C q)) =
      ev (C (coefficientDerivative q)) + ev velocity * ev (C q.derivative))
    (hX : ev (jetSeparant f) * δ (ev velocity) = -ev (secondAlongVelocity f))
    (N : JetRing) : ev (jetSeparant f) * δ (ev N) = ev (flow f N) := by
  have hstep (p q : JetRing)
      (hp : ev (jetSeparant f) * δ (ev p) = ev (flow f p))
      (hq : ev (jetSeparant f) * δ (ev q) = ev (flow f q)) :
      ev (jetSeparant f) * δ (ev (p*q)) = ev (flow f (p*q)) := by
    simp only [flow_mul, map_add, map_mul, deriv_mul]
    linear_combination ev p * hq + ev q * hp
  have hx : ev (jetSeparant f) * δ (ev velocity) = ev (flow f velocity) := by
    simpa only [flow_X, map_neg] using hX
  induction N using Polynomial.induction_on with
  | C s => rw [hC, flow_C, map_mul, map_add, map_mul]
  | add p q hp hq => simp only [map_add, mul_add, hp, hq]
  | monomial n s ih =>
    rw [pow_succ, ← mul_assoc]
    exact hstep _ _ ih hx
private theorem ordinate_deriv {R : Type*} [CommRing R] (δ : ChartDerivation R)
    {y z v : R} (hy : y*z = 1) (hv : δ y = v) : δ z = -(v*z^2) := by
  have h := congrArg (fun t => δ t) hy
  rw [deriv_mul, Derivation.map_one_eq_zero, hv] at h
  linear_combination z * h - δ z * hy
private theorem reverse_euler (f : Equation) (e : ℕ) (hf : f.natDegree ≤ e) :
    (Polynomial.X * f.derivative).reflect e + Polynomial.X * (f.reflect e).derivative =
      C (e : Seeds) * f.reflect e := by
  have hcoeff (g : Equation) (n : ℕ) : (Polynomial.X*g.derivative).coeff n = g.coeff n * (n : Seeds) := by
    cases n with
    | zero => simp
    | succ n => simp only [Polynomial.coeff_X_mul,
        Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one]
  apply Polynomial.ext
  intro n
  simp only [Polynomial.coeff_add, Polynomial.coeff_reflect, hcoeff, Polynomial.coeff_C_mul]
  by_cases hn : n ≤ e
  · rw [Polynomial.revAt_le hn, ← mul_add, ← Nat.cast_add, Nat.sub_add_cancel hn, mul_comm]
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hn),
      Polynomial.coeff_eq_zero_of_natDegree_lt (hf.trans_lt (Nat.lt_of_not_ge hn))]
    simp
private theorem reverse_chart {R : Type*} [CommRing R] (φ : JetRing →+* R)
    (z : R) (hy : φ ordinate * z = 1) (f : Equation) {e : ℕ}
    (hf : f.natDegree ≤ e) (he : 2 ≤ e) (hroot : φ (C f) = 0) :
    inverseEval φ z (C (f.reflect e)) = 0 ∧
      inverseEval φ z (jetSeparant (f.reflect e)) = -(z^(e-2) * φ (jetSeparant f)) := by
  let y := φ ordinate
  let i := seedMap φ
  let E := eval₂RingHom i z
  have hzy : z*y = 1 := (mul_comm _ _).trans hy
  let : Invertible y := ⟨z, hzy, hy⟩
  have href (p : Equation) (hp : p.natDegree ≤ e) : E (p.reflect e) = z^e * φ (C p) := by
    have h := Polynomial.eval₂_reflect_mul_pow i y e p hp
    rw [eval_coefficient]
    change E (p.reflect e) * y^e = p.eval₂ i y at h
    rw [← h, ← mul_assoc, mul_comm (z^e) (E _), mul_assoc, ← mul_pow, hzy, one_pow, mul_one]
  have hE (q : Equation) : inverseEval φ z (C q) = E q := by
    simp [inverseEval, Polynomial.coe_eval₂RingHom, E, i]
  have hF : E (f.reflect e) = 0 := by rw [href f hf, hroot, mul_zero]
  refine ⟨(hE _).trans hF, ?_⟩
  have hD : (Polynomial.X*f.derivative).natDegree ≤ e := by
    have hm := Polynomial.natDegree_mul_le (p := (Polynomial.X : Equation)) (q := f.derivative)
    rw [Polynomial.natDegree_X] at hm
    have hd := Polynomial.natDegree_derivative_le f
    omega
  have h := congrArg (fun q => E q) (reverse_euler f e hf)
  simp only [map_add, map_mul, hF, mul_zero] at h
  rw [href _ hD, map_mul, map_mul] at h
  rw [show jetSeparant (f.reflect e) = C (f.reflect e).derivative from rfl, hE]
  have hX : E Polynomial.X = z := Polynomial.eval₂_X _ _
  have hpow : z^e * y = z * z^(e-2) := by
    calc
      z^e * y = z^(e-2+1) * (z*y) := by
        rw [← mul_assoc, ← pow_succ, show e-2+1+1 = e by omega]
      _ = z * z^(e-2) := by rw [hzy, mul_one, pow_succ']
  change E (f.reflect e).derivative = -(z^(e-2) * φ (C f.derivative))
  apply cancel_unit (IsUnit.of_mul_eq_one y hzy)
  rw [hX, ← mul_assoc] at h
  change (z^e * y) * φ (C f.derivative) + z * E (f.reflect e).derivative = 0 at h
  rw [hpow] at h
  linear_combination h
private theorem transport {R : Type*} [CommRing R] (φ : JetRing →+* R)
    (z : R) (hy : φ ordinate * z = 1) (f : Equation) {e : ℕ} (hf : f.natDegree ≤ e)
    (he : 2 ≤ e) (hroot : φ (C f) = 0) (hc : IsUnit (φ (jetSeparant f)))
    (δ : ChartDerivation R) (h : ChartFlow f φ δ) :
    ChartFlow (f.reflect e) (inverseEval φ z) δ ∧
      inverseEval φ z (jetSeparant (f.reflect e)) = -(z^(e-2) * φ (jetSeparant f)) := by
  let ψ := inverseEval φ z
  let F := f.reflect e
  let E := ψ.comp (C : Equation →+* JetRing)
  obtain ⟨hF, hsep⟩ := reverse_chart φ z hy f hf he hroot
  have hseed (s : Seeds) : E (C s) = φ (C (C s)) := by
    simp [E, ψ, inverseEval, seedMap, Polynomial.coe_eval₂RingHom]
  have hs (s : Seeds) : δ (E (C s)) = E (C (P1_7_8_4.coeffDx s)) := by
    rw [hseed, hseed]
    apply cancel_unit hc
    have ha := h.action (C (C s))
    change φ (jetSeparant f) * δ (φ (C (C s))) = φ (flow f (C (C s))) at ha
    rw [ha, flow_C, coeffDiff_C]
    simp
  have hz : E Polynomial.X = z := by simp [E, ψ, inverseEval, Polynomial.coe_eval₂RingHom]
  have hw : ψ velocity = -(φ velocity*z^2) := by
    simp [ψ, inverseEval, velocity, Polynomial.coe_eval₂RingHom]
  have hδz : δ (E Polynomial.X) = ψ velocity := by
    rw [hz, hw]
    exact ordinate_deriv δ hy h.root
  have hC (q : Equation) :
      δ (E q) = E (coefficientDerivative q) + ψ velocity * E q.derivative := by
    rw [root_chain δ E hs, hδz]
  have hT : E (coefficientDerivative F) + ψ velocity * E F.derivative = 0 := by
    have ht := congrArg (fun t => δ t) hF
    change δ (E F) = δ 0 at ht
    rw [hC, map_zero] at ht
    exact ht
  have hV : ψ (jetSeparant F) * δ (ψ velocity) = -ψ (secondAlongVelocity F) := by
    have ht := congrArg (fun t => δ t) hT
    rw [map_zero, map_add, deriv_mul, hC (coefficientDerivative F), hC F.derivative,
      ← coeffDiff_derivative] at ht
    change E F.derivative * δ (ψ velocity) = _
    simp only [secondAlongVelocity, map_add, map_mul, map_ofNat, map_pow]
    change E F.derivative * δ (ψ velocity) =
      -(E (coefficientDerivative (coefficientDerivative F)) +
        2 * ψ velocity * E (coefficientDerivative F.derivative) +
        (ψ velocity)^2 * E F.derivative.derivative)
    linear_combination ht
  have hsepFlow : δ (ψ (jetSeparant F)) = ψ (sepAlong F) := by
    rw [sepAlong, map_add, map_mul]
    change δ (E F.derivative) =
      E (coefficientDerivative F.derivative) + ψ velocity * E F.derivative.derivative
    exact hC F.derivative
  exact ⟨⟨hδz, hsepFlow, jet_chain δ ψ F hC hV⟩, hsep⟩
private theorem inverse_flow : P1_7_8_3_1_2.c2 := by
  intro J B D δ h
  exact transport (finite J B D) (reciprocal J B D) (mul_reciprocal J B D)
    J.f le_rfl (Nat.le_of_succ_le J.sheets) (finite_root J B D) (separant_unit J B D) δ h
theorem proof : HighFamily82190_5.c1 :=
  P1_7_8_3_1_2.of_children finite_flow inverse_flow
end
end HighFamily82190_5_1
end
section
set_option autoImplicit false
namespace HighFamily82190_5_2
def c1 : Prop := P1_7_8_3_2_4.c1
def c2 : Prop := P1_7_8_3_2_4.c2
theorem of_children (h1 : c1) (h2 : c2) : HighFamily82190_5.c2 :=
  P1_7_8_3_2_4.of_children h1 h2
end HighFamily82190_5_2
end
section
set_option autoImplicit false
namespace HighFamily82190_5_2_1
noncomputable section
open K1_14 (FX)
open P1_7_8_3 P1_7_8_3_2_4 MvPolynomial
open scoped BigOperators MonomialOrder
private def finiteDegLex (α : Type) [Fintype α] : MonomialOrder α := by
  classical
  let _ : LinearOrder α := LinearOrder.lift' _ (Fintype.equivFin α).injective
  have : WellFoundedGT α := Finite.to_wellFoundedGT
  exact MonomialOrder.degLex
private def termOrder : MonomialOrder CoxVar := finiteDegLex CoxVar
private def leading (L : Layer) (d : Degree) : Set Exponent :=
  {m | ∃ p : Cox, p ∈ L d ∧ p ≠ 0 ∧ termOrder.degree p = m}
private def initial (L : Layer) : Set Exponent :=
  {m | m ∈ leading L (Finsupp.weight coxWeight m)}
private theorem leading_weight {L : Layer} {d : Degree} (hL : Stable L)
    {m : Exponent} (hm : m ∈ leading L d) : Finsupp.weight coxWeight m = d := by
  obtain ⟨p, hp, hp0, rfl⟩ := hm
  have hp' : p.IsWeightedHomogeneous coxWeight d := hL.1 d hp
  exact hp' (MonomialOrder.coeff_degree_ne_zero_iff.mpr hp0)
private theorem initial_upper {L : Layer} (hL : Stable L) : IsUpperSet (initial L) := by
  classical
  intro m n hmn hm
  obtain ⟨p, hp, hp0, hd⟩ := hm
  let q : Cox := monomial (n - m) 1
  have hq : q ∈ homogeneous (Finsupp.weight coxWeight (n - m)) :=
    isWeightedHomogeneous_monomial _ _ _ rfl
  have hq0 : q ≠ 0 := by simp [q]
  have he : Finsupp.weight coxWeight (n - m) + Finsupp.weight coxWeight m =
      Finsupp.weight coxWeight n := by
    rw [← map_add, tsub_add_cancel_of_le hmn]
  refine ⟨q * p, ?_, mul_ne_zero hq0 hp0, ?_⟩
  · rw [← he]
    exact hL.2 _ _ hq hp
  · rw [termOrder.degree_mul hq0 hp0, hd]
    simp only [q, termOrder.degree_monomial, one_ne_zero, ite_false, tsub_add_cancel_of_le hmn]
private theorem leading_finite {L : Layer} (hL : Stable L) (d : Degree) :
    (leading L d).Finite :=
  (finite_weight d).subset fun _ hm => leading_weight hL hm
private theorem mem_leading_iff {L : Layer} (hL : Stable L) {d : Degree} {m : Exponent} :
    m ∈ leading L d ↔ m ∈ initial L ∧ Finsupp.weight coxWeight m = d := by
  constructor
  · intro hm
    have hw := leading_weight hL hm
    exact ⟨show m ∈ leading L (Finsupp.weight coxWeight m) from hw.symm ▸ hm, hw⟩
  · rintro ⟨hm, hw⟩
    exact hw ▸ (show m ∈ leading L (Finsupp.weight coxWeight m) from hm)
private theorem independent_of_leading {σ K ι : Type} [Field K] [Fintype ι]
    (m : MonomialOrder σ) (p : ι → MvPolynomial σ K) (hp : ∀ i, p i ≠ 0)
    (hd : Function.Injective fun i => m.degree (p i)) : LinearIndependent K p := by
  classical
  refine (Fintype.linearIndependent_iff (v := p)).mpr ?_
  intro w hw j
  by_contra hj
  let active : Finset ι := Finset.univ.filter fun i => w i ≠ 0
  obtain ⟨i, hi, hmax⟩ := active.exists_max_image (fun a => m.toSyn (m.degree (p a)))
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  have hwi := (Finset.mem_filter.mp hi).2
  let e := m.degree (p i)
  have hz := congrArg (lcoeff K e) hw
  simp only [map_sum, map_smul, map_zero] at hz
  change ∑ a : ι, w a * (p a).coeff e = 0 at hz
  rw [Finset.sum_eq_single i] at hz
  · exact (mul_ne_zero hwi (MonomialOrder.coeff_degree_ne_zero_iff.mpr (hp i))) hz
  · intro a _ hai
    by_cases ha : w a = 0
    · rw [ha, zero_mul]
    · have hle := hmax a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
      have hlt := lt_of_le_of_ne hle (fun he => hai (hd (m.toSyn.injective he)))
      rw [m.coeff_eq_zero_of_lt hlt, mul_zero]
  · simp
private theorem rank_leading {L : Layer} (hL : Stable L) (d : Degree) :
    Module.finrank FX (L d) = (leading L d).ncard := by
  classical
  let : Fintype (leading L d) := (leading_finite hL d).fintype
  let coeffs : L d →ₗ[FX] (leading L d → FX) :=
    LinearMap.pi fun i => (lcoeff FX i.val).comp (L d).subtype
  have hinj : Function.Injective coeffs := by
    intro u v huv
    apply sub_eq_zero.mp
    let p := u - v
    change p = 0
    have hz : coeffs p = 0 := (coeffs.map_sub u v).trans (sub_eq_zero.mpr huv)
    apply Subtype.ext
    by_contra hp
    have hp0 : (p : Cox) ≠ 0 := hp
    let i : leading L d := ⟨termOrder.degree (p : Cox), p, p.property, hp0, rfl⟩
    have hc : (p : Cox).coeff (termOrder.degree (p : Cox)) = 0 :=
      congrFun hz i
    exact (MonomialOrder.coeff_degree_ne_zero_iff.mpr hp0) hc
  have : Module.Finite FX (L d) := Module.Finite.of_injective coeffs hinj
  choose p hp hp0 hd using (fun i : leading L d => i.property)
  let v : leading L d → L d := fun i => ⟨p i, hp i⟩
  have he : Function.Injective (fun i => termOrder.degree (p i)) := by
    intro i j hij
    exact Subtype.ext ((hd i).symm.trans (hij.trans (hd j)))
  have hind : LinearIndependent FX v := by
    exact LinearIndependent.of_comp (v := v) (L d).subtype
      (independent_of_leading termOrder p hp0 he)
  rw [← Set.fintypeCard_eq_ncard]
  refine le_antisymm ?_ hind.fintype_card_le_finrank
  rw [← Module.finrank_pi FX]
  exact LinearMap.finrank_le_finrank_of_injective (f := coeffs) hinj
theorem proof : HighFamily82190_5_2.c1 := by
  change P1_7_8_3_2_4.c1
  intro A B hA hB hab
  have hsub (d : Degree) : leading A d ⊆ leading B d := by
    rintro m ⟨p, hp, hp0, hd⟩
    exact ⟨p, hab d hp, hp0, hd⟩
  refine ⟨initial A, initial B, initial_upper hA, initial_upper hB,
    fun m hm => hsub (Finsupp.weight coxWeight m) hm, fun d => ?_⟩
  have he : {m | m ∈ initial B \ initial A ∧ Finsupp.weight coxWeight m = d} =
      leading B d \ leading A d := by
    ext m
    change (m ∈ initial B ∧ m ∉ initial A) ∧ Finsupp.weight coxWeight m = d ↔
      m ∈ leading B d ∧ m ∉ leading A d
    rw [mem_leading_iff hA, mem_leading_iff hB]
    tauto
  rw [rank_leading hA, rank_leading hB, exponentCount, he, add_comm]
  exact Set.ncard_sdiff_add_ncard_of_subset (hsub d) (leading_finite hB d)
end
end HighFamily82190_5_2_1
end
section
set_option autoImplicit false
namespace HighFamily82190_5_2_2
noncomputable section
open P1_7_8_3 P1_7_8_3_2_4
def rootFree (B : Block) : Finset (Fin 2) :=
  Finset.univ.filter fun i => Sum.inl i ∈ B.free
def seedFree (B : Block) : Finset (Fin 3) :=
  Finset.univ.filter fun i => tᵢ i ∈ B.free
def rv {R : Type} [Semiring R] (r : ℕ) (a b : Prop) [Decidable a] [Decidable b]
    (T H HT HT₂ : R) : R :=
  if r = 0 then 0
  else if a then
    if b then T * (if r = 1 then 1 else HT)
    else if r = 1 then 1 else HT₂
  else if b then if r = 1 then 1 else H
  else 0
def seeds {R : Type} [Semiring R] (r : ℕ) (S S₂ Q : R) : R :=
  if r = 1 then 1 else if r = 2 then S else if r = 3 then Q * S * S₂ else 0
private def velocities (B : Block) (b : ℕ) : Finset ℕ :=
  if v₀ ∈ B.free then (if v₁ ∈ B.free then Finset.range (b+1) else {b})
  else if v₁ ∈ B.free then {0} else ∅
private theorem mem_velocities (B : Block) {b j : ℕ} (hb : 0 < b) :
    j ∈ velocities B b ↔ j ≤ b ∧ (v₀ ∉ B.free → j = 0) ∧
      (v₁ ∉ B.free → b-j = 0) := by
  by_cases h₀' : v₀ ∈ B.free <;> by_cases h₁' : v₁ ∈ B.free <;>
    simp [velocities, h₀', h₁'] <;> omega
private theorem mem_comp {n d : ℕ} {F : Finset (Fin n)} {f : Fin n →₀ ℕ} :
    f ∈ F.finsuppAntidiag d ↔ (∑ i, f i) = d ∧ ∀ i ∉ F, f i = 0 := by
  rw [Finset.mem_finsuppAntidiag', Finsupp.sum_fintype _ _ (fun _ => rfl)]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · exact fun h i hi => Finsupp.notMem_support_iff.mp (fun hm => hi (h hm))
  · intro h i hi
    by_contra hf
    exact (Finsupp.mem_support_iff.mp hi) (h i hf)
private def project {n : ℕ} (m : Exponent) (f : Fin n → CoxVar) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m (f i))
private def pack (r : Fin 2 →₀ ℕ) (j b : ℕ) (z : Fin 3 →₀ ℕ) : Exponent :=
  Finsupp.equivFunOnFinite.symm (Sum.elim r (Sum.elim ![j,b-j] z))
private abbrev Increments (B : Block) (d : Degree) :=
  {m : Exponent // (∀ i ∉ B.free, m i = 0) ∧ Finsupp.weight coxWeight m = d}
private def enum (B : Block) (a b c : ℕ) (hb : 0 < b) :
    Increments B (nefDegree a b c) ≃
      (Σ j : velocities B b, (rootFree B).finsuppAntidiag (a+2*j.val)) ×
        (seedFree B).finsuppAntidiag c where
  toFun m := by
    have hz := m.prop.1
    have hw := m.prop.2
    rw [weight_coordinates] at hw
    have ha := congrArg Prod.fst hw
    have hv := congrArg (fun d : Degree => d.2.1) hw
    have hc := congrArg (fun d : Degree => d.2.2) hw
    change m.val h₀ + m.val h₁ + 2*m.val v₁ = a+2*b at ha
    change m.val v₀ + m.val v₁ = b at hv
    change m.val (tᵢ 0) + m.val (tᵢ 1) + m.val (tᵢ 2) = c at hc
    refine ⟨⟨⟨m.val v₀, (mem_velocities B hb).mpr ⟨by omega, hz _, ?_⟩⟩,
      ⟨project m.val Sum.inl, mem_comp.mpr ⟨?_, ?_⟩⟩⟩,
      ⟨project m.val tᵢ, mem_comp.mpr ⟨?_, ?_⟩⟩⟩
    · intro h
      have := hz v₁ h
      omega
    · rw [Fin.sum_univ_two]
      change m.val h₀ + m.val h₁ = a+2*m.val v₀
      omega
    · exact fun i hi => hz (Sum.inl i) (by simpa [rootFree] using hi)
    · rw [Fin.sum_univ_three]
      exact hc
    · exact fun i hi => hz (tᵢ i) (by simpa [seedFree] using hi)
  invFun p := by
    rcases p with ⟨⟨j, r⟩, z⟩
    have hj := ((mem_velocities B hb).mp j.prop).1
    have hj₀ := ((mem_velocities B hb).mp j.prop).2.1
    have hj₁ := ((mem_velocities B hb).mp j.prop).2.2
    have hr := (mem_comp.mp r.prop).1
    have hrz := (mem_comp.mp r.prop).2
    have hs := (mem_comp.mp z.prop).1
    have hsz := (mem_comp.mp z.prop).2
    rw [Fin.sum_univ_two] at hr
    rw [Fin.sum_univ_three] at hs
    refine ⟨pack r.val j.val b z.val, ?_, ?_⟩
    · intro i hi
      rcases i with i | (i | i)
      · exact hrz i (by simpa [rootFree] using hi)
      · fin_cases i
        · exact hj₀ hi
        · exact hj₁ hi
      · apply hsz i
        intro hz
        unfold seedFree at hz
        exact hi (Finset.mem_filter.mp hz).2
    · rw [weight_coordinates]
      change (r.val 0 + r.val 1 + 2*(b-j.val), j.val+(b-j.val),
        z.val 0+z.val 1+z.val 2) = (a+2*b,b,c)
      rw [hr, hs]
      congr 1
      · omega
      · congr 1
        omega
  left_inv m := by
    have hw := m.prop.2
    rw [weight_coordinates] at hw
    have hv := congrArg (fun d : Degree => d.2.1) hw
    change m.val v₀ + m.val v₁ = b at hv
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    rcases i with i | (i | i)
    · rfl
    · fin_cases i
      · rfl
      · change b-m.val v₀ = m.val v₁
        omega
    · rfl
  right_inv p := by
    rcases p with ⟨⟨j,r⟩,z⟩
    apply Prod.ext
    · exact Sigma.ext (Subtype.ext rfl) (heq_of_eq (Subtype.ext (Finsupp.ext fun _ => rfl)))
    · exact Subtype.ext (Finsupp.ext fun _ => rfl)
private def shift (B : Block) (d e : Degree) (hw : Finsupp.weight coxWeight B.base + d = e) :
    Increments B d ≃ {m : Exponent // m ∈ B.exponents ∧ Finsupp.weight coxWeight m = e} :=
  Equiv.ofBijective (fun m => ⟨B.base + m.val, ⟨m.val, m.prop.1, rfl⟩, by
    rw [map_add, m.prop.2, hw]⟩) (by
      constructor
      · intro m n h
        exact Subtype.ext (add_left_cancel (congrArg Subtype.val h))
      · rintro ⟨_, ⟨m, hm, rfl⟩, h⟩
        rw [map_add, ← hw] at h
        exact ⟨⟨m, hm, add_left_cancel h⟩, rfl⟩)
private theorem comp_card {ι : Type} [DecidableEq ι] (F : Finset ι)
    {n : ℕ} (hn : 0 < n) (hF : F.card ≤ 3) :
    (F.finsuppAntidiag n).card =
      if F.card = 0 then 0 else if F.card = 1 then 1
      else if F.card = 2 then n+1 else (n+2).choose 2 := by
  rw [Finset.card_finsuppAntidiag_nat_eq_choose]
  interval_cases h : F.card
  · simp [Nat.choose_eq_zero_of_lt (show n-1 < n by omega)]
  · simp [show 1+n-1 = n by omega]
  · rw [show 2+n-1 = n+1 by omega, Nat.choose_symm_of_eq_add (a := n) (b := 1) rfl]
    simp
  · rw [show 3+n-1 = n+2 by omega, Nat.choose_symm_of_eq_add (a := n) (b := 2) rfl]
    simp
private theorem sum_widths (a b : ℕ) :
    (∑ j ∈ Finset.range (b+1), (a+2*j+1)) = (b+1)*(a+b+1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih]
    ring
private theorem root_velocity_card (B : Block) {a b : ℕ} (ha : 0 < a) :
    (∑ j ∈ velocities B b, ((rootFree B).finsuppAntidiag (a+2*j)).card) =
      rv (rootFree B).card (v₀ ∈ B.free) (v₁ ∈ B.free)
        (b+1) (a+1) (a+b+1) (a+2*b+1) := by
  have hR : (rootFree B).card ≤ 2 := (Finset.card_le_univ _).trans (by simp)
  have hc (j : ℕ) := comp_card (rootFree B) (n := a+2*j) (by omega) (hR.trans (by decide))
  simp_rw [hc]
  interval_cases h : (rootFree B).card <;>
    by_cases h₀' : v₀ ∈ B.free <;> by_cases h₁' : v₁ ∈ B.free <;>
    simp [rv, velocities, h₀', h₁', sum_widths]
theorem fibre_card (B : Block) {a b c : ℕ} {e : Degree}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hw : Finsupp.weight coxWeight B.base + nefDegree a b c = e) :
    exponentCount B.exponents e =
      rv (rootFree B).card (v₀ ∈ B.free) (v₁ ∈ B.free)
        (b+1) (a+1) (a+b+1) (a+2*b+1) *
      (if (seedFree B).card = 0 then 0 else if (seedFree B).card = 1 then 1
        else if (seedFree B).card = 2 then c+1 else (c+2).choose 2) := by
  classical
  change Nat.card {m : Exponent // m ∈ B.exponents ∧ Finsupp.weight coxWeight m = e} = _
  rw [Nat.card_congr ((shift B _ _ hw).symm.trans (enum B a b c hb)),
    Nat.card_prod, Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  change (∑ j ∈ (velocities B b).attach, ((rootFree B).finsuppAntidiag (a+2*j.val)).card) * _ = _
  have hS : (seedFree B).card ≤ 3 := (Finset.card_le_univ _).trans (by simp)
  rw [Finset.sum_attach (velocities B b) (fun j : ℕ => ((rootFree B).finsuppAntidiag (a+2*j)).card),
    root_velocity_card B ha, comp_card (seedFree B) hc hS]
end
end HighFamily82190_5_2_2
end
section
set_option autoImplicit false
namespace HighFamily82190_5_2_2
noncomputable section
open P1_7_8_3 P1_7_8_3_2 P1_7_8_3_2_4 MvPolynomial
private abbrev Exp := Fin 3 →₀ ℕ
private theorem coeff_add_apply (p q : HilbertPoly) (m : Exp) :
    (p+q).coeff m = p.coeff m + q.coeff m := by simp
private theorem coeff_nonneg {p : HilbertPoly} (hp : NonnegativeTop p)
    {m : Exp} (hm : p.totalDegree ≤ m.degree) : 0 ≤ p.coeff m := by
  rcases lt_or_eq_of_le hm with h | h
  · rw [coeff_eq_zero_of_totalDegree_lt h]
  · exact hp m h.symm
private theorem top_add_right {p q : HilbertPoly} (hp : NonnegativeTop p)
    (hq : NonnegativeTop q) (hq' : q ≠ 0) (h : p.totalDegree ≤ q.totalDegree) :
    NonnegativeTop (p+q) := by
  obtain ⟨m, hm, hd⟩ := Finset.exists_mem_eq_sup q.support (support_nonempty.mpr hq')
    (fun m => m.degree)
  change q.totalDegree = m.degree at hd
  have hpos : 0 < q.coeff m :=
    lt_of_le_of_ne (hq m hd.symm) (ne_comm.mp (MvPolynomial.mem_support_iff.mp hm))
  have hm' : m ∈ (p+q).support := by
    rw [MvPolynomial.mem_support_iff, coeff_add_apply]
    exact (add_pos_of_nonneg_of_pos (coeff_nonneg hp (h.trans_eq hd)) hpos).ne'
  have hd' : (p+q).totalDegree = q.totalDegree :=
    le_antisymm ((totalDegree_add _ _).trans (max_eq_right h).le)
      (hd.trans_le (le_totalDegree hm'))
  intro n hn
  change n.degree = (p+q).totalDegree at hn
  rw [coeff_add_apply]
  exact add_nonneg (coeff_nonneg hp (h.trans_eq (hn.trans hd').symm)) (hq n (hn.trans hd'))
private theorem top_add {p q : HilbertPoly} (hp : NonnegativeTop p)
    (hq : NonnegativeTop q) : NonnegativeTop (p+q) := by
  by_cases hp' : p = 0
  · simpa [hp'] using hq
  by_cases hq' : q = 0
  · simpa [hq'] using hp
  rcases le_total p.totalDegree q.totalDegree with h | h
  · exact top_add_right hp hq hq' h
  · rw [add_comm]
    exact top_add_right hq hp hp' h
private theorem top_zero : NonnegativeTop (0 : HilbertPoly) := by
  intro m _
  simp
private theorem top_mul {p q : HilbertPoly} (hp : NonnegativeTop p)
    (hq : NonnegativeTop q) : NonnegativeTop (p*q) := by
  classical
  by_cases hp' : p = 0
  · simpa [hp'] using top_zero
  by_cases hq' : q = 0
  · simpa [hq'] using top_zero
  intro m hm
  change m.degree = (p*q).totalDegree at hm
  rw [totalDegree_mul_of_isDomain hp' hq'] at hm
  rw [coeff_mul]
  apply Finset.sum_nonneg
  rintro ⟨a,b⟩ hab
  have he : a+b = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have hd : a.degree+b.degree = m.degree := by rw [← map_add, he]
  by_cases ha : p.totalDegree < a.degree
  · simp [coeff_eq_zero_of_totalDegree_lt ha]
  by_cases hb : q.totalDegree < b.degree
  · simp [coeff_eq_zero_of_totalDegree_lt hb]
  exact mul_nonneg (hp a (by change a.degree = p.totalDegree; omega))
    (hq b (by change b.degree = q.totalDegree; omega))
private theorem top_C (r : ℚ) (hr : 0 ≤ r) : NonnegativeTop (C r : HilbertPoly) := by
  intro m _
  rw [coeff_C]
  split_ifs
  · exact hr
  · exact le_rfl
private theorem top_one : NonnegativeTop (1 : HilbertPoly) := by
  simpa only [map_one] using top_C 1 zero_le_one
private def affine (i j : Fin 3) (r b : ℚ) : HilbertPoly :=
  MvPolynomial.X i + C r * MvPolynomial.X j + C b
private theorem top_affine (i j : Fin 3) {r : ℚ} (hr : 0 ≤ r) (b : ℚ) :
    NonnegativeTop (affine i j r b) := by
  classical
  have hX (k : Fin 3) (m : Exp) : 0 ≤ (MvPolynomial.X k : HilbertPoly).coeff m := by
    rw [coeff_X]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  let p : HilbertPoly := MvPolynomial.X i + C r * MvPolynomial.X j
  have hp (m : Exp) : 0 ≤ p.coeff m := by
    change 0 ≤ (MvPolynomial.X i + C r * MvPolynomial.X j : HilbertPoly).coeff m
    rw [coeff_add_apply, coeff_C_mul]
    exact add_nonneg (hX i m) (mul_nonneg hr (hX j m))
  have hm : Finsupp.single i 1 ∈ p.support := by
    rw [MvPolynomial.mem_support_iff]
    change (MvPolynomial.X i + C r * MvPolynomial.X j : HilbertPoly).coeff (Finsupp.single i 1) ≠ 0
    rw [coeff_add_apply, coeff_C_mul, show (MvPolynomial.X i : HilbertPoly).coeff (Finsupp.single i 1) = 1 by
      simp [coeff_X]]
    exact (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr (hX j _))).ne'
  have hd := le_totalDegree hm
  change (Finsupp.single i 1).degree ≤ p.totalDegree at hd
  rw [Finsupp.degree_single] at hd
  intro m hm
  change m.degree = (p + C b).totalDegree at hm
  have hd' : (C b : HilbertPoly).totalDegree < p.totalDegree := by
    rw [totalDegree_C]
    omega
  rw [totalDegree_add_eq_left_of_totalDegree_lt hd'] at hm
  change 0 ≤ (p + C b).coeff m
  have hm' : (C b : HilbertPoly).totalDegree < m.degree := by rwa [hm]
  rw [coeff_add_apply, coeff_eq_zero_of_totalDegree_lt hm', add_zero]
  exact hp m
private def baseDegree (B : Block) : Degree := Finsupp.weight coxWeight B.base
private def profile (B : Block) : HilbertPoly :=
  let (u,v,w) := baseDegree B
  rv (rootFree B).card (v₀ ∈ B.free) (v₁ ∈ B.free)
    (affine 1 1 0 (1-v)) (affine 0 0 0 (1+2*v-u))
    (affine 0 1 1 (1+v-u)) (affine 0 1 2 (1-u)) *
  seeds (seedFree B).card
    (affine 2 2 0 (1-w)) (affine 2 2 0 (2-w)) (C (1/2))
private theorem profile_top (B : Block) : NonnegativeTop (profile B) := by
  change NonnegativeTop (rv _ _ _ _ _ _ _ * seeds _ _ _ _)
  apply top_mul
  · unfold rv
    split_ifs <;> first
      | exact top_zero
      | exact top_one
      | exact top_affine _ _ (by norm_num) _
      | exact top_mul (top_affine _ _ (by norm_num) _) top_one
      | exact top_mul (top_affine _ _ (by norm_num) _) (top_affine _ _ (by norm_num) _)
  · unfold seeds
    split_ifs <;> first
      | exact top_zero
      | exact top_one
      | exact top_affine _ _ (by norm_num) _
      | exact top_mul (top_mul (top_C _ (by norm_num)) (top_affine _ _ (by norm_num) _))
          (top_affine _ _ (by norm_num) _)
private def threshold (B : Block) : ℕ :=
  let (u,v,w) := baseDegree B
  u+v+w+1
private theorem profile_eval (B : Block) (h t s : ℕ)
    (hh : threshold B ≤ h) (ht : threshold B ≤ t) (hs : threshold B ≤ s) :
    (exponentCount B.exponents (nefDegree h t s) : ℚ) = evalHilbert (profile B) h t s := by
  rcases hbase : baseDegree B with ⟨u,v,w⟩
  have hw : Finsupp.weight coxWeight B.base = (u,v,w) := hbase
  simp only [threshold, hbase] at hh ht hs
  let a := h+2*v-u
  let b := t-v
  let c := s-w
  have ha : 0 < a := by dsimp [a]; omega
  have hb : 0 < b := by dsimp [b]; omega
  have hc : 0 < c := by dsimp [c]; omega
  have hweight : Finsupp.weight coxWeight B.base + nefDegree a b c = nefDegree h t s := by
    rw [hw]
    change (u+(a+2*b), v+b, w+c) = (h+2*t,t,s)
    dsimp [a,b,c]
    congr 1
    · omega
    · congr 1 <;> omega
  rw [fibre_card B ha hb hc hweight, Nat.cast_mul]
  let E := MvPolynomial.eval ![(h : ℚ),(t : ℚ),(s : ℚ)]
  unfold evalHilbert profile
  rw [hbase]
  change _ = E (_ * _)
  rw [map_mul]
  congr 1
  · unfold rv
    split_ifs <;> simp [E, affine, a, b, Nat.cast_sub (show u ≤ h+2*v by omega),
      Nat.cast_sub (show v ≤ t by omega)] <;> ring
  · have hS : (seedFree B).card ≤ 3 := (Finset.card_le_univ _).trans (by simp)
    interval_cases (seedFree B).card <;>
      simp [E, seeds, affine, c, Nat.cast_choose_two,
        Nat.cast_sub (show w ≤ s by omega)] <;> ring
private theorem sum_top (blocks : Finset Block) : NonnegativeTop (∑ B ∈ blocks, profile B) := by
  classical
  induction blocks using Finset.induction_on with
  | empty => simpa using top_zero
  | insert B _ hB ih => rw [Finset.sum_insert hB]; exact top_add (profile_top B) ih
theorem proof : HighFamily82190_5_2.c2 := by
  change P1_7_8_3_2_4.c2
  intro blocks
  let N := ∑ B ∈ blocks, threshold B
  refine ⟨∑ B ∈ blocks, profile B, sum_top blocks, N, fun h t s hh ht hs => ?_⟩
  change ((∑ B ∈ blocks, exponentCount B.exponents (nefDegree h t s) : ℕ) : ℚ) =
    MvPolynomial.eval ![(h : ℚ),(t : ℚ),(s : ℚ)] (∑ B ∈ blocks, profile B)
  rw [Nat.cast_sum, map_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hN : threshold B ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hB
  exact profile_eval B h t s (hN.trans hh) (hN.trans ht) (hN.trans hs)
end
end HighFamily82190_5_2_2
end
