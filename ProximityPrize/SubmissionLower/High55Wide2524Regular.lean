import ProximityPrize.SubmissionLower.High55Wide2524Family
import ProximityPrize.SubmissionLower.HighCore82268Tangent

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High55Wide2524

def asLooseModel {u del} (M : AnchorModel u del) : FrontCore82268.AnchorModel u del :=
  { M with height_bound := M.height_bound.trans (by decide) }

def asLooseFamily {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) :
    FrontCore82268.AnchoredFamily (asLooseModel M) Γ where
  scalar := F.scalar
  distinct := F.distinct
  mark γ hγ := by
    let m := F.mark γ hγ
    let B : P1.BadMarkAt HighCore82268.agreement u γ :=
      { m.bad with agreement := (by decide : HighCore82268.agreement ≤ agreement).trans m.bad.agreement }
    exact ⟨B, m.avoids_deleted, m.scalar_fixed, m.scalar_degree, m.scalar_hits, m.pole_unit, m.identity⟩

end High55Wide2524

section
set_option autoImplicit false
namespace High55Wide2524_5
noncomputable section
open High55Wide2524 (agreement blockLength)
open High55Wide2524 (degreeAt quotientOrder gap scale muNum lambdaNum properFee)
open P1_7_8 (mu_cross lambda_cross)
open HighCore82268Tangent (Input cutSeed cutVelocity cutOrdinate ratio_le_ceil)
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
end High55Wide2524_5
end
section
namespace High55Wide2524_5
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open High55Wide2524 (K I node agreement)
open High55Wide2524 (FixedWord)
open private occupancy from ProximityPrize.SubmissionLower.Fast055
open private incidence_arithmetic from ProximityPrize.SubmissionLower.PortHighBase
theorem section_capacity {w T s d} (h : FixedWord w T s d) (hd : d < agreement) (cap : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ T, (s γ).eval (node i) ≠ w i) →
      (T.filter fun γ => (s γ).eval (node i) = w i).card ≤ cap) :
    (agreement - d) * T.card ≤ High55Wide2524.t * cap + (agreement - d) := by
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
  have hnodes : nodes.card = x + High55Wide2524.t := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    change 262144 - common.card = (179876 - common.card) + 82268
    have hbound : common.card ≤ 179876 := hcommon.trans hd.le
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
  exact incidence_arithmetic High55Wide2524.t _ _ _ _ (by omega) (by omega) hx (by decide) second first
end
end High55Wide2524_5
end
section
set_option autoImplicit false
namespace High55Wide2524_5
noncomputable section
open Polynomial Finset
open High55Wide2524 (K I agreement blockLength node p)
open High55Wide2524 (FixedWord degreeAt gap scale muNum properFee flatFee)
open K1_14 (Equation graphEval)
open K1_14_4 (seedDegree)
open HighCore82268Tangent (Input ResidueLift Factors ProperCurve ProperCover FlatSections
  card_le_cover componentMarks mem_componentMarks root_component
  ratio_le_ceil)
open private persistent_le_degree from ProximityPrize.SubmissionLower.HighCore82268TangentDeps
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
    gap J.hi * (componentMarks J q).card ≤ High55Wide2524.t * ((p+1)*seedDegree q) + gap J.hi := by
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
  have hsum : g*n ≤ High55Wide2524.t*(p+1)*J.v + g*D.count := by
    calc
      _ = ∑ j, g*(U j).card := mul_sum ..
      _ ≤ ∑ j, (High55Wide2524.t*((p+1)*seedDegree (D.flat j)) + g) := by
        refine sum_le_sum fun j _ => ?_
        have hu : seedDegree (D.flat j) ≤ ∑ i, seedDegree (D.flat i) :=
          single_le_sum (f := fun i => seedDegree (D.flat i)) (fun _ _ => Nat.zero_le _) (mem_univ j)
        exact flat_component_count J hd hword (D.flat j) (hu.trans_lt (D.seed_sum.trans_lt hv)) (hsections j)
      _ = High55Wide2524.t*(p+1)*(∑ j, seedDegree (D.flat j)) + g*D.count := by
        rw [sum_add_distrib, sum_const, smul_eq_mul, card_univ, Fintype.card_fin,
          ← mul_sum, ← mul_sum, mul_assoc, Nat.mul_comm D.count]
      _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left _ D.seed_sum) _
  have hrem : g*(n-D.count) ≤ High55Wide2524.t*(p+1)*J.v := by
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
    J.marks.card ≤ High55Wide2524.tangentFee J.lo J.hi J.e J.v := by
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
  unfold High55Wide2524.tangentFee
  omega
end
end High55Wide2524_5
end
section
set_option autoImplicit false
namespace High55Wide2524_5
open High55Wide2524 (p agreement start finish)
open High55Wide2524 (degreeAt quotientOrder window_nat terminal_guards grade_checked
  asLooseModel asLooseFamily FixedWord)
open HighCore82268Tangent (Input)
def c1 : Prop := HighCore82268Tangent_3_1.c2
def c2 : Prop := HighCore82268Tangent_3_2.c4
theorem of_children (inverse : c1) (profiles : c2) : High55Wide2524.c5 := by
  intro b u del M Γ F hw hshift H hH i f hred he hlarge hpos hseed T hT hreg
  obtain ⟨hl, hu⟩ := window_nat hw
  obtain ⟨hlo, hhi, -, -, -⟩ := terminal_guards b
  have h : 0 < M.overhead.toNat := hlo.trans_le hl
  have hell : 0 < quotientOrder M.overhead.toNat := by
    change 0 < 131071 - M.overhead.toNat
    omega
  have hd : degreeAt (finish b) ≤ 164534 := Nat.add_le_add_left hhi 131071
  have hgap₁ : degreeAt (finish b) < HighCore82268.agreement := hd.trans_lt (by decide)
  have hgap₃ : degreeAt (finish b) < agreement := hd.trans_lt (by decide)
  have hfac : degreeAt (finish b) + 1 < p :=
    (Nat.succ_le_of_lt hgap₁).trans_lt (by decide)
  have hc := grade_checked b i
  rw [← he] at hc
  let J : Input := {
    words := u, deleted := del, model := asLooseModel M, labels := Γ, family := asLooseFamily M F
    shift_out := hshift, block := H, chart := hH, marks := T, marks_sub := hT
    f := f, regular := hreg, reduced := hred, sheets := hlarge, seed_pos := hpos
    v := ((High55Wide2524.grades b).get i).seedCap, seed_bound := hseed
    lo := (start b), hi := (finish b), lower := hl, upper := hu, positive := h
    quotient_pos := hell, agreement_gap := hgap₁, factorial_guard := hfac
    separant_guard := hc.separant, flat_guard := hc.flat }
  have hweak := HighCore82268Tangent.fixed_word J (Finset.Subset.refl J.marks)
  have hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi) :=
    ⟨hweak.distinct, hweak.degree, fun γ hγ => by
      let m := F.mark γ (hT hγ)
      exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩⟩
  obtain ⟨B⟩ := HighCore82268Tangent_1.proof J
  obtain ⟨D⟩ := HighCore82268Tangent_2.proof J B
  have lift := HighCore82268Tangent_3_1.of_children HighCore82268Tangent_3_1_1.proof inverse
  have mixed := HighCore82268Tangent_3_2.of_children HighCore82268Tangent_3_2_1.proof HighCore82268Tangent_3_2_2.proof
    HighCore82268Tangent_3_2_3.proof profiles HighCore82268Tangent_3_2_5.proof HighCore82268Tangent_3_2_6.proof
  have shorten := HighCore82268Tangent_3_3.of_children HighCore82268Tangent_3_3_1.proof HighCore82268Tangent_3_3_2.proof
  obtain ⟨C⟩ := HighCore82268Tangent_3.of_children lift mixed shorten J B D
  apply count J hgap₃ hword C
  intro j
  obtain ⟨E⟩ := HighCore82268Tangent_4.of_children HighCore82268Tangent_4_1.proof HighCore82268Tangent_4_2.proof J B D j
  exact HighCore82268Tangent_5.of_children HighCore82268Tangent_5_1.proof HighCore82268Tangent_5_2.proof J B D j E
end High55Wide2524_5
end

namespace High55Wide2524

theorem tangent_count : c5 :=
  High55Wide2524_5.of_children HighCore82268_5_1.proof
    (HighCore82268_5_2.of_children HighCore82268_5_2_1.proof HighCore82268_5_2_2.proof)

#print axioms tangent_count
end High55Wide2524
