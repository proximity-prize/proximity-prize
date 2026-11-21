import ProximityPrize.SubmissionLower.HighCore82706Family
import ProximityPrize.SubmissionLower.UpperBranch8

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000


set_option Elab.async false
set_option autoImplicit true
section
namespace HighCore82706Tangent
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P1 (K I node)
open HighCore82706 (agreement)
open private occupancy from ProximityPrize.SubmissionLower.Fast055
structure FixedWord (w : I → K) (T : Finset K) (s : K → K[X]) (d : ℕ) : Prop where
  distinct : Set.InjOn s (T : Set K)
  degree : ∀ γ ∈ T, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ T, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
theorem FixedWord.mono {w T s d} (h : FixedWord w T s d) {U : Finset K} (hU : U ⊆ T) :
    FixedWord w U s d :=
  ⟨h.distinct.mono hU, fun γ hγ => h.degree γ (hU hγ), fun γ hγ => h.hits γ (hU hγ)⟩
open private incidence_arithmetic from ProximityPrize.SubmissionLower.PortHighBase
theorem section_capacity {w T s d} (h : FixedWord w T s d) (hd : d < agreement) (cap : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ T, (s γ).eval (node i) ≠ w i) →
      (T.filter fun γ => (s γ).eval (node i) = w i).card ≤ cap) :
    (agreement - d) * T.card ≤ HighCore82706.t * cap + (agreement - d) := by
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
  have hnodes : nodes.card = x + HighCore82706.t := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    change 262144 - common.card = (179438 - common.card) + 82706
    have hbound : common.card ≤ 179438 := hcommon.trans hd.le
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
  exact incidence_arithmetic HighCore82706.t _ _ _ _ (by omega) (by omega) hx (by decide) second first
end
end HighCore82706Tangent
end
section
set_option autoImplicit false
namespace HighCore82706Tangent
noncomputable section
open Polynomial Finset
open P1 (K I Words p node blockLength)
open HighCore82706 (AnchorModel AnchoredFamily agreement)
open P1_7 (Reduced regularRoot degreeAt quotientOrder singularDegree)
open FrontCore82706 (AdjacentChart)
open K1_14 (L FX Seeds Equation SeedBound liftPoly atMark seedEmbedding)
open K1_14_4 (seedDegree)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx flatten cleared separant markEval)
open scoped BigOperators
structure Input where
  words : Words
  deleted : Finset I
  model : AnchorModel words deleted
  labels : Finset K
  family : AnchoredFamily model labels
  shift_out : model.shift ∉ labels
  block : L[X]
  chart : AdjacentChart model family block
  marks : Finset K
  marks_sub : marks ⊆ labels
  f : Equation
  regular : ∀ γ ∈ marks, regularRoot f (model.label γ) (family.scalar γ)
  reduced : Reduced f
  sheets : 3 ≤ f.natDegree
  seed_pos : 0 < seedDegree f
  v : ℕ
  seed_bound : SeedBound f v
  lo : ℕ
  hi : ℕ
  lower : lo ≤ model.overhead.toNat
  upper : model.overhead.toNat ≤ hi
  positive : 0 < model.overhead.toNat
  quotient_pos : 0 < quotientOrder model.overhead.toNat
  agreement_gap : degreeAt hi < agreement
  factorial_guard : degreeAt hi + 1 < p
  separant_guard : singularDegree f.natDegree v < p
  flat_guard : f.natDegree * degreeAt hi + v < p
abbrev Input.w (J : Input) : ℕ := J.model.overhead.toNat
abbrev Input.ell (J : Input) : ℕ := quotientOrder J.w
abbrev Input.e (J : Input) : ℕ := J.f.natDegree
def Input.secondBlock (J : Input) : L[X] := J.block.map (frobenius L p)
def Input.blockProduct (J : Input) : L[X] := J.block * J.secondBlock
abbrev SeedConstants := MvPolynomial (Fin 2) L
def residueData (_J : Input) (i : Fin 2) (g : K[X]) : SeedConstants[X] :=
  ((liftPoly g).map (if i = 0 then RingHom.id L else frobenius L p)).map MvPolynomial.C
def blockAt (J : Input) (i : Fin 2) : L[X] :=
  if i = 0 then J.block else J.secondBlock
def residueDenominator (J : Input) (i : Fin 2) : SeedConstants[X] :=
  residueData J i (J.model.factor * J.model.A₀) +
    C (MvPolynomial.X i) * residueData J i (J.model.factor * J.model.A₁)
def evalSeedConstants (z : K) : SeedConstants →+* L :=
  MvPolynomial.eval ![algebraMap K L z, (algebraMap K L z)^p]
structure ResidueLift (J : Input) where
  denominator : SeedConstants
  numerator : SeedConstants[X]
  denominator_ne : denominator ≠ 0
  denominator_degree : denominator.totalDegree ≤ 2 * J.w
  numerator_degree : ∀ j, (numerator.coeff j).totalDegree ≤ 2 * J.w
  numerator_width : numerator.natDegree < 2 * J.w
  congruences : ∀ i : Fin 2, (blockAt J i).map MvPolynomial.C ∣
    residueDenominator J i * numerator +
      C (MvPolynomial.X i * denominator) * residueData J i J.model.Q
  unit_at_marks : ∀ γ ∈ J.labels, evalSeedConstants (J.model.label γ) denominator ≠ 0
def constantAbscissa : L →+* FX :=
  (algebraMap L[X] FX).comp Polynomial.C
def liftSeeds : SeedConstants →+* Seeds := MvPolynomial.map constantAbscissa
def seedBiform : SeedConstants →+* Biform :=
  (MvPolynomial.rename (R := FX) (some : Fin 2 → Option (Fin 2))).toRingHom.comp liftSeeds
def center : FX := algebraMap L[X] FX Polynomial.X
def liftTaylor (P : SeedConstants[X]) (i : ℕ) : Biform :=
  (Polynomial.taylor (MvPolynomial.C center) (P.map seedBiform)).coeff i
def inverseBlockCoeff (J : Input) (i : ℕ) : FX :=
  (i.factorial : FX)⁻¹ *
    (Dx^[i]) ((algebraMap L[X] FX J.blockProduct)⁻¹)
def ordinateTaylorNum (f : Equation) (r : ℕ) : ℕ → Biform
  | 0 => separant (flatten f) ^ (2*r-1) * MvPolynomial.X none
  | i + 1 => MvPolynomial.C (((i+1).factorial : FX)⁻¹) *
      (separant (flatten f) ^ ((2*r-1)-(2*i+1)) * cleared (flatten f) i)
def quotientNumerator (J : Input) (B : ResidueLift J) (r : ℕ) : Biform :=
  ∑ i ∈ range (r+1), MvPolynomial.C (inverseBlockCoeff J (r-i)) *
    (seedBiform B.denominator * ordinateTaylorNum J.f r i -
      separant (flatten J.f) ^ (2*r-1) * liftTaylor B.numerator i)
def quotientDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : Biform :=
  seedBiform B.denominator * separant (flatten J.f) ^ (2*r-1)
def cutoff (J : Input) (B : ResidueLift J) : Equation :=
  MvPolynomial.optionEquivLeft FX (Fin 2) (quotientNumerator J B (J.ell+1))
abbrev SeedField := FractionRing Seeds
def generic (q : Equation) : SeedField[X] := q.map (algebraMap Seeds SeedField)
def rootOn (J : Input) (q : Equation) (γ : K) : Prop :=
  atMark q (J.model.label γ) (J.family.scalar γ) = 0
structure Factors (J : Input) (B : ResidueLift J) where
  proper : Equation
  count : ℕ
  flat : Fin count → Equation
  product : J.f = proper * ∏ j, flat j
  cutoff_at_marks : ∀ γ ∈ J.marks, rootOn J (cutoff J B) γ
  proper_coprime : IsCoprime (generic proper) (generic (cutoff J B))
  flat_reduced : ∀ j, Reduced (flat j)
  flat_irred : ∀ j, Irreducible (generic (flat j))
  flat_cutoff : ∀ j, generic (flat j) ∣ generic (cutoff J B)
  sheets : count ≤ J.e
  degree_each : ∀ j, (flat j).natDegree ≤ J.e
  seed_sum : ∑ j, seedDegree (flat j) ≤ J.v
structure ProperCurve (J : Input) (B : ResidueLift J) (D : Factors J B) where
  prime : Ideal Equation
  isPrime : prime.IsPrime
  onProper : D.proper ∈ prime
  onCutoff : cutoff J B ∈ prime
  marks : Finset K
  sub : marks ⊆ J.marks
  liesOn : ∀ γ ∈ marks, prime ≤ RingHom.ker
    (eval₂RingHom (K1_14.graphEval (J.model.label γ)) (K1_14.atX (J.family.scalar γ)))
  persistent : Finset I
  hits : ∀ γ ∈ marks, ∀ x ∈ persistent, (J.family.scalar γ).eval (node x) = J.model.word x
  fiber : ℕ
  tangent : ℕ
  seed : ℕ
  positive_seed : 0 < seed
  sections : ∀ x ∉ persistent,
    let r := J.ell - persistent.card
    (marks.filter fun γ => (J.family.scalar γ).eval (node x) = J.model.word x).card ≤
      (1 + (J.e-3)*r)*fiber + r*tangent + (r*J.v + 2*J.w)*seed
def cutVelocity (J : Input) : ℕ := quotientOrder J.lo + 1
def cutOrdinate (J : Input) : ℕ := 1 + cutVelocity J * (J.e-1)
def cutSeed (J : Input) : ℕ := cutVelocity J * J.v + 2*J.hi
structure ProperCover (J : Input) (B : ResidueLift J) (D : Factors J B) where
  count : ℕ
  curves : Fin count → ProperCurve J B D
  covers : ∀ γ ∈ J.marks, rootOn J D.proper γ → ∃ j, γ ∈ (curves j).marks
  fiber : ∑ j, (curves j).fiber ≤ J.v*cutSeed J + J.v^2*cutVelocity J
  tangent : ∑ j, (curves j).tangent ≤ 2*J.e*J.v*cutSeed J + J.v^2*cutOrdinate J
  seed : ∑ j, (curves j).seed ≤
    J.e*cutSeed J + J.v*((2*J.e-2)*cutVelocity J + cutOrdinate J)
abbrev SeedClosure := AlgebraicClosure SeedField
def intoSeedClosure : Seeds →+* SeedClosure :=
  (algebraMap SeedField SeedClosure).comp (algebraMap Seeds SeedField)
def genericPoint (y : SeedClosure) : Biform →+* SeedClosure :=
  (eval₂RingHom intoSeedClosure y).comp (MvPolynomial.optionEquivLeft FX (Fin 2)).toRingHom
def liftConstantSeeds : SeedConstants →+* SeedClosure :=
  intoSeedClosure.comp liftSeeds
def reconstructed (J : Input) (B : ResidueLift J) (y : SeedClosure) : SeedClosure[X] :=
  let ζ := intoSeedClosure (MvPolynomial.C center)
  let ev := genericPoint y
  C ((liftConstantSeeds B.denominator)⁻¹) * B.numerator.map liftConstantSeeds +
    J.blockProduct.map (liftConstantSeeds.comp MvPolynomial.C) *
      ∑ j ∈ range (J.ell+1),
        C (ev (quotientNumerator J B j) / ev (quotientDenominator J B j)) *
          (Polynomial.X - C ζ)^j
def genericRoots (q : Equation) : Finset SeedClosure := by
  classical
  exact (q.map intoSeedClosure).roots.toFinset
structure DifferentialProduct (J : Input) (B : ResidueLift J) (q : Equation) where
  numerator : Polynomial (Polynomial Seeds)
  denominator : Seeds
  denominator_ne : denominator ≠ 0
  leading : numerator.coeff q.natDegree = C denominator
  abscissa_width : ∀ j, (numerator.coeff j).natDegree ≤ q.natDegree * degreeAt J.hi
  numerator_constant : ∀ i j m, Dx (((numerator.coeff i).coeff j).coeff m) = 0
  denominator_constant : ∀ m, Dx (denominator.coeff m) = 0
  identity :
    numerator.map (Polynomial.mapRingHom intoSeedClosure) =
      C (C (intoSeedClosure denominator)) *
        ∏ y ∈ genericRoots q,
          (Polynomial.X - C (reconstructed J B y))
def FlatSections (J : Input) (q : Equation) : Prop :=
  ∀ x : I, (∃ γ ∈ J.marks, rootOn J q γ ∧
      (J.family.scalar γ).eval (node x) ≠ J.model.word x) →
    ∃ g : Seeds, g ≠ 0 ∧ g.totalDegree ≤ seedDegree q ∧
      ∀ γ ∈ J.marks, rootOn J q γ →
        (J.family.scalar γ).eval (node x) = J.model.word x →
          K1_14.graphEval (J.model.label γ) g = 0
end
end HighCore82706Tangent
end
section
set_option autoImplicit false
namespace HighCore82706Tangent
noncomputable section
open P1 (blockLength)
open HighCore82706 (agreement)
open P1_7 (degreeAt quotientOrder)
open HighCore82706 (gap scale muNum lambdaNum ceilRatio properFee)
theorem ratio_le_ceil {n d k : ℕ} (hd : 0 < d) (hk : d*k ≤ n) :
    k ≤ ceilRatio n d := by
  apply (Nat.le_div_iff_mul_le hd).mpr
  exact (Nat.mul_comm d k ▸ hk).trans (Nat.le_add_right _ _)
theorem mu_cross {A n d s : ℕ} (hA : A ≤ n) (hd : d ≤ A) (hs : s ≤ d) :
    (A-d)*(n-s) ≤ (A-s)*(n-d) := by
  have hsA := hs.trans hd
  have hdn := hd.trans hA
  have hsn := hsA.trans hA
  have h : 0 ≤ ((d : ℤ)-s)*((n : ℤ)-A) :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hs)) (sub_nonneg.mpr (by exact_mod_cast hA))
  apply Int.ofNat_le.mp
  push_cast [Nat.cast_sub hd, Nat.cast_sub hsn, Nat.cast_sub hsA, Nat.cast_sub hdn]
  nlinarith only [h]
theorem lambda_cross {A n l s : ℕ} (hA : A ≤ n) (hl : l ≤ A) (hs : s ≤ A) :
    A*(n-s)*(l-s) ≤ n*(A-s)*l := by
  by_cases ht : s ≤ l
  · have hsn := hs.trans hA
    have h₁ : 0 ≤ (s : ℤ)*n*((A : ℤ)-l) := by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hl))
    have h₂ : 0 ≤ (s : ℤ)*A*((l : ℤ)-s) := by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast ht))
    apply Int.ofNat_le.mp
    push_cast [Nat.cast_sub hsn, Nat.cast_sub ht, Nat.cast_sub hs]
    nlinarith only [h₁, h₂]
  · simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge ht))]
def nodeVelocity (J : Input) : ℕ := lambdaNum J.hi * quotientOrder J.lo
def nodeReducedOrdinate (J : Input) : ℕ := muNum J.hi + (J.e-3)*nodeVelocity J
def nodeSeed (J : Input) : ℕ := nodeVelocity J*J.v + 2*J.hi*muNum J.hi
def weightedSection (J : Input) (h t s : ℕ) : ℕ :=
  nodeReducedOrdinate J*h + nodeVelocity J*t + nodeSeed J*s
theorem incidence_weights (J : Input) (s : ℕ) (hs : s ≤ degreeAt J.hi) :
    scale J.hi * (blockLength-s) ≤ (agreement-s) * muNum J.hi ∧
    scale J.hi * (blockLength-s) * (J.ell-s) ≤ (agreement-s) * nodeVelocity J := by
  have hAn : agreement ≤ blockLength := by decide
  have hL : quotientOrder J.lo ≤ agreement :=
    (Nat.sub_le _ _).trans (by decide : 131071 ≤ agreement)
  have hr : J.ell-s ≤ quotientOrder J.lo-s := by
    exact Nat.sub_le_sub_right (Nat.sub_le_sub_left J.lower _) _
  have hMu := Nat.mul_le_mul_left agreement (mu_cross hAn J.agreement_gap.le hs)
  have hLam := Nat.mul_le_mul_left (gap J.hi)
    (lambda_cross hAn hL (hs.trans J.agreement_gap.le))
  constructor
  · unfold scale muNum gap
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hMu
  · calc
      _ ≤ scale J.hi * (blockLength-s) * (quotientOrder J.lo-s) :=
        Nat.mul_le_mul_left _ hr
      _ ≤ _ := by
        unfold scale nodeVelocity lambdaNum
        convert hLam using 1 <;> ring
theorem scale_pos (J : Input) : 0 < scale J.hi :=
  Nat.mul_pos (by decide) (Nat.sub_pos_of_lt J.agreement_gap)
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
theorem mix_to_fee (J : Input) {k : ℕ}
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
  apply ratio_le_ceil (scale_pos J)
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
end HighCore82706Tangent
end
section
set_option autoImplicit false
namespace HighCore82706Tangent
noncomputable section
open Polynomial Finset
open P1 (K I blockLength node p)
open HighCore82706 (agreement)
open P1_7 (degreeAt)
open HighCore82706 (gap scale muNum properFee flatFee)
open K1_14 (Equation Seeds graphEval)
open K1_14_4 (seedDegree)
open scoped BigOperators
theorem fixed_word (J : Input) {U : Finset K} (hU : U ⊆ J.marks) :
    FixedWord J.model.word U J.family.scalar (degreeAt J.hi) := by
  have hsub := hU.trans J.marks_sub
  refine ⟨J.family.distinct.mono hsub, ?_, ?_⟩
  · intro γ hγ
    rcases (J.family.mark γ (hsub hγ)).scalar_degree with hz | hd
    · simp [hz]
    · have hh := J.upper
      change ((J.family.scalar γ).natDegree : ℤ) ≤ 131072 - 1 + J.model.overhead at hd
      change (J.family.scalar γ).natDegree ≤ 131071 + J.hi
      omega
  · intro γ hγ
    let mark := J.family.mark γ (hsub hγ)
    exact ⟨mark.bad.support, mark.bad.agreement, mark.scalar_hits⟩
theorem card_le_cover {α : Type*} [DecidableEq α] {m : ℕ} (T : Finset α)
    (U : Fin m → Finset α) (h : ∀ a ∈ T, ∃ j, a ∈ U j) :
    T.card ≤ ∑ j, (U j).card := by
  apply le_trans (card_le_card (t := univ.biUnion U) ?_) card_biUnion_le
  intro a ha
  obtain ⟨j, hj⟩ := h a ha
  exact mem_biUnion.mpr ⟨j, mem_univ _, hj⟩
private theorem persistent_le_degree (J : Input) {B : ResidueLift J} {D : Factors J B}
    (C : ProperCurve J B D) (h : 1 < C.marks.card) :
    C.persistent.card ≤ degreeAt J.hi := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
  have hw := fixed_word J C.sub
  let P := J.family.scalar a - J.family.scalar b
  have hp : P ≠ 0 := sub_ne_zero.mpr fun he => hab (hw.distinct ha hb he)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node
    ProximityPrize.Benchmark.IRSProfile.domain.injective P hp C.persistent ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
  intro x hx
  change (J.family.scalar a - J.family.scalar b).eval (node x) = 0
  rw [eval_sub, C.hits a ha x hx, C.hits b hb x hx, sub_self]
theorem proper_curve_count (J : Input) {B : ResidueLift J} {D : Factors J B}
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
  have hs : 0 < agreement - s := Nat.sub_pos_of_lt (hsd.trans_lt J.agreement_gap)
  have hN : N.card = blockLength - s := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    exact congrArg (· - s) ProximityPrize.Benchmark.IRSProfile.card_index
  have hagree (γ : K) (hγ : γ ∈ C.marks) : agreement - s ≤ (N.filter (hit γ)).card := by
    obtain ⟨Aγ,hAγ,he⟩ := (fixed_word J C.sub).hits γ hγ
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
  obtain ⟨hMu, hLam⟩ := incidence_weights J s hsd
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
def componentMarks (J : Input) (q : Equation) : Finset K := by
  classical
  exact J.marks.filter (rootOn J q)
theorem mem_componentMarks {J : Input} {q : Equation} {γ : K} :
    γ ∈ componentMarks J q ↔ γ ∈ J.marks ∧ rootOn J q γ := by
  classical
  exact mem_filter
theorem proper_count (J : Input) {B : ResidueLift J} {D : Factors J B}
    (C : ProperCover J B D) :
    (componentMarks J D.proper).card ≤ properFee J.lo J.hi J.e J.v := by
  classical
  have hcov := card_le_cover (componentMarks J D.proper)
      (fun j => (C.curves j).marks) (fun γ hγ =>
        C.covers γ (mem_componentMarks.mp hγ).1 (mem_componentMarks.mp hγ).2)
  apply mix_to_fee J
  calc
    _ ≤ ∑ j, scale J.hi * (C.curves j).marks.card := by
      rw [← mul_sum]
      exact Nat.mul_le_mul_left _ hcov
    _ ≤ ∑ j, weightedSection J (C.curves j).fiber (C.curves j).tangent (C.curves j).seed :=
      sum_le_sum fun j _ => proper_curve_count J (C.curves j)
    _ = weightedSection J (∑ j, (C.curves j).fiber) (∑ j, (C.curves j).tangent)
          (∑ j, (C.curves j).seed) := by
      simp only [weightedSection, sum_add_distrib, mul_sum]
    _ ≤ _ :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left _ C.fiber) (Nat.mul_le_mul_left _ C.tangent))
        (Nat.mul_le_mul_left _ C.seed)
theorem flat_component_count (J : Input) (q : Equation) (hq : seedDegree q < p)
    (B : FlatSections J q) :
    gap J.hi * (componentMarks J q).card ≤ HighCore82706.t * ((p+1)*seedDegree q) + gap J.hi := by
  classical
  let U := componentMarks J q
  have hU : U ⊆ J.marks := fun _ hz => (mem_componentMarks.mp hz).1
  apply section_capacity (fixed_word J hU) J.agreement_gap ((p+1)*seedDegree q)
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
theorem flat_count (J : Input) {B : ResidueLift J} (D : Factors J B)
    (hsections : ∀ j, FlatSections J (D.flat j)) :
    (∑ j, (componentMarks J (D.flat j)).card) ≤ flatFee J.hi J.v + J.e := by
  classical
  let U := fun j => componentMarks J (D.flat j)
  let n := ∑ j, (U j).card
  let g := gap J.hi
  have hg : 0 < g := Nat.sub_pos_of_lt J.agreement_gap
  have hv : J.v < p := (Nat.le_add_left J.v (J.e * degreeAt J.hi)).trans_lt J.flat_guard
  have hsum : g*n ≤ HighCore82706.t*(p+1)*J.v + g*D.count := by
    calc
      _ = ∑ j, g*(U j).card := mul_sum ..
      _ ≤ ∑ j, (HighCore82706.t*((p+1)*seedDegree (D.flat j)) + g) := by
        refine sum_le_sum fun j _ => ?_
        have hu : seedDegree (D.flat j) ≤ ∑ i, seedDegree (D.flat i) :=
          single_le_sum (f := fun i => seedDegree (D.flat i)) (fun _ _ => Nat.zero_le _) (mem_univ j)
        exact flat_component_count J (D.flat j) (hu.trans_lt (D.seed_sum.trans_lt hv)) (hsections j)
      _ = HighCore82706.t*(p+1)*(∑ j, seedDegree (D.flat j)) + g*D.count := by
        rw [sum_add_distrib, sum_const, smul_eq_mul, card_univ, Fintype.card_fin,
          ← mul_sum, ← mul_sum, mul_assoc, Nat.mul_comm D.count]
      _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left _ D.seed_sum) _
  have hrem : g*(n-D.count) ≤ HighCore82706.t*(p+1)*J.v := by
    rw [Nat.mul_sub_left_distrib]
    omega
  have hceil := ratio_le_ceil hg hrem
  have hsize : D.count ≤ J.e := D.sheets
  change n ≤ flatFee J.hi J.v + J.e
  change n-D.count ≤ flatFee J.hi J.v at hceil
  omega
theorem root_component (J : Input) {B : ResidueLift J} (D : Factors J B)
    {γ : K} (hγ : γ ∈ J.marks) :
    rootOn J D.proper γ ∨ ∃ j, rootOn J (D.flat j) γ := by
  let ev := eval₂RingHom (graphEval (J.model.label γ)) (K1_14.atX (J.family.scalar γ))
  have hz : ev J.f = 0 := (J.regular γ hγ).1
  rw [D.product, map_mul, map_prod] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp h
    exact Or.inr ⟨j, hj⟩
theorem count (J : Input) {B : ResidueLift J} {D : Factors J B}
    (C : ProperCover J B D) (hsections : ∀ j, FlatSections J (D.flat j)) :
    J.marks.card ≤ HighCore82706.tangentFee J.lo J.hi J.e J.v := by
  classical
  let T := componentMarks J D.proper
  let U := fun j => componentMarks J (D.flat j)
  have hcov : J.marks ⊆ T ∪ univ.biUnion U := by
    intro γ hγ
    rcases root_component J D hγ with ht | ⟨j, hu⟩
    · exact mem_union.mpr (Or.inl (mem_componentMarks.mpr ⟨hγ,ht⟩))
    · exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨j,mem_univ _,mem_componentMarks.mpr ⟨hγ,hu⟩⟩))
  have hc := (card_le_card hcov).trans (card_union_le _ _)
  have hp := proper_count J C
  have hf := card_biUnion_le.trans (flat_count J D hsections)
  change T.card ≤ properFee J.lo J.hi J.e J.v at hp
  change (univ.biUnion U).card ≤ flatFee J.hi J.v + J.e at hf
  change J.marks.card ≤ T.card + (univ.biUnion U).card at hc
  unfold HighCore82706.tangentFee
  omega
end
end HighCore82706Tangent
end
section
set_option autoImplicit false
namespace HighCore82706Tangent
noncomputable section
open P1_7 (degreeAt quotientOrder)
open scoped BigOperators
def c1 : Prop :=
  ∀ J : Input, Nonempty (ResidueLift J)
def c2 : Prop :=
  ∀ (J : Input) (B : ResidueLift J), Nonempty (Factors J B)
def c3 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B), Nonempty (ProperCover J B D)
def c4 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B) (j : Fin D.count),
    Nonempty (DifferentialProduct J B (D.flat j))
def c5 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B) (j : Fin D.count),
    DifferentialProduct J B (D.flat j) → FlatSections J (D.flat j)

end
end HighCore82706Tangent
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3
noncomputable section
open P1 (K I node)
open HighCore82706Tangent (Input ResidueLift Factors)
open K1_14 (FX Equation Seeds atX graphEval seedEmbedding)
open K1_14_6_1 (Dx partialX flatten)
open Polynomial (eval₂RingHom)
abbrev JetRing := Polynomial Equation
instance jetCommRing : CommRing JetRing := @Polynomial.commRing Equation inferInstance
abbrev Degree := ℕ × ℕ × ℕ
def nefDegree (h t s : ℕ) : Degree := (h + 2*t, t, s)
abbrev CoxVar := Fin 2 ⊕ (Fin 2 ⊕ Fin 3)
abbrev Cox := MvPolynomial CoxVar FX
def h₀ : CoxVar := .inl 0
def h₁ : CoxVar := .inl 1
def v₀ : CoxVar := .inr (.inl 0)
def v₁ : CoxVar := .inr (.inl 1)
def tᵢ (i : Fin 3) : CoxVar := .inr (.inr i)
def coxWeight : CoxVar → Degree
  | .inl _ => (1, 0, 0)
  | .inr (.inl i) => (2*i.val, 1, 0)
  | .inr (.inr _) => (0, 0, 1)
def ordinate : JetRing := Polynomial.C Polynomial.X
def seedVar (i : Fin 2) : JetRing :=
  Polynomial.C (Polynomial.C (MvPolynomial.X i))
def affineCoord : CoxVar → JetRing
  | .inl i => if i = 0 then 1 else ordinate
  | .inr (.inl i) => if i = 0 then 1 else Polynomial.X
  | .inr (.inr i) => if hi : i.val < 2 then seedVar ⟨i.val, hi⟩ else 1
def dehom : Cox →ₐ[FX] JetRing := MvPolynomial.aeval affineCoord
structure RelativeSection (Q : Ideal JetRing) (d : Degree) where
  order : ℕ
  finiteChart : Cox
  inverseChart : Cox
  finite_degree :
    finiteChart.IsWeightedHomogeneous coxWeight (d + order • (1, 0, 0))
  inverse_degree :
    inverseChart.IsWeightedHomogeneous coxWeight (d + order • (1, 0, 0))
  glue : ordinate ^ order * dehom finiteChart - dehom inverseChart ∈ Q
def RelativeSection.affine {Q : Ideal JetRing} {d : Degree}
    (S : RelativeSection Q d) : JetRing :=
  dehom S.finiteChart
def RelativeSection.restrict {Q P : Ideal JetRing} {d : Degree} (h : Q ≤ P)
    (S : RelativeSection Q d) : RelativeSection P d :=
  { S with glue := h S.glue }
def gradedPiece (Q : Ideal JetRing) (d : Degree) : Submodule FX (JetRing ⧸ Q) :=
  (MvPolynomial.weightedHomogeneousSubmodule FX coxWeight d).map
    (((Ideal.Quotient.mkₐ FX Q).comp dehom).toLinearMap)
structure CurveProbe (Q : Ideal JetRing) where
  fiber : ℕ
  tangent : ℕ
  seed : ℕ
  offset : ℤ
  threshold : ℕ
  hilbert : ∀ h t s, threshold ≤ h → threshold ≤ t → threshold ≤ s →
    (Module.finrank FX (gradedPiece Q (nefDegree h t s)) : ℤ) =
      (h*fiber + t*tangent + s*seed : ℕ) + offset
def markRoot (J : Input) (γ : K) : Equation →+* FX :=
  eval₂RingHom (graphEval (J.model.label γ)) (atX (J.family.scalar γ))
def markPoint (J : Input) (γ : K) : JetRing →ₐ[FX] FX where
  toRingHom := eval₂RingHom (markRoot J γ) (Dx (atX (J.family.scalar γ)))
  commutes' a := by
    change (eval₂RingHom (markRoot J γ) (Dx (atX (J.family.scalar γ))))
      (Polynomial.C (Polynomial.C (MvPolynomial.C a))) = a
    simp [markRoot, graphEval]
def tangentEquation (f : Equation) : JetRing :=
  Polynomial.C (MvPolynomial.optionEquivLeft FX (Fin 2) (partialX (flatten f))) +
    Polynomial.X * Polynomial.C f.derivative
def rootIdeal {J : Input} {B : ResidueLift J} (D : Factors J B) : Ideal JetRing :=
  Ideal.span {Polynomial.C D.proper}
def residueInJet {J : Input} (B : ResidueLift J) : JetRing :=
  Polynomial.C (Polynomial.C (HighCore82706Tangent.liftSeeds B.denominator))
def openFactor (J : Input) (B : ResidueLift J) : JetRing :=
  residueInJet B * Polynomial.C J.f.derivative
def saturate (Q : Ideal JetRing) (g : JetRing) : Ideal JetRing where
  carrier := {f | ∃ n : ℕ, g^n * f ∈ Q}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro f h ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m+n, ?_⟩
    rw [mul_add, pow_add]
    have hf : g^m * g^n * f = g^n * (g^m * f) := by ring
    have hh : g^m * g^n * h = g^m * (g^n * h) := by ring
    rw [hf, hh]
    exact Q.add_mem (Q.mul_mem_left _ hm) (Q.mul_mem_left _ hn)
  smul_mem' := by
    rintro a f ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change g^n * (a * f) ∈ Q
    rw [show g^n * (a*f) = a * (g^n*f) by ring]
    exact Q.mul_mem_left _ hn
theorem le_saturate (Q : Ideal JetRing) (g : JetRing) : Q ≤ saturate Q g := by
  intro f hf
  exact ⟨0, by simpa using hf⟩
def graphIdeal (J : Input) (B : ResidueLift J) (D : Factors J B) : Ideal JetRing :=
  saturate (Ideal.span {Polynomial.C D.proper, tangentEquation J.f}) (openFactor J B)
theorem proper_mem_graph (J : Input) (B : ResidueLift J) (D : Factors J B) :
    Polynomial.C D.proper ∈ graphIdeal J B D :=
  le_saturate _ _ (Ideal.subset_span (by simp))
structure TangentSection (J : Input) {B : ResidueLift J} (D : Factors J B) where
  section_ : RelativeSection (rootIdeal D) (J.e, 1, J.v)
  affine_eq : section_.affine = tangentEquation J.f
def jetDegree (J : Input) (r : ℕ) : Degree :=
  nefDegree (1 + (J.e-3)*r) r (r*J.v + 2*J.w)
def jetDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  residueInJet B * Polynomial.C J.f.derivative ^ (r-1)
def oldDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  Polynomial.C
    (MvPolynomial.optionEquivLeft FX (Fin 2) (HighCore82706Tangent.quotientDenominator J B r))
def oldNumerator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  Polynomial.C
    (MvPolynomial.optionEquivLeft FX (Fin 2) (HighCore82706Tangent.quotientNumerator J B r))
structure TaylorSections (J : Input) (B : ResidueLift J) (D : Factors J B) (r : ℕ) where
  denominator : RelativeSection (graphIdeal J B D) (jetDegree J r)
  numerator : Fin (r+1) → RelativeSection (graphIdeal J B D) (jetDegree J r)
  den_eq : denominator.affine = jetDenominator J B r
  agrees : ∀ j : Fin (r+1),
    oldDenominator J B j.val * (numerator j).affine -
      oldNumerator J B j.val * denominator.affine ∈ graphIdeal J B D
structure CurveMarks (J : Input) (B : ResidueLift J) (D : Factors J B) where
  prime : Ideal JetRing
  isPrime : prime.IsPrime
  onGraph : graphIdeal J B D ≤ prime
  onCutoff : Polynomial.C (HighCore82706Tangent.cutoff J B) ∈ prime
  regular : openFactor J B ∉ prime
  marks : Finset K
  sub : marks ⊆ J.marks
  liesOn : ∀ γ ∈ marks, prime ≤ RingHom.ker (markPoint J γ).toRingHom
structure CurveSlice (J : Input) (B : ResidueLift J) (D : Factors J B)
    extends CurveMarks J B D where
  probe : CurveProbe prime
  positive_seed : 0 < probe.seed
open scoped BigOperators
structure MixedCover (J : Input) (B : ResidueLift J) (D : Factors J B) where
  count : ℕ
  curves : Fin count → CurveSlice J B D
  covers : ∀ γ ∈ J.marks, HighCore82706Tangent.rootOn J D.proper γ → ∃ j, γ ∈ (curves j).marks
  fiber : ∑ j, (curves j).probe.fiber ≤
    J.v*HighCore82706Tangent.cutSeed J + J.v^2*HighCore82706Tangent.cutVelocity J
  tangent : ∑ j, (curves j).probe.tangent ≤
    2*J.e*J.v*HighCore82706Tangent.cutSeed J + J.v^2*HighCore82706Tangent.cutOrdinate J
  seed : ∑ j, (curves j).probe.seed ≤
    J.e*HighCore82706Tangent.cutSeed J + J.v*((2*J.e-2)*HighCore82706Tangent.cutVelocity J + HighCore82706Tangent.cutOrdinate J)
structure NodeSections {J : Input} {B : ResidueLift J} {D : Factors J B}
    (C : CurveMarks J B D) where
  persistent : Finset I
  hits : ∀ γ ∈ C.marks, ∀ x ∈ persistent,
    (J.family.scalar γ).eval (node x) = J.model.word x
  cuts : ∀ x ∉ persistent,
    ∃ S : RelativeSection C.prime (jetDegree J (J.ell - persistent.card)),
      S.affine ∉ C.prime ∧
      ∀ γ ∈ C.marks, (J.family.scalar γ).eval (node x) = J.model.word x →
        markPoint J γ S.affine = 0
end
end HighCore82706Tangent_3
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3
noncomputable section
open HighCore82706Tangent (Input ResidueLift Factors)
open K1_14 (FX Seeds Equation)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten partialX separant box separant_bound)
open MvPolynomial
open scoped BigOperators
open private K1_14_6_1.flatten_bound K1_14_6_1.partialX_bound from ProximityPrize.SubmissionLower.Fast055
local notation "cx" => MvPolynomial.X
local notation "unwrap" => MvPolynomial.optionEquivLeft FX (Fin 2)
def rootInJet : Biform →ₐ[FX] JetRing :=
  (Polynomial.CAlgHom : Equation →ₐ[FX] JetRing).comp (unwrap).toAlgHom
private theorem degreeOfSeeds (m : Option (Fin 2) →₀ ℕ) :
    m.some.sum (fun _ i => i) = m (some 0) + m (some 1) := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  rfl
private def homogenizeTerm (a c : ℕ) (m : Option (Fin 2) →₀ ℕ) (z : FX) : Cox :=
  MvPolynomial.C z *
    (cx h₀ ^ (a-m none) * cx h₁ ^ (m none) *
      cx (tᵢ 0) ^ (m (some 0)) * cx (tᵢ 1) ^ (m (some 1)) *
      cx (tᵢ 2) ^ (c-(m (some 0) + m (some 1))))
private theorem homogenizeTerm_degree {a c : ℕ} {m : Option (Fin 2) →₀ ℕ}
    (z : FX) (ha : m none ≤ a) (hc : m (some 0) + m (some 1) ≤ c) :
    (homogenizeTerm a c m z).IsWeightedHomogeneous coxWeight (a,0,c) := by
  have H₀ := (isWeightedHomogeneous_X FX coxWeight h₀).pow (a-m none)
  have H₁ := (isWeightedHomogeneous_X FX coxWeight h₁).pow (m none)
  have T₀ := (isWeightedHomogeneous_X FX coxWeight (tᵢ 0)).pow (m (some 0))
  have T₁ := (isWeightedHomogeneous_X FX coxWeight (tᵢ 1)).pow (m (some 1))
  have T₂ := (isWeightedHomogeneous_X FX coxWeight (tᵢ 2)).pow
    (c-(m (some 0) + m (some 1)))
  have hh := ((((H₀.mul H₁).mul T₀).mul T₁).mul T₂).C_mul z
  simpa [homogenizeTerm, coxWeight, h₀, h₁, tᵢ, Prod.smul_mk, Prod.mk_add_mk,
    Nat.sub_add_cancel ha, Nat.add_sub_of_le hc] using hh
private theorem rootInJet_X (i : Option (Fin 2)) :
    rootInJet (cx i) = i.elim ordinate seedVar := by
  cases i <;> simp [rootInJet, ordinate, seedVar]
private theorem rootInJet_aeval :
    rootInJet = MvPolynomial.aeval (fun i : Option (Fin 2) => i.elim ordinate seedVar) := by
  ext i
  simp [rootInJet_X]
private theorem dehom_homogenizeTerm (a c : ℕ) (m : Option (Fin 2) →₀ ℕ) (z : FX) :
    dehom (homogenizeTerm a c m z) = rootInJet (monomial m z) := by
  have h0 : dehom (cx h₀) = 1 := by simp [dehom, affineCoord, h₀]
  have h1 : dehom (cx h₁) = ordinate := by simp [dehom, affineCoord, h₁]
  have t0 : dehom (cx (tᵢ 0)) = seedVar 0 := by simp [dehom, affineCoord, tᵢ]
  have t1 : dehom (cx (tᵢ 1)) = seedVar 1 := by simp [dehom, affineCoord, tᵢ]
  have t2 : dehom (cx (tᵢ 2)) = 1 := by simp [dehom, affineCoord, tᵢ]
  rw [rootInJet_aeval, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_option, Fin.prod_univ_two]
  simp only [homogenizeTerm, map_mul, map_pow, h0, h1, t0, t1, t2, one_pow, one_mul, mul_one,
    Option.elim_none, Option.elim_some]
  rw [show dehom (MvPolynomial.C z) = algebraMap FX JetRing z by simp [dehom], mul_assoc]
theorem homogenizeBiform {a c : ℕ} {q : Biform} (hq : q ∈ box a c) :
    ∃ p : Cox, p.IsWeightedHomogeneous coxWeight (a,0,c) ∧ dehom p = rootInJet q := by
  classical
  refine ⟨∑ m ∈ q.support, homogenizeTerm a c m (q.coeff m), ?_, ?_⟩
  · apply IsWeightedHomogeneous.sum
    intro m hm
    obtain ⟨ha, hc⟩ := mem_restrictBidegree.mp hq m hm
    change m.some.sum (fun _ i => i) ≤ c at hc
    rw [degreeOfSeeds] at hc
    exact homogenizeTerm_degree _ ha hc
  · rw [map_sum, show rootInJet q = ∑ m ∈ q.support, rootInJet (monomial m (q.coeff m)) by
      conv_lhs => rw [q.as_sum, map_sum]]
    exact Finset.sum_congr rfl fun m _ => dehom_homogenizeTerm _ _ m _
private def inversePart (J : Input) : Equation :=
  Polynomial.X * J.f.derivative - Polynomial.C (J.e : Seeds) * J.f
private theorem seed_mul_nat (q : Seeds) (n : ℕ) :
    (q * (n : Seeds)).totalDegree ≤ q.totalDegree := by
  have hn : (n : Seeds) = MvPolynomial.C (n : FX) := (map_natCast MvPolynomial.C _).symm
  rw [hn]
  exact (totalDegree_mul _ _).trans_eq (by rw [totalDegree_C, add_zero])
private theorem inversePart_bound (J : Input) :
    (inversePart J).natDegree ≤ J.e-1 ∧ K1_14.SeedBound (inversePart J) J.v := by
  have hpos : 0 < J.e := J.reduced.1
  have hcoef (n : ℕ) :
      (inversePart J).coeff (n+1) =
        J.f.coeff (n+1) * (n+1 : ℕ) - (J.e : Seeds) * J.f.coeff (n+1) := by
    simp only [inversePart, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
      Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one]
  constructor
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    cases i with
    | zero => omega
    | succ i =>
      rw [hcoef]
      by_cases he : i+1 = J.e
      · rw [he, mul_comm, sub_self]
      · have hd : J.f.natDegree < i+1 := by
          change J.e < i+1
          omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd, zero_mul, mul_zero, sub_self]
  · intro i
    have hright (n : ℕ) : ((J.e : Seeds) * J.f.coeff n).totalDegree ≤ J.v := by
      rw [mul_comm]
      exact (seed_mul_nat _ _).trans (J.seed_bound _)
    cases i with
    | zero =>
      simp only [inversePart, Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero,
        Polynomial.coeff_C_mul, zero_sub, totalDegree_neg]
      exact hright _
    | succ i =>
      rw [hcoef]
      exact (totalDegree_sub _ _).trans
        (max_le ((seed_mul_nat _ _).trans (J.seed_bound _)) (hright _))
private theorem tangent_glue {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (y a f c : A) (v q : B) :
    φ y * (q + v*φ c) - (φ y*q + v*φ (y*c-a*f)) = v*(φ a*φ f) := by
  rw [map_sub, map_mul, map_mul]
  ring
set_option maxHeartbeats 800000 in
set_option maxSynthPendingDepth 16 in
set_option backward.isDefEq.respectTransparency false in
theorem tangent_section (J : Input) (B : ResidueLift J) (D : Factors J B) :
    Nonempty (TangentSection J D) := by
  let fX := partialX (flatten J.f)
  let yVar : Biform := cx (none : Option (Fin 2))
  have hF := K1_14_6_1.partialX_bound (K1_14_6_1.flatten_bound (f := J.f) le_rfl J.seed_bound)
  have hF' : fX ∈ box (J.e+1) J.v := by
    rw [mem_restrictBidegree] at hF ⊢
    exact fun m hm => ⟨(hF m hm).1.trans (Nat.le_succ _), (hF m hm).2⟩
  have hY : yVar ∈ box 1 0 := K1_14_6_1.ordinate_mem
  have hYF : yVar * fX ∈ box (J.e+1) J.v := by
    simpa only [Nat.add_comm 1, Nat.zero_add] using mul_mem_restrictBidegree hY hF
  obtain ⟨A₀, hA₀, evA₀⟩ := homogenizeBiform hF'
  obtain ⟨A₁, hA₁, evA₁⟩ := homogenizeBiform hYF
  obtain ⟨B₀, hB₀, evB₀⟩ := homogenizeBiform (separant_bound (f := J.f) le_rfl J.seed_bound)
  obtain ⟨B₁, hB₁, evB₁⟩ := homogenizeBiform
    (K1_14_6_1.flatten_bound (inversePart_bound J).1 (inversePart_bound J).2)
  let G₀ := cx v₀ * A₀ + cx v₁ * B₀
  let G₁ := cx v₀ * A₁ + cx v₁ * B₁
  have hg {A B : Cox} (hA : A.IsWeightedHomogeneous coxWeight (J.e+1,0,J.v))
      (hB : B.IsWeightedHomogeneous coxWeight (J.e-1,0,J.v)) :
      (cx v₀ * A + cx v₁ * B).IsWeightedHomogeneous coxWeight
        ((J.e,1,J.v) + (1 : ℕ) • (1,0,0)) := by
    have hep : 0 < J.e := J.reduced.1
    have he : 2 + (J.e-1) = J.e+1 := by omega
    have ha := (isWeightedHomogeneous_X FX coxWeight v₀).mul hA
    have hb := (isWeightedHomogeneous_X FX coxWeight v₁).mul hB
    apply IsWeightedHomogeneous.add
    · simpa [coxWeight, v₀, Prod.mk_add_mk] using ha
    · simpa [coxWeight, v₁, Prod.mk_add_mk, he] using hb
  have ev0 : dehom (cx v₀) = 1 := by simp [dehom, affineCoord, v₀]
  have ev1 : dehom (cx v₁) = (Polynomial.X : JetRing) := by simp [dehom, affineCoord, v₁]
  have hsep : rootInJet (separant (flatten J.f)) = Polynomial.C J.f.derivative := by
    simp only [separant, rootInJet, AlgHom.coe_comp, Function.comp_apply,
      AlgEquiv.coe_toAlgHom, optionEquivLeft_pderiv_none, AlgEquiv.apply_symm_apply]
    rfl
  have hinv : rootInJet (flatten (inversePart J)) = Polynomial.C (inversePart J) := by
    simp only [rootInJet, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply]
    rfl
  have hYF' : rootInJet (yVar*fX) = ordinate * rootInJet fX := by
    rw [map_mul, show rootInJet yVar = ordinate from rootInJet_X none]
  have heq₀ : dehom G₀ = tangentEquation J.f := by
    simp only [G₀, map_add, map_mul, ev0, ev1, evA₀, evB₀, hsep, one_mul]
    rfl
  have heq₁ :
      dehom G₁ = ordinate * rootInJet fX + Polynomial.X * Polynomial.C (inversePart J) := by
    simp only [G₁, map_add, map_mul, ev0, ev1, evA₁, evB₁, hYF', hinv, one_mul]
  refine ⟨⟨⟨1, G₀, G₁, hg hA₀ hB₀, hg hA₁ hB₁, ?_⟩, heq₀⟩⟩
  rw [pow_one, heq₀, heq₁]
  have heq :
      ordinate * tangentEquation J.f -
        (ordinate * rootInJet fX + Polynomial.X * Polynomial.C (inversePart J)) =
        Polynomial.X * (Polynomial.C (Polynomial.C (J.e : Seeds)) * Polynomial.C J.f) := by
    change ordinate * (rootInJet fX + Polynomial.X * Polynomial.C J.f.derivative) -
      (ordinate * rootInJet fX + Polynomial.X * Polynomial.C (inversePart J)) = _
    exact @tangent_glue Equation JetRing (@Polynomial.commRing Seeds inferInstance) jetCommRing
      Polynomial.C Polynomial.X
      (Polynomial.C (J.e : Seeds)) J.f J.f.derivative Polynomial.X (rootInJet fX)
  have hf : Polynomial.C J.f ∈ rootIdeal D := by
    rw [D.product, Polynomial.C_mul]
    exact (rootIdeal D).mul_mem_right _ (Ideal.subset_span (Set.mem_singleton _))
  rw [heq]
  exact (rootIdeal D).mul_mem_left _ ((rootIdeal D).mul_mem_left _ hf)
end
end HighCore82706Tangent_3
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3
noncomputable section
open K1_14 (FX)
open P1 (K)
open MvPolynomial
open scoped BigOperators
theorem weight_coordinates (m : CoxVar →₀ ℕ) :
    Finsupp.weight coxWeight m =
      (m h₀ + m h₁ + 2 * m v₁, m v₀ + m v₁, m (tᵢ 0) + m (tᵢ 1) + m (tᵢ 2)) := by
  rw [Finsupp.weight_eq_sum, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_three]
  simp [coxWeight, h₀, h₁, v₀, v₁, tᵢ, Prod.mk_add_mk, Prod.smul_mk,
    Nat.mul_comm, Nat.add_assoc]
private theorem cox_piece_finite (d : Degree) :
    Module.Finite FX (weightedHomogeneousSubmodule FX coxWeight d) := by
  have hle : weightedHomogeneousSubmodule FX coxWeight d ≤
      restrictTotalDegree CoxVar FX (d.1 + d.2.1 + d.2.2) := by
    intro p hp
    apply (mem_restrictTotalDegree _ _ _).mpr
    apply Finset.sup_le
    intro m hm
    have h := hp (mem_support_iff.mp hm)
    rw [weight_coordinates] at h
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sum_type, Fintype.sum_sum_type,
      Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_three]
    change m h₀ + m h₁ + (m v₀ + m v₁ + (m (tᵢ 0) + m (tᵢ 1) + m (tᵢ 2))) ≤ _
    rw [← h]
    change _ ≤ (m h₀ + m h₁ + 2*m v₁) + (m v₀ + m v₁) +
      (m (tᵢ 0) + m (tᵢ 1) + m (tᵢ 2))
    omega
  exact Submodule.finiteDimensional_of_le hle
instance gradedPiece_finite (Q : Ideal JetRing) (d : Degree) :
    Module.Finite FX (gradedPiece Q d) := by
  have := cox_piece_finite d
  unfold gradedPiece
  infer_instance
private def quotientMap (Q : Ideal JetRing) : Cox →ₐ[FX] JetRing ⧸ Q :=
  (Ideal.Quotient.mkₐ FX Q).comp dehom
private theorem mk_mem_piece {Q : Ideal JetRing} {d : Degree} {p : Cox}
    (hp : p.IsWeightedHomogeneous coxWeight d) :
    quotientMap Q p ∈ gradedPiece Q d :=
  Submodule.mem_map.mpr ⟨p, hp, rfl⟩
private theorem affine_X_h₀ : dehom (MvPolynomial.X h₀) = 1 := by simp [dehom, affineCoord, h₀]
private theorem affine_X_h₁ : dehom (MvPolynomial.X h₁) = ordinate := by simp [dehom, affineCoord, h₁]
private theorem affine_X_v₀ : dehom (MvPolynomial.X v₀) = 1 := by simp [dehom, affineCoord, v₀]
private theorem affine_X_t₀ : dehom (MvPolynomial.X (tᵢ 0)) = seedVar 0 := by
  simp [dehom, affineCoord, tᵢ]
private theorem affine_X_t₂ : dehom (MvPolynomial.X (tᵢ 2)) = 1 := by
  simp [dehom, affineCoord, tᵢ]
private theorem shifted_monomial {Q : Ideal JetRing} {d : Degree}
    (S : RelativeSection Q d) {h t s : ℕ} (hh : 2*S.order ≤ h)
    (m : CoxVar →₀ ℕ) (a : FX) (hm : Finsupp.weight coxWeight m = nefDegree h t s) :
    Ideal.Quotient.mk Q S.affine * quotientMap Q (monomial m a) ∈
      gradedPiece Q (nefDegree h t s + d) := by
  classical
  have hbase : h ≤ m h₀ + m h₁ := by
    have h' := hm
    rw [weight_coordinates] at h'
    have ha := congrArg Prod.fst h'
    have hb := congrArg (fun d : Degree => d.2.1) h'
    change m h₀ + m h₁ + 2*m v₁ = h + 2*t at ha
    change m v₀ + m v₁ = t at hb
    omega
  have helper (i : CoxVar) (hi : coxWeight i = (1, 0, 0)) (hm' : S.order ≤ m i)
      (p : Cox) (hp : p.IsWeightedHomogeneous coxWeight (d + S.order • (1,0,0)))
      (heq : Ideal.Quotient.mk Q S.affine * quotientMap Q (MvPolynomial.X i ^ S.order) =
        quotientMap Q p) :
      Ideal.Quotient.mk Q S.affine * quotientMap Q (monomial m a) ∈
        gradedPiece Q (nefDegree h t s + d) := by
    let u := m - Finsupp.single i S.order
    have hle : Finsupp.single i S.order ≤ m := Finsupp.single_le_iff.mpr hm'
    have hu : u + Finsupp.single i S.order = m := tsub_add_cancel_of_le hle
    have hwt : Finsupp.weight coxWeight u + S.order • (1, 0, 0) = nefDegree h t s := by
      rw [← hm, ← hu, map_add, Finsupp.weight_single, hi]
    have hw : (monomial u a : Cox).IsWeightedHomogeneous coxWeight
        (Finsupp.weight coxWeight u) := isWeightedHomogeneous_monomial _ _ _ rfl
    have hmem : quotientMap Q (monomial u a * p) ∈
        gradedPiece Q (Finsupp.weight coxWeight u + (d + S.order • (1,0,0))) :=
      mk_mem_piece (hw.mul hp)
    rw [show Finsupp.weight coxWeight u + (d + S.order • (1,0,0)) =
      nefDegree h t s + d by rw [← hwt]; ac_rfl] at hmem
    have hmdecomp : (monomial m a : Cox) = monomial u a * MvPolynomial.X i ^ S.order := by
      rw [MvPolynomial.X_pow_eq_monomial, monomial_mul_monomial, hu, mul_one]
    rw [hmdecomp, map_mul, mul_left_comm, heq, ← map_mul]
    exact hmem
  by_cases h₀ex : S.order ≤ m h₀
  · apply helper h₀ rfl h₀ex S.finiteChart S.finite_degree
    simp [quotientMap, RelativeSection.affine, affine_X_h₀]
  · have h₁ex : S.order ≤ m h₁ := by omega
    apply helper h₁ rfl h₁ex S.inverseChart S.inverse_degree
    have hg := Ideal.Quotient.eq_zero_iff_mem.mpr S.glue
    simp only [map_sub, map_mul, map_pow, sub_eq_zero] at hg
    change Ideal.Quotient.mk Q S.affine *
      Ideal.Quotient.mk Q (dehom (MvPolynomial.X h₁ ^ S.order)) =
        Ideal.Quotient.mk Q (dehom S.inverseChart)
    rw [map_pow, affine_X_h₁, map_pow, mul_comm]
    exact hg
theorem relativeSection_mul_gradedPiece {Q : Ideal JetRing} {d : Degree}
    (S : RelativeSection Q d) {h t s : ℕ} (hh : 2*S.order ≤ h)
    {a : JetRing ⧸ Q} (ha : a ∈ gradedPiece Q (nefDegree h t s)) :
    Ideal.Quotient.mk Q S.affine * a ∈ gradedPiece Q (nefDegree h t s + d) := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha
  change p.IsWeightedHomogeneous coxWeight (nefDegree h t s) at hp
  change Ideal.Quotient.mk Q S.affine * quotientMap Q p ∈ _
  have he : quotientMap Q p = ∑ m ∈ p.support, quotientMap Q (monomial m (p.coeff m)) := by
    conv_lhs => rw [p.as_sum, map_sum]
  rw [he, Finset.mul_sum]
  exact Submodule.sum_mem _ fun m hm =>
    shifted_monomial S hh m (p.coeff m) (hp (mem_support_iff.mp hm))
private theorem mark_separator {U : Finset K} {ev : K → JetRing →ₐ[FX] FX}
    (hinj : Set.InjOn (fun γ => ev γ (seedVar 0)) (U : Set K))
    (h t s : ℕ) (hs : U.card ≤ s) (γ : U) :
    ∃ p : Cox, p.IsWeightedHomogeneous coxWeight (nefDegree h t s) ∧
      ∀ η : U, ev η (dehom p) = if η = γ then 1 else 0 := by
  classical
  let E := (Finset.univ : Finset U).erase γ
  let sep (η : U) : Cox := MvPolynomial.X (tᵢ 0) - C (ev η (seedVar 0)) * MvPolynomial.X (tᵢ 2)
  have sep_eval (η θ : U) :
      ev η (dehom (sep θ)) = ev η (seedVar 0) - ev θ (seedVar 0) := by
    simp only [sep, map_sub, map_mul, affine_X_t₀, affine_X_t₂, mul_one]
    rw [show dehom (C (ev θ (seedVar 0))) = algebraMap FX JetRing (ev θ (seedVar 0)) by
      simp [dehom], (ev η.val).commutes]
    rfl
  let poly := ∏ η ∈ E, sep η
  have hγ : ev γ (dehom poly) ≠ 0 := by
    rw [show ev γ (dehom poly) = ∏ η ∈ E, ev γ (dehom (sep η)) by simp [poly, map_prod]]
    apply Finset.prod_ne_zero_iff.mpr
    intro η hη
    rw [sep_eval, sub_ne_zero]
    exact fun hEq => (Finset.mem_erase.mp hη).1 (Subtype.ext (hinj η.property γ.property hEq.symm))
  let pad : Cox := MvPolynomial.X h₀ ^ (h+2*t) * MvPolynomial.X v₀ ^ t * MvPolynomial.X (tᵢ 2) ^ (s-E.card)
  let p := C (ev γ (dehom poly))⁻¹ * (poly * pad)
  have hhom (η : U) : (sep η).IsWeightedHomogeneous coxWeight (0,0,1) := by
    exact (isWeightedHomogeneous_X FX coxWeight (tᵢ 0)).sub
      ((isWeightedHomogeneous_X FX coxWeight (tᵢ 2)).C_mul _)
  have hsum : (∑ _η ∈ E, ((0,0,1) : Degree)) = (0,0,E.card) := by
    rw [Finset.sum_const]
    simp [Prod.smul_mk]
  have hpoly : poly.IsWeightedHomogeneous coxWeight (0,0,E.card) := by
    rw [← hsum]
    exact IsWeightedHomogeneous.prod E sep (fun _ => (0,0,1)) (fun η _ => hhom η)
  have hp := ((hpoly.mul (((isWeightedHomogeneous_X FX coxWeight h₀).pow (h+2*t)).mul
    ((isWeightedHomogeneous_X FX coxWeight v₀).pow t) |>.mul
    ((isWeightedHomogeneous_X FX coxWeight (tᵢ 2)).pow (s-E.card)))).C_mul
    (ev γ (dehom poly))⁻¹)
  have hc : E.card ≤ s := (Finset.card_le_card (Finset.erase_subset _ _)).trans
    (by simpa only [Finset.card_univ, Fintype.card_coe] using hs)
  refine ⟨p, ?_, ?_⟩
  · have hdeg : (0, 0, E.card) + ((h+2*t) • coxWeight h₀ +
        t • coxWeight v₀ + (s-E.card) • coxWeight (tᵢ 2)) = nefDegree h t s := by
      simp [coxWeight, h₀, v₀, tᵢ, nefDegree, Prod.smul_mk, Prod.mk_add_mk,
        Nat.add_sub_of_le hc]
    exact hdeg ▸ hp
  · intro η
    have hpad : dehom pad = 1 := by simp [pad, affine_X_h₀, affine_X_v₀, affine_X_t₂]
    have hval : ev η (dehom p) = (ev γ (dehom poly))⁻¹ * ev η (dehom poly) := by
      simp only [p, map_mul, hpad, mul_one]
      rw [show dehom (C (ev γ (dehom poly))⁻¹) =
        algebraMap FX JetRing (ev γ (dehom poly))⁻¹ by simp [dehom],
        (ev η.val).commutes]
      rfl
    rw [hval]
    split_ifs with h
    · subst η
      exact inv_mul_cancel₀ hγ
    · have hη : η ∈ E := Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩
      have hz : ev η (dehom poly) = 0 := by
        rw [show ev η (dehom poly) = ∏ θ ∈ E, ev η (dehom (sep θ)) by simp [poly, map_prod]]
        exact Finset.prod_eq_zero hη (by rw [sep_eval, sub_self])
      rw [hz, mul_zero]
theorem count_relative_section
    (Q : Ideal JetRing) (hQ : Q.IsPrime) (G : CurveProbe Q) (h t s : ℕ)
    (S : RelativeSection Q (nefDegree h t s)) (hS : S.affine ∉ Q)
    (U : Finset K) (ev : K → JetRing →ₐ[FX] FX)
    (hinj : Set.InjOn (fun γ => ev γ (seedVar 0)) (U : Set K))
    (hI : ∀ γ ∈ U, Q ≤ RingHom.ker (ev γ).toRingHom)
    (hz : ∀ γ ∈ U, ev γ S.affine = 0) :
    U.card ≤ h*G.fiber + t*G.tangent + s*G.seed := by
  classical
  let N := G.threshold + 2*S.order + U.card
  let A := gradedPiece Q (nefDegree N N N)
  let B := gradedPiece Q (nefDegree (N+h) (N+t) (N+s))
  let qev (γ : U) : JetRing ⧸ Q →ₐ[FX] FX :=
    Ideal.Quotient.liftₐ Q (ev γ) (hI γ γ.property)
  let E : B →ₗ[FX] (U → FX) :=
    LinearMap.pi fun γ => (qev γ).toLinearMap.comp B.subtype
  have eval_mk (γ : U) (q : JetRing) : qev γ (Ideal.Quotient.mk Q q) = ev γ q := rfl
  have hsurj : Function.Surjective E := by
    have hlarge : U.card ≤ N+s := by dsimp only [N]; omega
    choose p hp he using fun γ : U => mark_separator hinj (N+h) (N+t) (N+s) hlarge γ
    let v (γ : U) : B := ⟨quotientMap Q (p γ), mk_mem_piece (hp γ)⟩
    have hv (γ η : U) : E (v γ) η = if η = γ then 1 else 0 := by
      change qev η (Ideal.Quotient.mk Q (dehom (p γ))) = _
      rw [eval_mk]
      exact he γ η
    intro f
    refine ⟨∑ γ : U, f γ • v γ, ?_⟩
    ext η
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv]
    simp
  let bySection := LinearMap.mulLeft FX (Ideal.Quotient.mk Q S.affine)
  have hto (a : A) : bySection a.val ∈ B := by
    have hn : 2*S.order ≤ N := by dsimp only [N]; omega
    have hh := relativeSection_mul_gradedPiece S (t := N) (s := N) hn a.property
    have heq : nefDegree N N N + nefDegree h t s =
        nefDegree (N+h) (N+t) (N+s) := by
      simp only [nefDegree, Prod.mk_add_mk]
      congr 1
      ring
    rw [heq] at hh
    exact hh
  let M : A →ₗ[FX] B := (bySection.comp A.subtype).codRestrict B hto
  have hk (a : A) : M a ∈ LinearMap.ker E := by
    rw [LinearMap.mem_ker]
    ext γ
    change qev γ ((Ideal.Quotient.mk Q S.affine) * a.val) = 0
    rw [map_mul, eval_mk, hz γ γ.property, zero_mul]
  let MK := M.codRestrict (LinearMap.ker E) hk
  let _ : Q.IsPrime := hQ
  have hmk : Ideal.Quotient.mk Q S.affine ≠ 0 := fun h0 => hS
    (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hminj : Function.Injective MK := by
    intro a b hab
    apply Subtype.ext
    apply mul_left_cancel₀ hmk
    exact congrArg (fun x : LinearMap.ker E => x.val.val) hab
  have hd := LinearMap.finrank_le_finrank_of_injective hminj
  have hr := E.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe] at hr
  have hg : G.threshold ≤ N := by dsimp only [N]; omega
  have hA : (Module.finrank FX A : ℤ) =
      (N*G.fiber + N*G.tangent + N*G.seed : ℕ) + G.offset :=
    G.hilbert N N N hg hg hg
  have hB : (Module.finrank FX B : ℤ) =
      ((N+h)*G.fiber + (N+t)*G.tangent + (N+s)*G.seed : ℕ) + G.offset :=
    G.hilbert _ _ _ (hg.trans (Nat.le_add_right _ _))
      (hg.trans (Nat.le_add_right _ _)) (hg.trans (Nat.le_add_right _ _))
  have hdim : U.card + Module.finrank FX A ≤ Module.finrank FX B :=
    (Nat.add_le_add_left hd _).trans_eq hr
  have hcast := Int.ofNat_le.mpr hdim
  rw [Nat.cast_add, hA, hB] at hcast
  push_cast at hcast
  apply Int.ofNat_le.mp
  push_cast
  linarith only [hcast,
    add_mul (N : ℤ) (h : ℤ) (G.fiber : ℤ),
    add_mul (N : ℤ) (t : ℤ) (G.tangent : ℤ),
    add_mul (N : ℤ) (s : ℤ) (G.seed : ℤ)]
end
end HighCore82706Tangent_3
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3
noncomputable section
open P1 (K I node)
open HighCore82706Tangent (Input ResidueLift Factors)
open K1_14 (FX Equation Seeds seedEmbedding)
open MvPolynomial (optionEquivLeft)
open Polynomial (eval₂RingHom)
def c1 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B) (r : ℕ),
    r ≤ J.ell + 1 → Nonempty (TaylorSections J B D r)
def c2 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B) (_G : TangentSection J D)
    (S : RelativeSection (graphIdeal J B D) (jetDegree J (J.ell+1))),
    (∀ P : Ideal JetRing, P.IsPrime → graphIdeal J B D ≤ P → openFactor J B ∉ P →
      (S.affine ∈ P ↔ Polynomial.C (HighCore82706Tangent.cutoff J B) ∈ P)) →
    Nonempty (MixedCover J B D)
def c3 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B),
    (∀ r : ℕ, r ≤ J.ell + 1 → TaylorSections J B D r) →
    ∀ C : CurveMarks J B D, Nonempty (NodeSections C)
private theorem seedBiform_image (s : HighCore82706Tangent.SeedConstants) :
    optionEquivLeft FX (Fin 2) (HighCore82706Tangent.seedBiform s) =
      Polynomial.C (HighCore82706Tangent.liftSeeds s) := by
  change optionEquivLeft FX (Fin 2) (MvPolynomial.rename some (HighCore82706Tangent.liftSeeds s)) = _
  generalize HighCore82706Tangent.liftSeeds s = g
  induction g using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.rename_C, MvPolynomial.optionEquivLeft_C]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | mul_X a i ha => rw [map_mul, map_mul, map_mul, MvPolynomial.rename_X,
      MvPolynomial.optionEquivLeft_X_some, ha]
private theorem oldDenominator_eq (J : Input) (B : ResidueLift J) (r : ℕ) :
    oldDenominator J B r = residueInJet B * Polynomial.C J.f.derivative ^ (2*r-1) := by
  unfold oldDenominator HighCore82706Tangent.quotientDenominator K1_14_6_1.separant
  rw [map_mul, map_pow, seedBiform_image, MvPolynomial.optionEquivLeft_pderiv_none,
    AlgEquiv.apply_symm_apply, map_mul, map_pow]
  rfl
private theorem cutoff_agrees {J : Input} {B : ResidueLift J} {D : Factors J B}
    (T : TaylorSections J B D (J.ell+1)) (P : Ideal JetRing) (hp : P.IsPrime)
    (hg : graphIdeal J B D ≤ P) (hu : openFactor J B ∉ P) :
    (T.numerator (Fin.last (J.ell+1))).affine ∈ P ↔ Polynomial.C (HighCore82706Tangent.cutoff J B) ∈ P := by
  have hB : residueInJet B ∉ P := fun h => hu (P.mul_mem_right _ h)
  have hsep : Polynomial.C J.f.derivative ∉ P := fun h => hu (P.mul_mem_left _ h)
  have not_mem (m : ℕ) : residueInJet B * Polynomial.C J.f.derivative ^ m ∉ P := by
    intro h
    exact ((hp.mul_mem_iff_mem_or_mem.mp h).resolve_left hB |> hp.mem_of_pow_mem m) |> hsep
  have hO : oldDenominator J B (J.ell+1) ∉ P := by
    rw [oldDenominator_eq]
    exact not_mem _
  have hD : T.denominator.affine ∉ P := by
    rw [T.den_eq, jetDenominator]
    exact not_mem _
  have h := hg (T.agrees (Fin.last (J.ell+1)))
  change
    oldDenominator J B (J.ell+1) * (T.numerator (Fin.last (J.ell+1))).affine -
      Polynomial.C (HighCore82706Tangent.cutoff J B) * T.denominator.affine ∈ P at h
  have hp' {a b : JetRing} (hab : a - b ∈ P) : a ∈ P ↔ b ∈ P := by
    constructor
    · intro ha
      convert P.sub_mem ha hab using 1
      abel
    · intro hb
      convert P.add_mem hab hb using 1
      abel
  calc
    _ ↔ oldDenominator J B (J.ell+1) * (T.numerator (Fin.last (J.ell+1))).affine ∈ P := by
      rw [hp.mul_mem_iff_mem_or_mem, or_iff_right hO]
    _ ↔ Polynomial.C (HighCore82706Tangent.cutoff J B) * T.denominator.affine ∈ P := hp' h
    _ ↔ _ := by rw [hp.mul_mem_iff_mem_or_mem, or_iff_left hD]
private theorem mark_seed (J : Input) (γ : K) :
    markPoint J γ (seedVar 0) = seedEmbedding (J.model.label γ) := by
  change (eval₂RingHom (markRoot J γ) _) (Polynomial.C (Polynomial.C (MvPolynomial.X 0))) = _
  simp [markRoot, K1_14.graphEval]
private theorem mark_seed_inj (J : Input) (U : Finset K) :
    Set.InjOn (fun γ => markPoint J γ (seedVar 0)) (U : Set K) := by
  intro γ _ η _ he
  change markPoint J γ (seedVar 0) = markPoint J η (seedVar 0) at he
  rw [mark_seed, mark_seed] at he
  exact sub_left_inj.mp (seedEmbedding.injective he)
private def packCurve {J : Input} {B : ResidueLift J}
    {D : Factors J B} (C : CurveSlice J B D) (N : NodeSections C.toCurveMarks) :
    HighCore82706Tangent.ProperCurve J B D where
  prime := C.prime.comap Polynomial.C
  isPrime := C.isPrime.comap Polynomial.C
  onProper := C.onGraph (proper_mem_graph J B D)
  onCutoff := C.onCutoff
  marks := C.marks
  sub := C.sub
  liesOn γ hγ := by
    intro f hf
    have he := C.liesOn γ hγ hf
    change (eval₂RingHom (markRoot J γ) _) (Polynomial.C f) = 0 at he
    simpa [markRoot] using he
  persistent := N.persistent
  hits := N.hits
  fiber := C.probe.fiber
  tangent := C.probe.tangent
  seed := C.probe.seed
  positive_seed := C.positive_seed
  sections := by
    classical
    intro x hx
    obtain ⟨S, hS, hz⟩ := N.cuts x hx
    let U := C.marks.filter fun γ => (J.family.scalar γ).eval (node x) = J.model.word x
    exact count_relative_section C.prime C.isPrime C.probe _ _ _ S hS U (markPoint J)
      (mark_seed_inj J U)
      (fun γ hγ => C.liesOn γ (Finset.mem_filter.mp hγ).1)
      (fun γ hγ => hz γ (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hγ).2)
theorem of_children (lift : c1) (mixed : c2) (shorten : c3) : HighCore82706Tangent.c3 := by
  classical
  intro J B D
  obtain ⟨G⟩ := tangent_section J B D
  let T (r : ℕ) (hr : r ≤ J.ell+1) := Classical.choice (lift J B D r hr)
  let C₀ := T (J.ell+1) le_rfl
  obtain ⟨M⟩ := mixed J B D G (C₀.numerator (Fin.last (J.ell+1))) (cutoff_agrees C₀)
  let N (j : Fin M.count) := Classical.choice (shorten J B D T (M.curves j).toCurveMarks)
  let C (j : Fin M.count) := packCurve (M.curves j) (N j)
  exact ⟨{
    count := M.count
    curves := C
    covers := M.covers
    fiber := M.fiber
    tangent := M.tangent
    seed := M.seed }⟩
end
end HighCore82706Tangent_3
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_1
noncomputable section
open HighCore82706Tangent (Input)
open HighCore82706Tangent_3 (JetRing Degree Cox coxWeight dehom ordinate jetDegree RelativeSection)
open K1_14 (FX Equation)
open K1_14_6_1 (flatten partialX)
abbrev velocity : JetRing := Polynomial.X
def coefficientDerivative (f : Equation) : Equation :=
  MvPolynomial.optionEquivLeft FX (Fin 2) (partialX (flatten f))
def jetCoeffDerivative (δ : Equation → Equation) (P : JetRing) : JetRing :=
  P.sum fun k q => Polynomial.monomial k (δ q)
abbrev jetSeparant (f : Equation) : JetRing := Polynomial.C f.derivative
def secondAlongVelocity (f : Equation) : JetRing :=
  Polynomial.C (coefficientDerivative (coefficientDerivative f)) +
    2 * velocity * Polynomial.C (coefficientDerivative f.derivative) +
    velocity ^ 2 * Polynomial.C f.derivative.derivative
def velocityNumerator (f : Equation) : ℕ → JetRing
  | 0 => velocity
  | k+1 =>
    let N := velocityNumerator f k
    jetSeparant f * (jetCoeffDerivative coefficientDerivative N +
      velocity * jetCoeffDerivative Polynomial.derivative N) -
    secondAlongVelocity f * N.derivative -
    (k : JetRing) *
      (Polynomial.C (coefficientDerivative f.derivative) +
        velocity * Polynomial.C f.derivative.derivative) * N
def pureDen (J : Input) (r : ℕ) : JetRing :=
  jetSeparant J.f ^ (r-1)
def pureOrdinate (J : Input) (r : ℕ) : ℕ → JetRing
  | 0 => pureDen J r * ordinate
  | k+1 => algebraMap FX JetRing (((k+1).factorial : FX)⁻¹) *
      (jetSeparant J.f ^ (r-1-k) * velocityNumerator J.f k)
def pureDegree (J : Input) (r : ℕ) : Degree :=
  ((jetDegree J r).1, r, r*J.v)
def FiniteLift (d : Degree) (q : JetRing) : Prop :=
  ∃ n : ℕ, ∃ A : Cox,
    A.IsWeightedHomogeneous coxWeight (d + n • (1,0,0)) ∧ dehom A = q
def InverseLift (Q : Ideal JetRing) (d : Degree) (q : JetRing) : Prop :=
  ∃ n : ℕ, ∃ A : Cox,
    A.IsWeightedHomogeneous coxWeight (d + n • (1,0,0)) ∧
    ordinate ^ n * q - dehom A ∈ Q
def Represented (Q : Ideal JetRing) (d : Degree) (q : JetRing) : Prop :=
  ∃ S : RelativeSection Q d, S.affine = q
end
end HighCore82706Tangent_3_1
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_1
noncomputable section
open HighCore82706Tangent_3 (JetRing Degree Cox coxWeight dehom ordinate
  RelativeSection h₀ h₁ v₀ tᵢ affineCoord)
open K1_14 (FX)
open MvPolynomial (IsWeightedHomogeneous isWeightedHomogeneous_zero
  isWeightedHomogeneous_X)
open scoped BigOperators
local notation "H" => ((1,0,0) : Degree)
local notation "cx" => MvPolynomial.X
private theorem dehom_h₀ : dehom (cx h₀) = 1 := by simp [dehom, affineCoord, h₀]
private theorem dehom_h₁ : dehom (cx h₁) = ordinate := by simp [dehom, affineCoord, h₁]
private theorem dehom_v₀ : dehom (cx v₀) = 1 := by simp [dehom, affineCoord, v₀]
private theorem dehom_t₂ : dehom (cx (tᵢ 2)) = 1 := by simp [dehom, affineCoord, tᵢ]
private theorem shift_degree {A : Cox} {d : Degree} {n : ℕ}
    (hA : A.IsWeightedHomogeneous coxWeight (d + n • H))
    {i : HighCore82706Tangent_3.CoxVar} (hi : coxWeight i = H) (k : ℕ) :
    (cx i ^ k * A).IsWeightedHomogeneous coxWeight (d + (n+k) • H) := by
  simpa only [hi, add_nsmul, add_assoc, add_comm, add_left_comm] using
    ((isWeightedHomogeneous_X FX coxWeight i).pow k).mul hA
private theorem shift_glue {Q : Ideal JetRing} {q a : JetRing} {n : ℕ}
    (h : ordinate^n * q - a ∈ Q) (k : ℕ) :
    ordinate^(n+k) * q - ordinate^k * a ∈ Q := by
  rw [pow_add, show ordinate^n * ordinate^k * q - ordinate^k * a =
    ordinate^k * (ordinate^n * q - a) by ring]
  exact Q.mul_mem_left _ h
theorem represented_of_charts {Q : Ideal JetRing} {d : Degree} {q : JetRing}
    (hf : FiniteLift d q) (hi : InverseLift Q d q) : Represented Q d q := by
  obtain ⟨n, A, hA, evA⟩ := hf
  obtain ⟨m, B, hB, evB⟩ := hi
  refine ⟨⟨n+m, cx h₀ ^ m * A, cx h₁ ^ n * B, shift_degree hA rfl m, ?_, ?_⟩, ?_⟩
  · rw [Nat.add_comm]
    exact shift_degree hB rfl n
  · simp only [map_mul, map_pow, dehom_h₀, dehom_h₁, one_pow, one_mul, evA]
    rw [Nat.add_comm]
    exact shift_glue evB n
  · simp only [RelativeSection.affine, map_mul, map_pow, dehom_h₀, one_pow, one_mul, evA]
private def shiftOrder {Q : Ideal JetRing} {d : Degree} (S : RelativeSection Q d)
    (k : ℕ) : RelativeSection Q d where
  order := S.order + k
  finiteChart := cx h₀ ^ k * S.finiteChart
  inverseChart := cx h₁ ^ k * S.inverseChart
  finite_degree := shift_degree S.finite_degree rfl k
  inverse_degree := shift_degree S.inverse_degree rfl k
  glue := by
    simpa only [map_mul, map_pow, dehom_h₀, dehom_h₁, one_pow, one_mul] using
      shift_glue S.glue k
private theorem shiftOrder_affine {Q : Ideal JetRing} {d : Degree}
    (S : RelativeSection Q d) (k : ℕ) : (shiftOrder S k).affine = S.affine := by
  simp only [shiftOrder, RelativeSection.affine, map_mul, map_pow, dehom_h₀, one_pow, one_mul]
theorem represented_homogeneous {Q : Ideal JetRing} {d : Degree} {A : Cox}
    (hA : A.IsWeightedHomogeneous coxWeight d) : Represented Q d (dehom A) := by
  refine ⟨⟨0, A, A, ?_, ?_, ?_⟩, rfl⟩
  · simpa only [zero_nsmul, add_zero] using hA
  · simpa only [zero_nsmul, add_zero] using hA
  · simp
theorem represented_zero (Q : Ideal JetRing) (d : Degree) : Represented Q d 0 := by
  simpa only [map_zero] using
    (represented_homogeneous (Q := Q) (isWeightedHomogeneous_zero FX coxWeight d))
theorem represented_one (Q : Ideal JetRing) (d : Degree) : Represented Q d 1 := by
  rcases d with ⟨a, b, c⟩
  have h := (((isWeightedHomogeneous_X FX coxWeight h₀).pow a).mul
    ((isWeightedHomogeneous_X FX coxWeight v₀).pow b)).mul
    ((isWeightedHomogeneous_X FX coxWeight (tᵢ 2)).pow c)
  have hd : (cx h₀ ^ a * cx v₀ ^ b * cx (tᵢ 2) ^ c : Cox).IsWeightedHomogeneous
      coxWeight (a,b,c) := by
    simpa [coxWeight, h₀, v₀, tᵢ, Prod.smul_mk, Prod.mk_add_mk] using h
  simpa only [map_mul, map_pow, dehom_h₀, dehom_v₀, dehom_t₂, one_pow, one_mul] using
    (represented_homogeneous (Q := Q) hd)
theorem represented_ordinate (Q : Ideal JetRing) : Represented Q H ordinate := by
  rw [← dehom_h₁]
  exact represented_homogeneous (isWeightedHomogeneous_X FX coxWeight h₁)
theorem represented_mul {Q : Ideal JetRing} {a b : Degree} {q r : JetRing}
    (hq : Represented Q a q) (hr : Represented Q b r) : Represented Q (a+b) (q*r) := by
  obtain ⟨S, hS⟩ := hq
  obtain ⟨T, hT⟩ := hr
  have hd : (a + S.order • H) + (b + T.order • H) = (a+b) + (S.order+T.order) • H := by
    rw [add_nsmul]
    ac_rfl
  refine ⟨⟨S.order+T.order, S.finiteChart*T.finiteChart, S.inverseChart*T.inverseChart,
    hd ▸ S.finite_degree.mul T.finite_degree, hd ▸ S.inverse_degree.mul T.inverse_degree, ?_⟩, ?_⟩
  · simp only [map_mul, pow_add]
    have he :
        (ordinate^S.order * ordinate^T.order) * (dehom S.finiteChart * dehom T.finiteChart) -
          dehom S.inverseChart * dehom T.inverseChart =
        (S.affine * ordinate^S.order - dehom S.inverseChart) * (ordinate^T.order * T.affine) +
          dehom S.inverseChart * (ordinate^T.order * T.affine - dehom T.inverseChart) := by
      simp only [RelativeSection.affine]
      ring
    rw [he, mul_comm S.affine]
    exact Q.add_mem (Q.mul_mem_right _ S.glue) (Q.mul_mem_left _ T.glue)
  · simpa only [RelativeSection.affine, map_mul] using congrArg₂ (· * ·) hS hT
theorem represented_pow {Q : Ideal JetRing} {d : Degree} {q : JetRing}
    (hq : Represented Q d q) (n : ℕ) : Represented Q (n • d) (q^n) := by
  induction n with
  | zero => simpa only [zero_nsmul, pow_zero] using represented_one Q 0
  | succ n ih => simpa only [succ_nsmul, pow_succ] using represented_mul ih hq
theorem represented_add {Q : Ideal JetRing} {d : Degree} {q r : JetRing}
    (hq : Represented Q d q) (hr : Represented Q d r) : Represented Q d (q+r) := by
  obtain ⟨S, hS⟩ := hq
  obtain ⟨T, hT⟩ := hr
  let A := shiftOrder S T.order
  let B := shiftOrder T S.order
  have ho : B.order = A.order := Nat.add_comm _ _
  refine ⟨⟨A.order, A.finiteChart+B.finiteChart, A.inverseChart+B.inverseChart,
    A.finite_degree.add (ho ▸ B.finite_degree), A.inverse_degree.add (ho ▸ B.inverse_degree),
    ?_⟩, ?_⟩
  · simp only [map_add, mul_add, add_sub_add_comm]
    exact Q.add_mem A.glue (ho ▸ B.glue)
  · change dehom (A.finiteChart + B.finiteChart) = _
    rw [map_add, ← show A.affine = dehom A.finiteChart from rfl,
      ← show B.affine = dehom B.finiteChart from rfl, shiftOrder_affine, shiftOrder_affine, hS, hT]
theorem represented_neg {Q : Ideal JetRing} {d : Degree} {q : JetRing}
    (hq : Represented Q d q) : Represented Q d (-q) := by
  obtain ⟨S, hS⟩ := hq
  refine ⟨⟨S.order, -S.finiteChart, -S.inverseChart, S.finite_degree.neg,
    S.inverse_degree.neg, ?_⟩, ?_⟩
  · simpa only [map_neg, mul_neg, neg_sub_neg, neg_sub] using Q.neg_mem S.glue
  · simpa only [RelativeSection.affine, map_neg] using congrArg Neg.neg hS
theorem represented_sub {Q : Ideal JetRing} {d : Degree} {q r : JetRing}
    (hq : Represented Q d q) (hr : Represented Q d r) : Represented Q d (q-r) := by
  simpa only [sub_eq_add_neg] using represented_add hq (represented_neg hr)
theorem represented_sum {ι : Type*} {Q : Ideal JetRing} {d : Degree}
    {f : ι → JetRing} {s : Finset ι} (hf : ∀ i ∈ s, Represented Q d (f i)) :
    Represented Q d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using represented_zero Q d
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact represented_add (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
theorem represented_smul {Q : Ideal JetRing} {d : Degree} {q : JetRing} (z : FX)
    (hq : Represented Q d q) : Represented Q d (algebraMap FX JetRing z * q) := by
  have hC := represented_homogeneous (Q := Q)
    (MvPolynomial.isWeightedHomogeneous_C coxWeight z)
  have ev : dehom (MvPolynomial.C z) = algebraMap FX JetRing z := by simp [dehom]
  rw [ev] at hC
  simpa only [zero_add] using represented_mul hC hq
theorem represented_pad {Q : Ideal JetRing} {d e : Degree} {q : JetRing}
    (hq : Represented Q d q) : Represented Q (d+e) q := by
  simpa only [mul_one] using represented_mul hq (represented_one Q e)
end
end HighCore82706Tangent_3_1
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_1
noncomputable section
open HighCore82706Tangent (Input ResidueLift Factors SeedConstants seedBiform liftTaylor)
open HighCore82706Tangent_3 (JetRing Degree Cox coxWeight dehom ordinate rootInJet graphIdeal
  homogenizeBiform proper_mem_graph jetDegree residueInJet)
open K1_14 (FX Equation Seeds SeedBound)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant separant_bound box)
open MvPolynomial (mem_restrictBidegree optionEquivLeft)
open scoped BigOperators
open private K1_14_6_1.flatten_bound from ProximityPrize.SubmissionLower.Fast055
open HighCore82706Tangent_3 (inversePart inversePart_bound)
open HighCore82706Tangent_3 (seedBiform_image)
theorem embed_separant (f : Equation) :
    rootInJet (separant (flatten f)) = jetSeparant f := by
  simp only [separant, rootInJet, AlgHom.coe_comp, Function.comp_apply,
    AlgEquiv.coe_toAlgHom, MvPolynomial.optionEquivLeft_pderiv_none,
    AlgEquiv.apply_symm_apply]
  rfl
theorem embed_seedBiform (s : SeedConstants) :
    rootInJet (seedBiform s) = Polynomial.C (Polynomial.C (HighCore82706Tangent.liftSeeds s)) := by
  change Polynomial.C (optionEquivLeft FX (Fin 2) (seedBiform s)) = _
  rw [seedBiform_image]
private theorem separant_glue {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (y c e f : R) :
    φ y * φ c - φ (y*c-e*f) = φ e * φ f := by
  rw [map_sub, map_mul, map_mul]
  ring
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem represent_separant (J : Input) (B : ResidueLift J) (D : Factors J B) :
    Represented (graphIdeal J B D) (J.e-2,0,J.v) (jetSeparant J.f) := by
  have hn : J.e-2+1 = J.e-1 := by have hE : 3 ≤ J.e := J.sheets; omega
  have hd : ((J.e-2,0,J.v) : Degree) + (1 : ℕ) • (1,0,0) = (J.e-1,0,J.v) := by
    simp [Prod.mk_add_mk, hn]
  obtain ⟨A, hA, evA⟩ := homogenizeBiform (separant_bound (f := J.f) le_rfl J.seed_bound)
  obtain ⟨I, hI, evI⟩ := homogenizeBiform
    (K1_14_6_1.flatten_bound (inversePart_bound J).1 (inversePart_bound J).2)
  have hf : Polynomial.C J.f ∈ graphIdeal J B D := by
    rw [D.product, Polynomial.C_mul]
    exact (graphIdeal J B D).mul_mem_right _ (proper_mem_graph J B D)
  apply represented_of_charts
  · exact ⟨1, A, hd ▸ hA, evA.trans (embed_separant J.f)⟩
  · refine ⟨1, I, hd ▸ hI, ?_⟩
    have evI' : rootInJet (flatten (inversePart J)) = Polynomial.C (inversePart J) := by
      simp only [rootInJet, AlgHom.coe_comp, Function.comp_apply,
        AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
      rfl
    rw [pow_one, evI, evI']
    change ordinate * jetSeparant J.f -
      Polynomial.C (inversePart J) ∈ graphIdeal J B D
    have h :
        ordinate * jetSeparant J.f - Polynomial.C (inversePart J) =
          Polynomial.C (Polynomial.C (J.e : Seeds)) * Polynomial.C J.f := by
      exact @separant_glue Equation JetRing (@Polynomial.commRing Seeds inferInstance)
        HighCore82706Tangent_3.jetCommRing Polynomial.C Polynomial.X J.f.derivative
        (Polynomial.C (J.e : Seeds)) J.f
    rw [h]
    exact (graphIdeal J B D).mul_mem_left _ hf
private theorem pad_le {Q : Ideal JetRing} {d e : Degree} {q : JetRing}
    (hq : Represented Q d q)
    (ha : d.1 ≤ e.1) (hb : d.2.1 ≤ e.2.1) (hc : d.2.2 ≤ e.2.2) :
    Represented Q e q := by
  have hd : d + (e.1-d.1,e.2.1-d.2.1,e.2.2-d.2.2) = e :=
    Prod.ext (Nat.add_sub_of_le ha)
      (Prod.ext (Nat.add_sub_of_le hb) (Nat.add_sub_of_le hc))
  rw [← hd]
  exact represented_pad hq
private theorem root_degree (J : Input) (r : ℕ) :
    (pureDegree J r).1 = 1+r*(J.e-1) := by
  change 1+(J.e-3)*r+2*r = _
  have he : J.e-1 = (J.e-3)+2 := by have hE : 3 ≤ J.e := J.sheets; omega
  rw [he, Nat.mul_add, Nat.mul_comm r (J.e-3), Nat.mul_comm r 2, Nat.add_assoc]
private theorem sep_room (J : Input) (r : ℕ) :
    (r-1)*(J.e-2) ≤ r*(J.e-1) :=
  Nat.mul_le_mul (Nat.sub_le r 1) (Nat.sub_le_sub_left (by decide : 1 ≤ 2) J.e)
theorem represent_pureDen (J : Input) (B : ResidueLift J) (D : Factors J B) (r : ℕ) :
    Represented (graphIdeal J B D) (pureDegree J r) (pureDen J r) := by
  have h := represented_pow (represent_separant J B D) (r-1)
  refine pad_le h ?_ ?_ ?_
  · rw [root_degree]
    change (r-1)*(J.e-2) ≤ _
    have := sep_room J r
    omega
  · change (r-1)*0 ≤ r
    simp
  · change (r-1)*J.v ≤ r*J.v
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
theorem represent_pureOrdinate_zero (J : Input) (B : ResidueLift J)
    (D : Factors J B) (r : ℕ) :
    Represented (graphIdeal J B D) (pureDegree J r) (pureOrdinate J r 0) := by
  have h := represented_mul (represented_pow (represent_separant J B D) (r-1))
    (represented_ordinate (graphIdeal J B D))
  refine pad_le h ?_ ?_ ?_
  · rw [root_degree]
    change (r-1)*(J.e-2)+1 ≤ _
    have := sep_room J r
    omega
  · change (r-1)*0+0 ≤ r
    simp
  · change (r-1)*J.v+0 ≤ r*J.v
    rw [add_zero]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem seedBiform_box {s : SeedConstants} {c : ℕ} (hc : s.totalDegree ≤ c) :
    seedBiform s ∈ box 0 c := by
  have hF : flatten (Polynomial.C (HighCore82706Tangent.liftSeeds s)) = seedBiform s := by
    apply (optionEquivLeft FX (Fin 2)).injective
    rw [AlgEquiv.apply_symm_apply, seedBiform_image]
  rw [← hF]
  apply K1_14_6_1.flatten_bound (Polynomial.natDegree_C _).le
  intro i
  by_cases hi : i = 0
  · subst i
    rw [Polynomial.coeff_C_zero]
    have hs : (MvPolynomial.map HighCore82706Tangent.constantAbscissa s).totalDegree ≤ s.totalDegree :=
      Finset.sup_mono (MvPolynomial.support_map_subset HighCore82706Tangent.constantAbscissa s)
    exact hs.trans hc
  · rw [Polynomial.coeff_C_of_ne_zero hi, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
private theorem liftTaylor_box (J : Input) (B : ResidueLift J) (i : ℕ) :
    liftTaylor B.numerator i ∈ box 0 (2*J.w) := by
  rw [liftTaylor, Polynomial.taylor_coeff, Polynomial.hasseDeriv_apply,
    Polynomial.sum_def, Polynomial.eval_finsetSum]
  apply (box 0 (2*J.w)).sum_mem
  intro k _
  rw [Polynomial.eval_monomial, Polynomial.coeff_map]
  have hterm :
      (k.choose i : Biform) * seedBiform (B.numerator.coeff k) *
          MvPolynomial.C HighCore82706Tangent.center ^ (k-i) =
        ((k.choose i : FX) * HighCore82706Tangent.center ^ (k-i)) •
          seedBiform (B.numerator.coeff k) := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, map_pow, map_natCast]
    ring
  rw [hterm]
  exact (box 0 (2*J.w)).smul_mem _ (seedBiform_box (B.numerator_degree k))
theorem represent_crtDen (J : Input) (B : ResidueLift J) (D : Factors J B) :
    Represented (graphIdeal J B D) (0,0,2*J.w) (residueInJet B) := by
  obtain ⟨A, hA, evA⟩ := homogenizeBiform (seedBiform_box B.denominator_degree)
  rw [embed_seedBiform] at evA
  rw [← show dehom A = residueInJet B from evA]
  exact represented_homogeneous hA
theorem represent_crtTaylor (J : Input) (B : ResidueLift J) (D : Factors J B)
    (i : ℕ) :
    Represented (graphIdeal J B D) (0,0,2*J.w) (rootInJet (liftTaylor B.numerator i)) := by
  obtain ⟨A, hA, evA⟩ := homogenizeBiform (liftTaylor_box J B i)
  rw [← evA]
  exact represented_homogeneous hA
end
end HighCore82706Tangent_3_1
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_1
noncomputable section
open K1_14 (FX Seeds Equation SeedBound)
open K1_14_6_1 (flatten partialX box)
open HighCore82706Tangent (Input)
open HighCore82706Tangent_3 (JetRing Cox Degree coxWeight dehom v₀ v₁ affineCoord
  rootInJet homogenizeBiform)
open MvPolynomial (mem_restrictBidegree isWeightedHomogeneous_X)
open scoped BigOperators
open private K1_14_6_1.flatten_bound K1_14_6_1.partialX_bound from ProximityPrize.SubmissionLower.Fast055
private def Bounded (P : JetRing) (v s : ℕ) : Prop :=
  P.natDegree ≤ v ∧ ∀ j, SeedBound (P.coeff j) s
private theorem seedBound_zero (s : ℕ) : SeedBound 0 s := by
  intro i
  simp
private theorem seedBound_scalar (x : FX) : SeedBound (Polynomial.C (MvPolynomial.C x)) 0 := by
  intro i
  by_cases hi : i = 0
  · simp [hi]
  · simp [Polynomial.coeff_C_of_ne_zero hi]
private theorem seedBound_mul {A B : Equation} {a b : ℕ}
    (hA : SeedBound A a) (hB : SeedBound B b) : SeedBound (A*B) (a+b) := by
  intro i
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hA j.1) (hB j.2))
private theorem seedBound_derivative {A : Equation} {a : ℕ} (hA : SeedBound A a) :
    SeedBound A.derivative a := by
  intro i
  rw [Polynomial.coeff_derivative]
  have E : (↑i+1 : Seeds) = MvPolynomial.C ((i : FX)+1) := by
    simp only [map_add, map_one, map_natCast]
  rw [E]
  exact (MvPolynomial.totalDegree_mul (A.coeff (i+1))
    (MvPolynomial.C ((i : FX)+1))).trans
    (by simpa only [MvPolynomial.totalDegree_C, Nat.add_zero] using hA (i+1))
private theorem seedBound_coeffDiff {A : Equation} {a : ℕ} (hA : SeedBound A a) :
    SeedBound (coefficientDerivative A) a := by
  have h := mem_restrictBidegree.mp (K1_14_6_1.partialX_bound (K1_14_6_1.flatten_bound le_rfl hA))
  intro j
  apply Finset.sup_le
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  let n := Finsupp.optionElim j m
  have he := MvPolynomial.optionEquivLeft_coeff_coeff FX (partialX (flatten A)) j m
  have hn : n ∈ (partialX (flatten A)).support := by
    rw [MvPolynomial.mem_support_iff, ← he]
    exact hm
  have hseed := (h n hn).2
  change n.some.sum (fun _ i => i) ≤ a at hseed
  simpa only [n, Finsupp.some_optionElim] using hseed
private theorem Bounded.mono {P : JetRing} {v s v' s' : ℕ}
    (hP : Bounded P v s) (hv : v ≤ v') (hs : s ≤ s') : Bounded P v' s' :=
  ⟨hP.1.trans hv, fun j i => (hP.2 j i).trans hs⟩
private theorem Bounded.C {P : Equation} {s : ℕ} (hP : SeedBound P s) :
    Bounded (Polynomial.C P) 0 s := by
  refine ⟨(Polynomial.natDegree_C _).le, fun j => ?_⟩
  by_cases hj : j = 0
  · subst j
    simpa only [Polynomial.coeff_C_zero] using hP
  · rw [Polynomial.coeff_C_of_ne_zero hj]
    exact seedBound_zero s
private theorem Bounded.scalar (x : FX) : Bounded (algebraMap FX JetRing x) 0 0 :=
  Bounded.C (seedBound_scalar x)
private theorem Bounded.nat (k : ℕ) : Bounded (k : JetRing) 0 0 := by
  rw [← map_natCast (algebraMap FX JetRing)]
  exact Bounded.scalar (k : FX)
private theorem Bounded.velocity : Bounded velocity 1 0 := by
  refine ⟨Polynomial.natDegree_X.le, fun j => ?_⟩
  by_cases hj : j = 1
  · subst j
    rw [Polynomial.coeff_X_one]
    simpa only [map_one] using seedBound_scalar (1 : FX)
  · rw [Polynomial.coeff_X_of_ne_one hj]
    exact seedBound_zero 0
private theorem Bounded.add {P Q : JetRing} {v s : ℕ}
    (hP : Bounded P v s) (hQ : Bounded Q v s) : Bounded (P+Q) v s := by
  refine ⟨?_, fun j i => ?_⟩
  · simpa only [max_self] using Polynomial.natDegree_add_le_of_le hP.1 hQ.1
  · rw [Polynomial.coeff_add, Polynomial.coeff_add]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hP.2 j i) (hQ.2 j i))
private theorem Bounded.mul {P Q : JetRing} {v w s t : ℕ}
    (hP : Bounded P v s) (hQ : Bounded Q w t) : Bounded (P*Q) (v+w) (s+t) := by
  refine ⟨Polynomial.natDegree_mul_le_of_le hP.1 hQ.1, fun j i => ?_⟩
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  exact MvPolynomial.totalDegree_finsetSum_le fun k _ =>
    seedBound_mul (hP.2 k.1) (hQ.2 k.2) i
private theorem Bounded.neg {P : JetRing} {v s : ℕ} (hP : Bounded P v s) :
    Bounded (-P) v s := by
  simpa only [map_neg, map_one, neg_one_mul, Nat.zero_add] using
    (Bounded.scalar (-1 : FX)).mul hP
private theorem Bounded.sub {P Q : JetRing} {v s : ℕ}
    (hP : Bounded P v s) (hQ : Bounded Q v s) : Bounded (P-Q) v s := by
  rw [sub_eq_add_neg]
  exact hP.add hQ.neg
private theorem Bounded.pow {P : JetRing} {v s : ℕ} (hP : Bounded P v s) (n : ℕ) :
    Bounded (P^n) (n*v) (n*s) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.zero_mul, Nat.cast_one] using Bounded.nat 1
  | succ n ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul hP
private theorem Bounded.derivative {P : JetRing} {v s : ℕ} (hP : Bounded P v s) :
    Bounded P.derivative (v-1) s := by
  refine ⟨(Polynomial.natDegree_derivative_le _).trans (Nat.sub_le_sub_right hP.1 _),
    fun j => ?_⟩
  rw [Polynomial.coeff_derivative]
  rw [← map_natCast (Polynomial.C : Seeds →+* Equation), ← map_natCast (MvPolynomial.C : FX →+* Seeds)]
  simpa only [Nat.add_zero, map_add, map_one] using seedBound_mul (hP.2 (j+1)) (seedBound_scalar (j+1))
private theorem Bounded.coeffDiff {P : JetRing} {v s : ℕ} (hP : Bounded P v s)
    {δ : Equation → Equation} (h0 : δ 0 = 0)
    (hδ : ∀ A, SeedBound A s → SeedBound (δ A) s) :
    Bounded (jetCoeffDerivative δ P) v s := by
  have hc (k : ℕ) : (jetCoeffDerivative δ P).coeff k = δ (P.coeff k) := by
    rw [jetCoeffDerivative, Polynomial.sum_def, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single k]
    · exact Polynomial.coeff_monomial_same _ _
    · exact fun j _ hj => Polynomial.coeff_monomial_of_ne _ hj.symm
    · intro hk
      rw [Polynomial.notMem_support_iff.mp hk, h0, Polynomial.monomial_zero_right, Polynomial.coeff_zero]
  refine ⟨Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => ?_), fun k => ?_⟩
  · rw [hc, Polynomial.coeff_eq_zero_of_natDegree_lt (hP.1.trans_lt hk), h0]
  · rw [hc]
    exact hδ _ (hP.2 k)
private theorem coefficientDerivative_zero : coefficientDerivative 0 = 0 := by
  simp [coefficientDerivative, map_zero]
private theorem second_bound {f : Equation} {s : ℕ} (hf : SeedBound f s) :
    Bounded (secondAlongVelocity f) 2 s := by
  have hx := Bounded.C (seedBound_coeffDiff (seedBound_coeffDiff hf))
  have hxy := Bounded.C (seedBound_coeffDiff (seedBound_derivative hf))
  have hyy := Bounded.C (seedBound_derivative (seedBound_derivative hf))
  have h1 : Bounded (2 * velocity * Polynomial.C (coefficientDerivative f.derivative)) 1 s := by
    simpa only [Nat.cast_ofNat, Nat.zero_add, Nat.add_zero] using
      ((Bounded.nat 2).mul Bounded.velocity).mul hxy
  have h2 : Bounded (velocity ^ 2 * Polynomial.C f.derivative.derivative) 2 s := by
    simpa only [Nat.mul_one, Nat.mul_zero, Nat.zero_add, Nat.add_zero] using
      (Bounded.velocity.pow 2).mul hyy
  exact ((hx.mono (by omega) le_rfl).add (h1.mono (by omega) le_rfl)).add h2
private theorem numerator_bound {f : Equation} {s : ℕ} (hf : SeedBound f s) (k : ℕ) :
    Bounded (velocityNumerator f k) (k+1) (k*s) := by
  have hsep := Bounded.C (seedBound_derivative hf)
  have hxx := second_bound hf
  have hxy := Bounded.C (seedBound_coeffDiff (seedBound_derivative hf))
  have hyy := Bounded.C (seedBound_derivative (seedBound_derivative hf))
  induction k with
  | zero => simpa only [velocityNumerator, Nat.zero_mul, Nat.zero_add] using Bounded.velocity
  | succ k ih =>
    have h1 := ih.coeffDiff coefficientDerivative_zero (fun _ h => seedBound_coeffDiff h)
    have h2 := ih.coeffDiff (Polynomial.derivative_zero (R := Seeds))
      (fun _ h => seedBound_derivative h)
    have hsum : Bounded (jetCoeffDerivative coefficientDerivative (velocityNumerator f k) +
        velocity * jetCoeffDerivative Polynomial.derivative (velocityNumerator f k)) (k+2) (k*s) := by
      apply (h1.mono (Nat.le_succ _) le_rfl).add
      simpa only [Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Bounded.velocity.mul h2
    have h3 := hsep.mul hsum
    have h4 := hxx.mul ih.derivative
    have hs : Bounded (Polynomial.C (coefficientDerivative f.derivative) +
        velocity * Polynomial.C f.derivative.derivative) 1 s := by
      apply (hxy.mono (by omega) le_rfl).add
      simpa only [Nat.add_zero, Nat.zero_add] using Bounded.velocity.mul hyy
    have h5 := ((Bounded.nat k).mul hs).mul ih
    have e : s + k*s = (k+1)*s := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [velocityNumerator]
    apply Bounded.sub (Bounded.sub ?_ ?_) ?_
    · simpa only [Nat.zero_add, e] using h3
    · simpa only [Nat.add_sub_cancel, Nat.add_comm 2 k, e] using h4
    · simpa only [Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, ← e] using h5
private theorem pureOrdinate_bound (J : Input) {r k : ℕ} (hk : k+1 ≤ r) :
    Bounded (pureOrdinate J r (k+1)) r (r*J.v) := by
  have hsep := Bounded.C (seedBound_derivative J.seed_bound)
  have hN := numerator_bound J.seed_bound k
  have h := (Bounded.scalar (((k+1).factorial : FX)⁻¹)).mul ((hsep.pow (r-1-k)).mul hN)
  have e : (r-1-k)*J.v + k*J.v = (r-1)*J.v := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega : k ≤ r-1)]
  apply h.mono
  · simpa only [Nat.mul_zero, Nat.zero_add] using hk
  · simpa only [Nat.zero_add, e] using Nat.mul_le_mul_right J.v (Nat.sub_le r 1)
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem Bounded.finiteLift {P : JetRing} {a b c : ℕ} (hP : Bounded P b c) :
    FiniteLift (a,b,c) P := by
  classical
  let L := P.support.sup fun j => (P.coeff j).natDegree
  let n := 2*b+L
  have hj (j : ℕ) (hm : j ∈ P.support) : j ≤ b :=
    (Polynomial.le_natDegree_of_mem_supp j hm).trans hP.1
  have hroot (j : ℕ) : (P.coeff j).natDegree ≤ a+n-2*j := by
    by_cases hm : j ∈ P.support
    · have hL : (P.coeff j).natDegree ≤ L :=
        Finset.le_sup (f := fun k => (P.coeff k).natDegree) hm
      have hb := hj j hm
      dsimp [n]
      omega
    · rw [Polynomial.notMem_support_iff.mp hm, Polynomial.natDegree_zero]
      exact Nat.zero_le _
  have hLift (j : ℕ) := homogenizeBiform (K1_14_6_1.flatten_bound (hroot j) (hP.2 j))
  choose A hA evA using hLift
  let E (j : ℕ) : Cox := MvPolynomial.X v₀ ^ (b-j) * MvPolynomial.X v₁ ^ j * A j
  refine ⟨n, ∑ j ∈ P.support, E j, ?_, ?_⟩
  · apply MvPolynomial.IsWeightedHomogeneous.sum
    intro j hm
    have hv := ((isWeightedHomogeneous_X FX coxWeight v₀).pow (b-j)).mul
      ((isWeightedHomogeneous_X FX coxWeight v₁).pow j)
    have hb := hj j hm
    have hroot' : 2*j+(a+n-2*j) = a+n := by dsimp [n]; omega
    simpa [E, coxWeight, v₀, v₁, Prod.smul_mk, Prod.mk_add_mk, Nat.mul_comm j 2,
      Nat.sub_add_cancel hb, hroot'] using hv.mul (hA j)
  · have e0 : dehom (MvPolynomial.X v₀) = 1 := by simp [dehom, affineCoord, v₀]
    have e1 : dehom (MvPolynomial.X v₁) = HighCore82706Tangent_3_1.velocity := by
      simp [dehom, affineCoord, v₁]
    rw [map_sum]
    refine Eq.trans ?_ (P.sum_monomial_eq)
    rw [Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro j _
    simp only [E, map_mul, map_pow, e0, e1, one_pow, one_mul, evA]
    have ev : rootInJet (flatten (P.coeff j)) = Polynomial.C (P.coeff j) := by
      simp only [rootInJet, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
        AlgEquiv.apply_symm_apply]
      rfl
    rw [ev, mul_comm]
    exact Polynomial.C_mul_X_pow_eq_monomial
theorem finite_ordinate (J : Input) (r k : ℕ) (hk : k+1 ≤ r) :
    FiniteLift (pureDegree J r) (pureOrdinate J r (k+1)) :=
  (pureOrdinate_bound J hk).finiteLift
end
end HighCore82706Tangent_3_1
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_1
noncomputable section
open HighCore82706Tangent (Input ResidueLift Factors liftTaylor inverseBlockCoeff ordinateTaylorNum)
open HighCore82706Tangent_3 (JetRing Degree rootInJet ordinate graphIdeal jetDegree jetDenominator
  oldNumerator oldDenominator residueInJet TaylorSections RelativeSection)
open K1_14 (FX)
open K1_14_6_1 (flatten separant cleared)
open Finset (range)
open scoped BigOperators
open HighCore82706Tangent_3 (oldDenominator_eq)
def c1 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B) (k : ℕ),
    k+1 ≤ J.ell+1 →
    jetSeparant J.f ^ (2*k+1) * velocityNumerator J.f k -
      rootInJet (cleared (flatten J.f) k) * jetSeparant J.f ^ k ∈ graphIdeal J B D
def c2 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B) (r k : ℕ),
    k+1 ≤ r → r ≤ J.ell+1 →
    InverseLift (graphIdeal J B D) (pureDegree J r) (pureOrdinate J r (k+1))
private theorem embed_C (a : FX) :
    rootInJet (MvPolynomial.C a) = algebraMap FX JetRing a := by
  exact rootInJet.commutes a
private theorem full_degree (J : Input) (r : ℕ) :
    pureDegree J r + (0,0,2*J.w) = jetDegree J r := by
  simp only [pureDegree, jetDegree, HighCore82706Tangent_3.nefDegree, Prod.mk_add_mk, add_zero]
private def shortQuotient (J : Input) (B : ResidueLift J) (r j : ℕ) : JetRing :=
  ∑ i ∈ range (j+1), algebraMap FX JetRing (inverseBlockCoeff J (j-i)) *
    (residueInJet B * pureOrdinate J r i - pureDen J r * rootInJet (liftTaylor B.numerator i))
private theorem represent_quotient (hInv : c2)
    (J : Input) (B : ResidueLift J) (D : Factors J B) {r j : ℕ}
    (hj : j ≤ r) (hr : r ≤ J.ell+1) :
    Represented (graphIdeal J B D) (jetDegree J r) (shortQuotient J B r j) := by
  have hD := represent_pureDen J B D r
  have hB := represent_crtDen J B D
  unfold shortQuotient
  apply represented_sum
  intro i hi
  have hir : i ≤ r := by
    have := Finset.mem_range.mp hi
    omega
  have hOrd : Represented (graphIdeal J B D) (pureDegree J r) (pureOrdinate J r i) := by
    cases i with
    | zero => exact represent_pureOrdinate_zero J B D r
    | succ k => exact represented_of_charts (finite_ordinate J r k hir) (hInv J B D r k hir hr)
  apply represented_smul
  apply represented_sub
  · rw [← full_degree, add_comm]
    exact represented_mul hB hOrd
  · rw [← full_degree]
    exact represented_mul hD (represent_crtTaylor J B D i)
private theorem comparison_of_powers {R : Type*} [CommRing R]
    (y z u v : R) {a b m n : ℕ} (ha : a ≤ m) (hb : b ≤ n)
    (h : y^b * u = v*y^a) :
    y^n * (z * (y^(m-a)*u)) = (z * (y^(n-b)*v)) * y^m := by
  have hm : y^(m-a) * y^a = y^m := by rw [← pow_add, Nat.sub_add_cancel ha]
  have hn : y^(n-b) * y^b = y^n := by rw [← pow_add, Nat.sub_add_cancel hb]
  calc
    y^n * (z * (y^(m-a)*u)) = z * y^(n-b) * y^(m-a) * (y^b * u) := by rw [← hn]; ring
    _ = (z * (y^(n-b)*v)) * y^m := by rw [h, ← hm]; ring
private theorem agree_ordinate (hCmp : c1)
    (J : Input) (B : ResidueLift J) (D : Factors J B) {r j i : ℕ}
    (hij : i ≤ j) (hjr : j ≤ r) (hr : r ≤ J.ell+1) :
    let φ := Ideal.Quotient.mk (graphIdeal J B D)
    φ (jetSeparant J.f ^ (2*j-1)) * φ (pureOrdinate J r i) =
      φ (rootInJet (ordinateTaylorNum J.f j i)) * φ (pureDen J r) := by
  let Q := graphIdeal J B D
  let φ := Ideal.Quotient.mk Q
  change φ _ * φ _ = φ _ * φ _
  cases i with
  | zero =>
    simp only [pureOrdinate, ordinateTaylorNum, map_mul, map_pow, embed_separant]
    rw [show rootInJet (MvPolynomial.X none) = ordinate by simp [rootInJet, ordinate]]
    ring
  | succ k =>
    have hk : k+1 ≤ J.ell+1 := hij.trans (hjr.trans hr)
    have h := Ideal.Quotient.eq.mpr (hCmp J B D k hk)
    simp only [map_mul, map_pow] at h
    simp only [pureOrdinate, pureDen, ordinateTaylorNum, map_mul, map_pow, embed_separant, embed_C]
    exact comparison_of_powers _ _ _ _ (by omega) (by omega) h
private theorem embed_oldNumerator (J : Input) (B : ResidueLift J) (j : ℕ) :
    oldNumerator J B j =
      ∑ i ∈ range (j+1), algebraMap FX JetRing (inverseBlockCoeff J (j-i)) *
        (residueInJet B * rootInJet (ordinateTaylorNum J.f j i) -
          jetSeparant J.f ^ (2*j-1) * rootInJet (liftTaylor B.numerator i)) := by
  change rootInJet (HighCore82706Tangent.quotientNumerator J B j) = _
  simp only [HighCore82706Tangent.quotientNumerator, map_sum, map_mul, map_sub, map_pow,
    embed_C, embed_seedBiform, embed_separant]
  rfl
private theorem crt_comparison {R : Type*} [CommRing R] (s t b l d u v : R)
    (h : s*u = v*d) :
    (b*s) * (t*(b*u-d*l)) = (t*(b*v-s*l)) * (b*d) := by
  linear_combination t*b^2*h
private theorem agree_quotient (hCmp : c1) (J : Input) (B : ResidueLift J)
    (D : Factors J B) {r j : ℕ} (hj : j ≤ r) (hr : r ≤ J.ell+1) :
    oldDenominator J B j * shortQuotient J B r j -
      oldNumerator J B j * jetDenominator J B r ∈ graphIdeal J B D := by
  apply Ideal.Quotient.eq.mp
  have hd : jetDenominator J B r = residueInJet B * pureDen J r := rfl
  rw [oldDenominator_eq, shortQuotient, embed_oldNumerator, hd]
  simp only [map_mul, map_sub, map_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
  apply crt_comparison
  exact agree_ordinate hCmp J B D hij hj hr
theorem of_children (hCmp : c1) (hInv : c2) : HighCore82706Tangent_3.c1 := by
  intro J B D r hr
  have hDen : Represented (graphIdeal J B D) (jetDegree J r) (jetDenominator J B r) := by
    rw [← full_degree]
    change Represented _ _ (residueInJet B * pureDen J r)
    rw [add_comm]
    exact represented_mul (represent_crtDen J B D) (represent_pureDen J B D r)
  obtain ⟨den, den_eq⟩ := hDen
  have hNum (j : Fin (r+1)) : Represented (graphIdeal J B D) (jetDegree J r)
      (shortQuotient J B r j.val) :=
    represent_quotient hInv J B D (by have := j.isLt; omega) hr
  choose nums nums_eq using hNum
  refine ⟨⟨den, nums, den_eq, ?_⟩⟩
  intro j
  rw [den_eq, nums_eq j]
  exact agree_quotient hCmp J B D (by have := j.isLt; omega) hr
end
end HighCore82706Tangent_3_1
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_1_2
noncomputable section
open HighCore82706Tangent (Input ResidueLift Factors)
open HighCore82706Tangent_3 (JetRing ordinate graphIdeal openFactor)
open HighCore82706Tangent_3_1 (velocity jetSeparant coefficientDerivative jetCoeffDerivative
  secondAlongVelocity)
open K1_14 (Equation Seeds)
open Polynomial (eval₂RingHom)
abbrev Graph (J : Input) (B : ResidueLift J) (D : Factors J B) :=
  JetRing ⧸ graphIdeal J B D
def overlapFactor (J : Input) (B : ResidueLift J) (D : Factors J B) : Graph J B D :=
  Ideal.Quotient.mk _ (ordinate * openFactor J B)
abbrev Overlap (J : Input) (B : ResidueLift J) (D : Factors J B) :=
  Localization.Away (overlapFactor J B D)
def finite (J : Input) (B : ResidueLift J) (D : Factors J B) : JetRing →+* Overlap J B D :=
  (algebraMap (Graph J B D) (Overlap J B D)).comp (Ideal.Quotient.mk _)
def reciprocal (J : Input) (B : ResidueLift J) (D : Factors J B) : Overlap J B D :=
  finite J B D (openFactor J B) * IsLocalization.Away.invSelf (overlapFactor J B D)
theorem mul_reciprocal (J : Input) (B : ResidueLift J) (D : Factors J B) :
    finite J B D ordinate * reciprocal J B D = 1 := by
  rw [reciprocal, ← mul_assoc, ← map_mul]
  exact IsLocalization.Away.mul_invSelf (overlapFactor J B D)
def seedMap {R : Type*} [CommRing R] (φ : JetRing →+* R) : Seeds →+* R :=
  (φ.comp Polynomial.C).comp Polynomial.C
def inverseEval {R : Type*} [CommRing R] (φ : JetRing →+* R) (z : R) : JetRing →+* R :=
  eval₂RingHom (eval₂RingHom (seedMap φ) z) (-(φ velocity * z^2))
abbrev inverse (J : Input) (B : ResidueLift J) (D : Factors J B) :
    JetRing →+* Overlap J B D :=
  inverseEval (finite J B D) (reciprocal J B D)
def reverseEquation (J : Input) : Equation := J.f.reflect J.e
def sepAlong (f : Equation) : JetRing :=
  Polynomial.C (coefficientDerivative f.derivative) +
    velocity * Polynomial.C f.derivative.derivative
def clearedAction (f : Equation) (N : JetRing) : JetRing :=
  jetSeparant f * (jetCoeffDerivative coefficientDerivative N +
    velocity * jetCoeffDerivative Polynomial.derivative N) -
  secondAlongVelocity f * N.derivative
abbrev ChartDerivation (R : Type*) [CommRing R] := Derivation ℤ R R
structure ChartFlow {R : Type*} [CommRing R] (f : Equation) (ev : JetRing →+* R)
    (δ : ChartDerivation R) : Prop where
  root : δ (ev ordinate) = ev velocity
  sep : δ (ev (jetSeparant f)) = ev (sepAlong f)
  action : ∀ N, ev (jetSeparant f) * δ (ev N) = ev (clearedAction f N)
def reciprocalNumerator (f : Equation) : ℕ → JetRing
  | 0 => -velocity
  | k+1 =>
    let N := reciprocalNumerator f k
    ordinate * (clearedAction f N - (k : JetRing) * sepAlong f * N) -
      ((k+2 : ℕ) : JetRing) * jetSeparant f * velocity * N
end
end HighCore82706Tangent_3_1_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_1_2
noncomputable section
open HighCore82706Tangent_3 (JetRing Degree Cox coxWeight dehom ordinate v₀ v₁ h₁ affineCoord
  rootInJet homogenizeBiform graphIdeal openFactor)
open HighCore82706Tangent_3_1 (velocity InverseLift)
open HighCore82706Tangent (Input ResidueLift Factors)
open K1_14 (FX Equation SeedBound)
open K1_14_6_1 (flatten)
open private K1_14_6_1.flatten_bound from ProximityPrize.SubmissionLower.Fast055
open scoped BigOperators
private theorem reflect_bound {q : Equation} {c : ℕ} (h : SeedBound q c) (N : ℕ) :
    SeedBound (q.reflect N) c := by
  intro i
  rw [Polynomial.coeff_reflect]
  exact h _
theorem reverse_seedBound (J : Input) : SeedBound (reverseEquation J) J.v :=
  reflect_bound J.seed_bound J.e
private theorem eval_coefficient {R : Type*} [CommRing R] (φ : JetRing →+* R) (q : Equation) :
    φ (Polynomial.C q) = q.eval₂ (seedMap φ) (φ ordinate) := by
  change (φ.comp Polynomial.C) q =
    q.eval₂ ((φ.comp Polynomial.C).comp Polynomial.C) ((φ.comp Polynomial.C) Polynomial.X)
  rw [← Polynomial.hom_eval₂, Polynomial.eval₂_C_X]
private theorem scale_velocity {R : Type*} [CommRing R] (y z v c : R) {d j : ℕ}
    (h : y*z = 1) (hj : 2*j ≤ d) :
    y^d * (c * (-(v*z^2))^j) = v^j * ((-1)^j * (c*y^(d-2*j))) := by
  have hy : y^d = y^(d-2*j)*y^(2*j) := by rw [← pow_add, Nat.sub_add_cancel hj]
  have hz : y^(2*j) * (z^2)^j = 1 := by rw [← pow_mul, ← mul_pow, h, one_pow]
  calc
    _ = v^j * ((-1)^j * (c*y^(d-2*j))) * (y^(2*j) * (z^2)^j) := by
      rw [hy, neg_eq_neg_one_mul, mul_pow, mul_pow v]
      ring
    _ = _ := by rw [hz, mul_one]
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem inverse_homogeneous {R : Type*} [CommRing R] (φ : JetRing →+* R) (z : R)
    (hz : φ ordinate * z = 1) {P : JetRing} {a b c : ℕ}
    (hvel : P.natDegree ≤ b) (hseed : ∀ j, SeedBound (P.coeff j) c) :
    ∃ n : ℕ, ∃ A : Cox,
      A.IsWeightedHomogeneous coxWeight ((a,b,c) + n • (1,0,0)) ∧
      φ (dehom A) = (φ ordinate)^(a+n) * inverseEval φ z P := by
  classical
  let y := φ ordinate
  let : Invertible y := ⟨z, by rw [mul_comm]; exact hz, hz⟩
  let n := 2*b + P.support.sup (fun j => (P.coeff j).natDegree)
  let N := fun j => a+n-2*j
  have hj (j : ℕ) (hm : j ∈ P.support) : j ≤ b :=
    (Polynomial.le_natDegree_of_mem_supp j hm).trans hvel
  have hr (j : ℕ) : (P.coeff j).natDegree ≤ N j := by
    by_cases hm : j ∈ P.support
    · have hL : (P.coeff j).natDegree ≤ P.support.sup (fun k => (P.coeff k).natDegree) :=
        Finset.le_sup (f := fun k => (P.coeff k).natDegree) hm
      have hb := hj j hm
      dsimp [N, n]
      omega
    · rw [Polynomial.notMem_support_iff.mp hm, Polynomial.natDegree_zero]
      exact Nat.zero_le _
  have hrev (j : ℕ) : ((P.coeff j).reflect (N j)).natDegree ≤ N j :=
    Polynomial.natDegree_reflect_le.trans (max_le le_rfl (hr j))
  have hL (j : ℕ) := homogenizeBiform (K1_14_6_1.flatten_bound (hrev j) (reflect_bound (hseed j) (N j)))
  choose A hA evA using hL
  let E (j : ℕ) : Cox := MvPolynomial.X v₀ ^ (b-j) * MvPolynomial.X v₁ ^ j *
    (MvPolynomial.C ((-1 : FX)^j) * A j)
  refine ⟨n, ∑ j ∈ P.support, E j, ?_, ?_⟩
  · apply MvPolynomial.IsWeightedHomogeneous.sum
    intro j hm
    have hv := ((MvPolynomial.isWeightedHomogeneous_X FX coxWeight v₀).pow (b-j)).mul
      ((MvPolynomial.isWeightedHomogeneous_X FX coxWeight v₁).pow j)
    have hb := hj j hm
    have he : 2*j+N j = a+n := by dsimp [N, n]; omega
    simpa [E, coxWeight, v₀, v₁, Prod.smul_mk, Prod.mk_add_mk, Nat.mul_comm j 2,
      Nat.sub_add_cancel hb, he] using hv.mul ((hA j).C_mul ((-1 : FX)^j))
  · have e0 : dehom (MvPolynomial.X v₀) = 1 := by simp [dehom, affineCoord, v₀]
    have e1 : dehom (MvPolynomial.X v₁) = velocity := by simp [dehom, affineCoord, v₁]
    have emb (q : Equation) : rootInJet (flatten q) = Polynomial.C q := by
      simp only [rootInJet, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
        AlgEquiv.apply_symm_apply]
      rfl
    rw [map_sum, map_sum]
    conv_rhs => rw [← P.sum_monomial_eq, Polynomial.sum_def, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hm
    have hv : 2*j ≤ a+n := by have hb := hj j hm; dsimp [n]; omega
    simp only [E, map_mul, map_pow, e0, e1, one_pow, one_mul,
      evA, emb, eval_coefficient φ, map_neg, map_one]
    change φ velocity ^ j * ((-1)^j * ((P.coeff j).reflect (N j)).eval₂ (seedMap φ) y) =
      y^(a+n) * (Polynomial.monomial j (P.coeff j)).eval₂
        (Polynomial.eval₂RingHom (seedMap φ) z) (-(φ velocity * z^2))
    rw [Polynomial.eval₂_monomial, Polynomial.coe_eval₂RingHom, scale_velocity y z (φ velocity)
      ((P.coeff j).eval₂ (seedMap φ) z) hz hv]
    have hm' := Polynomial.eval₂_reflect_mul_pow (seedMap φ) y (N j)
      ((P.coeff j).reflect (N j)) (hrev j)
    simp only [Polynomial.reflect_reflect] at hm'
    change (P.coeff j).eval₂ (seedMap φ) z * y^(N j) =
      ((P.coeff j).reflect (N j)).eval₂ (seedMap φ) y at hm'
    rw [← hm']
theorem clear_overlap (J : Input) (B : ResidueLift J) (D : Factors J B) {p : JetRing}
    (hp : finite J B D p = 0) : ∃ m : ℕ, ordinate^m * p ∈ graphIdeal J B D := by
  let Q := graphIdeal J B D
  let f := overlapFactor J B D
  obtain ⟨q, hq⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers f) (Overlap J B D) (Ideal.Quotient.mk Q p)).mp hp
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff (q : Graph J B D) f).mp q.2
  rw [← hm] at hq
  change (Ideal.Quotient.mk Q (ordinate * openFactor J B))^m * Ideal.Quotient.mk Q p = 0 at hq
  rw [← map_pow, ← map_mul] at hq
  have h : (ordinate * openFactor J B)^m * p ∈ Q := Ideal.Quotient.eq_zero_iff_mem.mp hq
  rw [mul_pow, mul_assoc, mul_left_comm] at h
  obtain ⟨l, hl⟩ := h
  rw [← mul_assoc, ← pow_add] at hl
  exact ⟨m, ⟨l+m, hl⟩⟩
theorem lift_of_overlap (J : Input) (B : ResidueLift J) (D : Factors J B)
    {d : Degree} {q : JetRing} {n : ℕ} {A : Cox}
    (hA : A.IsWeightedHomogeneous coxWeight (d + n • (1,0,0)))
    (h : finite J B D (ordinate^n * q - dehom A) = 0) :
    InverseLift (graphIdeal J B D) d q := by
  obtain ⟨m, hm⟩ := clear_overlap J B D h
  refine ⟨n+m, MvPolynomial.X h₁ ^ m * A, ?_, ?_⟩
  · have hu := ((MvPolynomial.isWeightedHomogeneous_X FX coxWeight h₁).pow m).mul hA
    simpa only [coxWeight, h₁, add_nsmul, add_assoc, add_comm, add_left_comm] using hu
  · have ev : dehom (MvPolynomial.X h₁) = ordinate := by simp [dehom, affineCoord, h₁]
    rw [map_mul, map_pow, ev, pow_add]
    convert hm using 1
    ring
end
end HighCore82706Tangent_3_1_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_1_2
noncomputable section
open HighCore82706Tangent_3 (JetRing ordinate)
open HighCore82706Tangent_3_1 (velocity jetSeparant coefficientDerivative jetCoeffDerivative
  velocityNumerator secondAlongVelocity)
open K1_14 (Equation SeedBound)
open HighCore82706Tangent_3_1 (Bounded seedBound_derivative seedBound_coeffDiff coefficientDerivative_zero second_bound)
open HighCore82706Tangent_3_1.Bounded (mono C nat velocity add mul neg sub derivative coeffDiff)
private theorem scaled_pow {R : Type*} [CommRing R] (δ : Derivation ℤ R R) (a : R)
    (n : ℕ) : a * δ (a^n) = (n : R) * δ a * a^n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [δ.leibniz_pow, Nat.succ_sub_one, pow_succ a n]
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
private theorem finite_step {R : Type*} [CommRing R] (δ : Derivation ℤ R R)
    (c t : R) (k : ℕ) :
    c * δ (c^k*t) - (k : R) * δ c * (c^k*t) = c^(k+1) * δ t := by
  simp only [δ.leibniz, smul_eq_mul, pow_succ c k]
  linear_combination t * scaled_pow δ c k
private theorem reciprocal_step {R : Type*} [CommRing R] (δ : Derivation ℤ R R)
    (z c t : R) (k : ℕ) :
    z * (c * δ (z^(k+2)*c^k*t) - (k : R) * δ c * (z^(k+2)*c^k*t)) -
        ((k+2 : ℕ) : R) * c * δ z * (z^(k+2)*c^k*t) =
      z^(k+3) * c^(k+1) * δ t := by
  change _ = z^((k+2)+1) * c^(k+1) * δ t
  simp only [δ.leibniz, smul_eq_mul, pow_succ z (k+2), pow_succ c k]
  linear_combination c * c^k * t * scaled_pow δ z (k+2) +
    z * z^(k+2) * t * scaled_pow δ c k
theorem finite_iterate {R : Type*} [CommRing R] {f : Equation} {ev : JetRing →+* R}
    {δ : Derivation ℤ R R} (h : ChartFlow f ev δ) (k : ℕ) :
    ev (velocityNumerator f k) = ev (jetSeparant f)^k * (δ^[k+1]) (ev ordinate) := by
  induction k with
  | zero => simp only [velocityNumerator, pow_zero, one_mul, Nat.zero_add, Function.iterate_one, h.root]
  | succ k ih =>
    change ev (clearedAction f (velocityNumerator f k) -
      (k : JetRing) * sepAlong f * velocityNumerator f k) = _
    simp only [map_sub, map_mul, map_natCast, ← h.action, ← h.sep, ih]
    rw [finite_step, Function.iterate_succ_apply' δ (k+1)]
theorem reciprocal_iterate {R : Type*} [CommRing R] {f : Equation} {ev : JetRing →+* R}
    {δ : Derivation ℤ R R} (h : ChartFlow f ev δ) (y : R) (hy : ev ordinate * y = 1) (k : ℕ) :
    ev (reciprocalNumerator f k) =
      (ev ordinate)^(k+2) * (ev (jetSeparant f))^k * (δ^[k+1]) y := by
  induction k with
  | zero =>
    have hd := congrArg δ hy
    simp only [δ.leibniz, smul_eq_mul, Derivation.map_one_eq_zero] at hd
    rw [reciprocalNumerator, map_neg, ← h.root]
    simp only [pow_zero, mul_one, Nat.zero_add, Function.iterate_one]
    linear_combination -(ev ordinate) * hd + δ (ev ordinate) * hy
  | succ k ih =>
    rw [reciprocalNumerator]
    simp only [map_sub, map_mul, map_natCast, ← h.action, ← h.sep, ← h.root, ih]
    rw [reciprocal_step, Function.iterate_succ_apply' δ (k+1)]
private theorem bound_ordinate : Bounded ordinate 0 0 := by
  apply Bounded.C
  intro i
  by_cases hi : i = 1
  · simp [hi]
  · simp [Polynomial.coeff_X_of_ne_one hi]
theorem reciprocal_bound {f : Equation} {s : ℕ} (hf : SeedBound f s) (k : ℕ) :
    Bounded (reciprocalNumerator f k) (k+1) (k*s) := by
  have hsep := Bounded.C (seedBound_derivative hf)
  have hB := second_bound hf
  have hxy := Bounded.C (seedBound_coeffDiff (seedBound_derivative hf))
  have hyy := Bounded.C (seedBound_derivative (seedBound_derivative hf))
  have hs : Bounded (sepAlong f) 1 s := by
    apply Bounded.add (Bounded.mono hxy (by omega) le_rfl)
    simpa only [Nat.zero_add, Nat.add_zero] using Bounded.mul Bounded.velocity hyy
  induction k with
  | zero => simpa only [reciprocalNumerator, Nat.zero_mul, Nat.zero_add] using Bounded.neg Bounded.velocity
  | succ k ih =>
    have h1 := Bounded.coeffDiff ih coefficientDerivative_zero (fun _ h => seedBound_coeffDiff h)
    have h2 := Bounded.coeffDiff ih (Polynomial.derivative_zero (R := K1_14.Seeds))
      (fun _ h => seedBound_derivative h)
    have hsum : Bounded (jetCoeffDerivative coefficientDerivative (reciprocalNumerator f k) +
        HighCore82706Tangent_3_1.velocity * jetCoeffDerivative Polynomial.derivative (reciprocalNumerator f k))
        (k+2) (k*s) := by
      apply Bounded.add (Bounded.mono h1 (Nat.le_succ _) le_rfl)
      simpa only [Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Bounded.mul Bounded.velocity h2
    have h3 := Bounded.mul hsep hsum
    have h4 := Bounded.mul hB (Bounded.derivative ih)
    have h5 := Bounded.mul (Bounded.mul (Bounded.nat k) hs) ih
    have h6 := Bounded.mul (Bounded.mul (Bounded.mul (Bounded.nat (k+2)) hsep) Bounded.velocity) ih
    have e : s + k*s = (k+1)*s := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    have hA : Bounded (clearedAction f (reciprocalNumerator f k) -
        (k : JetRing) * sepAlong f * reciprocalNumerator f k) (k+2) ((k+1)*s) := by
      apply Bounded.sub (Bounded.sub ?_ ?_) ?_
      · simpa only [clearedAction, Nat.zero_add, e] using h3
      · simpa only [Nat.add_sub_cancel, Nat.add_comm 2 k, e] using h4
      · simpa only [Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, ← e] using h5
    rw [reciprocalNumerator]
    apply Bounded.sub
    · simpa only [Nat.zero_add] using Bounded.mul bound_ordinate hA
    · simpa only [Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, ← e] using h6
end
end HighCore82706Tangent_3_1_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_1_2
noncomputable section
open HighCore82706Tangent (Input ResidueLift Factors)
open HighCore82706Tangent_3 (JetRing ordinate dehom)
open HighCore82706Tangent_3_1 (jetSeparant pureDegree pureOrdinate velocityNumerator)
open K1_14 (FX)
open HighCore82706Tangent_3_1 (Bounded seedBound_derivative)
open HighCore82706Tangent_3_1.Bounded (C pow mul mono scalar)
open HighCore82706Tangent_3_1 (root_degree)
open HighCore82706Tangent_3_1_2 (bound_ordinate)
def c1 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B),
    ∃ δ : ChartDerivation (Overlap J B D), ChartFlow J.f (finite J B D) δ
def c2 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B)
    (δ : ChartDerivation (Overlap J B D)),
    ChartFlow J.f (finite J B D) δ →
    ChartFlow (reverseEquation J) (inverse J B D) δ ∧
      inverse J B D (jetSeparant (reverseEquation J)) =
        -(reciprocal J B D^(J.e-2) * finite J B D (jetSeparant J.f))
private theorem inverse_ordinate {R : Type*} [CommRing R] (φ : JetRing →+* R) (z : R) :
    inverseEval φ z ordinate = z := by
  simp [inverseEval, ordinate, Polynomial.coe_eval₂RingHom]
private theorem inverse_scalar {R : Type*} [CommRing R] (φ : JetRing →+* R) (z : R) (s : FX) :
    inverseEval φ z (algebraMap FX JetRing s) = φ (algebraMap FX JetRing s) := by
  change inverseEval φ z (Polynomial.C (Polynomial.C (MvPolynomial.C s))) =
    φ (Polynomial.C (Polynomial.C (MvPolynomial.C s)))
  simp [inverseEval, seedMap, Polynomial.coe_eval₂RingHom]
private theorem scale_glue {R : Type*} [CommRing R] (y z c t s : R)
    {u m k a h : ℕ} (hy : y*z = 1) (hk : k ≤ m) (ha : a = u*m+(k+2)+h) :
    s * (c^(m-k) * (c^k*t)) =
      y^a * (((-1)^m*s) * (z^h * ((-(z^u*c))^(m-k) *
        (z^(k+2) * (-(z^u*c))^k * t)))) := by
  have hp : ∀ x : R, x^(m-k) * x^k = x^m := by
    intro x
    rw [← pow_add, Nat.sub_add_cancel hk]
  have h1 : y^a * (z^h * (z^(k+2) * (z^u)^m)) = 1 := by
    rw [← pow_mul, ← pow_add, ← pow_add, show h + (k+2+u*m) = a by omega,
      ← mul_pow, hy, one_pow]
  have hs : ((-1 : R)^m)*((-1)^m) = 1 := by rw [← mul_pow]; simp
  symm
  calc
    _ = y^a * (((-1)^m*s) * (z^h * (z^(k+2) * ((-(z^u*c))^(m-k) * (-(z^u*c))^k) * t))) := by
      ring
    _ = (((-1)^m)*((-1)^m)) * (y^a * (z^h * (z^(k+2) * (z^u)^m))) * (s * (c^m*t)) := by
      rw [hp, neg_pow (z^u*c), mul_pow (z^u)]
      ring
    _ = _ := by rw [hs, h1, one_mul, one_mul, ← hp c]; ring
private theorem root_exponent (J : Input) {r k : ℕ} (hk : k+1 ≤ r) :
    (pureDegree J r).1 = (J.e-2)*(r-1)+(k+2)+(J.e-2+(r-1-k)) := by
  have he : 3 ≤ J.e := J.sheets
  have hE : J.e-1 = (J.e-2)+1 := by omega
  have hR : r*(J.e-2) = (r-1)*(J.e-2)+(J.e-2) := by
    conv_lhs => rw [show r = (r-1)+1 by omega, Nat.add_mul, Nat.one_mul]
  rw [root_degree, hE, Nat.mul_add, Nat.mul_one, hR, Nat.mul_comm (r-1)]
  omega
private abbrev factorialScalar (k : ℕ) : FX := (((k+1).factorial : FX)⁻¹)
private def inverseOrdinate (J : Input) (r k : ℕ) : JetRing :=
  let F := reverseEquation J
  algebraMap FX JetRing ((-1 : FX)^(r-1) * factorialScalar k) *
    (ordinate^(J.e-2+(r-1-k)) * (jetSeparant F^(r-1-k) * reciprocalNumerator F k))
private theorem inverseOrdinate_bound (J : Input) {r k : ℕ} (hk : k+1 ≤ r) :
    Bounded (inverseOrdinate J r k) r (r*J.v) := by
  have hs := Bounded.C (seedBound_derivative (reverse_seedBound J))
  have hp := Bounded.mul (Bounded.scalar ((-1 : FX)^(r-1) * factorialScalar k))
    (Bounded.mul (Bounded.pow bound_ordinate (J.e-2+(r-1-k)))
      (Bounded.mul (Bounded.pow hs (r-1-k)) (reciprocal_bound (reverse_seedBound J) k)))
  have hmul : (r-1-k)*J.v + k*J.v = (r-1)*J.v := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega : k ≤ r-1)]
  apply Bounded.mono hp
  · simpa only [Nat.mul_zero, Nat.zero_add] using hk
  · simpa only [Nat.mul_zero, Nat.zero_add, hmul] using Nat.mul_le_mul_right J.v (Nat.sub_le r 1)
private theorem coord_transition {R : Type*} [CommRing R]
    (J : Input) {r k : ℕ} (hk : k+1 ≤ r) (φ : JetRing →+* R) (z : R)
    {δ : ChartDerivation R} (hd : ChartFlow J.f φ δ)
    (hi : ChartFlow (reverseEquation J) (inverseEval φ z) δ)
    (hy : φ ordinate * z = 1)
    (hc : inverseEval φ z (jetSeparant (reverseEquation J)) =
      -(z^(J.e-2) * φ (jetSeparant J.f))) :
    φ (pureOrdinate J r (k+1)) =
      (φ ordinate)^(pureDegree J r).1 * inverseEval φ z (inverseOrdinate J r k) := by
  let ψ := inverseEval φ z
  let F := reverseEquation J
  have hψ : ψ ordinate = z := inverse_ordinate φ z
  have hsmap (t : FX) : ψ (algebraMap FX JetRing t) = φ (algebraMap FX JetRing t) :=
    inverse_scalar φ z t
  have hf := finite_iterate hd k
  have hz : ψ ordinate * φ ordinate = 1 := by rw [hψ, mul_comm]; exact hy
  have hr : ψ (reciprocalNumerator F k) =
      (ψ ordinate)^(k+2) * (ψ (jetSeparant F))^k * (δ^[k+1]) (φ ordinate) :=
    reciprocal_iterate hi (φ ordinate) hz k
  have hsep : ψ (jetSeparant F) = -(z^(J.e-2) * φ (jetSeparant J.f)) := hc
  change φ (algebraMap FX JetRing (factorialScalar k) *
    (jetSeparant J.f^(r-1-k)*velocityNumerator J.f k)) =
    (φ ordinate)^(pureDegree J r).1 * ψ
      (algebraMap FX JetRing ((-1 : FX)^(r-1) * factorialScalar k) *
        (ordinate^(J.e-2+(r-1-k)) * (jetSeparant F^(r-1-k) * reciprocalNumerator F k)))
  simp only [map_mul, map_pow, hf, hsmap, map_neg, map_one, hψ, hr, hsep]
  exact scale_glue _ _ _ _ _ hy (by omega) (root_exponent J hk)
private theorem glue_eq {R : Type*} [CommRing R] (φ : JetRing →+* R)
    {z : R} {q P : JetRing} {A : HighCore82706Tangent_3.Cox} {a n : ℕ}
    (hA : φ (dehom A) = (φ ordinate)^(a+n) * inverseEval φ z P)
    (hq : φ q = (φ ordinate)^a * inverseEval φ z P) :
    φ (ordinate^n*q - dehom A) = 0 := by
  rw [map_sub, map_mul, map_pow, hA, hq, ← mul_assoc, ← pow_add, Nat.add_comm n a, sub_self]
theorem of_children (h1 : c1) (h2 : c2) : HighCore82706Tangent_3_1.c2 := by
  intro J B D r k hk _
  obtain ⟨δ, hd⟩ := h1 J B D
  obtain ⟨hi, hc⟩ := h2 J B D δ hd
  let φ := finite J B D
  let z := reciprocal J B D
  have hy := mul_reciprocal J B D
  have hb := inverseOrdinate_bound J hk
  obtain ⟨n, A, hA, evA⟩ :=
    inverse_homogeneous φ z hy (a := (pureDegree J r).1) hb.1 hb.2
  exact lift_of_overlap J B D hA (glue_eq φ evA (coord_transition J hk φ z hd hi hy hc))
end
end HighCore82706Tangent_3_1_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_1_1
noncomputable section
open K1_14 (FX Seeds Equation)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx Dx_mul coeff_partialX flatten partialX separant tangent cleared)
open HighCore82706Tangent_3 (JetRing rootInJet tangentEquation graphIdeal le_saturate)
open HighCore82706Tangent_3_1 (jetSeparant coefficientDerivative jetCoeffDerivative velocity
  secondAlongVelocity velocityNumerator embed_separant)
local notation "unwrap" => MvPolynomial.optionEquivLeft FX (Fin 2)
private theorem dx_nat (n : ℕ) : Dx (n : FX) = 0 := by
  have h : Dx 1 = 0 := by
    have h₁ := Dx_mul 1 1
    simp only [mul_one, one_mul] at h₁
    exact add_left_cancel (h₁.symm.trans (add_zero _).symm)
  rw [← nsmul_one, map_nsmul, h, nsmul_zero]
private theorem partial_mul (p q : Biform) :
    partialX (p * q) = p * partialX q + partialX p * q := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [coeff_partialX, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    MvPolynomial.coeff_mul, map_sum, Dx_mul, Finset.sum_add_distrib]
private theorem coeffDiff_mul (p q : Equation) :
    coefficientDerivative (p * q) =
      p * coefficientDerivative q + coefficientDerivative p * q := by
  unfold coefficientDerivative
  rw [show flatten (p * q) = flatten p * flatten q from map_mul _ _ _,
    partial_mul, map_add, map_mul, map_mul]
  simp only [AlgEquiv.apply_symm_apply]
private theorem coeffDiff_zero : coefficientDerivative 0 = 0 := by
  simp [coefficientDerivative]
private theorem coeffDiff_add (p q : Equation) :
    coefficientDerivative (p + q) = coefficientDerivative p + coefficientDerivative q := by
  simp only [coefficientDerivative, map_add]
private theorem coeff_coeffDiff (p : Equation) (i : ℕ) (m : Fin 2 →₀ ℕ) :
    ((coefficientDerivative p).coeff i).coeff m = Dx ((p.coeff i).coeff m) := by
  rw [coefficientDerivative, MvPolynomial.optionEquivLeft_coeff_coeff, coeff_partialX,
    ← MvPolynomial.optionEquivLeft_coeff_coeff FX, AlgEquiv.apply_symm_apply]
private theorem coeffDiff_one : coefficientDerivative 1 = 0 := by
  classical
  have h : Dx 1 = 0 := by simpa only [Nat.cast_one] using dx_nat 1
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro m
  by_cases hi : i = 0 <;> by_cases hm : (0 : Fin 2 →₀ ℕ) = m <;>
    simp [coeff_coeffDiff, Polynomial.coeff_one, MvPolynomial.coeff_one, hi, hm, h]
private theorem coeffDiff_derivative (p : Equation) :
    coefficientDerivative p.derivative = (coefficientDerivative p).derivative := by
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro m
  have h (q : Seeds) : (q * ((i : Seeds)+1)).coeff m = (↑(i+1 : ℕ) : FX) * q.coeff m := by
    rw [show (i : Seeds)+1 = (↑(i+1 : ℕ) : Seeds) from (Nat.cast_succ i).symm,
      ← map_natCast (MvPolynomial.C : FX →+* Seeds), mul_comm, MvPolynomial.coeff_C_mul]
  simp only [coeff_coeffDiff, Polynomial.coeff_derivative, h, Dx_mul, dx_nat, zero_mul, add_zero]
private theorem coeff_lift {d : Equation → Equation} (h0 : d 0 = 0) (p : JetRing) (i : ℕ) :
    (jetCoeffDerivative d p).coeff i = d (p.coeff i) := by
  rw [jetCoeffDerivative, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · exact Polynomial.coeff_monomial_same _ _
  · exact fun j _ hj => Polynomial.coeff_monomial_of_ne _ hj.symm
  · intro hi
    rw [Polynomial.notMem_support_iff.mp hi, h0, Polynomial.monomial_zero_right,
      Polynomial.coeff_zero]
private theorem lift_zero {d : Equation → Equation} (h0 : d 0 = 0) :
    jetCoeffDerivative d 0 = 0 := by
  ext i
  simp only [coeff_lift h0, Polynomial.coeff_zero, h0]
private theorem lift_add {d : Equation → Equation} (h0 : d 0 = 0)
    (hadd : ∀ a b, d (a + b) = d a + d b) (p q : JetRing) :
    jetCoeffDerivative d (p + q) = jetCoeffDerivative d p + jetCoeffDerivative d q := by
  ext i
  simp only [coeff_lift h0, Polynomial.coeff_add, hadd]
private theorem lift_mul {d : Equation → Equation} (h0 : d 0 = 0)
    (hadd : ∀ a b, d (a + b) = d a + d b)
    (hmul : ∀ a b, d (a * b) = a * d b + d a * b) (p q : JetRing) :
    jetCoeffDerivative d (p * q) = p * jetCoeffDerivative d q + jetCoeffDerivative d p * q := by
  let D : Equation →+ Equation := ⟨⟨d, h0⟩, hadd⟩
  have hs {α : Type} (s : Finset α) (g : α → Equation) :
      d (∑ a ∈ s, g a) = ∑ a ∈ s, d (g a) := map_sum D g s
  ext i
  simp only [coeff_lift h0, Polynomial.coeff_add, Polynomial.coeff_mul, hs, hmul,
    Finset.sum_add_distrib]
private theorem lift_C {d : Equation → Equation} (h0 : d 0 = 0) (q : Equation) :
    jetCoeffDerivative d (Polynomial.C q) = Polynomial.C (d q) := by
  ext i
  cases i <;> simp [coeff_lift h0, h0]
private theorem lift_X {d : Equation → Equation} (h0 : d 0 = 0) (h1 : d 1 = 0) :
    jetCoeffDerivative d velocity = 0 := by
  ext i
  by_cases hi : 1 = i <;> simp [velocity, coeff_lift h0, Polynomial.coeff_X, hi, h0, h1]
private def slope (f : Equation) : JetRing :=
  Polynomial.C (coefficientDerivative f.derivative) + velocity * Polynomial.C f.derivative.derivative
private def flow (f : Equation) : JetRing →+ JetRing where
  toFun p :=
    jetSeparant f * (jetCoeffDerivative coefficientDerivative p +
      velocity * jetCoeffDerivative Polynomial.derivative p) -
    secondAlongVelocity f * p.derivative
  map_zero' := by
    simp [lift_zero coeffDiff_zero, lift_zero Polynomial.derivative_zero]
  map_add' p q := by
    simp only [lift_add coeffDiff_zero coeffDiff_add,
      lift_add Polynomial.derivative_zero (fun a b : Equation => map_add Polynomial.derivative a b),
      map_add]
    ring
private theorem flow_mul (f : Equation) (p q : JetRing) :
    flow f (p * q) = p * flow f q + flow f p * q := by
  simp only [flow, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Polynomial.derivative_mul,
    lift_mul coeffDiff_zero coeffDiff_add coeffDiff_mul,
    lift_mul Polynomial.derivative_zero (fun a b : Equation => map_add Polynomial.derivative a b)
      (fun a b => Polynomial.derivative_mul.trans (add_comm _ _))]
  ring
private theorem flow_C (f q : Equation) :
    flow f (Polynomial.C q) =
      jetSeparant f * (Polynomial.C (coefficientDerivative q) + velocity * Polynomial.C q.derivative) := by
  simp [flow, lift_C coeffDiff_zero, lift_C Polynomial.derivative_zero]
private theorem flow_X (f : Equation) : flow f velocity = -secondAlongVelocity f := by
  change jetSeparant f * (jetCoeffDerivative coefficientDerivative Polynomial.X +
    velocity * jetCoeffDerivative Polynomial.derivative Polynomial.X) -
    secondAlongVelocity f * Polynomial.derivative Polynomial.X = _
  rw [lift_X coeffDiff_zero coeffDiff_one, lift_X Polynomial.derivative_zero
    Polynomial.derivative_one, Polynomial.derivative_X]
  ring
private theorem flow_tangentEquation (f : Equation) : flow f (tangentEquation f) = 0 := by
  change flow f (Polynomial.C (coefficientDerivative f) + velocity * jetSeparant f) = 0
  rw [map_add, flow_mul, flow_X, flow_C, flow_C, ← coeffDiff_derivative]
  unfold secondAlongVelocity
  ring
private theorem flow_sep (f : Equation) :
    flow f (jetSeparant f) = jetSeparant f * slope f :=
  flow_C f f.derivative
private theorem flow_sep_pow (f : Equation) (k : ℕ) :
    flow f (jetSeparant f ^ k) = (k : JetRing) * jetSeparant f ^ k * slope f := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, zero_mul, ← Polynomial.C_1, flow_C,
      coeffDiff_one, Polynomial.derivative_one]
    simp
  | succ k ih =>
    rw [pow_succ, flow_mul, flow_sep, ih, Nat.cast_succ]
    ring
private def tangentIdeal (f : Equation) : Ideal JetRing := Ideal.span {tangentEquation f}
private abbrev image (f : Equation) := Ideal.Quotient.mk (tangentIdeal f)
private theorem flow_congr (f : Equation) {p q : JetRing}
    (h : image f p = image f q) : image f (flow f p) = image f (flow f q) := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp h)
  apply Ideal.Quotient.eq.mpr
  rw [← map_sub, ← ha, flow_mul, flow_tangentEquation, mul_zero, zero_add]
  exact Ideal.mem_span_singleton'.mpr ⟨flow f a, rfl⟩
private theorem tangent_zero (f : Equation) : image f (tangentEquation f) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
private theorem rootInJet_apply (p : Biform) : rootInJet p = Polynomial.C (unwrap p) := rfl
private theorem tangent_image (f : Equation) (p : Biform) :
    image f (rootInJet (tangent (flatten f) p)) = image f (flow f (rootInJet p)) := by
  have hx (q : Biform) : rootInJet (partialX q) =
      Polynomial.C (coefficientDerivative (unwrap q)) := by
    simp only [rootInJet_apply, coefficientDerivative, AlgEquiv.symm_apply_apply]
  have hy : rootInJet (MvPolynomial.pderiv none p) = Polynomial.C (unwrap p).derivative := by
    rw [rootInJet_apply, MvPolynomial.optionEquivLeft_pderiv_none]
  have ht : rootInJet (tangent (flatten f) p) =
      flow f (rootInJet p) - tangentEquation f * rootInJet (MvPolynomial.pderiv none p) := by
    rw [tangent, map_sub, map_mul, map_mul, embed_separant, hx, hx, hy,
      AlgEquiv.apply_symm_apply, rootInJet_apply, flow_C]
    change _ = _ - (Polynomial.C (coefficientDerivative f) + velocity * jetSeparant f) * _
    ring
  rw [ht, map_sub, map_mul, tangent_zero, zero_mul, sub_zero]
private abbrev oldNum (f : Equation) (k : ℕ) : JetRing :=
  rootInJet (cleared (flatten f) k)
private theorem old_next (f : Equation) (k : ℕ) :
    image f (oldNum f (k+1)) =
      image f (jetSeparant f) * image f (flow f (oldNum f k)) -
      (↑(2*k+1 : ℕ) : JetRing ⧸ tangentIdeal f) *
        image f (jetSeparant f * slope f) * image f (oldNum f k) := by
  simp only [oldNum, cleared, map_sub, map_mul, embed_separant, tangent_image]
  rw [flow_sep, map_mul]
  have h : rootInJet (MvPolynomial.C (↑(2*k+1 : ℕ) : FX)) = (↑(2*k+1 : ℕ) : JetRing) :=
    (rootInJet.commutes _).trans (map_natCast (algebraMap FX JetRing) _)
  rw [h, map_natCast]
private theorem velocity_next (f : Equation) (k : ℕ) :
    velocityNumerator f (k+1) =
      flow f (velocityNumerator f k) - (k : JetRing) * slope f * velocityNumerator f k := rfl
set_option maxHeartbeats 800000 in
private theorem comparison (f : Equation) (k : ℕ) :
    image f (jetSeparant f ^ (k+1) * velocityNumerator f k) = image f (oldNum f k) := by
  induction k with
  | zero =>
    rw [show velocityNumerator f 0 = velocity from rfl,
      show oldNum f 0 = rootInJet (-partialX (flatten f)) from rfl,
      map_neg, rootInJet_apply, pow_one, mul_comm, map_mul, map_neg]
    have ht := tangent_zero f
    change image f (Polynomial.C (coefficientDerivative f) + velocity * jetSeparant f) = 0 at ht
    rw [map_add, map_mul] at ht
    exact eq_neg_of_add_eq_zero_right ht
  | succ k ih =>
    have hd := flow_congr f ih
    simp only [flow_mul, flow_sep_pow, map_add, map_mul, map_natCast, map_pow] at hd
    simp only [map_mul, map_pow] at ih
    rw [old_next, ← hd, ← ih]
    simp only [velocity_next, map_sub, map_mul, map_pow, map_natCast, Nat.cast_add,
      Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    rw [pow_succ _ (k+1)]
    ring
theorem proof : HighCore82706Tangent_3_1.c1 := by
  intro J B D k _
  have hle : tangentIdeal J.f ≤ graphIdeal J B D :=
    (graphIdeal J B D).span_singleton_le_iff_mem.mpr
      (le_saturate _ _ (Ideal.subset_span (by simp)))
  apply hle
  apply Ideal.Quotient.eq.mp
  change image J.f _ = image J.f _
  have hp : 2*k+1 = k+(k+1) := by omega
  rw [hp, pow_add, mul_assoc]
  simp only [map_mul, map_pow] at *
  have hc := comparison J.f k
  simp only [map_mul, map_pow] at hc
  rw [hc, mul_comm]
end
end HighCore82706Tangent_3_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HighCore82706Tangent_1
noncomputable section
open Polynomial Module
open K1_14 (L)
open HighCore82706Tangent (SeedConstants)
open private K1_14_1_1.quotientBasis K1_14_1_1.mulMatrix K1_14_1_1.mulMatrix_entry mulMatrix_specialize
  mulMatrix_det_ne_zero from ProximityPrize.SubmissionLower.Fast065
abbrev liftConstants (g : L[X]) : SeedConstants[X] := g.map MvPolynomial.C
private lemma det_degree {n : ℕ} (M : Matrix (Fin n) (Fin n) SeedConstants)
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) : M.det.totalDegree ≤ n := by
  classical
  rw [Matrix.det_apply']
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  have hs : (((Equiv.Perm.sign σ : ℤ) : SeedConstants)).totalDegree = 0 := by
    rw [← map_intCast (MvPolynomial.C : L →+* SeedConstants), MvPolynomial.totalDegree_C]
  have hp : (∏ j, M (σ j) j).totalDegree ≤ n := by
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc
      (∑ j, (M (σ j) j).totalDegree) ≤ ∑ _j : Fin n, 1 :=
        Finset.sum_le_sum fun j _ => hM (σ j) j
      _ = n := by simp
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa only [hs, zero_add] using hp)
private lemma coeff_degree_affine (A B : L[X]) (x : Fin 2) (j : ℕ) :
    ((liftConstants A + C (MvPolynomial.X x) * liftConstants B).coeff j).totalDegree ≤ 1 := by
  rw [coeff_add, coeff_C_mul, coeff_map, coeff_map]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]
    exact Nat.zero_le _
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, add_zero])
private lemma coeff_degree_product {A B : SeedConstants[X]} {s t : ℕ}
    (ha : ∀ j, (A.coeff j).totalDegree ≤ s)
    (hb : ∀ j, (B.coeff j).totalDegree ≤ t) (j : ℕ) :
    ((A * B).coeff j).totalDegree ≤ s + t := by
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (ha k.1) (hb k.2))
private lemma affine_mod (b A B : L[X]) (hb : b.Monic) (x : Fin 2) :
    (liftConstants A + C (MvPolynomial.X x) * liftConstants B) %ₘ liftConstants b =
      liftConstants (A %ₘ b) + C (MvPolynomial.X x) * liftConstants (B %ₘ b) := by
  rw [add_modByMonic, ← smul_eq_C_mul, smul_modByMonic, smul_eq_C_mul]
  simp only [liftConstants, map_modByMonic MvPolynomial.C hb]
private lemma eval_constants (z : Fin 2 → L) (g : L[X]) :
    (liftConstants g).map (MvPolynomial.eval z) = g := by
  have h : (MvPolynomial.eval z).comp MvPolynomial.C = RingHom.id L :=
    RingHom.ext fun c => MvPolynomial.eval_C c
  rw [map_map, h, map_id]
private lemma basis_coeff {b : SeedConstants[X]} {n : ℕ} (hb : b.Monic)
    (hn : b.natDegree = n) (v : AdjoinRoot b) (j : Fin n) :
    (K1_14_1_1.quotientBasis hb hn).equivFun v j = (AdjoinRoot.modByMonicHom hb v).coeff j := by
  rw [Basis.equivFun_apply]
  unfold K1_14_1_1.quotientBasis
  rw [Basis.repr_reindex_apply, AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  rfl
private theorem cleared_solution {b a q : SeedConstants[X]} {n : ℕ}
    (hb : b.Monic) (hn : b.natDegree = n) (hpos : 0 < n)
    (ha : ∀ i j, (K1_14_1_1.mulMatrix hb hn a i j).totalDegree ≤ 1)
    (hq : ∀ j, ((-q %ₘ b).coeff j).totalDegree ≤ 1) :
    ∃ t : SeedConstants[X], t.natDegree < n ∧
      (∀ j, (t.coeff j).totalDegree ≤ n) ∧ b ∣ a * t + C (K1_14_1_1.mulMatrix hb hn a).det * q := by
  let basis := K1_14_1_1.quotientBasis hb hn
  let M := K1_14_1_1.mulMatrix hb hn a
  let target := AdjoinRoot.mk b (-q)
  let solution := basis.equivFun.symm (M.cramer (basis.equivFun target))
  let t := AdjoinRoot.modByMonicHom hb solution
  have hcoord : basis.equivFun solution = M.cramer (basis.equivFun target) :=
    basis.equivFun.apply_symm_apply _
  have hsol : AdjoinRoot.mk b a * solution = M.det • target := by
    apply basis.equivFun.injective
    have hvec := Algebra.leftMulMatrix_mulVec_repr basis (AdjoinRoot.mk b a) solution
    change M.mulVec (basis.repr solution) = ⇑(basis.repr (AdjoinRoot.mk b a * solution)) at hvec
    rw [← Basis.equivFun_apply, ← Basis.equivFun_apply, hcoord, Matrix.mulVec_cramer] at hvec
    rw [map_smul]
    exact hvec.symm
  have hwidth : t.natDegree < n := by
    obtain ⟨s, hs⟩ := AdjoinRoot.mk_surjective solution
    dsimp only [t]
    rw [← hs, AdjoinRoot.modByMonicHom_mk, ← hn]
    apply natDegree_modByMonic_lt _ hb
    intro he
    rw [he, natDegree_one] at hn
    omega
  refine ⟨t, hwidth, ?_, AdjoinRoot.mk_eq_zero.mp ?_⟩
  · intro j
    by_cases hj : j < n
    · let k : Fin n := ⟨j, hj⟩
      change (t.coeff (k : ℕ)).totalDegree ≤ n
      rw [← basis_coeff hb hn solution k]
      change (basis.equivFun solution k).totalDegree ≤ n
      rw [hcoord, Matrix.cramer_apply]
      apply det_degree
      intro r c
      by_cases hc : c = k
      · subst c
        rw [Matrix.updateCol_self]
        rw [basis_coeff, AdjoinRoot.modByMonicHom_mk]
        exact hq r
      · rw [Matrix.updateCol_ne hc]
        exact ha r c
    · rw [coeff_eq_zero_of_natDegree_lt (show t.natDegree < j by omega),
        MvPolynomial.totalDegree_zero]
      exact Nat.zero_le _
  · change AdjoinRoot.mk b (a * t + C M.det * q) = 0
    rw [map_add, map_mul, map_mul, AdjoinRoot.mk_leftInverse hb solution, hsol, AdjoinRoot.mk_C]
    simp [target, Algebra.smul_def]
structure BlockContribution (h : ℕ) (b e A B Q : L[X]) (i : Fin 2) where
  den : SeedConstants
  num : SeedConstants[X]
  den_ne : den ≠ 0
  den_degree : den.totalDegree ≤ h
  num_degree : ∀ j, (num.coeff j).totalDegree ≤ h
  width : num.natDegree < 2 * h
  other_dvd : liftConstants e ∣ num
  congruence : liftConstants b ∣
    (liftConstants A + C (MvPolynomial.X i) * liftConstants B) * num +
      C (den * MvPolynomial.X i) * liftConstants Q
  regular : ∀ z : Fin 2 → L, IsCoprime (A + C (z i) * B) b →
    MvPolynomial.eval z den ≠ 0
theorem block_contribution {h : ℕ} (hpos : 0 < h) {b e A B Q : L[X]} (i : Fin 2)
    (hb : b.Monic) (he : e.Monic) (hbn : b.natDegree = h) (hen : e.natDegree = h)
    (hcop : IsCoprime e b) (h0 : IsCoprime A b) :
    Nonempty (BlockContribution h b e A B Q i) := by
  let amplitude := liftConstants A + C (MvPolynomial.X i) * liftConstants B
  let a := amplitude * liftConstants e
  let q := C (MvPolynomial.X i) * liftConstants Q
  have hbm : (liftConstants b).Monic := hb.map _
  have hbd : (liftConstants b).natDegree = h := (hb.natDegree_map _).trans hbn
  have hed : (liftConstants e).natDegree = h := (he.natDegree_map _).trans hen
  let M := K1_14_1_1.mulMatrix hbm hbd a
  have hM (r c : Fin h) : (M r c).totalDegree ≤ 1 := by
    change (K1_14_1_1.mulMatrix hbm hbd a r c).totalDegree ≤ 1
    rw [K1_14_1_1.mulMatrix_entry]
    have ha :
        a * Polynomial.X ^ (c : ℕ) =
          liftConstants (A * e * Polynomial.X ^ (c : ℕ)) +
            C (MvPolynomial.X i) * liftConstants (B * e * Polynomial.X ^ (c : ℕ)) := by
      simp only [a, amplitude, add_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
      ring
    rw [ha, affine_mod b _ _ hb]
    exact coeff_degree_affine _ _ _ _
  have hq (j : ℕ) : ((-q %ₘ liftConstants b).coeff j).totalDegree ≤ 1 := by
    have heq : -q = liftConstants 0 + C (MvPolynomial.X i) * liftConstants (-Q) := by
      simp only [q, liftConstants, Polynomial.map_zero, zero_add, Polynomial.map_neg]
      exact (_root_.mul_neg (C (MvPolynomial.X i : SeedConstants)) (liftConstants Q)).symm
    rw [heq, affine_mod b _ _ hb]
    exact coeff_degree_affine _ _ _ _
  have hregular (z : Fin 2 → L) (hz : IsCoprime (A + C (z i) * B) b) :
      MvPolynomial.eval z M.det ≠ 0 := by
    have hmapa : a.map (MvPolynomial.eval z) = (A + C (z i) * B) * e := by
      simp only [a, amplitude, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        eval_constants, MvPolynomial.eval_X]
    rw [mulMatrix_specialize (MvPolynomial.eval z) hbm hbd hb hbn (eval_constants z b) hmapa]
    exact mulMatrix_det_ne_zero hb hbn (hz.mul_left hcop)
  have hne : M.det ≠ 0 := by
    intro hd
    exact hregular (fun _ => 0) (by simpa using h0) (by simp [hd])
  obtain ⟨t, ht, htd, hc⟩ := cleared_solution hbm hbd hpos hM hq
  refine ⟨⟨M.det, liftConstants e * t, hne, det_degree M hM, ?_, ?_,
    dvd_mul_right _ _, ?_, hregular⟩⟩
  · intro j
    have hl (k : ℕ) : ((liftConstants e).coeff k).totalDegree ≤ 0 := by
      rw [coeff_map, MvPolynomial.totalDegree_C]
    simpa only [zero_add] using coeff_degree_product hl htd j
  · refine natDegree_mul_le.trans_lt ?_
    rw [hed]
    omega
  · change liftConstants b ∣ amplitude * (liftConstants e * t) +
      C (M.det * MvPolynomial.X i) * liftConstants Q
    simpa only [a, q, ← mul_assoc, ← map_mul] using hc
end
end HighCore82706Tangent_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HighCore82706Tangent_1
noncomputable section
open Polynomial
open P1 (K p)
open K1_14 (L liftPoly)
open HighCore82706Tangent (Input SeedConstants blockAt residueData residueDenominator)
private lemma combine_congruence {b a q N M : SeedConstants[X]} {d x : SeedConstants}
    (e : SeedConstants) (h : b ∣ a * N + C (d * x) * q) (hother : b ∣ M) :
    b ∣ a * (C e * N + C d * M) + C (x * (d * e)) * q := by
  have he := dvd_mul_of_dvd_right h (C e)
  have hm := dvd_mul_of_dvd_right hother (a * C d)
  convert dvd_add he hm using 1
  simp only [map_mul]
  ring
private lemma block_zero (J : Input) : blockAt J 0 = J.block := rfl
private lemma block_one (J : Input) : blockAt J 1 = J.secondBlock := rfl
private lemma data_zero (J : Input) (g : K[X]) :
    residueData J 0 g = liftConstants (liftPoly g) := by
  unfold residueData
  rw [ite_eq_left rfl, Polynomial.map_id]
private lemma data_one (J : Input) (g : K[X]) :
    residueData J 1 g = liftConstants ((liftPoly g).map (frobenius L p)) := rfl
theorem proof : HighCore82706Tangent.c1 := by
  intro J
  rcases J.chart with ⟨hm, hd, _, hm', hd', _, hcop, _, hdet, _, hmarks⟩
  let σ := frobenius L p
  let A := liftPoly (J.model.factor * J.model.A₀)
  let B := liftPoly (J.model.factor * J.model.A₁)
  let Q := liftPoly J.model.Q
  have hQA : IsCoprime (Q * A) J.block := by
    simpa only [A, Q, liftPoly, Polynomial.map_mul, mul_assoc] using hdet
  have hA : IsCoprime A J.block := hQA.of_mul_left_right
  obtain ⟨T₀⟩ := block_contribution (b := J.block) (e := J.secondBlock)
    (A := A) (B := B) (Q := Q) J.positive 0 hm hm' hd hd' hcop.symm hA
  obtain ⟨T₁⟩ := block_contribution (b := J.secondBlock) (e := J.block)
    (A := A.map σ) (B := B.map σ) (Q := Q.map σ) J.positive 1 hm' hm hd' hd hcop
    (hA.map (Polynomial.mapRingHom σ))
  refine ⟨⟨T₀.den * T₁.den, C T₁.den * T₀.num + C T₀.den * T₁.num, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact mul_ne_zero T₀.den_ne T₁.den_ne
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      ((Nat.add_le_add T₀.den_degree T₁.den_degree).trans (by rw [two_mul]))
  · intro j
    rw [coeff_add, coeff_C_mul, coeff_C_mul]
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_mul _ _).trans
        ((Nat.add_le_add T₁.den_degree (T₀.num_degree j)).trans (by rw [two_mul]))
    · exact (MvPolynomial.totalDegree_mul _ _).trans
        ((Nat.add_le_add T₀.den_degree (T₁.num_degree j)).trans (by rw [two_mul]))
  · apply (natDegree_add_le _ _).trans_lt
    exact max_lt ((natDegree_C_mul_le _ _).trans_lt T₀.width)
      ((natDegree_C_mul_le _ _).trans_lt T₁.width)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [block_zero, residueDenominator, data_zero, data_zero, data_zero]
      exact combine_congruence T₁.den T₀.congruence T₁.other_dvd
    · have hj : j = 0 := Subsingleton.elim j 0
      subst j
      change (blockAt J 1).map MvPolynomial.C ∣ residueDenominator J 1 *
        (C T₁.den * T₀.num + C T₀.den * T₁.num) +
          C (MvPolynomial.X 1 * (T₀.den * T₁.den)) * residueData J 1 J.model.Q
      rw [block_one, residueDenominator, data_one, data_one, data_one]
      have h := combine_congruence T₀.den T₁.congruence T₀.other_dvd
      rw [add_comm (C T₀.den * T₁.num) (C T₁.den * T₀.num), mul_comm T₁.den T₀.den] at h
      exact h
  · intro γ hγ
    let z := algebraMap K L (J.model.label γ)
    let seeds : Fin 2 → L := ![z, z ^ p]
    have hz : liftPoly (J.model.factor * J.model.amplitude γ) = A + C z * B := by
      simp only [A, B, z, P1.ModelAt.amplitude, liftPoly, mul_add, Polynomial.map_add,
        Polynomial.map_mul, Polynomial.map_C, mul_left_comm]
    obtain ⟨h₀, h₁, _, _⟩ := hmarks γ hγ
    have h₀' : IsCoprime (A + C (seeds 0) * B) J.block := by
      change IsCoprime (A + C z * B) J.block
      rwa [← hz]
    have h₁' : IsCoprime (A.map σ + C (seeds 1) * B.map σ) J.secondBlock := by
      change IsCoprime (A.map σ + C (z ^ p) * B.map σ) J.secondBlock
      rw [hz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at h₁
      exact h₁
    change MvPolynomial.eval seeds (T₀.den * T₁.den) ≠ 0
    rw [map_mul]
    exact mul_ne_zero (T₀.regular seeds h₀') (T₁.regular seeds h₁')
end
end HighCore82706Tangent_1
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_2
noncomputable section
open Polynomial
open P1 (K p)
open P1_7 (degreeAt quotientOrder)
open HighCore82706Tangent
open K1_14 (L FX liftPoly)
private theorem specialize_data (J : Input) (z : K) (i : Fin 2) (g : K[X]) :
    (residueData J i g).map (evalSeedConstants z) =
      (liftPoly g).map (if i = 0 then RingHom.id L else frobenius L p) := by
  rw [residueData, Polynomial.map_map]
  have h : (evalSeedConstants z).comp MvPolynomial.C = RingHom.id L := by
    ext x
    simp [evalSeedConstants]
  rw [h, Polynomial.map_id]
private theorem specialize_residue (J : Input) (B : ResidueLift J) (γ : K)
    (hγ : γ ∈ J.labels) (i : Fin 2) :
    blockAt J i ∣ C (evalSeedConstants (J.model.label γ) B.denominator) *
      liftPoly (J.family.scalar γ) - B.numerator.map (evalSeedConstants (J.model.label γ)) := by
  let z := J.model.label γ
  let ev := evalSeedConstants z
  let u := (![algebraMap K L z, (algebraMap K L z)^p] : Fin 2 → L) i
  let D := (residueDenominator J i).map ev
  let Q := (residueData J i J.model.Q).map ev
  let S := liftPoly (J.family.scalar γ)
  let a := C (ev B.denominator)
  let N := B.numerator.map ev
  have hX : evalSeedConstants z (MvPolynomial.X i) = u := MvPolynomial.eval_X i
  change blockAt J i ∣ a * S - N
  have h : blockAt J i ∣ D * N + a * (C u * Q) := by
    have hC : (evalSeedConstants z).comp MvPolynomial.C = RingHom.id L :=
      RingHom.ext fun x => MvPolynomial.eval_C x
    have he := Polynomial.map_dvd (evalSeedConstants z) (B.congruences i)
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map,
      hC, Polynomial.map_id, map_mul, hX] at he
    change blockAt J i ∣ D * N + (C u * a) * Q at he
    rwa [mul_comm (C u) a, mul_assoc] at he
  have hD : D = (liftPoly (J.model.factor * J.model.amplitude γ)).map
      (if i = 0 then RingHom.id L else frobenius L p) := by
    have hu : (if i = 0 then RingHom.id L else frobenius L p) (algebraMap K L z) = u := by
      fin_cases i <;> rfl
    have ha : J.model.factor * J.model.amplitude γ =
        J.model.factor * J.model.A₀ + C z * (J.model.factor * J.model.A₁) := by
      unfold P1.ModelAt.amplitude
      ring
    change (residueDenominator J i).map (evalSeedConstants z) = _
    rw [residueDenominator, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hX,
      specialize_data, specialize_data, ha]
    simp only [liftPoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hu]
  have hc : IsCoprime (blockAt J i) D ∧ blockAt J i ∣ D * S + C u * Q := by
    obtain ⟨h₀, h₁, h₂, h₃⟩ := J.chart.2.2.2.2.2.2.2.2.2.2 γ hγ
    rw [hD]
    change _ ∧ blockAt J i ∣ _ + C u * (residueData J i J.model.Q).map (evalSeedConstants z)
    rw [specialize_data]
    fin_cases i
    · simpa [blockAt, u, S, z] using And.intro h₀.symm h₂
    · exact ⟨h₁.symm, h₃⟩
  apply hc.1.dvd_of_dvd_mul_left
  have he : D * (a * S - N) = a * (D * S + C u * Q) - (D * N + a * (C u * Q)) := by ring
  rw [he]
  exact dvd_sub (hc.2.mul_left a) h
theorem marked_quotient (J : Input) (B : ResidueLift J) (γ : K) (hγ : γ ∈ J.marks) :
    ∃ T : L[X], T.natDegree ≤ J.ell ∧
      C (evalSeedConstants (J.model.label γ) B.denominator) * liftPoly (J.family.scalar γ) -
        B.numerator.map (evalSeedConstants (J.model.label γ)) = J.blockProduct * T := by
  let ev := evalSeedConstants (J.model.label γ)
  let W := C (ev B.denominator) * liftPoly (J.family.scalar γ) - B.numerator.map ev
  have hγ' := J.marks_sub hγ
  have hleft : J.block ∣ W := specialize_residue J B γ hγ' 0
  have hright : J.secondBlock ∣ W := specialize_residue J B γ hγ' 1
  have hcop : IsCoprime J.block J.secondBlock := J.chart.2.2.2.2.2.2.1
  obtain ⟨T, hT⟩ := hcop.mul_dvd hleft hright
  refine ⟨T, ?_, hT⟩
  by_cases hzero : T = 0
  · simp [hzero]
  have hg : J.blockProduct ≠ 0 := mul_ne_zero J.chart.1.ne_zero (J.chart.1.map _).ne_zero
  have hb : J.blockProduct.natDegree = 2 * J.w := by
    have h₁ : J.block.natDegree = J.w := J.chart.2.1
    have h₂ : J.secondBlock.natDegree = J.w := J.chart.2.2.2.2.1
    have hm : J.secondBlock.Monic := J.chart.2.2.2.1
    change (J.block * J.secondBlock).natDegree = _
    rw [Polynomial.natDegree_mul J.chart.1.ne_zero hm.ne_zero, h₁, h₂, two_mul]
  have hW : W.natDegree ≤ degreeAt J.w := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ _).trans (by
        rw [liftPoly, Polynomial.natDegree_map]
        exact HighCore82706.degree_at_height J.model J.family γ hγ')
    · have h := (natDegree_map_le (p := B.numerator) (f := ev)).trans B.numerator_width.le
      have hp : 0 < 131071 - J.w := J.quotient_pos
      unfold degreeAt
      omega
  change W = J.blockProduct * T at hT
  rw [hT, Polynomial.natDegree_mul hg hzero, hb] at hW
  unfold degreeAt at hW
  change T.natDegree ≤ quotientOrder J.w
  unfold quotientOrder
  omega
end
end HighCore82706Tangent_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_2
noncomputable section
open Polynomial Finset
open P1 (K p)
open P1_7 (degreeAt quotientOrder)
open HighCore82706Tangent
open K1_14 (L FX atX liftPoly seedEmbedding)
open K1_14_6 (Biform rootPoint)
open K1_14_6_1 (Dx Dx_mul derivativeAt flatten separant cleared markEval)
open scoped BigOperators
open private rationalJet rationalJet_incl from ProximityPrize.SubmissionLower.Fast055
private abbrev incl := algebraMap L[X] FX
private theorem factorial_ne_zero {n : ℕ} (hn : n < p) : (n.factorial : FX) ≠ 0 := by
  let : CharP FX p := charP_of_injective_ringHom seedEmbedding.injective p
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : ((n+1 : ℕ) : FX) ≠ 0 := by
      intro h
      exact (not_le_of_gt hn)
        (Nat.le_of_dvd (Nat.succ_pos n) ((CharP.cast_eq_zero_iff FX p _).mp h))
    simpa only [Nat.factorial_succ, Nat.cast_mul] using mul_ne_zero hc (ih (Nat.lt_of_succ_lt hn))
private def jet (a : FX) (i : ℕ) : FX := (i.factorial : FX)⁻¹ * (Dx^[i]) a
private theorem iterate_mul (a b : FX) (n : ℕ) :
    (Dx^[n]) (a*b) = ∑ k ∈ range (n+1), n.choose k • ((Dx^[n-k]) a * (Dx^[k]) b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit :
        (∑ k ∈ range (n+1), n.choose k • ((Dx^[n-k+1]) a * (Dx^[k]) b)) =
        (∑ k ∈ range (n+1), n.choose (k+1) • ((Dx^[n-k]) a * (Dx^[k+1]) b)) +
          (Dx^[n+1]) a * b := by
      rw [sum_range_succ', Nat.choose_zero_right, one_smul, tsub_zero,
        Function.iterate_zero_apply]
      congr 1
      rw [sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero]
      refine sum_congr rfl fun k hk => ?_
      rw [show n - (k+1) + 1 = n-k by have := mem_range.mp hk; omega]
    calc
      _ = Dx (∑ k ∈ range (n+1), n.choose k • ((Dx^[n-k]) a * (Dx^[k]) b)) := by
        rw [Function.iterate_succ_apply', ih]
      _ = (∑ k ∈ range (n+1), n.choose k • ((Dx^[n-k+1]) a * (Dx^[k]) b)) +
          ∑ k ∈ range (n+1), n.choose k • ((Dx^[n-k]) a * (Dx^[k+1]) b) := by
        simp only [map_sum, map_nsmul, Dx_mul, nsmul_add, sum_add_distrib,
          Function.iterate_succ_apply']
        rw [add_comm]
      _ = _ := by
        rw [hsplit, add_right_comm, ← sum_add_distrib, sum_range_succ' _ (n+1)]
        simp only [Nat.choose_zero_right, one_smul, tsub_zero, Function.iterate_zero_apply,
          Nat.choose_succ_succ, Nat.succ_sub_succ, add_smul]
        congr 1
        refine sum_congr rfl fun k _ => ?_
        exact add_comm _ _
private theorem jet_mul (a b : FX) {n : ℕ} (hn : n < p) :
    jet (a*b) n = ∑ i ∈ range (n+1), jet a (n-i) * jet b i := by
  unfold jet
  rw [iterate_mul, Finset.mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hle : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hs : (n.factorial : FX)⁻¹ * (n.choose i : FX) =
      ((n-i).factorial : FX)⁻¹ * (i.factorial : FX)⁻¹ := by
    have h := congrArg (fun k : ℕ => (k : FX)) (Nat.choose_mul_factorial_mul_factorial hle)
    push_cast at h
    field_simp [factorial_ne_zero hn, factorial_ne_zero (hle.trans_lt hn),
      factorial_ne_zero ((Nat.sub_le _ _).trans_lt hn)]
    linear_combination h
  rw [nsmul_eq_mul, ← mul_assoc, hs]
  ring
private theorem iterate_incl (H : L[X]) (n : ℕ) :
    (Dx^[n]) (incl H) = incl ((Polynomial.derivative^[n]) H) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    change (rationalJet (incl ((Polynomial.derivative^[n]) H))).snd = _
    rw [rationalJet_incl]
    rfl
private theorem jet_poly (H : L[X]) {i : ℕ} (hi : i < p) :
    jet (incl H) i = (Polynomial.taylor center (H.map constantAbscissa)).coeff i := by
  rw [jet, iterate_incl, Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, Polynomial.eval_map]
  have hev (P : L[X]) : P.eval₂ constantAbscissa center = incl P := by
    change P.eval₂ (incl.comp Polynomial.C) (incl Polynomial.X) = incl P
    rw [← Polynomial.hom_eval₂, Polynomial.eval₂_C_X]
  rw [hev]
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := L) i) H
  rw [← h, LinearMap.smul_apply, map_nsmul, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (factorial_ne_zero hi), one_mul]
private theorem seed_at_mark (z : K) (S : K[X]) :
    (markEval z S).comp seedBiform = constantAbscissa.comp (evalSeedConstants z) := by
  apply MvPolynomial.ringHom_ext
  · intro x
    simp [seedBiform, liftSeeds, evalSeedConstants]
  · intro i
    fin_cases i <;>
      simp [seedBiform, liftSeeds, evalSeedConstants, rootPoint, seedEmbedding,
        constantAbscissa]
private theorem liftTaylor_at_mark (z : K) (S : K[X]) (N : SeedConstants[X]) {i : ℕ}
    (hi : i < p) :
    markEval z S (liftTaylor N i) = jet (incl (N.map (evalSeedConstants z))) i := by
  rw [liftTaylor, ← Polynomial.coeff_map, Polynomial.map_taylor, Polynomial.map_map,
    seed_at_mark, MvPolynomial.eval_C, ← Polynomial.map_map, ← jet_poly _ hi]
private theorem iterate_atX (S : K[X]) (i : ℕ) :
    (Dx^[i]) (atX S) = derivativeAt S i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, K1_14_6_1.Dx_atX]
    exact congrArg atX (Function.iterate_succ_apply' (Polynomial.derivative (R := K)) i S).symm
private theorem ordinate_at_mark (J : Input) (z : K) (S : K[X])
    (hf : markEval z S (flatten J.f) = 0) {r i : ℕ} (hi : i ≤ r) :
    markEval z S (ordinateTaylorNum J.f r i) =
      markEval z S (separant (flatten J.f)) ^ (2*r-1) * jet (atX S) i := by
  cases i with
  | zero => simp [ordinateTaylorNum, jet, rootPoint]
  | succ i =>
    rw [ordinateTaylorNum, map_mul, map_mul, map_pow, MvPolynomial.eval_C,
      K1_14_6_1.eval_cleared _ _ _ hf]
    have he : (2*r-1-(2*i+1))+(2*i+1) = 2*r-1 := by omega
    simp only [jet, iterate_atX]
    let a := markEval z S (separant (flatten J.f))
    have hp : a ^ (2*r-1-(2*i+1)) * a ^ (2*i+1) = a ^ (2*r-1) := by
      rw [← pow_add, he]
    calc
      _ = (a ^ (2*r-1-(2*i+1)) * a ^ (2*i+1)) *
          (((i+1).factorial : FX)⁻¹ * derivativeAt S (i+1)) := by ring
      _ = _ := by rw [hp]
theorem cutoff_at_mark (J : Input) (B : ResidueLift J) (γ : K) (hγ : γ ∈ J.marks) :
    rootOn J (cutoff J B) γ := by
  let z := J.model.label γ
  let S := J.family.scalar γ
  let ev := markEval z S
  let δ := evalSeedConstants z B.denominator
  let N := B.numerator.map (evalSeedConstants z)
  let W := C δ * liftPoly S - N
  let r := J.ell+1
  have hr : r < p := by
    have h := J.factorial_guard
    change 131071 + J.hi + 1 < p at h
    change 131071 - J.w + 1 < p
    omega
  obtain ⟨T, hT, hW⟩ := marked_quotient J B γ hγ
  change W = J.blockProduct * T at hW
  have hG : incl J.blockProduct ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective L[X] FX).ne
      (show J.blockProduct ≠ 0 from mul_ne_zero J.chart.1.ne_zero (J.chart.1.map _).ne_zero)
  have hf : ev (flatten J.f) = 0 :=
    (K1_14_6_1.eval_flatten z S J.f).trans (J.regular γ hγ).1
  have hδ : ev (seedBiform B.denominator) = constantAbscissa δ :=
    RingHom.congr_fun (seed_at_mark z S) _
  have hcoeff (i : ℕ) (hi : i < p) : jet (incl W) i =
      constantAbscissa δ * jet (atX S) i - jet (incl N) i := by
    rw [jet_poly _ hi, atX, jet_poly _ hi, jet_poly _ hi]
    simp only [W, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, map_sub,
      Polynomial.taylor_mul, Polynomial.taylor_C, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  have hTzero : jet (incl T) r = 0 := by
    rw [jet_poly _ hr]
    apply coeff_eq_zero_of_natDegree_lt
    rw [Polynomial.natDegree_taylor]
    exact Polynomial.natDegree_map_le.trans_lt (Nat.lt_succ_of_le hT)
  have hc : ev (quotientNumerator J B r) = 0 := by
    let s := ev (separant (flatten J.f)) ^ (2*r-1)
    calc
      _ = s * ∑ i ∈ range (r+1), jet (incl J.blockProduct)⁻¹ (r-i) * jet (incl W) i := by
        rw [quotientNumerator, map_sum, Finset.mul_sum]
        refine sum_congr rfl fun i hi => ?_
        have hi' : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
        simp only [map_mul, map_sub, map_pow]
        rw [hδ, ordinate_at_mark J z S hf hi', liftTaylor_at_mark z S _ (hi'.trans_lt hr),
          hcoeff i (hi'.trans_lt hr)]
        have heval (a : FX) : ev (MvPolynomial.C a) = a := MvPolynomial.eval_C a
        rw [heval]
        change jet (incl J.blockProduct)⁻¹ (r-i) *
            (constantAbscissa δ * (s * jet (atX S) i) - s * jet (incl N) i) =
          s * (jet (incl J.blockProduct)⁻¹ (r-i) *
            (constantAbscissa δ * jet (atX S) i - jet (incl N) i))
        ring
      _ = s * jet ((incl J.blockProduct)⁻¹ * incl W) r := by rw [jet_mul _ _ hr]
      _ = 0 := by
        rw [hW, map_mul, ← mul_assoc, inv_mul_cancel₀ hG, one_mul, hTzero, mul_zero]
  exact (K1_14_6_1.eval_flatten z S (cutoff J B)).symm.trans (by
    change ev ((MvPolynomial.optionEquivLeft FX (Fin 2)).symm
      (MvPolynomial.optionEquivLeft FX (Fin 2) (quotientNumerator J B r))) = 0
    rw [AlgEquiv.symm_apply_apply]
    exact hc)
end
end HighCore82706Tangent_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_2
noncomputable section
open Polynomial Finset UniqueFactorizationMonoid
open K1_14 (Seeds Equation)
open K1_14_4 (seedDegree seedDegree_mul seedDegree_le_iff)
open HighCore82706Tangent
open scoped BigOperators
private theorem seedDegree_prod {α : Type*} (s : Finset α) (g : α → Equation)
    (hn : ∀ x ∈ s, g x ≠ 0) :
    seedDegree (∏ x ∈ s, g x) = ∑ x ∈ s, seedDegree (g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [seedDegree]
  | insert a s ha ih =>
    have hs : ∀ x ∈ s, g x ≠ 0 := fun x hx => hn x (mem_insert_of_mem hx)
    rw [prod_insert ha, sum_insert ha, seedDegree_mul
      (hn a (mem_insert_self _ _)) (prod_ne_zero_iff.mpr hs), ih hs]
private theorem coprime_generic_prod (s : Multiset Equation) (q : SeedField[X])
    (hc : ∀ g ∈ s, IsCoprime (generic g) q) : IsCoprime (generic s.prod) q := by
  induction s using Multiset.induction_on with
  | empty => simpa [generic] using (isCoprime_one_left : IsCoprime 1 q)
  | cons a s ih =>
    rw [Multiset.prod_cons, generic, Polynomial.map_mul]
    exact (hc a (Multiset.mem_cons_self _ _)).mul_left
      (ih fun g hg => hc g (Multiset.mem_cons_of_mem hg))
theorem factor_inventory (J : Input) (B : ResidueLift J)
    (hcut : ∀ γ ∈ J.marks, rootOn J (cutoff J B) γ) : Nonempty (Factors J B) := by
  classical
  let _ : StrongNormalizationMonoid Seeds := UniqueFactorizationMonoid.strongNormalizationMonoid
  let _ : IsGCDMonoid Seeds := nonempty_normalizedGCDMonoid_iff_isGCDMonoid.mp
    ⟨UniqueFactorizationMonoid.toNormalizedGCDMonoid Seeds⟩
  have hf := J.reduced
  have hf0 : J.f ≠ 0 := fun h => by simpa [h] using hf.1
  let q := generic (cutoff J B)
  let s := factors J.f
  let flat := s.filter fun g => generic g ∣ q
  let proper := s.filter fun g => ¬ generic g ∣ q
  let l := flat.toList
  let g : Fin l.length → Equation := fun j => l[j.1]
  have hred (a : Equation) (ha : a ∈ s) : P1_7.Reduced a := by
    have hd : a ∣ J.f := dvd_of_mem_factors ha
    have hp := isPrimitive_of_dvd hf.2.1 hd
    refine ⟨Nat.pos_of_ne_zero ?_, hp, hf.2.2.of_dvd (Polynomial.map_dvd _ hd)⟩
    intro hz
    have hu : IsUnit (a.coeff 0) :=
      (isPrimitive_iff_isUnit_of_C_dvd.mp hp) _ (by rw [← eq_C_of_natDegree_eq_zero hz])
    exact (irreducible_of_factor a ha).not_isUnit
      ((eq_C_of_natDegree_eq_zero hz).symm ▸ hu.map (C : Seeds →+* Equation))
  have hi (a : Equation) (ha : a ∈ s) : Irreducible (generic a) :=
    ((hred a ha).2.1.irreducible_iff_irreducible_map_fraction_map (K := SeedField)).mp
      (irreducible_of_factor a ha)
  obtain ⟨u, hu⟩ := factors_prod hf0
  have hpart : flat + proper = s := Multiset.filter_add_not _ _
  have hprod : (∏ j, g j) = flat.prod :=
    (Fin.prod_univ_getElem l).trans (Multiset.prod_toList flat)
  have hsplit : J.f = (proper.prod * (u : Equation)) * ∏ j, g j := by
    rw [hprod, ← hu]
    change s.prod * (u : Equation) = _
    rw [← hpart, Multiset.prod_add]
    ring
  have hg (j : Fin l.length) : g j ∈ s ∧ generic (g j) ∣ q := by
    have hj : g j ∈ flat := Multiset.mem_toList.mp (List.getElem_mem j.isLt)
    exact Multiset.mem_filter.mp hj
  have hgd (j : Fin l.length) : g j ∣ J.f := dvd_of_mem_factors (hg j).1
  refine ⟨⟨proper.prod * (u : Equation), l.length, g, hsplit, hcut, ?_,
    fun j => hred _ (hg j).1, fun j => hi _ (hg j).1, fun j => (hg j).2,
    ?_, fun j => natDegree_le_of_dvd (hgd j) hf0, ?_⟩⟩
  · have hc := coprime_generic_prod proper q (fun a ha =>
      ((hi a (Multiset.mem_filter.mp ha).1).isCoprime_or_dvd q).resolve_right
        (Multiset.mem_filter.mp ha).2)
    change IsCoprime (generic (proper.prod * (u : Equation))) q
    rw [generic, Polynomial.map_mul]
    exact (isCoprime_mul_unit_right_left
      (u.isUnit.map (Polynomial.mapRingHom (algebraMap Seeds SeedField))) _ _).mpr hc
  · have hsum : l.length ≤ ∑ j, (g j).natDegree := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using
        (Finset.sum_le_sum (s := (univ : Finset (Fin l.length))) (f := fun _ => 1)
          (g := fun j => (g j).natDegree) fun j _ => (hred (g j) (hg j).1).1)
    rw [← natDegree_prod _ _ (fun j _ => (irreducible_of_factor _ (hg j).1).ne_zero)] at hsum
    exact hsum.trans (natDegree_le_of_dvd ⟨_, hsplit.trans (mul_comm _ _)⟩ hf0)
  · rw [← seedDegree_prod _ _ (fun j _ => (irreducible_of_factor _ (hg j).1).ne_zero)]
    have h₁ : proper.prod * (u : Equation) ≠ 0 := left_ne_zero_of_mul (hsplit ▸ hf0)
    have h₂ : (∏ j, g j) ≠ 0 := right_ne_zero_of_mul (hsplit ▸ hf0)
    have hb := (seedDegree_le_iff _ _).mpr J.seed_bound
    conv at hb => lhs; rw [hsplit, seedDegree_mul h₁ h₂]
    exact (Nat.le_add_left _ _).trans hb
end
end HighCore82706Tangent_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_2
theorem proof : HighCore82706Tangent.c2 := by
  intro J B
  exact factor_inventory J B (cutoff_at_mark J B)
end HighCore82706Tangent_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2
noncomputable section
open K1_14 (FX)
open HighCore82706Tangent (Input ResidueLift Factors)
open HighCore82706Tangent_3
def cutoffIdeal (J : Input) (B : ResidueLift J) (D : Factors J B) : Ideal JetRing :=
  Ideal.span {Polynomial.C D.proper, tangentEquation J.f, Polynomial.C (HighCore82706Tangent.cutoff J B)}
def sectionIdeal {J : Input} {B : ResidueLift J} {D : Factors J B}
    (S : RelativeSection (graphIdeal J B D) (jetDegree J (J.ell+1))) : Ideal JetRing :=
  graphIdeal J B D ⊔ Ideal.span {S.affine}
def CutoffAgreement (J : Input) (B : ResidueLift J) (D : Factors J B)
    (S : RelativeSection (graphIdeal J B D) (jetDegree J (J.ell+1))) : Prop :=
  ∀ P : Ideal JetRing, P.IsPrime → graphIdeal J B D ≤ P → openFactor J B ∉ P →
    (S.affine ∈ P ↔ Polynomial.C (HighCore82706Tangent.cutoff J B) ∈ P)
def SeedTranscendental (P : Ideal JetRing) : Prop :=
  ∃ i : Fin 2, Transcendental FX (Ideal.Quotient.mk P (seedVar i))
def hilbert (Q : Ideal JetRing) (h t s : ℕ) : ℕ :=
  Module.finrank FX (gradedPiece Q (nefDegree h t s))
def EventuallyInChamber (p : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ N : ℕ, ∀ h t s, N ≤ h → N ≤ t → N ≤ s → p h t s
abbrev HilbertPoly := MvPolynomial (Fin 3) ℚ
def evalHilbert (p : HilbertPoly) (h t s : ℕ) : ℚ :=
  MvPolynomial.eval ![(h : ℚ), (t : ℚ), (s : ℚ)] p
def IsProfile (Q : Ideal JetRing) (p : HilbertPoly) : Prop :=
  EventuallyInChamber fun h t s => (hilbert Q h t s : ℚ) = evalHilbert p h t s
def NonnegativeTop (p : HilbertPoly) : Prop :=
  ∀ m : Fin 3 →₀ ℕ, (∑ i ∈ m.support, m i) = p.totalDegree → 0 ≤ p.coeff m
def difference (p : HilbertPoly) (a b c : ℕ) : HilbertPoly :=
  p - MvPolynomial.bind₁
    (fun i : Fin 3 => MvPolynomial.X i - MvPolynomial.C (![a, b, c] i : ℚ)) p
def ambient : HilbertPoly :=
  let H : HilbertPoly := MvPolynomial.X 0
  let T : HilbertPoly := MvPolynomial.X 1
  let U : HilbertPoly := MvPolynomial.X 2
  MvPolynomial.C (1/2 : ℚ) * (T+1) * (H+T+1) * (U+1) * (U+2)
structure Budget where
  fiber : ℕ
  tangent : ℕ
  seed : ℕ
def Budget.eval (b : Budget) (h t s : ℕ) : ℕ :=
  h*b.fiber + t*b.tangent + s*b.seed
def HasBudget (Q : Ideal JetRing) (b : Budget) : Prop :=
  ∃ offset : ℚ, EventuallyInChamber fun h t s =>
    (hilbert Q h t s : ℚ) ≤ (b.eval h t s : ℚ) + offset
def mixedBudget (e v a b c : ℕ) : Budget where
  fiber := v*c + v^2*b
  tangent := 2*e*v*c + v^2*a
  seed := e*c + v*((2*e-2)*b+a)
def actualOrdinate (J : Input) : ℕ := 1 + (J.ell+1)*(J.e-1)
def actualBudget (J : Input) : Budget :=
  mixedBudget J.e J.v (actualOrdinate J) (J.ell+1) ((J.ell+1)*J.v + 2*J.w)
def endpointBudget (J : Input) : Budget :=
  mixedBudget J.e J.v (HighCore82706Tangent.cutOrdinate J) (HighCore82706Tangent.cutVelocity J) (HighCore82706Tangent.cutSeed J)
end
end HighCore82706Tangent_3_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2
noncomputable section
open K1_14 (FX Seeds Equation atX atMark graphEval seedEmbedding)
open P1 (K)
open HighCore82706Tangent (Input ResidueLift Factors)
open HighCore82706Tangent_3
open K1_14_4 (seedDegree seedDegree_le_iff seedDegree_mul)
open K1_14_6_1 (flatten partialX markEval Dx Dx_eval Dx_atX eval_flatten eval_separant)
open MvPolynomial (optionEquivLeft)
open Polynomial (eval₂RingHom)
open private K1_14_6_1.flatten_bound from ProximityPrize.SubmissionLower.Fast055
theorem proper_ne_zero {J : Input} {B : ResidueLift J} (D : Factors J B) :
    D.proper ≠ 0 := by
  intro h
  have hf : J.f = 0 := by rw [D.product, h, zero_mul]
  exact (Nat.ne_of_gt J.reduced.1) (by simp [hf])
theorem root_section (J : Input) (B : ResidueLift J) (D : Factors J B) :
    ∃ R : RelativeSection (⊥ : Ideal JetRing) (nefDegree J.e 0 J.v),
      R.affine = Polynomial.C D.proper := by
  have hf : J.f ≠ 0 := fun h => (Nat.ne_of_gt J.reduced.1) (by simp [h])
  have hp := proper_ne_zero D
  have hprod : (∏ j, D.flat j) ≠ 0 := right_ne_zero_of_mul (D.product ▸ hf)
  have hpdeg : D.proper.natDegree ≤ J.e :=
    Polynomial.natDegree_le_of_dvd ⟨_, D.product⟩ hf
  have hs := (seedDegree_le_iff J.f J.v).mpr J.seed_bound
  rw [D.product, seedDegree_mul hp hprod] at hs
  have hps := (seedDegree_le_iff D.proper J.v).mp ((Nat.le_add_right _ _).trans hs)
  obtain ⟨p, hd, hdehom⟩ := homogenizeBiform (K1_14_6_1.flatten_bound hpdeg hps)
  have hd' : p.IsWeightedHomogeneous coxWeight (nefDegree J.e 0 J.v + 0 • (1, 0, 0)) := by
    simpa [nefDegree] using hd
  refine ⟨⟨0, p, p, hd', hd', by simp⟩, ?_⟩
  change dehom p = _
  rw [hdehom]
  change Polynomial.C (optionEquivLeft FX (Fin 2) (flatten D.proper)) = _
  rw [AlgEquiv.apply_symm_apply]
theorem tangent_nef (J : Input) : (J.e, 1, J.v) = nefDegree (J.e-2) 1 J.v := by
  have he : 3 ≤ J.e := J.sheets
  simp [nefDegree, Nat.sub_add_cancel (show 2 ≤ J.e by omega)]
theorem actualOrdinate_eq (J : Input) :
    1 + (J.e-3)*(J.ell+1) + 2*(J.ell+1) = actualOrdinate J := by
  have he : 3 ≤ J.e := J.sheets
  have h : J.e-3+2 = J.e-1 := by omega
  unfold actualOrdinate
  rw [Nat.add_assoc, ← Nat.add_mul, h, Nat.mul_comm (J.e-1)]
theorem endpoint_bounds (J : Input) :
    (actualBudget J).fiber ≤ (endpointBudget J).fiber ∧
    (actualBudget J).tangent ≤ (endpointBudget J).tangent ∧
    (actualBudget J).seed ≤ (endpointBudget J).seed := by
  have hb : J.ell+1 ≤ HighCore82706Tangent.cutVelocity J :=
    Nat.add_le_add_right (Nat.sub_le_sub_left J.lower 131071) 1
  have ha : actualOrdinate J ≤ HighCore82706Tangent.cutOrdinate J :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ hb) 1
  have hc : (J.ell+1)*J.v + 2*J.w ≤ HighCore82706Tangent.cutSeed J :=
    Nat.add_le_add (Nat.mul_le_mul_right _ hb) (Nat.mul_le_mul_left _ J.upper)
  exact ⟨Nat.add_le_add (Nat.mul_le_mul_left _ hc) (Nat.mul_le_mul_left _ hb),
    Nat.add_le_add (Nat.mul_le_mul_left _ hc) (Nat.mul_le_mul_left _ ha),
    Nat.add_le_add (Nat.mul_le_mul_left _ hc)
      (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hb) ha))⟩
private theorem seed_at_mark (z : K) :
    (graphEval z).comp HighCore82706Tangent.liftSeeds =
      HighCore82706Tangent.constantAbscissa.comp (HighCore82706Tangent.evalSeedConstants z) := by
  apply MvPolynomial.ringHom_ext
  · intro x
    simp [graphEval, HighCore82706Tangent.liftSeeds, HighCore82706Tangent.evalSeedConstants]
  · intro i
    fin_cases i <;>
      simp [graphEval, HighCore82706Tangent.liftSeeds, HighCore82706Tangent.evalSeedConstants,
        seedEmbedding, HighCore82706Tangent.constantAbscissa]
private theorem mark_C (J : Input) (γ : K) (q : Equation) :
    markPoint J γ (Polynomial.C q) = atMark q (J.model.label γ) (J.family.scalar γ) := by
  change (Polynomial.C q).eval₂ (markRoot J γ) (Dx (atX (J.family.scalar γ))) = _
  rw [Polynomial.eval₂_C]
  rfl
private theorem mark_tangent (J : Input) (γ : K) (hγ : γ ∈ J.marks) :
    markPoint J γ (tangentEquation J.f) = 0 := by
  let z := J.model.label γ
  let g := J.family.scalar γ
  have hf : markEval z g (flatten J.f) = 0 :=
    (eval_flatten z g J.f).trans (J.regular γ hγ).1
  have ht := Dx_eval z g (flatten J.f)
  change Dx (markEval z g (flatten J.f)) =
    markEval z g (partialX (flatten J.f)) +
      atX g.derivative * markEval z g (K1_14_6_1.separant (flatten J.f)) at ht
  rw [hf, map_zero, eval_separant] at ht
  have hPartial : flatten (optionEquivLeft FX (Fin 2) (partialX (flatten J.f))) =
      partialX (flatten J.f) := AlgEquiv.symm_apply_apply _ _
  unfold tangentEquation
  rw [map_add, map_mul, mark_C, mark_C, ← eval_flatten, hPartial]
  change markEval z g (partialX (flatten J.f)) +
    (Polynomial.X : JetRing).eval₂ (markRoot J γ) (Dx (atX g)) *
      atMark J.f.derivative z g = 0
  rw [Polynomial.eval₂_X, Dx_atX]
  exact ht.symm
theorem mark_regular (J : Input) (B : ResidueLift J) {γ : K} (hγ : γ ∈ J.marks) :
    openFactor J B ∉ RingHom.ker (markPoint J γ).toRingHom := by
  intro hz
  change markPoint J γ (openFactor J B) = 0 at hz
  rw [openFactor, map_mul, mark_C] at hz
  have hB : markPoint J γ (residueInJet B) =
    HighCore82706Tangent.constantAbscissa (HighCore82706Tangent.evalSeedConstants (J.model.label γ) B.denominator) := by
    rw [residueInJet, mark_C]
    change (Polynomial.C (HighCore82706Tangent.liftSeeds B.denominator)).eval₂
      (graphEval (J.model.label γ)) (atX (J.family.scalar γ)) = _
    rw [Polynomial.eval₂_C]
    exact DFunLike.congr_fun (seed_at_mark (J.model.label γ)) B.denominator
  have hBne : markPoint J γ (residueInJet B) ≠ 0 := by
    rw [hB]
    simpa only [map_zero] using
      (RingHom.injective HighCore82706Tangent.constantAbscissa).ne (B.unit_at_marks γ (J.marks_sub hγ))
  exact (mul_ne_zero hBne (J.regular γ hγ).2.2) hz
theorem cutoff_le_mark (J : Input) (B : ResidueLift J) (D : Factors J B) {γ : K}
    (hγ : γ ∈ J.marks) (hr : HighCore82706Tangent.rootOn J D.proper γ) :
    cutoffIdeal J B D ≤ RingHom.ker (markPoint J γ).toRingHom := by
  have hp : markPoint J γ (Polynomial.C D.proper) = 0 := (mark_C ..).trans hr
  have hc : markPoint J γ (Polynomial.C (HighCore82706Tangent.cutoff J B)) = 0 :=
    (mark_C ..).trans (D.cutoff_at_marks γ hγ)
  unfold cutoffIdeal
  rw [Ideal.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact hp
  · exact mark_tangent J γ hγ
  · exact hc
theorem graph_le_prime {J : Input} {B : ResidueLift J} {D : Factors J B} {P : Ideal JetRing}
    (hp : P.IsPrime) (hcut : cutoffIdeal J B D ≤ P) (hreg : openFactor J B ∉ P) :
    graphIdeal J B D ≤ P := by
  have hbase : Ideal.span {Polynomial.C D.proper, tangentEquation J.f} ≤ P := by
    apply le_trans _ hcut
    exact Ideal.span_mono (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  rintro x ⟨n, hn⟩
  exact (hp.mul_mem_iff_mem_or_mem.mp (hbase hn)).resolve_left (fun h => hreg (hp.mem_of_pow_mem n h))
theorem section_le_prime {J : Input} {B : ResidueLift J} {D : Factors J B}
    {S : RelativeSection (graphIdeal J B D) (jetDegree J (J.ell+1))}
    (hc : CutoffAgreement J B D S) {P : Ideal JetRing} (hp : P.IsPrime)
    (hcut : cutoffIdeal J B D ≤ P) (hreg : openFactor J B ∉ P) :
    sectionIdeal S ≤ P := by
  have hg := graph_le_prime hp hcut hreg
  apply sup_le hg
  rw [Ideal.span_singleton_le_iff_mem]
  exact (hc P hp hg hreg).mpr (hcut (Ideal.subset_span (by simp)))
end
end HighCore82706Tangent_3_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2
noncomputable section
open K1_14 (FX Seeds Equation)
open HighCore82706Tangent_3
open MvPolynomial
open scoped BigOperators
private def quotientMap (Q : Ideal JetRing) : Cox →ₐ[FX] JetRing ⧸ Q :=
  (Ideal.Quotient.mkₐ FX Q).comp dehom
private def factorMap {I P : Ideal JetRing} (h : I ≤ P) : (JetRing ⧸ I) →ₐ[FX] JetRing ⧸ P where
  toRingHom := Ideal.Quotient.factor h
  commutes' _ := rfl
theorem hilbert_mono {I P : Ideal JetRing} (h : I ≤ P) (a b c : ℕ) :
    hilbert P a b c ≤ hilbert I a b c := by
  let d := nefDegree a b c
  let F := (factorMap h).toLinearMap
  have hF (x : gradedPiece I d) : F x.val ∈ gradedPiece P d := by
    obtain ⟨q, hq, he⟩ := Submodule.mem_map.mp x.prop
    exact Submodule.mem_map.mpr ⟨q, hq, by rw [← he]; rfl⟩
  let L := (F.comp (gradedPiece I d).subtype).codRestrict (gradedPiece P d) hF
  apply LinearMap.finrank_le_finrank_of_surjective (f := L)
  intro x
  obtain ⟨q, hq, he⟩ := Submodule.mem_map.mp x.prop
  exact ⟨⟨quotientMap I q, Submodule.mem_map.mpr ⟨q, hq, rfl⟩⟩, Subtype.ext he⟩
set_option maxHeartbeats 500000 in
private theorem dehom_surjective : Function.Surjective dehom := by
  let s : Seeds →+* Cox :=
    MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X (tᵢ i.castSucc))
  let y : Equation →+* Cox := Polynomial.eval₂RingHom s (MvPolynomial.X h₁)
  let v : JetRing →+* Cox := Polynomial.eval₂RingHom y (MvPolynomial.X v₁)
  have hs : dehom.toRingHom.comp s =
      (Polynomial.C : Equation →+* JetRing).comp (Polynomial.C : Seeds →+* Equation) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change dehom (MvPolynomial.eval₂Hom MvPolynomial.C _ (MvPolynomial.C a)) =
        Polynomial.C (Polynomial.C (MvPolynomial.C a))
      rw [MvPolynomial.eval₂Hom_C]
      change MvPolynomial.aeval affineCoord (MvPolynomial.C a) = _
      rw [MvPolynomial.aeval_C]
      rfl
    · intro i
      change dehom (MvPolynomial.eval₂Hom MvPolynomial.C _ (MvPolynomial.X i)) = _
      rw [MvPolynomial.eval₂Hom_X']
      change MvPolynomial.aeval affineCoord (MvPolynomial.X (tᵢ i.castSucc)) =
        Polynomial.C (Polynomial.C (MvPolynomial.X i))
      rw [MvPolynomial.aeval_X]
      fin_cases i <;> rfl
  have hy : dehom.toRingHom.comp y = Polynomial.C := by
    apply Polynomial.ringHom_ext
    · intro a
      change dehom ((Polynomial.C a).eval₂ s (MvPolynomial.X h₁)) =
        Polynomial.C (Polynomial.C a)
      rw [Polynomial.eval₂_C]
      exact DFunLike.congr_fun hs a
    · change dehom ((Polynomial.X : Equation).eval₂ s (MvPolynomial.X h₁)) = Polynomial.C Polynomial.X
      rw [Polynomial.eval₂_X]
      simp [dehom, affineCoord, h₁, ordinate]
  have hv : dehom.toRingHom.comp v = RingHom.id JetRing := by
    apply Polynomial.ringHom_ext
    · intro a
      change dehom ((Polynomial.C a).eval₂ y (MvPolynomial.X v₁)) = Polynomial.C a
      rw [Polynomial.eval₂_C]
      exact DFunLike.congr_fun hy a
    · change dehom ((Polynomial.X : JetRing).eval₂ y (MvPolynomial.X v₁)) = Polynomial.X
      rw [Polynomial.eval₂_X]
      simp [dehom, affineCoord, v₁]
  exact fun x => ⟨v x, DFunLike.congr_fun hv x⟩
private theorem pad_monomial (m : CoxVar →₀ ℕ) (a : FX) (k : ℕ)
    (h₁' : (Finsupp.weight coxWeight m).1 ≤ 3*k)
    (hv' : (Finsupp.weight coxWeight m).2.1 ≤ k)
    (ht' : (Finsupp.weight coxWeight m).2.2 ≤ k) :
    ∃ p : Cox, p.IsWeightedHomogeneous coxWeight (nefDegree k k k) ∧
      dehom p = dehom (monomial m a) := by
  let w := Finsupp.weight coxWeight m
  let i := 3*k - w.1
  let j := k - w.2.1
  let l := k - w.2.2
  refine ⟨monomial m a * (MvPolynomial.X h₀)^i * (MvPolynomial.X v₀)^j *
    (MvPolynomial.X (tᵢ 2))^l, ?_, ?_⟩
  · have hw := (((isWeightedHomogeneous_monomial coxWeight m a rfl).mul
        ((isWeightedHomogeneous_X FX coxWeight h₀).pow i)).mul
        ((isWeightedHomogeneous_X FX coxWeight v₀).pow j)).mul
        ((isWeightedHomogeneous_X FX coxWeight (tᵢ 2)).pow l)
    have he : w + i • coxWeight h₀ + j • coxWeight v₀ + l • coxWeight (tᵢ 2) =
        nefDegree k k k := by
      change (w.1 + (i*1) + (j*0) + (l*0), w.2.1 + (i*0) + (j*1) + (l*0),
        w.2.2 + (i*0) + (j*0) + (l*1)) = (k + 2*k, k, k)
      have ha : w.1 ≤ 3*k := h₁'
      have hb : w.2.1 ≤ k := hv'
      have hc : w.2.2 ≤ k := ht'
      dsimp [i,j,l]
      congr 1 <;> simp only [mul_one]
      · omega
      · congr 1 <;> omega
    rwa [← he]
  · simp [dehom, affineCoord, h₀, v₀, tᵢ]
private theorem lift_big (x : JetRing) :
    ∃ n, ∀ k, n ≤ k → ∃ p : Cox,
      p.IsWeightedHomogeneous coxWeight (nefDegree k k k) ∧ dehom p = x := by
  classical
  obtain ⟨q, hq⟩ := dehom_surjective x
  let size := fun m : CoxVar →₀ ℕ =>
    let w := Finsupp.weight coxWeight m
    w.1 + w.2.1 + w.2.2
  refine ⟨q.support.sup size, fun k hk => ?_⟩
  have hex (m : q.support) : ∃ p : Cox,
      p.IsWeightedHomogeneous coxWeight (nefDegree k k k) ∧
        dehom p = dehom (monomial m.val (q.coeff m.val)) := by
    have hm : size m.val ≤ k := (Finset.le_sup m.prop).trans hk
    change (Finsupp.weight coxWeight m.val).1 + (Finsupp.weight coxWeight m.val).2.1 +
      (Finsupp.weight coxWeight m.val).2.2 ≤ k at hm
    exact pad_monomial m.val (q.coeff m.val) k (by omega) (by omega) (by omega)
  choose f hd hf using hex
  refine ⟨∑ m, f m, (weightedHomogeneousSubmodule FX coxWeight _).sum_mem
    (fun m _ => hd m), ?_⟩
  rw [map_sum]
  simp_rw [hf]
  rw [Finset.sum_coe_sort q.support (fun m => dehom (monomial m (q.coeff m))),
    ← map_sum, ← MvPolynomial.as_sum, hq]
private def mulQuotient (I P : Ideal JetRing) (s : JetRing)
    (h : ∀ p ∈ I, s * p ∈ P) : (JetRing ⧸ I) →ₗ[FX] JetRing ⧸ P :=
  (I.restrictScalars FX).liftQ ((Ideal.Quotient.mkₐ FX P).toLinearMap ∘ₗ LinearMap.mulLeft FX s)
    (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (h p hp))
private theorem mul_mem_iInf {ι : Type} {P : ι → Ideal JetRing} {s : ι → JetRing}
    (hmem : ∀ i j, i ≠ j → s i ∈ P j) (i : ι) :
    ∀ p ∈ P i, s i * p ∈ ⨅ j, P j := by
  classical
  intro p hp
  refine Ideal.mem_iInf.mpr fun j => ?_
  by_cases hij : i = j
  · subst hij
    exact (P i).mul_mem_left _ hp
  · exact (P j).mul_mem_right _ (hmem i j hij)
theorem separator_bound {ι : Type} [Fintype ι] (I : Ideal JetRing) (P : ι → Ideal JetRing)
    (hp : ∀ i, (P i).IsPrime) (hinc : Pairwise fun i j => ¬P i ≤ P j) (hI : ∀ i, I ≤ P i) :
    ∃ k, ∀ h t s, (∑ i, hilbert (P i) h t s) ≤ hilbert I (h+k) (t+k) (s+k) := by
  classical
  obtain ⟨sep, hsep⟩ := Ideal.exists_separators_of_pairwise_not_le hp hinc
  choose n hn using fun i => lift_big (sep i)
  let k := Finset.univ.sup n
  have hk (i : ι) : n i ≤ k := Finset.le_sup (Finset.mem_univ i)
  choose lift hd he using fun i => hn i k (hk i)
  let Q := ⨅ j, P j
  let F (i : ι) := mulQuotient (P i) Q (sep i)
    (mul_mem_iInf (fun i j h => (hsep i j).mpr h) i)
  have hF (i : ι) (p : JetRing) :
      F i (Ideal.Quotient.mk (P i) p) = Ideal.Quotient.mk Q (sep i * p) := rfl
  refine ⟨k, fun h t s => ?_⟩
  let d := nefDegree h t s
  let d' := nefDegree (h+k) (t+k) (s+k)
  let Φ : ((i : ι) → gradedPiece (P i) d) →ₗ[FX] JetRing ⧸ Q :=
    ∑ i, F i ∘ₗ (gradedPiece (P i) d).subtype ∘ₗ LinearMap.proj i
  have hΦ (x : (i : ι) → gradedPiece (P i) d) : Φ x ∈ gradedPiece Q d' := by
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.subtype_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨q, hq, hx⟩ := Submodule.mem_map.mp (x i).prop
    change q.IsWeightedHomogeneous coxWeight d at hq
    change quotientMap (P i) q = (x i).val at hx
    rw [← hx, show quotientMap (P i) q = Ideal.Quotient.mk (P i) (dehom q) from rfl]
    have hsum : nefDegree k k k + d = d' := by
      change (k+2*k+(h+2*t), k+t, k+s) = (h+k+2*(t+k), t+k, s+k)
      congr 1
      · omega
      · congr 1 <;> omega
    exact Submodule.mem_map.mpr ⟨lift i * q, hsum ▸ (hd i).mul hq, by
      change Ideal.Quotient.mk Q (dehom (lift i * q)) = F i (Ideal.Quotient.mk (P i) (dehom q))
      rw [map_mul, he, hF]⟩
  have hker (x : (i : ι) → gradedPiece (P i) d) (hx : Φ x = 0) : x = 0 := by
    funext i
    apply Subtype.ext
    have hfac := congrArg (Ideal.Quotient.factor (iInf_le P i)) hx
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.subtype_apply, map_sum, map_zero] at hfac
    rw [Finset.sum_eq_single i] at hfac
    · obtain ⟨q, _, hq⟩ := Submodule.mem_map.mp (x i).prop
      change Ideal.Quotient.mk (P i) (dehom q) = (x i).val at hq
      rw [← hq, hF, Ideal.Quotient.factor_mk, map_mul] at hfac
      have := hp i
      have hnz : Ideal.Quotient.mk (P i) (sep i) ≠ 0 := fun hz =>
        (hsep i i).mp (Ideal.Quotient.eq_zero_iff_mem.mp hz) rfl
      simp only [Pi.zero_apply, ZeroMemClass.coe_zero, ← hq]
      exact (mul_eq_zero.mp hfac).resolve_left hnz
    · intro j _ hji
      obtain ⟨q, _, hq⟩ := Submodule.mem_map.mp (x j).prop
      change Ideal.Quotient.mk (P j) (dehom q) = (x j).val at hq
      rw [← hq, hF, Ideal.Quotient.factor_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((P i).mul_mem_right _ ((hsep j i).mpr hji))
    · simp
  have hdim : (∑ i, hilbert (P i) h t s) ≤ hilbert Q (h+k) (t+k) (s+k) := by
    have (i : ι) : Module.Free FX (gradedPiece (P i) d) := Module.Free.of_divisionRing FX _
    change (∑ i, Module.finrank FX (gradedPiece (P i) d)) ≤ Module.finrank FX (gradedPiece Q d')
    rw [← Module.finrank_pi_fintype]
    apply LinearMap.finrank_le_finrank_of_injective (f := Φ.codRestrict _ hΦ)
    intro x y heq
    exact sub_eq_zero.mp (hker _ ((map_sub Φ x y).trans (sub_eq_zero.mpr (congrArg Subtype.val heq))))
  exact hdim.trans (hilbert_mono (le_iInf hI) _ _ _)
end
end HighCore82706Tangent_3_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2
noncomputable section
open HighCore82706Tangent_3
open scoped BigOperators
private theorem slope_le {u v N : ℕ} {a b : ℚ}
    (h : ∀ n : ℕ, N ≤ n → (n : ℚ)*u + a ≤ (n : ℚ)*v + b) : u ≤ v := by
  by_contra! hlt
  obtain ⟨n, hn⟩ := exists_nat_gt (b-a)
  let m := max n N
  have hm : b-a < (m : ℚ) := hn.trans_le (by exact_mod_cast le_max_left n N)
  have h₁ := h m (le_max_right n N)
  have h₂ : (v : ℚ) + 1 ≤ (u : ℚ) := by exact_mod_cast Nat.succ_le_of_lt hlt
  have h₃ := mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg m)
  linarith
theorem probe_sums {ι : Type} [Fintype ι] {I : Ideal JetRing} {b : Budget}
    (P : ι → Ideal JetRing) (T : ∀ i, CurveProbe (P i))
    (hdim : ∃ k, ∀ h t s, (∑ i, hilbert (P i) h t s) ≤ hilbert I (h+k) (t+k) (s+k))
    (hb : HasBudget I b) :
    (∑ i, (T i).fiber) ≤ b.fiber ∧
      (∑ i, (T i).tangent) ≤ b.tangent ∧ (∑ i, (T i).seed) ≤ b.seed := by
  classical
  obtain ⟨k, hk⟩ := hdim
  obtain ⟨offset, N, hN⟩ := hb
  let M := max N (Finset.univ.sup fun i => (T i).threshold)
  let u := ∑ i, (T i).fiber
  let v := ∑ i, (T i).tangent
  let w := ∑ i, (T i).seed
  let A : ℚ := ∑ i, ((T i).offset : ℚ)
  let B : ℚ := (k : ℚ)*(b.fiber + b.tangent + b.seed) + offset
  have hM (i : ι) : (T i).threshold ≤ M := by
    have hi : (T i).threshold ≤ Finset.univ.sup (fun j => (T j).threshold) :=
      Finset.le_sup (f := fun j => (T j).threshold) (Finset.mem_univ i)
    exact hi.trans (le_max_right _ _)
  have hline (h t s : ℕ) (hh : M ≤ h) (ht : M ≤ t) (hs : M ≤ s) :
      (h : ℚ)*u + (t : ℚ)*v + (s : ℚ)*w + A ≤
        (h : ℚ)*b.fiber + (t : ℚ)*b.tangent + (s : ℚ)*b.seed + B := by
    have heval (i : ι) :
        (hilbert (P i) h t s : ℚ) =
          (h : ℚ)*(T i).fiber + (t : ℚ)*(T i).tangent +
          (s : ℚ)*(T i).seed + ((T i).offset : ℚ) := by
      have hi := (T i).hilbert h t s ((hM i).trans hh) ((hM i).trans ht) ((hM i).trans hs)
      exact_mod_cast hi
    have he : (∑ i, (hilbert (P i) h t s : ℚ)) =
        (h : ℚ)*u + (t : ℚ)*v + (s : ℚ)*w + A := by
      simp only [heval, u, v, w, A, Nat.cast_sum, Finset.mul_sum, Finset.sum_add_distrib]
    have hshift (x : ℕ) (hx : M ≤ x) : N ≤ x+k :=
      (le_max_left _ _).trans (hx.trans (Nat.le_add_right _ _))
    have hsum : (∑ i, (hilbert (P i) h t s : ℚ)) ≤ (hilbert I (h+k) (t+k) (s+k) : ℚ) := by
      exact_mod_cast hk h t s
    have hoff := hN (h+k) (t+k) (s+k) (hshift h hh) (hshift t ht) (hshift s hs)
    rw [he] at hsum
    have htotal := hsum.trans hoff
    simp only [Budget.eval, Nat.cast_add, Nat.cast_mul] at htotal
    dsimp [B]
    linarith only [htotal]
  refine ⟨slope_le (N := M) (a := (M : ℚ)*v + (M : ℚ)*w + A)
      (b := (M : ℚ)*b.tangent + (M : ℚ)*b.seed + B) (fun n hn => ?_),
    slope_le (N := M) (a := (M : ℚ)*u + (M : ℚ)*w + A)
      (b := (M : ℚ)*b.fiber + (M : ℚ)*b.seed + B) (fun n hn => ?_),
    slope_le (N := M) (a := (M : ℚ)*u + (M : ℚ)*v + A)
      (b := (M : ℚ)*b.fiber + (M : ℚ)*b.tangent + B) (fun n hn => ?_)⟩
  · linarith only [hline n M M hn le_rfl le_rfl]
  · linarith only [hline M n M le_rfl hn le_rfl]
  · linarith only [hline M M n le_rfl le_rfl hn]
end
end HighCore82706Tangent_3_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2
noncomputable section
open K1_14 (FX Seeds Equation)
open HighCore82706Tangent (Input ResidueLift Factors)
open HighCore82706Tangent_3
def c1 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B)
    (S : RelativeSection (graphIdeal J B D) (jetDegree J (J.ell+1))),
    CutoffAgreement J B D S →
    IsLeftRegular (Ideal.Quotient.mk (rootIdeal D) (tangentEquation J.f)) ∧
    IsLeftRegular (Ideal.Quotient.mk (graphIdeal J B D) S.affine)
def c2 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B)
    (P : Ideal JetRing), P ∈ (cutoffIdeal J B D).minimalPrimes →
    openFactor J B ∉ P → SeedTranscendental P
def c3 : Prop :=
  IsProfile ⊥ ambient
def c4 : Prop :=
  (∀ Q : Ideal JetRing, ∃ p : HilbertPoly, IsProfile Q p ∧ NonnegativeTop p) ∧
  (∀ (Q R : Ideal JetRing) (a b c : ℕ) (S : RelativeSection Q (nefDegree a b c)),
    Q ≤ R → S.affine ∈ R → IsLeftRegular (Ideal.Quotient.mk Q S.affine) →
    ∀ p q : HilbertPoly, IsProfile Q p → IsProfile R q →
      NonnegativeTop (difference p a b c - q))
def c5 : Prop :=
  ∀ (e v a b c : ℕ), 2 ≤ e →
    ∀ p₁ p₂ p₃ : HilbertPoly,
      NonnegativeTop p₁ → NonnegativeTop p₂ → NonnegativeTop p₃ →
      NonnegativeTop (difference ambient e 0 v - p₁) →
      NonnegativeTop (difference p₁ (e-2) 1 v - p₂) →
      NonnegativeTop (difference p₂ a b c - p₃) →
      ∃ offset : ℚ, ∀ h t s : ℕ,
        evalHilbert p₃ h t s ≤ ((mixedBudget e v (a+2*b) b c).eval h t s : ℚ) + offset
def c6 : Prop :=
  ∀ (P : Ideal JetRing) (p : HilbertPoly) (b : Budget),
    P.IsPrime → IsProfile P p → NonnegativeTop p → HasBudget P b →
    SeedTranscendental P → ∃ probe : CurveProbe P, 0 < probe.seed
private theorem affine_regrade {Q : Ideal JetRing} {d d' : Degree}
    (hd : d = d') (S : RelativeSection Q d) :
    (hd ▸ S : RelativeSection Q d').affine = S.affine := by subst d'; rfl
private theorem cutoff_budget (h1 : c1) (h3 : c3) (h4 : c4) (h5 : c5)
    (J : Input) (B : ResidueLift J) (D : Factors J B) (G : TangentSection J D)
    (S : RelativeSection (graphIdeal J B D) (jetDegree J (J.ell+1)))
    (hc : CutoffAgreement J B D S) : HasBudget (sectionIdeal S) (actualBudget J) := by
  obtain ⟨p₁, hp₁, hpos₁⟩ := h4.1 (rootIdeal D)
  obtain ⟨p₂, hp₂, hpos₂⟩ := h4.1 (graphIdeal J B D)
  obtain ⟨p₃, hp₃, hpos₃⟩ := h4.1 (sectionIdeal S)
  obtain ⟨R, hR⟩ := root_section J B D
  have hRne : R.affine ≠ 0 := by
    rw [hR]
    exact Polynomial.C_ne_zero.mpr (proper_ne_zero D)
  have hRreg : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal JetRing) R.affine) := by
    have : (⊥ : Ideal JetRing).IsPrime := Ideal.isPrime_bot
    apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hRne
  have hd₁ := h4.2 ⊥ (rootIdeal D) J.e 0 J.v R bot_le
    (by rw [hR]; exact Ideal.subset_span (Set.mem_singleton _)) hRreg ambient p₁ h3 hp₁
  have ht : rootIdeal D ≤ graphIdeal J B D := by
    rw [rootIdeal, Ideal.span_singleton_le_iff_mem]
    exact proper_mem_graph J B D
  let G' : RelativeSection (rootIdeal D) (nefDegree (J.e-2) 1 J.v) :=
    tangent_nef J ▸ G.section_
  have hG : G'.affine = tangentEquation J.f :=
    (affine_regrade (tangent_nef J) G.section_).trans G.affine_eq
  obtain ⟨hGreg, hSreg⟩ := h1 J B D S hc
  have hGmem : G'.affine ∈ graphIdeal J B D := by
    rw [hG]
    exact le_saturate _ _ (Ideal.subset_span (by simp))
  have hd₂ := h4.2 (rootIdeal D) (graphIdeal J B D) (J.e-2) 1 J.v G' ht hGmem
    (hG.symm ▸ hGreg) p₁ p₂ hp₁ hp₂
  have hSspan : Ideal.span {S.affine} ≤ sectionIdeal S := le_sup_right
  have hSmem : S.affine ∈ sectionIdeal S := hSspan (Ideal.subset_span (Set.mem_singleton _))
  have hd₃ := h4.2 (graphIdeal J B D) (sectionIdeal S) (1 + (J.e-3)*(J.ell+1)) (J.ell+1)
    ((J.ell+1)*J.v + 2*J.w) S le_sup_left hSmem hSreg p₂ p₃ hp₂ hp₃
  have he : 2 ≤ J.e := (by decide : 2 ≤ 3).trans J.sheets
  obtain ⟨z, hz⟩ := h5 J.e J.v (1 + (J.e-3)*(J.ell+1)) (J.ell+1) ((J.ell+1)*J.v + 2*J.w)
    he p₁ p₂ p₃ hpos₁ hpos₂ hpos₃ hd₁ hd₂ hd₃
  simp only [actualOrdinate_eq] at hz
  obtain ⟨N, hN⟩ := hp₃
  refine ⟨z, N, fun h t s hh ht hs => ?_⟩
  exact (hN h t s hh ht hs).trans_le (hz h t s)
private theorem hasBudget_mono {I P : Ideal JetRing} (hIP : I ≤ P) {b : Budget}
    (hb : HasBudget I b) : HasBudget P b := by
  obtain ⟨c, N, hN⟩ := hb
  refine ⟨c, N, fun h t s hh ht hs => ?_⟩
  have hm : (hilbert P h t s : ℚ) ≤ (hilbert I h t s : ℚ) := by
    exact_mod_cast hilbert_mono hIP h t s
  exact hm.trans (hN h t s hh ht hs)
private theorem jet_noetherian : IsNoetherianRing JetRing := by
  have : IsNoetherianRing FX := by
    rw [isNoetherianRing_iff_ideal_fg]
    intro I
    rcases I.eq_bot_or_top with rfl | rfl
    · exact Submodule.fg_bot
    · refine ⟨{1}, ?_⟩
      change Ideal.span (({1} : Finset FX) : Set FX) = ⊤
      simp
  have : IsNoetherianRing Seeds := MvPolynomial.isNoetherianRing_fin
  have hEquation : IsNoetherianRing Equation := Polynomial.isNoetherianRing (R := Seeds)
  exact @Polynomial.isNoetherianRing Equation _ hEquation
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) (h6 : c6) :
    HighCore82706Tangent_3.c2 := by
  classical
  intro J B D G S hcut
  let I := cutoffIdeal J B D
  let onOpen : Set (Ideal JetRing) := {P | P ∈ I.minimalPrimes ∧ openFactor J B ∉ P}
  have : IsNoetherianRing JetRing := jet_noetherian
  have hfin : onOpen.Finite :=
    I.finite_minimalPrimes_of_isNoetherianRing.subset (fun _ h => h.1)
  let _ := hfin.fintype
  let count := Fintype.card onOpen
  let E : Fin count ≃ onOpen := (Fintype.equivFin onOpen).symm
  let P (i : Fin count) : Ideal JetRing := (E i).val
  have hmin (i : Fin count) : I.IsMinimalPrime (P i) := (E i).prop.1
  have hreg (i : Fin count) : openFactor J B ∉ P i := (E i).prop.2
  have hprime (i : Fin count) : (P i).IsPrime := (hmin i).isPrime
  have hgraph (i : Fin count) : graphIdeal J B D ≤ P i :=
    graph_le_prime (hprime i) (hmin i).le (hreg i)
  have hsection (i : Fin count) : sectionIdeal S ≤ P i :=
    section_le_prime hcut (hprime i) (hmin i).le (hreg i)
  have hinc : Pairwise fun i j => ¬P i ≤ P j := by
    intro i j hij hle
    apply hij
    apply E.injective
    apply Subtype.ext
    exact le_antisymm hle ((hmin j).2 (hmin i).1 hle)
  have hbudget := cutoff_budget h1 h3 h4 h5 J B D G S hcut
  have hprobe (i : Fin count) : ∃ T : CurveProbe (P i), 0 < T.seed := by
    obtain ⟨p, hp, hpos⟩ := h4.1 (P i)
    exact h6 (P i) p (actualBudget J) (hprime i) hp hpos
      (hasBudget_mono (hsection i) hbudget) (h2 J B D (P i) (hmin i) (hreg i))
  choose T hT using hprobe
  let curve (i : Fin count) : CurveSlice J B D := {
    prime := P i
    isPrime := hprime i
    onGraph := hgraph i
    onCutoff := (hmin i).le (Ideal.subset_span (by simp))
    regular := hreg i
    marks := J.marks.filter (fun γ => P i ≤ RingHom.ker (markPoint J γ).toRingHom)
    sub := Finset.filter_subset _ _
    liesOn := fun γ hg => (Finset.mem_filter.mp hg).2
    probe := T i
    positive_seed := hT i
  }
  obtain ⟨hf, ht, hs⟩ := probe_sums P T (separator_bound (sectionIdeal S) P hprime hinc hsection) hbudget
  obtain ⟨hef, het, hes⟩ := endpoint_bounds J
  refine ⟨⟨count, curve, ?_, hf.trans hef, ht.trans het, hs.trans hes⟩⟩
  intro γ hγ hr
  let ker := RingHom.ker (markPoint J γ).toRingHom
  let _ : ker.IsPrime := RingHom.ker_isPrime (markPoint J γ).toRingHom
  obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (cutoff_le_mark J B D hγ hr)
  let p' : onOpen := ⟨p, hp, fun h => mark_regular J B hγ (hple h)⟩
  refine ⟨E.symm p', Finset.mem_filter.mpr ⟨hγ, ?_⟩⟩
  change (E (E.symm p')).val ≤ ker
  rw [Equiv.apply_symm_apply]
  exact hple
end
end HighCore82706Tangent_3_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2_1
noncomputable section
open K1_14 (L FX Seeds Equation)
open K1_14_6_1 (partialX flatten)
open HighCore82706Tangent (Input ResidueLift Factors SeedField generic liftSeeds constantAbscissa)
open HighCore82706Tangent_3
open HighCore82706Tangent_3_2 (CutoffAgreement)
open Polynomial
private theorem regular_of_kernel {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (I : Ideal R) (h : RingHom.ker f = I)
    (x : R) (hx : IsLeftRegular (f x)) : IsLeftRegular (Ideal.Quotient.mk I x) := by
  have hz : ∀ r ∈ I, f r = 0 := fun r hr => RingHom.mem_ker.mp (h.symm ▸ hr)
  let F := Ideal.Quotient.lift I f hz
  have hF : Function.Injective F := RingHom.lift_injective_of_ker_le_ideal I hz h.le
  intro a b hab
  apply hF
  apply hx
  simpa only [map_mul, Ideal.Quotient.lift_mk, F] using congrArg F hab
private theorem linear_regular {T : Type*} [CommRing T] (a b : T) (ha : IsUnit a) :
    IsLeftRegular (C b + Polynomial.X * C a) := by
  obtain ⟨u, rfl⟩ := ha
  let q : T[X] := Polynomial.X + C (↑u⁻¹ * b)
  have he : C b + Polynomial.X * C (u : T) = C (u : T) * q := by
    dsimp only [q]
    rw [mul_add, ← C_mul, Units.mul_inv_cancel_left, mul_comm (C (u : T)) Polynomial.X,
      add_comm]
  rw [he, isLeftRegular_iff_right_eq_zero_of_mul]
  intro p hp
  have hq : q.Monic := monic_X_add_C _
  apply hq.mul_right_eq_zero_iff.mp
  have hu : IsUnit (C (u : T)) := u.isUnit.map C
  apply hu.mul_left_cancel (b := q * p) (c := 0)
  rw [← mul_assoc, hp, mul_zero]
private theorem coprime_unit {T : Type*} [CommRing T] {p q : T} (h : IsCoprime p q) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {p}) q) := by
  let m := Ideal.Quotient.mk (Ideal.span {p})
  obtain ⟨a, b, hab⟩ := h
  have hp : m p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have he := congrArg m hab
  rw [map_add, map_mul, map_mul, map_one, hp, mul_zero, zero_add, mul_comm] at he
  exact isUnit_iff_dvd_one.mpr ⟨m b, he.symm⟩
private theorem clear_velocity {R T : Type*} [CommRing R] [CommRing T]
    (χ : R[X] →+* T) (a b : R) (p : R[X]) (ht : χ (C b + Polynomial.X * C a) = 0) :
    χ (C a ^ p.natDegree * p) = χ (C ((p.scaleRoots a).eval (-b))) := by
  let ψ := χ.comp (C : R →+* R[X])
  have hx : ψ a * χ Polynomial.X = ψ (-b) := by
    change χ (C a) * χ Polynomial.X = χ (C (-b))
    rw [map_neg, map_neg]
    apply eq_neg_of_add_eq_zero_right
    simpa only [map_add, map_mul, mul_comm] using ht
  have hev : p.eval₂ ψ (χ Polynomial.X) = χ p := by
    change p.eval₂ (χ.comp C) (χ Polynomial.X) = χ p
    rw [← hom_eval₂, eval₂_C_X]
  calc
    χ (C a ^ p.natDegree * p) = ψ a ^ p.natDegree * p.eval₂ ψ (χ Polynomial.X) := by
      rw [hev, map_mul, map_pow]
      rfl
    _ = (p.scaleRoots a).eval₂ ψ (ψ a * χ Polynomial.X) :=
      (scaleRoots_eval₂_mul ψ (χ Polynomial.X) a).symm
    _ = χ (C ((p.scaleRoots a).eval (-b))) := by
      rw [hx]
      change _ = ψ ((p.scaleRoots a).eval (-b))
      simpa only [RingHom.comp_id, eval₂_id] using
        ((p.scaleRoots a).hom_eval₂ (RingHom.id R) ψ (-b)).symm
set_option maxHeartbeats 1000000 in
theorem proof : HighCore82706Tangent_3_2.c1 := by
  intro J B D S hagree
  let I : Ideal SeedField[X] := Ideal.span {generic D.proper}
  let T := SeedField[X] ⧸ I
  let _ : CommRing T := Ideal.Quotient.commRing I
  let _ : CommRing T[X] := Polynomial.commRing
  let φ : Equation →+* T :=
    (Ideal.Quotient.mk I).comp (Polynomial.mapRingHom (algebraMap Seeds SeedField))
  let a := J.f.derivative
  let b := MvPolynomial.optionEquivLeft FX (Fin 2) (partialX (flatten J.f))
  have ht : tangentEquation J.f = C b + Polynomial.X * C a := rfl
  have hdiv : D.proper ∣ J.f := ⟨_, D.product⟩
  have hprim := isPrimitive_of_dvd J.reduced.2.1 hdiv
  have hφ (q : Equation) : φ q = 0 ↔ D.proper ∣ q := by
    change Ideal.Quotient.mk I (generic q) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact (hprim.dvd_iff_fraction_map_dvd_fraction_map SeedField).symm
  have hc : IsCoprime (generic J.f) (generic a) := by
    simpa only [generic, a, Separable, ← derivative_map] using J.reduced.2.2
  have ha : IsUnit (φ a) :=
    coprime_unit (hc.of_isCoprime_of_dvd_left (Polynomial.map_dvd _ hdiv))
  constructor
  · let F := Polynomial.mapRingHom φ
    have hF : RingHom.ker F = rootIdeal D := by
      have hker : RingHom.ker φ = Ideal.span {D.proper} := by
        ext q
        rw [RingHom.mem_ker, hφ, Ideal.mem_span_singleton]
      rw [Polynomial.ker_mapRingHom, hker, Ideal.map_span, Set.image_singleton]
      rfl
    have hL : IsLeftRegular (F (tangentEquation J.f)) := by
      rw [ht]
      simpa only [F, coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, map_C, map_X]
        using linear_regular (φ a) (φ b) ha
    exact regular_of_kernel (R := JetRing) (T := T[X]) F (rootIdeal D) hF
      (tangentEquation J.f) hL
  let E : Ideal JetRing := Ideal.span {C D.proper, tangentEquation J.f}
  let d := liftSeeds B.denominator
  let u := ha.unit
  let v : T := -φ b * ↑u⁻¹
  let ev : JetRing →+* T := eval₂RingHom φ v
  have hevC (q : Equation) : ev (C q) = φ q := eval₂_C _ _
  have hevT : ev (tangentEquation J.f) = 0 := by
    have hevX : ev Polynomial.X = v := eval₂_X _ _
    rw [ht, map_add, map_mul, hevC, hevC, hevX]
    dsimp only [v]
    rw [← ha.unit_spec, Units.inv_mul_cancel_right, add_neg_cancel]
  have hevO : IsUnit (ev (openFactor J B)) := by
    have hι : Function.Injective constantAbscissa :=
      (IsFractionRing.injective L[X] FX).comp Polynomial.C_injective
    have hd : d ≠ 0 := by
      simpa only [d, liftSeeds, map_zero] using
        (MvPolynomial.map_injective _ hι).ne B.denominator_ne
    have hd' : IsUnit (algebraMap Seeds SeedField d) :=
      isUnit_iff_ne_zero.mpr
        ((map_ne_zero_iff _ (IsFractionRing.injective Seeds SeedField)).mpr hd)
    have hφd : IsUnit (φ (C d)) := by
      change IsUnit (Ideal.Quotient.mk I ((C d).map (algebraMap Seeds SeedField)))
      rw [map_C]
      exact (hd'.map C).map (Ideal.Quotient.mk I)
    change IsUnit (ev (C (C d) * C a))
    rw [map_mul, hevC, hevC]
    exact hφd.mul ha
  have hE : E ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact RingHom.mem_ker.mpr ((hevC _).trans ((hφ _).mpr dvd_rfl))
    · exact RingHom.mem_ker.mpr hevT
  have hg : graphIdeal J B D ≤ RingHom.ker ev := by
    rintro p ⟨n, hn⟩
    have hzero := RingHom.mem_ker.mp (hE hn)
    rw [map_mul, map_pow, ← mul_zero ((ev (openFactor J B))^n)] at hzero
    exact RingHom.mem_ker.mpr ((hevO.pow n).mul_left_cancel hzero)
  have hker : RingHom.ker ev = graphIdeal J B D := by
    refine le_antisymm ?_ hg
    intro p hp
    let r := (p.scaleRoots a).eval (-b)
    have hr : φ r = 0 := by
      have he := clear_velocity ev a b p (ht ▸ hevT)
      rw [map_mul, RingHom.mem_ker.mp hp, mul_zero, hevC] at he
      exact he.symm
    have hCr : C r ∈ E := by
      obtain ⟨q, hq⟩ := (hφ r).mp hr
      rw [hq, map_mul, mul_comm]
      exact E.mul_mem_left _ (Ideal.subset_span (by simp))
    have hT : Ideal.Quotient.mk E (C b + Polynomial.X * C a) = 0 := by
      rw [← ht, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by simp)
    have hp' : C a ^ p.natDegree * p ∈ E :=
      Ideal.Quotient.eq_zero_iff_mem.mp
        ((clear_velocity (Ideal.Quotient.mk E) a b p hT).trans
          (Ideal.Quotient.eq_zero_iff_mem.mpr hCr))
    refine ⟨p.natDegree, ?_⟩
    rw [openFactor, mul_pow, mul_assoc]
    exact E.mul_mem_left _ hp'
  have hcut : IsUnit (ev (C (HighCore82706Tangent.cutoff J B))) := by
    rw [hevC]
    exact coprime_unit D.proper_coprime
  have hS : IsUnit (ev S.affine) := by
    by_contra hn
    obtain ⟨M, hM, hle⟩ := Ideal.ne_top_iff_exists_maximal.mp
      (mt Ideal.span_singleton_eq_top.mp hn)
    let P := M.comap ev
    let _ : M.IsPrime := hM.isPrime
    have hP : P.IsPrime := Ideal.comap_isPrime ev M
    have hG : graphIdeal J B D ≤ P := fun p hp => by
      change ev p ∈ M
      rw [RingHom.mem_ker.mp (hg hp)]
      exact M.zero_mem
    have hO : openFactor J B ∉ P := Ideal.notMem_of_isUnit M hevO
    have hmem : S.affine ∈ P := hle (Ideal.mem_span_singleton_self _)
    exact Ideal.notMem_of_isUnit M hcut ((hagree P hP hG hO).mp hmem)
  exact regular_of_kernel (R := JetRing) (T := T) ev (graphIdeal J B D) hker S.affine
    (fun _ _ h => hS.mul_left_cancel h)
end
end HighCore82706Tangent_3_2_1
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2_2
noncomputable section
open K1_14 (FX Seeds Equation)
open HighCore82706Tangent (Input ResidueLift Factors)
open HighCore82706Tangent_3
open HighCore82706Tangent_3_2 (cutoffIdeal SeedTranscendental)
open scoped Polynomial
private theorem height_aevalTower {k R E : Type*} [Field k] [CommRing R] [CommRing E] [IsDomain E]
    [Algebra k R] [Algebra k E] (g : R →ₐ[k] E) {x : E} (hx : IsAlgebraic k x) :
    (RingHom.ker g.toRingHom).height + 1 ≤ (RingHom.ker (Polynomial.aevalTower g x).toRingHom).height := by
  let q := RingHom.ker g.toRingHom
  let Q := q.map (Polynomial.C : R →+* R[X])
  let p := RingHom.ker (Polynomial.aevalTower g x).toRingHom
  let : q.IsPrime := RingHom.ker_isPrime _
  let : Q.IsPrime := Ideal.isPrime_map_C_of_isPrime
  let : p.IsPrime := RingHom.ker_isPrime _
  have hQ : Q.under R = q := by
    ext a
    change Polynomial.C a ∈ Q ↔ a ∈ q
    rw [Ideal.mem_map_C_iff]
    constructor
    · intro h
      simpa only [Polynomial.coeff_C_zero] using h 0
    · intro h n
      cases n with
      | zero => simpa only [Polynomial.coeff_C_zero] using h
      | succ n =>
        rw [Polynomial.coeff_C_of_ne_zero (Nat.succ_ne_zero n)]
        exact q.zero_mem
  have hle : Q ≤ p := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change Polynomial.aevalTower g x (Polynomial.C a) = 0
    rwa [Polynomial.aevalTower_C]
  obtain ⟨a, ha, haz⟩ := hx.isIntegral
  let b := a.map (algebraMap k R)
  have hb : b.Monic := ha.map _
  have hbQ : b ∉ Q := by
    intro h
    exact (Ideal.one_notMem q) (by
      simpa only [Polynomial.coeff_natDegree, hb.leadingCoeff] using Ideal.mem_map_C_iff.mp h b.natDegree)
  have hbp : b ∈ p := by
    change (a.map (algebraMap k R)).eval₂ g.toRingHom x = 0
    have hcomp : g.toRingHom.comp (algebraMap k R) = algebraMap k E :=
      RingHom.ext g.commutes
    rw [Polynomial.eval₂_map, hcomp]
    exact haz
  have hlt : Q < p := lt_of_le_not_ge hle fun h => hbQ (h hbp)
  have hh := Ideal.height_under_le_height (R := R) Q
  rw [hQ] at hh
  exact (add_le_add_left hh 1).trans (Ideal.height_add_one_le_of_lt_of_isPrime hlt)
private theorem seed_height {k E : Type*} [Field k] [Field E] [Algebra k E]
    {n : ℕ} (s : Fin n → E) (hs : ∀ i, IsAlgebraic k (s i)) :
    (n : ℕ∞) ≤ (RingHom.ker (MvPolynomial.aeval s : MvPolynomial (Fin n) k →ₐ[k] E).toRingHom).height := by
  induction n with
  | zero => exact zero_le
  | succ n ih =>
    let g : MvPolynomial (Fin n) k →ₐ[k] E := MvPolynomial.aeval (fun i => s i.succ)
    let e := MvPolynomial.finSuccEquiv k n
    have he : (Polynomial.aevalTower g (s 0)).comp e.toAlgHom = MvPolynomial.aeval s := by
      apply MvPolynomial.algHom_ext
      refine Fin.cases ?_ (fun j => ?_)
      · simp [e, MvPolynomial.finSuccEquiv_X_zero]
      · simp [e, g, MvPolynomial.finSuccEquiv_X_succ]
    have hk : RingHom.ker (MvPolynomial.aeval s : MvPolynomial (Fin (n+1)) k →ₐ[k] E).toRingHom =
        (RingHom.ker (Polynomial.aevalTower g (s 0)).toRingHom).comap e.toRingEquiv := by
      rw [← he]
      apply Ideal.ext
      intro a
      simp only [RingHom.mem_ker, Ideal.mem_comap, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, AlgHom.comp_apply,
        AlgEquiv.toAlgHom_apply, AlgEquiv.coe_ringEquiv]
    rw [hk, e.toRingEquiv.height_comap, Nat.cast_succ]
    exact (add_le_add_left (ih _ fun i => hs i.succ) 1).trans (height_aevalTower g (hs 0))
private theorem height_two_extensions {k R E : Type*}
    [Field k] [CommRing R] [Field E] [Algebra k R] [Algebra k E]
    (g : R →ₐ[k] E) (y v : E) (h2 : 2 ≤ (RingHom.ker g.toRingHom).height)
    (hy : IsAlgebraic k y) (hv : IsAlgebraic k v) :
    let gy := Polynomial.aevalTower g y
    let gv := Polynomial.aevalTower gy v
    4 ≤ (RingHom.ker gv.toRingHom).height := by
  intro gy gv
  have h3 : (2 : ℕ∞) + 1 ≤ (RingHom.ker gy.toRingHom).height :=
    (add_le_add_left h2 1).trans (height_aevalTower g hy)
  calc
    (4 : ℕ∞) = (2 + 1) + 1 := by decide
    _ ≤ (RingHom.ker gy.toRingHom).height + 1 := add_le_add_left h3 1
    _ ≤ _ := height_aevalTower gy hv
private theorem jet_noetherian : IsNoetherianRing JetRing := by
  have : IsNoetherianRing FX := by
    rw [isNoetherianRing_iff_ideal_fg]
    intro I
    rcases I.eq_bot_or_top with rfl | rfl
    · exact Submodule.fg_bot
    · refine ⟨{1}, ?_⟩
      change Ideal.span (({1} : Finset FX) : Set FX) = ⊤
      simp
  have : IsNoetherianRing Seeds := MvPolynomial.isNoetherianRing_fin
  have hEquation : IsNoetherianRing Equation := Polynomial.isNoetherianRing (R := Seeds)
  exact @Polynomial.isNoetherianRing Equation _ hEquation
private theorem height_cutoff (J : Input) (B : ResidueLift J) (D : Factors J B)
    (P : Ideal JetRing) (hP : P ∈ (cutoffIdeal J B D).minimalPrimes) : P.height ≤ 3 := by
  have : IsNoetherianRing JetRing := jet_noetherian
  let G : Set JetRing := {Polynomial.C D.proper, tangentEquation J.f, Polynomial.C (HighCore82706Tangent.cutoff J B)}
  have h := Ideal.height_le_encard_of_mem_minimalPrimes_span (s := G) hP
  have hcard : G.encard ≤ 3 := by
    dsimp [G]
    refine (Set.encard_insert_le _ _).trans ?_
    refine (add_le_add_left (Set.encard_insert_le _ _) 1).trans ?_
    simp only [Set.encard_singleton]
    decide
  exact h.trans hcard
set_option maxHeartbeats 800000 in
theorem proof : HighCore82706Tangent_3_2.c2 := by
  classical
  intro J B D P hP hregular
  by_contra hseed
  let : P.IsPrime := hP.isPrime
  let A := JetRing ⧸ P
  let E := FractionRing A
  let iE : A →ₐ[FX] E := IsScalarTower.toAlgHom FX A E
  let μ : JetRing →ₐ[FX] E := iE.comp (Ideal.Quotient.mkₐ FX P)
  have hμ (q : JetRing) : μ q = 0 ↔ q ∈ P := by
    change algebraMap A E (Ideal.Quotient.mk P q) = 0 ↔ q ∈ P
    rw [map_eq_zero_iff _ (IsFractionRing.injective A E), Ideal.Quotient.eq_zero_iff_mem]
  let s (i : Fin 2) := μ (seedVar i)
  let y := μ ordinate
  let v := μ (Polynomial.X : JetRing)
  let g : Seeds →ₐ[FX] E := MvPolynomial.aeval s
  let gy : Equation →ₐ[FX] E := Polynomial.aevalTower g y
  have hgy (a : Equation) : gy a = μ (Polynomial.C a) := by
    have he : gy = μ.comp Polynomial.CAlgHom := by
      apply Polynomial.algHom_ext'
      · apply MvPolynomial.algHom_ext
        intro i
        simp [gy, g, s, seedVar]
      · simp [gy, y, ordinate]
    exact DFunLike.congr_fun he a
  have hv : (Polynomial.aevalTower gy v : JetRing →ₐ[FX] E) = μ := by
    apply Polynomial.algHom_ext'
    · exact AlgHom.ext fun a => (Polynomial.aevalTower_C gy v a).trans (hgy a)
    · exact Polynomial.aevalTower_X gy v
  have hs (i : Fin 2) : IsAlgebraic FX (s i) := by
    have ha : IsAlgebraic FX (Ideal.Quotient.mk P (seedVar i)) :=
      Classical.byContradiction fun ht => hseed ⟨i, ht⟩
    exact ha.algHom iE
  have hsep : gy J.f.derivative ≠ 0 := by
    rw [hgy]
    intro hz
    exact hregular (Ideal.mul_mem_left P _ ((hμ _).mp hz))
  have hroot : gy J.f = 0 := by
    rw [hgy, hμ, D.product, map_mul]
    exact Ideal.mul_mem_right _ _ (hP.le (Ideal.subset_span (by simp)))
  let S := Subalgebra.algebraicClosure FX E
  let gS : Seeds →ₐ[FX] S := MvPolynomial.aeval (fun i => ⟨s i, hs i⟩)
  have hgS : S.val.comp gS = g := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [gS, g]
  have hgSring : S.val.toRingHom.comp gS.toRingHom = g.toRingHom :=
    congrArg AlgHom.toRingHom hgS
  have hy : IsAlgebraic FX y := by
    have hmap : J.f.map g.toRingHom ≠ 0 := by
      intro hz
      apply hsep
      change J.f.derivative.eval₂ g.toRingHom y = 0
      rw [Polynomial.eval₂_eq_eval_map, ← Polynomial.derivative_map, hz]
      simp
    have halg : IsAlgebraic S y := by
      refine ⟨J.f.map gS.toRingHom, fun hz => hmap ?_, ?_⟩
      · rw [← hgSring, ← Polynomial.map_map, hz, Polynomial.map_zero]
      · change (J.f.map gS.toRingHom).eval₂ S.val.toRingHom y = 0
        rw [Polynomial.eval₂_map, hgSring]
        exact hroot
    exact halg.restrictScalars FX
  let gyS := Polynomial.aevalTower gS (⟨y, hy⟩ : S)
  have hgyS : S.val.comp gyS = gy := by
    apply Polynomial.algHom_ext'
    · exact AlgHom.ext fun a => by simpa [gyS, gy] using DFunLike.congr_fun hgS a
    · simp [gyS, gy]
  let a := MvPolynomial.optionEquivLeft FX (Fin 2) (K1_14_6_1.partialX (K1_14_6_1.flatten J.f))
  have halg (q : Equation) : IsAlgebraic FX (gy q) := by
    rw [← DFunLike.congr_fun hgyS q]
    exact (gyS q).property
  have hlin : gy a + v * gy J.f.derivative = 0 := by
    have ht : μ (tangentEquation J.f) = 0 := (hμ _).mpr (hP.le (Ideal.subset_span (by simp)))
    change μ (Polynomial.C a + Polynomial.X * Polynomial.C J.f.derivative) = 0 at ht
    simpa only [map_add, map_mul, ← hgy] using ht
  have hvEq : v = -gy a * (gy J.f.derivative)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (eq_div_iff hsep).mpr
    exact eq_neg_of_add_eq_zero_right hlin
  have hvAlg : IsAlgebraic FX v := by
    rw [hvEq]
    exact (halg a).neg.mul (halg J.f.derivative).inv
  have hg : 2 ≤ (RingHom.ker g.toRingHom).height := seed_height s hs
  have hV : 4 ≤ (RingHom.ker (Polynomial.aevalTower gy v).toRingHom).height :=
    height_two_extensions g y v hg hy hvAlg
  have hker : RingHom.ker μ.toRingHom = P := Ideal.ext fun q => RingHom.mem_ker.trans (hμ q)
  rw [hv, hker] at hV
  have hhi := height_cutoff J B D P hP
  exact (by decide : ¬ (4 : ℕ∞) ≤ 3) (hV.trans hhi)
end
end HighCore82706Tangent_3_2_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2_3
noncomputable section
open K1_14 (FX Seeds Equation)
open HighCore82706Tangent_3 HighCore82706Tangent_3_2 MvPolynomial
open scoped BigOperators
private abbrev Exponents (d : Degree) :=
  {m : CoxVar →₀ ℕ // Finsupp.weight coxWeight m = d}
private theorem coordinates {d : Degree} (m : Exponents d) :
    m.val h₀ + m.val h₁ + 2*m.val v₁ = d.1 ∧
    m.val v₀ + m.val v₁ = d.2.1 ∧
    m.val (tᵢ 0) + m.val (tᵢ 1) + m.val (tᵢ 2) = d.2.2 := by
  have hm := m.property
  rw [weight_coordinates] at hm
  exact ⟨congrArg Prod.fst hm, congrArg (fun x : Degree => x.2.1) hm,
    congrArg (fun x : Degree => x.2.2) hm⟩
private theorem exponent_ext {m n : CoxVar →₀ ℕ}
    (ha : m h₀ = n h₀) (hb : m h₁ = n h₁) (hc : m v₀ = n v₀) (hd : m v₁ = n v₁)
    (ht : ∀ i, m (tᵢ i) = n (tᵢ i)) : m = n := by
  apply Finsupp.ext
  intro i
  rcases i with i | (i | i)
  · fin_cases i
    · exact ha
    · exact hb
  · fin_cases i
    · exact hc
    · exact hd
  · exact ht i
private def seedLift : Seeds →+* Cox :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X (tᵢ i.castSucc))
private def rootLift : Equation →+* Cox :=
  Polynomial.eval₂RingHom seedLift (MvPolynomial.X h₁)
private def affineLift : JetRing →+* Cox :=
  Polynomial.eval₂RingHom rootLift (MvPolynomial.X v₁)
private def kept : CoxVar → Prop
  | .inl i => i ≠ 0
  | .inr (.inl i) => i ≠ 0
  | .inr (.inr i) => i.val < 2
private def surviving (m : CoxVar →₀ ℕ) : CoxVar →₀ ℕ := by
  classical
  exact m.filter kept
open scoped Classical in
private theorem lift_coord (i : CoxVar) :
    affineLift (affineCoord i) = if kept i then MvPolynomial.X i else 1 := by
  rcases i with i | (i | i) <;> fin_cases i <;>
    simp [affineCoord, affineLift, rootLift, seedLift, kept, ordinate, seedVar, h₁, v₁, tᵢ]
private theorem lift_monomial (m : CoxVar →₀ ℕ) (a : FX) :
    affineLift (dehom (monomial m a)) = monomial (surviving m) a := by
  classical
  have ha : affineLift (algebraMap FX JetRing a) = MvPolynomial.C a := by
    change affineLift (Polynomial.C (Polynomial.C (MvPolynomial.C a))) = MvPolynomial.C a
    simp [affineLift, rootLift, seedLift]
  conv_rhs => rw [monomial_eq]
  rw [dehom, aeval_monomial, map_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ha]
  apply congrArg (fun p : Cox => MvPolynomial.C a * p)
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow, lift_coord]
  by_cases hi : kept i <;> simp [surviving, hi]
private theorem surviving_injective (d : Degree) :
    Function.Injective (fun m : Exponents d => surviving m.val) := by
  intro m n he
  have same (i : CoxVar) (hi : kept i) : m.val i = n.val i := by
    simpa only [surviving, Finsupp.filter_apply, ite_eq_left hi] using
      DFunLike.congr_fun he i
  have hh := same h₁ (by change (1 : Fin 2) ≠ 0; decide)
  have hv := same v₁ (by change (1 : Fin 2) ≠ 0; decide)
  have ht₀ := same (tᵢ 0) (by change 0 < (2 : ℕ); decide)
  have ht₁ := same (tᵢ 1) (by change 1 < (2 : ℕ); decide)
  obtain ⟨hm₁, hm₂, hm₃⟩ := coordinates m
  obtain ⟨hn₁, hn₂, hn₃⟩ := coordinates n
  apply Subtype.ext
  refine exponent_ext (by omega) hh (by omega) hv (fun i => ?_)
  fin_cases i
  · exact ht₀
  · exact ht₁
  · change m.val (tᵢ 2) = n.val (tᵢ 2)
    omega
private theorem coeff_lift {d : Degree} {p : Cox} (hp : p.IsWeightedHomogeneous coxWeight d)
    (m : Exponents d) : (affineLift (dehom p)).coeff (surviving m.val) = p.coeff m.val := by
  classical
  conv_rhs => rw [p.as_sum, coeff_sum]
  conv_lhs => rw [p.as_sum, map_sum, map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := hp (mem_support_iff.mp hn)
  have he : surviving n = surviving m.val ↔ n = m.val :=
    ⟨fun h => congrArg Subtype.val (surviving_injective d (a₁ := ⟨n, hn'⟩) (a₂ := m) h),
      congrArg surviving⟩
  simp only [lift_monomial, coeff_monomial, he]
private theorem dehom_eq_of_degree {d : Degree} {p q : Cox}
    (hp : p.IsWeightedHomogeneous coxWeight d) (hq : q.IsWeightedHomogeneous coxWeight d)
    (he : dehom p = dehom q) : p = q := by
  apply MvPolynomial.ext
  intro m
  by_cases hm : Finsupp.weight coxWeight m = d
  · rw [← coeff_lift hp ⟨m, hm⟩, ← coeff_lift hq ⟨m, hm⟩, he]
  · have hp₀ : p.coeff m = 0 := by by_contra h; exact hm (hp h)
    have hq₀ : q.coeff m = 0 := by by_contra h; exact hm (hq h)
    rw [hp₀, hq₀]
private theorem ambient_rank (d : Degree) :
    Module.finrank FX (gradedPiece ⊥ d) = Nat.card (Exponents d) := by
  let S := weightedHomogeneousSubmodule FX coxWeight d
  let f := ((Ideal.Quotient.mkₐ FX (⊥ : Ideal JetRing)).comp dehom).toLinearMap
  let g : S →ₗ[FX] gradedPiece ⊥ d :=
    (f.comp S.subtype).codRestrict _ (fun p => Submodule.mem_map.mpr ⟨p.val, p.prop, rfl⟩)
  have hg : Function.Bijective g := by
    constructor
    · intro p q he
      apply Subtype.ext
      apply dehom_eq_of_degree p.prop q.prop
      have he' : Ideal.Quotient.mk ⊥ (dehom p.val) = Ideal.Quotient.mk ⊥ (dehom q.val) :=
        congrArg Subtype.val he
      simpa only [RingEquiv.quotientBot_mk] using congrArg (RingEquiv.quotientBot JetRing) he'
    · intro q
      obtain ⟨p, hp, he⟩ := Submodule.mem_map.mp q.prop
      exact ⟨⟨p, hp⟩, Subtype.ext he⟩
  rw [← (LinearEquiv.ofBijective g hg).finrank_eq]
  change Module.finrank FX (weightedHomogeneousSubmodule FX coxWeight d) = _
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport FX {m | Finsupp.weight coxWeight m = d})
private def seedSet (s : ℕ) : Finset (Fin 3 →₀ ℕ) :=
  (Finset.univ : Finset (Fin 3)).finsuppAntidiag s
private theorem mem_seedSet {z : Fin 3 →₀ ℕ} {s : ℕ} :
    z ∈ seedSet s ↔ z 0 + z 1 + z 2 = s := by
  simp [seedSet, Fin.sum_univ_three, Nat.add_assoc]
private def seedExponents (m : CoxVar →₀ ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m (tᵢ i))
private def pack (a b c d : ℕ) (z : Fin 3 →₀ ℕ) : CoxVar →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim ![a,b] (Sum.elim ![c,d] z))
private abbrev RootExponents (h t : ℕ) :=
  Σ j : Fin (t+1), Fin (h+2*j.val+1)
private def exponentEquiv (h t s : ℕ) :
    Exponents (nefDegree h t s) ≃ RootExponents h t × seedSet s where
  toFun m := by
    have hm₁ : m.val h₀ + m.val h₁ + 2*m.val v₁ = h+2*t := (coordinates m).1
    have hm₂ : m.val v₀ + m.val v₁ = t := (coordinates m).2.1
    let j : Fin (t+1) := ⟨m.val v₀, by omega⟩
    have hi : m.val h₁ < h+2*j.val+1 := by
      change m.val h₁ < h+2*m.val v₀+1
      omega
    exact ⟨⟨j, ⟨m.val h₁, hi⟩⟩,
      ⟨seedExponents m.val, mem_seedSet.mpr (coordinates m).2.2⟩⟩
  invFun p := by
    rcases p with ⟨⟨j, i⟩, z⟩
    refine ⟨pack (h+2*j.val-i.val) i.val j.val (t-j.val) z.val, ?_⟩
    have hi := i.isLt
    have hj := j.isLt
    have hz := mem_seedSet.mp z.prop
    rw [weight_coordinates]
    change (h+2*j.val-i.val+i.val+2*(t-j.val), j.val+(t-j.val),
      z.val 0+z.val 1+z.val 2) = (h+2*t, t, s)
    rw [hz]
    congr 1
    · omega
    · congr 1
      omega
  left_inv m := by
    obtain ⟨hm₁, hm₂, _⟩ := coordinates m
    change m.val h₀ + m.val h₁ + 2*m.val v₁ = h+2*t at hm₁
    change m.val v₀ + m.val v₁ = t at hm₂
    apply Subtype.ext
    refine exponent_ext ?_ rfl rfl ?_ (fun _ => rfl)
    · change h+2*m.val v₀-m.val h₁ = m.val h₀
      omega
    · change t-m.val v₀ = m.val v₁
      omega
  right_inv p := by
    rcases p with ⟨⟨j, i⟩, z⟩
    apply Prod.ext
    · exact Sigma.ext (Fin.ext rfl) (heq_of_eq (Fin.ext rfl))
    · apply Subtype.ext
      exact Finsupp.ext fun _ => rfl
private theorem sum_widths (h t : ℕ) :
    (∑ j ∈ Finset.range (t+1), (h+2*j+1)) = (t+1)*(h+t+1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    ring
private theorem seed_count (s : ℕ) : (seedSet s).card = (s+2).choose 2 := by
  rw [seedSet, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin,
    show 3+s-1 = s+2 by omega]
  exact Nat.choose_symm_of_eq_add rfl
private theorem nef_rank (h t s : ℕ) :
    hilbert ⊥ h t s = (t+1)*(h+t+1)*(s+2).choose 2 := by
  rw [hilbert, ambient_rank, Nat.card_congr (exponentEquiv h t s), Nat.card_prod, Nat.card_sigma]
  simp only [Nat.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun j => h+2*j+1), sum_widths,
    Nat.card_eq_fintype_card, Fintype.card_coe, seed_count]
theorem proof : HighCore82706Tangent_3_2.c3 := by
  refine ⟨0, fun h t s _ _ _ => ?_⟩
  change (hilbert ⊥ h t s : ℚ) = evalHilbert ambient h t s
  rw [nef_rank, Nat.cast_mul, Nat.cast_choose_two]
  push_cast
  simp [evalHilbert, ambient]
  ring
end
end HighCore82706Tangent_3_2_3
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2_5
noncomputable section
open HighCore82706Tangent_3_2 MvPolynomial
open scoped BigOperators
private abbrev Exp := Fin 3 →₀ ℕ
private def Top (n : ℕ) (p : HilbertPoly) : Prop :=
  p.totalDegree ≤ n ∧ ∀ m : Exp, m.degree = n → 0 ≤ p.coeff m
private theorem top_add {n : ℕ} {p q : HilbertPoly} (hp : Top n p) (hq : Top n q) :
    Top n (p + q) :=
  ⟨(totalDegree_add _ _).trans (max_le hp.1 hq.1),
    fun m hm => add_nonneg (hp.2 m hm) (hq.2 m hm)⟩
private theorem top_of_nonnegative {n : ℕ} {p : HilbertPoly}
    (hd : p.totalDegree ≤ n) (hp : NonnegativeTop p) : Top n p := by
  refine ⟨hd, fun m hm => ?_⟩
  rcases lt_or_eq_of_le hd with hlt | heq
  · rw [coeff_eq_zero_of_totalDegree_lt (show p.totalDegree < m.degree by omega)]
  · exact hp m (hm.trans heq.symm)
private theorem cut {n : ℕ} {p q : HilbertPoly} (hd : p.totalDegree ≤ n)
    (hq : NonnegativeTop q) (hgap : NonnegativeTop (p - q)) :
    q.totalDegree ≤ n ∧ Top n (p - q) := by
  have hqn : q.totalDegree ≤ n := by
    by_contra! h
    have hne : q ≠ 0 := by
      rintro rfl
      simp at h
    obtain ⟨m, hm, hdeg⟩ := Finset.exists_mem_eq_sup q.support (support_nonempty.mpr hne)
      (fun m => m.degree)
    change q.totalDegree = m.degree at hdeg
    have hpzero := coeff_eq_zero_of_totalDegree_lt (f := p)
      (d := m) (show p.totalDegree < m.degree by omega)
    have hdiff : (p - q).totalDegree = q.totalDegree := by
      rw [sub_eq_add_neg, totalDegree_add_eq_right_of_totalDegree_lt, totalDegree_neg]
      simpa only [totalDegree_neg] using hd.trans_lt h
    have h1 := hq m hdeg.symm
    have h2 := hgap m (hdeg.symm.trans hdiff.symm)
    rw [coeff_sub, hpzero, zero_sub] at h2
    exact (mem_support_iff.mp hm) (le_antisymm (nonpos_of_neg_nonneg h2) h1)
  exact ⟨hqn, top_of_nonnegative ((totalDegree_sub _ _).trans (max_le hd hqn)) hgap⟩
private def diffAdd (a b c : ℕ) : HilbertPoly →+ HilbertPoly where
  toFun p := difference p a b c
  map_zero' := by simp [difference]
  map_add' p q := by simp only [difference, map_add]; abel
private theorem diff_sub (p q : HilbertPoly) (a b c : ℕ) :
    difference (p - q) a b c = difference p a b c - difference q a b c :=
  map_sub (diffAdd a b c) p q
private theorem diff_mul_X (p : HilbertPoly) (a b c : ℕ) (i : Fin 3) :
    difference (p * MvPolynomial.X i) a b c =
      difference p a b c * MvPolynomial.X i + C (![a, b, c] i : ℚ) * p -
        C (![a, b, c] i : ℚ) * difference p a b c := by
  simp only [difference, map_mul, bind₁_X_right]
  ring
private theorem degree_sub_single {m : Exp} {i : Fin 3} (hi : i ∈ m.support) :
    (m - Finsupp.single i 1).degree + 1 = m.degree := by
  simpa only [map_add, Finsupp.degree_single] using
    congrArg Finsupp.degree (Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi))
private theorem diff_monomial (a b c : ℕ) (d : Exp) (r : ℚ) :
    ∀ n : ℕ, (monomial d r).totalDegree ≤ n →
      (∀ m : Exp, n ≤ m.degree → (difference (monomial d r) a b c).coeff m = 0) ∧
      ((∀ m : Exp, 0 ≤ (monomial d r).coeff m) →
        ∀ m : Exp, n = m.degree + 1 → 0 ≤ (difference (monomial d r) a b c).coeff m) := by
  refine MvPolynomial.induction_on_monomial (motive := fun p =>
    ∀ n : ℕ, p.totalDegree ≤ n →
      (∀ m : Exp, n ≤ m.degree → (difference p a b c).coeff m = 0) ∧
      ((∀ m : Exp, 0 ≤ p.coeff m) →
        ∀ m : Exp, n = m.degree + 1 → 0 ≤ (difference p a b c).coeff m)) ?_ ?_ d r
  · intro x n _
    simp [difference]
  · intro p i ih n hn
    by_cases hp : p = 0
    · subst p
      simp [difference]
    rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X] at hn
    obtain ⟨hzero, hpos⟩ := ih p.totalDegree le_rfl
    have hcoeff (m : Exp) :
        (difference (p * MvPolynomial.X i) a b c).coeff m =
          (difference p a b c * MvPolynomial.X i).coeff m + (![a, b, c] i : ℚ) * p.coeff m -
            (![a, b, c] i : ℚ) * (difference p a b c).coeff m := by
      rw [diff_mul_X, coeff_sub]
      change (difference p a b c * MvPolynomial.X i).coeff m +
        (C (![a, b, c] i : ℚ) * p).coeff m -
        (C (![a, b, c] i : ℚ) * difference p a b c).coeff m = _
      simp only [coeff_C_mul]
    constructor
    · intro m hm
      rw [hcoeff, hzero m (by omega),
        coeff_eq_zero_of_totalDegree_lt (show p.totalDegree < m.degree by omega),
        mul_zero, add_zero, sub_zero, coeff_mul_X']
      split_ifs with hi
      · have hdeg := degree_sub_single hi
        exact hzero _ (by omega)
      · rfl
    · intro h m hm
      have hpcoeff (u : Exp) : 0 ≤ p.coeff u := by
        rw [← MvPolynomial.coeff_mul_X u i p]
        exact h _
      rw [hcoeff, hzero m (by omega), mul_zero, sub_zero]
      refine add_nonneg ?_ (mul_nonneg (Nat.cast_nonneg _) (hpcoeff m))
      rw [coeff_mul_X']
      split_ifs with hi
      · have hdeg := degree_sub_single hi
        rcases lt_or_eq_of_le (show p.totalDegree ≤ (m - Finsupp.single i 1).degree + 1 by
          omega) with hlt | heq
        · rw [hzero _ (by omega)]
        · exact hpos hpcoeff _ heq
      · exact le_rfl
private theorem diff_coeff_sum (p : HilbertPoly) (a b c : ℕ) (m : Exp) :
    (difference p a b c).coeff m =
      ∑ d ∈ p.support, (difference (monomial d (p.coeff d)) a b c).coeff m := by
  change ((diffAdd a b c) p).coeff m = _
  conv_lhs => rw [p.as_sum, map_sum, coeff_sum]
  rfl
private theorem diff_le {n : ℕ} {p : HilbertPoly} (hp : p.totalDegree ≤ n + 1)
    (a b c : ℕ) : (difference p a b c).totalDegree ≤ n := by
  rw [totalDegree]
  refine Finset.sup_le fun m hm => ?_
  change m.degree ≤ n
  by_contra! h
  apply mem_support_iff.mp hm
  rw [diff_coeff_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hdeg : d.degree ≤ n + 1 := (le_totalDegree hd).trans hp
  exact (diff_monomial a b c d (p.coeff d) (n + 1) ((totalDegree_monomial_le _ _).trans hdeg)).1
    m (by omega)
private theorem diff_top {n : ℕ} {p : HilbertPoly} (hp : Top (n + 1) p)
    (a b c : ℕ) : Top n (difference p a b c) := by
  refine ⟨diff_le hp.1 a b c, fun m hm => ?_⟩
  rw [diff_coeff_sum]
  refine Finset.sum_nonneg fun d hd => ?_
  have hdeg : d.degree ≤ n + 1 := (le_totalDegree hd).trans hp.1
  have hmono : (monomial d (p.coeff d)).totalDegree ≤ d.degree :=
    totalDegree_monomial_le _ _
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · rw [(diff_monomial a b c d (p.coeff d) d.degree hmono).1 m (by omega)]
  · apply (diff_monomial a b c d (p.coeff d) d.degree hmono).2 _ m (by omega)
    intro u
    rw [coeff_monomial]
    split_ifs
    · exact hp.2 d heq
    · exact le_rfl
private theorem advance {n : ℕ} {p q r : HilbertPoly}
    (prev : Top (n + 1) (p - q)) (hq : q.totalDegree ≤ n + 1) (a b c : ℕ)
    (hr : NonnegativeTop r) (hgap : NonnegativeTop (difference q a b c - r)) :
    r.totalDegree ≤ n ∧ Top n (difference p a b c - r) := by
  obtain ⟨hd, h₁⟩ := cut (diff_le hq a b c) hr hgap
  have h₂ := diff_top prev a b c
  rw [diff_sub] at h₂
  refine ⟨hd, ?_⟩
  convert top_add h₂ h₁ using 1
  ring
private theorem ambient_le : ambient.totalDegree ≤ 4 := by
  have mul_le {p q : HilbertPoly} {m n : ℕ} (hp : p.totalDegree ≤ m)
      (hq : q.totalDegree ≤ n) : (p*q).totalDegree ≤ m+n :=
    (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)
  have add_le {p q : HilbertPoly} (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1) :
      (p+q).totalDegree ≤ 1 := (totalDegree_add _ _).trans (max_le hp hq)
  have hx (i : Fin 3) : (MvPolynomial.X i : HilbertPoly).totalDegree ≤ 1 := by simp
  have h₁ : (1 : HilbertPoly).totalDegree ≤ 1 := by simp
  have h₂ : (2 : HilbertPoly).totalDegree ≤ 1 := by
    change (C (2 : ℚ) : HilbertPoly).totalDegree ≤ 1
    simp
  have hc : (C (1/2 : ℚ) : HilbertPoly).totalDegree ≤ 0 := by simp
  exact mul_le (mul_le (mul_le (mul_le hc (add_le (hx 1) h₁))
    (add_le (add_le (hx 0) (hx 1)) h₁)) (add_le (hx 2) h₁)) (add_le (hx 2) h₂)
private theorem eval_nonneg_of_coeff (p : HilbertPoly) (x : Fin 3 → ℚ)
    (hc : ∀ m : Exp, 0 ≤ p.coeff m) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x p := by
  rw [MvPolynomial.eval_eq]
  exact Finset.sum_nonneg fun m _ => mul_nonneg (hc m)
    (Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _)
private theorem eval_top (p : HilbertPoly) (hp : Top 1 p) (h t s : ℕ) :
    p.coeff 0 ≤ evalHilbert p h t s := by
  have hc (m : Exp) : 0 ≤ (p - C (p.coeff 0)).coeff m := by
    rw [coeff_sub, coeff_C]
    split_ifs with hm
    · subst m
      rw [sub_self]
    rw [sub_zero]
    have hn : m.degree ≠ 0 := fun h => hm ((Finsupp.degree_eq_zero_iff m).mp h).symm
    by_cases h₁ : m.degree = 1
    · exact hp.2 m h₁
    · rw [coeff_eq_zero_of_totalDegree_lt (show p.totalDegree < m.degree from
        lt_of_le_of_lt hp.1 (by omega))]
  have hx (i : Fin 3) : 0 ≤ ![(h : ℚ), (t : ℚ), (s : ℚ)] i := by
    fin_cases i <;> simp
  have he := eval_nonneg_of_coeff (p - C (p.coeff 0)) _ hc hx
  rw [map_sub, eval_C] at he
  exact sub_nonneg.mp he
private abbrev evalQ (p : HilbertPoly) (x y z : ℚ) : ℚ := eval ![x, y, z] p
private theorem evalQ_diff (p : HilbertPoly) (a b c : ℕ) (x y z : ℚ) :
    evalQ (difference p a b c) x y z =
      evalQ p x y z - evalQ p (x-a) (y-b) (z-c) := by
  simp only [evalQ, difference, map_sub]
  congr 1
  change eval₂Hom (RingHom.id ℚ) _ (bind₁ _ p) = eval₂Hom (RingHom.id ℚ) _ p
  rw [eval₂Hom_bind₁]
  congr 2
  funext i
  fin_cases i <;> simp
private theorem evalQ_ambient (x y z : ℚ) :
    evalQ ambient x y z = (1/2) * (y+1) * (x+y+1) * (z+1) * (z+2) := by
  simp [evalQ, ambient]
private theorem eval_three (e v a b c h t s : ℕ) (he : 2 ≤ e) :
    let q := difference (difference (difference ambient e 0 v) (e-2) 1 v) a b c
    evalHilbert q h t s =
      ((mixedBudget e v (a+2*b) b c).eval h t s : ℚ) + evalHilbert q 0 0 0 := by
  intro q
  change evalQ q h t s = _ + evalQ q 0 0 0
  have he' : 2 ≤ 2 * e := by omega
  simp only [q, evalQ_diff, evalQ_ambient, mixedBudget, Budget.eval, Nat.cast_sub he,
    Nat.cast_sub he', Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow]
  ring
theorem proof : HighCore82706Tangent_3_2.c5 := by
  intro e v a b c he p₁ p₂ p₃ hp₁ hp₂ hp₃ hd₁ hd₂ hd₃
  obtain ⟨hb₁, h₁⟩ := cut (diff_le (n := 3) ambient_le e 0 v) hp₁ hd₁
  obtain ⟨hb₂, h₂⟩ := advance (n := 2) h₁ hb₁ (e-2) 1 v hp₂ hd₂
  obtain ⟨_, h₃⟩ := advance (n := 1) h₂ hb₂ a b c hp₃ hd₃
  let q := difference (difference (difference ambient e 0 v) (e-2) 1 v) a b c
  refine ⟨evalHilbert q 0 0 0 - (q-p₃).coeff 0, fun h t s => ?_⟩
  have hbound := eval_top (q-p₃) h₃ h t s
  have heq := eval_three e v a b c h t s he
  change (q-p₃).coeff 0 ≤ eval ![(h : ℚ), (t : ℚ), (s : ℚ)] (q-p₃) at hbound
  rw [map_sub] at hbound
  change (q-p₃).coeff 0 ≤ evalHilbert q h t s - evalHilbert p₃ h t s at hbound
  change evalHilbert q h t s = _ + evalHilbert q 0 0 0 at heq
  linarith only [hbound, heq]
end
end HighCore82706Tangent_3_2_5
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2_6
noncomputable section
open K1_14 (FX)
open HighCore82706Tangent_3 HighCore82706Tangent_3_2 MvPolynomial
open scoped BigOperators
private def diagonal (p : HilbertPoly) : Polynomial ℚ :=
  ∑ m ∈ p.support, Polynomial.monomial m.degree (p.coeff m)
private theorem eval_diagonal (p : HilbertPoly) (n : ℕ) :
    (diagonal p).eval (n : ℚ) = evalHilbert p n n n := by
  rw [diagonal, Polynomial.eval_finsetSum, evalHilbert]
  conv_rhs => rw [p.as_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Polynomial.eval_monomial, MvPolynomial.eval_monomial, Finsupp.degree_apply,
    ← Finset.prod_pow_eq_pow_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  fin_cases i <;> rfl
private theorem degree_le_one {P : Ideal JetRing} {p : HilbertPoly} {b : Budget}
    (hp : IsProfile P p) (hpos : NonnegativeTop p) (hb : HasBudget P b) :
    p.totalDegree ≤ 1 := by
  classical
  by_contra! hd
  have hs : p.support.Nonempty := support_nonempty.mpr fun hz => by
    simp [hz] at hd
  obtain ⟨m₀, hm₀, hdeg₀⟩ := p.support.exists_mem_eq_sup hs
    (fun m : Fin 3 →₀ ℕ => m.degree)
  change p.totalDegree = m₀.degree at hdeg₀
  have hcoef : 0 < (diagonal p).coeff p.totalDegree := by
    simp only [diagonal, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    apply Finset.sum_pos'
    · intro m _
      split_ifs with hm
      · exact hpos m hm
      · exact le_rfl
    · refine ⟨m₀, hm₀, ?_⟩
      rw [ite_eq_left hdeg₀.symm]
      exact (hpos m₀ hdeg₀.symm).lt_of_ne' (mem_support_iff.mp hm₀)
  obtain ⟨N, hN⟩ := hp
  obtain ⟨z, M, hM⟩ := hb
  let R : Polynomial ℚ :=
    Polynomial.C z + Polynomial.C ((b.fiber : ℚ) + b.tangent + b.seed) * Polynomial.X
  have hR (n : ℕ) : R.eval (n : ℚ) = (b.eval n n n : ℚ) + z := by
    simp [R, Budget.eval]
    ring
  have hnonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ (diagonal p).eval (n : ℚ) :=
    Filter.eventually_atTop.mpr ⟨N, fun n hn => by
      rw [eval_diagonal, ← hN n n n hn hn hn]
      exact Nat.cast_nonneg _⟩
  have hbound : ∀ᶠ n : ℕ in Filter.atTop, (diagonal p).eval (n : ℚ) ≤ R.eval (n : ℚ) :=
    Filter.eventually_atTop.mpr ⟨max N M, fun n hn => by
      have h := (le_max_left N M).trans hn
      have h' := (le_max_right N M).trans hn
      simpa only [eval_diagonal, ← hN n n n h h h, hR] using hM n n n h' h' h'⟩
  have hRdeg : R.natDegree ≤ 1 := by
    simpa only [R, add_comm] using
      (Polynomial.natDegree_linear_le (a := (b.fiber : ℚ) + b.tangent + b.seed) (b := z))
  exact (not_le_of_gt hd) ((Polynomial.le_natDegree_of_ne_zero hcoef.ne').trans
    ((Polynomial.natDegree_le_of_eventually_eval_natCast_le hnonneg hbound).1.trans hRdeg))
private def slope (p : HilbertPoly) (i : Fin 3) : ℚ :=
  p.coeff (Finsupp.single i 1)
private theorem slope_nonneg {p : HilbertPoly} (hp : p.totalDegree ≤ 1)
    (hpos : NonnegativeTop p) (i : Fin 3) : 0 ≤ slope p i := by
  by_cases h : p.totalDegree = 1
  · apply hpos
    exact (Finsupp.degree_single i 1).trans h.symm
  · have hd : p.totalDegree < (Finsupp.single i 1).degree := by
      rw [Finsupp.degree_single]
      omega
    rw [slope, MvPolynomial.coeff_eq_zero_of_totalDegree_lt hd]
private theorem eval_affine {p : HilbertPoly} (hp : p.totalDegree ≤ 1) (h t s : ℕ) :
    evalHilbert p h t s = p.coeff 0 + slope p 0 * h + slope p 1 * t + slope p 2 * s := by
  classical
  have hlinear : p = C (p.coeff 0) + C (slope p 0) * MvPolynomial.X 0 +
      C (slope p 1) * MvPolynomial.X 1 + C (slope p 2) * MvPolynomial.X 2 := by
    ext m
    by_cases hm : m.degree ≤ 1
    · rcases show m.degree = 0 ∨ m.degree = 1 by omega with hz | ho
      · rw [(Finsupp.degree_eq_zero_iff m).mp hz]
        simp [C_mul_X_eq_monomial, Finsupp.single_eq_zero]
      · obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff m).mp ho
        fin_cases i <;> simp [slope, C_mul_X_eq_monomial, Finsupp.single_eq_zero,
          Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0), eq_comm]
    · rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt (hp.trans_lt (Nat.lt_of_not_ge hm))]
      have hz : 0 ≠ m := by
        rintro rfl
        exact hm (by simp)
      have hi (i : Fin 3) : Finsupp.single i 1 ≠ m := by
        rintro rfl
        exact hm (by simp)
      simp [C_mul_X_eq_monomial, hz, hi]
  unfold evalHilbert
  conv_lhs => rw [hlinear]
  simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rfl
private theorem nat_slope {a : ℚ} {u v : ℕ} (ha : 0 ≤ a)
    (hd : (v : ℚ) = (u : ℚ) + a) : ∃ k : ℕ, (k : ℚ) = a := by
  have huv : u ≤ v := by
    exact_mod_cast (show (u : ℚ) ≤ (v : ℚ) by linarith)
  refine ⟨v - u, ?_⟩
  rw [Nat.cast_sub huv, hd, add_sub_cancel_left]
private theorem seed_pow_mem (P : Ideal JetRing) (i : Fin 2) (h t s j : ℕ) (hj : j ≤ s) :
    (Ideal.Quotient.mk P (seedVar i)) ^ j ∈ gradedPiece P (nefDegree h t s) := by
  let q : Cox := MvPolynomial.X h₀ ^ (h+2*t) * MvPolynomial.X v₀ ^ t *
    MvPolynomial.X (tᵢ i.castSucc) ^ j * MvPolynomial.X (tᵢ 2) ^ (s-j)
  refine Submodule.mem_map.mpr ⟨q, ?_, ?_⟩
  · have hw := (((isWeightedHomogeneous_X FX coxWeight h₀).pow (h+2*t)).mul
        ((isWeightedHomogeneous_X FX coxWeight v₀).pow t)).mul
        ((isWeightedHomogeneous_X FX coxWeight (tᵢ i.castSucc)).pow j)
    have hd : (h+2*t) • coxWeight h₀ + t • coxWeight v₀ + j • coxWeight (tᵢ i.castSucc) +
        (s-j) • coxWeight (tᵢ 2) = nefDegree h t s := by
      change ((h+2*t)*1 + t*0 + j*0 + (s-j)*0,
        (h+2*t)*0 + t*1 + j*0 + (s-j)*0,
        (h+2*t)*0 + t*0 + j*1 + (s-j)*1) = (h+2*t, t, s)
      simp only [mul_one, mul_zero, add_zero, zero_add, Nat.add_sub_of_le hj]
    exact hd ▸ hw.mul ((isWeightedHomogeneous_X FX coxWeight (tᵢ 2)).pow (s-j))
  · have hi : dehom (MvPolynomial.X (tᵢ i.castSucc)) = seedVar i := by
      fin_cases i <;> simp [dehom, affineCoord, tᵢ]
    change Ideal.Quotient.mk P (dehom q) = _
    have hq : dehom q = (seedVar i)^j := by
      simp [q, hi, show dehom (MvPolynomial.X h₀) = 1 by simp [dehom, affineCoord, h₀],
        show dehom (MvPolynomial.X v₀) = 1 by simp [dehom, affineCoord, v₀],
        show dehom (MvPolynomial.X (tᵢ 2)) = 1 by simp [dehom, affineCoord, tᵢ]]
    rw [hq, map_pow]
private theorem seed_bound {P : Ideal JetRing} (hseed : SeedTranscendental P) (h t s : ℕ) :
    s + 1 ≤ hilbert P h t s := by
  obtain ⟨i, hi⟩ := hseed
  let z := Ideal.Quotient.mk P (seedVar i)
  let F : Polynomial FX →ₐ[FX] JetRing ⧸ P := Polynomial.aeval z
  have hF : Function.Injective F := transcendental_iff_injective.mp hi
  have hpow : LinearIndependent FX (fun j : ℕ => z ^ j) := by
    have he : (F.toLinearMap ∘ (Polynomial.basisMonomials FX : ℕ → Polynomial FX)) =
        fun j => z ^ j := by
      funext j
      simp only [Function.comp_apply, Polynomial.coe_basisMonomials,
        Polynomial.monomial_one_right_eq_X_pow, AlgHom.toLinearMap_apply, F,
        Polynomial.aeval_X_pow]
    rw [← he]
    exact (Polynomial.basisMonomials FX).linearIndependent.map' F.toLinearMap
      (LinearMap.ker_eq_bot.mpr hF)
  let d := nefDegree h t s
  let f (j : Fin (s+1)) : gradedPiece P d :=
    ⟨z ^ j.val, seed_pow_mem P i h t s j.val (Nat.le_of_lt_succ j.isLt)⟩
  have hf : LinearIndependent FX f := LinearIndependent.of_comp (gradedPiece P d).subtype
    (hpow.comp Fin.val Fin.val_injective)
  simpa [hilbert, d] using hf.fintype_card_le_finrank
theorem proof : HighCore82706Tangent_3_2.c6 := by
  intro P p b _ hp hpos hb hseed
  have hd := degree_le_one hp hpos hb
  obtain ⟨N, hN⟩ := hp
  have hval (h t s : ℕ) (hh : N ≤ h) (ht : N ≤ t) (hs : N ≤ s) :
      (hilbert P h t s : ℚ) =
        p.coeff 0 + slope p 0 * h + slope p 1 * t + slope p 2 * s :=
    (hN h t s hh ht hs).trans (eval_affine hd h t s)
  have hbase := hval N N N le_rfl le_rfl le_rfl
  have hnext : N ≤ N+1 := Nat.le_succ _
  obtain ⟨a, ha⟩ := nat_slope (slope_nonneg hd hpos 0)
    (u := hilbert P N N N) (v := hilbert P (N+1) N N) (by
      rw [hval _ _ _ hnext le_rfl le_rfl, hbase, Nat.cast_add, Nat.cast_one]
      ring)
  obtain ⟨b', hb'⟩ := nat_slope (slope_nonneg hd hpos 1)
    (u := hilbert P N N N) (v := hilbert P N (N+1) N) (by
      rw [hval _ _ _ le_rfl hnext le_rfl, hbase, Nat.cast_add, Nat.cast_one]
      ring)
  obtain ⟨c, hc⟩ := nat_slope (slope_nonneg hd hpos 2)
    (u := hilbert P N N N) (v := hilbert P N N (N+1)) (by
      rw [hval _ _ _ le_rfl le_rfl hnext, hbase, Nat.cast_add, Nat.cast_one]
      ring)
  let z : ℤ := (hilbert P N N N : ℤ) - ((N*a + N*b' + N*c : ℕ) : ℤ)
  have hz : (z : ℚ) = p.coeff 0 := by
    dsimp only [z]
    push_cast
    rw [ha, hb', hc, hbase]
    ring
  have hlin (h t s : ℕ) (hh : N ≤ h) (ht : N ≤ t) (hs : N ≤ s) :
      (hilbert P h t s : ℤ) = ((h*a + t*b' + s*c : ℕ) : ℤ) + z := by
    have heq : (hilbert P h t s : ℚ) =
        (((h*a + t*b' + s*c : ℕ) : ℤ) : ℚ) + (z : ℚ) := by
      push_cast
      rw [ha, hb', hc, hz, hval h t s hh ht hs]
      ring
    exact_mod_cast heq
  refine ⟨⟨a, b', c, z, N, hlin⟩, ?_⟩
  change 0 < c
  apply Nat.pos_of_ne_zero
  intro hc0
  let s := N + hilbert P N N N
  have hs : N ≤ s := Nat.le_add_right _ _
  have hsame : (hilbert P N N s : ℤ) = (hilbert P N N N : ℤ) := by
    rw [hlin N N s le_rfl le_rfl hs, hlin N N N le_rfl le_rfl le_rfl, hc0]
    simp
  have hsame' : hilbert P N N s = hilbert P N N N := by exact_mod_cast hsame
  have hlarge := seed_bound hseed N N s
  rw [hsame'] at hlarge
  dsimp [s] at hlarge
  omega
end
end HighCore82706Tangent_3_2_6
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_3
noncomputable section
open P1 (I node)
open HighCore82706Tangent
open HighCore82706Tangent_3
open K1_14 (FX L seedEmbedding)
open scoped BigOperators
def nodeAt (x : I) : FX := seedEmbedding (node x)
def wordAt (J : Input) (x : I) : FX := seedEmbedding (J.model.word x)
def blockAtNode (J : Input) (x : I) : FX :=
  constantAbscissa (J.blockProduct.eval (algebraMap P1.K L (node x)))
def seedInJet (q : SeedConstants) : JetRing :=
  Polynomial.C (Polynomial.C (liftSeeds q))
def residueAtNode {J : Input} (B : ResidueLift J) (x : I) : SeedConstants :=
  B.numerator.eval (MvPolynomial.C (algebraMap P1.K L (node x)))
def residueCut (J : Input) (B : ResidueLift J) (r : ℕ) (x : I) : JetRing :=
  seedInJet (residueAtNode B x) * Polynomial.C J.f.derivative ^ (r-1)
def prefixLength (J : Input) (sites : Finset I) : ℕ :=
  J.ell + 1 - sites.card
def prefixIndex (J : Input) (sites : Finset I) (j : Fin (prefixLength J sites)) :
    Fin (J.ell + 1) :=
  j.castLE (Nat.sub_le _ _)
def sectionIndex (J : Input) (sites : Finset I) (j : Fin (prefixLength J sites)) :
    Fin (J.ell - sites.card + 1) :=
  j.castLE (by unfold prefixLength; omega)
def reconstructedValue {E : Type} [Field E] [Algebra FX E]
    (J : Input) (Lx : I → E) (jet : Fin (J.ell + 1) → E) (x : I) : E :=
  Lx x + algebraMap FX E (blockAtNode J x) *
    ∑ j : Fin (J.ell + 1), jet j * algebraMap FX E ((nodeAt x - center) ^ j.val)
def FixedWeights (J : Input) (sites : Finset I) (x : I)
    (b : I → FX) (a : Fin (prefixLength J sites) → FX) : Prop :=
  ∀ (E : Type) [Field E] [Algebra FX E] (Lx : I → E) (ν : Fin (J.ell + 1) → E),
    (∀ i ∈ sites, reconstructedValue J Lx ν i = algebraMap FX E (wordAt J i)) →
    reconstructedValue J Lx ν x - algebraMap FX E (wordAt J x) =
      (Lx x - algebraMap FX E (wordAt J x)) +
      (∑ i ∈ sites, algebraMap FX E (b i) * (algebraMap FX E (wordAt J i) - Lx i)) +
      ∑ j, algebraMap FX E (a j) * ν (prefixIndex J sites j)
def residueValue {E : Type} [Field E] [Algebra FX E]
    (φ : JetRing →ₐ[FX] E) {J : Input} (B : ResidueLift J) (x : I) : E :=
  φ (seedInJet (residueAtNode B x)) / φ (residueInJet B)
def canonicalJet {E : Type} [Field E] [Algebra FX E]
    (φ : JetRing →ₐ[FX] E) (J : Input) (B : ResidueLift J)
    (j : Fin (J.ell + 1)) : E :=
  φ (oldNumerator J B j.val) / φ (oldDenominator J B j.val)
def curveValue {E : Type} [Field E] [Algebra FX E]
    (φ : JetRing →ₐ[FX] E) (J : Input) (B : ResidueLift J) (x : I) : E :=
  reconstructedValue J (residueValue φ B) (canonicalJet φ J B) x
end
end HighCore82706Tangent_3_3
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_3
noncomputable section
open HighCore82706Tangent_3
open MvPolynomial (IsWeightedHomogeneous)
private theorem pad_degree (m n : ℕ) (d : Degree) :
    d + m • (1, 0, 0) + n • (1, 0, 0) = d + (m + n) • (1, 0, 0) := by
  rw [add_nsmul, add_assoc]
private theorem pad_degree' (m n : ℕ) (d : Degree) :
    d + n • (1, 0, 0) + m • (1, 0, 0) = d + (m + n) • (1, 0, 0) := by
  rw [pad_degree, Nat.add_comm n m]
private theorem dehom_h₀ : dehom (MvPolynomial.X h₀) = 1 := by
  simp [dehom, affineCoord, h₀]
private theorem dehom_h₁ : dehom (MvPolynomial.X h₁) = ordinate := by
  simp [dehom, affineCoord, h₁]
def sectionValues (Q : Ideal JetRing) (d : Degree) : Submodule K1_14.FX JetRing where
  carrier := {q | ∃ S : RelativeSection Q d, S.affine = q}
  zero_mem' := by
    refine ⟨⟨0, 0, 0, MvPolynomial.isWeightedHomogeneous_zero _ _ _,
      MvPolynomial.isWeightedHomogeneous_zero _ _ _, by simp⟩, ?_⟩
    exact dehom.map_zero
  add_mem' := by
    rintro _ _ ⟨S, rfl⟩ ⟨T, rfl⟩
    let h0 : Cox := MvPolynomial.X h₀
    let h1 : Cox := MvPolynomial.X h₁
    have h0w : h0.IsWeightedHomogeneous coxWeight (1,0,0) :=
      MvPolynomial.isWeightedHomogeneous_X _ _ _
    have h1w : h1.IsWeightedHomogeneous coxWeight (1,0,0) :=
      MvPolynomial.isWeightedHomogeneous_X _ _ _
    have h0a : dehom h0 = 1 := dehom_h₀
    have h1a : dehom h1 = ordinate := dehom_h₁
    refine ⟨⟨S.order+T.order,
      S.finiteChart * h0^T.order + T.finiteChart * h0^S.order,
      S.inverseChart * h1^T.order + T.inverseChart * h1^S.order, ?_, ?_, ?_⟩, ?_⟩
    · have hs := S.finite_degree.mul (h0w.pow T.order)
      have ht := T.finite_degree.mul (h0w.pow S.order)
      rw [pad_degree] at hs
      rw [pad_degree'] at ht
      exact hs.add ht
    · have hs := S.inverse_degree.mul (h1w.pow T.order)
      have ht := T.inverse_degree.mul (h1w.pow S.order)
      rw [pad_degree] at hs
      rw [pad_degree'] at ht
      exact hs.add ht
    · simp only [map_add, map_mul, map_pow, h0a, h1a, one_pow, mul_one]
      have h := Q.add_mem (Q.mul_mem_left (ordinate^T.order) S.glue)
        (Q.mul_mem_left (ordinate^S.order) T.glue)
      convert h using 1
      rw [pow_add]
      ring
    · simp only [RelativeSection.affine, map_add, map_mul, map_pow, h0a, one_pow, mul_one]
  smul_mem' := by
    rintro a _ ⟨S, rfl⟩
    refine ⟨⟨S.order, MvPolynomial.C a * S.finiteChart, MvPolynomial.C a * S.inverseChart,
      S.finite_degree.C_mul a, S.inverse_degree.C_mul a, ?_⟩, ?_⟩
    · simp only [map_mul]
      have h := Q.mul_mem_left (dehom (MvPolynomial.C a)) S.glue
      convert h using 1; ring
    · change dehom (MvPolynomial.C a * S.finiteChart) = a • dehom S.finiteChart
      rw [map_mul, Algebra.smul_def]
      congr 1
      simp [dehom]
theorem affine_mem {Q : Ideal JetRing} {d : Degree} (S : RelativeSection Q d) :
    S.affine ∈ sectionValues Q d :=
  ⟨S, rfl⟩
end
end HighCore82706Tangent_3_3
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_3
noncomputable section
open P1 (I)
open HighCore82706Tangent
open HighCore82706Tangent_3
open K1_14 (FX Equation SeedBound)
open K1_14_6_1 (box box_pow flatten separant separant_bound)
open MvPolynomial
open private K1_14_6_1.flatten_bound from ProximityPrize.SubmissionLower.Fast055
private theorem residue_degree {J : Input} (B : ResidueLift J) (x : I) :
    (residueAtNode B x).totalDegree ≤ 2 * J.w := by
  classical
  unfold residueAtNode
  rw [Polynomial.eval_eq_sum_range]
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by
    rw [← map_pow, totalDegree_C, Nat.add_zero]
    exact B.numerator_degree i)
private theorem rootInJet_flatten (f : Equation) :
    rootInJet (flatten f) = Polynomial.C f := by
  simp [rootInJet, flatten]
private theorem rootInJet_separant (f : Equation) :
    rootInJet (separant (flatten f)) = Polynomial.C f.derivative := by
  simp [rootInJet, flatten, separant, MvPolynomial.optionEquivLeft_pderiv_none]
theorem residue_section (J : Input) (B : ResidueLift J) (D : Factors J B) (r : ℕ) (x : I) :
    ∃ S : RelativeSection (graphIdeal J B D) (jetDegree J r),
      S.affine = residueCut J B r x := by
  let a := 1 + (J.e-3)*r + 2*r
  let c := r*J.v + 2*J.w
  let N : Equation := Polynomial.C (liftSeeds (residueAtNode B x))
  have hN : SeedBound N (2 * J.w) := by
    intro i
    cases i with
    | zero =>
      rw [show N.coeff 0 = liftSeeds (residueAtNode B x) from Polynomial.coeff_C_zero]
      have hmap : (liftSeeds (residueAtNode B x)).totalDegree ≤ (residueAtNode B x).totalDegree :=
        Finset.sup_mono (support_map_subset constantAbscissa _)
      exact hmap.trans (residue_degree B x)
    | succ i =>
      rw [show N.coeff (i+1) = 0 from Polynomial.coeff_C_succ, totalDegree_zero]
      exact Nat.zero_le _
  have hs := separant_bound (f := J.f) (le_refl J.e) J.seed_bound
  have hmul := mul_mem_restrictBidegree
    (K1_14_6_1.flatten_bound (show N.natDegree ≤ 0 by simp [N]) hN) (box_pow hs (r-1))
  have ha : (r-1)*(J.e-1) ≤ a := by
    apply (Nat.mul_le_mul_right _ (Nat.sub_le r 1)).trans
    have he : J.e-1 = (J.e-3)+2 := by
      have h : 3 ≤ J.e := J.sheets
      omega
    rw [he, Nat.mul_add, Nat.mul_comm r (J.e-3), Nat.mul_comm r 2]
    unfold a
    omega
  have hc : 2*J.w + (r-1)*J.v ≤ c :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le r 1)) _).trans_eq (Nat.add_comm _ _)
  have hbox : flatten N * separant (flatten J.f)^(r-1) ∈ box a c :=
    mem_restrictBidegree_mono hmul (by simpa only [Nat.zero_add] using ha) hc
  obtain ⟨P, hP, he⟩ := homogenizeBiform hbox
  let V : Cox := MvPolynomial.X v₀
  have hv : V.IsWeightedHomogeneous coxWeight (0,1,0) :=
    isWeightedHomogeneous_X FX coxWeight v₀
  have hdeg : (P * V^r).IsWeightedHomogeneous coxWeight
      (jetDegree J r + 0 • (1, 0, 0)) := by
    simpa [jetDegree, nefDegree, a, c, Prod.smul_mk] using hP.mul (hv.pow r)
  refine ⟨⟨0, P * V^r, P * V^r, hdeg, hdeg, by simp⟩, ?_⟩
  have hv₀ : dehom V = 1 := by simp [V, dehom, affineCoord, v₀]
  change dehom (P * V^r) = _
  rw [map_mul, map_pow, hv₀, one_pow, mul_one, he, map_mul, map_pow,
    rootInJet_flatten, rootInJet_separant]
  rfl
end
end HighCore82706Tangent_3_3
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_3
noncomputable section
open P1 (K I node)
open HighCore82706Tangent
open HighCore82706Tangent_3
open K1_14 (FX seedEmbedding)
open scoped BigOperators
open HighCore82706Tangent_3 (oldDenominator_eq)
def c1 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (γ : K), γ ∈ J.marks →
    markPoint J γ (openFactor J B) ≠ 0 ∧
    ∀ x : I, curveValue (markPoint J γ) J B x =
      seedEmbedding ((J.family.scalar γ).eval (node x))
def c2 : Prop :=
  ∀ (J : Input) (sites : Finset I) (x : I),
    ∃ b : I → FX, ∃ a : Fin (prefixLength J sites) → FX, FixedWeights J sites x b a
private theorem denominator_nonzero {E : Type} [Field E] [Algebra FX E]
    (φ : JetRing →ₐ[FX] E) (J : Input) (B : ResidueLift J)
    (hu : φ (openFactor J B) ≠ 0) :
    ∀ z : ℕ, φ (residueInJet B * Polynomial.C J.f.derivative ^ z) ≠ 0 := by
  rw [openFactor, map_mul, mul_ne_zero_iff] at hu
  intro z
  rw [map_mul, map_pow]
  exact mul_ne_zero hu.1 (pow_ne_zero _ hu.2)
private theorem normalize_residue {E : Type} [Field E] [Algebra FX E]
    (φ : JetRing →ₐ[FX] E) {J : Input} {B : ResidueLift J} {D : Factors J B} {r : ℕ}
    (T : TaylorSections J B D r) (hu : φ (openFactor J B) ≠ 0) (x : I) :
    φ (residueCut J B r x) / φ T.denominator.affine = residueValue φ B x := by
  have hden := denominator_nonzero φ J B hu
  rw [T.den_eq, jetDenominator, residueValue]
  apply (div_eq_div_iff (hden _) (by simpa only [pow_zero, mul_one] using hden 0)).2
  simp only [residueCut, map_mul, map_pow]
  ring
private theorem normalize_jet {E : Type} [Field E] [Algebra FX E]
    (φ : JetRing →ₐ[FX] E) {J : Input} {B : ResidueLift J} {D : Factors J B}
    (sites : Finset I) (T : TaylorSections J B D (J.ell - sites.card))
    (hu : φ (openFactor J B) ≠ 0) (hz : ∀ q ∈ graphIdeal J B D, φ q = 0)
    (j : Fin (prefixLength J sites)) :
    φ (T.numerator (sectionIndex J sites j)).affine / φ T.denominator.affine =
      canonicalJet φ J B (prefixIndex J sites j) := by
  have hden := denominator_nonzero φ J B hu
  unfold canonicalJet
  have h₁ : φ T.denominator.affine ≠ 0 := by rw [T.den_eq, jetDenominator]; exact hden _
  have h₂ : φ (oldDenominator J B (prefixIndex J sites j).val) ≠ 0 := by
    rw [oldDenominator_eq]; exact hden _
  apply (div_eq_div_iff h₁ h₂).2
  have h := hz _ (T.agrees (sectionIndex J sites j))
  rw [map_sub, map_mul, map_mul, sub_eq_zero, mul_comm (φ (oldDenominator J B _))] at h
  exact h
private def cut {J : Input} {B : ResidueLift J} {D : Factors J B} (sites : Finset I)
    (T : TaylorSections J B D (J.ell - sites.card)) (x : I)
    (b : I → FX) (a : Fin (prefixLength J sites) → FX) : JetRing :=
  let r := J.ell - sites.card
  let d := T.denominator.affine
  (residueCut J B r x - wordAt J x • d) +
    (∑ i ∈ sites, b i • (wordAt J i • d - residueCut J B r i)) +
    ∑ j, a j • (T.numerator (sectionIndex J sites j)).affine
private theorem normalize_cut {E : Type} [Field E] [Algebra FX E]
    (φ : JetRing →ₐ[FX] E) {J : Input} {B : ResidueLift J} {D : Factors J B}
    (sites : Finset I) (T : TaylorSections J B D (J.ell - sites.card))
    (hu : φ (openFactor J B) ≠ 0) (hz : ∀ q ∈ graphIdeal J B D, φ q = 0)
    (x : I) (b : I → FX) (a : Fin (prefixLength J sites) → FX) :
    φ (cut sites T x b a) / φ T.denominator.affine =
      (residueValue φ B x - algebraMap FX E (wordAt J x)) +
      (∑ i ∈ sites, algebraMap FX E (b i) * (algebraMap FX E (wordAt J i) - residueValue φ B i)) +
      ∑ j, algebraMap FX E (a j) * canonicalJet φ J B (prefixIndex J sites j) := by
  classical
  have hden : φ T.denominator.affine ≠ 0 := by
    rw [T.den_eq, jetDenominator]
    exact denominator_nonzero φ J B hu _
  have heval (a : FX) (q : JetRing) : φ (a • q) = algebraMap FX E a * φ q := by
    rw [Algebra.smul_def, map_mul, AlgHom.commutes]
  simp only [cut, map_add, map_sub, map_sum, heval, add_div, sub_div, Finset.sum_div,
    mul_div_assoc, div_self hden, mul_one, normalize_residue φ T hu,
    normalize_jet φ sites T hu hz]
set_option maxHeartbeats 500000 in
theorem of_children (specialize : c1) (weights : c2) : HighCore82706Tangent_3.c3 := by
  classical
  intro J B D tuple C
  haveI : C.prime.IsPrime := C.isPrime
  let R := JetRing ⧸ C.prime
  let E := FractionRing R
  let q : JetRing →+* E := (algebraMap R E).comp (Ideal.Quotient.mk C.prime)
  let curveAlgebra : Algebra FX E := (q.comp (algebraMap FX JetRing)).toAlgebra
  letI := curveAlgebra
  let φ : JetRing →ₐ[FX] E := ⟨q, fun _ => rfl⟩
  have hvanish (f : JetRing) : φ f = 0 ↔ f ∈ C.prime := by
    change algebraMap R E (Ideal.Quotient.mk C.prime f) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective R E), Ideal.Quotient.eq_zero_iff_mem]
  have hφopen : φ (openFactor J B) ≠ 0 := fun h => C.regular ((hvanish _).mp h)
  have hφgraph : ∀ f ∈ graphIdeal J B D, φ f = 0 :=
    fun f hf => (hvanish f).mpr (C.onGraph hf)
  let sites := Finset.univ.filter fun i : I => curveValue φ J B i = algebraMap FX E (wordAt J i)
  have hsites (i : I) :
      i ∈ sites ↔ curveValue φ J B i = algebraMap FX E (wordAt J i) := by
    simp [sites]
  let r := J.ell - sites.card
  have hr : r ≤ J.ell := Nat.sub_le _ _
  let T := tuple r (hr.trans (Nat.le_succ _))
  let V := sectionValues (graphIdeal J B D) (jetDegree J r)
  have hres (i : I) : residueCut J B r i ∈ V := residue_section J B D r i
  have hden : T.denominator.affine ∈ V := affine_mem _
  have hmarkzero (γ : K) (hγ : γ ∈ C.marks) (f : JetRing)
      (hf : f ∈ graphIdeal J B D) : markPoint J γ f = 0 :=
    C.liesOn γ hγ (C.onGraph hf)
  have eval_cut {E' : Type} [Field E'] [Algebra FX E']
      (ψ : JetRing →ₐ[FX] E') (S : Finset I) (U : TaylorSections J B D (J.ell - S.card))
      (ho : ψ (openFactor J B) ≠ 0) (hg : ∀ f ∈ graphIdeal J B D, ψ f = 0)
      (x : I) (b : I → FX) (a : Fin (prefixLength J S) → FX)
      (hw : FixedWeights J S x b a)
      (hs : ∀ i ∈ S, curveValue ψ J B i = algebraMap FX E' (wordAt J i)) :
      ψ (cut S U x b a) / ψ U.denominator.affine =
        curveValue ψ J B x - algebraMap FX E' (wordAt J x) :=
    (normalize_cut ψ S U ho hg x b a).trans
      (hw E' (residueValue ψ B) (canonicalJet ψ J B) hs).symm
  have hresolved (γ : K) (hγ : γ ∈ C.marks) (i : I) (hi : i ∈ sites) :
      curveValue (markPoint J γ) J B i = wordAt J i := by
    let empty : Finset I := ∅
    let U := tuple (J.ell - empty.card) ((Nat.sub_le _ _).trans (Nat.le_succ _))
    obtain ⟨b, a, hw⟩ := weights J empty i
    have hn : φ U.denominator.affine ≠ 0 := by
      rw [U.den_eq, jetDenominator]
      exact denominator_nonzero φ J B hφopen _
    have hg := eval_cut φ empty U hφopen hφgraph i b a hw (by simp [empty])
    rw [(hsites i).mp hi, sub_self] at hg
    have hmem := (hvanish _).mp ((div_eq_zero_iff.mp hg).resolve_right hn)
    have hpt : markPoint J γ (cut empty U i b a) = 0 := C.liesOn γ hγ hmem
    have hm := eval_cut (markPoint J γ) empty U
      (specialize J B γ (C.sub hγ)).1 (hmarkzero γ hγ) i b a hw (by simp [empty])
    rw [hpt, zero_div, eq_comm, sub_eq_zero] at hm
    simpa using hm
  refine ⟨⟨sites, ?_, ?_⟩⟩
  · intro γ hγ x hx
    have he := hresolved γ hγ x hx
    rw [(specialize J B γ (C.sub hγ)).2 x] at he
    exact seedEmbedding.injective he
  · intro x hx
    obtain ⟨b, a, hw⟩ := weights J sites x
    have hc : cut sites T x b a ∈ V := by
      apply V.add_mem
      · apply V.add_mem
        · exact V.sub_mem (hres x) (V.smul_mem _ hden)
        · exact Submodule.sum_mem V fun i _ =>
            V.smul_mem _ (V.sub_mem (V.smul_mem _ hden) (hres i))
      · exact Submodule.sum_mem V fun j _ => V.smul_mem _ (affine_mem _)
    obtain ⟨S, hS⟩ := hc
    refine ⟨S.restrict C.onGraph, ?_, ?_⟩
    · change S.affine ∉ C.prime
      rw [hS]
      intro h
      have he := eval_cut φ sites T hφopen hφgraph x b a hw (fun i => (hsites i).mp)
      rw [(hvanish _).mpr h, zero_div, eq_comm, sub_eq_zero] at he
      exact hx ((hsites x).mpr he)
    · intro γ hγ hhit
      change markPoint J γ S.affine = 0
      rw [hS]
      have hs : ∀ i ∈ sites,
          curveValue (markPoint J γ) J B i = algebraMap FX FX (wordAt J i) :=
        fun i hi => by simpa using hresolved γ hγ i hi
      have he := eval_cut (markPoint J γ) sites T (specialize J B γ (C.sub hγ)).1
        (hmarkzero γ hγ) x b a hw hs
      have hv := (specialize J B γ (C.sub hγ)).2 x
      rw [hhit] at hv
      rw [hv, Algebra.algebraMap_self, RingHom.id_apply, wordAt, sub_self] at he
      exact (div_eq_zero_iff.mp he).resolve_right (by
        rw [T.den_eq, jetDenominator]
        exact denominator_nonzero _ J B (specialize J B γ (C.sub hγ)).1 _)
end
end HighCore82706Tangent_3_3
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_5
noncomputable section
open Polynomial
open P1 (K)
open K1_14 (FX Seeds Equation atX graphEval seedEmbedding)
open HighCore82706Tangent (Input ResidueLift SeedClosure intoSeedClosure center reconstructed genericRoots rootOn)
def atAbscissa (a : FX) : Polynomial (Polynomial Seeds) →+* Equation :=
  Polynomial.mapRingHom (Polynomial.evalRingHom (MvPolynomial.C a))
def embedFX : FX →+* SeedClosure := intoSeedClosure.comp MvPolynomial.C
def evalRoot (y : SeedClosure) : Equation →+* SeedClosure := eval₂RingHom intoSeedClosure y
def evalMark (J : Input) (γ : K) : Equation →+* FX :=
  eval₂RingHom (graphEval (J.model.label γ)) (atX (J.family.scalar γ))
structure RegularValues (J : Input) (B : ResidueLift J) (q : Equation) where
  denominator : Equation
  numerator : K → Equation
  generic_value : ∀ y ∈ genericRoots q, ∀ x : K,
    evalRoot y (numerator x) = evalRoot y denominator *
      (reconstructed J B y).eval (embedFX (seedEmbedding x))
  marked_value : ∀ γ ∈ J.marks, rootOn J q γ →
    evalMark J γ denominator ≠ 0 ∧ ∀ x : K,
      evalMark J γ (numerator x) = evalMark J γ denominator *
        seedEmbedding ((J.family.scalar γ).eval x)
structure BoundedProduct (J : Input) (B : ResidueLift J) (q : Equation) where
  numerator : Polynomial (Polynomial Seeds)
  degree : ∀ i j, ((numerator.coeff i).coeff j).totalDegree ≤ K1_14_4.seedDegree q
  identity : numerator.map (Polynomial.mapRingHom intoSeedClosure) =
    C (C (intoSeedClosure q.leadingCoeff)) *
      ∏ y ∈ genericRoots q, (Polynomial.X - C (reconstructed J B y))
def CoeffConstant (a : Seeds) : Prop :=
  ∀ s, K1_14_6_1.Dx (a.coeff s) = 0
end
end HighCore82706Tangent_5
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_5
noncomputable section
open Polynomial
open P1 (K I node)
open K1_14 (FX Seeds Equation seedEmbedding graphEval)
open P1_7 (Reduced)
open HighCore82706Tangent (Input ResidueLift SeedField SeedClosure intoSeedClosure reconstructed genericRoots
  generic rootOn FlatSections)
theorem atAbscissa_eval {a : FX} (P : Polynomial (Polynomial Seeds)) :
    (atAbscissa a P).map intoSeedClosure =
      (P.map (Polynomial.mapRingHom intoSeedClosure)).map (evalRingHom (embedFX a)) := by
  ext i
  simp only [atAbscissa, coe_mapRingHom, Polynomial.coeff_map]
  change intoSeedClosure ((P.coeff i).eval (MvPolynomial.C a)) =
    ((P.coeff i).map intoSeedClosure).eval (embedFX a)
  exact (Polynomial.eval_map_apply (p := P.coeff i) intoSeedClosure _).symm
theorem evaluated_product {J : Input} {B : ResidueLift J} {q : Equation}
    {N : Polynomial (Polynomial Seeds)} {den : Seeds}
    (hN : N.map (Polynomial.mapRingHom intoSeedClosure) =
      C (C (intoSeedClosure den)) * ∏ y ∈ genericRoots q,
        (Polynomial.X - C (reconstructed J B y))) (x : FX) :
    (atAbscissa x N).map intoSeedClosure =
      C (intoSeedClosure den) * ∏ y ∈ genericRoots q,
        (Polynomial.X - C ((reconstructed J B y).eval (embedFX x))) := by
  rw [atAbscissa_eval, hN]
  change Polynomial.mapRingHom (evalRingHom (embedFX x)) (_ * _) = _
  simp only [map_mul, map_prod, map_sub, coe_mapRingHom, map_C, map_X, coe_evalRingHom,
    eval_C]
private theorem coeff_degree_eval (F : Polynomial Seeds) (a : FX) (u : ℕ)
    (hF : K1_14.SeedBound F u) : (F.eval (MvPolynomial.C a)).totalDegree ≤ u := by
  classical
  rw [Polynomial.eval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    rw [← map_pow, MvPolynomial.totalDegree_C, Nat.add_zero]
    exact hF i)
private theorem abscissa_degree {J : Input} {B : ResidueLift J} {q : Equation}
    (G : BoundedProduct J B q) (a : FX) :
    K1_14.SeedBound (atAbscissa a G.numerator) (K1_14_4.seedDegree q) := by
  intro i
  simp only [atAbscissa, coe_mapRingHom, coeff_map, coe_evalRingHom]
  exact coeff_degree_eval (G.numerator.coeff i) a _ (G.degree i)
theorem intoSeedClosure_injective : Function.Injective intoSeedClosure :=
  (algebraMap SeedField SeedClosure).injective.comp
    (IsFractionRing.injective Seeds SeedField)
private theorem root_of_mem {q : Equation} {y : SeedClosure} (h : y ∈ genericRoots q) :
    evalRoot y q = 0 := by
  classical
  have hy : y ∈ (q.map intoSeedClosure).roots := Multiset.mem_toFinset.mp h
  simpa only [evalRoot, coe_eval₂RingHom, ← eval_map, IsRoot] using isRoot_of_mem_roots hy
private theorem mem_genericRoots {q : Equation} (hq : 0 < q.natDegree) :
    (genericRoots q).Nonempty := by
  classical
  have hsplit := IsAlgClosed.splits (q.map intoSeedClosure)
  have hd : 0 < (q.map intoSeedClosure).natDegree := by
    rwa [natDegree_map_eq_of_injective intoSeedClosure_injective]
  rw [genericRoots, Finset.nonempty_iff_ne_empty]
  intro hz
  have hcard := (Multiset.toFinset_eq_empty.mp hz)
  rw [hsplit.natDegree_eq_card_roots, hcard, Multiset.card_zero] at hd
  exact (Nat.lt_irrefl 0) hd
private theorem dvd_of_generic_zero {q H : Equation} (hprim : q.IsPrimitive)
    (hirr : Irreducible (generic q)) {y : SeedClosure} (hy : y ∈ genericRoots q)
    (hH : evalRoot y H = 0) : q ∣ H := by
  apply hprim.dvd_of_fraction_map_dvd_fraction_map (K := SeedField)
  change generic q ∣ generic H
  apply hirr.dvd_iff_not_isCoprime.mpr
  rintro ⟨A, B, hab⟩
  let ev := eval₂RingHom (algebraMap SeedField SeedClosure) y
  have hcomp (T : Equation) : ev (generic T) = evalRoot y T := by
    simp only [ev, generic, coe_eval₂RingHom, eval₂_map, evalRoot, intoSeedClosure]
  have h := congrArg ev hab
  simp only [map_add, map_mul, map_one, hcomp, root_of_mem hy, hH, mul_zero, add_zero] at h
  exact zero_ne_one h
private theorem marked_zero {J : Input} {q H : Equation} {γ : K} (hq : rootOn J q γ)
    (hd : q ∣ H) : evalMark J γ H = 0 := by
  obtain ⟨T, rfl⟩ := hd
  have hr : evalMark J γ q = 0 := hq
  rw [_root_.map_mul, hr, zero_mul]
private theorem eval_homogeneous {R S : Type*} [CommRing R] [CommRing S]
    (F : R[X]) (num den : R) (φ : R →+* S) (v : S) (hv : φ num = φ den * v) :
    φ ((F.scaleRoots den).eval num) = (φ den)^F.natDegree * F.eval₂ φ v := by
  rw [← eval₂_id, Polynomial.hom_eval₂, RingHom.comp_id, hv, scaleRoots_eval₂_mul]
theorem flat_sections {J : Input} {B : ResidueLift J} {q : Equation}
    (hq : Reduced q) (hirr : Irreducible (generic q))
    (R : RegularValues J B q) (G : BoundedProduct J B q) : FlatSections J q := by
  classical
  intro x hmiss
  let a := seedEmbedding (node x)
  let b := seedEmbedding (J.model.word x)
  let F := atAbscissa a G.numerator
  let g := F.eval (MvPolynomial.C b)
  have hg_eval : intoSeedClosure g = intoSeedClosure q.leadingCoeff *
      ∏ y ∈ genericRoots q, (embedFX b - (reconstructed J B y).eval (embedFX a)) := by
    rw [show intoSeedClosure g = (F.map intoSeedClosure).eval (embedFX b) by
      exact (Polynomial.eval_map_apply (p := F) intoSeedClosure _).symm, evaluated_product G.identity a]
    simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  have hq0 : q ≠ 0 := fun hz => hq.1.ne' (hz ▸ natDegree_zero)
  have hlead : intoSeedClosure q.leadingCoeff ≠ 0 :=
    (map_ne_zero_iff _ intoSeedClosure_injective).mpr (leadingCoeff_ne_zero.mpr hq0)
  refine ⟨g, ?_, coeff_degree_eval F b _ (abscissa_degree G a), ?_⟩
  · intro hg
    rw [hg, map_zero] at hg_eval
    have hh := (mul_eq_zero.mp hg_eval.symm).resolve_left hlead
    obtain ⟨y, hy, hyb⟩ := Finset.prod_eq_zero_iff.mp hh
    let H := R.numerator (node x) - C (MvPolynomial.C b) * R.denominator
    have hH : evalRoot y H = 0 := by
      simp only [H, evalRoot, coe_eval₂RingHom, eval₂_sub, eval₂_mul, eval₂_C]
      change evalRoot y (R.numerator (node x)) - embedFX b * evalRoot y R.denominator = 0
      rw [R.generic_value y hy, ← sub_eq_zero.mp hyb, mul_comm, sub_self]
    obtain ⟨γ, hγ, hqγ, hm⟩ := hmiss
    obtain ⟨hden, hnum⟩ := R.marked_value γ hγ hqγ
    have hz := marked_zero hqγ (dvd_of_generic_zero hq.2.1 hirr hy hH)
    change evalMark J γ H = 0 at hz
    simp only [H, evalMark, coe_eval₂RingHom, eval₂_sub, eval₂_mul, eval₂_C,
      graphEval, MvPolynomial.eval_C] at hz
    change evalMark J γ (R.numerator (node x)) - b * evalMark J γ R.denominator = 0 at hz
    rw [hnum, mul_comm b, ← mul_sub] at hz
    exact hm (seedEmbedding.injective (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hden)))
  · intro γ hγ hqγ hhit
    let T : Polynomial Equation := F.map (Polynomial.C : Seeds →+* Equation)
    let n := R.numerator (node x)
    let d := R.denominator
    let H := (T.scaleRoots d).eval n
    obtain ⟨y, hy⟩ := mem_genericRoots hq.1
    let v := (reconstructed J B y).eval (embedFX a)
    have heval (φ : Equation →+* SeedClosure)
        (hφ : φ.comp (Polynomial.C : Seeds →+* Equation) = intoSeedClosure) :
        T.eval₂ φ v = (F.map intoSeedClosure).eval v := by
      dsimp only [T]
      rw [eval₂_map, hφ, eval_map]
    have hφ : (evalRoot y).comp (Polynomial.C : Seeds →+* Equation) = intoSeedClosure := by
      apply RingHom.ext
      intro s
      exact eval₂_C _ _
    have hH : evalRoot y H = 0 := by
      dsimp only [H]
      rw [eval_homogeneous T n d _ v (R.generic_value y hy _), heval _ hφ,
        evaluated_product G.identity a, eval_mul, eval_prod]
      have hv : (∏ z ∈ genericRoots q,
          (Polynomial.X - C ((reconstructed J B z).eval (embedFX a))).eval v) = 0 :=
        Finset.prod_eq_zero hy (by simp [v])
      rw [hv, mul_zero, mul_zero]
    have hz := marked_zero hqγ (dvd_of_generic_zero hq.2.1 hirr hy hH)
    obtain ⟨hden, hnum⟩ := R.marked_value γ hγ hqγ
    have hnb : evalMark J γ n = evalMark J γ d * b := by
      dsimp only [n, d, b]
      rw [hnum, hhit]
    have hφγ : (evalMark J γ).comp (Polynomial.C : Seeds →+* Equation) =
        graphEval (J.model.label γ) := by
      apply RingHom.ext
      intro s
      exact eval₂_C _ _
    dsimp only [H] at hz
    rw [eval_homogeneous T n d _ b hnb] at hz
    dsimp only [T] at hz
    rw [eval₂_map, hφγ] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hden)
    change graphEval _ (F.eval (MvPolynomial.C b)) = 0
    rw [← eval₂_id, hom_eval₂, RingHom.comp_id]
    simpa only [graphEval, MvPolynomial.eval_C] using hzero
end
end HighCore82706Tangent_5
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_5
noncomputable section
open Polynomial
open K1_14 (L FX Seeds Equation)
open K1_14_6 (Biform)
open P1_7 (Reduced)
open HighCore82706Tangent (Input ResidueLift SeedConstants SeedClosure intoSeedClosure center reconstructed
  genericRoots generic liftConstantSeeds seedBiform liftSeeds constantAbscissa liftTaylor
  inverseBlockCoeff ordinateTaylorNum quotientNumerator quotientDenominator DifferentialProduct)
private theorem genericPoint_C (y : SeedClosure) (a : FX) :
    HighCore82706Tangent.genericPoint y (MvPolynomial.C a) = embedFX a := by
  change eval₂ intoSeedClosure y (MvPolynomial.optionEquivLeft FX (Fin 2) (MvPolynomial.C a)) = _
  rw [MvPolynomial.optionEquivLeft_C, eval₂_C]
  rfl
private theorem genericPoint_Y (y : SeedClosure) :
    HighCore82706Tangent.genericPoint y (MvPolynomial.X (R := FX) (none : Option (Fin 2))) = y := by
  change eval₂ intoSeedClosure y (MvPolynomial.optionEquivLeft FX (Fin 2) (MvPolynomial.X none)) = _
  rw [MvPolynomial.optionEquivLeft_X_none, eval₂_X]
private theorem genericPoint_seed (y : SeedClosure) :
    (HighCore82706Tangent.genericPoint y).comp seedBiform = liftConstantSeeds := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change HighCore82706Tangent.genericPoint y (MvPolynomial.rename some (MvPolynomial.map constantAbscissa
      (MvPolynomial.C a))) = intoSeedClosure (MvPolynomial.map constantAbscissa (MvPolynomial.C a))
    rw [MvPolynomial.map_C, MvPolynomial.rename_C, genericPoint_C]
    rfl
  · intro i
    change HighCore82706Tangent.genericPoint y (MvPolynomial.rename some (MvPolynomial.map constantAbscissa
      (MvPolynomial.X i))) = intoSeedClosure (MvPolynomial.map constantAbscissa (MvPolynomial.X i))
    rw [MvPolynomial.map_X, MvPolynomial.rename_X]
    change eval₂ intoSeedClosure y (MvPolynomial.optionEquivLeft FX (Fin 2)
      (MvPolynomial.X (some i))) = _
    rw [MvPolynomial.optionEquivLeft_X_some, eval₂_C]
private theorem taylor_zero (B : Polynomial SeedConstants) (y : SeedClosure) :
    HighCore82706Tangent.genericPoint y (liftTaylor B 0) = (B.map liftConstantSeeds).eval (embedFX center) := by
  rw [liftTaylor, taylor_coeff_zero, ← eval₂_id, hom_eval₂, RingHom.comp_id,
    eval₂_map, genericPoint_seed, genericPoint_C, eval_map]
private theorem seed_nonzero {D : SeedConstants} (hD : D ≠ 0) : liftConstantSeeds D ≠ 0 := by
  have hψ : Function.Injective constantAbscissa :=
    (IsFractionRing.injective L[X] FX).comp Polynomial.C_injective
  have hι : Function.Injective liftConstantSeeds :=
    intoSeedClosure_injective.comp (MvPolynomial.map_injective _ hψ)
  exact (map_ne_zero_iff _ hι).mpr hD
private theorem eval_block (J : Input) :
    (J.blockProduct.map (liftConstantSeeds.comp MvPolynomial.C)).eval (embedFX center) =
      embedFX (algebraMap L[X] FX J.blockProduct) := by
  have hc : liftConstantSeeds.comp MvPolynomial.C = embedFX.comp constantAbscissa := by
    apply RingHom.ext
    intro a
    change intoSeedClosure (MvPolynomial.map constantAbscissa (MvPolynomial.C a)) = _
    rw [MvPolynomial.map_C]
    rfl
  rw [eval_map, hc]
  rw [← hom_eval₂]
  congr 1
  unfold constantAbscissa center
  rw [← hom_eval₂, eval₂_C_X]
private theorem embedFX_injective : Function.Injective embedFX :=
  intoSeedClosure_injective.comp (MvPolynomial.C_injective (Fin 2) FX)
theorem reconstructed_center (J : Input) (B : ResidueLift J) (y : SeedClosure) :
    (reconstructed J B y).eval (embedFX center) = y := by
  classical
  let a := liftConstantSeeds B.denominator
  let g := algebraMap L[X] FX J.blockProduct
  let b := embedFX g
  let t := (B.numerator.map liftConstantSeeds).eval (embedFX center)
  have ha : a ≠ 0 := seed_nonzero B.denominator_ne
  have hg : g ≠ 0 := by
    apply (map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr
    exact mul_ne_zero J.chart.1.ne_zero J.chart.2.2.2.1.ne_zero
  have hb : b ≠ 0 := (map_ne_zero_iff _ embedFX_injective).mpr hg
  have hs : HighCore82706Tangent.genericPoint y (seedBiform B.denominator) = a :=
    congrArg (fun φ : SeedConstants →+* SeedClosure => φ B.denominator) (genericPoint_seed y)
  have hn : HighCore82706Tangent.genericPoint y (quotientNumerator J B 0) = b⁻¹ * (a * y - t) := by
    simp only [quotientNumerator, Nat.zero_add, Finset.range_one, Finset.sum_singleton,
      inverseBlockCoeff, Nat.factorial_zero, Nat.cast_one, inv_one,
      Function.iterate_zero, id_eq, one_mul, ordinateTaylorNum, Nat.mul_zero, Nat.zero_sub,
      pow_zero, map_sub, map_mul, genericPoint_C, genericPoint_Y, hs, taylor_zero, map_inv₀]
    rfl
  have hd : HighCore82706Tangent.genericPoint y (quotientDenominator J B 0) = a := by
    simp only [quotientDenominator, Nat.mul_zero, Nat.zero_sub, pow_zero, mul_one, hs]
  have hsum : (∑ j ∈ Finset.range (J.ell+1),
      C (HighCore82706Tangent.genericPoint y (quotientNumerator J B j) / HighCore82706Tangent.genericPoint y (quotientDenominator J B j)) *
        (Polynomial.X - C (embedFX center))^j).eval (embedFX center) =
      HighCore82706Tangent.genericPoint y (quotientNumerator J B 0) / HighCore82706Tangent.genericPoint y (quotientDenominator J B 0) := by
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]
    rw [Finset.sum_eq_single_of_mem 0 (by simp)]
    · simp only [pow_zero, mul_one]
    · intro n _ hn
      rw [zero_pow hn, mul_zero]
  change (C a⁻¹ * B.numerator.map liftConstantSeeds +
    J.blockProduct.map (liftConstantSeeds.comp MvPolynomial.C) * _).eval (embedFX center) = y
  rw [eval_add, eval_mul, eval_C, eval_mul, eval_block]
  rw [show intoSeedClosure (MvPolynomial.C center) = embedFX center from rfl, hsum, hn, hd]
  change a⁻¹ * t + b * (b⁻¹ * (a * y - t) / a) = y
  field_simp
  ring
theorem diagonal_identity {J : Input} {B : ResidueLift J} {q : Equation}
    (hq : Reduced q) (D : DifferentialProduct J B q) :
    C q.leadingCoeff * atAbscissa center D.numerator = C D.denominator * q := by
  classical
  have hn : (q.map intoSeedClosure).roots.Nodup := by
    have h := hq.2.2.map (f := algebraMap HighCore82706Tangent.SeedField SeedClosure)
    rw [Polynomial.map_map] at h
    exact Polynomial.nodup_roots h
  have hfactor : q.map intoSeedClosure = C (intoSeedClosure q.leadingCoeff) *
      ∏ y ∈ genericRoots q, (Polynomial.X - C y) := by
    have h := (IsAlgClosed.splits (q.map intoSeedClosure)).eq_prod_roots
    rw [leadingCoeff_map_of_injective intoSeedClosure_injective] at h
    rw [h]
    congr 1
    simp only [genericRoots, Finset.prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hn]
  apply Polynomial.map_injective _ intoSeedClosure_injective
  rw [Polynomial.map_mul, Polynomial.map_C, evaluated_product D.identity, Polynomial.map_mul,
    Polynomial.map_C, hfactor]
  simp_rw [reconstructed_center]
  ring
end
end HighCore82706Tangent_5
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_5
noncomputable section
open Polynomial
open P1 (K p)
open K1_14 (FX L Seeds atX liftPoly seedEmbedding)
open K1_14_6_1 (Dx Dx_atX Dx_mul Dx_pow)
open HighCore82706Tangent (center)
private theorem Dx_center : Dx center = 1 := by
  have h := Dx_atX (Polynomial.X (R := K))
  simpa only [atX, liftPoly, center, map_X, derivative_X, Polynomial.map_one, map_one] using h
private theorem Dx_nat (n : ℕ) : Dx (n : FX) = 0 := by
  have h : Dx 1 = 0 := by
    have h := Dx_atX (1 : K[X])
    simpa only [atX, liftPoly, derivative_one, Polynomial.map_one, Polynomial.map_zero,
      map_one, map_zero] using h
  rw [← nsmul_one, map_nsmul, h, nsmul_zero]
private theorem center_power_sum_ne_zero (n : ℕ) (c : ℕ → FX)
    (hc : ∀ i ≤ n, Dx (c i) = 0) (ht : c n ≠ 0) (hn : n < p) :
    ∑ i ∈ Finset.range (n+1), c i * center^i ≠ 0 := by
  induction n generalizing c with
  | zero => simpa only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one] using ht
  | succ n ih =>
    let e (i : ℕ) := (↑(i+1 : ℕ) : FX) * c (i+1)
    have hce (i : ℕ) (hi : i ≤ n) : Dx (e i) = 0 := by
      dsimp only [e]
      rw [Dx_mul, Dx_nat, hc _ (Nat.succ_le_succ hi), mul_zero, zero_mul, add_zero]
    let : CharP FX p := charP_of_injective_ringHom seedEmbedding.injective p
    have hnc : (↑(n+1 : ℕ) : FX) ≠ 0 := fun h =>
      (not_le_of_gt hn) (Nat.le_of_dvd (Nat.succ_pos n) ((CharP.cast_eq_zero_iff FX p _).mp h))
    have htop : e n ≠ 0 := mul_ne_zero hnc ht
    intro h
    have hD := congrArg (fun a => Dx a) h
    simp only [map_zero, map_sum] at hD
    apply ih e hce htop (Nat.lt_of_succ_lt hn)
    rw [Finset.sum_range_succ'] at hD
    simp only [pow_zero, mul_one, hc 0 (Nat.zero_le _), add_zero] at hD
    rw [← hD]
    apply Finset.sum_congr rfl
    intro i hi
    have hle := Nat.succ_le_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    rw [Dx_mul, Dx_pow, Dx_center, mul_one, hc _ hle, zero_mul, add_zero,
      Nat.add_sub_cancel]
    dsimp only [e]
    ring
private theorem diagonal_support {T : Polynomial Seeds} (hT : T.natDegree < p)
    (hc : ∀ i, CoeffConstant (T.coeff i)) {s : Fin 2 →₀ ℕ} {i : ℕ}
    (hs : (T.coeff i).coeff s ≠ 0) : (T.eval (MvPolynomial.C center)).coeff s ≠ 0 := by
  classical
  let n := T.natDegree + 1
  let Q : FX[X] := ofFn n fun j => (T.coeff j).coeff s
  have hQdeg : Q.natDegree < n := ofFn_natDegree_lt (Nat.succ_pos _) _
  have hQc (j : ℕ) (hj : j < n) : Q.coeff j = (T.coeff j).coeff s :=
    ofFn_coeff_eq_val_of_lt _ hj
  have hi : i < n := Nat.lt_succ_of_le (le_natDegree_of_ne_zero (by
    intro hz
    exact hs (by simp [hz])))
  have hQ : Q ≠ 0 := fun hz => hs ((hQc i hi).symm.trans (by rw [hz, coeff_zero]))
  have hne : Q.eval center ≠ 0 := by
    rw [eval_eq_sum_range]
    exact center_power_sum_ne_zero Q.natDegree Q.coeff
      (fun j hj => by rw [hQc j (hj.trans_lt hQdeg)]; exact hc j s)
      (leadingCoeff_ne_zero.mpr hQ) ((Nat.le_of_lt_succ hQdeg).trans_lt hT)
  have he : (T.eval (MvPolynomial.C center)).coeff s = Q.eval center := by
    rw [eval_eq_sum_range' (n := n) (Nat.lt_succ_self _), eval_eq_sum_range' hQdeg]
    simp only [MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hQc j (Finset.mem_range.mp hj), ← map_pow, mul_comm (T.coeff j), MvPolynomial.coeff_C_mul,
      mul_comm]
  rwa [he]
theorem degree_of_cleared {a b den : Seeds} {T N : Polynomial Seeds} {u : ℕ}
    (hb : b ≠ 0) (hden : den ≠ 0) (hT : T.natDegree < p)
    (hc : ∀ i, CoeffConstant (T.coeff i)) (ha : a.totalDegree ≤ u)
    (hdiag : b * T.eval (MvPolynomial.C center) = den * a)
    (hN : C b * T = C den * N) : ∀ i, (N.coeff i).totalDegree ≤ u := by
  classical
  intro i
  by_cases hNi : N.coeff i = 0
  · simp [hNi]
  have hcoeff := congrArg (fun F : Polynomial Seeds => F.coeff i) hN
  simp only [coeff_C_mul] at hcoeff
  have hTi : T.coeff i ≠ 0 := fun h0 => (mul_ne_zero hden hNi) (by
    rw [h0, mul_zero] at hcoeff
    exact hcoeff.symm)
  obtain ⟨s, hs⟩ := MvPolynomial.exists_coeff_ne_zero hTi
  have hs' := diagonal_support hT hc hs
  have hdiag0 : T.eval (MvPolynomial.C center) ≠ 0 := fun hz => hs' (by simp [hz])
  have ha0 : a ≠ 0 := fun hz => (mul_ne_zero hb hdiag0) (by rw [hdiag, hz, mul_zero])
  have hdeg : (T.coeff i).totalDegree ≤ (T.eval (MvPolynomial.C center)).totalDegree := by
    unfold MvPolynomial.totalDegree
    apply Finset.sup_le
    intro s hs
    have hmem := MvPolynomial.mem_support_iff.mpr
      (diagonal_support hT hc (MvPolynomial.mem_support_iff.mp hs))
    exact Finset.le_sup (f := fun d : Fin 2 →₀ ℕ => d.sum fun _ e => e) hmem
  have h1 := congrArg MvPolynomial.totalDegree hcoeff
  have h2 := congrArg MvPolynomial.totalDegree hdiag
  rw [MvPolynomial.totalDegree_mul_of_isDomain hb hTi,
    MvPolynomial.totalDegree_mul_of_isDomain hden hNi] at h1
  rw [MvPolynomial.totalDegree_mul_of_isDomain hb hdiag0,
    MvPolynomial.totalDegree_mul_of_isDomain hden ha0] at h2
  omega
end
end HighCore82706Tangent_5
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_5
noncomputable section
open Polynomial
open K1_14 (Seeds Equation)
open K1_14_4 (seedDegree seedDegree_le_iff)
open P1_7 (Reduced degreeAt)
open HighCore82706Tangent (Input ResidueLift Factors DifferentialProduct SeedClosure intoSeedClosure center)
def c1 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B) (j : Fin D.count),
    Nonempty (RegularValues J B (D.flat j))
def c2 : Prop :=
  ∀ (a b den : Seeds) (T : Polynomial Seeds) (m u : ℕ),
    b ≠ 0 → den ≠ 0 → CoeffConstant den →
    (∀ i, CoeffConstant (T.coeff i)) → T.natDegree ≤ m → m + u < P1.p →
    b.totalDegree ≤ u →
    b * T.eval (MvPolynomial.C center) = den * a →
    C den ∣ C b * T
private theorem bounded_product (h : c2) {J : Input} {B : ResidueLift J} {q : Equation}
    (hq : Reduced q) (hguard : q.natDegree * degreeAt J.hi + seedDegree q < P1.p)
    (D : DifferentialProduct J B q) : Nonempty (BoundedProduct J B q) := by
  classical
  let b := q.leadingCoeff
  let n := D.numerator.natDegree + 1
  have hq0 : q ≠ 0 := fun hz => hq.1.ne' (hz ▸ natDegree_zero)
  have hb : b ≠ 0 := leadingCoeff_ne_zero.mpr hq0
  have hu := (seedDegree_le_iff q _).mp le_rfl
  have hub : b.totalDegree ≤ seedDegree q := hu q.natDegree
  have hdiag := diagonal_identity hq D
  have hcoeff (i : ℕ) : b * (D.numerator.coeff i).eval (MvPolynomial.C center) =
      D.denominator * q.coeff i := by
    have hd := congrArg (fun P : Equation => P.coeff i) hdiag
    simpa only [coeff_C_mul, atAbscissa, coe_mapRingHom, coeff_map, coe_evalRingHom] using hd
  have hex (i : ℕ) := h (q.coeff i) b D.denominator (D.numerator.coeff i)
    _ _ hb D.denominator_ne D.denominator_constant (D.numerator_constant i)
    (D.abscissa_width i) hguard hub (hcoeff i)
  choose N hN using hex
  have hdN (i : ℕ) := degree_of_cleared hb D.denominator_ne
    ((D.abscissa_width i).trans_lt ((Nat.le_add_right _ _).trans_lt hguard))
    (D.numerator_constant i) (hu i) (hcoeff i) (hN i)
  let F : Polynomial (Polynomial Seeds) := ofFn n fun i => N i
  have hF : C (C b) * D.numerator = C (C D.denominator) * F := by
    ext i : 1
    simp only [coeff_C_mul]
    by_cases hi : i < n
    · rw [ofFn_coeff_eq_val_of_lt _ hi]
      exact hN i
    · have hz : D.numerator.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by
        dsimp only [n] at hi
        omega)
      rw [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi), hz, mul_zero, mul_zero]
  refine ⟨⟨F, fun i j => ?_, ?_⟩⟩
  · by_cases hi : i < n
    · rw [ofFn_coeff_eq_val_of_lt _ hi]
      exact hdN i j
    · rw [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi), coeff_zero,
        MvPolynomial.totalDegree_zero]
      exact Nat.zero_le _
  · let φ := Polynomial.mapRingHom (Polynomial.mapRingHom intoSeedClosure)
    let P : Polynomial (Polynomial SeedClosure) :=
      ∏ y ∈ HighCore82706Tangent.genericRoots q, (Polynomial.X - C (HighCore82706Tangent.reconstructed J B y))
    let Bc : Polynomial (Polynomial SeedClosure) := C (C (intoSeedClosure b))
    let Dc : Polynomial (Polynomial SeedClosure) := C (C (intoSeedClosure D.denominator))
    have hDc : Dc ≠ 0 := by
      dsimp only [Dc]
      exact C_ne_zero.mpr (C_ne_zero.mpr
        ((map_ne_zero_iff _ intoSeedClosure_injective).mpr D.denominator_ne))
    have he : Bc * (Dc * P) = Dc * φ F := by
      have he := congrArg φ hF
      simp only [φ, coe_mapRingHom, Polynomial.map_mul, Polynomial.map_C, D.identity] at he
      exact he
    apply mul_left_cancel₀ hDc
    calc
      Dc * φ F = Bc * (Dc * P) := he.symm
      _ = Dc * (Bc * P) := by rw [mul_left_comm]
theorem of_children (h1 : c1) (h2 : c2) : HighCore82706Tangent.c5 := by
  intro J B D j P
  have hu : seedDegree (D.flat j) ≤ J.v :=
    (Finset.single_le_sum (f := fun i => seedDegree (D.flat i))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ j)).trans D.seed_sum
  have hg : (D.flat j).natDegree * degreeAt J.hi + seedDegree (D.flat j) < P1.p :=
    (Nat.add_le_add (Nat.mul_le_mul_right _ (D.degree_each j)) hu).trans_lt J.flat_guard
  obtain ⟨R⟩ := h1 J B D j
  obtain ⟨G⟩ := bounded_product h2 (D.flat_reduced j) hg P
  exact flat_sections (D.flat_reduced j) (D.flat_irred j) R G
end
end HighCore82706Tangent_5
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_5_1
noncomputable section
open Polynomial Finset
open P1 (K)
open K1_14 (L FX Equation seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (separant flatten)
open HighCore82706Tangent (Input ResidueLift center constantAbscissa SeedConstants seedBiform
  quotientNumerator quotientDenominator)
def constantLift : L →+* Biform := MvPolynomial.C.comp constantAbscissa
def denominator (J : Input) (B : ResidueLift J) : Biform :=
  quotientDenominator J B J.ell
def numerator (J : Input) (B : ResidueLift J) (x : K) : Biform :=
  let s := separant (flatten J.f)
  let a := algebraMap K L x
  let d := MvPolynomial.C (seedEmbedding x - center)
  s ^ (2 * J.ell - 1) * B.numerator.eval₂ seedBiform (constantLift a) +
    J.blockProduct.eval₂ constantLift (constantLift a) *
      ∑ i ∈ range (J.ell + 1),
        s ^ ((2 * J.ell - 1) - (2 * i - 1)) * quotientNumerator J B i * d ^ i
def valuePolynomial {F : Type*} [Field F] (ev : Biform →+* F)
    (J : Input) (B : ResidueLift J) : F[X] :=
  C (ev (seedBiform B.denominator))⁻¹ * B.numerator.map (ev.comp seedBiform) +
    J.blockProduct.map (ev.comp constantLift) *
      ∑ i ∈ range (J.ell + 1),
        C (ev (quotientNumerator J B i) / ev (quotientDenominator J B i)) *
          (Polynomial.X - C (ev (MvPolynomial.C center))) ^ i
theorem eval_valuePolynomial {F : Type*} [Field F] (ev : Biform →+* F)
    (J : Input) (B : ResidueLift J) (x : K) :
    (valuePolynomial ev J B).eval (ev (MvPolynomial.C (seedEmbedding x))) =
      (ev (seedBiform B.denominator))⁻¹ *
        B.numerator.eval₂ (ev.comp seedBiform) (ev (constantLift (algebraMap K L x))) +
      J.blockProduct.eval₂ (ev.comp constantLift) (ev (constantLift (algebraMap K L x))) *
        ∑ i ∈ range (J.ell + 1),
          (ev (quotientNumerator J B i) / ev (quotientDenominator J B i)) *
            ev (MvPolynomial.C (seedEmbedding x - center)) ^ i := by
  simp only [valuePolynomial, eval_add, eval_mul, eval_C, eval_map, eval_finsetSum,
    eval_pow, eval_sub, eval_X, map_sub]
  rfl
theorem eval_denominator {F : Type*} [Field F] (ev : Biform →+* F)
    (J : Input) (B : ResidueLift J) (i : ℕ) :
    ev (quotientDenominator J B i) =
      ev (seedBiform B.denominator) * ev (separant (flatten J.f)) ^ (2 * i - 1) := by
  simp only [quotientDenominator, map_mul, map_pow]
theorem cleared_value {F : Type*} [Field F] (ev : Biform →+* F)
    (J : Input) (B : ResidueLift J)
    (hb : ev (seedBiform B.denominator) ≠ 0)
    (hs : ev (separant (flatten J.f)) ≠ 0) (x : K) :
    ev (numerator J B x) = ev (denominator J B) *
      (valuePolynomial ev J B).eval (ev (MvPolynomial.C (seedEmbedding x))) := by
  rw [eval_valuePolynomial, denominator, eval_denominator]
  simp only [numerator, map_add, map_mul, map_pow, map_sum, Polynomial.hom_eval₂]
  let b := ev (seedBiform B.denominator)
  let s := ev (separant (flatten J.f))
  let n := 2 * J.ell - 1
  let t := ev (MvPolynomial.C (seedEmbedding x - center))
  let l := B.numerator.eval₂ (ev.comp seedBiform) (ev (constantLift (algebraMap K L x)))
  let g := J.blockProduct.eval₂ (ev.comp constantLift) (ev (constantLift (algebraMap K L x)))
  change s ^ n * l + g * (∑ i ∈ range (J.ell + 1),
      s ^ (n - (2 * i - 1)) * ev (quotientNumerator J B i) * t ^ i) =
    (b * s ^ n) * (b⁻¹ * l + g * (∑ i ∈ range (J.ell + 1),
      (ev (quotientNumerator J B i) / ev (quotientDenominator J B i)) * t ^ i))
  have hl : (b * s ^ n) * (b⁻¹ * l) = s ^ n * l := by
    calc
      _ = s ^ n * l * (b * b⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hb, mul_one]
  rw [mul_add, hl, mul_left_comm (b * s ^ n) g, Finset.mul_sum _ _ (b * s ^ n)]
  refine congrArg (fun u : F => s ^ n * l + g * u) (sum_congr rfl ?_)
  intro i hi
  have hi' := Finset.mem_range.mp hi
  let m := 2 * i - 1
  have hm : m ≤ n := by dsimp only [m, n]; omega
  have hp : s ^ n = s ^ (n - m) * s ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]
  have hbm : b * s ^ m ≠ 0 := mul_ne_zero hb (pow_ne_zero _ hs)
  rw [eval_denominator]
  change _ = (b * s ^ n) * ((ev (quotientNumerator J B i) / (b * s ^ m)) * t ^ i)
  calc
    _ = s ^ (n - m) * ((b * s ^ m) * (ev (quotientNumerator J B i) / (b * s ^ m))) *
        t ^ i := by rw [mul_div_cancel₀ _ hbm]
    _ = _ := by rw [hp]; ring
end
end HighCore82706Tangent_5_1
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_5_1
noncomputable section
open Polynomial Finset
open P1 (K p)
open K1_14 (L FX atX liftPoly seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant markEval)
open HighCore82706Tangent (Input ResidueLift center constantAbscissa SeedConstants seedBiform
  evalSeedConstants liftTaylor inverseBlockCoeff quotientNumerator)
open HighCore82706Tangent_2 (jet jet_mul jet_poly seed_at_mark liftTaylor_at_mark ordinate_at_mark)
private abbrev inc := algebraMap L[X] FX
private theorem marked_coefficient (J : Input) (B : ResidueLift J) (γ : K)
    (hγ : γ ∈ J.marks) (T : L[X])
    (hT : C (evalSeedConstants (J.model.label γ) B.denominator) *
      liftPoly (J.family.scalar γ) - B.numerator.map (evalSeedConstants (J.model.label γ)) =
        J.blockProduct * T) {r : ℕ} (hr : r < p) :
    let ev := markEval (J.model.label γ) (J.family.scalar γ)
    ev (quotientNumerator J B r) = ev (separant (flatten J.f)) ^ (2 * r - 1) *
      jet (inc T) r := by
  let z := J.model.label γ
  let S := J.family.scalar γ
  let ev := markEval z S
  let δ := evalSeedConstants z B.denominator
  let N := B.numerator.map (evalSeedConstants z)
  let W := C δ * liftPoly S - N
  let s := ev (separant (flatten J.f)) ^ (2 * r - 1)
  change W = J.blockProduct * T at hT
  change ev (quotientNumerator J B r) = s * jet (inc T) r
  have hG : inc J.blockProduct ≠ 0 := by
    apply (map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr
    exact mul_ne_zero J.chart.1.ne_zero J.chart.2.2.2.1.ne_zero
  have hf : ev (flatten J.f) = 0 :=
    (K1_14_6_1.eval_flatten z S J.f).trans (J.regular γ hγ).1
  have hδ : ev (seedBiform B.denominator) = constantAbscissa δ :=
    RingHom.congr_fun (HighCore82706Tangent_2.seed_at_mark z S) _
  have hcoeff (i : ℕ) (hi : i < p) : jet (inc W) i =
      constantAbscissa δ * jet (atX S) i - jet (inc N) i := by
    rw [jet_poly _ hi, atX, jet_poly _ hi, jet_poly _ hi]
    simp only [W, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, map_sub,
      Polynomial.taylor_mul, Polynomial.taylor_C, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  calc
    _ = s * ∑ i ∈ range (r+1), jet (inc J.blockProduct)⁻¹ (r-i) * jet (inc W) i := by
      rw [quotientNumerator, map_sum, Finset.mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hi' : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
      simp only [map_mul, map_sub, map_pow]
      rw [hδ, ordinate_at_mark J z S hf hi', liftTaylor_at_mark z S _ (hi'.trans_lt hr),
        hcoeff i (hi'.trans_lt hr)]
      have heval (a : FX) : ev (MvPolynomial.C a) = a := MvPolynomial.eval_C a
      rw [heval]
      change jet (inc J.blockProduct)⁻¹ (r-i) *
          (constantAbscissa δ * (s * jet (atX S) i) - s * jet (inc N) i) =
        s * (jet (inc J.blockProduct)⁻¹ (r-i) *
          (constantAbscissa δ * jet (atX S) i - jet (inc N) i))
      ring
    _ = s * jet ((inc J.blockProduct)⁻¹ * inc W) r := by rw [jet_mul _ _ hr]
    _ = _ := by rw [hT, map_mul, ← mul_assoc, inv_mul_cancel₀ hG, one_mul]
private theorem eval_shifted (T : L[X]) {r : ℕ} (hd : T.natDegree ≤ r)
    (hr : r < p) (a : L) :
    (∑ i ∈ range (r+1), jet (inc T) i * (constantAbscissa a - center) ^ i) =
      constantAbscissa (T.eval a) := by
  have ht : (Polynomial.taylor center (T.map constantAbscissa)).natDegree < r+1 := by
    rw [Polynomial.natDegree_taylor]
    exact Polynomial.natDegree_map_le.trans_lt (Nat.lt_succ_of_le hd)
  rw [← eval_map_apply (p := T), ← Polynomial.taylor_eval_sub center,
    Polynomial.eval_eq_sum_range' ht]
  refine sum_congr rfl fun i hi => ?_
  rw [jet_poly _ ((Nat.lt_succ_iff.mp (mem_range.mp hi)).trans_lt hr)]
theorem marked_value (J : Input) (B : ResidueLift J) (γ : K) (hγ : γ ∈ J.marks) :
    let ev := markEval (J.model.label γ) (J.family.scalar γ)
    ev (denominator J B) ≠ 0 ∧ ∀ x : K,
      ev (numerator J B x) = ev (denominator J B) * seedEmbedding ((J.family.scalar γ).eval x) := by
  let z := J.model.label γ
  let S := J.family.scalar γ
  let ev := markEval z S
  let δ := evalSeedConstants z B.denominator
  let N := B.numerator.map (evalSeedConstants z)
  let s := ev (separant (flatten J.f))
  let n := 2 * J.ell - 1
  have hb : δ ≠ 0 := B.unit_at_marks γ (J.marks_sub hγ)
  have hs : s ≠ 0 := by
    dsimp only [s]
    rw [K1_14_6_1.eval_separant]
    exact (J.regular γ hγ).2.2
  have hφ : ev.comp seedBiform = constantAbscissa.comp (evalSeedConstants z) := HighCore82706Tangent_2.seed_at_mark z S
  have hφG : ev.comp constantLift = constantAbscissa :=
    RingHom.ext fun a => MvPolynomial.eval_C (constantAbscissa a)
  have hden : ev (denominator J B) = constantAbscissa δ * s ^ n := by
    rw [denominator, eval_denominator]
    exact congrArg (fun b : FX => b * s ^ n) (RingHom.congr_fun hφ _)
  change ev (denominator J B) ≠ 0 ∧ ∀ x : K,
    ev (numerator J B x) = ev (denominator J B) * seedEmbedding (S.eval x)
  rw [hden]
  constructor
  · have hι : Function.Injective constantAbscissa :=
      (IsFractionRing.injective L[X] FX).comp Polynomial.C_injective
    exact mul_ne_zero ((map_ne_zero_iff _ hι).mpr hb) (pow_ne_zero _ hs)
  intro x
  let a := algebraMap K L x
  have hr : J.ell < p := by
    have h := J.factorial_guard
    change 131071 + J.hi + 1 < p at h
    change 131071 - J.w < p
    omega
  obtain ⟨T, hdegree, hT⟩ := HighCore82706Tangent_2.marked_quotient J B γ hγ
  change C δ * liftPoly S - N = J.blockProduct * T at hT
  have hx : ev (constantLift a) = constantAbscissa a := RingHom.congr_fun hφG a
  have hN : B.numerator.eval₂ (ev.comp seedBiform) (ev (constantLift a)) =
      constantAbscissa (N.eval a) := by
    rw [hφ, hx, ← Polynomial.hom_eval₂, ← Polynomial.eval_map]
  have hG : J.blockProduct.eval₂ (ev.comp constantLift) (ev (constantLift a)) =
      constantAbscissa (J.blockProduct.eval a) := by
    rw [hφG, hx]
    simpa only [Polynomial.eval₂_id, RingHom.comp_id] using
      (Polynomial.hom_eval₂ J.blockProduct (RingHom.id L) constantAbscissa a).symm
  have ht : ev (MvPolynomial.C (seedEmbedding x - center)) = constantAbscissa a - center :=
    MvPolynomial.eval_C _
  have hsum :
      (∑ i ∈ range (J.ell + 1), s ^ (n - (2 * i - 1)) * ev (quotientNumerator J B i) *
          ev (MvPolynomial.C (seedEmbedding x - center)) ^ i) =
        s ^ n * constantAbscissa (T.eval a) := by
    rw [← eval_shifted T hdegree hr a, Finset.mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi' := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hp : n - (2 * i - 1) + (2 * i - 1) = n := by
      dsimp only [n]
      omega
    rw [ht, marked_coefficient J B γ hγ T hT (hi'.trans_lt hr)]
    change s ^ (n - (2 * i - 1)) * (s ^ (2 * i - 1) * jet (inc T) i) *
        (constantAbscissa a - center) ^ i = s ^ n * (jet (inc T) i * (constantAbscissa a - center) ^ i)
    rw [← mul_assoc (s ^ (n - (2 * i - 1))), ← pow_add, hp, mul_assoc]
  have hS : (liftPoly S).eval a = algebraMap K L (S.eval x) :=
    eval_map_apply (p := S) (algebraMap K L) x
  have h := congrArg (fun H : L[X] => constantAbscissa (H.eval a)) hT
  change constantAbscissa ((C δ * liftPoly S - N).eval a) =
    constantAbscissa ((J.blockProduct * T).eval a) at h
  simp only [eval_sub, eval_mul, eval_C, map_sub, map_mul, hS] at h
  have h' : constantAbscissa δ * seedEmbedding (S.eval x) - constantAbscissa (N.eval a) =
      constantAbscissa (J.blockProduct.eval a) * constantAbscissa (T.eval a) := h
  simp only [numerator, map_add, map_mul, map_pow, map_sum, Polynomial.hom_eval₂]
  change s ^ n * B.numerator.eval₂ (ev.comp seedBiform) (ev (constantLift a)) +
      J.blockProduct.eval₂ (ev.comp constantLift) (ev (constantLift a)) * _ = _
  rw [hN, hG, hsum]
  linear_combination - (s ^ n) * h'
end
end HighCore82706Tangent_5_1
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_3_1
noncomputable section
open Polynomial
open P1 (K p node)
open K1_14 (L FX Equation atMark atX liftPoly seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx flatten separant markEval)
open HighCore82706Tangent HighCore82706Tangent_3 HighCore82706Tangent_3_3
open scoped BigOperators
open HighCore82706Tangent_3 (seedBiform_image)
open HighCore82706Tangent_2 (jet seed_at_mark)
open HighCore82706Tangent_5_1 (marked_coefficient eval_shifted)
private theorem mark_constant (J : Input) (γ : K) (q : Equation) :
    markPoint J γ (C q) = atMark q (J.model.label γ) (J.family.scalar γ) := by
  change (C q).eval₂ (markRoot J γ) (Dx (atX (J.family.scalar γ))) = _
  rw [eval₂_C]
  rfl
private theorem mark_biform (J : Input) (γ : K) (q : Biform) :
    markPoint J γ (C (MvPolynomial.optionEquivLeft FX (Fin 2) q)) =
      markEval (J.model.label γ) (J.family.scalar γ) q := by
  rw [mark_constant, ← K1_14_6_1.eval_flatten, flatten, AlgEquiv.symm_apply_apply]
private theorem mark_seed (J : Input) (γ : K) (q : SeedConstants) :
    markPoint J γ (seedInJet q) = constantAbscissa (evalSeedConstants (J.model.label γ) q) := by
  unfold seedInJet
  rw [← seedBiform_image, mark_biform]
  exact RingHom.congr_fun (HighCore82706Tangent_2.seed_at_mark (J.model.label γ) (J.family.scalar γ)) q
theorem proof : HighCore82706Tangent_3_3.c1 := by
  intro J B γ hγ
  let z := J.model.label γ
  let S := J.family.scalar γ
  let ev := markEval z S
  let δ := evalSeedConstants z B.denominator
  let N := B.numerator.map (evalSeedConstants z)
  let s := ev (separant (flatten J.f))
  have hδ : constantAbscissa δ ≠ 0 :=
    (map_ne_zero_iff _ constantAbscissa.injective).mpr (B.unit_at_marks γ (J.marks_sub hγ))
  have hs : s ≠ 0 := by
    dsimp only [s, ev]
    rw [K1_14_6_1.eval_separant]
    exact (J.regular γ hγ).2.2
  have hden : markPoint J γ (residueInJet B) = constantAbscissa δ :=
    mark_seed J γ B.denominator
  refine ⟨?_, ?_⟩
  · rw [openFactor, map_mul, hden, mark_constant]
    exact mul_ne_zero hδ (J.regular γ hγ).2.2
  have hr : J.ell < p := by
    have h := J.factorial_guard
    change 131071 + J.hi + 1 < p at h
    change 131071 - J.w < p
    omega
  obtain ⟨T, hdegree, hT⟩ := HighCore82706Tangent_2.marked_quotient J B γ hγ
  change C δ * liftPoly S - N = J.blockProduct * T at hT
  have hjet (j : Fin (J.ell + 1)) :
      canonicalJet (markPoint J γ) J B j = jet (algebraMap L[X] FX T) j.val / constantAbscissa δ := by
    rw [canonicalJet, oldNumerator, oldDenominator, mark_biform, mark_biform]
    have hj := (Nat.lt_succ_iff.mp j.isLt).trans_lt hr
    rw [marked_coefficient J B γ hγ T hT hj, quotientDenominator, map_mul, map_pow]
    have hseed : ev (seedBiform B.denominator) = constantAbscissa δ :=
      RingHom.congr_fun (HighCore82706Tangent_2.seed_at_mark z S) B.denominator
    change s ^ (2 * j.val - 1) * _ / (ev (seedBiform B.denominator) * s ^ (2 * j.val - 1)) = _
    rw [hseed, mul_comm (s ^ _), mul_div_mul_right _ _ (pow_ne_zero _ hs)]
  intro x
  let a := algebraMap K L (node x)
  have hres : residueValue (markPoint J γ) B x = constantAbscissa (N.eval a) / constantAbscissa δ := by
    rw [residueValue, mark_seed, hden]
    have hN : evalSeedConstants z (residueAtNode B x) = N.eval a := by
      have hmap := eval_map_apply (p := B.numerator) (evalSeedConstants z) (MvPolynomial.C a)
      have ha : evalSeedConstants z (MvPolynomial.C a) = a := MvPolynomial.eval_C a
      rw [ha] at hmap
      exact hmap.symm
    rw [hN]
  have hsum :
      (∑ j : Fin (J.ell + 1), canonicalJet (markPoint J γ) J B j * (nodeAt x - center) ^ j.val) =
        constantAbscissa (T.eval a) / constantAbscissa δ := by
    simp_rw [hjet, div_mul_eq_mul_div₀]
    rw [← Finset.sum_div,
      Fin.sum_univ_eq_sum_range (fun i => jet (algebraMap L[X] FX T) i * (nodeAt x - center) ^ i)]
    exact congrArg (· / constantAbscissa δ) (eval_shifted T hdegree hr a)
  rw [curveValue, reconstructedValue]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [hres, hsum, ← mul_div_assoc, ← add_div]
  apply (div_eq_iff hδ).2
  have hS : (liftPoly S).eval a = algebraMap K L (S.eval (node x)) :=
    eval_map_apply (p := S) (algebraMap K L) (node x)
  have h := congrArg (fun H : L[X] => constantAbscissa (H.eval a)) hT
  change constantAbscissa ((C δ * liftPoly S - N).eval a) =
    constantAbscissa ((J.blockProduct * T).eval a) at h
  simp only [eval_sub, eval_mul, eval_C, map_sub, map_mul, hS] at h
  change constantAbscissa (N.eval a) +
      constantAbscissa (J.blockProduct.eval a) * constantAbscissa (T.eval a) =
    constantAbscissa (algebraMap K L (S.eval (node x))) * constantAbscissa δ
  linear_combination -h
end
end HighCore82706Tangent_3_3_1
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_3_2
noncomputable section
open P1 (K I node)
open HighCore82706Tangent (Input center constantAbscissa)
open HighCore82706Tangent_3_3
open K1_14 (L FX seedEmbedding)
open ProximityPrize.Benchmark
open scoped BigOperators
private theorem tail_weights {F ι : Type*} [Field F] [DecidableEq ι]
    (sites : Finset ι) (d u : ι → F) (hd : Function.Injective d)
    (hd₀ : ∀ i, d i ≠ 0) (hu : ∀ i, u i ≠ 0) (m : ℕ) (x : ι) :
    ∃ b : ι → F, ∀ j : ℕ, m ≤ j → j - m < sites.card →
      u x * d x ^ j = ∑ i ∈ sites, b i * (u i * d i ^ j) := by
  let w i := (Lagrange.basis sites d i).eval (d x)
  let k i := u i * d i ^ m
  refine ⟨fun i => (k x * w i) / k i, ?_⟩
  intro j hm hj
  have hfactor (i : ι) : u i * d i ^ j = k i * d i ^ (j - m) := by
    dsimp only [k]
    rw [mul_assoc, ← pow_add, Nat.add_comm m, Nat.sub_add_cancel hm]
  have hpoly : (Polynomial.X : Polynomial F) ^ (j - m) =
      Lagrange.interpolate sites d
        (fun i => ((Polynomial.X : Polynomial F) ^ (j - m)).eval (d i)) := by
    apply Lagrange.eq_interpolate hd.injOn
    rw [Polynomial.degree_X_pow]
    exact WithBot.coe_lt_coe.mpr hj
  have he : d x ^ (j - m) = ∑ i ∈ sites, w i * d i ^ (j - m) := by
    simpa only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm, w]
      using congrArg (Polynomial.eval (d x)) hpoly
  rw [hfactor x, he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hk : k i ≠ 0 := mul_ne_zero (hu i) (pow_ne_zero _ (hd₀ i))
  rw [hfactor i, ← mul_assoc (k x), ← mul_assoc ((k x * w i) / k i), div_mul_cancel₀ _ hk]
private theorem sum_prefix {A : Type*} [AddCommMonoid A] {m n : ℕ} (h : m ≤ n)
    (f : Fin n → A) (hz : ∀ j, m ≤ j.val → f j = 0) :
    ∑ j : Fin m, f (j.castLE h) = ∑ j : Fin n, f j := by
  classical
  change (∑ j : Fin m, f (Fin.castLEEmb h j)) = ∑ j : Fin n, f j
  rw [← Finset.sum_map]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  apply hz
  by_contra! hlt
  exact hj (Finset.mem_map.mpr ⟨⟨j.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
private theorem node_ne_center (x : I) : nodeAt x ≠ center := by
  intro h
  exact (Polynomial.X_ne_C (algebraMap K L (node x)))
    ((IsFractionRing.injective (Polynomial L) FX) h.symm)
private theorem block_ne_zero (J : Input) (i : I) : blockAtNode J i ≠ 0 := by
  have h := J.chart.2.2.2.2.2.2.2.1 i
  rw [blockAtNode, Input.blockProduct, Polynomial.eval_mul, map_mul]
  exact mul_ne_zero (fun e => h.1 (constantAbscissa.injective (e.trans constantAbscissa.map_zero.symm)))
    (fun e => h.2 (constantAbscissa.injective (e.trans constantAbscissa.map_zero.symm)))
theorem proof : HighCore82706Tangent_3_3.c2 := by
  classical
  intro J sites x
  let m := prefixLength J sites
  let d (i : I) := nodeAt i - center
  let coeff (i : I) (j : ℕ) := blockAtNode J i * d i ^ j
  have hn : Function.Injective nodeAt := seedEmbedding.injective.comp IRSProfile.domain.injective
  obtain ⟨b, hb⟩ := tail_weights sites d (blockAtNode J)
    (fun _ _ h => hn (sub_left_inj.mp h))
    (fun i => sub_ne_zero.mpr (node_ne_center i)) (block_ne_zero J) m x
  let r (j : Fin (J.ell + 1)) := coeff x j - ∑ i ∈ sites, b i * coeff i j
  refine ⟨b, fun j => r (prefixIndex J sites j), ?_⟩
  intro E _ _ Lx ν hs
  let f := algebraMap FX E
  let Q (i : I) := ∑ j : Fin (J.ell + 1), f (coeff i j) * ν j
  have hrec (i : I) : reconstructedValue J Lx ν i = Lx i + Q i := by
    rw [reconstructedValue, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [coeff, map_mul]
    ac_rfl
  have hsites (i : I) (hi : i ∈ sites) : Q i = f (wordAt J i) - Lx i := by
    rw [← hs i hi, hrec, add_sub_cancel_left]
  have hprefix :
      (∑ j : Fin m, f (r (prefixIndex J sites j)) * ν (prefixIndex J sites j)) =
        ∑ j : Fin (J.ell + 1), f (r j) * ν j := by
    have hm : m ≤ J.ell + 1 := Nat.sub_le _ _
    refine sum_prefix hm (fun j => f (r j) * ν j) ?_
    intro j hj
    have hdegree : j.val - m < sites.card := by
      have hj' := j.isLt
      unfold m prefixLength at hj ⊢
      omega
    have hzero : r j = 0 := sub_eq_zero.mpr (hb j hj hdegree)
    rw [hzero, map_zero, zero_mul]
  have hsum : (∑ i ∈ sites, f (b i) * Q i) =
      ∑ j : Fin (J.ell + 1), f (∑ i ∈ sites, b i * coeff i j) * ν j := by
    simp only [Q, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have hdecomp : Q x = (∑ i ∈ sites, f (b i) * Q i) +
      ∑ j : Fin (J.ell + 1), f (r j) * ν j := by
    rw [hsum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← add_mul, ← map_add, add_comm _ (r j)]
    dsimp only [r]
    rw [sub_add_cancel]
  have hvalues : (∑ i ∈ sites, f (b i) * Q i) =
      ∑ i ∈ sites, f (b i) * (f (wordAt J i) - Lx i) :=
    Finset.sum_congr rfl fun i hi => congrArg (f (b i) * ·) (hsites i hi)
  change reconstructedValue J Lx ν x - f (wordAt J x) = _
  rw [hrec, hdecomp, ← hprefix, hvalues]
  abel
end
end HighCore82706Tangent_3_3_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_4
noncomputable section
open Polynomial Finset
open HighCore82706Tangent
open K1_14 (L FX Seeds Equation)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx)
abbrev seedMap : Seeds →+* SeedField := algebraMap Seeds SeedField
def splitting (q : Equation) : IntermediateField SeedField SeedClosure :=
  IntermediateField.adjoin SeedField ((generic q).rootSet SeedClosure)
abbrev SplitField (q : Equation) := ↥(splitting q)
def geomRoots (q : Equation) : Finset (SplitField q) := by
  classical
  exact ((generic q).map (algebraMap SeedField (SplitField q))).roots.toFinset
def coeffDx : Seeds →+ Seeds :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom Dx).comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
theorem coeff_coeffDx (s : Seeds) (m : Fin 2 →₀ ℕ) :
    (coeffDx s).coeff m = Dx (s.coeff m) := rfl
abbrev splitMap (q : Equation) : Seeds →+* SplitField q :=
  (algebraMap SeedField (SplitField q)).comp seedMap
def point {F : Type} [Field F] (ι : Seeds →+* F) (y : F) : Biform →+* F :=
  (eval₂RingHom ι y).comp (MvPolynomial.optionEquivLeft FX (Fin 2)).toRingHom
def origin {F : Type} [Field F] (ι : Seeds →+* F) : F :=
  ι (MvPolynomial.C center)
def crt {F : Type} [Field F] (ι : Seeds →+* F) {J : Input}
    (B : ResidueLift J) : F[X] :=
  C ((ι (liftSeeds B.denominator))⁻¹) * B.numerator.map (ι.comp liftSeeds)
def blocks {F : Type} [Field F] (ι : Seeds →+* F) (J : Input) : F[X] :=
  J.blockProduct.map ((ι.comp liftSeeds).comp MvPolynomial.C)
def jet {F : Type} [Field F] (ι : Seeds →+* F) {J : Input}
    (B : ResidueLift J) (y : F) (r : ℕ) : F :=
  point ι y (quotientNumerator J B r) / point ι y (quotientDenominator J B r)
def quotientValue {F : Type} [Field F] (ι : Seeds →+* F) {J : Input}
    (B : ResidueLift J) (y : F) : F :=
  (y - (crt ι B).eval (origin ι)) / (blocks ι J).eval (origin ι)
def modelValue {F : Type} [Field F] (ι : Seeds →+* F) {J : Input}
    (B : ResidueLift J) (y : F) : F[X] :=
  crt ι B + blocks ι J *
    ∑ r ∈ range (J.ell + 1), C (jet ι B y r) * ((Polynomial.X : F[X]) - C (origin ι))^r
structure DifferentialData (q : Equation) where
  base : Derivation ℤ SeedField SeedField
  split : Derivation ℤ (SplitField q) (SplitField q)
  extends_seed : ∀ s : Seeds, base (seedMap s) = seedMap (coeffDx s)
  extends_base : ∀ a : SeedField,
    split (algebraMap SeedField (SplitField q) a) =
      algebraMap SeedField (SplitField q) (base a)
  center_one : split (origin (splitMap q)) = 1
  frozen : ∀ s : SeedConstants, split (splitMap q (liftSeeds s)) = 0
end
end HighCore82706Tangent_4
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_4
noncomputable section
open Polynomial Finset
open HighCore82706Tangent
open K1_14 (Seeds Equation)
def coeffDeriv {F : Type} [CommRing F] (δ : Derivation ℤ F F) :
    Derivation ℤ F[X] F[X] :=
  letI : Differential F := ⟨δ⟩
  Differential.mapCoeffs
@[simp] theorem coeff_coeffDeriv {F : Type} [CommRing F] (δ : Derivation ℤ F F)
    (P : F[X]) (i : ℕ) : (coeffDeriv δ P).coeff i = δ (P.coeff i) := rfl
@[simp] theorem coeffDeriv_C {F : Type} [CommRing F] (δ : Derivation ℤ F F)
    (x : F) : coeffDeriv δ (C x) = C (δ x) := by
  let : Differential F := ⟨δ⟩
  exact Differential.mapCoeffs_C x
@[simp] theorem coeffDeriv_X {F : Type} [CommRing F] (δ : Derivation ℤ F F) :
    coeffDeriv δ (Polynomial.X : F[X]) = 0 := by
  let : Differential F := ⟨δ⟩
  exact Differential.mapCoeffs_X (A := F)
private theorem taylor_constant {F : Type} [Field F] (δ : Derivation ℤ F F)
    (x R : F) (l : ℕ) (hx : δ x = 1) (hflat : (δ^[l+1]) R = 0)
    (hfac : ∀ r ≤ l, (r.factorial : F) ≠ 0) :
    coeffDeriv δ (∑ r ∈ range (l+1), C ((δ^[r]) R / (r.factorial : F)) *
      ((Polynomial.X : F[X]) - C x)^r) = 0 := by
  let z : F[X] := (Polynomial.X : F[X]) - C x
  let t (r : ℕ) : F := (δ^[r]) R / (r.factorial : F)
  let A (r : ℕ) : F[X] := C (δ (t r)) * z^r
  let E (r : ℕ) : F[X] := C (t r) * coeffDeriv δ (z^r)
  have hz : coeffDeriv δ z = -1 := by simp [z, hx]
  have hA : A l = 0 := by
    have hzero : δ ((δ^[l]) R) = 0 := (Function.iterate_succ_apply' _ _ _).symm.trans hflat
    simp only [A, t, δ.leibniz_div_const _ _ (δ.map_natCast _), hzero, smul_zero,
      map_zero, zero_mul]
  have hE₀ : E 0 = 0 := by simp [E]
  have hstep (r : ℕ) (hr : r < l) : E (r+1) = -A r := by
    have hfac' := hfac (r+1) (Nat.succ_le_of_lt hr)
    rw [Nat.factorial_succ, Nat.cast_mul] at hfac'
    have hn : ((r+1 : ℕ) : F) ≠ 0 := fun h => hfac' (by rw [h, zero_mul])
    have hf := hfac r hr.le
    have ht : t (r+1) * ((r+1 : ℕ) : F) = δ (t r) := by
      have hiter : (δ^[r+1]) R = δ ((δ^[r]) R) := Function.iterate_succ_apply' _ _ _
      dsimp only [t]
      rw [hiter, δ.leibniz_div_const _ _ (δ.map_natCast _),
        Nat.factorial_succ, Nat.cast_mul, smul_eq_mul]
      field_simp
    simp only [E, A, Derivation.leibniz_pow, hz, Nat.add_sub_cancel,
      smul_eq_mul, nsmul_eq_mul, ← C_eq_natCast, mul_neg, ← mul_assoc, mul_one, ← map_mul, ht]
  change coeffDeriv δ (∑ r ∈ range (l+1), C (t r) * z^r) = 0
  rw [map_sum]
  calc
    _ = ∑ r ∈ range (l+1), (E r + A r) := by
      apply sum_congr rfl
      intro r _
      rw [Derivation.leibniz]
      simp only [smul_eq_mul, coeffDeriv_C, E, A, mul_comm (z ^ r)]
    _ = 0 := by
      rw [sum_add_distrib, sum_range_succ' E, sum_range_succ A, hE₀, hA, add_zero, add_zero]
      rw [show (∑ i ∈ range l, E (i + 1)) = ∑ i ∈ range l, -A i by
        exact sum_congr rfl fun i hi => hstep i (mem_range.mp hi)]
      rw [sum_neg_distrib, neg_add_cancel]
theorem reconstructed_constant {q : Equation} (T : DifferentialData q)
    (J : Input) (B : ResidueLift J) (y : SplitField q)
    (hjet : ∀ r ≤ J.ell, jet (splitMap q) B y r =
      (T.split^[r]) (quotientValue (splitMap q) B y) / (r.factorial : SplitField q))
    (hflat : (T.split^[J.ell+1]) (quotientValue (splitMap q) B y) = 0)
    (hfac : ∀ r ≤ J.ell, (r.factorial : SplitField q) ≠ 0) :
    coeffDeriv T.split (modelValue (splitMap q) B y) = 0 := by
  have hcrt : coeffDeriv T.split (crt (splitMap q) B) = 0 := by
    have hnum : coeffDeriv T.split (B.numerator.map ((splitMap q).comp liftSeeds)) = 0 := by
      apply Polynomial.ext
      intro k
      rw [coeff_coeffDeriv, coeff_map, coeff_zero]
      exact T.frozen _
    unfold crt
    rw [Derivation.leibniz, hnum, coeffDeriv_C, T.split.leibniz_inv, T.frozen]
    simp
  have hblock : coeffDeriv T.split (blocks (splitMap q) J) = 0 := by
    apply Polynomial.ext
    intro k
    rw [coeff_coeffDeriv, blocks, coeff_map, coeff_zero]
    exact T.frozen _
  have hTaylor := taylor_constant T.split (origin (splitMap q))
    (quotientValue (splitMap q) B y) J.ell T.center_one hflat hfac
  have ht : (∑ r ∈ range (J.ell+1), C (jet (splitMap q) B y r) *
        ((Polynomial.X : (SplitField q)[X]) - C (origin (splitMap q))) ^ r) =
      ∑ r ∈ range (J.ell+1), C ((T.split^[r]) (quotientValue (splitMap q) B y) /
        (r.factorial : SplitField q)) *
        ((Polynomial.X : (SplitField q)[X]) - C (origin (splitMap q))) ^ r := by
    apply sum_congr rfl
    intro r hr
    rw [hjet r (Nat.le_of_lt_succ (mem_range.mp hr))]
  unfold modelValue
  rw [ht, map_add, Derivation.leibniz, hcrt, hblock, hTaylor]
  simp
theorem model_width {F : Type} [Field F] (ι : Seeds →+* F)
    (J : Input) (B : ResidueLift J) (y : F) :
    (modelValue ι B y).natDegree ≤ P1_7.degreeAt J.hi := by
  have hd := J.chart.2.1
  have hg : (blocks ι J).natDegree ≤ 2 * J.w := by
    unfold blocks Input.blockProduct Input.secondBlock
    refine natDegree_map_le.trans (natDegree_mul_le.trans ?_)
    have hh := natDegree_map_le (p := J.block) (f := frobenius K1_14.L P1.p)
    change J.block.natDegree = J.w at hd
    rw [hd] at hh ⊢
    omega
  have hc : (crt ι B).natDegree ≤ 2 * J.w := by
    unfold crt
    refine natDegree_mul_le.trans ?_
    rw [natDegree_C, zero_add]
    exact natDegree_map_le.trans B.numerator_width.le
  have ht : (∑ r ∈ range (J.ell + 1), C (jet ι B y r) *
        ((Polynomial.X : F[X]) - C (origin ι))^r).natDegree ≤ J.ell := by
    apply natDegree_sum_le_of_forall_le
    intro r hr
    refine natDegree_mul_le.trans ?_
    rw [natDegree_C, zero_add]
    refine (natDegree_pow_le_of_le r (natDegree_X_sub_C_le _)).trans ?_
    simpa only [mul_one] using Nat.le_of_lt_succ (mem_range.mp hr)
  unfold modelValue
  refine (natDegree_add_le _ _).trans (max_le (hc.trans ?_) ?_)
  · unfold P1_7.degreeAt
    have huw : J.w ≤ J.hi := J.upper
    have hp := J.quotient_pos
    change 0 < 131071 - J.w at hp
    omega
  · refine natDegree_mul_le.trans ((Nat.add_le_add hg ht).trans ?_)
    change 2 * J.w + (131071 - J.w) ≤ 131071 + J.hi
    have huw : J.w ≤ J.hi := J.upper
    have hp := J.quotient_pos
    change 0 < 131071 - J.w at hp
    omega
end
end HighCore82706Tangent_4
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_4
noncomputable section
open Polynomial Finset
open HighCore82706Tangent
open K1_14 (Seeds Equation)
instance splittingField (q : Equation) : (generic q).IsSplittingField SeedField (SplitField q) :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
theorem map_model {F G : Type} [Field F] [Field G] (ι : Seeds →+* F) (ρ : F →+* G)
    (J : Input) (B : ResidueLift J) (y : F) :
    (modelValue ι B y).map ρ = modelValue (ρ.comp ι) B (ρ y) := by
  simp [modelValue, crt, blocks, jet, point, origin, Polynomial.map_sum, Polynomial.map_map,
    Polynomial.hom_eval₂, RingHom.comp_assoc]
def splitProduct (J : Input) (B : ResidueLift J) (q : Equation) :
    Polynomial (Polynomial (SplitField q)) :=
  ∏ y ∈ geomRoots q, (Polynomial.X - C (modelValue (splitMap q) B y))
theorem coeff_splitProduct_top (J : Input) (B : ResidueLift J) (q : Equation)
    (hsep : (generic q).Separable) : (splitProduct J B q).coeff q.natDegree = 1 := by
  classical
  let H := (generic q).map (algebraMap SeedField (SplitField q))
  have hs : H.Splits := IsSplittingField.splits _ _
  have hcard : (geomRoots q).card = q.natDegree := by
    unfold geomRoots
    change H.roots.toFinset.card = _
    have hH : H.Separable := hsep.map
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hH), ← hs.natDegree_eq_card_roots]
    unfold H generic
    rw [natDegree_map, natDegree_map_eq_of_injective (IsFractionRing.injective Seeds SeedField)]
  unfold splitProduct
  have hd := natDegree_finsetProd_X_sub_C_eq_card (geomRoots q) (modelValue (splitMap q) B)
  rw [← hcard, ← hd, coeff_natDegree]
  exact (monic_prod_X_sub_C _ _).leadingCoeff
private theorem prod_width {F α : Type} [Field F] (S : Finset α)
    (f : α → F[X]) (d : ℕ) (h : ∀ y ∈ S, (f y).natDegree ≤ d) (i : ℕ) :
    ((∏ y ∈ S, ((Polynomial.X : Polynomial F[X]) - C (f y))).coeff i).natDegree ≤
      S.card * d := by
  classical
  induction S using Finset.induction_on generalizing i with
  | empty =>
    cases i <;> simp [coeff_one]
  | @insert a S ha ih =>
    have ha' := h a (Finset.mem_insert_self ..)
    have hS := fun j => ih (fun y hy => h y (Finset.mem_insert_of_mem hy)) j
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.add_mul, one_mul]
    cases i with
    | zero =>
      simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
      refine natDegree_mul_le.trans ?_
      rw [natDegree_neg]
      exact (Nat.add_le_add ha' (hS 0)).trans (Nat.add_comm _ _).le
    | succ i =>
      rw [coeff_X_sub_C_mul]
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · exact (hS i).trans (Nat.le_add_right _ _)
      · exact natDegree_mul_le.trans (by simpa only [add_comm] using Nat.add_le_add ha' (hS (i+1)))
theorem splitProduct_width (J : Input) (B : ResidueLift J) (q : Equation) (i : ℕ) :
    ((splitProduct J B q).coeff i).natDegree ≤ q.natDegree * P1_7.degreeAt J.hi := by
  classical
  have hcard : (geomRoots q).card ≤ q.natDegree := by
    unfold geomRoots
    refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
    unfold generic
    exact natDegree_map_le.trans natDegree_map_le
  exact (prod_width _ _ _ (fun y _ => model_width _ J B y) i).trans
    (Nat.mul_le_mul_right _ hcard)
theorem splitProduct_constant {q : Equation} (T : DifferentialData q) (J : Input)
    (B : ResidueLift J)
    (h : ∀ y ∈ geomRoots q, coeffDeriv T.split (modelValue (splitMap q) B y) = 0)
    (i j : ℕ) : T.split (((splitProduct J B q).coeff i).coeff j) = 0 := by
  have hp (k : ℕ) : coeffDeriv T.split ((splitProduct J B q).coeff k) = 0 := by
    unfold splitProduct
    classical
    generalize heq : geomRoots q = s at h ⊢
    clear heq
    induction s using Finset.induction_on generalizing k with
    | empty => simp [coeff_one, apply_ite]
    | @insert a s ha ih =>
      have hfactor (m : ℕ) : coeffDeriv T.split
          ((Polynomial.X - C (modelValue (splitMap q) B a)).coeff m) = 0 := by
        rw [coeff_sub, map_sub, coeff_X, coeff_C]
        simp [apply_ite, h a (mem_insert_self ..)]
      rw [Finset.prod_insert ha, coeff_mul, map_sum]
      apply sum_eq_zero
      intro ij _
      rw [Derivation.leibniz, hfactor, ih ij.2 (fun y hy => h y (mem_insert_of_mem hy))]
      simp
  have hcoeff := congrArg (fun P : (SplitField q)[X] => P.coeff j) (hp i)
  exact hcoeff.trans (coeff_zero j)
private theorem geomRoots_set (q : Equation) :
    (geomRoots q : Set (SplitField q)) = (generic q).rootSet (SplitField q) := by
  classical
  rw [rootSet_def]
  rfl
private theorem rootImage {F : Type} [Field F] [Algebra SeedField F] [DecidableEq F]
    (q : Equation) (ρ : SplitField q →ₐ[SeedField] F) :
    (geomRoots q).image ρ = (((generic q).map (algebraMap SeedField F)).roots.toFinset) := by
  classical
  apply Finset.coe_injective
  rw [Finset.coe_image, geomRoots_set]
  have hs := IsSplittingField.splits (SplitField q) (generic q)
  rw [hs.image_rootSet ρ, rootSet_def]
theorem splitProduct_descend (J : Input) (B : ResidueLift J) (q : Equation)
    (hsep : (generic q).Separable) :
    ∃ P : Polynomial SeedField[X],
      P.map (mapRingHom (algebraMap SeedField (SplitField q))) = splitProduct J B q := by
  classical
  let : IsGalois SeedField (SplitField q) := IsGalois.of_separable_splitting_field hsep
  let : FiniteDimensional SeedField (SplitField q) := IsSplittingField.finiteDimensional _ (generic q)
  have hinv (σ : SplitField q ≃ₐ[SeedField] SplitField q) :
      (splitProduct J B q).map (mapRingHom σ.toRingHom) = splitProduct J B q := by
    have hσ : σ.toRingHom.comp (splitMap q) = splitMap q := by
      apply RingHom.ext
      intro s
      exact σ.commutes (seedMap s)
    have hr : (geomRoots q).image σ.toAlgHom = geomRoots q := rootImage q σ.toAlgHom
    unfold splitProduct
    rw [Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      coe_mapRingHom, map_model, hσ]
    calc
      _ = ∏ y ∈ (geomRoots q).image σ.toAlgHom,
          (Polynomial.X - C (modelValue (splitMap q) B y)) := by
        rw [Finset.prod_image (g := σ.toAlgHom) σ.injective.injOn]
        rfl
      _ = _ := by rw [hr]
  apply (mem_lifts _).mp
  apply (lifts_iff_coeff_lifts _).mpr
  intro i
  apply (lifts_iff_set_range _).mp
  apply (lifts_iff_coeff_lifts _).mpr
  intro j
  apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro σ
  have he := congrArg (fun P : Polynomial (Polynomial (SplitField q)) =>
    (P.coeff i).coeff j) (hinv σ)
  change (((splitProduct J B q).map (mapRingHom σ.toRingHom)).coeff i).coeff j =
    ((splitProduct J B q).coeff i).coeff j at he
  rwa [coeff_map, coe_mapRingHom, coeff_map] at he
theorem splitProduct_closure (J : Input) (B : ResidueLift J) (q : Equation) :
    (splitProduct J B q).map (mapRingHom (splitting q).val.toRingHom) =
      ∏ y ∈ genericRoots q, (Polynomial.X - C (reconstructed J B y)) := by
  classical
  let ρ : SplitField q →ₐ[SeedField] SeedClosure := (splitting q).val
  have hρ : ρ.toRingHom.comp (splitMap q) = intoSeedClosure := rfl
  have hr : (geomRoots q).image ρ = genericRoots q := by
    rw [rootImage q ρ, genericRoots, generic, Polynomial.map_map]
    rfl
  change (splitProduct J B q).map (mapRingHom ρ.toRingHom) = _
  unfold splitProduct
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    coe_mapRingHom, map_model, hρ]
  rw [← hr, Finset.prod_image (g := ρ) ρ.injective.injOn]
  rfl
end
end HighCore82706Tangent_4
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_4
noncomputable section
open Polynomial
open HighCore82706Tangent
open K1_14 (Seeds Equation seedEmbedding)
open K1_14_6_1 (Dx)
private theorem clear_two (P : Polynomial (Polynomial SeedField)) :
    ∃ b : Seeds, b ≠ 0 ∧ ∃ N : Polynomial (Polynomial Seeds),
      N.map (mapRingHom seedMap) = C (C (seedMap b)) * P := by
  let s := P.support.biUnion (fun i => (P.coeff i).support.image (fun j => (i, j)))
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors Seeds) s
    (fun ij => (P.coeff ij.1).coeff ij.2)
  refine ⟨b, mem_nonZeroDivisors_iff_ne_zero.mp b.property, ?_⟩
  apply (mem_lifts _).mp
  apply (lifts_iff_coeff_lifts _).mpr
  intro i
  apply (lifts_iff_set_range _).mp
  apply (lifts_iff_coeff_lifts _).mpr
  intro j
  rw [coeff_C_mul, coeff_C_mul]
  by_cases hc : (P.coeff i).coeff j = 0
  · exact ⟨0, by rw [hc, mul_zero, map_zero]⟩
  have hi : i ∈ P.support := mem_support_iff.mpr (fun h => hc (by rw [h, coeff_zero]))
  have hj : j ∈ (P.coeff i).support := mem_support_iff.mpr hc
  have hij : (i, j) ∈ s := Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  have h := hb (i, j) hij
  rw [Algebra.smul_def] at h
  exact h
theorem charSeed : CharP SeedField P1.p :=
  charP_of_injective_ringHom ((seedMap.comp (MvPolynomial.C.comp seedEmbedding))).injective P1.p
theorem charSplit (q : Equation) : CharP (SplitField q) P1.p :=
  charP_of_injective_ringHom
    (((splitMap q).comp (MvPolynomial.C.comp seedEmbedding))).injective P1.p
private theorem dx_zero_of_base {q : Equation} (T : DifferentialData q) (b : Seeds)
    (hb : T.base (seedMap b) = 0) (m : Fin 2 →₀ ℕ) : Dx (b.coeff m) = 0 := by
  rw [T.extends_seed] at hb
  have h : coeffDx b = 0 :=
    (IsFractionRing.injective Seeds SeedField) (hb.trans (map_zero seedMap).symm)
  have h0 : (0 : Seeds).coeff m = 0 := by simp
  rw [← coeff_coeffDx, h, h0]
theorem clear_product {q : Equation} (T : DifferentialData q) (J : Input) (B : ResidueLift J)
    (hsep : (generic q).Separable)
    (hconst : ∀ i j, T.split (((splitProduct J B q).coeff i).coeff j) = 0) :
    Nonempty (DifferentialProduct J B q) := by
  let α := algebraMap SeedField (SplitField q)
  obtain ⟨P, hP⟩ := splitProduct_descend J B q hsep
  have hcoeff (i : ℕ) : (P.coeff i).map α = (splitProduct J B q).coeff i := by
    exact (coeff_map (p := P) (mapRingHom α) i).symm.trans
      (congrArg (fun Q => Q.coeff i) hP)
  have hbase (i j : ℕ) : T.base ((P.coeff i).coeff j) = 0 := by
    apply α.injective
    rw [← T.extends_base, ← coeff_map, hcoeff, hconst, map_zero]
  obtain ⟨b, hb, N, hN⟩ := clear_two P
  let b₀ := b ^ P1.p
  let A : Polynomial (Polynomial Seeds) := C (C (b ^ (P1.p-1))) * N
  have hpow : b ^ (P1.p-1) * b = b₀ := by
    change b ^ (P1.p-1) * b = b ^ P1.p
    have hp : 1 ≤ P1.p := KoalaBear.is_prime.pos
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have hA : A.map (mapRingHom seedMap) = C (C (seedMap b₀)) * P := by
    simp only [A, Polynomial.map_mul, Polynomial.map_C, coe_mapRingHom]
    rw [hN, ← mul_assoc, ← C_mul, ← C_mul, ← map_mul, hpow]
  have hb₀ : T.base (seedMap b₀) = 0 := by
    let := charSeed
    have hp : (P1.p : SeedField) = 0 := CharP.cast_eq_zero _ _
    rw [show seedMap b₀ = seedMap b ^ P1.p from map_pow _ _ _,
      Derivation.leibniz_pow, nsmul_eq_mul, hp, zero_mul]
  have hAc (i : ℕ) : (A.coeff i).map seedMap = C (seedMap b₀) * P.coeff i := by
    have h := congrArg (fun Q : Polynomial (Polynomial SeedField) => Q.coeff i) hA
    simpa only [coeff_map, coeff_C_mul, coe_mapRingHom] using h
  refine ⟨⟨A, b₀, pow_ne_zero _ hb, ?_, ?_, ?_, dx_zero_of_base T _ hb₀, ?_⟩⟩
  · have ht : P.coeff q.natDegree = 1 :=
      (Polynomial.map_injective α α.injective) (by
        rw [hcoeff, coeff_splitProduct_top J B q hsep, Polynomial.map_one])
    apply Polynomial.map_injective seedMap (IsFractionRing.injective Seeds SeedField)
    rw [hAc, ht, mul_one, Polynomial.map_C]
  · intro i
    rw [← natDegree_map_eq_of_injective (IsFractionRing.injective Seeds SeedField) (A.coeff i), hAc]
    apply natDegree_mul_le.trans
    rw [natDegree_C, zero_add, ← natDegree_map α, hcoeff]
    exact splitProduct_width J B q i
  · intro i j m
    apply dx_zero_of_base T _ _ m
    rw [← coeff_map, hAc, coeff_C_mul, T.base.leibniz, hbase, hb₀]
    simp
  · let γ : SeedField →+* SeedClosure := algebraMap SeedField SeedClosure
    have hγ : γ.comp seedMap = intoSeedClosure := rfl
    have hα : (splitting q).val.toRingHom.comp α = γ := rfl
    have hPγ : P.map (mapRingHom γ) =
        ∏ y ∈ genericRoots q, (Polynomial.X - C (reconstructed J B y)) := by
      rw [← splitProduct_closure J B q, ← hP, Polynomial.map_map, mapRingHom_comp, hα]
    rw [← hγ, ← mapRingHom_comp, ← Polynomial.map_map, hA, Polynomial.map_mul,
      Polynomial.map_C, coe_mapRingHom, Polynomial.map_C, hPγ]
    rfl
end
end HighCore82706Tangent_4
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_4
noncomputable section
open Polynomial
open HighCore82706Tangent
open K1_14 (Equation)
def c1 : Prop :=
  ∀ q : Equation, (generic q).Separable → Nonempty (DifferentialData q)
def c2 : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B) (j : Fin D.count)
    (T : DifferentialData (D.flat j)) (y : SplitField (D.flat j)),
    y ∈ geomRoots (D.flat j) → ∀ r ≤ J.ell + 1,
    jet (splitMap (D.flat j)) B y r =
      (T.split^[r]) (quotientValue (splitMap (D.flat j)) B y) /
        (r.factorial : SplitField (D.flat j))
private theorem jet_omitted_zero (J : Input) (B : ResidueLift J) (D : Factors J B)
    (j : Fin D.count) (y : SplitField (D.flat j)) (hy : y ∈ geomRoots (D.flat j)) :
    jet (splitMap (D.flat j)) B y (J.ell+1) = 0 := by
  classical
  let q := D.flat j
  have hroot : (generic q).aeval y = 0 := by
    apply aeval_eq_zero_of_mem_rootSet
    rwa [rootSet_def]
  obtain ⟨a, ha⟩ := D.flat_cutoff j
  have hcut : (generic (cutoff J B)).aeval y = 0 := by
    rw [ha, map_mul, hroot, zero_mul]
  unfold jet
  rw [show point (splitMap q) y (quotientNumerator J B (J.ell+1)) = 0 from by
    change (cutoff J B).eval₂ (splitMap q) y = 0
    simpa only [aeval_def, generic, eval₂_map] using hcut, zero_div]
theorem of_children (h₁ : c1) (h₂ : c2) : HighCore82706Tangent.c4 := by
  intro J B D j
  let q := D.flat j
  have hsep : (generic q).Separable := (D.flat_reduced j).2.2
  obtain ⟨T⟩ := h₁ q hsep
  have hfac : ∀ r ≤ J.ell + 1, (r.factorial : SplitField q) ≠ 0 := by
    let := charSplit q
    intro r hr hzero
    have hrt : r < P1.p := by
      have h := J.factorial_guard
      change 131071 + J.hi + 1 < P1.p at h
      change r ≤ (131071 - J.w) + 1 at hr
      omega
    exact (not_le_of_gt hrt) (KoalaBear.is_prime.dvd_factorial.mp
      ((CharP.cast_eq_zero_iff (SplitField q) P1.p _).mp hzero))
  apply clear_product T J B hsep
  apply splitProduct_constant T J B
  intro y hy
  have hjet := h₂ J B D j T y hy
  have hz := (hjet _ le_rfl).symm.trans (jet_omitted_zero J B D j y hy)
  apply reconstructed_constant T J B y
  · exact fun r hr => hjet r (hr.trans (Nat.le_succ _))
  · exact (div_eq_zero_iff.mp hz).resolve_right (hfac _ le_rfl)
  · exact fun r hr => hfac r (hr.trans (Nat.le_succ _))
end
end HighCore82706Tangent_4
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_4_1
noncomputable section
open Polynomial
open K1_14 (L FX Seeds Equation)
open K1_14_6_1 (Dx Dx_mul)
open HighCore82706Tangent (SeedConstants SeedField center constantAbscissa liftSeeds generic)
open HighCore82706Tangent_4 (SplitField coeffDx coeff_coeffDx seedMap)
open private rationalJet rationalJet_incl from ProximityPrize.SubmissionLower.Fast055
open private lift_derivation from ProximityPrize.SubmissionLower.Fast073
private theorem Dx_polynomial (f : L[X]) :
    Dx (algebraMap L[X] FX f) = algebraMap L[X] FX f.derivative := by
  change (rationalJet (algebraMap L[X] FX f)).snd = _
  rw [rationalJet_incl]
  rfl
private theorem Dx_constantAbscissa (a : L) : Dx (constantAbscissa a) = 0 := by
  change Dx (algebraMap L[X] FX (C a)) = 0
  rw [Dx_polynomial, derivative_C, map_zero]
private theorem Dx_center : Dx center = 1 := by
  unfold center
  rw [Dx_polynomial, derivative_X, map_one]
set_option backward.isDefEq.respectTransparency false in
private def intDerivation {A : Type*} [CommRing A] (d : A →+ A)
    (hmul : ∀ a b, d (a * b) = a * d b + b * d a) : Derivation ℤ A A :=
  Derivation.mk' d.toIntLinearMap hmul
private def transportIntAlgebra {A : Type*} [CommRing A] {source target : Algebra ℤ A}
    (d : @Derivation ℤ A A inferInstance inferInstance inferInstance source
      inferInstance inferInstance) :
    @Derivation ℤ A A inferInstance inferInstance inferInstance target
      inferInstance inferInstance :=
  Subsingleton.elim source target ▸ d
private theorem transportIntAlgebra_apply {A : Type*} [CommRing A]
    {source target : Algebra ℤ A}
    (d : @Derivation ℤ A A inferInstance inferInstance inferInstance source
      inferInstance inferInstance) (a : A) :
    transportIntAlgebra (target := target) d a = d a := by
  have h : source = target := Subsingleton.elim _ _
  subst target
  rfl
private theorem coeffDx_mul (U V : Seeds) :
    coeffDx (U * V) = U * coeffDx V + V * coeffDx U := by
  classical
  rw [mul_comm V (coeffDx U)]
  apply MvPolynomial.ext
  intro m
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_mul,
    coeff_coeffDx, map_sum, Dx_mul, Finset.sum_add_distrib]
private theorem coeffDx_C (a : FX) : coeffDx (MvPolynomial.C a : Seeds) = MvPolynomial.C (Dx a) := by
  classical
  apply MvPolynomial.ext
  intro m
  by_cases h : 0 = m <;>
    simp only [coeff_coeffDx, MvPolynomial.coeff_C, h, ite_true, ite_false, map_zero]
private theorem coeffDx_liftSeeds (s : SeedConstants) : coeffDx (liftSeeds s) = 0 := by
  apply MvPolynomial.ext
  intro m
  simp only [coeff_coeffDx, liftSeeds, MvPolynomial.coeff_map, Dx_constantAbscissa,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
set_option backward.isDefEq.respectTransparency false in
theorem proof : HighCore82706Tangent_4.c1 := by
  intro q hsep
  let : Algebra.FormallyEtale Seeds SeedField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Seeds)
  obtain ⟨base, extendsSeed⟩ := lift_derivation (A := Seeds) (B := SeedField)
    (intDerivation (A := Seeds) coeffDx coeffDx_mul)
  let : Algebra.IsSeparable SeedField (SplitField q) :=
    Algebra.isSeparable_of_separable_splitting_field SeedField (SplitField q) hsep
  let : Algebra.FormallyEtale SeedField (SplitField q) :=
    Algebra.FormallyEtale.of_isSeparable SeedField (SplitField q)
  obtain ⟨split, extendsBase⟩ := lift_derivation (A := SeedField) (B := SplitField q) base
  change ∀ s : Seeds, base (seedMap s) = seedMap (coeffDx s) at extendsSeed
  refine ⟨⟨transportIntAlgebra base, transportIntAlgebra split, ?_, ?_, ?_, ?_⟩⟩
  · intro s
    simpa only [transportIntAlgebra_apply] using extendsSeed s
  · intro a
    simpa only [transportIntAlgebra_apply] using extendsBase a
  · simp only [HighCore82706Tangent_4.origin, HighCore82706Tangent_4.splitMap, RingHom.comp_apply, transportIntAlgebra_apply]
    rw [extendsBase, extendsSeed, coeffDx_C, Dx_center, map_one, map_one, map_one]
  · intro s
    simp only [HighCore82706Tangent_4.splitMap, RingHom.comp_apply, transportIntAlgebra_apply]
    rw [extendsBase, extendsSeed, coeffDx_liftSeeds, map_zero, map_zero]
end
end HighCore82706Tangent_4_1
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_4_2
noncomputable section
open Polynomial Finset HighCore82706Tangent HighCore82706Tangent_4
open K1_14 (FX Seeds Equation)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx flatten separant partialX cleared tangent)
open private K1_14_6_1.partialX_C K1_14_6_1.partialX_mul_X from ProximityPrize.SubmissionLower.Fast055
abbrev embed (q : Equation) : FX →+* SplitField q :=
  (splitMap q).comp MvPolynomial.C
theorem point_C {q : Equation} (y : SplitField q) (a : FX) :
    point (splitMap q) y (MvPolynomial.C a) = embed q a := by
  change eval₂ (splitMap q) y (MvPolynomial.optionEquivLeft FX (Fin 2) (MvPolynomial.C a)) = _
  rw [MvPolynomial.optionEquivLeft_C, eval₂_C]
  rfl
private theorem point_Y {q : Equation} (y : SplitField q) :
    point (splitMap q) y (MvPolynomial.X (R := FX) (none : Option (Fin 2))) = y := by
  change eval₂ (splitMap q) y (MvPolynomial.optionEquivLeft FX (Fin 2) (MvPolynomial.X none)) = _
  rw [MvPolynomial.optionEquivLeft_X_none, eval₂_X]
private theorem point_seedVar {q : Equation} (y : SplitField q) (i : Fin 2) :
    point (splitMap q) y (MvPolynomial.X (R := FX) (some i)) =
      splitMap q (liftSeeds (MvPolynomial.X i)) := by
  change eval₂ (splitMap q) y (MvPolynomial.optionEquivLeft FX (Fin 2) (MvPolynomial.X (some i))) = _
  rw [MvPolynomial.optionEquivLeft_X_some, eval₂_C, liftSeeds, MvPolynomial.map_X]
theorem point_seed {q : Equation} (y : SplitField q) :
    (point (splitMap q) y).comp seedBiform = (splitMap q).comp liftSeeds := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change point (splitMap q) y (MvPolynomial.rename some (MvPolynomial.map constantAbscissa
      (MvPolynomial.C a))) = splitMap q (MvPolynomial.map constantAbscissa (MvPolynomial.C a))
    rw [MvPolynomial.map_C, MvPolynomial.rename_C, point_C]
    rfl
  · intro i
    change point (splitMap q) y (MvPolynomial.rename some (MvPolynomial.map constantAbscissa
      (MvPolynomial.X i))) = _
    rw [MvPolynomial.map_X, MvPolynomial.rename_X, point_seedVar]
    rfl
theorem split_embed {q : Equation} (T : DifferentialData q) (a : FX) :
    T.split (embed q a) = embed q (Dx a) := by
  change T.split (algebraMap SeedField (SplitField q) (seedMap (MvPolynomial.C a))) =
    algebraMap SeedField (SplitField q) (seedMap (MvPolynomial.C (Dx a)))
  rw [T.extends_base, T.extends_seed]
  apply congrArg (fun s : Seeds => algebraMap SeedField (SplitField q) (seedMap s))
  apply MvPolynomial.ext
  intro m
  classical
  by_cases h : (0 : Fin 2 →₀ ℕ) = m <;>
    simp [coeff_coeffDx, MvPolynomial.coeff_C, h]
private theorem split_mul {q : Equation} (T : DifferentialData q) (a b : SplitField q) :
    T.split (a * b) = a * T.split b + T.split a * b := by
  rw [T.split.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b]
private theorem split_point {q : Equation} (T : DifferentialData q) (y : SplitField q)
    (P : Biform) :
    T.split (point (splitMap q) y P) =
      point (splitMap q) y (partialX P) +
        T.split y * point (splitMap q) y (MvPolynomial.pderiv none P) := by
  let ev := point (splitMap q) y
  change T.split (ev P) = ev (partialX P) + T.split y * ev (MvPolynomial.pderiv none P)
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [ev, K1_14_6_1.partialX_C, point_C, MvPolynomial.pderiv_C, map_zero, mul_zero, add_zero]
    exact split_embed T a
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ, mul_add]
    ring
  | mul_X P i hP =>
    have hi : T.split (ev (MvPolynomial.X i)) =
        T.split y * ev (MvPolynomial.pderiv none (MvPolynomial.X i)) := by
      cases i with
      | none => simp [ev, point_Y]
      | some j =>
        rw [show ev (MvPolynomial.X (some j)) = _ from point_seedVar y j,
          MvPolynomial.pderiv_X_of_ne (Option.some_ne_none j), map_zero, mul_zero]
        exact T.frozen _
    simp only [map_mul, split_mul T, hP, K1_14_6_1.partialX_mul_X, MvPolynomial.pderiv_mul, map_add, hi]
    ring
private theorem eval_tangent {q : Equation} (T : DifferentialData q) (y : SplitField q)
    (f P : Biform) (hf : point (splitMap q) y f = 0) :
    point (splitMap q) y (tangent f P) =
      point (splitMap q) y (separant f) * T.split (point (splitMap q) y P) := by
  have h := split_point T y f
  rw [hf, map_zero] at h
  rw [split_point T, tangent, map_sub, map_mul, map_mul]
  linear_combination -point (splitMap q) y (MvPolynomial.pderiv none P) * (Eq.symm h)
private theorem cleared_product_rule {q : Equation} (T : DifferentialData q)
    (m : ℕ) (a v : SplitField q) :
    a * (a * T.split (a^m * v)) - (m : SplitField q) * (a * T.split a) * (a^m * v) =
      a^(m+2) * T.split v := by
  cases m with
  | zero => simp [pow_two, mul_assoc]
  | succ m =>
    rw [split_mul T, T.split.leibniz_pow, Nat.succ_sub_one, pow_add a (m+1) 2, pow_succ' a m]
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
private theorem eval_cleared {q : Equation} (T : DifferentialData q) (y : SplitField q)
    (f : Biform) (hf : point (splitMap q) y f = 0) (n : ℕ) :
    point (splitMap q) y (cleared f n) =
      point (splitMap q) y (separant f) ^ (2*n+1) * (T.split^[n+1]) y := by
  induction n with
  | zero =>
    have h := split_point T y f
    rw [hf, map_zero] at h
    simp only [cleared, map_neg, Nat.mul_zero, Nat.zero_add, pow_one, Function.iterate_one]
    linear_combination -(Eq.symm h)
  | succ n ih =>
    rw [cleared, map_sub, map_mul, map_mul, map_mul, point_C, eval_tangent T _ _ _ hf,
      eval_tangent T _ _ _ hf, ih, map_natCast, cleared_product_rule T,
      show 2*(n+1)+1 = 2*n+1+2 by omega, Function.iterate_succ_apply' T.split (n+1) y]
theorem ordinate {q : Equation} (T : DifferentialData q) (y : SplitField q)
    (f : Equation) (hf : point (splitMap q) y (flatten f) = 0) {r i : ℕ} (hi : i ≤ r) :
    point (splitMap q) y (ordinateTaylorNum f r i) =
      point (splitMap q) y (separant (flatten f))^(2*r-1) *
        ((T.split^[i]) y / (i.factorial : SplitField q)) := by
  cases i with
  | zero => simp [ordinateTaylorNum, point_Y]
  | succ i =>
    rw [ordinateTaylorNum, map_mul, map_mul, map_pow, point_C,
      eval_cleared T y _ hf, map_inv₀, map_natCast]
    let a := point (splitMap q) y (separant (flatten f))
    have hp : a ^ (2*r-1-(2*i+1)) * a ^ (2*i+1) = a ^ (2*r-1) := by
      rw [← pow_add, show (2*r-1-(2*i+1))+(2*i+1) = 2*r-1 by omega]
    change _ * (a^_ * (a^_ * (T.split^[i+1]) y)) = a^_ * _
    rw [← mul_assoc (a^_) (a^_), hp]
    ring
private theorem point_flatten {q : Equation} (y : SplitField q) (f : Equation) :
    point (splitMap q) y (flatten f) = (generic f).aeval y := by
  change eval₂ (splitMap q) y ((MvPolynomial.optionEquivLeft FX (Fin 2))
    ((MvPolynomial.optionEquivLeft FX (Fin 2)).symm f)) = _
  rw [AlgEquiv.apply_symm_apply, aeval_def, generic, eval₂_map]
theorem regular {J : Input} {B : ResidueLift J} (D : Factors J B) (j : Fin D.count)
    (y : SplitField (D.flat j)) (hy : y ∈ geomRoots (D.flat j)) :
    point (splitMap (D.flat j)) y (flatten J.f) = 0 ∧
      point (splitMap (D.flat j)) y (separant (flatten J.f)) ≠ 0 := by
  classical
  have hj : (generic (D.flat j)).aeval y = 0 := by
    apply aeval_eq_zero_of_mem_rootSet
    rwa [rootSet_def]
  have hf : (generic J.f).aeval y = 0 := by
    have hd : D.flat j ∣ J.f := by
      rw [D.product]
      exact dvd_mul_of_dvd_right (dvd_prod_of_mem D.flat (mem_univ j)) _
    obtain ⟨g, hg⟩ := hd
    simp only [hg, generic, Polynomial.map_mul, map_mul]
    rw [show ((D.flat j).map (algebraMap Seeds SeedField)).aeval y = 0 from hj, zero_mul]
  refine ⟨(point_flatten y J.f).trans hf, ?_⟩
  have he : separant (flatten J.f) = flatten J.f.derivative := by
    apply (MvPolynomial.optionEquivLeft FX (Fin 2)).injective
    rw [MvPolynomial.optionEquivLeft_pderiv_none, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rw [he, point_flatten, generic, ← Polynomial.derivative_map]
  exact J.reduced.2.2.aeval_derivative_ne_zero hf
end
end HighCore82706Tangent_4_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_4_2
noncomputable section
open Polynomial Finset HighCore82706Tangent HighCore82706Tangent_4
open K1_14 (L FX Equation)
open K1_14_6_1 (Dx)
def divided {F : Type} [Field F] (δ : Derivation ℤ F F) (a : F) (i : ℕ) : F :=
  (i.factorial : F)⁻¹ * (δ^[i]) a
private theorem iterate_mul {F : Type} [Field F] (δ : Derivation ℤ F F) (a b : F) (n : ℕ) :
    (δ^[n]) (a*b) = ∑ k ∈ range (n+1), n.choose k • ((δ^[n-k]) a * (δ^[k]) b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit :
        (∑ k ∈ range (n+1), n.choose k • ((δ^[n-k+1]) a * (δ^[k]) b)) =
        (∑ k ∈ range (n+1), n.choose (k+1) • ((δ^[n-k]) a * (δ^[k+1]) b)) +
          (δ^[n+1]) a * b := by
      rw [sum_range_succ', Nat.choose_zero_right, one_smul, tsub_zero,
        Function.iterate_zero_apply]
      congr 1
      rw [sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero]
      refine sum_congr rfl fun k hk => ?_
      rw [show n - (k+1) + 1 = n-k by have := mem_range.mp hk; omega]
    calc
      _ = δ (∑ k ∈ range (n+1), n.choose k • ((δ^[n-k]) a * (δ^[k]) b)) := by
        rw [Function.iterate_succ_apply', ih]
      _ = (∑ k ∈ range (n+1), n.choose k • ((δ^[n-k+1]) a * (δ^[k]) b)) +
          ∑ k ∈ range (n+1), n.choose k • ((δ^[n-k]) a * (δ^[k+1]) b) := by
        simp only [map_sum, map_nsmul, δ.leibniz, smul_eq_mul, nsmul_add, sum_add_distrib]
        rw [add_comm]
        simp only [Function.iterate_succ_apply']
        congr 1
        exact sum_congr rfl fun _ _ => by rw [mul_comm]
      _ = _ := by
        rw [hsplit, add_right_comm, ← sum_add_distrib, sum_range_succ' _ (n+1)]
        simp only [Nat.choose_zero_right, one_smul, tsub_zero, Function.iterate_zero_apply,
          Nat.choose_succ_succ, Nat.succ_sub_succ, add_smul]
        congr 1
        exact sum_congr rfl fun k _ => add_comm _ _
theorem divided_mul {F : Type} [Field F] (δ : Derivation ℤ F F) (a b : F) {n : ℕ}
    (hfac : ∀ i ≤ n, (i.factorial : F) ≠ 0) :
    divided δ (a*b) n = ∑ i ∈ range (n+1), divided δ a (n-i) * divided δ b i := by
  unfold divided
  rw [iterate_mul, Finset.mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hle : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hs : (n.factorial : F)⁻¹ * (n.choose i : F) =
      ((n-i).factorial : F)⁻¹ * (i.factorial : F)⁻¹ := by
    have h := congrArg (fun k : ℕ => (k : F)) (Nat.choose_mul_factorial_mul_factorial hle)
    push_cast at h
    field_simp [hfac n le_rfl, hfac i hle, hfac (n-i) (Nat.sub_le _ _)]
    linear_combination h
  rw [nsmul_eq_mul, ← mul_assoc, hs]
  ring
theorem divided_sub {F : Type} [Field F] (δ : Derivation ℤ F F) (a b : F) (i : ℕ) :
    divided δ (a-b) i = divided δ a i - divided δ b i := by
  have h : (δ^[i]) (a-b) = (δ^[i]) a - (δ^[i]) b := by
    induction i with
    | zero => rfl
    | succ i ih => simp only [Function.iterate_succ_apply', ih, map_sub]
  simp only [divided, h, mul_sub]
theorem divided_const_mul {F : Type} [Field F] (δ : Derivation ℤ F F) (c a : F)
    (hc : δ c = 0) (i : ℕ) : divided δ (c*a) i = c * divided δ a i := by
  have h : (δ^[i]) (c*a) = c * (δ^[i]) a := by
    induction i with
    | zero => rfl
    | succ i ih =>
      simp only [Function.iterate_succ_apply', ih, δ.leibniz, smul_eq_mul, hc, mul_zero, add_zero]
  simp only [divided, h, mul_left_comm]
private theorem iterate_eval {q : Equation} (T : DifferentialData q)
    (N : SeedConstants[X]) (i : ℕ) :
    (T.split^[i]) ((N.map ((splitMap q).comp liftSeeds)).eval (origin (splitMap q))) =
      ((Polynomial.derivative^[i]) (N.map ((splitMap q).comp liftSeeds))).eval
        (origin (splitMap q)) := by
  let κ := (splitMap q).comp liftSeeds
  let x := origin (splitMap q)
  have hone (P : SeedConstants[X]) : T.split ((P.map κ).eval x) =
      (P.derivative.map κ).eval x := by
    rw [← Polynomial.derivative_map, T.split.apply_eval_eq]
    have hcoeff : T.split.mapCoeffs (P.map κ) = 0 := by
      apply PolynomialModule.coeff_injective
      apply Finsupp.ext
      intro k
      rw [Derivation.mapCoeffs_apply, coeff_map, PolynomialModule.coeff_zero]
      exact T.frozen _
    simp [hcoeff, x, T.center_one, smul_eq_mul]
  rw [Polynomial.iterate_derivative_map]
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, hone, Function.iterate_succ_apply']
theorem numerator_taylor {q : Equation} (T : DifferentialData q) (y : SplitField q)
    (N : SeedConstants[X]) (i : ℕ) (hi : (i.factorial : SplitField q) ≠ 0) :
    point (splitMap q) y (liftTaylor N i) =
      divided T.split ((N.map ((splitMap q).comp liftSeeds)).eval (origin (splitMap q))) i := by
  rw [liftTaylor, ← Polynomial.coeff_map, Polynomial.map_taylor, Polynomial.map_map,
    point_seed, point_C, Polynomial.taylor_coeff, divided, iterate_eval]
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := SplitField q) i)
    (N.map ((splitMap q).comp liftSeeds))
  rw [← h, LinearMap.smul_apply, eval_smul, nsmul_eq_mul, inv_mul_cancel_left₀ hi]
  rfl
theorem eval_blocks {q : Equation} (J : Input) :
    (blocks (splitMap q) J).eval (origin (splitMap q)) =
      embed q (algebraMap L[X] FX J.blockProduct) := by
  have hc : ((splitMap q).comp liftSeeds).comp MvPolynomial.C =
      (embed q).comp constantAbscissa := by
    apply RingHom.ext
    intro a
    change splitMap q (MvPolynomial.map constantAbscissa (MvPolynomial.C a)) =
      splitMap q (MvPolynomial.C (constantAbscissa a))
    rw [MvPolynomial.map_C]
  rw [blocks, eval_map, hc, show origin (splitMap q) = embed q center from rfl, ← hom_eval₂]
  congr 1
  unfold constantAbscissa center
  rw [← hom_eval₂, eval₂_C_X]
theorem inverse_block_taylor {q : Equation} (T : DifferentialData q) (J : Input) (i : ℕ) :
    embed q (inverseBlockCoeff J i) =
      divided T.split ((blocks (splitMap q) J).eval (origin (splitMap q)))⁻¹ i := by
  have hiter (a : FX) (n : ℕ) : embed q ((Dx^[n]) a) = (T.split^[n]) (embed q a) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ← split_embed T, ih,
        Function.iterate_succ_apply']
  rw [inverseBlockCoeff, divided, eval_blocks, map_mul, map_inv₀, map_natCast, hiter, map_inv₀]
end
end HighCore82706Tangent_4_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_4_2
noncomputable section
open Polynomial Finset HighCore82706Tangent HighCore82706Tangent_4
open K1_14 (L FX)
open K1_14_6_1 (flatten separant)
theorem proof : HighCore82706Tangent_4.c2 := by
  classical
  intro J B D j T y hy r hr
  let q := D.flat j
  let ι := splitMap q
  let ev := point ι y
  let a := ι (liftSeeds B.denominator)
  let s := ev (separant (flatten J.f)) ^ (2*r-1)
  let t := (B.numerator.map (ι.comp liftSeeds)).eval (origin ι)
  let g := (blocks ι J).eval (origin ι)
  have ha : a ≠ 0 := by
    have hψ : Function.Injective constantAbscissa :=
      (IsFractionRing.injective L[X] FX).comp Polynomial.C_injective
    have hι : Function.Injective ι :=
      (algebraMap SeedField (SplitField q)).injective.comp (IsFractionRing.injective _ _)
    have hmap : Function.Injective (ι.comp liftSeeds) :=
      hι.comp (MvPolynomial.map_injective _ hψ)
    exact (map_ne_zero_iff _ hmap).mpr B.denominator_ne
  obtain ⟨hf, hs⟩ := regular D j y hy
  have hfac (i : ℕ) (hi : i ≤ r) : (i.factorial : SplitField q) ≠ 0 := by
    let := charSplit q
    have hguard := J.factorial_guard
    change 131071 + J.hi + 1 < P1.p at hguard
    change r ≤ 131071 - J.w + 1 at hr
    intro hzero
    exact (show ¬ P1.p ≤ i by omega) (KoalaBear.is_prime.dvd_factorial.mp
      ((CharP.cast_eq_zero_iff (SplitField q) P1.p _).mp hzero))
  have hseed : ev (seedBiform B.denominator) = a :=
    RingHom.congr_fun (point_seed y) B.denominator
  have hcrt : (crt ι B).eval (origin ι) = a⁻¹ * t := by
    rw [crt, eval_mul, eval_C] <;> rfl
  have hconst : T.split a⁻¹ = 0 := by
    rw [T.split.leibniz_inv, show T.split a = 0 from T.frozen _, smul_zero]
  have hnum : ev (quotientNumerator J B r) =
      (a*s) * divided T.split (quotientValue ι B y) r := by
    rw [quotientValue, hcrt, div_eq_inv_mul, ← show g = (blocks ι J).eval (origin ι) from rfl,
      divided_mul _ _ _ hfac, quotientNumerator, map_sum, Finset.mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hir : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
    simp only [map_mul, map_sub, map_pow]
    rw [point_C, inverse_block_taylor T, hseed, ordinate T y J.f hf hir,
      numerator_taylor T y _ i (hfac i hir), divided_sub, divided_const_mul _ _ _ hconst]
    change divided T.split g⁻¹ (r-i) *
        (a * (s * ((T.split^[i]) y / (i.factorial : SplitField q))) -
          s * divided T.split t i) =
      a * s * (divided T.split g⁻¹ (r-i) *
        (divided T.split y i - a⁻¹ * divided T.split t i))
    rw [show (T.split^[i]) y / (i.factorial : SplitField q) = divided T.split y i by
      rw [divided, div_eq_inv_mul]]
    have hcancel (z : SplitField q) : a * (a⁻¹ * z) = z :=
      mul_inv_cancel_left₀ ha z
    calc
      _ = s * (divided T.split g⁻¹ (r-i) *
          (a * divided T.split y i - divided T.split t i)) := by ring
      _ = _ := by
        conv_lhs => rw [← hcancel (divided T.split t i)]
        ring
  have hden : ev (quotientDenominator J B r) = a * s := by
    rw [quotientDenominator, map_mul, hseed, map_pow]
  change ev (quotientNumerator J B r) / ev (quotientDenominator J B r) = _
  rw [hnum, hden, mul_comm (a*s), mul_div_cancel_right₀ _ (mul_ne_zero ha (pow_ne_zero _ hs))]
  rw [divided, div_eq_inv_mul]
end
end HighCore82706Tangent_4_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_5_1
noncomputable section
open Polynomial
open P1 (K)
open K1_14 (L FX Equation seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant markEval)
open HighCore82706Tangent (Input ResidueLift Factors SeedField SeedClosure intoSeedClosure center
  constantAbscissa liftSeeds seedBiform liftConstantSeeds genericPoint genericRoots reconstructed)
open HighCore82706Tangent_5 (evalRoot evalMark embedFX)
open HighCore82706Tangent_5 (genericPoint_C genericPoint_seed seed_nonzero)
open HighCore82706Tangent_5 (root_of_mem)
private abbrev toEquation : Biform ≃ₐ[FX] Equation := MvPolynomial.optionEquivLeft FX (Fin 2)
private theorem eval_mark_equation (J : Input) (γ : K) (H : Biform) :
    evalMark J γ (toEquation H) = markEval (J.model.label γ) (J.family.scalar γ) H := by
  have h := (K1_14_6_1.eval_flatten (J.model.label γ) (J.family.scalar γ) (toEquation H)).symm
  rw [show flatten (toEquation H) = H from toEquation.symm_apply_apply H] at h
  exact h
private theorem generic_valuePolynomial (J : Input) (B : ResidueLift J) (y : SeedClosure) :
    valuePolynomial (genericPoint y) J B = reconstructed J B y := by
  have hb : genericPoint y (seedBiform B.denominator) = liftConstantSeeds B.denominator :=
    RingHom.congr_fun (genericPoint_seed y) _
  have hg : (genericPoint y).comp constantLift = liftConstantSeeds.comp MvPolynomial.C := by
    apply RingHom.ext
    intro a
    change genericPoint y (MvPolynomial.C (constantAbscissa a)) =
      intoSeedClosure (MvPolynomial.map constantAbscissa (MvPolynomial.C a))
    rw [genericPoint_C, MvPolynomial.map_C]
    rfl
  rw [valuePolynomial, reconstructed, hb, genericPoint_seed, hg, genericPoint_C]
  rfl
private theorem generic_separant (J : Input) (B : ResidueLift J) (D : Factors J B)
    (j : Fin D.count) {y : SeedClosure} (hy : y ∈ genericRoots (D.flat j)) :
    genericPoint y (separant (flatten J.f)) ≠ 0 := by
  classical
  have hdiv : D.flat j ∣ J.f := by
    rw [D.product]
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem D.flat (Finset.mem_univ j)) _
  obtain ⟨Q, hQ⟩ := hdiv
  have hz : evalRoot y J.f = 0 := by
    rw [hQ, map_mul, root_of_mem hy, zero_mul]
  have hsep : (J.f.map intoSeedClosure).Separable := by
    simpa only [Polynomial.map_map, intoSeedClosure] using
      (J.reduced.2.2.map (f := algebraMap SeedField SeedClosure))
  have hz' : (J.f.map intoSeedClosure).eval₂ (RingHom.id SeedClosure) y = 0 := by
    simpa only [eval₂_id, eval_map, evalRoot, coe_eval₂RingHom] using hz
  have hd := hsep.eval₂_derivative_ne_zero (RingHom.id SeedClosure) hz'
  change evalRoot y (toEquation (separant (flatten J.f))) ≠ 0
  rw [MvPolynomial.optionEquivLeft_pderiv_none, toEquation.apply_symm_apply]
  simpa only [eval₂_id, derivative_map, eval_map, evalRoot, coe_eval₂RingHom] using hd
theorem proof : HighCore82706Tangent_5.c1 := by
  intro J B D j
  refine ⟨⟨toEquation (denominator J B), fun x => toEquation (numerator J B x), ?_, ?_⟩⟩
  · intro y hy x
    have hb : genericPoint y (seedBiform B.denominator) ≠ 0 := by
      rw [show genericPoint y (seedBiform B.denominator) = liftConstantSeeds B.denominator from
        RingHom.congr_fun (genericPoint_seed y) _]
      exact seed_nonzero B.denominator_ne
    change genericPoint y (numerator J B x) = genericPoint y (denominator J B) *
      (reconstructed J B y).eval (embedFX (seedEmbedding x))
    rw [← generic_valuePolynomial J B y, ← genericPoint_C y]
    exact cleared_value (genericPoint y) J B hb (generic_separant J B D j hy) x
  · intro γ hγ _
    simpa only [eval_mark_equation] using marked_value J B γ hγ
end
end HighCore82706Tangent_5_1
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_5_2
noncomputable section
open Polynomial
open K1_14 (FX Seeds atX liftPoly seedEmbedding)
open K1_14_6_1 (Dx Dx_mul Dx_atX)
open P1 (K p)
open HighCore82706Tangent (center)
open HighCore82706Tangent_4 (coeffDx coeff_coeffDx)
open HighCore82706Tangent_5 (CoeffConstant)
private def δ : Derivation ℤ Seeds Seeds where
  toFun := coeffDx
  map_add' := map_add coeffDx
  map_smul' n a := by
    rw [RingHom.id_apply, Algebra.smul_def, eq_intCast, ← zsmul_eq_mul]
    exact map_zsmul coeffDx n a
  map_one_eq_zero' := by
    change coeffDx 1 = 0
    ext s
    have h₁ : Dx 1 = 0 := by
      simpa only [atX, liftPoly, derivative_one, Polynomial.map_one, Polynomial.map_zero,
        map_one, map_zero] using (Dx_atX (1 : K[X]))
    by_cases hs : (0 : Fin 2 →₀ ℕ) = s <;>
      simp [coeff_coeffDx, MvPolynomial.coeff_one, hs, h₁]
  leibniz' a b := by
    classical
    change coeffDx (a * b) = a * coeffDx b + b * coeffDx a
    rw [mul_comm b (coeffDx a)]
    ext s
    simp only [coeff_coeffDx, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      MvPolynomial.coeff_mul, map_sum, Dx_mul, Finset.sum_add_distrib]
private theorem constant_derivative {f : Seeds} (hf : CoeffConstant f) : δ f = 0 := by
  change coeffDx f = 0
  ext s
  simpa only [coeff_coeffDx, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hf s
private abbrev ξ : Seeds := MvPolynomial.C center
private theorem derivative_center : δ ξ = 1 := by
  change coeffDx (MvPolynomial.C center) = 1
  have hc : Dx center = 1 := by
    simpa only [atX, liftPoly, center, map_X, derivative_X, Polynomial.map_one, map_one]
      using (Dx_atX (Polynomial.X (R := K)))
  classical
  ext s
  by_cases hs : (0 : Fin 2 →₀ ℕ) = s <;>
    simp [coeff_coeffDx, MvPolynomial.coeff_C, MvPolynomial.coeff_one, hs, hc]
private theorem charFX : CharP FX p :=
  charP_of_injective_ringHom seedEmbedding.injective p
private theorem charSeeds : CharP Seeds p := by
  let := charFX
  exact charP_of_injective_ringHom (MvPolynomial.C_injective (Fin 2) FX) p
private theorem factorial_isUnit {i : ℕ} (hi : i < p) : IsUnit (i.factorial : Seeds) := by
  let := charFX
  have hp : Nat.Prime p := KoalaBear.is_prime
  have hne : (i.factorial : FX) ≠ 0 := fun h =>
    (not_le_of_gt hi) (hp.dvd_factorial.mp ((CharP.cast_eq_zero_iff FX p _).mp h))
  simpa only [map_natCast] using
    (isUnit_iff_ne_zero.mpr hne).map (MvPolynomial.C : FX →+* Seeds)
private theorem iterate_eval (T : Polynomial Seeds) (hc : ∀ i, CoeffConstant (T.coeff i))
    (j : ℕ) : ((δ : Seeds → Seeds)^[j]) (T.eval ξ) = ((derivative^[j]) T).eval ξ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hz : δ.mapCoeffs ((derivative^[j]) T) = 0 := by
      apply PolynomialModule.ext
      apply Finsupp.ext
      intro i
      rw [Derivation.mapCoeffs_apply, coeff_iterate_derivative, map_nsmul,
        constant_derivative (hc (i + j)), nsmul_zero, PolynomialModule.coeff_zero,
        Finsupp.zero_apply]
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      Derivation.apply_eval_eq, hz, derivative_center]
    simp
private theorem eval_iterate_eq_factorial_mul {R : Type*} [CommRing R]
    (T : Polynomial R) (x : R) (j : ℕ) :
    ((derivative^[j]) T).eval x = (j.factorial : R) * (taylor x T).coeff j := by
  rw [taylor_coeff]
  have hfac := congrFun (factorial_smul_hasseDeriv (R := R) j) T
  rw [LinearMap.smul_apply] at hfac
  rw [← hfac, nsmul_eq_mul, eval_natCast_mul]
private theorem coeff_dvd_of_iterate {g : Seeds} {T : Polynomial Seeds} {m : ℕ}
    (hc : ∀ i, CoeffConstant (T.coeff i)) (hdeg : T.natDegree ≤ m) (hp : m < p)
    (h : ∀ j ≤ m, g ∣ ((δ : Seeds → Seeds)^[j]) (T.eval ξ)) :
    ∀ i, g ∣ T.coeff i := by
  have hTaylor : C g ∣ taylor ξ T := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro j
    by_cases hj : j ≤ m
    · have he : ((δ : Seeds → Seeds)^[j]) (T.eval ξ) =
          (j.factorial : Seeds) * (taylor ξ T).coeff j := by
        rw [iterate_eval T hc, eval_iterate_eq_factorial_mul]
      exact (factorial_isUnit (hj.trans_lt hp)).dvd_mul_left.mp (he ▸ h j hj)
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_taylor]; omega)]
      exact dvd_zero _
  obtain ⟨Q, hQ⟩ := hTaylor
  apply (C_dvd_iff_dvd_coeff _ _).mp
  refine ⟨taylor (-ξ) Q, ?_⟩
  have he := congrArg (taylor (-ξ)) hQ
  simpa only [taylor_taylor, neg_add_cancel, taylor_zero, taylor_mul, taylor_C] using he
private theorem derivative_power_mul (g c : Seeds) (k : ℕ) :
    δ (g ^ (k + 1) * c) =
      g ^ k * (g * δ c + ((k + 1 : ℕ) : Seeds) * δ g * c) := by
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    Nat.add_sub_cancel]
  rw [pow_succ g k]
  ring
private theorem derivative_dvd {g f : Seeds} {k : ℕ} (h : g ^ (k + 1) ∣ f) :
    g ^ k ∣ δ f := by
  obtain ⟨c, rfl⟩ := h
  rw [derivative_power_mul]
  exact dvd_mul_right _ _
private theorem derivative_dvd_stable {g f : Seeds} (hg : g ∣ δ g) {k : ℕ}
    (h : g ^ k ∣ f) : g ^ k ∣ δ f := by
  cases k with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ k =>
    obtain ⟨c, rfl⟩ := h
    obtain ⟨d, hd⟩ := hg
    refine ⟨δ c + ((k + 1 : ℕ) : Seeds) * d * c, ?_⟩
    rw [derivative_power_mul, hd, pow_succ g k]
    ring
private theorem iterate_dvd {g f : Seeds} {k : ℕ} (h : g ^ k ∣ f) (i : ℕ) :
    g ^ (k - i) ∣ ((δ : Seeds → Seeds)^[i]) f := by
  induction i with
  | zero => simpa only [Nat.sub_zero, Function.iterate_zero_apply] using h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    by_cases hi : i < k
    · rw [show k - i = (k - (i + 1)) + 1 by omega] at ih
      exact derivative_dvd ih
    · rw [show k - (i + 1) = 0 by omega, pow_zero]
      exact one_dvd _
private theorem iterate_dvd_stable {g f : Seeds} (hg : g ∣ δ g) {k : ℕ}
    (h : g ^ k ∣ f) (i : ℕ) : g ^ k ∣ ((δ : Seeds → Seeds)^[i]) f := by
  induction i with
  | zero => exact h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact derivative_dvd_stable hg ih
private theorem char_dvd_multiplicity {g f : Seeds} (hg : Prime g) (hg' : ¬g ∣ δ g)
    (hf : f ≠ 0) (hc : CoeffConstant f) : p ∣ multiplicity g f := by
  let k := multiplicity g f
  obtain ⟨c, hfc⟩ := pow_multiplicity_dvd g f
  change f = g ^ k * c at hfc
  have hnd : ¬g ∣ c := by
    intro hd
    have h := (FiniteMultiplicity.of_prime_left hg hf).not_pow_dvd_of_multiplicity_lt
      (Nat.lt_succ_self k)
    apply h
    rw [hfc, pow_succ]
    exact mul_dvd_mul_left _ hd
  change p ∣ k
  rcases k with _ | k
  · exact dvd_zero _
  have hz := constant_derivative hc
  rw [hfc, derivative_power_mul] at hz
  have hsum := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hg.ne_zero)
  have hdvd : g ∣ ((k + 1 : ℕ) : Seeds) * δ g * c := by
    apply (dvd_add_right (dvd_mul_right g (δ c))).mp
    rw [hsum]
    exact dvd_zero _
  have hcast := (hg.dvd_mul.mp ((hg.dvd_mul.mp hdvd).resolve_right hnd)).resolve_right hg'
  let := charSeeds
  apply (CharP.cast_eq_zero_iff Seeds p _).mp
  by_contra hne
  have hnFX : ((k + 1 : ℕ) : FX) ≠ 0 := by
    intro h0
    apply hne
    simpa only [map_natCast, map_zero] using congrArg (MvPolynomial.C : FX →+* Seeds) h0
  exact hg.not_isUnit (isUnit_of_dvd_unit hcast (by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hnFX).map (MvPolynomial.C : FX →+* Seeds)))
private theorem degree_pos_of_prime {g : Seeds} (hg : Prime g) : 0 < g.totalDegree := by
  by_contra! h
  have he : g = MvPolynomial.C (g.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
  have hc : g.coeff 0 ≠ 0 := fun hz => hg.ne_zero (by rw [he, hz, map_zero])
  exact hg.not_isUnit (he.symm ▸ (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C)
private theorem multiplicity_le_degree {g b : Seeds} (hg : Prime g) (hb : b ≠ 0) :
    multiplicity g b ≤ b.totalDegree := by
  have hpow (n : ℕ) : (g ^ n).totalDegree = n * g.totalDegree := by
    induction n with
    | zero => rw [pow_zero, MvPolynomial.totalDegree_one, zero_mul]
    | succ n ih =>
      rw [pow_succ, MvPolynomial.totalDegree_mul_of_isDomain (pow_ne_zero _ hg.ne_zero)
        hg.ne_zero, ih, Nat.succ_mul]
  have h := MvPolynomial.totalDegree_le_of_dvd_of_isDomain (pow_multiplicity_dvd g b) hb
  rw [hpow] at h
  exact (Nat.le_mul_of_pos_right _ (degree_pos_of_prime hg)).trans h
private theorem eval_multiplicity {g b f : Seeds} (hg : Prime g) (hb : b ≠ 0) {d : ℕ}
    (h : g ^ d ∣ b * f) : g ^ (d - multiplicity g b) ∣ f := by
  by_cases hf : f = 0
  · rw [hf]
    exact dvd_zero _
  have hfin := FiniteMultiplicity.of_prime_left hg (mul_ne_zero hb hf)
  have hle := hfin.le_multiplicity_of_pow_dvd h
  rw [multiplicity_mul hg hfin] at hle
  exact pow_dvd_of_le_multiplicity (by omega)
private theorem le_of_char_dvd_of_sub_le {d c loss : ℕ} (hd : p ∣ d) (hc : p ∣ c)
    (hloss : loss < p) (h : d - loss ≤ c) : d ≤ c := by
  by_contra! hlt
  have hgap := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) (Nat.dvd_sub hd hc)
  omega
theorem proof : HighCore82706Tangent_5.c2 := by
  intro a b den T m u hb hden hcden hc hdeg hguard hbdeg hdiag
  apply (C_dvd_iff_dvd_coeff _ _).mpr
  intro i
  rw [coeff_C_mul]
  apply (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hden).mpr
  intro g hg
  let d := multiplicity g den
  let r := multiplicity g b
  have hr : r ≤ u := (multiplicity_le_degree hg hb).trans hbdeg
  have hmp : m < p := (Nat.le_add_right _ _).trans_lt hguard
  have hdiagPow : g ^ d ∣ b * T.eval ξ := by
    rw [hdiag]
    exact (pow_multiplicity_dvd g den).trans (dvd_mul_right den a)
  have hev : g ^ (d - r) ∣ T.eval ξ := eval_multiplicity hg hb hdiagPow
  rw [(FiniteMultiplicity.of_prime_left hg hden).emultiplicity_eq_multiplicity]
  apply pow_dvd_iff_le_emultiplicity.mp
  change g ^ d ∣ b * T.coeff i
  by_cases hg' : g ∣ δ g
  · have hcoeff := coeff_dvd_of_iterate hc hdeg hmp
      (fun j _ => iterate_dvd_stable hg' hev j) i
    exact (pow_dvd_pow g (show d ≤ r + (d - r) by omega)).trans (by
      rw [pow_add]
      exact mul_dvd_mul (pow_multiplicity_dvd g b) hcoeff)
  · have hcoeff := coeff_dvd_of_iterate hc hdeg hmp (g := g ^ (d - (r + m)))
      (fun j hj => (pow_dvd_pow g (show d - (r + m) ≤ d - r - j by omega)).trans
        (iterate_dvd hev j)) i
    by_cases hTi : T.coeff i = 0
    · simp [hTi]
    have hfin := FiniteMultiplicity.of_prime_left hg hTi
    have hle := hfin.le_multiplicity_of_pow_dvd hcoeff
    have hfull := le_of_char_dvd_of_sub_le (char_dvd_multiplicity hg hg' hden hcden)
      (char_dvd_multiplicity hg hg' hTi (hc i)) (show r + m < p by omega) hle
    exact (pow_dvd_of_le_multiplicity hfull).trans (dvd_mul_left _ _)
end
end HighCore82706Tangent_5_2
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2_4
noncomputable section
open K1_14 (FX)
open HighCore82706Tangent_3
open MvPolynomial
open scoped BigOperators
abbrev Exponent := CoxVar →₀ ℕ
abbrev Layer := Degree → Submodule FX Cox
def homogeneous : Layer := weightedHomogeneousSubmodule FX coxWeight
def Stable (L : Layer) : Prop :=
  (∀ d, L d ≤ homogeneous d) ∧
  ∀ d e {p q : Cox}, p ∈ homogeneous e → q ∈ L d → p * q ∈ L (e + d)
def exponentCount (U : Set Exponent) (d : Degree) : ℕ :=
  {m | m ∈ U ∧ Finsupp.weight coxWeight m = d}.ncard
structure Block where
  base : Exponent
  free : Finset CoxVar
def Block.exponents (B : Block) : Set Exponent :=
  {m | ∃ u : Exponent, (∀ i ∉ B.free, u i = 0) ∧ m = B.base + u}
def blockCount (blocks : Finset Block) (d : Degree) : ℕ :=
  ∑ B ∈ blocks, exponentCount B.exponents d
end
end HighCore82706Tangent_3_2_4
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2_4
noncomputable section
open K1_14 (FX)
open HighCore82706Tangent_3
open HighCore82706Tangent_3_2
open MvPolynomial
open HighCore82706Tangent_3 (cox_piece_finite)
private theorem homogeneous_mul {p q : Cox} {d e : Degree}
    (hp : p ∈ homogeneous e) (hq : q ∈ homogeneous d) : p * q ∈ homogeneous (e + d) :=
  IsWeightedHomogeneous.mul hp hq
theorem homogeneous_stable : Stable homogeneous := by
  refine ⟨fun _ => le_rfl, ?_⟩
  intro d e p q hp hq
  exact homogeneous_mul hp hq
private def qmap (Q : Ideal JetRing) : Cox →ₐ[FX] JetRing ⧸ Q :=
  (Ideal.Quotient.mkₐ FX Q).comp dehom
private theorem qmap_mem (Q : Ideal JetRing) {d : Degree} {p : Cox}
    (hp : p ∈ homogeneous d) : qmap Q p ∈ gradedPiece Q d :=
  Submodule.mem_map.mpr ⟨p, hp, rfl⟩
private theorem piece_mul {Q : Ideal JetRing} {d e : Degree} {x y : JetRing ⧸ Q}
    (hx : x ∈ gradedPiece Q e) (hy : y ∈ gradedPiece Q d) :
    x * y ∈ gradedPiece Q (e + d) := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hy
  exact Submodule.mem_map.mpr ⟨p * q, homogeneous_mul hp hq, map_mul (qmap Q) p q⟩
private def pullback (Q : Ideal JetRing) (V : Degree → Submodule FX (JetRing ⧸ Q)) :
    Layer := fun d => homogeneous d ⊓ (V d).comap (qmap Q).toLinearMap
private theorem stable_pullback (Q : Ideal JetRing)
    (V : Degree → Submodule FX (JetRing ⧸ Q))
    (hV : ∀ d e {x y : JetRing ⧸ Q}, x ∈ gradedPiece Q e → y ∈ V d → x * y ∈ V (e + d)) :
    Stable (pullback Q V) := by
  refine ⟨fun _ => inf_le_left, ?_⟩
  intro d e p q hp hq
  refine ⟨homogeneous_mul hp hq.1, ?_⟩
  change qmap Q (p * q) ∈ V (e + d)
  rw [map_mul]
  exact hV d e (qmap_mem Q hp) hq.2
def kernelLayer (Q : Ideal JetRing) : Layer := pullback Q fun _ => ⊥
theorem kernelLayer_stable (Q : Ideal JetRing) : Stable (kernelLayer Q) := by
  apply stable_pullback
  intro d e x y _ hy
  rw [(Submodule.mem_bot FX).mp hy, mul_zero]
  exact Submodule.zero_mem _
theorem kernelLayer_rank (Q : Ideal JetRing) (d : Degree) :
    Module.finrank FX (kernelLayer Q d) + Module.finrank FX (gradedPiece Q d) =
      Module.finrank FX (homogeneous d) := by
  have : Module.Finite FX (homogeneous d) := cox_piece_finite d
  let F := (qmap Q).toLinearMap.domRestrict (homogeneous d)
  have hker : LinearMap.ker F = (kernelLayer Q d).comap (homogeneous d).subtype := by
    ext x
    exact ⟨fun hx => ⟨x.prop, hx⟩, fun hx => hx.2⟩
  have hr := LinearMap.finrank_range_add_finrank_ker (K := FX)
    (V := ↥(homogeneous d)) (V₂ := JetRing ⧸ Q) F
  rw [LinearMap.range_domRestrict, hker,
    (Submodule.comapSubtypeEquivOfLe ((kernelLayer_stable Q).1 d)).finrank_eq, add_comm] at hr
  exact hr
private def sectionImage (Q : Ideal JetRing) (k : Degree) (u : JetRing ⧸ Q) (d : Degree) :
    Submodule FX (JetRing ⧸ Q) :=
  if k ≤ d then (gradedPiece Q (d - k)).map (LinearMap.mulLeft FX u) else ⊥
def cutLayer (Q : Ideal JetRing) (k : Degree) (u : JetRing ⧸ Q) : Layer :=
  pullback Q (sectionImage Q k u)
theorem cutLayer_stable (Q : Ideal JetRing) (k : Degree) (u : JetRing ⧸ Q) :
    Stable (cutLayer Q k u) := by
  apply stable_pullback
  intro d e x y hx hy
  by_cases hd : k ≤ d
  · have he : k ≤ e + d := hd.trans le_add_self
    rw [sectionImage, ite_eq_left hd] at hy
    rw [sectionImage, ite_eq_left he, add_tsub_assoc_of_le hd]
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨x * z, piece_mul hx hz, by
      simp only [LinearMap.mulLeft_apply]
      ac_rfl⟩
  · rw [sectionImage, ite_eq_right hd] at hy
    rw [(Submodule.mem_bot FX).mp hy, mul_zero]
    exact Submodule.zero_mem _
theorem cutLayer_le {Q R : Ideal JetRing} (hQR : Q ≤ R) (k : Degree) {u : JetRing}
    (hu : u ∈ R) (d : Degree) :
    cutLayer Q k (Ideal.Quotient.mk Q u) d ≤ kernelLayer R d := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  change qmap R p = 0
  have hcomp : Ideal.Quotient.factor hQR (qmap Q p) = qmap R p :=
    Ideal.Quotient.factor_mk hQR (dehom p)
  rw [← hcomp]
  have hmem : qmap Q p ∈ sectionImage Q k (Ideal.Quotient.mk Q u) d := hp.2
  by_cases hd : k ≤ d
  · rw [sectionImage, ite_eq_left hd] at hmem
    obtain ⟨z, _, hz⟩ := Submodule.mem_map.mp hmem
    rw [← hz, LinearMap.mulLeft_apply, map_mul, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hu, zero_mul]
  · rw [sectionImage, ite_eq_right hd] at hmem
    rw [(Submodule.mem_bot FX).mp hmem, map_zero]
private theorem cut_rank_aux (Q : Ideal JetRing) (k : Degree) (u : JetRing ⧸ Q)
    (d : Degree) (hV : sectionImage Q k u d ≤ gradedPiece Q d) :
    Module.finrank FX (kernelLayer Q d) + Module.finrank FX (sectionImage Q k u d) =
      Module.finrank FX (cutLayer Q k u d) := by
  have : Module.Finite FX (homogeneous d) := cox_piece_finite d
  have : Module.Finite FX (cutLayer Q k u d) :=
    Submodule.finiteDimensional_of_le ((cutLayer_stable Q k u).1 d)
  let F := (qmap Q).toLinearMap.domRestrict (cutLayer Q k u d)
  have hle : kernelLayer Q d ≤ cutLayer Q k u d := by
    intro p hp
    have hz : qmap Q p = 0 := hp.2
    exact ⟨hp.1, show qmap Q p ∈ sectionImage Q k u d by rw [hz]; exact Submodule.zero_mem _⟩
  have hker : LinearMap.ker F = (kernelLayer Q d).comap (cutLayer Q k u d).subtype := by
    ext x
    exact ⟨fun hx => ⟨x.prop.1, hx⟩, fun hx => hx.2⟩
  have hrange : LinearMap.range F = sectionImage Q k u d := by
    rw [LinearMap.range_domRestrict]
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
      exact hp.2
    · intro x hx
      obtain ⟨p, hp, he⟩ := Submodule.mem_map.mp (hV hx)
      refine Submodule.mem_map.mpr ⟨p, ⟨hp, ?_⟩, he⟩
      change qmap Q p ∈ sectionImage Q k u d
      change qmap Q p = x at he
      rwa [he]
  have hr := LinearMap.finrank_range_add_finrank_ker (K := FX)
    (V := ↥(cutLayer Q k u d)) (V₂ := JetRing ⧸ Q) F
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq, add_comm] at hr
  exact hr
theorem cutLayer_rank {Q : Ideal JetRing} {a b c : ℕ}
    (S : RelativeSection Q (nefDegree a b c))
    (hreg : IsLeftRegular (Ideal.Quotient.mk Q S.affine))
    {h t s : ℕ} (hh : 2 * S.order ≤ h) :
    Module.finrank FX (kernelLayer Q (nefDegree (h+a) (t+b) (s+c))) + hilbert Q h t s =
      Module.finrank FX (cutLayer Q (nefDegree a b c) (Ideal.Quotient.mk Q S.affine)
        (nefDegree (h+a) (t+b) (s+c))) := by
  let k := nefDegree a b c
  let e := nefDegree h t s
  let u := Ideal.Quotient.mk Q S.affine
  have he : e + k = nefDegree (h+a) (t+b) (s+c) := by
    simp only [e, k, nefDegree, Prod.mk_add_mk]
    congr 1
    omega
  have hI : sectionImage Q k u (e + k) =
      (gradedPiece Q e).map (LinearMap.mulLeft FX u) := by
    have hk : k ≤ e + k := le_add_self
    rw [sectionImage, ite_eq_left hk, add_tsub_cancel_right]
  have hV : sectionImage Q k u (e + k) ≤ gradedPiece Q (e + k) := by
    rw [hI]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact relativeSection_mul_gradedPiece S hh hy
  have hr := cut_rank_aux Q k u (e + k) hV
  rw [hI, ← (Submodule.equivMapOfInjective (LinearMap.mulLeft FX u) hreg _).finrank_eq, he] at hr
  exact hr
end
end HighCore82706Tangent_3_2_4
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2_4
noncomputable section
open HighCore82706Tangent_3
open scoped BigOperators
private theorem finite_generators (U : Set Exponent) (hU : IsUpperSet U) :
    ∃ F : Finset Exponent, ∀ m, m ∈ U ↔ ∃ b ∈ F, b ≤ m := by
  classical
  have hf : {b | Minimal (· ∈ U) b}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain fun a ha b hb hab hle =>
      hab (le_antisymm hle (hb.2 ha.1 hle))
  refine ⟨hf.toFinset, fun m => ?_⟩
  constructor
  · intro hm
    obtain ⟨b, hbm, hb⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ U) m hm
    exact ⟨b, hf.mem_toFinset.mpr hb, hbm⟩
  · rintro ⟨b, hb, hbm⟩
    exact hU hbm (hf.mem_toFinset.mp hb).1
private theorem mem_inf_iff {U : Set Exponent} (hU : IsUpperSet U)
    (F : Finset Exponent) (hF : ∀ m, m ∈ U ↔ ∃ b ∈ F, b ≤ m)
    {M : Exponent} (hM : ∀ b ∈ F, b ≤ M) (m : Exponent) :
    m ⊓ M ∈ U ↔ m ∈ U := by
  refine ⟨hU inf_le_left, fun hm => ?_⟩
  obtain ⟨b, hb, hbm⟩ := (hF m).mp hm
  exact (hF _).mpr ⟨b, hb, le_inf hbm (hM b hb)⟩
private def blockAt (M b : Exponent) : Block :=
  ⟨b, Finset.univ.filter fun i : CoxVar => b i = M i⟩
private theorem mem_blockAt_iff {M b m : Exponent} (hb : b ≤ M) :
    m ∈ (blockAt M b).exponents ↔ m ⊓ M = b := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    ext i
    change min (b i + u i) (M i) = b i
    by_cases he : b i = M i
    · rw [he, min_eq_right (by omega)]
    · have hz := hu i (by simp [blockAt, he])
      rw [hz, add_zero, min_eq_left (hb i)]
  · intro he
    have hm : b ≤ m := he ▸ inf_le_left
    refine ⟨m-b, ?_, (add_tsub_cancel_of_le hm).symm⟩
    intro i hi
    have hne : b i ≠ M i := by simpa [blockAt] using hi
    have h := congrArg (fun v : Exponent => v i) he
    change min (m i) (M i) = b i at h
    change m i - b i = 0
    omega
theorem finite_weight (d : Degree) :
    {m : Exponent | Finsupp.weight coxWeight m = d}.Finite := by
  let bound : Exponent := Finsupp.equivFunOnFinite.symm fun _ => d.1 + d.2.1 + d.2.2
  refine (Set.finite_Iic bound).subset (fun m hm => ?_)
  have he := (weight_coordinates m).symm.trans hm
  have hh := congrArg Prod.fst he
  have ht := congrArg (fun d : Degree => d.2.1) he
  have hs := congrArg (fun d : Degree => d.2.2) he
  change m h₀ + m h₁ + 2 * m v₁ = d.1 at hh
  change m v₀ + m v₁ = d.2.1 at ht
  change m (tᵢ 0) + m (tᵢ 1) + m (tᵢ 2) = d.2.2 at hs
  intro i
  change m i ≤ d.1 + d.2.1 + d.2.2
  rcases i with i | (i | i) <;> fin_cases i <;>
    dsimp [h₀, h₁, v₀, v₁, tᵢ] at * <;> omega
theorem orthant_partition (U V : Set Exponent) (hU : IsUpperSet U) (hV : IsUpperSet V) :
    ∃ blocks : Finset Block, ∀ d, exponentCount (V \ U) d = blockCount blocks d := by
  classical
  obtain ⟨FU, hFU⟩ := finite_generators U hU
  obtain ⟨FV, hFV⟩ := finite_generators V hV
  let M := (FU ∪ FV).sup id
  have same (m : Exponent) : m ⊓ M ∈ V \ U ↔ m ∈ V \ U := by
    have hu := mem_inf_iff hU FU hFU (M := M)
      (fun b hb => Finset.le_sup (f := id) (Finset.mem_union_left FV hb)) m
    have hv := mem_inf_iff hV FV hFV (M := M)
      (fun b hb => Finset.le_sup (f := id) (Finset.mem_union_right FU hb)) m
    change m ⊓ M ∈ V ∧ m ⊓ M ∉ U ↔ m ∈ V ∧ m ∉ U
    rw [hu, hv]
  let bases := (Finset.Iic M).filter fun b => b ∈ V \ U
  have hbase (b : Exponent) : b ∈ bases ↔ b ≤ M ∧ b ∈ V \ U := by simp [bases]
  let enc : Exponent ↪ Block := ⟨blockAt M, fun _ _ h => congrArg Block.base h⟩
  refine ⟨bases.map enc, fun d => ?_⟩
  let fiber (b : Exponent) := {m : Exponent | m ∈ (blockAt M b).exponents ∧
    Finsupp.weight coxWeight m = d}
  have hEq : {m : Exponent | m ∈ V \ U ∧ Finsupp.weight coxWeight m = d} =
      ⋃ b ∈ (bases : Set Exponent), fiber b := by
    ext m
    rw [Set.mem_iUnion₂]
    constructor
    · rintro ⟨hm, hd⟩
      have hb : m ⊓ M ≤ M := inf_le_right
      exact ⟨m ⊓ M, (hbase _).mpr ⟨hb, (same m).mpr hm⟩, (mem_blockAt_iff hb).mpr rfl, hd⟩
    · rintro ⟨b, hb, hm, hd⟩
      obtain ⟨hle, hmem⟩ := (hbase b).mp hb
      exact ⟨(same m).mp ((mem_blockAt_iff hle).mp hm ▸ hmem), hd⟩
  have hdisj : (bases : Set Exponent).PairwiseDisjoint fiber := by
    intro b hb z hz hne
    refine Set.disjoint_left.mpr fun m hm hm' => hne ?_
    have h₁ := (mem_blockAt_iff ((hbase b).mp hb).1).mp hm.1
    have h₂ := (mem_blockAt_iff ((hbase z).mp hz).1).mp hm'.1
    exact h₁.symm.trans h₂
  have hf (b : Exponent) (_ : b ∈ (bases : Set Exponent)) : (fiber b).Finite :=
    (finite_weight d).subset fun _ hm => hm.2
  change {m : Exponent | m ∈ V \ U ∧ Finsupp.weight coxWeight m = d}.ncard =
    ∑ B ∈ bases.map enc, exponentCount B.exponents d
  rw [hEq, bases.finite_toSet.ncard_biUnion hf hdisj,
    finsum_mem_eq_finite_toFinset_sum _ bases.finite_toSet,
    Finset.finite_toSet_toFinset, Finset.sum_map]
  rfl
end
end HighCore82706Tangent_3_2_4
end
section
set_option autoImplicit false
namespace HighCore82706Tangent_3_2_4
open K1_14 (FX)
open HighCore82706Tangent_3 HighCore82706Tangent_3_2
open MvPolynomial
def c1 : Prop :=
  ∀ A B : Layer, Stable A → Stable B → (∀ d, A d ≤ B d) →
    ∃ U V : Set Exponent, IsUpperSet U ∧ IsUpperSet V ∧ U ⊆ V ∧
      ∀ d, Module.finrank FX (A d) + exponentCount (V \ U) d =
        Module.finrank FX (B d)
def c2 : Prop :=
  ∀ blocks : Finset Block, ∃ p : HilbertPoly, NonnegativeTop p ∧
    EventuallyInChamber fun h t s =>
      (blockCount blocks (nefDegree h t s) : ℚ) = evalHilbert p h t s
private theorem layer_profile (h1 : c1) (h2 : c2) (A B : Layer)
    (hA : Stable A) (hB : Stable B) (hab : ∀ d, A d ≤ B d) :
    ∃ p : HilbertPoly, NonnegativeTop p ∧
      EventuallyInChamber fun h t s =>
        (Module.finrank FX (A (nefDegree h t s)) : ℚ) + evalHilbert p h t s =
          (Module.finrank FX (B (nefDegree h t s)) : ℚ) := by
  obtain ⟨U, V, hU, hV, _, hrank⟩ := h1 A B hA hB hab
  obtain ⟨blocks, hblocks⟩ := orthant_partition U V hU hV
  obtain ⟨p, hpos, N, hN⟩ := h2 blocks
  refine ⟨p, hpos, N, fun h t s hh ht hs => ?_⟩
  change (Module.finrank FX (A (nefDegree h t s)) : ℚ) + evalHilbert p h t s =
    (Module.finrank FX (B (nefDegree h t s)) : ℚ)
  rw [← hN h t s hh ht hs, ← hblocks]
  exact_mod_cast hrank (nefDegree h t s)
private theorem eq_of_eventual {p q : HilbertPoly}
    (h : EventuallyInChamber fun h t s => evalHilbert p h t s = evalHilbert q h t s) :
    p = q := by
  obtain ⟨N, hN⟩ := h
  let S : Fin 3 → Set ℚ := fun _ => Set.range (fun n : ℕ => ((N+n : ℕ) : ℚ))
  have hS (i : Fin 3) : (S i).Infinite := by
    apply Set.infinite_range_of_injective
    intro a b hab
    change ((N+a : ℕ) : ℚ) = ((N+b : ℕ) : ℚ) at hab
    have hc : N+a = N+b := by exact_mod_cast hab
    omega
  apply MvPolynomial.funext_set S hS
  intro x hx
  have htail (i : Fin 3) : ∃ n : ℕ, N ≤ n ∧ (n : ℚ) = x i := by
    obtain ⟨n, hn⟩ := hx i (Set.mem_univ i)
    exact ⟨N+n, Nat.le_add_right N n, hn⟩
  obtain ⟨a, ha, hea⟩ := htail 0
  obtain ⟨b, hb, heb⟩ := htail 1
  obtain ⟨c, hc, hec⟩ := htail 2
  have he : x = ![(a : ℚ), (b : ℚ), (c : ℚ)] := by
    funext i
    fin_cases i
    · exact hea.symm
    · exact heb.symm
    · exact hec.symm
  rw [he]
  exact hN a b c ha hb hc
private theorem eval_difference (p q : HilbertPoly) {a b c h t s : ℕ}
    (ha : a ≤ h) (hb : b ≤ t) (hc : c ≤ s) :
    evalHilbert (difference p a b c - q) h t s =
      evalHilbert p h t s - evalHilbert p (h-a) (t-b) (s-c) - evalHilbert q h t s := by
  let x : Fin 3 → ℚ := ![(h : ℚ), (t : ℚ), (s : ℚ)]
  have hx : (fun i : Fin 3 => aeval x (MvPolynomial.X i - MvPolynomial.C (![a, b, c] i : ℚ))) =
      ![((h-a : ℕ) : ℚ), ((t-b : ℕ) : ℚ), ((s-c : ℕ) : ℚ)] := by
    funext i
    fin_cases i <;> simp [x, Nat.cast_sub ha, Nat.cast_sub hb, Nat.cast_sub hc]
  change aeval x (p - bind₁ (fun i : Fin 3 => MvPolynomial.X i - MvPolynomial.C (![a, b, c] i : ℚ)) p - q) =
    aeval x p - aeval ![((h-a : ℕ) : ℚ), ((t-b : ℕ) : ℚ), ((s-c : ℕ) : ℚ)] p - aeval x q
  rw [map_sub, map_sub, aeval_bind₁, hx]
theorem of_children (h1 : c1) (h2 : c2) : HighCore82706Tangent_3_2.c4 := by
  constructor
  · intro Q
    obtain ⟨p, hpos, N, hN⟩ := layer_profile h1 h2 (kernelLayer Q) homogeneous
      (kernelLayer_stable Q) homogeneous_stable (kernelLayer_stable Q).1
    refine ⟨p, ⟨N, fun h t s hh ht hs => ?_⟩, hpos⟩
    have hr := congrArg (fun n : ℕ => (n : ℚ)) (kernelLayer_rank Q (nefDegree h t s))
    simp only [Nat.cast_add] at hr
    change (_ : ℚ) + (hilbert Q h t s : ℚ) = _ at hr
    linarith only [hr, hN h t s hh ht hs]
  · intro Q R a b c S hQR hmem hreg p q hp hq
    let A := cutLayer Q (nefDegree a b c) (Ideal.Quotient.mk Q S.affine)
    obtain ⟨r, hr, Nr, hNr⟩ := layer_profile h1 h2 A (kernelLayer R)
      (cutLayer_stable _ _ _) (kernelLayer_stable R) (cutLayer_le hQR _ hmem)
    suffices he : difference p a b c - q = r by rwa [he]
    apply eq_of_eventual
    obtain ⟨Np, hNp⟩ := hp
    obtain ⟨Nq, hNq⟩ := hq
    refine ⟨Np + Nq + Nr + 2*S.order + a + b + c, fun h t s hh ht hs => ?_⟩
    have ha : a ≤ h := by omega
    have hb : b ≤ t := by omega
    have hc : c ≤ s := by omega
    have hp0 := hNp h t s (by omega) (by omega) (by omega)
    have hp1 := hNp (h-a) (t-b) (s-c) (by omega) (by omega) (by omega)
    have hq0 := hNq h t s (by omega) (by omega) (by omega)
    have hR := hNr h t s (by omega) (by omega) (by omega)
    have hcut := cutLayer_rank S hreg (h := h-a) (t := t-b) (s := s-c) (by omega)
    rw [Nat.sub_add_cancel ha, Nat.sub_add_cancel hb, Nat.sub_add_cancel hc] at hcut
    let d := nefDegree h t s
    have hcut' : (Module.finrank FX (kernelLayer Q d) : ℚ) +
        (hilbert Q (h-a) (t-b) (s-c) : ℚ) = (Module.finrank FX (A d) : ℚ) := by
      exact_mod_cast hcut
    have hk (I : Ideal JetRing) : (Module.finrank FX (kernelLayer I d) : ℚ) +
        (hilbert I h t s : ℚ) = (Module.finrank FX (homogeneous d) : ℚ) := by
      exact_mod_cast kernelLayer_rank I d
    change evalHilbert (difference p a b c - q) h t s = evalHilbert r h t s
    rw [eval_difference p q ha hb hc]
    change (Module.finrank FX (A d) : ℚ) + evalHilbert r h t s =
      (Module.finrank FX (kernelLayer R d) : ℚ) at hR
    linarith only [hR, hcut', hk Q, hk R, hp0, hp1, hq0]
end HighCore82706Tangent_3_2_4
end
