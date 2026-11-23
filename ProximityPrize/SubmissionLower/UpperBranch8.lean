import Mathlib.Algebra.Order.Sub.Prod
import ProximityPrize.SubmissionLower.LowerBase
import ProximityPrize.SubmissionLower.UpperBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_8
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P1 (K I node agreement)
open private occupancy from ProximityPrize.SubmissionLower.Fast055
structure FixedWord (w : I → K) (T : Finset K) (s : K → K[X]) (d : ℕ) : Prop where
  distinct:Set.InjOn s (T:Set K)
  degree : ∀ γ ∈ T,(s γ).natDegree≤d
  hits : ∀ γ ∈ T, ∃ B:Finset I,agreement≤B.card ∧ ∀ i ∈ B,(s γ).eval (node i)=w i
theorem FixedWord.mono {w T s d} (h : FixedWord w T s d) {U : Finset K} (hU : U ⊆ T) :
    FixedWord w U s d :=
  ⟨h.distinct.mono hU,fun γ hγ => h.degree γ (hU hγ),fun γ hγ => h.hits γ (hU hγ)⟩
open private incidence_arithmetic from ProximityPrize.SubmissionLower.PortHighBase
theorem section_capacity {w T s d} (h : FixedWord w T s d) (hd : d < agreement) (cap : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ T, (s γ).eval (node i) ≠ w i) →
      (T.filter fun γ => (s γ).eval (node i)=w i).card≤ cap) :
    (agreement - d)*T.card≤P1.t*cap+(agreement - d):=by
  classical
  by_cases hm:T.card≤1
  · have hb := Nat.mul_le_mul_left (agreement - d) hm
    simp only [Nat.mul_one] at hb
    omega
  let hits (γ:K):Finset I:=univ.filter fun i => (s γ).eval (node i)=w i
  let common:Finset I:=univ.filter fun i => ∀ γ ∈ T,(s γ).eval (node i)=w i
  let nodes:Finset I:=univ \ common
  have common_le (γ : K) (hγ : γ ∈ T) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K) (hγ : γ ∈ T) : agreement ≤ (hits γ).card := by
    obtain ⟨B,hB,hval⟩:=h.hits γ hγ
    exact hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _,hval i hi⟩)
  have pair_count (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (hits a ∩ hits b).card≤d:=by
    let P:=s a - s b
    have hp:P≠0:=sub_ne_zero.mpr fun eq => hab (h.distinct ha hb eq)
    refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
      P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (h.degree a ha) (h.degree b hb)))
    intro i hi
    change ((s a) - (s b)).eval (node i)=0
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a,ha,b,hb,hab⟩:=one_lt_card.mp (by omega:1 < T.card)
  have hcommon : common.card ≤ d :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x:=agreement - common.card
  let t:=d - common.card
  have ht:t=x - (agreement - d):=by dsimp [t,x]; omega
  have hx:agreement - d≤x:=by dsimp [x]; omega
  have hnodes : nodes.card = x + P1.t := by
    rw [card_sdiff_of_subset (subset_univ common),card_univ,IRSProfile.card_index]
    change 262144 - common.card=(179944 - common.card)+82200
    have hbound:common.card≤179944:=hcommon.trans hd.le
    omega
  have exists_trim (γ : K) : ∃ B : Finset I, γ ∈ T → B ⊆ hits γ \ common ∧ B.card = x := by
    by_cases hγ:γ ∈ T
    · have hc := hit_count γ hγ
      have hsize : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨B,hB,hcard⟩:=exists_subset_card_eq hsize
      exact ⟨B,fun _ => ⟨hB,hcard⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose B hB using exists_trim
  have into_nodes (γ : K) (hγ : γ ∈ T) : B γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (B a ∩ B b).card≤t:=by
    have cover : (B a ∩ B b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with hi | hi
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hB a ha).1 (mem_inter.mp hi).1)).1,
          (mem_sdiff.mp ((hB b hb).1 (mem_inter.mp hi).2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hi,common_le b hb hi⟩
    have disj : Disjoint (B a ∩ B b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc:=(card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : I) (hi : i ∈ nodes) : (T.filter fun γ => i ∈ B γ).card ≤ cap := by
    have proper : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _,hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ,hi⟩:=mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ,(mem_filter.mp (mem_sdiff.mp ((hB γ hγ).1 hi)).1).2⟩
  obtain ⟨second, first⟩ := occupancy T nodes B x t cap
    (fun γ hγ => ⟨into_nodes γ hγ,(hB γ hγ).2⟩) overlap occ_le
  rw [hnodes,ht] at second
  rw [hnodes] at first
  exact incidence_arithmetic P1.t _ _ _ _ (by omega) (by omega) hx (by decide) second first
end
end P1_7_8
end
section
set_option autoImplicit false
namespace P1_7_8
noncomputable section
open Polynomial Finset
open P1 (K I Words AnchorModel AnchoredFamily p node agreement blockLength)
open P1_7 (Reduced AdjacentChart regularRoot degreeAt quotientOrder singularDegree)
open K1_14 (L FX Seeds Equation SeedBound liftPoly atMark seedEmbedding)
open K1_14_4 (seedDegree)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx flatten cleared separant markEval)
open scoped BigOperators
structure Input where
  words:Words
  deleted:Finset I
  model:AnchorModel words deleted
  labels:Finset K
  family:AnchoredFamily model labels
  shift_out:model.shift ∉ labels
  block:L[X]
  chart:AdjacentChart model family block
  marks:Finset K
  marks_sub:marks ⊆ labels
  f:Equation
  regular : ∀ γ ∈ marks,regularRoot f (model.label γ) (family.scalar γ)
  reduced:Reduced f
  sheets:3≤f.natDegree
  seed_pos:0 < seedDegree f
  v:ℕ
  seed_bound:SeedBound f v
  lo:ℕ
  hi:ℕ
  lower:lo≤ model.overhead.toNat
  upper:model.overhead.toNat≤hi
  positive:0 < model.overhead.toNat
  quotient_pos:0 < quotientOrder model.overhead.toNat
  agreement_gap:degreeAt hi < agreement
  factorial_guard:degreeAt hi+1 < p
  separant_guard:singularDegree f.natDegree v < p
  flat_guard:f.natDegree*degreeAt hi+v < p
abbrev Input.w (J:Input):ℕ:=J.model.overhead.toNat
abbrev Input.ell (J:Input):ℕ:=quotientOrder J.w
abbrev Input.e (J:Input):ℕ:=J.f.natDegree
def Input.secondBlock (J:Input):L[X]:=J.block.map (frobenius L p)
def Input.blockProduct (J:Input):L[X]:=J.block*J.secondBlock
abbrev SeedConstants:=MvPolynomial (Fin 2) L
def residueData (_J : Input) (i : Fin 2) (g : K[X]) : SeedConstants[X] :=
  ((liftPoly g).map (if i=0 then RingHom.id L else frobenius L p)).map MvPolynomial.C
def blockAt (J : Input) (i : Fin 2) : L[X] :=
  if i=0 then J.block else J.secondBlock
def residueDenominator (J : Input) (i : Fin 2) : SeedConstants[X] :=
  residueData J i (J.model.factor * J.model.A₀) +
    C (MvPolynomial.X i)*residueData J i (J.model.factor*J.model.A₁)
def evalSeedConstants (z : K) : SeedConstants →+* L :=
  MvPolynomial.eval ![algebraMap K L z,(algebraMap K L z)^p]
structure ResidueLift (J : Input) where
  denominator:SeedConstants
  numerator:SeedConstants[X]
  denominator_ne:denominator≠0
  denominator_degree:denominator.totalDegree≤2*J.w
  numerator_degree : ∀ j,(numerator.coeff j).totalDegree≤2*J.w
  numerator_width:numerator.natDegree < 2*J.w
  congruences : ∀ i : Fin 2, (blockAt J i).map MvPolynomial.C ∣
    residueDenominator J i * numerator +
      C (MvPolynomial.X i*denominator)*residueData J i J.model.Q
  unit_at_marks : ∀ γ ∈ J.labels,evalSeedConstants (J.model.label γ) denominator≠0
def constantAbscissa : L →+* FX :=
  (algebraMap L[X] FX).comp Polynomial.C
def liftSeeds:SeedConstants →+* Seeds:=MvPolynomial.map constantAbscissa
def seedBiform : SeedConstants →+* Biform :=
  (MvPolynomial.rename (R:=FX) (some:Fin 2→Option (Fin 2))).toRingHom.comp liftSeeds
def center:FX:=algebraMap L[X] FX Polynomial.X
def liftTaylor (P : SeedConstants[X]) (i : ℕ) : Biform :=
  (Polynomial.taylor (MvPolynomial.C center) (P.map seedBiform)).coeff i
def inverseBlockCoeff (J : Input) (i : ℕ) : FX :=
  (i.factorial : FX)⁻¹ *
    (Dx^[i]) ((algebraMap L[X] FX J.blockProduct)⁻¹)
def ordinateTaylorNum (f : Equation) (r : ℕ) : ℕ → Biform
  | 0 => separant (flatten f) ^ (2*r-1)*MvPolynomial.X none
  | i + 1 => MvPolynomial.C (((i+1).factorial : FX)⁻¹) *
      (separant (flatten f) ^ ((2*r-1)-(2*i+1))*cleared (flatten f) i)
def quotientNumerator (J : Input) (B : ResidueLift J) (r : ℕ) : Biform :=
  ∑ i ∈ range (r+1), MvPolynomial.C (inverseBlockCoeff J (r-i)) *
    (seedBiform B.denominator * ordinateTaylorNum J.f r i -
      separant (flatten J.f) ^ (2*r-1)*liftTaylor B.numerator i)
def quotientDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : Biform :=
  seedBiform B.denominator*separant (flatten J.f) ^ (2*r-1)
def cutoff (J : Input) (B : ResidueLift J) : Equation :=
  MvPolynomial.optionEquivLeft FX (Fin 2) (quotientNumerator J B (J.ell+1))
abbrev SeedField:=FractionRing Seeds
def generic (q:Equation):SeedField[X]:=q.map (algebraMap Seeds SeedField)
def rootOn (J : Input) (q : Equation) (γ : K) : Prop :=
  atMark q (J.model.label γ) (J.family.scalar γ)=0
structure Factors (J : Input) (B : ResidueLift J) where
  proper:Equation
  count:ℕ
  flat:Fin count→Equation
  product:J.f=proper * ∏ j,flat j
  cutoff_at_marks : ∀ γ ∈ J.marks,rootOn J (cutoff J B) γ
  proper_coprime:IsCoprime (generic proper) (generic (cutoff J B))
  flat_reduced : ∀ j,Reduced (flat j)
  flat_irred : ∀ j,Irreducible (generic (flat j))
  flat_cutoff : ∀ j,generic (flat j) ∣ generic (cutoff J B)
  sheets:count≤J.e
  degree_each : ∀ j,(flat j).natDegree≤J.e
  seed_sum : ∑ j,seedDegree (flat j)≤J.v
structure ProperCurve (J : Input) (B : ResidueLift J) (D : Factors J B) where
  prime:Ideal Equation
  isPrime:prime.IsPrime
  onProper:D.proper ∈ prime
  onCutoff:cutoff J B ∈ prime
  marks:Finset K
  sub:marks ⊆ J.marks
  liesOn : ∀ γ ∈ marks, prime ≤ RingHom.ker
    (eval₂RingHom (K1_14.graphEval (J.model.label γ)) (K1_14.atX (J.family.scalar γ)))
  persistent:Finset I
  hits : ∀ γ ∈ marks, ∀ x ∈ persistent,(J.family.scalar γ).eval (node x)=J.model.word x
  fiber:ℕ
  tangent:ℕ
  seed:ℕ
  positive_seed:0 < seed
  sections : ∀ x ∉ persistent,
    let r:=J.ell - persistent.card
    (marks.filter fun γ => (J.family.scalar γ).eval (node x) = J.model.word x).card ≤
      (1+(J.e-3)*r)*fiber+r*tangent+(r*J.v+2*J.w)*seed
def cutVelocity (J:Input):ℕ:=quotientOrder J.lo+1
def cutOrdinate (J:Input):ℕ:=1+cutVelocity J*(J.e-1)
def cutSeed (J:Input):ℕ:=cutVelocity J*J.v+2*J.hi
structure ProperCover (J : Input) (B : ResidueLift J) (D : Factors J B) where
  count:ℕ
  curves:Fin count→ProperCurve J B D
  covers : ∀ γ ∈ J.marks,rootOn J D.proper γ → ∃ j,γ ∈ (curves j).marks
  fiber : ∑ j,(curves j).fiber≤J.v*cutSeed J+J.v^2*cutVelocity J
  tangent : ∑ j,(curves j).tangent≤2*J.e*J.v*cutSeed J+J.v^2*cutOrdinate J
  seed : ∑ j, (curves j).seed ≤
    J.e*cutSeed J+J.v*((2*J.e-2)*cutVelocity J+cutOrdinate J)
abbrev SeedClosure:=AlgebraicClosure SeedField
def intoSeedClosure : Seeds →+* SeedClosure :=
  (algebraMap SeedField SeedClosure).comp (algebraMap Seeds SeedField)
def genericPoint (y : SeedClosure) : Biform →+* SeedClosure :=
  (eval₂RingHom intoSeedClosure y).comp (MvPolynomial.optionEquivLeft FX (Fin 2)).toRingHom
def liftConstantSeeds : SeedConstants →+* SeedClosure :=
  intoSeedClosure.comp liftSeeds
def reconstructed (J : Input) (B : ResidueLift J) (y : SeedClosure) : SeedClosure[X] :=
  let ζ:=intoSeedClosure (MvPolynomial.C center)
  let ev:=genericPoint y
  C ((liftConstantSeeds B.denominator)⁻¹) * B.numerator.map liftConstantSeeds +
    J.blockProduct.map (liftConstantSeeds.comp MvPolynomial.C) *
      ∑ j ∈ range (J.ell+1),
        C (ev (quotientNumerator J B j) / ev (quotientDenominator J B j)) *
          (Polynomial.X - C ζ)^j
def genericRoots (q : Equation) : Finset SeedClosure := by
  classical
  exact (q.map intoSeedClosure).roots.toFinset
structure DifferentialProduct (J : Input) (B : ResidueLift J) (q : Equation) where
  numerator:Polynomial (Polynomial Seeds)
  denominator:Seeds
  denominator_ne:denominator≠0
  leading:numerator.coeff q.natDegree=C denominator
  abscissa_width : ∀ j,(numerator.coeff j).natDegree≤q.natDegree*degreeAt J.hi
  numerator_constant : ∀ i j m,Dx (((numerator.coeff i).coeff j).coeff m)=0
  denominator_constant : ∀ m,Dx (denominator.coeff m)=0
  identity :
    numerator.map (Polynomial.mapRingHom intoSeedClosure) =
      C (C (intoSeedClosure denominator)) *
        ∏ y ∈ genericRoots q,
          (Polynomial.X - C (reconstructed J B y))
def FlatSections (J : Input) (q : Equation) : Prop :=
  ∀ x : I, (∃ γ ∈ J.marks, rootOn J q γ ∧
      (J.family.scalar γ).eval (node x)≠J.model.word x) →
    ∃ g : Seeds, g ≠ 0 ∧ g.totalDegree ≤ seedDegree q ∧
      ∀ γ ∈ J.marks, rootOn J q γ →
        (J.family.scalar γ).eval (node x) = J.model.word x →
          K1_14.graphEval (J.model.label γ) g=0
end
end P1_7_8
end
section
set_option autoImplicit false
namespace P1_7_8
noncomputable section
open P1 (agreement blockLength)
open P1_7 (degreeAt quotientOrder gap scale muNum lambdaNum ceilRatio properFee)
theorem ratio_le_ceil {n d k : ℕ} (hd : 0 < d) (hk : d*k ≤ n) :
    k≤ ceilRatio n d:=by
  apply (Nat.le_div_iff_mul_le hd).mpr
  exact (Nat.mul_comm d k ▸ hk).trans (Nat.le_add_right _ _)
theorem mu_cross {A n d s : ℕ} (hA : A ≤ n) (hd : d ≤ A) (hs : s ≤ d) :
    (A-d)*(n-s)≤(A-s)*(n-d):=by
  have hsA:=hs.trans hd
  have hdn:=hd.trans hA
  have hsn:=hsA.trans hA
  have h : 0 ≤ ((d : ℤ)-s)*((n : ℤ)-A) :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hs)) (sub_nonneg.mpr (by exact_mod_cast hA))
  apply Int.ofNat_le.mp
  push_cast [Nat.cast_sub hd,Nat.cast_sub hsn,Nat.cast_sub hsA,Nat.cast_sub hdn]
  nlinarith only [h]
theorem lambda_cross {A n l s : ℕ} (hA : A ≤ n) (hl : l ≤ A) (hs : s ≤ A) :
    A*(n-s)*(l-s)≤n*(A-s)*l:=by
  by_cases ht:s≤l
  · have hsn := hs.trans hA
    have h₁ : 0 ≤ (s : ℤ)*n*((A : ℤ)-l) := by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hl))
    have h₂ : 0 ≤ (s : ℤ)*A*((l : ℤ)-s) := by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast ht))
    apply Int.ofNat_le.mp
    push_cast [Nat.cast_sub hsn,Nat.cast_sub ht,Nat.cast_sub hs]
    nlinarith only [h₁,h₂]
  · simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge ht))]
def nodeVelocity (J:Input):ℕ:=lambdaNum J.hi*quotientOrder J.lo
def nodeReducedOrdinate (J:Input):ℕ:=muNum J.hi+(J.e-3)*nodeVelocity J
def nodeSeed (J:Input):ℕ:=nodeVelocity J*J.v+2*J.hi*muNum J.hi
def weightedSection (J : Input) (h t s : ℕ) : ℕ :=
  nodeReducedOrdinate J*h+nodeVelocity J*t+nodeSeed J*s
theorem incidence_weights (J : Input) (s : ℕ) (hs : s ≤ degreeAt J.hi) :
    scale J.hi*(blockLength-s)≤(agreement-s)*muNum J.hi ∧
    scale J.hi*(blockLength-s)*(J.ell-s)≤(agreement-s)*nodeVelocity J:=by
  have hAn:agreement≤blockLength:=by decide
  have hL : quotientOrder J.lo ≤ agreement :=
    (Nat.sub_le _ _).trans (by decide:131071≤agreement)
  have hr : J.ell-s ≤ quotientOrder J.lo-s := by
    exact Nat.sub_le_sub_right (Nat.sub_le_sub_left J.lower _) _
  have hMu:=Nat.mul_le_mul_left agreement (mu_cross hAn J.agreement_gap.le hs)
  have hLam := Nat.mul_le_mul_left (gap J.hi)
    (lambda_cross hAn hL (hs.trans J.agreement_gap.le))
  constructor
  · unfold scale muNum gap
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hMu
  · calc
      _ ≤ scale J.hi * (blockLength-s) * (quotientOrder J.lo-s) :=
        Nat.mul_le_mul_left _ hr
      _ ≤ _ := by
        unfold scale nodeVelocity lambdaNum
        convert hLam using 1 <;> ring
theorem scale_pos (J : Input) : 0 < scale J.hi :=
  Nat.mul_pos (by decide) (Nat.sub_pos_of_lt J.agreement_gap)
theorem unit_le_weight (J : Input) {h t s : ℕ} (hp : 0 < s) :
    scale J.hi≤weightedSection J h t s:=by
  have hAn:agreement≤blockLength:=by decide
  have hm : scale J.hi ≤ muNum J.hi :=
    Nat.mul_le_mul_left agreement (Nat.sub_le_sub_right hAn _)
  have hw : 1 ≤ 2*J.hi := by
    have:=J.positive.trans_le J.upper
    omega
  have hn : muNum J.hi ≤ nodeSeed J := by
    have H:=Nat.mul_le_mul_right (muNum J.hi) hw
    rw [Nat.one_mul] at H
    exact H.trans (Nat.le_add_left _ _)
  exact (hm.trans hn).trans
    ((by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (nodeSeed J) hp :
      nodeSeed J≤nodeSeed J*s).trans (Nat.le_add_left _ _))
theorem mix_to_fee (J : Input) {k : ℕ}
    (h : scale J.hi*k ≤
      weightedSection J (J.v*cutSeed J + J.v^2*cutVelocity J)
        (2*J.e*J.v*cutSeed J+J.v^2*cutOrdinate J)
        (J.e*cutSeed J+J.v*((2*J.e-2)*cutVelocity J+cutOrdinate J))) :
    k≤properFee J.lo J.hi J.e J.v:=by
  have he:(J.e-3)+2=J.e-1:=by have h:3≤J.e:=J.sheets; omega
  have he' : (2*J.e-2)+2=2*J.e:=by have h:3≤J.e:=J.sheets; omega
  have hco : 2*cutVelocity J ≤ cutOrdinate J := by
    have htwo:2≤J.e-1:=by have h:3≤J.e:=J.sheets; omega
    exact (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (cutVelocity J) htwo :
      2*cutVelocity J≤ cutVelocity J*(J.e-1)).trans (Nat.le_add_left _ _)
  let nA:=muNum J.hi+nodeVelocity J*(J.e-1)
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
        cutSeed J*((2*J.e-2)*nodeVelocity J+nA)) +
      J.v^2*((cutOrdinate J - 2*cutVelocity J)*nodeVelocity J+nA*cutVelocity J)
  generalize 2*J.e-2=em at he' ⊢
  generalize cutOrdinate J - 2*cutVelocity J=ac0 at hc ⊢
  rw [← hnA, ← he', ← hc]
  unfold weightedSection
  ring
end
end P1_7_8
end
section
set_option autoImplicit false
namespace P1_7_8_3
noncomputable section
open P1 (K I node)
open P1_7_8 (Input ResidueLift Factors)
open K1_14 (FX Equation Seeds atX graphEval seedEmbedding)
open K1_14_6_1 (Dx partialX flatten)
open Polynomial (eval₂RingHom)
abbrev JetRing:=Polynomial Equation
instance jetCommRing:CommRing JetRing := @Polynomial.commRing Equation inferInstance
abbrev Degree:=ℕ × ℕ × ℕ
def nefDegree (h t s:ℕ):Degree:=(h+2*t,t,s)
abbrev CoxVar:=Fin 2 ⊕ (Fin 2 ⊕ Fin 3)
abbrev Cox:=MvPolynomial CoxVar FX
def h₀:CoxVar := .inl 0
def h₁:CoxVar := .inl 1
def v₀:CoxVar := .inr (.inl 0)
def v₁:CoxVar := .inr (.inl 1)
def tᵢ (i:Fin 3):CoxVar := .inr (.inr i)
def coxWeight : CoxVar → Degree
  | .inl _ => (1,0,0)
  | .inr (.inl i) => (2*i.val,1,0)
  | .inr (.inr _) => (0,0,1)
def ordinate:JetRing:=Polynomial.C Polynomial.X
def seedVar (i : Fin 2) : JetRing :=
  Polynomial.C (Polynomial.C (MvPolynomial.X i))
def affineCoord : CoxVar → JetRing
  | .inl i => if i=0 then 1 else ordinate
  | .inr (.inl i) => if i=0 then 1 else Polynomial.X
  | .inr (.inr i) => if hi:i.val < 2 then seedVar ⟨i.val,hi⟩ else 1
def dehom:Cox →ₐ[FX] JetRing:=MvPolynomial.aeval affineCoord
structure RelativeSection (Q : Ideal JetRing) (d : Degree) where
  order:ℕ
  finiteChart:Cox
  inverseChart:Cox
  finite_degree :
    finiteChart.IsWeightedHomogeneous coxWeight (d+order • (1,0,0))
  inverse_degree :
    inverseChart.IsWeightedHomogeneous coxWeight (d+order • (1,0,0))
  glue:ordinate ^ order*dehom finiteChart - dehom inverseChart ∈ Q
def RelativeSection.affine {Q : Ideal JetRing} {d : Degree}
    (S:RelativeSection Q d):JetRing :=
  dehom S.finiteChart
def RelativeSection.restrict {Q P : Ideal JetRing} {d : Degree} (h : Q ≤ P)
    (S:RelativeSection Q d):RelativeSection P d :=
  { S with glue:=h S.glue }
def gradedPiece (Q : Ideal JetRing) (d : Degree) : Submodule FX (JetRing ⧸ Q) :=
  (MvPolynomial.weightedHomogeneousSubmodule FX coxWeight d).map
    (((Ideal.Quotient.mkₐ FX Q).comp dehom).toLinearMap)
structure CurveProbe (Q : Ideal JetRing) where
  fiber:ℕ
  tangent:ℕ
  seed:ℕ
  offset:ℤ
  threshold:ℕ
  hilbert : ∀ h t s, threshold ≤ h → threshold ≤ t → threshold ≤ s →
    (Module.finrank FX (gradedPiece Q (nefDegree h t s)) : ℤ) =
      (h*fiber+t*tangent+s*seed:ℕ)+offset
def markRoot (J : Input) (γ : K) : Equation →+* FX :=
  eval₂RingHom (graphEval (J.model.label γ)) (atX (J.family.scalar γ))
def markPoint (J : Input) (γ : K) : JetRing →ₐ[FX] FX where
  toRingHom:=eval₂RingHom (markRoot J γ) (Dx (atX (J.family.scalar γ)))
  commutes' a := by
    change (eval₂RingHom (markRoot J γ) (Dx (atX (J.family.scalar γ))))
      (Polynomial.C (Polynomial.C (MvPolynomial.C a)))=a
    simp [markRoot,graphEval]
def tangentEquation (f : Equation) : JetRing :=
  Polynomial.C (MvPolynomial.optionEquivLeft FX (Fin 2) (partialX (flatten f))) +
    Polynomial.X*Polynomial.C f.derivative
def rootIdeal {J : Input} {B : ResidueLift J} (D : Factors J B) : Ideal JetRing :=
  Ideal.span {Polynomial.C D.proper}
def residueInJet {J : Input} (B : ResidueLift J) : JetRing :=
  Polynomial.C (Polynomial.C (P1_7_8.liftSeeds B.denominator))
def openFactor (J : Input) (B : ResidueLift J) : JetRing :=
  residueInJet B*Polynomial.C J.f.derivative
def saturate (Q : Ideal JetRing) (g : JetRing) : Ideal JetRing where
  carrier := {f | ∃ n:ℕ,g^n*f ∈ Q}
  zero_mem' := ⟨0,by simp⟩
  add_mem' := by
    rintro f h ⟨m,hm⟩ ⟨n,hn⟩
    refine ⟨m+n, ?_⟩
    rw [mul_add,pow_add]
    have hf:g^m*g^n*f=g^n*(g^m*f):=by ring
    have hh:g^m*g^n*h=g^m*(g^n*h):=by ring
    rw [hf,hh]
    exact Q.add_mem (Q.mul_mem_left _ hm) (Q.mul_mem_left _ hn)
  smul_mem' := by
    rintro a f ⟨n,hn⟩
    refine ⟨n, ?_⟩
    change g^n*(a*f) ∈ Q
    rw [show g^n*(a*f)=a*(g^n*f) by ring]
    exact Q.mul_mem_left _ hn
theorem le_saturate (Q : Ideal JetRing) (g : JetRing) : Q ≤ saturate Q g := by
  intro f hf
  exact ⟨0,by simpa using hf⟩
def graphIdeal (J : Input) (B : ResidueLift J) (D : Factors J B) : Ideal JetRing :=
  saturate (Ideal.span {Polynomial.C D.proper,tangentEquation J.f}) (openFactor J B)
theorem proper_mem_graph (J : Input) (B : ResidueLift J) (D : Factors J B) :
    Polynomial.C D.proper ∈ graphIdeal J B D :=
  le_saturate _ _ (Ideal.subset_span (by simp))
structure TangentSection (J : Input) {B : ResidueLift J} (D : Factors J B) where
  section_:RelativeSection (rootIdeal D) (J.e,1,J.v)
  affine_eq:section_.affine=tangentEquation J.f
def jetDegree (J : Input) (r : ℕ) : Degree :=
  nefDegree (1+(J.e-3)*r) r (r*J.v+2*J.w)
def jetDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  residueInJet B*Polynomial.C J.f.derivative ^ (r-1)
def oldDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  Polynomial.C
    (MvPolynomial.optionEquivLeft FX (Fin 2) (P1_7_8.quotientDenominator J B r))
def oldNumerator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  Polynomial.C
    (MvPolynomial.optionEquivLeft FX (Fin 2) (P1_7_8.quotientNumerator J B r))
structure TaylorSections (J : Input) (B : ResidueLift J) (D : Factors J B) (r : ℕ) where
  denominator:RelativeSection (graphIdeal J B D) (jetDegree J r)
  numerator:Fin (r+1)→RelativeSection (graphIdeal J B D) (jetDegree J r)
  den_eq:denominator.affine=jetDenominator J B r
  agrees : ∀ j : Fin (r+1),
    oldDenominator J B j.val * (numerator j).affine -
      oldNumerator J B j.val*denominator.affine ∈ graphIdeal J B D
structure CurveMarks (J : Input) (B : ResidueLift J) (D : Factors J B) where
  prime:Ideal JetRing
  isPrime:prime.IsPrime
  onGraph:graphIdeal J B D≤prime
  onCutoff:Polynomial.C (P1_7_8.cutoff J B) ∈ prime
  regular:openFactor J B ∉ prime
  marks:Finset K
  sub:marks ⊆ J.marks
  liesOn : ∀ γ ∈ marks,prime≤RingHom.ker (markPoint J γ).toRingHom
structure CurveSlice (J : Input) (B : ResidueLift J) (D : Factors J B)
    extends CurveMarks J B D where
  probe:CurveProbe prime
  positive_seed:0 < probe.seed
open scoped BigOperators
structure MixedCover (J : Input) (B : ResidueLift J) (D : Factors J B) where
  count:ℕ
  curves:Fin count→CurveSlice J B D
  covers : ∀ γ ∈ J.marks,P1_7_8.rootOn J D.proper γ → ∃ j,γ ∈ (curves j).marks
  fiber : ∑ j, (curves j).probe.fiber ≤
    J.v*P1_7_8.cutSeed J+J.v^2*P1_7_8.cutVelocity J
  tangent : ∑ j, (curves j).probe.tangent ≤
    2*J.e*J.v*P1_7_8.cutSeed J+J.v^2*P1_7_8.cutOrdinate J
  seed : ∑ j, (curves j).probe.seed ≤
    J.e*P1_7_8.cutSeed J+J.v*((2*J.e-2)*P1_7_8.cutVelocity J+P1_7_8.cutOrdinate J)
structure NodeSections {J : Input} {B : ResidueLift J} {D : Factors J B}
    (C:CurveMarks J B D) where
  persistent:Finset I
  hits : ∀ γ ∈ C.marks, ∀ x ∈ persistent,
    (J.family.scalar γ).eval (node x)=J.model.word x
  cuts : ∀ x ∉ persistent,
    ∃ S : RelativeSection C.prime (jetDegree J (J.ell - persistent.card)),
      S.affine ∉ C.prime ∧
      ∀ γ ∈ C.marks, (J.family.scalar γ).eval (node x) = J.model.word x →
        markPoint J γ S.affine=0
end
end P1_7_8_3
end
