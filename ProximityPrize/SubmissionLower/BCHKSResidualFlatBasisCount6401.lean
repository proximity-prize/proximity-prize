import ProximityPrize.SubmissionLower.BCHKSCodimTupleCount6400

/-!
# Greedy flat-basis incidence count at score 6401

This file isolates the finite combinatorics behind the residual-span route.
If every independent prefix of length `s < r` rules out at most `flatCap s`
coordinates, and every owner row spans rank `r+1`, then the number of ordered
bases in an owner row is at least

`prod_{s < r} (a - flatCap s)`.

A full basis determines the owner, so a global double count bounds the owner
family by the ambient falling factorial divided by this product.  The theorem
is deliberately phrased with an abstract hereditary tuple predicate: the
linear/polynomial layer only has to prove its flat caps and uniqueness.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSResidualFlatBasisCount6401

open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

section TupleTree

variable {U : Type*} [DecidableEq U]

/-- Finite tuples with all entries in `A` satisfying the rank predicate `P`. -/
def goodTuples (A : Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    (t : Nat) : Finset (Fin t → U) :=
  (Fintype.piFinset fun _ : Fin t ↦ A).filter (P t)

/-- Legal last entries extending a fixed good prefix. -/
def tupleExtensions (A : Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    {t : Nat} (f : Fin t → U) : Finset U :=
  A.filter fun x ↦ P (t + 1) (Fin.snoc f x)

lemma mem_goodTuples_iff (A : Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    {t : Nat} {f : Fin t → U} :
    f ∈ goodTuples A P t ↔ (∀ i, f i ∈ A) ∧ P t f := by
  simp [goodTuples, Fintype.mem_piFinset]

lemma mem_tupleExtensions_iff (A : Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    {t : Nat} {f : Fin t → U} {x : U} :
    x ∈ tupleExtensions A P f ↔ x ∈ A ∧ P (t + 1) (Fin.snoc f x) := by
  simp [tupleExtensions]

/-- A hereditary tuple predicate decomposes uniquely into a good prefix and
one legal last entry. -/
lemma goodTuples_card_succ_eq_sum_extensions
    (A : Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    (t : Nat)
    (hhered : ∀ (f : Fin t → U) (x : U),
      P (t + 1) (Fin.snoc f x) → P t f) :
    (goodTuples A P (t + 1)).card =
      ∑ f ∈ goodTuples A P t, (tupleExtensions A P f).card := by
  classical
  let G := goodTuples A P (t + 1)
  let H := goodTuples A P t
  have hmaps : ∀ q ∈ G, Fin.init q ∈ H := by
    intro q hq
    rw [mem_goodTuples_iff] at hq ⊢
    refine ⟨?_, ?_⟩
    · intro i
      exact hq.1 i.castSucc
    · rw [← Fin.snoc_init_self q] at hq
      exact hhered (Fin.init q) (q (Fin.last t)) hq.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro f hf
  let e : {q // q ∈ G.filter fun q ↦ Fin.init q = f} ≃
      {x // x ∈ tupleExtensions A P f} := {
    toFun := fun q ↦ ⟨q.1 (Fin.last t), by
      rw [mem_tupleExtensions_iff]
      have hqmem := Finset.mem_filter.mp q.2
      have hq := hqmem.1
      rw [mem_goodTuples_iff] at hq
      refine ⟨hq.1 (Fin.last t), ?_⟩
      have hsnoc : Fin.snoc f (q.1 (Fin.last t)) = q.1 := by
        calc
          Fin.snoc f (q.1 (Fin.last t)) =
              Fin.snoc (Fin.init q.1) (q.1 (Fin.last t)) := by
                exact congrArg
                  (fun p : Fin t → U ↦
                    Fin.snoc (α := fun _ ↦ U) p (q.1 (Fin.last t))) hqmem.2.symm
          _ = q.1 := Fin.snoc_init_self q.1
      rw [hsnoc]
      exact hq.2⟩
    invFun := fun x ↦ ⟨Fin.snoc f x.1, by
      apply Finset.mem_filter.mpr
      constructor
      · rw [mem_goodTuples_iff]
        have hx := (mem_tupleExtensions_iff A P).mp x.2
        refine ⟨?_, hx.2⟩
        intro i
        cases i using Fin.lastCases with
        | last => simpa using hx.1
        | cast j => simpa using ((mem_goodTuples_iff A P).mp hf).1 j
      · simp⟩
    left_inv := fun q ↦ by
      apply Subtype.ext
      have hqmem := Finset.mem_filter.mp q.2
      exact (by
        calc
          Fin.snoc f (q.1 (Fin.last t)) =
              Fin.snoc (Fin.init q.1) (q.1 (Fin.last t)) := by
                exact congrArg
                  (fun p : Fin t → U ↦
                    Fin.snoc (α := fun _ ↦ U) p (q.1 (Fin.last t))) hqmem.2.symm
          _ = q.1 := Fin.snoc_init_self q.1)
    right_inv := fun x ↦ by
      apply Subtype.ext
      simp }
  simpa using Fintype.card_congr e

/-- One greedy extension step multiplies the ordered-tuple lower bound. -/
lemma goodTuples_card_mul_gap_le_succ
    (A : Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    (t gap : Nat)
    (hhered : ∀ (f : Fin t → U) (x : U),
      P (t + 1) (Fin.snoc f x) → P t f)
    (hext : ∀ f ∈ goodTuples A P t,
      gap ≤ (tupleExtensions A P f).card) :
    (goodTuples A P t).card * gap ≤ (goodTuples A P (t + 1)).card := by
  rw [goodTuples_card_succ_eq_sum_extensions A P t hhered]
  calc
    (goodTuples A P t).card * gap =
        ∑ _f ∈ goodTuples A P t, gap := by simp
    _ ≤ ∑ f ∈ goodTuples A P t, (tupleExtensions A P f).card := by
      exact Finset.sum_le_sum hext

/-- Iterating the greedy extension estimate.  This is the division-free
version of the usual product-of-gaps lower bound for ordered bases. -/
theorem prod_gaps_le_goodTuples_card
    (A : Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    (gap : Nat → Nat) (t : Nat)
    (hzero : P 0 Fin.elim0)
    (hhered : ∀ s (f : Fin s → U) (x : U),
      P (s + 1) (Fin.snoc f x) → P s f)
    (hext : ∀ s < t, ∀ f ∈ goodTuples A P s,
      gap s ≤ (tupleExtensions A P f).card) :
    (∏ s ∈ Finset.range t, gap s) ≤ (goodTuples A P t).card := by
  induction t with
  | zero =>
      have hempty : goodTuples A P 0 = {Fin.elim0} := by
        have hdef : (default : Fin 0 → U) = Fin.elim0 := Subsingleton.elim _ _
        ext f
        have hf : f = Fin.elim0 := Subsingleton.elim _ _
        simp [goodTuples, hf, hzero, hdef]
      simp [hempty]
  | succ t ih =>
      rw [Finset.prod_range_succ]
      have hi := ih (fun s hs ↦ hext s (Nat.lt.step hs))
      have hstep := goodTuples_card_mul_gap_le_succ A P t (gap t)
        (hhered t) (hext t (Nat.lt_succ_self t))
      exact (Nat.mul_le_mul_right (gap t) hi).trans hstep

/-- Global incidence swap for any owner-independent tuple predicate.
Every good tuple is charged to at most one owner.  We upper-bound ambient
tuples by `|U|^t`; an injective-tuple refinement may replace this by the
falling factorial, but is not needed for the score-6401 thresholds. -/
theorem ownerCard_mul_tupleMass_le_pow
    {Owner : Type*} [DecidableEq Owner]
    (Uset : Finset U) (S : Finset Owner) (A : Owner → Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    (t mass : Nat)
    (hsub : ∀ z ∈ S, A z ⊆ Uset)
    (hrow : ∀ z ∈ S, mass ≤ (goodTuples (A z) P t).card)
    (hunique : ∀ f ∈ goodTuples Uset P t,
      (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card ≤ 1) :
    S.card * mass ≤ Uset.card ^ t := by
  classical
  have hlower : S.card * mass ≤
      ∑ z ∈ S, (goodTuples (A z) P t).card := by
    calc
      S.card * mass = ∑ _z ∈ S, mass := by simp
      _ ≤ ∑ z ∈ S, (goodTuples (A z) P t).card := by
        exact Finset.sum_le_sum hrow
  have hswap : (∑ z ∈ S, (goodTuples (A z) P t).card) =
      ∑ f ∈ goodTuples Uset P t,
        (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card := by
    calc
      (∑ z ∈ S, (goodTuples (A z) P t).card) =
          ∑ z ∈ S, ∑ f ∈ goodTuples Uset P t,
            if f ∈ goodTuples (A z) P t then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [← Finset.card_filter]
        congr 1
        ext f
        simp only [Finset.mem_filter]
        constructor
        · intro hf
          refine ⟨?_, hf⟩
          rw [mem_goodTuples_iff] at hf ⊢
          exact ⟨fun i ↦ hsub z hz (hf.1 i), hf.2⟩
        · exact And.right
      _ = ∑ f ∈ goodTuples Uset P t, ∑ z ∈ S,
          if f ∈ goodTuples (A z) P t then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ f ∈ goodTuples Uset P t,
          (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card := by
        apply Finset.sum_congr rfl
        intro f hf
        simp
  have hambient : (goodTuples Uset P t).card ≤ Uset.card ^ t := by
    calc
      (goodTuples Uset P t).card ≤
          (Fintype.piFinset fun _ : Fin t ↦ Uset).card := by
        exact Finset.card_filter_le _ _
      _ = Uset.card ^ t := by simp
  calc
    S.card * mass ≤ ∑ z ∈ S, (goodTuples (A z) P t).card := hlower
    _ = ∑ f ∈ goodTuples Uset P t,
        (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card := hswap
    _ ≤ ∑ _f ∈ goodTuples Uset P t, 1 := by
      exact Finset.sum_le_sum hunique
    _ = (goodTuples Uset P t).card := by simp
    _ ≤ Uset.card ^ t := hambient

/-- The same incidence swap, retaining the exact ambient good-tuple count. -/
theorem ownerCard_mul_tupleMass_le_goodAmbient
    {Owner : Type*} [DecidableEq Owner]
    (Uset : Finset U) (S : Finset Owner) (A : Owner → Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    (t mass : Nat)
    (hsub : ∀ z ∈ S, A z ⊆ Uset)
    (hrow : ∀ z ∈ S, mass ≤ (goodTuples (A z) P t).card)
    (hunique : ∀ f ∈ goodTuples Uset P t,
      (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card ≤ 1) :
    S.card * mass ≤ (goodTuples Uset P t).card := by
  classical
  have hlower : S.card * mass ≤
      ∑ z ∈ S, (goodTuples (A z) P t).card := by
    calc
      S.card * mass = ∑ _z ∈ S, mass := by simp
      _ ≤ ∑ z ∈ S, (goodTuples (A z) P t).card := by
        exact Finset.sum_le_sum hrow
  have hswap : (∑ z ∈ S, (goodTuples (A z) P t).card) =
      ∑ f ∈ goodTuples Uset P t,
        (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card := by
    calc
      (∑ z ∈ S, (goodTuples (A z) P t).card) =
          ∑ z ∈ S, ∑ f ∈ goodTuples Uset P t,
            if f ∈ goodTuples (A z) P t then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [← Finset.card_filter]
        congr 1
        ext f
        simp only [Finset.mem_filter]
        constructor
        · intro hf
          refine ⟨?_, hf⟩
          rw [mem_goodTuples_iff] at hf ⊢
          exact ⟨fun i ↦ hsub z hz (hf.1 i), hf.2⟩
        · exact And.right
      _ = ∑ f ∈ goodTuples Uset P t, ∑ z ∈ S,
          if f ∈ goodTuples (A z) P t then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ f ∈ goodTuples Uset P t,
          (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card := by
        apply Finset.sum_congr rfl
        intro f hf
        simp
  calc
    S.card * mass ≤ ∑ z ∈ S, (goodTuples (A z) P t).card := hlower
    _ = ∑ f ∈ goodTuples Uset P t,
        (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card := hswap
    _ ≤ ∑ _f ∈ goodTuples Uset P t, 1 := by
      exact Finset.sum_le_sum hunique
    _ = (goodTuples Uset P t).card := by simp

/-- Injective ambient good tuples are counted by the exact falling
factorial. -/
theorem goodTuples_card_le_descFactorial
    (Uset : Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    (t : Nat)
    (hinj : ∀ f ∈ goodTuples Uset P t, Function.Injective f) :
    (goodTuples Uset P t).card ≤ Uset.card.descFactorial t := by
  classical
  let emb : ↥(goodTuples Uset P t) ↪ (Fin t ↪ ↥Uset) := {
    toFun := fun f ↦ {
      toFun := fun i ↦ ⟨f.1 i, (mem_goodTuples_iff Uset P).mp f.2 |>.1 i⟩
      inj' := by
        intro i j hij
        apply hinj f.1 f.2
        exact congrArg Subtype.val hij }
    inj' := by
      intro f g h
      apply Subtype.ext
      funext i
      exact congrArg (fun e : Fin t ↪ ↥Uset ↦ (e i : U)) h }
  calc
    (goodTuples Uset P t).card = Fintype.card ↥(goodTuples Uset P t) := by simp
    _ ≤ Fintype.card (Fin t ↪ ↥Uset) := Fintype.card_le_of_embedding emb
    _ = Uset.card.descFactorial t := by simp

/-- Exact falling-factorial variant of the global tuple incidence bound. -/
theorem ownerCard_mul_tupleMass_le_descFactorial
    {Owner : Type*} [DecidableEq Owner]
    (Uset : Finset U) (S : Finset Owner) (A : Owner → Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    (t mass : Nat)
    (hsub : ∀ z ∈ S, A z ⊆ Uset)
    (hrow : ∀ z ∈ S, mass ≤ (goodTuples (A z) P t).card)
    (hunique : ∀ f ∈ goodTuples Uset P t,
      (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card ≤ 1)
    (hinj : ∀ f ∈ goodTuples Uset P t, Function.Injective f) :
    S.card * mass ≤ Uset.card.descFactorial t :=
  (ownerCard_mul_tupleMass_le_goodAmbient Uset S A P t mass hsub hrow hunique).trans
    (goodTuples_card_le_descFactorial Uset P t hinj)

/-- End-to-end abstract greedy basis count. -/
theorem ownerCard_mul_prod_gaps_le_pow
    {Owner : Type*} [DecidableEq Owner]
    (Uset : Finset U) (S : Finset Owner) (A : Owner → Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    (gap : Nat → Nat) (t : Nat)
    (hsub : ∀ z ∈ S, A z ⊆ Uset)
    (hzero : P 0 Fin.elim0)
    (hhered : ∀ s (f : Fin s → U) (x : U),
      P (s + 1) (Fin.snoc f x) → P s f)
    (hext : ∀ z ∈ S, ∀ s < t, ∀ f ∈ goodTuples (A z) P s,
      gap s ≤ (tupleExtensions (A z) P f).card)
    (hunique : ∀ f ∈ goodTuples Uset P t,
      (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card ≤ 1) :
    S.card * (∏ s ∈ Finset.range t, gap s) ≤ Uset.card ^ t := by
  apply ownerCard_mul_tupleMass_le_pow Uset S A P t
    (∏ s ∈ Finset.range t, gap s) hsub
  · intro z hz
    exact prod_gaps_le_goodTuples_card (A z) P gap t hzero hhered
      (hext z hz)
  · exact hunique

/-- Exact falling-factorial end-to-end abstract greedy basis count. -/
theorem ownerCard_mul_prod_gaps_le_descFactorial
    {Owner : Type*} [DecidableEq Owner]
    (Uset : Finset U) (S : Finset Owner) (A : Owner → Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    (gap : Nat → Nat) (t : Nat)
    (hsub : ∀ z ∈ S, A z ⊆ Uset)
    (hzero : P 0 Fin.elim0)
    (hhered : ∀ s (f : Fin s → U) (x : U),
      P (s + 1) (Fin.snoc f x) → P s f)
    (hext : ∀ z ∈ S, ∀ s < t, ∀ f ∈ goodTuples (A z) P s,
      gap s ≤ (tupleExtensions (A z) P f).card)
    (hunique : ∀ f ∈ goodTuples Uset P t,
      (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card ≤ 1)
    (hinj : ∀ f ∈ goodTuples Uset P t, Function.Injective f) :
    S.card * (∏ s ∈ Finset.range t, gap s) ≤
      Uset.card.descFactorial t := by
  apply ownerCard_mul_tupleMass_le_descFactorial Uset S A P t
    (∏ s ∈ Finset.range t, gap s) hsub
  · intro z hz
    exact prod_gaps_le_goodTuples_card (A z) P gap t hzero hhered
      (hext z hz)
  · exact hunique
  · exact hinj

end TupleTree

section LinearFlatCount

variable {U Owner F V : Type*} [DecidableEq U] [DecidableEq Owner]
  [Field F] [AddCommGroup V] [Module F V]

/-- The tuple predicate used by the residual-span application. -/
def independentNormalTuples (normal : U → V) (t : Nat) (f : Fin t → U) : Prop :=
  LinearIndependent F (normal ∘ f)

noncomputable instance independentNormalTuples_decidable (normal : U → V) (t : Nat) :
    DecidablePred (independentNormalTuples (F := F) normal t) := Classical.decPred _

/-- Coordinates whose normal lies in the span of a fixed prefix.  The
definition is noncomputable only because membership in a general submodule
need not have a computational decision procedure. -/
noncomputable def normalSpanFlat (A : Finset U) (normal : U → V)
    {t : Nat} (f : Fin t → U) : Finset U := by
  classical
  exact A.filter fun x ↦ normal x ∈ Submodule.span F (Set.range (normal ∘ f))

lemma independentNormalTuples_zero (normal : U → V) :
    independentNormalTuples (F := F) normal 0 Fin.elim0 := by
  exact linearIndependent_empty_type

lemma independentNormalTuples_snoc_iff (normal : U → V)
    {t : Nat} (f : Fin t → U) (x : U) :
    independentNormalTuples (F := F) normal (t + 1) (Fin.snoc f x) ↔
      independentNormalTuples (F := F) normal t f ∧
        normal x ∉ Submodule.span F (Set.range (normal ∘ f)) := by
  rw [independentNormalTuples, independentNormalTuples, Fin.comp_snoc,
    linearIndependent_finSnoc]

/-- The legal extensions of an independent normal tuple are exactly the
coordinates whose normal lies outside the prefix span. -/
lemma independent_tupleExtensions_eq_filter_not_span
    (A : Finset U) (normal : U → V) {t : Nat} (f : Fin t → U)
    (hf : f ∈ goodTuples A (independentNormalTuples (F := F) normal) t) :
    tupleExtensions A (independentNormalTuples (F := F) normal) f =
      A \ normalSpanFlat (F := F) A normal f := by
  classical
  ext x
  rw [mem_tupleExtensions_iff]
  have hfi := (mem_goodTuples_iff A
    (independentNormalTuples (F := F) normal)).mp hf
  rw [independentNormalTuples_snoc_iff]
  simp only [Finset.mem_sdiff, normalSpanFlat, Finset.mem_filter]
  constructor
  · rintro ⟨hxA, _hp, hout⟩
    exact ⟨hxA, fun hin ↦ hout hin.2⟩
  · rintro ⟨hxA, hnot⟩
    exact ⟨hxA, hfi.2, fun hin ↦ hnot ⟨hxA, hin⟩⟩

/-- A flat-cardinality cap gives the corresponding greedy extension gap. -/
lemma independent_tupleExtensions_card_gap
    (A : Finset U) (normal : U → V) {t a cap : Nat} (f : Fin t → U)
    (hf : f ∈ goodTuples A (independentNormalTuples (F := F) normal) t)
    (hA : a ≤ A.card)
    (hflat : (normalSpanFlat (F := F) A normal f).card ≤ cap) :
    a - cap ≤
      (tupleExtensions A (independentNormalTuples (F := F) normal) f).card := by
  rw [independent_tupleExtensions_eq_filter_not_span A normal f hf]
  have hsubset : normalSpanFlat (F := F) A normal f ⊆ A := by
    classical
    intro x hx
    change x ∈ A.filter (fun x ↦
      normal x ∈ Submodule.span F (Set.range (normal ∘ f))) at hx
    exact (Finset.mem_filter.mp hx).1
  have hsplit := Finset.card_sdiff_add_card_eq_card hsubset
  omega

/-- Greedy independent-basis incidence bound from rank-flat caps.

`flatCap s` may include zero normals at `s=0`.  In the rational received-word
branch one takes the final cap to be `153578`; without that extra root bound,
one may use `a-1` merely from full spanning. -/
theorem ownerCard_mul_linearFlatGaps_le_pow
    (Uset : Finset U) (S : Finset Owner) (A : Owner → Finset U)
    (normal : U → V) (flatCap : Nat → Nat) (a t : Nat)
    (hsub : ∀ z ∈ S, A z ⊆ Uset)
    (hrow : ∀ z ∈ S, a ≤ (A z).card)
    (hflat : ∀ z ∈ S, ∀ s < t,
      ∀ f ∈ goodTuples (A z) (independentNormalTuples (F := F) normal) s,
        (normalSpanFlat (F := F) (A z) normal f).card ≤ flatCap s)
    (hunique : ∀ f ∈
        goodTuples Uset (independentNormalTuples (F := F) normal) t,
      (S.filter fun z ↦
        f ∈ goodTuples (A z) (independentNormalTuples (F := F) normal) t).card ≤ 1) :
    S.card * (∏ s ∈ Finset.range t, (a - flatCap s)) ≤ Uset.card ^ t := by
  apply ownerCard_mul_prod_gaps_le_pow Uset S A
    (independentNormalTuples (F := F) normal) (fun s ↦ a - flatCap s) t hsub
  · exact independentNormalTuples_zero normal
  · intro s f x hs
    exact (independentNormalTuples_snoc_iff normal f x).mp hs |>.1
  · intro z hz s hs f hf
    exact independent_tupleExtensions_card_gap (A z) normal f hf
      (hrow z hz) (hflat z hz s hs f hf)
  · exact hunique

/-- Exact falling-factorial form of `ownerCard_mul_linearFlatGaps_le_pow`. -/
theorem ownerCard_mul_linearFlatGaps_le_descFactorial
    (Uset : Finset U) (S : Finset Owner) (A : Owner → Finset U)
    (normal : U → V) (flatCap : Nat → Nat) (a t : Nat)
    (hsub : ∀ z ∈ S, A z ⊆ Uset)
    (hrow : ∀ z ∈ S, a ≤ (A z).card)
    (hflat : ∀ z ∈ S, ∀ s < t,
      ∀ f ∈ goodTuples (A z) (independentNormalTuples (F := F) normal) s,
        (normalSpanFlat (F := F) (A z) normal f).card ≤ flatCap s)
    (hunique : ∀ f ∈
        goodTuples Uset (independentNormalTuples (F := F) normal) t,
      (S.filter fun z ↦
        f ∈ goodTuples (A z) (independentNormalTuples (F := F) normal) t).card ≤ 1) :
    S.card * (∏ s ∈ Finset.range t, (a - flatCap s)) ≤
      Uset.card.descFactorial t := by
  apply ownerCard_mul_prod_gaps_le_descFactorial Uset S A
    (independentNormalTuples (F := F) normal) (fun s ↦ a - flatCap s) t hsub
  · exact independentNormalTuples_zero normal
  · intro s f x hs
    exact (independentNormalTuples_snoc_iff normal f x).mp hs |>.1
  · intro z hz s hs f hf
    exact independent_tupleExtensions_card_gap (A z) normal f hf
      (hrow z hz) (hflat z hz s hs f hf)
  · exact hunique
  · intro f hf
    have hli := (mem_goodTuples_iff Uset
      (independentNormalTuples (F := F) normal)).mp hf |>.2
    intro i j hij
    exact hli.injective (congrArg normal hij)

end LinearFlatCount

section RationalFinalFlat

variable {F I : Type*} [Field F] [DecidableEq I]

/-- A polynomial match to a cleared rational received direction can occur on
at most the degree of `lambda*T-R`, unless that obstruction is identically
zero.  This is the exact final-flat lemma needed by the rational residual
span count; denominator zeros cause no exception because the hypothesis is
already in cleared form. -/
theorem rationalMatchFlat_card_le
    (alpha : I ↪ F) (B : Finset I) (V : I → F)
    (lambda R T : Polynomial F)
    (denominatorCap numeratorCap polynomialCap : Nat)
    (hlambda : lambda.natDegree ≤ denominatorCap)
    (hR : R.natDegree ≤ numeratorCap)
    (hT : T.natDegree ≤ polynomialCap)
    (hcleared : ∀ i ∈ B,
      lambda.eval (alpha i) * V i = R.eval (alpha i))
    (hmatch : ∀ i ∈ B, T.eval (alpha i) = V i)
    (hnonzero : lambda * T - R ≠ 0) :
    B.card ≤ max (denominatorCap + polynomialCap) numeratorCap := by
  let D := lambda * T - R
  have hmul : (lambda * T).natDegree ≤ denominatorCap + polynomialCap :=
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add hlambda hT)
  have hdegree : D.natDegree ≤
      max (denominatorCap + polynomialCap) numeratorCap := by
    exact (Polynomial.natDegree_sub_le _ _).trans <| max_le
      (hmul.trans (Nat.le_max_left _ _))
      (hR.trans (Nat.le_max_right _ _))
  by_contra hcard
  have hlt : D.natDegree < B.card := hdegree.trans_lt (Nat.lt_of_not_ge hcard)
  have hzero : D = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      D (B.map alpha)
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
      dsimp [D]
      rw [Polynomial.eval_sub, Polynomial.eval_mul, hmatch i hi,
        hcleared i hi]
      exact sub_self _
    · simpa using hlt
  exact hnonzero hzero

end RationalFinalFlat

section Arithmetic6401

def flatAmbient6401 : Nat := 262144
def flatAgreement6401 : Nat := 185354
def flatDegreeCap6401 : Nat := 131071
def flatMcaBudget6401 : Nat := 274980728094349243
def rationalFinalFlatCap6401 : Nat := 153578

/-- Zero-row-safe flat cap for residual dimension `r`.  The last rank-`r`
flat receives only the trivial `a-1` cap. -/
def standardResidualFlatCap6401 (r s : Nat) : Nat :=
  if s < r then flatDegreeCap6401 - r + s + 1 else flatAgreement6401 - 1

/-- Rational/no-direction sharpening: the last rank-`r` flat has at most
`153578` coordinates by the degree of `lambda*T-R`. -/
def rationalResidualFlatCap6401 (r s : Nat) : Nat :=
  if s < r then flatDegreeCap6401 - r + s + 1 else rationalFinalFlatCap6401

def standardResidualBasisMass6401 (r : Nat) : Nat :=
  ∏ s ∈ Finset.range (r + 1),
    (flatAgreement6401 - standardResidualFlatCap6401 r s)

def rationalResidualBasisMass6401 (r : Nat) : Nat :=
  ∏ s ∈ Finset.range (r + 1),
    (flatAgreement6401 - rationalResidualFlatCap6401 r s)

/-- Concrete score-6401 rational final-flat cap. -/
theorem rationalMatchFlat_card_le_1535786401
    {F I : Type*} [Field F] [DecidableEq I]
    (alpha : I ↪ F) (B : Finset I) (V : I → F)
    (lambda R T : Polynomial F)
    (hlambda : lambda.natDegree ≤ 22507)
    (hR : R.natDegree ≤ rationalFinalFlatCap6401)
    (hT : T.natDegree ≤ flatDegreeCap6401)
    (hcleared : ∀ i ∈ B,
      lambda.eval (alpha i) * V i = R.eval (alpha i))
    (hmatch : ∀ i ∈ B, T.eval (alpha i) = V i)
    (hnonzero : lambda * T - R ≠ 0) :
    B.card ≤ rationalFinalFlatCap6401 := by
  have h := rationalMatchFlat_card_le alpha B V lambda R T
    22507 rationalFinalFlatCap6401 flatDegreeCap6401
    hlambda hR hT hcleared hmatch hnonzero
  norm_num [rationalFinalFlatCap6401, flatDegreeCap6401] at h ⊢
  exact h

/-- All rational residual dimensions `rho < 25` fit the MCA budget. -/
theorem rationalResidualFlat_all_dimensions_lt25_exact6401 :
    ∀ rho : Fin 25,
      flatAmbient6401.descFactorial (rho.val + 1) <
        flatMcaBudget6401 * rationalResidualBasisMass6401 rho.val := by
  native_decide

/-- The corrected zero-row-safe count closes every residual dimension through
17; dimension 18 is the first miss without a sharper final flat. -/
theorem standardResidualFlat_threshold_exact6401 :
    110431213677923142 * standardResidualBasisMass6401 17 ≤
        flatAmbient6401.descFactorial 18 ∧
      110431213677923143 * standardResidualBasisMass6401 17 >
        flatAmbient6401.descFactorial 18 ∧
      110431213677923142 < flatMcaBudget6401 ∧
      flatMcaBudget6401 * standardResidualBasisMass6401 18 <
        flatAmbient6401.descFactorial 19 := by
  native_decide

/-- Exact rank-four cap, including possible zero normal rows. -/
theorem standardResidualFlat_rankFour_exact6401 :
    142554087 * standardResidualBasisMass6401 4 ≤
        flatAmbient6401.descFactorial 5 ∧
      142554088 * standardResidualBasisMass6401 4 >
        flatAmbient6401.descFactorial 5 := by
  native_decide

/-- With the rational last-flat cap `153578`, the same count closes through
residual dimension 24; dimension 25 is the first miss. -/
theorem rationalResidualFlat_threshold_exact6401 :
    212208007407949630 * rationalResidualBasisMass6401 24 ≤
        flatAmbient6401.descFactorial 25 ∧
      212208007407949631 * rationalResidualBasisMass6401 24 >
        flatAmbient6401.descFactorial 25 ∧
      212208007407949630 < flatMcaBudget6401 ∧
      flatMcaBudget6401 * rationalResidualBasisMass6401 25 <
        flatAmbient6401.descFactorial 26 := by
  native_decide

/-- Packaged bounded-span branch.  Once the caller supplies the exact
generalized-flat caps and basis uniqueness for a residual space of dimension
`rho < 25`, the whole owner family fits below the MCA budget. -/
theorem ownerCard_lt_mca_of_rationalResidualDimension_lt25
    {U Owner F V : Type*} [DecidableEq U] [DecidableEq Owner]
    [Field F] [AddCommGroup V] [Module F V]
    (Uset : Finset U) (S : Finset Owner) (A : Owner → Finset U)
    (normal : U → V) (rho : Fin 25)
    (hUcard : Uset.card = flatAmbient6401)
    (hsub : ∀ z ∈ S, A z ⊆ Uset)
    (hrow : ∀ z ∈ S, flatAgreement6401 ≤ (A z).card)
    (hflat : ∀ z ∈ S, ∀ s < rho.val + 1,
      ∀ f ∈ goodTuples (A z)
          (independentNormalTuples (F := F) normal) s,
        (normalSpanFlat (F := F) (A z) normal f).card ≤
          rationalResidualFlatCap6401 rho.val s)
    (hunique : ∀ f ∈ goodTuples Uset
        (independentNormalTuples (F := F) normal) (rho.val + 1),
      (S.filter fun z ↦ f ∈ goodTuples (A z)
        (independentNormalTuples (F := F) normal) (rho.val + 1)).card ≤ 1) :
    S.card < flatMcaBudget6401 := by
  have hcount := ownerCard_mul_linearFlatGaps_le_descFactorial
    Uset S A normal (rationalResidualFlatCap6401 rho.val)
      flatAgreement6401 (rho.val + 1) hsub hrow hflat hunique
  rw [hUcard] at hcount
  change S.card * rationalResidualBasisMass6401 rho.val ≤
    flatAmbient6401.descFactorial (rho.val + 1) at hcount
  have hfit := rationalResidualFlat_all_dimensions_lt25_exact6401 rho
  by_contra hnot
  have hbudget : flatMcaBudget6401 ≤ S.card := Nat.le_of_not_gt hnot
  have hmul : flatMcaBudget6401 * rationalResidualBasisMass6401 rho.val ≤
      S.card * rationalResidualBasisMass6401 rho.val :=
    Nat.mul_le_mul_right (rationalResidualBasisMass6401 rho.val) hbudget
  exact (Nat.not_le_of_lt hfit) (hmul.trans hcount)

end Arithmetic6401

end BCHKSResidualFlatBasisCount6401
end ProximityPrize.SubmissionLower
