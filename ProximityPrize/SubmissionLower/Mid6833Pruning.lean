/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Affine agreement slicing for scalar and seed-dependent received words.
   Uses the affine-subspace pruning principle of Kopparty–Ron-Zewi–Saraf–Wootters
   and Tamo. The moving-word terminal condition is the bounded-pencil hypothesis. -/
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace Frontier.Pruning
open Polynomial Finset
open scoped Classical BigOperators Polynomial
noncomputable section
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableEq K := Classical.decEq _

def rank (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (S : Finset V) : ℕ := Module.finrank K (affineSpan K (↑S : Set V)).direction

private theorem smaller (S : Finset V) (f : V →ₗ[K] K) (y : K)
    (proper : ∃ p ∈ S, f p ≠ y) (ne : (S.filter (fun p => f p=y)).Nonempty) :
    rank K (S.filter (fun p => f p=y)) < rank K S := by
  classical
  let T := S.filter (fun p => f p=y)
  let H : AffineSubspace K V := (affineSpan K ({y} : Set K)).comap f.toAffineMap
  have inH (p : V) : p ∈ H ↔ f p=y := by
    change f p ∈ affineSpan K ({y} : Set K) ↔ f p=y
    exact AffineSubspace.mem_affineSpan_singleton _ _
  have sh : affineSpan K (↑T : Set V) ≤ H := affineSpan_le.mpr (fun p hp =>
    (inH p).mpr (Finset.mem_filter.mp hp).2)
  have ss : affineSpan K (↑T : Set V) < affineSpan K (↑S : Set V) := by
    refine lt_of_le_of_ne (affineSpan_mono K (Finset.filter_subset _ _)) ?_
    intro same
    obtain ⟨p,hp,bad⟩ := proper
    rw [same] at sh
    exact bad ((inH p).mp (sh (subset_affineSpan K _ hp)))
  let : FiniteDimensional K (affineSpan K (↑S : Set V)).direction := by
    rw [direction_affineSpan]
    exact .span_of_finite K (S.finite_toSet.vsub S.finite_toSet)
  exact Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty ss (ne.to_set.affineSpan K))

/-- Integer recursion permits an exceptional class of size b at every node of the proof. -/
def cap (n a d b : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => max b ((n-d)*cap n a d b k/(a-d))

theorem slice (f : I → V →ₗ[K] K) (word : I → K) (a d b : ℕ)
    (hda : d<a) (han : a≤Fintype.card I) (k : ℕ) (S : Finset V) (rk : rank K S ≤ k)
    (single : ∀ p ∈ S, a ≤ (Finset.univ.filter (fun i => f i p=word i)).card)
    (common : ∀ T ⊆ S, b<T.card →
      (Finset.univ.filter (fun i => ∀ p ∈ T, f i p=word i)).card ≤ d) :
    S.card ≤ cap (Fintype.card I) a d b k := by
  classical
  induction k generalizing S with
  | zero =>
    apply Finset.card_le_one.mpr
    intro p hp q hq
    by_contra pq
    have lt : Module.finrank K (affineSpan K ({p} : Set V)).direction < rank K S := by
      have ss : affineSpan K ({p} : Set V) < affineSpan K (↑S : Set V) := by
        apply lt_of_le_of_ne (affineSpan_mono K (Set.singleton_subset_iff.mpr hp))
        intro eq
        have mq := subset_affineSpan K (↑S : Set V) hq
        rw [← eq] at mq
        exact pq ((AffineSubspace.mem_affineSpan_singleton _ _).mp mq).symm
      let : FiniteDimensional K (affineSpan K (↑S : Set V)).direction := by
        rw [direction_affineSpan]
        exact .span_of_finite K (S.finite_toSet.vsub S.finite_toSet)
      exact Submodule.finrank_lt_finrank_of_lt
        (AffineSubspace.direction_lt_of_nonempty ss (Set.singleton_nonempty p |>.affineSpan K))
    omega
  | succ k IH =>
    rw [cap]
    by_cases small : S.card ≤ b
    · exact small.trans (le_max_left _ _)
    apply le_trans _ (le_max_right _ _)
    let C := Finset.univ.filter (fun i => ∀ p ∈ S, f i p=word i)
    let O := Finset.univ \ C
    let T (i : I) := S.filter (fun p => f i p=word i)
    let B := cap (Fintype.card I) a d b k
    have hc : C.card ≤ d := common S (Finset.Subset.refl _) (by omega)
    have on : O.card+C.card=Fintype.card I := by
      simp [O,Finset.card_sdiff_of_subset (Finset.subset_univ C),Nat.sub_add_cancel (Finset.card_le_univ C)]
    have child (i : I) (oi : i ∈ O) : (T i).card ≤ B := by
      by_cases neT : (T i).Nonempty
      swap
      · simp [Finset.not_nonempty_iff_eq_empty.mp neT]
      have proper : ∃ p ∈ S, f i p≠word i := by
        by_contra! all
        exact (Finset.mem_sdiff.mp oi).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,all⟩)
      have lt := smaller S (f i) (word i) proper neT
      have sub : T i ⊆ S := Finset.filter_subset _ _
      exact IH (T i) (by change rank K (S.filter _) ≤ k; omega)
        (fun p hp => single p (sub hp)) (fun Z hz => common Z (hz.trans sub))
    have countP (p : V) (hp : p ∈ S) :
        a ≤ C.card+(O.filter (fun i => f i p=word i)).card := by
      apply (single p hp).trans
      have sub : Finset.univ.filter (fun i => f i p=word i) ⊆ C ∪ O.filter (fun i => f i p=word i) := by
        intro i hi
        by_cases inside : i ∈ C
        · exact Finset.mem_union_left _ inside
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,inside⟩,(Finset.mem_filter.mp hi).2⟩)
      exact (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    have mass : S.card*(a-C.card) ≤ O.card*B := by
      calc
        _ = ∑ _p ∈ S, (a-C.card) := by simp
        _ ≤ ∑ p ∈ S, (O.filter (fun i => f i p=word i)).card := Finset.sum_le_sum (fun p hp => by have := countP p hp; omega)
        _ = ∑ i ∈ O, (T i).card := by simp only [T,Finset.card_filter]; exact Finset.sum_comm
        _ ≤ ∑ _i ∈ O, B := Finset.sum_le_sum child
        _ = _ := by simp
    apply (Nat.le_div_iff_mul_le (by omega : 0<a-d)).mpr
    by_cases sb : S.card ≤ B
    · exact Nat.mul_le_mul sb (by omega : a-d ≤ Fintype.card I-d) |>.trans_eq (Nat.mul_comm _ _)
    have H : (d-C.card)*B ≤ (d-C.card)*S.card := Nat.mul_le_mul_left _ (by omega)
    have ea : a-C.card=(a-d)+(d-C.card) := by omega
    have en : O.card=(Fintype.card I-d)+(d-C.card) := by omega
    rw [ea,en,Nat.mul_add,Nat.add_mul] at mass
    nlinarith only [H,mass]

omit [Fintype I] in
private theorem eq_of_nodes (x : I ↪ K) (C : Finset I) (d : ℕ) (large : d<C.card)
    (p q : K[X]) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (same : ∀ i ∈ C, p.eval (x i)=q.eval (x i)) : p=q := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (f := fun i : C => x i.val)
    (x.injective.comp Subtype.val_injective)
  · intro i
    exact same i i.property
  · rw [Fintype.card_coe]
    exact lt_of_le_of_lt (max_le hp hq) large

/-- A dimension-sensitive scalar RS list certificate on any evaluation domain. -/
theorem scalar (x : I ↪ K) (word : I → K) (a d k : ℕ)
    (hda : d<a) (han : a≤Fintype.card I)
    (S : Finset K[X]) (rk : rank K S ≤ k) (deg : ∀ p ∈ S, p.natDegree ≤ d)
    (ag : ∀ p ∈ S, a ≤ (Finset.univ.filter (fun i => p.eval (x i)=word i)).card) :
    S.card ≤ cap (Fintype.card I) a d 1 k := by
  classical
  apply slice (fun i => Polynomial.leval (x i)) word a d 1 hda han k S rk ag
  intro T sub large
  let C := Finset.univ.filter (fun i => ∀ p ∈ T, p.eval (x i)=word i)
  change C.card ≤ d
  by_contra! hc
  obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp large
  exact ne (eq_of_nodes x C d hc p q (deg p (sub hp)) (deg q (sub hq)) (by
    intro i hi
    have hh := (Finset.mem_filter.mp (show i ∈ Finset.univ.filter _ from hi)).2
    exact (hh p hp).trans (hh q hq).symm))

/-- For a graph of selected polynomials over seeds, the evaluation constraint
    is linear on the joint space of a polynomial and its seed. A common match
    on d+1 distinct nodes forces the full subset onto a single affine pencil. -/
theorem moving (x : I ↪ K) (u v : I → K) (a d b k : ℕ)
    (hda : d<a) (han : a≤Fintype.card I) (hb : 1≤b)
    (S : Finset (K[X] × K)) (rk : rank K S ≤ k)
    (uniqueSeed : Set.InjOn Prod.snd (↑S : Set (K[X] × K)))
    (deg : ∀ z ∈ S, z.1.natDegree ≤ d)
    (ag : ∀ z ∈ S, a ≤ (Finset.univ.filter (fun i => z.1.eval (x i)=u i+z.2*v i)).card)
    (pencil : ∀ P Q : K[X], P.natDegree ≤ d → Q.natDegree ≤ d →
      (S.filter (fun z => z.1=P+Polynomial.C z.2*Q)).card ≤ b) :
    S.card ≤ cap (Fintype.card I) a d b k := by
  classical
  let f (i : I) : (K[X] × K) →ₗ[K] K :=
    (Polynomial.leval (x i)).comp (LinearMap.fst K K[X] K) -
      v i • LinearMap.snd K K[X] K
  have iff_match (i : I) (z : K[X] × K) : f i z = u i ↔ z.1.eval (x i)=u i+z.2*v i := by
    change z.1.eval (x i) - v i * z.2 = u i ↔ _
    rw [mul_comm (v i), sub_eq_iff_eq_add]
  apply slice f u a d b hda han k S rk
  · intro z hz
    simpa only [iff_match] using ag z hz
  intro T sub large
  let E := Finset.univ.filter (fun i => ∀ z ∈ T, f i z = u i)
  change E.card ≤ d
  by_contra! hc
  obtain ⟨r,hr,t,ht,ne⟩ := Finset.one_lt_card.mp (lt_of_le_of_lt hb large)
  have hseed : t.2-r.2 ≠ 0 := sub_ne_zero.mpr (fun eq => ne (uniqueSeed (sub hr) (sub ht) eq.symm))
  let Q := Polynomial.C (t.2-r.2)⁻¹*(t.1-r.1)
  let P := r.1-Polynomial.C r.2*Q
  have hQ : Q.natDegree ≤ d := (Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_sub_le _ _).trans (max_le (deg t (sub ht)) (deg r (sub hr))))
  have hP : P.natDegree ≤ d := (Polynomial.natDegree_sub_le _ _).trans
    (max_le (deg r (sub hr)) ((Polynomial.natDegree_C_mul_le _ _).trans hQ))
  have fit : T ⊆ S.filter (fun z => z.1=P+Polynomial.C z.2*Q) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨sub hz, eq_of_nodes x E d hc _ _ (deg z (sub hz))
      ((Polynomial.natDegree_add_le _ _).trans (max_le hP ((Polynomial.natDegree_C_mul_le _ _).trans hQ))) ?_⟩
    intro i hi
    have ev (s : K[X] × K) (hs : s ∈ T) : s.1.eval (x i)=u i+s.2*v i :=
      (iff_match i s).mp ((Finset.mem_filter.mp hi).2 s hs)
    simp only [P,Q,eval_add,eval_sub,eval_mul,eval_C,ev z hz,ev r hr,ev t ht]
    field_simp
    ring
  exact large.not_ge ((Finset.card_le_card fit).trans (pencil P Q hP hQ))

#print axioms slice
#print axioms scalar
#print axioms moving
end
end Frontier.Pruning
