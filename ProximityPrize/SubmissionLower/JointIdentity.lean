import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace JointIdentity
open Polynomial Finset
open scoped Classical
noncomputable section
variable {K I : Type*} [Field K] [DecidableEq K] [DecidableEq I]

def missed (nodes : Finset I) (x : I ↪ K) (u v : I → K) (sel : K → K[X]) (g : K) :=
  nodes.filter (fun i => (sel g).eval (x i) ≠ u i + g * v i)

theorem three_seed_pencil (S : Finset K) (nodes : Finset I) (x : I ↪ K)
    (u v : I → K) (sel : K → K[X]) (w k : ℕ) (many : w+3*k < nodes.card)
    (degree : ∀ g ∈ S, (sel g).natDegree ≤ w)
    (few : ∀ g ∈ S, (missed nodes x u v sel g).card ≤ k)
    (size : 1 < S.card) :
    ∃ P Q : K[X], P.natDegree ≤ w ∧ Q.natDegree ≤ w ∧
      ∀ g ∈ S, sel g = P+C g*Q := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp size
  let Q := C (b-a)⁻¹ * (sel b - sel a)
  let P := sel a - C a * Q
  have hQ : Q.natDegree ≤ w :=
    (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_sub_le _ _).trans
      (max_le (degree b hb) (degree a ha)))
  have hP : P.natDegree ≤ w :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (degree a ha)
      ((Polynomial.natDegree_C_mul_le _ _).trans hQ))
  refine ⟨P,Q,hP,hQ,?_⟩
  intro g hg
  let bad := fun z => missed nodes x u v sel z
  let discard := (bad a ∪ bad b) ∪ bad g
  let keep := nodes \ discard
  have bound : discard.card ≤ 3*k := by
    have h1 := Finset.card_union_le (bad a) (bad b)
    have h2 := Finset.card_union_le (bad a ∪ bad b) (bad g)
    have A := few a ha
    have B := few b hb
    have G := few g hg
    change (bad a).card ≤ k at A
    change (bad b).card ≤ k at B
    change (bad g).card ≤ k at G
    dsimp only [discard]
    omega
  have enough : w < keep.card := by
    have hh := Finset.le_card_sdiff discard nodes
    change nodes.card-discard.card ≤ keep.card at hh
    omega
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (f := fun i : keep => x i.val)
    (x.injective.comp Subtype.val_injective)
  · intro i
    obtain ⟨hi,hno⟩ := Finset.mem_sdiff.mp i.property
    have clean (z : K) (h : i.val ∉ bad z) : (sel z).eval (x i.val) = u i.val+z*v i.val := by
      by_contra ne
      exact h (Finset.mem_filter.mpr ⟨hi,ne⟩)
    have ca := clean a (fun h => hno (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
    have cb := clean b (fun h => hno (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
    have cg := clean g (fun h => hno (Finset.mem_union_right _ h))
    have dn : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
    simp only [P,Q,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,ca,cb,cg]
    field_simp
    ring
  · rw [Fintype.card_coe]
    exact lt_of_le_of_lt (max_le (degree g hg) ((Polynomial.natDegree_add_le _ _).trans
      (max_le hP ((Polynomial.natDegree_C_mul_le _ _).trans hQ)))) enough

theorem many_identities (S : Finset K) (nodes : Finset I) (x : I ↪ K)
    (u v : I → K) (sel : K → K[X]) (w e k D : ℕ) (many : w+3*k < nodes.card)
    (degree : ∀ g ∈ S, (sel g).natDegree ≤ w)
    (fiber : ∀ i ∈ nodes, (S.filter (fun g => (sel g).eval (x i) ≠ u i + g*v i)).card ≤ D)
    (line : ∀ P Q : K[X], P.natDegree ≤ w → Q.natDegree ≤ w →
      (S.filter (fun g => sel g = P+C g*Q)).card ≤ e+1) :
    S.card ≤ nodes.card * D / (k+1) + (e+1) := by
  let good := S.filter (fun g => (missed nodes x u v sel g).card ≤ k)
  let bad := S \ good
  have bnd : bad.card*(k+1) ≤ nodes.card*D := by
    apply (show (bad.card • (k+1 : ℕ) ≤ nodes.card • D) → _ by simp only [nsmul_eq_mul, Nat.cast_id, imp_self])
    apply Finset.card_nsmul_le_card_nsmul (R := ℕ) (s := bad) (t := nodes) (fun g i => (sel g).eval (x i) ≠ u i + g*v i)
    · intro g hg
      obtain ⟨hs,hn⟩ := Finset.mem_sdiff.mp hg
      change k+1 ≤ (missed nodes x u v sel g).card
      by_contra! h
      exact hn (Finset.mem_filter.mpr ⟨hs,by omega⟩)
    · intro i hi
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.sdiff_subset : bad ⊆ S))).trans (fiber i hi)
  have hbad : bad.card ≤ nodes.card*D/(k+1) := (Nat.le_div_iff_mul_le (Nat.succ_pos k)).mpr bnd
  have hgood : good.card ≤ e+1 := by
    by_cases hs : 1 < good.card
    · obtain ⟨P,Q,hP,hQ,fit⟩ := three_seed_pencil good nodes x u v sel w k many
        (fun g h => degree g (Finset.mem_filter.mp h).1) (fun _ h => (Finset.mem_filter.mp h).2) hs
      apply (Finset.card_le_card (t := S.filter (fun g => sel g=P+C g*Q)) ?_).trans (line P Q hP hQ)
      intro g hg
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,fit g hg⟩
    · omega
  have eq : bad.card = S.card-good.card := Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
  omega

def tolerance (w a : ℕ) := (a-w-1)/4
def splitPoint (w a : ℕ) := w+3*tolerance w a

#print axioms many_identities
end
end JointIdentity
