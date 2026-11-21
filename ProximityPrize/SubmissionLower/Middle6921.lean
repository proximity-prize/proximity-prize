import ProximityPrize.SubmissionLower.ColumnRank6921
import ProximityPrize.SubmissionLower.Fast003
import ProximityPrize.SubmissionLower.Fast005
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Fast054
import ProximityPrize.SubmissionLower.Fast067
import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.Fast072
import ProximityPrize.SubmissionLower.Fast074
import ProximityPrize.SubmissionLower.Fast076
import ProximityPrize.SubmissionLower.Fast077
import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Growth6921
import ProximityPrize.SubmissionLower.Pruning6921
import ProximityPrize.SubmissionLower.RankCases6921
set_option Elab.async false

/- Profile transport of Dadon's PR 627. -/
section Port_K1_2SharedIncidence
set_option autoImplicit true
set_option autoImplicit false

/-! One fixed punctured input counts all exact-error strata together.
No partition or varying-own-radius premise is hidden in these consumers. -/
namespace K21_2.Mixed
noncomputable section
open Finset
open scoped BigOperators
variable {α σ : Type*} [DecidableEq α] [DecidableEq σ]
local instance decShared (P : Prop) : Decidable P := Classical.propDecidable P

/-- The child bound is for the UNION of parent slopes incident to a
fixed removed set. Exact-error weight may vary with the parent slope. -/
theorem shared_child_incidence (D : Finset α) (Γ : Finset σ)
    (incident : α → σ → Prop) (beta child : ℕ)
    (hparent : ∀ γ∈Γ,beta ≤ (D.filter (fun I => incident I γ)).card)
    (hchild : ∀ I∈D,(Γ.filter (fun γ => incident I γ)).card ≤ child) :
    beta*Γ.card ≤ D.card*child := by
  classical
  have hswap : (∑ γ∈Γ,(D.filter (fun I => incident I γ)).card) =
      ∑ I∈D,(Γ.filter (fun γ => incident I γ)).card := by
    simp only [card_eq_sum_ones,sum_filter]
    rw [sum_comm]
  calc
    beta*Γ.card = ∑ _γ∈Γ,beta := by simp [Nat.mul_comm]
    _ ≤ ∑ γ∈Γ,(D.filter (fun I => incident I γ)).card := sum_le_sum hparent
    _ = ∑ I∈D,(Γ.filter (fun γ => incident I γ)).card := hswap
    _ ≤ ∑ _I∈D,child := sum_le_sum hchild
    _ = D.card*child := by simp

theorem shared_removed_set_incidence (nodes : Finset α) (Γ : Finset σ)
    (d beta child : ℕ) (incident : Finset α → σ → Prop)
    (hparent : ∀ γ∈Γ,beta ≤
      ((nodes.powersetCard d).filter (fun I => incident I γ)).card)
    (hchild : ∀ I∈nodes.powersetCard d,
      (Γ.filter (fun γ => incident I γ)).card ≤ child) :
    beta*Γ.card ≤ nodes.card.choose d*child := by
  simpa only [card_powersetCard] using
    shared_child_incidence (nodes.powersetCard d) Γ incident beta child hparent hchild

/-- Multiplying by a denominator preserves a RATIONAL child price,
avoiding a separate ceiling per removed set. -/
theorem shared_child_rational_incidence (D : Finset α) (Γ : Finset σ)
    (incident : α → σ → Prop) (beta numerator denominator : ℕ)
    (hparent : ∀ γ∈Γ,beta ≤ (D.filter (fun I => incident I γ)).card)
    (hchild : ∀ I∈D,denominator*(Γ.filter (fun γ => incident I γ)).card ≤ numerator) :
    denominator*beta*Γ.card ≤ D.card*numerator := by
  classical
  have hswap : (∑ γ∈Γ,(D.filter (fun I => incident I γ)).card) =
      ∑ I∈D,(Γ.filter (fun γ => incident I γ)).card := by
    simp only [card_eq_sum_ones,sum_filter]
    rw [sum_comm]
  have hlow : beta*Γ.card ≤ ∑ γ∈Γ,(D.filter (fun I => incident I γ)).card := by
    calc
      beta*Γ.card = ∑ _γ∈Γ,beta := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum hparent
  calc
    denominator*beta*Γ.card = denominator*(beta*Γ.card) := by ring
    _ ≤ denominator*(∑ γ∈Γ,(D.filter (fun I => incident I γ)).card) :=
      Nat.mul_le_mul_left denominator hlow
    _ = ∑ I∈D,denominator*(Γ.filter (fun γ => incident I γ)).card := by
      rw [hswap,mul_sum]
    _ ≤ ∑ _I∈D,numerator := sum_le_sum hchild
    _ = D.card*numerator := by simp

end
end K21_2.Mixed
end Port_K1_2SharedIncidence

section Port_K1_2BetaMinimum
set_option autoImplicit true
set_option autoImplicit false

namespace K21_2.Mixed
open Nat

def deletionBeta (T A v c u : ℕ) : ℕ :=
  (T-u).choose (v-u+c)*(A+u-1).choose (u+c)

/-- The product, rather than every consecutive ratio, is bounded below
by its u=0 value. No native finite enumeration is used. -/
theorem deletionBeta_zero_le (T A v c u : ℕ) (hAT : T≤A)
    (hu : u≤v) (hfit : v+c≤T) :
    deletionBeta T A v c 0 ≤ deletionBeta T A v c u := by
  by_cases hu0 : u=0
  · subst u; rfl
  have huT : u≤T := by omega
  have hA : 0<A := by omega
  have hm1 : (T.choose u)*(u+c).choose u > 0 :=
    Nat.mul_pos (Nat.choose_pos huT) (Nat.choose_pos (by omega))
  have hcmp1 : (u+c).choose u ≤ (v+c).choose u :=
    Nat.choose_le_choose u (by omega)
  have hcmp2 : T.choose u ≤ (A+u-1).choose u :=
    Nat.choose_le_choose u (by omega)
  have hT := Nat.choose_mul (n:=T) (k:=v+c) (s:=u) (by omega)
  have hB := Nat.choose_mul (n:=A+u-1) (k:=u+c) (s:=u) (by omega)
  have he1 : v+c-u=v-u+c := by omega
  have he2 : A+u-1-u=A-1 := by omega
  have he3 : u+c-u=c := by omega
  rw [he1] at hT
  rw [he2,he3] at hB
  apply Nat.le_of_mul_le_mul_right (c := (T.choose u)*(u+c).choose u) ?_ hm1
  calc
    deletionBeta T A v c 0*((T.choose u)*(u+c).choose u) ≤
        deletionBeta T A v c 0*((v+c).choose u*(A+u-1).choose u) :=
      Nat.mul_le_mul_left _ (by simpa only [Nat.mul_comm] using Nat.mul_le_mul hcmp1 hcmp2)
    _ = deletionBeta T A v c u*((T.choose u)*(u+c).choose u) := by
      simp only [deletionBeta,Nat.sub_zero,Nat.add_zero,Nat.zero_add]
      calc
        T.choose (v+c)*(A-1).choose c*((v+c).choose u*(A+u-1).choose u) =
            (T.choose (v+c)*(v+c).choose u)*
              ((A+u-1).choose u*(A-1).choose c) := by ring
        _ = (T.choose u*(T-u).choose (v-u+c))*
              ((A+u-1).choose (u+c)*(u+c).choose u) := by rw [hT,←hB]
        _ = _ := by ring

end K21_2.Mixed
end Port_K1_2BetaMinimum

section Port_K1_2_4Projection
set_option autoImplicit true
set_option autoImplicit false

/-! Verbatim R5Bez projection-resultant argument, repackaged with a direct
Mathlib root bound to avoid importing the unrelated old campaign tree.
Provenance: moonshots/r5/leanM/src/R5Bez.lean (existing theorem).
This counts DISTINCT first coordinates, as required by gamma -> (gamma,gamma^p). -/
namespace K21_2_4
open Polynomial Finset

variable {F : Type*} [Field F]

theorem natDegree_det_le_col {R : Type*} [CommRing R] {k : ℕ} (M : Matrix (Fin k) (Fin k) R[X]) (d : Fin k → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ d j) : M.det.natDegree ≤ ∑ j, d j := by
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [Units.smul_def]
  refine (natDegree_smul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  exact Finset.sum_le_sum fun i _ => hM _ _

theorem resultant_natDegree_le {R : Type*} [CommRing R] (f g : Polynomial (Polynomial R)) (m n df dg : ℕ)
    (hdf : ∀ k, (f.coeff k).natDegree ≤ df) (hdg : ∀ k, (g.coeff k).natDegree ≤ dg) :
    (resultant f g m n).natDegree ≤ m * dg + n * df := by
  unfold resultant
  have h := natDegree_det_le_col (sylvester f g m n) (fun j => if (j : ℕ) < m then dg else df) ?_
  · refine h.trans (le_of_eq ?_)
    rw [Fin.sum_univ_add]
    simp [Finset.sum_const, Finset.card_univ]
  · intro i j
    induction j using Fin.addCases with
    | left j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left, Fin.val_castAdd, j₁.isLt, ↓reduceIte]
      split_ifs
      · exact hdg _
      · simp
    | right j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right, Fin.val_natAdd,
        show ¬ (m + (j₁ : ℕ) < m) by omega, ↓reduceIte]
      split_ifs
      · exact hdf _
      · simp

open Classical in
theorem bez_proj (f g : Polynomial (Polynomial F)) (m n df dg : ℕ) (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n)
    (hmn : m ≠ 0 ∨ n ≠ 0) (hdf : ∀ k, (f.coeff k).natDegree ≤ df) (hdg : ∀ k, (g.coeff k).natDegree ≤ dg)
    (hres : resultant f g m n ≠ 0) (Γ : Finset F)
    (hΓ : ∀ β ∈ Γ, ∃ ρ : F, (f.map (evalRingHom β)).eval ρ = 0 ∧ (g.map (evalRingHom β)).eval ρ = 0) :
    Γ.card ≤ m * dg + n * df := by
  obtain ⟨p, q, _, _, e⟩ := exists_mul_add_mul_eq_C_resultant f g (m := m) (n := n) hfm hgn hmn
  have hroot : ∀ β ∈ Γ, (resultant f g m n).eval β = 0 := by
    intro β hβ
    obtain ⟨ρ, hf0, hg0⟩ := hΓ β hβ
    have e2 := congrArg (fun P => (P.map (evalRingHom β)).eval ρ) e
    simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hf0, hg0, zero_mul, add_zero,
      Polynomial.map_C, eval_C] at e2
    rw [coe_evalRingHom] at e2
    exact e2.symm
  calc Γ.card = (Γ.filter fun β => (resultant f g m n).eval β = 0).card := by
        rw [Finset.filter_true_of_mem hroot]
    _ ≤ (resultant f g m n).natDegree := by
      by_contra h
      apply hres
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Γ
      · intro β hβ
        exact hroot β hβ
      · simpa only [Finset.filter_true_of_mem hroot] using (Nat.lt_of_not_ge h)
    _ ≤ m * dg + n * df := resultant_natDegree_le f g m n df dg hdf hdg

theorem resultant_ne_zero_of_coprime (f g : Polynomial (Polynomial F))
    (hcop : IsCoprime (f.map (algebraMap F[X] (FractionRing F[X]))) (g.map (algebraMap F[X] (FractionRing F[X])))) :
    resultant f g ≠ 0 := by
  have hinj : Function.Injective (algebraMap F[X] (FractionRing F[X])) := IsFractionRing.injective F[X] (FractionRing F[X])
  have h := Polynomial.resultant_ne_zero _ _ hcop
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj, resultant_map_map] at h
  intro h0
  apply h
  rw [h0, map_zero]

/-- bidegree Bezout on P¹ × P¹, counted over distinct β -/
theorem bez_proj_coprime (f g : Polynomial (Polynomial F)) (df dg : ℕ)
    (hdf : ∀ k, (f.coeff k).natDegree ≤ df) (hdg : ∀ k, (g.coeff k).natDegree ≤ dg)
    (hcop : IsCoprime (f.map (algebraMap F[X] (FractionRing F[X]))) (g.map (algebraMap F[X] (FractionRing F[X]))))
    (hpos : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0) (Γ : Finset F)
    (hΓ : ∀ β ∈ Γ, ∃ ρ : F, (f.map (evalRingHom β)).eval ρ = 0 ∧ (g.map (evalRingHom β)).eval ρ = 0) :
    Γ.card ≤ f.natDegree * dg + g.natDegree * df :=
  bez_proj f g f.natDegree g.natDegree df dg le_rfl le_rfl hpos hdf hdg (resultant_ne_zero_of_coprime f g hcop) Γ hΓ

end K21_2_4
end Port_K1_2_4Projection

section Port_K1_2BadDeletion
set_option autoImplicit true
set_option autoImplicit false

/-! Good-node deletions of the SAME nonjoint support. The lower bound is
sharp; it does not choose an unrelated decoder after puncturing. -/
namespace K21_2.Mixed
open FrobeniusLocator
open FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
variable {F ι : Type} [Field F] [DecidableEq ι]
local instance decProp (P : Prop) : Decidable P := Classical.propDecidable P

def JointOn (x u v : ι → F) (k : ℕ) (S : Finset ι) : Prop :=
  ExtendsOn x u k S ∧ ExtendsOn x v k S

theorem deletion_intersection_large (S J J' : Finset ι) (k j : ℕ)
    (hsize : k+2*j ≤ S.card) (hJ : J.card=j) (hJ' : J'.card=j) :
    k ≤ ((S\J) ∩ (S\J')).card := by
  have hcover : S ⊆ ((S\J) ∩ (S\J')) ∪ J ∪ J' := by
    intro i hi
    by_cases h : i∈J
    · exact mem_union_left _ (mem_union_right _ h)
    · by_cases h' : i∈J'
      · exact mem_union_right _ h'
      · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr
          ⟨mem_sdiff.mpr ⟨hi,h⟩,mem_sdiff.mpr ⟨hi,h'⟩⟩))
  have hc := card_le_card hcover
  have h1 := card_union_le (((S\J) ∩ (S\J')) ∪ J) J'
  have h2 := card_union_le ((S\J) ∩ (S\J')) J
  omega

theorem polynomial_unique_on_deletions (x : ι → F) (hx : Function.Injective x)
    (u : ι → F) (k j : ℕ) (S J J' : Finset ι)
    (hsize : k+2*j ≤ S.card) (hJ : J.card=j) (hJ' : J'.card=j)
    (P Q : F[X]) (hP : P.degree<k) (hQ : Q.degree<k)
    (hPv : ∀ i∈S\J,P.eval (x i)=u i)
    (hQv : ∀ i∈S\J',Q.eval (x i)=u i) : P=Q := by
  have hcard := deletion_intersection_large S J J' k j hsize hJ hJ'
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq ((S\J) ∩ (S\J'))
    (fun a _ b _ hab => hx hab)
    (hP.trans_le (by exact_mod_cast hcard))
    (hQ.trans_le (by exact_mod_cast hcard))
  intro i hi
  exact (hPv i (mem_inter.mp hi).1).trans (hQv i (mem_inter.mp hi).2).symm

/-- If one retained set is jointly explained, every other such set has
the SAME explaining polynomial pair. -/
theorem joint_deletions_same_pair (x : ι → F) (hx : Function.Injective x)
    (u v : ι → F) (k j : ℕ) (S J J' : Finset ι)
    (hsize : k+2*j ≤ S.card) (hJ : J.card=j) (hJ' : J'.card=j)
    (P0 P1 Q0 Q1 : F[X])
    (hP0 : P0.degree<k) (hP1 : P1.degree<k)
    (hQ0 : Q0.degree<k) (hQ1 : Q1.degree<k)
    (hPv0 : ∀ i∈S\J,P0.eval (x i)=u i)
    (hPv1 : ∀ i∈S\J,P1.eval (x i)=v i)
    (hQv0 : ∀ i∈S\J',Q0.eval (x i)=u i)
    (hQv1 : ∀ i∈S\J',Q1.eval (x i)=v i) : P0=Q0 ∧ P1=Q1 :=
  ⟨polynomial_unique_on_deletions x hx u k j S J J' hsize hJ hJ' P0 Q0 hP0 hQ0 hPv0 hQv0,
   polynomial_unique_on_deletions x hx v k j S J J' hsize hJ hJ' P1 Q1 hP1 hQ1 hPv1 hQv1⟩

/-- At least choose(B-1,j) agreement-node deletions retain nonjointness,
provided B-2j>=k. Both polynomial degrees remain <k. -/
theorem bad_good_deletion_count (x : ι → F) (hx : Function.Injective x)
    (u v : ι → F) (k j : ℕ) (S : Finset ι)
    (hsize : k+2*j ≤ S.card) (hbad : ¬JointOn x u v k S) :
    (S.card-1).choose j ≤
      ((S.powersetCard j).filter (fun J => ¬JointOn x u v k (S\J))).card := by
  classical
  by_cases hex : ∃ J∈S.powersetCard j,JointOn x u v k (S\J)
  · obtain ⟨J0,hJ0,⟨P0,hP0,hPv0⟩,⟨P1,hP1,hPv1⟩⟩ := hex
    obtain ⟨i,hi,hfail⟩ : ∃ i∈S,P0.eval (x i)≠u i ∨ P1.eval (x i)≠v i := by
      by_contra hn
      push Not at hn
      exact hbad ⟨⟨P0,hP0,fun i hi => (hn i hi).1⟩,
        ⟨P1,hP1,fun i hi => (hn i hi).2⟩⟩
    have hsub : (S.erase i).powersetCard j ⊆
        (S.powersetCard j).filter (fun J => ¬JointOn x u v k (S\J)) := by
      intro J hJ
      obtain ⟨hJS,hJcard⟩ := mem_powersetCard.mp hJ
      apply mem_filter.mpr
      refine ⟨mem_powersetCard.mpr ⟨hJS.trans (erase_subset _ _),hJcard⟩,?_⟩
      rintro ⟨⟨Q0,hQ0,hQv0⟩,⟨Q1,hQ1,hQv1⟩⟩
      obtain ⟨h0,h1⟩ := joint_deletions_same_pair x hx u v k j S J0 J
        hsize (mem_powersetCard.mp hJ0).2 hJcard P0 P1 Q0 Q1
        hP0 hP1 hQ0 hQ1 hPv0 hPv1 hQv0 hQv1
      have hiJ : i∉J := fun h => (notMem_erase i S) (hJS h)
      have hi' : i∈S\J := mem_sdiff.mpr ⟨hi,hiJ⟩
      rcases hfail with h | h
      · exact h (h0 ▸ hQv0 i hi')
      · exact h (h1 ▸ hQv1 i hi')
    have hc := card_le_card hsub
    simpa only [card_powersetCard,card_erase_of_mem hi] using hc
  · have heq : (S.powersetCard j).filter (fun J => ¬JointOn x u v k (S\J)) =
        S.powersetCard j := by
      apply filter_eq_self.mpr
      intro J hJ hj
      exact hex ⟨J,hJ,hj⟩
    rw [heq,card_powersetCard]
    exact Nat.choose_le_choose j (Nat.sub_le _ _)

end
end K21_2.Mixed
end Port_K1_2BadDeletion

section Port_K1_2MixedDeletions
set_option autoImplicit true
set_option autoImplicit false

namespace K21_2.Mixed
noncomputable section
open Finset
variable {F ι : Type} [Field F] [DecidableEq ι]
local instance decMixed (P : Prop) : Decidable P := Classical.propDecidable P

theorem disjoint_union_pair_injective (E S : Finset ι) (hES : Disjoint E S)
    (p q : Finset ι × Finset ι)
    (hpE : p.1⊆E) (hpS : p.2⊆S) (hqE : q.1⊆E) (hqS : q.2⊆S)
    (heq : p.1∪p.2=q.1∪q.2) : p=q := by
  have hd : ∀ i∈E,i∉S := fun i hi => (disjoint_left.mp hES hi)
  have hfirst : p.1=q.1 := by
    ext i
    constructor
    · intro hi
      have hm : i∈q.1∪q.2 := heq ▸ mem_union_left _ hi
      exact (mem_union.mp hm).resolve_right (fun h => hd i (hpE hi) (hqS h))
    · intro hi
      have hm : i∈p.1∪p.2 := heq.symm ▸ mem_union_left _ hi
      exact (mem_union.mp hm).resolve_right (fun h => hd i (hqE hi) (hpS h))
  have hsecond : p.2=q.2 := by
    ext i
    constructor
    · intro hi
      have hm : i∈q.1∪q.2 := heq ▸ mem_union_right _ hi
      exact (mem_union.mp hm).resolve_left (fun h => hd i (hqE h) (hpS hi))
    · intro hi
      have hm : i∈p.1∪p.2 := heq.symm ▸ mem_union_right _ hi
      exact (mem_union.mp hm).resolve_left (fun h => hd i (hpE h) (hqS hi))
  exact Prod.ext hfirst hsecond

def goodDeletions (x u v : ι→F) (k j : ℕ) (S : Finset ι) : Finset (Finset ι) :=
  (S.powersetCard j).filter (fun J => ¬JointOn x u v k (S\J))

def mixedDeletions (x u v : ι→F) (k b j : ℕ) (E S : Finset ι) : Finset (Finset ι) :=
  ((E.powersetCard b).product (goodDeletions x u v k j S)).image (fun p => p.1∪p.2)

theorem mixedDeletions_card (x u v : ι→F) (k b j : ℕ) (E S : Finset ι)
    (hES : Disjoint E S) :
    (mixedDeletions x u v k b j E S).card =
      E.card.choose b*(goodDeletions x u v k j S).card := by
  unfold mixedDeletions
  rw [card_image_of_injOn]
  · simp only [Finset.product_eq_sprod,Finset.card_product,card_powersetCard]
  intro p hp q hq heq
  obtain ⟨hpE,hpS⟩ := mem_product.mp hp
  obtain ⟨hqE,hqS⟩ := mem_product.mp hq
  apply disjoint_union_pair_injective E S hES p q
    (mem_powersetCard.mp hpE).1
    (mem_powersetCard.mp (mem_filter.mp hpS).1).1
    (mem_powersetCard.mp hqE).1
    (mem_powersetCard.mp (mem_filter.mp hqS).1).1 heq

theorem mixedDeletions_lower_bound (x u v : ι→F) (hx : Function.Injective x)
    (k b j : ℕ) (E S : Finset ι) (hES : Disjoint E S)
    (hsize : k+2*j≤S.card) (hbad : ¬JointOn x u v k S) :
    E.card.choose b*(S.card-1).choose j ≤
      (mixedDeletions x u v k b j E S).card := by
  rw [mixedDeletions_card x u v k b j E S hES]
  exact Nat.mul_le_mul_left _ (bad_good_deletion_count x hx u v k j S hsize hbad)

theorem mixedDeletions_spec (x u v : ι→F) (k b j : ℕ) (E S I : Finset ι)
    (hES : Disjoint E S) (hI : I∈mixedDeletions x u v k b j E S) :
    I⊆E∪S ∧ I.card=b+j ∧ (S\I).card=S.card-j ∧
      ¬JointOn x u v k (S\I) := by
  obtain ⟨⟨B,J⟩,hmem,rfl⟩ := mem_image.mp hI
  obtain ⟨hB,hJ⟩ := mem_product.mp hmem
  obtain ⟨hBE,hBc⟩ := mem_powersetCard.mp hB
  obtain ⟨hJS,hJc⟩ := mem_powersetCard.mp (mem_filter.mp hJ).1
  have hd : Disjoint B J := hES.mono hBE hJS
  have hremain : S\(B∪J)=S\J := by
    ext i
    simp only [mem_sdiff,mem_union,not_or]
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · intro h
      exact ⟨h.1,fun hi => disjoint_left.mp hES (hBE hi) h.1,h.2⟩
  refine ⟨union_subset_union hBE hJS,?_,?_,?_⟩
  · rw [card_union_of_disjoint hd,hBc,hJc]
  · rw [hremain,card_sdiff_of_subset hJS,hJc]
  · rw [hremain]
    exact (mem_filter.mp hJ).2

end
end K21_2.Mixed
end Port_K1_2MixedDeletions

section Port_K1_2SharedMixedCount
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! This is the complete finite shared-deletion argument. Its remaining
child-price premise is explicit, and is not a native geometric theorem. -/
namespace K21_2.Mixed
noncomputable section
open Finset
variable {F ι : Type} [Field F] [DecidableEq F] [DecidableEq ι]
local instance decSharedMixed (P : Prop) : Decidable P := Classical.propDecidable P

theorem shared_mixed_rational_count (x u v : ι→F) (hx : Function.Injective x)
    (nodes : Finset ι) (Γ : Finset F) (k A T vcount c numerator denominator : ℕ)
    (S E : F→Finset ι) (U : F→ℕ)
    (hAT : T≤A) (hfit : vcount+c≤T) (hguard : k+vcount+2*c≤A)
    (hwitness : ∀ γ∈Γ, U γ≤vcount ∧ (S γ).card=A+U γ ∧
      (E γ).card=T-U γ ∧ Disjoint (E γ) (S γ) ∧ E γ∪S γ⊆nodes ∧
      ¬JointOn x u v k (S γ))
    (hchild : ∀ I∈nodes.powersetCard (vcount+2*c),
      denominator*(Γ.filter (fun γ =>
        I∈mixedDeletions x u v k (vcount-U γ+c) (U γ+c) (E γ) (S γ))).card≤numerator) :
    denominator*(T.choose (vcount+c)*(A-1).choose c)*Γ.card ≤
      nodes.card.choose (vcount+2*c)*numerator := by
  classical
  let incident : Finset ι→F→Prop := fun I γ =>
    I∈mixedDeletions x u v k (vcount-U γ+c) (U γ+c) (E γ) (S γ)
  have hparent : ∀ γ∈Γ,T.choose (vcount+c)*(A-1).choose c≤
      ((nodes.powersetCard (vcount+2*c)).filter (fun I => incident I γ)).card := by
    intro γ hγ
    obtain ⟨hU,hS,hE,hES,hsub,hbad⟩ := hwitness γ hγ
    have hsize : k+2*(U γ+c)≤(S γ).card := by rw [hS]; omega
    have hlow := mixedDeletions_lower_bound x u v hx k (vcount-U γ+c) (U γ+c)
      (E γ) (S γ) hES hsize hbad
    rw [hS,hE] at hlow
    have hbeta := deletionBeta_zero_le T A vcount c (U γ) hAT hU hfit
    have hlow' : T.choose (vcount+c)*(A-1).choose c≤
        (mixedDeletions x u v k (vcount-U γ+c) (U γ+c) (E γ) (S γ)).card := by
      have hbeta' : T.choose (vcount+c)*(A-1).choose c≤
          (T-U γ).choose (vcount-U γ+c)*(A+U γ-1).choose (U γ+c) := by
        simpa only [deletionBeta,Nat.sub_zero,Nat.add_zero,Nat.zero_add] using hbeta
      exact hbeta'.trans hlow
    apply hlow'.trans
    apply card_le_card
    intro I hI
    obtain ⟨hIS,hIc,hremain,hbad'⟩ := mixedDeletions_spec x u v k
      (vcount-U γ+c) (U γ+c) (E γ) (S γ) I hES hI
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hIS.trans hsub,by omega⟩,hI⟩
  have hh := shared_child_rational_incidence
    (nodes.powersetCard (vcount+2*c)) Γ incident
    (T.choose (vcount+c)*(A-1).choose c) numerator denominator
    (by
      intro γ hγ
      convert hparent γ hγ using 1 <;> congr 2)
    (by
      intro I hI
      convert hchild I hI using 1
      congr 2
      ext γ
      simp only [mem_filter,incident])
  simpa only [card_powersetCard] using hh

theorem shared_mixed_count_floor (x u v : ι→F) (hx : Function.Injective x)
    (nodes : Finset ι) (Γ : Finset F) (k A T vcount c numerator denominator : ℕ)
    (S E : F→Finset ι) (U : F→ℕ)
    (hAT : T≤A) (hfit : vcount+c≤T) (hguard : k+vcount+2*c≤A)
    (hpositive : 0<denominator*(T.choose (vcount+c)*(A-1).choose c))
    (hwitness : ∀ γ∈Γ, U γ≤vcount ∧ (S γ).card=A+U γ ∧
      (E γ).card=T-U γ ∧ Disjoint (E γ) (S γ) ∧ E γ∪S γ⊆nodes ∧
      ¬JointOn x u v k (S γ))
    (hchild : ∀ I∈nodes.powersetCard (vcount+2*c),
      denominator*(Γ.filter (fun γ =>
        I∈mixedDeletions x u v k (vcount-U γ+c) (U γ+c) (E γ) (S γ))).card≤numerator) :
    Γ.card≤(nodes.card.choose (vcount+2*c)*numerator)/
      (denominator*(T.choose (vcount+c)*(A-1).choose c)) := by
  apply (Nat.le_div_iff_mul_le hpositive).mpr
  simpa only [Nat.mul_comm Γ.card] using shared_mixed_rational_count x u v hx
    nodes Γ k A T vcount c numerator denominator S E U hAT hfit hguard hwitness hchild

end
end K21_2.Mixed
end Port_K1_2SharedMixedCount

section Port_K1_2_4_3Height
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace K21_2_4_3

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator

/-- A coefficient shift translates the moment index by the same amount. -/
private theorem shift_sum {R : Type} [CommRing R] (P : R[X]) (r n j : ℕ)
    (hP : P.natDegree ≤ r) (h : r + j < n) (f : ℕ → R) :
    (∑ i : Fin n, (P * Polynomial.X ^ j).coeff i.val * f i.val) =
      ∑ i : Fin (r + 1), P.coeff i.val * f (i.val + j) := by
  let g (i : ℕ) := (P * Polynomial.X ^ j).coeff i * f i
  change (∑ i : Fin n, g i.val) = _
  rw [Fin.sum_univ_eq_sum_range g n,
    Fin.sum_univ_eq_sum_range (fun i => P.coeff i * f (i + j)) (r + 1)]
  have hsplit := Finset.sum_range_add g j (n - j)
  rw [Nat.add_sub_of_le (by omega : j ≤ n)] at hsplit
  rw [hsplit]
  have hzero : (∑ i ∈ range j, g i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [g, Polynomial.coeff_mul_X_pow', Nat.not_le.mpr hi']
  rw [hzero, zero_add]
  symm
  calc
    _ = ∑ i ∈ range (n - j), P.coeff i * f (i + j) := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i _ hi
      have hri : r < i := by simpa [Finset.mem_range] using hi
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt (hP.trans_lt hri)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [g]
      rw [Nat.add_comm j i, Polynomial.coeff_mul_X_pow]

/-- Use the verified shift-minor theorem with the second polynomial set to zero. -/
private theorem single_shift_minors {F : Type} [Field F] (r s : ℕ) (hs : 0 < s)
    (q : Fin (r + 1) → F[X]) (hq : PrimitiveVector.IsPrimitive q)
    (P : F[X][X]) (hP : P.natDegree ≤ r) (hc : ∀ j : Fin (r + 1), P.coeff j.val = q j) :
    let e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
    let W : Matrix (Fin r ⊕ Fin s) (Fin s) F[X] :=
      fun i j => (P * Polynomial.X ^ j.val).coeff (e i).val
    PrimitiveVector.IsPrimitive (K1_6.maximalMinors W) ∧
      ∃ H : ℕ, (∀ j, (q j).natDegree ≤ H) ∧
        (0 < H → ∃ rows : Fin s → Fin r ⊕ Fin s,
          (K1_6.maximalMinors W rows).natDegree = s * H) := by
  classical
  dsimp only
  let B (b : Fin 2) : F[X][X] := if b = 0 then P else 0
  let e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
  let W : Matrix (Fin r ⊕ Fin s) (Fin s) F[X] :=
    fun i j => (P * Polynomial.X ^ j.val).coeff (e i).val
  change PrimitiveVector.IsPrimitive (K1_6.maximalMinors W) ∧ _
  have hdeg : ∀ b, (B b).natDegree ≤ r := by
    intro b
    by_cases hb : b = 0
    · simpa [B, hb] using hP
    · simp [B, hb]
  have hprim : PrimitiveVector.IsPrimitive (K1_6.pairCoordinates B r) := by
    unfold PrimitiveVector.IsPrimitive at hq ⊢
    apply top_unique
    rw [← hq]
    apply Ideal.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨(0, j), by simpa [K1_6.pairCoordinates, B] using hc j⟩
  obtain ⟨hminors, H, hH, rows, hrows⟩ :=
    K1_6_1.proof F r (r + s) s B rfl hs hdeg hprim
  let m := K1_6.maximalMinors (K1_6.shifts B (r + s) s)
  have hproj (J : Fin s → Fin 2 × Fin (r + s)) (hJ : ∀ i, (J i).1 = 0) :
      m J = K1_6.maximalMinors W (fun i => e.symm (J i).2) := by
    unfold m K1_6.maximalMinors
    congr 1
    apply Matrix.ext
    intro i j
    simp [K1_6.shifts, B, hJ i, W]
  have hvanish (J : Fin s → Fin 2 × Fin (r + s)) (i : Fin s) (hi : (J i).1 ≠ 0) :
      m J = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    simp [K1_6.shifts, B, hi]
  refine ⟨?_, H, fun j => ?_, ?_⟩
  · unfold PrimitiveVector.IsPrimitive at hminors ⊢
    apply top_unique
    rw [← hminors]
    apply Ideal.span_le.mpr
    rintro _ ⟨J, rfl⟩
    by_cases hJ : ∀ i, (J i).1 = 0
    · rw [show K1_6.maximalMinors (K1_6.shifts B (r + s) s) J = _ from hproj J hJ]
      exact Ideal.subset_span (Set.mem_range_self _)
    · push Not at hJ
      obtain ⟨i, hi⟩ := hJ
      rw [show K1_6.maximalMinors (K1_6.shifts B (r + s) s) J = 0 from hvanish J i hi]
      exact Ideal.zero_mem _
  · rw [← hc j]
    simpa [B] using hH 0 j.val
  · intro hHpos
    have hJ : ∀ i, (rows i).1 = 0 := by
      by_contra! hJ
      obtain ⟨i, hi⟩ := hJ
      change (m rows).natDegree = s * H at hrows
      rw [hvanish rows i hi, Polynomial.natDegree_zero] at hrows
      exact (Nat.mul_pos hs hHpos).ne' hrows.symm
    exact ⟨fun i => e.symm (rows i).2, (congrArg Polynomial.natDegree (hproj rows hJ)).symm.trans hrows⟩

/-- Keep the same moments while using one more row and one fewer column.
The extra row supplies the additional shift in the sharp height factor. -/
theorem sharp_hankel_height {F : Type} [Field F] (seq : ℕ → F[X]) (r s : ℕ)
    (hs : 0 < s) (hentry : ∀ j, (seq j).natDegree ≤ 1)
    (q : Fin (r + 1) → F[X]) (hq : PrimitiveVector.IsPrimitive q)
    (hker : ∀ i < r + s - 1, ∑ j : Fin (r + 1), seq (i + j.val) * q j = 0)
    (hpivot : (Matrix.of (fun (i j : Fin r) => seq (i.val + j.val))).det ≠ 0) :
    ∃ H : ℕ, (∀ j, (q j).natDegree ≤ H) ∧ s * H ≤ r := by
  classical
  let φ := algebraMap F[X] (GenericLayer.GenericField F)
  have hφ := IsFractionRing.injective F[X] (GenericLayer.GenericField F)
  let e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
  let P := Polynomial.ofFn (r + 1) q
  let W : Matrix (Fin r ⊕ Fin s) (Fin s) F[X] :=
    fun i j => (P * Polynomial.X ^ j.val).coeff (e i).val
  let C : Matrix (Fin r ⊕ Fin s) (Fin r) F[X] :=
    fun i j => seq ((e i).val + j.val)
  have hC (v) (hv : (C.map φ).mulVec v = 0) : v = 0 := by
    let A := Matrix.of (fun (i j : Fin r) => seq (i.val + j.val))
    have hA : (A.map φ).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← φ.map_det]
      exact fun hz => hpivot (hφ (hz.trans (map_zero φ).symm))
    apply Matrix.eq_zero_of_mulVec_eq_zero hA
    funext i
    exact congrFun hv (Sum.inl i)
  have hP : P.natDegree ≤ r :=
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) q)
  have hc (j : Fin (r + 1)) : P.coeff j.val = q j :=
    Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt
  have hWCpoly : W.transpose * C = 0 := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, W, C]
    let f : Fin (r + s) → F[X] :=
      fun k => (P * Polynomial.X ^ i.val).coeff k.val * seq (k.val + j.val)
    change (∑ k : Fin r ⊕ Fin s, f (e k)) = 0
    rw [e.sum_comp f]
    have hi := i.isLt
    have hj := j.isLt
    dsimp only [f]
    have hshift := shift_sum P r (r + s) i.val hP (by omega) (fun k => seq (k + j.val))
    rw [hshift]
    calc
      _ = ∑ k : Fin (r + 1), seq (i.val + j.val + k.val) * q k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hc k, mul_comm, show k.val + i.val + j.val = i.val + j.val + k.val by omega]
      _ = 0 := hker (i.val + j.val) (by omega)
  have hWC : (W.map φ).transpose * (C.map φ) = 0 := by
    have h := congrArg (fun N : Matrix (Fin s) (Fin r) F[X] => N.map φ) hWCpoly
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_zero _ (map_zero φ)] at h
    exact h
  obtain ⟨hprim, H, hH, hrows⟩ := single_shift_minors r s hs q hq P hP hc
  refine ⟨H, hH, ?_⟩
  by_cases hH0 : H = 0
  · simp [hH0]
  obtain ⟨rows, hrows⟩ := hrows (by omega)
  have hbound := K1_6_2.primitive_minor_degree φ hφ C W hWC hC hprim
    (fun _ => 1) (fun _ => le_rfl) (fun i j => hentry ((e i).val + j.val)) rows
  change (K1_6.maximalMinors W rows).natDegree ≤ _ at hbound
  rw [hrows] at hbound
  simpa [Fintype.card_sum] using hbound

end

end K21_2_4_3
end Port_K1_2_4_3Height

section Port_K1_2Defs
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace K21_2
noncomputable section

open Polynomial Matrix Finset FrobeniusLocator
open K21

/-- The branch with two active generators in the low-nullity prefix. -/
def MiddleGuard (u : Words) : Prop :=
  7 ≤ nullity u ∧ nullity u ≤ 16 ∧ firstRank u = 49058 ∧
    ¬ TypeAtMostOne u ∧ ¬ HomogeneousPrincipal u ∧ ¬ ConstantKernel u

def JointOn (u : Words) (S : Finset I) : Prop :=
  ExtendsOn node (u 0) 131072 S ∧ ExtendsOn node (u 1) 131072 S

def BadOn (D : Finset I) (v w : I → K) (γ : K) : Prop :=
  ∃ S : Finset I, S ⊆ D ∧ 180130 ≤ S.card ∧
    ExtendsOn node (fun i => v i + γ * w i) 131072 S ∧
    ¬ (ExtendsOn node v 131072 S ∧ ExtendsOn node w 131072 S)

def ShortenedCap (N cap : ℕ) : Prop :=
  ∀ (D : Finset I), D.card ≤ N → ∀ (v w : I → K) (Γ : Finset K),
    (∀ γ ∈ Γ, BadOn D v w γ) → Γ.card ≤ cap

def padding (r : ℕ) : ℕ :=
  if r = 7 then 2 else if r ≤ 9 then 3 else if r = 10 then 4 else
    if r ≤ 12 then 5 else if r ≤ 14 then 6 else if r = 15 then 7 else 8

def cutoff (r : ℕ) : ℕ := if r = 16 then 3 else 64
def fixedLimit (_r : ℕ) : ℕ := 14678

def reducedHeight (r g : ℕ) : ℕ := 32957 - r - g
def childRows (r : ℕ) : ℕ := 49058 - padding r
def childErrors (r g : ℕ) : ℕ := childRows r + reducedHeight r g
def deletionSize (r : ℕ) : ℕ := r - 1 + 2 * padding r

def rankReserve (r : ℕ) : ℕ := 49058 + 2130706433 * (32957 - r)

def extraReserve (r g : ℕ) : ℕ :=
  let H := reducedHeight r g
  2 * H * ((2130706433 * 49058 + H) / (49058 - H)) +
    (49058 / (49058 - H)) * (2130706433 + 1)

def incidenceDenominator (r g : ℕ) : ℕ :=
  (82014 - g).choose (r - 1 + padding r) * (180130 - 1).choose (padding r)

def incidenceRatio (r g : ℕ) : ℚ :=
  ((262144 - g).choose (deletionSize r) : ℚ) / incidenceDenominator r g

def curveBeta (A a C : ℕ) : ℚ :=
  1 + (A : ℚ) / (a - C + 1 : ℕ)

def ordinaryCore (A a C : ℕ) : ℕ :=
  let d := a - C
  d + (A + d) / (C + 1)

def planeThreshold (A a C : ℕ) : ℕ :=
  (⌈(ordinaryCore A a C : ℚ) / (2 * curveBeta A a C)⌉ : ℤ).toNat - 1

def oldPlanePrice (A a b : ℕ) : ℚ :=
  (A + a + b : ℚ)^2 * b / (a + b : ℚ)

def newPlanePrice (β : ℚ) (A a b : ℕ) : ℚ :=
  2 * β * (b : ℚ)^2 * (A + a + b : ℚ) / (a + b : ℚ)

def planePrice (A a b C : ℕ) : ℚ :=
  let q := planeThreshold A a C
  if b ≤ q then oldPlanePrice A a b
  else min (oldPlanePrice A a b)
    (max (oldPlanePrice A a q) (newPlanePrice (curveBeta A a C) A a b))

def nativePlanePrice (r g : ℕ) : ℚ :=
  planePrice (131072 + childRows r) (childRows r) (reducedHeight r g) (cutoff r)

/-- The full agreement set of a specified decoder on a specified puncture. -/
def goodSet (u : Words) (D : Finset I) (γ : K) (P : K[X]) : Finset I := by
  classical
  exact D.filter fun i => P.eval (node i) = u 0 i + γ * u 1 i

def errorSet (u : Words) (D : Finset I) (γ : K) (P : K[X]) : Finset I :=
  D \ goodSet u D γ P

/-- One family on the complement of the fixed common node roots. -/
structure PaddedFamily (u : Words) (D : Finset I) (Γ : Finset K) (r g : ℕ) where
  decoder : K → K[X]
  slack : K → ℕ
  domain_card : D.card = 262144 - g
  degree : ∀ γ ∈ Γ, (decoder γ).degree < 131072
  witness : ∀ γ ∈ Γ,
    slack γ ≤ r - 1 ∧
    (goodSet u D γ (decoder γ)).card = 180130 + slack γ ∧
    (errorSet u D γ (decoder γ)).card = 82014 - g - slack γ ∧
    ¬ JointOn u (goodSet u D γ (decoder γ))

/-- A single deletion union, with the error and agreement parts determined
by the marked decoder. The agreement part must preserve nonjointness. -/
def mixedChoices (u : Words) (b j : ℕ) (E S : Finset I) : Finset (Finset I) := by
  classical
  exact ((E.powersetCard b).product
    ((S.powersetCard j).filter (fun J => ¬ JointOn u (S \ J)))).image
      (fun pair => pair.1 ∪ pair.2)

def childSlopes {u : Words} {D : Finset I} {Γ : Finset K} {r g : ℕ}
    (F : PaddedFamily u D Γ r g) (J : Finset I) : Finset K := by
  classical
  exact Γ.filter fun γ =>
    J ∈ mixedChoices u (r - 1 - F.slack γ + padding r) (F.slack γ + padding r)
      (errorSet u D γ (F.decoder γ)) (goodSet u D γ (F.decoder γ))

/-- The global reduced relation on the surviving domain. Its polynomial
output has the same X-degree cutoff that applies to the marked decoders. -/
structure ReducedRelation (u : Words) (D : Finset I) (H : ℕ) where
  U : Bivar
  V : Bivar
  output : Bivar
  nonzero : U ≠ 0 ∨ V ≠ 0
  height : max U.natDegree V.natDegree = H
  output_degree : output.degree < (131072 + H : ℕ)
  nodes : relationOn u (Finset.univ \ D) U V output

def RegularAt {u : Words} {D : Finset I} {H : ℕ} (Q : ReducedRelation u D H)
    (γ : K) : Prop :=
  let U := atSlope Q.U γ
  let V := atSlope Q.V γ
  IsCoprime U V ∧ max U.natDegree V.natDegree = H

/-- Seed parameters are independent. The inner polynomial variable belongs
to the ordinary block and the outer one to the conjugated block. -/
def planeMatrix (u : Words) (D : Finset I) (a R : ℕ) :
    Matrix (Fin 2 × Fin a) (Fin (R + 1)) Bivar := fun i j =>
  let x : D → K := fun z => node z.val
  let s (b : Fin 2) := syndrome x (fun z => u b z.val) (i.2.val + j.val)
  if i.1 = 0 then
    Polynomial.C (Polynomial.C (s 0) + Polynomial.X (R := K) * Polynomial.C (s 1))
  else
    Polynomial.C (Polynomial.C (s 0 ^ K21.p)) + Polynomial.X (R := K[X]) * Polynomial.C (Polynomial.C (s 1 ^ K21.p))

def onGraph (γ : K) : Bivar →+* K :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom γ) (γ ^ K21.p)

/-- The locator line has the expected rank both generically on the plane
and at every selected slope. Exact agreement and errors refer to the same
given decoder before any further fixed-root deflation. -/
structure RegularPlane (u : Words) (D : Finset I) (a R : ℕ) (Γ : Finset K)
    (P : K → K[X]) : Prop where
  domain_card : D.card = 131072 + a + R
  generic_rank :
    ((planeMatrix u D a R).map (algebraMap Bivar (FractionRing Bivar))).rank = R
  mark : ∀ γ ∈ Γ, (P γ).degree < 131072 ∧
    (errorSet u D γ (P γ)).card = R ∧
    ¬ JointOn u (goodSet u D γ (P γ)) ∧
    ((planeMatrix u D a R).map (onGraph γ)).rank = R

end
end K21_2
end Port_K1_2Defs

section Port_K1_2_4Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K21_2_4

noncomputable section

open Polynomial FrobeniusLocator
open K21 K21_2

/-- Degree in the inner seed variable. The outer seed degree is natDegree. -/
def seedDegree {F : Type*} [Field F] (Q : F[X][X]) : ℕ :=
  (Polynomial.Bivariate.swap Q).natDegree

def SeedBox {F : Type*} [Field F] (Q : F[X][X]) (s t : ℕ) : Prop :=
  seedDegree Q ≤ s ∧ Q.natDegree ≤ t

/-- Insert a node as a constant in both seed variables. -/
def planeConstant : K →+* Bivar :=
  Polynomial.C.comp Polynomial.C

def nodeEquation (L : Bivar[X]) (i : I) : Bivar :=
  L.eval (planeConstant (node i))

/-- Grid roots fixed at the generic point of a curve. -/
def curveFixed (D : Finset I) (L : Bivar[X]) (Q : Bivar) : Finset I := by
  classical
  exact D.filter (fun i => Q ∣ nodeEquation L i)

theorem mem_curveFixed {D : Finset I} {L : Bivar[X]} {Q : Bivar} {i : I} :
    i ∈ curveFixed D L Q ↔ i ∈ D ∧ Q ∣ nodeEquation L i := by
  classical
  exact Finset.mem_filter

def onCurve (Γ : Finset K) (Q : Bivar) : Finset K := by
  classical
  exact Γ.filter (fun γ => onGraph γ Q = 0)

/-- The same polynomial kernel line on the entire plane and at the selected
points. At every selected point its fiber is the exact error locator of P. -/
structure BoxedLocator (u : Words) (D : Finset I) (a b : ℕ) (Γ : Finset K)
    (P : K → K[X]) (L : Bivar[X]) : Prop where
  degree : L.natDegree ≤ a + b
  kernel : (planeMatrix u D a (a + b)).mulVec (fun j => L.coeff j.val) = 0
  box : ∀ j, SeedBox (L.coeff j) b b
  noFixed : ∀ i ∈ D, nodeEquation L i ≠ 0
  fiber : ∀ γ ∈ Γ, ∃ c : K, c ≠ 0 ∧
    L.map (onGraph γ) = c • locator node (errorSet u D γ (P γ))

/-- The only data needed from the two orientations of the curve cofactors.
Either representative is allowed to vanish identically in X at an
individual selected seed; it must be proper at the generic curve point. -/
structure OppositeCuts (u : Words) (D : Finset I) (Γ : Finset K) (P : K → K[X])
    (Q : Bivar) (a d : ℕ) (i : I) where
  first : Bivar
  second : Bivar
  first_box : SeedBox first (min a d) (d - a)
  second_box : SeedBox second (d - a) (min a d)
  first_proper : ¬ Q ∣ first
  second_proper : ¬ Q ∣ second
  zeros : ∀ γ ∈ Γ, i ∈ errorSet u D γ (P γ) →
    onGraph γ first = 0 ∧ onGraph γ second = 0

end

end K21_2_4
end Port_K1_2_4Defs

section Port_K1_2_4Geometry
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K21_2_4

noncomputable section

open Polynomial Finset FrobeniusLocator ProximityPrize.Benchmark
open K21 K21_2
open scoped BigOperators

section Bidegrees

variable {F : Type*} [Field F]

theorem coeff_coeff_swap (P : F[X][X]) (i j : ℕ) :
    ((Polynomial.Bivariate.swap P).coeff i).coeff j = (P.coeff j).coeff i := by
  classical
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ]
  | monomial n f =>
    induction f using Polynomial.induction_on' with
    | add f g hf hg => simp only [map_add, coeff_add, hf, hg]
    | monomial m c =>
      rw [Polynomial.Bivariate.swap_monomial_monomial]
      by_cases hi : m = i <;> by_cases hj : n = j <;> simp [Polynomial.coeff_monomial, hi, hj]

theorem coeff_natDegree_le_seedDegree (P : F[X][X]) (j : ℕ) :
    (P.coeff j).natDegree ≤ seedDegree P := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [← coeff_coeff_swap]
  have hz : (Polynomial.Bivariate.swap P).coeff i = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt hi
  rw [hz, Polynomial.coeff_zero]

theorem box_coefficients {P : F[X][X]} {a b : ℕ} (h : SeedBox P a b) :
    P.natDegree ≤ b ∧ ∀ j, (P.coeff j).natDegree ≤ a :=
  ⟨h.2, fun j => (coeff_natDegree_le_seedDegree P j).trans h.1⟩

theorem box_sum {ι : Type*} (D : Finset ι) (P : ι→F[X][X]) (a b : ℕ)
    (h : ∀ i∈D,SeedBox (P i) a b) : SeedBox (∑ i∈D,P i) a b := by
  constructor
  · unfold seedDegree
    rw [map_sum]
    apply Polynomial.natDegree_sum_le_of_forall_le
    exact fun i hi => (h i hi).1
  · apply Polynomial.natDegree_sum_le_of_forall_le
    exact fun i hi => (h i hi).2

theorem box_mul_constant (P : F[X][X]) (c : F) (a b : ℕ)
    (h : SeedBox P a b) : SeedBox (P*C (C c)) a b := by
  constructor
  · unfold seedDegree
    rw [map_mul,Polynomial.Bivariate.swap_C_C]
    apply (Polynomial.natDegree_mul_le).trans
    simpa only [natDegree_C,Nat.add_zero,seedDegree] using h.1
  · apply (Polynomial.natDegree_mul_le).trans
    simpa only [natDegree_C,Nat.add_zero] using h.2

theorem box_of_dvd {P Q : F[X][X]} {a b : ℕ} (hP : P ≠ 0)
    (hQP : Q ∣ P) (hbox : SeedBox P a b) : SeedBox Q a b := by
  constructor
  · exact (Polynomial.natDegree_le_of_dvd
      (map_dvd (Polynomial.Bivariate.swap.toRingHom) hQP)
      (by simpa using hP)).trans hbox.1
  · exact (Polynomial.natDegree_le_of_dvd hQP hP).trans hbox.2

theorem curve_coprime_of_irreducible (C P : F[X][X])
    (hC : Irreducible C) (hdeg : C.natDegree ≠ 0) (hproper : ¬ C ∣ P) :
    IsCoprime (C.map (algebraMap F[X] (FractionRing F[X])))
      (P.map (algebraMap F[X] (FractionRing F[X]))) := by
  have hprim : C.IsPrimitive := hC.isPrimitive hdeg
  have hirr : Irreducible (C.map (algebraMap F[X] (FractionRing F[X]))) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := FractionRing F[X])).mp hC
  have hn : ¬ C.map (algebraMap F[X] (FractionRing F[X])) ∣
      P.map (algebraMap F[X] (FractionRing F[X])) := by
    intro hd
    exact hproper (hprim.dvd_of_fraction_map_dvd_fraction_map hd)
  exact (hirr.isCoprime_or_dvd _).resolve_right hn
end Bidegrees

section Factors

variable {F : Type*} [Field F] [NormalizationMonoid F[X][X]]

def factorCurves (P : F[X][X]) : Finset F[X][X] := by
  classical
  exact (UniqueFactorizationMonoid.normalizedFactors P).toFinset

theorem sum_toFinset_le_sum_map {R : Type*} [DecidableEq R] (m : Multiset R) (d : R → ℕ) :
    (∑ f ∈ m.toFinset,d f) ≤ (m.map d).sum := by
  classical
  induction m using Multiset.induction_on with
  | empty => simp
  | cons f m ih =>
    simp only [Multiset.toFinset_cons,Multiset.map_cons,Multiset.sum_cons]
    by_cases hf : f∈m.toFinset
    · rw [Finset.insert_eq_of_mem hf]
      omega
    · rw [Finset.sum_insert hf]
      omega

omit [NormalizationMonoid F[X][X]] in
theorem seedDegree_multiset_prod (m : Multiset F[X][X]) (hzero : 0∉m) :
    seedDegree m.prod = (m.map seedDegree).sum := by
  unfold seedDegree
  rw [map_multiset_prod]
  have hn : (0:F[X][X])∉m.map Polynomial.Bivariate.swap := by
    intro h
    obtain ⟨f,hf,heq⟩ := Multiset.mem_map.mp h
    have hz : f=0 := Polynomial.Bivariate.swap.injective (heq.trans (map_zero _).symm)
    exact hzero (hz ▸ hf)
  rw [Polynomial.natDegree_multiset_prod _ hn]
  simp only [Multiset.map_map,Function.comp_def]

theorem factorCurves_irreducible {P C : F[X][X]} (hC : C∈factorCurves P) : Irreducible C := by
  classical
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor C (Multiset.mem_toFinset.mp hC)).irreducible

theorem factorCurves_degree_budget (P : F[X][X]) (hP : P≠0) :
    (∑ C ∈ factorCurves P,seedDegree C) ≤ seedDegree P ∧
      (∑ C ∈ factorCurves P,C.natDegree) ≤ P.natDegree := by
  classical
  let m := UniqueFactorizationMonoid.normalizedFactors P
  have hz : (0:F[X][X])∉m := UniqueFactorizationMonoid.zero_notMem_normalizedFactors P
  have hd : m.prod∣P := (UniqueFactorizationMonoid.prod_normalizedFactors hP).dvd
  have hbox := box_of_dvd hP hd (show SeedBox P (seedDegree P) P.natDegree from ⟨le_rfl,le_rfl⟩)
  constructor
  · calc
      _ ≤ (m.map seedDegree).sum := sum_toFinset_le_sum_map m seedDegree
      _ = seedDegree m.prod := (seedDegree_multiset_prod m hz).symm
      _ ≤ seedDegree P := hbox.1
  · calc
      _ ≤ (m.map Polynomial.natDegree).sum := sum_toFinset_le_sum_map m Polynomial.natDegree
      _ = m.prod.natDegree := (Polynomial.natDegree_multiset_prod m hz).symm
      _ ≤ P.natDegree := hbox.2

theorem factorCurves_cover {K : Type*} [Field K] (φ : F[X][X] →+* K)
    (P : F[X][X]) (hP : P≠0) (heval : φ P=0) :
    ∃ C∈factorCurves P,φ C=0 := by
  classical
  obtain ⟨u,hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hP
  have hh := congrArg φ hu
  rw [map_mul,heval] at hh
  have hu0 : φ (u:F[X][X]) ≠ 0 := (Units.isUnit u |>.map φ).ne_zero
  have hp := (mul_eq_zero.mp hh).resolve_right hu0
  rw [map_multiset_prod,Multiset.prod_eq_zero_iff] at hp
  obtain ⟨C,hC,hz⟩ := Multiset.mem_map.mp hp
  exact ⟨C,Multiset.mem_toFinset.mpr hC,hz⟩

end Factors

local instance normalizedPlane : NormalizationMonoid Bivar :=
  letI : StrongNormalizationMonoid Bivar :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  inferInstance

local instance decidablePredicate (P : Prop) : Decidable P := Classical.propDecidable P

theorem evalGraph (γ : K) (Q : Bivar) :
    onGraph γ Q = (Q.map (evalRingHom γ)).eval (γ ^ p) := by
  change Q.eval₂ (evalRingHom γ) (γ ^ p) = _
  rw [Polynomial.eval_map]

theorem nodeEquation_box (L : Bivar[X]) (s t : ℕ)
    (h : ∀ j, SeedBox (L.coeff j) s t) (i : I) : SeedBox (nodeEquation L i) s t := by
  rw [nodeEquation, Polynomial.eval_eq_sum, Polynomial.sum]
  apply box_sum
  intro j hj
  simpa only [planeConstant, RingHom.comp_apply, ← Polynomial.C_pow] using
    box_mul_constant (L.coeff j) (node i ^ j) s t (h j)

theorem root_iff_error {u D a b Γ P L} (h : BoxedLocator u D a b Γ P L)
    {γ : K} (hγ : γ ∈ Γ) (i : I) :
    onGraph γ (nodeEquation L i) = 0 ↔ i ∈ errorSet u D γ (P γ) := by
  obtain ⟨c, hc, hL⟩ := h.fiber γ hγ
  have hconst : onGraph γ (planeConstant (node i)) = node i := by
    rw [evalGraph]
    simp [planeConstant]
  rw [nodeEquation, ← Polynomial.eval_map_apply, hconst, hL, Polynomial.eval_smul,
    smul_eq_mul, mul_eq_zero, or_iff_right hc]
  exact Principal.locator_eval_zero_iff node IRSProfile.domain.injective _ i

theorem proper_intersection (Q T : Bivar) (hQ : Irreducible Q)
    (ht : Q.natDegree ≠ 0) (hproper : ¬ Q ∣ T) (s t : ℕ) (hbox : SeedBox T s t)
    (Γ : Finset K) (hΓ : ∀ γ ∈ Γ, onGraph γ Q = 0 ∧ onGraph γ T = 0) :
    Γ.card ≤ Q.natDegree * s + seedDegree Q * t := by
  have h := bez_proj_coprime Q T (seedDegree Q) s
    (fun j => coeff_natDegree_le_seedDegree Q j) (box_coefficients hbox).2
    (curve_coprime_of_irreducible Q T hQ ht hproper) (Or.inl ht) Γ (by
      intro γ hγ
      exact ⟨γ ^ p, by simpa only [← evalGraph] using hΓ γ hγ⟩)
  exact h.trans (by
    rw [Nat.mul_comm T.natDegree (seedDegree Q)]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hbox.2) _)

/-- On a one-coordinate cut, count the roots of its univariate equation
using the corresponding injective coordinate of the selected graph. -/
theorem coordinate_intersection (Q : Bivar) (hQ : Q ≠ 0)
    (hcoord : seedDegree Q = 0 ∨ Q.natDegree = 0)
    (Γ : Finset K) (hΓ : ∀ γ ∈ Γ, onGraph γ Q = 0) :
    Γ.card ≤ seedDegree Q + Q.natDegree := by
  by_cases ht : Q.natDegree = 0
  · have heq : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero ht
    have hc : Q.coeff 0 ≠ 0 := by intro hz; exact hQ (by rw [heq, hz, Polynomial.C_0])
    have hroot : ∀ γ ∈ Γ, (Q.coeff 0).eval γ = 0 := by
      intro γ hγ
      have h := hΓ γ hγ
      rw [evalGraph, heq, Polynomial.map_C, Polynomial.eval_C, Polynomial.coe_evalRingHom] at h
      exact h
    have hcard : Γ.card ≤ (Q.coeff 0).natDegree := by
      by_contra h
      exact hc (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Γ hroot (by omega))
    exact hcard.trans ((coeff_natDegree_le_seedDegree Q 0).trans (Nat.le_add_right _ _))
  · have hs : seedDegree Q = 0 := hcoord.resolve_right ht
    have hc : ∀ j, Q.coeff j = Polynomial.C ((Q.coeff j).coeff 0) := by
      intro j
      exact Polynomial.eq_C_of_natDegree_eq_zero
        (Nat.eq_zero_of_le_zero (hs ▸ coeff_natDegree_le_seedDegree Q j))
    let T := Q.map (evalRingHom (0 : K))
    have heq : ∀ γ : K, Q.map (evalRingHom γ) = T := by
      intro γ
      ext j
      simp only [T, Polynomial.coeff_map]
      rw [hc j]
      simp
    have hT : T ≠ 0 := by
      intro hz
      apply hQ
      apply Polynomial.ext
      intro j
      have hh := congrArg (fun (V : K[X]) => V.coeff j) hz
      simp only [T, Polynomial.coeff_map, Polynomial.coeff_zero] at hh
      rw [hc j, Polynomial.coe_evalRingHom, Polynomial.eval_C] at hh
      rw [hc j, hh, Polynomial.C_0, Polynomial.coeff_zero]
    let σ : K →+* K := frobenius K p
    have hroot : ∀ y ∈ Γ.image σ, T.eval y = 0 := by
      intro y hy
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hy
      have h := hΓ γ hγ
      rw [evalGraph, heq γ] at h
      exact h
    have hcard : (Γ.image σ).card ≤ T.natDegree := by
      by_contra h
      exact hT (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
        _ (Γ.image σ) hroot (by omega))
    rw [Finset.card_image_of_injective _ σ.injective] at hcard
    exact hcard.trans (Polynomial.natDegree_map_le.trans (Nat.le_add_left _ _))

theorem rational_incidence (D : Finset I) (Γ : Finset K) (rel : I → K → Prop)
    (R : ℕ) (B : ℚ)
    (hroots : ∀ γ ∈ Γ, R ≤ (D.filter (fun i => rel i γ)).card)
    (hfib : ∀ i ∈ D, ((Γ.filter (rel i)).card : ℚ) ≤ B) :
    (R : ℚ) * Γ.card ≤ D.card * B := by
  have hcount : (∑ γ ∈ Γ, (D.filter (fun i => rel i γ)).card) =
      ∑ i ∈ D, (Γ.filter (rel i)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  calc
    (R : ℚ) * Γ.card = ∑ _γ ∈ Γ, (R : ℚ) := by simp [mul_comm]
    _ ≤ ∑ γ ∈ Γ, ((D.filter (fun i => rel i γ)).card : ℚ) :=
      Finset.sum_le_sum (fun γ hγ => by exact_mod_cast hroots γ hγ)
    _ = ∑ i ∈ D, ((Γ.filter (rel i)).card : ℚ) := by exact_mod_cast hcount
    _ ≤ ∑ _i ∈ D, B := Finset.sum_le_sum hfib
    _ = D.card * B := by simp

/-- Factor each node equation, sum the curve charges using its two degree
budgets, then count the selected root incidences in the other direction. -/
theorem plane_incidence {u D a b Γ P L} (h : BoxedLocator u D a b Γ P L)
    (hR : ∀ γ ∈ Γ, (errorSet u D γ (P γ)).card = a + b)
    (w : ℚ) (hw : 0 ≤ w)
    (hcurve : ∀ Q : Bivar, Irreducible Q →
      ((onCurve Γ Q).card : ℚ) ≤ w * (seedDegree Q + Q.natDegree : ℕ)) :
    (a + b : ℚ) * Γ.card ≤ D.card * (2 * w * b) := by
  let rel := fun i γ => onGraph γ (nodeEquation L i) = 0
  have hroots : ∀ γ ∈ Γ, a+b ≤ (D.filter (fun i => rel i γ)).card := by
    intro γ hγ
    rw [← hR γ hγ]
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1, (root_iff_error h hγ i).mpr hi⟩
  have hfib : ∀ i ∈ D, ((Γ.filter (rel i)).card : ℚ) ≤ 2*w*b := by
    intro i hi
    let C := factorCurves (nodeEquation L i)
    have hcover : Γ.filter (rel i) ⊆ C.biUnion (onCurve Γ) := by
      intro γ hγ
      obtain ⟨hγΓ, hz⟩ := Finset.mem_filter.mp hγ
      obtain ⟨Q, hQ, hzero⟩ :=
        factorCurves_cover (onGraph γ) _ (h.noFixed i hi) hz
      exact Finset.mem_biUnion.mpr ⟨Q, hQ, Finset.mem_filter.mpr ⟨hγΓ, hzero⟩⟩
    have hcard : (Γ.filter (rel i)).card ≤ ∑ Q ∈ C, (onCurve Γ Q).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have hbox := nodeEquation_box L b b h.box i
    have hbudget := factorCurves_degree_budget _ (h.noFixed i hi)
    have hS := hbudget.1.trans hbox.1
    have hT := hbudget.2.trans hbox.2
    have hsum : (∑ Q ∈ C, (seedDegree Q + Q.natDegree)) ≤ 2*b := by
      rw [Finset.sum_add_distrib]
      change (∑ Q ∈ C, seedDegree Q) ≤ b at hS
      change (∑ Q ∈ C, Q.natDegree) ≤ b at hT
      omega
    have hsumq : (∑ Q ∈ C, ((seedDegree Q + Q.natDegree : ℕ) : ℚ)) ≤ 2*b := by
      exact_mod_cast hsum
    calc
      _ ≤ ∑ Q ∈ C, ((onCurve Γ Q).card : ℚ) := by exact_mod_cast hcard
      _ ≤ ∑ Q ∈ C, w * (seedDegree Q + Q.natDegree : ℕ) :=
        Finset.sum_le_sum (fun _ hQ => hcurve _ (factorCurves_irreducible hQ))
      _ = w * (∑ Q ∈ C, ((seedDegree Q + Q.natDegree : ℕ) : ℚ)) := by rw [Finset.mul_sum]
      _ ≤ w * (2*b) := mul_le_mul_of_nonneg_left hsumq hw
      _ = _ := by ring
  have hi := rational_incidence D Γ rel (a+b) (2*w*b) (by
    intro γ hγ
    convert hroots γ hγ using 2
    ext i
    simp only [Finset.mem_filter]) (by
    intro i hi
    convert hfib i hi using 3
    ext γ
    simp only [Finset.mem_filter])
  simpa only [Nat.cast_add] using hi

end

end K21_2_4
end Port_K1_2_4Geometry

section Port_K1_2_3Graph
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000

namespace K21_2_3
noncomputable section

open Polynomial Matrix Finset FrobeniusLocator
open K21 K21_2

variable {F : Type*} [Field F]

private def graphSubst (p : ℕ) (P : F[X][X]) : F[X] :=
  P.eval₂ (RingHom.id F[X]) ((Polynomial.X : F[X]) ^ p)

private theorem graphSubst_coeff (p : ℕ) (hp : 0<p) (P : F[X][X])
    (hbox : ∀ j,(P.coeff j).natDegree<p) (i j : ℕ) (hi : i<p) :
    (graphSubst p P).coeff (i+p*j)=(P.coeff j).coeff i := by
  classical
  rw [graphSubst,eval₂_eq_sum,Polynomial.sum,finsetSum_coeff]
  simp only [RingHom.id_apply,←pow_mul]
  rw [Finset.sum_eq_single j]
  · exact coeff_mul_X_pow (P.coeff j) (p*j) i
  · intro k hk hkj
    rw [coeff_mul_X_pow']
    rcases lt_or_gt_of_ne hkj with hkj' | hjk
    · have hpk : p*(k+1)≤p*j := Nat.mul_le_mul_left p (by omega)
      have hprod : p*k+p≤p*j := by nlinarith
      have hbound : p ≤ i+p*j-p*k := by omega
      rw [ite_eq_left (by omega)]
      exact coeff_eq_zero_of_natDegree_lt ((hbox k).trans_le hbound)
    · have hpk : p*(j+1)≤p*k := Nat.mul_le_mul_left p (by omega)
      rw [ite_eq_right (by nlinarith)]
  · intro hj
    have hz : P.coeff j=0 := by simpa only [Polynomial.mem_support_iff,not_not] using hj
    simp only [hz,zero_mul,coeff_zero]

private theorem graphSubst_eq_zero_iff (p : ℕ) (hp : 0<p) (P : F[X][X])
    (hbox : ∀ j,(P.coeff j).natDegree<p) : graphSubst p P=0 ↔ P=0 := by
  constructor
  · intro hz
    ext j i
    by_cases hi : i<p
    · have h := graphSubst_coeff p hp P hbox i j hi
      rw [hz,coeff_zero] at h
      simpa only [coeff_zero] using h.symm
    · rw [coeff_zero]
      exact coeff_eq_zero_of_natDegree_lt ((hbox j).trans_le (by omega))
  · rintro rfl
    simp [graphSubst]

/-- Every low-S-degree minor vanishing on the formal Frobenius graph
vanishes on the whole independent parameter plane. -/
private theorem low_degree_minor_zero (p a : ℕ) (hap : a<p) (P : F[X][X])
    (hdegree : ∀ j,(P.coeff j).natDegree≤a) (hgraph : graphSubst p P=0) : P=0 :=
  (graphSubst_eq_zero_iff p (by omega) P (fun j => (hdegree j).trans_lt hap)).mp hgraph

def graphHom : Bivar →+* K[X] :=
  Polynomial.eval₂RingHom (RingHom.id K[X]) ((Polynomial.X : K[X]) ^ p)

private theorem coeff_coeff_swap (P : Bivar) (i j : ℕ) :
    ((Polynomial.Bivariate.swap P).coeff i).coeff j = (P.coeff j).coeff i := by
  classical
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ]
  | monomial n f =>
    induction f using Polynomial.induction_on' with
    | add f g hf hg => simp only [map_add, coeff_add, hf, hg]
    | monomial m c =>
      rw [Polynomial.Bivariate.swap_monomial_monomial]
      by_cases hi : m = i <;> by_cases hj : n = j <;>
        simp [Polynomial.coeff_monomial, hi, hj]

private theorem det_degree {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1) :
    M.det.natDegree ≤ Fintype.card ι := by
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [Units.smul_def]
  refine (Polynomial.natDegree_smul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
  exact (Finset.sum_le_sum (fun i _ => hM _ _)).trans_eq (by simp)

private theorem plane_entry_degree (u : Words) (D : Finset I) (a R : ℕ)
    (i : Fin 2 × Fin a) (j : Fin (R + 1)) :
    (Polynomial.Bivariate.swap (planeMatrix u D a R i j)).natDegree ≤ 1 := by
  unfold planeMatrix
  dsimp only
  split_ifs
  · rw [Polynomial.Bivariate.swap_C]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le (by simp)
    exact Polynomial.natDegree_mul_le.trans (by simp)
  · rw [map_add, map_mul, Polynomial.Bivariate.swap_C_C, Polynomial.Bivariate.swap_C_C,
      Polynomial.Bivariate.swap_Y, ← Polynomial.C_mul, ← Polynomial.C_add]
    exact (Polynomial.natDegree_C _).le.trans (by decide : 0 ≤ 1)

/-- Full-column minors have inner seed degree at most the number of columns.
Thus their vanishing on the formal graph lifts to the independent plane. -/
theorem plane_rank_le (u : Words) (D : Finset I) (a R : ℕ) (hRp : R + 1 < p)
    (hgraph : ((planeMatrix u D a R).map
      ((algebraMap K[X] Frac).comp graphHom)).rank ≤ R) :
    ((planeMatrix u D a R).map (algebraMap Bivar (FractionRing Bivar))).rank ≤ R := by
  classical
  let M := planeMatrix u D a R
  let f := (algebraMap K[X] Frac).comp graphHom
  let g := algebraMap Bivar (FractionRing Bivar)
  apply Strata.rank_le_of_all_maximal_minors_zero
  intro rows
  let N := M.submatrix rows id
  have hz : (N.map f).det = 0 := by
    by_contra hn
    have hk := Matrix.rank_submatrix_le (M.map f) rows id
    change (N.map f).rank ≤ (M.map f).rank at hk
    rw [Matrix.rank_of_det_ne_zero hn, Fintype.card_fin] at hk
    change (M.map f).rank ≤ R at hgraph
    omega
  have hf : graphSubst p N.det = 0 := by
    apply IsFractionRing.injective K[X] Frac
    change f N.det = (algebraMap K[X] Frac) 0
    exact ((f.map_det N).trans hz).trans (map_zero _).symm
  have hd : (Polynomial.Bivariate.swap N.det).natDegree ≤ R + 1 := by
    rw [AlgEquiv.map_det]
    change (N.map Polynomial.Bivariate.swap).det.natDegree ≤ R + 1
    simpa only [Fintype.card_fin] using
      det_degree (N.map Polynomial.Bivariate.swap) (fun i j => plane_entry_degree u D a R (rows i) j)
  have hc (j : ℕ) : (N.det.coeff j).natDegree ≤ R + 1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [← coeff_coeff_swap, Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hi), coeff_zero]
  change (N.map g).det = 0
  calc
    _ = g N.det := (g.map_det N).symm
    _ = 0 := (congrArg g (low_degree_minor_zero p (R + 1) hRp N.det hc hf)).trans (map_zero g)

/-- A nonzero minor at a slope is a nonzero minor over the fraction field. -/
theorem rank_ge_specialization {A F E row col : Type*}
    [CommRing A] [Field F] [Field E] [Fintype row] [Fintype col]
    (M : Matrix row col A) (f : A →+* F) (g : A →+* E) (hg : Function.Injective g) :
    (M.map f).rank ≤ (M.map g).rank := by
  classical
  let N := M.map f
  let r := N.rank
  obtain ⟨κ, c, hc, hspan, hli⟩ := exists_linearIndependent' F N.col
  let : Finite κ := Finite.of_injective c hc
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols]
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let cols : Fin r → col := c ∘ e
  have hind : LinearIndependent F (fun j => N.col (cols j)) := hli.comp e e.injective
  obtain ⟨rows, hdet⟩ := GenericRank.exists_rows_det_ne_zero (N.submatrix id cols) (by
    intro v hv
    have hsum : (∑ j, v j • N.col (cols j)) = 0 := by
      funext i
      simpa only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq, Matrix.col, Matrix.transpose_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm, Pi.zero_apply] using congrFun hv i
    funext j
    exact Fintype.linearIndependent_iff.mp hind v hsum j)
  let P := M.submatrix rows cols
  have hP : P.det ≠ 0 := by
    intro h
    apply hdet
    change (P.map f).det = 0
    exact ((f.map_det P).symm.trans (congrArg f h)).trans (map_zero f)
  have hPg : (P.map g).det ≠ 0 := by
    intro h
    exact hP (hg (((g.map_det P).trans h).trans (map_zero g).symm))
  have hle := Matrix.rank_submatrix_le (M.map g) rows cols
  change (P.map g).rank ≤ _ at hle
  rwa [Matrix.rank_of_det_ne_zero hPg, Fintype.card_fin] at hle

end
end K21_2_3
end Port_K1_2_3Graph

section Port_K1_2_4_1Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K21_2_4_1

noncomputable section

open Polynomial FrobeniusLocator
open K21 K21_2 K21_2_4

/-- The polynomial locator line and its selected fibers before removing
the globally fixed nodes. -/
structure MarkedLocator (u : Words) (D : Finset I) (a d : ℕ) (Γ : Finset K)
    (P : K → K[X]) (L : Bivar[X]) : Prop where
  degree : L.natDegree ≤ d
  kernel : (planeMatrix u D a d).mulVec (fun j => L.coeff j.val) = 0
  fiber : ∀ γ ∈ Γ, ∃ c : K, c ≠ 0 ∧
    L.map (onGraph γ) = c • locator node (errorSet u D γ (P γ))

/-- The fixed-root factor, viewed as a polynomial in the node variable. -/
def fixedFactor (F : Finset I) : Bivar[X] := (locator node F).map planeConstant

end

end K21_2_4_1
end Port_K1_2_4_1Defs

section Port_K1_2_2Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K21_2_2

noncomputable section

open K21 Polynomial Matrix FrobeniusLocator

/-- The two syndrome streams on the complement of the fixed node roots.
The number of rows stays fixed because all the deleted nodes are errors. -/
def shortenedStack {u : Words} {T : TwoActive u} (R : Relation T) :
    Matrix (Fin 2 × Fin 49058) (Fin (82014 - (fixedNodes R).card + 1)) K[X] :=
  let D := Finset.univ \ fixedNodes R
  stacked p (fun i : D => node i.val) (fun i => u 0 i.val) (fun i => u 1 i.val)
    49058 (82014 - (fixedNodes R).card)

/-- Coefficient polynomials in the seed, with the outer variable
reserved for the evaluation coordinate. -/
def pair {u : Words} {T : TwoActive u} {R : Relation T} (A : Reduction u T R) :
    Fin 2 → Bivar :=
  Fin.cases A.U (fun _ => A.V)

end

end K21_2_2
end Port_K1_2_2Defs

section Port_K1_2_2Resultant
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace K21_2_2
noncomputable section

open K21 K21_2 Polynomial Matrix FrobeniusLocator
open scoped BigOperators

private theorem padded_resultant_ne {F : Type*} [Field F] {A B : F[X]} {H : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hcop : IsCoprime A B)
    (hmax : max A.natDegree B.natDegree = H) :
    resultant A B H H ≠ 0 := by
  have hres := resultant_ne_zero A B hcop
  rcases le_total A.natDegree B.natDegree with hab | hba
  · rw [max_eq_right hab] at hmax
    have he : A.natDegree + (H - A.natDegree) = H := by omega
    have hp := resultant_add_left_deg A B A.natDegree B.natDegree (H - A.natDegree) le_rfl
    rw [he, hmax] at hp
    rw [hmax] at hres
    rw [hp]
    have hc : B.coeff H ≠ 0 := by rw [← hmax, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hB
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (pow_ne_zero _ hc)) hres
  · rw [max_eq_left hba] at hmax
    have he : B.natDegree + (H - B.natDegree) = H := by omega
    have hp := resultant_add_right_deg A B A.natDegree B.natDegree (H - B.natDegree) le_rfl
    rw [he, hmax] at hp
    rw [hmax] at hres
    rw [hp]
    have hc : A.coeff H ≠ 0 := by rw [← hmax, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hA
    exact mul_ne_zero (pow_ne_zero _ hc) hres

private theorem resultant_degree {F : Type*} [Field F]
    {U V : F[X][X]} {H ζ : ℕ} (hU : ∀ i, (U.coeff i).natDegree ≤ ζ)
    (hV : ∀ i, (V.coeff i).natDegree ≤ ζ) :
    (resultant U V H H).natDegree ≤ 2 * H * ζ := by
  change (sylvester U V H H).det.natDegree ≤ _
  have h := natDegree_det_le_row_sum (sylvester U V H H)
    (fun _ => ζ) (fun i j => by
      refine Fin.addCases ?_ ?_ j
      · intro k
        simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
        split
        · exact hV _
        · simp
      · intro k
        simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
        split
        · exact hU _
        · simp)
  simpa [nsmul_eq_mul, two_mul] using h

/-- The Sylvester determinant with both degree declarations equal to the
maximum detects a finite common factor as well as a common root at infinity. -/
theorem resultant_book {u : Words} {D : Finset I} {H ζ : ℕ}
    (Q : ReducedRelation u D H) (hH : 0 < H)
    (hU : Q.U ≠ 0) (hV : Q.V ≠ 0) (hcop : IsCoprime (extendSeed Q.U) (extendSeed Q.V))
    (hζU : ∀ i, (Q.U.coeff i).natDegree ≤ ζ) (hζV : ∀ i, (Q.V.coeff i).natDegree ≤ ζ)
    (Γ : Finset K) :
    ∃ book : Finset K, book ⊆ Γ ∧ book.card ≤ 2 * H * ζ ∧
      ∀ γ ∈ Γ \ book, RegularAt Q γ := by
  classical
  let Δ := resultant Q.U Q.V H H
  let φ : K[X] →+* Frac := algebraMap K[X] Frac
  have hφ := IsFractionRing.injective K[X] Frac
  have hne {P : Bivar} (hP : P ≠ 0) : P.map φ ≠ 0 :=
    fun hz => hP ((Polynomial.map_injective φ hφ) (hz.trans (Polynomial.map_zero φ).symm))
  have hmax : max (Q.U.map φ).natDegree (Q.V.map φ).natDegree = H := by
    rw [natDegree_map_eq_of_injective hφ Q.U, natDegree_map_eq_of_injective hφ Q.V]
    exact Q.height
  have hΔ : Δ ≠ 0 := by
    intro hz
    apply padded_resultant_ne (hne hU) (hne hV) hcop hmax
    rw [resultant_map_map]
    exact (congrArg φ hz).trans (map_zero φ)
  let book := Γ.filter fun γ => Δ.eval γ = 0
  refine ⟨book, Finset.filter_subset _ _, ?_, ?_⟩
  · apply (Polynomial.card_le_degree_of_subset_roots ?_).trans
      (resultant_degree hζU hζV)
    intro γ hγ
    exact (Polynomial.mem_roots hΔ).mpr (Finset.mem_filter.mp hγ).2
  · intro γ hγ
    have hval : Δ.eval γ ≠ 0 := fun hzero =>
      (Finset.mem_sdiff.mp hγ).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hγ).1, hzero⟩)
    let A := atSlope Q.U γ
    let B := atSlope Q.V γ
    let d := resultant A B H H
    have hd : d ≠ 0 := by
      change resultant (Q.U.map (evalRingHom γ)) (Q.V.map (evalRingHom γ)) H H ≠ 0
      rw [resultant_map_map]
      exact hval
    have hA : A.natDegree ≤ H := natDegree_map_le.trans ((le_max_left _ _).trans_eq Q.height)
    have hB : B.natDegree ≤ H := natDegree_map_le.trans ((le_max_right _ _).trans_eq Q.height)
    change IsCoprime A B ∧ max A.natDegree B.natDegree = H
    refine ⟨?_, le_antisymm (max_le hA hB) (Nat.le_of_not_gt ?_)⟩
    · obtain ⟨a, b, _, _, hab⟩ :=
        exists_mul_add_mul_eq_C_resultant A B hA hB (Or.inl hH.ne')
      refine ⟨C d⁻¹ * a, C d⁻¹ * b, ?_⟩
      calc
        _ = C d⁻¹ * (A * a + B * b) := by ring
        _ = 1 := by rw [hab, ← map_mul, inv_mul_cancel₀ hd, map_one]
    · intro hlt
      exact hd (resultant_eq_zero_of_lt_lt A B H H
        ((le_max_left _ _).trans_lt hlt) ((le_max_right _ _).trans_lt hlt))

end
end K21_2_2
end Port_K1_2_2Resultant

section Port_K1_2_2Primitive
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace K21_2_2
noncomputable section

open K21 Polynomial FrobeniusLocator K1_6

theorem pair_degree {u : Words} {T : TwoActive u} {R : Relation T}
    (A : Reduction u T R) (b : Fin 2) : (pair A b).natDegree ≤ A.height := by
  fin_cases b
  · exact (le_max_left _ _).trans_eq A.max_degree
  · exact (le_max_right _ _).trans_eq A.max_degree

/-- The ideal generated by the reduced coefficients contains every
coefficient of the original pair, by multiplying back the fixed locator. -/
theorem pair_primitive {u : Words} {T : TwoActive u} {R : Relation T}
    (A : Reduction u T R) : PrimitiveVector.IsPrimitive (pairCoordinates (pair A) A.height) := by
  let J : Ideal K[X] := Ideal.span (Set.range (pairCoordinates (pair A) A.height))
  let φ := Ideal.Quotient.mk J
  have hzero (b : Fin 2) : (pair A b).map φ = 0 := by
    ext i
    rw [coeff_map, coeff_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    by_cases hi : i < A.height + 1
    · exact Ideal.subset_span (Set.mem_range_self ((b, ⟨i, hi⟩) : Fin 2 × Fin (A.height + 1)))
    · rw [coeff_eq_zero_of_natDegree_lt ((pair_degree A b).trans_lt (by omega))]
      exact J.zero_mem
  have hfactor (b : Fin 2) :
      Principal.assemble (fun j => R.coefficients (b, j)) =
        liftX (locator node (fixedNodes R)) * pair A b := by
    fin_cases b
    · exact A.U_factor
    · exact A.V_factor
  have horig (i : Fin 2 × Fin (T.height + 1)) : R.coefficients i ∈ J := by
    have h := congrArg (Polynomial.map φ) (hfactor i.1)
    rw [Polynomial.map_mul, hzero, mul_zero] at h
    have hc := congrArg (fun P : (K[X] ⧸ J)[X] => P.coeff i.2.val) h
    rw [coeff_map, Principal.assemble_coeff, coeff_zero] at hc
    exact Ideal.Quotient.eq_zero_iff_mem.mp hc
  change J = ⊤
  apply top_unique
  rw [← R.primitive]
  exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact horig i)

end
end K21_2_2
end Port_K1_2_2Primitive

section Port_K1_2_4_1_1Cofactors
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace K21_2_4_1_1

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator
open K21 K21_2 K21_2_4

/-- Complete a preferred independent block prefix to a square row pivot. -/
theorem select_rows {a d : ℕ} (M : Matrix (Fin 2 × Fin a) (Fin d) K)
    (hM : M.rank = d) (b : Fin 2)
    (hprefix : LinearIndependent K (fun j : Fin (min a d) =>
      M.row (b, j.castLE (min_le_left _ _)))) :
    ∃ rows : Fin d → Fin 2 × Fin a, (M.submatrix rows id).det ≠ 0 ∧
      (Finset.univ.filter (fun j => (rows j).1 = b)).card = min a d := by
  classical
  let f : Fin (min a d) ↪ Fin 2 × Fin a :=
    ⟨fun j => (b, j.castLE (min_le_left _ _)), fun i j h =>
      Fin.ext (congrArg (fun k : Fin 2 × Fin a => k.2.val) h)⟩
  let S := Set.range f
  have hS : LinearIndepOn K M.row S := (linearIndepOn_range_iff f.injective M.row).mpr hprefix
  let T := hS.extend (Set.subset_univ S)
  have hST := hS.subset_extend (Set.subset_univ S)
  have hli : LinearIndependent K (fun i : T => M.row i.val) :=
    (hS.linearIndepOn_extend (Set.subset_univ S)).linearIndependent_restrict
  have hspace : Submodule.span K (Set.range (fun i : T => M.row i.val)) =
      Submodule.span K (Set.range M.row) := by
    have heq : Set.range (fun i : T => M.row i.val) = M.row '' T := by
      ext v
      exact ⟨fun ⟨i, hi⟩ => ⟨i.val, i.property, hi⟩,
        fun ⟨i, hi, hv⟩ => ⟨⟨i, hi⟩, hv⟩⟩
    rw [heq, hS.span_image_extend_eq_span_image (Set.subset_univ S), Set.image_univ]
  have hcard : Fintype.card T = d := by
    rw [← finrank_span_eq_card hli, hspace, ← Matrix.rank_eq_finrank_span_row, hM]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let rows : Fin d → Fin 2 × Fin a := Subtype.val ∘ e
  have hinj : Function.Injective rows := Subtype.val_injective.comp e.injective
  have hpiv : LinearIndependent K (M.submatrix rows id).row := hli.comp e e.injective
  refine ⟨rows, ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hpiv)).ne_zero, ?_⟩
  let B := Finset.univ.filter (fun j => (rows j).1 = b)
  let intoB (j : Fin (min a d)) : B :=
    ⟨e.symm ⟨f j, hST (Set.mem_range_self j)⟩, by simp [B, rows, f]⟩
  have hlo := Fintype.card_le_of_injective intoB (by
    intro i j hij
    apply f.injective
    have he := e.symm.injective (congrArg Subtype.val hij)
    exact congrArg Subtype.val he)
  have hhi := Fintype.card_le_of_injective (fun i : B => (rows i.val).2) (by
    intro i j hij
    apply Subtype.ext
    apply hinj
    exact Prod.ext ((Finset.mem_filter.mp i.property).2.trans
      (Finset.mem_filter.mp j.property).2.symm) hij)
  simp only [Fintype.card_fin, Fintype.card_coe] at hlo hhi
  have hB := Finset.card_le_card (Finset.filter_subset (fun j => (rows j).1 = b) Finset.univ)
  rw [Finset.card_univ, Fintype.card_fin] at hB
  exact le_antisymm (le_min hhi hB) hlo

/-- Signed cofactors of a selected frame, with the monic slot last. -/
def cofactor {R : Type*} [CommRing R] {d : ℕ}
    (N : Matrix (Fin d) (Fin (d+1)) R) (j : Fin (d+1)) : R :=
  (-1) ^ (d+j.val) * (N.submatrix id j.succAbove).det

theorem cofactor_last {R : Type*} [CommRing R] {d : ℕ}
    (N : Matrix (Fin d) (Fin (d+1)) R) :
    cofactor N (Fin.last d) = (N.submatrix id Fin.castSucc).det := by
  simp [cofactor, ← two_mul d, pow_mul]

theorem cofactor_map {R S : Type*} [CommRing R] [CommRing S] {d : ℕ}
    (f : R →+* S) (N : Matrix (Fin d) (Fin (d+1)) R) (j : Fin (d+1)) :
    f (cofactor N j) = cofactor (N.map f) j := by
  simp only [cofactor, map_mul, map_pow, map_neg, map_one, f.map_det]
  rfl

private theorem selected_kernel {R : Type*} [CommRing R] {d : ℕ}
    (N : Matrix (Fin d) (Fin (d+1)) R) : N.mulVec (cofactor N) = 0 := by
  funext i
  let Q : Matrix (Fin (d+1)) (Fin (d+1)) R := Fin.lastCases (N i) N
  have hz : Q.det = 0 := Matrix.det_zero_of_row_eq
    (Fin.castSucc_lt_last i).ne' (by simp [Q])
  rw [Matrix.det_succ_row Q (Fin.last d)] at hz
  change (∑ j, N i j * cofactor N j) = 0
  simpa only [Q, cofactor, Fin.val_last,
    Fin.succAbove_last, Matrix.submatrix, Fin.lastCases_castSucc, Fin.lastCases_last,
    id_eq, mul_assoc, mul_left_comm] using hz

/-- A nonzero pivot at generic rank d makes the cofactor a kernel vector
for every row, as an identity over the coefficient ring. -/
theorem cofactor_kernel {R E row : Type*} [CommRing R] [Field E] [Fintype row] {d : ℕ}
    (φ : R →+* E) (hφ : Function.Injective φ) (M : Matrix row (Fin (d+1)) R)
    (rows : Fin d → row) (hrank : (M.map φ).rank = d)
    (hpivot : φ (cofactor (M.submatrix rows id) (Fin.last d)) ≠ 0) :
    M.mulVec (cofactor (M.submatrix rows id)) = 0 := by
  let A := M.map φ
  let N := A.submatrix rows id
  have hp : (N.submatrix id Fin.castSucc).det ≠ 0 := by
    rw [cofactor_map, cofactor_last] at hpivot
    exact hpivot
  have hlo := Matrix.rank_submatrix_le N id Fin.castSucc
  rw [Matrix.rank_of_det_ne_zero hp, Fintype.card_fin] at hlo
  have hN : N.rank = d := le_antisymm
    (by simpa only [Fintype.card_fin] using N.rank_le_card_height) hlo
  have hle : LinearMap.ker A.mulVecLin ≤ LinearMap.ker N.mulVecLin := by
    intro v hv
    funext i
    exact congrFun (show A.mulVec v = 0 from hv) (rows i)
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [GenericRank.nullity_one_of_rank A (by simp [A, hrank]),
      GenericRank.nullity_one_of_rank N (by simp [hN])])
  have hker : A.mulVec (cofactor N) = 0 := by
    have hmem : cofactor N ∈ LinearMap.ker N.mulVecLin := selected_kernel N
    rw [← heq] at hmem
    exact hmem
  have hmap (j : Fin (d+1)) : cofactor N j = φ (cofactor (M.submatrix rows id) j) :=
    (cofactor_map φ _ j).symm
  funext i
  apply hφ
  simpa only [A, hmap, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply,
    map_sum, map_mul, map_zero] using congrFun hker i

private theorem determinant_degree {A : Type*} [CommRing A] {d : ℕ}
    (N : Matrix (Fin d) (Fin d) A[X]) (v : Fin d → ℕ)
    (hN : ∀ i j, (N i j).natDegree ≤ v i) : N.det.natDegree ≤ ∑ i, v i := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [Units.smul_def]
  exact (Polynomial.natDegree_smul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans
    (Finset.sum_le_sum fun i _ => hN i (σ i)))

private theorem cofactor_degree {A : Type*} [CommRing A] {d : ℕ}
    (N : Matrix (Fin d) (Fin (d+1)) A[X]) (v : Fin d → ℕ)
    (hN : ∀ i j, (N i j).natDegree ≤ v i) (j : Fin (d+1)) :
    (cofactor N j).natDegree ≤ ∑ i, v i := by
  unfold cofactor
  have hs : ((-1 : A[X]) ^ (d+j.val)).natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact natDegree_pow_le.trans (by simp)
  exact natDegree_mul_le.trans (by
    rw [hs, zero_add]
    exact determinant_degree _ v (fun i k => hN i (j.succAbove k)))

private theorem affine_degree {A : Type*} [CommRing A] [Nontrivial A] (v w : A) :
    (Polynomial.C v + Polynomial.X * Polynomial.C w).natDegree ≤ 1 := by
  rw [Polynomial.natDegree_C_add]
  exact Polynomial.natDegree_mul_le.trans (by simp)

private theorem entry_box (u : Words) (D : Finset I) (a d : ℕ) (r : Fin 2 × Fin a)
    (j : Fin (d+1)) :
    SeedBox (planeMatrix u D a d r j) (if r.1 = 0 then 1 else 0)
      (if r.1 ≠ 0 then 1 else 0) := by
  unfold planeMatrix SeedBox seedDegree
  dsimp only
  by_cases h : r.1 = 0
  · simp only [h, ite_true]
    constructor
    · rw [Polynomial.Bivariate.swap_C, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
      exact affine_degree (A := K[X]) _ _
    · exact (Polynomial.natDegree_C _).le
  · simp only [ite_eq_right h, ite_eq_left h]
    constructor
    · rw [map_add, map_mul, Polynomial.Bivariate.swap_C_C, Polynomial.Bivariate.swap_C_C,
        Polynomial.Bivariate.swap_Y, ← Polynomial.C_mul, ← Polynomial.C_add]
      exact (Polynomial.natDegree_C _).le
    · exact affine_degree (A := K[X]) _ _

theorem cofactor_box (u : Words) (D : Finset I) (a d : ℕ)
    (rows : Fin d → Fin 2 × Fin a) (j : Fin (d+1)) :
    SeedBox (cofactor ((planeMatrix u D a d).submatrix rows id) j)
      (Finset.univ.filter (fun i => (rows i).1 = 0)).card
      (Finset.univ.filter (fun i => (rows i).1 ≠ 0)).card := by
  classical
  let N := (planeMatrix u D a d).submatrix rows id
  constructor
  · change (Polynomial.Bivariate.swap.toRingHom (cofactor N j)).natDegree ≤ _
    rw [cofactor_map]
    simpa only [Finset.sum_boole, Nat.cast_id] using
      cofactor_degree (N.map Polynomial.Bivariate.swap.toRingHom)
        (fun i => if (rows i).1 = 0 then 1 else 0) (fun i k => (entry_box u D a d (rows i) k).1) j
  · simpa only [Finset.sum_boole, Nat.cast_id] using
      cofactor_degree N (fun i => if (rows i).1 ≠ 0 then 1 else 0)
        (fun i k => (entry_box u D a d (rows i) k).2) j

end

end K21_2_4_1_1
end Port_K1_2_4_1_1Cofactors

section Port_K1_2_3FormalRank
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

namespace K21_2_3
noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K21 K21_2
open scoped BigOperators

private theorem map_syndrome {F E ι : Type*} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (f : F →+* E) (x w : ι → F) (j : ℕ) :
    f (syndrome x w j) = syndrome (fun i => f (x i)) (fun i => f (w i)) j := by
  simp only [syndrome, weight, map_sum, map_mul, map_pow, map_inv₀, map_prod, map_sub]

private theorem shifts_rank {E : Type} [Field E] (P : Fin 2 → E[X]) (a H : ℕ) (hH : H ≤ a)
    (hP : ∀ b, (P b).natDegree ≤ H) (hnz : ∃ b, P b ≠ 0) :
    (K1_6.shifts P a (a - H)).rank = a - H := by
  let W := K1_6.shifts P a (a - H)
  obtain ⟨b, hb⟩ := hnz
  have hinj : Function.Injective W.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    let A : E[X] := ∑ j : Fin (a - H), monomial j.val (v j)
    have hA : P b * A = 0 := by
      ext n
      by_cases hn : n < a
      · have hh := congrFun hv (b, ⟨n, hn⟩)
        change (∑ j : Fin (a - H), (P b * Polynomial.X ^ j.val).coeff n * v j) = 0 at hh
        simpa only [A, Finset.mul_sum, ← C_mul_X_pow_eq_monomial, mul_left_comm (P b),
          coeff_C_mul, finsetSum_coeff, coeff_zero, mul_comm (v _)] using hh
      · rw [coeff_zero]
        simp only [A, Finset.mul_sum, finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro j _
        have hd : (P b * monomial j.val (v j)).natDegree ≤ H + j.val :=
          natDegree_mul_le.trans (Nat.add_le_add (hP b) (natDegree_monomial_le _))
        exact coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by have := j.isLt; omega))
    have hz := (mul_eq_zero.mp hA).resolve_left hb
    funext j
    have h := congrArg (fun P : E[X] => P.coeff j.val) hz
    simp only [A, finsetSum_coeff, coeff_monomial, coeff_zero] at h
    rw [Finset.sum_eq_single j] at h
    · simpa only [ite_true, Pi.zero_apply] using h
    · intro i _ hij
      simp [show i.val ≠ j.val from fun h => hij (Fin.ext h)]
    · simp
  change Module.finrank E (LinearMap.range W.mulVecLin) = a - H
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

private def GraphNodes {F E ι : Type} [Field F] [Field E] (q : ℕ) (x u v : ι → F)
    (φ : F[X] →+* E) (U V out : F[X][X]) : Prop :=
  let f := φ.comp (C : F →+* F[X])
  let z := φ (Polynomial.X (R := F))
  ∀ i, (U.map φ).eval (f (x i)) * (f (u i) + z * f (v i)) +
    (V.map φ).eval (f (x i)) * (f (u i ^ q) + z ^ q * f (v i ^ q)) =
      (out.map φ).eval (f (x i))

private theorem stacked_rank_le {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (q : ℕ) [ExpChar F q]
    (y u v : ι → F) (hy : Function.Injective y) (hfix : ∀ i, y i ^ q = y i)
    (φ : F[X] →+* E) (hφ : Function.Injective φ) (k a H : ℕ) (hH : H ≤ a)
    (hD : k + a + (a + H) ≤ Fintype.card ι) (U V out : F[X][X])
    (hnon : U ≠ 0 ∨ V ≠ 0) (hheight : max U.natDegree V.natDegree = H)
    (houtput : out.degree < (k + H : ℕ))
    (hnodes : GraphNodes q y u v φ U V out) :
    ((stacked q y u v a (a + H)).map φ).rank ≤ a + H := by
  classical
  let f := φ.comp (C : F →+* F[X])
  let x : ι → E := fun i => f (y i)
  let z : E := φ (Polynomial.X (R := F))
  let w (b : Fin 2) (i : ι) : E :=
    if b = 0 then f (u i) + z * f (v i) else f (u i ^ q) + z ^ q * f (v i ^ q)
  let P (b : Fin 2) : E[X] := (if b = 0 then U else V).map φ
  let M := (stacked q y u v a (a + H)).map φ
  let W := K1_6.shifts P a (a - H)
  have hP (b : Fin 2) : (P b).natDegree ≤ H := by
    dsimp only [P]
    split_ifs
    · exact natDegree_map_le.trans ((le_max_left _ _).trans_eq hheight)
    · exact natDegree_map_le.trans ((le_max_right _ _).trans_eq hheight)
  have hnz : ∃ b, P b ≠ 0 := by
    rcases hnon with hU | hV
    · exact ⟨0, (Polynomial.map_ne_zero_iff hφ).mpr hU⟩
    · exact ⟨1, (Polynomial.map_ne_zero_iff hφ).mpr hV⟩
  have hmom (b : Fin 2) (l : Fin a) (j : Fin (a + H + 1)) :
      M (b,l) j = syndrome x (w b) (l.val + j.val) := by
    by_cases hb : b = 0
    · simp only [M, Matrix.map_apply, stacked, hankel, hb, ite_true, map_add, map_mul]
      change f (syndrome y u _) + z * f (syndrome y v _) = _
      rw [map_syndrome, map_syndrome]
      simpa only [w, hb, ite_true, one_mul] using
        (Principal.syndrome_linear x (fun i => f (u i)) (fun i => f (v i)) 1 z _).symm
    · simp only [M, Matrix.map_apply, stacked, hb, ite_false]
      rw [φ.map_add, φ.map_mul, φ.map_pow]
      change f (syndrome y u _ ^ q) + z ^ q * f (syndrome y v _ ^ q) = _
      rw [← syndrome_frobenius q y hfix, ← syndrome_frobenius q y hfix,
        map_syndrome, map_syndrome]
      simpa only [w, hb, ite_false, one_mul] using
        (Principal.syndrome_linear x (fun i => f (u i ^ q))
          (fun i => f (v i ^ q)) 1 (z ^ q) _).symm
  have hnode (i : ι) :
      (P 0).eval (x i) * w 0 i + (P 1).eval (x i) * w 1 i =
        (out.map φ).eval (x i) := by
    simpa only [P, x, w, ite_true, one_ne_zero, ite_false] using hnodes i
  have hann : W.transpose * M = 0 := by
    apply Matrix.ext
    intro d j
    have ha : 0 < a := by have := d.isLt; omega
    let B (b : Fin 2) : E[X] := P b * Polynomial.X ^ d.val
    have hb (b : Fin 2) : (B b).natDegree ≤ a - 1 :=
      natDegree_mul_le.trans (by rw [natDegree_X_pow]; have := hP b; have := d.isLt; omega)
    have he (i : ι) : (B 0).eval (x i) * w 0 i + (B 1).eval (x i) * w 1 i =
        ((out.map φ) * Polynomial.X ^ d.val).eval (x i) := by
      simp only [B, eval_mul, eval_pow, eval_X]
      rw [← hnode i]
      ring
    have hdeg : ((out.map φ) * Polynomial.X ^ d.val).degree < ((k + (a - 1) : ℕ) : WithBot ℕ) := by
      have h := Strata.degree_mul_lt_add (Polynomial.X (R := E) ^ d.val) (out.map φ) d.val
        (k + H) (by simp) (degree_map_le.trans_lt houtput)
      rw [mul_comm] at h
      apply h.trans_le
      exact_mod_cast (show k + H + d.val ≤ k + (a - 1) by have := d.isLt; omega)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, W, K1_6.shifts,
      Fintype.sum_prod_type, Fin.sum_univ_two, hmom]
    have heq : a - 1 + 1 = a := by omega
    have hcontract (b : Fin 2) :
        syndrome x (fun i => (B b).eval (x i) * w b i) j.val =
          ∑ l : Fin a, (B b).coeff l.val * syndrome x (w b) (l.val + j.val) := by
      have h := Strata.syndrome_polynomial_multiple x (w b) (B b) (a - 1) j.val (hb b)
      rw [Fin.sum_univ_eq_sum_range (fun n => (B b).coeff n * syndrome x (w b) (n + j.val))] at h ⊢
      simpa only [heq] using h
    change (∑ l : Fin a, (B 0).coeff l.val * syndrome x (w 0) (l.val + j.val)) +
      (∑ l : Fin a, (B 1).coeff l.val * syndrome x (w 1) (l.val + j.val)) = 0
    rw [← hcontract 0, ← hcontract 1]
    have hlin := Principal.syndrome_linear x (fun i => (B 0).eval (x i) * w 0 i)
      (fun i => (B 1).eval (x i) * w 1 i) 1 1 j.val
    simp only [one_mul] at hlin
    rw [← hlin]
    simp_rw [he]
    apply Strata.syndrome_eval_zero x (f.injective.comp hy) _ _ _ hdeg
    have := j.isLt
    omega
  have hmul : M.transpose * W = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using
      congrArg Matrix.transpose hann
  have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero hmul
  rw [Matrix.rank_transpose, shifts_rank P a H hH hP hnz,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  change M.rank ≤ a + H
  omega


private theorem graph_entry {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (x u v : ι → F) (a R : ℕ) (i : Fin 2 × Fin a) (j : Fin (R + 1)) :
    let s (w : ι → F) := syndrome x w (i.2.val + j.val)
    (Polynomial.eval₂RingHom (RingHom.id F[X]) (Polynomial.X (R := F) ^ q))
      (if i.1 = 0 then C (C (s u) + Polynomial.X (R := F) * C (s v))
       else C (C (s u ^ q)) + Polynomial.X (R := F[X]) * C (C (s v ^ q))) =
        stacked q x u v a R i j := by
  dsimp only
  unfold stacked hankel
  split_ifs <;>
    simp only [coe_eval₂RingHom, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, RingHom.id_apply]

/-- The reduced relation survives on every subset. Its shifts give the
required independent left dependencies on the formal Frobenius graph. -/
theorem formal_graph_rank_le {u : Words} {D D' : Finset I} {H a : ℕ}
    (Q : ReducedRelation u D H) (hsub : D' ⊆ D) (hH : H ≤ a)
    (hD : D'.card = 131072 + a + (a + H)) :
    ((planeMatrix u D' a (a + H)).map
      ((algebraMap K[X] Frac).comp graphHom)).rank ≤ a + H := by
  classical
  let x : D' → K := fun i => node i.val
  let v (b : Fin 2) (i : D') := u b i.val
  let φ := algebraMap K[X] Frac
  have hm : ((planeMatrix u D' a (a + H)).map (φ.comp graphHom)) =
      (stacked p x (v 0) (v 1) a (a + H)).map φ := by
    apply Matrix.ext
    intro i j
    exact congrArg φ (graph_entry p x (v 0) (v 1) a (a + H) i j)
  rw [hm]
  have hn : GraphNodes p x (v 0) (v 1) φ Q.U Q.V Q.output := by
    intro i
    have h := congrArg φ (Q.nodes i.val (fun hi => (Finset.mem_sdiff.mp hi).2 (hsub i.property)))
    simpa only [x, v, RingHom.comp_apply, map_add, map_mul, map_pow, eval_map_apply] using h
  exact stacked_rank_le (F := K) (E := Frac) (ι := D') p x (v 0) (v 1)
    (IRSProfile.domain.injective.comp Subtype.val_injective)
    (fun i => Native.native_domain_fixed i.val) φ (IsFractionRing.injective K[X] Frac)
    131072 a H hH (by rw [Fintype.card_coe, hD]) Q.U Q.V Q.output Q.nonzero Q.height
    Q.output_degree hn

end
end K21_2_3
end Port_K1_2_3FormalRank

section Port_K1_2Apolar
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000

namespace K21_2
noncomputable section

open Polynomial Matrix FrobeniusLocator K1_1
open ProximityPrize.Benchmark

private def nativeMoments (u : K21.Words) : Fin 2 → ℕ → K21.Frac :=
  fun b j => algebraMap K21.K[X] K21.Frac
    (Principal.parameterSyndromes K21.p K21.node (u 0) (u 1) b j)

private theorem independent_nativeMoments (u : K21.Words)
    (h : ¬ K21.TypeAtMostOne u) : IndependentMoments (nativeMoments u) 131072 := by
  classical
  unfold IndependentMoments
  by_contra! hall
  apply h
  unfold K21.TypeAtMostOne Principal.TypeOneSyndromes
  rw [IRSProfile.card_index]
  intro i j
  apply IsFractionRing.injective K21.K[X] K21.Frac
  simpa [nativeMoments, Principal.parameterSyndromes, map_mul] using hall i j

private theorem locator_matrix (u : K21.Words) :
    Principal.recurrenceMatrix (nativeMoments u) 131072 82014 =
      (K21.twoBlock u).map (algebraMap K21.K[X] K21.Frac) :=
  Principal.recurrenceMatrix_parameter (algebraMap K21.K[X] K21.Frac)
    K21.p K21.node (u 0) (u 1) 131072 82014

private theorem locator_nullity (u : K21.Words) :
    sliceDim (nativeMoments u) 131072 82015 = K21.nullity u := by
  rw [sliceDim_succ (nativeMoments u) 131072 82014, locator_matrix]
  rfl

private theorem principal_of_one_active (u : K21.Words) (a : ℕ) (ha : a ≤ 82014)
    (hone : sliceDim (nativeMoments u) 131072 (a+1) = 1)
    (hnull : K21.nullity u = 82015-a) : K21.HomogeneousPrincipal u := by
  have hpos : 0 < sliceDim (nativeMoments u) 131072 (a+1) := by omega
  have hdim : sliceDim (nativeMoments u) 131072 82015 = (82014-a)+1 := by
    rw [locator_nullity]
    omega
  obtain ⟨g, hg, hdeg, hfac⟩ := principal_of_slice (nativeMoments u) 131072 a 82014
    ha (by decide) hpos hdim
  refine ⟨a, g, hg, hdeg, ha, fun P hP => ?_⟩
  rw [← locator_matrix]
  exact hfac P hP

/-- The binary level profile uses positive nullity, with no lower
threshold beyond positivity. -/
theorem two_active_of_positive (u : K21.Words) (hpos : 0 < K21.nullity u)
    (htype : ¬ K21.TypeAtMostOne u) (hprincipal : ¬ K21.HomogeneousPrincipal u) :
    Nonempty (K21.TwoActive u) := by
  obtain ⟨a, b, c, hab, hbc, hc, hsum, hdim⟩ := level_profile
    (nativeMoments u) 131072 (independent_nativeMoments u htype)
  have hloc := hdim 82015 (by decide)
  rw [locator_nullity] at hloc
  have hinactive : 82014 < c := by omega
  have ha : a ≤ 82014 := by omega
  have hb : b ≤ 82014 := by
    by_contra hb
    have hsmall := hdim (a+1) (by omega)
    exact hprincipal (principal_of_one_active u a ha (by omega) (by omega))
  refine ⟨⟨a, b, c, hab, hb, hinactive, hc, hsum, by omega, ?_⟩⟩
  exact level_of_profile _ _ _ _ _ hdim

end
end K21_2
end Port_K1_2Apolar

section Port_K1_2Saturation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

namespace K21_2
noncomputable section

open Polynomial Matrix FrobeniusLocator K21
open ProximityPrize.Benchmark

private theorem eval_atSlope (P : Bivar) (a γ : K) :
    (atSlope P γ).eval a = (P.eval (C a)).eval γ := by
  simpa only [atSlope, Polynomial.coe_evalRingHom, Polynomial.eval_C] using
    (Polynomial.eval_map_apply (Polynomial.evalRingHom γ) (C a) (p := P))

private theorem atSlope_constant (G : K[X]) (γ : K) :
    atSlope (G.map C) γ = G := by
  rw [atSlope, Polynomial.map_map]
  have h : (Polynomial.evalRingHom γ).comp C = RingHom.id K := by
    ext a
    simp
  rw [h, Polynomial.map_id]

private theorem twoBlock_atSlope (u : Words) (γ : K) :
    ((twoBlock u).map (evalRingHom γ)) =
      Strata.conjugateHankel (Strata.twoConjugations (frobenius K p))
        node (fun i => u 0 i + γ * u 1 i) 49058 82014 := by
  rw [twoBlock, Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval]
  have h : (fun b : Fin 2 => iterateFrobenius K p b.val) =
      Strata.twoConjugations (frobenius K p) := by
    funext b
    fin_cases b
    · exact iterateFrobenius_zero K p
    · exact iterateFrobenius_one K p
  rw [h]

private theorem rank_at_normal {u : Words} (T : TwoActive u) {γ : K} (hγ : Normal u γ) :
    ((twoBlock u).map (evalRingHom γ)).rank = 49058 + T.height := by
  change _ = stackRank u at hγ
  rw [hγ, actual_stackRank]
  have := T.degreeSum
  have := T.nullitySum
  have := T.top
  unfold TwoActive.height
  omega

/-- The original stack has the same rank as its two evaluated error blocks. -/
private theorem error_rank {u : Words} {γ : K} (M : BadMark u γ)
    (E : Finset I) (hE : E.card ≤ 82014)
    (hEagree : ∀ i ∉ E, u 0 i + γ * u 1 i = M.decoder.eval (node i)) :
    ((twoBlock u).map (evalRingHom γ)).rank =
      (Strata.errorTwoMatrix (frobenius K p) (fun i : E => node i.val)
        (fun i : E => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)) 49058).rank := by
  have hfix : ∀ b i, Strata.twoConjugations (frobenius K p) b (node i) = node i := by
    intro b i
    fin_cases b <;> simp [Strata.twoConjugations, frobenius_def, Native.native_domain_fixed]
  have h := Strata.conjugateHankel_error_rank
    (Strata.twoConjugations (frobenius K p)) node (fun i => u 0 i + γ * u 1 i)
    IRSProfile.domain.injective hfix M.decoder 131072 49058 82014 M.degree
    (by rw [IRSProfile.card_index]) E (by omega) hEagree
  rw [Strata.conjugateErrors_two] at h
  rw [twoBlock_atSlope]
  exact h

/-- When the distinct common error roots exhaust the gcd degree, their
monic locator has the same divisors as the gcd. -/
private theorem commonGCD_of_roots (U V : K[X]) (hV : V ≠ 0) (S : Finset I)
    (hroots : ∀ i ∈ S, (GCDMonoid.gcd U V).eval (node i) = 0)
    (hcard : S.card = (GCDMonoid.gcd U V).natDegree) :
    IsCommonGCD (locator node S) U V := by
  have hG : GCDMonoid.gcd U V ≠ 0 := gcd_ne_zero_of_right hV
  have hdiv := Strata.locator_dvd_of_eval_zero node IRSProfile.domain.injective S _ hroots
  have hassoc := Polynomial.associated_of_dvd_of_natDegree_le hdiv hG
    (by rw [locator_natDegree, hcard])
  exact ⟨(locator_monic node S).ne_zero, hdiv.trans (gcd_dvd_left U V),
    hdiv.trans (gcd_dvd_right U V), fun H hHU hHV => (dvd_gcd hHU hHV).trans hassoc.dvd'⟩

private theorem lift_dvd_atSlope {P : Bivar} {G : K[X]} (γ : K) (h : G.map C ∣ P) :
    G ∣ atSlope P γ := by
  have h' := map_dvd (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) h
  change atSlope (G.map C) γ ∣ atSlope P γ at h'
  rwa [atSlope_constant] at h'

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

/-- Normal saturation depends on the height being strictly below the
ordinary row count. The same argument covers the middle prefix. -/
theorem saturation_of_height (u : Words) (T : TwoActive u) (R : Relation T)
    (hH : T.height < 49058) : NormalSaturation R := by
  classical
  intro γ hγ M
  let U := atSlope (leftU R) γ
  let V := atSlope (leftV R) γ
  let E : Finset I := Finset.univ.filter (fun i => M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i)
  let e : E → K := fun i => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)
  let x : E → K := fun i => node i.val
  have hEagree (i : I) (hi : i ∉ E) : u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm h⟩)
  have hEcard : E.card ≤ 82014 := by
    have hsub : E ⊆ Finset.univ \ M.support := by
      intro i hi
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hs => ?_⟩
      exact (Finset.mem_filter.mp hi).2 (M.hits i hs)
    have h := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      IRSProfile.card_index] at h
    have := M.agreement
    omega
  have hfit : 131072 + T.height ≤ M.support.card := by
    have := M.agreement
    omega
  have hfix (i : I) : frobenius K p (node i) = node i := Native.native_domain_fixed i
  obtain ⟨hpair, hrel⟩ :=
    Strata.certificate_specializes p node (u 0) (u 1) 131072 T.height R γ
  have hUle : U.natDegree ≤ T.height := hrel.degree_U
  have hVle : V.natDegree ≤ T.height := hrel.degree_V
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have he (i : E) : e i ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp i.property).2)
  have herror (i : E) : U.eval (x i) * e i + V.eval (x i) * frobenius K p (e i) = 0 :=
    Strata.certificate_error_identity p node (u 0) (u 1) IRSProfile.domain.injective
      Native.native_domain_fixed 131072 T.height R γ M.support hfit M.decoder M.degree M.hits i.val
  have hrank : (Strata.errorTwoMatrix (frobenius K p) x e 49058).rank = 49058 + T.height :=
    (error_rank M E hEcard hEagree).symm.trans (rank_at_normal T hγ)
  obtain ⟨hU, hV⟩ := Strata.saturated_coefficients_nonzero (frobenius K p) x e hx U V
    T.height 49058 hUle hVle hpair hH he herror hrank
  let G := GCDMonoid.gcd U V
  let C₀ := (Finset.univ : Finset E).filter (fun i => G.eval (x i) = 0)
  let S := C₀.image (fun i : E => i.val)
  obtain ⟨hC, hsum, _⟩ := Strata.normal_error_three_rank (frobenius K p) x e hx
    (fun i => hfix i.val) U V T.height 49058 hUle hVle hpair hH he herror hrank
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
end K21_2
end Port_K1_2Saturation

section Port_K1_2Counting
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace K21_2
noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K21

local instance : NeZero (131072 : ℕ) := ⟨by decide⟩

/-- The donor's exact-support pruning argument, instantiated on the
benchmark's stacked matrix and the small shortened-domain core. -/
theorem rank_book (u : Words) (hfirst : firstRank u = 49058) (Γ : Finset K) :
    (abnormalSlopes u Γ).card ≤ rankReserve (nullity u) := by
  classical
  have hb := Strata.two_block_rank_exception_count p node (u 0) (u 1) 49058 82014
    (nullity u) (actual_stackRank u) hfirst (abnormalSlopes u Γ) (by
      intro γ hγ
      rw [← actual_stackRank u]
      exact (Finset.mem_filter.mp hγ).2)
  have he : 82014 + 1 - nullity u - 49058 = 32957 - nullity u := by omega
  rw [he] at hb
  exact hb

theorem padding_le_eight (r : ℕ) : padding r ≤ 8 := by
  unfold padding
  split_ifs <;> omega

theorem fixedLimit_le (r : ℕ) : fixedLimit r ≤ 14678 := by
  exact le_rfl

theorem planePrice_nonneg (A a b C : ℕ) : 0 ≤ planePrice A a b C := by
  dsimp only [planePrice]
  split_ifs
  · unfold oldPlanePrice
    positivity
  · apply le_min
    · unfold oldPlanePrice
      positivity
    · apply le_trans _ (le_max_left _ _)
      unfold oldPlanePrice
      positivity

/-- Apply one child count per deletion union and keep the rational child
price through the finite incidence inequality. -/
theorem padded_count {u : Words} {D : Finset I} {Γ : Finset K} {r g : ℕ}
    (F : PaddedFamily u D Γ r g) (hr : 7 ≤ r) (hr16 : r ≤ 16) (hg : g ≤ fixedLimit r)
    (hchild : ∀ J ∈ D.powersetCard (deletionSize r),
      ((childSlopes F J).card : ℚ) ≤ nativePlanePrice r g) :
    (Γ.card : ℚ) ≤ incidenceRatio r g * nativePlanePrice r g := by
  classical
  have hg' := hg.trans (fixedLimit_le r)
  have hj := padding_le_eight r
  let q := nativePlanePrice r g
  let n := q.num.toNat
  let d := q.den
  have hd : (0 : ℚ) < d := by exact_mod_cast Rat.den_pos q
  have hn : (n : ℚ) = (q.num : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg]
    exact Rat.num_nonneg.mpr (planePrice_nonneg _ _ _ _)
  have hq : (n : ℚ) / d = q := by rw [hn, Rat.num_div_den]
  have hfit : r - 1 + padding r ≤ 82014 - g := by omega
  have hden : 0 < (incidenceDenominator r g : ℚ) := by
    unfold incidenceDenominator
    exact_mod_cast Nat.mul_pos (Nat.choose_pos hfit)
      (Nat.choose_pos (by omega : padding r ≤ 180130 - 1))
  have hcount := Mixed.shared_mixed_rational_count node (u 0) (u 1)
    IRSProfile.domain.injective D Γ 131072 180130 (82014 - g) (r - 1) (padding r) n d
    (fun γ => goodSet u D γ (F.decoder γ)) (fun γ => errorSet u D γ (F.decoder γ)) F.slack
    (by omega) hfit (by omega)
    (by
      intro γ hγ
      rcases F.witness γ hγ with ⟨hs, hS, hE, hbad⟩
      have hsub : goodSet u D γ (F.decoder γ) ⊆ D := by
        intro i hi
        exact (mem_filter.mp hi).1
      exact ⟨hs, hS, hE, Finset.sdiff_disjoint, union_subset sdiff_subset hsub, hbad⟩)
    (by
      intro J hJ
      have hh := hchild J hJ
      change ((childSlopes F J).card : ℚ) ≤ q at hh
      rw [← hq] at hh
      have hmul := (le_div_iff₀ hd).mp hh
      have hc : (childSlopes F J).card * d ≤ n := by exact_mod_cast hmul
      have hsame : childSlopes F J = Γ.filter (fun γ =>
          J ∈ Mixed.mixedDeletions node (u 0) (u 1) 131072
            (r - 1 - F.slack γ + padding r) (F.slack γ + padding r)
            (errorSet u D γ (F.decoder γ)) (goodSet u D γ (F.decoder γ))) := by
        ext γ
        simp only [childSlopes, mem_filter]
        unfold mixedChoices Mixed.mixedDeletions Mixed.goodDeletions JointOn Mixed.JointOn
        rfl
      rw [hsame, mul_comm] at hc
      exact hc)
  change d * incidenceDenominator r g * Γ.card ≤ D.card.choose (deletionSize r) * n at hcount
  rw [F.domain_card] at hcount
  have hcountQ : (d : ℚ) * incidenceDenominator r g * Γ.card ≤
      ((262144 - g).choose (deletionSize r) : ℚ) * n := by exact_mod_cast hcount
  change (Γ.card : ℚ) ≤ incidenceRatio r g * q
  rw [← hq, incidenceRatio, div_mul_div_comm]
  apply (le_div_iff₀ (mul_pos hden hd)).mpr
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hcountQ

end
end K21_2
end Port_K1_2Counting

section Port_K1_2Arithmetic
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K21_2

private theorem new_price_mono (β : ℚ) (A a x y : ℕ)
    (hβ : 0 ≤ β) (ha : 0 < a) (hxy : x ≤ y) :
    newPlanePrice β A a x ≤ newPlanePrice β A a y := by
  have hx : (0 : ℚ) ≤ x := by positivity
  have hy : (0 : ℚ) ≤ y := by positivity
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hxy' : (x : ℚ) ≤ y := by exact_mod_cast hxy
  have hfrac : (x : ℚ) / (a + x) ≤ y / (a + y) := by
    apply (div_le_div_iff₀ (by linarith : (0 : ℚ) < a + x)
      (by linarith : (0 : ℚ) < a + y)).mpr
    nlinarith
  have hsquare : (x : ℚ)^2 / (a + x) ≤ (y : ℚ)^2 / (a + y) := by
    calc
      (x : ℚ)^2 / (a + x) = x * (x / (a + x)) := by ring
      _ ≤ y * (y / (a + y)) := mul_le_mul hxy' hfrac (by positivity) hy
      _ = (y : ℚ)^2 / (a + y) := by ring
  calc
    newPlanePrice β A a x = 2 * β * ((x : ℚ)^2 / (a + x) * (A + a + x)) := by
      unfold newPlanePrice
      ring
    _ ≤ 2 * β * ((y : ℚ)^2 / (a + y) * (A + a + y)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hsquare (by linarith) (by positivity) (by positivity)
    _ = newPlanePrice β A a y := by unfold newPlanePrice; ring

private def newNativePrice (r g : ℕ) : ℚ :=
  let a := childRows r
  let A := 131072 + a
  newPlanePrice (curveBeta A a (cutoff r)) A a (reducedHeight r g)

private theorem new_native_mono (r lo g : ℕ) (hl : lo ≤ g) :
    newNativePrice r g ≤ newNativePrice r lo := by
  have hj := padding_le_eight r
  dsimp only [newNativePrice]
  apply new_price_mono
  · unfold curveBeta
    positivity
  · unfold childRows
    omega
  · unfold reducedHeight
    omega

private theorem threshold_check (r : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16) :
    let a := childRows r
    let A := 131072 + a
    let q := planeThreshold A a (cutoff r)
    q < reducedHeight r (fixedLimit r) ∧
      oldPlanePrice A a q ≤ newNativePrice r (fixedLimit r) := by
  interval_cases r <;> decide +kernel

private theorem plane_le_new (r g : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hg : g ≤ fixedLimit r) : nativePlanePrice r g ≤ newNativePrice r g := by
  have h := threshold_check r hr hr16
  dsimp only at h
  have hH : reducedHeight r (fixedLimit r) ≤ reducedHeight r g := by
    unfold reducedHeight
    omega
  have hq := h.1.trans_le hH
  dsimp only [nativePlanePrice, planePrice]
  rw [ite_eq_right (not_le.mpr hq)]
  change min _ (max _ (newNativePrice r g)) ≤ newNativePrice r g
  apply min_le_of_right_le
  exact max_le (h.2.trans (new_native_mono r g _ hg)) le_rfl

private theorem reserve_le (r lo g : ℕ) (hr : 7 ≤ r) (hl : lo ≤ g) :
    extraReserve r g ≤ extraReserve r lo := by
  have hH : reducedHeight r g ≤ reducedHeight r lo := by unfold reducedHeight; omega
  have hd : 49058 - reducedHeight r lo ≤ 49058 - reducedHeight r g := by omega
  have hdpos : 0 < 49058 - reducedHeight r lo := by unfold reducedHeight; omega
  have hz :
      (2130706433 * 49058 + reducedHeight r g) / (49058 - reducedHeight r g) ≤
      (2130706433 * 49058 + reducedHeight r lo) / (49058 - reducedHeight r lo) :=
    (Nat.div_le_div_right (Nat.add_le_add_left hH _)).trans (Nat.div_le_div_left hd hdpos)
  have hn : 49058 / (49058 - reducedHeight r g) ≤ 49058 / (49058 - reducedHeight r lo) :=
    Nat.div_le_div_left hd hdpos
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hH) hz)
    (Nat.mul_le_mul_right (2130706433 + 1) hn)

-- The descending factorial evaluates using recursion on the small
-- lower argument of the binomial coefficient.
private def fastChoose (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

private theorem fastChoose_eq (n k : ℕ) : fastChoose n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

private def intervalRatio (r lo hi : ℕ) : ℚ :=
  (fastChoose (262144 - lo) (deletionSize r) : ℚ) /
    (fastChoose (82014 - hi) (r - 1 + padding r) * fastChoose (180130 - 1) (padding r) : ℕ)

private theorem ratio_le_interval (r g lo hi : ℕ) (hr16 : r ≤ 16)
    (hl : lo ≤ g) (hh : g ≤ hi) (hhi : hi ≤ fixedLimit r) :
    incidenceRatio r g ≤ intervalRatio r lo hi := by
  have hj := padding_le_eight r
  have hhi' := hhi.trans (fixedLimit_le r)
  have htop := Nat.choose_le_choose (deletionSize r) (show 262144 - g ≤ 262144 - lo by omega)
  have hbot : incidenceDenominator r hi ≤ incidenceDenominator r g := by
    unfold incidenceDenominator
    exact Nat.mul_le_mul_right _ (Nat.choose_le_choose _ (by omega))
  have hpos : 0 < incidenceDenominator r hi := by
    unfold incidenceDenominator
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hpos' : (0 : ℚ) < incidenceDenominator r hi := by exact_mod_cast hpos
  simp only [intervalRatio, fastChoose_eq, incidenceRatio]
  change ((262144 - g).choose (deletionSize r) : ℚ) / incidenceDenominator r g ≤
    ((262144 - lo).choose (deletionSize r) : ℚ) / incidenceDenominator r hi
  exact div_le_div₀ (by positivity) (by exact_mod_cast htop) hpos' (by exact_mod_cast hbot)

private def intervalBound (r lo hi : ℕ) : ℚ :=
  ((rankReserve r + extraReserve r lo : ℕ) : ℚ) +
    intervalRatio r lo hi * newNativePrice r lo

private theorem native_le_interval (r g lo hi : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hl : lo ≤ g) (hh : g ≤ hi) (hhi : hi ≤ fixedLimit r) :
    ((rankReserve r + extraReserve r g : ℕ) : ℚ) +
      incidenceRatio r g * nativePlanePrice r g ≤ intervalBound r lo hi := by
  unfold intervalBound
  apply add_le_add
  · exact_mod_cast Nat.add_le_add_left (reserve_le r lo g hr hl) (rankReserve r)
  · exact mul_le_mul (ratio_le_interval r g lo hi hr16 hl hh hhi)
      ((plane_le_new r g hr hr16 (hh.trans hhi)).trans (new_native_mono r lo g hl))
      (planePrice_nonneg _ _ _ _) (by unfold intervalRatio; positivity)

private def endpoints : ℕ → List ℕ
  | 7 => [14678]
  | 8 => [14678]
  | 9 => [14678]
  | 10 => [14678]
  | 11 => [14678]
  | 12 => [14678]
  | 13 => [14678]
  | 14 => [13380, 14678]
  | 15 => [9498, 14678]
  | 16 => [6117, 9629, 11725, 13014, 13826, 14345, 14678]
  | _ => []

private def certified (r : ℕ) : ℕ → List ℕ → Bool
  | lo, [] => decide (fixedLimit r < lo)
  | lo, hi :: rest =>
    decide (lo ≤ hi ∧ hi ≤ fixedLimit r ∧ intervalBound r lo hi ≤ 200000000000000000) &&
      certified r (hi + 1) rest

private theorem covers (r lo g : ℕ) (cuts : List ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hl : lo ≤ g) (hg : g ≤ fixedLimit r) (hcert : certified r lo cuts = true) :
    ((rankReserve r + extraReserve r g : ℕ) : ℚ) +
      incidenceRatio r g * nativePlanePrice r g ≤ 200000000000000000 := by
  induction cuts generalizing lo with
  | nil =>
    have he : fixedLimit r < lo := of_decide_eq_true hcert
    omega
  | cons hi rest ih =>
    obtain ⟨hcurrent, hrest⟩ := Bool.and_eq_true_iff.mp hcert
    obtain ⟨_, hhi, hbound⟩ :
        lo ≤ hi ∧ hi ≤ fixedLimit r ∧ intervalBound r lo hi ≤ 200000000000000000 :=
      of_decide_eq_true hcurrent
    by_cases hh : g ≤ hi
    · exact (native_le_interval r g lo hi hr hr16 hl hh hhi).trans hbound
    · exact ih (hi + 1) (by omega) hrest

private theorem endpoints_checked (r : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16) :
    certified r 0 (endpoints r) = true := by
  interval_cases r <;> decide +kernel

theorem arithmetic_bound (r g : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16) (hg : g ≤ fixedLimit r) :
    ((rankReserve r + extraReserve r g : ℕ) : ℚ) +
      incidenceRatio r g * nativePlanePrice r g ≤ 200000000000000000 :=
  covers r 0 g (endpoints r) hr hr16 (Nat.zero_le g) hg (endpoints_checked r hr hr16)

end K21_2
end Port_K1_2Arithmetic

section Port_K1_2Split
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace K21_2
noncomputable section

open Polynomial Finset FrobeniusLocator ProximityPrize.Benchmark
open K21

/-- The primitive wide left pair has the shifted-minor seed-height bound. -/
def c1 : Prop :=
  ∀ (u : Words), MiddleGuard u → ∀ (T : TwoActive u) (R : Relation T),
    ∀ i, (R.coefficients i).natDegree ≤ 6489210095

/-- Once the original rank drops have been removed, only the reduced
resultant and normalization reserves are used to prepare the marked family. -/
def c2 : Prop :=
  ∀ (u : Words), MiddleGuard u → ∀ (T : TwoActive u) (R : Relation T),
    ¬ MovingGCD R → ¬ InvalidLeft R → NormalSaturation R →
    ∀ Γ : Finset K, Γ.Nonempty → BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) →
      let r := nullity u
      let g := (fixedNodes R).card
      let D := Finset.univ \ fixedNodes R
      g ≤ fixedLimit r →
        ∃ book : Finset K, book ⊆ Γ ∧ book.card ≤ extraReserve r g ∧
          ∃ _ : PaddedFamily u D (Γ \ book) r g,
          ∃ Q : ReducedRelation u D (reducedHeight r g),
            ∀ γ ∈ Γ \ book, RegularAt Q γ

/-- At a fixed deletion union there is one exact child plane across the
physical error sizes. The marked decoder is unchanged by puncturing. -/
def c3 : Prop :=
  ∀ (u : Words) (D : Finset I) (Γ : Finset K) (r g : ℕ),
    7 ≤ r → r ≤ 16 → g ≤ fixedLimit r →
    ∀ (F : PaddedFamily u D Γ r g) (Q : ReducedRelation u D (reducedHeight r g)),
      (∀ γ ∈ Γ, RegularAt Q γ) →
      ∀ J ∈ D.powersetCard (deletionSize r), (childSlopes F J).Nonempty →
        RegularPlane u (D \ J) (childRows r) (childErrors r g)
          (childSlopes F J) F.decoder

/-- The carried primitive-box consumer for one regular punctured input. -/
def c4 : Prop :=
  ∀ (u : Words) (D : Finset I) (Γ : Finset K) (P : K → K[X]) (a b C : ℕ),
    1 ≤ b → b ≤ a → 1 ≤ C → C ≤ a →
    RegularPlane u D a (a + b) Γ P →
      (Γ.card : ℚ) ≤ planePrice (131072 + a) a b C

private theorem main_height_guards (r g : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hg : g ≤ fixedLimit r) :
    1 ≤ reducedHeight r g ∧ reducedHeight r g ≤ childRows r ∧
      1 ≤ cutoff r ∧ cutoff r ≤ childRows r := by
  have hpad := padding_le_eight r
  have hsmall := hg.trans (fixedLimit_le r)
  unfold reducedHeight childRows cutoff
  split_ifs <;> omega

private theorem normal_count_large_g (hcore : ShortenedCap 247465 3680066762208196)
    (u : Words) (T : TwoActive u) (R : Relation T) (hsat : NormalSaturation R)
    (Γ : Finset K) (hΓ : BadFamily u Γ) (hn : ∀ γ ∈ Γ, Normal u γ)
    (hg : fixedLimit (nullity u) < (fixedNodes R).card) :
    Γ.card ≤ 3680066762208196 := by
  classical
  refine hcore (Finset.univ \ fixedNodes R) ?_ (u 0) (u 1) Γ ?_
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index]
    unfold fixedLimit at hg
    omega
  · intro γ hγ
    obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγ
    have sat := hsat γ (hn γ hγ) M
    refine ⟨M.support, ?_, M.agreement, ⟨M.decoder, M.degree, M.hits⟩, M.nonjoint⟩
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hi' => sat.fixed_errors i hi' (M.hits i hi)⟩

private theorem add_rank_book (u : Words) (Γ : Finset K) (hfirst : firstRank u = 49058)
    (b : ℕ) (hb : (normalSlopes u Γ).card ≤ b) :
    Γ.card ≤ rankReserve (nullity u) + b := by
  classical
  have hr := rank_book u hfirst Γ
  have hsplit := Finset.card_filter_add_card_filter_not (s := Γ) (p := Normal u)
  change (normalSlopes u Γ).card + (abnormalSlopes u Γ).card = Γ.card at hsplit
  omega

private theorem middle_count (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (u : Words) (hm : MiddleGuard u)
    (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ 200000000000000000 := by
  classical
  let r := nullity u
  have hr : 7 ≤ r := hm.1
  have hr16 : r ≤ 16 := hm.2.1
  have hfirst := hm.2.2.1
  have hrank : rankReserve r ≤ 70206777016408 := by
    unfold rankReserve
    have hh : 32957 - r ≤ 32950 := by omega
    have hmul := Nat.mul_le_mul_left 2130706433 hh
    omega
  obtain ⟨T⟩ := two_active_of_positive u (by omega) hm.2.2.2.1 hm.2.2.2.2.1
  let R : Relation T := Strata6921.native_lemmaT_of_two_active_level u r
    T.a T.b T.c hr T.ab T.active T.inactive T.top T.degreeSum T.nullitySum T.level
  have hH : T.height < 49058 := by
    have := T.degreeSum
    have := T.nullitySum
    have := T.top
    unfold TwoActive.height
    omega
  have hsat := saturation_of_height u T R hH
  let N := normalSlopes u Γ
  have hN : BadFamily u N := normal_badFamily hΓ
  have hn : ∀ γ ∈ N, Normal u γ := normal_on_normalSlopes
  by_cases hnon : N.Nonempty
  swap
  · have hnempty := Finset.not_nonempty_iff_eq_empty.mp hnon
    have hh := add_rank_book u Γ hfirst 0 (by change N.card ≤ 0; simp [hnempty])
    change Γ.card ≤ rankReserve r + 0 at hh
    omega
  by_cases hmov : MovingGCD R
  · have hcount := K21_6.normal_growth_count R (h1 u hm T R) hmov hsat N hN hn
    have hh := add_rank_book u Γ hfirst _ hcount
    change Γ.card ≤ rankReserve r + 1701107491143680 at hh
    omega
  have hinv : ¬ InvalidLeft R := by
    obtain ⟨γ, hγ⟩ := hnon
    obtain ⟨M⟩ := bad_mark u N hN γ hγ
    exact (hsat γ (hn γ hγ) M).valid
  let g := (fixedNodes R).card
  by_cases hg : g ≤ fixedLimit r
  · obtain ⟨book, hbook, hfee, F, Q, hreg⟩ := h2 u hm T R hmov hinv hsat N hnon hN hn hg
    obtain ⟨hb, hba, hc, hca⟩ := main_height_guards r g hr hr16 hg
    have hp := padded_count F hr hr16 hg (by
      intro J hJ
      by_cases hJE : (childSlopes F J).Nonempty
      · have hplane := h3 u _ _ r g hr hr16 hg F Q hreg J hJ hJE
        exact h4 u _ _ F.decoder (childRows r) (reducedHeight r g) (cutoff r) hb hba hc hca hplane
      · rw [Finset.not_nonempty_iff_eq_empty.mp hJE, Finset.card_empty, Nat.cast_zero]
        exact planePrice_nonneg _ _ _ _)
    have hsolid := Finset.card_sdiff_add_card_eq_card hbook
    have hsplit : Γ.card ≤ rankReserve r + ((N \ book).card + book.card) := by
      rw [hsolid]
      exact add_rank_book u Γ hfirst _ le_rfl
    have hsplit' : (Γ.card : ℚ) ≤ (rankReserve r : ℚ) + ((N \ book).card : ℚ) + book.card := by
      exact_mod_cast (by simpa only [Nat.add_assoc] using hsplit)
    have hfee' : (book.card : ℚ) ≤ extraReserve r g := by exact_mod_cast hfee
    have hprice := arithmetic_bound r g hr hr16 hg
    push_cast at hprice
    have hfinal : (Γ.card : ℚ) ≤ 200000000000000000 := by linarith
    exact_mod_cast hfinal
  · have hc := normal_count_large_g Row6921.puncture_247716 u T R hsat N hN hn (Nat.lt_of_not_ge hg)
    have hh := add_rank_book u Γ hfirst _ hc
    change Γ.card ≤ rankReserve r + 3680066762208196 at hh
    omega

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) : K21.c2 := by
  intro u Γ hu hΓ
  by_cases hd : firstRank u < 49058
  · exact (K21_3.proof u Γ hd hΓ).trans (by decide)
  have hfirst : firstRank u = 49058 := by have := firstRank_le u; omega
  by_cases hlow : nullity u ≤ 6
  · exact (Row6921.count_nullity_le_six u hfirst hlow Γ hΓ).trans (by decide)
  by_cases ht : TypeAtMostOne u
  · exact (Native6921.native_type_one_MCA_count u ht Γ hΓ).trans (by decide)
  by_cases hp : HomogeneousPrincipal u
  · exact (K21_4.proof u Γ hp hΓ).trans (by decide)
  by_cases hk : ConstantKernel u
  · exact (K21_5.proof u Γ hk hΓ).trans (by decide)
  exact middle_count h1 h2 h3 h4 u
    ⟨by omega, hu, hfirst, ht, hp, hk⟩ Γ hΓ

end
end K21_2
end Port_K1_2Split

section Port_K1_2_3Marks
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K21_2_3
noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K21 K21_2

theorem child_parameters (r g : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hg : g ≤ fixedLimit r) :
    reducedHeight r g ≤ childRows r ∧
      0 < childErrors r g ∧ childErrors r g + 1 < p ∧
      262144 - g - deletionSize r = 131072 + childRows r + childErrors r g := by
  have hp := padding_le_eight r
  have hg' := hg.trans (fixedLimit_le r)
  change _ ∧ _ ∧ childErrors r g + 1 < 2130706433 ∧ _
  simp only [childErrors, childRows, reducedHeight, deletionSize]
  omega

theorem child_mark {u : Words} {D : Finset I} {Γ : Finset K} {r g : ℕ}
    (F : PaddedFamily u D Γ r g) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hg : g ≤ fixedLimit r) {J : Finset I} {γ : K} (hγ : γ ∈ childSlopes F J) :
    γ ∈ Γ ∧ (F.decoder γ).degree < 131072 ∧
      (errorSet u (D \ J) γ (F.decoder γ)).card = childErrors r g ∧
      ¬ JointOn u (goodSet u (D \ J) γ (F.decoder γ)) := by
  classical
  obtain ⟨hΓ, hJ⟩ := Finset.mem_filter.mp hγ
  obtain ⟨hslack, _, herrors, _⟩ := F.witness γ hΓ
  let S := goodSet u D γ (F.decoder γ)
  let E := errorSet u D γ (F.decoder γ)
  change J ∈ mixedChoices u (r - 1 - F.slack γ + padding r) (F.slack γ + padding r) E S at hJ
  obtain ⟨⟨B, C⟩, hmem, rfl⟩ := Finset.mem_image.mp hJ
  obtain ⟨hB, hC⟩ := Finset.mem_product.mp hmem
  obtain ⟨hBE, hBc⟩ := Finset.mem_powersetCard.mp hB
  obtain ⟨hCS, _⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hC).1
  have hbad := (Finset.mem_filter.mp hC).2
  have hgood : goodSet u (D \ (B ∪ C)) γ (F.decoder γ) = S \ C := by
    ext i
    have hBnot (h : i ∈ B) : i ∉ S := (Finset.mem_sdiff.mp (hBE h)).2
    simp only [S, goodSet, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union] at hBnot ⊢
    tauto
  have herr : errorSet u (D \ (B ∪ C)) γ (F.decoder γ) = E \ B := by
    ext i
    have hCs (h : i ∈ C) : i ∈ S := hCS h
    simp only [E, errorSet, S, goodSet, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_union] at hCs ⊢
    tauto
  refine ⟨hΓ, F.degree γ hΓ, ?_, hgood.symm ▸ hbad⟩
  rw [herr, Finset.card_sdiff_of_subset hBE]
  change E.card = _ at herrors
  rw [herrors, hBc]
  have hp := padding_le_eight r
  have hg' := hg.trans (fixedLimit_le r)
  unfold childErrors childRows reducedHeight
  omega

theorem plane_at_slope (u : Words) (D : Finset I) (a R : ℕ) (γ : K) :
    (planeMatrix u D a R).map (onGraph γ) =
      Strata.conjugateHankel (Strata.twoConjugations (frobenius K p))
        (fun i : D => node i.val) (fun i : D => u 0 i.val + γ * u 1 i.val) a R := by
  apply Matrix.ext
  intro ⟨b, l⟩ j
  let x : D → K := fun i => node i.val
  have hs := Principal.syndrome_linear x (fun i : D => u 0 i.val)
    (fun i : D => u 1 i.val) 1 γ (l.val + j.val)
  simp only [one_mul] at hs
  let A := syndrome x (fun i : D => u 0 i.val) (l.val + j.val)
  let B := syndrome x (fun i : D => u 1 i.val) (l.val + j.val)
  have hpow : frobenius K p (A + γ * B) = A ^ p + γ ^ p * B ^ p := by
    simp only [map_add, map_mul, frobenius_def]
  fin_cases b
  · change (onGraph γ) (Polynomial.C (R := K[X]) (Polynomial.C (R := K) A + Polynomial.X (R := K) * Polynomial.C (R := K) B)) =
      syndrome x (fun i : D => u 0 i.val + γ * u 1 i.val) (l.val + j.val)
    simpa only [onGraph, coe_eval₂RingHom, eval₂_C, coe_evalRingHom, eval_add,
      eval_mul, eval_C, eval_X, A, B] using hs.symm
  · change (onGraph γ) (Polynomial.C (R := K[X]) (Polynomial.C (R := K) (A ^ p)) + Polynomial.X (R := K[X]) * Polynomial.C (R := K[X]) (Polynomial.C (R := K) (B ^ p))) =
      frobenius K p (syndrome x (fun i : D => u 0 i.val + γ * u 1 i.val) (l.val + j.val))
    rw [hs]
    change (onGraph γ) (Polynomial.C (R := K[X]) (Polynomial.C (R := K) (A ^ p)) + Polynomial.X (R := K[X]) * Polynomial.C (R := K[X]) (Polynomial.C (R := K) (B ^ p))) =
      frobenius K p (A + γ * B)
    rw [hpow]
    simp only [onGraph, coe_eval₂RingHom, eval₂_add, eval₂_mul, eval₂_C, eval₂_X,
      coe_evalRingHom, eval_C]


private theorem eval_atSlope (P : Bivar) (a γ : K) :
    (atSlope P γ).eval a = (P.eval (C a)).eval γ := by
  simpa only [atSlope, Polynomial.coe_evalRingHom, Polynomial.eval_C] using
    (Polynomial.eval_map_apply (Polynomial.evalRingHom γ) (C a) (p := P))

private theorem specialize_relation {u : Words} {D D' : Finset I} {H : ℕ}
    (Q : ReducedRelation u D H) (hsub : D' ⊆ D) (γ : K) :
    Strata.TwistedRelation (frobenius K p) (fun i : D' => node i.val)
      (fun i : D' => u 0 i.val + γ * u 1 i.val) 131072 H
      (atSlope Q.U γ) (atSlope Q.V γ) (atSlope Q.output γ) := by
  refine ⟨natDegree_map_le.trans (le_max_left _ _ |>.trans_eq Q.height),
    natDegree_map_le.trans (le_max_right _ _ |>.trans_eq Q.height),
    degree_map_le.trans_lt Q.output_degree, ?_⟩
  intro i
  have hn := Q.nodes i.val (by simp [hsub i.property])
  have he := congrArg (evalRingHom γ) hn
  simpa only [map_add, map_mul, coe_evalRingHom, eval_C, eval_X, eval_pow,
    ← eval_atSlope, frobenius_def, add_pow_expChar, mul_pow] using he

theorem evaluated_rank {u : Words} {D D' : Finset I} {H a : ℕ}
    (Q : ReducedRelation u D H) (hsub : D' ⊆ D) (hH : H ≤ a) (hR : 0 < a + H)
    (hD : D'.card = 131072 + a + (a + H))
    (γ : K) (hregular : RegularAt Q γ) (P : K[X]) (hP : P.degree < 131072)
    (hE : (errorSet u D' γ P).card = a + H) :
    ((planeMatrix u D' a (a + H)).map (onGraph γ)).rank = a + H := by
  classical
  let x : D' → K := fun i => node i.val
  let w : D' → K := fun i => u 0 i.val + γ * u 1 i.val
  let S := (goodSet u D' γ P).subtype (· ∈ D')
  let E := (errorSet u D' γ P).subtype (· ∈ D')
  have hgood (i : D') : i ∈ S ↔ P.eval (x i) = w i := by
    simp [S, goodSet, x, w, Finset.mem_subtype, i.property]
  have herr (i : D') : i ∈ E ↔ P.eval (x i) ≠ w i := by
    simp [E, errorSet, goodSet, x, w, Finset.mem_subtype, i.property]
  have hEc : E.card = a + H := by
    have hmap : E.map (Function.Embedding.subtype (· ∈ D')) = errorSet u D' γ P :=
      Finset.subtype_map_of_mem (fun i hi => (Finset.mem_sdiff.mp hi).1)
    rw [← Finset.card_map (f := Function.Embedding.subtype (· ∈ D')), hmap, hE]
  have hSize : Fintype.card D' = 131072 + a + (a + H) := by
    rw [Fintype.card_coe, hD]
  have hSc : 131072 + H ≤ S.card := by
    have hcard := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset D')) (p := fun i => P.eval (x i) = w i)
    have hS' : S = Finset.univ.filter (fun i => P.eval (x i) = w i) := by
      ext i
      simp [hgood]
    have hE' : E = Finset.univ.filter (fun i => P.eval (x i) ≠ w i) := by
      ext i
      simp [herr]
    rw [← hS', ← hE', Finset.card_univ, hSize, hEc] at hcard
    omega
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have hfix (i : D') : frobenius K p (x i) = x i := Native.native_domain_fixed i.val
  have hfix₂ (b : Fin 2) (i : D') : Strata.twoConjugations (frobenius K p) b (x i) = x i := by
    fin_cases b <;> simp [Strata.twoConjugations, hfix]
  have hnot (i : D') (hi : i ∉ E) : w i = P.eval (x i) :=
    (not_ne_iff.mp (fun hn => hi ((herr i).mpr hn))).symm
  rw [plane_at_slope, Strata.conjugateHankel_error_rank _ x w hx hfix₂
    P 131072 a (a + H) hP hSize.ge E (by omega) hnot, Strata.conjugateErrors_two]
  let e (i : E) := w i.val - P.eval (x i.val)
  let y (i : E) := x i.val
  let U := atSlope Q.U γ
  let V := atSlope Q.V γ
  have hrel (i : E) : U.eval (y i) * e i + V.eval (y i) * frobenius K p (e i) = 0 :=
    Strata.decoder_error_identity (frobenius K p) x w hx hfix 131072 H U V _
      (specialize_relation Q hsub γ) S hSc P hP (fun i hi => (hgood i).mp hi) i.val
  have hne (i : E) : e i ≠ 0 := sub_ne_zero.mpr ((herr i.val).mp i.property).symm
  have hunits (i : E) : U.eval (y i) ≠ 0 ∧ V.eval (y i) ≠ 0 :=
    Strata.coprime_relation_units _ U V (y i) (e i) hregular.1 (hne i) (hrel i)
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [hEc]; exact hR)
  have hU : U ≠ 0 := fun hz => (hunits ⟨i, hi⟩).1 (by rw [hz, eval_zero])
  have hV : V ≠ 0 := fun hz => (hunits ⟨i, hi⟩).2 (by rw [hz, eval_zero])
  have heq := Strata.error_two_rank_no_common (frobenius K p) y e
    (hx.comp Subtype.val_injective) U V H a hU hV hregular.2 hregular.1 hH hne
    (fun i => (hunits i).2) hrel
  simpa only [Fintype.card_coe, hEc, min_self] using heq

end
end K21_2_3
end Port_K1_2_3Marks

section Port_K1_2_4Split
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace K21_2_4

noncomputable section

open Polynomial Finset FrobeniusLocator
open K21 K21_2

/-- Remove the global fixed roots and recompute the simultaneous box, with
the same decoder marks and agreement. A constant box stops the family. -/
def c1 : Prop :=
  ∀ (u : Words) (D : Finset I) (Γ : Finset K) (P : K → K[X]) (a b : ℕ),
    1 ≤ b → b ≤ a → RegularPlane u D a (a+b) Γ P →
    Γ = ∅ ∨ ∃ (F : Finset I) (L : Bivar[X]), F ⊆ D ∧ F.card < b ∧
      (∀ γ ∈ Γ, F ⊆ errorSet u D γ (P γ)) ∧
      RegularPlane u (D \ F) a (a+(b-F.card)) Γ P ∧
      BoxedLocator u (D \ F) a (b-F.card) Γ P L

/-- On a mixed-coordinate curve, construct the two proper cofactor
representatives at each nonfixed grid root after removing curve-fixed errors. -/
def c2 : Prop :=
  ∀ (u : Words) (D : Finset I) (Γ : Finset K) (P : K → K[X]) (a b : ℕ),
    1 ≤ b → b ≤ a → RegularPlane u D a (a+b) Γ P →
    ∀ (L : Bivar[X]), BoxedLocator u D a b Γ P L →
    ∀ (Q : Bivar), Irreducible Q → 0 < seedDegree Q → 0 < Q.natDegree →
      Γ.Nonempty → (∀ γ ∈ Γ, onGraph γ Q = 0) →
      let d := a+b-(curveFixed D L Q).card
      0 < d → ∀ i ∈ D \ curveFixed D L Q,
        Nonempty (OppositeCuts u D Γ P Q a d i)

/-- The ordinary unique-decoding cap on an arbitrary punctured input with
agreement 131072+a and exact error count d strictly below a. -/
def c3 : Prop :=
  ∀ (u : Words) (D : Finset I) (Γ : Finset K) (P : K → K[X]) (a d : ℕ),
    d < a → D.card = 131072+a+d →
    (∀ γ ∈ Γ, (P γ).degree < 131072 ∧ (errorSet u D γ (P γ)).card = d ∧
      ¬ JointOn u (goodSet u D γ (P γ))) →
    Γ.card ≤ d + (131072+a+d)/(a-d+1)
private theorem restrict_plane {u D a b Γ P} (h : RegularPlane u D a (a+b) Γ P)
    (Q : Bivar) : RegularPlane u D a (a+b) (onCurve Γ Q) P :=
  ⟨h.domain_card, h.generic_rank, fun γ hγ => h.mark γ (Finset.mem_filter.mp hγ).1⟩

private theorem restrict_locator {u D a b Γ P L} (h : BoxedLocator u D a b Γ P L)
    (Q : Bivar) : BoxedLocator u D a b (onCurve Γ Q) P L :=
  ⟨h.degree, h.kernel, h.box, h.noFixed, fun γ hγ => h.fiber γ (Finset.mem_filter.mp hγ).1⟩

private theorem curveFixed_subset (D : Finset I) (L : Bivar[X]) (Q : Bivar) :
    curveFixed D L Q ⊆ D :=
  fun _ hi => (mem_curveFixed.mp hi).1

private theorem curveFixed_errors {u D a b Γ P L}
    (h : BoxedLocator u D a b Γ P L) {γ : K} (hγ : γ ∈ Γ)
    {Q : Bivar} (hQ : onGraph γ Q = 0) :
    curveFixed D L Q ⊆ errorSet u D γ (P γ) := by
  intro i hi
  obtain ⟨T, hT⟩ := (mem_curveFixed.mp hi).2
  apply (root_iff_error h hγ i).mp
  rw [hT, map_mul, hQ, zero_mul]

private theorem marks_after_puncture (u : Words) (D F : Finset I)
    (γ : K) (P : K[X]) (hF : F ⊆ errorSet u D γ P) :
    goodSet u (D \ F) γ P = goodSet u D γ P ∧
    errorSet u (D \ F) γ P = errorSet u D γ P \ F := by
  have hgood : goodSet u (D \ F) γ P = goodSet u D γ P := by
    ext i
    constructor
    · intro hi
      obtain ⟨hiD, hv⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hiD).1, hv⟩
    · intro hi
      obtain ⟨hiD, hv⟩ := Finset.mem_filter.mp hi
      have hin : i ∉ F := fun hiF => (Finset.mem_sdiff.mp (hF hiF)).2 hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hiD, hin⟩, hv⟩
  refine ⟨hgood, ?_⟩
  unfold errorSet
  rw [hgood]
  ext i
  simp only [Finset.mem_sdiff]
  tauto

/-- The two card identities use the same fixed set on both sides of the
incidence count. Every permitted puncture preserves the full good set. -/
private theorem punctured_curve_data {u D a b Γ P L}
    (hreg : RegularPlane u D a (a+b) Γ P) (h : BoxedLocator u D a b Γ P L)
    (Q : Bivar) (hΓ : Γ.Nonempty) (hQ : ∀ γ ∈ Γ, onGraph γ Q = 0) :
    let F := curveFixed D L Q
    let d := a+b-F.card
    (D \ F).card = 131072+a+d ∧
      ∀ γ ∈ Γ, (P γ).degree < 131072 ∧ (errorSet u (D \ F) γ (P γ)).card = d ∧
        ¬ JointOn u (goodSet u (D \ F) γ (P γ)) := by
  dsimp only
  obtain ⟨γ, hγ⟩ := hΓ
  have hle := Finset.card_le_card (curveFixed_errors h hγ (hQ γ hγ))
  rw [(hreg.mark γ hγ).2.1] at hle
  constructor
  · rw [Finset.card_sdiff_of_subset (curveFixed_subset D L Q), hreg.domain_card]
    omega
  · intro η hη
    have hsub := curveFixed_errors h hη (hQ η hη)
    obtain ⟨hg, he⟩ := marks_after_puncture u D (curveFixed D L Q) η (P η) hsub
    obtain ⟨hdegree, hcard, hbad, _⟩ := hreg.mark η hη
    rw [hg, he, Finset.card_sdiff_of_subset hsub, hcard]
    exact ⟨hdegree, rfl, hbad⟩

private theorem curve_root_incidence {u D a b Γ P L}
    (hreg : RegularPlane u D a (a+b) Γ P) (h : BoxedLocator u D a b Γ P L)
    (Q : Bivar) (hQ : ∀ γ ∈ Γ, onGraph γ Q = 0) (f : ℚ)
    (hcap : ∀ i ∈ D \ curveFixed D L Q,
      ((Γ.filter (fun γ => i ∈ errorSet u D γ (P γ))).card : ℚ) ≤ f) :
    ((a+b-(curveFixed D L Q).card : ℕ) : ℚ) * Γ.card ≤
      (D \ curveFixed D L Q).card * f := by
  let rel := fun i γ => i ∈ errorSet u D γ (P γ)
  apply rational_incidence _ _ rel _ f _ ?_
  · intro γ hγ
    have hsub := curveFixed_errors h hγ (hQ γ hγ)
    rw [← (hreg.mark γ hγ).2.1, ← Finset.card_sdiff_of_subset hsub]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hiE, hiF⟩ := Finset.mem_sdiff.mp hi
    exact (@Finset.mem_filter I (fun j => rel j γ)
      (fun j => Classical.propDecidable (rel j γ)) _ i).mpr
      ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hiE).1, hiF⟩, hiE⟩
  · intro i hi
    convert hcap i hi using 3
    ext γ
    simp only [Finset.mem_filter, rel]

private theorem old_curve (hcuts : c2) (hcore : c3) {u D a b Γ P L}
    (hb : 1 ≤ b) (hba : b ≤ a) (hreg : RegularPlane u D a (a+b) Γ P)
    (h : BoxedLocator u D a b Γ P L) (Q : Bivar) (hQ : Irreducible Q)
    (hzeros : ∀ γ ∈ Γ, onGraph γ Q = 0) :
    (Γ.card : ℚ) ≤ D.card / 2 * (seedDegree Q + Q.natDegree : ℕ) := by
  have hM : (131072 : ℚ) + a + (a+b) = D.card := by exact_mod_cast hreg.domain_card.symm
  have hweight : (1 : ℚ) ≤ D.card / 2 := by
    have ha : (0 : ℚ) ≤ a := by positivity
    have hbq : (0 : ℚ) ≤ b := by positivity
    linarith
  by_cases hcoord : seedDegree Q = 0 ∨ Q.natDegree = 0
  · have hc : (Γ.card : ℚ) ≤ (seedDegree Q + Q.natDegree : ℕ) := by
      exact_mod_cast coordinate_intersection Q hQ.ne_zero hcoord Γ hzeros
    exact hc.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hweight (show (0 : ℚ) ≤ (seedDegree Q + Q.natDegree : ℕ) by positivity))
  have hS : 0 < seedDegree Q := Nat.pos_of_ne_zero (fun hz => hcoord (Or.inl hz))
  have hT : 0 < Q.natDegree := Nat.pos_of_ne_zero (fun hz => hcoord (Or.inr hz))
  by_cases hne : Γ.Nonempty
  swap
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    positivity
  let d := a+b-(curveFixed D L Q).card
  let E := D \ curveFixed D L Q
  by_cases hd : d = 0
  · obtain ⟨hcard, hmark⟩ := punctured_curve_data hreg h Q hne hzeros
    change E.card = 131072+a+d at hcard
    have hc := hcore u E Γ P a d (by omega) hcard hmark
    rw [hd] at hc
    have hc' : Γ.card ≤ 131072+a := by
      simpa using hc.trans (by simpa using Nat.div_le_self (131072+a) (a+1))
    have hcq : (Γ.card : ℚ) ≤ 131072+a := by exact_mod_cast hc'
    have hDN : (131072 : ℚ) + a ≤ D.card := by
      rw [← hM]
      exact le_add_of_nonneg_right (by positivity)
    have hperim : (2 : ℚ) ≤ (seedDegree Q + Q.natDegree : ℕ) := by
      exact_mod_cast (show 2 ≤ seedDegree Q + Q.natDegree by omega)
    calc
      _ ≤ (D.card : ℚ) := hcq.trans hDN
      _ = (D.card : ℚ) / 2 * 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hperim (by positivity)
  have hdq : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
  have hinc := curve_root_incidence hreg h Q hzeros
    ((d : ℚ)/2 * (seedDegree Q + Q.natDegree : ℕ)) (by
      intro i hi
      obtain ⟨cut⟩ := hcuts u D Γ P a b hb hba hreg L h Q hQ hS hT
        hne hzeros (Nat.pos_of_ne_zero hd) i hi
      let G := Γ.filter (fun γ => i ∈ errorSet u D γ (P γ))
      have hf : (G.card : ℚ) ≤ (Q.natDegree : ℚ) * (min a d : ℕ) + seedDegree Q * (d-a : ℕ) := by
        exact_mod_cast proper_intersection Q cut.first hQ hT.ne' cut.first_proper
          _ _ cut.first_box G (fun γ hγ =>
            ⟨hzeros γ (Finset.mem_filter.mp hγ).1,
              (cut.zeros γ (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hγ).2).1⟩)
      have hs : (G.card : ℚ) ≤ (Q.natDegree : ℚ) * (d-a : ℕ) + seedDegree Q * (min a d : ℕ) := by
        exact_mod_cast proper_intersection Q cut.second hQ hT.ne' cut.second_proper
          _ _ cut.second_box G (fun γ hγ =>
            ⟨hzeros γ (Finset.mem_filter.mp hγ).1,
              (cut.zeros γ (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hγ).2).2⟩)
      have hadd : (min a d : ℕ) + ((d-a : ℕ) : ℚ) = (d : ℚ) := by
        exact_mod_cast (show min a d + (d-a) = d by omega)
      change (G.card : ℚ) ≤ _
      have heq := congrArg (fun x : ℚ => x * (seedDegree Q + Q.natDegree : ℕ)) hadd
      simp only [Nat.cast_add] at heq ⊢
      linarith only [hf, hs, heq])
  change (d : ℚ)*Γ.card ≤ E.card*((d : ℚ)/2*(seedDegree Q + Q.natDegree : ℕ)) at hinc
  have hE : (E.card : ℚ) ≤ D.card := by
    exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset : E ⊆ D))
  apply (mul_le_mul_iff_left₀ hdq).mp
  calc
    (Γ.card : ℚ)*d = (d : ℚ)*Γ.card := mul_comm _ _
    _ ≤ E.card*((d : ℚ)/2*(seedDegree Q + Q.natDegree : ℕ)) := hinc
    _ ≤ D.card*((d : ℚ)/2*(seedDegree Q + Q.natDegree : ℕ)) :=
      mul_le_mul_of_nonneg_right hE (by positivity)
    _ = _ := by ring

private theorem beta_at_least_one (A a C : ℕ) : 1 ≤ curveBeta A a C := by
  unfold curveBeta
  have hn : 0 ≤ (A : ℚ)/(a-C+1 : ℕ) := by positivity
  linarith

private theorem carried_curve (hcore : c3) {u D a b Γ P L}
    (hb : 1 ≤ b) (C : ℕ) (hC : 1 ≤ C) (hCa : C ≤ a)
    (hreg : RegularPlane u D a (a+b) Γ P) (h : BoxedLocator u D a b Γ P L)
    (hprice : ((ordinaryCore (131072+a) a C : ℕ) : ℚ) ≤
      2 * curveBeta (131072+a) a C * b)
    (Q : Bivar) (hQ : Irreducible Q) (hzeros : ∀ γ ∈ Γ, onGraph γ Q = 0) :
    (Γ.card : ℚ) ≤ curveBeta (131072+a) a C * b * (seedDegree Q + Q.natDegree : ℕ) := by
  let A := 131072+a
  let β := curveBeta A a C
  have hβ : 1 ≤ β := beta_at_least_one A a C
  have hbq : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have hw : (1 : ℚ) ≤ β*b := by nlinarith
  change (Γ.card : ℚ) ≤ β*b*(seedDegree Q + Q.natDegree : ℕ)
  by_cases hcoord : seedDegree Q = 0 ∨ Q.natDegree = 0
  · have hc : (Γ.card : ℚ) ≤ (seedDegree Q + Q.natDegree : ℕ) := by
      exact_mod_cast coordinate_intersection Q hQ.ne_zero hcoord Γ hzeros
    exact hc.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hw (show (0 : ℚ) ≤ (seedDegree Q + Q.natDegree : ℕ) by positivity))
  have hS : 0 < seedDegree Q := Nat.pos_of_ne_zero (fun hz => hcoord (Or.inl hz))
  have hT : 0 < Q.natDegree := Nat.pos_of_ne_zero (fun hz => hcoord (Or.inr hz))
  by_cases hne : Γ.Nonempty
  swap
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by linarith) (by positivity)
  let F := curveFixed D L Q
  let d := a+b-F.card
  let E := D \ F
  obtain ⟨hcard, hmark⟩ := punctured_curve_data hreg h Q hne hzeros
  change E.card = A+d at hcard
  by_cases hsmall : d ≤ a-C
  · have hc := hcore u E Γ P a d (by omega) hcard hmark
    have hnum : (A+d)/(a-d+1) ≤ (A+(a-C))/(a-d+1) := Nat.div_le_div_right (by omega)
    have hden : (A+(a-C))/(a-d+1) ≤ (A+(a-C))/(C+1) := Nat.div_le_div_left (by omega) (by omega)
    have hc' : Γ.card ≤ ordinaryCore A a C := by
      unfold ordinaryCore
      change Γ.card ≤ (a-C)+(A+(a-C))/(C+1)
      change Γ.card ≤ d+(A+d)/(a-d+1) at hc
      omega
    have hcq : (Γ.card : ℚ) ≤ ordinaryCore A a C := by exact_mod_cast hc'
    have hperim : (2 : ℚ) ≤ (seedDegree Q + Q.natDegree : ℕ) := by
      exact_mod_cast (show 2 ≤ seedDegree Q + Q.natDegree by omega)
    calc
      _ ≤ 2*β*b := hcq.trans hprice
      _ = β*b*2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hperim (by linarith)
  have hdq : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
  have hinc := curve_root_incidence hreg h Q hzeros
    ((b : ℚ)*(seedDegree Q + Q.natDegree : ℕ)) (by
      intro i hi
      let G := Γ.filter (fun γ => i ∈ errorSet u D γ (P γ))
      have hp : ¬ Q ∣ nodeEquation L i := by
        intro hdiv
        obtain ⟨hiD, hiF⟩ := Finset.mem_sdiff.mp hi
        exact hiF (mem_curveFixed.mpr ⟨hiD, hdiv⟩)
      have hh := proper_intersection Q (nodeEquation L i) hQ hT.ne' hp
        b b (nodeEquation_box L b b h.box i) G (by
          intro γ hγ
          obtain ⟨hγΓ, hγerr⟩ := Finset.mem_filter.mp hγ
          exact ⟨hzeros γ hγΓ, (root_iff_error h hγΓ i).mpr hγerr⟩)
      have hh' : G.card ≤ b*(seedDegree Q + Q.natDegree) := hh.trans_eq (by ring)
      exact_mod_cast hh')
  change (d : ℚ)*Γ.card ≤ E.card*((b : ℚ)*(seedDegree Q + Q.natDegree : ℕ)) at hinc
  have hcardq : (E.card : ℚ) = A+d := by exact_mod_cast hcard
  rw [hcardq] at hinc
  have hlo : ((a-C+1 : ℕ) : ℚ) ≤ d := by exact_mod_cast (show a-C+1 ≤ d by omega)
  have hratio : ((A : ℚ)+d)/d ≤ β := by
    calc
      _ = 1 + (A : ℚ)/d := by field_simp; ring
      _ ≤ β := by
        unfold β curveBeta
        gcongr
  calc
    (Γ.card : ℚ) ≤ ((A+d)*((b : ℚ)*(seedDegree Q + Q.natDegree : ℕ)))/d :=
      (le_div_iff₀ hdq).mpr (by rwa [mul_comm (Γ.card : ℚ)])
    _ = ((A+d)/d)*b*(seedDegree Q + Q.natDegree : ℕ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hratio (by positivity)) (by positivity)

private theorem price_fraction_mono (a x y : ℚ) (ha : 0 < a) (hx : 0 ≤ x) (hxy : x ≤ y) :
    x/(a+x) ≤ y/(a+y) := by
  apply (div_le_div_iff₀ (by linarith : 0 < a+x) (by linarith : 0 < a+y)).mpr
  nlinarith

private theorem old_price_mono (A a x y : ℕ) (ha : 0 < a) (hxy : x ≤ y) :
    oldPlanePrice A a x ≤ oldPlanePrice A a y := by
  have hxyq : (x : ℚ) ≤ y := by exact_mod_cast hxy
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hf := price_fraction_mono a x y haq (by positivity) hxyq
  have hs : ((A : ℚ)+a+x)^2 ≤ (A+a+y)^2 := by gcongr
  unfold oldPlanePrice
  calc
    _ = ((A : ℚ)+a+x)^2*(x/(a+x)) := by ring
    _ ≤ ((A : ℚ)+a+y)^2*(y/(a+y)) := mul_le_mul hs hf (by positivity) (by positivity)
    _ = _ := by ring

private theorem new_price_mono (β : ℚ) (A a x y : ℕ)
    (hβ : 0 ≤ β) (ha : 0 < a) (hxy : x ≤ y) :
    newPlanePrice β A a x ≤ newPlanePrice β A a y := by
  have hxyq : (x : ℚ) ≤ y := by exact_mod_cast hxy
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hf := price_fraction_mono a x y haq (by positivity) hxyq
  have hpx : (x : ℚ)*(A+a+x) ≤ (y : ℚ)*(A+a+y) := by gcongr
  unfold newPlanePrice
  calc
    _ = 2*β*(x/(a+x)*((x : ℚ)*(A+a+x))) := by ring
    _ ≤ 2*β*(y/(a+y)*((y : ℚ)*(A+a+y))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul hf hpx (by positivity) (by positivity)) (by positivity)
    _ = _ := by ring

private theorem core_below_threshold (A a C z : ℕ)
    (hz : planeThreshold A a C < z) :
    (ordinaryCore A a C : ℚ) ≤ 2*curveBeta A a C*z := by
  let x := (ordinaryCore A a C : ℚ)/(2*curveBeta A a C)
  have hceil : ⌈x⌉ ≤ (z : ℤ) := by
    by_contra hn
    change (⌈x⌉ : ℤ).toNat - 1 < z at hz
    omega
  have hdiv : x ≤ (z : ℚ) := by simpa only [Int.cast_natCast] using (Int.ceil_le.mp hceil)
  have hβ : 1 ≤ curveBeta A a C := beta_at_least_one A a C
  have hm := (div_le_iff₀ (show (0 : ℚ) < 2*curveBeta A a C by linarith)).mp hdiv
  simpa only [mul_comm (z : ℚ)] using hm

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K21_2.c4 := by
  intro u D Γ P a b C hb hba hC hCa hreg
  obtain he | ⟨F, L, _, hf, _, hplane, hloc⟩ := h1 u D Γ P a b hb hba hreg
  · rw [he, Finset.card_empty, Nat.cast_zero]
    exact K21_2.planePrice_nonneg _ _ _ _
  let z := b-F.card
  let A := 131072+a
  let β := curveBeta A a C
  let q := planeThreshold A a C
  have hz : 1 ≤ z := by omega
  have hzb : z ≤ b := Nat.sub_le _ _
  have hza := hzb.trans hba
  have ha : 0 < a := by omega
  have hpos : (0 : ℚ) < a+z := by
    exact_mod_cast (show 0 < a+z by omega)
  have hdom : ((D \ F).card : ℚ) = A+a+z := by
    exact_mod_cast (show (D \ F).card = A+a+z by have he := hplane.domain_card; dsimp [A, z]; omega)
  have hold : (Γ.card : ℚ) ≤ oldPlanePrice A a z := by
    have hinc := plane_incidence hloc (fun γ hγ => (hplane.mark γ hγ).2.1)
      (((D \ F).card : ℚ)/2) (by positivity) (by
        intro Q hQ
        exact old_curve h2 h3 hz hza (restrict_plane hplane Q) (restrict_locator hloc Q) Q hQ
          (fun γ hγ => (Finset.mem_filter.mp hγ).2))
    change (a+z : ℚ)*Γ.card ≤ ((D \ F).card : ℚ)*(2*(((D \ F).card : ℚ)/2)*z) at hinc
    rw [hdom] at hinc
    apply (le_div_iff₀ hpos).mpr
    calc
      (Γ.card : ℚ)*(a+z) = (a+z)*Γ.card := by ring
      _ ≤ _ := hinc
      _ = _ := by ring
  have hbase := hold.trans (old_price_mono A a z b ha hzb)
  change (Γ.card : ℚ) ≤ if b ≤ q then oldPlanePrice A a b else
    min (oldPlanePrice A a b) (max (oldPlanePrice A a q) (newPlanePrice β A a b))
  split_ifs
  · exact hbase
  apply le_min hbase
  by_cases hzq : z ≤ q
  · exact (hold.trans (old_price_mono A a z q ha hzq)).trans (le_max_left _ _)
  have hK := core_below_threshold A a C z (Nat.lt_of_not_ge hzq)
  have hβ : 0 ≤ β := (by norm_num : (0 : ℚ) ≤ 1).trans (beta_at_least_one A a C)
  have hinc := plane_incidence hloc (fun γ hγ => (hplane.mark γ hγ).2.1)
    (β*z) (by positivity) (by
      intro Q hQ
      exact carried_curve h3 hz C hC hCa (restrict_plane hplane Q) (restrict_locator hloc Q)
        hK Q hQ (fun γ hγ => (Finset.mem_filter.mp hγ).2))
  change (a+z : ℚ)*Γ.card ≤ ((D \ F).card : ℚ)*(2*(β*z)*z) at hinc
  rw [hdom] at hinc
  have hnew : (Γ.card : ℚ) ≤ newPlanePrice β A a z := by
    apply (le_div_iff₀ hpos).mpr
    calc
      (Γ.card : ℚ)*(a+z) = (a+z)*Γ.card := by ring
      _ ≤ _ := hinc
      _ = _ := by ring
  exact (hnew.trans (new_price_mono β A a z b hβ ha hzb)).trans (le_max_right _ _)

end

end K21_2_4
end Port_K1_2_4Split

section Port_K1_2_4_1Ranks
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K21_2_4_1

noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open K21 K21_2 K21_2_4

/-- Removing only errors preserves every agreement and restricts the error set. -/
theorem puncture_marks {u : Words} {D F : Finset I} {γ : K} {P : K[X]}
    (hF : F ⊆ errorSet u D γ P) :
    goodSet u (D \ F) γ P = goodSet u D γ P ∧
    errorSet u (D \ F) γ P = errorSet u D γ P \ F := by
  have hg : goodSet u (D \ F) γ P = goodSet u D γ P := by
    ext i
    have hnot (hi : i ∈ F) : i ∉ goodSet u D γ P := (Finset.mem_sdiff.mp (hF hi)).2
    simp only [goodSet, Finset.mem_filter, Finset.mem_sdiff] at hnot ⊢
    tauto
  refine ⟨hg, ?_⟩
  unfold errorSet
  rw [hg]
  ext i
  simp only [Finset.mem_sdiff]
  tauto

private def errorColumns (u : Words) (E : Finset I) (a : ℕ) (γ : K) (P : K[X]) :
    Matrix (Fin 2 × Fin a) E K :=
  Strata.conjugateErrors (Strata.twoConjugations (frobenius K p))
    (fun i : E => node i.val) (fun i : E => u 0 i.val + γ * u 1 i.val - P.eval (node i.val)) a

private theorem plane_rank_error_columns (u : Words) (D : Finset I) (a d : ℕ)
    (γ : K) (P : K[X]) (hD : D.card = 131072+a+d) (hP : P.degree < 131072)
    (hE : (errorSet u D γ P).card = d) :
    ((planeMatrix u D a d).map (onGraph γ)).rank = (errorColumns u (errorSet u D γ P) a γ P).rank := by
  classical
  let x : D → K := fun i => node i.val
  let w : D → K := fun i => u 0 i.val + γ * u 1 i.val
  let E := errorSet u D γ P
  let S := E.subtype (· ∈ D)
  have hsub : E ⊆ D := Finset.sdiff_subset
  let e : E ≃ S :=
    { toFun := fun i => ⟨⟨i.val, hsub i.property⟩, Finset.mem_subtype.mpr i.property⟩
      invFun := fun i => ⟨i.val.val, Finset.mem_subtype.mp i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : S.card = d := by
    rw [← Fintype.card_coe, ← Fintype.card_congr e, Fintype.card_coe, hE]
  have hsize : 131072+a+d ≤ Fintype.card D := by rw [Fintype.card_coe, hD]
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have hf (i : D) : frobenius K p (x i) = x i := Native.native_domain_fixed i.val
  have hfixed (b : Fin 2) (i : D) : Strata.twoConjugations (frobenius K p) b (x i) = x i := by
    fin_cases b <;> simp [Strata.twoConjugations, hf]
  have hagree (i : D) (hi : i ∉ S) : w i = P.eval (x i) := by
    by_contra hn
    exact hi (Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr ⟨i.property, by
      simp only [goodSet, Finset.mem_filter, i.property, true_and]
      exact Ne.symm hn⟩))
  rw [K21_2_3.plane_at_slope, Strata.conjugateHankel_error_rank _ x w hx hfixed
    P 131072 a d hP hsize S (by omega) hagree]
  exact (Matrix.rank_submatrix _ (Equiv.refl _) e).symm

/-- The same marked decoder at a shorter domain gives the restriction of
the original full-column-rank weighted error matrix, with weights stripped. -/
theorem puncture_point_rank {u : Words} {D F : Finset I} {a R : ℕ} {γ : K} {P : K[X]}
    (hD : D.card = 131072+a+R) (hP : P.degree < 131072)
    (hE : (errorSet u D γ P).card = R) (hR : ((planeMatrix u D a R).map (onGraph γ)).rank = R)
    (hF : F ⊆ errorSet u D γ P) :
    ((planeMatrix u (D \ F) a (R-F.card)).map (onGraph γ)).rank = R-F.card := by
  classical
  let E := errorSet u D γ P
  let E' := errorSet u (D \ F) γ P
  have heq : E' = E \ F := (puncture_marks hF).2
  have hE' : E'.card = R-F.card := by rw [heq, Finset.card_sdiff_of_subset hF, hE]
  have hDF : (D \ F).card = 131072+a+(R-F.card) := by
    have hle := Finset.card_le_card hF
    rw [hE] at hle
    rw [Finset.card_sdiff_of_subset (hF.trans Finset.sdiff_subset), hD]
    omega
  rw [plane_rank_error_columns u (D \ F) a (R-F.card) γ P hDF hP hE', ← hE', ← Fintype.card_coe]
  have hfull : (errorColumns u E a γ P).rank = Fintype.card E := by
    rw [← plane_rank_error_columns u D a R γ P hD hP hE, hR, Fintype.card_coe, hE]
  have hli : LinearIndependent K (errorColumns u E a γ P).col := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    unfold Set.finrank
    rw [← Matrix.rank_eq_finrank_span_cols, hfull]
  have hEE : E' ⊆ E := by rw [heq]; exact Finset.sdiff_subset
  let e : E' → E := fun i => ⟨i.val, hEE i.property⟩
  have he : Function.Injective e := fun _ _ h => Subtype.ext (congrArg (fun i : E => i.val) h)
  have hli' : LinearIndependent K (errorColumns u E' a γ P).col := hli.comp e he
  rw [Matrix.rank_eq_finrank_span_cols]
  exact finrank_span_eq_card hli'

end

end K21_2_4_1
end Port_K1_2_4_1Ranks

section Port_K1_2_2Marks
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace K21_2_2
noncomputable section

open K21 K21_2 Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark

private theorem twoBlock_atSlope (u : Words) (γ : K) :
    ((twoBlock u).map (evalRingHom γ)) =
      Strata.conjugateHankel (Strata.twoConjugations (frobenius K p))
        node (fun i => u 0 i + γ * u 1 i) 49058 82014 := by
  rw [twoBlock, Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval]
  have h : (fun b : Fin 2 => iterateFrobenius K p b.val) =
      Strata.twoConjugations (frobenius K p) := by
    funext b
    fin_cases b
    · exact iterateFrobenius_zero K p
    · exact iterateFrobenius_one K p
  rw [h]

/-- The rank of a normal stack is a lower bound on the number of actual
nonzero errors of every degree-bounded decoder of that slope. -/
theorem rank_le_errors {u : Words} {γ : K} (M : BadMark u γ)
    (hγ : Normal u γ) (E : Finset I)
    (hagree : ∀ i ∉ E, u 0 i + γ * u 1 i = M.decoder.eval (node i)) :
    stackRank u ≤ E.card := by
  have hfix : ∀ b i, Strata.twoConjugations (frobenius K p) b (node i) = node i := by
    intro b i
    fin_cases b <;> simp [Strata.twoConjugations, frobenius_def, Native.native_domain_fixed]
  have h := Strata.conjugateHankel_factorization
    (Strata.twoConjugations (frobenius K p)) node (fun i => u 0 i + γ * u 1 i)
    IRSProfile.domain.injective hfix M.decoder 131072 49058 82014 M.degree
    (by rw [IRSProfile.card_index]) E hagree
  change ((twoBlock u).map (evalRingHom γ)).rank = stackRank u at hγ
  rw [← hγ, twoBlock_atSlope, h]
  refine (Matrix.rank_mul_le_right _ _).trans ?_
  simpa only [Fintype.card_coe] using
    Matrix.rank_le_card_height (Strata.nodeVandermonde (fun i : E => node i.val) 82014)

theorem domain_card (S : Finset I) :
    (Finset.univ \ S).card = 262144 - S.card := by
  classical
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index]

private theorem mark_counts {u : Words} {γ : K} (M : BadMark u γ)
    (hγ : Normal u γ) {S : Finset I}
    (hfixed : ∀ i ∈ S, M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i) :
    let D := Finset.univ \ S
    let G := goodSet u D γ M.decoder
    let s := G.card - 180130
    s ≤ nullity u - 1 ∧ G.card = 180130 + s ∧
      (errorSet u D γ M.decoder).card = 82014 - S.card - s ∧ ¬ JointOn u G := by
  classical
  dsimp only
  let D := Finset.univ \ S
  let G := goodSet u D γ M.decoder
  let E := Finset.univ \ G
  have hsupport : M.support ⊆ G := by
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hs => hfixed i hs (M.hits i hi)⟩, M.hits i hi⟩
  have hlow := M.agreement.trans (Finset.card_le_card hsupport)
  have hGD : G ⊆ D := Finset.filter_subset _ _
  have hGle := Finset.card_le_card hGD
  have hD : D.card = 262144 - S.card := domain_card S
  have hE : E.card = 262144 - G.card := domain_card G
  have hEg : ∀ i ∉ E, u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    intro i hi
    by_contra hne
    apply hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hG =>
      hne (Finset.mem_filter.mp hG).2.symm⟩
  have hrank := rank_le_errors M hγ E hEg
  have hrankBound : stackRank u + nullity u = 82015 := by
    simpa only [stackRank, nullity, Fintype.card_fin] using
      GenericLayer.rank_add_nullity (twoBlock u)
  have herror : (errorSet u D γ M.decoder).card = D.card - G.card :=
    Finset.card_sdiff_of_subset hGD
  change G.card - 180130 ≤ nullity u - 1 ∧ G.card = 180130 + (G.card - 180130) ∧
    (errorSet u D γ M.decoder).card = 82014 - S.card - (G.card - 180130) ∧ ¬ JointOn u G
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro hjoint
  apply M.nonjoint
  obtain ⟨⟨P, hP, hPval⟩, ⟨Q, hQ, hQval⟩⟩ := hjoint
  exact ⟨⟨P, hP, fun i hi => hPval i (hsupport hi)⟩,
    ⟨Q, hQ, fun i hi => hQval i (hsupport hi)⟩⟩

/-- A single choice of a genuine decoder across the selected slopes,
with its full agreement set and unchanged nonjointness witness. -/
theorem paddedFamily {u : Words} {T : TwoActive u} {R : Relation T}
    (hsat : NormalSaturation R) (Γ : Finset K) (hbad : BadFamily u Γ)
    (hn : ∀ γ ∈ Γ, Normal u γ) :
    Nonempty (PaddedFamily u (Finset.univ \ fixedNodes R) Γ
      (nullity u) (fixedNodes R).card) := by
  classical
  let D := Finset.univ \ fixedNodes R
  let M (γ : K) (hγ : γ ∈ Γ) : BadMark u γ :=
    Classical.choice (bad_mark u Γ hbad γ hγ)
  let P (γ : K) : K[X] := if hγ : γ ∈ Γ then (M γ hγ).decoder else 0
  refine ⟨⟨P, fun γ => (goodSet u D γ (P γ)).card - 180130, domain_card _, ?_, ?_⟩⟩
  · intro γ hγ
    simpa only [P, dite_eq_left hγ] using (M γ hγ).degree
  · intro γ hγ
    have h := mark_counts (M γ hγ) (hn γ hγ) (hsat γ (hn γ hγ) (M γ hγ)).fixed_errors
    simpa only [P, dite_eq_left hγ, D] using h

end
end K21_2_2
end Port_K1_2_2Marks

section Port_K1_2_4_1Deflation
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K21_2_4_1

noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open K21 K21_2 K21_2_4

theorem eval_planeConstant (γ : K) (x : K) : onGraph γ (planeConstant x) = x := by
  rw [K21_2_4.evalGraph]
  simp [planeConstant]

theorem root_iff_error {u : Words} {D : Finset I} {Γ : Finset K} {P : K → K[X]}
    {a d : ℕ} {L : Bivar[X]} (hL : MarkedLocator u D a d Γ P L)
    {γ : K} (hγ : γ ∈ Γ) (i : I) :
    onGraph γ (nodeEquation L i) = 0 ↔ i ∈ errorSet u D γ (P γ) := by
  obtain ⟨c, hc, hf⟩ := hL.fiber γ hγ
  rw [nodeEquation, ← Polynomial.eval_map_apply, eval_planeConstant, hf, Polynomial.eval_smul,
    smul_eq_mul, mul_eq_zero, or_iff_right hc]
  exact Principal.locator_eval_zero_iff node IRSProfile.domain.injective _ i

theorem locator_nonzero {u : Words} {D : Finset I} {Γ : Finset K} {P : K → K[X]}
    {a d : ℕ} {L : Bivar[X]} (hL : MarkedLocator u D a d Γ P L) (hΓ : Γ.Nonempty) : L ≠ 0 := by
  obtain ⟨γ, hγ⟩ := hΓ
  obtain ⟨c, hc, hf⟩ := hL.fiber γ hγ
  intro hz
  rw [hz, Polynomial.map_zero] at hf
  exact (smul_ne_zero hc (locator_monic node _).ne_zero) hf.symm

/-- Divisibility holds over the polynomial coefficient ring. At a different
node the removed linear factor evaluates to a nonzero constant. -/
theorem fixedFactor_dvd (F : Finset I) (L : Bivar[X])
    (h : ∀ i ∈ F, nodeEquation L i = 0) : fixedFactor F ∣ L := by
  classical
  induction F using Finset.induction_on generalizing L with
  | empty => simp [fixedFactor, locator]
  | insert i F hi ih =>
    obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.mpr (h i (Finset.mem_insert_self i F))
    have hroot (j : I) (hj : j ∈ F) : nodeEquation Q j = 0 := by
      have he := h j (Finset.mem_insert_of_mem hj)
      rw [nodeEquation, hQ, eval_mul, eval_sub, eval_X, eval_C] at he
      apply (mul_eq_zero.mp he).resolve_left
      exact sub_ne_zero.mpr (fun heq => hi ((IRSProfile.domain.injective
        (planeConstant.injective heq)) ▸ hj))
    obtain ⟨V, hV⟩ := ih Q hroot
    refine ⟨V, ?_⟩
    have hfac : fixedFactor (insert i F) =
        (Polynomial.X (R := Bivar) - C (planeConstant (node i))) * fixedFactor F := by
      simp only [fixedFactor, locator, Finset.prod_insert hi, Polynomial.map_mul,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [hQ, hV, hfac, mul_assoc]

theorem fixedFactor_monic (F : Finset I) : (fixedFactor F).Monic :=
  (locator_monic node F).map _

theorem fixedFactor_natDegree (F : Finset I) : (fixedFactor F).natDegree = F.card := by
  rw [fixedFactor, (locator_monic node F).natDegree_map, locator_natDegree]

private abbrev FunctionField := FractionRing Bivar

private def planeEmbedding : Bivar →+* FunctionField := algebraMap Bivar FunctionField

private theorem planeEmbedding_injective : Function.Injective planeEmbedding :=
  IsFractionRing.injective Bivar FunctionField

private theorem map_locator_kernel {row : Type*} {d : ℕ}
    (M : Matrix row (Fin (d+1)) Bivar) {L : Bivar[X]}
    (h : M.mulVec (fun j => L.coeff j.val) = 0) :
    (M.map planeEmbedding).mulVec (fun j => (L.map planeEmbedding).coeff j.val) = 0 := by
  funext i
  simpa only [coeff_map, Function.comp_def, h, Pi.zero_apply, map_zero] using
    (planeEmbedding.map_mulVec M (fun j => L.coeff j.val) i).symm

private theorem map_locator_vector_ne_zero {d : ℕ} {L : Bivar[X]} (hL : L ≠ 0)
    (hd : L.natDegree ≤ d) : (fun j : Fin (d+1) => (L.map planeEmbedding).coeff j.val) ≠ 0 := by
  intro hz
  have h := congrFun hz ⟨L.natDegree, Nat.lt_succ_of_le hd⟩
  apply leadingCoeff_ne_zero.mpr hL
  apply planeEmbedding_injective
  simpa only [leadingCoeff, coeff_map, map_zero, Pi.zero_apply] using h

theorem generic_rank_le_of_locator {row : Type*} {d : ℕ} (M : Matrix row (Fin (d+1)) Bivar)
    {L : Bivar[X]} (hL : L ≠ 0) (hd : L.natDegree ≤ d)
    (hker : M.mulVec (fun j => L.coeff j.val) = 0) :
    (M.map (algebraMap Bivar (FractionRing Bivar))).rank ≤ d := by
  let N := M.map planeEmbedding
  have h := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  change N.rank + _ = d+1 at h
  have hpos : 0 < Module.finrank FunctionField (LinearMap.ker N.mulVecLin) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hbot := Submodule.finrank_eq_zero.mp hz
    have hv : (fun j => (L.map planeEmbedding).coeff j.val) ∈ LinearMap.ker N.mulVecLin :=
      map_locator_kernel M hker
    rw [hbot, Submodule.mem_bot] at hv
    exact map_locator_vector_ne_zero hL hd hv
  change N.rank ≤ d
  omega

/-- At generic rank d, a recomputed kernel polynomial has the same grid
zeros as the shortened polynomial locator. -/
theorem repack_node_nonzero {row : Type*} {d : ℕ} (M : Matrix row (Fin (d+1)) Bivar)
    (hr : (M.map (algebraMap Bivar (FractionRing Bivar))).rank = d)
    {L Q : Bivar[X]} (hL : L ≠ 0) (hQ : Q ≠ 0) (hLd : L.natDegree ≤ d) (hQd : Q.natDegree ≤ d)
    (hLker : M.mulVec (fun j => L.coeff j.val) = 0) (hQker : M.mulVec (fun j => Q.coeff j.val) = 0)
    (i : I) (hi : nodeEquation Q i ≠ 0) : nodeEquation L i ≠ 0 := by
  let N := M.map planeEmbedding
  have hn : N.rank+1 = Fintype.card (Fin (d+1)) := by rw [Fintype.card_fin]; exact congrArg (· + 1) hr
  obtain ⟨c, hc⟩ := GenericRank.kernel_line_of_finrank N (GenericRank.nullity_one_of_rank N hn)
    _ (map_locator_vector_ne_zero hQ hQd) (map_locator_kernel M hQker) _ (map_locator_kernel M hLker)
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hc
    exact map_locator_vector_ne_zero hL hLd hc
  have he : L.map planeEmbedding = c • Q.map planeEmbedding := by
    apply Polynomial.ext
    intro j
    by_cases hj : j < d+1
    · simpa only [coeff_smul, Pi.smul_apply] using congrFun hc ⟨j, hj⟩
    · rw [coeff_smul, coeff_map, coeff_map, coeff_eq_zero_of_natDegree_lt (show L.natDegree < j by omega),
        coeff_eq_zero_of_natDegree_lt (show Q.natDegree < j by omega), map_zero, smul_zero]
  intro hz
  have heval := congrArg (fun V : FunctionField[X] => V.eval (planeEmbedding (planeConstant (node i)))) he
  rw [Polynomial.eval_map_apply, Polynomial.eval_smul, Polynomial.eval_map_apply] at heval
  change planeEmbedding (nodeEquation L i) = c * planeEmbedding (nodeEquation Q i) at heval
  rw [hz, map_zero] at heval
  exact hi (planeEmbedding_injective ((mul_eq_zero.mp heval.symm).resolve_left hc0 |>.trans (map_zero _).symm))

end

end K21_2_4_1
end Port_K1_2_4_1Deflation

section Port_K1_2_2Split
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace K21_2_2
noncomputable section

open K21 K21_2 K1_6 Polynomial Matrix FrobeniusLocator

/-- A genuine normal witness supplies the shortened stack's rank lower
bound after deletion of the fixed error columns. -/
def c1 : Prop :=
  ∀ (u : Words) (T : TwoActive u) (R : Relation T) (A : Reduction u T R)
    (γ : K), BadMark u γ → Normal u γ →
      49058 + A.height ≤ GenericLayer.genericRank (shortenedStack R)

/-- The shortened relation supplies all its bounded shifts as left
dependencies of the shortened stack. -/
def c2 : Prop :=
  ∀ (u : Words) (T : TwoActive u) (R : Relation T) (A : Reduction u T R),
    (shifts (pair A) 49058 (49058 - A.height)).transpose * shortenedStack R = 0

private theorem shifted_pair_height
    (F : Type) [Field F] (L H w q : ℕ) (P : Fin 2 → F[X][X])
    (M : Matrix (Fin 2 × Fin L) (Fin w) F[X])
    (hq : 1 ≤ q) (hHL : H < L)
    (hP : ∀ b, (P b).natDegree ≤ H)
    (hprim : PrimitiveVector.IsPrimitive (pairCoordinates P H))
    (hrank : L + H ≤ GenericLayer.genericRank M)
    (hshift : (shifts P L (L - H)).transpose * M = 0)
    (hentry : ∀ i j, (M i j).natDegree ≤ if i.1 = 0 then 1 else q) :
    ∀ b j, ((P b).coeff j).natDegree ≤ (q * L + H) / (L - H) := by
  classical
  intro b j
  let s := L - H
  have hs : 0 < s := by dsimp [s]; omega
  have hsum : H + s = L := by dsimp [s]; omega
  let W := shifts P L s
  let φ : F[X] →+* GenericLayer.GenericField F := algebraMap _ _
  obtain ⟨hminors, ζ, hζ, rows, hrows⟩ := K1_6_1.proof F H L s P hsum hs hP hprim
  obtain ⟨I, hI⟩ := PrimitiveVector.exists_eval_ne_zero (maximalMinors W) hminors 0
  have hI' : (W.submatrix I id).det ≠ 0 := fun hz => hI (by simp [maximalMinors, hz])
  have hdet : ((W.map φ).submatrix I id).det ≠ 0 := by
    have h := φ.map_det (W.submatrix I id)
    change φ ((W.submatrix I id).det) = ((W.map φ).submatrix I id).det at h
    rw [← h]
    exact fun hz => hI' ((IsFractionRing.injective F[X] (GenericLayer.GenericField F))
      (hz.trans (map_zero φ).symm))
  have hW : s ≤ (W.map φ).rank := by
    have h := Matrix.rank_submatrix_le (W.map φ) I id
    rwa [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at h
  have hmap : (W.map φ).transpose * M.map φ = 0 := by
    have h := congrArg (fun N : Matrix (Fin s) (Fin w) F[X] => N.map φ) hshift
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_zero _ (map_zero φ)] at h
    exact h
  have hu := Matrix.rank_add_rank_le_card_of_mul_eq_zero hmap
  rw [Matrix.rank_transpose, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hu
  change (W.map φ).rank + GenericLayer.genericRank M ≤ 2 * L at hu
  have hR : GenericLayer.genericRank M + s = 2 * L := by omega
  have hb := K1_6_2.proof F L w s q M W hq hR hshift hentry hminors rows
  rw [hrows] at hb
  have hledger : L * (q + 1) - s = q * L + H := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm L q]
    omega
  rw [hledger] at hb
  exact (hζ b j).trans ((Nat.le_div_iff_mul_le hs).mpr (by simpa only [Nat.mul_comm] using hb))

theorem of_children (h1 : c1) (h2 : c2) : K21_2.c2 := by
  classical
  intro u hm T R hmov hinv hsat Γ hnon hbad hn
  dsimp only
  intro hg
  obtain ⟨γ, hγ⟩ := hnon
  obtain ⟨M⟩ := bad_mark u Γ hbad γ hγ
  have hSat := hsat γ (hn γ hγ) M
  have hU : leftU R ≠ 0 := by
    intro hz
    exact hSat.U_ne (by rw [atSlope, hz, Polynomial.map_zero])
  obtain ⟨A⟩ := K21_8.puncture R hsat ⟨γ, hn γ hγ, ⟨M⟩⟩
    (K21_8.fixed_gcd R hU hmov hinv)
  let D := Finset.univ \ fixedNodes R
  let H := reducedHeight (nullity u) (fixedNodes R).card
  have hheight : A.height = H := by
    have h := A.height_eq
    have := T.degreeSum
    have := T.nullitySum
    have := T.top
    unfold TwoActive.height at h
    dsimp [H, reducedHeight]
    omega
  have hpos : 0 < H := by
    have hg' := hg.trans (fixedLimit_le (nullity u))
    have hr := hm.2.1
    dsimp [H, reducedHeight]
    omega
  have hlt : A.height < 49058 := by
    have hr := hm.1
    rw [hheight]
    dsimp [H, reducedHeight]
    omega
  have hnodes : relationOn u (Finset.univ \ D) A.U A.V A.output := by
    intro i hi
    have hi' : i ∉ fixedNodes R := by
      intro hs
      exact hi (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hD => (Finset.mem_sdiff.mp hD).2 hs⟩)
    simpa only [Polynomial.C_1, one_mul] using K21_8.reduced_scaled_relation A (1 : K[X]) i hi'
  let Q : ReducedRelation u D H :=
    ⟨A.U, A.V, A.output, Or.inl A.U_ne, A.max_degree.trans hheight,
      hheight ▸ A.output_degree, hnodes⟩
  have hrank := h1 u T R A γ M (hn γ hγ)
  have hshift := h2 u T R A
  have hentry (i : Fin 2 × Fin 49058) (j : Fin (82014 - (fixedNodes R).card + 1)) :
      (shortenedStack R i j).natDegree ≤ if i.1 = 0 then 1 else p :=
    stacked_entry_natDegree p (fun i : D => node i.val) (fun i => u 0 i.val)
      (fun i => u 1 i.val) 49058 (82014 - (fixedNodes R).card) i j
  have hp : 1 ≤ p := by decide
  have hz := shifted_pair_height K 49058 A.height _ p (pair A) (shortenedStack R) hp hlt (pair_degree A)
    (pair_primitive A) hrank hshift hentry
  rw [hheight] at hz
  let ζ := (p * 49058 + H) / (49058 - H)
  have hζU (i : ℕ) : (Q.U.coeff i).natDegree ≤ ζ := hz 0 i
  have hζV (i : ℕ) : (Q.V.coeff i).natDegree ≤ ζ := hz 1 i
  obtain ⟨book, hbsub, hbcard, hreg⟩ :=
    resultant_book Q hpos A.U_ne A.V_ne A.coprime hζU hζV Γ
  obtain ⟨F⟩ := paddedFamily hsat (Γ \ book)
    (fun z hz => hbad z (Finset.mem_sdiff.mp hz).1)
    (fun z hz => hn z (Finset.mem_sdiff.mp hz).1)
  refine ⟨book, hbsub, ?_, F, Q, hreg⟩
  exact hbcard.trans (Nat.le_add_right _ _)

end
end K21_2_2
end Port_K1_2_2Split

section Port_K1_2_4_1Split
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K21_2_4_1

noncomputable section

open Polynomial Finset FrobeniusLocator ProximityPrize.Benchmark
open K21 K21_2 K21_2_4

/-- Opposite cofactor choices bound both seed degrees, with a nonzero
primitive specialization at every selected exact-rank point. -/
def c1 : Prop :=
  ∀ (u : Words) (D : Finset I) (Γ : Finset K) (P : K → K[X]) (a d : ℕ),
    0 < d → d ≤ a+a → Γ.Nonempty → RegularPlane u D a d Γ P →
    ∃ L : Bivar[X], MarkedLocator u D a d Γ P L ∧
      ∀ j, SeedBox (L.coeff j) (d-a) (d-a)

/-- Transport the literal independent-parameter Hankel kernel equation
through division by the locator of a set of deleted grid nodes. -/
def c2 : Prop :=
  ∀ (u : Words) (D F : Finset I) (a d : ℕ), F ⊆ D →
    ∀ Q : Bivar[X], Q.natDegree ≤ d →
      (planeMatrix u D a (F.card+d)).mulVec (fun j => (fixedFactor F * Q).coeff j.val) = 0 →
      (planeMatrix u (D \ F) a d).mulVec (fun j => Q.coeff j.val) = 0

private theorem constant_node_specialization {V : Bivar} (hV : SeedBox V 0 0) (γ : K) :
    onGraph γ V = 0 → V = 0 := by
  have hT : V.natDegree = 0 := Nat.eq_zero_of_le_zero hV.2
  have hS : (V.coeff 0).natDegree = 0 :=
    Nat.eq_zero_of_le_zero ((coeff_natDegree_le_seedDegree V 0).trans hV.1)
  have hC : V = planeConstant ((V.coeff 0).coeff 0) :=
    (eq_C_of_natDegree_eq_zero hT).trans (congrArg Polynomial.C (eq_C_of_natDegree_eq_zero hS))
  intro hz
  rw [hC, eval_planeConstant] at hz
  rw [hC, hz, map_zero]

/-- With zero remaining errors the degree-zero kernel kills both formal
ordinary syndrome coefficients, giving separate decoders on the full puncture. -/
private theorem joint_of_zero_error_kernel (u : Words) (D : Finset I) (a : ℕ)
    (hD : D.card = 131072+a) (Q : Bivar[X]) (hQ : Q ≠ 0) (hQd : Q.natDegree ≤ 0)
    (hker : (planeMatrix u D a 0).mulVec (fun j => Q.coeff j.val) = 0) : JointOn u D := by
  classical
  let x : D → K := fun i => node i.val
  have hq : Q.coeff 0 ≠ 0 := by
    simpa only [Nat.eq_zero_of_le_zero hQd, leadingCoeff] using leadingCoeff_ne_zero.mpr hQ
  have hsz : Fintype.card D = 131072+a := by rw [Fintype.card_coe, hD]
  have hs (j : ℕ) (hj : j < a) :
      syndrome x (fun i => u 0 i.val) j = 0 ∧ syndrome x (fun i => u 1 i.val) j = 0 := by
    have hrow : (∑ t : Fin 1, planeMatrix u D a 0 (0, ⟨j, hj⟩) t * Q.coeff t.val) = 0 :=
      congrFun hker ((0 : Fin 2), (⟨j, hj⟩ : Fin a))
    rw [Fin.sum_univ_one, Fin.val_zero] at hrow
    have hz := (mul_eq_zero.mp hrow).resolve_right hq
    have hi : Polynomial.C (syndrome x (fun i => u 0 i.val) j) +
        Polynomial.X * Polynomial.C (syndrome x (fun i => u 1 i.val) j) = 0 := by
      apply Polynomial.C_injective (R := K[X])
      simpa [planeMatrix, x] using hz
    constructor
    · simpa only [coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero, coeff_zero] using
        congrArg (fun V : K[X] => V.coeff 0) hi
    · simpa [coeff_add, coeff_X_mul] using congrArg (fun V : K[X] => V.coeff 1) hi
  have extend (b : Fin 2) (hb : ∀ j < a, syndrome x (fun i => u b i.val) j = 0) :
      ExtendsOn node (u b) 131072 D := by
    obtain ⟨A, hA, hfit⟩ := Principal.extendsOn_of_syndrome_zero x
      (IRSProfile.domain.injective.comp Subtype.val_injective) (fun i => u b i.val) 131072
      (by omega) (fun j hj => hb j (by omega))
    exact ⟨A, hA, fun i hi => hfit ⟨i, hi⟩ (Finset.mem_univ _)⟩
  exact ⟨extend 0 (fun j hj => (hs j hj).1), extend 1 (fun j hj => (hs j hj).2)⟩

theorem of_children (hbox : c1) (hcontract : c2) : K21_2_4.c1 := by
  classical
  intro u D Γ P a b hb hba hreg
  by_cases hΓ : Γ.Nonempty
  swap
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hΓ)
  have hΓ' := hΓ
  obtain ⟨γ₀, hγ₀⟩ := hΓ'
  obtain ⟨L, hL, _⟩ := hbox u D Γ P a (a+b) (by omega) (by omega) hΓ hreg
  let F := D.filter (fun i => nodeEquation L i = 0)
  let d := a+b-F.card
  have hF : F ⊆ D := Finset.filter_subset _ _
  have hsub (γ : K) (hγ : γ ∈ Γ) : F ⊆ errorSet u D γ (P γ) := by
    intro i hi
    apply (K21_2_4_1.root_iff_error hL hγ i).mp
    rw [(Finset.mem_filter.mp hi).2, map_zero]
  have hfmax : F.card ≤ a+b := (Finset.card_le_card (hsub γ₀ hγ₀)).trans_eq (hreg.mark γ₀ hγ₀).2.1
  have hadd : F.card+d = a+b := by omega
  obtain ⟨Q, hQ⟩ := fixedFactor_dvd F L (fun i hi => (Finset.mem_filter.mp hi).2)
  have hQ0 : Q ≠ 0 := by
    intro hz
    exact locator_nonzero hL hΓ (by rw [hQ, hz, mul_zero])
  have hQd : Q.natDegree ≤ d := by
    have he := natDegree_mul (fixedFactor_monic F).ne_zero hQ0
    rw [← hQ, fixedFactor_natDegree] at he
    have hd := hL.degree
    omega
  have hQker : (planeMatrix u (D \ F) a d).mulVec (fun j => Q.coeff j.val) = 0 := by
    apply hcontract u D F a d hF Q hQd
    rw [hadd, ← hQ]
    exact hL.kernel
  have hno (i : I) (hi : i ∈ D \ F) : nodeEquation Q i ≠ 0 := by
    intro hz
    change Q.eval (planeConstant (node i)) = 0 at hz
    have he : nodeEquation L i = 0 := by rw [nodeEquation, hQ, eval_mul, hz, mul_zero]
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1, he⟩)
  have hD : (D \ F).card = 131072+a+d := by
    rw [Finset.card_sdiff_of_subset hF, hreg.domain_card]
    omega
  have hshort_mark (γ : K) (hγ : γ ∈ Γ) : (P γ).degree < 131072 ∧
      (errorSet u (D \ F) γ (P γ)).card = d ∧ ¬ JointOn u (goodSet u (D \ F) γ (P γ)) ∧
      ((planeMatrix u (D \ F) a d).map (onGraph γ)).rank = d := by
    obtain ⟨hP, hE, hbad, hr⟩ := hreg.mark γ hγ
    obtain ⟨hg, he⟩ := puncture_marks (hsub γ hγ)
    refine ⟨hP, ?_, hg.symm ▸ hbad, puncture_point_rank hreg.domain_card hP hE hr (hsub γ hγ)⟩
    rw [he, Finset.card_sdiff_of_subset (hsub γ hγ), hE]
  by_cases hd : d = 0
  · exfalso
    obtain ⟨_, hE, hbad, _⟩ := hshort_mark γ₀ hγ₀
    have hg : goodSet u (D \ F) γ₀ (P γ₀) = D \ F := by
      apply le_antisymm (Finset.filter_subset _ _)
      intro i hi
      by_contra hn
      have he : i ∈ errorSet u (D \ F) γ₀ (P γ₀) := Finset.mem_sdiff.mpr ⟨hi, hn⟩
      rw [hd, Finset.card_eq_zero] at hE
      exact Finset.notMem_empty i (hE ▸ he)
    apply hbad
    rw [hg]
    have hQker0 : (planeMatrix u (D \ F) a 0).mulVec (fun j => Q.coeff j.val) = 0 :=
      Eq.mp (congrArg (fun n => (planeMatrix u (D \ F) a n).mulVec (fun j => Q.coeff j.val) = 0) hd) hQker
    exact joint_of_zero_error_kernel u (D \ F) a (by simpa only [hd, add_zero] using hD)
      Q hQ0 (by simpa only [hd] using hQd) hQker0
  have hgen : ((planeMatrix u (D \ F) a d).map (algebraMap Bivar (FractionRing Bivar))).rank = d := by
    apply le_antisymm (generic_rank_le_of_locator _ hQ0 hQd hQker)
    calc
      d = ((planeMatrix u (D \ F) a d).map (onGraph γ₀)).rank := (hshort_mark γ₀ hγ₀).2.2.2.symm
      _ ≤ _ := K21_2_3.rank_ge_specialization _ (onGraph γ₀) _ (IsFractionRing.injective Bivar _)
  have hshort : RegularPlane u (D \ F) a d Γ P := ⟨hD, hgen, hshort_mark⟩
  obtain ⟨L', hL', hbox'⟩ := hbox u (D \ F) Γ P a d (by omega) (by omega) hΓ hshort
  have hno' (i : I) (hi : i ∈ D \ F) : nodeEquation L' i ≠ 0 :=
    repack_node_nonzero _ hgen (locator_nonzero hL' hΓ) hQ0 hL'.degree hQd hL'.kernel hQker i (hno i hi)
  have hda : a < d := by
    by_contra hn
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [(hshort_mark γ₀ hγ₀).2.1]; omega)
    have hzero := (K21_2_4_1.root_iff_error hL' hγ₀ i).mpr hi
    have hz : d-a = 0 := by omega
    apply hno' i (Finset.mem_sdiff.mp hi).1
    exact constant_node_specialization (by simpa only [hz] using nodeEquation_box L' _ _ hbox' i) γ₀ hzero
  have hfb : F.card < b := by omega
  have heq : d = a+(b-F.card) := by omega
  have hbeq : d-a = b-F.card := by omega
  exact Or.inr ⟨F, L', hF, hfb, hsub, heq ▸ hshort,
    ⟨heq ▸ hL'.degree, heq ▸ hL'.kernel, fun j => hbeq ▸ hbox' j, hno', hL'.fiber⟩⟩

end

end K21_2_4_1
end Port_K1_2_4_1Split

section Port_K1_2_4_1_1Fiber
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace K21_2_4_1_1

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K21 K21_2

/-- At exact error weight and rank, the leading columns retain the whole rank,
and each block has an independent prefix of the required length. -/
theorem fiber_data {u : Words} {D : Finset I} {a d : ℕ} {γ : K} {P : K[X]}
    (hD : D.card = 131072+a+d) (hP : P.degree < 131072)
    (hE : (errorSet u D γ P).card = d)
    (hrank : ((planeMatrix u D a d).map (onGraph γ)).rank = d) :
    let M := (planeMatrix u D a d).map (onGraph γ)
    let A := M.submatrix id Fin.castSucc
    A.rank = d ∧
      (∀ b : Fin 2, LinearIndependent K (fun j : Fin (min a d) =>
        A.row (b, j.castLE (min_le_left _ _)))) ∧
      M.mulVec (fun j => (locator node (errorSet u D γ P)).coeff j.val) = 0 := by
  classical
  dsimp only
  let M := (planeMatrix u D a d).map (onGraph γ)
  let x : D → K := fun i => node i.val
  let w : D → K := fun i => u 0 i.val + γ * u 1 i.val
  let σ := Strata.twoConjugations (frobenius K p)
  let E := (errorSet u D γ P).subtype (· ∈ D)
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have herr (i : D) : i ∈ E ↔ P.eval (x i) ≠ w i := by
    simp [E, errorSet, goodSet, x, w, Finset.mem_subtype, i.property]
  have hagree (i : D) (hi : i ∉ E) : w i = P.eval (x i) := by
    by_contra hn
    exact hi ((herr i).mpr (Ne.symm hn))
  have hEc : Fintype.card E = d := by
    have heq : E.map (Function.Embedding.subtype (· ∈ D)) = errorSet u D γ P :=
      Finset.subtype_map_of_mem (fun i hi => (Finset.mem_sdiff.mp hi).1)
    rw [Fintype.card_coe, ← Finset.card_map (f := Function.Embedding.subtype (· ∈ D)), heq, hE]
  have hfix (b : Fin 2) (i : D) : σ b (x i) = x i := by
    fin_cases b
    · rfl
    · exact Native.native_domain_fixed i.val
  let W (b : Fin 2) (i : E) := weight x i.val * σ b (w i.val - P.eval (x i.val))
  let H : Matrix (Fin 2 × Fin a) E K := fun j i => W j.1 i * x i.val ^ j.2.val
  let V := Strata.nodeVandermonde (fun i : E => x i.val) d
  have hfactor : M = H * V := by
    change (planeMatrix u D a d).map (onGraph γ) = _
    rw [K21_2_3.plane_at_slope]
    exact Strata.conjugateHankel_factorization σ x w hx hfix P 131072 a d hP
      (by rw [Fintype.card_coe, hD]) E hagree
  let e : Fin d ≃ E := (Fintype.equivFinOfCardEq hEc).symm
  let y : Fin d → K := fun i => x (e i).val
  have hy : Function.Injective y := hx.comp (Subtype.val_injective.comp e.injective)
  let C := H.submatrix id e
  have hC : C.rank = d := by
    have hlo := Matrix.rank_mul_le_left H V
    rw [← hfactor, show M.rank = d from hrank] at hlo
    have hhi := H.rank_le_card_width
    rw [hEc] at hhi
    rw [show C.rank = H.rank from Matrix.rank_submatrix H (Equiv.refl _) e]
    exact le_antisymm hhi hlo
  have hlead : M.submatrix id Fin.castSucc = C * Matrix.vandermonde y := by
    rw [hfactor]
    exact Matrix.submatrix_mul H V id e Fin.castSucc e.bijective
  have hdet := Matrix.det_vandermonde_ne_zero_iff.mpr hy
  refine ⟨?_, ?_, ?_⟩
  · rw [show ((planeMatrix u D a d).map (onGraph γ)).submatrix id Fin.castSucc =
        M.submatrix id Fin.castSucc from rfl, hlead, Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hdet, hC]
  · intro b
    let m := min a d
    let r : Fin m → Fin 2 × Fin a := fun j => (b, j.castLE (min_le_left _ _))
    let c : Fin m ↪ Fin d := Fin.castLEEmb (min_le_right _ _)
    have hW (i : Fin d) : W b (e i) ≠ 0 := by
      apply mul_ne_zero (Strata.weight_ne_zero x hx _)
      intro hz
      have he := (σ b).injective (hz.trans (map_zero _).symm)
      exact ((herr (e i).val).mp (e i).property) (sub_eq_zero.mp he).symm
    have hsquare : C.submatrix r c =
        (Matrix.vandermonde (y ∘ c)).transpose * Matrix.diagonal (fun i => W b (e (c i))) := by
      apply Matrix.ext
      intro j k
      simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.transpose_apply,
        Matrix.vandermonde_apply, Function.comp_apply, C, H, r, y]
      exact mul_comm _ _
    have hsq : (C.submatrix r c).det ≠ 0 := by
      rw [hsquare, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
      exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr (hy.comp c.injective))
        (Finset.prod_ne_zero_iff.mpr fun i _ => hW (c i))
    have hprefix : (C.submatrix r id).rank = m := by
      have hlo := Matrix.rank_submatrix_le (C.submatrix r id) id c
      change (C.submatrix r c).rank ≤ _ at hlo
      rw [Matrix.rank_of_det_ne_zero hsq, Fintype.card_fin] at hlo
      exact le_antisymm (by simpa using (C.submatrix r id).rank_le_card_height) hlo
    change LinearIndependent K ((M.submatrix id Fin.castSucc).submatrix r id).row
    have hsub : (C * Matrix.vandermonde y).submatrix r id =
        C.submatrix r id * Matrix.vandermonde y := rfl
    rw [hlead, hsub]
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row,
      Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hdet, hprefix, Fintype.card_fin]
  · let T := locator node (errorSet u D γ P)
    have hTd : T.natDegree ≤ d := by
      change (locator node _).natDegree ≤ d
      rw [locator_natDegree, hE]
    have hv : V.mulVec (fun j => T.coeff j.val) = 0 := by
      funext i
      change (∑ j : Fin (d+1), x i.val ^ j.val * T.coeff j.val) = 0
      have hz : T.eval (x i.val) = 0 :=
        locator_eval_zero node (errorSet u D γ P) i.val.val (Finset.mem_subtype.mp i.property)
      rw [← hz, ← sum_coeff_eval T d hTd]
      exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    change M.mulVec (fun j => T.coeff j.val) = 0
    rw [hfactor, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

end

end K21_2_4_1_1
end Port_K1_2_4_1_1Fiber

section Port_K1_2_4_3Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

namespace K21_2_4_3

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator
open K21 K21_2

/-- Once common errors have been punctured, each node contributes only
the roots of its nonzero locator evaluation polynomial. -/
private theorem moving_count {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (x u v : ι → F) (hx : Function.Injective x) (k a r : ℕ)
    (hr : 0 < r) (hra : r < a) (hn : k + a + r = Fintype.card ι)
    (Γ : Finset F) (P : F → F[X]) (E : F → Finset ι) (hlarge : r + 1 < Γ.card)
    (hP : ∀ γ ∈ Γ, (P γ).degree < k)
    (hE : ∀ γ ∈ Γ, (E γ).card = r)
    (hout : ∀ γ ∈ Γ, ∀ i, i ∉ E γ → u i + γ * v i = (P γ).eval (x i))
    (hin : ∀ γ ∈ Γ, ∀ i ∈ E γ, u i + γ * v i ≠ (P γ).eval (x i))
    (hmoving : ∀ i, ∃ γ ∈ Γ, i ∉ E γ) :
    Γ.card ≤ Fintype.card ι / (a - r + 1) := by
  classical
  let s := a - r + 1
  let M := hankel x u v a r
  let φ := algebraMap F[X] (GenericLayer.GenericField F)
  have hφ := IsFractionRing.injective F[X] (GenericLayer.GenericField F)
  have heval (γ : F) (hγ : γ ∈ Γ) : (M.map (evalRingHom γ)).rank = r := by
    rw [K1_3.evaluated_hankel_rank x u v hx γ (P γ) k a r (hP γ hγ) hn.le (E γ)
      (by rw [hE γ hγ]; omega) (hout γ hγ) (hin γ hγ), hE γ hγ, min_eq_left hra.le]
  have hentry (i : Fin a) (j : Fin (r + 1)) : (M i j).natDegree ≤ 1 :=
    hankel_entry_natDegree x u v a r i j
  have hupper : (M.map φ).rank ≤ r := by
    by_contra! hnrank
    have hwidth := Matrix.rank_le_card_width (M.map φ)
    rw [Fintype.card_fin] at hwidth
    have hfull : (M.map φ).rank = r + 1 := by omega
    obtain ⟨B⟩ := NormalFiber.exists_rowBasis φ M (r + 1) hfull
    have hdeg : (NormalFiber.pivot B).det.natDegree ≤ r + 1 := by
      simpa using NormalFiber.minor_degree_le φ M (r + 1) B (fun _ => 1) hentry
    have hcard : Γ.card ≤ (NormalFiber.pivot B).det.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro γ hγ
      apply (Polynomial.mem_roots B.minor_ne).mpr
      by_contra hnonzero
      have hnormal := NormalFiber.rank_specializes φ hφ M (r + 1) B γ hnonzero
      have hactual := heval γ hγ
      omega
    omega
  let seq (j : ℕ) := Polynomial.C (syndrome x u j) + Polynomial.X * Polynomial.C (syndrome x v j)
  let A := Matrix.of (fun (i j : Fin r) => seq (i.val + j.val))
  have hpivotEval (γ : F) (hγ : γ ∈ Γ) : (A.map (evalRingHom γ)).det ≠ 0 := by
    have heq : A.map (evalRingHom γ) =
        Matrix.of (fun (i j : Fin r) => syndrome x (fun i => u i + γ * v i) (i.val + j.val)) := by
      ext i j
      exact congrFun (congrFun (K1_3.evaluated_hankel x u v γ r r) i) (Fin.castSucc j)
    rw [heq]
    exact K1_3.moment_det_ne_zero x _ hx (P γ) k r (hP γ hγ) (by omega)
      (E γ) (hE γ hγ) (hout γ hγ) (hin γ hγ)
  obtain ⟨γ₀, hγ₀⟩ : Γ.Nonempty := Finset.card_pos.mp (by omega)
  have hpivot : A.det ≠ 0 := by
    intro hz
    apply hpivotEval γ₀ hγ₀
    rw [← RingHom.mapMatrix_apply, ← (evalRingHom γ₀).map_det, hz, map_zero]
  have hAφ : (A.map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← φ.map_det]
    exact fun hz => hpivot (hφ (hz.trans (map_zero φ).symm))
  let rows (i : Fin r) : Fin a := ⟨i.val, i.isLt.trans hra⟩
  have hlower := Matrix.rank_submatrix_le (M.map φ) rows Fin.castSucc
  change (A.map φ).rank ≤ (M.map φ).rank at hlower
  rw [Matrix.rank_of_det_ne_zero hAφ, Fintype.card_fin] at hlower
  obtain ⟨B⟩ := NormalFiber.exists_rowBasis φ M r (le_antisymm hupper hlower)
  obtain ⟨q, hprim, hker, _, _⟩ := GenericCofactor.exists_primitive_line B hφ (by simp)
    (fun _ => 1) hentry
  obtain ⟨H, hH, hsharp⟩ := sharp_hankel_height seq r s (by omega)
    (fun j => by dsimp [seq]; compute_degree) q hprim
    (fun i hi => congrFun hker ⟨i, by dsimp [s] at hi; omega⟩) hpivot
  let Q (i : ι) : F[X] := ∑ j : Fin (r + 1), Polynomial.C (x i ^ j.val) * q j
  have hQdeg (i : ι) : (Q i).natDegree ≤ H :=
    Polynomial.natDegree_sum_le_of_forall_le _ _
      (fun j _ => (Polynomial.natDegree_C_mul_le _ _).trans (hH j))
  have hQroots (γ : F) (hγ : γ ∈ Γ) (i : ι) : (Q i).eval γ = 0 ↔ i ∈ E γ := by
    let L := locator x (E γ)
    have hLd : L.natDegree = r := (locator_natDegree _ _).trans (hE γ hγ)
    have hLtop : L.coeff r = 1 := hLd ▸ (locator_monic x (E γ)).coeff_natDegree
    have hL0 : (fun j : Fin (r + 1) => L.coeff j.val) ≠ 0 := by
      intro hz
      have hh : L.coeff r = 0 := congrFun hz (Fin.last r)
      exact one_ne_zero (hLtop.symm.trans hh)
    have hLker : (M.map (evalRingHom γ)).mulVec (fun j => L.coeff j.val) = 0 := by
      apply hankel_annihilates x hx u v γ k a r hn.le (P γ) L (hP γ hγ) hLd.le
      intro j
      by_cases hj : j ∈ E γ
      · simp [L, locator_eval_zero x (E γ) j hj]
      · rw [hout γ hγ j hj]
    have hqker : (M.map (evalRingHom γ)).mulVec (fun j => (q j).eval γ) = 0 := by
      funext i
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Polynomial.coe_evalRingHom,
        map_sum, map_mul, map_zero, Pi.zero_apply] using
        congrArg (evalRingHom γ) (congrFun hker i)
    have hnull := GenericRank.nullity_one_of_rank (M.map (evalRingHom γ))
      (by rw [heval γ hγ, Fintype.card_fin])
    obtain ⟨c, hc⟩ := GenericRank.kernel_line_of_finrank _ hnull _ hL0 hLker _ hqker
    have hcne : c ≠ 0 := by
      intro hz
      exact PrimitiveVector.eval_ne_zero q hprim γ (by simp [hc, hz])
    have hQeval : (Q i).eval γ = c * L.eval (x i) := by
      rw [← sum_coeff_eval L r hLd.le, Finset.mul_sum]
      simp only [Q, eval_finsetSum, eval_mul, eval_C]
      apply Finset.sum_congr rfl
      intro j _
      rw [congrFun hc j]
      change x i ^ j.val * (c * L.coeff j.val) = c * (L.coeff j.val * x i ^ j.val)
      ring
    rw [hQeval, mul_eq_zero, or_iff_right hcne]
    exact Principal.locator_eval_zero_iff x hx _ i
  have hfiber (i : ι) : (Γ.filter (fun γ => i ∈ E γ)).card ≤ H := by
    obtain ⟨γ, hγ, hi⟩ := hmoving i
    have hne : Q i ≠ 0 := fun hz => hi ((hQroots γ hγ i).mp (by simp [hz]))
    apply (Polynomial.card_le_degree_of_subset_roots ?_).trans (hQdeg i)
    intro ζ hζ
    exact (Polynomial.mem_roots hne).mpr ((hQroots ζ (Finset.mem_filter.mp hζ).1 i).mpr
      (Finset.mem_filter.mp hζ).2)
  have hinc := K1_2.Pruning.root_incidence Γ Finset.univ ∅ E r
    (fun γ _ => Finset.subset_univ (E γ)) hE
  simp only [Finset.card_empty, Nat.sub_zero, Finset.sdiff_empty] at hinc
  have hdouble : r * Γ.card ≤ Fintype.card ι * H := hinc.trans (by
    calc
      _ ≤ ∑ _i : ι, H := Finset.sum_le_sum (fun i _ => hfiber i)
      _ = _ := by simp)
  apply (Nat.le_div_iff_mul_le (by omega : 0 < s)).mpr
  apply Nat.le_of_mul_le_mul_right _ hr
  calc
    (Γ.card * s) * r = (r * Γ.card) * s := by ac_rfl
    _ ≤ (Fintype.card ι * H) * s := Nat.mul_le_mul_right _ hdouble
    _ = Fintype.card ι * (s * H) := by ac_rfl
    _ ≤ Fintype.card ι * r := Nat.mul_le_mul_left _ hsharp

theorem proof : K21_2_4.c3 := by
  classical
  intro u D Γ P a d hda hD hmark
  have hfloor : 1 ≤ (131072 + a + d) / (a - d + 1) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  by_cases hs : Γ.card ≤ d + 1
  · omega
  have hlarge : d + 1 < Γ.card := by omega
  obtain ⟨γ₀, hγ₀⟩ : Γ.Nonempty := Finset.card_pos.mp (by omega)
  let F := D.filter (fun i => ∀ γ ∈ Γ, i ∈ errorSet u D γ (P γ))
  let B := D \ F
  let r := d - F.card
  have hF (γ : K) (hγ : γ ∈ Γ) : F ⊆ errorSet u D γ (P γ) :=
    fun _ hi => (Finset.mem_filter.mp hi).2 γ hγ
  have hFD : F ⊆ D := Finset.filter_subset _ _
  have hFle : F.card ≤ d := (Finset.card_le_card (hF γ₀ hγ₀)).trans (hmark γ₀ hγ₀).2.1.le
  have hB : B.card = 131072 + a + r := by
    rw [Finset.card_sdiff_of_subset hFD, hD]
    dsimp [r]
    omega
  have hgood (γ : K) (hγ : γ ∈ Γ) (i : I) :
      i ∈ goodSet u D γ (P γ) → i ∈ B := by
    intro hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hi).1, fun hf =>
      (Finset.mem_sdiff.mp (hF γ hγ hf)).2 hi⟩
  let x (i : B) : K := node i.val
  let E (γ : K) : Finset B := Finset.univ.filter (fun i => i.val ∈ errorSet u D γ (P γ))
  have hE (γ : K) (hγ : γ ∈ Γ) : (E γ).card = r := by
    let f : B ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
    have heq : (E γ).map f = errorSet u D γ (P γ) \ F := by
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hj).2, (Finset.mem_sdiff.mp j.property).2⟩
      · intro hi
        obtain ⟨he, hf⟩ := Finset.mem_sdiff.mp hi
        let j : B := ⟨i, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp he).1, hf⟩⟩
        exact Finset.mem_map.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
    rw [← Finset.card_map f, heq, Finset.card_sdiff_of_subset (hF γ hγ), (hmark γ hγ).2.1]
  have hout (γ : K) (i : B) (hi : i ∉ E γ) :
      u 0 i.val + γ * u 1 i.val = (P γ).eval (x i) := by
    apply Eq.symm
    have hnot : i.val ∉ errorSet u D γ (P γ) :=
      fun he => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    have hiD := (Finset.mem_sdiff.mp i.property).1
    by_contra hn
    apply hnot
    exact Finset.mem_sdiff.mpr ⟨hiD, fun hg => hn (Finset.mem_filter.mp hg).2⟩
  by_cases hr : 0 < r
  · have hc := moving_count x (fun i => u 0 i.val) (fun i => u 1 i.val)
      (ProximityPrize.Benchmark.IRSProfile.domain.injective.comp Subtype.val_injective)
      131072 a r hr (by dsimp [r]; omega) (by simpa using hB.symm) Γ P E
      (by dsimp [r]; omega) (fun γ hg => (hmark γ hg).1) hE (fun γ _ => hout γ) ?_ ?_
    · have hn : Fintype.card B ≤ 131072 + a + d := by rw [Fintype.card_coe, hB]; dsimp [r]; omega
      have hrd : r ≤ d := Nat.sub_le _ _
      have hdiv : (131072 + a + d) / (a - r + 1) ≤ (131072 + a + d) / (a - d + 1) :=
        Nat.div_le_div_left (by omega) (by omega)
      exact (hc.trans ((Nat.div_le_div_right hn).trans hdiv)).trans (Nat.le_add_left _ _)
    · intro γ _ i hi he
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).2).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp i.property).1, he.symm⟩)
    · intro i
      by_contra! hi
      apply (Finset.mem_sdiff.mp i.property).2
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp i.property).1,
        fun γ hg => (Finset.mem_filter.mp (hi γ hg)).2⟩
  · have hsmall := K1_3.fixed_error_count node (u 0) (u 1) 131072 Γ (Finset.univ \ B) P
      (fun γ => goodSet u D γ (P γ)) (fun γ hg => (hmark γ hg).1) ?_ ?_
      (fun γ hg => (hmark γ hg).2.2)
    · omega
    · intro γ hg i hi
      have hmem : i ∈ B := by simpa using hi
      have he : E γ = ∅ := Finset.card_eq_zero.mp (by rw [hE γ hg]; omega)
      exact hout γ ⟨i, hmem⟩ (by simp [he])
    · intro γ hg i hi h
      exact (Finset.mem_sdiff.mp h).2 (hgood γ hg i hi)

end

end K21_2_4_3
end Port_K1_2_4_3Proof

section Port_K1_2_4_2Contraction
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K21_2_4_2

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K21 K21_2 K21_2_4

/-- Coefficients of multiplication by a fixed polynomial on bounded inputs. -/
def convolution {F : Type*} [CommRing F] (Δ : F[X]) (R d : ℕ) :
    Matrix (Fin (R + 1)) (Fin (d + 1)) F :=
  fun j k => (Δ * Polynomial.X ^ k.val).coeff j.val

theorem convolution_map {F E : Type*} [CommRing F] [CommRing E]
    (φ : F →+* E) (Δ : F[X]) (R d : ℕ) :
    (convolution Δ R d).map φ = convolution (Δ.map φ) R d := by
  ext j k
  change φ ((Δ * Polynomial.X ^ k.val).coeff j.val) = _
  rw [← Polynomial.coeff_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  rfl

theorem convolution_action {F : Type*} [CommRing F] (Δ T : F[X]) (R d : ℕ)
    (hT : T.natDegree ≤ d) :
    (convolution Δ R d).mulVec (fun j => T.coeff j.val) =
      fun j => (Δ * T).coeff j.val := by
  have hsum : T = ∑ k : Fin (d + 1), Polynomial.C (T.coeff k.val) *
      (Polynomial.X (R := F)) ^ k.val := by
    rw [Fin.sum_univ_eq_sum_range (fun n => Polynomial.C (T.coeff n) *
      (Polynomial.X (R := F)) ^ n)]
    exact T.as_sum_range_C_mul_X_pow' (by omega)
  funext j
  have heq : Δ * T = ∑ k : Fin (d + 1), Polynomial.C (T.coeff k.val) *
      (Δ * Polynomial.X ^ k.val) := by
    calc
      Δ * T = Δ * (∑ k : Fin (d + 1), Polynomial.C (T.coeff k.val) *
          (Polynomial.X (R := F)) ^ k.val) :=
        congrArg (Δ * ·) hsum
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  rw [heq, finsetSum_coeff]
  simp only [Matrix.mulVec, dotProduct, convolution, coeff_C_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

def contracted (u : Words) (D F : Finset I) (a R d : ℕ) :
    Matrix (Fin 2 × Fin a) (Fin (d + 1)) Bivar :=
  planeMatrix u D a R * (convolution (locator node F) R d).map planeConstant

theorem eval_nodeEquation {E : Type*} [Field E] (φ : Bivar →+* E)
    (L : Bivar[X]) (i : I) :
    φ (nodeEquation L i) = (L.map φ).eval (φ (planeConstant (node i))) := by
  rw [nodeEquation, Polynomial.eval_map_apply]

theorem graph_constant (γ c : K) : onGraph γ (planeConstant c) = c := by
  rw [K21_2_4.evalGraph]
  simp [planeConstant]

/-- The fixed-node equations divide the locator after any specialization
that kills them. Multiplication by that divisor contracts the matrix. -/
theorem contracted_kernel {E : Type} [Field E] (φ : Bivar →+* E)
    {u : Words} {D F : Finset I} {a R d : ℕ} {L : Bivar[X]}
    (hsize : R = d + F.card) (hL : L.natDegree ≤ R)
    (hker : (planeMatrix u D a R).mulVec (fun j => L.coeff j.val) = 0)
    (hF : ∀ i ∈ F, φ (nodeEquation L i) = 0) (hL0 : L.map φ ≠ 0) :
    ∃ T : E[X], T ≠ 0 ∧ T.natDegree ≤ d ∧
      L.map φ = locator (φ ∘ planeConstant ∘ node) F * T ∧
      ((contracted u D F a R d).map φ).mulVec (fun j => T.coeff j.val) = 0 := by
  classical
  let x := φ ∘ planeConstant ∘ node
  have hx : Function.Injective x :=
    (φ.comp planeConstant).injective.comp IRSProfile.domain.injective
  have hdiv : locator x F ∣ L.map φ :=
    Strata.locator_dvd_of_eval_zero x hx F _ (fun i hi =>
      (eval_nodeEquation φ L i).symm.trans (hF i hi))
  obtain ⟨T, hfactor⟩ := hdiv
  have hT0 : T ≠ 0 := fun hz => hL0 (by rw [hfactor, hz, mul_zero])
  have hdegree := (Polynomial.natDegree_map_le (f := φ) (p := L)).trans hL
  rw [hfactor, Polynomial.natDegree_mul (locator_monic x F).ne_zero hT0,
    locator_natDegree] at hdegree
  have hTd : T.natDegree ≤ d := by omega
  refine ⟨T, hT0, hTd, hfactor, ?_⟩
  have hmap : ((planeMatrix u D a R).map φ).mulVec
      (fun j => (L.map φ).coeff j.val) = 0 := by
    funext j
    have hj := congrArg φ (congrFun hker j)
    simpa only [RingHom.map_mulVec, Function.comp_def, Pi.zero_apply, map_zero,
      coeff_map] using hj
  have hc :
      ((convolution (locator node F) R d).map planeConstant).map φ =
        convolution (locator x F) R d := by
    change ((convolution (locator node F) R d).map (φ.comp planeConstant)) = _
    rw [convolution_map, locator_map]
    rfl
  rw [contracted, Matrix.map_mul, hc, ← Matrix.mulVec_mulVec, convolution_action _ _ _ _ hTd,
    ← hfactor]
  exact hmap

theorem coeff_vec_ne_zero {E : Type*} [Field E] (T : E[X]) (d : ℕ)
    (hTd : T.natDegree ≤ d) (hT0 : T ≠ 0) :
    (fun j : Fin (d + 1) => T.coeff j.val) ≠ 0 := by
  intro h
  have hz := congrFun h (⟨T.natDegree, by omega⟩ : Fin (d + 1))
  exact hT0 (Polynomial.leadingCoeff_eq_zero.mp hz)

instance curveDomain (Q : Bivar) [Fact (Prime Q)] : IsDomain (AdjoinRoot Q) :=
  AdjoinRoot.isDomain_of_prime Fact.out

abbrev CurveField (Q : Bivar) [Fact (Prime Q)] := FractionRing (AdjoinRoot Q)

def curveMap (Q : Bivar) [Fact (Prime Q)] : Bivar →+* CurveField Q :=
  (algebraMap (AdjoinRoot Q) (CurveField Q)).comp (AdjoinRoot.mk Q)

theorem curveMap_zero_iff (Q V : Bivar) [Fact (Prime Q)] : curveMap Q V = 0 ↔ Q ∣ V := by
  change algebraMap (AdjoinRoot Q) (CurveField Q) (AdjoinRoot.mk Q V) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective (AdjoinRoot Q) (CurveField Q)),
    AdjoinRoot.mk_eq_zero]

end

end K21_2_4_2
end Port_K1_2_4_2Contraction

section Port_K1_2_2_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

namespace K21_2_2_2

noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open K21 K21_2_2 K1_6
open scoped BigOperators

private theorem map_syndrome {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (f : F →+* E) (x w : ι → F) (j : ℕ) :
    f (syndrome x w j) = syndrome (fun i => f (x i)) (fun i => f (w i)) j := by
  simp only [syndrome, weight, map_sum, map_mul, map_pow, map_inv₀, map_prod, map_sub]

private def NodeIdentity {F ι : Type} [Field F] (q : ℕ) (y u v : ι → F)
    (U V out : F[X][X]) : Prop :=
  ∀ i, U.eval (C (y i)) * (C (u i) + Polynomial.X * C (v i)) +
    V.eval (C (y i)) * (C (u i ^ q) + Polynomial.X ^ q * C (v i ^ q)) =
      out.eval (C (y i))

/-- The all-node identity, multiplied by each bounded shift, has an output
whose dual moments vanish on the same domain as the stack. -/
private theorem shifts_annihilate {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (q : ℕ) [ExpChar F q]
    (y u v : ι → F) (hy : Function.Injective y) (hfix : ∀ i, y i ^ q = y i)
    (φ : F[X] →+* E) (hφ : Function.Injective φ)
    (k h L t s : ℕ) (hL : h + s = L + 1)
    (hsize : k + (L + 1) + t ≤ Fintype.card ι)
    (P : Fin 2 → F[X][X]) (out : F[X][X])
    (hP : ∀ b, (P b).natDegree ≤ h)
    (hout : out.degree < (k + h : ℕ))
    (hnodes : NodeIdentity q y u v (P 0) (P 1) out) :
    (shifts P (L + 1) s).transpose * stacked q y u v (L + 1) t = 0 := by
  classical
  let f : F →+* E := φ.comp Polynomial.C
  let x : ι → E := fun i => f (y i)
  let z : E := φ Polynomial.X
  let w (b : Fin 2) (i : ι) : E :=
    if b = 0 then f (u i) + z * f (v i) else f (u i ^ q) + z ^ q * f (v i ^ q)
  have hmoment (b : Fin 2) (l : Fin (L + 1)) (j : Fin (t + 1)) :
      φ (stacked q y u v (L + 1) t (b, l) j) = syndrome x (w b) (l.val + j.val) := by
    by_cases hb : b = 0
    · simp only [stacked, hankel, hb, ite_true, map_add, map_mul]
      change f (syndrome y u _) + z * f (syndrome y v _) = _
      rw [map_syndrome, map_syndrome]
      simpa only [w, hb, ite_true, one_mul] using
        (Principal.syndrome_linear x (fun i => f (u i)) (fun i => f (v i)) 1 z _).symm
    · simp only [stacked, hb, ite_false]
      rw [φ.map_add, φ.map_mul, φ.map_pow Polynomial.X]
      change f (syndrome y u _ ^ q) + z ^ q * f (syndrome y v _ ^ q) = _
      rw [← syndrome_frobenius q y hfix, ← syndrome_frobenius q y hfix,
        map_syndrome, map_syndrome]
      simpa only [w, hb, ite_false, one_mul] using
        (Principal.syndrome_linear x (fun i => f (u i ^ q))
          (fun i => f (v i ^ q)) 1 (z ^ q) _).symm
  have hnode (i : ι) :
      ((P 0).map φ).eval (x i) * w 0 i + ((P 1).map φ).eval (x i) * w 1 i =
        (out.map φ).eval (x i) := by
    simpa only [x, f, RingHom.comp_apply, z, w, ite_true, one_ne_zero, ite_false,
      map_add, map_mul, map_pow, eval_map_apply] using congrArg φ (hnodes i)
  apply Matrix.ext
  intro d j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, shifts]
  apply hφ
  let B (b : Fin 2) : E[X] := (P b).map φ * Polynomial.X ^ d.val
  have hd : h + d.val ≤ L := by have := d.isLt; omega
  have hB (b : Fin 2) : (B b).natDegree ≤ L :=
    natDegree_mul_le.trans (by
      rw [natDegree_X_pow]
      exact (Nat.add_le_add_right (natDegree_map_le.trans (hP b)) _).trans hd)
  have hshift (i : ι) :
      (B 0).eval (x i) * w 0 i + (B 1).eval (x i) * w 1 i =
        ((out.map φ) * Polynomial.X ^ d.val).eval (x i) := by
    simp only [B, eval_mul, eval_pow, eval_X]
    rw [← hnode i]
    ring
  have hdeg : ((out.map φ) * Polynomial.X ^ d.val).degree < ((k + L : ℕ) : WithBot ℕ) := by
    have hmul := Strata.degree_mul_lt_add (Polynomial.X ^ d.val : E[X])
      (out.map φ) d.val (k + h) (by simp) (degree_map_le.trans_lt hout)
    rw [mul_comm] at hmul
    apply hmul.trans_le
    exact_mod_cast (show k + h + d.val ≤ k + L by omega)
  rw [map_sum, map_zero, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [map_mul, hmoment, ← coeff_map, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X]
  change (∑ l : Fin (L + 1), (B 0).coeff l.val * syndrome x (w 0) (l.val + j.val)) +
    (∑ l : Fin (L + 1), (B 1).coeff l.val * syndrome x (w 1) (l.val + j.val)) = 0
  rw [← Strata.syndrome_polynomial_multiple x (w 0) (B 0) L j.val (hB 0),
    ← Strata.syndrome_polynomial_multiple x (w 1) (B 1) L j.val (hB 1)]
  have hlin := Principal.syndrome_linear x
    (fun i => (B 0).eval (x i) * w 0 i) (fun i => (B 1).eval (x i) * w 1 i) 1 1 j.val
  simp only [one_mul] at hlin
  rw [← hlin]
  simp_rw [hshift]
  apply Strata.syndrome_eval_zero x (f.injective.comp hy) _ (k + L) _ hdeg
  have := j.isLt
  omega

private def fieldPower {F : Type} [Field F] (x : F) (n : ℕ) : F := x ^ n

/-- The benchmark's concrete exponentiation agrees with the field power
used by the generic syndrome lemmas. -/
private theorem native_field_power (x : K) (n : ℕ) : fieldPower x n = x ^ n := by
  rw [CompPoly.Extension.Ext.pow_def]
  have hzero : fieldPower x 0 = 1 := pow_zero x
  have hsucc (m : ℕ) : fieldPower x (m + 1) = fieldPower x m * x := pow_succ x m
  induction n with
  | zero => rw [hzero, npowBinRec_zero]
  | succ n ih => rw [hsucc, npowBinRec_succ, ih]

private theorem restricted_nodes (q : ℕ) {u : Words} {S : Finset I} (U V out : Bivar)
    (hnodes : K21_8.relationOnAt q u S (C 1 * U) (C 1 * V) (C 1 * out)) :
    NodeIdentity q (fun i : (Finset.univ \ S : Finset I) => node i.val)
      (fun i => u 0 i.val) (fun i => u 1 i.val) U V out := by
  intro i
  have hi : i.val ∉ S := (Finset.mem_sdiff.mp i.property).2
  change U.eval (C (node i.val)) * (C (u 0 i.val) + Polynomial.X * C (u 1 i.val)) +
    V.eval (C (node i.val)) *
      (C (fieldPower (u 0 i.val) q) + Polynomial.X ^ q * C (fieldPower (u 1 i.val) q)) =
    out.eval (C (node i.val))
  rw [native_field_power, native_field_power]
  have h := hnodes i.val hi
  simpa only [Polynomial.C_1, one_mul] using h

private theorem native_relation : relationOn = K21_8.relationOnAt p := rfl

theorem proof : K21_2_2.c2 := by
  classical
  intro u T R A
  let D := Finset.univ \ fixedNodes R
  have hheight : T.height ≤ 49058 := by
    unfold TwoActive.height
    have := T.inactive
    omega
  have hL : A.height + (49058 - A.height) = 49057 + 1 := by
    have := A.height_eq
    omega
  have hsize : 131072 + (49057 + 1) + (82014 - (fixedNodes R).card) ≤ Fintype.card D := by
    rw [Fintype.card_coe, domain_card]
    have := A.height_eq
    omega
  refine shifts_annihilate (F := K) (E := Frac) (ι := D) p
    (fun i => node i.val) (fun i => u 0 i.val) (fun i => u 1 i.val)
    (IRSProfile.domain.injective.comp Subtype.val_injective)
    (fun i => Native.native_domain_fixed i.val)
    (algebraMap K[X] Frac) (IsFractionRing.injective K[X] Frac)
    131072 A.height 49057 _ _ hL hsize (pair A) A.output (pair_degree A) A.output_degree ?_
  apply restricted_nodes p (u := u) (S := fixedNodes R) A.U A.V A.output
  rw [← native_relation]
  exact K21_8.reduced_scaled_relation A (1 : K[X])

end

end K21_2_2_2
end Port_K1_2_2_2Proof

section Port_K1_2_4_1_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace K21_2_4_1_2

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K21 K21_2 K21_2_4 K21_2_4_1
open scoped BigOperators

/-- The dual weight written on a finite set of grid indices. -/
private def gridWeight (D : Finset I) (i : I) : K :=
  (∏ j ∈ D.erase i, (node i - node j))⁻¹

private theorem weight_on_grid (D : Finset I) (i : D) :
    weight (fun j : D => node j.val) i = gridWeight D i.val := by
  classical
  let e : D ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  have hu : (univ : Finset D).map e = D := by
    ext j
    constructor
    · intro hj
      obtain ⟨k, _, hk⟩ := mem_map.mp hj
      exact hk ▸ k.property
    · intro hj
      exact mem_map.mpr ⟨⟨j, hj⟩, mem_univ _, rfl⟩
  have he : ((univ : Finset D).erase i).map e = D.erase i.val := by
    rw [Finset.map_erase, hu]
    rfl
  unfold weight gridWeight
  exact congrArg (fun x : K => x⁻¹)
    ((Finset.prod_map _ e (fun j => node i.val - node j)).symm.trans
      (congrArg (fun S : Finset I => ∏ j ∈ S, (node i.val - node j)) he))

private theorem eval_locator_at_node (F : Finset I) (i : I) :
    (locator node F).eval (node i) = ∏ j ∈ F, (node i - node j) := by
  simp only [locator, eval_prod, eval_sub, eval_X, eval_C]

/-- Recompute the surviving weight by cancelling the nonzero deleted factors. -/
private theorem gridWeight_puncture {D F : Finset I} (hF : F ⊆ D)
    {i : I} (hi : i ∈ D \ F) :
    gridWeight (D \ F) i = gridWeight D i * (locator node F).eval (node i) := by
  have hiF := (mem_sdiff.mp hi).2
  have hs : F ⊆ D.erase i := fun j hj =>
    mem_erase.mpr ⟨fun h => hiF (h ▸ hj), hF hj⟩
  have hprod : (∏ j ∈ D.erase i, (node i - node j)) =
      (∏ j ∈ F, (node i - node j)) * ∏ j ∈ (D \ F).erase i, (node i - node j) := by
    rw [mul_comm, ← erase_sdiff_comm]
    exact (Finset.prod_sdiff hs).symm
  have hnz : (∏ j ∈ F, (node i - node j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj hz =>
      hiF ((IRSProfile.domain.injective (sub_eq_zero.mp hz)).symm ▸ hj))
  simp only [gridWeight, eval_locator_at_node, hprod, _root_.mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hnz, mul_one]

private theorem syndrome_as_sum (D : Finset I) (w : I → K) (n : ℕ) :
    syndrome (fun i : D => node i.val) (fun i => w i.val) n =
      ∑ i ∈ D, gridWeight D i * w i * node i ^ n := by
  unfold syndrome
  simp_rw [weight_on_grid]
  exact Finset.sum_coe_sort D (fun i => gridWeight D i * w i * node i ^ n)

private def rowSeed (b : Fin 2) : Bivar :=
  if b = 0 then Polynomial.C (Polynomial.X (R := K)) else Polynomial.X

private def rowStream (u : Words) (b v : Fin 2) (i : I) : K :=
  if b = 0 then u v i else u v i ^ p

private def rowWord (u : Words) (b : Fin 2) (i : I) : Bivar :=
  planeConstant (rowStream u b 0 i) + rowSeed b * planeConstant (rowStream u b 1 i)

private theorem plane_entry_syndromes (u : Words) (D : Finset I) (a t : ℕ)
    (i : Fin 2 × Fin a) (j : Fin (t + 1)) :
    planeMatrix u D a t i j =
      planeConstant (syndrome (fun z : D => node z.val)
        (fun z => rowStream u i.1 0 z.val) (i.2.val + j.val)) +
      rowSeed i.1 * planeConstant (syndrome (fun z : D => node z.val)
        (fun z => rowStream u i.1 1 z.val) (i.2.val + j.val)) := by
  by_cases h : i.1 = 0
  · simp only [planeMatrix, rowStream, rowSeed, h, ite_true, planeConstant,
      RingHom.comp_apply, map_add, map_mul]
  · simp only [planeMatrix, rowStream, rowSeed, h, ite_false, planeConstant,
      RingHom.comp_apply, syndrome_frobenius p (fun z : D => node z.val)
        (fun z => Native.native_domain_fixed z.val)]

private theorem plane_entry_sum (u : Words) (D : Finset I) (a t : ℕ)
    (i : Fin 2 × Fin a) (j : Fin (t + 1)) :
    planeMatrix u D a t i j =
      ∑ z ∈ D, planeConstant (gridWeight D z) * rowWord u i.1 z *
        planeConstant (node z) ^ (i.2.val + j.val) := by
  rw [plane_entry_syndromes, syndrome_as_sum, syndrome_as_sum]
  simp only [map_sum, Finset.mul_sum, ← Finset.sum_add_distrib, map_mul, map_pow]
  apply Finset.sum_congr rfl
  intro z _
  unfold rowWord
  ring

/-- A row acting on polynomial coefficients is a weighted sum of node evaluations. -/
private theorem plane_row_eval (u : Words) (D : Finset I) (a t : ℕ)
    (L : Bivar[X]) (hL : L.natDegree ≤ t) (i : Fin 2 × Fin a) :
    ((planeMatrix u D a t).mulVec (fun j => L.coeff j.val)) i =
      ∑ z ∈ D, planeConstant (gridWeight D z) * rowWord u i.1 z *
        planeConstant (node z) ^ i.2.val * L.eval (planeConstant (node z)) := by
  simp only [Matrix.mulVec, dotProduct, plane_entry_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  have he : (∑ j : Fin (t + 1), L.coeff j.val * planeConstant (node z) ^ j.val) =
      L.eval (planeConstant (node z)) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => L.coeff j * planeConstant (node z) ^ j)]
    exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hL) _).symm
  rw [← he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

private theorem fixedFactor_eval (F : Finset I) (i : I) :
    (fixedFactor F).eval (planeConstant (node i)) =
      planeConstant ((locator node F).eval (node i)) := by
  rw [fixedFactor, Polynomial.eval_map_apply]

theorem proof : K21_2_4_1.c2 := by
  intro u D F a d hF Q hQ hker
  have hL : (fixedFactor F * Q).natDegree ≤ F.card + d := by
    exact natDegree_mul_le.trans
      (by rw [fixedFactor_natDegree]; exact Nat.add_le_add_left hQ F.card)
  funext i
  have hrow := congrFun hker i
  rw [plane_row_eval u D a _ _ hL, Pi.zero_apply] at hrow
  rw [plane_row_eval u (D \ F) a _ _ hQ, Pi.zero_apply, ← hrow]
  calc
    _ = ∑ z ∈ D \ F, planeConstant (gridWeight D z) * rowWord u i.1 z *
        planeConstant (node z) ^ i.2.val *
          (fixedFactor F * Q).eval (planeConstant (node z)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [gridWeight_puncture hF hz, map_mul, Polynomial.eval_mul, fixedFactor_eval]
      ring
    _ = _ := by
      apply Finset.sum_subset Finset.sdiff_subset
      intro z hz hn
      have hzF : z ∈ F := by
        by_contra h
        exact hn (mem_sdiff.mpr ⟨hz, h⟩)
      rw [Polynomial.eval_mul, fixedFactor_eval, locator_eval_zero node F z hzF,
        map_zero, zero_mul, mul_zero]

end

end K21_2_4_1_2
end Port_K1_2_4_1_2Proof

section Port_K1_2_4_2Cofactors
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K21_2_4_2

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator
open K21 K21_2 K21_2_4

/-- Complete the independent rows in the preferred block to a pivot. -/
theorem select_rows {a d : ℕ} (M : Matrix (Fin 2 × Fin a) (Fin d) K)
    (hM : M.rank = d) (b : Fin 2)
    (hprefix : LinearIndependent K (fun j : Fin (min a d) =>
      M.row (b, j.castLE (min_le_left _ _)))) :
    ∃ rows : Fin d → Fin 2 × Fin a, (M.submatrix rows id).det ≠ 0 ∧
      (Finset.univ.filter (fun j => (rows j).1 = b)).card = min a d := by
  classical
  let f : Fin (min a d) ↪ Fin 2 × Fin a :=
    ⟨fun j => (b, j.castLE (min_le_left _ _)), fun i j h =>
      Fin.ext (congrArg (fun k : Fin 2 × Fin a => k.2.val) h)⟩
  let S := Set.range f
  have hS : LinearIndepOn K M.row S := (linearIndepOn_range_iff f.injective M.row).mpr hprefix
  let T := hS.extend (Set.subset_univ S)
  have hST := hS.subset_extend (Set.subset_univ S)
  have hli : LinearIndependent K (fun i : T => M.row i.val) :=
    (hS.linearIndepOn_extend (Set.subset_univ S)).linearIndependent_restrict
  have hspace : Submodule.span K (Set.range (fun i : T => M.row i.val)) =
      Submodule.span K (Set.range M.row) := by
    have heq : Set.range (fun i : T => M.row i.val) = M.row '' T := by
      ext v
      exact ⟨fun ⟨i, hi⟩ => ⟨i.val, i.property, hi⟩,
        fun ⟨i, hi, hv⟩ => ⟨⟨i, hi⟩, hv⟩⟩
    rw [heq, hS.span_image_extend_eq_span_image (Set.subset_univ S), Set.image_univ]
  have hcard : Fintype.card T = d := by
    rw [← finrank_span_eq_card hli, hspace, ← Matrix.rank_eq_finrank_span_row, hM]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let rows : Fin d → Fin 2 × Fin a := Subtype.val ∘ e
  have hinj : Function.Injective rows := Subtype.val_injective.comp e.injective
  have hpiv : LinearIndependent K (M.submatrix rows id).row := hli.comp e e.injective
  refine ⟨rows, ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hpiv)).ne_zero, ?_⟩
  let B := Finset.univ.filter (fun j => (rows j).1 = b)
  let intoB (j : Fin (min a d)) : B :=
    ⟨e.symm ⟨f j, hST (Set.mem_range_self j)⟩, by simp [B, rows, f]⟩
  have hlo := Fintype.card_le_of_injective intoB (by
    intro i j hij
    apply f.injective
    have he := e.symm.injective (congrArg Subtype.val hij)
    exact congrArg Subtype.val he)
  have hhi := Fintype.card_le_of_injective (fun i : B => (rows i.val).2) (by
    intro i j hij
    apply Subtype.ext
    apply hinj
    exact Prod.ext ((Finset.mem_filter.mp i.property).2.trans
      (Finset.mem_filter.mp j.property).2.symm) hij)
  simp only [Fintype.card_fin, Fintype.card_coe] at hlo hhi
  have hB := Finset.card_le_card (Finset.filter_subset (fun j => (rows j).1 = b) Finset.univ)
  rw [Finset.card_univ, Fintype.card_fin] at hB
  exact le_antisymm (le_min hhi hB) hlo

private theorem affine_degree {F : Type*} [CommRing F] [Nontrivial F] (v w : F) :
    (Polynomial.C v + Polynomial.X * Polynomial.C w).natDegree ≤ 1 := by
  rw [Polynomial.natDegree_C_add]
  exact Polynomial.natDegree_mul_le.trans (by simp)

private theorem matrix_box (u : Words) (D : Finset I) (a R : ℕ) (r : Fin 2 × Fin a)
    (j : Fin (R + 1)) :
    SeedBox (planeMatrix u D a R r j) (if r.1 = 0 then 1 else 0)
      (if r.1 = 0 then 0 else 1) := by
  unfold planeMatrix SeedBox seedDegree
  dsimp only
  split_ifs
  · constructor
    · rw [Polynomial.Bivariate.swap_C, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
      exact affine_degree _ _
    · exact (Polynomial.natDegree_C _).le
  · constructor
    · rw [map_add, map_mul, Polynomial.Bivariate.swap_C_C, Polynomial.Bivariate.swap_C_C,
        Polynomial.Bivariate.swap_Y, ← Polynomial.C_mul, ← Polynomial.C_add]
      exact (Polynomial.natDegree_C _).le
    · exact affine_degree _ _

/-- The appended node-evaluation row turns a pivot into a polynomial cut. -/
def cutMatrix {a d : ℕ} (N : Matrix (Fin 2 × Fin a) (Fin (d + 1)) Bivar)
    (rows : Fin d → Fin 2 × Fin a) (i : I) : Matrix (Fin (d + 1)) (Fin (d + 1)) Bivar :=
  fun j k => Fin.lastCases (planeConstant (node i ^ k.val)) (fun r => N (rows r) k) j

private theorem det_natDegree_le_row {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι A[X]) (v : ι → ℕ) (hP : ∀ j k, (P j k).natDegree ≤ v j) :
    P.det.natDegree ≤ ∑ j, v j := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [Units.smul_def]
  exact (Polynomial.natDegree_smul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans
    (Finset.sum_le_sum fun k _ => hP k (σ k)))

theorem cut_box (u : Words) (D F : Finset I) (a R d : ℕ)
    (rows : Fin d → Fin 2 × Fin a) (i : I) :
    SeedBox (cutMatrix (contracted u D F a R d) rows i).det
      (Finset.univ.filter (fun j => (rows j).1 = 0)).card
      (Finset.univ.filter (fun j => (rows j).1 ≠ 0)).card := by
  let M := cutMatrix (contracted u D F a R d) rows i
  let s : Fin (d + 1) → ℕ := Fin.lastCases 0 (fun j => if (rows j).1 = 0 then 1 else 0)
  let t : Fin (d + 1) → ℕ := Fin.lastCases 0 (fun j => if (rows j).1 ≠ 0 then 1 else 0)
  have hbox (j k : Fin (d + 1)) : SeedBox (M j k) (s j) (t j) := by
    refine Fin.lastCases ?_ (fun r => ?_) j
    · simp [M, cutMatrix, s, t, SeedBox, seedDegree, planeConstant,
        Polynomial.Bivariate.swap_C_C]
    · simp only [M, cutMatrix, s, t, Fin.lastCases_castSucc, contracted, Matrix.mul_apply]
      apply box_sum
      intro l _
      have h := box_mul_constant _ (convolution (locator node F) R d l k) _ _
        (matrix_box u D a R (rows r) l)
      simpa only [planeConstant, Matrix.map_apply, RingHom.comp_apply, ite_not] using h
  have hs : (∑ j, s j) = (Finset.univ.filter (fun j => (rows j).1 = 0)).card := by
    simp only [s, Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last, add_zero,
      Finset.sum_boole, Nat.cast_id]
  have ht : (∑ j, t j) = (Finset.univ.filter (fun j => (rows j).1 ≠ 0)).card := by
    simp only [t, Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last, add_zero,
      Finset.sum_boole, Nat.cast_id]
  constructor
  · change seedDegree M.det ≤ _
    rw [seedDegree, AlgEquiv.map_det, ← hs]
    exact det_natDegree_le_row (A := K[X]) (M.map (Polynomial.Bivariate.swap (R := K))) s
      (fun j k => (hbox j k).1)
  · change M.det.natDegree ≤ _
    rw [← ht]
    exact det_natDegree_le_row (A := K[X]) M t (fun j k => (hbox j k).2)

theorem cut_action {E : Type} [Field E] (φ : Bivar →+* E)
    {a d : ℕ} {N : Matrix (Fin 2 × Fin a) (Fin (d + 1)) Bivar}
    (rows : Fin d → Fin 2 × Fin a) (i : I) {T : E[X]}
    (hTd : T.natDegree ≤ d) (hker : (N.map φ).mulVec (fun j => T.coeff j.val) = 0) :
    ((cutMatrix N rows i).map φ).mulVec (fun j => T.coeff j.val) =
      Fin.lastCases (T.eval (φ (planeConstant (node i)))) (fun _ => 0) := by
  funext j
  refine Fin.lastCases ?_ (fun l => ?_) j
  · rw [Fin.lastCases_last, ← sum_coeff_eval T d hTd (φ (planeConstant (node i)))]
    change (∑ k : Fin (d + 1), φ (cutMatrix N rows i (Fin.last d) k) *
      T.coeff k.val) = _
    apply Finset.sum_congr rfl
    intro k _
    simp only [cutMatrix, Fin.lastCases_last, map_pow]
    exact mul_comm _ _
  · simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, cutMatrix,
      Fin.lastCases_castSucc, Pi.zero_apply] using congrFun hker (rows l)

/-- A pivot over the curve field and a nonzero node evaluation imply
that the augmented determinant is nonzero there. -/
theorem cut_ne_zero {E : Type} [Field E] (φ : Bivar →+* E)
    {a d : ℕ} {N : Matrix (Fin 2 × Fin a) (Fin (d + 1)) Bivar}
    (rows : Fin d → Fin 2 × Fin a) (i : I)
    (hpivot : ((N.map φ).submatrix rows Fin.castSucc).det ≠ 0)
    {T : E[X]} (hTd : T.natDegree ≤ d)
    (hker : (N.map φ).mulVec (fun j => T.coeff j.val) = 0)
    (hnode : T.eval (φ (planeConstant (node i))) ≠ 0) :
    φ (cutMatrix N rows i).det ≠ 0 := by
  classical
  let A := (cutMatrix N rows i).map φ
  let v : Fin (d + 1) → E := fun j => T.coeff j.val
  let B := A.updateCol (Fin.last d) (A.mulVec v)
  have hdet : B.det = v (Fin.last d) * A.det := by
    have hcol : (fun k => ∑ j, v j • A k j) = A.mulVec v := by
      funext k
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    change (A.updateCol (Fin.last d) (A.mulVec v)).det = _
    rw [← hcol]
    exact Matrix.det_updateCol_sum A (Fin.last d) v
  have hAv : A.mulVec v = Fin.lastCases (T.eval (φ (planeConstant (node i)))) (fun _ => 0) :=
    cut_action φ rows i hTd hker
  have hminor : B.submatrix (Fin.last d).succAbove (Fin.last d).succAbove =
      (N.map φ).submatrix rows Fin.castSucc := by
    ext j k
    simp [B, A, cutMatrix]
  have htop (j : Fin d) : B j.castSucc (Fin.last d) = 0 := by
    simp only [B, Matrix.updateCol_self, hAv, Fin.lastCases_castSucc]
  have hbottom : B (Fin.last d) (Fin.last d) = T.eval (φ (planeConstant (node i))) := by
    simp only [B, Matrix.updateCol_self, hAv, Fin.lastCases_last]
  have hB : B.det ≠ 0 := by
    rw [Matrix.det_succ_column B (Fin.last d), Fin.sum_univ_castSucc]
    simp only [htop, hbottom, hminor, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hnode)
      hpivot
  rw [φ.map_det]
  change A.det ≠ 0
  exact fun hz => hB (by rw [hdet, hz, mul_zero])

end

end K21_2_4_2
end Port_K1_2_4_2Cofactors

section Port_K1_2_4_2Anchor
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

namespace K21_2_4_2

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K21 K21_2 K21_2_4

private theorem evaluate_convolution {A ι : Type} [Field A] (x : ι → A)
    (Δ : A[X]) (R d : ℕ) (i : ι) (j : Fin (d + 1))
    (hdeg : (Δ * Polynomial.X ^ j.val).natDegree ≤ R) :
    (Strata.nodeVandermonde x R * convolution Δ R d) i j =
      Δ.eval (x i) * x i ^ j.val := by
  let T := Δ * (Polynomial.X (R := A)) ^ j.val
  calc
    _ = ∑ k : Fin (R + 1), T.coeff k.val * x i ^ k.val := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    _ = T.eval (x i) := sum_coeff_eval T R hdeg (x i)
    _ = _ := by simp only [T, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- The shorter leading columns factor through the surviving actual
errors, with weights multiplied by the fixed-node divisor. -/
theorem anchor_ranks {u : Words} {D F : Finset I} {a R d : ℕ}
    {γ : K} {P : K[X]} (hsize : R = d + F.card)
    (hD : D.card = 131072 + a + R) (hP : P.degree < 131072)
    (hE : (errorSet u D γ P).card = R) (hF : F ⊆ errorSet u D γ P)
    (hrank : ((planeMatrix u D a R).map (onGraph γ)).rank = R) :
    let M := ((contracted u D F a R d).map (onGraph γ)).submatrix id Fin.castSucc
    M.rank = d ∧ ∀ b : Fin 2,
      LinearIndependent K (fun j : Fin (min a d) => M.row (b, j.castLE (min_le_left _ _))) := by
  classical
  dsimp only
  let x : D → K := fun i => node i.val
  let w : D → K := fun i => u 0 i.val + γ * u 1 i.val
  let σ := Strata.twoConjugations (frobenius K p)
  let E := (errorSet u D γ P).subtype (· ∈ D)
  let S := (Finset.univ : Finset E).filter (fun i => i.val.val ∉ F)
  let Δ := locator node F
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have herr (i : D) : i ∈ E ↔ P.eval (x i) ≠ w i := by
    simp [E, errorSet, goodSet, x, w, Finset.mem_subtype, i.property]
  have hnos (i : D) (hi : i ∉ E) : w i = P.eval (x i) :=
    ((not_ne_iff.mp fun hn => hi ((herr i).mpr hn)) : P.eval (x i) = w i).symm
  have hEc : E.card = R := by
    have heq : E.map (Function.Embedding.subtype (· ∈ D)) = errorSet u D γ P :=
      Finset.subtype_map_of_mem (fun i hi => (Finset.mem_sdiff.mp hi).1)
    rw [← Finset.card_map (f := Function.Embedding.subtype (· ∈ D)), heq, hE]
  let eS : S ≃ (errorSet u D γ P \ F : Finset I) := {
    toFun := fun i => ⟨i.val.val.val, Finset.mem_sdiff.mpr
      ⟨(Finset.mem_subtype.mp i.val.property), (Finset.mem_filter.mp i.property).2⟩⟩
    invFun := fun i =>
      let h := Finset.mem_sdiff.mp i.property
      ⟨⟨⟨i.val, (Finset.mem_sdiff.mp h.1).1⟩, Finset.mem_subtype.mpr h.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hSc : Fintype.card S = d := by
    rw [Fintype.card_congr eS, Fintype.card_coe, Finset.card_sdiff_of_subset hF, hE]
    omega
  let e := (Fintype.equivFinOfCardEq hSc).symm
  let ι : Fin d ↪ E := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ S))
  let y : Fin d → K := x ∘ Subtype.val ∘ ι
  have hy : Function.Injective y := hx.comp (Subtype.val_injective.comp ι.injective)
  have hfix (b : Fin 2) (i : D) : σ b (x i) = x i := by
    fin_cases b
    · rfl
    · exact Native.native_domain_fixed i.val
  let W (b : Fin 2) (i : E) := weight x i.val * σ b (w i.val - P.eval (x i.val))
  let H : Matrix (Fin 2 × Fin a) E K := fun j i => W j.1 i * x i.val ^ j.2.val
  let V := Strata.nodeVandermonde (fun i : E => x i.val) R
  have hfactor : (planeMatrix u D a R).map (onGraph γ) = H * V := by
    rw [K21_2_3.plane_at_slope]
    exact Strata.conjugateHankel_factorization σ x w hx hfix P 131072 a R hP
      (by rw [Fintype.card_coe, hD]) E hnos
  have hH : H.rank = Fintype.card E := by
    have hh := Matrix.rank_mul_le_left H V
    rw [← hfactor, hrank] at hh
    rw [Fintype.card_coe, hEc]
    exact le_antisymm (by simpa only [Fintype.card_coe, hEc] using H.rank_le_card_width) hh
  let C : Matrix (Fin 2 × Fin a) (Fin d) K :=
    fun j i => H j (ι i) * Δ.eval (y i)
  have hΔ (i : Fin d) : Δ.eval (y i) ≠ 0 := fun hz =>
    (Finset.mem_filter.mp (e i).property).2
      ((Principal.locator_eval_zero_iff node IRSProfile.domain.injective F _).mp hz)
  have hC : C.rank = d := by
    have hi : LinearIndependent K H.col := by
      apply linearIndependent_iff_card_eq_finrank_span.mpr
      rw [Set.finrank, ← Matrix.rank_eq_finrank_span_cols, hH]
    have hc := (hi.comp ι ι.injective).units_smul (fun i => Units.mk0 (Δ.eval (y i)) (hΔ i))
    have hcol : LinearIndependent K C.col := by
      have heq : C.col = (fun i : Fin d =>
          Units.mk0 (Δ.eval (y i)) (hΔ i) • (H.col ∘ ι) i) := by
        funext i j
        simp only [Matrix.col, C, Function.comp_def, Units.smul_def, Units.val_mk0,
          Pi.smul_apply, smul_eq_mul]
        exact mul_comm _ _
      rw [heq]
      exact hc
    simpa only [← Matrix.rank_eq_finrank_span_cols, Fintype.card_fin, Set.finrank]
      using (linearIndependent_iff_card_eq_finrank_span.mp hcol).symm
  have hconst : (onGraph γ).comp planeConstant = RingHom.id K :=
    RingHom.ext (graph_constant γ)
  have hconv : ((convolution Δ R d).map planeConstant).map (onGraph γ) = convolution Δ R d := by
    change (convolution Δ R d).map ((onGraph γ).comp planeConstant) = _
    rw [hconst]
    rfl
  have hV (i : E) (j : Fin (d + 1)) :
      (V * convolution Δ R d) i j = Δ.eval (x i.val) * x i.val ^ j.val := by
    have hdeg : (Δ * Polynomial.X ^ j.val).natDegree ≤ R := by
      have hh := Polynomial.natDegree_mul_le (p := Δ) (q := (Polynomial.X (R := K)) ^ j.val)
      rw [Polynomial.natDegree_X_pow, show Δ.natDegree = F.card from locator_natDegree _ _] at hh
      have := j.isLt
      omega
    exact evaluate_convolution (fun i : E => x i.val) Δ R d i j hdeg
  have hshort :
      ((contracted u D F a R d).map (onGraph γ)).submatrix id Fin.castSucc =
        C * Matrix.vandermonde y := by
    rw [contracted, Matrix.map_mul, hfactor, hconv, Matrix.mul_assoc]
    apply Matrix.ext
    intro j k
    change (∑ l : E, H j l * (V * convolution Δ R d) l k.castSucc) =
      ∑ l : Fin d, C j l * (Matrix.vandermonde y) l k
    simp only [hV, Fin.val_castSucc, Matrix.vandermonde_apply, C]
    let g (i : E) := H j i * (Δ.eval (x i.val) * x i.val ^ k.val)
    calc
      (∑ i : E, g i) = ∑ i ∈ S, g i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i _ hi
        have hiF : i.val.val ∈ F := by simpa [S] using hi
        simp [g, x, Δ, locator_eval_zero node F i.val.val hiF]
      _ = ∑ i : S, g i.val := (Finset.sum_coe_sort S g).symm
      _ = ∑ i : Fin d, g (e i).val := (Equiv.sum_comp e (fun i : S => g i.val)).symm
      _ = _ := Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)
  have hdet := Matrix.det_vandermonde_ne_zero_iff.mpr hy
  rw [hshort]
  refine ⟨(Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hdet).trans hC, ?_⟩
  intro b
  let m := min a d
  let r : Fin m → Fin 2 × Fin a := fun j => (b, j.castLE (min_le_left _ _))
  let c : Fin m ↪ Fin d := Fin.castLEEmb (min_le_right _ _)
  have hW (i : Fin d) : W b (ι i) ≠ 0 := by
    apply mul_ne_zero (Strata.weight_ne_zero x hx _)
    intro hz
    have he := (σ b).injective (hz.trans (map_zero _).symm)
    exact ((herr (ι i).val).mp (ι i).property) (sub_eq_zero.mp he).symm
  have hsquare : C.submatrix r c =
      (Matrix.vandermonde (y ∘ c)).transpose *
        Matrix.diagonal (fun i => W b (ι (c i)) * Δ.eval (y (c i))) := by
    apply Matrix.ext
    intro j k
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.transpose_apply,
      Matrix.vandermonde_apply, Function.comp_apply, C, H, r, Fin.val_castLE, y]
    ring
  have hsq : (C.submatrix r c).det ≠ 0 := by
    rw [hsquare, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr (hy.comp c.injective))
      (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (hW (c i)) (hΔ (c i)))
  have hprefix : (C.submatrix r id).rank = m := by
    have hlo := Matrix.rank_submatrix_le (C.submatrix r id) id c
    change (C.submatrix r c).rank ≤ _ at hlo
    rw [Matrix.rank_of_det_ne_zero hsq, Fintype.card_fin] at hlo
    exact le_antisymm (by simpa using (C.submatrix r id).rank_le_card_height) hlo
  have hsub : (C * Matrix.vandermonde y).submatrix r id =
      C.submatrix r id * Matrix.vandermonde y := by
    apply Matrix.ext
    intro i j
    rfl
  change LinearIndependent K ((C * Matrix.vandermonde y).submatrix r id).row
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row, hsub,
    Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hdet, hprefix, Fintype.card_fin]

end

end K21_2_4_2
end Port_K1_2_4_2Anchor

section Port_K1_2_4_1_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace K21_2_4_1_1

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator
open K21 K21_2 K21_2_4 K21_2_4_1

private theorem map_kernel {R S row col : Type*} [CommRing R] [CommRing S] [Fintype col]
    (φ : R →+* S) (M : Matrix row col R) (v : col → R) (hv : M.mulVec v = 0) :
    (M.map φ).mulVec (fun j => φ (v j)) = 0 := by
  funext i
  simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_mul, map_sum, map_zero,
    Pi.zero_apply] using congrArg φ (congrFun hv i)

/-- A primitive generator divides every integral vector on its rational line.
The gcd argument applies over the plane even when its coordinates have a
common zero in codimension two. -/
private theorem polynomial_multiple {R col : Type*} [CommRing R] [IsDomain R]
    [NormalizedGCDMonoid R] [Fintype col] (Q V : col → R) (k : col) (hQ : Q k ≠ 0)
    (hprim : Finset.univ.gcd Q = 1) (hcross : ∀ j, V j * Q k = V k * Q j) :
    ∃ g, ∀ j, V j = g * Q j := by
  classical
  have hd : Q k ∣ Finset.univ.gcd (fun j => V k * Q j) := Finset.dvd_gcd fun j _ => by
    rw [← hcross j]
    exact dvd_mul_left _ _
  have h := hd.trans (Finset.gcd_mul_left' Finset.univ Q (V k)).dvd
  rw [hprim, mul_one] at h
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun j => mul_right_cancel₀ hQ ?_⟩
  rw [hcross j, hg]
  ring

theorem proof : K21_2_4_1.c1 := by
  classical
  let : NormalizedGCDMonoid Bivar := UniqueFactorizationMonoid.toNormalizedGCDMonoid Bivar
  intro u D Γ P a d _ _ hΓ hreg
  let M := planeMatrix u D a d
  let V (rows : Fin d → Fin 2 × Fin a) := cofactor (M.submatrix rows id)
  let k := Fin.last d
  let φ := algebraMap Bivar (FractionRing Bivar)
  have hφ : Function.Injective φ := IsFractionRing.injective Bivar _
  have hfne {x : Bivar} (h : x ≠ 0) : φ x ≠ 0 :=
    fun hz => h (hφ (hz.trans (map_zero φ).symm))
  have hdata (γ : K) (hγ : γ ∈ Γ) :=
    fiber_data hreg.domain_card (hreg.mark γ hγ).1 (hreg.mark γ hγ).2.1
      (hreg.mark γ hγ).2.2.2
  have hrows (γ : K) (hγ : γ ∈ Γ) (b : Fin 2) :
      ∃ rows : Fin d → Fin 2 × Fin a, onGraph γ (V rows k) ≠ 0 ∧
        (Finset.univ.filter (fun i => (rows i).1 = b)).card = min a d := by
    obtain ⟨rows, hp, hb⟩ := select_rows _ (hdata γ hγ).1 b ((hdata γ hγ).2.1 b)
    refine ⟨rows, ?_, hb⟩
    change onGraph γ (cofactor (M.submatrix rows id) (Fin.last d)) ≠ 0
    rw [cofactor_map, cofactor_last]
    exact hp
  have hnonzero (rows : Fin d → Fin 2 × Fin a) (γ : K) (h : onGraph γ (V rows k) ≠ 0) :
      V rows k ≠ 0 := fun hz => h ((congrArg (onGraph γ) hz).trans (map_zero _))
  have hVker (rows : Fin d → Fin 2 × Fin a) (h : V rows k ≠ 0) : M.mulVec (V rows) = 0 :=
    cofactor_kernel φ hφ M rows hreg.generic_rank (hfne h)
  obtain ⟨γ₀, hγ₀⟩ := hΓ
  obtain ⟨r₀, hp₀, hc₀⟩ := hrows γ₀ hγ₀ 0
  obtain ⟨r₁, hp₁, hc₁⟩ := hrows γ₀ hγ₀ 1
  let g := Finset.univ.gcd (V r₀)
  have hg : g ≠ 0 := Finset.gcd_ne_zero_iff.mpr ⟨k, Finset.mem_univ _, hnonzero r₀ γ₀ hp₀⟩
  obtain ⟨Q, hQ, hprim⟩ := Finset.extract_gcd (V r₀) (Finset.univ_nonempty (α := Fin (d+1)))
  have hQ' (j : Fin (d+1)) : V r₀ j = g * Q j := hQ j (Finset.mem_univ _)
  have hQk : Q k ≠ 0 := by
    intro hz
    exact hnonzero r₀ γ₀ hp₀ (by rw [hQ', hz, mul_zero])
  have hQker : M.mulVec Q = 0 := by
    have hv := hVker r₀ (hnonzero r₀ γ₀ hp₀)
    funext i
    change (∑ j, M i j * Q j) = 0
    have hi : (∑ j, M i j * V r₀ j) = 0 := congrFun hv i
    have he : (∑ j, M i j * V r₀ j) = g * ∑ j, M i j * Q j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hQ']
      ac_rfl
    exact (mul_eq_zero.mp (he.symm.trans hi)).resolve_left hg
  have hmult (rows : Fin d → Fin 2 × Fin a) (hn : V rows k ≠ 0) :
      ∃ t : Bivar, ∀ j, V rows j = t * Q j := by
    apply polynomial_multiple Q (V rows) k hQk hprim
    have hnull := GenericRank.nullity_one_of_rank (M.map φ) (by
      rw [show (M.map φ).rank = d from hreg.generic_rank, Fintype.card_fin])
    have hnz : (fun j => φ (Q j)) ≠ 0 := by
      intro hz
      exact hfne hQk (congrFun hz k)
    obtain ⟨c, hc⟩ := GenericRank.kernel_line_of_finrank _ hnull _ hnz
      (map_kernel φ M Q hQker) _ (map_kernel φ M _ (hVker rows hn))
    intro j
    apply hφ
    simp only [map_mul]
    rw [congrFun hc j, congrFun hc k]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨t, ht⟩ := hmult r₁ (hnonzero r₁ γ₀ hp₁)
  have ht0 : t ≠ 0 := by
    intro hz
    exact hnonzero r₁ γ₀ hp₁ (by rw [ht, hz, zero_mul])
  have hcount (rows : Fin d → Fin 2 × Fin a) :
      (Finset.univ.filter (fun j => (rows j).1 = 0)).card +
        (Finset.univ.filter (fun j => (rows j).1 ≠ 0)).card = d := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun j => (rows j).1 = 0)
  have hb₀ : (Finset.univ.filter (fun j => (r₀ j).1 ≠ 0)).card = d-a := by
    have h := hcount r₀
    omega
  have hb₁ : (Finset.univ.filter (fun j => (r₁ j).1 = 0)).card = d-a := by
    have he (j : Fin d) : (r₁ j).1 ≠ 0 ↔ (r₁ j).1 = 1 := by omega
    have h := hcount r₁
    simp only [he, hc₁] at h
    omega
  have hbox (j : Fin (d+1)) : SeedBox (Q j) (d-a) (d-a) := by
    by_cases hz : Q j = 0
    · simp [hz, SeedBox, seedDegree]
    have h₀ := box_of_dvd (by rw [hQ']; exact mul_ne_zero hg hz)
      (show Q j ∣ V r₀ j by rw [hQ']; exact dvd_mul_left _ _)
      (cofactor_box u D a d r₀ j)
    have h₁ := box_of_dvd (by rw [ht]; exact mul_ne_zero ht0 hz)
      (show Q j ∣ V r₁ j by rw [ht]; exact dvd_mul_left _ _)
      (cofactor_box u D a d r₁ j)
    exact ⟨hb₁ ▸ h₁.1, hb₀ ▸ h₀.2⟩
  let L := Principal.assemble Q
  have hLd : L.natDegree ≤ d := Principal.assemble_natDegree_le Q
  refine ⟨L, ⟨hLd, ?_, ?_⟩, ?_⟩
  · simpa only [L, Principal.assemble_coeff] using hQker
  · intro γ hγ
    obtain ⟨rows, hp, _⟩ := hrows γ hγ 0
    obtain ⟨s, hs⟩ := hmult rows (hnonzero rows γ hp)
    have hpoint : onGraph γ (Q k) ≠ 0 := by
      intro hz
      exact hp (by rw [hs, map_mul, hz, mul_zero])
    let T := locator node (errorSet u D γ (P γ))
    let v (j : Fin (d+1)) := T.coeff j.val
    have hTd : T.natDegree = d := (locator_natDegree _ _).trans (hreg.mark γ hγ).2.1
    have hvk : v k = 1 := by
      change T.coeff d = 1
      rw [← hTd]
      exact locator_monic _ _
    have hv0 : v ≠ 0 := fun hz => one_ne_zero (hvk.symm.trans (congrFun hz k))
    have hnull := GenericRank.nullity_one_of_rank (M.map (onGraph γ)) (by
      rw [show (M.map (onGraph γ)).rank = d from (hreg.mark γ hγ).2.2.2, Fintype.card_fin])
    obtain ⟨c, hc⟩ := GenericRank.kernel_line_of_finrank _ hnull v hv0
      (hdata γ hγ).2.2 _ (map_kernel (onGraph γ) M Q hQker)
    refine ⟨c, fun hz => hpoint (by simpa [hz] using congrFun hc k), ?_⟩
    apply Polynomial.ext
    intro j
    rw [coeff_map, coeff_smul]
    by_cases hj : j < d+1
    · exact (congrArg (onGraph γ) (Principal.assemble_coeff Q ⟨j, hj⟩)).trans
        (congrFun hc ⟨j, hj⟩)
    · rw [coeff_eq_zero_of_natDegree_lt (hLd.trans_lt (by omega)), map_zero,
        coeff_eq_zero_of_natDegree_lt (hTd.trans_lt (by omega)), smul_zero]
  · intro j
    by_cases hj : j < d+1
    · exact (Principal.assemble_coeff Q ⟨j, hj⟩).symm ▸ hbox ⟨j, hj⟩
    · rw [coeff_eq_zero_of_natDegree_lt (hLd.trans_lt (by omega))]
      simp [SeedBox, seedDegree]

end

end K21_2_4_1_1
end Port_K1_2_4_1_1Proof

section Port_K1_2_2_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace K21_2_2_1

noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark K21

private theorem stacked_at_slope {ι : Type} [Fintype ι] [DecidableEq ι]
    (x a b : ι → K) (L t : ℕ) (γ : K) :
    (stacked p x a b L t).map (evalRingHom γ) =
      Strata.conjugateHankel (Strata.twoConjugations (frobenius K p))
        x (fun i => a i + γ * b i) L t := by
  rw [Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval]
  have h : (fun b : Fin 2 => iterateFrobenius K p b.val) =
      Strata.twoConjugations (frobenius K p) := by
    funext b
    fin_cases b
    · exact iterateFrobenius_zero K p
    · exact iterateFrobenius_one K p
  rw [h]

private theorem node_fixed (b : Fin 2) (i : I) :
    Strata.twoConjugations (frobenius K p) b (node i) = node i := by
  fin_cases b <;> simp [Strata.twoConjugations, frobenius_def, Native.native_domain_fixed]

private theorem rank_le_retained_rank_add_deleted {row ι : Type}
    [Fintype row] [Fintype ι] [DecidableEq ι]
    (M : Matrix row ι K) (C : Finset ι) :
    M.rank ≤ (M.submatrix id (Subtype.val : {i // i ∉ C} → ι)).rank + C.card := by
  have h := Strata.subspace_projection_bound (Strata.forgetCoordinates (F := K) C)
    (Submodule.span K (Set.range M.row))
  rw [Strata.rowspace_forget, Strata.forgetCoordinates_nullity,
    ← Matrix.rank_eq_finrank_span_row, ← Matrix.rank_eq_finrank_span_row] at h
  exact h

/-- Switch between the surviving-domain error set and the surviving subset
of the original error set before applying the coordinate projection bound. -/
private theorem rank_le_punctured_rank_add_deleted {row ι : Type}
    [Fintype row] [DecidableEq ι] (D E S : Finset ι)
    (hD : ∀ i, i ∈ D ↔ i ∉ S) (hS : S ⊆ E) (M : Matrix row E K) :
    M.rank ≤ (M.submatrix id (fun i : ↥(E.subtype (fun j => j ∈ D)) =>
      (⟨i.val.val, Finset.mem_subtype.mp i.property⟩ : E))).rank + S.card := by
  let C : Finset E := S.subtype (fun i : ι => i ∈ E)
  have hC (i : E) : i ∈ C ↔ i.val ∈ S := Finset.mem_subtype
  have hCcard : C.card = S.card := by
    change (S.subtype (fun i : ι => i ∈ E)).card = S.card
    rw [Finset.card_subtype, Finset.filter_true_of_mem (fun i hi => hS hi)]
  let e : ↥(E.subtype (fun j => j ∈ D)) ≃ {i : E // i ∉ C} := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      let j : E := ⟨i.val.val, Finset.mem_subtype.mp i.property⟩
      exact ⟨j, fun hj => (hD i.val.val).1 i.val.property ((hC j).1 hj)⟩
    · intro j
      have hj : j.val.val ∉ S := fun hs => j.property ((hC j.val).2 hs)
      let i : D := ⟨j.val.val, (hD j.val.val).2 hj⟩
      exact ⟨i, Finset.mem_subtype.mpr j.val.property⟩
    · intro i
      rfl
    · intro j
      rfl
  let M₀ := M.submatrix id (Subtype.val : {i : E // i ∉ C} → E)
  change M.rank ≤ (M₀.submatrix (Equiv.refl row) e).rank + S.card
  rw [Matrix.rank_submatrix, ← hCcard]
  exact rank_le_retained_rank_add_deleted M C

theorem proof : K21_2_2.c1 := by
  classical
  intro u T R A γ M hn
  let S := fixedNodes R
  let D := Finset.univ \ S
  let w (i : I) := u 0 i + γ * u 1 i
  let G := Finset.univ.filter (fun i : I => w i = M.decoder.eval (node i))
  let E := Finset.univ \ G
  let E' : Finset D := E.subtype (fun i : I => i ∈ D)
  have hE (i : I) : i ∈ E ↔ w i ≠ M.decoder.eval (node i) := by
    simp [E, G]
  have hS : S ⊆ E := fun i hi => (hE i).2 (A.deleted_error γ hn M i hi).symm
  have hG : 180130 ≤ G.card := M.agreement.trans (Finset.card_le_card (by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (M.hits i hi).symm⟩))
  have hEcard : E.card ≤ 82014 := by
    have hg := K21_2_2.domain_card G
    change E.card = 262144 - G.card at hg
    omega
  have hDcard : Fintype.card D = 262144 - S.card := by
    rw [Fintype.card_coe]
    exact K21_2_2.domain_card S
  have hDsize : 131072 + 49058 + (82014 - S.card) ≤ Fintype.card D := by
    have hs := Finset.card_le_card hS
    omega
  have hE'card : E'.card ≤ 82014 - S.card := by
    have hfilter : E.filter (fun i : I => i ∈ D) = E \ S := by
      ext i
      simp [D]
    change (E.subtype (fun i : I => i ∈ D)).card ≤ _
    rw [Finset.card_subtype, hfilter, Finset.card_sdiff_of_subset hS]
    exact Nat.sub_le_sub_right hEcard _
  have hagree (i : I) (hi : i ∉ E) : w i = M.decoder.eval (node i) :=
    not_not.mp (fun hne => hi ((hE i).2 hne))
  have hagree' (i : D) (hi : i ∉ E') : w i.val = M.decoder.eval (node i.val) :=
    hagree i.val (fun he => hi (Finset.mem_subtype.mpr he))
  let σ := Strata.twoConjugations (frobenius K p)
  let x (i : D) := node i.val
  let B := Strata.conjugateErrors σ (fun i : E => node i.val)
    (fun i : E => w i.val - M.decoder.eval (node i.val)) 49058
  let B' := Strata.conjugateErrors σ (fun i : E' => x i.val)
    (fun i : E' => w i.val.val - M.decoder.eval (x i.val)) 49058
  -- Both Vandermonde factors have full row rank; the weights on each domain
  -- are removed by the existing rank factorization.
  have hfull : ((twoBlock u).map (evalRingHom γ)).rank = B.rank := by
    rw [twoBlock, stacked_at_slope]
    exact Strata.conjugateHankel_error_rank σ node w IRSProfile.domain.injective
      node_fixed M.decoder 131072 49058 82014 M.degree
      (by rw [IRSProfile.card_index]) E (by omega) hagree
  have hshort : ((K21_2_2.shortenedStack R).map (evalRingHom γ)).rank = B'.rank := by
    change ((stacked p x (fun i : D => u 0 i.val) (fun i : D => u 1 i.val)
      49058 (82014 - S.card)).map (evalRingHom γ)).rank = B'.rank
    rw [stacked_at_slope]
    exact Strata.conjugateHankel_error_rank σ x (fun i : D => w i.val)
      (IRSProfile.domain.injective.comp Subtype.val_injective)
      (fun b i => node_fixed b i.val) M.decoder 131072 49058 (82014 - S.card)
      M.degree hDsize E' (by omega) hagree'
  have hD (i : I) : i ∈ D ↔ i ∉ S := by simp [D]
  have hrank : B.rank ≤ B'.rank + S.card :=
    rank_le_punctured_rank_add_deleted D E S hD hS B
  have hnormal : ((twoBlock u).map (evalRingHom γ)).rank = 49058 + T.height := by
    change ((twoBlock u).map (evalRingHom γ)).rank = stackRank u at hn
    rw [hn, actual_stackRank]
    have := T.degreeSum
    have := T.nullitySum
    have := T.top
    unfold TwoActive.height
    omega
  have hspecial := K21_2_3.rank_ge_specialization (K21_2_2.shortenedStack R)
    (evalRingHom γ) (algebraMap K[X] Frac) (IsFractionRing.injective K[X] Frac)
  change ((K21_2_2.shortenedStack R).map (evalRingHom γ)).rank ≤
    GenericLayer.genericRank (K21_2_2.shortenedStack R) at hspecial
  rw [hshort] at hspecial
  rw [← hfull, hnormal] at hrank
  have hheight := A.height_eq
  change A.height + S.card = T.height at hheight
  omega

end

end K21_2_2_1
end Port_K1_2_2_1Proof

section Port_K1_2_4_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K21_2_4_2

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K21 K21_2 K21_2_4

theorem proof : K21_2_4.c2 := by
  classical
  intro u D Γ P a b _ _ hreg L hL Q hQ _ _ hΓ hQΓ
  let F := curveFixed D L Q
  let R := a + b
  let d := R - F.card
  change 0 < d → ∀ i ∈ D \ F, Nonempty (OppositeCuts u D Γ P Q a d i)
  intro _ i hi
  have hiF : i ∉ F := (Finset.mem_sdiff.mp hi).2
  have hF (γ : K) (hγ : γ ∈ Γ) : F ⊆ errorSet u D γ (P γ) := by
    intro j hj
    obtain ⟨V, hV⟩ := (mem_curveFixed.mp hj).2
    apply (root_iff_error hL hγ j).mp
    rw [hV, map_mul, hQΓ γ hγ, zero_mul]
  obtain ⟨γ₀, hγ₀⟩ := hΓ
  obtain ⟨hP, hE, _, hR⟩ := hreg.mark γ₀ hγ₀
  have hcard := Finset.card_le_card (hF γ₀ hγ₀)
  rw [hE] at hcard
  have hsize : R = d + F.card := by dsimp [d, R]; omega
  let N := contracted u D F a R d
  have ha := anchor_ranks hsize hreg.domain_card hP hE (hF γ₀ hγ₀) hR
  letI : Fact (Prime Q) := ⟨hQ.prime⟩
  let φ := curveMap Q
  have hnot : φ (nodeEquation L i) ≠ 0 := by
    intro hz
    exact hiF (mem_curveFixed.mpr ⟨(Finset.mem_sdiff.mp hi).1,
      (curveMap_zero_iff Q _).mp hz⟩)
  have hLφ : L.map φ ≠ 0 := fun hz => hnot (by rw [eval_nodeEquation, hz, eval_zero])
  obtain ⟨T, _, hTd, hLT, hNT⟩ := contracted_kernel φ hsize hL.degree hL.kernel
    (fun j hj => (curveMap_zero_iff Q _).mpr (mem_curveFixed.mp hj).2) hLφ
  have hTi : T.eval (φ (planeConstant (node i))) ≠ 0 := by
    intro hz
    exact hnot (by rw [eval_nodeEquation, hLT, eval_mul, hz, mul_zero])
  have selected_cut (rows : Fin d → Fin 2 × Fin a) (γ : K) (hγ : γ ∈ Γ)
      (hγi : i ∈ errorSet u D γ (P γ)) :
      onGraph γ (cutMatrix N rows i).det = 0 := by
    obtain ⟨c, hc, hLc⟩ := hL.fiber γ hγ
    have hLγ : L.map (onGraph γ) ≠ 0 := by
      rw [hLc]
      exact smul_ne_zero hc (locator_monic node _).ne_zero
    obtain ⟨U, hU, hUd, hLU, hNU⟩ := contracted_kernel (onGraph γ) hsize hL.degree hL.kernel
      (fun j hj => (root_iff_error hL hγ j).mpr (hF γ hγ hj)) hLγ
    have hz := (root_iff_error hL hγ i).mpr hγi
    simp only [eval_nodeEquation, hLU, eval_mul, Function.comp_def, graph_constant] at hz
    have hUi := (mul_eq_zero.mp hz).resolve_left (fun he =>
      hiF ((Principal.locator_eval_zero_iff node IRSProfile.domain.injective F i).mp he))
    rw [(onGraph γ).map_det]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨_, coeff_vec_ne_zero U d hUd hU, ?_⟩
    change ((cutMatrix N rows i).map (onGraph γ)).mulVec (fun j => U.coeff j.val) = 0
    rw [cut_action (onGraph γ) (N := N) rows i hUd hNU, graph_constant, hUi]
    funext j
    exact Fin.lastCases (by simp) (fun l => by simp) j
  have makeCut (o : Fin 2) :
      ∃ V : Bivar,
        SeedBox V (if o = 0 then min a d else d - a) (if o = 0 then d - a else min a d) ∧
        (¬ Q ∣ V) ∧ ∀ γ ∈ Γ, i ∈ errorSet u D γ (P γ) → onGraph γ V = 0 := by
    obtain ⟨rows, hdet, hcount⟩ := select_rows _ ha.1 o (ha.2 o)
    let B := N.submatrix rows Fin.castSucc
    have hB : onGraph γ₀ B.det ≠ 0 := by
      rw [(onGraph γ₀).map_det]
      exact hdet
    have hBφ : ((N.map φ).submatrix rows Fin.castSucc).det ≠ 0 := by
      change (φ.mapMatrix B).det ≠ 0
      rw [← φ.map_det B]
      intro hz
      obtain ⟨W, hW⟩ := (curveMap_zero_iff Q B.det).mp hz
      exact hB (by rw [hW, map_mul, hQΓ γ₀ hγ₀, zero_mul])
    refine ⟨(cutMatrix N rows i).det, ?_, ?_, selected_cut rows⟩
    · let A₀ := Finset.univ.filter (fun j => (rows j).1 = 0)
      let A₁ := Finset.univ.filter (fun j => (rows j).1 ≠ 0)
      have hb : SeedBox (cutMatrix N rows i).det A₀.card A₁.card :=
        cut_box u D F a R d rows i
      have htotal : A₀.card + A₁.card = d := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          (Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin d))) (p := fun j => (rows j).1 = 0))
      have hsum : min a d + (d - a) = d := by omega
      by_cases ho : o = 0
      · have hcount₀ : A₀.card = min a d := by simpa only [ho] using hcount
        rw [hcount₀] at htotal
        have hcount₁ := Nat.add_left_cancel (htotal.trans hsum.symm)
        simpa [ho, hcount₀, hcount₁] using hb
      · have hval : o.val ≠ 0 := fun h => ho (Fin.ext h)
        have h₁ : o = 1 := Fin.ext (by have := o.isLt; omega)
        have heq (k : Fin 2) : (k = 1) ↔ (k ≠ 0) := by
          fin_cases k <;> simp
        have hfilter : A₁ = Finset.univ.filter (fun j => (rows j).1 = o) := by
          apply Finset.ext
          intro j
          simp only [A₁, Finset.mem_filter, Finset.mem_univ, true_and, h₁, heq]
        have hcount₁ : A₁.card = min a d := by rw [hfilter, hcount]
        rw [hcount₁] at htotal
        have hcount₀ := Nat.add_right_cancel (htotal.trans ((Nat.add_comm _ _).trans hsum).symm)
        simpa [ho, hcount₀, hcount₁] using hb
    · exact fun hz => (cut_ne_zero φ (N := N) rows i hBφ hTd hNT hTi)
        ((curveMap_zero_iff Q _).mpr hz)
  obtain ⟨V, hVb, hVp, hVz⟩ := makeCut 0
  obtain ⟨W, hWb, hWp, hWz⟩ := makeCut 1
  exact ⟨⟨V, W, by simpa using hVb, by simpa using hWb, hVp, hWp,
    fun γ hγ hγi => ⟨hVz γ hγ hγi, hWz γ hγ hγi⟩⟩⟩

end

end K21_2_4_2
end Port_K1_2_4_2Proof

section Port_K1_2_3Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000

namespace K21_2_3

open Finset Matrix FrobeniusLocator K21 K21_2

theorem proof : K21_2.c3 := by
  intro u D Γ r g hr hr16 hg F Q hreg J hJ hnon
  obtain ⟨hH, hR, hRp, hsize⟩ := child_parameters r g hr hr16 hg
  obtain ⟨hsub, hJc⟩ := Finset.mem_powersetCard.mp hJ
  have hD : (D \ J).card = 131072 + childRows r + childErrors r g := by
    rw [Finset.card_sdiff_of_subset hsub, F.domain_card, hJc, hsize]
  have hmark := fun γ hγ => child_mark F hr hr16 hg (γ := γ) (J := J) hγ
  have hrank (γ : K) (hγ : γ ∈ childSlopes F J) :=
    evaluated_rank Q (Finset.sdiff_subset : D \ J ⊆ D) hH hR hD γ
      (hreg γ (hmark γ hγ).1) (F.decoder γ) (hmark γ hγ).2.1 (hmark γ hγ).2.2.1
  refine ⟨hD, le_antisymm ?_ ?_, ?_⟩
  · exact plane_rank_le u (D \ J) (childRows r) (childErrors r g) hRp
      (formal_graph_rank_le Q Finset.sdiff_subset hH hD)
  · obtain ⟨γ, hγ⟩ := hnon
    exact (hrank γ hγ).ge.trans
      (rank_ge_specialization _ (onGraph γ) _ (IsFractionRing.injective Bivar (FractionRing Bivar)))
  · intro γ hγ
    obtain ⟨_, hdegree, hE, hbad⟩ := hmark γ hγ
    exact ⟨hdegree, hE, hbad, hrank γ hγ⟩

end K21_2_3
end Port_K1_2_3Proof

section Port_K1_2_1Complement
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace K21_2_1
noncomputable section

open Polynomial Matrix Finset FrobeniusLocator K1_6

variable {E : Type*} [Field E]

private def unitColumns {R row col : Type*} [Zero R] [One R] [DecidableEq row]
    (I : col → row) : Matrix row col R :=
  fun i j => (Pi.single (I j) 1 : row → R) i

private theorem transpose_mul_unitColumns {row col pick : Type*} [Fintype row] [DecidableEq row]
    (B : Matrix row col E) (I : pick → row) :
    B.transpose*unitColumns I=(B.submatrix I id).transpose := by
  ext i j
  change B.transpose.mulVec (Pi.single (I j) 1) i= _
  rw [Matrix.mulVec_single_one]
  rfl

private theorem augmentation_det_ne_zero {r s : ℕ}
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) E) (B : Matrix (Fin r ⊕ Fin s) (Fin s) E)
    (hBC : B.transpose*C=0)
    (hC : ∀ a, C.mulVec a=0 → a=0)
    (I : Fin s → (Fin r ⊕ Fin s)) (hI : (B.submatrix I id).det ≠ 0) :
    (Matrix.fromCols C (unitColumns I)).det ≠ 0 := by
  classical
  let A := Matrix.fromCols C (unitColumns I)
  have hker : ∀ w, A.mulVec w=0 → w=0 := by
    intro w hw
    have hh := congrArg B.transpose.mulVec hw
    rw [Matrix.mulVec_zero] at hh
    change B.transpose.mulVec ((Matrix.fromCols C (unitColumns I)).mulVec w)=0 at hh
    rw [Matrix.fromCols_mulVec,Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
      hBC,Matrix.zero_mulVec,zero_add,transpose_mul_unitColumns] at hh
    have hb : w ∘ Sum.inr=0 := Matrix.eq_zero_of_mulVec_eq_zero
      (by simpa only [Matrix.det_transpose] using hI) hh
    change (Matrix.fromCols C (unitColumns I)).mulVec w=0 at hw
    rw [Matrix.fromCols_mulVec,hb,Matrix.mulVec_zero,add_zero] at hw
    have ha := hC (w ∘ Sum.inl) hw
    funext i
    cases i with
    | inl i => exact congrFun ha i
    | inr i => exact congrFun hb i
  have hinj : Function.Injective A.mulVec := by
    intro u v huv
    have hh := hker (u-v) (by rw [Matrix.mulVec_sub,huv,sub_self])
    exact sub_eq_zero.mp hh
  have hu : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact ((Matrix.isUnit_iff_isUnit_det A).mp hu).ne_zero

/-- Rectangular kernel minors and unit-column augmented determinants are
proportional, with no complementary-index signs. -/
private theorem augmented_minor_cross {r s : ℕ}
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) E) (B : Matrix (Fin r ⊕ Fin s) (Fin s) E)
    (hBC : B.transpose*C=0) (hC : ∀ a, C.mulVec a=0 → a=0)
    (I0 I : Fin s → (Fin r ⊕ Fin s)) (hI0 : (B.submatrix I0 id).det ≠ 0) :
    (Matrix.fromCols C (unitColumns I)).det*(B.submatrix I0 id).det=
      (Matrix.fromCols C (unitColumns I0)).det*(B.submatrix I id).det := by
  classical
  let A0 := Matrix.fromCols C (unitColumns I0)
  let AI := Matrix.fromCols C (unitColumns I)
  have hA0 : IsUnit A0.det := isUnit_iff_ne_zero.mpr (augmentation_det_ne_zero C B hBC hC I0 hI0)
  let T := A0⁻¹*AI
  let J : Matrix (Fin r ⊕ Fin s) (Fin r) E := Matrix.fromRows 1 0
  have hA0J : A0*J=C := by
    simp only [A0,J,Matrix.fromCols_mul_fromRows,Matrix.mul_one,Matrix.mul_zero,add_zero]
  have hfirst : T.submatrix id Sum.inl=J := by
    have heq : T.submatrix id Sum.inl=A0⁻¹*C := by
      ext i j
      rfl
    rw [heq,← hA0J,Matrix.nonsing_inv_mul_cancel_left A0 J hA0]
  let D := T.submatrix Sum.inr Sum.inr
  let U := T.submatrix Sum.inl Sum.inr
  have hT : T=Matrix.fromBlocks 1 U 0 D := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrFun (congrFun hfirst (Sum.inl i)) j
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j => exact congrFun (congrFun hfirst (Sum.inr i)) j
      | inr j => rfl
  have hAT : A0*T=AI := Matrix.mul_nonsing_inv_cancel_left A0 AI hA0
  have hB0 : B.transpose*A0=Matrix.fromCols 0 (B.submatrix I0 id).transpose := by
    dsimp only [A0]
    rw [Matrix.mul_fromCols,hBC,transpose_mul_unitColumns]
  have hBI : B.transpose*AI=Matrix.fromCols 0 (B.submatrix I id).transpose := by
    dsimp only [AI]
    rw [Matrix.mul_fromCols,hBC,transpose_mul_unitColumns]
  have hbottom : (B.submatrix I0 id).transpose*D=(B.submatrix I id).transpose := by
    have hh : (B.transpose*A0)*T=B.transpose*AI := by rw [Matrix.mul_assoc,hAT]
    rw [hB0,hBI,hT,Matrix.fromCols_mul_fromBlocks,Matrix.zero_mul,Matrix.mul_zero,
      zero_add,Matrix.zero_mul,zero_add] at hh
    have hz := congrArg (fun M : Matrix (Fin s) (Fin r ⊕ Fin s) E => M.submatrix id Sum.inr) hh
    exact hz
  have hdetD : (B.submatrix I0 id).det*D.det=(B.submatrix I id).det := by
    have hh := congrArg Matrix.det hbottom
    simpa only [Matrix.det_mul,Matrix.det_transpose] using hh
  have hdetT : T.det=D.det := by
    rw [hT,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,one_mul]
  have hdetAI : AI.det=A0.det*D.det := by
    have hh := congrArg Matrix.det hAT
    rw [Matrix.det_mul,hdetT] at hh
    exact hh.symm
  change AI.det*(B.submatrix I0 id).det=A0.det*(B.submatrix I id).det
  rw [hdetAI,← hdetD]
  ring

variable {F : Type} [Field F]

private theorem unitColumns_map {row col : Type*} [DecidableEq row]
    (φ : F[X] →+* E) (I : col → row) :
    (unitColumns I : Matrix row col F[X]).map φ=unitColumns I := by
  ext i j
  by_cases h : I j=i <;> simp [unitColumns, h]

private theorem augmented_map_det {r s : ℕ} (φ : F[X] →+* E)
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) F[X]) (I : Fin s → (Fin r ⊕ Fin s)) :
    φ (Matrix.fromCols C (unitColumns I)).det=
      (Matrix.fromCols (C.map φ) (unitColumns I)).det := by
  have hh := φ.map_det (Matrix.fromCols C (unitColumns I))
  rw [RingHom.mapMatrix_apply] at hh
  rw [hh]
  congr 1
  ext i j
  cases j with
  | inl j => rfl
  | inr j => exact congrFun (congrFun (unitColumns_map φ I) i) j

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Each constant column saves one from a positive row budget. This
gives the exact pL+H complementary-minor budget after augmentation. -/
private theorem det_degree_sub_constant_columns (M : Matrix ι ι F[X]) (d : ι → ℕ)
    (S : Finset ι) (hpositive : ∀ i, 1 ≤ d i)
    (hdegree : ∀ i j, (M i j).natDegree ≤ d i)
    (hconstant : ∀ j ∈ S, ∀ i, (M i j).natDegree=0) :
    M.det.natDegree ≤ (∑ i, d i)-S.card := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro sigma hsigma
  have hsign : (Equiv.Perm.sign sigma • ∏ i, M (sigma i) i).natDegree=
      (∏ i, M (sigma i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign sigma) with h | h
    · rw [h,one_smul]
    · rw [h,Units.neg_smul,one_smul,Polynomial.natDegree_neg]
  rw [hsign]
  have hpoint : ∀ j, (M (sigma j) j).natDegree+(if j ∈ S then 1 else 0) ≤ d (sigma j) := by
    intro j
    by_cases hj : j ∈ S
    · rw [ite_eq_left hj,hconstant j hj (sigma j),Nat.zero_add]
      exact hpositive _
    · simpa only [ite_eq_right hj,Nat.add_zero] using hdegree (sigma j) j
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hpoint j)
  have hbool : (∑ j : ι, if j ∈ S then 1 else 0)=S.card := by simp
  rw [Finset.sum_add_distrib,hbool,Equiv.sum_comp sigma d] at hsum
  have hprod := Polynomial.natDegree_prod_le (Finset.univ : Finset ι) (fun i => M (sigma i) i)
  omega

private theorem augmented_det_row_budget {r s : ℕ}
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) F[X])
    (d : (Fin r ⊕ Fin s) → ℕ) (hpositive : ∀ i, 1 ≤ d i)
    (hdegree : ∀ i j, (C i j).natDegree ≤ d i) (I : Fin s → (Fin r ⊕ Fin s)) :
    (Matrix.fromCols C (unitColumns I)).det.natDegree ≤ (∑ i, d i)-s := by
  classical
  let S : Finset (Fin r ⊕ Fin s) := Finset.univ.image Sum.inr
  have hS : S.card=s := by rw [Finset.card_image_of_injective _ Sum.inr_injective]; simp
  have hbound : (Matrix.fromCols C (unitColumns I)).det.natDegree ≤ (∑ i, d i)-S.card := by
    apply det_degree_sub_constant_columns _ d S hpositive
    · intro i j
      cases j with
      | inl j => exact hdegree i j
      | inr j =>
        simp only [Matrix.fromCols_apply_inr,unitColumns,Pi.single_apply]
        split_ifs <;> simp
    · intro j hj i
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      simp only [Matrix.fromCols_apply_inr,unitColumns,Pi.single_apply]
      split_ifs <;> simp
  simpa only [hS] using hbound

/-- Bézout for the kernel minors clears the common scalar from the complementary tuple. -/
private theorem primitive_minor_le_augmented {r s : ℕ}
    (φ : F[X] →+* E) (hφ : Function.Injective φ)
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) F[X]) (B : Matrix (Fin r ⊕ Fin s) (Fin s) F[X])
    (hBC : (B.map φ).transpose * C.map φ = 0)
    (hC : ∀ v, (C.map φ).mulVec v = 0 → v = 0)
    (hprim : PrimitiveVector.IsPrimitive (maximalMinors B))
    (I₀ : Fin s → (Fin r ⊕ Fin s)) (hI₀ : maximalMinors B I₀ ≠ 0) :
    (maximalMinors B I₀).natDegree ≤ (Matrix.fromCols C (unitColumns I₀)).det.natDegree := by
  classical
  let P := maximalMinors B
  let A := fun I : Fin s → (Fin r ⊕ Fin s) => (Matrix.fromCols C (unitColumns I)).det
  have hPmap (I : Fin s → (Fin r ⊕ Fin s)) :
      φ (P I) = ((B.map φ).submatrix I id).det := φ.map_det (B.submatrix I id)
  have hI₀map : ((B.map φ).submatrix I₀ id).det ≠ 0 := by
    rw [← hPmap]
    exact fun hz => hI₀ (hφ (hz.trans (map_zero φ).symm))
  have hcross (I) : A I * P I₀ = A I₀ * P I := by
    apply hφ
    simp only [map_mul, A, augmented_map_det, hPmap]
    exact augmented_minor_cross (C.map φ) (B.map φ) hBC hC I₀ I hI₀map
  have hA₀ : A I₀ ≠ 0 := by
    intro hz
    apply augmentation_det_ne_zero (C.map φ) (B.map φ) hBC hC I₀ hI₀map
    rw [← augmented_map_det φ C I₀]
    exact (congrArg φ hz).trans (map_zero φ)
  obtain ⟨a, ha⟩ := (PrimitiveVector.primitive_iff_bezout P).mp hprim
  have hfactor : A I₀ = P I₀ * ∑ I, a I * A I := by
    rw [Finset.mul_sum, ← mul_one (A I₀), ← ha, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    calc
      A I₀ * (a I * P I) = a I * (A I₀ * P I) := by ring
      _ = a I * (A I * P I₀) := by rw [hcross]
      _ = P I₀ * (a I * A I) := by ring
  exact Polynomial.natDegree_le_of_dvd ⟨_, hfactor⟩ hA₀

/-- A selected column basis of the stacked matrix gives complementary minors
for the primitive left kernel. The unit columns each save one row degree. -/
theorem complementary_minor_bound {F : Type} [Field F] (L w s p : ℕ)
    (M : Matrix (Fin 2 × Fin L) (Fin w) F[X])
    (W : Matrix (Fin 2 × Fin L) (Fin s) F[X])
    (hp : 1 ≤ p) (hrank : GenericLayer.genericRank M + s = 2 * L)
    (hWM : W.transpose * M = 0)
    (hM : ∀ i j, (M i j).natDegree ≤ if i.1 = 0 then 1 else p)
    (hprim : PrimitiveVector.IsPrimitive (maximalMinors W))
    (I : Fin s → Fin 2 × Fin L) :
    (maximalMinors W I).natDegree ≤ L * (p + 1) - s := by
  classical
  by_cases hI : maximalMinors W I = 0
  · simp [hI]
  let φ := algebraMap F[X] (GenericLayer.GenericField F)
  have hφ := IsFractionRing.injective F[X] (GenericLayer.GenericField F)
  let r := GenericLayer.genericRank M
  obtain ⟨D⟩ := NormalFiber.exists_rowBasis φ M r rfl
  let e : (Fin r ⊕ Fin s) ≃ Fin 2 × Fin L :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      using hrank)
  let C := M.submatrix e D.cols
  let B := W.submatrix e id
  have hC (v) (hv : (C.map φ).mulVec v = 0) : v = 0 := by
    have hdet : ((M.map φ).submatrix D.rows D.cols).det ≠ 0 := by
      rw [← show φ (M.submatrix D.rows D.cols).det =
        ((M.map φ).submatrix D.rows D.cols).det from φ.map_det _]
      exact fun hz => D.minor_ne (hφ (hz.trans (map_zero φ).symm))
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext i
    have hv' := congrFun hv (e.symm (D.rows i))
    simpa only [C, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.submatrix_apply,
      Equiv.apply_symm_apply, Pi.zero_apply] using hv'
  have hBC : (B.map φ).transpose * C.map φ = 0 := by
    ext i j
    have hh := congrArg φ (congrFun (congrFun hWM i) (D.cols j))
    change (∑ k : Fin r ⊕ Fin s, φ (W (e k) i) * φ (M (e k) (D.cols j))) = 0
    rw [Equiv.sum_comp e (fun k => φ (W k i) * φ (M k (D.cols j)))]
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, map_sum, map_mul,
      map_zero] using hh
  have hB : PrimitiveVector.IsPrimitive (maximalMinors B) := by
    have hs : Function.Surjective
        (fun J : Fin s → (Fin r ⊕ Fin s) => e ∘ J) := by
      intro J
      exact ⟨e.symm ∘ J, funext (fun j => e.apply_symm_apply (J j))⟩
    change Ideal.span (Set.range (maximalMinors W ∘ (fun J : Fin s → (Fin r ⊕ Fin s) => e ∘ J))) = ⊤
    rwa [hs.range_comp]
  let J := e.symm ∘ I
  have hBI : maximalMinors B J = maximalMinors W I := by
    unfold maximalMinors
    apply congrArg Matrix.det
    ext i j
    simp only [B, J, Matrix.submatrix_apply, Function.comp_apply, Equiv.apply_symm_apply, id_eq]
  let d : (Fin r ⊕ Fin s) → ℕ := fun i => if (e i).1 = 0 then 1 else p
  have hd (i) : 1 ≤ d i := by dsimp [d]; split_ifs <;> omega
  have htotal : ∑ i, d i = L * (p + 1) := by
    dsimp only [d]
    rw [Equiv.sum_comp e (fun i : Fin 2 × Fin L => if i.1 = 0 then 1 else p)]
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, Nat.mul_add, Nat.add_comm]
  have hbound := (primitive_minor_le_augmented φ hφ C B hBC hC hB J (by rwa [hBI])).trans
    (augmented_det_row_budget C d hd (fun i j => hM (e i) (D.cols j)) J)
  simpa only [hBI, htotal] using hbound

end
end K21_2_1
end Port_K1_2_1Complement

section Port_K1_2_1Shifts
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace K21_2_1

open Polynomial Matrix FrobeniusLocator K1_6

/-- After a coefficient projection, a nonzero block gives a triangular shift minor.
The same construction works in a residue field and at the leading seed coefficient. -/
private theorem exists_projected_shift_minor {A E : Type} [CommRing A] [Field E]
    (P : Fin 2 → A[X]) (h s : ℕ) (f : A → E) (hf : f 0 = 0)
    (hP : ∀ b, (P b).natDegree ≤ h)
    (hnonzero : ∃ i : Fin 2 × Fin (h + 1), f ((P i.1).coeff i.2.val) ≠ 0) :
    ∃ rows : Fin s → Fin 2 × Fin (h + s),
      (((shifts P (h + s) s).submatrix rows id).map f).det ≠ 0 := by
  obtain ⟨⟨b, i⟩, hi⟩ := hnonzero
  let Q : E[X] := Principal.assemble (fun j : Fin (h + 1) => f ((P b).coeff j.val))
  have hQcoeff (j : ℕ) : Q.coeff j = f ((P b).coeff j) := by
    by_cases hj : j < h + 1
    · exact Principal.assemble_coeff _ ⟨j, hj⟩
    · rw [coeff_eq_zero_of_natDegree_lt (p := Q)
        (Principal.assemble_natDegree_le _ |>.trans_lt (by omega)),
        coeff_eq_zero_of_natDegree_lt (p := P b) ((hP b).trans_lt (by omega)), hf]
  have hQ : Q ≠ 0 := by
    intro hz
    exact hi ((hQcoeff i.val).symm.trans (by rw [hz, coeff_zero]))
  let d := Q.natDegree
  have hd : d ≤ h := Principal.assemble_natDegree_le _
  let rows (j : Fin s) : Fin 2 × Fin (h + s) := (b, ⟨d + j.val, by have := j.isLt; omega⟩)
  let B := ((shifts P (h + s) s).submatrix rows id).map f
  have htri : B.IsUpperTriangular := by
    intro j k hjk
    change k.val < j.val at hjk
    change f (((P b) * (Polynomial.X : A[X]) ^ k.val).coeff (d + j.val)) = 0
    rw [coeff_mul_X_pow', ite_eq_left (by omega), ← hQcoeff]
    exact coeff_eq_zero_of_natDegree_lt (p := Q) (show d < d + j.val - k.val by omega)
  refine ⟨rows, ?_⟩
  change B.det ≠ 0
  rw [Matrix.det_of_isUpperTriangular htri]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  change f (((P b) * (Polynomial.X : A[X]) ^ j.val).coeff (d + j.val)) ≠ 0
  rw [coeff_mul_X_pow, ← hQcoeff, coeff_natDegree]
  exact leadingCoeff_ne_zero.mpr hQ

theorem shift_minors_primitive {F : Type} [Field F] (P : Fin 2 → F[X][X])
    (h s : ℕ) (hP : ∀ b, (P b).natDegree ≤ h)
    (hprim : PrimitiveVector.IsPrimitive (pairCoordinates P h)) :
    PrimitiveVector.IsPrimitive (maximalMinors (shifts P (h + s) s)) := by
  classical
  by_contra hn
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal
    (Ideal.span (Set.range (maximalMinors (shifts P (h + s) s)))) hn
  let : J.IsMaximal := hJ
  let : Field (F[X] ⧸ J) := Ideal.Quotient.field J
  let φ := Ideal.Quotient.mk J
  have hnz : ∃ i, φ (pairCoordinates P h i) ≠ 0 := by
    by_contra hnz
    push Not at hnz
    obtain ⟨a, ha⟩ := (PrimitiveVector.primitive_iff_bezout _).mp hprim
    have hh := congrArg φ ha
    simp only [map_sum, map_mul, hnz, mul_zero, Finset.sum_const_zero, map_one] at hh
    exact zero_ne_one hh
  obtain ⟨rows, hrows⟩ := exists_projected_shift_minor P h s φ (map_zero φ) hP hnz
  apply hrows
  rw [← RingHom.mapMatrix_apply, ← φ.map_det]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ (Ideal.subset_span (Set.mem_range_self rows)))

/-- The coefficient of degree sH is the determinant of the matrix of H-th coefficients. -/
private theorem coeff_det_uniform {F : Type} [Field F] {s : ℕ}
    (M : Matrix (Fin s) (Fin s) F[X]) (H : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ H) :
    M.det.coeff (s * H) = (M.map (fun Q => Q.coeff H)).det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Polynomial.coeff_smul]
  congr 1
  simpa only [Finset.card_univ, Fintype.card_fin, Matrix.map_apply] using
    Polynomial.coeff_prod_of_natDegree_le (Finset.univ : Finset (Fin s))
      (fun i => M (σ i) i) H (fun i _ => hM (σ i) i)

theorem shift_minors_height {F : Type} [Field F] (P : Fin 2 → F[X][X])
    (h s : ℕ) (hP : ∀ b, (P b).natDegree ≤ h)
    (hprim : PrimitiveVector.IsPrimitive (pairCoordinates P h)) :
    ∃ H : ℕ, (∀ b j, ((P b).coeff j).natDegree ≤ H) ∧
      ∃ rows : Fin s → Fin 2 × Fin (h + s),
        (maximalMinors (shifts P (h + s) s) rows).natDegree = s * H := by
  classical
  let Q := pairCoordinates P h
  let S := Finset.univ.filter fun i => Q i ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := PrimitiveVector.exists_eval_ne_zero Q hprim 0
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hz => hi (by simp [hz])⟩⟩
  let H := S.sup fun i => (Q i).natDegree
  have hH (b : Fin 2) (j : ℕ) : ((P b).coeff j).natDegree ≤ H := by
    by_cases hn : (P b).coeff j = 0
    · simp [hn]
    have hj : j < h + 1 := by
      have := le_natDegree_of_ne_zero hn
      have := hP b
      omega
    exact Finset.le_sup (s := S) (f := fun i => (Q i).natDegree)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, show Q (b, ⟨j, hj⟩) ≠ 0 from hn⟩)
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup S hS (fun i => (Q i).natDegree)
  have htop : (Q i).coeff H ≠ 0 := by
    change H = (Q i).natDegree at hmax
    rw [hmax, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (Finset.mem_filter.mp hi).2
  obtain ⟨rows, hrows⟩ :=
    exists_projected_shift_minor P h s (fun Q => Q.coeff H) (coeff_zero _) hP ⟨i, htop⟩
  let M := (shifts P (h + s) s).submatrix rows id
  have hM (i j) : (M i j).natDegree ≤ H := by
    change (((P (rows i).1) * (Polynomial.X : F[X][X]) ^ j.val).coeff (rows i).2.val).natDegree ≤ H
    rw [coeff_mul_X_pow']
    split_ifs
    · exact hH _ _
    · simp
  have hcoeff : M.det.coeff (s * H) ≠ 0 := by
    rw [coeff_det_uniform M H hM]
    exact hrows
  have hdeg := natDegree_det_le_row_sum M (fun _ => H) hM
  refine ⟨H, hH, rows, ?_⟩
  change M.det.natDegree = s * H
  apply natDegree_eq_of_le_of_coeff_ne_zero _ hcoeff
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using hdeg

end K21_2_1
end Port_K1_2_1Shifts

section Port_K1_2_1Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K21_2_1

open Polynomial FrobeniusLocator K21 K1_6

theorem proof : K21_2.c1 := by
  intro u guard T R
  let P (b : Fin 2) : Bivar := Principal.assemble (fun j => R.coefficients (b, j))
  let s := 49058 - T.height
  have hP : ∀ b, (P b).natDegree ≤ T.height := R.x_degree
  have hBalance : 49058 + T.height + nullity u = 82015 ∧
      T.height ≤ 32950 ∧ T.height < 49058 :=
    Native6921Balance (nullity u) T.a T.b T.c
      T.top T.degreeSum T.nullitySum (by have := guard.1; omega)
  have hSum : T.height + s = 49058 := by omega
  have hs : 16108 ≤ s := by omega
  have hRank : GenericLayer.genericRank (twoBlock u) + s = 2 * 49058 := by
    change stackRank u + s = _
    rw [K21.actual_stackRank u]
    omega
  have hCoordinates : pairCoordinates P T.height = R.coefficients := by
    funext i
    exact Principal.assemble_coeff (fun j => R.coefficients (i.1, j)) i.2
  have hPrim : PrimitiveVector.IsPrimitive (pairCoordinates P T.height) := by
    rw [hCoordinates]
    exact R.primitive
  have hMinors := shift_minors_primitive P T.height s hP hPrim
  obtain ⟨H, hH, rows, hRows⟩ := shift_minors_height P T.height s hP hPrim
  rw [hSum] at hMinors
  have hBound := complementary_minor_bound 49058 82015 s p (twoBlock u) (shifts P 49058 s)
    (by norm_num [Native.p]) hRank (K21_6.certificate_shifts_annihilate R s hSum)
    (stacked_entry_natDegree p node (u 0) (u 1) 49058 82014) hMinors
  have hRows' : ∃ rows : Fin s → Fin 2 × Fin 49058,
      (maximalMinors (shifts P 49058 s) rows).natDegree = s * H := by
    rw [← hSum]
    exact ⟨rows, hRows⟩
  obtain ⟨rows', hdeg⟩ := hRows'
  have hDegree := hBound rows'
  rw [hdeg] at hDegree
  have hProduct := Nat.mul_le_mul_right H hs
  have hCeiling : 49058 * (p + 1) = 104528196239172 := by norm_num [Native.p]
  have hCap : H ≤ 6489210095 := by omega
  intro i
  rw [← hCoordinates]
  exact (hH i.1 i.2.val).trans hCap

end K21_2_1
end Port_K1_2_1Proof
