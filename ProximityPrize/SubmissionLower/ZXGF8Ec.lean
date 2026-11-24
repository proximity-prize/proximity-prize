import ProximityPrize.SubmissionLower.ZjpV9lc
import ProximityPrize.SubmissionLower.ZofdZzd
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qRoCwuc
noncomputable section
open Polynomial Finset
open P5 (K p blockLength)
open qAxtVye (gap)
open cu (L)
open Cu (sQ)
open quN7Z4a (Sheet quadraticUnit)
open private common_divisor from ProximityPrize.SubmissionLower.ZjpV9lc
open scoped BigOperators
def c1 :Prop :=
  ∀ {C₀:sQ} [Fact (Irreducible C₀)] {J H T z s}
    (S:Sheet C₀ J 2 H T z s),Set.InjOn z (T:Set K) →
    (∀ j,((disc S).coeff j).totalDegree≤2) →
    (∀ γ∈goodMarks S,IsSquare ((disc S).map (MvPolynomial.eval (S.parameter γ)))) →
    (genericDisc S).natDegree<p → ¬ ConstantOddPart (genericDisc S) →
    Nonempty (OddModel (genericDisc S) (goodMarks S) H)
def c2 :Prop :=
  ∀ (A:Type) [CommRing A] (ρ:A →+* L) (π:A),
    Function.Surjective ρ→RingHom.ker ρ=Ideal.span {π} →
    ∀ (P Q:A[X]) (m n:ℕ) (D:L[X]),
      P.natDegree≤ m→Q.natDegree≤n→D.Monic→D.natDegree≤ m+n →
      D ∣P.map ρ→D ∣Q.map ρ→π^D.natDegree∣P.resultant Q m n
private theorem odd_count {F:Type} [Field F] {D:F[X]} {U:Finset K} {H :ℕ}
    (O:OddModel D U H) (h:c2) :U.card≤8*H := by
  classical
  by_cases hU:U.Nonempty
  swap
  · simp [not_nonempty_iff_eq_empty.mp hU]
  let m:=O.radical.natDegree
  have gX (γ:U) :
      ∃ k,m=2*k∧O.uniformizer γ^k∣(O.model γ).resultant (O.model γ).derivative m (m-1) := by
    let f :=O.model γ
    have hm:f.natDegree=m:= by
      rw [show m= _ from (congrArg natDegree (O.lift_eq γ)).symm,
        natDegree_map_eq_of_injective Subtype.val_injective]
    have hr : (f.map (O.residue γ)).natDegree=m:=((O.model_monic γ).natDegree_map _).trans hm
    obtain ⟨w,hw⟩:=O.square γ
    have hs :w^2=C (1 :L)*(1 :L[X])^2*f.map (O.residue γ) := by
      simpa only [pow_two,map_one,one_mul,f] using hw.symm
    obtain ⟨E,hE,hdeg,hf,hd⟩ :=
      common_divisor ((O.model_monic γ).map (O.residue γ)).ne_zero one_ne_zero one_ne_zero hs
    rw [hr] at hdeg
    refine ⟨E.natDegree,hdeg.symm,h _ _ _ (O.surjective γ) (O.kernel γ) _ _ _ _ E
      hm.le ?_ hE (by omega) hf ?_⟩
    · exact (natDegree_derivative_le _).trans_eq (by rw [hm])
    · simpa only [derivative_map] using hd
  obtain ⟨γ,hγ⟩:=hU
  obtain ⟨k,hk,_⟩:=gX ⟨γ,hγ⟩
  have hkpos :0<k := by have hm:0< m:=O.positive; omega
  have hsum:=O.budget (fun _=>k) (by
    intro δ
    obtain ⟨l,hl,hp⟩:=gX δ
    rwa [show k=l by omega])
  rw [sum_const,smul_eq_mul] at hsum
  apply Nat.le_of_mul_le_mul_right _ hkpos
  refine hsum.trans ?_
  calc
    _≤(2*m)*(2*H) :=Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _=8*H*k := by rw [hk]; ring
private theorem good_subset {C₀:sQ} [Fact (Irreducible C₀)] {J H T z s}
    (S:Sheet C₀ J 2 H T z s) :goodMarks S⊆T:= by
  classical
  unfold goodMarks
  exact filter_subset _ _
private theorem leading_exceptions {C₀:sQ} [Fact (Irreducible C₀)] {J H T z s}
    (S:Sheet C₀ J 2 H T z s) (hz :Set.InjOn z (T:Set K)) :
    (T \ goodMarks S).card≤2*H := by
  classical
  have he :coord S (leadCut S)=(genericDisc S).leadingCoeff := by
    rw [← coeff_natDegree]
    exact (coeff_map _ _).symm
  have hn:coord S (leadCut S)≠0:=he ▸ leadingCoeff_ne_zero.mpr (genericDisc_ne_zero S)
  exact (dSG S hz _ hn _ sdiff_subset (fun γ hγ=> by
    by_contra h
    exact (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨(mem_sdiff.mp hγ).1,h⟩))).trans
    (Nat.mul_le_mul_right H (disc_height S _))
theorem of_children (h1 :c1) (h2 :c2) :quN7Z4a.c3:= by
  classical
  intro b C₀ _ J T z s w d H S hb _ _ _ ht hw hz W
  have hn:0≤(blockLength:ℚ)/gap b:= by positivity
  have hA:3*(blockLength:ℚ)/gap b≤quadraticUnit b:= by
    unfold quadraticUnit
    rw [mul_div_assoc,mul_div_assoc]
    linarith only [hn]
  have hB: (10 :ℚ)≤quadraticUnit b:= by
    unfold quadraticUnit
    rw [mul_div_assoc]
    linarith only [hn]
  by_cases hd:ConstantOddPart (genericDisc S)
  · exact (dO2 S hz W (quN7Z4a.degree_lt hb) hd).trans
      (add_le_add (mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg H)) (by decide))
  · obtain ⟨O⟩:=h1 S hz (disc_height S)
      (fun γ hγ=>disc_square S (good_subset S hγ)) (disc_tame S hw ht) hd
    have hm:=odd_count O h2
    have he :=leading_exceptions S hz
    have hs :=card_sdiff_add_card_eq_card (good_subset S)
    have hc:T.card≤10*H := by omega
    exact (show (T.card:ℚ)≤10*H by exact_mod_cast hc).trans
      ((mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg H)).trans (le_add_of_nonneg_right (by decide)))
end
end qRoCwuc
