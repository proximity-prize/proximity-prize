import ProximityPrize.SubmissionLower.ZpdLrZa
import ProximityPrize.SubmissionLower.Zi9hW0a
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qYVN5fe
noncomputable section
open Polynomial Finset

open P5 (p)
open qAW6lac (Index block ng pairDegree)
open private fXo from ProximityPrize.SubmissionLower.ZQfUTPd
def c1 :Prop :=
  ∀ d s W:ℕ,0<s→s<p→2≤d→d<p→d*s≤W → ∀ k :Fin 3,
    let F:=pairForm d s W k (left k)
    let G:=pairForm d s W k (right k)
    let m:=yCap d (left k)
    let n:=yCap d (right k)
    IsCoprime (F.coeff m) (G.coeff n)∧F.resultant G m n≠0
def c2 :Prop :=
  ∀ (K:Type) [Field K] (F G:lK K) (m n:ℕ),0< m→0<n →
    F.natDegree≤ m→G.natDegree≤n→ IsCoprime (F.coeff m) (G.coeff n) →
    F.resultant G m n≠0 →
    Module.Finite K (pairQuot F G) ∧
      Module.finrank K (pairQuot F G)≤(F.resultant G m n).natDegree
def c3:Prop :=
  ∀ d s W:ℕ,0<s→s<p→2≤d→d<p→d*s≤W → ∀ k :Fin 3,
    Module.Finite (Ground d s W k) (PairAlgebra d s W k) →
    ∃ N :LocalRing d s W k,N≠0 ∧
      N.totalDegree≤Module.finrank (Ground d s W k) (PairAlgebra d s W k) ∧
      Polynomial.C (Polynomial.C N)∈Ideal.span (Set.range (localForm d s W k))
private theorem slot_caps {d s W:ℕ} (i:Index d s W) :
  yDeg i≤yCap d (block i)∧xDeg i+yDeg i*s≤wCap s W (block i) := by
 rcases i with i | (i | i)
 all_goals
  refine ⟨?_,?_⟩
  · simpa [block,yCap,yDeg] using Nat.le_of_lt_succ i.val.1.isLt
  · simpa [block,wCap,xDeg,yDeg] using i.prop
private theorem cSQ {K:Type} [CommRing K] {d s W:ℕ}
   (u:Index d s W→K) (j:Fin 3) : (form u j).natDegree≤yCap d j:= by
 apply natDegree_sum_le_of_forall_le
 intro i _
 split_ifs with hi
 · exact (natDegree_monomial_le _).trans (hi ▸ (slot_caps i).1)
 · simp
private theorem form_weight {K:Type} [CommRing K] {d s W:ℕ}
   (u:Index d s W→K) (j:Fin 3) (hcap:yCap d j*s≤wCap s W j)
   (t:ℕ) (ht: (form u j).coeff t≠0) :
   ((form u j).coeff t).natDegree+s*t≤wCap s W j:= by
 have hst:s*t≤wCap s W j:= by
   rw [Nat.mul_comm]
   exact (Nat.mul_le_mul_right s ((le_natDegree_of_ne_zero ht).trans (cSQ u j))).trans hcap
 suffices hb: ((form u j).coeff t).natDegree≤wCap s W j - s*t by omega
 rw [form,finsetSum_coeff]
 apply natDegree_sum_le_of_forall_le
 intro i _
 split_ifs with hi
 · by_cases he :yDeg i=t
   · rw [coeff_monomial,ite_eq_left he]
     have hw:=(slot_caps i).2
     rw [hi,he,Nat.mul_comm t s] at hw
     exact (natDegree_monomial_le _).trans (by omega)
   · simp [coeff_monomial,he]
 · simp
private theorem cap_valid {d s W:ℕ} (hW:d*s≤W) (j:Fin 3) :
   yCap d j*s≤wCap s W j:= by
 by_cases hj:j=2
 · simp only [yCap,wCap,hj,ite_true]
   by_cases hd:d=0
   · simp [hd]
   · have h:d-1+1=d:= by omega
     have hh: (d-1)*s+s=d*s := by rw [← Nat.succ_mul,Nat.succ_eq_add_one,h]
     omega
 · simpa [yCap,wCap,hj] using hW
private theorem cap_pos {d:ℕ} (hd:2≤d) (j:Fin 3) :0<yCap d j:= by
 unfold yCap
 split <;> omega
private theorem pair_cap (d s W:ℕ) (k :Fin 3) :
  yCap d (left k)*wCap s W (right k)+yCap d (right k)*wCap s W (left k) -
   s*(yCap d (left k)*yCap d (right k))=ng d s W k := by
 fin_cases k <;> simp [left,right,yCap,wCap,ng,pairDegree,Nat.mul_comm,Nat.mul_left_comm]
private theorem eJB (guards :c1) (quotient:c2)
   (d s W:ℕ) (hs :0<s) (hsp:s<p) (hd:2≤d) (hdp:d<p)
   (hW:d*s≤W) (k :Fin 3) :
   Module.Finite (Ground d s W k) (PairAlgebra d s W k) ∧
     Module.finrank (Ground d s W k) (PairAlgebra d s W k)≤ng d s W k := by
 obtain ⟨hc,hr⟩:=guards d s W hs hsp hd hdp hW k
 let F:=pairForm d s W k (left k)
 let G:=pairForm d s W k (right k)
 let m:=yCap d (left k)
 let n:=yCap d (right k)
 obtain ⟨hfinite,hdim⟩:=quotient _ F G m n (cap_pos hd _) (cap_pos hd _)
   (cSQ _ _) (cSQ _ _) hc hr
 refine ⟨hfinite,hdim.trans ?_⟩
 rw [← pair_cap d s W k]
 exact fXo F G m n s _ _ (form_weight _ _ (cap_valid hW _))
   (form_weight _ _ (cap_valid hW _))
theorem of_children (guards :c1) (quotient:c2) (norm:c3) :qAW6lac.c2 := by
 intro d s W hs hsp hd hdp hW R m hm k
 obtain ⟨hfinite,hdim⟩:=eJB guards quotient d s W hs hsp hd hdp hW k
 obtain ⟨N,hN,hdeg,hI⟩:=norm d s W hs hsp hd hdp hW k hfinite
 obtain ⟨Q,hQ,hvan,hbound⟩:=clear_norm k N hN hI
 have hdiv := _root_.map_dvd (splitCoeff d s W k).toRingHom (R.generates Q hvan)
 have hdeg' := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv
  ((map_ne_zero_iff _ (splitCoeff d s W k).injective).mpr hQ)
 exact (block_degree_le k R.poly m hm).trans (hdeg'.trans (hbound.trans (hdeg.trans hdim)))
end
end qYVN5fe
