import ProximityPrize.SubmissionLower.ZN2gA7a
import ProximityPrize.SubmissionLower.ZE36Kga
import ProximityPrize.SubmissionLower.ZF73i6b
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qWnROxa
noncomputable section
open Polynomial Finset


open qNu3xvc qypA4Sc


private theorem fXo {E :Type} [Field E]
    (P Q:E[X][X]) (m n B D s :ℕ)
    (hP : ∀ i≤ m,(P.coeff i).natDegree+s*i≤B)
    (hQ : ∀ i≤n,(Q.coeff i).natDegree+s*i≤D) :
    (P.resultant Q m n).natDegree≤n*B+m*D - s*(m*n) := by
  classical
  let M:=sylvester P Q m n
  let W:Fin (m+n)→ℕ:=Fin.addCases
    (fun j:Fin m=>D + s*j.val) (fun j:Fin n=>B+s*j.val)
  have hentry (i j:Fin (m+n)) (hne :M i j≠0) :
      (M i j).natDegree+s*i.val≤W j:= by
    cases j using Fin.addCases with
    | left a =>
      simp only [M,sylvester,Matrix.of_apply,Fin.addCases_left] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hh:=hQ (i.val-a.val) (by have :=h.2; omega)
        simp only [W,Fin.addCases_left]
        have he :s*(i.val-a.val)+s*a.val=s*i.val :=
          by rw [← Nat.mul_add,Nat.sub_add_cancel h.1]
        omega
      · exact (hne rfl).elim
    | right a =>
      simp only [M,sylvester,Matrix.of_apply,Fin.addCases_right] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hh:=hP (i.val-a.val) (by have :=h.2; omega)
        simp only [W,Fin.addCases_right]
        have he :s*(i.val-a.val)+s*a.val=s*i.val :=
          by rw [← Nat.mul_add,Nat.sub_add_cancel h.1]
        omega
      · exact (hne rfl).elim
  let S:=(∑ j:Fin m,s*j.val) + ∑ j:Fin n,s*j.val
  have hW : ∑ i,W i=m*D + n*B+S:= by
    simp only [W,S,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,
      Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    ring
  have hsum : ∑ i:Fin (m+n),s*i.val=s*(m*n)+S:= by
    simp only [S,Fin.sum_univ_add,Fin.val_castAdd,Fin.val_natAdd,Nat.mul_add,
      Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    ring
  change M.det.natDegree≤_
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  have hterm : (∏ i,M (σ i) i).natDegree≤n*B+m*D - s*(m*n) := by
    by_cases hz : ∃ i,M (σ i) i=0
    · obtain ⟨i,hi⟩:=hz
      have hp: (∏ j,M (σ j) j)=0:=Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hp,natDegree_zero]
      exact Nat.zero_le _
    · simp only [not_exists] at hz
      apply (natDegree_prod_le _ _).trans
      have h:=Finset.sum_le_sum (s :=Finset.univ) (fun i _=>hentry (σ i) i (hz i))
      rw [Finset.sum_add_distrib,Equiv.sum_comp σ (fun i=>s*i.val),hW,hsum] at h
      omega
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simpa [hs] using hterm
end
end qWnROxa
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qXLxXWd
noncomputable section
open P6 (K)
open P5_7 (midAgreement)
open P5_7_1 (wD)
open qH0Nw9c (LineRow LineCaps)
open qckEfrc (Var Box Regular point)
open qp56ikd (gap errors total top seed kK charged)
open cu (L FX kr Jet)
open Finset MvPolynomial
open private e rename_caps from ProximityPrize.SubmissionLower.ZhyMlza
open private OF OF.mk from ProximityPrize.SubmissionLower.ZogIzOe
def feeAt (D b j u:ℕ) :ℕ :=
  let t:=2*D-3
  let a :=1+t*(b-1)
  let v :=min a (t*(j-1)+D)
  let U:=t*u
  let mix :=u*(2*a*v-v*v)+2*U*(b*v+j*(a-v))
  let rest:=u*(2*a+v)+U*(2*b+j)+b*v+j*a+u+b+j
  let q:=midAgreement-D
  (2*(262144-midAgreement)*(mix+rest)+q-1)/q+b+u+1
private theorem bw {D n b j u:ℕ} (hg:0<gap D)
    (h:gap D *n≤2*errors*kK D b j u+gap D *(b+u)) :
    n≤feeAt D b j u:= by
  let a :=total D b
  let v :=top D b j
  let U:=seed D u
  let M:=kK D b j u
  let C:=u*(2*a+v)+U*(2*b+j)+b*v+j*a+u+b+j
  have hM:M=u*(2*a*v-v*v)+2*U*(b*v+j*(a-v)) := by
    change kK D b j u= _
    rw [kK,cappedBidegreeMixedVolume_eq (show v≤a from min_le_left _ _)]
    change u*v*(2*a-v)+2*U*(b*v+j*(a-v))= _
    rw [Nat.mul_assoc u v,Nat.mul_sub_left_distrib,mul_comm v (2*a)]
  change n≤(2*errors*((u*(2*a*v-v*v)+2*U*(b*v+j*(a-v)))+C)+gap D-1)/gap D+b+u+1
  rw [← hM]
  have hx :gap D *(n-(b+u))≤2*errors*M:= by
    by_cases hn:n≤b+u
    · simp [Nat.sub_eq_zero_of_le hn]
    · have hh:=congrArg (gap D * ·) (Nat.sub_add_cancel (show b+u≤n by omega))
      rw [Nat.mul_add] at hh
      change gap D *n≤2*errors*M+gap D*(b+u) at h
      omega
  have hnum :2*errors*M≤2*errors*(M+C)+gap D-1 := by
    have hh:=Nat.mul_le_mul_left (2*errors) (Nat.le_add_right M C)
    omega
  have hd:=(Nat.le_div_iff_mul_le hg).mpr ((mul_comm _ _).trans_le (hx.trans hnum))
  omega
open scoped Classical in
theorem count {D A:ℕ} (hd:2≤D) (hdD:D ≤133774) (hg:0<gap D)
    (hA:midAgreement≤A) {h u del} {M:P1.FJ h u del} {Γ:Finset K}
    (F:P1.bje A M Γ) (hdeg : ∀ γ∈Γ,(F.scalar γ).natDegree≤D)
    (f :Jet) (g:LineRow) (hj:0<wD f 1) (hu:0<wD f 2) (hcaps :LineCaps f g) :
    (Γ.filter fun γ => ∃ z :L,
      let v := ![algebraMap L FX z,kr (F.scalar γ),kr (F.scalar γ).derivative]
      MvPolynomial.eval v g=0∧MvPolynomial.eval v (MvPolynomial.pderiv 2 g)≠0).card ≤
      feeAt D (wD f 0) (wD f 1) (wD f 2) := by
  classical
  have hf :f≠0:=Polynomial.ne_zero_of_natDegree_gt hj
  have hb:0<wD f 0:=hj.trans_le (akZ.caQ hf)
  let T:=Γ.filter fun γ => ∃ z :L,
      let v := ![algebraMap L FX z,kr (F.scalar γ),kr (F.scalar γ).derivative]
      MvPolynomial.eval v g=0∧MvPolynomial.eval v (MvPolynomial.pderiv 2 g)≠0
  have hG:rename e g∈Box (wD f 0) (wD f 1) (wD f 2) :=rename_caps hcaps
  have hz (γ:K) : ∃ z :L,γ∈T→Regular (rename e g) z (F.scalar γ) := by
    by_cases hγ:γ∈T
    · obtain ⟨z,hz⟩:=(mem_filter.mp hγ).2
      have hp:point z (F.scalar γ) ∘ e =
          ![algebraMap L FX z,kr (F.scalar γ),kr (F.scalar γ).derivative] := by
        funext i
        fin_cases i <;> rfl
      refine ⟨z,fun _ => ?_⟩
      unfold Regular
      rw [show (some 1 :Var)=e 2 by rfl,pderiv_rename e.injective,eval_rename,eval_rename,hp]
      exact hz
    · exact ⟨0,fun hh=>(hγ hh).elim⟩
  choose z hz using hz
  have hT:T⊆Γ:=filter_subset _ _
  have hw:OF M.word T F.scalar D:= by
    refine OF.mk (F.distinct.mono hT) (fun γ hγ=>hdeg γ (hT hγ)) ?_
    intro γ hγ
    let m:=F.mark γ (hT hγ)
    exact ⟨m.bad.support,hA.trans m.bad.dw,m.scalar_hits⟩
  have h:=charged hw hd hdD hb hj hu hG z hz
  apply bw (n:=T.card) (b:=wD f 0) (j:=wD f 1) (u:=wD f 2) hg
  exact_mod_cast h
end
end qXLxXWd
end
