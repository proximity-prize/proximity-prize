import ProximityPrize.SubmissionLower.ZhyMlza
set_option Elab.async false
section
set_option autoImplicit true
namespace qOu6zab
noncomputable section


open qckEfrc (Var af Box drift zD BA)
open cu (FX)
open aZa (D6 aG6)
open MvPolynomial Finset
local notation "ord" => (some (0:Fin 2))
local notation "vel" => (some (1 :Fin 2))
local notation "sep" => MvPolynomial.pderiv (R:=FX) vel
private abbrev W (w:Var→ℕ) (n:ℕ) :=restrictWeightedDegree (R:=FX) w n
private theorem avO {w:Var→ℕ} {q:af} {n:ℕ}
  (hq:q∈W w n) :D6 q∈W w n:= by
 rw [mem_restrictWeightedDegree] at hq ⊢
 intro m hm
 apply hq m
 contrapose! hm
 rw [notMem_support_iff] at hm ⊢
 rw [aG6,hm,map_zero]
private theorem c00 {w:Var→ℕ} {f q:af} {a n:ℕ} (i:Var)
   (hf :f∈W w (a+w i)) (hq:q∈W w n) :f*pderiv i q∈W w (a+n) := by
 classical
 by_cases hi:w i≤n
 · have h:=mul_mem_restrictWeightedDegree hf (pderiv_mem_restrictWeightedDegree i hq)
   rwa [show a+w i+(n - w i)=a+n by omega] at h
 · have hz :pderiv i q=0:= by
     apply MvPolynomial.eq_zero_iff.mpr
     intro m
     rw [coeff_pderiv]
     suffices h:q.coeff (m+Finsupp.single i 1)=0 by rw [h,zero_mul]
     by_contra hc
     have hn:=mem_restrictWeightedDegree.mp hq _ (mem_support_iff.mpr hc)
     rw [map_add,Finsupp.weight_single,one_smul] at hn
     omega
   rw [hz,mul_zero]
   exact (W w _).zero_mem
private theorem drift_bound {w:Var→ℕ} {q:af} {n δ:ℕ}
  (hw:w vel=w ord+δ) (hq:q∈W w n) :drift q∈W w (n+δ) := by
 unfold drift
 refine (W w _).add_mem
  (restrictWeightedDegree_mono w (Nat.le_add_right _ _) (avO hq)) ?_
 have hx :MvPolynomial.X vel∈W w (δ+w ord) :=
  X_mem_restrictWeightedDegree w (δ+w ord) vel (by omega)
 simpa only [Nat.add_comm δ n] using c00 ord hx hq
private theorem sep_bound {w:Var→ℕ} {g:af} {a :ℕ}
  (hg:g∈W w (a+w vel)) :sep g∈W w a := by
 simpa only [Nat.add_sub_cancel] using pderiv_mem_restrictWeightedDegree vel hg
private theorem aFc {w:Var→ℕ} {g q:af} {a n δ:ℕ}
   (hg:g∈W w (a+w vel)) (hw:w vel=w ord+δ) (hq:q∈W w n) :
   zD g q∈W w (a+n+δ) := by
 unfold zD
 refine (W w _).sub_mem ?_ ?_
 · simpa only [Nat.add_assoc] using
     mul_mem_restrictWeightedDegree (sep_bound hg) (drift_bound hw hq)
 · have hd:drift g∈W w ((a+δ)+w vel) := by
     simpa only [Nat.add_right_comm a (w vel) δ] using drift_bound hw hg
   simpa only [Nat.add_right_comm a δ n] using c00 vel hd hq
private abbrev coeffCap (w:Var→ℕ) (a δ i:ℕ) :=
 w ord+(2*i+1)*a+(i+2)*δ
private theorem bCJ {w:Var→ℕ} {g:af} {a δ:ℕ}
    (hg:g∈W w (a+w vel)) (hw:w vel=w ord+δ) (i:ℕ) :
    BA g i∈W w (coeffCap w a δ i) := by
  have hs :=sep_bound hg
  induction i with
  | zero =>
    rw [BA,show coeffCap w a δ 0=a+w vel+δ by
      rw [hw]
      unfold coeffCap
      ring]
    exact (W w _).neg_mem (drift_bound hw hg)
  | succ i ih =>
    rw [BA]
    refine (W w _).sub_mem ?_ ?_
    · have h:=mul_mem_restrictWeightedDegree hs (aFc hg hw ih)
      rwa [show a+(a+coeffCap w a δ i+δ)=coeffCap w a δ (i+1) by
        unfold coeffCap
        ring] at h
    · rw [mul_assoc,← smul_eq_C_mul]
      apply (W w _).smul_mem
      have h:=mul_mem_restrictWeightedDegree (aFc hg hw hs) ih
      rwa [show a+a+δ+coeffCap w a δ i=coeffCap w a δ (i+1) by
        unfold coeffCap
        ring] at h
private theorem padded_cap {D i:ℕ} (a δ z :ℕ) (hi:i+2≤D) :
  (2*D-3-(2*i+1))*a+(z+(2*i+1)*a+(i+2)*δ)≤z+(2*D-3)*a+D*δ:= by
 have he :2*D-3-(2*i+1)+(2*i+1)=2*D-3:= by omega
 calc
  _=z+(2*D-3-(2*i+1)+(2*i+1))*a+(i+2)*δ:= by ring
  _≤_:= by
    rw [he]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right δ hi) _
local notation "ws" => (fun v :Var=>Option.elim v 1 fun _=>0)
local notation "wt" => (fun v :Var=>Option.elim v 0 fun _=>1)
private abbrev wv :Var→ℕ:=Pi.single vel 1
private theorem box_of_weights {q:af} {b j u:ℕ}
  (hs :q∈W ws u) (ht:q∈W wt b) (hv :q∈W wv j) :
  q∈Box b (min b j) u:= by
 rw [mem_restrictWeightedDegree] at hs ht hv
 simp only [Finsupp.weight_elim_one_zero] at hs
 simp only [Finsupp.weight_elim_zero_one] at ht
 simp only [wv,Finsupp.weight_single_one_apply] at hv
 exact mem_restrictCappedBidegree_of_mem_restrictBidegree
  (mem_restrictBidegree.mpr fun m hm=>⟨hs m hm,ht m hm⟩) (degreeOf_le_iff.mpr hv)
end
end qOu6zab
end
section
set_option autoImplicit true
namespace qRG2vfc
noncomputable section
open P5 (K)

open qckEfrc

open cu (L FX kr)
open vq (Dx apZ aYD ZC)
open aZa (D6)
open MvPolynomial Finset
open scoped Polynomial
open private dmS aZa.cbs aZa.cbt from ProximityPrize.SubmissionLower.Z3EWiUc
open private vq.anS from ProximityPrize.SubmissionLower.Z3EWiUc


local notation "ord" => (some (0:Fin 2))
local notation "vel" => (some (1 :Fin 2))
local notation "sep" => MvPolynomial.pderiv (R:=FX) vel
private abbrev ev (z :L) (S:K[X]) :=eval (point z S)
private theorem aKe (z :L) (S:K[X]) (q:af) :
    Dx (ev z S q)=ev z S (drift q)+kr S.derivative.derivative*ev z S (sep q) := by
  classical
  have chain :
      Dx (ev z S q)=ev z S (D6 q)+kr S.derivative*ev z S (pderiv ord q) +
        kr S.derivative.derivative*ev z S (sep q) := by
    induction q using MvPolynomial.induction_on with
    | C a=>simp [ev,aZa.cbs]
    | add q r hq hr =>
      simp only [map_add,hq,hr,mul_add]
      ring
    | mul_X q i hq =>
      have hi:Dx (ev z S (MvPolynomial.X i)) =
          kr S.derivative*ev z S (pderiv ord (MvPolynomial.X i)) +
          kr S.derivative.derivative*ev z S (sep (MvPolynomial.X i)) := by
        cases i with
        | none=>simp [ev,point,pderiv_X,dmS]
        | some j=>fin_cases j <;> simp [ev,point,pderiv_X,aYD]
      simp only [map_mul,apZ,hq,aZa.cbt,pderiv_mul,map_add,hi]
      ring
  have hvel:point z S vel=kr S.derivative :=rfl
  simpa only [drift,map_add,map_mul,eval_X,hvel] using chain
private theorem bpI (g q:af) (z :L) (S:K[X])
  (hg:ev z S g=0) :ev z S (zD g q)=ev z S (sep g)*Dx (ev z S q) := by
 have h:=aKe z S g
 rw [hg,map_zero] at h
 rw [aKe,zD,map_sub,map_mul,map_mul]
 linear_combination ev z S (sep q)*h
private theorem aNv (g:af) (z :L) (S:K[X]) (hg:ev z S g=0) (i:ℕ) :
   ev z S (BA g i)=ev z S (sep g)^(2*i+1)*ZC S (i+2) := by
 induction i with
 | zero =>
   have h:=aKe z S g
   rw [hg,map_zero] at h
   simp only [BA,map_neg,Nat.mul_zero,Nat.zero_add,pow_one]
   change -ev z S (drift g)=ev z S (sep g)*kr S.derivative.derivative
   linear_combination h
 | succ i ih =>
   rw [BA,map_sub,map_mul,map_mul,map_mul,eval_C,bpI _ _ _ _ hg,
    bpI _ _ _ _ hg,ih,vq.anS,
    show 2*(i+1)+1=2*i+1+2 by omega,aYD]
   congr 1
   exact congrArg kr (Function.iterate_succ_apply' _ _ _).symm
private theorem padding {d i:ℕ} (hi:i+1<d) :
 2*d-3-(2*i+1)+(2*i+1)=2*d-3:= by omega
end
end qRG2vfc
end
