import Mathlib.Algebra.Polynomial.CoeffMem
import ProximityPrize.SubmissionLower.Zw100fa
set_option Elab.async false
open _root_ renaming Fintype.card_fin → zgY, Function.Injective → zq4, LinearMap.pi → z9H, Module.finrank → zsE, Module.finrank_pi_fintype → z0r, Nat.le_of_lt_succ → zeh, Nat.le_of_not_gt → zqB, Polynomial.induction_on' → zCU, Polynomial.map_pow → z5m, Polynomial.map_sub → z3A, Submodule.sum_mem → zo3, Submodule.zero_mem → z4M
set_option backward.isDefEq.respectTransparency false
namespace qvwhqDa
noncomputable section
open Polynomial Finset
open cu (L)
open qBd5KZd (Allowance small btN bounded modulus weight j3)
open scoped Classical WithZero
variable {E :Type} [Field E] [Algebra L E]
private theorem afg {A B:Allowance E} {f h:E[X][X]}
  (hf :bounded A f) (hh:bounded B h) :bounded (B+A) (f*h) := by
 intro i j
 rw [coeff_mul,finsetSum_coeff]
 apply zo3
 intro ij _
 rw [coeff_mul]
 apply zo3
 intro kl _ v
 have ha :=hf ij.1 kl.1 v
 have hb:=hh ij.2 kl.2 v
 change small v ((B+A) v) _
 simp only [small,map_mul,Finsupp.add_apply,Nat.cast_add,WithZero.exp_add] at ha hb ⊢
 exact (mul_le_mul' ha hb).trans_eq (mul_comm _ _)
private theorem bounded_div (A:Allowance E) (b:L) (M:ℕ) {f :E[X]}
   (hf : ∀ i,f.coeff i∈btN A) (j:ℕ) :
   (f %ₘ modulus b M).coeff j∈btN A ∧
     (f /ₘ modulus b M).coeff j∈btN A:= by
 let d:L[X] :=(Polynomial.X-Polynomial.C b)^M
 have hd:d.map (algebraMap L E)=modulus b M:= by
   simp only [d,modulus,z5m,z3A,map_X,map_C]
 have hconst (i:ℕ) : (modulus b M:E[X]).coeff i∈(1 :Submodule L E) := by
   rw [← hd,coeff_map]
   exact Submodule.mem_one.mpr ⟨_,rfl⟩
 have hone : (1 :E)∈btN A:= by
   intro v
   change v.value 1≤WithZero.exp ((A v :ℕ) :ℤ)
   rw [map_one,WithZero.one_le_exp_iff]
   exact Int.natCast_nonneg _
 constructor
 · simpa only [one_pow,one_mul] using
     coeff_modByMonic_mem_pow_natDegree_mul f _ (btN A) hf hone 1 hconst (by simp) j
 · simpa only [one_pow,one_mul] using
     coeff_divByMonic_mem_pow_natDegree_mul f _ (btN A) hf hone 1 hconst (by simp) j
omit [Algebra L E] in
private theorem bOH (P:E[X][X]) (i j:ℕ) :
   ((Bivariate.swap P).coeff j).coeff i=(P.coeff i).coeff j:= by
 induction P using zCU with
 | add P Q hp hq=>simp only [map_add,coeff_add,hp,hq]
 | monomial n P =>
   induction P using zCU with
   | add P Q hp hq=>simp only [map_add,coeff_add,hp,hq]
   | monomial m c =>
     rw [Bivariate.swap_monomial_monomial]
     by_cases hi:n=i <;> by_cases hj:m=j <;> simp [coeff_monomial,hi,hj]
private theorem fresh {f :E[X][X]} (hf :f≠0) :
  ∃ b:L,¬ IsRoot (Bivariate.swap f) (C (algebraMap L E b)) := by
 by_contra! hb
 have hF:Bivariate.swap f≠0:= fun h=>hf (Bivariate.swap.injective (h.trans (map_zero _).symm))
 exact (Set.infinite_range_of_injective (C_injective.comp (algebraMap L E).injective))
  ((finite_setOfPred_isRoot hF).subset (Set.range_subset_iff.mpr hb))
private theorem no_divisor {f h:E[X][X]} (hf :f≠0) (hh:h≠0) {b:L} {M:ℕ}
  (hb : ¬ IsRoot (Bivariate.swap f) (C (algebraMap L E b)))
  (hdeg: (Bivariate.swap h).natDegree<M) : ¬ C (modulus b M)∣f*h:= by
 intro hd
 have hd' := _root_.map_dvd (Bivariate.swap (R:=E)) hd
 rw [map_mul,Bivariate.swap_C] at hd'
 simp only [modulus,z5m,z3A,map_X,map_C] at hd'
 have hF:Bivariate.swap f≠0:= fun h=>hf (Bivariate.swap.injective (h.trans (map_zero _).symm))
 have hH :Bivariate.swap h≠0:= fun h=>hh (Bivariate.swap.injective (h.trans (map_zero _).symm))
 have hmul :=mul_ne_zero hF hH
 have hm:=(le_rootMultiplicity_iff hmul).mpr hd'
 rw [rootMultiplicity_mul hmul,rootMultiplicity_eq_zero hb,zero_add] at hm
 have hn:=natDegree_le_of_dvd ((le_rootMultiplicity_iff hH).mp hm) hH
 rw [natDegree_pow,natDegree_X_sub_C,mul_one] at hn
 exact hdeg.not_ge hn
private abbrev Stock (g M:ℕ) (B:Allowance E) :=Fin (g+1)×Fin M→btN B
private def pack (g M:ℕ) (B:Allowance E) :Stock g M B →ₗ[L] E[X][X] :=
 ((ofFn (g+1)).restrictScalars L).comp (z9H fun i =>
   ((ofFn M).restrictScalars L).comp (z9H fun j =>
     (btN B).subtype.comp (LinearMap.proj (i,j))))
private theorem eIR {g M:ℕ} {B:Allowance E} (u:Stock g M B) (i j:ℕ) :
   ((pack g M B u).coeff i).coeff j =
     if hi:i<g+1 then if hj:j<M then (u (⟨i,hi⟩,⟨j,hj⟩) :E) else 0 else 0:= by
 change ((ofFn (g+1) fun a=>ofFn M fun b=>(u (a,b) :E)).coeff i).coeff j= _
 by_cases hi:i<g+1
 · rw [ofFn_coeff_eq_val_of_lt _ hi,dite_eq_left hi]
   by_cases hj:j<M
   · rw [ofFn_coeff_eq_val_of_lt _ hj,dite_eq_left hj]
   · rw [ofFn_coeff_eq_zero_of_ge _ (zqB hj),dite_eq_right hj]
 · rw [ofFn_coeff_eq_zero_of_ge _ (zqB hi),coeff_zero,dite_eq_right hi]
private def Kt (n:ℕ) (t:E[X] →ₗ[L] E[X]) :E[X][X] →ₗ[L] E[X][X] :=
 ((ofFn (n+1)).restrictScalars L).comp (z9H fun i =>
   t.comp ((lcoeff (E[X]) i).restrictScalars L))
private theorem onRows_coeff (n:ℕ) (t:E[X] →ₗ[L] E[X]) (P:E[X][X]) (i:ℕ) :
   (Kt n t P).coeff i=if i<n+1 then t (P.coeff i) else 0:= by
 change (ofFn (n+1) fun j=>t (P.coeff j)).coeff i= _
 by_cases hi:i<n+1
 · rw [ofFn_coeff_eq_val_of_lt _ hi,ite_eq_left hi]
 · rw [ofFn_coeff_eq_zero_of_ge _ (zqB hi),ite_eq_right hi]
private abbrev Removed (D n:ℕ) :=Σ i:Fin (n+1),Fin ((i:ℕ)*D)
private theorem removed_card (D n:ℕ) :Fintype.card (Removed D n)=j3 D n:= by
 rw [Fintype.card_sigma]
 simp only [zgY,← Finset.sum_mul]
 let s := ∑ i:Fin (n+1),(i:ℕ)
 have hs :s*2=n*(n+1) := by
   dsimp only [s]
   rw [Fin.sum_univ_eq_sum_range (fun i:ℕ=>i),sum_range_id_mul_two,
     Nat.add_sub_cancel,Nat.mul_comm]
 have hs' : (s*D)*2=D*n*(n+1) := by
   calc
     _=D*(s*2) := by ring
     _ = _:= by rw [hs]; ring
 change s*D =D*n*(n+1)/2
 omega
theorem proof :qBd5KZd.c4 := by
  intro E _ _ D e g M f A B hf he hM hA hBdim hSdim
  let _:=hBdim
  let _:=hSdim
  let n:=e+g
  have hM0:0<M:=Nat.zero_lt_of_lt hM
  obtain ⟨b,hb⟩:=fresh hf
  let d:E[X] :=modulus b M
  have hd:d.Monic:=(monic_X_sub_C _).pow M
  have hddeg:d.natDegree=M:= by simp [d,modulus,natDegree_pow]
  have hd1 :d≠1 := fun h=>hM0.ne' (hddeg.symm.trans (by rw [h,natDegree_one]))
  let prod:=(LinearMap.mulLeft L f).comp (pack g M B)
  let T:=(Kt n ((modByMonicHom d).restrictScalars L)).comp prod
  let Q:=(Kt n ((divByMonicHom d).restrictScalars L)).comp prod
  have hpack (u:Stock g M B) :bounded B (pack g M B u) := by
    intro i j
    rw [eIR]
    split_ifs <;> first | exact Subtype.property _ | exact z4M _
  have hprod (u:Stock g M B) :bounded (B+A) (prod u) :=afg hA (hpack u)
  have hpdeg (u:Stock g M B) : (prod u).natDegree≤n :=
    natDegree_mul_le_of_le he (zeh (ofFn_natDegree_lt (Nat.zero_lt_succ g) _))
  have htdeg (u:Stock g M B) : (T u).natDegree≤n :=
    zeh (ofFn_natDegree_lt (Nat.zero_lt_succ n) _)
  have hrem (u:Stock g M B) (i:ℕ) :
      (T u).coeff i=if i<n+1 then (prod u).coeff i %ₘ d else 0 :=
    onRows_coeff n _ _ i
  have hquot (u:Stock g M B) (i:ℕ) :
      (Q u).coeff i=if i<n+1 then (prod u).coeff i /ₘ d else 0 :=
    onRows_coeff n _ _ i
  have hT (u:Stock g M B) :bounded (B+A) (T u) := by
    intro i j
    rw [hrem]
    split_ifs
    · exact (bounded_div (B+A) b M (hprod u i) j).1
    · rw [coeff_zero]; exact z4M _
  have hQ (u:Stock g M B) :bounded (B+A) (Q u) := by
    intro i j
    rw [hquot]
    split_ifs
    · exact (bounded_div (B+A) b M (hprod u i) j).2
    · rw [coeff_zero]; exact z4M _
  have hrel (u:Stock g M B) :f*pack g M B u=T u+C d*Q u:= by
    apply Polynomial.ext
    intro i
    change (prod u).coeff i= _
    rw [coeff_add,coeff_C_mul,hrem,hquot]
    split_ifs with hi
    · exact (modByMonic_add_div _ _).symm
    · rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le
        ((Nat.succ_le_succ (hpdeg u)).trans (zqB hi))),mul_zero,add_zero]
  have hTin:zq4 T:= by
    apply (injective_iff_map_eq_zero T).mpr
    intro u hu
    have hz :pack g M B u=0:= by
      by_contra hh
      have hdeg: (Bivariate.swap (pack g M B u)).natDegree<M:= by
        apply Nat.lt_of_le_pred hM0
        apply natDegree_le_iff_coeff_eq_zero.mpr
        intro j hj
        apply Polynomial.ext
        intro i
        rw [bOH,coeff_zero,eIR]
        have hk : ¬ j<M:= fun h=>hj.not_ge ((Nat.lt_iff_le_pred hM0).mp h)
        by_cases hi:i<g+1 <;> simp [hi,hk]
      apply no_divisor hf hh hb hdeg
      exact ⟨Q u,by rw [hrel,hu,zero_add]⟩
    funext k
    obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩:=k
    apply Subtype.ext
    change (u (⟨i,hi⟩,⟨j,hj⟩) :E)=0
    have h:=congrArg (fun P:E[X][X]=>(P.coeff i).coeff j) hz
    simpa only [eIR,dite_eq_left hi,dite_eq_left hj,coeff_zero] using h
  let test :Stock g M B →ₗ[L] (Removed D n→btN (B+A)) :=z9H fun j =>
    ((((lcoeff E (M-1-j.2)).restrictScalars L).comp
      ((lcoeff (E[X]) j.1).restrictScalars L)).comp T).codRestrict _
        (fun u=>hT u j.1 (M-1-j.2))
  let out:=T.comp test.ker.subtype
  refine ⟨b,out.range,?_,?_⟩
  · have hI:zsE L (Stock g M B) =
        ((g+1)*M)*zsE L (btN B) := by
      rw [z0r,sum_const,card_univ,Fintype.card_prod,zgY,
        zgY,Nat.nsmul_eq_mul]
    have hJ:zsE L (Removed D n→btN (B+A)) =
        j3 D n*zsE L (btN (B+A)) := by
      rw [z0r,sum_const,card_univ,removed_card,Nat.nsmul_eq_mul]
    have hout:zq4 out:= by
      intro u v huv
      exact Subtype.ext (hTin huv)
    rw [LinearMap.finrank_range_of_inj hout]
    have hr :=test.range.finrank_le
    have hk :=test.finrank_range_add_finrank_ker
    rw [hJ] at hr
    rw [hI] at hk
    rw [← hk,Nat.add_comm (zsE L test.ker)]
    exact Nat.add_le_add_right hr _
  · rintro G ⟨u,rfl⟩
    change (T u.val).natDegree≤n∧weight D (T u.val)<M∧bounded (B+A) (T u.val)∧_
    refine ⟨htdeg _,?_,hT _,pack g M B u.val,Q u.val,hpack _,hQ _,hrel _⟩
    apply (Finset.sup_lt_iff hM0).mpr
    intro i hi
    have hrow:=mem_support_iff.mp hi
    have hin:i<n+1 :=Nat.lt_succ_of_le ((le_natDegree_of_ne_zero hrow).trans (htdeg _))
    let k :=((T u.val).coeff i).natDegree
    have hk :k<M:= by
      dsimp only [k]
      rw [hrem,ite_eq_left hin]
      exact (natDegree_modByMonic_lt _ hd hd1).trans_le hddeg.le
    change k+i*D <M
    by_contra! hbig
    have htop:M-1-k< i*D:= by omega
    let j:Removed D n:=⟨⟨i,hin⟩,⟨M-1-k,htop⟩⟩
    have hzero :=congrArg (fun v :Removed D n→btN (B+A)=>(v j:E))
      (LinearMap.mem_ker.mp u.property)
    change ((T u.val).coeff i).coeff (M-1-(M-1-k))=0 at hzero
    rw [show M-1-(M-1-k)=k by omega] at hzero
    exact (leadingCoeff_ne_zero.mpr hrow) hzero
end
end qvwhqDa
