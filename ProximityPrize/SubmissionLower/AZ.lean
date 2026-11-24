import ProximityPrize.SubmissionLower.Z0omYcd
import ProximityPrize.SubmissionLower.ZYswgKc
set_option Elab.async false
set_option autoImplicit true
section
namespace vF
open fP (Ew)
open scoped BigOperators
noncomputable section
abbrev Ground :=ZMod P1.p
abbrev Exponent:=Fin 4 →₀ ℕ
abbrev gU (cut:ℕ) :=
 {m:Exponent // Ew 49 (cut:ℤ) 49 14 m}
instance cGU (cut:ℕ) :Finite (gU cut) :=
 ((Finsupp.finite_of_degree_le _).subset fun _ (h:Ew _ _ _ _ _) =>
   Nat.le_of_eq h.1).to_subtype
instance cGV (cut:ℕ) :Fintype (gU cut) :=
 Fintype.ofFinite _
end
end vF
end
section
namespace bAj
open vF (Ground)
open scoped BigOperators Matrix
open Polynomial
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem bmL {n:ℕ} (hn:0<n) (h:n<50) :
  (n:Ground)≠0:= by
 intro hz
 have hn' : n<P1.p:=h.trans (by decide)
 have hv :=congrArg ZMod.val hz
 rw [ZMod.val_natCast_of_lt hn',ZMod.val_zero] at hv
 omega
private theorem bcd {n:ℕ} (h:n<50) :
   (n.factorial:Ground)≠0:= by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [Nat.factorial_succ,Nat.cast_mul]
   exact mul_ne_zero (bmL (by omega) h) (ih (by omega))
private theorem cEn {n k :ℕ} (hk :k≤n) (hn:n<50) :
  (n.choose k :Ground)≠0:= by
 intro hz
 have h:=congrArg (fun v :ℕ=>(v :Ground))
  (Nat.choose_mul_factorial_mul_factorial hk)
 simp only [Nat.cast_mul,hz,zero_mul] at h
 exact bcd hn h.symm
theorem a6t (l s a :ℕ) (h:l+s+a≤50) (y :Fin a→Ground) :
   ∃ u:Fin a→Ground,∀ j:Fin a,
     (∑ i:Fin a,u i*((l+s+i.val).choose (l+j.val) :Ground))=y j:= by
 let x (i:Fin a) :Ground :=((s+i.val :ℕ) :Ground)
 let p (j:Fin a) :Polynomial Ground :=descPochhammer Ground j.val
 let M:Matrix (Fin a) (Fin a) Ground :=Matrix.of (fun i j=>(p j).eval (x i))
 have hx :Function.Injective x := by
   intro i j hij
   have hi:s+i.val<P1.p:=(show s+i.val<50 by omega).trans (by decide)
   have hj:s+j.val<P1.p:=(show s+j.val<50 by omega).trans (by decide)
   have hv :=congrArg ZMod.val hij
   change (((s+i.val :ℕ) :Ground)).val=(((s+j.val :ℕ) :Ground)).val at hv
   rw [ZMod.val_natCast_of_lt hi,ZMod.val_natCast_of_lt hj] at hv
   exact Fin.ext (by omega)
 have hdet:M.det≠0:= by
   rw [← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x p
     (fun j=>descPochhammer_natDegree _ _) (fun j=>monic_descPochhammer _ _)]
   exact Matrix.det_vandermonde_ne_zero_iff.mpr hx
 let C (i:Fin a) :Ground :=((l+s+i.val).choose l:Ground)
 let D (j:Fin a) :Ground :=((l+j.val).choose l:Ground)*(j.val.factorial:Ground)
 have hC (i:Fin a) :C i≠0:=cEn (by omega) (by omega)
 have hD (j:Fin a) :D j≠0 :=
   mul_ne_zero (cEn (by omega) (by omega)) (bcd (by omega))
 have hscale (i j:Fin a) :
     ((l+s+i.val).choose (l+j.val) :Ground)*D j=C i*M i j:= by
   have hc:=congrArg (fun v :ℕ=>(v :Ground))
     (Nat.choose_mul (n:=l+s+i.val) (k :=l+j.val) (s :=l) (by omega))
   simp only [Nat.cast_mul,Nat.add_sub_cancel_left] at hc
   have hsub:l+s+i.val-l=s+i.val := by omega
   rw [hsub] at hc
   change _ *(_ *_)= _ *(p j).eval (x i)
   rw [← mul_assoc,hc]
   change _ = _ *(descPochhammer Ground j.val).eval ((s+i.val :ℕ) :Ground)
   rw [descPochhammer_eval_eq_descFactorial,Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
   simp only [C,mul_assoc,mul_comm,mul_left_comm,Nat.add_assoc]
 obtain ⟨w,hw⟩:=(Matrix.vecMul_surjective_iff_isUnit.mpr
   ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet))) (fun j=>y j*D j)
 refine ⟨fun i=>w i/C i,fun j=>mul_right_cancel₀ (hD j) ?_⟩
 rw [Finset.sum_mul,← congrFun hw j]
 change _ = ∑ i:Fin a,w i*M i j
 apply Finset.sum_congr rfl
 intro i _
 rw [mul_assoc,hscale i j,← mul_assoc,div_mul_cancel₀ _ (hC i)]
end
end bAj
end
section
namespace cj
open vF
open scoped BigOperators
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem bGN (w s :ℕ) (v :Fin w→Ground) :
    ∃ c:Fin w→Ground,∀ j:Fin w,
      (∑ i:Fin w,c i*((s+j.val).choose i.val :Ground))=v j:= by
  induction w with
  | zero=>exact ⟨Fin.elim0,fun j=>j.elim0⟩
  | succ w ih =>
    obtain ⟨a,ha⟩:=ih (fun j=>v j.succ - v j.castSucc)
    let c:Fin (w+1)→Ground :=
      Fin.cases (v 0 - ∑ i:Fin w,a i*(s.choose (i.val+1) :Ground)) a
    refine ⟨c,?_⟩
    let ev (j:Fin (w+1)) :=
      ∑ i:Fin (w+1),c i*((s+j.val).choose i.val :Ground)
    change ∀ j,ev j=v j
    have step (j:Fin w) :ev j.succ-ev j.castSucc=v j.succ - v j.castSucc:= by
      rw [← ha j]
      dsimp only [ev]
      rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
      simp only [Fin.val_zero,Nat.choose_zero_right,Nat.cast_one,mul_one,
        add_sub_add_left_eq_sub,← Finset.sum_sub_distrib,Fin.val_succ,Fin.val_castSucc,
        ← Nat.add_assoc,Nat.choose_succ_succ,Nat.cast_add,mul_add,c,Fin.cases_succ]
      apply Finset.sum_congr rfl
      intro i _
      abel
    intro j
    induction j using Fin.induction with
    | zero =>
      dsimp only [ev]
      rw [Fin.sum_univ_succ]
      simp [c]
    | succ j hj =>
      have h:=step j
      rw [hj] at h
      exact sub_left_injective h
end cj
end
section
namespace cj
open vF

open scoped BigOperators
noncomputable section
private def exp (a b c f :ℕ) :Exponent :=
 Finsupp.equivFunOnFinite.symm ![a,b,c,f]
end
end cj
end
