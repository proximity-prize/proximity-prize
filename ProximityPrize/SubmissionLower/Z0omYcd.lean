import ProximityPrize.SubmissionLower.E7
import ProximityPrize.SubmissionLower.D6
import ProximityPrize.SubmissionLower.D9
import ProximityPrize.SubmissionLower.BJ
set_option Elab.async false
set_option autoImplicit true
section
namespace bR9
open scoped BigOperators
set_option maxHeartbeats 600000
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private abbrev F:=ZMod P1.p
private theorem c6L {ι κ:Type*} [Fintype ι] [Fintype κ]
  {ρ:ι→Type*} (M:Matrix (Sigma ρ) κ F) :
  M.rank ≤ ∑ i:ι,(M.submatrix (Sigma.mk i) id).rank := by
 let qv (i:ι) :=(M.submatrix (Sigma.mk i) id).mulVecLin
 let curry :=LinearEquiv.piCurry F (fun (i:ι) (_:ρ i)=>F)
 have he :LinearMap.pi qv=curry.toLinearMap.comp M.mulVecLin:= by
  ext x i j
  rfl
 have h:=LinearMap.finrank_range_pi_le_sum qv
 rw [he,LinearMap.range_comp,LinearEquiv.finrank_map_eq] at h
 exact h
end
end bR9
end
section
namespace ank
open MvPolynomial
open fP (cF)
open private rU OZ from ProximityPrize.SubmissionLower.BI
open scoped BigOperators
noncomputable section
local notation "F" => ZMod P1.p
local notation "Poly" => MvPolynomial (Fin 4) F
local notation "Exp" => (Fin 4 →₀ ℕ)
def J5 (e :Exp) :Poly :=
  MvPolynomial.X 0^e 0*(MvPolynomial.X 0+MvPolynomial.X 1)^e 1 *
    (MvPolynomial.X 0+MvPolynomial.X 2)^e 2*(MvPolynomial.X 0+MvPolynomial.X 3)^e 3
private def bVC (i:Fin 4) (n k :ℕ) :Poly :=
 monomial (Finsupp.single i k+Finsupp.single 0 (n - k)) (n.choose k :F)
private theorem dy6 (i:Fin 4) (n:ℕ) :
   ((MvPolynomial.X 0+MvPolynomial.X i)^n:Poly) =
     ∑ k∈Finset.range (n+1),bVC i n k := by
 rw [add_comm,add_pow]
 apply Finset.sum_congr rfl
 intro k _
 have hcast: (n.choose k :Poly)=C (n.choose k :F) :=
   (map_natCast (C:F →+* Poly) (n.choose k)).symm
 rw [bVC,hcast,mul_comm _ (C _),← smul_eq_C_mul,
   X_pow_eq_monomial,X_pow_eq_monomial,monomial_mul_monomial,mul_one,
   smul_monomial,smul_eq_mul,mul_one]
private def byx (e :Exp) :Finset (ℕ×ℕ×ℕ) :=
 Finset.range (e 1+1) ×ˢ (Finset.range (e 2+1) ×ˢ Finset.range (e 3+1))
private def bhT (e :Exp) (k :ℕ×ℕ×ℕ) :Exp :=
 rU (e 0+(e 1 - k.1)+(e 2 - k.2.1)+(e 3 - k.2.2)) k.1 k.2.1 k.2.2
private def bxC (e :Exp) (k :ℕ×ℕ×ℕ) :F :=
 ((e 1).choose k.1 :F)*((e 2).choose k.2.1 :F)*((e 3).choose k.2.2 :F)
private theorem fT0 (e :Exp) :
  J5 e = ∑ k∈byx e,monomial (bhT e k) (bxC e k) := by
 unfold J5 byx
 simp only [dy6,Finset.sum_product]
 rw [Finset.mul_sum (Finset.range (e 1+1)),Finset.sum_mul,Finset.sum_mul]
 refine Finset.sum_congr rfl fun i _ => ?_
 rw [Finset.mul_sum (Finset.range (e 2+1)),Finset.sum_mul]
 refine Finset.sum_congr rfl fun j _ => ?_
 rw [Finset.mul_sum]
 refine Finset.sum_congr rfl fun k _ => ?_
 simp only [bVC,X_pow_eq_monomial,monomial_mul_monomial,one_mul]
 apply congrArg (fun d:Exp=>monomial d (bxC e (i,j,k)))
 ext z
 fin_cases z <;> simp [bhT]
theorem ao9 (e m:Exp) (hdeg:e.degree=m.degree) :
    (J5 e).coeff m =
      ((e 1).choose (m 1) :F)*((e 2).choose (m 2) :F)*((e 3).choose (m 3) :F) := by
  classical
  let k :ℕ×ℕ×ℕ:=(m 1,m 2,m 3)
  have hscalar :bxC e k =
      ((e 1).choose (m 1) :F)*((e 2).choose (m 2) :F)*((e 3).choose (m 3) :F) :=rfl
  rw [← hscalar,fT0,coeff_sum]
  have hmem (t:ℕ×ℕ×ℕ) :t∈byx e ↔
      t.1≤e 1∧t.2.1≤e 2∧t.2.2≤e 3:= by
    simp only [byx,Finset.mem_product,Finset.mem_range,Nat.lt_succ_iff]
  have hother (t:ℕ×ℕ×ℕ) (hne :t≠k) :bhT e t≠m:= by
    intro ht
    apply hne
    have h1 :=congrArg (fun d:Exp=>d 1) ht
    have h2 :=congrArg (fun d:Exp=>d 2) ht
    have h3:=congrArg (fun d:Exp=>d 3) ht
    simp only [bhT,OZ,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three] at h1 h2 h3
    exact Prod.ext h1 (Prod.ext h2 h3)
  by_cases hk :k∈byx e
  · rw [Finset.sum_eq_single_of_mem k hk
      (fun t _ hne=> by simp [coeff_monomial,hother t hne])]
    have ⟨h1,h2,h3⟩:=(hmem k).mp hk
    have heq :bhT e k=m:= by
      rw [cF,cF] at hdeg
      ext z
      fin_cases z <;> simp [bhT,k] at *
      omega
    simp [coeff_monomial,heq]
  · have hz :bxC e k=0:= by
      rw [hmem] at hk
      have hb:e 1< m 1∨e 2< m 2∨e 3< m 3:= by
        change ¬(m 1≤e 1∧m 2≤e 2∧m 3≤e 3) at hk
        omega
      rcases hb with h | h | h <;> simp [bxC,k,Nat.choose_eq_zero_of_lt h]
    rw [hz]
    refine Finset.sum_eq_zero fun t ht => ?_
    have hne :t≠k := fun h=>hk (h ▸ ht)
    simp [coeff_monomial,hother t hne]
end
end ank
end
section
namespace bR9
open fP (qI aAs aAr)
open scoped BigOperators
private def triangle (n:ℕ) :ℕ:=(n+1)*n/2
private theorem dh1 (n:ℕ) :triangle (n+1)=triangle n+(n+1) := by
 simpa only [triangle,Nat.add_sub_cancel] using Nat.triangle_succ (n+1)
private theorem dh0:Monotone triangle :=
 monotone_nat_of_le_succ fun n=> by rw [dh1]; omega
private theorem sum_congr (n:ℕ) {f h:ℕ→ℕ} (he : ∀ i,f i=h i) :
 qI n f=qI n h:=congrArg (qI n) (funext he)
private theorem sum_comm (n m:ℕ) (f :ℕ→ℕ→ℕ) :
  (qI n fun r=>qI m (f r))=qI m fun c=>qI n fun r=>f r c:= by
 simp only [aAs]
 exact Finset.sum_comm
private theorem bOz (n:ℕ) (f h:ℕ→ℕ) :
  (qI n fun i=>f i+h i)=qI n f+qI n h:= by
 simp only [aAs,Finset.sum_add_distrib]
private theorem sum_mono (n:ℕ) {f h:ℕ→ℕ} (he : ∀ i,f i≤h i) :
  qI n f≤qI n h:= by
 simp only [aAs]
 exact Finset.sum_le_sum fun i _=>he i
private theorem bxa (n x :ℕ) :
   (qI n fun r=>x - r)=triangle x - triangle (x - n) := by
 induction n generalizing x with
 | zero=>simp [qI]
 | succ n ih =>
   rw [show n+1=1+n by omega,aAr]
   rw [show (qI 1 fun r=>x - r)=x by change 0+(x - 0)=x; simp]
   cases x with
   | zero=>simp [aAs]
   | succ x =>
     simp only [Nat.succ_sub_succ_eq_sub,Nat.add_comm 1 n]
     rw [ih,dh1]
     have h:=dh0 (Nat.sub_le x n)
     omega
private theorem dfU (n k x :ℕ) (hx :x≤n) :
   (qI n fun r=>min k (x - r))=triangle x - triangle (x - k) := by
 have he : (qI n fun r=>min k (x - r))+(qI n fun r=>x - k - r) =
     qI n fun r=>x - r := by
   rw [← bOz]
   exact sum_congr _ fun r=> by omega
 rw [bxa,bxa,Nat.sub_eq_zero_of_le hx,
   Nat.sub_eq_zero_of_le ((Nat.sub_le x k).trans hx)] at he
 have hz :triangle 0=0:=rfl
 rw [hz] at he
 have h:=dh0 (Nat.sub_le x k)
 omega
end bR9
end
