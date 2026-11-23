import ProximityPrize.SubmissionLower.D6
import ProximityPrize.SubmissionLower.ZL8vffb
set_option Elab.async false
set_option autoImplicit true
namespace P5_7_4
noncomputable section
open P5 (p)

open cu (Shape vP Jet FX triangle ku A5)
open gT (alm)

open Polynomial Finset


open private eligible boi bDM from ProximityPrize.SubmissionLower.D6
private theorem ee7 (h r :ℕ) (s :Shape) :
  O3 h r s 1≤O3 h r s 0:= by
 unfold O3 ku
 simp only [zero_mul,Nat.sub_zero]
 exact Nat.mul_le_mul_left _ (sum_le_sum fun _ _=>sum_le_sum fun _ _=>Nat.sub_le _ _)
private theorem eHt (h N W:ℕ) (hh:0<h) (hW:W<N)
   {G P R:Jet} (hi:Irreducible G) (hv :0<G.natDegree)
   (hm:alm G) (hP:P≠0) (hdiv :G∣P) {U:ℕ} (hp:U<p)
   (hseed : ∀ j i,((P.coeff j).coeff i).totalDegree≤U) (hnR:R≠0)
   (commonShift : ∀ (i:Fin 2) a,W+2*h*a≤N-1→G∣A5 i a R) :
   N≤W+2*h*R.natDegree := by
 let e :=1+(N - 1-W)/(2*h)
 have hpower :G^e∣R :=
   bjF.proof G P R U e hi hv hm hP hdiv hp hseed (by
     intro i a ha
     have hle :a≤(N - 1-W)/(2*h) := by dsimp [e] at ha; omega
     have ht:=(Nat.le_div_iff_mul_le (by omega :0<2*h)).mp hle
     rw [Nat.mul_comm a] at ht
     exact commonShift i a (by omega))
 have hdegree :=Polynomial.natDegree_le_of_dvd hpower hnR
 rw [Polynomial.natDegree_pow] at hdegree
 have he :e≤R.natDegree :=(Nat.le_mul_of_pos_right e hv).trans hdegree
 have hdiv' : (N - 1-W)/(2*h)<R.natDegree := by dsimp [e] at he; omega
 have ht:=(Nat.div_lt_iff_lt_mul (by omega :0<2*h)).mp hdiv'
 rw [Nat.mul_comm R.natDegree] at ht
 omega
private theorem eD6 (rows :vP) (s :Shape) (h r :ℕ)
    (hk :1≤131071-h)
    (hcaps : ∀ W,∀ P∈rows s W,qQ.oU P s)
    (hlead:qQ.aSa h rows s)
    (horder : ∀ W<Mq h r s,∀ P∈rows s W,P≠0 →
      Mq h r s≤W+2*h*P.natDegree) :
    (∑ W∈range (Mq h r s),Module.finrank FX (rows s W))+O3 h r s 1 ≤
      O3 h r s 0:= by
  let N :=Mq h r s
  have hsum: (∑ W∈range N,Module.finrank FX (rows s W)) ≤
      triangle s.U*(∑ W∈range N,ku s (fun q j =>
        if eligible h N W q j then 1 else 0)) := by
    rw [mul_sum]
    exact sum_le_sum (fun W hW =>
      boi s h N W _ (hcaps W) (hlead W) (horder W (mem_range.mp hW)))
  have heq :=congrArg (triangle s.U * ·) (bDM s h N hk)
  rw [Nat.mul_add] at heq
  unfold O3 amv
  simp only [one_mul,zero_mul,Nat.sub_zero]
  exact (Nat.add_le_add_right hsum _).trans_eq heq
end
end P5_7_4
