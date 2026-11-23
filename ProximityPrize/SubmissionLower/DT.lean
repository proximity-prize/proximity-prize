import ProximityPrize.SubmissionLower.AR
set_option Elab.async false
set_option autoImplicit true
section
namespace Rw
noncomputable section
open xE (UT)
open gW (Dj)
open PolynomialDifferential ReedSolomon.HiddenDerivative Finset
abbrev qB:=Σ _:ℕ,Σ _:ℕ,Σ _:ℕ,Σ _:ℕ,ℕ
private def exponent:qB→UT
 | ⟨f,c,b,a,x⟩=>Finsupp.equivFunOnFinite.symm (fun v=>v.elim x ![a,b,c,f])
private def aD (e :UT) :qB :=
 ⟨e (some 3),e (some 2),e (some 1),e (some 0),e none⟩
private def equiv :qB ≃ UT where
 toFun:=exponent
 invFun:=aD
 left_inv := by rintro ⟨f,c,b,a,x⟩; simp [aD,exponent]
 right_inv := by
  intro e
  ext v
  cases v with
  | none=>simp [aD,exponent]
  | some j=>fin_cases j <;> simp [aD,exponent]
def cap (q:ℕ) :ℕ:=if q<3400 then 1650 else Dj q
def arF:qB→Prop
 | ⟨f,c,b,a,_⟩=>b+c+f≤ cap (a+b+c+f)
instance (t:qB) :Decidable (arF t) := by
 rcases t with ⟨f,c,b,a,x⟩
 unfold arF
 infer_instance
end
end Rw
end
section
namespace Rw
open Finset
open scoped BigOperators
theorem amJ (k :ℤ) (g p:ℤ→ℤ)
   (base :p 0=0) (step : ∀ t,p (t+1)=p t+k*g t) (n:ℕ) :
   k*(∑ i∈range n,g i)=p n:= by
 induction n with
 | zero=>simpa using base.symm
 | succ n ih=>rw [sum_range_succ,Nat.cast_succ,mul_add,ih,step]
theorem bKe (g:ℕ→ℤ) (p:ℤ→ℤ) (N :ℕ) (base :p 0=0)
   (step : ∀ q:ℕ,q<N→p (q+1)=p q+120*(g (2*q)+g (2*q+1)))
   (n:ℕ) (hn:n≤N) :120*(∑ f∈range (2*n),g f)=p n:= by
 induction n with
 | zero=>simpa using base.symm
 | succ n ih =>
   have hindex :2*(n+1)=(2*n+1)+1 := by omega
   have hcast: ((n+1 :ℕ) :ℤ)=(n:ℤ)+1 :=Nat.cast_succ n
   rw [hindex,sum_range_succ,sum_range_succ,add_assoc,
     mul_add,ih (by omega),hcast,step n (by omega)]
end Rw
end
