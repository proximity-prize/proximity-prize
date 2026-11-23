import ProximityPrize.SubmissionLower.Z0omYcd
import ProximityPrize.SubmissionLower.ZYswgKc
set_option Elab.async false
open _root_ renaming Fin.prod_univ_four → zE3, Fin.sum_univ_four → zmL, Finsupp.finite_of_degree_le → z30, Finsupp.prod_fintype → z6B, MvPolynomial.X → z9v
set_option maxHeartbeats 1000000
set_option autoImplicit true
section
namespace aiW
noncomputable section

open fP (Ew m9)
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
def asu (q:ℕ) :ℕ :=
 if q≤101 then 50 else
 if q≤113 then 49 - 2*((q - 102)/2) else 36 - 2*((q - 114)/2)
def iO (q:ℕ) :ℕ:=min q (asu q)
def Vm (q:ℕ) (g:ℤ) :ℤ:=90-(q:ℤ) - g
abbrev XN (q:ℕ) (g:ℤ) :=
 {m:Fin 4 →₀ ℕ // Ew (iO q) (-g) 50 15 m}
abbrev ait (q:ℕ) (g:ℤ) :=
 {m:Fin 4 →₀ ℕ // m.degree=iO q ∧
   m.weight m9<(Vm q g).toNat}
instance gOZ (q:ℕ) (g:ℤ) :Finite (XN q g) :=
 ((z30 _).subset fun _ (h:Ew _ _ _ _ _) =>
   Nat.le_of_eq h.1).to_subtype
instance gO1 (q:ℕ) (g:ℤ) :Finite (ait q g) :=
 ((z30 _).subset fun _ (h:_∧_) =>
   Nat.le_of_eq h.1).to_subtype
noncomputable instance gO0 (q:ℕ) (g:ℤ) :Fintype (XN q g) :=
 Fintype.ofFinite _
noncomputable instance gO2 (q:ℕ) (g:ℤ) :Fintype (ait q g) :=
 Fintype.ofFinite _
end
end aiW
end
section
namespace aiW
open aR MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open fP (Form lP m9 L4)
open scoped BigOperators
noncomputable section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
private abbrev Local:=LocalPolynomial ao 3
private abbrev T:Local:=z9v (localT 3)
private def brP (j:Fin 4) :LocalVariable 3 := ![localE 3,localY 0,localY 1,localY 2] j
private def be8 (j:Fin 4) :ℕ:=if j=0 then 1 else j.val
private def a5k (j:Fin 4) :Local:=T^be8 j*z9v (brP j)
private def aDF:Form →ₐ[ao] Local:=bind₁ a5k
private theorem bIp (j:Fin 4) :aDF (z9v j)=a5k j:=bind₁_X_right _ _
private theorem cXS :
  aDF L4=unscaledLocalSubstitution 3 0 0 (z9v (some 0)) := by
 rw [unscaledLocalSubstitution_Y_zero]
 simp only [L4,map_add,map_sub,bIp,localCorrection,Fin.sum_univ_three]
 simp [a5k,be8,brP]
 ring
private theorem aIu (j:Fin 4) :
   a5k j∈restrictWeightedOrder (localContactWeight 3) (1+m9 j) := by
 have h:be8 j*1+localContactWeight 3 (brP j)=1+m9 j:= by
   fin_cases j <;> decide
 rw [← h]
 exact mul_mem_restrictWeightedOrder
   (pow_mem_restrictWeightedOrder (X_mem_restrictWeightedOrder _ _ (localContactWeight_T 3).ge)
     (be8 j))
   (X_mem_restrictWeightedOrder _ _ le_rfl)
private theorem djp :
  L4.IsWeightedHomogeneous (fun _=>(1 :ℕ)) 1 := by
 let h:=isWeightedHomogeneous_X ao (fun _:Fin 4=>(1 :ℕ))
 exact (((h 0).add (h 1)).sub (h 2)).add (h 3)
private theorem cXT :
  aDF L4∈restrictWeightedOrder (localContactWeight 3) 1 := by
 have h (j:Fin 4) :
    a5k j∈restrictWeightedOrder (localContactWeight 3) 1 :=
  restrictWeightedOrder_anti _ (Nat.le_add_right 1 (m9 j)) (aIu j)
 simpa only [L4,map_add,map_sub,bIp] using
  (add_mem (sub_mem (add_mem (h 0) (h 1)) (h 2)) (h 3))
private def postprocess (s :ℕ) (g:ℤ) :Form →ₗ[ao] Local :=
 (projectLowContact 140).comp
   ((LinearMap.mulLeft ao (T^(g+50).toNat *
     (aDF L4)^(s - iO s))).comp aDF.toLinearMap)
private theorem aWA (cut:ℕ) (e :LocalVariable 3 →₀ ℕ) (a :ao) :
   projectLowContact cut (monomial e a) =
     if localContactOrder 3 e<cut then monomial e a else 0:= by
 classical
 by_cases hc:localContactOrder 3 e<cut
 · rw [ite_eq_left hc]
   ext v
   by_cases h:e=v
   · subst v
     simp [coeff_projectLowContact,hc]
   · simp [coeff_projectLowContact,coeff_monomial,h]
 · rw [ite_eq_right hc]
   ext v
   by_cases h:e=v
   · subst v
     simp [coeff_projectLowContact,hc]
   · simp [coeff_projectLowContact,coeff_monomial,h]
private theorem bH2 (m:Fin 4 →₀ ℕ) :
  m.weight lP=m 1+2*m 2 + 3*m 3:= by
 simp [Finsupp.weight_eq_sum,zmL,lP,Nat.mul_comm]
private theorem deP (u:JetVariable 3 →₀ ℕ) (a :ao) :
   monomial u a=MvPolynomial.C a*z9v none^u none *
     z9v (some 0)^u (some 0)*z9v (some 1)^u (some 1) *
     z9v (some 2)^u (some 2)*z9v (some 3)^u (some 3) := by
 rw [monomial_eq,z6B _ _ (fun _=>pow_zero _),Fintype.prod_option]
 change _ *(_ * ∏ i:Fin 4,z9v (some i)^u (some i))= _
 rw [zE3]
 ring
private theorem cSR (m:Fin 4 →₀ ℕ) (a :ao) :
   monomial m a=MvPolynomial.C a*z9v 0^m 0*z9v 1^m 1 *
     z9v 2^m 2*z9v 3^m 3:= by
 rw [monomial_eq,z6B _ _ (fun _=>pow_zero _),zE3]
 ring
private def merge {ι:Type} [Fintype ι] {V:ι→Submodule ao Form}
   (post:ι→Form →ₗ[ao] Local) : (∀ i,V i) →ₗ[ao] Local :=
 ∑ i,(post i).comp ((V i).subtype.comp (LinearMap.proj i))
private theorem c0l {ι:Type} [Fintype ι] [DecidableEq ι]
   {V:ι→Submodule ao Form} (post:ι→Form →ₗ[ao] Local) (i:ι) (v :V i) :
   merge post (Pi.single i v)=post i v := by
 rw [merge,LinearMap.sum_apply,Finset.sum_eq_single i]
 · simp
 · intro j _ hj
   have hj' : (Pi.single i v : (k :ι)→V k) j=0 :=
     Pi.single_eq_of_ne (M:= fun k => ↥(V k)) hj v
   simp [hj']
 · simp
end
end aiW
end
section
namespace aiW
open aR fP MvPolynomial
open scoped BigOperators
noncomputable section
private def UD (m:Fin 4 →₀ ℕ) :Fin 4 →₀ ℕ :=
 Finsupp.equivFunOnFinite.symm ![0,m 1,m 2,m 3]
@[simp] private theorem gR0 (m:Fin 4 →₀ ℕ) (j:Fin 4) :
   UD m j = ![0,m 1,m 2,m 3] j:= by simp [UD]
private theorem c0O (m:Fin 4 →₀ ℕ) :
   (monomial m 1 :Form)=z9v 0^m 0*z9v 1^m 1 *
     z9v 2^m 2*z9v 3^m 3:= by
 rw [monic_monomial_eq,z6B _ _ (fun _=>pow_zero _),zE3]
private theorem cCH (m:Fin 4 →₀ ℕ) :
  Jx (monomial m 1)=L4^m 0*monomial (UD m) 1 := by
 rw [c0O m,c0O (UD m)]
 simp [a1u 1 (by decide),a1u 2 (by decide),
  a1u 3 (by decide),mul_assoc]
private theorem cGq (d:Fin 4 →₀ ℕ) (n:ℕ) (h:d.degree=n) :
   (L4^n).coeff d=(d.multinomial:ao)*(-1 :ao)^d 2 := by
 have hv :L4 =
     ∑ j:Fin 4,(![1,1,-1,1] :Fin 4→ao) j•z9v j:= by
   simp [L4,zmL,sub_eq_add_neg,add_assoc]
 rw [hv,coeff_linearCombination_X_pow_of_fintype]
 change (if d.degree=n then _ else _)= _
 rw [ite_eq_left h,z6B _ _ (fun _=>pow_zero _),zE3]
 simp
private def aNJ (d:Fin 4 →₀ ℕ) :ao :=
 ∏ j:Fin 4,((d j).factorial:ao)
private theorem c07 (d:Fin 4 →₀ ℕ) :
  (d.multinomial:ao)*aNJ d=(d.degree.factorial:ao) := by
 have h:=congrArg (fun k :ℕ=>(k :ao)) (Nat.multinomial_spec Finset.univ d)
 rw [Nat.cast_mul,Nat.cast_prod,← Finsupp.multinomial_eq_of_support_subset
  (Finset.subset_univ d.support),← Finsupp.degree_eq_sum,mul_comm] at h
 exact h
private theorem cFA {n k :ℕ} (h:k≤n) :
  (n.choose k :ao)*(k.factorial:ao)*((n - k).factorial:ao) =
    (n.factorial:ao) := by
 simpa only [Nat.cast_mul] using
  congrArg (fun a :ℕ=>(a :ao)) (Nat.choose_mul_factorial_mul_factorial h)
end
end aiW
end
section
namespace aiW
def aOx (t c order :ℕ) :ℕ :=
 min (t+1) (order-(2*t+c))
open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
end
end aiW
end
