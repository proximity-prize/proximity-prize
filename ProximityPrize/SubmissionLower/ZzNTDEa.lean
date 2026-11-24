import ProximityPrize.SubmissionLower.Z4WdLEc
set_option Elab.async false
open _root_ renaming Matrix.cons_val_one → z87, Matrix.cons_val_three → z7s, Matrix.cons_val_two → zrz, Matrix.cons_val_zero → zbs, MvPolynomial.X → z9v, Submodule.sub_mem → zMG
set_option autoImplicit true
namespace P1_6_1_3_2
noncomputable section
open MvPolynomial
open fP (lP m9 xH oG)
open scoped BigOperators
abbrev Exp:=Fin 4 →₀ ℕ
abbrev Poly (R:Type*) [CommRing R] :=MvPolynomial (Fin 4) R
variable {R:Type*} [CommRing R]
def adjacent:Fin 4→Poly R :=
  ![-MvPolynomial.X 3,z9v 0+MvPolynomial.X 1,z9v 2 - z9v 1,z9v 3-MvPolynomial.X 2]
def original :Fin 4→Poly R :=
  ![z9v 1+MvPolynomial.X 2+MvPolynomial.X 3+MvPolynomial.X 0,-MvPolynomial.X 2 - z9v 3-MvPolynomial.X 0,-MvPolynomial.X 3-MvPolynomial.X 0,-MvPolynomial.X 0]
theorem bind_original (P:Poly R) :
    bind₁ adjacent (bind₁ original P)=P:= by
  rw [bind₁_bind₁]
  have h: (fun i=>bind₁ adjacent (original i:Poly R))=MvPolynomial.X:= by
    funext i
    fin_cases i <;> simp [original,adjacent]
  rw [h,bind₁_X_left]
  rfl
theorem original_homogeneous {m:Exp} :
    (bind₁ original (monomial m (1 :R))).IsWeightedHomogeneous
      (fun _=>(1 :ℕ)) m.degree := by
  apply IsWeightedHomogeneous.bind₁ (w:= fun _:Fin 4=>(1 :ℕ)) _
    (isWeightedHomogeneous_monomial _ m (1 :R) (by rw [← Finsupp.degree_eq_weight_one]))
  intro i
  let h:=isWeightedHomogeneous_X R (fun _:Fin 4=>(1 :ℕ))
  fin_cases i
  · exact (((h 1).add (h 2)).add (h 3)).add (h 0)
  · exact (((h 2).neg).sub (h 3)).sub (h 0)
  · exact (h 3).neg.sub (h 0)
  · exact (h 0).neg
theorem bind_adjacent_monomial (e :Exp) (a :R) :
    bind₁ adjacent (monomial e a) =
      a•((z9v 0+MvPolynomial.X 1)^e 1*(z9v 2 - z9v 1)^e 2 *
        (z9v 3-MvPolynomial.X 2)^e 3*(-MvPolynomial.X 3)^e 0:Poly R) := by
  rw [bind₁_monomial,← Finsupp.prod,Finsupp.prod_fintype _ _ (fun _=>pow_zero _),
    Fin.prod_univ_four,← smul_eq_C_mul]
  simp only [adjacent,zbs,z87,zrz,
    z7s,Matrix.head_cons,Matrix.tail_cons]
  ac_rfl
theorem adjacent_order (e :Exp) :
    bind₁ adjacent (monomial e (1 :R))∈restrictWeightedOrder lP
      (e.weight m9) := by
  apply bind₁_mem_restrictWeightedOrder (w:=m9)
  · let h (i:Fin 4) {w:ℕ} (hi:w≤lP i) :=
      X_mem_restrictWeightedOrder (R:=R) lP i hi
    intro i
    fin_cases i
    · exact Submodule.neg_mem _ (h 3 (by decide))
    · exact Submodule.add_mem _ (h 0 (by decide)) (h 1 (by decide))
    · exact zMG _ (h 2 (by decide)) (h 1 (by decide))
    · exact zMG _ (h 3 (by decide)) (h 2 (by decide))
  · exact (monomial_mem_restrictWeightedOrder _ _ _ _).mpr (Or.inl le_rfl)
private def JE :Derivation R (Poly R) (Poly R) :=
  (z9v 1 :Poly R)•pderiv 1+(2•z9v 2 :Poly R)•pderiv 2 +
    (3•z9v 3:Poly R)•pderiv 3 -
    (z9v 1 :Poly R)•pderiv 0-(z9v 2 :Poly R)•pderiv 0 -
    (z9v 3:Poly R)•pderiv 0+(z9v 2 :Poly R)•pderiv 1 +
    (z9v 3:Poly R)•pderiv 1+(z9v 3:Poly R)•pderiv 2
private theorem euler_adjacent (i:Fin 4) :
    JE (adjacent i:Poly R)=(m9 i:R)•adjacent i:= by
  fin_cases i <;>
    simp [adjacent,m9,JE,Derivation.sub_apply,smul_eq_mul,smul_eq_C_mul,
      _root_.map_ofNat] <;> ring
private theorem aUk {P Q:Poly R} {a b:ℕ}
    (hp:JE P=(a :R)•P) (hq:JE Q=(b:R)•Q) :
    JE (P*Q)=((a+b:ℕ) :R)•(P*Q) := by
  rw [Derivation.leibniz,hp,hq]
  simp only [Nat.cast_add,smul_eq_mul]
  simp only [← C_mul',map_add]
  ring
private theorem a3B {P:Poly R} {a :ℕ} (hp:JE P=(a :R)•P) (n:ℕ) :
    JE (P^n)=((n*a :ℕ) :R)•P^n:= by
  induction n with
  | zero=>simp
  | succ n ih=>rw [pow_succ,Nat.succ_mul]; exact aUk ih hp
private theorem euler_bind_adjacent (e :Exp) (a :R) :
    JE (bind₁ adjacent (monomial e a)) =
      (((e.weight m9:ℕ) :R)*a)•bind₁ adjacent (monomial e 1) := by
  simp only [bind_adjacent_monomial,one_smul,Derivation.map_smul]
  have h:=aUk (aUk (aUk (a3B (euler_adjacent (R:=R) 1) (e 1))
    (a3B (euler_adjacent (R:=R) 2) (e 2)))
    (a3B (euler_adjacent (R:=R) 3) (e 3)))
    (a3B (euler_adjacent (R:=R) 0) (e 0))
  simp only [adjacent,zbs,z87,zrz,
    z7s,Matrix.head_cons,Matrix.tail_cons] at h
  rw [h,smul_smul,mul_comm a]
  have hw:e 1*m9 1+e 2*m9 2+e 3*m9 3 +
      e 0*m9 0=e.weight m9:= by
    rw [oG]
    change e 1*0+e 2*1+e 3*2+e 0*3=3*e 0+e 2+2*e 3
    omega
  rw [hw]
def shell (P:Poly R) :Poly R:=JE P-(49:R)•P
theorem shell_bind_adjacent (e :Exp) (a :R) :
    shell (bind₁ adjacent (monomial e a)) =
      ((((e.weight m9:ℕ) :R)-49)*a)•bind₁ adjacent (monomial e 1) := by
  have h:bind₁ adjacent (monomial e a)=a•bind₁ adjacent (monomial e 1) := by
    simp only [bind_adjacent_monomial,one_smul]
  rw [shell,euler_bind_adjacent]
  nth_rw 1 [h]
  rw [smul_smul,← sub_smul,sub_mul]
private theorem coeff_raise (e m:Exp) (i j:Fin 4) (hij:i<j)
    (h:m.weight lP≤e.weight lP∨e.weight lP+3< m.weight lP) :
    ((z9v j:Poly R)*pderiv i (monomial e 1)).coeff m=0:= by
  rw [pderiv_monomial]
  by_cases hi:e i=0
  · simp [hi]
  rw [z9v,monomial_mul_monomial,coeff_monomial,ite_eq_right_iff]
  intro he
  have hw:=congrArg (Finsupp.weight lP) he
  rw [map_add,Finsupp.weight_single,one_smul] at hw
  have hew:=Finsupp.weight_sub_single_add (w:=lP) hi
  have hj:=j.isLt
  change i.val<j.val at hij
  change j.val+(e-Finsupp.single i 1).weight lP=m.weight lP at hw
  change (e-Finsupp.single i 1).weight lP+i.val=e.weight lP at hew
  omega
theorem shell_coeff (e m:Exp)
    (h:m.weight lP≤e.weight lP∨e.weight lP+3< m.weight lP) :
    (shell (monomial e (1 :R))).coeff m =
      if e=m then (e.weight lP:R)-49 else 0:= by
  have hn (j:Fin 4) (n:ℕ) :
      (n•(z9v j:Poly R))*pderiv j (monomial e 1) =
        n•(e j•monomial e (1 :R)) := by
    simp only [nsmul_eq_mul,mul_assoc,X_mul_pderiv_monomial]
  change (lcoeff R m) (shell (monomial e 1))= _
  simp only [shell,JE,Derivation.add_apply,Derivation.sub_apply,Derivation.smul_apply,
    smul_eq_mul,hn,X_mul_pderiv_monomial,map_add,map_sub,map_nsmul,map_smul]
  simp only [lcoeff_apply]
  rw [coeff_raise e m 0 1 (by decide) h,coeff_raise e m 0 2 (by decide) h,
    coeff_raise e m 0 3 (by decide) h,coeff_raise e m 1 2 (by decide) h,
    coeff_raise e m 1 3 (by decide) h,coeff_raise e m 2 3 (by decide) h]
  by_cases he :e=m
  · simp [coeff_monomial,he,xH,Nat.cast_add,Nat.cast_mul,nsmul_eq_mul]
  · simp [coeff_monomial,he]
end
end P1_6_1_3_2
