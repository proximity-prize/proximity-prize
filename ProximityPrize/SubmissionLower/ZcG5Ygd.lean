import ProximityPrize.SubmissionLower.AS
import ProximityPrize.SubmissionLower.ZzNTDEa
set_option Elab.async false
open _root_ renaming MvPolynomial.X → z9v, Submodule.add_mem → zcy
set_option autoImplicit true
namespace dnZ
open aiW MvPolynomial
open P1_6_1_3 (Target adjacentProduct)
open ank (J5)
open P1_6_1_3_2 (adjacent)
open fP (m9)
open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
abbrev F:=ZMod P1.p
abbrev Exp:=Fin 4 →₀ ℕ
abbrev Poly :=MvPolynomial (Fin 4) F
def keep (v :ℕ) {q:ℕ} (e :Target q) :Prop :=
  e.val 0≤15∧e.val.weight m9<v
instance (v q:ℕ) :DecidablePred (keep v (q:=q)) := fun e =>
  inferInstanceAs (Decidable (e.val 0≤15∧e.val.weight m9<v))
private def prefixSum:Fin 4→Poly :=
  ![z9v 1+MvPolynomial.X 2+MvPolynomial.X 3+MvPolynomial.X 0,
    z9v 1,z9v 1+MvPolynomial.X 2,
    z9v 1+MvPolynomial.X 2+MvPolynomial.X 3]
private theorem prefixSum_weight (i:Fin 4) :
    prefixSum i∈restrictWeightAtMost m9 (m9 i) := by
  have hx (j:Fin 4) (n:ℕ) (h:m9 j≤n) :
      (z9v j:Poly)∈restrictWeightAtMost m9 n :=
    X_mem_restrictWeightAtMost _ _ h
  fin_cases i
  · exact zcy _ (zcy _ (zcy _
      (hx 1 3 (by decide)) (hx 2 3 (by decide))) (hx 3 3 (by decide))) (hx 0 3 (by decide))
  · exact hx 1 0 (by decide)
  · exact zcy _ (hx 1 1 (by decide)) (hx 2 1 (by decide))
  · exact zcy _ (zcy _
      (hx 1 2 (by decide)) (hx 2 2 (by decide))) (hx 3 2 (by decide))
private theorem prefixSum_homogeneous (i:Fin 4) :
    (prefixSum i).IsWeightedHomogeneous (fun _=>(1 :ℕ)) 1 := by
  let hx :=isWeightedHomogeneous_X F (fun _:Fin 4=>(1 :ℕ))
  fin_cases i
  · exact (((hx 1).add (hx 2)).add (hx 3)).add (hx 0)
  · exact hx 1
  · exact (hx 1).add (hx 2)
  · exact ((hx 1).add (hx 2)).add (hx 3)
private theorem prefix_support (e d:Exp)
    (hd:d∈(bind₁ prefixSum (monomial e (1 :F))).support) :
    d.degree=e.degree∧d.weight m9≤e.weight m9:= by
  constructor
  · simp only [Finsupp.degree_eq_weight_one]
    have he :=isWeightedHomogeneous_monomial (fun _:Fin 4=>(1 :ℕ)) e (1 :F) rfl
    exact (he.bind₁ prefixSum_homogeneous) (MvPolynomial.mem_support_iff.mp hd)
  · have he :monomial e (1 :F)∈restrictWeightAtMost m9 (e.weight m9) :=
      (monomial_mem_restrictWeightAtMost _ _ _ _).mpr (Or.inl le_rfl)
    exact mem_restrictWeightAtMost.mp
      (bind₁_mem_restrictWeightAtMost prefixSum_weight he) d hd
private theorem a1D (f :Fin 4→Poly) (e :Exp) (r :F) :
    bind₁ f (monomial e r)=r•(f 0^e 0*f 1^e 1*f 2^e 2*f 3^e 3) := by
  rw [bind₁_monomial]
  change C r*e.prod (fun i n=>f i^n)= _
  rw [Finsupp.prod_fintype _ _ (fun _=>pow_zero _),Fin.prod_univ_four,smul_eq_C_mul]
private theorem bind_prefix (e :Exp) :
    bind₁ adjacent (bind₁ prefixSum (monomial e (1 :F)))=J5 e := by
  have h0:bind₁ adjacent (prefixSum 0)=z9v 0:= by
    simp [prefixSum,adjacent]
  have h1 :bind₁ adjacent (prefixSum 1)=z9v 0+MvPolynomial.X 1 := by
    simp [prefixSum,adjacent]
  have h2 :bind₁ adjacent (prefixSum 2)=z9v 0+MvPolynomial.X 2 := by
    simp [prefixSum,adjacent]
  have h3:bind₁ adjacent (prefixSum 3)=z9v 0+MvPolynomial.X 3:= by
    simp [prefixSum,adjacent]
  simp only [a1D,one_smul,map_mul,map_pow,h0,h1,h2,h3,J5]
private theorem adjacent_coeff_zero (d m:Exp) (h:m 3<d 0) :
    (adjacentProduct d).coeff m=0:= by
  have hn : ¬Finsupp.single (3:Fin 4) (d 0)≤ m:= by
    rw [Finsupp.single_le_iff]
    exact not_le_of_gt h
  unfold adjacentProduct
  rw [show -(MvPolynomial.X 3:Poly)=(-1 :Poly)*MvPolynomial.X 3 by simp,
    mul_pow,← mul_assoc,X_pow_eq_monomial,coeff_mul_monomial',ite_eq_right hn]
end
end dnZ
