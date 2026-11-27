import ArkLib.ToMathlib.RingTheory.MvPolynomial.Bidegree
import Mathlib.Tactic

set_option Elab.async false

-- Source: Research6969.ScaledBidegree
set_option autoImplicit true
namespace Research6969.ScaledBidegree
noncomputable section
open MvPolynomial Finset
open scoped BigOperators
variable {F:Type*} [Field F] (a b:ℕ)

private def triple (y x z:ℕ) : Option (Fin 2) →₀ ℕ :=
  (Finsupp.equivFunOnFinite.symm ![x,z]).optionElim y

private theorem degree_pair (m:Fin 2 →₀ ℕ) : m.degree=m 0+m 1 := by
  change m.sum (fun _ n=>n)=m 0+m 1
  rw [Finsupp.sum_fintype _ _ (fun _=>rfl),Fin.sum_univ_two]

@[simp] private theorem triple_none (y x z:ℕ) : triple y x z none=y := by
  simp [triple]
@[simp] private theorem triple_zero (y x z:ℕ) : triple y x z (some 0)=x := by
  simp [triple]
@[simp] private theorem triple_one (y x z:ℕ) : triple y x z (some 1)=z := by
  simp [triple]

private theorem triple_eta (m:Option (Fin 2) →₀ ℕ) :
    triple (m none) (m (some 0)) (m (some 1))=m := by
  ext i
  cases i with
  | none => simp
  | some i => fin_cases i <;> simp

private theorem lift_monomial (k y x z:ℕ) (hy:y≤a*k) (hz:x+z≤b*k) :
    ∃ Q:MvPolynomial (bidegreeExponents (Fin 2) a b) F, Q.totalDegree≤k ∧
      bidegreeMap (Fin 2) F a b Q=monomial (triple y x z) 1 := by
  classical
  induction k generalizing y x z with
  | zero =>
    simp only [Nat.mul_zero] at hy hz
    have : y=0 := by omega
    have : x=0 := by omega
    have : z=0 := by omega
    subst_vars
    have zero : triple 0 0 0=0 := (triple_eta (0:Option (Fin 2)→₀ℕ))
    exact ⟨1,by simp,by simp [zero]⟩
  | succ k ih =>
    rw [Nat.mul_succ] at hy hz
    let Y:=min y a
    let X₀:=min x b
    let Z:=min z (b-X₀)
    have yp : y-Y≤a*k := by dsimp [Y];omega
    have rest : (x-X₀)+(z-Z)≤b*k := by dsimp [X₀,Z] at *;omega
    obtain ⟨Q,bound,eq⟩:=ih (y-Y) (x-X₀) (z-Z) yp rest
    have fits : triple Y X₀ Z ∈ bidegreeExponents (Fin 2) a b := by
      rw [mem_bidegreeExponents,degree_pair]
      simp only [Finsupp.some_apply,triple_none,triple_zero,triple_one]
      dsimp [Y,Z,X₀];omega
    let slot : bidegreeExponents (Fin 2) a b := ⟨_,fits⟩
    have add : triple Y X₀ Z+triple (y-Y) (x-X₀) (z-Z)=triple y x z := by
      ext i
      cases i with
      | none => simp only [Finsupp.add_apply,triple_none];dsimp [Y];omega
      | some i =>
        fin_cases i
        · simp only [Finsupp.add_apply,Fin.zero_eta,triple_zero];dsimp [X₀];omega
        · simp only [Finsupp.add_apply,Fin.mk_one,triple_one];dsimp [Z];omega
    refine ⟨X slot*Q,(totalDegree_mul _ _).trans ?_,?_⟩
    · rw [totalDegree_X];omega
    · rw [map_mul,bidegreeMap_X,eq,monomial_mul_monomial,one_mul]
      exact congrArg (fun m=>monomial m (1:F)) add

/-- A test in the scaled bidegree rectangle has a total-degree-k lift in
the same fixed embedding, at every shortening order k. -/
theorem exists_lift (k:ℕ) (f:MvPolynomial (Option (Fin 2)) F)
    (support:f∈restrictBidegree (Fin 2) F (a*k) (b*k)) :
    ∃ Q:MvPolynomial (bidegreeExponents (Fin 2) a b) F, Q.totalDegree≤k ∧
      bidegreeMap (Fin 2) F a b Q=f := by
  classical
  have per (m:f.support) :
      ∃ Q:MvPolynomial (bidegreeExponents (Fin 2) a b) F, Q.totalDegree≤k ∧
        bidegreeMap (Fin 2) F a b Q=monomial m.val 1 := by
    obtain ⟨hy,hz⟩:=mem_restrictBidegree.mp support m.val m.property
    rw [degree_pair] at hz
    obtain ⟨Q,hq,eq⟩:=lift_monomial (F:=F) a b k _ _ _ hy hz
    exact ⟨Q,hq,eq.trans (congrArg (fun d=>monomial d (1:F)) (triple_eta m.val))⟩
  choose Q bound eq using per
  refine ⟨∑ m:f.support,C (f.coeff m.val)*Q m,?_,?_⟩
  · apply totalDegree_finsetSum_le
    intro m _
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_C,zero_add];exact bound m)
  · simp only [map_sum,map_mul,bidegreeMap,aeval_C,algebraMap_eq] at eq ⊢
    simp_rw [eq,C_mul_monomial,mul_one]
    rw [Finset.sum_coe_sort f.support (fun m=>monomial m (f.coeff m))]
    exact f.support_sum_monomial_coeff

end
end Research6969.ScaledBidegree
