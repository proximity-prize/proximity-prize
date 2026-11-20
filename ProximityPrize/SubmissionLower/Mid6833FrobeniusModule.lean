/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

/- Polynomial Frobenius modules for the two-sided normal-form rows of Lucieno's
   PR 618 as extended in TwoSided.lean. The algebra is independent of that instance. -/
namespace KoalaFrontier
open Polynomial
open scoped Polynomial
noncomputable section
variable {K : Type*} [Field K] (σ : K →+* K) (L R : K[X])

def Solves (P : K[X]) : Prop := L * P.map σ = R * P

private theorem cross {U V : K[X]} (hL : L ≠ 0)
    (hu : Solves σ L R U) (hv : Solves σ L R V) :
    U.map σ * V = V.map σ * U := by
  apply mul_left_cancel₀ hL
  unfold Solves at hu hv
  linear_combination V*hu-U*hv

private theorem subtract_fixed_multiple {P H T : K[X]}
    (hP : Solves σ L R P) (hH : Solves σ L R H) (hT : T.map σ = T) :
    Solves σ L R (P-H*T) := by
  unfold Solves at *
  rw [Polynomial.map_sub, Polynomial.map_mul,hT]
  linear_combination hP-T*hH

/-- Polynomial part of rank-one semilinear descent.
    A least-degree nonzero solution generates the entire kernel over the
    coefficientwise fixed polynomial subring. -/
theorem minimal_generator (H : K[X]) (hH : H ≠ 0) (hL : L ≠ 0)
    (hs : Solves σ L R H)
    (minimal : ∀ U : K[X], U ≠ 0 → Solves σ L R U → H.natDegree ≤ U.natDegree)
    (P : K[X]) :
    Solves σ L R P ↔ ∃ T : K[X], T.map σ = T ∧ P=H*T := by
  classical
  refine ⟨?_,?_⟩
  · intro hP
    induction k : P.natDegree using Nat.strong_induction_on generalizing P with
    | h k ih =>
      by_cases pz : P = 0
      · exact ⟨0, by simp, by simp [pz]⟩
      let c := P.leadingCoeff / H.leadingCoeff
      have lp : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr pz
      have lh : H.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hH
      have fixed : σ c = c := by
        have rel := congrArg Polynomial.leadingCoeff (cross σ L R hL hP hs)
        simp only [leadingCoeff_mul,leadingCoeff_map] at rel
        simp only [c,map_div₀]
        apply (div_eq_div_iff (fun z => lh (σ.injective (z.trans (map_zero σ).symm))) lh).mpr
        linear_combination rel
      let T := C c * X^(P.natDegree-H.natDegree)
      have tfix : T.map σ = T := by simp [T,fixed]
      have cn : c ≠ 0 := div_ne_zero lp lh
      have tn : T ≠ 0 := mul_ne_zero (C_ne_zero.mpr cn) (pow_ne_zero _ X_ne_zero)
      have htn : H*T ≠ 0 := mul_ne_zero hH tn
      have deq : P.natDegree = (H*T).natDegree := by
        rw [natDegree_mul hH tn]
        simp only [T,natDegree_C_mul cn,natDegree_X_pow]
        have := minimal P pz hP
        omega
      have leq : P.leadingCoeff = (H*T).leadingCoeff := by
        simp only [T,leadingCoeff_mul,leadingCoeff_C,leadingCoeff_pow,leadingCoeff_X,one_pow,mul_one,c]
        field_simp
      have dd := degree_sub_lt_left (by simpa [degree_eq_natDegree pz,degree_eq_natDegree htn] using deq)
          pz leq
      have remsol := subtract_fixed_multiple σ L R hP hs tfix
      by_cases z : P-H*T=0
      · exact ⟨T,tfix,sub_eq_zero.mp z⟩
      · have less := (natDegree_lt_natDegree_iff z).mpr dd
        obtain ⟨V,hV,eV⟩ := ih _ (by omega) _ remsol rfl
        refine ⟨T+V,by simp [Polynomial.map_add,tfix,hV],?_⟩
        linear_combination eV
  · rintro ⟨T,fix,rfl⟩
    unfold Solves at *
    rw [Polynomial.map_mul,fix]
    linear_combination T*hs

theorem exists_minimal (hex : ∃ U : K[X], U ≠ 0 ∧ Solves σ L R U) :
    ∃ H : K[X], H ≠ 0 ∧ Solves σ L R H ∧
      ∀ U : K[X], U ≠ 0 → Solves σ L R U → H.natDegree ≤ U.natDegree := by
  classical
  let good (n : ℕ) := ∃ U : K[X], U ≠ 0 ∧ Solves σ L R U ∧ U.natDegree = n
  have nonempty : ∃ n, good n := by
    obtain ⟨P,h,hp⟩ := hex
    exact ⟨_,P,h,hp,rfl⟩
  obtain ⟨H,hn,hs,hdeg⟩ := Nat.find_spec nonempty
  exact ⟨H,hn,hs,fun U un us => hdeg.trans_le (Nat.find_min' nonempty ⟨U,un,us,rfl⟩)⟩

/-- At every evaluation node fixed by the coefficient map, the primitive
    generator is a unit upon evaluation. Translation and division preserve
    every original agreement. -/
theorem generator_avoids_fixed_nodes (H : K[X]) (hH : H ≠ 0) (hs : Solves σ L R H)
    (minimal : ∀ U : K[X], U ≠ 0 → Solves σ L R U → H.natDegree ≤ U.natDegree)
    (x : K) (hx : σ x = x) : H.eval x ≠ 0 := by
  intro root
  obtain ⟨V,e⟩ := (Polynomial.dvd_iff_isRoot.mpr root : X-C x ∣ H)
  have vn : V ≠ 0 := by intro z; simp [z] at e; exact hH e
  have fn := X_sub_C_ne_zero x
  have vs : Solves σ L R V := by
    unfold Solves at *
    apply mul_left_cancel₀ fn
    rw [e,Polynomial.map_mul,Polynomial.map_sub,map_X,map_C,hx] at hs
    linear_combination hs
  have bd := minimal V vn vs
  rw [e,natDegree_mul fn vn,natDegree_X_sub_C] at bd
  omega

/-- Directly obtains a common affine quotient and a full-domain received word. -/
theorem normalized_affine_family {I J : Type*} (Q : J → K[X]) (r : J) (x : I → K)
    (W : I → K) (fixed : ∀ i, σ (x i)=x i) (hL : L≠0) (O : K[X])
    (rows : ∀ g, L*(Q g).map σ=R*Q g+O) (varies : ∃ g, Q g≠Q r) :
    ∃ H : K[X], ∃ T : J → K[X], ∃ u : I → K,
      H≠0 ∧ Solves σ L R H ∧ (∀ i, H.eval (x i)≠0) ∧
      (∀ g, (T g).map σ=T g ∧ Q g-Q r=H*T g) ∧
      (∀ g i, (Q g).eval (x i)=W i ↔ (T g).eval (x i)=u i) := by
  classical
  have dif (g : J) : Solves σ L R (Q g-Q r) := by
    unfold Solves
    rw [Polynomial.map_sub]
    linear_combination rows g-rows r
  obtain ⟨v,hv⟩ := varies
  obtain ⟨H,hn,hs,hm⟩ := exists_minimal σ L R ⟨_,sub_ne_zero.mpr hv,dif v⟩
  choose T fix fac using fun g => (minimal_generator σ L R H hn hL hs hm _).mp (dif g)
  have units i := generator_avoids_fixed_nodes σ L R H hn hs hm (x i) (fixed i)
  refine ⟨H,T,fun i => (W i-(Q r).eval (x i))/H.eval (x i),hn,hs,units,fun g => ⟨fix g,fac g⟩,?_⟩
  intro g i
  have ev := congrArg (fun P : K[X] => P.eval (x i)) (fac g)
  simp only [eval_sub,eval_mul] at ev
  rw [eq_div_iff (units i)]
  constructor
  · intro hh; linear_combination hh-ev
  · intro hh; linear_combination ev+hh

#print axioms minimal_generator
#print axioms exists_minimal
#print axioms generator_avoids_fixed_nodes
#print axioms normalized_affine_family
end
end KoalaFrontier
