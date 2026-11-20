import ProximityPrize.SubmissionLower.Koala6831IntrinsicAffineFamily
import ProximityPrize.SubmissionLower.Koala6831IntrinsicChartProjection
import ProximityPrize.SubmissionLower.Koala6831IntrinsicLongLiteral

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped BigOperators
open MvPolynomial RCN002 RCN005 RCN042 RCN093 RCN113 RCN120 RCN125 RCN135
  RCN136 RCN264 RCN341 RCN344

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

variable {K : Type} [Field K] {A : Type} [Fintype A]

local notation "Ω" => GenericField K
local notation "φ" => polynomialEmbedding K

private theorem literal_seed_notin_powerField {P : Ideal (MvPolynomial (Fin 3) Ω)}
    [P.IsPrime] (p : ℕ) [ExpChar Ω p] [ExpChar (CoordinateField Ω P) p]
    (hp : p.Prime) (seed : SeparableLiteralCoordinate P) :
    coordinate Ω P seed.index ∉ powerField (CoordinateField Ω P) p := by
  letI : ExpChar (RatFunc Ω) p :=
    expChar_of_injective_algebraMap (algebraMap Ω (RatFunc Ω)).injective p
  letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
    rationalBaseAlgebra Ω P seed.index seed.transcendental
  letI : Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P) := seed.separable
  have h := separating_ratFunc_coordinate_notin_powerField
    (K := Ω) (E := CoordinateField Ω P) p hp
  rwa [← RatFunc.algebraMap_X, rational_variable_image Ω P seed.index seed.transcendental] at h

theorem weighted_coordinate_pole_le_of_degree
    (E : A → Type) [∀ a, Field (E a)] [∀ a, Algebra Ω (E a)]
    (u : ∀ a, Coordinate Ω (E a)) (weight : A → ℕ)
    (W : ∀ a, Finset (Place Ω (E a))) (budget : ℕ)
    (hdegree : (∑ a, weight a * coordinateDegree Ω (E a) (u a)) ≤ budget) :
    (∑ a, (weight a : ℤ) * ∑ v ∈ W a,
      RCN187.poleOrder v.val (coordinateValue Ω (E a) (u a))) ≤ (budget : ℤ) := by
  calc
    _ ≤ ∑ a, (weight a : ℤ) * (coordinateDegree Ω (E a) (u a) : ℤ) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        (finite_sum_coordinate_pole_le_degree Ω (E a) (u a) (W a)) (by positivity)
    _ ≤ (budget : ℤ) := by exact_mod_cast hdegree

theorem intrinsic_affine_weighted_pole_bound
    (F : Carrier K) (w p : ℕ) [CharP K p] (hp : p.Prime)
    (G : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (hproper : ¬ G ∣ surfaceMap φ (tailNumerator F w))
    (hderiv : MvPolynomial.pderiv (0 : Fin 3) G ≠ 0)
    (component : A → RegularComponent Ω G
      (surfaceMap φ (tailNumerator F w)) (surfaceMap φ (implicitRegularity F)))
    (hinj : Function.Injective component)
    (charts : ∀ a, CurveChartData F w (component a).1)
    (seed : ∀ a, SeparableLiteralCoordinate (component a).1)
    (hseed : ∀ a, (seed a).index = 1 ∨ (seed a).index = 2)
    (hactive : ∀ a, Transcendental Ω (coordinate Ω (component a).1 0) ∨
      Transcendental Ω (coordinate Ω (component a).1 1))
    (W : ∀ a, Finset (Place Ω (CoordinateField Ω (component a).1)))
    (tg tt zg zt : ℕ)
    (hGt : ∀ d ∈ G.support, d 0 + d 1 ≤ tg)
    (hTt : ∀ d ∈ (surfaceMap φ (tailNumerator F w)).support, d 0 + d 1 ≤ tt)
    (hGz : G.degreeOf 2 ≤ zg) (hTz : (surfaceMap φ (tailNumerator F w)).degreeOf 2 ≤ zt)
    (hzg : zg < p) (hzt : zt < p) :
    (∑ a, (curveTailOrder F w (component a).1 (charts a) : ℤ) * ∑ v ∈ W a,
      max (RCN187.poleOrder v.val (coordinate Ω (component a).1 1))
        (RCN187.poleOrder v.val (coordinate Ω (component a).1 0))) ≤
      ((tt * zg + tg * zt : ℕ) : ℤ) := by
  classical
  let T := surfaceMap φ (tailNumerator F w)
  let H := surfaceMap φ (implicitRegularity F)
  let Q (a : A) := (component a).1
  let E (a : A) := CoordinateField Ω (Q a)
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP Ω p := genericField_charP K p
  letI : ExpChar Ω p := .prime hp
  letI : ∀ a, ExpChar (E a) p :=
    fun a => expChar_of_injective_algebraMap (algebraMap Ω (E a)).injective p
  have hinjQ : Function.Injective Q := fun _ _ h => hinj (Subtype.ext h)
  have hGmem (a : A) : G ∈ Q a := regularComponent_G_mem Ω G T H (component a)
  have hTmem (a : A) : T ∈ Q a := regularComponent_T_mem Ω G T H (component a)
  have hpower (a : A) : coordinate Ω (Q a) 1 ∉ powerField (E a) p ∨
      coordinate Ω (Q a) 0 ∉ powerField (E a) p := by
    have hn := literal_seed_notin_powerField p hp (seed a)
    rcases hseed a with h | h
    · exact Or.inl (by rwa [h] at hn)
    · rw [h] at hn
      exact (active_pair_has_nonpower (Q a) p hp hn G T hG (hGmem a) (hTmem a)
        hproper (hGz.trans_lt hzg) (hTz.trans_lt hzt) (hactive a)).symm
  let s (a : A) : SeparableCoordinate Ω (E a) :=
    ⟨rationalBaseEmbedding Ω (Q a) (seed a).index (seed a).transcendental,
      (seed a).finite, (seed a).separable⟩
  obtain ⟨lam, hpos, ht, hfinite, hsep, hval⟩ :=
    exists_separating_affine_pair Q hinjQ G T hG hGmem hTmem hproper hderiv
      p hp hpower s W tg tt zg zt hGt hTt hGz hTz
  let u (a : A) := flagEvaluation Ω (Q a) 0 lam 0 (MvPolynomial.X (seedZeroOrder 0))
  have hgate (a : A) (hx : Transcendental Ω (u a)) :
      (letI := flagBaseAlgebra Ω (Q a) 0 lam 0 seedZeroOrder hx
       FiniteDimensional (RatFunc Ω) (E a)) ∧
      (letI := flagBaseAlgebra Ω (Q a) 0 lam 0 seedZeroOrder hx
       Algebra.IsSeparable (RatFunc Ω) (E a)) :=
    ⟨hfinite a, hsep a⟩
  have hcap := affine_pair_resultant_degree lam G T tg tt zg zt hGt hTt hGz hTz
  have hbudget := intrinsic_sum_order_mul_coordinateDegree_le
    F w p hp component charts 0 lam 0 seedZeroOrder ht hfinite
    (fun a => affine_pair_generators (Q a) lam (ht a))
    hinj hG hdiv rfl hproper hpos hgate (tt * zg + tg * zt) hcap
  have hbound := weighted_coordinate_pole_le_of_degree E
    (fun a => coordinateOfGate (u a) (hgate a))
    (fun a => curveTailOrder F w (component a).1 (charts a))
    W (tt * zg + tg * zt) hbudget
  refine le_trans ?_ hbound
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro v hv
  have hvalue : coordinateValue Ω (E a) (coordinateOfGate (u a) (hgate a)) = u a :=
    coordinateOfGate_value (K := Ω) (L := E a) (u a) (hgate a)
  rw [hvalue]
  exact (hval a v hv).symm.le

theorem intrinsic_affine_weighted_pole_bound_all
    (F : Carrier K) (w p : ℕ) [CharP K p] (hp : p.Prime)
    (G : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (hproper : ¬ G ∣ surfaceMap φ (tailNumerator F w))
    (component : A → RegularComponent Ω G
      (surfaceMap φ (tailNumerator F w)) (surfaceMap φ (implicitRegularity F)))
    (hinj : Function.Injective component)
    (charts : ∀ a, CurveChartData F w (component a).1)
    (seed : ∀ a, SeparableLiteralCoordinate (component a).1)
    (hseed : ∀ a, (seed a).index = 1 ∨ (seed a).index = 2)
    (W : ∀ a, Finset (Place Ω (CoordinateField Ω (component a).1)))
    (tg tt zg zt : ℕ)
    (hGt : ∀ d ∈ G.support, d 0 + d 1 ≤ tg)
    (hTt : ∀ d ∈ (surfaceMap φ (tailNumerator F w)).support, d 0 + d 1 ≤ tt)
    (hGz : G.degreeOf 2 ≤ zg) (hTz : (surfaceMap φ (tailNumerator F w)).degreeOf 2 ≤ zt)
    (hzg : zg < p) (hzt : zt < p) :
    (∑ a, (curveTailOrder F w (component a).1 (charts a) : ℤ) * ∑ v ∈ W a,
      max (RCN187.poleOrder v.val (coordinate Ω (component a).1 1))
        (RCN187.poleOrder v.val (coordinate Ω (component a).1 0))) ≤
      ((tt * zg + tg * zt : ℕ) : ℤ) := by
  classical
  by_cases hn : Nonempty A
  · obtain ⟨a₀⟩ := hn
    have hd : MvPolynomial.pderiv (0 : Fin 3) G ≠ 0 := by
      intro hz
      exact (long_regular_pderiv_Y_not_mem F w hdiv (component a₀)) (hz ▸ Ideal.zero_mem _)
    let active (a : A) := Transcendental Ω (coordinate Ω (component a).1 0) ∨
      Transcendental Ω (coordinate Ω (component a).1 1)
    let mass (a : A) : ℤ := (curveTailOrder F w (component a).1 (charts a) : ℤ) *
      ∑ v ∈ W a, max (RCN187.poleOrder v.val (coordinate Ω (component a).1 1))
        (RCN187.poleOrder v.val (coordinate Ω (component a).1 0))
    have hbound : (∑ a : {a // active a}, mass a.1) ≤ ((tt * zg + tg * zt : ℕ) : ℤ) :=
      intrinsic_affine_weighted_pole_bound F w p hp G hG hdiv hproper hd
        (fun a : {a // active a} => component a.1)
        (hinj.comp Subtype.val_injective) (fun a => charts a.1) (fun a => seed a.1)
        (fun a => hseed a.1) (fun a => a.2) (fun a => W a.1)
        tg tt zg zt hGt hTt hGz hTz hzg hzt
    have hzero (a : A) (ha : ¬ active a) : mass a = 0 := by
      obtain ⟨hy, hz⟩ := not_or.mp ha
      simp [mass, RCN037.poleOrder_eq_zero_of_isAlgebraic _ _ (not_not.mp hy),
        RCN037.poleOrder_eq_zero_of_isAlgebraic _ _ (not_not.mp hz)]
    change (∑ a, mass a) ≤ _
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ active mass]
    have hzsum : (∑ a ∈ Finset.univ.filter (fun a => ¬ active a), mass a) = 0 := by
      exact Finset.sum_eq_zero (fun a ha => hzero a (Finset.mem_filter.mp ha).2)
    rw [hzsum, add_zero]
    exact (by
      simpa only [Finset.subtype_univ] using
        (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset A)) mass (p := active)).symm :
         (∑ a ∈ Finset.univ.filter active, mass a) = ∑ a : {a // active a}, mass a.1).trans_le hbound
  · letI : IsEmpty A := not_nonempty_iff.mp hn
    simp
    positivity

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
