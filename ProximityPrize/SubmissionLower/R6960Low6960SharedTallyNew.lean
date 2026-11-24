import ProximityPrize.SubmissionLower.Fast063
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import ProximityPrize.SubmissionLower.R6960Low6960VariableSelect
import ProximityPrize.SubmissionLower.Shared50OrderDivision
import ProximityPrize.SubmissionLower.R6960Low6960RetainedAssembly
import ProximityPrize.SubmissionLower.R6960Low6960SharedBentCaps
import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.R6960Low6960TiltedRectangle

-- merged module Shared50MultiplicityLocal
section Merged_Shared50MultiplicityLocal
set_option Elab.async false
set_option maxHeartbeats 650000
namespace Shared50Multiplicity
noncomputable section
open Ideal IsLocalRing
open K1_13_6_3_6 (quotientMul quotientMul_injective quotientMul_exact)
open scoped ENat
variable {R : Type} [CommRing R]
private abbrev quotientLength (I : Ideal R) : ℕ∞ := Module.length R (R ⧸ I)
private abbrev single (x : R) : Ideal R := Ideal.span {x}
private theorem length_step (I : Ideal R) (g : R) :
    quotientLength I = quotientLength (I.colon {g}) + quotientLength (I ⊔ single g) :=
  Module.length_eq_add_of_exact (quotientMul I g)
    (Submodule.factor (le_sup_left : I ≤ I ⊔ single g))
    (quotientMul_injective I g) (Submodule.factor_surjective le_sup_left) (quotientMul_exact I g)
private theorem length_anti {I J : Ideal R} (h : I ≤ J) : quotientLength J ≤ quotientLength I :=
  Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)
private theorem length_top : quotientLength (⊤ : Ideal R) = 0 := by
  exact Module.length_eq_zero
private theorem length_max [IsLocalRing R] : quotientLength (maximalIdeal R) = 1 := by
  have : IsSimpleModule R (R ⧸ maximalIdeal R) :=
    isSimpleModule_iff_isCoatom.mpr (maximalIdeal.isMaximal R).1
  exact Module.length_eq_one _ _
private theorem decompose {m I : Ideal R} {u v z : R} (hm : m = single u ⊔ single v)
    (h : z ∈ m*I) : ∃ a∈I, ∃ b∈I, u*a+v*b = z := by
  rw [hm, Ideal.sup_mul] at h
  obtain ⟨p,hp,q,hq,hz⟩ := Submodule.mem_sup.mp h
  obtain ⟨a,ha,rfl⟩ := Ideal.mem_span_singleton_mul.mp hp
  obtain ⟨b,hb,rfl⟩ := Ideal.mem_span_singleton_mul.mp hq
  exact ⟨a,ha,b,hb,hz⟩
private theorem nonprincipal_of_spanFinrank_two {m : Ideal R}
    (hr : m.spanFinrank = 2) (x : R) : m ≠ single x := by
  intro h
  have hh := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_singleton x)
  have hh' : (single x).spanFinrank ≤ 1 := by simpa only [Set.ncard_singleton] using hh
  rw [← h, hr] at hh'
  omega
private theorem prime_parameters [IsDomain R] [IsLocalRing R] [UniqueFactorizationMonoid R]
    [IsNoetherianRing R] (hm2 : (maximalIdeal R).spanFinrank = 2) :
    ∃ u v : R, maximalIdeal R = single u ⊔ single v ∧ Prime u ∧ ¬ u ∣ v := by
  classical
  let m := maximalIdeal R
  have hfg : Submodule.FG m := Ideal.fg_of_isNoetherianRing _
  obtain ⟨s,hs,hspan⟩ := hfg.exists_span_finset_card_eq_spanFinrank
  rw [hm2, Finset.card_eq_two] at hs
  obtain ⟨u,v,_,rfl⟩ := hs
  have hm : m = single u ⊔ single v := by
    change Submodule.span R (↑({u,v} : Finset R) : Set R) = m at hspan
    simpa only [Finset.coe_insert, Finset.coe_singleton, Submodule.span_insert,
      Ideal.submodule_span_eq] using hspan.symm
  have hnu := nonprincipal_of_spanFinrank_two hm2 u
  have hnv := nonprincipal_of_spanFinrank_two hm2 v
  have hu : u ∈ m := hm ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self u)
  have hv : v ∈ m := hm ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self v)
  have hnuv : ¬ u ∣ v := by
    intro h
    exact hnu (hm.trans (sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_span_singleton.mpr h))))
  have hnum : u ∉ m*m := by
    intro h
    obtain ⟨a,ha,b,hb,hab⟩ := decompose hm h
    have hua : IsUnit (1-a) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits a
      ((IsLocalRing.mem_maximalIdeal a).mp ha)
    have hub : (1-a)*u = v*b := by linear_combination -hab
    have hdiv : v ∣ u := by
      have hg : v ∣ (1-a)*u := ⟨b,hub⟩
      exact (hua.dvd_mul_left).mp hg
    exact hnv (hm.trans (sup_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_span_singleton.mpr hdiv))))
  have huI : Irreducible u := by
    refine ⟨(IsLocalRing.mem_maximalIdeal u).mp hu, ?_⟩
    intro x y he
    by_contra! h
    exact hnum (he ▸ Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal x).mpr h.1)
      ((IsLocalRing.mem_maximalIdeal y).mpr h.2))
  exact ⟨u,v,hm,UniqueFactorizationMonoid.irreducible_iff_prime.mp huI,hnuv⟩
private theorem colon_power_left [IsDomain R] {m : Ideal R} {u v : R}
    (hm : m = single u ⊔ single v) (hu : Prime u) (hn : ¬ u ∣ v) (n : ℕ) :
    (m^(n+1)).colon {u} = m^n := by
  have hum : u ∈ m := hm ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self u)
  induction n with
  | zero =>
    rw [Nat.zero_add, pow_one, pow_zero, Ideal.one_eq_top]
    apply top_unique
    intro x _
    exact Submodule.mem_colon_singleton.mpr (m.mul_mem_left x hum)
  | succ n ih =>
    ext x
    change x ∈ (m^(n+2)).colon {u} ↔ x ∈ m^(n+1)
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    constructor
    · intro hx
      have hx' : x*u ∈ m * m^(n+1) := by rwa [← pow_succ']
      obtain ⟨a,ha,b,hb,hab⟩ := decompose hm hx'
      have hd : u ∣ v*b := ⟨x-a,by linear_combination hab⟩
      obtain ⟨c,hc⟩ := (hu.dvd_mul.mp hd).resolve_left hn
      have hc' : c ∈ m^n := by
        rw [← ih, Submodule.mem_colon_singleton, smul_eq_mul, mul_comm c u, ← hc]
        exact hb
      have hvc : v*c ∈ m^(n+1) := by
        rw [pow_succ']
        exact Ideal.mul_mem_mul (hm ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self v)) hc'
      have he : x = a+v*c := by
        apply mul_right_cancel₀ hu.ne_zero
        rw [hc] at hab
        linear_combination -hab
      exact he ▸ (m^(n+1)).add_mem ha hvc
    · intro hx
      rw [pow_succ]
      exact Ideal.mul_mem_mul hx hum
private theorem higher_mod_left {m : Ideal R} {u v : R} (hm : m = single u ⊔ single v) (n : ℕ) :
    m^n ⊔ single u = single u ⊔ (single v)^n := by
  induction n with
  | zero => simp [Ideal.one_eq_top]
  | succ n ih =>
    have hv : single v ≤ m := by rw [hm]; exact le_sup_right
    have hi : m^n ≤ single u ⊔ (single v)^n := by rw [← ih]; exact le_sup_left
    have hform : m^(n+1) = (single u*m^n) ⊔ (single v*m^n) := by
      rw [pow_succ', ← Ideal.sup_mul, ← hm]
    apply le_antisymm
    · apply sup_le _ le_sup_left
      rw [hform]
      apply sup_le
      · exact (show single u*m^n ≤ single u from mul_le_left).trans le_sup_left
      · calc
          _ ≤ single v * (single u ⊔ (single v)^n) := Ideal.mul_mono le_rfl hi
          _ = single v * single u ⊔ (single v)^(n+1) := by rw [Ideal.mul_sup, pow_succ']
          _ ≤ _ := sup_le ((show single v*single u ≤ single u from mul_le_right).trans le_sup_left)
            le_sup_right
    · exact sup_le le_sup_right ((Ideal.pow_right_mono hv _).trans le_sup_left)
private theorem colon_power_mod_left [IsDomain R] {u v : R} (hu : Prime u) (hn : ¬ u ∣ v) (n : ℕ) :
    (single u ⊔ (single v)^(n+1)).colon {v} = single u ⊔ (single v)^n := by
  ext x
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  simp only [Ideal.span_singleton_pow]
  constructor
  · intro hx
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y,rfl⟩ := Ideal.mem_span_singleton.mp ha
    obtain ⟨z,rfl⟩ := Ideal.mem_span_singleton.mp hb
    have hdiv : u ∣ v*(x-v^n*z) := ⟨y,by rw [pow_succ] at hab; linear_combination -hab⟩
    have hleft : x-v^n*z ∈ single u := Ideal.mem_span_singleton.mpr ((hu.dvd_mul.mp hdiv).resolve_left hn)
    have hright : v^n*z ∈ single (v^n) := Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    apply Submodule.mem_sup.mpr
    refine ⟨_,hleft,_,hright,sub_add_cancel _ _⟩
  · intro hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y,rfl⟩ := Ideal.mem_span_singleton.mp ha
    obtain ⟨z,rfl⟩ := Ideal.mem_span_singleton.mp hb
    rw [add_mul]
    apply (single u ⊔ single (v^(n+1))).add_mem
    · apply Ideal.mem_sup_left
      exact Ideal.mem_span_singleton.mpr ⟨y*v,by ring⟩
    · apply Ideal.mem_sup_right
      exact Ideal.mem_span_singleton.mpr ⟨z,by rw [pow_succ]; ring⟩
private theorem length_mod_left [IsDomain R] [IsLocalRing R] {u v : R}
    (hm : maximalIdeal R = single u ⊔ single v) (hu : Prime u) (hn : ¬ u ∣ v) (n : ℕ) :
    quotientLength (single u ⊔ (single v)^n) = n := by
  induction n with
  | zero => simp only [pow_zero, Ideal.one_eq_top, sup_top_eq, length_top, Nat.cast_zero]
  | succ n ih =>
    have h := length_step (single u ⊔ (single v)^(n+1)) v
    rw [colon_power_mod_left hu hn n, ih] at h
    have hs : (single u ⊔ (single v)^(n+1)) ⊔ single v = maximalIdeal R := by
      have hv : (single v)^(n+1) ≤ single v := Ideal.pow_le_self (Nat.succ_ne_zero _)
      rw [sup_assoc, sup_eq_right.mpr hv, ← hm]
    rw [hs, length_max] at h
    exact h.trans (Nat.cast_succ n).symm
private def triangle : ℕ → ℕ
  | 0 => 0
  | n+1 => triangle n + (n+1)
private theorem length_max_power [IsDomain R] [IsLocalRing R] [UniqueFactorizationMonoid R]
    [IsNoetherianRing R] (hm2 : (maximalIdeal R).spanFinrank = 2) (n : ℕ) :
    quotientLength ((maximalIdeal R)^n) = triangle n := by
  obtain ⟨u,v,hm,hu,hn⟩ := prime_parameters hm2
  induction n with
  | zero => simp only [pow_zero, Ideal.one_eq_top, length_top, triangle, Nat.cast_zero]
  | succ n ih =>
    rw [length_step _ u, colon_power_left hm hu hn n, ih,
      higher_mod_left hm (n+1), length_mod_left hm hu hn, triangle]
    simp only [Nat.cast_add]
private theorem triangle_add (a b : ℕ) : triangle (a+b) = triangle a + triangle b + a*b := by
  induction b with
  | zero => simp [triangle]
  | succ b ih =>
    rw [Nat.add_succ, triangle, triangle, ih, Nat.mul_succ]
    omega
private theorem triangle_mul (a b : ℕ) :
    triangle (a+b+1) = triangle b + triangle a + (a+1)*(b+1) := by
  rw [triangle, triangle_add, Nat.add_mul, Nat.mul_add, one_mul, mul_one]
  omega
theorem length_ge_product [IsDomain R] [IsLocalRing R] [UniqueFactorizationMonoid R]
    [IsNoetherianRing R] (hm2 : (maximalIdeal R).spanFinrank = 2) {f g : R} {a b : ℕ}
    (hf : f ∈ maximalIdeal R ^ a) (hg : g ∈ maximalIdeal R ^ b) :
    ((a*b : ℕ) : ℕ∞) ≤ quotientLength (Ideal.span {f,g}) := by
  cases a with
  | zero => simp
  | succ a =>
    cases b with
    | zero => simp
    | succ b =>
      let m := maximalIdeal R
      let t := a+b+1
      let I := m^t
      let J := I ⊔ single f
      let K := J ⊔ single g
      have hfa : m^b ≤ I.colon {f} := by
        intro x hx
        apply Submodule.mem_colon_singleton.mpr
        change x*f ∈ m^t
        rw [show t = b+(a+1) by unfold t; omega, pow_add]
        exact Ideal.mul_mem_mul hx hf
      have hgb : m^a ≤ J.colon {g} := by
        intro x hx
        apply Submodule.mem_colon_singleton.mpr
        apply (show I ≤ J from le_sup_left)
        change x*g ∈ m^t
        rw [show t = a+(b+1) by rfl, pow_add]
        exact Ideal.mul_mem_mul hx hg
      have hlen : quotientLength I ≤ quotientLength (m^b) + quotientLength (m^a) + quotientLength K := by
        calc
          _ = quotientLength (I.colon {f}) + (quotientLength (J.colon {g}) + quotientLength K) := by
            rw [length_step I f, show I ⊔ single f = J from rfl, length_step J g]
          _ ≤ quotientLength (m^b) + (quotientLength (m^a) + quotientLength K) :=
            add_le_add (length_anti hfa) (add_le_add (length_anti hgb) le_rfl)
          _ = _ := (add_assoc ..).symm
      change quotientLength (m^t) ≤ _ at hlen
      rw [length_max_power hm2 t, length_max_power hm2 b, length_max_power hm2 a,
        show triangle t = triangle b + triangle a + (a+1)*(b+1) by exact triangle_mul a b,
        Nat.cast_add, Nat.cast_add] at hlen
      have hfinite : (triangle b : ℕ∞) + (triangle a : ℕ∞) ≠ ⊤ := by
        rw [← Nat.cast_add]; exact ENat.natCast_ne_top _
      have hlow : (((a+1)*(b+1) : ℕ) : ℕ∞) ≤ quotientLength K :=
        (ENat.add_le_add_iff_left hfinite).mp hlen
      apply hlow.trans
      apply length_anti
      rw [Ideal.span_insert]
      exact sup_le (show single f ≤ K from le_sup_right.trans le_sup_left)
        (show single g ≤ K from le_sup_right)
end
#print axioms length_ge_product
end Shared50Multiplicity

end Merged_Shared50MultiplicityLocal

-- merged module Shared50Multiplicity
section Merged_Shared50Multiplicity

set_option Elab.async false
set_option maxHeartbeats 750000

namespace Shared50Multiplicity

open K1_13 (Row)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo pair_height)
open K1_13_6_3 (cycleWeight)
open scoped ENat BigOperators

/-- Prescribed orders on the two cutting equations multiply in the original
height-two local intersection length. The gain feeds the existing cycle ledger. -/
theorem cycleLength_ge_product {f Q : Row 4} {P : Ideal GeoJets} [P.IsPrime] {a b : ℕ}
    (hheight : P.height = 2) (hf : VanishesTo P (toGeneric f) a)
    (hQ : VanishesTo P (toGeneric Q) b) :
    ((a*b : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P ‹P.IsPrime› := by
  let L := Localization.AtPrime P
  let φ := algebraMap GeoJets L
  let : IsRegularLocalRing L := by
    change IsRegularLocalRing (Localization.AtPrime P)
    infer_instance
  have hm2 : (IsLocalRing.maximalIdeal L).spanFinrank = 2 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := L)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P L, hheight] at h
    exact_mod_cast h
  have hmap : (intersectionIdeal f Q).map φ =
      Ideal.span {φ (toGeneric f), φ (toGeneric Q)} := by
    rw [intersectionIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change ((a*b : ℕ) : ℕ∞) ≤ Module.length L (L ⧸ (intersectionIdeal f Q).map φ)
  rw [hmap]
  exact length_ge_product hm2 hf hQ

theorem cycleLength_ge_product_of_minimal {f Q : Row 4} {P : Ideal GeoJets} {a b : ℕ}
    (hP : (intersectionIdeal f Q).IsMinimalPrime P) (hfn : toGeneric f ≠ 0)
    (hQrel : IsRelPrime (toGeneric f) (toGeneric Q))
    (hf : @VanishesTo GeoJets _ P hP.isPrime (toGeneric f) a)
    (hQ : @VanishesTo GeoJets _ P hP.isPrime (toGeneric Q) b) :
    ((a*b : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P hP.isPrime := by
  let := hP.isPrime
  exact cycleLength_ge_product (pair_height hfn hQrel hP) hf hQ



#print axioms cycleLength_ge_product
#print axioms cycleLength_ge_product_of_minimal
end Shared50Multiplicity

end Merged_Shared50Multiplicity

-- merged module R6960Low6960SharedChooseCut
section Merged_R6960Low6960SharedChooseCut
set_option Elab.async false
set_option linter.style.haveILetI false
set_option maxRecDepth 12000

namespace Low6960SharedChooseCut
noncomputable section

open K1_13 (Geom Row Shape shape InBox indexDegree)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo pair_height cycleLength_ge_order)
open MvPolynomial
open Low6960SharedPrice (slope coord)

theorem weighted_pow (w : Fin 4 → ℕ) {P : Row 4} (h : P ≠ 0) (a : ℕ) :
    (P^a).weightedTotalDegree w = a * P.weightedTotalDegree w := by
  induction a with
  | zero => rw [pow_zero,zero_mul,← MvPolynomial.C_1,weightedTotalDegree_C]
  | succ a ih =>
    rw [pow_succ,weightedTotalDegree_mul _ _ _ (pow_ne_zero _ h) h,ih,Nat.succ_mul]

theorem valuation_factorization {f P : Row 4} (hf : f ≠ 0)
    (hpos : 0 < f.totalDegree) (hP : P ≠ 0) :
    ∃ a : ℕ, ∃ G : Row 4, P=f^a*G ∧ G≠0 ∧ ¬ f ∣ G := by
  have hm : FiniteMultiplicity f P := by
    refine ⟨P.totalDegree, ?_⟩
    intro hd
    have hle := weightedTotalDegree_le_of_dvd (1 : Fin 4→ℕ) hd hP
    rw [weighted_pow _ hf,weightedTotalDegree_one,weightedTotalDegree_one] at hle
    have ht := Nat.mul_le_mul_left (P.totalDegree+1) hpos
    simp only [Nat.mul_one] at ht
    omega
  obtain ⟨G,hG,hd⟩ := hm.exists_eq_pow_mul_and_not_dvd
  exact ⟨_,G,hG,fun h0 => hP (by rw [hG,h0,mul_zero]),hd⟩

theorem weight_coord (i : Fin 3) (P : Row 4) :
    coord (shape P) i =
      P.weightedTotalDegree (![fun _ : Fin 4 => 1,Fin.val,Pi.single 3 1] i) := by
  fin_cases i
  · exact (weightedTotalDegree_one P).symm
  · exact K1_13_1.indexDegree_eq P
  · exact (weightedTotalDegree_piSingle (3 : Fin 4) P).symm

theorem shape_product {f Q G : Row 4} (hf : f ≠ 0) (hG : G ≠ 0)
    {a : ℕ} (he : Q=f^a*G) (i : Fin 3) :
    coord (shape Q) i = a*coord (shape f) i+coord (shape G) i := by
  simp only [weight_coord,he,weightedTotalDegree_mul _ _ _ (pow_ne_zero _ hf) hG,weighted_pow _ hf]

private theorem cap_coords {Q : Row 4} {r : ℕ}
    (hQ : ∀ m ∈ Q.support, Low6960ShapeGate.fits r m) (i : Fin 3) :
    coord (shape Q) i ≤ r*coord slope i := by
  rw [weight_coord]
  apply Finset.sup_le
  intro m hm
  have hs := hQ m hm
  fin_cases i
  · exact hs.1
  · exact hs.2.1
  · simpa [Finsupp.weight_eq_sum, Finsupp.sum_fintype, Low6960SharedPrice.coord,
      Low6960SharedPrice.slope, Pi.single_apply] using hs.2.2

theorem minimal_pair {f G : Row 4} {P : Ideal GeoJets} [P.IsPrime]
    (hf : Irreducible f) (hproper : ¬f∣G) (hP : P.height=2)
    (hF : toGeneric f∈P) (hG : toGeneric G∈P) :
    (intersectionIdeal f G).IsMinimalPrime P := by
  have hsub : intersectionIdeal f G ≤ P := by
    unfold intersectionIdeal
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl|rfl
    · exact hF
    · exact hG
  obtain ⟨P',hmin,hle⟩ := Ideal.exists_minimalPrimes_le hsub
  have hzero := K1_13_6_3_6.toGeneric_ne_zero hf.ne_zero
  have hrel := K1_13_7_1.proper_generic f G hf hproper
  have hht : P'.height=2 := pair_height hzero hrel hmin
  letI : P'.IsPrime := hmin.isPrime
  have heq : P'=P := by
    by_contra hne
    have hs := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    rw [hht,hP] at hs
    exact (by decide : ¬(2:ℕ∞)+1≤2) hs
  exact heq ▸ hmin

theorem mem_of_order {P : Ideal GeoJets} [P.IsPrime] {Q : GeoJets} {n : ℕ}
    (hn : 0<n) (hQ : VanishesTo P Q n) : Q∈P := by
  let L := Localization.AtPrime P
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L P _).mp
    ((Ideal.pow_le_self (Nat.ne_of_gt hn)) hQ)

structure SuitableSurface (f : Row 4) (s : ℕ) (P : Ideal GeoJets) : Prop where
  prime : P.IsPrime
  height : P.height = 2
  contains : toGeneric f ∈ P
  low : ¬ @VanishesTo _ _ P prime (toGeneric f) (s+1)

/-- The same independent cut has positive residual order at every selected surface. -/
theorem exists_cut {w Γ s} (hm : Low6960Prices.Messages w Γ s)
    (f : Row 4) (hf : Irreducible f) (hpos : 0<f.totalDegree)
    (multiplicityCap : ℕ) (pivot : Fin 3)
    (hguard : multiplicityCap*coord slope pivot < coord (shape f) pivot)
    (surfaces : Finset (Ideal GeoJets))
    (hp : ∀ P ∈ surfaces, Low6960SharedPersistent.Persistent Γ s P)
    (hh : ∀ P ∈ surfaces, SuitableSurface f multiplicityCap P) :
    ∃ r a : ℕ, 0<r ∧ 0<r-multiplicityCap*a ∧ ∃ G : Row 4, G≠0 ∧ ¬f∣G ∧
      (∀ i, a*coord (shape f) i + coord (shape G) i ≤ r*coord slope i) ∧
      ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f G).IsMinimalPrime P,
        @VanishesTo _ _ P h.isPrime (toGeneric G) (r-multiplicityCap*a) ∧
        ((r-multiplicityCap*a : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f G) P h.isPrime := by
  obtain ⟨r,hr,Q,hQ,hs,ho⟩ := Low6960SharedShapeRank.exists_polynomial hm surfaces hp
  obtain ⟨a,G,hfac,hG,hind⟩ := valuation_factorization hf.ne_zero hpos hQ
  have hbound (i : Fin 3) : a*coord (shape f) i+coord (shape G) i ≤ r*coord slope i := by
    rw [← shape_product hf.ne_zero hG hfac i]
    exact cap_coords hs i
  have hres : 0<r-multiplicityCap*a := Shared50ShapeRankBase.residual_order_pos hr hguard
    ((Nat.le_add_right _ _).trans (hbound pivot))
  refine ⟨r,a,hr,hres,G,hG,hind,hbound,?_⟩
  intro P hP
  have hdata := hh P hP
  letI := hdata.prime
  have hmap : toGeneric Q = (toGeneric f)^a*toGeneric G := by
    simp [hfac,toGeneric,map_mul,map_pow]
  have hGo : VanishesTo P (toGeneric G) (r-multiplicityCap*a) := by
    apply Shared50OrderDivision.vanishesTo_of_pow_mul_hasse P hdata.low
    rw [← hmap]
    exact ho P hP
  have hmin := minimal_pair hf hind hdata.height hdata.contains (mem_of_order hres hGo)
  exact ⟨hmin,hGo,cycleLength_ge_order hdata.height hdata.contains hGo⟩

#print axioms exists_cut
end
end Low6960SharedChooseCut

end Merged_R6960Low6960SharedChooseCut

-- merged module R6960Low6960SharedTallyNew
section Merged_R6960Low6960SharedTallyNew

set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
namespace Low6960SharedTallyNew
noncomputable section
open P3 (K)
open K1_13 (Row Shape shape InBox chart)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_2_4 (oldEmbedding)
open K1_13_6_1_2 (VanishesTo cycleLength_ge_order pair_height)
open Low6960GeometryCut (CutInput)
open Low6960GeometryCut_2 (Branch)
open Low6960Prices (taylorLength)
open Low6960SharedPrice (Rate RateFits coord slope deficit weights surface surfaceScale)
open Low6960SharedTally (Data)
open MvPolynomial Finset
open scoped Polynomial BigOperators
open Low6960SharedChooseCut (minimal_pair mem_of_order)

variable {Γ : Finset K} {s : K→(Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

def tally (D : Data Γ s f Q l S) (F : Finset (Branch f Q l)) : ℕ :=
  ∑ b∈F,b.weight*(D.points b).card

private theorem scale_limit {x y e : ℕ} (h : ∀ N>0, N*x ≤ N*y+e) : x≤y := by
  by_contra! hh
  have hb := h (e+1) (by omega)
  have hc := Nat.mul_le_mul_left (e+1) (show y+1≤x by omega)
  rw [Nat.mul_add,Nat.mul_one] at hc
  omega

private theorem power_box (G : Row 4) (N : ℕ) :
    InBox (shape (G^N)) ⟨N*(shape G).chamber.b+3,N*(shape G).j+3,N*(shape G).t+1⟩ := by
  refine ⟨?_,?_,?_⟩
  · have h := weightedTotalDegree_pow_le (1 : Fin 4→ℕ) G N
    rw [weightedTotalDegree_one,weightedTotalDegree_one] at h
    exact (h.trans (Nat.mul_le_mul_left _ (le_max_left _ _))).trans (Nat.le_add_right _ _)
  · have h := weightedTotalDegree_pow_le (Fin.val : Fin 4→ℕ) G N
    rw [← K1_13_1.indexDegree_eq,← K1_13_1.indexDegree_eq] at h
    exact h.trans (Nat.le_add_right _ _)
  · have h := weightedTotalDegree_pow_le (Pi.single (3 : Fin 4) 1) G N
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans (Nat.le_add_right _ _)

private theorem power_order {P : Ideal GeoJets} [P.IsPrime] {G : Row 4} {n : ℕ}
    (h : VanishesTo P (toGeneric G) n) (N : ℕ) : VanishesTo P (toGeneric (G^N)) (N*n) := by
  let L := Localization.AtPrime P
  change algebraMap GeoJets L (toGeneric (G^N)) ∈ IsLocalRing.maximalIdeal L^(N*n)
  unfold toGeneric
  rw [map_pow,map_pow,Nat.mul_comm N n,pow_mul]
  exact Ideal.pow_mem_pow h _

private theorem four_count (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F⊆D.branches) (G : Row 4) (hproper : ¬ f∣G)
    (n amount : ℕ) (hn : 0<n) (hv : K1_13_8.Valid (shape f))
    (hcut : ∀ b∈F, ∃ h : (intersectionIdeal f G).IsMinimalPrime b.surface,
      @VanishesTo _ _ b.surface h.isPrime (toGeneric G) n)
    (hrate : surface .ordinary (shape f) (shape G).chamber ≤ 32*amount*n) :
    tally D F ≤ amount := by
  let W := weights .ordinary (shape f)
  have hbase : W.b*(shape G).chamber.b+W.j*(shape G).j+W.t*(shape G).t ≤ 32*amount*n := by
    rw [Low6960SharedPrice.surface_ordinary_eq_weights hv] at hrate
    change _ ≤ _ at hrate
    exact hrate
  have hall (N : ℕ) (hN : 0<N) :
      N*(32*n*tally D F) ≤ N*(32*n*amount)+(W.b*3+W.j*3+W.t) := by
    let q : Shape := ⟨N*(shape G).chamber.b+3,N*(shape G).j+3,N*(shape G).t+1⟩
    have hCh : K1_13_6_2_3.ChamberBox q := by
      have ht := (K1_13_7_1.shape_chamber G).2
      have hj := Nat.mul_le_mul_left N ht
      have hb := Nat.mul_le_mul_left N (le_max_right (shape G).b (shape G).j)
      refine ⟨?_,?_,?_⟩
      · change N*(shape G).j+3 ≤ N*max (shape G).b (shape G).j+3
        exact Nat.add_le_add_right hb _
      · change 3*(N*(shape G).t+1) ≤ N*(shape G).j+3
        rw [show 3*(N*(shape G).t+1)=N*(3*(shape G).t)+3 by ring]
        exact Nat.add_le_add_right hj _
      · dsimp [q]; omega
    have hp' : ¬ f∣G^N := fun h => hproper (input.small.1.prime.dvd_of_dvd_pow h)
    have hdata (b : Branch f Q l) (hb : b∈F) :
        ∃ h : (intersectionIdeal f (G^N)).IsMinimalPrime b.surface,
          ((N*n : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f (G^N)) b.surface h.isPrime := by
      obtain ⟨hP,horder⟩ := hcut b hb
      letI := hP.isPrime
      have hheight := pair_height (K1_13_6_3_6.toGeneric_ne_zero input.small.1.ne_zero)
        (K1_13_7_1.proper_generic f G input.small.1 hproper) hP
      have hmem : toGeneric f∈b.surface := hP.le (Ideal.subset_span (by simp))
      have ho := power_order horder N
      have hmin := minimal_pair input.small.1 hp' hheight hmem
        (mem_of_order (Nat.mul_pos hN hn) ho)
      exact ⟨hmin,cycleLength_ge_order hheight hmem ho⟩
    have hbound := Low6960SharedCycleFour.bound_with_cut K1_13_6_2_3_1.proof
      (K1_13_6_2_3_2.of_children
        K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
        K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
      (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
        (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
      f Q (G^N) l input.small hp' q hCh (power_box G N) (fun _ => N*n) F D.points
      (fun b hb => D.four input b (hF hb)) hdata
    have hnum : N*(32*n*tally D F) ≤ surface .ordinary (shape f) q := by
      have h := (le_div_iff₀ (by norm_num : (0:ℚ)<32)).mp hbound
      apply (Nat.cast_le (α := ℚ)).mp
      simpa only [tally,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,← Finset.mul_sum,
        mul_comm,mul_left_comm,mul_assoc, surface] using h
    have hlin : surface .ordinary (shape f) q =
        N*(W.b*(shape G).chamber.b+W.j*(shape G).j+W.t*(shape G).t)+(W.b*3+W.j*3+W.t) := by
      rw [Low6960SharedPrice.surface_ordinary_eq_weights hv]
      unfold q W
      ring
    rw [hlin] at hnum
    exact hnum.trans (by simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.add_le_add_right (Nat.mul_le_mul_left N hbase) (W.b*3+W.j*3+W.t))
  have hh := scale_limit hall
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos (by decide : 0<32) hn)
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh

theorem tilted_count (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F⊆D.branches) (G : Row 4) (hproper : ¬ f∣G)
    (n amount : ℕ) (hn : 0<n) (htilt : Low6960Prices.tiltedFits (shape f))
    (hcut : ∀ b∈F, ∃ h : (intersectionIdeal f G).IsMinimalPrime b.surface,
      (n : ℕ∞) ≤ cycleLength (intersectionIdeal f G) b.surface h.isPrime)
    (hrate : surface .tilted (shape f) (shape G).chamber ≤ 1920*amount*n) :
    tally D F ≤ amount := by
  let p := (shape f).chamber
  let q := (shape G).chamber
  have ht : 1≤p.t := input.small.2.1
  have hq : Low48BentLattice.Chamber (q,0) :=
    ⟨(K1_13_7_1.shape_chamber G).1,(K1_13_7_1.shape_chamber G).2,Nat.zero_le _⟩
  have hfamily := Low6960SharedBentCaps.caps_chamber (K1_13_7_1.shape_chamber f).1 ht htilt.1 hq
  let R := Low48BentCycle.rawFamily (Low6960SharedBentCaps.caps p q)
  let B := Low48BentCycle.capFamily (Low6960SharedBentCaps.caps p q)
  have h := Low6960SharedCycleBound.bound_with_cut (R := R) (B := B)
    Low6960SharedBentCaps.ordinary_doubled f Q G l input.small hproper (fun _ => n)
    (Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩)
    (Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩)
    F D.points (fun b hb => D.bent input (Low6960SharedBentCaps.chart q ht) b (hF hb)) hcut
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℚ)≤60*32)).trans
    (Low6960SharedBentCaps.ordinary_budget hfamily)
  have hnum : 1920*n*tally D F ≤ surface .tilted (shape f) (shape G).chamber := by
    norm_num only [show (60 : ℚ) * 32 = 1920 by norm_num] at hh
    apply (Nat.cast_le (α := ℚ)).mp
    simpa only [tally,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,← Finset.mul_sum, mul_comm,mul_left_comm,mul_assoc, surface] using hh
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos (by decide : 0<1920) hn)
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hnum.trans hrate

theorem count (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F⊆D.branches) (G : Row 4) (hproper : ¬ f∣G)
    (u : Rate) (hu : RateFits (shape f) u) (r a : ℕ) (hn : 0<r-u.split*a)
    (hv : K1_13_8.Valid (shape f))
    (hbound : ∀ i, a*coord (shape f) i+coord (shape G) i≤r*coord slope i)
    (hcut : ∀ b∈F, ∃ h : (intersectionIdeal f G).IsMinimalPrime b.surface,
      @VanishesTo _ _ b.surface h.isPrime (toGeneric G) (r-u.split*a) ∧
      ((r-u.split*a : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f G) b.surface h.isPrime) :
    tally D F ≤ u.amount := by
  have hfit i := (Nat.le_add_right _ _).trans (hbound i)
  have hb (i : Fin 3) : coord (shape G) i≤r*coord slope i-a*coord (shape f) i :=
    Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hbound i)
  have hbox : InBox (shape G) (deficit r a (shape f)) := ⟨hb 0,hb 1,hb 2⟩
  have hc := Low6960SharedPrice.chamber_bound hu r a hfit (shape G) hbox (K1_13_7_1.shape_chamber G).2
  have hcap : (weights u.kind (shape f)).b*(shape G).chamber.b +
      (weights u.kind (shape f)).j*(shape G).j + (weights u.kind (shape f)).t*(shape G).t ≤
      surfaceScale u.kind*u.amount*(r-u.split*a) :=
    Nat.le_of_mul_le_mul_left (by simpa only [Nat.mul_assoc] using hc) (by decide : 0<3)
  cases hkind : u.kind
  · apply four_count D input F hF G hproper _ _ hn hv
    · intro b hb
      obtain ⟨h,ho,_⟩ := hcut b hb
      exact ⟨h,ho⟩
    · rw [Low6960SharedPrice.surface_ordinary_eq_weights hv]
      rw [hkind] at hcap
      exact hcap
  · have ht := hu.1 hkind
    apply tilted_count D input F hF G hproper _ _ hn ht
    · intro b hb
      obtain ⟨h,_,hl⟩ := hcut b hb
      exact ⟨h,hl⟩
    · rw [Low6960SharedPrice.surface_tilted_eq_weights hv ht]
      rw [hkind] at hcap
      exact hcap

#print axioms count
end
end Low6960SharedTallyNew

end Merged_R6960Low6960SharedTallyNew
