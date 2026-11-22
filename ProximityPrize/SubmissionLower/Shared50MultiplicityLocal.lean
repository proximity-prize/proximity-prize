import ProximityPrize.SubmissionLower.Fast063
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import ProximityPrize.SubmissionLower.Shared50OrderDivision -- serialize candidate build

set_option maxHeartbeats 650000

namespace Shared50Multiplicity

noncomputable section

open Ideal IsLocalRing
open K1_13_6_3_6 (quotientMul quotientMul_injective quotientMul_exact)
open scoped ENat

variable {R : Type} [CommRing R]

abbrev quotientLength (I : Ideal R) : ℕ∞ := Module.length R (R ⧸ I)
private abbrev single (x : R) : Ideal R := Ideal.span {x}

private theorem length_step (I : Ideal R) (g : R) :
    quotientLength I = quotientLength (I.colon {g}) + quotientLength (I ⊔ single g) :=
  Module.length_eq_add_of_exact (quotientMul I g)
    (Submodule.factor (le_sup_left : I ≤ I ⊔ single g))
    (quotientMul_injective I g) (Submodule.factor_surjective le_sup_left) (quotientMul_exact I g)

theorem length_anti {I J : Ideal R} (h : I ≤ J) : quotientLength J ≤ quotientLength I :=
  Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)

private theorem length_top : quotientLength (⊤ : Ideal R) = 0 := by
  exact Module.length_eq_zero

theorem length_max [IsLocalRing R] : quotientLength (maximalIdeal R) = 1 := by
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

theorem nonprincipal_of_spanFinrank_two {m : Ideal R}
    (hr : m.spanFinrank = 2) (x : R) : m ≠ single x := by
  intro h
  have hh := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_singleton x)
  have hh' : (single x).spanFinrank ≤ 1 := by simpa only [Set.ncard_singleton] using hh
  rw [← h, hr] at hh'
  omega

theorem prime_parameters [IsDomain R] [IsLocalRing R] [UniqueFactorizationMonoid R]
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

theorem colon_power_left [IsDomain R] {m : Ideal R} {u v : R}
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

theorem higher_mod_left {m : Ideal R} {u v : R} (hm : m = single u ⊔ single v) (n : ℕ) :
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

theorem colon_power_mod_left [IsDomain R] {u v : R} (hu : Prime u) (hn : ¬ u ∣ v) (n : ℕ) :
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

theorem length_mod_left [IsDomain R] [IsLocalRing R] {u v : R}
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

/-- A two-dimensional regular local UFD has triangular maximal-ideal quotient lengths. -/
theorem length_max_power [IsDomain R] [IsLocalRing R] [UniqueFactorizationMonoid R]
    [IsNoetherianRing R] (hm2 : (maximalIdeal R).spanFinrank = 2) (n : ℕ) :
    quotientLength ((maximalIdeal R)^n) = triangle n := by
  obtain ⟨u,v,hm,hu,hn⟩ := prime_parameters hm2
  induction n with
  | zero => simp only [pow_zero, Ideal.one_eq_top, length_top, triangle, Nat.cast_zero]
  | succ n ih =>
    rw [length_step _ u, colon_power_left hm hu hn n, ih,
      higher_mod_left hm (n+1), length_mod_left hm hu hn, triangle]
    simp only [Nat.cast_add]

theorem triangle_add (a b : ℕ) : triangle (a+b) = triangle a + triangle b + a*b := by
  induction b with
  | zero => simp [triangle]
  | succ b ih =>
    rw [Nat.add_succ, triangle, triangle, ih, Nat.mul_succ]
    omega

theorem triangle_mul (a b : ℕ) :
    triangle (a+b+1) = triangle b + triangle a + (a+1)*(b+1) := by
  rw [triangle, triangle_add, Nat.add_mul, Nat.mul_add, one_mul, mul_one]
  omega

/-- The quotient by two local equations has length at least the product of
their prescribed vanishing orders. -/
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

end Shared50Multiplicity
