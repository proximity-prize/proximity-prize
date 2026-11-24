import Mathlib.GroupTheory.CosetCover
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import ArkLib.Data.MvPolynomial.WeightedDegree.Products
import ArkLib.Data.MvPolynomial.WeightAtMost
import Mathlib.RingTheory.MvPolynomial.Homogeneous
set_option Elab.async false

-- merged module Gate61Coprime
section Merged_Gate61Coprime

set_option autoImplicit false

namespace Gate61Coprime

variable {K R : Type*} [Field K] [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Algebra K R]

def divisible (V : Submodule K R) (p : R) : Submodule K V where
  carrier := {v | p ∣ (v : R)}
  add_mem' := fun {a b} ha hb => by
    exact (dvd_add ha hb : p ∣ (a : R) + (b : R))
  zero_mem' := dvd_zero p
  smul_mem' := fun c v hv => by
    show p ∣ ((c • v : V) : R)
    rw [Submodule.coe_smul, Algebra.smul_def]
    exact Dvd.dvd.mul_left hv _

theorem mem_divisible {V : Submodule K R} {p : R} {v : V} :
    v ∈ divisible V p ↔ p ∣ (v : R) := Iff.rfl

theorem exists_relPrime_member [Infinite K] (V : Submodule K R)
    (hV : ∀ p : R, Irreducible p → ∃ v ∈ V, ¬ p ∣ v) {G₁ : R} (hG₁ : G₁ ≠ 0) :
    ∃ G₂ ∈ V, IsRelPrime G₁ G₂ := by
  classical
  let S : Finset R := (UniqueFactorizationMonoid.factors G₁).toFinset
  have hcover : ∃ v : V, ∀ p ∈ S, ¬ p ∣ (v : R) := by
    by_contra hcon
    push_neg at hcon
    have hall : ⋃ i : S, ((divisible V (i : R) : Submodule K V) : Set V) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro v
      obtain ⟨p, hp, hpv⟩ := hcon v
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hpv⟩
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hall
    have hirr : Irreducible (i : R) :=
      UniqueFactorizationMonoid.irreducible_of_factor _ (Multiset.mem_toFinset.mp i.2)
    obtain ⟨v, hvV, hv⟩ := hV _ hirr
    have hmem : (⟨v, hvV⟩ : V) ∈ divisible V (i : R) := by rw [hi]; trivial
    exact hv hmem
  obtain ⟨v, hv⟩ := hcover
  refine ⟨v, v.2, ?_⟩
  intro d hd1 hd2
  by_contra hnu
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hG₁ (zero_dvd_iff.mp hd1)
  obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hd0
  obtain ⟨q, hq, hpq⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hG₁ hp (hpd.trans hd1)
  have hqS : q ∈ S := Multiset.mem_toFinset.mpr hq
  apply hv q hqS
  exact (hpq.symm.dvd).trans (hpd.trans hd2)

end Gate61Coprime

end Merged_Gate61Coprime

-- merged module Gate61Gcd
section Merged_Gate61Gcd

set_option autoImplicit false

namespace Gate61Gcd

variable {K R : Type*} [Field K] [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Algebra K R]

theorem gcd_split (V : Submodule K R) (hV : V ≠ ⊥) :
    ∃ g : R, g ≠ 0 ∧ ∃ V' : Submodule K R, V' = V.comap (LinearMap.mulLeft K g) ∧
      (∀ v ∈ V, g ∣ v) ∧ (∀ p : R, Irreducible p → ∃ w ∈ V', ¬ p ∣ w) := by
  classical
  obtain ⟨v0, hv0, hv0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  let Q : Set R := {q | ∃ g : R, (∀ v ∈ V, g ∣ v) ∧ v0 = g * q}
  have hne : Q.Nonempty := ⟨v0, 1, fun v _ => one_dvd v, by simp⟩
  obtain ⟨q0, ⟨g0, hg0, hq0⟩, hmin⟩ := (wellFounded_dvdNotUnit (α := R)).has_min Q hne
  have hg0ne : g0 ≠ 0 := by
    rintro rfl
    exact hv0ne (by simpa using hq0)
  refine ⟨g0, hg0ne, V.comap (LinearMap.mulLeft K g0), rfl, hg0, ?_⟩
  intro p hp
  by_contra hcon
  push_neg at hcon
  have hall : ∀ v ∈ V, p * g0 ∣ v := by
    intro v hv
    obtain ⟨w, hw⟩ := hg0 v hv
    have : w ∈ V.comap (LinearMap.mulLeft K g0) := by
      show g0 * w ∈ V
      rw [← hw]; exact hv
    obtain ⟨u, hu⟩ := hcon w this
    exact ⟨u, by rw [hw, hu]; ring⟩
  have hq0mem : q0 ∈ V.comap (LinearMap.mulLeft K g0) := by
    show g0 * q0 ∈ V
    rw [← hq0]; exact hv0
  obtain ⟨q1, hq1⟩ := hcon q0 hq0mem
  have hq1Q : q1 ∈ Q := ⟨p * g0, hall, by rw [hq0, hq1]; ring⟩
  have hq0ne : q0 ≠ 0 := by
    rintro rfl
    exact hv0ne (by simpa using hq0)
  have hq1ne : q1 ≠ 0 := by
    rintro rfl
    exact hq0ne (by simpa using hq1)
  exact hmin q1 hq1Q ⟨hq1ne, p, hp.not_isUnit, by rw [hq1]; ring⟩

theorem split_power (f g : R) (hf : Irreducible f) (hg : g ≠ 0) :
    ∃ a : ℕ, ∃ h : R, g = f ^ a * h ∧ ¬ f ∣ h := by
  obtain ⟨n, c, hnd, hc⟩ := WfDvdMonoid.max_power_factor hg hf
  exact ⟨n, c, hc, hnd⟩

theorem two_general [Infinite K] (V' : Submodule K R)
    (hV : ∀ p : R, Irreducible p → ∃ v ∈ V', ¬ p ∣ v) {T : R} (hT : T ≠ 0) (hTn : ¬ IsUnit T) :
    ∃ G₁ ∈ V', ∃ G₂ ∈ V', G₁ ≠ 0 ∧ IsRelPrime T G₁ ∧ IsRelPrime G₁ G₂ := by
  obtain ⟨G₁, h₁, hrel₁⟩ := Gate61Coprime.exists_relPrime_member V' hV hT
  have hG : G₁ ≠ 0 := by
    rintro rfl
    exact hTn (hrel₁ (dvd_refl T) (dvd_zero T))
  obtain ⟨G₂, h₂, hrel₂⟩ := Gate61Coprime.exists_relPrime_member V' hV hG
  exact ⟨G₁, h₁, G₂, h₂, hG, hrel₁, hrel₂⟩

theorem finrank_split (V : Submodule K R) (g : R) (hg : g ≠ 0) (hdiv : ∀ v ∈ V, g ∣ v) :
    Module.finrank K (V.comap (LinearMap.mulLeft K g)) = Module.finrank K V := by
  have hinj : Function.Injective (LinearMap.mulLeft K g) := mul_right_injective₀ hg
  have hle : V ≤ LinearMap.range (LinearMap.mulLeft K g) := by
    intro v hv
    obtain ⟨w, hw⟩ := hdiv v hv
    exact ⟨w, hw.symm⟩
  have hmap : (V.comap (LinearMap.mulLeft K g)).map (LinearMap.mulLeft K g) = V := by
    rw [Submodule.map_comap_eq]; exact inf_eq_right.mpr hle
  have h := LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (V.comap (LinearMap.mulLeft K g)))
  rw [hmap] at h
  exact h

theorem split_power_nonunit (f g : R) (hf : ¬ IsUnit f) (hg : g ≠ 0) :
    ∃ a : ℕ, ∃ h : R, g = f ^ a * h ∧ ¬ f ∣ h := by
  obtain ⟨n, c, hnd, hc⟩ := WfDvdMonoid.max_power_factor' hg hf
  exact ⟨n, c, hc, hnd⟩

end Gate61Gcd

end Merged_Gate61Gcd

-- merged module Gate61Shape
section Merged_Gate61Shape

set_option autoImplicit false

namespace Gate61Shape

open MvPolynomial

variable {F : Type*} [Field F]

def wv : Fin 3 → (Fin 4 → ℕ) := ![fun _ => 1, Fin.val, Pi.single 3 1]

noncomputable def shp (i : Fin 3) (P : MvPolynomial (Fin 4) F) : ℕ := P.weightedTotalDegree (wv i)

theorem shp_mul {P Q : MvPolynomial (Fin 4) F} (hP : P ≠ 0) (hQ : Q ≠ 0) (i : Fin 3) :
    shp i (P * Q) = shp i P + shp i Q :=
  weightedTotalDegree_mul _ _ _ hP hQ

def freeSet (Y : Fin 3 → ℕ) : Set (Fin 4 →₀ ℕ) := {m | ∀ i, m.weight (wv i) ≤ Y i}

theorem freeSet_finite (Y : Fin 3 → ℕ) : (freeSet Y).Finite := by
  apply (Finsupp.finite_of_degree_le (Y 0)).subset
  intro m hm
  have h := hm 0
  have hd : m.degree = m.weight (wv 0) := by
    rw [Finsupp.degree_eq_weight_one]; rfl
  simpa [hd] using h

noncomputable def free (Y : Fin 3 → ℕ) : ℕ := (freeSet_finite Y).toFinset.card

theorem mem_restrict_iff {P : MvPolynomial (Fin 4) F} {Y : Fin 3 → ℕ} :
    P ∈ restrictSupport F (freeSet Y) ↔ ∀ i, shp i P ≤ Y i := by
  rw [mem_restrictSupport_iff]
  constructor
  · intro h i
    unfold shp weightedTotalDegree
    exact Finset.sup_le fun m hm => h hm i
  · intro h m hm i
    exact (Finset.le_sup (f := fun m => m.weight (wv i)) hm).trans (h i)

theorem finrank_restrict (Y : Fin 3 → ℕ) :
    Module.finrank F (restrictSupport F (freeSet Y)) = free Y := by
  have h : (↑(freeSet_finite Y).toFinset : Set (Fin 4 →₀ ℕ)) = freeSet Y := Set.Finite.coe_toFinset _
  rw [← h, finrank_restrictSupport_finset]; rfl

theorem dim_le_free [Infinite F] (V : Submodule F (MvPolynomial (Fin 4) F)) (g : MvPolynomial (Fin 4) F)
    (hg : g ≠ 0) (hdiv : ∀ v ∈ V, g ∣ v) (B : Fin 3 → ℕ) (hB : ∀ v ∈ V, ∀ i, shp i v ≤ B i) :
    Module.finrank F V ≤ free (fun i => B i - shp i g) := by
  classical
  have hsplit : Module.finrank F (V.comap (LinearMap.mulLeft F g)) = Module.finrank F V :=
    Gate61Gcd.finrank_split V g hg hdiv
  rw [← hsplit, ← finrank_restrict (F := F) (fun i => B i - shp i g)]
  haveI : Module.Finite F (restrictSupport F (freeSet (fun i => B i - shp i g))) :=
    restrictSupport_finite (freeSet_finite _)
  apply Submodule.finrank_mono
  intro w hw
  rw [mem_restrict_iff]
  intro i
  by_cases h0 : w = 0
  · subst h0; simp [shp, MvPolynomial.weightedTotalDegree]
  · have hmem : g * w ∈ V := hw
    have h1 := hB _ hmem i
    rw [shp_mul hg h0] at h1
    omega

theorem wt_apply (m : Fin 4 →₀ ℕ) : m.weight (wv 0) = m 0 + m 1 + m 2 + m 3 ∧
    m.weight (wv 1) = m 1 + 2 * m 2 + 3 * m 3 ∧ m.weight (wv 2) = m 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wv, Fin.sum_univ_four, Pi.single_apply]
  omega

theorem shp_valid {P : MvPolynomial (Fin 4) F} (hP : P ≠ 0) :
    shp 2 P ≤ shp 0 P ∧ 3 * shp 2 P ≤ shp 1 P ∧ shp 1 P ≤ 2 * shp 0 P + shp 2 P := by
  have hne : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  have le : ∀ i, ∀ m ∈ P.support, m.weight (wv i) ≤ shp i P := fun i m hm =>
    Finset.le_sup (f := fun m => m.weight (wv i)) hm
  obtain ⟨m2, hm2, e2⟩ := Finset.exists_mem_eq_sup P.support hne (fun m => m.weight (wv 2))
  obtain ⟨m1, hm1, e1⟩ := Finset.exists_mem_eq_sup P.support hne (fun m => m.weight (wv 1))
  have s2 : shp 2 P = m2.weight (wv 2) := e2
  have s1 : shp 1 P = m1.weight (wv 1) := e1
  have a2 := wt_apply m2
  have a1 := wt_apply m1
  have b0 := le 0 m2 hm2
  have b1 := le 1 m2 hm2
  have c0 := le 0 m1 hm1
  have c2 := le 2 m1 hm1
  rw [a2.1] at b0
  rw [a2.2.1] at b1
  rw [a1.1] at c0
  rw [a1.2.2] at c2
  rw [a2.2.2] at s2
  rw [a1.2.1] at s1
  refine ⟨by omega, by omega, by omega⟩

end Gate61Shape

end Merged_Gate61Shape
