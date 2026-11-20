import ArkLib.Data.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
set_option linter.all false

section Compact_TriangularKernel

namespace ProximityPrize.SubmissionLower.TriangularKernel
noncomputable section
set_option autoImplicit false

variable {K : Type*} [Field K] {n : ℕ}
variable {V W : Fin n → Type*}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

theorem eq_zero_of_triangular
    (F : (∀ i, V i) →ₗ[K] (∀ i, W i))
    (D : ∀ i, V i →ₗ[K] W i)
    (hD : ∀ i, Function.Injective (D i))
    (hdiag : ∀ v i, (∀ j, j.val < i.val → v j = 0) →
      F v i = D i (v i))
    (v : ∀ i, V i) (hv : F v = 0) : v = 0 := by
  have hall : ∀ k : ℕ, ∀ i : Fin n, i.val = k → v i = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      apply hD i
      calc
        D i (v i) = F v i := (hdiag v i (fun j hj =>
          ih j.val (by omega) j rfl)).symm
        _ = 0 := congrFun hv i
        _ = D i 0 := (map_zero (D i)).symm
  funext i
  exact hall i.val i rfl

theorem injective_of_triangular
    (F : (∀ i, V i) →ₗ[K] (∀ i, W i))
    (D : ∀ i, V i →ₗ[K] W i)
    (hD : ∀ i, Function.Injective (D i))
    (hdiag : ∀ v i, (∀ j, j.val < i.val → v j = 0) →
      F v i = D i (v i)) : Function.Injective F := by
  intro v u h
  apply sub_eq_zero.mp
  apply eq_zero_of_triangular F D hD hdiag (v-u)
  rw [map_sub, h, sub_self]

end
end ProximityPrize.SubmissionLower.TriangularKernel

end Compact_TriangularKernel
section Compact_SecondJetBasis

namespace ProximityPrize.SubmissionLower.SecondJetBasis
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K B : Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
abbrev Jet (B : Type*) [CommRing B] := Polynomial (Polynomial B)

def lift : B →ₐ[K] Jet B :=
  (Polynomial.CAlgHom (R := K) (A := Polynomial B)).comp
    (Polynomial.CAlgHom (R := K) (A := B))

def factor (v : B) (r h a b : ℕ) : Jet B :=
  Polynomial.X^r *
    (Polynomial.C (Polynomial.X^h) *
      (Polynomial.C (Polynomial.C v) +
        Polynomial.X * Polynomial.C Polynomial.X)^a *
      Polynomial.C (Polynomial.C v)^b)

def term (v : B) (r h a b : ℕ) : B →ₗ[K] Jet B :=
  (LinearMap.mulLeft K (factor v r h a b)).comp lift.toLinearMap

variable {m s : ℕ}

def truncate : Jet B →ₗ[K] (Fin m → Fin s → B) :=
  LinearMap.pi (fun r => LinearMap.pi (fun h =>
    ((Polynomial.lcoeff B h.val).restrictScalars K).comp
      ((Polynomial.lcoeff (Polynomial B) r.val).restrictScalars K)))

theorem truncate_apply (P : Jet B) (r : Fin m) (h : Fin s) :
    truncate (K := K) P r h = (P.coeff r.val).coeff h.val := rfl

theorem exponent_budget (m r s h : ℕ) (hr : r ≤ m) (hh : h ≤ s) :
    let q := max ((m-r+1)/2) (m-r-(s-h))
    let a := min q (s-h)
    let b := q-a
    a+b = q ∧ h+a ≤ s ∧ m ≤ r+2*a+b := by
  dsimp
  omega

end
end ProximityPrize.SubmissionLower.SecondJetBasis

end Compact_SecondJetBasis
section Compact_SecondJetTruncate

namespace ProximityPrize.SubmissionLower.SecondJetBasis
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K B : Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]

def truncateOuter (m : ℕ) : Jet B →ₗ[K] Jet B :=
  (Polynomial.modByMonicHom (Polynomial.X^m : Jet B)).restrictScalars K

theorem truncateOuter_coeff (m : ℕ) (P : Jet B) (r : ℕ) (hr : r < m) :
    (truncateOuter (K := K) m P).coeff r = P.coeff r := by
  change (P %ₘ Polynomial.X^m).coeff r = P.coeff r
  have heq := Polynomial.modByMonic_add_div P (Polynomial.X^m)
  have hc := congrArg (fun Q : Jet B => Q.coeff r) heq
  simpa only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    if_neg (Nat.not_le.mpr hr), add_zero] using hc

theorem truncateOuter_coeff_high (m : ℕ) (P : Jet B) (r : ℕ) (hr : m ≤ r) :
    (truncateOuter (K := K) m P).coeff r = 0 := by
  change (P %ₘ Polynomial.X^m).coeff r = 0
  apply Polynomial.coeff_eq_zero_of_degree_lt
  apply (Polynomial.degree_modByMonic_lt P (Polynomial.monic_X_pow m)).trans_le
  simp only [Polynomial.degree_X_pow]
  exact_mod_cast hr

theorem truncate_truncateOuter {m s : ℕ} (P : Jet B) :
    truncate (K := K) (m := m) (s := s) (truncateOuter (K := K) m P) =
      truncate (K := K) (m := m) (s := s) P := by
  funext r h
  exact congrArg (fun Q : Polynomial B => Q.coeff h.val)
    (truncateOuter_coeff (K := K) m P r.val r.isLt)

theorem truncateOuter_contact {C : Type*} [CommRing C]
    (φ : Jet B →+* C) (t : C) (m : ℕ) (P : Jet B)
    (hε : φ Polynomial.X = t) (hP : t^m ∣ φ P) :
    t^m ∣ φ (truncateOuter (K := K) m P) := by
  have hd : t^m ∣ φ ((Polynomial.X^m : Jet B) * (P /ₘ Polynomial.X^m)) := by
    simp only [map_mul, map_pow, hε]
    exact dvd_mul_right _ _
  have heq := congrArg φ (Polynomial.modByMonic_add_div P (Polynomial.X^m))
  rw [map_add] at heq
  have hsub := dvd_sub hP hd
  rwa [← heq, add_sub_cancel_right] at hsub

end
end ProximityPrize.SubmissionLower.SecondJetBasis

end Compact_SecondJetTruncate
section Compact_SecondJetSupport

namespace ProximityPrize.SubmissionLower.SecondJetSupport
open scoped BigOperators Pointwise
open MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]
abbrev Poly := MvPolynomial (Fin 5) K

def Box (lo a r s t : ℕ) (P : Poly (K := K)) : Prop :=
  ∀ d ∈ P.support, lo ≤ d 0 ∧ d 2 ≤ a ∧ d 3 ≤ r ∧ d 1 ≤ s ∧
    d 1+d 2+d 3+d 4 ≤ t

def flatEquiv : Poly (K := K) ≃ₐ[K] SecondJetBasis.Jet (MvPolynomial (Fin 3) K) :=
  (MvPolynomial.finSuccEquiv K 4).trans (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquiv K 3))

theorem flatEquiv_X (j : Fin 5) :
    flatEquiv (K := K) (MvPolynomial.X j) =
      ![Polynomial.X, Polynomial.C Polynomial.X,
        Polynomial.C (Polynomial.C (MvPolynomial.X 0)),
        Polynomial.C (Polynomial.C (MvPolynomial.X 1)),
        Polynomial.C (Polynomial.C (MvPolynomial.X 2))] j := by
  have h0 : flatEquiv (K := K) (MvPolynomial.X 0) = Polynomial.X := by
    change Polynomial.map _ ((MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X 0)) = _
    rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]
  have hs (i : Fin 4) : flatEquiv (K := K) (MvPolynomial.X i.succ) =
      Polynomial.C ((MvPolynomial.finSuccEquiv K 3) (MvPolynomial.X i)) := by
    change Polynomial.map _ ((MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X i.succ)) = _
    rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
    rfl
  fin_cases j
  · exact h0
  · change flatEquiv (K := K) (MvPolynomial.X (0 : Fin 4).succ) = Polynomial.C Polynomial.X
    rw [hs, MvPolynomial.finSuccEquiv_X_zero]
  · change flatEquiv (K := K) (MvPolynomial.X ((0 : Fin 3).succ).succ) = _
    rw [hs, MvPolynomial.finSuccEquiv_X_succ]
    rfl
  · change flatEquiv (K := K) (MvPolynomial.X ((1 : Fin 3).succ).succ) = _
    rw [hs, MvPolynomial.finSuccEquiv_X_succ]
    rfl
  · change flatEquiv (K := K) (MvPolynomial.X ((2 : Fin 3).succ).succ) = _
    rw [hs, MvPolynomial.finSuccEquiv_X_succ]
    rfl

theorem flatEquiv_coeff (P : Poly (K := K)) (r h : ℕ) (d : Fin 3 →₀ ℕ) :
    AddMonoidAlgebra.coeff (((flatEquiv (K := K) P).coeff r).coeff h) d =
      AddMonoidAlgebra.coeff P ((d.cons h).cons r) := by
  simp only [flatEquiv, AlgEquiv.trans_apply, Polynomial.coe_mapAlgEquiv, Polynomial.coeff_map]
  change AddMonoidAlgebra.coeff (((MvPolynomial.finSuccEquiv K 3)
    (((MvPolynomial.finSuccEquiv K 4) P).coeff r)).coeff h) d = _
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.finSuccEquiv_coeff_coeff]

def truncFlat (m : ℕ) : Poly (K := K) →ₗ[K] Poly (K := K) :=
  (flatEquiv (K := K)).symm.toLinearMap.comp
    ((SecondJetBasis.truncateOuter (K := K) m).comp (flatEquiv (K := K)).toLinearMap)

theorem flatEquiv_truncFlat (m : ℕ) (P : Poly (K := K)) :
    flatEquiv (K := K) (truncFlat (K := K) m P) =
      SecondJetBasis.truncateOuter (K := K) m (flatEquiv (K := K) P) := by
  simp [truncFlat]

theorem coeff_truncFlat_cons (m r h : ℕ) (d : Fin 3 →₀ ℕ) (P : Poly (K := K)) :
    AddMonoidAlgebra.coeff (truncFlat (K := K) m P) ((d.cons h).cons r) =
      if r < m then AddMonoidAlgebra.coeff P ((d.cons h).cons r) else 0 := by
  rw [← flatEquiv_coeff, flatEquiv_truncFlat]
  by_cases hr : r < m
  · rw [if_pos hr, SecondJetBasis.truncateOuter_coeff m _ r hr, flatEquiv_coeff]
  · rw [if_neg hr, SecondJetBasis.truncateOuter_coeff_high m _ r (by omega)]
    simp

theorem support_truncFlat (m : ℕ) (P : Poly (K := K)) (d : Fin 5 →₀ ℕ)
    (hd : d ∈ (truncFlat (K := K) m P).support) : d 0 < m ∧ d ∈ P.support := by
  have heq : ((d.tail.tail).cons (d.tail 0)).cons (d 0) = d := by
    rw [Finsupp.cons_tail, Finsupp.cons_tail]
  have hne := MvPolynomial.mem_support_iff.mp hd
  rw [← heq, coeff_truncFlat_cons] at hne
  split_ifs at hne with h
  · refine ⟨h, MvPolynomial.mem_support_iff.mpr ?_⟩
    simpa only [heq] using hne
  · exact False.elim (hne rfl)

def Allowed (m L s1 s2 : ℕ) (d : Fin 5 →₀ ℕ) : Prop :=
  d 0 < m ∧ d 2 ≤ d 0 ∧ d 3 ≤ s1 ∧ d 1 ≤ s2 ∧ d 1+d 2+d 3+d 4 ≤ L

end
end ProximityPrize.SubmissionLower.SecondJetSupport

end Compact_SecondJetSupport
section Compact_SecondJetLocal

namespace ProximityPrize.SubmissionLower.SecondJetLocal
open scoped BigOperators
open SecondJetBasis SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]
abbrev Base := MvPolynomial (Fin 3) K
abbrev Target := Polynomial (MvPolynomial (Fin 4) K)

def baseEval : Base (K := K) →ₐ[K] Target (K := K) :=
  MvPolynomial.aeval ![
    Polynomial.C (MvPolynomial.X 2)-Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
      Polynomial.X^2*Polynomial.C (MvPolynomial.X 1),
    Polynomial.C (MvPolynomial.X 2), Polynomial.C (MvPolynomial.X 3)]

def innerEval : Polynomial (Base (K := K)) →ₐ[K] Target (K := K) :=
  Polynomial.eval₂AlgHom baseEval (Polynomial.C (MvPolynomial.X 0)) (fun _ => Commute.all _ _)

def contact : Jet (Base (K := K)) →ₐ[K] Target (K := K) :=
  Polynomial.eval₂AlgHom innerEval Polynomial.X (fun _ => Commute.all _ _)

@[simp] theorem contact_X : contact (K := K) Polynomial.X = Polynomial.X := by
  simp [contact]

@[simp] theorem contact_C_C (p : Base (K := K)) :
    contact (K := K) (Polynomial.C (Polynomial.C p)) = baseEval (K := K) p := by
  simp [contact, innerEval]

@[simp] theorem contact_C_X :
    contact (K := K) (Polynomial.C Polynomial.X) = Polynomial.C (MvPolynomial.X 0) := by
  simp [contact, innerEval]

def v : Base (K := K) := MvPolynomial.X 0-MvPolynomial.X 1

theorem v_ne_zero : v (K := K) ≠ 0 := by
  unfold v
  apply sub_ne_zero.mpr
  intro h
  have hh := MvPolynomial.X_injective h
  exact (by decide : (0 : Fin 3) ≠ 1) hh

theorem contact_v : contact (K := K) (Polynomial.C (Polynomial.C v)) =
    (Polynomial.X : Target (K := K)) * (-(Polynomial.C (MvPolynomial.X (0 : Fin 4)) : Target (K := K))+
      Polynomial.X*Polynomial.C (MvPolynomial.X 1)) := by
  rw [contact_C_C]
  simp only [v, map_sub, baseEval, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem contact_u : contact (K := K)
    (Polynomial.C (Polynomial.C v)+Polynomial.X*Polynomial.C Polynomial.X) =
      Polynomial.X^2*Polynomial.C (MvPolynomial.X 1) := by
  rw [map_add, map_mul, contact_v, contact_X, contact_C_X]
  ring

end
end ProximityPrize.SubmissionLower.SecondJetLocal

end Compact_SecondJetLocal
section Compact_FiniteMonomials

namespace ProximityPrize.SubmissionLower.FiniteMonomials
open scoped BigOperators
noncomputable section
set_option autoImplicit false
variable {K σ I : Type*} [Field K] [Fintype I]
local instance : DecidableEq σ := Classical.decEq σ
local instance : DecidableEq I := Classical.decEq I

def reconstruct (e : I → σ →₀ ℕ) : (I → K) →ₗ[K] MvPolynomial σ K :=
  ∑ i, (MvPolynomial.monomial (e i)).comp (LinearMap.proj i)

theorem reconstruct_apply (e : I → σ →₀ ℕ) (c : I → K) :
    reconstruct e c = ∑ i, MvPolynomial.monomial (e i) (c i) := by
  simp [reconstruct]

theorem coeff_reconstruct (e : I → σ →₀ ℕ) (he : Function.Injective e)
    (c : I → K) (i : I) : AddMonoidAlgebra.coeff (reconstruct e c) (e i) = c i := by
  classical
  rw [reconstruct_apply, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, he.eq_iff]
  simp

theorem reconstruct_injective (e : I → σ →₀ ℕ) (he : Function.Injective e) :
    Function.Injective (reconstruct (K := K) e) := by
  intro c d h
  funext i
  have hh := congrArg (AddMonoidAlgebra.coeff · (e i)) h
  simpa only [coeff_reconstruct e he] using hh

theorem coeff_reconstruct_of_notmem (e : I → σ →₀ ℕ) (c : I → K)
    (d : σ →₀ ℕ) (hd : d ∉ Set.range e) :
    AddMonoidAlgebra.coeff (reconstruct e c) d = 0 := by
  classical
  rw [reconstruct_apply, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [MvPolynomial.coeff_monomial, if_neg (fun h => hd ⟨i,h⟩)]

theorem mem_range_iff (e : I → σ →₀ ℕ) (he : Function.Injective e)
    (P : MvPolynomial σ K) : P ∈ (reconstruct (K := K) e).range ↔
      ∀ d ∈ P.support, d ∈ Set.range e := by
  classical
  constructor
  · rintro ⟨c,rfl⟩ d hd
    by_contra hn
    exact MvPolynomial.mem_support_iff.mp hd (coeff_reconstruct_of_notmem e c d hn)
  · intro h
    refine ⟨fun i => P.coeff (e i), ?_⟩
    ext d
    by_cases hd : d ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hd
      exact coeff_reconstruct e he _ i
    · rw [coeff_reconstruct_of_notmem e _ d hd]
      exact (MvPolynomial.notMem_support_iff.mp (fun hs => hd (h d hs))).symm

end
end ProximityPrize.SubmissionLower.FiniteMonomials

end Compact_FiniteMonomials
section Compact_SecondJetSpace

namespace ProximityPrize.SubmissionLower.SecondJetSpace
open scoped BigOperators
open SecondJetBasis SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def bound (m L s1 s2 : ℕ) : Fin 5 → ℕ := ![m,s2+1,m,s1+1,L+1]

def Index (m L s1 s2 : ℕ) :=
  {d : ∀ k, Fin (bound m L s1 s2 k) //
    (d 2).val ≤ (d 0).val ∧ (d 1).val+(d 2).val+(d 3).val+(d 4).val ≤ L}

instance (m L s1 s2 : ℕ) : Fintype (Index m L s1 s2) := by
  unfold Index
  infer_instance

def exponent {m L s1 s2 : ℕ} (d : Index m L s1 s2) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => (d.val k).val)

@[simp] theorem exponent_apply {m L s1 s2 : ℕ} (d : Index m L s1 s2) (k : Fin 5) :
    exponent d k = (d.val k).val := by simp [exponent]

theorem exponent_injective (m L s1 s2 : ℕ) :
    Function.Injective (exponent (m := m) (L := L) (s1 := s1) (s2 := s2)) := by
  intro d e h
  apply Subtype.ext
  funext k
  apply Fin.ext
  simpa only [exponent_apply] using congrArg (fun f : Fin 5 →₀ ℕ => f k) h

theorem exponent_allowed {m L s1 s2 : ℕ} (d : Index m L s1 s2) :
    Allowed m L s1 s2 (exponent d) := by
  have h0 : (d.val 0).val < m := (d.val 0).isLt
  have h1 : (d.val 1).val < s2+1 := (d.val 1).isLt
  have h3 : (d.val 3).val < s1+1 := (d.val 3).isLt
  simp only [Allowed, exponent_apply]
  exact ⟨h0,d.property.1,by omega,by omega,d.property.2⟩

theorem mem_range_exponent (m L s1 s2 : ℕ) (d : Fin 5 →₀ ℕ) :
    d ∈ Set.range (exponent (m := m) (L := L) (s1 := s1) (s2 := s2)) ↔
      Allowed m L s1 s2 d := by
  constructor
  · rintro ⟨e,rfl⟩
    exact exponent_allowed e
  · intro h
    dsimp only [Allowed] at h
    have hb : ∀ k, d k < bound m L s1 s2 k := by
      intro k
      fin_cases k
      · exact h.1
      · change d 1 < s2+1
        omega
      · change d 2 < m
        omega
      · change d 3 < s1+1
        omega
      · change d 4 < L+1
        omega
    let e : Index m L s1 s2 := ⟨fun k => ⟨d k,hb k⟩,h.2.1,h.2.2.2.2⟩
    refine ⟨e,?_⟩
    ext k
    simp [e, exponent]

def sourceMap (m L s1 s2 : ℕ) : (Index m L s1 s2 → K) →ₗ[K]
    Jet (MvPolynomial (Fin 3) K) :=
  (flatEquiv (K := K)).toLinearMap.comp (FiniteMonomials.reconstruct exponent)

def source (m L s1 s2 : ℕ) : Submodule K (Jet (MvPolynomial (Fin 3) K)) :=
  (sourceMap (K := K) m L s1 s2).range

instance source_finite (m L s1 s2 : ℕ) : FiniteDimensional K (source (K := K) m L s1 s2) := by
  unfold source
  infer_instance

end
end ProximityPrize.SubmissionLower.SecondJetSpace

end Compact_SecondJetSpace
section Compact_SecondJetGlobalSupport

namespace ProximityPrize.SubmissionLower.SecondJetGlobalSupport
open scoped BigOperators Pointwise
open MvPolynomial SecondJetSupport SecondJetBasis
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def LocalBound (B s L : ℕ) (P : Poly (K := K)) : Prop :=
  ∀ d ∈ P.support, d 2 ≤ d 0 ∧ d 1+d 3 ≤ B ∧ d 1 ≤ s ∧ d 1+d 2+d 3+d 4 ≤ L

theorem LocalBound.mono {B s L B' s' L' : ℕ} {P : Poly (K := K)}
    (h : LocalBound B s L P) (hB : B ≤ B') (hs : s ≤ s') (hL : L ≤ L') :
    LocalBound B' s' L' P := by
  intro d hd
  have hh := h d hd
  exact ⟨hh.1,hh.2.1.trans hB,hh.2.2.1.trans hs,hh.2.2.2.trans hL⟩

theorem LocalBound.mul {B s L B' s' L' : ℕ} {P Q : Poly (K := K)}
    (hP : LocalBound B s L P) (hQ : LocalBound B' s' L' Q) :
    LocalBound (B+B') (s+s') (L+L') (P*Q) := by
  intro d hd
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  have hp := hP u hu
  have hq := hQ v hv
  simp only [Finsupp.add_apply]
  omega

theorem LocalBound.add {B s L : ℕ} {P Q : Poly (K := K)}
    (hP : LocalBound B s L P) (hQ : LocalBound B s L Q) : LocalBound B s L (P+Q) := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hP d h
  · exact hQ d h

theorem local_C (c : K) : LocalBound 0 0 0 (MvPolynomial.C c : Poly (K := K)) := by
  intro d hd
  have hd0 : d = 0 := Finset.mem_singleton.mp (MvPolynomial.support_C_subset hd)
  subst d
  simp

theorem LocalBound.pow {B s L : ℕ} {P : Poly (K := K)}
    (hP : LocalBound B s L P) (n : ℕ) : LocalBound (n*B) (n*s) (n*L) (P^n) := by
  induction n with
  | zero => simpa using (local_C (K := K) 1)
  | succ n ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul hP

def localize (x u0 u1 : K) : Poly (K := K) →ₐ[K] Poly (K := K) :=
  MvPolynomial.aeval ![MvPolynomial.C x+MvPolynomial.X 0,MvPolynomial.X 1,
    MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4+
      MvPolynomial.X 0*MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]

theorem local_X (j : Fin 5) (hj : j ≠ 2) :
    LocalBound (if j=1 ∨ j=3 then 1 else 0) (if j=1 then 1 else 0)
      (if j=0 then 0 else 1) (MvPolynomial.X j : Poly (K := K)) := by
  intro d hd
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at hd
  subst d
  fin_cases j <;> norm_num [Finsupp.single_apply, Fin.ext_iff] at *

theorem local_epsilon_A : LocalBound 0 0 1
    (MvPolynomial.X 0*MvPolynomial.X 2 : Poly (K := K)) := by
  intro d hd
  rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul] at hd
  have hd' := MvPolynomial.support_monomial_subset hd
  have hd0 := Finset.mem_singleton.mp hd'
  subst d
  norm_num [Finsupp.add_apply, Finsupp.single_apply, Fin.ext_iff]

theorem localize_X (x u0 u1 : K) (j : Fin 5) :
    LocalBound (if j=1 ∨ j=3 then 1 else 0) (if j=1 then 1 else 0)
      (if j=0 then 0 else 1) (localize x u0 u1 (MvPolynomial.X j)) := by
  have hE : LocalBound 0 0 0 (MvPolynomial.X 0 : Poly (K := K)) := by
    simpa using local_X (K := K) 0 (by decide)
  have hZ : LocalBound 0 0 1 (MvPolynomial.X 4 : Poly (K := K)) := by
    simpa using local_X (K := K) 4 (by decide)
  fin_cases j
  · simpa [localize] using (local_C x).add hE
  · simpa [localize] using local_X (K := K) 1 (by decide)
  · have hU : LocalBound 0 0 1 (MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4 : Poly (K := K)) :=
      ((local_C u0).mono (by omega) (by omega) (by omega)).add
        ((local_C u1).mul hZ)
    simpa [localize] using hU.add (local_epsilon_A (K := K))
  · simpa [localize] using local_X (K := K) 3 (by decide)
  · simpa [localize] using hZ

theorem localize_monomial (x u0 u1 : K) (d : Fin 5 →₀ ℕ) (c : K) :
    LocalBound (d 1+d 3) (d 1) (d 1+d 2+d 3+d 4)
      (localize x u0 u1 (MvPolynomial.monomial d c)) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow,
      map_C]
    have h0 := (localize_X x u0 u1 0).pow (d 0)
    have h1 := (localize_X x u0 u1 1).pow (d 1)
    have h2 := (localize_X x u0 u1 2).pow (d 2)
    have h3 := (localize_X x u0 u1 3).pow (d 3)
    have h4 := (localize_X x u0 u1 4).pow (d 4)
    simpa [Nat.add_assoc] using (local_C c).mul (h0.mul (h1.mul (h2.mul (h3.mul h4))))
  · intro i
    simp

end
end ProximityPrize.SubmissionLower.SecondJetGlobalSupport

end Compact_SecondJetGlobalSupport
section Compact_SecondJetRank

namespace ProximityPrize.SubmissionLower.SecondJetRank
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetLocal SecondJetSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def q (m s2 r h : ℕ) := max ((m-r+1)/2) (m-r-(s2-h))
def a (m s2 r h : ℕ) := min (q m s2 r h) (s2-h)
def b (m s2 r h : ℕ) := q m s2 r h-a m s2 r h

theorem budgets (m s2 r h : ℕ) (hr : r ≤ m) (hh : h ≤ s2) :
    a m s2 r h+b m s2 r h=q m s2 r h ∧ h+a m s2 r h ≤ s2 ∧
      m ≤ r+2*a m s2 r h+b m s2 r h :=
  exponent_budget m r s2 h hr hh

def Block (m L s1 s2 r h : ℕ) :=
  {d : Fin 3 → Fin (L+1) //
    (d 0).val+q m s2 r h ≤ r ∧ (d 1).val+q m s2 r h ≤ s1 ∧
      (d 0).val+(d 1).val+(d 2).val+h+q m s2 r h ≤ L}

instance (m L s1 s2 r h : ℕ) : Fintype (Block m L s1 s2 r h) := by
  unfold Block
  infer_instance

def blockExponent {m L s1 s2 r h : ℕ} (d : Block m L s1 s2 r h) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => (d.val k).val)

@[simp] theorem blockExponent_apply {m L s1 s2 r h : ℕ}
    (d : Block m L s1 s2 r h) (k : Fin 3) : blockExponent d k = (d.val k).val := by
  simp [blockExponent]

theorem blockExponent_injective (m L s1 s2 r h : ℕ) :
    Function.Injective (blockExponent (m := m) (L := L) (s1 := s1) (s2 := s2) (r := r) (h := h)) := by
  intro d e hde
  apply Subtype.ext
  funext k
  apply Fin.ext
  simpa only [blockExponent_apply] using congrArg (fun f : Fin 3 →₀ ℕ => f k) hde

theorem block_monomial (m L s1 s2 r h : ℕ) (d : Block m L s1 s2 r h) :
    MvPolynomial.monomial (blockExponent d) (1 : K) =
      MvPolynomial.X 0^(d.val 0).val * MvPolynomial.X 1^(d.val 1).val *
        MvPolynomial.X 2^(d.val 2).val := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp [Fin.prod_univ_three]
  · intro i
    simp

def contactMap (m : ℕ) : Jet (Base (K := K)) →ₗ[K] Target (K := K) :=
  ((Polynomial.modByMonicHom (Polynomial.X^m : Target (K := K))).restrictScalars K).comp
    (contact (K := K)).toLinearMap

end
end ProximityPrize.SubmissionLower.SecondJetRank

end Compact_SecondJetRank
section Compact_SecondJetCounts

namespace ProximityPrize.SubmissionLower.SecondJetCounts
open scoped BigOperators
open SecondJetSpace SecondJetRank
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev BlockSumIndex (m L s1 s2 r h : ℕ) :=
  Σ i : Fin (r-q m s2 r h+1), Σ j : Fin (s1-q m s2 r h+1),
    Fin (L+1-h-q m s2 r h-i.val-j.val)

def blockEquiv (m L s1 s2 r h : ℕ) (hr : q m s2 r h ≤ r) (hs : q m s2 r h ≤ s1) :
    Block m L s1 s2 r h ≃ BlockSumIndex m L s1 s2 r h where
  toFun d := by
    have hd := d.property
    exact ⟨⟨(d.val 0).val,by omega⟩,⟨(d.val 1).val,by omega⟩,
      ⟨(d.val 2).val,by dsimp; omega⟩⟩
  invFun u := by
    rcases u with ⟨i,j,z⟩
    have hi := i.isLt
    have hj := j.isLt
    have hz := z.isLt
    let iv : Fin (L+1) := ⟨i.val,by omega⟩
    let jv : Fin (L+1) := ⟨j.val,by omega⟩
    let zv : Fin (L+1) := ⟨z.val,by omega⟩
    refine ⟨![iv,jv,zv],?_,?_,?_⟩
    · change i.val+q m s2 r h ≤ r
      omega
    · change j.val+q m s2 r h ≤ s1
      omega
    · change i.val+j.val+z.val+h+q m s2 r h ≤ L
      omega
  left_inv d := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k <;> rfl
  right_inv u := by
    rcases u with ⟨i,j,z⟩
    rfl

theorem card_block_of_le (m L s1 s2 r h : ℕ)
    (hr : q m s2 r h ≤ r) (hs : q m s2 r h ≤ s1) :
    Fintype.card (Block m L s1 s2 r h) =
      ∑ i : Fin (r-q m s2 r h+1), ∑ j : Fin (s1-q m s2 r h+1),
        (L+1-h-q m s2 r h-i.val-j.val) := by
  rw [Fintype.card_congr (blockEquiv m L s1 s2 r h hr hs)]
  simp [BlockSumIndex]

theorem card_block_of_not_le (m L s1 s2 r h : ℕ)
    (hq : ¬ (q m s2 r h ≤ r ∧ q m s2 r h ≤ s1)) :
    Fintype.card (Block m L s1 s2 r h) = 0 := by
  letI : IsEmpty (Block m L s1 s2 r h) := ⟨fun d => by have hd := d.property; omega⟩
  simp

def rectangle (A B C : ℕ) :=
  A*B*C-B*(A*(A-1)/2)-A*(B*(B-1)/2)

theorem sum_fin_val (n : ℕ) : (∑ i : Fin n, i.val) = n*(n-1)/2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]

theorem sum_rectangle (A B C : ℕ) (h : ∀ i : Fin A, ∀ j : Fin B, i.val+j.val ≤ C) :
    (∑ i : Fin A, ∑ j : Fin B, (C-i.val-j.val)) = rectangle A B C := by
  have hs : (∑ i : Fin A, ∑ j : Fin B, ((C-i.val-j.val)+i.val+j.val)) = A*(B*C) := by
    calc
      _ = ∑ _i : Fin A, ∑ _j : Fin B, C := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have hij := h i j
        omega
      _ = _ := by simp
  have hs' : (∑ i : Fin A, ∑ j : Fin B, (C-i.val-j.val)) +
      B*(A*(A-1)/2)+A*(B*(B-1)/2) = A*(B*C) := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum, sum_fin_val] using hs
  unfold rectangle
  rw [mul_assoc]
  omega

theorem card_block_closed (m L s1 s2 r h : ℕ) (hL : m+s1+s2 ≤ L)
    (hrm : r < m) (hhs : h ≤ s2) :
    Fintype.card (Block m L s1 s2 r h) =
      if q m s2 r h ≤ r ∧ q m s2 r h ≤ s1 then
        rectangle (r-q m s2 r h+1) (s1-q m s2 r h+1) (L+1-h-q m s2 r h)
      else 0 := by
  split_ifs with hq
  · rw [card_block_of_le m L s1 s2 r h hq.1 hq.2]
    apply sum_rectangle
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    omega
  · exact card_block_of_not_le m L s1 s2 r h hq

def kernelCell (m L s1 s2 r h : ℕ) : ℕ :=
  if q m s2 r h ≤ r ∧ q m s2 r h ≤ s1 then
    rectangle (r-q m s2 r h+1) (s1-q m s2 r h+1) (L+1-h-q m s2 r h)
  else 0

variable {K : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.SecondJetCounts

end Compact_SecondJetCounts
section Compact_SecondJetGlobalCounts

namespace ProximityPrize.SubmissionLower.SecondJetGlobalCounts
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem sum_range_square_mul_six (n : ℕ) :
    (∑ i ∈ Finset.range n, i^2)*6 = n*(n-1)*(2*n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    cases n with
    | zero => simp
    | succ n =>
      have h1 : 2*(n+1)-1 = 2*n+1 := by omega
      have h2 : 2*(n+1+1)-1 = 2*n+3 := by omega
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, h1] at ih
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, h2]
      nlinarith [ih]

theorem sum_fin_square (n : ℕ) :
    (∑ i : Fin n, i.val^2) = n*(n-1)*(2*n-1)/6 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i^2), ← sum_range_square_mul_six]
  exact (Nat.mul_div_cancel _ (by decide : 0 < 6)).symm

def weightedCell (q w C n : ℕ) : ℕ :=
  n*q*C+w*(n*(n-1)*(2*n-1)/6)-(q+w*C)*(n*(n-1)/2)

theorem sum_weighted_cell (q w C n : ℕ)
    (hq : ∀ y : Fin n, w*y.val ≤ q) (hC : ∀ y : Fin n, y.val ≤ C) :
    (∑ y : Fin n, (q-w*y.val)*(C-y.val)) = weightedCell q w C n := by
  have hcell : ∀ y : Fin n,
      (q-w*y.val)*(C-y.val)+(q+w*C)*y.val = q*C+w*y.val^2 := by
    intro y
    have hqy : q = q-w*y.val+w*y.val := (Nat.sub_add_cancel (hq y)).symm
    have hCy : C = C-y.val+y.val := (Nat.sub_add_cancel (hC y)).symm
    calc
      _ = (q-w*y.val)*(C-y.val)+((q-w*y.val+w*y.val)+w*(C-y.val+y.val))*y.val := by
        conv_lhs => arg 2; arg 1; rw [hqy, hCy]
      _ = (q-w*y.val+w*y.val)*(C-y.val+y.val)+w*y.val^2 := by ring
      _ = _ := by rw [← hqy, ← hCy]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun y _ => hcell y)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, SecondJetCounts.sum_fin_val, sum_fin_square] at hs
  unfold weightedCell
  rw [mul_comm n q, mul_assoc]
  omega

end
end ProximityPrize.SubmissionLower.SecondJetGlobalCounts

end Compact_SecondJetGlobalCounts
section Compact_SecondJetWeightedContact

namespace ProximityPrize.SubmissionLower.SecondJetWeightedContact
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {B C : Type*} [CommRing B] [CommRing C]

def V (a r : B) : Polynomial B := Polynomial.C (a-r)
def U (a r s : B) : Polynomial B :=
  V a r + Polynomial.X*Polynomial.C s
def J (a r s : B) : Polynomial B :=
  Polynomial.C r*V a r + Polynomial.X*Polynomial.C (a*s)

theorem J_eq (a r s : B) :
    J a r s = Polynomial.C r*U a r s +
      Polynomial.X*Polynomial.C s*V a r := by
  simp only [J, U, V, map_sub, map_mul]
  ring

theorem contact_J (a r s : B) (φ : Polynomial B →+* C) (ε : C)
    (hε : φ Polynomial.X = ε)
    (hU : ε^2 ∣ φ (U a r s)) (hV : ε ∣ φ (V a r)) :
    ε^2 ∣ φ (J a r s) := by
  obtain ⟨u, hu⟩ := hU
  obtain ⟨v, hv⟩ := hV
  refine ⟨φ (Polynomial.C r)*u + φ (Polynomial.C s)*v, ?_⟩
  rw [J_eq, map_add, map_mul, map_mul, map_mul, hε, hu, hv]
  ring

def family (a r s z : B) (ρ h u v i j ℓ : ℕ) : Polynomial B :=
  Polynomial.X^ρ * (Polynomial.C (s^h) *
    U a r s^(u-ℓ) * J a r s^ℓ * V a r^v *
    Polynomial.C (a^i*r^(j-ℓ)*z))

theorem family_contact (a r s z : B) (ρ h u v i j ℓ : ℕ)
    (hℓ : ℓ ≤ u) (φ : Polynomial B →+* C) (ε : C)
    (hε : φ Polynomial.X = ε)
    (hU : ε^2 ∣ φ (U a r s)) (hV : ε ∣ φ (V a r)) :
    ε^(ρ+2*u+v) ∣ φ (family a r s z ρ h u v i j ℓ) := by
  have hJ := contact_J a r s φ ε hε hU hV
  obtain ⟨cu, hu⟩ := hU
  obtain ⟨cv, hv⟩ := hV
  obtain ⟨cj, hj⟩ := hJ
  refine ⟨φ (Polynomial.C (s^h))*cu^(u-ℓ)*cj^ℓ*cv^v*
    φ (Polynomial.C (a^i*r^(j-ℓ)*z)), ?_⟩
  simp only [family, map_mul, map_pow, hε, hu, hv, hj, mul_pow]
  have he : ρ+2*u+v = ρ+2*(u-ℓ)+2*ℓ+v := by omega
  rw [he]
  simp only [pow_add, pow_mul]
  ring

theorem family_coeff_lt (a r s z : B) (ρ h u v i j ℓ d : ℕ)
    (hd : d < ρ) : (family a r s z ρ h u v i j ℓ).coeff d = 0 := by
  simp [family, Polynomial.coeff_X_pow_mul', Nat.not_le.mpr hd]

theorem family_coeff_self (a r s z : B) (ρ h u v i j ℓ : ℕ)
    (hu : ℓ ≤ u) (hj : ℓ ≤ j) :
    (family a r s z ρ h u v i j ℓ).coeff ρ =
      s^h*(a-r)^(u+v)*(a^i*r^j*z) := by
  obtain ⟨u', rfl⟩ := Nat.exists_eq_add_of_le hu
  obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hj
  simp only [family, Polynomial.coeff_X_pow_mul', Nat.sub_self, if_pos (le_refl ρ)]
  simp [Polynomial.coeff_zero_eq_eval_zero, U, J, V, pow_add]
  rw [mul_pow]
  ring

end
end ProximityPrize.SubmissionLower.SecondJetWeightedContact

end Compact_SecondJetWeightedContact
section Compact_SecondJetWeightedBasis

namespace ProximityPrize.SubmissionLower.SecondJetWeightedBasis
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetRank SecondJetLocal
open MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem C_smul_base (c : K) (v : Base (K := K)) :
    Polynomial.C (c • v) = c • (Polynomial.C v : Polynomial (Base (K := K))) :=
  map_smul (Polynomial.CAlgHom (R := K) (A := Base (K := K))) c v

def weightedTerm (r h a b : ℕ) (e : Fin 3 →₀ ℕ) : Jet (Base (K := K)) :=
  SecondJetWeightedContact.family
    (Polynomial.C (MvPolynomial.X 0)) (Polynomial.C (MvPolynomial.X 1))
    Polynomial.X (Polynomial.C (MvPolynomial.X 2^(e 2)))
    r h a b (e 0) (e 1) (min a (e 1))

theorem weightedTerm_coeff_lt (r h a b : ℕ) (e : Fin 3 →₀ ℕ)
    (d : ℕ) (hd : d < r) : (weightedTerm (K := K) r h a b e).coeff d = 0 :=
  SecondJetWeightedContact.family_coeff_lt _ _ _ _ _ _ _ _ _ _ _ _ hd

theorem weightedTerm_coeff_self (r h a b : ℕ) (e : Fin 3 →₀ ℕ) :
    (weightedTerm (K := K) r h a b e).coeff r = Polynomial.X^h *
      Polynomial.C (SecondJetLocal.v^(a+b)*MvPolynomial.monomial e (1 : K)) := by
  rw [weightedTerm, SecondJetWeightedContact.family_coeff_self _ _ _ _ _ _ _ _ _ _ _
    (min_le_left _ _) (min_le_right _ _)]
  have hm : MvPolynomial.monomial e (1 : K) =
      MvPolynomial.X 0^(e 0)*MvPolynomial.X 1^(e 1)*MvPolynomial.X 2^(e 2) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    · simp [Fin.prod_univ_three]
    · intro i; simp
  rw [hm]
  simp only [SecondJetLocal.v, map_sub, map_mul, map_pow, mul_assoc]

variable {m s : ℕ} {I : Fin m → Fin s → Type*} [∀ r h, Fintype (I r h)]
abbrev Parameters := ∀ r : Fin m, ∀ h : Fin s, I r h → K

def weightedMake (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) : Parameters (K := K) (I := I) →ₗ[K] Jet (Base (K := K)) :=
  ∑ r, ∑ h, ∑ i, LinearMap.smulRight
    (((LinearMap.proj i : (I r h → K) →ₗ[K] K).comp
      (LinearMap.proj h : (∀ h, I r h → K) →ₗ[K] (I r h → K))).comp (LinearMap.proj r : Parameters (K := K) (I := I) →ₗ[K] (∀ h, I r h → K)))
    (weightedTerm r.val h.val (a r h) (b r h) (e r h i))

theorem weightedMake_apply (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (p : Parameters (K := K) (I := I)) :
    weightedMake a b e p = ∑ r, ∑ h, ∑ i,
      p r h i • weightedTerm r.val h.val (a r h) (b r h) (e r h i) := by
  simp [weightedMake]

theorem weightedMake_initial (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (p : Parameters (K := K) (I := I)) (r : Fin m)
    (hp : ∀ j, j.val < r.val → p j = 0) :
    (weightedMake a b e p).coeff r.val = ∑ h, Polynomial.X^h.val *
      Polynomial.C (SecondJetLocal.v^(a r h+b r h)*FiniteMonomials.reconstruct (e r h) (p r h)) := by
  rw [weightedMake_apply, Polynomial.finsetSum_coeff, Finset.sum_eq_single r]
  · simp_rw [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, weightedTerm_coeff_self]
    apply Finset.sum_congr rfl
    intro h _
    rw [FiniteMonomials.reconstruct_apply, Finset.mul_sum, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hm : MvPolynomial.monomial (e r h i) (p r h i) =
        p r h i • MvPolynomial.monomial (e r h i) (1 : K) := by
      simpa only [smul_eq_mul, mul_one] using
        (map_smul (MvPolynomial.monomial (e r h i)) (p r h i) (1 : K))
    rw [hm]
    simp only [mul_smul_comm, C_smul_base]
  · intro j _ hj
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro i _
    by_cases hlt : j.val < r.val
    · simp [hp j hlt]
    · rw [weightedTerm_coeff_lt]
      · simp
      · have hne : j.val ≠ r.val := fun he => hj (Fin.ext he)
        omega
  · simp

theorem truncate_weightedMake_initial (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (p : Parameters (K := K) (I := I)) (r : Fin m)
    (hp : ∀ j, j.val < r.val → p j = 0) :
    truncate (K := K) (m := m) (s := s) (weightedMake a b e p) r =
      fun h => SecondJetLocal.v^(a r h+b r h)*FiniteMonomials.reconstruct (e r h) (p r h) := by
  funext h
  rw [truncate_apply, weightedMake_initial a b e p r hp, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Fin.val_inj]
  simp

theorem truncate_weightedMake_injective (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (he : ∀ r h, Function.Injective (e r h)) :
    Function.Injective ((truncate (K := K) (m := m) (s := s)).comp (weightedMake a b e)) := by
  let D : ∀ r : Fin m, (∀ h : Fin s, I r h → K) →ₗ[K] (Fin s → Base (K := K)) := fun r =>
    LinearMap.pi (fun h => (LinearMap.mulLeft K (SecondJetLocal.v^(a r h+b r h))).comp
      ((FiniteMonomials.reconstruct (e r h)).comp (LinearMap.proj h)))
  apply TriangularKernel.injective_of_triangular _ D
  · intro r p q hpq
    funext h i
    have hh := congrFun hpq h
    change SecondJetLocal.v^(a r h+b r h)*FiniteMonomials.reconstruct (e r h) (p h) =
      SecondJetLocal.v^(a r h+b r h)*FiniteMonomials.reconstruct (e r h) (q h) at hh
    have hz := mul_left_cancel₀ (pow_ne_zero _ (SecondJetLocal.v_ne_zero (K := K))) hh
    exact congrFun (FiniteMonomials.reconstruct_injective (e r h) (he r h) hz) i
  · intro p r hp
    exact truncate_weightedMake_initial a b e p r hp

theorem truncateOuter_weightedMake_injective (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (he : ∀ r h, Function.Injective (e r h)) :
    Function.Injective ((truncateOuter (K := K) m).comp (weightedMake a b e)) := by
  intro p q hpq
  apply truncate_weightedMake_injective a b e he
  have hh := congrArg (truncate (K := K) (m := m) (s := s)) hpq
  simpa only [LinearMap.comp_apply, truncate_truncateOuter] using hh

theorem finite_source_rank {T : Type*} [AddCommGroup T] [Module K T]
    (W : Submodule K (Jet (Base (K := K)))) [FiniteDimensional K W]
    (f : W →ₗ[K] T) (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (he : ∀ r h, Function.Injective (e r h))
    (hW : ∀ p, truncateOuter (K := K) m (weightedMake a b e p) ∈ W)
    (hzero : ∀ p, f ⟨truncateOuter (K := K) m (weightedMake a b e p), hW p⟩ = 0) :
    Module.finrank K f.range + (∑ r : Fin m, ∑ h : Fin s, Fintype.card (I r h)) ≤
      Module.finrank K W := by
  let g := (truncateOuter (K := K) m).comp (weightedMake a b e)
  have hg : Function.Injective g := truncateOuter_weightedMake_injective a b e he
  let gw : Parameters (K := K) (I := I) →ₗ[K] W := g.codRestrict W hW
  let gk : Parameters (K := K) (I := I) →ₗ[K] f.ker := gw.codRestrict f.ker hzero
  have hi : Function.Injective gk := by
    intro p q hpq
    apply hg
    exact congrArg (fun x : f.ker => (x.val : Jet (Base (K := K)))) hpq
  letI : AddCommGroup W := inferInstance
  letI : Module K W := W.module
  letI : FiniteDimensional K f.ker := inferInstance
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have hsum := f.finrank_range_add_finrank_ker
  have hd : Module.finrank K (Parameters (K := K) (I := I)) =
      ∑ r : Fin m, ∑ h : Fin s, Fintype.card (I r h) := by
    simp [Parameters, Module.finrank_pi_fintype]
  rw [hd] at hdim
  omega

end
end ProximityPrize.SubmissionLower.SecondJetWeightedBasis

end Compact_SecondJetWeightedBasis
section Compact_SecondJetWeightedSupport

namespace ProximityPrize.SubmissionLower.SecondJetWeightedSupport
open scoped BigOperators Pointwise
open MvPolynomial SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

def weight (w : Fin 5 → ℤ) (e : Fin 5 →₀ ℕ) : ℤ := ∑ j, (e j : ℤ)*w j

def LinearBound (w : Fin 5 → ℤ) (b : ℤ) (P : Poly (K := K)) : Prop :=
  ∀ e ∈ P.support, weight w e ≤ b

theorem weight_add (w : Fin 5 → ℤ) (e f : Fin 5 →₀ ℕ) :
    weight w (e+f) = weight w e+weight w f := by
  simp [weight, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem LinearBound.mono {w : Fin 5 → ℤ} {b c : ℤ} {P : Poly (K := K)}
    (h : LinearBound w b P) (hbc : b ≤ c) : LinearBound w c P :=
  fun e he => (h e he).trans hbc

theorem LinearBound.mul {w : Fin 5 → ℤ} {b c : ℤ} {P Q : Poly (K := K)}
    (hP : LinearBound w b P) (hQ : LinearBound w c Q) : LinearBound w (b+c) (P*Q) := by
  intro e he
  obtain ⟨f,hf,g,hg,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q he)
  rw [weight_add]
  exact add_le_add (hP f hf) (hQ g hg)

theorem LinearBound.add {w : Fin 5 → ℤ} {b : ℤ} {P Q : Poly (K := K)}
    (hP : LinearBound w b P) (hQ : LinearBound w b Q) : LinearBound w b (P+Q) := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hP e h
  · exact hQ e h

theorem LinearBound.neg {w : Fin 5 → ℤ} {b : ℤ} {P : Poly (K := K)}
    (hP : LinearBound w b P) : LinearBound w b (-P) := by
  simpa only [LinearBound, MvPolynomial.support_neg] using hP

theorem linear_one (w : Fin 5 → ℤ) : LinearBound w 0 (1 : Poly (K := K)) := by
  intro e he
  simp only [MvPolynomial.support_one, Finset.mem_singleton] at he
  subst e
  simp [weight]

theorem LinearBound.pow {w : Fin 5 → ℤ} {b : ℤ} {P : Poly (K := K)}
    (hP : LinearBound w b P) (n : ℕ) : LinearBound w ((n : ℤ)*b) (P^n) := by
  induction n with
  | zero => simpa using linear_one (K := K) w
  | succ n ih => simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hP

theorem linear_X (w : Fin 5 → ℤ) (j : Fin 5) :
    LinearBound w (w j) (MvPolynomial.X j : Poly (K := K)) := by
  intro e he
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at he
  subst e
  simp [weight, Finsupp.single_apply]

def weightedVector (r h a b i j z l : ℕ) : Poly (K := K) :=
  MvPolynomial.X 0^r * MvPolynomial.X 1^h *
    (MvPolynomial.X 2-MvPolynomial.X 3+MvPolynomial.X 0*MvPolynomial.X 1)^(a-l) *
    (MvPolynomial.X 3*(MvPolynomial.X 2-MvPolynomial.X 3)+
      MvPolynomial.X 0*MvPolynomial.X 2*MvPolynomial.X 1)^l *
    (MvPolynomial.X 2-MvPolynomial.X 3)^b *
    MvPolynomial.X 2^i * MvPolynomial.X 3^(j-l) * MvPolynomial.X 4^z

theorem weightedVector_bound (w : Fin 5 → ℤ) (r h a b i j z l : ℕ) :
    LinearBound w ((r : ℤ)*w 0+(h : ℤ)*w 1+
      ((a-l : ℕ) : ℤ)*max (max (w 2) (w 3)) (w 0+w 1)+
      (l : ℤ)*max (w 3+max (w 2) (w 3)) (w 0+w 2+w 1)+
      (b : ℤ)*max (w 2) (w 3)+(i : ℤ)*w 2+((j-l : ℕ) : ℤ)*w 3+(z : ℤ)*w 4)
      (weightedVector (K := K) r h a b i j z l) := by
  have hE := linear_X (K := K) w 0
  have hS := linear_X (K := K) w 1
  have hA := linear_X (K := K) w 2
  have hR := linear_X (K := K) w 3
  have hZ := linear_X (K := K) w 4
  have hV : LinearBound w (max (w 2) (w 3))
      (MvPolynomial.X 2-MvPolynomial.X 3 : Poly (K := K)) := by
    rw [sub_eq_add_neg]
    exact (hA.mono (le_max_left _ _)).add (hR.neg.mono (le_max_right _ _))
  have hU := (hV.mono (le_max_left _ (w 0+w 1))).add
    ((hE.mul hS).mono (le_max_right _ _))
  have hJ := ((hR.mul hV).mono (le_max_left _ (w 0+w 2+w 1))).add
    (((hE.mul hA).mul hS).mono (le_max_right _ _))
  exact (((((((hE.pow r).mul (hS.pow h)).mul (hU.pow (a-l))).mul (hJ.pow l)).mul
    (hV.pow b)).mul (hA.pow i)).mul (hR.pow (j-l))).mul (hZ.pow z)

theorem weightedVector_support (r h a b i j z l : ℕ) (hla : l ≤ a) (hlj : l ≤ j)
    (e : Fin 5 →₀ ℕ) (he : e ∈ (weightedVector (K := K) r h a b i j z l).support) :
    r ≤ e 0 ∧ e 2 ≤ i+a+b ∧ e 3 ≤ j+a+b ∧ h ≤ e 1 ∧ e 1 ≤ h+a ∧
      e 1+e 2+e 3 ≤ i+j+h+a+b ∧ e 1+e 2+e 3+e 4 ≤ i+j+h+a+b+z ∧
      2*e 1+e 3 ≤ 2*h+2*a+b+j-l := by
  have h0 := weightedVector_bound (K := K) ![-1,0,0,0,0] r h a b i j z l e he
  have hA := weightedVector_bound (K := K) ![0,0,1,0,0] r h a b i j z l e he
  have hR := weightedVector_bound (K := K) ![0,0,0,1,0] r h a b i j z l e he
  have hSlo := weightedVector_bound (K := K) ![0,-1,0,0,0] r h a b i j z l e he
  have hShi := weightedVector_bound (K := K) ![0,1,0,0,0] r h a b i j z l e he
  have hM := weightedVector_bound (K := K) ![0,1,1,1,0] r h a b i j z l e he
  have hT := weightedVector_bound (K := K) ![0,1,1,1,1] r h a b i j z l e he
  have hB := weightedVector_bound (K := K) ![0,2,0,1,0] r h a b i j z l e he
  norm_num [weight, Fin.sum_univ_five, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] at h0 hA hR hSlo hShi hM hT hB
  omega

end
end ProximityPrize.SubmissionLower.SecondJetWeightedSupport

end Compact_SecondJetWeightedSupport
section Compact_SecondJetWeightedLocal

namespace ProximityPrize.SubmissionLower.SecondJetWeightedLocal
open SecondJetBasis SecondJetSupport SecondJetLocal SecondJetWeightedBasis
open SecondJetWeightedSupport MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem flatEquiv_weightedVector (r h a b : ℕ) (e : Fin 3 →₀ ℕ) :
    flatEquiv (K := K) (weightedVector (K := K) r h a b (e 0) (e 1) (e 2) (min a (e 1))) =
      weightedTerm (K := K) r h a b e := by
  simp only [weightedVector, map_mul, map_pow, map_add, map_sub, flatEquiv_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  simp only [weightedTerm, SecondJetWeightedContact.family, SecondJetWeightedContact.U,
    SecondJetWeightedContact.V, SecondJetWeightedContact.J, map_mul, map_pow, map_add, map_sub]
  ring

theorem weightedTerm_vanishes (m r h a b : ℕ) (e : Fin 3 →₀ ℕ)
    (horder : m ≤ r+2*a+b) :
    Polynomial.X^m ∣ contact (K := K) (weightedTerm (K := K) r h a b e) := by
  apply (pow_dvd_pow Polynomial.X horder).trans
  unfold weightedTerm
  apply SecondJetWeightedContact.family_contact _ _ _ _ _ _ _ _ _ _ _
    (min_le_left _ _) (contact (K := K)).toRingHom Polynomial.X contact_X
  · have hu : (Polynomial.X : Target (K := K))^2 ∣ contact (K := K)
        (Polynomial.C (Polynomial.C SecondJetLocal.v)+Polynomial.X*Polynomial.C Polynomial.X) :=
      ⟨Polynomial.C (MvPolynomial.X 1), contact_u⟩
    simpa only [SecondJetWeightedContact.U, SecondJetWeightedContact.V,
      SecondJetLocal.v, map_sub, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hu
  · have hv : (Polynomial.X : Target (K := K)) ∣
        contact (K := K) (Polynomial.C (Polynomial.C SecondJetLocal.v)) := by
      rw [contact_v]
      exact dvd_mul_right _ _
    simpa only [SecondJetWeightedContact.V, SecondJetLocal.v, map_sub, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hv

end
end ProximityPrize.SubmissionLower.SecondJetWeightedLocal

end Compact_SecondJetWeightedLocal
section Compact_SecondJetRelaxedSpace

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedSpace
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetWeightedSupport SecondJetWeightedLocal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def Index (m L B s U : ℕ) (caps : ℕ → ℕ) :=
  {d : SecondJetSpace.Index m L B s // 2*(d.val 1).val+(d.val 3).val ≤ B ∧
    (d.val 1).val+(d.val 2).val+(d.val 3).val ≤ U ∧
    (d.val 1).val+(d.val 2).val+(d.val 3).val ≤ caps (d.val 1).val}

instance (m L B s U : ℕ) (caps : ℕ → ℕ) : Fintype (Index m L B s U caps) := by
  unfold Index
  infer_instance

def exponent {m L B s U : ℕ} {caps : ℕ → ℕ} (d : Index m L B s U caps) : Fin 5 →₀ ℕ :=
  SecondJetSpace.exponent d.val

theorem exponent_injective (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Function.Injective (exponent (m := m) (L := L) (B := B) (s := s) (U := U) (caps := caps)) :=
  (SecondJetSpace.exponent_injective m L B s).comp Subtype.val_injective

theorem mem_range_exponent (m L B s U : ℕ) (caps : ℕ → ℕ) (d : Fin 5 →₀ ℕ) :
    d ∈ Set.range (exponent (m := m) (L := L) (B := B) (s := s) (U := U) (caps := caps)) ↔
      Allowed m L B s d ∧ 2*d 1+d 3 ≤ B ∧ d 1+d 2+d 3 ≤ U ∧ d 1+d 2+d 3 ≤ caps (d 1) := by
  constructor
  · rintro ⟨e,rfl⟩
    exact ⟨SecondJetSpace.exponent_allowed e.val,e.property⟩
  · rintro ⟨hd, hrs⟩
    obtain ⟨e,he⟩ := (SecondJetSpace.mem_range_exponent m L B s d).mpr hd
    have hrs' : 2*(e.val 1).val+(e.val 3).val ≤ B ∧ (e.val 1).val+(e.val 2).val+(e.val 3).val ≤ U ∧ (e.val 1).val+(e.val 2).val+(e.val 3).val ≤ caps (e.val 1).val := by
      simpa only [← he, SecondJetSpace.exponent_apply] using hrs
    exact ⟨⟨e,hrs'⟩,he⟩

def sourceMap (m L B s U : ℕ) (caps : ℕ → ℕ) : (Index m L B s U caps → K) →ₗ[K]
    Jet (MvPolynomial (Fin 3) K) :=
  (flatEquiv (K := K)).toLinearMap.comp (FiniteMonomials.reconstruct exponent)

def source (m L B s U : ℕ) (caps : ℕ → ℕ) : Submodule K (Jet (MvPolynomial (Fin 3) K)) :=
  (sourceMap (K := K) m L B s U caps).range

instance source_finite (m L B s U : ℕ) (caps : ℕ → ℕ) : FiniteDimensional K (source (K := K) m L B s U caps) := by
  unfold source
  infer_instance

theorem sourceMap_injective (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Function.Injective (sourceMap (K := K) m L B s U caps) :=
  (flatEquiv (K := K)).injective.comp
    (FiniteMonomials.reconstruct_injective _ (exponent_injective m L B s U caps))

theorem finrank_source (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Module.finrank K (source (K := K) m L B s U caps) = Fintype.card (Index m L B s U caps) := by
  unfold source
  rw [← (LinearEquiv.ofInjective (sourceMap (K := K) m L B s U caps)
    (sourceMap_injective m L B s U caps)).finrank_eq]
  simp

theorem mem_source_iff (m L B s U : ℕ) (caps : ℕ → ℕ) (P : Jet (MvPolynomial (Fin 3) K)) :
    P ∈ source (K := K) m L B s U caps ↔
      ∀ d ∈ ((flatEquiv (K := K)).symm P).support,
        Allowed m L B s d ∧ 2*d 1+d 3 ≤ B ∧ d 1+d 2+d 3 ≤ U ∧ d 1+d 2+d 3 ≤ caps (d 1) := by
  have hm : P ∈ source (K := K) m L B s U caps ↔
      (flatEquiv (K := K)).symm P ∈ (FiniteMonomials.reconstruct (K := K)
        (exponent (m := m) (L := L) (B := B) (s := s) (U := U) (caps := caps))).range := by
    constructor
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h := congrArg (flatEquiv (K := K)).symm hc
      simpa [sourceMap] using h
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h := congrArg (flatEquiv (K := K)) hc
      simpa [sourceMap] using h
  rw [hm, FiniteMonomials.mem_range_iff _ (exponent_injective m L B s U caps)]
  simp only [mem_range_exponent]

theorem truncated_weightedTerm_mem (m L B s U : ℕ) (caps : ℕ → ℕ)
    (r h a b : ℕ) (e : Fin 3 →₀ ℕ)
    (hi : e 0+a+b ≤ r) (hS : h+a ≤ s)
    (hB : 2*h+2*a+b+e 1-min a (e 1) ≤ B)
    (hU : e 0+e 1+h+a+b ≤ U)
    (hL : e 0+e 1+h+a+b+e 2 ≤ L)
    (hcaps : ∀ j, h ≤ j → j ≤ h+a → e 0+e 1+h+a+b ≤ caps j) :
    truncateOuter (K := K) m (SecondJetWeightedBasis.weightedTerm r h a b e) ∈
      source (K := K) m L B s U caps := by
  rw [← flatEquiv_weightedVector, ← flatEquiv_truncFlat, mem_source_iff]
  simp only [AlgEquiv.symm_apply_apply]
  intro d hd
  have ht := support_truncFlat m _ d hd
  obtain ⟨h0,hA,hR,hlo,hhi,hM,hT,hRS⟩ := weightedVector_support r h a b
    (e 0) (e 1) (e 2) (min a (e 1)) (min_le_left _ _) (min_le_right _ _) d ht.2
  refine ⟨?_,hRS.trans hB,hM.trans hU,hM.trans (hcaps (d 1) hlo hhi)⟩
  dsimp only [Allowed]
  exact ⟨ht.1,by omega,by omega,by omega,hT.trans hL⟩

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedSpace

end Compact_SecondJetRelaxedSpace
section Compact_SecondJetRelaxedSourceCounts

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedSourceCounts
open scoped BigOperators
open SecondJetRelaxedSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev SourceSumIndex (m L B s U : ℕ) :=
  Σ r : Fin m, Σ h : Fin (s+1), Σ i : Fin (r.val+1), Σ j : Fin (B-2*h.val+1),
    Fin (if h.val+i.val+j.val ≤ U then L+1-h.val-i.val-j.val else 0)

def sourceEquiv (m L B s U : ℕ) (caps : ℕ → ℕ) (hsB : 2*s ≤ B)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Index m L B s U caps ≃ SourceSumIndex m L B s U where
  toFun d := by
    have hi := d.val.property.1
    have ht := d.val.property.2
    have hd := d.property
    refine ⟨d.val.val 0,d.val.val 1,⟨(d.val.val 2).val,by omega⟩,
      ⟨(d.val.val 3).val,by change (d.val.val 3).val < B-2*(d.val.val 1).val+1; omega⟩,
      ⟨(d.val.val 4).val,?_⟩⟩
    change (d.val.val 4).val <
      if (d.val.val 1).val+(d.val.val 2).val+(d.val.val 3).val ≤ U then
        L+1-(d.val.val 1).val-(d.val.val 2).val-(d.val.val 3).val else 0
    rw [if_pos hd.2.1]
    omega
  invFun u := by
    rcases u with ⟨r,h,i,j,z⟩
    have hh := h.isLt
    have hi := i.isLt
    have hj := j.isLt
    have hz := z.isLt
    have hU : h.val+i.val+j.val ≤ U := by
      by_contra hn
      simp only [if_neg hn] at hz
      omega
    simp only [if_pos hU] at hz
    let iv : Fin m := ⟨i.val,by have hr := r.isLt; omega⟩
    let jv : Fin (B+1) := ⟨j.val,by omega⟩
    let zv : Fin (L+1) := ⟨z.val,by omega⟩
    let d : ∀ k, Fin (SecondJetSpace.bound m L B s k) :=
      Fin.cases r (Fin.cases h (Fin.cases iv (Fin.cases jv (Fin.cases zv (fun i => Fin.elim0 i)))))
    refine ⟨⟨d,?_,?_⟩,?_,?_,?_⟩
    · change i.val ≤ r.val
      omega
    · change h.val+i.val+j.val+z.val ≤ L
      omega
    · change 2*h.val+j.val ≤ B
      omega
    · exact hU
    · exact hU.trans (hcaps h.val (by omega))
  left_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k <;> rfl
  right_inv u := by
    rcases u with ⟨r,h,i,j,z⟩
    rfl

theorem card_source (m L B s U : ℕ) (caps : ℕ → ℕ) (hsB : 2*s ≤ B)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Fintype.card (Index m L B s U caps) =
      ∑ r : Fin m, ∑ h : Fin (s+1), ∑ i : Fin (r.val+1), ∑ j : Fin (B-2*h.val+1),
        if h.val+i.val+j.val ≤ U then L+1-h.val-i.val-j.val else 0 := by
  rw [Fintype.card_congr (sourceEquiv m L B s U caps hsB hcaps)]
  simp [SourceSumIndex]



end
end ProximityPrize.SubmissionLower.SecondJetRelaxedSourceCounts

end Compact_SecondJetRelaxedSourceCounts
section Compact_SecondJetRelaxedRank

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedRank
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetLocal SecondJetRelaxedSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

def q (m s r h : ℕ) := max ((m-r+1)/2) (m-r-(s-h))
def a (m s r h : ℕ) := m-r-q m s r h
def b (m s r h : ℕ) := q m s r h-a m s r h

theorem budgets (m s r h : ℕ) (hr : r ≤ m) (hh : h ≤ s) :
    a m s r h+b m s r h = q m s r h ∧ h+a m s r h ≤ s ∧
      r+2*a m s r h+b m s r h = m := by
  dsimp [a,b,q]
  omega

def Block (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ) :=
  {e : Fin 3 → Fin (L+1) //
    (e 0).val+q m s r h ≤ r ∧ (e 1).val+q m s r h+2*h ≤ B ∧
    m-r+2*h ≤ B ∧ (e 0).val+(e 1).val+h+q m s r h ≤ U ∧
    (e 0).val+(e 1).val+h+q m s r h+(e 2).val ≤ L ∧
    ∀ j : Fin (a m s r h+1),
      (e 0).val+(e 1).val+h+q m s r h ≤ caps (h+j.val)}

instance (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ) :
    Fintype (Block m L B s U caps r h) := by
  unfold Block
  infer_instance

def exponent {m L B s U : ℕ} {caps : ℕ → ℕ} {r h : ℕ}
    (e : Block m L B s U caps r h) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => (e.val j).val)

@[simp] theorem exponent_apply {m L B s U : ℕ} {caps : ℕ → ℕ} {r h : ℕ}
    (e : Block m L B s U caps r h) (j : Fin 3) : exponent e j = (e.val j).val := by
  simp [exponent]

theorem exponent_injective (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ) :
    Function.Injective (exponent (m := m) (L := L) (B := B) (s := s) (U := U)
      (caps := caps) (r := r) (h := h)) := by
  intro e f hef
  apply Subtype.ext
  funext j
  apply Fin.ext
  simpa only [exponent_apply] using congrArg (fun g : Fin 3 →₀ ℕ => g j) hef

abbrev Parameters (m L B s U : ℕ) (caps : ℕ → ℕ) :=
  ∀ r : Fin m, ∀ h : Fin (s+1), Block m L B s U caps r.val h.val → K

def make (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Parameters (K := K) m L B s U caps →ₗ[K] Jet (Base (K := K)) :=
  (truncateOuter (K := K) m).comp (SecondJetWeightedBasis.weightedMake
    (fun r h => a m s r.val h.val) (fun r h => b m s r.val h.val)
    (fun _ _ => exponent))

theorem make_mem_source (m L B s U : ℕ) (caps : ℕ → ℕ)
    (p : Parameters (K := K) m L B s U caps) :
    make m L B s U caps p ∈ source (K := K) m L B s U caps := by
  simp only [make, LinearMap.comp_apply, SecondJetWeightedBasis.weightedMake_apply, map_sum, map_smul]
  apply Submodule.sum_mem
  intro r _
  apply Submodule.sum_mem
  intro h _
  apply Submodule.sum_mem
  intro e _
  apply Submodule.smul_mem
  have hb := budgets m s r.val h.val (Nat.le_of_lt r.isLt) (Nat.le_of_lt_succ h.isLt)
  have he := e.property
  apply truncated_weightedTerm_mem
  · simp only [exponent_apply]
    omega
  · exact hb.2.1
  · simp only [exponent_apply]
    omega
  · simp only [exponent_apply]
    omega
  · simp only [exponent_apply]
    omega
  · intro j hj hj'
    have hd := he.2.2.2.2.2 (⟨j-h.val, by omega⟩ : Fin (a m s r.val h.val+1))
    simp only [exponent_apply]
    dsimp at hd
    have hjj : h.val+(j-h.val)=j := by omega
    rw [hjj] at hd
    omega

def restrictedMap (m L B s U : ℕ) (caps : ℕ → ℕ) :
    source (K := K) m L B s U caps →ₗ[K] Target (K := K) :=
  (SecondJetRank.contactMap (K := K) m).comp (source (K := K) m L B s U caps).subtype

theorem make_zero (m L B s U : ℕ) (caps : ℕ → ℕ)
    (p : Parameters (K := K) m L B s U caps) :
    SecondJetRank.contactMap (K := K) m (make m L B s U caps p) = 0 := by
  change contact (K := K) (make m L B s U caps p) %ₘ Polynomial.X^m = 0
  apply (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mpr
  change Polynomial.X^m ∣ contact (K := K) (truncateOuter (K := K) m _)
  apply truncateOuter_contact (K := K) (contact (K := K)).toRingHom Polynomial.X m _ contact_X
  change Polynomial.X^m ∣ contact (K := K) _
  rw [SecondJetWeightedBasis.weightedMake_apply, map_sum]
  apply Finset.dvd_sum
  intro r _
  rw [map_sum]
  apply Finset.dvd_sum
  intro h _
  rw [map_sum]
  apply Finset.dvd_sum
  intro e _
  rw [map_smul, Algebra.smul_def]
  apply dvd_mul_of_dvd_right
  apply SecondJetWeightedLocal.weightedTerm_vanishes
  exact le_of_eq (budgets m s r.val h.val (Nat.le_of_lt r.isLt)
    (Nat.le_of_lt_succ h.isLt)).2.2.symm

theorem local_rank_bound (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Module.finrank K (restrictedMap (K := K) m L B s U caps).range +
      (∑ r : Fin m, ∑ h : Fin (s+1), Fintype.card (Block m L B s U caps r.val h.val)) ≤
        Fintype.card (Index m L B s U caps) := by
  have h := SecondJetWeightedBasis.finite_source_rank
    (source (K := K) m L B s U caps) (restrictedMap (K := K) m L B s U caps)
    (fun r h => a m s r.val h.val) (fun r h => b m s r.val h.val)
    (fun _ _ => exponent) (fun r h => exponent_injective m L B s U caps r.val h.val)
    (make_mem_source m L B s U caps) (make_zero m L B s U caps)
  rwa [finrank_source] at h

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedRank

end Compact_SecondJetRelaxedRank
section Compact_SecondJetRelaxedKernelCounts

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedKernelCounts
open scoped BigOperators
open SecondJetRelaxedRank
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

abbrev BlockSumIndex (m L B s U r h : ℕ) :=
  Σ i : Fin (r-q m s r h+1), Σ j : Fin (B-2*h-q m s r h+1),
    Fin (if h+q m s r h+i.val+j.val ≤ U then L+1-h-q m s r h-i.val-j.val else 0)

def blockEquiv (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ)
    (hrm : r ≤ m) (hhs : h ≤ s)
    (hr : q m s r h ≤ r) (hB : m-r+2*h ≤ B)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Block m L B s U caps r h ≃ BlockSumIndex m L B s U r h where
  toFun d := by
    have hd := d.property
    refine ⟨⟨(d.val 0).val,by omega⟩,⟨(d.val 1).val,by omega⟩,
      ⟨(d.val 2).val,?_⟩⟩
    change (d.val 2).val < if h+q m s r h+(d.val 0).val+(d.val 1).val ≤ U then
      L+1-h-q m s r h-(d.val 0).val-(d.val 1).val else 0
    rw [if_pos (by omega)]
    omega
  invFun u := by
    rcases u with ⟨i,j,z⟩
    have hi := i.isLt
    have hj := j.isLt
    have hz := z.isLt
    have hU : h+q m s r h+i.val+j.val ≤ U := by
      by_contra hn
      simp only [if_neg hn] at hz
      omega
    simp only [if_pos hU] at hz
    have hb := budgets m s r h hrm hhs
    let iv : Fin (L+1) := ⟨i.val,by omega⟩
    let jv : Fin (L+1) := ⟨j.val,by omega⟩
    let zv : Fin (L+1) := ⟨z.val,by omega⟩
    refine ⟨![iv,jv,zv],?_,?_,?_,?_,?_,?_⟩
    · change i.val+q m s r h ≤ r
      omega
    · change j.val+q m s r h+2*h ≤ B
      omega
    · exact hB
    · change i.val+j.val+h+q m s r h ≤ U
      omega
    · change i.val+j.val+h+q m s r h+z.val ≤ L
      omega
    · intro t
      change i.val+j.val+h+q m s r h ≤ caps (h+t.val)
      have ht := t.isLt
      have hc := hcaps (h+t.val) (by omega)
      omega
  left_inv d := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k <;> rfl
  right_inv u := by
    rcases u with ⟨i,j,z⟩
    rfl

theorem card_block_of_le (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ)
    (hrm : r ≤ m) (hhs : h ≤ s)
    (hr : q m s r h ≤ r) (hB : m-r+2*h ≤ B)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Fintype.card (Block m L B s U caps r h) =
      ∑ i : Fin (r-q m s r h+1), ∑ j : Fin (B-2*h-q m s r h+1),
        if h+q m s r h+i.val+j.val ≤ U then L+1-h-q m s r h-i.val-j.val else 0 := by
  rw [Fintype.card_congr (blockEquiv m L B s U caps r h hrm hhs hr hB hcaps)]
  simp [BlockSumIndex]

theorem card_block_of_not_le (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ)
    (hq : ¬ (q m s r h ≤ r ∧ m-r+2*h ≤ B)) :
    Fintype.card (Block m L B s U caps r h) = 0 := by
  letI : IsEmpty (Block m L B s U caps r h) := ⟨fun d => by have hd := d.property; omega⟩
  simp





end
end ProximityPrize.SubmissionLower.SecondJetRelaxedKernelCounts

end Compact_SecondJetRelaxedKernelCounts
section Compact_SecondJetRelaxedGlobalSupport

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalSupport
open scoped BigOperators
open MvPolynomial SecondJetSupport SecondJetBasis SecondJetGlobalSupport
open SecondJetWeightedSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem linear_C (w : Fin 5 → ℤ) (c : K) : LinearBound w 0 (MvPolynomial.C c) := by
  intro e he
  have he0 : e = 0 := Finset.mem_singleton.mp (MvPolynomial.support_C_subset he)
  subst e
  simp [weight]

theorem localize_X_bound (w : Fin 5 → ℤ) (hw0 : w 0 = 0) (hw4 : w 4 = 0)
    (hw2 : 0 ≤ w 2) (x u0 u1 : K) (j : Fin 5) :
    LinearBound w (w j) (localize x u0 u1 (MvPolynomial.X j)) := by
  have hE := linear_X (K := K) w 0
  have hZ := linear_X (K := K) w 4
  fin_cases j
  · simpa [localize, hw0] using (linear_C w x).add (hE.mono (by omega))
  · simpa [localize] using linear_X (K := K) w 1
  · have hU : LinearBound w (w 2)
        (MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4 : Poly (K := K)) :=
      ((linear_C w u0).mono hw2).add (((linear_C w u1).mul hZ).mono (by omega))
    have hA := linear_X (K := K) w 2
    simpa [localize] using hU.add ((hE.mul hA).mono (by omega))
  · simpa [localize] using linear_X (K := K) w 3
  · simpa [localize] using hZ

theorem localize_monomial_bound (w : Fin 5 → ℤ) (hw0 : w 0 = 0) (hw4 : w 4 = 0)
    (hw2 : 0 ≤ w 2) (x u0 u1 : K) (e : Fin 5 →₀ ℕ) (c : K) :
    LinearBound w (weight w e) (localize x u0 u1 (MvPolynomial.monomial e c)) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow, map_C]
    have h0 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 0).pow (e 0)
    have h1 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 1).pow (e 1)
    have h2 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 2).pow (e 2)
    have h3 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 3).pow (e 3)
    have h4 := (localize_X_bound w hw0 hw4 hw2 x u0 u1 4).pow (e 4)
    simpa [weight, Fin.sum_univ_five, add_assoc] using
      (linear_C w c).mul (h0.mul (h1.mul (h2.mul (h3.mul h4))))
  · intro i
    simp

theorem localize_support (x u0 u1 : K) (e d : Fin 5 →₀ ℕ) (c : K)
    (hd : d ∈ (localize x u0 u1 (MvPolynomial.monomial e c)).support) :
    d 1 = e 1 ∧ 2*d 1+d 3 ≤ 2*e 1+e 3 ∧ d 1+d 2+d 3 ≤ e 1+e 2+e 3 := by
  have hs := localize_monomial_bound ![0,1,0,0,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  have hl := localize_monomial_bound ![0,-1,0,0,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  have hB := localize_monomial_bound ![0,2,0,1,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  have hM := localize_monomial_bound ![0,1,1,1,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  norm_num [weight, Fin.sum_univ_five, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four] at hs hl hB hM
  omega



end
end ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalSupport

end Compact_SecondJetRelaxedGlobalSupport
section Compact_SecondJetRelaxedGlobalMap

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalMap
open scoped BigOperators
open SecondJetSupport SecondJetBasis SecondJetGlobalSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I N : Type*} [Field K] [Fintype I] [Fintype N]

def rankBound (m L B s U : ℕ) (caps : ℕ → ℕ) : ℕ :=
  Fintype.card (SecondJetRelaxedSpace.Index m L B s U caps) -
    ∑ r : Fin m, ∑ h : Fin (s+1),
      Fintype.card (SecondJetRelaxedRank.Block m L B s U caps r.val h.val)

theorem local_rank_le_count (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Module.finrank K (SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps).range ≤
      rankBound m L B s U caps := by
  have hh := SecondJetRelaxedRank.local_rank_bound (K := K) m L B s U caps
  unfold rankBound
  omega



end
end ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalMap

end Compact_SecondJetRelaxedGlobalMap
section Compact_SecondJetRelaxedGlobalIndex

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalIndex
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def budget (D : ℕ → ℕ) (w h r : ℕ) := D h-(w-2)*h-(w-1)*r
def yCount (D : ℕ → ℕ) (w U h r : ℕ) :=
  min ((budget D w h r-1)/w+1) (U+1-h-r)
abbrev Index (D : ℕ → ℕ) (w L B s U : ℕ) :=
  Σ h : Fin (s+1), Σ r : Fin (B-2*h.val+1), Σ y : Fin (yCount D w U h.val r.val),
    Fin (budget D w h.val r.val-w*y.val) × Fin (L+1-h.val-r.val-y.val)

def exponent {D : ℕ → ℕ} {w L B s U : ℕ} (i : Index D w L B s U) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![i.2.2.2.1.val,i.1.val,i.2.2.1.val,i.2.1.val,i.2.2.2.2.val]

theorem exponent_injective (D : ℕ → ℕ) (w L B s U : ℕ) :
    Function.Injective (exponent (D := D) (w := w) (L := L) (B := B) (s := s) (U := U)) := by
  rintro ⟨h,r,y,x,z⟩ ⟨h',r',y',x',z'⟩ he
  have hv : ∀ k : Fin 5, ![x.val,h.val,y.val,r.val,z.val] k =
      ![x'.val,h'.val,y'.val,r'.val,z'.val] k := by
    intro k
    simpa [exponent] using congrArg (fun d : Fin 5 →₀ ℕ => d k) he
  have hh : h = h' := Fin.ext (hv 1)
  subst h'
  have hr : r = r' := Fin.ext (hv 3)
  subst r'
  have hy : y = y' := Fin.ext (hv 2)
  subst y'
  have hx : x = x' := Fin.ext (hv 0)
  have hz : z = z' := Fin.ext (hv 4)
  subst x'
  subst z'
  rfl

theorem exponent_bounds (D : ℕ → ℕ) (w L B s U : ℕ) (hsB : 2*s ≤ B)
    (i : Index D w L B s U) :
    2*exponent i 1+exponent i 3 ≤ B ∧ exponent i 1 ≤ s ∧
      exponent i 1+exponent i 2+exponent i 3 ≤ U ∧
      exponent i 1+exponent i 2+exponent i 3+exponent i 4 ≤ L ∧
      exponent i 0+w*exponent i 2+(w-1)*exponent i 3+(w-2)*exponent i 1 < D (exponent i 1) := by
  rcases i with ⟨h,r,y,x,z⟩
  have hh := h.isLt
  have hr := r.isLt
  have hy := y.isLt
  have hx := x.isLt
  have hz := z.isLt
  simp only [budget] at hx
  simp only [yCount] at hy
  simp [exponent]
  omega

theorem card_index (D : ℕ → ℕ) (w L B s U : ℕ) :
    Fintype.card (Index D w L B s U) =
      ∑ h : Fin (s+1), ∑ r : Fin (B-2*h.val+1), ∑ y : Fin (yCount D w U h.val r.val),
        (budget D w h.val r.val-w*y.val)*(L+1-h.val-r.val-y.val) := by
  simp [Index]

variable {K N : Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalIndex

end Compact_SecondJetRelaxedGlobalIndex
section Compact_SecondJetRelaxedGlobalCounts

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalCounts
open scoped BigOperators
open SecondJetRelaxedGlobalIndex
open SecondJetGlobalCounts (weightedCell sum_weighted_cell)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem y_weight_le (D : ℕ → ℕ) (w U h r : ℕ) (y : Fin (yCount D w U h r)) :
    w*y.val ≤ budget D w h r := by
  have hy : y.val ≤ (budget D w h r-1)/w := by
    have hh := y.isLt
    unfold yCount at hh
    omega
  calc
    w*y.val ≤ w*((budget D w h r-1)/w) := Nat.mul_le_mul_left w hy
    _ ≤ budget D w h r-1 := by
      simpa only [mul_comm] using Nat.div_mul_le_self (budget D w h r-1) w
    _ ≤ budget D w h r := Nat.sub_le _ _

def coefficientCount (D : ℕ → ℕ) (w L B s U : ℕ) : ℕ :=
  ∑ h : Fin (s+1), ∑ r : Fin (B-2*h.val+1),
    weightedCell (budget D w h.val r.val) w (L+1-h.val-r.val) (yCount D w U h.val r.val)

theorem card_index_closed (D : ℕ → ℕ) (w L B s U : ℕ) (hUL : U ≤ L) :
    Fintype.card (Index D w L B s U) = coefficientCount D w L B s U := by
  rw [card_index]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro r _
  apply sum_weighted_cell
  · exact y_weight_le D w U h.val r.val
  · intro y
    have hy := y.isLt
    unfold yCount at hy
    omega

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalCounts

end Compact_SecondJetRelaxedGlobalCounts



namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetRelaxedGlobalIndex
open SecondJetSupport

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2200000

abbrev AuxiliaryIndex (D : ℕ → ℕ) (w B s U : ℕ) :=
  Σ h : Fin (s+1), Σ r : Fin (B-2*h.val+1),
    Σ y : Fin (yCount D w U h.val r.val), Fin (budget D w h.val r.val-w*y.val)

private def auxiliaryExponent {D : ℕ → ℕ} {w B s U : ℕ}
    (i : AuxiliaryIndex D w B s U) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![i.2.2.2.val,i.1.val,i.2.2.1.val,i.2.1.val,0]

private theorem auxiliaryExponent_injective (D : ℕ → ℕ) (w B s U : ℕ) :
    Function.Injective (auxiliaryExponent (D := D) (w := w) (B := B) (s := s) (U := U)) := by
  rintro ⟨h,r,y,x⟩ ⟨h',r',y',x'⟩ he
  have hv : ∀ k : Fin 5, ![x.val,h.val,y.val,r.val,0] k =
      ![x'.val,h'.val,y'.val,r'.val,0] k := by
    intro k
    simpa [auxiliaryExponent] using congrArg (fun d : Fin 5 →₀ ℕ => d k) he
  have hh : h = h' := Fin.ext (hv 1)
  subst h'
  have hr : r = r' := Fin.ext (hv 3)
  subst r'
  have hy : y = y' := Fin.ext (hv 2)
  subst y'
  have hx : x = x' := Fin.ext (hv 0)
  subst x'
  rfl

theorem card_auxiliaryIndex (D : ℕ → ℕ) (w B s U : ℕ) :
    Fintype.card (AuxiliaryIndex D w B s U) =
      ∑ h : Fin (s+1), ∑ r : Fin (B-2*h.val+1), ∑ y : Fin (yCount D w U h.val r.val),
        (budget D w h.val r.val-w*y.val) := by
  simp [AuxiliaryIndex]

abbrev NormalizedIndex (D : ℕ → ℕ) (w wQ L B s U q : ℕ) :=
  Index D w L B s U ⊕
    (Σ j : Fin q, AuxiliaryIndex (fun h => D h-wQ*(j.val+1)) w B s (U-(j.val+1)))

private def normalizedSlot {D : ℕ → ℕ} {w wQ L B s U q : ℕ}
    (i : NormalizedIndex D w wQ L B s U q) : ℕ × (Fin 5 →₀ ℕ) :=
  match i with
  | Sum.inl v => (0, exponent v)
  | Sum.inr ⟨j,v⟩ => (j.val+1, auxiliaryExponent v)

private theorem normalizedSlot_injective (D : ℕ → ℕ) (w wQ L B s U q : ℕ) :
    Function.Injective
      (normalizedSlot (D := D) (w := w) (wQ := wQ) (L := L) (B := B) (s := s) (U := U) (q := q)) := by
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact congrArg Sum.inl (exponent_injective D w L B s U (congrArg Prod.snd hij))
    | inr j =>
      have h := congrArg Prod.fst hij
      change 0 = j.1.val+1 at h
      omega
  | inr i =>
    cases j with
    | inl j =>
      have h := congrArg Prod.fst hij
      change i.1.val+1 = 0 at h
      omega
    | inr j =>
      obtain ⟨p,i⟩ := i
      obtain ⟨c,j⟩ := j
      have hpc : p = c := by
        have h := congrArg Prod.fst hij
        change p.val+1 = c.val+1 at h
        apply Fin.ext
        omega
      subst c
      have hij' := auxiliaryExponent_injective (fun h => D h-wQ*(p.val+1))
        w B s (U-(p.val+1)) (congrArg Prod.snd hij)
      subst j
      rfl

def normalizedExponent {D : ℕ → ℕ} {w wQ L B s U q : ℕ}
    (i : NormalizedIndex D w wQ L B s U q) : Fin 6 →₀ ℕ :=
  (normalizedSlot i).2.cons (normalizedSlot i).1

theorem normalizedExponent_injective (D : ℕ → ℕ) (w wQ L B s U q : ℕ) :
    Function.Injective
      (normalizedExponent (D := D) (w := w) (wQ := wQ) (L := L) (B := B) (s := s) (U := U) (q := q)) := by
  intro i j hij
  apply normalizedSlot_injective D w wQ L B s U q
  apply Prod.ext
  · simpa only [normalizedExponent, Finsupp.cons_zero] using
      congrArg (fun d : Fin 6 →₀ ℕ => d 0) hij
  · ext k
    simpa only [normalizedExponent, Finsupp.cons_succ] using
      congrArg (fun d : Fin 6 →₀ ℕ => d k.succ) hij

theorem card_normalizedIndex (D : ℕ → ℕ) (w wQ L B s U q : ℕ) :
    Fintype.card (NormalizedIndex D w wQ L B s U q) =
      Fintype.card (Index D w L B s U) +
        ∑ j : Fin q, Fintype.card (AuxiliaryIndex (fun h => D h-wQ*(j.val+1)) w B s
          (U-(j.val+1))) := by
  simp [NormalizedIndex]

private theorem normalizedSlot_bounds
    (D : ℕ → ℕ) (w wQ L B s U q : ℕ) (hsB : 2*s ≤ B) (hUL : U ≤ L) (hqU : q ≤ U)
    (i : NormalizedIndex D w wQ L B s U q) :
    let j := (normalizedSlot i).1
    let e := (normalizedSlot i).2
    j ≤ q ∧ 2*e 1+e 3 ≤ B ∧ e 1 ≤ s ∧ e 1+e 2+e 3+j ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L ∧
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+wQ*j < D (e 1) ∧ (0 < j → e 4 = 0) := by
  cases i with
  | inl v =>
    obtain ⟨hB,hs,hU,hL,hD⟩ := exponent_bounds D w L B s U hsB v
    simpa [normalizedSlot] using And.intro hB (And.intro hs
      (And.intro hU (And.intro hL hD)))
  | inr i =>
    rcases i with ⟨j,h,r,y,x⟩
    have hj := j.isLt
    have hh := h.isLt
    have hr := r.isLt
    have hy := y.isLt
    have hx := x.isLt
    simp only [budget] at hx
    simp only [yCount] at hy
    simp [normalizedSlot, auxiliaryExponent]
    omega

section Reconstruction

variable {K : Type*} [Field K]

def reconstructNormalized (D : ℕ → ℕ) (w wQ L B s U q : ℕ) :
    (NormalizedIndex D w wQ L B s U q → K) →ₗ[K] Polynomial (Poly (K := K)) :=
  (MvPolynomial.finSuccEquiv K 5).toLinearMap.comp
    (FiniteMonomials.reconstruct normalizedExponent)

theorem reconstructNormalized_injective (D : ℕ → ℕ) (w wQ L B s U q : ℕ) :
    Function.Injective (reconstructNormalized (K := K) D w wQ L B s U q) :=
  (MvPolynomial.finSuccEquiv K 5).injective.comp
    (FiniteMonomials.reconstruct_injective _ (normalizedExponent_injective D w wQ L B s U q))

theorem reconstructed_normalized_bounds
    (D : ℕ → ℕ) (w wQ L B s U q : ℕ) (hsB : 2*s ≤ B) (hUL : U ≤ L) (hqU : q ≤ U)
    (c : NormalizedIndex D w wQ L B s U q → K) (j : ℕ) (e : Fin 5 →₀ ℕ)
    (he : e ∈ ((reconstructNormalized D w wQ L B s U q c).coeff j).support) :
    j ≤ q ∧ 2*e 1+e 3 ≤ B ∧ e 1 ≤ s ∧ e 1+e 2+e 3+j ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L ∧
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+wQ*j < D (e 1) ∧ (0 < j → e 4 = 0) := by
  change e ∈ ((MvPolynomial.finSuccEquiv K 5
    (FiniteMonomials.reconstruct normalizedExponent c)).coeff j).support at he
  have he' := MvPolynomial.mem_support_coeff_finSuccEquiv.mp he
  have hslots := (FiniteMonomials.mem_range_iff _
    (normalizedExponent_injective D w wQ L B s U q) _).mp ⟨c,rfl⟩
  obtain ⟨i,hi⟩ := hslots _ he'
  have hj : (normalizedSlot i).1 = j := by
    simpa only [normalizedExponent, Finsupp.cons_zero] using
      congrArg (fun d : Fin 6 →₀ ℕ => d 0) hi
  have hs : (normalizedSlot i).2 = e := by
    ext k
    simpa only [normalizedExponent, Finsupp.cons_succ] using
      congrArg (fun d : Fin 6 →₀ ℕ => d k.succ) hi
  simpa only [hj,hs] using normalizedSlot_bounds D w wQ L B s U q hsB hUL hqU i

end Reconstruction
end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
