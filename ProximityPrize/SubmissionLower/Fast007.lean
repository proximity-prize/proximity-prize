import ArkLib.Data.MvPolynomial.WeightedOrder
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.NumberTheory.FLT.MasonStothers
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import ProximityPrize.SubmissionLower.Fast004
import ProximityPrize.SubmissionLower.Fast005
set_option Elab.async false

section PackSource_K1_14Graph
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_14
noncomputable section
open MvPolynomial Finset
variable {F : Type*} [Field F]

def graphExponent (p : ℕ) (e : Fin 2 →₀ ℕ) : ℕ := e 0+p*e 1

def frobeniusGraph (p : ℕ) : MvPolynomial (Fin 2) F →ₐ[F] Polynomial F :=
  aeval ![Polynomial.X,Polynomial.X^p]

theorem graphExponent_injOn (p : ℕ) (hp : 0<p) :
    Set.InjOn (graphExponent p) {e : Fin 2 →₀ ℕ | e 0<p} := by
  intro e he f hf h
  have hm := congrArg (fun n : ℕ => n%p) h
  simp only [graphExponent,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt he,Nat.mod_eq_of_lt hf] at hm
  have hmul : p*e 1=p*f 1 := by unfold graphExponent at h; omega
  have h1 : e 1=f 1 := Nat.eq_of_mul_eq_mul_left hp hmul
  ext i
  fin_cases i <;> assumption

theorem frobeniusGraph_monomial (p : ℕ) (e : Fin 2 →₀ ℕ) (a : F) :
    frobeniusGraph p (monomial e a)=Polynomial.monomial (graphExponent p e) a := by
  rw [frobeniusGraph,aeval_monomial]
  simp [Finsupp.prod_fintype,Fin.prod_univ_succ,graphExponent,← pow_mul,← pow_add,Polynomial.C_mul_X_pow_eq_monomial]

theorem frobeniusGraph_coeff (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hdegree : Q.degreeOf 0<p) (e : Fin 2 →₀ ℕ) (he : e∈Q.support) :
    (frobeniusGraph p Q).coeff (graphExponent p e)=Q.coeff e := by
  classical
  have hex : frobeniusGraph p Q=∑ f∈Q.support,Polynomial.monomial (graphExponent p f) (Q.coeff f) := by
    conv_lhs => rw [Q.as_sum]
    simp only [map_sum,frobeniusGraph_monomial]
  rw [hex,Polynomial.finsetSum_coeff]
  trans ((Polynomial.monomial (graphExponent p e) (Q.coeff e)).coeff (graphExponent p e))
  · apply Finset.sum_eq_single_of_mem e he
    intro f hf hfe
    rw [Polynomial.coeff_monomial,ite_eq_right]
    intro h
    apply hfe
    apply graphExponent_injOn p hp
    · exact (le_degreeOf_of_mem_support 0 hf).trans_lt hdegree
    · exact (le_degreeOf_of_mem_support 0 he).trans_lt hdegree
    · exact h
  · simp

theorem frobeniusGraph_ne_zero (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hQ : Q≠0) (hdegree : Q.degreeOf 0<p) : frobeniusGraph p Q≠0 := by
  obtain ⟨e,he⟩ := support_nonempty.mpr hQ
  intro hz
  have hh := frobeniusGraph_coeff p hp Q hdegree e he
  rw [hz,Polynomial.coeff_zero] at hh
  exact (mem_support_iff.mp he) hh.symm

theorem frobeniusGraph_degree (p a b : ℕ) (Q : MvPolynomial (Fin 2) F)
    (hA : Q.degreeOf 0≤a) (hB : Q.degreeOf 1≤b) :
    (frobeniusGraph p Q).natDegree≤a+p*b := by
  apply (natDegree_aeval_le_weightedTotalDegree ![Polynomial.X,Polynomial.X^p] Q).trans
  apply Finset.sup_le
  intro e he
  have h0 := (le_degreeOf_of_mem_support 0 he).trans hA
  have h1 := (le_degreeOf_of_mem_support 1 he).trans hB
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul]
  nlinarith

/-- One nonzero parameter coefficient pays every zero specialization,
without primitive-content removal or a separate basepoint argument. -/
theorem frobenius_coefficient_exception_count (p a b : ℕ) (hp : 0<p)
    (Q : MvPolynomial (Fin 2) F) (hQ : Q≠0) (hA : Q.degreeOf 0≤a) (ha : a<p)
    (hB : Q.degreeOf 1≤b) (Γ : Finset F)
    (hΓ : ∀ γ∈Γ,MvPolynomial.eval ![γ,γ^p] Q=0) : Γ.card≤a+p*b := by
  have hn := frobeniusGraph_ne_zero p hp Q hQ (hA.trans_lt ha)
  have hcard : Γ.card≤(frobeniusGraph p Q).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro γ hγ
    apply (Polynomial.mem_roots hn).mpr
    have he : (frobeniusGraph p Q).eval γ=MvPolynomial.eval ![γ,γ^p] Q := by
      have hmap : (Polynomial.evalRingHom γ).comp (frobeniusGraph (F:=F) p).toRingHom=
          MvPolynomial.eval ![γ,γ^p] := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [frobeniusGraph]
        · intro i
          fin_cases i <;> simp [frobeniusGraph]
      exact RingHom.congr_fun hmap Q
    change (frobeniusGraph p Q).eval γ=0
    rw [he]
    exact hΓ γ hγ
  exact hcard.trans (frobeniusGraph_degree p a b Q hA hB)

end
end K1_14
end PackSource_K1_14Graph

section PackSource_FinitePolynomialAvoidance
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Finset MvPolynomial
open scoped BigOperators
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem exists_nonzero_evaluation_of_totalDegree_lt_card {n : ℕ}
    (p : MvPolynomial (Fin n) F) (hp : p≠0) (hdeg : p.totalDegree<Fintype.card F) :
    ∃ x : Fin n → F, MvPolynomial.eval x p≠0 := by
  classical
  by_contra hn
  push Not at hn
  have hs := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset F)
  have hgrid : (Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset F)))=Finset.univ := by
    ext x
    simp
  rw [hgrid] at hs
  simp only [hn,Finset.filter_true,Finset.card_univ,Fintype.card_fun,Fintype.card_fin] at hs
  have hpos : 0<(Fintype.card F : ℚ≥0) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card F)
  have hpow : (Fintype.card F : ℚ≥0)^n≠0 := pow_ne_zero _ hpos.ne'
  rw [Nat.cast_pow,div_self hpow] at hs
  have hlt : (p.totalDegree : ℚ≥0)/(Fintype.card F : ℚ≥0)<1 :=
    (div_lt_one hpos).mpr (by exact_mod_cast hdeg)
  exact (not_lt_of_ge hs) hlt

/-- The same nonzero-evaluation theorem with any finite variable type. -/
theorem exists_nonzero_evaluation_finite_variables {ν : Type} [Fintype ν]
    (p : MvPolynomial ν F) (hp : p≠0) (hdeg : p.totalDegree<Fintype.card F) :
    ∃ x : ν → F, MvPolynomial.eval x p≠0 := by
  let e := Fintype.equivFin ν
  let q := MvPolynomial.rename e p
  have hq : q≠0 := by
    intro hz
    exact hp ((MvPolynomial.rename_eq_zero_iff_of_injective p e.injective).mp hz)
  have hqd : q.totalDegree<Fintype.card F := (MvPolynomial.totalDegree_rename_le e p).trans_lt hdeg
  obtain ⟨x,hx⟩ := exists_nonzero_evaluation_of_totalDegree_lt_card q hq hqd
  refine ⟨x ∘ e,?_⟩
  simpa only [q,MvPolynomial.eval,MvPolynomial.eval₂Hom_rename] using hx

end
end FrobeniusLocator.Strata
end PackSource_FinitePolynomialAvoidance

section PackSource_K1_10Graph
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_10
noncomputable section
open MvPolynomial Finset
variable {F : Type*} [Field F]

def graphExponent (p : ℕ) (e : Fin 2 →₀ ℕ) : ℕ := e 0+p*e 1

def frobeniusGraph (p : ℕ) : MvPolynomial (Fin 2) F →ₐ[F] Polynomial F :=
  aeval ![Polynomial.X,Polynomial.X^p]

theorem graphExponent_injOn (p : ℕ) (hp : 0<p) :
    Set.InjOn (graphExponent p) {e : Fin 2 →₀ ℕ | e 0<p} := by
  intro e he f hf h
  have hm := congrArg (fun n : ℕ => n%p) h
  simp only [graphExponent,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt he,Nat.mod_eq_of_lt hf] at hm
  have hmul : p*e 1=p*f 1 := by unfold graphExponent at h; omega
  have h1 : e 1=f 1 := Nat.eq_of_mul_eq_mul_left hp hmul
  ext i
  fin_cases i <;> assumption

theorem frobeniusGraph_monomial (p : ℕ) (e : Fin 2 →₀ ℕ) (a : F) :
    frobeniusGraph p (monomial e a)=Polynomial.monomial (graphExponent p e) a := by
  rw [frobeniusGraph,aeval_monomial]
  simp [Finsupp.prod_fintype,Fin.prod_univ_succ,graphExponent,← pow_mul,← pow_add,Polynomial.C_mul_X_pow_eq_monomial]

theorem frobeniusGraph_coeff (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hdegree : Q.degreeOf 0<p) (e : Fin 2 →₀ ℕ) (he : e∈Q.support) :
    (frobeniusGraph p Q).coeff (graphExponent p e)=Q.coeff e := by
  classical
  have hex : frobeniusGraph p Q=∑ f∈Q.support,Polynomial.monomial (graphExponent p f) (Q.coeff f) := by
    conv_lhs => rw [Q.as_sum]
    simp only [map_sum,frobeniusGraph_monomial]
  rw [hex,Polynomial.finsetSum_coeff]
  trans ((Polynomial.monomial (graphExponent p e) (Q.coeff e)).coeff (graphExponent p e))
  · apply Finset.sum_eq_single_of_mem e he
    intro f hf hfe
    have hdistinct : graphExponent p f ≠ graphExponent p e := by
      intro h
      apply hfe
      apply graphExponent_injOn p hp
      · exact (le_degreeOf_of_mem_support 0 hf).trans_lt hdegree
      · exact (le_degreeOf_of_mem_support 0 he).trans_lt hdegree
      · exact h
    simp [Polynomial.coeff_monomial, hdistinct]
  · simp

theorem frobeniusGraph_ne_zero (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hQ : Q≠0) (hdegree : Q.degreeOf 0<p) : frobeniusGraph p Q≠0 := by
  obtain ⟨e,he⟩ := support_nonempty.mpr hQ
  intro hz
  have hh := frobeniusGraph_coeff p hp Q hdegree e he
  rw [hz,Polynomial.coeff_zero] at hh
  exact (mem_support_iff.mp he) hh.symm

theorem frobeniusGraph_degree (p a b : ℕ) (Q : MvPolynomial (Fin 2) F)
    (hA : Q.degreeOf 0≤a) (hB : Q.degreeOf 1≤b) :
    (frobeniusGraph p Q).natDegree≤a+p*b := by
  apply (natDegree_aeval_le_weightedTotalDegree ![Polynomial.X,Polynomial.X^p] Q).trans
  apply Finset.sup_le
  intro e he
  have h0 := (le_degreeOf_of_mem_support 0 he).trans hA
  have h1 := (le_degreeOf_of_mem_support 1 he).trans hB
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul]
  nlinarith

/-- One nonzero parameter coefficient pays every zero specialization,
without primitive-content removal or a separate basepoint argument. -/
theorem frobenius_coefficient_exception_count (p a b : ℕ) (hp : 0<p)
    (Q : MvPolynomial (Fin 2) F) (hQ : Q≠0) (hA : Q.degreeOf 0≤a) (ha : a<p)
    (hB : Q.degreeOf 1≤b) (Γ : Finset F)
    (hΓ : ∀ γ∈Γ,MvPolynomial.eval ![γ,γ^p] Q=0) : Γ.card≤a+p*b := by
  have hn := frobeniusGraph_ne_zero p hp Q hQ (hA.trans_lt ha)
  have hcard : Γ.card≤(frobeniusGraph p Q).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro γ hγ
    apply (Polynomial.mem_roots hn).mpr
    have he : (frobeniusGraph p Q).eval γ=MvPolynomial.eval ![γ,γ^p] Q := by
      have hmap : (Polynomial.evalRingHom γ).comp (frobeniusGraph (F:=F) p).toRingHom=
          MvPolynomial.eval ![γ,γ^p] := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [frobeniusGraph]
        · intro i
          fin_cases i <;> simp [frobeniusGraph]
      exact RingHom.congr_fun hmap Q
    change (frobeniusGraph p Q).eval γ=0
    rw [he]
    exact hΓ γ hγ
  exact hcard.trans (frobeniusGraph_degree p a b Q hA hB)

end
end K1_10
end PackSource_K1_10Graph

section PackSource_K1_14_2_2_4_4Aux1
set_option autoImplicit true
namespace K1_14_2_2_4_4

noncomputable section

open IsLocalRing

/-- The powers of the maximal ideal remain strictly descending after imposing
a single anchor in a Noetherian local ring of dimension at least two. -/
theorem linear_length {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x f g : R} {n : ℕ} (hx : x ∈ maximalIdeal R)
    (hd : 1 < (maximalIdeal R).height)
    (hf : f ∈ (maximalIdeal R) ^ n ⊔ Ideal.span {x})
    (hg : g ∈ (maximalIdeal R) ^ n ⊔ Ideal.span {x}) :
    (n : ℕ∞) ≤ Module.length R (R ⧸ Ideal.span {f, g}) := by
  let m := maximalIdeal R
  let A : Ideal R := Ideal.span {x}
  let J (i : ℕ) := A ⊔ m ^ i
  have hno (i : ℕ) : ¬ m ^ i ≤ A := by
    intro h
    have hmin : m ∈ A.minimalPrimes := by
      refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem m).mpr hx⟩, ?_⟩
      intro P hP _
      exact fun z hz => hP.1.mem_of_pow_mem i (hP.2 (h (Ideal.pow_mem_pow hz i)))
    let _ : A.IsPrincipal := ⟨⟨x, rfl⟩⟩
    exact (not_le_of_gt hd)
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing A hmin)
  have hstep (i : ℕ) : J (i + 1) < J i := by
    refine lt_of_le_of_ne (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ i)) _) ?_
    intro he
    apply hno i
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := m) (IsNoetherian.noetherian _)
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · change m ^ i ≤ A ⊔ m • m ^ i
      rw [smul_eq_mul, ← pow_succ']
      change m ^ i ≤ J (i + 1)
      rw [he]
      exact le_sup_right
  have hlength (i : ℕ) : (i : ℕ∞) ≤ Order.coheight (J i : Submodule R R) := by
    induction i with
    | zero => simp
    | succ i ih =>
        rw [Nat.cast_succ]
        exact (add_le_add_left ih 1).trans
          (Order.coheight_add_one_le (show (J (i + 1) : Submodule R R) < J i from hstep i))
  rw [Module.length_quotient]
  apply (hlength n).trans
  apply Order.coheight_anti
  apply Ideal.span_le.mpr
  simpa [J, A, m, Set.insert_subset_iff, Set.singleton_subset_iff, sup_comm] using And.intro hf hg

/-- The triangular Hilbert function of a regular local surface. -/
def triangle : ℕ → ℕ
  | 0 => 0
  | k + 1 => triangle k + (k + 1)

private theorem two_mul_triangle (k : ℕ) : 2 * triangle k = k * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change 2 * (triangle k + (k + 1)) = (k + 1) * (k + 1 + 1)
      nlinarith

private theorem triangle_truncation (k : ℕ) :
    triangle (k + k + 1) = (k + 1) ^ 2 + (triangle k + triangle k) := by
  have h := two_mul_triangle k
  have H := two_mul_triangle (k + k + 1)
  nlinarith

def multiplyToQuotient {R : Type*} [CommRing R] (A B : Ideal R) (x : R)
    (hx : ∀ r ∈ A, r * x ∈ B) : (R ⧸ A) →ₗ[R] (R ⧸ B) :=
  A.liftQ ((LinearMap.id : R →ₗ[R] R).smulRight (Ideal.Quotient.mk B x)) (by
    intro r hr
    simpa [Algebra.smul_def, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] using hx r hr)

theorem multiplyToQuotient_mk {R : Type*} [CommRing R] (A B : Ideal R) (x : R)
    (hx : ∀ r ∈ A, r * x ∈ B) (r : R) :
    multiplyToQuotient A B x hx (Ideal.Quotient.mk A r) = Ideal.Quotient.mk B (r * x) := by
  change r • Ideal.Quotient.mk B x = _
  simp [Algebra.smul_def]

/-- Truncate in degree 2k+1. Each row of order at least k+1 gives an
image of a copy of the quotient truncated in degree k. -/
theorem square_length_of_hilbert {R : Type*} [CommRing R] (m : Ideal R)
    (hh : ∀ i, Module.length R (R ⧸ m ^ i) = (triangle i : ℕ∞))
    {f g : R} {n : ℕ} (hn : 0 < n) (hf : f ∈ m ^ n) (hg : g ∈ m ^ n) :
    (↑(n ^ 2 : ℕ) : ℕ∞) ≤ Module.length R (R ⧸ Ideal.span {f, g}) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let T := m ^ (k + k + 1)
  let J : Ideal R := Ideal.span {f, g}
  have hmul (x : R) (hx : x ∈ m ^ (k + 1)) (r : R) (hr : r ∈ m ^ k) :
      r * x ∈ T := by
    have h := Ideal.mul_mem_mul hr hx
    rwa [← pow_add, ← Nat.add_assoc] at h
  let F := multiplyToQuotient (m ^ k) T f (hmul f hf)
  let G := multiplyToQuotient (m ^ k) T g (hmul g hg)
  let H := LinearMap.coprod F G
  let q := Submodule.factor (show (T : Submodule R R) ≤ T ⊔ J from le_sup_left)
  have hker : LinearMap.ker q = LinearMap.range H := by
    ext z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk (T ⊔ J) z = 0 ↔ Ideal.Quotient.mk T z ∈ LinearMap.range H
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · rintro hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.mp hb
      refine ⟨(Ideal.Quotient.mk _ c, Ideal.Quotient.mk _ d), ?_⟩
      simp [H, F, G, multiplyToQuotient_mk, map_add,
        Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    · rintro ⟨⟨c, d⟩, he⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
      have he' : Ideal.Quotient.mk T (c * f + d * g) = Ideal.Quotient.mk T z := by
        simpa [H, F, G, multiplyToQuotient_mk, map_add] using he
      rw [Ideal.Quotient.eq] at he'
      have hz : z = (-(c * f + d * g - z)) + (c * f + d * g) := by ring
      rw [hz]
      exact (T ⊔ J).add_mem (Ideal.mem_sup_left (T.neg_mem he'))
        (Ideal.mem_sup_right (Ideal.mem_span_pair.mpr ⟨c, d, rfl⟩))
  have hq := Module.length_eq_add_of_exact (LinearMap.ker q).subtype q
    (Submodule.subtype_injective _) (Submodule.factor_surjective _)
    (LinearMap.exact_subtype_ker_map q)
  have hsmall := Module.length_le_of_surjective H.rangeRestrict H.surjective_rangeRestrict
  rw [← hker, Module.length_prod, hh] at hsmall
  have hsum : (↑((k + 1) ^ 2 : ℕ) : ℕ∞) + ((triangle k : ℕ∞) + triangle k) ≤
      Module.length R (R ⧸ (T ⊔ J : Ideal R)) + ((triangle k : ℕ∞) + triangle k) := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← triangle_truncation, ← hh]
    change Module.length R (R ⧸ T) ≤ _
    rw [hq, Nat.cast_add, add_comm (Module.length R ↥(LinearMap.ker q))]
    exact add_le_add_right hsmall _
  exact ((ENat.add_le_add_iff_right (by rw [← Nat.cast_add]; exact ENat.natCast_ne_top _)).mp hsum).trans
    (Module.length_le_of_surjective (Submodule.factor (show J ≤ T ⊔ J from le_sup_right))
      (Submodule.factor_surjective _))

end
end K1_14_2_2_4_4
end PackSource_K1_14_2_2_4_4Aux1

section PackSource_MultivariateMinorDegree
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Finset Matrix MvPolynomial
open scoped BigOperators
variable {F ν c : Type} [Field F] [Fintype c] [DecidableEq c]

theorem totalDegree_det_le_row_sum (M : Matrix c c (MvPolynomial ν F))
    (d : c → ℕ) (hM : ∀ i j, (M i j).totalDegree≤d i) :
    M.det.totalDegree≤∑ i, d i := by
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  have hs : (Equiv.Perm.sign σ • ∏ i, M (σ i) i).totalDegree≤
      (∏ i, M (σ i) i).totalDegree := MvPolynomial.totalDegree_smul_le _ _
  exact hs.trans ((MvPolynomial.totalDegree_finsetProd _ _).trans
    ((Finset.sum_le_sum (fun i _ => hM (σ i) i)).trans_eq (Equiv.sum_comp σ d)))

end
end FrobeniusLocator.Strata
end PackSource_MultivariateMinorDegree
