import ProximityPrize.SubmissionLower.Koala6844Comparison






namespace ProximityPrize.SubmissionLower.Koala6844Comparison

open Polynomial

variable {R I : Type*} [CommRing R] [IsDomain R]

structure SymbolicRow (R : Type*) [CommRing R] where
  beta : Polynomial R
  first : Polynomial R
  second : Polynomial R

def SymbolicRow.atNode (q : SymbolicRow R) (x u v : R) : R :=
  q.beta.eval x + q.first.eval x * u + q.second.eval x * v

theorem eq_zero_of_vanishing_on_nodes (P : Polynomial R)
    (x : I ↪ R) (nodes : Finset I) (hdegree : P.natDegree < nodes.card)
    (hvanish : ∀ i ∈ nodes, P.eval (x i) = 0) :
    P = 0 := by
  classical
  by_contra hp
  apply Nat.not_le_of_gt hdegree
  calc
    nodes.card = (nodes.image x).card :=
      (Finset.card_image_of_injective _ x.injective).symm
    _ ≤ P.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact (Polynomial.mem_roots hp).mpr (hvanish i hi)

theorem first_cross_beta_eq_of_determinant_zero
    (x : I ↪ R) (nodes : Finset I) (u v : I → R)
    (q r : SymbolicRow R) (a b : ℕ) (hbudget : a + b < nodes.card)
    (hqFirst : q.first.natDegree ≤ a) (hrFirst : r.first.natDegree ≤ a)
    (hqBeta : q.beta.natDegree ≤ b) (hrBeta : r.beta.natDegree ≤ b)
    (hq : ∀ i ∈ nodes, q.atNode (x i) (u i) (v i) = 0)
    (hr : ∀ i ∈ nodes, r.atNode (x i) (u i) (v i) = 0)
    (hdet : q.first * r.second = r.first * q.second) :
    q.first * r.beta = r.first * q.beta := by
  apply sub_eq_zero.mp
  apply eq_zero_of_vanishing_on_nodes _ x nodes
  · have hleft : (q.first * r.beta).natDegree ≤ a + b := calc
      _ ≤ q.first.natDegree + r.beta.natDegree := Polynomial.natDegree_mul_le
      _ ≤ a + b := Nat.add_le_add hqFirst hrBeta
    have hright : (r.first * q.beta).natDegree ≤ a + b := calc
      _ ≤ r.first.natDegree + q.beta.natDegree := Polynomial.natDegree_mul_le
      _ ≤ a + b := Nat.add_le_add hrFirst hqBeta
    exact ((Polynomial.natDegree_sub_le _ _).trans (max_le hleft hright)).trans_lt hbudget
  · intro i hi
    have hqNode := hq i hi
    have hrNode := hr i hi
    have hdetNode := congrArg (fun P : Polynomial R => P.eval (x i)) hdet
    simp only [SymbolicRow.atNode] at hqNode hrNode
    simp only [Polynomial.eval_mul] at hdetNode
    simp only [Polynomial.eval_sub, Polynomial.eval_mul]
    linear_combination (q.first.eval (x i)) * hrNode -
      (r.first.eval (x i)) * hqNode - (v i) * hdetNode

theorem cross_beta_eq_of_determinant_zero
    (x : I ↪ R) (nodes : Finset I) (u v : I → R)
    (q r : SymbolicRow R) (a b : ℕ) (hbudget : a + b < nodes.card)
    (hqFirst : q.first.natDegree ≤ a) (hrFirst : r.first.natDegree ≤ a)
    (hqSecond : q.second.natDegree ≤ a) (hrSecond : r.second.natDegree ≤ a)
    (hqBeta : q.beta.natDegree ≤ b) (hrBeta : r.beta.natDegree ≤ b)
    (hq : ∀ i ∈ nodes, q.atNode (x i) (u i) (v i) = 0)
    (hr : ∀ i ∈ nodes, r.atNode (x i) (u i) (v i) = 0)
    (hdet : q.first * r.second = r.first * q.second) :
    q.first * r.beta = r.first * q.beta ∧ q.second * r.beta = r.second * q.beta := by
  constructor
  · exact first_cross_beta_eq_of_determinant_zero x nodes u v q r a b hbudget
      hqFirst hrFirst hqBeta hrBeta hq hr hdet
  · let q' : SymbolicRow R := ⟨q.beta, q.second, q.first⟩
    let r' : SymbolicRow R := ⟨r.beta, r.second, r.first⟩
    have hq' : ∀ i ∈ nodes, q'.atNode (x i) (v i) (u i) = 0 := by
      intro i hi
      simpa only [q', SymbolicRow.atNode, add_assoc,
        add_comm (q.second.eval (x i) * v i) (q.first.eval (x i) * u i)] using hq i hi
    have hr' : ∀ i ∈ nodes, r'.atNode (x i) (v i) (u i) = 0 := by
      intro i hi
      simpa only [r', SymbolicRow.atNode, add_assoc,
        add_comm (r.second.eval (x i) * v i) (r.first.eval (x i) * u i)] using hr i hi
    have hd' : q'.first * r'.second = r'.first * q'.second := by
      change q.second * r.first = r.second * q.first
      calc
        q.second * r.first = r.first * q.second := mul_comm _ _
        _ = q.first * r.second := hdet.symm
        _ = r.second * q.first := mul_comm _ _
    exact first_cross_beta_eq_of_determinant_zero x nodes v u q' r' a b hbudget
      hqSecond hrSecond hqBeta hrBeta hq' hr' hd'

theorem exists_polynomial_multiplier_of_primitive_first
    [GCDMonoid (Polynomial R)] (q r : SymbolicRow R)
    (hq : q.first ≠ 0) (hprimitive : IsUnit (gcd q.beta (gcd q.first q.second)))
    (hsecond : q.first * r.second = r.first * q.second)
    (hbeta : q.first * r.beta = r.first * q.beta) :
    ∃ m : Polynomial R, r.beta = m * q.beta ∧
      r.first = m * q.first ∧ r.second = m * q.second := by
  have hdBeta : q.first ∣ q.beta * r.first := by
    rw [mul_comm q.beta r.first, ← hbeta]
    exact dvd_mul_right _ _
  have hdSecond : q.first ∣ q.second * r.first := by
    rw [mul_comm q.second r.first, ← hsecond]
    exact dvd_mul_right _ _
  have hdBoth : q.first ∣ gcd q.first q.second * r.first :=
    (dvd_gcd (dvd_mul_right q.first r.first) hdSecond).trans
      (gcd_mul_right' r.first q.first q.second).dvd
  have hdPrimitive : q.first ∣ gcd q.beta (gcd q.first q.second) * r.first :=
    (dvd_gcd hdBeta hdBoth).trans (gcd_mul_right' r.first q.beta (gcd q.first q.second)).dvd
  have hdFirst : q.first ∣ r.first := by
    have hu : gcd q.beta (gcd q.first q.second) ∣ 1 := isUnit_iff_dvd_one.mp hprimitive
    have h := mul_dvd_mul hu (dvd_refl r.first)
    exact hdPrimitive.trans (by simpa only [one_mul] using h)
  obtain ⟨m, hm⟩ := hdFirst
  refine ⟨m, ?_, by rw [hm, mul_comm], ?_⟩
  · apply mul_left_cancel₀ hq
    rw [hbeta, hm, mul_assoc]
  · apply mul_left_cancel₀ hq
    rw [hsecond, hm, mul_assoc]

theorem exists_primitive_factor_of_first_ne_zero
    [GCDMonoid (Polynomial R)] (r : SymbolicRow R) (hr : r.first ≠ 0) :
    ∃ (q : SymbolicRow R) (m : Polynomial R),
      m ≠ 0 ∧ q.first ≠ 0 ∧ IsUnit (gcd q.beta (gcd q.first q.second)) ∧
      r.beta = m * q.beta ∧ r.first = m * q.first ∧ r.second = m * q.second := by
  let m := gcd r.beta (gcd r.first r.second)
  obtain ⟨β, hβ⟩ := gcd_dvd_left r.beta (gcd r.first r.second)
  obtain ⟨α, hα⟩ := (gcd_dvd_right r.beta (gcd r.first r.second)).trans
    (gcd_dvd_left r.first r.second)
  obtain ⟨δ, hδ⟩ := (gcd_dvd_right r.beta (gcd r.first r.second)).trans
    (gcd_dvd_right r.first r.second)
  change r.beta = m * β at hβ
  change r.first = m * α at hα
  change r.second = m * δ at hδ
  have hm : m ≠ 0 := fun h => hr (by simpa [h] using hα)
  have hα₀ : α ≠ 0 := fun h => hr (by simpa [h] using hα)
  have hUnit : IsUnit (gcd β (gcd α δ)) := by
    let d := gcd β (gcd α δ)
    have hdβ : d ∣ β := gcd_dvd_left β (gcd α δ)
    have hdα : d ∣ α := (gcd_dvd_right β (gcd α δ)).trans (gcd_dvd_left α δ)
    have hdδ : d ∣ δ := (gcd_dvd_right β (gcd α δ)).trans (gcd_dvd_right α δ)
    have hd1 : m * d ∣ r.beta := hβ ▸ mul_dvd_mul_left m hdβ
    have hd2 : m * d ∣ r.first := hα ▸ mul_dvd_mul_left m hdα
    have hd3 : m * d ∣ r.second := hδ ▸ mul_dvd_mul_left m hdδ
    have hmd : m * d ∣ m := dvd_gcd hd1 (dvd_gcd hd2 hd3)
    apply isUnit_iff_dvd_one.mpr
    apply (mul_dvd_mul_iff_left hm).mp
    simpa only [mul_one] using hmd
  exact ⟨⟨β, α, δ⟩, m, hm, hα₀, hUnit, hβ, hα, hδ⟩

theorem multiplier_eval_eq_zero_of_bad_node
    (q r : SymbolicRow R) (m : Polynomial R) (x u v : R)
    (hβ : r.beta = m * q.beta) (hα : r.first = m * q.first)
    (hδ : r.second = m * q.second) (hr : r.atNode x u v = 0)
    (hq : q.atNode x u v ≠ 0) :
    m.eval x = 0 := by
  have hfactor : r.atNode x u v = m.eval x * q.atNode x u v := by
    simp only [SymbolicRow.atNode, hβ, hα, hδ, Polynomial.eval_mul]
    ring
  exact (mul_eq_zero.mp (hfactor.symm.trans hr)).resolve_right hq

theorem beta_eq_zero_of_no_active_coefficient
    (q : SymbolicRow R) (x : I ↪ R) (nodes : Finset I) (u v : I → R)
    (hβ : q.beta.natDegree < nodes.card)
    (hfirst : q.first = 0) (hsecond : q.second = 0)
    (hq : ∀ i ∈ nodes, q.atNode (x i) (u i) (v i) = 0) :
    q.beta = 0 := by
  apply eq_zero_of_vanishing_on_nodes q.beta x nodes hβ
  intro i hi
  simpa [SymbolicRow.atNode, hfirst, hsecond] using hq i hi

noncomputable def badNodeLocator (x : I ↪ R) (bad : Finset I) : Polynomial R := by
  classical
  exact ((bad.image x).val.map fun a => Polynomial.X - Polynomial.C a).prod

theorem badNodeLocator_natDegree (x : I ↪ R) (bad : Finset I) :
    (badNodeLocator x bad).natDegree = bad.card := by
  classical
  rw [badNodeLocator, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
  exact Finset.card_image_of_injective _ x.injective

theorem badNodeLocator_dvd_of_vanishing (x : I ↪ R) (bad : Finset I) (m : Polynomial R)
    (hm : ∀ i ∈ bad, m.eval (x i) = 0) : badNodeLocator x bad ∣ m := by
  classical
  by_cases hz : m = 0
  · simp [hz]
  unfold badNodeLocator
  apply (Multiset.prod_X_sub_C_dvd_iff_le_roots hz _).mpr
  apply (Multiset.le_iff_subset (bad.image x).nodup).mpr
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_def.mpr ha)
  exact (Polynomial.mem_roots hz).mpr (hm i hi)


private noncomputable def withSeedVariables {S : Type*}
    (P : Polynomial (MvPolynomial S R)) : MvPolynomial (Option S) R :=
  (MvPolynomial.optionEquivLeft R S).symm P

omit [IsDomain R] in
private theorem withSeedVariables_degree_le_iff {S : Type*}
    (P : Polynomial (MvPolynomial S R)) (i : S) (d : ℕ) :
    (withSeedVariables P).degreeOf (some i) ≤ d ↔
      ∀ n, (P.coeff n).degreeOf i ≤ d := by
  classical
  constructor
  · intro h n
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hsupport : e.optionElim n ∈ (withSeedVariables P).support := by
      apply (MvPolynomial.mem_support_coeff_optionEquivLeft (R := R)).mp
      simpa [withSeedVariables] using he
    simpa only [Finsupp.optionElim_apply_some] using
      MvPolynomial.degreeOf_le_iff.mp h _ hsupport
  · intro h
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hsupport : e.some ∈ (P.coeff (e none)).support := by
      have hpart : e.some.optionElim (e none) ∈ (withSeedVariables P).support := by
        rwa [Finsupp.optionElim_some]
      have hs := (MvPolynomial.mem_support_coeff_optionEquivLeft (R := R)).mpr hpart
      simpa [withSeedVariables] using hs
    simpa only [Finsupp.some_apply] using MvPolynomial.degreeOf_le_iff.mp (h (e none)) _ hsupport

theorem multiplier_seed_coeff_degree_le {S : Type*}
    (m q r : Polynomial (MvPolynomial S R)) (i : S) (d : ℕ)
    (hr : r = m * q) (hr0 : r ≠ 0) (hdegree : ∀ n, (r.coeff n).degreeOf i ≤ d) :
    ∀ n, (m.coeff n).degreeOf i ≤ d := by
  have hm : m ≠ 0 := fun h => hr0 (by simpa [h] using hr)
  have hq : q ≠ 0 := fun h => hr0 (by simpa [h] using hr)
  have hm' : withSeedVariables m ≠ 0 := by
    intro h
    apply hm
    apply (MvPolynomial.optionEquivLeft R S).symm.injective
    simpa [withSeedVariables] using h
  have hq' : withSeedVariables q ≠ 0 := by
    intro h
    apply hq
    apply (MvPolynomial.optionEquivLeft R S).symm.injective
    simpa [withSeedVariables] using h
  have hr' : withSeedVariables r = withSeedVariables m * withSeedVariables q := by
    simp [withSeedVariables, hr]
  have hb := (withSeedVariables_degree_le_iff r i d).mpr hdegree
  rw [hr', MvPolynomial.degreeOf_mul_eq hm' hq'] at hb
  apply (withSeedVariables_degree_le_iff m i d).mp
  omega

end ProximityPrize.SubmissionLower.Koala6844Comparison



namespace ProximityPrize.SubmissionLower.Koala6844Comparison

open Polynomial
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

private def boxExponent {b c : ℕ} (j : SeedIndex b c) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 j.1.val + Finsupp.single 1 j.2.val

private theorem boxExponent_eq {b c : ℕ} (e : Fin 2 →₀ ℕ) (h₀ : e 0 < b) (h₁ : e 1 < c) :
    boxExponent (⟨e 0, h₀⟩, ⟨e 1, h₁⟩) = e := by
  have hOne : (1 : Fin 2) ≠ 0 := by decide
  have hZero : (0 : Fin 2) ≠ 1 := Ne.symm hOne
  ext i
  fin_cases i
  · simp [boxExponent, hZero]
  · simp [boxExponent, hOne]

def restrictMultiplierCoefficients (h b c : ℕ) :
    Polynomial (SeedRing K) →ₗ[K] (CoefficientIndex h b c → K) where
  toFun P j := (P.coeff j.1.val).coeff (boxExponent j.2)
  map_add' P Q := by
    funext j
    simp
  map_smul' z P := by
    funext j
    simp [Polynomial.coeff_smul]

def InMultiplierBox (h b c : ℕ) (P : Polynomial (SeedRing K)) : Prop :=
  (∀ n, h ≤ n → P.coeff n = 0) ∧
    (∀ n, (P.coeff n).degreeOf 0 < b ∧ (P.coeff n).degreeOf 1 < c)

theorem multiplierCoefficients_identify {h b c : ℕ} {P Q : Polynomial (SeedRing K)}
    (hP : InMultiplierBox h b c P) (hQ : InMultiplierBox h b c Q)
    (hEq : restrictMultiplierCoefficients h b c P = restrictMultiplierCoefficients h b c Q) :
    P = Q := by
  apply Polynomial.ext
  intro n
  by_cases hn : n < h
  · apply MvPolynomial.ext
    intro e
    by_cases h₀ : e 0 < b
    · by_cases h₁ : e 1 < c
      · have he := congrFun hEq (⟨n, hn⟩, (⟨e 0, h₀⟩, ⟨e 1, h₁⟩))
        change (P.coeff n).coeff (boxExponent (⟨e 0, h₀⟩, ⟨e 1, h₁⟩)) =
          (Q.coeff n).coeff (boxExponent (⟨e 0, h₀⟩, ⟨e 1, h₁⟩)) at he
        have hbox : boxExponent (b := b) (c := c) (⟨e 0, h₀⟩, ⟨e 1, h₁⟩) = e :=
          boxExponent_eq e h₀ h₁
        simpa only [hbox] using he
      · have hzero (R : Polynomial (SeedRing K)) (hR : InMultiplierBox h b c R) :
            (R.coeff n).coeff e = 0 := by
          by_contra hne
          have hm := MvPolynomial.mem_support_iff.mpr hne
          exact h₁ ((MvPolynomial.le_degreeOf_of_mem_support (1 : Fin 2) hm).trans_lt (hR.2 n).2)
        rw [hzero P hP, hzero Q hQ]
    · have hzero (R : Polynomial (SeedRing K)) (hR : InMultiplierBox h b c R) :
          (R.coeff n).coeff e = 0 := by
        by_contra hne
        have hm := MvPolynomial.mem_support_iff.mpr hne
        exact h₀ ((MvPolynomial.le_degreeOf_of_mem_support (0 : Fin 2) hm).trans_lt (hR.2 n).1)
      rw [hzero P hP, hzero Q hQ]
  · rw [hP.1 n (Nat.le_of_not_gt hn), hQ.1 n (Nat.le_of_not_gt hn)]

theorem finrank_le_of_multiplierBox {V : Type*} [AddCommGroup V] [Module K V]
    (L : V →ₗ[K] Polynomial (SeedRing K)) (hL : Function.Injective L)
    (h b c : ℕ) (hbox : ∀ v, InMultiplierBox h b c (L v)) :
    Module.finrank K V ≤ h * b * c := by
  let f := (restrictMultiplierCoefficients h b c).comp L
  have hinj : Function.Injective f := by
    intro u v huv
    apply hL
    exact multiplierCoefficients_identify (hbox u) (hbox v) huv
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card] at hd
  simpa only [CoefficientIndex, SeedIndex, Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc] using hd

def divideMultiplierLinear {V : Type*} [AddCommGroup V] [Module K V]
    (L : V →ₗ[K] Polynomial (SeedRing K))
    (q : Polynomial (SeedRing K)) (hq : q ≠ 0) (hdiv : ∀ v, q ∣ L v) :
    V →ₗ[K] Polynomial (SeedRing K) where
  toFun v := Classical.choose (hdiv v)
  map_add' x y := by
    apply mul_left_cancel₀ hq
    rw [mul_add, ← Classical.choose_spec (hdiv (x + y)),
      ← Classical.choose_spec (hdiv x), ← Classical.choose_spec (hdiv y), map_add]
  map_smul' z x := by
    apply mul_left_cancel₀ hq
    simp only [RingHom.id_apply, mul_smul_comm]
    rw [← Classical.choose_spec (hdiv (z • x)), ← Classical.choose_spec (hdiv x), map_smul]

theorem divideMultiplierLinear_spec {V : Type*} [AddCommGroup V] [Module K V]
    (L : V →ₗ[K] Polynomial (SeedRing K))
    (q : Polynomial (SeedRing K)) (hq : q ≠ 0) (hdiv : ∀ v, q ∣ L v) (v : V) :
    L v = q * divideMultiplierLinear L q hq hdiv v :=
  Classical.choose_spec (hdiv v)

end

end ProximityPrize.SubmissionLower.Koala6844Comparison



namespace ProximityPrize.SubmissionLower.Koala6844Comparison

open Polynomial
open scoped BigOperators

noncomputable section

variable {K I : Type*} [Field K]

abbrev SeedCoefficients (K : Type*) [Field K] := Polynomial (SeedRing K)

def rankRow {A a d : ℕ} (θ : RowIndex A a d → K) : SymbolicRow (SeedRing K) :=
  let q := symbolicRow θ
  ⟨q.beta, q.first, q.second⟩

private theorem symbolicRow_ext {R : Type*} [CommRing R] {q r : SymbolicRow R}
    (hb : q.beta = r.beta) (h₀ : q.first = r.first) (h₁ : q.second = r.second) : q = r := by
  cases q
  cases r
  simp_all

theorem rankRow_injective (A a d : ℕ) :
    Function.Injective (rankRow : (RowIndex A a d → K) → SymbolicRow (SeedRing K)) := by
  intro θ η h
  apply symbolicRow_injective A a d
  exact congrArg (fun r : SymbolicRow (SeedRing K) =>
    (⟨r.beta, r.first, r.second⟩ : SpecializedRow (SeedRing K))) h

theorem rankRow_degrees {A a d : ℕ} (θ : RowIndex A a d → K) :
    let q := rankRow θ
    q.beta.natDegree ≤ A - 1 ∧ q.first.natDegree ≤ a - 1 ∧ q.second.natDegree ≤ a - 1 :=
  specialize_degrees (fun j => MvPolynomial.C (θ j))
    (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2))

def seedNode (x : I ↪ K) : I ↪ SeedRing K :=
  ⟨fun i => MvPolynomial.C (x i), (MvPolynomial.C_injective (Fin 2) K).comp x.injective⟩

def affineSeedWord (u v : Fin 2 → I → K) (j : Fin 2) (i : I) : SeedRing K :=
  MvPolynomial.C (u j i) + MvPolynomial.X j * MvPolynomial.C (v j i)

theorem rankRow_atNode_zero {A a d : ℕ}
    (x : I ↪ K) (u v : Fin 2 → I → K) (θ : ComparisonSpace A a d x u v) (i : I) :
    (rankRow θ.1).atNode (seedNode x i) (affineSeedWord u v 0 i) (affineSeedWord u v 1 i) = 0 := by
  exact symbolicRow_eval_received_eq_zero x u v θ i

private theorem rankRow_zero {A a d : ℕ} :
    rankRow (0 : RowIndex A a d → K) = ⟨0, 0, 0⟩ := by
  simp [rankRow, symbolicRow, specialize, specializePiece]

theorem rankRow_has_active_coefficient [Fintype I] {A a d : ℕ}
    (x : I ↪ K) (u v : Fin 2 → I → K) (θ : ComparisonSpace A a d x u v)
    (hθ : θ.1 ≠ 0) (hA : A - 1 < Fintype.card I) :
    (rankRow θ.1).first ≠ 0 ∨ (rankRow θ.1).second ≠ 0 := by
  classical
  by_contra! hz
  have hb := beta_eq_zero_of_no_active_coefficient
    (rankRow θ.1) (seedNode x) Finset.univ
    (affineSeedWord u v 0) (affineSeedWord u v 1)
    ((rankRow_degrees θ.1).1.trans_lt (by simpa using hA))
    hz.1 hz.2 (fun i _ => rankRow_atNode_zero x u v θ i)
  apply hθ (rankRow_injective A a d ?_)
  rw [rankRow_zero]
  exact symbolicRow_ext hb hz.1 hz.2

structure RowFactors (q r : SymbolicRow (SeedRing K)) (m : SeedCoefficients K) : Prop where
  beta : r.beta = m * q.beta
  first : r.first = m * q.first
  second : r.second = m * q.second

def IsPrimitiveRow (q : SymbolicRow (SeedRing K)) : Prop :=
  ∀ f, f ∣ q.beta → f ∣ q.first → f ∣ q.second → IsUnit f

private def swapValueCoefficients (q : SymbolicRow (SeedRing K)) : SymbolicRow (SeedRing K) :=
  ⟨q.beta, q.second, q.first⟩

private theorem primitiveRow_from_unit_gcd [GCDMonoid (SeedCoefficients K)]
    (q : SymbolicRow (SeedRing K)) (h : IsUnit (gcd q.beta (gcd q.first q.second))) :
    IsPrimitiveRow q := by
  intro f hb h₀ h₁
  exact isUnit_of_dvd_unit (dvd_gcd hb (dvd_gcd h₀ h₁)) h

private theorem unit_gcd_from_primitiveRow [GCDMonoid (SeedCoefficients K)]
    (q : SymbolicRow (SeedRing K)) (h : IsPrimitiveRow q) :
    IsUnit (gcd q.beta (gcd q.first q.second)) :=
  h _ (gcd_dvd_left _ _) ((gcd_dvd_right _ _).trans (gcd_dvd_left _ _))
    ((gcd_dvd_right _ _).trans (gcd_dvd_right _ _))

theorem primitive_factor_of_active (r : SymbolicRow (SeedRing K))
    (h : r.first ≠ 0 ∨ r.second ≠ 0) :
    ∃ (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K), m ≠ 0 ∧
      (q.first ≠ 0 ∨ q.second ≠ 0) ∧ IsPrimitiveRow q ∧ RowFactors q r m := by
  let _ : NormalizedGCDMonoid (SeedCoefficients K) := Classical.ofNonempty
  rcases h with h₀ | h₁
  · obtain ⟨q, m, hm, ha, hunit, hb, hf, hs⟩ := exists_primitive_factor_of_first_ne_zero r h₀
    exact ⟨q, m, hm, Or.inl ha, primitiveRow_from_unit_gcd q hunit, ⟨hb, hf, hs⟩⟩
  · obtain ⟨q, m, hm, ha, hunit, hb, hf, hs⟩ :=
      exists_primitive_factor_of_first_ne_zero (swapValueCoefficients r) h₁
    refine ⟨swapValueCoefficients q, m, hm, Or.inr ha, ?_, ⟨hb, hs, hf⟩⟩
    intro f hβ hfirst hsecond
    exact primitiveRow_from_unit_gcd q hunit f hβ hsecond hfirst

private theorem multiply_primitive_of_cross_eq (q r : SymbolicRow (SeedRing K))
    (hp : IsPrimitiveRow q) (ha : q.first ≠ 0 ∨ q.second ≠ 0)
    (hdet : q.first * r.second = r.first * q.second)
    (hb₀ : q.first * r.beta = r.first * q.beta)
    (hb₁ : q.second * r.beta = r.second * q.beta) :
    ∃ m : SeedCoefficients K, RowFactors q r m := by
  let _ : NormalizedGCDMonoid (SeedCoefficients K) := Classical.ofNonempty
  rcases ha with ha | ha
  · obtain ⟨m, hb, h₀, h₁⟩ :=
      exists_polynomial_multiplier_of_primitive_first q r ha
        (unit_gcd_from_primitiveRow q hp) hdet hb₀
    exact ⟨m, ⟨hb, h₀, h₁⟩⟩
  · have hps : IsPrimitiveRow (swapValueCoefficients q) := by
      intro f hb h₀ h₁
      exact hp f hb h₁ h₀
    have hdet' : (swapValueCoefficients q).first * (swapValueCoefficients r).second =
        (swapValueCoefficients r).first * (swapValueCoefficients q).second := by
      change q.second * r.first = r.second * q.first
      rw [mul_comm q.second, hdet.symm, mul_comm q.first]
    obtain ⟨m, hb, h₁, h₀⟩ :=
      exists_polynomial_multiplier_of_primitive_first (swapValueCoefficients q)
        (swapValueCoefficients r) ha (unit_gcd_from_primitiveRow _ hps) hdet' hb₁
    exact ⟨m, ⟨hb, h₀, h₁⟩⟩

private theorem cross_eq_of_mul_left {a b c d m : SeedCoefficients K}
    (hm : m ≠ 0) (h : (m * a) * b = c * (m * d)) : a * b = c * d := by
  apply mul_left_cancel₀ hm
  rw [← mul_assoc, h, mul_left_comm]

theorem exists_primitive_comparison_generator [Fintype I] {A a d₀ d₁ : ℕ}
    (x : I ↪ K) (u v : Fin 2 → I → K)
    (θ₀ : ComparisonSpace A a d₀ x u v) (hθ₀ : θ₀.1 ≠ 0)
    (hbudget : (a - 1) + (A - 1) < Fintype.card I)
    (hcollinear : ∀ θ : ComparisonSpace A a d₁ x u v,
      (rankRow θ₀.1).first * (rankRow θ.1).second =
        (rankRow θ.1).first * (rankRow θ₀.1).second) :
    ∃ (q : SymbolicRow (SeedRing K)) (m₀ : SeedCoefficients K), m₀ ≠ 0 ∧
      (q.first ≠ 0 ∨ q.second ≠ 0) ∧ IsPrimitiveRow q ∧
      RowFactors q (rankRow θ₀.1) m₀ ∧
      ∀ θ : ComparisonSpace A a d₁ x u v, ∃ m, RowFactors q (rankRow θ.1) m := by
  classical
  obtain ⟨q, m, hm, ha, hp, hm₀⟩ := primitive_factor_of_active (rankRow θ₀.1)
    (rankRow_has_active_coefficient x u v θ₀ hθ₀ (by omega))
  refine ⟨q, m, hm, ha, hp, hm₀, fun θ => ?_⟩
  have hd₀ := rankRow_degrees θ₀.1
  have hd₁ := rankRow_degrees θ.1
  have ⟨hb₀, hb₁⟩ := cross_beta_eq_of_determinant_zero
    (seedNode x) Finset.univ (affineSeedWord u v 0) (affineSeedWord u v 1)
    (rankRow θ₀.1) (rankRow θ.1) (a - 1) (A - 1) (by simpa using hbudget)
    hd₀.2.1 hd₁.2.1 hd₀.2.2 hd₁.2.2 hd₀.1 hd₁.1
    (fun i _ => rankRow_atNode_zero x u v θ₀ i)
    (fun i _ => rankRow_atNode_zero x u v θ i) (hcollinear θ)
  apply multiply_primitive_of_cross_eq q (rankRow θ.1) hp ha
  · apply cross_eq_of_mul_left hm
    rw [← hm₀.first, ← hm₀.second]
    exact hcollinear θ
  · apply cross_eq_of_mul_left hm
    rw [← hm₀.first, ← hm₀.beta]
    exact hb₀
  · apply cross_eq_of_mul_left hm
    rw [← hm₀.second, ← hm₀.beta]
    exact hb₁

end

end ProximityPrize.SubmissionLower.Koala6844Comparison



namespace ProximityPrize.SubmissionLower.Koala6844Comparison

open Polynomial
open scoped BigOperators Classical

noncomputable section

variable {K I : Type*} [Field K]

def primitiveBadNodes [Fintype I] (x : I ↪ K) (u v : Fin 2 → I → K)
    (q : SymbolicRow (SeedRing K)) : Finset I :=
  Finset.univ.filter fun i => q.atNode (seedNode x i) (affineSeedWord u v 0 i)
    (affineSeedWord u v 1 i) ≠ 0

def primitiveExcess (w : ℕ) (q : SymbolicRow (SeedRing K)) : ℕ :=
  max (q.beta.natDegree - w) (max q.first.natDegree q.second.natDegree)

private theorem row_eq_of_piece_eq {R : Type*} [CommRing R] {q r : SymbolicRow R}
    (hβ : q.beta = r.beta) (h₀ : q.first = r.first) (h₁ : q.second = r.second) : q = r := by
  cases q
  cases r
  simp_all

private def firstPieceLinear {A a d : ℕ} (x : I ↪ K) (u v : Fin 2 → I → K) :
    ComparisonSpace A a d x u v →ₗ[K] SeedCoefficients K where
  toFun θ := (rankRow θ.1).first
  map_add' θ η := by
    simp [rankRow, symbolicRow, specialize, specializePiece, add_mul, Finset.sum_add_distrib]
  map_smul' s θ := by
    simp [rankRow, symbolicRow, specialize, specializePiece, Polynomial.smul_monomial,
      MvPolynomial.smul_eq_C_mul, Finset.smul_sum, mul_assoc]

private theorem badNodeLocator_ne_zero (x : I ↪ K) (bad : Finset I) :
    badNodeLocator (seedNode x) bad ≠ 0 := by
  unfold badNodeLocator
  exact (Polynomial.monic_multisetProd_X_sub_C _).ne_zero

private theorem locator_dvd_multiplier [Fintype I] {A a d : ℕ}
    (x : I ↪ K) (u v : Fin 2 → I → K) (q : SymbolicRow (SeedRing K))
    (θ : ComparisonSpace A a d x u v) (m : SeedCoefficients K)
    (hm : RowFactors q (rankRow θ.1) m) :
    badNodeLocator (seedNode x) (primitiveBadNodes x u v q) ∣ m := by
  apply badNodeLocator_dvd_of_vanishing
  intro i hi
  exact multiplier_eval_eq_zero_of_bad_node q (rankRow θ.1) m (seedNode x i)
    (affineSeedWord u v 0 i) (affineSeedWord u v 1 i) hm.beta hm.first hm.second
    (rankRow_atNode_zero x u v θ i) (Finset.mem_filter.mp hi).2

private theorem quotient_mul_divides_first [Fintype I] {A a d : ℕ}
    (x : I ↪ K) (u v : Fin 2 → I → K) (q : SymbolicRow (SeedRing K))
    (h : ∀ θ : ComparisonSpace A a d x u v, ∃ m, RowFactors q (rankRow θ.1) m)
    (θ : ComparisonSpace A a d x u v) :
    badNodeLocator (seedNode x) (primitiveBadNodes x u v q) * q.first ∣
      firstPieceLinear (A := A) (a := a) (d := d) x u v θ := by
  obtain ⟨m, hm⟩ := h θ
  obtain ⟨f, hf⟩ := locator_dvd_multiplier x u v q θ m hm
  refine ⟨f, ?_⟩
  change (rankRow θ.1).first = _
  rw [hm.first, hf]
  ac_rfl

theorem comparisonSpace_finrank_le_primitiveBox [Fintype I] {A a d w : ℕ}
    (x : I ↪ K) (u v : Fin 2 → I → K) (q : SymbolicRow (SeedRing K))
    (h₀ : q.first ≠ 0) (h₁ : q.second ≠ 0) (ha : 0 < a) (hA : a + w = A)
    (h : ∀ θ : ComparisonSpace A a d x u v, ∃ m, RowFactors q (rankRow θ.1) m) :
    Module.finrank K (ComparisonSpace A a d x u v) ≤
      (a - (primitiveExcess w q + (primitiveBadNodes x u v q).card)) * (d + 1) * (d + 1) := by
  let bad := primitiveBadNodes x u v q
  let D := badNodeLocator (seedNode x) bad
  have hD : D ≠ 0 := badNodeLocator_ne_zero x bad
  let L := firstPieceLinear (A := A) (a := a) (d := d) x u v
  let f := divideMultiplierLinear L (D * q.first) (mul_ne_zero hD h₀)
    (quotient_mul_divides_first x u v q h)
  have factors (v' : ComparisonSpace A a d x u v) : RowFactors q (rankRow v'.1) (D * f v') := by
    obtain ⟨m, hm⟩ := h v'
    have he := divideMultiplierLinear_spec L (D * q.first) (mul_ne_zero hD h₀)
      (quotient_mul_divides_first x u v q h) v'
    change (rankRow v'.1).first = (D * q.first) * f v' at he
    have hm' : m = D * f v' := by
      apply mul_right_cancel₀ h₀
      rw [← hm.first, he]
      ac_rfl
    simpa only [hm'] using hm
  have hinj : Function.Injective f := by
    intro v' t' he
    apply Subtype.ext
    apply rankRow_injective A a d
    apply row_eq_of_piece_eq
    · rw [(factors v').beta, (factors t').beta, he]
    · rw [(factors v').first, (factors t').first, he]
    · rw [(factors v').second, (factors t').second, he]
  apply finrank_le_of_multiplierBox f hinj
  intro θ
  let fθ := f θ
  change InMultiplierBox (a - (primitiveExcess w q + bad.card)) (d + 1) (d + 1) fθ
  by_cases hf : fθ = 0
  · simp [hf, InMultiplierBox]
  have hb := rankRow_degrees θ.1
  have hF : RowFactors q (rankRow θ.1) (D * fθ) := factors θ
  have hid : D.natDegree = bad.card := badNodeLocator_natDegree (seedNode x) bad
  have hnonzero : D * fθ ≠ 0 := mul_ne_zero hD hf
  have hdf : (D * fθ).natDegree = bad.card + fθ.natDegree := by
    rw [Polynomial.natDegree_mul hD hf, hid]
  have hα₀ : fθ.natDegree + bad.card + q.first.natDegree ≤ a - 1 := by
    have hh := hb.2.1
    rw [hF.first, Polynomial.natDegree_mul hnonzero h₀, hdf] at hh
    omega
  have hα₁ : fθ.natDegree + bad.card + q.second.natDegree ≤ a - 1 := by
    have hh := hb.2.2
    rw [hF.second, Polynomial.natDegree_mul hnonzero h₁, hdf] at hh
    omega
  have hβ : fθ.natDegree + bad.card + (q.beta.natDegree - w) ≤ a - 1 := by
    by_cases hz : q.beta = 0
    · simp [hz]
      omega
    · have hh := hb.1
      rw [hF.beta, Polynomial.natDegree_mul hnonzero hz, hdf] at hh
      omega
  have hx : fθ.natDegree < a - (primitiveExcess w q + bad.card) := by
    unfold primitiveExcess
    omega
  have hp₀ : (rankRow θ.1).first = fθ * (D * q.first) := by rw [hF.first]; ac_rfl
  have hp₁ : (rankRow θ.1).second = fθ * (D * q.second) := by rw [hF.second]; ac_rfl
  have hd₀ := multiplier_seed_coeff_degree_le fθ _ _ (0 : Fin 2) d hp₀
    (hp₀ ▸ mul_ne_zero hf (mul_ne_zero hD h₀))
    (fun n => (symbolicRow_seed_degree_bounds θ.1 n).2.1.1)
  have hd₁ := multiplier_seed_coeff_degree_le fθ _ _ (1 : Fin 2) d hp₁
    (hp₁ ▸ mul_ne_zero hf (mul_ne_zero hD h₁))
    (fun n => (symbolicRow_seed_degree_bounds θ.1 n).2.2.2)
  refine ⟨fun n hn => Polynomial.coeff_eq_zero_of_natDegree_lt (hx.trans_le hn), fun n => ?_⟩
  exact ⟨Nat.lt_succ_of_le (hd₀ n), Nat.lt_succ_of_le (hd₁ n)⟩

theorem primitive_excess_add_badCard_le_31606 [Fintype I]
    (x : I ↪ K) (u v : Fin 2 → I → K) (q : SymbolicRow (SeedRing K))
    (h₀ : q.first ≠ 0) (h₁ : q.second ≠ 0) (hcard : Fintype.card I = 262144)
    (h : ∀ θ : ComparisonSpace 180957 49886 200 x u v, ∃ m, RowFactors q (rankRow θ.1) m) :
    primitiveExcess 131071 q + (primitiveBadNodes x u v q).card ≤ 31614 := by
  have hlo := comparisonSpace_finrank_lower_bound 180957 49886 200 81187 x u v hcard
  have hhi := comparisonSpace_finrank_le_primitiveBox x u v q h₀ h₁ (by decide)
    (w := 131071) (by decide) h
  have hbound := hlo.trans hhi
  norm_num at hbound
  omega

end

end ProximityPrize.SubmissionLower.Koala6844Comparison



namespace ProximityPrize.SubmissionLower.Koala6844Comparison

open Polynomial
open scoped BigOperators Classical

noncomputable section

variable {K I : Type*} [Field K]

def conjugateWord (σ : K →+* K) (u : I → K) (j : Fin 2) (i : I) : K :=
  if j = 0 then u i else σ (u i)

def primitiveSelected (σ : K →+* K) (p : ℕ) (q : SymbolicRow (SeedRing K))
    (selected : K → Polynomial K) (g : K) : Polynomial K :=
  let E := MvPolynomial.eval (Koala6844BivariateSeeds.coordinates g (g ^ p))
  q.beta.map E + q.first.map E * selected g + q.second.map E * (selected g).map σ

private theorem seedDegree_right_factor (m q r : SeedCoefficients K) (j : Fin 2) (d : ℕ)
    (hm : m ≠ 0) (hr : r = m * q) (hd : ∀ n, (r.coeff n).degreeOf j ≤ d) :
    ∀ n, (q.coeff n).degreeOf j ≤ d := by
  by_cases hz : r = 0
  · have hq : q = 0 := (mul_eq_zero.mp (hr.symm.trans hz)).resolve_left hm
    simp [hq]
  · exact multiplier_seed_coeff_degree_le q m r j d (hr.trans (mul_comm _ _)) hz hd

private theorem x_degree_right_factor (m q r : SeedCoefficients K)
    (hm : m ≠ 0) (hr : r = m * q) : q.natDegree ≤ r.natDegree := by
  by_cases hz : r = 0
  · have hq : q = 0 := (mul_eq_zero.mp (hr.symm.trans hz)).resolve_left hm
    simp [hq, hz]
  · exact Polynomial.natDegree_le_of_dvd ⟨m, hr.trans (mul_comm _ _)⟩ hz

theorem primitive_x_degree_caps {A a d : ℕ} (θ : RowIndex A a d → K)
    (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K)
    (hm : m ≠ 0) (h : RowFactors q (rankRow θ) m) :
    q.beta.natDegree ≤ A - 1 ∧ q.first.natDegree ≤ a - 1 ∧ q.second.natDegree ≤ a - 1 :=
  ⟨(x_degree_right_factor m _ _ hm h.beta).trans (rankRow_degrees θ).1,
    (x_degree_right_factor m _ _ hm h.first).trans (rankRow_degrees θ).2.1,
    (x_degree_right_factor m _ _ hm h.second).trans (rankRow_degrees θ).2.2⟩

theorem primitive_seed_degree_caps {A a d : ℕ} (θ : RowIndex A a d → K)
    (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K)
    (hm : m ≠ 0) (h : RowFactors q (rankRow θ) m) (n : ℕ) :
    ((q.beta.coeff n).degreeOf 0 ≤ d + 1 ∧ (q.beta.coeff n).degreeOf 1 ≤ d + 1) ∧
      ((q.first.coeff n).degreeOf 0 ≤ d ∧ (q.first.coeff n).degreeOf 1 ≤ d + 1) ∧
      ((q.second.coeff n).degreeOf 0 ≤ d + 1 ∧ (q.second.coeff n).degreeOf 1 ≤ d) :=
  ⟨⟨seedDegree_right_factor _ _ _ _ _ hm h.beta
        (fun j => (symbolicRow_seed_degree_bounds θ j).1.1) n,
      seedDegree_right_factor _ _ _ _ _ hm h.beta
        (fun j => (symbolicRow_seed_degree_bounds θ j).1.2) n⟩,
    ⟨seedDegree_right_factor _ _ _ _ _ hm h.first
        (fun j => (symbolicRow_seed_degree_bounds θ j).2.1.1) n,
      seedDegree_right_factor _ _ _ _ _ hm h.first
        (fun j => (symbolicRow_seed_degree_bounds θ j).2.1.2) n⟩,
    ⟨seedDegree_right_factor _ _ _ _ _ hm h.second
        (fun j => (symbolicRow_seed_degree_bounds θ j).2.2.1) n,
      seedDegree_right_factor _ _ _ _ _ hm h.second
        (fun j => (symbolicRow_seed_degree_bounds θ j).2.2.2) n⟩⟩

private theorem lowMultiplier_seed_degree_caps {A a : ℕ} (θ : RowIndex A a 4 → K)
    (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K)
    (hm : m ≠ 0) (ha : q.first ≠ 0 ∨ q.second ≠ 0)
    (h : RowFactors q (rankRow θ) m) (n : ℕ) :
    (m.coeff n).degreeOf 0 < 6 ∧ (m.coeff n).degreeOf 1 < 6 := by
  rcases ha with ha | ha
  · have hr : (rankRow θ).first ≠ 0 := h.first ▸ mul_ne_zero hm ha
    have h₀ := multiplier_seed_coeff_degree_le m q.first _ (0 : Fin 2) 4 h.first hr
      (fun j => (symbolicRow_seed_degree_bounds θ j).2.1.1) n
    have h₁ := multiplier_seed_coeff_degree_le m q.first _ (1 : Fin 2) 5 h.first hr
      (fun j => (symbolicRow_seed_degree_bounds θ j).2.1.2) n
    omega
  · have hr : (rankRow θ).second ≠ 0 := h.second ▸ mul_ne_zero hm ha
    have h₀ := multiplier_seed_coeff_degree_le m q.second _ (0 : Fin 2) 5 h.second hr
      (fun j => (symbolicRow_seed_degree_bounds θ j).2.2.1) n
    have h₁ := multiplier_seed_coeff_degree_le m q.second _ (1 : Fin 2) 4 h.second hr
      (fun j => (symbolicRow_seed_degree_bounds θ j).2.2.2) n
    omega

private theorem seedDegree_at_base (P : SeedCoefficients K) (x : K) (j : Fin 2) (d : ℕ)
    (ha : ∀ n, (P.coeff n).degreeOf j ≤ d) :
    (P.eval (MvPolynomial.C x)).degreeOf j ≤ d := by
  rw [P.eval_eq_sum_range' (Nat.lt_succ_self P.natDegree)]
  apply (MvPolynomial.degreeOf_sum_le j _ _).trans
  apply Finset.sup_le
  intro n _
  apply (MvPolynomial.degreeOf_mul_le j _ _).trans
  simpa only [← map_pow, MvPolynomial.degreeOf_C, Nat.add_zero] using ha n

private theorem affineSeedWord_degree (u v : Fin 2 → I → K) (i : I) (j k : Fin 2) :
    (affineSeedWord u v k i).degreeOf j ≤ if j = k then 1 else 0 := by
  unfold affineSeedWord
  apply (MvPolynomial.degreeOf_add_le j _ _).trans
  apply max_le
  · simp
  · apply (MvPolynomial.degreeOf_mul_le j _ _).trans
    by_cases h : j = k
    · subst j
      simp
    · simp [MvPolynomial.degreeOf_X_of_ne h, h]

theorem lowPrimitiveNode_degree {A a : ℕ} (θ : RowIndex A a 4 → K)
    (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K)
    (hm : m ≠ 0) (h : RowFactors q (rankRow θ) m)
    (x : I ↪ K) (u v : Fin 2 → I → K) (i : I) :
    let P := q.atNode (seedNode x i) (affineSeedWord u v 0 i) (affineSeedWord u v 1 i)
    P.degreeOf 0 < 6 ∧ P.degreeOf 1 < 6 := by
  have hβ (j : Fin 2) : ((q.beta.eval (MvPolynomial.C (x i))).degreeOf j) ≤ 5 := by
    apply seedDegree_at_base
    intro n
    fin_cases j
    · exact (primitive_seed_degree_caps θ q m hm h n).1.1
    · exact (primitive_seed_degree_caps θ q m hm h n).1.2
  have hfirst (j : Fin 2) : ((q.first.eval (MvPolynomial.C (x i))).degreeOf j) ≤
      if j = 0 then 4 else 5 := by
    apply seedDegree_at_base
    intro n
    fin_cases j
    · exact (primitive_seed_degree_caps θ q m hm h n).2.1.1
    · exact (primitive_seed_degree_caps θ q m hm h n).2.1.2
  have hsecond (j : Fin 2) : ((q.second.eval (MvPolynomial.C (x i))).degreeOf j) ≤
      if j = 1 then 4 else 5 := by
    apply seedDegree_at_base
    intro n
    fin_cases j
    · exact (primitive_seed_degree_caps θ q m hm h n).2.2.1
    · exact (primitive_seed_degree_caps θ q m hm h n).2.2.2
  have hout (j : Fin 2) :
      (q.atNode (seedNode x i) (affineSeedWord u v 0 i) (affineSeedWord u v 1 i)).degreeOf j ≤ 5 := by
    change (q.beta.eval (MvPolynomial.C (x i)) +
      q.first.eval (MvPolynomial.C (x i)) * affineSeedWord u v 0 i +
      q.second.eval (MvPolynomial.C (x i)) * affineSeedWord u v 1 i).degreeOf j ≤ 5
    apply (MvPolynomial.degreeOf_add_le j _ _).trans
    apply max_le
    · apply (MvPolynomial.degreeOf_add_le j _ _).trans
      apply max_le (hβ j)
      apply (MvPolynomial.degreeOf_mul_le j _ _).trans
      have hb := Nat.add_le_add (hfirst j) (affineSeedWord_degree u v i j 0)
      exact hb.trans (by fin_cases j <;> decide)
    · apply (MvPolynomial.degreeOf_mul_le j _ _).trans
      have hb := Nat.add_le_add (hsecond j) (affineSeedWord_degree u v i j 1)
      exact hb.trans (by fin_cases j <;> decide)
  exact ⟨Nat.lt_succ_of_le (hout 0), Nat.lt_succ_of_le (hout 1)⟩

private theorem eval_seedNode (P : SeedCoefficients K) (x : K) (z : Fin 2 → K) :
    MvPolynomial.eval z (P.eval (MvPolynomial.C x)) =
      (P.map (MvPolynomial.eval z)).eval x := by
  have h : (P.map (MvPolynomial.eval z)).eval (MvPolynomial.eval z (MvPolynomial.C x)) =
      MvPolynomial.eval z (P.eval (MvPolynomial.C x)) :=
    Polynomial.eval_map_apply (MvPolynomial.eval z) (MvPolynomial.C x)
  simpa only [MvPolynomial.eval_C] using h.symm

private theorem eval_conjugate_polynomial (σ : K →+* K) (x : I ↪ K)
    (hfixed : ∀ i, σ (x i) = x i) (P : Polynomial K) (i : I) :
    (P.map σ).eval (x i) = σ (P.eval (x i)) := by
  have h : (P.map σ).eval (σ (x i)) = σ (P.eval (x i)) := Polynomial.eval_map_apply σ (x i)
  simpa only [hfixed i] using h

theorem retain_primitive_rows [Fintype I] {A a w p : ℕ}
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hsigma : ∀ g, σ g = g ^ p) (hp : 6 ≤ p)
    (U : Fin 2 → I → K) (ha : 0 < a) (hA : a + w = A)
    (θ : ComparisonSpace A a 4 x (conjugateWord σ (U 0)) (conjugateWord σ (U 1)))
    (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K) (hm : m ≠ 0)
    (hq : q.first ≠ 0 ∨ q.second ≠ 0) (hf : RowFactors q (rankRow θ.1) m)
    (seeds : Finset K) (agree : K → Finset I) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hcard : ∀ g ∈ seeds, A ≤ (agree g).card)
    (hagree : ∀ g ∈ seeds, ∀ i ∈ agree g, (selected g).eval (x i) = U 0 i + g * U 1 i) :
    let bad := primitiveBadNodes x (conjugateWord σ (U 0)) (conjugateWord σ (U 1)) q
    ∃ retained : Finset K, retained ⊆ seeds ∧
      seeds.card ≤ retained.card + (bad.card + 1) * (5 * (p + 1)) ∧
      ∀ g ∈ retained, primitiveSelected σ p q selected g = 0 ∧ Disjoint (agree g) bad := by
  let u := conjugateWord σ (U 0)
  let v := conjugateWord σ (U 1)
  let bad := primitiveBadNodes x u v q
  let test (i : I) := q.atNode (seedNode x i) (affineSeedWord u v 0 i) (affineSeedWord u v 1 i)
  have hproduct (g : K) (hg : g ∈ seeds) :
      m.map (MvPolynomial.eval (Koala6844BivariateSeeds.coordinates g (g ^ p))) *
        primitiveSelected σ p q selected g = 0 := by
    let z := Koala6844BivariateSeeds.coordinates g (g ^ p)
    let E := MvPolynomial.eval z
    have hr := specialize_selected_eq_zero x U σ hfixed ha hA θ g (selected g)
      (hdegree g hg) (agree g) (hcard g hg) (hagree g hg)
    obtain ⟨hb, h₀, h₁⟩ := symbolicRow_map_seedEval θ.1 z
    have hraw : (rankRow θ.1).beta.map E +
        (rankRow θ.1).first.map E * selected g +
        (rankRow θ.1).second.map E * (selected g).map σ = 0 := by
      change (symbolicRow θ.1).beta.map E + (symbolicRow θ.1).first.map E * selected g +
        (symbolicRow θ.1).second.map E * (selected g).map σ = 0
      rw [hb, h₀, h₁]
      simpa [z, Koala6844BivariateSeeds.coordinates, hsigma g] using hr
    change m.map E * primitiveSelected σ p q selected g = 0
    calc
      _ = (rankRow θ.1).beta.map E +
          (rankRow θ.1).first.map E * selected g +
          (rankRow θ.1).second.map E * (selected g).map σ := by
        simp only [primitiveSelected, hf.beta, hf.first, hf.second, Polynomial.map_mul, E]
        ring
      _ = _ := hraw
  have hnodeZero (i : I) (g : K) (hg : g ∈ seeds) (hgi : i ∈ agree g)
      (hmE : m.map (MvPolynomial.eval (Koala6844BivariateSeeds.coordinates g (g ^ p))) ≠ 0) :
      MvPolynomial.eval (Koala6844BivariateSeeds.coordinates g (g ^ p)) (test i) = 0 := by
    let z := Koala6844BivariateSeeds.coordinates g (g ^ p)
    have hprim := (mul_eq_zero.mp (hproduct g hg)).resolve_left hmE
    have hroot := congrArg (Polynomial.eval (x i)) hprim
    have hcEval := eval_conjugate_polynomial σ x hfixed (selected g) i
    have hAgree := hagree g hg i hgi
    have hConj : ((selected g).map σ).eval (x i) = σ (U 0 i) + g ^ p * σ (U 1 i) := by
      rw [hcEval, hAgree, map_add, map_mul, hsigma g]
    have hroot' : ((primitiveSelected σ p q selected g).eval (x i)) = 0 := by
      simpa only [Polynomial.eval_zero] using hroot
    simpa [test, SymbolicRow.atNode, seedNode, affineSeedWord, u, v, conjugateWord,
      z, Koala6844BivariateSeeds.coordinates, eval_seedNode, primitiveSelected,
      Polynomial.eval_mul, Polynomial.eval_add, hAgree, hConj] using hroot'
  let multiplier (g : K) := m.map (MvPolynomial.eval (Koala6844BivariateSeeds.coordinates g (g ^ p)))
  let singular := seeds.filter fun g => multiplier g = 0
  let regular := seeds \ singular
  let atBad (i : I) := regular.filter fun g => i ∈ agree g
  let badSeeds := bad.biUnion atBad
  let retained := regular \ badSeeds
  have hmultNonzero (g : K) (hg : g ∈ regular) : multiplier g ≠ 0 := by
    intro hz
    exact (Finset.mem_sdiff.mp hg).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hg).1, hz⟩)
  have hsingularSubset : singular ⊆ seeds := Finset.filter_subset _ _
  have hbadSubset : badSeeds ⊆ regular := by
    intro g hg
    obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.mp hg
    exact (Finset.mem_filter.mp hgi).1
  let limit := 5 + p * 5
  have hsingular : singular.card ≤ limit := by
    have hcap := lowMultiplier_seed_degree_caps θ.1 q m hm hq hf m.natDegree
    have hcoeff : m.coeff m.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hm
    apply Koala6844BivariateSeeds.card_le_of_vanishing (b := 6) (c := 6)
      (by omega : 0 < p) hp hcoeff hcap.1 hcap.2
    intro g hg
    have hz : multiplier g = 0 := (Finset.mem_filter.mp hg).2
    have he := congrArg (fun P : Polynomial K => P.coeff m.natDegree) hz
    simpa only [multiplier, Polynomial.coeff_map, Polynomial.coeff_zero] using he
  have hbadSeeds : badSeeds.card ≤ bad.card * limit := by
    calc
      _ ≤ ∑ i ∈ bad, (atBad i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ bad, limit := by
        apply Finset.sum_le_sum
        intro i hi
        have hcap := lowPrimitiveNode_degree θ.1 q m hm hf x u v i
        have hnonzero : test i ≠ 0 := (Finset.mem_filter.mp hi).2
        apply Koala6844BivariateSeeds.card_le_of_vanishing (b := 6) (c := 6)
          (by omega : 0 < p) hp hnonzero hcap.1 hcap.2
        intro g hg
        obtain ⟨hreg, hgi⟩ := Finset.mem_filter.mp hg
        exact hnodeZero i g (Finset.sdiff_subset hreg) hgi (hmultNonzero g hreg)
      _ = _ := by simp [Nat.mul_comm]
  have hsum : seeds.card = regular.card + singular.card := by
    change _ = (seeds \ singular).card + singular.card
    rw [Finset.card_sdiff_of_subset hsingularSubset]
    exact (Nat.sub_add_cancel (Finset.card_le_card hsingularSubset)).symm
  have hsum' : regular.card = retained.card + badSeeds.card := by
    change _ = (regular \ badSeeds).card + badSeeds.card
    rw [Finset.card_sdiff_of_subset hbadSubset]
    exact (Nat.sub_add_cancel (Finset.card_le_card hbadSubset)).symm
  refine ⟨retained, Finset.sdiff_subset.trans Finset.sdiff_subset, ?_, ?_⟩
  · calc
      seeds.card = retained.card + badSeeds.card + singular.card := by rw [hsum, hsum']
      _ ≤ retained.card + bad.card * limit + limit :=
        Nat.add_le_add (Nat.add_le_add_left hbadSeeds _) hsingular
      _ = _ := by dsimp [limit]; ring
  · intro g hg
    obtain ⟨hreg, hkeep⟩ := Finset.mem_sdiff.mp hg
    refine ⟨(mul_eq_zero.mp (hproduct g (Finset.sdiff_subset hreg))).resolve_left
      (hmultNonzero g hreg), ?_⟩
    rw [Finset.disjoint_left]
    intro i hgi hi
    exact hkeep (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hreg, hgi⟩⟩)


end

end ProximityPrize.SubmissionLower.Koala6844Comparison



namespace ProximityPrize.SubmissionLower.Koala6844OneSided

open Koala6844Comparison Koala6844BivariateSeeds
open Polynomial
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false

variable {K I : Type} [Field K]

private theorem map_eval_at_fixed_node (x : I ↪ K) (τ : K →+* K)
    (hfixed : ∀ i, τ (x i) = x i) (P : K[X]) (i : I) :
    (P.map τ).eval (x i) = τ (P.eval (x i)) := by
  rw [← hfixed i, Polynomial.eval_map_apply, hfixed i]

private theorem identity_nodes_card_le
    (x : I ↪ K) (u₀ u₁ : I → K) (τ : K →+* K)
    (hfixed : ∀ i, τ (x i) = x i)
    (selected : K → K[X]) (D N : K → K[X]) (hD : ∀ x, D x ≠ 0)
    (seeds : Finset K) (identities : Finset I) (w e denCap : ℕ)
    (hDdegree : ∀ x, (D x).natDegree ≤ denCap)
    (hcard : w < identities.card)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hidentity : ∀ i ∈ identities, ∀ g ∈ seeds,
      (N (x i)).eval g = (D (x i)).eval g * τ (u₀ i + g * u₁ i))
    (hchart : ∀ g ∈ seeds, ∀ i,
      (D (x i)).eval g * ((selected g).map τ).eval (x i) = (N (x i)).eval g)
    (hpencil : ∀ q₀ q₁ : K[X], q₀.natDegree ≤ w → q₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected q₀ q₁).card ≤ e + 1) :
    seeds.card ≤ (w + 1) * denCap + (e + 1) := by
  obtain ⟨testNodes, hnodes, htestCard⟩ :=
    Finset.exists_subset_card_eq (show w + 1 ≤ identities.card by omega)
  let failing (i : I) := seeds.filter (fun g => (D (x i)).eval g = 0)
  let excluded := testNodes.biUnion failing
  let retained := seeds \ excluded
  have hexcluded : excluded ⊆ seeds := by
    intro g hg
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hg
    exact (Finset.mem_filter.mp hi).1
  have hfail (i : I) : (failing i).card ≤ denCap := by
    apply le_trans _ (hDdegree (x i))
    apply Polynomial.card_le_degree_of_subset_roots
    intro g hg
    exact (Polynomial.mem_roots (hD (x i))).mpr (Finset.mem_filter.mp hg).2
  have hexcludedCard : excluded.card ≤ (w + 1) * denCap := by
    calc
      excluded.card ≤ ∑ i ∈ testNodes, (failing i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ testNodes, denCap := Finset.sum_le_sum fun i _ => hfail i
      _ = (w + 1) * denCap := by simp [htestCard]
  have hretainedValues (g : ↥retained) (i : I) (hi : i ∈ testNodes) :
      (selected (g : K)).eval (x i) = u₀ i + (g : K) * u₁ i := by
    obtain ⟨hg, hv⟩ := Finset.mem_sdiff.mp g.property
    have hnonzero : (D (x i)).eval (g : K) ≠ 0 := by
      intro h
      apply hv
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hg, h⟩⟩
    apply τ.injective
    apply mul_left_cancel₀ hnonzero
    calc
      _ = (D (x i)).eval (g : K) * ((selected (g : K)).map τ).eval (x i) := by
        rw [map_eval_at_fixed_node x τ hfixed]
      _ = (N (x i)).eval (g : K) := hchart (g : K) hg i
      _ = _ := hidentity i (hnodes hi) (g : K) hg
  obtain ⟨q₀, q₁, h₀, h₁, hfit⟩ := RCN147.exists_basefield_affine_pencil_of_identity_nodes
    (RingHom.id K) testNodes x u₀ u₁ w (by omega) x.injective.injOn
    (fun g : ↥retained => (g : K)) (fun g => selected g)
    (fun g => hdegree (g : K) (Finset.mem_sdiff.mp g.property).1)
    (fun g i hi => by simpa only [RingHom.id_apply] using hretainedValues g i hi)
  have hretainedCard : retained.card ≤ e + 1 := by
    apply (Finset.card_le_card (t := RCN050.pencilSeeds seeds selected q₀ q₁) ?_).trans
      (hpencil q₀ q₁ h₀ h₁)
    intro g hg
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_sdiff.mp hg).1, ?_⟩
    simpa only [Polynomial.map_id] using hfit ⟨g, hg⟩
  have hsum : retained.card + excluded.card = seeds.card := by
    rw [show retained.card = seeds.card - excluded.card from Finset.card_sdiff_of_subset hexcluded]
    exact Nat.sub_add_cancel (Finset.card_le_card hexcluded)
  omega

private theorem encoded_chart_card_le
    (x : I ↪ K) (u₀ u₁ : I → K) (τ : K →+* K)
    (hfixed : ∀ i, τ (x i) = x i) (power : ℕ) (hpower : ∀ g, τ g = g ^ power)
    (selected : K → K[X]) (denominator numerator : Polynomial K[X]) (hne : denominator ≠ 0)
    (seeds : Finset K) (nodes : Finset I) (w A e denCap numCap : ℕ)
    (hw : w < A) (hA : A ≤ nodes.card)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagreement : ∀ g ∈ seeds,
      A ≤ (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hDdegree : ∀ j, (denominator.coeff j).natDegree ≤ denCap)
    (hNdegree : ∀ j, (numerator.coeff j).natDegree ≤ numCap)
    (heq : ∀ g ∈ seeds, denominator.map (evalRingHom g) * (selected g).map τ =
      numerator.map (evalRingHom g))
    (hpencil : ∀ q₀ q₁ : K[X], q₀.natDegree ≤ w → q₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected q₀ q₁).card ≤ e + 1) :
    seeds.card ≤ max ((nodes.card - w) * max numCap (denCap + power) / (A - w))
      ((w + 1) * denCap + (e + 1)) := by
  obtain ⟨D, N, hD, hDcap, hNcap, hnode⟩ :=
    Koala6844ChartNormalization.exists_node_tests denominator numerator hne denCap numCap
      hDdegree hNdegree
  let word (i : I) : Polynomial K := C (τ (u₀ i)) + (Polynomial.X : Polynomial K) ^ power * C (τ (u₁ i))
  let test (i : I) := N (x i) - D (x i) * word i
  let identities := nodes.filter (fun i => test i = 0)
  have hWordEval (i : I) (g : K) : (word i).eval g = τ (u₀ i + g * u₁ i) := by
    simp only [word, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, map_add, map_mul, hpower g]
  have hWordDegree (i : I) : (word i).natDegree ≤ power := by
    dsimp only [word]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (Polynomial.natDegree_mul_C_le _ _).trans (by simp)
  have htestDegree (i : I) : (test i).natDegree ≤ max numCap (denCap + power) := by
    unfold test
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le_max (hNcap (x i)) ?_)
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hDcap (x i)) (hWordDegree i))
  have hnodeChart (g : K) (hg : g ∈ seeds) (i : I) :
      (D (x i)).eval g * ((selected g).map τ).eval (x i) = (N (x i)).eval g :=
    hnode (x i) g ((selected g).map τ) (heq g hg)
  have htestEval (i : I) (g : K) :
      (test i).eval g = (N (x i)).eval g - (D (x i)).eval g * τ (u₀ i + g * u₁ i) := by
    simp only [test, Polynomial.eval_sub, Polynomial.eval_mul, hWordEval i]
  by_cases hsmall : identities.card ≤ w
  · apply le_trans _ (le_max_left _ _)
    apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hw)).mpr
    apply RCN173.sharp_incidence_bound
      (fun g i => (selected g).eval (x i) = u₀ i + g * u₁ i)
      seeds nodes identities A w (max numCap (denCap + power)) (Finset.filter_subset _ _)
      hsmall hw hA hagreement
    intro i hi
    have hnonzero : test i ≠ 0 := by
      intro hz
      obtain ⟨hmem, hnot⟩ := Finset.mem_sdiff.mp hi
      exact hnot (Finset.mem_filter.mpr ⟨hmem, hz⟩)
    apply le_trans _ (htestDegree i)
    apply Polynomial.card_le_degree_of_subset_roots
    intro g hg
    obtain ⟨hseed, hfit⟩ := Finset.mem_filter.mp hg
    apply (Polynomial.mem_roots hnonzero).mpr
    rw [Polynomial.IsRoot, htestEval, ← hnodeChart g hseed i,
      map_eval_at_fixed_node x τ hfixed, hfit, sub_self]
  · apply le_trans _ (le_max_right _ _)
    refine identity_nodes_card_le x u₀ u₁ τ hfixed selected D N hD seeds identities
      w e denCap hDcap (Nat.lt_of_not_ge hsmall) hdegree ?_ hnodeChart hpencil
    intro i hi g _
    have hz : test i = 0 := (Finset.mem_filter.mp hi).2
    have h := congrArg (Polynomial.eval g) hz
    rw [htestEval, Polynomial.eval_zero] at h
    exact sub_eq_zero.mp h

def SeedDegreeFive (F : Polynomial (SeedPolynomial K)) : Prop :=
  ∀ j, (F.coeff j).degreeOf 0 ≤ 5 ∧ (F.coeff j).degreeOf 1 ≤ 5

private theorem map_frobenius_eval (F : Polynomial (SeedPolynomial K)) (p : ℕ) (g : K) :
    (F.map (frobeniusHom p)).map (evalRingHom g) =
      F.map (MvPolynomial.eval (coordinates g (g ^ p))) := by
  have h : (evalRingHom g).comp (frobeniusHom p) =
      MvPolynomial.eval (coordinates g (g ^ p)) := by
    apply RingHom.ext
    intro S
    exact eval_frobeniusHom p S g
  rw [Polynomial.map_map, h]

private theorem map_frobenius_coeff_degree (F : Polynomial (SeedPolynomial K))
    (hF : SeedDegreeFive F) (p j : ℕ) :
    ((F.map (frobeniusHom p)).coeff j).natDegree ≤ 5 * (p + 1) := by
  rw [Polynomial.coeff_map]
  have h := hF j
  refine (natDegree_frobeniusHom_le (b := 6) (c := 6) p _
    (Nat.lt_succ_of_le h.1) (Nat.lt_succ_of_le h.2)).trans_eq ?_
  simp
  omega

private theorem map_frobenius_ne_zero {p : ℕ} (hp : 0 < p) (hwidth : 6 ≤ p)
    (F : Polynomial (SeedPolynomial K)) (hF : SeedDegreeFive F) (hne : F ≠ 0) :
    F.map (frobeniusHom p) ≠ 0 := by
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hne
  intro hz
  apply frobeniusHom_nonzero hp hwidth (Polynomial.mem_support_iff.mp hj)
    (b := 6) (c := 6) (Nat.lt_succ_of_le (hF j).1) (Nat.lt_succ_of_le (hF j).2)
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using
    congrArg (fun q : Polynomial K[X] => q.coeff j) hz

theorem primitive_rows_card_le {p w A e : ℕ} (hp : 0 < p) (hwidth : 6 ≤ p)
    (x : I ↪ K) (u₀ u₁ : I → K) (σ : K →+* K)
    (hfixed : ∀ i, σ (x i) = x i) (hσ : ∀ g, σ g = g ^ p)
    (β α₀ α₁ : Polynomial (SeedPolynomial K))
    (hβ : SeedDegreeFive β) (h₀ : SeedDegreeFive α₀) (h₁ : SeedDegreeFive α₁)
    (hone : (α₀ ≠ 0 ∧ α₁ = 0) ∨ (α₀ = 0 ∧ α₁ ≠ 0))
    (seeds : Finset K) (nodes : Finset I) (selected : K → K[X])
    (hwa : w < A) (han : A ≤ nodes.card)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagreement : ∀ g ∈ seeds,
      A ≤ (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hrow : ∀ g ∈ seeds,
      let f := MvPolynomial.eval (coordinates g (g ^ p))
      β.map f + α₀.map f * selected g + α₁.map f * (selected g).map σ = 0)
    (hpencil : ∀ q₀ q₁ : K[X], q₀.natDegree ≤ w → q₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected q₀ q₁).card ≤ e + 1) :
    seeds.card ≤ max ((nodes.card - w) * (6 * (p + 1)) / (A - w))
      ((w + 1) * (5 * (p + 1)) + (e + 1)) := by
  let N := (-β).map (frobeniusHom p)
  have hNdegree : ∀ j, (N.coeff j).natDegree ≤ 5 * (p + 1) := by
    intro j
    simpa only [N, Polynomial.map_neg, Polynomial.coeff_neg, Polynomial.natDegree_neg]
      using map_frobenius_coeff_degree β hβ p j
  have count (α : Polynomial (SeedPolynomial K)) (hα : SeedDegreeFive α) (hne : α ≠ 0)
      (τ : K →+* K) (hτfixed : ∀ i, τ (x i) = x i) (power : ℕ)
      (hpower : ∀ g, τ g = g ^ power) (hpowerLe : power ≤ p)
      (hproduct : ∀ g ∈ seeds,
        let f := MvPolynomial.eval (coordinates g (g ^ p))
        α.map f * (selected g).map τ = (-β).map f) :
      seeds.card ≤ max ((nodes.card - w) * (6 * (p + 1)) / (A - w))
        ((w + 1) * (5 * (p + 1)) + (e + 1)) := by
    have hChart : ∀ g ∈ seeds, ((α.map (frobeniusHom p)).map (evalRingHom g)) * (selected g).map τ =
        N.map (evalRingHom g) := by
      intro g hg
      dsimp only [N]
      rw [map_frobenius_eval, map_frobenius_eval]
      exact hproduct g hg
    apply (encoded_chart_card_le x u₀ u₁ τ hτfixed power hpower selected _ N
      (map_frobenius_ne_zero hp hwidth α hα hne) seeds nodes w A e _ _
      hwa han hdegree hagreement (map_frobenius_coeff_degree α hα p) hNdegree hChart hpencil).trans
    apply max_le_max _ le_rfl
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (max_le (by omega) (by omega)))
  rcases hone with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · apply count α₀ h₀ hfirst (RingHom.id K) (fun _ => rfl) 1 (fun g => by simp) (by omega)
    intro g hg
    have hh := hrow g hg
    simp only [hsecond, Polynomial.map_zero, zero_mul, add_zero] at hh
    simp only [Polynomial.map_neg, Polynomial.map_id]
    linear_combination hh
  · apply count α₁ h₁ hsecond σ hfixed p hσ le_rfl
    intro g hg
    have hh := hrow g hg
    simp only [hfirst, Polynomial.map_zero, zero_mul, add_zero] at hh
    simp only [Polynomial.map_neg]
    linear_combination hh


theorem one_sided_of_nonzero_multiplier
    {m a₀ a₁ : Polynomial (SeedPolynomial K)} (hm : m ≠ 0)
    (hone : (a₀ ≠ 0 ∧ a₁ = 0) ∨ (a₀ = 0 ∧ a₁ ≠ 0)) :
    (m * a₀ ≠ 0 ∧ m * a₁ = 0) ∨ (m * a₀ = 0 ∧ m * a₁ ≠ 0) := by
  rcases hone with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · exact Or.inl ⟨mul_ne_zero hm h₀, by rw [h₁, mul_zero]⟩
  · exact Or.inr ⟨by rw [h₀, mul_zero], mul_ne_zero hm h₁⟩

theorem one_sided_comparison_card_le [Fintype I]
    {p w A a e : ℕ} (hp : 0 < p) (hwidth : 6 ≤ p)
    (x : I ↪ K) (U : Fin 2 → I → K) (σ : K →+* K)
    (hfixed : ∀ i, σ (x i) = x i) (hσ : ∀ g, σ g = g ^ p)
    (haPos : 0 < a) (ha : a + w = A) (han : A ≤ Fintype.card I)
    (θ : ComparisonSpace A a 4 x (fun j i => if j = 0 then U 0 i else σ (U 0 i))
      (fun j i => if j = 0 then U 1 i else σ (U 1 i)))
    (hone : let q := symbolicRow θ.1
      (q.first ≠ 0 ∧ q.second = 0) ∨ (q.first = 0 ∧ q.second ≠ 0))
    (seeds : Finset K) (selected : K → K[X])
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagreement : ∀ g ∈ seeds,
      A ≤ (Finset.univ.filter (fun i => (selected g).eval (x i) = U 0 i + g * U 1 i)).card)
    (hpencil : ∀ q₀ q₁ : K[X], q₀.natDegree ≤ w → q₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected q₀ q₁).card ≤ e + 1) :
    seeds.card ≤ max ((Fintype.card I - w) * (6 * (p + 1)) / (A - w))
      ((w + 1) * (5 * (p + 1)) + (e + 1)) := by
  rw [← Finset.card_univ (α := I)]
  refine primitive_rows_card_le hp hwidth x (U 0) (U 1) σ hfixed hσ
    (symbolicRow θ.1).beta (symbolicRow θ.1).first (symbolicRow θ.1).second
    ?_ ?_ ?_ hone seeds Finset.univ selected (by omega) (by simpa using han)
    hdegree hagreement ?_ hpencil
  · intro j
    exact (symbolicRow_seed_degree_bounds θ.1 j).1
  · intro j
    have hb := (symbolicRow_seed_degree_bounds θ.1 j).2.1
    exact ⟨hb.1.trans (by decide), hb.2⟩
  · intro j
    have hb := (symbolicRow_seed_degree_bounds θ.1 j).2.2
    exact ⟨hb.1, hb.2.trans (by decide)⟩
  · intro g hg
    dsimp only
    obtain ⟨hb, h₀, h₁⟩ := symbolicRow_map_seedEval θ.1 (coordinates g (g ^ p))
    rw [hb, h₀, h₁]
    simpa [coordinates, ← hσ g] using
      specialize_selected_eq_zero x U σ hfixed haPos ha θ g (selected g) (hdegree g hg)
        _ (hagreement g hg) (fun _ hi => (Finset.mem_filter.mp hi).2)

theorem koala_one_sided_budget :
    max ((262144 - 131071 : ℕ) * (6 * (2130706433 + 1)) / (180957 - 131071))
      ((131071 + 1) * (5 * (2130706433 + 1)) + (81187 + 1)) =
      1396379768667428 := by
  decide +kernel


end

end ProximityPrize.SubmissionLower.Koala6844OneSided

namespace ProximityPrize.SubmissionLower.Koala6844Cramer

open Polynomial
open scoped BigOperators Classical Matrix Polynomial

variable {K ι : Type*} [Field K]

theorem equation_of_node_agreement (domain : ι ↪ K) (nodes : Finset ι)
    (denominator selected numerator₀ numerator₁ : K[X]) (g : K) (w deg : ℕ)
    (hden : denominator.natDegree ≤ deg) (hsel : selected.natDegree ≤ w)
    (hnum₀ : numerator₀.natDegree ≤ w + deg) (hnum₁ : numerator₁.natDegree ≤ w + deg)
    (hcard : w + deg < nodes.card)
    (heval : ∀ i ∈ nodes, denominator.eval (domain i) * selected.eval (domain i) =
      numerator₀.eval (domain i) + g * numerator₁.eval (domain i)) :
    denominator * selected = numerator₀ + C g * numerator₁ := by
  classical
  let difference := denominator * selected - (numerator₀ + C g * numerator₁)
  have hdegree : difference.natDegree ≤ w + deg := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simpa only [Nat.add_comm deg w] using natDegree_mul_le_of_le hden hsel
    · exact (natDegree_add_le _ _).trans
        (max_le hnum₀ ((natDegree_C_mul_le _ _).trans hnum₁))
  suffices difference = 0 from sub_eq_zero.mp this
  by_contra hnonzero
  have hroots : (nodes.image domain).card ≤ difference.natDegree := by
    apply card_le_degree_of_subset_roots
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_roots hnonzero).mpr
    simpa only [IsRoot, difference, eval_sub, eval_mul, eval_add, eval_C, sub_eq_zero] using
      heval i hi
  rw [Finset.card_image_of_injective _ domain.injective] at hroots
  exact (not_le_of_gt hcard) (hroots.trans hdegree)

theorem polynomial_pencil_of_common_denominator [DecidableEq K]
    (seeds : Finset K) (selected : K → K[X]) (denominator numerator₀ numerator₁ : K[X])
    (hden : denominator ≠ 0) (hsize : 1 < seeds.card) (w : ℕ)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hrelation : ∀ g ∈ seeds, denominator * selected g = numerator₀ + C g * numerator₁) :
    ∃ endpoint₀ endpoint₁ : K[X], endpoint₀.natDegree ≤ w ∧ endpoint₁.natDegree ≤ w ∧
      ∀ g ∈ seeds, selected g = endpoint₀ + C g * endpoint₁ := by
  obtain ⟨g, hg, h, hh, hne⟩ := Finset.one_lt_card.mp hsize
  let inverseDifference := C ((h - g)⁻¹)
  let endpoint₁ := inverseDifference * (selected h - selected g)
  let endpoint₀ := selected g - C g * endpoint₁
  have hdeg₁ : endpoint₁.natDegree ≤ w :=
    (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans
      (max_le (hdegree h hh) (hdegree g hg)))
  have hdeg₀ : endpoint₀.natDegree ≤ w := (natDegree_sub_le _ _).trans
    (max_le (hdegree g hg) ((natDegree_C_mul_le _ _).trans hdeg₁))
  have hcoeff : inverseDifference * (C h - C g) = 1 := by
    dsimp only [inverseDifference]
    rw [← map_sub, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm), map_one]
  have hendpoint₁ : denominator * endpoint₁ = numerator₁ := by
    calc
      denominator * endpoint₁ =
          inverseDifference * (denominator * selected h - denominator * selected g) := by
        dsimp only [endpoint₁]
        ring
      _ = (inverseDifference * (C h - C g)) * numerator₁ := by
        rw [hrelation h hh, hrelation g hg]
        ring
      _ = numerator₁ := by rw [hcoeff, one_mul]
  have hendpoint₀ : denominator * endpoint₀ = numerator₀ := by
    calc
      denominator * endpoint₀ = denominator * selected g - C g * (denominator * endpoint₁) := by
        dsimp only [endpoint₀]
        ring
      _ = numerator₀ := by rw [hrelation g hg, hendpoint₁, add_sub_cancel_right]
  refine ⟨endpoint₀, endpoint₁, hdeg₀, hdeg₁, ?_⟩
  intro t ht
  apply mul_left_cancel₀ hden
  rw [hrelation t ht, mul_add, show denominator * (C t * endpoint₁) =
    C t * (denominator * endpoint₁) by ring, hendpoint₀, hendpoint₁]

theorem card_le_of_common_denominator [DecidableEq K]
    (seeds : Finset K) (selected : K → K[X]) (denominator numerator₀ numerator₁ : K[X])
    (hden : denominator ≠ 0) (w e : ℕ)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hrelation : ∀ g ∈ seeds, denominator * selected g = numerator₀ + C g * numerator₁)
    (hno : ∀ P₀ P₁ : K[X], P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (seeds.filter (fun γ ↦ selected γ = P₀ + C γ * P₁)).card ≤ e + 1) :
    seeds.card ≤ e + 1 := by
  classical
  by_cases hsmall : seeds.card ≤ 1
  · exact hsmall.trans (Nat.succ_le_succ (Nat.zero_le e))
  obtain ⟨P₀, P₁, h₀, h₁, hp⟩ := polynomial_pencil_of_common_denominator
    seeds selected denominator numerator₀ numerator₁ hden (lt_of_not_ge hsmall) w hdegree hrelation
  have hfilter : (seeds.filter (fun γ ↦ selected γ = P₀ + C γ * P₁)) = seeds := by
    ext g
    exact Finset.mem_filter.trans ⟨fun h ↦ h.1, fun hg ↦ ⟨hg, hp g hg⟩⟩
  simpa only [hfilter] using hno P₀ P₁ h₀ h₁

theorem det_natDegree_le_of_column_bounds {m : ℕ} (M : Matrix (Fin m) (Fin m) K[X])
    (bound : Fin m → ℕ) (hbound : ∀ i j, (M i j).natDegree ≤ bound j) :
    M.det.natDegree ≤ ∑ j, bound j := by
  rw [Matrix.det_apply']
  apply natDegree_sum_le_of_forall_le
  intro σ _
  have hprod : (∏ j, M (σ j) j).natDegree ≤ ∑ j, bound j :=
    (natDegree_prod_le (s := Finset.univ) (f := fun j ↦ M (σ j) j)).trans
      (Finset.sum_le_sum fun j _ ↦ hbound (σ j) j)
  have hsign : (((Equiv.Perm.sign σ : ℤ) : K[X])).natDegree ≤ 0 := by simp
  simpa only [Nat.zero_add] using natDegree_mul_le_of_le hsign hprod

theorem cramer_natDegree_le {m : ℕ} (M : Matrix (Fin m) (Fin m) K[X])
    (rhs : Fin m → K[X]) (col : Fin m) (w δ : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ δ) (hrhs : ∀ i, (rhs i).natDegree ≤ w + δ) :
    ((M.updateCol col rhs).det).natDegree ≤ w + m * δ := by
  let bounds : Fin m → ℕ := fun j ↦ δ + if j = col then w else 0
  have hdet := det_natDegree_le_of_column_bounds (M.updateCol col rhs) bounds (by
    intro i j
    by_cases h : j = col
    · subst j
      simpa [Matrix.updateCol_apply, bounds, Nat.add_comm] using hrhs i
    · simpa [Matrix.updateCol_apply, bounds, h] using hM i j)
  simpa [bounds, Finset.sum_add_distrib, Nat.add_comm] using hdet

theorem eval_cramer_identity {m : ℕ} (M : Matrix (Fin m) (Fin m) K[X])
    (rhs : Fin m → K[X]) (x : K) (values : Fin m → K) (col : Fin m)
    (hrow : (evalRingHom x).mapMatrix M *ᵥ values = fun i ↦ (rhs i).eval x) :
    M.det.eval x * values col = ((M.updateCol col rhs).det).eval x := by
  let f := evalRingHom x
  let A := f.mapMatrix M
  have hmap : f.mapMatrix (M.updateCol col rhs) = A.updateCol col (fun i ↦ f (rhs i)) := by
    exact Matrix.map_updateCol (f := f) (M := M) (j := col) (c := rhs)
  have hrow' : A *ᵥ values = fun i ↦ f (rhs i) := hrow
  have hcramer : A.cramer (fun i ↦ f (rhs i)) = A.det • values := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hrow', Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  change f M.det * values col = f ((M.updateCol col rhs).det)
  rw [f.map_det, f.map_det, hmap, ← Matrix.cramer_apply, hcramer]
  rfl

theorem augmented_minor_eq_zero (domain : ι ↪ K) (nodes : Finset ι)
    (M : Matrix (Fin 4) (Fin 4) K[X]) (rhs : Fin 4 → K[X]) (values : ι → Fin 4 → K)
    (w δ : ℕ) (col : Fin 4) (hdet : M.det = 0)
    (hM : ∀ i j, (M i j).natDegree ≤ δ) (hrhs : ∀ i, (rhs i).natDegree ≤ w + δ)
    (hcard : w + 4 * δ < nodes.card)
    (hrow : ∀ i ∈ nodes,
      (evalRingHom (domain i)).mapMatrix M *ᵥ values i = fun j ↦ (rhs j).eval (domain i)) :
    (M.updateCol col rhs).det = 0 := by
  classical
  by_contra hnonzero
  have hroots : (nodes.image domain).card ≤ ((M.updateCol col rhs).det).natDegree := by
    apply card_le_degree_of_subset_roots
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_roots hnonzero).mpr
    simpa only [IsRoot, hdet, eval_zero, zero_mul] using
      (eval_cramer_identity M rhs (domain i) (values i) col (hrow i hi)).symm
  rw [Finset.card_image_of_injective _ domain.injective] at hroots
  exact (not_le_of_gt hcard) (hroots.trans (cramer_natDegree_le M rhs col w δ hM hrhs))

theorem card_le_of_rank_four [DecidableEq K] (domain : ι ↪ K)
    (seeds : Finset K) (agreement : K → Finset ι) (selected : K → K[X])
    (M : Matrix (Fin 4) (Fin 4) K[X]) (rhs : Fin 4 → K[X]) (values : ι → Fin 4 → K)
    (w δ e : ℕ) (hdet : M.det ≠ 0) (hM : ∀ i j, (M i j).natDegree ≤ δ)
    (hrhs : ∀ i, (rhs i).natDegree ≤ w + δ)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagree : ∀ g ∈ seeds, w + 4 * δ < (agreement g).card)
    (hrow : ∀ g ∈ seeds, ∀ i ∈ agreement g,
      (evalRingHom (domain i)).mapMatrix M *ᵥ values i = fun j ↦ (rhs j).eval (domain i))
    (hfit : ∀ g ∈ seeds, ∀ i ∈ agreement g,
      (selected g).eval (domain i) = values i 0 + g * values i 1)
    (hno : ∀ P₀ P₁ : K[X], P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (seeds.filter (fun γ ↦ selected γ = P₀ + C γ * P₁)).card ≤ e + 1) :
    seeds.card ≤ e + 1 := by
  let numerator₀ := (M.updateCol 0 rhs).det
  let numerator₁ := (M.updateCol 1 rhs).det
  apply card_le_of_common_denominator seeds selected M.det numerator₀ numerator₁ hdet w e hdegree
    _ hno
  intro g hg
  refine equation_of_node_agreement domain (agreement g) M.det (selected g) numerator₀ numerator₁
    g w (4 * δ) ?_ (hdegree g hg) (cramer_natDegree_le M rhs 0 w δ hM hrhs)
    (cramer_natDegree_le M rhs 1 w δ hM hrhs) (hagree g hg) ?_
  · simpa using det_natDegree_le_of_column_bounds M (fun _ ↦ δ) hM
  · intro i hi
    have h₀ := eval_cramer_identity M rhs (domain i) (values i) 0 (hrow g hg i hi)
    have h₁ := eval_cramer_identity M rhs (domain i) (values i) 1 (hrow g hg i hi)
    rw [hfit g hg i hi, show numerator₀.eval (domain i) = _ from h₀.symm,
      show numerator₁.eval (domain i) = _ from h₁.symm]
    ring

end ProximityPrize.SubmissionLower.Koala6844Cramer

namespace ProximityPrize.SubmissionLower.Koala6844CoefficientSystem

open Polynomial
open scoped BigOperators Classical Matrix Polynomial

variable {K : Type*} [Field K]

abbrev SeedRing (K : Type*) [CommRing K] := MvPolynomial (Fin 2) K
abbrev SeedMonomial := Fin 2 →₀ ℕ

noncomputable def coefficientPolynomial (P : (SeedRing K)[X])
    (key : SeedMonomial) (cap : ℕ) : K[X] :=
  ∑ i ∈ Finset.range (cap + 1), monomial i ((P.coeff i).coeff key)

theorem coefficientPolynomial_degree (P : (SeedRing K)[X])
    (key : SeedMonomial) (cap : ℕ) : (coefficientPolynomial P key cap).natDegree ≤ cap := by
  unfold coefficientPolynomial
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

theorem eval_coefficientPolynomial (P : (SeedRing K)[X])
    (key : SeedMonomial) (cap : ℕ) (x : K) (hP : P.natDegree ≤ cap) :
    (coefficientPolynomial P key cap).eval x = (P.eval (MvPolynomial.C x)).coeff key := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), MvPolynomial.coeff_sum]
  simp only [coefficientPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro i _
  symm
  calc
    _ = (MvPolynomial.C (x ^ i) * P.coeff i).coeff key := by rw [map_pow, mul_comm]
    _ = _ := by rw [MvPolynomial.coeff_C_mul, mul_comm]

theorem matrix_node_equation {m : ℕ} (cols : Fin m → (SeedRing K)[X])
    (rhs : (SeedRing K)[X]) (keys : Fin m → SeedMonomial) (w δ : ℕ) (x : K)
    (word : Fin m → K) (hcols : ∀ j, (cols j).natDegree ≤ δ) (hrhs : rhs.natDegree ≤ w + δ)
    (h : (∑ j, MvPolynomial.C (word j) * (cols j).eval (MvPolynomial.C x)) =
      rhs.eval (MvPolynomial.C x)) :
    (evalRingHom x).mapMatrix (Matrix.of fun i j ↦ coefficientPolynomial (cols j) (keys i) δ)
        *ᵥ word = fun i ↦ (coefficientPolynomial rhs (keys i) (w + δ)).eval x := by
  funext i
  change (∑ j, (coefficientPolynomial (cols j) (keys i) δ).eval x * word j) =
    (coefficientPolynomial rhs (keys i) (w + δ)).eval x
  rw [eval_coefficientPolynomial _ _ _ _ hrhs]
  simp_rw [eval_coefficientPolynomial _ _ _ _ (hcols _)]
  have hcoeff := congrArg (fun p : SeedRing K ↦ p.coeff (keys i)) h
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul] at hcoeff
  simpa only [mul_comm] using hcoeff

theorem card_le_of_nonsingular_coefficients {ι : Type*} [DecidableEq K] (domain : ι ↪ K)
    (seeds : Finset K) (agreement : K → Finset ι) (selected : K → K[X])
    (cols : Fin 4 → (SeedRing K)[X]) (rhs : (SeedRing K)[X]) (keys : Fin 4 → SeedMonomial)
    (word : ι → Fin 4 → K) (w δ e : ℕ)
    (hdet : (Matrix.of fun i j ↦ coefficientPolynomial (cols j) (keys i) δ).det ≠ 0)
    (hcols : ∀ j, (cols j).natDegree ≤ δ) (hrhs : rhs.natDegree ≤ w + δ)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagree : ∀ g ∈ seeds, w + 4 * δ < (agreement g).card)
    (hnode : ∀ g ∈ seeds, ∀ i ∈ agreement g,
      (∑ j, MvPolynomial.C (word i j) * (cols j).eval (MvPolynomial.C (domain i))) =
        rhs.eval (MvPolynomial.C (domain i)))
    (hfit : ∀ g ∈ seeds, ∀ i ∈ agreement g, (selected g).eval (domain i) = word i 0 + g * word i 1)
    (hno : ∀ P₀ P₁ : K[X], P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (seeds.filter (fun g ↦ selected g = P₀ + C g * P₁)).card ≤ e + 1) :
    seeds.card ≤ e + 1 := by
  apply Koala6844Cramer.card_le_of_rank_four domain seeds agreement selected
    (Matrix.of fun i j ↦ coefficientPolynomial (cols j) (keys i) δ)
    (fun i ↦ coefficientPolynomial rhs (keys i) (w + δ)) word w δ e hdet
    (fun _ _ ↦ coefficientPolynomial_degree _ _ _) (fun _ ↦ coefficientPolynomial_degree _ _ _)
    hdegree hagree ?_ hfit hno
  intro g hg i hi
  exact matrix_node_equation cols rhs keys w δ (domain i) (word i) hcols hrhs (hnode g hg i hi)

end ProximityPrize.SubmissionLower.Koala6844CoefficientSystem

namespace ProximityPrize.SubmissionLower.Koala6844RankFour

open Polynomial
open scoped BigOperators Classical Matrix Polynomial
open Koala6844Comparison (SymbolicRow)
open Koala6844CoefficientSystem (SeedRing SeedMonomial coefficientPolynomial)

set_option maxHeartbeats 1800000

variable {K I : Type*} [Field K]

noncomputable def columns (q : SymbolicRow (SeedRing K)) : Fin 4 → (SeedRing K)[X] :=
  ![q.first, Polynomial.C (MvPolynomial.X 0) * q.first,
    q.second, Polynomial.C (MvPolynomial.X 1) * q.second]

noncomputable def matrix (q : SymbolicRow (SeedRing K)) (keys : Fin 4 → SeedMonomial)
    (δ : ℕ) : Matrix (Fin 4) (Fin 4) K[X] :=
  Matrix.of fun i j ↦ coefficientPolynomial (columns q j) (keys i) δ

private theorem columns_degree (q : SymbolicRow (SeedRing K)) (δ : ℕ)
    (hfirst : q.first.natDegree ≤ δ) (hsecond : q.second.natDegree ≤ δ) :
    ∀ j, (columns q j).natDegree ≤ δ := by
  intro j
  fin_cases j
  · exact hfirst
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hfirst
  · exact hsecond
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hsecond

theorem equation_of_good_node (q : SymbolicRow (SeedRing K)) (x : K) (word : Fin 4 → K)
    (h : q.atNode (MvPolynomial.C x)
      (MvPolynomial.C (word 0) + MvPolynomial.X 0 * MvPolynomial.C (word 1))
      (MvPolynomial.C (word 2) + MvPolynomial.X 1 * MvPolynomial.C (word 3)) = 0) :
    (∑ j, MvPolynomial.C (word j) * (columns q j).eval (MvPolynomial.C x)) =
      (-q.beta).eval (MvPolynomial.C x) := by
  unfold SymbolicRow.atNode at h
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    columns, Matrix.cons_val_zero, Matrix.cons_val_succ, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_neg]
  simp only [show (0 : Fin 3).succ = (1 : Fin 4) by decide,
    show (0 : Fin 2).succ.succ = (2 : Fin 4) by decide,
    show (0 : Fin 1).succ.succ.succ = (3 : Fin 4) by decide]
  linear_combination h

theorem retained_card_le [DecidableEq K] (domain : I ↪ K)
    (retained : Finset K) (agreement : K → Finset I) (selected : K → K[X])
    (q : SymbolicRow (SeedRing K)) (keys : Fin 4 → SeedMonomial) (word : I → Fin 4 → K)
    (δ : ℕ) (hδ : δ ≤ 11499) (hdet : (matrix q keys δ).det ≠ 0)
    (hbeta : q.beta.natDegree ≤ 131071 + δ)
    (hfirst : q.first.natDegree ≤ δ) (hsecond : q.second.natDegree ≤ δ)
    (hdegree : ∀ g ∈ retained, (selected g).natDegree ≤ 131071)
    (hcard : ∀ g ∈ retained, 180957 ≤ (agreement g).card)
    (hgood : ∀ g ∈ retained, ∀ i ∈ agreement g,
      q.atNode (MvPolynomial.C (domain i))
        (MvPolynomial.C (word i 0) + MvPolynomial.X 0 * MvPolynomial.C (word i 1))
        (MvPolynomial.C (word i 2) + MvPolynomial.X 1 * MvPolynomial.C (word i 3)) = 0)
    (hfit : ∀ g ∈ retained, ∀ i ∈ agreement g, (selected g).eval (domain i) = word i 0 + g * word i 1)
    (hno : ∀ P₀ P₁ : K[X], P₀.natDegree ≤ 131071 → P₁.natDegree ≤ 131071 →
      (retained.filter (fun g ↦ selected g = P₀ + C g * P₁)).card ≤ 81188) :
    retained.card ≤ 81188 := by
  have hneg : (-q.beta).natDegree ≤ 131071 + δ := by simpa using hbeta
  apply Koala6844CoefficientSystem.card_le_of_nonsingular_coefficients domain retained agreement
    selected (columns q) (-q.beta) keys word 131071 δ 81187 hdet
    (columns_degree q δ hfirst hsecond) hneg hdegree ?_ ?_ hfit hno
  · intro g hg
    have hn := hcard g hg
    omega
  · exact fun g hg i hi ↦ equation_of_good_node q (domain i) (word i) (hgood g hg i hi)

end ProximityPrize.SubmissionLower.Koala6844RankFour


namespace ProximityPrize.SubmissionLower.Koala6844BenchmarkPrimitive

open ProximityPrize.Benchmark
open Koala6844BenchmarkField Koala6844BenchmarkCases Koala6844Comparison Koala6844Protocol
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

theorem one_sided_rows_le_seed_budget
    {received : ReceivedWords} (row : ComparisonRows received 4)
    (hone : let q := symbolicRow row.1
      (q.first ≠ 0 ∧ q.second = 0) ∨ (q.first = 0 ∧ q.second ≠ 0))
    (seeds : Finset IRSProfile.Field) (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (support : Selection received seeds selected) : seeds.card ≤ mcaBudget := by
  have bound := Koala6844OneSided.one_sided_comparison_card_le
    (p := prime) (w := 131071) (e := 81187)
    (by decide) (by decide) IRSProfile.domain received frobenius.toRingHom
    domain_fixed frobenius_apply (by decide) (by decide)
    (by rw [IRSProfile.card_index]; decide)
    row hone seeds selected support.degree_le support.agreement support.pencil
  rw [IRSProfile.card_index, Koala6844OneSided.koala_one_sided_budget] at bound
  exact bound.trans (by decide +kernel)

def TwoSidedPrimitiveSeedBound : Prop :=
  ∀ (received : ReceivedWords) (seeds : Finset IRSProfile.Field)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field),
    Selection received seeds selected →
    ∀ (row : ComparisonRows received 4)
      (q : SymbolicRow (SeedRing IRSProfile.Field)) (m : SeedCoefficients IRSProfile.Field),
      q.first ≠ 0 → q.second ≠ 0 → m ≠ 0 → IsPrimitiveRow q →
      RowFactors q (rankRow row.1) m →
      primitiveExcess 131071 q +
        (primitiveBadNodes IRSProfile.domain (conjugateWord received 0)
          (conjugateWord received 1) q).card ≤ 31614 →
      seeds.card ≤ mcaBudget

private theorem cross_eq_of_symbolic_det_zero {K : Type*} [Field K] {A a d₀ d₁ : ℕ}
    (first : RowIndex A a d₀ → K) (second : RowIndex A a d₁ → K)
    (hzero : rowDeterminant first second = 0) :
    (rankRow first).first * (rankRow second).second =
      (rankRow second).first * (rankRow first).second := by
  unfold rowDeterminant at hzero
  simpa only [rankRow, mul_comm (symbolicRow first).second (symbolicRow second).first]
    using sub_eq_zero.mp hzero

private theorem comparison_one_sided_of_factor {K : Type} [Field K] {A a d : ℕ}
    (row : RowIndex A a d → K) (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K)
    (hm : m ≠ 0) (hfactor : RowFactors q (rankRow row) m)
    (hone : (q.first ≠ 0 ∧ q.second = 0) ∨ (q.first = 0 ∧ q.second ≠ 0)) :
    let r := symbolicRow row
    (r.first ≠ 0 ∧ r.second = 0) ∨ (r.first = 0 ∧ r.second ≠ 0) := by
  have hr := Koala6844OneSided.one_sided_of_nonzero_multiplier hm hone
  rw [← hfactor.first, ← hfactor.second] at hr
  simpa only [rankRow] using hr

private theorem card_le_from_primitive_cases {K I : Type} [Field K] [Fintype I]
    (x : I ↪ K) (u v : Fin 2 → I → K) (hcard : Fintype.card I = 262144)
    (row : ComparisonSpace 180957 49886 4 x u v) (hrow : row.1 ≠ 0)
    (hdet : ∀ other : ComparisonSpace 180957 49886 200 x u v,
      rowDeterminant row.1 other.1 = 0)
    (seedCount budget : ℕ)
    (honeCase : (let r := symbolicRow row.1
      (r.first ≠ 0 ∧ r.second = 0) ∨ (r.first = 0 ∧ r.second ≠ 0)) → seedCount ≤ budget)
    (hbothCase : ∀ (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K),
      q.first ≠ 0 → q.second ≠ 0 → m ≠ 0 → IsPrimitiveRow q → RowFactors q (rankRow row.1) m →
      primitiveExcess 131071 q + (primitiveBadNodes x u v q).card ≤ 31614 → seedCount ≤ budget) :
    seedCount ≤ budget := by
  obtain ⟨q, m, hm, hactive, hprimitive, hfactor, hlarge⟩ :=
    exists_primitive_comparison_generator x u v row hrow (by rw [hcard]; decide)
      (fun other => cross_eq_of_symbolic_det_zero row.1 other.1 (hdet other))
  by_cases hone : (q.first ≠ 0 ∧ q.second = 0) ∨ (q.first = 0 ∧ q.second ≠ 0)
  · exact honeCase (comparison_one_sided_of_factor row.1 q m hm hfactor hone)
  · have hboth : q.first ≠ 0 ∧ q.second ≠ 0 := by
      rcases hactive with hf | hs
      · exact ⟨hf, fun hz => hone (Or.inl ⟨hf, hz⟩)⟩
      · exact ⟨fun hz => hone (Or.inr ⟨hz, hs⟩), hs⟩
    have hcap := primitive_excess_add_badCard_le_31606 x u v q hboth.1 hboth.2 hcard hlarge
    exact hbothCase q m
      hboth.1 hboth.2 hm hprimitive hfactor hcap

theorem rank_one_seed_bound_of_two_sided
    (hPrimitive : TwoSidedPrimitiveSeedBound) : RankOneSeedBound := by
  intro received seeds selected support row hrow hcollinear
  exact card_le_from_primitive_cases (K := IRSProfile.Field) (I := IRSProfile.Index)
    IRSProfile.domain (conjugateWord received 0)
    (conjugateWord received 1) IRSProfile.card_index row hrow
    hcollinear seeds.card mcaBudget
    (fun hone => one_sided_rows_le_seed_budget row hone seeds selected support)
    (hPrimitive received seeds selected support row)


end

end ProximityPrize.SubmissionLower.Koala6844BenchmarkPrimitive


namespace ProximityPrize.SubmissionLower.Koala6844BenchmarkRetention

open ProximityPrize.Benchmark
open Koala6844BenchmarkField Koala6844BenchmarkCases Koala6844BenchmarkPrimitive
open Koala6844Comparison Koala6844Protocol
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

abbrev badNodes (received : ReceivedWords) (q : SymbolicRow (SeedRing IRSProfile.Field)) :=
  primitiveBadNodes IRSProfile.domain (Koala6844BenchmarkCases.conjugateWord received 0)
    (Koala6844BenchmarkCases.conjugateWord received 1) q

def commonDiscardBudget : ℕ := 336811419554550

def retainedSeedBudget : ℕ := 274587713363640831

structure RetainedComparison (received : ReceivedWords) (retained : Finset IRSProfile.Field)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (q : SymbolicRow (SeedRing IRSProfile.Field)) : Prop where
  selection : Selection received retained selected
  first_ne : q.first ≠ 0
  second_ne : q.second ≠ 0
  primitive : IsPrimitiveRow q
  xDegree : q.beta.natDegree ≤ 180956 ∧ q.first.natDegree ≤ 49885 ∧ q.second.natDegree ≤ 49885
  seedDegree : ∀ j, ((q.beta.coeff j).degreeOf 0 ≤ 5 ∧ (q.beta.coeff j).degreeOf 1 ≤ 5) ∧
    ((q.first.coeff j).degreeOf 0 ≤ 4 ∧ (q.first.coeff j).degreeOf 1 ≤ 5) ∧
    ((q.second.coeff j).degreeOf 0 ≤ 5 ∧ (q.second.coeff j).degreeOf 1 ≤ 4)
  excess_bad : primitiveExcess 131071 q + (badNodes received q).card ≤ 31614
  good : ∀ g ∈ retained, primitiveSelected frobenius.toRingHom prime q selected g = 0 ∧
    Disjoint (agreementSet received selected g) (badNodes received q)

def RetainedTwoSidedSeedBound : Prop :=
  ∀ (received : ReceivedWords) (retained : Finset IRSProfile.Field)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (q : SymbolicRow (SeedRing IRSProfile.Field)),
    RetainedComparison received retained selected q → retained.card ≤ retainedSeedBudget

private theorem selection_of_subset {received : ReceivedWords}
    {seeds retained : Finset IRSProfile.Field} {selected : IRSProfile.Field → Polynomial IRSProfile.Field}
    (support : Selection received seeds selected) (hsub : retained ⊆ seeds) :
    Selection received retained selected := by
  refine ⟨fun g hg => support.degree_le g (hsub hg), fun g hg => support.agreement g (hsub hg), ?_⟩
  intro p₀ p₁ hp₀ hp₁
  refine (Finset.card_le_card (t := RCN050.pencilSeeds seeds selected p₀ p₁) ?_).trans
    (support.pencil p₀ p₁ hp₀ hp₁)
  intro g hg
  obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hg
  exact Finset.mem_filter.mpr ⟨hsub hmem, heq⟩

theorem primitive_bound_of_retained (hRetained : RetainedTwoSidedSeedBound) :
    TwoSidedPrimitiveSeedBound := by
  intro received seeds selected support row q m hfirst hsecond hm hprimitive hfactor hcap
  obtain ⟨retained, hsub, hseedCount, hrow⟩ := retain_primitive_rows
    (A := 180957) (a := 49886) (w := 131071) (p := prime)
    IRSProfile.domain frobenius.toRingHom domain_fixed frobenius_apply (by decide)
    received (by decide) (by decide) row q m hm (Or.inl hfirst) hfactor
    seeds (agreementSet received selected) selected support.degree_le support.agreement
    (fun g _ i hi => (Finset.mem_filter.mp hi).2)
  have hX := primitive_x_degree_caps row.1 q m hm hfactor
  have hB := primitive_seed_degree_caps row.1 q m hm hfactor
  have hretained := hRetained received retained selected q
    ⟨selection_of_subset support hsub, hfirst, hsecond, hprimitive, hX, hB, hcap, hrow⟩
  have hbad : (badNodes received q).card + 1 ≤ 31615 := by
    change primitiveExcess 131071 q + (badNodes received q).card ≤ 31614 at hcap
    omega
  have hdiscard : ((badNodes received q).card + 1) * (5 * (prime + 1)) ≤ commonDiscardBudget :=
    (Nat.mul_le_mul_right (5 * (prime + 1)) hbad).trans_eq (by decide +kernel)
  have hsum : retainedSeedBudget + commonDiscardBudget = mcaBudget := by decide +kernel
  calc
    seeds.card ≤ retained.card + ((badNodes received q).card + 1) * (5 * (prime + 1)) := hseedCount
    _ ≤ retainedSeedBudget + commonDiscardBudget := Nat.add_le_add hretained hdiscard
    _ = mcaBudget := hsum


end

end ProximityPrize.SubmissionLower.Koala6844BenchmarkRetention


namespace ProximityPrize.SubmissionLower.Koala6844BenchmarkGeometry

open ProximityPrize.Benchmark
open Koala6844BenchmarkField Koala6844BenchmarkCases Koala6844BenchmarkRetention
open Koala6844Comparison
open scoped Classical Matrix

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

private def word (received : ReceivedWords) (i : IRSProfile.Index) : Fin 4 → IRSProfile.Field :=
  ![received 0 i, received 1 i, frobenius (received 0 i), frobenius (received 1 i)]

theorem rank_four_retained_le_seed_budget
    {received : ReceivedWords} {retained : Finset IRSProfile.Field}
    {selected : IRSProfile.Field → Polynomial IRSProfile.Field}
    {q : SymbolicRow (SeedRing IRSProfile.Field)}
    (h : RetainedComparison received retained selected q)
    (hδ : primitiveExcess 131071 q ≤ 11499)
    (keys : Fin 4 → Koala6844CoefficientSystem.SeedMonomial)
    (hdet : (Koala6844RankFour.matrix q keys (primitiveExcess 131071 q)).det ≠ 0) :
    retained.card ≤ retainedSeedBudget := by
  let δ := primitiveExcess 131071 q
  have hbetaExcess : q.beta.natDegree - 131071 ≤ δ := le_max_left _ _
  have hβ : q.beta.natDegree ≤ 131071 + δ := by omega
  have hfirst : q.first.natDegree ≤ δ := (le_max_left _ _).trans (le_max_right _ _)
  have hsecond : q.second.natDegree ≤ δ := (le_max_right _ _).trans (le_max_right _ _)
  refine (Koala6844RankFour.retained_card_le (K := IRSProfile.Field) (I := IRSProfile.Index)
    IRSProfile.domain retained (agreementSet received selected) selected
    q keys (word received) δ hδ hdet hβ hfirst hsecond h.selection.degree_le
    h.selection.agreement ?_ ?_ ?_).trans (by decide +kernel)
  · intro g hg i hi
    have hnotBad : i ∉ badNodes received q :=
      fun hbad => (Finset.disjoint_left.mp (h.good g hg).2) hi hbad
    have hzero : q.atNode (seedNode IRSProfile.domain i)
        (affineSeedWord (Koala6844BenchmarkCases.conjugateWord received 0)
          (Koala6844BenchmarkCases.conjugateWord received 1) 0 i)
        (affineSeedWord (Koala6844BenchmarkCases.conjugateWord received 0)
          (Koala6844BenchmarkCases.conjugateWord received 1) 1 i) = 0 := by
      by_contra hnonzero
      exact hnotBad (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnonzero⟩)
    simpa [word, seedNode, affineSeedWord, Koala6844BenchmarkCases.conjugateWord] using hzero
  · intro g hg i hi
    simpa [word] using (Finset.mem_filter.mp hi).2
  · intro p₀ p₁ hp₀ hp₁
    refine (Finset.card_le_card (t := RCN050.pencilSeeds retained selected p₀ p₁) ?_).trans
      (h.selection.pencil p₀ p₁ hp₀ hp₁)
    intro g hg
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp hg)

def RemainingGeometrySeedBound : Prop :=
  ∀ (received : ReceivedWords) (retained : Finset IRSProfile.Field)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (q : SymbolicRow (SeedRing IRSProfile.Field)),
    RetainedComparison received retained selected q →
    (primitiveExcess 131071 q ≤ 11499 →
      ∀ keys : Fin 4 → Koala6844CoefficientSystem.SeedMonomial,
        (Koala6844RankFour.matrix q keys (primitiveExcess 131071 q)).det = 0) →
    retained.card ≤ retainedSeedBudget

theorem retained_bound_of_geometry (hGeometry : RemainingGeometrySeedBound) :
    RetainedTwoSidedSeedBound := by
  intro received retained selected q h
  by_cases hRankFour : primitiveExcess 131071 q ≤ 11499 ∧
      ∃ keys : Fin 4 → Koala6844CoefficientSystem.SeedMonomial,
        (Koala6844RankFour.matrix q keys (primitiveExcess 131071 q)).det ≠ 0
  · obtain ⟨hδ, keys, hdet⟩ := hRankFour
    exact rank_four_retained_le_seed_budget h hδ keys hdet
  · refine hGeometry received retained selected q h ?_
    intro hδ keys
    by_contra hdet
    exact hRankFour ⟨hδ, keys, hdet⟩

theorem rank_one_bound_of_geometry (hGeometry : RemainingGeometrySeedBound) : RankOneSeedBound :=
  Koala6844BenchmarkPrimitive.rank_one_seed_bound_of_two_sided
    (primitive_bound_of_retained (retained_bound_of_geometry hGeometry))

end

end ProximityPrize.SubmissionLower.Koala6844BenchmarkGeometry

