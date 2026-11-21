import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.NormTrace
import ProximityPrize.SubmissionLower.Fast035
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_14_3_4
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
private def dx (A : ClearedSeeds) : ClearedSeeds :=
  ∑ e ∈ A.support, MvPolynomial.monomial e (AddMonoidAlgebra.coeff A e).derivative
private theorem coeff_dx (g : ClearedEquation) (j : ℕ) :
    (clearedDx g).coeff j = dx (g.coeff j) := by
  classical
  unfold clearedDx
  rw [coeff_sum, Polynomial.sum_def, Finset.sum_eq_single j]
  · simp [dx]
  · intro l _ hl
    exact coeff_monomial_of_ne _ (Ne.symm hl)
  · intro hj
    have h : g.coeff j = 0 := by simpa [Polynomial.mem_support_iff] using hj
    simp [h]
private def innerTest (g : ClearedEquation) : ClearedEquation :=
  clearedDx g + (Polynomial.X (R := ClearedSeeds)) * g.derivative
private theorem inner_coeff (g : ClearedEquation) (j : ℕ) :
    (innerTest g).coeff j = dx (g.coeff j) + g.coeff j * (j : ClearedSeeds) := by
  cases j with
  | zero => simp [innerTest, coeff_dx]
  | succ j => simp only [innerTest, coeff_add, coeff_dx, coeff_X_mul, coeff_derivative, Nat.cast_succ]
private theorem inner_degree (g : ClearedEquation) : (innerTest g).natDegree ≤ g.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp [inner_coeff, coeff_eq_zero_of_natDegree_lt hn, dx]
private theorem eval_dx (A : ClearedSeeds) (t : Fin 2 → L) :
    MvPolynomial.eval (fun i => C (t i)) (dx A) =
      (MvPolynomial.eval (fun i => C (t i)) A).derivative := by
  classical
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff A]
  simp only [dx, map_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro e _
  have hprod : (e.prod fun i n => (C (t i)) ^ n) = C (e.prod fun i n => (t i) ^ n) := by
    simp only [Finsupp.prod, map_prod, map_pow]
  rw [hprod, mul_comm _ (C _), derivative_mul, derivative_C]
  ring
private theorem specialize_nonzero (A : ClearedSeeds) (hA : A ≠ 0) :
    ∃ t : Fin 2 → L, MvPolynomial.eval (fun i => C (t i)) A ≠ 0 := by
  classical
  by_contra! h
  apply hA
  apply MvPolynomial.funext_set (fun _ => Set.range (C : L → L[X]))
    (fun _ => Set.infinite_range_of_injective Polynomial.C_injective)
  intro x hx
  choose t ht using fun i => hx i (Set.mem_univ i)
  have he : x = fun i => C (t i) := funext fun i => (ht i).symm
  rw [he, h, map_zero]
private theorem no_log_derivative {A B : L[X]} (hab : A * B ≠ 0)
    {n : ℕ} (hn : (n : L) ≠ 0) :
    A.derivative * B ≠ A * B.derivative + C (n : L) * (A * B) := by
  intro he
  have d (T : L[X]) : T.derivative.natDegree ≤ T.natDegree :=
    (natDegree_derivative_le T).trans (Nat.sub_le _ _)
  have dz (T : L[X]) : T.derivative.coeff T.natDegree = 0 := by
    rw [coeff_derivative, coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), zero_mul]
  have hh := congrArg (fun T : L[X] => T.coeff (A.natDegree + B.natDegree)) he
  rw [coeff_add, coeff_mul_add_eq_of_natDegree_le (d A) le_rfl,
    coeff_mul_add_eq_of_natDegree_le le_rfl (d B), coeff_C_mul,
    coeff_mul_degree_add_degree, dz, dz, zero_mul, mul_zero, zero_add] at hh
  exact (mul_ne_zero hn (mul_ne_zero (leadingCoeff_ne_zero.mpr (left_ne_zero_of_mul hab))
    (leadingCoeff_ne_zero.mpr (right_ne_zero_of_mul hab)))) hh.symm
private theorem no_cross {A B : ClearedSeeds} (ha : A ≠ 0) (hb : B ≠ 0)
    {n : ℕ} (hn : (n : L) ≠ 0) :
    dx A * B ≠ A * (dx B + B * (n : ClearedSeeds)) := by
  intro he
  obtain ⟨t, ht⟩ := specialize_nonzero (A * B) (mul_ne_zero ha hb)
  let ev := MvPolynomial.eval (fun i => C (t i))
  have hab : ev A * ev B ≠ 0 := by simpa only [ev, map_mul] using ht
  have hh := congrArg ev he
  simp only [ev, map_mul, map_add, map_natCast, eval_dx] at hh
  apply no_log_derivative hab hn
  rw [hh, C_eq_natCast]
  ring
private abbrev toSeed : Seeds →+* SeedField := algebraMap _ _
private abbrev liftSeed : ClearedSeeds →+* Seeds := MvPolynomial.map (algebraMap L[X] FX)
private abbrev toField : ClearedSeeds →+* SeedField := toSeed.comp liftSeed
private theorem liftSeed_inj : Function.Injective liftSeed :=
  MvPolynomial.map_injective _ (IsFractionRing.injective L[X] FX)
private theorem toField_inj : Function.Injective toField :=
  (IsFractionRing.injective Seeds SeedField).comp liftSeed_inj
private theorem at_fibre (f : Equation) (y v : SeedClosure) :
    seedFibreEval y v (C f) = aeval y (f.map toSeed) := by
  change (eval₂RingHom (eval₂RingHom seedGeneric y) v) (C f) = _
  rw [coe_eval₂RingHom, eval₂_C, coe_eval₂RingHom, aeval_def, eval₂_map]
  rfl
private theorem eqn_minimal {f : Equation} (hirr : Irreducible f) (hd : 0 < f.natDegree) :
    Irreducible (f.map toSeed) := by
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (σ := Fin 2)
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α := Seeds)
  let gcdSeeds := UniqueFactorizationMonoid.toNormalizedGCDMonoid Seeds
  let : IsGCDMonoid Seeds := nonempty_normalizedGCDMonoid_iff_isGCDMonoid.mp ⟨gcdSeeds⟩
  have hprim : f.IsPrimitive := by
    apply isPrimitive_iff_isUnit_of_C_dvd.mpr
    rintro c ⟨u, hu⟩
    rcases hirr.isUnit_or_isUnit hu with h | h
    · exact isUnit_C.mp h
    · have hc := associated_mul_unit_left (C c) u h
      rw [← hu] at hc
      have he := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hc)
      simp only [natDegree_C] at he
      omega
  exact (hprim.irreducible_iff_irreducible_map_fraction_map (K := SeedField)).mp hirr
private theorem constant_ne {f : Equation} {q : Surface} (hq : Parent q)
    (hf : Irreducible f) (hmem : C f ∈ q.asIdeal) : f.coeff 0 ≠ 0 := by
  intro hz
  have divX := (Polynomial.prime_X (R := Seeds)).irreducible.dvd_symm hf (Polynomial.X_dvd_iff.mpr hz)
  have hY : C (Polynomial.X : Equation) ∈ q.asIdeal :=
    q.asIdeal.mem_of_dvd (map_dvd (C : Equation →+* Jet) divX) hmem
  obtain ⟨t, hcomp, hker, _⟩ := hq.jet_side
  let ordVar : JetPlane := C (Polynomial.X (R := FX))
  have hYmap : fixedEmbedding ordVar = C (Polynomial.X : Equation) := by
    simp [ordVar, fixedEmbedding]
  rw [← hYmap, ← hker, RingHom.mem_ker] at hY
  have he := DFunLike.congr_fun hcomp ordVar
  have hj : jetGeneric ordVar = 0 := he.symm.trans hY
  have hjinj : Function.Injective jetGeneric :=
    (algebraMap JetField JetClosure).injective.comp (IsFractionRing.injective JetPlane JetField)
  have h0 := hjinj (hj.trans (map_zero jetGeneric).symm)
  simp [ordVar] at h0
private theorem mapped_lift (g : ClearedEquation) :
    (liftEquation g).map toSeed = g.map toField := by
  change (g.map liftSeed).map toSeed = _
  rw [Polynomial.map_map]
private theorem exclude_inner {f : Equation} {q : Surface} (hq : Parent q)
    (hi : Irreducible f) (hd : 0 < f.natDegree) (hp : f.natDegree < p)
    (hm : C f ∈ q.asIdeal) {g : ClearedEquation} {a : L[X]} (hg : IsClearing f g a)
    (ht : C (liftEquation (innerTest g)) ∈ q.asIdeal) : False := by
  obtain ⟨y, v, hpoint, hy, _⟩ := hq.seed_side
  have root (H : Equation) (hh : C H ∈ q.asIdeal) : minpoly SeedField y ∣ H.map toSeed := by
    apply minpoly.dvd
    rwa [← at_fibre _ _ v, ← RingHom.mem_ker, hpoint]
  have hdiv := ((minpoly.irreducible hy.isIntegral).dvd_symm (eqn_minimal hi hd)
    (root f hm)).trans (root _ ht)
  let a' : Seeds := MvPolynomial.C (algebraMap L[X] FX a)
  have ha' : a' ≠ 0 := MvPolynomial.C_ne_zero.mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr hg.1)
  have hscale : g.map toField = C (toSeed a') * f.map toSeed := by
    rw [← mapped_lift, hg.2, Polynomial.map_mul, Polynomial.map_C]
  have hgdeg : g.natDegree = f.natDegree := by
    have hh := congrArg Polynomial.natDegree hscale
    rwa [natDegree_map_eq_of_injective toField_inj, natDegree_C_mul
      ((map_ne_zero_iff _ (IsFractionRing.injective Seeds SeedField)).mpr ha'),
      natDegree_map_eq_of_injective (IsFractionRing.injective Seeds SeedField)] at hh
  rw [mapped_lift] at hdiv
  have hdiv' : g.map toField ∣ (innerTest g).map toField := by
    rw [hscale]
    exact ((associated_unit_mul_left _ _ (isUnit_C.mpr
      (((map_ne_zero_iff _ (IsFractionRing.injective Seeds SeedField)).mpr ha').isUnit))).dvd).trans hdiv
  obtain ⟨u, hu⟩ := hdiv'
  have hg₀ : g ≠ 0 := fun he => by rw [he, natDegree_zero] at hgdeg; omega
  have hgm : g.map toField ≠ 0 := (Polynomial.map_ne_zero_iff toField_inj).mpr hg₀
  have hdeg : u.natDegree = 0 := by
    by_cases hu₀ : u = 0
    · simp [hu₀]
    have hh := inner_degree g
    have he := congrArg Polynomial.natDegree hu
    rw [natDegree_mul hgm hu₀, natDegree_map_eq_of_injective toField_inj,
      natDegree_map_eq_of_injective toField_inj] at he
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg] at hu
  have hcoef (n : ℕ) := congrArg (fun H : SeedField[X] => H.coeff n) hu
  simp only [coeff_map, coeff_mul_C] at hcoef
  let n := g.natDegree
  have hz : g.coeff 0 ≠ 0 := by
    intro hz
    have he := congrArg (fun F : Equation => F.coeff 0) hg.2
    have hcoeff : (liftEquation g).coeff 0 = liftSeed (g.coeff 0) := coeff_map _ _
    rw [hcoeff] at he
    rw [hz, map_zero, coeff_C_mul] at he
    exact (mul_ne_zero ha' (constant_ne hq hi hm)) he.symm
  have hlead : g.coeff n ≠ 0 := leadingCoeff_ne_zero.mpr hg₀
  have charL : CharP L p := charP_of_injective_ringHom (algebraMap K L).injective p
  have hn : (n : L) ≠ 0 := by
    intro he
    exact (not_le_of_gt (show n < p by dsimp [n]; omega))
      (Nat.le_of_dvd (by dsimp [n]; omega) ((CharP.cast_eq_zero_iff L p n).mp he))
  apply no_cross hz hlead hn
  apply toField_inj
  have h0 := hcoef 0
  have hN := hcoef n
  simp only [inner_coeff, Nat.cast_zero, mul_zero, add_zero] at h0
  rw [inner_coeff] at hN
  rw [map_mul, map_mul, h0, hN]
  ring
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
private theorem cutter_reading (g : ClearedEquation) :
    ordinaryCutter g = C (liftEquation (clearedDx g)) +
      C (Polynomial.X : Equation) * C (liftEquation g.derivative) ∨
    ordinaryCutter g = graphCutter g := by
  first | exact Or.inl rfl | exact Or.inr rfl
private theorem lift_inner (g : ClearedEquation) :
    C (liftEquation (innerTest g)) = C (liftEquation (clearedDx g)) +
      C (Polynomial.X : Equation) * C (liftEquation g.derivative) := by
  have hx : liftEquation (Polynomial.X : ClearedEquation) = (Polynomial.X : Equation) :=
    Polynomial.map_X _
  simp only [innerTest, map_add, map_mul, hx]
theorem graph_test_of_compatible {P Q : Jet} {q : Surface} {f : Equation}
    (hq : Parent q) (hc : Compatible P Q q)
    (hi : Irreducible f) (hd : 0 < f.natDegree) (hp : f.natDegree < p)
    (hP : C f ∣ P) (hQ : C f ∣ Q) (hm : C f ∈ q.asIdeal)
    (g : ClearedEquation) (a : L[X]) (hg : IsClearing f g a) :
    graphCutter g ∈ q.asIdeal := by
  have ht := hc f hi hd hP hQ hm g a hg
  rcases cutter_reading g with h | h
  · rw [h, ← lift_inner] at ht
    exact (exclude_inner hq hi hd hp hm hg ht).elim
  · rwa [← h]
end
end K1_14_3_4
end
section
namespace K1_13_1
noncomputable section
open K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 120 ∧
    u.some.weight (fun i => i.val) ≤ 48 ∧
    u (some 3) ≤ 10 ∧
    u (some 1) + u (some 2) + u (some 3) ≤ 48 - (u.some.degree - 113 + 1) / 2 ∧
    u.weight (differentialWeight 133671) ≤ 90 * 180265 - 1
def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}
def anchorLocal (center received : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 90 center received).domRestrict anchorSpace
end
end K1_13_1
end
section
namespace K1_13_1
noncomputable section
section Evaluation
open K1 K1_13 PolynomialDifferential Polynomial ReedSolomon.HiddenDerivative
open scoped BigOperators
private theorem coeff_flatten {n : ℕ} (P : Row n) (m : Fin n →₀ ℕ) (i : ℕ) :
    ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).coeff (m.optionElim i) =
      (P.coeff m).coeff i := by
  rw [← MvPolynomial.optionEquivRight_coeff_coeff, AlgEquiv.apply_symm_apply]
theorem trueWeight_iff {n D : ℕ} (P : Row n) :
    TrueWeightLE P D ↔
      ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).weightedTotalDegree
        (fun v => v.elim 1 (fun i => 133671 - i.val)) ≤ D := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc : (P.coeff u.some).coeff (u none) ≠ 0 := by
      rw [← coeff_flatten, Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm : u.some ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz => hc (by simp [hz]))
    have hi := Polynomial.le_natDegree_of_ne_zero hc
    rw [← Finsupp.optionElim_some u, Finsupp.weight_optionElim, one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h _ hm
  · intro h m hm
    let d := (P.coeff m).natDegree
    have hc : (P.coeff m).coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu : m.optionElim d ∈ ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten])
    have hb := h _ hu
    rw [Finsupp.weight_optionElim, one_mul] at hb
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hb
private theorem differentialWeight_eq : differentialWeight (d := 3) 133671 =
    fun v => v.elim 1 (fun i => 133671 - i.val) := by
  funext v
  cases v <;> rfl
private theorem anchor_bounds (Q : anchorSpace) :
    InBox (shape (MvPolynomial.optionEquivRight Geom (Fin 4) Q)) ⟨120, 48, 10⟩ ∧
      TrueWeightLE (MvPolynomial.optionEquivRight Geom (Fin 4) Q) (90 * 180265 - 1) := by
  classical
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hQ := (MvPolynomial.mem_restrictSupport_iff Geom).mp Q.property
  have hm (m : Fin 4 →₀ ℕ) (h : m ∈ P.support) : ∃ i, AnchorEligible (m.optionElim i) := by
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp h)
    refine ⟨i, hQ ?_⟩
    exact MvPolynomial.mem_support_iff.mpr (by
      rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff])
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.degree_apply, Finsupp.sum] using hi.1
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hi.2.1
  · change P.degreeOf 3 ≤ 10
    rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.optionElim_apply_some] using hi.2.2.1
  · apply (trueWeight_iff P).mpr
    rw [AlgEquiv.symm_apply_apply, ← differentialWeight_eq,
      MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
    exact fun m h => (hQ h).2.2.2.2
private theorem atJet_unflatten (Q : DifferentialPolynomial Geom 3) (S : Geom[X]) :
    atJet (MvPolynomial.optionEquivRight Geom (Fin 4) Q) S =
      differentialSpecialization Q S := by
  let x : Option (Fin 4) → Geom[X] := fun
    | none => Polynomial.X
    | some i => jet S i
  have h := MvPolynomial.aeval_map_optionEquivRight (R := Geom) x Q
  have hx : x none = Polynomial.X := rfl
  have hj : (fun j => x (some j)) = jet S := rfl
  rw [hx, hj, Polynomial.aeval_X_left] at h
  rw [show (AlgHom.id Geom Geom[X]).toRingHom = RingHom.id (Geom[X]) from rfl,
    MvPolynomial.map_id] at h
  rw [MvPolynomial.aeval_eq_eval] at h
  unfold atJet differentialSpecialization
  refine h.trans (AlgHom.congr_fun ?_ Q)
  apply MvPolynomial.algHom_ext
  intro v
  rw [differentialSpecializationHom, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  cases v <;> rfl
theorem exists_anchor
    (hRank : ∀ x y : Geom, Module.finrank Geom (LinearMap.range (anchorLocal x y)) ≤ 9199626)
    (hDim : 2411626758144 < Module.finrank Geom anchorSpace) (w : I → K) :
    ∃ Q : Row 4, Q ≠ 0 ∧ InBox (shape Q) ⟨120, 48, 10⟩ ∧
      TrueWeightLE Q (90 * 180265 - 1) ∧
      ∀ Γ s, Messages w Γ s → ∀ γ ∈ Γ, atJet Q (extend (s γ)) = 0 := by
  let localRows (i : I) := anchorLocal (embed (node i)) (embed (w i))
  have hr : (∑ i, Module.finrank Geom (LinearMap.range (localRows i))) ≤
      2411626758144 := by
    calc
      _ ≤ ∑ _ : I, (9199626 : ℕ) := Finset.sum_le_sum fun i _ => hRank _ _
      _ = _ := by simp
  obtain ⟨Q, hQ, hlocal⟩ :=
    LinearMap.exists_ne_zero_of_sum_finrank_range_lt localRows (hr.trans_lt hDim)
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hP : P ≠ 0 := by
    intro h
    exact hQ (Subtype.ext ((MvPolynomial.optionEquivRight Geom (Fin 4)).injective
      (h.trans (map_zero _).symm)))
  obtain ⟨hbox, hweight⟩ := anchor_bounds Q
  refine ⟨P, hP, hbox, hweight, ?_⟩
  intro Γ s hm γ hγ
  obtain ⟨T, hT, hhit⟩ := hm.hits γ hγ
  have hdeg : differentialWeightedDegree 133671 (Q : DifferentialPolynomial Geom 3) <
      90 * 180265 := by
    have h := (trueWeight_iff P).mp hweight
    rw [AlgEquiv.symm_apply_apply] at h
    rw [differentialWeightedDegree, differentialWeight_eq]
    exact lt_of_le_of_lt h (by decide : 90 * 180265 - 1 < 90 * 180265)
  have hS : (extend (s γ)).natDegree ≤ 133671 :=
    Polynomial.natDegree_map_le.trans (hm.degree γ hγ)
  rw [atJet_unflatten]
  refine differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    (fun i => embed (node i)) (fun i => embed (w i)) T hdeg
    (fun i _ => hlocal i) _ hS
    ((RingHom.injective embed).comp node.injective).injOn hT ?_
  intro i hi
  rw [Polynomial.eval_map, Polynomial.eval₂_hom, hhit i hi]
end Evaluation
section LeadingCoefficient
open K1_13 MvPolynomial
open scoped Polynomial
def topView : Row 4 ≃ₐ[Geom[X]] Polynomial (Row 3) :=
  (renameEquiv Geom[X] finSuccEquivLast).trans (optionEquivLeft Geom[X] (Fin 3))
def anchorLead (P : Row 4) : Row 3 := (topView P).leadingCoeff
theorem topView_degree (P : Row 4) : (topView P).natDegree = (shape P).t := by
  change (optionEquivLeft _ _ (rename finSuccEquivLast P)).natDegree = P.degreeOf 3
  rw [natDegree_optionEquivLeft]
  exact degreeOf_rename_of_injective finSuccEquivLast.injective (Fin.last 3)
theorem anchorLead_ne {P : Row 4} (hP : P ≠ 0) : anchorLead P ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mpr (fun h => hP (topView.injective (h.trans (map_zero _).symm)))
theorem anchorLead_mul (P Q : Row 4) : anchorLead (P * Q) = anchorLead P * anchorLead Q := by
  rw [anchorLead, map_mul, Polynomial.leadingCoeff_mul]
  rfl
private def partialEval (S : Geom[X]) : Row 4 →+* Geom[X][X] :=
  eval₂Hom Polynomial.C fun i : Fin 4 =>
    if i = 3 then Polynomial.X else Polynomial.C (jet S i)
private theorem partialEval_eq_map (P : Row 4) (S : Geom[X]) :
    partialEval S P = (topView P).map (eval (jet S)) := by
  have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
  have h : partialEval S = (Polynomial.mapRingHom (eval (jet S))).comp topView.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp [partialEval, topView, optionEquivLeft_C]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [partialEval, topView, hlast, optionEquivLeft_X_none, show Fin.last 3 = (3 : Fin 4) by rfl]
      · have hj : j.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last j
        simp [partialEval, topView, optionEquivLeft_X_some, hj, jet]
  exact RingHom.congr_fun h P
theorem eval_anchorLead (P : Row 4) (S : Geom[X]) :
    atJet (anchorLead P) S = topLead P S := by
  change eval (jet S) (topView P).leadingCoeff =
    (partialEval S P).coeff (shape P).t
  rw [partialEval_eq_map, Polynomial.coeff_map, ← topView_degree, Polynomial.leadingCoeff]
theorem atJet_eq_anchorLead_of_top_zero (P : Row 4) (S : Geom[X]) (ht : (shape P).t = 0) :
    atJet P S = atJet (anchorLead P) S := by
  have he : atJet P S = (partialEval S P).eval (jet S (3 : Fin 4)) := by
    have h : eval (jet S) =
        (Polynomial.evalRingHom (jet S (3 : Fin 4))).comp (partialEval S) := by
      apply MvPolynomial.ringHom_ext
      · intro p
        simp [partialEval]
      · intro i
        by_cases hi : i = 3
        · subst i
          simp [partialEval]
        · simp [partialEval, hi]
    exact RingHom.congr_fun h P
  have hd : (partialEval S P).natDegree ≤ 0 := by
    rw [partialEval_eq_map]
    exact Polynomial.natDegree_map_le.trans (by rw [topView_degree, ht])
  rw [he, eval_anchorLead]
  change (partialEval S P).eval _ = (partialEval S P).coeff (shape P).t
  rw [ht, Polynomial.eq_C_of_natDegree_le_zero hd, Polynomial.eval_C, Polynomial.coeff_C_zero]
theorem indexDegree_eq {n : ℕ} (P : Row n) :
    indexDegree P = P.weightedTotalDegree (fun i => i.val) := by
  simp only [indexDegree, weightedTotalDegree, Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]
private theorem anchorLead_term (P : Row 4) (m : Fin 3 →₀ ℕ) (hm : m ∈ (anchorLead P).support) :
    ∃ u ∈ P.support, P.coeff u = (anchorLead P).coeff m ∧
      ∀ w : Fin 4 → ℕ, m.weight (fun i => w i.castSucc) ≤ u.weight w := by
  classical
  let k := (topView P).natDegree
  let c := rename finSuccEquivLast P
  have hc : c.coeff (m.optionElim k) = (anchorLead P).coeff m := by
    exact (optionEquivLeft_coeff_coeff _ _ _ _).symm
  have hs : m.optionElim k ∈ c.support :=
    mem_support_iff.mpr (by rw [hc]; exact mem_support_iff.mp hm)
  rw [show c = rename finSuccEquivLast P from rfl,
    support_rename_of_injective finSuccEquivLast.injective] at hs
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hs
  refine ⟨u, hu, ?_, fun w => ?_⟩
  · rw [← hc, ← he, coeff_rename_mapDomain _ finSuccEquivLast.injective]
  · let w' : Option (Fin 3) → ℕ := fun v => v.elim (w 3) (fun i => w i.castSucc)
    have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
    have hw : ∀ i : Fin 4, w' (finSuccEquivLast i) = w i := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [w', hlast, show Fin.last 3 = (3 : Fin 4) by rfl]
      · simp [w']
    have hweight : (m.optionElim k).weight w' = u.weight w := by
      rw [← he]
      simp only [Finsupp.weight_apply, smul_eq_mul]
      rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
      simp only [hw]
    rw [Finsupp.weight_optionElim] at hweight
    exact hweight ▸ Nat.le_add_left _ _
theorem lower_of_anchor (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨120, 48, 10⟩) (hw : TrueWeightLE P (90 * 180265 - 1)) :
    LowerRow (anchorLead P) := by
  refine ⟨anchorLead_ne hP, ?_, ?_, ?_⟩
  · rw [← weightedTotalDegree_one, weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    obtain ⟨u, hu, _, h⟩ := anchorLead_term P m hm
    have hab := (le_weightedTotalDegree (1 : Fin 4 → ℕ) hu)
    rw [weightedTotalDegree_one] at hab
    exact (h (1 : Fin 4 → ℕ)).trans (hab.trans hbox.1)
  · rw [indexDegree_eq, weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    obtain ⟨u, hu, _, h⟩ := anchorLead_term P m hm
    have hab := le_weightedTotalDegree (fun i => i.val) hu
    rw [← indexDegree_eq] at hab
    exact (h (fun i => i.val)).trans (hab.trans hbox.2.1)
  · intro m hm
    obtain ⟨u, hu, hc, h⟩ := anchorLead_term P m hm
    have hle := h (fun i => 133671 - i.val)
    rw [← hc]
    apply (Nat.add_le_add_left _ _).trans (hw u hu)
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm, Fin.val_castSucc] using hle
end LeadingCoefficient
section FactorCover
open K1 K1_13 MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
private theorem factor_small {P f : Row 4} (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨120, 48, 10⟩) (hw : TrueWeightLE P (90 * 180265 - 1))
    (hf : Irreducible f) (ht : 0 < (shape f).t) (hd : f ∣ P) : SmallFactor f := by
  refine ⟨hf, ht, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h := weightedTotalDegree_le_of_dvd (1 : Fin 4 → ℕ) hd hP
    rw [weightedTotalDegree_one, weightedTotalDegree_one] at h
    exact h.trans hbox.1
  · have h := weightedTotalDegree_le_of_dvd (fun i => i.val) hd hP
    rw [← indexDegree_eq, ← indexDegree_eq] at h
    exact h.trans hbox.2.1
  · have h := weightedTotalDegree_le_of_dvd (Pi.single (3 : Fin 4) 1) hd hP
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans hbox.2.2
  · let e := MvPolynomial.optionEquivRight Geom (Fin 4)
    have hd' : e.symm f ∣ e.symm P := map_dvd e.symm hd
    have hP' : e.symm P ≠ 0 := fun h => hP (e.symm.injective (h.trans (map_zero _).symm))
    exact (trueWeight_iff f).mpr
      ((weightedTotalDegree_le_of_dvd _ hd' hP').trans ((trueWeight_iff P).mp hw))
private theorem index_bounds (P : Row 4) :
    3 * (shape P).t ≤ (shape P).j ∧ (shape P).j ≤ 3 * (shape P).b := by
  classical
  change 3 * P.degreeOf 3 ≤ indexDegree P ∧ indexDegree P ≤ 3 * P.totalDegree
  rw [indexDegree_eq]
  constructor
  · rw [MvPolynomial.degreeOf_eq_sup]
    have h : P.support.sup (fun m => m (3 : Fin 4)) ≤
        P.weightedTotalDegree (fun i => i.val) / 3 := by
      apply Finset.sup_le
      intro m hm
      have hterm := Finsupp.apply_smul_le_weight (fun i : Fin 4 => i.val) m (3 : Fin 4)
      have hthree : (3 : Fin 4).val = 3 := rfl
      have hle := le_weightedTotalDegree (fun i : Fin 4 => i.val) hm
      have hmul : 3 * m (3 : Fin 4) ≤ P.weightedTotalDegree (fun i => i.val) :=
        (by simpa only [smul_eq_mul, Nat.mul_comm, hthree] using hterm :
          3 * m (3 : Fin 4) ≤ m.weight (fun i => i.val)).trans hle
      omega
    omega
  · rw [weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    have hle := Finsupp.weight_le_weight
      (w := fun i : Fin 4 => i.val) (w' := fun _ => 3) (fun i => Nat.le_of_lt_succ i.isLt) m
    have he : m.weight (fun _ => 3) = 3 * m.degree := by
      simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul,
        Finset.mul_sum, Nat.mul_comm]
    have hdeg : m.degree ≤ P.totalDegree := le_totalDegree hm
    exact hle.trans (he.trans_le (Nat.mul_le_mul_left 3 hdeg))
private theorem fits_of_prod {n : ℕ} (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨120, 48, 10⟩) (f : Fin n → Row 4)
    (ht : ∀ i, 0 < (shape (f i)).t) (hd : (∏ i, f i) ∣ P) :
    Fits (fun i => shape (f i)) := by
  refine ⟨fun i => ⟨ht i, index_bounds (f i)⟩, ?_, ?_, ?_⟩
  · have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 4 → ℕ) Finset.univ f hP hd
    simp only [weightedTotalDegree_one] at h
    exact h.trans hbox.1
  · have h := sum_weightedTotalDegree_le_of_prod_dvd (fun i => i.val) Finset.univ f hP hd
    simp only [← indexDegree_eq] at h
    exact h.trans hbox.2.1
  · have h := sum_weightedTotalDegree_le_of_prod_dvd (Pi.single (3 : Fin 4) 1) Finset.univ f hP hd
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans hbox.2.2
theorem cover_of_anchor {Γ : Finset K} {s : K → K[X]} (P : Row 4)
    (hP : P ≠ 0) (hbox : InBox (shape P) ⟨120, 48, 10⟩)
    (hw : TrueWeightLE P (90 * 180265 - 1))
    (hz : ∀ γ ∈ Γ, atJet P (extend (s γ)) = 0) :
    ∃ (n : ℕ) (g : Row 3) (f : Fin n → Row 4), Cover Γ s g f := by
  classical
  let _ : StrongNormalizationMonoid (Row 4) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors P
  let T := A.toFinset.filter fun q => 0 < (shape q).t
  let n := Fintype.card ↥T
  let e : Fin n ≃ ↥T := (Fintype.equivFin ↥T).symm
  let f : Fin n → Row 4 := fun i => (e i).val
  have hT : ∀ q ∈ T, q ∈ A ∧ 0 < (shape q).t := by
    intro q hq
    simpa [T] using hq
  have hfi (i : Fin n) : f i ∈ A ∧ 0 < (shape (f i)).t := hT _ (e i).property
  have hd : (∏ i, f i) ∣ P := by
    have heq : (∏ i, f i) = ∏ q ∈ T, q := by
      rw [show (∏ i, f i) = ∏ q : ↥T, q.val from e.prod_comp Subtype.val]
      exact Finset.prod_coe_sort T id
    rw [heq]
    exact ((Finset.prod_dvd_prod_of_subset T A.toFinset id (Finset.filter_subset _ _)).trans
      (Multiset.toFinset_prod_dvd_prod A)).trans (prod_normalizedFactors hP).dvd
  refine ⟨n, anchorLead P, f, ⟨lower_of_anchor P hP hbox hw, ?_, ?_,
    fits_of_prod P hP hbox f (fun i => (hfi i).2) hd, ?_⟩⟩
  · intro i
    exact factor_small hP hbox hw (irreducible_of_normalized_factor _ (hfi i).1)
      (hfi i).2 (dvd_of_mem_normalizedFactors (hfi i).1)
  · intro i j hij hassoc
    apply hij
    apply e.injective
    exact Subtype.ext (mem_normalizedFactors_eq_of_associated (hfi i).1 (hfi j).1 hassoc)
  · intro γ hγ
    let S := extend (s γ)
    by_cases hg : atJet (anchorLead P) S = 0
    · exact Or.inl hg
    right
    have hSA : eval (jet S) A.prod = 0 := by
      have hdiv := map_dvd (eval (jet S)) (prod_normalizedFactors hP).symm.dvd
      change atJet P S ∣ eval (jet S) A.prod at hdiv
      rw [hz γ hγ, zero_dvd_iff] at hdiv
      exact hdiv
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hSA
    obtain ⟨q, hq, hqS⟩ := hSA
    have hqlead : atJet (anchorLead q) S ≠ 0 := by
      intro hzero
      obtain ⟨R, hR⟩ := dvd_of_mem_normalizedFactors hq
      apply hg
      rw [hR, anchorLead_mul, atJet, map_mul]
      exact mul_eq_zero_of_left hzero _
    have hqt : 0 < (shape q).t := by
      by_contra! h
      apply hqlead
      rw [← atJet_eq_anchorLead_of_top_zero q S (Nat.eq_zero_of_le_zero h)]
      exact hqS
    have hqT : q ∈ T := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hq, hqt⟩
    let j := e.symm ⟨q, hqT⟩
    have hj : f j = q := congrArg Subtype.val (e.apply_symm_apply ⟨q, hqT⟩)
    exact ⟨j, by rw [hj, OnFactor, ← eval_anchorLead]; exact ⟨hqS, hqlead⟩⟩
end FactorCover
section Composition
open K1_13
def c1 : Prop :=
  ∀ x y : Geom, Module.finrank Geom (LinearMap.range (anchorLocal x y)) ≤ 9199626
def c2 : Prop :=
  2411626758144 < Module.finrank Geom anchorSpace
theorem of_children (h1 : c1) (h2 : c2) : K1_13.c1 := by
  intro w Γ s hm
  obtain ⟨P, hP, hb, hw, hz⟩ := exists_anchor h1 h2 w
  exact cover_of_anchor P hP hb hw (hz Γ s hm)
end Composition
end
end K1_13_1
end
section
namespace K1_13_1_1
open K1_13 K1_13_1 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
def residualDegree (s : ℕ) : ℕ :=
  min s (48 - (s - 113 + 1) / 2)
def offset (r : ℕ) : ℤ := (r : ℤ) - 48
def activeIndex (g : ℤ) : ℤ := min 48 (89 - g)
def orderCutoff (s : ℕ) (g : ℤ) : ℤ := 90 - (s : ℤ) - g
def jetIndex : Fin 4 → ℕ := Fin.val
def targetOrder : Fin 4 → ℕ := ![3,0,1,2]
def BandExponent (d : ℕ) (lo hi : ℤ) (f : ℕ) (m : Fin 4 →₀ ℕ) : Prop :=
  m.degree = d ∧ lo ≤ (m.weight jetIndex : ℤ) ∧ (m.weight jetIndex : ℤ) ≤ hi ∧ m 3 ≤ f
def intervalSize (lo hi : ℤ) : ℕ := (hi + 1 - lo).toNat
def sumRange (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec 0 (fun i a => a + f i) n
theorem sumRange_eq_sum (n : ℕ) (f : ℕ → ℕ) :
    sumRange n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl
def bandCount (d : ℕ) (lo hi : ℤ) (top : ℕ) : ℕ :=
  sumRange (min d top + 1) fun f =>
    sumRange (min (d - f) ((hi - 3 * f) / 2).toNat + 1) fun c =>
      intervalSize (max 0 (lo - 2 * c - 3 * f))
        (min ((d : ℤ) - f - c) (hi - 2 * c - 3 * f))
def targetCount (d : ℕ) (lo order : ℤ) : ℕ :=
  sumRange (d + 1) fun a =>
    sumRange (d - a + 1) fun f =>
      intervalSize (max 0 (lo - d + a - 2 * f))
        (min ((d : ℤ) - a - f) (order - 1 - 3 * a - 2 * f))
def lineBound (d : ℕ) (lo order : ℤ) (b c : ℕ) : ℕ :=
  let fmin := max 0 ((lo - b - 2 * (min c 24 : ℕ) + 2) / 3)
  let rowMin := max fmin (3 * (d : ℤ) - 3 * b - 2 * c - order + 1)
  min (intervalSize fmin (min d 10)) (intervalSize rowMin ((d : ℤ) - b - c))
def pairBound (d : ℕ) (lo : ℤ) (b : ℕ) : ℕ :=
  sumRange (min d 10 + 1) fun f =>
    intervalSize (max 0 ((lo - b - 3 * f + 1) / 2))
      (min ((d : ℤ) - f) ((48 - 3 * f) / 2))
def pascalBound (s : ℕ) (g : ℤ) : ℕ :=
  let d := residualDegree s
  let lo := -g
  let order := orderCutoff s g
  min (bandCount d lo (activeIndex g) 10)
    (sumRange (d + 1) fun b =>
      min (pairBound d lo b) (sumRange (d - b + 1) (lineBound d lo order b)))
structure FactorPowers where
  value : ℕ
  jetTwo : ℕ
  quad : ℕ
  cubic : ℕ
def FactorPowers.degree (v : FactorPowers) : ℕ := v.value + v.jetTwo + 2 * v.quad + 3 * v.cubic
def FactorPowers.minIndex (v : FactorPowers) : ℕ := 2 * v.jetTwo + v.quad + 2 * v.cubic
def FactorPowers.maxIndex (v : FactorPowers) : ℕ := 2 * v.jetTwo + 2 * v.quad + 3 * v.cubic
def FactorPowers.maxTop (v : FactorPowers) : ℕ := v.cubic
def FactorPowers.minOrder (v : FactorPowers) : ℕ := v.jetTwo + 2 * v.quad + 3 * v.cubic
def flagBound (s : ℕ) (g : ℤ) (v : FactorPowers) : ℕ :=
  let d := residualDegree s
  let count := bandCount d (-g) 48 10
  if v.degree ≤ d ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 10 then
    let d' := d - v.degree
    let lo' := -g - (v.minIndex : ℤ)
    let hi' := 48 - (v.maxIndex : ℤ)
    let order' := orderCutoff s g - (v.minOrder : ℤ)
    count - (bandCount d' lo' hi' (10 - v.maxTop) - targetCount d' lo' order')
  else count
def selectedFactors (s : ℕ) (g : ℤ) : Option FactorPowers :=
  let choices : List (ℤ × FactorPowers) := match s with
    | 55 => [(-13,⟨0,0,6,0⟩)]
    | 56 => [(-14,⟨0,0,6,0⟩)]
    | 57 => [(-15,⟨0,0,7,0⟩)]
    | 58 => [(-16,⟨0,0,8,0⟩)]
    | 59 => [(-17,⟨0,0,8,1⟩)]
    | 60 => [(-18,⟨0,0,8,1⟩),(-17,⟨0,0,6,0⟩)]
    | 61 => [(-19,⟨0,0,12,0⟩),(-18,⟨0,0,6,0⟩)]
    | 62 => [(-20,⟨0,0,12,1⟩),(-19,⟨0,0,6,0⟩)]
    | 63 => [(-21,⟨0,0,12,2⟩),(-20,⟨0,0,6,1⟩)]
    | 64 => [(-22,⟨0,0,16,0⟩),(-21,⟨0,0,8,1⟩)]
    | 65 => [(-23,⟨0,0,16,1⟩),(-22,⟨0,0,8,1⟩),(-21,⟨0,0,6,0⟩)]
    | 66 => [(-24,⟨0,0,24,0⟩),(-23,⟨0,0,8,2⟩),(-22,⟨0,0,6,0⟩)]
    | 67 => [(-24,⟨0,0,12,1⟩),(-23,⟨0,0,6,1⟩)]
    | 68 => [(-25,⟨0,0,16,1⟩),(-24,⟨0,0,6,2⟩),(-23,⟨0,0,4,0⟩)]
    | 69 => [(-26,⟨0,0,16,2⟩),(-25,⟨0,0,8,2⟩),(-24,⟨0,0,5,0⟩)]
    | 70 => [(-26,⟨0,0,8,2⟩),(-25,⟨0,0,6,0⟩)]
    | 71 => [(-27,⟨0,0,12,2⟩),(-26,⟨0,0,6,1⟩)]
    | 72 => [(-27,⟨0,0,6,2⟩),(-26,⟨0,0,4,0⟩)]
    | 73 => [(-28,⟨0,0,8,2⟩),(-27,⟨0,0,4,1⟩)]
    | 74 => [(-29,⟨0,0,8,3⟩),(-28,⟨0,0,6,1⟩)]
    | 75 => [(-29,⟨0,0,6,2⟩),(-28,⟨0,0,3,0⟩)]
    | 76 => [(-30,⟨0,0,6,3⟩),(-29,⟨0,0,4,0⟩)]
    | 77 => [(-30,⟨0,0,4,1⟩)]
    | 78 => [(-31,⟨0,0,6,2⟩),(-30,⟨0,0,3,0⟩)]
    | 79 => [(-32,⟨0,0,6,3⟩),(-31,⟨0,0,4,0⟩)]
    | 80 => [(-32,⟨0,0,4,2⟩)]
    | 81 => [(-33,⟨0,0,6,2⟩),(-32,⟨0,0,3,0⟩)]
    | 82 => [(-33,⟨0,0,3,1⟩)]
    | 83 => [(-34,⟨0,0,4,2⟩)]
    | 84 => [(-34,⟨0,0,2,0⟩)]
    | 85 => [(-35,⟨0,0,3,2⟩)]
    | 87 => [(-36,⟨0,0,2,1⟩)]
    | 89 => [(-37,⟨3,0,2,0⟩)]
    | 93 => [(-39,⟨6,1,0,0⟩)]
    | 94 => [(-39,⟨4,0,0,0⟩)]
    | 95 => [(-40,⟨8,2,0,0⟩),(-39,⟨3,0,0,0⟩)]
    | 96 => [(-40,⟨6,1,0,0⟩),(-39,⟨2,0,0,0⟩)]
    | 97 => [(-41,⟨12,2,0,0⟩),(-40,⟨6,0,0,0⟩),(-39,⟨1,0,0,0⟩)]
    | 98 => [(-41,⟨8,1,0,0⟩),(-40,⟨4,0,0,0⟩)]
    | 99 => [(-42,⟨12,3,0,0⟩),(-41,⟨8,0,0,0⟩),(-40,⟨3,0,0,0⟩)]
    | 100 => [(-42,⟨12,2,0,0⟩),(-41,⟨6,0,0,0⟩),(-40,⟨2,0,0,0⟩)]
    | 101 =>
      [(-43,⟨16,3,0,0⟩),(-42,⟨12,1,0,0⟩),(-41,⟨6,0,0,0⟩),
       (-40,⟨1,0,0,0⟩)]
    | 102 => [(-43,⟨12,2,0,0⟩),(-42,⟨8,0,0,0⟩),(-41,⟨4,0,0,0⟩)]
    | 103 =>
      [(-44,⟨16,4,0,0⟩),(-43,⟨12,1,0,0⟩),(-42,⟨8,0,0,0⟩),
       (-41,⟨3,0,0,0⟩)]
    | 104 =>
      [(-44,⟨16,3,0,0⟩),(-43,⟨12,0,0,0⟩),(-42,⟨6,0,0,0⟩),
       (-41,⟨2,0,0,0⟩)]
    | 105 =>
      [(-45,⟨16,4,0,0⟩),(-44,⟨16,2,0,0⟩),(-43,⟨12,0,0,0⟩),
       (-42,⟨6,0,0,0⟩),(-41,⟨1,0,0,0⟩)]
    | 106 =>
      [(-45,⟨16,3,0,0⟩),(-44,⟨12,1,0,0⟩),(-43,⟨8,0,0,0⟩),
       (-42,⟨4,0,0,0⟩)]
    | 107 =>
      [(-46,⟨24,6,0,0⟩),(-45,⟨16,2,0,0⟩),(-44,⟨12,0,0,0⟩),
       (-43,⟨8,0,0,0⟩),(-42,⟨3,0,0,0⟩)]
    | 108 =>
      [(-46,⟨24,4,0,0⟩),(-45,⟨16,1,0,0⟩),(-44,⟨12,0,0,0⟩),
       (-43,⟨6,0,0,0⟩),(-42,⟨2,0,0,0⟩)]
    | 109 =>
      [(-47,⟨24,6,0,0⟩),(-46,⟨17,0,0,0⟩),(-45,⟨16,0,0,0⟩),
       (-44,⟨12,0,0,0⟩),(-43,⟨6,0,0,0⟩),(-42,⟨1,0,0,0⟩)]
    | 110 =>
      [(-47,⟨24,4,0,0⟩),(-46,⟨16,2,0,0⟩),(-45,⟨12,0,0,0⟩),
       (-44,⟨8,0,0,0⟩),(-43,⟨4,0,0,0⟩)]
    | 111 =>
      [(-47,⟨24,4,0,0⟩),(-46,⟨16,1,0,0⟩),(-45,⟨12,0,0,0⟩),
       (-44,⟨8,0,0,0⟩),(-43,⟨3,0,0,0⟩)]
    | 112 =>
      [(-48,⟨26,0,0,0⟩),(-47,⟨18,0,0,0⟩),(-46,⟨16,0,0,0⟩),
       (-45,⟨12,0,0,0⟩),(-44,⟨6,0,0,0⟩),(-43,⟨2,0,0,0⟩)]
    | 113 =>
      [(-48,⟨25,0,0,0⟩),(-47,⟨17,0,0,0⟩),(-46,⟨16,0,0,0⟩),
       (-45,⟨12,0,0,0⟩),(-44,⟨6,0,0,0⟩),(-43,⟨1,0,0,0⟩)]
    | 114 =>
      [(-48,⟨24,0,0,0⟩),(-47,⟨16,0,0,0⟩),(-46,⟨12,0,0,0⟩),
       (-45,⟨8,0,0,0⟩),(-44,⟨3,0,0,0⟩)]
    | 115 =>
      [(-48,⟨22,0,0,0⟩),(-47,⟨16,0,0,0⟩),(-46,⟨12,0,0,0⟩),
       (-45,⟨6,0,0,0⟩),(-44,⟨2,0,0,0⟩)]
    | 116 =>
      [(-48,⟨16,0,0,0⟩),(-47,⟨12,0,0,0⟩),(-46,⟨8,0,0,0⟩),
       (-45,⟨4,0,0,0⟩)]
    | 117 =>
      [(-48,⟨16,0,0,0⟩),(-47,⟨12,0,0,0⟩),(-46,⟨8,0,0,0⟩),
       (-45,⟨3,0,0,0⟩)]
    | 118 =>
      [(-48,⟨16,0,0,0⟩),(-47,⟨12,0,0,0⟩),(-46,⟨6,0,0,0⟩),
       (-45,⟨1,0,0,0⟩)]
    | 119 => [(-48,⟨12,0,0,0⟩),(-47,⟨8,0,0,0⟩),(-46,⟨4,0,0,0⟩)]
    | 120 => [(-48,⟨12,0,0,0⟩),(-47,⟨6,0,0,0⟩),(-46,⟨2,0,0,0⟩)]
    | _ => []
  choices.lookup g
def blockBudget (s : ℕ) (g : ℤ) : ℕ :=
  if g < 90 - (s : ℤ) then
    match selectedFactors s g with
    | none => pascalBound s g
    | some v => min (pascalBound s g) (flagBound s g v)
  else 0
def gradeBudget (s : ℕ) : ℕ :=
  sumRange 138 fun r => blockBudget s (offset r)
def totalBudget : ℕ := sumRange 121 gradeBudget
noncomputable section
abbrev Form := MvPolynomial (Fin 4) Geom
def bandSpace (d : ℕ) (lo hi : ℤ) (f : ℕ) : Submodule Geom Form :=
  restrictSupport Geom {m | BandExponent d lo hi f m}
def valueForm : Form := MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 2 + MvPolynomial.X 3
def flagFactor (v : FactorPowers) : Form :=
  let x₀ : Form := MvPolynomial.X 0
  let x₁ : Form := MvPolynomial.X 1
  let x₂ : Form := MvPolynomial.X 2
  let x₃ : Form := MvPolynomial.X 3
  x₀ ^ v.value * x₂ ^ v.jetTwo *
    (x₀ * x₁ - x₁ ^ 2 + x₀ * x₂) ^ v.quad *
    (x₀ ^ 2 * x₃ + x₀ ^ 2 * x₂ - 2 * x₀ * x₁ * x₂ - x₀ * x₁ ^ 2 + x₁ ^ 3) ^ v.cubic
def backShift : Form →ₐ[Geom] Form :=
  bind₁ fun j => if j = 0 then valueForm else MvPolynomial.X j
def blockMap (s : ℕ) (g : ℤ) : bandSpace (residualDegree s) (-g) 48 10 →ₗ[Geom] Form :=
  ((weightedTruncation targetOrder (orderCutoff s g).toNat).comp
    backShift.toLinearMap).domRestrict _
def projectJet (j : Fin 4) (k : ℕ) : Form →ₗ[Geom] Form :=
  filterSupport fun m => m j = k
def pascalRowScale (e : Fin 4 →₀ ℕ) : Geom :=
  (-1 : Geom) ^ (e 2) / ∏ j : Fin 4, ((e j).factorial : Geom)
def pascalColScale (m : Fin 4 →₀ ℕ) : Geom :=
  (-1 : Geom) ^ (m 2) * ∏ j : Fin 4, ((m j).factorial : Geom)
def PascalEntries : Prop :=
  ∀ (m e : Fin 4 →₀ ℕ), m.degree = e.degree → m.degree ≤ 48 →
    (backShift (monomial m 1)).coeff e =
      pascalRowScale e * pascalColScale m *
        ((e 1).choose (m 1) : Geom) * ((e 2).choose (m 2) : Geom) *
          ((e 3).choose (m 3) : Geom)
end
end K1_13_1_1
end
section
namespace K1_13_1_1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
def remainingCap (f : ℕ → ℕ) : (n start cap : ℕ) → ℕ
  | 0, _, cap => cap
  | n + 1, start, cap =>
    if cap = 0 then 0 else remainingCap f n (start + 1) (cap - f start)
def sumToCap (f : ℕ → ℕ) (n start cap : ℕ) : ℕ :=
  cap - remainingCap f n start cap
def activeNatCount (d lo hi : ℕ) : ℕ :=
  sumRange (min (min d 10) (hi / 3) + 1) fun f =>
    sumRange (min (d - f) ((hi - 3 * f) / 2) + 1) fun c =>
      min (d - f - c) (hi - 2 * c - 3 * f) + 1 - (lo - (2 * c + 3 * f))
def natLine (d lo o b c : ℕ) : ℕ :=
  let fmin := (lo - (b + 2 * min c 24) + 2) / 3
  let rowMin := max fmin (3 * d + 1 - (3 * b + 2 * c + o))
  min (min d 10 + 1 - fmin) (d - b - c + 1 - rowMin)
def natPairs (d lo b : ℕ) : ℕ :=
  sumRange (min d 10 + 1) fun f =>
    min (d - f) ((48 - 3 * f) / 2) + 1 - ((lo - (b + 3 * f) + 1) / 2)
def fastPascal (s r : ℕ) : ℕ :=
  let d := residualDegree s
  let lo := 48 - r
  let o := 138 - (s + r)
  let hi := min 48 (137 - r)
  let startB := d + 1 - o
  sumToCap (fun b =>
    let startC := 2 * (d - b) + 1 - o
    sumToCap (natLine d lo o b) (d - b + 1 - startC) startC (natPairs d lo b))
    (d + 1 - startB) startB (activeNatCount d lo hi)
def fastBlock (s r : ℕ) : ℕ :=
  if s + r < 138 then
    match selectedFactors s (offset r) with
    | none => fastPascal s r
    | some v => min (fastPascal s r) (flagBound s (offset r) v)
  else 0
def fastGrade (s : ℕ) : ℕ :=
  sumRange 138 (fastBlock s)
end K1_13_1_1
end
