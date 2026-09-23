import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.HFreePlace6812
import ProximityPrize.SubmissionLower.HFreeNormalize6812
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# H-free bridge: the per-slice budget `HFreeSliceBudget`

Assembles the per-place bound on `L0` (HFreePlace6812) into the consumer's statement:
for a slice component `D` (prime of `E[Y,Y',Γ]` with a separable literal coordinate,
containing `F` and the slice equation `ℓ - t`, `H ∉ D`) and every finite set `W` of places,

  `3 Σ pole_ν τ ≤ Σ [(w+1)(4 T_ν + 2 zero_ν H) + 3 flagPole_ν unitAllFlag]`.

Each place `ν` restricts along `ψ : L0 → CoordinateField E D` to a trivial valuation (no
pole) or to `v^e` with `v` normalized; all quantities scale by `e`.  The centre of an affine
place has height `≤ 2` (Nullstellensatz, since `ℓ = t` is transcendental), which gives the two
local generators.  Pieces 3 and 4 (`CrudeBound`, `ResiduallySeparable`) are hypotheses.
-/

namespace ProximityPrize.SubmissionLower.HFree6812

open WithZero MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341 RCN313 RCN055 RCN095 RCN204

section Centre

variable {Ω R : Type*} [Field Ω] [IsAlgClosed Ω] [Field R] [Algebra Ω R]

/-- The centre of a valuation on `Ω[Y,Y',Γ]` whose point has a coordinate combination
transcendental over `Ω` has height at most `2`. -/
theorem centre_height_le_two (ν : Valuation R ℤᵐ⁰) (y : Fin 3 → R)
    (𝔮 : Ideal (MvPolynomial (Fin 3) Ω)) [𝔮.IsPrime]
    (h𝔮 : ∀ P, P ∈ 𝔮 ↔ ν (aeval y P) < 1)
    (c : Fin 3 → Ω) (hcω : ∀ a : Ω, a ≠ 0 → ν (algebraMap Ω R a) = 1)
    (hℓ : ∀ a : Fin 3 → Ω, ν (∑ m, algebraMap Ω R (c m) * y m - algebraMap Ω R (∑ m, c m * a m)) = 1) :
    𝔮.height ≤ 2 := by
  classical
  have hnotmax : ¬ 𝔮.IsMaximal := by
    intro hmax
    obtain ⟨a, ha⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton (I := 𝔮)).1 hmax
    have hsmall : ∀ j, ν (y j - algebraMap Ω R (a j)) < 1 := by
      intro j
      have hmem : (MvPolynomial.X j - MvPolynomial.C (a j) : MvPolynomial (Fin 3) Ω) ∈ 𝔮 := by
        rw [ha, MvPolynomial.mem_vanishingIdeal_singleton_iff]
        simp
      have := (h𝔮 _).1 hmem
      simpa using this
    have hsum : ∑ m, algebraMap Ω R (c m) * y m - algebraMap Ω R (∑ m, c m * a m) =
        ∑ m, algebraMap Ω R (c m) * (y m - algebraMap Ω R (a m)) := by
      simp only [map_sum, map_mul, mul_sub, Finset.sum_sub_distrib]
    have hlt : ν (∑ m, algebraMap Ω R (c m) * y m - algebraMap Ω R (∑ m, c m * a m)) < 1 := by
      rw [hsum]
      refine ν.map_sum_lt one_ne_zero fun m _ => ?_
      rw [ν.map_mul]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' ?_) (hsmall m)
      rcases eq_or_ne (c m) 0 with hc | hc
      · rw [hc, map_zero, ν.map_zero]; exact zero_le
      · exact (hcω _ hc).le
    exact absurd (hℓ a) (ne_of_lt hlt)
  obtain ⟨𝔪, h𝔪max, h𝔮𝔪⟩ := Ideal.exists_le_maximal 𝔮 Ideal.IsPrime.ne_top'
  have hlt : 𝔮 < 𝔪 := lt_of_le_of_ne h𝔮𝔪 (fun h => hnotmax (h ▸ h𝔪max))
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 : (𝔪.height : WithBot ℕ∞) ≤ 3 := by
    refine (Ideal.height_le_ringKrullDim_of_isPrime (I := 𝔪)).trans (le_of_eq ?_)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h3 : 𝔪.height ≤ 3 := WithBot.coe_le_coe.mp h2
  have h4 : 𝔮.height + 1 ≤ 3 := h1.trans h3
  have hne : 𝔮.height ≠ ⊤ := by
    intro htop; rw [htop] at h4; exact absurd h4 (by decide)
  lift 𝔮.height to ℕ using hne with n hn
  have : n + 1 ≤ 3 := by exact_mod_cast h4
  exact_mod_cast (show n ≤ 2 by omega)

end Centre

section ValCentre

variable {R L : Type*} [CommRing R] [Field L]

/-- The centre `{r | ν (f r) < 1}` of a valuation on an integral ring hom, as a prime ideal. -/
def valCentre (f : R →+* L) (ν : Valuation L ℤᵐ⁰) (hint : ∀ r, ν (f r) ≤ 1) : Ideal R where
  carrier := {r | ν (f r) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact (ν.map_add _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, ν.map_mul] at hx ⊢
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint c)) hx

theorem mem_valCentre (f : R →+* L) (ν : Valuation L ℤᵐ⁰) (hint : ∀ r, ν (f r) ≤ 1) (r : R) :
    r ∈ valCentre f ν hint ↔ ν (f r) < 1 := Iff.rfl

instance valCentre_isPrime (f : R →+* L) (ν : Valuation L ℤᵐ⁰) (hint : ∀ r, ν (f r) ≤ 1) :
    (valCentre f ν hint).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : (1 : R) ∈ valCentre f ν hint := htop ▸ Submodule.mem_top
    rw [mem_valCentre, map_one, ν.map_one] at h1
    exact lt_irrefl _ h1
  · intro a b hab
    rw [mem_valCentre, map_mul, ν.map_mul] at hab
    by_contra h
    rw [not_or] at h
    have ha : ν (f a) = 1 := le_antisymm (hint a) (not_lt.1 fun h' => h.1 h')
    have hb : ν (f b) = 1 := le_antisymm (hint b) (not_lt.1 fun h' => h.2 h')
    rw [ha, hb, one_mul] at hab
    exact lt_irrefl _ hab

theorem zm_pow_le_one {x : ℤᵐ⁰} {e : ℕ} (he : e ≠ 0) : x ^ e ≤ 1 ↔ x ≤ 1 := by
  constructor
  · intro h; by_contra hx; exact absurd h (not_le.2 (one_lt_pow' (not_le.1 hx) he))
  · intro h; exact pow_le_one' h e

theorem zm_pow_lt_one {x : ℤᵐ⁰} {e : ℕ} (he : e ≠ 0) : x ^ e < 1 ↔ x < 1 := by
  constructor
  · intro h; by_contra hx; exact absurd h (not_lt.2 (one_le_pow_of_one_le' (not_lt.1 hx) e))
  · intro h; exact pow_lt_one' h he

end ValCentre

section Budget

variable {K : Type} [Field K] {E : Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

local notation "w" => RCN326.w

/-- The generic slice coefficient map `K[X] → E`. -/
noncomputable abbrev phiE (K E : Type) [Field K] [Field E] [Algebra (GenericField K) E] :
    Polynomial K →+* E :=
  (algebraMap (GenericField K) E).comp (polynomialEmbedding K)

section Images

variable (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (F₀ : MvPolynomial (Fin 4) K)
  [Fact (Irreducible F₀)] (hker : RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀})

omit [IsAlgClosed E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_coord (j : Fin 3) :
    sliceEmbedding D F₀ hker (sliceCoord F₀ j) = coordinate E D j := by
  rw [sliceCoord, sliceEmbedding_proj, sliceMap, RingHom.comp_apply, surfaceMap_X_succ]
  rfl

omit [IsAlgClosed E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_const (a : K) :
    sliceEmbedding D F₀ hker (algebraMap K (SliceField F₀) a) =
      algebraMap E (CoordinateField E D) (phiE K E (Polynomial.C a)) := by
  rw [← sliceProj_C, sliceEmbedding_proj, sliceMap, RingHom.comp_apply, surfaceMap_C]
  exact (coordinateEvaluation E D).commutes _

omit [IsAlgClosed E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_X0 :
    sliceEmbedding D F₀ hker (sliceProj F₀ (MvPolynomial.X 0)) =
      algebraMap E (CoordinateField E D) (phiE K E Polynomial.X) := by
  rw [sliceEmbedding_proj, sliceMap, RingHom.comp_apply, surfaceMap_X_zero]
  exact (coordinateEvaluation E D).commutes _

omit [IsAlgClosed E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_sigma (F : MvPolynomial (Fin 4) K) :
    sliceEmbedding D F₀ hker (sliceSigma F F₀) =
      RCN064.movingRatio D (surfaceMap (phiE K E) (polyH K F))
        (surfaceMap (phiE K E) (polyG K F)) := by
  rw [sliceSigma, map_div₀, sliceEmbedding_proj, sliceEmbedding_proj]
  rfl

end Images

theorem scale_target (e : ℤ) (he : 0 ≤ e) (a b c d : ℤ) :
    max (2 * max (e * a) (max (e * b) (e * c))) (max (e * b) (e * c) + e * d) =
      e * max (2 * max a (max b c)) (max b c + d) := by
  rw [mul_max_of_nonneg _ _ he, mul_add, mul_left_comm e 2, mul_max_of_nonneg _ _ he,
    mul_max_of_nonneg _ _ he]

theorem scale_flag (e : ℤ) (he : 0 ≤ e) (a b c : ℤ) :
    max (e * a) (max (e * b) (e * c)) = e * max a (max b c) := by
  rw [mul_max_of_nonneg _ _ he, mul_max_of_nonneg _ _ he]

/-- **Per-place bound at a slice place**, in the consumer's quantities. -/
theorem nu_place_bound (F : MvPolynomial (Fin 4) K) (D : Ideal (MvPolynomial (Fin 3) E))
    [D.IsPrime] (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hker : RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀})
    (hHD : surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c : Fin 3 → GenericField K) (q : Fin 3 → Polynomial K)
    (hq : ∀ m, polynomialEmbedding K (q m) = c m)
    (hslice : MvPolynomial.C (sliceValue (GenericField K) E) -
      scalarPolynomialMap (GenericField K) E
        (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D)
    (h2 : (2 : K) ≠ 0)
    (ν : RCN026.Place E (CoordinateField E D))
    (hchar : ∀ n : ℕ, 0 < n → (n : ℤ) ≤ max (flagPole ν.val (coordinate E D) unitAllFlag)
      (RCN026.zeroOrder E (CoordinateField E D) ν
        (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) → (n : K) ≠ 0)
    (hdefer : ∀ (e : ℕ) (v : Valuation (SliceField F₀) ℤᵐ⁰), 1 ≤ e → (∃ x, v x = exp (-1)) →
      (∀ x, ν.val (sliceEmbedding D F₀ hker x) = v x ^ e) →
      (∃ C, CrudeBound v (sliceDerivation F F₀ hdvd) C) ∧
      ResiduallySeparable v (sliceDerivation F F₀ hdvd)
        (exp (vpole v (sliceDerivation F F₀ hdvd (sliceLinearL F₀ q))))) :
    3 * RCN187.poleOrder ν.val
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)^(2*w-1)) ≤
    ((w+1 : ℕ) : ℤ) *
      (4*RCN064.movingPoleTarget D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) ν +
        2*RCN026.zeroOrder E (CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) +
      3*flagPole ν.val (coordinate E D) unitAllFlag := by
  classical
  set ψ := sliceEmbedding D F₀ hker with hψdef
  set Dd := sliceDerivation F F₀ hdvd with hDd
  set wv : Valuation (SliceField F₀) ℤᵐ⁰ := ν.val.comap ψ with hwvdef
  have hwv : ∀ x, wv x = ν.val (ψ x) := fun _ => rfl
  have hHψ : ψ (sliceProj F₀ (polyH K F)) ≠ 0 := by
    rw [hψdef, sliceEmbedding_proj]
    intro h
    exact hHD ((coordEval_eq_zero_iff D _).1 h)
  have hH : sliceProj F₀ (polyH K F) ≠ 0 := fun h => hHψ (by rw [h, map_zero])
  have hτ : SecondJetComponentRoots.coefficientMap (phiE K E) D (baseNumerator F (w-1)) /
      SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)^(2*w-1) =
      ψ ((⇑Dd)^[w] (sliceCoord F₀ 1)) := by
    have h := sliceDerivation_iterate F F₀ hdvd hH (w - 1)
    have hw1 : w - 1 + 1 = w := rfl
    have hw2 : 2 * (w - 1) + 1 = 2 * w - 1 := rfl
    rw [hw1, hw2] at h
    rw [show sliceCoord F₀ 1 = sliceProj F₀ (MvPolynomial.X 2) from rfl, h, map_div₀, map_pow,
      hψdef, sliceEmbedding_proj, sliceEmbedding_proj]
    rfl
  rw [hτ]
  have hRHS0 : 0 ≤ ((w+1 : ℕ) : ℤ) *
      (4*RCN064.movingPoleTarget D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) ν +
        2*RCN026.zeroOrder E (CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) +
      3*flagPole ν.val (coordinate E D) unitAllFlag := by
    have h1 : 0 ≤ RCN064.movingPoleTarget D (surfaceMap (phiE K E) (polyH K F))
        (surfaceMap (phiE K E) (polyG K F)) ν := by
      unfold RCN064.movingPoleTarget
      exact le_max_of_le_left (mul_nonneg (by norm_num)
        (le_max_of_le_left (le_max_left _ _)))
    have h2 := RCN026.zeroOrder_nonneg E (CoordinateField E D) ν
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))
    have h3 := flagPole_nonneg ν.val (coordinate E D) unitAllFlag
    positivity
  by_cases hnt : ∃ x, wv x ≠ 0 ∧ wv x ≠ 1
  swap
  · have hpole : RCN187.poleOrder ν.val (ψ ((⇑Dd)^[w] (sliceCoord F₀ 1))) = 0 := by
      set x := (⇑Dd)^[w] (sliceCoord F₀ 1)
      have hx : wv x = 0 ∨ wv x = 1 := by
        by_contra h; rw [not_or] at h; exact hnt ⟨x, h.1, h.2⟩
      show max 0 (ν.val (ψ x)).log = 0
      rw [← hwv]
      rcases hx with h | h <;> simp [h]
    rw [hpole, mul_zero]
    exact hRHS0
  obtain ⟨e, v, he, hvn, hwve⟩ := exists_normalization wv hnt
  have he0 : e ≠ 0 := by omega
  have hν : ∀ x, ν.val (ψ x) = v x ^ e := fun x => hwve x
  have hpole : ∀ x, RCN187.poleOrder ν.val (ψ x) = e * vpole v x :=
    fun x => poleOrder_pow v wv e hwve x
  have hzeroν : ∀ x, RCN026.zeroOrder E (CoordinateField E D) ν (ψ x) = e * vzero v x :=
    fun x => zeroOrder_pow v wv e hwve x
  have hνE : ∀ a : E, a ≠ 0 → ν.val (algebraMap E (CoordinateField E D) a) = 1 :=
    fun a ha => (ν.property.2).eq_one a ha
  have hφinj : Function.Injective (phiE K E) :=
    (algebraMap (GenericField K) E).injective.comp (polynomialEmbedding_injective K)
  have hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1 := by
    intro a ha
    have h1 : ν.val (ψ (algebraMap K _ a)) = 1 := by
      rw [hψdef, psi_const]
      exact hνE _ (fun h => ha (Polynomial.C_eq_zero.mp (hφinj (h.trans (map_zero _).symm))))
    rw [hν] at h1
    exact le_antisymm ((zm_pow_le_one he0).1 h1.le)
      (not_lt.1 fun hlt => absurd h1 (ne_of_lt ((zm_pow_lt_one he0).2 hlt)))
  have hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1 := by
    have h1 : ν.val (ψ (sliceProj F₀ (MvPolynomial.X 0))) ≤ 1 := by
      rw [hψdef, psi_X0]
      haveI := ν.property.2
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one ν.val _
    rw [hν] at h1
    exact (zm_pow_le_one he0).1 h1
  obtain ⟨⟨C, hcrude⟩, hsep⟩ := hdefer e v he hvn hwve
  have hℓ := sliceLinearL_bound F F₀ hdvd v hH hK hX0 q
  -- the consumer quantities scale by `e`
  have hcoordν : ∀ j, RCN187.poleOrder ν.val (coordinate E D j) =
      e * vpole v (sliceCoord F₀ j) := by
    intro j; rw [← psi_coord D F₀ hker j, ← hψdef, hpole]
  have hPν : flagPole ν.val (coordinate E D) unitAllFlag = e * placeP F₀ v := by
    simp only [flagPole, unitAllFlag, Nat.cast_zero, zero_mul, Nat.cast_one, one_mul, zero_add]
    rw [hcoordν, hcoordν, hcoordν, placeP, scale_flag (e : ℤ) (by positivity)]
  have hhν : RCN026.zeroOrder E (CoordinateField E D) ν
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)) =
        e * placeH F F₀ v := by
    have : SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F) =
        ψ (sliceProj F₀ (polyH K F)) := by rw [hψdef, sliceEmbedding_proj]; rfl
    rw [this, hzeroν]
    rfl
  have hTν : RCN064.movingPoleTarget D (surfaceMap (phiE K E) (polyH K F))
      (surfaceMap (phiE K E) (polyG K F)) ν = e * placeT F F₀ v := by
    unfold RCN064.movingPoleTarget
    rw [hcoordν, hcoordν, hcoordν, ← psi_sigma D F₀ hker F, ← hψdef, hpole, placeT, placeP,
      scale_target (e : ℤ) (by positivity)]
  have hPv0 : 0 ≤ placeP F₀ v := le_max_of_le_left (vpole_nonneg _ _)
  have hhv0 : 0 ≤ placeH F F₀ v := vzero_nonneg _ _
  have hcharv : ∀ n : ℕ, 0 < n → (n : ℤ) ≤ max (placeP F₀ v) (placeH F F₀ v) → (n : K) ≠ 0 := by
    intro n hn hle
    refine hchar n hn ?_
    rw [hPν, hhν]
    have h1 : placeP F₀ v ≤ e * placeP F₀ v := le_mul_of_one_le_left hPv0 (by exact_mod_cast he)
    have h2 : placeH F F₀ v ≤ e * placeH F F₀ v := le_mul_of_one_le_left hhv0 (by exact_mod_cast he)
    exact hle.trans (max_le_max h1 h2)
  have hgen : placeP F₀ v = 0 → ∃ a b : MvPolynomial (Fin 4) K,
      v (sliceProj F₀ a) < 1 ∧ v (sliceProj F₀ b) < 1 ∧
      ∀ g, v (sliceProj F₀ g) < 1 → ∃ s x y : MvPolynomial (Fin 4) K,
        v (sliceProj F₀ s) = 1 ∧ s * g = x * a + y * b := by
    intro hP0
    have hint := place_hint F₀ v hK hX0 hP0
    set 𝔓 := valCentre (sliceProj F₀) v hint with h𝔓def
    set y : Fin 3 → CoordinateField E D := coordinate E D
    have hev : ∀ P : MvPolynomial (Fin 3) (GenericField K),
        aeval y P = coordinateEvaluation E D (scalarPolynomialMap (GenericField K) E P) := by
      intro P
      rw [coordinateEvaluation_eq_aeval, scalarPolynomialMap, aeval_map_algebraMap]
    have hνΩ : ∀ a : GenericField K,
        ν.val (algebraMap (GenericField K) (CoordinateField E D) a) ≤ 1 := by
      intro a
      rw [IsScalarTower.algebraMap_apply (GenericField K) E (CoordinateField E D)]
      haveI := ν.property.2
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one ν.val _
    have hyint : ∀ j, ν.val (y j) ≤ 1 := by
      intro j
      rw [show y j = ψ (sliceCoord F₀ j) from (psi_coord D F₀ hker j).symm, hν]
      exact pow_le_one' (hint _) e
    let fy : MvPolynomial (Fin 3) (GenericField K) →+* CoordinateField E D := (aeval y).toRingHom
    have hintΩ : ∀ P : MvPolynomial (Fin 3) (GenericField K), ν.val (fy P) ≤ 1 := by
      intro P
      change ν.val (aeval y P) ≤ 1
      induction P using MvPolynomial.induction_on with
      | C a => rw [aeval_C]; exact hνΩ a
      | add p r hp hr => rw [map_add]; exact (ν.val.map_add _ _).trans (max_le hp hr)
      | mul_X p j hp =>
        rw [map_mul, ν.val.map_mul, aeval_X]; exact mul_le_one' hp (hyint j)
    set 𝔮 := valCentre fy ν.val hintΩ with h𝔮def
    have hP𝔮 : originalPrime 𝔮 = 𝔓 := by
      ext g
      rw [mem_originalPrime_iff, h𝔮def, h𝔓def, mem_valCentre, mem_valCentre]
      change ν.val (aeval y _) < 1 ↔ _
      rw [hev, ← surfaceMap_generic_eq]
      change ν.val (sliceMap D g) < 1 ↔ _
      rw [← sliceEmbedding_proj D F₀ hker, ← hψdef, hν, zm_pow_lt_one he0]
    have hcω : ∀ a : GenericField K, a ≠ 0 →
        ν.val (algebraMap (GenericField K) (CoordinateField E D) a) = 1 := by
      intro a ha
      rw [IsScalarTower.algebraMap_apply (GenericField K) E (CoordinateField E D)]
      exact hνE _ ((map_ne_zero_iff _ (algebraMap (GenericField K) E).injective).2 ha)
    have hsl : ∑ m, algebraMap (GenericField K) (CoordinateField E D) (c m) * y m =
        algebraMap E (CoordinateField E D) (sliceValue (GenericField K) E) := by
      have h1 := (coordEval_eq_zero_iff D _).2 hslice
      rw [map_sub, sub_eq_zero, ← hev] at h1
      have h2 : coordinateEvaluation E D (MvPolynomial.C (sliceValue (GenericField K) E)) =
          algebraMap E (CoordinateField E D) (sliceValue (GenericField K) E) :=
        (coordinateEvaluation E D).commutes _
      rw [h2] at h1
      rw [h1]
      simp only [map_sum, map_mul, aeval_C, aeval_X]
    have hℓ' : ∀ a : Fin 3 → GenericField K,
        ν.val (∑ m, algebraMap (GenericField K) (CoordinateField E D) (c m) * y m -
          algebraMap (GenericField K) (CoordinateField E D) (∑ m, c m * a m)) = 1 := by
      intro a
      rw [hsl, IsScalarTower.algebraMap_apply (GenericField K) E (CoordinateField E D),
        ← map_sub]
      apply hνE
      intro h
      apply sliceValue_transcendental (Ω := GenericField K) (E := E)
      rw [sub_eq_zero] at h
      rw [h]
      exact isAlgebraic_algebraMap _
    have h𝔮h : 𝔮.height ≤ 2 :=
      centre_height_le_two ν.val y 𝔮 (fun P => mem_valCentre _ _ _ P) c hcω hℓ'
    have h𝔓h : 𝔓.height ≤ 2 := hP𝔮 ▸ (originalPrime_height_le 𝔮).trans h𝔮h
    haveI := RCN230.mvPolynomial_atPrime_isRegularLocalRing 𝔓
    obtain ⟨a, ha, b, hb, hgen'⟩ := exists_two_local_generators 𝔓 h𝔓h
    refine ⟨a, b, ha, hb, fun g hg => ?_⟩
    obtain ⟨s, hs, x, y, hsg⟩ := hgen' g hg
    exact ⟨s, x, y, le_antisymm (hint s) (not_lt.1 hs), hsg⟩
  have hmain := place_bound F F₀ hdvd v hH hvn hK hX0 (sliceLinearL F₀ q) hℓ C hcrude hsep h2
    hcharv hgen w
  rw [hpole, hTν, hhν, hPν]
  have hT0 : 0 ≤ placeT F F₀ v := le_max_of_le_left (by omega)
  have hvp0 := vpole_nonneg v ((⇑Dd)^[w] (sliceCoord F₀ 1))
  have he1 : (1 : ℤ) ≤ e := by exact_mod_cast he
  have hk := mul_le_mul_of_nonneg_left hmain (show (0 : ℤ) ≤ e by positivity)
  have hprod := mul_nonneg (show (0:ℤ) ≤ e by positivity)
    (show (0:ℤ) ≤ 4 * placeT F F₀ v + 2 * placeH F F₀ v by omega)
  push_cast at hk ⊢
  linarith

/-- **The H-free per-slice budget** (the `pole_le` field of `HFreeSliceBudget` with
`phi = phiE K E` and `C0 = unitAllFlag`), for a slice `C t - Σ c_m X_m` with `c_i = 1` and
`c_m = q_m(X)` in the image of `K[X]`.  Open inputs: `hchar` (pole and zero orders below the
characteristic) and `hdefer` (pieces 3 and 4 at every place of `L0` over the slice). -/
theorem hfree_slice_budget (F : MvPolynomial (Fin 4) K) (D : Ideal (MvPolynomial (Fin 3) E))
    [D.IsPrime] (sep : SeparableLiteralCoordinate D)
    (hFD : surfaceMap (phiE K E) F ∈ D) (hHD : surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c : Fin 3 → GenericField K) (i : Fin 3) (hci : c i = 1) (q : Fin 3 → Polynomial K)
    (hq : ∀ m, polynomialEmbedding K (q m) = c m)
    (hslice : MvPolynomial.C (sliceValue (GenericField K) E) -
      scalarPolynomialMap (GenericField K) E
        (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D)
    (h2 : (2 : K) ≠ 0)
    (hchar : ∀ ν : RCN026.Place E (CoordinateField E D), ∀ n : ℕ, 0 < n →
      (n : ℤ) ≤ max (flagPole ν.val (coordinate E D) unitAllFlag)
        (RCN026.zeroOrder E (CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) → (n : K) ≠ 0)
    (hdefer : ∀ (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
      (hker : RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀})
      (ν : RCN026.Place E (CoordinateField E D)) (e : ℕ) (v : Valuation (SliceField F₀) ℤᵐ⁰),
      1 ≤ e → (∃ x, v x = exp (-1)) →
      (∀ x, ν.val (sliceEmbedding D F₀ hker x) = v x ^ e) →
      (∃ C, CrudeBound v (sliceDerivation F F₀ hdvd) C) ∧
      ResiduallySeparable v (sliceDerivation F F₀ hdvd)
        (exp (vpole v (sliceDerivation F F₀ hdvd (sliceLinearL F₀ q)))))
    (W : Finset (RCN026.Place E (CoordinateField E D))) :
    3 * (∑ nu ∈ W, RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)^(2*w-1))) ≤
    ∑ nu ∈ W, (((w+1 : ℕ) : ℤ) *
      (4*RCN064.movingPoleTarget D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) nu +
        2*RCN026.zeroOrder E (CoordinateField E D) nu
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) +
      3*flagPole nu.val (coordinate E D) unitAllFlag) := by
  have hF : F ≠ 0 := by
    rintro rfl
    apply hHD
    simp [polyH]
  obtain ⟨F₀, hirr, hdvd, hker⟩ := slice_descent D sep F hF hFD c i hci hslice
  haveI : Fact (Irreducible F₀) := ⟨hirr⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun ν _ =>
    nu_place_bound F D F₀ hdvd hker hHD c q hq hslice h2 ν (hchar ν) (hdefer F₀ hdvd hker ν)

end Budget

end ProximityPrize.SubmissionLower.HFree6812
