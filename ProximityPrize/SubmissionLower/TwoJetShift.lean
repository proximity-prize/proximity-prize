import ProximityPrize.SubmissionLower.PoleBound2Jet

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
set_option maxHeartbeats 400000

/-!
# 2-Jet Bounded-Shift Theorem (`TwoJetShift`)

Proves the **Bounded-Shift Theorem** for 2-jet pole spaces (`poleSpace2 Crt s`) and
complete 2-jet interpolation spaces (`complete2 Crt word s W`):

For any `Q ∈ complete2 Crt word s W`, any pole block `i : Fin 2`, and any `r : ℕ`:
  `cleared2Shift D s i r Q := E^{D(s, r)} * sourceHasse2 i r Q ∈ complete2 Crt word s (W + D(s, r) * h)`
where `E = D.block i` (degree `h`) and
  `D(s, r) = min (3 * r) (min (r + s.J) (s.B + s.J))`.

Key mathematical mechanism:
1. Over `Abscissa = SeedField[X]` with `E^3`-rescaled shift `ρ₃ = rescale (E^3) ∘ seriesPolynomial (seedShift i)`,
   the 2-jet shift homomorphism `rawShift2` intertwines `forward2` with `rescale (E^3) ∘ map forward2 ∘ sourceShift2`
   via exact `E^3` cancellation in all three coordinates `(Y₀, Y₁, Y₂)`.
2. Every monomial `(e₀, e₁, e₂)` of the quotient `W` (where `forward2 Q = H^(B+J) * W`) satisfies
   `e₀ + e₁ + e₂ ≤ s.B` and `e₁ + 2*e₂ ≤ s.J`. In `PowerSeries.coeff r (rawShift2 W)`, every binomial term
   `(a₀, a₁, a₂)` with `a₀ ≤ e₀, a₁ ≤ e₁, a₂ ≤ e₂, a₀ + a₁ + a₂ ≤ r` carries at least
   `3 * r - (a₀ + 2*a₁ + 3*a₂) ≥ 3 * r - D(s, r)` factors of `E`.
3. Cancelling `E^(3 * r - D(s, r))` from `E^(3 * r)` in the integral domain `Abscissa` proves
   `H^(s.B + s.J) ∣ forward2 (cleared2Shift D s i r Q)` with zero denominators.
-/

namespace TwoJetShift
noncomputable section

open Polynomial Finset
open K1 (I)
open K1_14 (L)
open K1_14_1 (SeedPoly SeedField seedWeight PoleData CRTLift poleProduct rawBlock crtPolynomial
  otherBlock seedInField nodeL)
open K1_14_1_3 (translation seedCoeff mapCoeffs mapCoeffs_coeff mapCoeffs_monomial sourceX)
open K1_14_1_3_2 (Abscissa basePolynomial seriesPolynomial seriesPolynomial_C seriesPolynomial_X
  seriesPolynomial_coeff seriesPolynomial_fixed seriesPolynomial_constantCoeff
  sourceSeedShift genericSeedShift seedShift seedShift_algebraMap seedShift_constantCoeff
  seedShift_base seedShift_other seedShift_inv_fixed rescale_C)
open PoleMoment2Jet (Shape2 jetIdx JetPolys2 TrueSource2 jetConstant2 forward2 Shaped2 PoleTest2
  sourceCoeff2)
open PoleBound2Jet (Source2 RawSource2 coeffAt2 trueEligible2 ambient2 atPhysical2 physical2
  poleSpace2 contacted2 complete2 contacted2_shaped)
open scoped BigOperators Polynomial

/-! ## 1. Bounded-Shift Exponent & 2-Jet Seed Hasse Derivative -/

def boundedShiftExp (s : Shape2) (r : ℕ) : ℕ :=
  min (3 * r) (min (r + s.J) (s.B + s.J))

theorem boundedShiftExp_le_three_mul (s : Shape2) (r : ℕ) :
    boundedShiftExp s r ≤ 3 * r := by
  unfold boundedShiftExp; omega

theorem boundedShiftExp_bound {s : Shape2} {r e₀ e₁ e₂ a₀ a₁ a₂ : ℕ}
    (hB : e₀ + e₁ + e₂ ≤ s.B) (hJ : e₁ + 2 * e₂ ≤ s.J)
    (h0 : a₀ ≤ e₀) (h1 : a₁ ≤ e₁) (h2 : a₂ ≤ e₂)
    (hr : a₀ + a₁ + a₂ ≤ r) :
    a₀ + 2 * a₁ + 3 * a₂ ≤ boundedShiftExp s r := by
  unfold boundedShiftExp; omega

def sourceHasse2 (i : Fin 2) (r : ℕ) : Source2 →ₗ[L] Source2 :=
  mapCoeffs (mapCoeffs (mapCoeffs (mapCoeffs (seedCoeff i r))))

def cleared2Shift {h : ℕ} (D : PoleData h) (s : Shape2) (i : Fin 2) (r : ℕ)
    (Q : Source2) : Source2 :=
  jetConstant2 (sourceX (D.block i ^ boundedShiftExp s r)) * sourceHasse2 i r Q

/-! ## 2. Preservation of `ambient2` and `physical2` -/

private theorem seedCoeff_totalDegree' (i : Fin 2) (r : ℕ) (P : SeedPoly) :
    (seedCoeff i r P).totalDegree ≤ P.totalDegree := by
  classical
  let g : Fin 2 → MvPolynomial (Option (Fin 2)) L :=
    fun j => MvPolynomial.X (some j) + if j = i then MvPolynomial.X none else 0
  let f : SeedPoly →ₐ[L] MvPolynomial (Option (Fin 2)) L := MvPolynomial.aeval g
  have htrans : translation i = (MvPolynomial.optionEquivLeft L (Fin 2)).toAlgHom.comp f := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = i <;> simp [translation, f, g, hj]
  have hg (j : Fin 2) : (g j).totalDegree ≤ 1 := by
    by_cases hj : j = i
    · simpa [g, hj] using (MvPolynomial.totalDegree_add
        (MvPolynomial.X (some j) : MvPolynomial (Option (Fin 2)) L)
        (MvPolynomial.X none))
    · simp [g, hj]
  have hf : (f P).totalDegree ≤ P.totalDegree := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro m hm
    change (MvPolynomial.aeval g (MvPolynomial.monomial m (P.coeff m))).totalDegree ≤ _
    rw [MvPolynomial.aeval_monomial]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) (MvPolynomial.le_totalDegree hm)
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m j) (hg j))
  change ((translation i P).coeff r).totalDegree ≤ _
  rw [htrans]
  exact (MvPolynomial.totalDegree_coeff_optionEquivLeft_le L (Fin 2) (f P) r).trans hf

theorem ambient2_cleared {h : ℕ} (D : PoleData h) {s : Shape2} {W : ℕ} {Q : Source2}
    (hQ : Q ∈ ambient2 h s W) (i : Fin 2) (r : ℕ) :
    cleared2Shift D s i r Q ∈ ambient2 h s (W + boundedShiftExp s r * h) := by
  classical
  intro e₂ e₁ e₀ a e he
  simp only [cleared2Shift, coeffAt2, sourceCoeff2, jetConstant2, RingHom.comp_apply]
  rw [coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_mul, MvPolynomial.coeff_sum]
  simp only [sourceX, coeff_map, MvPolynomial.coeff_C_mul, sourceHasse2, mapCoeffs_coeff]
  apply Finset.sum_eq_zero
  rintro ⟨b, c⟩ hbc
  by_cases hb : (D.block i ^ boundedShiftExp s r).coeff b = 0
  · simp [hb]
  have hbdeg : b ≤ boundedShiftExp s r * h := by
    have hb' := le_natDegree_of_ne_zero hb
    rw [natDegree_pow, D.degree] at hb'
    exact hb'
  have hbc' : b + c = a := by
    simpa only [Finset.HasAntidiagonal.mem_antidiagonal] using hbc
  let A := (((Q.coeff e₂).coeff e₁).coeff e₀).coeff c
  change (D.block i ^ boundedShiftExp s r).coeff b * (seedCoeff i r A).coeff e = 0
  by_contra hne
  have hseed : (seedCoeff i r A).coeff e ≠ 0 := fun hz => hne (by simp [hz])
  have ht : seedWeight e ≤ A.totalDegree :=
    (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hseed)).trans
      (seedCoeff_totalDegree' i r A)
  have hAnz : A ≠ 0 := fun hz => hseed (by simp [hz])
  have hshape : ∃ d, trueEligible2 h s W e₂ e₁ e₀ c d := by
    by_contra hall
    apply hAnz
    apply MvPolynomial.ext
    intro d
    simpa [coeffAt2, sourceCoeff2, A] using hQ e₂ e₁ e₀ c d (fun hd => hall ⟨d, hd⟩)
  obtain ⟨d, hB, hJ, hC, _, hW⟩ := hshape
  have hseedCap : A.totalDegree ≤ s.U := by
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    intro d hd
    by_contra hbad
    exact (MvPolynomial.mem_support_iff.mp hd)
      (hQ e₂ e₁ e₀ c d (fun hd' => hbad hd'.2.2.2.1))
  exact he ⟨hB, hJ, hC, ht.trans hseedCap, by omega⟩

private abbrev sx2 : Source2 := C (C (C (Polynomial.X (R := SeedPoly))))
private abbrev sy0 : Source2 := C (C (Polynomial.X (R := SeedPoly[X])))
private abbrev sy1 : Source2 := C (Polynomial.X (R := SeedPoly[X][X]))
private abbrev sy2 : Source2 := Polynomial.X
private abbrev seedC2 : SeedPoly →+* Source2 := C.comp (C.comp (C.comp C))

private theorem source2_ext {T : Type*} [Semiring T] {f g : Source2 →+* T}
    (hSeed : ∀ p, f (seedC2 p) = g (seedC2 p))
    (hX : f sx2 = g sx2) (hY0 : f sy0 = g sy0) (hY1 : f sy1 = g sy1) (hY2 : f sy2 = g sy2) :
    f = g := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · exact Polynomial.ringHom_ext hSeed hX
      · exact hY0
    · exact hY1
  · exact hY2

private def extendTranslation2 {A S : Type*} [CommSemiring A] [CommSemiring S]
    (f : A →+* S[X]) : A[X] →+* Polynomial (Polynomial S) :=
  eval₂RingHom ((mapRingHom (C : S →+* S[X])).comp f) (C (Polynomial.X : S[X]))

@[simp] private theorem extendTranslation2_C {A S : Type*} [CommSemiring A] [CommSemiring S]
    (f : A →+* S[X]) (a : A) :
    extendTranslation2 f (C a) = (f a).map (C : S →+* S[X]) := by
  simp [extendTranslation2]

@[simp] private theorem extendTranslation2_X {A S : Type*} [CommSemiring A] [CommSemiring S]
    (f : A →+* S[X]) : extendTranslation2 f Polynomial.X = C (Polynomial.X : S[X]) := by
  simp [extendTranslation2]

private theorem extendTranslation2_coeff {A S : Type*} [CommSemiring A] [CommSemiring S]
    [Module L A] [Module L S] {f : A →+* S[X]} {g : A →ₗ[L] S} {r : ℕ}
    (hg : ∀ a, (f a).coeff r = g a) (P : A[X]) :
    (extendTranslation2 f P).coeff r = mapCoeffs g P := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => rw [map_add, coeff_add, map_add, hp, hq]
  | monomial n a =>
    rw [mapCoeffs_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow,
      extendTranslation2_C, extendTranslation2_X,
      ← (C : S[X] →+* Polynomial (Polynomial S)).map_pow, coeff_mul_C, coeff_map, hg,
      C_mul_X_pow_eq_monomial]

private def translateSource2 (i : Fin 2) : Source2 →+* Source2[X] :=
  extendTranslation2 (extendTranslation2 (extendTranslation2 (extendTranslation2 (translation i).toRingHom)))

private theorem translateSource2_coeff (i : Fin 2) (r : ℕ) (P : Source2) :
    (translateSource2 i P).coeff r = sourceHasse2 i r P := by
  unfold translateSource2 sourceHasse2
  apply extendTranslation2_coeff; intro P3
  apply extendTranslation2_coeff; intro P2
  apply extendTranslation2_coeff; intro P1
  apply extendTranslation2_coeff; intro a
  rfl

private theorem translateSource2_seed (i : Fin 2) (p : SeedPoly) :
    translateSource2 i (seedC2 p) = (translation i p).map seedC2 := by
  simp only [translateSource2, seedC2, RingHom.comp_apply, extendTranslation2_C,
    Polynomial.map_map]
  rfl

private theorem translateSource2_scalar (i : Fin 2) (x : L) :
    translateSource2 i (algebraMap L Source2 x) = C (algebraMap L Source2 x) := by
  change translateSource2 i (seedC2 (MvPolynomial.C x)) = C (seedC2 (MvPolynomial.C x))
  rw [translateSource2_seed]
  have h : translation i (MvPolynomial.C x) = C (MvPolynomial.C x) := by
    simp [translation, MvPolynomial.algebraMap_eq]
  rw [h, Polynomial.map_C]

private theorem physical2_hasse (x r₀ : L) (i : Fin 2) (r : ℕ) (P : Source2) :
    atPhysical2 x r₀ (sourceHasse2 i r P) = sourceHasse2 i r (atPhysical2 x r₀ P) := by
  let f := (mapRingHom (atPhysical2 x r₀).toRingHom).comp (translateSource2 i)
  let g := (translateSource2 i).comp (atPhysical2 x r₀).toRingHom
  have hsub := PoleBound2Jet.atPhysical2_as_substitute x r₀
  have hX : atPhysical2 x r₀ sx2 = sx2 + algebraMap L Source2 x := by
    change (atPhysical2 x r₀).toRingHom (jetConstant2 Polynomial.X) = _
    rw [hsub, PoleMoment2Jet.substitute2_base]
    simp [sx2, jetConstant2, IsScalarTower.algebraMap_apply L SeedPoly Source2,
      IsScalarTower.algebraMap_apply L SeedPoly[X] Source2]
  have hSeed (p : SeedPoly) : atPhysical2 x r₀ (seedC2 p) = seedC2 p := by
    change (atPhysical2 x r₀).toRingHom (jetConstant2 (C p)) = _
    rw [hsub, PoleMoment2Jet.substitute2_base]
    simp [seedC2, jetConstant2]
  have hY0 : atPhysical2 x r₀ sy0 = algebraMap L Source2 r₀ + sx2 * sy1 - sx2 ^ 2 * sy2 + sy0 := by
    change (atPhysical2 x r₀).toRingHom (C (C Polynomial.X)) = _
    rw [hsub, PoleMoment2Jet.substitute2_y0]
    simp [sy0, sy1, sy2, sx2, jetConstant2, map_pow,
      IsScalarTower.algebraMap_apply L SeedPoly Source2,
      IsScalarTower.algebraMap_apply L SeedPoly[X] Source2]
  have hY1 : atPhysical2 x r₀ sy1 = sy1 := by
    change (atPhysical2 x r₀).toRingHom (C Polynomial.X) = _
    rw [hsub, PoleMoment2Jet.substitute2_y1]
  have hY2 : atPhysical2 x r₀ sy2 = sy2 := by
    change (atPhysical2 x r₀).toRingHom Polynomial.X = _
    rw [hsub, PoleMoment2Jet.substitute2_y2]
  have hfg : f = g := by
    apply source2_ext
    · intro p
      change (translateSource2 i (seedC2 p)).map (atPhysical2 x r₀).toRingHom =
        translateSource2 i (atPhysical2 x r₀ (seedC2 p))
      rw [hSeed, translateSource2_seed, Polynomial.map_map]
      congr 1
      apply RingHom.ext; intro q
      exact hSeed q
    · change (translateSource2 i sx2).map (atPhysical2 x r₀).toRingHom =
        translateSource2 i (atPhysical2 x r₀ sx2)
      have htx : translateSource2 i sx2 = C sx2 := by simp [translateSource2, sx2, jetConstant2]
      rw [hX, map_add, translateSource2_scalar, htx, Polynomial.map_C]
      change C (atPhysical2 x r₀ sx2) = _
      rw [hX, map_add]
    · change (translateSource2 i sy0).map (atPhysical2 x r₀).toRingHom =
        translateSource2 i (atPhysical2 x r₀ sy0)
      rw [hY0, map_add, map_sub, map_add, map_mul, map_mul, map_pow, translateSource2_scalar]
      have hts : translateSource2 i sy0 = C sy0 := by simp [translateSource2, sy0]
      have htx : translateSource2 i sx2 = C sx2 := by simp [translateSource2, sx2, jetConstant2]
      have ht1 : translateSource2 i sy1 = C sy1 := by simp [translateSource2, sy1]
      have ht2 : translateSource2 i sy2 = C sy2 := by simp [translateSource2, sy2]
      rw [hts, htx, ht1, ht2, Polynomial.map_C]
      change C (atPhysical2 x r₀ sy0) = _
      rw [hY0]
      simp [map_add, map_sub, map_mul, map_pow]
    · change (translateSource2 i sy1).map (atPhysical2 x r₀).toRingHom =
        translateSource2 i (atPhysical2 x r₀ sy1)
      have ht1 : translateSource2 i sy1 = C sy1 := by simp [translateSource2, sy1]
      rw [hY1, ht1, Polynomial.map_C]
      exact congrArg Polynomial.C hY1
    · change (translateSource2 i sy2).map (atPhysical2 x r₀).toRingHom =
        translateSource2 i (atPhysical2 x r₀ sy2)
      have ht2 : translateSource2 i sy2 = C sy2 := by simp [translateSource2, sy2]
      rw [hY2, ht2, Polynomial.map_C]
      exact congrArg Polynomial.C hY2
  have he := congrArg (fun Q : Source2[X] => Q.coeff r) (RingHom.congr_fun hfg P)
  simpa [f, g, coe_mapRingHom, Polynomial.coeff_map, translateSource2_coeff] using he

private theorem atPhysical2_const (x r₀ : L) (p : L[X]) :
    atPhysical2 x r₀ (jetConstant2 (sourceX p)) =
      jetConstant2 (sourceX (p.comp (Polynomial.X + C x))) := by
  have hsub := PoleBound2Jet.atPhysical2_as_substitute x r₀
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    change atPhysical2 x r₀ (jetConstant2 (sourceX (p + q))) = _
    rw [show sourceX (p + q) = sourceX p + sourceX q by simp [sourceX, Polynomial.map_add],
      map_add, map_add, hp, hq, Polynomial.add_comp,
      show sourceX (p.comp (Polynomial.X + C x) + q.comp (Polynomial.X + C x)) =
        sourceX (p.comp (Polynomial.X + C x)) + sourceX (q.comp (Polynomial.X + C x)) by
        simp [sourceX, Polynomial.map_add], map_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
      Polynomial.X_comp]
    simp only [sourceX, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      map_mul, map_pow]
    have hC : atPhysical2 x r₀ (jetConstant2 (C (MvPolynomial.C a))) =
        jetConstant2 (C (MvPolynomial.C a)) := by
      change (atPhysical2 x r₀).toRingHom (jetConstant2 (C (MvPolynomial.C a))) = _
      rw [hsub, PoleMoment2Jet.substitute2_base]; simp
    have hX : atPhysical2 x r₀ (jetConstant2 (Polynomial.X (R := SeedPoly))) =
        jetConstant2 (Polynomial.X (R := SeedPoly) + C (MvPolynomial.C x)) := by
      change (atPhysical2 x r₀).toRingHom (jetConstant2 Polynomial.X) = _
      rw [hsub, PoleMoment2Jet.substitute2_base]; simp
    rw [hC, hX]
    simp [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]

theorem physical2_cleared {h : ℕ} (D : PoleData h) (word : I → L) {s : Shape2} {Q : Source2}
    (hQ : Q ∈ physical2 word s) (i : Fin 2) (r : ℕ) :
    cleared2Shift D s i r Q ∈ physical2 word s := by
  intro idx a b e₁ e₂ e hab
  rw [cleared2Shift, map_mul, atPhysical2_const, physical2_hasse]
  simp only [coeffAt2, sourceCoeff2, jetConstant2, RingHom.comp_apply]
  rw [coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_mul, MvPolynomial.coeff_sum]
  simp only [sourceX, coeff_map, MvPolynomial.coeff_C_mul, sourceHasse2, mapCoeffs_coeff]
  apply Finset.sum_eq_zero
  rintro ⟨c₁, c₂⟩ hc
  have hc' : c₁ + c₂ = a := by simpa only [Finset.HasAntidiagonal.mem_antidiagonal] using hc
  have hzero : (((((atPhysical2 (nodeL idx) (word idx) Q).coeff e₂).coeff e₁).coeff b).coeff c₂) = 0 := by
    apply MvPolynomial.ext; intro d
    simpa [coeffAt2, sourceCoeff2] using hQ idx c₂ b e₁ e₂ d (by omega)
  simp [hzero]

/-! ## 3. Exact `E^3` Shift Identity & Bounded-Shift Pole Space Theorem -/

private def jetHom2 {A B : Type*} [CommSemiring A] [CommSemiring B]
    (base : A →+* B) (y0 y1 y2 : B) : Polynomial (Polynomial (Polynomial A)) →+* B :=
  eval₂RingHom (eval₂RingHom (eval₂RingHom base y0) y1) y2

@[simp] private theorem jetHom2_base {A B : Type*} [CommSemiring A] [CommSemiring B]
    (base : A →+* B) (y0 y1 y2 : B) (a : A) :
    jetHom2 base y0 y1 y2 (C (C (C a))) = base a := by simp [jetHom2]

@[simp] private theorem jetHom2_y0 {A B : Type*} [CommSemiring A] [CommSemiring B]
    (base : A →+* B) (y0 y1 y2 : B) :
    jetHom2 base y0 y1 y2 (C (C Polynomial.X)) = y0 := by simp [jetHom2]

@[simp] private theorem jetHom2_y1 {A B : Type*} [CommSemiring A] [CommSemiring B]
    (base : A →+* B) (y0 y1 y2 : B) :
    jetHom2 base y0 y1 y2 (C Polynomial.X) = y1 := by simp [jetHom2]

@[simp] private theorem jetHom2_y2 {A B : Type*} [CommSemiring A] [CommSemiring B]
    (base : A →+* B) (y0 y1 y2 : B) :
    jetHom2 base y0 y1 y2 Polynomial.X = y2 := by simp [jetHom2]

private abbrev rawY0 : RawSource2 := C (C (Polynomial.X (R := Abscissa)))
private abbrev rawY1 : RawSource2 := C (Polynomial.X (R := Abscissa[X]))
private abbrev rawY2 : RawSource2 := Polynomial.X
private abbrev rawC2 : Abscissa →+* RawSource2 := jetConstant2
private abbrev rawSeriesC2 : PowerSeries Abscissa →+* PowerSeries RawSource2 :=
  PowerSeries.map rawC2

private def scaledShift3 (i : Fin 2) (E : Abscissa) : Abscissa →+* PowerSeries Abscissa :=
  (PowerSeries.rescale (E ^ 3)).comp (seriesPolynomial (seedShift i))

private theorem scaledShift3_base (i : Fin 2) (E : Abscissa) (P : L[X]) :
    scaledShift3 i E (basePolynomial P) = PowerSeries.C (basePolynomial P) := by
  unfold scaledShift3 basePolynomial
  rw [RingHom.comp_apply, seriesPolynomial_fixed _ _ (seedShift_base i), rescale_C]

private theorem scaledShift3_base_deriv (i : Fin 2) (E : Abscissa) (P : L[X]) :
    scaledShift3 i E (basePolynomial P).derivative =
      PowerSeries.C (basePolynomial P).derivative := by
  change scaledShift3 i E ((P.map _).derivative) = PowerSeries.C ((P.map _).derivative)
  rw [derivative_map]
  exact scaledShift3_base i E P.derivative

private theorem scaledShift3_base_hasse2 (i : Fin 2) (E : Abscissa) (P : L[X]) :
    scaledShift3 i E (hasseDeriv 2 (basePolynomial P)) =
      PowerSeries.C (hasseDeriv 2 (basePolynomial P)) := by
  change scaledShift3 i E (hasseDeriv 2 (P.map _)) = PowerSeries.C (hasseDeriv 2 (P.map _))
  rw [hasseDeriv_map]
  exact scaledShift3_base i E (hasseDeriv 2 P)

private def sourceShift2 (i : Fin 2) : Source2 →+* PowerSeries Source2 :=
  seriesPolynomial (seriesPolynomial (seriesPolynomial (seriesPolynomial (sourceSeedShift i))))

private theorem sourceShift2_coeff (i : Fin 2) (r : ℕ) (Q : Source2) :
    PowerSeries.coeff r (sourceShift2 i Q) = sourceHasse2 i r Q := by
  unfold sourceShift2 sourceHasse2
  apply seriesPolynomial_coeff (R := L); intro P3
  apply seriesPolynomial_coeff (R := L); intro P2
  apply seriesPolynomial_coeff (R := L); intro P1
  apply seriesPolynomial_coeff (R := L); intro a
  exact Polynomial.coeff_coe (φ := translation i a) r

private def rawShift2 (i : Fin 2) (E : Abscissa) (B B₁ B₂ : PowerSeries Abscissa) :
    RawSource2 →+* PowerSeries RawSource2 :=
  jetHom2 (rawSeriesC2.comp (scaledShift3 i E))
    (PowerSeries.C rawY0 - rawSeriesC2 (PowerSeries.C (E ^ 2) * B))
    (PowerSeries.C rawY1 + rawSeriesC2 (PowerSeries.C (E * E.derivative) * B -
      PowerSeries.C (E ^ 2) * B₁))
    (PowerSeries.C rawY2 + rawSeriesC2
      (PowerSeries.C (E * hasseDeriv 2 E - E.derivative ^ 2) * B +
       PowerSeries.C (E * E.derivative) * B₁ -
       PowerSeries.C (E ^ 2) * B₂))

private theorem rawShift2_constants (i : Fin 2) (E : Abscissa) (B B₁ B₂ : PowerSeries Abscissa)
    (P : Abscissa) (hP : scaledShift3 i E P = PowerSeries.C P) :
    rawShift2 i E B B₁ B₂ (rawC2 P) = PowerSeries.C (rawC2 P) := by
  change rawShift2 i E B B₁ B₂ (C (C (C P))) = _
  simp [rawShift2, hP]

private theorem cancel_ordinate2 {R : Type*} [CommRing R] (G E Y0 l B : R) :
    let H := G * E
    H * (Y0 - E ^ 2 * B) + (l + G * E ^ 3 * B) = H * Y0 + l := by
  dsimp only; ring

private theorem cancel_velocity2 {R : Type*} [CommRing R] (G G' E E' Y0 Y1 l1 B B1 : R) :
    let H := G * E
    let H' := G' * E + G * E'
    H * (Y1 + (E * E' * B - E ^ 2 * B1)) + H' * (Y0 - E ^ 2 * B) +
      (l1 + G' * E ^ 3 * B + G * E ^ 3 * B1) = H * Y1 + H' * Y0 + l1 := by
  dsimp only; ring

private theorem cancel_accel2 {R : Type*} [CommRing R]
    (G G' G2 E E' E2 Y0 Y1 Y2 l2 B B1 B2 : R) :
    let H := G * E
    let H' := G' * E + G * E'
    let H2 := G2 * E + G' * E' + G * E2
    H * (Y2 + ((E * E2 - E' ^ 2) * B + E * E' * B1 - E ^ 2 * B2)) +
      H' * (Y1 + (E * E' * B - E ^ 2 * B1)) +
      H2 * (Y0 - E ^ 2 * B) +
      (l2 + G2 * E ^ 3 * B + G' * E ^ 3 * B1 + G * E ^ 3 * B2) =
    H * Y2 + H' * Y1 + H2 * Y0 + l2 := by
  dsimp only; ring

private def crtTerm2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (j : Fin 2) : Abscissa :=
  C (seedInField j (Crt.denominator j))⁻¹ * (Crt.numerator j).map (seedInField j).toRingHom

private theorem crt_add2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i : Fin 2) :
    crtPolynomial Crt = crtTerm2 Crt i + crtTerm2 Crt (otherBlock i) := by
  have he (j : Fin 2) :
      (seedInField j (Crt.denominator j))⁻¹ • (Crt.numerator j).map (seedInField j) =
        crtTerm2 Crt j := Polynomial.smul_eq_C_mul _
  simp only [crtPolynomial, Fin.sum_univ_two, he]
  fin_cases i
  · rfl
  · exact add_comm _ _

private theorem crtTerm2_factor {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i : Fin 2) :
    ∃ W, crtTerm2 Crt i = basePolynomial (D.block (otherBlock i)) * W := by
  obtain ⟨N, hN⟩ := Crt.other_dvd i
  have hf : (seedInField i).toRingHom.comp (C (R := L)) = algebraMap L SeedField := by
    apply RingHom.ext; intro a; exact (seedInField i).commutes a
  refine ⟨C (seedInField i (Crt.denominator i))⁻¹ * N.map (seedInField i).toRingHom, ?_⟩
  rw [crtTerm2, hN, Polynomial.map_mul, Polynomial.map_map, hf, basePolynomial]
  exact mul_left_comm _ _ _

private theorem crtTerm2_fixed {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i j : Fin 2)
    (hji : j ≠ i) (E : Abscissa) :
    scaledShift3 i E (crtTerm2 Crt j) = PowerSeries.C (crtTerm2 Crt j) ∧
    scaledShift3 i E (crtTerm2 Crt j).derivative = PowerSeries.C (crtTerm2 Crt j).derivative ∧
    scaledShift3 i E (hasseDeriv 2 (crtTerm2 Crt j)) =
      PowerSeries.C (hasseDeriv 2 (crtTerm2 Crt j)) := by
  have hd : seedShift i (seedInField j (Crt.denominator j))⁻¹ =
      PowerSeries.C (seedInField j (Crt.denominator j))⁻¹ :=
    seedShift_inv_fixed _ _ (seedShift_other i j hji _)
  have hm (P : Polynomial L[X]) :
      scaledShift3 i E (C (seedInField j (Crt.denominator j))⁻¹ * P.map (seedInField j).toRingHom) =
        PowerSeries.C (C (seedInField j (Crt.denominator j))⁻¹ * P.map (seedInField j).toRingHom) := by
    have hmap := seriesPolynomial_fixed (seedShift i) (seedInField j).toRingHom
      (seedShift_other i j hji) P
    simp only [scaledShift3, RingHom.comp_apply, map_mul, seriesPolynomial_C, hd,
      PowerSeries.map_C, hmap, rescale_C]
  refine ⟨hm _, ?_, ?_⟩
  · simp only [crtTerm2, derivative_mul, derivative_C, zero_mul, zero_add, derivative_map]
    exact hm _
  · have hh : hasseDeriv 2 (crtTerm2 Crt j) =
        C (seedInField j (Crt.denominator j))⁻¹ *
          (hasseDeriv 2 (Crt.numerator j)).map (seedInField j).toRingHom := by
      unfold crtTerm2
      rw [← Polynomial.smul_eq_C_mul, map_smul, Polynomial.smul_eq_C_mul, hasseDeriv_map]
    rw [hh]
    exact hm _

private theorem rawBlock_factor2 {h : ℕ} (D : PoleData h) (i : Fin 2) :
    rawBlock D = basePolynomial (D.block (otherBlock i)) * basePolynomial (D.block i) := by
  fin_cases i <;> simp [rawBlock, poleProduct, basePolynomial, otherBlock, Polynomial.map_mul,
    mul_comm]

private theorem hasseDeriv2_mul_abscissa (a b : Abscissa) :
    hasseDeriv 2 (a * b) =
      hasseDeriv 2 a * b + a.derivative * b.derivative + a * hasseDeriv 2 b := by
  rw [Polynomial.hasseDeriv_mul]
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
  simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Polynomial.hasseDeriv_zero,
    LinearMap.id_apply]
  rw [Polynomial.hasseDeriv_one', Polynomial.hasseDeriv_one']
  ring

private theorem rescale3_difference (E P : Abscissa) (F : PowerSeries Abscissa)
    (hF : PowerSeries.constantCoeff F = P) :
    ∃ B : PowerSeries Abscissa,
      PowerSeries.rescale (E ^ 3) F = PowerSeries.C P + PowerSeries.C (E ^ 3) * B ∧
      PowerSeries.constantCoeff B = 0 ∧
      ∀ n, E ^ (3 * (n - 1)) ∣ PowerSeries.coeff n B := by
  have hd : (PowerSeries.X : PowerSeries Abscissa) ∣ F - PowerSeries.C P := by
    rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, hF, sub_self]
  obtain ⟨U, hU⟩ := hd
  refine ⟨PowerSeries.X * PowerSeries.rescale (E ^ 3) U, ?_, ?_, ?_⟩
  · have he := congrArg (PowerSeries.rescale (E ^ 3)) hU
    rw [map_sub, rescale_C, map_mul, PowerSeries.rescale_X, mul_assoc] at he
    rw [← he]; ring
  · simp
  · intro n
    cases n with
    | zero => simp
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_rescale, Nat.add_sub_cancel]
      rw [← pow_mul]
      exact dvd_mul_right _ _

private theorem crt_corrections_2jet {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i : Fin 2) :
    let E := basePolynomial (D.block i)
    let G := basePolynomial (D.block (otherBlock i))
    let ρ := scaledShift3 i E
    let C₀ := PowerSeries.C (R := Abscissa)
    ∃ B B₁ B₂ : PowerSeries Abscissa,
      PowerSeries.constantCoeff B = 0 ∧
      PowerSeries.constantCoeff B₁ = 0 ∧
      PowerSeries.constantCoeff B₂ = 0 ∧
      (∀ n, E ^ (3 * (n - 1)) ∣ PowerSeries.coeff n B) ∧
      (∀ n, E ^ (3 * (n - 1)) ∣ PowerSeries.coeff n B₁) ∧
      (∀ n, E ^ (3 * (n - 1)) ∣ PowerSeries.coeff n B₂) ∧
      ρ (crtPolynomial Crt) = C₀ (crtPolynomial Crt) + C₀ G * C₀ (E ^ 3) * B ∧
      ρ (crtPolynomial Crt).derivative = C₀ (crtPolynomial Crt).derivative +
        C₀ G.derivative * C₀ (E ^ 3) * B + C₀ G * C₀ (E ^ 3) * B₁ ∧
      ρ (hasseDeriv 2 (crtPolynomial Crt)) = C₀ (hasseDeriv 2 (crtPolynomial Crt)) +
        C₀ (hasseDeriv 2 G) * C₀ (E ^ 3) * B +
        C₀ G.derivative * C₀ (E ^ 3) * B₁ +
        C₀ G * C₀ (E ^ 3) * B₂ := by
  dsimp only
  let E := basePolynomial (D.block i)
  let G := basePolynomial (D.block (otherBlock i))
  let ρ := scaledShift3 i E
  let C₀ := PowerSeries.C (R := Abscissa)
  obtain ⟨W, hW⟩ := crtTerm2_factor Crt i
  have heq : crtPolynomial Crt = G * W + crtTerm2 Crt (otherBlock i) :=
    (crt_add2 Crt i).trans (congrArg (· + crtTerm2 Crt (otherBlock i)) hW)
  have hne : otherBlock i ≠ i := by fin_cases i <;> decide
  obtain ⟨hfix0, hfix1, hfix2⟩ := crtTerm2_fixed Crt i (otherBlock i) hne E
  have hG0 : ρ G = C₀ G := scaledShift3_base i E (D.block (otherBlock i))
  have hG1 : ρ G.derivative = C₀ G.derivative := scaledShift3_base_deriv i E (D.block (otherBlock i))
  have hG2 : ρ (hasseDeriv 2 G) = C₀ (hasseDeriv 2 G) :=
    scaledShift3_base_hasse2 i E (D.block (otherBlock i))
  obtain ⟨B, hB, hB0, hBdvd⟩ := rescale3_difference E W _
    (seriesPolynomial_constantCoeff _ (seedShift_constantCoeff i) W)
  obtain ⟨B₁, hB₁, hB₁0, hB₁dvd⟩ := rescale3_difference E W.derivative _
    (seriesPolynomial_constantCoeff _ (seedShift_constantCoeff i) W.derivative)
  obtain ⟨B₂, hB₂, hB₂0, hB₂dvd⟩ := rescale3_difference E (hasseDeriv 2 W) _
    (seriesPolynomial_constantCoeff _ (seedShift_constantCoeff i) (hasseDeriv 2 W))
  change ρ W = C₀ W + C₀ (E ^ 3) * B at hB
  change ρ W.derivative = C₀ W.derivative + C₀ (E ^ 3) * B₁ at hB₁
  change ρ (hasseDeriv 2 W) = C₀ (hasseDeriv 2 W) + C₀ (E ^ 3) * B₂ at hB₂
  refine ⟨B, B₁, B₂, hB0, hB₁0, hB₂0, hBdvd, hB₁dvd, hB₂dvd, ?_, ?_, ?_⟩
  · rw [heq, map_add ρ, map_mul ρ, hG0, hB, hfix0]; simp only [C₀, map_add, map_mul]; ring
  · rw [heq, derivative_add, derivative_mul, map_add ρ, map_add ρ, map_mul ρ, map_mul ρ,
      hG0, hG1, hB, hB₁, hfix1]; simp only [C₀, map_add, map_mul]; ring
  · rw [heq, map_add (hasseDeriv 2), hasseDeriv2_mul_abscissa, map_add ρ, map_add ρ, map_add ρ,
      map_mul ρ, map_mul ρ, map_mul ρ, hG0, hG1, hG2, hB, hB₁, hB₂, hfix2]
    simp only [C₀, map_add, map_mul]; ring

private theorem forward2_abscissa_def {h : ℕ} {D : PoleData h} (Crt : CRTLift D) :
    let H := rawBlock D
    let l := crtPolynomial Crt
    (forward2 (poleProduct D) l).toRingHom =
      jetHom2 (rawC2.comp (Polynomial.mapRingHom (algebraMap SeedPoly SeedField)))
        (rawC2 H * rawY0 + rawC2 l)
        (rawC2 H * rawY1 + rawC2 H.derivative * rawY0 + rawC2 l.derivative)
        (rawC2 H * rawY2 + rawC2 H.derivative * rawY1 + rawC2 (hasseDeriv 2 H) * rawY0 +
          rawC2 (hasseDeriv 2 l)) := by
  dsimp only
  rw [PoleMoment2Jet.forward2_as_substitute]
  apply PoleMoment2Jet.jetHom2_ext
  · intro p
    rw [PoleMoment2Jet.substitute2_base]
    change _ = jetHom2 _ _ _ _ (C (C (C p)))
    rw [jetHom2_base]
  · rw [PoleMoment2Jet.substitute2_y0, jetHom2_y0]; rfl
  · rw [PoleMoment2Jet.substitute2_y1, jetHom2_y1]; rfl
  · rw [PoleMoment2Jet.substitute2_y2, jetHom2_y2]; rfl

private theorem forward2_shift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i : Fin 2)
    (B B₁ B₂ : PowerSeries Abscissa)
    (hY0 : scaledShift3 i (basePolynomial (D.block i)) (crtPolynomial Crt) =
      PowerSeries.C (crtPolynomial Crt) +
        PowerSeries.C (basePolynomial (D.block (otherBlock i))) *
        PowerSeries.C (basePolynomial (D.block i) ^ 3) * B)
    (hY1 : scaledShift3 i (basePolynomial (D.block i)) (crtPolynomial Crt).derivative =
      PowerSeries.C (crtPolynomial Crt).derivative +
        PowerSeries.C (basePolynomial (D.block (otherBlock i))).derivative *
        PowerSeries.C (basePolynomial (D.block i) ^ 3) * B +
        PowerSeries.C (basePolynomial (D.block (otherBlock i))) *
        PowerSeries.C (basePolynomial (D.block i) ^ 3) * B₁)
    (hY2 : scaledShift3 i (basePolynomial (D.block i)) (hasseDeriv 2 (crtPolynomial Crt)) =
      PowerSeries.C (hasseDeriv 2 (crtPolynomial Crt)) +
        PowerSeries.C (hasseDeriv 2 (basePolynomial (D.block (otherBlock i)))) *
        PowerSeries.C (basePolynomial (D.block i) ^ 3) * B +
        PowerSeries.C (basePolynomial (D.block (otherBlock i))).derivative *
        PowerSeries.C (basePolynomial (D.block i) ^ 3) * B₁ +
        PowerSeries.C (basePolynomial (D.block (otherBlock i))) *
        PowerSeries.C (basePolynomial (D.block i) ^ 3) * B₂) :
    let E := basePolynomial (D.block i)
    (rawShift2 i E B B₁ B₂).comp (forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom =
      (PowerSeries.rescale (rawC2 (E ^ 3))).comp
        ((PowerSeries.map (forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom).comp
          (sourceShift2 i)) := by
  let E := basePolynomial (D.block i)
  let G := basePolynomial (D.block (otherBlock i))
  let F := (forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom
  let Φ := rawShift2 i E B B₁ B₂
  let S := PowerSeries.rescale (rawC2 (E ^ 3))
  have hH : rawBlock D = G * E := rawBlock_factor2 D i
  have hH' : (rawBlock D).derivative = G.derivative * E + G * E.derivative := by
    rw [hH, derivative_mul]
  have hH2 : hasseDeriv 2 (rawBlock D) =
      hasseDeriv 2 G * E + G.derivative * E.derivative + G * hasseDeriv 2 E := by
    rw [hH, hasseDeriv2_mul_abscissa]
  have hHfix : scaledShift3 i E (rawBlock D) = PowerSeries.C (rawBlock D) :=
    scaledShift3_base i E (poleProduct D)
  have hH'fix : scaledShift3 i E (rawBlock D).derivative = PowerSeries.C (rawBlock D).derivative :=
    scaledShift3_base_deriv i E (poleProduct D)
  have hH2fix : scaledShift3 i E (hasseDeriv 2 (rawBlock D)) =
      PowerSeries.C (hasseDeriv 2 (rawBlock D)) :=
    scaledShift3_base_hasse2 i E (poleProduct D)
  have hbase (P : Abscissa) (hp : scaledShift3 i E P = PowerSeries.C P) :
      Φ (rawC2 P) = PowerSeries.C (rawC2 P) := rawShift2_constants i E B B₁ B₂ P hp
  have hFdef := forward2_abscissa_def Crt
  dsimp only at hFdef
  change Φ.comp F = S.comp ((PowerSeries.map F).comp (sourceShift2 i))
  apply source2_ext
  · intro a
    change Φ (F (seedC2 a)) = S (PowerSeries.map F (sourceShift2 i (seedC2 a)))
    have hFa : ∀ b : SeedPoly, F (seedC2 b) = rawC2 (C (algebraMap SeedPoly SeedField b)) := by
      intro b
      change (forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom (C (C (C (C b)))) = _
      rw [hFdef, jetHom2_base]; simp [rawC2]
    rw [hFa a]
    apply PowerSeries.ext; intro n
    have hL : PowerSeries.coeff n (Φ (rawC2 (C (algebraMap SeedPoly SeedField a)))) =
        rawC2 ((E ^ 3) ^ n * C (algebraMap SeedPoly SeedField (seedCoeff i n a))) := by
      have hphi : Φ (rawC2 (C (algebraMap SeedPoly SeedField a))) =
          rawSeriesC2 (scaledShift3 i E (C (algebraMap SeedPoly SeedField a))) :=
        jetHom2_base _ _ _ _ _
      rw [hphi, rawSeriesC2, PowerSeries.coeff_map, scaledShift3, RingHom.comp_apply,
        PowerSeries.coeff_rescale, seriesPolynomial_C, seedShift_algebraMap, genericSeedShift,
        PowerSeries.coeff_map, RingHom.comp_apply, PowerSeries.coeff_map]
      congr 4
      exact Polynomial.coeff_coe (φ := translation i a) n
    have hR : PowerSeries.coeff n (S (PowerSeries.map F (sourceShift2 i (seedC2 a)))) =
        (rawC2 (E ^ 3)) ^ n * F (seedC2 (seedCoeff i n a)) := by
      dsimp only [S]
      rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map, sourceShift2_coeff]
      congr 2
      apply Polynomial.ext; intro e₂; apply Polynomial.ext; intro e₁
      apply Polynomial.ext; intro e₀; apply Polynomial.ext; intro c
      cases e₂ <;> cases e₁ <;> cases e₀ <;> cases c <;>
        simp [sourceHasse2, seedC2, seedCoeff, mapCoeffs_coeff]
    rw [hL, hR, hFa, map_mul, map_pow]
  · change Φ (F sx2) = S (PowerSeries.map F (sourceShift2 i sx2))
    have hFx : F sx2 = rawC2 Polynomial.X := by
      change (forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom (C (C (C Polynomial.X))) = _
      rw [hFdef, jetHom2_base]; simp [rawC2]
    rw [hFx]
    simp only [sourceShift2, sx2, seriesPolynomial_C, seriesPolynomial_X, PowerSeries.map_C,
      hFx, S, rescale_C]
    exact hbase _ (by simp [scaledShift3])
  · change Φ (F sy0) = S (PowerSeries.map F (sourceShift2 i sy0))
    simp only [sourceShift2, sy0, seriesPolynomial_C, seriesPolynomial_X, PowerSeries.map_C, S,
      rescale_C]
    change Φ ((forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom (C (C Polynomial.X))) =
      PowerSeries.C ((forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom (C (C Polynomial.X)))
    rw [hFdef, jetHom2_y0, map_add, map_mul, hbase _ hHfix]
    have hl : Φ (rawC2 (crtPolynomial Crt)) = rawSeriesC2 (scaledShift3 i E (crtPolynomial Crt)) :=
      jetHom2_base _ _ _ _ _
    rw [hl, hY0]
    have hy0' : Φ rawY0 = PowerSeries.C rawY0 - rawSeriesC2 (PowerSeries.C (E ^ 2) * B) :=
      jetHom2_y0 _ _ _ _
    rw [hy0', hH]
    simp only [rawSeriesC2, map_add, map_mul, map_pow, PowerSeries.map_C]
    exact cancel_ordinate2 (PowerSeries.C (rawC2 G)) (PowerSeries.C (rawC2 E))
      (PowerSeries.C rawY0) (PowerSeries.C (rawC2 (crtPolynomial Crt))) (PowerSeries.map rawC2 B)
  · change Φ (F sy1) = S (PowerSeries.map F (sourceShift2 i sy1))
    simp only [sourceShift2, sy1, seriesPolynomial_C, seriesPolynomial_X, PowerSeries.map_C, S,
      rescale_C]
    change Φ ((forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom (C Polynomial.X)) =
      PowerSeries.C ((forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom (C Polynomial.X))
    rw [hFdef, jetHom2_y1, map_add, map_add, map_mul, map_mul, hbase _ hHfix, hbase _ hH'fix]
    have hl1 : Φ (rawC2 (crtPolynomial Crt).derivative) =
        rawSeriesC2 (scaledShift3 i E (crtPolynomial Crt).derivative) := jetHom2_base _ _ _ _ _
    rw [hl1, hY1]
    have hy0' : Φ rawY0 = PowerSeries.C rawY0 - rawSeriesC2 (PowerSeries.C (E ^ 2) * B) :=
      jetHom2_y0 _ _ _ _
    have hy1' : Φ rawY1 = PowerSeries.C rawY1 +
        rawSeriesC2 (PowerSeries.C (E * E.derivative) * B - PowerSeries.C (E ^ 2) * B₁) :=
      jetHom2_y1 _ _ _ _
    rw [hy0', hy1', hH', hH]
    simp only [rawSeriesC2, map_add, map_mul, map_sub, map_pow, PowerSeries.map_C]
    exact cancel_velocity2 (PowerSeries.C (rawC2 G)) (PowerSeries.C (rawC2 G.derivative))
      (PowerSeries.C (rawC2 E)) (PowerSeries.C (rawC2 E.derivative))
      (PowerSeries.C rawY0) (PowerSeries.C rawY1)
      (PowerSeries.C (rawC2 (crtPolynomial Crt).derivative))
      (PowerSeries.map rawC2 B) (PowerSeries.map rawC2 B₁)
  · change Φ (F sy2) = S (PowerSeries.map F (sourceShift2 i sy2))
    simp only [sourceShift2, sy2, seriesPolynomial_X, PowerSeries.map_C, S, rescale_C]
    change Φ ((forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom Polynomial.X) =
      PowerSeries.C ((forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom Polynomial.X)
    rw [hFdef, jetHom2_y2, map_add, map_add, map_add, map_mul, map_mul, map_mul,
      hbase _ hHfix, hbase _ hH'fix, hbase _ hH2fix]
    have hl2 : Φ (rawC2 (hasseDeriv 2 (crtPolynomial Crt))) =
        rawSeriesC2 (scaledShift3 i E (hasseDeriv 2 (crtPolynomial Crt))) := jetHom2_base _ _ _ _ _
    rw [hl2, hY2]
    have hy0' : Φ rawY0 = PowerSeries.C rawY0 - rawSeriesC2 (PowerSeries.C (E ^ 2) * B) :=
      jetHom2_y0 _ _ _ _
    have hy1' : Φ rawY1 = PowerSeries.C rawY1 +
        rawSeriesC2 (PowerSeries.C (E * E.derivative) * B - PowerSeries.C (E ^ 2) * B₁) :=
      jetHom2_y1 _ _ _ _
    have hy2' : Φ rawY2 = PowerSeries.C rawY2 +
        rawSeriesC2 (PowerSeries.C (E * hasseDeriv 2 E - E.derivative ^ 2) * B +
          PowerSeries.C (E * E.derivative) * B₁ - PowerSeries.C (E ^ 2) * B₂) :=
      jetHom2_y2 _ _ _ _
    rw [hy0', hy1', hy2', hH2, hH', hH]
    simp only [rawSeriesC2, map_add, map_mul, map_sub, map_pow, PowerSeries.map_C]
    exact cancel_accel2 (PowerSeries.C (rawC2 G)) (PowerSeries.C (rawC2 G.derivative))
      (PowerSeries.C (rawC2 (hasseDeriv 2 G)))
      (PowerSeries.C (rawC2 E)) (PowerSeries.C (rawC2 E.derivative))
      (PowerSeries.C (rawC2 (hasseDeriv 2 E)))
      (PowerSeries.C rawY0) (PowerSeries.C rawY1) (PowerSeries.C rawY2)
      (PowerSeries.C (rawC2 (hasseDeriv 2 (crtPolynomial Crt))))
      (PowerSeries.map rawC2 B) (PowerSeries.map rawC2 B₁) (PowerSeries.map rawC2 B₂)

/-! ## 4. Shape Preservation under `forward2` and `E^(3r - D)` Divisibility -/

private def RawShaped2 (s : Shape2) (W : RawSource2) : Prop :=
  ∀ e₂ e₁ e₀, (((W.coeff e₂).coeff e₁).coeff e₀) ≠ 0 →
    e₀ + e₁ + e₂ ≤ s.B ∧ e₁ + 2 * e₂ ≤ s.J ∧ e₂ ≤ s.C

private def WeightBounded2 (b j c : ℕ) (W : RawSource2) : Prop :=
  ∀ e₂ e₁ e₀, (((W.coeff e₂).coeff e₁).coeff e₀) ≠ 0 →
    e₀ + e₁ + e₂ ≤ b ∧ e₁ + 2 * e₂ ≤ j ∧ e₂ ≤ c

private theorem weightBounded2_zero (b j c : ℕ) : WeightBounded2 b j c 0 := by
  intro e₂ e₁ e₀ h; simp at h

private theorem weightBounded2_add {b j c : ℕ} {P Q : RawSource2}
    (hP : WeightBounded2 b j c P) (hQ : WeightBounded2 b j c Q) :
    WeightBounded2 b j c (P + Q) := by
  intro e₂ e₁ e₀ h
  by_contra hnot
  apply h
  simp only [coeff_add]
  have hp : (((P.coeff e₂).coeff e₁).coeff e₀) = 0 := by
    by_contra hn; exact hnot (hP e₂ e₁ e₀ hn)
  have hq : (((Q.coeff e₂).coeff e₁).coeff e₀) = 0 := by
    by_contra hn; exact hnot (hQ e₂ e₁ e₀ hn)
  simp [hp, hq]

private theorem weightBounded2_sum {ι : Type*} {b j c : ℕ} (T : Finset ι) (f : ι → RawSource2)
    (hf : ∀ x ∈ T, WeightBounded2 b j c (f x)) : WeightBounded2 b j c (∑ x ∈ T, f x) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using weightBounded2_zero b j c
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact weightBounded2_add (hf a (Finset.mem_insert_self a s))
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))

private theorem weightBounded2_mono {b₁ j₁ c₁ b₂ j₂ c₂ : ℕ} {P : RawSource2}
    (hP : WeightBounded2 b₁ j₁ c₁ P) (hb : b₁ ≤ b₂) (hj : j₁ ≤ j₂) (hc : c₁ ≤ c₂) :
    WeightBounded2 b₂ j₂ c₂ P := by
  intro e₂ e₁ e₀ h
  obtain ⟨h1, h2, h3⟩ := hP e₂ e₁ e₀ h
  exact ⟨h1.trans hb, h2.trans hj, h3.trans hc⟩

private theorem weightBounded2_mul {b₁ j₁ c₁ b₂ j₂ c₂ : ℕ} {P Q : RawSource2}
    (hP : WeightBounded2 b₁ j₁ c₁ P) (hQ : WeightBounded2 b₂ j₂ c₂ Q) :
    WeightBounded2 (b₁ + b₂) (j₁ + j₂) (c₁ + c₂) (P * Q) := by
  intro e₂ e₁ e₀ h
  by_contra hnot
  apply h
  rw [coeff_mul, finsetSum_coeff, finsetSum_coeff]
  apply Finset.sum_eq_zero; intro p₂ hp₂
  rw [coeff_mul, finsetSum_coeff]
  apply Finset.sum_eq_zero; intro p₁ hp₁
  rw [coeff_mul]
  apply Finset.sum_eq_zero; intro p₀ hp₀
  by_contra hm
  have h1 := hP p₂.1 p₁.1 p₀.1 (left_ne_zero_of_mul hm)
  have h2 := hQ p₂.2 p₁.2 p₀.2 (right_ne_zero_of_mul hm)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp₂ hp₁ hp₀
  exact hnot ⟨by omega, by omega, by omega⟩

private theorem weightBounded2_pow {b j c : ℕ} {P : RawSource2}
    (hP : WeightBounded2 b j c P) (n : ℕ) :
    WeightBounded2 (n * b) (n * j) (n * c) (P ^ n) := by
  induction n with
  | zero =>
    intro e₂ e₁ e₀ h
    simp only [pow_zero, coeff_one] at h
    split_ifs at h with h2
    · subst h2; simp only [coeff_one] at h
      split_ifs at h with h1
      · subst h1; simp only [coeff_one] at h
        split_ifs at h with h0
        · subst h0; simp
        · exact (h rfl).elim
      · simp at h
    · simp at h
  | succ n ih =>
    rw [pow_succ]
    have hmul := weightBounded2_mul ih hP
    exact weightBounded2_mono hmul (by ring_nf; omega) (by ring_nf; omega) (by ring_nf; omega)

private theorem weightBounded2_const (a : Abscissa) : WeightBounded2 0 0 0 (rawC2 a) := by
  intro e₂ e₁ e₀ h
  simp only [rawC2, jetConstant2, RingHom.comp_apply, coeff_C] at h
  split_ifs at h with h2
  · subst h2; simp only [coeff_C] at h
    split_ifs at h with h1
    · subst h1; simp only [coeff_C] at h
      split_ifs at h with h0
      · subst h0; simp
      · exact (h rfl).elim
    · simp at h
  · simp at h

private theorem weightBounded2_rawY0 : WeightBounded2 1 0 0 rawY0 := by
  intro e₂ e₁ e₀ h
  simp only [rawY0, coeff_C] at h
  split_ifs at h with h2
  · subst h2; simp only [coeff_C] at h
    split_ifs at h with h1
    · subst h1; simp only [coeff_X] at h
      split_ifs at h with h0
      · subst h0; simp
      · exact (h rfl).elim
    · simp at h
  · simp at h

private theorem weightBounded2_rawY1 : WeightBounded2 1 1 0 rawY1 := by
  intro e₂ e₁ e₀ h
  simp only [rawY1, coeff_C] at h
  split_ifs at h with h2
  · subst h2; simp only [coeff_X] at h
    split_ifs at h with h1
    · subst h1; simp only [coeff_one] at h
      split_ifs at h with h0
      · subst h0; simp
      · exact (h rfl).elim
    · simp at h
  · simp at h

private theorem weightBounded2_rawY2 : WeightBounded2 1 2 1 rawY2 := by
  intro e₂ e₁ e₀ h
  simp only [rawY2, coeff_X] at h
  split_ifs at h with h2
  · subst h2; simp only [coeff_one] at h
    split_ifs at h with h1
    · subst h1; simp only [coeff_one] at h
      split_ifs at h with h0
      · subst h0; simp
      · exact (h rfl).elim
    · simp at h
  · simp at h

private theorem forward2_rawShaped2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D)
    {s : Shape2} {Q : Source2} (hQ : Shaped2 s Q) :
    RawShaped2 s (forward2 (poleProduct D) (crtPolynomial Crt) Q) := by
  let H := rawBlock D
  let l := crtPolynomial Crt
  let f := (forward2 (poleProduct D) l).toRingHom
  have hdef := forward2_abscissa_def Crt
  dsimp only at hdef
  have hy0 : WeightBounded2 1 0 0 (f sy0) := by
    change WeightBounded2 1 0 0 ((forward2 (poleProduct D) l).toRingHom (C (C Polynomial.X)))
    rw [hdef, jetHom2_y0]
    exact weightBounded2_add
      (weightBounded2_mono (weightBounded2_mul (weightBounded2_const H) weightBounded2_rawY0)
        (by omega) (by omega) (by omega))
      (weightBounded2_mono (weightBounded2_const l) (by omega) (by omega) (by omega))
  have hy1 : WeightBounded2 1 1 0 (f sy1) := by
    change WeightBounded2 1 1 0 ((forward2 (poleProduct D) l).toRingHom (C Polynomial.X))
    rw [hdef, jetHom2_y1]
    exact weightBounded2_add
      (weightBounded2_add
        (weightBounded2_mono (weightBounded2_mul (weightBounded2_const H) weightBounded2_rawY1)
          (by omega) (by omega) (by omega))
        (weightBounded2_mono (weightBounded2_mul (weightBounded2_const H.derivative) weightBounded2_rawY0)
          (by omega) (by omega) (by omega)))
      (weightBounded2_mono (weightBounded2_const l.derivative) (by omega) (by omega) (by omega))
  have hy2 : WeightBounded2 1 2 1 (f sy2) := by
    change WeightBounded2 1 2 1 ((forward2 (poleProduct D) l).toRingHom Polynomial.X)
    rw [hdef, jetHom2_y2]
    exact weightBounded2_add
      (weightBounded2_add
        (weightBounded2_add
          (weightBounded2_mono (weightBounded2_mul (weightBounded2_const H) weightBounded2_rawY2)
            (by omega) (by omega) (by omega))
          (weightBounded2_mono (weightBounded2_mul (weightBounded2_const H.derivative) weightBounded2_rawY1)
            (by omega) (by omega) (by omega)))
        (weightBounded2_mono (weightBounded2_mul (weightBounded2_const (hasseDeriv 2 H)) weightBounded2_rawY0)
          (by omega) (by omega) (by omega)))
      (weightBounded2_mono (weightBounded2_const (hasseDeriv 2 l)) (by omega) (by omega) (by omega))
  change WeightBounded2 s.B s.J s.C (f Q)
  rw [Q.as_sum_support_C_mul_X_pow, map_sum]
  apply weightBounded2_sum; intro e₂ he₂
  rw [map_mul, map_pow, (Q.coeff e₂).as_sum_support_C_mul_X_pow]
  simp only [map_sum, Finset.sum_mul]
  apply weightBounded2_sum; intro e₁ he₁
  rw [map_mul, map_pow, ((Q.coeff e₂).coeff e₁).as_sum_support_C_mul_X_pow]
  simp only [map_sum, Finset.sum_mul]
  apply weightBounded2_sum; intro e₀ he₀
  have hne : ((Q.coeff e₂).coeff e₁).coeff e₀ ≠ 0 := Polynomial.mem_support_iff.mp he₀
  have hslot : e₀ + e₁ + e₂ ≤ s.B ∧ e₁ + 2 * e₂ ≤ s.J ∧ e₂ ≤ s.C := by
    by_contra hbad
    apply hne
    apply Polynomial.ext; intro a
    apply MvPolynomial.ext; intro e
    simp only [Polynomial.coeff_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_contra hz
    obtain ⟨h1, h2, h3, _⟩ := hQ e₂ e₁ e₀ a e hz
    exact hbad ⟨h1, h2, h3⟩
  have hbase : WeightBounded2 0 0 0 (f (C (C (C (((Q.coeff e₂).coeff e₁).coeff e₀))))) := by
    change WeightBounded2 0 0 0 ((forward2 (poleProduct D) l).toRingHom (C (C (C _))))
    rw [hdef, jetHom2_base]; exact weightBounded2_const _
  simp only [map_mul, map_pow]
  have hp0 := weightBounded2_pow hy0 e₀
  have hp1 := weightBounded2_pow hy1 e₁
  have hp2 := weightBounded2_pow hy2 e₂
  have hm1 := weightBounded2_mul hbase hp0
  have hm2 := weightBounded2_mul hm1 hp1
  have hm3 := weightBounded2_mul hm2 hp2
  exact weightBounded2_mono hm3 (by omega) (by omega) (by omega)

private theorem rawShaped2_of_mul_const {s : Shape2} {c : Abscissa} (hc : c ≠ 0)
    {W : RawSource2} (hCW : RawShaped2 s (rawC2 c * W)) : RawShaped2 s W := by
  intro e₂ e₁ e₀ hne
  apply hCW e₂ e₁ e₀
  simp only [rawC2, jetConstant2, RingHom.comp_apply, coeff_C_mul]
  exact mul_ne_zero hc hne

/-- `E`-divisibility tracking for `PowerSeries RawSource2`:
    a series `F` has `SeriesEDvd E k F` if for every `n`, `rawC2 (E ^ (3 * n - k)) ∣ coeff n F`
    (with truncated subtraction on `ℕ`, so for `3 * n ≤ k` the condition is trivial!). -/
private def SeriesEDvd (E : Abscissa) (k : ℕ) (F : PowerSeries RawSource2) : Prop :=
  ∀ n, rawC2 (E ^ (3 * n - k)) ∣ PowerSeries.coeff n F

private theorem seriesEDvd_mono {E : Abscissa} {k₁ k₂ : ℕ} {F : PowerSeries RawSource2}
    (hF : SeriesEDvd E k₁ F) (hk : k₁ ≤ k₂) : SeriesEDvd E k₂ F := by
  intro n
  have hle : 3 * n - k₂ ≤ 3 * n - k₁ := by omega
  exact (map_dvd rawC2 (pow_dvd_pow E hle)).trans (hF n)

private theorem seriesEDvd_add {E : Abscissa} {k : ℕ} {F G : PowerSeries RawSource2}
    (hF : SeriesEDvd E k F) (hG : SeriesEDvd E k G) : SeriesEDvd E k (F + G) := by
  intro n
  rw [map_add]
  exact dvd_add (hF n) (hG n)

private theorem seriesEDvd_sum {ι : Type*} {E : Abscissa} {k : ℕ} (T : Finset ι)
    (f : ι → PowerSeries RawSource2) (hf : ∀ x ∈ T, SeriesEDvd E k (f x)) :
    SeriesEDvd E k (∑ x ∈ T, f x) := by
  intro n
  rw [map_sum]
  exact Finset.dvd_sum fun x hx => hf x hx n

private theorem seriesEDvd_mul {E : Abscissa} {k₁ k₂ : ℕ} {F G : PowerSeries RawSource2}
    (hF : SeriesEDvd E k₁ F) (hG : SeriesEDvd E k₂ G) : SeriesEDvd E (k₁ + k₂) (F * G) := by
  intro n
  rw [PowerSeries.coeff_mul]
  apply Finset.dvd_sum
  rintro ⟨a, b⟩ hab
  have hab' : a + b = n := Finset.mem_antidiagonal.mp hab
  have hd : rawC2 (E ^ ((3 * a - k₁) + (3 * b - k₂))) ∣
      PowerSeries.coeff a F * PowerSeries.coeff b G := by
    rw [pow_add, map_mul]
    exact mul_dvd_mul (hF a) (hG b)
  have hle : 3 * n - (k₁ + k₂) ≤ (3 * a - k₁) + (3 * b - k₂) := by omega
  exact (map_dvd rawC2 (pow_dvd_pow E hle)).trans hd

private theorem seriesEDvd_pow {E : Abscissa} {k : ℕ} {F : PowerSeries RawSource2}
    (hF : SeriesEDvd E k F) (m : ℕ) : SeriesEDvd E (m * k) (F ^ m) := by
  induction m with
  | zero =>
    intro n
    cases n with
    | zero => simp
    | succ n => simp [PowerSeries.coeff_one]
  | succ m ih =>
    rw [pow_succ]
    have hmul := seriesEDvd_mul ih hF
    simpa [Nat.succ_mul] using hmul

private theorem seriesEDvd_const (E : Abscissa) (x : RawSource2) :
    SeriesEDvd E 0 (PowerSeries.C x) := by
  intro n
  cases n with
  | zero => simp
  | succ n => simp

private theorem seriesEDvd_scaledShift3 (i : Fin 2) (E : Abscissa) (a : Abscissa) :
    SeriesEDvd E 0 (rawSeriesC2 (scaledShift3 i E a)) := by
  intro n
  rw [Nat.sub_zero, PowerSeries.coeff_map]
  simp only [scaledShift3, RingHom.comp_apply, PowerSeries.coeff_rescale, ← pow_mul, map_mul]
  exact dvd_mul_right _ _

private theorem seriesEDvd_correction (E : Abscissa) (k : ℕ) (p : Abscissa)
    (F : PowerSeries Abscissa) (_hk : 3 ≤ k → False)
    (hF0 : PowerSeries.constantCoeff F = 0)
    (hFdvd : ∀ n, E ^ (3 * (n - 1)) ∣ PowerSeries.coeff n F)
    (hpdvd : E ^ (3 - k) ∣ p) :
    SeriesEDvd E k (rawSeriesC2 (PowerSeries.C p * F)) := by
  intro n
  cases n with
  | zero =>
    simp [rawSeriesC2, hF0]
  | succ m =>
    dsimp only [rawSeriesC2]
    rw [PowerSeries.coeff_map, PowerSeries.coeff_C_mul]
    have h1 := hFdvd (m + 1)
    rw [Nat.add_sub_cancel] at h1
    have hprod : E ^ ((3 - k) + 3 * m) ∣ p * PowerSeries.coeff (m + 1) F := by
      rw [pow_add]
      exact mul_dvd_mul hpdvd h1
    have hle : 3 * (m + 1) - k ≤ (3 - k) + 3 * m := by omega
    exact _root_.map_dvd rawC2 ((pow_dvd_pow E hle).trans hprod)

private theorem seriesEDvd_correction3 (E : Abscissa) (p : Abscissa)
    (F : PowerSeries Abscissa)
    (hF0 : PowerSeries.constantCoeff F = 0)
    (hFdvd : ∀ n, E ^ (3 * (n - 1)) ∣ PowerSeries.coeff n F) :
    SeriesEDvd E 3 (rawSeriesC2 (PowerSeries.C p * F)) := by
  intro n
  cases n with
  | zero =>
    simp [rawSeriesC2, hF0]
  | succ m =>
    dsimp only [rawSeriesC2]
    rw [PowerSeries.coeff_map, PowerSeries.coeff_C_mul, map_mul]
    have h1 := hFdvd (m + 1)
    rw [Nat.add_sub_cancel] at h1
    have hle : 3 * (m + 1) - 3 = 3 * m := by omega
    rw [hle]
    exact dvd_mul_of_dvd_right (_root_.map_dvd rawC2 h1) _

private theorem seriesEDvd_rawShift2_monomial (i : Fin 2) (E : Abscissa)
    (B B₁ B₂ : PowerSeries Abscissa)
    (hB0 : PowerSeries.constantCoeff B = 0)
    (hB₁0 : PowerSeries.constantCoeff B₁ = 0)
    (hB₂0 : PowerSeries.constantCoeff B₂ = 0)
    (hBdvd : ∀ n, E ^ (3 * (n - 1)) ∣ PowerSeries.coeff n B)
    (hB₁dvd : ∀ n, E ^ (3 * (n - 1)) ∣ PowerSeries.coeff n B₁)
    (hB₂dvd : ∀ n, E ^ (3 * (n - 1)) ∣ PowerSeries.coeff n B₂)
    (s : Shape2) (e₀ e₁ e₂ : ℕ) (hB : e₀ + e₁ + e₂ ≤ s.B) (hJ : e₁ + 2 * e₂ ≤ s.J)
    (a : Abscissa) (r : ℕ) :
    rawC2 (E ^ (3 * r - boundedShiftExp s r)) ∣
      PowerSeries.coeff r (rawShift2 i E B B₁ B₂ (rawC2 a * rawY0 ^ e₀ * rawY1 ^ e₁ * rawY2 ^ e₂)) := by
  let Φ := rawShift2 i E B B₁ B₂
  let d0 : PowerSeries RawSource2 := -rawSeriesC2 (PowerSeries.C (E ^ 2) * B)
  let d1 : PowerSeries RawSource2 :=
    rawSeriesC2 (PowerSeries.C (E * E.derivative) * B - PowerSeries.C (E ^ 2) * B₁)
  let d2 : PowerSeries RawSource2 :=
    rawSeriesC2 (PowerSeries.C (E * hasseDeriv 2 E - E.derivative ^ 2) * B +
      PowerSeries.C (E * E.derivative) * B₁ - PowerSeries.C (E ^ 2) * B₂)
  have hd0 : SeriesEDvd E 1 d0 := by
    intro n
    have h := seriesEDvd_correction E 1 (E ^ 2) B (by omega) hB0 hBdvd (by simp) n
    simpa [d0] using dvd_neg.mpr h
  have hd1 : SeriesEDvd E 2 d1 := by
    have h1 := seriesEDvd_correction E 2 (E * E.derivative) B (by omega) hB0 hBdvd
      (by simp [dvd_mul_right])
    have h2 := seriesEDvd_correction E 1 (E ^ 2) B₁ (by omega) hB₁0 hB₁dvd (by simp)
    intro n
    have hsub := dvd_sub (h1 n) (seriesEDvd_mono h2 (by omega) n)
    simpa [d1, map_sub] using hsub
  have hd2 : SeriesEDvd E 3 d2 := by
    have h1 := seriesEDvd_correction3 E (E * hasseDeriv 2 E - E.derivative ^ 2) B hB0 hBdvd
    have h2 := seriesEDvd_correction E 2 (E * E.derivative) B₁ (by omega) hB₁0 hB₁dvd
      (by simp [dvd_mul_right])
    have h3 := seriesEDvd_correction E 1 (E ^ 2) B₂ (by omega) hB₂0 hB₂dvd (by simp)
    intro n
    have hadd := dvd_add (h1 n) (seriesEDvd_mono h2 (by omega) n)
    have hsub := dvd_sub hadd (seriesEDvd_mono h3 (by omega) n)
    simpa [d2, map_add, map_sub] using hsub
  have hy0 : Φ rawY0 = PowerSeries.C rawY0 + d0 := by
    simp [Φ, rawShift2, d0, sub_eq_add_neg]
  have hy1 : Φ rawY1 = PowerSeries.C rawY1 + d1 := by
    simp [Φ, rawShift2, d1]
  have hy2 : Φ rawY2 = PowerSeries.C rawY2 + d2 := by
    simp [Φ, rawShift2, d2]
  have hconst (F : PowerSeries Abscissa) (hF : PowerSeries.constantCoeff F = 0) :
      PowerSeries.constantCoeff (rawSeriesC2 F) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, rawSeriesC2, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hF, map_zero]
  have hd0_c : PowerSeries.constantCoeff d0 = 0 := by
    change PowerSeries.constantCoeff (-rawSeriesC2 _) = 0
    rw [map_neg, hconst _ (by simp [hB0]), neg_zero]
  have hd1_c : PowerSeries.constantCoeff d1 = 0 :=
    hconst _ (by simp [hB0, hB₁0])
  have hd2_c : PowerSeries.constantCoeff d2 = 0 :=
    hconst _ (by simp [hB0, hB₁0, hB₂0])
  -- Every power d_k ^ a_k has X ^ a_k dividing it, so coeff n (d0^a0 * d1^a1 * d2^a2) = 0 when n < a0+a1+a2
  have hpow_vanish (F : PowerSeries RawSource2) (hFc : PowerSeries.constantCoeff F = 0)
      (m : ℕ) (n : ℕ) (hn : n < m) : PowerSeries.coeff n (F ^ m) = 0 := by
    have hX : (PowerSeries.X : PowerSeries RawSource2) ∣ F :=
      PowerSeries.X_dvd_iff.mpr hFc
    obtain ⟨U, hU⟩ := pow_dvd_pow_of_dvd hX m
    rw [hU, PowerSeries.coeff_X_pow_mul']
    simp [hn]
  -- Expand Φ(rawC2 a * rawY0^e0 * rawY1^e1 * rawY2^e2) via add_pow!
  change rawC2 (E ^ (3 * r - boundedShiftExp s r)) ∣
    PowerSeries.coeff r (Φ (rawC2 a * rawY0 ^ e₀ * rawY1 ^ e₁ * rawY2 ^ e₂))
  rw [map_mul Φ, map_mul Φ, map_mul Φ, map_pow Φ, map_pow Φ, map_pow Φ, hy0, hy1, hy2]
  rw [add_pow (PowerSeries.C rawY0) d0 e₀, add_pow (PowerSeries.C rawY1) d1 e₁,
      add_pow (PowerSeries.C rawY2) d2 e₂]
  simp only [Finset.mul_sum, Finset.sum_mul, map_sum]
  apply Finset.dvd_sum; intro a₂ ha₂
  apply Finset.dvd_sum; intro a₁ ha₁
  apply Finset.dvd_sum; intro a₀ ha₀
  have ha₀' : a₀ ≤ e₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₀)
  have ha₁' : a₁ ≤ e₁ := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)
  have ha₂' : a₂ ≤ e₂ := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₂)
  -- Wait: add_pow has `x^m * y^(n - m) * C(n, m)`; let b_k = e_k - a_k be the power of d_k!
  let b₀ := e₀ - a₀
  let b₁ := e₁ - a₁
  let b₂ := e₂ - a₂
  have hb₀ : b₀ ≤ e₀ := Nat.sub_le _ _
  have hb₁ : b₁ ≤ e₁ := Nat.sub_le _ _
  have hb₂ : b₂ ≤ e₂ := Nat.sub_le _ _
  by_cases hsum : b₀ + b₁ + b₂ ≤ r
  · -- Case 1: b0 + b1 + b2 <= r, so b0 + 2*b1 + 3*b2 <= boundedShiftExp s r!
    have hbd := boundedShiftExp_bound hB hJ hb₀ hb₁ hb₂ hsum
    have hca : SeriesEDvd E 0 (Φ (rawC2 a)) := by
      rw [show Φ (rawC2 a) = rawSeriesC2 (scaledShift3 i E a) from jetHom2_base _ _ _ _ _]
      exact seriesEDvd_scaledShift3 i E a
    have hterm : SeriesEDvd E (b₀ + 2 * b₁ + 3 * b₂)
        (Φ (rawC2 a) *
          (PowerSeries.C rawY0 ^ a₀ * d0 ^ b₀ * (e₀.choose a₀ : PowerSeries RawSource2)) *
          (PowerSeries.C rawY1 ^ a₁ * d1 ^ b₁ * (e₁.choose a₁ : PowerSeries RawSource2)) *
          (PowerSeries.C rawY2 ^ a₂ * d2 ^ b₂ * (e₂.choose a₂ : PowerSeries RawSource2))) := by
      have hc_nat (k : ℕ) : SeriesEDvd E 0 (k : PowerSeries RawSource2) := by
        simpa only [← map_natCast PowerSeries.C] using seriesEDvd_const E (k : RawSource2)
      have hp0 : SeriesEDvd E (b₀ * 1) (PowerSeries.C rawY0 ^ a₀ * d0 ^ b₀ * (e₀.choose a₀)) := by
        have := seriesEDvd_mul
          (seriesEDvd_mul (seriesEDvd_pow (seriesEDvd_const E rawY0) a₀) (seriesEDvd_pow hd0 b₀))
          (hc_nat (e₀.choose a₀))
        simpa using this
      have hp1 : SeriesEDvd E (b₁ * 2) (PowerSeries.C rawY1 ^ a₁ * d1 ^ b₁ * (e₁.choose a₁)) := by
        have := seriesEDvd_mul
          (seriesEDvd_mul (seriesEDvd_pow (seriesEDvd_const E rawY1) a₁) (seriesEDvd_pow hd1 b₁))
          (hc_nat (e₁.choose a₁))
        simpa using this
      have hp2 : SeriesEDvd E (b₂ * 3) (PowerSeries.C rawY2 ^ a₂ * d2 ^ b₂ * (e₂.choose a₂)) := by
        have := seriesEDvd_mul
          (seriesEDvd_mul (seriesEDvd_pow (seriesEDvd_const E rawY2) a₂) (seriesEDvd_pow hd2 b₂))
          (hc_nat (e₂.choose a₂))
        simpa using this
      have htot := seriesEDvd_mul (seriesEDvd_mul (seriesEDvd_mul hca hp0) hp1) hp2
      exact seriesEDvd_mono htot (by omega)
    exact seriesEDvd_mono hterm hbd r
  · -- Case 2: r < b0 + b1 + b2, so X^(b0+b1+b2) divides the whole product, hence coeff r = 0!
    have hX0 : (PowerSeries.X : PowerSeries RawSource2) ^ b₀ ∣ d0 ^ b₀ :=
      pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hd0_c) b₀
    have hX1 : (PowerSeries.X : PowerSeries RawSource2) ^ b₁ ∣ d1 ^ b₁ :=
      pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hd1_c) b₁
    have hX2 : (PowerSeries.X : PowerSeries RawSource2) ^ b₂ ∣ d2 ^ b₂ :=
      pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hd2_c) b₂
    have hXall : (PowerSeries.X : PowerSeries RawSource2) ^ (b₀ + b₁ + b₂) ∣
        Φ (rawC2 a) *
          (PowerSeries.C rawY0 ^ a₀ * d0 ^ b₀ * (e₀.choose a₀ : PowerSeries RawSource2)) *
          (PowerSeries.C rawY1 ^ a₁ * d1 ^ b₁ * (e₁.choose a₁ : PowerSeries RawSource2)) *
          (PowerSeries.C rawY2 ^ a₂ * d2 ^ b₂ * (e₂.choose a₂ : PowerSeries RawSource2)) := by
      have h1 : (PowerSeries.X : PowerSeries RawSource2) ^ (b₀ + b₁ + b₂) =
          PowerSeries.X ^ b₀ * PowerSeries.X ^ b₁ * PowerSeries.X ^ b₂ := by
        rw [pow_add, pow_add]
      rw [h1]
      have hdvd : PowerSeries.X ^ b₀ * PowerSeries.X ^ b₁ * PowerSeries.X ^ b₂ ∣
          d0 ^ b₀ * d1 ^ b₁ * d2 ^ b₂ :=
        mul_dvd_mul (mul_dvd_mul hX0 hX1) hX2
      have hfac : d0 ^ b₀ * d1 ^ b₁ * d2 ^ b₂ ∣
          Φ (rawC2 a) *
            (PowerSeries.C rawY0 ^ a₀ * d0 ^ b₀ * (e₀.choose a₀ : PowerSeries RawSource2)) *
            (PowerSeries.C rawY1 ^ a₁ * d1 ^ b₁ * (e₁.choose a₁ : PowerSeries RawSource2)) *
            (PowerSeries.C rawY2 ^ a₂ * d2 ^ b₂ * (e₂.choose a₂ : PowerSeries RawSource2)) := by
        refine ⟨Φ (rawC2 a) *
          (PowerSeries.C rawY0 ^ a₀ * (e₀.choose a₀ : PowerSeries RawSource2)) *
          (PowerSeries.C rawY1 ^ a₁ * (e₁.choose a₁ : PowerSeries RawSource2)) *
          (PowerSeries.C rawY2 ^ a₂ * (e₂.choose a₂ : PowerSeries RawSource2)), ?_⟩
        ring
      exact hdvd.trans hfac
    obtain ⟨U, hU⟩ := hXall
    rw [hU, PowerSeries.coeff_X_pow_mul']
    have hlt : ¬ b₀ + b₁ + b₂ ≤ r := by omega
    rw [ite_eq_right hlt]
    exact dvd_zero _

private theorem rawShift2_coeff_dvd (i : Fin 2) (E : Abscissa)
    (B B₁ B₂ : PowerSeries Abscissa)
    (hB0 : PowerSeries.constantCoeff B = 0)
    (hB₁0 : PowerSeries.constantCoeff B₁ = 0)
    (hB₂0 : PowerSeries.constantCoeff B₂ = 0)
    (hBdvd : ∀ n, E ^ (3 * (n - 1)) ∣ PowerSeries.coeff n B)
    (hB₁dvd : ∀ n, E ^ (3 * (n - 1)) ∣ PowerSeries.coeff n B₁)
    (hB₂dvd : ∀ n, E ^ (3 * (n - 1)) ∣ PowerSeries.coeff n B₂)
    {s : Shape2} {W : RawSource2} (hW : RawShaped2 s W) (r : ℕ) :
    rawC2 (E ^ (3 * r - boundedShiftExp s r)) ∣
      PowerSeries.coeff r (rawShift2 i E B B₁ B₂ W) := by
  conv_rhs => rw [W.as_sum_support_C_mul_X_pow]
  rw [map_sum, map_sum]
  apply Finset.dvd_sum; intro e₂ he₂
  conv_rhs => rw [(W.coeff e₂).as_sum_support_C_mul_X_pow]
  simp only [map_sum, Finset.sum_mul]
  apply Finset.dvd_sum; intro e₁ he₁
  conv_rhs => rw [((W.coeff e₂).coeff e₁).as_sum_support_C_mul_X_pow]
  simp only [map_sum, Finset.sum_mul]
  apply Finset.dvd_sum; intro e₀ he₀
  have hne : (((W.coeff e₂).coeff e₁).coeff e₀) ≠ 0 := Polynomial.mem_support_iff.mp he₀
  obtain ⟨hB, hJ, _⟩ := hW e₂ e₁ e₀ hne
  have hmon : C (C (C (((W.coeff e₂).coeff e₁).coeff e₀) * Polynomial.X ^ e₀) * Polynomial.X ^ e₁) *
      Polynomial.X ^ e₂ =
      rawC2 (((W.coeff e₂).coeff e₁).coeff e₀) * rawY0 ^ e₀ * rawY1 ^ e₁ * rawY2 ^ e₂ := by
    simp only [rawC2, jetConstant2, rawY0, rawY1, rawY2, RingHom.comp_apply, map_mul, map_pow]
  rw [hmon]
  exact seriesEDvd_rawShift2_monomial i E B B₁ B₂ hB0 hB₁0 hB₂0 hBdvd hB₁dvd hB₂dvd
    s e₀ e₁ e₂ hB hJ (((W.coeff e₂).coeff e₁).coeff e₀) r

/-! ## 5. Main Bounded-Shift Theorems -/

private theorem generic_sourceX2 (P : L[X]) :
    (sourceX P).map (algebraMap SeedPoly SeedField) = basePolynomial P := by
  change (P.map MvPolynomial.C).map (algebraMap SeedPoly SeedField) =
    P.map (algebraMap L SeedField)
  rw [Polynomial.map_map]
  have h : (algebraMap SeedPoly SeedField).comp (MvPolynomial.C : L →+* SeedPoly) =
      algebraMap L SeedField := by
    apply RingHom.ext; intro a
    rw [RingHom.comp_apply, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [h]

theorem poleSpace2_cleared {h : ℕ} {D : PoleData h} (Crt : CRTLift D) {s : Shape2}
    {Q : Source2} (hSh : Shaped2 s Q) (hQ : Q ∈ poleSpace2 Crt s) (i : Fin 2) (r : ℕ) :
    cleared2Shift D s i r Q ∈ poleSpace2 Crt s := by
  let E := basePolynomial (D.block i)
  let H := rawBlock D
  let d := boundedShiftExp s r
  obtain ⟨B, B₁, B₂, hB0, hB₁0, hB₂0, hBdvd, hB₁dvd, hB₂dvd, hY0, hY1, hY2⟩ :=
    crt_corrections_2jet Crt i
  let Φ := rawShift2 i E B B₁ B₂
  have hcompat := RingHom.congr_fun (forward2_shift Crt i B B₁ B₂ hY0 hY1 hY2) Q
  have hr := congrArg (PowerSeries.coeff r) hcompat
  change PowerSeries.coeff r (Φ (forward2 (poleProduct D) (crtPolynomial Crt) Q)) =
    PowerSeries.coeff r (PowerSeries.rescale (rawC2 (E ^ 3))
      (PowerSeries.map (forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom
        (sourceShift2 i Q))) at hr
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map, sourceShift2_coeff] at hr
  change rawC2 (H ^ (s.B + s.J)) ∣ forward2 (poleProduct D) (crtPolynomial Crt) Q at hQ
  obtain ⟨W, hW⟩ := hQ
  have hHne : H ≠ 0 := by
    have hm : (poleProduct D).Monic := (D.monic 0).mul (D.monic 1)
    exact (hm.map (algebraMap L SeedField)).ne_zero
  have hWshaped : RawShaped2 s W :=
    rawShaped2_of_mul_const (pow_ne_zero (s.B + s.J) hHne)
      (hW ▸ forward2_rawShaped2 Crt hSh)
  have hfix : Φ (rawC2 (H ^ (s.B + s.J))) = PowerSeries.C (rawC2 (H ^ (s.B + s.J))) := by
    apply rawShift2_constants
    rw [map_pow]
    change (scaledShift3 i E (basePolynomial (poleProduct D))) ^ (s.B + s.J) = _
    rw [scaledShift3_base i E (poleProduct D), ← map_pow]
    rfl
  rw [hW, map_mul, hfix, PowerSeries.coeff_C_mul] at hr
  obtain ⟨W_r, hWr⟩ := rawShift2_coeff_dvd i E B B₁ B₂ hB0 hB₁0 hB₂0 hBdvd hB₁dvd hB₂dvd hWshaped r
  rw [hWr] at hr
  have hEne : E ≠ 0 := ((D.monic i).map (algebraMap L SeedField)).ne_zero
  have hEraw_ne : rawC2 (E ^ (3 * r - d)) ≠ 0 := by
    intro hz
    have h0 := congrArg (fun P : RawSource2 => (((P.coeff 0).coeff 0).coeff 0)) hz
    simp only [rawC2, jetConstant2, RingHom.comp_apply, coeff_C, ite_true, coeff_zero] at h0
    exact pow_ne_zero (3 * r - d) hEne h0
  have hdle : d ≤ 3 * r := boundedShiftExp_le_three_mul s r
  have hEsplit : (rawC2 (E ^ 3)) ^ r = rawC2 (E ^ (3 * r - d)) * rawC2 (E ^ d) := by
    rw [← map_pow, ← pow_mul, ← map_mul, ← pow_add, Nat.sub_add_cancel hdle]
  rw [hEsplit, mul_left_comm (rawC2 (H ^ (s.B + s.J))), mul_assoc] at hr
  have hcancel : rawC2 (H ^ (s.B + s.J)) * W_r =
      rawC2 (E ^ d) * forward2 (poleProduct D) (crtPolynomial Crt) (sourceHasse2 i r Q) :=
    mul_left_cancel₀ hEraw_ne hr
  have hrow : forward2 (poleProduct D) (crtPolynomial Crt) (cleared2Shift D s i r Q) =
      rawC2 (E ^ d) * forward2 (poleProduct D) (crtPolynomial Crt) (sourceHasse2 i r Q) := by
    rw [cleared2Shift, map_mul]
    have hc : forward2 (poleProduct D) (crtPolynomial Crt)
        (jetConstant2 (sourceX (D.block i ^ d))) = rawC2 (E ^ d) := by
      have hFdef := forward2_abscissa_def Crt
      dsimp only at hFdef
      change (forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom
        (C (C (C (sourceX (D.block i ^ d))))) = _
      rw [hFdef, jetHom2_base, RingHom.comp_apply, coe_mapRingHom,
        generic_sourceX2, basePolynomial, Polynomial.map_pow]
      rfl
    rw [hc]
  change rawC2 (H ^ (s.B + s.J)) ∣
    forward2 (poleProduct D) (crtPolynomial Crt) (cleared2Shift D s i r Q)
  exact ⟨W_r, hrow.trans hcancel.symm⟩

theorem complete2_cleared {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s : Shape2} {W : ℕ} {Q : Source2}
    (hQ : Q ∈ complete2 Crt word s W) (i : Fin 2) (r : ℕ) :
    cleared2Shift D s i r Q ∈ complete2 Crt word s (W + boundedShiftExp s r * h) :=
  ⟨⟨ambient2_cleared D hQ.1.1 i r, physical2_cleared D word hQ.1.2 i r⟩,
    poleSpace2_cleared Crt (contacted2_shaped hQ.1) hQ.2 i r⟩

#print axioms poleSpace2_cleared
#print axioms complete2_cleared

end
end TwoJetShift
