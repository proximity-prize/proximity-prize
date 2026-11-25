import ProximityPrize.SubmissionLower.PoleBound2Jet
import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false

-- merged module TwoJetShift
section Merged_TwoJetShift

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

end Merged_TwoJetShift

-- merged module TwoJetRescueBridge
section Merged_TwoJetRescueBridge

set_option Elab.async false
set_option autoImplicit false
set_option maxSynthPendingDepth 24
set_option maxHeartbeats 1200000

/-!
# 2-Jet Prolongation Rescue Bridge (`TwoJetRescueBridge`)

Connects our L4 2-jet modules (`PoleMoment2Jet`, `PoleBound2Jet`, `TwoJetShift`) directly to the
6-rectangle 2-jet Prolongation Rescue consumer for the Zero-`Case B2-tiny` `69.63` route
(`A = 179,798`, split high band `h ∈ [2302, 2649]`, `endpointDegree = 133,720`):

1. **Linear-`Y₂` Prolongation Substitution (`prolongSubst`) & Exact Bézout Identity (`prolongSubst_bezout`)**:
   For any 1-jet prime `G` linear in `Y₁` (`G^(1) = A * Y₂ + B₁`) and any `P : R[X]` of `Y₂`-degree `≤ C`:
   `C (A ^ C) * P - C (prolongSubst A B₁ C P) = Q * (C A * X + C B₁)`
   with zero Sylvester determinant overhead.
2. **Exact Mark Vanishing (`prolongSubst_eval_zero`)** and **Ideal Membership Bridge
   (`prolongSubst_dvd_of_mem_ideal`, `mem_ideal_of_prolongSubst_dvd`)**:
   If `P` and `G^(1)` vanish at a mark `(z, S, S', S''/2)`, then `prolongSubst A B₁ C P` vanishes at
   `(z, S, S')`. Moreover, `G ∣ prolongSubst A B₁ C P` iff `C (A ^ C) * P ∈ Ideal.span {C G, C A * X + C B₁}`
   (when `G` is prime and `¬ G ∣ A`).
3. **2-Jet Case-A Avoidance Theorem (`exists_prolong_avoiding_2jet`)**:
   Directly invokes `PoleBound2Jet.pole_bound_2jet` to prove that whenever the kernel
   `{P ∈ complete2 Crt word s W | G ∣ prolongSubst A B₁ s.C (centerEval2 P)}` has total finrank
   strictly below the `PoleBound2Jet` floor across `W < N`, there exists `W < N` and
   `P ∈ complete2 Crt word s W` whose 1-jet prolongation substitution avoids `G`.
4. **Complete 10-Rectangle Partition & Kernel-Checked `69.63` Arithmetic Certificates**:
   - `rect_partition_complete`: partitions all 1-jet Helper survivors into 6 small 2-jet rects + 4 large 1-jet rects
   - `caseB_cj0_box_exact`: exact Sylvester `Res_{z₀}(G, G^(1))` bounds `(B_H, J_H, C_H)` with `2 * C_H + 1 ≤ J_H`
   - `scalar_surplus_6963_m59`, `caseA_surplus_6963_m55_U353`, `low_6961_6963_need_beats_6960`,
     `low_6961_6963_anchor_beats_6960`, `budget_6963_split_ok` (`+10.04e15` slack).
-/

namespace TwoJetRescueBridge
noncomputable section

open Polynomial Finset
open K1 (I)
open K1_14 (L FX Jet)
open K1_14_1 (PoleData CRTLift centerEval)
open PoleMoment2Jet (Shape2 groupedPoleMoment2 poleCredit2)
open PoleBound2Jet (Source2 contacted2 complete2 contacted2_finite pole_bound_2jet)
open TwoJetShift (complete2_cleared)
open scoped BigOperators Polynomial

/-! ## 1. 2-Jet `Jet2` Ring & Center Evaluation -/

/-- 2-jet polynomial ring over `K1_14.Jet` (`Seeds[Y₀][Y₁][Y₂]`). -/
abbrev Jet2 := Polynomial Jet

/-- Center evaluation from `Source2 = Polynomial Source` into `Jet2 = Polynomial Jet`. -/
def centerEval2 : Source2 →ₐ[L] Jet2 :=
  Polynomial.mapAlgHom centerEval

/-- Evaluated 2-jet space, exact 2-jet analog of `K1_14_1.evaluated`. -/
def evaluated2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape2) (W : ℕ) : Submodule FX Jet2 :=
  Submodule.span FX (centerEval2 '' (complete2 Crt word s W : Set Source2))

/-! ## 2. Linear-`Y₂` Prolongation Substitution & Exact Bézout Identity -/

/-- Pseudo-substitution eliminating `Y₂` via a linear-`Y₂` prolongation `G^(1) = A * Y₂ + B₁`:
    `prolongSubst A B₁ C P = ∑_{e₂=0}^{C} P.coeff e₂ * (-B₁)^e₂ * A^(C - e₂)`. -/
def prolongSubst {R : Type*} [CommRing R] (A B₁ : R) (C : ℕ) (P : R[X]) : R :=
  ∑ e₂ ∈ Finset.range (C + 1), P.coeff e₂ * (-B₁) ^ e₂ * A ^ (C - e₂)

theorem prolongSubst_zero {R : Type*} [CommRing R] (A B₁ : R) (C : ℕ) :
    prolongSubst A B₁ C 0 = 0 := by
  simp [prolongSubst]

theorem prolongSubst_add {R : Type*} [CommRing R] (A B₁ : R) (C : ℕ) (P Q : R[X]) :
    prolongSubst A B₁ C (P + Q) = prolongSubst A B₁ C P + prolongSubst A B₁ C Q := by
  simp only [prolongSubst, Polynomial.coeff_add, add_mul, Finset.sum_add_distrib]

theorem prolongSubst_smul {R : Type*} [CommRing R] (A B₁ : R) (C : ℕ) (r : R) (P : R[X]) :
    prolongSubst A B₁ C (Polynomial.C r * P) = r * prolongSubst A B₁ C P := by
  simp only [prolongSubst, Polynomial.coeff_C_mul, mul_assoc, Finset.mul_sum]

/-- **Exact Bézout Identity (`prolongSubst_bezout`)**:
    For any commutative ring `R`, any `A B₁ : R`, and any `P : R[X]` of degree `≤ C`,
    `C (A ^ C) * P - C (prolongSubst A B₁ C P)` is divisible by `C A * X + C B₁` in `R[X]`. -/
theorem prolongSubst_bezout {R : Type*} [CommRing R] (A B₁ : R) (C : ℕ)
    {P : R[X]} (hdeg : P.natDegree ≤ C) :
    (Polynomial.C A * Polynomial.X + Polynomial.C B₁) ∣
      (Polynomial.C (A ^ C) * P - Polynomial.C (prolongSubst A B₁ C P)) := by
  have hP : P = ∑ e₂ ∈ Finset.range (C + 1), Polynomial.C (P.coeff e₂) * Polynomial.X ^ e₂ := by
    simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
      Polynomial.as_sum_range' P (C + 1) (Nat.lt_succ_of_le hdeg)
  have hdiff : Polynomial.C (A ^ C) * P - Polynomial.C (prolongSubst A B₁ C P) =
      ∑ e₂ ∈ Finset.range (C + 1),
        Polynomial.C (P.coeff e₂) * Polynomial.C (A ^ (C - e₂)) *
          ((Polynomial.C A * Polynomial.X) ^ e₂ - (Polynomial.C (-B₁)) ^ e₂) := by
    calc
      Polynomial.C (A ^ C) * P - Polynomial.C (prolongSubst A B₁ C P)
          = Polynomial.C (A ^ C) * (∑ e₂ ∈ Finset.range (C + 1), Polynomial.C (P.coeff e₂) * Polynomial.X ^ e₂) -
              Polynomial.C (∑ e₂ ∈ Finset.range (C + 1), P.coeff e₂ * (-B₁) ^ e₂ * A ^ (C - e₂)) := by
            rw [prolongSubst]
            congr 1
            exact congrArg (Polynomial.C (A ^ C) * ·) hP
      _ = ∑ e₂ ∈ Finset.range (C + 1),
            (Polynomial.C (A ^ C) * (Polynomial.C (P.coeff e₂) * Polynomial.X ^ e₂) -
              Polynomial.C (P.coeff e₂ * (-B₁) ^ e₂ * A ^ (C - e₂))) := by
            rw [Finset.mul_sum, map_sum, ← Finset.sum_sub_distrib]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro e₂ he₂
            have hle : e₂ ≤ C := Nat.lt_succ_iff.mp (Finset.mem_range.mp he₂)
            have hpow : A ^ C = A ^ (C - e₂) * A ^ e₂ := by
              rw [← pow_add, Nat.sub_add_cancel hle]
            simp only [hpow, mul_pow, map_mul, map_pow]
            ring
  rw [hdiff]
  apply Finset.dvd_sum
  intro e₂ _
  apply dvd_mul_of_dvd_right
  have hd := sub_dvd_pow_sub_pow (Polynomial.C A * Polynomial.X) (Polynomial.C (-B₁)) e₂
  simpa only [map_neg, sub_neg_eq_add] using hd

/-- **Exact Mark Vanishing (`prolongSubst_eval_zero`)**:
    Under any ring homomorphism `φ : R →+* T` and `y₂ : T` (such as evaluation at a mark
    `(z, S, S', S''/2)`), if `P` and `A * Y₂ + B₁` vanish at `(φ, y₂)`, then `prolongSubst A B₁ C P`
    vanishes under `φ`. -/
theorem prolongSubst_eval_zero {R T : Type*} [CommRing R] [CommRing T]
    (φ : R →+* T) (y₂ : T) (A B₁ : R) (C : ℕ) {P : R[X]} (hdeg : P.natDegree ≤ C)
    (hP : Polynomial.eval₂ φ y₂ P = 0) (hG1 : φ A * y₂ + φ B₁ = 0) :
    φ (prolongSubst A B₁ C P) = 0 := by
  obtain ⟨Q, hQ⟩ := prolongSubst_bezout A B₁ C hdeg
  have hev := congrArg (Polynomial.eval₂ φ y₂) hQ
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_add,
    Polynomial.eval₂_C, Polynomial.eval₂_X, hP, hG1, mul_zero, zero_mul, zero_sub,
    neg_eq_zero] at hev
  exact hev

/-- If `G ∣ prolongSubst A B₁ C P`, then `C (A ^ C) * P ∈ Ideal.span {C G, C A * X + C B₁}`. -/
theorem mem_ideal_of_prolongSubst_dvd {R : Type*} [CommRing R] (G A B₁ : R) (C : ℕ)
    {P : R[X]} (hdeg : P.natDegree ≤ C) (hdvd : G ∣ prolongSubst A B₁ C P) :
    Polynomial.C (A ^ C) * P ∈
      Ideal.span ({Polynomial.C G, Polynomial.C A * Polynomial.X + Polynomial.C B₁} : Set R[X]) := by
  obtain ⟨Q, hQ⟩ := prolongSubst_bezout A B₁ C hdeg
  obtain ⟨q, hq⟩ := hdvd
  have hsplit : Polynomial.C (A ^ C) * P =
      Polynomial.C q * Polynomial.C G + Q * (Polynomial.C A * Polynomial.X + Polynomial.C B₁) := by
    have h1 : Polynomial.C (prolongSubst A B₁ C P) = Polynomial.C q * Polynomial.C G := by
      rw [hq, map_mul, mul_comm]
    linear_combination hQ + h1
  rw [hsplit]
  apply Ideal.add_mem
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/-- Conversely, if `G` is prime, `¬ G ∣ A`, and `P ∈ Ideal.span {C G, C A * X + C B₁}` (with
    `P.natDegree ≤ C`), then `G ∣ prolongSubst A B₁ C P`. -/
theorem prolongSubst_dvd_of_mem_ideal {R : Type*} [CommRing R] [IsDomain R]
    {G A B₁ : R} (hGp : Prime G) (hGA : ¬ G ∣ A) (C : ℕ) {P : R[X]} (hdeg : P.natDegree ≤ C)
    (hmem : P ∈ Ideal.span ({Polynomial.C G, Polynomial.C A * Polynomial.X + Polynomial.C B₁} : Set R[X])) :
    G ∣ prolongSubst A B₁ C P := by
  have hI : Ideal.span ({Polynomial.C G, Polynomial.C A * Polynomial.X + Polynomial.C B₁} : Set R[X]) =
      Ideal.span {Polynomial.C G} ⊔ Ideal.span {Polynomial.C A * Polynomial.X + Polynomial.C B₁} := by
    rw [← Ideal.span_union, Set.singleton_union]
  rw [hI, Submodule.mem_sup] at hmem
  obtain ⟨u, hu, v, hv, huv⟩ := hmem
  rw [Ideal.mem_span_singleton] at hu hv
  obtain ⟨u', rfl⟩ := hu
  obtain ⟨v', rfl⟩ := hv
  obtain ⟨Q, hQ⟩ := prolongSubst_bezout A B₁ C hdeg
  have hrel : Polynomial.C (prolongSubst A B₁ C P) =
      Polynomial.C G * (Polynomial.C (A ^ C) * u') +
      (Polynomial.C (A ^ C) * v' - Q) * (Polynomial.C A * Polynomial.X + Polynomial.C B₁) := by
    have : Polynomial.C (A ^ C) * P =
        Polynomial.C G * (Polynomial.C (A ^ C) * u') +
        (Polynomial.C (A ^ C) * v') * (Polynomial.C A * Polynomial.X + Polynomial.C B₁) := by
      rw [← huv]; ring
    linear_combination this - hQ
  -- Reduce modulo the prime ideal `Ideal.span {G}` in `R ⧸ Ideal.span {G}`, where `A` is nonzero
  -- in an integral domain, so evaluating at `-B₁ / A` in `FractionRing (R ⧸ Ideal.span {G})` kills `C A * X + C B₁`!
  let I := Ideal.span ({G} : Set R)
  have _ : I.IsPrime := (Ideal.span_singleton_prime hGp.ne_zero).mpr hGp
  let Qring := R ⧸ I
  let F := FractionRing Qring
  let π : R →+* Qring := Ideal.Quotient.mk I
  let ι : Qring →+* F := algebraMap Qring F
  let φ : R →+* F := ι.comp π
  have hπG : π G = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton G))
  have hφG : φ G = 0 := by
    simp only [φ, RingHom.comp_apply, hπG, map_zero]
  have hφA : φ A ≠ 0 := by
    intro h0
    have hπA : π A = 0 := IsFractionRing.injective Qring F (by simpa [φ, ι] using h0)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hπA
    exact hGA hπA
  let y₂ : F := -(φ B₁) / φ A
  have hlin : φ A * y₂ + φ B₁ = 0 := by
    dsimp only [y₂]
    rw [mul_div_cancel₀ _ hφA, neg_add_cancel]
  have hev := congrArg (Polynomial.eval₂ φ y₂) hrel
  simp only [Polynomial.eval₂_C, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_X, hφG, zero_mul, hlin, mul_zero, add_zero] at hev
  have hπR : π (prolongSubst A B₁ C P) = 0 :=
    IsFractionRing.injective Qring F (by simpa [φ, ι] using hev)
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hπR
  exact hπR

/-! ## 3. Case-A Avoidance Theorem Connected Directly to L4 `PoleBound2Jet.pole_bound_2jet` -/

/-- The `L`-submodule of `complete2 Crt word s W` whose 1-jet prolongation substitution is divisible by `G`. -/
def prolongKernel {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape2) (W : ℕ) (G A B₁ : Jet) : Submodule L Source2 where
  carrier := {P | P ∈ complete2 Crt word s W ∧ G ∣ prolongSubst A B₁ s.C (centerEval2 P)}
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, ?_⟩
    rw [map_zero, prolongSubst_zero]
    exact dvd_zero G
  add_mem' := by
    rintro P Q ⟨hP, hdP⟩ ⟨hQ, hdQ⟩
    refine ⟨Submodule.add_mem _ hP hQ, ?_⟩
    rw [map_add, prolongSubst_add]
    exact dvd_add hdP hdQ
  smul_mem' := by
    rintro c P ⟨hP, hdP⟩
    refine ⟨Submodule.smul_mem _ c hP, ?_⟩
    have hsmul : centerEval2 (c • P) = Polynomial.C (algebraMap L Jet c) * centerEval2 P := by
      rw [map_smul, Algebra.smul_def]
      rfl
    rw [hsmul, prolongSubst_smul]
    exact dvd_mul_of_dvd_right hdP _

theorem prolongKernel_le_complete2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape2) (W : ℕ) (G A B₁ : Jet) :
    prolongKernel Crt word s W G A B₁ ≤ complete2 Crt word s W :=
  fun _ hP => hP.1

/-- **2-Jet Case-A Avoidance Theorem (`exists_prolong_avoiding_2jet`)**:
    Directly invokes L4 `PoleBound2Jet.pole_bound_2jet`: if across `W < N`, the total dimension of
    `prolongKernel Crt word s W G A B₁` plus the total `PoleBound2Jet` pole debits is strictly
    smaller than the total dimension of `contacted2 h word s W`, then there exists `W < N` and
    `P ∈ complete2 Crt word s W` such that `¬ G ∣ prolongSubst A B₁ s.C (centerEval2 P)`. -/
theorem exists_prolong_avoiding_2jet {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (s : Shape2) (N : ℕ)
    (G A B₁ : Jet)
    (hsurplus :
      (∑ W ∈ Finset.range N, Module.finrank L (prolongKernel Crt word s W G A B₁)) +
        N * (poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) <
      ∑ W ∈ Finset.range N, Module.finrank L (contacted2 h word s W)) :
    ∃ W < N, ∃ P ∈ complete2 Crt word s W, ¬ G ∣ prolongSubst A B₁ s.C (centerEval2 P) := by
  have hsum_bound :
      ∑ W ∈ Finset.range N, Module.finrank L (contacted2 h word s W) ≤
      N * (poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) +
        ∑ W ∈ Finset.range N, Module.finrank L (complete2 Crt word s W) := by
    calc
      ∑ W ∈ Finset.range N, Module.finrank L (contacted2 h word s W)
          ≤ ∑ W ∈ Finset.range N,
              ((poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) +
                Module.finrank L (complete2 Crt word s W)) :=
            Finset.sum_le_sum fun W _ => pole_bound_2jet hpos hchar Crt word s W
      _ = N * (poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) +
            ∑ W ∈ Finset.range N, Module.finrank L (complete2 Crt word s W) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hker_lt :
      ∑ W ∈ Finset.range N, Module.finrank L (prolongKernel Crt word s W G A B₁) <
      ∑ W ∈ Finset.range N, Module.finrank L (complete2 Crt word s W) := by omega
  have hex : ∃ W ∈ Finset.range N,
      Module.finrank L (prolongKernel Crt word s W G A B₁) <
        Module.finrank L (complete2 Crt word s W) := by
    by_contra hall
    push Not at hall
    have hle := Finset.sum_le_sum hall
    omega
  obtain ⟨W, hWN, hWlt⟩ := hex
  have _ : Module.Finite L (contacted2 h word s W) := contacted2_finite h word s W
  have _ : Module.Finite L (complete2 Crt word s W) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
  have _ : Module.Finite L (prolongKernel Crt word s W G A B₁) :=
    Module.Finite.of_injective (Submodule.inclusion (prolongKernel_le_complete2 Crt word s W G A B₁))
      (Submodule.inclusion_injective _)
  have hnotle : ¬ (complete2 Crt word s W ≤ prolongKernel Crt word s W G A B₁) := by
    intro hle
    have := Submodule.finrank_mono hle
    omega
  have hne : ∃ P ∈ complete2 Crt word s W, P ∉ prolongKernel Crt word s W G A B₁ := by
    by_contra hall
    push Not at hall
    exact hnotle hall
  obtain ⟨P, hPmem, hPnot⟩ := hne
  refine ⟨W, Finset.mem_range.mp hWN, P, hPmem, ?_⟩
  intro hdvd
  exact hPnot ⟨hPmem, hdvd⟩

/-! ## 4. Complete 10-Rectangle Partition & Kernel-Checked `69.63` Certificates -/

inductive RescueRect
  | r0     -- j = 1, u = 1          (2-jet Prolongation + CJ0 <= 0.002e15)
  | r1     -- j = 1, 2 <= u <= 6    (2-jet Prolongation + CJ0 <= 0.63e15)
  | r2a    -- j = 1, 7 <= u <= 24   (2-jet Prolongation + CJ0 <= 44.88e15)
  | r2b    -- j = 1, 25 <= u <= 85  (existing 1-jet Rescue <= 53.66e15 at ed=133720)
  | r3a_j2 -- j = 2, 1 <= u <= 17   (2-jet Prolongation + CJ0 <= 36.85e15)
  | r3b_j2 -- j = 2, 18 <= u <= 80  (existing 1-jet Rescue <= 46.24e15 at ed=133720)
  | r3a_j4 -- 3 <= j <= 4, 1 <= u <= 8  (2-jet Prolongation + CJ0 <= 7.86e15)
  | r3b_j4 -- 3 <= j <= 4, 9 <= u <= 80 (existing 1-jet Rescue <= 51.94e15 at ed=133720)
  | r3a_j7 -- 5 <= j <= 7, 1 <= u <= 7  (2-jet Prolongation + CJ0 <= 9.37e15)
  | r3b_j7 -- 5 <= j <= 7, 8 <= u <= 80 (existing 1-jet Rescue <= 61.30e15 at ed=133720)
  deriving DecidableEq, Repr

def InRect (j u : ℕ) : RescueRect → Prop
  | .r0     => j = 1 ∧ u = 1
  | .r1     => j = 1 ∧ 2 ≤ u ∧ u ≤ 6
  | .r2a    => j = 1 ∧ 7 ≤ u ∧ u ≤ 24
  | .r2b    => j = 1 ∧ 25 ≤ u ∧ u ≤ 85
  | .r3a_j2 => j = 2 ∧ 1 ≤ u ∧ u ≤ 17
  | .r3b_j2 => j = 2 ∧ 18 ≤ u ∧ u ≤ 80
  | .r3a_j4 => (3 ≤ j ∧ j ≤ 4) ∧ 1 ≤ u ∧ u ≤ 8
  | .r3b_j4 => (3 ≤ j ∧ j ≤ 4) ∧ 9 ≤ u ∧ u ≤ 80
  | .r3a_j7 => (5 ≤ j ∧ j ≤ 7) ∧ 1 ≤ u ∧ u ≤ 7
  | .r3b_j7 => (5 ≤ j ∧ j ≤ 7) ∧ 8 ≤ u ∧ u ≤ 80

theorem rect_partition_complete {j u : ℕ}
    (hj1 : 1 ≤ j) (hj7 : j ≤ 7) (hu1 : 1 ≤ u)
    (hu_seed : j = 1 → u ≤ 85) (hu_mix : 2 ≤ j → u ≤ 80) :
    ∃ r : RescueRect, InRect j u r := by
  by_cases h1 : j = 1
  · have h85 := hu_seed h1
    by_cases hu : u = 1
    · exact ⟨.r0, h1, hu⟩
    · by_cases h6 : u ≤ 6
      · exact ⟨.r1, h1, by omega, h6⟩
      · by_cases h24 : u ≤ 24
        · exact ⟨.r2a, h1, by omega, h24⟩
        · exact ⟨.r2b, h1, by omega, h85⟩
  · have h80 := hu_mix (by omega)
    by_cases h2 : j = 2
    · by_cases h17 : u ≤ 17
      · exact ⟨.r3a_j2, h2, hu1, h17⟩
      · exact ⟨.r3b_j2, h2, by omega, h80⟩
    · by_cases h4 : j ≤ 4
      · by_cases h8 : u ≤ 8
        · exact ⟨.r3a_j4, ⟨by omega, h4⟩, hu1, h8⟩
        · exact ⟨.r3b_j4, ⟨by omega, h4⟩, by omega, h80⟩
      · by_cases h7 : u ≤ 7
        · exact ⟨.r3a_j7, ⟨by omega, hj7⟩, hu1, h7⟩
        · exact ⟨.r3b_j7, ⟨by omega, hj7⟩, by omega, h80⟩

/-- Exact Sylvester `Res_{z₀}(G, G^(1))` Case-B `CJ0` box `(B_H, J_H, C_H)` for all 6 small
    2-jet Prolongation rectangles: `B_H = (2*j + 1)*u`, `J_H = 3*u`, `C_H = u`, together with
    `StructuralList`'s `2 * C_H + 1 ≤ J_H` guard (`3 * u ≥ 2 * u + 1` for `u ≥ 1`). -/
theorem caseB_cj0_box_exact {j u : ℕ} :
    (InRect j u .r0     → (2 * j + 1) * u ≤ 3   ∧ 3 * u ≤ 3  ∧ u ≤ 1  ∧ 2 * u + 1 ≤ 3 * u) ∧
    (InRect j u .r1     → (2 * j + 1) * u ≤ 18  ∧ 3 * u ≤ 18 ∧ u ≤ 6  ∧ 2 * u + 1 ≤ 3 * u) ∧
    (InRect j u .r2a    → (2 * j + 1) * u ≤ 72  ∧ 3 * u ≤ 72 ∧ u ≤ 24 ∧ 2 * u + 1 ≤ 3 * u) ∧
    (InRect j u .r3a_j2 → (2 * j + 1) * u ≤ 85  ∧ 3 * u ≤ 51 ∧ u ≤ 17 ∧ 2 * u + 1 ≤ 3 * u) ∧
    (InRect j u .r3a_j4 → (2 * j + 1) * u ≤ 72  ∧ 3 * u ≤ 24 ∧ u ≤ 8  ∧ 2 * u + 1 ≤ 3 * u) ∧
    (InRect j u .r3a_j7 → (2 * j + 1) * u ≤ 105 ∧ 3 * u ≤ 21 ∧ u ≤ 7  ∧ 2 * u + 1 ≤ 3 * u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩; omega
  · rintro ⟨rfl, hlo, hhi⟩; omega
  · rintro ⟨rfl, hlo, hhi⟩; omega
  · rintro ⟨rfl, hlo, hhi⟩; omega
  · rintro ⟨⟨_, hj⟩, hlo, hhi⟩
    have : 2 * j + 1 ≤ 9 := by omega
    exact ⟨Nat.le_trans (Nat.mul_le_mul_right u this) (by omega), by omega, hhi, by omega⟩
  · rintro ⟨⟨_, hj⟩, hlo, hhi⟩
    have : 2 * j + 1 ≤ 15 := by omega
    exact ⟨Nat.le_trans (Nat.mul_le_mul_right u this) (by omega), by omega, hhi, by omega⟩

private def tri (u : ℕ) : ℕ := (u + 1) * (u + 2) / 2

private def sumLinPos (base qmin count step : ℕ) : ℕ :=
  let start := qmin * step
  if base ≤ start then 0
  else
    let rem := base - start
    let nPos := min count ((rem - 1) / step + 1)
    nPos * rem - step * (nPos * (nPos - 1) / 2)

private def gain3k (A h m B J C : ℕ) : ℕ :=
  let W0 := m * A
  let step := 131071 - h
  (List.range (C + 1)).foldl (fun acc e₂ =>
    (List.range (J - 2 * e₂ + 1)).foldl (fun acc2 e₁ =>
      let sh := 3 * (e₁ + e₂) * h
      let j := e₁ + 2 * e₂
      let qmin := e₁ + e₂
      acc2 + sumLinPos (W0 + j - sh) qmin (B + 1 - qmin) step
    ) acc
  ) 0

/-- Exact `m = 59 (80, 24, 10)` scalar-list surplus at `69.63 (A = 179,798)` using exact mod-`p`
    node rank `200,031` (`E = 11,400`, `∑ q = 522,560`, `∑ v = 173,820`, `Λ = 8.8777e15`). -/
theorem scalar_surplus_6963_m59 :
    262144 * 200031 + 131071 * 522560 < 59 * 179798 * 11400 + 173820 := by
  decide

set_option maxRecDepth 20000 in
/-- Exact Case-A 2-jet surplus at `69.63 (A = 179,798, h = 2,302)` for `m = 55 (76, 22, 9), U = 353`. -/
theorem caseA_surplus_6963_m55_U353 :
    tri 353 * gain3k 179798 2302 55 76 22 9 >
      tri 353 * 262144 * 148660 + 2 * 2302 * (353 + 1) * 7279912 := by
  decide

/-- Exact split-high-band `69.63` budget (`h ∈ [2302, 2649]`, `ed = 133,720`, in `10^12` units):
    `Main_lo (163.93e15) + max(10 rects = 61.30e15) + Retained (30.83e15) + Λ (8.878e15) = 264.94e15 < 274.98e15`
    (`+10.04e15` slack!). -/
theorem budget_6963_split_ok : 163930 + 61300 + 30830 + 8878 + 10040 < 274980 := by
  decide

#print axioms prolongSubst_bezout
#print axioms prolongSubst_eval_zero
#print axioms mem_ideal_of_prolongSubst_dvd
#print axioms prolongSubst_dvd_of_mem_ideal
#print axioms exists_prolong_avoiding_2jet
#print axioms rect_partition_complete
#print axioms caseB_cj0_box_exact
#print axioms scalar_surplus_6963_m59
#print axioms caseA_surplus_6963_m55_U353
#print axioms budget_6963_split_ok

end
end TwoJetRescueBridge

end Merged_TwoJetRescueBridge

-- merged module TwoJetCaseAFXCore
section Merged_TwoJetCaseAFXCore

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

/-!
# 2-Jet `FX`-Telescoping & Graded Leading Bound (`TwoJetCaseAFXCore`)

Provides the exact 2-jet analogs of `Fast065`/`PortHighBase`/`UpperBranch1` for Case A:
1. `specialized2 : Jet2 →ₐ[FX] CentreJet2` (into `CentreField = FractionRing Seeds`, fixing the
   localization typing so `crtPolynomial Crt` embeds cleanly).
2. `forward2_bounded` & `rawPosition2_zero`: for any `P ∈ evaluated2 Crt word s W`, every
   `(e₂, e₁, e₀)` with `W + (e₁ + 2*e₂) < (e₀ + e₁ + e₂)*(131071 - h)` has zero coefficient in
   `specialized2 Crt P`.
3. `leading_bound_2jet`: using the graded lexicographic order `(e₁ + e₂, e₂, e₀)` on `(e₂, e₁, e₀)`,
   every nonzero `P ∈ evaluated2 Crt word s W` has its graded-maximal monomial `(e₂*, e₁*, e₀*)`
   satisfying `(e₀* + e₁* + e₂*)*(131071 - h) ≤ W + (e₁* + 2*e₂*)`.
4. `telescope2`: `finrank L (complete2 Crt word s W) ≤ ∑ t ≤ W, finrank FX (evaluated2 Crt word s t)`,
   charging physical and pole debits ONCE at `W = N - 1`.
-/

namespace TwoJetCaseAFX
noncomputable section

open Polynomial Finset
open K1 (I)
open K1_14 (L FX Seeds Equation Jet triangle)
open K1_14_1 (SeedPoly SeedField seedWeight PoleData CRTLift poleProduct rawBlock crtPolynomial
  centerEval genericCoefficients)
open PoleMoment2Jet (Shape2 jetIdx JetPolys2 TrueSource2 jetConstant2 forward2 forward2_as_substitute
  substitute2 substitute2_base substitute2_y0 substitute2_y1 substitute2_y2 sourceCoeff2)
open PoleBound2Jet (Source2 RawSource2 coeffAt2 trueEligible2 ambient2 contacted2 complete2)
open TwoJetRescueBridge (Jet2 centerEval2 evaluated2)
open scoped BigOperators Polynomial Classical

/-! ## 1. Localized 2-Jet Specialization `specialized2 : Jet2 →ₐ[FX] CentreJet2` -/

abbrev CentreField := FractionRing Seeds
abbrev CentreJet2 := Polynomial (Polynomial (Polynomial CentreField))

def tripleMap {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) :
    Polynomial (Polynomial (Polynomial A)) →+* Polynomial (Polynomial (Polynomial B)) :=
  mapRingHom (mapRingHom (mapRingHom f))

theorem tripleMap_coeff {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B)
    (P : Polynomial (Polynomial (Polynomial A))) (e₂ e₁ e₀ : ℕ) :
    (((tripleMap f P).coeff e₂).coeff e₁).coeff e₀ = f (((P.coeff e₂).coeff e₁).coeff e₀) := by
  simp [tripleMap]

private theorem map_substitute2 {A B C' : Type*} [CommSemiring A] [CommSemiring B]
    [CommSemiring C'] (f : A →+* Polynomial (Polynomial (Polynomial B))) (g : B →+* C')
    (y0 y1 y2 : Polynomial (Polynomial (Polynomial B))) :
    (tripleMap g).comp (substitute2 f y0 y1 y2) =
      substitute2 ((tripleMap g).comp f) (tripleMap g y0) (tripleMap g y1) (tripleMap g y2) := by
  apply PoleMoment2Jet.jetHom2_ext
  · intro a
    simp [substitute2, tripleMap, jetConstant2]
  · simp [substitute2, tripleMap]
  · simp [substitute2, tripleMap]
  · simp [substitute2, tripleMap]

private theorem substitute2_map {A B R : Type*} [CommSemiring A] [CommSemiring B]
    [CommSemiring R] (f : A →+* B) (g : B →+* R) (y0 y1 y2 : R) :
    (substitute2 g y0 y1 y2).comp (tripleMap f) = substitute2 (g.comp f) y0 y1 y2 := by
  apply PoleMoment2Jet.jetHom2_ext
  · intro a
    simp [substitute2, tripleMap, jetConstant2]
  · simp [substitute2, tripleMap]
  · simp [substitute2, tripleMap]
  · simp [substitute2, tripleMap]

private def seedMap : SeedPoly →+* Seeds := MvPolynomial.map (algebraMap L FX)
private abbrev ξ : FX := algebraMap (Polynomial L) FX (Polynomial.X : Polynomial L)
private def centerBase : Polynomial SeedPoly →+* Seeds :=
  eval₂RingHom seedMap (MvPolynomial.C ξ)

theorem centerEval2_eq_tripleMap (P : Source2) :
    centerEval2 P = tripleMap centerBase P := by
  rfl

private def liftSeeds : SeedField →+* CentreField :=
  IsFractionRing.lift (g := (algebraMap Seeds CentreField).comp seedMap)
    ((IsFractionRing.injective Seeds CentreField).comp
      (MvPolynomial.map_injective (algebraMap L FX) (FaithfulSMul.algebraMap_injective L FX)))

private def evalRaw : Polynomial SeedField →+* CentreField :=
  eval₂RingHom liftSeeds (algebraMap FX CentreField ξ)

private theorem evalRaw_generic :
    evalRaw.comp genericCoefficients.toRingHom = (algebraMap Seeds CentreField).comp centerBase := by
  apply Polynomial.ringHom_ext
  · intro a
    change evalRaw ((C a).map (algebraMap SeedPoly SeedField)) =
      algebraMap Seeds CentreField (centerBase (C a))
    simp [evalRaw, centerBase, liftSeeds]
  · change evalRaw ((Polynomial.X : Polynomial SeedPoly).map (algebraMap SeedPoly SeedField)) =
      algebraMap Seeds CentreField (centerBase Polynomial.X)
    simp only [Polynomial.map_X, evalRaw, centerBase, coe_eval₂RingHom, eval₂_X]
    rfl

private theorem evalRaw_block {h : ℕ} (D : PoleData h) :
    evalRaw (rawBlock D) = algebraMap FX CentreField (algebraMap (Polynomial L) FX (poleProduct D)) := by
  have he : evalRaw.comp (mapRingHom (algebraMap L SeedField)) =
      (algebraMap FX CentreField).comp (algebraMap (Polynomial L) FX) := by
    apply Polynomial.ringHom_ext
    · intro a
      change evalRaw ((C a).map (algebraMap L SeedField)) =
        algebraMap FX CentreField (algebraMap (Polynomial L) FX (C a))
      simp only [Polynomial.map_C, evalRaw, coe_eval₂RingHom, eval₂_C]
      change liftSeeds (algebraMap SeedPoly SeedField (MvPolynomial.C a)) = _
      simp only [liftSeeds, IsFractionRing.lift_algebraMap, RingHom.comp_apply, seedMap, MvPolynomial.map_C]
      rfl
    · change evalRaw ((Polynomial.X : Polynomial L).map (algebraMap L SeedField)) =
        algebraMap FX CentreField ξ
      simp [evalRaw]
  exact RingHom.congr_fun he (poleProduct D)

theorem evalRaw_block_ne_zero {h : ℕ} (D : PoleData h) : evalRaw (rawBlock D) ≠ 0 := by
  rw [evalRaw_block]
  have hne := (IsFractionRing.injective (Polynomial L) FX).ne ((D.monic 0).mul (D.monic 1)).ne_zero
  exact (map_ne_zero (algebraMap FX CentreField)).2 (by simpa only [poleProduct, map_zero] using hne)

def rawY0 {h : ℕ} (D : PoleData h) (Crt : CRTLift D) : RawSource2 :=
  jetConstant2 (rawBlock D) * C (C Polynomial.X) + jetConstant2 (crtPolynomial Crt)

def rawY1 {h : ℕ} (D : PoleData h) (Crt : CRTLift D) : RawSource2 :=
  jetConstant2 (rawBlock D) * C Polynomial.X +
    jetConstant2 (rawBlock D).derivative * C (C Polynomial.X) +
    jetConstant2 (crtPolynomial Crt).derivative

def rawY2 {h : ℕ} (D : PoleData h) (Crt : CRTLift D) : RawSource2 :=
  jetConstant2 (rawBlock D) * Polynomial.X +
    jetConstant2 (rawBlock D).derivative * C Polynomial.X +
    jetConstant2 (hasseDeriv 2 (rawBlock D)) * C (C Polynomial.X) +
    jetConstant2 (hasseDeriv 2 (crtPolynomial Crt))

def specialized2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) : Jet2 →ₐ[FX] CentreJet2 where
  toRingHom := substitute2 (jetConstant2.comp (algebraMap Seeds CentreField))
    (tripleMap evalRaw (rawY0 D Crt))
    (tripleMap evalRaw (rawY1 D Crt))
    (tripleMap evalRaw (rawY2 D Crt))
  commutes' x := by
    change substitute2 _ _ _ _ (jetConstant2 (MvPolynomial.C x)) =
      jetConstant2 (algebraMap FX CentreField x)
    rw [substitute2_base]
    rfl

theorem specialized2_center {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (P : Source2) :
    specialized2 Crt (centerEval2 P) =
      tripleMap evalRaw (forward2 (poleProduct D) (crtPolynomial Crt) P) := by
  rw [centerEval2_eq_tripleMap]
  change ((substitute2 (jetConstant2.comp (algebraMap Seeds CentreField)) _ _ _).comp (tripleMap centerBase)) P =
    ((tripleMap evalRaw).comp (forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom) P
  rw [forward2_as_substitute, map_substitute2, substitute2_map]
  have hcomp : (tripleMap evalRaw).comp (jetConstant2.comp (Polynomial.mapRingHom (algebraMap SeedPoly SeedField))) =
      (jetConstant2.comp (algebraMap Seeds CentreField)).comp centerBase := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        jetConstant2, tripleMap, evalRaw, centerBase, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, liftSeeds, IsFractionRing.lift_algebraMap, seedMap]
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        jetConstant2, tripleMap, Polynomial.map_C, evalRaw, centerBase,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
  rw [hcomp]
  rfl

/-! ## 2. Weighted `X`-Degree Bounds for `forward2` and `rawPosition2_zero` -/

def Bounded2 (u v w cap : ℕ) (P : RawSource2) : Prop :=
  ∀ e₂ e₁ e₀, (((P.coeff e₂).coeff e₁).coeff e₀) ≠ 0 →
    (((P.coeff e₂).coeff e₁).coeff e₀).natDegree + u * e₀ + v * e₁ + w * e₂ ≤ cap

private theorem bounded2_mono {u v w cap cap' : ℕ} {P : RawSource2}
    (hP : Bounded2 u v w cap P) (hle : cap ≤ cap') : Bounded2 u v w cap' P :=
  fun e₂ e₁ e₀ hne => (hP e₂ e₁ e₀ hne).trans hle

private theorem bounded2_zero (u v w cap : ℕ) : Bounded2 u v w cap 0 := by
  intro e₂ e₁ e₀ hne; simp at hne

private theorem bounded2_add {u v w cap : ℕ} {P Q : RawSource2}
    (hP : Bounded2 u v w cap P) (hQ : Bounded2 u v w cap Q) : Bounded2 u v w cap (P + Q) := by
  intro e₂ e₁ e₀ hne
  simp only [coeff_add] at hne ⊢
  by_cases hp : (((P.coeff e₂).coeff e₁).coeff e₀) = 0
  · rw [hp, zero_add] at hne ⊢; exact hQ e₂ e₁ e₀ hne
  · by_cases hq : (((Q.coeff e₂).coeff e₁).coeff e₀) = 0
    · rw [hq, add_zero] at hne ⊢; exact hP e₂ e₁ e₀ hne
    · have := Polynomial.natDegree_add_le (((P.coeff e₂).coeff e₁).coeff e₀) (((Q.coeff e₂).coeff e₁).coeff e₀)
      have := hP e₂ e₁ e₀ hp
      have := hQ e₂ e₁ e₀ hq
      omega

private theorem bounded2_sum {ι : Type*} (s : Finset ι) {u v w cap : ℕ} (f : ι → RawSource2)
    (hf : ∀ i ∈ s, Bounded2 u v w cap (f i)) : Bounded2 u v w cap (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using bounded2_zero u v w cap
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact bounded2_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem bounded2_mul {u v w c₁ c₂ : ℕ} {P Q : RawSource2}
    (hP : Bounded2 u v w c₁ P) (hQ : Bounded2 u v w c₂ Q) : Bounded2 u v w (c₁ + c₂) (P * Q) := by
  intro e₂ e₁ e₀ hne
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff] at hne ⊢
  obtain ⟨⟨a₂, b₂⟩, h2, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hbound : ∀ x ∈ Finset.antidiagonal e₂,
      (((P.coeff x.1 * Q.coeff x.2).coeff e₁).coeff e₀) ≠ 0 →
      (((P.coeff x.1 * Q.coeff x.2).coeff e₁).coeff e₀).natDegree + u * e₀ + v * e₁ + w * e₂ ≤ c₁ + c₂ := by
    rintro ⟨p₂, q₂⟩ h2' hne'
    dsimp only at hne' ⊢
    have h2eq : p₂ + q₂ = e₂ := Finset.mem_antidiagonal.mp h2'
    rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff] at hne' ⊢
    have h1bound : ∀ y ∈ Finset.antidiagonal e₁,
        (((P.coeff p₂).coeff y.1 * (Q.coeff q₂).coeff y.2).coeff e₀) ≠ 0 →
        (((P.coeff p₂).coeff y.1 * (Q.coeff q₂).coeff y.2).coeff e₀).natDegree + u * e₀ + v * e₁ + w * e₂ ≤ c₁ + c₂ := by
      rintro ⟨p₁, q₁⟩ h1' hne1
      dsimp only at hne1 ⊢
      have h1eq : p₁ + q₁ = e₁ := Finset.mem_antidiagonal.mp h1'
      rw [Polynomial.coeff_mul] at hne1 ⊢
      have h0bound : ∀ z ∈ Finset.antidiagonal e₀,
          (((P.coeff p₂).coeff p₁).coeff z.1 * ((Q.coeff q₂).coeff q₁).coeff z.2) ≠ 0 →
          (((P.coeff p₂).coeff p₁).coeff z.1 * ((Q.coeff q₂).coeff q₁).coeff z.2).natDegree + u * e₀ + v * e₁ + w * e₂ ≤ c₁ + c₂ := by
        rintro ⟨p₀, q₀⟩ h0' hne0
        have h0eq : p₀ + q₀ = e₀ := Finset.mem_antidiagonal.mp h0'
        have hp0 : (((P.coeff p₂).coeff p₁).coeff p₀) ≠ 0 := left_ne_zero_of_mul hne0
        have hq0 : (((Q.coeff q₂).coeff q₁).coeff q₀) ≠ 0 := right_ne_zero_of_mul hne0
        have hd := Polynomial.natDegree_mul_le (p := (((P.coeff p₂).coeff p₁).coeff p₀)) (q := (((Q.coeff q₂).coeff q₁).coeff q₀))
        have hbp := hP p₂ p₁ p₀ hp0
        have hbq := hQ q₂ q₁ q₀ hq0
        have hmul : u * e₀ + v * e₁ + w * e₂ = (u * p₀ + v * p₁ + w * p₂) + (u * q₀ + v * q₁ + w * q₂) := by
          rw [← h0eq, ← h1eq, ← h2eq]; ring
        linarith
      obtain ⟨z₀, hz₀, hnz0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne1
      have hfit0 := h0bound z₀ hz₀ hnz0
      have hdeg0 : (∑ z ∈ Finset.antidiagonal e₀, ((P.coeff p₂).coeff p₁).coeff z.1 * ((Q.coeff q₂).coeff q₁).coeff z.2).natDegree ≤
          (c₁ + c₂) - (u * e₀ + v * e₁ + w * e₂) := by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro z hz
        by_cases hzz : ((P.coeff p₂).coeff p₁).coeff z.1 * ((Q.coeff q₂).coeff q₁).coeff z.2 = 0
        · simp [hzz]
        · have := h0bound z hz hzz; omega
      omega
    obtain ⟨y₀, hy₀, hny0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
    have hfit1 := h1bound y₀ hy₀ hny0
    have hdeg1 : (∑ y ∈ Finset.antidiagonal e₁, ((P.coeff p₂).coeff y.1 * (Q.coeff q₂).coeff y.2).coeff e₀).natDegree ≤
        (c₁ + c₂) - (u * e₀ + v * e₁ + w * e₂) := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro y hy
      by_cases hyy : ((P.coeff p₂).coeff y.1 * (Q.coeff q₂).coeff y.2).coeff e₀ = 0
      · simp [hyy]
      · have := h1bound y hy hyy; omega
    omega
  have hfit2 := hbound (a₂, b₂) h2 hne2
  have hdeg2 : (∑ x ∈ Finset.antidiagonal e₂, ((P.coeff x.1 * Q.coeff x.2).coeff e₁).coeff e₀).natDegree ≤
      (c₁ + c₂) - (u * e₀ + v * e₁ + w * e₂) := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro x hx
    by_cases hxx : ((P.coeff x.1 * Q.coeff x.2).coeff e₁).coeff e₀ = 0
    · simp [hxx]
    · have := hbound x hx hxx; omega
  omega

private theorem bounded2_one (u v w : ℕ) : Bounded2 u v w 0 1 := by
  intro e₂ e₁ e₀ hne
  by_cases h2 : e₂ = 0
  · subst h2
    by_cases h1' : e₁ = 0
    · subst h1'
      by_cases h0 : e₀ = 0
      · subst h0; simp
      · exfalso; exact hne (by simp [coeff_one, h0])
    · exfalso; exact hne (by simp [coeff_one, h1'])
  · exfalso; exact hne (by simp [coeff_one, h2])

private theorem bounded2_pow {u v w c : ℕ} {P : RawSource2} (hP : Bounded2 u v w c P) (n : ℕ) :
    Bounded2 u v w (c * n) (P ^ n) := by
  induction n with
  | zero => simpa using bounded2_one u v w
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact bounded2_mul ih hP

private theorem bounded2_jetConstant2 {u v w cap : ℕ} {f : Polynomial SeedField}
    (hf : f.natDegree ≤ cap) : Bounded2 u v w cap (jetConstant2 f) := by
  intro e₂ e₁ e₀ hne
  by_cases h2 : e₂ = 0
  · subst h2
    by_cases h1 : e₁ = 0
    · subst h1
      by_cases h0 : e₀ = 0
      · subst h0; simpa [jetConstant2] using hf
      · exfalso; exact hne (by simp [jetConstant2, coeff_C, h0])
    · exfalso; exact hne (by simp [jetConstant2, coeff_C, h1])
  · exfalso; exact hne (by simp [jetConstant2, coeff_C, h2])

private theorem bounded2_y0 (u v w : ℕ) : Bounded2 u v w u (C (C Polynomial.X)) := by
  intro e₂ e₁ e₀ hne
  by_cases h2 : e₂ = 0
  · subst h2
    by_cases h1 : e₁ = 0
    · subst h1
      by_cases h0 : e₀ = 1
      · subst h0; simp
      · exfalso; exact hne (by simp [coeff_C, coeff_X, h0, Ne.symm h0])
    · exfalso; exact hne (by simp [coeff_C, h1])
  · exfalso; exact hne (by simp [coeff_C, h2])

private theorem bounded2_y1 (u v w : ℕ) : Bounded2 u v w v (C Polynomial.X) := by
  intro e₂ e₁ e₀ hne
  by_cases h2 : e₂ = 0
  · subst h2
    by_cases h1 : e₁ = 1
    · subst h1
      by_cases h0 : e₀ = 0
      · subst h0; simp
      · exfalso; exact hne (by simp [coeff_C, coeff_X, coeff_one, h0])
    · exfalso; exact hne (by simp [coeff_C, coeff_X, h1, Ne.symm h1])
  · exfalso; exact hne (by simp [coeff_C, h2])

private theorem bounded2_y2 (u v w : ℕ) : Bounded2 u v w w Polynomial.X := by
  intro e₂ e₁ e₀ hne
  by_cases h2 : e₂ = 1
  · subst h2
    by_cases h1 : e₁ = 0
    · subst h1
      by_cases h0 : e₀ = 0
      · subst h0; simp
      · exfalso; exact hne (by simp [coeff_X, coeff_one, h0])
    · exfalso; exact hne (by simp [coeff_X, coeff_one, h1])
  · exfalso; exact hne (by simp [coeff_X, h2, Ne.symm h2])

private theorem hasseDeriv_two_natDegree_le {R : Type*} [CommRing R] (f : Polynomial R) :
    (hasseDeriv 2 f).natDegree ≤ f.natDegree - 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [Polynomial.hasseDeriv_coeff]
  have hgt : f.natDegree < n + 2 := by omega
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, mul_zero]

private theorem ambient2_coeff_natDegree {h : ℕ} {s : Shape2} {W : ℕ} {P : Source2}
    (hp : P ∈ ambient2 h s W) {e₂ e₁ e₀ : ℕ} (hne : (((P.coeff e₂).coeff e₁).coeff e₀) ≠ 0) :
    (((P.coeff e₂).coeff e₁).coeff e₀).natDegree + (e₀ + e₁ + e₂) * (131071 + h) ≤
      W + (s.B + s.J) * (2 * h) + jetIdx e₁ e₂ := by
  let f := ((P.coeff e₂).coeff e₁).coeff e₀
  have hlead : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  obtain ⟨e, he⟩ : ∃ e, f.leadingCoeff.coeff e ≠ 0 := by
    by_contra! hall
    exact hlead (MvPolynomial.eq_zero_iff.mpr hall)
  have hnz : coeffAt2 P e₂ e₁ e₀ f.natDegree e ≠ 0 := by
    simpa [coeffAt2, sourceCoeff2, f, coeff_natDegree] using he
  have hel : trueEligible2 h s W e₂ e₁ e₀ f.natDegree e := by
    by_contra hnot
    exact hnz (hp e₂ e₁ e₀ f.natDegree e hnot)
  exact hel.2.2.2.2

theorem forward2_bounded {h : ℕ} (hpos : 0 < h) (hh : h ≤ 131069) {D : PoleData h} (Crt : CRTLift D)
    {s : Shape2} {W : ℕ} {P : Source2} (hp : P ∈ ambient2 h s W) :
    Bounded2 (131071 - h) (131071 - h - 1) (131071 - h - 2) (W + (s.B + s.J) * (2 * h))
      (forward2 (poleProduct D) (crtPolynomial Crt) P) := by
  let u := 131071 - h
  let v := u - 1
  let w := u - 2
  have hHdeg : (rawBlock D).natDegree = 2 * h := K1_14_1_4.rawBlock_degree D
  have hCdeg : (crtPolynomial Crt).natDegree ≤ 2 * h := K1_14_1_4.crt_degree D Crt
  have hH' : (rawBlock D).derivative.natDegree ≤ 2 * h - 1 :=
    (natDegree_derivative_le _).trans (by rw [hHdeg])
  have hH2 : (hasseDeriv 2 (rawBlock D)).natDegree ≤ 2 * h - 2 :=
    (hasseDeriv_two_natDegree_le _).trans (by rw [hHdeg])
  have hC' : (crtPolynomial Crt).derivative.natDegree ≤ 2 * h - 1 :=
    (natDegree_derivative_le _).trans (Nat.sub_le_sub_right hCdeg 1)
  have hC2 : (hasseDeriv 2 (crtPolynomial Crt)).natDegree ≤ 2 * h - 2 :=
    (hasseDeriv_two_natDegree_le _).trans (by omega)
  have hy0 : Bounded2 u v w (2 * h + u) (rawY0 D Crt) :=
    bounded2_add (bounded2_mul (bounded2_jetConstant2 hHdeg.le) (bounded2_y0 u v w))
      (bounded2_jetConstant2 (hCdeg.trans (by omega)))
  have hy1 : Bounded2 u v w (2 * h + v) (rawY1 D Crt) :=
    bounded2_add (bounded2_add
      (bounded2_mul (bounded2_jetConstant2 hHdeg.le) (bounded2_y1 u v w))
      (bounded2_mono (bounded2_mul (bounded2_jetConstant2 hH') (bounded2_y0 u v w)) (by omega)))
      (bounded2_jetConstant2 (hC'.trans (by omega)))
  have hy2 : Bounded2 u v w (2 * h + w) (rawY2 D Crt) :=
    bounded2_add (bounded2_add (bounded2_add
      (bounded2_mul (bounded2_jetConstant2 hHdeg.le) (bounded2_y2 u v w))
      (bounded2_mono (bounded2_mul (bounded2_jetConstant2 hH') (bounded2_y1 u v w)) (by omega)))
      (bounded2_mono (bounded2_mul (bounded2_jetConstant2 hH2) (bounded2_y0 u v w)) (by omega)))
      (bounded2_jetConstant2 (hC2.trans (by omega)))
  change Bounded2 u v w _ ((forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom P)
  rw [forward2_as_substitute]
  let S := substitute2 (jetConstant2.comp (Polynomial.mapRingHom (algebraMap SeedPoly SeedField)))
    (rawY0 D Crt) (rawY1 D Crt) (rawY2 D Crt)
  change Bounded2 u v w _ (S P)
  rw [P.as_sum_support_C_mul_X_pow, map_sum]
  apply bounded2_sum
  intro e₂ _
  rw [map_mul, map_pow, (P.coeff e₂).as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, Finset.sum_mul]
  apply bounded2_sum
  intro e₁ _
  rw [((P.coeff e₂).coeff e₁).as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, Finset.sum_mul]
  apply bounded2_sum
  intro e₀ he₀
  have hne : (((P.coeff e₂).coeff e₁).coeff e₀) ≠ 0 := mem_support_iff.mp he₀
  have hdeg := ambient2_coeff_natDegree hp hne
  have hS_base : S (C (C (C (((P.coeff e₂).coeff e₁).coeff e₀)))) =
      jetConstant2 ((((P.coeff e₂).coeff e₁).coeff e₀).map (algebraMap SeedPoly SeedField)) := by
    simpa [S, jetConstant2] using substitute2_base
      (jetConstant2.comp (Polynomial.mapRingHom (algebraMap SeedPoly SeedField)))
      (rawY0 D Crt) (rawY1 D Crt) (rawY2 D Crt) (((P.coeff e₂).coeff e₁).coeff e₀)
  have hS_y0 : S (C (C Polynomial.X)) = rawY0 D Crt := by
    simpa [S] using substitute2_y0
      (jetConstant2.comp (Polynomial.mapRingHom (algebraMap SeedPoly SeedField)))
      (rawY0 D Crt) (rawY1 D Crt) (rawY2 D Crt)
  have hS_y1 : S (C Polynomial.X) = rawY1 D Crt := by
    simpa [S] using substitute2_y1
      (jetConstant2.comp (Polynomial.mapRingHom (algebraMap SeedPoly SeedField)))
      (rawY0 D Crt) (rawY1 D Crt) (rawY2 D Crt)
  have hS_y2 : S Polynomial.X = rawY2 D Crt := by
    simpa [S] using substitute2_y2
      (jetConstant2.comp (Polynomial.mapRingHom (algebraMap SeedPoly SeedField)))
      (rawY0 D Crt) (rawY1 D Crt) (rawY2 D Crt)
  rw [hS_base, hS_y0, hS_y1, hS_y2]
  have hfit : (((P.coeff e₂).coeff e₁).coeff e₀).natDegree + (2 * h + u) * e₀ +
      (2 * h + v) * e₁ + (2 * h + w) * e₂ ≤ W + (s.B + s.J) * (2 * h) := by
    have hu : 131071 + h = 2 * h + u := by dsimp [u]; omega
    have hv : 2 * h + u = (2 * h + v) + 1 := by dsimp [u, v]; omega
    have hw' : 2 * h + u = (2 * h + w) + 2 := by dsimp [u, w]; omega
    have hsplit : (e₀ + e₁ + e₂) * (131071 + h) =
        (2 * h + u) * e₀ + (2 * h + v) * e₁ + (2 * h + w) * e₂ + jetIdx e₁ e₂ := by
      unfold jetIdx
      rw [hu]
      have : (e₀ + e₁ + e₂) * (2 * h + u) =
          (2 * h + u) * e₀ + ((2 * h + v) + 1) * e₁ + ((2 * h + w) + 2) * e₂ := by
        rw [← hv, ← hw']; ring
      rw [this]; ring
    omega
  apply bounded2_mono (bounded2_mul (bounded2_mul (bounded2_mul
    (bounded2_jetConstant2 (natDegree_map_le)) (bounded2_pow hy0 e₀))
    (bounded2_pow hy1 e₁)) (bounded2_pow hy2 e₂))
  omega

private theorem quotient_positions2 {h : ℕ} {D : PoleData h} (s : Shape2) (W : ℕ)
    {P Q : RawSource2}
    (hb : Bounded2 (131071 - h) (131071 - h - 1) (131071 - h - 2) (W + (s.B + s.J) * (2 * h)) P)
    (hdiv : P = jetConstant2 ((rawBlock D) ^ (s.B + s.J)) * Q)
    (e₂ e₁ e₀ : ℕ)
    (hw : W < (131071 - h) * e₀ + (131071 - h - 1) * e₁ + (131071 - h - 2) * e₂) :
    (((Q.coeff e₂).coeff e₁).coeff e₀) = 0 := by
  by_contra hq
  have hm : ((rawBlock D) ^ (s.B + s.J)).Monic := (((D.monic 0).mul (D.monic 1)).map _).pow _
  have hc : (((P.coeff e₂).coeff e₁).coeff e₀) =
      (rawBlock D) ^ (s.B + s.J) * (((Q.coeff e₂).coeff e₁).coeff e₀) := by
    rw [hdiv]
    simp only [jetConstant2, RingHom.comp_apply, coeff_C_mul]
  have hne : (((P.coeff e₂).coeff e₁).coeff e₀) ≠ 0 := by
    rw [hc]; exact mul_ne_zero hm.ne_zero hq
  have hbd := hb e₂ e₁ e₀ hne
  rw [hc, hm.natDegree_mul' hq, natDegree_pow, K1_14_1_4.rawBlock_degree] at hbd
  omega

def rawPosition2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (e₂ e₁ e₀ : ℕ) :
    Jet2 →ₗ[FX] CentreField where
  toFun P := ((((specialized2 Crt P).coeff e₂).coeff e₁).coeff e₀)
  map_add' P Q := by simp
  map_smul' c P := by
    change ((((specialized2 Crt (c • P)).coeff e₂).coeff e₁).coeff e₀) = _
    rw [Algebra.smul_def, map_mul, AlgHom.commutes]
    change (((((jetConstant2 (algebraMap FX CentreField c)) * specialized2 Crt P).coeff e₂).coeff e₁).coeff e₀) = _
    simp [jetConstant2, Algebra.smul_def]

theorem rawPosition2_zero {h : ℕ} (hpos : 0 < h) (hh : h ≤ 131069) {D : PoleData h} (Crt : CRTLift D)
    (word : I → L) {s : Shape2} {W : ℕ} {P : Jet2} (hP : P ∈ evaluated2 Crt word s W)
    (e₂ e₁ e₀ : ℕ)
    (hw : W + jetIdx e₁ e₂ < (e₀ + e₁ + e₂) * (131071 - h)) :
    rawPosition2 Crt e₂ e₁ e₀ P = 0 := by
  have hw' : W < (131071 - h) * e₀ + (131071 - h - 1) * e₁ + (131071 - h - 2) * e₂ := by
    have hsplit : (e₀ + e₁ + e₂) * (131071 - h) =
        (131071 - h) * e₀ + (131071 - h - 1) * e₁ + (131071 - h - 2) * e₂ + jetIdx e₁ e₂ := by
      unfold jetIdx
      have h1 : 131071 - h = (131071 - h - 1) + 1 := by omega
      have h2 : 131071 - h = (131071 - h - 2) + 2 := by omega
      have : (e₀ + e₁ + e₂) * (131071 - h) =
          (131071 - h) * e₀ + ((131071 - h - 1) + 1) * e₁ + ((131071 - h - 2) + 2) * e₂ := by
        rw [← h1, ← h2]; ring
      rw [this]; ring
    omega
  have hsub : evaluated2 Crt word s W ≤ LinearMap.ker (rawPosition2 Crt e₂ e₁ e₀) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, hA, rfl⟩
    apply LinearMap.mem_ker.mpr
    obtain ⟨Q, hQ⟩ := hA.2
    have hQ' : forward2 (poleProduct D) (crtPolynomial Crt) A =
        jetConstant2 ((rawBlock D) ^ (s.B + s.J)) * Q := hQ
    have hz := quotient_positions2 s W (forward2_bounded hpos hh Crt hA.1.1) hQ' e₂ e₁ e₀ hw'
    change ((((specialized2 Crt (centerEval2 A)).coeff e₂).coeff e₁).coeff e₀) = 0
    rw [specialized2_center, hQ', tripleMap_coeff]
    simp only [jetConstant2, RingHom.comp_apply, coeff_C_mul, hz, mul_zero, map_zero]
  exact LinearMap.mem_ker.mp (hsub hP)

/-! ## 3. Graded Order `(e₁ + e₂, e₂, e₀)` and `leading_bound_2jet` -/

/-- Strict graded lexicographic order on `(e₂, e₁, e₀)` by `(e₁ + e₂, e₂, e₀)`. -/
def gradedLt (a b : ℕ × ℕ × ℕ) : Prop :=
  a.2.1 + a.1 < b.2.1 + b.1 ∨
    (a.2.1 + a.1 = b.2.1 + b.1 ∧ (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.2 < b.2.2)))

def gradedLe (a b : ℕ × ℕ × ℕ) : Prop := gradedLt a b ∨ a = b

theorem gradedLt_irrefl (a : ℕ × ℕ × ℕ) : ¬ gradedLt a a := by
  unfold gradedLt; omega

theorem gradedLt_trans {a b c : ℕ × ℕ × ℕ} (hab : gradedLt a b) (hbc : gradedLt b c) :
    gradedLt a c := by
  unfold gradedLt at *; omega

theorem gradedLe_total (a b : ℕ × ℕ × ℕ) : gradedLe a b ∨ gradedLe b a := by
  unfold gradedLe gradedLt
  rcases a with ⟨a2, a1, a0⟩; rcases b with ⟨b2, b1, b0⟩
  simp only [Prod.mk.injEq]
  omega

theorem gradedLe_add {a b c d : ℕ × ℕ × ℕ} (hab : gradedLe a b) (hcd : gradedLe c d) :
    gradedLe (a.1 + c.1, a.2.1 + c.2.1, a.2.2 + c.2.2) (b.1 + d.1, b.2.1 + d.2.1, b.2.2 + d.2.2) := by
  unfold gradedLe gradedLt at *
  rcases a with ⟨a2, a1, a0⟩; rcases b with ⟨b2, b1, b0⟩
  rcases c with ⟨c2, c1, c0⟩; rcases d with ⟨d2, d1, d0⟩
  simp only [Prod.mk.injEq] at *
  omega

theorem gradedLt_add_of_lt_le {a b c d : ℕ × ℕ × ℕ} (hab : gradedLt a b) (hcd : gradedLe c d) :
    gradedLt (a.1 + c.1, a.2.1 + c.2.1, a.2.2 + c.2.2) (b.1 + d.1, b.2.1 + d.2.1, b.2.2 + d.2.2) := by
  unfold gradedLe gradedLt at *
  rcases a with ⟨a2, a1, a0⟩; rcases b with ⟨b2, b1, b0⟩
  rcases c with ⟨c2, c1, c0⟩; rcases d with ⟨d2, d1, d0⟩
  simp only [Prod.mk.injEq] at *
  omega

theorem gradedLt_add_of_le_lt {a b c d : ℕ × ℕ × ℕ} (hab : gradedLe a b) (hcd : gradedLt c d) :
    gradedLt (a.1 + c.1, a.2.1 + c.2.1, a.2.2 + c.2.2) (b.1 + d.1, b.2.1 + d.2.1, b.2.2 + d.2.2) := by
  unfold gradedLe gradedLt at *
  rcases a with ⟨a2, a1, a0⟩; rcases b with ⟨b2, b1, b0⟩
  rcases c with ⟨c2, c1, c0⟩; rcases d with ⟨d2, d1, d0⟩
  simp only [Prod.mk.injEq] at *
  omega

/-- Every nonzero polynomial `P : R[Y₀][Y₁][Y₂]` over a ring `R` has a unique graded-maximal
    nonzero monomial `(e₂, e₁, e₀)` under `(e₁ + e₂, e₂, e₀)`. -/
def support3 {R : Type*} [Semiring R] [DecidableEq R] (P : Polynomial (Polynomial (Polynomial R))) :
    Finset (ℕ × ℕ × ℕ) :=
  P.support.biUnion fun e₂ =>
    (P.coeff e₂).support.biUnion fun e₁ =>
      ((P.coeff e₂).coeff e₁).support.image fun e₀ => (e₂, e₁, e₀)

theorem mem_support3 {R : Type*} [Semiring R] [DecidableEq R]
    (P : Polynomial (Polynomial (Polynomial R))) (m : ℕ × ℕ × ℕ) :
    m ∈ support3 P ↔ (((P.coeff m.1).coeff m.2.1).coeff m.2.2) ≠ 0 := by
  rcases m with ⟨e₂, e₁, e₀⟩
  simp only [support3, Finset.mem_biUnion, Finset.mem_image, Polynomial.mem_support_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨a₂, _, a₁, _, a₀, ha₀, rfl, rfl, rfl⟩; exact ha₀
  · intro hne
    refine ⟨e₂, ?_, e₁, ?_, e₀, hne, rfl, rfl, rfl⟩
    · intro hz; rw [hz, coeff_zero, coeff_zero] at hne; exact hne rfl
    · intro hz; rw [hz, coeff_zero] at hne; exact hne rfl

private theorem finset_graded_max {S : Finset (ℕ × ℕ × ℕ)} (hne : S.Nonempty) :
    ∃ m ∈ S, ∀ m' ∈ S, gradedLe m' m := by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, Finset.mem_singleton_self a, fun b hb => Or.inr (Finset.mem_singleton.mp hb)⟩
  | cons a s ha hs ih =>
    obtain ⟨m, hm, hmax⟩ := ih
    rcases gradedLe_total a m with ham | hma
    · refine ⟨m, Finset.mem_cons_of_mem hm, fun b hb => ?_⟩
      rcases Finset.mem_cons.mp hb with rfl | hbs
      · exact ham
      · exact hmax b hbs
    · refine ⟨a, Finset.mem_cons_self a s, fun b hb => ?_⟩
      rcases Finset.mem_cons.mp hb with rfl | hbs
      · exact Or.inr rfl
      · rcases hmax b hbs with hlt | rfl
        · rcases hma with hlt' | rfl
          · exact Or.inl (gradedLt_trans hlt hlt')
          · exact Or.inl hlt
        · exact hma

theorem exists_graded_max {R : Type*} [Semiring R] [DecidableEq R]
    {P : Polynomial (Polynomial (Polynomial R))} (hP : P ≠ 0) :
    ∃ m ∈ support3 P, ∀ m' ∈ support3 P, gradedLe m' m := by
  have hne : (support3 P).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hP
    apply Polynomial.ext; intro e₂
    apply Polynomial.ext; intro e₁
    apply Polynomial.ext; intro e₀
    simp only [coeff_zero]
    by_contra hnz
    have hmem : (e₂, e₁, e₀) ∈ support3 P := (mem_support3 P _).mpr hnz
    rw [hemp] at hmem
    exact Finset.notMem_empty _ hmem
  exact finset_graded_max hne

/-- Triangular property under `gradedLe`: `P` has all nonzero monomials `≤ m`, with exact coeff `c` at `m`. -/
def GradedTop {R : Type*} [Semiring R] (m : ℕ × ℕ × ℕ) (c : R)
    (P : Polynomial (Polynomial (Polynomial R))) : Prop :=
  (∀ m', (((P.coeff m'.1).coeff m'.2.1).coeff m'.2.2) ≠ 0 → gradedLe m' m) ∧
    (((P.coeff m.1).coeff m.2.1).coeff m.2.2) = c

private theorem gradedTop_mul {R : Type*} [CommSemiring R]
    {m₁ m₂ : ℕ × ℕ × ℕ} {c₁ c₂ : R} {P Q : Polynomial (Polynomial (Polynomial R))}
    (hP : GradedTop m₁ c₁ P) (hQ : GradedTop m₂ c₂ Q) :
    GradedTop (m₁.1 + m₂.1, m₁.2.1 + m₂.2.1, m₁.2.2 + m₂.2.2) (c₁ * c₂) (P * Q) := by
  have hterm : ∀ (p₂ q₂ p₁ q₁ p₀ q₀ : ℕ),
      (((P.coeff p₂).coeff p₁).coeff p₀) * (((Q.coeff q₂).coeff q₁).coeff q₀) ≠ 0 →
      gradedLe (p₂ + q₂, p₁ + q₁, p₀ + q₀) (m₁.1 + m₂.1, m₁.2.1 + m₂.2.1, m₁.2.2 + m₂.2.2) := by
    intro p₂ q₂ p₁ q₁ p₀ q₀ hne
    have hp := hP.1 (p₂, p₁, p₀) (left_ne_zero_of_mul hne)
    have hq := hQ.1 (q₂, q₁, q₀) (right_ne_zero_of_mul hne)
    exact gradedLe_add hp hq
  have huniq : ∀ (p₂ q₂ p₁ q₁ p₀ q₀ : ℕ),
      p₂ + q₂ = m₁.1 + m₂.1 → p₁ + q₁ = m₁.2.1 + m₂.2.1 → p₀ + q₀ = m₁.2.2 + m₂.2.2 →
      (((P.coeff p₂).coeff p₁).coeff p₀) * (((Q.coeff q₂).coeff q₁).coeff q₀) ≠ 0 →
      (p₂, p₁, p₀) = m₁ ∧ (q₂, q₁, q₀) = m₂ := by
    intro p₂ q₂ p₁ q₁ p₀ q₀ h2 h1 h0 hne
    have hp := hP.1 (p₂, p₁, p₀) (left_ne_zero_of_mul hne)
    have hq := hQ.1 (q₂, q₁, q₀) (right_ne_zero_of_mul hne)
    rcases hp with hplt | hpeq
    · exfalso
      have hlt := gradedLt_add_of_lt_le hplt hq
      rw [h2, h1, h0] at hlt
      exact gradedLt_irrefl _ hlt
    · rcases hq with hqlt | hqeq
      · exfalso
        have hlt := gradedLt_add_of_le_lt (Or.inr hpeq) hqlt
        rw [h2, h1, h0] at hlt
        exact gradedLt_irrefl _ hlt
      · exact ⟨hpeq, hqeq⟩
  constructor
  · rintro ⟨e₂, e₁, e₀⟩ hne
    rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff] at hne
    obtain ⟨⟨p₂, q₂⟩, h2, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff] at hne2
    obtain ⟨⟨p₁, q₁⟩, h1, hne1⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne2
    rw [Polynomial.coeff_mul] at hne1
    obtain ⟨⟨p₀, q₀⟩, h0, hne0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne1
    have h2e := Finset.mem_antidiagonal.mp h2
    have h1e := Finset.mem_antidiagonal.mp h1
    have h0e := Finset.mem_antidiagonal.mp h0
    subst h2e; subst h1e; subst h0e
    exact hterm p₂ q₂ p₁ q₁ p₀ q₀ hne0
  · rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single (m₁.1, m₂.1)]
    · rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single (m₁.2.1, m₂.2.1)]
      · rw [Polynomial.coeff_mul]
        rw [Finset.sum_eq_single (m₁.2.2, m₂.2.2)]
        · rw [hP.2, hQ.2]
        · rintro ⟨p₀, q₀⟩ h0 hne0
          by_contra hnz
          have ⟨hp, hq⟩ := huniq m₁.1 m₂.1 m₁.2.1 m₂.2.1 p₀ q₀ rfl rfl (Finset.mem_antidiagonal.mp h0) hnz
          exact hne0 (Prod.ext (congrArg (fun x : ℕ × ℕ × ℕ => x.2.2) hp) (congrArg (fun x : ℕ × ℕ × ℕ => x.2.2) hq))
        · intro hm; simp at hm
      · rintro ⟨p₁, q₁⟩ h1 hne1
        rw [Polynomial.coeff_mul]
        apply Finset.sum_eq_zero
        rintro ⟨p₀, q₀⟩ h0
        by_contra hnz
        have ⟨hp, hq⟩ := huniq m₁.1 m₂.1 p₁ q₁ p₀ q₀ rfl (Finset.mem_antidiagonal.mp h1) (Finset.mem_antidiagonal.mp h0) hnz
        exact hne1 (Prod.ext (congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) hp) (congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) hq))
      · intro hm; simp at hm
    · rintro ⟨p₂, q₂⟩ h2 hne2
      rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      rintro ⟨p₁, q₁⟩ h1
      rw [Polynomial.coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨p₀, q₀⟩ h0
      by_contra hnz
      have ⟨hp, hq⟩ := huniq p₂ q₂ p₁ q₁ p₀ q₀ (Finset.mem_antidiagonal.mp h2) (Finset.mem_antidiagonal.mp h1) (Finset.mem_antidiagonal.mp h0) hnz
      exact hne2 (Prod.ext (congrArg (fun x : ℕ × ℕ × ℕ => x.1) hp) (congrArg (fun x : ℕ × ℕ × ℕ => x.1) hq))
    · intro hm; simp at hm

private theorem gradedTop_pow {R : Type*} [CommSemiring R]
    {m : ℕ × ℕ × ℕ} {c : R} {P : Polynomial (Polynomial (Polynomial R))}
    (hP : GradedTop m c P) (n : ℕ) :
    GradedTop (n * m.1, n * m.2.1, n * m.2.2) (c ^ n) (P ^ n) := by
  induction n with
  | zero =>
    constructor
    · rintro ⟨e₂, e₁, e₀⟩ hne
      rw [pow_zero] at hne
      by_cases h2 : e₂ = 0
      · subst h2
        by_cases h1' : e₁ = 0
        · subst h1'
          by_cases h0 : e₀ = 0
          · subst h0; exact Or.inr (by simp)
          · exfalso; exact hne (by simp [coeff_one, h0])
        · exfalso; exact hne (by simp [coeff_one, h1'])
      · exfalso; exact hne (by simp [coeff_one, h2])
    · simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    have hm := gradedTop_mul ih hP
    have hidx : (n * m.1 + m.1, n * m.2.1 + m.2.1, n * m.2.2 + m.2.2) =
        ((n + 1) * m.1, (n + 1) * m.2.1, (n + 1) * m.2.2) := by
      simp only [Prod.mk.injEq]; exact ⟨by ring, by ring, by ring⟩
    rwa [hidx] at hm

private theorem gradedTop_const {R : Type*} [CommSemiring R] (c : R) :
    GradedTop (0, 0, 0) c (jetConstant2 c) := by
  constructor
  · rintro ⟨e₂, e₁, e₀⟩ hne
    by_cases h2 : e₂ = 0
    · subst h2
      by_cases h1 : e₁ = 0
      · subst h1
        by_cases h0 : e₀ = 0
        · subst h0; exact Or.inr rfl
        · exfalso; exact hne (by simp [jetConstant2, coeff_C, h0])
      · exfalso; exact hne (by simp [jetConstant2, coeff_C, h1])
    · exfalso; exact hne (by simp [jetConstant2, coeff_C, h2])
  · simp [jetConstant2]

private theorem gradedTop_add_lt {R : Type*} [Semiring R]
    {m₁ m₂ : ℕ × ℕ × ℕ} {c₁ c₂ : R} {P Q : Polynomial (Polynomial (Polynomial R))}
    (hP : GradedTop m₁ c₁ P) (hQ : GradedTop m₂ c₂ Q) (hlt : gradedLt m₂ m₁) :
    GradedTop m₁ c₁ (P + Q) := by
  constructor
  · intro m hne
    simp only [coeff_add] at hne
    by_cases hp : (((P.coeff m.1).coeff m.2.1).coeff m.2.2) = 0
    · rw [hp, zero_add] at hne
      rcases hQ.1 m hne with h | rfl
      · exact Or.inl (gradedLt_trans h hlt)
      · exact Or.inl hlt
    · exact hP.1 m hp
  · simp only [coeff_add, hP.2]
    have hq0 : (((Q.coeff m₁.1).coeff m₁.2.1).coeff m₁.2.2) = 0 := by
      by_contra hne
      rcases hQ.1 m₁ hne with h | h
      · exact gradedLt_irrefl _ (gradedLt_trans h hlt)
      · rw [h] at hlt; exact gradedLt_irrefl _ hlt
    rw [hq0, add_zero]

private theorem gradedTop_spec_y0 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) :
    GradedTop (0, 0, 1) (evalRaw (rawBlock D)) (tripleMap evalRaw (rawY0 D Crt)) := by
  have h1 : tripleMap evalRaw (rawY0 D Crt) =
      jetConstant2 (evalRaw (rawBlock D)) * C (C Polynomial.X) +
      jetConstant2 (evalRaw (crtPolynomial Crt)) := by
    simp [rawY0, tripleMap, jetConstant2]
  rw [h1]
  have hy : GradedTop (0, 0, 1) (1 : CentreField) (C (C Polynomial.X)) := by
    constructor
    · rintro ⟨e₂, e₁, e₀⟩ hne
      rw [coeff_C] at hne; split_ifs at hne with h2
      · subst h2; rw [coeff_C] at hne; split_ifs at hne with h1'
        · subst h1'; rw [coeff_X] at hne; split_ifs at hne with h0
          · subst h0; exact Or.inr rfl
          · exact absurd rfl hne
        · exact absurd rfl hne
      · exact absurd rfl hne
    · simp
  have hm := gradedTop_mul (gradedTop_const (evalRaw (rawBlock D))) hy
  simp only [zero_add, mul_one] at hm
  exact gradedTop_add_lt hm (gradedTop_const _) (by dsimp only [gradedLt]; omega)

private theorem gradedTop_spec_y1 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) :
    GradedTop (0, 1, 0) (evalRaw (rawBlock D)) (tripleMap evalRaw (rawY1 D Crt)) := by
  have h1 : tripleMap evalRaw (rawY1 D Crt) =
      jetConstant2 (evalRaw (rawBlock D)) * C Polynomial.X +
      jetConstant2 (evalRaw (rawBlock D).derivative) * C (C Polynomial.X) +
      jetConstant2 (evalRaw (crtPolynomial Crt).derivative) := by
    simp [rawY1, tripleMap, jetConstant2]
  rw [h1]
  have hy1 : GradedTop (0, 1, 0) (1 : CentreField) (C Polynomial.X) := by
    constructor
    · rintro ⟨e₂, e₁, e₀⟩ hne
      rw [coeff_C] at hne; split_ifs at hne with h2
      · subst h2; rw [coeff_X] at hne; split_ifs at hne with h1'
        · subst h1'; rw [show (1 : Polynomial CentreField) = C 1 from rfl, coeff_C] at hne
          split_ifs at hne with h0
          · subst h0; exact Or.inr rfl
          · exact absurd rfl hne
        · exact absurd rfl hne
      · exact absurd rfl hne
    · simp
  have hy0 : GradedTop (0, 0, 1) (1 : CentreField) (C (C Polynomial.X)) := by
    constructor
    · rintro ⟨e₂, e₁, e₀⟩ hne
      rw [coeff_C] at hne; split_ifs at hne with h2
      · subst h2; rw [coeff_C] at hne; split_ifs at hne with h1'
        · subst h1'; rw [coeff_X] at hne; split_ifs at hne with h0
          · subst h0; exact Or.inr rfl
          · exact absurd rfl hne
        · exact absurd rfl hne
      · exact absurd rfl hne
    · simp
  have hm1 := gradedTop_mul (gradedTop_const (evalRaw (rawBlock D))) hy1
  have hm0 := gradedTop_mul (gradedTop_const (evalRaw (rawBlock D).derivative)) hy0
  simp only [zero_add, mul_one] at hm1 hm0
  exact gradedTop_add_lt (gradedTop_add_lt hm1 hm0 (by dsimp only [gradedLt]; omega))
    (gradedTop_const _) (by dsimp only [gradedLt]; omega)

private theorem gradedTop_spec_y2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) :
    GradedTop (1, 0, 0) (evalRaw (rawBlock D)) (tripleMap evalRaw (rawY2 D Crt)) := by
  have h1 : tripleMap evalRaw (rawY2 D Crt) =
      jetConstant2 (evalRaw (rawBlock D)) * Polynomial.X +
      jetConstant2 (evalRaw (rawBlock D).derivative) * C Polynomial.X +
      jetConstant2 (evalRaw (hasseDeriv 2 (rawBlock D))) * C (C Polynomial.X) +
      jetConstant2 (evalRaw (hasseDeriv 2 (crtPolynomial Crt))) := by
    simp [rawY2, tripleMap, jetConstant2]
  rw [h1]
  have hy2 : GradedTop (1, 0, 0) (1 : CentreField) Polynomial.X := by
    constructor
    · rintro ⟨e₂, e₁, e₀⟩ hne
      rw [coeff_X] at hne; split_ifs at hne with h2
      · subst h2; rw [show (1 : Polynomial (Polynomial CentreField)) = C (C 1) from by simp, coeff_C] at hne
        split_ifs at hne with h1'
        · subst h1'; rw [coeff_C] at hne; split_ifs at hne with h0
          · subst h0; exact Or.inr rfl
          · exact absurd rfl hne
        · exact absurd rfl hne
      · exact absurd rfl hne
    · simp
  have hy1 : GradedTop (0, 1, 0) (1 : CentreField) (C Polynomial.X) := by
    constructor
    · rintro ⟨e₂, e₁, e₀⟩ hne
      rw [coeff_C] at hne; split_ifs at hne with h2
      · subst h2; rw [coeff_X] at hne; split_ifs at hne with h1'
        · subst h1'; rw [show (1 : Polynomial CentreField) = C 1 from rfl, coeff_C] at hne
          split_ifs at hne with h0
          · subst h0; exact Or.inr rfl
          · exact absurd rfl hne
        · exact absurd rfl hne
      · exact absurd rfl hne
    · simp
  have hy0 : GradedTop (0, 0, 1) (1 : CentreField) (C (C Polynomial.X)) := by
    constructor
    · rintro ⟨e₂, e₁, e₀⟩ hne
      rw [coeff_C] at hne; split_ifs at hne with h2
      · subst h2; rw [coeff_C] at hne; split_ifs at hne with h1'
        · subst h1'; rw [coeff_X] at hne; split_ifs at hne with h0
          · subst h0; exact Or.inr rfl
          · exact absurd rfl hne
        · exact absurd rfl hne
      · exact absurd rfl hne
    · simp
  have hm2 := gradedTop_mul (gradedTop_const (evalRaw (rawBlock D))) hy2
  have hm1 := gradedTop_mul (gradedTop_const (evalRaw (rawBlock D).derivative)) hy1
  have hm0 := gradedTop_mul (gradedTop_const (evalRaw (hasseDeriv 2 (rawBlock D)))) hy0
  simp only [zero_add, mul_one] at hm2 hm1 hm0
  exact gradedTop_add_lt
    (gradedTop_add_lt (gradedTop_add_lt hm2 hm1 (by dsimp only [gradedLt]; omega))
      hm0 (by dsimp only [gradedLt]; omega))
    (gradedTop_const _) (by dsimp only [gradedLt]; omega)

private theorem specialized2_monomial_top {h : ℕ} {D : PoleData h} (Crt : CRTLift D)
    (e₂ e₁ e₀ : ℕ) (c : Seeds) :
    GradedTop (e₂, e₁, e₀)
      (algebraMap Seeds CentreField c * (evalRaw (rawBlock D)) ^ (e₀ + e₁ + e₂))
      (specialized2 Crt (jetConstant2 c * C (C Polynomial.X) ^ e₀ * C Polynomial.X ^ e₁ * Polynomial.X ^ e₂)) := by
  simp only [map_mul, map_pow]
  have hc : specialized2 Crt (jetConstant2 c) = jetConstant2 (algebraMap Seeds CentreField c) := by
    change substitute2 _ _ _ _ (jetConstant2 c) = _
    simp [substitute2, jetConstant2]
  have hy0 : specialized2 Crt (C (C Polynomial.X)) = tripleMap evalRaw (rawY0 D Crt) := by
    change substitute2 _ _ _ _ (C (C Polynomial.X)) = _
    exact substitute2_y0 _ _ _ _
  have hy1 : specialized2 Crt (C Polynomial.X) = tripleMap evalRaw (rawY1 D Crt) := by
    change substitute2 _ _ _ _ (C Polynomial.X) = _
    exact substitute2_y1 _ _ _ _
  have hy2 : specialized2 Crt Polynomial.X = tripleMap evalRaw (rawY2 D Crt) := by
    change substitute2 _ _ _ _ Polynomial.X = _
    exact substitute2_y2 _ _ _ _
  rw [hc, hy0, hy1, hy2]
  have h0 := gradedTop_pow (gradedTop_spec_y0 Crt) e₀
  have h1 := gradedTop_pow (gradedTop_spec_y1 Crt) e₁
  have h2 := gradedTop_pow (gradedTop_spec_y2 Crt) e₂
  have hm := gradedTop_mul (gradedTop_mul (gradedTop_mul (gradedTop_const (algebraMap Seeds CentreField c)) h0) h1) h2
  simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero] at hm
  have hcEq : algebraMap Seeds CentreField c * evalRaw (rawBlock D) ^ e₀ * evalRaw (rawBlock D) ^ e₁ *
      evalRaw (rawBlock D) ^ e₂ =
      algebraMap Seeds CentreField c * evalRaw (rawBlock D) ^ (e₀ + e₁ + e₂) := by
    rw [pow_add, pow_add]; ring
  rwa [hcEq] at hm

private theorem jet2_as_sum_support3 (P : Jet2) :
    P = ∑ m ∈ support3 P,
      jetConstant2 (((P.coeff m.1).coeff m.2.1).coeff m.2.2) *
        C (C Polynomial.X) ^ m.2.2 * C Polynomial.X ^ m.2.1 * Polynomial.X ^ m.1 := by
  apply Polynomial.ext; intro e₂
  apply Polynomial.ext; intro e₁
  apply Polynomial.ext; intro e₀
  rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  have hterm (m : ℕ × ℕ × ℕ) :
      ((((jetConstant2 (((P.coeff m.1).coeff m.2.1).coeff m.2.2) *
        C (C Polynomial.X) ^ m.2.2 * C Polynomial.X ^ m.2.1 * Polynomial.X ^ m.1 : Jet2).coeff e₂).coeff e₁).coeff e₀) =
      if m = (e₂, e₁, e₀) then (((P.coeff e₂).coeff e₁).coeff e₀) else 0 := by
    rcases m with ⟨m₂, m₁, m₀⟩
    have hmul : (jetConstant2 (((P.coeff m₂).coeff m₁).coeff m₀) *
        C (C Polynomial.X) ^ m₀ * C Polynomial.X ^ m₁ * Polynomial.X ^ m₂ : Jet2) =
        C (C (C (((P.coeff m₂).coeff m₁).coeff m₀) * Polynomial.X ^ m₀) * Polynomial.X ^ m₁) * Polynomial.X ^ m₂ := by
      simp only [jetConstant2, RingHom.comp_apply, ← Polynomial.C_pow, ← Polynomial.C_mul]
    rw [hmul]
    simp only [coeff_mul_X_pow', Prod.mk.injEq]
    by_cases h2 : m₂ = e₂
    · subst h2
      simp only [le_refl, Nat.sub_self, ite_true, true_and, coeff_C_zero, coeff_mul_X_pow']
      by_cases h1 : m₁ = e₁
      · subst h1
        simp only [le_refl, Nat.sub_self, ite_true, true_and, coeff_C_zero, coeff_mul_X_pow']
        by_cases h0 : m₀ = e₀
        · subst h0; simp
        · simp only [h0, ite_false]
          split_ifs with hle
          · have hne : e₀ - m₀ ≠ 0 := by omega
            simp [coeff_C, hne]
          · rfl
      · simp only [h1, false_and, ite_false]
        split_ifs with hle
        · have hne : e₁ - m₁ ≠ 0 := by omega
          rw [coeff_C, if_neg hne, coeff_zero]
        · simp
    · simp only [h2, false_and, ite_false]
      split_ifs with hle
      · have hne : e₂ - m₂ ≠ 0 := by omega
        rw [coeff_C, if_neg hne, coeff_zero, coeff_zero]
      · simp
  simp_rw [hterm]
  by_cases hmem : (e₂, e₁, e₀) ∈ support3 P
  · rw [Finset.sum_eq_single (e₂, e₁, e₀)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hmem h
  · rw [Finset.sum_eq_zero]
    · by_contra hnz; exact hmem ((mem_support3 P _).mpr hnz)
    · intro b hb; simp [show b ≠ (e₂, e₁, e₀) from fun heq => hmem (heq ▸ hb)]

theorem specialized2_graded_leading {h : ℕ} {D : PoleData h} (Crt : CRTLift D)
    {P : Jet2} {m : ℕ × ℕ × ℕ} (hm : m ∈ support3 P)
    (hmax : ∀ m' ∈ support3 P, gradedLe m' m) :
    rawPosition2 Crt m.1 m.2.1 m.2.2 P ≠ 0 := by
  have hP := jet2_as_sum_support3 P
  conv_lhs => rw [hP, map_sum]
  rw [Finset.sum_eq_single m]
  · have htop := specialized2_monomial_top Crt m.1 m.2.1 m.2.2 (((P.coeff m.1).coeff m.2.1).coeff m.2.2)
    change ((((specialized2 Crt _).coeff m.1).coeff m.2.1).coeff m.2.2) ≠ 0
    rw [htop.2]
    have hcne : (((P.coeff m.1).coeff m.2.1).coeff m.2.2) ≠ 0 := (mem_support3 P m).mp hm
    have hmapne : algebraMap Seeds CentreField (((P.coeff m.1).coeff m.2.1).coeff m.2.2) ≠ 0 :=
      fun hz => hcne (IsFractionRing.injective Seeds CentreField (hz.trans (map_zero _).symm))
    exact mul_ne_zero hmapne (pow_ne_zero _ (evalRaw_block_ne_zero D))
  · intro m' hm' hne
    have hlt : gradedLt m' m := (hmax m' hm').resolve_right hne
    have htop := specialized2_monomial_top Crt m'.1 m'.2.1 m'.2.2 (((P.coeff m'.1).coeff m'.2.1).coeff m'.2.2)
    change ((((specialized2 Crt _).coeff m.1).coeff m.2.1).coeff m.2.2) = 0
    by_contra hnz
    rcases htop.1 m hnz with h | h
    · exact gradedLt_irrefl _ (gradedLt_trans h hlt)
    · rw [h] at hlt; exact gradedLt_irrefl _ hlt
  · intro hnot; exact absurd hm hnot

/-- **2-Jet Graded Leading Bound (`leading_bound_2jet`)**:
    For every nonzero `P ∈ evaluated2 Crt word s W`, its graded-maximal monomial `(e₂*, e₁*, e₀*)`
    satisfies `(e₀* + e₁* + e₂*) * (131071 - h) ≤ W + (e₁* + 2 * e₂*)`. -/
theorem leading_bound_2jet {h : ℕ} (hpos : 0 < h) (hh : h ≤ 131069) {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) (s : Shape2) (W : ℕ) {P : Jet2}
    (hP : P ∈ evaluated2 Crt word s W) {m : ℕ × ℕ × ℕ} (hm : m ∈ support3 P)
    (hmax : ∀ m' ∈ support3 P, gradedLe m' m) :
    (m.2.2 + m.2.1 + m.1) * (131071 - h) ≤ W + jetIdx m.2.1 m.1 := by
  by_contra! hlt
  have h0 := rawPosition2_zero hpos hh Crt word hP m.1 m.2.1 m.2.2 hlt
  exact specialized2_graded_leading Crt hm hmax h0

/-! ## 4. 2-Jet `FX`-Telescoping (`telescope2`) -/

abbrev Position2 := ℕ × ℕ × ℕ × (Fin 2 →₀ ℕ)

def mvCoeffPoly (e : Fin 2 →₀ ℕ) (f : Polynomial SeedPoly) : Polynomial L :=
  ∑ a ∈ f.support, Polynomial.monomial a ((f.coeff a).coeff e)

theorem mvCoeffPoly_coeff (e : Fin 2 →₀ ℕ) (f : Polynomial SeedPoly) (a : ℕ) :
    (mvCoeffPoly e f).coeff a = (f.coeff a).coeff e := by
  unfold mvCoeffPoly
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_monomial]
  by_cases ha : a ∈ f.support
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd ha h
  · rw [Finset.sum_eq_zero]
    · simp [Polynomial.notMem_support_iff.mp ha]
    · intro b hb; simp [show b ≠ a from fun heq => ha (heq ▸ hb)]

private theorem mvCoeffPoly_add (e : Fin 2 →₀ ℕ) (p q : Polynomial SeedPoly) :
    mvCoeffPoly e (p + q) = mvCoeffPoly e p + mvCoeffPoly e q := by
  ext a
  simp [mvCoeffPoly_coeff]

private theorem mvCoeffPoly_monomial (e : Fin 2 →₀ ℕ) (n : ℕ) (a : SeedPoly) :
    mvCoeffPoly e (Polynomial.monomial n a) = Polynomial.monomial n (a.coeff e) := by
  ext k
  rw [mvCoeffPoly_coeff, Polynomial.coeff_monomial, Polynomial.coeff_monomial]
  by_cases h : n = k
  · subst h; simp
  · simp [h]

def sourceCoord2 (P : Source2) (t : Position2) : Polynomial L :=
  mvCoeffPoly t.2.2.2 (((P.coeff t.1).coeff t.2.1).coeff t.2.2.1)

theorem sourceCoord2_coeff (P : Source2) (t : Position2) (a : ℕ) :
    (sourceCoord2 P t).coeff a = coeffAt2 P t.1 t.2.1 t.2.2.1 a t.2.2.2 := by
  rw [sourceCoord2, mvCoeffPoly_coeff]; rfl

def jetCoords2 : Jet2 →ₗ[FX] (Position2 → FX) where
  toFun P t := (((P.coeff t.1).coeff t.2.1).coeff t.2.2.1).coeff t.2.2.2
  map_add' P Q := by funext t; simp
  map_smul' c P := by
    funext t
    change ((((c • P).coeff t.1).coeff t.2.1).coeff t.2.2.1).coeff t.2.2.2 = _
    rw [Algebra.smul_def]
    change (((((jetConstant2 (MvPolynomial.C c)) * P).coeff t.1).coeff t.2.1).coeff t.2.2.1).coeff t.2.2.2 = _
    simp [jetConstant2, MvPolynomial.coeff_C_mul]

private theorem eval2_centerBase_coeff (f : Polynomial SeedPoly) (e : Fin 2 →₀ ℕ) :
    (centerBase f).coeff e =
      algebraMap (Polynomial L) FX (mvCoeffPoly e f) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, MvPolynomial.coeff_add, hp, hq, mvCoeffPoly_add, map_add]
  | monomial n a =>
    have h1 : centerBase (Polynomial.monomial n a) = MvPolynomial.C (ξ ^ n) * seedMap a := by
      simp [centerBase, Polynomial.eval₂_monomial, mul_comm]
    rw [h1, MvPolynomial.coeff_C_mul, seedMap, MvPolynomial.coeff_map,
      mvCoeffPoly_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    change ξ ^ n * algebraMap L FX (a.coeff e) = algebraMap (Polynomial L) FX (C (a.coeff e)) * ξ ^ n
    rw [mul_comm]; rfl

theorem coords2_center (P : Source2) (t : Position2) :
    jetCoords2 (centerEval2 P) t = algebraMap (Polynomial L) FX (sourceCoord2 P t) := by
  change ((((tripleMap centerBase P).coeff t.1).coeff t.2.1).coeff t.2.2.1).coeff t.2.2.2 = _
  rw [tripleMap_coeff]
  exact eval2_centerBase_coeff _ _

def boundaryDegree2 (h : ℕ) (s : Shape2) (W : ℕ) (t : Position2) : ℕ :=
  W + (s.B + s.J) * (2 * h) + jetIdx t.2.1 t.1 - (t.2.2.1 + t.2.1 + t.1) * (131071 + h)

def coeffLin2 (e₂ e₁ e₀ a : ℕ) (e : Fin 2 →₀ ℕ) : Source2 →ₗ[L] L where
  toFun P := coeffAt2 P e₂ e₁ e₀ a e
  map_add' P Q := by simp [coeffAt2, sourceCoeff2]
  map_smul' c P := by simp [coeffAt2, sourceCoeff2, Polynomial.coeff_smul]

def boundaryMap2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape2) (W : ℕ) : complete2 Crt word s W →ₗ[L] (Position2 → L) :=
  LinearMap.pi fun t =>
    (coeffLin2 t.1 t.2.1 t.2.2.1 (boundaryDegree2 h s W t) t.2.2.2).comp (complete2 Crt word s W).subtype

private theorem complete2_finite {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape2) (W : ℕ) : Module.Finite L (complete2 Crt word s W) := by
  letI := PoleBound2Jet.contacted2_finite h word s W
  exact Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)

private theorem evaluated2_finite {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape2) (W : ℕ) : Module.Finite FX (evaluated2 Crt word s W) := by
  letI := complete2_finite Crt word s W
  have hfg : ((complete2 Crt word s W).map centerEval2.toLinearMap).FG :=
    (Module.Finite.iff_fg.mp inferInstance).map _
  change Module.Finite FX (Submodule.span FX (centerEval2 '' (complete2 Crt word s W : Set Source2)))
  have heq : (centerEval2 '' (complete2 Crt word s W : Set Source2)) =
      (((complete2 Crt word s W).map centerEval2.toLinearMap : Submodule L Jet2) : Set Jet2) := rfl
  rw [heq]
  obtain ⟨S, hS⟩ := hfg
  apply Module.Finite.of_fg
  refine ⟨S, le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)⟩
  · intro x hx
    exact Submodule.subset_span (hS ▸ Submodule.subset_span hx)
  · intro x hx
    have hx' : x ∈ Submodule.span L (S : Set Jet2) := hS.symm ▸ hx
    exact Submodule.span_le_restrictScalars L FX (S : Set Jet2) hx'

private theorem sourceCoord2_degree {h : ℕ} {D : PoleData h} {Crt : CRTLift D} {word : I → L}
    {s : Shape2} {W : ℕ} (P : complete2 Crt word s W) (t : Position2) :
    (sourceCoord2 (P : Source2) t).natDegree ≤ boundaryDegree2 h s W t := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro a ha
  rw [sourceCoord2_coeff]
  apply P.property.1.1
  intro he
  have hw := he.2.2.2.2
  unfold boundaryDegree2 at ha
  omega

private theorem boundary_rank_le2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape2) (W : ℕ) :
    Module.finrank L (LinearMap.range (boundaryMap2 Crt word s W)) ≤
      Module.finrank FX (evaluated2 Crt word s W) := by
  letI := complete2_finite Crt word s W
  letI := evaluated2_finite Crt word s W
  let F := boundaryMap2 Crt word s W
  letI : Module.Finite L (LinearMap.range F) := Module.Finite.range F
  let b := Module.finBasis L (LinearMap.range F)
  have hex (k : Fin (Module.finrank L (LinearMap.range F))) :
      ∃ P : complete2 Crt word s W, F P = (b k : Position2 → L) := (b k).property
  choose P hP using hex
  have hli : LinearIndependent L (fun k t =>
      (sourceCoord2 (P k : Source2) t).coeff (boundaryDegree2 h s W t)) := by
    have heq : (fun k t => (sourceCoord2 (P k : Source2) t).coeff (boundaryDegree2 h s W t)) =
        fun k => ((b k : LinearMap.range F) : Position2 → L) := by
      funext k t
      rw [sourceCoord2_coeff]
      exact congrFun (hP k) t
    rw [heq]
    exact b.linearIndependent.map' (LinearMap.range F).subtype (LinearMap.range F).ker_subtype
  have heval : LinearIndependent FX (fun k => centerEval2 (P k : Source2)) := by
    apply LinearIndependent.of_comp jetCoords2
    have hf : jetCoords2 ∘ (fun k => centerEval2 (P k : Source2)) =
        fun k t => algebraMap (Polynomial L) FX (sourceCoord2 (P k : Source2) t) :=
      funext fun k => funext fun t => coords2_center (P k : Source2) t
    rw [hf]
    exact K1_14_1_8.independent_at_fraction (fun k t => sourceCoord2 (P k : Source2) t)
      (boundaryDegree2 h s W) (fun k t => sourceCoord2_degree (P k) t) hli
  have hmem (k : Fin (Module.finrank L (LinearMap.range F))) :
      centerEval2 (P k : Source2) ∈ evaluated2 Crt word s W :=
    Submodule.subset_span ⟨(P k : Source2), (P k).property, rfl⟩
  let v : Fin (Module.finrank L (LinearMap.range F)) → evaluated2 Crt word s W :=
    fun k => ⟨centerEval2 (P k : Source2), hmem k⟩
  have hv : LinearIndependent FX v :=
    LinearIndependent.of_comp (evaluated2 Crt word s W).subtype heval
  simpa [Fintype.card_fin] using hv.fintype_card_le_finrank

private theorem ker_step_le2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape2) (W : ℕ) :
    Module.finrank L (LinearMap.ker (boundaryMap2 Crt word s (W + 1))) ≤
      Module.finrank L (complete2 Crt word s W) := by
  letI := complete2_finite Crt word s (W + 1)
  letI := complete2_finite Crt word s W
  let f : LinearMap.ker (boundaryMap2 Crt word s (W + 1)) →ₗ[L] complete2 Crt word s W :=
    { toFun := fun P => ⟨P.1.1, ⟨⟨fun e₂ e₁ e₀ a e hnot => by
        by_cases h1 : trueEligible2 h s (W + 1) e₂ e₁ e₀ a e
        · have heq : a = boundaryDegree2 h s (W + 1) (e₂, e₁, e₀, e) := by
            obtain ⟨hB, hJ, hC, hU, hW1⟩ := h1
            unfold trueEligible2 at hnot
            dsimp only [boundaryDegree2]
            have : ¬ a + (e₀ + e₁ + e₂) * (131071 + h) ≤ W + (s.B + s.J) * (2 * h) + jetIdx e₁ e₂ :=
              fun hok => hnot ⟨hB, hJ, hC, hU, hok⟩
            omega
          rw [heq]
          exact congrFun (LinearMap.mem_ker.mp P.property) (e₂, e₁, e₀, e)
        · exact P.1.2.1.1 e₂ e₁ e₀ a e h1, P.1.2.1.2⟩, P.1.2.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective f := fun P Q hPQ => by
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (fun x : complete2 Crt word s W => x.1) hPQ
  exact LinearMap.finrank_le_finrank_of_injective hinj

private theorem ker_zero2 {h : ℕ} (hpos : 0 < h) (hh : h ≤ 131068) {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) (s : Shape2) :
    LinearMap.ker (boundaryMap2 Crt word s 0) = ⊥ := by
  apply bot_unique
  intro P hP
  rw [Submodule.mem_bot]
  apply Subtype.ext
  change (P : Source2) = 0
  by_contra hnz
  -- Show centerEval2 P ≠ 0 via coords2_center!
  have hcnz : centerEval2 (P : Source2) ≠ 0 := by
    intro hz
    apply hnz
    apply Polynomial.ext; intro e₂
    apply Polynomial.ext; intro e₁
    apply Polynomial.ext; intro e₀
    apply Polynomial.ext; intro a
    apply MvPolynomial.ext; intro e
    simp only [Polynomial.coeff_zero, MvPolynomial.coeff_zero]
    have h0 := congrArg (fun Q => jetCoords2 Q (e₂, e₁, e₀, e)) hz
    rw [map_zero, Pi.zero_apply, coords2_center] at h0
    have hsc : sourceCoord2 (P : Source2) (e₂, e₁, e₀, e) = 0 :=
      IsFractionRing.injective (Polynomial L) FX (h0.trans (map_zero _).symm)
    have ha := congrArg (fun q : Polynomial L => q.coeff a) hsc
    rw [sourceCoord2_coeff, coeff_zero] at ha
    exact ha
  obtain ⟨m, hm, hmax⟩ := exists_graded_max hcnz
  have hmem : centerEval2 (P : Source2) ∈ evaluated2 Crt word s 0 :=
    Submodule.subset_span ⟨(P : Source2), P.property, rfl⟩
  have hbd := leading_bound_2jet hpos (by omega) Crt word s 0 hmem hm hmax
  -- From hbd: (e0+e1+e2)*(131071 - h) <= e1 + 2*e2 <= 2*(e0+e1+e2), forcing e0=e1=e2=0!
  have hq0 : m.2.2 + m.2.1 + m.1 = 0 := by
    have hmul : (m.2.2 + m.2.1 + m.1) * 3 ≤ (m.2.2 + m.2.1 + m.1) * (131071 - h) :=
      Nat.mul_le_mul_left _ (by omega)
    unfold jetIdx at hbd; omega
  have hm0 : m = (0, 0, 0) := by
    rcases m with ⟨m2, m1, m0⟩; dsimp only at hq0; simp only [Prod.mk.injEq]; omega
  -- So P has nonzero (0, 0, 0) coefficient g with deg(g) < (B+J)*2h (since P ∈ ker boundaryMap2 0),
  -- contradicting H^(B+J) ∣ forward2 P at (0, 0, 0)!
  have hg_ne : (((P : Source2).coeff 0).coeff 0).coeff 0 ≠ 0 := by
    intro hg0
    have h0 := (mem_support3 (centerEval2 (P : Source2)) m).mp hm
    rw [hm0, centerEval2_eq_tripleMap, tripleMap_coeff, hg0, map_zero] at h0
    exact h0 rfl
  obtain ⟨Q, hQ⟩ := P.property.2
  have hfwd : forward2 (poleProduct D) (crtPolynomial Crt) (P : Source2) =
      jetConstant2 ((rawBlock D) ^ (s.B + s.J)) * Q := hQ
  -- Also P has NO nonzero monomials other than (0, 0, 0), so forward2 P = jetConstant2(genericCoefficients g)!
  have honly : ∀ m', (((P : Source2).coeff m'.1).coeff m'.2.1).coeff m'.2.2 ≠ 0 → m' = (0, 0, 0) := by
    intro m' hne'
    have hcm : m' ∈ support3 (centerEval2 (P : Source2)) := by
      rw [mem_support3, centerEval2_eq_tripleMap, tripleMap_coeff]
      intro hz
      apply hne'
      apply Polynomial.ext; intro a
      apply MvPolynomial.ext; intro e
      simp only [Polynomial.coeff_zero, MvPolynomial.coeff_zero]
      have hce := congrArg (fun q : Seeds => q.coeff e) hz
      rw [MvPolynomial.coeff_zero, eval2_centerBase_coeff] at hce
      have hsc : mvCoeffPoly e ((((P : Source2).coeff m'.1).coeff m'.2.1).coeff m'.2.2) = 0 :=
        IsFractionRing.injective (Polynomial L) FX (hce.trans (map_zero _).symm)
      have ha := congrArg (fun q : Polynomial L => q.coeff a) hsc
      rw [mvCoeffPoly_coeff, coeff_zero] at ha
      exact ha
    have hle := hmax m' hcm
    rw [hm0] at hle
    rcases m' with ⟨a2, a1, a0⟩
    unfold gradedLe gradedLt at hle
    simp only [Prod.mk.injEq] at hle ⊢
    omega
  have hPeq : (P : Source2) = jetConstant2 ((((P : Source2).coeff 0).coeff 0).coeff 0) := by
    apply Polynomial.ext; intro e₂
    apply Polynomial.ext; intro e₁
    apply Polynomial.ext; intro e₀
    by_cases h00 : (e₂, e₁, e₀) = (0, 0, 0)
    · rcases Prod.mk.inj h00 with ⟨rfl, h01⟩
      rcases Prod.mk.inj h01 with ⟨rfl, rfl⟩
      simp [jetConstant2]
    · have hzero : (((P : Source2).coeff e₂).coeff e₁).coeff e₀ = 0 := by
        by_contra hne'; exact h00 (honly _ hne')
      rw [hzero]
      by_cases h2 : e₂ = 0
      · subst h2
        by_cases h1 : e₁ = 0
        · subst h1
          by_cases h0 : e₀ = 0
          · subst h0; exact absurd rfl h00
          · simp [jetConstant2, coeff_C, h0]
        · simp [jetConstant2, coeff_C, h1]
      · simp [jetConstant2, coeff_C, h2]
  have hdiv : (rawBlock D) ^ (s.B + s.J) ∣
      ((((P : Source2).coeff 0).coeff 0).coeff 0).map (algebraMap SeedPoly SeedField) := by
    refine ⟨(((Q.coeff 0).coeff 0).coeff 0), ?_⟩
    have hc := congrArg (fun R : RawSource2 => (((R.coeff 0).coeff 0).coeff 0)) hfwd
    rw [hPeq] at hc
    change ((((forward2 (poleProduct D) (crtPolynomial Crt)).toRingHom
      (jetConstant2 ((((P : Source2).coeff 0).coeff 0).coeff 0))).coeff 0).coeff 0).coeff 0 = _ at hc
    rw [forward2_as_substitute, substitute2_base] at hc
    simpa only [jetConstant2, RingHom.comp_apply, Polynomial.coe_mapRingHom, coeff_C_mul,
      coeff_C_zero] using hc
  have hinj : Function.Injective (algebraMap SeedPoly SeedField) :=
    IsFractionRing.injective SeedPoly SeedField
  have hgmap_ne : ((((P : Source2).coeff 0).coeff 0).coeff 0).map (algebraMap SeedPoly SeedField) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hinj).mpr hg_ne
  have hdeg_ge : (s.B + s.J) * (2 * h) ≤ ((((P : Source2).coeff 0).coeff 0).coeff 0).natDegree := by
    have hd := Polynomial.natDegree_le_of_dvd hdiv hgmap_ne
    rw [Polynomial.natDegree_map_eq_of_injective hinj, natDegree_pow, K1_14_1_4.rawBlock_degree] at hd
    exact hd
  -- Yet P ∈ ker(boundaryMap2 0) forces natDegree < (s.B + s.J) * (2 * h)!
  have hlead : ((((P : Source2).coeff 0).coeff 0).coeff 0).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg_ne
  obtain ⟨e, he⟩ : ∃ e, ((((P : Source2).coeff 0).coeff 0).coeff 0).leadingCoeff.coeff e ≠ 0 := by
    by_contra! hall; exact hlead (MvPolynomial.eq_zero_iff.mpr hall)
  have hdeg_le := ambient2_coeff_natDegree P.property.1.1 hg_ne
  simp only [Nat.add_zero, Nat.zero_mul, jetIdx] at hdeg_le
  have hdeg_eq : ((((P : Source2).coeff 0).coeff 0).coeff 0).natDegree =
      boundaryDegree2 h s 0 (0, 0, 0, e) := by
    dsimp only [boundaryDegree2, jetIdx]; omega
  have hker0 := congrFun (LinearMap.mem_ker.mp hP) (0, 0, 0, e)
  change coeffAt2 (P : Source2) 0 0 0 (boundaryDegree2 h s 0 (0, 0, 0, e)) e = 0 at hker0
  rw [← hdeg_eq] at hker0
  exact he (by simpa [coeffAt2, sourceCoeff2, coeff_natDegree] using hker0)

/-- **2-Jet `FX`-Telescoping Theorem (`telescope2`)**:
    `finrank L (complete2 Crt word s W) ≤ ∑ t ∈ range (W + 1), finrank FX (evaluated2 Crt word s t)`. -/
theorem telescope2 {h : ℕ} (hpos : 0 < h) (hh : h ≤ 131068) {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) (s : Shape2) (W : ℕ) :
    Module.finrank L (complete2 Crt word s W) ≤
      ∑ t ∈ Finset.range (W + 1), Module.finrank FX (evaluated2 Crt word s t) := by
  induction W with
  | zero =>
    letI := complete2_finite Crt word s 0
    have hr := (boundaryMap2 Crt word s 0).finrank_range_add_finrank_ker
    rw [ker_zero2 hpos hh Crt word s, finrank_bot, add_zero] at hr
    simpa [← hr] using boundary_rank_le2 Crt word s 0
  | succ W ih =>
    letI := complete2_finite Crt word s (W + 1)
    rw [Finset.sum_range_succ]
    have hr := (boundaryMap2 Crt word s (W + 1)).finrank_range_add_finrank_ker
    have ha := boundary_rank_le2 Crt word s (W + 1)
    have hb := ker_step_le2 Crt word s W
    omega

#print axioms specialized2_center
#print axioms rawPosition2_zero
#print axioms leading_bound_2jet
#print axioms telescope2

end
end TwoJetCaseAFX

end Merged_TwoJetCaseAFXCore
