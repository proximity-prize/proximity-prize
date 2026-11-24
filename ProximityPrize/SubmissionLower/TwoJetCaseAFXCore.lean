import ProximityPrize.SubmissionLower.TwoJetRescueBridge
import ProximityPrize.SubmissionLower.UpperBranch1

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
