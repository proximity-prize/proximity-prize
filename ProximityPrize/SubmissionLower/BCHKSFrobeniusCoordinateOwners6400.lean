import ProximityPrize.SubmissionLower.BCHKSFrobeniusProductionPencil6400
import ProximityPrize.SubmissionLower.BCHKSFrobeniusConjugateNonzero6400

/-!
# Coordinate owners for the Frobenius cofactor branch

Cancelling a polynomial gcd in the rational-scroll construction can discard
source coordinates.  Those coordinates cannot simply be ignored in the final
MCA contradiction.  This file records a different finish: a genuinely bad
witness must choose one discarded coordinate, while the global Frobenius
cofactor identity restricts the value of its quotient there to a degree-`p`
linearized polynomial.  At a coordinate where the direct error ratio is
wrong, the quotient value is an injective Möbius function of the challenge.
Consequently one discarded coordinate owns at most `p` challenges.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Coordinates on which the normalized direct pair does not have the error
ratio carried by a Frobenius amplitude atom. -/
noncomputable def FrobeniusAmplitudeAtom.defect
    {S : Finset F} {error₀ error₁ : F → F}
    {sigma : F ≃+* F} {z : F} {h : ℕ}
    (atom : FrobeniusAmplitudeAtom S error₀ error₁ sigma z h) : Finset F :=
  S.filter fun x ↦
    atom.direct₀.eval x * error₁ x ≠ atom.direct₁.eval x * error₀ x

theorem FrobeniusAmplitudeAtom.not_mem_defect_of_mem_valid
    {S : Finset F} {error₀ error₁ : F → F}
    {sigma : F ≃+* F} {z : F} {h : ℕ}
    (atom : FrobeniusAmplitudeAtom S error₀ error₁ sigma z h)
    {x : F} (hx : x ∈ atom.valid) : x ∉ atom.defect := by
  intro hxdefect
  have hneq := (Finset.mem_filter.mp hxdefect).2
  apply hneq
  rw [atom.decomposition₀ x hx, atom.decomposition₁ x hx]
  ring

theorem FrobeniusAmplitudeAtom.defect_subset_sdiff_valid
    {S : Finset F} {error₀ error₁ : F → F}
    {sigma : F ≃+* F} {z : F} {h : ℕ}
    (atom : FrobeniusAmplitudeAtom S error₀ error₁ sigma z h) :
    atom.defect ⊆ S \ atom.valid := by
  intro x hx
  have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
  exact Finset.mem_sdiff.mpr
    ⟨hxS, fun hxvalid ↦ atom.not_mem_defect_of_mem_valid hxvalid hx⟩

/-- The exact normalization loss bounds the number of coordinates which can
own otherwise unexplained MCA witnesses. -/
theorem FrobeniusAmplitudeAtom.card_defect_le_loss
    {S : Finset F} {error₀ error₁ : F → F}
    {sigma : F ≃+* F} {z : F} {h : ℕ}
    (atom : FrobeniusAmplitudeAtom S error₀ error₁ sigma z h) :
    atom.defect.card ≤ atom.baseLoss + atom.gcdLoss := by
  have hdefect : atom.defect.card ≤ (S \ atom.valid).card :=
    Finset.card_le_card atom.defect_subset_sdiff_valid
  have hsplit := Finset.card_sdiff_add_card_eq_card atom.valid_subset
  have hcoverage := atom.coverage
  omega

/-- Intersecting an arbitrary subset of `S` with a defect-aware valid set
loses no more points than the atom's global coverage defect. -/
theorem card_le_inter_add_of_coverage
    (Raw Valid S : Finset F) (loss : ℕ)
    (hRaw : Raw ⊆ S) (hValid : Valid ⊆ S)
    (hcoverage : S.card ≤ Valid.card + loss) :
    Raw.card ≤ (Raw ∩ Valid).card + loss := by
  have hsdiffSubset : Raw \ Valid ⊆ S \ Valid := by
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨hRaw (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
  have hsdiffRaw : (Raw \ Valid).card ≤ (S \ Valid).card :=
    Finset.card_le_card hsdiffSubset
  have hSsplit := Finset.card_sdiff_add_card_eq_card hValid
  have hRawSplit := Finset.card_inter_add_card_sdiff Raw Valid
  omega

/-- The scalar equation obtained by evaluating a coefficient-Frobenius
polynomial identity at one base-domain coordinate. -/
noncomputable def frobeniusValueFiber
    (sigma : F ≃+* F) (a b : F) : Finset F :=
  Finset.univ.filter fun y ↦ a * sigma y = b * y

/-- A nonzero linearized equation `a*Y^p-b*Y=0` has at most `p` roots.
This formulation needs no classification of the fixed field. -/
theorem card_frobeniusValueFiber_le
    (sigma : F ≃+* F) (p : ℕ) (hp : 1 < p)
    (hpow : ∀ y : F, sigma y = y ^ p)
    (a b : F) (hab : ¬(a = 0 ∧ b = 0)) :
    (frobeniusValueFiber sigma a b).card ≤ p := by
  let R : F[X] := Polynomial.C a * Polynomial.X ^ p -
    Polynomial.C b * Polynomial.X
  have hR : R ≠ 0 := by
    intro hzero
    by_cases ha : a = 0
    · have hb : b ≠ 0 := fun hb ↦ hab ⟨ha, hb⟩
      have hnonzero : -(Polynomial.C b * Polynomial.X) ≠ (0 : F[X]) :=
        neg_ne_zero.mpr (mul_ne_zero (Polynomial.C_ne_zero.mpr hb)
          Polynomial.X_ne_zero)
      apply hnonzero
      simpa only [R, ha, Polynomial.C_0, zero_mul, zero_sub] using hzero
    · have heq : Polynomial.C a * Polynomial.X ^ p =
          Polynomial.C b * Polynomial.X := sub_eq_zero.mp hzero
      have hleft : (Polynomial.C a * Polynomial.X ^ p).natDegree = p :=
        Polynomial.natDegree_C_mul_X_pow p a ha
      have hright : (Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
        simpa only [Polynomial.natDegree_X] using
          Polynomial.natDegree_C_mul_le b Polynomial.X
      have := congrArg Polynomial.natDegree heq
      rw [hleft] at this
      omega
  have hdegree : R.natDegree ≤ p := by
    dsimp only [R]
    have hleft : (Polynomial.C a * Polynomial.X ^ p).natDegree ≤ p := by
      simpa using Polynomial.natDegree_C_mul_le a (Polynomial.X ^ p)
    have hright : (Polynomial.C b * Polynomial.X).natDegree ≤ p := by
      have hlin : (Polynomial.C b * Polynomial.X).natDegree ≤ 1 :=
        by simpa only [Polynomial.natDegree_X] using
          Polynomial.natDegree_C_mul_le b Polynomial.X
      omega
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le hleft hright)
  let Roots : Finset F := R.roots.toFinset
  have hmaps : Set.MapsTo (fun y : F ↦ y)
      (frobeniusValueFiber sigma a b : Set F) (Roots : Set F) := by
    intro y hy
    have heq := (Finset.mem_filter.mp hy).2
    change y ∈ R.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hR,
      Polynomial.IsRoot.def]
    dsimp only [R]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    change a * y ^ p - b * y = 0
    rw [← hpow]
    exact sub_eq_zero.mpr heq
  have hinj : ((frobeniusValueFiber sigma a b : Set F)).InjOn
      (fun y : F ↦ y) := by
    intro u _ v _ huv
    exact huv
  calc
    (frobeniusValueFiber sigma a b).card ≤ Roots.card :=
      Finset.card_le_card_of_injOn (fun y : F ↦ y) hmaps hinj
    _ ≤ R.natDegree := (Multiset.toFinset_card_le R.roots).trans
      (Polynomial.card_roots' R)
    _ ≤ p := hdegree

/-- Coprime polynomial coefficients cannot both vanish at a field point. -/
theorem not_both_eval_eq_zero_of_isCoprime
    (D A : F[X]) (hDA : IsCoprime D A) (x : F) :
    ¬(D.eval x = 0 ∧ A.eval x = 0) := by
  obtain ⟨U, V, hbezout⟩ := hDA
  intro hzero
  have heval := congrArg (fun P : F[X] ↦ P.eval x) hbezout
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_one, hzero.1, hzero.2, mul_zero, add_zero] at heval
  exact zero_ne_one heval

/-- Evaluating a global semilinear polynomial identity lands in the bounded
linearized fibre at every coordinate. -/
theorem mem_frobeniusValueFiber_of_polynomial_identity
    (sigma : F ≃+* F) (D A M : F[X])
    (hidentity : D * M.map sigma.toRingHom = A * M) (x : F)
    (hfixed : sigma x = x) :
    M.eval x ∈ frobeniusValueFiber sigma (D.eval x) (A.eval x) := by
  rw [frobeniusValueFiber, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have heval := congrArg (fun P : F[X] ↦ P.eval x) hidentity
  rw [Polynomial.eval_mul, Polynomial.eval_mul,
    polynomial_map_eval_of_fixed sigma M x hfixed] at heval
  exact heval

/-- After the direct affine factor divides a cofactor, the cofactor identity
cancels both that factor and its coefficient conjugate. -/
theorem quotient_semilinear_identity_of_cofactorRelation_eq_zero
    {S : Finset F} {error₀ error₁ : F → F}
    {sigma : F ≃+* F} {z : F} {h : ℕ}
    (atom : FrobeniusAmplitudeAtom S error₀ error₁ sigma z h)
    (w : F) (Cof Q : F[X])
    (hfactor : affinePolynomial atom.direct₀ atom.direct₁ w * Q = Cof)
    (hCw : affinePolynomial atom.direct₀ atom.direct₁ w ≠ 0)
    (hidentity : atom.cofactorRelation w Cof = 0) :
    atom.denominator * Q.map sigma.toRingHom =
      atom.amplitudeMultiplier * Q := by
  let Cw := affinePolynomial atom.direct₀ atom.direct₁ w
  have hCwMap : Cw.map sigma.toRingHom ≠ 0 :=
    Polynomial.map_ne_zero hCw
  have hrel : atom.denominator * Cw * (Cw.map sigma.toRingHom *
        Q.map sigma.toRingHom) =
      atom.amplitudeMultiplier * Cw.map sigma.toRingHom * (Cw * Q) := by
    have hrel' := sub_eq_zero.mp hidentity
    rw [← hfactor, Polynomial.map_mul] at hrel'
    simpa only [Cw, FrobeniusAmplitudeAtom.cofactorRelation] using hrel'
  apply mul_left_cancel₀ (mul_ne_zero hCw hCwMap)
  calc
    (Cw * Cw.map sigma.toRingHom) *
          (atom.denominator * Q.map sigma.toRingHom) =
        atom.denominator * Cw *
          (Cw.map sigma.toRingHom * Q.map sigma.toRingHom) := by ring
    _ = atom.amplitudeMultiplier * Cw.map sigma.toRingHom * (Cw * Q) := hrel
    _ = (Cw * Cw.map sigma.toRingHom) *
          (atom.amplitudeMultiplier * Q) := by ring

/-- Multiplying the quotient by a locator fixed by Frobenius preserves the
same semilinear identity. -/
theorem locator_mul_quotient_semilinear_identity
    (sigma : F ≃+* F) (D A L Q : F[X])
    (hQ : D * Q.map sigma.toRingHom = A * Q)
    (hLfixed : L.map sigma.toRingHom = L) :
    D * (L * Q).map sigma.toRingHom = A * (L * Q) := by
  rw [Polynomial.map_mul, hLfixed]
  calc
    D * (L * Q.map sigma.toRingHom) = L *
        (D * Q.map sigma.toRingHom) := by ring
    _ = L * (A * Q) := by rw [hQ]
    _ = A * (L * Q) := by ring

/-- Cancelling the polynomial gcd of the two semilinear coefficients is safe
because the relation is already a global polynomial identity. -/
theorem NormalizedPolynomialPair.semilinear_identity
    (D A M : F[X]) (bound loss : ℕ)
    (pair : NormalizedPolynomialPair D A bound loss)
    (sigma : F ≃+* F)
    (hidentity : D * M.map sigma.toRingHom = A * M) :
    pair.first * M.map sigma.toRingHom = pair.second * M := by
  apply mul_left_cancel₀ pair.common_ne_zero
  calc
    pair.common * (pair.first * M.map sigma.toRingHom) =
        (pair.common * pair.first) * M.map sigma.toRingHom := by ring
    _ = D * M.map sigma.toRingHom := by rw [pair.first_factor]
    _ = A * M := hidentity
    _ = (pair.common * pair.second) * M := by rw [pair.second_factor]
    _ = pair.common * (pair.second * M) := by ring

/-- The fixed coprime coefficient pair governing all quotient values produced
from one amplitude atom. -/
noncomputable def FrobeniusAmplitudeAtom.semilinearPair
    {S : Finset F} {error₀ error₁ : F → F}
    {sigma : F ≃+* F} {z : F} {h : ℕ}
    (atom : FrobeniusAmplitudeAtom S error₀ error₁ sigma z h) :
    NormalizedPolynomialPair atom.denominator atom.amplitudeMultiplier
      h atom.baseLoss :=
  normalizePolynomialPair atom.denominator atom.amplitudeMultiplier
    h atom.baseLoss
    (fun hzero ↦ atom.denominator_ne_zero hzero.1)
    atom.denominator_degree atom.amplitudeMultiplier_degree

theorem FrobeniusAmplitudeAtom.semilinearPair_identity
    {S : Finset F} {error₀ error₁ : F → F}
    {sigma : F ≃+* F} {z : F} {h : ℕ}
    (atom : FrobeniusAmplitudeAtom S error₀ error₁ sigma z h)
    (M : F[X])
    (hidentity : atom.denominator * M.map sigma.toRingHom =
      atom.amplitudeMultiplier * M) :
    atom.semilinearPair.first * M.map sigma.toRingHom =
      atom.semilinearPair.second * M :=
  atom.semilinearPair.semilinear_identity
    atom.denominator atom.amplitudeMultiplier M h atom.baseLoss sigma hidentity

/-- Evaluation form of the normalized semilinear identity.  Keeping this as
an atom-level lemma prevents downstream concrete instantiations from having
to unfold the normalization construction during elaboration. -/
theorem FrobeniusAmplitudeAtom.multiplier_eval_mem_semilinearFiber
    {S : Finset F} {error₀ error₁ : F → F}
    {sigma : F ≃+* F} {z : F} {h : ℕ}
    (atom : FrobeniusAmplitudeAtom S error₀ error₁ sigma z h)
    (M : F[X])
    (hidentity : atom.denominator * M.map sigma.toRingHom =
      atom.amplitudeMultiplier * M)
    (x : F) (hfixed : sigma x = x) :
    M.eval x ∈ frobeniusValueFiber sigma
      (atom.semilinearPair.first.eval x)
      (atom.semilinearPair.second.eval x) := by
  exact mem_frobeniusValueFiber_of_polynomial_identity sigma
    atom.semilinearPair.first atom.semilinearPair.second M
    (atom.semilinearPair_identity M hidentity) x hfixed

/-- At a genuine direct-ratio defect, the quotient value forced by agreement
is an injective Möbius function of the challenge. -/
theorem mobiusValue_injectiveOn_of_defect
    (e₀ e₁ A B : F) (T : Finset F)
    (hdefect : A * e₁ ≠ B * e₀)
    (hden : ∀ w ∈ T, A + w * B ≠ 0) :
    (T : Set F).InjOn
      (fun w ↦ (e₀ + w * e₁) / (A + w * B)) := by
  intro u hu v hv heq
  have huDen := hden u hu
  have hvDen := hden v hv
  have hcross :
      (e₀ + u * e₁) * (A + v * B) =
        (e₀ + v * e₁) * (A + u * B) := by
    exact (div_eq_div_iff huDen hvDen).mp heq
  have hproduct : (u - v) * (A * e₁ - B * e₀) = 0 := by
    linear_combination hcross
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hproduct).resolve_right (sub_ne_zero.mpr hdefect))

/-- A nonzero affine direct value and the direct-ratio identity recover both
components from their affine combination. -/
theorem direct_pair_eq_of_cross_and_affine
    (A B e₀ e₁ w m : F)
    (hCw : A + w * B ≠ 0)
    (hcross : A * e₁ = B * e₀)
    (haffine : (A + w * B) * m = e₀ + w * e₁) :
    A * m = e₀ ∧ B * m = e₁ := by
  let r₀ := A * m - e₀
  let r₁ := B * m - e₁
  have hline : r₀ + w * r₁ = 0 := by
    dsimp only [r₀, r₁]
    linear_combination haffine
  have hresidualCross : A * r₁ = B * r₀ := by
    dsimp only [r₀, r₁]
    linear_combination -hcross
  have hr₀ : r₀ = 0 := by
    apply (mul_eq_zero.mp (show (A + w * B) * r₀ = 0 by
      calc
        (A + w * B) * r₀ = A * r₀ + w * (B * r₀) := by ring
        _ = A * r₀ + w * (A * r₁) := by rw [← hresidualCross]
        _ = A * (r₀ + w * r₁) := by ring
        _ = 0 := by rw [hline, mul_zero])).resolve_left hCw
  have hr₁ : r₁ = 0 := by
    apply (mul_eq_zero.mp (show (A + w * B) * r₁ = 0 by
      calc
        (A + w * B) * r₁ = A * r₁ + w * (B * r₁) := by ring
        _ = B * r₀ + w * (B * r₁) := by rw [hresidualCross]
        _ = B * (r₀ + w * r₁) := by ring
        _ = 0 := by rw [hline, mul_zero])).resolve_left hCw
  constructor
  · exact sub_eq_zero.mp hr₀
  · exact sub_eq_zero.mp hr₁

/-- A family of challenges whose injective Möbius values all satisfy the same
nondegenerate Frobenius equation has cardinality at most `p`. -/
theorem card_le_of_injective_frobenius_values
    {A : Type} [DecidableEq A]
    (sigma : F ≃+* F) (p : ℕ) (hp : 1 < p)
    (hpow : ∀ y : F, sigma y = y ^ p)
    (a b : F) (hab : ¬(a = 0 ∧ b = 0))
    (T : Finset A) (value : A → F)
    (hvalue : ∀ w ∈ T, value w ∈ frobeniusValueFiber sigma a b)
    (hinj : (T : Set A).InjOn value) :
    T.card ≤ p := by
  calc
    T.card ≤ (frobeniusValueFiber sigma a b).card :=
      Finset.card_le_card_of_injOn value
        (fun w hw ↦ hvalue w hw) hinj
    _ ≤ p := card_frobeniusValueFiber_le sigma p hp hpow a b hab

/-- Equation-only form of the same capacity bound.  Its statement avoids a
concrete `Finset.univ`, which is important for large extension-field
instantiations whose enumerable-field instance is expensive to elaborate. -/
theorem card_le_of_injective_frobenius_equation
    {A : Type} [DecidableEq A]
    (sigma : F ≃+* F) (p : ℕ) (hp : 1 < p)
    (hpow : ∀ y : F, sigma y = y ^ p)
    (a b : F) (hab : ¬(a = 0 ∧ b = 0))
    (T : Finset A) (value : A → F)
    (hequation : ∀ w ∈ T, a * sigma (value w) = b * value w)
    (hinj : (T : Set A).InjOn value) :
    T.card ≤ p := by
  apply card_le_of_injective_frobenius_values sigma p hp hpow a b hab
    T value
  · intro w hw
    rw [frobeniusValueFiber, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hequation w hw⟩
  · exact hinj

end ProximityPrize.SubmissionLower
