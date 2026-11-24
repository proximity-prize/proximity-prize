import ProximityPrize.SubmissionLower.ListProofA

set_option Elab.async false
set_option maxRecDepth 5000
namespace ShortenChart
noncomputable section
open CJ0 CJ0_3 PolynomialDifferential MvPolynomial
open scoped BigOperators Polynomial
open CJ0_3 (eval_at_center)

section Affine

variable {R : Type*} [CommRing R]

/-- The first three coefficients of `g + l · u` in power-series coordinates. -/
def triangular (g l u : Fin 3 → R) : Fin 3 → R :=
  ![g 0 + l 0 * u 0,
    g 1 + l 1 * u 0 + l 0 * u 1,
    g 2 + l 2 * u 0 + l 1 * u 1 + l 0 * u 2]

theorem map_triangular {A : Type*} [CommRing A] (φ : R →+* A)
    (g l u : Fin 3 → R) (i : Fin 3) :
    φ (triangular g l u i) = triangular (φ ∘ g) (φ ∘ l) (φ ∘ u) i := by
  fin_cases i <;> simp [triangular]

def affineVars (g l : Fin 3 → R) : Fin 3 → MvPolynomial (Fin 3) R :=
  triangular (C ∘ g) (C ∘ l) MvPolynomial.X

def affineMap (g l : Fin 3 → R) : MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  MvPolynomial.aeval (affineVars g l)

theorem eval_affine (g l u : Fin 3 → R) (P : MvPolynomial (Fin 3) R) :
    MvPolynomial.eval u (affineMap g l P) = MvPolynomial.eval (triangular g l u) P := by
  change MvPolynomial.aeval u (MvPolynomial.aeval (affineVars g l) P) =
    MvPolynomial.aeval (triangular g l u) P
  rw [MvPolynomial.comp_aeval_apply]
  have he : (fun i => MvPolynomial.aeval u (affineVars g l i)) = triangular g l u := by
    funext i
    simpa only [affineVars, MvPolynomial.aeval_eq_eval, Function.comp_def,
      MvPolynomial.eval_C, MvPolynomial.eval_X] using
      map_triangular (MvPolynomial.eval u) (C ∘ g) (C ∘ l) MvPolynomial.X i
  rw [he]

theorem map_affine {A : Type*} [CommRing A] (φ : R →+* A)
    (g l : Fin 3 → R) (P : MvPolynomial (Fin 3) R) :
    MvPolynomial.map φ (affineMap g l P) = affineMap (φ ∘ g) (φ ∘ l) (MvPolynomial.map φ P) := by
  let F := (MvPolynomial.map φ).comp (affineMap g l).toRingHom
  let H := (affineMap (φ ∘ g) (φ ∘ l)).toRingHom.comp (MvPolynomial.map φ)
  have heq : F = H := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [F, H, affineMap, MvPolynomial.algebraMap_eq]
    · intro i
      simpa only [F, H, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        affineMap, aeval_X, affineVars, Function.comp_def, MvPolynomial.map_C, MvPolynomial.map_X] using
        map_triangular (MvPolynomial.map φ) (C ∘ g) (C ∘ l) MvPolynomial.X i
  exact DFunLike.congr_fun heq P

private theorem weight_sum (w : Fin 3 → ℕ) {P Q : MvPolynomial (Fin 3) R} {b : ℕ}
    (hp : P.weightedTotalDegree w ≤ b) (hq : Q.weightedTotalDegree w ≤ b) :
    (P + Q).weightedTotalDegree w ≤ b :=
  (show (P + Q).weightedTotalDegree w ≤ max (P.weightedTotalDegree w) (Q.weightedTotalDegree w)
    from AddMonoidAlgebra.supDegree_add_le).trans (max_le hp hq)

private theorem weight_C_mul (w : Fin 3 → ℕ) (a : R)
    {P : MvPolynomial (Fin 3) R} {b : ℕ} (hp : P.weightedTotalDegree w ≤ b) :
    (C a * P).weightedTotalDegree w ≤ b :=
  (weightedTotalDegree_mul_le _ _ _).trans (by simpa only [weightedTotalDegree_C, zero_add] using hp)

private theorem weight_X [Nontrivial R] (w : Fin 3 → ℕ) (i : Fin 3) :
    (MvPolynomial.X i : MvPolynomial (Fin 3) R).weightedTotalDegree w = w i := by
  classical
  rw [show MvPolynomial.X i = (monomial (Finsupp.single i 1) 1 : MvPolynomial (Fin 3) R) from rfl]
  simp [weightedTotalDegree_monomial, Finsupp.weight_single]

private theorem triangular_weight (w : Fin 3 → ℕ) (hw : Monotone w) (g l : Fin 3 → R)
    (u : Fin 3 → MvPolynomial (Fin 3) R) (hu : ∀ i, (u i).weightedTotalDegree w ≤ w i)
    (i : Fin 3) :
    (triangular (C ∘ g) (C ∘ l) u i).weightedTotalDegree w ≤ w i := by
  have hC (a : R) (b : ℕ) : (C a : MvPolynomial (Fin 3) R).weightedTotalDegree w ≤ b := by simp
  have hu' (i j : Fin 3) (h : i ≤ j) : (u i).weightedTotalDegree w ≤ w j := (hu i).trans (hw h)
  fin_cases i
  · exact weight_sum w (hC _ _) (weight_C_mul w _ (hu 0))
  · exact weight_sum w (weight_sum w (hC _ _) (weight_C_mul w _ (hu' 0 1 (by decide))))
      (weight_C_mul w _ (hu 1))
  · exact weight_sum w
      (weight_sum w (weight_sum w (hC _ _) (weight_C_mul w _ (hu' 0 2 (by decide))))
        (weight_C_mul w _ (hu' 1 2 (by decide))))
      (weight_C_mul w _ (hu 2))

theorem affine_weight [Nontrivial R] (w : Fin 3 → ℕ) (hw : Monotone w)
    (g l : Fin 3 → R) (P : MvPolynomial (Fin 3) R) :
    (affineMap g l P).weightedTotalDegree w ≤ P.weightedTotalDegree w :=
  weightedTotalDegree_aeval_le_of_le w w _ _ <|
    triangular_weight w hw g l MvPolynomial.X (fun i => (weight_X (R := R) w i).le)

private theorem pderiv_affineVar (g l : Fin 3 → R) (i : Fin 3) :
    pderiv (Fin.last 2) (affineMap g l (MvPolynomial.X i)) =
      C (l 0) * affineMap g l (pderiv (Fin.last 2) (MvPolynomial.X i)) := by
  change pderiv (Fin.last 2) (MvPolynomial.aeval (affineVars g l) (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]
  fin_cases i <;> simp [affineVars, triangular, affineMap, pderiv_X,
    show Fin.last 2 = (2 : Fin 3) from rfl]

theorem pderiv_affine (g l : Fin 3 → R) (P : MvPolynomial (Fin 3) R) :
    pderiv (Fin.last 2) (affineMap g l P) = C (l 0) * affineMap g l (pderiv (Fin.last 2) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [affineMap, MvPolynomial.algebraMap_eq]
  | add P Q hp hq => simp only [map_add, hp, hq, mul_add]
  | mul_X P i ih =>
    rw [map_mul, pderiv_mul, ih, pderiv_affineVar, pderiv_mul, map_add, map_mul, map_mul]
    ring

end Affine

section Inverse
variable {F : Type*} [Field F]

def inverseScale (l : Fin 3 → F) : Fin 3 → F :=
  ![(l 0)⁻¹, -(l 1) * ((l 0)⁻¹)^2,
    (l 1)^2 * ((l 0)⁻¹)^3 - l 2 * ((l 0)⁻¹)^2]

def inverseJet (g l u : Fin 3 → F) : Fin 3 → F :=
  triangular 0 (inverseScale l) (fun i => u i - g i)

theorem triangular_inverse (g l u : Fin 3 → F) (hl : l 0 ≠ 0) :
    triangular g l (inverseJet g l u) = u := by
  funext i
  fin_cases i <;> simp [triangular, inverseJet, inverseScale] <;> field_simp [hl] <;> ring

theorem inverse_triangular (g l u : Fin 3 → F) (hl : l 0 ≠ 0) :
    inverseJet g l (triangular g l u) = u := by
  funext i
  fin_cases i <;> simp [triangular, inverseJet, inverseScale] <;> field_simp [hl] <;> ring

def inverseVars (g l : Fin 3 → F) : Fin 3 → MvPolynomial (Fin 3) F :=
  triangular (C ∘ 0) (C ∘ inverseScale l) (fun i => MvPolynomial.X i - C (g i))

def inverseMap (g l : Fin 3 → F) : MvPolynomial (Fin 3) F →ₐ[F] MvPolynomial (Fin 3) F :=
  MvPolynomial.aeval (inverseVars g l)

theorem eval_inverse (g l u : Fin 3 → F) (P : MvPolynomial (Fin 3) F) :
    MvPolynomial.eval u (inverseMap g l P) = MvPolynomial.eval (inverseJet g l u) P := by
  change MvPolynomial.aeval u (MvPolynomial.aeval (inverseVars g l) P) =
    MvPolynomial.aeval (inverseJet g l u) P
  rw [MvPolynomial.comp_aeval_apply]
  have he : (fun i => MvPolynomial.aeval u (inverseVars g l i)) = inverseJet g l u := by
    funext i
    fin_cases i <;> simp [inverseVars, inverseJet, triangular, MvPolynomial.aeval_eq_eval]
  rw [he]

theorem inverse_weight (w : Fin 3 → ℕ) (hw : Monotone w)
    (g l : Fin 3 → F) (P : MvPolynomial (Fin 3) F) :
    (inverseMap g l P).weightedTotalDegree w ≤ P.weightedTotalDegree w := by
  refine weightedTotalDegree_aeval_le_of_le w w _ _
    (triangular_weight w hw 0 (inverseScale l) _ ?_)
  intro i
  change (MvPolynomial.X i - C (g i) : MvPolynomial (Fin 3) F).weightedTotalDegree w ≤ w i
  rw [sub_eq_add_neg, ← map_neg (C : F →+* MvPolynomial (Fin 3) F)]
  exact weight_sum w (weight_X w i).le ((weightedTotalDegree_C w (-g i)).le.trans (Nat.zero_le _))

end Inverse

def derivatives {R : Type*} [CommRing R] (g : (Polynomial R)) (i : Fin 3) : (Polynomial R) :=
  Polynomial.hasseDeriv i.val g

theorem derivatives_affine {R : Type*} [CommRing R] (g L h : (Polynomial R)) :
    derivatives (g + L * h) = triangular (derivatives g) (derivatives L) (derivatives h) := by
  funext i
  have h₂ : Finset.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} := by decide
  fin_cases i <;> simp [derivatives, triangular, Polynomial.hasseDeriv_mul, h₂] <;> ring

def transform (g L : (Polynomial K)) (G : Equation) : Equation :=
  (MvPolynomial.optionEquivRight K (Fin 3)).symm
    (affineMap (derivatives g) (derivatives L) (MvPolynomial.optionEquivRight K (Fin 3) G))

private theorem spec_of_flatten {R : Type*} [CommRing R]
    (Q : MvPolynomial (Fin 3) (Polynomial R)) (h : (Polynomial R)) :
    differentialSpecialization ((MvPolynomial.optionEquivRight R (Fin 3)).symm Q) h =
      MvPolynomial.eval (derivatives h) Q := by
  let x : Option (Fin 3) → (Polynomial R) := fun i => i.elim Polynomial.X (derivatives h)
  have he : differentialSpecializationHom h = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X]
    cases i with
    | none => exact differentialSpecialization_x h
    | some i => exact differentialSpecialization_jet i h
  rw [differentialSpecialization, he, MvPolynomial.aeval_optionEquivRight_symm]
  rw [show x none = Polynomial.X from rfl, Polynomial.aeval_X_left,
    show (AlgHom.id R (Polynomial R)).toRingHom = RingHom.id (Polynomial R) from rfl, MvPolynomial.map_id]
  rfl

theorem transform_spec (g L h : (Polynomial K)) (G : Equation) :
    differentialSpecialization (transform g L G) h =
      differentialSpecialization G (g + L * h) := by
  conv_rhs => rw [← (MvPolynomial.optionEquivRight K (Fin 3)).symm_apply_apply G]
  rw [transform, spec_of_flatten, eval_affine, spec_of_flatten, derivatives_affine]

theorem nativeJet_derivatives (g : (Polynomial K)) (i : Fin 3) :
    nativeJet g i = centerMap (derivatives g i) := by
  change (Polynomial.hasseDeriv i.val (g.map embed)).eval center = _
  rw [Polynomial.hasseDeriv_map, eval_at_center]
  rfl

theorem nativeJet_eq (g : (Polynomial K)) : nativeJet g = centerMap ∘ derivatives g :=
  funext (nativeJet_derivatives g)

theorem nativeJet_affine (g L h : (Polynomial K)) :
    nativeJet (g + L * h) = triangular (nativeJet g) (nativeJet L) (nativeJet h) := by
  funext i
  simp only [nativeJet_eq, Function.comp_apply, derivatives_affine]
  exact map_triangular centerMap _ _ _ i

theorem nativeJet_zero_ne {L : (Polynomial K)} (hL : L ≠ 0) : nativeJet L 0 ≠ 0 := by
  rw [nativeJet_derivatives]
  exact map_ne_zero_iff centerMap centerMap_injective |>.mpr (by simpa [derivatives] using hL)

theorem transform_initial (g L : (Polynomial K)) (G : Equation) :
    initial (transform g L G) = affineMap (nativeJet g) (nativeJet L) (initial G) := by
  rw [initial_eq_map, transform, AlgEquiv.apply_symm_apply, map_affine, ← initial_eq_map]
  simp only [nativeJet_eq]

theorem transform_initialSep (g L : (Polynomial K)) (G : Equation) :
    initialSep (transform g L G) =
      C (nativeJet L 0) * affineMap (nativeJet g) (nativeJet L) (initialSep G) := by
  rw [show initialSep (transform g L G) = pderiv (Fin.last 2) (initial (transform g L G)) from
    (pderiv_last_initialJetEquation _ _).symm, transform_initial, pderiv_affine,
    show pderiv (Fin.last 2) (initial G) = initialSep G from pderiv_last_initialJetEquation _ _]

theorem transform_weight (g L : (Polynomial K)) (G : Equation) (w : Fin 3 → ℕ) (hw : Monotone w) :
    (transform g L G).weightedTotalDegree (fun j => j.elim 0 w) ≤
      G.weightedTotalDegree (fun j => j.elim 0 w) := by
  rw [← weightedTotalDegree_optionEquivRight, ← weightedTotalDegree_optionEquivRight]
  rw [transform, AlgEquiv.apply_symm_apply]
  exact affine_weight w hw _ _ _

#print axioms transform_initialSep
end
end ShortenChart
