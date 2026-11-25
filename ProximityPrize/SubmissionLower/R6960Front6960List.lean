import ProximityPrize.SubmissionLower.ListProofA
import ProximityPrize.SubmissionLower.StructuralListPrice
import ProximityPrize.SubmissionLower.R6960Front6960ListRank
import ProximityPrize.SubmissionLower.StructuralListMain
import ProximityPrize.SubmissionLower.RungSplit

-- merged module ShortenChartJet
section Merged_ShortenChartJet

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

end Merged_ShortenChartJet

-- merged module ShortenChart
section Merged_ShortenChart

set_option Elab.async false
set_option maxRecDepth 8000
namespace ShortenChart
noncomputable section
open CJ0 CJ0_3 PolynomialDifferential MvPolynomial
open StructuralList (ShortBand InBand exponent totalCap indexCap topCap)
open scoped Polynomial BigOperators
open CJ0_3 (lifted_total lifted_top lifted_weight indexWeight_eq coeffWeight_eq totalWeight_eq degreeOf_top_of_index readJet_eq)
open CJ0_3_2 (commonTaylor_top)

private theorem exponent_sufficient (length : ℕ) :
    TaylorExponentSufficient 2 length (exponent length) := by
  intro l
  have hl := l.isLt
  unfold exponent
  omega

private theorem top_monotone : Monotone (Pi.single (Fin.last 2) (1 : ℕ)) := by
  intro i j hij
  by_cases hi : i = Fin.last 2
  · have hj : j = Fin.last 2 := le_antisymm (Fin.le_last j) (hi ▸ hij)
    rw [hi, hj]
  · have hi₂ : i ≠ (2 : Fin 3) := hi
    have hw : (Pi.single (Fin.last 2) (1 : ℕ) : Fin 3 → ℕ) i = 0 := by simp [hi₂]
    rw [hw]
    exact Nat.zero_le _

private theorem lift_total {s : Source} {G : Equation} (hG : OrderTwo s G) (g L : (Polynomial K)) :
    jetTotalDegree (lifted (transform g L G)) ≤ s.B := by
  rw [lifted_total]
  have h := transform_weight g L G 1 (fun _ _ _ => le_rfl)
  rw [totalWeight_eq] at h
  exact h.trans hG.2.1

private theorem lift_index {s : Source} {G : Equation} (hG : OrderTwo s G) (g L : (Polynomial K)) :
    (lifted (transform g L G)).weightedTotalDegree (Astra7.jetWeight 0 1 3) ≤ s.J := by
  rw [lifted_weight, indexWeight_eq]
  exact (transform_weight g L G Fin.val (fun _ _ h => h)).trans hG.2.2.1

private theorem lift_top {s : Source} {G : Equation} (hG : OrderTwo s G) (g L : (Polynomial K)) :
    (lifted (transform g L G)).degreeOf (some (Fin.last 2)) ≤ s.C := by
  change jetDegree (lifted (transform g L G)) (Fin.last 2) ≤ s.C
  rw [lifted_top]
  have hw := transform_weight g L G (Pi.single (Fin.last 2) 1) top_monotone
  have he : (fun v : Option (Fin 3) => v.elim 0 (Pi.single (Fin.last 2) 1)) =
      Pi.single (some (Fin.last 2)) (1 : ℕ) := by
    funext v
    cases v <;> simp [Pi.single_apply]
  rw [he, weightedTotalDegree_piSingle, weightedTotalDegree_piSingle] at hw
  exact hw.trans hG.2.2.2

private def basisPolynomial (L : (Polynomial K)) (j : ℕ) : (Polynomial Geo) :=
  L.map embed * (Polynomial.X - Polynomial.C center) ^ j

private def rawDenominator (length : ℕ) (G : Equation) : InitialRing 2 :=
  initialSep G ^ exponent length

private def rawNumerator (length : ℕ) (g L : (Polynomial K)) (G : Equation)
    (i : Fin k) : InitialRing 2 :=
  C ((g.map embed).coeff i.val) * rawDenominator length G +
    ∑ l : Fin length, C ((basisPolynomial L l.val).coeff i.val) *
      commonTaylorNumerator center (lifted G) (exponent length) l.val

def chart (length : ℕ) (g L : (Polynomial K)) (G : Equation) (E : InitialRing 2) : Chart 2 :=
  ⟨E, inverseMap (nativeJet g) (nativeJet L) (rawDenominator length (transform g L G)),
    fun i => inverseMap (nativeJet g) (nativeJet L) (rawNumerator length g L (transform g L G) i)⟩

private theorem rawDenominator_band (s : Source) (length : ℕ) (hK : 3 ≤ length)
    (g L : (Polynomial K)) (G : Equation) (hG : OrderTwo s G) :
    InBand s length (rawDenominator length (transform g L G)) := by
  let Q := lifted (transform g L G)
  have hb : (initialJetSeparant center Q).totalDegree ≤ s.B - 1 :=
    (totalDegree_initialJetSeparant_le center Q).trans
      (Nat.sub_le_sub_right (lift_total hG g L) 1)
  have hi : (initialJetSeparant center Q).weightedTotalDegree Fin.val ≤ s.J - 2 := by
    simpa only [coeffWeight_eq, zero_add, one_mul] using
      (Astra7.initialSeparant_weight 0 1 center Q).trans (Nat.sub_le_sub_right (lift_index hG g L) (0 + 1 * 2))
  have ht : (initialJetSeparant center Q).degreeOf (Fin.last 2) ≤ s.C - 1 :=
    (degreeOf_initialJetSeparant_le center Q).trans (Nat.sub_le_sub_right (lift_top hG g L) 1)
  have hindex : (initialJetSeparant center Q ^ exponent length).weightedTotalDegree Fin.val ≤ indexCap s length :=
    ((weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _ hi)).trans (by
      unfold indexCap
      omega)
  refine ⟨((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hb)).trans (by unfold totalCap; omega),
    hindex, le_min ?_ (degreeOf_top_of_index hindex)⟩
  exact ((degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _ ht)).trans (by omega)

private theorem rawCentered_band (s : Source) (hs : ShapeOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : (Polynomial K)) (G : Equation) (hG : OrderTwo s G) (l : Fin length) :
    InBand s length (commonTaylorNumerator center (lifted (transform g L G)) (exponent length) l.val) := by
  let Q := lifted (transform g L G)
  have hlK := l.isLt
  have hJ := hs.index_top
  have hC := hs.top_pos
  have hi := Astra7.commonTaylor_weight 0 1 s.J length (exponent length) center Q
    (exponent_sufficient length) (by omega) (lift_index hG g L) l
  have hindex : (commonTaylorNumerator center Q (exponent length) l.val).weightedTotalDegree Fin.val ≤
      indexCap s length := by
    have h : (commonTaylorNumerator center Q (exponent length) l.val).weightedTotalDegree Fin.val ≤
        exponent length * (s.J - 2) + l.val := by
      simpa only [coeffWeight_eq, zero_add, one_mul, add_zero] using hi
    exact h.trans (by unfold indexCap; omega)
  refine ⟨?_, hindex, le_min ?_ (degreeOf_top_of_index hindex)⟩
  · exact (totalDegree_commonTaylorNumerator_le center Q (exponent_sufficient length l)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (lift_total hG g L) 1)) 1)
  · have hl : l.val - 1 ≤ length - 2 := by omega
    apply (commonTaylor_top center Q hs.top_pos (lift_top hG g L) (exponent_sufficient length) l).trans
    rw [Nat.add_sub_assoc (by omega : 2 ≤ length)]
    exact Nat.add_le_add_left hl _

private theorem rawNumerator_band (s : Source) (hs : ShapeOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : (Polynomial K)) (G : Equation) (hG : OrderTwo s G) (i : Fin k) :
    InBand s length (rawNumerator length g L (transform g L G) i) := by
  let V := CJ0_4.bandSpace (totalCap s length) (indexCap s length) (topCap s length)
  have hmem {P : InitialRing 2} (hp : InBand s length P) : P ∈ V := CJ0_4.mem_bandSpace.mpr hp
  have hc (a : Geo) {P : InitialRing 2} (hp : InBand s length P) : C a * P ∈ V := by
    rw [← MvPolynomial.smul_eq_C_mul]
    exact V.smul_mem _ (hmem hp)
  suffices h : rawNumerator length g L (transform g L G) i ∈ V from CJ0_4.mem_bandSpace.mp h
  unfold rawNumerator
  exact V.add_mem (hc _ (rawDenominator_band s length hK g L G hG))
    (V.sum_mem fun l _ => hc _ (rawCentered_band s hs length hK g L G hG l))

private theorem inverse_band (s : Source) (length : ℕ) (g L : (Polynomial K)) {P : InitialRing 2}
    (hp : InBand s length P) : InBand s length (inverseMap (nativeJet g) (nativeJet L) P) := by
  have hb := inverse_weight (1 : Fin 3 → ℕ) (fun _ _ _ => le_rfl) (nativeJet g) (nativeJet L) P
  have hi := inverse_weight Fin.val (fun _ _ h => h) (nativeJet g) (nativeJet L) P
  have ht := inverse_weight (Pi.single (Fin.last 2) 1) top_monotone (nativeJet g) (nativeJet L) P
  simp only [weightedTotalDegree_one] at hb
  simp only [weightedTotalDegree_piSingle] at ht
  exact ⟨hb.trans hp.1, hi.trans hp.2.1, ht.trans hp.2.2⟩

theorem chart_band (s : Source) (hs : ShapeOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : (Polynomial K)) (G : Equation) (hG : OrderTwo s G) (E : InitialRing 2) :
    ShortBand s length (chart length g L G E) :=
  ⟨inverse_band s length g L (rawDenominator_band s length hK g L G hG),
    fun i => inverse_band s length g L (rawNumerator_band s hs length hK g L G hG i)⟩

private theorem denominator_eval (length : ℕ) (g L : (Polynomial K)) (G : Equation) (E : InitialRing 2)
    (u : Fin 3 → Geo) (hL : L ≠ 0) :
    MvPolynomial.eval u (chart length g L G E).denominator =
      (nativeJet L 0 * MvPolynomial.eval u (initialSep G)) ^ exponent length := by
  change MvPolynomial.eval u (inverseMap (nativeJet g) (nativeJet L)
    (rawDenominator length (transform g L G))) = _
  rw [eval_inverse, rawDenominator, map_pow, transform_initialSep, map_mul, MvPolynomial.eval_C,
    eval_affine, triangular_inverse _ _ _ (nativeJet_zero_ne hL)]

private theorem denominator_regular (length : ℕ) (g L : (Polynomial K)) (G : Equation) (E : InitialRing 2)
    (hL : L ≠ 0) (hE : Irreducible E) (hreg : ¬ E ∣ initialSep G) :
    ¬ E ∣ (chart length g L G E).denominator := by
  have he : (chart length g L G E).denominator =
      C (nativeJet L 0 ^ exponent length) * (initialSep G) ^ exponent length := by
    apply MvPolynomial.funext
    intro u
    rw [denominator_eval length g L G E u hL, map_mul, MvPolynomial.eval_C, map_pow, mul_pow]
  rw [he]
  have hu : IsUnit (C (nativeJet L 0 ^ exponent length) : InitialRing 2) :=
    ((isUnit_iff_ne_zero).mpr (pow_ne_zero _ (nativeJet_zero_ne hL))).map C
  intro h
  have hh := (hE.prime.dvd_or_dvd h).resolve_left (fun hd => hE.not_isUnit (isUnit_of_dvd_unit hd hu))
  exact hreg (hE.prime.dvd_of_dvd_pow hh)

private theorem reconstruct_basis (length : ℕ) (L : (Polynomial K)) (G : Equation) (u : Fin 3 → Geo) :
    L.map embed * rationalTaylorPolynomial center (lifted G) length u =
      ∑ l : Fin length, Polynomial.C (rationalTaylorCoefficient center (lifted G) u l.val) *
        basisPolynomial L l.val := by
  rw [rationalTaylorPolynomial, Polynomial.centeredCoefficientPrefix, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.taylor_monomial, map_neg, ← sub_eq_add_neg]
  unfold basisPolynomial
  ring

private theorem raw_output (length : ℕ) (g L : (Polynomial K)) (G : Equation)
    (u : Fin 3 → Geo) (hsep : MvPolynomial.eval u (initialSep G) ≠ 0) (i : Fin k) :
    MvPolynomial.eval u (rawNumerator length g L G i) / MvPolynomial.eval u (rawDenominator length G) =
      (g.map embed + L.map embed * rationalTaylorPolynomial center (lifted G) length u).coeff i.val := by
  have hpow : MvPolynomial.eval u (initialSep G) ^ exponent length ≠ 0 := pow_ne_zero _ hsep
  rw [reconstruct_basis, Polynomial.coeff_add, Polynomial.finsetSum_coeff, rawNumerator,
    map_add, add_div, map_mul, MvPolynomial.eval_C, rawDenominator, map_pow, mul_div_cancel_right₀ _ hpow,
    map_sum, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.coeff_C_mul, map_mul, MvPolynomial.eval_C, ← MvPolynomial.aeval_eq_eval (f := u),
    aeval_commonTaylorNumerator center (lifted G) u (exponent_sufficient length l) hsep]
  change _ * (MvPolynomial.eval u (initialSep G) ^ exponent length * _) /
    MvPolynomial.eval u (initialSep G) ^ exponent length = _
  field_simp

private theorem chart_output (length : ℕ) (hK : 3 ≤ length) (g L : (Polynomial K)) (G : Equation)
    (E : InitialRing 2) (u : Fin 3 → Geo) (hu : MvPolynomial.eval u (chart length g L G E).denominator ≠ 0)
    (i : Fin k) :
    (chart length g L G E).output u i =
      (g.map embed + L.map embed * rationalTaylorPolynomial center (lifted (transform g L G))
        length (inverseJet (nativeJet g) (nativeJet L) u)).coeff i.val := by
  let v := inverseJet (nativeJet g) (nativeJet L) u
  have hv : MvPolynomial.eval v (initialSep (transform g L G)) ≠ 0 := by
    intro hh
    apply hu
    change MvPolynomial.eval u (inverseMap (nativeJet g) (nativeJet L)
      (rawDenominator length (transform g L G))) = 0
    rw [eval_inverse, rawDenominator, map_pow, hh, zero_pow]
    unfold exponent
    omega
  rw [Chart.output, chart, eval_inverse, eval_inverse]
  exact raw_output length g L (transform g L G) v hv i

private theorem geoJet_affine (g L h : (Polynomial Geo)) :
    polynomialJet (d := 2) center (g + L * h) =
      triangular (polynomialJet center g) (polynomialJet center L) (polynomialJet center h) := by
  funext i
  change Polynomial.evalRingHom center (derivatives (g + L * h) i) =
    triangular (Polynomial.evalRingHom center ∘ derivatives g)
      (Polynomial.evalRingHom center ∘ derivatives L) (Polynomial.evalRingHom center ∘ derivatives h) i
  rw [derivatives_affine]
  exact map_triangular (Polynomial.evalRingHom center) _ _ _ i

private theorem natDegree_lt {F : Type*} [Field F] {P : (Polynomial F)} {b : ℕ} (hb : 0 < b)
    (hp : P.degree < b) : P.natDegree < b := by
  by_cases hz : P = 0
  · simpa [hz] using hb
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hp

private theorem reconstruction_degree (length : ℕ) (hK : 3 ≤ length) (g L : (Polynomial K))
    (hg : g.degree < k) (hsum : L.natDegree + length ≤ k) (G : Equation) (u : Fin 3 → Geo) :
    (g.map embed + L.map embed * rationalTaylorPolynomial center (lifted G) length u).degree < k := by
  let U := rationalTaylorPolynomial center (lifted G) length u
  have hU : U.natDegree < length :=
    natDegree_lt (by omega) (Polynomial.degree_centeredCoefficientPrefix_lt _ _ _)
  have hg' : (g.map embed).natDegree < k :=
    Polynomial.natDegree_map_le.trans_lt (natDegree_lt (by decide) hg)
  have hm : (L.map embed * U).natDegree < k :=
    (Polynomial.natDegree_mul_le).trans_lt ((Nat.add_lt_add_of_le_of_lt Polynomial.natDegree_map_le hU).trans_le hsum)
  have hh : (g.map embed + L.map embed * U).natDegree < k :=
    (Polynomial.natDegree_add_le _ _).trans_lt (max_lt hg' hm)
  exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hh)

theorem chart_ok (length : ℕ) (hK : 3 ≤ length) (g L : (Polynomial K)) (hL : L ≠ 0)
    (hg : g.degree < k) (hsum : L.natDegree + length ≤ k) (G : Equation)
    (E : InitialRing 2) (hE : Irreducible E) (hreg : ¬ E ∣ initialSep G) :
    ChartOK (chart length g L G E) := by
  refine ⟨hE, denominator_regular length g L G E hL hE hreg, ?_⟩
  intro u hu j
  let v := inverseJet (nativeJet g) (nativeJet L) u
  let U := rationalTaylorPolynomial center (lifted (transform g L G)) length v
  let P := g.map embed + L.map embed * U
  have hcoeff : (chart length g L G E).output u = (fun i : Fin k => P.coeff i.val) := by
    funext i
    exact chart_output length hK g L G E u hu.2 i
  rw [hcoeff, show readJet (fun i : Fin k => P.coeff i.val) j.val =
    (polynomialJet (d := 2) center P) j from readJet_eq P
      (reconstruction_degree length hK g L hg hsum (transform g L G) v) j.val]
  have hU : polynomialJet (d := 2) center U = v :=
    polynomialJet_rationalTaylorPolynomial center (lifted (transform g L G)) (by omega) v
  change (polynomialJet (d := 2) center (g.map embed + L.map embed * U)) j = u j
  rw [geoJet_affine, hU]
  exact congrFun (triangular_inverse (nativeJet g) (nativeJet L) u (nativeJet_zero_ne hL)) j

private theorem chart_contains (length : ℕ) (hK : 3 ≤ length) (hk : length ≤ k)
    (g L : (Polynomial K)) (hL : L ≠ 0) (G : Equation) (E : InitialRing 2)
    {f h : (Polynomial K)} (hh : h.degree < length) (hf : f = g + L * h)
    (hsol : differentialSpecialization G f = 0) (hE : MvPolynomial.eval (nativeJet f) E = 0)
    (hsep : MvPolynomial.eval (nativeJet f) (initialSep G) ≠ 0) :
    coeffPoint f ∈ (chart length g L G E).imageSet := by
  have hL0 := nativeJet_zero_ne hL
  have hu : MvPolynomial.eval (nativeJet f) (chart length g L G E).denominator ≠ 0 := by
    rw [denominator_eval length g L G E _ hL]
    exact pow_ne_zero _ (mul_ne_zero hL0 hsep)
  have hv : inverseJet (nativeJet g) (nativeJet L) (nativeJet f) = nativeJet h := by
    rw [hf, nativeJet_affine]
    exact inverse_triangular _ _ _ hL0
  have hs : MvPolynomial.eval (nativeJet h) (initialSep (transform g L G)) ≠ 0 := by
    rw [transform_initialSep, map_mul, MvPolynomial.eval_C, eval_affine, ← nativeJet_affine, ← hf]
    exact mul_ne_zero hL0 hsep
  have hsol' : differentialSpecialization (lifted (transform g L G)) (h.map embed) = 0 := by
    rw [lifted, ← map_differentialSpecialization, transform_spec, ← hf, hsol, Polynomial.map_zero]
  have hsep' : jetEvaluation (separant (lifted (transform g L G)) (Fin.last 2)) center (nativeJet h) ≠ 0 := by
    simpa only [initialSep, ← MvPolynomial.aeval_eq_eval, aeval_initialJetSeparant] using hs
  let : CharP Geo p := charP_of_injective_ringHom embed.injective p
  have hbin (i : ℕ) (hlo : 2 < i) (hhi : i < length) : (i.choose 2 : Geo) ≠ 0 :=
    Sol1.C40Primitives.native_binomial_guard 2 le_rfl i hlo (Nat.lt_succ_of_lt (hhi.trans_le hk))
  have hrec := rationalTaylorPolynomial_polynomialJet center (lifted (transform g L G))
    (h.map embed) hsol' hsep' (Polynomial.degree_map_le.trans_lt hh) hbin
  refine ⟨nativeJet f, ⟨hE, hu⟩, ?_⟩
  funext i
  rw [chart_output length hK g L G E _ hu, hv, nativeJet, hrec,
    ← Polynomial.map_mul, ← Polynomial.map_add, ← hf, Polynomial.coeff_map]
  rfl

/-- Shortening the quotient chart by the number of common agreement positions bounds the
numerator and denominator while retaining the original jet coordinates. -/
theorem shortenChart (s : Source) (hs : ShapeOK s) (G : Equation) (hG : OrderTwo s G)
    (E : InitialRing 2) (hE : Irreducible E) (_hEdvd : E ∣ initial G)
    (hreg : ¬ E ∣ initialSep G) (S : Finset Node) (hS : S.card + 3 ≤ k) (w : Node → K) :
    ∃ T : Chart 2, ChartOK T ∧ T.equation = E ∧ ShortBand s (k - S.card) T ∧
      ∀ f : (Polynomial K), f.degree < k → differentialSpecialization G f = 0 →
        MvPolynomial.eval (nativeJet f) E = 0 → MvPolynomial.eval (nativeJet f) (initialSep G) ≠ 0 →
        (∀ i ∈ S, f.eval (node i) = w i) → coeffPoint f ∈ T.imageSet := by
  classical
  let g := Lagrange.interpolate S node w
  let L := FrobeniusLocator.locator node S
  let length := k - S.card
  have hK : 3 ≤ length := by dsimp [length]; omega
  have hk : length ≤ k := Nat.sub_le _ _
  have hL := (FrobeniusLocator.locator_monic node S).ne_zero
  have hLn : L.natDegree = S.card := FrobeniusLocator.locator_natDegree _ _
  have hx : Function.Injective node := ProximityPrize.Benchmark.IRSProfile.domain.injective
  have hg : g.degree < k := (Lagrange.degree_interpolate_lt w hx.injOn).trans_le
    (by exact_mod_cast (show S.card ≤ k by omega))
  have hsum : L.natDegree + length ≤ k := by rw [hLn]; dsimp [length]; omega
  refine ⟨chart length g L G E, chart_ok length hK g L hL hg hsum G E hE hreg, rfl,
    chart_band s hs length hK g L G hG E, ?_⟩
  intro f hf hroot hEroot hsep hits
  have hdiv : L ∣ f - g := FrobeniusLocator.Strata.locator_dvd_of_eval_zero node hx S _ (fun i hi => by
    rw [Polynomial.eval_sub, hits i hi, show g.eval (node i) = w i from
      Lagrange.eval_interpolate_at_node w hx.injOn hi, sub_self])
  have hd : (f - g).degree < k := (Polynomial.degree_sub_le _ _).trans_lt (max_lt hf hg)
  have hdN : (f - g).natDegree ≤ N := by
    have hh := natDegree_lt (by decide) hd
    change _ < 131072 at hh
    change _ ≤ 131071
    omega
  have hS' : S.card ≤ N := by
    change _ ≤ 131072 at hS
    change _ ≤ 131071
    omega
  obtain ⟨h, hdeg, he⟩ :=
    FrobeniusLocator.Strata.bounded_locator_quotient node S (f - g) N hS' hdN hdiv
  have hf' : f = g + L * h := by rw [← he]; ring
  have hlen : N - S.card + 1 = length := by
    dsimp [length]
    change _ ≤ 131072 at hS
    change 131071 - S.card + 1 = 131072 - S.card
    omega
  rw [hlen] at hdeg
  exact chart_contains length hK hk g L hL G E hdeg hf' hroot hEroot hsep

#print axioms shortenChart
end
end ShortenChart

end Merged_ShortenChart

-- merged module R6960Front6960List
section Merged_R6960Front6960List

set_option Elab.async false
set_option maxRecDepth 18000

namespace Front6960ListBank
noncomputable section
open Finset
open CJ0 (ShapeOK mem_fullBox Jet fullBox Surplus AgreementOK SilentTail)
open scoped BigOperators

theorem native_shape : ShapeOK source := by
  have hmem := mem_fullBox (B := 80) (J := 24) (C := 10) (by decide) (by decide)
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun j hj => (hmem j).mp hj, ?_⟩
  intro j hj hpos
  obtain ⟨hq, hv, hc⟩ := (hmem j).mp hj
  apply (hmem _).mpr
  refine ⟨?_, hv, hc⟩
  change j.a-1 + j.b + j.c ≤ 80
  unfold Jet.q at hq
  omega
private def runLength (c b : ℕ) := 80 - (b+c) + 1
private def bRange (c : ℕ) := range (24 - 2*c + 1)
private def countRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b
private def totalRow (c : ℕ) := ∑ b ∈ bRange c,
  (runLength c b * (runLength c b - 1) / 2 + runLength c b * (b+c))
private def indexRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b * (b+2*c)
private theorem box_count : source.E.card = ∑ c ∈ range 11, countRow c := by
  simp only [source, fullBox, card_sigma, card_range, countRow, bRange, runLength]
private theorem box_total : (∑ j ∈ source.E, j.q) = ∑ c ∈ range 11, totalRow c := by
  simp only [source, fullBox, sum_sigma, totalRow, bRange, runLength, Jet.q, Jet.a, Jet.b, Jet.c]
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro b _
  simp only [Nat.add_assoc, sum_add_distrib, sum_range_id, sum_const, card_range, smul_eq_mul, Nat.mul_add]
private theorem box_index : (∑ j ∈ source.E, j.v) = ∑ c ∈ range 11, indexRow c := by
  simp only [source, fullBox, sum_sigma, indexRow, bRange, runLength, Jet.v, Jet.b, Jet.c,
    sum_const, card_range, smul_eq_mul]
private theorem row0 : countRow 0 = 1725 ∧ totalRow 0 = 78700 ∧ indexRow 0 = 19400 := by decide +kernel
private theorem row1 : countRow 1 = 1587 ∧ totalRow 1 = 72496 ∧ indexRow 1 = 19619 := by decide +kernel
private theorem row2 : countRow 2 = 1449 ∧ totalRow 2 = 66269 ∧ indexRow 2 = 19516 := by decide +kernel
private theorem row3 : countRow 3 = 1311 ∧ totalRow 3 = 60021 ∧ indexRow 3 = 19095 := by decide +kernel
private theorem row4 : countRow 4 = 1173 ∧ totalRow 4 = 53754 ∧ indexRow 4 = 18360 := by decide +kernel
private theorem row5 : countRow 5 = 1035 ∧ totalRow 5 = 47470 ∧ indexRow 5 = 17315 := by decide +kernel
private theorem row6 : countRow 6 = 897 ∧ totalRow 6 = 41171 ∧ indexRow 6 = 15964 := by decide +kernel
private theorem row7 : countRow 7 = 759 ∧ totalRow 7 = 34859 ∧ indexRow 7 = 14311 := by decide +kernel
private theorem row8 : countRow 8 = 621 ∧ totalRow 8 = 28536 ∧ indexRow 8 = 12360 := by decide +kernel
private theorem row9 : countRow 9 = 483 ∧ totalRow 9 = 22204 ∧ indexRow 9 = 10115 := by decide +kernel
private theorem row10 : countRow 10 = 345 ∧ totalRow 10 = 15865 ∧ indexRow 10 = 7580 := by decide +kernel
private theorem sum_rows (f : ℕ → ℕ) : (∑ i ∈ range 11, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by simp only [sum_range_succ, sum_range_zero, zero_add]
theorem moments : source.E.card = 11385 ∧ (∑ j ∈ source.E, j.q) = 521345 ∧
    (∑ j ∈ source.E, j.v) = 173635 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [box_count, sum_rows, row0.1, row1.1, row2.1, row3.1, row4.1, row5.1, row6.1, row7.1, row8.1, row9.1, row10.1]
  · rw [box_total, sum_rows, row0.2.1, row1.2.1, row2.2.1, row3.2.1, row4.2.1, row5.2.1, row6.2.1, row7.2.1, row8.2.1, row9.2.1, row10.2.1]
  · rw [box_index, sum_rows, row0.2.2, row1.2.2, row2.2.2, row3.2.2, row4.2.2, row5.2.2, row6.2.2, row7.2.2, row8.2.2, row9.2.2, row10.2.2]

theorem surplus : Surplus 179808 source 200031 := by
  obtain ⟨hT, hQ, hV⟩ := moments
  unfold Surplus
  rw [hT, hQ, hV]
  exact (by decide +kernel : 262144*200031+131071*521345 < 59*179808*11385+173635)

private theorem list_price : StructuralList.tariff 179808 source = 8874293514617645 := by decide +kernel

theorem scalar_list : CJ0.ScalarList 179808 8874293514617645 := by
  have agr : AgreementOK 179808 := ⟨by decide, by decide, by decide, by decide⟩
  have tail : SilentTail source 81 := by
    intro j hj hcut
    have hq : j.q ≤ 80 := (native_shape.support j hj).1
    omega
  have h := StructuralList.scalar_list_of_shortening ShortenChart.shortenChart
    179808 source 200031 agr (by decide) native_shape (by decide) (by decide) surplus
    (Or.inr ⟨81, le_rfl, tail, prefix_bound⟩)
  rwa [list_price] at h

#print axioms scalar_list
end
end Front6960ListBank

end Merged_R6960Front6960List
