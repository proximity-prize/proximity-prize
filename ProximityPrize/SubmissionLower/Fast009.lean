import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.GradedRank
import ArkLib.Data.MvPolynomial.RadicalSplit.Separable
import ArkLib.Data.MvPolynomial.WeightedDegree.Products
import ArkLib.Data.Polynomial.Differential.JetPrefix
import ArkLib.ToMathlib.MvPolynomial.SupportWeight
import ProximityPrize.SubmissionLower.Fast005
import ProximityPrize.SubmissionLower.Fast006
import ProximityPrize.SubmissionLower.Fast003
import ProximityPrize.SubmissionLower.Fast008
set_option Elab.async false

section PackSource_C57TopPresentation
set_option autoImplicit true
/-! Highest-jet polynomial coordinates and exact weighted coefficient triangles.
No list-count or source hypothesis is asserted here. -/
namespace Sol1.C57
open Polynomial PolynomialDifferential MvPolynomial
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Move the highest jet to none; the independent variable becomes some none. -/
def topVariableEquiv (d : ℕ) : JetVariable (d + 1) ≃ Option (JetVariable d) :=
  (Equiv.optionCongr (finSuccEquiv' (Fin.last (d + 1)))).trans (Equiv.swap none (some none))

@[simp] theorem topVariableEquiv_x (d : ℕ) : topVariableEquiv d none = some none := by
  simp [topVariableEquiv]
@[simp] theorem topVariableEquiv_top (d : ℕ) :
    topVariableEquiv d (some (Fin.last (d + 1))) = none := by
  simp [topVariableEquiv]
@[simp] theorem topVariableEquiv_lower (d : ℕ) (j : Fin (d + 1)) :
    topVariableEquiv d (some j.castSucc) = some (some j) := by
  have hj : j.castSucc < Fin.last (d + 1) := Fin.castSucc_lt_last j
  simp [topVariableEquiv, finSuccEquiv'_below hj, Equiv.swap_apply_def]

variable {E : Type*} [CommRing E]

def topReindex (d : ℕ) : DifferentialPolynomial E (d + 1) ≃ₐ[E]
    MvPolynomial (Option (JetVariable d)) E := renameEquiv E (topVariableEquiv d)

def topPresentation (d : ℕ) : DifferentialPolynomial E (d + 1) ≃ₐ[E]
    Polynomial (DifferentialPolynomial E d) :=
  (topReindex d).trans (optionEquivLeft E (JetVariable d))

def rootJetWeight (d : ℕ) : Option (JetVariable d) → ℕ := fun v ↦ v.elim 1 jetDegreeWeight

theorem topReindex_weight (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    (topReindex d Q).weightedTotalDegree (rootJetWeight d) = jetTotalDegree Q := by
  rw [topReindex, renameEquiv_apply, weightedTotalDegree_rename_of_injective
    (topVariableEquiv d).injective, jetTotalDegree]
  congr 1
  funext v
  rcases v with _ | j
  · simp [rootJetWeight, jetDegreeWeight]
  · induction j using Fin.lastCases with
    | last => simp [rootJetWeight, jetDegreeWeight]
    | cast j => simp [rootJetWeight, jetDegreeWeight]

theorem topReindex_degree (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    degreeOf none (topReindex d Q) = jetDegree Q (Fin.last (d + 1)) := by
  have h := degreeOf_rename_of_injective (p := Q) (topVariableEquiv d).injective
    (some (Fin.last (d + 1)))
  simpa only [topReindex, renameEquiv_apply, topVariableEquiv_top, jetDegree] using h

theorem topPresentation_degree (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    (topPresentation d Q).natDegree = jetDegree Q (Fin.last (d + 1)) := by
  rw [topPresentation, AlgEquiv.trans_apply, natDegree_optionEquivLeft, topReindex_degree]

theorem topReindex_pderiv (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    pderiv none (topReindex d Q) = topReindex d (separant Q (Fin.last (d + 1))) := by
  have h := pderiv_rename (topVariableEquiv d).injective (some (Fin.last (d + 1))) Q
  simpa only [topReindex, renameEquiv_apply, topVariableEquiv_top, separant] using h

theorem topPresentation_derivative (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    (topPresentation d Q).derivative = topPresentation d (separant Q (Fin.last (d + 1))) := by
  change (optionEquivLeft E (JetVariable d) (topReindex d Q)).derivative = _
  rw [← optionEquivLeft_pderiv_none, topReindex_pderiv]
  rfl

/-- Weighted coefficient triangle, retaining the outer exponent even for a zero coefficient. -/
theorem coeff_weight_add_le {σ : Type*} (w : σ → ℕ)
    (Q : MvPolynomial (Option σ) E) (i : ℕ) (hi : i ≤ degreeOf none Q) :
    i + ((optionEquivLeft E σ Q).coeff i).weightedTotalDegree w ≤
      Q.weightedTotalDegree (fun v ↦ v.elim 1 w) := by
  classical
  have hiB : i ≤ Q.weightedTotalDegree (fun v ↦ v.elim 1 w) :=
    hi.trans (degreeOf_le_weightedTotalDegree _ none (by simp) Q)
  have hh : ((optionEquivLeft E σ Q).coeff i).weightedTotalDegree w ≤
      Q.weightedTotalDegree (fun v ↦ v.elim 1 w) - i := by
    apply Finset.sup_le_iff.mpr
    intro u hu
    have hs := (mem_support_coeff_optionEquivLeft E).mp hu
    have hw := le_weightedTotalDegree (fun v : Option σ ↦ v.elim 1 w) hs
    rw [Finsupp.weight_optionElim, one_mul] at hw
    omega
  omega

/-- Polynomial evaluation at the highest Hasse jet is the original specialization. -/
theorem topPresentation_eval (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) (P : E[X]) :
    (topPresentation d Q).eval₂ (differentialSpecializationHom (d := d) P).toRingHom
      (Polynomial.hasseDeriv (d + 1) P) = differentialSpecialization Q P := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [topPresentation, topReindex, differentialSpecialization_C]
  | add Q R hQ hR =>
    simp only [map_add, Polynomial.eval₂_add, differentialSpecialization,
      map_add, hQ, hR]
  | mul_X Q v hQ =>
    have hv : (topPresentation d (MvPolynomial.X v)).eval₂
        (differentialSpecializationHom (d := d) P).toRingHom
        (Polynomial.hasseDeriv (d + 1) P) =
        differentialSpecialization (MvPolynomial.X v) P := by
      rcases v with _ | j
      · simp [topPresentation, topReindex]
      · induction j using Fin.lastCases with
        | last => simp [topPresentation, topReindex]
        | cast j => simp [topPresentation, topReindex]
    simp only [map_mul, Polynomial.eval₂_mul, differentialSpecialization,
      map_mul, hQ, hv]

end
end Sol1.C57
end PackSource_C57TopPresentation

section PackSource_C57RadicalSplit
set_option autoImplicit true
namespace Sol1.C57
open Polynomial PolynomialDifferential MvPolynomial
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {E : Type*} [Field E]

def regularPart (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    DifferentialPolynomial E (d + 1) :=
  (topReindex d).symm (radicalPrimPart none (topReindex d Q))

def lowerPart (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) : DifferentialPolynomial E d :=
  (optionEquivLeft E (JetVariable d) (radicalContent none (topReindex d Q))).coeff 0

theorem content_presentation (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    optionEquivLeft E (JetVariable d) (radicalContent none (topReindex d Q)) =
      Polynomial.C (lowerPart d Q) := by
  apply Polynomial.eq_C_of_natDegree_eq_zero
  rw [natDegree_optionEquivLeft, degreeOf_radicalContent]

theorem optionEquivLeft_rename_some {σ : Type*} (T : MvPolynomial σ E) :
    optionEquivLeft E σ (rename some T) = Polynomial.C T := by
  induction T using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p j hp => simp [hp]

theorem content_eq_rename (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    radicalContent none (topReindex d Q) = rename some (lowerPart d Q) := by
  apply (optionEquivLeft E (JetVariable d)).injective
  rw [content_presentation, optionEquivLeft_rename_some]

theorem content_weight (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    (radicalContent none (topReindex d Q)).weightedTotalDegree (rootJetWeight d) =
      jetTotalDegree (lowerPart d Q) := by
  rw [content_eq_rename, weightedTotalDegree_rename_of_injective (Option.some_injective (JetVariable d))]
  rfl

theorem regular_weight (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    (radicalPrimPart none (topReindex d Q)).weightedTotalDegree (rootJetWeight d) =
      jetTotalDegree (regularPart d Q) := by
  have h := topReindex_weight d (regularPart d Q)
  simpa only [regularPart, AlgEquiv.apply_symm_apply] using h

/-- Exact joint jet-degree budget of the lower content and squarefree regular equation. -/
theorem split_weight (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    jetTotalDegree (lowerPart d Q) + jetTotalDegree (regularPart d Q) ≤ jetTotalDegree Q := by
  have h := map_radicalContent_add_map_radicalPrimPart_le
    (d := fun T ↦ T.weightedTotalDegree (rootJetWeight d))
    (fun x y hx hy ↦ weightedTotalDegree_mul _ x y hx hy) none (topReindex d Q)
  rwa [content_weight, regular_weight, topReindex_weight] at h

theorem regular_ne_zero (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    regularPart d Q ≠ 0 := by
  apply (map_ne_zero_iff (topReindex d).symm (topReindex d).symm.injective).mpr
  exact radicalPrimPart_ne_zero none _

theorem lower_ne_zero (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    lowerPart d Q ≠ 0 := by
  intro hz
  have h := content_presentation d Q
  rw [hz, Polynomial.C_0] at h
  apply radicalContent_ne_zero none (topReindex d Q)
  apply (optionEquivLeft E (JetVariable d)).injective
  simpa only [map_zero] using h

theorem regular_presentation (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    topPresentation d (regularPart d Q) = ordinaryRootPolynomial (topReindex d Q) := by
  simp [topPresentation, regularPart, ordinaryRootPolynomial]

def rootEvaluation (d : ℕ) (P : E[X]) :
    MvPolynomial (Option (JetVariable d)) E →+* E[X] :=
  (differentialSpecializationHom (d := d + 1) P).toRingHom.comp (topReindex d).symm.toRingHom

theorem rootEvaluation_content (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) (P : E[X]) :
    rootEvaluation d P (radicalContent none (topReindex d Q)) =
      differentialSpecialization (lowerPart d Q) P := by
  have h := topPresentation_eval d
    ((topReindex d).symm (radicalContent none (topReindex d Q))) P
  rw [show topPresentation d ((topReindex d).symm (radicalContent none (topReindex d Q))) =
      Polynomial.C (lowerPart d Q) by
        simp only [topPresentation, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
          content_presentation]] at h
  change differentialSpecialization
    ((topReindex d).symm (radicalContent none (topReindex d Q))) P = _
  simpa only [Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, differentialSpecialization] using h.symm

/-- Exact full root coverage, including all lower-order content factors and multiplicities. -/
theorem root_split (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) (hQ : Q ≠ 0) (P : E[X])
    (hroot : differentialSpecialization Q P = 0) :
    differentialSpecialization (lowerPart d Q) P = 0 ∨
      differentialSpecialization (regularPart d Q) P = 0 := by
  have hQr : topReindex d Q ≠ 0 :=
    (map_ne_zero_iff (topReindex d) (topReindex d).injective).mpr hQ
  have hz := (map_radicalContent_mul_radicalPrimPart_eq_zero_iff
    (rootEvaluation d P) none hQr).mpr (by simpa [rootEvaluation] using hroot)
  rw [map_mul, rootEvaluation_content, mul_eq_zero] at hz
  exact hz

theorem regular_eq_one_of_degree_zero (d : ℕ) (Q : DifferentialPolynomial E (d + 1))
    (hdeg : jetDegree (regularPart d Q) (Fin.last (d + 1)) = 0) :
    regularPart d Q = 1 := by
  have hd : degreeOf none (radicalPrimPart none (topReindex d Q)) = 0 := by
    simpa only [regularPart, AlgEquiv.apply_symm_apply] using
      (topReindex_degree d (regularPart d Q)).trans hdeg
  rw [regularPart, radicalPrimPart_eq_one_of_degreeOf_eq_zero none _ hd, map_one]

/-- One nonzero lower-order polynomial catches every singular regular-part root. -/
def singularEquation (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) : DifferentialPolynomial E d :=
  let f := ordinaryRootPolynomial (topReindex d Q)
  Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1)

theorem singularEquation_ne_zero (d : ℕ) (Q : DifferentialPolynomial E (d + 1))
    (hchar : ringChar E = 0 ∨ jetDegree Q (Fin.last (d + 1)) < ringChar E) :
    singularEquation d Q ≠ 0 := by
  apply Polynomial.resultant_derivative_ne_zero_ordinaryRootPolynomial
  rwa [topReindex_degree]

end
end Sol1.C57
end PackSource_C57RadicalSplit

section PackSource_K1_11FilteredQuotient
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial
variable {F σ ι : Type*} [Field F]

/-- Simultaneous polynomial filtrations; none of the weights must be positive. -/
def filtered (v : ι → σ → ℕ) (d : ι → ℕ) : Submodule F (MvPolynomial σ F) :=
  ⨅ i, restrictWeightedDegree (v i) (d i)

@[simp] theorem mem_filtered (v : ι → σ → ℕ) (d : ι → ℕ) (P : MvPolynomial σ F) :
    P ∈ filtered v d ↔ ∀ i, P.weightedTotalDegree (v i) ≤ d i := by
  simp only [filtered, Submodule.mem_iInf, mem_restrictWeightedDegree_iff_weightedTotalDegree_le]

/-- Exact subtraction for ALL multiples, with the zero multiplier included. -/
theorem mul_mem_filtered_iff (v : ι → σ → ℕ) (d e : ι → ℕ)
    (L H : MvPolynomial σ F) (hL : L≠0)
    (hdeg : ∀ i, L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i) :
    L*H ∈ filtered v d ↔ H ∈ filtered v (fun i => d i-e i) := by
  by_cases hH : H=0
  · simp [hH]
  · simp only [mem_filtered]
    constructor
    · intro h i
      have hi := h i
      rw [weightedTotalDegree_mul _ _ _ hL hH,hdeg i] at hi
      omega
    · intro h i
      have hi := h i
      rw [weightedTotalDegree_mul _ _ _ hL hH,hdeg i]
      have := hed i
      omega

/-- Multiplication into the bounded source space. -/
def filteredMul (v : ι → σ → ℕ) (d e : ι → ℕ) (L : MvPolynomial σ F)
    (hL : L≠0) (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i)
    (hed : ∀ i,e i≤d i) :
    filtered (F:=F) v (fun i => d i-e i) →ₗ[F] filtered (F:=F) v d where
  toFun H := ⟨L*H.val,(mul_mem_filtered_iff v d e L H.val hL hdeg hed).mpr H.property⟩
  map_add' H J := by apply Subtype.ext; exact mul_add L H.val J.val
  map_smul' a H := by apply Subtype.ext; exact mul_smul_comm a L H.val

theorem filteredMul_injective (v : ι → σ → ℕ) (d e : ι → ℕ)
    (L : MvPolynomial σ F) (hL : L≠0)
    (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i) :
    Function.Injective (filteredMul v d e L hL hdeg hed) := by
  intro H J heq
  apply Subtype.ext
  exact mul_left_cancel₀ hL (congrArg Subtype.val heq)

/-- The range consists of exactly the source polynomials divisible by L. -/
theorem mem_filteredMul_range_iff (v : ι → σ → ℕ) (d e : ι → ℕ)
    (L : MvPolynomial σ F) (hL : L≠0)
    (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i)
    (Q : filtered (F:=F) v d) :
    Q ∈ LinearMap.range (filteredMul v d e L hL hdeg hed) ↔ L ∣ Q.val := by
  constructor
  · rintro ⟨H,hH⟩
    exact ⟨H.val,congrArg Subtype.val hH.symm⟩
  · rintro ⟨H,hH⟩
    have hm : H ∈ filtered v (fun i => d i-e i) :=
      (mul_mem_filtered_iff v d e L H hL hdeg hed).mp (hH ▸ Q.property)
    exact ⟨⟨H,hm⟩,Subtype.ext hH.symm⟩

/-- Dimension of the quotient by ALL polynomial multiples of L. The two
finite source dimensions may be supplied by any monomial enumeration. -/
theorem filtered_quotient_finrank (v : ι → σ → ℕ) (d e : ι → ℕ)
    (L : MvPolynomial σ F) (hL : L≠0)
    (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i)
    [Module.Finite F (filtered (F:=F) v d)] :
    Module.finrank F ((filtered (F:=F) v d) ⧸
      LinearMap.range (filteredMul v d e L hL hdeg hed)) =
    Module.finrank F (filtered (F:=F) v d) -
      Module.finrank F (filtered (F:=F) v (fun i => d i-e i)) := by
  have hr := LinearMap.finrank_range_of_inj (filteredMul_injective v d e L hL hdeg hed)
  have hq := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (filteredMul v d e L hL hdeg hed))
  omega

end
end K1_11
end PackSource_K1_11FilteredQuotient

section PackSource_K1_11SourceBox
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open Finset MvPolynomial

/-- Variable order X,Y0,Y1,S,T. -/
def sourceWeights (w : ℕ) : Fin 4 → Fin 5 → ℕ :=
  ![![1,w,w,0,0], ![0,1,1,0,0], ![0,1,0,1,0], ![0,0,1,0,1]]
def sourceBounds (D B s t : ℕ) : Fin 4 → ℕ := ![D,B,s,t]

def tuples (D w B s t : ℕ) : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ × ℕ × ℕ) :=
  (range (B+1)).sigma fun i => (range (B+1-i)).sigma fun j =>
    (range (D+1-w*(i+j))) ×ˢ ((range (s+1-i)) ×ˢ (range (t+1-j)))

def exponent5 (x i j a b : ℕ) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![x,i,j,a,b]

def tupleExponent (c : Σ _ : ℕ, Σ _ : ℕ, ℕ × ℕ × ℕ) : Fin 5 →₀ ℕ :=
  exponent5 c.2.2.1 c.1 c.2.1 c.2.2.2.1 c.2.2.2.2

@[simp] theorem exponent5_apply (x i j a b : ℕ) (q : Fin 5) :
    exponent5 x i j a b q = ![x,i,j,a,b] q := by
  simp [exponent5]

theorem tupleExponent_injective : Function.Injective tupleExponent := by
  intro c d h
  have h0 := congrArg (fun e : Fin 5 →₀ ℕ => e 0) h
  have h1 := congrArg (fun e : Fin 5 →₀ ℕ => e 1) h
  have h2 := congrArg (fun e : Fin 5 →₀ ℕ => e 2) h
  have h3 := congrArg (fun e : Fin 5 →₀ ℕ => e 3) h
  have h4 := congrArg (fun e : Fin 5 →₀ ℕ => e 4) h
  simp only [tupleExponent,exponent5_apply,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons] at h0 h1 h2 h3 h4
  rcases c with ⟨i,j,x,a,b⟩
  rcases d with ⟨i',j',x',a',b'⟩
  dsimp at h0 h1 h2 h3 h4
  subst i'; subst j'; subst x'; subst a'; subst b'
  rfl

@[simp] theorem tuples_card (D w B s t : ℕ) : (tuples D w B s t).card=V D w B s t := by
  simp [tuples,V,card_sigma,Nat.mul_assoc]

def sourceExponents (D w B s t : ℕ) : Finset (Fin 5 →₀ ℕ) :=
  (tuples D w B s t).image tupleExponent

theorem sourceExponents_card (D w B s t : ℕ) :
    (sourceExponents D w B s t).card=V D w B s t := by
  rw [sourceExponents,card_image_of_injective _ tupleExponent_injective,tuples_card]

theorem weight5 (e : Fin 5 →₀ ℕ) (a b c d f : ℕ) :
    e.weight ![a,b,c,d,f]=e 0*a+e 1*b+e 2*c+e 3*d+e 4*f := by
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul]
  omega

/-- Exact membership of the finite exponent box, without any positivity
assumption on D-w*B or on s-B/t-B. -/
theorem mem_sourceExponents (D w B s t : ℕ) (e : Fin 5 →₀ ℕ) :
    e∈sourceExponents D w B s t ↔
    e 0+w*(e 1+e 2)≤D ∧ e 1+e 2≤B ∧ e 1+e 3≤s ∧ e 2+e 4≤t := by
  constructor
  · rintro he
    obtain ⟨⟨i,j,x,a,b⟩,hc,rfl⟩ := mem_image.mp he
    simp only [tuples,mem_sigma,mem_range,mem_product] at hc
    simp [tupleExponent]
    omega
  · rintro ⟨hX,hY,hS,hT⟩
    apply mem_image.mpr
    refine ⟨⟨e 1,e 2,e 0,e 3,e 4⟩,?_,?_⟩
    · simp only [tuples,mem_sigma,mem_range,mem_product]
      omega
    · ext q
      fin_cases q <;> simp [tupleExponent]

/-- The four simultaneous filtrations are literally this finite
monomial coefficient space. -/
theorem source_filtered_eq {F : Type*} [Field F] (D w B s t : ℕ) :
    filtered (F:=F) (sourceWeights w) (sourceBounds D B s t)=
      restrictSupport F (↑(sourceExponents D w B s t) : Set (Fin 5 →₀ ℕ)) := by
  ext P
  rw [mem_filtered]
  simp only [mem_restrictSupport_iff,Finset.mem_coe]
  constructor
  · intro h e he
    apply (mem_sourceExponents D w B s t e).mpr
    have hh q := (le_weightedTotalDegree (sourceWeights w q) he).trans (h q)
    have h0 := hh 0
    have h1 := hh 1
    have h2 := hh 2
    have h3 := hh 3
    simp [sourceWeights,sourceBounds,weight5] at h0 h1 h2 h3
    constructor
    · nlinarith
    · exact ⟨h1,h2,h3⟩
  · intro h q
    apply Finset.sup_le
    change ∀ e∈P.support, _
    intro e he
    have hh := (mem_sourceExponents D w B s t e).mp (h he)
    fin_cases q <;> simp [sourceWeights,sourceBounds,weight5] <;> nlinarith

instance source_filtered_finite {F : Type*} [Field F] (D w B s t : ℕ) :
    Module.Finite F (filtered (F:=F) (sourceWeights w) (sourceBounds D B s t)) := by
  rw [source_filtered_eq]
  exact restrictSupport_finite (Finset.finite_toSet _)

theorem source_filtered_finrank {F : Type*} [Field F] (D w B s t : ℕ) :
    Module.finrank F (filtered (F:=F) (sourceWeights w) (sourceBounds D B s t))=
      V D w B s t := by
  rw [source_filtered_eq,finrank_restrictSupport_finset,sourceExponents_card]

end
end K1_11
end PackSource_K1_11SourceBox

section PackSource_K1_11EliminationDegrees
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open Finset MvPolynomial
variable {F σ : Type*} [Field F]

/-- Weighted denominator-clearing bound. The coefficient condition is
additive, avoiding an invalid truncated subtraction when j*e>d. -/
theorem clearedEval_weight_bound (v : σ → ℕ) (B d e aa bb : ℕ)
    (Q : Polynomial (MvPolynomial σ F)) (a b : MvPolynomial σ F)
    (hcoeff : ∀ j≤B,Q.coeff j≠0 → (Q.coeff j).weightedTotalDegree v+j*e≤d)
    (ha : a.weightedTotalDegree v≤aa) (hb : b.weightedTotalDegree v≤bb)
    (hbalance : aa≤e+bb) :
    (clearedEval B Q a b).weightedTotalDegree v≤d+B*bb := by
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  unfold clearedEval
  apply Submodule.sum_mem
  intro j hj
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
  by_cases hc : Q.coeff j=0
  · simp [hc,weightedTotalDegree]
  have hjB : j≤B := by have := mem_range.mp hj; omega
  have hco := hcoeff j hjB hc
  have hpa := (weightedTotalDegree_pow_le v a j).trans (Nat.mul_le_mul_left j ha)
  have hpb := (weightedTotalDegree_pow_le v b (B-j)).trans (Nat.mul_le_mul_left (B-j) hb)
  have hm := (weightedTotalDegree_mul_le v (Q.coeff j*a^j) (b^(B-j))).trans
    (Nat.add_le_add ((weightedTotalDegree_mul_le v _ _).trans (Nat.add_le_add_left hpa _)) hpb)
  have hjadd : j+(B-j)=B := Nat.add_sub_of_le hjB
  have hbal := Nat.mul_le_mul_left j hbalance
  nlinarith

end
end K1_11
end PackSource_K1_11EliminationDegrees

section PackSource_K1_11PolynomialView
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial
variable {F : Type*} [Field F]

/-- Old X,Y0,Y1,S,T become Y1,X,Y0,S,T before peeling the first variable. -/
def decoderPermutation : Fin 5 ≃ Fin 5 :=
  Equiv.ofBijective ![1,2,0,3,4] (by decide)

def polynomialView : MvPolynomial (Fin 5) F ≃ₐ[F] Polynomial (MvPolynomial (Fin 4) F) :=
  (renameEquiv F decoderPermutation).trans (finSuccEquiv F 4)

def scalarWeightY : Fin 4 → ℕ := ![0,1,0,0]
def scalarWeightYS : Fin 4 → ℕ := ![0,1,1,0]
def scalarWeightT : Fin 4 → ℕ := ![0,0,0,1]

/-- A coefficient monomial of the peeled polynomial comes from an actual
source monomial, with ALL original coordinates identified. -/
theorem polynomialView_coeff_support (Q : MvPolynomial (Fin 5) F) (j : ℕ)
    (f : Fin 4 →₀ ℕ) (hf : f∈((polynomialView Q).coeff j).support) :
    ∃ e∈Q.support,e 0=f 0 ∧ e 1=f 1 ∧ e 2=j ∧ e 3=f 2 ∧ e 4=f 3 := by
  have hc := mem_support_iff.mp hf
  change ((finSuccEquiv F 4 (rename decoderPermutation Q)).coeff j).coeff f≠0 at hc
  rw [finSuccEquiv_coeff_coeff] at hc
  obtain ⟨e,he,hcoeff⟩ := coeff_rename_ne_zero decoderPermutation Q (f.cons j) hc
  refine ⟨e,mem_support_iff.mpr hcoeff,?_⟩
  have hh (i : Fin 5) := congrArg (fun z : Fin 5 →₀ ℕ => z (decoderPermutation i)) he
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  have h4 := hh 4
  simp only [Finsupp.mapDomain_apply_of_injective decoderPermutation.injective] at h0 h1 h2 h3 h4
  simp [decoderPermutation] at h0 h1 h2 h3 h4
  exact ⟨h0,h1,h2,h3,h4⟩

/-- A nonzero polynomial with every weighted monomial plus a fixed charge
bounded has its maximum weighted degree plus that same charge bounded. -/
theorem weighted_degree_plus_le {σ : Type*} (v : σ → ℕ) (P : MvPolynomial σ F)
    (c d : ℕ) (hP : P≠0) (h : ∀ e∈P.support,e.weight v+c≤d) :
    P.weightedTotalDegree v+c≤d := by
  obtain ⟨e,he⟩ := support_nonempty.mpr hP
  have hcd : c≤d := by have := h e he; omega
  have hdeg : P.weightedTotalDegree v≤d-c := by
    apply Finset.sup_le
    intro e he
    have := h e he
    omega
  omega

/-- The actual five-variable filtered source gives all three coefficient
bounds required by the scalar elimination theorem. -/
theorem polynomialView_source_coefficients (D w B s t : ℕ)
    (Q : MvPolynomial (Fin 5) F)
    (hQ : Q∈filtered (sourceWeights w) (sourceBounds D B s t)) :
    (∀ j≤B,(polynomialView Q).coeff j≠0 →
      ((polynomialView Q).coeff j).weightedTotalDegree scalarWeightY+j≤B) ∧
    (∀ j≤B,(polynomialView Q).coeff j≠0 →
      ((polynomialView Q).coeff j).weightedTotalDegree scalarWeightYS≤s) ∧
    (∀ j≤B,(polynomialView Q).coeff j≠0 →
      ((polynomialView Q).coeff j).weightedTotalDegree scalarWeightT+j≤t) := by
  have hmono (j : ℕ) (f : Fin 4 →₀ ℕ) (hf : f∈((polynomialView Q).coeff j).support) :
      f 1+j≤B ∧ f 1+f 2≤s ∧ j+f 3≤t := by
    obtain ⟨e,he,he0,he1,he2,he3,he4⟩ := polynomialView_coeff_support Q j f hf
    rw [source_filtered_eq,mem_restrictSupport_iff] at hQ
    have hh := (mem_sourceExponents D w B s t e).mp (hQ he)
    omega
  constructor
  · intro j hj hc
    apply weighted_degree_plus_le scalarWeightY _ j B hc
    intro f hf
    have hh := hmono j f hf
    simpa [scalarWeightY,Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul] using hh.1
  constructor
  · intro j hj hc
    apply Finset.sup_le
    intro f hf
    have hh := hmono j f hf
    simpa [scalarWeightYS,Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul] using hh.2.1
  · intro j hj hc
    apply weighted_degree_plus_le scalarWeightT _ j t hc
    intro f hf
    have hh := hmono j f hf
    simpa [scalarWeightT,Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul,Nat.add_comm] using hh.2.2

theorem polynomialView_natDegree (D w B s t : ℕ) (Q : MvPolynomial (Fin 5) F)
    (hQ : Q∈filtered (sourceWeights w) (sourceBounds D B s t)) :
    (polynomialView Q).natDegree≤B := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_contra hc
  obtain ⟨f,hf⟩ := support_nonempty.mpr hc
  obtain ⟨e,he,he0,he1,he2,he3,he4⟩ := polynomialView_coeff_support Q j f hf
  rw [source_filtered_eq,mem_restrictSupport_iff] at hQ
  have hh := (mem_sourceExponents D w B s t e).mp (hQ he)
  omega

theorem polynomialView_X (i : Fin 5) :
    polynomialView (F:=F) (X i)=
      ![Polynomial.C (X 0),Polynomial.C (X 1),Polynomial.X,
        Polynomial.C (X 2),Polynomial.C (X 3)] i := by
  fin_cases i <;> simp [polynomialView,decoderPermutation,finSuccEquiv_apply,renameEquiv_apply] <;> rfl

def scalarImages (P : Polynomial F) (s t : F) : Fin 4 → Polynomial F :=
  ![Polynomial.X,P,Polynomial.C s,Polynomial.C t]

theorem polynomialView_eval (P Q : Polynomial F) (s t : F) (G : MvPolynomial (Fin 5) F) :
    Polynomial.eval₂ (aeval (scalarImages P s t)).toRingHom Q (polynomialView G)=
      aeval ![Polynomial.X,P,Q,Polynomial.C s,Polynomial.C t] G := by
  have heq : (Polynomial.eval₂RingHom (aeval (scalarImages P s t)).toRingHom Q).comp
      (polynomialView (F:=F)).toRingHom=(aeval ![Polynomial.X,P,Q,Polynomial.C s,Polynomial.C t]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [polynomialView,finSuccEquiv_apply]
    · intro i
      change Polynomial.eval₂ (aeval (scalarImages P s t)).toRingHom Q (polynomialView (X i))=_
      rw [polynomialView_X]
      fin_cases i <;> simp [scalarImages]
  exact RingHom.congr_fun heq G

end
end K1_11
end PackSource_K1_11PolynomialView

section PackSource_K1_11ContactJets
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial Finset
variable {F : Type*} [Field F]

def contactWeight : Fin 5 → ℕ := ![1,1,1,0,0]

abbrev JetSpace (F : Type*) [Field F] (d s t : ℕ) :=
  filtered (F:=F) (sourceWeights 1) (sourceBounds d d s t)

theorem J_eq_V (d s t : ℕ) : J (d+1) s t=V d 1 d s t := by
  unfold J V
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  simp only [one_mul,Nat.sub_sub]

theorem jetSpace_finrank (d s t : ℕ) :
    Module.finrank F (JetSpace F d s t)=J (d+1) s t := by
  rw [J_eq_V]
  exact source_filtered_finrank d 1 d s t

theorem jetSpace_support_bound (d s t : ℕ) (H : JetSpace F d s t) :
    ∀ e∈H.val.support,e.weight contactWeight<d+1 := by
  intro e he
  have hh := (le_weightedTotalDegree (sourceWeights 1 0) he).trans
    ((mem_filtered _ _ _).mp H.property 0)
  simpa [sourceWeights,sourceBounds,contactWeight] using Nat.lt_succ_of_le hh

/-- Truncation cannot increase either parameter filtration; its contact
support lies strictly below d+2. -/
theorem truncated_mul_mem_jet (d s t dS dT : ℕ) (L : MvPolynomial (Fin 5) F)
    (hS : L.weightedTotalDegree (sourceWeights 1 2)≤dS)
    (hT : L.weightedTotalDegree (sourceWeights 1 3)≤dT)
    (H : JetSpace F d s t) :
    weightedTruncation contactWeight (d+2) (L*H.val) ∈ JetSpace F (d+1) (s+dS) (t+dT) := by
  simp only [JetSpace]
  rw [source_filtered_eq,mem_restrictSupport_iff]
  intro e he
  have hc : e.weight contactWeight<d+2 := by
    have he' := mem_support_iff.mp he
    rw [coeff_weightedTruncation] at he'
    by_contra hh
    exact he' (if_neg hh)
  have heL : e∈(L*H.val).support := by
    apply mem_support_iff.mpr
    have := mem_support_iff.mp he
    simpa only [coeff_weightedTruncation,if_pos hc] using this
  have hHs := (mem_filtered _ _ _).mp H.property 2
  have hHt := (mem_filtered _ _ _).mp H.property 3
  have hs := (le_weightedTotalDegree (sourceWeights 1 2) heL).trans
    ((weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add hS hHs))
  have ht := (le_weightedTotalDegree (sourceWeights 1 3) heL).trans
    ((weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add hT hHt))
  apply (mem_sourceExponents (d+1) 1 (d+1) (s+dS) (t+dT) e).mpr
  simp [sourceWeights,sourceBounds,contactWeight,weight5] at hc hs ht ⊢
  omega

end
end K1_11
end PackSource_K1_11ContactJets

section PackSource_K1_11ContactShift
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial
variable {F : Type*} [Field F]

def shiftImages (x a b c d : F) : Fin 5 → MvPolynomial (Fin 5) F :=
  ![X 0+C x,X 1+C a+X 3*C b,X 2+C c+X 4*C d,X 3,X 4]

def contactShift (x a b c d : F) : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval (shiftImages x a b c d)

theorem contactShift_mul (x a b c d : F) (P Q : MvPolynomial (Fin 5) F) :
    contactShift x a b c d (P*Q)=contactShift x a b c d P*contactShift x a b c d Q :=
  map_mul _ _ _

theorem shift_preserves_weight (v : Fin 5 → ℕ) (hv1 : v 1=v 3) (hv2 : v 2=v 4)
    (x a b c d : F) (P : MvPolynomial (Fin 5) F) :
    (contactShift x a b c d P).weightedTotalDegree v≤P.weightedTotalDegree v := by
  apply weightedTotalDegree_aeval_le_of_le v v
  intro i
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  fin_cases i
  · change X 0+C x∈restrictWeightedDegree v (v 0)
    exact Submodule.add_mem _ (X_mem_restrictWeightedDegree v _ _ le_rfl)
      (C_mem_restrictWeightedDegree v _ _)
  · change X 1+C a+X 3*C b∈restrictWeightedDegree v (v 1)
    apply Submodule.add_mem _
      (Submodule.add_mem _ (X_mem_restrictWeightedDegree v _ _ le_rfl)
        (C_mem_restrictWeightedDegree v _ _))
    have hm := mul_mem_restrictWeightedDegree
      (X_mem_restrictWeightedDegree (R:=F) v (v 3) 3 le_rfl)
      (C_mem_restrictWeightedDegree (R:=F) v 0 b)
    simpa [hv1] using hm
  · change X 2+C c+X 4*C d∈restrictWeightedDegree v (v 2)
    apply Submodule.add_mem _
      (Submodule.add_mem _ (X_mem_restrictWeightedDegree v _ _ le_rfl)
        (C_mem_restrictWeightedDegree v _ _))
    have hm := mul_mem_restrictWeightedDegree
      (X_mem_restrictWeightedDegree (R:=F) v (v 4) 4 le_rfl)
      (C_mem_restrictWeightedDegree (R:=F) v 0 d)
    simpa [hv2] using hm
  · change X 3∈restrictWeightedDegree v (v 3)
    exact X_mem_restrictWeightedDegree v _ _ le_rfl
  · change X 4∈restrictWeightedDegree v (v 4)
    exact X_mem_restrictWeightedDegree v _ _ le_rfl

/-- Both original parameter filtrations survive affine contact translation. -/
theorem contactShift_parameter_weights (x a b c d : F) (P : MvPolynomial (Fin 5) F) :
    (contactShift x a b c d P).weightedTotalDegree (sourceWeights 1 2)≤
      P.weightedTotalDegree (sourceWeights 1 2) ∧
    (contactShift x a b c d P).weightedTotalDegree (sourceWeights 1 3)≤
      P.weightedTotalDegree (sourceWeights 1 3) := by
  constructor <;> apply shift_preserves_weight <;> decide

/-- Truncate ANY polynomial with bounded parameter weights to the finite
contact jet space. No bound on its full contact degree is needed. -/
theorem trunc_mem_jet_of_parameters (d s t : ℕ) (P : MvPolynomial (Fin 5) F)
    (hS : P.weightedTotalDegree (sourceWeights 1 2)≤s)
    (hT : P.weightedTotalDegree (sourceWeights 1 3)≤t) :
    weightedTruncation contactWeight (d+1) P∈JetSpace F d s t := by
  simp only [JetSpace]
  rw [source_filtered_eq,mem_restrictSupport_iff]
  intro e he
  have hc : e.weight contactWeight<d+1 := by
    have hh := mem_support_iff.mp he
    rw [coeff_weightedTruncation] at hh
    by_contra hn
    exact hh (if_neg hn)
  have heP : e∈P.support := by
    apply mem_support_iff.mpr
    have := mem_support_iff.mp he
    simpa only [coeff_weightedTruncation,if_pos hc] using this
  have hs := (le_weightedTotalDegree (sourceWeights 1 2) heP).trans hS
  have ht := (le_weightedTotalDegree (sourceWeights 1 3) heP).trans hT
  apply (mem_sourceExponents d 1 d s t e).mpr
  simp [sourceWeights,contactWeight,weight5] at hc hs ht ⊢
  omega

def sourceToJet (D w B s t d : ℕ) (x a b c e : F) :
    filtered (F:=F) (sourceWeights w) (sourceBounds D B s t) →ₗ[F] JetSpace F d s t where
  toFun Q := ⟨weightedTruncation contactWeight (d+1) (contactShift x a b c e Q.val),by
    apply trunc_mem_jet_of_parameters
    · exact (contactShift_parameter_weights x a b c e Q.val).1.trans
        ((mem_filtered _ _ _).mp Q.property 2)
    · exact (contactShift_parameter_weights x a b c e Q.val).2.trans
        ((mem_filtered _ _ _).mp Q.property 3)⟩
  map_add' Q R := by apply Subtype.ext; simp
  map_smul' a Q := by apply Subtype.ext; simp

end
end K1_11
end PackSource_K1_11ContactShift

section PackSource_K1_11ContactMembership
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial Polynomial
variable {F : Type*} [Field F]

/-- Contact modulo L pulls back to ordinary polynomial multiplicity whenever
L vanishes and the three contact coordinates vanish to first order. The
parameter coordinates have weight zero, so their values need not be units. -/
theorem contact_mod_relation_pullback {σ : Type*} (v : σ → ℕ) (m : ℕ)
    (P L H : MvPolynomial σ F) (g : σ → F[X]) (z : F[X])
    (hcontact : P-L*H∈restrictWeightedOrder v m)
    (hg : ∀ i,z^(v i) ∣ g i)
    (hL : eval₂Hom Polynomial.C g L=0) :
    z^m ∣ eval₂Hom Polynomial.C g P := by
  have hd := pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder Polynomial.C hcontact hg
  simpa only [map_sub,map_mul,hL,zero_mul,sub_zero] using hd

end
end K1_11
end PackSource_K1_11ContactMembership

section PackSource_K1_11DecoderPullback
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial Finset
variable {F : Type*} [Field F]

/-- The two decoder variables remain the ORIGINAL code polynomials. -/
def decoderImages (P Q : Polynomial F) (s t : F) : Fin 5 → Polynomial F :=
  ![Polynomial.X,P,Q,Polynomial.C s,Polynomial.C t]

def contactDecoderImages (x a b c d s t : F) (P Q : Polynomial F) : Fin 5 → Polynomial F :=
  ![Polynomial.X-Polynomial.C x,P-Polynomial.C (a+s*b),
    Q-Polynomial.C (c+t*d),Polynomial.C s,Polynomial.C t]

theorem decoder_contact_composition (x a b c d s t : F) (P Q : Polynomial F)
    (G : MvPolynomial (Fin 5) F) :
    aeval (contactDecoderImages x a b c d s t P Q) (contactShift x a b c d G)=
      aeval (decoderImages P Q s t) G := by
  rw [contactShift,aeval_eq_bind₁,aeval_bind₁]
  have hf : (fun i => aeval (contactDecoderImages x a b c d s t P Q) (shiftImages x a b c d i))=decoderImages P Q s t := by
    funext i
    fin_cases i <;> simp [shiftImages,contactDecoderImages,decoderImages] <;> ring
  rw [hf]

theorem contactDecoderImages_vanish (x a b c d s t : F) (P Q : Polynomial F)
    (hP : P.eval x=a+s*b) (hQ : Q.eval x=c+t*d) :
    ∀ i,(Polynomial.X-Polynomial.C x)^contactWeight i∣
      contactDecoderImages x a b c d s t P Q i := by
  have hp : (Polynomial.X-Polynomial.C x)∣P-Polynomial.C (a+s*b) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [hP]
  have hq : (Polynomial.X-Polynomial.C x)∣Q-Polynomial.C (c+t*d) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [hQ]
  simp only [Polynomial.C_add,Polynomial.C_mul] at hp hq
  intro i
  fin_cases i <;> simp [contactWeight,contactDecoderImages,hp,hq]

/-- Actual correct-node contact multiplicity after quotienting by L. -/
theorem decoder_contact_multiplicity (m : ℕ) (x a b c d s t : F)
    (P Q : Polynomial F) (G L H : MvPolynomial (Fin 5) F)
    (hP : P.eval x=a+s*b) (hQ : Q.eval x=c+t*d)
    (hL : aeval (decoderImages P Q s t) L=0)
    (hcontact : contactShift x a b c d G-contactShift x a b c d L*H∈
      restrictWeightedOrder contactWeight m) :
    (Polynomial.X-Polynomial.C x)^m∣aeval (decoderImages P Q s t) G := by
  have hh := contact_mod_relation_pullback contactWeight m
    (contactShift x a b c d G) (contactShift x a b c d L) H
    (contactDecoderImages x a b c d s t P Q) (Polynomial.X-Polynomial.C x)
    hcontact (contactDecoderImages_vanish x a b c d s t P Q hP hQ)
    (by
      change aeval (contactDecoderImages x a b c d s t P Q) (contactShift x a b c d L)=0
      rw [decoder_contact_composition]
      exact hL)
  change (Polynomial.X-Polynomial.C x)^m∣aeval (contactDecoderImages x a b c d s t P Q) (contactShift x a b c d G) at hh
  rwa [decoder_contact_composition] at hh

/-- The weighted source degree controls substitution by every actual
pair of degree<=w decoders, independently of the source's ordinary X-degree. -/
theorem decoder_eval_degree (w D : ℕ) (G : MvPolynomial (Fin 5) F)
    (hG : G.weightedTotalDegree (sourceWeights w 0)≤D)
    (P Q : Polynomial F) (hP : P.natDegree≤w) (hQ : Q.natDegree≤w) (s t : F) :
    (aeval (decoderImages P Q s t) G).natDegree≤D := by
  apply (natDegree_aeval_le_weightedTotalDegree_of_le (sourceWeights w 0)
    (decoderImages P Q s t) G ?_).trans hG
  intro i
  fin_cases i <;> simp [decoderImages,sourceWeights] <;> assumption

/-- A polynomial with m contacts at each distinct node is zero once its
weighted degree is strictly below m times the number of correct nodes. -/
theorem eq_zero_of_many_contacts {ι : Type*} (S : Finset ι) (x : ι → F)
    (hx : Function.Injective x) (m : ℕ) (Q : Polynomial F)
    (hcontact : ∀ i∈S,(Polynomial.X-Polynomial.C (x i))^m∣Q)
    (hdeg : Q.natDegree<m*S.card) : Q=0 := by
  classical
  by_contra hQ
  have hp : (∏ i∈S,(Polynomial.X-Polynomial.C (x i))^m)∣Q := by
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      exact (Polynomial.pairwise_coprime_X_sub_C hx hij).pow
    · exact hcontact
  have hd := Polynomial.natDegree_le_of_dvd hp hQ
  have hne : ∀ i∈S,(Polynomial.X-Polynomial.C (x i))^m≠0 := by
    intro i hi
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  rw [Polynomial.natDegree_prod _ _ hne] at hd
  simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,Nat.mul_one,
    Finset.sum_const,smul_eq_mul] at hd
  nlinarith

end
end K1_11
end PackSource_K1_11DecoderPullback

section PackSource_K1_11ScalarEliminant
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

namespace K1_11
noncomputable section
open MvPolynomial
variable {F : Type*} [Field F]

/-- Scalar annihilator in X,Y0,S,T after clearing the Y1 denominator. -/
def scalarEliminant (B : ℕ) (G : MvPolynomial (Fin 5) F)
    (a b : MvPolynomial (Fin 4) F) : MvPolynomial (Fin 4) F :=
  clearedEval B (polynomialView G) a b

theorem scalarEliminant_ne_zero (D w B s t : ℕ) (G L : MvPolynomial (Fin 5) F)
    (hG : G∈filtered (sourceWeights w) (sourceBounds D B s t))
    (hnot : ¬ L∣G) (a b : MvPolynomial (Fin 4) F) (hb : b≠0)
    (hlinear : polynomialView L=Polynomial.C b*Polynomial.X-Polynomial.C a)
    (hprimitive : (Polynomial.C b*Polynomial.X-Polynomial.C a).IsPrimitive) :
    scalarEliminant B G a b≠0 := by
  have hnd : ¬ (Polynomial.C b*Polynomial.X-Polynomial.C a)∣polynomialView G := by
    rintro ⟨H,hH⟩
    apply hnot
    refine ⟨polynomialView.symm H,?_⟩
    apply polynomialView.injective
    rw [map_mul,hlinear,AlgEquiv.apply_symm_apply]
    exact hH
  letI : GCDMonoid (MvPolynomial (Fin 4) F) := UniqueFactorizationMonoid.toGCDMonoid _
  exact clearedEval_ne_zero (K:=FractionRing (MvPolynomial (Fin 4) F)) B
    (polynomialView G) (polynomialView_natDegree D w B s t G hG) a b hb hprimitive hnd

/-- Specialized zero denominators are covered by a polynomial identity,
not division. The output still annihilates the ORIGINAL Y0 decoder. -/
theorem scalarEliminant_annihilates (D w B s t : ℕ) (G L : MvPolynomial (Fin 5) F)
    (hG : G∈filtered (sourceWeights w) (sourceBounds D B s t))
    (a b : MvPolynomial (Fin 4) F)
    (hlinear : polynomialView L=Polynomial.C b*Polynomial.X-Polynomial.C a)
    (P Q : Polynomial F) (s0 t0 : F)
    (hL : aeval (decoderImages P Q s0 t0) L=0)
    (hzero : aeval (decoderImages P Q s0 t0) G=0) :
    aeval (scalarImages P s0 t0) (scalarEliminant B G a b)=0 := by
  let φ : MvPolynomial (Fin 4) F →+* Polynomial F := (aeval (scalarImages P s0 t0)).toRingHom
  have hroot : Polynomial.eval Q ((polynomialView G).map φ)=0 := by
    rw [Polynomial.eval_map,polynomialView_eval]
    exact hzero
  have hrel : φ b*Q=φ a := by
    have hh := polynomialView_eval P Q s0 t0 L
    rw [hlinear] at hh
    have hz : Polynomial.eval₂ φ Q (Polynomial.C b*Polynomial.X-Polynomial.C a)=0 :=
      hh.trans hL
    apply sub_eq_zero.mp
    simpa only [Polynomial.eval₂_sub,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_X] using hz
  have hd : ((polynomialView G).map φ).natDegree≤B :=
    Polynomial.natDegree_map_le.trans (polynomialView_natDegree D w B s t G hG)
  have hh := clearedEval_zero_of_root B ((polynomialView G).map φ) hd (φ a) (φ b) Q hrel hroot
  rw [← map_clearedEval] at hh
  exact hh

end
end K1_11
end PackSource_K1_11ScalarEliminant

section PackSource_C42OriginGrading
set_option autoImplicit true
/-! Actual origin coefficient-map preservation of the second block grading g.
Together with the pinned total-jet grading this gives the off-block zeros;
full finite support/reindexing and uniform-rank transport remain separate. -/
namespace Sol1.C42

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
variable {R : Type*} [CommRing R]

def sourceBalance : JetVariable 2 → ℤ
  | none => 1
  | some j => -(j.val : ℤ)

def localBalance : LocalVariable 2 → ℤ
  | none => 1
  | some none => -1
  | some (some j) => -((j.val : ℤ) + 1)

theorem localCorrection_balance :
    (localCorrection (R := R) 2).IsWeightedHomogeneous localBalance 0 := by
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hC := isWeightedHomogeneous_C localBalance ((-1 : R) ^ j.val)
  have hT := (isWeightedHomogeneous_X R localBalance (localT 2)).pow (j.val + 1)
  have hY := isWeightedHomogeneous_X R localBalance (localY j)
  simpa [localBalance, localT, localY, nsmul_eq_mul] using (hC.mul hT).mul hY

theorem origin_image_balance (v : JetVariable 2) :
    (unscaledLocalImage 2 (0 : R) 0 v).IsWeightedHomogeneous localBalance (sourceBalance v) := by
  have hX := isWeightedHomogeneous_X R localBalance
  rcases v with _ | j
  · simpa [unscaledLocalImage, sourceBalance, localBalance, localT] using hX (localT 2)
  · refine Fin.cases ?_ (fun i ↦ ?_) j
    · have hTE : (X (localT 2) * X (localE 2) : LocalPolynomial R 2).IsWeightedHomogeneous
          localBalance 0 := by
        simpa [localBalance, localT, localE, localAux] using (hX (localT 2)).mul (hX (localE 2))
      simpa [unscaledLocalImage, sourceBalance] using localCorrection_balance.add hTE
    · simpa [unscaledLocalImage, sourceBalance, localBalance, localY] using hX (localY i)

theorem origin_substitution_balance {Q : DifferentialPolynomial R 2} {g : ℤ}
    (hQ : Q.IsWeightedHomogeneous sourceBalance g) :
    (unscaledLocalSubstitution 2 0 0 Q).IsWeightedHomogeneous localBalance g :=
  hQ.bind₁ origin_image_balance

theorem origin_constraint_balance (m : ℕ) {Q : DifferentialPolynomial R 2} {g : ℤ}
    (hQ : Q.IsWeightedHomogeneous sourceBalance g) :
    (localConstraintAt m 0 0 Q).IsWeightedHomogeneous localBalance g :=
  (origin_substitution_balance hQ).weightedTruncation _ m

theorem column_balance (i : SourceIndex) :
    ((columns i).polynomial : DifferentialPolynomial R 2).IsWeightedHomogeneous sourceBalance
      ((i.2.val : ℤ) - e1 i.1 - 2 * e2 i.1) := by
  rw [SourceColumn.polynomial_eq_sourceMonomial]
  have h := sourceMonomial_isWeightedHomogeneous (R := R) sourceBalance
    (columns i).x (columns i).y₀ (columns i).higher
  convert h using 1
  simp [sourceBalance, columns, Fin.sum_univ_two]
  ring

/-- Actual low-contact coefficients vanish off the source g block. -/
theorem origin_coefficient_zero_of_balance_ne
    (m : ℕ) (i : SourceIndex) (row : LocalVariable 2 →₀ ℕ)
    (hne : row.weight localBalance ≠ (i.2.val : ℤ) - e1 i.1 - 2 * e2 i.1) :
    (localConstraintAt (R := R) m 0 0 (columns i).polynomial).coeff row = 0 :=
  (origin_constraint_balance m (column_balance i)).coeff_eq_zero row hne

theorem column_jet_homogeneous (i : SourceIndex) :
    ((columns i).polynomial : DifferentialPolynomial R 2).IsWeightedHomogeneous
      jetDegreeWeight i.1.1.val := by
  rw [SourceColumn.polynomial_eq_sourceMonomial]
  have h := sourceMonomial_isWeightedHomogeneous_jetDegreeWeight (R := R)
    (columns i).x (columns i).y₀ (columns i).higher
  have hdegree : (columns i).y₀ + ∑ j, (columns i).higher j = i.1.1.val := by
    simpa [columns, Fin.sum_univ_two, Nat.add_assoc] using jet_total i.1
  rw [hdegree] at h
  exact h

theorem origin_coefficient_zero_of_jet_ne
    (m : ℕ) (i : SourceIndex) (row : LocalVariable 2 →₀ ℕ)
    (hne : row.weight (localJetDegreeWeight 2) ≠ i.1.1.val) :
    (localConstraintAt (R := R) m 0 0 (columns i).polynomial).coeff row = 0 :=
  (localConstraintAt_isWeightedHomogeneous 0 (column_jet_homogeneous i)).coeff_eq_zero row hne

/-- High global X powers are actually killed by the origin contact map. -/
theorem origin_high_X_zero (m : ℕ) (i : SourceIndex) (hlarge : m ≤ (columns i).x) :
    localConstraintAt (R := R) m 0 0 (columns i).polynomial = 0 := by
  have hsource : (X (none : JetVariable 2) : DifferentialPolynomial R 2) ^ (columns i).x ∣
      (columns i).polynomial := by
    rw [SourceColumn.polynomial_eq_sourceMonomial, sourceMonomial]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hmap := map_dvd (unscaledLocalSubstitution 2 (0 : R) 0).toRingHom hsource
  change unscaledLocalSubstitution 2 0 0
      ((X (none : JetVariable 2)) ^ (columns i).x) ∣
    unscaledLocalSubstitution 2 0 0 (columns i).polynomial at hmap
  simp only [map_pow, unscaledLocalSubstitution_X, C_0, zero_add] at hmap
  obtain ⟨G, hG⟩ := hmap
  rw [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    projectLowContact, weightedTruncation_eq_zero_iff, hG]
  have hT := pow_mem_restrictWeightedOrder (R := R)
    (X_mem_restrictWeightedOrder (localContactWeight 2) (localT 2) le_rfl) (columns i).x
  have hrest : G ∈ restrictWeightedOrder (localContactWeight 2) 0 := by simp
  refine restrictWeightedOrder_anti _ ?_ (mul_mem_restrictWeightedOrder hT hrest)
  simpa only [localContactWeight_T, add_zero, one_mul, mul_one] using hlarge


end Sol1.C42
end PackSource_C42OriginGrading
