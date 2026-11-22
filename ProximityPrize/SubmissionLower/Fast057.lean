import ProximityPrize.SubmissionLower.Fast051
import ProximityPrize.SubmissionLower.Fast052
import ProximityPrize.SubmissionLower.Fast053
set_option autoImplicit true
section
set_option maxSynthPendingDepth 8
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3R
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators Classical
open private pair_membership full_membership buffered_power paid_complement
  terminal_shape_data terminal_power from ProximityPrize.SubmissionLower.Pack_K1_14_3Split
def c1 : Prop :=
  ∀ (q : Surface) (P : Jet) (k : ℕ), Parent q → k < p →
    (∀ a b : ℕ, a + b < k → seedHasse 1 b (seedHasse 0 a P) ∈ q.asIdeal) →
    OrderAt q P k
end
end K1_14_3R
end
section
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3R_3
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators
end
end K1_14_3R_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3R_3_1
noncomputable section
open K1_14 K1_14_3 K1_14_3R_3 Polynomial
open scoped BigOperators RatFunc
def curveIdeal (q : Surface) : Ideal SectionJet :=
  q.asIdeal.map sectionMap ⊔ Ideal.span {lineEquation .seed}
abbrev Curve (q : Surface) := SectionJet ⧸ curveIdeal q
def toCurve (q : Surface) : SectionJet →ₐ[SectionField] Curve q :=
  Ideal.Quotient.mkₐ SectionField (curveIdeal q)
section FunctionField
variable (k : Type) {F : Type} [Field k] [Field F] [Algebra k F]
def SeparatingParameter (t : F) : Prop :=
  Transcendental k t ∧
    FiniteDimensional (IntermediateField.adjoin k ({t} : Set F)) F ∧
    Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F
def functionDegree (x : F) : ℕ := by
  classical
  exact if IsAlgebraic k x then 0 else
    Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F
@[instance_reducible]
def pencilAlgebra : Algebra (RatFunc k) (RatFunc F) :=
  (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k F))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap k F).injective))).toAlgebra
def jetPencilDegree (y v : F) : ℕ :=
  letI := pencilAlgebra k (F := F)
  functionDegree (RatFunc k)
    (algebraMap F (RatFunc F) y + RatFunc.X * algebraMap F (RatFunc F) v)
end FunctionField
section AffineCurve
def toFunction {A : Type} [CommRing A] [IsDomain A] (a : A) : FractionRing A :=
  algebraMap A (FractionRing A) a
variable (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
structure PoleProfile (t y v : A) where
  places : ℕ
  order : Fin places → A → ℕ
  weight : Fin places → ℕ
  scalar : ∀ p c, order p (algebraMap k A c) = 0
  add : ∀ p f g, order p (f + g) ≤ max (order p f) (order p g)
  mul : ∀ p f g, order p (f * g) ≤ order p f + order p g
  degree_le : ∀ f, functionDegree k (toFunction f) ≤ ∑ p, weight p * order p f
  seed_degree : (∑ p, weight p * order p t) = functionDegree k (toFunction t)
  ordinate_degree : (∑ p, weight p * order p y) = functionDegree k (toFunction y)
  jet_degree : (∑ p, weight p * max (order p y) (order p v)) =
    jetPencilDegree k (toFunction y) (toFunction v)
end AffineCurve
end
end K1_14_3R_3_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1600000
set_option maxRecDepth 2500
namespace K1_14_3R_3_1_2
noncomputable section
open K1_14 K1_14_3 K1_14_3R_3_1 K1_14_3_2_7 Polynomial
open scoped nonZeroDivisors
abbrev LineField := FractionRing (MvPolynomial (Fin 2) FX)
abbrev LineJet := Four LineField
def lineParam (i : Fin 2) : LineField :=
  algebraMap (MvPolynomial (Fin 2) FX) LineField (MvPolynomial.X i)
def lineMap : Jet →+* LineJet := extendScalars (algebraMap FX LineField)
def lineIdeal (q : Surface) : Ideal LineJet :=
  q.asIdeal.map lineMap ⊔ Ideal.span
    {seedVar 0 + scalar (lineParam 0) * seedVar 1 - scalar (lineParam 1)}
abbrev LineCurve (q : Surface) := LineJet ⧸ lineIdeal q
def rationalMap {k F : Type} [Field k] [Field F] (f : k →+* F) :
    RatFunc k →+* RatFunc F :=
  RatFunc.mapRingHom (Polynomial.mapRingHom f)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ f.injective))
structure RationalLineModel (K E k F : Type) [Field K] [Field E] [Field k] [Field F]
    [Algebra K E] [Algebra k F] (t y v : E) (t' y' v' : F) where
  base : K ≃+* RatFunc (RatFunc k)
  space : E ≃+* RatFunc (RatFunc F)
  commutes : (rationalMap (rationalMap (algebraMap k F))).comp base.toRingHom =
    space.toRingHom.comp (algebraMap K E)
  seed : space t = algebraMap (RatFunc F) (RatFunc (RatFunc F)) (algebraMap F (RatFunc F) t')
  ordinate : space y = algebraMap (RatFunc F) (RatFunc (RatFunc F)) (algebraMap F (RatFunc F) y')
  derivative : space v = algebraMap (RatFunc F) (RatFunc (RatFunc F)) (algebraMap F (RatFunc F) v')
section Slope
variable (k A : Type) [Field k] [CommRing A] [Algebra k A]
abbrev SlopeRing :=
  Localized (Polynomial.mapRingHom (algebraMap k A))
instance [IsDomain A] : IsDomain (SlopeRing k A) := by
  let f := Polynomial.mapRingHom (algebraMap k A)
  change IsDomain (Localized f)
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (M := denominators f)
  exact Submonoid.map_le_iff_le_comap.mpr
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f
      (Polynomial.map_injective _ (algebraMap k A).injective))
instance : Algebra (RatFunc k) (SlopeRing k A) :=
  Algebra.compHom _ (RatFunc.toFractionRingRingEquiv k).toRingHom
end Slope
end
end K1_14_3R_3_1_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000
namespace K1_14_3R_3_1_2
noncomputable section
open K1_14_3R_3_1
section RatFuncMap
variable {k l F : Type} [Field k] [Field l] [Field F]
@[simp] theorem rationalMap_poly (f : k →+* l) (p : Polynomial k) :
    rationalMap f (algebraMap (Polynomial k) (RatFunc k) p) =
      algebraMap (Polynomial l) (RatFunc l) (p.map f) := by
  have h := RatFunc.map_apply_div (Polynomial.mapRingHom f)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ f.injective)) p 1
  simpa [rationalMap, RatFunc.coe_mapRingHom_eq_coe_map] using h
@[simp] theorem rationalMap_constant (f : k →+* l) (a : k) :
    rationalMap f (algebraMap k (RatFunc k) a) = algebraMap l (RatFunc l) (f a) := by
  change rationalMap f (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C a)) =
    algebraMap (Polynomial l) (RatFunc l) (Polynomial.C (f a))
  rw [rationalMap_poly, Polynomial.map_C]
@[simp] theorem rationalMap_variable (f : k →+* l) :
    rationalMap f RatFunc.X = RatFunc.X := by
  simp [← RatFunc.algebraMap_X]
end RatFuncMap
section Degree
variable {k l F G : Type} [Field k] [Field l] [Field F] [Field G]
  [Algebra k F] [Algebra l G]
end Degree
end
end K1_14_3R_3_1_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace K1_14_3R_3_1_2
noncomputable section
open K1_14_3R_3_1 K1_14_3_2_7 Polynomial
open scoped nonZeroDivisors
attribute [local instance] Polynomial.algebra
theorem polynomial_fraction (A F : Type) [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] : IsFractionRing (Polynomial A) (RatFunc F) := by
  let M := (nonZeroDivisors A).map (C : A →+* Polynomial A).toMonoidHom
  let : IsLocalization M (Polynomial F) := Polynomial.isLocalization (nonZeroDivisors A) F
  have h := IsLocalization.localization_localization_isLocalization_of_has_all_units
    M (nonZeroDivisors (Polynomial F)) (RatFunc F) (fun _ hx => hx.mem_nonZeroDivisors)
  have he :
      (nonZeroDivisors (Polynomial F)).comap (algebraMap (Polynomial A) (Polynomial F)) =
        nonZeroDivisors (Polynomial A) := by
    ext x
    change algebraMap (Polynomial A) (Polynomial F) x ∈ nonZeroDivisors (Polynomial F) ↔
      x ∈ nonZeroDivisors (Polynomial A)
    rw [mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
    exact not_congr (map_eq_zero_iff _ (Polynomial.map_injective _ (IsFractionRing.injective A F)))
  rw [he] at h
  exact h
end
end K1_14_3R_3_1_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace K1_14_3R_3_1
noncomputable section
open K1_14 K1_14_3 K1_14_3R_3 Polynomial
open K1_14_3_2_4 (parameter seedVar ordinateVar derivativeVar)
open scoped BigOperators
section PoleEstimates
variable {k A : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
  {t y v : A} (D : PoleProfile k A t y v) (p : Fin D.places)
end PoleEstimates
end
end K1_14_3R_3_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace K1_14_3R_3_1_2
noncomputable section
open K1_14_3R_3_1
open scoped Polynomial.Bivariate
attribute [local instance] Polynomial.algebra
section Swap
variable (k : Type) [Field k]
local instance : IsFractionRing (Polynomial (Polynomial k)) (RatFunc (RatFunc k)) :=
  polynomial_fraction (Polynomial k) (RatFunc k)
def rationalSwap : RatFunc (RatFunc k) ≃+* RatFunc (RatFunc k) :=
  IsFractionRing.ringEquivOfRingEquiv (Polynomial.Bivariate.swap (R := k)).toRingEquiv
private theorem rationalSwap_poly (p : Polynomial (Polynomial k)) :
    rationalSwap k (algebraMap (Polynomial (Polynomial k)) (RatFunc (RatFunc k)) p) =
      algebraMap (Polynomial (Polynomial k)) (RatFunc (RatFunc k))
        (Polynomial.Bivariate.swap p) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ p
private theorem bivariateMap (p : Polynomial (Polynomial k)) :
    algebraMap (Polynomial (Polynomial k)) (RatFunc (RatFunc k)) p =
      algebraMap (Polynomial (RatFunc k)) (RatFunc (RatFunc k))
        (p.map (algebraMap (Polynomial k) (RatFunc k))) := by
  rw [IsScalarTower.algebraMap_apply (Polynomial (Polynomial k)) (Polynomial (RatFunc k))]
  rfl
@[simp] theorem rationalSwap_inner :
    rationalSwap k (algebraMap (RatFunc k) (RatFunc (RatFunc k)) RatFunc.X) = RatFunc.X := by
  have h := rationalSwap_poly k (Polynomial.C (Polynomial.X : Polynomial k))
  simpa [bivariateMap, Polynomial.Bivariate.swap_X, RatFunc.algebraMap_X,
    ← RatFunc.algebraMap_eq_C] using h
@[simp] theorem rationalSwap_outer :
    rationalSwap k RatFunc.X = algebraMap (RatFunc k) (RatFunc (RatFunc k)) RatFunc.X := by
  have h := rationalSwap_poly k (Polynomial.X : Polynomial (Polynomial k))
  simpa [bivariateMap, Polynomial.Bivariate.swap_Y, RatFunc.algebraMap_X,
    ← RatFunc.algebraMap_eq_C] using h
@[simp] theorem rationalSwap_constant (x : k) :
    rationalSwap k (algebraMap (RatFunc k) (RatFunc (RatFunc k))
      (algebraMap k (RatFunc k) x)) = algebraMap (RatFunc k) (RatFunc (RatFunc k))
        (algebraMap k (RatFunc k) x) := by
  have h := rationalSwap_poly k (Polynomial.C (Polynomial.C x))
  simpa [bivariateMap, Polynomial.Bivariate.swap_C_C, ← RatFunc.algebraMap_eq_C] using h
end Swap
end
end K1_14_3R_3_1_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace K1_14_3R_3_1_2
noncomputable section
open K1_14_3R_3_1 Polynomial
open scoped nonZeroDivisors
attribute [local instance] Polynomial.algebra
section Unused
variable {k F : Type} [Field k] [Field F] [Algebra k F]
end Unused
end
end K1_14_3R_3_1_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace K1_14_3R_3_1_2_1
noncomputable section
open K1_14 K1_14_3 K1_14_3R_3_1_2 Polynomial
attribute [local instance] Polynomial.algebra
abbrev Bi (A : Type) [CommRing A] := Polynomial (Polynomial A)
abbrev Params (A : Type) [CommRing A] := MvPolynomial (Fin 2) A
abbrev Rats (F : Type) [Field F] := RatFunc (RatFunc F)
def twoVars (A : Type) [CommRing A] : Params A ≃+* Bi A :=
  (MvPolynomial.finSuccEquiv A 1).toRingEquiv.trans
    (Polynomial.mapEquiv ((MvPolynomial.finSuccEquiv A 0).toRingEquiv.trans
      (Polynomial.mapEquiv (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).toRingEquiv)))
@[simp] theorem twoVars_C (A : Type) [CommRing A] (x : A) :
    twoVars A (MvPolynomial.C x) = C (C x) := by
  simp [twoVars, MvPolynomial.finSuccEquiv_apply, Polynomial.mapEquiv]
@[simp] theorem twoVars_X_zero (A : Type) [CommRing A] :
    twoVars A (MvPolynomial.X 0) = Polynomial.X := by
  simp [twoVars, MvPolynomial.finSuccEquiv_X_zero, Polynomial.mapEquiv]
@[simp] theorem twoVars_X_one (A : Type) [CommRing A] :
    twoVars A (MvPolynomial.X 1) = C Polynomial.X := by
  change Polynomial.map _ (MvPolynomial.finSuccEquiv A 1 (MvPolynomial.X (Fin.succ 0))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  change C (Polynomial.map (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).toRingHom
    (MvPolynomial.finSuccEquiv A 0 (MvPolynomial.X 0))) = _
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]
section Fractions
variable (A F : Type) [CommRing A] [Field F] [Algebra A F]
local instance biFraction [IsDomain A] [IsFractionRing A F] : IsFractionRing (Bi A) (Rats F) := by
  let : IsFractionRing (Polynomial A) (RatFunc F) := polynomial_fraction A F
  exact polynomial_fraction (Polynomial A) (RatFunc F)
@[instance_reducible]
def paramAlgebra : Algebra (Params A) (Rats F) :=
  Algebra.compHom (Rats F) (twoVars A).toRingHom
attribute [local instance] paramAlgebra
def constants : F →+* Rats F :=
  (algebraMap (RatFunc F) (Rats F)).comp (algebraMap F (RatFunc F))
@[simp] theorem bi_C (x : A) :
    algebraMap (Bi A) (Rats F) (C (C x)) = constants F (algebraMap A F x) := by
  rw [IsScalarTower.algebraMap_apply (Bi A) (Polynomial (RatFunc F)) (Rats F),
    Polynomial.algebraMap_def, Polynomial.coe_mapRingHom, Polynomial.map_C]
  change algebraMap (Polynomial (RatFunc F)) (Rats F) (C (algebraMap (Polynomial A) (RatFunc F) (C x))) = _
  rw [IsScalarTower.algebraMap_apply (Polynomial A) (Polynomial F) (RatFunc F),
    Polynomial.algebraMap_def, Polynomial.coe_mapRingHom, Polynomial.map_C]
  rfl
@[simp] theorem param_C (x : A) :
    algebraMap (Params A) (Rats F) (MvPolynomial.C x) = constants F (algebraMap A F x) := by
  change algebraMap (Bi A) (Rats F) (twoVars A (MvPolynomial.C x)) = _
  rw [twoVars_C, bi_C]
@[simp] theorem param_X_zero :
    algebraMap (Params A) (Rats F) (MvPolynomial.X 0) = RatFunc.X := by
  change algebraMap (Bi A) (Rats F) (twoVars A (MvPolynomial.X 0)) = _
  rw [twoVars_X_zero, IsScalarTower.algebraMap_apply (Bi A) (Polynomial (RatFunc F)) (Rats F),
    Polynomial.algebraMap_def, Polynomial.coe_mapRingHom, Polynomial.map_X, RatFunc.algebraMap_X]
@[simp] theorem param_X_one :
    algebraMap (Params A) (Rats F) (MvPolynomial.X 1) =
      algebraMap (RatFunc F) (Rats F) RatFunc.X := by
  change algebraMap (Bi A) (Rats F) (twoVars A (MvPolynomial.X 1)) = _
  rw [twoVars_X_one, IsScalarTower.algebraMap_apply (Bi A) (Polynomial (RatFunc F)) (Rats F),
    Polynomial.algebraMap_def, Polynomial.coe_mapRingHom, Polynomial.map_C,
    IsScalarTower.algebraMap_apply (Polynomial A) (Polynomial F) (RatFunc F),
    Polynomial.algebraMap_def, Polynomial.coe_mapRingHom, Polynomial.map_X, RatFunc.algebraMap_X]
  rfl
end Fractions
open K1_14_3_2_4 (parameter)
private def order : Fin 4 ≃ Fin 4 :=
  Equiv.ofBijective (![2, 1, 3, 0] : Fin 4 → Fin 4) (by decide)
private def orderedParameters : MvPolynomial (Fin 4) FX ≃+* Bi (Params FX) :=
  (MvPolynomial.renameEquiv FX order).toRingEquiv.trans
    ((MvPolynomial.finSuccEquiv FX 3).toRingEquiv.trans
      (Polynomial.mapEquiv (MvPolynomial.finSuccEquiv FX 2).toRingEquiv))
local instance : IsFractionRing (Bi (Params FX)) (Rats LineField) := biFraction _ _
def baseEquiv : SectionField ≃+* Rats LineField :=
  IsFractionRing.ringEquivOfRingEquiv orderedParameters
private theorem base_polynomial (p : MvPolynomial (Fin 4) FX) :
    baseEquiv (algebraMap _ SectionField p) =
      algebraMap (Bi (Params FX)) (Rats LineField) (orderedParameters p) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap orderedParameters p
@[simp] theorem base_scalar (x : FX) :
    baseEquiv (algebraMap FX SectionField x) = constants LineField (algebraMap FX LineField x) := by
  rw [IsScalarTower.algebraMap_apply FX (MvPolynomial (Fin 4) FX) SectionField]
  change baseEquiv (algebraMap _ SectionField (MvPolynomial.C x)) = _
  rw [base_polynomial]
  have h : orderedParameters (MvPolynomial.C x) = C (C (MvPolynomial.C x)) := by
    simp [orderedParameters, MvPolynomial.finSuccEquiv_apply, Polynomial.mapEquiv]
  rw [h, bi_C]
  rfl
private theorem ordered_seed (i : Fin 2) :
    orderedParameters (MvPolynomial.X (if i = 0 then 0 else 2)) = C (C (MvPolynomial.X i)) := by
  fin_cases i
  · change Polynomial.map (MvPolynomial.finSuccEquiv FX 2).toRingEquiv.toRingHom
      (MvPolynomial.finSuccEquiv FX 3 (MvPolynomial.rename order (MvPolynomial.X 0))) = _
    rw [MvPolynomial.rename_X, show order 0 = Fin.succ (Fin.succ (0 : Fin 2)) from rfl,
      MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
    change C (MvPolynomial.finSuccEquiv FX 2 (MvPolynomial.X (Fin.succ 0))) = _
    rw [MvPolynomial.finSuccEquiv_X_succ]
    rfl
  · change Polynomial.map (MvPolynomial.finSuccEquiv FX 2).toRingEquiv.toRingHom
      (MvPolynomial.finSuccEquiv FX 3 (MvPolynomial.rename order (MvPolynomial.X 2))) = _
    rw [MvPolynomial.rename_X, show order 2 = Fin.succ (Fin.succ (1 : Fin 2)) from rfl,
      MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
    change C (MvPolynomial.finSuccEquiv FX 2 (MvPolynomial.X (Fin.succ 1))) = _
    rw [MvPolynomial.finSuccEquiv_X_succ]
    rfl
@[simp] theorem base_slope : baseEquiv (parameter 0) = constants LineField (lineParam 0) := by
  rw [parameter, base_polynomial]
  change algebraMap (Bi (Params FX)) (Rats LineField)
    (orderedParameters (MvPolynomial.X (if (0 : Fin 2) = 0 then 0 else 2))) = _
  rw [ordered_seed, bi_C]
  rfl
@[simp] theorem base_offset : baseEquiv (parameter 2) = constants LineField (lineParam 1) := by
  rw [parameter, base_polynomial]
  change algebraMap (Bi (Params FX)) (Rats LineField)
    (orderedParameters (MvPolynomial.X (if (1 : Fin 2) = 0 then 0 else 2))) = _
  rw [ordered_seed, bi_C]
  rfl
end
end K1_14_3R_3_1_2_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3R_3_2
noncomputable section
open K1_14 K1_14_3 Polynomial
abbrev JetParameters := MvPolynomial (Fin 2) FX
abbrev JetLineField := FractionRing JetParameters
def jetParameter (i : Fin 2) : JetLineField :=
  algebraMap JetParameters JetLineField (MvPolynomial.X i)
abbrev Coordinates := Option (Fin 2)
abbrev CurveAmbient := MvPolynomial Coordinates JetLineField
abbrev FurtherParameters := MvPolynomial (Fin 2) JetLineField
abbrev FurtherField := FractionRing FurtherParameters
def furtherParameter (i : Fin 2) : FurtherField :=
  algebraMap FurtherParameters FurtherField (MvPolynomial.X i)
end
end K1_14_3R_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace K1_14_3R_3_1_2_1
noncomputable section
open K1_14_3R_3_1_2 MvPolynomial
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Polynomial.algebra
attribute [local instance] MvPolynomial.algebraMvPolynomial Algebra.TensorProduct.rightAlgebra
section
variable (k A : Type) [Field k] [CommRing A] [Algebra k A]
abbrev RationalTensor := Rats k ⊗[k] A
local instance rationalParameters : Algebra (Params k) (Rats k) := paramAlgebra k k
local instance rationalParameterSMul : SMul (Params k) (Rats k) :=
  (rationalParameters k).toSMul
local instance constantsTower : IsScalarTower k (Params k) (Rats k) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    change constants k x = algebraMap (Params k) (Rats k) (MvPolynomial.C x)
    rw [param_C, Algebra.algebraMap_self, RingHom.id_apply]
private def polynomialToTensor : Params A →+* RationalTensor k A :=
  MvPolynomial.eval₂Hom Algebra.TensorProduct.includeRight.toRingHom
    (fun i => algebraMap (Rats k) (RationalTensor k A)
      (algebraMap (Params k) (Rats k) (MvPolynomial.X i)))
local instance tensorAlgebra : Algebra (Params A) (RationalTensor k A) :=
  (polynomialToTensor k A).toAlgebra
variable [IsDomain A] [IsDomain (RationalTensor k A)]
structure TensorModel where
  equiv : FractionRing (RationalTensor k A) ≃+* Rats (FractionRing A)
  left : ∀ x : Rats k, equiv (algebraMap (RationalTensor k A) _ (algebraMap (Rats k) _ x)) =
    rationalMap (rationalMap (algebraMap k (FractionRing A))) x
  right : ∀ a : A, equiv (algebraMap (RationalTensor k A) _ (1 ⊗ₜ[k] a)) =
    constants (FractionRing A) (algebraMap A (FractionRing A) a)
end
end
end K1_14_3R_3_1_2_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3R_3_2
noncomputable section
open scoped TensorProduct
variable {k E σ : Type} [Field k] [Field E] [Algebra k E]
def quotientBaseChange (I : Ideal (MvPolynomial σ k)) :
    E ⊗[k] (MvPolynomial σ k ⧸ I) ≃ₐ[E]
      (MvPolynomial σ E ⧸ I.map (MvPolynomial.map (algebraMap k E))) := by
  let e : E ⊗[k] MvPolynomial σ k ≃ₐ[E] MvPolynomial σ E :=
    MvPolynomial.algebraTensorAlgEquiv k E
  let i : MvPolynomial σ k →+* E ⊗[k] MvPolynomial σ k :=
    (Algebra.TensorProduct.includeRight (A := E) (R := k)).toRingHom
  have hmap : e.toAlgHom.toRingHom.comp i = MvPolynomial.map (algebraMap k E) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[k] p) = MvPolynomial.map (algebraMap k E) p
    simpa only [e, one_smul] using MvPolynomial.algebraTensorAlgEquiv_tmul k E 1 p
  exact (Algebra.TensorProduct.tensorQuotientEquiv E (MvPolynomial σ k) E I).trans
    (Ideal.quotientEquivAlg (I.map i) _ e (by
      change _ = (I.map i).map e.toAlgHom.toRingHom
      rw [Ideal.map_map, hmap]))
end
end K1_14_3R_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_14_3R_3_2
noncomputable section
open MvPolynomial
open scoped TensorProduct Polynomial
end
end K1_14_3R_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace K1_14_3R_3_1_2_1
noncomputable section
open K1_14 K1_14_3 K1_14_3R_3 K1_14_3R_3_1 K1_14_3R_3_1_2 K1_14_3_2_7
open scoped TensorProduct
attribute [local instance] Polynomial.algebra
private abbrev Coord := Option (Option (Fin 2))
private abbrev Multi (k : Type) [CommRing k] := MvPolynomial Coord k
private def nest (k : Type) [CommRing k] : Multi k ≃ₐ[k] Four k :=
  (MvPolynomial.optionEquivLeft k _).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.optionEquivLeft k _))
private abbrev k := LineField
private abbrev K := Rats k
private def baseInclusion : k →+* K := constants k
private def coeffChange : SectionJet ≃+* Four K :=
  Polynomial.mapEquiv (Polynomial.mapEquiv (MvPolynomial.mapEquiv (Fin 2) baseEquiv))
private structure CurveTensor (q : Surface) where
  equiv : Curve q ≃+* RationalTensor k (LineCurve q)
  left : ∀ c : SectionField, equiv (algebraMap SectionField (Curve q) c) =
    algebraMap K (RationalTensor k (LineCurve q)) (baseEquiv c)
  right : ∀ p : Multi k,
    equiv (toCurve q (coeffChange.symm (extendScalars baseInclusion (nest k p)))) =
      1 ⊗ₜ[k] Ideal.Quotient.mk (lineIdeal q) (nest k p)
end
end K1_14_3R_3_1_2_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace K1_14_3R_3_2
noncomputable section
open K1_14 K1_14_3 K1_14_3R_3 Polynomial
private def jetIndex (i : Fin 2) : Fin 4 := if i = 0 then 1 else 3
private theorem jetIndex_injective : Function.Injective jetIndex := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide
private abbrev Parameters := MvPolynomial (Fin 4) FX
private def includesParameters : JetParameters →+* SectionField :=
  (algebraMap Parameters SectionField).comp (MvPolynomial.rename jetIndex).toRingHom
private theorem includesParameters_injective : Function.Injective includesParameters :=
  (IsFractionRing.injective Parameters SectionField).comp
    (MvPolynomial.rename_injective jetIndex jetIndex_injective)
private def includeJetField : JetLineField →+* SectionField :=
  IsFractionRing.lift (K := JetLineField) includesParameters_injective
private instance : Algebra JetLineField SectionField := includeJetField.toAlgebra
@[simp] private theorem include_parameter (i : Fin 2) :
    algebraMap JetLineField SectionField (jetParameter i) =
      algebraMap Parameters SectionField (MvPolynomial.X (jetIndex i)) := by
  change includeJetField (algebraMap JetParameters JetLineField (MvPolynomial.X i)) = _
  rw [includeJetField, IsFractionRing.lift_algebraMap]
  simp [includesParameters]
@[simp] private theorem include_scalar (x : FX) :
    algebraMap JetLineField SectionField (algebraMap FX JetLineField x) =
      algebraMap FX SectionField x := by
  change includeJetField (algebraMap JetParameters JetLineField (MvPolynomial.C x)) = _
  rw [includeJetField, IsFractionRing.lift_algebraMap]
  change algebraMap Parameters SectionField (MvPolynomial.rename jetIndex (MvPolynomial.C x)) = _
  rw [MvPolynomial.rename_C]
  exact (IsScalarTower.algebraMap_apply FX Parameters SectionField x).symm
private abbrev Over := MvPolynomial Coordinates SectionField
private abbrev slope : SectionField := algebraMap Parameters SectionField (MvPolynomial.X 1)
private abbrev offset : SectionField := algebraMap Parameters SectionField (MvPolynomial.X 3)
private abbrev t (i : Fin 2) : SectionJet := C (C (MvPolynomial.X i))
private abbrev y : SectionJet := C (Polynomial.X (R := SectionSeeds))
private abbrev v : SectionJet := Polynomial.X
private def eliminate : SectionJet →ₐ[SectionField] Over where
  toRingHom := eval₂RingHom
    (eval₂RingHom (MvPolynomial.eval₂Hom MvPolynomial.C (MvPolynomial.X ∘ some))
      (MvPolynomial.C offset - MvPolynomial.C slope * MvPolynomial.X none))
    (MvPolynomial.X none)
  commutes' c := by
    change eval₂RingHom _ _ (C (C (MvPolynomial.C c))) = MvPolynomial.C c
    simp
@[simp] private theorem eliminate_t (i : Fin 2) : eliminate (t i) = MvPolynomial.X (some i) := by
  simp [eliminate]
@[simp] private theorem eliminate_y :
    eliminate y = MvPolynomial.C offset - MvPolynomial.C slope * MvPolynomial.X none := by
  simp [eliminate]
@[simp] private theorem eliminate_v : eliminate v = MvPolynomial.X none := by
  simp [eliminate]
end
end K1_14_3R_3_2
end
section
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000
set_option autoImplicit false
namespace K1_14_3R_3_1_2_3
noncomputable section
open K1_14 K1_14_3 K1_14_3R_3_1_2 Polynomial
open K1_14_3_2_4 (parameter)
open scoped nonZeroDivisors
abbrev OffsetField (k : Type) [Field k] := FractionRing (Polynomial (RatFunc k))
def offsetConstant (k : Type) [Field k] : RatFunc k →+* OffsetField k :=
  (algebraMap (Polynomial (RatFunc k)) (OffsetField k)).comp C
def offsetCoordinate (k : Type) [Field k] : OffsetField k :=
  algebraMap (Polynomial (RatFunc k)) (OffsetField k) Polynomial.X
attribute [local instance] Polynomial.algebra
private theorem polynomialFraction {A F G : Type} [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] [Field G] [Algebra (Polynomial F) G]
    [IsFractionRing (Polynomial F) G] :
    letI : Algebra (Polynomial A) G := Algebra.compHom G (algebraMap _ (Polynomial F))
    IsFractionRing (Polynomial A) G := by
  let : Algebra (Polynomial A) G := Algebra.compHom G (algebraMap _ (Polynomial F))
  let : IsScalarTower (Polynomial A) (Polynomial F) G := IsScalarTower.of_algebraMap_eq' rfl
  let M := (nonZeroDivisors A).map (C : A →+* Polynomial A).toMonoidHom
  let : IsLocalization M (Polynomial F) := Polynomial.isLocalization (nonZeroDivisors A) F
  have h := IsLocalization.localization_localization_isLocalization_of_has_all_units
    M (nonZeroDivisors (Polynomial F)) G (fun _ hx => hx.mem_nonZeroDivisors)
  have he : (nonZeroDivisors (Polynomial F)).comap (algebraMap (Polynomial A) (Polynomial F)) =
      nonZeroDivisors (Polynomial A) := by
    ext x
    change algebraMap (Polynomial A) (Polynomial F) x ∈ nonZeroDivisors (Polynomial F) ↔
      x ∈ nonZeroDivisors (Polynomial A)
    rw [mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
    exact not_congr (map_eq_zero_iff _ (Polynomial.map_injective _ (IsFractionRing.injective A F)))
  rw [he] at h
  exact h
section Parameters
variable (k : Type) [Field k]
private abbrev SeedParameters := MvPolynomial (Fin 2) k
private abbrev SeedCoefficients := FractionRing (SeedParameters k)
private abbrev SlopeParameters := Polynomial (SeedParameters k)
private abbrev NestedParameters := Polynomial (SlopeParameters k)
local instance : Algebra (SlopeParameters k) (RatFunc (SeedCoefficients k)) :=
  Algebra.compHom (RatFunc (SeedCoefficients k))
    (algebraMap (SlopeParameters k) (Polynomial (SeedCoefficients k)))
local instance : IsFractionRing (SlopeParameters k) (RatFunc (SeedCoefficients k)) :=
  polynomialFraction
local instance nestedAlgebra : Algebra (NestedParameters k) (OffsetField (SeedCoefficients k)) :=
  Algebra.compHom (OffsetField (SeedCoefficients k))
    (algebraMap (NestedParameters k) (Polynomial (RatFunc (SeedCoefficients k))))
local instance nestedFraction : IsFractionRing (NestedParameters k) (OffsetField (SeedCoefficients k)) :=
  polynomialFraction
end Parameters
set_option backward.isDefEq.respectTransparency false
end
end K1_14_3R_3_1_2_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace K1_14_3R_3_1_1
noncomputable section
open K1_14 K1_14_3 K1_14_3R_3 K1_14_3R_3_1
open K1_14_3_2_4 (parameter seedVar ordinateVar derivativeVar)
open Polynomial hiding derivative
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end K1_14_3R_3_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace K1_14_3R_3_2
noncomputable section
open K1_14 K1_14_3 K1_14_3R_3 MvPolynomial
end
end K1_14_3R_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 8
namespace K1_14_3R_3_1_1
noncomputable section
open K1_14 K1_14_3 K1_14_3R_3 K1_14_3R_3_1
open K1_14_3_2_4 (parameter seedVar ordinateVar derivativeVar)
open Polynomial hiding derivative
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra Polynomial.isLocalization
end
end K1_14_3R_3_1_1
end
section
namespace K1_14_2_2_7_3_3
noncomputable section
open K1_14_2 K1_14_2_2_7_3
open K1_14_3R_3_1 (functionDegree toFunction jetPencilDegree)
abbrev coord {k : Type} [Field k] (H : Ideal (MvPolynomial (Fin 4) k))
    (i : Fin 4) : CoordinateRing H :=
  Ideal.Quotient.mk H (MvPolynomial.X i)
abbrev seedCoord {k : Type} [Field k] (H : Ideal (MvPolynomial (Fin 4) k))
    (i : Fin 2) : CoordinateRing H :=
  coord H (Fin.castLE (by decide : 2 ≤ 4) i)
abbrev cutFunction {k : Type} [Field k] (H : Ideal (MvPolynomial (Fin 4) k))
    (G : Polynomial (MvPolynomial (Fin 2) k)) : CoordinateRing H :=
  Ideal.Quotient.mk H (blockEval G)
structure PoleProfile (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (x y : A) where
  places : ℕ
  weight : Fin places → ℕ
  order : Fin places → A → ℕ
  scalar : ∀ p c, order p (algebraMap k A c) = 0
  add : ∀ p f g, order p (f + g) ≤ max (order p f) (order p g)
  mul : ∀ p f g, order p (f * g) ≤ order p f + order p g
  degree_eq : ∀ f, (∑ p, weight p * order p f) = functionDegree k (toFunction f)
  pencil_eq : (∑ p, weight p * max (order p x) (order p y)) =
    jetPencilDegree k (toFunction x) (toFunction y)
end
end K1_14_2_2_7_3_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3R_3_2_3
noncomputable section
open K1_14_3R_3_2 MvPolynomial
abbrev HomVariables := Sum Bool Coordinates
abbrev HomAmbient (k : Type) [CommSemiring k] := MvPolynomial HomVariables k
def homogenizer (seed : Bool) : HomVariables := Sum.inl seed
def homWeight : HomVariables → ℕ × ℕ
  | .inl false | .inr none => (1, 0)
  | .inl true | .inr (some _) => (0, 1)
section Presentation
variable {k : Type} [CommRing k]
def dehom : HomAmbient k →+* MvPolynomial Coordinates k :=
  eval₂Hom MvPolynomial.C (Sum.elim (fun _ => 1) MvPolynomial.X)
abbrev dehomClass (I : Ideal (MvPolynomial Coordinates k)) :
    HomAmbient k →+* (MvPolynomial Coordinates k ⧸ I) :=
  (Ideal.Quotient.mk I).comp dehom
def reesMap (I : Ideal (MvPolynomial Coordinates k)) :
    HomAmbient k →+* AddMonoidAlgebra (MvPolynomial Coordinates k ⧸ I) (ℕ × ℕ) :=
  eval₂Hom
    (AddMonoidAlgebra.singleZeroRingHom.comp ((Ideal.Quotient.mk I).comp MvPolynomial.C))
    (fun v => AddMonoidAlgebra.single (homWeight v) (dehomClass I (MvPolynomial.X v)))
end Presentation
end
end K1_14_3R_3_2_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000
namespace K1_14_2_2_7_3_3
noncomputable section
open Algebra Polynomial
open K1_14_3R_3_1 (functionDegree toFunction)
open scoped BigOperators Polynomial nonZeroDivisors IntermediateField.algebraAdjoinAdjoin
theorem principal_finite {k A : Type} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (hdim : ringKrullDim A = 1) {f : A}
    (hf : f ≠ 0) : Module.Finite k (A ⧸ Ideal.span {f}) := by
  let I : Ideal A := Ideal.span {f}
  let : Algebra.FiniteType k (A ⧸ I) := Algebra.FiniteType.quotient k I
  apply (Module.finite_iff_krullDimLE_zero k (A ⧸ I)).mpr
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro P hP
  let : P.IsPrime := hP.isPrime
  have hfP : f ∈ P := hP.le (Ideal.mem_span_singleton_self f)
  have hne : P ≠ ⊥ := fun h => hf (by simpa [h] using hfP)
  have hlow : 1 ≤ P.height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hne)
  have hu : (P.height : WithBot ℕ∞) ≤ 1 :=
    hdim ▸ Ideal.height_le_ringKrullDim_of_isPrime (I := P)
  let : FiniteRingKrullDim A :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr (by rw [hdim]; exact ⟨by decide, by decide⟩)
  apply Ideal.isMaximal_of_height_eq_ringKrullDim
  rw [hdim]
  exact le_antisymm hu (WithBot.coe_le_coe.mpr hlow)
private theorem trdeg_le_one {k A : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hdim : ringKrullDim A = 1) : Algebra.trdeg k A ≤ 1 := by
  obtain ⟨d, f, hf, hfint⟩ := exists_finite_inj_algHom_of_fg k A
  let B := MvPolynomial (Fin d) k
  let : Algebra B A := f.toRingHom.toAlgebra
  let : IsScalarTower k B A := IsScalarTower.of_algHom f
  let : Module.Finite B A := hfint
  let : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  let : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hf
  have hdB : ringKrullDim B = (d : WithBot ℕ∞) := by
    simp [B, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  obtain ⟨l, hlen⟩ := Order.le_krullDim_iff.mp hdB.ge
  have := l.head.isPrime
  have hle : (⊥ : Ideal A).under B ≤ l.head.asIdeal := by
    change Ideal.comap (algebraMap B A) ⊥ ≤ l.head.asIdeal
    have hinj := FaithfulSMul.algebraMap_injective B A
    rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨P, _, hP, hPhead⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal A) hle
  let : P.IsPrime := hP
  let : P.LiesOver l.head.asIdeal := ⟨hPhead.symm⟩
  obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  have hle : (d : WithBot ℕ∞) ≤ ringKrullDim A :=
    Order.le_krullDim_iff.mpr ⟨L, hL.trans hlen⟩
  rw [hdim] at hle
  have hd : d ≤ 1 := by exact_mod_cast hle
  have ht := trdeg_add_eq k B (A := A)
  rw [trdeg_eq_zero (R := B) (A := A), add_zero] at ht
  rw [← ht]
  change Algebra.trdeg k (MvPolynomial (Fin d) k) ≤ 1
  rw [MvPolynomial.trdeg_of_isDomain]
  simpa using (Nat.cast_le.mpr hd : (d : Cardinal.{0}) ≤ (1 : ℕ))
theorem finite_function_field {k A : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hdim : ringKrullDim A = 1) {z : FractionRing A}
    (hz : Transcendental k z) :
    Module.Finite (IntermediateField.adjoin k ({z} : Set (FractionRing A))) (FractionRing A) := by
  let F := FractionRing A
  let R := Algebra.adjoin k ({z} : Set F)
  let B := IntermediateField.adjoin k ({z} : Set F)
  have : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic _ A⁰
  have ht := trdeg_add_eq k A (A := F)
  rw [trdeg_eq_zero (R := A) (A := F), add_zero] at ht
  have htr : Algebra.trdeg k F ≤ 1 := ht.symm ▸ trdeg_le_one hdim
  let x : Fin 1 → F := fun _ => z
  have hi : AlgebraicIndependent k x := algebraicIndependent_unique_type_iff.mpr hz
  have hx := hi.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have hrange : Set.range x = {z} := by simp [x]
  have hR := hx.isAlgebraic
  rw [hrange] at hR
  let : Algebra.IsAlgebraic R F := hR
  have : Algebra.IsAlgebraic B F :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective R B)
  have : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_isLocalization F A⁰
  have : Algebra.EssFiniteType k F := Algebra.EssFiniteType.comp k A F
  have : Algebra.EssFiniteType B F := Algebra.EssFiniteType.of_comp k B F
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic
private theorem polynomial_relation {k A : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    {ι : Type} [Fintype ι] {f : A} (hf : f ≠ 0) (b : ι → A)
    (hb : LinearIndependent k (fun i => Ideal.Quotient.mk (Ideal.span {f}) (b i)))
    (P : ι → k[X]) (hP : (∑ i, aeval f (P i) * b i) = 0) : ∀ i, P i = 0 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  have hex : ∃ n, ∃ j, (P j).coeff n ≠ 0 :=
    ⟨(P i).natTrailingDegree, i, coeff_natTrailingDegree_ne_zero.mpr hi⟩
  let n := Nat.find hex
  have hdiv (j : ι) : (Polynomial.X (R := k)) ^ n ∣ P j :=
    X_pow_dvd_iff.mpr fun d hd => by
      by_contra hc
      exact (Nat.find_min hex hd) ⟨j, hc⟩
  choose Q hQ using hdiv
  have hscaled : f ^ n * (∑ i, aeval f (Q i) * b i) = 0 := by
    simpa only [hQ, aeval_mul, aeval_X_pow, mul_assoc, Finset.mul_sum] using hP
  have hrel := (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero n hf)
  let q := Ideal.Quotient.mkₐ k (Ideal.span {f})
  have hqf : q f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
  have hred := congrArg q hrel
  simp only [map_sum, map_mul, ← aeval_algHom_apply q, hqf, ← coeff_zero_eq_aeval_zero',
    map_zero, ← Algebra.smul_def] at hred
  have hzero := Fintype.linearIndependent_iff.mp hb _ hred
  obtain ⟨j, hj⟩ := Nat.find_spec hex
  apply hj
  have heq : (P j).coeff n = (Q j).coeff 0 := by
    rw [hQ j]
    simpa using (coeff_X_pow_mul (Q j) n 0)
  exact heq.trans (hzero j)
private theorem lifts_independent {k A : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    {ι : Type} [Fintype ι] {f : A} (hf : f ≠ 0) (hz : Transcendental k (toFunction f))
    (b : ι → A) (hb : LinearIndependent k (fun i => Ideal.Quotient.mk (Ideal.span {f}) (b i))) :
    LinearIndependent (IntermediateField.adjoin k ({toFunction f} : Set (FractionRing A)))
      (fun i => toFunction (b i)) := by
  let F := FractionRing A
  let z := toFunction f
  let R := Algebra.adjoin k ({z} : Set F)
  let B := IntermediateField.adjoin k ({z} : Set F)
  apply LinearIndependent.localization (R := R) B R⁰
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let e := Polynomial.algEquivOfTranscendental k z hz
  let P (j : ι) := e.symm (c j)
  let incl : A →ₐ[k] F := IsScalarTower.toAlgHom k A F
  have he (j : ι) : incl (aeval f (P j)) = (c j : F) := by
    rw [← aeval_algHom_apply incl]
    change aeval z (P j) = (c j : F)
    rw [← aeval_subalgebra_coe (P j) R ⟨z, Algebra.self_mem_adjoin_singleton k z⟩]
    change (e (P j) : F) = (c j : F)
    rw [show e (P j) = c j from e.apply_symm_apply (c j)]
  have hp : (∑ j, aeval f (P j) * b j) = 0 := by
    apply IsFractionRing.injective A F
    change incl (∑ j, aeval f (P j) * b j) = incl 0
    change (∑ j, (c j : F) * incl (b j)) = 0 at hc
    simpa only [map_sum, map_mul, map_zero, he] using hc
  exact e.symm.injective (by simpa [P] using polynomial_relation hf b hb P hp i)
theorem principal_length_le {k A : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hdim : ringKrullDim A = 1) {f : A} (hf : f ≠ 0) :
    Module.finrank k (A ⧸ Ideal.span {f}) ≤ functionDegree k (toFunction f) := by
  classical
  by_cases h : IsAlgebraic k (toFunction f)
  · have hfalg : IsAlgebraic k f :=
      (isAlgebraic_algebraMap_iff (IsFractionRing.injective A (FractionRing A))).mp h
    have htop : (Ideal.span {f} : Ideal A) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_span_singleton_self f) (hfalg.isIntegral.isUnit hf)
    rw [htop, Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  · unfold functionDegree
    rw [ite_eq_right h]
    let : Module.Finite k (A ⧸ Ideal.span {f}) := principal_finite hdim hf
    let : Module.Finite (IntermediateField.adjoin k ({toFunction f} : Set (FractionRing A)))
        (FractionRing A) := finite_function_field hdim h
    let b := Module.finBasis k (A ⧸ Ideal.span {f})
    choose lift hlift using fun i => Ideal.Quotient.mk_surjective (b i)
    have hlin : LinearIndependent k (fun i => Ideal.Quotient.mk (Ideal.span {f}) (lift i)) :=
      (funext hlift).symm ▸ b.linearIndependent
    simpa only [Fintype.card_fin] using (lifts_independent hf h lift hlin).fintype_card_le_finrank
end
end K1_14_2_2_7_3_3
end
section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace K1_14_3R_3_2_2
noncomputable section
open K1_14 K1_14_3 K1_14_3R_3_2 MvPolynomial
open K1_14_3_2_4 (parameter)
open scoped nonZeroDivisors
section
variable {R S F : Type} [CommRing R] [IsDomain R] [CommRing S]
  [Algebra R S] {M : Submonoid R} [IsLocalization M S] [Field F]
  [Algebra S F] [IsFractionRing S F]
private theorem fraction_after_localization (hM : M ≤ nonZeroDivisors R) :
    let : Algebra R F := Algebra.compHom F (algebraMap R S)
    IsFractionRing R F := by
  let : Algebra R F := Algebra.compHom F (algebraMap R S)
  let : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq' rfl
  have hi : Function.Injective (algebraMap R F) :=
    (IsFractionRing.injective S F).comp (IsLocalization.injective S hM)
  let : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective R F).mpr hi
  apply IsFractionRing.of_field
  intro z
  obtain ⟨x, y, _, hz⟩ := IsFractionRing.div_surjective S z
  obtain ⟨a, m, hm⟩ := IsLocalization.exists_mk'_eq M x
  obtain ⟨b, n, hn⟩ := IsLocalization.exists_mk'_eq M y
  have hcoe (s : M) : algebraMap R F (s : R) ≠ 0 := fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp (hM s.property)) (hi (h.trans (map_zero _).symm))
  refine ⟨a * n, b * m, ?_⟩
  have he (r : R) (s : M) :
      algebraMap S F (IsLocalization.mk' S r s) =
        algebraMap R F r / algebraMap R F (s : R) := by
    apply (eq_div_iff (hcoe s)).mpr
    rw [IsScalarTower.algebraMap_apply R S F (s : R), ← map_mul,
      IsLocalization.mk'_spec, IsScalarTower.algebraMap_apply R S F r]
  rw [← hz, ← hm, ← hn, he, he, map_mul, map_mul]
  simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
end
section FieldChange
variable (k : Type) [Field k]
private abbrev JetParams := MvPolynomial (Fin 2) k
private abbrev JetCoefficients := FractionRing (JetParams k)
private abbrev LaterParams := MvPolynomial (Fin 2) (JetCoefficients k)
private abbrev LaterField := FractionRing (LaterParams k)
private abbrev JointParams := MvPolynomial (Fin 4) k
private abbrev JointField := FractionRing (JointParams k)
private abbrev Nested := MvPolynomial (Fin 2) (JetParams k)
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance nestedAlgebra : Algebra (Nested k) (LaterField k) :=
  Algebra.compHom (LaterField k) (algebraMap (Nested k) (LaterParams k))
local instance nestedFraction : IsFractionRing (Nested k) (LaterField k) :=
  fraction_after_localization (M := (nonZeroDivisors (JetParams k)).map
    (MvPolynomial.C (σ := Fin 2))) <| by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact (map_ne_zero_iff _ (MvPolynomial.C_injective (Fin 2) (JetParams k))).2
        (mem_nonZeroDivisors_iff_ne_zero.mp hx)
private def index : Fin 2 ⊕ Fin 2 → Fin 4 :=
  Sum.elim ![0, 2] ![1, 3]
private def pairIndex : Fin 2 ⊕ Fin 2 ≃ Fin 4 :=
  Equiv.ofBijective index (by decide)
private def flatten : (Nested k) ≃+* (JointParams k) :=
  (MvPolynomial.sumRingEquiv k (Fin 2) (Fin 2)).symm.trans
    (MvPolynomial.renameEquiv k pairIndex).toRingEquiv
private def forward : (JointParams k) →ₐ[k] (JointParams k) :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 3, MvPolynomial.X 2 + MvPolynomial.X 1 * MvPolynomial.X 3]
private def backward : (JointParams k) →ₐ[k] (JointParams k) :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2, MvPolynomial.X 2]
private def jetsChange : (JointParams k) ≃ₐ[k] (JointParams k) :=
  AlgEquiv.ofAlgHom (forward k) (backward k)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [forward, backward])
    (by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [forward, backward])
private def coefficients (jets : Bool) : (Nested k) ≃+* (JointParams k) :=
  if jets then (flatten k).trans (jetsChange k).toRingEquiv else flatten k
private def fractionEquiv {A B F G : Type} [CommRing A] [CommRing B]
    [CommRing F] [CommRing G] [Algebra A F] [IsFractionRing A F]
    [Algebra B G] [IsFractionRing B G] (e : A ≃+* B) : F ≃+* G :=
  IsFractionRing.ringEquivOfRingEquiv e
private theorem fractionEquiv_apply {A B F G : Type} [CommRing A] [CommRing B]
    [CommRing F] [CommRing G] [Algebra A F] [IsFractionRing A F]
    [Algebra B G] [IsFractionRing B G] (e : A ≃+* B) (x : A) :
    (fractionEquiv (F := F) (G := G) e) (algebraMap A F x) = algebraMap B G (e x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap e x
def fieldEquiv (jets : Bool) :=
  @fractionEquiv (Nested k) (JointParams k) (LaterField k) (JointField k)
    inferInstance inferInstance inferInstance inferInstance
    (nestedAlgebra k) (nestedFraction k) inferInstance inferInstance (coefficients k jets)
private theorem flatten_c (c : k) : flatten k (C (C c)) = C c := by
  simp [flatten]
private theorem flatten_outer (i : Fin 2) : flatten k (MvPolynomial.X i) = MvPolynomial.X (index (.inl i)) := by
  simp [flatten, pairIndex]
private theorem flatten_inner (i : Fin 2) : flatten k (C (MvPolynomial.X i)) = MvPolynomial.X (index (.inr i)) := by
  simp [flatten, pairIndex]
private theorem map_nested (jets : Bool) (p : (Nested k)) :
    fieldEquiv k jets (algebraMap (Nested k) (LaterField k) p) =
      algebraMap (JointParams k) (JointField k) (coefficients k jets p) :=
  @fractionEquiv_apply (Nested k) (JointParams k) (LaterField k) (JointField k)
    inferInstance inferInstance inferInstance inferInstance
    (nestedAlgebra k) (nestedFraction k) inferInstance inferInstance (coefficients k jets) p
private theorem nested_inner (p : JetParams k) :
    algebraMap (Nested k) (LaterField k) (C p) =
      algebraMap (JetCoefficients k) (LaterField k)
        (algebraMap (JetParams k) (JetCoefficients k) p) := by
  change algebraMap (LaterParams k) (LaterField k)
    (MvPolynomial.map (algebraMap (JetParams k) (JetCoefficients k)) (C p)) = _
  rw [MvPolynomial.map_C]
  rfl
private theorem nested_outer (i : Fin 2) :
    algebraMap (Nested k) (LaterField k) (MvPolynomial.X i) =
      algebraMap (LaterParams k) (LaterField k) (MvPolynomial.X i) := by
  change algebraMap (LaterParams k) (LaterField k)
    (MvPolynomial.map (algebraMap (JetParams k) (JetCoefficients k)) (MvPolynomial.X i)) = _
  rw [MvPolynomial.map_X]
end FieldChange
abbrev Parameters := MvPolynomial (Fin 4) FX
@[simp] theorem fieldEquiv_scalar (jets : Bool) (c : FX) :
    fieldEquiv FX jets (algebraMap JetLineField FurtherField (algebraMap FX JetLineField c)) =
      algebraMap FX SectionField c := by
  rw [IsScalarTower.algebraMap_apply FX JetParameters JetLineField]
  change fieldEquiv FX jets
    (algebraMap JetLineField FurtherField (algebraMap JetParameters JetLineField (C c))) = _
  rw [← nested_inner FX]
  rw [map_nested, IsScalarTower.algebraMap_apply FX Parameters SectionField]
  cases jets <;> simp [coefficients, flatten_c, jetsChange, forward]
@[simp] theorem fieldEquiv_a (jets : Bool) :
    fieldEquiv FX jets (algebraMap JetLineField FurtherField (jetParameter 0)) = parameter 1 := by
  rw [jetParameter, ← nested_inner FX (MvPolynomial.X 0)]
  rw [map_nested]
  cases jets <;> simp [coefficients, flatten_inner, index, jetsChange, forward, parameter]
@[simp] theorem fieldEquiv_d (jets : Bool) :
    fieldEquiv FX jets (algebraMap JetLineField FurtherField (jetParameter 1)) =
      if jets then parameter 2 + parameter 1 * parameter 3 else parameter 3 := by
  rw [jetParameter, ← nested_inner FX (MvPolynomial.X 1)]
  rw [map_nested]
  cases jets <;> simp [coefficients, flatten_inner, index, jetsChange, forward, parameter]
@[simp] theorem fieldEquiv_s (jets : Bool) :
    fieldEquiv FX jets (furtherParameter 0) = parameter 0 := by
  rw [furtherParameter, ← nested_outer FX 0]
  rw [map_nested]
  cases jets <;> simp [coefficients, flatten_outer, index, jetsChange, forward, parameter]
@[simp] theorem fieldEquiv_t (jets : Bool) :
    fieldEquiv FX jets (furtherParameter 1) = if jets then parameter 3 else parameter 2 := by
  rw [furtherParameter, ← nested_outer FX 1]
  rw [map_nested]
  cases jets <;> simp [coefficients, flatten_outer, index, jetsChange, forward, parameter]
end
end K1_14_3R_3_2_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 900000
namespace K1_14_3R_3_1_2_3
noncomputable section
open K1_14_3_2_7 K1_14_3R_3_1_2 Polynomial
open scoped nonZeroDivisors
section Localization
variable {B A T : Type} [CommRing B] [CommRing A] [CommRing T]
variable (f : B →+* A) (g : A →+* T) (ρ : FractionRing B →+* T)
variable (h : ∀ b, g (f b) = ρ (algebraMap B (FractionRing B) b))
private def liftLocalized : Localized f →+* T :=
  IsLocalization.lift (M := denominators f) (g := g) (by
    rintro ⟨_, b, hb, rfl⟩
    change IsUnit (g (f b))
    rw [h]
    exact (IsLocalization.map_units (FractionRing B) ⟨b, hb⟩).map ρ)
@[simp] private theorem liftLocalized_apply (a : A) :
    liftLocalized f g ρ h (algebraMap A (Localized f) a) = g a :=
  IsLocalization.lift_eq _ _
end Localization
section Mixed
variable {k A : Type} [Field k] [CommRing A] [Algebra k A]
variable (y v : A)
variable {T : Type} [CommRing T]
variable (ρ : OffsetField k →+* T) (g : A →+* T)
variable (hρ : ∀ c, g (algebraMap k A c) = ρ (offsetConstant k (algebraMap k (RatFunc k) c)))
variable (hcut : g y + ρ (offsetConstant k RatFunc.X) * g v = ρ (offsetCoordinate k))
end Mixed
end
end K1_14_3R_3_1_2_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3R_3_2_3
noncomputable section
open K1_14_3R_3_2 MvPolynomial
variable {k : Type} [Field k]
@[simp] theorem dehom_C (c : k) : dehom (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [dehom]
@[simp] theorem dehom_affine (v : Coordinates) :
    dehom (MvPolynomial.X (Sum.inr v) : HomAmbient k) = MvPolynomial.X v := by
  simp [dehom]
@[simp] theorem dehom_homogenizer (seed : Bool) :
    dehom (MvPolynomial.X (homogenizer seed) : HomAmbient k) = 1 := by
  simp [dehom, homogenizer]
end
end K1_14_3R_3_2_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3R_3_2_3
noncomputable section
open K1_14_3R_3_2 MvPolynomial
variable {k : Type} [Field k]
variable (I : Ideal (MvPolynomial Coordinates k))
@[simp] theorem reesMap_X (v : HomVariables) :
    reesMap I (MvPolynomial.X v) =
      AddMonoidAlgebra.single (homWeight v) (dehomClass I (MvPolynomial.X v)) := by
  simp [reesMap]
@[simp] theorem reesMap_C (c : k) :
    reesMap I (MvPolynomial.C c) =
      AddMonoidAlgebra.single 0 (Ideal.Quotient.mk I (MvPolynomial.C c)) := by
  simp [reesMap, AddMonoidAlgebra.singleZeroRingHom]
@[simp] theorem reesMap_monomial (m : HomVariables →₀ ℕ) (c : k) :
    reesMap I (monomial m c) =
      AddMonoidAlgebra.single (Finsupp.weight homWeight m) (dehomClass I (monomial m c)) := by
  rw [monomial_eq]
  simp only [map_mul, reesMap_C, Finsupp.prod, map_prod, map_pow, reesMap_X,
    AddMonoidAlgebra.single_pow, AddMonoidAlgebra.prod_single, AddMonoidAlgebra.single_mul_single,
    zero_add, Finsupp.weight_apply, Finsupp.sum, RingHom.comp_apply, dehom_C, dehomClass]
end
end K1_14_3R_3_2_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_7_4_4_4
noncomputable section
open K1_14_2 K1_14_2_2_7_4 K1_14_2_2_7_4_4 Polynomial
open scoped Polynomial WithZero
private theorem eval₂_value_one {k K : Type} [Field k] [Field K]
    (v : Valuation K ℤᵐ⁰) (ι : k →+* K) (hι : ∀ c, v (ι c) ≤ 1)
    {r t : K} (ht : v t ≤ 1) (hrt : v (r - t) < 1)
    (p : k[X]) (hp : v (p.eval₂ ι t) = 1) :
    v (p.eval₂ ι r) = 1 := by
  let O := v.valuationSubring
  have hr : v r ≤ 1 := by
    have h := v.map_add_le hrt.le ht
    rwa [sub_add_cancel] at h
  let a : O := ⟨r, hr⟩
  let b : O := ⟨t, ht⟩
  let j : k →+* O := ι.codRestrict O.toSubring hι
  let ρ := IsLocalRing.residue O
  have hab : ρ a = ρ b := by
    apply sub_eq_zero.mp
    rw [← map_sub, IsLocalRing.residue_eq_zero_iff, v.mem_maximalIdeal_iff]
    exact hrt
  let z (x : O) := p.eval₂ j x
  have hz (x : O) : (z x : K) = p.eval₂ ι (x : K) :=
    Polynomial.hom_eval₂ p j O.subtype x
  have hres : ρ (z a) = ρ (z b) := by
    dsimp only [z]
    simp only [Polynomial.hom_eval₂, hab]
  have hb : ρ (z b) ≠ 0 := by
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff, v.mem_maximalIdeal_iff, hz, show (b : K) = t from rfl, hp]
    exact lt_irrefl 1
  rw [← show (a : K) = r from rfl, ← hz]
  refine le_antisymm (z a).2 (le_of_not_gt fun hlt => hb ?_)
  rw [← hres, IsLocalRing.residue_eq_zero_iff, v.mem_maximalIdeal_iff]
  exact hlt
private theorem no_pole_of_polynomial_values {k A : Type} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (hdim : ringKrullDim A = 1) (v : Valuation (FractionRing A) ℤᵐ⁰)
    (r y : FractionRing A) (hpoly : ∀ p : k[X], p ≠ 0 → v (aeval r p) = 1) :
    v y ≤ 1 := by
  have hr : Transcendental k r := by
    rintro ⟨p, hp, hzero⟩
    have h := hpoly p hp
    rw [hzero, map_zero] at h
    exact zero_ne_one h
  let E := IntermediateField.adjoin k {r}
  let : Module.Finite E (FractionRing A) :=
    K1_14_2_2_7_3_3.finite_function_field hdim hr
  let : v.IsTrivialOn E := ⟨by
    intro x hx
    have hx' : (x : FractionRing A) ≠ 0 := fun h => hx (Subtype.ext h)
    obtain ⟨p, q, hpq⟩ :=
      (IntermediateField.mem_adjoin_simple_iff k (x : FractionRing A)).mp x.2
    have hp : p ≠ 0 := fun h => hx' (by simp [hpq, h])
    have hq : q ≠ 0 := fun h => hx' (by simp [hpq, h])
    change v (x : FractionRing A) = 1
    rw [hpq, v.map_div, hpoly p hp, hpoly q hq, div_self one_ne_zero]⟩
  by_contra! h
  have hy : y ≠ 0 := by
    intro hy
    simp [hy] at h
  exact (v.transcendental_of_ne_one E y hy h.ne')
    (Algebra.IsAlgebraic.isAlgebraic y)
private theorem map_neg_div_sub {L K : Type} [Field L] [Field K]
    (e : L →+* K) (x y : L) (t : K) (hy : e y ≠ 0) :
    e (-x / y) - t = -(e x + t * e y) / e y := by
  rw [map_div₀, map_neg, neg_add, ← sub_eq_add_neg, sub_div, mul_div_cancel_right₀ _ hy]
variable {k : Type} [Field k] (D : Ideal (CurvePoly k))
private theorem genericSlope_ne_zero : genericSlope k ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (SlopeField k))).mpr
    Polynomial.X_ne_zero
private theorem seedParameter_eq :
    seedParameter D = fieldCoord D (some 0) +
      algebraMap (SlopeField k) (CurveField D) (genericSlope k) * fieldCoord D (some 1) := by
  have hC (c : SlopeField k) :
      algebraMap (SlopedCurve D) (CurveField D)
        (Ideal.Quotient.mk (slopeIdeal D) (MvPolynomial.C c)) =
        algebraMap (SlopeField k) (CurveField D) c :=
    (IsScalarTower.algebraMap_apply (SlopeField k) (SlopedCurve D) (CurveField D) c).symm
  let f : CurvePoly (SlopeField k) →+* CurveField D :=
    (algebraMap (SlopedCurve D) (CurveField D)).comp (Ideal.Quotient.mk (slopeIdeal D))
  have hX (i : Option (Fin 2)) : fieldCoord D i = f (MvPolynomial.X i) := by
    change f (MvPolynomial.map (algebraMap k (SlopeField k)) (MvPolynomial.X i)) = _
    rw [MvPolynomial.map_X]
  change f (MvPolynomial.X (some 0) + MvPolynomial.C (genericSlope k) * MvPolynomial.X (some 1)) = _
  rw [hX, hX, f.map_add, f.map_mul]
  exact congrArg (fun c => f (MvPolynomial.X (some 0)) + c * f (MvPolynomial.X (some 1))) (hC _)
variable [IsDomain (SlopedCurve D)]
private theorem second_seed_value_le_of_pole (hprime : D.IsPrime)
    (hdim : ringKrullDim (CoordinateRing D) = 1)
    (w : Place (SlopeField k) (CurveField D))
    (hy : 1 < w.val (fieldCoord D (some 1))) :
    w.val (fieldCoord D (some 1)) ≤ w.val (seedParameter D) := by
  by_contra! hcancel
  let : IsDomain (CoordinateRing D) := (Ideal.Quotient.isDomain_iff_prime D).mpr hprime
  let F := SlopeField k
  let K := CurveField D
  let A := CoordinateRing D
  let L := FractionRing A
  let ι : k →+* K := (algebraMap F K).comp (algebraMap k F)
  let t : K := algebraMap F K (genericSlope k)
  let g : A →+* K := Ideal.Quotient.lift D (fieldEval D) fun f hf => by
    change algebraMap (SlopedCurve D) K (Ideal.Quotient.mk (slopeIdeal D) (slopeMap k f)) = 0
    have hf' : slopeMap k f ∈ slopeIdeal D := Ideal.mem_map_of_mem (slopeMap k) hf
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf', map_zero]
  have hg : Function.Injective g := (injective_iff_map_eq_zero g).mpr fun a ha => by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    change fieldEval D f = 0 at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Classical.byContradiction fun hf =>
      fieldEval_ne_zero hf ha)
  let e : L →+* K := IsFractionRing.lift hg
  have he (f : CurvePoly k) :
      e (algebraMap A L (Ideal.Quotient.mk D f)) = fieldEval D f :=
    IsFractionRing.lift_algebraMap hg _
  have heC : e.comp (algebraMap k L) = ι := by
    apply RingHom.ext
    intro c
    change e (algebraMap k L c) = ι c
    rw [IsScalarTower.algebraMap_apply k A L]
    change e (algebraMap A L (Ideal.Quotient.mk D (MvPolynomial.C c))) = ι c
    rw [he]
    simp only [fieldEval, slopeMap, RingHom.comp_apply, MvPolynomial.map_C]
    exact (IsScalarTower.algebraMap_apply F (SlopedCurve D) K (algebraMap k F c)).symm
  let x := algebraMap A L (Ideal.Quotient.mk D (MvPolynomial.X (some 0)))
  let y := algebraMap A L (Ideal.Quotient.mk D (MvPolynomial.X (some 1)))
  let r := -x / y
  have hx' : e x = fieldCoord D (some 0) := he _
  have hy' : e y = fieldCoord D (some 1) := he _
  have hvy : 1 < w.val (e y) := by simpa only [hy'] using hy
  have hy0 : e y ≠ 0 := by
    intro hz
    simp [hz] at hvy
  have hdiff : e r - t = -seedParameter D / e y := by
    rw [seedParameter_eq, ← hx', ← hy']
    exact map_neg_div_sub e x y t hy0
  have hclose : w.val (e r - t) < 1 := by
    rw [hdiff, w.val.map_div, w.val.map_neg, div_lt_one₀ (w.val.pos_iff.mpr hy0)]
    simpa only [hy'] using hcancel
  have htv : w.val t ≤ 1 := (w.trivial _ genericSlope_ne_zero).le
  have hι (c : k) : w.val (ι c) ≤ 1 := by
    change w.val (algebraMap F K (algebraMap k F c)) ≤ 1
    by_cases hc : algebraMap k F c = 0
    · simp [hc]
    · exact (w.trivial _ hc).le
  have hTpoly (p : k[X]) (hp : p ≠ 0) : w.val (p.eval₂ ι t) = 1 := by
    let j : Polynomial k →+* K :=
      (algebraMap F K).comp (algebraMap (Polynomial k) F)
    have hj : j.comp Polynomial.C = ι := by
      apply RingHom.ext
      intro c
      change algebraMap F K (algebraMap (Polynomial k) F (Polynomial.C c)) =
        algebraMap F K (algebraMap k F c)
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) F]
      rfl
    have heval := Polynomial.hom_eval₂ p Polynomial.C j Polynomial.X
    rw [Polynomial.eval₂_C_X, hj] at heval
    change j p = p.eval₂ ι t at heval
    rw [← heval]
    exact w.trivial _ (fun hz => hp ((IsFractionRing.injective (Polynomial k) F)
      (hz.trans (map_zero _).symm)))
  have hpoly (p : k[X]) (hp : p ≠ 0) : (w.val.comap e) (aeval r p) = 1 := by
    change w.val (e (p.eval₂ (algebraMap k L) r)) = 1
    rw [Polynomial.hom_eval₂, heC]
    exact eval₂_value_one w.val ι hι htv hclose p (hTpoly p hp)
  exact (not_le_of_gt hvy) (no_pole_of_polynomial_values hdim (w.val.comap e) r y hpoly)
private theorem poleOrder_mono {F K : Type} [Field F] [Field K] [Algebra F K]
    (w : Place F K) {a b : K} (h : w.val a ≤ w.val b) : poleOrder w a ≤ poleOrder w b := by
  by_cases ha : w.val a = 0
  · simp [poleOrder, ha]
  have hb : w.val b ≠ 0 := ne_of_gt ((zero_lt_iff.mpr ha).trans_le h)
  exact Int.toNat_le_toNat ((WithZero.log_le_log ha hb).mpr h)
theorem proof : K1_14_2_2_7_4_4.c4 := by
  intro k _ D _ hprime hdim w
  let x := fieldCoord D (some 0)
  let y := fieldCoord D (some 1)
  let t := algebraMap (SlopeField k) (CurveField D) (genericSlope k)
  have hty : w.val (t * y) = w.val y := by
    rw [map_mul, w.trivial _ genericSlope_ne_zero, one_mul]
  change max (poleOrder w x) (poleOrder w y) ≤ poleOrder w (seedParameter D)
  rcases lt_trichotomy (w.val x) (w.val y) with hlt | heq | hgt
  · have hs : w.val (seedParameter D) = w.val y := by
      rw [seedParameter_eq, show w.val (x + t * y) = w.val (t * y) from
        w.val.map_add_eq_of_lt_right (hty ▸ hlt), hty]
    exact max_le (poleOrder_mono w (hs ▸ hlt.le)) (poleOrder_mono w hs.ge)
  · by_cases hy : 1 < w.val y
    · have hs := second_seed_value_le_of_pole D hprime hdim w hy
      exact max_le (poleOrder_mono w (heq.trans_le hs)) (poleOrder_mono w hs)
    · have hzero : poleOrder w y = 0 := by
        by_cases hy0 : w.val y = 0
        · simp [poleOrder, hy0]
        · rw [poleOrder, Int.toNat_eq_zero]
          exact (WithZero.log_le_iff_le_exp hy0).mpr (by simpa using le_of_not_gt hy)
      have hxzero := (poleOrder_mono w heq.le).trans (le_of_eq hzero)
      exact (max_le hxzero (le_of_eq hzero)).trans (Nat.zero_le _)
  · have hs : w.val (seedParameter D) = w.val x := by
      rw [seedParameter_eq]
      exact w.val.map_add_eq_of_lt_left (hty ▸ hgt)
    exact max_le (poleOrder_mono w hs.ge) (poleOrder_mono w (hs ▸ hgt.le))
end
end K1_14_2_2_7_4_4_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 12
namespace K1_14_3R_3_2_1
noncomputable section
open K1_14 K1_14_3 K1_14_3R_3_2 Polynomial
open scoped Polynomial nonZeroDivisors
private abbrev Raw := MvPolynomial Coordinates JetParameters
private def rawRow : Jet →+* Raw :=
  eval₂RingHom (eval₂RingHom
    (MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) (MvPolynomial.X ∘ some))
    (MvPolynomial.C (MvPolynomial.X 1) - MvPolynomial.C (MvPolynomial.X 0) * MvPolynomial.X none))
    (MvPolynomial.X none)
private def toRaw : Jet[X] →+* Raw :=
  eval₂RingHom rawRow (MvPolynomial.C (MvPolynomial.X 0))
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance : Algebra Jet[X] CurveAmbient :=
  ((algebraMap Raw CurveAmbient).comp toRaw).toAlgebra
end
end K1_14_3R_3_2_1
end
section
set_option autoImplicit false
namespace K1_14_3R_3_1_3
noncomputable section
open K1_13_6_3_5_3 (CurvePlace poleOrder)
open scoped BigOperators Polynomial WithZero nonZeroDivisors
variable {k F : Type} [Field k] [Field F] [Algebra k F]
abbrev PlaceResidue (p : CurvePlace k F) := IsLocalRing.ResidueField p.value.valuationSubring
def placeConstants (p : CurvePlace k F) : k →+* p.value.valuationSubring :=
  (algebraMap k F).codRestrict p.value.valuationSubring.toSubring (fun a => by
    change p.value (algebraMap k F a) ≤ 1
    obtain rfl | ha := eq_or_ne a 0
    · simp
    · rw [p.on_constants _ ha])
instance placeResidueAlgebra (p : CurvePlace k F) : Algebra k (PlaceResidue p) :=
  ((IsLocalRing.residue _).comp (placeConstants p)).toAlgebra
def placeWeight (p : CurvePlace k F) : ℕ :=
  Module.finrank k (PlaceResidue p)
@[instance_reducible]
def chartAlgebra (u : F) : Algebra k[X] F :=
  (Polynomial.aeval u).toRingHom.toAlgebra
abbrev inverseChart (x : F) :=
  letI := chartAlgebra (k := k) x⁻¹
  integralClosure k[X] F
def weightedPoleDegree (x : F) : ℕ :=
  ∑ᶠ p : CurvePlace k F, placeWeight p * poleOrder p.value x
theorem pencilAlgebra_polynomial (P : k[X]) :
    letI := K1_14_3R_3_1.pencilAlgebra k (F := F)
    algebraMap (RatFunc k) (RatFunc F) (algebraMap k[X] (RatFunc k) P) =
      algebraMap F[X] (RatFunc F) (P.map (algebraMap k F)) := by
  let f := Polynomial.mapRingHom (algebraMap k F)
  let hf : k[X]⁰ ≤ F[X]⁰.comap f :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap k F).injective)
  change RatFunc.map f hf (algebraMap k[X] _ P) = algebraMap F[X] _ (f P)
  simpa only [map_one, div_one] using RatFunc.map_apply_div f hf P 1
def GaussAt [Algebra (RatFunc k) (RatFunc F)]
    (p : CurvePlace k F) (q : CurvePlace (RatFunc k) (RatFunc F)) : Prop :=
  ∀ P : F[X], q.value (algebraMap F[X] (RatFunc F) P) =
    P.support.sup (fun i => p.value (P.coeff i))
end
end K1_14_3R_3_1_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace K1_14_3R_3_1_3_2
noncomputable section
open Polynomial IntermediateField
open scoped nonZeroDivisors
variable {k F : Type} [Field k] [Field F] [Algebra k F]
abbrev origin (k : Type) [Field k] : Ideal k[X] := Ideal.span {Polynomial.X}
instance origin_maximal : (origin k).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible irreducible_X
def originQuotient : (k[X] ⧸ origin k) ≃ₐ[k] k := by
  rw [show origin k = Ideal.span {Polynomial.X - C (0 : k)} by simp]
  exact quotientSpanXSubCAlgEquiv 0
abbrev chartField (u : F) := IntermediateField.adjoin k ({u} : Set F)
theorem chartField_inv (x : F) : chartField (k := k) x⁻¹ = chartField (k := k) x := by
  apply le_antisymm <;> apply IntermediateField.adjoin_le_iff.mpr
  · exact Set.singleton_subset_iff.mpr (IntermediateField.inv_mem _ (mem_adjoin_simple_self k x))
  · apply Set.singleton_subset_iff.mpr
    change x ∈ chartField (k := k) x⁻¹
    simpa only [inv_inv] using
      (chartField (k := k) x⁻¹).inv_mem (mem_adjoin_simple_self k x⁻¹)
section Chart
variable [Algebra k[X] F] [IsScalarTower k k[X] F]
def coordinate (k : Type) [Field k] (F : Type) [Field F] [Algebra k[X] F] : F :=
  algebraMap k[X] F Polynomial.X
abbrev Normalization (k : Type) [Field k] (F : Type) [Field F] [Algebra k[X] F] :=
  integralClosure k[X] F
private theorem chart_aeval (f : k[X]) : algebraMap k[X] F f = aeval (coordinate k F) f := by
  have h : IsScalarTower.toAlgHom k k[X] F = aeval (coordinate k F) :=
    Polynomial.algHom_ext (by simp [coordinate])
  exact DFunLike.congr_fun h f
private theorem chart_injective (h : Transcendental k (coordinate k F)) :
    Function.Injective (algebraMap k[X] F) := by
  intro p q hpq
  apply (transcendental_iff_injective.mp h)
  rwa [← chart_aeval (F := F) p, ← chart_aeval (F := F) q]
theorem normalization_torsionFree (h : Transcendental k (coordinate k F)) :
    Module.IsTorsionFree k[X] (Normalization k F) := by
  have : Module.IsTorsionFree k[X] F :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (chart_injective h)
  exact IsIntegralClosure.isTorsionFree k[X] F
local instance chartFieldAlgebra : Algebra k[X] (chartField (k := k) (coordinate k F)) :=
  (aeval (AdjoinSimple.gen k (coordinate k F))).toRingHom.toAlgebra
local instance chartFieldTower : IsScalarTower k[X] (chartField (k := k) (coordinate k F)) F :=
  IsScalarTower.of_algebraMap_eq fun f => by
    rw [chart_aeval (F := F) f]
    exact aeval_algHom_apply (chartField (k := k) (coordinate k F)).val
      (AdjoinSimple.gen k (coordinate k F)) f
private theorem chartField_isFractionRing (h : Transcendental k (coordinate k F)) :
    IsFractionRing k[X] (chartField (k := k) (coordinate k F)) := by
  let K := chartField (k := k) (coordinate k F)
  have : FaithfulSMul k[X] K := (faithfulSMul_iff_algebraMap_injective k[X] K).mpr
    (fun _ _ e => chart_injective h (by
      rw [IsScalarTower.algebraMap_eq k[X] K F]
      exact congrArg (algebraMap K F) e))
  apply IsFractionRing.of_field
  intro z
  obtain ⟨p, q, hpq⟩ := (mem_adjoin_simple_iff k (z : F)).mp z.property
  refine ⟨p, q, (algebraMap K F).injective ?_⟩
  rw [map_div₀, ← IsScalarTower.algebraMap_apply k[X] K F,
    ← IsScalarTower.algebraMap_apply k[X] K F, chart_aeval (F := F) p, chart_aeval (F := F) q]
  exact hpq
theorem normalization_fraction (h : Transcendental k (coordinate k F))
    [FiniteDimensional (chartField (k := k) (coordinate k F)) F] :
    IsFractionRing (Normalization k F) F := by
  have := chartField_isFractionRing h
  exact integralClosure.isFractionRing_of_finite_extension
    (chartField (k := k) (coordinate k F)) F
theorem normalization_dedekind (h : Transcendental k (coordinate k F))
    [FiniteDimensional (chartField (k := k) (coordinate k F)) F]
    [Module.Finite k[X] (Normalization k F)] :
    IsDedekindDomain (Normalization k F) := by
  let B := Normalization k F
  have := chartField_isFractionRing h
  exact
    { isNoetherianRing_iff.mpr (isNoetherian_of_tower k[X] (show IsNoetherian k[X] B from inferInstance)),
      Ring.DimensionLEOne.of_isIntegral k[X] B,
      integralClosure.isIntegrallyClosedOfFiniteExtension
        (chartField (k := k) (coordinate k F)) with }
theorem normalization_rank (h : Transcendental k (coordinate k F))
    [FiniteDimensional (chartField (k := k) (coordinate k F)) F]
    [Module.Finite k[X] (Normalization k F)] :
    Module.finrank k[X] (Normalization k F) =
      Module.finrank (chartField (k := k) (coordinate k F)) F := by
  let K := chartField (k := k) (coordinate k F)
  let B := Normalization k F
  have : IsFractionRing k[X] K := chartField_isFractionRing h
  have : Module.IsTorsionFree k[X] B := normalization_torsionFree h
  have : IsLocalization (Algebra.algebraMapSubmonoid B k[X]⁰) F :=
    IsIntegralClosure.isLocalization k[X] K F B
  let b := Module.Basis.localizationLocalization K k[X]⁰ F (Module.Free.chooseBasis k[X] B)
  rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_eq_card_basis b]
end Chart
end
end K1_14_3R_3_1_3_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000
namespace K1_14_2_2_7_3_3
noncomputable section
open K1_14_2 K1_14_2_2_7_3
open K1_14_3R_3_1 (functionDegree toFunction jetPencilDegree)
open scoped BigOperators
def c1 : Prop :=
  ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A], ringKrullDim A = 1 →
    ∀ (x y : A), Nonempty (PoleProfile k A x y)
def c2 : Prop :=
  ∀ (k : Type) [Field k] (H : Ideal (MvPolynomial (Fin 4) k)) [H.IsPrime],
    ringKrullDim (CoordinateRing H) = 1 →
    Module.Finite (PlaneField k) (SeedFibre H) →
    Module.Finite (PlaneField k) (VFibre H) →
    Module.finrank (PlaneField k) (SeedFibre H) =
      jetPencilDegree k (toFunction (coord H 0)) (toFunction (coord H 1)) ∧
    Module.finrank (PlaneField k) (VFibre H) =
      functionDegree k (toFunction (coord H 3))
section Estimates
variable {k A : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
  {x y : A} (D : PoleProfile k A x y) (p : Fin D.places)
private theorem pole_sum_le {ι : Type} (S : Finset ι) (f : ι → A) (d : ℕ)
    (h : ∀ i ∈ S, D.order p (f i) ≤ d) : D.order p (∑ i ∈ S, f i) ≤ d := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa using (D.scalar p 0).le.trans (Nat.zero_le d)
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (D.add p _ _).trans (max_le (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))))
private theorem pole_pow_le (f : A) (n : ℕ) : D.order p (f ^ n) ≤ n * D.order p f := by
  induction n with
  | zero => simpa using (D.scalar p 1).le
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (D.mul p _ _).trans (Nat.add_le_add_right ih _)
private theorem seed_pole_bound (z : Fin 2 → A) (f : MvPolynomial (Fin 2) k) :
    D.order p (MvPolynomial.eval₂ (algebraMap k A) z f) ≤
      f.totalDegree * max (D.order p (z 0)) (D.order p (z 1)) := by
  classical
  rw [MvPolynomial.eval₂_eq']
  apply pole_sum_le D p
  intro e he
  have hdeg := MvPolynomial.le_totalDegree he
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at hdeg
  rw [Fin.prod_univ_two]
  apply (D.mul p _ _).trans
  rw [D.scalar, zero_add]
  apply (D.mul p _ _).trans
  calc
    _ ≤ e 0 * max (D.order p (z 0)) (D.order p (z 1)) +
        e 1 * max (D.order p (z 0)) (D.order p (z 1)) :=
      Nat.add_le_add
        ((pole_pow_le D p _ _).trans (Nat.mul_le_mul_left _ (le_max_left _ _)))
        ((pole_pow_le D p _ _).trans (Nat.mul_le_mul_left _ (le_max_right _ _)))
    _ ≤ _ := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hdeg
end Estimates
private theorem cut_expansion {k : Type} [Field k] (H : Ideal (MvPolynomial (Fin 4) k))
    (G : Polynomial (MvPolynomial (Fin 2) k)) :
    cutFunction H G =
      ∑ j ∈ G.support, MvPolynomial.eval₂ (algebraMap k (CoordinateRing H)) (seedCoord H)
        (G.coeff j) * coord H 3 ^ j := by
  let q := Ideal.Quotient.mk H
  let r : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 4) k :=
    (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 4))).toRingHom
  have heval : q.comp r = MvPolynomial.eval₂Hom (algebraMap k (CoordinateRing H)) (seedCoord H) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, r, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.rename_C, MvPolynomial.eval₂Hom_C]
      exact (Ideal.Quotient.mk_algebraMap (R₁ := k) H a).symm
    · intro i
      simp [q, r, seedCoord, coord]
  change q (G.eval₂ r (MvPolynomial.X 3)) = _
  rw [Polynomial.hom_eval₂, heval, Polynomial.eval₂_eq_sum]
  rfl
private theorem cut_degree_bound {k : Type} [Field k] (H : Ideal (MvPolynomial (Fin 4) k))
    [H.IsPrime] (D : PoleProfile k (CoordinateRing H) (coord H 0) (coord H 1))
    {G : Polynomial (MvPolynomial (Fin 2) k)} {U J : ℕ} (hJ : G.natDegree ≤ J)
    (hU : ∀ j, (G.coeff j).totalDegree ≤ U) :
    functionDegree k (toFunction (cutFunction H G)) ≤
      U * jetPencilDegree k (toFunction (coord H 0)) (toFunction (coord H 1)) +
      J * functionDegree k (toFunction (coord H 3)) := by
  classical
  have hbound (p : Fin D.places) :
      D.order p (cutFunction H G) ≤
        U * max (D.order p (coord H 0)) (D.order p (coord H 1)) +
        J * D.order p (coord H 3) := by
    rw [cut_expansion]
    apply pole_sum_le D p
    intro j hj
    have hdeg := (Polynomial.le_natDegree_of_mem_supp j hj).trans hJ
    apply (D.mul p _ _).trans
    apply Nat.add_le_add
    · exact (seed_pole_bound D p (seedCoord H) (G.coeff j)).trans
        (Nat.mul_le_mul_right _ (hU j))
    · exact (pole_pow_le D p _ j).trans (Nat.mul_le_mul_right _ hdeg)
  rw [← D.degree_eq (cutFunction H G), ← D.pencil_eq, ← D.degree_eq (coord H 3)]
  calc
    _ ≤ ∑ p, D.weight p *
        (U * max (D.order p (coord H 0)) (D.order p (coord H 1)) +
          J * D.order p (coord H 3)) :=
      Finset.sum_le_sum fun p _ => Nat.mul_le_mul_left _ (hbound p)
    _ = _ := by
      simp only [Nat.mul_add, Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_left_comm]
private def cutEquiv {k : Type} [Field k] (H : Ideal (MvPolynomial (Fin 4) k))
    (G : Polynomial (MvPolynomial (Fin 2) k)) :
    (CoordinateRing H ⧸ Ideal.span {cutFunction H G}) ≃ₐ[k]
      CoordinateRing (H ⊔ Ideal.span {blockEval G}) := by
  let I : Ideal (MvPolynomial (Fin 4) k) := Ideal.span {blockEval G}
  have hmap : I.map (Ideal.Quotient.mkₐ k H) = Ideal.span {cutFunction H G} := by
    dsimp only [I]
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  exact (Ideal.quotientEquivAlgOfEq k hmap.symm).trans (DoubleQuot.quotQuotEquivQuotSupₐ k H I)
theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_2_7_3.c3 := by
  intro k _ H U J G hprime hdim hseed hv hJ hU hG
  let : H.IsPrime := hprime
  let : Algebra.FiniteType k (CoordinateRing H) := Algebra.FiniteType.quotient k H
  have hne : cutFunction H G ≠ 0 :=
    fun hz => hG (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hfin := principal_finite (k := k) hdim hne
  obtain ⟨D⟩ := h1 k (CoordinateRing H) hdim (coord H 0) (coord H 1)
  obtain ⟨hseedDegree, hvDegree⟩ := h2 k H hdim hseed hv
  have hlength := (principal_length_le (k := k) hdim hne).trans (cut_degree_bound H D hJ hU)
  let e := (cutEquiv H G).toLinearEquiv
  let := hfin
  exact ⟨Module.Finite.equiv e, by rwa [← e.finrank_eq, hseedDegree, hvDegree]⟩
end
end K1_14_2_2_7_3_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3R_3_2_4
noncomputable section
open MvPolynomial TensorProduct
open scoped TensorProduct nonZeroDivisors
variable {k : Type} [Field k]
variable {σ : Type}
end
end K1_14_3R_3_2_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3R_3_1_3
noncomputable section
open K1_13_6_3_5_3 (CurvePlace)
open K1_14_3R_3_1 (pencilAlgebra)
open scoped Polynomial WithZero nonZeroDivisors
variable {k F : Type} [Field k] [Field F] [Algebra k F]
private def gaussValue (w : Valuation F ℤᵐ⁰) (P : F[X]) : ℤᵐ⁰ :=
  P.support.sup (fun n => w (P.coeff n))
private theorem coeff_le_gauss (w : Valuation F ℤᵐ⁰) (P : F[X]) (n : ℕ) :
    w (P.coeff n) ≤ gaussValue w P := by
  by_cases hn : P.coeff n = 0
  · simp [hn]
  · exact Finset.le_sup (f := fun i => w (P.coeff i))
      (Polynomial.mem_support_iff.mpr hn)
private theorem gaussValue_C (w : Valuation F ℤᵐ⁰) (a : F) :
    gaussValue w (Polynomial.C a) = w a := by
  by_cases ha : a = 0
  · simp [ha, gaussValue]
  · simp [gaussValue, Polynomial.support_C ha]
private theorem gaussValue_ne_zero (w : Valuation F ℤᵐ⁰) {P : F[X]} (hp : P ≠ 0) :
    gaussValue w P ≠ 0 := by
  obtain ⟨n, hn⟩ := Polynomial.support_nonempty.mpr hp
  have hv : 0 < w (P.coeff n) :=
    WithZero.pos_iff_ne_zero.mpr (w.zero_iff.not.mpr (Polynomial.mem_support_iff.mp hn))
  exact (hv.trans_le (coeff_le_gauss w P n)).ne'
private theorem exists_min_gauss (w : Valuation F ℤᵐ⁰) (P : F[X]) (hp : P ≠ 0) :
    ∃ i, w (P.coeff i) = gaussValue w P ∧
      ∀ n < i, w (P.coeff n) < gaussValue w P := by
  classical
  have hs := Polynomial.support_nonempty.mpr hp
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hs (fun n => w (P.coeff n))
  rw [Finset.sup'_eq_sup] at hi
  have hex : ∃ n, w (P.coeff n) = gaussValue w P := ⟨i, hi.symm⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun n hn =>
    lt_of_le_of_ne (coeff_le_gauss w P n) (Nat.find_min hex hn)⟩
private theorem gaussValue_mul (w : Valuation F ℤᵐ⁰) (P Q : F[X]) :
    gaussValue w (P * Q) = gaussValue w P * gaussValue w Q := by
  apply le_antisymm
  · apply Finset.sup_le
    intro n _
    rw [Polynomial.coeff_mul]
    apply w.map_sum_le
    intro a _
    rw [map_mul]
    exact mul_le_mul' (coeff_le_gauss w P a.1) (coeff_le_gauss w Q a.2)
  obtain rfl | hp := eq_or_ne P 0
  · simp [gaussValue]
  obtain rfl | hq := eq_or_ne Q 0
  · simp [gaussValue]
  obtain ⟨i, hi, hi_min⟩ := exists_min_gauss w P hp
  obtain ⟨j, hj, hj_min⟩ := exists_min_gauss w Q hq
  have hvp := WithZero.pos_iff_ne_zero.mpr (gaussValue_ne_zero w hp)
  have hvq := WithZero.pos_iff_ne_zero.mpr (gaussValue_ne_zero w hq)
  have hdominant : w ((P * Q).coeff (i + j)) = gaussValue w P * gaussValue w Q := by
    rw [Polynomial.coeff_mul]
    rw [w.map_sum_eq_of_lt (j := (i, j)) (by simp)]
    · simp only [map_mul, hi, hj]
    intro a ha
    obtain ⟨hamem, hane⟩ := Finset.mem_sdiff.mp ha
    have hsum : a.1 + a.2 = i + j := Finset.HasAntidiagonal.mem_antidiagonal.mp hamem
    simp only [map_mul, hi, hj]
    have hindex : a.1 < i ∨ a.2 < j := by
      by_contra! h
      apply hane
      apply Finset.mem_singleton.mpr
      exact Prod.ext (by omega) (by omega)
    rcases hindex with h | h
    · exact (mul_le_mul' le_rfl (coeff_le_gauss w Q a.2)).trans_lt
        (mul_lt_mul_of_pos_right (hi_min _ h) hvq)
    · exact (mul_le_mul' (coeff_le_gauss w P a.1) le_rfl).trans_lt
        (mul_lt_mul_of_pos_left (hj_min _ h) hvp)
  rw [← hdominant]
  exact coeff_le_gauss w (P * Q) (i + j)
private def gaussPolynomial (w : Valuation F ℤᵐ⁰) : Valuation F[X] ℤᵐ⁰ where
  toFun := gaussValue w
  map_zero' := by simp [gaussValue]
  map_one' := by simpa using gaussValue_C w 1
  map_mul' := gaussValue_mul w
  map_add_le_max' P Q := by
    apply Finset.sup_le
    intro n _
    rw [Polynomial.coeff_add]
    exact (w.map_add _ _).trans (max_le_max (coeff_le_gauss w P n) (coeff_le_gauss w Q n))
private def gaussRational (w : Valuation F ℤᵐ⁰) : Valuation (RatFunc F) ℤᵐ⁰ :=
  (gaussPolynomial w).extendToLocalization (S := F[X]⁰)
    (fun _ h => gaussValue_ne_zero w (nonZeroDivisors.ne_zero h)) (RatFunc F)
private theorem gaussRational_polynomial (w : Valuation F ℤᵐ⁰) (P : F[X]) :
    gaussRational w (algebraMap F[X] (RatFunc F) P) = gaussValue w P :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ _
private theorem gaussValue_map (p : CurvePlace k F) (P : k[X]) (hp : P ≠ 0) :
    gaussValue p.value (P.map (algebraMap k F)) = 1 := by
  have hmap : P.map (algebraMap k F) ≠ 0 := fun h =>
    hp ((Polynomial.map_injective _ (algebraMap k F).injective) (by simpa using h))
  unfold gaussValue
  rw [← Finset.sup'_eq_sup (Polynomial.support_nonempty.mpr hmap)]
  apply Finset.sup'_eq_of_forall
  intro i hi
  rw [Polynomial.coeff_map]
  apply p.on_constants
  intro hc
  exact (Polynomial.mem_support_iff.mp hi) (by simp [hc])
theorem exists_gauss_extension (p : CurvePlace k F) :
    letI := pencilAlgebra k (F := F)
    ∃ q : CurvePlace (RatFunc k) (RatFunc F), GaussAt p q := by
  let _ : Algebra (RatFunc k) (RatFunc F) := pencilAlgebra k (F := F)
  let q : CurvePlace (RatFunc k) (RatFunc F) := {
    value := gaussRational p.value
    normalized := by
      intro a
      obtain ⟨x, hx⟩ := p.normalized a
      exact ⟨RatFunc.C x, (gaussRational_polynomial p.value (Polynomial.C x)).trans
        ((gaussValue_C p.value x).trans hx)⟩
    on_constants := by
      intro a
      induction a using RatFunc.induction_on with
      | _ P Q hQ =>
        intro ha
        have hP : P ≠ 0 := by
          intro h
          exact ha (by simp [h])
        rw [map_div₀, (gaussRational p.value).map_div, pencilAlgebra_polynomial,
          pencilAlgebra_polynomial, gaussRational_polynomial, gaussRational_polynomial,
          gaussValue_map p P hP, gaussValue_map p Q hQ, div_one] }
  exact ⟨q, gaussRational_polynomial p.value⟩
end
end K1_14_3R_3_1_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
namespace K1_14_3R_3_1_3_2
noncomputable section
open K1_13_6_3_5_3 (CurvePlace poleOrder)
open K1_14_3R_3_1_3 (placeConstants)
open Polynomial WithZero IsDedekindDomain
open scoped WithZero nonZeroDivisors
variable {k F : Type} [Field k] [Field F] [Algebra k F]
private theorem pole_iff {v : Valuation F ℤᵐ⁰} {x : F} (hx : x ≠ 0) :
    poleOrder v x ≠ 0 ↔ v x⁻¹ < 1 := by
  have hv : v x ≠ 0 := (v.ne_zero_iff).mpr hx
  have hlog : 0 < log (v x) ↔ 1 < v x := by
    simpa only [log_one] using (log_lt_log (x := 1) one_ne_zero hv)
  rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.mpr hv), ← hlog, poleOrder]
  omega
private theorem least_value {v : ℤᵐ⁰} (h : 1 < v) : exp (1 : ℤ) ≤ v := by
  apply le_log_iff_exp_le (zero_lt_one.trans h).ne' |>.mp
  have : 0 < log v := by
    simpa only [log_one] using (log_lt_log one_ne_zero (zero_lt_one.trans h).ne').mpr h
  omega
private theorem normalized_eq {v w : Valuation F ℤᵐ⁰}
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) : v = w := by
  obtain ⟨a, ha⟩ := hv (exp 1)
  obtain ⟨b, hb⟩ := hw (exp 1)
  have hap : 1 < w a := h.one_lt_iff_one_lt.mp (by simp [ha])
  have hbp : 1 < v b := h.one_lt_iff_one_lt.mpr (by simp [hb])
  have haw : w a = exp 1 :=
    le_antisymm (hb ▸ (h a b).mp (ha ▸ least_value hbp)) (least_value hap)
  ext z
  obtain rfl | hz := eq_or_ne z 0
  · simp
  let n := log (v z)
  have he (t : Valuation F ℤᵐ⁰) (ht : t a = exp 1) : t (a ^ n) = exp n := by
    rw [map_zpow₀, ht, ← exp_zsmul]
    simp
  have hvz : v z = v (a ^ n) := by
    rw [he v ha, exp_log ((v.ne_zero_iff).mpr hz)]
  exact hvz.trans ((he v ha).trans ((he w haw).symm.trans (h.eq_iff.mp hvz).symm))
section Fibre
variable [Algebra k[X] F] [IsScalarTower k k[X] F]
abbrev OriginPrimes (k F : Type) [Field k] [Field F] [Algebra k[X] F] :=
  (origin k).primesOver (Normalization k F)
abbrev PolePlaces (k F : Type) [Field k] [Field F] [Algebra k F] (x : F) :=
  {p : CurvePlace k F // poleOrder p.value x ≠ 0}
private theorem chart_mem (p : CurvePlace k F) (hu : p.value (coordinate k F) < 1)
    (f : k[X]) : algebraMap k[X] F f ∈ p.value.valuationSubring := by
  let u : p.value.valuationSubring := ⟨coordinate k F, hu.le⟩
  let g : k[X] →+* p.value.valuationSubring := eval₂RingHom (placeConstants p) u
  have hg : p.value.valuationSubring.toSubring.subtype.comp g = algebraMap k[X] F := by
    apply Polynomial.ringHom_ext
    · intro a
      change ((g (C a) : p.value.valuationSubring) : F) = algebraMap k[X] F (C a)
      rw [show g (C a) = placeConstants p a from eval₂_C _ _]
      exact IsScalarTower.algebraMap_apply k k[X] F a
    · change ((g Polynomial.X : p.value.valuationSubring) : F) = coordinate k F
      rw [show g Polynomial.X = u from eval₂_X _ _]
  rw [← hg]
  exact (g f).property
private def normalizationToPlace (p : CurvePlace k F) (hu : p.value (coordinate k F) < 1) :
    Normalization k F →+* p.value.valuationSubring :=
  let V := p.value.valuationSubring.toSubring
  have : IsFractionRing V F := inferInstanceAs (IsFractionRing p.value.valuationSubring F)
  have : IsIntegrallyClosedIn V F :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn F).mp
      (inferInstanceAs (IsIntegrallyClosed p.value.valuationSubring))
  let h := Subring.integralClosure_le_iff.mpr (chart_mem p hu)
  (integralClosure k[X] F).val.toRingHom.codRestrict V (fun b => h b.property)
private def center (p : CurvePlace k F) (hu : p.value (coordinate k F) < 1) :
    Ideal (Normalization k F) :=
  (IsLocalRing.maximalIdeal p.value.valuationSubring).comap (normalizationToPlace p hu)
private theorem mem_center (p : CurvePlace k F) (hu : p.value (coordinate k F) < 1)
    (b : Normalization k F) : b ∈ center p hu ↔ p.value (b : F) < 1 :=
  p.value.mem_maximalIdeal_iff (a := normalizationToPlace p hu b)
private def centerPrime (p : CurvePlace k F) (hu : p.value (coordinate k F) < 1) :
    OriginPrimes k F := by
  let Q := center p hu
  have hQ : Q.IsPrime := Ideal.IsPrime.comap _
  have hX : algebraMap k[X] (Normalization k F) Polynomial.X ∈ Q :=
    (mem_center p hu _).mpr hu
  have hle : origin k ≤ Q.under k[X] := (Ideal.span_singleton_le_iff_mem _).mpr hX
  have hproper : Q.under k[X] ≠ ⊤ := (Ideal.IsPrime.comap (algebraMap k[X] _) (K := Q)).ne_top
  exact ⟨Q, hQ, ⟨(origin_maximal (k := k)).eq_of_le hproper hle⟩⟩
variable [IsDedekindDomain (Normalization k F)] [IsFractionRing (Normalization k F) F]
def primeAtOrigin (hcoord : coordinate k F ≠ 0) (P : OriginPrimes k F) :
    HeightOneSpectrum (Normalization k F) where
  asIdeal := P.val
  isPrime := P.property.1
  ne_bot := by
    have : P.val.LiesOver (origin k) := P.property.2
    have hX := (P.val.mem_of_liesOver (origin k) Polynomial.X).mp (Ideal.subset_span (by simp))
    intro h
    rw [h, Ideal.mem_bot] at hX
    apply hcoord
    rw [coordinate, IsScalarTower.algebraMap_apply k[X] (Normalization k F) F, hX, map_zero]
private def primePlace (hcoord : coordinate k F ≠ 0) (P : OriginPrimes k F) : CurvePlace k F where
  value := (primeAtOrigin hcoord P).valuation F
  normalized := (primeAtOrigin hcoord P).valuation_surjective F
  on_constants a ha := by
    let B := Normalization k F
    rw [IsScalarTower.algebraMap_apply k k[X] F,
      IsScalarTower.algebraMap_apply k[X] B F]
    apply (primeAtOrigin hcoord P).valuation_eq_one_iff_notMem.mpr
    have : P.val.IsPrime := P.property.1
    exact P.val.notMem_of_isUnit
      (((isUnit_iff_ne_zero.mpr ha).map (algebraMap k k[X])).map (algebraMap k[X] B))
private theorem primePlace_small (hcoord : coordinate k F ≠ 0) (P : OriginPrimes k F) :
    (primePlace hcoord P).value (coordinate k F) < 1 := by
  have : P.val.LiesOver (origin k) := P.property.2
  change (primeAtOrigin hcoord P).valuation F (algebraMap k[X] F Polynomial.X) < 1
  rw [IsScalarTower.algebraMap_apply k[X] (Normalization k F) F]
  exact ((primeAtOrigin hcoord P).valuation_lt_one_iff_mem _).mpr
    ((P.val.mem_of_liesOver (origin k) Polynomial.X).mp (Ideal.subset_span (by simp)))
private theorem center_valuation (hcoord : coordinate k F ≠ 0) (p : CurvePlace k F)
    (hu : p.value (coordinate k F) < 1) :
    (primePlace hcoord (centerPrime p hu)).value = p.value := by
  let Q := primeAtOrigin hcoord (centerPrime p hu)
  have hle : Q.valuationSubringAtPrime F ≤ p.value.valuationSubring := by
    rintro z ⟨a, b, hb, rfl⟩
    change p.value ((a : F) * (b : F)⁻¹) ≤ 1
    have hb' : ¬ p.value (b : F) < 1 := fun h => hb ((mem_center p hu b).mpr h)
    have hbound (c : Normalization k F) : p.value (c : F) ≤ 1 :=
      (normalizationToPlace p hu c).property
    have hval : p.value (b : F) = 1 := le_antisymm (hbound b) (not_lt.mp hb')
    rw [map_mul, map_inv₀, hval, inv_one, mul_one]
    exact hbound a
  have hproper : p.value.valuationSubring ≠ ⊤ := by
    intro ht
    obtain ⟨a, ha⟩ := p.normalized (exp 1)
    have hm : a ∈ p.value.valuationSubring := by rw [ht]; trivial
    exact (not_le_of_gt (show 1 < p.value a by simp [ha])) hm
  have h := ValuationSubring.eq_of_le_of_ne_top _ hle hproper
  rw [Q.valuationSubringAtPrime_eq_valuationSubring] at h
  exact normalized_eq (Q.valuation_surjective F) p.normalized
    ((Valuation.isEquiv_iff_valuationSubring _ _).mpr h)
def primePole (x : F) (hx : x ≠ 0) (hu : coordinate k F = x⁻¹)
    (P : OriginPrimes k F) : PolePlaces k F x :=
  let hcoord : coordinate k F ≠ 0 := hu ▸ inv_ne_zero hx
  ⟨primePlace hcoord P, (pole_iff hx).mpr (hu ▸ primePlace_small hcoord P)⟩
theorem primePole_bijective (x : F) (hx : x ≠ 0) (hu : coordinate k F = x⁻¹) :
    Function.Bijective (primePole x hx hu) := by
  let hcoord : coordinate k F ≠ 0 := hu ▸ inv_ne_zero hx
  constructor
  · intro P Q h
    apply Subtype.ext
    have hv : (primeAtOrigin hcoord P).valuation F = (primeAtOrigin hcoord Q).valuation F :=
      congrArg (fun p : PolePlaces k F x => p.val.value) h
    exact congrArg HeightOneSpectrum.asIdeal (HeightOneSpectrum.valuation_injective F hv)
  · rintro ⟨p, hp⟩
    have hsmall : p.value (coordinate k F) < 1 := hu.symm ▸ (pole_iff hx).mp hp
    refine ⟨centerPrime p hsmall, Subtype.ext ?_⟩
    have h := center_valuation hcoord p hsmall
    change primePlace hcoord (centerPrime p hsmall) = p
    generalize primePlace hcoord (centerPrime p hsmall) = q at h ⊢
    cases q
    cases p
    cases h
    rfl
theorem primePole_order (x : F) (hx : x ≠ 0) (hu : coordinate k F = x⁻¹)
    (P : OriginPrimes k F) :
    poleOrder (primePole x hx hu P).val.value x = P.val.ramificationIdx k[X] := by
  let hcoord : coordinate k F ≠ 0 := hu ▸ inv_ne_zero hx
  let Q := primeAtOrigin hcoord P
  let B := Normalization k F
  let b := algebraMap k[X] B Polynomial.X
  have hb : b ≠ 0 := by
    intro hb
    apply hcoord
    rw [coordinate, IsScalarTower.algebraMap_apply k[X] B F]
    change algebraMap B F b = 0
    rw [hb, map_zero]
  have hspan : (origin k).map (algebraMap k[X] B) = Ideal.span {b} := by
    rw [origin, Ideal.map_span, Set.image_singleton]
  have : P.val.IsPrime := P.property.1
  have : P.val.LiesOver (origin k) := P.property.2
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (origin k) P.val (by
    rw [hspan, Ne, Ideal.span_singleton_eq_bot]
    exact hb)
  rw [hspan] at he
  change poleOrder (Q.valuation F) x = _
  have hx' : x = (algebraMap B F b)⁻¹ := by
    rw [← IsScalarTower.algebraMap_apply k[X] B F, ← coordinate, hu, inv_inv]
  rw [hx', poleOrder, map_inv₀, Q.valuation_of_algebraMap, Q.intValuation_eq_exp_neg_multiplicity hb]
  simp only [log_inv, log_exp, neg_neg, Int.toNat_natCast]
  change multiplicity P.val (Ideal.span {b}) = _
  exact he.symm
end Fibre
end
end K1_14_3R_3_1_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_3_3_1
noncomputable section
open Algebra
open K1_13_6_3_5_3 (CurveField)
open K1_14_2_2_7_3_3 (finite_function_field)
open K1_14_3R_3_1 (pencilAlgebra toFunction)
open K1_14_3R_3_1_3 (pencilAlgebra_polynomial)
open scoped Polynomial nonZeroDivisors IntermediateField.algebraAdjoinAdjoin
theorem affine_curve_field {k A : Type} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (hdim : ringKrullDim A = 1) :
    CurveField k (FractionRing A) := by
  have h : Algebra.Transcendental k A := by
    rw [Algebra.transcendental_iff_not_isAlgebraic]
    intro h
    let : Algebra.IsIntegral k A := ⟨fun a => (h.1 a).isIntegral⟩
    have hf : IsField A := isField_of_isIntegral_of_isField' (Field.toIsField k)
    exact zero_ne_one ((ringKrullDim_eq_zero_of_isField hf).symm.trans hdim)
  obtain ⟨a, ha⟩ := h.transcendental
  have ht : Transcendental k (toFunction a) :=
    (transcendental_algebraMap_iff (IsFractionRing.injective A (FractionRing A))).2 ha
  exact ⟨toFunction a, ht, finite_function_field hdim ht⟩
variable {k F : Type} [Field k] [Field F] [Algebra k F]
private theorem curve_trdeg (h : CurveField k F) : trdeg k F = 1 := by
  obtain ⟨t, ht, hfin⟩ := h
  let B := Algebra.adjoin k ({t} : Set F)
  let T := IntermediateField.adjoin k ({t} : Set F)
  let : Module.Finite T F := hfin
  have hB : Algebra.IsAlgebraic B F := Algebra.IsAlgebraic.trans B T F
  have hi : AlgebraicIndependent k (fun _ : Unit => t) :=
    (algebraicIndependent_singleton_iff ()).2 ht
  have hb := hi.isTranscendenceBasis_iff_isAlgebraic.mpr
    (show Algebra.IsAlgebraic (Algebra.adjoin k (Set.range (fun _ : Unit => t))) F by
      rwa [Set.range_const])
  simpa using hb.cardinalMk_eq_trdeg.symm
private theorem curve_of_trdeg [Algebra.EssFiniteType k F] (h : trdeg k F = 1) :
    CurveField k F := by
  have htrans : Algebra.Transcendental k F :=
    trdeg_ne_zero_iff.mp (h.trans_ne one_ne_zero)
  obtain ⟨t, ht⟩ := htrans.transcendental
  have hi : AlgebraicIndependent k (fun _ : Unit => t) :=
    (algebraicIndependent_singleton_iff ()).2 ht
  have hb := hi.isTranscendenceBasis_of_trdeg_le_of_finite (by simp [h])
  let E := IntermediateField.adjoin k ({t} : Set F)
  have hrange : Set.range (fun _ : Unit => t) = {t} := Set.range_const
  let : Algebra.IsAlgebraic E F := Eq.mp
    (congrArg (fun s => Algebra.IsAlgebraic (IntermediateField.adjoin k s) F) hrange)
    hb.isAlgebraic_field
  have : Algebra.EssFiniteType E F := Algebra.EssFiniteType.of_comp k E F
  exact ⟨t, ht, Algebra.finite_of_essFiniteType_of_isAlgebraic⟩
private theorem ratFunc_trdeg (E : Type) [Field E] : trdeg E (RatFunc E) = 1 := by
  have : Algebra.IsAlgebraic E[X] (RatFunc E) :=
    IsLocalization.isAlgebraic _ E[X]⁰
  have : FaithfulSMul E[X] (RatFunc E) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  simpa [Polynomial.trdeg_of_isDomain, trdeg_eq_zero (R := E[X]) (A := RatFunc E)] using
    (trdeg_add_eq (A := RatFunc E) E E[X]).symm
private theorem ratFunc_essFiniteType (E : Type) [Field E] :
    Algebra.EssFiniteType E (RatFunc E) := by
  let : Algebra.EssFiniteType E[X] (RatFunc E) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc E) E[X]⁰
  exact Algebra.EssFiniteType.comp E E[X] (RatFunc E)
attribute [local instance] Polynomial.algebra
theorem pencil_curve_field (h : CurveField k F) :
    letI := pencilAlgebra k (F := F)
    CurveField (RatFunc k) (RatFunc F) := by
  let : Algebra (RatFunc k) (RatFunc F) := pencilAlgebra k (F := F)
  have : IsScalarTower k (RatFunc k) (RatFunc F) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      simp only [IsScalarTower.algebraMap_apply k k[X] (RatFunc k),
        IsScalarTower.algebraMap_apply k F (RatFunc F),
        IsScalarTower.algebraMap_apply F F[X] (RatFunc F),
        pencilAlgebra_polynomial]
      change algebraMap F[X] (RatFunc F) (Polynomial.C (algebraMap k F a)) =
        algebraMap F[X] (RatFunc F) ((Polynomial.C a).map (algebraMap k F))
      rw [Polynomial.map_C]
  have htr := curve_trdeg h
  obtain ⟨t, _, hfin⟩ := h
  let T := IntermediateField.adjoin k ({t} : Set F)
  let : Module.Finite T F := hfin
  have : Algebra.EssFiniteType k T := IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton t))
  have : Algebra.EssFiniteType k F := Algebra.EssFiniteType.comp k T F
  have := ratFunc_essFiniteType F
  have : Algebra.EssFiniteType k (RatFunc F) := Algebra.EssFiniteType.comp k F (RatFunc F)
  have : Algebra.EssFiniteType (RatFunc k) (RatFunc F) :=
    Algebra.EssFiniteType.of_comp k (RatFunc k) (RatFunc F)
  have hrank : trdeg k (RatFunc F) = (1 : Cardinal) + 1 := by
    rw [← trdeg_add_eq (A := RatFunc F) k F, htr, ratFunc_trdeg F]
  apply curve_of_trdeg
  apply Cardinal.add_one_inj.mp
  rw [add_comm (trdeg (RatFunc k) (RatFunc F)), ← ratFunc_trdeg k,
    trdeg_add_eq (A := RatFunc F) k (RatFunc k), hrank, ratFunc_trdeg k]
end
end K1_14_2_2_7_3_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace K1_14_3R_3_1_3
noncomputable section
open K1_14_3R_3_1 (SeparatingParameter functionDegree jetPencilDegree pencilAlgebra
  PoleProfile toFunction)
open K1_13_6_3_5_3 (CurvePlace poleOrder)
open scoped BigOperators Polynomial WithZero
def c1 : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (t x : F),
    SeparatingParameter k t → Transcendental k x →
    FiniteDimensional (IntermediateField.adjoin k {x}) F ∧
      Module.Finite k[X] (inverseChart (k := k) x)
def c2 : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (x : F),
    Transcendental k x → FiniteDimensional (IntermediateField.adjoin k {x}) F →
    Module.Finite k[X] (inverseChart (k := k) x) →
    (fun p : CurvePlace k F => poleOrder p.value x).HasFiniteSupport ∧
      (∀ p : CurvePlace k F, poleOrder p.value x ≠ 0 →
        FiniteDimensional k (PlaceResidue p)) ∧
      weightedPoleDegree (k := k) x = functionDegree k x
def c3 : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (t : F),
    SeparatingParameter k t →
    letI := pencilAlgebra k (F := F)
    SeparatingParameter (RatFunc k) (RatFunc.C t)
def c4 : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (p : CurvePlace k F),
    FiniteDimensional k (PlaceResidue p) →
    letI := pencilAlgebra k (F := F)
    ∀ q : CurvePlace (RatFunc k) (RatFunc F), GaussAt p q →
      placeWeight q = placeWeight p
def c5 : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F],
    (∀ p : CurvePlace k F, FiniteDimensional k (PlaceResidue p)) →
    letI := pencilAlgebra k (F := F)
    ∀ q : CurvePlace (RatFunc k) (RatFunc F),
      (∀ x : F, q.value (RatFunc.C x) ≤ 1) ∨ ∃ p : CurvePlace k F, GaussAt p q
section PoleOrder
variable {k F : Type} [Field k] [Field F] [Algebra k F]
end PoleOrder
section Pencil
variable {k F : Type} [Field k] [Field F] [Algebra k F]
local instance : Algebra (RatFunc k) (RatFunc F) := pencilAlgebra k (F := F)
end Pencil
end
end K1_14_3R_3_1_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace K1_14_2_2_7_3_3_2
noncomputable section
open K1_14_2 K1_14_2_2_7_3
open scoped nonZeroDivisors
abbrev Parameters (k : Type) [Field k] := MvPolynomial (Fin 2) k
abbrev Ambient (R : Type) [CommRing R] := MvPolynomial (Fin 4) R
variable {k : Type} [Field k]
def intercept (H : Ideal (Ambient k)) (g h : Ambient k) : Polynomial (CoordinateRing H) :=
  Polynomial.C (Ideal.Quotient.mk H g) + Polynomial.X * Polynomial.C (Ideal.Quotient.mk H h)
def parameterEval (H : Ideal (Ambient k)) (g h : Ambient k) :
    Parameters k →+* Polynomial (CoordinateRing H) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap k (CoordinateRing H)))
    ![Polynomial.X, intercept H g h]
@[simp] theorem parameterEval_C (H : Ideal (Ambient k)) (g h : Ambient k) (a : k) :
    parameterEval H g h (MvPolynomial.C a) = Polynomial.C (algebraMap k (CoordinateRing H) a) := by
  simp [parameterEval]
@[simp] theorem parameterEval_X0 (H : Ideal (Ambient k)) (g h : Ambient k) :
    parameterEval H g h (MvPolynomial.X 0) = Polynomial.X := by simp [parameterEval]
@[simp] theorem parameterEval_X1 (H : Ideal (Ambient k)) (g h : Ambient k) :
    parameterEval H g h (MvPolynomial.X 1) = intercept H g h := by simp [parameterEval]
def fibreEquation {R : Type} [CommRing R] (f : k →+* R) (s t : R) (g h : Ambient k) :
    Ambient R :=
  MvPolynomial.map f g + MvPolynomial.C s * MvPolynomial.map f h - MvPolynomial.C t
def fibreIdeal (H : Ideal (Ambient k)) (g h : Ambient k) : Ideal (Ambient (PlaneField k)) :=
  H.map (genericBase k) ⊔ Ideal.span
    {fibreEquation (algebraMap k (PlaneField k)) (planeScalar k 0) (planeScalar k 1) g h}
private def beforeBase : Ambient k →+* Ambient (Parameters k) :=
  MvPolynomial.map MvPolynomial.C
private def beforeIdeal (H : Ideal (Ambient k)) (g h : Ambient k) :
    Ideal (Ambient (Parameters k)) :=
  H.map beforeBase ⊔ Ideal.span
    {fibreEquation MvPolynomial.C (MvPolynomial.X 0) (MvPolynomial.X 1) g h}
private def beforeEval (H : Ideal (Ambient k)) (g h : Ambient k) :
    Ambient (Parameters k) →+* Polynomial (CoordinateRing H) :=
  MvPolynomial.eval₂Hom (parameterEval H g h)
    (fun i => Polynomial.C (Ideal.Quotient.mk H (MvPolynomial.X i)))
private theorem beforeEval_comp (H : Ideal (Ambient k)) (g h : Ambient k) :
    (beforeEval H g h).comp beforeBase = Polynomial.C.comp (Ideal.Quotient.mk H) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [beforeBase, beforeEval]
    rfl
  · intro i
    simp [beforeBase, beforeEval]
private theorem beforeEval_surjective (H : Ideal (Ambient k)) (g h : Ambient k) :
    Function.Surjective (beforeEval H g h) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p', rfl⟩ := hp
    obtain ⟨q', rfl⟩ := hq
    exact ⟨p' + q', map_add _ _ _⟩
  | monomial n a =>
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := H) a
    refine ⟨beforeBase b * MvPolynomial.C (MvPolynomial.X 0) ^ n, ?_⟩
    rw [map_mul, map_pow, ← RingHom.comp_apply, beforeEval_comp, RingHom.comp_apply]
    rw [show beforeEval H g h (MvPolynomial.C (MvPolynomial.X 0)) = Polynomial.X by
      simp [beforeEval], Polynomial.C_mul_X_pow_eq_monomial]
private theorem beforeIdeal_eq_ker (H : Ideal (Ambient k)) (g h : Ambient k) :
    beforeIdeal H g h = RingHom.ker (beforeEval H g h) := by
  let D := beforeIdeal H g h
  let q := Ideal.Quotient.mk D
  have hD : D ≤ RingHom.ker (beforeEval H g h) := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, beforeEval_comp]
      intro p hp
      exact RingHom.mem_ker.mpr (by simp [Ideal.Quotient.eq_zero_iff_mem.mpr hp])
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      apply RingHom.mem_ker.mpr
      have he (p : Ambient k) : beforeEval H g h (beforeBase p) =
          Polynomial.C (Ideal.Quotient.mk H p) := RingHom.congr_fun (beforeEval_comp H g h) p
      simp only [fibreEquation, map_sub, map_add, map_mul, ← show beforeBase = MvPolynomial.map
        (MvPolynomial.C : k →+* Parameters k) from rfl, he]
      rw [show beforeEval H g h (MvPolynomial.C (MvPolynomial.X 0)) = Polynomial.X by
          simp [beforeEval],
        show beforeEval H g h (MvPolynomial.C (MvPolynomial.X 1)) = intercept H g h by
          simp [beforeEval], intercept, sub_self]
  let u : CoordinateRing H →+* Ambient (Parameters k) ⧸ D :=
    Ideal.Quotient.lift H (q.comp beforeBase)
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_left (Ideal.mem_map_of_mem beforeBase ha)))
  let v : Polynomial (CoordinateRing H) →+* Ambient (Parameters k) ⧸ D :=
    Polynomial.eval₂RingHom u (q (MvPolynomial.C (MvPolynomial.X 0)))
  have hrel :
      q (beforeBase g) + q (MvPolynomial.C (MvPolynomial.X 0)) * q (beforeBase h) =
        q (MvPolynomial.C (MvPolynomial.X 1)) := by
    apply sub_eq_zero.mp
    simp only [← map_mul, ← map_add, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have he : v.comp (beforeEval H g h) = q := by
    apply MvPolynomial.ringHom_ext
    · have hC : (v.comp (beforeEval H g h)).comp MvPolynomial.C = q.comp MvPolynomial.C := by
        apply MvPolynomial.ringHom_ext
        · intro a
          simp only [RingHom.comp_apply, beforeEval, MvPolynomial.eval₂Hom_C, parameterEval_C,
            v, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
          rw [← Ideal.Quotient.mk_algebraMap (R₁ := k) H a]
          simp only [u, Ideal.Quotient.lift_mk, RingHom.comp_apply, beforeBase,
            MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
        · intro i
          simp only [RingHom.comp_apply, beforeEval, MvPolynomial.eval₂Hom_C]
          fin_cases i
          · change v (parameterEval H g h (MvPolynomial.X 0)) = _
            simp [v]
          · change v (parameterEval H g h (MvPolynomial.X 1)) = _
            simp only [parameterEval_X1, intercept, map_add, map_mul, v,
              Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X, u,
              Ideal.Quotient.lift_mk, RingHom.comp_apply]
            exact hrel
      exact RingHom.congr_fun hC
    · intro i
      simp only [RingHom.comp_apply, beforeEval, MvPolynomial.eval₂Hom_X', v,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, u, Ideal.Quotient.lift_mk,
        beforeBase, MvPolynomial.map_X]
  refine le_antisymm hD fun a ha => Ideal.Quotient.eq_zero_iff_mem.mp ?_
  have ha' := RingHom.congr_fun he a
  rw [RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero] at ha'
  exact ha'.symm
attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem localized_beforeIdeal (H : Ideal (Ambient k)) (g h : Ambient k) :
    (beforeIdeal H g h).map
        (algebraMap (Ambient (Parameters k)) (Ambient (PlaneField k))) = fibreIdeal H g h := by
  rw [beforeIdeal, Ideal.map_sup, Ideal.map_map, Ideal.map_span, Set.image_singleton]
  change H.map ((MvPolynomial.map (algebraMap (Parameters k) (PlaneField k))).comp beforeBase) ⊔
      Ideal.span {MvPolynomial.map (algebraMap (Parameters k) (PlaneField k))
        (fibreEquation MvPolynomial.C (MvPolynomial.X 0) (MvPolynomial.X 1) g h)} = _
  rw [fibreIdeal]
  have hcomp : (MvPolynomial.map (algebraMap (Parameters k) (PlaneField k))).comp beforeBase =
      genericBase k := by
    apply MvPolynomial.ringHom_ext <;> intro a <;> simp [beforeBase, genericBase]
    rfl
  rw [hcomp]
  simp only [fibreEquation, map_sub, map_add, map_mul, MvPolynomial.map_C, planeScalar,
    MvPolynomial.map_map]
  rfl
abbrev parameterRank (H : Ideal (Ambient k)) (g h : Ambient k) : ℕ :=
  @Module.finrank (Parameters k) (Polynomial (CoordinateRing H)) _ _
    (parameterEval H g h).toAlgebra.toModule
set_option backward.isDefEq.respectTransparency true in
theorem fibre_finrank (H : Ideal (Ambient k)) (g h : Ambient k) :
    Module.finrank (PlaneField k) (CoordinateRing (fibreIdeal H g h)) =
      parameterRank H g h := by
  let R := Parameters k
  let S := PlaneField k
  let D := Polynomial (CoordinateRing H)
  let B := CoordinateRing (fibreIdeal H g h)
  let f := beforeEval H g h
  let q := Ideal.Quotient.mk (fibreIdeal H g h)
  let : Algebra (Ambient R) (Ambient S) := MvPolynomial.algebraMvPolynomial
  let M : Submonoid (Ambient R) := R⁰.map MvPolynomial.C
  let : IsLocalization M (Ambient S) := MvPolynomial.isLocalization R⁰ S
  let aRD : Algebra R D := (parameterEval H g h).toAlgebra
  let : Module R D := aRD.toModule
  let : SMul R D := aRD.toSMul
  have hk : RingHom.ker q = (RingHom.ker f).map (algebraMap (Ambient R) (Ambient S)) := by
    rw [Ideal.mk_ker, ← beforeIdeal_eq_ker H g h, localized_beforeIdeal]
  let q' : { p : Ambient R →+* B // RingHom.ker f ≤ RingHom.ker p } :=
    ⟨q.comp (algebraMap (Ambient R) (Ambient S)), by
      rw [← RingHom.comap_ker, hk]
      exact Ideal.le_comap_map⟩
  let φ : D →+* B := f.liftOfSurjective (beforeEval_surjective H g h) q'
  have hφ : φ.comp f = q.comp (algebraMap (Ambient R) (Ambient S)) :=
    f.liftOfSurjective_comp (beforeEval_surjective H g h) q'
  let aDB : Algebra D B := φ.toAlgebra
  let : SMul D B := aDB.toSMul
  let aRB : Algebra R B := ((algebraMap S B).comp (algebraMap R S)).toAlgebra
  let : Module R B := aRB.toModule
  let : SMul R B := aRB.toSMul
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R D B := IsScalarTower.of_algebraMap_eq fun a => by
    change q (MvPolynomial.C (algebraMap R S a)) = φ (parameterEval H g h a)
    have ht := RingHom.congr_fun hφ (MvPolynomial.C a)
    change φ (beforeEval H g h (MvPolynomial.C a)) =
      q (MvPolynomial.map (algebraMap R S) (MvPolynomial.C a)) at ht
    simpa only [beforeEval, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C] using ht.symm
  have hloc : IsLocalization (M.map f) B :=
    IsLocalization.of_surjective M (Ambient S) f (beforeEval_surjective H g h) q
      Ideal.Quotient.mk_surjective hφ.symm hk.le
  have hparams : (M.map f) = Algebra.algebraMapSubmonoid D R⁰ := by
    change (R⁰.map (MvPolynomial.C (σ := Fin 4)).toMonoidHom).map f.toMonoidHom =
      R⁰.map (parameterEval H g h).toMonoidHom
    rw [Submonoid.map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    exact MvPolynomial.eval₂Hom_C _ _ _
  let : IsLocalization (Algebra.algebraMapSubmonoid D R⁰) B := hparams ▸ hloc
  exact (IsFractionRing.finrank_right_eq R S B).trans
    (IsLocalizedModule.finrank_eq R⁰ (IsScalarTower.toAlgHom R D B).toLinearMap le_rfl)
end
end K1_14_2_2_7_3_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace K1_14_2_2_7_2_2_1
open K1_14 K1_14_2 K1_14_2_2_7_2 K1_14_2_2_7_2_2 MvPolynomial
open scoped Polynomial RatFunc TensorProduct
noncomputable section
attribute [local instance] Polynomial.algebra
private abbrev E := RatFunc SeedField
private abbrev D := MvPolynomial (Fin 2) E
private abbrev B := Polynomial SeedField
private def cutSeed₀ : E := RatFunc.C (generic 1) - RatFunc.C (generic 0) * RatFunc.X
private def seedSubstitution : Seeds →+* Polynomial Seeds :=
  eval₂Hom (Polynomial.C.comp C)
    ![Polynomial.C (MvPolynomial.X 1) - Polynomial.C (MvPolynomial.X 0) * Polynomial.X, Polynomial.X]
private def specializeSlope : Polynomial Seeds →+* Seeds :=
  Polynomial.eval₂RingHom (eval₂Hom C ![0, MvPolynomial.X 0]) (MvPolynomial.X 1)
private theorem seedSubstitution_injective : Function.Injective seedSubstitution := by
  have h : specializeSlope.comp seedSubstitution = RingHom.id Seeds := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [seedSubstitution, specializeSlope]
    · intro i
      fin_cases i <;> simp [seedSubstitution, specializeSlope]
  exact Function.LeftInverse.injective (RingHom.congr_fun h)
private def seedsToField : Seeds →+* E :=
  (algebraMap B E).comp ((Polynomial.mapRingHom (algebraMap Seeds SeedField)).comp seedSubstitution)
private def seedCoefficients : SeedField →+* E :=
  IsFractionRing.lift (g := seedsToField) ((IsFractionRing.injective B E).comp
    ((Polynomial.map_injective _ (IsFractionRing.injective Seeds SeedField)).comp
      seedSubstitution_injective))
private theorem seedCoefficients_ground (c : FX) :
    seedCoefficients (algebraMap FX SeedField c) = RatFunc.C (algebraMap FX SeedField c) := by
  change seedCoefficients (algebraMap Seeds SeedField (C c)) = _
  rw [seedCoefficients, IsFractionRing.lift_algebraMap]
  simp [seedsToField, seedSubstitution, RatFunc.algebraMap_C]
  rfl
private theorem seedCoefficients_zero : seedCoefficients (generic 0) = cutSeed₀ := by
  rw [generic, seedCoefficients, IsFractionRing.lift_algebraMap]
  simp [seedsToField, seedSubstitution, cutSeed₀, generic, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X]
private theorem seedCoefficients_one : seedCoefficients (generic 1) = RatFunc.X := by
  rw [generic, seedCoefficients, IsFractionRing.lift_algebraMap]
  simp [seedsToField, seedSubstitution, RatFunc.algebraMap_X]
private def fullEval : Ambient →+* D := (MvPolynomial.map seedCoefficients).comp mapGenericSeed
private def cutEval : SeedAmbient →+* D :=
  eval₂Hom (C.comp RatFunc.C) ![C cutSeed₀, C RatFunc.X, MvPolynomial.X 0, MvPolynomial.X 1]
private theorem cutEval_base : cutEval.comp seedBase = fullEval := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [cutEval, seedBase, fullEval, mapGenericSeed, seedCoefficients_ground]
  · intro i
    fin_cases i <;> simp [cutEval, seedBase, fullEval, mapGenericSeed,
      seedCoefficients_zero, seedCoefficients_one]
private theorem cutEval_line : cutEval (seedLine 0 1) = 0 := by
  simp [cutEval, seedLine, cutSeed₀, map_sub, map_mul, map_add, sub_add_cancel]
private abbrev fibreIdeal (I : Ideal Ambient) : Ideal D := I.map fullEval
private abbrev CutRing (I : Ideal Ambient) := D ⧸ fibreIdeal I
private abbrev F (I : Ideal Ambient) := GenericFibre SeedField (JetSeedSection I) (seedCoord I 1)
private local instance parameterAlgebra (I : Ideal Ambient) : Algebra B (JetSeedSection I) :=
  (Polynomial.aeval (seedCoord I 1) : B →ₐ[SeedField] JetSeedSection I).toRingHom.toAlgebra
private local instance targetParameterAlgebra (I : Ideal Ambient) : Algebra B (CutRing I) :=
  Algebra.compHom (CutRing I) (algebraMap B E)
private local instance targetParameterTower (I : Ideal Ambient) :
    @IsScalarTower B E (CutRing I) (show Algebra B E from inferInstance).toSMul
      (show Algebra E (CutRing I) from inferInstance).toSMul (targetParameterAlgebra I).toSMul :=
  IsScalarTower.of_algebraMap_eq' rfl
private def toCutRing (I : Ideal Ambient) : JetSeedSection I →+* CutRing I :=
  Ideal.Quotient.lift (seedIdeal I) ((Ideal.Quotient.mk (fibreIdeal I)).comp cutEval) <| by
    change seedIdeal I ≤ RingHom.ker _
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change Ideal.Quotient.mk (fibreIdeal I) ((cutEval.comp seedBase) a) = 0
      rw [RingHom.congr_fun cutEval_base a]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)
    · rw [Ideal.span_singleton_le_iff_mem]
      change Ideal.Quotient.mk (fibreIdeal I) (cutEval (seedLine 0 1)) = 0
      rw [cutEval_line, map_zero]
private theorem toCutRing_mk (I : Ideal Ambient) (p : SeedAmbient) :
    toCutRing I (Ideal.Quotient.mk (seedIdeal I) p) = Ideal.Quotient.mk (fibreIdeal I) (cutEval p) :=
  rfl
private def toCutRingAlg (I : Ideal Ambient) : JetSeedSection I →ₐ[B] CutRing I :=
  { toCutRing I with
    commutes' := by
      have h : (toCutRing I).comp (algebraMap B (JetSeedSection I)) = algebraMap B (CutRing I) := by
        apply Polynomial.ringHom_ext
        · intro c
          change toCutRing I (Polynomial.aeval (seedCoord I 1) (Polynomial.C c)) =
            algebraMap E (CutRing I) (algebraMap B E (Polynomial.C c))
          rw [Polynomial.aeval_C, RatFunc.algebraMap_C]
          change toCutRing I (Ideal.Quotient.mk (seedIdeal I) (C c)) = _
          rw [toCutRing_mk]
          simp only [cutEval, eval₂Hom_C, RingHom.comp_apply]
          rfl
        · change toCutRing I (Polynomial.aeval (seedCoord I 1) Polynomial.X) =
            algebraMap E (CutRing I) (algebraMap B E Polynomial.X)
          rw [Polynomial.aeval_X, RatFunc.algebraMap_X, seedCoord, toCutRing_mk]
          simp only [cutEval, eval₂Hom_X']
          rfl
      exact RingHom.congr_fun h }
private def toCut (I : Ideal Ambient) : F I →ₐ[E] CutRing I :=
  AlgHom.liftEquiv B E (JetSeedSection I) (CutRing I) (toCutRingAlg I)
private def inc (I : Ideal Ambient) : SeedAmbient →+* F I :=
  (Algebra.TensorProduct.includeRight (R := B) (A := E) (B := JetSeedSection I)).toRingHom.comp
    (Ideal.Quotient.mk (seedIdeal I))
private theorem inc_eq_zero (I : Ideal Ambient) (p : SeedAmbient) (hp : p ∈ seedIdeal I) :
    inc I p = 0 := by
  let right := Algebra.TensorProduct.includeRight (R := B) (A := E) (B := JetSeedSection I)
  change right (Ideal.Quotient.mk (seedIdeal I) p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
private theorem inc_C (I : Ideal Ambient) (c : SeedField) :
    inc I (C c) = algebraMap E (F I) (RatFunc.C c) := by
  let right := Algebra.TensorProduct.includeRight (R := B) (A := E) (B := JetSeedSection I)
  have h := right.commutes (Polynomial.C c)
  change right (Polynomial.aeval (seedCoord I 1) (Polynomial.C c)) =
    algebraMap E (F I) (algebraMap B E (Polynomial.C c)) at h
  rw [Polynomial.aeval_C, RatFunc.algebraMap_C] at h
  exact h
private theorem inc_X₁ (I : Ideal Ambient) : inc I (MvPolynomial.X 1) = algebraMap E (F I) RatFunc.X := by
  let right := Algebra.TensorProduct.includeRight (R := B) (A := E) (B := JetSeedSection I)
  have h := right.commutes (Polynomial.X : B)
  change right (Polynomial.aeval (seedCoord I 1) Polynomial.X) =
    algebraMap E (F I) (algebraMap B E Polynomial.X) at h
  rw [Polynomial.aeval_X, RatFunc.algebraMap_X] at h
  exact h
private theorem inc_X₀ (I : Ideal Ambient) : inc I (MvPolynomial.X 0) = algebraMap E (F I) cutSeed₀ := by
  have hle : Ideal.span {seedLine 0 1} ≤ seedIdeal I := le_sup_right
  have h := inc_eq_zero I (seedLine 0 1) (hle (Ideal.subset_span (by simp)))
  simp only [seedLine, map_sub, map_add, map_mul, inc_C, inc_X₁] at h
  rw [cutSeed₀, map_sub, map_mul, eq_sub_iff_add_eq, ← sub_eq_zero]
  exact h
private def jetEval (I : Ideal Ambient) : D →ₐ[E] F I :=
  aeval ![inc I (MvPolynomial.X 2), inc I (MvPolynomial.X 3)]
private theorem jetEval_cutEval (I : Ideal Ambient) :
    (jetEval I).toRingHom.comp cutEval = inc I := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [cutEval, jetEval, inc_C]
  · intro i
    fin_cases i <;>
      simp [cutEval, jetEval, inc_X₀, inc_X₁]
private def fromCut (I : Ideal Ambient) : CutRing I →ₐ[E] F I :=
  { Ideal.Quotient.lift (fibreIdeal I) (jetEval I).toRingHom (by
      change I.map fullEval ≤ RingHom.ker (jetEval I).toRingHom
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      change jetEval I (fullEval p) = 0
      rw [← RingHom.congr_fun cutEval_base p]
      change ((jetEval I).toRingHom.comp cutEval) (seedBase p) = 0
      rw [jetEval_cutEval]
      have hle : I.map seedBase ≤ seedIdeal I := le_sup_left
      exact inc_eq_zero I (seedBase p) (hle (Ideal.mem_map_of_mem _ hp))) with
    commutes' := fun c => (jetEval I).commutes c }
private theorem fromCut_mk (I : Ideal Ambient) (p : D) :
    fromCut I (Ideal.Quotient.mk (fibreIdeal I) p) = jetEval I p :=
  rfl
private theorem toCut_inc (I : Ideal Ambient) (p : SeedAmbient) :
    toCut I (inc I p) = Ideal.Quotient.mk (fibreIdeal I) (cutEval p) := by
  have h := AlgHom.congr_fun
    ((AlgHom.liftEquiv B E (JetSeedSection I) (CutRing I)).left_inv (toCutRingAlg I))
    (Ideal.Quotient.mk (seedIdeal I) p)
  exact h.trans (toCutRing_mk I p)
private def fibreEquiv (I : Ideal Ambient) : F I ≃ₐ[E] CutRing I :=
  AlgEquiv.ofAlgHom (toCut I) (fromCut I) (by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;>
      simp [fromCut_mk, jetEval, toCut_inc, cutEval]) (by
    apply AlgHom.coe_ringHom_injective
    apply Algebra.TensorProduct.ringHom_ext (R := B) (A := E) (B := JetSeedSection I)
    · apply RingHom.ext
      intro c
      exact ((fromCut I).comp (toCut I)).commutes c
    · apply Ideal.Quotient.ringHom_ext
      apply RingHom.ext
      intro p
      change fromCut I (toCut I (inc I p)) = inc I p
      rw [toCut_inc, fromCut_mk]
      exact RingHom.congr_fun (jetEval_cutEval I) p)
theorem proof : K1_14_2_2_7_2_2.c1 := by
  intro I
  let : Algebra SeedField E := seedCoefficients.toAlgebra
  let e : E ⊗[SeedField] OverSeeds I ≃ₐ[E] CutRing I :=
    (K1_14_3R_3_2.quotientBaseChange (E := E) (I.map mapGenericSeed)).trans
      (Ideal.quotientEquivAlgOfEq E (Ideal.map_map _ _))
  exact (fibreEquiv I).toLinearEquiv.finrank_eq.trans
    (e.toLinearEquiv.finrank_eq.symm.trans Module.finrank_baseChange)
end
end K1_14_2_2_7_2_2_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000
namespace K1_14_3R_2
noncomputable section
open K1 K1_14 K1_14_3 K1_14_3_2 Polynomial
structure FullGcd (P Q : Jet) (s t : Shape) where
  fixed : JetPlane
  ordinary : Equation
  left : Jet
  right : Jet
  fixed_ne : fixed ≠ 0
  ordinary_ne : ordinary ≠ 0
  left_factor : P = fixedEmbedding fixed * (C ordinary * left)
  right_factor : Q = fixedEmbedding fixed * (C ordinary * right)
  proper : ProperPair left right
  ordinary_y : ordinary.natDegree ≤ s.B
  ordinary_seed : ordinarySeedDegree ordinary ≤ s.U
  left_caps : RowCaps left s
  right_caps : RowCaps right t
end
end K1_14_3R_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
namespace K1_14_2_2_7_2_3
noncomputable section
open K1_14_2_2_7_2 (CurvePoles PoleOrder coordinateDegree lineDegree)
open K1_14_3R_3_1 (SeparatingParameter jetPencilDegree pencilAlgebra)
open K1_14_3R_3_1_3 (c1 c2 c3 c4 c5 GaussAt PlaceResidue exists_gauss_extension placeWeight
  weightedPoleDegree pencilAlgebra_polynomial)
open K1_13_6_3_5_3 (CurvePlace poleOrder)
open scoped BigOperators Polynomial RatFunc WithZero
attribute [local instance] Polynomial.algebra
section Degrees
variable {k F : Type} [Field k] [Field F] [Algebra k F]
private theorem degree_compare (a : F) :
    K1_14_2_2_7_2.functionDegree k F a = K1_14_3R_3_1.functionDegree k a := by
  classical
  by_cases h : IsAlgebraic k a <;>
    simp [K1_14_2_2_7_2.functionDegree, K1_14_3R_3_1.functionDegree, Transcendental, h]
private theorem separating_of_small (ell : ℕ) [CharP k ell] (a : F)
    (hpos : 0 < K1_14_2_2_7_2.functionDegree k F a)
    (hsmall : K1_14_2_2_7_2.functionDegree k F a < ell) :
    SeparatingParameter k a := by
  classical
  have htr : Transcendental k a := by
    by_contra h
    simp [K1_14_2_2_7_2.functionDegree, h] at hpos
  rw [K1_14_2_2_7_2.functionDegree, ite_eq_left htr] at hpos hsmall
  let E := IntermediateField.adjoin k ({a} : Set F)
  let : FiniteDimensional E F := Module.finite_of_finrank_pos hpos
  let : CharP E ell := charP_of_injective_ringHom (algebraMap k E).injective ell
  have hell : 0 < ell := hpos.trans hsmall
  let : Fact ell.Prime := ⟨(CharP.char_is_prime_or_zero E ell).resolve_right hell.ne'⟩
  refine ⟨htr, inferInstanceAs (FiniteDimensional E F), ?_⟩
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow E F ell
  apply (isSeparable_iff_finInsepDegree_eq_one E F).mpr
  cases n with
  | zero => simpa using hn
  | succ n =>
    have hle : ell ≤ ell ^ (n + 1) := by
      rw [pow_succ']
      exact Nat.le_mul_of_pos_right _ (pow_pos hell _)
    have hdvd : ell ^ (n + 1) ∣ Module.finrank E F := by
      rw [← hn, ← Field.finSepDegree_mul_finInsepDegree E F]
      exact dvd_mul_left _ _
    exact (not_lt_of_ge (hle.trans (Nat.le_of_dvd hpos hdvd)) hsmall).elim
private theorem trunc_mono : Monotone (fun a : ℤᵐ⁰ => (WithZero.log a).toNat) := by
  intro a b hab
  by_cases ha : a = 0
  · simp [ha]
  · exact Int.toNat_le_toNat ((WithZero.log_le_log ha
      (ne_of_gt ((WithZero.pos_iff_ne_zero.mpr ha).trans_le hab))).mpr hab)
private theorem pole_add (p : CurvePlace k F) (a b : F) :
    poleOrder p.value (a + b) ≤ max (poleOrder p.value a) (poleOrder p.value b) := by
  unfold poleOrder
  exact (trunc_mono (p.value.map_add a b)).trans trunc_mono.map_max.le
private theorem pole_mul (p : CurvePlace k F) (a b : F) :
    poleOrder p.value (a * b) ≤ poleOrder p.value a + poleOrder p.value b := by
  unfold poleOrder
  obtain rfl | ha := eq_or_ne a 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  rw [map_mul, WithZero.log_mul (by simpa using ha) (by simpa using hb)]
  omega
private theorem pole_scalar (p : CurvePlace k F) (c : k) :
    poleOrder p.value (algebraMap k F c) = 0 := by
  obtain rfl | hc := eq_or_ne c 0
  · simp [poleOrder]
  · simp [poleOrder, p.on_constants c hc]
private theorem pole_of_le_one (p : CurvePlace k F) {a : F} (ha : p.value a ≤ 1) :
    poleOrder p.value a = 0 :=
  Nat.eq_zero_of_le_zero (by simpa [poleOrder] using trunc_mono ha)
private theorem poles_and_degree (h1 : c1) (h2 : c2) (t : F)
    (ht : SeparatingParameter k t) (a : F) :
    (fun p : CurvePlace k F => poleOrder p.value a).HasFiniteSupport ∧
      (∀ p : CurvePlace k F, poleOrder p.value a ≠ 0 → FiniteDimensional k (PlaceResidue p)) ∧
      weightedPoleDegree (k := k) a = K1_14_3R_3_1.functionDegree k a := by
  by_cases ha : IsAlgebraic k a
  · have hp (p : CurvePlace k F) : poleOrder p.value a = 0 := by
      let : p.value.IsTrivialOn k := ⟨p.on_constants⟩
      obtain rfl | hne := eq_or_ne a 0
      · simp [poleOrder]
      · have hv : p.value a = 1 := by
          by_contra h
          exact (Valuation.transcendental_of_ne_one k a hne h) ha
        simp [poleOrder, hv]
    refine ⟨?_, fun p h => (h (hp p)).elim, ?_⟩
    · simp [Function.HasFiniteSupport, Function.support, hp]
    · simp [weightedPoleDegree, K1_14_3R_3_1.functionDegree, ha, hp]
  · obtain ⟨hfinite, hchart⟩ := h1 k F t a ht ha
    exact h2 k F a ha hfinite hchart
private theorem residue_finite (h1 : c1) (h2 : c2) (t : F)
    (ht : SeparatingParameter k t) (p : CurvePlace k F) :
    FiniteDimensional k (PlaceResidue p) := by
  obtain ⟨a, ha⟩ := p.normalized (WithZero.exp 1)
  exact (poles_and_degree h1 h2 t ht a).2.1 p (by simp [poleOrder, ha])
end Degrees
section Pencil
variable {k F : Type} [Field k] [Field F] [Algebra k F]
private theorem pencilAlgebra_eq :
    pencilAlgebra k (F := F) = (inferInstance : Algebra (RatFunc k) (RatFunc F)) := by
  apply Algebra.algebra_ext
  intro f
  have hpoly (P : k[X]) :
      @algebraMap (RatFunc k) (RatFunc F) _ _ (pencilAlgebra k (F := F))
        (algebraMap k[X] (RatFunc k) P) =
      algebraMap (RatFunc k) (RatFunc F) (algebraMap k[X] (RatFunc k) P) := by
    rw [pencilAlgebra_polynomial, ← IsScalarTower.algebraMap_apply k[X] (RatFunc k)
      (RatFunc F), IsScalarTower.algebraMap_apply k[X] F[X] (RatFunc F)]
    rfl
  induction f using RatFunc.induction_on with
  | _ P Q hQ =>
    change @algebraMap (RatFunc k) (RatFunc F) _ _ (pencilAlgebra k (F := F)) _ =
      algebraMap (RatFunc k) (RatFunc F) _
    rw [map_div₀, map_div₀, hpoly, hpoly]
private theorem line_compare {A : Type} [CommRing A] [IsDomain A] [Algebra k A] (y v : A) :
    lineDegree k A y v =
      jetPencilDegree k (algebraMap A (FractionRing A) y) (algebraMap A (FractionRing A) v) := by
  unfold lineDegree jetPencilDegree
  rw [pencilAlgebra_eq]
  exact degree_compare _
local instance : Algebra (RatFunc k) (RatFunc F) := pencilAlgebra k (F := F)
private theorem gauss_constants {p : CurvePlace k F} {q : CurvePlace (RatFunc k) (RatFunc F)}
    (h : GaussAt p q) (a : F) : q.value (RatFunc.C a) = p.value a := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · simpa [Polynomial.support_C ha] using h (Polynomial.C a)
private theorem place_ext {p q : CurvePlace k F} (h : p.value = q.value) : p = q := by
  cases p
  cases q
  cases h
  rfl
private theorem gauss_unique {p : CurvePlace k F} {q r : CurvePlace (RatFunc k) (RatFunc F)}
    (hq : GaussAt p q) (hr : GaussAt p r) : q = r := by
  apply place_ext
  apply Valuation.ext
  intro a
  induction a using RatFunc.induction_on with
  | _ P Q hQ => rw [q.value.map_div, r.value.map_div, hq P, hq Q, hr P, hr Q]
private def pencil (y v : F) : RatFunc F := RatFunc.C y + RatFunc.X * RatFunc.C v
private theorem gauss_pencil {p : CurvePlace k F} {q : CurvePlace (RatFunc k) (RatFunc F)}
    (h : GaussAt p q) (y v : F) :
    poleOrder q.value (pencil y v) = max (poleOrder p.value y) (poleOrder p.value v) := by
  let P : F[X] := Polynomial.C y + Polynomial.X * Polynomial.C v
  have hP : algebraMap F[X] (RatFunc F) P = pencil y v := by
    simp only [P, pencil, map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  have hc0 : P.coeff 0 = y := by simp [P]
  have hc1 : P.coeff 1 = v := by simp [P]
  have hrest (i : ℕ) (hi : 2 ≤ i) : P.coeff i = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    simp [P, add_comm]
  have hmax : P.support.sup (fun i => p.value (P.coeff i)) = max (p.value y) (p.value v) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i hi
      by_cases h0 : i = 0
      · simp [h0, hc0]
      by_cases h1 : i = 1
      · simp [h1, hc1]
      · simp [hrest i (by omega)]
    · apply max_le
      · by_cases hy : y = 0
        · simp [hy]
        · exact hc0 ▸ (Finset.le_sup (f := fun i => p.value (P.coeff i))
            (Polynomial.mem_support_iff.mpr (hc0.symm ▸ hy)))
      · by_cases hv : v = 0
        · simp [hv]
        · exact hc1 ▸ (Finset.le_sup (f := fun i => p.value (P.coeff i))
            (Polynomial.mem_support_iff.mpr (hc1.symm ▸ hv)))
  unfold poleOrder
  rw [← hP, h P, hmax, trunc_mono.map_max]
private theorem pencil_pole_degree (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    (t : F) (ht : SeparatingParameter k t) (y v : F) :
    (∑ᶠ p : CurvePlace k F, placeWeight p * max (poleOrder p.value y) (poleOrder p.value v)) =
      jetPencilDegree k y v := by
  classical
  let lift (p : CurvePlace k F) := (exists_gauss_extension p).choose
  have hlift (p : CurvePlace k F) : GaussAt p (lift p) := (exists_gauss_extension p).choose_spec
  have hinj : Function.Injective lift := by
    intro p r he
    apply place_ext
    apply Valuation.ext
    intro a
    rw [← gauss_constants (hlift p), ← gauss_constants (hlift r), he]
  let g (q : CurvePlace (RatFunc k) (RatFunc F)) := placeWeight q * poleOrder q.value (pencil y v)
  have hoff (q : CurvePlace (RatFunc k) (RatFunc F)) (hq : q ∉ Set.range lift) : g q = 0 := by
    rcases h5 k F (residue_finite h1 h2 t ht) q with htriv | ⟨p, hp⟩
    · have hX : q.value (RatFunc.X : RatFunc F) = 1 := by
        have halg : algebraMap (RatFunc k) (RatFunc F) RatFunc.X = RatFunc.X := by
          simpa only [Polynomial.map_X, RatFunc.algebraMap_X] using
            (pencilAlgebra_polynomial (k := k) (F := F) Polynomial.X)
        rw [← halg]
        exact q.on_constants _ RatFunc.X_ne_zero
      have hle : q.value (pencil y v) ≤ 1 := by
        unfold pencil
        apply (q.value.map_add _ _).trans
        rw [map_mul, hX, one_mul]
        exact max_le (htriv y) (htriv v)
      simp [g, pole_of_le_one q hle]
    · exact (hq ⟨p, gauss_unique (hlift p) hp⟩).elim
  have hsupp : Function.support g ⊆ Set.range lift := by
    intro q hq
    by_contra h
    exact hq (hoff q h)
  have hsum : (∑ᶠ q, g q) = ∑ᶠ q ∈ Set.range lift, g q := by
    rw [← finsum_mem_support g]
    apply finsum_mem_inter_support_eq'
    intro q hq
    simp [hq, hsupp hq]
  calc
    _ = ∑ᶠ p, g (lift p) := by
      apply finsum_congr
      intro p
      simp only [g, gauss_pencil (hlift p), h4 k F p (residue_finite h1 h2 t ht p) _ (hlift p)]
    _ = ∑ᶠ q ∈ Set.range lift, g q := (finsum_mem_range hinj).symm
    _ = weightedPoleDegree (k := RatFunc k) (pencil y v) := hsum.symm
    _ = jetPencilDegree k y v := (poles_and_degree h1 h2 _ (h3 k F t ht) _).2.2
end Pencil
theorem of_place_laws (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) :
    K1_14_2_2_7_2.c3 := by
  classical
  intro ell k A _ _ _ _ _ hfinite _ x y v hx hsmall
  let F := FractionRing A
  let f : A →+* F := algebraMap A F
  let t := f x
  have ht : SeparatingParameter k t := separating_of_small ell t hx hsmall
  have hdegree (a : A) := poles_and_degree h1 h2 t ht (f a)
  let order (p : CurvePlace k F) (a : A) := poleOrder p.value (f a)
  obtain ⟨generators, hgen⟩ := hfinite.out
  let S := generators.biUnion (fun a => (hdegree a).1.toFinset)
  have hz (p : CurvePlace k F) (hp : p ∉ S) (a : A) : order p a = 0 := by
    have ha : a ∈ Algebra.adjoin k (↑generators : Set A) := by
      rw [hgen]
      trivial
    induction ha using Algebra.adjoin_induction with
    | mem b hb =>
      have h : p ∉ (hdegree b).1.toFinset := fun h =>
        hp (Finset.mem_biUnion.mpr ⟨b, hb, h⟩)
      simpa [order, Function.mem_support] using h
    | algebraMap c =>
      simpa [order, f, IsScalarTower.algebraMap_apply k A F] using pole_scalar (F := F) p c
    | add a b _ _ ha hb =>
      have hab : order p (a + b) ≤ max (order p a) (order p b) := by
        simpa only [order, map_add] using pole_add p (f a) (f b)
      exact Nat.eq_zero_of_le_zero (by simpa [ha, hb] using hab)
    | mul a b _ _ ha hb =>
      have hab : order p (a * b) ≤ order p a + order p b := by
        simpa only [order, map_mul] using pole_mul p (f a) (f b)
      exact Nat.eq_zero_of_le_zero (by simpa [ha, hb] using hab)
  let e := S.equivFin.symm
  have hsum (g : CurvePlace k F → ℕ) (hg : ∀ p ∉ S, g p = 0) :
      (∑ i, g (e i)) = ∑ᶠ p, g p := by
    rw [e.sum_comp (fun p : S => g p), Finset.sum_coe_sort]
    exact (finsum_eq_finsetSum_of_support_subset _ (fun p hp => by
      by_contra h
      exact hp (hg p h))).symm
  let orders (p : CurvePlace k F) : PoleOrder k A :=
    { order := order p
      constant := fun c => by
        simpa [order, f, IsScalarTower.algebraMap_apply k A F] using pole_scalar (F := F) p c
      add_le := fun a b => by simpa only [order, map_add] using pole_add p (f a) (f b)
      mul_le := fun a b => by simpa only [order, map_mul] using pole_mul p (f a) (f b) }
  refine ⟨{
    count := S.card
    place := fun i => orders (e i)
    residueDegree := fun i => placeWeight (e i : CurvePlace k F)
    degree_eq := fun a => ?_
    line_eq := ?_ }⟩
  · change coordinateDegree k A a = ∑ i, order (e i) a * placeWeight (e i : CurvePlace k F)
    calc
      _ = weightedPoleDegree (k := k) (f a) := by
        exact (degree_compare (f a)).trans (hdegree a).2.2.symm
      _ = ∑ i, placeWeight (e i : CurvePlace k F) * order (e i) a :=
        (hsum (fun p => placeWeight p * order p a) (fun p hp => by
          rw [hz p hp a, Nat.mul_zero])).symm
      _ = _ := Finset.sum_congr rfl (fun _ _ => Nat.mul_comm _ _)
  · change lineDegree k A y v =
      ∑ i, max (order (e i) y) (order (e i) v) * placeWeight (e i : CurvePlace k F)
    calc
      _ = ∑ᶠ p : CurvePlace k F, placeWeight p * max (order p y) (order p v) :=
        (line_compare y v).trans (pencil_pole_degree h1 h2 h3 h4 h5 t ht (f y) (f v)).symm
      _ = ∑ i, placeWeight (e i : CurvePlace k F) * max (order (e i) y) (order (e i) v) :=
        (hsum (fun p => placeWeight p * max (order p y) (order p v))
          (fun p hp => by rw [hz p hp y, hz p hp v, max_self, Nat.mul_zero])).symm
      _ = _ := Finset.sum_congr rfl (fun _ _ => Nat.mul_comm _ _)
end
end K1_14_2_2_7_2_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3R_3_1_3_4
noncomputable section
open K1_13_6_3_5_3 (CurvePlace)
open K1_14_3R_3_1 (pencilAlgebra)
open K1_14_3R_3_1_3
open Polynomial
open scoped Polynomial WithZero
attribute [local instance] Polynomial.algebra
open scoped RatFunc in
private theorem finrank_eq_of_rational_model {K E G : Type}
    [Field K] [Field E] [Field G] [Algebra K E] [Algebra (RatFunc K) G]
    [FiniteDimensional K E] (f : RatFunc E →+* G) (hf : Function.Surjective f)
    (h : ∀ P : K[X], f (algebraMap E[X] (RatFunc E) (P.map (algebraMap K E))) =
      algebraMap (RatFunc K) G (algebraMap K[X] (RatFunc K) P)) :
    Module.finrank (RatFunc K) G = Module.finrank K E := by
  have hP (P : K[X]) :
      f (algebraMap (RatFunc K) (RatFunc E) (algebraMap K[X] (RatFunc K) P)) =
        algebraMap (RatFunc K) G (algebraMap K[X] (RatFunc K) P) := by
    rw [← IsScalarTower.algebraMap_apply K[X] (RatFunc K) (RatFunc E),
      IsScalarTower.algebraMap_apply K[X] E[X] (RatFunc E)]
    exact h P
  have hcomm (a : RatFunc K) :
      f (algebraMap (RatFunc K) (RatFunc E) a) = algebraMap (RatFunc K) G a := by
    induction a using RatFunc.induction_on with
    | _ P Q _ => simp only [map_div₀, hP]
  let e : RatFunc E →ₐ[RatFunc K] G := { f with commutes' := hcomm }
  let E' := AlgEquiv.ofBijective e ⟨f.injective, hf⟩
  exact E'.toLinearEquiv.finrank_eq.symm.trans (RatFunc.finrank_ratFunc_ratFunc K E)
variable {k F : Type} [Field k] [Field F] [Algebra k F]
variable {p : CurvePlace k F}
local notation "Oₚ" => p.value.valuationSubring
local notation "ι" => p.value.valuationSubring.toSubring.subtype
local notation "j" => algebraMap F[X] (RatFunc F)
section ResidueMap
variable [Algebra (RatFunc k) (RatFunc F)]
variable {q : CurvePlace (RatFunc k) (RatFunc F)}
local notation "O_q" => q.value.valuationSubring
private theorem gauss_C (h : GaussAt p q) (a : F) :
    q.value (RatFunc.C a) = p.value a := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · simpa [Polynomial.support_C ha] using h (Polynomial.C a)
private theorem integral_iff (h : GaussAt p q) (P : F[X]) :
    q.value (j P) ≤ 1 ↔ ∀ n, p.value (P.coeff n) ≤ 1 := by
  rw [h P, Finset.sup_le_iff]
  refine ⟨fun hP n => ?_, fun hP n _ => hP n⟩
  by_cases hn : P.coeff n = 0
  · simp [hn]
  · exact hP n (Polynomial.mem_support_iff.mpr hn)
private theorem small_iff (h : GaussAt p q) (P : F[X]) :
    q.value (j P) < 1 ↔ ∀ n, p.value (P.coeff n) < 1 := by
  rw [h P, Finset.sup_lt_iff (show (⊥ : ℤᵐ⁰) < 1 from zero_lt_one)]
  refine ⟨fun hP n => ?_, fun hP n _ => hP n⟩
  by_cases hn : P.coeff n = 0
  · simp [hn]
  · exact hP n (Polynomial.mem_support_iff.mpr hn)
private def integralPolynomial (h : GaussAt p q) : Oₚ[X] →+* O_q :=
  ((j).comp (Polynomial.mapRingHom ι)).codRestrict (O_q).toSubring
    (fun P => by
      change q.value (j (P.map ι)) ≤ 1
      apply (integral_iff h _).mpr
      intro n
      rw [Polynomial.coeff_map]
      exact (P.coeff n).property)
private theorem integralPolynomial_value (h : GaussAt p q) (P : Oₚ[X]) :
    (integralPolynomial h P : RatFunc F) = j (P.map ι) := rfl
private theorem residue_polynomial_eq_zero (h : GaussAt p q) (P : Oₚ[X]) :
    IsLocalRing.residue O_q (integralPolynomial h P) = 0 ↔
      P.map (IsLocalRing.residue Oₚ) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, q.value.mem_maximalIdeal_iff,
    integralPolynomial_value, small_iff h, Polynomial.ext_iff]
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff,
    p.value.mem_maximalIdeal_iff]
  rfl
private def residueConstant (h : GaussAt p q) : PlaceResidue p →+* PlaceResidue q :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal Oₚ)
    ((IsLocalRing.residue O_q).comp ((integralPolynomial h).comp Polynomial.C))
    (fun a ha => by
      change IsLocalRing.residue O_q (integralPolynomial h (Polynomial.C a)) = 0
      apply (residue_polynomial_eq_zero h _).mpr
      rw [Polynomial.map_C, (IsLocalRing.residue_eq_zero_iff a).mpr ha, Polynomial.C_0])
private theorem residueConstant_apply (h : GaussAt p q) (a : Oₚ) :
    residueConstant h (IsLocalRing.residue Oₚ a) =
      IsLocalRing.residue O_q (integralPolynomial h (Polynomial.C a)) := rfl
private def residuePolynomial (h : GaussAt p q) : (PlaceResidue p)[X] →+* PlaceResidue q :=
  Polynomial.eval₂RingHom (residueConstant h)
    (IsLocalRing.residue O_q (integralPolynomial h Polynomial.X))
private theorem residuePolynomial_apply (h : GaussAt p q) (P : Oₚ[X]) :
    residuePolynomial h (P.map (IsLocalRing.residue Oₚ)) =
      IsLocalRing.residue O_q (integralPolynomial h P) := by
  have heq : (residuePolynomial h).comp (Polynomial.mapRingHom (IsLocalRing.residue Oₚ)) =
      (IsLocalRing.residue O_q).comp (integralPolynomial h) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        residuePolynomial, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact residueConstant_apply h a
    · simp [residuePolynomial]
  exact RingHom.congr_fun heq P
private theorem residuePolynomial_injective (h : GaussAt p q) :
    Function.Injective (residuePolynomial h) := by
  apply (injective_iff_map_eq_zero (residuePolynomial h)).mpr
  intro P hP
  obtain ⟨P, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue Oₚ)
    IsLocalRing.residue_surjective P
  rw [residuePolynomial_apply] at hP
  exact (residue_polynomial_eq_zero h P).mp hP
private def residueRational (h : GaussAt p q) : RatFunc (PlaceResidue p) →+* PlaceResidue q :=
  IsFractionRing.lift (residuePolynomial_injective h)
private theorem residueRational_polynomial (h : GaussAt p q) (P : Oₚ[X]) :
    residueRational h
      (algebraMap (PlaceResidue p)[X] (RatFunc (PlaceResidue p))
        (P.map (IsLocalRing.residue Oₚ))) =
      IsLocalRing.residue O_q (integralPolynomial h P) :=
  (IsFractionRing.lift_algebraMap (residuePolynomial_injective h) _).trans
    (residuePolynomial_apply h P)
private theorem integralPolynomial_lift (h : GaussAt p q) {P : F[X]}
    (hP : q.value (j P) ≤ 1) :
    ∃ A : Oₚ[X], (integralPolynomial h A : RatFunc F) = j P := by
  have hrange : P ∈ (Polynomial.mapRingHom ι).range := by
    apply (Polynomial.mem_map_range _).mpr
    intro n
    exact ⟨⟨P.coeff n, (integral_iff h P).mp hP n⟩, rfl⟩
  obtain ⟨A, hA⟩ := hrange
  exact ⟨A, congrArg j hA⟩
private theorem residueRational_surjective (h : GaussAt p q) :
    Function.Surjective (residueRational h) := by
  intro z
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨P, Q, hQ, hz⟩ : ∃ P Q : F[X], Q ≠ 0 ∧ (z : RatFunc F) = j P / j Q := by
    induction (z : RatFunc F) using RatFunc.induction_on with
    | _ P Q hQ => exact ⟨P, Q, hQ, rfl⟩
  have hjQ : j Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ
  have hvQ : q.value (j Q) ≠ 0 := q.value.zero_iff.not.mpr hjQ
  obtain ⟨a, ha⟩ := p.normalized (q.value (j Q))
  let D : F[X] := Polynomial.C a⁻¹
  have hvD : q.value (j D) = (q.value (j Q))⁻¹ := by
    rw [show j D = RatFunc.C a⁻¹ from RatFunc.algebraMap_C _, gauss_C h, map_inv₀, ha]
  have hQ' : q.value (j (D * Q)) = 1 := by
    rw [map_mul, map_mul, hvD, inv_mul_cancel₀ hvQ]
  have hprod : (z : RatFunc F) * j (D * Q) = j (D * P) := by
    rw [map_mul, map_mul, mul_left_comm, (eq_div_iff hjQ).mp hz]
  have hP' : q.value (j (D * P)) ≤ 1 := by
    rw [← hprod, map_mul, hQ', mul_one]
    exact z.property
  obtain ⟨A, hA⟩ := integralPolynomial_lift h hP'
  obtain ⟨B, hB⟩ := integralPolynomial_lift h hQ'.le
  have hmul : z * integralPolynomial h B = integralPolynomial h A := by
    apply Subtype.ext
    change (z : RatFunc F) * (integralPolynomial h B : RatFunc F) = _
    rw [hA, hB, hprod]
  have hden : IsLocalRing.residue O_q (integralPolynomial h B) ≠ 0 := by
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff, q.value.mem_maximalIdeal_iff, hB, hQ']
    exact lt_irrefl 1
  refine ⟨algebraMap (PlaceResidue p)[X] (RatFunc (PlaceResidue p))
      (A.map (IsLocalRing.residue Oₚ)) /
    algebraMap (PlaceResidue p)[X] (RatFunc (PlaceResidue p))
      (B.map (IsLocalRing.residue Oₚ)), ?_⟩
  rw [map_div₀, residueRational_polynomial, residueRational_polynomial, div_eq_iff hden]
  exact (congrArg (IsLocalRing.residue O_q) hmul).symm.trans (map_mul _ _ _)
end ResidueMap
private theorem residueRational_base_polynomial (P : k[X]) :
    letI := pencilAlgebra k (F := F)
    ∀ (q : CurvePlace (RatFunc k) (RatFunc F)) (h : GaussAt p q),
      residueRational h (algebraMap (PlaceResidue p)[X] (RatFunc (PlaceResidue p))
        (P.map (algebraMap k (PlaceResidue p)))) =
        algebraMap (RatFunc k) (PlaceResidue q) (algebraMap k[X] (RatFunc k) P) := by
  let := pencilAlgebra k (F := F)
  intro q h
  have hred : P.map (algebraMap k (PlaceResidue p)) =
      (P.map (placeConstants p)).map (IsLocalRing.residue Oₚ) :=
    (Polynomial.map_map _ _ _).symm
  rw [hred, residueRational_polynomial]
  change IsLocalRing.residue q.value.valuationSubring
    (integralPolynomial h (P.map (placeConstants p))) =
    IsLocalRing.residue q.value.valuationSubring
      (placeConstants q (algebraMap k[X] (RatFunc k) P))
  congr 1
  apply Subtype.ext
  change j ((P.map (placeConstants p)).map ι) =
    algebraMap (RatFunc k) (RatFunc F) (algebraMap k[X] (RatFunc k) P)
  rw [Polynomial.map_map, pencilAlgebra_polynomial]
  rfl
theorem proof : K1_14_3R_3_1_3.c4 := by
  intro k F _ _ _ p hp
  let : FiniteDimensional k (PlaceResidue p) := hp
  let := pencilAlgebra k (F := F)
  change ∀ q : CurvePlace (RatFunc k) (RatFunc F), GaussAt p q →
    placeWeight q = placeWeight p
  intro q h
  exact finrank_eq_of_rational_model (residueRational h) (residueRational_surjective h)
    (fun P => residueRational_base_polynomial P q h)
end
end K1_14_3R_3_1_3_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 4000
set_option maxHeartbeats 2500000
namespace K1_14_3R_3_1_2_2
noncomputable section
open K1_14_3_2_7 K1_14_3R_3_1_2 Polynomial
open scoped TensorProduct nonZeroDivisors
variable {k G : Type} [Field k] [Field G]
end
end K1_14_3R_3_1_2_2
end
section
set_option autoImplicit false
namespace K1_14_3R_3_1_3_1
open IntermediateField
open K1_14_3R_3_1_3 (chartAlgebra)
open scoped Polynomial algebraAdjoinAdjoin
variable {k F : Type} [Field k] [Field F] [Algebra k F]
theorem finite_projection {t x : F} (ht : Transcendental k t)
    (hfin : Module.Finite (IntermediateField.adjoin k {t}) F)
    (hx : Transcendental k x) : Module.Finite (IntermediateField.adjoin k {x}) F := by
  let := hfin
  have ht' : IsAlgebraic (IntermediateField.adjoin k {x}) t :=
    isAlgebraic_adjoin_iff.mpr (.adjoin_singleton ht hx
      (isAlgebraic_adjoin_iff.mp (Algebra.IsAlgebraic.isAlgebraic x)))
  let Kxt := restrictScalars k (IntermediateField.adjoin (IntermediateField.adjoin k {x}) {t})
  let Ktx := restrictScalars k (IntermediateField.adjoin (IntermediateField.adjoin k {t}) {x})
  let : Algebra (IntermediateField.adjoin k {x}) Kxt :=
    (IntermediateField.adjoin (IntermediateField.adjoin k {x}) {t}).algebra
  let : Module (IntermediateField.adjoin k {x}) Kxt := Algebra.toModule
  let : SMul (IntermediateField.adjoin k {x}) Kxt := Algebra.toSMul
  let : Algebra (IntermediateField.adjoin k {t}) Ktx :=
    (IntermediateField.adjoin (IntermediateField.adjoin k {t}) {x}).algebra
  let : Module (IntermediateField.adjoin k {t}) Ktx := Algebra.toModule
  let : SMul (IntermediateField.adjoin k {t}) Ktx := Algebra.toSMul
  have : Module.Finite (IntermediateField.adjoin k {x}) Kxt :=
    IntermediateField.adjoin.finiteDimensional ht'.isIntegral
  have : Module.Finite Kxt F := by
    unfold Kxt
    rw [adjoin_simple_comm]
    have : IsScalarTower (IntermediateField.adjoin k {t}) Ktx F := isScalarTower_mid' _
    exact .right (IntermediateField.adjoin k {t}) Ktx F
  have : IsScalarTower (IntermediateField.adjoin k {x}) Kxt F := isScalarTower_mid' _
  exact Module.Finite.trans Kxt F
theorem adjoin_inv (x : F) :
    IntermediateField.adjoin k ({x⁻¹} : Set F) = IntermediateField.adjoin k {x} := by
  apply le_antisymm <;> apply IntermediateField.adjoin_le_iff.mpr
  · exact Set.singleton_subset_iff.mpr (IntermediateField.inv_mem _ (mem_adjoin_simple_self k x))
  · apply Set.singleton_subset_iff.mpr
    change x ∈ IntermediateField.adjoin k ({x⁻¹} : Set F)
    simpa only [inv_inv] using
      (IntermediateField.adjoin k ({x⁻¹} : Set F)).inv_mem (mem_adjoin_simple_self k x⁻¹)
@[instance_reducible]
noncomputable def fractionChartAlgebra (u : F) (hu : Transcendental k u) :
    Algebra k[X] (IntermediateField.adjoin k {u}) :=
  ((algebraMap (Algebra.adjoin k {u}) (IntermediateField.adjoin k {u})).comp
    (Polynomial.algEquivOfTranscendental k u hu).toRingHom).toAlgebra
theorem fraction_chart {u : F} (hu : Transcendental k u) :
    let K := IntermediateField.adjoin k {u}
    letI : Algebra k[X] F := chartAlgebra u
    letI : Algebra k[X] K := fractionChartAlgebra u hu
    IsFractionRing k[X] K ∧ IsScalarTower k[X] K F := by
  let R := Algebra.adjoin k ({u} : Set F)
  let K := IntermediateField.adjoin k ({u} : Set F)
  let e := Polynomial.algEquivOfTranscendental k u hu
  let : Algebra k[X] F := chartAlgebra u
  let : Algebra k[X] K := fractionChartAlgebra u hu
  constructor
  · exact (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (S := K) e.symm.toRingEquiv).mp
      (inferInstance : IsFractionRing R K)
  · apply IsScalarTower.of_algebraMap_eq
    intro P
    change Polynomial.aeval u P = ((e P : R) : F)
    rw [Polynomial.algEquivOfTranscendental_apply, Polynomial.aeval_subalgebra_coe]
end K1_14_3R_3_1_3_1
end
section
set_option autoImplicit false
namespace K1_14_3R_3_1_3_1
open K1_14_3R_3_1_3 (chartAlgebra)
open scoped Polynomial
theorem proof : K1_14_3R_3_1_3.c1 := by
  intro k F _ _ _ t x ht hx
  have hfin := finite_projection ht.1 ht.2.1 hx
  refine ⟨hfin, ?_⟩
  have hxi : Transcendental k x⁻¹ := fun h => hx (IsAlgebraic.inv_iff.mp h)
  let K := IntermediateField.adjoin k ({x⁻¹} : Set F)
  let : Algebra k[X] F := chartAlgebra x⁻¹
  let : Algebra k[X] K := fractionChartAlgebra x⁻¹ hxi
  have : IsFractionRing k[X] K := (fraction_chart hxi).1
  have : IsScalarTower k[X] K F := (fraction_chart hxi).2
  have : FiniteDimensional K F := by
    change Module.Finite (IntermediateField.adjoin k ({x⁻¹} : Set F)) F
    rw [adjoin_inv]
    exact hfin
  exact finite_normalization k[X] K F (polynomial_frobenius_lattices k)
end K1_14_3R_3_1_3_1
end
section
end
