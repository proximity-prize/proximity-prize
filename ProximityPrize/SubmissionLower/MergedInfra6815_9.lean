import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.MergedInfra6815_5
import ProximityPrize.SubmissionLower.LowerFoundation
import ProximityPrize.SubmissionLower.MergedInfra6815_4
import ProximityPrize.SubmissionLower.MergedInfra6815_6
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.FirstSlicePoleBudget6807
open scoped Classical BigOperators WithZero
open RCN057 (WeightBound)
open RCN002 RCN005 RCN006 RCN026 RCN055 RCN341 RCN095 RCN136 RCN156 RCN187 RCN204 RCN234 RCN313
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

section ActualSource
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

end ActualSource
end
end ProximityPrize.SubmissionLower.FirstSlicePoleBudget6807
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.PureFlagSliceBudget6807
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN026 RCN046 RCN084 RCN095 RCN114
open RCN204 RCN234 RCN237 RCN264 RCN340 RCN341
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {E : Type} [Field E] [IsAlgClosed E]
  {G T H : MvPolynomial (Fin 3) E} {p q : FlagDegree}
  {base : ∀ C : RegularComponent E G T H, SeparableLiteralCoordinate C.1}

theorem sum_flagPole_le (U : AdaptiveUnitPoleBudget base p q)
    (C : RegularComponent E G T H) (r : FlagDegree)
    (W : Finset (Place E (CoordinateField E C.1))) :
    (∑ v ∈ W, flagPole v.val (coordinate E C.1) r) ≤
      (U.toPrimeFlagBudgetFamily.weightedCost r C : ℤ) := by
  have hz := U.zPole C W
  have hy := U.yzPole C W
  have ha := U.allPole C W
  simp only [exponentSetPoleWeight_unitZ] at hz
  simp only [exponentSetPoleWeight_unitYZ] at hy
  simp only [exponentSetPoleWeight_unitAll] at ha
  have h := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg r.zOnly))
    (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg r.yz)))
    (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg r.all))
  simpa only [flagPole, Finset.sum_add_distrib, ← Finset.mul_sum,
    PrimeFlagBudgetFamily.weightedCost,
    AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily, Nat.cast_add, Nat.cast_mul] using h

theorem weightedCost_add_smul (U : AdaptiveUnitPoleBudget base p q)
    (C : RegularComponent E G T H) (d w : ℕ) (J V : FlagDegree) :
    U.toPrimeFlagBudgetFamily.weightedCost (d • J + w • V) C =
      d * U.toPrimeFlagBudgetFamily.weightedCost J C +
        w * U.toPrimeFlagBudgetFamily.weightedCost V C := by
  simp only [PrimeFlagBudgetFamily.weightedCost]
  change (d*J.zOnly+w*V.zOnly)*U.zCost C +
      (d*J.yz+w*V.yz)*U.yzCost C + (d*J.all+w*V.all)*U.allCost C = _
  dsimp only [AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily]
  ring

theorem all_active_slice_costs_le (F N R : MvPolynomial (Fin 3) E)
    (hF : F ≠ 0) (p q r : FlagDegree) (hFp : PolynomialInFlag p F)
    (base : ∀ g : ↥(activeFactors F N), ∀ C : RegularComponent E g.1 N R,
      SeparableLiteralCoordinate C.1)
    (U : ∀ g : ↥(activeFactors F N), AdaptiveUnitPoleBudget (base g) (exactFlag g.1) q) :
    (∑ g : ↥(activeFactors F N), ∑ C : RegularComponent E g.1 N R,
      (U g).toPrimeFlagBudgetFamily.weightedCost r C) ≤ flagMixed p q r := by
  exact (Finset.sum_le_sum (fun g _ =>
    (U g).toPrimeFlagBudgetFamily.sum_weightedCost_le r)).trans
      (activeFactors_mixed_sum_le F N hF p q r hFp)

end
end ProximityPrize.SubmissionLower.PureFlagSliceBudget6807
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.WeightedPlaceOrder6807
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

section ValuationFiltration
variable {A L : Type*} [CommRing A] [Field L]
  (iota : A →+* L) (v : Valuation L (WithZero (Multiplicative ℤ)))
  (hbound : ∀ a : A, v (iota a) ≤ 1)

def orderIdeal (n : ℕ) : Ideal A where
  carrier := {a | v (iota a) ≤ WithZero.exp (-(n : ℤ))}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change v (iota (a+b)) ≤ _
    rw [map_add]
    exact (v.map_add _ _).trans (max_le ha hb)
  smul_mem' := by
    intro r a ha
    change v (iota (r*a)) ≤ _
    rw [map_mul, map_mul]
    simpa only [one_mul] using mul_le_mul' (hbound r) ha

theorem ideal_pow_value_le (J : Ideal A)
    (hvanish : ∀ a ∈ J, v (iota a) < 1) (n : ℕ) :
    J^n ≤ orderIdeal iota v hbound n := by
  induction n with
  | zero =>
    intro a _
    change v (iota a) ≤ WithZero.exp (-(0 : ℤ))
    simpa only [neg_zero, WithZero.exp_zero] using hbound a
  | succ n ih =>
    rw [pow_succ]
    apply Ideal.mul_le.mpr
    intro a ha b hb
    have h1 : v (iota b) ≤ WithZero.exp (-1 : ℤ) :=
      RCN359.value_le_exp_neg_one (hvanish b hb)
    have hn : v (iota a) ≤ WithZero.exp (-(n : ℤ)) := ih ha
    change v (iota (a*b)) ≤ WithZero.exp (-((n+1 : ℕ) : ℤ))
    rw [map_mul, map_mul]
    have hm := mul_le_mul' hn h1
    have he : WithZero.exp (-(n : ℤ)) * WithZero.exp (-1 : ℤ) =
        WithZero.exp (-((n+1 : ℕ) : ℤ)) := by
      rw [← WithZero.exp_add]
      congr 1
      push_cast
      ring
    exact hm.trans_eq he

theorem order_ge_of_value_le (x : L) (hx : x ≠ 0) (n : ℕ)
    (hn : v x ≤ WithZero.exp (-(n : ℤ))) :
    (n : ℤ) ≤ -(v x).log := by
  have hv0 : v x ≠ 0 := (Valuation.ne_zero_iff v).mpr hx
  have hlog : (v x).log ≤ -(n : ℤ) := by
    have h := (WithZero.log_le_log hv0 (by simp)).2 hn
    simpa only [WithZero.log_exp] using h
  omega

include hbound in

theorem normalized_order_ge_pow {K : Type*} [Field K] [Algebra K A]
    (phi : A →ₐ[K] K)
    (hpoint : ∀ a, v (iota a) < 1 ↔ phi a = 0)
    (n : ℕ) (a b : A) (ha : a ∈ (RingHom.ker phi.toRingHom)^n)
    (hb : phi b ≠ 0) (hx : iota a / iota b ≠ 0) :
    (n : ℤ) ≤ -(v (iota a / iota b)).log := by
  have hbval : v (iota b) = 1 := by
    apply le_antisymm (hbound b)
    apply le_of_not_gt
    intro h
    exact hb ((hpoint b).mp h)
  have han : v (iota a) ≤ WithZero.exp (-(n : ℤ)) :=
    ideal_pow_value_le iota v hbound (RingHom.ker phi.toRingHom)
      (fun a ha => (hpoint a).mpr ha) n ha
  apply order_ge_of_value_le v _ hx n
  simpa only [map_div₀, hbval, div_one] using han

end ValuationFiltration

section ActualAffinePlaces
variable (K A L : Type*) [Field K] [IsAlgClosed K]
  [CommRing A] [IsDomain A] [Field L]
  [Algebra K A] [Algebra K L] [Algebra A L] [IsFractionRing A L]
  [Algebra (Polynomial K) A] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) A] [IsScalarTower K (Polynomial K) L]
  [IsScalarTower K A L] [IsScalarTower (Polynomial K) A L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

local instance : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K),
      ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L,
      ← IsScalarTower.algebraMap_apply K (Polynomial K) L]

theorem actual_normalized_order_ge_pow (phi : A →ₐ[K] K)
    (n : ℕ) (a b : A) (ha : a ∈ (RingHom.ker phi.toRingHom)^n)
    (hb : phi b ≠ 0)
    (hx : algebraMap A L a / algebraMap A L b ≠ 0) :
    (n : ℤ) ≤ RCN026.order K L (RCN344.modelPlace K L A phi)
      (algebraMap A L a / algebraMap A L b) := by
  exact normalized_order_ge_pow (algebraMap A L)
    ((RCN000.actualPointPlace K A L phi).valuation L)
    (RCN000.actual_model_value_le_one K A L phi) phi
    (RCN000.actual_model_value_lt_one_iff K A L phi) n a b ha hb hx

end ActualAffinePlaces
end
end ProximityPrize.SubmissionLower.WeightedPlaceOrder6807
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.WeightedZeroMass6807
open scoped Classical BigOperators WithZero
open RCN026
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

theorem weighted_places_le_poleMass {I : Type*} [Fintype I]
    (x : L) (hx : x ≠ 0) (place : I → Place K L)
    (hinj : Function.Injective place) (mu : I → ℕ)
    (hmu : ∀ i, 1 ≤ mu i)
    (horder : ∀ i, (mu i : ℤ) ≤ order K L (place i) x) :
    (∑ i, (mu i : ℤ)) ≤
      ∑ v ∈ placesFor K L x hx, RCN346.poleOrder K L v x := by
  classical
  let U : Finset (Place K L) := Finset.univ.image place
  have hsub : U ⊆ placesFor K L x hx := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    apply placesFor_covers K L x hx (place i)
    have hi := horder i
    have hm : (1 : ℤ) ≤ (mu i : ℤ) := by exact_mod_cast hmu i
    omega
  calc
    (∑ i, (mu i : ℤ)) ≤ ∑ i, zeroOrder K L (place i) x := by
      apply Finset.sum_le_sum
      intro i _
      exact (horder i).trans (le_max_right _ _)
    _ = ∑ v ∈ U, zeroOrder K L v x := by
      dsimp only [U]
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    _ ≤ ∑ v ∈ placesFor K L x hx, zeroOrder K L v x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro v _ _
      exact zeroOrder_nonneg K L v x
    _ = _ := sum_placesFor_zero_eq_pole K L x hx

section Affine
variable (A : Type*) [CommRing A] [IsDomain A]
  [Algebra K A] [Algebra A L] [IsFractionRing A L]
  [Algebra (Polynomial K) A]
  [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
  [IsScalarTower (Polynomial K) A L]

theorem weighted_affine_points_le_poleMass {I : Type*} [Fintype I]
    (phi : I → (A →ₐ[K] K)) (hinj : Function.Injective phi)
    (mu : I → ℕ) (hmu : ∀ i, 1 ≤ mu i) (a b : A)
    (ha : ∀ i, a ∈ (RingHom.ker (phi i).toRingHom)^(mu i))
    (hb : ∀ i, phi i b ≠ 0)
    (hx : algebraMap A L a / algebraMap A L b ≠ 0) :
    (∑ i, (mu i : ℤ)) ≤
      ∑ v ∈ placesFor K L (algebraMap A L a / algebraMap A L b) hx,
        RCN346.poleOrder K L v (algebraMap A L a / algebraMap A L b) := by
  apply weighted_places_le_poleMass K L _ hx
    (fun i => RCN344.modelPlace K L A (phi i))
    ((RCN344.modelPlace_injective K L A).comp hinj) mu hmu
  intro i
  exact WeightedPlaceOrder6807.actual_normalized_order_ge_pow K A L
    (phi i) (mu i) a b (ha i) (hb i) hx

theorem weighted_affine_points_scaled {I : Type*} [Fintype I]
    (phi : I → (A →ₐ[K] K)) (hinj : Function.Injective phi)
    (mu : I → ℕ) (hmu : ∀ i, 1 ≤ mu i) (a b : A)
    (ha : ∀ i, a ∈ (RingHom.ker (phi i).toRingHom)^(mu i))
    (hb : ∀ i, phi i b ≠ 0)
    (hx : algebraMap A L a / algebraMap A L b ≠ 0)
    (d cost : ℕ)
    (hpole : ∀ W : Finset (Place K L),
      (d : ℤ) * (∑ v ∈ W,
        RCN346.poleOrder K L v (algebraMap A L a / algebraMap A L b)) ≤ cost) :
    d * (∑ i, mu i) ≤ cost := by
  have hm := weighted_affine_points_le_poleMass K L A phi hinj mu hmu a b ha hb hx
  have hs := (mul_le_mul_of_nonneg_left hm (Int.natCast_nonneg d)).trans
    (hpole (placesFor K L _ hx))
  exact_mod_cast hs

end Affine
end
end ProximityPrize.SubmissionLower.WeightedZeroMass6807
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.ActualWeightedFirstSlice6807
open RCN057 (WeightBound)
open RCN204 (flagPole)
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN055 RCN074 RCN086 RCN095
open RCN134 RCN135 RCN136 RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualSliceMultiplicity6807 ActualFirstCutPole6807
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000
variable {K I E T : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Fintype T] [Nonempty T]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "w" => RCN326.w

local notation "φE" => RingHom.comp (algebraMap (GenericField K) E) (polynomialEmbedding K)

theorem first_cut_on_prime_slice_of
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (old : T → FirstTailComponent S)
    (emb : ∀ i, CoordinateField Ω (old i).1 →ₐ[Ω] E)
    (hinj : Function.Injective (fun i => embeddingPoint (old i).1 (emb i)))
    (D : Ideal PE) [D.IsPrime] (sep : SeparableLiteralCoordinate D)
    (hpoint : ∀ i, D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint (old i).1 (emb i)) : PE →ₐ[E] E).toRingHom)
    (hcarrier : scalarPolynomialMap Ω E S.G ∈ D)
    (hisolated : scalarPolynomialMap Ω E
      (globalTailCut (polynomialEmbedding K) S.F (w+1)) ∉ D)
    (e d cost : ℕ)
    (hpole : surfaceMap φE S.F ∈ D → surfaceMap φE (polyH K S.F) ∉ D →
      (∀ F0 : MvPolynomial (Fin 4) K,
        (∀ i, surfaceMap (polynomialEmbedding K) F0 ∉ (old i).1) → surfaceMap φE F0 ∉ D) →
      ∀ W : Finset (Place E (CoordinateField E D)),
        (d : ℤ) * (∑ nu ∈ W, RCN187.poleOrder nu.val
          (SecondJetComponentRoots.coefficientMap φE D (baseNumerator S.F (w-1))/
            SecondJetComponentRoots.coefficientMap φE D (polyH K S.F)^e)) ≤ cost) :
    d * (∑ i, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i)) ≤ cost := by
  classical
  let A := CoordinateRing E D
  let Lf := CoordinateField E D
  letI := quotientPolynomialAlgebra E D sep.index
  letI := polynomialBaseAlgebra E D sep.index
  letI := rationalBaseAlgebra E D sep.index sep.transcendental
  letI := quotientBaseScalarTower E D sep.index
  letI := polynomialBaseScalarTower E D sep.index
  letI := quotientFractionScalarTower E D sep.index
  letI := polynomialRationalScalarTower E D sep.index sep.transcendental
  letI := rationalBaseScalarTower E D sep.index sep.transcendental
  letI : FiniteDimensional (RatFunc E) Lf := sep.finite
  letI : Algebra.IsSeparable (RatFunc E) Lf := sep.separable
  let i0 : T := Classical.choice inferInstance
  let ev := SecondJetComponentRoots.coefficientMap φE D
  let evalPoint := fun i => pointHom E D (slicePoint S (old i) (emb i) D (hpoint i))
  let mu := fun i => localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i)
  let a : A := firstTailInSlice S D
  let H : A := originalToSlice (K := K) D (polyH K S.F)
  let c : A := firstTailScalarInSlice (K := K) D
  let b : A := c*H^(e+3)
  let iota : A →+* Lf := algebraMap A Lf
  have hpi : Function.Injective evalPoint := by
    intro i j hh
    have hs := pointHom_injective E D hh
    exact hinj (congrArg Subtype.val hs)
  have hmu : ∀ i, 1 ≤ mu i := fun i => one_le_localMultiplicity S hproper (old i)
  have ha : ∀ i, a ∈ (RingHom.ker (evalPoint i).toRingHom)^(mu i) := by
    intro i
    exact actual_first_tail_mem_point_power S hproper (old i) (emb i) D
      (hpoint i) hcarrier
  have hHpt : ∀ i, evalPoint i H ≠ 0 := fun i =>
    original_H_point_ne_zero S (old i) (emb i) D (hpoint i)
  have hcpt : ∀ i, evalPoint i c ≠ 0 := fun i => firstTailScalar_point_ne_zero D _
  have hb : ∀ i, evalPoint i b ≠ 0 := by
    intro i
    simpa only [b,map_mul,map_pow] using mul_ne_zero (hcpt i) (pow_ne_zero _ (hHpt i))
  have hiota : Function.Injective iota := IsFractionRing.injective A Lf
  have hHi : iota H ≠ 0 := by
    intro hz
    have hH0 : H = 0 := hiota (by simpa only [map_zero] using hz)
    exact hHpt i0 (by rw [hH0,map_zero])
  have hci : iota c ≠ 0 := by
    intro hz
    have hc0 : c = 0 := hiota (by simpa only [map_zero] using hz)
    exact hcpt i0 (by rw [hc0,map_zero])
  have hai : iota a ≠ 0 := by
    intro hz
    exact firstTailInSlice_ne_zero S D hisolated
      (hiota (by simpa only [map_zero] using hz))
  have hbi : iota b ≠ 0 := by
    simpa only [b,map_mul,map_pow] using mul_ne_zero hci (pow_ne_zero _ hHi)
  have hx : iota a / iota b ≠ 0 := div_ne_zero hai hbi
  have hrepr : iota a / iota b = ev (baseNumerator S.F (w-1))/ev (polyH K S.F)^e := by
    have hh := normalized_first_tail_identity iota a
      (originalToSlice (K := K) D (baseNumerator S.F (w-1))) H c e
      (firstTailInSlice_normal_form S D) hHi hci
    have hbv : iota (originalToSlice (K := K) D (baseNumerator S.F (w-1))) =
        ev (baseNumerator S.F (w-1)) := originalToSlice_fraction_value D _
    have hHv : iota H = ev (polyH K S.F) := originalToSlice_fraction_value D _
    exact hh.trans (by rw [hbv, hHv])
  have hnot (F0 : MvPolynomial (Fin 4) K)
      (hn0 : ∀ i, surfaceMap (polynomialEmbedding K) F0 ∉ (old i).1) :
      surfaceMap φE F0 ∉ D := by
    intro hmem
    have hz := RingHom.mem_ker.mp (hpoint i0 hmem)
    change MvPolynomial.eval (embeddingPoint (old i0).1 (emb i0))
      (surfaceMap φE F0) = 0 at hz
    apply GenericSlicePoints6807.scalar_eval_ne_zero (old i0).1 (emb i0)
      (surfaceMap (polynomialEmbedding K) F0) (hn0 i0)
    simpa only [scalar_surfaceMap, MvPolynomial.aeval_eq_eval] using hz
  have hFd : surfaceMap φE S.F ∈ D := by
    rw [← scalar_surfaceMap]
    exact D.mem_of_dvd (map_dvd (scalarPolynomialMap Ω E) S.G_dvd_surface) hcarrier
  have hHd : surfaceMap φE (polyH K S.F) ∉ D :=
    hnot _ (fun i => RCN312.firstTailComponent_regularity_not_mem S (old i))
  apply WeightedZeroMass6807.weighted_affine_points_scaled E Lf A
    evalPoint hpi mu hmu a b ha hb hx d cost
  intro W
  change (d : ℤ) * (∑ nu ∈ W, RCN187.poleOrder nu.val (iota a / iota b)) ≤ (cost : ℤ)
  rw [hrepr]
  exact hpole hFd hHd hnot W

end
end ProximityPrize.SubmissionLower.ActualWeightedFirstSlice6807
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.WeightedSliceAssignment6807
open scoped Classical BigOperators
open RCN002 RCN007 RCN072 RCN084 RCN095 RCN134 RCN264
noncomputable section
set_option autoImplicit false
local instance {A : Type*} : DecidableEq A := Classical.decEq A
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
variable {E I : Type} [Field E] [IsAlgClosed E] [Fintype I]
local notation "Poly" => MvPolynomial (Fin 3) E

abbrev SliceComponent (F N R : Poly) :=
  (g : ↥(activeFactors F N)) × RegularComponent E g.1 N R

theorem exists_point_assignment (F N R : Poly) (point : I → Fin 3 → E)
    (hcover : ∀ i, ∃ g : ↥(activeFactors F N), MvPolynomial.eval (point i) g.1 = 0)
    (hN : ∀ i, MvPolynomial.eval (point i) N = 0)
    (hR : ∀ i, MvPolynomial.eval (point i) R ≠ 0) :
    ∃ assign : I → SliceComponent F N R,
      ∀ i, (assign i).2.1 ≤ RingHom.ker
        (MvPolynomial.aeval (point i) : Poly →ₐ[E] E).toRingHom := by
  classical
  have he (i : I) : ∃ a : SliceComponent F N R,
      a.2.1 ≤ RingHom.ker (MvPolynomial.aeval (point i) : Poly →ₐ[E] E).toRingHom := by
    obtain ⟨g, hg⟩ := hcover i
    obtain ⟨C, hC⟩ := exists_regular_component E g.1 N R (point i) hg (hN i) (hR i)
    exact ⟨⟨g,C⟩,hC⟩
  exact ⟨fun i => (he i).choose, fun i => (he i).choose_spec⟩

omit [Field E] [IsAlgClosed E] in

theorem weighted_assignment_sum {A : Type*} [Fintype A] [DecidableEq A]
    (assign : I → A) (mu : I → ℕ) :
    (∑ a, ∑ i with assign i = a, mu i) = ∑ i, mu i := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := assign) (fun _ _ => Finset.mem_univ _) _

omit [Field E] [IsAlgClosed E] in

theorem sum_local_slice_bounds {A : Type*} [Fintype A] [DecidableEq A]
    (assign : I → A) (mu : I → ℕ) (cost : A → ℕ) (d : ℕ)
    (hlocal : ∀ a, d * (∑ i with assign i = a, mu i) ≤ cost a) :
    d * (∑ i, mu i) ≤ ∑ a, cost a := by
  rw [← weighted_assignment_sum assign mu, Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => hlocal a)

theorem first_tail_not_mem_assigned (F N A R : Poly)
    (point : I → Fin 3 → E) (assign : I → SliceComponent F N R)
    (hpoint : ∀ i, (assign i).2.1 ≤ RingHom.ker
      (MvPolynomial.aeval (point i) : Poly →ₐ[E] E).toRingHom)
    (hisolated : ∀ i, IsolatedPoint F N A (point i)) (i : I) :
    A ∉ (assign i).2.1 := by
  let g := (assign i).1
  let C := (assign i).2
  exact hisolated i C.1 inferInstance (regularComponent_ne_point E g.1 N R C)
    (hpoint i)
    (C.1.mem_of_dvd (activeFactors_spec F N g).2.1
      (regularComponent_G_mem E g.1 N R C))
    (regularComponent_T_mem E g.1 N R C)

end
end ProximityPrize.SubmissionLower.WeightedSliceAssignment6807
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.SmallSliceBudgets6807
open scoped Classical BigOperators
open RCN095 RCN237 RCN264 RCN340 RCN341 RCN084 RCN039 RCN046
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
variable {E : Type} [Field E] [IsAlgClosed E]
local notation "Poly" => MvPolynomial (Fin 3) E

structure SliceBudgets (F N R : Poly) (q : FlagDegree) where
  base : ∀ g : ↥(activeFactors F N), ∀ C : RegularComponent E g.1 N R,
    SeparableLiteralCoordinate C.1
  unit : ∀ g : ↥(activeFactors F N),
    AdaptiveUnitPoleBudget (base g) (exactFlag g.1) q

theorem exists_sliceBudgets (F N R : Poly) (p q : FlagDegree)
    (hF : F ≠ 0) (hFp : PolynomialInFlag p F) (hNq : PolynomialInFlag q N)
    (c : ℕ) [CharP E c] (hdeg : p.zOnly+p.yz+p.all < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c) :
    Nonempty (SliceBudgets F N R q) := by
  classical
  obtain ⟨base,hY,hZ⟩ := exists_small_projection_data F N R hF p q hFp hNq
    c hdeg hmix
  have he (g : ↥(activeFactors F N)) :
      Nonempty (AdaptiveUnitProjectionFamily (base g) (exactFlag g.1) q) := by
    have hg := activeFactors_spec F N g
    exact exists_adaptiveUnitProjectionFamily_of_nested (exactFlag g.1) q
      (base g) (hY g) (hZ g) hg.2.2.2 hg.1 hg.2.2.1
      ((support_subset_flagSupport_iff _ _).mpr (polynomialIn_exactFlag g.1))
      ((support_subset_flagSupport_iff _ _).mpr hNq)
  exact ⟨⟨base, fun g => (Classical.choice (he g)).toAdaptiveUnitPoleBudget⟩⟩

theorem sum_cost_le (F N R : Poly) (p q r : FlagDegree)
    (hF : F ≠ 0) (hFp : PolynomialInFlag p F) (B : SliceBudgets F N R q) :
    (∑ g : ↥(activeFactors F N), ∑ C : RegularComponent E g.1 N R,
      (B.unit g).toPrimeFlagBudgetFamily.weightedCost r C) ≤ flagMixed p q r :=
  PureFlagSliceBudget6807.all_active_slice_costs_le F N R hF p q r hFp B.base B.unit

end
end ProximityPrize.SubmissionLower.SmallSliceBudgets6807
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.ActiveSliceAssembly6807
open RCN057 (WeightBound)
open RCN086 RCN074
open scoped Classical BigOperators
open RCN002 RCN007 RCN084 RCN095 RCN134 RCN135 RCN136 RCN156 RCN159
open RCN207 RCN208 RCN234 RCN237 RCN243 RCN244 RCN248 RCN264 RCN267 RCN313 RCN341
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807 GenericSlicePoints6807 WeightedSliceAssignment6807
open SmallSliceBudgets6807
open RCN204 (flagPole)
open RCN026 (Place)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 500000
variable {K I E T : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Fintype T]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "w" => RCN326.w

theorem carrier_derivative_not_mem
    (S : Stage K I Gamma x p flag errorCap stageSupport) (C : FirstTailComponent S) :
    MvPolynomial.pderiv (1 : Fin 3) S.G ∉ C.1 := by
  intro hd
  apply RCN312.firstTailComponent_regularity_not_mem S C
  change surfaceMap (polynomialEmbedding K)
    (MvPolynomial.pderiv (2 : Fin 4) S.F) ∈ C.1
  rw [← surfaceMap_pderiv_R]
  obtain ⟨Q,hQ⟩ := S.G_dvd_surface
  rw [hQ,MvPolynomial.pderiv_mul]
  exact C.1.add_mem (C.1.mul_mem_right Q hd)
    (C.1.mul_mem_right (MvPolynomial.pderiv (1 : Fin 3) Q)
      (regularComponent_G_mem Ω S.G _ _ C))

def SliceCharge (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (Good : FirstTailComponent S → Prop) (N : PE) (c m n : ℕ) (J V : FlagDegree) : Prop :=
  ∀ (T0 : Type) [Fintype T0] [Nonempty T0] (old : T0 → FirstTailComponent S),
    (∀ i, Good (old i)) → ∀ emb : ∀ i, CoordinateField Ω (old i).1 →ₐ[Ω] E,
    Function.Injective (fun i => embeddingPoint (old i).1 (emb i)) →
    ∀ (D : Ideal PE) [D.IsPrime], SeparableLiteralCoordinate D →
    (∀ i, D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint (old i).1 (emb i)) : PE →ₐ[E] E).toRingHom) →
    scalarPolynomialMap Ω E S.G ∈ D → N ∈ D →
    scalarPolynomialMap Ω E (globalTailCut (polynomialEmbedding K) S.F (w+1)) ∉ D →
    ∀ CJ CV : ℕ,
    (∀ W : Finset (Place E (CoordinateField E D)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E D) J) ≤ (CJ : ℤ)) →
    (∀ W : Finset (Place E (CoordinateField E D)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E D) V) ≤ (CV : ℤ)) →
    c * (∑ i, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i)) ≤ m*CJ+n*CV

theorem first_cut_on_all_active_slices
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (old : T → FirstTailComponent S)
    (emb : ∀ i, CoordinateField Ω (old i).1 →ₐ[Ω] E)
    (hinj : Function.Injective (fun i => embeddingPoint (old i).1 (emb i)))
    (N : PE) (q : FlagDegree) (hNq : PolynomialInFlag q N)
    (hNpoint : ∀ i, MvPolynomial.eval (embeddingPoint (old i).1 (emb i)) N = 0)
    (hisolated : ∀ i, IsolatedPoint (scalarPolynomialMap Ω E S.G) N
      (scalarPolynomialMap Ω E (globalTailCut (polynomialEmbedding K) S.F (w+1)))
      (embeddingPoint (old i).1 (emb i)))
    (hdeg : flag.zOnly+flag.yz+flag.all < p)
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(q.zOnly+q.yz+q.all) < p)
    (Good : FirstTailComponent S → Prop) (hgood : ∀ i, Good (old i))
    (c m n : ℕ) (J V : FlagDegree) (hslice : SliceCharge S hproper Good N c m n J V) :
    c*(∑ i, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i)) ≤
      flagMixed flag q (m • J + n • V) := by
  classical
  let F := scalarPolynomialMap Ω E S.G
  let A := scalarPolynomialMap Ω E (globalTailCut (polynomialEmbedding K) S.F (w+1))
  let R := scalarPolynomialMap Ω E (regularitySurface (polynomialEmbedding K) S.F)
  let point := fun i => embeddingPoint (old i).1 (emb i)
  let mu := fun i => localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i)
  let D1 := m • J + n • V
  have hF : F ≠ 0 := by
    intro hz
    apply S.irreducible_G.ne_zero
    apply MvPolynomial.map_injective (algebraMap Ω E) (algebraMap Ω E).injective
    simpa only [F, scalarPolynomialMap, map_zero] using hz
  have hFp : PolynomialInFlag flag F := inFlag_map _ S.flag_support
  have hFpoint (i : T) : MvPolynomial.eval (point i) F = 0 := by
    rw [scalar_eval_embedding]
    have hc := regularComponent_G_mem Ω S.G _ _ (old i)
    have hz : coordinateEvaluation Ω (old i).1 S.G = 0 := by
      apply (RingHom.mem_ker (f := (coordinateEvaluation Ω (old i).1).toRingHom)).mp
      rw [coordinateEvaluation_ker]
      exact hc
    rw [hz,map_zero]
  have hApoint (i : T) : MvPolynomial.eval (point i) A = 0 := by
    rw [scalar_eval_embedding]
    have hc := regularComponent_T_mem Ω S.G _ _ (old i)
    have hz : coordinateEvaluation Ω (old i).1
        (globalTailCut (polynomialEmbedding K) S.F (w+1)) = 0 := by
      apply (RingHom.mem_ker (f := (coordinateEvaluation Ω (old i).1).toRingHom)).mp
      rw [coordinateEvaluation_ker]
      exact hc
    rw [hz,map_zero]
  have hRpoint (i : T) : MvPolynomial.eval (point i) R ≠ 0 :=
    scalar_eval_ne_zero (old i).1 (emb i) _
      (regularComponent_H_not_mem Ω S.G _ _ (old i))
  have hDpoint (i : T) :
      MvPolynomial.eval (point i) (MvPolynomial.pderiv (1 : Fin 3) F) ≠ 0 := by
    have hh := scalar_eval_ne_zero (old i).1 (emb i)
      (MvPolynomial.pderiv (1 : Fin 3) S.G) (carrier_derivative_not_mem S (old i))
    simpa only [F,scalarPolynomialMap,MvPolynomial.pderiv_map] using hh
  have hcover (i : T) : ∃ g : ↥(activeFactors F N), MvPolynomial.eval (point i) g.1 = 0 :=
    exists_active_factor_of_isolated F N A R hF (point i)
      (hFpoint i) (hApoint i) (hRpoint i) (hDpoint i) (hisolated i)
  obtain ⟨assign,hassigned⟩ := exists_point_assignment F N R point hcover hNpoint hRpoint
  let budgets := Classical.choice
    (exists_sliceBudgets F N R flag q hF hFp hNq p hdeg hmix)
  let cost := fun a : SliceComponent F N R =>
    (budgets.unit a.1).toPrimeFlagBudgetFamily.weightedCost D1 a.2
  have hlocal (a : SliceComponent F N R) :
      c*(∑ i with assign i = a, mu i) ≤ cost a := by
    let T0 := {i : T // assign i = a}
    by_cases hne : Nonempty T0
    · letI : Nonempty T0 := hne
      let old0 := fun i : T0 => old i.1
      let emb0 := fun i : T0 => emb i.1
      have hi0 : Function.Injective (fun i : T0 => embeddingPoint (old0 i).1 (emb0 i)) := by
        intro i j hh
        exact Subtype.ext (hinj hh)
      have hpt (i : T0) : a.2.1 ≤ RingHom.ker
          (MvPolynomial.aeval (embeddingPoint (old0 i).1 (emb0 i)) : PE →ₐ[E] E).toRingHom := by
        have he : assign i.1 = a := i.2
        have hh := hassigned i.1
        rw [he] at hh
        exact hh
      have hcar : F ∈ a.2.1 := a.2.1.mem_of_dvd (activeFactors_spec F N a.1).2.1
        (regularComponent_G_mem E a.1.1 N R a.2)
      let i0 : T0 := Classical.choice hne
      have hAz : A ∉ a.2.1 := by
        have hh := first_tail_not_mem_assigned F N A R point assign hassigned hisolated i0.1
        have he : assign i0.1 = a := i0.2
        rwa [he] at hh
      let unit := budgets.unit a.1
      let CJ := unit.toPrimeFlagBudgetFamily.weightedCost J a.2
      let CV := unit.toPrimeFlagBudgetFamily.weightedCost V a.2
      have hb := hslice T0 old0 (fun i => hgood i.1) emb0 hi0 a.2.1 (budgets.base a.1 a.2)
        hpt hcar (regularComponent_T_mem E a.1.1 N R a.2) hAz CJ CV
        (PureFlagSliceBudget6807.sum_flagPole_le unit a.2 J)
        (PureFlagSliceBudget6807.sum_flagPole_le unit a.2 V)
      have hsum : (∑ i with assign i = a, mu i) = ∑ i : T0, mu i.1 := by
        simpa only [T0,Finset.subtype_univ] using
          (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset T))
            mu (p := fun i => assign i = a)).symm
      rw [hsum]
      calc
        _ ≤ m*CJ+n*CV := hb
        _ = cost a := (PureFlagSliceBudget6807.weightedCost_add_smul
          unit a.2 m n J V).symm
    · have he : (Finset.univ.filter (fun i : T => assign i = a)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hne ⟨⟨i,(Finset.mem_filter.mp hi).2⟩⟩
      simp only [he,Finset.sum_empty,Nat.mul_zero,Nat.zero_le]
  calc
    _ ≤ ∑ a : SliceComponent F N R, cost a := sum_local_slice_bounds assign mu cost c hlocal
    _ = ∑ g : ↥(activeFactors F N), ∑ C : RegularComponent E g.1 N R,
        (budgets.unit g).toPrimeFlagBudgetFamily.weightedCost D1 C := by
      rw [Fintype.sum_sigma]
    _ ≤ flagMixed flag q D1 := sum_cost_le F N R flag q D1 hF hFp budgets
end
end ProximityPrize.SubmissionLower.ActiveSliceAssembly6807
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.ActualGenericChannel6807
open RCN057 (WeightBound)
open RCN086 RCN074
open scoped Classical BigOperators
open RCN002 RCN095 RCN134 RCN135 RCN136 RCN156 RCN207 RCN208 RCN244 RCN248
open RCN264 RCN313 RCN341 RCN344
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807 GenericSlicePoints6807
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 500000
variable {K I E A : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
  [Fintype A]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "w" => RCN326.w

theorem first_cut_for_generic_channel
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (old : A → FirstTailComponent S) (hold : Function.Injective old)
    (ell : MvPolynomial (Fin 3) Ω) (q : FlagDegree) (hell : PolynomialInFlag q ell)
    (projection : ∀ a, SeparableCoordinate Ω (CoordinateField Ω (old a).1))
    (hvalue : ∀ a, SeparableCoordinate.value Ω (CoordinateField Ω (old a).1) (projection a) =
      coordinateEvaluation Ω (old a).1 ell)
    (hdeg : flag.zOnly+flag.yz+flag.all < p)
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(q.zOnly+q.yz+q.all) < p)
    (Good : FirstTailComponent S → Prop) (hgood : ∀ a, Good (old a))
    (c m n : ℕ) (J V : FlagDegree) (hslice : ActiveSliceAssembly6807.SliceCharge S hproper Good
      (sliceEquation (E := E) ell) c m n J V) :
    c*(∑ a, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old a) *
      SeparableCoordinate.degree Ω (CoordinateField Ω (old a).1) (projection a)) ≤
      flagMixed flag q (m • J + n • V) := by
  classical
  let oldPrime := fun a => (old a).1
  letI : ∀ a : A, Algebra (RatFunc Ω) (CoordinateField Ω (oldPrime a)) :=
    fun a => (projection a).embedding.toRingHom.toAlgebra
  letI : ∀ a : A, IsScalarTower Ω (RatFunc Ω) (CoordinateField Ω (oldPrime a)) :=
    fun a => IsScalarTower.of_algebraMap_eq fun c => ((projection a).embedding.commutes c).symm
  letI : ∀ a : A, FiniteDimensional (RatFunc Ω) (CoordinateField Ω (oldPrime a)) :=
    fun a => (projection a).finite
  letI : ∀ a : A, Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (oldPrime a)) :=
    fun a => (projection a).separable
  let T := (a : A) × (CoordinateField Ω (oldPrime a) →ₐ[RatFunc Ω] E)
  let oldT := fun i : T => old i.1
  let embT := fun i : T => i.2.restrictScalars Ω
  let N := sliceEquation (E := E) ell
  have hprimes : Function.Injective oldPrime := by
    intro a b hh
    exact hold (Subtype.ext hh)
  have hpoints : Function.Injective
      (fun i : T => embeddingPoint (oldT i).1 (embT i)) :=
    commonBaseEmbeddingPoint_injective oldPrime hprimes
  have hcert (i : T) := GenericSlicePoints6807.embedding_point_certificate S.G
    (globalTailCut (polynomialEmbedding K) S.F (w+1))
    (RCN243.regularitySurface (polynomialEmbedding K) S.F) ell (old i.1)
    (hvalue i.1) i.2
  have hNq : PolynomialInFlag q N :=
    inFlag_sub_poly (inFlag_const q _) (inFlag_map _ hell)
  have hmass := ActiveSliceAssembly6807.first_cut_on_all_active_slices S hproper
    oldT embT hpoints N q hNq (fun i => (hcert i).2.1)
    (fun i => (hcert i).2.2.2.2) hdeg hmix Good (fun i => hgood i.1) c m n J V hslice
  have hsum := GenericSlicePoints6807.weighted_embedding_sum (E := E) oldPrime
    (fun a => localMultiplicity S (canonicalLocalDVRFamily S hproper) (old a))
  simpa only [oldT,embT,T,SeparableCoordinate.degree,oldPrime,hsum] using hmass

theorem first_cut_for_coordinate_channel
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (old : A → FirstTailComponent S) (hold : Function.Injective old)
    (ell : MvPolynomial (Fin 3) Ω) (q : FlagDegree) (hell : PolynomialInFlag q ell)
    (projection : ∀ a, Coordinate Ω (CoordinateField Ω (old a).1))
    (hvalue : ∀ a, coordinateValue Ω (CoordinateField Ω (old a).1) (projection a) =
      coordinateEvaluation Ω (old a).1 ell)
    (hdeg : flag.zOnly+flag.yz+flag.all < p)
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(q.zOnly+q.yz+q.all) < p)
    (Good : FirstTailComponent S → Prop) (hgood : ∀ a, Good (old a))
    (c m n : ℕ) (J V : FlagDegree) (hslice : ActiveSliceAssembly6807.SliceCharge S hproper Good
      (sliceEquation (E := E) ell) c m n J V) :
    c*(∑ a, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old a) *
      coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a)) ≤
      flagMixed flag q (m • J + n • V) := by
  classical
  let Alive : Set A := {a | ∃ c, projection a = Sum.inr c}
  let sep := fun a : Alive => Classical.choose a.2
  have hsep (a : Alive) : projection a.1 = Sum.inr (sep a) :=
    Classical.choose_spec a.2
  let old0 := fun a : Alive => old a.1
  have hi0 : Function.Injective old0 := by
    intro a b hh
    exact Subtype.ext (hold hh)
  have hv0 (a : Alive) :
      SeparableCoordinate.value Ω (CoordinateField Ω (old0 a).1) (sep a) =
        coordinateEvaluation Ω (old0 a).1 ell := by
    have hh := hvalue a.1
    rw [hsep a] at hh
    exact hh
  let weight := fun a => localMultiplicity S (canonicalLocalDVRFamily S hproper) (old a)
  have hsum : (∑ a, weight a * coordinateDegree Ω
      (CoordinateField Ω (old a).1) (projection a)) =
      ∑ a : Alive, weight a.1 * SeparableCoordinate.degree Ω
        (CoordinateField Ω (old0 a).1) (sep a) := by
    apply Finset.sum_congr_set Alive
      (fun a => weight a * coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a))
      (fun a => weight a.1 * SeparableCoordinate.degree Ω (CoordinateField Ω (old0 a).1) (sep a))
    · intro a ha
      simp only [hsep ⟨a,ha⟩,coordinateDegree,Sum.elim_inr,old0]
    · intro a ha
      cases hpj : projection a with
      | inl c => simp only [hpj,coordinateDegree,Sum.elim_inl,Nat.mul_zero]
      | inr c => exact (ha ⟨c,hpj⟩).elim
  have hb := first_cut_for_generic_channel (E := E) S hproper old0 hi0 ell q hell
    sep hv0 hdeg hmix Good (fun a => hgood a.1) c m n J V hslice
  rw [show (∑ a, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old a) *
      coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a)) =
      ∑ a : Alive, weight a.1 * SeparableCoordinate.degree Ω
        (CoordinateField Ω (old0 a).1) (sep a) from hsum]
  exact hb

end
end ProximityPrize.SubmissionLower.ActualGenericChannel6807
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.CommonLinearChannels6807
open scoped Classical BigOperators
open RCN002 RCN022 RCN030 RCN037 RCN038 RCN040 RCN042 RCN046 RCN093
open RCN095 RCN207 RCN237 RCN264 RCN340 RCN341 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 40000
variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
local notation "Poly" => MvPolynomial (Fin 3) Ω

def linearZ : Poly := MvPolynomial.X 2
def linearU (lam : Ω) : Poly := MvPolynomial.X 0 + MvPolynomial.C lam * MvPolynomial.X 2
def linearA (mu lam : Ω) : Poly := MvPolynomial.X 1 +
  MvPolynomial.C mu * MvPolynomial.X 0 + MvPolynomial.C (mu*lam) * MvPolynomial.X 2

private theorem inFlag_X (i : Fin 3) (q : FlagDegree)
    (hi : InFlag q (Finsupp.single i 1)) : PolynomialInFlag q (MvPolynomial.X i : Poly) := by
  intro e he
  have hh : e = Finsupp.single i 1 := by simpa only [MvPolynomial.support_X,Finset.mem_singleton] using he
  subst e
  exact hi
private theorem inFlag_add_poly {q : FlagDegree} {A B : Poly}
    (hA : PolynomialInFlag q A) (hB : PolynomialInFlag q B) : PolynomialInFlag q (A+B) := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hA e h
  · exact hB e h
private theorem inFlag_const_mul {q : FlagDegree} {A : Poly}
    (c : Ω) (hA : PolynomialInFlag q A) : PolynomialInFlag q (MvPolynomial.C c * A) := by
  intro e he
  rw [← MvPolynomial.smul_eq_C_mul] at he
  exact hA e (MvPolynomial.support_smul he)

theorem linearZ_in_flag : PolynomialInFlag unitZFlag (linearZ : Poly) := by
  exact inFlag_X 2 unitZFlag (by simp [InFlag,unitZFlag,Finsupp.single_apply])
theorem linearU_in_flag (lam : Ω) : PolynomialInFlag unitYZFlag (linearU lam) := by
  exact inFlag_add_poly
    (inFlag_X 0 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply]))
    (inFlag_const_mul lam (inFlag_X 2 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply])))
theorem linearA_in_flag (mu lam : Ω) : PolynomialInFlag unitAllFlag (linearA mu lam) := by
  exact inFlag_add_poly (inFlag_add_poly
    (inFlag_X 1 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))
    (inFlag_const_mul mu (inFlag_X 0 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))))
    (inFlag_const_mul (mu*lam) (inFlag_X 2 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply])))

theorem eval_linearU (P : Ideal Poly) [P.IsPrime] (lam : Ω) :
    coordinateEvaluation Ω P (linearU lam) = affineU Ω P lam := by
  rw [coordinateEvaluation_eq_aeval]
  simp only [linearU,affineU,Algebra.smul_def,map_add,map_mul,
    MvPolynomial.aeval_X,MvPolynomial.aeval_C]
theorem eval_linearA (P : Ideal Poly) [P.IsPrime] (mu lam : Ω) :
    coordinateEvaluation Ω P (linearA mu lam) = affineV Ω P mu (mu*lam) := by
  rw [coordinateEvaluation_eq_aeval]
  simp only [linearA,affineV,Algebra.smul_def,map_add,map_mul,
    MvPolynomial.aeval_X,MvPolynomial.aeval_C]

variable {G T H : MvPolynomial (Fin 3) Ω} {p q : FlagDegree}
  {base : ∀ C : RegularComponent Ω G T H, SeparableLiteralCoordinate C.1}

structure CommonLinearValues
    (unit : AdaptiveUnitProjectionFamily (Omega := Ω) (G := G) (T := T) (H := H) base p q) where
  lam : Ω
  mu : Ω
  yzValue : ∀ C : RegularComponent Ω G T H,
    coordinateValue Ω (CoordinateField Ω C.1) (unit.yzProjection C) = affineU Ω C.1 lam
  allValue : ∀ C : RegularComponent Ω G T H,
    coordinateValue Ω (CoordinateField Ω C.1) (unit.allProjection C) = affineV Ω C.1 mu (mu*lam)

theorem common_z_value (unit : AdaptiveUnitProjectionFamily base p q)
    (C : RegularComponent Ω G T H) :
    coordinateValue Ω (CoordinateField Ω C.1) (unit.zProjection C) =
      coordinateEvaluation Ω C.1 (linearZ : Poly) := unit.zValue C

theorem common_u_value (unit : AdaptiveUnitProjectionFamily base p q)
    (D : CommonLinearValues unit) (C : RegularComponent Ω G T H) :
    coordinateValue Ω (CoordinateField Ω C.1) (unit.yzProjection C) =
      coordinateEvaluation Ω C.1 (linearU D.lam) := by
  rw [eval_linearU]
  exact D.yzValue C

theorem common_a_value (unit : AdaptiveUnitProjectionFamily base p q)
    (D : CommonLinearValues unit) (C : RegularComponent Ω G T H) :
    coordinateValue Ω (CoordinateField Ω C.1) (unit.allProjection C) =
      coordinateEvaluation Ω C.1 (linearA D.mu D.lam) := by
  rw [eval_linearA]
  exact D.allValue C

def of_active_nested
    (base : ∀ C : RegularComponent Ω G T H, SeparableLiteralCoordinate C.1)
    (hactive : ∀ C : RegularComponent Ω G T H,
      KaehlerDifferential.D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 0) ≠ 0 ∨
      KaehlerDifferential.D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 2) ≠ 0)
    (hZ : ∀ C : RegularComponent Ω G T H, LiteralProjectionGate C 2)
    (hSderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (D : AdaptiveNestedProjectionDataActive (Omega := Ω) (G := G) (T := T) (H := H)
      base hactive hSderiv)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGsupport : G.support ⊆ flagSupport p) (hTsupport : T.support ⊆ flagSupport q) :
    CommonLinearValues (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper hGsupport hTsupport) where
  lam := D.lam
  mu := D.mu
  yzValue := by
    intro C
    change coordinateValue Ω (CoordinateField Ω C.1)
      (coordinateOfGate (affineU Ω C.1 D.lam) (D.uGate C)) = _
    exact coordinateOfGate_value _ _
  allValue := by
    intro C
    change (elementEmbedding Ω (CoordinateField Ω C.1)
      (affineV Ω C.1 D.mu (D.mu*D.lam)) (D.allAffineTranscendental C))
        (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X) = _
    exact elementEmbedding_variable Ω (CoordinateField Ω C.1) _ _

def of_congruent_cut {T' : Poly} (h : G ∣ T-T')
    {base' : ∀ C : RegularComponent Ω G T' H, SeparableLiteralCoordinate C.1}
    (U : AdaptiveUnitProjectionFamily base' p q)
    (newBase : ∀ C : RegularComponent Ω G T H, SeparableLiteralCoordinate C.1)
    (D : CommonLinearValues U) :
    CommonLinearValues (LocatorHybridTransportC2.unitFamilyOfCongruentCut h U newBase) where
  lam := D.lam
  mu := D.mu
  yzValue C := D.yzValue (RCN066.regularComponentEquiv h C)
  allValue C := D.allValue (RCN066.regularComponentEquiv h C)

end
end ProximityPrize.SubmissionLower.CommonLinearChannels6807
end MergedPart9
section MergedPart10
namespace ProximityPrize.SubmissionLower.JointBudgetArithmetic6807
open scoped BigOperators
open RCN095 RCN237
set_option autoImplicit false

variable {ι : Type*} [Fintype ι]

end ProximityPrize.SubmissionLower.JointBudgetArithmetic6807
end MergedPart10
section MergedPart11
namespace ProximityPrize.SubmissionLower.ThreeChannelJoint6807
open RCN057 (WeightBound)
open RCN086 RCN074
open scoped Classical BigOperators
open RCN002 RCN095 RCN135 RCN136 RCN156 RCN207 RCN244 RCN264 RCN313
open RCN341 RCN344 RCN046 RCN237
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807 CommonLinearChannels6807
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 500000
variable {K I E : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "w" => RCN326.w

end
end ProximityPrize.SubmissionLower.ThreeChannelJoint6807
end MergedPart11
section MergedPart12
namespace ProximityPrize.SubmissionLower.ReducedCommonLinear6807
open scoped Classical BigOperators
open RCN159 RCN263 RCN086 RCN327
open RCN135 RCN136 RCN264 RCN243 RCN095 RCN237 RCN198 RCN275 RCN244
open RCN334 RCN332 RCN336 RCN338 RCN199 RCN207 RCN313 RCN341 RCN030
open LocatorHybridTransportC2 CommonLinearChannels6807 BoundaryTailReduced
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {stageErrorCap a b s : ℕ}

def reduced_common
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hc : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hm : flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
    CommonLinearValues (reducedUnitFamily S hp hc hm) := by
  let A := reducedActiveGeometry S hp hc hm
  exact of_active_nested A.base A.hactive A.hZ
    (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
    S.irreducible_G (reducedFirstCut_proper S hp)
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff
      (reducedResidualAgreementFlag (support a b s) (w+1))
      (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))

def original_common
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hc : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hm : flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
    CommonLinearValues (unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
      (reducedUnitFamily S hp hc hm) (reducedBaseOrd S hp hc hm)) :=
  of_congruent_cut (ordinary_sub_reducedFirstCut_dvd S)
    (reducedUnitFamily S hp hc hm) (reducedBaseOrd S hp hc hm)
    (reduced_common S hp hc hm)

theorem original_common_lam_poly
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hc : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hm : flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
    (original_common S hp hc hm).lam ∈ Set.range (polynomialEmbedding K) :=
  (reducedActiveGeometry S hp hc hm).lam_poly

theorem original_common_mu_poly
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hc : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hm : flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
    (original_common S hp hc hm).mu ∈ Set.range (polynomialEmbedding K) :=
  (reducedActiveGeometry S hp hc hm).mu_poly

end
end ProximityPrize.SubmissionLower.ReducedCommonLinear6807
end MergedPart12
section MergedPart13
section Compact_SecondJetActiveMovingBudget6807

namespace ProximityPrize.SubmissionLower.SecondJetActiveMovingBudget6807
open scoped BigOperators
open RCN005 RCN006 RCN064 RCN002 RCN095 RCN187 RCN204 RCN207 RCN264 RCN341 RCN046 RCN199
open RCN344 (SeparableCoordinate coordinateDegree)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K : Type} [Field K] [IsAlgClosed K]

end
end ProximityPrize.SubmissionLower.SecondJetActiveMovingBudget6807

end Compact_SecondJetActiveMovingBudget6807

section Compact_SecondJetRetainedBudgets6807

namespace ProximityPrize.SubmissionLower.SecondJetRetainedBudgets6807
open scoped Classical BigOperators
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open RCN002 RCN136 RCN264 RCN341 RCN046 RCN095 RCN199
open RCN344 (coordinateDegree)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

end
end ProximityPrize.SubmissionLower.SecondJetRetainedBudgets6807

end Compact_SecondJetRetainedBudgets6807
end MergedPart13
section MergedPart14
namespace ProximityPrize.SubmissionLower.BoundaryTailJointBudget6807
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
open BoundaryTailAlgebra
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p] [CharP K p]
variable {stageErrorCap : ℕ}

def cellNormal (t y r : ℕ) : FlagDegree :=
  BoundaryTailAlgebra.normalFlag w r (y-r) (t-y)

theorem exists_provider_of_joint_curve_budget
    (t y r : Nat) (hr3 : 3 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (hchar : 2 * (w - 1) < p)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (tail1 : FlagDegree)
    (B : PrimeFlagBudgetFamily
      (G := S.G) (T := globalTailCut (polynomialEmbedding K) S.F
        (w + 1))
      (H := regularitySurface (polynomialEmbedding K) S.F) flag tail1)
    (base : ∀ C : FirstTailComponent S, SeparableLiteralCoordinate C.1)
    (budget : ∀ C : FirstTailComponent S,
      MovingPoleBudget C.1
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (hcost : ∀ C : FirstTailComponent S,
      (budget C).zCost = B.zCost C ∧ (budget C).yzCost = B.yzCost C ∧
        (budget C).allCost = B.allCost C)
    (active : Finset (FirstTailComponent S)) (divisorBound : ℕ)
    (hinactive : ∀ C : FirstTailComponent S, C ∉ active →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card = 0)
    (hjoint : (∑ C ∈ active,
      (localMultiplicity (loosenStageGeneral S)
        (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C *
        B.weightedCost (cellNormal t y r) C +
        65539 * (budget C).movingCost)) ≤ divisorBound)
    (hgate : stageErrorCap + 1 ≤ (cellNormal t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap + 1) * B.yzCost C)
    : Nonempty (HybridTailMultiplicityProvider
      (tailFlag1 := tail1)
      (tailFlag2 := cellNormal t y r) S divisorBound) := by
  classical
  have hry : r < y := by omega
  have hr2 : 2 ≤ r := by omega
  let S0 := loosenStageGeneral S
  let multiplicity : FirstTailComponent S → ℕ := fun C =>
    localMultiplicity S0 (canonicalLocalDVRFamily S0 hfirstProper) C
  have hone : ∀ C, 1 ≤ multiplicity C :=
    loosenStageGeneral_one_le_localMultiplicity S hfirstProper
  have hwcEq : ∀ (C : FirstTailComponent S) (f : FlagDegree),
      (budget C).weightedCost f = B.weightedCost f C := by
    intro C f
    obtain ⟨hz, hy', ha⟩ := hcost C
    simp only [MovingPoleBudget.weightedCost,
      PrimeFlagBudgetFamily.weightedCost, hz, hy', ha]
  have hscale : ∀ (m : ℕ) (f : FlagDegree) (C : FirstTailComponent S),
      B.weightedCost (m • f) C = m * B.weightedCost f C := by
    intro m f C
    simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly, nsmul_yz,
      nsmul_all]
    ring
  have hnormal : ∀ C : FirstTailComponent S,
      B.weightedCost (cellHybridCoordinateC1 t y r) C ≤
        B.weightedCost (cellNormal t y r) C := by
    intro C
    unfold cellNormal
    rw [normalFlag_eq_cell t y r hr3 hb]
    apply weightedCost_mono B C
    all_goals simp only [add_zOnly, add_yz, add_all, nsmul_zOnly,
      nsmul_yz, nsmul_all, unitAllFlag]
    all_goals omega
  let cost : FirstTailComponent S → ℕ := fun C =>
    multiplicity C * B.weightedCost (cellNormal t y r) C +
      65539 * (budget C).movingCost
  have hcost_pointwise : ∀ C, cost C ≤
      multiplicity C * B.weightedCost (cellNormal t y r) C +
        65539 * (budget C).movingCost := fun _ => le_rfl
  have hbound : ∀ C,
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤ cost C := by
    intro C
    have dichotomy := local_order_tail_dichotomy S0
      (canonicalLocalDVRFamily S0 hfirstProper) C hfirstProper
    rcases dichotomy.2 with hproper | htangentBranch
    · obtain ⟨delay, hdelay, hdelayMu, htail⟩ := hproper
      by_cases hm : 6 ≤ multiplicity C
      · have hzero : ∀ gamma ∈ componentSeeds (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (w + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C,
            MvPolynomial.aeval
              (selectedPoint (polynomialEmbedding K) S.selected gamma)
              (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) = 0 := by
          intro gamma hgamma
          have hGamma := componentSeeds_subset (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (w + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
          exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K)
            S.F S.selected gamma w (w + 1 + delay)
            (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
        have hflagMod : PolynomialInFlagMod C.1
            (multiplicity C • cellHybridCoordinateC1 t y r)
            (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
          refine ⟨globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay),
            laterTail_in_hybridFlagC1 t y r hr3 hry S delay
              (multiplicity C) hdelay hdelayMu hm, ?_⟩
          simp
        have hcount := component_secondTail_card_le_mod (Seed := K) B C Gamma
          (selectedPoint (polynomialEmbedding K) S.selected)
          (selectedPoint_injective (polynomialEmbedding K) S.selected)
          hflagMod htail hzero
        rw [hscale] at hcount
        exact hcount.trans ((Nat.mul_le_mul_left _ (hnormal C)).trans
          (Nat.le_add_right _ _))
      · have hdm : delay ≤ multiplicity C := hdelayMu
        have hcount := BoundaryTailComponent.component_moving_card_le_delay
          t y r hr3 hb hyt hchar S C (budget C) (base C) delay hdelay
          65539 (low_delay_factor delay (multiplicity C) hdm (by omega)) htail
        simp only [hwcEq] at hcount
        have hmono := normalFlag_delay_le_smul w (multiplicity C) delay r
          (y-r) (t-y) (by norm_num [w]) (hone C) hdm (by omega)
        have hcostle := weightedCost_mono B C hmono.1 hmono.2.1 hmono.2.2
        rw [hscale] at hcostle
        exact hcount.trans (Nat.add_le_add_right hcostle _)
    · have hcount := htangent C htangentBranch
      calc _ ≤ (stageErrorCap + 1) * B.yzCost C := hcount
        _ ≤ B.weightedCost (cellNormal t y r) C :=
          yzCost_mul_le_weightedCost B (cellNormal t y r) C
            (stageErrorCap + 1) hgate
        _ ≤ multiplicity C * B.weightedCost (cellNormal t y r) C := by
          simpa only [one_mul] using Nat.mul_le_mul_right
            (B.weightedCost (cellNormal t y r) C) (hone C)
        _ ≤ cost C := Nat.le_add_right _ _
  let activeCost : FirstTailComponent S → ℕ := fun C => if C ∈ active then cost C else 0
  have hactiveBound : ∀ C,
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤ activeCost C := by
    intro C
    by_cases hC : C ∈ active
    · simpa only [activeCost,if_pos hC] using hbound C
    · simp only [activeCost,if_neg hC,hinactive C hC,le_refl]
  have hsum : (∑ C, activeCost C) ≤ divisorBound := by
    have ha : (∑ C, activeCost C) = ∑ C ∈ active, cost C := by
      simp only [activeCost, Finset.sum_ite_mem, Finset.univ_inter]
    rw [ha]
    simpa only [cost, multiplicity, S0] using hjoint
  have providerDichotomy := loosenStageGeneral_dichotomy_with_tangent S
    hfirstProper B htangent
  exact ⟨{
    budgetFamily := B
    multiplicity := multiplicity
    cost := activeCost
    one_le_multiplicity := hone
    tangentYZGate := hgate
    cost_sum_le := hsum
    componentBound := hactiveBound
    dichotomy := providerDichotomy }⟩

end
end ProximityPrize.SubmissionLower.BoundaryTailJointBudget6807
end MergedPart14
section MergedPart15
namespace ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807
open RCN057 (WeightBound)
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
open BoundaryTailProvider
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p] [CharP K p]
variable {stageErrorCap : ℕ}

end
end ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807
end MergedPart15
