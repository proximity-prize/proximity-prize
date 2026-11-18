import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.MergedInfra6815_10
set_option Elab.async false
section MergedPart0
section Compact_MovingFiberScalar6815

namespace ProximityPrize.SubmissionLower.MovingFiberScalar6815
open scoped BigOperators
open ProximityPrize.Benchmark RCN279 RCN285
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

end ProximityPrize.SubmissionLower.MovingFiberScalar6815

end Compact_MovingFiberScalar6815

section Compact_MovingFiberScalarList6815

namespace ProximityPrize.SubmissionLower.MovingFiberScalarList6815Arithmetic
open ProximityPrize.Benchmark
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

end
end ProximityPrize.SubmissionLower.MovingFiberScalarList6815Arithmetic

namespace ProximityPrize.SubmissionLower.MovingFiberScalarList6815
open scoped Classical BigOperators
open ProximityPrize.Benchmark RCN319 RCN174 RCN231 RCN081 RCN167 RCN313 RCN136 RCN135 RCN138 RCN137 RCN267 RCN238 RCN243 RCN222 RCN290 RCN293 RCN286 RCN279 RCN282 RCN283 RCN001 RCN281 RCN019 RCN018
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

section
variable (K:Type) [Field K]

end

end
end ProximityPrize.SubmissionLower.MovingFiberScalarList6815

end Compact_MovingFiberScalarList6815
end MergedPart0
section MergedPart1
section Compact_MovingFiberProtocol6815

namespace ProximityPrize.SubmissionLower.MovingFiberProtocol6815Arithmetic
open ProximityPrize.Benchmark
open scoped NNReal
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

end
end ProximityPrize.SubmissionLower.MovingFiberProtocol6815Arithmetic

namespace ProximityPrize.SubmissionLower.MovingFiberProtocol6815
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem RCN018 RCN019 RCN284 RCN280
open scoped NNReal
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 5000000

end
end ProximityPrize.SubmissionLower.MovingFiberProtocol6815

end Compact_MovingFiberProtocol6815

section Compact_Protocol80850

namespace ProximityPrize.SubmissionLower.Lower80860.Protocol
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem RCN018 RCN019 RCN284 RCN280

end ProximityPrize.SubmissionLower.Lower80860.Protocol

end Compact_Protocol80850
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.MovingFiberSourceZeros6811
open scoped BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN095 RCN136 RCN187 RCN204 RCN207 RCN257 RCN313 RCN341
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000

private theorem pole_le_of_value_le {L : Type*} [Field L]
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x : L) (b : ℤ)
    (hb : 0 ≤ b) (hx : v x ≤ WithZero.exp b) : poleOrder v x ≤ b := by
  unfold poleOrder
  apply max_le hb
  by_cases hz : v x = 0
  · simpa only [hz,WithZero.log_zero] using hb
  · simpa only [WithZero.log_exp] using
      (WithZero.log_le_log hz WithZero.exp_ne_zero).mpr hx

theorem moving_difference_pole_le {E L : Type*} [Field E] [Field L]
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : E →+* L) (hc : ∀ c, v (coeff c) ≤ 1)
    (x : Fin 3 → L) (sigma : L) (Q U : MvPolynomial (Fin 3) E) (target : E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hU : PolynomialInFlag unitYZFlag U) :
    poleOrder v (coeff target - MvPolynomial.eval₂Hom coeff x Q -
      MvPolynomial.eval₂Hom coeff x U * sigma) ≤
      max (2*flagPole v x unitAllFlag)
        (flagPole v x unitYZFlag + poleOrder v sigma) := by
  let theta := max (2*flagPole v x unitAllFlag)
    (flagPole v x unitYZFlag + poleOrder v sigma)
  have htheta : 0 ≤ theta :=
    (mul_nonneg (by norm_num) (flagPole_nonneg _ _ _)).trans (le_max_left _ _)
  apply pole_le_of_value_le v _ theta htheta
  apply v.map_sub_le
  · have hv := valuation_eval_le_flag v coeff hc x (2 • unitAllFlag)
      (MvPolynomial.C target-Q) (inFlag_sub_poly (inFlag_const _ _) hQ)
    have he : flagPole v x (2 • unitAllFlag) = 2*flagPole v x unitAllFlag := by
      simp only [flagPole,nsmul_zOnly,nsmul_yz,nsmul_all,unitAllFlag]
      norm_num
    simp only [map_sub,MvPolynomial.eval₂Hom_C,he] at hv
    exact hv.trans (WithZero.exp_le_exp.mpr (le_max_left _ _))
  · have hu := valuation_eval_le_flag v coeff hc x unitYZFlag U hU
    have hs : v sigma ≤ WithZero.exp (poleOrder v sigma) :=
      WithZero.le_exp_of_log_le (le_max_right _ _)
    rw [map_mul]
    exact (mul_le_mul' hu hs).trans (by
      rw [← WithZero.exp_add]
      exact WithZero.exp_le_exp.mpr (le_max_right _ _))

variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

theorem source_moving_pole_mass
    (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base : SeparableLiteralCoordinate C)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hF : surfaceMap phi F ∈ C)
    (hH : surfaceMap phi (polyH K F) ∉ C)
    (hlead : surfaceMap phi (asS P).leadingCoeff ∉ C)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (Q A : MvPolynomial (Fin 3) E) (target : E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : PolynomialInFlag unitYZFlag A)
    (CV : ℕ)
    (hbudget : ∀ W : Finset (Place E (CoordinateField E C)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E C)
        (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0)) ≤ (CV : ℤ))
    (W : Finset (Place E (CoordinateField E C))) :
    ((k+1 : ℕ) : ℤ) * (∑ nu ∈ W, poleOrder nu.val
      (algebraMap E (CoordinateField E C) target - coordinateEvaluation E C Q -
        coordinateEvaluation E C A * RCN064.movingRatio C
          (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))) ≤ (CV : ℤ) := by
  letI := polynomialBaseAlgebra E C base.index
  letI := rationalBaseAlgebra E C base.index base.transcendental
  letI := polynomialBaseScalarTower E C base.index
  letI := polynomialRationalScalarTower E C base.index base.transcendental
  letI := rationalBaseScalarTower E C base.index base.transcendental
  letI : FiniteDimensional (RatFunc E) (CoordinateField E C) := base.finite
  letI : Algebra.IsSeparable (RatFunc E) (CoordinateField E C) := base.separable
  have hdeg := SecondJetComponentRoots.degree_retained phi C P hlead
  have hroot := SecondJetComponentRoots.roots_retained phi C P F s k hS
    hF hH hlead hdiv h2 hfact
  have hdegree : n0 ≤ (SecondJetComponentRoots.componentPolynomial phi C P).natDegree := by
    rw [hdeg.2]
    exact hn
  have hs := SecondJetRelaxedFlag.moving_bound
    (MvPolynomial.map (phi.comp Polynomial.C) P) (phi Polynomial.X)
    B U T (k+1) n0 hBU hUT hdn hB
    (SecondJetSurfaceMap.mapped_support_bounds _ P B U T hP)
    (coordinate E C) (SecondJetComponentRoots.componentPolynomial phi C P)
    (SecondJetComponentRoots.coefficients phi C P) hdeg.1 hdegree
    (RCN064.movingRatio C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F))/2) hroot (CV : ℤ) hbudget W
  simp only [SecondJetPoleScaling.pole_half _ h2] at hs
  apply le_trans _ hs
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _)
  apply Finset.sum_le_sum
  intro nu _
  have hh := moving_difference_pole_le nu.val (algebraMap E (CoordinateField E C))
    (RCN344.constant_value_le_one E (CoordinateField E C) nu) (coordinate E C)
    (RCN064.movingRatio C (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))
    Q A target hQ hA
  simpa only [coordinateEvaluation_eq_aeval,MvPolynomial.aeval_eq_eval₂Hom] using hh

theorem finite_moving_zeros_of_source
    (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base : SeparableLiteralCoordinate C)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hF : surfaceMap phi F ∈ C)
    (hH : surfaceMap phi (polyH K F) ∉ C)
    (hlead : surfaceMap phi (asS P).leadingCoeff ∉ C)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (Q A : MvPolynomial (Fin 3) E) (target : E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : PolynomialInFlag unitYZFlag A)
    (hproper : movingEquation (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F)) Q A target ∉ C)
    (CV : ℕ)
    (hbudget : ∀ W : Finset (Place E (CoordinateField E C)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E C)
        (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0)) ≤ (CV : ℤ)) :
    RCN271.FiniteRegularZeroSetBound C (surfaceMap phi (polyH K F))
      (movingEquation (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target) (CV/(k+1)) := by
  let H := surfaceMap phi (polyH K F)
  let G := surfaceMap phi (polyG K F)
  have hHne : coordinateEvaluation E C H ≠ 0 := by
    intro hz
    exact hH ((SecondJetComponentRoots.evaluation_zero_iff C _).mp hz)
  have hnorm : MvPolynomial.aeval (coordinate E C) (movingEquation H G Q A target) /
      MvPolynomial.aeval (coordinate E C) H =
      algebraMap E (CoordinateField E C) target - coordinateEvaluation E C Q -
        coordinateEvaluation E C A * RCN064.movingRatio C H G := by
    simp only [movingEquation,map_sub,map_mul,MvPolynomial.aeval_C,
      RCN064.movingRatio,coordinateEvaluation_eq_aeval] at *
    field_simp
  apply finite_regular_zero_bound_of_separator E C base H _ 1 (CV/(k+1)) hproper hH
  intro W
  have hsource := source_moving_pole_mass phi F C base P B U T s k n0
    hS hP hBU hUT hdn hB hn hF hH hlead hdiv h2 hfact Q A target hQ hA CV hbudget W
  simp only [pow_one]
  change (∑ nu ∈ W, poleOrder nu.val
    (MvPolynomial.aeval (coordinate E C) (movingEquation H G Q A target) /
      MvPolynomial.aeval (coordinate E C) H)) ≤ ((CV/(k+1) : ℕ) : ℤ)
  simp_rw [hnorm]
  rw [Int.natCast_ediv]
  apply (Int.le_ediv_iff_mul_le (by positivity : (0 : ℤ) < ((k+1 : ℕ) : ℤ))).mpr
  simpa only [H,G,mul_comm] using hsource

end
end ProximityPrize.SubmissionLower.MovingFiberSourceZeros6811
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingFiberIsolatedZeros6811
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN039 RCN046 RCN084 RCN095
open RCN114 RCN136 RCN187 RCN204 RCN207 RCN237 RCN257 RCN264 RCN271 RCN313 RCN340 RCN341
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open MovingFiberSourceZeros6811
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]
local instance : DecidableEq E := Classical.decEq E
local notation "Poly3" => MvPolynomial (Fin 3) E

private theorem pure_flag_poles
    {G N R : Poly3} {p q : FlagDegree}
    {base : ∀ C : RegularComponent E G N R, SeparableLiteralCoordinate C.1}
    (U : AdaptiveUnitPoleBudget base p q) (C : RegularComponent E G N R)
    (V : FlagDegree) (W : Finset (Place E (CoordinateField E C.1))) :
    (∑ nu ∈ W, flagPole nu.val (coordinate E C.1) V) ≤
      (U.toPrimeFlagBudgetFamily.weightedCost V C : ℤ) := by
  have hz := U.zPole C W
  have hy := U.yzPole C W
  have ha := U.allPole C W
  simp only [exponentSetPoleWeight_unitZ] at hz
  simp only [exponentSetPoleWeight_unitYZ] at hy
  simp only [exponentSetPoleWeight_unitAll] at ha
  have h := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg V.zOnly))
    (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg V.yz)))
    (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg V.all))
  simpa only [flagPole,Finset.sum_add_distrib,← Finset.mul_sum,
    PrimeFlagBudgetFamily.weightedCost,AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily,
    Nat.cast_add,Nat.cast_mul] using h

theorem isolated_moving_points_scaled
    (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (carrier N : Poly3) (p q : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier) (hNflag : PolynomialInFlag q N)
    (c : ℕ) [CharP E c]
    (hdeg : p.zOnly+p.yz+p.all < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (Q A : Poly3) (target : E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : PolynomialInFlag unitYZFlag A)
    (points : Finset (Fin 3 → E))
    (hpoints : ∀ x ∈ points,
      MvPolynomial.eval x carrier = 0 ∧ MvPolynomial.eval x N = 0 ∧
      MvPolynomial.eval x (movingEquation (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target) = 0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)) ≠ 0 ∧
      MvPolynomial.eval x (surfaceMap phi (asS P).leadingCoeff) ≠ 0 ∧
      MvPolynomial.eval x (MvPolynomial.pderiv (1 : Fin 3) carrier) ≠ 0)
    (hisolated : ∀ x ∈ points, IsolatedPoint carrier N
      (movingEquation (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target) x) :
    (k+1)*points.card ≤
      flagMixed p q (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0) := by
  classical
  let H := surfaceMap phi (polyH K F)
  let L := surfaceMap phi (asS P).leadingCoeff
  let R := H*L
  let M := movingEquation H (surfaceMap phi (polyG K F)) Q A target
  let V := SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0
  have hR : ∀ x ∈ points, MvPolynomial.eval x R ≠ 0 := by
    intro x hx
    simpa only [R,map_mul] using mul_ne_zero (hpoints x hx).2.2.2.1 (hpoints x hx).2.2.2.2.1
  have hcover : ∀ x ∈ points, ∃ g : ↥(activeFactors carrier N), MvPolynomial.eval x g.1 = 0 := by
    intro x hx
    exact exists_active_factor_of_isolated carrier N M R hcarrier x
      (hpoints x hx).1 (hpoints x hx).2.2.1 (hR x hx)
      (hpoints x hx).2.2.2.2.2 (hisolated x hx)
  obtain ⟨base,hY,hZ⟩ := exists_small_projection_data carrier N R hcarrier p q hflag hNflag c hdeg hmix
  let S (g : ↥(activeFactors carrier N)) : Finset (Fin 3 → E) :=
    points.filter (fun (x : Fin 3 → E) => MvPolynomial.eval x g.1 = (0:E))
  have hcoverage : points ⊆ Finset.univ.biUnion S := by
    intro x hx
    obtain ⟨g,hg⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hx,hg⟩⟩
  have hcount (g : ↥(activeFactors carrier N)) :
      (k+1)*(S g).card ≤ flagMixed (exactFlag g.1) q V := by
    have hg := activeFactors_spec carrier N g
    obtain ⟨unit⟩ := exists_adaptiveUnitProjectionFamily_of_nested (exactFlag g.1) q
      (base g) (hY g) (hZ g) hg.2.2.2 hg.1 hg.2.2.1
      ((support_subset_flagSupport_iff _ _).mpr (polynomialIn_exactFlag g.1))
      ((support_subset_flagSupport_iff _ _).mpr hNflag)
    let budget := unit.toPrimeFlagBudgetFamily
    have hcard := card_le_sum_componentSeeds E g.1 N R (S g) id
      (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun x hx => (hpoints x (Finset.mem_filter.mp hx).1).2.1)
      (fun x hx => hR x (Finset.mem_filter.mp hx).1)
    have hlocal (C : RegularComponent E g.1 N R) :
        (k+1)*(componentSeeds E g.1 N R (S g) id C).card ≤ budget.weightedCost V C := by
      by_cases he : (componentSeeds E g.1 N R (S g) id C).Nonempty
      · obtain ⟨x,hx⟩ := he
        have hxS := componentSeeds_subset E g.1 N R (S g) id C hx
        have hxpoints := (Finset.mem_filter.mp hxS).1
        have hxC := componentSeeds_on_prime E g.1 N R (S g) id C x hx
        have hcar : carrier ∈ C.1 := C.1.mem_of_dvd hg.2.1 (regularComponent_G_mem E g.1 N R C)
        have hF : surfaceMap phi F ∈ C.1 := C.1.mem_of_dvd hcarrierF hcar
        have hH : H ∉ C.1 := by
          intro hh
          exact regularComponent_H_not_mem E g.1 N R C (C.1.mul_mem_right L hh)
        have hL : L ∉ C.1 := by
          intro hl
          exact regularComponent_H_not_mem E g.1 N R C (C.1.mul_mem_left H hl)
        have hproper : M ∉ C.1 := hisolated x hxpoints C.1 inferInstance
          (regularComponent_ne_point E g.1 N R C) hxC hcar (regularComponent_T_mem E g.1 N R C)
        have hb := finite_moving_zeros_of_source phi F C.1 (base g C) P B U T s k n0
          hS hP hBU hUT hdn hB hn hF hH hL hdiv h2 hfact Q A target hQ hA hproper
          (budget.weightedCost V C) (fun W => pure_flag_poles unit.toAdaptiveUnitPoleBudget C V W)
        have hc := hb (componentSeeds E g.1 N R (S g) id C)
          (fun y hy => componentSeeds_on_prime E g.1 N R (S g) id C y hy)
          (fun y hy => (hpoints y (Finset.mem_filter.mp
            (componentSeeds_subset E g.1 N R (S g) id C hy)).1).2.2.2.1)
          (fun y hy => (hpoints y (Finset.mem_filter.mp
            (componentSeeds_subset E g.1 N R (S g) id C hy)).1).2.2.1)
        exact (Nat.mul_le_mul_left (k+1) hc).trans (by
          simpa only [Nat.mul_comm] using Nat.div_mul_le_self (budget.weightedCost V C) (k+1))
      · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.mul_zero,Nat.zero_le]
    calc
      (k+1)*(S g).card ≤ (k+1)*∑ C : RegularComponent E g.1 N R,
          (componentSeeds E g.1 N R (S g) id C).card := Nat.mul_le_mul_left _ hcard
      _ = ∑ C : RegularComponent E g.1 N R,
          (k+1)*(componentSeeds E g.1 N R (S g) id C).card := Finset.mul_sum _ _ _
      _ ≤ ∑ C : RegularComponent E g.1 N R, budget.weightedCost V C := Finset.sum_le_sum (fun C _ => hlocal C)
      _ ≤ _ := budget.sum_weightedCost_le V
  have hc := (Finset.card_le_card hcoverage).trans Finset.card_biUnion_le
  calc
    (k+1)*points.card ≤ (k+1)*∑ g : ↥(activeFactors carrier N), (S g).card := Nat.mul_le_mul_left _ hc
    _ = ∑ g : ↥(activeFactors carrier N), (k+1)*(S g).card := Finset.mul_sum _ _ _
    _ ≤ ∑ g : ↥(activeFactors carrier N), flagMixed (exactFlag g.1) q V := Finset.sum_le_sum (fun g _ => hcount g)
    _ ≤ _ := activeFactors_mixed_sum_le carrier N hcarrier p q V hflag

end
end ProximityPrize.SubmissionLower.MovingFiberIsolatedZeros6811
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.MovingFiberProjection6811
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN072 RCN076 RCN084 RCN095 RCN134 RCN136
open RCN207 RCN208 RCN237 RCN264 RCN313 RCN341 RCN344
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open MovingFiberIsolatedZeros6811
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000

variable {K Ω E : Type} [Field K] [Field Ω] [Field E] [IsAlgClosed Ω] [IsAlgClosed E]
  [Algebra Ω E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E]

omit [IsAlgClosed Ω] [IsAlgClosed E] [Algebra (RatFunc Ω) E]
  [IsScalarTower Ω (RatFunc Ω) E] in
private theorem scalar_surface_MovingFiberProjection6811 (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K) :
    scalarPolynomialMap Ω E (surfaceMap phi F) =
      surfaceMap ((algebraMap Ω E).comp phi) F := by
  simp only [scalarPolynomialMap,surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]

private theorem filtered_zero {R : Type*} [CommRing R] (F H G : R) :
    filteredCut 0 (fun _ : Fin 1 => F) H G = F := by
  simp [filteredCut]

omit [IsAlgClosed Ω] in
theorem sum_separable_projection_degrees {ι : Type} [Fintype ι]
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (carrier : MvPolynomial (Fin 3) Ω) (p q : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (ell : MvPolynomial (Fin 3) Ω) (hell : PolynomialInFlag q ell)
    (c : ℕ) [CharP E c]
    (hdeg : p.zOnly+p.yz+p.all < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (Q A : MvPolynomial (Fin 3) Ω) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : PolynomialInFlag unitYZFlag A)
    (old : ι → RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*surfaceMap phi (asS P).leadingCoeff))
    (hold : Function.Injective old)
    (projection : ∀ i, SeparableCoordinate Ω (CoordinateField Ω (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Ω (CoordinateField Ω (old i).1) (projection i) =
      coordinateEvaluation Ω (old i).1 ell) :
    (k+1)*(∑ i, SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i)) ≤
      flagMixed p q (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0) := by
  classical
  let H := surfaceMap phi (polyH K F)
  let G := surfaceMap phi (polyG K F)
  let L := surfaceMap phi (asS P).leadingCoeff
  let R := H*L
  let M := movingEquation H G Q A target
  have hderiv : H ∈ Ideal.span
      ({carrier,MvPolynomial.pderiv (1 : Fin 3) carrier} : Set (MvPolynomial (Fin 3) Ω)) := by
    let carrierIdeal := Ideal.span
      ({carrier,MvPolynomial.pderiv (1 : Fin 3) carrier} : Set (MvPolynomial (Fin 3) Ω))
    have hcar : carrier ∈ carrierIdeal := Ideal.subset_span (by simp)
    have hdc : MvPolynomial.pderiv (1 : Fin 3) carrier ∈ carrierIdeal := Ideal.subset_span (by simp)
    obtain ⟨b,hb⟩ := hcarrierF
    change surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F) ∈ carrierIdeal
    rw [← RCN267.surfaceMap_pderiv_R,hb,MvPolynomial.pderiv_mul]
    exact carrierIdeal.add_mem (carrierIdeal.mul_mem_right b hdc)
      (carrierIdeal.mul_mem_right (MvPolynomial.pderiv (1 : Fin 3) b) hcar)
  let mu := scalarPolynomialMap Ω E
  let phiE := (algebraMap Ω E).comp phi
  let prime := fun i => (old i).1
  letI : ∀ i, Algebra (RatFunc Ω) (CoordinateField Ω (prime i)) :=
    fun i => (projection i).embedding.toRingHom.toAlgebra
  letI : ∀ i, IsScalarTower Ω (RatFunc Ω) (CoordinateField Ω (prime i)) :=
    fun i => IsScalarTower.of_algebraMap_eq (fun a => ((projection i).embedding.commutes a).symm)
  letI : ∀ i, FiniteDimensional (RatFunc Ω) (CoordinateField Ω (prime i)) := fun i => (projection i).finite
  letI : ∀ i, Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (prime i)) := fun i => (projection i).separable
  let points := genericFiberPoints (B := RatFunc Ω) (L := E) prime
  let t := algebraMap (RatFunc Ω) E (RCN202.rationalVariable Ω)
  let N := MvPolynomial.C t-mu ell
  have hprime : Function.Injective prime := by
    intro i j hij
    exact hold (Subtype.ext hij)
  have hNflag : PolynomialInFlag q N :=
    inFlag_sub_poly (inFlag_const _ _) (inFlag_map _ hell)
  have hmuM : mu M = movingEquation (surfaceMap phiE (polyH K F))
      (surfaceMap phiE (polyG K F)) (mu Q) (mu A) (algebraMap Ω E target) := by
    simp only [M,movingEquation,map_sub,map_mul]
    rw [show mu H = surfaceMap phiE (polyH K F) from scalar_surface_MovingFiberProjection6811 phi _,
      show mu G = surfaceMap phiE (polyG K F) from scalar_surface_MovingFiberProjection6811 phi _]
    simp only [mu,scalarPolynomialMap,MvPolynomial.map_C]
  have certificate (i : ι) (f : CoordinateField Ω (prime i) →ₐ[RatFunc Ω] E) :
      let x := embeddingPoint (prime i) (f.restrictScalars Ω)
      MvPolynomial.eval x (mu carrier) = 0 ∧ MvPolynomial.eval x N = 0 ∧
      MvPolynomial.eval x (mu M) = 0 ∧ MvPolynomial.eval x (mu R) ≠ 0 ∧
      IsolatedPoint (mu carrier) N (mu M) x := by
    let C0 : RegularComponent Ω carrier (filteredCut 0 (fun _ : Fin 1 => M) R 0) R :=
      ⟨(old i).1,by simpa only [filtered_zero] using (old i).2⟩
    letI : Algebra (RatFunc Ω) (CoordinateField Ω C0.1) :=
      (projection i).embedding.toRingHom.toAlgebra
    have hj : algebraMap (RatFunc Ω) (CoordinateField Ω C0.1) (RCN202.rationalVariable Ω) =
        movingValue C0.1 R 0 ell 1 := by
      change SeparableCoordinate.value Ω (CoordinateField Ω (old i).1) (projection i) = _
      simpa only [movingValue,map_one,map_zero,mul_zero,zero_div,add_zero] using hvalue i
    have hone : (1 : MvPolynomial (Fin 3) Ω) ∉ C0.1 := by
      intro h
      have hz := (SecondJetComponentRoots.evaluation_zero_iff C0.1 1).mpr h
      exact one_ne_zero (by simpa only [map_one] using hz)
    have hc := RCN202.embedding_point_certificate carrier R 0 ell 1 0
      (fun _ : Fin 1 => M) C0 hj hone f
    have hc' :
        let x := embeddingPoint (prime i) (f.restrictScalars Ω)
        MvPolynomial.eval x (mu carrier) = 0 ∧ MvPolynomial.eval x (mu R*N) = 0 ∧
        MvPolynomial.eval x (mu M) = 0 ∧ MvPolynomial.eval x (mu R) ≠ 0 ∧
        IsolatedPoint (mu carrier) (mu R*N) (mu M) x := by
      simpa only [map_zero,map_one,movingEquation,eliminatedCut,filtered_zero,
        mul_zero,sub_zero,mul_one,MvPolynomial.aeval_eq_eval] using hc
    dsimp only at hc' ⊢
    have hn : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω)) N = 0 :=
      (mul_eq_zero.mp (by simpa only [map_mul] using hc'.2.1)).resolve_left hc'.2.2.2.1
    refine ⟨hc'.1,hn,hc'.2.2.1,hc'.2.2.2.1,?_⟩
    intro D hD hnot hp hF hN
    exact hc'.2.2.2.2 D hD hnot hp hF (D.mul_mem_left (mu R) hN)
  have hpoints : ∀ x ∈ points,
      MvPolynomial.eval x (mu carrier) = 0 ∧ MvPolynomial.eval x N = 0 ∧
      MvPolynomial.eval x (mu M) = 0 ∧
      MvPolynomial.eval x (surfaceMap phiE (polyH K F)) ≠ 0 ∧
      MvPolynomial.eval x (surfaceMap phiE (asS P).leadingCoeff) ≠ 0 ∧
      MvPolynomial.eval x (MvPolynomial.pderiv (1 : Fin 3) (mu carrier)) ≠ 0 := by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩ := Finset.mem_image.mp hx
    have hc := certificate i f
    have hRne := hc.2.2.2.1
    have hHL : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω)) (mu H) ≠ 0 ∧
        MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω)) (mu L) ≠ 0 := by
      simpa only [R,map_mul,mul_ne_zero_iff] using hRne
    have hHne : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω))
        (surfaceMap phiE (polyH K F)) ≠ 0 := by simpa only [H,mu,scalar_surface_MovingFiberProjection6811,phiE] using hHL.1
    have hLne : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω))
        (surfaceMap phiE (asS P).leadingCoeff) ≠ 0 := by simpa only [L,mu,scalar_surface_MovingFiberProjection6811,phiE] using hHL.2
    have hd := map_pderiv_ne_zero_of_mem_span (MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω)))
      (mu carrier) (mu H) (scalar_derivative_span carrier H hderiv) hc.1 hHL.1
    exact ⟨hc.1,hc.2.1,hc.2.2.1,hHne,hLne,hd⟩
  have hiso : ∀ x ∈ points, IsolatedPoint (mu carrier) N (mu M) x := by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩ := Finset.mem_image.mp hx
    exact (certificate i f).2.2.2.2
  have hcar : mu carrier ∣ surfaceMap phiE F := by
    simpa only [mu,scalar_surface_MovingFiberProjection6811,phiE] using map_dvd mu hcarrierF
  have hmu : Function.Injective mu := MvPolynomial.map_injective (algebraMap Ω E) (algebraMap Ω E).injective
  have hne : mu carrier ≠ 0 := fun hz => hcarrier (hmu (by simpa only [map_zero] using hz))
  rw [hmuM] at hpoints hiso
  have hc := isolated_moving_points_scaled phiE F (mu carrier) N p q hne hcar
    (inFlag_map _ hflag) hNflag c hdeg hmix P B U T s k n0 hS hP hBU hUT hdn hB hn hdiv h2 hfact
    (mu Q) (mu A) (algebraMap Ω E target) (inFlag_map _ hQ) (inFlag_map _ hA) points hpoints hiso
  have hcard := genericFiberPoints_card (B := RatFunc Ω) (L := E) prime hprime
  simpa only [points,hcard,SeparableCoordinate.degree,prime] using hc

omit [IsAlgClosed Ω] in
theorem sum_coordinate_projection_degrees {ι : Type} [Fintype ι]
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (carrier : MvPolynomial (Fin 3) Ω) (p q : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (ell : MvPolynomial (Fin 3) Ω) (hell : PolynomialInFlag q ell)
    (c : ℕ) [CharP E c]
    (hdeg : p.zOnly+p.yz+p.all < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (Q A : MvPolynomial (Fin 3) Ω) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : PolynomialInFlag unitYZFlag A)
    (old : ι → RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*surfaceMap phi (asS P).leadingCoeff))
    (hold : Function.Injective old)
    (projection : ∀ i, Coordinate Ω (CoordinateField Ω (old i).1))
    (hvalue : ∀ i, coordinateValue Ω (CoordinateField Ω (old i).1) (projection i) =
      coordinateEvaluation Ω (old i).1 ell) :
    (k+1)*(∑ i, coordinateDegree Ω (CoordinateField Ω (old i).1) (projection i)) ≤
      flagMixed p q (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0) := by
  classical
  let Alive : Set ι := {i | ∃ C, projection i = Sum.inr C}
  let sep := fun i : Alive => Classical.choose i.2
  have hsep (i : Alive) : projection i.1 = Sum.inr (sep i) := Classical.choose_spec i.2
  let old0 := fun i : Alive => old i.1
  have hi0 : Function.Injective old0 := by
    intro i j h
    exact Subtype.ext (hold h)
  have hv0 (i : Alive) :
      SeparableCoordinate.value Ω (CoordinateField Ω (old0 i).1) (sep i) =
        coordinateEvaluation Ω (old0 i).1 ell := by
    have h := hvalue i.1
    rw [hsep i] at h
    exact h
  have hsum : (∑ i, coordinateDegree Ω (CoordinateField Ω (old i).1) (projection i)) =
      ∑ i : Alive, SeparableCoordinate.degree Ω (CoordinateField Ω (old0 i).1) (sep i) := by
    apply Finset.sum_congr_set Alive
      (fun i => coordinateDegree Ω (CoordinateField Ω (old i).1) (projection i))
      (fun i => SeparableCoordinate.degree Ω (CoordinateField Ω (old0 i).1) (sep i))
    · intro i hi
      simp only [hsep ⟨i,hi⟩,coordinateDegree,Sum.elim_inr,old0]
    · intro i hi
      cases hp : projection i with
      | inl C => simp only [coordinateDegree,Sum.elim_inl]
      | inr C => exact (hi ⟨C,hp⟩).elim
  rw [hsum]
  exact sum_separable_projection_degrees (E := E) phi F carrier p q hcarrier hcarrierF hflag ell hell
    c hdeg hmix P B U T s k n0 hS hP hBU hUT hdn hB hn hdiv h2 hfact Q A target hQ hA
    old0 hi0 sep hv0

end
end ProximityPrize.SubmissionLower.MovingFiberProjection6811
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.MovingFiberNativeBudget6811
open scoped Classical BigOperators
open RCN002 RCN022 RCN037 RCN039 RCN042 RCN046 RCN071 RCN076 RCN084 RCN093 RCN095 RCN135 RCN136 RCN207
open RCN237 RCN264 RCN313 RCN340 RCN341 RCN344
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open MovingFiberProjection6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 40000
variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]

local notation "Poly3" => MvPolynomial (Fin 3) Ω

def linearZ : Poly3 := MvPolynomial.X 2
def linearU (a : Ω) : Poly3 := MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 2
def linearA (b a : Ω) : Poly3 := MvPolynomial.X 1 + MvPolynomial.C b * MvPolynomial.X 0 +
  MvPolynomial.C (b*a) * MvPolynomial.X 2

omit [IsAlgClosed Ω] in
private theorem flag_X (i : Fin 3) (p : FlagDegree)
    (hi : InFlag p (Finsupp.single i 1)) : PolynomialInFlag p (MvPolynomial.X i : Poly3) := by
  intro e he
  have : e = Finsupp.single i 1 := by simpa only [MvPolynomial.support_X,Finset.mem_singleton] using he
  subst e
  exact hi
omit [IsAlgClosed Ω] in
private theorem flag_add {p : FlagDegree} {A B : Poly3}
    (hA : PolynomialInFlag p A) (hB : PolynomialInFlag p B) : PolynomialInFlag p (A+B) := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hA e h
  · exact hB e h
omit [IsAlgClosed Ω] in
private theorem flag_scale {p : FlagDegree} {A : Poly3} (c : Ω)
    (hA : PolynomialInFlag p A) : PolynomialInFlag p (MvPolynomial.C c*A) := by
  intro e he
  rw [← MvPolynomial.smul_eq_C_mul] at he
  exact hA e (MvPolynomial.support_smul he)

theorem linearZ_flag : PolynomialInFlag unitZFlag (linearZ : Poly3) :=
  flag_X 2 unitZFlag (by simp [InFlag,unitZFlag,Finsupp.single_apply])
theorem linearU_flag (a : Ω) : PolynomialInFlag unitYZFlag (linearU a) :=
  flag_add (flag_X 0 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply]))
    (flag_scale a (flag_X 2 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply])))
theorem linearA_flag (b a : Ω) : PolynomialInFlag unitAllFlag (linearA b a) :=
  flag_add (flag_add (flag_X 1 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))
    (flag_scale b (flag_X 0 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))))
    (flag_scale (b*a) (flag_X 2 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply])))

theorem exists_common_native_unit {G N R : Poly3} (p q : FlagDegree)
    (base : ∀ C : RegularComponent Ω G N R, SeparableLiteralCoordinate C.1)
    (hY : ∀ C : RegularComponent Ω G N R, LiteralProjectionGate C 0)
    (hZ : ∀ C : RegularComponent Ω G N R, LiteralProjectionGate C 2)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (hG : Irreducible G) (hproper : ¬ G ∣ N)
    (hGflag : PolynomialInFlag p G) (hNflag : PolynomialInFlag q N) :
    ∃ (unit : AdaptiveUnitProjectionFamily base p q) (a b : Ω),
      (∀ C : RegularComponent Ω G N R, coordinateValue Ω (CoordinateField Ω C.1) (unit.zProjection C) =
        coordinateEvaluation Ω C.1 linearZ) ∧
      (∀ C : RegularComponent Ω G N R, coordinateValue Ω (CoordinateField Ω C.1) (unit.yzProjection C) =
        coordinateEvaluation Ω C.1 (linearU a)) ∧
      (∀ C : RegularComponent Ω G N R, coordinateValue Ω (CoordinateField Ω C.1) (unit.allProjection C) =
        coordinateEvaluation Ω C.1 (linearA b a)) := by
  obtain ⟨D⟩ := exists_adaptiveNestedProjectionData base hY hZ hderiv
  let unit := adaptiveUnitProjectionFamily_of_nested p q base hY hZ hderiv D hG hproper
    ((support_subset_flagSupport_iff _ _).mpr hGflag) ((support_subset_flagSupport_iff _ _).mpr hNflag)
  refine ⟨unit,D.lam,D.mu,?_,?_,?_⟩
  · intro C
    exact unit.zValue C
  · intro C
    have hv : coordinateValue Ω (CoordinateField Ω C.1) (unit.yzProjection C) = affineU Ω C.1 D.lam := by
      change coordinateValue Ω (CoordinateField Ω C.1)
        (coordinateOfGate (affineU Ω C.1 D.lam) (D.uGate C)) = _
      exact coordinateOfGate_value _ _
    rw [hv,coordinateEvaluation_eq_aeval]
    simp only [linearU,affineU,map_add,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Algebra.smul_def]
  · intro C
    have hv : coordinateValue Ω (CoordinateField Ω C.1) (unit.allProjection C) =
        affineV Ω C.1 D.mu (D.mu*D.lam) := by
      change (elementEmbedding Ω (CoordinateField Ω C.1)
        (affineV Ω C.1 D.mu (D.mu*D.lam)) (D.allAffineTranscendental C))
        (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X) = _
      exact elementEmbedding_variable Ω (CoordinateField Ω C.1) _ _
    rw [hv,coordinateEvaluation_eq_aeval]
    simp only [linearA,affineV,map_add,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Algebra.smul_def]

end
end ProximityPrize.SubmissionLower.MovingFiberNativeBudget6811
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.MovingFiberThreeSources6811
open scoped Classical BigOperators
open RCN002 RCN037 RCN039 RCN042 RCN046 RCN071 RCN076 RCN084 RCN095 RCN136 RCN207 RCN237 RCN264 RCN313 RCN340 RCN341 RCN344
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open MovingFiberNativeBudget6811 MovingFiberProjection6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 60000
set_option maxRecDepth 50000
variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local instance : DecidableEq Ω := Classical.decEq Ω
local notation "Poly3" => MvPolynomial (Fin 3) Ω

structure Source (F : MvPolynomial (Fin 4) K) where
  P : Poly (K := K)
  B : ℕ
  U : ℕ
  T : ℕ
  s : ℕ
  k : ℕ
  n0 : ℕ
  hS : ∀ e ∈ P.support, e 1 ≤ s
  hshape : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ T
  hBU : B ≤ U
  hUT : U ≤ T
  hdn : k+1 ≤ n0
  hB : 2*(n0-(k+1)) ≤ B
  hn : n0 ≤ (asS P).natDegree
  hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j

def Source.d {F : MvPolynomial (Fin 4) K} (S : Source F) : ℕ := S.k+1
def Source.flag {F : MvPolynomial (Fin 4) K} (S : Source F) : FlagDegree :=
  SecondJetRelaxedFlag.budgetFlag S.B S.U S.T S.d S.n0
def Source.leading {F : MvPolynomial (Fin 4) K} (S : Source F) (phi : Polynomial K →+* Ω) : Poly3 :=
  surfaceMap phi (asS S.P).leadingCoeff
def direction : Fin 3 → FlagDegree := ![unitZFlag,unitYZFlag,unitAllFlag]
def weight (W : FlagDegree) : Fin 3 → ℕ := ![W.zOnly,W.yz,W.all]

theorem pure_cut_three_sources
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (source : Fin 3 → Source F) (D : ℕ) (hD : ∀ j, (source j).d ∣ D)
    (carrier : Poly3) (p q W : FlagDegree)
    (hcarrier : Irreducible carrier) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (c : ℕ) [CharP Ω c] (hunit : 2*(p.zOnly+p.yz+p.all) < c)
    (h2 : (2 : Ω) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : Ω) ≠ 0)
    (Q A : Poly3) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) carrier ≠ 0)
    (hproper : ¬ carrier ∣ movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
    (hNflag : PolynomialInFlag q (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target))
    (base : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*∏ j, (source j).leading phi), SeparableLiteralCoordinate C.1)
    (hY : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*∏ j, (source j).leading phi), LiteralProjectionGate C 0)
    (hZ : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*∏ j, (source j).leading phi), LiteralProjectionGate C 2)
    (cut : Poly3) (hcut : PolynomialInFlag W cut) (points : Finset (Fin 3 → Ω))
    (hpoints : ∀ x ∈ points, MvPolynomial.eval x carrier = 0 ∧
      MvPolynomial.eval x (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) = 0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*∏ j, (source j).leading phi) ≠ 0 ∧
      MvPolynomial.aeval x cut = 0)
    (hisolated : ∀ x ∈ points, IsolatedPoint carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) cut x) :
    D*points.card ≤ ∑ j : Fin 3, weight W j*(D/(source j).d)*flagMixed p (direction j) (source j).flag := by
  classical
  let H := surfaceMap phi (polyH K F)
  let N := movingEquation H (surfaceMap phi (polyG K F)) Q A target
  let R := H*∏ j, (source j).leading phi
  let Family := RegularComponent Ω carrier N R
  obtain ⟨unit,a,b,hzv,hyv,hav⟩ := exists_common_native_unit p q base hY hZ hderiv hcarrier hproper hflag hNflag
  let ell : Fin 3 → Poly3 := ![linearZ,linearU a,linearA b a]
  let projection : (j : Fin 3) → (C : Family) → Coordinate Ω (CoordinateField Ω C.1) :=
    ![unit.zProjection,unit.yzProjection,unit.allProjection]
  have hell (j : Fin 3) : PolynomialInFlag (direction j) (ell j) := by
    fin_cases j
    · exact linearZ_flag
    · exact linearU_flag a
    · exact linearA_flag b a
  have hvalue (j : Fin 3) (C : Family) :
      coordinateValue Ω (CoordinateField Ω C.1) (projection j C) = coordinateEvaluation Ω C.1 (ell j) := by
    fin_cases j
    · exact hzv C
    · exact hyv C
    · exact hav C
  have hH (C : Family) : H ∉ C.1 := by
    intro h
    exact regularComponent_H_not_mem Ω carrier N R C
      (C.1.mul_mem_right (∏ j, (source j).leading phi) h)
  have hL (j : Fin 3) (C : Family) : (source j).leading phi ∉ C.1 := by
    intro h
    have hd : (source j).leading phi ∣ R :=
      dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun j => (source j).leading phi) (Finset.mem_univ j)) H
    exact regularComponent_H_not_mem Ω carrier N R C (C.1.mem_of_dvd hd h)
  let forget (j : Fin 3) (C : Family) : RegularComponent Ω carrier N (H*(source j).leading phi) :=
    ⟨C.1,(mem_regularComponents Ω).mpr ⟨regularComponent_mem Ω carrier N R C,by
      intro h
      exact ((inferInstance : C.1.IsPrime).mem_or_mem h).elim (hH C) (hL j C)⟩⟩
  have hinj (j : Fin 3) : Function.Injective (forget j) := by
    intro C C' h
    have hh := congrArg (fun C0 : RegularComponent Ω carrier N (H*(source j).leading phi) => C0.1) h
    exact Subtype.ext hh
  let Ext := AlgebraicClosure (RatFunc Ω)
  letI : Algebra Ω Ext := ((algebraMap (RatFunc Ω) Ext).comp (algebraMap Ω (RatFunc Ω))).toAlgebra
  letI : SMul (RatFunc Ω) Ext := (inferInstance : Algebra (RatFunc Ω) Ext).toSMul
  letI : SMul Ω Ext := (inferInstance : Algebra Ω Ext).toSMul
  letI : IsScalarTower Ω (RatFunc Ω) Ext := by
    constructor
    intro a b x
    simp only [Algebra.smul_def,map_mul]
    exact mul_assoc _ _ _
  letI : CharP Ext c := by infer_instance
  have h2e : (2 : Ext) ≠ 0 := by
    simpa only [map_ofNat,map_zero] using (algebraMap Ω Ext).injective.ne h2
  have hproj (j : Fin 3) :
      (source j).d*(∑ C : Family, coordinateDegree Ω (CoordinateField Ω C.1) (projection j C)) ≤
        flagMixed p (direction j) (source j).flag := by
    have hfe : ((source j).k.factorial : Ext) ≠ 0 := by
      simpa only [map_natCast,map_zero] using (algebraMap Ω Ext).injective.ne (hfact j)
    have hdirection : (direction j).zOnly+(direction j).yz+(direction j).all = 1 := by fin_cases j <;> rfl
    exact sum_coordinate_projection_degrees (E := Ext) phi F carrier p (direction j) hcarrier.ne_zero hcarrierF hflag
      (ell j) (hell j) c (by omega) (by rw [hdirection,mul_one]; exact hunit)
      (source j).P (source j).B (source j).U (source j).T (source j).s (source j).k (source j).n0
      (source j).hS (source j).hshape (source j).hBU (source j).hUT (source j).hdn (source j).hB
      (source j).hn (source j).hdiv h2e hfe Q A target hQ hA (forget j) (hinj j) (projection j) (hvalue j)
  have hscaled (j : Fin 3) :
      D*(∑ C : Family, coordinateDegree Ω (CoordinateField Ω C.1) (projection j C)) ≤
        (D/(source j).d)*flagMixed p (direction j) (source j).flag := by
    have h := Nat.mul_le_mul_left (D/(source j).d) (hproj j)
    simpa only [← Nat.mul_assoc,Nat.div_mul_cancel (hD j)] using h
  let budget := unit.toPrimeFlagBudgetFamily
  have hcard : points.card ≤ ∑ C : Family, budget.weightedCost W C := by
    apply (card_le_sum_componentSeeds Ω carrier N R points id
      (fun x hx => (hpoints x hx).1) (fun x hx => (hpoints x hx).2.1)
      (fun x hx => (hpoints x hx).2.2.1)).trans
    apply Finset.sum_le_sum
    intro C _
    by_cases he : (componentSeeds Ω carrier N R points id C).Nonempty
    · obtain ⟨x,hx⟩ := he
      have hxS := componentSeeds_subset Ω carrier N R points id C hx
      have hxC := componentSeeds_on_prime Ω carrier N R points id C x hx
      apply (budget.primeBudget C).zero_le W cut hcut
        (hisolated x hxS C.1 inferInstance (regularComponent_ne_point Ω carrier N R C)
          hxC (regularComponent_G_mem Ω carrier N R C) (regularComponent_T_mem Ω carrier N R C))
      · intro y hy
        exact componentSeeds_on_prime Ω carrier N R points id C y hy
      · intro y hy
        exact (hpoints y (componentSeeds_subset Ω carrier N R points id C hy)).2.2.2
    · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.zero_le]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    Nat.mul_le_mul_left (weight W j) (hscaled j))
  have hb : D*(∑ C : Family, budget.weightedCost W C) ≤
      ∑ j : Fin 3, weight W j*(D/(source j).d)*flagMixed p (direction j) (source j).flag := by
    have hl : D*(∑ C : Family, budget.weightedCost W C) =
        ∑ j : Fin 3, weight W j*(D*∑ C : Family, coordinateDegree Ω (CoordinateField Ω C.1) (projection j C)) := by
      simp only [Fin.sum_univ_three,projection,weight,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,
        budget,PrimeFlagBudgetFamily.weightedCost,AdaptiveUnitProjectionFamily.toPrimeFlagBudgetFamily,
        AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily,AdaptiveUnitProjectionFamily.toAdaptiveUnitPoleBudget,
        Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    have hr : (∑ j : Fin 3, weight W j*(D/(source j).d)*flagMixed p (direction j) (source j).flag) =
        ∑ j : Fin 3, weight W j*((D/(source j).d)*flagMixed p (direction j) (source j).flag) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hl,hr]
    exact hs
  exact (Nat.mul_le_mul_left D hcard).trans hb

theorem isolated_pure_cut_three_sources
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (source : Fin 3 → Source F) (D : ℕ) (hD : ∀ j, (source j).d ∣ D)
    (carrier : Poly3) (p q W : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (c : ℕ) [CharP Ω c] (hunit : 2*(p.zOnly+p.yz+p.all) < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c)
    (h2 : (2 : Ω) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : Ω) ≠ 0)
    (Q A : Poly3) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (hNflag : PolynomialInFlag q (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target))
    (cut : Poly3) (hcut : PolynomialInFlag W cut) (points : Finset (Fin 3 → Ω))
    (hpoints : ∀ x ∈ points, MvPolynomial.eval x carrier = 0 ∧
      MvPolynomial.eval x (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) = 0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*∏ j, (source j).leading phi) ≠ 0 ∧
      MvPolynomial.aeval x cut = 0)
    (hisolated : ∀ x ∈ points, IsolatedPoint carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) cut x) :
    D*points.card ≤ ∑ j : Fin 3, weight W j*(D/(source j).d)*flagMixed p (direction j) (source j).flag := by
  classical
  let H := surfaceMap phi (polyH K F)
  let N := movingEquation H (surfaceMap phi (polyG K F)) Q A target
  let R := H*∏ j, (source j).leading phi
  have hdeg : p.zOnly+p.yz+p.all < c := by omega
  have hderiv : H ∈ Ideal.span ({carrier,MvPolynomial.pderiv (1 : Fin 3) carrier} : Set Poly3) := by
    let I := Ideal.span ({carrier,MvPolynomial.pderiv (1 : Fin 3) carrier} : Set Poly3)
    have hc : carrier ∈ I := Ideal.subset_span (by simp)
    have hd : MvPolynomial.pderiv (1 : Fin 3) carrier ∈ I := Ideal.subset_span (by simp)
    obtain ⟨b,hb⟩ := hcarrierF
    change surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F) ∈ I
    rw [← RCN267.surfaceMap_pderiv_R,hb,MvPolynomial.pderiv_mul]
    exact I.add_mem (I.mul_mem_right b hd) (I.mul_mem_right (MvPolynomial.pderiv (1 : Fin 3) b) hc)
  have hcover : ∀ x ∈ points, ∃ g : ↥(activeFactors carrier N), MvPolynomial.eval x g.1 = 0 := by
    intro x hx
    have hp := hpoints x hx
    have hh : MvPolynomial.eval x H ≠ 0 := by
      have hr : MvPolynomial.eval x H * MvPolynomial.eval x (∏ j, (source j).leading phi) ≠ 0 := by
        simpa only [map_mul] using hp.2.2.1
      exact (mul_ne_zero_iff.mp hr).1
    exact exists_active_factor_of_isolated carrier N cut R hcarrier x hp.1 hp.2.2.2 hp.2.2.1
      (map_pderiv_ne_zero_of_mem_span (MvPolynomial.eval x) carrier H hderiv hp.1 hh) (hisolated x hx)
  obtain ⟨base,hY,hZ⟩ := exists_small_projection_data carrier N R hcarrier p q hflag hNflag c hdeg hmix
  let S (g : ↥(activeFactors carrier N)) : Finset (Fin 3 → Ω) :=
    points.filter (fun x => MvPolynomial.eval x g.1 = (0:Ω))
  have hcoverage : points ⊆ Finset.univ.biUnion S := by
    intro x hx
    obtain ⟨g,hg⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hx,hg⟩⟩
  have hcount (g : ↥(activeFactors carrier N)) :
      D*(S g).card ≤ ∑ j : Fin 3, weight W j*(D/(source j).d)*flagMixed (exactFlag g.1) (direction j) (source j).flag := by
    have hg := activeFactors_spec carrier N g
    have hgtotal : (exactFlag g.1).zOnly+(exactFlag g.1).yz+(exactFlag g.1).all ≤
        p.zOnly+p.yz+p.all := by
      rw [(exactFlag_cumulative g.1).2.2]
      exact (weightedTotalDegree_le_of_dvd_fin3 flagTotalWeights g.1 carrier hg.2.1 hcarrier).trans
        (inFlag_weight_caps carrier p hflag).2.2
    apply pure_cut_three_sources phi F source D hD g.1 (exactFlag g.1) q W hg.1
      (dvd_trans hg.2.1 hcarrierF) (polynomialIn_exactFlag g.1) c (by omega) h2 hfact
      Q A target hQ hA hg.2.2.2 hg.2.2.1 hNflag (base g) (hY g) (hZ g) cut hcut (S g)
    · intro x hx
      have hs := Finset.mem_filter.mp hx
      have hp := hpoints x hs.1
      exact ⟨hs.2,hp.2.1,hp.2.2.1,hp.2.2.2⟩
    · intro x hx J hj hnot hpoint hG hN
      exact hisolated x (Finset.mem_filter.mp hx).1 J hj hnot hpoint (J.mem_of_dvd hg.2.1 hG) hN
  calc
    D*points.card ≤ D*∑ g : ↥(activeFactors carrier N), (S g).card :=
      Nat.mul_le_mul_left _ ((Finset.card_le_card hcoverage).trans Finset.card_biUnion_le)
    _ = ∑ g : ↥(activeFactors carrier N), D*(S g).card := Finset.mul_sum _ _ _
    _ ≤ ∑ g : ↥(activeFactors carrier N), ∑ j : Fin 3,
        weight W j*(D/(source j).d)*flagMixed (exactFlag g.1) (direction j) (source j).flag :=
      Finset.sum_le_sum (fun g _ => hcount g)
    _ = ∑ j : Fin 3, weight W j*(D/(source j).d)*
        ∑ g : ↥(activeFactors carrier N), flagMixed (exactFlag g.1) (direction j) (source j).flag := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _
      (activeFactors_mixed_sum_le carrier N hcarrier p (direction j) (source j).flag hflag))

end
end ProximityPrize.SubmissionLower.MovingFiberThreeSources6811
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.MovingFiberDegreeSum6811
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN046 RCN072 RCN084 RCN095 RCN134 RCN136 RCN202
open RCN199 RCN200 RCN207 RCN208 RCN209 RCN237 RCN264 RCN313 RCN341 RCN344
open SecondJetCoefficients MovingFiberThreeSources6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 50000
variable {K Ω E : Type} [Field K] [Field Ω] [Field E] [IsAlgClosed Ω] [IsAlgClosed E]
  [Algebra Ω E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E]

omit [IsAlgClosed Ω] [IsAlgClosed E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E] in
private theorem scalar_surface_MovingFiberDegreeSum6811 (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K) :
    scalarPolynomialMap Ω E (surfaceMap phi F) = surfaceMap ((algebraMap Ω E).comp phi) F := by
  simp only [scalarPolynomialMap,surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]

omit [IsAlgClosed Ω] [IsAlgClosed E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E] in
private theorem eval_embedding (C : Ideal (MvPolynomial (Fin 3) Ω)) [C.IsPrime]
    (f : CoordinateField Ω C →ₐ[Ω] E) (F : MvPolynomial (Fin 3) Ω) :
    MvPolynomial.eval (embeddingPoint C f) (scalarPolynomialMap Ω E F) = f (coordinateEvaluation Ω C F) := by
  have h := AlgHom.congr_fun (embeddingPoint_aeval C f) F
  change MvPolynomial.eval (embeddingPoint C f) (MvPolynomial.map (algebraMap Ω E) F) = _
  rw [MvPolynomial.eval_map]
  exact h

theorem sum_moving_degrees_three_sources {ι : Type} [Fintype ι]
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (source : Fin 3 → Source F) (D : ℕ) (hD : ∀ j, (source j).d ∣ D)
    (carrier : MvPolynomial (Fin 3) Ω) (p : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (a b s n : ℕ) (center : FlagDegree)
    (coeff : Fin (n+1) → MvPolynomial (Fin 3) Ω) (coeffFlag : Fin (n+1) → FlagDegree)
    (hHflag : PolynomialInFlag (⟨a,b+1,s+1⟩ : FlagDegree) (surfaceMap phi (polyH K F)))
    (hGflag : PolynomialInFlag (⟨a,b,s+3⟩ : FlagDegree) (surfaceMap phi (polyG K F)))
    (hcoeff : ∀ j, PolynomialInFlag (coeffFlag j) (coeff j))
    (hcoeffEq : ∀ j, coeffFlag j+(n-j.val) • (⟨a,b+1,s+1⟩ : FlagDegree)+
      j.val • (⟨a,b,s+3⟩ : FlagDegree) = center+n • (⟨2*a,2*b+1,2*s+3⟩ : FlagDegree))
    (c : ℕ) [CharP E c] (hunit : 2*(p.zOnly+p.yz+p.all) < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < c)
    (h2 : (2 : E) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : E) ≠ 0)
    (Q A : MvPolynomial (Fin 3) Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (old : ι → RegularComponent Ω carrier
      (filteredCut n coeff (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))
      (surfaceMap phi (polyH K F)))
    (hold : Function.Injective old)
    (hleading : ∀ i j, (source j).leading phi ∉ (old i).1)
    (hAnonzero : ∀ i, A ∉ (old i).1)
    (projection : ∀ i, SeparableCoordinate Ω (CoordinateField Ω (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Ω (CoordinateField Ω (old i).1) (projection i) =
      movingValue (old i).1 (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A) :
    D*(∑ i, SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i)) ≤
      ∑ j : Fin 3, weight (center+n • (⟨a,b+1,s+2⟩ : FlagDegree)) j*(D/(source j).d)*
        flagMixed p (direction j) (source j).flag := by
  classical
  let H := surfaceMap phi (polyH K F)
  let G := surfaceMap phi (polyG K F)
  let mu := scalarPolynomialMap Ω E
  let phiE := (algebraMap Ω E).comp phi
  let prime := fun i => (old i).1
  letI : ∀ i, Algebra (RatFunc Ω) (CoordinateField Ω (prime i)) :=
    fun i => (projection i).embedding.toRingHom.toAlgebra
  letI : ∀ i, IsScalarTower Ω (RatFunc Ω) (CoordinateField Ω (prime i)) :=
    fun i => IsScalarTower.of_algebraMap_eq (fun a => ((projection i).embedding.commutes a).symm)
  letI : ∀ i, FiniteDimensional (RatFunc Ω) (CoordinateField Ω (prime i)) := fun i => (projection i).finite
  letI : ∀ i, Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (prime i)) := fun i => (projection i).separable
  let points := genericFiberPoints (B := RatFunc Ω) (L := E) prime
  let target := algebraMap (RatFunc Ω) E (rationalVariable Ω)
  let N := fiberEquation (E := E) H G Q A
  let cut := fiberCut (E := E) n coeff Q A
  let W := center+n • (⟨a,b+1,s+2⟩ : FlagDegree)
  have hi : Function.Injective prime := by
    intro i j h
    exact hold (Subtype.ext h)
  have certificate (i : ι) (f : CoordinateField Ω (prime i) →ₐ[RatFunc Ω] E) :
      let x := embeddingPoint (prime i) (f.restrictScalars Ω)
      MvPolynomial.eval x (mu carrier) = 0 ∧ MvPolynomial.eval x N = 0 ∧
      MvPolynomial.aeval x cut = 0 ∧ MvPolynomial.eval x (mu H*mu A) ≠ 0 ∧
      IsolatedPoint (mu carrier) N cut x := by
    letI : Algebra (RatFunc Ω) (CoordinateField Ω (old i).1) :=
      (projection i).embedding.toRingHom.toAlgebra
    have hj : algebraMap (RatFunc Ω) (CoordinateField Ω (old i).1) (rationalVariable Ω) =
        movingValue (old i).1 H G Q A := hvalue i
    exact RCN202.embedding_point_certificate carrier H G Q A n coeff (old i) hj (hAnonzero i) f
  have hpoints : ∀ x ∈ points,
      MvPolynomial.eval x (mu carrier) = 0 ∧ MvPolynomial.eval x N = 0 ∧
      MvPolynomial.eval x (surfaceMap phiE (polyH K F)*∏ j, (source j).leading phiE) ≠ 0 ∧
      MvPolynomial.aeval x cut = 0 := by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩ := Finset.mem_image.mp hx
    have hc := certificate i f
    have hHne : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω)) (mu H) ≠ 0 := by
      have hh := hc.2.2.2.1
      rw [map_mul] at hh
      exact (mul_ne_zero_iff.mp hh).1
    have hLne (j : Fin 3) : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω))
        ((source j).leading phiE) ≠ 0 := by
      have he : (source j).leading phiE = mu ((source j).leading phi) := by
        exact (scalar_surface_MovingFiberDegreeSum6811 phi (asS (source j).P).leadingCoeff).symm
      rw [he,eval_embedding]
      intro hz
      exact hleading i j ((SecondJetComponentRoots.evaluation_zero_iff (prime i) _).mp
        ((map_eq_zero_iff f f.injective).mp hz))
    have hprod : (∏ j : Fin 3, MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω))
        ((source j).leading phiE)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hLne j)
    have hgate : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω))
        (surfaceMap phiE (polyH K F)*∏ j, (source j).leading phiE) ≠ 0 := by
      rw [map_mul,map_prod]
      apply mul_ne_zero _ hprod
      simpa only [H,mu,scalar_surface_MovingFiberDegreeSum6811,phiE] using hHne
    exact ⟨hc.1,hc.2.1,hgate,hc.2.2.1⟩
  have hiso : ∀ x ∈ points, IsolatedPoint (mu carrier) N cut x := by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩ := Finset.mem_image.mp hx
    exact (certificate i f).2.2.2.2
  obtain ⟨hNflag,hcutflag⟩ := RCN202.fiber_small_flags (E := E) a b s n center H G Q A coeff coeffFlag
    hHflag hGflag hQ hA hcoeff hcoeffEq
  have hN : N = movingEquation (surfaceMap phiE (polyH K F)) (surfaceMap phiE (polyG K F))
      (mu Q) (mu A) target := by
    dsimp only [N,fiberEquation]
    rw [show scalarPolynomialMap Ω E H = surfaceMap phiE (polyH K F) from scalar_surface_MovingFiberDegreeSum6811 phi _,
      show scalarPolynomialMap Ω E G = surfaceMap phiE (polyG K F) from scalar_surface_MovingFiberDegreeSum6811 phi _]
  have hcar : mu carrier ∣ surfaceMap phiE F := by
    simpa only [mu,scalar_surface_MovingFiberDegreeSum6811,phiE] using map_dvd mu hcarrierF
  have hmu : Function.Injective mu := MvPolynomial.map_injective (algebraMap Ω E) (algebraMap Ω E).injective
  have hne : mu carrier ≠ 0 := fun hz => hcarrier (hmu (by simpa only [map_zero] using hz))
  have hNflag' : PolynomialInFlag (⟨a,b+1,s+3⟩ : FlagDegree)
      (movingEquation (surfaceMap phiE (polyH K F)) (surfaceMap phiE (polyG K F)) (mu Q) (mu A) target) := by
    change PolynomialInFlag (⟨a,b+1,s+3⟩ : FlagDegree) N at hNflag
    rwa [hN] at hNflag
  rw [hN] at hpoints hiso
  have hc := isolated_pure_cut_three_sources phiE F source D hD (mu carrier) p (⟨a,b+1,s+3⟩ : FlagDegree) W
    hne hcar (inFlag_map _ hflag) c hunit hmix h2 hfact (mu Q) (mu A) target
    (inFlag_map _ hQ) (inFlag_map _ hA) hNflag' cut hcutflag points hpoints hiso
  have hcard := genericFiberPoints_card (B := RatFunc Ω) (L := E) prime hi
  simpa only [points,hcard,SeparableCoordinate.degree,prime,W] using hc

theorem actual_first_tail_moving_degrees {ι : Type} [Fintype ι]
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (source : Fin 3 → Source F) (D : ℕ) (hD : ∀ j, (source j).d ∣ D)
    (carrier : MvPolynomial (Fin 3) Ω) (p : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (a b s w : ℕ) (hw : 1 ≤ w)
    (hR : F.degreeOf 2 ≤ s+2)
    (hYR : RCN234.wt ![0,1,1,0] F ≤ b+s+3)
    (hAll : RCN234.wt ![0,1,1,1] F ≤ a+b+s+3)
    (c : ℕ) [CharP E c] (hunit : 2*(p.zOnly+p.yz+p.all) < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < c)
    (h2 : (2 : E) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : E) ≠ 0)
    (Q A : MvPolynomial (Fin 3) Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (old : ι → RegularComponent Ω carrier (RCN086.globalTailCut phi F (w+1)) (surfaceMap phi (polyH K F)))
    (hold : Function.Injective old)
    (hleading : ∀ i j, (source j).leading phi ∉ (old i).1)
    (hAnonzero : ∀ i, A ∉ (old i).1)
    (projection : ∀ i, SeparableCoordinate Ω (CoordinateField Ω (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Ω (CoordinateField Ω (old i).1) (projection i) =
      movingValue (old i).1 (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A) :
    D*(∑ i, SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i)) ≤
      ∑ j : Fin 3, weight (RCN198.center a b s+w • (⟨a,b+1,s+2⟩ : FlagDegree)) j*(D/(source j).d)*
        flagMixed p (direction j) (source j).flag := by
  classical
  obtain ⟨coeff,flags,heq,hcoeff,hrel⟩ := RCN086.exists_filtered_certificate phi a b s F hR hYR hAll
    (w+1) (by omega) (RCN086.tailSelector (w+1)) 0 0 0
  have heq' : RCN086.globalTailCut phi F (w+1) =
      filteredCut w coeff (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) := heq
  let old' : ι → RegularComponent Ω carrier
      (filteredCut w coeff (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))
      (surfaceMap phi (polyH K F)) := fun i => ⟨(old i).1,by rw [← heq']; exact (old i).2⟩
  have hi : Function.Injective old' := by
    intro i j h
    have hh := congrArg (fun C : RegularComponent Ω carrier
      (filteredCut w coeff (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))
      (surfaceMap phi (polyH K F)) => C.1) h
    exact hold (Subtype.ext hh)
  obtain ⟨hHflag,hGflag⟩ := RCN201.surfaceMap_HG_flags phi a b s F hR hYR hAll
  exact sum_moving_degrees_three_sources (E := E) phi F source D hD carrier p hcarrier hcarrierF hflag
    a b s w (RCN198.center a b s) coeff flags hHflag hGflag hcoeff hrel c hunit hmix h2 hfact
    Q A hQ hA old' hi hleading hAnonzero projection hvalue

theorem exists_first_tail_budget
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (source : Fin 3 → Source F) (D : ℕ) (hDpos : 0 < D) (hD : ∀ j, (source j).d ∣ D)
    (carrier : MvPolynomial (Fin 3) Ω) (p tailFlag : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (a b s w : ℕ) (hw : 1 ≤ w)
    (hR : F.degreeOf 2 ≤ s+2)
    (hYR : RCN234.wt ![0,1,1,0] F ≤ b+s+3)
    (hAll : RCN234.wt ![0,1,1,1] F ≤ a+b+s+3)
    (c : ℕ) [CharP E c] (hunit : 2*(p.zOnly+p.yz+p.all) < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < c)
    (h2 : (2 : E) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : E) ≠ 0)
    (base : ∀ C : RegularComponent Ω carrier (RCN086.globalTailCut phi F (w+1))
      (surfaceMap phi (polyH K F)), SeparableLiteralCoordinate C.1)
    (unit : AdaptiveUnitProjectionFamily base p tailFlag)
    (active : Finset (RegularComponent Ω carrier (RCN086.globalTailCut phi F (w+1)) (surfaceMap phi (polyH K F))))
    (hleading : ∀ C ∈ active, ∀ j, (source j).leading phi ∉ C.1) :
    ∃ budget : ∀ C : RegularComponent Ω carrier (RCN086.globalTailCut phi F (w+1)) (surfaceMap phi (polyH K F)),
        MovingPoleBudget C.1 (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)),
      (∀ C : RegularComponent Ω carrier (RCN086.globalTailCut phi F (w+1)) (surfaceMap phi (polyH K F)),
        (budget C).zCost = unit.toPrimeFlagBudgetFamily.zCost C ∧
        (budget C).yzCost = unit.toPrimeFlagBudgetFamily.yzCost C ∧
        (budget C).allCost = unit.toPrimeFlagBudgetFamily.allCost C) ∧
      (∑ C ∈ active, (budget C).movingCost) ≤
        (∑ j : Fin 3, weight (RCN198.center a b s+w • (⟨a,b+1,s+2⟩ : FlagDegree)) j*(D/(source j).d)*
          flagMixed p (direction j) (source j).flag)/D := by
  classical
  let H := surfaceMap phi (polyH K F)
  let G := surfaceMap phi (polyG K F)
  let T := RCN086.globalTailCut phi F (w+1)
  obtain ⟨Q,A,J,hQ,hA,hJ⟩ := exists_separable_moving_coordinates carrier T H G base
  let budget := budgetOfProjections carrier T H G unit J (fun C v => (hJ C).2.2.1 v)
  refine ⟨budget,(fun _ => ⟨rfl,rfl,rfl⟩),?_⟩
  have hb := actual_first_tail_moving_degrees (E := E) phi F source D hD carrier p hcarrier hcarrierF hflag
    a b s w hw hR hYR hAll c hunit hmix h2 hfact Q A hQ hA
    (fun C : active => C.val) Subtype.val_injective
    (fun C j => hleading C.val C.property j)
    (fun C => (hJ C.val).1) (fun C => J C.val) (fun C => (hJ C.val).2.1)
  have hsum : (∑ C ∈ active, (budget C).movingCost) =
      ∑ C : active, SeparableCoordinate.degree Ω (CoordinateField Ω C.val.1) (J C.val) := by
    exact (Finset.sum_coe_sort active (fun C => (budget C).movingCost)).symm
  apply (Nat.le_div_iff_mul_le hDpos).mpr
  rw [hsum]
  simpa only [Nat.mul_comm] using hb

end
end ProximityPrize.SubmissionLower.MovingFiberDegreeSum6811
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.PhasePotential6815
open RCN260 AsymmetricHelper
set_option autoImplicit false
set_option maxHeartbeats 1000000

end ProximityPrize.SubmissionLower.PhasePotential6815
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.BalancedPhasePotential6815
open RCN260 AsymmetricHelper PhasePotential6815
set_option autoImplicit false
set_option maxHeartbeats 1400000

end ProximityPrize.SubmissionLower.BalancedPhasePotential6815
end MergedPart9
section MergedPart10
set_option Elab.async false

namespace ProximityPrize.SubmissionLower.Lower80899.SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open Lower80899.FactorSwitch Lower80899.PowerRoute
open Lower80899.Oracle
open LocatorPhase6800Oracle (Potential)

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Phase00

end Phase00
namespace Phase01

end Phase01
namespace Phase02

end Phase02
namespace Phase03

end Phase03
namespace Phase04

end Phase04
namespace Phase05

end Phase05
namespace Phase06

end Phase06
namespace PhaseFinal

end PhaseFinal
end ProximityPrize.SubmissionLower.Lower80899.SourceSound
end MergedPart10
