import ProximityPrize.SubmissionLower.BCHKSUniversalOuterCover6399
import ProximityPrize.SubmissionLower.BCHKSSelectedNonpole

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators

set_option maxHeartbeats 2000000

namespace UniversalPairFiberBridge6399

open UniversalOuterCover6399

/-- Split the one-time outer obstruction into its leading and separability
components at a surviving seed. -/
theorem obstruction_seed_parts
    (x₀ z : F) (R : TriPoly)
    (hobs : Polynomial.eval z
      (Polynomial.eval (Polynomial.C x₀) (factorXObstruction R)) ≠ 0) :
    Polynomial.eval z
        (Polynomial.eval (Polynomial.C x₀) R.leadingCoeff) ≠ 0 ∧
      Polynomial.eval z
        (Polynomial.eval (Polynomial.C x₀) (rawSepResultant R)) ≠ 0 := by
  simpa [factorXObstruction, Polynomial.eval_mul] using hobs

/-- A positive normalized inner factor retains its leading coefficient at any
seed where the outer leading coefficient survives. -/
theorem inner_leadingCoeff_eval_ne_zero
    (x₀ z : F) (R : TriPoly) (H : BiPoly)
    (hBdeg : (triSpecializeX R x₀).natDegree = R.natDegree)
    (hHd : H ∣ triSpecializeX R x₀)
    (hRlead : Polynomial.eval z
      (Polynomial.eval (Polynomial.C x₀) R.leadingCoeff) ≠ 0) :
    H.leadingCoeff.eval z ≠ 0 := by
  let B := triSpecializeX R x₀
  have hBlead : B.leadingCoeff =
      Polynomial.eval (Polynomial.C x₀) R.leadingCoeff := by
    have heq : B.leadingCoeff = B.coeff R.natDegree := by
      rw [← hBdeg, Polynomial.coeff_natDegree]
    rw [heq]
    change (R.map (Polynomial.evalRingHom (Polynomial.C x₀))).coeff R.natDegree = _
    rw [Polynomial.coeff_map, Polynomial.coeff_natDegree]
    rfl
  obtain ⟨C, hBC⟩ := hHd
  have hmul : B.leadingCoeff = H.leadingCoeff * C.leadingCoeff := by
    change (triSpecializeX R x₀).leadingCoeff = _
    rw [hBC]
    exact Polynomial.leadingCoeff_mul H C
  intro hHz
  apply hRlead
  rw [← hBlead, hmul, Polynomial.eval_mul, hHz, zero_mul]

/-- Exact value of the finite `Y`-slope after the two specializations. -/
theorem ySlope_eq_derivative_specialization
    (R : TriPoly) (z x y : F) :
    FiniteHensel.ySlope (triSpecializeZ R z) x y =
      Polynomial.eval y
        (biSpecializeZ (triSpecializeX R.derivative x) z) := by
  simp only [FiniteHensel.ySlope, triSpecializeZ, triSpecializeX,
    biSpecializeZ, Polynomial.derivative_map]
  induction Polynomial.derivative R using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [eval_map_eval_eq_eval_eval_C]

/-- The raw separability component of the outer obstruction makes every
selected outer root simple at a surviving seed. -/
theorem simple_slope_of_pairRel
    (Pz : F → Polynomial F) (x₀ z : F) (R : TriPoly) (H : BiPoly)
    (hrel : pairRel Pz x₀ z (R, H))
    (hBdeg : (triSpecializeX R x₀).natDegree = R.natDegree)
    (hRpos : 0 < R.natDegree) :
    FiniteHensel.ySlope (triSpecializeZ R z) x₀
      ((Pz z).eval x₀) ≠ 0 := by
  let B := triSpecializeX R x₀
  have hparts := obstruction_seed_parts x₀ z R hrel.2.2.1
  have hresX : Polynomial.eval (Polynomial.C x₀) (rawSepResultant R) =
      Polynomial.resultant B B.derivative R.natDegree
        (R.natDegree - 1) := by
    change (Polynomial.evalRingHom (Polynomial.C x₀))
        (Polynomial.resultant R R.derivative R.natDegree
          (R.natDegree - 1)) =
      Polynomial.resultant
        (R.map (Polynomial.evalRingHom (Polynomial.C x₀)))
        (R.map (Polynomial.evalRingHom (Polynomial.C x₀))).derivative
        R.natDegree (R.natDegree - 1)
    rw [Polynomial.derivative_map]
    exact (Polynomial.resultant_map_map R R.derivative R.natDegree
      (R.natDegree - 1) (Polynomial.evalRingHom (Polynomial.C x₀))).symm
  have hresB : Polynomial.eval z
      (Polynomial.resultant B B.derivative B.natDegree
        (B.natDegree - 1)) ≠ 0 := by
    rw [hBdeg, ← hresX]
    exact hparts.2
  have hBroot : Polynomial.eval ((Pz z).eval x₀)
      (biSpecializeZ B z) = 0 := by
    change biEval B ((Pz z).eval x₀) z = 0
    exact (eval_triEval_eq_biEval_triSpecializeX R (Pz z) x₀ z).symm.trans
      (by simpa using congrArg (Polynomial.eval x₀) hrel.1)
  have hsimple := simple_root_of_fixed_resultant_eval_ne_zero
    B z ((Pz z).eval x₀) (by simpa [B, hBdeg] using hRpos) hresB hBroot
  rw [ySlope_eq_derivative_specialization]
  simpa [B, triSpecializeX, Polynomial.derivative_map] using hsimple

/-- All elementary data carried by one selected pair at one fiber seed. -/
structure FiberFacts
    (Pz : F → Polynomial F) (Q : TriPoly) (x₀ z : F) (RH : Pair) : Prop where
  hRmem : RH.1 ∈ UniqueFactorizationMonoid.normalizedFactors Q
  hRpos : 0 < RH.1.natDegree
  hHmem : RH.2 ∈ UniqueFactorizationMonoid.normalizedFactors
    (triSpecializeX RH.1 x₀)
  hHpos : 0 < RH.2.natDegree
  hHd : RH.2 ∣ triSpecializeX RH.1 x₀
  hBprimitive : (triSpecializeX RH.1 x₀).IsPrimitive
  hRirreducible : Irreducible RH.1
  hHirreducible : Irreducible RH.2
  hHleading : RH.2.leadingCoeff.eval z ≠ 0
  hRExact : (triSpecializeZ RH.1 z).eval (Pz z) = 0
  hHroot : Polynomial.evalEval z ((Pz z).eval x₀) RH.2 = 0
  hsimple : FiniteHensel.IsSimpleRootAt (triSpecializeZ RH.1 z) x₀
    ((Pz z).eval x₀)

/-- Deterministic bridge from the global cover relation and the chosen-x₀
facts to all elementary selected-fiber facts. -/
theorem fiberFacts_of_pairRel
    (Pz : F → Polynomial F) (Q : TriPoly) (x₀ z : F) (RH : Pair)
    (hRH : RH ∈ pairs Q x₀)
    (hx : ∀ R ∈ outerFactors Q,
      (triSpecializeX R x₀).IsPrimitive ∧
      Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 ∧
      triSpecializeX R x₀ ≠ 0 ∧
      (triSpecializeX R x₀).natDegree = R.natDegree ∧
      Polynomial.eval (Polynomial.C x₀) (rawSepResultant R) ≠ 0)
    (hrel : pairRel Pz x₀ z RH) :
    FiberFacts Pz Q x₀ z RH := by
  have hm := pair_mem_facts Q x₀ RH hRH
  have hRouter : RH.1 ∈ outerFactors Q :=
    Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hm.1, hm.2.1⟩
  have hxR := hx RH.1 hRouter
  have hparts := obstruction_seed_parts x₀ z RH.1 hrel.2.2.1
  have hHlead := inner_leadingCoeff_eval_ne_zero x₀ z RH.1 RH.2
    hxR.2.2.2.1 hm.2.2.2.2 hparts.1
  have hRExact : (triSpecializeZ RH.1 z).eval (Pz z) = 0 := hrel.1
  have hHroot : Polynomial.evalEval z ((Pz z).eval x₀) RH.2 = 0 := by
    exact (eval_map_eval_eq_eval_eval_C RH.2 ((Pz z).eval x₀) z).symm.trans
      hrel.2.1
  have hslope := simple_slope_of_pairRel Pz x₀ z RH.1 RH.2 hrel
    hxR.2.2.2.1 hm.2.1
  refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2,
    hxR.1, ?_, ?_, hHlead, hRExact, hHroot, ?_⟩
  · exact (UniqueFactorizationMonoid.prime_of_normalized_factor RH.1 hm.1).irreducible
  · exact (UniqueFactorizationMonoid.prime_of_normalized_factor RH.2 hm.2.2.1).irreducible
  · refine ⟨?_, hslope⟩
    have he := congrArg (Polynomial.eval x₀) hRExact
    calc
      (triSpecializeZ RH.1 z).eval₂ (Polynomial.evalRingHom x₀)
          ((Pz z).eval x₀) =
          (Polynomial.evalRingHom x₀)
            ((triSpecializeZ RH.1 z).eval (Pz z)) := by
        exact (Polynomial.hom_eval₂ (triSpecializeZ RH.1 z) (RingHom.id F[X])
          (Polynomial.evalRingHom x₀) (Pz z)).symm
      _ = 0 := by simpa using he

end UniversalPairFiberBridge6399

end ProximityPrize.SubmissionLower
