import ProximityPrize.SubmissionBinaryLower.B6402OrderTwoFibres
import ProximityPrize.SubmissionBinaryLower.P64Resultant

/-! At a regular quartic site, discard only zeros of its original seed
coefficient. Every retained witness that misses the site receives 2b roots. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402RegularWitness
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd B6402MixedDegree
open B6402FibreSlice B6402MissedFibres B6402PrimarySystem P64LineOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {K : Type} [Field K] [CharP K 2]

noncomputable def quartic (F : ContactPoly (Polynomial K)) (x : K) := ((F.coeff 1).coeff 4).eval (C x)

theorem top (F : ContactPoly (Polynomial K)) (x : K) (y : K[X]) (h : (F.coeff 1).natDegree≤4) :
    (ordinateHom x y (F.coeff 1)).coeff 4=quartic F x := by
  let p := evalXAt (F.coeff 1) x
  have hdeg : p.natDegree≤4 := natDegree_map_le.trans h
  have he : p.coeff 4=quartic F x := by simp [p,evalXAt,quartic,coeff_map]
  rw [←he]; change (taylor y p).coeff 4=p.coeff 4
  by_cases heq : p.natDegree=4
  · rw [←heq,coeff_taylor_natDegree,coeff_natDegree]
  · have h' : (taylor y p).natDegree<4 := by rw [natDegree_taylor]; omega
    rw [coeff_eq_zero_of_natDegree_lt h',coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree<4)]

theorem quartic_degree {q H : ℕ} (F : ContactPoly (Polynomial K)) (x : K) (hf : mixed q F≤H) :
    (quartic F x).natDegree≤H := by
  unfold quartic
  apply P64Resultant.natDegree_eval_C_le_of_coeff ((F.coeff 1).coeff 4) x H
  intro a; by_cases hz : ((F.coeff 1).coeff 4).coeff a=0
  · simp [hz]
  · have hi := (mixed_le_iff _ _ _).mp hf 1 4 a hz; omega

theorem unit_at_miss (F : ContactPoly (Polynomial K)) (x : K) (y : K[X]) (z : K) (P : K[X])
    (quart : ordinateHom x y (F.coeff 1)=monomial 4 (quartic F x))
    (retained : (quartic F x).eval z≠0) (miss : P.eval x≠y.eval z) :
    IsCoprime (Polynomial.X-C x) (((evalZContact F z).coeff 1).eval P) := by
  apply (irreducible_X_sub_C x).coprime_iff_not_dvd.mpr
  intro hv
  have hz := dvd_iff_isRoot.mp hv
  have ec : (evalZContact F z).coeff 1=BCHKSSubstitutionVanish.specializeZ (F.coeff 1) z := by
    unfold evalZContact BCHKSSubstitutionVanish.specializeZ; rw [coeff_map]; rfl
  rw [IsRoot.def,ec] at hz
  change (BCHKSSubstitutionVanish.triEval (F.coeff 1) z P).eval x=0 at hz
  have siteZero := (P64Resultant.eval_triEval_eq_biEval_triSpecializeX (F.coeff 1) P x z).symm.trans hz
  let a := P.eval x-y.eval z
  have ha : a≠0 := sub_ne_zero.mpr miss
  have hs := congrArg (fun p : Polynomial (Polynomial K) => (p.map (evalRingHom z)).eval a) quart
  have he : ((ordinateHom x y (F.coeff 1)).map (evalRingHom z)).eval a=
      P64Resultant.biEval (P64Resultant.triSpecializeX (F.coeff 1) x) (P.eval x) z := by
    change (((evalXAt (F.coeff 1) x).comp (Polynomial.X+C y)).map (evalRingHom z)).eval a=_
    rw [Polynomial.map_comp]; simp [eval_comp,a,P64Resultant.biEval,P64Resultant.triSpecializeX,evalXAt]
  change ((ordinateHom x y (F.coeff 1)).map (evalRingHom z)).eval a= _ at hs
  rw [he,siteZero] at hs
  have neq : (quartic F x).eval z*a^4 ≠0 := mul_ne_zero retained (pow_ne_zero _ ha)
  apply neq
  simpa [Polynomial.map_monomial,eval_monomial] using hs.symm

theorem regular_miss (F G : ContactPoly (Polynomial K)) (x : K) (y : K[X]) (z : K) (P : K[X]) (s b : ℕ)
    (hF : F.natDegree≤1) (hG : G.natDegree≤s) (onF : evalContact (evalZContact F z) P=0)
    (quart : ordinateHom x y (F.coeff 1)=monomial 4 (quartic F x))
    (retained : (quartic F x).eval z≠0) (miss : P.eval x≠y.eval z)
    (hd : C ((Polynomial.X : (Polynomial K)[X])-C (C x))^(2*b) ∣ resultant F G 1 s) :
    (Polynomial.X-C x)^(2*b) ∣ evalContact (evalZContact G z) P := by
  let φ := Polynomial.mapRingHom (Polynomial.mapRingHom (evalRingHom z))
  apply missed_roots_of_resultant (evalZContact F z) (evalZContact G z) P x s b
    (natDegree_map_le.trans hF) (natDegree_map_le.trans hG) onF (unit_at_miss F x y z P quart retained miss)
  obtain ⟨p,hp⟩ := hd
  refine ⟨φ p,?_⟩
  have he := congrArg φ hp
  rw [map_mul,map_pow] at he
  have hj : φ (C ((Polynomial.X : (Polynomial K)[X])-C (C x))) = C (Polynomial.X-C x) := by simp [φ]
  rw [hj] at he
  change Polynomial.resultant (F.map φ) (G.map φ) 1 s=_
  exact (Polynomial.resultant_map_map F G 1 s φ).trans he

#print axioms quartic_degree
#print axioms regular_miss
end ProximityPrize.SubmissionBinaryLower.B6402RegularWitness
