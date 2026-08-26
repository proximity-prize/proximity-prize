import ProximityPrize.SubmissionLower.BCHKSFullOrderSlice6400
import ProximityPrize.SubmissionLower.BCHKSCoreVandermonde6400
import ProximityPrize.SubmissionLower.BCHKSCodimTupleCount6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSFullCoreOwnerBridge6400
open Polynomial
open scoped BigOperators
open BCHKSSubstitutionVanish
open BCHKSFullOrderSlice6400
open BCHKSFullCoreLineArrangement6400
open BCHKSCoreVandermonde6400
open BCHKSBoundaryCoreArrangement6400
open BCHKSCodimTupleCount6400
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
noncomputable def receivedLineAt
    {F : Type*} [Field F] (U0 U1 : F → F) (x : F) : F[X] :=
  Polynomial.C (U0 x) + Polynomial.C (U1 x) * Polynomial.X
@[simp]
theorem eval_receivedLineAt
    {F : Type*} [Field F] (U0 U1 : F → F) (x z : F) :
    Polynomial.eval z (receivedLineAt U0 U1 x) = U0 x + z * U1 x := by
  simp only [receivedLineAt, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  rw [mul_comm (U1 x) z]
noncomputable def coreBasePolynomial
    {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) (U : F → F) : F[X] :=
  Lagrange.interpolate E id U
@[simp]
theorem coreBasePolynomial_eval
    {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) (U : F → F) (x : F) (hx : x ∈ E) :
    Polynomial.eval x (coreBasePolynomial E U) = U x := by
  classical
  simpa [coreBasePolynomial] using
    (Lagrange.eval_interpolate_at_node U
      (Set.injOn_id (↑E : Set F)) hx)
theorem coreBasePolynomial_natDegree_le
    {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) (U : F → F) (k s : ℕ)
    (hcard : E.card + s = k) :
    (coreBasePolynomial E U).natDegree ≤ k := by
  classical
  let B : F[X] := coreBasePolynomial E U
  change B.natDegree ≤ k
  by_cases hB : B = 0
  · simp [B, hB]
  · have hdegree : B.degree < (E.card : WithBot ℕ) := by
      simpa [B, coreBasePolynomial] using
        (Lagrange.degree_interpolate_lt U
          (Set.injOn_id (↑E : Set F)))
    have hnat : B.natDegree < E.card :=
      (Polynomial.natDegree_lt_iff_degree_lt hB).2 hdegree
    omega
def NoLargeAffineOwnerLine
    {F : Type*} [Field F]
    (S : Finset F) (P : F → F[X]) (k e : ℕ) : Prop :=
  ∀ T : Finset F, T ⊆ S →
    ∀ p0 p1 : F[X], p0.natDegree ≤ k → p1.natDegree ≤ k →
      (∀ z ∈ T, P z = p0 + Polynomial.C z * p1) → T.card ≤ e
theorem owner_matches_received_on_fullOrderCore
    {F : Type*} [Field F] [DecidableEq F]
    (R : Polynomial (Polynomial (Polynomial F)))
    (E S : Finset F) (P : F → F[X]) (U0 U1 : F → F) (d : ℕ)
    (hd : 1 ≤ d)
    (hshift : ∀ x ∈ E,
      Polynomial.Bivariate.shift R (Polynomial.C x)
        (receivedLineAt U0 U1 x) ≠ 0)
    (horder : ∀ x ∈ E,
      BCHKSLocalValuation6400.localOrder
        (Polynomial.Bivariate.shift R (Polynomial.C x)
          (receivedLineAt U0 U1 x)) = d)
    (hsliceDegree : ∀ x ∈ E,
      (zeroXSlice (Polynomial.Bivariate.shift R (Polynomial.C x)
        (receivedLineAt U0 U1 x))).natDegree ≤ d)
    (hlead : ∀ z ∈ S, ∀ x ∈ E,
      Polynomial.eval z
        ((zeroXSlice (Polynomial.Bivariate.shift R (Polynomial.C x)
          (receivedLineAt U0 U1 x))).coeff d) ≠ 0)
    (hroot : ∀ z ∈ S, triEval R z (P z) = 0) :
    ∀ z ∈ S, ∀ x ∈ E,
      Polynomial.eval x (P z) = U0 x + z * U1 x := by
  intro z hz x hx
  have hmatch := owner_matches_received_of_full_order_slice
    R x z (receivedLineAt U0 U1 x) (P z) d
      (hshift x hx) (horder x hx) (hsliceDegree x hx) hd
      (hlead z hz x hx) (hroot z hz)
  simpa using hmatch
theorem exists_bounded_coreQuotient_family
    {F : Type*} [Field F] [DecidableEq F]
    (E S : Finset F) (P : F → F[X]) (U0 U1 : F → F)
    (k s : ℕ)
    (hcard : E.card + s = k)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ k)
    (hcoreMatch : ∀ z ∈ S, ∀ x ∈ E,
      Polynomial.eval x (P z) = U0 x + z * U1 x) :
    ∃ B0 B1 : F[X], ∃ Q : F → F[X],
      B0.natDegree ≤ k ∧ B1.natDegree ≤ k ∧
      (∀ x ∈ E, B0.eval x = U0 x) ∧
      (∀ x ∈ E, B1.eval x = U1 x) ∧
      (∀ z ∈ S, (Q z).natDegree ≤ s) ∧
      (∀ z ∈ S,
        P z = B0 + Polynomial.C z * B1 + coreLocator E * Q z) := by
  classical
  let B0 : F[X] := coreBasePolynomial E U0
  let B1 : F[X] := coreBasePolynomial E U1
  have hB0degree : B0.natDegree ≤ k :=
    coreBasePolynomial_natDegree_le E U0 k s hcard
  have hB1degree : B1.natDegree ≤ k :=
    coreBasePolynomial_natDegree_le E U1 k s hcard
  have hB0eval : ∀ x ∈ E, B0.eval x = U0 x := by
    intro x hx
    exact coreBasePolynomial_eval E U0 x hx
  have hB1eval : ∀ x ∈ E, B1.eval x = U1 x := by
    intro x hx
    exact coreBasePolynomial_eval E U1 x hx
  have hexists : ∀ z : F, ∃ q : F[X], z ∈ S →
      q.natDegree ≤ s ∧
        P z = B0 + Polynomial.C z * B1 + coreLocator E * q := by
    intro z
    by_cases hz : z ∈ S
    · have hbaseDegree :
          (B0 + Polynomial.C z * B1).natDegree ≤ k :=
        (Polynomial.natDegree_add_le _ _).trans
          (max_le hB0degree
            ((Polynomial.natDegree_C_mul_le z B1).trans hB1degree))
      have heval : ∀ x ∈ E,
          (P z).eval x = (B0 + Polynomial.C z * B1).eval x := by
        intro x hx
        rw [hcoreMatch z hz x hx]
        simp [hB0eval x hx, hB1eval x hx]
      obtain ⟨q, hqdegree, hqshape⟩ :=
        exists_coreQuotient_natDegree_le E (P z)
          (B0 + Polynomial.C z * B1) k s hcard
          (hPdegree z hz) hbaseDegree heval
      refine ⟨q, ?_⟩
      intro _
      exact ⟨hqdegree, by simpa [add_assoc] using hqshape⟩
    · exact ⟨0, fun h ↦ (hz h).elim⟩
  choose Q hQ using hexists
  refine ⟨B0, B1, Q, hB0degree, hB1degree, hB0eval, hB1eval, ?_, ?_⟩
  · intro z hz
    exact (hQ z hz).1
  · intro z hz
    exact (hQ z hz).2
theorem exists_degreeBoundedAffineLine_of_sharedTuple_family_allCard
    {F : Type*} [Field F] [DecidableEq F]
    (T V : Finset F) (G B0 B1 : F[X]) (Q P : F → F[X])
    (U0 U1 : F → F) (s k : ℕ)
    (hTcard : T.card = s + 1)
    (hQdegree : ∀ z ∈ V, (Q z).natDegree ≤ s)
    (hPdegree : ∀ z ∈ V, (P z).natDegree ≤ k)
    (hG : ∀ x ∈ T, G.eval x ≠ 0)
    (hshape : ∀ z ∈ V,
      P z = B0 + Polynomial.C z * B1 + G * Q z)
    (hmatch : ∀ z ∈ V, ∀ x ∈ T,
      (P z).eval x = U0 x + z * U1 x) :
    ∃ p0 p1 : F[X], p0.natDegree ≤ k ∧ p1.natDegree ≤ k ∧
      ∀ z ∈ V, P z = p0 + Polynomial.C z * p1 := by
  by_cases hlarge : 1 < V.card
  · exact exists_degreeBoundedAffineLine_of_sharedTuple_family
      T V G B0 B1 Q P U0 U1 s k hTcard hlarge hQdegree hPdegree
        hG hshape hmatch
  · have hsmall : V.card ≤ 1 := by omega
    rcases Nat.eq_zero_or_pos V.card with hzero | hpos
    · have hV : V = ∅ := Finset.card_eq_zero.mp hzero
      subst V
      exact ⟨0, 0, by simp, by simp, by simp⟩
    · have hone : V.card = 1 := by omega
      obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp hone
      refine ⟨P z, 0, hPdegree z (by simp), by simp, ?_⟩
      intro w hw
      simp only [Finset.mem_singleton] at hw
      subst w
      simp
theorem sharedTupleFiber_card_le_of_noLargeAffineOwnerLine
    {F : Type*} [Field F] [DecidableEq F]
    (E U S T : Finset F) (A : F → Finset F)
    (P Q : F → F[X]) (B0 B1 : F[X]) (U0 U1 : F → F)
    (s k e : ℕ)
    (hT : T ∈ U.powersetCard (s + 1))
    (hdisjoint : Disjoint E U)
    (hQdegree : ∀ z ∈ S, (Q z).natDegree ≤ s)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ k)
    (hshape : ∀ z ∈ S,
      P z = B0 + Polynomial.C z * B1 + coreLocator E * Q z)
    (hoffCoreMatch : ∀ z ∈ S, ∀ x ∈ A z,
      (P z).eval x = U0 x + z * U1 x)
    (hnonalignment : NoLargeAffineOwnerLine S P k e) :
    (S.filter fun z ↦ T ⊆ A z).card ≤ e := by
  have hTsub : T ⊆ U := (Finset.mem_powersetCard.mp hT).1
  have hTcard : T.card = s + 1 := (Finset.mem_powersetCard.mp hT).2
  let V : Finset F := S.filter fun z ↦ T ⊆ A z
  have hVS : V ⊆ S := Finset.filter_subset _ _
  have hG : ∀ x ∈ T, (coreLocator E).eval x ≠ 0 := by
    intro x hx
    apply coreLocator_eval_ne_zero_of_not_mem
    intro hxE
    exact Finset.disjoint_left.mp hdisjoint hxE (hTsub hx)
  have hQdegreeV : ∀ z ∈ V, (Q z).natDegree ≤ s := by
    intro z hz
    exact hQdegree z (hVS hz)
  have hPdegreeV : ∀ z ∈ V, (P z).natDegree ≤ k := by
    intro z hz
    exact hPdegree z (hVS hz)
  have hshapeV : ∀ z ∈ V,
      P z = B0 + Polynomial.C z * B1 + coreLocator E * Q z := by
    intro z hz
    exact hshape z (hVS hz)
  have hmatchV : ∀ z ∈ V, ∀ x ∈ T,
      (P z).eval x = U0 x + z * U1 x := by
    intro z hz x hx
    have hTsubA : T ⊆ A z := (Finset.mem_filter.mp hz).2
    exact hoffCoreMatch z (hVS hz) x (hTsubA hx)
  obtain ⟨p0, p1, hp0, hp1, hline⟩ :=
    exists_degreeBoundedAffineLine_of_sharedTuple_family_allCard
      T V (coreLocator E) B0 B1 Q P U0 U1 s k hTcard
        hQdegreeV hPdegreeV hG hshapeV hmatchV
  exact hnonalignment V hVS p0 p1 hp0 hp1 hline
theorem ownerCard_le_codim24_of_fullOrderCore
    {F : Type*} [Field F] [DecidableEq F]
    (R : Polynomial (Polynomial (Polynomial F)))
    (E U S : Finset F) (A : F → Finset F)
    (P : F → F[X]) (U0 U1 : F → F) (d : ℕ)
    (hEcard : E.card + bchksBoundaryCoreCodimension6400 = 131071)
    (hUcard : U.card = bchksBoundaryTupleAmbient6400)
    (hdisjoint : Disjoint E U)
    (hd : 1 ≤ d)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ 131071)
    (hshift : ∀ x ∈ E,
      Polynomial.Bivariate.shift R (Polynomial.C x)
        (receivedLineAt U0 U1 x) ≠ 0)
    (horder : ∀ x ∈ E,
      BCHKSLocalValuation6400.localOrder
        (Polynomial.Bivariate.shift R (Polynomial.C x)
          (receivedLineAt U0 U1 x)) = d)
    (hsliceDegree : ∀ x ∈ E,
      (zeroXSlice (Polynomial.Bivariate.shift R (Polynomial.C x)
        (receivedLineAt U0 U1 x))).natDegree ≤ d)
    (hlead : ∀ z ∈ S, ∀ x ∈ E,
      Polynomial.eval z
        ((zeroXSlice (Polynomial.Bivariate.shift R (Polynomial.C x)
          (receivedLineAt U0 U1 x))).coeff d) ≠ 0)
    (hroot : ∀ z ∈ S, triEval R z (P z) = 0)
    (hsub : ∀ z ∈ S, A z ⊆ U)
    (hrow : ∀ z ∈ S,
      bchksBoundaryTupleIncidences6400 ≤ (A z).card)
    (hoffCoreMatch : ∀ z ∈ S, ∀ x ∈ A z,
      (P z).eval x = U0 x + z * U1 x)
    (hnonalignment : NoLargeAffineOwnerLine S P 131071
      bchksBoundaryErrors6400) :
    S.card ≤ bchksBoundaryCodim24PerFactorCap6400 := by
  have hcoreMatch := owner_matches_received_on_fullOrderCore
    R E S P U0 U1 d hd hshift horder hsliceDegree hlead hroot
  obtain ⟨B0, B1, Q, hB0degree, hB1degree, hB0eval, hB1eval,
      hQdegree, hshape⟩ :=
    exists_bounded_coreQuotient_family E S P U0 U1 131071
      bchksBoundaryCoreCodimension6400 hEcard hPdegree hcoreMatch
  apply card_le_codim24PerFactorCap_of_tupleFibers U S A hUcard hsub hrow
  intro T hT
  exact sharedTupleFiber_card_le_of_noLargeAffineOwnerLine
    E U S T A P Q B0 B1 U0 U1 bchksBoundaryCoreCodimension6400
      131071 bchksBoundaryErrors6400
      (by simpa [bchksBoundaryTupleSize6400,
        bchksBoundaryCoreCodimension6400] using hT)
      hdisjoint hQdegree hPdegree hshape hoffCoreMatch hnonalignment
end BCHKSFullCoreOwnerBridge6400
end ProximityPrize.SubmissionLower
