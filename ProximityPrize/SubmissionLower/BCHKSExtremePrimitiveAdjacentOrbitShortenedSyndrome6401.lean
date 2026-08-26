import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveAdjacentOrbitFixedError6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveAdjacentOrbitShortenedSyndrome6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusConstantPairEndpoint6401
open BCHKSFrobeniusProjectiveAffineLine6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveFixedLanePunctureSeam6401
open BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
open BCHKSExtremePrimitiveAdjacentOrbitFixedError6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
section FixedAffineClassification
variable {F J : Type*} [Field F] [Fintype F] [DecidableEq F]
theorem fixedAffineValues_many_forces_slope_zero6401
    (sigma : F →+* F) (T : Finset F) (a b : F)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (hlarge : q6401 < T.card)
    (hfixedValues : ∀ z ∈ T, sigma (a + z * b) = a + z * b) :
    b = 0 := by
  by_contra hb
  let f : F → F := fun z ↦ a + z * b
  have hsubset : T.image f ⊆ frobeniusFixedScalars sigma := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    rw [mem_frobeniusFixedScalars]
    exact hfixedValues z hz
  have hinjective : ∀ z ∈ T, ∀ w ∈ T, f z = f w → z = w := by
    intro z _hz w _hw hzw
    have hfactor : (z - w) * b = 0 := by
      dsimp [f] at hzw
      linear_combination hzw
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hb)
  have hcardImage : (T.image f).card = T.card :=
    Finset.card_image_iff.mpr hinjective
  have hcap := Finset.card_le_card hsubset
  rw [hcardImage] at hcap
  omega
theorem fixedAffineVector_many_forces_direction_zero6401
    [DecidableEq J]
    (sigma : F →+* F) (T : Finset F) (a b : J → F)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (hlarge : q6401 < T.card)
    (hfixedValues : ∀ z ∈ T, ∀ j,
      sigma (a j + z * b j) = a j + z * b j) :
    b = 0 := by
  funext j
  exact fixedAffineValues_many_forces_slope_zero6401
    sigma T (a j) (b j) hfixedCard hlarge
      (fun z hz ↦ hfixedValues z hz j)
omit [Fintype F] [DecidableEq F] in
theorem weightedSyndrome_fixed_of_pointwise_fixed6401
    [Fintype J] [DecidableEq J]
    (sigma : F →+* F) (alpha : J ↪ F)
    (hfixedAlpha : ∀ i, sigma (alpha i) = alpha i)
    (y : J → F) (hfixedWord : ∀ i, sigma (y i) = y i)
    (j : Nat) :
    sigma (weightedSyndrome alpha y j) = weightedSyndrome alpha y j := by
  rw [sigma_weightedSyndrome sigma alpha hfixedAlpha y j]
  apply congrArg (fun v : J → F ↦ weightedSyndrome alpha v j)
  funext i
  exact hfixedWord i
end FixedAffineClassification
section SourceShortening
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
abbrev TwoRowGoodIndex6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) :=
  {i : Fin n6401 // i ∉ twoRowSourceBadCoordinates6401 W}
def twoRowGoodAlpha6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) :
    TwoRowGoodIndex6401 W ↪ F where
  toFun i := alpha i.1
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact alpha.injective hij
theorem twoRowGoodAlpha_fixed6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (hfixed : ∀ i, sigma (alpha i) = alpha i) :
    ∀ i, sigma (twoRowGoodAlpha6401 W i) = twoRowGoodAlpha6401 W i :=
  fun i ↦ hfixed i.1
noncomputable def adjacentOrbitShortenedReceivedBase6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (B : F[X]) : TwoRowGoodIndex6401 W → F :=
  fun i ↦ B.eval (alpha i.1) * u0 i.1
noncomputable def adjacentOrbitShortenedReceivedDirection6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (B : F[X]) : TwoRowGoodIndex6401 W → F :=
  fun i ↦ B.eval (alpha i.1) * u1 i.1
theorem adjacentOrbit_shortenedReceivedSyndrome_fixed6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G A B : F[X])
    (hG : G ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B)
    (hadjacent : A = B.map sigma)
    (hzero : R.laneZero6401 =
      Polynomial.C G * A.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * B.map Polynomial.C)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (z : F) (hz : z ∈ R.goodChallenges6401)
    (hGz : G.eval z ≠ 0) (j : Nat)
    (hdegree : (B * Owner z).natDegree + j <
      Fintype.card (TwoRowGoodIndex6401 W) - 1) :
    sigma (weightedSyndrome (twoRowGoodAlpha6401 W)
        (fun i ↦ B.eval (alpha i.1) * (u0 i.1 + z * u1 i.1)) j) =
      weightedSyndrome (twoRowGoodAlpha6401 W)
        (fun i ↦ B.eval (alpha i.1) * (u0 i.1 + z * u1 i.1)) j := by
  let E : TwoRowGoodIndex6401 W → F := fun i ↦
    -(adjacentOrbitWeightedFullError6401 W B z i.1)
  let received : TwoRowGoodIndex6401 W → F := fun i ↦
    B.eval (alpha i.1) * (u0 i.1 + z * u1 i.1)
  have howner :=
    recursiveAdjacentOrbit_weightedError_fixed_off_twoRowPuncture6401
      W R G A B hG hA hB hcoprime hadjacent hzero hone hsigma hfixed
        z hz hGz
  have hEfixed : ∀ i, sigma (E i) = E i := by
    intro i
    dsimp [E]
    rw [map_neg, howner.2.1 i.1 i.2]
  have hdecomposition : ∀ i,
      received i = (B * Owner z).eval (twoRowGoodAlpha6401 W i) + E i := by
    intro i
    dsimp only [received, E, adjacentOrbitWeightedFullError6401,
      fullOwnerError6401, twoRowGoodAlpha6401]
    change B.eval (alpha i.1) * (u0 i.1 + z * u1 i.1) =
      (B * Owner z).eval (alpha i.1) +
        -(B.eval (alpha i.1) *
          ((Owner z).eval (alpha i.1) - (u0 i.1 + z * u1 i.1)))
    rw [Polynomial.eval_mul]
    ring
  have hsyndrome := weightedSyndrome_received_eq_error
    (twoRowGoodAlpha6401 W) (B * Owner z) E received j
      hdecomposition hdegree
  have hEsyndrome := weightedSyndrome_fixed_of_pointwise_fixed6401
    sigma (twoRowGoodAlpha6401 W) (twoRowGoodAlpha_fixed6401 W hfixed)
      E hEfixed j
  change sigma (weightedSyndrome (twoRowGoodAlpha6401 W) received j) =
    weightedSyndrome (twoRowGoodAlpha6401 W) received j
  rw [hsyndrome]
  exact hEsyndrome
end SourceShortening
section ManyOwnerClassification
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
theorem adjacentOrbit_manyOwners_shortenedDirectionSyndrome_zero6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G A B : F[X])
    (hG : G ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B)
    (hadjacent : A = B.map sigma)
    (hzero : R.laneZero6401 =
      Polynomial.C G * A.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * B.map Polynomial.C)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (T : Finset F) (hT : T ⊆ R.goodChallenges6401)
    (hTG : ∀ z ∈ T, G.eval z ≠ 0)
    (hlarge : q6401 < T.card)
    (j : Nat)
    (hdegree : ∀ z ∈ T, (B * Owner z).natDegree + j <
      Fintype.card (TwoRowGoodIndex6401 W) - 1) :
    weightedSyndrome (twoRowGoodAlpha6401 W)
      (adjacentOrbitShortenedReceivedDirection6401 W B) j = 0 := by
  let a := weightedSyndrome (twoRowGoodAlpha6401 W)
    (adjacentOrbitShortenedReceivedBase6401 W B) j
  let b := weightedSyndrome (twoRowGoodAlpha6401 W)
    (adjacentOrbitShortenedReceivedDirection6401 W B) j
  have hfixedValues : ∀ z ∈ T, sigma (a + z * b) = a + z * b := by
    intro z hz
    have hfixedReceived := adjacentOrbit_shortenedReceivedSyndrome_fixed6401
      W R G A B hG hA hB hcoprime hadjacent hzero hone hsigma hfixed
        z (hT hz) (hTG z hz) j (hdegree z hz)
    have hword :
        (fun i : TwoRowGoodIndex6401 W ↦
          B.eval (alpha i.1) * (u0 i.1 + z * u1 i.1)) =
        (fun i ↦ adjacentOrbitShortenedReceivedBase6401 W B i +
          z * adjacentOrbitShortenedReceivedDirection6401 W B i) := by
      funext i
      simp only [adjacentOrbitShortenedReceivedBase6401,
        adjacentOrbitShortenedReceivedDirection6401]
      ring
    rw [hword, weightedSyndrome_affine] at hfixedReceived
    simpa only [a, b] using hfixedReceived
  have hbzero := fixedAffineValues_many_forces_slope_zero6401
    sigma T a b hfixedCard hlarge hfixedValues
  exact hbzero
end ManyOwnerClassification
end BCHKSExtremePrimitiveAdjacentOrbitShortenedSyndrome6401
end ProximityPrize.SubmissionLower
