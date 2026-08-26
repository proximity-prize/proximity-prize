import ProximityPrize.SubmissionLower.BCHKSParameters6401

/-!
# A scalable three-owner NTT counterprofile at score 64.01

The order-`2^18` NTT group is partitioned by `x ↦ x^65536` into four
fibres of size `65536`.  Choose three fibre values `t01,t02,t12`, and put a
`54282`-point common locator core inside the fourth fibre.  For its locator
`G`, use the three lifted affine branches

* `f0 = 0`,
* `f1 = G*(t12-t02)*(X^65536-t01)`,
* `f2 = G*(t12-t01)*(X^65536-t02)`.

All three agree on the core; `f0=f1`, `f0=f2`, and `f1=f2` on the three
designated fibres.  A centre that takes the corresponding common value on
each block gives each branch exactly `54282 + 2*65536 = 185354`
agreements.  The lifted degree is only `119818 < 131072`.

Thus a fixed-NTT three-owner intersection matrix need not have full rank;
total row surplus alone cannot prove list size at most two.  This file
records the exact arithmetic and the affine-branch identities.  Turning the
standard four-fibre fact for the concrete KoalaBear NTT domain into a literal
benchmark list is a separate domain-API adapter.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSNTTThreeListCounterprofile6401

def domainCard6401 : Nat := 262144
def ownerDimension6401 : Nat := 131072
def ownerDegreeCap6401 : Nat := ownerDimension6401 - 1
def quarterFibreCard6401 : Nat := 65536
def commonCoreCard6401 : Nat := 54282
def unusedFourthFibreCard6401 : Nat :=
  quarterFibreCard6401 - commonCoreCard6401
def liftedOwnerDegree6401 : Nat :=
  commonCoreCard6401 + quarterFibreCard6401
def constructedAgreementCard6401 : Nat :=
  commonCoreCard6401 + 2 * quarterFibreCard6401
def constructedPairIntersection6401 : Nat :=
  commonCoreCard6401 + quarterFibreCard6401
def constructedLocalRowMass6401 : Nat :=
  2 * commonCoreCard6401 + 3 * quarterFibreCard6401
def requiredThreeOwnerRowMass6401 : Nat :=
  3 * bchksAgreements6401 - domainCard6401

theorem ntt_threeList_profile_exact6401 :
    4 * quarterFibreCard6401 = domainCard6401 ∧
      unusedFourthFibreCard6401 = 11254 ∧
      commonCoreCard6401 + 3 * quarterFibreCard6401 +
          unusedFourthFibreCard6401 = domainCard6401 ∧
      liftedOwnerDegree6401 = 119818 ∧
      liftedOwnerDegree6401 ≤ ownerDegreeCap6401 ∧
      constructedAgreementCard6401 = bchksAgreements6401 ∧
      domainCard6401 - constructedAgreementCard6401 =
        bchksErrors6401 ∧
      constructedPairIntersection6401 = 119818 ∧
      constructedPairIntersection6401 ≤ ownerDegreeCap6401 ∧
      constructedLocalRowMass6401 = 305172 ∧
      requiredThreeOwnerRowMass6401 = 293918 ∧
      constructedLocalRowMass6401 - requiredThreeOwnerRowMass6401 =
        unusedFourthFibreCard6401 := by
  norm_num [quarterFibreCard6401, domainCard6401,
    unusedFourthFibreCard6401, commonCoreCard6401,
    liftedOwnerDegree6401, ownerDegreeCap6401, ownerDimension6401,
    constructedAgreementCard6401, bchksAgreements6401,
    bchksErrors6401, constructedPairIntersection6401,
    constructedLocalRowMass6401, requiredThreeOwnerRowMass6401]

section AffineBranches

variable {F : Type*} [Field F]

def branch0 (_t01 _t02 _t12 _T : F) : F := 0
def branch1 (t01 t02 t12 T : F) : F :=
  (t12 - t02) * (T - t01)
def branch2 (t01 t02 t12 T : F) : F :=
  (t12 - t01) * (T - t02)

theorem branch01_equal_at_t01 (t01 t02 t12 : F) :
    branch0 t01 t02 t12 t01 = branch1 t01 t02 t12 t01 := by
  simp [branch0, branch1]

theorem branch02_equal_at_t02 (t01 t02 t12 : F) :
    branch0 t01 t02 t12 t02 = branch2 t01 t02 t12 t02 := by
  simp [branch0, branch2]

theorem branch12_equal_at_t12 (t01 t02 t12 : F) :
    branch1 t01 t02 t12 t12 = branch2 t01 t02 t12 t12 := by
  simp [branch1, branch2]
  ring

def liftedValue (G phi : F → F) (j : Fin 3)
    (t01 t02 t12 x : F) : F :=
  G x * (if j = 0 then branch0 t01 t02 t12 (phi x)
    else if j = 1 then branch1 t01 t02 t12 (phi x)
    else branch2 t01 t02 t12 (phi x))

theorem lifted_all_equal_on_core (G phi : F → F)
    (t01 t02 t12 x : F) (hx : G x = 0) :
    liftedValue G phi 0 t01 t02 t12 x =
        liftedValue G phi 1 t01 t02 t12 x ∧
      liftedValue G phi 0 t01 t02 t12 x =
        liftedValue G phi 2 t01 t02 t12 x := by
  simp [liftedValue, hx]

theorem lifted01_equal_on_fibre (G phi : F → F)
    (t01 t02 t12 x : F) (hx : phi x = t01) :
    liftedValue G phi 0 t01 t02 t12 x =
      liftedValue G phi 1 t01 t02 t12 x := by
  simp [liftedValue, hx, branch0, branch1]

theorem lifted02_equal_on_fibre (G phi : F → F)
    (t01 t02 t12 x : F) (hx : phi x = t02) :
    liftedValue G phi 0 t01 t02 t12 x =
      liftedValue G phi 2 t01 t02 t12 x := by
  simp [liftedValue, hx, branch0, branch2]

theorem lifted12_equal_on_fibre (G phi : F → F)
    (t01 t02 t12 x : F) (hx : phi x = t12) :
    liftedValue G phi 1 t01 t02 t12 x =
      liftedValue G phi 2 t01 t02 t12 x := by
  change G x * branch1 t01 t02 t12 (phi x) =
    G x * branch2 t01 t02 t12 (phi x)
  rw [hx, branch12_equal_at_t12]

end AffineBranches

/-! At the `n=16,k=8,a=10` analogue the same construction has fibre size
`4`, core size `2`, lifted degree `6`, and three owners.  Exhaustively
interpolating every `8`-subset over `F_97` gives exactly those three close
polynomials for this centre.  Over the unusually tiny field `F_17`, the same
centre has list size `15`, illustrating a small-field artefact rather than a
scalable rank theorem. -/

theorem smallAnalogue_parameters_exact :
    2 + 2 * 4 = 10 ∧ 2 + 4 = 6 ∧ 6 < 8 ∧
      2 + 3 * 4 + 2 = 16 := by
  norm_num

end BCHKSNTTThreeListCounterprofile6401
end ProximityPrize.SubmissionLower
