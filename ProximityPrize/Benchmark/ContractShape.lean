/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.Benchmark.TargetUpper
import ProximityPrize.Benchmark.BinaryTargetLower
import ProximityPrize.Benchmark.BinaryTargetUpper

/-!
# What the four contracts need checked

Each track states its own `ProtocolClaim`, and a track and its twin must not
drift apart in what they claim -- only in which profile they claim it over.

Sharing one structure across the tracks would make that agreement definitional,
and an earlier revision of this branch did exactly that. It was reverted on
measurement: the four duplicated structures are about 52 lines and the shared
modules replacing them were 129, so the dedup cost more than it saved, and it
dragged a tail of scaffolding behind it -- theorems pinning that old solutions
still elaborate, and a widening of each track's visible surface (a lower track
could name the upper shape) that needed a guard of its own. Proving the
agreement instead leaves all four contracts byte-identical to what solvers
already built against.

So the shape is stated once, below, and each contract is proved equivalent to it
at its own parameters. Two contracts equivalent to the same shape agree about
what is claimed, and a divergence in any field's statement, order or count fails
to elaborate.

Three further things need checking, and none follows from the shape agreement.

**The vocabulary.** The shapes take already-evaluated `NNReal` values, so they
pass each track's `claimedError`, `reductionTarget` and so on through opaquely
-- a track redefining its own vocabulary would still satisfy its shape theorem.
`rfl` closes that, for exactly the vocabulary which is not profile dependent.

**The geometry.** Nothing above notices a change to a profile *value*: edit
`IRSProfile.domainSize` from `2 ^ 18` to `2 ^ 19` and every claim still
elaborates, while the meaning of the claim and the score it implies have moved.
Pinning the geometry makes that a build error.

No module that states a claim imports this one -- the dependency runs the other
way, so nothing here can affect what a claim means. `ProximityPrize.lean` does
import it, and must: that import is the only thing that gets this file
compiled, so removing it as unused would silently disable every check below
while the build stayed green.

## What each guard covers

Every row below was verified by injecting the change it describes.

"Field" below means a record field of a claim; the algebraic field a profile is
over is called the alphabet, and has its own row.

| Change | shape | vocabulary | geometry | Lean-vs-Python | textual |
| --- | --- | --- | --- | --- | --- |
| record field statement, order or count in one contract | catches | -- | -- | -- | catches |
| the same edit applied to *both* a track and its twin | catches | -- | -- | -- | misses |
| a contract instantiated at the wrong profile value | -- | -- | -- | -- | catches |
| vocabulary redefined in one track | -- | catches | -- | -- | catches |
| profile value edited (e.g. `domainSize`) | -- | -- | catches | catches | misses |
| profile alphabet changed (e.g. `Field`) | -- | -- | catches | misses | misses |
| published metadata drifts from Lean | -- | -- | -- | catches | -- |
| docstring-only edit to one contract | passes | -- | -- | -- | false positive |

The alphabet row is why `Geometry.koala_field`/`binary_field` exist. Lean-vs-Python
misses it because `emit-profile-geometry.lean` reports `field` as a hardcoded
string: that column compares two copies of a string and would stay green while
the underlying type changed. Only the `rfl` pins see it.

Row two is the one that justifies proving anything here. The textual guard in
`scripts/test-benchmark-profiles.py` compares a track only to its twin, so it
detects asymmetry and nothing else: the same edit applied to both files leaves
them byte-equal modulo profile and passes. `LowerShape` is a third, independent
statement of what is being claimed, so changing both contracts without changing
it fails both `Iff`s. Verified -- weakening `admissible` from `Set.Ioo` to
`Set.Ico` in both lower contracts passes the textual guard and fails
`lower_shape` and `binary_lower_shape` in both directions.

Row three is why the textual guard is still carried alongside: a contract could
satisfy its shape theorem while named at the wrong profile value, and only
comparing the two contracts directly sees that.

## What nothing here catches

Editing both contracts identically *is* caught, by the shape theorems above.
What is not is a coordinated change that moves the shape with them: if the
ArkLib pin moves so that `certifiedGammaError` or `ProximityGap.prizeThreshold`
means something new, the contracts and `LowerShape` all change together and
every check here still passes, because they are all stated in the same moved
vocabulary. The score artifacts now record `arklibRev`, `compPolyRev` with its
URL, and `leanToolchain`, so such a move is at least visible after the fact; a
fingerprint over the contract files, the pinned geometry and that revision,
committed beside each version in `challenges.json`, would make it visible
before.
-/

namespace ProximityPrize.Benchmark.ContractShape

open ToyProblem
open scoped NNReal

/-! ## The profile-independent shape of each certificate

Stated over an abstract index type, alphabet and encoder, and taking
already-evaluated `ℝ≥0` values, so that substituting a track's own vocabulary
reproduces exactly the field types that track's contract has. -/

section Lower

variable {ι F : Type} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [BEq F] [LawfulBEq F] [SampleableType F]

/-- One admissible radius at which the executable IRS extractor's certified
combination-round error is at most `target`, scored by the induced spot-check
term `(1 - radius) ^ t`. A smaller `bound` is the stronger claim. -/
structure LowerShape (k s t : ℕ) (domain : ι ↪ F)
    (minRelativeDistance radius target bound : ℝ≥0) : Prop where
  admissible : radius ∈ Set.Ioo (0 : ℝ≥0) minRelativeDistance
  reduction : ToyProblem.Impl.IRS.certifiedGammaError k s domain radius ≤ target
  score : (1 - radius) ^ t ≤ bound

end Lower

section Upper

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- An unsafe-from-here radius for the worst-case winning-challenge density,
scored by the induced spot-check term. The whole admissible suffix is certified,
because no monotonicity theorem is assumed. A larger `bound` is stronger. -/
structure UpperShape {k : ℕ} (t : ℕ) (enc : (Fin k → F) →ₗ[F] (ι → A))
    (minRelativeDistance unsafeRadius target bound : ℝ≥0) : Prop where
  admissible : unsafeRadius ∈ Set.Ioo (0 : ℝ≥0) minRelativeDistance
  unsafeAbove : ∀ δ ∈ Set.Ico unsafeRadius minRelativeDistance,
    target < winningSetDensity enc δ
  score : bound ≤ (1 - unsafeRadius) ^ t

end Upper

/-! ## Each contract is that shape at its own parameters

Stated as `Iff` so a divergence in either direction fails to elaborate. Two
contracts equivalent to the same shape agree about what is being claimed, which
is what duplicating the structures put at risk. -/

theorem lower_shape (centiBits numerator denominator : Nat) :
    ProtocolClaim centiBits numerator denominator ↔
      LowerShape IRSProfile.totalDimension IRSProfile.interleaving
        IRSProfile.repetitions IRSProfile.domain IRSProfile.minRelativeDistance
        (claimedRadius numerator denominator) reductionTarget
        (claimedError centiBits) :=
  ⟨fun h => ⟨h.admissible, h.reduction, h.score⟩,
   fun h => ⟨h.admissible, h.reduction, h.score⟩⟩

theorem binary_lower_shape (centiBits numerator denominator : Nat) :
    Binary.ProtocolClaim centiBits numerator denominator ↔
      LowerShape BinaryIRSProfile.totalDimension BinaryIRSProfile.interleaving
        BinaryIRSProfile.repetitions BinaryIRSProfile.domain
        BinaryIRSProfile.minRelativeDistance
        (Binary.claimedRadius numerator denominator) Binary.reductionTarget
        (Binary.claimedError centiBits) :=
  ⟨fun h => ⟨h.admissible, h.reduction, h.score⟩,
   fun h => ⟨h.admissible, h.reduction, h.score⟩⟩

theorem upper_shape (centiBits unsafeIndex : Nat) :
    Upper.ProtocolClaimUpper centiBits unsafeIndex ↔
      UpperShape IRSProfile.repetitions IRSProfile.encoder
        IRSProfile.minRelativeDistance (Upper.claimedUnsafeRadius unsafeIndex)
        Upper.epsilonStar ((2 : ℝ≥0) ^ (-((centiBits : ℝ) / 100))) :=
  ⟨fun h => ⟨h.admissible, h.unsafeAbove, h.score⟩,
   fun h => ⟨h.admissible, h.unsafeAbove, h.score⟩⟩

theorem binary_upper_shape (centiBits unsafeIndex : Nat) :
    Binary.Upper.ProtocolClaimUpper centiBits unsafeIndex ↔
      UpperShape BinaryIRSProfile.repetitions BinaryIRSProfile.encoder
        BinaryIRSProfile.minRelativeDistance
        (Binary.Upper.claimedUnsafeRadius unsafeIndex) Binary.Upper.epsilonStar
        ((2 : ℝ≥0) ^ (-((centiBits : ℝ) / 100))) :=
  ⟨fun h => ⟨h.admissible, h.unsafeAbove, h.score⟩,
   fun h => ⟨h.admissible, h.unsafeAbove, h.score⟩⟩

/-! ## The profile-independent vocabulary agrees

The shape theorems above prove each contract is wired to its parameters the same
way, but they say nothing about whether those parameters *mean* the same thing:
they pass `claimedError centiBits` through opaquely, so a track redefining its
own `claimedError` would still satisfy its shape theorem.

Closing that gap is `rfl`, for exactly the vocabulary that is not profile
dependent. `claimedUnsafeRadius` is absent on purpose — it is
`ProximityGap.gridPt` over each track's own `Index`, so the two genuinely differ
and must. -/

theorem claimedRadius_agree (numerator denominator : Nat) :
    claimedRadius numerator denominator =
      Binary.claimedRadius numerator denominator := rfl

theorem claimedError_agree (centiBits : Nat) :
    claimedError centiBits = Binary.claimedError centiBits := rfl

theorem reductionTarget_agree : reductionTarget = Binary.reductionTarget := rfl

theorem epsilonStar_agree :
    Upper.epsilonStar = Binary.Upper.epsilonStar := rfl

/-! ## The profile geometry is pinned

Neither the shape theorems nor the textual guard notices a change to a *profile
value*: edit `IRSProfile.repetitions` from 128 to 64 and both still pass, because
the contract references the symbol and the contract files are untouched. Yet the
meaning of the claim, and the score it implies, have changed.

Pin the geometry so that edit is a build error instead. `scripts/check-profile-geometry.py`
checks the same numbers against the ones `benchmark_profiles.py` publishes in the
score artifact, so the released metadata cannot describe a geometry the
formalisation does not have. -/

namespace Geometry

theorem koala_totalDimension : IRSProfile.totalDimension = 2 ^ 20 := rfl
theorem koala_interleaving : IRSProfile.interleaving = 8 := rfl
theorem koala_baseDimension : IRSProfile.baseDimension = 2 ^ 17 := rfl
theorem koala_domainSize : IRSProfile.domainSize = 2 ^ 18 := rfl
theorem koala_repetitions : IRSProfile.repetitions = 128 := rfl
theorem koala_cardIndex : Fintype.card IRSProfile.Index = 2 ^ 18 :=
  IRSProfile.card_index

theorem binary_totalDimension : BinaryIRSProfile.totalDimension = 2 ^ 26 := rfl
theorem binary_interleaving : BinaryIRSProfile.interleaving = 64 := rfl
theorem binary_baseDimension : BinaryIRSProfile.baseDimension = 2 ^ 20 := rfl
theorem binary_domainSize : BinaryIRSProfile.domainSize = 2 ^ 21 := rfl
theorem binary_repetitions : BinaryIRSProfile.repetitions = 128 := rfl
theorem binary_cardIndex : Fintype.card BinaryIRSProfile.Index = 2 ^ 21 :=
  BinaryIRSProfile.card_index

/-! The alphabet itself, which the numerals above cannot pin.

`scripts/emit-profile-geometry.lean` reports `field` as a hardcoded string, so
that key is compared against `benchmark_profiles.py`'s own hardcoded string --
agreement between two copies, not a fact about Lean. These two close it: the
type a profile is actually over cannot change while they typecheck. -/

theorem koala_field : IRSProfile.Field = KoalaBear.Ext6 := rfl
theorem binary_field : BinaryIRSProfile.Field = BF64.Ext3 := rfl

/-- Each scalar row really is the total dimension split across the lanes. -/
theorem koala_rows : IRSProfile.totalDimension / IRSProfile.interleaving =
    IRSProfile.baseDimension := IRSProfile.totalDimension_div_interleaving

theorem binary_rows :
    BinaryIRSProfile.totalDimension / BinaryIRSProfile.interleaving =
      BinaryIRSProfile.baseDimension :=
  BinaryIRSProfile.totalDimension_div_interleaving

/-- Rate 1/2, as the published `alphabetRate` asserts. -/
theorem koala_rate : IRSProfile.domainSize = 2 * IRSProfile.baseDimension := rfl
theorem binary_rate :
    BinaryIRSProfile.domainSize = 2 * BinaryIRSProfile.baseDimension := rfl

end Geometry

end ProximityPrize.Benchmark.ContractShape
