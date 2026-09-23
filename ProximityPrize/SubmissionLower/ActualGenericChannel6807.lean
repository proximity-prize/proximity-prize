/-
UNCOMPILED. The point and isolation inputs of ActiveSliceAssembly6807 are supplied
by the actual k=0 embedding certificate. No prescribed first-cut inequality is
assumed. The projection is a single polynomial shared by the indexed old primes.
-/
import ProximityPrize.SubmissionLower.ActiveSliceAssembly6807

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

/-- Every coordinate is an actual finite separable map with the same value ell.
Empty indexed families are allowed, and do not require an artificial basepoint. -/
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
/-- The constant branch of Coordinate has degree zero and is excluded BEFORE
forming generic fibres. No finite extension is invented for a constant map. -/
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
