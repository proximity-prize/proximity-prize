import ProximityPrize.SubmissionLower.MovingSourceAllSliceCount6814

/-! Actual generic fibres of the retained coordinate channels. The point
certificate, disjoint slice assignment, shared moving budget and weighted
embedding identity are all supplied before the first-cut bound is returned. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePairFirstChannel6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136 RCN156 RCN207 RCN208 RCN244 RCN248 RCN264 RCN313 RCN341 RCN344
open GenericSlicePoints6807 HFreeDir6813 MovingFiberThreeSources6811
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedPointCount6814
open MovingSourceExtendedThickPair6814 MovingSourceCoupledClearing6814

variable {K I E A : Type} [Field K] [CharP K 2130706433]
  [Field E] [IsAlgClosed E] [Algebra (GenericField K) E] [CharP E 2130706433]
  [Algebra (RatFunc (GenericField K)) E] [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] [Fintype A]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree} {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "w" => RCN326.w
local notation "eta" => (algebraMap Ω E)

theorem first_cut_generic_channel
    (S : Stage K I Gamma x 2130706433 flag errorCap stageSupport)
    (hproper : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
    (old : A → FirstTailComponent S) (hold : Function.Injective old)
    (ell : MvPolynomial (Fin 3) Ω) (q : FlagDegree) (hell : PolynomialInFlag q ell)
    (projection : ∀ a, SeparableCoordinate Ω (CoordinateField Ω (old a).1))
    (hvalue : ∀ a, SeparableCoordinate.value Ω (CoordinateField Ω (old a).1) (projection a)=
      coordinateEvaluation Ω (old a).1 ell)
    (hdeg : flag.zOnly+flag.yz+flag.all<2130706433)
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(q.zOnly+q.yz+q.all)<2130706433)
    (SZ : Source S.F) (hleading : ∀ a, SZ.leading (polynomialEmbedding K)∉(old a).1)
    (d : Fin 3) (r v z : ℕ) (hr : 3≤r) (hv : 2≤v)
    (hR : WeightBound residualSWeights S.F (r : ℤ))
    (hYR : WeightBound residualYSWeights S.F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights S.F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree) (hfree : HFreeChannelDir (E:=E) S.F ell C0 d)
    (scale zCap uCap vCap : ℕ)
    (hbound : ∀ Q U : PE, (2 : PE)*U≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag U →
      ExtendedPointBudget eta S.F SZ Q U scale zCap uCap vCap) :
    3*scale*(∑ a, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old a)*
      SeparableCoordinate.degree Ω (CoordinateField Ω (old a).1) (projection a))≤
      scale*flagMixed flag q (hfreeFlagDir d r v z C0)+
        4*(w+1)*(q.zOnly*zCap+q.yz*uCap+q.all*vCap) := by
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
  have hmass := MovingSourceAllSliceCount6814.first_cut_all_slices S hproper
    oldT embT hpoints N q hNq (fun i => (hcert i).2.1)
    (fun i => (hcert i).2.2.2.2) hdeg hmix SZ (fun i => hleading i.1)
    d r v z hr hv hR hYR hAll C0
    (fun D _ sep hFD hND hHD => hfree D sep hFD hND hHD)
    scale zCap uCap vCap hbound
  have hsum := GenericSlicePoints6807.weighted_embedding_sum (E := E) oldPrime
    (fun a => localMultiplicity S (canonicalLocalDVRFamily S hproper) (old a))
  simpa only [oldT,embT,T,SeparableCoordinate.degree,oldPrime,hsum] using hmass


theorem first_cut_coordinate_channel
    (S : Stage K I Gamma x 2130706433 flag errorCap stageSupport)
    (hproper : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
    (old : A → FirstTailComponent S) (hold : Function.Injective old)
    (ell : MvPolynomial (Fin 3) Ω) (q : FlagDegree) (hell : PolynomialInFlag q ell)
    (projection : ∀ a, Coordinate Ω (CoordinateField Ω (old a).1))
    (hvalue : ∀ a, coordinateValue Ω (CoordinateField Ω (old a).1) (projection a)=
      coordinateEvaluation Ω (old a).1 ell)
    (hdeg : flag.zOnly+flag.yz+flag.all<2130706433)
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(q.zOnly+q.yz+q.all)<2130706433)
    (SZ : Source S.F) (hleading : ∀ a, SZ.leading (polynomialEmbedding K)∉(old a).1)
    (d : Fin 3) (r v z : ℕ) (hr : 3≤r) (hv : 2≤v)
    (hR : WeightBound residualSWeights S.F (r : ℤ))
    (hYR : WeightBound residualYSWeights S.F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights S.F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree) (hfree : HFreeChannelDir (E:=E) S.F ell C0 d)
    (scale zCap uCap vCap : ℕ)
    (hbound : ∀ Q U : PE, (2 : PE)*U≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag U →
      ExtendedPointBudget eta S.F SZ Q U scale zCap uCap vCap) :
    3*scale*(∑ a, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old a)*
      coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a))≤
      scale*flagMixed flag q (hfreeFlagDir d r v z C0)+
        4*(w+1)*(q.zOnly*zCap+q.yz*uCap+q.all*vCap) := by
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
  have hb := first_cut_generic_channel (E := E) S hproper old0 hi0 ell q hell
    sep hv0 hdeg hmix SZ (fun a => hleading a.1) d r v z hr hv hR hYR hAll C0 hfree
    scale zCap uCap vCap hbound
  rw [show (∑ a, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old a) *
      coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a)) =
      ∑ a : Alive, weight a.1 * SeparableCoordinate.degree Ω
        (CoordinateField Ω (old0 a).1) (sep a) from hsum]
  exact hb

/-- Both geometry and first-cut aggregation are supplied from actual
coprime Sources. No local slice charge or desired degree sum is assumed. -/
theorem first_cut_weighted_sources
    (S : Stage K I Gamma x 2130706433 flag errorCap stageSupport) (hF : S.F≠0)
    (hproper : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
    (old : A → FirstTailComponent S) (hold : Function.Injective old)
    (ell : MvPolynomial (Fin 3) Ω) (q : FlagDegree) (hell : PolynomialInFlag q ell)
    (projection : ∀ a, Coordinate Ω (CoordinateField Ω (old a).1))
    (hvalue : ∀ a, coordinateValue Ω (CoordinateField Ω (old a).1) (projection a)=
      coordinateEvaluation Ω (old a).1 ell)
    (hdeg : flag.zOnly+flag.yz+flag.all<2130706433)
    (hmix : 2*(flag.zOnly+flag.yz+flag.all)*(q.zOnly+q.yz+q.all)<2130706433)
    (SZ : Source S.F) (hleading : ∀ a, SZ.leading (polynomialEmbedding K)∉(old a).1)
    (d : Fin 3) (r v z : ℕ) (hr : 3≤r) (hv : 2≤v)
    (hR : WeightBound residualSWeights S.F (r : ℤ))
    (hYR : WeightBound residualYSWeights S.F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights S.F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree) (hfree : HFreeChannelDir (E:=E) S.F ell C0 d)
    (hpos : 0<S.F.degreeOf 2) (hsmall : S.F.degreeOf 2<2130706433)
    (SP SQ : Source S.F) (hcop : IsRelPrime SP.P SQ.P)
    (delta : ℕ) (hd : 0<delta) (hP : delta≤SP.d) (hQ : delta≤SQ.d) (hchar : delta≤2130706433)
    (hZchar : SZ.k<2130706433)
    (parent : FlagDegree) (hp : PolynomialInFlag parent (extendedCarrier eta S.F))
    (hunit : 2*(parent.zOnly+parent.yz+parent.all)<2130706433)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag<2130706433) :
    3*(SZ.d*delta)*(∑ a, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old a)*
      coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a))≤
      (SZ.d*delta)*flagMixed flag q (hfreeFlagDir d r v z C0)+
        4*(w+1)*(q.zOnly*(delta*flagMixed parent unitZFlag SZ.flag)+
          q.yz*(SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)+
          q.all*(SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag)) := by
  exact first_cut_coordinate_channel (E:=E) S hproper old hold ell q hell projection hvalue hdeg hmix
    SZ hleading d r v z hr hv hR hYR hAll C0 hfree _ _ _ _
    (fun Q U hden hQflag hUflag => extended_sources_point_budget eta S.F hF hpos hsmall SP SQ hcop delta hd hP hQ
      hchar SZ hZchar parent hp hunit Q U hden hQflag hUflag hz hu)

#print axioms first_cut_generic_channel
#print axioms first_cut_coordinate_channel
#print axioms first_cut_weighted_sources
end
end ProximityPrize.SubmissionLower.MovingSourcePairFirstChannel6814
