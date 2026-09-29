import ProximityPrize.SubmissionLower.MovingSourceOuterAllSlices6814

/-! The outer joint count consumes actual common coordinate projections.
Generic fibres, their isolation and multiplicities are constructed here.
Constant coordinates contribute zero and are retained correctly. -/
namespace ProximityPrize.SubmissionLower.MovingSourceOuterChannel6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136 RCN156 RCN207 RCN208 RCN244 RCN248 RCN264 RCN313 RCN341 RCN344
open GenericSlicePoints6807 HFreeDir6813 MovingFiberThreeSources6811
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedMovingDegrees6814
open MovingSourceExtendedPointCount6814 MovingSourceOuterAllSlices6814

variable {K I E A : Type} [Field K] [CharP K 2130706433]
  [Field E] [IsAlgClosed E] [Algebra (GenericField K) E] [CharP E 2130706433]
  [Algebra (RatFunc (GenericField K)) E] [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] [Fintype A]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {errorCap : ℕ} {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "w" => RCN326.w
local notation "eta" => (algebraMap Ω E)

theorem outer_first_cut_generic_channel
    (Gamma : A → Finset K) (flag : A → FlagDegree)
    (S : ∀ a, Stage K I (Gamma a) x 2130706433 (flag a) errorCap stageSupport)
    (F : MvPolynomial (Fin 4) K) (hF : F≠0) (hSF : ∀ a, (S a).F=F)
    (parent : FlagDegree) (hparent : PolynomialInFlag parent (frozenCarrier eta F))
    (hproper : ∀ a, ¬(S a).G∣globalTailCut (polynomialEmbedding K) (S a).F (w+1))
    (old : ∀ a, FirstTailComponent (S a)) (hold : Function.Injective (fun a => (old a).1))
    (ell : MvPolynomial (Fin 3) Ω) (q : FlagDegree) (hell : PolynomialInFlag q ell)
    (projection : ∀ a, SeparableCoordinate Ω (CoordinateField Ω (old a).1))
    (hvalue : ∀ a, SeparableCoordinate.value Ω (CoordinateField Ω (old a).1) (projection a)=
      coordinateEvaluation Ω (old a).1 ell)
    (hdeg : parent.zOnly+parent.yz+parent.all<2130706433)
    (hmix : 2*(parent.zOnly+parent.yz+parent.all)*(q.zOnly+q.yz+q.all)<2130706433)
    (SZ : Source F) (hleading : ∀ a, SZ.leading (polynomialEmbedding K)∉(old a).1)
    (d : Fin 3) (r v z : ℕ) (hr : 3≤r) (hv : 2≤v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree) (hfree : HFreeChannelDir (E:=E) F ell C0 d)
    (scale zCap uCap vCap : ℕ)
    (hbound : ∀ Q U : PE, (2 : PE)*U≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag U →
      ExtendedPointBudget eta F SZ Q U scale zCap uCap vCap) :
    3*scale*(∑ a, localMultiplicity (S a) (canonicalLocalDVRFamily (S a) (hproper a)) (old a)*
      SeparableCoordinate.degree Ω (CoordinateField Ω (old a).1) (projection a))≤
      scale*flagMixed parent q (hfreeFlagDir d r v z C0)+
        4*(w+1)*(q.zOnly*zCap+q.yz*uCap+q.all*vCap) := by
  classical
  let oldPrime := fun a => (old a).1
  letI : ∀ a : A, Algebra (RatFunc Ω) (CoordinateField Ω (oldPrime a)) :=
    fun a => (projection a).embedding.toRingHom.toAlgebra
  letI : ∀ a : A, IsScalarTower Ω (RatFunc Ω) (CoordinateField Ω (oldPrime a)) :=
    fun a => IsScalarTower.of_algebraMap_eq fun c => ((projection a).embedding.commutes c).symm
  letI : ∀ a : A, FiniteDimensional (RatFunc Ω) (CoordinateField Ω (oldPrime a)) := fun a => (projection a).finite
  letI : ∀ a : A, Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (oldPrime a)) := fun a => (projection a).separable
  let T := (a : A) × (CoordinateField Ω (oldPrime a) →ₐ[RatFunc Ω] E)
  let oldT := fun i : T => old i.1
  let embT := fun i : T => i.2.restrictScalars Ω
  let N := sliceEquation (E := E) ell
  have hpoints : Function.Injective (fun i : T => embeddingPoint (oldT i).1 (embT i)) :=
    commonBaseEmbeddingPoint_injective oldPrime hold
  have hcert (i : T) := GenericSlicePoints6807.embedding_point_certificate (S i.1).G
    (globalTailCut (polynomialEmbedding K) (S i.1).F (w+1))
    (RCN243.regularitySurface (polynomialEmbedding K) (S i.1).F) ell (old i.1) (hvalue i.1) i.2
  have hNq : PolynomialInFlag q N := inFlag_sub_poly (inFlag_const q _) (inFlag_map _ hell)
  have hmass := outer_first_cut_all_slices (fun i : T => Gamma i.1) (fun i : T => flag i.1)
    (fun i : T => S i.1) F hF (fun i => hSF i.1) parent hparent (fun i => hproper i.1)
    oldT embT hpoints N q hNq (fun i => (hcert i).2.1) (fun i => (hcert i).2.2.2.2)
    hdeg hmix SZ (fun i => hleading i.1) d r v z hr hv hR hYR hAll C0
    (fun D _ sep hFD hND hHD => hfree D sep hFD hND hHD) scale zCap uCap vCap hbound
  have hsum := GenericSlicePoints6807.weighted_embedding_sum (E := E) oldPrime
    (fun a => localMultiplicity (S a) (canonicalLocalDVRFamily (S a) (hproper a)) (old a))
  simpa only [oldT,embT,T,SeparableCoordinate.degree,oldPrime,hsum] using hmass

theorem outer_first_cut_coordinate_channel
    (Gamma : A → Finset K) (flag : A → FlagDegree)
    (S : ∀ a, Stage K I (Gamma a) x 2130706433 (flag a) errorCap stageSupport)
    (F : MvPolynomial (Fin 4) K) (hF : F≠0) (hSF : ∀ a, (S a).F=F)
    (parent : FlagDegree) (hparent : PolynomialInFlag parent (frozenCarrier eta F))
    (hproper : ∀ a, ¬(S a).G∣globalTailCut (polynomialEmbedding K) (S a).F (w+1))
    (old : ∀ a, FirstTailComponent (S a)) (hold : Function.Injective (fun a => (old a).1))
    (ell : MvPolynomial (Fin 3) Ω) (q : FlagDegree) (hell : PolynomialInFlag q ell)
    (projection : ∀ a, Coordinate Ω (CoordinateField Ω (old a).1))
    (hvalue : ∀ a, coordinateValue Ω (CoordinateField Ω (old a).1) (projection a)=
      coordinateEvaluation Ω (old a).1 ell)
    (hdeg : parent.zOnly+parent.yz+parent.all<2130706433)
    (hmix : 2*(parent.zOnly+parent.yz+parent.all)*(q.zOnly+q.yz+q.all)<2130706433)
    (SZ : Source F) (hleading : ∀ a, SZ.leading (polynomialEmbedding K)∉(old a).1)
    (d : Fin 3) (r v z : ℕ) (hr : 3≤r) (hv : 2≤v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree) (hfree : HFreeChannelDir (E:=E) F ell C0 d)
    (scale zCap uCap vCap : ℕ)
    (hbound : ∀ Q U : PE, (2 : PE)*U≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag U →
      ExtendedPointBudget eta F SZ Q U scale zCap uCap vCap) :
    3*scale*(∑ a, localMultiplicity (S a) (canonicalLocalDVRFamily (S a) (hproper a)) (old a)*
      coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a))≤
      scale*flagMixed parent q (hfreeFlagDir d r v z C0)+
        4*(w+1)*(q.zOnly*zCap+q.yz*uCap+q.all*vCap) := by
  classical
  let Alive : Set A := {a | ∃ c, projection a=Sum.inr c}
  let sep := fun a : Alive => Classical.choose a.2
  have hsep (a : Alive) : projection a.1=Sum.inr (sep a) := Classical.choose_spec a.2
  let old0 := fun a : Alive => old a.1
  have hi0 : Function.Injective (fun a : Alive => (old0 a).1) := by
    intro a b hh
    exact Subtype.ext (hold hh)
  have hv0 (a : Alive) : SeparableCoordinate.value Ω (CoordinateField Ω (old0 a).1) (sep a)=
      coordinateEvaluation Ω (old0 a).1 ell := by
    have hh := hvalue a.1
    rw [hsep a] at hh
    exact hh
  let weight := fun a => localMultiplicity (S a) (canonicalLocalDVRFamily (S a) (hproper a)) (old a)
  have hsum : (∑ a, weight a*coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a))=
      ∑ a : Alive, weight a.1*SeparableCoordinate.degree Ω (CoordinateField Ω (old0 a).1) (sep a) := by
    apply Finset.sum_congr_set Alive
      (fun a => weight a*coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a))
      (fun a => weight a.1*SeparableCoordinate.degree Ω (CoordinateField Ω (old0 a).1) (sep a))
    · intro a ha
      simp only [hsep ⟨a,ha⟩,coordinateDegree,Sum.elim_inr,old0]
    · intro a ha
      cases hpj : projection a with
      | inl c => simp only [hpj,coordinateDegree,Sum.elim_inl,Nat.mul_zero]
      | inr c => exact (ha ⟨c,hpj⟩).elim
  have hb := outer_first_cut_generic_channel (E := E)
    (fun a : Alive => Gamma a.1) (fun a : Alive => flag a.1) (fun a : Alive => S a.1)
    F hF (fun a => hSF a.1) parent hparent (fun a => hproper a.1) old0 hi0 ell q hell
    sep hv0 hdeg hmix SZ (fun a => hleading a.1) d r v z hr hv hR hYR hAll C0 hfree
    scale zCap uCap vCap hbound
  change 3*scale*(∑ a, weight a*coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a))≤_
  rw [hsum]
  exact hb

#print axioms outer_first_cut_generic_channel
#print axioms outer_first_cut_coordinate_channel
end
end ProximityPrize.SubmissionLower.MovingSourceOuterChannel6814
