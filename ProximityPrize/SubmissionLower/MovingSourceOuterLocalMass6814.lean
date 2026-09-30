import ProximityPrize.SubmissionLower.MovingSourceOuterStageFrames6814
namespace ProximityPrize.SubmissionLower.MovingSourceOuterLocalMass6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open ActualSliceMultiplicity6807 ActualFirstCutPole6807 GenericSlicePoints6807
open MovingSourcePairFirstCutPole6814 HFreeDir6813
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper

variable {K I E T : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Fintype T] [Nonempty T]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {p errorCap : ℕ} [CharP (GenericField K) p]
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "w" => RCN326.w
local notation "phiE" => RingHom.comp (algebraMap Ω E) (polynomialEmbedding K)

theorem outer_first_cut_on_prime_slice
    (Gamma : T → Finset K) (flag : T → FlagDegree)
    (S : ∀ i, Stage K I (Gamma i) x p (flag i) errorCap stageSupport)
    (F : MvPolynomial (Fin 4) K) (hF : ∀ i, (S i).F=F)
    (hproper : ∀ i, ¬(S i).G∣globalTailCut (polynomialEmbedding K) (S i).F (w+1))
    (old : ∀ i, FirstTailComponent (S i))
    (emb : ∀ i, CoordinateField Ω (old i).1 →ₐ[Ω] E)
    (hinj : Function.Injective (fun i => embeddingPoint (old i).1 (emb i)))
    (D : Ideal PE) [D.IsPrime] (sep : SeparableLiteralCoordinate D)
    (hpoint : ∀ i, D≤RingHom.ker (MvPolynomial.aeval (embeddingPoint (old i).1 (emb i)) : PE →ₐ[E] E).toRingHom)
    (hcarrier : ∀ i, scalarPolynomialMap Ω E (S i).G∈D)
    (hisolated : scalarPolynomialMap Ω E (globalTailCut (polynomialEmbedding K) F (w+1))∉D)
    (e d cost : ℕ)
    (hpole : surfaceMap phiE F∈D → surfaceMap phiE (polyH K F)∉D →
      ∀ W : Finset (Place E (CoordinateField E D)),
        (d : ℤ)*(∑ nu∈W, RCN187.poleOrder nu.val
          (SecondJetComponentRoots.coefficientMap phiE D (baseNumerator F (w-1))/
            SecondJetComponentRoots.coefficientMap phiE D (polyH K F)^e))≤cost) :
    d*(∑ i, localMultiplicity (S i) (canonicalLocalDVRFamily (S i) (hproper i)) (old i))≤cost := by
  classical
  let A := CoordinateRing E D
  let Lf := CoordinateField E D
  letI := quotientPolynomialAlgebra E D sep.index
  letI := polynomialBaseAlgebra E D sep.index
  letI := rationalBaseAlgebra E D sep.index sep.transcendental
  letI := quotientBaseScalarTower E D sep.index
  letI := quotientFractionScalarTower E D sep.index
  letI := polynomialRationalScalarTower E D sep.index sep.transcendental
  letI := rationalBaseScalarTower E D sep.index sep.transcendental
  letI : FiniteDimensional (RatFunc E) Lf := sep.finite
  letI : Algebra.IsSeparable (RatFunc E) Lf := sep.separable
  let i0 : T := Classical.choice inferInstance
  let ev := SecondJetComponentRoots.coefficientMap phiE D
  let evalPoint := fun i => pointHom E D (slicePoint (S i) (old i) (emb i) D (hpoint i))
  let mu := fun i => localMultiplicity (S i) (canonicalLocalDVRFamily (S i) (hproper i)) (old i)
  let a : A := firstTailInSlice (S i0) D
  let H : A := originalToSlice (K := K) D (polyH K F)
  let c : A := firstTailScalarInSlice (K := K) D
  let b : A := c*H^(e+3)
  let iota : A →+* Lf := algebraMap A Lf
  have haEq (i : T) : a=firstTailInSlice (S i) D := by
    simp only [a,firstTailInSlice,hF]
  have hpi : Function.Injective evalPoint := by
    intro i j hh
    exact hinj (congrArg Subtype.val (pointHom_injective E D hh))
  have hmu : ∀ i, 1≤mu i := fun i => one_le_localMultiplicity (S i) (hproper i) (old i)
  have ha : ∀ i, a∈(RingHom.ker (evalPoint i).toRingHom)^(mu i) := by
    intro i
    rw [haEq i]
    exact actual_first_tail_mem_point_power (S i) (hproper i) (old i) (emb i) D (hpoint i) (hcarrier i)
  have hHpt : ∀ i, evalPoint i H≠0 := by
    intro i
    have hh := original_H_point_ne_zero (S i) (old i) (emb i) D (hpoint i)
    simpa only [hF] using hh
  have hcpt : ∀ i, evalPoint i c≠0 := fun i => firstTailScalar_point_ne_zero D _
  have hb : ∀ i, evalPoint i b≠0 := by
    intro i
    simpa only [b,map_mul,map_pow] using mul_ne_zero (hcpt i) (pow_ne_zero _ (hHpt i))
  have hiota : Function.Injective iota := IsFractionRing.injective A Lf
  have hHi : iota H≠0 := by
    intro hz
    have hh : H=0 := hiota (by simpa only [map_zero] using hz)
    exact hHpt i0 (by rw [hh,map_zero])
  have hci : iota c≠0 := by
    intro hz
    have hh : c=0 := hiota (by simpa only [map_zero] using hz)
    exact hcpt i0 (by rw [hh,map_zero])
  have hai : iota a≠0 := by
    intro hz
    apply firstTailInSlice_ne_zero (S i0) D (by simpa only [hF] using hisolated)
    exact hiota (by simpa only [map_zero] using hz)
  have hbi : iota b≠0 := by
    simpa only [b,map_mul,map_pow] using mul_ne_zero hci (pow_ne_zero _ hHi)
  have hx : iota a/iota b≠0 := div_ne_zero hai hbi
  have hrepr : iota a/iota b=ev (baseNumerator F (w-1))/ev (polyH K F)^e := by
    have hn : a=c*H^3*originalToSlice (K := K) D (baseNumerator F (w-1)) := by
      simpa only [hF] using firstTailInSlice_normal_form (S i0) D
    have hh := normalized_first_tail_identity iota a
      (originalToSlice (K := K) D (baseNumerator F (w-1))) H c e hn hHi hci
    exact hh.trans (by rw [originalToSlice_fraction_value,originalToSlice_fraction_value]; rfl)
  have hFd : surfaceMap phiE F∈D := by
    rw [←hF i0,←scalar_surfaceMap]
    exact D.mem_of_dvd (map_dvd (scalarPolynomialMap Ω E) (S i0).G_dvd_surface) (hcarrier i0)
  have hHd : surfaceMap phiE (polyH K F)∉D := by
    intro hm
    have hz := RingHom.mem_ker.mp (hpoint i0 hm)
    change MvPolynomial.eval (embeddingPoint (old i0).1 (emb i0))
      (surfaceMap phiE (polyH K F))=0 at hz
    apply scalar_eval_ne_zero (old i0).1 (emb i0)
      (surfaceMap (polynomialEmbedding K) (polyH K (S i0).F))
      (RCN312.firstTailComponent_regularity_not_mem (S i0) (old i0))
    simpa only [scalar_surfaceMap,hF,MvPolynomial.aeval_eq_eval] using hz
  apply WeightedZeroMass6807.weighted_affine_points_scaled E Lf A
    evalPoint hpi mu hmu a b ha hb hx d cost
  intro W
  change (d : ℤ)*(∑ nu∈W, RCN187.poleOrder nu.val (iota a/iota b))≤(cost : ℤ)
  rw [hrepr]
  exact hpole hFd hHd W

end
end ProximityPrize.SubmissionLower.MovingSourceOuterLocalMass6814
