import ProximityPrize.SubmissionLower.Fast077
import ProximityPrize.SubmissionLower.PortHighBase
import ProximityPrize.SubmissionLower.PortLow8
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_10R
noncomputable section
open P0 (AnchorModel AnchoredFamily K highPrefix)
open P0_10 (BufferedPair BankVanishes freeShape movingShape fullShape MarkOn band TerminalDivisibility)
open K1_14 (Banks Equation)
open K1_14_3 (Surface Parent ProjectedProduct)
def SurfacePass {w : ℤ} {rows : Banks} {i : Fin 2} (pair : BufferedPair w rows i)
    (q : Surface) : Prop :=
  BankVanishes rows (freeShape w i) q ∧
  BankVanishes rows (movingShape w i) q ∧ K1_14_3R.compatible pair.free pair.moving q
structure RetainedCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} (pairs : ∀ i : Fin 2, BufferedPair M.overhead rows i) where
  kept : Finset K
  subset : kept ⊆ Γ
  paid : (Γ \ kept).card ≤ highPrefix M.overhead
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  initial : ∀ q ∈ parents, (pairs 0).free ∈ q.asIdeal ∧ (pairs 0).moving ∈ q.asIdeal
  survives : ∀ q ∈ parents, SurfacePass (pairs 1) q
  terminal : ∀ q ∈ parents, BankVanishes rows (fullShape M.overhead) q
  covers : ∀ γ ∈ kept, ∃ q ∈ parents, MarkOn M F q γ
  equation : Equation
  projected : ProjectedProduct parents equation
  y_bound : equation.natDegree ≤ (band M.overhead).yBound
  divides : TerminalDivisibility M.overhead rows equation
end
end P0_10R
namespace P0_10R.Bridge
noncomputable section
open P0 (AnchorModel AnchoredFamily agreement p K t)
open P0_10 (BufferedPair)
open K1_14 (Banks Equation Jet Shape)
open K1_14_2 (Ambient ODE OnJet SmallRootCurve OnRoot endpointDegree)
open K1_14_2_2 (Active Fits)
open Polynomial
def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)
def initialCap : Fin 4 → ℕ := ![5548, 125234, 577116, 5169640]
def initialE₀ : ℕ := 6242936
def initialFee : ℕ := (p+1)*577116 + initialE₀ + 5548 + (p+1)*(1036+4990)
structure InitialCover {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (P Q : Jet) (freeFixed movingFixed : ODE) where
  parents : Finset (Ideal Ambient)
  active : ∀ I ∈ parents, Active I
  height_two : ∀ I ∈ parents, I.height = 2
  initial : ∀ I ∈ parents, K1_14_2.toJet P ∈ I ∧ K1_14_2.toJet Q ∈ I
  masses : Fits parents initialCap
  direct : Finset K
  paid : direct.card ≤ initialFee
  cover : ∀ γ ∈ Γ, γ ∈ direct ∨ K1_14_2.fixedAt freeFixed (F.scalar γ) = 0 ∨
    K1_14_2.fixedAt movingFixed (F.scalar γ) = 0 ∨ ∃ I ∈ parents, OnParent F I γ
end
end P0_10R.Bridge
namespace P0_10R.Later
noncomputable section
open Polynomial
open P0 (agreement)
open K1_14 (Jet Shape atX jetAt)
open K1_14_3 (Surface Parent MassCap mass JetPlane JetCaps SeedCover fixedAt)
open K1_14_3_2 (AtSurface)
structure InitialCover (P Q : Jet) where
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  initial : ∀ q ∈ parents, P ∈ q.asIdeal ∧ Q ∈ q.asIdeal
  masses : MassCap parents 1643 28355 183584
  jetMass : mass parents .jets ≤ 1221580
  seeds : SeedCover
  seedDegree : seeds.curve.totalDegree ≤ 183584 + 515 + 1857
  seedPoints : seeds.points.card ≤ 1221580
  ordinates : Finset K1_14.FX
  ordinateCount : ordinates.card ≤ 1643
  lowJet : JetPlane
  fixedFree : JetPlane
  fixedMoving : JetPlane
  lowJet_ne : lowJet ≠ 0
  fixedFree_ne : fixedFree ≠ 0
  fixedMoving_ne : fixedMoving ≠ 0
  lowJet_caps : JetCaps lowJet 183584 28355
  fixedFree_caps : JetCaps fixedFree 47 10
  fixedMoving_caps : JetCaps fixedMoving 93 18
  cover : ∀ z S, jetAt P z S = 0 → jetAt Q z S = 0 →
    seeds.Covers z ∨ atX S ∈ ordinates ∨ fixedAt lowJet S = 0 ∨
    fixedAt fixedFree S = 0 ∨ fixedAt fixedMoving S = 0 ∨
    ∃ q ∈ parents, AtSurface q z S
end
end P0_10R.Later
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 900000
namespace P0_10R.Bridge
noncomputable section
open Polynomial
open P0 (AnchorModel AnchoredFamily agreement p lowCutoff)
open P0_10 (JetSource scheduled terminalShape fullShape fullCutoff)
open K1_14 (Banks Shape Jet Equation Seeds FX seedHasse)
open K1_14_2 (Ambient toJet FibreRing mapGenericSeed mapGenericJets eval_toJet generic)
open K1_14_2_2 (Active dual)
open K1_14_3 (Surface Parent SeedClosure SeedField JetField JetClosure JetPlane seedFibreEval
  seedGeneric jetGeneric fixedEmbedding OrderAt ProjectedProduct)
open K1_14_2_6 (genericSeedPoint genericJetPoint)
open private ambientToJet toJet_equiv from ProximityPrize.SubmissionLower.Fast071
open private fibreHom seedMap jetMap seedPoint jetPoint from ProximityPrize.SubmissionLower.Fast069
open private seed_chart toJet_C toJet_y toJet_v toJet_seed jetCoordinates fractionCoordinates
  generic_C generic_Y generic_V seedGeneric_C from ProximityPrize.SubmissionLower.Fast069
def surfaceOf (I : Ideal Ambient) (hI : I.IsPrime) : Surface :=
  ⟨I.comap toJet, hI.comap _⟩
theorem fixed_chart (a b : SeedClosure) :
    (genericJetPoint a b).comp (toJet.comp fixedEmbedding) =
      seedGeneric.comp jetCoordinates.symm.toRingHom := by
  have hV : ((genericJetPoint a b).comp (toJet.comp fixedEmbedding)) (Polynomial.X (R := FX[X])) =
      (seedGeneric.comp jetCoordinates.symm.toRingHom) Polynomial.X := by
    simp [fixedEmbedding, generic_V, toJet_v, genericJetPoint, seedGeneric, generic]
  apply Polynomial.ringHom_ext' _ hV
  have hY : (((genericJetPoint a b).comp (toJet.comp fixedEmbedding)).comp C)
      (Polynomial.X (R := FX)) =
      ((seedGeneric.comp jetCoordinates.symm.toRingHom).comp C) Polynomial.X := by
    simp [fixedEmbedding, generic_Y, toJet_y, genericJetPoint, seedGeneric, generic]
  apply Polynomial.ringHom_ext' _ hY
  ext x
  simp [fixedEmbedding, generic_C, toJet_C, genericJetPoint, seedGeneric_C]
theorem surface_height {I : Ideal Ambient} (hI : I.IsPrime) (hh : I.height = 2) :
    (surfaceOf I hI).asIdeal.height = 2 := by
  change (I.comap toJet).height = 2
  rw [toJet_equiv]
  exact (ambientToJet.symm.height_comap I).trans hh
theorem seed_side_of_active {I : Ideal Ambient} (hI : Active I) :
    ∃ y v, K1_14_3.OnSeedFibre (surfaceOf I hI.prime) y v ∧
      IsSeparable SeedField y ∧ IsSeparable SeedField v := by
  obtain ⟨f, hf, hsep⟩ := @fibreHom mapGenericSeed _ seedMap I hI.prime
    hI.seed_finite hI.seed_size.1 hI.seed_size.2
  refine ⟨f (MvPolynomial.X 0), f (MvPolynomial.X 1), ?_, hsep _, hsep _⟩
  unfold K1_14_3.OnSeedFibre
  rw [← seed_chart, ← RingHom.comap_ker, seedPoint, hf]
  rfl
theorem jet_side_transport {I : Ideal Ambient} (hI : I.IsPrime)
    (a b : SeedClosure) (hjker : RingHom.ker (genericJetPoint a b) = I)
    (ha : IsSeparable SeedField a) (hb : IsSeparable SeedField b) :
    ∃ g : Jet →+* JetClosure,
      g.comp fixedEmbedding = jetGeneric ∧ RingHom.ker g = (surfaceOf I hI).asIdeal ∧
      ∀ i : Fin 2, IsSeparable JetField (g (C (C (MvPolynomial.X i)))) := by
  let e := fractionCoordinates.symm
  let top : JetField →+* JetClosure := algebraMap JetField JetClosure
  let : Algebra SeedField JetClosure := (top.comp e.toRingHom).toAlgebra
  let l : SeedClosure →ₐ[SeedField] JetClosure :=
    IsAlgClosed.lift (R := SeedField) (S := SeedClosure) (M := JetClosure)
  let F := l.toRingHom.comp ((genericJetPoint a b).comp toJet)
  have hscalar (x : SeedField) :
      l (algebraMap SeedField SeedClosure x) = algebraMap JetField JetClosure (e x) := by
    exact l.commutes x
  refine ⟨F, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    change l ((genericJetPoint a b).comp (toJet.comp fixedEmbedding) x) = _
    rw [fixed_chart, RingHom.comp_apply]
    change l (algebraMap SeedField SeedClosure (algebraMap Seeds SeedField
      (jetCoordinates.symm x))) = _
    rw [hscalar]
    change top (e (algebraMap Seeds SeedField (jetCoordinates.symm x))) =
      top (algebraMap JetPlane JetField x)
    apply congrArg top
    apply fractionCoordinates.injective
    rw [RingEquiv.apply_symm_apply]
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap (A := JetPlane)
      (K := JetField) (B := Seeds) (L := SeedField) jetCoordinates.symm x).symm
  · change RingHom.ker (l.toRingHom.comp ((genericJetPoint a b).comp toJet)) = _
    rw [RingHom.ker_comp_of_injective _ l.injective, ← RingHom.comap_ker, hjker]
    rfl
  · have hs (x : SeedClosure) (hx : IsSeparable SeedField x) : IsSeparable JetField (l x) := by
      have hx' : (minpoly SeedField x).Separable := hx
      apply (hx'.map (f := e.toRingHom)).of_dvd
      apply minpoly.dvd
      rw [aeval_def, Polynomial.eval₂_map]
      change (minpoly SeedField x).eval₂ (algebraMap SeedField JetClosure) (l x) = 0
      rw [← aeval_def, aeval_algHom_apply l, minpoly.aeval, map_zero]
    intro i
    fin_cases i
    · change IsSeparable JetField (l ((genericJetPoint a b) (toJet (C (C (MvPolynomial.X 0))))))
      rw [toJet_seed]
      simpa [genericJetPoint] using hs a ha
    · change IsSeparable JetField (l ((genericJetPoint a b) (toJet (C (C (MvPolynomial.X 1))))))
      rw [toJet_seed]
      simpa [genericJetPoint] using hs b hb
theorem parent_of_dual {I : Ideal Ambient} (hI : Active I) (hh : I.height = 2) (hj : dual I) :
    Parent (surfaceOf I hI.prime) := by
  obtain ⟨g, hg, hsep⟩ := @fibreHom mapGenericJets _ jetMap I hI.prime hI.jet_finite hj hI.jet_lt
  have hker : RingHom.ker (genericJetPoint (g (MvPolynomial.X 0)) (g (MvPolynomial.X 1))) = I := by
    rw [jetPoint, hg]
  exact ⟨surface_height hI.prime hh, seed_side_of_active hI,
    jet_side_transport hI.prime _ _ hker (hsep _) (hsep _)⟩
end
end P0_10R.Bridge
end
section
namespace P0_10R.Bridge
theorem donor_2_1 : K1_14_2_2_7_2.c1 :=
  K1_14_2_2_7_2_1.proof
theorem donor_2_2_1 : K1_14_2_2_7_2_2.c1 :=
  K1_14_2_2_7_2_2_1.proof
theorem donor_2_2_2 : K1_14_2_2_7_2_2.c2 :=
  K1_14_2_2_7_2_2_2.proof
theorem donor_2_2_3 : K1_14_2_2_7_2_2.c3 :=
  K1_14_2_2_7_2_2_3.proof
theorem donor_2_2 : K1_14_2_2_7_2.c2 :=
  K1_14_2_2_7_2_2.of_children donor_2_2_1 donor_2_2_2 donor_2_2_3
theorem donor_2_3 : K1_14_2_2_7_2.c3 :=
  K1_14_2_2_7_2_3.proof
theorem donor_2_4 : K1_14_2_2_7_2.c4 :=
  K1_14_2_2_7_2_4.proof
theorem donor_2_5 : K1_14_2_2_7_2.c5 :=
  K1_14_2_2_7_2_5.proof
theorem cut_seed_mass : K1_14_2_2_7.c2 :=
  K1_14_2_2_7_2.of_children donor_2_1 donor_2_2 donor_2_3 donor_2_4 donor_2_5
theorem donor_3_1 : K1_14_2_2_7_3.c1 :=
  K1_14_2_2_7_3_1.proof
theorem donor_3_2 : K1_14_2_2_7_3.c2 :=
  K1_14_2_2_7_3_2.proof
theorem donor_3_3_1_1 : K1_14_2_2_7_3_3_1.c1 :=
  K1_14_2_2_7_3_3_1_1.proof
theorem donor_3_3_1_2 : K1_14_2_2_7_3_3_1.c2 :=
  K1_14_2_2_7_3_3_1_2.proof
theorem donor_3_3_1_3 : K1_14_2_2_7_3_3_1.c3 :=
  K1_14_2_2_7_3_3_1_3.proof
theorem donor_3_3_1_4 : K1_14_2_2_7_3_3_1.c4 :=
  K1_14_2_2_7_3_3_1_4.proof
theorem donor_3_3_1 : K1_14_2_2_7_3_3.c1 :=
  K1_14_2_2_7_3_3_1.of_children donor_3_3_1_1 donor_3_3_1_2 donor_3_3_1_3 donor_3_3_1_4
theorem donor_3_3_2 : K1_14_2_2_7_3_3.c2 :=
  K1_14_2_2_7_3_3_2.proof
theorem donor_3_3 : K1_14_2_2_7_3.c3 :=
  K1_14_2_2_7_3_3.of_children donor_3_3_1 donor_3_3_2
theorem cut_ordinate_mass : K1_14_2_2_7.c3 :=
  K1_14_2_2_7_3.of_children donor_3_1 donor_3_2 donor_3_3
theorem donor_4_1 : K1_14_2_2_7_4.c1 :=
  K1_14_2_2_7_4_1.proof
theorem donor_4_2 : K1_14_2_2_7_4.c2 :=
  K1_14_2_2_7_4_2.proof
theorem donor_4_3 : K1_14_2_2_7_4.c3 :=
  K1_14_2_2_7_4_3.proof
theorem donor_4_4_1 : K1_14_2_2_7_4_4.c1 :=
  K1_14_2_2_7_4_4_1.proof
theorem donor_4_4_2 : K1_14_2_2_7_4_4.c2 :=
  K1_14_2_2_7_4_4_2.proof
theorem donor_4_4_3 : K1_14_2_2_7_4_4.c3 :=
  K1_14_2_2_7_4_4_3.proof
theorem donor_4_4_4 : K1_14_2_2_7_4_4.c4 :=
  K1_14_2_2_7_4_4_4.proof
theorem donor_4_4_5 : K1_14_2_2_7_4_4.c5 :=
  K1_14_2_2_7_4_4_5.proof
theorem donor_4_4_6 : K1_14_2_2_7_4_4.c6 :=
  K1_14_2_2_7_4_4_6.proof
theorem donor_4_4_7_1 : K1_14_2_2_7_4_4_7.c1 :=
  K1_14_2_2_7_4_4_7_1.proof
theorem donor_4_4_7_2 : K1_14_2_2_7_4_4_7.c2 :=
  K1_14_2_2_7_4_4_7_2.proof
theorem donor_4_4_7 : K1_14_2_2_7_4_4.c7 :=
  K1_14_2_2_7_4_4_7.of_children donor_4_4_7_1 donor_4_4_7_2
theorem donor_4_4_8 : K1_14_2_2_7_4_4.c8 :=
  K1_14_2_2_7_4_4_8.proof
theorem donor_4_4 : K1_14_2_2_7_4.c4 :=
  K1_14_2_2_7_4_4.of_children
    donor_4_4_1 donor_4_4_2 donor_4_4_3 donor_4_4_4 donor_4_4_5 donor_4_4_6 donor_4_4_7 donor_4_4_8
theorem cut_constant_count : K1_14_2_2_7.c4 :=
  K1_14_2_2_7_4.of_children donor_4_1 donor_4_2 donor_4_3 donor_4_4
end P0_10R.Bridge
end
section
namespace P0_10R.Bridge
theorem donor_1_1_1 : K1_14_2_4_1_1.c1 :=
  K1_14_2_4_1_1_1.proof
theorem donor_1_1_2 : K1_14_2_4_1_1.c2 :=
  K1_14_2_4_1_1_2.proof
private theorem donor_1_1 : K1_14_2_4_1.c1 :=
  K1_14_2_4_1_1.of_children donor_1_1_1 donor_1_1_2
theorem donor_1_2_1 : K1_14_2_4_1_2.c1 :=
  K1_14_2_4_1_2_1.proof
theorem donor_1_2_2 : K1_14_2_4_1_2.c2 :=
  K1_14_2_4_1_2_2.proof
private theorem donor_1_2 : K1_14_2_4_1.c2 :=
  K1_14_2_4_1_2.of_children donor_1_2_1 donor_1_2_2
theorem donor_1_3_1 : K1_14_2_4_1_3.c1 :=
  K1_14_2_4_1_3_1.proof
theorem donor_1_3_2_1 : K1_14_2_4_1_3_2.c1 :=
  K1_14_2_4_1_3_2_1.proof
theorem donor_1_3_2_2 : K1_14_2_4_1_3_2.c2 :=
  K1_14_2_4_1_3_2_2.proof
theorem donor_1_3_2 : K1_14_2_4_1_3.c2 :=
  K1_14_2_4_1_3_2.of_children donor_1_3_2_1 donor_1_3_2_2
theorem donor_1_3_3_1 : K1_14_2_4_1_3_3.c1 :=
  K1_14_2_4_1_3_3_1.proof
theorem donor_1_3_3_2 : K1_14_2_4_1_3_3.c2 :=
  K1_14_2_4_1_3_3_2.proof
theorem donor_1_3_3_3 : K1_14_2_4_1_3_3.c3 :=
  K1_14_2_4_1_3_3_3.proof
theorem donor_1_3_3 : K1_14_2_4_1_3.c3 :=
  K1_14_2_4_1_3_3.of_children donor_1_3_3_1 donor_1_3_3_2 donor_1_3_3_3
private theorem donor_1_3 : K1_14_2_4_1.c3 :=
  K1_14_2_4_1_3.of_children donor_1_3_1 donor_1_3_2 donor_1_3_3
theorem donor_1_4_1 : K1_14_2_4_1_4.c1 :=
  K1_14_2_4_1_4_1.proof
theorem donor_1_4_2 : K1_14_2_4_1_4.c2 :=
  K1_14_2_4_1_4_2.proof
theorem donor_1_4_3 : K1_14_2_4_1_4.c3 :=
  K1_14_2_4_1_4_3.proof
private theorem donor_1_4 : K1_14_2_4_1.c4 :=
  K1_14_2_4_1_4.of_children donor_1_4_1 donor_1_4_2 donor_1_4_3
theorem donor_1_5_1 : K1_14_2_4_1_5.c1 :=
  K1_14_2_4_1_5_1.proof
theorem donor_1_5_2 : K1_14_2_4_1_5.c2 :=
  K1_14_2_4_1_5_2.proof
private theorem donor_1_5 : K1_14_2_4_1.c5 :=
  K1_14_2_4_1_5.of_children donor_1_5_1 donor_1_5_2
theorem donor_3_1_1 : K1_14_2_4_3_1.c1 :=
  K1_14_2_4_3_1_1.proof
theorem donor_3_1_2 : K1_14_2_4_3_1.c2 :=
  K1_14_2_4_3_1_2.proof
theorem donor_3_1_P0_10RBridgeRootDonors : K1_14_2_4_3.c1 :=
  K1_14_2_4_3_1.of_children donor_3_1_1 donor_3_1_2
theorem donor_3_2_1 : K1_14_2_4_3_2.c1 :=
  K1_14_2_4_3_2_1.proof
theorem donor_3_2_2 : K1_14_2_4_3_2.c2 :=
  K1_14_2_4_3_2_2.proof
theorem donor_3_2_P0_10RBridgeRootDonors : K1_14_2_4_3.c2 :=
  K1_14_2_4_3_2.of_children donor_3_2_1 donor_3_2_2
theorem root_embedding : K1_14_2_4.c3 :=
  K1_14_2_4_3.of_children donor_3_1_P0_10RBridgeRootDonors donor_3_2_P0_10RBridgeRootDonors
end P0_10R.Bridge
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace P0_10R_1
noncomputable section
open P0 (AnchorModel AnchoredFamily K p)
open P0_10R.Bridge (InitialCover OnParent initialCap initialE₀ initialFee)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (SeedCover seed_count joinCovers joinCovers_degree joinCovers_points
  joinCovers_covers scalar_atX_injective)
open scoped BigOperators Classical
open private K1_14_2_2_2_3.jetEquiv jetEquiv_apply from ProximityPrize.SubmissionLower.Fast051
open private properPair_height from ProximityPrize.SubmissionLower.PortHighBase
private theorem section_bound : K1_14_2_2_2.c4 :=
  K1_14_2_2_2_4.of_children K1_14_2_2_2_4_1.proof K1_14_2_2_2_4_2.proof K1_14_2_2_2_4_3.proof
private theorem seed_projection : K1_14_2_2_2.c6 :=
  K1_14_2_2_2_6.of_children K1_14_2_2_2_6_1.proof K1_14_2_2_2_6_2.proof
theorem height_le {I : Ideal Ambient} (hI : I.IsPrime)
    (hdim : ringKrullDim (CoordinateRing I) = 2) : I.height ≤ 2 := by
  let x : PrimeSpectrum Ambient := ⟨I, hI⟩
  have hc : Order.coheight x = 2 := by
    rw [ringKrullDim_quotient] at hdim
    change Order.krullDim (Set.Ici x) = 2 at hdim
    rw [← Order.coheight_eq_krullDim_Ici] at hdim
    exact WithBot.coe_injective hdim
  have hd : ringKrullDim Ambient = 4 := by simp [ringKrullDim_eq_zero_of_field]
  have hh : (↑(Order.height x + Order.coheight x) : WithBot ℕ∞) ≤ ringKrullDim Ambient := by
    rw [ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun y : PrimeSpectrum Ambient =>
      Order.height y + Order.coheight y) x)
  rw [hc, ← x.height_eq_orderHeight, hd] at hh
  have hh' : I.height + 2 ≤ (2 : ℕ∞) + 2 := WithBot.coe_le_coe.mp hh
  exact (ENat.add_le_add_iff_right (by simp : (2 : ℕ∞) ≠ ⊤)).mp hh'
private theorem component_height {P Q : Jet} {I : Ideal Ambient} (hp : ProperPair P Q)
    (hI : I.IsPrime) (hdim : ringKrullDim (CoordinateRing I) = 2)
    (hP : toJet P ∈ I) (hQ : toJet Q ∈ I) : I.height = 2 := by
  let J := I.comap K1_14_2_2_2_3.jetEquiv.toRingHom
  let : J.IsPrime := hI.comap _
  have hP' : P ∈ J := by change K1_14_2_2_2_3.jetEquiv P ∈ I; rwa [jetEquiv_apply]
  have hQ' : Q ∈ J := by change K1_14_2_2_2_3.jetEquiv Q ∈ I; rwa [jetEquiv_apply]
  exact le_antisymm (height_le hI hdim)
    ((K1_14_2_2_2_3.jetEquiv.height_comap I) ▸ properPair_height hp J hP' hQ')
private theorem ordinary_cover (f : Equation) (hi : Irreducible f) (hd : 0 < f.natDegree)
    (hp : f.natDegree < p) :
    ∃ S : Finset (Ideal Ambient),
      (∀ I ∈ S, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ I.height = 2 ∧
        FiniteSections I ∧ toJet (C f) ∈ I) ∧
      Fits S (ordinaryBudget (ordinarySeedDegree f) f.natDegree) ∧
      ∀ z R, atMark f z R = 0 → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨g, a, hclear, hproper, hfCaps, hgCaps⟩ := K1_14_3_4_2.proof f hi hd hp
  obtain ⟨S, hS, hcover⟩ := K1_14_2_2_2_3.proof _ _ hproper
  obtain ⟨hfinite, hfits⟩ := section_bound _ _ hproper
    ⟨0, f.natDegree, 0, ordinarySeedDegree f⟩ ⟨0, f.natDegree, 1, ordinarySeedDegree f⟩
    (Nat.zero_le _) hd hfCaps hgCaps S hS
  refine ⟨S, ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨hprime, hdim, hrow, hcut⟩ := hS I hI
    exact ⟨hprime, hdim, component_height hproper hprime hdim hrow hcut, hfinite I hI, hrow⟩
  · intro k
    have h := hfits k
    fin_cases k <;> simpa [residualBudget, ordinaryBudget, two_mul, Nat.add_mul] using h
  · intro z R hz
    exact hcover z R (by simpa [jetAt, atMark] using hz) (K1_14_3R.chainCutter_zero hclear hz)
end
end P0_10R_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P0_10R_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4 Polynomial
open private factor_caps natDegree_zero_of_factors dvd_of_dvd_residual
  toJet_equiv ambientToJet from ProximityPrize.SubmissionLower.Fast071
structure SharedGcd {P Q : Jet} {s t : Shape} (A : FixedPart P s) (B : FixedPart Q t) where
  ordinary : Equation
  left : Jet
  right : Jet
  ordinary_ne : ordinary ≠ 0
  left_ne : left ≠ 0
  right_ne : right ≠ 0
  left_factor : P = fixedIncl A.equation * (C ordinary * left)
  right_factor : Q = fixedIncl B.equation * (C ordinary * right)
  relativelyPrime : IsRelPrime (toJet left) (toJet right)
  seed_le : seedDegree ordinary ≤ s.U
  ordinate_le : ordinary.natDegree ≤ s.B
  left_caps : RowCaps left (residualShape s (seedDegree ordinary) ordinary.natDegree)
  right_caps : RowCaps right (residualShape t (seedDegree ordinary) ordinary.natDegree)
theorem sharedGcd {P Q : Jet} {s t : Shape} (A : FixedPart P s) (B : FixedPart Q t)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hPs : RowCaps P s) (hQs : RowCaps Q t)
    (hno : K1_14_3.NoMovingCommon P Q) : Nonempty (SharedGcd A B) := by
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D := Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D := Equation)
  let gcdJet : GCDMonoid Jet := UniqueFactorizationMonoid.toGCDMonoid Jet
  let D : Jet := gcdJet.gcd A.residual B.residual
  obtain ⟨L, R, hL, hR, hrel⟩ := @extract_gcd Jet _ gcdJet A.residual B.residual
  change A.residual = D * L at hL
  change B.residual = D * R at hR
  have hF : P = fixedIncl A.equation * (D * L) :=
    A.factorization.trans (congrArg (fixedIncl A.equation * ·) hL)
  have hG : Q = fixedIncl B.equation * (D * R) :=
    B.factorization.trans (congrArg (fixedIncl B.equation * ·) hR)
  have hFL := right_ne_zero_of_mul (hF ▸ hP)
  have hGR := right_ne_zero_of_mul (hG ▸ hQ)
  have hDne := left_ne_zero_of_mul hFL
  have hDdeg : D.natDegree = 0 := by
    apply natDegree_zero_of_factors
    intro F hIrr hfd
    by_contra hpos
    have hleft := hfd.trans (gcdJet.gcd_dvd_left A.residual B.residual)
    have hright := hfd.trans (gcdJet.gcd_dvd_right A.residual B.residual)
    obtain ⟨G, hG⟩ := hno F hIrr (dvd_of_dvd_residual A hleft)
      (dvd_of_dvd_residual B hright) (Nat.pos_of_ne_zero hpos)
    exact A.stripped G (hG ▸ hIrr) (hG ▸ hleft)
  let H := D.coeff 0
  have hD : D = C H := eq_C_of_natDegree_eq_zero hDdeg
  have hH : H ≠ 0 := fun hz => hDne (by rw [hD, hz, map_zero])
  rw [hD] at hF hG
  obtain ⟨hFu, hFb, hLc⟩ := factor_caps hP hH hPs hF
  obtain ⟨_, _, hRc⟩ := factor_caps hQ hH hQs hG
  have hprime : IsRelPrime (toJet L) (toJet R) := by
    have hr := (@gcd_isUnit_iff_isRelPrime Jet _ gcdJet L R).mp hrel
    rw [toJet_equiv]
    intro E hEL hER
    have h1 : ambientToJet E ∣ L := by
      simpa using map_dvd ambientToJet.toRingHom hEL
    have h2 : ambientToJet E ∣ R := by
      simpa using map_dvd ambientToJet.toRingHom hER
    simpa using (hr h1 h2).map ambientToJet.symm.toRingHom
  exact ⟨⟨H, L, R, hH, right_ne_zero_of_mul hFL, right_ne_zero_of_mul hGR,
    hF, hG, hprime, hFu, hFb, hLc, hRc⟩⟩
end
end P0_10R_2
end
