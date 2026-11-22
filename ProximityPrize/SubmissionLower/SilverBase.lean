import ProximityPrize.SubmissionLower.FrontBranch4
set_option autoImplicit true
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P2
noncomputable section
open Polynomial Matrix CoreDefinitions Code FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators NNReal
export P0 (K I Words node p blockLength k Frac Bivar TypeAtMostOne coefficientBlocks
  extendSeed IsCommonGCD atSlope seed liftX twist amplitudeDegree sixNorm columnRank
  threeU threeV sameDirection relationOn)
abbrev Rung := P1.Rung
abbrev target : Rung := ⟨179935,336731609,1073741824,2365,0x3a5b3ea2263e00a,8352383558747982⟩
abbrev agreement := target.agreement
abbrev radiusNumerator := target.numerator
abbrev radiusDenominator := target.denominator
abbrev t : ℕ := blockLength - agreement
abbrev L : ℕ := agreement - k
abbrev heightCap : ℕ := t + 1 - L - 2
def queryRadius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator
def radius : ℝ := queryRadius
def BadFamily (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius
abbrev BadMarkAt := P1.BadMarkAt
abbrev BadMark := BadMarkAt agreement
def ordinary (u : Words) := hankel node (u 0) (u 1) L t
def twoBlock (u : Words) := stacked p node (u 0) (u 1) L t
def stackRank (u : Words) := GenericLayer.genericRank (twoBlock u)
def nullity (u : Words) := GenericLayer.genericNullity (twoBlock u)
def Normal (u : Words) (γ : K) : Prop :=
  ((twoBlock u).map (evalRingHom γ)).rank = stackRank u
structure TwoActive (u : Words) where
  a : ℕ
  b : ℕ
  c : ℕ
  ab : a ≤ b
  active : b ≤ t
  inactive : t < c
  top : c ≤ k
  degreeSum : a + b + c = 2 * k + 2
  nullitySum : nullity u + a + b = 2 * (t + 1)
  level : Strata.HasLevelHilbertFunction
    (fun s j => algebraMap K[X] Frac (Principal.parameterSyndromes p node (u 0) (u 1) s j))
    k a b c
def TwoActive.height {u : Words} (T : TwoActive u) := (k + 1) - T.c
abbrev Relation {u : Words} (T : TwoActive u) :=
  Strata.PolynomialRelationCertificate p node (u 0) (u 1) k T.height
def leftU {u : Words} {T : TwoActive u} (R : Relation T) : Bivar :=
  Principal.assemble (fun j => R.coefficients (0, j))
def leftV {u : Words} {T : TwoActive u} (R : Relation T) : Bivar :=
  Principal.assemble (fun j => R.coefficients (1, j))
def fixedNodes {u : Words} {T : TwoActive u} (R : Relation T) : Finset I := by
  classical
  exact Finset.univ.filter fun i =>
    (leftU R).eval (C (node i)) = 0 ∧ (leftV R).eval (C (node i)) = 0
def InvalidLeft {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  max (leftU R).natDegree (leftV R).natDegree < T.height ∨
    ∃ G : K[X], G ≠ 0 ∧ G.map Polynomial.C ∣ leftU R ∧ G.map Polynomial.C ∣ leftV R ∧
      ¬ G ∣ locator node Finset.univ
structure SaturatedAt {u : Words} {T : TwoActive u} (R : Relation T)
    {γ : K} (M : BadMark u γ) : Prop where
  U_ne : atSlope (leftU R) γ ≠ 0
  V_ne : atSlope (leftV R) γ ≠ 0
  degree_eq : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree =
    T.height
  gcd_errors : ∃ errors : Finset I,
    (∀ i ∈ errors, M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i) ∧
    IsCommonGCD (locator node errors) (atSlope (leftU R) γ) (atSlope (leftV R) γ)
  fixed_errors : ∀ i ∈ fixedNodes R, M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i
  valid : ¬ InvalidLeft R
structure Reduction (u : Words) (T : TwoActive u) (R : Relation T) where
  U : Bivar
  V : Bivar
  output : Bivar
  height : ℕ
  height_eq : height + (fixedNodes R).card = T.height
  max_degree : max U.natDegree V.natDegree = height
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  coprime : IsCoprime (extendSeed U) (extendSeed V)
  U_factor : leftU R = liftX (locator node (fixedNodes R)) * U
  V_factor : leftV R = liftX (locator node (fixedNodes R)) * V
  output_factor : R.output = liftX (locator node (fixedNodes R)) * output
  output_degree : output.degree < (k + height : ℕ)
  deleted_error : ∀ γ, Normal u γ → ∀ M : BadMark u γ, ∀ i ∈ fixedNodes R,
    M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i
structure RankThree (u : Words) (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) where
  rank_eq : columnRank D.U D.V = 3
  α : Fin 2 → K[X]
  β : Fin 2 → K[X]
  a : K[X]
  b : K[X]
  a_ne : a ≠ 0
  b_ne : b ≠ 0
  α_primitive : IsCoprime (α 0) (α 1)
  β_primitive : IsCoprime (β 0) (β 1)
  first_degree : a.natDegree + amplitudeDegree (β 0) (β 1) ≤ D.height
  second_degree : b.natDegree + amplitudeDegree (α 0) (α 1) ≤ D.height
  same_direction : sameDirection D.U D.V (threeU a β) (threeV b α)
  output : Bivar
  output_degree : output.degree < (k + D.height : ℕ)
  nodes : relationOn u (fixedNodes R) (threeU a β) (threeV b α) output
abbrev ModelAt := P1.ModelAt
abbrev FamilyAt := @P1.FamilyAt
abbrev ModelAt.overhead := @P1.ModelAt.overhead
abbrev ModelAt.label := @P1.ModelAt.label
abbrev AnchorModel := ModelAt heightCap
abbrev AnchoredFamily {u deleted} (M : AnchorModel u deleted) := FamilyAt agreement M
abbrev AnchorModel.overhead {u deleted} (M : AnchorModel u deleted) := ModelAt.overhead M
abbrev AnchorModel.label {u deleted} (M : AnchorModel u deleted) := ModelAt.label M
abbrev HighRow := P1.HighRow
inductive HighBand where
  | h2366
  | h2380
  | h2400
  | h2420
  | h2440
  | h2450
  | h2460
  | h2480
  | h2500
  | h2520
  | h2530
  | h2540
  | h2550
  | h2560
  | h2570
  | h2585
  | h2590
  | h2600
  | h2601
  | h2611
  | h2621
  | h2640
  | h2670
  | h2700
  | h2750
  | h2800
  | h2900
  | h2950
  | h2980
  | h3000
  | h3050
  | h3100
  | h3200
  | h3400
  | h3555
  | h4000
  | h4800
  | h7745
  | h8000
  | h14500
  | h21448
  | h24000
  | h28300
  | h32411
def HighBand.row : HighBand → HighRow
  | .h2366 => ⟨2366,2379,93115474939138867,0x2527a38f00982c1⟩
  | .h2380 => ⟨2380,2399,86963514617499853,0x1fccf32e289515b⟩
  | .h2400 => ⟨2400,2419,80141144427743360,0x1cdd60170fdc3a5⟩
  | .h2420 => ⟨2420,2439,75622379684181559,0x1ba53a4844c18cf⟩
  | .h2440 => ⟨2440,2449,0xec6c9a01c501b4,0x16f8c08dfd144a0⟩
  | .h2450 => ⟨2450,2459,0xdf784c422b4446,95031637448831224⟩
  | .h2460 => ⟨2460,2479,0xd400aa56489568,87684038095193899⟩
  | .h2480 => ⟨2480,2499,0xc06b218c0e0594,73878593397754386⟩
  | .h2500 => ⟨2500,2519,0xae37b01afebac5,0xe7a9e01bb2e1cb⟩
  | .h2520 => ⟨2520,2529,0x97db23e85cf884,0xc76b58e77616e5⟩
  | .h2530 => ⟨2530,2539,0x8f4bd87e5f1747,0xba123f2a591e67⟩
  | .h2540 => ⟨2540,2549,0x87eccc7b933ab2,0xab638004c86172⟩
  | .h2550 => ⟨2550,2559,0x815ca68fc615d8,0xa0c4961e9227e7⟩
  | .h2560 => ⟨2560,2569,0x7b35caa13aa40d,0x94e4eee879f5fb⟩
  | .h2570 => ⟨2570,2584,0x75e6d9cedc8b78,0x8b925e6d61c3ef⟩
  | .h2585 => ⟨2585,2589,0x6e3d4eba25800e,0x7f9bedcfbffab2⟩
  | .h2590 => ⟨2590,2599,0x6beedc13cf3fce,0x7b4364c3ac8d1e⟩
  | .h2600 => ⟨2600,2600,0x67e2d7a116990b,0x742f5f37049655⟩
  | .h2601 => ⟨2601,2610,0x5e7d279c5cee1e,0x7864caf748b232⟩
  | .h2611 => ⟨2611,2620,0x5abc7f01347485,0x716683048d043d⟩
  | .h2621 => ⟨2621,2639,0x576c6e6f8f6fa7,0x6a9e19368e944e⟩
  | .h2640 => ⟨2640,2669,0x5249d9435f23f6,0x5eefb661488c92⟩
  | .h2670 => ⟨2670,2699,0x49f59157b93a46,0x4f9b17715a306e⟩
  | .h2700 => ⟨2700,2749,0x437a3712c2d445,0x442f4f0de3f4c6⟩
  | .h2750 => ⟨2750,2799,0x3b336d17c1cb32,0x35272981f520f4⟩
  | .h2800 => ⟨2800,2899,0x375dab361799d4,0x284ddeae93503a⟩
  | .h2900 => ⟨2900,2949,0x2b6b6c50e8eb3d,7539989889497143⟩
  | .h2950 => ⟨2950,2979,8777438934015614,6750022438537705⟩
  | .h2980 => ⟨2980,2999,8232174646093835,6265299422480654⟩
  | .h3000 => ⟨3000,3049,7920769328756114,5914027083230035⟩
  | .h3050 => ⟨3050,3099,7233131619602069,5133838392304890⟩
  | .h3100 => ⟨3100,3199,5780812131934959,4711544557140173⟩
  | .h3200 => ⟨3200,3399,4609990374200773,0xd4775ea2351fc⟩
  | .h3400 => ⟨3400,3554,0xc2cb28591a32b,0x91b1a34f0449e⟩
  | .h3555 => ⟨3555,3999,0x7bd73fd4c6710,0x7cc99261b72f8⟩
  | .h4000 => ⟨4000,4799,0x3c1dcb06bed3a,0x4e1e3a877504e⟩
  | .h4800 => ⟨4800,7744,456991479392525,705676274027289⟩
  | .h7745 => ⟨7745,7999,723244967547378,471048191238102⟩
  | .h8000 => ⟨8000,14499,651486155753195,425841080879578⟩
  | .h14500 => ⟨14500,21447,47471425797023,0x97983d103a57⟩
  | .h21448 => ⟨21448,23999,21281850144313,78255348716729⟩
  | .h24000 => ⟨24000,28299,19998784942889,63464881996079⟩
  | .h28300 => ⟨28300,32410,18715989025685,51455234429739⟩
  | .h32411 => ⟨32411,33345,3323301173093,58347874659230⟩
end
end P2
end
section
set_option autoImplicit false
namespace P2_4
noncomputable section
open P2 MvPolynomial
def WedgeBounds (h : ℕ) (U V : MvPolynomial (Fin 5) K) : Prop :=
  (L - h) * U.degreeOf 3 ≤ h ∧ (L - h) * U.degreeOf 4 ≤ L ∧
    (L - h) * V.degreeOf 3 ≤ L ∧ (L - h) * V.degreeOf 4 ≤ h
structure IndependentLift {u : Words} {T : TwoActive u} (R : Relation T) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : K1_11_2.OmitsMessages U
  V_omits : K1_11_2.OmitsMessages V
  heights : U.degreeOf 0 ≤ T.height ∧ V.degreeOf 0 ≤ T.height
  bounds : WedgeBounds T.height U V
  primitive : ∀ q : MvPolynomial (Fin 2) K,
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ U →
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ V → IsUnit q
  content : Polynomial K
  content_ne : content ≠ 0
  graphU : K1_11_2.graph p U = Polynomial.C content * leftU R
  graphV : K1_11_2.graph p V = Polynomial.C content * leftV R
structure ReducedPair {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (A : IndependentLift R) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : K1_11_2.OmitsMessages U
  V_omits : K1_11_2.OmitsMessages V
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  U_dvd : U ∣ A.U
  V_dvd : V ∣ A.V
  relPrime : IsRelPrime U V
  height : max (U.degreeOf 0) (V.degreeOf 0) = D.height
  graphU : K1_11_2.graph p U = Polynomial.C A.content * D.U
  graphV : K1_11_2.graph p V = Polynomial.C A.content * D.V
abbrev Puncture := K1_11.Puncture
open K1_11 (sourceWeights scalarWeightY scalarWeightYS scalarWeightT
  contactLift contactWeight contactShift polynomialView scalarImages)
structure Marks (u : Words) (deleted : Finset I) (Γ : Finset K) where
  mark : ∀ γ ∈ Γ, BadMark u γ
  survives : ∀ γ (hγ : γ ∈ Γ) i, i ∈ (mark γ hγ).support → i ∉ deleted
inductive Bank
  | w22 | w22Swapped | w12 | w21 | w13 | w23 | w31 | w32 | w33 | w33Swapped
def Bank.dS : Bank → ℕ
  | .w22 | .w22Swapped | .w21 | .w23 => 2
  | .w12 | .w13 => 1
  | .w31 | .w32 | .w33 | .w33Swapped => 3
def Bank.dT : Bank → ℕ
  | .w22 | .w22Swapped | .w12 | .w32 => 2
  | .w21 | .w31 => 1
  | .w13 | .w23 | .w33 | .w33Swapped => 3
def Bank.s : Bank → ℕ
  | .w12 => 16
  | .w13 => 8
  | .w21 => 10
  | .w22 => 11
  | .w22Swapped => 10
  | .w23 => 8
  | .w31 => 7
  | .w32 => 6
  | .w33 => 6
  | .w33Swapped => 8
def Bank.t : Bank → ℕ
  | .w12 => 10
  | .w13 => 7
  | .w21 => 16
  | .w22 => 10
  | .w22Swapped => 11
  | .w23 => 6
  | .w31 => 8
  | .w32 => 8
  | .w33 => 8
  | .w33Swapped => 6
def Bank.a (b : Bank) : ℕ := b.s + 5 * b.dS
def Bank.b (b : Bank) : ℕ := b.t + 5 * (b.dT - 1)
def Bank.E (b : Bank) : ℕ := b.a + b.b
def Bank.M (b : Bank) : ℕ := (2 * 131071 - 1) * (b.E - 1) + 1
def Bank.zeroFee (b : Bank) : ℕ := b.a + p * b.b
abbrev nodeCut := K1_11.nodeCut
def Bank.relationBounds (b : Bank) (H : ℕ) : Fin 4 → ℕ := ![131071 + H, 1, b.dS, b.dT]
structure ContactInput (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (b : Bank) (H : ℕ) where
  L : MvPolynomial (Fin 5) K
  L_ne : L ≠ 0
  degrees : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = b.relationBounds H j
  order_one : ∀ i : Fin P.N,
    (contactLift contactWeight
      (contactShift (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
        (u 0 (P.index i) ^ p) (u 1 (P.index i) ^ p) L)).natTrailingDegree = 1
  numerator : MvPolynomial (Fin 4) K
  denominator : MvPolynomial (Fin 4) K
  denominator_ne : denominator ≠ 0
  linear : polynomialView L =
    Polynomial.C denominator * Polynomial.X - Polynomial.C numerator
  primitive : (Polynomial.C denominator * Polynomial.X - Polynomial.C numerator).IsPrimitive
  numerator_Y : numerator.weightedTotalDegree scalarWeightY ≤ 1
  denominator_Y : denominator.weightedTotalDegree scalarWeightY ≤ 0
  numerator_S : numerator.weightedTotalDegree scalarWeightYS ≤ b.dS
  denominator_S : denominator.weightedTotalDegree scalarWeightYS ≤ b.dS
  numerator_T : numerator.weightedTotalDegree scalarWeightT ≤ b.dT
  denominator_T : denominator.weightedTotalDegree scalarWeightT ≤ b.dT - 1
abbrev scalarWeightTotal := K1_11.scalarWeightTotal
structure Annihilator {u : Words} {deleted : Finset I} {Γ : Finset K}
    (F : Marks u deleted Γ) (b : Bank) where
  Q : MvPolynomial (Fin 4) K
  nonzero : Q ≠ 0
  degreeY : Q.weightedTotalDegree scalarWeightY ≤ 5
  degreeS : Q.weightedTotalDegree scalarWeightYS ≤ b.a
  degreeT : Q.weightedTotalDegree scalarWeightT ≤ b.b
  degreeTotal : Q.weightedTotalDegree scalarWeightTotal ≤ b.E
  vanishes : ∀ γ (hγ : γ ∈ Γ),
    aeval (scalarImages (F.mark γ hγ).decoder γ (γ ^ p)) Q = 0
structure TaylorChart (u : Words) {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank) (Λ : Finset K) where
  subset : Λ ⊆ Γ
  equation : MvPolynomial (Fin 3) Frac
  equation_ne : equation ≠ 0
  equation_degree : equation.totalDegree ≤ b.E
  numerator : Polynomial (MvPolynomial (Fin 3) Frac)
  numerator_degree : numerator.natDegree ≤ 131071
  denominator : MvPolynomial (Fin 3) Frac
  cut_degree : ∀ i, (nodeCut u P numerator denominator i).totalDegree ≤ b.M
  point : K → Fin 3 → Frac
  slope : ∀ γ ∈ Λ, point γ 1 = algebraMap K Frac γ
  on_equation : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) equation = 0
  regular : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) denominator ≠ 0
  reconstruction : ∀ γ (hγ : γ ∈ Λ),
    numerator.map (MvPolynomial.eval (point γ)) =
      Polynomial.C (MvPolynomial.eval (point γ) denominator) *
        (F.mark γ (subset hγ)).decoder.map (algebraMap K Frac)
end
end P2_4
end
section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace P2_4
noncomputable section
open P2 MvPolynomial
open K1_11_3 (SimpleRoot derivativeChart exists_simple_derivative_at_root)
open private exceptions specializeY yView_degree specializeY_eval specializeY_iterate
  specializeY_derivative from ProximityPrize.SubmissionLower.Fast070
open private centerPoint atCenter atCenter_degree K1_11_3.numerator numerator_degree K1_11_3.denominator
  eval_atCenter pderiv_atCenter numerator_eval_degree denominator_degree reconstruct
  natDegree_le_of_degree_lt_succ derivativeChart_degree from ProximityPrize.SubmissionLower.Fast072
theorem assign {u : Words} {deleted : Finset I} {Γ : Finset K}
    {F : Marks u deleted Γ} {b : Bank} (A : Annihilator F b) :
    ∃ (exceptional : Finset K) (charts : Fin 5 → Finset K),
      exceptional.card ≤ b.zeroFee ∧
      (∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j) ∧
      ∀ j, ∃ hsub : charts j ⊆ Γ, ∀ γ (hγ : γ ∈ charts j),
        SimpleRoot (derivativeChart A.Q j) (F.mark γ (hsub hγ)).decoder γ (γ ^ p) := by
  classical
  obtain ⟨exceptional, hfee, hex⟩ := exceptions A.Q A.nonzero p b.a b.b (by decide)
    (by cases b <;> decide) A.degreeS A.degreeT Γ
  have hassign (γ : K) (hγ : γ ∈ Γ) (hn : γ ∉ exceptional) :
      ∃ j : Fin 5, SimpleRoot (derivativeChart A.Q j) (F.mark γ hγ).decoder γ (γ ^ p) := by
    let f := specializeY A.Q γ (γ ^ p)
    have hdeg : f.natDegree ≤ 5 :=
      (Polynomial.natDegree_map_le).trans ((yView_degree A.Q).le.trans A.degreeY)
    have hroot : f.IsRoot (F.mark γ hγ).decoder :=
      (specializeY_eval A.Q _ γ (γ ^ p)).trans (A.vanishes γ hγ)
    obtain ⟨j, hj, hz, hnz⟩ := exists_simple_derivative_at_root p 5 f
      (hex γ hγ hn) hdeg (by decide) _ hroot
    refine ⟨⟨j,hj⟩, ?_, ?_⟩
    · rw [← specializeY_eval, specializeY_iterate]
      exact hz
    · rw [← specializeY_eval, specializeY_derivative, specializeY_iterate]
      exact hnz
  let charts (j : Fin 5) := Γ.filter fun γ =>
    ∃ hγ : γ ∈ Γ, SimpleRoot (derivativeChart A.Q j) (F.mark γ hγ).decoder γ (γ ^ p)
  refine ⟨exceptional, charts, hfee, ?_, ?_⟩
  · intro γ hγ
    by_cases he : γ ∈ exceptional
    · exact Or.inl he
    · obtain ⟨j,hj⟩ := hassign γ hγ he
      exact Or.inr ⟨j, Finset.mem_filter.mpr ⟨hγ, hγ, hj⟩⟩
  · intro j
    refine ⟨fun _ hγ => (Finset.mem_filter.mp hγ).1, ?_⟩
    intro γ hγ
    obtain ⟨_, h⟩ := (Finset.mem_filter.mp hγ).2
    exact h
private theorem build_chart
    {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank)
    (Λ : Finset K) (hsub : Λ ⊆ Γ) (hne : Λ.Nonempty)
    (G : MvPolynomial (Fin 4) K) (hG : G.weightedTotalDegree scalarWeightTotal ≤ b.E)
    (hroot : ∀ γ (hγ : γ ∈ Λ),
      SimpleRoot G (F.mark γ (hsub hγ)).decoder γ (γ ^ p)) :
    Nonempty (TaylorChart u P F b Λ) := by
  classical
  let point (γ : K) : Fin 3 → Frac := if h : γ ∈ Λ then
    centerPoint (F.mark γ (hsub h)).decoder γ (γ ^ p) else fun _ => 0
  have hpnt (γ : K) (hγ : γ ∈ Λ) :
      point γ = centerPoint (F.mark γ (hsub hγ)).decoder γ (γ ^ p) := by
    simp [point, hγ]
  refine ⟨{
    subset := hsub
    equation := atCenter G
    equation_ne := ?_
    equation_degree := (atCenter_degree G).trans hG
    numerator := K1_11_3.numerator G 131071
    numerator_degree := numerator_degree _ _
    denominator := K1_11_3.denominator G 131071
    cut_degree := ?_
    point := point
    slope := fun γ hγ => by rw [hpnt γ hγ]; rfl
    on_equation := fun γ hγ => by rw [hpnt γ hγ, eval_atCenter, (hroot γ hγ).1, map_zero]
    regular := ?_
    reconstruction := ?_ }⟩
  · obtain ⟨γ, hγ⟩ := hne
    have hn := (hroot γ hγ).2
    intro hz
    apply hn
    apply (IsFractionRing.injective (Polynomial K) Frac)
    rw [map_zero, ← eval_atCenter, ← pderiv_atCenter, hz, map_zero, map_zero]
  · intro i
    unfold nodeCut
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact numerator_eval_degree K1_11_3_1.proof G 131071 b.E (by cases b <;> decide) hG _
    · apply (totalDegree_mul _ _).trans
      have ha : (C (σ := Fin 3) (algebraMap K Frac (u 0 (P.index i))) +
          MvPolynomial.X 1 * C (algebraMap K Frac (u 1 (P.index i)))).totalDegree ≤ 1 := by
        exact (totalDegree_add _ _).trans (max_le (by simp)
          ((totalDegree_mul _ _).trans (by simp)))
      exact Nat.add_le_add (denominator_degree G 131071 b.E hG) ha
  · intro γ hγ
    rw [hpnt γ hγ, K1_11_3.denominator, map_pow, eval_atCenter]
    exact pow_ne_zero _ (fun h => (hroot γ hγ).2
      ((IsFractionRing.injective (Polynomial K) Frac) (h.trans (map_zero _).symm)))
  · intro γ hγ
    rw [hpnt γ hγ]
    apply reconstruct K1_11_3_2.proof
    · exact natDegree_le_of_degree_lt_succ (F.mark γ (hsub hγ)).degree
    · exact (hroot γ hγ).1
    · intro n hn
      have pp := CharP.char_is_prime_of_two_le K p (by decide)
      intro hz
      have hn' := pp.dvd_factorial.mp ((CharP.cast_eq_zero_iff K p _).mp hz)
      exact (not_lt_of_ge (hn'.trans hn)) (by decide)
theorem chart_cover {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} {F : Marks u deleted Γ} {b : Bank} (A : Annihilator F b) :
    ∃ (exceptional : Finset K) (charts : Fin 5 → Finset K),
      exceptional.card ≤ b.zeroFee ∧
      (∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j) ∧
      ∀ j, charts j = ∅ ∨ Nonempty (TaylorChart u P F b (charts j)) := by
  obtain ⟨exceptional, charts, hfee, hcover, hcharts⟩ := assign A
  refine ⟨exceptional, charts, hfee, hcover, fun j => ?_⟩
  rcases (charts j).eq_empty_or_nonempty with he | hn
  · exact Or.inl he
  · obtain ⟨hsub, hroot⟩ := hcharts j
    exact Or.inr (build_chart P F b (charts j) hsub hn (derivativeChart A.Q j)
      ((derivativeChart_degree A.Q j).trans A.degreeTotal) hroot)
end
end P2_4
end
section
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
namespace P2_4
open P2 Finset
open K1_11 (V J)
open private countRow gradeRow count grade contactRow V_affine rational_fee from ProximityPrize.SubmissionLower.PortFrontA
open private
  dims_5_16_10 dims_4_15_8 jets_4_16_10 jets_3_15_8
  dims_5_8_7 dims_4_7_4 jets_4_8_7 jets_3_7_4
  dims_5_10_16 dims_4_8_15 jets_4_10_16 jets_3_8_15
  dims_5_11_10 dims_4_9_8 jets_4_11_10 jets_3_9_8
  dims_5_8_6 dims_4_6_3 jets_4_8_6 jets_3_6_3
  dims_5_7_8 dims_4_4_7 jets_4_7_8 jets_3_4_7
  dims_5_6_8 dims_4_3_6 jets_4_6_8 jets_3_3_6
  dims_4_3_5 jets_3_3_5 from ProximityPrize.SubmissionLower.FrontBranch4
private theorem dims_5_10_11 : count 5 10 11 = 2002 ∧ grade 5 10 11 = 6174 := by
  constructor
  · have r0 : countRow 5 10 11 0 = 627 := by decide
    have r1 : countRow 5 10 11 1 = 500 := by decide
    have r2 : countRow 5 10 11 2 = 378 := by decide
    have r3 : countRow 5 10 11 3 = 264 := by decide
    have r4 : countRow 5 10 11 4 = 161 := by decide
    have r5 : countRow 5 10 11 5 = 72 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 10 11 i) = 6174
    have r0 : gradeRow 5 10 11 0 = 1375 := by decide
    have r1 : gradeRow 5 10 11 1 = 1400 := by decide
    have r2 : gradeRow 5 10 11 2 = 1278 := by decide
    have r3 : gradeRow 5 10 11 3 = 1040 := by decide
    have r4 : gradeRow 5 10 11 4 = 721 := by decide
    have r5 : gradeRow 5 10 11 5 = 360 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
private theorem jets_4_10_11 : J 4 10 11 = 2301 := by
  change (∑ i ∈ range 4, contactRow 4 10 11 i) = 2301
  have r0 : contactRow 4 10 11 0 = 1210 := by decide
  have r1 : contactRow 4 10 11 1 = 680 := by decide
  have r2 : contactRow 4 10 11 2 = 315 := by decide
  have r3 : contactRow 4 10 11 3 = 96 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]
private theorem dims_4_8_9 : count 4 8 9 = 985 ∧ grade 4 8 9 = 2419 := by
  constructor
  · have r0 : countRow 4 8 9 0 = 360 := by decide
    have r1 : countRow 4 8 9 1 = 272 := by decide
    have r2 : countRow 4 8 9 2 = 189 := by decide
    have r3 : countRow 4 8 9 3 = 114 := by decide
    have r4 : countRow 4 8 9 4 = 50 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 8 9 i) = 2419
    have r0 : gradeRow 4 8 9 0 = 630 := by decide
    have r1 : gradeRow 4 8 9 1 = 640 := by decide
    have r2 : gradeRow 4 8 9 2 = 553 := by decide
    have r3 : gradeRow 4 8 9 3 = 396 := by decide
    have r4 : gradeRow 4 8 9 4 = 200 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem jets_3_8_9 : J 3 8 9 = 806 := by
  change (∑ i ∈ range 3, contactRow 3 8 9 i) = 806
  have r0 : contactRow 3 8 9 0 = 504 := by decide
  have r1 : contactRow 3 8 9 1 = 232 := by decide
  have r2 : contactRow 3 8 9 2 = 70 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem dims_4_5_3 : count 4 5 3 = 175 ∧ grade 4 5 3 = 364 := by
  constructor
  · have r0 : countRow 4 5 3 0 = 60 := by decide
    have r1 : countRow 4 5 3 1 = 50 := by decide
    have r2 : countRow 4 5 3 2 = 36 := by decide
    have r3 : countRow 4 5 3 3 = 21 := by decide
    have r4 : countRow 4 5 3 4 = 8 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 5 3 i) = 364
    have r0 : gradeRow 4 5 3 0 = 60 := by decide
    have r1 : gradeRow 4 5 3 1 = 100 := by decide
    have r2 : gradeRow 4 5 3 2 = 100 := by decide
    have r3 : gradeRow 4 5 3 3 = 72 := by decide
    have r4 : gradeRow 4 5 3 4 = 32 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem jets_3_5_3 : J 3 5 3 = 191 := by
  change (∑ i ∈ range 3, contactRow 3 5 3 i) = 191
  have r0 : contactRow 3 5 3 0 = 120 := by decide
  have r1 : contactRow 3 5 3 1 = 55 := by decide
  have r2 : contactRow 3 5 3 2 = 16 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
end P2_4
end
section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace P2_4
noncomputable section
open MvPolynomial
open P2 (heightCap)
open K1_11 (V J filtered filteredMul filteredMul_injective mem_filteredMul_range_iff
  sourceWeights sourceBounds source_filtered_finrank JetSpace jetSpace_finrank sourceToJet
  contactShift contactLift contactWeight contactShift_parameter_weights
  truncated_mul_mem_jet contact_product_not_high_order
  jetSpace_support_bound)
open private exists_kernel_outside from ProximityPrize.SubmissionLower.Fast065
abbrev Multipliers (F : Type*) [Field F] (b : Bank) := JetSpace F 2 (b.s - b.dS) (b.t - b.dT)
variable {F : Type*} [Field F]
structure ContactData (N : ℕ) (L : MvPolynomial (Fin 5) F) (b : Bank) where
  x : Fin N → F
  first : Fin N → F
  firstSlope : Fin N → F
  second : Fin N → F
  secondSlope : Fin N → F
  nonzero : L ≠ 0
  degreeS : L.weightedTotalDegree (sourceWeights 1 2) ≤ b.dS
  degreeT : L.weightedTotalDegree (sourceWeights 1 3) ≤ b.dT
  order_one : ∀ i, (contactLift contactWeight
    (contactShift (x i) (first i) (firstSlope i) (second i) (secondSlope i) L)).natTrailingDegree = 1
variable {N : ℕ} {L : MvPolynomial (Fin 5) F} {b : Bank} {H : ℕ} (D : ContactData N L b)
def ContactData.shifted (i : Fin N) (Q : MvPolynomial (Fin 5) F) :=
  contactShift (D.x i) (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i) Q
private theorem shifted_S (i : Fin N) :
    (D.shifted i L).weightedTotalDegree (sourceWeights 1 2) ≤ b.dS := by
  apply (contactShift_parameter_weights _ _ _ _ _ L).1.trans
  exact D.degreeS
private theorem shifted_T (i : Fin N) :
    (D.shifted i L).weightedTotalDegree (sourceWeights 1 3) ≤ b.dT := by
  apply (contactShift_parameter_weights _ _ _ _ _ L).2.trans
  exact D.degreeT
private theorem shifted_ne (i : Fin N) : D.shifted i L ≠ 0 := by
  intro hz
  have hh := D.order_one i
  change (contactLift contactWeight (D.shifted i L)).natTrailingDegree = 1 at hh
  simp [hz] at hh
private theorem bank_s (b : Bank) : b.s - b.dS + b.dS = b.s := by cases b <;> rfl
private theorem bank_t (b : Bank) : b.t - b.dT + b.dT = b.t := by cases b <;> rfl
private def localMultiply (i : Fin N) : Multipliers F b →ₗ[F] JetSpace F 3 b.s b.t where
  toFun Q := ⟨weightedTruncation contactWeight 4 (D.shifted i L * Q.val), by
    simpa only [bank_s, bank_t] using
      truncated_mul_mem_jet 2 (b.s-b.dS) (b.t-b.dT) b.dS b.dT (D.shifted i L)
        (shifted_S D i) (shifted_T D i) Q⟩
  map_add' Q R := by apply Subtype.ext; simp [mul_add]
  map_smul' a Q := by apply Subtype.ext; simp
private theorem localMultiply_injective (i : Fin N) :
    Function.Injective (localMultiply D i) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro Q hQ
  by_contra hn
  have hprod : weightedTruncation contactWeight 4 (D.shifted i L * Q.val) = 0 :=
    congrArg (fun x : JetSpace F 3 b.s b.t => x.val) hQ
  have hhigh := (weightedTruncation_eq_zero_iff _ _ _).mp hprod
  have hQn : Q.val ≠ 0 := fun hz => hn (Subtype.ext hz)
  exact contact_product_not_high_order contactWeight 4 (D.shifted i L) Q.val
    (D.order_one i) (shifted_ne D i) hQn (jetSpace_support_bound _ _ _ Q) hhigh
private abbrev LocalSpace (i : Fin N) :=
  (JetSpace F 3 b.s b.t) ⧸ LinearMap.range (localMultiply D i)
private theorem local_finrank (i : Fin N) :
    Module.finrank F (LocalSpace D i) = J 4 b.s b.t - J 3 (b.s-b.dS) (b.t-b.dT) := by
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range (localMultiply D i))
  rw [LinearMap.finrank_range_of_inj (localMultiply_injective D i), jetSpace_finrank,
    jetSpace_finrank] at hq
  change Module.finrank F (LocalSpace D i) + J 3 (b.s-b.dS) (b.t-b.dT) = J 4 b.s b.t at hq
  omega
end
end P2_4
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace P2_4
noncomputable section
open P2 FrobeniusLocator MvPolynomial
open K1_11 (V J contactLift contactWeight contactShift
  contactLift_X_pow_dvd_iff
  contactDecoderImages_vanish decoder_contact_composition decoder_eval_degree
  eq_zero_of_many_contacts decoder_contact_multiplicity decoderImages contactDecoderImages
  sourceWeights mem_filtered correctOn nodes_injective indexedSupport indexedSupport_card
  mem_indexedSupport scalarWeightY scalarWeightYS scalarWeightT scalarEliminant
  scalarEliminant_ne_zero polynomialView_source_coefficients clearedEval_weight_bound
  polynomialView scalarEliminant_annihilates)
open private scalar_total_weight_le from ProximityPrize.SubmissionLower.Fast071
variable {u : Words} {deleted : Finset I} {P : Puncture deleted} {b : Bank} {H : ℕ}
    (D : ContactInput u P b H)
def ContactInput.shifted (_D : ContactInput u P b H) (i : Fin P.N) (Q : MvPolynomial (Fin 5) K) :=
  contactShift (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
    (u 0 (P.index i) ^ p) (u 1 (P.index i) ^ p) Q
private def asContactData : ContactData P.N D.L b where
  x := P.nodes
  first := fun i => u 0 (P.index i)
  firstSlope := fun i => u 1 (P.index i)
  second := fun i => u 0 (P.index i) ^ p
  secondSlope := fun i => u 1 (P.index i) ^ p
  nonzero := D.L_ne
  degreeS := le_of_eq (D.degrees 2)
  degreeT := le_of_eq (D.degrees 3)
  order_one := D.order_one
private theorem contact_order_one_mem {σ : Type*} (v : σ → ℕ) (L : MvPolynomial σ K)
    (hL : (contactLift v L).natTrailingDegree = 1) : L ∈ restrictWeightedOrder v 1 := by
  apply (contactLift_X_pow_dvd_iff v 1 L).mp
  apply Polynomial.X_pow_dvd_iff.mpr
  intro d hd
  apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
  omega
theorem mark_degree {u : Words} {γ : K} (M : BadMark u γ) :
    M.decoder.natDegree ≤ 131071 := by
  apply Polynomial.natDegree_le_of_degree_le
  exact Order.le_of_lt_succ (show M.decoder.degree < (131072 : ℕ) from M.degree)
theorem correctOn_mark {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {γ : K} (M : BadMark u γ) :
    correctOn u P M.decoder (M.decoder.map twist) γ (γ ^ p) (indexedSupport P M.support) := by
  intro i hi
  have h := M.hits (P.index i) ((mem_indexedSupport P M.support i).mp hi)
  refine ⟨h, ?_⟩
  change (M.decoder.map twist).eval (node (P.index i)) =
    u 0 (P.index i) ^ p + γ ^ p * u 1 (P.index i) ^ p
  rw [Strata.eval_coefficient_map twist M.decoder _ (Native.native_domain_fixed (P.index i)), h]
  simp only [map_add, map_mul, P0.twist, frobenius_def]
private theorem bank_cancel (b : Bank) : 1 + (b.dT - 1) = b.dT := by cases b <;> rfl
end
end P2_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace P2_4
noncomputable section
open P2 MvPolynomial
open scoped BigOperators
open K1_11 (indexedSupport mem_indexedSupport indexedSupport_card nodes_injective)
open private ncard_inter_filter surface_count_with_terminal from ProximityPrize.SubmissionLower.Fast070
open private seed_eq_of_mismatch from ProximityPrize.SubmissionLower.Fast065
variable {u : Words} {deleted : Finset I} {P : Puncture deleted}
  {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}
private theorem pencil_bad_count (hsub : Λ ⊆ Γ) (P₀ P₁ : Polynomial K)
    (h₀ : P₀.degree < (131072 : ℕ)) (h₁ : P₁.degree < (131072 : ℕ))
    (pencil : ∀ γ (hγ : γ ∈ Λ),
      (F.mark γ (hsub hγ)).decoder = P₀ + Polynomial.C γ * P₁) :
    Λ.card ≤ P.N := by
  classical
  have mismatch (γ : Λ) :
      ∃ i : Fin P.N,
        (P₀.eval (P.nodes i) ≠ u 0 (P.index i) ∨ P₁.eval (P.nodes i) ≠ u 1 (P.index i)) ∧
        P₀.eval (P.nodes i) + (γ : K) * P₁.eval (P.nodes i) =
          u 0 (P.index i) + (γ : K) * u 1 (P.index i) := by
    let M := F.mark γ (hsub γ.property)
    obtain ⟨idx, hi, hm⟩ :
        ∃ idx ∈ M.support, P₀.eval (node idx) ≠ u 0 idx ∨ P₁.eval (node idx) ≠ u 1 idx := by
      by_contra hn
      push Not at hn
      exact M.nonjoint ⟨⟨P₀, h₀, fun j hj => (hn j hj).1⟩, ⟨P₁, h₁, fun j hj => (hn j hj).2⟩⟩
    obtain ⟨i, rfl⟩ := (P.retained idx).mpr (F.survives γ (hsub γ.property) idx hi)
    refine ⟨i, hm, ?_⟩
    have hh := M.hits (P.index i) hi
    change (F.mark (γ : K) (hsub γ.property)).decoder.eval (P.nodes i) = _ at hh
    simpa only [pencil _ γ.property, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C] using hh
  let f : Λ → Fin P.N := fun γ => Classical.choose (mismatch γ)
  have hf : Function.Injective f := by
    intro γ δ he
    apply Subtype.ext
    obtain ⟨hm, hγ⟩ := Classical.choose_spec (mismatch γ)
    have hδ := (Classical.choose_spec (mismatch δ)).2
    change f γ = f δ at he
    change
      (P₀.eval (P.nodes (f γ)) ≠ u 0 (P.index (f γ)) ∨
        P₁.eval (P.nodes (f γ)) ≠ u 1 (P.index (f γ))) at hm
    change P₀.eval (P.nodes (f γ)) + (γ : K) * P₁.eval (P.nodes (f γ)) =
      u 0 (P.index (f γ)) + (γ : K) * u 1 (P.index (f γ)) at hγ
    change P₀.eval (P.nodes (f δ)) + (δ : K) * P₁.eval (P.nodes (f δ)) =
      u 0 (P.index (f δ)) + (δ : K) * u 1 (P.index (f δ)) at hδ
    rw [← he] at hδ
    exact seed_eq_of_mismatch (F := K) hγ hδ hm
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf
variable (chart : TaylorChart u P F b Λ)
theorem chart_cut_iff (γ : K) (hγ : γ ∈ Λ) (i : Fin P.N) :
    MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0 ↔
      (F.mark γ (chart.subset hγ)).decoder.eval (P.nodes i) =
        u 0 (P.index i) + γ * u 1 (P.index i) := by
  let val := MvPolynomial.eval (chart.point γ)
  let x := algebraMap K Frac (P.nodes i)
  change val (nodeCut u P chart.numerator chart.denominator i) = 0 ↔ _
  have heval := Polynomial.eval_map_apply val (C x) (p := chart.numerator)
  unfold nodeCut
  change val (chart.numerator.eval (C x) - _) = 0 ↔ _
  rw [map_sub, ← heval]
  change (chart.numerator.map val).eval (val (C x)) - _ = 0 ↔ _
  rw [show val (C x) = x by simp [val], show chart.numerator.map val = _ from chart.reconstruction γ hγ]
  rw [Polynomial.eval_mul, Polynomial.eval_C, show x = algebraMap K Frac (P.nodes i) from rfl,
    Polynomial.eval_map_apply, map_mul, map_add, map_mul]
  simp only [val, eval_C, eval_X, chart.slope γ hγ]
  rw [← map_mul, ← map_add, sub_eq_zero]
  constructor
  · intro h
    exact (algebraMap K Frac).injective (mul_left_cancel₀ (chart.regular γ hγ) h)
  · intro h
    rw [h]
theorem chart_persistent (J : Ideal (MvPolynomial (Fin 3) Frac)) (W : Finset K) (hW : W ⊆ Λ)
    (hzero : ∀ γ ∈ W, chart.point γ ∈ zeroLocus Frac J)
    (hpersist : 131072 ≤ {i | nodeCut u P chart.numerator chart.denominator i ∈ J}.ncard) :
    W.card ≤ P.N := by
  classical
  let keep := Finset.univ.filter fun i => nodeCut u P chart.numerator chart.denominator i ∈ J
  have hk : 131072 ≤ keep.card := by
    rw [← Set.ncard_coe_finset]
    exact hpersist.trans_eq (congrArg Set.ncard (by ext i; simp [keep]))
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hk
  let P₀ := Lagrange.interpolate S P.nodes (fun i => u 0 (P.index i))
  let P₁ := Lagrange.interpolate S P.nodes (fun i => u 1 (P.index i))
  have hinj : Set.InjOn P.nodes (S : Set (Fin P.N)) := nodes_injective.injOn
  have hd₀ : P₀.degree < (131072 : ℕ) := by
    simpa only [P₀, hcard] using Lagrange.degree_interpolate_lt (fun i => u 0 (P.index i)) hinj
  have hd₁ : P₁.degree < (131072 : ℕ) := by
    simpa only [P₁, hcard] using Lagrange.degree_interpolate_lt (fun i => u 1 (P.index i)) hinj
  apply pencil_bad_count (P := P) (F := F) (fun _ hg => chart.subset (hW hg)) P₀ P₁ hd₀ hd₁
  intro γ hγ
  let M := F.mark γ (chart.subset (hW hγ))
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hinj
  · rw [hcard]
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (mark_degree M)))
  · rw [hcard]
    have hm : (Polynomial.C γ * P₁).degree ≤ P₁.degree := by
      refine (Polynomial.degree_mul_le _ _).trans ?_
      simpa only [zero_add] using add_le_add_left (Polynomial.degree_C_le (a := γ)) P₁.degree
    exact (Polynomial.degree_add_le _ _).trans_lt (max_lt hd₀ (hm.trans_lt hd₁))
  · intro i hi
    have hcut : nodeCut u P chart.numerator chart.denominator i ∈ J := (Finset.mem_filter.mp (hS hi)).2
    have hz : MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0 :=
      hzero γ hγ _ hcut
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    exact (chart_cut_iff chart γ (hW hγ) i).mp hz |>.trans (by
      rw [Lagrange.eval_interpolate_at_node _ hinj hi, Lagrange.eval_interpolate_at_node _ hinj hi])
end
end P2_4
end
section
namespace P2_7
open P2 (HighBand)
abbrev Bank := P1_7.Bank
abbrev Stage := P1_7.Stage
structure Grade where
  seedCap : ℕ
  slots : ℕ
  buffer : Option ℕ
def terminal : HighBand → Bank
  | .h2366 => ⟨⟨6800,9477,2012,231200⟩,9304500718796800,0xc61e52a39be7⟩
  | .h2380 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,327528160189452⟩
  | .h2400 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,327528160189452⟩
  | .h2420 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,327528160189452⟩
  | .h2440 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,327528160189452⟩
  | .h2450 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,327528160189452⟩
  | .h2460 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,327528160189452⟩
  | .h2480 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,327528160189452⟩
  | .h2500 => ⟨⟨6500,9061,1924,217087⟩,8129289859891200,0xa595a9fe5605⟩
  | .h2520 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2530 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2540 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2550 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2560 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2570 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2585 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2590 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2600 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2601 => ⟨⟨4800,6693,1416,139703⟩,0xb9a7af1b00000,54063203881458⟩
  | .h2611 => ⟨⟨4800,6693,1416,139703⟩,0xb9a7af1b00000,54063203881458⟩
  | .h2621 => ⟨⟨4800,6693,1416,139703⟩,0xb9a7af1b00000,54063203881458⟩
  | .h2640 => ⟨⟨4800,6693,1416,139703⟩,0xb9a7af1b00000,54063203881458⟩
  | .h2670 => ⟨⟨4800,6693,1416,139703⟩,0xb9a7af1b00000,54063203881458⟩
  | .h2700 => ⟨⟨4800,6693,1416,139703⟩,0xb9a7af1b00000,54063203881458⟩
  | .h2750 => ⟨⟨4800,6693,1416,139703⟩,0xb9a7af1b00000,54063203881458⟩
  | .h2800 => ⟨⟨6500,9016,1885,136084⟩,8002773617213440,0xa05cc1f7753a⟩
  | .h2900 => ⟨⟨6500,9024,1885,121313⟩,8002773617213440,0xa0d1fe03ba36⟩
  | .h2950 => ⟨⟨4100,5688,1209,82080⟩,0x73aeffed40000,28309856493724⟩
  | .h2980 => ⟨⟨4100,5688,1209,82080⟩,0x73aeffed40000,28309856493724⟩
  | .h3000 => ⟨⟨4100,5688,1209,82080⟩,0x73aeffed40000,28309856493724⟩
  | .h3050 => ⟨⟨4100,5688,1209,82080⟩,0x73aeffed40000,28309856493724⟩
  | .h3100 => ⟨⟨3000,4189,858,50872⟩,779135648792576,8094070384976⟩
  | .h3200 => ⟨⟨3000,4189,858,50872⟩,779135648792576,8094070384976⟩
  | .h3400 => ⟨⟨3000,4189,858,50872⟩,779135648792576,8094070384976⟩
  | .h3555 => ⟨⟨1360,1890,386,23288⟩,72306230820864,335491349509⟩
  | .h4000 => ⟨⟨652,908,184,12230⟩,7963633254400,17851299543⟩
  | .h4800 => ⟨⟨492,686,138,6001⟩,3414278537216,5800691370⟩
  | .h7745 => ⟨⟨124,173,32,946⟩,52879163392,22832869⟩
  | .h8000 => ⟨⟨124,173,32,946⟩,52879163392,22832869⟩
  | .h14500 => ⟨⟨40,56,8,289⟩,1610612736,230946⟩
  | .h21448 => ⟨⟨30,42,6,207⟩,711983104,77331⟩
  | .h24000 => ⟨⟨30,42,6,207⟩,711983104,77331⟩
  | .h28300 => ⟨⟨30,42,6,207⟩,711983104,77331⟩
  | .h32411 => ⟨⟨8,11,1,55⟩,17039360,517⟩
def subbank (b : HighBand) (g : Grade) : Bank :=
  let t := terminal b
  { t with shape := { t.shape with U := g.slots } }
def grades : HighBand → List Grade
  | .h2366 =>
    [⟨403,178628, none⟩,⟨398,180297, none⟩,⟨392,181576, some 10⟩,⟨386,183191, some 13⟩,
     ⟨380,185227, some 16⟩,⟨373,187019, some 19⟩,⟨366,189446, some 22⟩,⟨359,192743, some 25⟩,
     ⟨351,196385, some 27⟩,⟨342,200852, some 30⟩,⟨333,208297, some 32⟩,⟨321,218538, some 34⟩,
     ⟨307,231200, some 36⟩,⟨290,231200, some 37⟩,⟨271,231200, some 37⟩,⟨249,231200, some 36⟩,
     ⟨226,231200, some 35⟩,⟨199,231200, some 33⟩,⟨170,231200, some 30⟩,⟨139,231200, some 26⟩,
     ⟨106,231200, some 21⟩,⟨71,231200, some 14⟩,⟨33,231200, some 7⟩]
  | .h2380 =>
    [⟨378,191872, none⟩,⟨373,193603, none⟩,⟨367,194880, some 9⟩,⟨361,196538, some 12⟩,
     ⟨355,198675, some 15⟩,⟨349,201431, some 18⟩,⟨342,204072, some 21⟩,⟨335,207757, some 23⟩,
     ⟨327,211929, some 26⟩,⟨319,218423, some 28⟩,⟨309,226713, some 30⟩,⟨297,234728, some 32⟩,
     ⟨284,234728, some 33⟩,⟨269,234728, some 34⟩,⟨251,234728, some 34⟩,⟨232,234728, some 34⟩,
     ⟨210,234728, some 33⟩,⟨186,234728, some 31⟩,⟨160,234728, some 28⟩,⟨132,234728, some 25⟩,
     ⟨102,234728, some 20⟩,⟨70,234728, some 14⟩,⟨36,234728, some 7⟩]
  | .h2400 =>
    [⟨364,188372, none⟩,⟨359,190039, none⟩,⟨353,191241, some 9⟩,⟨348,193679, some 12⟩,
     ⟨342,195789, some 15⟩,⟨335,197622, some 17⟩,⟨329,201197, some 20⟩,⟨322,204962, some 22⟩,
     ⟨314,209308, some 24⟩,⟨305,215045, some 27⟩,⟨295,224261, some 29⟩,⟨283,234728, some 30⟩,
     ⟨269,234728, some 31⟩,⟨253,234728, some 32⟩,⟨235,234728, some 32⟩,⟨214,234728, some 31⟩,
     ⟨191,234728, some 30⟩,⟨166,234728, some 27⟩,⟨139,234728, some 24⟩,⟨110,234728, some 20⟩,
     ⟨78,234728, some 15⟩,⟨45,234728, some 9⟩,⟨9,234728, some 1⟩]
  | .h2420 =>
    [⟨358,186933, none⟩,⟨353,188574, none⟩,⟨347,189744, some 9⟩,⟨342,192163, some 12⟩,
     ⟨336,194251, some 14⟩,⟨329,196062, some 17⟩,⟨323,199641, some 19⟩,⟨316,203427, some 22⟩,
     ⟨308,207837, some 24⟩,⟨299,213746, some 26⟩,⟨289,223484, some 28⟩,⟨277,234728, some 29⟩,
     ⟨263,234728, some 30⟩,⟨246,234728, some 31⟩,⟨227,234728, some 31⟩,⟨206,234728, some 30⟩,
     ⟨183,234728, some 28⟩,⟨157,234728, some 26⟩,⟨129,234728, some 23⟩,⟨100,234728, some 18⟩,
     ⟨67,234728, some 13⟩,⟨33,234728, some 6⟩]
  | .h2440 =>
    [⟨333,180191, none⟩,⟨328,181695, none⟩,⟨323,183568, some 8⟩,⟨318,185901, some 11⟩,
     ⟨312,187895, some 13⟩,⟨306,190585, some 16⟩,⟨299,193211, some 18⟩,⟨292,197106, some 20⟩,
     ⟨284,201833, some 22⟩,⟨276,209949, some 24⟩,⟨265,221356, some 26⟩,⟨252,234728, some 27⟩,
     ⟨236,234728, some 27⟩,⟨218,234728, some 27⟩,⟨197,234728, some 27⟩,⟨174,234728, some 25⟩,
     ⟨148,234728, some 23⟩,⟨120,234728, some 20⟩,⟨90,234728, some 15⟩,⟨58,234728, some 10⟩,
     ⟨23,234728, some 4⟩]
  | .h2450 =>
    [⟨322,177369, none⟩,⟨317,178815, none⟩,⟨312,180635, some 8⟩,⟨307,182925, some 10⟩,
     ⟨301,184871, some 13⟩,⟨295,187535, some 15⟩,⟨288,190151, some 17⟩,⟨281,194108, some 19⟩,
     ⟨274,200243, some 21⟩,⟨265,207740, some 23⟩,⟨254,221212, some 24⟩,⟨240,234728, some 25⟩,
     ⟨224,234728, some 26⟩,⟨204,234728, some 25⟩,⟨183,234728, some 25⟩,⟨158,234728, some 23⟩,
     ⟨132,234728, some 20⟩,⟨103,234728, some 17⟩,⟨72,234728, some 12⟩,⟨38,234728, some 6⟩,
     ⟨2,234728, some 0⟩]
  | .h2460 =>
    [⟨312,174980, none⟩,⟨307,176379, none⟩,⟨302,178158, some 8⟩,⟨296,179487, some 10⟩,
     ⟨291,182330, some 12⟩,⟨285,184988, some 14⟩,⟨278,187619, some 17⟩,⟨271,191674, some 19⟩,
     ⟨264,198098, some 20⟩,⟨255,206329, some 22⟩,⟨244,222653, some 23⟩,⟨229,234728, some 24⟩,
     ⟨211,234728, some 24⟩,⟨191,234728, some 24⟩,⟨169,234728, some 23⟩,⟨144,234728, some 21⟩,
     ⟨116,234728, some 18⟩,⟨86,234728, some 14⟩,⟨53,234728, some 9⟩,⟨19,234728, some 3⟩]
  | .h2480 =>
    [⟨292,169092, none⟩,⟨287,170354, none⟩,⟨282,172001, some 7⟩,⟨277,174142, some 9⟩,
     ⟨272,176932, some 11⟩,⟨266,179548, some 13⟩,⟨260,183306, some 15⟩,⟨253,187623, some 17⟩,
     ⟨245,193434, some 19⟩,⟨236,203436, some 20⟩,⟨224,225763, some 21⟩,⟨208,234728, some 22⟩,
     ⟨189,234728, some 22⟩,⟨167,234728, some 21⟩,⟨142,234728, some 19⟩,⟨115,234728, some 16⟩,
     ⟨85,234728, some 13⟩,⟨53,234728, some 8⟩,⟨18,234728, some 2⟩]
  | .h2500 =>
    [⟨278,142438, none⟩,⟨273,143455, none⟩,⟨269,145636, some 7⟩,⟨263,146611, some 9⟩,
     ⟨258,148995, some 11⟩,⟨252,151245, some 13⟩,⟨246,154558, some 15⟩,⟨239,158480, some 16⟩,
     ⟨231,164042, some 18⟩,⟨222,174640, some 19⟩,⟨209,201727, some 20⟩,⟨189,217087, some 20⟩,
     ⟨166,217087, some 19⟩,⟨139,217087, some 17⟩,⟨110,217087, some 14⟩,⟨77,217087, some 11⟩,
     ⟨42,217087, some 6⟩,⟨4,217087, some 0⟩]
  | .h2520 =>
    [⟨261,135659, none⟩,⟨257,137342, none⟩,⟨252,138587, some 6⟩,⟨247,140280, some 8⟩,
     ⟨242,142575, some 10⟩,⟨236,144752, some 12⟩,⟨230,148067, some 13⟩,⟨223,152135, some 15⟩,
     ⟨215,158308, some 16⟩,⟨206,168072, some 18⟩,⟨194,168072, some 18⟩,⟨181,168072, some 19⟩,
     ⟨165,168072, some 19⟩,⟨147,168072, some 18⟩,⟨126,168072, some 17⟩,⟨104,168072, some 15⟩,
     ⟨79,168072, some 12⟩,⟨53,168072, some 8⟩,⟨24,168072, some 3⟩]
  | .h2530 =>
    [⟨254,134061, none⟩,⟨250,135715, none⟩,⟨245,136925, some 6⟩,⟨240,138591, some 8⟩,
     ⟨235,140876, some 10⟩,⟨229,143052, some 11⟩,⟨223,146421, some 13⟩,⟨216,150642, some 15⟩,
     ⟨208,157293, some 16⟩,⟨199,168072, some 17⟩,⟨186,168072, some 18⟩,⟨172,168072, some 18⟩,
     ⟨156,168072, some 18⟩,⟨137,168072, some 17⟩,⟨116,168072, some 15⟩,⟨93,168072, some 13⟩,
     ⟨67,168072, some 10⟩,⟨40,168072, some 6⟩,⟨10,168072, some 1⟩]
  | .h2540 =>
    [⟨247,132249, none⟩,⟨243,133866, none⟩,⟨238,135030, some 6⟩,⟨233,136657, some 8⟩,
     ⟨228,138915, some 9⟩,⟨222,141074, some 11⟩,⟨216,144474, some 13⟩,⟨209,148825, some 14⟩,
     ⟨202,157361, some 15⟩,⟨191,168072, some 16⟩,⟨179,168072, some 17⟩,⟨164,168072, some 17⟩,
     ⟨147,168072, some 17⟩,⟨127,168072, some 15⟩,⟨106,168072, some 14⟩,⟨82,168072, some 11⟩,
     ⟨55,168072, some 8⟩,⟨27,168072, some 4⟩]
  | .h2550 =>
    [⟨240,130228, none⟩,⟨236,131797, none⟩,⟨231,132905, some 6⟩,⟨227,135395, some 7⟩,
     ⟨221,136695, some 9⟩,⟨216,139842, some 11⟩,⟨210,143332, some 12⟩,⟨203,147908, some 14⟩,
     ⟨195,155754, some 15⟩,⟨185,168072, some 16⟩,⟨172,168072, some 16⟩,⟨156,168072, some 16⟩,
     ⟨138,168072, some 16⟩,⟨118,168072, some 14⟩,⟨96,168072, some 12⟩,⟨71,168072, some 10⟩,
     ⟨44,168072, some 6⟩,⟨15,168072, some 2⟩]
  | .h2560 =>
    [⟨234,128826, none⟩,⟨230,130368, none⟩,⟨225,131442, some 5⟩,⟨220,132991, some 7⟩,
     ⟨215,135200, some 9⟩,⟨210,138371, some 10⟩,⟨204,141934, some 12⟩,⟨197,146719, some 13⟩,
     ⟨189,155329, some 14⟩,⟨178,168072, some 15⟩,⟨165,168072, some 16⟩,⟨149,168072, some 15⟩,
     ⟨130,168072, some 15⟩,⟨109,168072, some 13⟩,⟨86,168072, some 11⟩,⟨61,168072, some 8⟩,
     ⟨33,168072, some 4⟩,⟨3,168072, some 0⟩]
  | .h2570 =>
    [⟨228,127244, none⟩,⟨224,128750, none⟩,⟨219,129781, some 5⟩,⟨215,132239, some 7⟩,
     ⟨209,133480, some 8⟩,⟨204,136660, some 10⟩,⟨198,140276, some 11⟩,⟨191,145254, some 13⟩,
     ⟨183,154681, some 14⟩,⟨172,168072, some 15⟩,⟨158,168072, some 15⟩,⟨141,168072, some 14⟩,
     ⟨122,168072, some 14⟩,⟨101,168072, some 12⟩,⟨77,168072, some 10⟩,⟨50,168072, some 7⟩,
     ⟨22,168072, some 3⟩]
  | .h2585 =>
    [⟨219,124537, none⟩,⟨215,125976, none⟩,⟨211,127846, some 5⟩,⟨206,129327, some 7⟩,
     ⟨201,131509, some 8⟩,⟨196,134739, some 10⟩,⟨190,138493, some 11⟩,⟨183,143877, some 12⟩,
     ⟨175,155003, some 13⟩,⟨163,168072, some 14⟩,⟨148,168072, some 14⟩,⟨130,168072, some 13⟩,
     ⟨110,168072, some 12⟩,⟨88,168072, some 10⟩,⟨63,168072, some 8⟩,⟨36,168072, some 4⟩,
     ⟨6,168072, some 0⟩]
  | .h2590 =>
    [⟨217,124407, none⟩,⟨212,124959, none⟩,⟨208,126803, some 5⟩,⟨203,128254, some 6⟩,
     ⟨199,131440, some 8⟩,⟨193,133624, some 9⟩,⟨187,137381, some 11⟩,⟨180,142839, some 12⟩,
     ⟨172,154459, some 13⟩,⟨160,168072, some 14⟩,⟨145,168072, some 14⟩,⟨127,168072, some 13⟩,
     ⟨107,168072, some 12⟩,⟨84,168072, some 10⟩,⟨58,168072, some 7⟩,⟨31,168072, some 4⟩,
     ⟨1,168072, some 0⟩]
  | .h2600 =>
    [⟨211,122310, none⟩,⟨207,123694, none⟩,⟨203,125517, some 5⟩,⟨198,126943, some 6⟩,
     ⟨193,129092, some 8⟩,⟨188,132338, some 9⟩,⟨182,136190, some 10⟩,⟨175,141952, some 12⟩,
     ⟨167,155067, some 13⟩,⟨154,168072, some 13⟩,⟨138,168072, some 13⟩,⟨120,168072, some 12⟩,
     ⟨99,168072, some 11⟩,⟨76,168072, some 9⟩,⟨50,168072, some 6⟩,⟨21,168072, some 2⟩]
  | .h2601 =>
    [⟨215,92904, none⟩,⟨211,93979, none⟩,⟨206,94683, some 5⟩,⟨202,96499, some 6⟩,
     ⟨197,98156, some 8⟩,⟨191,99798, some 9⟩,⟨186,103558, some 11⟩,⟨179,107873, some 12⟩,
     ⟨170,115979, some 13⟩,⟨157,139703, some 13⟩,⟨138,139703, some 13⟩,⟨117,139703, some 12⟩,
     ⟨92,139703, some 10⟩,⟨64,139703, some 7⟩,⟨34,139703, some 4⟩,⟨1,139703, some 0⟩]
  | .h2611 =>
    [⟨210,91931, none⟩,⟨206,92983, none⟩,⟨201,93659, some 5⟩,⟨197,95465, some 6⟩,
     ⟨192,97114, some 8⟩,⟨187,99610, some 9⟩,⟨181,102604, some 10⟩,⟨174,107153, some 12⟩,
     ⟨165,116393, some 12⟩,⟨151,139703, some 13⟩,⟨132,139703, some 12⟩,⟨110,139703, some 11⟩,
     ⟨84,139703, some 9⟩,⟨56,139703, some 6⟩,⟨25,139703, some 3⟩]
  | .h2621 =>
    [⟨205,90848, none⟩,⟨201,91872, none⟩,⟨196,92514, some 5⟩,⟨192,94301, some 6⟩,
     ⟨187,95934, some 7⟩,⟨182,98438, some 9⟩,⟨176,101487, some 10⟩,⟨169,106263, some 11⟩,
     ⟨160,116784, some 12⟩,⟨145,139703, some 12⟩,⟨126,139703, some 12⟩,⟨103,139703, some 10⟩,
     ⟨77,139703, some 8⟩,⟨48,139703, some 5⟩,⟨16,139703, some 1⟩]
  | .h2640 =>
    [⟨196,88833, none⟩,⟨192,89803, none⟩,⟨188,91118, some 4⟩,⟨183,92128, some 6⟩,
     ⟨179,94553, some 7⟩,⟨173,96245, some 8⟩,⟨167,99403, some 10⟩,⟨160,104673, some 11⟩,
     ⟨151,118386, some 11⟩,⟨135,139703, some 11⟩,⟨114,139703, some 10⟩,⟨90,139703, some 9⟩,
     ⟨63,139703, some 7⟩,⟨32,139703, some 3⟩]
  | .h2670 =>
    [⟨183,85767, none⟩,⟨179,86648, none⟩,⟨175,87882, some 4⟩,⟨171,89609, some 5⟩,
     ⟨166,91198, some 7⟩,⟨161,93811, some 8⟩,⟨155,97277, some 9⟩,⟨148,103800, some 10⟩,
     ⟨138,124332, some 10⟩,⟨119,139703, some 10⟩,⟨97,139703, some 9⟩,⟨71,139703, some 7⟩,
     ⟨42,139703, some 4⟩,⟨10,139703, some 0⟩]
  | .h2700 =>
    [⟨172,83341, none⟩,⟨168,84152, none⟩,⟨164,85326, some 4⟩,⟨160,87017, some 5⟩,
     ⟨155,88584, some 6⟩,⟨150,91280, some 7⟩,⟨144,95084, some 8⟩,⟨137,103355, some 9⟩,
     ⟨125,134193, some 9⟩,⟨105,139703, some 9⟩,⟨81,139703, some 7⟩,⟨53,139703, some 5⟩,
     ⟨22,139703, some 2⟩]
  | .h2750 =>
    [⟨156,79569, none⟩,⟨152,80258, none⟩,⟨149,82169, some 3⟩,⟨144,82951, some 4⟩,
     ⟨140,85444, some 5⟩,⟨135,88401, some 6⟩,⟨129,93132, some 7⟩,⟨121,105297, some 8⟩,
     ⟨105,139703, some 8⟩,⟨82,139703, some 6⟩,⟨56,139703, some 5⟩,⟨25,139703, some 2⟩]
  | .h2800 =>
    [⟨140,101308, none⟩,⟨137,103134, none⟩,⟨133,104407, some 3⟩,⟨129,106480, some 4⟩,
     ⟨125,109860, some 5⟩,⟨120,114140, some 6⟩,⟨114,122192, some 6⟩,⟨105,136084, some 7⟩,
     ⟨93,136084, some 7⟩,⟨79,136084, some 6⟩,⟨62,136084, some 5⟩,⟨42,136084, some 4⟩,
     ⟨20,136084, some 1⟩]
  | .h2900 =>
    [⟨119,93873, none⟩,⟨116,95493, none⟩,⟨113,97830, some 2⟩,⟨109,99863, some 3⟩,
     ⟨105,103569, some 4⟩,⟨100,109148, some 4⟩,⟨93,121313, some 5⟩,⟨84,121313, some 5⟩,
     ⟨72,121313, some 5⟩,⟨57,121313, some 4⟩,⟨41,121313, some 3⟩,⟨22,121313, some 1⟩,
     ⟨1,121313, some 0⟩]
  | .h2950 =>
    [⟨113,57650, none⟩,⟨110,58628, none⟩,⟨107,60073, some 2⟩,⟨103,61331, some 3⟩,
     ⟨99,63734, some 4⟩,⟨94,67621, some 4⟩,⟨87,79989, some 5⟩,⟨75,82080, some 4⟩,
     ⟨60,82080, some 4⟩,⟨43,82080, some 3⟩,⟨23,82080, some 1⟩,⟨0,82080, none⟩]
  | .h2980 =>
    [⟨109,56979, none⟩,⟨106,57946, none⟩,⟨102,58518, some 2⟩,⟨99,60684, some 3⟩,
     ⟨95,63214, some 3⟩,⟨90,67608, some 4⟩,⟨82,82080, some 4⟩,⟨69,82080, some 4⟩,
     ⟨54,82080, some 3⟩,⟨36,82080, some 2⟩,⟨15,82080, some 1⟩]
  | .h3000 =>
    [⟨106,56159, none⟩,⟨103,57096, none⟩,⟨100,58526, some 2⟩,⟨96,59789, some 3⟩,
     ⟨92,62346, some 3⟩,⟨87,66998, some 4⟩,⟨79,82080, some 4⟩,⟨66,82080, some 4⟩,
     ⟨50,82080, some 3⟩,⟨31,82080, some 2⟩,⟨10,82080, some 0⟩]
  | .h3050 =>
    [⟨99,54118, none⟩,⟨96,54975, none⟩,⟨93,56337, some 2⟩,⟨90,58553, some 2⟩,
     ⟨86,61316, some 3⟩,⟨80,65558, some 3⟩,⟨71,82080, some 4⟩,⟨57,82080, some 3⟩,
     ⟨40,82080, some 2⟩,⟨20,82080, some 1⟩]
  | .h3100 =>
    [⟨95,39227, none⟩,⟨92,39836, none⟩,⟨89,40830, some 2⟩,⟨86,42490, some 2⟩,
     ⟨82,44643, some 3⟩,⟨76,48476, some 3⟩,⟨68,50872, some 3⟩,⟨58,50872, some 3⟩,
     ⟨45,50872, some 3⟩,⟨29,50872, some 2⟩,⟨12,50872, some 0⟩]
  | .h3200 =>
    [⟨85,37292, none⟩,⟨82,37825, none⟩,⟨79,38774, some 1⟩,⟨76,40487, some 2⟩,
     ⟨72,42980, some 2⟩,⟨66,50107, some 3⟩,⟨56,50872, some 3⟩,⟨44,50872, some 2⟩,
     ⟨29,50872, some 1⟩,⟨12,50872, some 0⟩]
  | .h3400 =>
    [⟨70,33968, none⟩,⟨68,35116, none⟩,⟨65,36037, some 1⟩,⟨61,36994, some 1⟩,
     ⟨57,40579, some 2⟩,⟨50,50872, some 2⟩,⟨37,50872, some 1⟩,⟨22,50872, some 1⟩,
     ⟨4,50872, some 0⟩]
  | .h3555 =>
    [⟨65,14832, none⟩,⟨63,15336, none⟩,⟨60,15736, some 1⟩,⟨57,16649, some 1⟩,
     ⟨52,18175, some 1⟩,⟨43,23288, some 1⟩,⟨30,23288, some 1⟩,⟨13,23288, some 0⟩]
  | .h4000 =>
    [⟨53,6533, none⟩,⟨50,6564, none⟩,⟨48,6948, some 0⟩,⟨45,7508, some 1⟩,
     ⟨39,9673, some 1⟩,⟨25,12230, some 0⟩,⟨6,12230, some 0⟩]
  | .h4800 =>
    [⟨38,4203, none⟩,⟨36,4345, none⟩,⟨34,4682, some 0⟩,⟨30,5351, some 0⟩,
     ⟨23,6001, some 0⟩,⟨13,6001, some 0⟩]
  | .h7745 =>
    [⟨26,919, none⟩,⟨24,946, none⟩,⟨22,946, none⟩,⟨19,946, none⟩,
     ⟨14,946, none⟩,⟨8,946, none⟩]
  | .h8000 =>
    [⟨25,902, none⟩,⟨23,932, none⟩,⟨21,946, none⟩,⟨18,946, none⟩,
     ⟨13,946, none⟩,⟨6,946, none⟩]
  | .h14500 =>
    [⟨18,252, none⟩,⟨17,282, none⟩,⟨14,289, none⟩,⟨11,289, none⟩,
     ⟨5,289, none⟩]
  | .h21448 =>
    [⟨14,169, none⟩,⟨13,194, none⟩,⟨10,207, none⟩,⟨5,207, none⟩]
  | .h24000 =>
    [⟨13,164, none⟩,⟨12,189, none⟩,⟨9,207, none⟩,⟨4,207, none⟩]
  | .h28300 =>
    [⟨12,159, none⟩,⟨11,187, none⟩,⟨8,207, none⟩,⟨2,207, none⟩]
  | .h32411 =>
    [⟨13,47, none⟩,⟨12,55, none⟩,⟨9,55, none⟩,⟨4,55, none⟩]
def stages : HighBand → List Stage
  | .h2366 =>
    [⟨0, ⟨⟨73,101,22,876⟩,12438470656,3108650⟩, ⟨⟨377,525,110,12520⟩,1587867287552,2061878340⟩⟩,
     ⟨1, ⟨⟨78,108,24,1011⟩,15341977600,4103823⟩, ⟨⟨377,525,110,14879⟩,1587867287552,2061878340⟩⟩,
     ⟨2, ⟨⟨86,119,26,1076⟩,20190855168,5931589⟩, ⟨⟨425,591,124,15634⟩,2271510528000,3308696108⟩⟩,
     ⟨3, ⟨⟨96,133,29,1089⟩,27911782400,9174699⟩, ⟨⟨438,609,128,17789⟩,2488618188800,3734056387⟩⟩,
     ⟨4, ⟨⟨104,144,32,1142⟩,35837181952,12729182⟩, ⟨⟨499,694,146,18017⟩,3678284546048,6290986493⟩⟩,
     ⟨5, ⟨⟨112,155,34,1216⟩,44177817600,16852996⟩, ⟨⟨558,776,163,18668⟩,5131801722880,9809476816⟩⟩,
     ⟨6, ⟨⟨118,163,36,1321⟩,51745914880,20664170⟩, ⟨⟨609,847,178,19601⟩,6669510901760,13915453029⟩⟩,
     ⟨10, ⟨⟨136,188,42,1943⟩,79525314560,36641499⟩, ⟨⟨761,1058,225,24389⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨16, ⟨⟨163,226,50,3349⟩,135467106304,75401397⟩, ⟨⟨1042,1449,305,30822⟩,33334360276992,118840568423⟩⟩,
     ⟨18, ⟨⟨226,313,69,1973⟩,356954931200,273860683⟩, ⟨⟨1042,1449,305,34358⟩,33334360276992,118840568423⟩⟩,
     ⟨24, ⟨⟨186,258,57,26737⟩,200431370240,127350358⟩, ⟨⟨1042,1449,305,52384⟩,33334360276992,118840568423⟩⟩,
     ⟨32, ⟨⟨261,362,82,5348⟩,560158474240,498527994⟩, ⟨⟨1549,2154,456,51462⟩,0x63e152ac0000,581810422259⟩⟩,
     ⟨36, ⟨⟨251,348,77,35117⟩,489745285120,418551513⟩, ⟨⟨1220,1697,357,113326⟩,53453923287040,223282021540⟩⟩,
     ⟨42, ⟨⟨443,614,139,3398⟩,2716582543360,4085953544⟩, ⟨⟨1755,2441,512,69006⟩,0x90361c680000,952199116915⟩⟩,
     ⟨54, ⟨⟨429,594,135,5980⟩,2473328640000,3591463239⟩, ⟨⟨2357,3280,689,78457⟩,384417778892800,3105034566503⟩⟩,
     ⟨81, ⟨⟨635,880,195,7706⟩,7847044710400,16889053700⟩, ⟨⟨3390,4714,997,110149⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩,
     ⟨100, ⟨⟨753,1044,235,9568⟩,0xc085f900000,33814964626⟩, ⟨⟨4266,5936,1250,130569⟩,0x81acc5ab00000,33333334927556⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,11337⟩,35306242048000,124373325152⟩, ⟨⟨5461,7594,1612,174067⟩,4811423842304000,89819624460464⟩⟩]
  | .h2380 =>
    [⟨0, ⟨⟨73,101,22,841⟩,12438470656,3108650⟩, ⟨⟨352,489,103,12101⟩,1296449929216,1560122533⟩⟩,
     ⟨1, ⟨⟨78,108,24,967⟩,15341977600,4103823⟩, ⟨⟨345,480,101,15116⟩,1221414354944,1447711168⟩⟩,
     ⟨2, ⟨⟨86,119,26,1032⟩,20190855168,5931589⟩, ⟨⟨385,535,112,15973⟩,1686840279040,2221379895⟩⟩,
     ⟨3, ⟨⟨94,130,29,1084⟩,26637762560,8531244⟩, ⟨⟨411,572,120,17561⟩,2056243380224,2904427648⟩⟩,
     ⟨4, ⟨⟨102,141,31,1153⟩,33533460480,11621252⟩, ⟨⟨438,609,128,19166⟩,2488618188800,3734056387⟩⟩,
     ⟨5, ⟨⟨108,150,33,1249⟩,39862927360,14840297⟩, ⟨⟨522,726,153,18102⟩,4214585819136,7540240839⟩⟩,
     ⟨6, ⟨⟨108,149,33,1575⟩,39862927360,14526868⟩, ⟨⟨570,792,167,18952⟩,5481425797120,10673329627⟩⟩,
     ⟨10, ⟨⟨142,197,43,1697⟩,89085444096,43318982⟩, ⟨⟨696,968,204,23993⟩,9967068774400,23761225895⟩⟩,
     ⟨16, ⟨⟨163,226,50,3170⟩,135467106304,75401397⟩, ⟨⟨851,1183,249,33006⟩,18172149760000,52867790342⟩⟩,
     ⟨18, ⟨⟨221,306,68,1964⟩,335886942208,251865996⟩, ⟨⟨952,1324,279,34090⟩,25456515481600,82958819253⟩⟩,
     ⟨24, ⟨⟨212,294,65,4169⟩,295979712512,214017359⟩, ⟨⟨1115,1550,329,42853⟩,41081354321920,156562227172⟩⟩,
     ⟨32, ⟨⟨261,362,82,5085⟩,560158474240,498527994⟩, ⟨⟨1463,2034,430,49821⟩,92429551140864,462204056864⟩⟩,
     ⟨36, ⟨⟨246,341,75,107961⟩,459094360064,384291762⟩, ⟨⟨1220,1696,357,94310⟩,53453923287040,222859445142⟩⟩,
     ⟨42, ⟨⟨279,386,85,92837⟩,667877376000,629746567⟩, ⟨⟨1240,1725,359,250287⟩,55666189271040,236367501665⟩⟩,
     ⟨54, ⟨⟨534,740,167,4154⟩,4737851195392,8580372579⟩, ⟨⟨2252,3131,661,75123⟩,336378654883840,2588552103973⟩⟩,
     ⟨81, ⟨⟨637,883,197,7396⟩,7963588165632,17210339526⟩, ⟨⟨3474,4830,1019,101958⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,8842⟩,0xcf60ca00000,37305519000⟩, ⟨⟨4170,5798,1223,123531⟩,0x7934721300000,30381132426145⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,11069⟩,35306242048000,124373325152⟩, ⟨⟨5487,7630,1607,162969⟩,4851195216658432,90974896361155⟩⟩]
  | .h2400 =>
    [⟨0, ⟨⟨73,101,22,817⟩,12438470656,3108650⟩, ⟨⟨352,489,103,11429⟩,1296449929216,1560122533⟩⟩,
     ⟨1, ⟨⟨78,108,24,939⟩,15341977600,4103823⟩, ⟨⟨345,480,101,14062⟩,1221414354944,1447711168⟩⟩,
     ⟨2, ⟨⟨86,119,26,1004⟩,20190855168,5931589⟩, ⟨⟨385,535,112,14923⟩,1686840279040,2221379895⟩⟩,
     ⟨3, ⟨⟨94,130,29,1056⟩,26637762560,8531244⟩, ⟨⟨411,572,120,16387⟩,2056243380224,2904427648⟩⟩,
     ⟨4, ⟨⟨102,141,31,1124⟩,33533460480,11621252⟩, ⟨⟨438,609,128,17863⟩,2488618188800,3734056387⟩⟩,
     ⟨5, ⟨⟨108,150,33,1219⟩,39862927360,14840297⟩, ⟨⟨522,726,153,17129⟩,4214585819136,7540240839⟩⟩,
     ⟨6, ⟨⟨108,149,33,1526⟩,39862927360,14526868⟩, ⟨⟨570,792,167,17978⟩,5481425797120,10673329627⟩⟩,
     ⟨10, ⟨⟨142,197,43,1657⟩,89085444096,43318982⟩, ⟨⟨696,968,204,22736⟩,9967068774400,23761225895⟩⟩,
     ⟨16, ⟨⟨163,226,50,3054⟩,135467106304,75401397⟩, ⟨⟨851,1183,249,31094⟩,18172149760000,52867790342⟩⟩,
     ⟨18, ⟨⟨221,306,68,1932⟩,335886942208,251865996⟩, ⟨⟨952,1324,279,32270⟩,25456515481600,82958819253⟩⟩,
     ⟨24, ⟨⟨212,294,65,4023⟩,295979712512,214017359⟩, ⟨⟨1115,1550,329,40429⟩,41081354321920,156562227172⟩⟩,
     ⟨32, ⟨⟨261,362,82,4914⟩,560158474240,498527994⟩, ⟨⟨1463,2034,430,47329⟩,92429551140864,462204056864⟩⟩,
     ⟨36, ⟨⟨246,341,75,60386⟩,459094360064,384291762⟩, ⟨⟨1220,1696,357,84168⟩,53453923287040,222859445142⟩⟩,
     ⟨42, ⟨⟨279,386,85,58505⟩,667877376000,629746567⟩, ⟨⟨1240,1725,359,190238⟩,55666189271040,236367501665⟩⟩,
     ⟨54, ⟨⟨534,740,167,4102⟩,4737851195392,8580372579⟩, ⟨⟨2252,3131,661,71478⟩,336378654883840,2588552103973⟩⟩,
     ⟨81, ⟨⟨637,883,197,7261⟩,7963588165632,17210339526⟩, ⟨⟨3474,4830,1019,97610⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,8685⟩,0xcf60ca00000,37305519000⟩, ⟨⟨4170,5798,1223,118228⟩,0x7934721300000,30381132426145⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,10888⟩,35306242048000,124373325152⟩, ⟨⟨5487,7630,1607,155971⟩,4851195216658432,90974896361155⟩⟩]
  | .h2420 =>
    [⟨0, ⟨⟨73,101,22,785⟩,12438470656,3108650⟩, ⟨⟨352,489,103,10964⟩,1296449929216,1560122533⟩⟩,
     ⟨1, ⟨⟨78,108,24,901⟩,15341977600,4103823⟩, ⟨⟨345,480,101,13344⟩,1221414354944,1447711168⟩⟩,
     ⟨2, ⟨⟨86,119,26,967⟩,20190855168,5931589⟩, ⟨⟨385,535,112,14225⟩,1686840279040,2221379895⟩⟩,
     ⟨3, ⟨⟨94,130,29,1022⟩,26637762560,8531244⟩, ⟨⟨411,572,120,15625⟩,2056243380224,2904427648⟩⟩,
     ⟨4, ⟨⟨102,141,31,1090⟩,33533460480,11621252⟩, ⟨⟨438,609,128,17039⟩,2488618188800,3734056387⟩⟩,
     ⟨5, ⟨⟨108,150,33,1182⟩,39862927360,14840297⟩, ⟨⟨522,726,153,16534⟩,4214585819136,7540240839⟩⟩,
     ⟨6, ⟨⟨108,149,33,1469⟩,39862927360,14526868⟩, ⟨⟨570,792,167,17397⟩,5481425797120,10673329627⟩⟩,
     ⟨10, ⟨⟨142,197,43,1615⟩,89085444096,43318982⟩, ⟨⟨696,968,204,22025⟩,9967068774400,23761225895⟩⟩,
     ⟨16, ⟨⟨163,226,50,2943⟩,135467106304,75401397⟩, ⟨⟨851,1183,249,30070⟩,18172149760000,52867790342⟩⟩,
     ⟨18, ⟨⟨221,306,68,1905⟩,335886942208,251865996⟩, ⟨⟨952,1324,279,31314⟩,25456515481600,82958819253⟩⟩,
     ⟨24, ⟨⟨212,294,65,3898⟩,295979712512,214017359⟩, ⟨⟨1115,1550,329,39219⟩,41081354321920,156562227172⟩⟩,
     ⟨32, ⟨⟨261,362,82,4780⟩,560158474240,498527994⟩, ⟨⟨1463,2034,430,46120⟩,92429551140864,462204056864⟩⟩,
     ⟨36, ⟨⟨246,341,75,43886⟩,459094360064,384291762⟩, ⟨⟨1220,1696,357,79500⟩,53453923287040,222859445142⟩⟩,
     ⟨42, ⟨⟨279,386,85,45082⟩,667877376000,629746567⟩, ⟨⟨1240,1725,359,167686⟩,55666189271040,236367501665⟩⟩,
     ⟨54, ⟨⟨534,740,167,4069⟩,4737851195392,8580372579⟩, ⟨⟨2252,3131,661,69795⟩,336378654883840,2588552103973⟩⟩,
     ⟨81, ⟨⟨637,883,197,7183⟩,7963588165632,17210339526⟩, ⟨⟨3474,4830,1019,95660⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,8599⟩,0xcf60ca00000,37305519000⟩, ⟨⟨4170,5798,1223,115879⟩,0x7934721300000,30381132426145⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,10796⟩,35306242048000,124373325152⟩, ⟨⟨5487,7630,1607,152904⟩,4851195216658432,90974896361155⟩⟩]
  | .h2440 =>
    [⟨0, ⟨⟨73,101,22,745⟩,12438470656,3108650⟩, ⟨⟨352,489,103,9934⟩,1296449929216,1560122533⟩⟩,
     ⟨1, ⟨⟨78,108,24,854⟩,15341977600,4103823⟩, ⟨⟨345,480,101,11823⟩,1221414354944,1447711168⟩⟩,
     ⟨2, ⟨⟨86,119,26,920⟩,20190855168,5931589⟩, ⟨⟨385,535,112,12680⟩,1686840279040,2221379895⟩⟩,
     ⟨3, ⟨⟨94,130,29,974⟩,26637762560,8531244⟩, ⟨⟨411,572,120,13901⟩,2056243380224,2904427648⟩⟩,
     ⟨4, ⟨⟨102,141,31,1042⟩,33533460480,11621252⟩, ⟨⟨438,609,128,15129⟩,2488618188800,3734056387⟩⟩,
     ⟨5, ⟨⟨108,150,33,1130⟩,39862927360,14840297⟩, ⟨⟨522,726,153,15018⟩,4214585819136,7540240839⟩⟩,
     ⟨6, ⟨⟨108,149,33,1388⟩,39862927360,14526868⟩, ⟨⟨570,792,167,15862⟩,5481425797120,10673329627⟩⟩,
     ⟨10, ⟨⟨142,197,43,1546⟩,89085444096,43318982⟩, ⟨⟨696,968,204,20046⟩,9967068774400,23761225895⟩⟩,
     ⟨16, ⟨⟨163,226,50,2754⟩,135467106304,75401397⟩, ⟨⟨851,1183,249,27113⟩,18172149760000,52867790342⟩⟩,
     ⟨18, ⟨⟨221,306,68,1848⟩,335886942208,251865996⟩, ⟨⟨952,1324,279,28447⟩,25456515481600,82958819253⟩⟩,
     ⟨24, ⟨⟨212,294,65,3657⟩,295979712512,214017359⟩, ⟨⟨1115,1550,329,35435⟩,41081354321920,156562227172⟩⟩,
     ⟨32, ⟨⟨261,362,82,4494⟩,560158474240,498527994⟩, ⟨⟨1463,2034,430,42123⟩,92429551140864,462204056864⟩⟩,
     ⟨36, ⟨⟨246,341,75,27047⟩,459094360064,384291762⟩, ⟨⟨1220,1696,357,66375⟩,53453923287040,222859445142⟩⟩,
     ⟨42, ⟨⟨279,386,85,29009⟩,667877376000,629746567⟩, ⟨⟨1240,1725,359,118786⟩,55666189271040,236367501665⟩⟩,
     ⟨54, ⟨⟨534,740,167,3973⟩,4737851195392,8580372579⟩, ⟨⟨2252,3131,661,63900⟩,336378654883840,2588552103973⟩⟩,
     ⟨81, ⟨⟨637,883,197,6938⟩,7963588165632,17210339526⟩, ⟨⟨3474,4830,1019,88461⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,8314⟩,0xcf60ca00000,37305519000⟩, ⟨⟨4170,5798,1223,107104⟩,0x7934721300000,30381132426145⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,10465⟩,35306242048000,124373325152⟩, ⟨⟨5487,7630,1607,141320⟩,4851195216658432,90974896361155⟩⟩]
  | .h2450 =>
    [⟨0, ⟨⟨73,101,22,728⟩,12438470656,3108650⟩, ⟨⟨352,489,103,9494⟩,1296449929216,1560122533⟩⟩,
     ⟨1, ⟨⟨78,108,24,832⟩,15341977600,4103823⟩, ⟨⟨345,480,101,11193⟩,1221414354944,1447711168⟩⟩,
     ⟨2, ⟨⟨86,119,26,898⟩,20190855168,5931589⟩, ⟨⟨385,535,112,12034⟩,1686840279040,2221379895⟩⟩,
     ⟨3, ⟨⟨94,130,29,953⟩,26637762560,8531244⟩, ⟨⟨411,572,120,13183⟩,2056243380224,2904427648⟩⟩,
     ⟨4, ⟨⟨102,141,31,1020⟩,33533460480,11621252⟩, ⟨⟨438,609,128,14336⟩,2488618188800,3734056387⟩⟩,
     ⟨5, ⟨⟨108,150,33,1106⟩,39862927360,14840297⟩, ⟨⟨522,726,153,14367⟩,4214585819136,7540240839⟩⟩,
     ⟨6, ⟨⟨108,149,33,1352⟩,39862927360,14526868⟩, ⟨⟨570,792,167,15200⟩,5481425797120,10673329627⟩⟩,
     ⟨10, ⟨⟨142,197,43,1514⟩,89085444096,43318982⟩, ⟨⟨696,968,204,19195⟩,9967068774400,23761225895⟩⟩,
     ⟨16, ⟨⟨163,226,50,2670⟩,135467106304,75401397⟩, ⟨⟨851,1183,249,25857⟩,18172149760000,52867790342⟩⟩,
     ⟨18, ⟨⟨221,306,68,1821⟩,335886942208,251865996⟩, ⟨⟨952,1324,279,27216⟩,25456515481600,82958819253⟩⟩,
     ⟨24, ⟨⟨212,294,65,3549⟩,295979712512,214017359⟩, ⟨⟨1115,1550,329,33823⟩,41081354321920,156562227172⟩⟩,
     ⟨32, ⟨⟨261,362,82,4365⟩,560158474240,498527994⟩, ⟨⟨1463,2034,430,40394⟩,92429551140864,462204056864⟩⟩,
     ⟨36, ⟨⟨246,341,75,22738⟩,459094360064,384291762⟩, ⟨⟨1220,1696,357,61371⟩,53453923287040,222859445142⟩⟩,
     ⟨42, ⟨⟨279,386,85,24666⟩,667877376000,629746567⟩, ⟨⟨1240,1725,359,103831⟩,55666189271040,236367501665⟩⟩,
     ⟨54, ⟨⟨534,740,167,3927⟩,4737851195392,8580372579⟩, ⟨⟨2252,3131,661,61341⟩,336378654883840,2588552103973⟩⟩,
     ⟨81, ⟨⟨637,883,197,6823⟩,7963588165632,17210339526⟩, ⟨⟨3474,4830,1019,85291⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,8180⟩,0xcf60ca00000,37305519000⟩, ⟨⟨4170,5798,1223,103242⟩,0x7934721300000,30381132426145⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,10309⟩,35306242048000,124373325152⟩, ⟨⟨5487,7630,1607,136223⟩,4851195216658432,90974896361155⟩⟩]
  | .h2460 =>
    [⟨0, ⟨⟨73,101,22,711⟩,12438470656,3108650⟩, ⟨⟨352,489,103,9094⟩,1296449929216,1560122533⟩⟩,
     ⟨1, ⟨⟨78,108,24,812⟩,15341977600,4103823⟩, ⟨⟨345,480,101,10631⟩,1221414354944,1447711168⟩⟩,
     ⟨2, ⟨⟨86,119,26,878⟩,20190855168,5931589⟩, ⟨⟨385,535,112,11456⟩,1686840279040,2221379895⟩⟩,
     ⟨3, ⟨⟨94,130,29,932⟩,26637762560,8531244⟩, ⟨⟨411,572,120,12540⟩,2056243380224,2904427648⟩⟩,
     ⟨4, ⟨⟨102,141,31,998⟩,33533460480,11621252⟩, ⟨⟨438,609,128,13627⟩,2488618188800,3734056387⟩⟩,
     ⟨5, ⟨⟨108,150,33,1083⟩,39862927360,14840297⟩, ⟨⟨522,726,153,13775⟩,4214585819136,7540240839⟩⟩,
     ⟨6, ⟨⟨108,149,33,1317⟩,39862927360,14526868⟩, ⟨⟨570,792,167,14596⟩,5481425797120,10673329627⟩⟩,
     ⟨10, ⟨⟨142,197,43,1484⟩,89085444096,43318982⟩, ⟨⟨696,968,204,18418⟩,9967068774400,23761225895⟩⟩,
     ⟨16, ⟨⟨163,226,50,2591⟩,135467106304,75401397⟩, ⟨⟨851,1183,249,24722⟩,18172149760000,52867790342⟩⟩,
     ⟨18, ⟨⟨221,306,68,1795⟩,335886942208,251865996⟩, ⟨⟨952,1324,279,26096⟩,25456515481600,82958819253⟩⟩,
     ⟨24, ⟨⟨212,294,65,3447⟩,295979712512,214017359⟩, ⟨⟨1115,1550,329,32363⟩,41081354321920,156562227172⟩⟩,
     ⟨32, ⟨⟨261,362,82,4244⟩,560158474240,498527994⟩, ⟨⟨1463,2034,430,38814⟩,92429551140864,462204056864⟩⟩,
     ⟨36, ⟨⟨246,341,75,19636⟩,459094360064,384291762⟩, ⟨⟨1220,1696,357,57101⟩,53453923287040,222859445142⟩⟩,
     ⟨42, ⟨⟨279,386,85,21477⟩,667877376000,629746567⟩, ⟨⟨1240,1725,359,92304⟩,55666189271040,236367501665⟩⟩,
     ⟨54, ⟨⟨534,740,167,3883⟩,4737851195392,8580372579⟩, ⟨⟨2252,3131,661,58997⟩,336378654883840,2588552103973⟩⟩,
     ⟨81, ⟨⟨637,883,197,6713⟩,7963588165632,17210339526⟩, ⟨⟨3474,4830,1019,82363⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,8051⟩,0xcf60ca00000,37305519000⟩, ⟨⟨4170,5798,1223,99678⟩,0x7934721300000,30381132426145⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,10158⟩,35306242048000,124373325152⟩, ⟨⟨5487,7630,1607,131518⟩,4851195216658432,90974896361155⟩⟩]
  | .h2480 =>
    [⟨0, ⟨⟨73,101,22,679⟩,12438470656,3108650⟩, ⟨⟨352,489,103,8396⟩,1296449929216,1560122533⟩⟩,
     ⟨1, ⟨⟨78,108,24,775⟩,15341977600,4103823⟩, ⟨⟨345,480,101,9671⟩,1221414354944,1447711168⟩⟩,
     ⟨2, ⟨⟨86,119,26,840⟩,20190855168,5931589⟩, ⟨⟨385,535,112,10462⟩,1686840279040,2221379895⟩⟩,
     ⟨3, ⟨⟨94,130,29,894⟩,26637762560,8531244⟩, ⟨⟨411,572,120,11438⟩,2056243380224,2904427648⟩⟩,
     ⟨4, ⟨⟨102,141,31,959⟩,33533460480,11621252⟩, ⟨⟨438,609,128,12414⟩,2488618188800,3734056387⟩⟩,
     ⟨5, ⟨⟨108,150,33,1040⟩,39862927360,14840297⟩, ⟨⟨522,726,153,12738⟩,4214585819136,7540240839⟩⟩,
     ⟨6, ⟨⟨108,149,33,1254⟩,39862927360,14526868⟩, ⟨⟨570,792,167,13532⟩,5481425797120,10673329627⟩⟩,
     ⟨10, ⟨⟨142,197,43,1427⟩,89085444096,43318982⟩, ⟨⟨696,968,204,17055⟩,9967068774400,23761225895⟩⟩,
     ⟨16, ⟨⟨163,226,50,2448⟩,135467106304,75401397⟩, ⟨⟨851,1183,249,22747⟩,18172149760000,52867790342⟩⟩,
     ⟨18, ⟨⟨221,306,68,1746⟩,335886942208,251865996⟩, ⟨⟨952,1324,279,24133⟩,25456515481600,82958819253⟩⟩,
     ⟨24, ⟨⟨212,294,65,3263⟩,295979712512,214017359⟩, ⟨⟨1115,1550,329,29819⟩,41081354321920,156562227172⟩⟩,
     ⟨32, ⟨⟨261,362,82,4024⟩,560158474240,498527994⟩, ⟨⟨1463,2034,430,36029⟩,92429551140864,462204056864⟩⟩,
     ⟨36, ⟨⟨246,341,75,15466⟩,459094360064,384291762⟩, ⟨⟨1220,1696,357,50199⟩,53453923287040,222859445142⟩⟩,
     ⟨42, ⟨⟨279,386,85,17106⟩,667877376000,629746567⟩, ⟨⟨1240,1725,359,75698⟩,55666189271040,236367501665⟩⟩,
     ⟨54, ⟨⟨534,740,167,3798⟩,4737851195392,8580372579⟩, ⟨⟨2252,3131,661,54856⟩,336378654883840,2588552103973⟩⟩,
     ⟨81, ⟨⟨637,883,197,6506⟩,7963588165632,17210339526⟩, ⟨⟨3474,4830,1019,77132⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,7808⟩,0xcf60ca00000,37305519000⟩, ⟨⟨4170,5798,1223,93312⟩,0x7934721300000,30381132426145⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,9874⟩,35306242048000,124373325152⟩, ⟨⟨5487,7630,1607,123116⟩,4851195216658432,90974896361155⟩⟩]
  | .h2500 =>
    [⟨0, ⟨⟨67,93,20,744⟩,9604431872,2228964⟩, ⟨⟨280,389,81,8690⟩,649184149504,622002556⟩⟩,
     ⟨1, ⟨⟨73,101,22,835⟩,12438470656,3108650⟩, ⟨⟨325,452,94,9210⟩,0xebc42c0000,1129274177⟩⟩,
     ⟨2, ⟨⟨73,101,22,1163⟩,12438470656,3108650⟩, ⟨⟨360,501,105,9956⟩,1383041597440,1711611949⟩⟩,
     ⟨4, ⟨⟨96,133,30,1003⟩,28613279744,9411251⟩, ⟨⟨438,609,128,11414⟩,2488618188800,3734056387⟩⟩,
     ⟨6, ⟨⟨106,147,33,1225⟩,38240780288,13913593⟩, ⟨⟨485,674,140,13437⟩,3343671623680,5543427992⟩⟩,
     ⟨10, ⟨⟨134,186,40,1551⟩,74214277120,34121885⟩, ⟨⟨593,825,173,17018⟩,6150084362240,12507204741⟩⟩,
     ⟨16, ⟨⟨171,237,52,2060⟩,155191869440,90459259⟩, ⟨⟨804,1118,239,21820⟩,0xe1c7ba00000,42702576640⟩⟩,
     ⟨24, ⟨⟨208,288,64,3314⟩,280399708160,197963022⟩, ⟨⟨985,1370,289,29761⟩,28216312463360,95160984481⟩⟩,
     ⟨36, ⟨⟨253,351,78,8539⟩,503341383680,434522864⟩, ⟨⟨985,1370,289,89368⟩,28216312463360,95160984481⟩⟩,
     ⟨54, ⟨⟨438,607,139,4598⟩,2648411996160,3938005884⟩, ⟨⟨2009,2793,594,53430⟩,0xda7987240000,1649110555219⟩⟩,
     ⟨81, ⟨⟨593,822,188,7233⟩,6549464678400,13184443531⟩, ⟨⟨2730,3796,810,78509⟩,603993145344000,5637020026038⟩⟩]
  | .h2520 =>
    [⟨0, ⟨⟨60,83,18,921⟩,6978011136,1437938⟩, ⟨⟨261,363,75,8474⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,868⟩,10960502784,2641452⟩, ⟨⟨311,432,91,8671⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,968⟩,14043578368,3635193⟩, ⟨⟨320,445,93,10004⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1245⟩,20190855168,5931589⟩, ⟨⟨393,546,113,11372⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,1129⟩,29954146304,10105062⟩, ⟨⟨425,591,124,11993⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1209⟩,36607098880,13013367⟩, ⟨⟨456,634,132,12828⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1743⟩,60131901440,25559185⟩, ⟨⟨558,776,163,16381⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1976⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,20760⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2472⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,22890⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2936⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,26912⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,5980⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,53906⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3482⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,37015⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,9675⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,72054⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4938⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,51832⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,6470⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,74315⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,7659⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,86317⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2530 =>
    [⟨0, ⟨⟨60,83,18,888⟩,6978011136,1437938⟩, ⟨⟨261,363,75,8052⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,844⟩,10960502784,2641452⟩, ⟨⟨311,432,91,8308⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,941⟩,14043578368,3635193⟩, ⟨⟨320,445,93,9538⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1208⟩,20190855168,5931589⟩, ⟨⟨393,546,113,10889⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,1103⟩,29954146304,10105062⟩, ⟨⟨425,591,124,11503⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1182⟩,36607098880,13013367⟩, ⟨⟨456,634,132,12308⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1698⟩,60131901440,25559185⟩, ⟨⟨558,776,163,15703⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1938⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,19979⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2412⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,21980⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2870⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,25939⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,5744⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,49830⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3420⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,35646⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,9179⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,66171⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4852⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,49926⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,6373⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,71543⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,7548⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,83413⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2540 =>
    [⟨0, ⟨⟨60,83,18,857⟩,6978011136,1437938⟩, ⟨⟨261,363,75,7673⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,822⟩,10960502784,2641452⟩, ⟨⟨311,432,91,7977⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,916⟩,14043578368,3635193⟩, ⟨⟨320,445,93,9117⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1173⟩,20190855168,5931589⟩, ⟨⟨393,546,113,10449⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,1079⟩,29954146304,10105062⟩, ⟨⟨425,591,124,11056⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1157⟩,36607098880,13013367⟩, ⟨⟨456,634,132,11832⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1655⟩,60131901440,25559185⟩, ⟨⟨558,776,163,15084⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1900⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,19260⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2356⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,21146⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2808⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,25042⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,5527⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,46353⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3361⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,34384⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,8736⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,61212⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4769⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,48169⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,6279⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,68990⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,7442⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,80718⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2550 =>
    [⟨0, ⟨⟨60,83,18,829⟩,6978011136,1437938⟩, ⟨⟨261,363,75,7330⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,801⟩,10960502784,2641452⟩, ⟨⟨311,432,91,7673⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,892⟩,14043578368,3635193⟩, ⟨⟨320,445,93,8735⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1141⟩,20190855168,5931589⟩, ⟨⟨393,546,113,10046⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,1056⟩,29954146304,10105062⟩, ⟨⟨425,591,124,10644⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1132⟩,36607098880,13013367⟩, ⟨⟨456,634,132,11394⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1615⟩,60131901440,25559185⟩, ⟨⟨558,776,163,14516⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1865⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,18596⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2303⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,20379⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2748⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,24211⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,5328⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,43352⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3304⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,33218⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,8336⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,56976⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4689⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,46544⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,6189⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,66631⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,7340⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,78212⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2560 =>
    [⟨0, ⟨⟨60,83,18,802⟩,6978011136,1437938⟩, ⟨⟨261,363,75,7020⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,781⟩,10960502784,2641452⟩, ⟨⟨311,432,91,7394⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,870⟩,14043578368,3635193⟩, ⟨⟨320,445,93,8386⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1110⟩,20190855168,5931589⟩, ⟨⟨393,546,113,9676⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,1034⟩,29954146304,10105062⟩, ⟨⟨425,591,124,10266⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1109⟩,36607098880,13013367⟩, ⟨⟨456,634,132,10991⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1578⟩,60131901440,25559185⟩, ⟨⟨558,776,163,13993⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1831⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,17981⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2253⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,19671⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2692⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,23439⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,5144⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,40735⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3249⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,32136⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,7974⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,53314⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4613⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,45036⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,6102⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,64445⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,7241⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,75873⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2570 =>
    [⟨0, ⟨⟨60,83,18,778⟩,6978011136,1437938⟩, ⟨⟨261,363,75,6736⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,762⟩,10960502784,2641452⟩, ⟨⟨311,432,91,7137⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,849⟩,14043578368,3635193⟩, ⟨⟨320,445,93,8066⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1081⟩,20190855168,5931589⟩, ⟨⟨393,546,113,9334⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,1013⟩,29954146304,10105062⟩, ⟨⟨425,591,124,9915⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1087⟩,36607098880,13013367⟩, ⟨⟨456,634,132,10618⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1542⟩,60131901440,25559185⟩, ⟨⟨558,776,163,13510⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1799⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,17410⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2205⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,19016⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2638⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,22720⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,4973⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,38433⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3197⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,31130⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,7645⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,50119⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4540⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,43633⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,6017⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,62413⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,7145⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,73688⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2585 =>
    [⟨0, ⟨⟨60,83,18,744⟩,6978011136,1437938⟩, ⟨⟨261,363,75,6355⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,735⟩,10960502784,2641452⟩, ⟨⟨311,432,91,6786⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,820⟩,14043578368,3635193⟩, ⟨⟨320,445,93,7634⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1041⟩,20190855168,5931589⟩, ⟨⟨393,546,113,8870⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,983⟩,29954146304,10105062⟩, ⟨⟨425,591,124,9437⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1055⟩,36607098880,13013367⟩, ⟨⟨456,634,132,10109⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1491⟩,60131901440,25559185⟩, ⟨⟨558,776,163,12851⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1753⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,16625⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2137⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,18119⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2562⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,21730⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,4740⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,35456⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3122⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,29746⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,7203⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,46021⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4435⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,41704⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,5897⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,59620⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,7008⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,70664⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2590 =>
    [⟨0, ⟨⟨60,83,18,733⟩,6978011136,1437938⟩, ⟨⟨261,363,75,6238⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,727⟩,10960502784,2641452⟩, ⟨⟨311,432,91,6677⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,810⟩,14043578368,3635193⟩, ⟨⟨320,445,93,7500⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1029⟩,20190855168,5931589⟩, ⟨⟨393,546,113,8726⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,974⟩,29954146304,10105062⟩, ⟨⟨425,591,124,9289⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1045⟩,36607098880,13013367⟩, ⟨⟨456,634,132,9951⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1476⟩,60131901440,25559185⟩, ⟨⟨558,776,163,12647⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1738⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,16381⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2116⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,17840⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2538⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,21422⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,4667⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,34570⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3098⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,29315⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,7067⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,44809⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4401⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,41103⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,5858⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,58750⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,6964⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,69717⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2600 =>
    [⟨0, ⟨⟨60,83,18,713⟩,6978011136,1437938⟩, ⟨⟨261,363,75,6018⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,711⟩,10960502784,2641452⟩, ⟨⟨311,432,91,6471⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,793⟩,14043578368,3635193⟩, ⟨⟨320,445,93,7249⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1005⟩,20190855168,5931589⟩, ⟨⟨393,546,113,8453⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,955⟩,29954146304,10105062⟩, ⟨⟨425,591,124,9008⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1026⟩,36607098880,13013367⟩, ⟨⟨456,634,132,9651⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1445⟩,60131901440,25559185⟩, ⟨⟨558,776,163,12260⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1709⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,15916⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2074⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,17311⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2492⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,20833⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,4529⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,32935⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3051⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,28495⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,6813⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,42579⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4336⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,39957⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,5782⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,57094⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,6877⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,67909⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2601 =>
    [⟨0, ⟨⟨60,83,18,711⟩,6978011136,1437938⟩, ⟨⟨261,363,75,5997⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,710⟩,10960502784,2641452⟩, ⟨⟨311,432,91,6451⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,791⟩,14043578368,3635193⟩, ⟨⟨320,445,93,7225⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1002⟩,20190855168,5931589⟩, ⟨⟨393,546,113,8427⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨91,126,27,1143⟩,23524802560,7319461⟩, ⟨⟨416,579,117,9452⟩,2071969136640,2960992207⟩⟩,
     ⟨6, ⟨⟨105,145,32,1024⟩,36607098880,13013367⟩, ⟨⟨456,634,132,9622⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨129,179,39,1344⟩,66930606080,29610973⟩, ⟨⟨580,806,168,12109⟩,5724127625216,11343589427⟩⟩,
     ⟨16, ⟨⟨171,237,52,1706⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,15871⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨163,226,51,2478⟩,137473556480,76546979⟩, ⟨⟨652,907,184,21252⟩,7963633254400,17788313333⟩⟩,
     ⟨24, ⟨⟨186,258,57,4171⟩,200431370240,127350358⟩, ⟨⟨716,996,207,29933⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨32, ⟨⟨214,297,65,11376⟩,302242856960,221096948⟩, ⟨⟨817,1135,232,53020⟩,0xe4bfae40000,43795155603⟩⟩,
     ⟨36, ⟨⟨302,418,94,3047⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,28415⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨417,578,129,4330⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,39847⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,5775⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,56935⟩,543617725235200,4924236090842⟩⟩]
  | .h2611 =>
    [⟨0, ⟨⟨60,83,18,692⟩,6978011136,1437938⟩, ⟨⟨261,363,75,5795⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,694⟩,10960502784,2641452⟩, ⟨⟨311,432,91,6260⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,774⟩,14043578368,3635193⟩, ⟨⟨320,445,93,6994⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,980⟩,20190855168,5931589⟩, ⟨⟨393,546,113,8175⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨91,126,27,1116⟩,23524802560,7319461⟩, ⟨⟨416,579,117,9152⟩,2071969136640,2960992207⟩⟩,
     ⟨6, ⟨⟨105,145,32,1006⟩,36607098880,13013367⟩, ⟨⟨456,634,132,9344⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨129,179,39,1319⟩,66930606080,29610973⟩, ⟨⟨580,806,168,11769⟩,5724127625216,11343589427⟩⟩,
     ⟨16, ⟨⟨171,237,52,1679⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,15437⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨163,226,51,2417⟩,137473556480,76546979⟩, ⟨⟨652,907,184,20331⟩,7963633254400,17788313333⟩⟩,
     ⟨24, ⟨⟨186,258,57,4027⟩,200431370240,127350358⟩, ⟨⟨716,996,207,28320⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨32, ⟨⟨214,297,65,10509⟩,302242856960,221096948⟩, ⟨⟨817,1135,232,48698⟩,0xe4bfae40000,43795155603⟩⟩,
     ⟨36, ⟨⟨302,418,94,3002⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,27650⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨417,578,129,4267⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,38778⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,5702⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,55391⟩,543617725235200,4924236090842⟩⟩]
  | .h2621 =>
    [⟨0, ⟨⟨60,83,18,675⟩,6978011136,1437938⟩, ⟨⟨261,363,75,5608⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,680⟩,10960502784,2641452⟩, ⟨⟨311,432,91,6082⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,758⟩,14043578368,3635193⟩, ⟨⟨320,445,93,6778⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,958⟩,20190855168,5931589⟩, ⟨⟨393,546,113,7939⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨91,126,27,1090⟩,23524802560,7319461⟩, ⟨⟨416,579,117,8872⟩,2071969136640,2960992207⟩⟩,
     ⟨6, ⟨⟨105,145,32,988⟩,36607098880,13013367⟩, ⟨⟨456,634,132,9083⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨129,179,39,1296⟩,66930606080,29610973⟩, ⟨⟨580,806,168,11450⟩,5724127625216,11343589427⟩⟩,
     ⟨16, ⟨⟨171,237,52,1653⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,15030⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨163,226,51,2359⟩,137473556480,76546979⟩, ⟨⟨652,907,184,19493⟩,7963633254400,17788313333⟩⟩,
     ⟨24, ⟨⟨186,258,57,3893⟩,200431370240,127350358⟩, ⟨⟨716,996,207,26883⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨32, ⟨⟨214,297,65,9769⟩,302242856960,221096948⟩, ⟨⟨817,1135,232,45054⟩,0xe4bfae40000,43795155603⟩⟩,
     ⟨36, ⟨⟨302,418,94,2959⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,26930⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨417,578,129,4207⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,37773⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,5631⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,53939⟩,543617725235200,4924236090842⟩⟩]
  | .h2640 =>
    [⟨0, ⟨⟨60,83,18,644⟩,6978011136,1437938⟩, ⟨⟨261,363,75,5287⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,655⟩,10960502784,2641452⟩, ⟨⟨311,432,91,5772⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,730⟩,14043578368,3635193⟩, ⟨⟨320,445,93,6407⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,920⟩,20190855168,5931589⟩, ⟨⟨393,546,113,7531⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨91,126,27,1045⟩,23524802560,7319461⟩, ⟨⟨416,579,117,8390⟩,2071969136640,2960992207⟩⟩,
     ⟨6, ⟨⟨105,145,32,957⟩,36607098880,13013367⟩, ⟨⟨456,634,132,8630⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨129,179,39,1255⟩,66930606080,29610973⟩, ⟨⟨580,806,168,10895⟩,5724127625216,11343589427⟩⟩,
     ⟨16, ⟨⟨171,237,52,1606⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,14320⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨163,226,51,2258⟩,137473556480,76546979⟩, ⟨⟨652,907,184,18091⟩,7963633254400,17788313333⟩⟩,
     ⟨24, ⟨⟨186,258,57,3664⟩,200431370240,127350358⟩, ⟨⟨716,996,207,24543⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨32, ⟨⟨214,297,65,8628⟩,302242856960,221096948⟩, ⟨⟨817,1135,232,39499⟩,0xe4bfae40000,43795155603⟩⟩,
     ⟨36, ⟨⟨302,418,94,2881⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,25673⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨417,578,129,4098⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,36018⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,5503⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,51408⟩,543617725235200,4924236090842⟩⟩]
  | .h2670 =>
    [⟨0, ⟨⟨60,83,18,601⟩,6978011136,1437938⟩, ⟨⟨261,363,75,4856⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,619⟩,10960502784,2641452⟩, ⟨⟨311,432,91,5350⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,690⟩,14043578368,3635193⟩, ⟨⟨320,445,93,5906⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,866⟩,20190855168,5931589⟩, ⟨⟨393,546,113,6975⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨91,126,27,981⟩,23524802560,7319461⟩, ⟨⟨416,579,117,7738⟩,2071969136640,2960992207⟩⟩,
     ⟨6, ⟨⟨105,145,32,912⟩,36607098880,13013367⟩, ⟨⟨456,634,132,8011⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨129,179,39,1197⟩,66930606080,29610973⟩, ⟨⟨580,806,168,10134⟩,5724127625216,11343589427⟩⟩,
     ⟨16, ⟨⟨171,237,52,1537⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,13343⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨163,226,51,2118⟩,137473556480,76546979⟩, ⟨⟨652,907,184,16276⟩,7963633254400,17788313333⟩⟩,
     ⟨24, ⟨⟨186,258,57,3358⟩,200431370240,127350358⟩, ⟨⟨716,996,207,21624⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨32, ⟨⟨214,297,65,7305⟩,302242856960,221096948⟩, ⟨⟨817,1135,232,33161⟩,0xe4bfae40000,43795155603⟩⟩,
     ⟨36, ⟨⟨302,418,94,2768⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,23942⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨417,578,129,3940⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,33599⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,5315⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,47922⟩,543617725235200,4924236090842⟩⟩]
  | .h2700 =>
    [⟨0, ⟨⟨60,83,18,564⟩,6978011136,1437938⟩, ⟨⟨261,363,75,4497⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,587⟩,10960502784,2641452⟩, ⟨⟨311,432,91,4993⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,654⟩,14043578368,3635193⟩, ⟨⟨320,445,93,5486⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,820⟩,20190855168,5931589⟩, ⟨⟨393,546,113,6505⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨91,126,27,926⟩,23524802560,7319461⟩, ⟨⟨416,579,117,7191⟩,2071969136640,2960992207⟩⟩,
     ⟨6, ⟨⟨105,145,32,872⟩,36607098880,13013367⟩, ⟨⟨456,634,132,7486⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨129,179,39,1144⟩,66930606080,29610973⟩, ⟨⟨580,806,168,9486⟩,5724127625216,11343589427⟩⟩,
     ⟨16, ⟨⟨171,237,52,1476⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,12509⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨163,226,51,1997⟩,137473556480,76546979⟩, ⟨⟨652,907,184,14823⟩,7963633254400,17788313333⟩⟩,
     ⟨24, ⟨⟨186,258,57,3105⟩,200431370240,127350358⟩, ⟨⟨716,996,207,19372⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨32, ⟨⟨214,297,65,6353⟩,302242856960,221096948⟩, ⟨⟨817,1135,232,28664⟩,0xe4bfae40000,43795155603⟩⟩,
     ⟨36, ⟨⟨302,418,94,2666⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,22461⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨417,578,129,3796⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,31528⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,5144⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,44941⟩,543617725235200,4924236090842⟩⟩]
  | .h2750 =>
    [⟨0, ⟨⟨60,83,18,513⟩,6978011136,1437938⟩, ⟨⟨261,363,75,4017⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,542⟩,10960502784,2641452⟩, ⟨⟨311,432,91,4506⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,605⟩,14043578368,3635193⟩, ⟨⟨320,445,93,4920⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,754⟩,20190855168,5931589⟩, ⟨⟨393,546,113,5866⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨91,126,27,849⟩,23524802560,7319461⟩, ⟨⟨416,579,117,6454⟩,2071969136640,2960992207⟩⟩,
     ⟨6, ⟨⟨105,145,32,814⟩,36607098880,13013367⟩, ⟨⟨456,634,132,6769⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨129,179,39,1068⟩,66930606080,29610973⟩, ⟨⟨580,806,168,8596⟩,5724127625216,11343589427⟩⟩,
     ⟨16, ⟨⟨171,237,52,1387⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,11359⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨163,226,51,1827⟩,137473556480,76546979⟩, ⟨⟨652,907,184,12950⟩,7963633254400,17788313333⟩⟩,
     ⟨24, ⟨⟨186,258,57,2767⟩,200431370240,127350358⟩, ⟨⟨716,996,207,16577⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨32, ⟨⟨214,297,65,5246⟩,302242856960,221096948⟩, ⟨⟨817,1135,232,23505⟩,0xe4bfae40000,43795155603⟩⟩,
     ⟨36, ⟨⟨302,418,94,2516⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,20417⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨417,578,129,3585⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,28669⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,4888⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,40832⟩,543617725235200,4924236090842⟩⟩]
  | .h2800 =>
    [⟨0, ⟨⟨58,80,17,503⟩,6215172096,1227093⟩, ⟨⟨241,335,70,3607⟩,416374063104,344250867⟩⟩,
     ⟨1, ⟨⟨67,93,20,528⟩,9604431872,2228964⟩, ⟨⟨280,389,81,4036⟩,649184149504,622002556⟩⟩,
     ⟨2, ⟨⟨73,101,22,587⟩,12438470656,3108650⟩, ⟨⟨280,389,81,4450⟩,649184149504,622002556⟩⟩,
     ⟨4, ⟨⟨84,116,26,719⟩,19164561408,5468512⟩, ⟨⟨325,452,94,5301⟩,0xebc42c0000,1129274177⟩⟩,
     ⟨6, ⟨⟨96,133,30,841⟩,28613279744,9411251⟩, ⟨⟨397,552,116,6113⟩,1855024005120,2523691858⟩⟩,
     ⟨10, ⟨⟨122,169,38,1064⟩,57995165696,24161620⟩, ⟨⟨485,674,140,7810⟩,3343671623680,5543427992⟩⟩,
     ⟨16, ⟨⟨171,237,52,1310⟩,155191869440,90459259⟩, ⟨⟨656,912,194,10335⟩,8405942272000,18868434791⟩⟩,
     ⟨24, ⟨⟨208,288,64,1918⟩,280399708160,197963022⟩, ⟨⟨890,1237,263,13653⟩,20938983735296,63680038117⟩⟩,
     ⟨36, ⟨⟨241,334,76,4171⟩,442881015808,363216208⟩, ⟨⟨846,1177,251,23628⟩,18044378677248,52336361555⟩⟩,
     ⟨54, ⟨⟨417,577,129,3409⟩,2243231744000,3158702492⟩, ⟨⟨1557,2166,459,26437⟩,0x658b06900000,595336955222⟩⟩,
     ⟨81, ⟨⟨564,782,178,5237⟩,5617949081600,10765253509⟩, ⟨⟨2342,3257,695,37625⟩,381495224041472,3056207072401⟩⟩]
  | .h2900 =>
    [⟨0, ⟨⟨54,75,16,459⟩,5084807168,957077⟩, ⟨⟨208,289,59,2996⟩,263771914240,188037891⟩⟩,
     ⟨1, ⟨⟨61,84,18,516⟩,7237009408,1493513⟩, ⟨⟨241,335,70,3341⟩,416374063104,344250867⟩⟩,
     ⟨2, ⟨⟨64,89,19,610⟩,8365015040,1866743⟩, ⟨⟨253,352,72,3719⟩,473877446656,412256635⟩⟩,
     ⟨4, ⟨⟨84,116,26,628⟩,19164561408,5468512⟩, ⟨⟨325,452,94,4417⟩,0xebc42c0000,1129274177⟩⟩,
     ⟨6, ⟨⟨96,133,30,737⟩,28613279744,9411251⟩, ⟨⟨360,501,105,5132⟩,1383041597440,1711611949⟩⟩,
     ⟨10, ⟨⟨128,177,39,904⟩,65782415360,28566713⟩, ⟨⟨485,675,140,6569⟩,3343671623680,5569859382⟩⟩,
     ⟨16, ⟨⟨148,205,45,1430⟩,101033181184,50931776⟩, ⟨⟨593,825,173,8713⟩,6150084362240,12507204741⟩⟩,
     ⟨24, ⟨⟨171,237,52,2896⟩,155191869440,90459259⟩, ⟨⟨564,784,164,14625⟩,5280188334080,10186247915⟩⟩,
     ⟨36, ⟨⟨280,388,88,2375⟩,690965446656,657571316⟩, ⟨⟨1090,1516,321,15881⟩,38326569795584,143016000830⟩⟩,
     ⟨54, ⟨⟨593,821,188,2728⟩,6549464678400,13132884772⟩, ⟨⟨1814,2523,537,22682⟩,0xa10619640000,0xffe856d21a⟩⟩,
     ⟨81, ⟨⟨564,781,178,4736⟩,5617949081600,10721014375⟩, ⟨⟨2225,3095,660,32065⟩,327058085642240,2491104440193⟩⟩]
  | .h2950 =>
    [⟨0, ⟨⟨57,79,17,401⟩,5981601792,1179228⟩, ⟨⟨190,264,55,2742⟩,204603392000,133373011⟩⟩,
     ⟨1, ⟨⟨63,87,19,454⟩,8079278080,1737013⟩, ⟨⟨210,291,61,3100⟩,276307902464,197239731⟩⟩,
     ⟨2, ⟨⟨70,97,21,502⟩,10960502784,2641452⟩, ⟨⟨233,323,68,3439⟩,377887129600,299518730⟩⟩,
     ⟨4, ⟨⟨82,113,25,611⟩,17656184832,4885777⟩, ⟨⟨263,365,76,4152⟩,538134446080,482812069⟩⟩,
     ⟨5, ⟨⟨86,119,26,680⟩,20190855168,5931589⟩, ⟨⟨267,371,79,4676⟩,573046784000,524154366⟩⟩,
     ⟨6, ⟨⟨92,127,28,736⟩,24752685056,7713813⟩, ⟨⟨311,432,91,4819⟩,895738707968,952519333⟩⟩,
     ⟨10, ⟨⟨117,162,36,938⟩,50775982080,20261980⟩, ⟨⟨360,500,105,6457⟩,1383041597440,1700679003⟩⟩,
     ⟨16, ⟨⟨152,210,47,1281⟩,110731722752,56864480⟩, ⟨⟨477,662,139,8611⟩,3204474470400,5203785784⟩⟩,
     ⟨18, ⟨⟨146,202,44,1824⟩,96396902400,47762018⟩, ⟨⟨416,578,117,12867⟩,2071969136640,2944634929⟩⟩,
     ⟨24, ⟨⟨208,288,64,1628⟩,280399708160,197963022⟩, ⟨⟨635,882,186,11449⟩,7570694078464,16399828679⟩⟩,
     ⟨32, ⟨⟨214,296,65,3238⟩,302242856960,218719650⟩, ⟨⟨616,856,174,21716⟩,6723698688000,14142442253⟩⟩,
     ⟨54, ⟨⟨377,521,117,3414⟩,1663607242752,2110154682⟩, ⟨⟨1182,1642,341,22699⟩,48093513646080,193780511162⟩⟩,
     ⟨81, ⟨⟨563,779,173,4593⟩,5476835655680,10401501082⟩, ⟨⟨1729,2402,504,31993⟩,0x89d0bdc40000,893089263594⟩⟩]
  | .h2980 =>
    [⟨0, ⟨⟨57,79,17,386⟩,5981601792,1179228⟩, ⟨⟨190,264,55,2602⟩,204603392000,133373011⟩⟩,
     ⟨1, ⟨⟨63,87,19,438⟩,8079278080,1737013⟩, ⟨⟨210,291,61,2941⟩,276307902464,197239731⟩⟩,
     ⟨2, ⟨⟨70,97,21,485⟩,10960502784,2641452⟩, ⟨⟨233,323,68,3267⟩,377887129600,299518730⟩⟩,
     ⟨4, ⟨⟨82,113,25,590⟩,17656184832,4885777⟩, ⟨⟨263,365,76,3934⟩,538134446080,482812069⟩⟩,
     ⟨5, ⟨⟨86,119,26,656⟩,20190855168,5931589⟩, ⟨⟨267,371,79,4407⟩,573046784000,524154366⟩⟩,
     ⟨6, ⟨⟨92,127,28,710⟩,24752685056,7713813⟩, ⟨⟨311,432,91,4578⟩,895738707968,952519333⟩⟩,
     ⟨10, ⟨⟨117,162,36,908⟩,50775982080,20261980⟩, ⟨⟨360,500,105,6091⟩,1383041597440,1700679003⟩⟩,
     ⟨16, ⟨⟨152,210,47,1240⟩,110731722752,56864480⟩, ⟨⟨477,662,139,8133⟩,3204474470400,5203785784⟩⟩,
     ⟨18, ⟨⟨146,202,44,1738⟩,96396902400,47762018⟩, ⟨⟨416,578,117,11657⟩,2071969136640,2944634929⟩⟩,
     ⟨24, ⟨⟨208,288,64,1583⟩,280399708160,197963022⟩, ⟨⟨635,882,186,10829⟩,7570694078464,16399828679⟩⟩,
     ⟨32, ⟨⟨214,296,65,3070⟩,302242856960,218719650⟩, ⟨⟨616,856,174,19492⟩,6723698688000,14142442253⟩⟩,
     ⟨54, ⟨⟨377,521,117,3314⟩,1663607242752,2110154682⟩, ⟨⟨1182,1642,341,21429⟩,48093513646080,193780511162⟩⟩,
     ⟨81, ⟨⟨563,779,173,4477⟩,5476835655680,10401501082⟩, ⟨⟨1729,2402,504,30293⟩,0x89d0bdc40000,893089263594⟩⟩]
  | .h3000 =>
    [⟨0, ⟨⟨57,79,17,377⟩,5981601792,1179228⟩, ⟨⟨190,264,55,2518⟩,204603392000,133373011⟩⟩,
     ⟨1, ⟨⟨63,87,19,428⟩,8079278080,1737013⟩, ⟨⟨210,291,61,2846⟩,276307902464,197239731⟩⟩,
     ⟨2, ⟨⟨70,97,21,474⟩,10960502784,2641452⟩, ⟨⟨233,323,68,3163⟩,377887129600,299518730⟩⟩,
     ⟨4, ⟨⟨82,113,25,577⟩,17656184832,4885777⟩, ⟨⟨263,365,76,3803⟩,538134446080,482812069⟩⟩,
     ⟨5, ⟨⟨86,119,26,642⟩,20190855168,5931589⟩, ⟨⟨267,371,79,4248⟩,573046784000,524154366⟩⟩,
     ⟨6, ⟨⟨92,127,28,695⟩,24752685056,7713813⟩, ⟨⟨311,432,91,4432⟩,895738707968,952519333⟩⟩,
     ⟨10, ⟨⟨117,162,36,889⟩,50775982080,20261980⟩, ⟨⟨360,500,105,5872⟩,1383041597440,1700679003⟩⟩,
     ⟨16, ⟨⟨152,210,47,1214⟩,110731722752,56864480⟩, ⟨⟨477,662,139,7848⟩,3204474470400,5203785784⟩⟩,
     ⟨18, ⟨⟨146,202,44,1686⟩,96396902400,47762018⟩, ⟨⟨416,578,117,10980⟩,2071969136640,2944634929⟩⟩,
     ⟨24, ⟨⟨208,288,64,1554⟩,280399708160,197963022⟩, ⟨⟨635,882,186,10459⟩,7570694078464,16399828679⟩⟩,
     ⟨32, ⟨⟨214,296,65,2969⟩,302242856960,218719650⟩, ⟨⟨616,856,174,18265⟩,6723698688000,14142442253⟩⟩,
     ⟨54, ⟨⟨377,521,117,3252⟩,1663607242752,2110154682⟩, ⟨⟨1182,1642,341,20670⟩,48093513646080,193780511162⟩⟩,
     ⟨81, ⟨⟨563,779,173,4403⟩,5476835655680,10401501082⟩, ⟨⟨1729,2402,504,29273⟩,0x89d0bdc40000,893089263594⟩⟩]
  | .h3050 =>
    [⟨0, ⟨⟨57,79,17,357⟩,5981601792,1179228⟩, ⟨⟨190,264,55,2334⟩,204603392000,133373011⟩⟩,
     ⟨1, ⟨⟨63,87,19,404⟩,8079278080,1737013⟩, ⟨⟨210,291,61,2637⟩,276307902464,197239731⟩⟩,
     ⟨2, ⟨⟨70,97,21,450⟩,10960502784,2641452⟩, ⟨⟨233,323,68,2935⟩,377887129600,299518730⟩⟩,
     ⟨4, ⟨⟨82,113,25,548⟩,17656184832,4885777⟩, ⟨⟨263,365,76,3517⟩,538134446080,482812069⟩⟩,
     ⟨5, ⟨⟨86,119,26,608⟩,20190855168,5931589⟩, ⟨⟨267,371,79,3902⟩,573046784000,524154366⟩⟩,
     ⟨6, ⟨⟨92,127,28,658⟩,24752685056,7713813⟩, ⟨⟨311,432,91,4112⟩,895738707968,952519333⟩⟩,
     ⟨10, ⟨⟨117,162,36,846⟩,50775982080,20261980⟩, ⟨⟨360,500,105,5400⟩,1383041597440,1700679003⟩⟩,
     ⟨16, ⟨⟨152,210,47,1157⟩,110731722752,56864480⟩, ⟨⟨477,662,139,7228⟩,3204474470400,5203785784⟩⟩,
     ⟨18, ⟨⟨146,202,44,1572⟩,96396902400,47762018⟩, ⟨⟨416,578,117,9616⟩,2071969136640,2944634929⟩⟩,
     ⟨24, ⟨⟨208,288,64,1489⟩,280399708160,197963022⟩, ⟨⟨635,882,186,9651⟩,7570694078464,16399828679⟩⟩,
     ⟨32, ⟨⟨214,296,65,2748⟩,302242856960,218719650⟩, ⟨⟨616,856,174,15832⟩,6723698688000,14142442253⟩⟩,
     ⟨54, ⟨⟨377,521,117,3109⟩,1663607242752,2110154682⟩, ⟨⟨1182,1642,341,19025⟩,48093513646080,193780511162⟩⟩,
     ⟨81, ⟨⟨563,779,173,4234⟩,5476835655680,10401501082⟩, ⟨⟨1729,2402,504,27049⟩,0x89d0bdc40000,893089263594⟩⟩]
  | .h3100 =>
    [⟨0, ⟨⟨44,61,13,458⟩,2798387200,428950⟩, ⟨⟨137,191,38,2364⟩,75017486336,35709156⟩⟩,
     ⟨1, ⟨⟨47,65,14,600⟩,3407872000,552788⟩, ⟨⟨153,213,43,2663⟩,105135472640,55592342⟩⟩,
     ⟨2, ⟨⟨52,72,16,680⟩,4679270400,841239⟩, ⟨⟨171,238,48,2968⟩,146151047168,86226612⟩⟩,
     ⟨4, ⟨⟨63,87,19,808⟩,8079278080,1737013⟩, ⟨⟨208,290,58,3589⟩,260378460160,187629114⟩⟩,
     ⟨5, ⟨⟨70,97,21,809⟩,10960502784,2641452⟩, ⟨⟨239,333,67,3743⟩,395393892352,326459980⟩⟩,
     ⟨6, ⟨⟨76,105,23,856⟩,14043578368,3635193⟩, ⟨⟨254,354,72,4036⟩,478049206272,419800747⟩⟩,
     ⟨10, ⟨⟨99,137,30,1063⟩,30636769280,10343855⟩, ⟨⟨340,473,96,5131⟩,1137596432384,1327710081⟩⟩,
     ⟨16, ⟨⟨137,190,42,1292⟩,80832888832,37902732⟩, ⟨⟨443,617,127,6896⟩,2537151266816,3870016120⟩⟩,
     ⟨18, ⟨⟨131,181,39,2181⟩,69258444800,30680913⟩, ⟨⟨393,547,109,9578⟩,1729602519040,2335147916⟩⟩,
     ⟨24, ⟨⟨269,373,84,1280⟩,610154577920,559058208⟩, ⟨⟨738,1028,211,8858⟩,0xa9980180000,29591361675⟩⟩,
     ⟨32, ⟨⟨239,331,74,1974⟩,426141286400,345715284⟩, ⟨⟨772,1075,216,11547⟩,0xbee14380000,34787713530⟩⟩,
     ⟨54, ⟨⟨360,499,110,3229⟩,1432542248960,1751700680⟩, ⟨⟨1200,1672,344,17590⟩,50076691988480,206796824881⟩⟩]
  | .h3200 =>
    [⟨0, ⟨⟨44,61,13,386⟩,2798387200,428950⟩, ⟨⟨137,191,38,1959⟩,75017486336,35709156⟩⟩,
     ⟨1, ⟨⟨47,65,14,490⟩,3407872000,552788⟩, ⟨⟨153,213,43,2215⟩,105135472640,55592342⟩⟩,
     ⟨2, ⟨⟨52,72,16,557⟩,4679270400,841239⟩, ⟨⟨171,238,48,2480⟩,146151047168,86226612⟩⟩,
     ⟨4, ⟨⟨63,87,19,674⟩,8079278080,1737013⟩, ⟨⟨208,290,58,3020⟩,260378460160,187629114⟩⟩,
     ⟨5, ⟨⟨70,97,21,692⟩,10960502784,2641452⟩, ⟨⟨239,333,67,3208⟩,395393892352,326459980⟩⟩,
     ⟨6, ⟨⟨76,105,23,737⟩,14043578368,3635193⟩, ⟨⟨254,354,72,3460⟩,478049206272,419800747⟩⟩,
     ⟨10, ⟨⟨99,137,30,933⟩,30636769280,10343855⟩, ⟨⟨340,473,96,4452⟩,1137596432384,1327710081⟩⟩,
     ⟨16, ⟨⟨137,190,42,1162⟩,80832888832,37902732⟩, ⟨⟨443,617,127,5989⟩,2537151266816,3870016120⟩⟩,
     ⟨18, ⟨⟨131,181,39,1818⟩,69258444800,30680913⟩, ⟨⟨393,547,109,7693⟩,1729602519040,2335147916⟩⟩,
     ⟨24, ⟨⟨269,373,84,1220⟩,610154577920,559058208⟩, ⟨⟨738,1028,211,7963⟩,0xa9980180000,29591361675⟩⟩,
     ⟨32, ⟨⟨239,331,74,1817⟩,426141286400,345715284⟩, ⟨⟨772,1075,216,10113⟩,0xbee14380000,34787713530⟩⟩,
     ⟨54, ⟨⟨360,499,110,2967⟩,1432542248960,1751700680⟩, ⟨⟨1200,1672,344,15514⟩,50076691988480,206796824881⟩⟩]
  | .h3400 =>
    [⟨0, ⟨⟨44,61,13,299⟩,2798387200,428950⟩, ⟨⟨137,191,38,1493⟩,75017486336,35709156⟩⟩,
     ⟨1, ⟨⟨47,65,14,368⟩,3407872000,552788⟩, ⟨⟨153,213,43,1695⟩,105135472640,55592342⟩⟩,
     ⟨2, ⟨⟨52,72,16,419⟩,4679270400,841239⟩, ⟨⟨171,238,48,1908⟩,146151047168,86226612⟩⟩,
     ⟨4, ⟨⟨63,87,19,518⟩,8079278080,1737013⟩, ⟨⟨208,290,58,2342⟩,260378460160,187629114⟩⟩,
     ⟨5, ⟨⟨70,97,21,547⟩,10960502784,2641452⟩, ⟨⟨239,333,67,2544⟩,395393892352,326459980⟩⟩,
     ⟨6, ⟨⟨76,105,23,588⟩,14043578368,3635193⟩, ⟨⟨254,354,72,2745⟩,478049206272,419800747⟩⟩,
     ⟨10, ⟨⟨99,137,30,762⟩,30636769280,10343855⟩, ⟨⟨340,473,96,3586⟩,1137596432384,1327710081⟩⟩,
     ⟨16, ⟨⟨137,190,42,983⟩,80832888832,37902732⟩, ⟨⟨443,617,127,4830⟩,2537151266816,3870016120⟩⟩,
     ⟨18, ⟨⟨131,181,39,1395⟩,69258444800,30680913⟩, ⟨⟨393,547,109,5661⟩,1729602519040,2335147916⟩⟩,
     ⟨24, ⟨⟨269,373,84,1124⟩,610154577920,559058208⟩, ⟨⟨738,1028,211,6723⟩,0xa9980180000,29591361675⟩⟩,
     ⟨32, ⟨⟨239,331,74,1586⟩,426141286400,345715284⟩, ⟨⟨772,1075,216,8246⟩,0xbee14380000,34787713530⟩⟩,
     ⟨54, ⟨⟨360,499,110,2585⟩,1432542248960,1751700680⟩, ⟨⟨1200,1672,344,12766⟩,50076691988480,206796824881⟩⟩]
  | .h3555 =>
    [⟨0, ⟨⟨50,69,15,245⟩,4099932160,701658⟩, ⟨⟨122,169,35,1268⟩,54567370752,22700544⟩⟩,
     ⟨1, ⟨⟨56,77,17,282⟩,5752750080,1087341⟩, ⟨⟨141,196,41,1459⟩,84641579008,41100650⟩⟩,
     ⟨2, ⟨⟨58,80,17,333⟩,6215172096,1227093⟩, ⟨⟨148,205,42,1653⟩,95960170496,48317762⟩⟩,
     ⟨4, ⟨⟨73,101,22,396⟩,12438470656,3108650⟩, ⟨⟨189,262,55,2030⟩,202217881600,130167655⟩⟩,
     ⟨5, ⟨⟨78,108,23,442⟩,14874050560,3975609⟩, ⟨⟨203,282,58,2204⟩,246690611200,171576630⟩⟩,
     ⟨6, ⟨⟨84,116,26,472⟩,19164561408,5468512⟩, ⟨⟨208,289,59,2419⟩,263771914240,188037891⟩⟩,
     ⟨10, ⟨⟨106,147,32,636⟩,37385666560,13594640⟩, ⟨⟨267,371,79,3259⟩,573046784000,524154366⟩⟩,
     ⟨16, ⟨⟨141,195,44,861⟩,89201049600,42666368⟩, ⟨⟨360,500,105,4380⟩,1383041597440,1700679003⟩⟩,
     ⟨18, ⟨⟨124,171,38,1354⟩,60131901440,25087376⟩, ⟨⟨282,392,79,7399⟩,647128678400,625249766⟩⟩,
     ⟨32, ⟨⟨239,330,74,1462⟩,426141286400,342375034⟩, ⟨⟨582,808,165,7614⟩,5689291046912,11274483946⟩⟩]
  | .h4000 =>
    [⟨0, ⟨⟨37,51,11,205⟩,1703936000,216872⟩, ⟨⟨101,140,28,866⟩,30431510528,10519447⟩⟩,
     ⟨1, ⟨⟨44,61,13,236⟩,2798387200,428950⟩, ⟨⟨111,154,30,1016⟩,39462109184,15012021⟩⟩,
     ⟨2, ⟨⟨50,69,15,269⟩,4099932160,701658⟩, ⟨⟨128,178,36,1151⟩,61978705920,27365980⟩⟩,
     ⟨4, ⟨⟨61,84,18,344⟩,7237009408,1493513⟩, ⟨⟨171,238,48,1445⟩,146151047168,86226612⟩⟩,
     ⟨5, ⟨⟨67,93,20,374⟩,9604431872,2228964⟩, ⟨⟨172,239,48,1586⟩,148052115456,87388892⟩⟩,
     ⟨6, ⟨⟨67,93,20,439⟩,9604431872,2228964⟩, ⟨⟨180,250,50,1740⟩,168877096960,104120721⟩⟩,
     ⟨10, ⟨⟨96,133,30,536⟩,28613279744,9411251⟩, ⟨⟨253,352,70,2311⟩,463835234304,403341966⟩⟩,
     ⟨18, ⟨⟨138,191,43,824⟩,83595100160,39238708⟩, ⟨⟨352,490,98,3492⟩,1248242958336,1510758854⟩⟩,
     ⟨32, ⟨⟨203,281,63,1405⟩,262479544320,180754880⟩, ⟨⟨550,766,155,5530⟩,4781960069120,9047270849⟩⟩]
  | .h4800 =>
    [⟨0, ⟨⟨24,33,7,180⟩,489684992,40841⟩, ⟨⟨50,70,13,596⟩,3701211136,661273⟩⟩,
     ⟨2, ⟨⟨34,47,10,248⟩,1326448640,156979⟩, ⟨⟨74,103,20,807⟩,11955077120,3080759⟩⟩,
     ⟨5, ⟨⟨50,69,15,336⟩,4099932160,701658⟩, ⟨⟨111,155,30,1125⟩,39462109184,15324191⟩⟩,
     ⟨10, ⟨⟨70,97,21,559⟩,10960502784,2641452⟩, ⟨⟨155,216,41,1811⟩,104371585024,56031580⟩⟩,
     ⟨18, ⟨⟨118,163,37,719⟩,52800782336,21096205⟩, ⟨⟨267,372,72,2545⟩,534023503872,491959495⟩⟩,
     ⟨32, ⟨⟨182,252,55,1226⟩,185930350592,114923195⟩, ⟨⟨440,613,121,4035⟩,2408228061184,3649568203⟩⟩]
  | .h7745 =>
    [⟨0, ⟨⟨11,15,3,131⟩,55574528,2194⟩, ⟨⟨20,28,4,267⟩,230686720,17031⟩⟩,
     ⟨2, ⟨⟨21,29,6,154⟩,332136448,24733⟩, ⟨⟨38,53,9,387⟩,1568931840,211909⟩⟩,
     ⟨5, ⟨⟨34,47,10,235⟩,1326448640,156979⟩, ⟨⟨64,89,15,603⟩,7035944960,1564938⟩⟩,
     ⟨10, ⟨⟨54,75,16,386⟩,5084807168,957077⟩, ⟨⟨101,141,24,1013⟩,27099136000,9562298⟩⟩]
  | .h8000 =>
    [⟨0, ⟨⟨11,15,3,109⟩,55574528,2194⟩, ⟨⟨20,28,4,231⟩,230686720,17031⟩⟩,
     ⟨2, ⟨⟨21,29,6,143⟩,332136448,24733⟩, ⟨⟨38,53,9,357⟩,1568931840,211909⟩⟩,
     ⟨5, ⟨⟨34,47,10,222⟩,1326448640,156979⟩, ⟨⟨64,89,15,567⟩,7035944960,1564938⟩⟩,
     ⟨10, ⟨⟨54,75,16,368⟩,5084807168,957077⟩, ⟨⟨101,141,24,956⟩,27099136000,9562298⟩⟩]
  | .h14500 =>
    [⟨0, ⟨⟨6,8,1,46⟩,9699328,212⟩, ⟨⟨8,11,1,82⟩,17039360,517⟩⟩]
  | .h21448 =>
    [⟨0, ⟨⟨6,8,1,22⟩,9699328,212⟩, ⟨⟨8,11,1,38⟩,17039360,517⟩⟩]
  | .h24000 =>
    [⟨0, ⟨⟨6,8,1,20⟩,9699328,212⟩, ⟨⟨8,11,1,34⟩,17039360,517⟩⟩]
  | .h28300 =>
    [⟨0, ⟨⟨6,8,1,18⟩,9699328,212⟩, ⟨⟨8,11,1,30⟩,17039360,517⟩⟩]
  | .h32411 =>
    [⟨0, ⟨⟨4,5,1,14⟩,4456448,60⟩, ⟨⟨5,7,1,26⟩,6815744,147⟩⟩]
end P2_7
end
section
namespace P2_7
open P2 (K HighBand)
structure PrefixFees where
  loss : ℕ
  point : ℕ
  lowSeed : ℕ
  lowJet : ℕ
  fixedODE : ℕ
  content : ℕ
def fees : HighBand → PrefixFees
  | .h2366 => ⟨0xe6b3eaec27b59e,116861997479,876521492288411,0x56be1fb3444b08,36093253508147,0xa1fdd7428d118⟩
  | .h2380 => ⟨0xd7da5bf8c88f0f,120121004910,829961295151253,0x4de879ce710c0c,38156335697557,0xc1c5cf330d31a⟩
  | .h2400 => ⟨0xc6b4a89f175fc7,109202204960,799694610111234,0x485e6ef27fade1,38162053248458,0xaaaba8a2b00ec⟩
  | .h2420 => ⟨0xbc7c9b9657031f,104699174824,770778792970012,0x433817ba838782,38167770799362,0xa15a01828a7d0⟩
  | .h2440 => ⟨0xa5ba4c54fdb8f8,97123092498,722456501538907,0x3b18e334b1c1cb,38170629574814,0x8e58a8d23dde6⟩
  | .h2450 => ⟨0x9cb474b0b21856,93759998288,701000287653402,0x37a9848876641b,38173488350263,0x879f6e6222c34⟩
  | .h2460 => ⟨0x94bd4cafbb617f,90729212514,681214547626267,0x34959ba46895ec,38179205901170,0x81f63f920bf0e⟩
  | .h2480 => ⟨0x87404a1f4947c2,85195986838,645116119073289,0x2f308330a8a181,38184923452070,0x78ccafa1e700c⟩
  | .h2500 => ⟨0x758eb498217dff,83000086975,662025405704944,0x31c479e61e3971,0xf2c595875ec,0x47b26231210ba⟩
  | .h2520 => ⟨0x5e4b20e28b35c9,69011616860,669088697639264,0x317453bda290fd,20449002605676,0x5a87db516cf96⟩
  | .h2530 => ⟨0x5983f69b1fa65f,66032709527,644707023796535,0x2df5a9db6692cd,20450533209213,0x57533981600d0⟩
  | .h2540 => ⟨0x558b7831bf250a,63238370539,621976647446251,0x2ad19314510d11,20452063812747,0x5476965154836⟩
  | .h2550 => ⟨0x51f9a34669c6b7,60755120886,601353539775450,0x280f3de3a3e9b1,20453594416286,0x51e2f7f14a202⟩
  | .h2560 => ⟨0x4e84c65cce1f0e,58467108221,582209142378665,0x2594081cdb76ce,20455125019829,0x4f8cfd5140b56⟩
  | .h2570 => ⟨0x4b9e28b8080ee5,56373526110,564581807971278,9954786551412656,20457420925133,0x4d6b98b1381ea⟩
  | .h2585 => ⟨0x472aaf21fc6be2,53546576365,540325845824095,9125660097229378,20458186226900,0x4a8ce1b12c8ca⟩
  | .h2590 => ⟨0x45d57c0c17186e,52658248135,532742661592927,8874696388329827,20459716830439,0x49ab408128ff0⟩
  | .h2600 => ⟨0x439cbe4dc4f079,50970254110,518285818376782,8404625238494599,20459869890795,0x4801aa61224b4⟩
  | .h2601 => ⟨0x3b853ec4c81753,40999001950,509967540456296,8290466690667268,0xa412293d4cb,0x3a9ab650ec436⟩
  | .h2611 => ⟨0x39728e0660aa1c,39735374243,496535567039145,7860731024967260,0xa4154d94007,0x38ec2a30e57ba⟩
  | .h2621 => ⟨0x379a1a2f6154c2,38629285775,484531166942327,7486267955628802,0xa41b45d2563,974868506867322⟩
  | .h2640 => ⟨0x34fe7b6ef44fd9,36645832014,463064299533725,6840117752241147,0xa424b2d6711,931142149428774⟩
  | .h2670 => ⟨0x2ffea917c48294,33932729865,433219494399691,5988634705221924,0xa42e1fda8c4,875181275646198⟩
  | .h2700 => ⟨0x2c32fc093909bf,31629138521,407570050254289,5302914379007106,0xa43dd58c0f0,830440701945066⟩
  | .h2750 => ⟨0x275e48b17d4d87,28528772410,372306858653812,0xfb9c1fc0456d9,0xa44d8b3d91a,772383213031434⟩
  | .h2800 => ⟨0x2538de09cc6080,28080568800,355171717494870,0xe8fe110b23201,0xdbd1bc63251,637861062320844⟩
  | .h2900 => ⟨8211310618036248,21985174892,311688260461006,0xb1f1c7bb415a3,0xdd8f62edb28,552858659842848⟩
  | .h2950 => ⟨5779605417970943,12314607552,0xee2be809b958,0x7df0528da7cac,6697446031395,513713321237400⟩
  | .h2980 => ⟨5436736669042317,11736765360,0xe4b3000919da,0x74359e988b66f,6698445270597,492892057964352⟩
  | .h3000 => ⟨5241607407812057,11402680968,0xdf16cf08c0fd,0x6ea462987d7fa,6700943368600,480723593519778⟩
  | .h3050 => ⟨4808048251602143,10648967184,0xd25a7b07fa7c,0x62768f8ab1e4c,6703441466602,454901562246132⟩
  | .h3100 => ⟨0xc7502b3d30722,7490920973,0xd2908e0a77a5,0x625b531ead610,3531207081657,309090928848210⟩
  | .h3200 => ⟨0xa5cb1b9af72be,6025297867,0xb0511707dd41,0x44ff90ff37330,3536466905213,282086355503694⟩
  | .h3400 => ⟨0x82cdf0c1351dd,4421538731,0x882efd053a65,724019902369272,3540543268468,0xe1ed17038ed2⟩
  | .h3555 => ⟨0x4a422f35fa09b,1753633570,0x7be5c104169b,600049872150299,776330431965,0x7af82001efc0⟩
  | .h4000 => ⟨614847196277551,636562212,95856221147901,0xf56e7b7c9fc9,316305083107,76703300917566⟩
  | .h4800 => ⟨0xf647043590b5,289460748,68753635351992,74267057961282,170921398682,43014701489592⟩
  | .h7745 => ⟨690577758626885,16792623,0xede8701079c,7526287483595,9222203107,8782771920948⟩
  | .h8000 => ⟨623583651015993,12641632,0xca10b00c3ae,5699400605080,9653236886,8307624386166⟩
  | .h14500 => ⟨43982042210628,665546,2475880882196,124630598996,366856679,888504582978⟩
  | .h21448 => ⟨19521532348308,168462,1163365714284,27841155795,212139586,568898617878⟩
  | .h24000 => ⟨18370950873948,147204,0xf414000810,23193953813,218022042,556114379274⟩
  | .h28300 => ⟨0xfa96e003f24,126954,933249418956,18816293570,223645947,543330140670⟩
  | .h32411 => ⟨2627161033122,18700,485801067512,7907570234,14372295,202417111230⟩
structure PrefixBooks (b : HighBand) where
  loss : Finset K
  point : Finset K
  lowSeed : Finset K
  lowJet : Finset K
  fixedODE : Finset K
  content : Finset K
  loss_le : loss.card ≤ (fees b).loss
  point_le : point.card ≤ (fees b).point
  lowSeed_le : lowSeed.card ≤ (fees b).lowSeed
  lowJet_le : lowJet.card ≤ (fees b).lowJet
  fixedODE_le : fixedODE.card ≤ (fees b).fixedODE
  content_le : content.card ≤ (fees b).content
noncomputable def PrefixBooks.union {b} (B : PrefixBooks b) : Finset K := by
  classical exact B.loss ∪ B.point ∪ B.lowSeed ∪ B.lowJet ∪ B.fixedODE ∪ B.content
end P2_7
end
section
namespace P2_7
noncomputable section
open Polynomial
open P2 (HighBand AnchorModel AnchoredFamily K p node twist agreement)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum)
open K1_14_3 (Surface Parent)
open scoped BigOperators
abbrev GradeIndex (b : HighBand) := Fin (grades b).length
def Listed (b : HighBand) (t : Bank) : Prop :=
  t = terminal b ∨ (∃ s ∈ stages b, t = s.free ∨ t = s.moving) ∨
    ∃ i : GradeIndex b, t = subbank b ((grades b).get i)
def fullCutoff (s : Shape) := s.m * agreement - 1
def buffered (h r : ℕ) (s : Shape) := fullCutoff s - 2*h*r
def debit (h : ℕ) (t : Bank) :=
  triangle t.shape.U * t.nodeRows + 2*h*(t.shape.U+1)*t.poleMoment
def RankFloor (h : ℕ) (t : Bank) (rows : Banks) : Prop :=
  ∀ W < t.shape.m * agreement,
    (∀ q ≤ t.shape.B, ∀ j ≤ min q t.shape.J, q * (131071-h) ≤ W+1+j) →
    triangle t.shape.U * shapeSum t.shape (fun q j => W+1+j - q*(131071-h)) ≤
      debit h t + ∑ w ∈ Finset.range (W+1), Module.finrank FX (rows t.shape w)
structure Source (b : HighBand) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) (rows : Banks) : Prop where
  nested : ∀ t, Listed b t → ∀ t', Listed b t' →
    t.shape.m = t'.shape.m → t.shape.B = t'.shape.B → t.shape.J = t'.shape.J →
    t.shape.U ≤ t'.shape.U → ∀ W W', W ≤ W' → rows t.shape W ≤ rows t'.shape W'
  necessary : ∀ t, Listed b t → ∀ W < t.shape.m * agreement, ∀ P ∈ rows t.shape W,
    ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0
  shape : ∀ t, Listed b t → ∀ W, ∀ P ∈ rows t.shape W, K1_14_3.RowCaps P t.shape
  leading : ∀ t, Listed b t → K1_14_3.LeadingFilter M.overhead.toNat rows t.shape
  shift : ∀ t, Listed b t → K1_14_3.SeedShift M.overhead.toNat rows t.shape
  floor_bound : ∀ t, Listed b t → RankFloor M.overhead.toNat t rows
structure BufferedPair (h : ℕ) (rows : Banks) (s : Stage) where
  free : Jet
  moving : Jet
  free_ne : free ≠ 0
  moving_ne : moving ≠ 0
  free_mem : free ∈ rows s.free.shape (buffered h s.reserve s.free.shape)
  moving_mem : moving ∈ rows s.moving.shape (buffered h s.reserve s.moving.shape)
  no_moving : K1_14_3.NoMovingCommon free moving
abbrev Pairs (b : HighBand) (h : ℕ) (rows : Banks) :=
  ∀ s ∈ stages b, BufferedPair h rows s
def BankPass (rows : Banks) (s : Shape) (q : Surface) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), P ∈ q.asIdeal
def PairPass {h rows s} (pair : BufferedPair h rows s) (q : Surface) : Prop :=
  BankPass rows s.free.shape q ∧ BankPass rows s.moving.shape q ∧
    K1_14_3R.compatible pair.free pair.moving q
def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))
structure PrefixInventory (b : HighBand) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) {rows : Banks} (pairs : Pairs b M.overhead.toNat rows) where
  books : PrefixBooks b
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  stage_pass : ∀ q ∈ parents, ∀ s (hs : s ∈ stages b), 0 < s.reserve →
    PairPass (pairs s hs) q
  terminal_pass : ∀ q ∈ parents, BankPass rows (terminal b).shape q
  covers : ∀ γ ∈ Γ, γ ∈ books.union ∨ ∃ q ∈ parents, MarkOn M F q γ
def contactPower (h : ℕ) (s : Shape) (W : ℕ) := 1 + (fullCutoff s - W)/(2*h)
structure TerminalTrace (h : ℕ) (t : Bank) (rows : Banks) (f : Equation) : Prop where
  floor_bound : RankFloor h t rows
  shape : ∀ W, ∀ P ∈ rows t.shape W, K1_14_3.RowCaps P t.shape
  leading : K1_14_3.LeadingFilter h rows t.shape
  divides : ∀ W < t.shape.m * agreement, ∀ P ∈ rows t.shape W, P ≠ 0 →
    f ^ (contactPower h t.shape W - P.natDegree) ∣ P.leadingCoeff
end
end P2_7
end
section
namespace P2_7_2
open P2 (agreement)
open K1_14 (Shape triangle shapeSum)
def cutoffCount (h r : ℕ) (s : Shape) : ℕ :=
  s.m * agreement - 2 * h * r
def rawWidth (h r : ℕ) (s : Shape) (q j : ℕ) : ℕ :=
  cutoffCount h r s + j - q * (131071 - h)
def WidthGuard (h r : ℕ) (s : Shape) : Prop :=
  s.B * (131071 - h) < cutoffCount h r s
def gain (h r : ℕ) (s : Shape) (mode : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => rawWidth h r s q j - mode * (2 * h * j))
end P2_7_2
end
section
namespace P2_7_2_2
open Finset
open P2 (agreement)
open P2_7 (Bank Stage debit)
open P2_7_2 (cutoffCount rawWidth WidthGuard gain)
open K1_14 (Shape shapeSum triangle)
open private twice_sum_linear from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
private def row (x y z : ℤ) (q n : ℕ) : ℤ :=
  (n : ℤ) * (x + y*q + z*((n : ℤ)-1))
private def rising (x y z : ℤ) (n : ℕ) : ℤ :=
  (n : ℤ)*((n : ℤ)+1)*(3*x+2*(y+z)*((n : ℤ)-1))
private def level (x y z : ℤ) (J n : ℕ) : ℤ :=
  3*(n : ℤ)*((J : ℤ)+1)*(2*(x+(y+z)*J)+y*((n : ℤ)-1))
private theorem sum_rising (x y z : ℤ) (n : ℕ) :
    6*(∑ q ∈ range n, row x y z q (q+1)) = rising x y z n := by
  induction n with
  | zero => simp [rising]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    simp only [rising, row, Nat.cast_succ]
    ring
private theorem sum_level (x y z : ℤ) (J n : ℕ) :
    6*(∑ i ∈ range n, row x y z (J+i) (J+1)) = level x y z J n := by
  induction n with
  | zero => simp [level]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    simp only [level, row, Nat.cast_succ, Nat.cast_add]
    ring
private def tailSum (f : ℕ → ℤ) (k : ℕ) : ℕ → ℤ
  | 0 => 0
  | n+1 => tailSum f k n + f (k+n)
private theorem tailSum_eq (f : ℕ → ℤ) (k n : ℕ) :
    tailSum f k n = ∑ i ∈ range n, f (k+i) := by
  induction n with
  | zero => simp [tailSum]
  | succ n ih => rw [tailSum, sum_range_succ, ih]
end P2_7_2_2
end
