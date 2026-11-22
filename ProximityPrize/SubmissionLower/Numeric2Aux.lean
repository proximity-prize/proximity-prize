import ProximityPrize.SubmissionLower.Fast022
import ProximityPrize.SubmissionLower.PortFoundation
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ0
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem ProximityPrize.Benchmark
open Sol1.OneCount (A16 R16 scalarCode squaredCode flatten flatten_injective
  flatten_rows_mem flatten_agreement_le)
open Sol1.FiniteRowProjection
open scoped NNReal
theorem scalar_word_count {A cap} (hlist : ScalarList A cap) (w : Node → K) (P : Finset (Node → K))
    (hP : ∀ f ∈ P, f ∈ scalarCode ∧ A ≤ agreementCard f w) : P.card ≤ cap := by
  classical
  have : NeZero (k : ℕ) := ⟨by decide⟩
  choose poly hdegree heval using fun f : P ↦
    ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hP f.val f.property).1
  have hinj : Function.Injective poly := by
    intro f g hfg
    apply Subtype.ext
    funext i
    calc
      f.val i = (poly f).eval (IRSProfile.domain i) := (heval f i).symm
      _ = (poly g).eval (IRSProfile.domain i) := by rw [hfg]
      _ = g.val i := heval g i
  let polys : Finset K[X] := Finset.univ.image poly
  have hpolyscard : polys.card = P.card := by
    dsimp [polys]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hpolys : (polys : Set K[X]) ⊆
      close A w := by
    intro q hq
    obtain ⟨f,_hf,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨?_, ?_⟩
    · have hd : (poly f).natDegree < k := hdegree f
      exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast hd)
    · refine (hP f.val f.property).2.trans (Finset.card_le_card ?_)
      intro i hi
      apply (ReedSolomon.mem_polynomialAgreementSet node w (poly f) i).mpr
      have hfw : f.val i = w i := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
      exact (heval f i).trans hfw
  obtain ⟨hfinite,hbound⟩ := hlist w
  have hcount := (Set.ncard_le_ncard hpolys hfinite).trans hbound
  have hcount' : polys.card ≤ cap := by simpa only [Set.ncard_coe_finset] using hcount
  rwa [hpolyscard] at hcount'
theorem squared_word_count {A cap} (hlist : ScalarList A cap)
    (hroom : (cap+1)^2 ≤ Fintype.card K) (w : Node → A16) (P : Finset (Node → A16))
    (hP : ∀ f ∈ P, f ∈ squaredCode ∧ A ≤ agreementCard f w) : P.card ≤ cap := by
  classical
  let flattened := P.image flatten
  have hflat : ∀ f ∈ flattened,
      (∀ r : R16, (fun i ↦ f i r) ∈ scalarCode) ∧
        A ≤ agreementCard f (flatten w) := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hcode,hagree⟩ := hP g hg
    exact ⟨flatten_rows_mem g hcode,hagree.trans (flatten_agreement_le g w)⟩
  have hcount := finset_vector_list_card_le scalarCode A cap hroom
    (scalar_word_count hlist) (flatten w) flattened hflat
  have hcard : flattened.card = P.card := Finset.card_image_of_injective P flatten_injective
  rwa [hcard] at hcount
theorem squared_lambda_le {A cap} (hlist : ScalarList A cap)
    (hroom : (cap+1)^2 ≤ Fintype.card K) (radius : ℝ)
    (hcut : ∀ f w : Node → A16, (δᵣ(w,f) : ℝ) ≤ radius → A ≤ agreementCard f w) :
    Code.Lambda (squaredCode : Set (Node → A16)) radius ≤ (cap : ℕ∞) := by
  classical
  apply Code.Lambda_le_iff_forall_encard_le.mpr
  intro w
  have hfinite : (Code.closeCodewordsRel (squaredCode : Set (Node → A16)) w radius).Finite :=
    Set.toFinite _
  have hcard : hfinite.toFinset.card ≤ cap := by
    apply squared_word_count hlist hroom w hfinite.toFinset
    intro f hf
    obtain ⟨hcode,hclose⟩ := Code.mem_closeCodewordsRel_iff.mp (hfinite.mem_toFinset.mp hf)
    exact ⟨hcode,hcut f w hclose⟩
  calc
    (Code.closeCodewordsRel (squaredCode : Set (Node → A16)) w radius).encard =
        (hfinite.toFinset.card : ℕ∞) := hfinite.encard_eq_coe_toFinset_card
    _ ≤ (cap : ℕ∞) := by exact_mod_cast hcard
theorem anchored_list_count {cap} (hlist : ScalarList P0.agreement cap) {u deleted} (M : P0.AnchorModel u deleted)
    (Γ : Finset K) (F : P0.AnchoredFamily M Γ) (hw : M.overhead ≤ 0) :
    Γ.card ≤ cap := by
  classical
  obtain ⟨hfinite, hprice⟩ := hlist M.word
  have hsub : Γ.image F.scalar ⊆ hfinite.toFinset := by
    intro P hP
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hP
    have mark := F.mark γ hγ
    apply hfinite.mem_toFinset.mpr
    constructor
    · rcases mark.scalar_degree with hz | hd
      · rw [hz, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe k
      · have hn : (F.scalar γ).natDegree < P0.k := by omega
        exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hn)
    · apply mark.bad.agreement.trans
      apply Finset.card_le_card
      intro i hi
      simp only [ReedSolomon.polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact mark.scalar_hits i hi
  calc
    Γ.card = (Γ.image F.scalar).card := (Finset.card_image_of_injOn F.distinct).symm
    _ ≤ hfinite.toFinset.card := Finset.card_le_card hsub
    _ = _ := (Set.ncard_eq_toFinset_card _ hfinite).symm
    _ ≤ cap := hprice
end
end CJ0
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P1
noncomputable section
open Polynomial Matrix CoreDefinitions Code FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators NNReal
export P0 (K I Words node p blockLength k Frac Bivar TypeAtMostOne coefficientBlocks
  extendSeed IsCommonGCD atSlope seed liftX twist amplitudeDegree sixNorm columnRank
  threeU threeV sameDirection relationOn)
structure Rung where
  agreement : ℕ
  numerator : ℕ
  denominator : ℕ
  lowEnd : ℕ
  mcaBound : ℕ
  listBound : ℕ
abbrev target : Rung := ⟨179944,336691697,1073741824,2369,0x3aca17061ce8c43,8491707658716571⟩
abbrev agreement := target.agreement
abbrev radiusNumerator := target.numerator
abbrev radiusDenominator := target.denominator
abbrev lowCutoff : ℤ := target.lowEnd
abbrev scalarCap := target.mcaBound
abbrev listCap := target.listBound
abbrev t : ℕ := blockLength - agreement
abbrev L : ℕ := agreement - k
abbrev heightCap : ℕ := t + 1 - L - 2
abbrev rankFee : ℕ := 71010053341463
abbrev anchorFee : ℕ := 71010053621391
abbrev budget : ℕ := 0x3d0ed83eb28710f
def queryRadius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator
def radius : ℝ := queryRadius
def BadFamily (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius
structure BadMarkAt (A : ℕ) (u : Words) (γ : K) where
  support : Finset I
  decoder : K[X]
  agreement : A ≤ support.card
  degree : decoder.degree < k
  hits : ∀ i ∈ support, decoder.eval (node i) = u 0 i + γ * u 1 i
  nonjoint : ¬ (ExtendsOn node (u 0) k support ∧ ExtendsOn node (u 1) k support)
abbrev BadMark := BadMarkAt agreement
def ordinary (u : Words) := hankel node (u 0) (u 1) L t
def twoBlock (u : Words) := stacked p node (u 0) (u 1) L t
def firstRank (u : Words) := GenericLayer.genericRank (ordinary u)
def stackRank (u : Words) := GenericLayer.genericRank (twoBlock u)
def nullity (u : Words) := GenericLayer.genericNullity (twoBlock u)
def Normal (u : Words) (γ : K) : Prop :=
  ((twoBlock u).map (evalRingHom γ)).rank = stackRank u
def normalSlopes (u : Words) (Γ : Finset K) : Finset K := by
  classical exact Γ.filter (Normal u)
def abnormalSlopes (u : Words) (Γ : Finset K) : Finset K := by
  classical exact Γ.filter (fun γ => ¬ Normal u γ)
def HomogeneousPrincipal (u : Words) : Prop :=
  ∃ (a : ℕ) (g : Frac[X]), g ≠ 0 ∧ g.natDegree ≤ a ∧ a ≤ t ∧
    ∀ P : Frac[X], P.natDegree ≤ t →
      (((twoBlock u).map (algebraMap K[X] Frac)).mulVec (fun i => P.coeff i.val) = 0 ↔
        ∃ Q : Frac[X], Q.natDegree ≤ t - a ∧ P = g * Q)
abbrev coefficientStack (u : Words) := coefficientBlocks p node (u 0) (u 1) L t
def ConstantKernel (u : Words) : Prop :=
  stackRank u = (coefficientStack u).rank
def FrontRemainder (u : Words) : Prop :=
  2 ≤ nullity u ∧ firstRank u = L ∧ ¬ TypeAtMostOne u ∧
    ¬ HomogeneousPrincipal u ∧ ¬ ConstantKernel u
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
def FixedLeftGCD {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  ∃ G : K[X], IsCommonGCD (G.map (algebraMap K Frac))
    (extendSeed (leftU R)) (extendSeed (leftV R))
def MovingGCD {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  ¬ FixedLeftGCD R ∧ ∃ G : Frac[X], G ≠ 0 ∧ G ∣ extendSeed (leftU R) ∧
    G ∣ extendSeed (leftV R) ∧ (fixedNodes R).card < G.natDegree
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
def NormalSaturation {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  ∀ γ, Normal u γ → ∀ M : BadMark u γ, SaturatedAt R M
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
def Parallel {u T R D} (B : RankThree u T R D) : Prop :=
  B.α = B.β
def Nonparallel {u T R D} (B : RankThree u T R D) : Prop :=
  B.α 0 * B.β 1 - B.α 1 * B.β 0 ≠ 0
def UnitNorm {u T R D} (B : RankThree u T R D) : Prop :=
  sixNorm B.a = sixNorm B.b
structure ModelAt (maxHeight : ℕ) (u : Words) (deleted : Finset I) where
  shift : K
  pencil₀ : K[X]
  pencil₁ : K[X]
  pencil₀_degree : pencil₀.degree < k
  pencil₁_degree : pencil₁.degree < k
  E : K[X]
  factor : K[X]
  Q : K[X]
  A₀ : K[X]
  A₁ : K[X]
  word : I → K
  word_fixed : ∀ i, twist (word i) = word i
  word_deleted : ∀ i ∈ deleted, word i = 0
  E_monic : E.Monic
  E_nodes : ∀ i, E.eval (node i) ≠ 0
  factor_nodes : ∀ i ∉ deleted, factor.eval (node i) ≠ 0
  coprime_factor : IsCoprime E factor
  offset_proper : Q.degree < E.degree
  offset_reduced : IsCoprime Q E
  adjacent_coprime : IsCoprime E (E.map twist)
  amplitudes_primitive : IsCoprime A₀ A₁
  first_amplitude_unit : IsCoprime A₀ E
  height_bound : E.natDegree + amplitudeDegree A₀ A₁ ≤ maxHeight
  first_word : ∀ i ∉ deleted,
    E.eval (node i) * (u 0 i + shift * u 1 i - pencil₀.eval (node i)) =
      factor.eval (node i) * A₀.eval (node i) * word i
  second_word : ∀ i ∉ deleted,
    E.eval (node i) * (u 1 i - pencil₁.eval (node i)) =
      Q.eval (node i) + factor.eval (node i) * A₁.eval (node i) * word i
def ModelAt.overhead {h u deleted} (M : ModelAt h u deleted) : ℤ :=
  (M.E.natDegree : ℤ) - M.factor.natDegree - amplitudeDegree M.A₀ M.A₁
def ModelAt.label {h u deleted} (M : ModelAt h u deleted) (γ : K) : K :=
  γ - M.shift
def ModelAt.amplitude {h u deleted} (M : ModelAt h u deleted) (γ : K) : K[X] :=
  M.A₀ + Polynomial.C (M.label γ) * M.A₁
def ModelAt.decoder {h u deleted} (M : ModelAt h u deleted) {A : ℕ} {γ : K}
    (B : BadMarkAt A u γ) : K[X] :=
  B.decoder - M.pencil₀ - Polynomial.C (M.label γ) * M.pencil₁
structure MarkAt {A h : ℕ} {u deleted} (M : ModelAt h u deleted) (γ : K) (S : K[X]) where
  bad : BadMarkAt A u γ
  avoids_deleted : Disjoint bad.support deleted
  scalar_fixed : S.map twist = S
  scalar_degree : S = 0 ∨ (S.natDegree : ℤ) ≤ (k : ℤ) - 1 + M.overhead
  scalar_hits : ∀ i ∈ bad.support, S.eval (node i) = M.word i
  pole_unit : IsCoprime (M.amplitude γ) M.E
  identity : M.E * M.decoder bad - Polynomial.C (M.label γ) * M.Q =
    M.factor * M.amplitude γ * S
structure FamilyAt (A : ℕ) {h : ℕ} {u deleted} (M : ModelAt h u deleted) (Γ : Finset K) where
  scalar : K → K[X]
  mark : ∀ γ ∈ Γ, MarkAt (A := A) M γ (scalar γ)
  distinct : Set.InjOn scalar (Γ : Set K)
abbrev AnchorModel := ModelAt heightCap
abbrev AnchorMark {u deleted} (M : AnchorModel u deleted) := MarkAt (A := agreement) M
abbrev AnchoredFamily {u deleted} (M : AnchorModel u deleted) := FamilyAt agreement M
abbrev AnchorModel.overhead {u deleted} (M : AnchorModel u deleted) := ModelAt.overhead M
abbrev AnchorModel.label {u deleted} (M : AnchorModel u deleted) := ModelAt.label M
abbrev AnchorModel.amplitude {u deleted} (M : AnchorModel u deleted) := ModelAt.amplitude M
abbrev AnchorModel.decoder {u deleted} (M : AnchorModel u deleted) {γ : K} (B : BadMark u γ) :=
  ModelAt.decoder M B
structure HighRow where
  lo : ℕ
  hi : ℕ
  prefixFee : ℕ
  retained : ℕ
inductive HighBand where
  | h2370
  | h2390
  | h2410
  | h2420
  | h2440
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
  | h7773
  | h8000
  | h14500
  | h21473
  | h24000
  | h28323
  | h32433
def HighBand.row : HighBand → HighRow
  | .h2370 => ⟨2370,2389,80495530196751944,0x28e2603a4656e54⟩
  | .h2390 => ⟨2390,2409,0xf9469c19b9863c,0x21fe894e17f659f⟩
  | .h2410 => ⟨2410,2419,0xee922aa6fec352,0x1eff8184d4a712c⟩
  | .h2420 => ⟨2420,2439,0xd28aff6311d93c,0x1a52aa17a200c95⟩
  | .h2440 => ⟨2440,2459,0xbeb8e493d358e1,0x16440d31f9520f1⟩
  | .h2460 => ⟨2460,2479,0xadb5b5f73be6d7,88314402295386218⟩
  | .h2480 => ⟨2480,2499,0x98613c34a8f326,75580977671294650⟩
  | .h2500 => ⟨2500,2519,0x8847d91eac7fbf,0xe7d2adf917f50b⟩
  | .h2520 => ⟨2520,2529,0x7b4912a16ade38,0xc93bdc41198359⟩
  | .h2530 => ⟨2530,2539,0x75bb6a9f28f8fc,0xbe4d42573a1d57⟩
  | .h2540 => ⟨2540,2549,0x7065eff66bf144,0xb1980d09f47784⟩
  | .h2550 => ⟨2550,2559,0x6bfcd5ef169d7c,0xa7562d1ae58b34⟩
  | .h2560 => ⟨2560,2569,0x67b6e230093f68,0x9d62cb6f698f1f⟩
  | .h2570 => ⟨2570,2584,0x63dd572a4ca3e6,0x93bde56871940b⟩
  | .h2585 => ⟨2585,2589,0x5eb6d2250b1503,0x86c08e98cac21c⟩
  | .h2590 => ⟨2590,2599,0x5d1bb688d646a2,0x83265da321d05f⟩
  | .h2600 => ⟨2600,2600,0x5a06673904a74f,0x7a6d993286262d⟩
  | .h2601 => ⟨2601,2610,0x59b9e3dbbe7374,0x7a5c8387d06239⟩
  | .h2611 => ⟨2611,2620,0x56d2daf9e81b62,0x727d26c0359ab2⟩
  | .h2621 => ⟨2621,2639,0x546a03afc3ebfd,0x6dd9162595c015⟩
  | .h2640 => ⟨2640,2669,0x4ea52c8664f159,0x6366dbc040862e⟩
  | .h2670 => ⟨2670,2699,0x46e3fa6f4e6c0b,0x55627b039d421f⟩
  | .h2700 => ⟨2700,2749,0x407e41254c3346,0x49ae7b6f42cb70⟩
  | .h2750 => ⟨2750,2799,0x38389d07305818,0x39b81ba31578a8⟩
  | .h2800 => ⟨2800,2899,0x316a41e4b3309d,0x2e14919bf19ff8⟩
  | .h2900 => ⟨2900,2949,8872442622423809,9173807193376184⟩
  | .h2950 => ⟨2950,2979,7987270307117438,7610274941597429⟩
  | .h2980 => ⟨2980,2999,7538749239604091,6908034803302175⟩
  | .h3000 => ⟨3000,3049,7276823856763379,6569338538207742⟩
  | .h3050 => ⟨3050,3099,5747479670950418,5916768739855770⟩
  | .h3100 => ⟨3100,3199,5245621618597394,5004749729248126⟩
  | .h3200 => ⟨3200,3399,0xf8da1f5a11d37,0xd6d6924e7144a⟩
  | .h3400 => ⟨3400,3554,0x8e07cbdfe181c,0x99c8040f438ad⟩
  | .h3555 => ⟨3555,3999,0x75165f52b2eb6,0x716d568103f96⟩
  | .h4000 => ⟨4000,4799,0x450c90e105601,0x42206b4855593⟩
  | .h4800 => ⟨4800,7772,437785780857465,667070016592432⟩
  | .h7773 => ⟨7773,7999,698804344963922,0xfaad6c38dfe1⟩
  | .h8000 => ⟨8000,14499,640008163332508,0xfc080066b8fc⟩
  | .h14500 => ⟨14500,21472,46894316540129,0x7ed9806efa33⟩
  | .h21473 => ⟨21473,23999,21281848741227,74246611859481⟩
  | .h24000 => ⟨24000,28322,19998787150510,62656060897488⟩
  | .h28323 => ⟨28323,32432,18715990635494,51439696596499⟩
  | .h32433 => ⟨32433,33327,3323299909641,56675196335681⟩
end
end P1
end
section
namespace P1
theorem high_with_reserve (b : HighBand) :
    b.row.prefixFee + b.row.retained + 1 + anchorFee + rankFee ≤ scalarCap := by
  cases b <;> decide
end P1
end
section
namespace CJ1
inductive Bank where
  | leftLow | rightLow | leftHigh | rightHigh
  deriving DecidableEq
def Bank.onRows : Bank → Bool
  | .leftLow | .leftHigh => true
  | .rightLow | .rightHigh => false
structure Block where
  bank : Bank
  cap : Nat
  free : List (Nat × Nat)
  vectors : List (List (List Nat))
def Block.coeff (z : Block) (j i k : Nat) : Nat := (((z.vectors[j]?).getD [])[i]?.getD [])[k]?.getD 0
def block31u15 : Block where
  bank := .leftLow
  cap := 89
  free := [(8,1)]
  vectors := [
    [[1014622111,1724857590,710235497,174,1131,5655,22620,1217620856,1217750921,476905,953810,1647490,2471235,3231615,1830013074,1830013074,3231615,2471235], [1014622111,710235479,18,156,975,4680,17940,1217602916,148005,328900,624910,1022580,1448655,1782960,1828230114,1782960], [1014622111,1826319801,304386650,1826319939,304387469,1826323644,304400729,913202187,1217652251,913383082,1217948261,913780752,1218374336,914115057], [1014622111,811697690,1623395393,202924546,101462923,1724860721,710246441,202955746,1014696505,2029393010,1319261684,1725225501], [1014622111,1927782012,1826319814,507311165,1724858191,2530,710243911,1623418268,1521984670,507408340], [1014622111,913159901,913159913,1724857685,506,2024,710241887,913176381], [1014622111,2029244223,1014622123,710235562,1420471377,710237080], [1014622111,1014622112,11,710235551], [1014622111,1]]]
def block32u14 : Block where
  bank := .leftLow
  cap := 88
  free := [(8,0),(8,1)]
  vectors := [
    [[2130706346,2130703977,2130672735,2130406805,2128764332,2120921021,2090804753,1995393593,1741682018,1169265953,67615403,390158206,8919294,1376135785,878968938,1419720791,1410025946,872125518], [2130706357,2130704361,2130678965,2130470309,2129225681,2123482853,2102172473,2036951993,1869625613,1506322673,836353373,1920727246,553537786,1234461759,85789779,1745794772], [2130706368,2130704723,2130684536,2130524381,2129600783,2125476533,2110658483,2066768273,1957984598,1730599583,1329259358,734884733,9875513,1445227546], [2130706379,2130705063,2130689481,2130569933,2129901733,2127004813,2116892633,2087817873,2018058183,1877617883,1640776993,1309801933], [2130706390,2130705381,2130693833,2130607833,2130139483,2128156193,2121390973,2102421033,2058240908,1972556133], [2130706401,2130705677,2130697625,2130638905,2130323897,2129006273,2124571689,2112362921], [2130706412,2130705951,2130700890,2130663929,2130463806,2129619039], [2130706423,2130706203,2130703661,2130683641], [1,0]],
    [[4,113,1065354768,13804,89523,451269,1067193919,6243120,17948970,44352165,1160495764,178449180,294076965,427143465,1613111959,620470080,620470080,546903315], [1065353220,1065353312,1267,10899,1065421603,1065686959,1318590,4332510,1077415624,1094189524,59744685,107967405,1236251899,1302876919,290176740,311572260], [3,79,1065354229,8424,1065404404,242190,928395,2960100,7992270,18500625,1102379134,64422540,1163137429,129710340], [1065353219,1065353280,1065354003,1065359554,37375,171925,641355,1989845,1070574504,1077070279,1088006204,1103259689], [2,49,1065353804,4600,26450,118910,433895,1315600,3364900,7330675], [1065353218,1065353252,414,3174,17963,79695,286902,855646], [1,23,1065353481,2024,1065364728,51359], [1065353217,1065353228,1065353354,1065354333], [0,1]]]
def block33u13 : Block where
  bank := .rightLow
  cap := 86
  free := [(15,0),(16,0),(17,0),(18,0)]
  vectors := [
    [[0,0,1,3,3,1], [0,0,5,10,3,2130706429,2130706431], [0,10,0,2130706398,2130706401,2130706427,1], [0,10,2130706393,2130706358,0,38,12], [5,2130706368,15,175,105,3,2130706428], [1,2130706391,163,176,2130706328,2130706307,2130706408], [2130706423,153,2130706269,2130706041,2130706328,35,10], [45,2130706121,2130706377,336,175,20], [2130706313,378,322,2130706363,2130706358,2130706423], [210,2130706181,2130706083,2130706353,0], [2130706181,42,172,54,5], [210,72,2130706407,2130706425], [2130706313,2130706370,2130706424,2130706432], [45,22,3], [2130706423,2130706430,0], [1,0], [0,0], [0], [0]],
    [[0,0,10,31,32,11], [0,0,50,106,38,2130706393,2130706411], [0,100,15,2130706083,2130706086,2130706361,11], [0,100,2130706053,2130705633,2130706363,388,136], [50,2130705798,40,1750,1190,73,2130706377], [10,2130706019,1522,1976,2130705593,2130705103,2130706135], [2130706334,1478,2130705118,2130702401,2130705033,294,115], [440,2130703511,2130705361,3136,1960,270], [2130705278,3348,3626,2130706153,2130705683,2130706313], [1980,2130704501,2130702877,2130705353,2130706383], [2130704123,2130706349,1538,604,65], [1848,972,2130706333,2130706365], [2130705443,2130705755,2130706290,2130706417], [330,202,34], [2130706378,2130706415,1], [0,2130706431], [1,0], [0], [0]],
    [[0,0,55,175,186,66], [0,0,275,610,252,2130706217,2130706301], [0,550,150,2130704529,2130704396,2130705965,66], [0,550,2130704433,2130701843,2130705663,2128,840], [275,2130703008,2130706193,9450,7210,693,2130706091], [55,2130704183,7906,11616,2130703073,2130698943,2130704501], [2130705893,7902,2130700502,2130684341,2130696983,1120,721], [2376,2130691191,2130698765,15456,11550,1954], [2130700273,16713,20790,840,2130702623,2130705648], [10395,2130697901,2130687701,2130699233,2130705758], [2130694553,2130704501,6954,3414,460], [9240,5724,366,2130706225], [2130701681,2130702950,2130705436,2130706297], [1485,862,170], [2130706213,2130706415,17], [0,2130706415], [0,2130706432], [1], [0]],
    [[0,0,220,715,780,286], [0,0,1100,2530,1170,2130705601,2130705861], [0,2200,825,2130698943,2130697866,2130704249,286], [0,2200,2130698733,2130687533,2130701939,8268,3744], [1100,2130692958,2130704033,36820,30870,4173,2130704925], [220,2130697523,30130,48416,2130697613,2130676823,2130697411], [2130704288,30870,2130686646,2130619521,2130663383,1610,3263], [9360,2130648071,2130671049,54936,46900,10070], [2130682409,61758,84154,10640,2130694133,2130702727], [40040,2130678101,2130635565,2130675393,2130701513], [2130661388,2130695261,22930,12264,2345], [34320,23148,3472,412], [2130689273,2130693545,2130702602,2130705617], [5148,2842,306], [2130705718,2130706415,153], [0,2130706415], [0,2130706415], [0], [1]]]
def block34u12 : Block where
  bank := .rightLow
  cap := 84
  free := [(16,0),(17,0),(18,0)]
  vectors := [
    [[0,0,0,1,2,1], [0,0,6,8,0,2130706431], [0,0,15,0,2130706406,2130706421,1], [0,20,2130706383,2130706363,8,16], [0,15,2130706323,0,140,43,2130706427], [6,2130706325,216,210,2130706363,2130706385], [1,2130706381,325,2130706321,2130706083,2130706377,15], [2130706423,198,2130705921,2130706209,210,70], [45,2130706001,406,420,0,2130706413], [2130706313,588,2130706377,2130706153,2130706383], [210,2130705929,2130706251,64,15], [2130706181,252,160,12], [210,2130706385,2130706380,2130706427], [2130706313,2130706415,4], [45,12,1], [2130706423,2130706431], [1,0], [0], [0]],
    [[0,0,0,10,21,11], [0,0,60,87,4,2130706411], [0,0,150,21,2130706156,2130706295,11], [0,200,2130705968,2130705663,38,180], [0,150,2130705368,2130706258,1435,528,2130706366], [60,2130705374,1936,2415,2130705873,2130705876], [10,2130705920,3089,2130705901,2130702758,2130705628,171], [2130706334,1918,2130701845,2130703409,1925,854], [440,2130702356,3080,4690,315,2130706198], [2130705278,5328,518,2130703633,2130705758], [1980,2130702191,2130703927,444,185], [2130704123,1764,1796,232], [1848,2130706415,2130705931,2130706352], [2130705443,2130706085,5], [330,147,17], [2130706378,2130706415], [0,2130706432], [1], [0]],
    [[0,0,0,55,120,66], [0,0,330,510,48,2130706301], [0,0,825,210,2130704906,2130705569,66], [0,1100,2130704033,2130701939,2130706341,1104], [0,825,2130700733,2130704753,7770,3513,2130706025], [330,2130700703,9696,14280,2130704543,2130702911], [55,2130703643,16293,2130705761,2130686483,2130700343,1063], [2130705893,10278,2130683369,2130687449,8400,5670], [2376,2130685031,13314,26040,4200,2130704927], [2130700273,27108,6132,2130692993,2130701513], [10395,2130686021,2130691523,384,1245], [2130694553,7308,9192,2172], [9240,972,2130704582,2130705837], [2130701681,2130704435,2130706079], [1485,642,153], [2130706213,2130706415], [0,2130706415], [0], [1]]]
def block34u13 : Block where
  bank := .leftLow
  cap := 80
  free := [(8,0)]
  vectors := [
    [[1,31,465,4495,31465,169911,736281,2629575,7888725,20160075,44352165,84672315,141120525,206253075,265182525,300540195,300540195], [1,30,435,4060,27405,142506,593775,2035800,5852925,14307150,30045015,54627300,86493225,119759850,145422675], [1,29,406,3654,23751,118755,475020,1560780,4292145,10015005,20030010,34597290,51895935], [1,28,378,3276,20475,98280,376740,1184040,3108105,6906900,13123110], [1,27,351,2925,17550,80730,296010,888030,2220075], [1,26,325,2600,14950,65780,230230], [1,25,300,2300,12650], [1,24,276], [1]]]
def block35u11 : Block where
  bank := .rightLow
  cap := 81
  free := [(17,0),(18,0)]
  vectors := [
    [[0,0,0,1,1], [0,0,0,7,4,2130706431], [0,0,21,2130706426,2130706415,1], [0,0,35,2130706363,2130706391,20], [0,35,2130706258,35,98,2130706426], [0,21,2130706209,315,140,2130706356], [7,2130706272,588,2130706258,2130706188,21], [1,2130706371,532,2130705649,2130706258,154], [2130706423,243,2130705453,490,315,2130706398], [45,2130705881,1078,0,2130706258], [2130706313,798,2130705747,2130706237,35], [210,2130705677,196,112], [2130706181,462,28,2130706412], [210,2130706265,2130706398], [2130706313,27,7], [45,2], [2130706423,2130706432], [1], [0]],
    [[0,0,0,10,11], [0,0,0,70,48,2130706411], [0,0,210,2130706391,2130706229,11], [0,0,350,2130705789,2130705901,224], [0,350,2130704753,70,1148,2130706355], [0,210,2130704249,2730,1960,2130705551], [70,2130704851,5488,2130705733,2130703423,238], [10,2130705821,5096,2130699769,2130703283,1820], [2130706334,2358,2130697417,2940,4200,2130706027], [440,2130701201,9212,1960,2130704263], [2130705278,7308,2130701533,2130703297,420], [1980,2130699881,392,1512], [2130704123,3612,1064,2130706167], [1848,2130705425,2130705859], [2130705443,2130706415,98], [330,92], [2130706378,2130706415], [0], [1]]]
def block35u12 : Block where
  bank := .leftLow
  cap := 79
  free := [(7,2),(8,0)]
  vectors := [
    [[1970330680,435305616,532676618,355117833,177559534,3654,532692899,1065413725,1598220681,518375,533901387,1067889484,1602657971,7470400,543369452,1078945009,1613379996], [1724039345,1976058386,85915590,1758405653,1013804383,120284570,1941704092,1323143059,739006031,395559566,1667558414,1599623121,466746484,674487663,1397788227], [1477748010,1878687393,486854971,481127318,1787044498,343664371,1116911185,756087403,2027697941,1718542400,258258265,1100708223,70406528], [1231456675,143192637,996620756,171831209,51549642,1735496242,1718317760,1512135221,85976455,1151420119,2027932656], [985165340,1030986984,876338940,1202818181,1769861201,618593247,652962691,1649593497,1477788592], [738874005,280657568,1517841951,670141563,904977612,561315867,927891203], [492582670,22910822,51549351,916432890,1626668451], [246291335,257746746,1], [0]],
    [[1237184375,1512114078,2130704004,2130683143,2130543018,2129811609,2126725400,2115919739,2083967858,2003242733,1827785048,1498850663,968055398,236960033,1524995341,749597836,257441881], [549859720,1649579038,1924507094,893503979,549736484,136808272,1303071323,1501814846,2030254890,671850523,492839720,1737389873,743799903,277065310,677881726], [1993241498,1030986875,962253012,549846104,824699121,1305446423,1578854689,1161403231,1078510463,82543936,1388703536,101657515,271599155], [1305916843,1787044022,1443380659,1718301779,1580782615,1374322240,136103806,201464709,1910539274,1889127884,1022273048], [618592188,1787044046,1305916070,1374642586,1718268425,1924290284,136561276,1577733829,1984175002], [2061973966,1030986947,618591713,1374645160,1237157374,2061835270,755477833], [1374649311,1649579158,1580846489,2061971890,2061959240], [687324656,1512114246,0], [1]]]
def block36u10 : Block where
  bank := .rightLow
  cap := 78
  free := [(18,0)]
  vectors := [
    [[0,0,0,0,1], [0,0,0,8,2130706431], [0,0,0,28,2130706409,1], [0,0,56,2130706321,24], [0,0,70,2130706153,168,2130706425], [0,56,2130706013,560,2130706321], [0,28,2130706041,1050,2130705873,28], [8,2130706209,1176,2130705033,280], [1,2130706361,784,2130704473,1050,2130706377], [2130706423,288,2130704865,1960,2130706013], [45,2130705761,1960,2130705257,70], [2130706313,1008,2130704865,392], [210,2130705425,784,2130706377], [2130706181,672,2130706209], [210,2130706145,28], [2130706313,72], [45,2130706425], [2130706423], [1]]]
def block36u11 : Block where
  bank := .leftLow
  cap := 77
  free := [(7,0),(7,1),(7,2),(8,0)]
  vectors := [
    [[1408,42224,621726,5996950,42644840,238479528,1092074634,2077956673,1131472302,1676427906,1045297919,558888412,1103451277,1681235625,109312149,34708593,1116376740], [1057,30786,441225,4151980,28869645,158192622,711073881,562656967,235949293,1341704087,1896992881,902509461,1203933366,399994888,1593714435], [756,21400,299040,2752680,18781560,101266956,448893900,1679195700,1134475034,162189769,713329079,919719979,1020755657], [505,13916,190218,1720908,11590551,61916400,272661480,1014778440,1113872632,485153248,556727620], [304,8184,110106,987426,6633900,35528220,157372020,589813380,1896832080], [153,4054,54351,491400,3362450,18480540,84326970], [52,1376,18900,179900,1327600], [1,0,0], [0]],
    [[710235361,2130702934,1065301686,1775091511,2127169643,2110919443,974699405,715817971,974429714,933831791,1173100686,1406153041,849600274,1538980696,1700576279,1736568122,71971065], [1065353129,2130703884,2130669889,2130362398,1062959774,2117583498,2071681544,1906995764,337427479,70278908,1271460249,1538948763,458220924,359778819,984106949], [1065353154,355115969,2130681688,2130478493,1063796714,1056953584,2093441114,1991197583,616756204,1941907887,1187760141,1883787872,1169229802], [710235436,2130705284,2130690712,2130564039,2129746187,2125570484,2108063813,2046356453,1860812588,1380995328,310392938], [2130706408,2130705759,1065344132,1065271582,2130156884,2127758033,2117627588,2081636048,1972785098], [1065353204,1420470623,2130701960,2130665834,709956736,2129170483,2123685913], [1775588690,1065353105,2130704884,1420456072,2130595908], [0,1,0], [0]],
    [[1420470960,140,1065355279,355137646,141670,792918,1068987424,1079370874,46385703,133523975,1403078299,1821356029,1505285600,544070287,1053839238,716449015,1298173926], [1065353220,102,1463,13780,1065449134,526176,2367792,8977878,1094575429,82732650,205632765,451585680,1945307974,1525362300,224570617], [1065353219,1775588765,991,9135,1065415639,1065690298,1496313,5604105,1083378529,1115753404,123518395,266763315,1574752789], [1420470957,46,630,5712,38556,206388,910455,3393000,10858185,30160130,73213140], [1,27,1065353581,1065356497,22113,118755,527085,1977885,6364215], [1065353217,710235491,180,1638,1420482222,62140,284050], [355117739,1065353221,63,710236086,4525], [0,0,1], [0]],
    [[1420471065,3283,1065401499,355583178,3309870,18521198,1150267812,1393139854,1086014475,1000533042,477971267,1823063985,1444189272,1518352043,1785332253,2128291403,283232897], [1065353298,2370,33940,319390,1067575849,12197864,54947025,208669500,1745946604,1931578350,552813044,2081373718,487073099,1958512972,448692317], [1065353274,1775590320,22720,209380,1066784874,1073095129,34438950,129329850,1482649804,105556946,749799767,1984308434,255874006], [1420470993,1038,14213,128996,872550,4684680,20742540,77631840,249603705,696774650,1700133435], [22,594,1065361251,1065425779,491400,2653560,11850345,44764785,145044900], [1065353227,710235759,3825,35100,1420714597,1356940,6267040], [355117742,1065353304,1250,710247761,92975], [0,0,0], [1]]]
def block37u10 : Block where
  bank := .rightLow
  cap := 75
  free := [(15,1),(16,1),(17,0),(18,0)]
  vectors := [
    [[0,0,0,2130706432,2130706432], [0,0,2130706427,2130706430,2], [0,0,2130706418,9,15,2130706432], [0,2130706413,55,24,2130706416], [0,2130706418,105,2130706383,2130706367,6], [2130706427,99,2130706223,2130706383,54], [2130706432,47,2130706160,175,125,2130706418], [9,2130706273,399,0,2130706348], [0,2130706397,308,2130706118,2130706328,20], [0,84,2130706069,105,70], [0,2130706307,266,21,2130706418], [0,126,2130706321,2130706406], [0,2130706349,20,6], [0,36,2], [0,2130706424,2130706432], [0,1], [0,0], [0], [0]],
    [[0,0,0,2130706424,2130706423], [0,0,2130706379,2130706399,20], [0,0,2130706298,60,156,2130706423], [0,2130706253,460,300,2130706259], [0,2130706298,910,2130706158,2130705713,61], [2130706379,870,2130704753,2130705633,570], [2130706424,416,2130704123,1050,1475,2130706277], [80,2130705049,3150,700,2130705493], [0,2130706118,2576,2130704333,2130704963,215], [0,720,2130703549,210,840], [0,2130705383,1904,630,2130706263], [0,1008,2130705817,2130706043], [0,2130705803,2130706417,75], [0,240,74], [0,2130706388,2130706417], [0,0], [0,1], [0], [0]],
    [[0,0,0,2130706425,2130706424], [0,0,2130706385,2130706401,17], [0,0,2130706313,44,136,2130706425], [0,2130706273,384,276,2130706289], [0,2130706313,770,2130706257,2130705821,48], [2130706385,736,2130705103,2130705697,460], [2130706425,348,2130704585,700,1224,2130706313], [64,2130705349,2352,700,2130705697], [2130706432,2130706209,1876,2130705033,2130705243,160], [9,448,2130704501,0,630], [2130706397,2130705873,1148,504,2130706313], [84,448,2130706125,2130706161], [2130706307,2130706209,2130706397,48], [126,64,44], [2130706349,2130706425,2130706425], [36,0], [2130706424,0], [1], [0]],
    [[0,0,0,2130706353,2130706336], [0,0,2130705953,2130706065,184], [0,0,2130705233,300,1504,2130706346], [0,2130704833,3616,3320,2130704849], [0,2130705233,7490,2130705793,2130699473,528], [2130705953,7248,2130694393,2130696833,5160], [2130706353,3452,2130688737,3850,14480,2130705093], [640,2130695817,21168,11200,2130697953], [2130706424,2130704193,17976,2130696353,2130691383,1824], [80,4480,2130688681,2130702513,7560], [2130706118,2130700833,9520,7392,2130705023], [720,4480,2130704921,2130702929], [2130705383,2130704193,2130705289,592], [1008,640,664], [2130705803,2130706353,2130706325], [240,0], [2130706388,0], [0], [1]]]
def block37u11 : Block where
  bank := .leftLow
  cap := 71
  free := [(7,1)]
  vectors := [
    [[573651732,1884855692,327801010,1966806148,1966807512,327810118,819545073,1639169258,534006,1483350,3560040,7443720,13646820,1169348327,1670497610,695492684], [573651732,1311203960,1147303483,819502665,1147304847,1311211704,1639039802,129456,404550,1078800,2481240,4962480,8684340,1160663987], [573651732,737552228,409751255,409751410,737553437,573658267,1065381535,1065454354,1065656629,1066128604,1067059069,1068609844], [573651732,163900496,245850759,163900651,573652786,5481,1065376054,78300,1065578329,550275], [573651732,1720955197,655601995,1639005089,1065354130,1065357784,18270,60030], [573651732,1147303465,1639004963,126,1065354004,3780], [573651732,573651733,1065353230,1065353329], [573651732,1]]]
def block38u9 : Block where
  bank := .rightLow
  cap := 72
  free := [(16,1),(18,0)]
  vectors := [
    [[0,0,0,2130706432], [0,0,0,2130706426,2], [0,0,2130706412,21,2130706432], [0,0,2130706398,84,2130706412], [0,2130706398,175,2130706307,7], [0,2130706412,210,2130706083,84], [2130706426,147,2130705908,350,2130706412], [2130706432,56,2130705992,700,2130706258], [9,2130706237,735,2130705908,35], [0,2130706397,392,2130705698,210], [0,84,2130705943,441,2130706398], [0,2130706307,392,2130706286], [0,126,2130706237,21], [0,2130706349,56], [0,36,2130706426], [0,2130706424], [0,1], [0], [0]],
    [[0,0,0,2130706425], [0,0,0,2130706377,15], [0,0,2130706265,160,2130706426], [0,0,2130706153,644,2130706281], [0,2130706153,1344,2130705509,48], [0,2130706265,1610,2130703857,588], [2130706377,1120,2130702583,2464,2130706293], [2130706425,420,2130703241,4900,2130705257], [64,2130705061,5040,2130702933,224], [2130706432,2130706209,2548,2130701673,1330], [9,448,2130703493,2688,2130706223], [2130706397,2130705873,2156,2130705593], [84,448,2130705453,112], [2130706307,2130706209,252], [126,64,2130706405], [2130706349,2130706425], [36,0], [2130706424], [1]]]
def block38u10 : Block where
  bank := .leftLow
  cap := 70
  free := [(7,0),(7,1)]
  vectors := [
    [[532676562,2130704928,1065329275,2130458185,2128819339,2119494353,2076514713,1911803529,1377490970,2022978382,587770749,1682923631,1031436419,1296965239,719937828,719681883], [1065353177,1065351967,2130687089,2130511009,2129257493,2122302581,2091035361,1974194129,1605001799,607305983,415922386,7210052,417621604,1093409002], [1598029792,1065352209,1598014627,2130556548,531589942,1059182930,1569498936,2020474649,170452652,40257229,1207718879,969059124], [2130706407,2130705654,1065341734,1065242219,2129915748,2126288747,1045247995,988968304,1884374633,1448515508], [532676589,2130705869,2130698255,2130628278,1597477614,2127642554,1051518259,2078691743], [1065353204,1065352854,2130701169,2130655655,1064989990,1063315954], [1598029819,1065353042,532673888,2130678119], [1,0]],
    [[532676610,57,1065354124,9416,71610,425568,2056912,8306760,28569321,84847620,219832470,500671080,1008003750,1801380240,735125767,1936045927], [1065353218,1065353264,736,7440,55180,320044,1510320,5954976,19984770,57850650,145853760,322561200,628994340,1085542500], [1598029826,1065353255,1598030406,5735,532718187,1065589204,1599120087,4207320,546481877,1104358579,1693790181,205632765], [1,30,1065353659,1065357494,30450,169911,1066125124,1068279679,9415575,26013000], [532676609,22,319,3045,1598051292,118755,1065887614,2001870], [1065353217,1065353231,210,2016,1065367549,1065433069], [1598029825,1065353224,532676723,1170], [0,1]]]
def block39u9 : Block where
  bank := .leftLow
  cap := 68
  free := [(6,2),(6,3),(7,0),(7,1)]
  vectors := [
    [[2035466956,1386509583,1170084864,665409270,1725057426,1401628957,1380468422,322526456,52156263,410394656,74391477,1794456481,89955748,1408060781,569204561,418717593], [1193341151,1470991115,347734744,1564331208,1302337324,1180799322,1847616452,829962503,268083156,1774395701,1664588692,2114065822,339350897,239566821], [1854005694,2075809256,648957310,488220408,913313763,132391142,1497119534,2064324925,1254549580,1735424816,1055346366,1901062088], [1886754152,823299395,1155371895,822982677,374943685,806198132,215872581,160086306,549956354,209972062], [1291586525,1727916220,1442514188,1351704324,777418723,1612418681,1439624777,1451820293], [68502813,281288687,1579836234,403106577,1598029368,431896542], [348209449,497871484,1,0], [0,0]],
    [[1973204456,1387247883,24152662,346926388,24470288,866127810,2130182121,1667011842,288529849,415980129,1231122957,161393306,215974512,2050549612,2044525333,1628286241], [58483156,1040884160,1274289443,2077338680,502038354,1119886125,1582708363,1719476443,140228680,404293837,1780257712,296031105,1309241809,1855541262], [412897761,15591993,349211421,1455100361,263552632,217218628,1094161611,1192930167,195614059,1608354445,1007029541,296919501], [905741838,26789399,1183743378,784873170,1184007334,1900361541,14405524,2019684245,1995104510,562591845], [1537015387,659187962,20461196,495182015,691040070,604660866,1871571344,715741344], [176011975,1497499266,324636888,2015533119,1598029886,28793761], [1084144468,2126434895,0,1], [0,0]],
    [[1785186575,1957949790,287986057,864348219,1328710971,1465278005,415750129,135586229,1320835505,1177040661,1599979616,1581688225,75255829,1235346162,1225643881,899989675], [1957946526,806215558,518315661,2015896935,1903110621,1801648979,944953267,1547724849,1273388429,1220780919,103074271,1683032518,320736488,670135189], [1785186520,2073121269,1957969092,518506895,462388987,2083184515,625217330,320263114,1598690784,1778713044,437169072,461029428], [1266906557,403107495,57599663,1612555712,922349589,1790917523,316218817,636853005,1062078574,2039885808], [403106637,1094146973,978979543,748689687,1037037474,1442578253,1224127653,985459244], [1324493193,921386708,287935427,1957968410,176904,577040474], [1900359792,921386571,0,0], [1,0]],
    [[411966105,1435236648,722046266,1510523080,2108409316,1970336309,2028774603,52057760,277455846,1743131714,1360427414,1807117953,1357228600,2075462675,521060388,603375240], [2008888495,22148633,775203770,1940214534,1749650903,1722587749,1999383964,103294858,1281989197,2055551710,671442942,1586181407,775732423,1777591485], [821717344,2035466902,1107434957,939097359,516004247,1543406353,458942128,511042653,1730597830,1848931039,1047525623,794304172], [1111865518,912527047,1734243945,2011098632,48692158,575659955,1294688169,1262697416,1770075629,931716178], [748626584,744196825,881518637,828359591,403088945,1151626846,114638701,2013243190], [1862706975,1359931127,1377650020,287932447,1065346507,460649680], [192693825,458478411,0,0], [0,1]]]
def block40u8 : Block where
  bank := .rightLow
  cap := 66
  free := [(14,2),(16,1),(18,0)]
  vectors := [
    [[0,0,0,1], [0,0,6,2130706431], [0,0,15,2130706415,1], [0,20,2130706373,18], [0,15,2130706333,90,2130706427], [6,2130706343,200,2130706373], [1,2130706391,225,2130706233,15], [2130706425,126,2130706133,100], [0,28,2130706223,225,2130706413], [0,2130706377,210,2130706343], [0,0,70,2130706307,15], [0,0,2130706377,42], [0,0,28,2130706427], [0,0,2130706425], [0,0,1], [0,0], [0,0], [0], [0]],
    [[0,0,0,7], [0,0,42,2130706420], [0,0,105,2130706314,6], [0,140,2130706034,112], [0,105,2130705768,567,2130706398], [42,2130705838,1260,2130706076], [7,2130706160,1400,2130705243,84], [2130706384,756,2130704683,560], [1,147,2130705278,1225,2130706328], [2130706425,2130706188,1050,2130705978], [0,28,245,2130705866,70], [0,2130706377,2130706286,168], [0,70,49,2130706412], [0,2130706377,2130706426], [0,28,0], [0,2130706425], [0,1], [0], [0]],
    [[0,0,0,28], [0,0,168,2130706385], [0,0,420,2130705985,21], [0,560,2130704921,400], [0,420,2130703913,2044,2130706313], [168,2130704193,4536,2130705201], [28,2130705425,4970,2130702345,280], [2130706265,2576,2130700553,1848], [8,420,2130702793,3920,2130706097], [2130706377,2130705873,3080,2130705033], [1,168,420,2130704865,210], [2130706425,2130706153,2130706265,448], [28,280,28,2130706377], [2130706377,2130706265,0], [70,56,0], [2130706377,2130706425], [28,0], [2130706425], [1]]]
def block40u9 : Block where
  bank := .leftLow
  cap := 63
  free := [(7,0)]
  vectors := [
    [[1,35,595,6545,52360,324632,1623160,6724520,23535820,70607460,183579396,417225900,834451800,1476337800,189252967], [1,34,561,5984,46376,278256,1344904,5379616,18156204,52451256,131128140,286097760,548354040], [1,33,528,5456,40920,237336,1107568,4272048,13884156,38567100,92561040], [1,32,496,4960,35960,201376,906192,3365856,10518300], [1,31,465,4495,31465,169911,736281], [1,30,435,4060,27405], [1,29,406], [1]]]
def block41u8 : Block where
  bank := .leftLow
  cap := 62
  free := [(6,2),(7,0)]
  vectors := [
    [[738399988,778809938,422467662,1359243839,1065353871,852286762,1337223797,147040422,353617,1136212,429330796,860166704,17264520,33643680,58544430], [1241687542,1733954201,1910288532,433488614,1337202479,1616401182,999244156,69564,1278676609,1705358176,854452970,5220462,11098620], [1744975096,1682523356,1755995996,264501538,191029243,146947670,1278435863,1278474055,852461189,852830492,1462890], [117556217,624517403,1469452716,44083619,146945562,852284334,8680,35712,852407342], [620843771,690642775,429814921,1212298515,1598030034,1704566405,1811106620], [1124131325,1880899472,146945273,1065353235,1065353360], [1627418879,2064581061,1], [0]],
    [[532676604,2130706286,1598027331,1065325549,1065127414,2129261297,2123158739,2097663533,2007143378,1730597493,997456700,1432621264,133730799,460027398,1767240913], [1065353213,2130706315,2130704478,1065331992,2130536637,2129639785,2125234065,2107170613,2044296351,1856346017,1370163221,277031363,267964966], [1598029822,1065353126,1065351748,2130690769,2130582991,2129941229,2126829945,2114251137,2071164764,1944813011,1625477423], [2130706431,1065353152,2130705401,2130695521,2130620873,2130177821,2128038201,2119443761,2090316161], [532676607,2130706393,532675965,1065346319,1597974761,2130360318,530906702], [1065353216,2130706416,2130706133,1065349664,1065322259], [1598029825,1065353221,0], [1]]]
def block42u7 : Block where
  bank := .rightHigh
  cap := 60
  free := [(12,3),(14,2),(16,1)]
  vectors := [
    [[0,0,2130706432], [0,0,2130706428,2], [0,2130706423,15,2130706432], [0,2130706423,40,2130706418], [2130706428,50,2130706373,5], [2130706432,30,2130706333,40], [7,2130706358,100,2130706423], [0,2130706412,100,2130706383], [0,35,2130706358,10], [0,0,2130706398,30], [0,0,21,2130706428], [0,0,0,2130706426], [0,0,0,1], [0,0,0], [0,0,0], [0,0], [0,0], [0], [0]],
    [[0,0,2130706427], [0,0,2130706403,11], [0,2130706373,84,2130706428], [0,2130706373,225,2130706355], [2130706403,280,2130706118,24], [2130706427,165,2130705913,195], [36,2130706058,480,2130706388], [2130706432,2130706343,450,2130706213], [7,120,2130706133,40], [0,2130706412,2130706343,105], [0,35,36,2130706418], [0,0,2130706398,2130706427], [0,0,21,0], [0,0,2130706426], [0,0,1], [0,0], [0,0], [0], [0]],
    [[0,0,2130706412], [0,0,2130706328,35], [0,2130706223,273,2130706418], [0,2130706223,735,2130706195], [2130706328,910,2130705467,70], [2130706412,525,2130704858,567], [105,2130705348,1365,2130706307], [2130706426,2130706223,1190,2130705838], [42,210,2130705698,105], [2130706432,2130706328,2130706328,245], [7,140,21,2130706398], [0,2130706412,2130706328,0], [0,35,42,0], [0,2130706398,2130706426], [0,21,0], [0,2130706426], [0,1], [0], [0]]]
def block43u7 : Block where
  bank := .leftHigh
  cap := 55
  free := [(6,1)]
  vectors := [
    [[824789587,687324657,1718311661,1580846959,1718313770,687338717,824864580,332112,1245420,4013020,11236456,27580392,59757516,114918300], [824789587,1993241503,1855776591,1855776801,1993243402,824801748,62832,269280,976140,3036880,8199576,19380816], [824789587,1168451916,687324675,1168452126,824791276,10472,52360,216920,759220,2277660], [824789587,343662329,343662346,824789780,1496,8976,43384,173536], [824789587,1649579175,824789604,176,1320,7656], [824789587,824789588,16,160], [824789587,1]]]
def block44u6 : Block where
  bank := .leftHigh
  cap := 54
  free := [(6,0),(6,1)]
  vectors := [
    [[2130706402,2130705287,1420450149,2130459125,2128542488,2115850711,2047450106,1739478497,559788997,926939579,400447108,1431272219,1934507775,842673283], [710235452,1420470027,2130689915,2130513723,2129049358,2119518410,2069026353,1845679537,1006204373,1133068177,623042163,1881818535], [1420470935,1420470234,1420458332,2130561253,709002836,702011467,2085907217,1216107382,625856842,883784455], [2130706418,2130705908,1420461849,2130602274,2129825289,704376643,2098938873,1986801705], [710235468,1420470616,2130700482,1420401846,709641683,2126707185], [1420470951,1420470791,1420467814,710195963], [1,0]],
    [[1,37,355118411,7992,69930,479927,1068041248,12620256,50619404,175880980,534935566,725306901,1289262175,875313993], [1775588695,355117769,537,6265,1065407064,1065716464,2000152,9228824,36347190,834078721,1789198802,966680316], [1420470956,1420470979,355118153,4760,1775629055,710504259,1460844,1427118182,1446248282,1506768962], [1065353217,1065353234,355118042,1065356676,29172,710428711,1043460,4707164], [710235478,1420470967,1065353420,1420473302,710255483,133672], [355117739,355117745,1420471070,710236883], [0,1]]]
def block46u5 : Block where
  bank := .leftHigh
  cap := 47
  free := [(5,2),(6,0)]
  vectors := [
    [[940549529,459422270,206197398,412394809,1580846848,412395771,206202936,1580872822,2062078422,359788,1079364,2845596,1128062282], [940549529,1649579174,687324657,1855776585,1855776696,687325508,1649583861,2061995394,83028,276760,1346512272], [940549529,709029645,2109001445,1877481573,2109001556,709030385,940553476,1121441918,65495], [940549529,1899186549,209814896,1667666677,441334879,267695506,1078017774], [940549529,958637020,1381884309,285782368,1819601677], [940549529,18087491,1], [0]],
    [[766909616,79584962,1512114278,893522487,1649583084,893549423,1512269342,1650310356,209122125,10074064,30222192,79676688,1756961402], [766909616,1443381779,68732499,824789988,824793096,68756327,1443513015,206797341,2324784,7749280,1480132879], [766909616,676472163,1522966769,1432529652,1522969877,676492883,767020132,1570483642,1865325], [766909616,2040268980,1613404222,1949831863,1703844447,1103354869,354603550], [766909616,1273359364,340044858,1609787005,1942599403], [766909616,506449748,0], [1]]]
def block48u4 : Block where
  bank := .leftHigh
  cap := 40
  free := [(5,0),(5,1)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,2130381801,2127923873], [0,0,0,0,0,0,0,0,46376,321904], [0,0,0,0,0,0,2130700977,2130677665], [0,0,0,0,496,1767], [0,0,2130706402,2130706377], [1,0]],
    [[0,0,0,0,0,0,0,0,0,0,0,2130428177], [0,0,0,0,0,0,0,0,0,40920], [0,0,0,0,0,0,0,2130701473], [0,0,0,0,0,465], [0,0,0,2130706403], [0,1]]]
def block49u4 : Block where
  bank := .leftHigh
  cap := 35
  free := [(5,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,2130381801], [0,0,0,0,0,0,0,0,46376], [0,0,0,0,0,0,2130700977], [0,0,0,0,496], [0,0,2130706402], [1]]]
def block50u3 : Block where
  bank := .rightHigh
  cap := 32
  free := [(4,1),(6,1),(8,1)]
  vectors := [
    [[2130706432], [2130706432,2], [3,2130706432], [0,2130706430], [0,1], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0], [0]],
    [[2130706431], [2130706431,3], [4,2130706432], [2130706432,2130706431], [3,0], [0,2130706430], [0,1], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0], [0]],
    [[2130706430], [2130706430,3], [3,2130706432], [2130706430,0], [6,0], [2130706432,2130706430], [3,0], [0,2130706430], [0,1], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0,0], [0], [0]]]
def block51u3 : Block where
  bank := .leftHigh
  cap := 28
  free := [(4,0),(4,1)]
  vectors := [
    [[0,0,0,0,0,0,0,0,66045,471240], [0,0,0,0,0,0,2130699293,2130667758], [0,0,0,0,595,2176], [0,0,2130706399,2130706370], [1,0]],
    [[0,0,0,0,0,0,0,0,0,58905], [0,0,0,0,0,0,0,2130699888], [0,0,0,0,0,561], [0,0,0,2130706400], [0,1]]]
def block52u2 : Block where
  bank := .rightHigh
  cap := 24
  free := [(2,1),(4,1),(6,1)]
  vectors := [
    [[1], [2130706431], [0,1], [0], [0,0], [0], [0,0], [0], [0,0], [0], [0,0], [0], [0,0], [0], [0,0], [0], [0,0], [0], [0]],
    [[1], [2130706432], [1,0], [2130706431], [0,1], [0], [0,0], [0], [0,0], [0], [0,0], [0], [0,0], [0], [0,0], [0], [0,0], [0], [0]],
    [[1], [0], [2,0], [2130706431], [1,0], [2130706431], [0,1], [0], [0,0], [0], [0,0], [0], [0,0], [0], [0,0], [0], [0,0], [0], [0]]]
def block52u3 : Block where
  bank := .leftHigh
  cap := 24
  free := [(4,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,66045], [0,0,0,0,0,0,2130699293], [0,0,0,0,595], [0,0,2130706399], [1]]]
def block53u2 : Block where
  bank := .leftHigh
  cap := 21
  free := [(3,0),(3,1),(3,2),(4,0)]
  vectors := [
    [[0,0,0,0,0,0,2130697294,2130655817,2130519953], [0,0,0,0,703,2627,7344], [0,0,2130706396,2130706363,2130706301], [1,0,0], [0]],
    [[0,0,0,0,0,0,0,2130697997,2130659813], [0,0,0,0,0,666,2484], [0,0,0,2130706397,2130706365], [0,1,0], [0]],
    [[0,0,0,0,0,0,0,0,2130698663], [0,0,0,0,0,0,630], [0,0,0,0,2130706398], [0,0,1], [0]],
    [[0,0,0,0,0,0,0,0,2130508298], [0,0,0,0,0,0,14280], [0,0,0,0,2130705838], [0,0,0], [1]]]
def block54u1 : Block where
  bank := .rightHigh
  cap := 16
  free := [(2,0),(4,0)]
  vectors := [
    [[], [2130706432], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
    [[], [2130706432], [0], [2130706432], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]
def block54u2 : Block where
  bank := .leftHigh
  cap := 18
  free := [(3,0),(3,1)]
  vectors := [
    [[0,0,0,0,0,0,2130697294,2130655817], [0,0,0,0,703,2627], [0,0,2130706396,2130706363], [1,0]],
    [[0,0,0,0,0,0,0,2130697997], [0,0,0,0,0,666], [0,0,0,2130706397], [0,1]]]
def block55u1 : Block where
  bank := .rightHigh
  cap := 14
  free := [(1,0),(2,0),(4,0),(6,0)]
  vectors := [
    [[], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
    [[], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
    [[], [0], [0], [2130706432], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
    [[], [0], [0], [2130706432], [0], [2130706432], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]
def block55u2 : Block where
  bank := .leftHigh
  cap := 15
  free := [(3,0)]
  vectors := [
    [[0,0,0,0,0,0,2130697294], [0,0,0,0,703], [0,0,2130706396], [1]]]
def block56u0 : Block where
  bank := .rightHigh
  cap := 8
  free := [(2,0)]
  vectors := [
    [[], [], [1], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0]]]
def block56u1 : Block where
  bank := .leftHigh
  cap := 12
  free := [(2,0),(2,1),(2,2),(3,0)]
  vectors := [
    [[0,0,0,0,820,3120,8892], [0,0,2130706393,2130706356,2130706285], [1,0,0], [0]],
    [[0,0,0,0,0,780,2964], [0,0,0,2130706394,2130706358], [0,1,0], [0]],
    [[0,0,0,0,0,0,741], [0,0,0,0,2130706395], [0,0,1], [0]],
    [[0,0,0,0,0,0,18278], [0,0,0,0,2130705730], [0,0,0], [1]]]
def block57u0 : Block where
  bank := .rightHigh
  cap := 7
  free := [(2,0),(4,0)]
  vectors := [
    [[], [], [1], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0]],
    [[], [], [0], [], [1], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0]]]
def block57u1 : Block where
  bank := .leftHigh
  cap := 10
  free := [(2,0),(2,1)]
  vectors := [
    [[0,0,0,0,820,3120], [0,0,2130706393,2130706356], [1,0]],
    [[0,0,0,0,0,780], [0,0,0,2130706394], [0,1]]]
def block58u0 : Block where
  bank := .rightHigh
  cap := 6
  free := [(2,0),(4,0),(6,0)]
  vectors := [
    [[], [], [1], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0]],
    [[], [], [0], [], [1], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0]],
    [[], [], [0], [], [0], [], [1], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0]]]
def block58u1 : Block where
  bank := .leftHigh
  cap := 8
  free := [(2,0)]
  vectors := [
    [[0,0,0,0,820], [0,0,2130706393], [1]]]
def block59u0 : Block where
  bank := .rightHigh
  cap := 5
  free := [(2,0),(4,0),(6,0),(8,0)]
  vectors := [
    [[], [], [1], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0]],
    [[], [], [0], [], [1], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0]],
    [[], [], [0], [], [0], [], [1], [], [0], [], [0], [], [0], [], [0], [], [0], [], [0]],
    [[], [], [0], [], [0], [], [0], [], [1], [], [0], [], [0], [], [0], [], [0], [], [0]]]
def block60u0 : Block where
  bank := .leftHigh
  cap := 4
  free := [(1,0),(1,1)]
  vectors := [
    [[0,0,2130706390,2130706349], [1,0]],
    [[0,0,0,2130706391], [0,1]]]
def block61u0 : Block where
  bank := .leftHigh
  cap := 3
  free := [(1,0)]
  vectors := [
    [[0,0,2130706390], [1]]]
def exceptional : Nat → Nat → Option Block
  | 31,15 => some block31u15
  | 32,14 => some block32u14
  | 33,13 => some block33u13
  | 34,12 => some block34u12
  | 34,13 => some block34u13
  | 35,11 => some block35u11
  | 35,12 => some block35u12
  | 36,10 => some block36u10
  | 36,11 => some block36u11
  | 37,10 => some block37u10
  | 37,11 => some block37u11
  | 38,9 => some block38u9
  | 38,10 => some block38u10
  | 39,9 => some block39u9
  | 40,8 => some block40u8
  | 40,9 => some block40u9
  | 41,8 => some block41u8
  | 42,7 => some block42u7
  | 43,7 => some block43u7
  | 44,6 => some block44u6
  | 46,5 => some block46u5
  | 48,4 => some block48u4
  | 49,4 => some block49u4
  | 50,3 => some block50u3
  | 51,3 => some block51u3
  | 52,2 => some block52u2
  | 52,3 => some block52u3
  | 53,2 => some block53u2
  | 54,1 => some block54u1
  | 54,2 => some block54u2
  | 55,1 => some block55u1
  | 55,2 => some block55u2
  | 56,0 => some block56u0
  | 56,1 => some block56u1
  | 57,0 => some block57u0
  | 57,1 => some block57u1
  | 58,0 => some block58u0
  | 58,1 => some block58u1
  | 59,0 => some block59u0
  | 60,0 => some block60u0
  | 61,0 => some block61u0
  | _, _ => none
end CJ1
end
section
namespace CJ1
def total {α : Type*} [AddMonoid α] (f : ℕ → α) : ℕ → α
  | 0 => 0
  | n + 1 => total f n + f n
def rowLo (q u h : ℕ) := u + 2*q + h + 1 - 64
def rowHi (q u h : ℕ) := min (q + 1 - h) (u + 2*q + h + 1 - 18)
def rowLen (q u h : ℕ) := rowHi q u h - rowLo q u h
def colLo (u b : ℕ) := (19 - (u+b)) / 2
def colHi (q b : ℕ) := min 9 (min (q-b+1) ((18-b)/2+1))
def colLen (q u b : ℕ) := colHi q b - colLo u b
abbrev Row (q u : ℕ) := (h : Fin (q+1)) × Fin (rowLen q u h)
abbrev Col (q u : ℕ) := (b : Fin (min q 18 + 1)) × Fin (colLen q u b)
def rowAt (q u h i : ℕ) : CJ0.Jet :=
  let d := rowLo q u h + i
  ⟨q - (h+d), d, h⟩
def rowJet (q u : ℕ) (r : Row q u) : CJ0.Jet := rowAt q u r.1 r.2
def colAt (q u b i : ℕ) : CJ0.Jet :=
  let c := colLo u b + i
  ⟨c, b, q - (b+c)⟩
def colJet (q u : ℕ) (s : Col q u) : CJ0.Jet := colAt q u s.1 s.2
def packet (q u : ℕ) : Matrix (Row q u) (Col q u) (ZMod CJ0.p) :=
  fun r s => CJ0.blockEntry (rowJet q u r) (colJet q u s)
def rows (q u : ℕ) := total (rowLen q u) (q+1)
def cols (q u : ℕ) := total (colLen q u) (min q 18 + 1)
def nominal (q u : ℕ) := min (rows q u) (cols q u)
def allowance (q u : ℕ) : ℕ :=
  match exceptional q u with
  | none => nominal q u
  | some z => z.cap
def grade (q : ℕ) := total (allowance q) (64-q)
def outer (onRows : Bool) (q : ℕ) := if onRows then q+1 else min q 18+1
def fiber (onRows : Bool) (q u : ℕ) := if onRows then rowLen q u else colLen q u
abbrev Axis (onRows : Bool) (q u : ℕ) :=
  (i : Fin (outer onRows q)) × Fin (fiber onRows q u i)
def fastChoose (n k : ℕ) := n.descFactorial k / k.factorial
def entryZ (r c : CJ0.Jet) : ℤ :=
  if c.b ≤ r.b ∧ c.c ≤ r.c ∧ r.a + (r.b-c.b) + (r.c-c.c) = c.a then
    (-1 : ℤ)^(r.c-c.c) * (fastChoose c.a r.a : ℤ) * (fastChoose (c.a-r.a) (r.b-c.b) : ℤ)
  else 0
def orientedEntry (onRows : Bool) (q u i k b t : ℕ) : ℤ :=
  if onRows then entryZ (rowAt q u b t) (colAt q u i k)
  else entryZ (rowAt q u i k) (colAt q u b t)
def dot (q u : ℕ) (z : Block) (j i k : ℕ) : ℤ :=
  total (fun b => total (fun t =>
    let w := z.coeff j b t
    if w = 0 then 0 else orientedEntry z.bank.onRows q u i k b t * (w : ℤ))
    (fiber z.bank.onRows q u b)) (outer z.bank.onRows q)
def Dots (q u : ℕ) (z : Block) : Prop :=
  ∀ j < z.free.length, ∀ i < outer (!z.bank.onRows) q,
    ∀ k < fiber (!z.bank.onRows) q u i, dot q u z j i k % (CJ0.p : ℤ) = 0
end CJ1
end
section
namespace CJ1
open scoped BigOperators
open CJ0 (Jet blockRows blockCols blockMatrix source180120)
theorem total_eq_sum {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    total f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [total]
  | succ n ih => rw [total, Finset.sum_range_succ, ih]
private theorem row_bounds (q u c d h : ℕ)
    (hr : (⟨c,d,h⟩ : Jet) ∈ blockRows 46 q ((u : ℤ)-18)) :
    h < q+1 ∧ rowLo q u h ≤ d ∧ d < rowHi q u h ∧ q-(h+d) = c := by
  simp only [blockRows, Finset.mem_filter, Finset.mem_sigma, Finset.mem_range,
    Finset.mem_singleton, Jet.v, Jet.b, Jet.c, Jet.a, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hr
  unfold rowLo rowHi
  omega
private theorem col_bounds (q u c b a : ℕ)
    (hs : (⟨c,b,a⟩ : Jet) ∈ blockCols source180120 q ((u : ℤ)-18)) :
    b < min q 18 + 1 ∧ colLo u b ≤ c ∧ c < colHi q b ∧ q-(b+c) = a := by
  change (⟨c,b,a⟩ : Jet) ∈ (CJ0.fullBox 63 18 8).filter _ at hs
  rw [Finset.mem_filter, CJ0.mem_fullBox (by decide) (by decide)] at hs
  simp only [Jet.q, Jet.v, Jet.a, Jet.b, Jet.c, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hs
  unfold colLo colHi
  omega
private def rowIndex (q u : ℕ) :
    ↥(blockRows 46 q ((u : ℤ)-18)) → Row q u
  | ⟨⟨c,d,h⟩, hr⟩ =>
    let H := row_bounds q u c d h hr
    ⟨⟨h,H.1⟩, ⟨d-rowLo q u h, by
      change d - rowLo q u h < rowHi q u h - rowLo q u h
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private def colIndex (q u : ℕ) :
    ↥(blockCols source180120 q ((u : ℤ)-18)) → Col q u
  | ⟨⟨c,b,a⟩, hs⟩ =>
    let H := col_bounds q u c b a hs
    ⟨⟨b,H.1⟩, ⟨c-colLo u b, by
      change c - colLo u b < colHi q b - colLo u b
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private theorem rowJet_index (q u : ℕ) (r : ↥(blockRows 46 q ((u : ℤ)-18))) :
    rowJet q u (rowIndex q u r) = r.val := by
  rcases r with ⟨⟨c,d,h⟩,hr⟩
  obtain ⟨_, hlo, _, hc⟩ := row_bounds q u c d h hr
  change (⟨q-(h+(rowLo q u h+(d-rowLo q u h))),rowLo q u h+(d-rowLo q u h),h⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, hc]
private theorem colJet_index (q u : ℕ) (s : ↥(blockCols source180120 q ((u : ℤ)-18))) :
    colJet q u (colIndex q u s) = s.val := by
  rcases s with ⟨⟨c,b,a⟩,hs⟩
  obtain ⟨_, hlo, _, ha⟩ := col_bounds q u c b a hs
  change (⟨colLo u b+(c-colLo u b),b,q-(b+(colLo u b+(c-colLo u b)))⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, ha]
theorem block_rank_le (q u : ℕ) :
    (blockMatrix source180120 q ((u : ℤ)-18)).rank ≤ (packet q u).rank := by
  have he : blockMatrix source180120 q ((u : ℤ)-18) =
      (packet q u).submatrix (rowIndex q u) (colIndex q u) := by
    ext r s
    change CJ0.blockEntry r.val s.val =
      CJ0.blockEntry (rowJet q u (rowIndex q u r)) (colJet q u (colIndex q u s))
    exact congrArg₂ CJ0.blockEntry (rowJet_index q u r).symm (colJet_index q u s).symm
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _
theorem card_row (q u : ℕ) : Fintype.card (Row q u) = rows q u := by
  simp only [Row, Fintype.card_sigma, Fintype.card_fin, rows, total_eq_sum,
    Finset.sum_fin_eq_sum_range]
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
theorem card_col (q u : ℕ) : Fintype.card (Col q u) = cols q u := by
  simp only [Col, Fintype.card_sigma, Fintype.card_fin, cols, total_eq_sum,
    Finset.sum_fin_eq_sum_range]
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
theorem rank_le_nominal (q u : ℕ) : (packet q u).rank ≤ nominal q u := by
  exact le_min ((packet q u).rank_le_card_height.trans_eq (card_row q u))
    ((packet q u).rank_le_card_width.trans_eq (card_col q u))
theorem right_witness {F ρ κ : Type*} [Field F] [Fintype ρ] [Fintype κ]
    (M : Matrix ρ κ F) {d : ℕ} (V : Matrix κ (Fin d) F) (free : Fin d → κ)
    (hMV : M * V = 0) (hid : V.submatrix free id = 1) :
    M.rank + d ≤ Fintype.card κ := by
  have h := V.rank_submatrix_le free id
  rw [hid, Matrix.rank_one, Fintype.card_fin] at h
  exact (Nat.add_le_add_left h _).trans (Matrix.rank_add_rank_le_card_of_mul_eq_zero hMV)
end CJ1
end
section
namespace CJ6
def source : CJ0.Source := ⟨52, 71, 20, 9, CJ0.fullBox 71 20 9⟩
def At : Prop := CJ0.ScalarList 179983 7541063022938771
def Cert : Prop := CJ0.prefixRank source 72 ≤ 115565
end CJ6
end
section
namespace CJ6
open CJ1 (Block total entryZ)
def rowLo (q u h : ℕ) := u + 2*q + h + 1 - 72
def rowHi (q u h : ℕ) := min (q + 1 - h) (u + 2*q + h + 1 - 20)
def rowLen (q u h : ℕ) := rowHi q u h - rowLo q u h
def colLo (u b : ℕ) := (21 - (u+b)) / 2
def colHi (q b : ℕ) := min 10 (min (q-b+1) ((20-b)/2+1))
def colLen (q u b : ℕ) := colHi q b - colLo u b
abbrev Row (q u : ℕ) := (h : Fin (q+1)) × Fin (rowLen q u h)
abbrev Col (q u : ℕ) := (b : Fin (min q 20 + 1)) × Fin (colLen q u b)
def rowAt (q u h i : ℕ) : CJ0.Jet :=
  let d := rowLo q u h + i
  ⟨q - (h+d), d, h⟩
def rowJet (q u : ℕ) (r : Row q u) : CJ0.Jet := rowAt q u r.1 r.2
def colAt (q u b i : ℕ) : CJ0.Jet :=
  let c := colLo u b + i
  ⟨c, b, q - (b+c)⟩
def colJet (q u : ℕ) (s : Col q u) : CJ0.Jet := colAt q u s.1 s.2
def packet (q u : ℕ) : Matrix (Row q u) (Col q u) (ZMod CJ0.p) :=
  fun r s => CJ0.blockEntry (rowJet q u r) (colJet q u s)
def rows (q u : ℕ) := total (rowLen q u) (q+1)
def cols (q u : ℕ) := total (colLen q u) (min q 20 + 1)
def nominal (q u : ℕ) := min (rows q u) (cols q u)
def outer (onRows : Bool) (q : ℕ) := if onRows then q+1 else min q 20+1
def fiber (onRows : Bool) (q u : ℕ) := if onRows then rowLen q u else colLen q u
abbrev Axis (onRows : Bool) (q u : ℕ) :=
  (i : Fin (outer onRows q)) × Fin (fiber onRows q u i)
def orientedEntry (onRows : Bool) (q u i k b t : ℕ) : ℤ :=
  if onRows then entryZ (rowAt q u b t) (colAt q u i k)
  else entryZ (rowAt q u i k) (colAt q u b t)
def dot (q u : ℕ) (z : Block) (j i k : ℕ) : ℤ :=
  total (fun b => total (fun t =>
    let w := z.coeff j b t
    if w = 0 then 0 else orientedEntry z.bank.onRows q u i k b t * (w : ℤ))
    (fiber z.bank.onRows q u b)) (outer z.bank.onRows q)
def Dots (q u : ℕ) (z : Block) : Prop :=
  ∀ j < z.free.length, ∀ i < outer (!z.bank.onRows) q,
    ∀ k < fiber (!z.bank.onRows) q u i, dot q u z j i k % (CJ0.p : ℤ) = 0
def VectorDots (q u : ℕ) (z : Block) (j : ℕ) : Prop :=
  ∀ i < outer (!z.bank.onRows) q,
    ∀ k < fiber (!z.bank.onRows) q u i, dot q u z j i k % (CJ0.p : ℤ) = 0
abbrev Cell := ℕ × ℕ × ℕ
def Checks : List Cell → Prop
  | [] => True
  | (q,u,r)::xs => (CJ0.blockMatrix source q ((u : ℤ)-20)).rank ≤ r ∧ Checks xs
def boundIn (q u d : ℕ) : List Cell → ℕ
  | [] => d
  | (a,b,r)::xs => if q = a ∧ u = b then r else boundIn q u d xs
def rows0 : List Cell := [(35,17,109),(38,14,104)]
def rows1 : List Cell := [(36,16,108),(37,15,106),(38,15,99)]
def rows2 : List Cell := [(39,13,101),(39,14,98),(40,12,98),(40,13,96)]
def rows3 : List Cell := [(41,11,94),(41,12,94),(41,13,89),(42,11,91),(42,12,88)]
def rows4 : List Cell := [(43,10,88),(43,11,86),(44,10,84),(44,11,80)]
def rows5 : List Cell := [(45,9,81),(45,10,79),(46,9,77),(47,8,75),(47,9,71),(48,8,70)]
def rows6 : List Cell := [(49,7,68),(50,7,63),(51,6,61),(53,5,53),(54,5,48),(55,4,45),(56,4,40)]
def rows7 : List Cell := [(57,3,36),(57,4,35),(58,3,32),(59,2,27),(59,3,28),(60,2,24),(60,3,24),(61,1,18),(61,2,21)]
def rows8 : List Cell := [(62,1,16),(62,2,18),(63,0,9),(63,1,14),(63,2,15),(64,0,8),(64,1,12),(65,0,7),(65,1,10),(66,0,6),(66,1,8),(67,0,5),(68,0,4),(69,0,3)]
def cells (q : ℕ) :=
  if q < 35 then [] else
  if q ≤ 38 then rows0 ++ rows1 else
  if q ≤ 40 then rows2 else
  if q ≤ 42 then rows3 else
  if q ≤ 44 then rows4 else
  if q ≤ 48 then rows5 else
  if q ≤ 56 then rows6 else
  if q ≤ 61 then rows7 else
  rows8
def allowance (q u : ℕ) := boundIn q u (nominal q u) (cells q)
def grade (q : ℕ) := CJ1.total (allowance q) (72-q)
end CJ6
end
section
namespace K1_13_2_3_2
open K1_13_2 Finset
open scoped BigOperators
private theorem twice_half (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have h : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ x) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ x - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private def denPolynomial (q r : ℤ) : ℤ :=
  2 + r * (r + 1) + q * (44 + 14 * r + r * (r - 1)) +
    (57 + 6 * r) * (q * (q - 1)) + 12 * q * (q - 1) * (q - 2)
private theorem twice_den (u : ℤ) (h : 0 ≤ u) :
    2 * denominator u = denPolynomial (u / 6) (u % 6) := by
  let q := u / 6
  let r := u % 6
  simp only [denominator, not_lt.mpr h, ite_false, denPolynomial]
  change 2 * (1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)) = _
  have hr := twice_half (r + 1)
  rw [show (r + 1) * (r + 1 - 1) = r * (r + 1) by ring] at hr
  change _ = denPolynomial q r
  unfold denPolynomial
  linear_combination hr + q * twice_half r + (57 + 6 * r) * twice_half q
private def denPrefixPolynomial (q r : ℤ) : ℤ :=
  984 * q + 3084 * q * (q - 1) + 1728 * q * (q - 1) * (q - 2) +
    216 * q * (q - 1) * (q - 2) * (q - 3) + (24 * r + 4 * (r - 1) * r * (r + 1)) +
    q * (528 * r + 84 * (r - 1) * r + 4 * (r - 2) * (r - 1) * r) +
    (684 * r + 36 * (r - 1) * r) * q * (q - 1) + 144 * r * q * (q - 1) * (q - 2)
private def denPrefix (n : ℤ) : ℤ := denPrefixPolynomial (n / 6) (n % 6)
private theorem denPrefix_step (n : ℤ) (hn : 0 ≤ n) :
    denPrefix (n + 1) = denPrefix n + 24 * denominator n := by
  have hden := twice_den n hn
  have hq : (n + 1) / 6 = n / 6 + (n % 6 + 1) / 6 := by omega
  have hr : (n + 1) % 6 = (n % 6 + 1) % 6 := by omega
  have hlo : 0 ≤ n % 6 := by omega
  have hhi : n % 6 < 6 := by omega
  rw [denPrefix, denPrefix, hq, hr]
  generalize n % 6 = r at hden hlo hhi ⊢
  interval_cases r <;> norm_num [denPrefixPolynomial, denPolynomial] at hden ⊢ <;>
    linear_combination (norm := ring_nf) -12 * hden
theorem denPrefix_eq (n : ℕ) :
    24 * (∑ u ∈ range n, denominator (u : ℤ)) = denPrefix n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, Nat.cast_succ, denPrefix_step _ (by omega)]
private theorem sum_shift (f : ℤ → ℤ) (hz : ∀ x < 0, f x = 0) (n a : ℕ) :
    (∑ u ∈ range n, f ((u : ℤ) - a)) = ∑ u ∈ range (n - a), f (u : ℤ) := by
  have hzero (b : ℕ) (hb : b ≤ a) : (∑ u ∈ range b, f ((u : ℤ) - a)) = 0 := by
    exact sum_eq_zero fun u hu => hz _ (by have := mem_range.mp hu; omega)
  by_cases h : a ≤ n
  · conv_lhs => rw [← Nat.add_sub_of_le h, sum_range_add]
    rw [hzero a le_rfl, zero_add]
    apply sum_congr rfl
    intro u _
    congr 1
    push_cast
    ring
  · rw [hzero n (by omega), show n - a = 0 by omega, sum_range_zero]
theorem sum_shift_cumulative (d n a : ℕ) :
    (∑ u ∈ range n, cumulative (d : ℤ) ((u : ℤ) - a)) =
      ∑ u ∈ range (n - a), cumulative (d : ℤ) (u : ℤ) :=
  sum_shift _ (fun x hx => by simp [cumulative, hx]) n a
def cumulativePrefix (d n : ℕ) : ℤ :=
  denPrefix n - denPrefix (n - (d + 1) : ℕ) - denPrefix (n - (d + 2) : ℕ) -
    denPrefix (n - (d + 3) : ℕ) + denPrefix (n - (2 * d + 3) : ℕ) +
    denPrefix (n - (2 * d + 4) : ℕ) + denPrefix (n - (2 * d + 5) : ℕ) -
    denPrefix (n - (3 * d + 6) : ℕ)
theorem cumulative_expand (d u : ℕ) (hu : u ≤ 3 * d) :
    cumulative (d : ℤ) (u : ℤ) =
      denominator u - denominator ((u : ℤ) - (d + 1 : ℕ)) -
        denominator ((u : ℤ) - (d + 2 : ℕ)) - denominator ((u : ℤ) - (d + 3 : ℕ)) +
        denominator ((u : ℤ) - (2 * d + 3 : ℕ)) + denominator ((u : ℤ) - (2 * d + 4 : ℕ)) +
        denominator ((u : ℤ) - (2 * d + 5 : ℕ)) - denominator ((u : ℤ) - (3 * d + 6 : ℕ)) := by
  have hd : ¬ (d : ℤ) < 0 := by omega
  have hu₀ : ¬ (u : ℤ) < 0 := by omega
  simp [cumulative, hd, hu₀, min_eq_left (show (u : ℤ) ≤ 3 * (d : ℤ) by omega)]
  ring_nf
theorem prefix_eq (d n : ℕ) (hn : n ≤ 3 * d + 1) :
    24 * (∑ u ∈ range n, cumulative (d : ℤ) (u : ℤ)) = cumulativePrefix d n := by
  have hs (a : ℕ) : 24 * (∑ u ∈ range n, denominator ((u : ℤ) - a)) =
      denPrefix (n - a : ℕ) := by
    rw [sum_shift _ (fun x hx => by simp [denominator, hx]), denPrefix_eq]
  rw [sum_congr rfl (fun u hu => cumulative_expand d u (by have := mem_range.mp hu; omega))]
  simp only [cumulativePrefix, sum_sub_distrib, sum_add_distrib, mul_sub, mul_add, hs, denPrefix_eq]
end K1_13_2_3_2
end
