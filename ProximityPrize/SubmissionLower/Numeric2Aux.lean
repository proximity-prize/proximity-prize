import ProximityPrize.SubmissionLower.Fast022
import ProximityPrize.SubmissionLower.PortFoundation
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
abbrev t : ℕ := blockLength - agreement
abbrev L : ℕ := agreement - k
abbrev heightCap : ℕ := t + 1 - L - 2
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
abbrev AnchoredFamily {u deleted} (M : AnchorModel u deleted) := FamilyAt agreement M
abbrev AnchorModel.overhead {u deleted} (M : AnchorModel u deleted) := ModelAt.overhead M
abbrev AnchorModel.label {u deleted} (M : AnchorModel u deleted) := ModelAt.label M
abbrev AnchorModel.amplitude {u deleted} (M : AnchorModel u deleted) := ModelAt.amplitude M
abbrev AnchorModel.decoder {u deleted} (M : AnchorModel u deleted) {γ : K} (B : BadMark u γ) :=
  ModelAt.decoder M B
def listSource : CJ0.Source := ⟨53,72,21,10, CJ0.fullBox 72 21 10⟩
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
end CJ1
end
section
namespace CJ1
def total {α : Type*} [AddMonoid α] (f : ℕ → α) : ℕ → α
  | 0 => 0
  | n + 1 => total f n + f n
def fastChoose (n k : ℕ) := n.descFactorial k / k.factorial
def entryZ (r c : CJ0.Jet) : ℤ :=
  if c.b ≤ r.b ∧ c.c ≤ r.c ∧ r.a + (r.b-c.b) + (r.c-c.c) = c.a then
    (-1 : ℤ)^(r.c-c.c) * (fastChoose c.a r.a : ℤ) * (fastChoose (c.a-r.a) (r.b-c.b) : ℤ)
  else 0
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
private theorem denPrefix_eq (n : ℕ) :
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
private theorem cumulative_expand (d u : ℕ) (hu : u ≤ 3 * d) :
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
