import ProximityPrize.SubmissionLower.Fast015
import ProximityPrize.SubmissionLower.Fast022 -- serialize candidate build
set_option autoImplicit true
section
namespace CJ0
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
abbrev K := FrobeniusLocator.Native.K
abbrev Node := FrobeniusLocator.Native.I
abbrev node := ProximityPrize.Benchmark.IRSProfile.domain
abbrev p : ℕ := 2130706433
abbrev n : ℕ := 262144
abbrev k : ℕ := 131072
abbrev N : ℕ := 131071
abbrev Jet := Sigma fun _ : ℕ => Sigma fun _ : ℕ => ℕ
def Jet.a (j : Jet) : ℕ := j.2.2
def Jet.b (j : Jet) : ℕ := j.2.1
def Jet.c (j : Jet) : ℕ := j.1
def Jet.q (j : Jet) : ℕ := j.a + j.b + j.c
def Jet.v (j : Jet) : ℕ := j.b + 2 * j.c
structure Source where
  m : ℕ
  B : ℕ
  J : ℕ
  C : ℕ
  E : Finset Jet
def fullBox (B J C : ℕ) : Finset Jet :=
  (Finset.range (C + 1)).sigma fun c =>
    (Finset.range (J - 2*c + 1)).sigma fun b => Finset.range (B - (b+c) + 1)
structure ShapeOK (s : Source) : Prop where
  multiplicity : 0 < s.m
  top_pos : 0 < s.C
  index_top : 2*s.C ≤ s.J
  total_index : s.J ≤ s.B
  characteristic : max N (s.B*(s.B-1)) < p
  support : ∀ j ∈ s.E, j.q ≤ s.B ∧ j.v ≤ s.J ∧ j.c ≤ s.C
  lower : ∀ j ∈ s.E, 0 < j.a → (⟨j.c, j.b, j.a-1⟩ : Jet) ∈ s.E
def errors (A : ℕ) := n - A
def gap (A : ℕ) := A - N
structure AgreementOK (A : ℕ) : Prop where
  gt_degree : N < A
  lt_length : A < n
  one_le_beta : gap A ≤ errors A
  beta_lt_two : errors A < 2 * gap A
def width (A : ℕ) (s : Source) (j : Jet) := s.m*A - N*j.q + j.v
abbrev ColumnIndex (A : ℕ) (s : Source) := (j : s.E) × Fin (width A s j.val)
def column (A : ℕ) (s : Source) (i : ColumnIndex A s) : SourceColumn 2 :=
  ⟨i.2.val, i.1.val.a, ![i.1.val.b, i.1.val.c]⟩
def Surplus (A : ℕ) (s : Source) (R : ℕ) : Prop :=
  n*R + N*(∑ j ∈ s.E, j.q) < s.m*A*s.E.card + ∑ j ∈ s.E, j.v
def originRank (A : ℕ) (s : Source) : ℕ :=
  (localConstraintMatrix s.m (fun _ : Unit => (0 : ZMod p)) (fun _ => 0) (column A s)).rank
def stackRank (A : ℕ) (s : Source) (w : Node → K) : ℕ :=
  (localConstraintMatrix s.m (fun i => node i) w (column A s)).rank
def blockRows (m q : ℕ) (g : ℤ) : Finset Jet :=
  ((Finset.range (q+1)).sigma fun c =>
    (Finset.range (q-c+1)).sigma fun b => {q-(b+c)}).filter fun j : Jet =>
      0 ≤ g + (j.v : ℤ) + 3*(j.a : ℤ) ∧ g + (j.v : ℤ) + 3*(j.a : ℤ) < (m : ℤ)
def blockCols (s : Source) (q : ℕ) (g : ℤ) : Finset Jet :=
  s.E.filter fun j => j.q = q ∧ 0 ≤ g + (j.v : ℤ)
def blockEntry (row col : Jet) : ZMod p :=
  if col.b ≤ row.b ∧ col.c ≤ row.c ∧ row.a + (row.b-col.b) + (row.c-col.c) = col.a
  then (-1)^(row.c-col.c) * (col.a.choose row.a : ℕ) * ((col.a-row.a).choose (row.b-col.b) : ℕ)
  else 0
def blockMatrix (s : Source) (q : ℕ) (g : ℤ) :
    Matrix (blockRows s.m q g) (blockCols s q g) (ZMod p) :=
  fun r c => blockEntry r.val c.val
def prefixRank (s : Source) (cut : ℕ) : ℕ :=
  ∑ q ∈ Finset.range cut, ∑ u ∈ Finset.range (s.m+s.J-q),
    (blockMatrix s q ((u : ℤ) - s.J)).rank
def SilentTail (s : Source) (cut : ℕ) : Prop :=
  ∀ j ∈ s.E, cut ≤ j.q → s.m ≤ j.a
def RankCertificate (A : ℕ) (s : Source) (R : ℕ) : Prop :=
  originRank A s ≤ R ∨ ∃ cut ≤ s.B+1, SilentTail s cut ∧ prefixRank s cut ≤ R
def t : ℕ := max (2*k-7) (k-2)
def t₁ : ℕ := 2*k-5
def a₀ (s : Source) := 1 + t*(s.B-1)
def D (s : Source) := t*(s.J-2) + k-1
def e (s : Source) := min (t*(s.C-1) + k-2) (D s / 2)
def R₂ (s : Source) :=
  (s.C*D s + e s*s.J - 2*s.C*e s)*(2*a₀ s - D s) +
    e s*(D s-e s)*(2*s.B-s.J)
def H (s : Source) := max s.B ((2*s.C-1)*s.B - s.C^2)
def I₁ (s : Source) := max s.J ((2*s.C-1)*s.J - 2*s.C^2)
def a₁ (s : Source) := 1+t₁*(H s-1)
def d₁ (s : Source) := min (a₁ s) (t₁*(I₁ s-1)+k-1)
def R₁ (s : Source) := H s*d₁ s + I₁ s*a₁ s - I₁ s*d₁ s
def chargeNumerator (A : ℕ) (s : Source) :=
  errors A * (2*R₂ s + R₁ s) + gap A * (s.B + H s ^ 2)
def L (A : ℕ) (s : Source) := (chargeNumerator A s + (gap A-1)) / gap A
abbrev close (A : ℕ) (w : Node → K) := ReedSolomon.closePolynomialSet node w k A
def ScalarList (A cap : ℕ) : Prop :=
  ∀ w : Node → K, (close A w).Finite ∧ (close A w).ncard ≤ cap
def Main : Prop :=
  ∀ (A : ℕ) (s : Source) (R : ℕ), AgreementOK A → ShapeOK s →
    s.m ≤ s.m*A - N*s.B → Surplus A s R → RankCertificate A s R →
    ScalarList A (L A s)
def source180120 : Source := ⟨46, 63, 18, 8, fullBox 63 18 8⟩
def indexWeight {r : ℕ} : JetVariable r → ℕ := fun j => j.elim 0 Fin.val
def OrderTwo (s : Source) (Q : DifferentialPolynomial K 2) : Prop :=
  Q ≠ 0 ∧ jetTotalDegree Q ≤ s.B ∧ Q.weightedTotalDegree indexWeight ≤ s.J ∧
    jetDegree Q (Fin.last 2) ≤ s.C
def OrderOne (s : Source) (Q : DifferentialPolynomial K 1) : Prop :=
  Q ≠ 0 ∧ jetTotalDegree Q ≤ H s ∧ jetDegree Q (Fin.last 1) ≤ I₁ s
def RegularRoot {r : ℕ} (Q : DifferentialPolynomial K r) (f : K[X]) : Prop :=
  ∃ G : DifferentialPolynomial K r, Irreducible G ∧ G ∣ Q ∧
    differentialSpecialization G f = 0 ∧ differentialSpecialization (separant G (Fin.last r)) f ≠ 0
abbrev FX := FractionRing K[X]
abbrev Geo := AlgebraicClosure FX
abbrev CoeffRing := MvPolynomial (Fin k) Geo
abbrev InitialRing (r : ℕ) := MvPolynomial (Fin (r+1)) Geo
def embed : K →+* Geo :=
  (algebraMap FX Geo).comp ((algebraMap K[X] FX).comp Polynomial.C)
def center : Geo := algebraMap FX Geo (algebraMap K[X] FX Polynomial.X)
def coeffPoint (f : K[X]) (i : Fin k) : Geo := embed (f.coeff i.val)
def readJet (y : Fin k → Geo) (j : ℕ) : Geo :=
  ∑ i : Fin k, (i.val.choose j : Geo) * center^(i.val-j) * y i
structure Chart (r : ℕ) where
  equation : InitialRing r
  denominator : InitialRing r
  numerator : Fin k → InitialRing r
def Chart.locus {r} (T : Chart r) : Set (Fin (r+1) → Geo) :=
  {u | MvPolynomial.eval u T.equation = 0 ∧ MvPolynomial.eval u T.denominator ≠ 0}
def Chart.output {r} (T : Chart r) (u : Fin (r+1) → Geo) (i : Fin k) : Geo :=
  MvPolynomial.eval u (T.numerator i) / MvPolynomial.eval u T.denominator
def Chart.imageSet {r} (T : Chart r) := T.output '' T.locus
def Chart.ideal {r} (T : Chart r) : Ideal CoeffRing := MvPolynomial.vanishingIdeal Geo T.imageSet
structure ChartOK {r} (T : Chart r) : Prop where
  irreducible : Irreducible T.equation
  nonvanishing : ¬ T.equation ∣ T.denominator
  recover : ∀ u ∈ T.locus, ∀ j : Fin (r+1), readJet (T.output u) j.val = u j
structure Family (r : ℕ) where
  count : ℕ
  chart : Fin count → Chart r
def inBand₂ (s : Source) (P : InitialRing 2) : Prop :=
  P.totalDegree ≤ a₀ s ∧ P.weightedTotalDegree Fin.val ≤ D s ∧ P.degreeOf (Fin.last 2) ≤ e s
def inBand₁ (s : Source) (P : InitialRing 1) : Prop :=
  P.totalDegree ≤ a₁ s ∧ P.degreeOf (Fin.last 1) ≤ d₁ s
structure Family₂ (s : Source) (F : Family 2) : Prop where
  count : F.count ≤ s.B
  chart_ok : ∀ i, ChartOK (F.chart i)
  total : (∑ i, (F.chart i).equation.totalDegree) ≤ s.B
  index : (∑ i, (F.chart i).equation.weightedTotalDegree Fin.val) ≤ s.J
  top : (∑ i, (F.chart i).equation.degreeOf (Fin.last 2)) ≤ s.C
  bands : ∀ i, inBand₂ s (F.chart i).denominator ∧ ∀ j, inBand₂ s ((F.chart i).numerator j)
structure Family₁ (s : Source) (F : Family 1) : Prop where
  count : F.count ≤ H s
  chart_ok : ∀ i, ChartOK (F.chart i)
  total : (∑ i, (F.chart i).equation.totalDegree) ≤ H s
  index : (∑ i, (F.chart i).equation.degreeOf (Fin.last 1)) ≤ I₁ s
  bands : ∀ i, inBand₁ s (F.chart i).denominator ∧ ∀ j, inBand₁ s ((F.chart i).numerator j)
def CoversRegular {r} (F : Family r) (Q : DifferentialPolynomial K r) : Prop :=
  ∀ f : K[X], f.degree < k → RegularRoot Q f → ∃ i, coeffPoint f ∈ (F.chart i).imageSet
structure ImageDegrees {r} (F : Family r) (budget : ℕ) : Prop where
  prime : ∀ i, (F.chart i).ideal.IsPrime
  dimension : ∀ i, (MvPolynomial.affineHilbertPolynomial (F.chart i).ideal).natDegree = r
  total : (∑ i, MvPolynomial.affineDegree (F.chart i).ideal) ≤ (budget : ℚ)
end
end CJ0
end
section
namespace CJ0
noncomputable section
open Finset
open scoped BigOperators
theorem mem_fullBox {B J C : ℕ} (hBJ : J ≤ B) (hJC : 2*C ≤ J) (j : Jet) :
    j ∈ fullBox B J C ↔ j.q ≤ B ∧ j.v ≤ J ∧ j.c ≤ C := by
  rcases j with ⟨c, b, a⟩
  simp only [fullBox, mem_sigma, mem_range, Jet.q, Jet.v, Jet.c, Jet.b, Jet.a]
  omega
private def runLength (c b : ℕ) := 63 - (b+c) + 1
private def bRange (c : ℕ) := range (18 - 2*c + 1)
private def countRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b
private def totalRow (c : ℕ) := ∑ b ∈ bRange c,
  (runLength c b * (runLength c b - 1) / 2 + runLength c b * (b+c))
private def indexRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b * (b+2*c)
private theorem box_index : (∑ j ∈ source180120.E, j.v) = ∑ c ∈ range 9, indexRow c := by
  simp only [source180120, fullBox, sum_sigma, indexRow, bRange, runLength, Jet.v, Jet.b, Jet.c,
    sum_const, card_range, smul_eq_mul]
end
end CJ0
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P0
noncomputable section
open Polynomial Matrix CoreDefinitions Code
open FrobeniusLocator
open ProximityPrize.Benchmark
open scoped BigOperators NNReal
abbrev K := Native.K
abbrev I := Native.I
abbrev Words := Fin 2 → I → K
abbrev node := IRSProfile.domain
abbrev p := Native.p
abbrev blockLength : ℕ := 262144
abbrev k : ℕ := 131072
abbrev agreement : ℕ := 180217
abbrev t : ℕ := blockLength - agreement
abbrev L : ℕ := agreement - k
abbrev frontLimit : ℕ := 16
abbrev heightCap : ℕ := t + 1 - L - (frontLimit + 1)
abbrev lowCutoff : ℤ := 2480
abbrev radiusNumerator : ℕ := 335573291
abbrev radiusDenominator : ℕ := 1073741824
def queryRadius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator
def radius : ℝ := queryRadius
abbrev scalarCap : ℕ := 229652235871261455
abbrev listCap : ℕ := 31973440934878498
abbrev rankFee : ℕ := 69814727032823
abbrev anchorFee : ℕ := 69814727311356
def WeightedList : Prop :=
  ∀ word : I → K,
    let S := ReedSolomon.closePolynomialSet node word (k + 1) agreement
    S.Finite ∧ S.ncard ≤ listCap
abbrev Frac := GenericLayer.GenericField K
abbrev Bivar := Polynomial K[X]
def BadFamily (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius
structure BadMark (u : Words) (γ : K) where
  support : Finset I
  decoder : K[X]
  agreement : P0.agreement ≤ support.card
  degree : decoder.degree < k
  hits : ∀ i ∈ support, decoder.eval (node i) = u 0 i + γ * u 1 i
  nonjoint : ¬ (ExtendsOn node (u 0) k support ∧ ExtendsOn node (u 1) k support)
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
def TypeAtMostOne (u : Words) : Prop :=
  Principal.TypeOneSyndromes node (u 0) (u 1) k p
def HomogeneousPrincipal (u : Words) : Prop :=
  ∃ (a : ℕ) (g : Frac[X]), g ≠ 0 ∧ g.natDegree ≤ a ∧ a ≤ t ∧
    ∀ P : Frac[X], P.natDegree ≤ t →
      (((twoBlock u).map (algebraMap K[X] Frac)).mulVec (fun i => P.coeff i.val) = 0 ↔
        ∃ Q : Frac[X], Q.natDegree ≤ t - a ∧ P = g * Q)
def coefficientBlocks {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (l t : ℕ) : Matrix (Fin 4 × Fin l) (Fin (t + 1)) F :=
  fun i j =>
    if i.1 = 0 then syndrome x u (i.2.val + j.val) else
    if i.1 = 1 then syndrome x v (i.2.val + j.val) else
    if i.1 = 2 then syndrome x u (i.2.val + j.val) ^ p else
      syndrome x v (i.2.val + j.val) ^ p
abbrev coefficientStack (u : Words) := coefficientBlocks p node (u 0) (u 1) L t
def ConstantKernel (u : Words) : Prop :=
  stackRank u = (coefficientStack u).rank
def FrontRemainder (u : Words) : Prop :=
  frontLimit < nullity u ∧ firstRank u = L ∧ ¬ TypeAtMostOne u ∧
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
def extendSeed (U : Bivar) : Frac[X] :=
  U.map (algebraMap K[X] Frac)
def IsCommonGCD {F : Type} [Field F] (G U V : F[X]) : Prop :=
  G ≠ 0 ∧ G ∣ U ∧ G ∣ V ∧ ∀ H : F[X], H ∣ U → H ∣ V → H ∣ G
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
def atSlope (P : Bivar) (γ : K) : K[X] := P.map (evalRingHom γ)
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
def seed : Bivar := Polynomial.C (R := K[X]) (Polynomial.X (R := K))
def liftX (P : K[X]) : Bivar := P.map Polynomial.C
def twist : K →+* K := frobenius K p
def amplitudeDegree (a₀ a₁ : K[X]) : ℕ := max a₀.natDegree a₁.natDegree
def sixNorm (a : K[X]) : K[X] :=
  ∏ j : Fin 6, a.map (iterateFrobenius K p j.val)
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
def columnRank (U V : Bivar) : ℕ :=
  Module.finrank Frac (Submodule.span Frac (Set.range fun j : Fin 4 =>
    extendSeed (Polynomial.Bivariate.swap
      (if j = 0 then U else if j = 1 then seed * U else if j = 2 then V else seed ^ p * V))))
def _root_.P0_4.columnRankAt (q : ℕ) (U V : Bivar) : ℕ :=
  Module.finrank Frac (Submodule.span Frac (Set.range fun j : Fin 4 =>
    extendSeed (Polynomial.Bivariate.swap
      (if j = 0 then U else if j = 1 then seed * U else if j = 2 then V else seed ^ q * V))))
def threeU (a : K[X]) (β : Fin 2 → K[X]) : Bivar :=
  liftX a * (liftX ((β 0).map twist) + seed ^ p * liftX ((β 1).map twist))
def _root_.P0_4.threeUAt (q : ℕ) (a : K[X]) (β : Fin 2 → K[X]) : Bivar :=
  liftX a * (liftX ((β 0).map twist) + seed ^ q * liftX ((β 1).map twist))
def _root_.P0_5.threeUAt (q : ℕ) (a : K[X]) (β : Fin 2 → K[X]) : Bivar :=
  liftX a * (liftX ((β 0).map twist) + seed ^ q * liftX ((β 1).map twist))
def threeV (b : K[X]) (α : Fin 2 → K[X]) : Bivar :=
  -(liftX b * (liftX (α 0) + seed * liftX (α 1)))
def sameDirection (U V U' V' : Bivar) : Prop := U * V' = V * U'
def relationOn (u : Words) (deleted : Finset I) (U V output : Bivar) : Prop :=
  ∀ i ∉ deleted,
    U.eval (C (node i)) * (C (u 0 i) + Polynomial.X (R := K) * C (u 1 i)) +
    V.eval (C (node i)) * (C (u 0 i ^ p) + Polynomial.X (R := K) ^ p * C (u 1 i ^ p)) =
      output.eval (C (node i))
def _root_.P0_4.relationOnAt (q : ℕ) (u : Words) (deleted : Finset I) (U V output : Bivar) : Prop :=
  ∀ i ∉ deleted,
    U.eval (C (node i)) * (C (u 0 i) + Polynomial.X (R := K) * C (u 1 i)) +
    V.eval (C (node i)) * (C (u 0 i ^ q) + Polynomial.X (R := K) ^ q * C (u 1 i ^ q)) =
      output.eval (C (node i))
def _root_.P0_5.relationOnAt (q : ℕ) (u : Words) (deleted : Finset I) (U V output : Bivar) : Prop :=
  ∀ i ∉ deleted,
    U.eval (C (node i)) * (C (u 0 i) + Polynomial.X (R := K) * C (u 1 i)) +
    V.eval (C (node i)) * (C (u 0 i ^ q) + Polynomial.X (R := K) ^ q * C (u 1 i ^ q)) =
      output.eval (C (node i))
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
structure AnchorModel (u : Words) (deleted : Finset I) where
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
  height_bound : E.natDegree + amplitudeDegree A₀ A₁ ≤ heightCap
  first_word : ∀ i ∉ deleted,
    E.eval (node i) * (u 0 i + shift * u 1 i - pencil₀.eval (node i)) =
      factor.eval (node i) * A₀.eval (node i) * word i
  second_word : ∀ i ∉ deleted,
    E.eval (node i) * (u 1 i - pencil₁.eval (node i)) =
      Q.eval (node i) + factor.eval (node i) * A₁.eval (node i) * word i
def AnchorModel.overhead {u deleted} (M : AnchorModel u deleted) : ℤ :=
  (M.E.natDegree : ℤ) - M.factor.natDegree - amplitudeDegree M.A₀ M.A₁
def AnchorModel.label {u deleted} (M : AnchorModel u deleted) (γ : K) : K :=
  γ - M.shift
def AnchorModel.amplitude {u deleted} (M : AnchorModel u deleted) (γ : K) : K[X] :=
  M.A₀ + Polynomial.C (M.label γ) * M.A₁
def AnchorModel.decoder {u deleted} (M : AnchorModel u deleted) {γ : K}
    (B : BadMark u γ) : K[X] :=
  B.decoder - M.pencil₀ - Polynomial.C (M.label γ) * M.pencil₁
structure AnchorMark {u deleted} (M : AnchorModel u deleted) (γ : K) (S : K[X]) where
  bad : BadMark u γ
  avoids_deleted : Disjoint bad.support deleted
  scalar_fixed : S.map twist = S
  scalar_degree : S = 0 ∨ (S.natDegree : ℤ) ≤ (k : ℤ) - 1 + M.overhead
  scalar_hits : ∀ i ∈ bad.support, S.eval (node i) = M.word i
  pole_unit : IsCoprime (M.amplitude γ) M.E
  identity : M.E * M.decoder bad - Polynomial.C (M.label γ) * M.Q =
    M.factor * M.amplitude γ * S
structure AnchoredFamily {u deleted} (M : AnchorModel u deleted) (Γ : Finset K) where
  scalar : K → K[X]
  mark : ∀ γ ∈ Γ, AnchorMark M γ (scalar γ)
  distinct : Set.InjOn scalar (Γ : Set K)
def highPrefix (w : ℤ) : ℕ :=
  if w ≤ 3554 then 72330561486509196
  else if w ≤ 8249 then 83625638374831363
  else if w ≤ 23999 then 88272853155571659
  else 94479354514532614
def highRetained (w : ℤ) : ℕ :=
  if w ≤ 3554 then 147341630862505162
  else if w ≤ 8249 then 43002915371002194
  else if w ≤ 23999 then 26524108968507199
  else 39471880490774732
end
end P0
end
section
set_option maxRecDepth 12000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
namespace P0
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem
open FrobeniusLocator ProximityPrize.Benchmark
open Sol1.OneCount Sol1.FiniteRowProjection
open scoped NNReal
theorem support_threshold :
    (Fintype.card I : ℝ) * (1 - radius) = (738168533 : ℝ) / 4096 := by
  rw [IRSProfile.card_index]
  norm_num [radius, queryRadius, claimedRadius]
theorem agreement_of_threshold {s : ℕ}
    (hs : (Fintype.card I : ℝ) * (1 - radius) ≤ s) : agreement ≤ s := by
  rw [support_threshold] at hs
  have hlt : (180216 : ℝ) < (738168533 : ℝ) / 4096 := by norm_num
  have hn : 180216 < s := by exact_mod_cast hlt.trans_le hs
  exact hn
theorem bad_slope (u : Words) (γ : K)
    (hγ : IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius) :
    Principal.BadSlope node (u 0) (u 1) k agreement γ := by
  let : NeZero k := ⟨by decide⟩
  exact Principal.isMCA_implies_badSlope node u k agreement radius
    (fun _ hT => agreement_of_threshold hT) γ hγ
theorem bad_mark (u : Words) (Γ : Finset K) (hΓ : BadFamily u Γ) (γ : K) (hγ : γ ∈ Γ) :
    Nonempty (BadMark u γ) := by
  obtain ⟨S, hS, ⟨P, hP, he⟩, hn⟩ := bad_slope u γ (hΓ γ hγ)
  exact ⟨⟨S, P, hS, hP, he, hn⟩⟩
private theorem dyadic_mul {a i j x y u v z w e s : ℕ}
    (hi : a ^ i ≤ x * 2 ^ u) (hj : a ^ j ≤ y * 2 ^ v)
    (hc : x * y ≤ z * 2 ^ w) (he : i + j = e) (hs : u + v + w = s) :
    a ^ e ≤ z * 2 ^ s := by
  subst e
  subst s
  calc
    a ^ (i + j) = a ^ i * a ^ j := pow_add ..
    _ ≤ (x * 2 ^ u) * (y * 2 ^ v) := Nat.mul_le_mul hi hj
    _ = (x * y) * 2 ^ (u + v) := by rw [pow_add]; ac_rfl
    _ ≤ (z * 2 ^ w) * 2 ^ (u + v) := Nat.mul_le_mul_right _ hc
    _ = z * (2 ^ (u + v) * 2 ^ w) := by ac_rfl
    _ = z * 2 ^ (u + v + w) := congrArg (z * ·) (pow_add (2 : ℕ) (u + v) w).symm
theorem complement_pow_1600 : (738168533 : ℕ) ^ 1600 ≤ 2 ^ 47135 := by
  have h1 : (738168533 : ℕ) ^ 1 ≤ 738168533 * 2 ^ 0 := by decide
  have h2 : (738168533 : ℕ) ^ 2 ≤ 0x78fd9196a06fd39 * 2 ^ 0 :=
    dyadic_mul h1 h1 (z := 0x78fd9196a06fd39) (w := 0) (e := 2)
      (s := 0) (by decide) (by decide) (by decide)
  have h4 : (738168533 : ℕ) ^ 4 ≤ 0xe4bace9933b7b70 * 2 ^ 58 :=
    dyadic_mul h2 h2 (z := 0xe4bace9933b7b70) (w := 58) (e := 4)
      (s := 58) (by decide) (by decide) (by decide)
  have h8 : (738168533 : ℕ) ^ 8 ≤ 0xcc5d4851c1794fe * 2 ^ 176 :=
    dyadic_mul h4 h4 (z := 0xcc5d4851c1794fe) (w := 60) (e := 8)
      (s := 176) (by decide) (by decide) (by decide)
  have h16 : (738168533 : ℕ) ^ 16 ≤ 0xa324cd3fec2e007 * 2 ^ 412 :=
    dyadic_mul h8 h8 (z := 0xa324cd3fec2e007) (w := 60) (e := 16)
      (s := 412) (by decide) (by decide) (by decide)
  have h24 : (738168533 : ℕ) ^ 24 ≤ 0x823cc603f4186ec * 2 ^ 648 :=
    dyadic_mul h16 h8 (z := 0x823cc603f4186ec) (w := 60) (e := 24)
      (s := 648) (by decide) (by decide) (by decide)
  have h25 : (738168533 : ℕ) ^ 25 ≤ 0xb311c3afd2b98d1 * 2 ^ 677 :=
    dyadic_mul h24 h1 (z := 0xb311c3afd2b98d1) (w := 29) (e := 25)
      (s := 677) (by decide) (by decide) (by decide)
  have h50 : (738168533 : ℕ) ^ 50 ≤ 0xfa83b1c6e73d977 * 2 ^ 1413 :=
    dyadic_mul h25 h25 (z := 0xfa83b1c6e73d977) (w := 59) (e := 50)
      (s := 1413) (by decide) (by decide) (by decide)
  have h100 : (738168533 : ℕ) ^ 100 ≤ 0xf5257af7e8a99b2 * 2 ^ 2886 :=
    dyadic_mul h50 h50 (z := 0xf5257af7e8a99b2) (w := 60) (e := 100)
      (s := 2886) (by decide) (by decide) (by decide)
  have h200 : (738168533 : ℕ) ^ 200 ≤ 0xeac0c2db4a0f1dd * 2 ^ 5832 :=
    dyadic_mul h100 h100 (z := 0xeac0c2db4a0f1dd) (w := 60) (e := 200)
      (s := 5832) (by decide) (by decide) (by decide)
  have h400 : (738168533 : ℕ) ^ 400 ≤ 0xd744f55dc0a3d15 * 2 ^ 11724 :=
    dyadic_mul h200 h200 (z := 0xd744f55dc0a3d15) (w := 60) (e := 400)
      (s := 11724) (by decide) (by decide) (by decide)
  have h800 : (738168533 : ℕ) ^ 800 ≤ 0xb504e6b6be8e15b * 2 ^ 23508 :=
    dyadic_mul h400 h400 (z := 0xb504e6b6be8e15b) (w := 60) (e := 800)
      (s := 23508) (by decide) (by decide) (by decide)
  have h1600 : (738168533 : ℕ) ^ 1600 ≤ 0xffffdcacde2f7ff * 2 ^ 47075 :=
    dyadic_mul h800 h800 (z := 0xffffdcacde2f7ff) (w := 59) (e := 1600)
      (s := 47075) (by decide) (by decide) (by decide)
  refine h1600.trans ?_
  calc
    0xffffdcacde2f7ff * 2 ^ 47075 ≤ 2 ^ 60 * 2 ^ 47075 :=
      Nat.mul_le_mul_right _ (by decide)
    _ = 2 ^ (60 + 47075) := (pow_add (2 : ℕ) 60 47075).symm
    _ = 2 ^ 47135 := congrArg (fun e : ℕ => (2 : ℕ) ^ e) (by decide)
theorem score_integer_cross :
    (738168533 : ℕ) ^ 12800 * 2 ^ 6920 ≤ 1073741824 ^ 12800 := by
  calc
    (738168533 : ℕ) ^ 12800 * 2 ^ 6920 = (738168533 ^ 1600) ^ 8 * 2 ^ 6920 := by
      rw [← pow_mul]
    _ ≤ ((2 : ℕ) ^ 47135) ^ 8 * 2 ^ 6920 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left complement_pow_1600 8)
    _ = (2 ^ 30) ^ 12800 := by
      simp only [← pow_mul, ← pow_add]
    _ = 1073741824 ^ 12800 := congrArg (fun b : ℕ => b ^ 12800) (by decide)
theorem query_score : (1 - queryRadius) ^ IRSProfile.repetitions ≤ claimedError 6920 := by
  have hcomplement : (1 - queryRadius : ℝ≥0) = 738168533 / 1073741824 := by
    apply NNReal.coe_injective
    have hr : queryRadius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [queryRadius, claimedRadius]
    rw [NNReal.coe_sub hr]
    norm_num [queryRadius, claimedRadius]
  change (1 - queryRadius) ^ 128 ≤ claimedError 6920
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (100 : ℕ) ≠ 0)).mp
  rw [← pow_mul, Sol1.C42.claimedError_pow_100, hcomplement]
  change ((738168533 : ℝ≥0) / 1073741824) ^ 12800 ≤ 1 / (2 : ℝ≥0) ^ 6920
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast score_integer_cross
theorem query_admissible : queryRadius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [queryRadius, claimedRadius, IRSProfile.minRelativeDistance]
theorem finset_scalar_list_card_le (hlist : WeightedList) (w : I → K) (P : Finset (I → K))
    (hP : ∀ f ∈ P, f ∈ scalarCode ∧ agreement ≤ agreementCard f w) : P.card ≤ listCap := by
  classical
  have : NeZero (k : ℕ) := ⟨by norm_num⟩
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
      ReedSolomon.closePolynomialSet node w (k + 1) agreement := by
    intro q hq
    obtain ⟨f,_hf,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨?_, ?_⟩
    · have hd : (poly f).natDegree < (k + 1) := (hdegree f).trans (by norm_num)
      exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast hd)
    · refine (hP f.val f.property).2.trans (Finset.card_le_card ?_)
      intro i hi
      apply (ReedSolomon.mem_polynomialAgreementSet node w (poly f) i).mpr
      have hfw : f.val i = w i := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
      exact (heval f i).trans hfw
  obtain ⟨hfinite,hbound⟩ := hlist w
  have hcount := (Set.ncard_le_ncard hpolys hfinite).trans hbound
  have hcount' : polys.card ≤ listCap := by simpa only [Set.ncard_coe_finset] using hcount
  rwa [hpolyscard] at hcount'
theorem list_projection_room : (listCap + 1) ^ 2 ≤ Fintype.card K :=
  projection_room listCap (by decide)
theorem finset_squared_list_card_le (hlist : WeightedList) (w : I → A16) (P : Finset (I → A16))
    (hP : ∀ f ∈ P, f ∈ squaredCode ∧ agreement ≤ agreementCard f w) : P.card ≤ listCap := by
  classical
  let flattened := P.image flatten
  have hflat : ∀ f ∈ flattened,
      (∀ r : R16, (fun i ↦ f i r) ∈ scalarCode) ∧
        agreement ≤ agreementCard f (flatten w) := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hcode,hagree⟩ := hP g hg
    exact ⟨flatten_rows_mem g hcode,hagree.trans (flatten_agreement_le g w)⟩
  have hcount := finset_vector_list_card_le scalarCode agreement listCap list_projection_room
    (finset_scalar_list_card_le hlist) (flatten w) flattened hflat
  have hcard : flattened.card = P.card := Finset.card_image_of_injective P flatten_injective
  rwa [hcard] at hcount
theorem close_agreement_ge (f w : I → A16)
    (hd : (δᵣ(w,f) : ℝ) ≤ radius) : agreement ≤ agreementCard f w := by
  classical
  have hpos : 0 < Fintype.card I := by rw [IRSProfile.card_index]; decide
  have hposR : (0 : ℝ) < Fintype.card I := by exact_mod_cast hpos
  have hradius : radius =
      1 - ((Fintype.card I : ℝ) * (1 - radius)) / Fintype.card I := by
    rw [mul_comm, mul_div_cancel_right₀ _ hposR.ne']
    ring
  have hagree := (Code.relHammingDist_le_one_sub_div_iff hpos).mp
    (show (δᵣ(w,f) : ℝ) ≤ 1 - ((Fintype.card I : ℝ) * (1 - radius)) / Fintype.card I by
      rwa [← hradius])
  have hcard : Code.agree f w ≤ agreementCard f w := by
    unfold Code.agree agreementCard
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi
  exact (agreement_of_threshold hagree).trans hcard
theorem squared_lambda_le (hlist : WeightedList) :
    Code.Lambda (squaredCode : Set (I → A16)) radius ≤ (listCap : ℕ∞) := by
  classical
  apply Code.Lambda_le_iff_forall_encard_le.mpr
  intro w
  have hfinite : (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius).Finite :=
    Set.toFinite _
  have hcard : hfinite.toFinset.card ≤ listCap := by
    apply finset_squared_list_card_le hlist w hfinite.toFinset
    intro f hf
    obtain ⟨hcode,hclose⟩ := Code.mem_closeCodewordsRel_iff.mp (hfinite.mem_toFinset.mp hf)
    exact ⟨hcode,close_agreement_ge f w hclose⟩
  calc
    (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius).encard =
        (hfinite.toFinset.card : ℕ∞) := hfinite.encard_eq_coe_toFinset_card
    _ ≤ (listCap : ℕ∞) := by exact_mod_cast hcard
def nativeBadSlopes (U : Sol1.C64.NativePair) : Finset K := by
  classical
  exact Finset.univ.filter fun γ => IsMCA (AffineLineGenerator K) IRSProfile.code γ U radius
theorem native_cap_of_scalar_cap
    (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) (U : Sol1.C64.NativePair) :
    (nativeBadSlopes U).card ≤ scalarCap := by
  classical
  apply Sol1.C64.restricted_interleaved_card_le IRSProfile.baseCode
    (⊤ : ModuleCode I K K) radius scalarCap
    (by rw [Sol1.C64.native_field_card]; decide)
    (fun u _ Γ hΓ => hscalar u Γ hΓ) U (by simp) (nativeBadSlopes U)
  intro γ hγ
  change γ ∈ Finset.univ.filter (fun z => IsMCA (AffineLineGenerator K)
    IRSProfile.code z U radius) at hγ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
  rw [Sol1.C64.native_code_eq] at hγ
  exact hγ
theorem mca_error_le_of_scalar_cap (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) :
    mcaError (AffineLineGenerator K) IRSProfile.code radius ≤
      (scalarCap : ENNReal) / (Fintype.card K : ENNReal) := by
  classical
  refine iSup_le fun U => ?_
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  change ENNReal.ofReal (((nativeBadSlopes U).card : ℝ) / Fintype.card K) ≤ _
  calc
    _ ≤ ENNReal.ofReal ((scalarCap : ℝ) / Fintype.card K) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right (by exact_mod_cast native_cap_of_scalar_cap hscalar U)
        (by positivity)
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]
private theorem error_budget :
    (scalarCap + listCap) * 2 ^ 128 ≤ (2130706433 : ℕ) ^ 6 := by decide
theorem gamma_error_le_of_scalar_cap (hlist : WeightedList)
    (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) :
    ToyProblem.certifiedGammaError IRSProfile.code queryRadius ≤ reductionTarget := by
  have hNat := ENat.toNat_le_of_le_natCast (squared_lambda_le hlist)
  have hList :
      ((Code.Lambda (squaredCode : Set (I → A16)) radius).toNat : ENNReal) /
        (Fintype.card K : ENNReal) ≤ (listCap : ENNReal) / Fintype.card K :=
    ENNReal.div_le_div_right (by exact_mod_cast hNat) _
  have hreal : ((scalarCap + listCap : ℕ) : ℝ) / Fintype.card K ≤ (1 : ℝ) / 2 ^ 128 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    norm_num only [one_mul]
    exact_mod_cast (Sol1.C64.native_field_card ▸ error_budget :
      (scalarCap + listCap) * 2 ^ 128 ≤ Fintype.card K)
  have hENN : ((scalarCap + listCap : ℕ) : ENNReal) / Fintype.card K ≤
      (1 : ENNReal) / 2 ^ 128 := by
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, ENNReal.ofReal_div_of_pos (by positivity)] at h
    simpa using h
  rw [← ENNReal.coe_le_coe, ToyProblem.coe_certifiedGammaError]
  calc
    _ ≤ (scalarCap : ENNReal) / Fintype.card K + (listCap : ENNReal) / Fintype.card K :=
      add_le_add (mca_error_le_of_scalar_cap hscalar) hList
    _ = ((scalarCap + listCap : ℕ) : ENNReal) / Fintype.card K := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ 128 := hENN
    _ = (reductionTarget : ENNReal) := by
      norm_num [reductionTarget, ProximityGap.prizeThreshold]
theorem protocol_claim_of_scalar_cap (hlist : WeightedList)
    (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) :
    ProtocolClaim 6920 radiusNumerator radiusDenominator where
  admissible := query_admissible
  reduction := gamma_error_le_of_scalar_cap hlist hscalar
  score := query_score
end
end P0
end
