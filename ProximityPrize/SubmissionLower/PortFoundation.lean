import ProximityPrize.SubmissionLower.Fast015
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
abbrev Frac := GenericLayer.GenericField K
abbrev Bivar := Polynomial K[X]
structure BadMark (u : Words) (γ : K) where
  support : Finset I
  decoder : K[X]
  agreement : P0.agreement ≤ support.card
  degree : decoder.degree < k
  hits : ∀ i ∈ support, decoder.eval (node i) = u 0 i + γ * u 1 i
  nonjoint : ¬ (ExtendsOn node (u 0) k support ∧ ExtendsOn node (u 1) k support)
def ordinary (u : Words) := hankel node (u 0) (u 1) L t
def twoBlock (u : Words) := stacked p node (u 0) (u 1) L t
def stackRank (u : Words) := GenericLayer.genericRank (twoBlock u)
def nullity (u : Words) := GenericLayer.genericNullity (twoBlock u)
def Normal (u : Words) (γ : K) : Prop :=
  ((twoBlock u).map (evalRingHom γ)).rank = stackRank u
def TypeAtMostOne (u : Words) : Prop :=
  Principal.TypeOneSyndromes node (u 0) (u 1) k p
def coefficientBlocks {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (l t : ℕ) : Matrix (Fin 4 × Fin l) (Fin (t + 1)) F :=
  fun i j =>
    if i.1 = 0 then syndrome x u (i.2.val + j.val) else
    if i.1 = 1 then syndrome x v (i.2.val + j.val) else
    if i.1 = 2 then syndrome x u (i.2.val + j.val) ^ p else
      syndrome x v (i.2.val + j.val) ^ p
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
end
end P0
end
