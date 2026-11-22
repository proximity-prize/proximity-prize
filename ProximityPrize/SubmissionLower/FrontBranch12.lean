import ProximityPrize.SubmissionLower.PortHighFinish
import ProximityPrize.SubmissionLower.RungSplit
set_option autoImplicit true
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P3
noncomputable section
open Polynomial Matrix CoreDefinitions Code FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators NNReal
export P0 (K I Words node p blockLength k Frac Bivar TypeAtMostOne coefficientBlocks
  extendSeed IsCommonGCD atSlope seed liftX twist amplitudeDegree sixNorm columnRank
  threeU threeV sameDirection relationOn)
abbrev Rung := P1.Rung
abbrev target : Rung := ⟨179983, 0x140f123d, 0x40000000, 2273, 0x3aa55b4097fdbda, 0x1aca8e8eb60a93⟩
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
  | h2274
  | h2294
  | h7773
def HighBand.row : HighBand → HighRow
  | .h2274 => ⟨2274, 2293, 0x124358a0ab6e5a0, 0x2859f4cc0c22fa4⟩
  | .h2294 => ⟨2294, 7772, 0x112e33dd5733643, 0x20ca3b555c8e27a⟩
  | .h7773 => ⟨7773, 33249, 0x27cb2464b9a7d, 0x10b6e3d18a24d⟩
end
end P3
end
section
set_option maxRecDepth 12000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
namespace P3
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem
open FrobeniusLocator ProximityPrize.Benchmark
open Sol1.OneCount Sol1.FiniteRowProjection
open scoped NNReal
open private dyadic_mul from ProximityPrize.SubmissionLower.PortFoundation
local notation "step!" left "," right "," mant "," shift "," power "," total =>
  dyadic_mul left right (z := mant) (w := shift) (e := power) (s := total) (by decide) (by decide) (by decide)
end
end P3
end
section
namespace P3
noncomputable section
open Polynomial
open K1_13 (Geom embed extend)
abbrev physicalDegree : ℕ := k - 1 + lowCutoff.toNat
structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧
    ∀ i ∈ T, (s γ).eval (node i) = w i
structure PoleData (Γ : Finset K) (s : K → K[X]) where
  H : Geom[X]
  monic : H.Monic
  small : 1 ≤ H.natDegree ∧ H.natDegree ≤ lowCutoff.toNat
  nodes : ∀ i, H.eval (embed (node i)) ≠ 0
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ k - 1 + H.natDegree
  z : K → Geom
  injective : Function.Injective z
  c : Geom[X]
  q : Geom[X]
  a₀ : Geom[X]
  a₁ : Geom[X]
  c_unit : IsCoprime c H
  q_unit : IsCoprime q H
  a₀_unit : IsCoprime a₀ H
  regular : ∀ γ ∈ Γ, IsCoprime (a₀ + C (z γ) * a₁) H
  residue : ∀ γ ∈ Γ, H ∣ c * (a₀ + C (z γ) * a₁) * extend (s γ) + C (z γ) * q
def asOldPole {Γ s} (P : PoleData Γ s) : K1_13.PoleData Γ s where
  H := P.H
  monic := P.monic
  small := ⟨P.small.1, P.small.2.trans (by decide)⟩
  nodes := P.nodes
  degree := P.degree
  z := P.z
  injective := P.injective
  c := P.c
  q := P.q
  a₀ := P.a₀
  a₁ := P.a₁
  c_unit := P.c_unit
  q_unit := P.q_unit
  a₀_unit := P.a₀_unit
  regular := P.regular
  residue := P.residue
end
end P3
end
section
namespace P3
noncomputable section
open Finset
open CJ0 (ShapeOK mem_fullBox Jet fullBox Surplus AgreementOK SilentTail)
open scoped BigOperators
private def runLength (c b : ℕ) := 71 - (b+c) + 1
private def bRange (c : ℕ) := range (20 - 2*c + 1)
private def countRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b
private def totalRow (c : ℕ) := ∑ b ∈ bRange c,
  (runLength c b * (runLength c b - 1) / 2 + runLength c b * (b+c))
private def indexRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b * (b+2*c)
local notation "mom!" c "," n "," q "," v => countRow c = n ∧ totalRow c = q ∧ indexRow c = v
private theorem r0 : mom! 0, 1302, 52346, 12250 := by decide
private theorem r1 : mom! 1, 1178, 47424, 12388 := by decide
private theorem r2 : mom! 2, 1054, 42483, 12240 := by decide
private theorem r3 : mom! 3, 930, 37525, 11810 := by decide
private theorem r4 : mom! 4, 806, 32552, 11102 := by decide
private theorem r5 : mom! 5, 682, 27566, 10120 := by decide
private theorem r6 : mom! 6, 558, 22569, 8868 := by decide
private theorem r7 : mom! 7, 434, 17563, 7350 := by decide
private theorem r8 : mom! 8, 310, 12550, 5570 := by decide
private theorem r9 : mom! 9, 186, 7532, 3532 := by decide
open private curve_johnson from ProximityPrize.SubmissionLower.RungSplit
end
end P3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
namespace P1_1
noncomputable section
open Polynomial Matrix FrobeniusLocator P1
open ProximityPrize.Benchmark
private theorem eval_atSlope (P : Bivar) (a γ : K) :
    (atSlope P γ).eval a = (P.eval (C a)).eval γ := by
  simpa only [atSlope, Polynomial.coe_evalRingHom, Polynomial.eval_C] using
    (Polynomial.eval_map_apply (Polynomial.evalRingHom γ) (C a) (p := P))
private theorem atSlope_constant (G : K[X]) (γ : K) :
    atSlope (G.map C) γ = G := by
  rw [atSlope, Polynomial.map_map]
  have h : (Polynomial.evalRingHom γ).comp C = RingHom.id K := by
    ext a
    simp
  rw [h, Polynomial.map_id]
private theorem commonGCD_of_roots (U V : K[X]) (hV : V ≠ 0) (S : Finset I)
    (hroots : ∀ i ∈ S, (GCDMonoid.gcd U V).eval (node i) = 0)
    (hcard : S.card = (GCDMonoid.gcd U V).natDegree) :
    IsCommonGCD (locator node S) U V := by
  have hG : GCDMonoid.gcd U V ≠ 0 := gcd_ne_zero_of_right hV
  have hdiv := Strata.locator_dvd_of_eval_zero node IRSProfile.domain.injective S _ hroots
  have hassoc := Polynomial.associated_of_dvd_of_natDegree_le hdiv hG
    (by rw [locator_natDegree, hcard])
  exact ⟨(locator_monic node S).ne_zero, hdiv.trans (gcd_dvd_left U V),
    hdiv.trans (gcd_dvd_right U V), fun H hHU hHV => (dvd_gcd hHU hHV).trans hassoc.dvd'⟩
private theorem lift_dvd_atSlope {P : Bivar} {G : K[X]} (γ : K) (h : G.map C ∣ P) :
    G ∣ atSlope P γ := by
  have h' := map_dvd (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) h
  change atSlope (G.map C) γ ∣ atSlope P γ at h'
  rwa [atSlope_constant] at h'
end
end P1_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace P1_2
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P0 (Words k amplitudeDegree)
open K1_9 (K I node twist pencil fold pencil_degree
  seedCoeff crossValue CoefficientIdentities sixNorm_mul sixNorm_ne_zero)
open private seedCoeff_degree from ProximityPrize.SubmissionLower.Fast068
open private coefficientsAt pow_eq_twist threeUAt_native relationOnAt_native from ProximityPrize.SubmissionLower.PortFrontA
abbrev heightBound : ℕ := P1.heightCap
structure PolarData (u : Words) where
  a : K[X]
  b : K[X]
  A : Fin 2 → K[X]
  Q : K → K → K[X]
  a_ne : a ≠ 0
  norms_ne : K1.sixNorm a ≠ K1.sixNorm b
  primitive : IsCoprime (A 0) (A 1)
  a_bound : a.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  b_bound : b.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  Q_degree : ∀ r s, (Q r s).degree < (k + heightBound : ℕ)
  nodes : ∀ r s i,
    (Q r s).eval (node i) =
      a.eval (node i) * twist ((pencil (A 0) (A 1) r).eval (node i)) * fold u s i -
      b.eval (node i) * (pencil (A 0) (A 1) s).eval (node i) * twist (fold u r i)
private theorem polarData_of_set {u : Words} (S : Finset I) (height : ℕ)
    (a b : K[X]) (A : Fin 2 → K[X]) (output : P0.Bivar)
    (hh : height + S.card ≤ heightBound)
    (hout : output.degree < (k + height : ℕ))
    (hfirst : a.natDegree + amplitudeDegree (A 0) (A 1) ≤ height)
    (hsecond : b.natDegree + amplitudeDegree (A 0) (A 1) ≤ height)
    (hane : a ≠ 0) (hn : K1.sixNorm a ≠ K1.sixNorm b) (hA : IsCoprime (A 0) (A 1))
    (hc : ∀ i ∉ S, CoefficientIdentities u a b A output i) : Nonempty (PolarData u) := by
  classical
  let g := locator node S
  let v (j : ℕ) := g * seedCoeff output j
  have hg : g.natDegree = S.card := locator_natDegree _ _
  have hd (j : ℕ) : (v j).degree < (k + heightBound : ℕ) := by
    have h := Strata.degree_mul_lt_add g (seedCoeff output j) g.natDegree
      (k + height) le_rfl (seedCoeff_degree _ _ _ hout)
    exact h.trans_le (by exact_mod_cast (show k + height + g.natDegree ≤ k + heightBound by omega))
  have ha : (g * a).natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound := by
    have h := natDegree_mul_le (p := g) (q := a)
    omega
  have hb : (g * b).natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound := by
    have h := natDegree_mul_le (p := g) (q := b)
    omega
  have hgn : g ≠ 0 := (locator_monic node S).ne_zero
  refine ⟨⟨g * a, g * b, A,
    fun r s => pencil (pencil (v 0) (v 1) s) (pencil (v K1.p) (v (K1.p + 1)) s) (twist r),
    mul_ne_zero hgn hane, ?_, hA, ha, hb, ?_, ?_⟩⟩
  · intro h
    rw [sixNorm_mul, sixNorm_mul] at h
    exact hn (mul_left_cancel₀ (sixNorm_ne_zero hgn) h)
  · intro r s
    exact pencil_degree (pencil_degree (hd 0) (hd 1) s)
      (pencil_degree (hd K1.p) (hd (K1.p + 1)) s) _
  · intro r s i
    by_cases hi : i ∈ S
    · have hz : g.eval (node i) = 0 := locator_eval_zero node _ i hi
      simp only [pencil, v, eval_mul, eval_add, eval_C, hz, zero_mul, mul_zero, add_zero, sub_zero]
    obtain ⟨h0, h1, h2, h3⟩ := hc i hi
    simp only [pencil, fold, v, eval_add, eval_mul, eval_C, h0, h1, h2, h3,
      crossValue, map_add, map_mul]
    ring
end
end P1_2
end
