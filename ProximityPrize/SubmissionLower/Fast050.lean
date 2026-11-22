import ProximityPrize.SubmissionLower.Fast048
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace K1_6
open K1 Polynomial Matrix
open FrobeniusLocator ProximityPrize.Benchmark
private theorem map_syndrome {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (f : F →+* E)
    (x w : ι → F) (j : ℕ) :
    f (syndrome x w j) = syndrome (fun i => f (x i)) (fun i => f (w i)) j := by
  simp only [syndrome, weight, map_sum, map_mul, map_pow, map_inv₀, map_prod, map_sub]
private theorem generic_stacked_moment {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (p : ℕ) [ExpChar F p]
    (node u v : ι → F) (hfixed : ∀ i, node i ^ p = node i)
    (φ : F[X] →+* E) (L t : ℕ) (b : Fin 2) (l : Fin L) (j : Fin (t + 1)) :
    let f := φ.comp Polynomial.C
    let z := φ Polynomial.X
    φ (stacked p node u v L t (b, l) j) =
      syndrome (fun i => f (node i)) (fun i =>
        if b = 0 then f (u i) + z * f (v i)
        else f (u i ^ p) + z ^ p * f (v i ^ p)) (l.val + j.val) := by
  let f := φ.comp Polynomial.C
  let z := φ Polynomial.X
  let x := fun i => f (node i)
  dsimp only
  by_cases hb : b = 0
  · simp only [stacked, hankel, hb, ite_true, map_add, map_mul]
    change f (syndrome node u _) + z * f (syndrome node v _) = _
    rw [map_syndrome, map_syndrome]
    simpa only [one_mul] using
      (Principal.syndrome_linear x (fun i => f (u i)) (fun i => f (v i))
        1 z (l.val + j.val)).symm
  · simp only [stacked, hb, ite_false]
    rw [φ.map_add, φ.map_mul, φ.map_pow Polynomial.X]
    change f (syndrome node u _ ^ p) + z ^ p * f (syndrome node v _ ^ p) = _
    rw [← syndrome_frobenius p node hfixed, ← syndrome_frobenius p node hfixed,
      map_syndrome, map_syndrome]
    simpa only [one_mul] using
      (Principal.syndrome_linear x (fun i => f (u i ^ p)) (fun i => f (v i ^ p))
        1 (z ^ p) (l.val + j.val)).symm
private theorem certificate_shifts_annihilate_generic {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (p : ℕ) [ExpChar F p]
    (node u v : ι → F) (hx : Function.Injective node) (hfixed : ∀ i, node i ^ p = node i)
    (φ : F[X] →+* E) (hφ : Function.Injective φ)
    (k h L t s : ℕ) (hL : h + s = L + 1) (hsize : k + (L + 1) + t ≤ Fintype.card ι)
    (R : Strata.PolynomialRelationCertificate p node u v k h)
    (P : Fin 2 → F[X][X])
    (hP : ∀ b, P b = Principal.assemble (fun j => R.coefficients (b, j))) :
    (shifts P (L + 1) s).transpose * stacked p node u v (L + 1) t = 0 := by
  classical
  let f : F →+* E := φ.comp Polynomial.C
  let x : ι → E := fun i => f (node i)
  let z : E := φ Polynomial.X
  let w : Fin 2 → ι → E := fun b i =>
    if b = 0 then f (u i) + z * f (v i)
    else f (u i ^ p) + z ^ p * f (v i ^ p)
  have hMoment (b : Fin 2) (l : Fin (L + 1)) (j : Fin (t + 1)) :
      φ (stacked p node u v (L + 1) t (b, l) j) = syndrome x (w b) (l.val + j.val) :=
    generic_stacked_moment p node u v hfixed φ (L + 1) t b l j
  have hDegree (b : Fin 2) : (P b).natDegree ≤ h := by
    rw [hP]
    exact R.x_degree b
  have hNode (i : ι) :
      ((P 0).map φ).eval (x i) * w 0 i + ((P 1).map φ).eval (x i) * w 1 i =
        (R.output.map φ).eval (x i) := by
    have he := congrArg φ (R.nodes i)
    simpa only [hP, x, f, RingHom.comp_apply, z, w,
      zero_ne_one, one_ne_zero, ite_true, ite_false, map_add, map_mul, map_pow,
      eval_map_apply] using he
  apply Matrix.ext
  intro d j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, shifts]
  apply hφ
  let A (b : Fin 2) : E[X] := (P b).map φ * Polynomial.X ^ d.val
  have hA (b : Fin 2) : (A b).natDegree ≤ L := by
    have hd : ((P b).map φ).natDegree ≤ h := natDegree_map_le.trans (hDegree b)
    have ha := natDegree_mul_le (p := (P b).map φ) (q := (Polynomial.X : E[X]) ^ d.val)
    rw [natDegree_X_pow] at ha
    have := d.isLt
    dsimp only [A]
    omega
  have hOut (i : ι) : (A 0).eval (x i) * w 0 i + (A 1).eval (x i) * w 1 i =
      ((R.output.map φ) * Polynomial.X ^ d.val).eval (x i) := by
    simp only [A, eval_mul, eval_pow, eval_X]
    rw [← hNode i]
    ring
  have hOutDegree : ((R.output.map φ) * Polynomial.X ^ d.val).degree < ((k + L : ℕ) : WithBot ℕ) := by
    have hR : (R.output.map φ).degree < ((k + h : ℕ) : WithBot ℕ) := degree_map_le.trans_lt R.output_degree
    have hd := Strata.degree_mul_lt_add (Polynomial.X ^ d.val : E[X])
      (R.output.map φ) d.val (k + h) (by simp) hR
    rw [mul_comm] at hd
    refine hd.trans_le ?_
    exact_mod_cast (show k + h + d.val ≤ k + L by have := d.isLt; omega)
  rw [map_sum, map_zero, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [map_mul, hMoment, ← coeff_map, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X]
  change (∑ l : Fin (L + 1), (A 0).coeff l.val * syndrome x (w 0) (l.val + j.val)) +
    (∑ l : Fin (L + 1), (A 1).coeff l.val * syndrome x (w 1) (l.val + j.val)) = 0
  rw [← Strata.syndrome_polynomial_multiple x (w 0) (A 0) _ _ (hA 0),
    ← Strata.syndrome_polynomial_multiple x (w 1) (A 1) _ _ (hA 1)]
  have hLin := Principal.syndrome_linear x
    (fun i => (A 0).eval (x i) * w 0 i) (fun i => (A 1).eval (x i) * w 1 i) 1 1 j.val
  simp only [one_mul] at hLin
  rw [← hLin]
  simp_rw [hOut]
  apply Strata.syndrome_eval_zero x (f.injective.comp hx) _ (k + L) _ hOutDegree
  have := j.isLt
  omega
end K1_6
end
section
namespace K1_13_4
noncomputable section
open K1 K1_13
open scoped Polynomial BigOperators
abbrev GenericX := FractionRing (Polynomial Geom)
abbrev GenericSeed := FractionRing (Polynomial Geom)
abbrev SeedVar := Option (Fin 3)
abbrev SeedRow (R : Type*) [CommSemiring R] := MvPolynomial SeedVar R
abbrev PhysicalRow := SeedRow (Polynomial Geom)
abbrev GenericRow := SeedRow GenericX
abbrev Lower := MvPolynomial (Fin 3) GenericX
abbrev inclX : Geom[X] →+* GenericX := algebraMap _ _
abbrev inclConst : Geom →+* GenericX := algebraMap _ _
def liftX (p : Geom[X]) : GenericSeed[X] := p.map (algebraMap Geom GenericSeed)
def genericResidue (num : Geom[X][X]) (den : Geom[X]) : GenericSeed[X] :=
  Polynomial.C ((algebraMap Geom[X] GenericSeed den)⁻¹) *
    num.map (algebraMap Geom[X] GenericSeed)
def residueAt (num : Geom[X][X]) (den : Geom[X]) (z : Geom) : Geom[X] :=
  Polynomial.C ((den.eval z)⁻¹) * num.map (Polynomial.evalRingHom z)
structure ResidueChart {Γ : Finset K} {s : K → K[X]} (P : PoleData Γ s) where
  numerator : Geom[X][X]
  denominator : Geom[X]
  at_zero : denominator.eval 0 ≠ 0
  small : numerator.natDegree < P.H.natDegree
  generic_unit : IsCoprime
    (liftX P.c * (liftX P.a₀ +
      Polynomial.C (algebraMap Geom[X] GenericSeed Polynomial.X) * liftX P.a₁))
    (liftX P.H)
  generic_congruence : liftX P.H ∣
    liftX P.c * (liftX P.a₀ +
      Polynomial.C (algebraMap Geom[X] GenericSeed Polynomial.X) * liftX P.a₁) *
      genericResidue numerator denominator +
      Polynomial.C (algebraMap Geom[X] GenericSeed Polynomial.X) * liftX P.q
  regular : ∀ γ ∈ Γ, denominator.eval (P.z γ) ≠ 0
  quotient : ∀ γ ∈ Γ, ∃ T : Geom[X], T.natDegree ≤ 131071 ∧
    extend (s γ) = P.H * T + residueAt numerator denominator (P.z γ)
def jetTotal {R : Type*} [CommSemiring R] (F : SeedRow R) : ℕ :=
  F.weightedTotalDegree (fun i => i.elim 0 (fun _ => 1))
def jetIndex {R : Type*} [CommSemiring R] (F : SeedRow R) : ℕ :=
  F.weightedTotalDegree (fun i => i.elim 0 Fin.val)
def seedDegree {R : Type*} [CommSemiring R] (F : SeedRow R) : ℕ := F.degreeOf none
def Caps {R : Type*} [CommSemiring R] (a : Shape) (F : SeedRow R) : Prop :=
  jetTotal F ≤ a.b ∧ jetIndex F ≤ a.j ∧ F.degreeOf (some 2) ≤ a.t ∧
    seedDegree F ≤ 70000
def firstBox : Shape := ⟨6789, 2300, 1150⟩
def secondBox : Shape := ⟨6820, 2300, 1150⟩
abbrev firstOrder : ℕ := 5746355
abbrev secondOrder : ℕ := 2769994
abbrev firstCut : ℕ := 5000 * 180265 - firstOrder
abbrev secondCut : ℕ := 5000 * 180265 - secondOrder
def backwardShift (x v : Geom) (F : PhysicalRow) : PhysicalRow :=
  MvPolynomial.eval₂ MvPolynomial.C (fun j =>
    if j = some 0 then
      MvPolynomial.X (some 0) + MvPolynomial.C (Polynomial.C v) -
        MvPolynomial.C (Polynomial.C x - Polynomial.X) * MvPolynomial.X (some 1) -
        MvPolynomial.C ((Polynomial.C x - Polynomial.X) ^ 2) * MvPolynomial.X (some 2)
    else MvPolynomial.X j) F
def PhysicalContact (w : I → K) (F : PhysicalRow) : Prop :=
  ∀ i (a : SeedVar →₀ ℕ),
    (Polynomial.X - Polynomial.C (embed (node i))) ^ (5000 - 3 * a (some 0)) ∣
      (backwardShift (embed (node i)) (embed (w i)) F).coeff a
def TrueCut (h t : ℕ) (F : PhysicalRow) : Prop :=
  ∀ a ∈ F.support, (F.coeff a).natDegree +
    a.sum (fun i e => i.elim 0 (fun j => (131071 + h - j.val) * e)) ≤ t
def restoredJet {Γ s} (P : PoleData Γ s) (L : ResidueChart P) (i : Fin 3) :
    MvPolynomial (Fin 3) GenericSeed[X] :=
  MvPolynomial.C (Polynomial.hasseDeriv i.val (genericResidue L.numerator L.denominator)) +
    ∑ j : Fin 3, if j.val ≤ i.val then
      MvPolynomial.C (Polynomial.hasseDeriv (i.val - j.val) (liftX P.H)) *
        MvPolynomial.X j
    else 0
def restore {Γ s} (P : PoleData Γ s) (L : ResidueChart P) (F : PhysicalRow) :
    MvPolynomial (Fin 3) GenericSeed[X] :=
  MvPolynomial.eval₂ (MvPolynomial.C.comp (Polynomial.mapRingHom (algebraMap Geom GenericSeed)))
    (fun i => i.elim
      (MvPolynomial.C (Polynomial.C (algebraMap Geom[X] GenericSeed Polynomial.X)))
      (restoredJet P L)) F
def Source {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P)
    (a : Shape) (t : ℕ) (F : PhysicalRow) : Prop :=
  Caps a F ∧ TrueCut P.H.natDegree (t + (a.b + a.j) * P.H.natDegree) F ∧
    PhysicalContact w F ∧
    (MvPolynomial.C (liftX P.H)) ^ (a.b + a.j) ∣ restore P L F
def HasRank {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P)
    (a : Shape) (t n : ℕ) : Prop :=
  ∃ e : Fin n → PhysicalRow, LinearIndependent Geom e ∧
    ∀ i, Source w P L a t (e i)
def mixedWeight (a : SeedVar →₀ ℕ) : ℕ :=
  7800 * a none + 49196 * a.some.sum (fun _ e => e)
def mixedHasse (a : SeedVar →₀ ℕ) (F : PhysicalRow) : PhysicalRow :=
  (MvPolynomial.eval₂ (MvPolynomial.C.comp MvPolynomial.C)
    (fun i => MvPolynomial.X i + MvPolynomial.C (MvPolynomial.X i)) F).coeff a
def Necessary {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) :
    Submodule Geom PhysicalRow :=
  Submodule.span Geom {Q | ∃ t F a, Source w P L secondBox t F ∧
    t + mixedWeight a ≤ secondCut ∧ Q = mixedHasse a F}
def toGeneric (F : PhysicalRow) : GenericRow := MvPolynomial.map inclX F
def atPoint (z : GenericX) (y : Fin 3 → GenericX) : SeedVar → GenericX :=
  fun i => i.elim z y
def trajectory (S : Geom[X]) : Fin 3 → GenericX := fun i => inclX (jet S i)
def translate {σ : Type*} (y : σ → GenericX) :
    MvPolynomial σ GenericX →+* MvPolynomial σ GenericX :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (y i))
def MixedOrder (F : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ) : Prop :=
  ∀ a ∈ (translate (atPoint z y) F).support, d ≤ mixedWeight a
def LowerOrder (F : Lower) (y : Fin 3 → GenericX) (d : ℕ) : Prop :=
  ∀ a ∈ (translate y F).support, d ≤ a.sum (fun _ e => e)
def lowerIndex (F : Lower) : ℕ := F.support.sup (fun a => a.sum (fun i e => i.val * e))
def PairOrders (F G : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) : Prop :=
  MixedOrder F z y firstOrder ∧ MixedOrder G z y secondOrder
def asSeedPoly (F : GenericRow) : Lower[X] := MvPolynomial.optionEquivLeft _ _ F
def pureSeed (f : GenericX[X]) : GenericRow :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X none) f
structure CommonPair (F G : GenericRow) where
  fixed : Finset GenericRow
  moving : Finset GenericRow
  pure : GenericX[X]
  exponent : GenericRow → ℕ
  left : GenericRow
  right : GenericRow
  pure_ne : pure ≠ 0
  pure_degree : pure.natDegree ≤ 140000
  fixed_kind : ∀ f ∈ fixed, Irreducible f ∧ 0 < jetTotal f ∧ seedDegree f = 0
  moving_kind : ∀ f ∈ moving, Irreducible f ∧ 0 < jetTotal f ∧
    0 < seedDegree f ∧ f.degreeOf (some 2) = 0
  fixed_total : jetTotal (∏ f ∈ fixed, f) ≤ 68
  fixed_index : jetIndex (∏ f ∈ fixed, f) ≤ 23
  moving_total : jetTotal (∏ f ∈ moving, f) ≤ 10
  moving_index : jetIndex (∏ f ∈ moving, f) ≤ 3
  moving_seed : seedDegree (∏ f ∈ moving, f) ≤ 112
  left_eq : F = (pureSeed pure * (∏ f ∈ fixed, f ^ exponent f) *
    (∏ f ∈ moving, f ^ exponent f)) * left
  right_eq : G = (pureSeed pure * (∏ f ∈ fixed, f ^ exponent f) *
    (∏ f ∈ moving, f ^ exponent f)) * right
  left_ne : left ≠ 0
  right_ne : right ≠ 0
  proper : IsRelPrime left right
  left_caps : Caps firstBox left
  right_caps : Caps secondBox right
def pad (F : GenericRow) (a : Geom[X]) : GenericRow :=
  F * pureSeed (a.map inclConst)
def seedResultant (F G : GenericRow) : Lower :=
  Polynomial.resultant (asSeedPoly F) (asSeedPoly G) 70000 70000
structure PaddedPair (F G : GenericRow) where
  a : Geom[X]
  b : Geom[X]
  degree_left : (asSeedPoly (pad F a)).natDegree = 70000
  degree_right : (asSeedPoly (pad G b)).natDegree = 70000
  nonzero : seedResultant (pad F a) (pad G b) ≠ 0
  total : (seedResultant (pad F a) (pad G b)).totalDegree ≤ 952630000
  index : lowerIndex (seedResultant (pad F a) (pad G b)) ≤ 322000000
  keeps_order : ∀ z y, PairOrders F G z y → PairOrders (pad F a) (pad G b) z y
theorem native_degree_arithmetic :
    70000 * (6789 + 6820) = 952630000 ∧ 70000 * (2300 + 2300) = 322000000 ∧
    68 + 2 * 112 * 10 ≤ 6300 ∧ 23 + (2 * 3 + 1) * 112 ≤ 2403 := by
  decide
theorem native_factor_arithmetic :
    let T := 525913765916471
    let S := 2561085868844197170227
    49196 * 6820 * T / S = 68 ∧ 49196 * 2300 * T / S = 23 ∧
      7800 * 6820 * T / S = 10 ∧ 7800 * 2300 * T / S = 3 ∧
      7800 * 70000 * T / S = 112 ∧ 1571799066189253395000 < S := by
  decide
end
end K1_13_4
end
section
namespace K1_13_4
noncomputable section
open K1 K1_13
open scoped Polynomial BigOperators
def c1 : Prop :=
  ∀ Γ s (P : PoleData Γ s), Nonempty (ResidueChart P)
def c6 : Prop :=
  ∀ F G : GenericRow, F ≠ 0 → G ≠ 0 → IsRelPrime F G →
    Caps firstBox F → Caps secondBox G → Nonempty (PaddedPair F G)
end
end K1_13_4
end
section
namespace K1_13_4_2
set_option backward.isDefEq.respectTransparency false
noncomputable section
open K1 K1_13 K1_13_4
open scoped Polynomial BigOperators
inductive Bank where
  | first
  | second
def Bank.box : Bank → Shape
  | .first => firstBox
  | .second => secondBox
def Bank.cut : Bank → ℕ
  | .first => firstCut
  | .second => secondCut
def Bank.targetRank : Bank → ℕ
  | .first => 1
  | .second => 2561085868844197170227
def Bank.nodeRank : Bank → ℕ
  | .first => 10697571688375
  | .second => 10697783317215
def gradeCount (a : Shape) (q : ℕ) : ℕ :=
  ∑ e₂ ∈ Finset.range (min q (min a.t (a.j / 2)) + 1),
    (min (q - e₂) (a.j - 2 * e₂) + 1)
def poleDebit (a : Shape) : ℕ :=
  ∑ q ∈ Finset.range (a.b + 1),
    (a.b + a.j - q) * gradeCount a q * (70001 + (a.b - q))
def codimIn (V W : Submodule Geom PhysicalRow) : ℕ :=
  Module.finrank Geom V - Module.finrank Geom (V ⊓ W : Submodule Geom PhysicalRow)
private def backwardLinear (x v : Geom) : PhysicalRow →ₗ[Geom] PhysicalRow :=
  (MvPolynomial.aeval (R := Geom[X]) (fun j : SeedVar =>
    if j = some 0 then
      MvPolynomial.X (some 0) + MvPolynomial.C (Polynomial.C v) -
        MvPolynomial.C (Polynomial.C x - Polynomial.X) * MvPolynomial.X (some 1) -
        MvPolynomial.C ((Polynomial.C x - Polynomial.X) ^ 2) * MvPolynomial.X (some 2)
    else MvPolynomial.X j)).toLinearMap.restrictScalars Geom
def contactAt (x v : Geom) : Submodule Geom PhysicalRow :=
  ⨅ e : SeedVar →₀ ℕ,
    ((Ideal.span {((Polynomial.X - Polynomial.C x) ^ (5000 - 3 * e (some 0)) :
      Geom[X])}).restrictScalars Geom).comap
      (((MvPolynomial.lcoeff Geom[X] e).restrictScalars Geom).comp (backwardLinear x v))
abbrev RawRow := MvPolynomial (Fin 3) GenericSeed[X]
private def restoreLinear {Γ s} (P : PoleData Γ s) (L : ResidueChart P) :
    PhysicalRow →ₗ[Geom] RawRow :=
  (MvPolynomial.aevalTower
    (((Algebra.ofId GenericSeed[X] RawRow).restrictScalars Geom).comp
      (Polynomial.mapAlgHom (Algebra.ofId Geom GenericSeed)))
    (fun i : SeedVar => i.elim
      (MvPolynomial.C (Polynomial.C (algebraMap Geom[X] GenericSeed Polynomial.X)))
      (restoredJet P L))).toLinearMap
def poleCondition {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (a : Shape) (D : GenericSeed[X]) : Submodule Geom PhysicalRow :=
  ((Ideal.span {((MvPolynomial.C D : RawRow) ^ (a.b + a.j))}).restrictScalars Geom).comap
    (restoreLinear P L)
def localPole (α : Geom) : GenericSeed[X] :=
  Polynomial.X - Polynomial.C (algebraMap Geom GenericSeed α)
def IsConstantShift {Γ s Γ' s'} (P : PoleData Γ s) (P' : PoleData Γ' s') : Prop :=
  (∃ ε : Geom, P'.H = P.H + Polynomial.C ε) ∧
    P'.c = P.c ∧ P'.q = P.q ∧ P'.a₀ = P.a₀ ∧ P'.a₁ = P.a₁
theorem mem_contactAt (x v : Geom) (F : PhysicalRow) :
    F ∈ contactAt x v ↔ ∀ e : SeedVar →₀ ℕ,
      (Polynomial.X - Polynomial.C x) ^ (5000 - 3 * e (some 0)) ∣
        (backwardShift x v F).coeff e := by
  simp only [contactAt, Submodule.mem_iInf, Submodule.mem_comap, Submodule.restrictScalars_mem,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, MvPolynomial.lcoeff_apply,
    Ideal.mem_span_singleton]
  rfl
theorem mem_poleCondition {Γ s} (P : PoleData Γ s) (L : ResidueChart P) (a : Shape)
    (D : GenericSeed[X]) (F : PhysicalRow) :
    F ∈ poleCondition P L a D ↔ (MvPolynomial.C D) ^ (a.b + a.j) ∣ restore P L F := by
  simp only [poleCondition, Submodule.mem_comap, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton]
  rfl
end
end K1_13_4_2
end
section
namespace K1_13_4_2
set_option maxHeartbeats 700000
noncomputable section
open K1 K1_13 K1_13_4
open scoped Polynomial BigOperators
def c2 : Prop :=
  ∀ (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow), Module.Finite Geom V →
    (∀ F ∈ V, Caps b.box F) →
    codimIn V (contactAt x v) ≤ 70001 * b.nodeRank
def c3 : Prop :=
  ∀ (Γ : Finset K) (s : K → K[X]) (P : PoleData Γ s) (L : ResidueChart P)
    (a : Shape) (α : Geom) (V : Submodule Geom PhysicalRow), Module.Finite Geom V →
    (∀ F ∈ V, Caps a F) → P.H.IsRoot α → P.H.derivative.eval α ≠ 0 →
    codimIn V (poleCondition P L a (localPole α)) ≤ poleDebit a
def c4 : Prop :=
  ∀ (Γ : Finset K) (s : K → K[X]) (P : PoleData Γ s) (L : ResidueChart P)
    (a : Shape) (V : Submodule Geom PhysicalRow) (r : ℕ), Module.Finite Geom V →
    (∀ (P' : PoleData ∅ (fun _ : K => (0 : K[X]))) (L' : ResidueChart P'),
      IsConstantShift P P' → P'.H.natDegree = P.H.natDegree → P'.H.Separable →
      codimIn V (poleCondition P' L' a (liftX P'.H)) ≤ r) →
    codimIn V (poleCondition P L a (liftX P.H)) ≤ r
private theorem rank_lt_of_le {V U : Submodule Geom PhysicalRow} [Module.Finite Geom V]
    (h : U ≤ V) : Module.rank Geom U < Cardinal.aleph0 :=
  (Submodule.rank_mono h).trans_lt (Module.rank_lt_aleph0 Geom ↥V)
private theorem codim_inf_le (V U W : Submodule Geom PhysicalRow) [Module.Finite Geom V] :
    codimIn V (U ⊓ W) ≤ codimIn V U + codimIn V W := by
  have he : (V ⊓ U) ⊓ (V ⊓ W) = V ⊓ (U ⊓ W) := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left)
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
        (le_inf inf_le_left (inf_le_right.trans inf_le_right))
  have h := Submodule.rank_sup_add_rank_inf_eq (V ⊓ U) (V ⊓ W)
  rw [he] at h
  have hle : (V ⊓ U) ⊔ (V ⊓ W) ≤ V := sup_le inf_le_left inf_le_left
  have hdim := congrArg Cardinal.toNat h
  rw [Cardinal.toNat_add (rank_lt_of_le hle) (rank_lt_of_le inf_le_left),
    Cardinal.toNat_add (rank_lt_of_le inf_le_left) (rank_lt_of_le inf_le_left)] at hdim
  change Module.finrank Geom ((V ⊓ U) ⊔ (V ⊓ W) : Submodule Geom PhysicalRow) +
    Module.finrank Geom (V ⊓ (U ⊓ W) : Submodule Geom PhysicalRow) =
      Module.finrank Geom (V ⊓ U : Submodule Geom PhysicalRow) +
      Module.finrank Geom (V ⊓ W : Submodule Geom PhysicalRow) at hdim
  have hsup := Submodule.finrank_mono hle
  unfold codimIn
  omega
private theorem codim_finset_inf_le {ι : Type*} (V : Submodule Geom PhysicalRow)
    [Module.Finite Geom V] (T : Finset ι) (U : ι → Submodule Geom PhysicalRow) (r : ℕ)
    (hr : ∀ i ∈ T, codimIn V (U i) ≤ r) :
    codimIn V (T.inf U) ≤ T.card * r := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.inf_empty, Finset.card_empty, zero_mul, codimIn, inf_top_eq, Nat.sub_self]
  | insert i T hi ih =>
    rw [Finset.inf_insert, Finset.card_insert_of_notMem hi, Nat.succ_mul]
    have hi' := hr i (Finset.mem_insert_self i T)
    have hT := ih fun j hj => hr j (Finset.mem_insert_of_mem hj)
    exact (codim_inf_le V (U i) (T.inf U)).trans
      (by simpa only [add_comm] using Nat.add_le_add hi' hT)
private theorem codim_antitone (V : Submodule Geom PhysicalRow) [Module.Finite Geom V]
    {U W : Submodule Geom PhysicalRow} (h : U ≤ W) : codimIn V W ≤ codimIn V U :=
  Nat.sub_le_sub_left
    (Cardinal.toNat_le_toNat (Submodule.rank_mono (inf_le_inf_left V h))
      (rank_lt_of_le (show V ⊓ W ≤ V from inf_le_left))) _
private theorem separable_rank (h3 : c3) {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (a : Shape) (V : Submodule Geom PhysicalRow) [hV : Module.Finite Geom V]
    (hcap : ∀ F ∈ V, Caps a F) (hsep : P.H.Separable) :
    codimIn V (poleCondition P L a (liftX P.H)) ≤ P.H.natDegree * poleDebit a := by
  classical
  let T : Finset Geom := ⟨P.H.roots, Polynomial.nodup_roots hsep⟩
  have hcard : T.card = P.H.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroot (α : Geom) (hα : α ∈ T) : P.H.IsRoot α :=
    (Polynomial.mem_roots P.monic.ne_zero).mp hα
  have hprod : (∏ α ∈ T, localPole α) = liftX P.H := by
    have he : (∏ α ∈ T, (Polynomial.X - Polynomial.C α)) = P.H :=
      ((IsAlgClosed.splits P.H).eq_prod_roots_of_monic P.monic).symm
    change _ = Polynomial.mapRingHom (algebraMap Geom GenericSeed) P.H
    rw [← he, map_prod]
    simp [localPole]
  let W : Geom → Submodule Geom PhysicalRow := fun α => poleCondition P L a (localPole α)
  have hlocal (α : Geom) (hα : α ∈ T) : codimIn V (W α) ≤ poleDebit a := by
    apply h3 Γ s P L a α V hV hcap (hroot α hα)
    exact hsep.eval₂_derivative_ne_zero (RingHom.id Geom) (hroot α hα)
  have hsub : T.inf W ≤ poleCondition P L a (liftX P.H) := by
    intro F hF
    have hd (α : Geom) (hα : α ∈ T) :
        (MvPolynomial.C (localPole α) : RawRow) ^ (a.b + a.j) ∣ restore P L F := by
      have hle : T.inf W ≤ W α := Finset.inf_le hα
      exact (mem_poleCondition P L a _ _).mp (hle hF)
    have hcop (α β : Geom) (hne : α ≠ β) :
        IsCoprime ((MvPolynomial.C (localPole α) : RawRow) ^ (a.b + a.j))
          ((MvPolynomial.C (localPole β) : RawRow) ^ (a.b + a.j)) := by
      apply IsCoprime.pow
      apply IsCoprime.map (f := MvPolynomial.C)
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr ((FaithfulSMul.algebraMap_injective Geom GenericSeed).ne hne)).isUnit
    have h := Finset.prod_dvd_of_coprime (t := T) (fun α _ β _ hne => hcop α β hne) hd
    rw [Finset.prod_pow, ← map_prod MvPolynomial.C, hprod] at h
    exact (mem_poleCondition P L a _ _).mpr h
  have hdim := codim_finset_inf_le V T W (poleDebit a) hlocal
  rw [hcard] at hdim
  exact (codim_antitone V hsub).trans hdim
private theorem dimension_of_debits {ambient kept required physical pole : ℕ}
    (hsize : required + physical + pole ≤ ambient)
    (hcodim : ambient - kept ≤ physical + pole) : required ≤ kept := by
  omega
end
end K1_13_4_2
end
section
namespace K1_13_4_2_2
noncomputable section
open K1_13 K1_13_4 MvPolynomial
open scoped BigOperators
abbrev Flat := MvPolynomial (Option (Fin 3)) Geom
abbrev Exp := Option (Fin 3) →₀ ℕ
def gradeWeight (v : Option (Fin 3)) : ℕ := v.elim 0 (fun _ => 1)
def indexWeight (v : Option (Fin 3)) : ℕ := v.elim 0 Fin.val
def topWeight (v : Option (Fin 3)) : ℕ := v.elim 0 (Pi.single (2 : Fin 3) 1)
def Eligible (B : ℕ) (e : Exp) : Prop :=
  e.weight gradeWeight ≤ B ∧ e.weight indexWeight ≤ 2300 ∧ e (some 2) ≤ 1150
def Capped (B : ℕ) : Submodule Geom Flat := restrictSupport Geom {e | Eligible B e}
def shearImage (v : Option (Fin 3)) : Flat :=
  if v = some 0 then
    MvPolynomial.X (some 0) + MvPolynomial.X none * MvPolynomial.X (some 1) -
      MvPolynomial.X none ^ 2 * MvPolynomial.X (some 2)
  else MvPolynomial.X v
def shear : Flat →ₐ[Geom] Flat := bind₁ shearImage
def contactWeight (v : Option (Fin 3)) : ℕ := v.elim 1 (Pi.single (0 : Fin 3) 3)
def origin : Flat →ₗ[Geom] Flat := (weightedTruncation contactWeight 5000).comp shear.toLinearMap
def offset (k : ℕ) : ℤ := (k : ℤ) - 2300
def blockExponents (q k : ℕ) : Set Exp :=
  { e | Eligible q e ∧ e.weight gradeWeight = q ∧
    (e none : ℤ) - (e.weight indexWeight : ℤ) = offset k }
def Block (q k : ℕ) : Submodule Geom Flat := restrictSupport Geom (blockExponents q k)
def originBlock (q k : ℕ) : Block q k →ₗ[Geom] Flat :=
  origin.domRestrict (Block q k)
abbrev Plane := MvPolynomial (Fin 3) Geom
abbrev PlaneExp := Fin 3 →₀ ℕ
def residualDegree (q : ℕ) : ℕ := min q 2300
def planeExponents (q : ℕ) (g : ℤ) : Set PlaneExp :=
  { e | e.weight (fun _ => 1) = residualDegree q ∧
    -g ≤ (e.weight Fin.val : ℤ) ∧ e.weight Fin.val ≤ 2300 ∧ e 2 ≤ 1150 }
def PlaneSource (q : ℕ) (g : ℤ) : Submodule Geom Plane :=
  restrictSupport Geom (planeExponents q g)
def planeImage (j : Fin 3) : Plane :=
  if j = 0 then MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 2
  else MvPolynomial.X j
def planeOrder (q : ℕ) (g : ℤ) : ℤ := 5000 - (q : ℤ) - g
def planeContact (q : ℕ) (g : ℤ) : PlaneSource q g →ₗ[Geom] Plane :=
  ((weightedTruncation (![2,0,1] : Fin 3 → ℕ) (planeOrder q g).toNat).comp
    (bind₁ planeImage).toLinearMap).domRestrict (PlaneSource q g)
structure Flag where
  ordinary : ℤ
  weighted : ℤ
def initialFlag (q : ℕ) (g : ℤ) (i : Fin 3) : Flag :=
  let d : ℤ := residualDegree q
  ![⟨0, -g⟩, ⟨d - 1150,2 * d - 2300⟩,⟨0, planeOrder q g⟩] i
abbrev Powers := Fin 6 → ℕ
def factorDegree (j : Fin 6) : ℤ := if j = 5 then 2 else 1
def factorFlag (j : Fin 6) (i : Fin 3) : Flag :=
  (![![⟨1,2⟩,⟨0,0⟩,⟨1,1⟩],
    ![⟨1,1⟩,⟨1,1⟩,⟨0,0⟩],
    ![⟨0,0⟩,⟨1,1⟩,⟨1,1⟩],
    ![⟨0,0⟩,⟨1,2⟩,⟨0,0⟩],
    ![⟨0,0⟩,⟨0,0⟩,⟨1,2⟩],
    ![⟨1,1⟩,⟨1,2⟩,⟨1,2⟩]] : Fin 6 → Fin 3 → Flag) j i
def remainingDegree (q : ℕ) (p : Powers) : ℤ :=
  residualDegree q - ∑ j, (p j : ℤ) * factorDegree j
def remainingFlag (q : ℕ) (g : ℤ) (p : Powers) (i : Fin 3) : Flag :=
  ⟨(initialFlag q g i).ordinary - ∑ j, (p j : ℤ) * (factorFlag j i).ordinary,
    (initialFlag q g i).weighted - ∑ j, (p j : ℤ) * (factorFlag j i).weighted⟩
def triangular (n : ℤ) : ℤ := n * (n + 1) / 2
def colength (F : Flag) : ℤ :=
  let u := max 0 (max F.ordinary ((F.weighted + 1) / 2))
  let v := max u F.weighted
  triangular u + triangular (v - u)
def kernelLower (d : ℤ) (F : Fin 3 → Flag) : ℤ :=
  if d < 0 then 0 else triangular (d + 1) - ∑ i, colength (F i)
def cumulative (d w : ℤ) : ℤ :=
  if w < 0 then 0 else
    let u := min w (2 * d)
    (u + 2) ^ 2 / 4 - triangular (max 0 (u - d))
def columnCount (q : ℕ) (g : ℤ) : ℤ :=
  let d : ℤ := residualDegree q
  cumulative d 2300 - cumulative d (min 2300 (-g - 1))
def blockBound (q : ℕ) (g : ℤ) (p : Powers) : ℕ :=
  if planeOrder q g ≤ 0 then 0 else
    let base := kernelLower (residualDegree q) (initialFlag q g)
    let shifted := kernelLower (remainingDegree q p) (remainingFlag q g p)
    (columnCount q g - max 0 (max base shifted)).toNat
def gradeBound (p : ℕ → ℕ → Powers) (q : ℕ) : ℕ :=
  ∑ k ∈ Finset.range 7300, blockBound q (offset k) (p q k)
end
end K1_13_4_2_2
end
section
namespace K1_13_4_2_2_5
def cost (w : ℤ) : ℤ := ((w + 1) / 2) * (w / 2 + 1)
def columns (k : ℤ) : ℤ := 1324801 - cost (max 0 (2300 - k))
def linearPower (k t : ℤ) : ℤ := t - 2 * k - 1
def conicPower (k t : ℤ) : ℤ := 2 * t - 2301 - k
def linearAt (both : Bool) (k t : ℤ) : ℤ :=
  if both then linearPower k t else 0
def shiftedRank (both : Bool) (k t : ℤ) : ℤ :=
  let n := linearAt both k t
  let m := conicPower k t
  columns k + cost (2300 - k - 2 * n - m) + cost (t - n - 2 * m) -
    (1151 - n - m) ^ 2
def admissible (both : Bool) (k l r : ℤ) : Prop :=
  (if both then 0 ≤ linearPower k l else linearPower k r ≤ 0) ∧
    0 ≤ conicPower k l ∧ linearAt both k r + conicPower k r ≤ 1150 ∧
    0 ≤ 2300 - k - 2 * linearAt both k r - conicPower k r ∧
    0 ≤ r - linearAt both k r - 2 * conicPower k r
instance (both : Bool) (k l r : ℤ) : Decidable (admissible both k l r) := by
  unfold admissible
  cases both <;> infer_instance
inductive Mode where
  | columns
  | empty
  | shifted (both : Bool)
  deriving DecidableEq
def valid (mode : Mode) (k l r : ℤ) : Prop :=
  match mode with
  | .columns | .empty => True
  | .shifted both => admissible both k l r
instance (mode : Mode) (k l r : ℤ) : Decidable (valid mode k l r) := by
  cases mode <;> unfold valid <;> infer_instance
def chooseMode (k t : ℤ) : Mode :=
  let c := columns k
  let e := cost t
  let both := decide (0 < linearPower k t)
  if admissible both k t t ∧ shiftedRank both k t < min c e then
    .shifted both
  else if c ≤ e then .columns else .empty
def linearSum (len : ℕ) : ℤ := (len : ℤ) * (len - 1 : ℤ) / 2
def squareSum (len : ℕ) : ℤ := (len : ℤ) * (len - 1 : ℤ) * (2 * len - 1 : ℤ) / 6
def sumCost (a b : ℤ) (len : ℕ) : ℤ :=
  (len : ℤ) * cost a + b * (a + 1) * linearSum len + b ^ 2 * squareSum len
def sumSquare (a b : ℤ) (len : ℕ) : ℤ :=
  (len : ℤ) * a ^ 2 + 2 * a * b * linearSum len + b ^ 2 * squareSum len
def modeSum (mode : Mode) (k start : ℤ) (len : ℕ) : ℤ :=
  match mode with
  | .columns => (len : ℤ) * columns k
  | .empty => sumCost start 1 len
  | .shifted both =>
    let n := linearAt both k start
    let m := conicPower k start
    let s : ℤ := if both then 1 else 0
    (len : ℤ) * columns k +
      sumCost (2300 - k - 2 * n - m) (-2 * s - 2) len +
      sumCost (start - n - 2 * m) (-3 - s) len -
      sumSquare (1151 - n - m) (-2 * s - 4) len
def endpoint (k start : ℤ) (mode : Mode) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if chooseMode k (start + 2 * mid) = mode then endpoint k start mode fuel mid hi
      else endpoint k start mode fuel lo mid
def runLength (k start : ℤ) (len : ℕ) (mode : Mode) : ℕ :=
  if chooseMode k (start + 2 * ((len : ℤ) - 1)) = mode then len
  else min len (endpoint k start mode 12 0 (len - 1) + 1)
def parityBound (k : ℤ) : ℕ → ℤ → ℕ → ℤ
  | 0, _, len => (len : ℤ) * columns k
  | fuel + 1, start, len =>
    if len = 0 then 0 else
      let mode := chooseMode k start
      let width := runLength k start len mode
      let last := start + 2 * ((width : ℤ) - 1)
      let bound := if valid mode k start last then
        modeSum mode k start width else (width : ℤ) * columns k
      bound + parityBound k fuel (start + 2 * width) (len - width)
def offsetTotal (k : ℕ) : ℤ :=
  let len := min 2700 (5000 - k)
  let start : ℤ := 5001 - (k : ℤ) - len
  parityBound k 8 start ((len + 1) / 2) + parityBound k 8 (start + 1) (len / 2)
def total (start : ℕ) : ℕ → ℤ
  | 0 => 0
  | len + 1 => total start len + offsetTotal (start + len)
end K1_13_4_2_2_5
end
section
namespace K1_13_4_2_2_5
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private theorem budgetHigh_total_add (s m n : ℕ) :
    total s (m + n) = total s m + total (s + m) n := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    change total s (m + n) + offsetTotal (s + (m + n)) =
      total s m + (total (s + m) n + offsetTotal (s + m + n))
    rw [ih, Nat.add_assoc s m n, add_assoc]
open scoped BigOperators
private theorem budgetHigh_total_chunks (s width count : ℕ) :
    total s (count * width) = ∑ i ∈ Finset.range count, total (s + i * width) width := by
  induction count with
  | zero => simp [total]
  | succ count ih => rw [Nat.succ_mul, budgetHigh_total_add, Finset.sum_range_succ, ih]
private theorem budgetHigh_chunk2250 : total 2250 5 = 8045641830 :=
  by decide +kernel
private theorem budgetHigh_chunk2255 : total 2255 5 = 8012814530 :=
  by decide +kernel
private theorem budgetHigh_chunk2260 : total 2260 5 = 7979950150 :=
  by decide +kernel
private theorem budgetHigh_chunk2265 : total 2265 5 = 7947049635 :=
  by decide +kernel
private theorem budgetHigh_chunk2270 : total 2270 5 = 7914114845 :=
  by decide +kernel
private theorem budgetHigh_chunk2275 : total 2275 5 = 7881146740 :=
  by decide +kernel
private theorem budgetHigh_chunk2280 : total 2280 5 = 7848147165 :=
  by decide +kernel
private theorem budgetHigh_chunk2285 : total 2285 5 = 7815117095 :=
  by decide +kernel
private theorem budgetHigh_chunk2290 : total 2290 5 = 7782058360 :=
  by decide +kernel
private theorem budgetHigh_chunk2295 : total 2295 5 = 7748971950 :=
  by decide +kernel
private theorem budgetHigh_chunk2300 : total 2300 5 = 7715860865 :=
  by decide +kernel
private theorem budgetHigh_chunk2305 : total 2305 5 = 7682740840 :=
  by decide +kernel
private theorem budgetHigh_chunk2310 : total 2310 5 = 7649620815 :=
  by decide +kernel
private theorem budgetHigh_chunk2315 : total 2315 5 = 7616500790 :=
  by decide +kernel
private theorem budgetHigh_chunk2320 : total 2320 5 = 7583380765 :=
  by decide +kernel
private theorem budgetHigh_chunk2325 : total 2325 5 = 7550260740 :=
  by decide +kernel
private theorem budgetHigh_chunk2330 : total 2330 5 = 7517140715 :=
  by decide +kernel
private theorem budgetHigh_chunk2335 : total 2335 5 = 7484020690 :=
  by decide +kernel
private theorem budgetHigh_chunk2340 : total 2340 5 = 7450900665 :=
  by decide +kernel
private theorem budgetHigh_chunk2345 : total 2345 5 = 7417780640 :=
  by decide +kernel
private theorem budgetHigh_chunk2350 : total 2350 5 = 7384660615 :=
  by decide +kernel
private theorem budgetHigh_chunk2355 : total 2355 5 = 7351540590 :=
  by decide +kernel
private theorem budgetHigh_chunk2360 : total 2360 5 = 7318420565 :=
  by decide +kernel
private theorem budgetHigh_chunk2365 : total 2365 5 = 7285300540 :=
  by decide +kernel
private theorem budgetHigh_chunk2370 : total 2370 5 = 7252180515 :=
  by decide +kernel
private theorem budgetHigh_chunk2375 : total 2375 5 = 7219060490 :=
  by decide +kernel
private theorem budgetHigh_chunk2380 : total 2380 5 = 7185940465 :=
  by decide +kernel
private theorem budgetHigh_chunk2385 : total 2385 5 = 7152820440 :=
  by decide +kernel
private theorem budgetHigh_chunk2390 : total 2390 5 = 7119700415 :=
  by decide +kernel
private theorem budgetHigh_chunk2395 : total 2395 5 = 7086580390 :=
  by decide +kernel
private theorem budgetHigh_chunk2400 : total 2400 5 = 7053460365 :=
  by decide +kernel
private theorem budgetHigh_chunk2405 : total 2405 5 = 7020340340 :=
  by decide +kernel
private theorem budgetHigh_chunk2410 : total 2410 5 = 6987220315 :=
  by decide +kernel
private theorem budgetHigh_chunk2415 : total 2415 5 = 6954100290 :=
  by decide +kernel
private theorem budgetHigh_chunk2420 : total 2420 5 = 6920980265 :=
  by decide +kernel
private theorem budgetHigh_chunk2425 : total 2425 5 = 6887860240 :=
  by decide +kernel
private theorem budgetHigh_chunk2430 : total 2430 5 = 6854740215 :=
  by decide +kernel
private theorem budgetHigh_chunk2435 : total 2435 5 = 6821620190 :=
  by decide +kernel
private theorem budgetHigh_chunk2440 : total 2440 5 = 6788500165 :=
  by decide +kernel
private theorem budgetHigh_chunk2445 : total 2445 5 = 6755380140 :=
  by decide +kernel
private theorem budgetHigh_chunk2450 : total 2450 5 = 6722260115 :=
  by decide +kernel
private theorem budgetHigh_chunk2455 : total 2455 5 = 6689140090 :=
  by decide +kernel
private theorem budgetHigh_chunk2460 : total 2460 5 = 6656020065 :=
  by decide +kernel
private theorem budgetHigh_chunk2465 : total 2465 5 = 6622900040 :=
  by decide +kernel
private theorem budgetHigh_chunk2470 : total 2470 5 = 6589780015 :=
  by decide +kernel
private theorem budgetHigh_chunk2475 : total 2475 5 = 6556659990 :=
  by decide +kernel
private theorem budgetHigh_chunk2480 : total 2480 5 = 6523539965 :=
  by decide +kernel
private theorem budgetHigh_chunk2485 : total 2485 5 = 6490419940 :=
  by decide +kernel
private theorem budgetHigh_chunk2490 : total 2490 5 = 6457299915 :=
  by decide +kernel
private theorem budgetHigh_chunk2495 : total 2495 5 = 6424179890 :=
  by decide +kernel
theorem window9 : total 2250 250 = 361775827400 := by
  rw [show 250 = 50 * 5 by decide, budgetHigh_total_chunks]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul,
    Nat.reduceAdd, budgetHigh_chunk2250, budgetHigh_chunk2255, budgetHigh_chunk2260, budgetHigh_chunk2265,
    budgetHigh_chunk2270, budgetHigh_chunk2275, budgetHigh_chunk2280, budgetHigh_chunk2285,
    budgetHigh_chunk2290, budgetHigh_chunk2295, budgetHigh_chunk2300, budgetHigh_chunk2305,
    budgetHigh_chunk2310, budgetHigh_chunk2315, budgetHigh_chunk2320, budgetHigh_chunk2325,
    budgetHigh_chunk2330, budgetHigh_chunk2335, budgetHigh_chunk2340, budgetHigh_chunk2345,
    budgetHigh_chunk2350, budgetHigh_chunk2355, budgetHigh_chunk2360, budgetHigh_chunk2365,
    budgetHigh_chunk2370, budgetHigh_chunk2375, budgetHigh_chunk2380, budgetHigh_chunk2385,
    budgetHigh_chunk2390, budgetHigh_chunk2395, budgetHigh_chunk2400, budgetHigh_chunk2405,
    budgetHigh_chunk2410, budgetHigh_chunk2415, budgetHigh_chunk2420, budgetHigh_chunk2425,
    budgetHigh_chunk2430, budgetHigh_chunk2435, budgetHigh_chunk2440, budgetHigh_chunk2445,
    budgetHigh_chunk2450, budgetHigh_chunk2455, budgetHigh_chunk2460, budgetHigh_chunk2465,
    budgetHigh_chunk2470, budgetHigh_chunk2475, budgetHigh_chunk2480, budgetHigh_chunk2485,
    budgetHigh_chunk2490, budgetHigh_chunk2495]
  decide +kernel
private theorem budgetHigh_chunk2500 : total 2500 5 = 6391059865 :=
  by decide +kernel
private theorem budgetHigh_chunk2505 : total 2505 5 = 6357939840 :=
  by decide +kernel
private theorem budgetHigh_chunk2510 : total 2510 5 = 6324819815 :=
  by decide +kernel
private theorem budgetHigh_chunk2515 : total 2515 5 = 6291699790 :=
  by decide +kernel
private theorem budgetHigh_chunk2520 : total 2520 5 = 6258579765 :=
  by decide +kernel
private theorem budgetHigh_chunk2525 : total 2525 5 = 6225459740 :=
  by decide +kernel
private theorem budgetHigh_chunk2530 : total 2530 5 = 6192339715 :=
  by decide +kernel
private theorem budgetHigh_chunk2535 : total 2535 5 = 6159219690 :=
  by decide +kernel
private theorem budgetHigh_chunk2540 : total 2540 5 = 6126099665 :=
  by decide +kernel
private theorem budgetHigh_chunk2545 : total 2545 5 = 6092979640 :=
  by decide +kernel
private theorem budgetHigh_chunk2550 : total 2550 5 = 6059859615 :=
  by decide +kernel
private theorem budgetHigh_chunk2555 : total 2555 5 = 6026739590 :=
  by decide +kernel
private theorem budgetHigh_chunk2560 : total 2560 5 = 5993619565 :=
  by decide +kernel
private theorem budgetHigh_chunk2565 : total 2565 5 = 5960499540 :=
  by decide +kernel
private theorem budgetHigh_chunk2570 : total 2570 5 = 5927379515 :=
  by decide +kernel
private theorem budgetHigh_chunk2575 : total 2575 5 = 5894259490 :=
  by decide +kernel
private theorem budgetHigh_chunk2580 : total 2580 5 = 5861139465 :=
  by decide +kernel
private theorem budgetHigh_chunk2585 : total 2585 5 = 5828019440 :=
  by decide +kernel
private theorem budgetHigh_chunk2590 : total 2590 5 = 5794899415 :=
  by decide +kernel
private theorem budgetHigh_chunk2595 : total 2595 5 = 5761779390 :=
  by decide +kernel
private theorem budgetHigh_chunk2600 : total 2600 5 = 5728659365 :=
  by decide +kernel
private theorem budgetHigh_chunk2605 : total 2605 5 = 5695539340 :=
  by decide +kernel
private theorem budgetHigh_chunk2610 : total 2610 5 = 5662419315 :=
  by decide +kernel
private theorem budgetHigh_chunk2615 : total 2615 5 = 5629299290 :=
  by decide +kernel
private theorem budgetHigh_chunk2620 : total 2620 5 = 5596179265 :=
  by decide +kernel
private theorem budgetHigh_chunk2625 : total 2625 5 = 5563059240 :=
  by decide +kernel
private theorem budgetHigh_chunk2630 : total 2630 5 = 5529939215 :=
  by decide +kernel
private theorem budgetHigh_chunk2635 : total 2635 5 = 5496819190 :=
  by decide +kernel
private theorem budgetHigh_chunk2640 : total 2640 5 = 5463699165 :=
  by decide +kernel
private theorem budgetHigh_chunk2645 : total 2645 5 = 5430579140 :=
  by decide +kernel
private theorem budgetHigh_chunk2650 : total 2650 5 = 5397459115 :=
  by decide +kernel
private theorem budgetHigh_chunk2655 : total 2655 5 = 5364339090 :=
  by decide +kernel
private theorem budgetHigh_chunk2660 : total 2660 5 = 5331219065 :=
  by decide +kernel
private theorem budgetHigh_chunk2665 : total 2665 5 = 5298099040 :=
  by decide +kernel
private theorem budgetHigh_chunk2670 : total 2670 5 = 5264979015 :=
  by decide +kernel
private theorem budgetHigh_chunk2675 : total 2675 5 = 5231858990 :=
  by decide +kernel
private theorem budgetHigh_chunk2680 : total 2680 5 = 5198738965 :=
  by decide +kernel
private theorem budgetHigh_chunk2685 : total 2685 5 = 5165618940 :=
  by decide +kernel
private theorem budgetHigh_chunk2690 : total 2690 5 = 5132498915 :=
  by decide +kernel
private theorem budgetHigh_chunk2695 : total 2695 5 = 5099378890 :=
  by decide +kernel
private theorem budgetHigh_chunk2700 : total 2700 5 = 5066281874 :=
  by decide +kernel
private theorem budgetHigh_chunk2705 : total 2705 5 = 5033305546 :=
  by decide +kernel
private theorem budgetHigh_chunk2710 : total 2710 5 = 5000472624 :=
  by decide +kernel
private theorem budgetHigh_chunk2715 : total 2715 5 = 4967782796 :=
  by decide +kernel
private theorem budgetHigh_chunk2720 : total 2720 5 = 4935235749 :=
  by decide +kernel
private theorem budgetHigh_chunk2725 : total 2725 5 = 4902831171 :=
  by decide +kernel
private theorem budgetHigh_chunk2730 : total 2730 5 = 4870568749 :=
  by decide +kernel
private theorem budgetHigh_chunk2735 : total 2735 5 = 4838448171 :=
  by decide +kernel
private theorem budgetHigh_chunk2740 : total 2740 5 = 4806469124 :=
  by decide +kernel
private theorem budgetHigh_chunk2745 : total 2745 5 = 4774631296 :=
  by decide +kernel
theorem window10 : total 2500 250 = 279004802200 := by
  rw [show 250 = 50 * 5 by decide, budgetHigh_total_chunks]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul,
    Nat.reduceAdd, budgetHigh_chunk2500, budgetHigh_chunk2505, budgetHigh_chunk2510, budgetHigh_chunk2515,
    budgetHigh_chunk2520, budgetHigh_chunk2525, budgetHigh_chunk2530, budgetHigh_chunk2535,
    budgetHigh_chunk2540, budgetHigh_chunk2545, budgetHigh_chunk2550, budgetHigh_chunk2555,
    budgetHigh_chunk2560, budgetHigh_chunk2565, budgetHigh_chunk2570, budgetHigh_chunk2575,
    budgetHigh_chunk2580, budgetHigh_chunk2585, budgetHigh_chunk2590, budgetHigh_chunk2595,
    budgetHigh_chunk2600, budgetHigh_chunk2605, budgetHigh_chunk2610, budgetHigh_chunk2615,
    budgetHigh_chunk2620, budgetHigh_chunk2625, budgetHigh_chunk2630, budgetHigh_chunk2635,
    budgetHigh_chunk2640, budgetHigh_chunk2645, budgetHigh_chunk2650, budgetHigh_chunk2655,
    budgetHigh_chunk2660, budgetHigh_chunk2665, budgetHigh_chunk2670, budgetHigh_chunk2675,
    budgetHigh_chunk2680, budgetHigh_chunk2685, budgetHigh_chunk2690, budgetHigh_chunk2695,
    budgetHigh_chunk2700, budgetHigh_chunk2705, budgetHigh_chunk2710, budgetHigh_chunk2715,
    budgetHigh_chunk2720, budgetHigh_chunk2725, budgetHigh_chunk2730, budgetHigh_chunk2735,
    budgetHigh_chunk2740, budgetHigh_chunk2745]
  decide +kernel
private theorem budgetHigh_chunk2750 : total 2750 25 = 23400509839 :=
  by decide +kernel
private theorem budgetHigh_chunk2775 : total 2775 25 = 22625567261 :=
  by decide +kernel
private theorem budgetHigh_chunk2800 : total 2800 25 = 21867925464 :=
  by decide +kernel
private theorem budgetHigh_chunk2825 : total 2825 25 = 21127389136 :=
  by decide +kernel
private theorem budgetHigh_chunk2850 : total 2850 25 = 20403762964 :=
  by decide +kernel
private theorem budgetHigh_chunk2875 : total 2875 25 = 19696851636 :=
  by decide +kernel
private theorem budgetHigh_chunk2900 : total 2900 25 = 19006459839 :=
  by decide +kernel
private theorem budgetHigh_chunk2925 : total 2925 25 = 18332392261 :=
  by decide +kernel
private theorem budgetHigh_chunk2950 : total 2950 25 = 17674453589 :=
  by decide +kernel
private theorem budgetHigh_chunk2975 : total 2975 25 = 17032448511 :=
  by decide +kernel
theorem window11 : total 2750 250 = 201167760500 := by
  rw [show 250 = 10 * 25 by decide, budgetHigh_total_chunks]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul,
    Nat.reduceAdd, budgetHigh_chunk2750, budgetHigh_chunk2775, budgetHigh_chunk2800, budgetHigh_chunk2825,
    budgetHigh_chunk2850, budgetHigh_chunk2875, budgetHigh_chunk2900, budgetHigh_chunk2925,
    budgetHigh_chunk2950, budgetHigh_chunk2975]
  decide +kernel
private theorem budgetHigh_chunk3000 : total 3000 25 = 16406181714 :=
  by decide +kernel
private theorem budgetHigh_chunk3025 : total 3025 25 = 15795457886 :=
  by decide +kernel
private theorem budgetHigh_chunk3050 : total 3050 25 = 15200081714 :=
  by decide +kernel
private theorem budgetHigh_chunk3075 : total 3075 25 = 14619857886 :=
  by decide +kernel
private theorem budgetHigh_chunk3100 : total 3100 25 = 14054591089 :=
  by decide +kernel
private theorem budgetHigh_chunk3125 : total 3125 25 = 13504086011 :=
  by decide +kernel
private theorem budgetHigh_chunk3150 : total 3150 25 = 12968147339 :=
  by decide +kernel
private theorem budgetHigh_chunk3175 : total 3175 25 = 12446579761 :=
  by decide +kernel
private theorem budgetHigh_chunk3200 : total 3200 25 = 11939187964 :=
  by decide +kernel
private theorem budgetHigh_chunk3225 : total 3225 25 = 11445776636 :=
  by decide +kernel
theorem window12 : total 3000 250 = 138379948000 := by
  rw [show 250 = 10 * 25 by decide, budgetHigh_total_chunks]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul,
    Nat.reduceAdd, budgetHigh_chunk3000, budgetHigh_chunk3025, budgetHigh_chunk3050, budgetHigh_chunk3075,
    budgetHigh_chunk3100, budgetHigh_chunk3125, budgetHigh_chunk3150, budgetHigh_chunk3175,
    budgetHigh_chunk3200, budgetHigh_chunk3225]
  decide +kernel
private theorem budgetHigh_chunk3250 : total 3250 25 = 10966150464 :=
  by decide +kernel
private theorem budgetHigh_chunk3275 : total 3275 25 = 10500114136 :=
  by decide +kernel
private theorem budgetHigh_chunk3300 : total 3300 25 = 10047472339 :=
  by decide +kernel
private theorem budgetHigh_chunk3325 : total 3325 25 = 9608029761 :=
  by decide +kernel
private theorem budgetHigh_chunk3350 : total 3350 25 = 9181591089 :=
  by decide +kernel
private theorem budgetHigh_chunk3375 : total 3375 25 = 8767961011 :=
  by decide +kernel
private theorem budgetHigh_chunk3400 : total 3400 25 = 8366944214 :=
  by decide +kernel
private theorem budgetHigh_chunk3425 : total 3425 25 = 7978345386 :=
  by decide +kernel
private theorem budgetHigh_chunk3450 : total 3450 25 = 7601969214 :=
  by decide +kernel
private theorem budgetHigh_chunk3475 : total 3475 25 = 7237620386 :=
  by decide +kernel
theorem window13 : total 3250 250 = 90256198000 := by
  rw [show 250 = 10 * 25 by decide, budgetHigh_total_chunks]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul,
    Nat.reduceAdd, budgetHigh_chunk3250, budgetHigh_chunk3275, budgetHigh_chunk3300, budgetHigh_chunk3325,
    budgetHigh_chunk3350, budgetHigh_chunk3375, budgetHigh_chunk3400, budgetHigh_chunk3425,
    budgetHigh_chunk3450, budgetHigh_chunk3475]
  decide +kernel
private theorem budgetHigh_chunk3500 : total 3500 25 = 6885103589 :=
  by decide +kernel
private theorem budgetHigh_chunk3525 : total 3525 25 = 6544223511 :=
  by decide +kernel
private theorem budgetHigh_chunk3550 : total 3550 25 = 6214784839 :=
  by decide +kernel
private theorem budgetHigh_chunk3575 : total 3575 25 = 5896592261 :=
  by decide +kernel
private theorem budgetHigh_chunk3600 : total 3600 25 = 5589450464 :=
  by decide +kernel
private theorem budgetHigh_chunk3625 : total 3625 25 = 5293164136 :=
  by decide +kernel
private theorem budgetHigh_chunk3650 : total 3650 25 = 5007537964 :=
  by decide +kernel
private theorem budgetHigh_chunk3675 : total 3675 25 = 4732376636 :=
  by decide +kernel
private theorem budgetHigh_chunk3700 : total 3700 25 = 4467484839 :=
  by decide +kernel
private theorem budgetHigh_chunk3725 : total 3725 25 = 4212667261 :=
  by decide +kernel
theorem window14 : total 3500 250 = 54843385500 := by
  rw [show 250 = 10 * 25 by decide, budgetHigh_total_chunks]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul,
    Nat.reduceAdd, budgetHigh_chunk3500, budgetHigh_chunk3525, budgetHigh_chunk3550, budgetHigh_chunk3575,
    budgetHigh_chunk3600, budgetHigh_chunk3625, budgetHigh_chunk3650, budgetHigh_chunk3675,
    budgetHigh_chunk3700, budgetHigh_chunk3725]
  decide +kernel
private theorem budgetHigh_chunk3750 : total 3750 25 = 3967728589 :=
  by decide +kernel
private theorem budgetHigh_chunk3775 : total 3775 25 = 3732473511 :=
  by decide +kernel
private theorem budgetHigh_chunk3800 : total 3800 25 = 3506706714 :=
  by decide +kernel
private theorem budgetHigh_chunk3825 : total 3825 25 = 3290232886 :=
  by decide +kernel
private theorem budgetHigh_chunk3850 : total 3850 25 = 3082856714 :=
  by decide +kernel
private theorem budgetHigh_chunk3875 : total 3875 25 = 2884382886 :=
  by decide +kernel
private theorem budgetHigh_chunk3900 : total 3900 25 = 2694616089 :=
  by decide +kernel
private theorem budgetHigh_chunk3925 : total 3925 25 = 2513361011 :=
  by decide +kernel
private theorem budgetHigh_chunk3950 : total 3950 25 = 2340422339 :=
  by decide +kernel
private theorem budgetHigh_chunk3975 : total 3975 25 = 2175604761 :=
  by decide +kernel
theorem window15 : total 3750 250 = 30188385500 := by
  rw [show 250 = 10 * 25 by decide, budgetHigh_total_chunks]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul,
    Nat.reduceAdd, budgetHigh_chunk3750, budgetHigh_chunk3775, budgetHigh_chunk3800, budgetHigh_chunk3825,
    budgetHigh_chunk3850, budgetHigh_chunk3875, budgetHigh_chunk3900, budgetHigh_chunk3925,
    budgetHigh_chunk3950, budgetHigh_chunk3975]
  decide +kernel
private theorem budgetHigh_chunk4000 : total 4000 25 = 2018712964 :=
  by decide +kernel
private theorem budgetHigh_chunk4025 : total 4025 25 = 1869551636 :=
  by decide +kernel
private theorem budgetHigh_chunk4050 : total 4050 25 = 1727925464 :=
  by decide +kernel
private theorem budgetHigh_chunk4075 : total 4075 25 = 1593639136 :=
  by decide +kernel
private theorem budgetHigh_chunk4100 : total 4100 25 = 1466497339 :=
  by decide +kernel
private theorem budgetHigh_chunk4125 : total 4125 25 = 1346304761 :=
  by decide +kernel
private theorem budgetHigh_chunk4150 : total 4150 25 = 1232866089 :=
  by decide +kernel
private theorem budgetHigh_chunk4175 : total 4175 25 = 1125986011 :=
  by decide +kernel
private theorem budgetHigh_chunk4200 : total 4200 25 = 1025469214 :=
  by decide +kernel
private theorem budgetHigh_chunk4225 : total 4225 25 = 931120386 :=
  by decide +kernel
theorem window16 : total 4000 250 = 14338073000 := by
  rw [show 250 = 10 * 25 by decide, budgetHigh_total_chunks]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul,
    Nat.reduceAdd, budgetHigh_chunk4000, budgetHigh_chunk4025, budgetHigh_chunk4050, budgetHigh_chunk4075,
    budgetHigh_chunk4100, budgetHigh_chunk4125, budgetHigh_chunk4150, budgetHigh_chunk4175,
    budgetHigh_chunk4200, budgetHigh_chunk4225]
  decide +kernel
private theorem budgetHigh_chunk4250 : total 4250 25 = 842744214 :=
  by decide +kernel
private theorem budgetHigh_chunk4275 : total 4275 25 = 760145386 :=
  by decide +kernel
private theorem budgetHigh_chunk4300 : total 4300 25 = 683128589 :=
  by decide +kernel
private theorem budgetHigh_chunk4325 : total 4325 25 = 611498511 :=
  by decide +kernel
private theorem budgetHigh_chunk4350 : total 4350 25 = 545059839 :=
  by decide +kernel
private theorem budgetHigh_chunk4375 : total 4375 25 = 483617261 :=
  by decide +kernel
private theorem budgetHigh_chunk4400 : total 4400 25 = 426975464 :=
  by decide +kernel
private theorem budgetHigh_chunk4425 : total 4425 25 = 374939136 :=
  by decide +kernel
private theorem budgetHigh_chunk4450 : total 4450 25 = 327312964 :=
  by decide +kernel
private theorem budgetHigh_chunk4475 : total 4475 25 = 283901636 :=
  by decide +kernel
theorem window17 : total 4250 250 = 5339323000 := by
  rw [show 250 = 10 * 25 by decide, budgetHigh_total_chunks]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul,
    Nat.reduceAdd, budgetHigh_chunk4250, budgetHigh_chunk4275, budgetHigh_chunk4300, budgetHigh_chunk4325,
    budgetHigh_chunk4350, budgetHigh_chunk4375, budgetHigh_chunk4400, budgetHigh_chunk4425,
    budgetHigh_chunk4450, budgetHigh_chunk4475]
  decide +kernel
private theorem budgetHigh_chunk4500 : total 4500 25 = 244509839 :=
  by decide +kernel
private theorem budgetHigh_chunk4525 : total 4525 25 = 208942261 :=
  by decide +kernel
private theorem budgetHigh_chunk4550 : total 4550 25 = 177003589 :=
  by decide +kernel
private theorem budgetHigh_chunk4575 : total 4575 25 = 148498511 :=
  by decide +kernel
private theorem budgetHigh_chunk4600 : total 4600 25 = 123231714 :=
  by decide +kernel
private theorem budgetHigh_chunk4625 : total 4625 25 = 101007886 :=
  by decide +kernel
private theorem budgetHigh_chunk4650 : total 4650 25 = 81631714 :=
  by decide +kernel
private theorem budgetHigh_chunk4675 : total 4675 25 = 64907886 :=
  by decide +kernel
private theorem budgetHigh_chunk4700 : total 4700 25 = 50641089 :=
  by decide +kernel
private theorem budgetHigh_chunk4725 : total 4725 25 = 38636011 :=
  by decide +kernel
theorem window18 : total 4500 250 = 1239010500 := by
  rw [show 250 = 10 * 25 by decide, budgetHigh_total_chunks]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul,
    Nat.reduceAdd, budgetHigh_chunk4500, budgetHigh_chunk4525, budgetHigh_chunk4550, budgetHigh_chunk4575,
    budgetHigh_chunk4600, budgetHigh_chunk4625, budgetHigh_chunk4650, budgetHigh_chunk4675,
    budgetHigh_chunk4700, budgetHigh_chunk4725]
  decide +kernel
private theorem budgetHigh_chunk4750 : total 4750 25 = 28697339 :=
  by decide +kernel
private theorem budgetHigh_chunk4775 : total 4775 25 = 20629761 :=
  by decide +kernel
private theorem budgetHigh_chunk4800 : total 4800 25 = 14237964 :=
  by decide +kernel
private theorem budgetHigh_chunk4825 : total 4825 25 = 9326636 :=
  by decide +kernel
private theorem budgetHigh_chunk4850 : total 4850 25 = 5700464 :=
  by decide +kernel
private theorem budgetHigh_chunk4875 : total 4875 25 = 3164136 :=
  by decide +kernel
private theorem budgetHigh_chunk4900 : total 4900 25 = 1522339 :=
  by decide +kernel
private theorem budgetHigh_chunk4925 : total 4925 25 = 579761 :=
  by decide +kernel
private theorem budgetHigh_chunk4950 : total 4950 25 = 141089 :=
  by decide +kernel
private theorem budgetHigh_chunk4975 : total 4975 25 = 11011 :=
  by decide +kernel
theorem window19 : total 4750 250 = 84010500 := by
  rw [show 250 = 10 * 25 by decide, budgetHigh_total_chunks]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul,
    Nat.reduceAdd, budgetHigh_chunk4750, budgetHigh_chunk4775, budgetHigh_chunk4800, budgetHigh_chunk4825,
    budgetHigh_chunk4850, budgetHigh_chunk4875, budgetHigh_chunk4900, budgetHigh_chunk4925,
    budgetHigh_chunk4950, budgetHigh_chunk4975]
  decide +kernel
end K1_13_4_2_2_5
end
section
namespace K1_13_4_2_2_5
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private theorem lowCostShift (a d : ℤ) :
    cost (a + 2*d) = cost a + d*(a+1) + d^2 := by
  have h : (a+1)/2 + (a/2+1) = a+1 := by omega
  unfold cost
  rw [show (a+2*d+1)/2 = (a+1)/2+d by omega,
      show (a+2*d)/2 = a/2+d by omega]
  linear_combination d * h
private theorem lowCostOdd (x : ℤ) : cost (2*x-1) = x^2 := by
  unfold cost
  rw [show (2*x-1+1)/2 = x by omega, show (2*x-1)/2 = x-1 by omega]
  ring
private theorem lowRankBoth (k t : ℤ) :
    shiftedRank true k t = columns k - (1151+k-t)^2 := by
  change columns k + cost (2300-k-2*(t-2*k-1)-(2*t-2301-k)) +
    cost (t-(t-2*k-1)-2*(2*t-2301-k)) - (1151-(t-2*k-1)-(2*t-2301-k))^2 = _
  rw [show 2300-k-2*(t-2*k-1)-(2*t-2301-k) = 2*(2*(1151+k-t))-1 by ring,
      show t-(t-2*k-1)-2*(2*t-2301-k) = 2*(2*(1151+k-t))-1 by ring,
      lowCostOdd]
  ring
private theorem lowRankOneCol (k t : ℤ) :
    shiftedRank false k t = columns k - (1151+k-t)^2 + cost (linearPower k t-1) := by
  change columns k + cost (2300-k-2*0-(2*t-2301-k)) +
    cost (t-0-2*(2*t-2301-k)) - (1151-0-(2*t-2301-k))^2 = _
  rw [show 2300-k-2*0-(2*t-2301-k) = 2*(2301-t)-1 by ring, lowCostOdd,
      show t-0-2*(2*t-2301-k) = (linearPower k t-1) + 2*(2*(1151+k-t)) by
        unfold linearPower; ring, lowCostShift]
  unfold linearPower
  ring
private theorem lowRankOneEmpty (k t : ℤ) (hk : k ≤ 2300) :
    shiftedRank false k t = cost t - cost (conicPower k t-1) := by
  change columns k + cost (2300-k-2*0-(2*t-2301-k)) +
    cost (t-0-2*(2*t-2301-k)) - (1151-0-(2*t-2301-k))^2 = _
  rw [show 2300-k-2*0-(2*t-2301-k) = 2*(2301-t)-1 by ring, lowCostOdd,
      show t-0-2*(2*t-2301-k) = t+2*(-(2*t-2301-k)) by ring, lowCostShift,
      show conicPower k t-1 = (2300-k)+2*(t-2301) by unfold conicPower; ring,
      lowCostShift]
  unfold columns
  rw [max_eq_right (by omega)]
  ring
private theorem lowGain (z : ℤ) (hz : 0 ≤ z) :
    0 ≤ cost (z-1) ∧ (0 < cost (z-1) ↔ 2 ≤ z) := by
  unfold cost
  have ha : 0 ≤ (z-1+1)/2 := by omega
  have hb : 0 ≤ (z-1)/2+1 := by omega
  constructor
  · exact mul_nonneg ha hb
  · by_cases h : 2 ≤ z
    · exact iff_of_true (mul_pos (by omega) (by omega)) h
    · rw [show (z-1+1)/2 = 0 by omega, zero_mul]
      omega
private theorem lowGainLtSq (d q : ℤ) (hd : d ≤ 0) (h : -d < 2*q) :
    cost (d-1) < q^2 := by
  unfold cost
  have ha : 0 ≤ -((d-1+1)/2) := by omega
  have hb : 0 ≤ -((d-1)/2+1) := by omega
  have hl : -((d-1+1)/2) ≤ q := by omega
  have hr : -((d-1)/2+1) < q := by omega
  have hp : 0 < q := by omega
  have h₁ := mul_le_mul_of_nonneg_right hl hb
  have h₂ := mul_lt_mul_of_pos_left hr hp
  nlinarith only [h₁, h₂]
private theorem lowShiftTest (k t : ℤ) (hk : k ≤ 2300) :
    (admissible (decide (0 < linearPower k t)) k t t ∧
      shiftedRank (decide (0 < linearPower k t)) k t < min (columns k) (cost t)) ↔
    2301+k ≤ 2*t ∧ t ≤ 2300 ∧ t ≤ k+1150 ∧ (2303+k ≤ 2*t ∨ 2*k+3 ≤ t) := by
  have hAdm : ∀ b : Bool, (b = decide (0 < linearPower k t)) →
      (admissible b k t t ↔ 2301+k ≤ 2*t ∧ t ≤ 2300 ∧ t ≤ k+1150) := by
    intro b hb
    cases b <;> simp [admissible, linearAt, linearPower, conicPower] at hb ⊢ <;> omega
  by_cases hb : 0 < linearPower k t
  · rw [decide_eq_true hb, hAdm true (by simp [hb])]
    constructor
    · rintro ⟨ha, hr⟩
      have hm := lowGain (conicPower k t) (by unfold conicPower; omega)
      have hn := lowGain (linearPower k t) (by omega)
      have h₁ := lowRankBoth k t
      have h₂ := lowRankOneCol k t
      have h₃ := lowRankOneEmpty k t hk
      have he := lt_of_lt_of_le hr (min_le_right _ _)
      unfold linearPower conicPower at *
      exact ⟨ha.1, ha.2.1, ha.2.2, by omega⟩
    · rintro ⟨h₁,h₂,h₃,h₄⟩
      refine ⟨⟨h₁,h₂,h₃⟩, lt_min ?_ ?_⟩
      · rw [lowRankBoth]
        have hq : 0 < 1151+k-t := by omega
        have hp := mul_pos hq hq
        nlinarith only [hp]
      · have hm := lowGain (conicPower k t) (by unfold conicPower; omega)
        have hn := lowGain (linearPower k t) (by omega)
        have e₁ := lowRankBoth k t
        have e₂ := lowRankOneCol k t
        have e₃ := lowRankOneEmpty k t hk
        unfold linearPower conicPower at *
        omega
  · rw [decide_eq_false hb, hAdm false (by simp [hb])]
    constructor
    · rintro ⟨ha, hr⟩
      have hm := lowGain (conicPower k t) (by unfold conicPower; omega)
      have he := lt_of_lt_of_le hr (min_le_right _ _)
      rw [lowRankOneEmpty k t hk] at he
      unfold conicPower at *
      exact ⟨ha.1, ha.2.1, ha.2.2, Or.inl (by omega)⟩
    · rintro ⟨h₁,h₂,h₃,h₄⟩
      refine ⟨⟨h₁,h₂,h₃⟩, lt_min ?_ ?_⟩
      · rw [lowRankOneCol]
        have hg := lowGainLtSq (linearPower k t) (1151+k-t)
          (by omega) (by unfold linearPower; omega)
        omega
      · rw [lowRankOneEmpty k t hk]
        have hm := lowGain (conicPower k t) (by unfold conicPower; omega)
        unfold linearPower conicPower at *
        omega
private def lowBegin (k : ℕ) := max ((k+2302)/2) (min ((k+2304)/2) (2*k+3))
private def lowEnd (k : ℕ) := min 2301 (k+1151)
private def lowMiddle (k : ℕ) := min (2*k+2) (lowEnd k)
private def lowMode (a b c t : ℕ) : Mode :=
  if t < a then .empty else if t < b then .shifted false
  else if t < c then .shifted true else .columns
private abbrev lowGood (k : ℕ) : Prop :=
  k ≤ 2249 ∧ (lowBegin k ≤ 2301-k ∨ cost ((lowBegin k : ℤ)-1) < columns k) ∧
    columns k ≤ cost ((max (2301-k) (lowEnd k) : ℕ) : ℤ)
private theorem lowCostMono {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) : cost a ≤ cost b := by
  unfold cost
  exact mul_le_mul (by omega) (by omega) (by omega) (by omega)
private theorem lowMode_correct (k t : ℕ) (hg : lowGood k) (ht : 2301-k ≤ t) :
    chooseMode k t = lowMode (lowBegin k) (lowMiddle k) (lowEnd k) t := by
  obtain ⟨hk,hlo,hhi⟩ := hg
  unfold chooseMode
  dsimp only
  simp only [lowShiftTest (k : ℤ) t (by omega)]
  by_cases ha : t < lowBegin k
  · have hlt : cost (t : ℤ) < columns k := by
      rcases hlo with h | h
      · omega
      · exact lt_of_le_of_lt (lowCostMono (by positivity) (by omega)) h
    have he : ¬ (2301+(k : ℤ) ≤ 2*(t : ℤ) ∧ (t : ℤ) ≤ 2300 ∧ (t : ℤ) ≤ (k : ℤ)+1150 ∧
        (2303+(k : ℤ) ≤ 2*(t : ℤ) ∨ 2*(k : ℤ)+3 ≤ (t : ℤ))) := by
      unfold lowBegin at ha; omega
    simp [not_le.mpr hlt, lowMode, ha]
    omega
  · by_cases hc : t < lowEnd k
    · have hs : 2301+(k : ℤ) ≤ 2*(t : ℤ) ∧ (t : ℤ) ≤ 2300 ∧ (t : ℤ) ≤ (k : ℤ)+1150 ∧
          (2303+(k : ℤ) ≤ 2*(t : ℤ) ∨ 2*(k : ℤ)+3 ≤ (t : ℤ)) := by
        unfold lowBegin at ha; unfold lowEnd at hc; omega
      by_cases hb : t < lowMiddle k
      · have hp : ¬ 0 < linearPower k t := by
          unfold lowMiddle at hb; unfold linearPower; omega
        simp [hs, hp, lowMode, ha, hb]
      · have hp : 0 < linearPower k t := by
          unfold lowMiddle at hb; unfold linearPower; omega
        simp [hs, hp, lowMode, ha, hb, hc]
    · have he : ¬ (2301+(k : ℤ) ≤ 2*(t : ℤ) ∧ (t : ℤ) ≤ 2300 ∧ (t : ℤ) ≤ (k : ℤ)+1150 ∧
          (2303+(k : ℤ) ≤ 2*(t : ℤ) ∨ 2*(k : ℤ)+3 ≤ (t : ℤ))) := by
        unfold lowEnd at hc; omega
      have hle := hhi.trans (lowCostMono (b := (t : ℤ)) (by positivity) (by omega))
      have hb : ¬t < lowMiddle k := by unfold lowMiddle; omega
      simp [hle, lowMode, ha, hb, hc]
      omega
private def lowWidth (a b c t n : ℕ) : ℕ :=
  if t < a then min n ((a+1-t)/2)
  else if t < b then min n ((b+1-t)/2)
  else if t < c then min n ((c+1-t)/2)
  else n
private theorem lowWidth_le (a b c t n : ℕ) : lowWidth a b c t n ≤ n := by
  unfold lowWidth
  split_ifs <;> omega
private theorem lowWidth_mem (a b c t n i : ℕ) (hi : i < n) :
    (lowMode a b c (t+2*i) = lowMode a b c t) ↔ i < lowWidth a b c t n := by
  unfold lowWidth lowMode
  split_ifs <;> simp_all <;> omega
private theorem lowEndpoint (k t : ℤ) (mode : Mode) (n w : ℕ)
    (cut : ∀ i : ℕ, i < n → (chooseMode k (t+2*i) = mode ↔ i < w))
    (fuel lo hi : ℕ) (hl : lo < w) (hr : w ≤ hi) (hn : hi < n)
    (hspan : hi-lo ≤ 2^fuel) : endpoint k t mode fuel lo hi = w-1 := by
  induction fuel generalizing lo hi with
  | zero => simp only [endpoint]; simp only [pow_zero] at hspan; omega
  | succ f ih =>
    rw [endpoint]
    split
    · omega
    · dsimp only
      have hm := cut ((lo+hi)/2) (by omega)
      rw [pow_succ] at hspan
      split
      · rename_i h
        have hh := hm.mp h
        apply ih <;> omega
      · rename_i h
        have hh := mt hm.mpr h
        apply ih <;> omega
private theorem lowLength (k t : ℤ) (mode : Mode) (n w : ℕ) (hn : 0 < n) (hcap : n ≤ 4096)
    (hw : w ≤ n) (hw₀ : 0 < w)
    (cut : ∀ i : ℕ, i < n → (chooseMode k (t+2*i) = mode ↔ i < w)) :
    runLength k t n mode = w := by
  unfold runLength
  rw [show (n : ℤ)-1 = ((n-1 : ℕ) : ℤ) by omega]
  have he := cut (n-1) (by omega)
  split
  · rename_i h
    have hh := he.mp h
    omega
  · rename_i h
    have hh := mt he.mpr h
    rw [lowEndpoint k t mode n w cut 12 0 (n-1) hw₀ (by omega) (by omega)
          (by change n-1-0 ≤ 4096; omega)]
    omega
private theorem lowAdmissible {k t : ℤ} {b : Bool} (h : chooseMode k t = .shifted b) :
    admissible b k t t := by
  unfold chooseMode at h
  dsimp only at h
  split at h
  next hs => cases h; exact hs.1
  next => split at h <;> contradiction
private theorem lowValid {k l r : ℤ} {mode : Mode}
    (hl : chooseMode k l = mode) (hr : chooseMode k r = mode) : valid mode k l r := by
  cases mode with
  | columns | empty => trivial
  | shifted b =>
    have h₁ := lowAdmissible hl
    have h₂ := lowAdmissible hr
    cases b <;> simp [admissible, valid] at h₁ h₂ ⊢ <;> tauto
private def lowNatCost (t : ℕ) := ((t+1)/2)*(t/2+1)
private def lowNatGain (t : ℕ) := (t/2)*((t+1)/2)
private def lowNatCol (k : ℕ) := 1324801 - lowNatCost (2300-k)
private def lowLin (n : ℕ) := n*(n-1)/2
private def lowSq (n : ℕ) := n*(n-1)*(2*n-1)/6
private theorem lowNatCost_eq (t : ℕ) : (lowNatCost t : ℤ) = cost t := by
  simp [lowNatCost, cost, Int.natCast_ediv]
private theorem lowNatGain_eq (t : ℕ) : (lowNatGain t : ℤ) = cost ((t : ℤ)-1) := by
  simp [lowNatGain, cost, Int.natCast_ediv, show ((t : ℤ)-1)/2+1 = ((t : ℤ)+1)/2 by omega]
private theorem lowNatCol_eq (k : ℕ) (hk : k ≤ 2249) :
    (lowNatCol k : ℤ) = columns k := by
  have hm := lowCostMono (a := ((2300-k : ℕ) : ℤ)) (b := 2300) (by positivity) (by omega)
  rw [← lowNatCost_eq] at hm
  have hd : cost 2300 ≤ 1324801 := by decide
  have hc : lowNatCost (2300-k) ≤ 1324801 := by omega
  simp [lowNatCol, columns, Nat.cast_sub hc, lowNatCost_eq,
    Nat.cast_sub (by omega : k ≤ 2300), max_eq_right (by omega : (0:ℤ) ≤ 2300-k)]
private theorem lowLin_eq (n : ℕ) (hn : 0 < n) : (lowLin n : ℤ) = linearSum n := by
  simp [lowLin, linearSum, Int.natCast_ediv, Nat.cast_sub (by omega : 1 ≤ n)]
private theorem lowSq_eq (n : ℕ) (hn : 0 < n) : (lowSq n : ℤ) = squareSum n := by
  simp [lowSq, squareSum, Int.natCast_ediv, Nat.cast_sub (by omega : 1 ≤ n),
    Nat.cast_sub (by omega : 1 ≤ 2*n)]
private theorem lowSumBoth (k t : ℤ) (n : ℕ) :
    modeSum (.shifted true) k t n =
      (n : ℤ)*columns k - sumSquare (1151+k-t) (-2) n := by
  have h := lowRankBoth k t
  simp [modeSum, shiftedRank, linearAt, sumCost, sumSquare, linearPower, conicPower] at h ⊢
  linear_combination (n : ℤ) * h
private theorem lowSumOne (k t : ℤ) (n : ℕ) (hk : k ≤ 2300) :
    modeSum (.shifted false) k t n =
      sumCost t 1 n - sumCost (conicPower k t-1) 2 n := by
  have h := lowRankOneEmpty k t hk
  simp [modeSum, shiftedRank, linearAt, sumCost, sumSquare, conicPower] at h ⊢
  linear_combination (n : ℤ) * h
private def lowCharge (mode : Mode) (k t w : ℕ) : ℤ :=
  let l := lowLin w
  let s := lowSq w
  let col := w*lowNatCol k
  let e := w*lowNatCost t+(t+1)*l+s
  match mode with
  | .columns => (col : ℤ)
  | .empty => (e : ℤ)
  | .shifted false =>
    let m := 2*t-(2301+k)
    (e : ℤ) - ((w*lowNatGain m + 2*m*l + 4*s : ℕ) : ℤ)
  | .shifted true =>
    let q := 1151+k-t
    ((col+4*q*l : ℕ) : ℤ) - ((w*q^2 + 4*s : ℕ) : ℤ)
private theorem lowCharge_eq (k t w : ℕ) (hk : k ≤ 2249) (hw : 0 < w)
    (mode : Mode) (hm : chooseMode k t = mode) : modeSum mode k t w = lowCharge mode k t w := by
  cases mode with
  | columns => simp [lowCharge, modeSum, lowNatCol_eq k hk]
  | empty => simp [lowCharge, modeSum, sumCost, lowNatCost_eq, lowLin_eq w hw, lowSq_eq w hw]
  | shifted b =>
    have ha := lowAdmissible hm
    cases b with
    | false =>
      have h : 2301+k ≤ 2*t := by simp [admissible, conicPower] at ha; omega
      rw [lowSumOne _ _ _ (by omega)]
      simp [lowCharge, sumCost, lowNatCost_eq, lowNatGain_eq, lowLin_eq w hw, lowSq_eq w hw,
        Nat.cast_sub h, conicPower]
      ring_nf
    | true =>
      have h : t ≤ 1151+k := by
        simp [admissible, linearAt, linearPower, conicPower] at ha; omega
      rw [lowSumBoth]
      simp [lowCharge, sumSquare, lowNatCol_eq k hk, lowLin_eq w hw, lowSq_eq w hw, Nat.cast_sub h]
      ring
private def lowParity (k a b c : ℕ) : ℕ → ℕ → ℕ → ℤ
  | 0, _, n => (n : ℤ) * columns k
  | fuel+1, t, n =>
    if n = 0 then 0 else
      let mode := lowMode a b c t
      let w := lowWidth a b c t n
      lowCharge mode k t w + lowParity k a b c fuel (t+2*w) (n-w)
private theorem lowParity_eq (k : ℕ) (hg : lowGood k) (fuel t n : ℕ)
    (ht : 2301-k ≤ t) (hcap : n ≤ 4096) :
    parityBound k fuel t n = lowParity k (lowBegin k) (lowMiddle k) (lowEnd k) fuel t n := by
  let a := lowBegin k
  let b := lowMiddle k
  let c := lowEnd k
  change parityBound k fuel t n = lowParity k a b c fuel t n
  induction fuel generalizing t n with
  | zero => rfl
  | succ f ih =>
    by_cases hn : n=0
    · simp [parityBound, lowParity, hn]
    · let w := lowWidth a b c t n
      let m := lowMode a b c t
      have hm : chooseMode k t = m := lowMode_correct k t hg ht
      have cut (i : ℕ) (hi : i < n) : chooseMode k ((t : ℤ)+2*i) = m ↔ i < w := by
        have hx := lowMode_correct k (t+2*i) hg (by omega)
        push_cast at hx
        rw [hx]
        exact lowWidth_mem a b c t n i hi
      have hw₀ : 0 < w := (cut 0 (by omega)).1 (by simpa using hm)
      have hw := lowLength (k : ℤ) (t : ℤ) m n w (by omega) hcap (lowWidth_le ..) hw₀ cut
      have hlast := (cut (w-1) (by have := lowWidth_le a b c t n; dsimp [w]; omega)).2 (by omega)
      rw [show ((w-1 : ℕ) : ℤ) = (w : ℤ)-1 by omega] at hlast
      have hv := lowValid hm hlast
      have hcharge := lowCharge_eq k t w hg.1 hw₀ m hm
      have tail := ih (t+2*w) (n-w) (by omega) (by omega)
      push_cast at tail
      simp only [parityBound, lowParity, ite_eq_right hn, hm, hw, ite_eq_left hv, hcharge]
      exact congrArg (_ + ·) tail
private abbrev lowGoodN (k : ℕ) : Prop :=
  k ≤ 2249 ∧ (lowBegin k ≤ 2301-k ∨ lowNatCost (lowBegin k-1) < lowNatCol k) ∧
    lowNatCol k ≤ lowNatCost (max (2301-k) (lowEnd k))
private theorem lowGood_of_nat {k : ℕ} (h : lowGoodN k) : lowGood k := by
  obtain ⟨hk, hlo, hhi⟩ := h
  refine ⟨hk, ?_, ?_⟩
  · rcases hlo with hl | hl
    · exact Or.inl hl
    · apply Or.inr
      have hcast : ((lowNatCost (lowBegin k-1) : ℕ) : ℤ) < lowNatCol k := by exact_mod_cast hl
      rw [lowNatCost_eq, lowNatCol_eq k hk] at hcast
      have hab : 1 ≤ lowBegin k := by unfold lowBegin; omega
      simpa only [Nat.cast_sub hab, Nat.cast_one] using hcast
  · have hcast : (lowNatCol k : ℤ) ≤ lowNatCost (max (2301-k) (lowEnd k)) := by exact_mod_cast hhi
    simpa only [lowNatCol_eq k hk, lowNatCost_eq] using hcast
private def lowStep (k : ℕ) (m : Mode) (u : ℕ) (next : ℕ → ℕ → ℤ) (t n : ℕ) : ℤ :=
  if n = 0 then 0 else
  if t < u then
    let w := min n ((u+1-t)/2)
    if w = n then lowCharge m k t n
    else lowCharge m k t w + next (t+2*w) (n-w)
  else next t n
private theorem lowParity_zero (k a b c f t : ℕ) : lowParity k a b c f t 0 = 0 := by
  cases f <;> simp [lowParity]
private theorem lowStep_eq (k a b c t n u f : ℕ) (m : Mode) (next : ℕ → ℕ → ℤ)
    (hm : t < u → lowMode a b c t = m)
    (hw : t < u → lowWidth a b c t n = min n ((u+1-t)/2))
    (skip : u ≤ t → lowParity k a b c (f+1) t n = next t n)
    (tail : ∀ w, u ≤ t+2*w → lowParity k a b c f (t+2*w) (n-w) = next (t+2*w) (n-w)) :
    lowParity k a b c (f+1) t n = lowStep k m u next t n := by
  by_cases hn : n=0
  · simp [hn, lowStep, lowParity_zero]
  by_cases hu : t < u
  · simp only [lowStep, lowParity, ite_eq_right hn, ite_eq_left hu, hm hu, hw hu]
    split
    · rename_i h
      simp only [h, Nat.sub_self, lowParity_zero, add_zero]
    · rename_i h
      rw [tail _ (by omega)]
  · simpa only [lowStep, ite_eq_right hn, ite_eq_right hu] using skip (by omega)
private theorem lowLast (k a b c t n f : ℕ) (ha : a ≤ t) (hb : b ≤ t) (hc : c ≤ t) :
    lowParity k a b c (f+1) t n = lowCharge .columns k t n := by
  by_cases hn : n=0
  · simp [hn, lowCharge, lowParity_zero]
  · simp [lowParity, hn, lowMode, lowWidth, not_lt.mpr ha, not_lt.mpr hb,
      not_lt.mpr hc, lowParity_zero]
private def lowTwo (k c : ℕ) :=
  lowStep k (.shifted true) c (lowCharge .columns k)
private theorem lowTwo_eq (k a b c t n f : ℕ) (ha : a ≤ t) (hb : b ≤ t) :
    lowParity k a b c (f+2) t n = lowTwo k c t n := by
  apply lowStep_eq
  · intro hc; simp [lowMode, not_lt.mpr ha, not_lt.mpr hb, hc]
  · intro hc; simp [lowWidth, not_lt.mpr ha, not_lt.mpr hb, hc]
  · exact lowLast k a b c t n (f+1) ha hb
  · intro w hc; exact lowLast _ _ _ _ _ _ f (by omega) (by omega) hc
private def lowOne (k b c : ℕ) := lowStep k (.shifted false) b (lowTwo k c)
private theorem lowOne_eq (k a b c t n f : ℕ) (ha : a ≤ t) :
    lowParity k a b c (f+3) t n = lowOne k b c t n := by
  apply lowStep_eq
  · intro hb; simp [lowMode, not_lt.mpr ha, hb]
  · intro hb; simp [lowWidth, not_lt.mpr ha, hb]
  · exact lowTwo_eq k a b c t n (f+1) ha
  · intro w hb; exact lowTwo_eq _ _ _ _ _ _ f (by omega) hb
private def lowFour (k a b c : ℕ) := lowStep k .empty a (lowOne k b c)
private theorem lowFour_eq (k a b c t n f : ℕ) :
    lowParity k a b c (f+4) t n = lowFour k a b c t n := by
  apply lowStep_eq
  · intro ha; simp [lowMode, ha]
  · intro ha; simp [lowWidth, ha]
  · exact lowOne_eq k a b c t n (f+1)
  · intro w ha; exact lowOne_eq _ _ _ _ _ _ f ha
private def lowOffset (k : ℕ) : ℤ :=
  if lowGoodN k then
    let a := lowBegin k; let b := lowMiddle k; let c := lowEnd k
    lowFour k a b c (2301-k) 1350 + lowFour k a b c (2302-k) 1350
  else offsetTotal k
private theorem lowOffset_eq (k : ℕ) : offsetTotal k = lowOffset k := by
  unfold lowOffset
  split
  · rename_i hn
    have hg := lowGood_of_nat hn
    have hk := hg.1
    unfold offsetTotal
    rw [min_eq_left (by omega : 2700 ≤ 5000-k)]
    change parityBound k 8 (5001-(k : ℤ)-2700) 1350 +
      parityBound k 8 (5001-(k : ℤ)-2700+1) 1350 = _
    rw [show 5001-(k : ℤ)-2700+1 = ((2302-k : ℕ) : ℤ) by omega,
        show 5001-(k : ℤ)-2700 = ((2301-k : ℕ) : ℤ) by omega,
        lowParity_eq k hg 8 (2301-k) 1350 (by omega) (by decide),
        lowParity_eq k hg 8 (2302-k) 1350 (by omega) (by decide),
        lowFour_eq _ _ _ _ _ _ 4, lowFour_eq _ _ _ _ _ _ 4]
  · rfl
private def lowSum (s : ℕ) : ℕ → ℤ
  | 0 => 0
  | n+1 => lowSum s n + lowOffset (s+n)
private theorem lowSum_eq (s n : ℕ) : total s n = lowSum s n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total, lowSum, ih, lowOffset_eq]
theorem window0 : total 0 250 = 93967425000 :=
  (lowSum_eq 0 250).trans (by decide +kernel)
theorem window1 : total 250 250 = 267062737500 :=
  (lowSum_eq 250 250).trans (by decide +kernel)
theorem window2 : total 500 250 = 418442617575 :=
  (lowSum_eq 500 250).trans (by decide +kernel)
theorem window3 : total 750 250 = 531379109797 :=
  (lowSum_eq 750 250).trans (by decide +kernel)
theorem window4 : total 1000 250 = 586700450900 :=
  (lowSum_eq 1000 250).trans (by decide +kernel)
theorem window5 : total 1250 250 = 595527605250 :=
  (lowSum_eq 1250 250).trans (by decide +kernel)
theorem window6 : total 1500 250 = 568622558375 :=
  (lowSum_eq 1500 250).trans (by decide +kernel)
theorem window7 : total 1750 250 = 514817120875 :=
  (lowSum_eq 1750 250).trans (by decide +kernel)
theorem window8 : total 2000 250 = 442900355250 :=
  (lowSum_eq 2000 250).trans (by decide +kernel)
end K1_13_4_2_2_5
end
section
namespace K1_13_4_2_2
open scoped BigOperators
set_option maxHeartbeats 600000
def tailPowers (q k : ℕ) (i : Fin 6) : ℕ :=
  if i = 0 ∨ i = 3 then 7299 - q - 3 * k else 0
private theorem gradeBound_tail (q : ℕ) :
    gradeBound tailPowers q =
      ∑ k ∈ Finset.range (7300 - q), blockBound q (offset k) (tailPowers q k) := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.sub_le _ _))
  intro k _ hk
  have h : planeOrder q (offset k) ≤ 0 := by
    unfold planeOrder offset
    simp only [Finset.mem_range] at hk
    omega
  simp [blockBound, h]
private def quarterSquare (w : ℤ) : ℤ := w ^ 2 / 4
private def weightCost (w : ℤ) : ℤ := quarterSquare (w + 1)
private theorem double_triangular (w : ℤ) : 2 * triangular w = w * (w + 1) := by
  unfold triangular
  apply Int.mul_ediv_cancel_of_dvd
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with h | h
  · have hw : w = 2 * (w / 2) := by omega
    exact dvd_mul_of_dvd_left (by rw [hw]; exact dvd_mul_right _ _) _
  · have hw : w + 1 = 2 * (w / 2 + 1) := by omega
    exact dvd_mul_of_dvd_right (by rw [hw]; exact dvd_mul_right _ _) _
private theorem quarterSquare_spec (w : ℤ) :
    4 * quarterSquare w = w ^ 2 - w % 2 := by
  unfold quarterSquare
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with h | h
  · have hw : w = 2 * (w / 2) := by omega
    have he : w ^ 2 = 4 * (w / 2) ^ 2 := by
      calc _ = (2 * (w / 2)) ^ 2 := congrArg (· ^ 2) hw
           _ = _ := by ring
    rw [he, h]
    omega
  · have hw : w = 2 * (w / 2) + 1 := by omega
    have he : w ^ 2 = 4 * ((w / 2) ^ 2 + w / 2) + 1 := by
      calc _ = (2 * (w / 2) + 1) ^ 2 := congrArg (· ^ 2) hw
           _ = _ := by ring
    rw [he, h]
    omega
private theorem weightCost_spec (w : ℤ) :
    4 * weightCost w = w ^ 2 + 2 * w + w % 2 := by
  unfold weightCost
  rw [quarterSquare_spec]
  have h : (w + 1) % 2 + w % 2 = 1 := by omega
  nlinarith only [h]
private theorem colength_eq_weightCost {a w : ℤ} (ha : a ≤ (w + 1) / 2) (hw : 0 ≤ w) :
    colength ⟨a, w⟩ = weightCost w := by
  have hu : 0 ≤ (w + 1) / 2 := by omega
  have huv : (w + 1) / 2 ≤ w := by omega
  have h : (w + 1) / 2 = w / 2 + w % 2 := by omega
  have h' : w - (w + 1) / 2 = w / 2 := by omega
  unfold colength
  simp only [max_eq_right ha, max_eq_right hu, max_eq_right huv]
  rw [h', h]
  have h₁ := double_triangular (w / 2 + w % 2)
  have h₂ := double_triangular (w / 2)
  have h₃ := weightCost_spec w
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with he | he
  · have hw : w = 2 * (w / 2) := by omega
    rw [he] at h₁ h₃ ⊢
    conv at h₃ => rhs; rw [hw]
    nlinarith only [h₁, h₂, h₃]
  · have hw : w = 2 * (w / 2) + 1 := by omega
    rw [he] at h₁ h₃ ⊢
    conv at h₃ => rhs; rw [hw]
    nlinarith only [h₁, h₂, h₃]
private theorem sum_powers (q k : ℕ) (f : Fin 6 → ℤ) :
    (∑ j, (tailPowers q k j : ℤ) * f j) =
      ((7299 - q - 3 * k : ℕ) : ℤ) * (f 0 + f 3) := by
  simp [Fin.sum_univ_succ, tailPowers, Fin.succ, mul_add]
private theorem tail_gain (k n t : ℤ) (hn : n = 0 ∨ t = n + 2 * k + 1) :
    triangular (2301 - 2 * n) - weightCost (2300 - k - 2 * n) - weightCost (2300 - 2 * n) -
        weightCost (t - n) =
      triangular 2301 - weightCost (2300 - k) - weightCost 2300 - weightCost t +
        quarterSquare n := by
  rcases hn with rfl | ht
  · simp [quarterSquare]
  have hp : (2300 - k - 2 * n) % 2 = (2300 - k) % 2 := by omega
  have hq : (2300 - 2 * n) % 2 = 0 := by omega
  have ho : (t - n) % 2 = 1 := by omega
  have hs : t % 2 = 1 - n % 2 := by omega
  have hTP := double_triangular (2301 - 2 * n)
  have hT := double_triangular 2301
  have hPP := weightCost_spec (2300 - k - 2 * n)
  have hP := weightCost_spec (2300 - k)
  have hQP := weightCost_spec (2300 - 2 * n)
  have hQ := weightCost_spec 2300
  have hOP := weightCost_spec (t - n)
  have hO := weightCost_spec t
  have hN := quarterSquare_spec n
  rw [hp] at hPP
  rw [hq] at hQP
  rw [ho] at hOP
  rw [hs] at hO
  norm_num only [Int.reduceMod] at hQ
  rw [ht] at hOP hO ⊢
  nlinarith only [hTP, hT, hPP, hP, hQP, hQ, hOP, hO, hN]
private def tailTerm (r k : ℕ) : ℕ :=
  (weightCost ((r : ℤ) - k) - quarterSquare ((r - 1 - 3 * k : ℕ) : ℤ)).toNat
private theorem blockBound_tail_le (q k : ℕ) (hlo : 6790 ≤ q) (hhi : q ≤ 6820)
    (hk : k < 7300 - q) :
    blockBound q (offset k) (tailPowers q k) ≤ tailTerm (7300 - q) k := by
  let n : ℤ := ((7299 - q - 3 * k : ℕ) : ℤ)
  let t : ℤ := 7300 - (q : ℤ) - k
  have hn : n = 0 ∨ t = n + 2 * (k : ℤ) + 1 := by
    dsimp [n, t]
    omega
  have hnr : 0 ≤ n := Int.natCast_nonneg _
  have htn : n ≤ t := by dsimp [n, t]; omega
  have hnmax : n ≤ 509 := by dsimp [n]; omega
  have hkmax : (k : ℤ) ≤ 509 := by omega
  have ht : 0 < t := by dsimp [t]; omega
  have hr (x : ℕ) : 7300 - q - 1 - x = 7299 - q - x := by omega
  have hd : residualDegree q = 2300 := min_eq_right (by omega)
  have ho : planeOrder q (offset k) = t := by unfold planeOrder offset t; ring
  have hc : columnCount q (offset k) = triangular 2301 - weightCost (2300 - k) - weightCost 2300 := by
    have harg : min (2300 : ℤ) (-offset k - 1) = 2300 - k - 1 := by unfold offset; omega
    have hpos : ¬ (2300 - (k : ℤ) - 1) < 0 := by omega
    have hmin : min (2300 - (k : ℤ) - 1) 4600 = 2300 - k - 1 := min_eq_left (by omega)
    have hmax : max (0 : ℤ) (2300 - k - 1 - 2300) = 0 := max_eq_left (by omega)
    have heval : cumulative 2300 2300 = triangular 2301 - weightCost 2300 := by decide
    unfold columnCount
    rw [hd, harg]
    change cumulative 2300 2300 - cumulative 2300 (2300 - (k : ℤ) - 1) = _
    rw [heval]
    simp only [cumulative, hpos, ite_false, show (2 * 2300 : ℤ) = 4600 by decide, hmin, hmax]
    unfold weightCost quarterSquare
    have he : (2300 - (k : ℤ) - 1 + 2) = 2300 - k + 1 := by ring
    rw [he]
    norm_num [triangular]
    ring
  have hd' : remainingDegree q (tailPowers q k) = 2300 - 2 * n := by
    rw [remainingDegree, hd, sum_powers]
    simp [factorDegree, n]
    ring
  have hP : remainingFlag q (offset k) (tailPowers q k) 0 = ⟨-n, 2300 - k - 2 * n⟩ := by
    simp [remainingFlag, sum_powers, initialFlag, factorFlag, offset, n]
    ring
  have hQ : remainingFlag q (offset k) (tailPowers q k) 1 = ⟨1150 - n, 2300 - 2 * n⟩ := by
    simp [remainingFlag, sum_powers, initialFlag, factorFlag, offset, n, hd]
    ring
  have hO : remainingFlag q (offset k) (tailPowers q k) 2 = ⟨-n, t - n⟩ := by
    simp [remainingFlag, sum_powers, initialFlag, factorFlag, ho, n]
  have hkernel :
      kernelLower (remainingDegree q (tailPowers q k)) (remainingFlag q (offset k) (tailPowers q k)) =
        columnCount q (offset k) - weightCost t + quarterSquare n := by
    rw [kernelLower, hd']
    simp only [show ¬ (2300 - 2 * n) < 0 by omega, ite_false]
    rw [Fin.sum_univ_three, hP, hQ, hO]
    rw [colength_eq_weightCost (by omega) (by omega),
      colength_eq_weightCost (by omega) (by omega),
      colength_eq_weightCost (by omega) (by omega), hc]
    calc
      _ = triangular (2301 - 2 * n) - weightCost (2300 - k - 2 * n) -
          weightCost (2300 - 2 * n) - weightCost (t - n) := by ring
      _ = _ := tail_gain k n t hn
  have htc : ((7300 - q : ℕ) : ℤ) - k = t := by dsimp [t]; omega
  unfold blockBound tailTerm
  simp only [ho, not_le_of_gt ht, ite_false, htc, hr]
  change _ ≤ (weightCost t - quarterSquare n).toNat
  apply Int.toNat_le_toNat
  calc
    _ ≤ columnCount q (offset k) -
        kernelLower (remainingDegree q (tailPowers q k)) (remainingFlag q (offset k) (tailPowers q k)) := by
      exact sub_le_sub_left ((le_max_right _ _).trans (le_max_right _ _)) _
    _ = weightCost t - quarterSquare n := by rw [hkernel]; ring
private def sumTerms (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTerms r n + tailTerm r n
private theorem sum_tailTerm (r n : ℕ) :
    (∑ k ∈ Finset.range n, tailTerm r k) = sumTerms r n := by
  induction n with
  | zero => simp [sumTerms]
  | succ n ih => rw [Finset.sum_range_succ, ih, sumTerms]
private def total : ℕ → ℕ
  | 0 => 0
  | n + 1 => total n + sumTerms (510 - n) (510 - n)
private theorem sum_prefix (n : ℕ) :
    (∑ j ∈ Finset.range n, sumTerms (510 - j) (510 - j)) = total n := by
  induction n with
  | zero => simp [total]
  | succ n ih => rw [Finset.sum_range_succ, ih, total]
section
set_option maxRecDepth 4096
private theorem tailRow510 : sumTerms 510 510 = 7456455 := by decide +kernel
private theorem tailRow509 : sumTerms 509 509 = 7412850 := by decide +kernel
private theorem tailRow508 : sumTerms 508 508 = 7369415 := by decide +kernel
private theorem tailRow507 : sumTerms 507 507 = 7326150 := by decide +kernel
private theorem tailRow506 : sumTerms 506 506 = 7283055 := by decide +kernel
private theorem tailRow505 : sumTerms 505 505 = 7240129 := by decide +kernel
private theorem tailRow504 : sumTerms 504 504 = 7197372 := by decide +kernel
private theorem tailRow503 : sumTerms 503 503 = 7154784 := by decide +kernel
private theorem tailRow502 : sumTerms 502 502 = 7112364 := by decide +kernel
private theorem tailRow501 : sumTerms 501 501 = 7070112 := by decide +kernel
private theorem tailRow500 : sumTerms 500 500 = 7028028 := by decide +kernel
private theorem tailRow499 : sumTerms 499 499 = 6986111 := by decide +kernel
private theorem tailRow498 : sumTerms 498 498 = 6944361 := by decide +kernel
private theorem tailRow497 : sumTerms 497 497 = 6902778 := by decide +kernel
private theorem tailRow496 : sumTerms 496 496 = 6861361 := by decide +kernel
private theorem tailRow495 : sumTerms 495 495 = 6820110 := by decide +kernel
private theorem tailRow494 : sumTerms 494 494 = 6779025 := by decide +kernel
private theorem tailRow493 : sumTerms 493 493 = 6738105 := by decide +kernel
private theorem tailRow492 : sumTerms 492 492 = 6697350 := by decide +kernel
private theorem tailRow491 : sumTerms 491 491 = 6656760 := by decide +kernel
private theorem tailRow490 : sumTerms 490 490 = 6616334 := by decide +kernel
private theorem tailRow489 : sumTerms 489 489 = 6576072 := by decide +kernel
private theorem tailRow488 : sumTerms 488 488 = 6535974 := by decide +kernel
private theorem tailRow487 : sumTerms 487 487 = 6496039 := by decide +kernel
private theorem tailRow486 : sumTerms 486 486 = 6456267 := by decide +kernel
private theorem tailRow485 : sumTerms 485 485 = 6416658 := by decide +kernel
private theorem tailRow484 : sumTerms 484 484 = 6377211 := by decide +kernel
private theorem tailRow483 : sumTerms 483 483 = 6337926 := by decide +kernel
private theorem tailRow482 : sumTerms 482 482 = 6298803 := by decide +kernel
private theorem tailRow481 : sumTerms 481 481 = 6259841 := by decide +kernel
private theorem tailRow480 : sumTerms 480 480 = 6221040 := by decide +kernel
end
private theorem tailTotal_next {n a b : ℕ} (hp : total n = a)
    (hr : sumTerms (510 - n) (510 - n) = b) : total (n + 1) = a + b :=
  congrArg₂ Nat.add hp hr
private theorem total_value : total 31 ≤ 211628840 := by
  have h0 : total 0 = 0 := rfl
  have h1 : total 1 = 7456455 := tailTotal_next h0 tailRow510
  have h2 : total 2 = 14869305 := tailTotal_next h1 tailRow509
  have h3 : total 3 = 22238720 := tailTotal_next h2 tailRow508
  have h4 : total 4 = 29564870 := tailTotal_next h3 tailRow507
  have h5 : total 5 = 36847925 := tailTotal_next h4 tailRow506
  have h6 : total 6 = 44088054 := tailTotal_next h5 tailRow505
  have h7 : total 7 = 51285426 := tailTotal_next h6 tailRow504
  have h8 : total 8 = 58440210 := tailTotal_next h7 tailRow503
  have h9 : total 9 = 65552574 := tailTotal_next h8 tailRow502
  have h10 : total 10 = 72622686 := tailTotal_next h9 tailRow501
  have h11 : total 11 = 79650714 := tailTotal_next h10 tailRow500
  have h12 : total 12 = 86636825 := tailTotal_next h11 tailRow499
  have h13 : total 13 = 93581186 := tailTotal_next h12 tailRow498
  have h14 : total 14 = 100483964 := tailTotal_next h13 tailRow497
  have h15 : total 15 = 107345325 := tailTotal_next h14 tailRow496
  have h16 : total 16 = 114165435 := tailTotal_next h15 tailRow495
  have h17 : total 17 = 120944460 := tailTotal_next h16 tailRow494
  have h18 : total 18 = 127682565 := tailTotal_next h17 tailRow493
  have h19 : total 19 = 134379915 := tailTotal_next h18 tailRow492
  have h20 : total 20 = 141036675 := tailTotal_next h19 tailRow491
  have h21 : total 21 = 147653009 := tailTotal_next h20 tailRow490
  have h22 : total 22 = 154229081 := tailTotal_next h21 tailRow489
  have h23 : total 23 = 160765055 := tailTotal_next h22 tailRow488
  have h24 : total 24 = 167261094 := tailTotal_next h23 tailRow487
  have h25 : total 25 = 173717361 := tailTotal_next h24 tailRow486
  have h26 : total 26 = 180134019 := tailTotal_next h25 tailRow485
  have h27 : total 27 = 186511230 := tailTotal_next h26 tailRow484
  have h28 : total 28 = 192849156 := tailTotal_next h27 tailRow483
  have h29 : total 29 = 199147959 := tailTotal_next h28 tailRow482
  have h30 : total 30 = 205407800 := tailTotal_next h29 tailRow481
  have h31 : total 31 = 211628840 := tailTotal_next h30 tailRow480
  exact le_of_eq h31
theorem tail_bound :
    ∃ p : ℕ → ℕ → Powers,
      (∑ j ∈ Finset.range 31, gradeBound p (6790 + j)) ≤ 211628840 := by
  refine ⟨tailPowers, ?_⟩
  apply le_trans _ total_value
  rw [← sum_prefix]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [gradeBound_tail, ← sum_tailTerm]
  have h : 7300 - (6790 + j) = 510 - j := by omega
  rw [← h]
  apply Finset.sum_le_sum
  intro k hk
  exact blockBound_tail_le _ _ (by omega) (by omega) (Finset.mem_range.mp hk)
end K1_13_4_2_2
end
section
namespace K1_13_4_2_2
noncomputable section
open K1_13 MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 600000
instance blockFinite (q k : ℕ) : Module.Finite Geom (Block q k) := by
  apply restrictSupport_finite
  refine (Finsupp.finite_of_nat_weight_le (fun _ : Option (Fin 3) => 1)
    (by simp) (q + k)).subset ?_
  intro e he
  change Eligible q e ∧ e.weight gradeWeight = q ∧ _ at he
  have hidx := he.1.2.1
  have ha : e none ≤ k := by
    have h := he.2.2
    unfold offset at h
    omega
  have hw : e.weight (fun _ => 1) = e none + e.weight gradeWeight := by
    simp only [Finsupp.weight_eq_sum, Fintype.sum_option, gradeWeight,
      Option.elim_none, Option.elim_some, smul_eq_mul, Nat.mul_one, Nat.mul_zero, zero_add]
  change e.weight (fun _ => 1) ≤ q + k
  rw [hw, he.2.1]
  omega
theorem high_monomial_vanishes (e : Exp) (c : Geom) (he : 5000 ≤ e none) :
    origin (monomial e c) = 0 := by
  change weightedTruncation contactWeight 5000 (bind₁ shearImage (monomial e c)) = 0
  apply (weightedTruncation_eq_zero_iff _ _ _).mpr
  refine bind₁_mem_restrictWeightedOrder
    (w := fun v : Option (Fin 3) => v.elim 1 (fun _ => 0)) ?_ ?_
  · intro v
    cases v with
    | none =>
      simpa [shearImage] using
        (X_mem_restrictWeightedOrder (R := Geom) contactWeight
          (none : Option (Fin 3)) (m := 1) (by rfl))
    | some j => simp
  · apply (monomial_mem_restrictWeightedOrder _ _ _ _).mpr
    exact Or.inl (by simpa only [Finsupp.weight_elim_one_zero] using he)
def cappedRange (B : ℕ) : Submodule Geom Flat := LinearMap.range (origin.domRestrict (Capped B))
private def blockRange (i : ℕ × ℕ) : Submodule Geom Flat :=
  LinearMap.range (originBlock i.1 i.2)
private instance (i : ℕ × ℕ) : Module.Finite Geom (blockRange i) :=
  Module.Finite.range (originBlock i.1 i.2)
private def pairs (B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (B + 1)) ×ˢ (Finset.range 7300)
private theorem range_cover (B : ℕ) : cappedRange B ≤ (pairs B).sup blockRange := by
  classical
  intro P hP
  obtain ⟨Q, rfl⟩ := LinearMap.mem_range.mp hP
  change origin Q.1 ∈ (pairs B).sup blockRange
  have expand := congrArg origin Q.1.as_sum
  rw [map_sum] at expand
  rw [expand]
  refine Submodule.sum_mem _ fun e he => ?_
  by_cases hi : 5000 ≤ e none
  · rw [high_monomial_vanishes e (Q.1.coeff e) hi]
    exact Submodule.zero_mem _
  have hbox : Eligible B e := Q.2 he
  let q := e.weight gradeWeight
  let k := e none + (2300 - e.weight indexWeight)
  have hmem : (q, k) ∈ pairs B := by
    simp only [pairs, Finset.mem_product, Finset.mem_range]
    have hq := hbox.1
    dsimp [q, k] at *
    omega
  apply (Finset.le_sup (f := blockRange) hmem)
  refine LinearMap.mem_range.mpr ⟨⟨monomial e (Q.1.coeff e), ?_⟩, rfl⟩
  intro u hu
  have hue : u = e := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hu) (by simp [coeff_monomial, Ne.symm hne])
  subst u
  change (q ≤ q ∧ e.weight indexWeight ≤ 2300 ∧ e (some 2) ≤ 1150) ∧
    e.weight gradeWeight = q ∧ (e none : ℤ) - (e.weight indexWeight : ℤ) = offset k
  refine ⟨⟨le_rfl, hbox.2.1, hbox.2.2⟩, rfl, ?_⟩
  have hj := hbox.2.1
  dsimp [offset, k]
  omega
instance cappedRangeFinite (B : ℕ) : Module.Finite Geom (cappedRange B) :=
  Module.Finite.of_injective (Submodule.inclusion (range_cover B))
    (Submodule.inclusion_injective (range_cover B))
private theorem finrank_finset_sup_le (S : Finset (ℕ × ℕ)) :
    Module.finrank Geom (S.sup blockRange : Submodule Geom Flat) ≤
      ∑ i ∈ S, Module.finrank Geom (blockRange i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    exact (Submodule.finrank_add_le_finrank_add_finrank (blockRange i) (S.sup blockRange)).trans
      (Nat.add_le_add_left ih _)
theorem cappedRange_le_sum (B : ℕ) (bound : ℕ → ℕ → ℕ)
    (h : ∀ q < B + 1, ∀ k < 7300,
      Module.finrank Geom (LinearMap.range (originBlock q k)) ≤ bound q k) :
    Module.finrank Geom (cappedRange B) ≤
      ∑ q ∈ Finset.range (B + 1), ∑ k ∈ Finset.range 7300, bound q k := by
  have hr := (Submodule.finrank_mono (range_cover B)).trans (finrank_finset_sup_le (pairs B))
  refine hr.trans ?_
  rw [← Finset.sum_product']
  apply Finset.sum_le_sum
  intro i hi
  have hp := Finset.mem_product.mp hi
  exact h i.1 (Finset.mem_range.mp hp.1) i.2 (Finset.mem_range.mp hp.2)
end
end K1_13_4_2_2
end
section
namespace K1_13_4_2_2
noncomputable section
open K1_13 MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 600000
instance planeSourceFinite (q : ℕ) (g : ℤ) : Module.Finite Geom (PlaneSource q g) := by
  apply restrictSupport_finite
  refine (Finsupp.finite_of_nat_weight_le (fun _ : Fin 3 => 1)
    (by simp) (residualDegree q)).subset ?_
  intro e he
  exact (show e.weight (fun _ => 1) = residualDegree q from he.1).le
private def removed (q : ℕ) : ℕ := q - residualDegree q
private def stripped (q : ℕ) (e : Exp) : PlaneExp :=
  Finsupp.equivFunOnFinite.symm ![e (some 0) - removed q, e (some 1), e (some 2)]
private theorem source_grade (e : Exp) :
    e.weight gradeWeight = e (some 0) + e (some 1) + e (some 2) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_three, gradeWeight, add_assoc]
private theorem source_index (e : Exp) :
    e.weight indexWeight = e (some 1) + 2 * e (some 2) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_three, indexWeight,
    smul_eq_mul, Nat.mul_comm]
private theorem removed_le {q k : ℕ} (e : blockExponents q k) :
    removed q ≤ e.val (some 0) := by
  have hd := e.property.2.1
  have hj := e.property.1.2.1
  rw [source_grade] at hd
  rw [source_index] at hj
  simp only [removed, residualDegree]
  omega
private theorem stripped_mem {q k : ℕ} (e : blockExponents q k) :
    stripped q e ∈ planeExponents q (offset k) := by
  have hd := e.property.2.1
  have hj := e.property.1.2.1
  have ht := e.property.1.2.2
  have hg := e.property.2.2
  have ha := removed_le e
  rw [source_grade] at hd
  rw [source_index] at hj hg
  change (stripped q e).weight (fun _ => 1) = residualDegree q ∧
    -offset k ≤ ((stripped q e).weight Fin.val : ℤ) ∧
    (stripped q e).weight Fin.val ≤ 2300 ∧ (stripped q e) 2 ≤ 1150
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, stripped, smul_eq_mul, Nat.mul_comm]
  simp only [removed, residualDegree] at *
  omega
private def encodeColumn (q k : ℕ) (e : blockExponents q k) :
    PlaneSource q (offset k) :=
  ⟨monomial (stripped q e) 1,
    (monomial_mem_restrictSupport Geom).mpr (Or.inl (stripped_mem e))⟩
private def encode (q k : ℕ) : Block q k →ₗ[Geom] PlaneSource q (offset k) :=
  (basisRestrictSupport Geom (blockExponents q k)).constr Geom (encodeColumn q k)
private theorem encode_basis (q k : ℕ) (e : blockExponents q k) :
    ((encode q k (basisRestrictSupport Geom (blockExponents q k) e)) : Plane) =
      monomial (stripped q e) 1 :=
  congrArg Subtype.val
    ((basisRestrictSupport Geom (blockExponents q k)).constr_basis Geom (encodeColumn q k) e)
local notation "T" => (MvPolynomial.X (none : Option (Fin 3)) : Flat)
private def y (j : Fin 3) : Flat := MvPolynomial.X (some j)
private def scaledImage : Fin 3 → Flat := ![y 0, T * y 1, T ^ 2 * y 2]
private theorem scaled_plane_zero :
    bind₁ scaledImage (planeImage 0) = shearImage (some 0) := by
  simp [planeImage, scaledImage, shearImage, y]
private theorem scaled_plane_one : bind₁ scaledImage (planeImage 1) = T * y 1 := by
  simp [planeImage, scaledImage]
private theorem scaled_plane_two : bind₁ scaledImage (planeImage 2) = T ^ 2 * y 2 := by
  simp [planeImage, scaledImage]
private theorem bind_monomial_one {σ τ : Type*} [Fintype σ]
    (f : σ → MvPolynomial τ Geom) (e : σ →₀ ℕ) :
    bind₁ f (monomial e 1) = ∏ j, f j ^ e j := by
  rw [bind₁_monomial, C_1, one_mul]
  exact Finsupp.prod_fintype e (fun j n => f j ^ n) (fun _ => pow_zero _)
private theorem source_monomial (e : Exp) :
    shear (monomial e 1) = T ^ e none *
      (shearImage (some 0) ^ e (some 0) * y 1 ^ e (some 1) * y 2 ^ e (some 2)) := by
  rw [shear, bind_monomial_one, Fintype.prod_option, Fin.prod_univ_three]
  simp [shearImage, y, mul_assoc]
private theorem stripped_monomial (q : ℕ) (e : Exp) :
    bind₁ scaledImage (bind₁ planeImage (monomial (stripped q e) 1)) =
      shearImage (some 0) ^ (e (some 0) - removed q) *
        (T * y 1) ^ e (some 1) * (T ^ 2 * y 2) ^ e (some 2) := by
  rw [bind₁_bind₁, bind_monomial_one, Fin.prod_univ_three]
  simp [scaled_plane_zero, scaled_plane_one, scaled_plane_two, stripped, mul_assoc]
private theorem shifted_monomial (q k : ℕ) (e : blockExponents q k) :
    T ^ (-offset k).toNat * shear (monomial e.val 1) =
      T ^ (offset k).toNat * shearImage (some 0) ^ removed q *
        bind₁ scaledImage (bind₁ planeImage (monomial (stripped q e) 1)) := by
  have hi := e.property.2.2
  rw [source_index] at hi
  have ht : (-offset k).toNat + e.val none =
      (offset k).toNat + e.val (some 1) + 2 * e.val (some 2) := by omega
  have ha : removed q + (e.val (some 0) - removed q) = e.val (some 0) := by
    have := removed_le e
    omega
  have hT : T ^ (-offset k).toNat * T ^ e.val none =
      T ^ (offset k).toNat * T ^ e.val (some 1) * T ^ (2 * e.val (some 2)) := by
    simpa only [pow_add] using congrArg (T ^ ·) ht
  have hA : shearImage (some 0) ^ e.val (some 0) =
      shearImage (some 0) ^ removed q * shearImage (some 0) ^ (e.val (some 0) - removed q) := by
    rw [← pow_add, ha]
  rw [source_monomial, stripped_monomial]
  simp only [mul_pow, ← pow_mul]
  calc
    _ = (T ^ (-offset k).toNat * T ^ e.val none) *
        (shearImage (some 0) ^ e.val (some 0) * y 1 ^ e.val (some 1) * y 2 ^ e.val (some 2)) := by
      ring
    _ = _ := by rw [hT, hA]; ring
private theorem shifted_shear (q k : ℕ) (p : Block q k) :
    T ^ (-offset k).toNat * shear (p : Flat) =
      T ^ (offset k).toNat * shearImage (some 0) ^ removed q *
        bind₁ scaledImage (bind₁ planeImage (encode q k p : Plane)) := by
  let l := (LinearMap.mulLeft Geom (T ^ (-offset k).toNat)).comp
    (shear.toLinearMap.comp (Block q k).subtype)
  let r := (LinearMap.mulLeft Geom (T ^ (offset k).toNat * shearImage (some 0) ^ removed q)).comp
    ((bind₁ scaledImage).toLinearMap.comp ((bind₁ planeImage).toLinearMap.comp
      ((PlaneSource q (offset k)).subtype.comp (encode q k))))
  have h : l = r := by
    apply (basisRestrictSupport Geom (blockExponents q k)).ext
    intro e
    change T ^ (-offset k).toNat *
      shear (↑(basisRestrictSupport Geom (blockExponents q k) e) : Flat) =
        T ^ (offset k).toNat * shearImage (some 0) ^ removed q *
          bind₁ scaledImage (bind₁ planeImage
            (↑(encode q k (basisRestrictSupport Geom (blockExponents q k) e)) : Plane))
    rw [encode_basis, coe_basisRestrictSupport_apply]
    exact shifted_monomial q k e
  exact LinearMap.congr_fun h p
private def planeWeight : Fin 3 → ℕ := ![2, 0, 1]
private def scaledWeight (j : Fin 3) : ℕ := planeWeight j + 1
private theorem weight_scaled (e : PlaneExp) :
    e.weight scaledWeight = e.weight planeWeight + e.weight (fun _ => 1) := by
  simp [Finsupp.weight_eq_sum, scaledWeight, smul_eq_mul, Nat.mul_add, Finset.sum_add_distrib]
private theorem t_power_order (n : ℕ) : T ^ n ∈ restrictWeightedOrder contactWeight n := by
  simpa using pow_mem_restrictWeightedOrder
    (X_mem_restrictWeightedOrder (R := Geom) contactWeight (none : Option (Fin 3))
      (m := 1) le_rfl) n
private theorem scaled_image_order (j : Fin 3) :
    scaledImage j ∈ restrictWeightedOrder contactWeight (scaledWeight j) := by
  have hy (j : Fin 3) : y j ∈ restrictWeightedOrder contactWeight 0 := by simp
  have he : y 0 ∈ restrictWeightedOrder contactWeight 3 := X_mem_restrictWeightedOrder _ _ le_rfl
  fin_cases j
  · simpa [scaledImage, scaledWeight, planeWeight] using he
  · simpa [scaledImage, scaledWeight, planeWeight] using mul_mem_restrictWeightedOrder
      (t_power_order 1) (hy 1)
  · simpa [scaledImage, scaledWeight, planeWeight] using mul_mem_restrictWeightedOrder
      (t_power_order 2) (hy 2)
private theorem value_order : shearImage (some 0) ∈ restrictWeightedOrder contactWeight 1 := by
  have h (j : Fin 3) : scaledImage j ∈ restrictWeightedOrder contactWeight 1 :=
    restrictWeightedOrder_anti _ (Nat.le_add_left 1 (planeWeight j)) (scaled_image_order j)
  rw [← scaled_plane_zero]
  simp only [planeImage, ite_true, map_add, map_sub, bind₁_X_right]
  exact Submodule.sub_mem _ (Submodule.add_mem _ (h 0) (h 1)) (h 2)
private theorem order_of_t_power_mul {n m : ℕ} {p : Flat}
    (h : T ^ n * p ∈ restrictWeightedOrder contactWeight (m + n)) :
    p ∈ restrictWeightedOrder contactWeight m := by
  rw [MvPolynomial.X_pow_eq_monomial] at h
  intro e he
  have hh := mem_restrictWeightedOrder.mp h (Finsupp.single none n + e) (by
    rw [MvPolynomial.mem_support_iff, coeff_monomial_mul, one_mul]
    exact MvPolynomial.mem_support_iff.mp he)
  change m ≤ e.weight contactWeight
  simp only [map_add, Finsupp.weight_single, contactWeight, Option.elim_none,
    smul_eq_mul, mul_one] at hh ⊢
  omega
private theorem planeImage_grade (j : Fin 3) :
    (planeImage j).IsWeightedHomogeneous (fun _ : Fin 3 => 1) 1 := by
  have h (i : Fin 3) := isWeightedHomogeneous_X Geom (fun _ : Fin 3 => (1 : ℕ)) i
  by_cases hj : j = 0
  · subst j
    simpa [planeImage] using ((h 0).add (h 1)).sub (h 2)
  · simpa [planeImage, hj] using h j
private theorem kernel_le (q k : ℕ) :
    LinearMap.ker ((planeContact q (offset k)).comp (encode q k)) ≤
      LinearMap.ker (originBlock q k) := by
  intro p hp
  let L : PlaneSource q (offset k) := encode q k p
  let S : Plane := bind₁ planeImage (L : Plane)
  let cut := (planeOrder q (offset k)).toNat
  have hz : weightedTruncation planeWeight cut S = 0 := LinearMap.mem_ker.mp hp
  have hcontact := (weightedTruncation_eq_zero_iff _ _ _).mp hz
  have hgrade : (L : Plane).IsWeightedHomogeneous (fun _ : Fin 3 => 1) (residualDegree q) :=
    fun e he => (L.property (mem_support_iff.mpr he)).1
  have hS : S.IsWeightedHomogeneous (fun _ : Fin 3 => 1) (residualDegree q) :=
    hgrade.bind₁ planeImage_grade
  have hscaled : S ∈ restrictWeightedOrder scaledWeight (cut + residualDegree q) := by
    intro e he
    have hg := hS (mem_support_iff.mp he)
    have hc := mem_restrictWeightedOrder.mp hcontact e he
    change cut + residualDegree q ≤ e.weight scaledWeight
    rw [weight_scaled, hg]
    exact Nat.add_le_add_right hc _
  have hprod := mul_mem_restrictWeightedOrder
    (mul_mem_restrictWeightedOrder (t_power_order (offset k).toNat)
      (by simpa using pow_mem_restrictWeightedOrder value_order (removed q)))
    (bind₁_mem_restrictWeightedOrder scaled_image_order hscaled)
  have hbound : 5000 + (-offset k).toNat ≤
      (offset k).toNat + removed q + (cut + residualDegree q) := by
    change 5000 + (-offset k).toNat ≤ (offset k).toNat + removed q +
      ((5000 - (q : ℤ) - offset k).toNat + residualDegree q)
    simp only [removed, residualDegree]
    omega
  have hshift : T ^ (-offset k).toNat * shear (p : Flat) ∈
      restrictWeightedOrder contactWeight (5000 + (-offset k).toNat) := by
    rw [shifted_shear]
    exact restrictWeightedOrder_anti _ hbound hprod
  apply LinearMap.mem_ker.mpr
  exact (weightedTruncation_eq_zero_iff _ _ _).mpr (order_of_t_power_mul hshift)
theorem rank_originBlock_le_plane (q k : ℕ) :
    Module.finrank Geom (LinearMap.range (originBlock q k)) ≤
      Module.finrank Geom (LinearMap.range (planeContact q (offset k))) := by
  let f := (planeContact q (offset k)).comp (encode q k)
  have hker := Submodule.finrank_mono (kernel_le q k)
  change Module.finrank Geom (LinearMap.ker f) ≤
    Module.finrank Geom (LinearMap.ker (originBlock q k)) at hker
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ := (originBlock q k).finrank_range_add_finrank_ker
  exact (show Module.finrank Geom (LinearMap.range (originBlock q k)) ≤
      Module.finrank Geom (LinearMap.range f) by omega).trans
    (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))
end
end K1_13_4_2_2
end
section
namespace K1_13_4_2_2
noncomputable section
open K1_13 K1_13_4 K1_13_4_2
open ReedSolomon.HiddenDerivative
open MvPolynomial
open scoped Polynomial BigOperators
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
private abbrev JetRow := MvPolynomial (Fin 3) Geom[X]
private def seedView : PhysicalRow ≃ₐ[Geom[X]] JetRow[X] :=
  optionEquivLeft _ _
private def toRow : Flat ≃ₐ[Geom] JetRow := optionEquivRight _ _
private def seedCoeff (n : ℕ) : PhysicalRow →ₗ[Geom] JetRow :=
  (Polynomial.lcoeff JetRow n).restrictScalars Geom ∘ₗ seedView.toLinearMap.restrictScalars Geom
private def flatCoeff (n : ℕ) : PhysicalRow →ₗ[Geom] Flat :=
  toRow.symm.toLinearMap ∘ₗ seedCoeff n
private theorem seedCoeff_apply (n : ℕ) (F : PhysicalRow) (e : PlaneExp) :
    (seedCoeff n F).coeff e = F.coeff (e.optionElim n) :=
  optionEquivLeft_coeff_coeff Geom[X] F n e
private theorem flatCoeff_apply (n : ℕ) (F : PhysicalRow) (e : Exp) :
    (flatCoeff n F).coeff e = (F.coeff (e.some.optionElim n)).coeff (e none) := by
  have h := optionEquivRight_coeff_coeff (flatCoeff n F) e.some (e none)
  rw [Finsupp.optionElim_some] at h
  change ((toRow (toRow.symm (seedCoeff n F))).coeff e.some).coeff (e none) = _ at h
  rw [AlgEquiv.apply_symm_apply, seedCoeff_apply] at h
  exact h.symm
private theorem coeff_mem_capped {b : Bank} {F : PhysicalRow} (hF : Caps b.box F) (n : ℕ) :
    flatCoeff n F ∈ Capped b.box.b := by
  intro e he
  change e ∈ (flatCoeff n F).support at he
  have hc := MvPolynomial.mem_support_iff.mp he
  rw [flatCoeff_apply] at hc
  have hs : e.some.optionElim n ∈ F.support := MvPolynomial.mem_support_iff.mpr
    (fun h => hc (by rw [h, Polynomial.coeff_zero]))
  have hb := (le_weightedTotalDegree gradeWeight hs).trans hF.1
  have hj := (le_weightedTotalDegree indexWeight hs).trans hF.2.1
  have ht := (degreeOf_le_iff.mp hF.2.2.1) _ hs
  have heq : e.some.optionElim (e none) = e := Finsupp.optionElim_some e
  change e.weight gradeWeight ≤ b.box.b ∧ e.weight indexWeight ≤ 2300 ∧
    e (some 2) ≤ 1150
  have hg (n : ℕ) : (e.some.optionElim n).weight gradeWeight = e.some.weight (fun _ => 1) := by
    unfold gradeWeight
    rw [Finsupp.weight_optionElim, zero_mul, zero_add]
  have hi (n : ℕ) : (e.some.optionElim n).weight indexWeight = e.some.weight Fin.val := by
    unfold indexWeight
    rw [Finsupp.weight_optionElim, zero_mul, zero_add]
  have hj' : b.box.j = 2300 := by cases b <;> rfl
  have ht' : b.box.t = 1150 := by cases b <;> rfl
  rw [hj'] at hj
  rw [ht'] at ht
  rw [hg] at hb
  rw [hi] at hj
  refine ⟨?_, ?_, ?_⟩
  · exact (congrArg (Finsupp.weight gradeWeight) heq).symm.le.trans ((hg (e none)).le.trans hb)
  · exact (congrArg (Finsupp.weight indexWeight) heq).symm.le.trans ((hi (e none)).le.trans hj)
  · simpa using ht
private theorem seedCoeff_eq_zero {b : Bank} {F : PhysicalRow} (hF : Caps b.box F)
    {n : ℕ} (hn : 70000 < n) :
    seedCoeff n F = 0 := by
  have hdeg : (seedView F).natDegree ≤ 70000 := by
    simpa only [seedView, natDegree_optionEquivLeft, seedDegree] using hF.2.2.2
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hn)
private def normalize (x v : Geom) : Flat →ₐ[Geom] Flat :=
  globalPointTranslation (d := 2) x v
private theorem normalize_mem_capped {B : ℕ} {Q : Flat} (h : Q ∈ Capped B) (x v : Geom) :
    normalize x v Q ∈ Capped B := by
  have preserve (w : Option (Fin 3) → ℕ) (a : ℕ)
      (hQ : ∀ e ∈ Q.support, e.weight w ≤ a) :
      ∀ e ∈ (normalize x v Q).support, e.weight w ≤ a :=
    mem_restrictWeightAtMost.mp
      (globalPointTranslation_mem_restrictWeightAtMost (Nat.zero_le _) (Nat.zero_le _)
        x v (mem_restrictWeightAtMost.mpr hQ))
  have htop (e : Exp) : e.weight topWeight = e (some 2) := by
    conv_lhs => rw [← Finsupp.optionElim_some e]
    unfold topWeight
    rw [Finsupp.weight_optionElim, zero_mul, zero_add,
      Finsupp.weight_single_one_apply]
    simp
  intro e he
  exact ⟨preserve gradeWeight B (fun t ht => (h ht).1) e he,
    preserve indexWeight 2300 (fun t ht => (h ht).2.1) e he,
    htop e ▸ preserve topWeight 1150 (fun t ht => (htop t).symm ▸ (h ht).2.2) e he⟩
private def backwardImage {ι : Type*} (x v : Geom)
    (y : Fin 3 → MvPolynomial ι Geom[X]) (j : Fin 3) : MvPolynomial ι Geom[X] :=
  if j = 0 then
    y 0 + C (Polynomial.C v) -
      C (Polynomial.C x - Polynomial.X) * y 1 -
      C ((Polynomial.C x - Polynomial.X) ^ 2) * y 2
  else y j
private def jetBackward (x v : Geom) : JetRow →ₐ[Geom[X]] JetRow :=
  aeval (backwardImage x v MvPolynomial.X)
private def fullBackward (x v : Geom) : PhysicalRow →ₐ[Geom[X]] PhysicalRow :=
  aeval (fun j => j.elim (MvPolynomial.X none)
    (backwardImage x v (fun i => MvPolynomial.X (some i))))
private theorem fullBackward_apply (x v : Geom) (F : PhysicalRow) :
    fullBackward x v F = backwardShift x v F := by
  rw [fullBackward, aeval_def, MvPolynomial.algebraMap_eq, backwardShift]
  apply congrArg (fun a => eval₂ C a F)
  funext j
  cases j <;> simp [backwardImage]
private theorem seedView_backward (x v : Geom) :
    seedView.toAlgHom.comp (fullBackward x v) =
      (Polynomial.mapAlgHom (jetBackward x v)).comp seedView.toAlgHom := by
  apply algHom_ext
  intro j
  cases j with
  | none => simp [seedView, fullBackward, optionEquivLeft_X_none]
  | some j =>
    by_cases hj : j = 0
    · subst j
      simp [seedView, fullBackward, jetBackward, backwardImage, optionEquivLeft_X_some,
        optionEquivLeft_C]
    · simp [seedView, fullBackward, jetBackward, backwardImage, hj, optionEquivLeft_X_some]
private theorem seedCoeff_backward (x v : Geom) (F : PhysicalRow) (n : ℕ) :
    seedCoeff n (backwardShift x v F) = jetBackward x v (seedCoeff n F) := by
  have h := DFunLike.congr_fun (seedView_backward x v) F
  have he : seedView (fullBackward x v F) =
      Polynomial.mapAlgHom (jetBackward x v) (seedView F) := h
  rw [fullBackward_apply] at he
  change (seedView (backwardShift x v F)).coeff n = jetBackward x v ((seedView F).coeff n)
  rw [he, Polynomial.coeff_mapAlgHom_apply]
private def taylorRows (x : Geom) : JetRow →ₐ[Geom] JetRow :=
  mapAlgHom (Polynomial.taylorAlgHom x)
private theorem normalize_shear (x v : Geom) :
    toRow.toAlgHom.comp (shear.comp (normalize x v)) =
      (taylorRows x).comp (((jetBackward x v).restrictScalars Geom).comp toRow.toAlgHom) := by
  apply algHom_ext
  intro j
  have h₁ : globalPointTranslation (d := 2) x v (MvPolynomial.X (some 1)) =
      MvPolynomial.X (some 1) := globalPointTranslation_Y_succ x v (0 : Fin 2)
  have h₂ : globalPointTranslation (d := 2) x v (MvPolynomial.X (some 2)) =
      MvPolynomial.X (some 2) := globalPointTranslation_Y_succ x v (1 : Fin 2)
  cases j with
  | none =>
    simp [normalize, shear, toRow, taylorRows, shearImage, jetBackward, Polynomial.taylor_X, add_comm]
  | some j =>
    fin_cases j <;>
      (simp [normalize, shear, toRow, taylorRows, shearImage, jetBackward, backwardImage,
        Polynomial.taylor_X, Polynomial.taylor_C, h₁, h₂]; try ring)
private theorem node_coeff (x v : Geom) (F : PhysicalRow) (n : ℕ) (e : PlaneExp) :
    (toRow (shear (normalize x v (flatCoeff n F)))).coeff e =
      Polynomial.taylor x ((backwardShift x v F).coeff (e.optionElim n)) := by
  have h := DFunLike.congr_fun (normalize_shear x v) (flatCoeff n F)
  change toRow (shear (normalize x v (flatCoeff n F))) =
    taylorRows x (jetBackward x v (toRow (toRow.symm (seedCoeff n F)))) at h
  rw [AlgEquiv.apply_symm_apply, ← seedCoeff_backward] at h
  rw [h, taylorRows, mapAlgHom_apply, coeff_map, seedCoeff_apply]
  rfl
private theorem contactWeight_eq (e : PlaneExp) (i : ℕ) :
    (e.optionElim i).weight contactWeight = i + 3 * e 0 := by
  unfold contactWeight
  rw [Finsupp.weight_optionElim, Finsupp.weight_single_index, one_mul,
    smul_eq_mul, Nat.mul_comm (e 0)]
private theorem mem_contact_of_origin_eq_zero {b : Bank} {x v : Geom} {F : PhysicalRow}
    (hcap : Caps b.box F) (h : ∀ n : Fin 70001, origin (normalize x v (flatCoeff n F)) = 0) :
    F ∈ contactAt x v := by
  apply (mem_contactAt x v F).mpr
  intro e
  let P := (backwardShift x v F).coeff (e.some.optionElim (e none))
  let E := Polynomial.taylorEquiv x
  have hE : E ((Polynomial.X - Polynomial.C x) ^ (5000 - 3 * e (some 0))) =
      Polynomial.X ^ (5000 - 3 * e (some 0)) := by
    have hX : E (Polynomial.X - Polynomial.C x) = Polynomial.X := by
      rw [map_sub]
      change Polynomial.taylor x Polynomial.X - Polynomial.taylor x (Polynomial.C x) = _
      simp
    rw [map_pow, hX]
  have hP : P = (backwardShift x v F).coeff e := by simp [P]
  rw [← hP, ← map_dvd_iff E, hE, Polynomial.X_pow_dvd_iff]
  intro i hi
  have hcoeff : E P =
      (toRow (shear (normalize x v (flatCoeff (e none) F)))).coeff e.some :=
    (node_coeff x v F (e none) e.some).symm
  rw [hcoeff]
  change ((optionEquivRight Geom (Fin 3) _).coeff e.some).coeff i = 0
  rw [optionEquivRight_coeff_coeff]
  by_cases hn : e none < 70001
  · have hz := congrArg (fun Q : Flat => Q.coeff (e.some.optionElim i)) (h ⟨e none, hn⟩)
    change (weightedTruncation contactWeight 5000
      (shear (normalize x v (flatCoeff (e none) F)))).coeff (e.some.optionElim i) = 0 at hz
    have hlt : (e.some.optionElim i).weight contactWeight < 5000 := by
      rw [contactWeight_eq]
      change i + 3 * e (some 0) < 5000
      omega
    rw [coeff_weightedTruncation] at hz
    simpa only [hlt, ite_true] using hz
  · have hz := seedCoeff_eq_zero hcap (n := e none) (by omega)
    have hz' : flatCoeff (e none) F = 0 := by
      change toRow.symm (seedCoeff (e none) F) = 0
      rw [hz, map_zero]
    simp [hz']
private def nodeInput (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    (hcap : ∀ F ∈ V, Caps b.box F) (n : Fin 70001) : V →ₗ[Geom] Capped b.box.b :=
  ((normalize x v).toLinearMap ∘ₗ flatCoeff n ∘ₗ V.subtype).codRestrict _
    (fun F => normalize_mem_capped (coeff_mem_capped (hcap F F.2) n) x v)
private def nodeMap (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    (hcap : ∀ F ∈ V, Caps b.box F) : V →ₗ[Geom] (Fin 70001 → cappedRange b.box.b) :=
  LinearMap.pi fun n =>
    (origin.domRestrict (Capped b.box.b)).rangeRestrict ∘ₗ nodeInput b x v V hcap n
theorem codim_le_cappedRange (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    [Module.Finite Geom V] (hcap : ∀ F ∈ V, Caps b.box F) :
    codimIn V (contactAt x v) ≤ 70001 * Module.finrank Geom (cappedRange b.box.b) := by
  let A := nodeMap b x v V hcap
  have hzero (F : A.ker) : (F.1 : PhysicalRow) ∈ contactAt x v := by
    apply mem_contact_of_origin_eq_zero (hcap F.1 F.1.2)
    intro n
    have h := congrFun (LinearMap.mem_ker.mp F.2) n
    have hval := congrArg (fun z : cappedRange b.box.b => z.val) h
    change origin (normalize x v (flatCoeff n F.1.1)) = 0 at hval
    exact hval
  let f : A.ker →ₗ[Geom] ↥(V ⊓ contactAt x v) :=
    (V.subtype ∘ₗ A.ker.subtype).codRestrict _ fun F => Submodule.mem_inf.mpr ⟨F.1.2, hzero F⟩
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    have he := congrArg (fun s : ↥(V ⊓ contactAt x v) => (s : PhysicalRow)) h
    exact he
  have hk := LinearMap.finrank_le_finrank_of_injective (f := f) hf
  have hr := Submodule.finrank_le A.range
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hr
  have hnull := LinearMap.finrank_range_add_finrank_ker (K := Geom)
    (V := ↥V) (V₂ := Fin 70001 → cappedRange b.box.b) A
  unfold codimIn
  omega
end
end K1_13_4_2_2
end
section
namespace K1_13_4_2_2
noncomputable section
open K1_13 K1_13_4 K1_13_4_2
open scoped BigOperators
def c1 : Prop :=
  ∀ q < 6821, ∀ k < 7300,
    (Module.finrank Geom (PlaneSource q (offset k)) : ℤ) ≤ columnCount q (offset k)
def c2 : Prop :=
  ∀ q < 6821, ∀ k < 7300, ∀ p : Powers,
    kernelLower (remainingDegree q p) (remainingFlag q (offset k) p) ≤
      (Module.finrank Geom (LinearMap.ker (planeContact q (offset k))) : ℤ)
def c3 : Prop :=
  ∃ p : ℕ → ℕ → Powers,
    (∑ j ∈ Finset.range 1151, gradeBound p j) ≤ 1054250623200
def c4 : Prop :=
  ∃ p : ℕ → ℕ → Powers,
    (∑ j ∈ Finset.range 1149, gradeBound p (1151 + j)) ≤ 4082300934025
def c5 : Prop :=
  ∃ p : ℕ → ℕ → Powers,
    (∑ j ∈ Finset.range 2700, gradeBound p (2300 + j)) ≤ 5196036704622
def c6 : Prop :=
  ∃ p : ℕ → ℕ → Powers,
    (∑ j ∈ Finset.range 1790, gradeBound p (5000 + j)) ≤ 364983426528
private theorem plane_rank_le (h1 : c1) (h2 : c2) {q k : ℕ} (hq : q < 6821) (hk : k < 7300)
    (p : Powers) :
    Module.finrank Geom (LinearMap.range (planeContact q (offset k))) ≤ blockBound q (offset k) p := by
  let f := planeContact q (offset k)
  by_cases hcut : planeOrder q (offset k) ≤ 0
  · have hz : f = 0 := by
      ext L : 1
      change MvPolynomial.weightedTruncation (![2, 0, 1] : Fin 3 → ℕ)
        (planeOrder q (offset k)).toNat (MvPolynomial.bind₁ planeImage (L : Plane)) = 0
      apply (MvPolynomial.weightedTruncation_eq_zero_iff _ _ _).mpr
      simp [Int.toNat_of_nonpos hcut]
    change Module.finrank Geom (LinearMap.range f) ≤ _
    simp [hz, blockBound, hcut]
  have hdim := f.finrank_range_add_finrank_ker
  have hcols := h1 q hq k hk
  have hshift := h2 q hq k hk p
  have hbase := h2 q hq k hk (fun _ => 0)
  have hdeg : remainingDegree q (fun _ => 0) = residualDegree q := by simp [remainingDegree]
  have hflag : remainingFlag q (offset k) (fun _ => 0) = initialFlag q (offset k) := by
    funext i
    simp only [remainingFlag, Nat.cast_zero, zero_mul, Finset.sum_const_zero, sub_zero]
  rw [hdeg, hflag] at hbase
  change _ ≤ (Module.finrank Geom (LinearMap.ker f) : ℤ) at hshift hbase
  have hlower := max_le (Int.natCast_nonneg (Module.finrank Geom (LinearMap.ker f)))
    (max_le hbase hshift)
  change Module.finrank Geom (LinearMap.range f) ≤ _
  unfold blockBound
  simp only [hcut, ite_false]
  have hbound : (Module.finrank Geom (LinearMap.range f) : ℤ) ≤
      columnCount q (offset k) -
        max 0 (max (kernelLower (residualDegree q) (initialFlag q (offset k)))
          (kernelLower (remainingDegree q p) (remainingFlag q (offset k) p))) := by
    omega
  simpa using Int.toNat_le_toNat hbound
private theorem join_windows {a m n r s : ℕ}
    (h₁ : ∃ p : ℕ → ℕ → Powers, (∑ j ∈ Finset.range m, gradeBound p (a + j)) ≤ r)
    (h₂ : ∃ p : ℕ → ℕ → Powers, (∑ j ∈ Finset.range n, gradeBound p (a + m + j)) ≤ s) :
    ∃ p : ℕ → ℕ → Powers, (∑ j ∈ Finset.range (m + n), gradeBound p (a + j)) ≤ r + s := by
  obtain ⟨p₁, hp₁⟩ := h₁
  obtain ⟨p₂, hp₂⟩ := h₂
  let p : ℕ → ℕ → Powers := fun q => if q < a + m then p₁ q else p₂ q
  have hfirst : (∑ j ∈ Finset.range m, gradeBound p (a + j)) =
      ∑ j ∈ Finset.range m, gradeBound p₁ (a + j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have h := Nat.add_lt_add_left (Finset.mem_range.mp hj) a
    simp only [gradeBound, p, h, ite_true]
  have hsecond : (∑ j ∈ Finset.range n, gradeBound p (a + m + j)) =
      ∑ j ∈ Finset.range n, gradeBound p₂ (a + m + j) := by
    apply Finset.sum_congr rfl
    intro j _
    have h : ¬ a + m + j < a + m := by omega
    simp only [gradeBound, p, h, ite_false]
  refine ⟨p, ?_⟩
  rw [Finset.sum_range_add, hfirst]
  simp only [← Nat.add_assoc]
  rw [hsecond]
  exact Nat.add_le_add hp₁ hp₂
private theorem bank_bound (h3 : c3) (h4 : c4) (h5 : c5) (h6 : c6) (b : Bank) :
    ∃ p : ℕ → ℕ → Powers, (∑ q ∈ Finset.range (b.box.b + 1), gradeBound p q) ≤ b.nodeRank := by
  unfold c3 at h3
  have h34 := join_windows (a := 0) (m := 1151) (n := 1149)
    (r := 1054250623200) (s := 4082300934025) (by simpa only [Nat.zero_add] using h3) h4
  have h345 := join_windows (m := 2300) (n := 2700) (a := 0) h34 h5
  have h3456 := join_windows (m := 5000) (n := 1790) (a := 0) h345 h6
  cases b with
  | first =>
    change ∃ p : ℕ → ℕ → Powers, (∑ q ∈ Finset.range 6790, gradeBound p q) ≤ 10697571688375
    simpa only [Nat.zero_add, Nat.reduceAdd] using h3456
  | second =>
    have hAll := join_windows (m := 6790) (n := 31) (a := 0) h3456 tail_bound
    change ∃ p : ℕ → ℕ → Powers, (∑ q ∈ Finset.range 6821, gradeBound p q) ≤ 10697783317215
    simpa only [Nat.zero_add, Nat.reduceAdd] using hAll
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) (h6 : c6) :
    K1_13_4_2.c2 := by
  intro b x v V hV hcap
  let : Module.Finite Geom V := hV
  obtain ⟨p, hp⟩ := bank_bound h3 h4 h5 h6 b
  apply (codim_le_cappedRange b x v V hcap).trans
  apply Nat.mul_le_mul_left
  apply (cappedRange_le_sum b.box.b (fun q k => blockBound q (offset k) (p q k)) ?_).trans hp
  intro q hq k hk
  have hB : b.box.b + 1 ≤ 6821 := by cases b <;> decide
  exact (rank_originBlock_le_plane q k).trans (plane_rank_le h1 h2 (hq.trans_le hB) hk (p q k))
end
end K1_13_4_2_2
end
section
namespace K1_13_4_3
noncomputable section
open K1 K1_13 K1_13_4
open scoped Polynomial BigOperators
def atSeed {R : Type*} [CommSemiring R] (z : R) :
    SeedRow R →+* MvPolynomial (Fin 3) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => i.elim (MvPolynomial.C z) MvPolynomial.X)
def restoreJets (H res : Geom[X]) : Row 3 →+* Row 3 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i =>
    MvPolynomial.C (jet res i) +
      ∑ j : Fin 3, if j.val ≤ i.val then
        MvPolynomial.C (Polynomial.hasseDeriv (i.val - j.val) H) * MvPolynomial.X j
      else 0)
def restoreAt (H res : Geom[X]) (z : Geom) (F : PhysicalRow) : Row 3 :=
  restoreJets H res (atSeed (Polynomial.C z) F)
def RawCut (t : ℕ) (Q : Row 3) : Prop :=
  ∀ m ∈ Q.support, (Q.coeff m).natDegree +
    m.sum (fun j e => (131071 - j.val) * e) ≤ t
def RawContact (m : ℕ) (w : I → K) (H res : Geom[X]) (Q : Row 3) : Prop :=
  ∀ i (T : Geom[X]), (H * T + res).eval (embed (node i)) = embed (w i) →
    (Polynomial.X - Polynomial.C (embed (node i))) ^ m ∣ atJet Q T
def clearedSeed (H : Geom[X]) (i : ℕ) (F : PhysicalRow) : PhysicalRow :=
  MvPolynomial.C (H ^ (3 * i)) * mixedHasse (Finsupp.single none i) F
end
end K1_13_4_3
end
section
namespace K1_13_4_3
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 12000
open K1 K1_13 K1_13_4 Polynomial
open scoped Polynomial BigOperators
private def contactError (S : Geom[X]) (x v : Geom) : Geom[X] :=
  S - Polynomial.C v + (Polynomial.C x - Polynomial.X) * hasseDeriv 1 S + (Polynomial.C x - Polynomial.X) ^ 2 * hasseDeriv 2 S
private theorem contactError_dvd (S : Geom[X]) (x v : Geom) (h : S.eval x = v) :
    (Polynomial.X - Polynomial.C x) ^ 3 ∣ contactError S x v := by
  have ht := map_dvd (Polynomial.taylorAlgHom (-x)).toRingHom
    (X_pow_succ_dvd_taylor_sub_C_sub_movingHasseSum_of_eval_eq 2 h)
  change Polynomial.taylor (-x) ((Polynomial.X : Geom[X]) ^ 3) ∣
    Polynomial.taylor (-x) (Polynomial.taylor x S - Polynomial.C v - movingHasseSum x S 2) at ht
  simp only [sub_eq_add_neg, LinearMap.map_add, LinearMap.map_neg, taylor_C, taylor_taylor,
    neg_add_cancel, taylor_zero, movingHasseSum, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, taylor_mul, taylor_X, pow_zero, C_1, one_mul, pow_succ, C_neg] at ht
  convert ht using 1 <;> simp [contactError, sub_eq_add_neg] <;> ring
theorem jet_restore (H res T : Geom[X]) (i : Fin 3) :
    jet (H * T + res) i = jet res i +
      ∑ j : Fin 3, if j.val ≤ i.val then
        hasseDeriv (i.val - j.val) H * jet T j else 0 := by
  have hj :
      ∑ j : Fin 3, (if j.val ≤ i.val then
        hasseDeriv (i.val - j.val) H * jet T j else 0) =
      hasseDeriv i.val (H * T) := by
    rw [hasseDeriv_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    fin_cases i <;>
      norm_num [Fin.sum_univ_three, Finset.sum_range_succ, jet] <;> ring
  rw [hj]
  change hasseDeriv i.val (H * T + res) = hasseDeriv i.val res + hasseDeriv i.val (H * T)
  rw [LinearMap.map_add, add_comm]
private theorem eval_restoreJets (H res T : Geom[X]) (F : Row 3) :
    atJet (restoreJets H res F) T = atJet F (H * T + res) := by
  have heval : (MvPolynomial.eval (jet T)).comp (restoreJets H res) =
      MvPolynomial.eval (jet (H * T + res)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [restoreJets]
    · intro i
      simp only [RingHom.comp_apply, restoreJets, MvPolynomial.eval₂Hom_X', map_add,
        MvPolynomial.eval_C, map_sum, apply_ite, map_mul, MvPolynomial.eval_X, map_zero]
      exact (jet_restore H res T i).symm
  exact DFunLike.congr_fun heval F
private theorem physicalContact_eval (F : PhysicalRow) (m : ℕ) (x v z : Geom) (S : Geom[X])
    (hF : ∀ a : SeedVar →₀ ℕ, (Polynomial.X - Polynomial.C x) ^ (m - 3 * a (some 0)) ∣
      (backwardShift x v F).coeff a) (hS : S.eval x = v) :
    (Polynomial.X - Polynomial.C x) ^ m ∣ atJet (atSeed (Polynomial.C z) F) S := by
  classical
  let d : Geom[X] := Polynomial.X - Polynomial.C x
  let e := contactError S x v
  let g : SeedVar → Geom[X] := fun j => j.elim (Polynomial.C z) (fun k => if k = 0 then e else jet S k)
  let ev := MvPolynomial.eval g
  let back : PhysicalRow →+* PhysicalRow := MvPolynomial.eval₂Hom MvPolynomial.C (fun j =>
    if j = some 0 then
      MvPolynomial.X (some 0) + MvPolynomial.C (Polynomial.C v) -
        MvPolynomial.C (Polynomial.C x - Polynomial.X) * MvPolynomial.X (some 1) -
        MvPolynomial.C ((Polynomial.C x - Polynomial.X) ^ 2) * MvPolynomial.X (some 2)
    else MvPolynomial.X j)
  have hcomp : ev.comp back = (MvPolynomial.eval (jet S)).comp (atSeed (Polynomial.C z)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ev, back, atSeed]
    · intro j
      cases j with
      | none => simp [ev, back, atSeed, g]
      | some j =>
        by_cases hj : j = 0
        · subst j
          simp [ev, back, atSeed, g, e, contactError, jet, hasseDeriv_zero]
          ring
        · simp [ev, back, atSeed, g, hj]
  change d ^ m ∣ (MvPolynomial.eval (jet S)) (atSeed (Polynomial.C z) F)
  have heval : ev (back F) = MvPolynomial.eval (jet S) (atSeed (Polynomial.C z) F) :=
    DFunLike.congr_fun hcomp F
  rw [← heval]
  set B := back F with hB
  rw [B.as_sum, map_sum]
  apply Finset.dvd_sum
  intro a _
  rw [MvPolynomial.eval_monomial]
  have hcoeff : d ^ (m - 3 * a (some 0)) ∣ B.coeff a := hF a
  have he : d ^ 3 ∣ g (some 0) := by
    simpa [d, g, e] using contactError_dvd S x v hS
  have hprod : d ^ (3 * a (some 0)) ∣ a.prod (fun j n => g j ^ n) := by
    rw [pow_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    exact (pow_dvd_pow_of_dvd he _).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ (some (0 : Fin 3))))
  have hle : m ≤ (m - 3 * a (some 0)) + 3 * a (some 0) := by omega
  exact (pow_dvd_pow d hle).trans (by rw [pow_add]; exact mul_dvd_mul hcoeff hprod)
theorem rawContact_of_restore (m : ℕ) (w : I → K) (H res : Geom[X]) (z : Geom) (r : ℕ)
    (F : PhysicalRow) (Q : Row 3) (hnodes : ∀ i, H.eval (embed (node i)) ≠ 0)
    (hF : ∀ i (a : SeedVar →₀ ℕ),
      (Polynomial.X - Polynomial.C (embed (node i))) ^ (m - 3 * a (some 0)) ∣
        (backwardShift (embed (node i)) (embed (w i)) F).coeff a)
    (hQ : restoreAt H res z F = MvPolynomial.C (H ^ r) * Q) :
    RawContact m w H res Q := by
  intro i T hT
  have hd : IsCoprime (Polynomial.X - Polynomial.C (embed (node i))) H :=
    (prime_X_sub_C _).coprime_iff_not_dvd.mpr (by
      rw [dvd_iff_isRoot]
      exact hnodes i)
  have hh := physicalContact_eval F m _ _ z _ (hF i) hT
  rw [← eval_restoreJets, ← restoreAt, hQ] at hh
  apply (hd.pow (m := m) (n := r)).dvd_of_dvd_mul_left
  simpa only [atJet, map_mul, MvPolynomial.eval_C] using hh
end
end K1_13_4_3
end
section
namespace K1_13_4_2_2_6
open K1_13_4_2_2
open scoped BigOperators
set_option maxHeartbeats 900000
def quarter (w : ℤ) : ℤ := w ^ 2 / 4
private def cost (w : ℤ) : ℤ := quarter (w + 1)
private theorem twice_triangle (w : ℤ) : 2 * triangular w = w * (w + 1) := by
  unfold triangular
  apply Int.mul_ediv_cancel_of_dvd
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with h | h
  · have hw : w = 2 * (w / 2) := by omega
    exact dvd_mul_of_dvd_left (by rw [hw]; exact dvd_mul_right _ _) _
  · have hw : w + 1 = 2 * (w / 2 + 1) := by omega
    exact dvd_mul_of_dvd_right (by rw [hw]; exact dvd_mul_right _ _) _
theorem quarter_spec (w : ℤ) : 4 * quarter w = w ^ 2 - w % 2 := by
  unfold quarter
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with h | h
  · have hw : w = 2 * (w / 2) := by omega
    have he : w ^ 2 = 4 * (w / 2) ^ 2 := by
      calc _ = (2 * (w / 2)) ^ 2 := congrArg (· ^ 2) hw
           _ = _ := by ring
    rw [he, h]
    omega
  · have hw : w = 2 * (w / 2) + 1 := by omega
    have he : w ^ 2 = 4 * ((w / 2) ^ 2 + w / 2) + 1 := by
      calc _ = (2 * (w / 2) + 1) ^ 2 := congrArg (· ^ 2) hw
           _ = _ := by ring
    rw [he, h]
    omega
private theorem cost_spec (w : ℤ) : 4 * cost w = w ^ 2 + 2 * w + w % 2 := by
  unfold cost
  rw [quarter_spec]
  have h : (w + 1) % 2 + w % 2 = 1 := by omega
  nlinarith only [h]
private theorem colength_eq_cost {a w : ℤ} (ha : a ≤ (w + 1) / 2) (hw : 0 ≤ w) :
    colength ⟨a, w⟩ = cost w := by
  have hu : 0 ≤ (w + 1) / 2 := by omega
  have huv : (w + 1) / 2 ≤ w := by omega
  have h : (w + 1) / 2 = w / 2 + w % 2 := by omega
  have h' : w - (w + 1) / 2 = w / 2 := by omega
  unfold colength
  simp only [max_eq_right ha, max_eq_right hu, max_eq_right huv]
  rw [h', h]
  have h₁ := twice_triangle (w / 2 + w % 2)
  have h₂ := twice_triangle (w / 2)
  have h₃ := cost_spec w
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with he | he
  · have hw : w = 2 * (w / 2) := by omega
    rw [he] at h₁ h₃ ⊢
    conv at h₃ => rhs; rw [hw]
    nlinarith only [h₁, h₂, h₃]
  · have hw : w = 2 * (w / 2) + 1 := by omega
    rw [he] at h₁ h₃ ⊢
    conv at h₃ => rhs; rw [hw]
    nlinarith only [h₁, h₂, h₃]
private theorem linear_gain (k a t : ℤ) (ha : a = 0 ∨ t = a + 2 * k + 1) :
    triangular (2301 - 2 * a) - cost (2300 - k - 2 * a) - cost (2300 - 2 * a) -
        cost (t - a) =
      triangular 2301 - cost (2300 - k) - cost 2300 - cost t + quarter a := by
  rcases ha with rfl | ht
  · simp [quarter]
  have hp : (2300 - k - 2 * a) % 2 = (2300 - k) % 2 := by omega
  have hq : (2300 - 2 * a) % 2 = 0 := by omega
  have ho : (t - a) % 2 = 1 := by omega
  have hs : t % 2 = 1 - a % 2 := by omega
  have hTP := twice_triangle (2301 - 2 * a)
  have hT := twice_triangle 2301
  have hPP := cost_spec (2300 - k - 2 * a)
  have hP := cost_spec (2300 - k)
  have hQP := cost_spec (2300 - 2 * a)
  have hQ := cost_spec 2300
  have hOP := cost_spec (t - a)
  have hO := cost_spec t
  have hA := quarter_spec a
  rw [hp] at hPP
  rw [hq] at hQP
  rw [ho] at hOP
  rw [hs] at hO
  norm_num only [Int.reduceMod] at hQ
  rw [ht] at hOP hO ⊢
  nlinarith only [hTP, hT, hPP, hP, hQP, hQ, hOP, hO, hA]
private theorem conic_gain (u : ℤ) :
    triangular (6 * u - 1) - cost (4 * u - 1) - cost (6 * u - 2) -
      cost (4 * u - 1) = u ^ 2 := by
  have hT := twice_triangle (6 * u - 1)
  have hP := cost_spec (4 * u - 1)
  have hQ := cost_spec (6 * u - 2)
  rw [show (4 * u - 1) % 2 = 1 by omega] at hP
  rw [show (6 * u - 2) % 2 = 0 by omega] at hQ
  nlinarith only [hT, hP, hQ]
def columns (k : ℕ) : ℤ := 1324801 - quarter (2301 - (k : ℤ))
def linearExp (r k : ℕ) : ℤ := (r : ℤ) - 1 - 3 * k
def conicExp (r k : ℕ) : ℤ := 2 * (r : ℤ) - 2301 - 3 * k
def conicParameter (r k : ℕ) : ℤ := 2 * (k : ℤ) + 1151 - r
def powers (r k : ℕ) (i : Fin 6) : ℕ :=
  if i = 0 ∨ i = 3 then (linearExp r k).toNat
  else if i = 5 then (conicExp r k).toNat else 0
def rankTerm (r k : ℕ) : ℤ :=
  if 0 < conicExp r k then
    columns k - (max 0 (conicParameter r k)) ^ 2
  else quarter ((r : ℤ) - k + 1) - quarter (max 0 (linearExp r k))
private theorem columnCount_eq {q k : ℕ} (hq : 5000 ≤ q) (hk : k < 2300) :
    columnCount q (offset k) = columns k := by
  have hd : residualDegree q = 2300 := min_eq_right (by omega)
  have harg : min (2300 : ℤ) (-offset k - 1) = 2300 - k - 1 := by unfold offset; omega
  have hpos : ¬ (2300 - (k : ℤ) - 1) < 0 := by omega
  have hmin : min (2300 - (k : ℤ) - 1) 4600 = 2300 - k - 1 := min_eq_left (by omega)
  have hmax : max (0 : ℤ) (2300 - k - 1 - 2300) = 0 := max_eq_left (by omega)
  unfold columnCount
  rw [hd, harg]
  change cumulative 2300 2300 - cumulative 2300 (2300 - (k : ℤ) - 1) = _
  rw [show cumulative 2300 2300 = 1324801 by decide]
  simp only [cumulative, hpos, ite_false, show (2 * 2300 : ℤ) = 4600 by decide, hmin, hmax]
  simp only [columns, quarter, show triangular 0 = 0 by decide, sub_zero]
  congr 2
  ring
private theorem sum_powers (r k : ℕ) (f : Fin 6 → ℤ) :
    (∑ j, (powers r k j : ℤ) * f j) =
      ((linearExp r k).toNat : ℤ) * (f 0 + f 3) + ((conicExp r k).toNat : ℤ) * f 5 := by
  simp [Fin.sum_univ_succ, powers, Fin.succ, mul_add, add_assoc]
private theorem square_mono {x y : ℤ} (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  nlinarith only [mul_nonneg (show 0 ≤ y - x by omega) (show 0 ≤ y + x by omega)]
private theorem conic_term_nonneg {r k : ℕ} (hk : k < 2300) (hb : 0 < conicExp r k) :
    0 ≤ columns k - (max 0 (conicParameter r k)) ^ 2 := by
  let u := max 0 (conicParameter r k)
  have hu : 0 ≤ 2 * u := by dsimp [u]; omega
  have huk : 2 * u ≤ (k : ℤ) := by
    unfold conicExp at hb
    dsimp [u, conicParameter]
    omega
  have hs := square_mono hu huk
  have hq := quarter_spec (2301 - (k : ℤ))
  have hmod : 0 ≤ (2301 - (k : ℤ)) % 2 := by omega
  have hprod : 0 ≤ (k : ℤ) * (2301 - k) := by
    exact mul_nonneg (by omega) (by omega)
  change 0 ≤ columns k - u ^ 2
  unfold columns
  nlinarith only [hs, hq, hmod, hprod]
theorem block_le {q k : ℕ} (hq : 5000 ≤ q) (hk : k < 7300 - q) :
    (blockBound q (offset k) (powers (7300 - q) k) : ℤ) ≤ rankTerm (7300 - q) k := by
  let r : ℕ := 7300 - q
  let a : ℤ := ((linearExp r k).toNat : ℤ)
  let b : ℤ := ((conicExp r k).toNat : ℤ)
  let t : ℤ := (r : ℤ) - k
  let p := powers r k
  have ha : a = max 0 (linearExp r k) := by
    simpa only [max_comm] using Int.toNat_eq_max (linearExp r k)
  have hb : b = max 0 (conicExp r k) := by
    simpa only [max_comm] using Int.toNat_eq_max (conicExp r k)
  have han : 0 ≤ a := by omega
  have hkn : k < 2300 := by omega
  have hd : residualDegree q = 2300 := min_eq_right (by omega)
  have ho : planeOrder q (offset k) = t := by unfold planeOrder offset t r; omega
  have ht : 0 < t := by dsimp [t, r]; omega
  have hc := columnCount_eq hq hkn
  have hd' : remainingDegree q p = 2300 - 2 * a - 2 * b := by
    dsimp only [p, remainingDegree]
    rw [hd, sum_powers]
    simp [factorDegree, a, b]
    ring
  have hP : remainingFlag q (offset k) p 0 = ⟨-a-b, 2300 - k - 2*a-b⟩ := by
    simp [p, remainingFlag, sum_powers, initialFlag, factorFlag, offset, a, b] <;>
      constructor <;> ring
  have hQ : remainingFlag q (offset k) p 1 = ⟨1150-a-b, 2300 - 2*a-2*b⟩ := by
    simp [p, remainingFlag, sum_powers, initialFlag, factorFlag, hd, a, b] <;>
      constructor <;> ring
  have hO : remainingFlag q (offset k) p 2 = ⟨-a-b, t-a-2*b⟩ := by
    simp [p, remainingFlag, sum_powers, initialFlag, factorFlag, ho, a, b] <;>
      constructor <;> ring
  let shift := kernelLower (remainingDegree q p) (remainingFlag q (offset k) p)
  have bound {v : ℤ} (hv : 0 ≤ v)
      (hle : columns k - max 0 (max (kernelLower (residualDegree q) (initialFlag q (offset k))) shift) ≤ v) :
      (blockBound q (offset k) p : ℤ) ≤ v := by
    rw [blockBound, ite_eq_right (by omega : ¬ planeOrder q (offset k) ≤ 0), hc,
      Int.toNat_eq_max]
    exact max_le hle hv
  have byShift {v : ℤ} (hv : 0 ≤ v) (hle : columns k - shift ≤ v) :
      (blockBound q (offset k) p : ℤ) ≤ v :=
    bound hv ((sub_le_sub_left ((le_max_right _ _).trans (le_max_right _ _)) _).trans hle)
  change (blockBound q (offset k) p : ℤ) ≤ rankTerm r k
  by_cases h : 0 < conicExp r k
  · let u := conicParameter r k
    have hnon := conic_term_nonneg hkn h
    simp only [rankTerm, h, ite_true]
    by_cases hu : 0 < u
    · have hrel : a = linearExp r k ∧ b = conicExp r k := by
        have ha' : 0 ≤ linearExp r k := by unfold linearExp conicExp at *; dsimp [r] at *; omega
        exact ⟨ha.trans (max_eq_right ha'), hb.trans (max_eq_right h.le)⟩
      have hdeg : 2300 - 2*a-2*b = 6*u-2 := by
        rw [hrel.1, hrel.2]; unfold u conicParameter linearExp conicExp; ring
      have hwp : 2300 - (k : ℤ) - 2*a-b = 4*u-1 := by
        rw [hrel.1, hrel.2]; unfold u conicParameter linearExp conicExp; ring
      have hwo : t-a-2*b = 4*u-1 := by
        rw [hrel.1, hrel.2]; unfold u conicParameter linearExp conicExp t; ring
      have hs : shift = u ^ 2 := by
        dsimp [shift]
        rw [kernelLower, hd', Fin.sum_univ_three, hP, hQ, hO, hwp, hwo]
        simp only [hdeg, ite_eq_right (by omega : ¬ 6*u-2 < 0)]
        rw [colength_eq_cost (a := -a-b) (w := 4*u-1) (by omega) (by omega),
          colength_eq_cost (a := 1150-a-b) (w := 6*u-2) (by omega) (by omega),
          show 6*u-2+1 = 6*u-1 by ring]
        linarith only [conic_gain u]
      exact byShift hnon (by rw [hs, max_eq_right hu.le])
    · apply bound hnon
      rw [max_eq_left (show u ≤ 0 by omega)]
      have hmax := le_max_left (0 : ℤ) (max (kernelLower (residualDegree q)
        (initialFlag q (offset k))) shift)
      simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
      omega
  · have hb' : b = 0 := hb.trans (max_eq_left (by omega))
    have halt : a = 0 ∨ t = a + 2 * k + 1 := by unfold linearExp at ha; dsimp [t]; omega
    have had : a ≤ t := by omega
    have hw : 0 ≤ 2300 - (k : ℤ) - 2*a := by
      unfold linearExp at ha
      unfold conicExp at h
      omega
    have hs : shift = columns k - cost t + quarter a := by
      dsimp [shift]
      rw [kernelLower, hd', Fin.sum_univ_three, hP, hQ, hO, hb']
      simp only [mul_zero, sub_zero, ite_eq_right (by omega : ¬ 2300 - 2*a < 0)]
      rw [colength_eq_cost (by omega) (by omega), colength_eq_cost (by omega) (by omega),
        colength_eq_cost (by omega) (by omega)]
      calc
        _ = triangular (2301 - 2*a) - cost (2300 - k - 2*a) - cost (2300 - 2*a) -
            cost (t-a) := by ring
        _ = _ := by
          rw [linear_gain _ _ _ halt]
          have hconst : triangular 2301 - cost 2300 = 1324801 := by decide
          have hcost : cost (2300 - (k : ℤ)) = quarter (2301-k) := by
            unfold cost
            congr 1
            ring
          unfold columns
          rw [hcost]
          linarith only [hconst]
    have hsq := square_mono han (show a ≤ t + 1 by omega)
    simp only [rankTerm, h, ite_false, ← ha]
    change (blockBound q (offset k) p : ℤ) ≤ cost t - quarter a
    apply byShift
    · unfold cost quarter
      omega
    · rw [hs]
      linarith only []
end K1_13_4_2_2_6
end
section
namespace K1_13_4_3
noncomputable section
open K1 K1_13 K1_13_4
open MvPolynomial
variable {σ R S : Type*} [CommSemiring R] [CommSemiring S]
def taylor : MvPolynomial σ R →+* MvPolynomial σ (MvPolynomial σ R) :=
  eval₂Hom (C.comp C) (fun i => MvPolynomial.X i + C (MvPolynomial.X i))
def hasse (a : σ →₀ ℕ) (F : MvPolynomial σ R) : MvPolynomial σ R :=
  (taylor F).coeff a
theorem partial_eq_mixedHasse (a : SeedVar →₀ ℕ) (F : PhysicalRow) :
    hasse a F = mixedHasse a F := rfl
theorem partial_mul_X [DecidableEq σ] (a : σ →₀ ℕ) (F : MvPolynomial σ R) (i : σ) :
    hasse a (F * MvPolynomial.X i) =
      (if i ∈ a.support then hasse (a - Finsupp.single i 1) F else 0) +
        hasse a F * MvPolynomial.X i := by
  simp only [hasse, taylor, map_mul, eval₂Hom_X', mul_add, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, coeff_mul_X']
  rw [mul_comm _ (C (MvPolynomial.X i)), coeff_C_mul, mul_comm (MvPolynomial.X i)]
theorem partial_C [DecidableEq σ] (a : σ →₀ ℕ) (c : R) :
    hasse a (C c) = if a = 0 then C c else 0 := by
  classical
  simp [hasse, taylor, coeff_C, eq_comm]
private def CoeffSplit (F : MvPolynomial σ R) (a b : σ →₀ ℕ) : Prop :=
  (F.coeff (a + b) = 0 → (hasse a F).coeff b = 0) ∧
    ((∀ i, i ∉ a.support ∨ i ∉ b.support) →
      (hasse a F).coeff b = F.coeff (a + b))
private theorem add_mem_support_iff {a b : σ →₀ ℕ} {i : σ} :
    i ∈ (a + b).support ↔ i ∈ a.support ∨ i ∈ b.support := by
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply]
  omega
private theorem sub_single_add [DecidableEq σ] {a b : σ →₀ ℕ} {i : σ}
    (ha : i ∈ a.support) :
    (a - Finsupp.single i 1) + b = a + b - Finsupp.single i 1 := by
  have hle : Finsupp.single i 1 ≤ a := by
    rw [Finsupp.single_le_iff]
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ha)
  apply add_right_cancel (b := Finsupp.single i 1)
  calc
    _ = (a - Finsupp.single i 1 + Finsupp.single i 1) + b := by ac_rfl
    _ = a + b := by rw [tsub_add_cancel_of_le hle]
    _ = _ := (tsub_add_cancel_of_le (hle.trans le_self_add)).symm
private theorem coeffSplit_mul_X (F : MvPolynomial σ R)
    (hF : ∀ a b, CoeffSplit F a b) (i : σ) (a b : σ →₀ ℕ) :
    CoeffSplit (F * MvPolynomial.X i) a b := by
  classical
  unfold CoeffSplit
  rw [partial_mul_X, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_X', coeff_mul_X']
  have ha' (hd : ∀ j, j ∉ a.support ∨ j ∉ b.support) (j : σ) :
      j ∉ (a - Finsupp.single i 1).support ∨ j ∉ b.support :=
    (hd j).imp (fun hj hk => hj (Finsupp.support_mono tsub_le_self hk)) id
  have hb' (hd : ∀ j, j ∉ a.support ∨ j ∉ b.support) (j : σ) :
      j ∉ a.support ∨ j ∉ (b - Finsupp.single i 1).support :=
    (hd j).imp id (fun hj hk => hj (Finsupp.support_mono tsub_le_self hk))
  simp only [add_mem_support_iff]
  by_cases ha : i ∈ a.support
  · have hsub := sub_single_add (b := b) ha
    by_cases hb : i ∈ b.support
    · have hsub' : a + (b - Finsupp.single i 1) = a + b - Finsupp.single i 1 := by
        simpa only [add_comm] using sub_single_add (b := a) hb
      simp only [ha, hb, true_or, ite_true]
      refine ⟨fun hz => ?_, fun hd => False.elim ((hd i).elim (fun h => h ha) (fun h => h hb))⟩
      rw [(hF _ _).1 ((congrArg F.coeff hsub).trans hz), (hF _ _).1 ((congrArg F.coeff hsub').trans hz), add_zero]
    · simp only [ha, hb, true_or, ite_true, ite_false, add_zero]
      exact ⟨fun hz => (hF _ _).1 ((congrArg F.coeff hsub).trans hz),
        fun hd => ((hF _ _).2 (ha' hd)).trans (congrArg F.coeff hsub)⟩
  · by_cases hb : i ∈ b.support
    · have hsub : a + (b - Finsupp.single i 1) = a + b - Finsupp.single i 1 := by
        simpa only [add_comm] using sub_single_add (b := a) hb
      simp only [ha, hb, false_or, ite_true, ite_false, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, zero_add]
      exact ⟨fun hz => (hF _ _).1 ((congrArg F.coeff hsub).trans hz),
        fun hd => ((hF _ _).2 (hb' hd)).trans (congrArg F.coeff hsub)⟩
    · simp [ha, hb]
private theorem coeffSplit_monomial (m : σ →₀ ℕ) (c : R) (a b : σ →₀ ℕ) :
    CoeffSplit (monomial m c) a b := by
  classical
  refine MvPolynomial.induction_on_monomial (motive := fun F => ∀ a b, CoeffSplit F a b)
    ?_ (fun G i ih => coeffSplit_mul_X G ih i) m c a b
  intro c a b
  unfold CoeffSplit
  by_cases ha : a = 0
  · subst a
    simp [partial_C]
  · have hab : a + b ≠ 0 := fun hz => ha (add_eq_zero.mp hz).1
    simp [partial_C, coeff_C, ha, Ne.symm hab]
theorem coeff_partial (a b : σ →₀ ℕ) (F : MvPolynomial σ R) : CoeffSplit F a b := by
  classical
  unfold CoeffSplit
  have hf : (hasse a F).coeff b = ∑ m ∈ F.support,
      (hasse a (monomial m (F.coeff m))).coeff b := by
    conv_lhs => rw [F.as_sum]
    simp only [hasse, map_sum, coeff_sum]
  rw [hf]
  have hzero (m : σ →₀ ℕ) (hm : m ≠ a + b) :
      (hasse a (monomial m (F.coeff m))).coeff b = 0 :=
    (coeffSplit_monomial m _ _ _).1 (by simp [coeff_monomial, hm])
  by_cases hmem : a + b ∈ F.support
  · rw [Finset.sum_eq_single_of_mem _ hmem (fun m _ hm => hzero m hm)]
    have h := coeffSplit_monomial (a + b) (F.coeff (a + b)) a b
    simpa [CoeffSplit] using h
  · rw [Finset.sum_eq_zero (fun m hm => hzero m (fun he => hmem (he ▸ hm)))]
    have hz : F.coeff (a + b) = 0 := by simpa [MvPolynomial.mem_support_iff] using hmem
    simp [hz]
theorem coeff_partial_eq_zero (a b : σ →₀ ℕ) (F : MvPolynomial σ R)
    (h : F.coeff (a + b) = 0) : (hasse a F).coeff b = 0 :=
  (coeff_partial a b F).1 h
theorem coeff_partial_eq_of_disjoint (a b : σ →₀ ℕ) (F : MvPolynomial σ R)
    (h : ∀ i, i ∉ a.support ∨ i ∉ b.support) :
    (hasse a F).coeff b = F.coeff (a + b) :=
  (coeff_partial a b F).2 h
theorem map_partial (f : R →+* S) (a : σ →₀ ℕ) (F : MvPolynomial σ R) :
    map f (hasse a F) = hasse a (map f F) := by
  let lhs : MvPolynomial σ R →+* MvPolynomial σ (MvPolynomial σ S) :=
    (map (map f)).comp taylor
  let rhs : MvPolynomial σ R →+* MvPolynomial σ (MvPolynomial σ S) :=
    taylor.comp (map f)
  have h : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs, taylor]
    · intro i
      simp [lhs, rhs, taylor]
  simpa only [lhs, rhs, RingHom.comp_apply, coeff_map, hasse] using
    congrArg (fun G : MvPolynomial σ (MvPolynomial σ S) => G.coeff a) (DFunLike.congr_fun h F)
theorem translate_partial (y : σ → GenericX) (a : σ →₀ ℕ)
    (F : MvPolynomial σ GenericX) :
    K1_13_4.translate y (hasse a F) = hasse a (K1_13_4.translate y F) := by
  let lhs : MvPolynomial σ GenericX →+* MvPolynomial σ (MvPolynomial σ GenericX) :=
    (map (K1_13_4.translate y)).comp taylor
  let rhs : MvPolynomial σ GenericX →+* MvPolynomial σ (MvPolynomial σ GenericX) :=
    taylor.comp (K1_13_4.translate y)
  have h : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs, K1_13_4.translate, taylor]
    · intro i
      simp [lhs, rhs, K1_13_4.translate, taylor, add_assoc]
  simpa only [lhs, rhs, RingHom.comp_apply, coeff_map, hasse] using
    congrArg (fun G : MvPolynomial σ (MvPolynomial σ GenericX) => G.coeff a)
      (DFunLike.congr_fun h F)
theorem translate_atSeed (z : GenericX) (y : Fin 3 → GenericX) (F : GenericRow) :
    K1_13_4.translate y (atSeed z F) = atSeed 0 (K1_13_4.translate (atPoint z y) F) := by
  have h : (K1_13_4.translate y).comp (atSeed z) = (atSeed 0).comp (K1_13_4.translate (atPoint z y)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [atSeed, K1_13_4.translate]
    · intro i
      cases i <;> simp [atSeed, K1_13_4.translate, atPoint]
  exact DFunLike.congr_fun h F
theorem coeff_atSeed_zero (F : GenericRow) (b : Fin 3 →₀ ℕ) :
    (atSeed 0 F).coeff b = F.coeff (b.optionElim 0) := by
  let e := (optionEquivLeft GenericX (Fin 3)).toRingHom
  have h : atSeed (0 : GenericX) = (Polynomial.evalRingHom 0).comp e := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [e, atSeed, optionEquivLeft_C]
    · intro i
      cases i <;> simp [e, atSeed, optionEquivLeft_X_some, optionEquivLeft_X_none]
  rw [h, RingHom.comp_apply]
  change ((asSeedPoly F).eval 0).coeff b = _
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  exact optionEquivLeft_coeff_coeff GenericX F 0 b
end
end K1_13_4_3
end
section
namespace K1_13_4_2_2_6
open K1_13_4_2_2 Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
private def affineSquares (a b : ℤ) (n : ℕ) : ℤ :=
  let N : ℤ := n
  (6 * N * a^2 + 6 * a*b * N*(N-1) + b^2 * N*(N-1)*(2*N-1)) / 6
private theorem sum_affineSquares (a b : ℤ) (n : ℕ) :
    (∑ k ∈ range n, (a + b * (k : ℤ))^2) = affineSquares a b n := by
  have h (n : ℕ) : 6 * (∑ k ∈ range n, (a+b*(k : ℤ))^2) =
      6 * (n : ℤ) * a^2 + 6*a*b*n*((n : ℤ)-1) + b^2*n*((n : ℤ)-1)*(2*(n : ℤ)-1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, mul_add, ih, Nat.cast_succ]
      ring
  dsimp [affineSquares]
  rw [← h n]
  omega
private def affineQuarters (a b : ℤ) (n : ℕ) : ℤ :=
  (affineSquares a b n - ((n : ℤ) + a % 2) / 2) / 4
private theorem sum_affineQuarters (a b : ℤ) (n : ℕ) (hb : b % 2 = 1) :
    (∑ k ∈ range n, quarter (a + b * (k : ℤ))) = affineQuarters a b n := by
  have hmod (k : ℕ) : (a + b * (k : ℤ)) % 2 = (a + (k : ℤ)) % 2 := by
    rw [Int.add_emod a, Int.mul_emod, hb, one_mul]
    omega
  have hpar (n : ℕ) : (∑ k ∈ range n, (a + b * (k : ℤ)) % 2) = ((n : ℤ) + a % 2) / 2 := by
    induction n with
    | zero =>
      simp
      omega
    | succ n ih =>
      rw [sum_range_succ, ih, hmod, Nat.cast_succ]
      omega
  have hsum : 4 * (∑ k ∈ range n, quarter (a + b * (k : ℤ))) =
      affineSquares a b n - ((n : ℤ) + a % 2) / 2 := by
    rw [mul_sum]
    simp_rw [quarter_spec]
    rw [sum_sub_distrib, sum_affineSquares, hpar]
  unfold affineQuarters
  omega
private theorem sum_split_at {f : ℕ → ℤ} {m n : ℕ} (h : m ≤ n) :
    (∑ k ∈ range n, f k) =
      (∑ k ∈ range m, f k) + ∑ k ∈ range (n-m), f (m+k) := by
  simpa only [Nat.add_sub_of_le h, Nat.add_comm] using sum_range_add f m (n-m)
private def conicCut (r : ℕ) : ℕ := ((2*(r : ℤ)-2299) / 3).toNat
private def lineCut (r : ℕ) : ℕ := (r+1)/3
private def zeroCut (r : ℕ) : ℕ := min (conicCut r) (((r : ℤ)-1149)/2).toNat
private def gradeValue (r : ℕ) : ℤ :=
  let c := conicCut r
  let z := zeroCut r
  let a := lineCut r
  (c : ℤ)*1324801 - affineQuarters 2301 (-1) c -
    affineSquares (2*(z : ℤ)+1151-r) 2 (c-z) +
    (affineQuarters ((r : ℤ)+1-c) (-1) (r-c) -
      affineQuarters ((r : ℤ)-1-3*c) (-3) (a-c))
private theorem sum_rankTerm (r : ℕ) (hr : r ≤ 2300) :
    (∑ k ∈ range r, rankTerm r k) = gradeValue r := by
  let c := conicCut r
  let a := lineCut r
  let z := zeroCut r
  have hc (k : ℕ) : k < c ↔ 0 < conicExp r k := by dsimp [c, conicCut, conicExp]; omega
  have ha (k : ℕ) : k < a ↔ 0 < linearExp r k := by dsimp [a, lineCut, linearExp]; omega
  have hCA : c ≤ a := by dsimp [c, conicCut, a, lineCut]; omega
  have hAr : a ≤ r := by dsimp [a, lineCut]; omega
  have hCZ : z ≤ c := min_le_left _ _
  have hz (k : ℕ) (hk : k < c) : k < z ↔ conicParameter r k ≤ 0 := by
    dsimp [z, zeroCut, conicParameter]
    change k < min c _ ↔ _
    omega
  have hcols : (∑ k ∈ range c, columns k) = (c : ℤ)*1324801 - affineQuarters 2301 (-1) c := by
    simp only [columns, sub_eq_add_neg, neg_one_mul, sum_add_distrib, sum_const, card_range,
      nsmul_eq_mul, sum_neg_distrib]
    rw [← sum_affineQuarters 2301 (-1) c (by decide)]
    simp
  have hconic : (∑ k ∈ range c, (max 0 (conicParameter r k))^2) =
      affineSquares (2*(z : ℤ)+1151-r) 2 (c-z) := by
    rw [sum_split_at hCZ]
    have hzero : (∑ k ∈ range z, (max 0 (conicParameter r k))^2) = 0 := by
      apply sum_eq_zero
      intro k hk
      have h := mem_range.mp hk
      simp [max_eq_left ((hz k (by omega)).mp h)]
    rw [hzero, zero_add, ← sum_affineSquares]
    apply sum_congr rfl
    intro k hk
    have h := mem_range.mp hk
    rw [max_eq_right (show 0 ≤ conicParameter r (z+k) by
      have hh := hz (z+k) (by omega)
      omega)]
    simp only [conicParameter, Nat.cast_add]
    ring
  have hfirst : (∑ k ∈ range c, rankTerm r k) =
      (c : ℤ)*1324801 - affineQuarters 2301 (-1) c - affineSquares (2*(z : ℤ)+1151-r) 2 (c-z) := by
    rw [← hcols, ← hconic, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    simp only [rankTerm, ite_eq_left ((hc k).mp (mem_range.mp hk))]
  have hline : (∑ k ∈ range (r-c), quarter (max 0 (linearExp r (c+k)))) =
      affineQuarters ((r : ℤ)-1-3*c) (-3) (a-c) := by
    rw [sum_split_at (m := a-c) (by omega)]
    have hzero : (∑ k ∈ range (r-c-(a-c)),
        quarter (max 0 (linearExp r (c+(a-c+k))))) = 0 := by
      apply sum_eq_zero
      intro k _
      have hh := ha (c+(a-c+k))
      simp [max_eq_left (show linearExp r (c+(a-c+k)) ≤ 0 by omega), quarter]
    rw [hzero, add_zero, ← sum_affineQuarters ((r : ℤ)-1-3*c) (-3) (a-c) (by decide)]
    apply sum_congr rfl
    intro k hk
    have h := mem_range.mp hk
    rw [max_eq_right (((ha (c+k)).mp (by omega)).le)]
    simp only [linearExp, Nat.cast_add]
    ring
  have hbase : (∑ k ∈ range (r-c), quarter ((r : ℤ)-(↑(c+k) : ℤ)+1)) =
      affineQuarters ((r : ℤ)+1-c) (-1) (r-c) := by
    rw [← sum_affineQuarters ((r : ℤ)+1-c) (-1) (r-c) (by decide)]
    apply sum_congr rfl
    intro k _
    simp only [Nat.cast_add]
    ring
  rw [sum_split_at (hCA.trans hAr), hfirst]
  change _ = (c : ℤ)*1324801 - affineQuarters 2301 (-1) c -
    affineSquares (2*(z : ℤ)+1151-r) 2 (c-z) + _
  congr 1
  rw [← hbase, ← hline, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  simp only [rankTerm, ite_eq_right (show ¬ 0 < conicExp r (c+k) by
    have hh := hc (c+k)
    omega)]
private theorem grade_le {q : ℕ} (hq : 5000 ≤ q) :
    (gradeBound (fun q => powers (7300-q)) q : ℤ) ≤ gradeValue (7300-q) := by
  have hsum : gradeBound (fun q => powers (7300-q)) q =
      ∑ k ∈ range (7300-q), blockBound q (offset k) (powers (7300-q) k) := by
    symm
    apply sum_subset (range_mono (Nat.sub_le _ _))
    intro k _ hk
    have h : planeOrder q (offset k) ≤ 0 := by
      unfold planeOrder offset
      simp only [mem_range] at hk
      omega
    simp [blockBound, h]
  rw [hsum, Nat.cast_sum, ← sum_rankTerm _ (by omega)]
  exact sum_le_sum fun _ hk => block_le hq (mem_range.mp hk)
private def total : ℕ → ℤ
  | 0 => 0
  | j+1 => total j + gradeValue (2300-j)
private theorem sum_prefix (n : ℕ) :
    (∑ j ∈ range n, gradeValue (2300-j)) = total n := by
  induction n with
  | zero => simp [total]
  | succ n ih => rw [sum_range_succ, ih, total]
private def gradeWindow (s : ℕ) : ℕ → ℤ
  | 0 => 0
  | n+1 => gradeWindow s n + gradeValue (2300-(s+n))
private theorem total_add_window (s n : ℕ) :
    total (s+n) = total s + gradeWindow s n := by
  induction n with
  | zero => simp [gradeWindow]
  | succ n ih => rw [Nat.add_succ, total, gradeWindow, ih, add_assoc]
private theorem total_window_value (s n : ℕ) (a b : ℤ)
    (hs : total s = a) (hn : gradeWindow s n = b) : total (s+n) = a+b := by
  rw [total_add_window, hs, hn]
private theorem total_to_32 : total 32 = 18649302073 :=
  total_window_value 0 32 0 18649302073 rfl (by decide +kernel)
private theorem total_to_64 : total 64 = 36632681586 :=
  total_window_value 32 32 18649302073 17983379513 total_to_32 (by decide +kernel)
private theorem total_to_96 : total 96 = 53962710528 :=
  total_window_value 64 32 36632681586 17330028942 total_to_64 (by decide +kernel)
private theorem total_to_128 : total 128 = 70651960889 :=
  total_window_value 96 32 53962710528 16689250361 total_to_96 (by decide +kernel)
private theorem total_to_160 : total 160 = 86713004658 :=
  total_window_value 128 32 70651960889 16061043769 total_to_128 (by decide +kernel)
private theorem total_to_192 : total 192 = 102158413824 :=
  total_window_value 160 32 86713004658 15445409166 total_to_160 (by decide +kernel)
private theorem total_to_224 : total 224 = 117000760377 :=
  total_window_value 192 32 102158413824 14842346553 total_to_192 (by decide +kernel)
private theorem total_to_256 : total 256 = 131252616306 :=
  total_window_value 224 32 117000760377 14251855929 total_to_224 (by decide +kernel)
private theorem total_to_288 : total 288 = 144926553600 :=
  total_window_value 256 32 131252616306 13673937294 total_to_256 (by decide +kernel)
private theorem total_to_320 : total 320 = 158035144249 :=
  total_window_value 288 32 144926553600 13108590649 total_to_288 (by decide +kernel)
private theorem total_to_352 : total 352 = 170590960242 :=
  total_window_value 320 32 158035144249 12555815993 total_to_320 (by decide +kernel)
private theorem total_to_384 : total 384 = 182606573568 :=
  total_window_value 352 32 170590960242 12015613326 total_to_352 (by decide +kernel)
private theorem total_to_416 : total 416 = 194094556217 :=
  total_window_value 384 32 182606573568 11487982649 total_to_384 (by decide +kernel)
private theorem total_to_448 : total 448 = 205067480178 :=
  total_window_value 416 32 194094556217 10972923961 total_to_416 (by decide +kernel)
private theorem total_to_480 : total 480 = 215537917440 :=
  total_window_value 448 32 205067480178 10470437262 total_to_448 (by decide +kernel)
private theorem total_to_512 : total 512 = 225518439993 :=
  total_window_value 480 32 215537917440 9980522553 total_to_480 (by decide +kernel)
private theorem total_to_544 : total 544 = 235021619826 :=
  total_window_value 512 32 225518439993 9503179833 total_to_512 (by decide +kernel)
private theorem total_to_576 : total 576 = 244060028928 :=
  total_window_value 544 32 235021619826 9038409102 total_to_544 (by decide +kernel)
private theorem total_to_608 : total 608 = 252646239289 :=
  total_window_value 576 32 244060028928 8586210361 total_to_576 (by decide +kernel)
private theorem total_to_640 : total 640 = 260792822898 :=
  total_window_value 608 32 252646239289 8146583609 total_to_608 (by decide +kernel)
private theorem total_to_672 : total 672 = 268512351744 :=
  total_window_value 640 32 260792822898 7719528846 total_to_640 (by decide +kernel)
private theorem total_to_704 : total 704 = 275817397817 :=
  total_window_value 672 32 268512351744 7305046073 total_to_672 (by decide +kernel)
private theorem total_to_736 : total 736 = 282720533106 :=
  total_window_value 704 32 275817397817 6903135289 total_to_704 (by decide +kernel)
private theorem total_to_768 : total 768 = 289234329600 :=
  total_window_value 736 32 282720533106 6513796494 total_to_736 (by decide +kernel)
private theorem total_to_800 : total 800 = 295371359289 :=
  total_window_value 768 32 289234329600 6137029689 total_to_768 (by decide +kernel)
private theorem total_to_832 : total 832 = 301144194162 :=
  total_window_value 800 32 295371359289 5772834873 total_to_800 (by decide +kernel)
private theorem total_to_864 : total 864 = 306565406208 :=
  total_window_value 832 32 301144194162 5421212046 total_to_832 (by decide +kernel)
private theorem total_to_896 : total 896 = 311647567417 :=
  total_window_value 864 32 306565406208 5082161209 total_to_864 (by decide +kernel)
private theorem total_to_928 : total 928 = 316403249778 :=
  total_window_value 896 32 311647567417 4755682361 total_to_896 (by decide +kernel)
private theorem total_to_960 : total 960 = 320845025280 :=
  total_window_value 928 32 316403249778 4441775502 total_to_928 (by decide +kernel)
private theorem total_to_992 : total 992 = 324985465913 :=
  total_window_value 960 32 320845025280 4140440633 total_to_960 (by decide +kernel)
private theorem total_to_1024 : total 1024 = 328837143666 :=
  total_window_value 992 32 324985465913 3851677753 total_to_992 (by decide +kernel)
private theorem total_to_1056 : total 1056 = 332412630528 :=
  total_window_value 1024 32 328837143666 3575486862 total_to_1024 (by decide +kernel)
private theorem total_to_1088 : total 1088 = 335724498489 :=
  total_window_value 1056 32 332412630528 3311867961 total_to_1056 (by decide +kernel)
private theorem total_to_1120 : total 1120 = 338785319538 :=
  total_window_value 1088 32 335724498489 3060821049 total_to_1088 (by decide +kernel)
private theorem total_to_1152 : total 1152 = 341607665664 :=
  total_window_value 1120 32 338785319538 2822346126 total_to_1120 (by decide +kernel)
private theorem total_to_1184 : total 1184 = 344204093457 :=
  total_window_value 1152 32 341607665664 2596427793 total_to_1152 (by decide +kernel)
private theorem total_to_1216 : total 1216 = 346586981097 :=
  total_window_value 1184 32 344204093457 2382887640 total_to_1184 (by decide +kernel)
private theorem total_to_1248 : total 1248 = 348768370824 :=
  total_window_value 1216 32 346586981097 2181389727 total_to_1216 (by decide +kernel)
private theorem total_to_1280 : total 1280 = 350759955353 :=
  total_window_value 1248 32 348768370824 1991584529 total_to_1248 (by decide +kernel)
private theorem total_to_1312 : total 1312 = 352573077873 :=
  total_window_value 1280 32 350759955353 1813122520 total_to_1280 (by decide +kernel)
private theorem total_to_1344 : total 1344 = 354218732048 :=
  total_window_value 1312 32 352573077873 1645654175 total_to_1312 (by decide +kernel)
private theorem total_to_1376 : total 1376 = 355707562017 :=
  total_window_value 1344 32 354218732048 1488829969 total_to_1344 (by decide +kernel)
private theorem total_to_1408 : total 1408 = 357049862393 :=
  total_window_value 1376 32 355707562017 1342300376 total_to_1376 (by decide +kernel)
private theorem total_to_1440 : total 1440 = 358255578264 :=
  total_window_value 1408 32 357049862393 1205715871 total_to_1408 (by decide +kernel)
private theorem total_to_1472 : total 1472 = 359334305193 :=
  total_window_value 1440 32 358255578264 1078726929 total_to_1440 (by decide +kernel)
private theorem total_to_1504 : total 1504 = 360295289217 :=
  total_window_value 1472 32 359334305193 960984024 total_to_1472 (by decide +kernel)
private theorem total_to_1536 : total 1536 = 361147426848 :=
  total_window_value 1504 32 360295289217 852137631 total_to_1504 (by decide +kernel)
private theorem total_to_1568 : total 1568 = 361899265073 :=
  total_window_value 1536 32 361147426848 751838225 total_to_1536 (by decide +kernel)
private theorem total_to_1600 : total 1600 = 362559001353 :=
  total_window_value 1568 32 361899265073 659736280 total_to_1568 (by decide +kernel)
private theorem total_to_1632 : total 1632 = 363134483624 :=
  total_window_value 1600 32 362559001353 575482271 total_to_1600 (by decide +kernel)
private theorem total_to_1664 : total 1664 = 363633210297 :=
  total_window_value 1632 32 363134483624 498726673 total_to_1632 (by decide +kernel)
private theorem total_to_1696 : total 1696 = 364062330257 :=
  total_window_value 1664 32 363633210297 429119960 total_to_1664 (by decide +kernel)
private theorem total_to_1728 : total 1728 = 364428642864 :=
  total_window_value 1696 32 364062330257 366312607 total_to_1696 (by decide +kernel)
private theorem total_to_1760 : total 1760 = 364738597953 :=
  total_window_value 1728 32 364428642864 309955089 total_to_1728 (by decide +kernel)
private theorem total_to_1790 : total 1790 = 364983426528 :=
  total_window_value 1760 30 364738597953 244828575 total_to_1760 (by decide +kernel)
private theorem total_value : total 1790 ≤ 364983426528 :=
  total_to_1790.le
theorem proof : K1_13_4_2_2.c6 := by
  refine ⟨fun q => powers (7300-q), Int.ofNat_le.mp ?_⟩
  change _ ≤ (364983426528 : ℤ)
  rw [Nat.cast_sum]
  refine le_trans (sum_le_sum (fun j _ => grade_le (q := 5000+j) (by omega))) ?_
  simpa only [show ∀ j : ℕ, 7300-(5000+j) = 2300-j by intro j; omega,
    sum_prefix] using total_value
end K1_13_4_2_2_6
end
section
namespace K1_13_4_3
noncomputable section
open K1 K1_13 K1_13_4
open scoped Polynomial BigOperators
private def linearJets (H : Geom[X]) (i : Fin 3) : Lower :=
  ∑ j : Fin 3, if j.val ≤ i.val then
    MvPolynomial.C (inclX (Polynomial.hasseDeriv (i.val - j.val) H)) * MvPolynomial.X j
  else 0
private def substitute (g : Fin 3 → Lower) : Lower →+* Lower :=
  MvPolynomial.eval₂Hom MvPolynomial.C g
private theorem inverse_linearJets (H : Geom[X]) (hH : H ≠ 0) :
    ∃ g : Fin 3 → Lower, (∀ i, (g i).IsHomogeneous 1) ∧
      (substitute g).comp (substitute (linearJets H)) = RingHom.id Lower := by
  let a := inclX H
  let b := inclX (Polynomial.hasseDeriv 1 H)
  let c := inclX (Polynomial.hasseDeriv 2 H)
  let u := a⁻¹
  let g₀ : Lower := MvPolynomial.C u * MvPolynomial.X 0
  let g₁ : Lower := MvPolynomial.C u * (MvPolynomial.X 1 - MvPolynomial.C b * g₀)
  let g₂ : Lower := MvPolynomial.C u *
    (MvPolynomial.X 2 - MvPolynomial.C c * g₀ - MvPolynomial.C b * g₁)
  let g : Fin 3 → Lower := ![g₀, g₁, g₂]
  have ha : a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Geom[X] GenericX)).mpr hH
  have hcancel (P : Lower) : MvPolynomial.C a * (MvPolynomial.C u * P) = P := by
    rw [← mul_assoc, ← map_mul, show a * u = 1 from mul_inv_cancel₀ ha, map_one, one_mul]
  refine ⟨g, ?_, ?_⟩
  · have h₀ : g₀.IsHomogeneous 1 := (MvPolynomial.isHomogeneous_X _ _).C_mul _
    have h₁ : g₁.IsHomogeneous 1 :=
      ((MvPolynomial.isHomogeneous_X _ _).sub (h₀.C_mul _)).C_mul _
    have h₂ : g₂.IsHomogeneous 1 :=
      (((MvPolynomial.isHomogeneous_X _ _).sub (h₀.C_mul _)).sub (h₁.C_mul _)).C_mul _
    intro i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  · apply MvPolynomial.ringHom_ext
    · intro r
      simp [substitute]
    · intro i
      simp only [RingHom.comp_apply, RingHom.id_apply, substitute, MvPolynomial.eval₂Hom_X',
        linearJets, map_sum, apply_ite, map_mul, MvPolynomial.eval₂Hom_C, map_zero]
      have h₀ : MvPolynomial.C a * g₀ = MvPolynomial.X 0 := by simp [g₀, hcancel]
      have h₁ : MvPolynomial.C b * g₀ + MvPolynomial.C a * g₁ = MvPolynomial.X 1 := by
        simp only [g₁, hcancel]
        abel
      have h₂ : MvPolynomial.C c * g₀ + MvPolynomial.C b * g₁ + MvPolynomial.C a * g₂ =
          MvPolynomial.X 2 := by
        simp only [g₂, hcancel]
        abel
      fin_cases i
      · simpa [Fin.sum_univ_three, a, g] using h₀
      · simpa [Fin.sum_univ_three, a, b, g] using h₁
      · simpa [Fin.sum_univ_three, a, b, c, g] using h₂
private theorem subst_preserves_order (F : Lower) (g : Fin 3 → Lower) (d : ℕ)
    (hg : ∀ i, (g i).IsHomogeneous 1) (hF : ∀ a ∈ F.support, d ≤ a.degree) :
    ∀ a ∈ (substitute g F).support, d ≤ a.degree := by
  intro a ha
  by_contra! hlt
  apply MvPolynomial.mem_support_iff.mp ha
  conv_lhs => rw [F.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro b hb
  have hh : (substitute g (MvPolynomial.monomial b (F.coeff b))).IsHomogeneous b.degree := by
    have hm : (MvPolynomial.monomial b (F.coeff b)).IsHomogeneous b.degree :=
      MvPolynomial.isHomogeneous_monomial _ rfl
    simpa only [substitute, MvPolynomial.coe_eval₂Hom, one_mul] using
      hm.eval₂ MvPolynomial.C g (fun r => MvPolynomial.isHomogeneous_C _ r) hg
  by_contra hz
  have hab : a.degree = b.degree := (DFunLike.congr_fun Finsupp.degree_eq_weight_one a).trans (hh hz)
  exact (not_le_of_gt hlt) (hab ▸ hF b hb)
private theorem restore_translate (H res T : Geom[X]) (F : Row 3) :
    K1_13_4.translate (trajectory T) (MvPolynomial.map inclX (restoreJets H res F)) =
      substitute (linearJets H)
        (K1_13_4.translate (trajectory (H * T + res)) (MvPolynomial.map inclX F)) := by
  let left := (K1_13_4.translate (trajectory T)).comp ((MvPolynomial.map inclX).comp (restoreJets H res))
  let right := (substitute (linearJets H)).comp
    ((K1_13_4.translate (trajectory (H * T + res))).comp (MvPolynomial.map inclX))
  have h : left = right := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [left, right, substitute, restoreJets, K1_13_4.translate]
    · intro i
      have hsum :
          (∑ j : Fin 3, if j.val ≤ i.val then
            MvPolynomial.C (inclX (Polynomial.hasseDeriv (i.val - j.val) H)) *
              (MvPolynomial.X j + MvPolynomial.C (inclX (jet T j)))
          else 0) = linearJets H i + MvPolynomial.C (inclX
            (∑ j : Fin 3, if j.val ≤ i.val then
              Polynomial.hasseDeriv (i.val - j.val) H * jet T j else 0)) := by
        unfold linearJets
        rw [map_sum, map_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j.val ≤ i.val
        · simp only [hj, ite_true, mul_add, map_mul]
        · simp [hj]
      simp only [left, right, RingHom.comp_apply, substitute, restoreJets,
        K1_13_4.translate, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, map_add,
        map_sum, apply_ite, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, map_zero,
        trajectory]
      rw [hsum, jet_restore, map_add, map_add]
      abel
  exact DFunLike.congr_fun h F
private theorem atSeed_map (z : Geom) (F : PhysicalRow) :
    MvPolynomial.map inclX (atSeed (Polynomial.C z) F) =
      atSeed (inclConst z) (toGeneric F) := by
  have hconst : inclX (Polynomial.C z) = inclConst z :=
    (IsScalarTower.algebraMap_apply Geom Geom[X] GenericX z).symm
  have h : (MvPolynomial.map inclX).comp (atSeed (Polynomial.C z)) =
      (atSeed (inclConst z)).comp (MvPolynomial.map inclX) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [atSeed]
    · intro i
      cases i <;> simp [atSeed, hconst]
  exact DFunLike.congr_fun h F
theorem trueOrder_of_raw (H res T : Geom[X]) (z : Geom) (r d : ℕ)
    (F : PhysicalRow) (Q : Row 3) (hH : H ≠ 0)
    (heq : restoreAt H res z F = MvPolynomial.C (H ^ r) * Q)
    (hq : LowerOrder (MvPolynomial.map inclX Q) (trajectory T) d) :
    LowerOrder (atSeed (inclConst z) (toGeneric F)) (trajectory (H * T + res)) d := by
  let G := K1_13_4.translate (trajectory (H * T + res)) (atSeed (inclConst z) (toGeneric F))
  have hc : substitute (linearJets H) G =
      MvPolynomial.C (inclX (H ^ r)) * K1_13_4.translate (trajectory T) (MvPolynomial.map inclX Q) := by
    dsimp only [G]
    rw [← atSeed_map, ← restore_translate, ← restoreAt, heq]
    simp [K1_13_4.translate]
  have ho : ∀ a ∈ (substitute (linearJets H) G).support, d ≤ a.degree := by
    intro a ha
    apply hq a
    rw [hc, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at ha
    exact MvPolynomial.mem_support_iff.mpr (fun hz => ha (by rw [hz, mul_zero]))
  obtain ⟨g, hg, hcomp⟩ := inverse_linearJets H hH
  have hid : substitute g (substitute (linearJets H) G) = G := DFunLike.congr_fun hcomp G
  have hvan := subst_preserves_order _ g d hg ho
  rwa [hid] at hvan
end
end K1_13_4_3
end
section
namespace K1_13_4_3
noncomputable section
open K1 K1_13 K1_13_4
open scoped Polynomial
def c2 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P) box t F,
    Source w P L box t F → ∀ γ ∈ Γ,
      ∃ Q : Row 3, RawCut t Q ∧
        restoreAt P.H (residueAt L.numerator L.denominator (P.z γ)) (P.z γ) F =
          MvPolynomial.C (P.H ^ (box.b + box.j)) * Q
private theorem coeff_eq_zero_of_lowerOrder {F : Lower} {x : Fin 3 → GenericX}
    {d : ℕ} (h : LowerOrder F x d) (a : Fin 3 →₀ ℕ) (ha : a.degree < d) :
    (K1_13_4.translate x F).coeff a = 0 := by
  by_contra hz
  exact (not_le_of_gt ha) (h a (MvPolynomial.mem_support_iff.mpr hz))
end
end K1_13_4_3
end
section
namespace K1_13_4_3_1
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_3
open scoped Polynomial
variable {R : Type*} [CommSemiring R]
def seedTaylor : SeedRow R →+* (SeedRow R)[X] :=
  (Polynomial.mapRingHom MvPolynomial.constantCoeff).comp
    ((MvPolynomial.optionEquivLeft (SeedRow R) (Fin 3)).toRingHom.comp taylor)
theorem coeff_seedTaylor (F : SeedRow R) (i : ℕ) :
    (seedTaylor F).coeff i = hasse (Finsupp.single none i) F := by
  simp only [seedTaylor, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
    MvPolynomial.constantCoeff_eq, hasse]
  change (((MvPolynomial.optionEquivLeft _ _) (taylor F)).coeff i).coeff 0 = _
  rw [MvPolynomial.optionEquivLeft_coeff_coeff, Finsupp.optionElim_zero]
@[simp] theorem seedTaylor_C (p : R) :
    seedTaylor (MvPolynomial.C p) = Polynomial.C (MvPolynomial.C p) := by
  simp [seedTaylor, taylor, MvPolynomial.optionEquivLeft_C]
@[simp] theorem seedTaylor_none :
    seedTaylor (MvPolynomial.X none : SeedRow R) =
      Polynomial.X + Polynomial.C (MvPolynomial.X none) := by
  simp [seedTaylor, taylor, MvPolynomial.optionEquivLeft_C,
    MvPolynomial.optionEquivLeft_X_none]
@[simp] theorem seedTaylor_some (j : Fin 3) :
    seedTaylor (MvPolynomial.X (some j) : SeedRow R) =
      Polynomial.C (MvPolynomial.X (some j)) := by
  simp [seedTaylor, taylor, MvPolynomial.optionEquivLeft_C,
    MvPolynomial.optionEquivLeft_X_some]
private theorem coeff_scalar (F : PhysicalRow) (i : ℕ) (b : SeedVar →₀ ℕ) :
    ∃ u : Geom, (hasse (Finsupp.single none i) F).coeff b =
      F.coeff (Finsupp.single none i + b) * Polynomial.C u := by
  let a : SeedVar →₀ ℕ := Finsupp.single none i
  let m := a + b
  let c := F.coeff m
  have hz : (hasse a (F - MvPolynomial.monomial m c)).coeff b = 0 :=
    coeff_partial_eq_zero _ _ _ (by simp [c, m])
  have hz' : (hasse a F).coeff b - (hasse a (MvPolynomial.monomial m c)).coeff b = 0 := by
    simpa only [hasse, map_sub, MvPolynomial.coeff_sub] using hz
  let G : SeedRow Geom := MvPolynomial.monomial m 1
  refine ⟨(hasse a G).coeff b, (sub_eq_zero.mp hz').trans ?_⟩
  have hG : (MvPolynomial.monomial m c : PhysicalRow) =
      MvPolynomial.C c * MvPolynomial.map Polynomial.C G := by
    simp [G, MvPolynomial.C_mul_monomial]
  rw [hG]
  have hmul : hasse a (MvPolynomial.C c * MvPolynomial.map Polynomial.C G) =
      MvPolynomial.C c * hasse a (MvPolynomial.map Polynomial.C G) := by
    simp [hasse, taylor, MvPolynomial.coeff_C_mul]
  rw [hmul, MvPolynomial.coeff_C_mul, ← map_partial, MvPolynomial.coeff_map]
private theorem support_seed {H : Geom[X]} {i : ℕ} {F : PhysicalRow} {b : SeedVar →₀ ℕ}
    (hb : b ∈ (clearedSeed H i F).support) : Finsupp.single none i + b ∈ F.support := by
  obtain ⟨u, hu⟩ := coeff_scalar F i b
  rw [MvPolynomial.mem_support_iff] at hb ⊢
  intro hz
  apply hb
  simp only [clearedSeed, ← partial_eq_mixedHasse, MvPolynomial.coeff_C_mul, hu, hz,
    zero_mul, mul_zero]
private theorem weight_shift (w : SeedVar → ℕ) (hw : w none = 0)
    (i : ℕ) (b : SeedVar →₀ ℕ) :
    Finsupp.weight w (Finsupp.single none i + b) = Finsupp.weight w b := by
  rw [map_add, Finsupp.weight_single, hw, smul_zero, zero_add]
theorem caps_seed (H : Geom[X]) (i : ℕ) (F : PhysicalRow) (box : Shape)
    (hF : Caps box F) : Caps box (clearedSeed H i F) := by
  obtain ⟨hB, hJ, hC, hU⟩ := hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold jetTotal MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro b hb
    rw [← weight_shift _ rfl i b]
    exact (MvPolynomial.le_weightedTotalDegree _ (support_seed hb)).trans hB
  · unfold jetIndex MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro b hb
    rw [← weight_shift _ rfl i b]
    exact (MvPolynomial.le_weightedTotalDegree _ (support_seed hb)).trans hJ
  · rw [MvPolynomial.degreeOf_le_iff]
    intro b hb
    have h := (MvPolynomial.monomial_le_degreeOf (some 2) (support_seed hb)).trans hC
    simpa using h
  · rw [seedDegree, MvPolynomial.degreeOf_le_iff]
    intro b hb
    exact (Nat.le_add_left ..).trans
      ((MvPolynomial.monomial_le_degreeOf none (support_seed hb)).trans hU)
private def back (x v : Geom) : PhysicalRow →+* PhysicalRow :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j =>
    if j = some 0 then
      MvPolynomial.X (some 0) + MvPolynomial.C (Polynomial.C v) -
        MvPolynomial.C (Polynomial.C x - Polynomial.X) * MvPolynomial.X (some 1) -
        MvPolynomial.C ((Polynomial.C x - Polynomial.X) ^ 2) * MvPolynomial.X (some 2)
    else MvPolynomial.X j)
private theorem back_C (x v : Geom) (p : Geom[X]) :
    back x v (MvPolynomial.C p) = MvPolynomial.C p := by
  simp [back]
private theorem back_seedTaylor (x v : Geom) :
    (Polynomial.mapRingHom (back x v)).comp seedTaylor = seedTaylor.comp (back x v) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [back]
  · intro j
    cases j with
    | none => simp [back]
    | some j =>
      by_cases h : j = 0
      · subst j
        simp [back]
      · simp [back, h]
private theorem back_divisibility (H : Geom[X]) (i m : ℕ) (x v : Geom) (F : PhysicalRow)
    (hF : ∀ b : SeedVar →₀ ℕ, (Polynomial.X - Polynomial.C x) ^ (m - 3 * b (some 0)) ∣
      (back x v F).coeff b) (b : SeedVar →₀ ℕ) :
    (Polynomial.X - Polynomial.C x) ^ (m - 3 * b (some 0)) ∣
      (back x v (clearedSeed H i F)).coeff b := by
  have hcomm :
      back x v (hasse (Finsupp.single none i) F) =
        hasse (Finsupp.single none i) (back x v F) := by
    have h := congrArg (fun p : PhysicalRow[X] => p.coeff i)
      (DFunLike.congr_fun (back_seedTaylor x v) F)
    simpa only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      coeff_seedTaylor] using h
  rw [clearedSeed, ← partial_eq_mixedHasse, map_mul, back_C, hcomm, MvPolynomial.coeff_C_mul]
  obtain ⟨u, hu⟩ := coeff_scalar (back x v F) i b
  rw [hu]
  have hd := hF (Finsupp.single none i + b)
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by decide), zero_add] at hd
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd _) _
theorem contact_seed (H : Geom[X]) (i : ℕ) (w : I → K) (F : PhysicalRow)
    (hF : PhysicalContact w F) : PhysicalContact w (clearedSeed H i F) :=
  fun j b => back_divisibility H i 5000 _ _ F (hF j) b
end
end K1_13_4_3_1
end
section
namespace K1_13_4_2_3
noncomputable section
open K1_13 K1_13_4 K1_13_4_2
open scoped Polynomial BigOperators
def centered (z₀ : GenericSeed) : PhysicalRow →+* RawRow :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Polynomial.mapRingHom (algebraMap Geom GenericSeed)))
    (fun i : SeedVar => i.elim
      (MvPolynomial.C (Polynomial.C (algebraMap Geom[X] GenericSeed Polynomial.X)))
      (fun j => if j = 0 then MvPolynomial.X j + MvPolynomial.C (Polynomial.C z₀)
        else MvPolynomial.X j))
def canonicalJet {R : Type*} [CommRing R] (t : R) (i : Fin 3) : MvPolynomial (Fin 3) R :=
  ![MvPolynomial.C t * MvPolynomial.X 0,
    MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1,
    MvPolynomial.X 1 + MvPolynomial.C t * MvPolynomial.X 2] i
def canonical {R : Type*} [CommRing R] (t : R) :
    MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 3) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (canonicalJet t)
def admissible (a : Shape) (e : Fin 3 →₀ ℕ) : Prop :=
  e 0 + e 1 + e 2 ≤ a.b ∧ e 1 + 2 * e 2 ≤ a.j ∧ e 2 ≤ a.t
abbrev Slot (a : Shape) (q : ℕ) :=
  Σ e₂ : Fin (min q (min a.t (a.j / 2)) + 1),
    Fin (min (q - e₂.val) (a.j - 2 * e₂.val) + 1)
def exponent (a : Shape) (q : ℕ) (e : Slot a q) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![q - e.1.val - e.2.val, e.2.val, e.1.val]
abbrev JetCoeff (a : Shape) (q : ℕ) := Fin (a.b + a.j) × Slot a q
def localCoeff (a : Shape) (α : Geom) (q : ℕ) (c : JetCoeff a q) (G : RawRow) :
    GenericSeed :=
  ((G.coeff (exponent a q c.2)).taylor (algebraMap Geom GenericSeed α)).coeff c.1.val
abbrev Test (a : Shape) (q : ℕ) := Fin ((a.b + a.j - q) * gradeCount a q)
abbrev SeedCoeff (a : Shape) (q : ℕ) := Fin (70001 + (a.b - q))
def dot (a : Shape) (α : Geom) (q : ℕ) (w : JetCoeff a q → Geom) (G : RawRow) :
    GenericSeed :=
  ∑ c, algebraMap Geom GenericSeed (w c) * localCoeff a α q c G
end
end K1_13_4_2_3
end
section
namespace K1_13_4_2_3
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open K1 (K)
open K1_13 K1_13_4 K1_13_4_2
open scoped Polynomial BigOperators
private abbrev Jets (R : Type*) [CommRing R] := MvPolynomial (Fin 3) R
private def affineJet {R : Type*} [CommRing R] (u v : Fin 3 → R) (i : Fin 3) : Jets R :=
  ![MvPolynomial.C (v 0) + MvPolynomial.C (u 0) * MvPolynomial.X 0,
    MvPolynomial.C (v 1) + MvPolynomial.C (u 1) * MvPolynomial.X 0 +
      MvPolynomial.C (u 0) * MvPolynomial.X 1,
    MvPolynomial.C (v 2) + MvPolynomial.C (u 2) * MvPolynomial.X 0 +
      MvPolynomial.C (u 1) * MvPolynomial.X 1 + MvPolynomial.C (u 0) * MvPolynomial.X 2] i
private def affine {R : Type*} [CommRing R] (u v : Fin 3 → R) : Jets R →+* Jets R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (affineJet u v)
private theorem recover_jet {R : Type*} [CommRing R] {u r : R} (hr : r * u = 1)
    (x p : Jets R) :
    p + MvPolynomial.C u * (MvPolynomial.C r * (x - p)) = x := by
  rw [← mul_assoc (MvPolynomial.C u) (MvPolynomial.C r), ← map_mul, mul_comm u r,
    hr, map_one, one_mul]
  ring
private theorem affine_injective {R : Type*} [CommRing R] (u v : Fin 3 → R)
    (hu : IsUnit (u 0)) : Function.Injective (affine u v) := by
  obtain ⟨r, hr⟩ := isUnit_iff_exists_inv'.mp hu
  let k₀ : Jets R := MvPolynomial.C (v 0)
  let x₀ := MvPolynomial.C r * (MvPolynomial.X (0 : Fin 3) - k₀)
  let k₁ := MvPolynomial.C (v 1) + MvPolynomial.C (u 1) * x₀
  let x₁ := MvPolynomial.C r * (MvPolynomial.X (1 : Fin 3) - k₁)
  let k₂ := MvPolynomial.C (v 2) + MvPolynomial.C (u 2) * x₀ + MvPolynomial.C (u 1) * x₁
  let x₂ := MvPolynomial.C r * (MvPolynomial.X (2 : Fin 3) - k₂)
  let ψ : Jets R →+* Jets R := MvPolynomial.eval₂Hom MvPolynomial.C ![x₀, x₁, x₂]
  have h : ψ.comp (affine u v) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ψ, affine]
    · intro i
      fin_cases i
      · simpa [ψ, affine, affineJet] using recover_jet hr (MvPolynomial.X 0) k₀
      · simpa [ψ, affine, affineJet] using recover_jet hr (MvPolynomial.X 1) k₁
      · simpa [ψ, affine, affineJet] using recover_jet hr (MvPolynomial.X 2) k₂
  have hleft : Function.LeftInverse ψ (affine u v) := fun p => DFunLike.congr_fun h p
  exact hleft.injective
private theorem map_affine {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (u v : Fin 3 → R) :
    (MvPolynomial.map f).comp (affine u v) =
      (affine (f ∘ u) (f ∘ v)).comp (MvPolynomial.map f) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [affine]
  · intro i
    fin_cases i <;> simp [affine, affineJet]
private theorem affine_dvd_iff {R : Type*} [CommRing R] (t : R) (n : ℕ)
    (u v : Fin 3 → R) (hu : IsCoprime t (u 0)) (G : Jets R) :
    MvPolynomial.C t ^ n ∣ affine u v G ↔ MvPolynomial.C t ^ n ∣ G := by
  let I : Ideal R := Ideal.span {t ^ n}
  let f := Ideal.Quotient.mk I
  have hf (x : R) : f x = 0 ↔ t ^ n ∣ x :=
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hu' : IsUnit (f (u 0)) := by
    obtain ⟨c, d, h⟩ := hu.pow_left (m := n)
    refine isUnit_iff_exists_inv'.mpr ⟨f d, ?_⟩
    have hm := congrArg f h
    simpa only [map_add, map_mul, map_one, (hf (t ^ n)).mpr dvd_rfl, mul_zero, zero_add] using hm
  have hmap := DFunLike.congr_fun (map_affine f u v) G
  simp only [RingHom.comp_apply] at hmap
  simp only [← map_pow, MvPolynomial.C_dvd_iff_map_hom_eq_zero f _ hf, hmap]
  exact (injective_iff_map_eq_zero' _).mp (affine_injective (f ∘ u) (f ∘ v) hu') _
private theorem hasse_two_mul_linear {R : Type*} [CommRing R] (x : R) (u : R[X]) :
    Polynomial.hasseDeriv 2 ((Polynomial.X - Polynomial.C x) * u) =
      Polynomial.hasseDeriv 1 u + (Polynomial.X - Polynomial.C x) * Polynomial.hasseDeriv 2 u := by
  rw [Polynomial.hasseDeriv_mul]
  simp [show 2 = 1 + 1 from rfl, Finset.Nat.antidiagonal_succ,
    Polynomial.hasseDeriv_X, Polynomial.hasseDeriv_C, Polynomial.hasseDeriv_one,
    add_comm]
private def jetCoeffs (u : GenericSeed[X]) (i : Fin 3) : GenericSeed[X] :=
  Polynomial.hasseDeriv i.val u
private theorem restore_eq_canonical {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (α : Geom) (z₀ : GenericSeed) (u v : GenericSeed[X])
    (hH : liftX P.H = localPole α * u)
    (hres : genericResidue L.numerator L.denominator = Polynomial.C z₀ + localPole α * v)
    (F : PhysicalRow) :
    restore P L F =
      affine (jetCoeffs u) (jetCoeffs v) (canonical (localPole α) (centered z₀ F)) := by
  let f : PhysicalRow →+* RawRow :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Polynomial.mapRingHom (algebraMap Geom GenericSeed)))
      (fun i : SeedVar => i.elim
        (MvPolynomial.C (Polynomial.C (algebraMap Geom[X] GenericSeed Polynomial.X)))
        (restoredJet P L))
  let g := (affine (jetCoeffs u) (jetCoeffs v)).comp
    ((canonical (localPole α)).comp (centered z₀))
  have h : f = g := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [f, g, affine, canonical, centered]
    · intro i
      cases i with
      | none => simp [f, g, affine, canonical, centered]
      | some i =>
        fin_cases i <;>
          simp [f, g, affine, affineJet, canonical, canonicalJet, centered, jetCoeffs, restoredJet,
            Fin.sum_univ_three, hH, hres, localPole, Polynomial.hasseDeriv_zero,
            Polynomial.hasseDeriv_C, hasse_two_mul_linear] <;> ring
  exact DFunLike.congr_fun h F
private theorem eval_lift (p : Geom[X]) (α : Geom) :
    (liftX p).eval (algebraMap Geom GenericSeed α) = algebraMap Geom GenericSeed (p.eval α) := by
  exact Polynomial.eval_map_apply (algebraMap Geom GenericSeed) α
private theorem eval_ne_of_coprime {p H : Geom[X]} {α : Geom} (hc : IsCoprime p H)
    (hroot : H.IsRoot α) : p.eval α ≠ 0 := by
  obtain ⟨u, v, hu⟩ := hc
  intro hp
  have h := congrArg (Polynomial.evalRingHom α) hu
  simp [hp, show H.eval α = 0 from hroot] at h
private theorem fractional_center {Γ s} (P : PoleData Γ s) (L : ResidueChart P) (α : Geom)
    (hroot : P.H.IsRoot α) :
    ∃ N D : Geom[X], D ≠ 0 ∧ N.natDegree ≤ 1 ∧ D.natDegree ≤ 1 ∧
      (genericResidue L.numerator L.denominator).eval (algebraMap Geom GenericSeed α) =
        algebraMap Geom[X] GenericSeed N / algebraMap Geom[X] GenericSeed D := by
  let N : Geom[X] := -Polynomial.X * Polynomial.C (P.q.eval α)
  let D : Geom[X] := Polynomial.C (P.c.eval α) *
    (Polynomial.C (P.a₀.eval α) + Polynomial.X * Polynomial.C (P.a₁.eval α))
  have hD : D ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.evalRingHom 0) h
    simp [D, eval_ne_of_coprime P.c_unit hroot, eval_ne_of_coprime P.a₀_unit hroot] at he
  have hNdeg : N.natDegree ≤ 1 := by
    simpa [N, neg_mul] using Polynomial.natDegree_mul_C_le (Polynomial.X : Geom[X]) (P.q.eval α)
  have hDdeg : D.natDegree ≤ 1 := by
    refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_))
    · simp
    · exact (Polynomial.natDegree_mul_C_le _ _).trans (by simp)
  refine ⟨N, D, hD, hNdeg, hDdeg, (eq_div_iff ?_).mpr ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective Geom[X] GenericSeed)).mpr hD
  have h := Polynomial.eval_dvd (x := algebraMap Geom GenericSeed α) L.generic_congruence
  have hz : P.H.eval α = 0 := hroot
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, eval_lift,
    hz, map_zero, zero_dvd_iff] at h
  have hC (a : Geom) : algebraMap Geom[X] GenericSeed (Polynomial.C a) =
      algebraMap Geom GenericSeed a := by
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simp only [N, D, map_mul, map_add, map_neg, hC]
  linear_combination h
theorem normalization {Γ s} (P : PoleData Γ s) (L : ResidueChart P) (α : Geom)
    (hroot : P.H.IsRoot α) (hsimple : P.H.derivative.eval α ≠ 0) :
    ∃ N D : Geom[X], D ≠ 0 ∧ N.natDegree ≤ 1 ∧ D.natDegree ≤ 1 ∧
      ∀ (a : Shape) (F : PhysicalRow),
        F ∈ poleCondition P L a (localPole α) ↔
          (MvPolynomial.C (localPole α) : RawRow) ^ (a.b + a.j) ∣
            canonical (localPole α)
              (centered (algebraMap Geom[X] GenericSeed N / algebraMap Geom[X] GenericSeed D) F) := by
  obtain ⟨N, D, hD, hNdeg, hDdeg, hcent⟩ := fractional_center P L α hroot
  refine ⟨N, D, hD, hNdeg, hDdeg, fun a F => ?_⟩
  let u₀ := P.H /ₘ (Polynomial.X - Polynomial.C α)
  have hu₀ : (Polynomial.X - Polynomial.C α) * u₀ = P.H :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hH : liftX P.H = localPole α * liftX u₀ := by
    have h := congrArg (Polynomial.mapRingHom (algebraMap Geom GenericSeed)) hu₀.symm
    simpa [liftX, localPole] using h
  have hcop : IsCoprime (localPole α) (liftX u₀) := by
    have h := Polynomial.isCoprime_of_is_root_of_eval_derivative_ne_zero P.H α hsimple
    simpa [localPole, liftX, u₀] using h.map (Polynomial.mapRingHom (algebraMap Geom GenericSeed))
  let z₀ := algebraMap Geom[X] GenericSeed N / algebraMap Geom[X] GenericSeed D
  have hres : localPole α ∣ genericResidue L.numerator L.denominator - Polynomial.C z₀ :=
    Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot, hcent, z₀])
  obtain ⟨v, hv⟩ := hres
  have hres' : genericResidue L.numerator L.denominator = Polynomial.C z₀ + localPole α * v := by
    linear_combination hv
  rw [mem_poleCondition, restore_eq_canonical P L α z₀ (liftX u₀) v hH hres' F]
  exact affine_dvd_iff (localPole α) (a.b + a.j) (jetCoeffs (liftX u₀)) (jetCoeffs v)
    (by simpa [jetCoeffs, Polynomial.hasseDeriv_zero] using hcop) _
end
end K1_13_4_2_3
end
section
namespace K1_13_4_3_1
noncomputable section
open K1 K1_13 K1_13_4
open scoped Polynomial PowerSeries
abbrev RawCoeff := GenericSeed[X]
abbrev Restored := MvPolynomial (Fin 3) RawCoeff
def seed : GenericSeed := algebraMap Geom[X] GenericSeed Polynomial.X
private def seedExpansion : Geom[X] →+* PowerSeries GenericSeed :=
  Polynomial.eval₂RingHom (PowerSeries.C.comp (algebraMap Geom GenericSeed))
    (PowerSeries.C seed + PowerSeries.X)
private theorem constant_seedExpansion :
    PowerSeries.constantCoeff.comp seedExpansion = algebraMap Geom[X] GenericSeed := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [seedExpansion, IsScalarTower.algebraMap_apply Geom Geom[X] GenericSeed]
  · simp [seedExpansion, seed]
private theorem seedExpansion_units (p : nonZeroDivisors Geom[X]) :
    IsUnit (seedExpansion p.val) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  change IsUnit ((PowerSeries.constantCoeff.comp seedExpansion) p.val)
  rw [constant_seedExpansion]
  exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective Geom[X] GenericSeed)).2
    (nonZeroDivisors.coe_ne_zero p))
private def seedFieldExpansion : GenericSeed →+* PowerSeries GenericSeed :=
  IsLocalization.lift seedExpansion_units
private theorem seedFieldExpansion_apply (p : Geom[X]) :
    seedFieldExpansion (algebraMap Geom[X] GenericSeed p) = seedExpansion p :=
  IsLocalization.lift_eq seedExpansion_units p
private theorem constant_seedFieldExpansion :
    PowerSeries.constantCoeff.comp seedFieldExpansion = RingHom.id GenericSeed := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors Geom[X])
  exact RingHom.ext fun p => by
    simp only [RingHom.comp_apply, seedFieldExpansion_apply, RingHom.id_apply]
    exact RingHom.congr_fun constant_seedExpansion p
def expand : RawCoeff →+* PowerSeries RawCoeff :=
  Polynomial.eval₂RingHom ((PowerSeries.map Polynomial.C).comp seedFieldExpansion)
    (PowerSeries.C Polynomial.X)
theorem constant_expand (p : RawCoeff) :
    PowerSeries.constantCoeff (expand p) = p := by
  have h : PowerSeries.constantCoeff.comp expand = RingHom.id RawCoeff := by
    apply Polynomial.ringHom_ext
    · intro k
      have hk := RingHom.congr_fun constant_seedFieldExpansion k
      change PowerSeries.constantCoeff (expand (Polynomial.C k)) = Polynomial.C k
      simp only [expand, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact congrArg Polynomial.C hk
    · simp [expand]
  exact RingHom.congr_fun h p
theorem expand_liftX (p : Geom[X]) : expand (liftX p) = PowerSeries.C (liftX p) := by
  let f := Polynomial.mapRingHom (algebraMap Geom GenericSeed)
  have h : expand.comp f = PowerSeries.C.comp f := by
    apply Polynomial.ringHom_ext
    · intro r
      have hr : seedFieldExpansion (algebraMap Geom GenericSeed r) =
          PowerSeries.C (algebraMap Geom GenericSeed r) := by
        have hc : algebraMap Geom[X] GenericSeed (Polynomial.C r) =
            algebraMap Geom GenericSeed r :=
          (IsScalarTower.algebraMap_apply Geom Geom[X] GenericSeed r).symm
        simpa [hc, seedExpansion] using seedFieldExpansion_apply (Polynomial.C r)
      simp [f, expand, hr]
    · simp [f, expand]
  exact RingHom.congr_fun h p
theorem expand_seed :
    expand (Polynomial.C seed) = PowerSeries.C (Polynomial.C seed) + PowerSeries.X := by
  simp [expand, seed, seedFieldExpansion_apply, seedExpansion]
@[simp] theorem rescale_const {A : Type*} [CommSemiring A] (a b : A) :
    PowerSeries.rescale a (PowerSeries.C b) = PowerSeries.C b := by
  ext n
  cases n <;> simp
theorem rescale_var {A : Type*} [CommSemiring A] (a : A) :
    PowerSeries.rescale a PowerSeries.X = PowerSeries.C a * PowerSeries.X := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  split_ifs with h <;> simp [h]
theorem expand_scaled_sub (a p : RawCoeff) :
    ∃ d : PowerSeries RawCoeff,
      PowerSeries.rescale a (expand p) = PowerSeries.C p + PowerSeries.C a * d := by
  obtain ⟨d, hd⟩ := (PowerSeries.X_dvd_iff).2
    (show PowerSeries.constantCoeff (expand p - PowerSeries.C p) = 0 by
      simp [constant_expand])
  refine ⟨PowerSeries.X * PowerSeries.rescale a d, ?_⟩
  have h := congrArg (PowerSeries.rescale a) hd
  rw [map_sub, rescale_const, map_mul, rescale_var, mul_assoc] at h
  rw [add_comm, ← sub_eq_iff_eq_add]
  exact h
end
end K1_13_4_3_1
end
section
namespace K1_13_4_2_2_5
open K1_13_4_2_2
open scoped BigOperators
set_option maxHeartbeats 600000
private theorem twice_triangular (w : ℤ) : 2 * triangular w = w * (w + 1) := by
  unfold triangular
  apply Int.mul_ediv_cancel_of_dvd
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with h | h
  · have hw : w = 2 * (w / 2) := by omega
    exact dvd_mul_of_dvd_left (by rw [hw]; exact dvd_mul_right _ _) _
  · have hw : w + 1 = 2 * (w / 2 + 1) := by omega
    exact dvd_mul_of_dvd_right (show (2 : ℤ) ∣ w + 1 from ⟨w / 2 + 1, hw⟩) w
private theorem cost_quarter (w : ℤ) : cost w = (w + 1) ^ 2 / 4 := by
  have h : 4 * cost w = (w + 1) ^ 2 - (w + 1) % 2 := by
    unfold cost
    rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with h | h
    · have hw : w = 2 * (w / 2) := by omega
      have hu : (w + 1) / 2 = w / 2 := by omega
      have hp : (w + 1) % 2 = 1 := by omega
      rw [hu, hp]
      conv_rhs => rw [hw]
      ring
    · have hw : w = 2 * (w / 2) + 1 := by omega
      have hu : (w + 1) / 2 = w / 2 + 1 := by omega
      have hp : (w + 1) % 2 = 0 := by omega
      rw [hu, hp]
      conv_rhs => rw [hw]
      ring
  omega
private theorem colength_cost {a w : ℤ} (ha : a ≤ (w + 1) / 2) (hw : 0 ≤ w) :
    colength ⟨a, w⟩ = cost w := by
  have hu : 0 ≤ (w + 1) / 2 := by omega
  have hv : (w + 1) / 2 ≤ w := by omega
  unfold colength cost
  simp only [max_eq_right ha, max_eq_right hu, max_eq_right hv]
  have h₁ := twice_triangular ((w + 1) / 2)
  have h₂ := twice_triangular (w - (w + 1) / 2)
  have he : w - (w + 1) / 2 = w / 2 := by omega
  rw [he] at h₂ ⊢
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with h | h
  · have h' : (w + 1) / 2 = w / 2 := by omega
    rw [h'] at h₁ ⊢
    nlinarith only [h₁, h₂]
  · have h' : (w + 1) / 2 = w / 2 + 1 := by omega
    rw [h'] at h₁ ⊢
    nlinarith only [h₁, h₂]
private theorem even_degree (s : ℤ) :
    triangular (2 * s + 1) - cost (2 * s) = (s + 1) ^ 2 := by
  have h := twice_triangular (2 * s + 1)
  unfold cost
  rw [show (2 * s + 1) / 2 = s by omega, show 2 * s / 2 = s by omega]
  nlinarith only [h]
private theorem columns_eq (q k : ℕ) (hq : 2300 ≤ q) :
    columnCount q (offset k) = columns k := by
  have hd : residualDegree q = 2300 := min_eq_right hq
  have harg : min (2300 : ℤ) (-offset k - 1) = 2300 - k - 1 := by
    unfold offset
    rw [min_eq_right (by omega)]
    ring
  have hval : cumulative 2300 2300 = 1324801 := by decide
  unfold columnCount columns
  rw [hd, harg]
  change cumulative 2300 2300 - cumulative 2300 (2300 - (k : ℤ) - 1) = _
  rw [hval]
  by_cases hk : k < 2300
  · have hnon : ¬ (2300 - (k : ℤ) - 1) < 0 := by omega
    have hclip : min (2300 - (k : ℤ) - 1) 4600 = 2300 - (k : ℤ) - 1 :=
      min_eq_left (by omega)
    have hmax : max (0 : ℤ) (2300 - k - 1 - 2300) = 0 := max_eq_left (by omega)
    rw [max_eq_right (show 0 ≤ 2300 - (k : ℤ) by omega), cost_quarter]
    simp only [cumulative, hnon, ite_false, show (2 * 2300 : ℤ) = 4600 by decide,
      hclip, hmax, show triangular 0 = 0 by decide, sub_zero]
    rw [show 2300 - (k : ℤ) - 1 + 2 = 2300 - k + 1 by ring]
  · have hneg : (2300 - (k : ℤ) - 1) < 0 := by omega
    simp [cumulative, hneg, max_eq_left (show 2300 - (k : ℤ) ≤ 0 by omega), cost]
private theorem cost_nonneg {w : ℤ} (hw : 0 ≤ w) : 0 ≤ cost w := by
  exact mul_nonneg (by omega) (by omega)
private theorem columns_nonneg {k : ℤ} (hk : 0 ≤ k) : 0 ≤ columns k := by
  let w := max 0 (2300 - k)
  have h₀ : 0 ≤ w := le_max_left _ _
  have h₁ : w ≤ 2300 := max_le (by omega) (by omega)
  unfold columns cost
  change 0 ≤ 1324801 - ((w + 1) / 2) * (w / 2 + 1)
  have h := mul_le_mul (show (w + 1) / 2 ≤ 1151 by omega)
    (show w / 2 + 1 ≤ 1151 by omega) (show 0 ≤ w / 2 + 1 by omega) (by omega)
  omega
private theorem product_drop {a b a' b' s : ℤ} (hab : a ≤ b) (hb : b ≤ 1151)
    (hb₀ : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1150)
    (hra : a - s ≤ a') (hrb : b - s ≤ b') :
    a * b - a' * b' ≤ 1324801 - (1151 - s) ^ 2 := by
  by_cases hsa : s ≤ a
  · have h := mul_le_mul hra hrb (show 0 ≤ b - s by omega) ha'
    have h' := mul_le_mul_of_nonneg_left (show a + b ≤ 2302 by omega) hs₀
    nlinarith only [h, h']
  · have h := mul_le_mul (show a ≤ s by omega) hb hb₀ hs₀
    have h' := mul_nonneg ha' hb'
    have h'' := mul_nonneg hs₀ (show 0 ≤ 1151 - s by omega)
    nlinarith only [h, h', h'']
private theorem shifted_nonneg {k n m t : ℤ} (hk : 0 ≤ k) (hn : 0 ≤ n) (hm : 0 ≤ m)
    (hs : n + m ≤ 1150) (hP : 0 ≤ 2300 - k - 2 * n - m) (hO : 0 ≤ t - n - 2 * m) :
    0 ≤ columns k + cost (2300 - k - 2 * n - m) + cost (t - n - 2 * m) -
      (1151 - n - m) ^ 2 := by
  let w := 2300 - k
  let v := w - 2 * n - m
  let s := n + m
  have hv : 0 ≤ v := hP
  have hw : 0 ≤ w := by dsimp [w, v] at *; omega
  have hws : w ≤ 2300 := by dsimp [w]; omega
  have hs₀ : 0 ≤ s := by dsimp [s]; omega
  have hs₁ : s ≤ 1150 := hs
  have hO' := cost_nonneg hO
  unfold columns
  rw [max_eq_right hw]
  rw [show 1151 - n - m = 1151 - s by dsimp [s]; ring]
  change 0 ≤ 1324801 - cost w + cost v + cost (t - n - 2 * m) - (1151 - s) ^ 2
  let a := (w + 1) / 2
  let b := w / 2 + 1
  let a' := (v + 1) / 2
  let b' := v / 2 + 1
  change 0 ≤ 1324801 - a * b + a' * b' + cost (t - n - 2 * m) - (1151 - s) ^ 2
  have h := product_drop (show a ≤ b by dsimp [a, b]; omega)
    (show b ≤ 1151 by dsimp [b]; omega) (show 0 ≤ b by dsimp [b]; omega)
    (show 0 ≤ a' by dsimp [a']; omega) (show 0 ≤ b' by dsimp [b']; omega)
    hs₀ hs₁ (show a - s ≤ a' by dsimp [a, a', s, v]; omega)
    (show b - s ≤ b' by dsimp [b, b', s, v]; omega)
  nlinarith only [h, hO']
private def product (n m : ℕ) (i : Fin 6) : ℕ :=
  if i = 0 ∨ i = 3 then n else if i = 5 then m else 0
def powers (q k : ℕ) : Powers :=
  let t := planeOrder q (offset k)
  product (linearPower k t).toNat (conicPower k t).toNat
private theorem product_sum (n m : ℕ) (f : Fin 6 → ℤ) :
    (∑ i, (product n m i : ℤ) * f i) =
      (n : ℤ) * (f 0 + f 3) + (m : ℤ) * f 5 := by
  simp [Fin.sum_univ_succ, product, Fin.succ, mul_add, add_assoc]
private theorem flag_formula {q k : ℕ} (hq : 2300 ≤ q) :
    initialFlag q (offset k) =
      ![⟨0, 2300 - (k : ℤ)⟩, ⟨1150, 2300⟩, ⟨0, planeOrder q (offset k)⟩] := by
  have hd : residualDegree q = 2300 := min_eq_right hq
  have h : -offset k = 2300 - (k : ℤ) := by unfold offset; ring
  unfold initialFlag
  dsimp only
  rw [hd, h]
  norm_num
private theorem bound_by_kernel {q k : ℕ} (t : ℤ) (ht : planeOrder q (offset k) = t)
    (hpos : 0 < t) (p : Powers) (r : ℤ) (hr : 0 ≤ r)
    (h : columnCount q (offset k) -
      max 0 (max (kernelLower (residualDegree q) (initialFlag q (offset k)))
        (kernelLower (remainingDegree q p) (remainingFlag q (offset k) p))) ≤ r) :
    (blockBound q (offset k) p : ℤ) ≤ r := by
  rw [blockBound, ht, ite_eq_right (not_le_of_gt hpos), Int.toNat_eq_max]
  exact max_le h hr
theorem block_columns {q k : ℕ} (hq : 2300 ≤ q) :
    (blockBound q (offset k) (powers q k) : ℤ) ≤ columns k := by
  by_cases h : planeOrder q (offset k) ≤ 0
  · simpa [blockBound, h] using columns_nonneg (Int.natCast_nonneg k)
  refine bound_by_kernel _ rfl (lt_of_not_ge h) _ _ (columns_nonneg (Int.natCast_nonneg k)) ?_
  rw [columns_eq q k hq]
  exact sub_le_self _ (le_max_left _ _)
theorem block_empty {q k : ℕ} (hq : 2300 ≤ q) {t : ℤ}
    (ht : planeOrder q (offset k) = t) (hpos : 0 < t) :
    (blockBound q (offset k) (powers q k) : ℤ) ≤ cost t := by
  have hkP : colength ⟨0, 2300 - (k : ℤ)⟩ = cost (max 0 (2300 - (k : ℤ))) := by
    by_cases hk : 0 ≤ 2300 - (k : ℤ)
    · rw [max_eq_right hk, colength_cost (by omega) hk]
    · have hhalf : (2300 - (k : ℤ) + 1) / 2 ≤ 0 := by omega
      simp [colength, max_eq_left (le_of_not_ge hk), max_eq_left hhalf, triangular, cost]
  have hQ : colength ⟨1150, 2300⟩ = 1323650 := by decide
  have hO : colength ⟨0, t⟩ = cost t := colength_cost (by omega) (by omega)
  have hd : residualDegree q = 2300 := min_eq_right hq
  have hbase : kernelLower (residualDegree q) (initialFlag q (offset k)) = columns k - cost t := by
    rw [hd, flag_formula hq, ht, kernelLower, Fin.sum_univ_three]
    rw [ite_eq_right (show ¬ (↑(2300 : ℕ) : ℤ) < 0 by decide)]
    change triangular 2301 - (colength ⟨0, 2300 - (k : ℤ)⟩ +
      colength ⟨1150, 2300⟩ + colength ⟨0, t⟩) = _
    rw [hkP, hQ, hO]
    unfold columns
    norm_num [triangular]
    ring
  refine bound_by_kernel t ht hpos _ _ (cost_nonneg (le_of_lt hpos)) ?_
  rw [columns_eq q k hq]
  have h : columns k - cost t ≤ max 0 (max (kernelLower (residualDegree q)
      (initialFlag q (offset k))) (kernelLower (remainingDegree q (powers q k))
      (remainingFlag q (offset k) (powers q k)))) := by
    rw [← hbase]
    exact (le_max_left _ _).trans (le_max_right _ _)
  omega
theorem admissible_point {both : Bool} {k l r t : ℤ} (ha : admissible both k l r)
    (hl : l ≤ t) (hr : t ≤ r) : admissible both k t t := by
  cases both <;> simp [admissible, linearAt, linearPower, conicPower] at ha ⊢ <;> omega
theorem block_shifted {q k : ℕ} (hq : 2300 ≤ q) {t : ℤ}
    (ht : planeOrder q (offset k) = t) (hpos : 0 < t) {both : Bool}
    (ha : admissible both k t t) :
    (blockBound q (offset k) (powers q k) : ℤ) ≤ shiftedRank both k t := by
  let n := linearAt both k t
  let m := conicPower k t
  obtain ⟨hlin, hm, hs, hP, hO⟩ := ha
  have hn : 0 ≤ n := by
    cases both
    · exact le_rfl
    · exact hlin
  have hs' : n + m ≤ 1150 := hs
  have hnc : ((linearPower k t).toNat : ℤ) = n := by
    cases both
    · exact Int.toNat_of_nonpos hlin ▸ rfl
    · exact Int.toNat_of_nonneg hlin
  have hmc : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
  have hp : powers q k = product n.toNat m.toNat := by
    unfold powers
    rw [ht, ← hnc, Int.toNat_natCast]
  have hnc' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
  have hd : residualDegree q = 2300 := min_eq_right hq
  have hd' : remainingDegree q (powers q k) = 2 * (1150 - n - m) := by
    rw [hp, remainingDegree, hd, product_sum, hnc', hmc]
    norm_num [factorDegree]
    ring
  have hP' : remainingFlag q (offset k) (powers q k) 0 =
      ⟨-n - m, 2300 - k - 2 * n - m⟩ := by
    simp [hp, remainingFlag, product_sum, hnc', hmc, flag_formula hq, factorFlag]
    constructor <;> first | trivial | ring
  have hQ' : remainingFlag q (offset k) (powers q k) 1 =
      ⟨1150 - n - m, 2 * (1150 - n - m)⟩ := by
    simp [hp, remainingFlag, product_sum, hnc', hmc, flag_formula hq, factorFlag]
    constructor <;> first | trivial | ring
  have hO' : remainingFlag q (offset k) (powers q k) 2 = ⟨-n - m, t - n - 2 * m⟩ := by
    simp [hp, remainingFlag, product_sum, hnc', hmc, flag_formula hq, factorFlag, ht]
    constructor <;> first | trivial | ring
  have hker : kernelLower (remainingDegree q (powers q k)) (remainingFlag q (offset k) (powers q k)) =
      (1151 - n - m) ^ 2 - cost (2300 - k - 2 * n - m) - cost (t - n - 2 * m) := by
    rw [kernelLower, hd', ite_eq_right (show ¬ 2 * (1150 - n - m) < 0 by omega),
      Fin.sum_univ_three, hP', hQ', hO']
    rw [colength_cost (by omega) hP, colength_cost (by omega) (by omega),
      colength_cost (by omega) hO]
    have h := even_degree (1150 - n - m)
    nlinarith only [h]
  refine bound_by_kernel t ht hpos _ _ (shifted_nonneg (Int.natCast_nonneg k) hn hm hs' hP hO) ?_
  have hle : kernelLower (remainingDegree q (powers q k)) (remainingFlag q (offset k) (powers q k)) ≤
      max 0 (max (kernelLower (residualDegree q) (initialFlag q (offset k)))
        (kernelLower (remainingDegree q (powers q k)) (remainingFlag q (offset k) (powers q k)))) :=
    (le_max_right _ _).trans (le_max_right _ _)
  calc
    _ ≤ columnCount q (offset k) -
        kernelLower (remainingDegree q (powers q k)) (remainingFlag q (offset k) (powers q k)) :=
      sub_le_sub_left hle _
    _ = _ := by
      rw [hker, columns_eq q k hq]
      change _ = columns k + cost (2300 - k - 2 * n - m) + cost (t - n - 2 * m) -
        (1151 - n - m) ^ 2
      ring
end K1_13_4_2_2_5
end
section
namespace K1_13_4_4
noncomputable section
open K1 K1_13 K1_13_4
open scoped BigOperators
def layerSpan {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P)
    (t : ℕ) : Submodule GenericX GenericRow :=
  Submodule.span GenericX {R | ∃ F, Source w P L secondBox t F ∧ toGeneric F = R}
structure FactorsFor (moving : Bool) (A : Finset GenericRow) : Prop where
  different : (↑A : Set GenericRow).Pairwise (fun f g => ¬ Associated f g)
  irreducible : ∀ f ∈ A, Irreducible f
  jets : ∀ f ∈ A, 0 < jetTotal f
  seed : ∀ f ∈ A, if moving then 0 < seedDegree f else seedDegree f = 0
def factorProduct (A : Finset GenericRow) : GenericRow := ∏ f ∈ A, f
def topSlots (a : ℕ) : ℕ := 70001 * 5671 * (1151 - a)^2
end
end K1_13_4_4
end
section
namespace K1_13_4_4
noncomputable section
open K1_13 K1_13_4
open scoped Polynomial BigOperators
private def pureEval : GenericRow →+* GenericX[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => i.elim Polynomial.X (fun _ => 0))
private theorem pureEval_section {F : GenericRow} (hF : jetTotal F = 0) :
    pureSeed (pureEval F) = F := by
  let φ := (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (none : SeedVar))).comp pureEval
  change φ F = (RingHom.id _) F
  apply MvPolynomial.hom_congr_vars
  · ext a
    simp [φ, pureEval]
  · intro i hi
    cases i with
    | none => simp [φ, pureEval]
    | some j =>
      have hd := MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi
      apply False.elim
      apply hd
      apply Nat.eq_zero_of_le_zero
      exact (MvPolynomial.degreeOf_le_weightedTotalDegree
        (fun i : SeedVar => i.elim 0 (fun _ => 1)) (some j) (show 0 < 1 by decide) F).trans_eq hF
  · rfl
private theorem asSeedPoly_pureSeed (p : GenericX[X]) :
    asSeedPoly (pureSeed p) = p.map MvPolynomial.C := by
  let e := (MvPolynomial.optionEquivLeft GenericX (Fin 3)).toRingHom
  let l := e.comp (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X none))
  let r := Polynomial.mapRingHom (MvPolynomial.C : GenericX →+* Lower)
  have h : l = r := by
    apply Polynomial.ringHom_ext
    · intro x
      simp [l, r, e, MvPolynomial.optionEquivLeft_C]
    · simp [l, r, e, MvPolynomial.optionEquivLeft_X_none]
  exact DFunLike.congr_fun h p
private theorem pure_degree_le {p : GenericX[X]} {F : GenericRow} (hF : F ≠ 0)
    (hp : pureSeed p ∣ F) : p.natDegree ≤ seedDegree F := by
  let e := MvPolynomial.optionEquivLeft GenericX (Fin 3)
  have hmap : asSeedPoly (pureSeed p) ∣ asSeedPoly F := map_dvd e.toRingHom hp
  have hne : asSeedPoly F ≠ 0 := (map_ne_zero_iff e e.injective).mpr hF
  have h := Polynomial.natDegree_le_of_dvd hmap hne
  rw [asSeedPoly_pureSeed, Polynomial.natDegree_map_eq_of_injective (MvPolynomial.C_injective (Fin 3) GenericX)] at h
  simpa only [asSeedPoly, MvPolynomial.natDegree_optionEquivLeft, seedDegree] using h
private theorem caps_of_dvd {a : Shape} {F Q : GenericRow} (hF : F ≠ 0)
    (hCap : Caps a F) (hQ : Q ∣ F) : Caps a Q := by
  classical
  refine ⟨(MvPolynomial.weightedTotalDegree_le_of_dvd _ hQ hF).trans hCap.1,
    (MvPolynomial.weightedTotalDegree_le_of_dvd _ hQ hF).trans hCap.2.1, ?_, ?_⟩
  · simpa only [MvPolynomial.weightedTotalDegree_piSingle] using
      (MvPolynomial.weightedTotalDegree_le_of_dvd (Pi.single (some 2 : SeedVar) 1) hQ hF).trans
        (by simpa only [MvPolynomial.weightedTotalDegree_piSingle] using hCap.2.2.1)
  · simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
      (MvPolynomial.weightedTotalDegree_le_of_dvd (Pi.single (none : SeedVar) 1) hQ hF).trans
        (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hCap.2.2.2)
end
end K1_13_4_4
end
section
namespace K1_13_4_4
noncomputable section
open K1 K1_13 K1_13_4
open scoped Polynomial BigOperators
def rowMap : PhysicalRow →ₗ[Geom] GenericRow :=
  (MvPolynomial.mapAlgHom (IsScalarTower.toAlgHom Geom Geom[X] GenericX)).toLinearMap
@[simp] theorem rowMap_apply (F : PhysicalRow) : rowMap F = toGeneric F := rfl
theorem toGeneric_injective : Function.Injective toGeneric :=
  MvPolynomial.map_injective _ (IsFractionRing.injective Geom[X] GenericX)
theorem toGeneric_ne_zero {F : PhysicalRow} (hF : F ≠ 0) : toGeneric F ≠ 0 := by
  intro h
  exact hF (toGeneric_injective (h.trans (rowMap.map_zero.symm)))
def capSpace (a : Shape) : Submodule GenericX GenericRow :=
  MvPolynomial.restrictWeightedDegree (fun i : SeedVar => i.elim 0 (fun _ => 1)) a.b ⊓
  MvPolynomial.restrictWeightedDegree (fun i : SeedVar => i.elim 0 Fin.val) a.j ⊓
  MvPolynomial.restrictWeightedDegree (Pi.single (some 2 : SeedVar) 1) a.t ⊓
  MvPolynomial.restrictWeightedDegree (Pi.single (none : SeedVar) 1) 70000
theorem mem_capSpace {a : Shape} {F : GenericRow} :
    F ∈ capSpace a ↔ Caps a F := by
  classical
  simp only [capSpace, Submodule.mem_inf,
    MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    MvPolynomial.weightedTotalDegree_piSingle, Caps, jetTotal, jetIndex, seedDegree]
  tauto
theorem toGeneric_caps {a : Shape} {F : PhysicalRow} (h : Caps a F) :
    Caps a (toGeneric F) := by
  have hs : (toGeneric F).support = F.support :=
    MvPolynomial.support_map_of_injective F (IsFractionRing.injective Geom[X] GenericX)
  simpa only [Caps, jetTotal, jetIndex, seedDegree, MvPolynomial.weightedTotalDegree,
    MvPolynomial.degreeOf_eq_sup, hs] using h
theorem layerSpan_caps {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {t : ℕ} {F : GenericRow} (hF : F ∈ layerSpan w P L t) : Caps secondBox F := by
  apply mem_capSpace.mp
  apply (Submodule.span_le.mpr ?_) hF
  rintro _ ⟨Q, hQ, rfl⟩
  exact mem_capSpace.mpr (toGeneric_caps hQ.1)
theorem mixedHasse_zero (F : PhysicalRow) : mixedHasse 0 F = F := by
  let ev : MvPolynomial SeedVar PhysicalRow →+* PhysicalRow :=
    MvPolynomial.eval₂Hom (RingHom.id _) (fun _ => 0)
  let shift : PhysicalRow →+* MvPolynomial SeedVar PhysicalRow :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
      (fun i => MvPolynomial.X i + MvPolynomial.C (MvPolynomial.X i))
  have hev (Q : MvPolynomial SeedVar PhysicalRow) : ev Q = Q.coeff 0 := by
    simp [ev, MvPolynomial.constantCoeff_eq]
  have hcomp : ev.comp shift = RingHom.id PhysicalRow := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp [ev, shift]
  change (shift F).coeff 0 = F
  rw [← hev]
  exact DFunLike.congr_fun hcomp F
private abbrev IncrementRow := MvPolynomial SeedVar PhysicalRow
private def CoeffBound (v : SeedVar → ℕ) (d : ℕ) (R : IncrementRow) : Prop :=
  ∀ a, R.coeff a ∈ MvPolynomial.restrictWeightedDegree v d
private theorem coeffBound_mul {v : SeedVar → ℕ} {d e : ℕ} {R S : IncrementRow}
    (hR : CoeffBound v d R) (hS : CoeffBound v e S) : CoeffBound v (d + e) (R * S) := by
  classical
  intro a
  rw [MvPolynomial.coeff_mul]
  exact Submodule.sum_mem _ fun b _ => MvPolynomial.mul_mem_restrictWeightedDegree (hR b.1) (hS b.2)
private theorem coeffBound_C {v : SeedVar → ℕ} {d : ℕ} {F : PhysicalRow}
    (hF : F ∈ MvPolynomial.restrictWeightedDegree v d) :
    CoeffBound v d (MvPolynomial.C F) := by
  classical
  intro a
  rw [MvPolynomial.coeff_C]
  split
  · exact hF
  · exact Submodule.zero_mem _
private theorem coeffBound_pow {v : SeedVar → ℕ} {d : ℕ} {R : IncrementRow}
    (hR : CoeffBound v d R) (n : ℕ) : CoeffBound v (n * d) (R ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.zero_mul, ← MvPolynomial.C_1]
    apply coeffBound_C
    rw [← MvPolynomial.C_1]
    exact MvPolynomial.C_mem_restrictWeightedDegree v 0 _
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact coeffBound_mul ih hR
private theorem coeffBound_prod {ι : Type*} {v : SeedVar → ℕ} (s : Finset ι)
    (d : ι → ℕ) (R : ι → IncrementRow) (h : ∀ i ∈ s, CoeffBound v (d i) (R i)) :
    CoeffBound v (∑ i ∈ s, d i) (∏ i ∈ s, R i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty, ← MvPolynomial.C_1]
    exact coeffBound_C (MvPolynomial.C_mem_restrictWeightedDegree v 0 _)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact coeffBound_mul (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
theorem mixedHasse_weightedDegree_le (v : SeedVar → ℕ) (a : SeedVar →₀ ℕ)
    (F : PhysicalRow) :
    (mixedHasse a F).weightedTotalDegree v ≤ F.weightedTotalDegree v := by
  classical
  let g : SeedVar → IncrementRow := fun i => MvPolynomial.X i + MvPolynomial.C (MvPolynomial.X i)
  have hg (i : SeedVar) : CoeffBound v (v i) (g i) := by
    intro b
    change (MvPolynomial.X i : IncrementRow).coeff b +
      (MvPolynomial.C (MvPolynomial.X i) : IncrementRow).coeff b ∈ _
    apply Submodule.add_mem
    · rw [MvPolynomial.coeff_X]
      split
      · rw [← MvPolynomial.C_1]
        exact MvPolynomial.C_mem_restrictWeightedDegree v (v i) _
      · exact Submodule.zero_mem _
    · exact coeffBound_C (MvPolynomial.X_mem_restrictWeightedDegree v (v i) i le_rfl) b
  apply MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  change (MvPolynomial.eval₂ (MvPolynomial.C.comp MvPolynomial.C) g F).coeff a ∈ _
  rw [MvPolynomial.eval₂_eq, MvPolynomial.coeff_sum]
  apply Submodule.sum_mem
  intro m hm
  have hp := coeffBound_prod m.support (fun i => m i * v i) (fun i => g i ^ m i)
    (fun i _ => coeffBound_pow (hg i) (m i))
  have hC : CoeffBound v 0 (MvPolynomial.C (MvPolynomial.C (F.coeff m))) :=
    coeffBound_C (MvPolynomial.C_mem_restrictWeightedDegree v 0 _)
  have hP := coeffBound_mul hC hp a
  apply MvPolynomial.restrictWeightedDegree_mono v _ hP
  rw [Nat.zero_add]
  simpa only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using
    MvPolynomial.le_weightedTotalDegree v hm
theorem mixedHasse_caps (a : SeedVar →₀ ℕ) (F : PhysicalRow) (hF : Caps secondBox F) :
    Caps secondBox (mixedHasse a F) := by
  classical
  obtain ⟨hb, hj, ht, hs⟩ := hF
  refine ⟨(mixedHasse_weightedDegree_le _ a F).trans hb,
    (mixedHasse_weightedDegree_le _ a F).trans hj, ?_, ?_⟩
  · simpa only [MvPolynomial.weightedTotalDegree_piSingle] using
      (mixedHasse_weightedDegree_le (Pi.single (some 2 : SeedVar) 1) a F).trans
        (by simpa only [MvPolynomial.weightedTotalDegree_piSingle] using ht)
  · simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
      (mixedHasse_weightedDegree_le (Pi.single (none : SeedVar) 1) a F).trans
        (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hs)
end
end K1_13_4_4
end
section
namespace K1_13_4_4
noncomputable section
open K1_13_4
open scoped BigOperators
set_option maxHeartbeats 650000
private abbrev Exponent := SeedVar →₀ ℕ
private def slotTuples (a : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.Ico a 1151).biUnion (fun k =>
    (Finset.range (2301 - 2*k)).biUnion (fun j =>
      (Finset.range (6821 - k - j)).biUnion (fun i =>
        (Finset.range 70001).image (fun z => (k, j, i, z)))))
private def slotExponent (q : ℕ × ℕ × ℕ × ℕ) : Exponent :=
  Finsupp.equivFunOnFinite.symm (fun i => i.elim q.2.2.2 (![q.2.2.1, q.2.1, q.1] ·))
private theorem sum_value_choices {k : ℕ} (hk : k ≤ 1150) :
    (∑ j ∈ Finset.range (2301 - 2*k), (6821 - k - j)) = (2301 - 2*k) * 5671 := by
  let n := 2301 - 2*k
  have hpair : (∑ j ∈ Finset.range n, (6821 - k - j)) +
      (∑ j ∈ Finset.range n, (6821 - k - (n - 1 - j))) = n * (5671 + 5671) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ ∈ Finset.range n, (5671 + 5671) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        dsimp [n] at hj' ⊢
        omega
      _ = _ := by simp
  let s := ∑ j ∈ Finset.range n, (6821 - k - j)
  have hs : (∑ j ∈ Finset.range n, (6821 - k - (n - 1 - j))) = s :=
    Finset.sum_range_reflect (fun j => 6821 - k - j) n
  rw [hs, Nat.mul_add] at hpair
  change s + s = n * 5671 + n * 5671 at hpair
  change s = n * 5671
  omega
private theorem sum_odds (n : ℕ) : (∑ k ∈ Finset.range n, (2*k + 1)) = n^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring
private theorem sum_index_choices (a : ℕ) :
    (∑ k ∈ Finset.Ico a 1151, (2301 - 2*k)) = (1151 - a)^2 := by
  rw [Finset.sum_Ico_eq_sum_range]
  let n := 1151 - a
  calc
    _ = ∑ k ∈ Finset.range n, (2 * (n - 1 - k) + 1) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      dsimp [n] at hk' ⊢
      omega
    _ = _ := by
      rw [Finset.sum_range_reflect (fun k => 2*k + 1) n, sum_odds]
private theorem tuples_card (a : ℕ) : (slotTuples a).card ≤ topSlots a := by
  unfold slotTuples
  calc
    _ ≤ ∑ k ∈ Finset.Ico a 1151, ∑ j ∈ Finset.range (2301 - 2*k),
        ∑ _ ∈ Finset.range (6821 - k - j), 70001 := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => ?_)
      exact Finset.card_image_le.trans_eq (Finset.card_range _)
    _ = topSlots a := by
      unfold topSlots
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      calc
        _ = ∑ k ∈ Finset.Ico a 1151, (70001 * 5671) * (2301 - 2*k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' : k ≤ 1150 := by have h := (Finset.mem_Ico.mp hk).2; omega
          rw [← Finset.sum_mul, sum_value_choices hk']
          ring
        _ = _ := by rw [← Finset.mul_sum, sum_index_choices]
private theorem exponent_mem {a : ℕ} {R : GenericRow} (hR : Caps secondBox R)
    {m : Exponent} (hm : m ∈ R.support) (ha : a ≤ m (some 2)) :
    m ∈ (slotTuples a).image slotExponent := by
  classical
  have ht := (MvPolynomial.le_weightedTotalDegree
    (fun i : SeedVar => i.elim 0 (fun _ => 1)) hm).trans hR.1
  have hj := (MvPolynomial.le_weightedTotalDegree
    (fun i : SeedVar => i.elim 0 Fin.val) hm).trans hR.2.1
  have hz := (MvPolynomial.le_degreeOf_of_mem_support (none : SeedVar) hm).trans hR.2.2.2
  have hk := (MvPolynomial.le_degreeOf_of_mem_support (some 2 : SeedVar) hm).trans hR.2.2.1
  have htotal : m (some 0) + m (some 1) + m (some 2) ≤ 6820 := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
      Fin.sum_univ_succ, secondBox, Nat.add_assoc] using ht
  have hindex : m (some 1) + 2 * m (some 2) ≤ 2300 := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
      Fin.sum_univ_succ, secondBox, Nat.mul_comm] using hj
  change m (some 2) ≤ 1150 at hk
  change m none ≤ 70000 at hz
  refine Finset.mem_image.mpr ⟨(m (some 2), m (some 1), m (some 0), m none), ?_, ?_⟩
  · simp only [slotTuples, Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_range,
      Finset.mem_image]
    exact ⟨m (some 2), ⟨ha, by omega⟩, m (some 1), by omega, m (some 0), by omega,
      m none, by omega, rfl⟩
  · ext i
    cases i with
    | none => simp [slotExponent]
    | some i => fin_cases i <;> simp [slotExponent]
private theorem rank_le_coeffs {σ 𝕜 : Type*} [Field 𝕜]
    (A : Finset (σ →₀ ℕ)) {r : ℕ} (e : Fin r → MvPolynomial σ 𝕜)
    (he : LinearIndependent 𝕜 e)
    (h : ∀ R ∈ Submodule.span 𝕜 (Set.range e), R ≠ 0 → ∃ m ∈ A, R.coeff m ≠ 0) :
    r ≤ A.card := by
  classical
  let V := Submodule.span 𝕜 (Set.range e)
  let proj : MvPolynomial σ 𝕜 →ₗ[𝕜] (↥A → 𝕜) :=
    LinearMap.pi fun m => MvPolynomial.lcoeff 𝕜 m.val
  let L := proj.comp V.subtype
  have hker : LinearMap.ker L = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro R hR
    apply Subtype.ext
    change R.val = 0
    by_contra hn
    obtain ⟨m, hm, hcoeff⟩ := h R.val R.property hn
    exact hcoeff (congrFun hR ⟨m, hm⟩)
  have hli : LinearIndependent 𝕜
      (fun i => (⟨e i, Submodule.subset_span (Set.mem_range_self i)⟩ : V)) :=
    LinearIndependent.of_comp V.subtype he
  have hr : Fintype.card (Fin r) ≤ Module.finrank 𝕜 (↥A → 𝕜) :=
    (hli.map' L hker).fintype_card_le_finrank
  simpa only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hr
theorem count_symbols (a r : ℕ) (e : Fin r → GenericRow) (he : LinearIndependent GenericX e)
    (h : ∀ R ∈ Submodule.span GenericX (Set.range e),
      Caps secondBox R ∧ (R ≠ 0 → a ≤ R.degreeOf (some 2))) :
    r ≤ topSlots a := by
  have hc := rank_le_coeffs ((slotTuples a).image slotExponent) e he (by
    intro R hR hn
    obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup R.support
      (MvPolynomial.support_nonempty.mpr hn) (fun u => u (some 2))
    have hdeg := (h R hR).2 hn
    rw [MvPolynomial.degreeOf_eq_sup, hmax] at hdeg
    exact ⟨m, exponent_mem (h R hR).1 hm hdeg, MvPolynomial.mem_support_iff.mp hm⟩)
  exact hc.trans (Finset.card_image_le.trans (tuples_card a))
end
end K1_13_4_4
end
section
namespace K1_13_4_2_2_5
open scoped BigOperators
private theorem total_add (s m n : ℕ) : total s (m + n) = total s m + total (s + m) n := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    change total s (m + n) + offsetTotal (s + (m + n)) =
      total s m + (total (s + m) n + offsetTotal (s + m + n))
    rw [ih, Nat.add_assoc s m n, add_assoc]
private theorem total_windows (s width n : ℕ) :
    total s (n * width) = ∑ i ∈ Finset.range n, total (s + i * width) width := by
  induction n with
  | zero => simp [total]
  | succ n ih => rw [Nat.succ_mul, total_add, Finset.sum_range_succ, ih]
theorem total_value : total 0 5000 = 5196036704622 := by
  rw [show 5000 = 20 * 250 by decide, total_windows 0 250 20]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.zero_add,
    window0, window1, window2, window3, window4, window5, window6, window7, window8, window9,
    window10, window11, window12, window13, window14, window15, window16, window17, window18, window19]
  norm_num
end K1_13_4_2_2_5
end
section
namespace K1_13_4_4
open K1_13_4
open scoped BigOperators
set_option maxRecDepth 1024
private theorem blocks (e : ℕ) (he : 0 < e) (q : ℕ → ℕ) (n : ℕ) :
    (∑ t ∈ Finset.range (n * e), q (t / e)) = e * ∑ k ∈ Finset.range n, q k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, Nat.mul_add]
    congr 1
    calc
      (∑ t ∈ Finset.range e, q ((n * e + t) / e)) =
          ∑ _ ∈ Finset.range e, q n := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht' := Finset.mem_range.mp ht
        rw [Nat.mul_comm n e, Nat.mul_add_div he, Nat.div_eq_of_lt ht', Nat.add_zero]
      _ = _ := by simp
theorem cutoff_sum_le {W e n : ℕ} (he : 0 < e) (r q : ℕ → ℕ)
    (h : ∀ t ≤ W, r t ≤ q ((W - t) / e)) (hz : ∀ k, n ≤ k → q k = 0) :
    (∑ t ∈ Finset.range (W + 1), r t) ≤ e * ∑ k ∈ Finset.range n, q k := by
  calc
    _ ≤ ∑ t ∈ Finset.range (W + 1), q ((W - t) / e) :=
      Finset.sum_le_sum fun t ht => h t (Nat.le_of_lt_succ (Finset.mem_range.mp ht))
    _ = ∑ t ∈ Finset.range (W + 1), q (t / e) := by
      simpa only [Nat.add_sub_cancel] using
        (Finset.sum_range_reflect (fun t => q (t / e)) (W + 1))
    _ ≤ _ := by
      rw [← blocks e he q n]
      by_cases hW : W + 1 ≤ n * e
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hW) (fun _ _ _ => Nat.zero_le _)
      · have hs := Finset.range_mono (show n * e ≤ W + 1 by omega)
        refine (Finset.sum_subset hs ?_).ge
        intro t _ ht
        apply hz
        apply (Nat.le_div_iff_mul_le he).mpr
        exact Nat.le_of_not_gt (fun hlt => ht (Finset.mem_range.mpr hlt))
private theorem sum_squares (n : ℕ) :
    6 * (∑ k ∈ Finset.range n, (n - k)^2) = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    rw [Nat.mul_add, ih]
    ring
theorem slot_constants :
    topSlots 0 = 525913765916471 ∧
      7800 * (∑ k ∈ Finset.range 1150, topSlots (1 + k)) = 1571799066189253395000 := by
  constructor
  · decide
  · have hs : (∑ k ∈ Finset.range 1150, topSlots (1 + k)) =
        (70001 * 5671) * ∑ k ∈ Finset.range 1150, (1150 - k)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hk : 1151 - (1 + k) = 1150 - k := by omega
      rw [topSlots, hk]
    rw [hs]
    have hsquare :
        (∑ k ∈ Finset.range 1150, (1150 - k)^2) = 507619775 := by
      have h := sum_squares 1150
      omega
    rw [hsquare]
end K1_13_4_4
end
section
namespace K1_13_4_2_3
set_option backward.isDefEq.respectTransparency false
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2
open scoped Polynomial BigOperators
def c1 : Prop :=
  ∀ (a : Shape) (α : Geom),
    ∃ w : ∀ q : Fin (a.b + 1), Test a q.val → JetCoeff a q.val → Geom,
      ∀ G : RawRow, (∀ e ∈ G.support, admissible a e) →
        (((MvPolynomial.C (localPole α) : RawRow) ^ (a.b + a.j) ∣
          canonical (localPole α) G) ↔
          ∀ (q : Fin (a.b + 1)) (i : Test a q.val), dot a α q.val (w q i) G = 0)
def c2 : Prop :=
  ∀ (a : Shape) (α : Geom) (N D : Geom[X]), D ≠ 0 →
    N.natDegree ≤ 1 → D.natDegree ≤ 1 →
    let z₀ : GenericSeed := algebraMap Geom[X] GenericSeed N / algebraMap Geom[X] GenericSeed D
    ∃ p : ∀ q : Fin (a.b + 1), PhysicalRow →ₗ[Geom] (JetCoeff a q.val → Geom[X]),
      ∀ F : PhysicalRow, Caps a F →
        (∀ e ∈ (centered z₀ F).support, admissible a e) ∧
        ∀ (q : Fin (a.b + 1)) (c : JetCoeff a q.val),
          (p q F c).natDegree ≤ 70000 + (a.b - q.val) ∧
          algebraMap Geom[X] GenericSeed (p q F c) =
            (algebraMap Geom[X] GenericSeed D) ^ (a.b - q.val) *
              localCoeff a α q.val c (centered z₀ F)
private def clearedTest {a : Shape} {q : ℕ}
    (w : JetCoeff a q → Geom) (p : PhysicalRow →ₗ[Geom] (JetCoeff a q → Geom[X])) :
    PhysicalRow →ₗ[Geom] Geom[X] :=
  ∑ c, w c • ((LinearMap.proj c).comp p)
private theorem clearedTest_apply {a : Shape} {q : ℕ}
    (w : JetCoeff a q → Geom) (p : PhysicalRow →ₗ[Geom] (JetCoeff a q → Geom[X]))
    (F : PhysicalRow) :
    clearedTest w p F = ∑ c, w c • p F c := by
  simp [clearedTest, LinearMap.sum_apply]
private theorem coeff_test_zero_iff {a : Shape} {q : ℕ} {α : Geom}
    {F : PhysicalRow} {G : RawRow} {D : Geom[X]} (hD : D ≠ 0)
    (w : JetCoeff a q → Geom) (p : PhysicalRow →ₗ[Geom] (JetCoeff a q → Geom[X]))
    (hp : ∀ c, (p F c).natDegree ≤ 70000 + (a.b - q) ∧
      algebraMap Geom[X] GenericSeed (p F c) =
        (algebraMap Geom[X] GenericSeed D) ^ (a.b - q) * localCoeff a α q c G) :
    (∀ k : SeedCoeff a q, (clearedTest w p F).coeff k.val = 0) ↔ dot a α q w G = 0 := by
  have hdeg : (clearedTest w p F).natDegree ≤ 70000 + (a.b - q) := by
    rw [clearedTest_apply]
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun c _ =>
      (Polynomial.natDegree_smul_le _ _).trans (hp c).1
  have hz : (∀ k : SeedCoeff a q, (clearedTest w p F).coeff k.val = 0) ↔
      clearedTest w p F = 0 := by
    refine ⟨fun h => Polynomial.ext fun n => ?_, by intro h k; rw [h, Polynomial.coeff_zero]⟩
    rw [Polynomial.coeff_zero]
    by_cases hn : n < 70001 + (a.b - q)
    · exact h ⟨n, hn⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hmap : algebraMap Geom[X] GenericSeed (clearedTest w p F) =
      (algebraMap Geom[X] GenericSeed D) ^ (a.b - q) * dot a α q w G := by
    rw [clearedTest_apply, dot, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Algebra.smul_def, map_mul, (hp c).2, IsScalarTower.algebraMap_apply Geom Geom[X] GenericSeed]
    ring
  rw [hz, ← (map_eq_zero_iff _ (IsFractionRing.injective Geom[X] GenericSeed)), hmap]
  have hne : algebraMap Geom[X] GenericSeed D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Geom[X] GenericSeed)).2 hD
  simp [pow_ne_zero _ hne]
private theorem codim_le_test_finrank {E : Type*} [AddCommGroup E] [Module Geom E]
    [Module.Finite Geom E] (V W : Submodule Geom PhysicalRow) [Module.Finite Geom V]
    (f : V →ₗ[Geom] E) (hker : LinearMap.ker f = W.comap V.subtype) :
    codimIn V W ≤ Module.finrank Geom E := by
  have h := LinearMap.finrank_range_add_finrank_ker (K := Geom) (V := ↥V) (V₂ := E) f
  have he := (V.equivSubtypeMap (W.comap V.subtype)).finrank_eq
  rw [Submodule.map_comap_subtype] at he
  rw [hker, he] at h
  have hle := Submodule.finrank_le (LinearMap.range f)
  unfold codimIn
  omega
theorem of_children (h1 : c1) (h2 : c2) : K1_13_4_2.c3 := by
  classical
  intro Γ s P L a α V hV hcap hroot hsimple
  obtain ⟨N, D, hD, hNdeg, hDdeg, hnorm⟩ := normalization P L α hroot hsimple
  obtain ⟨w, hw⟩ := h1 a α
  obtain ⟨p, hp⟩ := h2 a α N D hD hNdeg hDdeg
  let E := ∀ q : Fin (a.b + 1), (Test a q.val × SeedCoeff a q.val) → Geom
  let f : V →ₗ[Geom] E :=
    LinearMap.pi fun q => LinearMap.pi fun ij =>
      (Polynomial.lcoeff Geom ij.2.val).comp ((clearedTest (w q ij.1) (p q)).comp V.subtype)
  have hker : LinearMap.ker f = (poleCondition P L a (localPole α)).comap V.subtype := by
    ext F
    have h := hp F.val (hcap F.val F.property)
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    simp only [Submodule.subtype_apply, hnorm, hw _ h.1]
    constructor
    · intro hf q i
      apply (coeff_test_zero_iff hD (w q i) (p q) (h.2 q)).mp
      intro k
      exact congrFun (congrFun hf q) (i, k)
    · intro hf
      funext q ij
      exact (coeff_test_zero_iff hD (w q ij.1) (p q) (h.2 q)).mpr (hf q ij.1) ij.2
  have hdim : Module.finrank Geom E = poleDebit a := by
    unfold E poleDebit
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin]
    exact Fin.sum_univ_eq_sum_range
      (fun q => (a.b + a.j - q) * gradeCount a q * (70001 + (a.b - q))) (a.b + 1)
  exact (codim_le_test_finrank _ _ f hker).trans hdim.le
end
end K1_13_4_2_3
end
section
namespace K1_13_4_4
noncomputable section
open K1 K1_13 K1_13_4
open scoped BigOperators
set_option maxRecDepth 1024
private def multiples (D : GenericRow) : Submodule GenericX GenericRow :=
  (Ideal.span {D}).restrictScalars GenericX
private theorem mem_multiples {F D : GenericRow} : F ∈ multiples D ↔ D ∣ F :=
  Ideal.mem_span_singleton
private theorem count_layer {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {a r t : ℕ}
    (hb : ∃ e : Fin r → GenericRow, LinearIndependent GenericX e ∧
      ∀ i, e i ∈ layerSpan w P L t)
    (hdeg : ∀ R ∈ layerSpan w P L t, R ≠ 0 → a ≤ R.degreeOf (some 2)) :
    r ≤ topSlots a := by
  obtain ⟨e, he, hs⟩ := hb
  have hspan : Submodule.span GenericX (Set.range e) ≤ layerSpan w P L t :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hs i)
  exact count_symbols a r e he (fun R hR => ⟨layerSpan_caps (hspan hR), hdeg R (hspan hR)⟩)
private theorem weighted_pow (v : SeedVar → ℕ) (D : GenericRow) (hD : D ≠ 0) (n : ℕ) :
    (D ^ n).weightedTotalDegree v = n * D.weightedTotalDegree v := by
  induction n with
  | zero =>
    rw [pow_zero, zero_mul, ← MvPolynomial.C_1, MvPolynomial.weightedTotalDegree_C]
  | succ n ih =>
    rw [pow_succ, MvPolynomial.weightedTotalDegree_mul v _ _ (pow_ne_zero _ hD) hD,
      ih, Nat.succ_mul]
end
end K1_13_4_4
end
section
namespace K1_13_4_2_2_4
open K1_13_4_2_2 Finset
open scoped BigOperators
theorem double_triangular (w : ℤ) : 2 * triangular w = w * (w + 1) := by
  unfold triangular
  apply Int.mul_ediv_cancel_of_dvd
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with h | h
  · have hw : w = 2 * (w / 2) := by omega
    exact dvd_mul_of_dvd_left (by rw [hw]; exact dvd_mul_right _ _) _
  · have hw : w + 1 = 2 * (w / 2 + 1) := by omega
    exact dvd_mul_of_dvd_right (by rw [hw]; exact dvd_mul_right _ _) _
theorem triangular_mono {u v : ℤ} (hu : 0 ≤ u) (huv : u ≤ v) :
    triangular u ≤ triangular v := by
  have h := mul_nonneg (show 0 ≤ v - u by omega) (show 0 ≤ v + u + 1 by omega)
  nlinarith only [K1_13_4_2_2_4.double_triangular u, K1_13_4_2_2_4.double_triangular v, h]
def weightCost (w : ℤ) : ℤ :=
  let m := w / 2
  m * (m + 1) + w % 2 * (m + 1)
theorem weightCost_nonneg {w : ℤ} (hw : 0 ≤ w) : 0 ≤ K1_13_4_2_2_4.weightCost w :=
  add_nonneg (mul_nonneg (by omega) (by omega)) (mul_nonneg (by omega) (by omega))
theorem weightCost_eq_square (w : ℤ) : K1_13_4_2_2_4.weightCost w = (w + 1)^2 / 4 := by
  have hw : w = 2 * (w / 2) + w % 2 := by omega
  have hsq : (w + 1)^2 = 4 * K1_13_4_2_2_4.weightCost w + (1 - w % 2) := by
    conv_lhs => rw [hw]
    rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with he | he <;>
      simp only [K1_13_4_2_2_4.weightCost, he] <;> ring
  omega
theorem weightCost_step (w : ℤ) :
    K1_13_4_2_2_4.weightCost (w + 1) - K1_13_4_2_2_4.weightCost w = (w + 2) / 2 := by
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with he | he
  · rw [K1_13_4_2_2_4.weightCost, K1_13_4_2_2_4.weightCost, show (w + 1) / 2 = w / 2 by omega,
      show (w + 1) % 2 = 1 by omega, show (w + 2) / 2 = w / 2 + 1 by omega, he]
    ring
  · rw [K1_13_4_2_2_4.weightCost, K1_13_4_2_2_4.weightCost, show (w + 1) / 2 = w / 2 + 1 by omega,
      show (w + 1) % 2 = 0 by omega, show (w + 2) / 2 = w / 2 + 1 by omega, he]
    ring
theorem triangular_sub_weightCost (w : ℤ) :
    triangular (w + 1) - K1_13_4_2_2_4.weightCost w = K1_13_4_2_2_4.weightCost (w + 1) := by
  have heq : 2 * (K1_13_4_2_2_4.weightCost (w + 1) + K1_13_4_2_2_4.weightCost w) = (w + 1) * (w + 2) := by
    rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with he | he
    · rw [K1_13_4_2_2_4.weightCost, K1_13_4_2_2_4.weightCost, show (w + 1) / 2 = w / 2 by omega,
        show (w + 1) % 2 = 1 by omega, he]
      conv_rhs => rw [show w = 2 * (w / 2) by omega]
      ring
    · rw [K1_13_4_2_2_4.weightCost, K1_13_4_2_2_4.weightCost, show (w + 1) / 2 = w / 2 + 1 by omega,
        show (w + 1) % 2 = 0 by omega, he]
      conv_rhs => rw [show w = 2 * (w / 2) + 1 by omega]
      ring
  linarith only [heq, K1_13_4_2_2_4.double_triangular (w + 1)]
theorem colength_weightCost {a w : ℤ} (ha : a ≤ (w + 1) / 2) (hw : 0 ≤ w) :
    colength ⟨a, w⟩ = K1_13_4_2_2_4.weightCost w := by
  unfold colength
  simp only [max_eq_right ha, max_eq_right (show 0 ≤ (w + 1) / 2 by omega),
    max_eq_right (show (w + 1) / 2 ≤ w by omega)]
  have h : w - (w + 1) / 2 = w / 2 := by omega
  rw [h, K1_13_4_2_2_4.weightCost]
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with he | he
  · rw [show (w + 1) / 2 = w / 2 by omega, he]
    nlinarith only [K1_13_4_2_2_4.double_triangular (w / 2)]
  · rw [show (w + 1) / 2 = w / 2 + 1 by omega, he]
    nlinarith only [K1_13_4_2_2_4.double_triangular (w / 2), K1_13_4_2_2_4.double_triangular (w / 2 + 1)]
def weightPrefix (w : ℤ) : ℤ :=
  let m := w / 2
  m * (m + 1) * (4 * m + 5) + 6 * (w % 2) * (m + 1)^2
theorem weightPrefix_step (w : ℤ) :
    weightPrefix (w + 1) - weightPrefix w = 6 * K1_13_4_2_2_4.weightCost (w + 1) := by
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with he | he
  · rw [weightPrefix, weightPrefix, K1_13_4_2_2_4.weightCost, show (w + 1) / 2 = w / 2 by omega,
      show (w + 1) % 2 = 1 by omega, he]
    ring
  · rw [weightPrefix, weightPrefix, K1_13_4_2_2_4.weightCost, show (w + 1) / 2 = w / 2 + 1 by omega,
      show (w + 1) % 2 = 0 by omega, he]
    ring
def triPrefix (w : ℤ) : ℤ :=
  let n := max 0 w
  (n - 1) * n * (n + 1)
theorem triPrefix_step (w : ℤ) :
    triPrefix (w + 1) - triPrefix w = 6 * triangular (max 0 w) := by
  unfold triPrefix
  by_cases h : w < 0
  · rw [max_eq_left (show w + 1 ≤ 0 by omega), max_eq_left h.le]
    decide
  · rw [max_eq_right (show 0 ≤ w + 1 by omega), max_eq_right (show 0 ≤ w by omega)]
    linear_combination 3 * (K1_13_4_2_2_4.double_triangular w).symm
theorem scaled_sum (f p : ℤ → ℤ) (h : ∀ j, p (j + 1) - p j = 6 * f j)
    (a : ℤ) (n : ℕ) :
    6 * (∑ j ∈ range n, f (a + j)) = p (a + n) - p a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, ← h, Nat.cast_succ, ← add_assoc]
    ring
theorem sum_weight_down (a : ℤ) (n : ℕ) :
    6 * (∑ j ∈ range n, K1_13_4_2_2_4.weightCost (a - j)) = weightPrefix a - weightPrefix (a - n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, Nat.cast_succ]
    have h := weightPrefix_step (a - (n : ℤ) - 1)
    rw [sub_add_cancel] at h
    rw [show a - ((n : ℤ) + 1) = a - n - 1 by ring]
    linarith only [h]
def capCount (q w : ℤ) : ℤ :=
  K1_13_4_2_2_4.weightCost (w + 1) - triangular (max 0 (w - q))
theorem cumulative_eq {q w : ℤ} (hw : 0 ≤ w) (hq : w ≤ 2 * q) :
    cumulative q w = capCount q w := by
  rw [cumulative, ite_eq_right (not_lt.mpr hw), min_eq_left hq, capCount, weightCost_eq_square]
  ring_nf
private theorem capCount_step {q w : ℤ} (hw : 0 ≤ w) (hq : w + 1 ≤ 2 * q) :
    capCount q w ≤ capCount q (w + 1) := by
  have hW := weightCost_step (w + 1)
  have hT : triangular (max 0 (w + 1 - q)) - triangular (max 0 (w - q)) =
      max 0 (w + 1 - q) := by
    by_cases h : w < q
    · rw [max_eq_left (show w + 1 - q ≤ 0 by omega), max_eq_left (show w - q ≤ 0 by omega)]
      exact sub_self _
    · rw [max_eq_right (show 0 ≤ w + 1 - q by omega), max_eq_right (show 0 ≤ w - q by omega)]
      nlinarith only [K1_13_4_2_2_4.double_triangular (w + 1 - q), K1_13_4_2_2_4.double_triangular (w - q)]
  unfold capCount
  omega
theorem capCount_mono {q : ℤ} {w v : ℕ} (hwv : w ≤ v) (hv : (v : ℤ) ≤ 2 * q) :
    capCount q w ≤ capCount q v := by
  induction v with
  | zero =>
    obtain rfl : w = 0 := by omega
    exact le_rfl
  | succ v ih =>
    by_cases h : w = v + 1
    · rw [h]
    · refine (ih (by omega) (by omega)).trans ?_
      simpa only [Nat.cast_succ] using capCount_step (q := q) (w := (v : ℤ)) (by omega) (by omega)
theorem capCount_full {q : ℤ} (hq : q ≤ 2300) :
    capCount q 2300 = triangular (q + 1) - K1_13_4_2_2_4.weightCost (2 * q - 2300) := by
  have hQ : K1_13_4_2_2_4.weightCost (2 * q - 2300) = (q - 1150) * (q - 1149) := by
    rw [K1_13_4_2_2_4.weightCost, show (2 * q - 2300) / 2 = q - 1150 by omega,
      show (2 * q - 2300) % 2 = 0 by omega]
    ring
  rw [capCount, max_eq_right (show 0 ≤ 2300 - q by omega),
    show K1_13_4_2_2_4.weightCost (2300 + 1) = 1324801 by decide, hQ]
  nlinarith only [K1_13_4_2_2_4.double_triangular (2300 - q), K1_13_4_2_2_4.double_triangular (q + 1)]
end K1_13_4_2_2_4
end
section
namespace K1_13_4_2_2_5
open K1_13_4_2_2
open scoped BigOperators
set_option maxHeartbeats 1000000
private theorem moments (len : ℕ) :
    2 * (∑ i ∈ Finset.range len, (i : ℤ)) = (len : ℤ) * (len - 1 : ℤ) ∧
    6 * (∑ i ∈ Finset.range len, (i : ℤ) ^ 2) =
      (len : ℤ) * (len - 1 : ℤ) * (2 * len - 1 : ℤ) := by
  induction len with
  | zero => simp
  | succ len ih =>
    simp only [Finset.sum_range_succ, Nat.cast_succ]
    exact ⟨by nlinarith only [ih.1], by nlinarith only [ih.2]⟩
private theorem cost_progression (a b x : ℤ) :
    cost (a + 2 * b * x) = cost a + b * (a + 1) * x + b ^ 2 * x ^ 2 := by
  have hs : (a + 1) / 2 + (a / 2 + 1) = a + 1 := by omega
  have he : 2 * b * x = 2 * (b * x) := by ring
  have h₁ : (a + 2 * b * x + 1) / 2 = (a + 1) / 2 + b * x := by rw [he]; omega
  have h₂ : (a + 2 * b * x) / 2 = a / 2 + b * x := by rw [he]; omega
  unfold cost
  rw [h₁, h₂]
  linear_combination (b * x) * hs
private theorem const_sum (a : ℤ) (len : ℕ) :
    (∑ _i ∈ Finset.range len, a) = (len : ℤ) * a := by
  simp
private theorem quadratic_sum (a b c : ℤ) (len : ℕ) :
    (∑ i ∈ Finset.range len, (a + b * (i : ℤ) + c * (i : ℤ) ^ 2)) =
      (len : ℤ) * a + b * linearSum len + c * squareSum len := by
  have h₁ : linearSum len = ∑ i ∈ Finset.range len, (i : ℤ) := by
    unfold linearSum
    have h := (moments len).1
    omega
  have h₂ : squareSum len = ∑ i ∈ Finset.range len, (i : ℤ) ^ 2 := by
    unfold squareSum
    have h := (moments len).2
    omega
  simp only [Finset.sum_add_distrib, const_sum, Finset.mul_sum, h₁, h₂]
private theorem sumCost_eq (a b : ℤ) (len : ℕ) :
    sumCost a b len = ∑ i ∈ Finset.range len, cost (a + 2 * b * i) := by
  simp_rw [cost_progression]
  exact (quadratic_sum _ _ _ _).symm
private theorem sumSquare_eq (a b : ℤ) (len : ℕ) :
    sumSquare a b len = ∑ i ∈ Finset.range len, (a + b * i) ^ 2 := by
  have h (i : ℕ) : (a + b * (i : ℤ)) ^ 2 = a ^ 2 + (2 * a * b) * i + b ^ 2 * (i : ℤ) ^ 2 :=
    by ring
  simp_rw [h]
  exact (quadratic_sum _ _ _ _).symm
private def modeRank (mode : Mode) (k t : ℤ) : ℤ :=
  match mode with
  | .columns => columns k
  | .empty => cost t
  | .shifted both => shiftedRank both k t
private theorem modeSum_eq (mode : Mode) (k start : ℤ) (len : ℕ) :
    modeSum mode k start len = ∑ i ∈ Finset.range len, modeRank mode k (start + 2 * i) := by
  cases mode with
  | columns => exact (const_sum _ _).symm
  | empty => simpa only [modeSum, modeRank, mul_one] using sumCost_eq start 1 len
  | shifted both =>
    simp only [modeSum, modeRank, sumCost_eq, sumSquare_eq, ← const_sum (columns k) len,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases both <;> simp [shiftedRank, linearAt, linearPower, conicPower]
    all_goals
      apply congrArg₂ (fun a b : ℤ => a - b)
      · apply congrArg₂ (fun a b : ℤ => a + b)
        · apply congrArg (fun a : ℤ => columns k + a)
          apply congrArg cost
          ring
        · apply congrArg cost
          ring
      · apply congrArg (fun a : ℤ => a ^ 2)
        ring
private def contact (k : ℕ) (t : ℤ) : ℤ :=
  let q := (7300 - (k : ℤ) - t).toNat
  blockBound q (offset k) (powers q k)
private theorem contact_le {k : ℕ} {mode : Mode} {l r t : ℤ}
    (ha : valid mode k l r) (hl : l ≤ t) (hr : t ≤ r)
    (hpos : 0 < t) (hmax : t ≤ 5000 - (k : ℤ)) :
    contact k t ≤ modeRank mode k t := by
  let q := (7300 - (k : ℤ) - t).toNat
  have hq : 2300 ≤ q := by dsimp [q]; omega
  have ht : planeOrder q (offset k) = t := by unfold planeOrder offset q; omega
  change (blockBound q (offset k) (powers q k) : ℤ) ≤ _
  cases mode with
  | columns => exact block_columns hq
  | empty => exact block_empty hq ht hpos
  | shifted both => exact block_shifted hq ht hpos (admissible_point ha hl hr)
private theorem parity_sound (k fuel : ℕ) (start : ℤ) (len : ℕ) (hpos : 0 < start)
    (hmax : ∀ i : ℕ, i < len → start + 2 * i ≤ 5000 - (k : ℤ)) :
    (∑ i ∈ Finset.range len, contact k (start + 2 * i)) ≤ parityBound k fuel start len := by
  have width_bound (n : ℕ) (mode : Mode) (s : ℤ) : runLength k s n mode ≤ n := by
    unfold runLength
    split <;> omega
  induction fuel generalizing start len with
  | zero =>
    rw [parityBound, ← const_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact contact_le (mode := .columns) (l := start) (r := start + 2 * i)
      trivial (by omega) le_rfl (by omega) (hmax i (Finset.mem_range.mp hi))
  | succ fuel ih =>
    rw [parityBound]
    split
    · rename_i h
      simp [h]
    · let mode := chooseMode k start
      let width := runLength k start len mode
      let last := start + 2 * ((width : ℤ) - 1)
      have hw : width ≤ len := width_bound len mode start
      change _ ≤ (if valid mode k start last then modeSum mode k start width
        else (width : ℤ) * columns k) + parityBound k fuel (start + 2 * width) (len - width)
      conv_lhs =>
        rw [show len = width + (len - width) by omega, Finset.sum_range_add]
      apply add_le_add
      · split
        · rename_i hv
          rw [modeSum_eq]
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_range.mp hi
          exact contact_le hv (by omega) (by dsimp [last]; omega) (by omega) (hmax i (by omega))
        · rw [← const_sum]
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_range.mp hi
          exact contact_le (mode := .columns) (l := start) (r := start + 2 * i)
            trivial (by omega) le_rfl (by omega) (hmax i (by omega))
      · have hr (i : ℕ) (hi : i < len - width) :
            start + 2 * (width : ℤ) + 2 * (i : ℤ) ≤ 5000 - (k : ℤ) := by
          simpa only [Nat.cast_add, mul_add, add_assoc] using hmax (width + i) (by omega)
        have h := ih (start + 2 * width) (len - width) (by omega) hr
        refine le_trans (le_of_eq ?_) h
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        push_cast
        ring
private theorem sum_by_parity (f : ℕ → ℤ) (len : ℕ) :
    (∑ i ∈ Finset.range len, f i) = (∑ i ∈ Finset.range ((len + 1) / 2), f (2 * i)) +
      ∑ i ∈ Finset.range (len / 2), f (2 * i + 1) := by
  induction len with
  | zero => simp
  | succ len ih =>
    rw [Finset.sum_range_succ, ih]
    rcases (show len % 2 = 0 ∨ len % 2 = 1 by omega) with he | ho
    · rw [show (len.succ + 1) / 2 = (len + 1) / 2 + 1 by omega,
        show len.succ / 2 = len / 2 by omega, Finset.sum_range_succ (fun i => f (2 * i)),
        show 2 * (len / 2) = len by omega]
      abel
    · rw [show (len.succ + 1) / 2 = (len + 1) / 2 by omega,
        show len.succ / 2 = len / 2 + 1 by omega, Finset.sum_range_succ (fun i => f (2 * i + 1)),
        show 2 * (len / 2) + 1 = len by omega]
      abel
private theorem offset_sound {k : ℕ} (hk : k < 5000) :
    (∑ j ∈ Finset.range 2700, (blockBound (2300 + j) (offset k) (powers (2300 + j) k) : ℤ)) ≤
      offsetTotal k := by
  let len := min 2700 (5000 - k)
  let start : ℤ := 5001 - (k : ℤ) - len
  let rank (j : ℕ) : ℤ := blockBound (2300 + j) (offset k) (powers (2300 + j) k)
  change (∑ j ∈ Finset.range 2700, rank j) ≤ _
  have hlen : len ≤ 2700 := min_le_left _ _
  have hklen : len ≤ 5000 - k := min_le_right _ _
  have htrim : (∑ j ∈ Finset.range 2700, rank j) = ∑ j ∈ Finset.range len, rank j := by
    symm
    apply Finset.sum_subset (Finset.range_mono hlen)
    intro j hj h
    have hj' := Finset.mem_range.mp hj
    have hj'' := mt Finset.mem_range.mpr h
    have hcut : planeOrder (2300 + j) (offset k) ≤ 0 := by
      unfold planeOrder offset
      dsimp [len] at hj''
      omega
    simp [rank, blockBound, hcut]
  have hreflect : (∑ j ∈ Finset.range len, rank j) = ∑ j ∈ Finset.range len, contact k (start + j) := by
    rw [← Finset.sum_range_reflect rank len]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have he : (7300 - (k : ℤ) - (start + j)).toNat = 2300 + (len - 1 - j) := by
      dsimp [start]
      omega
    simp only [rank, contact, he]
  have hpos : 0 < start := by dsimp [start]; omega
  rw [htrim, hreflect, sum_by_parity]
  change _ ≤ parityBound k 8 start ((len + 1) / 2) + parityBound k 8 (start + 1) (len / 2)
  apply add_le_add
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      parity_sound k 8 start ((len + 1) / 2) hpos (by intros; dsimp [start]; omega)
  · simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
      parity_sound k 8 (start + 1) (len / 2) (by omega) (by intros; dsimp [start]; omega)
private theorem total_sum (n : ℕ) :
    total 0 n = ∑ k ∈ Finset.range n, offsetTotal k := by
  induction n with
  | zero => simp [total]
  | succ n ih => rw [total, Finset.sum_range_succ, ih, Nat.zero_add]
theorem proof : K1_13_4_2_2.c5 := by
  refine ⟨powers, ?_⟩
  apply Int.ofNat_le.mp
  push_cast [gradeBound]
  rw [Finset.sum_comm]
  have htrim : (∑ k ∈ Finset.range 7300, ∑ j ∈ Finset.range 2700,
      (blockBound (2300 + j) (offset k) (powers (2300 + j) k) : ℤ)) =
      ∑ k ∈ Finset.range 5000, ∑ j ∈ Finset.range 2700,
        (blockBound (2300 + j) (offset k) (powers (2300 + j) k) : ℤ) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by decide))
    intro k _ hk
    have hk' := mt Finset.mem_range.mpr hk
    apply Finset.sum_eq_zero
    intro j _
    have hcut : planeOrder (2300 + j) (offset k) ≤ 0 := by unfold planeOrder offset; omega
    simp [blockBound, hcut]
  rw [htrim]
  calc
    _ ≤ ∑ k ∈ Finset.range 5000, offsetTotal k :=
      Finset.sum_le_sum fun k hk => offset_sound (Finset.mem_range.mp hk)
    _ = total 0 5000 := (total_sum 5000).symm
    _ ≤ 5196036704622 := le_of_eq total_value
end K1_13_4_2_2_5
end
section
namespace K1_13_4_2_3_1
open K1_13 K1_13_4_2 K1_13_4_2_3
open scoped Polynomial Pointwise
noncomputable section
abbrev Exp := Fin 3 →₀ ℕ
abbrev Jets (R : Type*) [CommRing R] := MvPolynomial (Fin 3) R
def grade (e : Exp) : ℕ := e 0 + e 1 + e 2
def weight (e : Exp) : ℕ := e 1 + 2 * e 2
private def Below (d e : Exp) : Prop :=
  grade d = grade e ∧ weight d ≤ weight e ∧ d 2 ≤ e 2
private theorem below_add {d e f g : Exp} (h₁ : Below d e) (h₂ : Below f g) :
    Below (d + f) (e + g) := by
  obtain ⟨h₁, h₂', h₃⟩ := h₁
  obtain ⟨h₄, h₅, h₆⟩ := h₂
  simp only [Below, grade, weight, Finsupp.add_apply] at *
  omega
@[simp] theorem canonical_C {R : Type*} [CommRing R] (t c : R) :
    canonical t (MvPolynomial.C c) = MvPolynomial.C c :=
  MvPolynomial.eval₂Hom_C _ _ _
@[simp] theorem canonical_X {R : Type*} [CommRing R] (t : R) (i : Fin 3) :
    canonical t (MvPolynomial.X i) = canonicalJet t i :=
  MvPolynomial.eval₂Hom_X' _ _ _
private theorem jet_support {R : Type*} [CommRing R] (t : R) (i : Fin 3)
    {d : Exp} (hd : d ∈ (canonicalJet t i).support) :
    Below d (Finsupp.single i 1) := by
  classical
  fin_cases i
  all_goals
    simp [canonicalJet, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X] at hd
    try split_ifs at hd
    all_goals subst_vars
    all_goals simp_all [Below, grade, weight]
theorem canonical_support {R : Type*} [CommRing R] (t : R) (G : K1_13_4_2_3_1.Jets R)
    {d : Exp} (hd : d ∈ (canonical t G).support) :
    ∃ e ∈ G.support, grade d = grade e ∧ weight d ≤ weight e ∧ d 2 ≤ e 2 := by
  classical
  suffices h : ∀ d ∈ (canonical t G).support, ∃ e ∈ G.support, Below d e from h d hd
  clear d hd
  induction G using MvPolynomial.induction_on'' with
  | C r =>
      intro d hd
      simp only [canonical_C] at hd
      exact ⟨d, hd, rfl, le_rfl, le_rfl⟩
  | monomial_add a b G ha hb hG hm =>
      have hs : (MvPolynomial.monomial a b + G).support = insert a G.support := by
        have ha' : G.coeff a = 0 := MvPolynomial.notMem_support_iff.mp ha
        ext e
        by_cases he : a = e
        · subst e
          simp [MvPolynomial.coeff_monomial, ha', hb]
        · simp [MvPolynomial.coeff_monomial, he, Ne.symm he]
      intro d hd
      rw [map_add] at hd
      rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
      · obtain ⟨e, he, hde⟩ := hm d hd
        rw [hs]
        have hea : e = a := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
        subst e
        exact ⟨a, Finset.mem_insert_self _ _, hde⟩
      · obtain ⟨e, he, hde⟩ := hG d hd
        exact ⟨e, hs.symm ▸ Finset.mem_insert_of_mem he, hde⟩
  | mul_X G i hG =>
      intro d hd
      rw [map_mul, canonical_X] at hd
      obtain ⟨f, hf, g, hg, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hd)
      obtain ⟨e, he, hfe⟩ := hG f hf
      refine ⟨e + Finsupp.single i 1, ?_, below_add hfe (jet_support t i hg)⟩
      rw [MvPolynomial.support_mul_X]
      exact Finset.mem_map.mpr ⟨e, he, rfl⟩
theorem map_canonical {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (t : R)
    (G : K1_13_4_2_3_1.Jets R) : MvPolynomial.map f (canonical t G) = canonical (f t) (MvPolynomial.map f G) := by
  have h : (MvPolynomial.map f).comp (canonical t) =
      (canonical (f t)).comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      fin_cases i <;> simp [canonicalJet]
  exact DFunLike.congr_fun h G
private def scale {R : Type*} [CommRing R] (t : R) (n : ℕ) : K1_13_4_2_3_1.Jets R →+* K1_13_4_2_3_1.Jets R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => MvPolynomial.C (t ^ (n - i.val)) * MvPolynomial.X i)
private theorem scale_coeff {R : Type*} [CommRing R] (t : R) (n : ℕ) (G : K1_13_4_2_3_1.Jets R)
    (e : Exp) :
    (scale t n G).coeff e = t ^ ((n - 0) * e 0 + (n - 1) * e 1 + (n - 2) * e 2) * G.coeff e := by
  classical
  let k (d : Exp) := (n - 0) * d 0 + (n - 1) * d 1 + (n - 2) * d 2
  change (scale t n G).coeff e = t ^ k e * G.coeff e
  induction G using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ, mul_add]
  | monomial d r =>
      have hmono : (∏ i : Fin 3, MvPolynomial.X i ^ d i) = (MvPolynomial.monomial d 1 : K1_13_4_2_3_1.Jets R) := by
        rw [← Finsupp.prod_fintype d _ (by simp)]
        exact (MvPolynomial.monic_monomial_eq d).symm
      rw [scale, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype d _ (by simp)]
      simp_rw [mul_pow, ← map_pow, ← pow_mul]
      rw [Finset.prod_mul_distrib, hmono, ← map_prod, Finset.prod_pow_eq_pow_sum,
        Fin.sum_univ_three, ← mul_assoc, ← map_mul, MvPolynomial.coeff_C_mul]
      simp only [MvPolynomial.coeff_monomial]
      split
      · rename_i hd
        subst d
        simp [k, mul_comm]
      · simp
private theorem scale_canonical {R : Type*} [CommRing R] (t : R) (G : K1_13_4_2_3_1.Jets R) :
    scale t 2 (canonical t G) = canonical 1 (scale t 3 G) := by
  have h : (scale t 2).comp (canonical t) = (canonical 1).comp (scale t 3) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [scale]
    · intro i
      fin_cases i <;> simp [canonicalJet, scale, pow_succ] <;> ring
  exact DFunLike.congr_fun h G
private theorem canonical_one_dvd_iff {R : Type*} [CommRing R] (r : R) (G : K1_13_4_2_3_1.Jets R) :
    MvPolynomial.C r ∣ canonical 1 G ↔ MvPolynomial.C r ∣ G := by
  let inv : K1_13_4_2_3_1.Jets R →+* K1_13_4_2_3_1.Jets R := MvPolynomial.eval₂Hom MvPolynomial.C
    ![MvPolynomial.X 0, MvPolynomial.X 1 - MvPolynomial.X 0,
      MvPolynomial.X 2 - MvPolynomial.X 1 + MvPolynomial.X 0]
  have hi : inv.comp (canonical 1) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [inv]
    · intro i
      fin_cases i <;> simp [canonicalJet, inv]
  constructor
  · intro h
    have hh := map_dvd inv h
    have hleft : inv (canonical 1 G) = G := DFunLike.congr_fun hi G
    have hC : inv (MvPolynomial.C r) = MvPolynomial.C r := MvPolynomial.eval₂Hom_C _ _ _
    rwa [hleft, hC] at hh
  · intro h
    simpa only [canonical_C] using map_dvd (canonical (1 : R)) h
def probe {R : Type*} [CommRing R] (q : ℕ) (e : Exp) (i : ℕ) (G : K1_13_4_2_3_1.Jets R[X]) : R :=
  if i < weight e then (G.coeff e).coeff i
  else ((canonical Polynomial.X G).coeff e).coeff (q + i)
theorem grade_probe_iff {R : Type*} [CommRing R] (q L : ℕ) (G : K1_13_4_2_3_1.Jets R[X])
    (hG : ∀ e ∈ G.support, grade e = q ∧ q + weight e ≤ L) (hq : q ≤ L) :
    MvPolynomial.C ((Polynomial.X : R[X]) ^ L) ∣ canonical Polynomial.X G ↔
      ∀ e i, i < L - q → probe q e i G = 0 := by
  let A := canonical (Polynomial.X : R[X]) G
  have hA : ∀ e ∈ A.support, grade e = q ∧ q + weight e ≤ L := by
    intro e he
    obtain ⟨d, hd, hgrade, hw, _⟩ := canonical_support _ _ he
    exact ⟨hgrade.trans (hG d hd).1, (Nat.add_le_add_left hw _).trans (hG d hd).2⟩
  let Low := ∀ e i, i < weight e → (G.coeff e).coeff i = 0
  let High := ∀ e i, weight e ≤ i → i < L - q → (A.coeff e).coeff (q + i) = 0
  have htests : (∀ e i, i < L - q → probe q e i G = 0) ↔ Low ∧ High := by
    constructor
    · intro h
      refine ⟨?_, fun e i hw hi => by simpa [probe, not_lt.mpr hw, A] using h e i hi⟩
      intro e i hi
      by_cases he : e ∈ G.support
      · simpa [probe, hi] using h e i (by have := (hG e he).2; omega)
      · simp [MvPolynomial.notMem_support_iff.mp he]
    · rintro ⟨hl, hh⟩ e i hi
      by_cases hw : i < weight e
      · simpa [probe, hw] using hl e i hw
      · simpa [probe, hw, A] using hh e i (Nat.le_of_not_gt hw) hi
  have scale_low (n m : ℕ) (P : K1_13_4_2_3_1.Jets R[X]) (hP : ∀ e ∈ P.support, grade e = q) (hn : 2 ≤ n) :
      MvPolynomial.C ((Polynomial.X : R[X]) ^ (n * q + m)) ∣ scale Polynomial.X n P ↔
        ∀ e i, i < m + weight e → (P.coeff e).coeff i = 0 := by
    simp only [MvPolynomial.C_dvd_iff_dvd_coeff, Polynomial.X_pow_dvd_iff, scale_coeff,
      Polynomial.coeff_X_pow_mul']
    have hshift (e : Exp) (he : e ∈ P.support) :
        (n - 0) * e 0 + (n - 1) * e 1 + (n - 2) * e 2 + weight e = n * q := by
      rw [← hP e he]
      simp only [grade, weight, Nat.sub_zero]
      have h₁ : n - 1 + 1 = n := by omega
      have h₂ : n - 2 + 2 = n := by omega
      have hm₁ := congrArg (fun x => x * e 1) h₁
      have hm₂ := congrArg (fun x => x * e 2) h₂
      simp only [Nat.add_mul, Nat.one_mul] at hm₁ hm₂
      simp only [Nat.mul_add]
      omega
    constructor
    · intro h e i hi
      by_cases he : e ∈ P.support
      · let s := (n - 0) * e 0 + (n - 1) * e 1 + (n - 2) * e 2
        have hs : s + weight e = n * q := hshift e he
        have hz := h e (s + i) (by omega)
        change (if s ≤ s + i then (P.coeff e).coeff (s + i - s) else 0) = 0 at hz
        simpa only [ite_eq_left (by omega : s ≤ s + i), show s + i - s = i by omega] using hz
      · simp [MvPolynomial.notMem_support_iff.mp he]
    · intro h e i hi
      by_cases he : e ∈ P.support
      · split
        · exact h e _ (by have := hshift e he; omega)
        · rfl
      · simp [MvPolynomial.notMem_support_iff.mp he]
  have hl : (∀ e i, i < q + weight e → (A.coeff e).coeff i = 0) ↔ Low := by
    have hs : MvPolynomial.C ((Polynomial.X : R[X]) ^ (3 * q + 0)) ∣ scale Polynomial.X 3 G
        ↔ Low := by
      simpa [Low] using scale_low 3 0 G (fun e he => (hG e he).1) (by decide)
    rw [← scale_low 2 q A (fun e he => (hA e he).1) (by decide), ← hs]
    rw [show 2 * q + q = 3 * q + 0 by omega]
    change MvPolynomial.C ((Polynomial.X : R[X]) ^ (3 * q + 0)) ∣
      scale Polynomial.X 2 (canonical Polynomial.X G) ↔ _
    rw [scale_canonical, canonical_one_dvd_iff]
  rw [htests, ← hl, MvPolynomial.C_dvd_iff_dvd_coeff]
  simp only [Polynomial.X_pow_dvd_iff]
  change (∀ e i, i < L → (A.coeff e).coeff i = 0) ↔ _
  constructor
  · intro h
    refine ⟨?_, fun e i _ hi => h e _ (by omega)⟩
    intro e i hi
    by_cases he : e ∈ A.support
    · exact h e i (hi.trans_le (hA e he).2)
    · simp [MvPolynomial.notMem_support_iff.mp he]
  · rintro ⟨hl', hh⟩ e i hi
    by_cases hw : i < q + weight e
    · exact hl' e i hw
    · have heq : q + (i - q) = i := by omega
      rw [← heq]
      exact hh e (i - q) (by omega) (by omega)
end
end K1_13_4_2_3_1
end
section
namespace K1_13_4_5
noncomputable section
open K1_13_4
def actualSeedResultant (F G : GenericRow) : Lower :=
  Polynomial.resultant (asSeedPoly F) (asSeedPoly G) (seedDegree F) (seedDegree G)
end
end K1_13_4_5
end
section
namespace K1_13_4_2_4
noncomputable section
open K1_13 K1_13_4 K1_13_4_2
open scoped Polynomial BigOperators
abbrev ShiftSeed := Geom[X][X]
def specializeShift (ε : Geom) : ShiftSeed →+* Geom[X] :=
  Polynomial.mapRingHom (Polynomial.evalRingHom ε)
def shiftedBlock (H : Geom[X]) (ε : Geom) : Geom[X] := H + Polynomial.C ε
def residueAtShift (N : ShiftSeed[X]) (D : ShiftSeed) (ε : Geom) : GenericSeed[X] :=
  genericResidue (N.map (specializeShift ε)) (specializeShift ε D)
def residueMultiplier (c a₀ a₁ : Geom[X]) : GenericSeed[X] :=
  liftX c * (liftX a₀ +
    Polynomial.C (algebraMap Geom[X] GenericSeed Polynomial.X) * liftX a₁)
def residueOffset (q : Geom[X]) : GenericSeed[X] :=
  Polynomial.C (algebraMap Geom[X] GenericSeed Polynomial.X) * liftX q
structure RegularResidue (H c q a₀ a₁ : Geom[X]) (N : ShiftSeed[X]) (D : ShiftSeed)
    (ε : Geom) : Prop where
  at_zero : (specializeShift ε D).eval 0 ≠ 0
  small : (N.map (specializeShift ε)).natDegree < (shiftedBlock H ε).natDegree
  generic_unit : IsCoprime (residueMultiplier c a₀ a₁) (liftX (shiftedBlock H ε))
  generic_congruence : liftX (shiftedBlock H ε) ∣
    residueMultiplier c a₀ a₁ * residueAtShift N D ε + residueOffset q
def restoreWith (H : Geom[X]) (R : GenericSeed[X]) (F : PhysicalRow) : RawRow :=
  MvPolynomial.eval₂
    (MvPolynomial.C.comp (Polynomial.mapRingHom (algebraMap Geom GenericSeed)))
    (fun i : SeedVar => i.elim
      (MvPolynomial.C (Polynomial.C (algebraMap Geom[X] GenericSeed Polynomial.X)))
      (fun i : Fin 3 =>
        MvPolynomial.C (Polynomial.hasseDeriv i.val R) +
          ∑ j : Fin 3, if j.val ≤ i.val then
            MvPolynomial.C (Polynomial.hasseDeriv (i.val - j.val) (liftX H)) *
              MvPolynomial.X j
          else 0)) F
end
end K1_13_4_2_4
end
section
namespace K1_13_4_4_1
noncomputable section
open Polynomial K1 K1_13 K1_13_4 K1_13_4_4
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev Exponent := SeedVar →₀ ℕ
abbrev RawRow := K1_13_4_2.RawRow
abbrev polePower := secondBox.b + secondBox.j
def weight (h : ℕ) (a : K1_13_4_4_1.Exponent) : ℕ :=
  a.sum (fun i e => i.elim 0 (fun j => (131071 + h - j.val) * e))
def restored {Γ s} (P : PoleData Γ s) (L : ResidueChart P) : PhysicalRow →+* RawRow :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Polynomial.mapRingHom (algebraMap Geom GenericSeed)))
    (fun i => i.elim
      (MvPolynomial.C (Polynomial.C (algebraMap Geom[X] GenericSeed Polynomial.X)))
      (restoredJet P L))
theorem restored_apply {Γ s} (P : PoleData Γ s) (L : ResidueChart P) (F : PhysicalRow) :
    restored P L F = restore P L F := rfl
private theorem caps_generic (F : PhysicalRow) :
    Caps secondBox (toGeneric F) ↔ Caps secondBox F := by
  have hs : (toGeneric F).support = F.support :=
    MvPolynomial.support_map_of_injective F (IsFractionRing.injective Geom[X] GenericX)
  simp only [Caps, jetTotal, jetIndex, seedDegree, MvPolynomial.weightedTotalDegree,
    MvPolynomial.degreeOf_eq_sup, hs]
private def cutoff (h T : ℕ) : Submodule Geom PhysicalRow where
  carrier := {F | TrueCut h T F}
  zero_mem' := by simp [TrueCut]
  add_mem' {F G} hF hG := by
    change TrueCut h T F at hF
    change TrueCut h T G at hG
    intro m hm
    have hor := Finset.mem_union.mp (MvPolynomial.support_add hm)
    have hbound : weight h m ≤ T := by
      rcases hor with hf | hg
      · exact (Nat.le_add_left ..).trans (hF m hf)
      · exact (Nat.le_add_left ..).trans (hG m hg)
    have hd (Q : PhysicalRow) (hQ : TrueCut h T Q) :
        (Q.coeff m).natDegree ≤ T - weight h m := by
      by_cases hmem : m ∈ Q.support
      · have hh : (Q.coeff m).natDegree + weight h m ≤ T := hQ m hmem
        omega
      · simp [MvPolynomial.notMem_support_iff.mp hmem]
    change ((F + G).coeff m).natDegree + weight h m ≤ T
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    have hh := (natDegree_add_le (F.coeff m) (G.coeff m)).trans (max_le (hd F hF) (hd G hG))
    omega
  smul_mem' c F hF := by
    intro m hm
    have hh : (F.coeff m).natDegree + weight h m ≤ T :=
      hF m (MvPolynomial.support_smul hm)
    rw [MvPolynomial.coeff_smul]
    exact (Nat.add_le_add_right (natDegree_smul_le c (F.coeff m)) _).trans hh
private def bank {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    Submodule Geom PhysicalRow :=
  ((capSpace secondBox).restrictScalars Geom).comap rowMap ⊓
  cutoff P.H.natDegree (t + polePower * P.H.natDegree) ⊓
  (⨅ i : I, K1_13_4_2.contactAt (embed (node i)) (embed (w i))) ⊓
  K1_13_4_2.poleCondition P L secondBox (liftX P.H)
private theorem mem_bank {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P)
    (t : ℕ) (F : PhysicalRow) : F ∈ bank w P L t ↔ Source w P L secondBox t F := by
  simp only [bank, Submodule.mem_inf, Submodule.mem_comap, Submodule.restrictScalars_mem,
    rowMap_apply, mem_capSpace, caps_generic, Submodule.mem_iInf,
    K1_13_4_2.mem_contactAt, K1_13_4_2.mem_poleCondition, Source, PhysicalContact]
  change ((_ ∧ TrueCut _ _ F) ∧ _) ∧ _ ↔ _
  tauto
private instance finiteBank {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    Module.Finite Geom (bank w P L t) := by
  classical
  let T := t + polePower * P.H.natDegree
  let E := SeedVar → Fin 70001
  let f : bank w P L t →ₗ[Geom] ((E × Fin (T + 1)) → Geom) := LinearMap.pi fun u =>
    (Polynomial.lcoeff Geom u.2.val).comp
      (((MvPolynomial.lcoeff Geom[X] (Finsupp.equivFunOnFinite.symm (fun i => (u.1 i).val))
        : PhysicalRow →ₗ[Geom[X]] Geom[X]).restrictScalars Geom).comp (bank w P L t).subtype)
  have hzero (Q : bank w P L t) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨F, hF⟩ := Q
    have hsrc := (mem_bank w P L t F).mp hF
    apply Subtype.ext
    change F = 0
    apply MvPolynomial.ext
    intro m
    change F.coeff m = 0
    by_contra hnz
    have hm := MvPolynomial.mem_support_iff.mpr hnz
    have hd : (F.coeff m).natDegree ≤ T := (Nat.le_add_right ..).trans (hsrc.2.1 m hm)
    have he (i : SeedVar) : m i < 70001 := by
      cases i with
      | none =>
        exact Nat.lt_succ_of_le ((MvPolynomial.le_degreeOf_of_mem_support none hm).trans hsrc.1.2.2.2)
      | some i =>
        by_cases hz : m (some i) = 0
        · simp [hz]
        let v : SeedVar → ℕ := fun j => j.elim 0 (fun _ => 1)
        have hi := (MvPolynomial.le_weightedTotalDegree v hm).trans hsrc.1.1
        have hs := Finset.single_le_sum (f := fun j => m j * v j)
          (fun j _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hz)
        have hsum : Finsupp.weight v m = ∑ j ∈ m.support, m j * v j := by
          simp [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
        rw [hsum] at hi
        change _ ≤ 6820 at hi
        change m (some i) * 1 ≤ _ at hs
        omega
    let u : E := fun i => ⟨m i, he i⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < T + 1
    · have hval := congrFun hQ (u, ⟨k, hk⟩)
      change (F.coeff (Finsupp.equivFunOnFinite.symm (fun i => (u i).val))).coeff k = 0 at hval
      have heq : Finsupp.equivFunOnFinite.symm (fun i => (u i).val) = m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro Q R h
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, h, sub_self]
private def boundaryDegree (h t : ℕ) (m : K1_13_4_4_1.Exponent) : ℕ :=
  t + polePower * h - weight h m
private def boundary (h t : ℕ) : PhysicalRow →ₗ[Geom] (K1_13_4_4_1.Exponent → Geom) :=
  LinearMap.pi fun m => (Polynomial.lcoeff Geom (boundaryDegree h t m)).comp
    ((MvPolynomial.lcoeff Geom[X] m).restrictScalars Geom)
private theorem boundary_apply (h t : ℕ) (F : PhysicalRow) (m : K1_13_4_4_1.Exponent) :
    boundary h t F m = (F.coeff m).coeff (boundaryDegree h t m) := rfl
private theorem below_boundary {h t : ℕ} {F : PhysicalRow}
    (hF : TrueCut h (t + polePower * h) F) (hz : boundary h t F = 0)
    (m : K1_13_4_4_1.Exponent) (hm : m ∈ F.support) :
    (F.coeff m).natDegree + weight h m < t + polePower * h := by
  have hle : (F.coeff m).natDegree + weight h m ≤ t + polePower * h := hF m hm
  by_contra! hn
  have heq : (F.coeff m).natDegree = boundaryDegree h t m := by
    unfold boundaryDegree
    omega
  have h := congrFun hz m
  rw [boundary_apply, ← heq, coeff_natDegree] at h
  exact (leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)) h
private def bankEval {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    bank w P L t →ₗ[Geom] (K1_13_4_4_1.Exponent → Geom) :=
  (boundary P.H.natDegree t).comp (bank w P L t).subtype
private theorem kernel_le {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    Module.finrank Geom (bankEval w P L (t + 1)).ker ≤
      Module.finrank Geom (bank w P L t) := by
  let f := (bank w P L (t + 1)).subtype.comp (bankEval w P L (t + 1)).ker.subtype
  have hm (F : (bankEval w P L (t + 1)).ker) : f F ∈ bank w P L t := by
    obtain ⟨hc, hcut, hphys, hpole⟩ := (mem_bank w P L _ _).mp F.val.property
    have hz : boundary P.H.natDegree (t + 1) F.val.val = 0 := LinearMap.mem_ker.mp F.property
    apply (mem_bank w P L _ _).mpr
    refine ⟨hc, fun m hm => ?_, hphys, hpole⟩
    have h := below_boundary hcut hz m hm
    change ((F.val.val).coeff m).natDegree + weight P.H.natDegree m ≤ t + polePower * P.H.natDegree
    omega
  apply LinearMap.finrank_le_finrank_of_injective (f := f.codRestrict _ hm)
  intro F G he
  have heq := congrArg (fun Q : bank w P L t => Q.val) he
  exact Subtype.ext (Subtype.ext heq)
private theorem independent_generic {ι : Type*} [Fintype ι] {h t : ℕ} (e : ι → PhysicalRow)
    (hcut : ∀ i, TrueCut h (t + polePower * h) (e i))
    (he : LinearIndependent Geom (fun i => boundary h t (e i))) :
    LinearIndependent GenericX (fun i => toGeneric (e i)) := by
  apply (LinearIndependent.iff_fractionRing Geom[X] GenericX).mp
  let f : PhysicalRow →ₗ[Geom[X]] GenericRow :=
    (MvPolynomial.mapAlgHom (Algebra.ofId Geom[X] GenericX)).toLinearMap
  suffices hi : LinearIndependent Geom[X] e from
    hi.map' f (LinearMap.ker_eq_bot.mpr toGeneric_injective)
  classical
  rw [Fintype.linearIndependent_iff] at he ⊢
  intro c hc j
  by_contra hj
  let n := Finset.univ.sup (fun i => (c i).natDegree)
  have hn (i : ι) : (c i).natDegree ≤ n :=
    Finset.le_sup (f := fun i => (c i).natDegree) (Finset.mem_univ i)
  have hd (i : ι) (m : K1_13_4_4_1.Exponent) : ((e i).coeff m).natDegree ≤ boundaryDegree h t m := by
    by_cases hm : m ∈ (e i).support
    · have hh : ((e i).coeff m).natDegree + weight h m ≤ _ := hcut i m hm
      unfold boundaryDegree
      omega
    · simp [MvPolynomial.notMem_support_iff.mp hm]
  have hz : (∑ i, (c i).coeff n • boundary h t (e i)) = 0 := by
    funext m
    simpa only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul,
      Polynomial.finsetSum_coeff, coeff_mul_add_eq_of_natDegree_le (hn _) (hd _ m),
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, Polynomial.coeff_zero,
      Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, boundary_apply]
      using congrArg (fun F : PhysicalRow => (F.coeff m).coeff (n + boundaryDegree h t m)) hc
  have hlt (i : ι) (hi : c i ≠ 0) : (c i).natDegree < n :=
    lt_of_le_of_ne (hn i) (fun h => hi (leadingCoeff_eq_zero.mp (by
      rw [← coeff_natDegree, h, he _ hz i])))
  have hpos := (Nat.zero_le _).trans_lt (hlt j hj)
  have hle : n ≤ n - 1 := Finset.sup_le fun i _ => by
    by_cases hi : c i = 0
    · simp [hi]
    · have hh := hlt i hi
      omega
  omega
end
end K1_13_4_4_1
end
section
namespace K1_13_4_5
noncomputable section
open K1 K1_13 K1_13_4
open scoped Polynomial BigOperators
theorem lowerIndex_eq_weighted (Q : Lower) :
    lowerIndex Q = MvPolynomial.weightedTotalDegree Fin.val Q := by
  unfold lowerIndex MvPolynomial.weightedTotalDegree
  simp only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]
theorem fixed_lower (f : GenericRow) (hf : f ≠ 0) (hu : seedDegree f = 0) :
    ∃ q : Lower, q ≠ 0 ∧ q.totalDegree = jetTotal f ∧ lowerIndex q = jetIndex f ∧
      ∀ z y, MvPolynomial.eval (atPoint z y) f = MvPolynomial.eval y q := by
  have hsome : Function.Injective (Option.some : Fin 3 → SeedVar) := Option.some_injective _
  have hv : (f.vars : Set SeedVar) ⊆ Set.range (Option.some : Fin 3 → SeedVar) := by
    intro i hi
    cases i with
    | none => exact ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hu).elim
    | some i => exact ⟨i, rfl⟩
  obtain ⟨q, hq⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range f some hsome hv
  rw [← hq] at hf ⊢
  refine ⟨q, fun h => hf (by simp [h]), ?_, ?_, ?_⟩
  · rw [jetTotal, MvPolynomial.weightedTotalDegree_rename_of_injective hsome,
      ← MvPolynomial.weightedTotalDegree_one]
    rfl
  · rw [jetIndex, MvPolynomial.weightedTotalDegree_rename_of_injective hsome,
      lowerIndex_eq_weighted]
    rfl
  · intro z y
    rw [MvPolynomial.eval_rename]
    rfl
theorem pure_eval (p : GenericX[X]) (z : GenericX) (y : Fin 3 → GenericX) :
    MvPolynomial.eval (atPoint z y) (pureSeed p) = p.eval z := by
  let e := MvPolynomial.eval (atPoint z y)
  have he : e.comp (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X none)) =
      Polynomial.evalRingHom z := by
    apply Polynomial.ringHom_ext
    · intro x
      simp [e]
    · simp [e, atPoint]
  exact DFunLike.congr_fun he p
def seedBook (Γ : Finset K) (z : K → Geom) (p : GenericX[X]) : Finset K := by
  classical
  exact Γ.filter fun γ => p.eval (inclConst (z γ)) = 0
theorem mem_seedBook {Γ : Finset K} {z : K → Geom} {p : GenericX[X]} {γ : K} :
    γ ∈ seedBook Γ z p ↔ γ ∈ Γ ∧ p.eval (inclConst (z γ)) = 0 := by
  classical
  simp [seedBook]
theorem count_seed_roots (Γ : Finset K) (z : K → Geom) (hz : Function.Injective z)
    (p : GenericX[X]) (hp : p ≠ 0) :
    (seedBook Γ z p).card ≤ p.natDegree := by
  classical
  let B := seedBook Γ z p
  let e : K → GenericX := fun γ => inclConst (z γ)
  rw [show (seedBook Γ z p).card = (B.image e).card by
    have he : Function.Injective e := inclConst.injective.comp hz
    exact (Finset.card_image_of_injective B he).symm]
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  change x ∈ B.image e at hx
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
  exact (Polynomial.mem_roots hp).mpr (mem_seedBook.mp hγ).2
theorem actual_resultant_ne_zero {F G : GenericRow} (hF : Irreducible F)
    (hdeg : 0 < seedDegree F) (hrel : IsRelPrime F G) :
    actualSeedResultant F G ≠ 0 := by
  let e := MvPolynomial.optionEquivLeft GenericX (Fin 3)
  let φ := algebraMap Lower (FractionRing Lower)
  have hinj : Function.Injective φ := IsFractionRing.injective Lower (FractionRing Lower)
  have hsize (P : GenericRow) : (asSeedPoly P).natDegree = seedDegree P := by
    simp [asSeedPoly, seedDegree]
  have hi : Irreducible (asSeedPoly F) := (MulEquiv.irreducible_iff e).mpr hF
  have hp : (asSeedPoly F).IsPrimitive := hi.isPrimitive (by rw [hsize]; omega)
  have him : Irreducible ((asSeedPoly F).map φ) :=
    hp.irreducible_iff_irreducible_map_fraction_map.mp hi
  have hcop : IsCoprime ((asSeedPoly F).map φ) ((asSeedPoly G).map φ) := by
    apply him.coprime_iff_not_dvd.mpr
    intro hd
    obtain ⟨a, ha⟩ := hp.dvd_of_fraction_map_dvd_fraction_map hd
    apply hF.isRelPrime_iff_not_dvd.mp hrel
    refine ⟨e.symm a, e.injective ?_⟩
    change e G = e F * a at ha
    simpa only [map_mul, e.apply_symm_apply] using ha
  have hn := Polynomial.resultant_ne_zero _ _ hcop
  intro hz
  apply hn
  rw [Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.natDegree_map_eq_of_injective hinj, hsize, hsize, Polynomial.resultant_map_map]
  change φ (actualSeedResultant F G) = 0
  rw [hz, map_zero]
theorem actual_resultant_vanishes {F G : GenericRow} (hdeg : 0 < seedDegree F)
    {z : GenericX} {y : Fin 3 → GenericX}
    (hF : MvPolynomial.eval (atPoint z y) F = 0)
    (hG : MvPolynomial.eval (atPoint z y) G = 0) :
    MvPolynomial.eval y (actualSeedResultant F G) = 0 := by
  have hsize (P : GenericRow) : (asSeedPoly P).natDegree ≤ seedDegree P := by
    simp [asSeedPoly, seedDegree]
  obtain ⟨a, b, _, _, he⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    (asSeedPoly F) (asSeedPoly G) (hsize F) (hsize G) (Or.inl (Nat.ne_of_gt hdeg))
  have hEval (P : GenericRow) :
      Polynomial.eval₂RingHom (MvPolynomial.eval y) z (asSeedPoly P) =
        MvPolynomial.eval (atPoint z y) P := by
    change (asSeedPoly P).eval₂ (MvPolynomial.eval y) z = _
    rw [Polynomial.eval₂_eq_eval_map]
    exact (MvPolynomial.optionEquivLeft_elim_eval GenericX (Fin 3) y z P).symm
  have h := congrArg (Polynomial.eval₂RingHom (MvPolynomial.eval y) z) he
  simp only [map_add, map_mul, hEval F, hEval G, hF, hG, zero_mul, add_zero] at h
  change 0 = (Polynomial.C (actualSeedResultant F G)).eval₂ (MvPolynomial.eval y) z at h
  simpa only [Polynomial.eval₂_C] using h.symm
end
end K1_13_4_5
end
section
namespace K1_13_4_2_3_2
noncomputable section
open K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3
open scoped Polynomial BigOperators
private abbrev SourceExp := SeedVar →₀ ℕ
private abbrev JetExp := Fin 3 →₀ ℕ
private abbrev seedMap : Geom[X] →+* GenericSeed := algebraMap _ _
private abbrev constMap : Geom →+* GenericSeed := algebraMap _ _
private theorem seedMap_C (x : Geom) : seedMap (Polynomial.C x) = constMap x :=
  (IsScalarTower.algebraMap_apply Geom Geom[X] GenericSeed x).symm
private def grade (m : SourceExp) : ℕ :=
  m (some 0) + m (some 1) + m (some 2)
private def shiftedExp (m : SourceExp) (k : ℕ) : JetExp :=
  Finsupp.single 0 k + Finsupp.single 1 (m (some 1)) + Finsupp.single 2 (m (some 2))
private theorem shiftedExp_coords (m : SourceExp) (k : ℕ) :
    shiftedExp m k 0 = k ∧ shiftedExp m k 1 = m (some 1) ∧
      shiftedExp m k 2 = m (some 2) := by
  simp [shiftedExp, Finsupp.add_apply]
private theorem exponent_grade (a : Shape) (q : ℕ) (c : Slot a q) :
    exponent a q c 0 + exponent a q c 1 + exponent a q c 2 = q := by
  have h₂ : c.1.val ≤ q :=
    (Nat.le_of_lt_succ c.1.isLt).trans (min_le_left _ _)
  have h₁ : c.2.val ≤ q - c.1.val :=
    (Nat.le_of_lt_succ c.2.isLt).trans (min_le_left _ _)
  change q - c.1.val - c.2.val + c.2.val + c.1.val = q
  omega
private theorem support_bounds {a : Shape} {F : PhysicalRow} (hF : Caps a F)
    {m : SourceExp} (hm : m ∈ F.support) :
    grade m ≤ a.b ∧ m (some 1) + 2 * m (some 2) ≤ a.j ∧
      m (some 2) ≤ a.t ∧ m none ≤ 70000 := by
  have hB := MvPolynomial.le_weightedTotalDegree
    (fun i : SeedVar => i.elim 0 (fun _ => 1)) hm
  have hJ := MvPolynomial.le_weightedTotalDegree
    (fun i : SeedVar => i.elim 0 Fin.val) hm
  have hweight (w : SeedVar → ℕ) :
      Finsupp.weight w m = m none * w none + (m (some 0) * w (some 0) +
        m (some 1) * w (some 1) + m (some 2) * w (some 2)) := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • w i) (fun _ => by simp),
      Fintype.sum_option, Fin.sum_univ_three]
    simp only [smul_eq_mul]
  rw [hweight] at hB hJ
  refine ⟨?_, ?_, (MvPolynomial.monomial_le_degreeOf _ hm).trans hF.2.2.1,
    (MvPolynomial.monomial_le_degreeOf _ hm).trans hF.2.2.2⟩
  · simpa [grade, jetTotal] using hB.trans hF.1
  · simpa [jetIndex, Nat.mul_comm] using hJ.trans hF.2.1
private def seedTerm (z : GenericSeed) (m : SourceExp) (k : ℕ) : GenericSeed :=
  (seedMap Polynomial.X) ^ m none * z ^ (m (some 0) - k) * (m (some 0)).choose k
private theorem centered_monomial (z : GenericSeed) (m : SourceExp) (P : Geom[X]) :
    centered z (MvPolynomial.monomial m P) =
      ∑ k ∈ Finset.range (m (some 0) + 1),
        MvPolynomial.monomial (shiftedExp m k)
          (Polynomial.C (seedTerm z m k) * P.map constMap) := by
  classical
  unfold centered
  rw [MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_option, Fin.prod_univ_three]
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Option.elim,
    ite_true, ite_eq_right (show (1 : Fin 3) ≠ 0 by decide),
    ite_eq_right (show (2 : Fin 3) ≠ 0 by decide)]
  rw [add_pow]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hmon : (MvPolynomial.X (0 : Fin 3) ^ k * MvPolynomial.X 1 ^ m (some 1) *
      MvPolynomial.X 2 ^ m (some 2) : RawRow) =
      MvPolynomial.monomial (shiftedExp m k) 1 := by
    simp only [shiftedExp, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial, mul_one]
  calc
    _ = MvPolynomial.C (Polynomial.C (seedTerm z m k) * P.map constMap) *
        MvPolynomial.monomial (shiftedExp m k) 1 := by
      rw [← hmon]
      simp only [seedTerm, map_mul, map_pow, map_natCast]
      ring
    _ = _ := by rw [MvPolynomial.C_mul_monomial, mul_one]
private theorem centered_coeff (z : GenericSeed) (F : PhysicalRow) (e : JetExp) :
    (centered z F).coeff e =
      ∑ m ∈ F.support, ∑ k ∈ Finset.range (m (some 0) + 1),
        if shiftedExp m k = e then
          Polynomial.C (seedTerm z m k) * (F.coeff m).map constMap
        else 0 := by
  nth_rw 1 [F.as_sum]
  simp only [map_sum, centered_monomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
private theorem centered_admissible (z : GenericSeed) {a : Shape} {F : PhysicalRow}
    (hF : Caps a F) (e : JetExp) (he : e ∈ (centered z F).support) : admissible a e := by
  classical
  by_contra ha
  apply MvPolynomial.mem_support_iff.mp he
  rw [centered_coeff]
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro k hk
  refine ite_eq_right fun h => ha ?_
  subst e
  obtain ⟨h₀, h₁, h₂⟩ := shiftedExp_coords m k
  obtain ⟨hB, hJ, hT, _⟩ := support_bounds hF hm
  simp only [admissible, h₀, h₁, h₂]
  have hk' : k ≤ m (some 0) := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  unfold grade at hB
  exact ⟨by omega, hJ, hT⟩
private def clearedFactor (a : Shape) (N D : Geom[X]) (m : SourceExp) (k : ℕ) :
    Geom[X] :=
  Polynomial.C ((m (some 0)).choose k : Geom) * Polynomial.X ^ m none *
    N ^ (m (some 0) - k) * D ^ (a.b - grade m)
private def clearedMonomial (a : Shape) (α : Geom) (N D : Geom[X]) (i : ℕ)
    (e : JetExp) (m : SourceExp) : Geom[X] →ₗ[Geom] Geom[X] := by
  classical
  exact ∑ k ∈ Finset.range (m (some 0) + 1),
    if shiftedExp m k = e then
      ((Polynomial.lcoeff Geom i).comp (Polynomial.taylor α)).smulRight
        (clearedFactor a N D m k)
    else 0
private def cleared (a : Shape) (α : Geom) (N D : Geom[X]) (q : Fin (a.b + 1)) :
    PhysicalRow →ₗ[Geom] (JetCoeff a q.val → Geom[X]) :=
  LinearMap.pi fun c =>
    (Finsupp.lsum Geom (clearedMonomial a α N D c.1.val (exponent a q.val c.2))).comp
      (AddMonoidAlgebra.coeffLinearEquiv Geom).toLinearMap
private theorem cleared_apply (a : Shape) (α : Geom) (N D : Geom[X])
    (q : Fin (a.b + 1)) (F : PhysicalRow) (c : JetCoeff a q.val) :
    cleared a α N D q F c =
      ∑ m ∈ F.support, ∑ k ∈ Finset.range (m (some 0) + 1),
        if shiftedExp m k = exponent a q.val c.2 then
          ((F.coeff m).taylor α).coeff c.1.val • clearedFactor a N D m k
        else 0 := by
  classical
  change Finsupp.lsum Geom (clearedMonomial a α N D c.1.val (exponent a q.val c.2))
    F.coeff = _
  rw [Finsupp.lsum_apply]
  apply Finset.sum_congr rfl
  intro m _
  change clearedMonomial a α N D c.1.val (exponent a q.val c.2) m (F.coeff m) = _
  unfold clearedMonomial
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : shiftedExp m k = exponent a q.val c.2 <;> simp [h]
private theorem grade_sub {a : Shape} {q : ℕ} {c : Slot a q} {m : SourceExp} {k : ℕ}
    (hB : grade m ≤ a.b) (hk : k ≤ m (some 0))
    (he : shiftedExp m k = exponent a q c) :
    a.b - q = (m (some 0) - k) + (a.b - grade m) := by
  have h := exponent_grade a q c
  rw [← he] at h
  obtain ⟨h₀, h₁, h₂⟩ := shiftedExp_coords m k
  rw [h₀, h₁, h₂] at h
  unfold grade at *
  omega
private theorem cleared_degree {a : Shape} {α : Geom} {N D : Geom[X]}
    (hN : N.natDegree ≤ 1) (hD : D.natDegree ≤ 1) {F : PhysicalRow} (hF : Caps a F)
    (q : Fin (a.b + 1)) (c : JetCoeff a q.val) :
    (cleared a α N D q F c).natDegree ≤ 70000 + (a.b - q.val) := by
  classical
  rw [cleared_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  split
  next he =>
    apply (Polynomial.natDegree_smul_le _ _).trans
    obtain ⟨hB, _, _, hU⟩ := support_bounds hF hm
    have hq := grade_sub hB (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) he
    have hn : (N ^ (m (some 0) - k)).natDegree ≤ m (some 0) - k :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left _ hN)
    have hd : (D ^ (a.b - grade m)).natDegree ≤ a.b - grade m :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left _ hD)
    calc
      _ ≤ (m none + (m (some 0) - k)) + (a.b - grade m) := by
        unfold clearedFactor
        apply Polynomial.natDegree_mul_le.trans
        apply Nat.add_le_add _ hd
        apply Polynomial.natDegree_mul_le.trans
        apply Nat.add_le_add _ hn
        exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le _)
      _ ≤ _ := by omega
  next => simp
private theorem map_clearedFactor (a : Shape) {N D : Geom[X]} (hD : seedMap D ≠ 0)
    (m : SourceExp) (k q : ℕ)
    (hq : a.b - q = (m (some 0) - k) + (a.b - grade m)) :
    seedMap (clearedFactor a N D m k) =
      seedMap D ^ (a.b - q) * seedTerm (seedMap N / seedMap D) m k := by
  simp only [clearedFactor, seedTerm, map_mul, map_pow, map_natCast, hq, pow_add,
    div_pow]
  field_simp [pow_ne_zero _ hD]
private theorem map_cleared {a : Shape} {α : Geom} {N D : Geom[X]} (hD : seedMap D ≠ 0)
    {F : PhysicalRow} (hF : Caps a F) (q : Fin (a.b + 1)) (c : JetCoeff a q.val) :
    seedMap (cleared a α N D q F c) =
      seedMap D ^ (a.b - q.val) *
        localCoeff a α q.val c (centered (seedMap N / seedMap D) F) := by
  classical
  rw [cleared_apply, localCoeff, centered_coeff]
  simp only [map_sum, Polynomial.finsetSum_coeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  by_cases he : shiftedExp m k = exponent a q.val c.2
  · simp only [ite_eq_left he]
    rw [Polynomial.smul_eq_C_mul, map_mul, seedMap_C,
      map_clearedFactor a hD m k q.val
        (grade_sub (support_bounds hF hm).1 (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) he),
      Polynomial.taylor_mul, Polynomial.taylor_C, Polynomial.coeff_C_mul,
      ← Polynomial.map_taylor, Polynomial.coeff_map]
    ring
  · simp [he]
theorem proof : K1_13_4_2_3.c2 := by
  intro a α N D hD hNdeg hDdeg
  have hD' : seedMap D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Geom[X] GenericSeed)).2 hD
  refine ⟨cleared a α N D, fun F hF => ⟨centered_admissible _ hF, ?_⟩⟩
  intro q c
  exact ⟨cleared_degree hNdeg hDdeg hF q c, map_cleared hD' hF q c⟩
end
end K1_13_4_2_3_2
end
section
namespace K1_13_4_2_4
set_option backward.isDefEq.respectTransparency false
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 Polynomial
open scoped Polynomial
@[simp] theorem shiftedBlock_zero (H : Geom[X]) : shiftedBlock H 0 = H := by
  simp [shiftedBlock]
@[simp] theorem shiftedBlock_natDegree (H : Geom[X]) (ε : Geom) :
    (shiftedBlock H ε).natDegree = H.natDegree := Polynomial.natDegree_add_C
theorem shiftedBlock_monic {H : Geom[X]} (hm : H.Monic) (hp : 0 < H.natDegree)
    (ε : Geom) : (shiftedBlock H ε).Monic :=
  hm.add_of_left (degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp hp))
private theorem derivative_ne_zero {Γ s} (P : PoleData Γ s) : P.H.derivative ≠ 0 := by
  let : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  have hcast : (P.H.natDegree : Geom) ≠ 0 := by
    intro hz
    have hp := Nat.le_of_dvd P.small.1
      ((CharP.cast_eq_zero_iff Geom K1.p P.H.natDegree).mp hz)
    change 2130706433 ≤ P.H.natDegree at hp
    have hb := P.small.2
    omega
  intro hz
  let n := P.H.natDegree - 1
  have hn : n + 1 = P.H.natDegree := Nat.sub_add_cancel P.small.1
  have he : P.H.derivative.coeff n = (0 : Geom[X]).coeff n :=
    congrArg (fun f : Geom[X] => f.coeff n) hz
  rw [coeff_derivative, hn, coeff_natDegree, P.monic.leadingCoeff, one_mul, coeff_zero] at he
  apply hcast
  rw [← hn, Nat.cast_add, Nat.cast_one]
  exact he
private theorem amplitude_ne_zero {Γ s} (P : PoleData Γ s) {A : Geom[X]}
    (h : IsCoprime A P.H) : A ≠ 0 := by
  rintro rfl
  exact not_isUnit_of_natDegree_pos _ P.small.1 (isCoprime_zero_left.mp h)
private def forbiddenRootShifts (H A : Geom[X]) : Finset Geom := by
  classical
  exact A.roots.toFinset.image (fun x => -H.eval x)
private theorem coprime_shift {H A : Geom[X]} (hA : A ≠ 0) {ε : Geom}
    (hε : ε ∉ forbiddenRootShifts H A) :
    IsCoprime A (shiftedBlock H ε) := by
  classical
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed Geom Geom _ _).mpr
  intro x
  simp only [Polynomial.coe_aeval_eq_eval]
  by_cases hx : A.eval x = 0
  · right
    intro h
    apply hε
    unfold forbiddenRootShifts
    refine Finset.mem_image.mpr ⟨x, Multiset.mem_toFinset.mpr ((mem_roots hA).mpr hx), ?_⟩
    have he : H.eval x + ε = 0 := by simpa [shiftedBlock] using h
    exact (eq_neg_of_add_eq_zero_right he).symm
  · exact Or.inl hx
theorem goodShifts {Γ s} (P : PoleData Γ s) :
    ∃ bad : Finset Geom, ∀ ε ∉ bad,
      ∃ P' : PoleData ∅ (fun _ : K => (0 : K[X])),
        P'.H = shiftedBlock P.H ε ∧ IsConstantShift P P' ∧
          P'.H.natDegree = P.H.natDegree ∧ P'.H.Separable := by
  classical
  let badFor := forbiddenRootShifts P.H
  let badNodes : Finset Geom := Finset.univ.image (fun i : I => -P.H.eval (embed (node i)))
  refine ⟨(((badFor P.c ∪ badFor P.q) ∪ badFor P.a₀) ∪
    badFor P.H.derivative) ∪ badNodes, ?_⟩
  intro ε hε
  simp only [Finset.mem_union, not_or] at hε
  obtain ⟨⟨⟨⟨hc, hq⟩, ha⟩, hd⟩, hn⟩ := hε
  let H := shiftedBlock P.H ε
  have hsep : H.Separable := by
    rw [Polynomial.separable_def]
    have he : H.derivative = P.H.derivative := by simp [H, shiftedBlock]
    rw [he]
    exact (coprime_shift (derivative_ne_zero P) hd).symm
  let P' : PoleData ∅ (fun _ : K => (0 : K[X])) :=
    { H := H
      monic := shiftedBlock_monic P.monic P.small.1 ε
      small := by simpa [H] using P.small
      nodes := by
        intro i hi
        apply hn
        refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
        have he : P.H.eval (embed (node i)) + ε = 0 := by simpa [H, shiftedBlock] using hi
        exact (eq_neg_of_add_eq_zero_right he).symm
      degree := by simp
      z := P.z
      injective := P.injective
      c := P.c
      q := P.q
      a₀ := P.a₀
      a₁ := P.a₁
      c_unit := coprime_shift (amplitude_ne_zero P P.c_unit) hc
      q_unit := coprime_shift (amplitude_ne_zero P P.q_unit) hq
      a₀_unit := coprime_shift (amplitude_ne_zero P P.a₀_unit) ha
      regular := by simp
      residue := by simp }
  exact ⟨P', rfl, ⟨⟨ε, rfl⟩, rfl, rfl, rfl, rfl⟩, shiftedBlock_natDegree _ _,
    hsep⟩
end
end K1_13_4_2_4
end
section
namespace K1_13_4_2_2_4
open K1_13_4_2_2 Finset
open scoped BigOperators
private def exponent (q k : ℕ) : ℕ :=
  if 5000 - q ≤ k then 7300 - q - k - q else 0
private def powers (q k : ℕ) (i : Fin 6) : ℕ :=
  if i = 4 then exponent q k else 0
private theorem sum_powers (q k : ℕ) (f : Fin 6 → ℤ) :
    (∑ i, (powers q k i : ℤ) * f i) = (exponent q k : ℤ) * f 4 := by
  simp [powers]
private def removed (q k : ℕ) : ℤ :=
  if k < 2300 then capCount q (2299 - k) else 0
private def earlyTerm (q k : ℕ) : ℤ :=
  capCount q 2300 - removed q k
private theorem column_eq {q k : ℕ} (hlo : 1151 ≤ q) (hhi : q ≤ 2300) :
    columnCount q (offset k) = earlyTerm q k := by
  have hd : residualDegree q = q := min_eq_left hhi
  have harg : min (2300 : ℤ) (-offset k - 1) = 2299 - k := by unfold offset; omega
  rw [columnCount, hd, harg, cumulative_eq (by omega) (by omega), earlyTerm, removed]
  by_cases hk : k < 2300
  · rw [ite_eq_left hk, cumulative_eq (by omega) (by omega)]
  · rw [ite_eq_right hk, cumulative, ite_eq_left (by omega)]
private theorem earlyTerm_nonneg {q k : ℕ} (hq : 1151 ≤ q) : 0 ≤ earlyTerm q k := by
  rw [earlyTerm, sub_nonneg, removed]
  by_cases hk : k < 2300
  · rw [ite_eq_left hk, show (2299 : ℤ) - k = ((2299 - k : ℕ) : ℤ) by omega]
    exact capCount_mono (v := 2300) (by omega) (by omega)
  · rw [ite_eq_right hk]
    have h0 : capCount (q : ℤ) 0 = 1 := by
      rw [capCount, max_eq_left (by omega : (0 : ℤ) - q ≤ 0)]
      decide
    have hm := capCount_mono (q := q) (w := 0) (v := 2300) (by decide) (by omega)
    change capCount (q : ℤ) 0 ≤ capCount q 2300 at hm
    omega
private theorem block_le {q k : ℕ} {r : ℤ} (hr : 0 ≤ r)
    (h : columnCount q (offset k) -
        max 0 (max (kernelLower (residualDegree q) (initialFlag q (offset k)))
          (kernelLower (remainingDegree q (powers q k)) (remainingFlag q (offset k) (powers q k)))) ≤ r) :
    (blockBound q (offset k) (powers q k) : ℤ) ≤ r := by
  unfold blockBound
  split
  · simpa using hr
  · have h' := Int.toNat_le_toNat h
    exact (Int.ofNat_le.mpr h').trans_eq (Int.toNat_of_nonneg hr)
private theorem block_le_early {q k : ℕ} (hlo : 1151 ≤ q) (hhi : q ≤ 2300) :
    (blockBound q (offset k) (powers q k) : ℤ) ≤ earlyTerm q k := by
  apply block_le (earlyTerm_nonneg hlo)
  rw [column_eq hlo hhi]
  exact sub_le_self _ (le_max_left _ _)
private def lateTerm (q t : ℤ) : ℤ :=
  if t ≤ q then weightCost t else triangular (q + 1) - weightCost (2 * q - t + 1)
private theorem block_le_late {q j : ℕ} (hlo : 1151 ≤ q) (hhi : q ≤ 2300) (hj : j < 2300) :
    (blockBound q (offset (5000 - q + j)) (powers q (5000 - q + j)) : ℤ) ≤ lateTerm q (2300 - j) := by
  let k := 5000 - q + j
  let t : ℤ := 2300 - j
  let n : ℤ := exponent q k
  change (blockBound q (offset k) (powers q k) : ℤ) ≤ lateTerm q t
  have hn : n = max 0 (t - q) := by
    have h : 5000 - q ≤ k := by dsimp [k]; omega
    simp only [n, exponent, ite_eq_left h]
    dsimp [k, t]
    omega
  have ht : 0 < t ∧ t ≤ 2300 := by dsimp [t]; omega
  have hk : 2300 ≤ k := by dsimp [k]; omega
  have hd : residualDegree q = q := min_eq_left hhi
  have ho : planeOrder q (offset k) = t := by unfold planeOrder offset k t; omega
  have hcol : columnCount q (offset k) = triangular ((q : ℤ) + 1) - weightCost (2 * (q : ℤ) - 2300) := by
    rw [column_eq hlo hhi, earlyTerm, removed, ite_eq_right (not_lt.mpr hk), sub_zero, capCount_full (by omega)]
  have hdeg : remainingDegree q (powers q k) = (q : ℤ) - n := by
    rw [remainingDegree, hd, sum_powers]
    simp [factorDegree, n]
  have hP : remainingFlag q (offset k) (powers q k) 0 = ⟨0, 2300 - k⟩ := by
    simp [remainingFlag, sum_powers, initialFlag, factorFlag, offset]
  have hQ : remainingFlag q (offset k) (powers q k) 1 = ⟨(q : ℤ) - 1150, 2 * (q : ℤ) - 2300⟩ := by
    simp [remainingFlag, sum_powers, initialFlag, factorFlag, hd]
  have hO : remainingFlag q (offset k) (powers q k) 2 = ⟨-n, t - 2 * n⟩ := by
    simp [remainingFlag, sum_powers, initialFlag, factorFlag, ho, n, mul_comm]
  have hP0 : colength ⟨0, 2300 - (k : ℤ)⟩ = 0 := by
    simp [colength, max_eq_left (show (2300 - (k : ℤ) + 1) / 2 ≤ 0 by omega),
      max_eq_left (show 2300 - (k : ℤ) ≤ 0 by omega), triangular]
  have hnet : columnCount q (offset k) -
      kernelLower (remainingDegree q (powers q k)) (remainingFlag q (offset k) (powers q k)) =
      triangular ((q : ℤ) + 1) - triangular ((q : ℤ) - n + 1) + weightCost (t - 2 * n) := by
    rw [hcol, kernelLower, hdeg, ite_eq_right (by omega), Fin.sum_univ_three, hP, hQ, hO, hP0,
      colength_weightCost (by omega) (by omega), colength_weightCost (by omega) (by omega)]
    ring
  have hterm : lateTerm q t =
      triangular ((q : ℤ) + 1) - triangular ((q : ℤ) - n + 1) + weightCost (t - 2 * n) := by
    by_cases h : t ≤ (q : ℤ)
    · have hn0 : n = 0 := by omega
      simp [lateTerm, h, hn0]
    · have hn' : n = t - q := by omega
      rw [lateTerm, ite_eq_right h,
        show (q : ℤ) - n = 2 * (q : ℤ) - t by omega,
        show t - 2 * n = 2 * (q : ℤ) - t by omega]
      linarith only [triangular_sub_weightCost (2 * (q : ℤ) - t)]
  apply block_le
  · rw [hterm]
    exact add_nonneg (sub_nonneg.mpr (triangular_mono (by omega) (by omega))) (weightCost_nonneg (by omega))
  · rw [hterm, ← hnet]
    exact sub_le_sub_left ((le_max_right _ _).trans (le_max_right _ _)) _
private theorem sum_early (q : ℕ) (hhi : q ≤ 2300) :
    6 * (∑ k ∈ range (5000 - q), earlyTerm q k) =
      6 * (5000 - (q : ℤ)) * capCount q 2300 - weightPrefix 2300 + triPrefix (2300 - q) := by
  have hr : (∑ k ∈ range (5000 - q), removed q k) = ∑ k ∈ range 2300, capCount q k := by
    have htrunc : (∑ k ∈ range 2300, removed q k) = ∑ k ∈ range (5000 - q), removed q k := by
      apply sum_subset (range_mono (by omega))
      intro k _ hk
      simp [removed, not_lt.mpr (by simpa only [mem_range, not_lt] using hk : 2300 ≤ k)]
    rw [← htrunc, ← sum_range_reflect (fun k : ℕ => capCount q k) 2300]
    apply sum_congr rfl
    intro k hk
    have hk' := mem_range.mp hk
    rw [removed, ite_eq_left hk']
    exact congrArg (capCount (q : ℤ)) (show (2299 : ℤ) - k = ((2300 - 1 - k : ℕ) : ℤ) by omega)
  have hw := scaled_sum (fun w => weightCost (w + 1)) weightPrefix weightPrefix_step 0 2300
  have ht := scaled_sum (fun w => triangular (max 0 w)) triPrefix triPrefix_step (-(q : ℤ)) 2300
  have hz : triPrefix (-(q : ℤ)) = 0 := by simp [triPrefix]
  simp only [zero_add, show weightPrefix 0 = 0 by decide, sub_zero] at hw
  simp only [hz, sub_zero, neg_add_eq_sub] at ht
  have hc : 6 * (∑ k ∈ range 2300, capCount (q : ℤ) k) =
      weightPrefix 2300 - triPrefix (2300 - q) := by
    simp only [capCount, sum_sub_distrib, mul_sub]
    rw [hw, ht]
    simp only [Nat.cast_ofNat]
  simp only [earlyTerm, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, hr]
  rw [mul_sub, hc, show ((5000 - q : ℕ) : ℤ) = 5000 - q by omega]
  ring
private theorem sum_late (q : ℕ) (hhi : q ≤ 2300) :
    6 * (∑ j ∈ range 2300, lateTerm q (2300 - j)) =
      6 * (2300 - (q : ℤ)) * triangular ((q : ℤ) + 1) + weightPrefix (2 * (q : ℤ) - 2300) := by
  have hr : (∑ j ∈ range 2300, lateTerm q (2300 - j)) =
      ∑ j ∈ range 2300, lateTerm q ((j : ℤ) + 1) := by
    rw [← sum_range_reflect (fun j : ℕ => lateTerm q ((j : ℤ) + 1)) 2300]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    exact congrArg (lateTerm (q : ℤ))
      (show (2300 : ℤ) - j = ((2300 - 1 - j : ℕ) : ℤ) + 1 by omega)
  have hs : (∑ j ∈ range 2300, lateTerm q ((j : ℤ) + 1)) =
      (∑ j ∈ range q, lateTerm q ((j : ℤ) + 1)) +
      ∑ j ∈ range (2300 - q), lateTerm q (((q + j : ℕ) : ℤ) + 1) := by
    conv_lhs => rw [show (2300 : ℕ) = q + (2300 - q) by omega, sum_range_add]
  have ha : (∑ j ∈ range q, lateTerm q ((j : ℤ) + 1)) =
      ∑ j ∈ range q, weightCost ((j : ℤ) + 1) := by
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [lateTerm, ite_eq_left (by omega)]
  have hb : (∑ j ∈ range (2300 - q), lateTerm q (((q + j : ℕ) : ℤ) + 1)) =
      ((2300 - q : ℕ) : ℤ) * triangular ((q : ℤ) + 1) -
        ∑ j ∈ range (2300 - q), weightCost ((q : ℤ) - j) := by
    have hconst : (∑ _j ∈ range (2300 - q), triangular ((q : ℤ) + 1)) =
        ((2300 - q : ℕ) : ℤ) * triangular ((q : ℤ) + 1) := by simp
    rw [← hconst, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    push_cast
    rw [lateTerm, ite_eq_right (by omega)]
    rw [show 2 * (q : ℤ) - ((q : ℤ) + j + 1) + 1 = (q : ℤ) - j by ring]
  have hw := scaled_sum (fun w => weightCost (w + 1)) weightPrefix weightPrefix_step 0 q
  simp only [zero_add, show weightPrefix 0 = 0 by decide, sub_zero] at hw
  rw [hr, hs, ha, hb, mul_add, mul_sub, hw, sum_weight_down]
  rw [show ((2300 - q : ℕ) : ℤ) = 2300 - q by omega,
    show (q : ℤ) - (2300 - q) = 2 * (q : ℤ) - 2300 by ring]
  ring
private def budget (q : ℕ) : ℤ :=
  6 * (5000 - (q : ℤ)) * capCount q 2300 - weightPrefix 2300 + triPrefix (2300 - q) +
    (6 * (2300 - (q : ℤ)) * triangular ((q : ℤ) + 1) + weightPrefix (2 * (q : ℤ) - 2300))
private theorem grade_le {q : ℕ} (hlo : 1151 ≤ q) (hhi : q ≤ 2300) :
    6 * (gradeBound powers q : ℤ) ≤ budget q := by
  have hcut : gradeBound powers q = ∑ k ∈ range (7300 - q), blockBound q (offset k) (powers q k) := by
    symm
    apply sum_subset (range_mono (Nat.sub_le _ _))
    intro k _ hk
    have h : planeOrder q (offset k) ≤ 0 := by unfold planeOrder offset; simp only [mem_range] at hk; omega
    simp [blockBound, h]
  rw [hcut, show 7300 - q = (5000 - q) + 2300 by omega, sum_range_add, Nat.cast_add,
    Nat.cast_sum, Nat.cast_sum, mul_add, budget, ← sum_early q hhi, ← sum_late q hhi]
  apply add_le_add <;> apply mul_le_mul_of_nonneg_left _ (by decide) <;> apply sum_le_sum
  · intro k _
    exact block_le_early (k := k) hlo hhi
  · intro j hj
    exact block_le_late hlo hhi (mem_range.mp hj)
private def total : ℕ → ℤ
  | 0 => 0
  | n + 1 => total n + budget (1151 + n)
private theorem total_eq (n : ℕ) :
    (∑ j ∈ range n, budget (1151 + j)) = total n := by
  induction n with
  | zero => simp [total]
  | succ n ih => rw [sum_range_succ, ih, total]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem total_check : total 1149 = 24493805604150 := by decide +kernel
theorem proof : K1_13_4_2_2.c4 := by
  refine ⟨powers, ?_⟩
  have h := sum_le_sum (s := range 1149) (fun j hj =>
    grade_le (q := 1151 + j) (by omega) (by have := mem_range.mp hj; omega))
  rw [← mul_sum, total_eq, total_check, ← Nat.cast_sum] at h
  omega
end K1_13_4_2_2_4
end
section
namespace K1_13_4_2_4
set_option backward.isDefEq.respectTransparency false
noncomputable section
open K1_13 K1_13_4 K1_13_4_2 Polynomial
open scoped Polynomial BigOperators
def c1 : Prop :=
  ∀ (H c q a₀ a₁ : Geom[X]), H.Monic → 0 < H.natDegree →
    ∃ (N : ShiftSeed[X]) (D : ShiftSeed), ∀ ε : Geom,
      IsCoprime c (shiftedBlock H ε) → IsCoprime a₀ (shiftedBlock H ε) →
      RegularResidue H c q a₀ a₁ N D ε
def c2 : Prop :=
  ∀ (H : Geom[X]), H.Monic → 0 < H.natDegree → ∀ (N : ShiftSeed[X]) (D : ShiftSeed)
    (n m : ℕ) (F : Fin m → PhysicalRow),
    ∃ (k : ℕ) (M : Matrix (Fin k) (Fin m) Geom[X]),
      ∀ (ε : Geom), specializeShift ε D ≠ 0 → ∀ v : Fin m → Geom,
        (M.map (evalRingHom ε)).mulVecLin v = 0 ↔
          (MvPolynomial.C (liftX (shiftedBlock H ε))) ^ n ∣
            restoreWith (shiftedBlock H ε) (residueAtShift N D ε) (∑ j, v j • F j)
private theorem rank_at_zero_le {E : Type*} [Field E] [Infinite E] {k m : ℕ}
    (M : Matrix (Fin k) (Fin m) E[X]) (bad : Finset E) (r : ℕ)
    (h : ∀ ε ∉ bad, (M.map (evalRingHom ε)).rank ≤ r) :
    (M.map (evalRingHom 0)).rank ≤ r := by
  classical
  let B := M.map (evalRingHom 0)
  let d := B.rank
  obtain ⟨ι, col, hinj, hspan, hind⟩ := exists_linearIndependent' E B.col
  let : Finite ι := Finite.of_injective col hinj
  let : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = d := by
    rw [← finrank_span_eq_card hind, hspan, ← Matrix.rank_eq_finrank_span_cols]
  let e : Fin d ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let cols : Fin d → Fin m := col ∘ e
  have hli : LinearIndependent E (fun j => B.col (cols j)) := hind.comp e e.injective
  obtain ⟨rows, hdet⟩ :=
    FrobeniusLocator.GenericRank.exists_rows_det_ne_zero (B.submatrix id cols) (by
      intro v hv
      have hsum : (∑ j, v j • B.col (cols j)) = 0 := by
        funext i
        simpa only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq, Matrix.col,
          Matrix.transpose_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm,
          Pi.zero_apply] using congrFun hv i
      funext j
      exact Fintype.linearIndependent_iff.mp hli v hsum j)
  let T := M.submatrix rows cols
  have hT : T.det ≠ 0 := by
    intro hz
    apply hdet
    change ((evalRingHom (0 : E)).mapMatrix T).det = 0
    rw [← (evalRingHom (0 : E)).map_det, hz, map_zero]
  obtain ⟨ε, hε⟩ := Infinite.exists_notMem_finset (bad ∪ T.det.roots.toFinset)
  rw [Finset.mem_union, not_or] at hε
  have ht : (T.map (evalRingHom ε)).det ≠ 0 := by
    change ((evalRingHom ε).mapMatrix T).det ≠ 0
    rw [← (evalRingHom ε).map_det]
    exact fun hz => hε.2 (Multiset.mem_toFinset.mpr ((mem_roots hT).mpr hz))
  have hr := Matrix.rank_submatrix_le (M.map (evalRingHom ε)) rows cols
  change (T.map (evalRingHom ε)).rank ≤ _ at hr
  rw [Matrix.rank_of_det_ne_zero ht, Fintype.card_fin] at hr
  exact hr.trans (h ε hε.1)
private theorem residue_unique {Γ : Finset K1.K} {s : K1.K → K1.K[X]}
    (P : PoleData Γ s) (L : ResidueChart P) {N : ShiftSeed[X]} {D : ShiftSeed}
    (h : RegularResidue P.H P.c P.q P.a₀ P.a₁ N D 0) :
    residueAtShift N D 0 = genericResidue L.numerator L.denominator := by
  let A := residueMultiplier P.c P.a₀ P.a₁
  let R := residueAtShift N D 0
  let S := genericResidue L.numerator L.denominator
  let H := liftX P.H
  have hR : H ∣ A * R + residueOffset P.q := by
    simpa only [shiftedBlock_zero] using h.generic_congruence
  have hS : H ∣ A * S + residueOffset P.q := L.generic_congruence
  have hsub : H ∣ R - S := by
    have hu : IsCoprime A H := L.generic_unit
    apply hu.symm.dvd_of_dvd_mul_left
    simpa only [add_sub_add_right_eq_sub, ← mul_sub] using dvd_sub hR hS
  have hH : H.natDegree = P.H.natDegree := P.monic.natDegree_map _
  have hRdeg : R.natDegree < H.natDegree := by
    rw [hH]
    exact ((natDegree_C_mul_le _ _).trans natDegree_map_le).trans_lt
      (by simpa only [shiftedBlock_zero] using h.small)
  have hSdeg : S.natDegree < H.natDegree := by
    rw [hH]
    exact ((natDegree_C_mul_le _ _).trans natDegree_map_le).trans_lt L.small
  apply sub_eq_zero.mp
  by_contra hz
  exact (not_le_of_gt ((natDegree_sub_le _ _).trans_lt (max_lt hRdeg hSdeg)))
    (natDegree_le_of_dvd hsub hz)
private theorem codim_eq_rank (V W : Submodule Geom PhysicalRow) [Module.Finite Geom V]
    {k m : ℕ} (B : Module.Basis (Fin m) Geom V) (M : Matrix (Fin k) (Fin m) Geom)
    (h : ∀ v, M.mulVecLin v = 0 ↔ (B.equivFun.symm v : PhysicalRow) ∈ W) :
    codimIn V W = M.rank := by
  let f := M.mulVecLin.comp B.equivFun.toLinearMap
  have hker : f.ker = W.comap V.subtype := by
    ext x
    simpa [f, LinearMap.mem_ker] using h (B.equivFun x)
  have hrange : f.range = M.mulVecLin.range :=
    LinearMap.range_comp_of_range_eq_top _ B.equivFun.range
  have hk := Submodule.finrank_map_subtype_eq V f.ker
  rw [hker, Submodule.map_comap_subtype] at hk
  have hd := LinearMap.finrank_range_add_finrank_ker (K := Geom) (V := ↥V)
    (V₂ := Fin k → Geom) f
  rw [hrange, ← Matrix.rank, hker, ← hk] at hd
  unfold codimIn
  omega
private theorem restore_eq {Γ : Finset K1.K} {s : K1.K → K1.K[X]}
    (P : PoleData Γ s) (L : ResidueChart P) (F : PhysicalRow) :
    restore P L F = restoreWith P.H (genericResidue L.numerator L.denominator) F := rfl
theorem of_children (h1 : c1) (h2 : c2) : K1_13_4_2.c4 := by
  classical
  intro Γ s P L a V r hV hbound
  let : Module.Finite Geom V := hV
  obtain ⟨N, D, hres⟩ := h1 P.H P.c P.q P.a₀ P.a₁ P.monic P.small.1
  let : Module.Free Geom ↥V := Module.Free.of_divisionRing (K := Geom) (V := ↥V)
  let B := Module.finBasis Geom ↥V
  let F := fun j => (B j : PhysicalRow)
  obtain ⟨k, M, hM⟩ := h2 P.H P.monic P.small.1 N D (a.b + a.j) (Module.finrank Geom V) F
  have hmatch {Γ' : Finset K1.K} {s' : K1.K → K1.K[X]}
      (P' : PoleData Γ' s') (L' : ResidueChart P') (ε : Geom)
      (hd : specializeShift ε D ≠ 0) (hh : P'.H = shiftedBlock P.H ε)
      (hr : genericResidue L'.numerator L'.denominator = residueAtShift N D ε) :
      codimIn V (poleCondition P' L' a (liftX P'.H)) = (M.map (evalRingHom ε)).rank := by
    apply codim_eq_rank _ _ B
    intro v
    have hv : (B.equivFun.symm v : PhysicalRow) = ∑ j, v j • F j := by
      rw [B.equivFun_symm_apply]
      simp [F]
    rw [mem_poleCondition, restore_eq, hh, hr, hv]
    exact hM ε hd v
  have hz := hres 0 (by simpa using P.c_unit) (by simpa using P.a₀_unit)
  have hd {ε} (hz : (specializeShift ε D).eval 0 ≠ 0) : specializeShift ε D ≠ 0 :=
    fun he => hz (by rw [he, eval_zero])
  rw [hmatch P L 0 (hd hz.at_zero) (shiftedBlock_zero _).symm (residue_unique P L hz).symm]
  obtain ⟨bad, hbad⟩ := goodShifts P
  apply rank_at_zero_le M bad r
  intro ε hε
  obtain ⟨P', hh, hs, hdeg, hsep⟩ := hbad ε hε
  obtain ⟨hc, hq, ha₀, ha₁⟩ := hs.2
  have hc' : IsCoprime P.c (shiftedBlock P.H ε) := by rw [← hc, ← hh]; exact P'.c_unit
  have ha' : IsCoprime P.a₀ (shiftedBlock P.H ε) := by rw [← ha₀, ← hh]; exact P'.a₀_unit
  have h' := hres ε hc' ha'
  let L' : ResidueChart P' :=
    { numerator := N.map (specializeShift ε)
      denominator := specializeShift ε D
      at_zero := h'.at_zero
      small := by rw [hh]; exact h'.small
      generic_unit := by rw [hc, ha₀, ha₁, hh]; exact h'.generic_unit
      generic_congruence := by rw [hc, ha₀, ha₁, hq, hh]; exact h'.generic_congruence
      regular := by simp
      quotient := by simp }
  rw [← hmatch P' L' ε (hd h'.at_zero) hh rfl]
  exact hbound P' L' hs hdeg hsep
end
end K1_13_4_2_4
end
section
namespace K1_13_4_5
noncomputable section
open K1 K1_13 K1_13_4
open scoped Polynomial BigOperators
def c2 : Prop :=
  ∀ F G : GenericRow,
    (actualSeedResultant F G).totalDegree ≤
      seedDegree G * jetTotal F + seedDegree F * jetTotal G ∧
    lowerIndex (actualSeedResultant F G) ≤
      seedDegree G * jetIndex F + seedDegree F * jetIndex G
end
end K1_13_4_5
end
section
namespace K1_13_7_3
def LowPowers (P : K1_13_4.Lower) (threshold : ℕ) : Prop :=
  ∀ f : K1_13_4.Lower, Prime f → ¬ f ^ threshold ∣ P
end K1_13_7_3
end
section
namespace K1_13_4_2_1
open K1_13_4 K1_13_4_2
open scoped BigOperators
@[simp] theorem box_index (b : Bank) : b.box.j = 2300 := by
  cases b <;> rfl
@[simp] theorem box_top (b : Bank) : b.box.t = 1150 := by
  cases b <;> rfl
def jetSum {M : Type*} [AddCommMonoid M] (B : ℕ) (f : ℕ → ℕ → ℕ → M) : M :=
  ∑ q ∈ Finset.range (B + 1), ∑ k ∈ Finset.range (min q 1150 + 1),
    ∑ l ∈ Finset.range (min (q - k) (2300 - 2 * k) + 1), f q k l
def rawBase (b : Bank) : ℕ := b.cut + 1 - 131071 * b.box.b
def width (b : Bank) (h q k l : ℕ) : ℕ :=
  rawBase b + 131071 * (b.box.b - q) + (l + 2 * k) + (2300 + (b.box.b - q)) * h
end K1_13_4_2_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3R_3
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
def cutIdeal (q : Surface) (P : Jet) : Ideal Jet :=
  q.asIdeal ⊔ Ideal.span {P}
def seedInclusion : Seeds →+* Jet :=
  (Polynomial.C : Equation →+* Jet).comp Polynomial.C
def seedIdeal (R : Ideal Jet) : Ideal Seeds :=
  R.comap seedInclusion
def HasSeedEquation (R : Ideal Jet) (f : Seeds) : Prop :=
  f ≠ 0 ∧ seedIdeal R = Ideal.span {f}
def seedPointEval (t : FX × FX) : Seeds →+* FX :=
  MvPolynomial.eval ![t.1, t.2]
def HasSeedPoint (R : Ideal Jet) (t : FX × FX) : Prop :=
  seedIdeal R = RingHom.ker (seedPointEval t)
def markPoint (z : K) : FX × FX :=
  (seedEmbedding z, seedEmbedding z ^ p)
inductive Line where
  | seed
  | jet
def lineEquation : Line → SectionJet
  | .seed =>
    let t₀ : SectionJet := C (C (MvPolynomial.X 0))
    let t₁ : SectionJet := C (C (MvPolynomial.X 1))
    t₀ + sectionScalar 0 * t₁ - sectionScalar 2
  | .jet =>
    let y : SectionJet := C (R := Polynomial SectionSeeds) (Polynomial.X (R := SectionSeeds))
    let v : SectionJet := Polynomial.X (R := Polynomial SectionSeeds)
    y + sectionScalar 1 * v - sectionScalar 3
abbrev LineSection (I : Ideal Jet) (l : Line) :=
  SectionJet ⧸ (I.map sectionMap ⊔ Ideal.span {lineEquation l})
def lineLength (I : Ideal Jet) (l : Line) : ℕ :=
  Module.finrank SectionField (LineSection I l)
end
end K1_14_3R_3
end
section
namespace K1_13_3
noncomputable section
open Polynomial K1 K1_13
abbrev terminal : ℕ := 3000 * 180265 - 1
abbrev layerWidth : ℕ := 46597
def requiredOrder (T : ℕ) : ℕ :=
  (terminal - T) / layerWidth + 1
def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) ⟨4012, 1650, 550⟩ ∧ TrueWeightLE P T ∧ Contact w P
abbrev Symbol := MvPolynomial (Fin 4) Geom
def symbolAt (x : Geom) : Row 4 →+* Symbol :=
  MvPolynomial.map (Polynomial.evalRingHom x)
def symbolIndex (P : Symbol) : ℕ :=
  P.support.sup (fun m => m.sum (fun i a => i.val * a))
end
end K1_13_3
end
