import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Data.ENat.BigOperators
import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import ProximityPrize.SubmissionLower.Fast007
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Pack_K1_13_6_1_4Geometry
set_option Elab.async false

section PackSource_K1_14Defs
set_option autoImplicit true
namespace K1_14

noncomputable section

open K1 Polynomial
open scoped BigOperators

abbrev L := AlgebraicClosure K
abbrev FX := FractionRing L[X]
abbrev Seeds := MvPolynomial (Fin 2) FX
abbrev Equation := Polynomial Seeds

def liftPoly (g : K[X]) : L[X] := g.map (algebraMap K L)
def atX (g : K[X]) : FX := algebraMap L[X] FX (liftPoly g)

def seedEmbedding : K →+* FX :=
  (algebraMap L[X] FX).comp ((Polynomial.C : L →+* L[X]).comp (algebraMap K L))

def graphEval (z : K) : Seeds →+* FX :=
  MvPolynomial.eval ![seedEmbedding z, (seedEmbedding z) ^ p]

def atMark (f : Equation) (z : K) (S : K[X]) : FX :=
  f.eval₂ (graphEval z) (atX S)

/-- The second block and all its residue data are coefficient conjugates
of the first, with the same polynomial ordinate on both blocks. -/
def AdjacentChart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : L[X]) : Prop :=
  let σ := frobenius L p
  let H' := H.map σ
  H.Monic ∧ H.natDegree = M.overhead.toNat ∧ H ∣ liftPoly M.E ∧
  H'.Monic ∧ H'.natDegree = M.overhead.toNat ∧ H' ∣ liftPoly (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i, H.eval (algebraMap K L (node i)) ≠ 0 ∧ H'.eval (algebraMap K L (node i)) ≠ 0) ∧
  IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H ∧
  IsCoprime ((liftPoly (M.Q * M.factor * M.A₀)).map σ) H' ∧
  ∀ γ ∈ Γ,
    let z := algebraMap K L (M.label γ)
    let D := liftPoly (M.factor * M.amplitude γ)
    let S := liftPoly (F.scalar γ)
    IsCoprime D H ∧ IsCoprime (D.map σ) H' ∧
    H ∣ D * S + C z * liftPoly M.Q ∧
    H' ∣ D.map σ * S + C (z ^ p) * (liftPoly M.Q).map σ

/-- Outer variable V is the true derivative, inner variable Y the true value. -/
abbrev Jet := Polynomial Equation

structure Shape where
  m : ℕ
  B : ℕ
  J : ℕ
  U : ℕ
  deriving DecidableEq

structure Band where
  endpoint : ℕ
  yBound : ℕ
  seedBound : ℕ
  multiplicity : ℕ
  jetBound : ℕ
  vBound : ℕ
  subbankSeeds : ℕ

/-- The smaller seed caps belong to the last full bank in each schedule. -/
def band (w : ℤ) : Band :=
  if w ≤ 3554 then ⟨3554, 5, 144, 836, 1164, 247, 19371⟩
  else if w ≤ 8249 then ⟨8249, 4, 98, 358, 500, 105, 6798⟩
  else if w ≤ 23999 then ⟨23999, 4, 47, 358, 500, 105, 4860⟩
  else ⟨32680, 4, 36, 358, 500, 105, 3913⟩

def SeedBound (f : Equation) (b : ℕ) : Prop :=
  ∀ i, (f.coeff i).totalDegree ≤ b

def ReducedEquation (w : ℤ) (f : Equation) : Prop :=
  0 < f.natDegree ∧ f.natDegree ≤ (band w).yBound ∧ f.IsPrimitive ∧
    (f.map (algebraMap Seeds (FractionRing Seeds))).Separable

def triangle (U : ℕ) : ℕ := (U + 1) * (U + 2) / 2

def slots (U spent : ℕ) : ℕ :=
  if spent ≤ U then triangle (U - spent) else 0

abbrev Banks := Shape → ℕ → Submodule FX Jet

def shapeSum (s : Shape) (g : ℕ → ℕ → ℕ) : ℕ :=
  ∑ q ∈ Finset.range (s.B+1), ∑ j ∈ Finset.range (min q s.J+1), g q j

def sourceDebit (h : ℕ) (s : Shape) : ℕ :=
  triangle s.U * 262144 * shapeSum s (fun q i => s.m + min q s.J - (q + 2*i)) +
    2*h*(s.U+1)*shapeSum s (fun q _ => (s.B+s.J-q)*(s.B-q))

def terminalShape (w : ℤ) : Shape :=
  let b := band w
  ⟨b.multiplicity, b.jetBound, b.vBound, b.subbankSeeds⟩

def rawWidth (w : ℤ) (q j : ℕ) : ℕ :=
  (band w).multiplicity * 180265 + j - q * (131071 - w.toNat)

def rawVolume (w : ℤ) : ℕ :=
  triangle (band w).subbankSeeds * shapeSum (terminalShape w) (rawWidth w)

/-- The physical and full primary-pole debits in the M9 dimension floor. -/
def subbankDebit (w : ℤ) : ℕ := sourceDebit w.toNat (terminalShape w)

def forcedPower (w : ℤ) (W j : ℕ) : ℕ :=
  1 + ((band w).multiplicity * 180265 - 1 - W) / (2 * w.toNat) - j

/-- Simultaneous divisibility on the retained surfaces. It applies to every
nonzero row of the *same* smaller terminal bank. -/
def TerminalDivisibility (w : ℤ) (rows : Banks) (f : Equation) : Prop :=
  ∀ W < (band w).multiplicity * 180265, ∀ P ∈ rows (terminalShape w) W, P ≠ 0 →
    f ^ forcedPower w W P.natDegree ∣ P.leadingCoeff

/-- Only the filtered dimensions and their highest V coefficients enter the
seed-degree contradiction. The coefficient field contains the generic X. -/
def TerminalMass (w : ℤ) (f : Equation) : Prop :=
  let b := band w
  ∃ V : ℕ → Submodule FX Jet,
    rawVolume w ≤ subbankDebit w +
      ∑ W ∈ Finset.range (b.multiplicity * 180265), Module.finrank FX (V W) ∧
    ∀ W < b.multiplicity * 180265, ∀ P ∈ V W, P ≠ 0 →
      let j := P.natDegree
      let i := P.leadingCoeff.natDegree
      j ≤ b.vBound ∧ i+j ≤ b.jetBound ∧ (i+j)*(131071-w.toNat) ≤ W+j ∧
        SeedBound P.leadingCoeff b.subbankSeeds ∧ f ^ forcedPower w W j ∣ P.leadingCoeff

/-- Left sum of the strict test (T), with index r = l-1 in PAIR-CLOSURE. -/
def seedGain (w : ℤ) : ℕ :=
  let b := band w
  let U := b.subbankSeeds
  let v := b.seedBound + 1
  shapeSum (terminalShape w) fun q j => ∑ r ∈ Finset.range (U / v + 1),
    (slots U (r*v) - slots U ((r+1)*v)) * (rawWidth w q j - 2*w.toNat*(j+r))

/-- Exact integer ceiling of the simple-root Taylor/word charge, using
the indicated upper degree throughout the same height band. -/
def simplePrice (w : ℤ) : ℕ :=
  let b := band w
  let d := 131071 + b.endpoint
  let gap := 180265 - d
  let T := 2*d-1
  let a := 1+T*(b.yBound-1)
  let B := T*b.seedBound
  let D := b.yBound*B^2 + 2*b.seedBound*a*B
  (81879*(81879/gap+1)*D + (gap-1)) / gap + b.yBound

def singularDegree (w : ℤ) : ℕ :=
  (2*(band w).yBound-1)*(band w).seedBound

/-- Cheap/layered pairs in reserve order, then the final full bank and its
smaller seed-degree subbank. -/
def scheduled (w : ℤ) : List Shape :=
  let sub := terminalShape w
  if w ≤ 3554 then
    [⟨59,82,18,1899⟩, ⟨136,190,40,8441⟩, ⟨66,92,21,2076⟩, ⟨150,210,44,9356⟩,
     ⟨73,102,23,2261⟩, ⟨164,229,48,10272⟩, ⟨80,112,25,2455⟩, ⟨178,249,52,11191⟩,
     ⟨94,131,30,2824⟩, ⟨213,298,62,12959⟩, ⟨115,160,36,3401⟩, ⟨262,366,77,15611⟩,
     ⟨136,190,43,4204⟩, ⟨325,454,96,19187⟩, ⟨178,248,56,5332⟩, ⟨409,572,121,24615⟩,
     ⟨241,336,78,7235⟩, ⟨570,797,169,33523⟩, ⟨325,453,104,9976⟩, ⟨759,1061,224,46271⟩,
     ⟨836,1164,247,273617⟩, sub]
  else
    [⟨45,63,14,812⟩, ⟨84,118,24,2907⟩, ⟨57,80,18,1041⟩, ⟨114,160,33,3775⟩,
     ⟨81,114,26,1383⟩, ⟨144,203,42,5064⟩, ⟨123,173,40,2173⟩, ⟨231,325,67,8061⟩,
     ⟨358,500,105,66251⟩, sub]

def jetAt (P : Jet) (z : K) (S : K[X]) : FX :=
  P.eval₂ (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)

/-- Translate just the i-th formal seed by a new indeterminate. -/
def translateSeed (i : Fin 2) : Seeds →+* Polynomial Seeds :=
  MvPolynomial.eval₂Hom (C.comp MvPolynomial.C)
    (fun j => C (MvPolynomial.X j : Seeds) + if j = i then Polynomial.X (R := Seeds) else 0)

/-- Hasse coefficient at fixed true Y,V. -/
def seedHasse (i : Fin 2) (r : ℕ) (P : Jet) : Jet :=
  P.sum fun j g => monomial j (g.sum fun k c => monomial k ((translateSeed i c).coeff r))

/-- A single collection of evaluated filtered spaces over L(X). The rank
floor is telescoped over all cutoffs, not a rank claim at one fibre. -/
structure JetSource {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (rows : Banks) : Prop where
  nested : ∀ s ∈ scheduled M.overhead, ∀ s' ∈ scheduled M.overhead,
    s.m = s'.m → s.B = s'.B → s.J = s'.J → s.U ≤ s'.U →
    ∀ W W', W ≤ W' → rows s W ≤ rows s' W'
  necessary : ∀ s ∈ scheduled M.overhead, ∀ W, W < s.m*180265 → ∀ P ∈ rows s W,
    ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0
  shape : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, ∀ j i,
    ((P.coeff j).coeff i) ≠ 0 →
      i+j ≤ s.B ∧ j ≤ s.J ∧ ((P.coeff j).coeff i).totalDegree ≤ s.U
  leading : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, P ≠ 0 →
    (P.leadingCoeff.natDegree + P.natDegree)*(131071-M.overhead.toNat) ≤ W + P.natDegree
  shift : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, ∀ i r,
    seedHasse i r P ∈ rows s (W + 2*M.overhead.toNat*r)
  floor_bound : ∀ s ∈ scheduled M.overhead, ∀ W, W < s.m*180265 →
    (∀ q ≤ s.B, ∀ j ≤ min q s.J, q*(131071-M.overhead.toNat) ≤ W+1+j) →
    triangle s.U * shapeSum s (fun q j => W+1+j - q*(131071-M.overhead.toNat)) ≤
      sourceDebit M.overhead.toNat s + ∑ t ∈ Finset.range (W+1), Module.finrank FX (rows s t)

/-- The complement of the first-loss book satisfies a single reduced equation
in the original seed chart. The empty retained case needs no equation. -/
def PrefixCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) (rows : Banks) : Prop :=
  Γ.card ≤ highPrefix M.overhead ∨
    ∃ kept ⊆ Γ, (Γ \ kept).card ≤ highPrefix M.overhead ∧
      ∃ f : Equation, ReducedEquation M.overhead f ∧ TerminalDivisibility M.overhead rows f ∧
        ∀ γ ∈ kept, atMark f (M.label γ) (F.scalar γ) = 0

end
end K1_14
end PackSource_K1_14Defs

section PackSource_K1_14Separant
set_option autoImplicit true
namespace K1_14

noncomputable section

open K1 Polynomial
open scoped BigOperators

/-- Each term of the determinant uses one entry from each column. -/
private theorem det_degree {n b : ℕ} (A : Matrix (Fin n) (Fin n) Seeds)
    (h : ∀ i j, (A i j).totalDegree ≤ b) : A.det.totalDegree ≤ n*b := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro π _
  have hp : (∏ i, A (π i) i).totalDegree ≤ n*b := by
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    calc
      _ ≤ ∑ _i : Fin n, b := Finset.sum_le_sum fun i _ => h (π i) i
      _ = _ := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hh | hh <;> simpa [hh] using hp

private theorem resultant_degree {m n b : ℕ} {f g : Equation}
    (hf : SeedBound f b) (hg : SeedBound g b) :
    (f.resultant g m n).totalDegree ≤ (m+n)*b := by
  apply det_degree
  intro i j
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
    split
    · apply hg
    · simp
  · intro k
    simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
    split
    · apply hf
    · simp

private theorem derivative_seedBound {f : Equation} {b : ℕ} (hf : SeedBound f b) :
    SeedBound f.derivative b := by
  intro i
  rw [coeff_derivative]
  have hc : (↑i + 1 : Seeds) = MvPolynomial.C (↑i + 1 : FX) := by simp
  rw [hc]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simpa only [MvPolynomial.totalDegree_C, Nat.add_zero] using hf (i+1)

/-- A single nonzero polynomial in the formal seeds vanishes whenever the
specialized actual ordinate is a common root of f and its Y derivative. -/
theorem separant_certificate {w : ℤ} {f : Equation} (hf : ReducedEquation w f)
    (hs : SeedBound f (band w).seedBound) :
    ∃ Δ : Seeds, Δ ≠ 0 ∧ Δ.totalDegree ≤ singularDegree w ∧
      ∀ (z : K) (S : K[X]), atMark f z S = 0 → atMark f.derivative z S = 0 →
        graphEval z Δ = 0 := by
  obtain ⟨hpos, hy, _, hsep⟩ := hf
  let ι := algebraMap Seeds (FractionRing Seeds)
  have hi := IsFractionRing.injective Seeds (FractionRing Seeds)
  have hcop : IsCoprime (f.map ι) (f.derivative.map ι) := by
    simpa only [Separable, ← derivative_map] using hsep
  have hne := resultant_ne_zero _ _ hcop
  rw [natDegree_map_eq_of_injective hi, natDegree_map_eq_of_injective hi,
    resultant_map_map] at hne
  refine ⟨f.resultant f.derivative, fun h => hne (by simp [h]), ?_, ?_⟩
  · apply (resultant_degree hs (derivative_seedBound hs)).trans
    apply Nat.mul_le_mul_right
    have := natDegree_derivative_le f
    omega
  · intro z S hzero hder
    obtain ⟨a, b, _, _, hbez⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative
      (le_refl _) (le_refl _) (Or.inl hpos.ne')
    have ev := congrArg (eval₂RingHom (graphEval z) (atX S)) hbez
    change f.eval₂ _ _ = 0 at hzero
    change f.derivative.eval₂ _ _ = 0 at hder
    simpa [eval₂_add, eval₂_mul, hzero, hder] using ev.symm

theorem singular_degree_lt (w : ℤ) : singularDegree w < p := by
  unfold singularDegree band
  split_ifs <;> decide

/-- Count original labels by injecting the translated labels into the
coefficient field and applying the low-degree Frobenius-graph root bound. -/
theorem singular_count {u del} (M : AnchorModel u del) {w : ℤ} {f : Equation}
    (hf : ReducedEquation w f) (hs : SeedBound f (band w).seedBound)
    (Γ : Finset K) (S : K → K[X])
    (hroot : ∀ γ ∈ Γ, atMark f (M.label γ) (S γ) = 0)
    (hsing : ∀ γ ∈ Γ, atMark f.derivative (M.label γ) (S γ) = 0) :
    Γ.card ≤ (p+1)*singularDegree w := by
  classical
  obtain ⟨Δ, hne, hdegree, hz⟩ := separant_certificate hf hs
  let emb : K ↪ FX :=
    ⟨fun γ => seedEmbedding (M.label γ), fun a b h =>
      sub_left_inj.mp (seedEmbedding.injective h)⟩
  have hb := frobenius_coefficient_exception_count p (singularDegree w) (singularDegree w)
    (by decide) Δ hne ((Δ.degreeOf_le_totalDegree 0).trans hdegree)
    (singular_degree_lt w) ((Δ.degreeOf_le_totalDegree 1).trans hdegree)
    (Γ.map emb) (by
      intro x hx
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_map.mp hx
      exact hz _ _ (hroot γ hγ) (hsing γ hγ))
  simpa only [Finset.card_map, Nat.add_mul, Nat.one_mul, Nat.add_comm (singularDegree w)]
    using hb

/-- Kernel reductions of the four endpoint tariffs. -/
theorem retained_price (w : ℤ) :
    (p+1)*singularDegree w + simplePrice w = highRetained w := by
  unfold singularDegree simplePrice band highRetained
  split_ifs <;> decide

end
end K1_14
end PackSource_K1_14Separant

section PackSource_K1_14Chart
set_option autoImplicit true
namespace K1_14

noncomputable section

open K1 Polynomial

/-- Select a submultiset of all roots, keeping their primary multiplicities. -/
theorem trim (P : L[X]) (h : ℕ) (hh : h ≤ P.natDegree) :
    ∃ H : L[X], H.Monic ∧ H.natDegree = h ∧ H ∣ P := by
  classical
  have hc : 0 < (P.roots.powersetCard h).card := by
    rw [Multiset.card_powersetCard, IsAlgClosed.card_roots_eq_natDegree]
    exact Nat.choose_pos hh
  obtain ⟨s, hs⟩ := Multiset.card_pos_iff_exists_mem.mp hc
  obtain ⟨hle, hsize⟩ := Multiset.mem_powersetCard.mp hs
  exact ⟨_, monic_multisetProd_X_sub_C s, (natDegree_multiset_prod_X_sub_C_eq_card s).trans hsize,
    (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)).trans P.prod_multiset_X_sub_C_dvd⟩

theorem twist_lift (P : K[X]) :
    liftPoly (P.map twist) = (liftPoly P).map (frobenius L p) := by
  simp only [liftPoly, Polynomial.map_map, twist, RingHom.frobenius_comm]

/-- The two projectivities use the original translated label and its
Frobenius, and impose divisibility on the same scalar polynomial. -/
theorem adjacent_chart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) :
    ∃ H, AdjacentChart M F H := by
  let φ := algebraMap K L
  let σ := frobenius L p
  have hsmall : M.overhead.toNat ≤ (liftPoly M.E).natDegree := by
    rw [liftPoly, natDegree_map]
    unfold AnchorModel.overhead
    omega
  obtain ⟨H, hm, hdeg, hd⟩ := trim _ _ hsmall
  have hd' : H.map σ ∣ liftPoly (M.E.map twist) := by
    rw [twist_lift]
    exact Polynomial.map_dvd σ hd
  have hcop : IsCoprime H (H.map σ) := by
    have ha := M.adjacent_coprime.map (Polynomial.mapRingHom φ)
    exact (ha.of_isCoprime_of_dvd_left hd).of_isCoprime_of_dvd_right hd'
  have hunit : IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H :=
    (((M.offset_reduced.mul_left M.coprime_factor.symm).mul_left M.first_amplitude_unit).map
      (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
  refine ⟨H, hm, hdeg, hd, hm.map σ, (natDegree_map σ).trans hdeg, hd', hcop, ?_,
    hunit, hunit.map (Polynomial.mapRingHom σ), ?_⟩
  · intro i
    have h₀ : H.eval (φ (node i)) ≠ 0 := by
      intro hz
      have hb : (liftPoly M.E).eval (φ (node i)) = 0 := by
        obtain ⟨J, hj⟩ := hd
        simp [hj, eval_mul, hz]
      exact M.E_nodes i (φ.injective (by simpa [liftPoly, φ] using hb))
    have hx : σ (φ (node i)) = φ (node i) := by
      change φ (node i) ^ p = _
      rw [← map_pow, FrobeniusLocator.Native.native_domain_fixed]
    refine ⟨h₀, ?_⟩
    rw [← hx, eval_map_apply]
    exact (map_ne_zero σ).mpr h₀
  · intro γ hγ
    let z := M.label γ
    let B := F.mark γ hγ
    have ha : IsCoprime (liftPoly (M.factor * M.amplitude γ)) H :=
      ((M.coprime_factor.symm.mul_left B.pole_unit).map
        (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
    have hid : M.E ∣ (M.factor * M.amplitude γ) * F.scalar γ + C z * M.Q :=
      ⟨M.decoder B.bad, by rw [← B.identity]; ring⟩
    have hres : H ∣ liftPoly (M.factor * M.amplitude γ) * liftPoly (F.scalar γ) +
        C (φ z) * liftPoly M.Q := by
      simpa only [liftPoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        using hd.trans (Polynomial.map_dvd φ hid)
    have hfix : (liftPoly (F.scalar γ)).map σ = liftPoly (F.scalar γ) := by
      rw [← twist_lift, B.scalar_fixed]
    refine ⟨ha, ha.map (Polynomial.mapRingHom σ), hres, ?_⟩
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hfix,
      σ, frobenius_def] using (Polynomial.map_dvd σ hres)

end
end K1_14
end PackSource_K1_14Chart

section PackSource_K1_14Terminal
set_option autoImplicit true
namespace K1_14

noncomputable section

open K1 Polynomial

private theorem terminal_mem (w : ℤ) : terminalShape w ∈ scheduled w := by
  unfold scheduled
  split <;> simp

private theorem terminal_width (w : ℤ) (hw : 2601 ≤ w) {q : ℕ}
    (hq : q ≤ (terminalShape w).B) :
    q * (131071 - w.toNat) ≤ (terminalShape w).m * 180265 := by
  calc
    _ ≤ (terminalShape w).B * 128470 := Nat.mul_le_mul hq (by omega)
    _ ≤ _ := by unfold terminalShape band; split_ifs <;> decide

/-- Extract the exact rectangular subbank floor and leading-coefficient
bounds once, for either surface schedule. -/
theorem terminalMass_of_source {u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} (hr : JetSource M F rows)
    (hlo : 2601 ≤ M.overhead) {f : Equation}
    (hd : TerminalDivisibility M.overhead rows f) : TerminalMass M.overhead f := by
  let w := M.overhead
  let s := terminalShape w
  have hs := terminal_mem w
  have htop : 0 < s.m * 180265 := by
    unfold s terminalShape band
    split_ifs <;> decide
  have hent : s.m * 180265 - 1 + 1 = s.m * 180265 := by omega
  refine ⟨rows s, ?_, ?_⟩
  · have h := hr.floor_bound s hs (s.m*180265-1) (by omega) (by
      intro q hq j _
      have hq' : q * (131071 - M.overhead.toNat) ≤ s.m * 180265 := terminal_width w hlo hq
      rw [hent]
      exact hq'.trans (Nat.le_add_right _ _))
    rw [hent] at h
    exact h
  · intro W hW P hP hne
    have hlc := leadingCoeff_ne_zero.mpr hne
    have htopcoeff : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 :=
      leadingCoeff_ne_zero.mpr hlc
    obtain ⟨hb, hj, _⟩ := hr.shape s hs W P hP _ _ htopcoeff
    refine ⟨hj, hb, hr.leading s hs W P hP hne, ?_, hd W hW P hP hne⟩
    intro i
    by_cases h : P.leadingCoeff.coeff i = 0
    · simp [h]
    · exact (hr.shape s hs W P hP _ _ h).2.2

end
end K1_14
end PackSource_K1_14Terminal

section PackSource_K1_14Split
set_option autoImplicit true
namespace K1_14

noncomputable section

open K1 Polynomial

/-- The common true-jet source for the two adjacent primary blocks. -/
def c1 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    2601 ≤ M.overhead → M.overhead ≤ 32680 →
    ∀ H, AdjacentChart M F H → ∃ rows : Banks, JetSource M F rows

/-- Bridge prefix including its algebraic first-loss curve count. -/
def c2 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    2601 ≤ M.overhead → M.overhead ≤ 3554 →
    ∀ H, AdjacentChart M F H → ∀ rows, JetSource M F rows → PrefixCover M F rows

/-- Paired prefix with the direct Frobenius-graph loss price. -/
def c3 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    3555 ≤ M.overhead → M.overhead ≤ 32680 →
    ∀ H, AdjacentChart M F H → ∀ rows, JetSource M F rows → PrefixCover M F rows

/-- The dimension loss if the primitive projected equation exceeds the
tested total seed degree. -/
def c4 : Prop :=
  ∀ (w : ℤ), 2601 ≤ w → w ≤ 32680 → ∀ f : Equation,
    ReducedEquation w f → TerminalMass w f → ¬ SeedBound f (band w).seedBound →
      seedGain w ≤ subbankDebit w

/-- Strict test (T) for each native height, with all four subbank shapes. -/
def c5 : Prop :=
  ∀ (w : ℤ), 2601 ≤ w → w ≤ 32680 → subbankDebit w < seedGain w

/-- Count the actual simple polynomial roots via the Taylor map and
fixed-word incidence at this band's endpoint degree. -/
def c6 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    2601 ≤ M.overhead → M.overhead ≤ 32680 → ∀ f : Equation,
    ReducedEquation M.overhead f → SeedBound f (band M.overhead).seedBound →
    ∀ T ⊆ Γ, (∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0 ∧
        atMark f.derivative (M.label γ) (F.scalar γ) ≠ 0) →
      T.card ≤ simplePrice M.overhead

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    (h6 : c6) : K1.c14 := by
  classical
  intro u del M Γ F hlo hhi
  obtain ⟨H, hH⟩ := adjacent_chart M F
  obtain ⟨rows, hrows⟩ := h1 u del M Γ F hlo hhi H hH
  have cover : PrefixCover M F rows := by
    by_cases h : M.overhead ≤ 3554
    · exact h2 u del M Γ F hlo h H hH rows hrows
    · exact h3 u del M Γ F (by omega) hhi H hH rows hrows
  obtain hshort | ⟨kept, hsub, hprefix, f, hf, hm, hroots⟩ := cover
  · exact hshort.trans (Nat.le_add_right _ _)
  have hseed : SeedBound f (band M.overhead).seedBound := by
    by_contra hbad
    exact (h5 _ hlo hhi).not_ge (h4 _ hlo hhi f hf (terminalMass_of_source hrows hlo hm) hbad)
  let singular := kept.filter fun γ => atMark f.derivative (M.label γ) (F.scalar γ) = 0
  have hsubset : singular ⊆ kept := Finset.filter_subset _ _
  have hexception := singular_count M hf hseed singular F.scalar
    (fun γ hγ => hroots γ (hsubset hγ)) (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hsimple := h6 u del M Γ F hlo hhi f hf hseed (kept \ singular)
    (Finset.sdiff_subset.trans hsub) (by
      intro γ hγ
      obtain ⟨hk, hn⟩ := Finset.mem_sdiff.mp hγ
      exact ⟨hroots γ hk, fun hz => hn (Finset.mem_filter.mpr ⟨hk, hz⟩)⟩)
  have hpartition := Finset.card_sdiff_add_card_eq_card hsubset
  have htotal := Finset.card_sdiff_add_card_eq_card hsub
  rw [← retained_price M.overhead]
  omega

end
end K1_14
end PackSource_K1_14Split
