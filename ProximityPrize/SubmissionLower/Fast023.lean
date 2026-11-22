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
import ProximityPrize.SubmissionLower.Pack_K1_13_6_1_4Geometry
set_option autoImplicit true
section
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
def band (w : ℤ) : Band :=
  if w ≤ 3554 then ⟨3554,5,144,836,1164,247,19371⟩
  else if w ≤ 8249 then ⟨8249,4,98,358,500,105,6798⟩
  else if w ≤ 23999 then ⟨23999,4,47,358,500,105,4860⟩
  else ⟨32680,4,36,358,500,105,3913⟩
def SeedBound (f : Equation) (b : ℕ) : Prop :=
  ∀ i, (f.coeff i).totalDegree ≤ b
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
def subbankDebit (w : ℤ) : ℕ := sourceDebit w.toNat (terminalShape w)
def forcedPower (w : ℤ) (W j : ℕ) : ℕ :=
  1 + ((band w).multiplicity * 180265 - 1 - W) / (2 * w.toNat) - j
def seedGain (w : ℤ) : ℕ :=
  let b := band w
  let U := b.subbankSeeds
  let v := b.seedBound + 1
  shapeSum (terminalShape w) fun q j => ∑ r ∈ Finset.range (U / v + 1),
    (slots U (r*v) - slots U ((r+1)*v)) * (rawWidth w q j - 2*w.toNat*(j+r))
def scheduled (w : ℤ) : List Shape :=
  let sub := terminalShape w
  if w ≤ 3554 then
    [⟨59,82,18,1899⟩,⟨136,190,40,8441⟩,⟨66,92,21,2076⟩,⟨150,210,44,9356⟩,
     ⟨73,102,23,2261⟩,⟨164,229,48,10272⟩,⟨80,112,25,2455⟩,⟨178,249,52,11191⟩,
     ⟨94,131,30,2824⟩,⟨213,298,62,12959⟩,⟨115,160,36,3401⟩,⟨262,366,77,15611⟩,
     ⟨136,190,43,4204⟩,⟨325,454,96,19187⟩,⟨178,248,56,5332⟩,⟨409,572,121,24615⟩,
     ⟨241,336,78,7235⟩,⟨570,797,169,33523⟩,⟨325,453,104,9976⟩,⟨759,1061,224,46271⟩,
     ⟨836,1164,247,273617⟩, sub]
  else
    [⟨45,63,14,812⟩,⟨84,118,24,2907⟩,⟨57,80,18,1041⟩,⟨114,160,33,3775⟩,
     ⟨81,114,26,1383⟩,⟨144,203,42,5064⟩,⟨123,173,40,2173⟩,⟨231,325,67,8061⟩,
     ⟨358,500,105,66251⟩, sub]
def jetAt (P : Jet) (z : K) (S : K[X]) : FX :=
  P.eval₂ (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
def translateSeed (i : Fin 2) : Seeds →+* Polynomial Seeds :=
  MvPolynomial.eval₂Hom (C.comp MvPolynomial.C)
    (fun j => C (MvPolynomial.X j : Seeds) + if j = i then Polynomial.X (R := Seeds) else 0)
def seedHasse (i : Fin 2) (r : ℕ) (P : Jet) : Jet :=
  P.sum fun j g => monomial j (g.sum fun k c => monomial k ((translateSeed i c).coeff r))
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
end
end K1_14
end
section
namespace K1_14
noncomputable section
open K1 Polynomial
open scoped BigOperators
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
end
end K1_14
end
section
namespace K1_14
noncomputable section
open K1 Polynomial
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
end
end K1_14
end
