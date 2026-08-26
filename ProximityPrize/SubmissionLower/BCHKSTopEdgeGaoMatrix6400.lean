import ProximityPrize.SubmissionLower.BCHKSMixedHermiteRowSpan6400
import ProximityPrize.SubmissionLower.BCHKSMixedJetGaoAudit6400
import ProximityPrize.SubmissionLower.BCHKSTopEdgeMixedJetStableAudit6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSTopEdgeGaoMatrix6400
open Polynomial Matrix
open BCHKSMixedHermitePivot6400
open BCHKSMixedHermiteRowSpan6400
open BCHKSMixedJetRankBridge6400
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 200000
abbrev TrapezoidIndex (k d w : Nat) :=
  {q : Fin (w + 1) × Fin (d + 1) //
    (q.1 : Nat) + k * (q.2 : Nat) <= w}
def trapezoidX {k d w : Nat} (q : TrapezoidIndex k d w) : Nat :=
  q.1.1
def trapezoidY {k d w : Nat} (q : TrapezoidIndex k d w) : Nat :=
  q.1.2
abbrev TopEdgeGIndex (k d w : Nat) :=
  {q : TrapezoidIndex k d w // 0 < trapezoidX q}
abbrev TopEdgeHIndex (k d w : Nat) :=
  {q : TrapezoidIndex k d w //
    0 < trapezoidY q ∧ trapezoidY q < d}
abbrev TopEdgeSourceIndex (k d w : Nat) :=
  TopEdgeGIndex k d w ⊕ TopEdgeHIndex k d w
def gExponentX {k d w : Nat} (q : TopEdgeGIndex k d w) : Nat :=
  trapezoidX q.1 - 1
def gExponentY {k d w : Nat} (q : TopEdgeGIndex k d w) : Nat :=
  trapezoidY q.1
def hExponentX {k d w : Nat} (q : TopEdgeHIndex k d w) : Nat :=
  trapezoidX q.1
def hExponentY {k d w : Nat} (q : TopEdgeHIndex k d w) : Nat :=
  trapezoidY q.1 - 1
abbrev GaoOutputIndex (outX outY : Nat) :=
  Fin (outX + 1) × Fin (outY + 1)
noncomputable def biCoeff
    {F : Type*} [Field F]
    (f : Polynomial (Polynomial (Polynomial F))) (x y : Nat) :
    Polynomial F :=
  (f.coeff y).coeff x
noncomputable def topEdgeGaoMatrix
    {F : Type*} [Field F]
    (f : Polynomial (Polynomial (Polynomial F)))
    (k d w outX outY : Nat) :
    Matrix (GaoOutputIndex outX outY)
      (TopEdgeSourceIndex k d w) (Polynomial F) :=
  fun r c =>
    match c with
    | Sum.inl q =>
        let a := gExponentX q
        let b := gExponentY q
        let x := (r.1 : Nat)
        let y := (r.2 : Nat)
        if _h : a <= x ∧ b <= y + 1 then
          let yf := y + 1 - b
          Polynomial.C ((b : F) - (yf : F)) *
            biCoeff f (x - a) yf
        else 0
    | Sum.inr q =>
        let a := hExponentX q
        let b := hExponentY q
        let x := (r.1 : Nat)
        let y := (r.2 : Nat)
        if _h : a <= x + 1 ∧ b <= y then
          let xf := x + 1 - a
          Polynomial.C ((xf : F) - (a : F)) *
            biCoeff f xf (y - b)
        else 0
def FactorCoefficientDegreeCap
    {F : Type*} [Field F]
    (f : Polynomial (Polynomial (Polynomial F))) (cap : Nat) : Prop :=
  forall x y, (biCoeff f x y).natDegree <= cap
theorem topEdgeGaoMatrix_entry_natDegree_le
    {F : Type*} [Field F]
    (f : Polynomial (Polynomial (Polynomial F)))
    (k d w outX outY cap : Nat)
    (hcap : FactorCoefficientDegreeCap f cap) :
    forall r c,
      (topEdgeGaoMatrix f k d w outX outY r c).natDegree <= cap := by
  intro r c
  cases c with
  | inl q =>
      simp only [topEdgeGaoMatrix]
      split
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (hcap _ _)
      · simp
  | inr q =>
      simp only [topEdgeGaoMatrix]
      split
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (hcap _ _)
      · simp
abbrev TopEdgeJetIndex
    (I : Type*) (nu : I -> Nat) (d : Nat) :=
  Sigma fun b : Fin (d - 1) =>
    HermiteIndex I (predecessorLayerCount nu b)
def jetLayer
    {I : Type*} {nu : I -> Nat} {d : Nat}
    (j : TopEdgeJetIndex I nu d) : Nat :=
  j.1
def jetPoint
    {I : Type*} {nu : I -> Nat} {d : Nat}
    (j : TopEdgeJetIndex I nu d) : I :=
  j.2.1
def jetXOrder
    {I : Type*} {nu : I -> Nat} {d : Nat}
    (j : TopEdgeJetIndex I nu d) : Nat :=
  j.2.2
abbrev TopEdgeMixedJetRowIndex
    (I : Type*) (nu : I -> Nat) (d : Nat) :=
  TopEdgeJetIndex I nu d ⊕ TopEdgeJetIndex I nu d
theorem linearIndependent_sigmaFin_of_triangular_restriction
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {n : Nat}
    (J : Fin n -> Type*) [forall b, Fintype (J b)]
    (N : Fin n -> Type*)
    [forall b, AddCommGroup (N b)] [forall b, Module K (N b)]
    (block : forall b, J b -> M)
    (L : forall b, M →ₗ[K] N b)
    (hdiag : forall b, LinearIndependent K (fun j => L b (block b j)))
    (hzero : forall (b c : Fin n), (b : Nat) < c -> forall j,
      L b (block c j) = 0) :
    LinearIndependent K (fun q : Sigma J => block q.1 q.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff hrelation
  have hblock (b : Fin n)
      (hlower : forall a : Fin n, (a : Nat) < b ->
        forall j, coeff ⟨a, j⟩ = 0) :
      forall j, coeff ⟨b, j⟩ = 0 := by
    have hmapped := congrArg (L b) hrelation
    simp only [map_sum, map_smul, map_zero] at hmapped
    rw [Fintype.sum_sigma] at hmapped
    have houter :
        (∑ a : Fin n, ∑ j : J a,
          coeff ⟨a, j⟩ • L b (block a j)) =
        ∑ j : J b, coeff ⟨b, j⟩ • L b (block b j) := by
      rw [Finset.sum_eq_single b]
      · intro a _ hne
        apply Finset.sum_eq_zero
        intro j _
        by_cases hab : (a : Nat) < b
        · rw [hlower a hab j, zero_smul]
        · have hba : (b : Nat) < a := by omega
          rw [hzero b a hba j, smul_zero]
      · simp
    rw [houter] at hmapped
    have hd := hdiag b
    rw [Fintype.linearIndependent_iff] at hd
    exact hd (fun j => coeff ⟨b, j⟩) hmapped
  intro q
  have hprefix : forall m : Nat, forall b : Fin n,
      (b : Nat) = m -> forall j, coeff ⟨b, j⟩ = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro b hb
        apply hblock b
        intro a ha j
        exact ih a.val (by omega) a rfl j
  exact hprefix q.1.val q.1 rfl q.2
def TopEdgeLayerCapacity
    {I : Type*} [Fintype I]
    (nu : I -> Nat) (k d w : Nat) : Prop :=
  forall b : Fin (d - 1),
    (∑ i : I, predecessorLayerCount nu b i) + k * (b + 1) <= w + 1
theorem degree53_topEdgeLayerCapacity6400
    {I : Type*} [Fintype I]
    (nu : I -> Nat)
    (hcard : Fintype.card I = 185364)
    (hnu : forall i, nu i <= 53) :
    TopEdgeLayerCapacity nu 131071 53
      BCHKSTopEdgeMixedJetStableAudit6400.bchksTopEdgeWeight6400 := by
  intro b
  have hpoint : forall i : I,
      predecessorLayerCount nu b i <= 52 - (b : Nat) := by
    intro i
    have hi := hnu i
    simp only [predecessorLayerCount]
    omega
  calc
    (∑ i : I, predecessorLayerCount nu b i) + 131071 * ((b : Nat) + 1) <=
        (∑ _i : I, (52 - (b : Nat))) + 131071 * ((b : Nat) + 1) := by
      gcongr with i
      exact hpoint i
    _ = Fintype.card I * (52 - (b : Nat)) +
        131071 * ((b : Nat) + 1) := by simp
    _ = 185364 * (52 - (b : Nat)) +
        131071 * ((b : Nat) + 1) := by rw [hcard]
    _ <= BCHKSTopEdgeMixedJetStableAudit6400.bchksTopEdgeWeight6400 + 1 := by
      have hb := b.isLt
      norm_num [BCHKSTopEdgeMixedJetStableAudit6400.bchksTopEdgeWeight6400]
      omega
def hLayerColumn
    {I : Type*} [Fintype I]
    {nu : I -> Nat} {k d w : Nat}
    (hcap : TopEdgeLayerCapacity nu k d w)
    (b : Fin (d - 1))
    (a : Fin (∑ i : I, predecessorLayerCount nu b i)) :
    TopEdgeHIndex k d w := by
  have hxy : (a : Nat) + k * ((b : Nat) + 1) <= w := by
    have ha := a.isLt
    have hc := hcap b
    omega
  refine ⟨⟨(⟨a, ?_⟩, ⟨b + 1, ?_⟩), ?_⟩, ?_⟩
  · omega
  · have hb := b.isLt
    omega
  · exact hxy
  · constructor <;> simp only [trapezoidY] <;> omega
def gLayerColumn
    {I : Type*} [Fintype I]
    {nu : I -> Nat} {k d w : Nat}
    (hk : 1 <= k) (hcap : TopEdgeLayerCapacity nu k d w)
    (b : Fin (d - 1))
    (a : Fin (∑ i : I, predecessorLayerCount nu b i)) :
    TopEdgeGIndex k d w := by
  have hxy : (a : Nat) + 1 + k * (b : Nat) <= w := by
    have ha := a.isLt
    have hc := hcap b
    have hstrong : (a : Nat) + k * ((b : Nat) + 1) <= w := by omega
    simp only [Nat.mul_add, Nat.mul_one] at hstrong
    omega
  refine ⟨⟨(⟨a + 1, ?_⟩, ⟨b, ?_⟩), ?_⟩, ?_⟩
  · omega
  · have hb := b.isLt
    omega
  · exact hxy
  · simp [trapezoidX]
@[simp]
theorem hExponentX_hLayerColumn
    {I : Type*} [Fintype I]
    {nu : I -> Nat} {k d w : Nat}
    (hcap : TopEdgeLayerCapacity nu k d w)
    (b : Fin (d - 1))
    (a : Fin (∑ i : I, predecessorLayerCount nu b i)) :
    hExponentX (hLayerColumn hcap b a) = a := by
  rfl
@[simp]
theorem hExponentY_hLayerColumn
    {I : Type*} [Fintype I]
    {nu : I -> Nat} {k d w : Nat}
    (hcap : TopEdgeLayerCapacity nu k d w)
    (b : Fin (d - 1))
    (a : Fin (∑ i : I, predecessorLayerCount nu b i)) :
    hExponentY (hLayerColumn hcap b a) = b := by
  simp [hExponentY, hLayerColumn, trapezoidY]
@[simp]
theorem gExponentX_gLayerColumn
    {I : Type*} [Fintype I]
    {nu : I -> Nat} {k d w : Nat}
    (hk : 1 <= k) (hcap : TopEdgeLayerCapacity nu k d w)
    (b : Fin (d - 1))
    (a : Fin (∑ i : I, predecessorLayerCount nu b i)) :
    gExponentX (gLayerColumn hk hcap b a) = a := by
  simp [gExponentX, gLayerColumn, trapezoidX]
@[simp]
theorem gExponentY_gLayerColumn
    {I : Type*} [Fintype I]
    {nu : I -> Nat} {k d w : Nat}
    (hk : 1 <= k) (hcap : TopEdgeLayerCapacity nu k d w)
    (b : Fin (d - 1))
    (a : Fin (∑ i : I, predecessorLayerCount nu b i)) :
    gExponentY (gLayerColumn hk hcap b a) = b := by
  rfl
noncomputable def specializedOmega
    {F L I : Type*} [Field F] [Field L]
    (phi : Polynomial F →+* L) (omega : I ↪ F) : I ↪ L where
  toFun i := phi (Polynomial.C (omega i))
  inj' := fun _ _ h => omega.injective ((phi.comp Polynomial.C).injective h)
noncomputable def hermiteMonomialRow
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (mu : I -> Nat) (j : HermiteIndex I mu) :
    Fin (∑ i : I, mu i) -> K :=
  fun a => (Nat.choose (a : Nat) (j.2 : Nat) : K) *
    omega j.1 ^ ((a : Nat) - (j.2 : Nat))
theorem hermiteMonomialRow_linearIndependent
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (mu : I -> Nat) :
    LinearIndependent K (hermiteMonomialRow omega mu) := by
  classical
  let bP := Polynomial.degreeLT.basis K (∑ i : I, mu i)
  have hli := (selectedHermiteFunctional_linearIndependent omega mu).map'
    bP.dualBasis.equivFun.toLinearMap
    (LinearMap.ker_eq_bot_of_injective bP.dualBasis.equivFun.injective)
  have heq :
      (fun j => bP.dualBasis.equivFun
        (selectedHermiteFunctional omega mu j)) =
        hermiteMonomialRow omega mu := by
    funext j a
    simp [bP, hermiteMonomialRow, Module.Basis.dualBasis_equivFun,
      selectedHermiteFunctional_apply, Polynomial.X_pow_eq_monomial,
      Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial]
  rw [show (bP.dualBasis.equivFun.toLinearMap ∘
      selectedHermiteFunctional omega mu) = hermiteMonomialRow omega mu by
      simpa [Function.comp_def] using heq] at hli
  exact hli
noncomputable def monomialMixedHasseCoefficient
    {F : Type*} [Field F]
    (omega : F) (uZ : Polynomial F)
    (a c s b : Nat) : Polynomial F :=
  Polynomial.C
      ((Nat.choose a s : F) * omega ^ (a - s) *
        (Nat.choose c b : F)) *
    uZ ^ (c - b)
theorem monomialMixedHasseCoefficient_natDegree_le
    {F : Type*} [Field F]
    (omega : F) (uZ : Polynomial F)
    (a c s b d : Nat)
    (hu : uZ.natDegree <= 1) (hc : c <= d) :
    (monomialMixedHasseCoefficient omega uZ a c s b).natDegree <=
      d - b := by
  calc
    (monomialMixedHasseCoefficient omega uZ a c s b).natDegree <=
        (uZ ^ (c - b)).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ <= (c - b) * uZ.natDegree := Polynomial.natDegree_pow_le
    _ <= (c - b) * 1 := Nat.mul_le_mul_left _ hu
    _ = c - b := by simp
    _ <= d - b := Nat.sub_le_sub_right hc b
noncomputable def topEdgeMixedJetMatrix
    {F I : Type*} [Field F] [Fintype I]
    (omega : I -> F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w : Nat) :
    Matrix (TopEdgeMixedJetRowIndex I nu d)
      (TopEdgeSourceIndex k d w) (Polynomial F) :=
  fun r c =>
    match r, c with
    | Sum.inl j, Sum.inl q =>
        monomialMixedHasseCoefficient
          (omega (jetPoint j)) (uZ (jetPoint j))
          (gExponentX q) (gExponentY q)
          (jetXOrder j) (jetLayer j)
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr j, Sum.inr q =>
        monomialMixedHasseCoefficient
          (omega (jetPoint j)) (uZ (jetPoint j))
          (hExponentX q) (hExponentY q)
          (jetXOrder j) (jetLayer j)
def topEdgeMixedJetRowCap
    {I : Type*} {nu : I -> Nat} (d : Nat) :
    TopEdgeMixedJetRowIndex I nu d -> Nat :=
  Sum.elim (fun j => d - jetLayer j) (fun j => d - jetLayer j)
theorem topEdgeMixedJetMatrix_entry_natDegree_le
    {F I : Type*} [Field F] [Fintype I]
    (omega : I -> F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w : Nat)
    (hu : forall i, (uZ i).natDegree <= 1) :
    forall r c,
      (topEdgeMixedJetMatrix omega uZ nu k d w r c).natDegree <=
        topEdgeMixedJetRowCap d r := by
  intro r c
  cases r with
  | inl j =>
      cases c with
      | inl q =>
          apply monomialMixedHasseCoefficient_natDegree_le
          · exact hu (jetPoint j)
          · have hy := q.1.1.2.isLt
            simp only [gExponentY, trapezoidY]
            omega
      | inr q => simp [topEdgeMixedJetMatrix]
  | inr j =>
      cases c with
      | inl q => simp [topEdgeMixedJetMatrix]
      | inr q =>
          apply monomialMixedHasseCoefficient_natDegree_le
          · exact hu (jetPoint j)
          · have hy := q.1.1.2.isLt
            simp only [hExponentY, trapezoidY]
            omega
def restrictGComponent
    {L : Type*} [Field L] (k d w : Nat) :
    (TopEdgeSourceIndex k d w -> L) →ₗ[L] (TopEdgeGIndex k d w -> L) where
  toFun v q := v (Sum.inl q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def restrictHComponent
    {L : Type*} [Field L] (k d w : Nat) :
    (TopEdgeSourceIndex k d w -> L) →ₗ[L] (TopEdgeHIndex k d w -> L) where
  toFun v q := v (Sum.inr q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def restrictGToLayer
    {L I : Type*} [Field L] [Fintype I]
    {nu : I -> Nat} {k d w : Nat}
    (hk : 1 <= k) (hcap : TopEdgeLayerCapacity nu k d w)
    (b : Fin (d - 1)) :
    (TopEdgeGIndex k d w -> L) →ₗ[L]
      (Fin (∑ i : I, predecessorLayerCount nu b i) -> L) where
  toFun v a := v (gLayerColumn hk hcap b a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def restrictHToLayer
    {L I : Type*} [Field L] [Fintype I]
    {nu : I -> Nat} {k d w : Nat}
    (hcap : TopEdgeLayerCapacity nu k d w)
    (b : Fin (d - 1)) :
    (TopEdgeHIndex k d w -> L) →ₗ[L]
      (Fin (∑ i : I, predecessorLayerCount nu b i) -> L) where
  toFun v a := v (hLayerColumn hcap b a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def biMonomial
    {L : Type*} [Field L] (a c : Nat) (coeff : L) :
    Polynomial (Polynomial L) :=
  Polynomial.monomial c (Polynomial.monomial a coeff)
noncomputable def decodeTopEdgeG
    {L : Type*} [Field L] (k d w : Nat)
    (v : TopEdgeSourceIndex k d w -> L) :
    Polynomial (Polynomial L) :=
  ∑ q : TopEdgeGIndex k d w,
    biMonomial (gExponentX q) (gExponentY q) (v (Sum.inl q))
noncomputable def decodeTopEdgeH
    {L : Type*} [Field L] (k d w : Nat)
    (v : TopEdgeSourceIndex k d w -> L) :
    Polynomial (Polynomial L) :=
  ∑ q : TopEdgeHIndex k d w,
    biMonomial (hExponentX q) (hExponentY q) (v (Sum.inr q))
theorem mixedHasseJet_biMonomial
    {L : Type*} [Field L]
    (omega u coeff : L) (a c s b : Nat) :
    mixedHasseJet omega u s b (biMonomial a c coeff) =
      (Nat.choose a s : L) * omega ^ (a - s) *
        (Nat.choose c b : L) * u ^ (c - b) * coeff := by
  simp only [mixedHasseJet, biMonomial,
    Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial]
  have hpoly :
      (Nat.choose c b : Polynomial L) *
          Polynomial.monomial a coeff * Polynomial.C u ^ (c - b) =
          Polynomial.monomial a
          ((Nat.choose c b : L) * coeff * u ^ (c - b)) := by
    rw [← Polynomial.C_eq_natCast, Polynomial.C_mul_monomial,
      ← Polynomial.C_pow, Polynomial.monomial_mul_C]
  rw [hpoly, Polynomial.hasseDeriv_monomial,
    Polynomial.eval_monomial]
  ring
theorem map_monomialMixedHasseCoefficient
    {F L : Type*} [Field F] [Field L]
    (phi : Polynomial F →+* L)
    (omega : F) (uZ : Polynomial F) (a c s b : Nat) :
    phi (monomialMixedHasseCoefficient omega uZ a c s b) =
      (Nat.choose a s : L) * phi (Polynomial.C omega) ^ (a - s) *
        (Nat.choose c b : L) * phi uZ ^ (c - b) := by
  simp [monomialMixedHasseCoefficient, map_mul, map_pow]
theorem restrictGToLayer_mapped_gJet_diagonal
    {F L I : Type*} [Field F] [Field L] [Fintype I]
    (phi : Polynomial F →+* L)
    (omega : I ↪ F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w : Nat) (hk : 1 <= k)
    (hcap : TopEdgeLayerCapacity nu k d w)
    (b : Fin (d - 1)) :
    (fun j : HermiteIndex I (predecessorLayerCount nu b) =>
      restrictGToLayer hk hcap b
        (restrictGComponent k d w
          (((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
            (Sum.inl ⟨b, j⟩)))) =
      hermiteMonomialRow (specializedOmega phi omega)
        (predecessorLayerCount nu b) := by
  funext j a
  simp [restrictGToLayer, restrictGComponent, topEdgeMixedJetMatrix,
    map_monomialMixedHasseCoefficient, hermiteMonomialRow,
    specializedOmega, jetPoint, jetXOrder, jetLayer]
theorem restrictHToLayer_mapped_hJet_diagonal
    {F L I : Type*} [Field F] [Field L] [Fintype I]
    (phi : Polynomial F →+* L)
    (omega : I ↪ F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w : Nat)
    (hcap : TopEdgeLayerCapacity nu k d w)
    (b : Fin (d - 1)) :
    (fun j : HermiteIndex I (predecessorLayerCount nu b) =>
      restrictHToLayer hcap b
        (restrictHComponent k d w
          (((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
            (Sum.inr ⟨b, j⟩)))) =
      hermiteMonomialRow (specializedOmega phi omega)
        (predecessorLayerCount nu b) := by
  funext j a
  simp [restrictHToLayer, restrictHComponent, topEdgeMixedJetMatrix,
    map_monomialMixedHasseCoefficient, hermiteMonomialRow,
    specializedOmega, jetPoint, jetXOrder, jetLayer]
theorem restrictGToLayer_mapped_gJet_higher_zero
    {F L I : Type*} [Field F] [Field L] [Fintype I]
    (phi : Polynomial F →+* L)
    (omega : I ↪ F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w : Nat) (hk : 1 <= k)
    (hcap : TopEdgeLayerCapacity nu k d w)
    (b c : Fin (d - 1)) (hbc : (b : Nat) < c)
    (j : HermiteIndex I (predecessorLayerCount nu c)) :
    restrictGToLayer hk hcap b
        (restrictGComponent k d w
          (((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
            (Sum.inl ⟨c, j⟩))) = 0 := by
  funext a
  simp [restrictGToLayer, restrictGComponent, topEdgeMixedJetMatrix,
    map_monomialMixedHasseCoefficient,
    Nat.choose_eq_zero_of_lt hbc, jetPoint, jetXOrder, jetLayer]
theorem restrictHToLayer_mapped_hJet_higher_zero
    {F L I : Type*} [Field F] [Field L] [Fintype I]
    (phi : Polynomial F →+* L)
    (omega : I ↪ F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w : Nat)
    (hcap : TopEdgeLayerCapacity nu k d w)
    (b c : Fin (d - 1)) (hbc : (b : Nat) < c)
    (j : HermiteIndex I (predecessorLayerCount nu c)) :
    restrictHToLayer hcap b
        (restrictHComponent k d w
          (((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
            (Sum.inr ⟨c, j⟩))) = 0 := by
  funext a
  simp [restrictHToLayer, restrictHComponent, topEdgeMixedJetMatrix,
    map_monomialMixedHasseCoefficient,
    Nat.choose_eq_zero_of_lt hbc, jetPoint, jetXOrder, jetLayer]
theorem topEdgeMappedGJetRows_restrict_linearIndependent
    {F L I : Type*} [Field F] [Field L] [Fintype I]
    (phi : Polynomial F →+* L)
    (omega : I ↪ F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w : Nat) (hk : 1 <= k)
    (hcap : TopEdgeLayerCapacity nu k d w) :
    LinearIndependent L
      (fun j : TopEdgeJetIndex I nu d =>
        restrictGComponent k d w
          (((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
            (Sum.inl j))) := by
  classical
  apply linearIndependent_sigmaFin_of_triangular_restriction
    (J := fun b : Fin (d - 1) =>
      HermiteIndex I (predecessorLayerCount nu b))
    (N := fun b : Fin (d - 1) =>
      Fin (∑ i : I, predecessorLayerCount nu b i) -> L)
    (block := fun b j =>
      restrictGComponent k d w
        (((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
          (Sum.inl ⟨b, j⟩)))
    (L := fun b => restrictGToLayer hk hcap b)
  · intro b
    rw [restrictGToLayer_mapped_gJet_diagonal]
    exact hermiteMonomialRow_linearIndependent
      (specializedOmega phi omega) (predecessorLayerCount nu b)
  · intro b c hbc j
    exact restrictGToLayer_mapped_gJet_higher_zero
      phi omega uZ nu k d w hk hcap b c hbc j
theorem topEdgeMappedHJetRows_restrict_linearIndependent
    {F L I : Type*} [Field F] [Field L] [Fintype I]
    (phi : Polynomial F →+* L)
    (omega : I ↪ F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w : Nat)
    (hcap : TopEdgeLayerCapacity nu k d w) :
    LinearIndependent L
      (fun j : TopEdgeJetIndex I nu d =>
        restrictHComponent k d w
          (((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
            (Sum.inr j))) := by
  classical
  apply linearIndependent_sigmaFin_of_triangular_restriction
    (J := fun b : Fin (d - 1) =>
      HermiteIndex I (predecessorLayerCount nu b))
    (N := fun b : Fin (d - 1) =>
      Fin (∑ i : I, predecessorLayerCount nu b i) -> L)
    (block := fun b j =>
      restrictHComponent k d w
        (((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
          (Sum.inr ⟨b, j⟩)))
    (L := fun b => restrictHToLayer hcap b)
  · intro b
    rw [restrictHToLayer_mapped_hJet_diagonal]
    exact hermiteMonomialRow_linearIndependent
      (specializedOmega phi omega) (predecessorLayerCount nu b)
  · intro b c hbc j
    exact restrictHToLayer_mapped_hJet_higher_zero
      phi omega uZ nu k d w hcap b c hbc j
theorem topEdgeMixedJetMatrix_mapped_row_linearIndependent
    {F L I : Type*} [Field F] [Field L] [Fintype I]
    (phi : Polynomial F →+* L)
    (omega : I ↪ F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w : Nat) (hk : 1 <= k)
    (hcap : TopEdgeLayerCapacity nu k d w) :
    LinearIndependent L
      ((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row := by
  classical
  have hg := topEdgeMappedGJetRows_restrict_linearIndependent
    phi omega uZ nu k d w hk hcap
  have hhRestricted := topEdgeMappedHJetRows_restrict_linearIndependent
    phi omega uZ nu k d w hcap
  have hh : LinearIndependent L
      (fun j : TopEdgeJetIndex I nu d =>
        ((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
          (Sum.inr j)) := by
    apply LinearIndependent.of_comp (restrictHComponent k d w)
    change LinearIndependent L
      (fun j : TopEdgeJetIndex I nu d =>
        restrictHComponent k d w
          (((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
            (Sum.inr j)))
    exact hhRestricted
  have hzero : forall j : TopEdgeJetIndex I nu d,
      restrictGComponent k d w
        (((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
          (Sum.inr j)) = 0 := by
    intro j
    funext q
    simp [restrictGComponent, topEdgeMixedJetMatrix]
  have hsum := linearIndependent_sum_of_triangular_restriction
      (fun j : TopEdgeJetIndex I nu d =>
        ((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
          (Sum.inl j))
      (fun j : TopEdgeJetIndex I nu d =>
        ((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
          (Sum.inr j))
      (restrictGComponent k d w) hg hh hzero
  have heq :
      Sum.elim
        (fun j : TopEdgeJetIndex I nu d =>
          ((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
            (Sum.inl j))
        (fun j : TopEdgeJetIndex I nu d =>
          ((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
            (Sum.inr j)) =
        ((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row := by
    funext r
    cases r <;> rfl
  rw [heq] at hsum
  exact hsum
theorem dotProduct_mapped_topEdgeMixedJetMatrix_inl
    {F L I : Type*} [Field F] [Field L] [Fintype I]
    (phi : Polynomial F →+* L)
    (omega : I -> F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w : Nat) (v : TopEdgeSourceIndex k d w -> L)
    (j : TopEdgeJetIndex I nu d) :
    dotProduct
        (((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
          (Sum.inl j)) v =
      mixedHasseJet
        (phi (Polynomial.C (omega (jetPoint j))))
        (phi (uZ (jetPoint j))) (jetXOrder j) (jetLayer j)
        (decodeTopEdgeG k d w v) := by
  classical
  have hsum :
      mixedHasseJet
          (phi (Polynomial.C (omega (jetPoint j))))
          (phi (uZ (jetPoint j))) (jetXOrder j) (jetLayer j)
          (decodeTopEdgeG k d w v) =
        ∑ q : TopEdgeGIndex k d w,
          mixedHasseJet
            (phi (Polynomial.C (omega (jetPoint j))))
            (phi (uZ (jetPoint j))) (jetXOrder j) (jetLayer j)
            (biMonomial (gExponentX q) (gExponentY q)
              (v (Sum.inl q))) := by
    change mixedHasseJetLinear _ _ _ _
        (∑ q : TopEdgeGIndex k d w,
          biMonomial (gExponentX q) (gExponentY q) (v (Sum.inl q))) = _
    rw [map_sum]
    rfl
  rw [hsum]
  simp [dotProduct, Fintype.sum_sum_type,
    topEdgeMixedJetMatrix,
    map_monomialMixedHasseCoefficient,
    mixedHasseJet_biMonomial, mul_assoc, mul_left_comm, mul_comm]
theorem dotProduct_mapped_topEdgeMixedJetMatrix_inr
    {F L I : Type*} [Field F] [Field L] [Fintype I]
    (phi : Polynomial F →+* L)
    (omega : I -> F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w : Nat) (v : TopEdgeSourceIndex k d w -> L)
    (j : TopEdgeJetIndex I nu d) :
    dotProduct
        (((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row
          (Sum.inr j)) v =
      mixedHasseJet
        (phi (Polynomial.C (omega (jetPoint j))))
        (phi (uZ (jetPoint j))) (jetXOrder j) (jetLayer j)
        (decodeTopEdgeH k d w v) := by
  classical
  have hsum :
      mixedHasseJet
          (phi (Polynomial.C (omega (jetPoint j))))
          (phi (uZ (jetPoint j))) (jetXOrder j) (jetLayer j)
          (decodeTopEdgeH k d w v) =
        ∑ q : TopEdgeHIndex k d w,
          mixedHasseJet
            (phi (Polynomial.C (omega (jetPoint j))))
            (phi (uZ (jetPoint j))) (jetXOrder j) (jetLayer j)
            (biMonomial (hExponentX q) (hExponentY q)
              (v (Sum.inr q))) := by
    change mixedHasseJetLinear _ _ _ _
        (∑ q : TopEdgeHIndex k d w,
          biMonomial (hExponentX q) (hExponentY q) (v (Sum.inr q))) = _
    rw [map_sum]
    rfl
  rw [hsum]
  simp [dotProduct, Fintype.sum_sum_type,
    topEdgeMixedJetMatrix,
    map_monomialMixedHasseCoefficient,
    mixedHasseJet_biMonomial, mul_assoc, mul_left_comm, mul_comm]
structure TopEdgeGaoKernelMixedJetInterface
    {F L I : Type*} [Field F] [Field L] [Fintype I]
    (phi : Polynomial F →+* L)
    (f : Polynomial (Polynomial (Polynomial F)))
    (omega : I -> F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w outX outY : Nat) : Prop where
  gLocalJets : forall v : TopEdgeSourceIndex k d w -> L,
    ((topEdgeGaoMatrix f k d w outX outY).map phi).mulVec v = 0 ->
      forall (i : I) (s b : Nat), s + b < nu i - 1 ->
        mixedHasseJet
          (phi (Polynomial.C (omega i)))
          (phi (uZ i)) s b
          (decodeTopEdgeG k d w v) = 0
  hLocalJets : forall v : TopEdgeSourceIndex k d w -> L,
    ((topEdgeGaoMatrix f k d w outX outY).map phi).mulVec v = 0 ->
      forall (i : I) (s b : Nat), s + b < nu i - 1 ->
        mixedHasseJet
          (phi (Polynomial.C (omega i)))
          (phi (uZ i)) s b
          (decodeTopEdgeH k d w v) = 0
theorem topEdgeMixedJets_annihilate_gaoKernel
    {F L I : Type*} [Field F] [Field L] [Fintype I]
    (phi : Polynomial F →+* L)
    (f : Polynomial (Polynomial (Polynomial F)))
    (omega : I -> F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w outX outY : Nat)
    (H : TopEdgeGaoKernelMixedJetInterface
      phi f omega uZ nu k d w outX outY) :
    forall v,
      ((topEdgeGaoMatrix f k d w outX outY).map phi).mulVec v = 0 ->
      forall r,
        dotProduct
          (((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row r) v =
          0 := by
  intro v hv r
  cases r with
  | inl j =>
      rw [dotProduct_mapped_topEdgeMixedJetMatrix_inl]
      apply H.gLocalJets v hv
      have hs := j.2.2.isLt
      change jetXOrder j <
        predecessorLayerCount nu (jetLayer j) (jetPoint j) at hs
      simp only [predecessorLayerCount] at hs
      omega
  | inr j =>
      rw [dotProduct_mapped_topEdgeMixedJetMatrix_inr]
      apply H.hLocalJets v hv
      have hs := j.2.2.isLt
      change jetXOrder j <
        predecessorLayerCount nu (jetLayer j) (jetPoint j) at hs
      simp only [predecessorLayerCount] at hs
      omega
def topEdgeAugmentedRowCap
    {I : Type*} {nu : I -> Nat}
    (d factorCap outX outY : Nat) :
    TopEdgeMixedJetRowIndex I nu d ⊕ GaoOutputIndex outX outY -> Nat :=
  Sum.elim (topEdgeMixedJetRowCap d) (fun _ => factorCap)
theorem topEdgeAugmentedMatrix_entry_natDegree_le
    {F I : Type*} [Field F] [Fintype I]
    (f : Polynomial (Polynomial (Polynomial F)))
    (omega : I -> F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w outX outY factorCap : Nat)
    (hf : FactorCoefficientDegreeCap f factorCap)
    (hu : forall i, (uZ i).natDegree <= 1) :
    forall q c,
      (augmentedPolynomialMatrix
        (topEdgeMixedJetMatrix omega uZ nu k d w)
        (topEdgeGaoMatrix f k d w outX outY) q c).natDegree <=
      topEdgeAugmentedRowCap d factorCap outX outY q := by
  intro q c
  cases q with
  | inl r =>
      exact topEdgeMixedJetMatrix_entry_natDegree_le
        omega uZ nu k d w hu r c
  | inr r =>
      exact topEdgeGaoMatrix_entry_natDegree_le
        f k d w outX outY factorCap hf r c
theorem topEdgeMixedJetRowCap_le_53
    {I : Type*} {nu : I -> Nat} {d : Nat}
    (hd : d <= 53) (r : TopEdgeMixedJetRowIndex I nu d) :
    topEdgeMixedJetRowCap d r <= 53 := by
  cases r <;> simp [topEdgeMixedJetRowCap] <;> omega
theorem topEdgeGao_exists_controlled_augmented_minor
    {F L I : Type*} [Field F] [Field L] [Fintype I] [DecidableEq I]
    (phi : Polynomial F →+* L)
    (f : Polynomial (Polynomial (Polynomial F)))
    (omega : I -> F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w outX outY factorCap : Nat)
    (hf : FactorCoefficientDegreeCap f factorCap)
    (hu : forall i, (uZ i).natDegree <= 1)
    (hjetLI : LinearIndependent L
      ((topEdgeMixedJetMatrix omega uZ nu k d w).map phi).row)
    (H : TopEdgeGaoKernelMixedJetInterface
      phi f omega uZ nu k d w outX outY) :
    AugmentedRowBasisMinorCertificate phi
      (topEdgeMixedJetMatrix omega uZ nu k d w)
      (topEdgeGaoMatrix f k d w outX outY)
      (topEdgeAugmentedRowCap d factorCap outX outY) := by
  classical
  apply controlledAugmentedRowBasis_exists_minor_of_kernel_annihilation
  · exact topEdgeAugmentedMatrix_entry_natDegree_le
      f omega uZ nu k d w outX outY factorCap hf hu
  · exact hjetLI
  · exact topEdgeMixedJets_annihilate_gaoKernel
      phi f omega uZ nu k d w outX outY H
theorem topEdgeGao_exists_controlled_augmented_minor_of_layerCapacity
    {F L I : Type*} [Field F] [Field L] [Fintype I] [DecidableEq I]
    (phi : Polynomial F →+* L)
    (f : Polynomial (Polynomial (Polynomial F)))
    (omega : I ↪ F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w outX outY factorCap : Nat)
    (hf : FactorCoefficientDegreeCap f factorCap)
    (hu : forall i, (uZ i).natDegree <= 1)
    (hk : 1 <= k)
    (hcap : TopEdgeLayerCapacity nu k d w)
    (H : TopEdgeGaoKernelMixedJetInterface
      phi f omega uZ nu k d w outX outY) :
    AugmentedRowBasisMinorCertificate phi
      (topEdgeMixedJetMatrix omega uZ nu k d w)
      (topEdgeGaoMatrix f k d w outX outY)
      (topEdgeAugmentedRowCap d factorCap outX outY) := by
  apply topEdgeGao_exists_controlled_augmented_minor
    phi f omega uZ nu k d w outX outY factorCap hf hu
  · exact topEdgeMixedJetMatrix_mapped_row_linearIndependent
      phi omega uZ nu k d w hk hcap
  · exact H
theorem topEdgeGao_degree53_exists_controlled_augmented_minor6400
    {F L I : Type*} [Field F] [Field L] [Fintype I] [DecidableEq I]
    (phi : Polynomial F →+* L)
    (f : Polynomial (Polynomial (Polynomial F)))
    (omega : I ↪ F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (outX outY factorCap : Nat)
    (hcard : Fintype.card I = 185364)
    (hnu : forall i, nu i <= 53)
    (hf : FactorCoefficientDegreeCap f factorCap)
    (hu : forall i, (uZ i).natDegree <= 1)
    (H : TopEdgeGaoKernelMixedJetInterface
      phi f omega uZ nu 131071 53
        BCHKSTopEdgeMixedJetStableAudit6400.bchksTopEdgeWeight6400
        outX outY) :
    AugmentedRowBasisMinorCertificate phi
      (topEdgeMixedJetMatrix omega uZ nu 131071 53
        BCHKSTopEdgeMixedJetStableAudit6400.bchksTopEdgeWeight6400)
      (topEdgeGaoMatrix f 131071 53
        BCHKSTopEdgeMixedJetStableAudit6400.bchksTopEdgeWeight6400
        outX outY)
      (topEdgeAugmentedRowCap 53 factorCap outX outY) := by
  apply topEdgeGao_exists_controlled_augmented_minor_of_layerCapacity
    phi f omega uZ nu 131071 53
      BCHKSTopEdgeMixedJetStableAudit6400.bchksTopEdgeWeight6400
      outX outY factorCap hf hu
  · norm_num
  · exact degree53_topEdgeLayerCapacity6400 nu hcard hnu
  · exact H
end BCHKSTopEdgeGaoMatrix6400
end ProximityPrize.SubmissionLower
