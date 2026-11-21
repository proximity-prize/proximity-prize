import ProximityPrize.SubmissionLower.Fast065
import ProximityPrize.SubmissionLower.Hi6921Fast023

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace HighSource6921

noncomputable section

open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators

/-- Generic CRT lift with denominators regular at every permitted specialization. -/
def CRTReady : Prop :=
  ∀ h, 2472 ≤ h → h ≤ 32950 → ∀ D : PoleData h, Nonempty (CRTLift D)

/-- Contact and the unpunctured agreement force each evaluated row to be an identity. -/
def ContactNecessary : Prop :=
  ∀ h, 2472 ≤ h → h ≤ 32950 → ∀ (D : PoleData h) (Crt : CRTLift D) (word : I → L),
    (∀ i k, (D.block i).eval (nodeL k) ≠ 0) →
    ∀ z S, MarkResidues D z S → (liftPoly S).natDegree ≤ 131071+h →
    ∀ hits : Finset I, 180130 ≤ hits.card → (∀ k ∈ hits, (liftPoly S).eval (nodeL k) = word k) →
    ∀ s W, W < s.m*180130 → ∀ P ∈ evaluated Crt word s W, jetAt P z S = 0

/-- Fixed-true-jet seed derivatives consume at most 2h of cutoff per order. -/
def HasseClosed : Prop :=
  ∀ h, 2472 ≤ h → h ≤ 32950 → ∀ (D : PoleData h) (Crt : CRTLift D) (word : I → L),
    ∀ s W, ∀ P ∈ evaluated Crt word s W, ∀ i r,
      seedHasse i r P ∈ evaluated Crt word s (W+2*h*r)

/-- The leading V,Y position of an evaluated row satisfies the raw cutoff. -/
def LeadingWeight : Prop :=
  ∀ h, 2472 ≤ h → h ≤ 32950 → ∀ (D : PoleData h) (Crt : CRTLift D) (word : I → L),
    ∀ s W, ∀ P ∈ evaluated Crt word s W, P ≠ 0 →
      (P.leadingCoeff.natDegree + P.natDegree)*(131071-h) ≤ W+P.natDegree

/-- Count the true ambient monomials before the two sets of constraints. -/
def AmbientRank : Prop :=
  ∀ h, 2472 ≤ h → h ≤ 32950 → ∀ s W, rawWidthCond h s W →
    rawVolumeAt h s W + poleCredit h s ≤ Module.finrank L (ambient h s W)

/-- Restricting to the physical contacts costs at most the sum of the node debits. -/
def ContactRank : Prop :=
  ∀ h, 2472 ≤ h → h ≤ 32950 → ∀ (word : I → L) s W,
    Module.finrank L (ambient h s W) ≤
      physicalDebit s + Module.finrank L (contacted h word s W)

/-- Full primary divisibility costs at most the main pole credit and seed debit. -/
def PoleRank : Prop :=
  ∀ h, 2472 ≤ h → h ≤ 32950 → ∀ (D : PoleData h) (Crt : CRTLift D) (word : I → L) s W,
    Module.finrank L (contacted h word s W) ≤
      poleCredit h s + poleSeedDebit h s + Module.finrank L (complete Crt word s W)

/-- Whole-cutoff sum of evaluated dimensions dominates the symbolic dimension. -/
def CutoffRank : Prop :=
  ∀ h, 2472 ≤ h → h ≤ 32950 → ∀ (D : PoleData h) (Crt : CRTLift D) (word : I → L) s W,
    Module.finrank L (complete Crt word s W) ≤
      ∑ t ∈ Finset.range (W+1), Module.finrank FX (evaluated Crt word s t)

end
end HighSource6921

section PackSource_K1_14_1_1Proof
set_option autoImplicit true
namespace HighSource6921.CRT

noncomputable section

open K1_14 K1_14_1 Module Polynomial
open scoped Polynomial

private def quotientBasis {R : Type*} [CommRing R] {b : R[X]} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) : Basis (Fin n) R (AdjoinRoot b) :=
  (AdjoinRoot.powerBasisAux' hb).reindex (finCongr hd)

private def mulMatrix {R : Type*} [CommRing R] {b : R[X]} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) (a : R[X]) : Matrix (Fin n) (Fin n) R :=
  Algebra.leftMulMatrix (quotientBasis hb hd) (AdjoinRoot.mk b a)

private theorem mulMatrix_entry {R : Type*} [CommRing R] {b : R[X]} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) (a : R[X]) (i j : Fin n) :
    mulMatrix hb hd a i j = ((a * Polynomial.X (R := R) ^ (j : ℕ)) %ₘ b).coeff i := by
  have hpow (k : Fin b.natDegree) :
      (AdjoinRoot.powerBasisAux' hb) k = AdjoinRoot.root b ^ (k : ℕ) :=
    (AdjoinRoot.powerBasis' hb).basis_eq_pow k
  unfold mulMatrix
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  unfold quotientBasis
  rw [Basis.reindex_apply, hpow, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul,
    Basis.repr_reindex_apply, AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    AdjoinRoot.modByMonicHom_mk]
  rfl

private theorem mulMatrix_specialize {R S : Type*} [CommRing R] [CommRing S]
    {b a : R[X]} {b' a' : S[X]} {n : ℕ} (f : R →+* S)
    (hb : b.Monic) (hd : b.natDegree = n) (hb' : b'.Monic) (hd' : b'.natDegree = n)
    (hmapb : b.map f = b') (hmapa : a.map f = a') :
    f (mulMatrix hb hd a).det = (mulMatrix hb' hd' a').det := by
  rw [f.map_det]
  congr 1
  ext i j
  change f (mulMatrix hb hd a i j) = mulMatrix hb' hd' a' i j
  rw [mulMatrix_entry, mulMatrix_entry, ← Polynomial.coeff_map, Polynomial.map_modByMonic f hb,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, hmapa, hmapb]

private theorem mulMatrix_det_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    {b a : R[X]} {n : ℕ} (hb : b.Monic) (hd : b.natDegree = n)
    (hcop : IsCoprime a b) : (mulMatrix hb hd a).det ≠ 0 := by
  obtain ⟨u, v, huv⟩ := hcop
  have hinv : AdjoinRoot.mk b u * AdjoinRoot.mk b a = 1 := by
    have h := congrArg (AdjoinRoot.mk b) huv
    simpa only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero, map_one] using h
  have hmat : mulMatrix hb hd u * mulMatrix hb hd a = 1 := by
    unfold mulMatrix
    rw [← map_mul, hinv, map_one]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  intro hz
  rw [hz, mul_zero] at hdet
  exact zero_ne_one hdet

/-- Cramer's rule in the full quotient by the monic block. -/
private theorem clearedSolution {R : Type*} [CommRing R] [Nontrivial R]
    {b : R[X]} {n : ℕ} (hb : b.Monic) (hd : b.natDegree = n) (a q : R[X]) :
    ∃ t : R[X], t.degree < b.degree ∧ b ∣ a * t + C (mulMatrix hb hd a).det * q := by
  let basis := quotientBasis hb hd
  let matrix := mulMatrix hb hd a
  let target := AdjoinRoot.mk b (-q)
  let solution := basis.equivFun.symm (matrix.cramer (basis.equivFun target))
  have hcoord : basis.equivFun solution = matrix.cramer (basis.equivFun target) :=
    basis.equivFun.apply_symm_apply _
  have hsol : AdjoinRoot.mk b a * solution = matrix.det • target := by
    apply basis.equivFun.injective
    have hvec := Algebra.leftMulMatrix_mulVec_repr basis (AdjoinRoot.mk b a) solution
    change matrix.mulVec (basis.repr solution) = ⇑(basis.repr (AdjoinRoot.mk b a * solution)) at hvec
    rw [← Basis.equivFun_apply, ← Basis.equivFun_apply, hcoord, Matrix.mulVec_cramer] at hvec
    rw [map_smul]
    exact hvec.symm
  obtain ⟨t, ht⟩ := AdjoinRoot.mk_surjective solution
  have hrep : AdjoinRoot.mk b (t %ₘ b) = solution := by
    rw [← AdjoinRoot.modByMonicHom_mk hb, AdjoinRoot.mk_leftInverse hb, ht]
  refine ⟨t %ₘ b, degree_modByMonic_lt _ hb, AdjoinRoot.mk_eq_zero.mp ?_⟩
  change AdjoinRoot.mk b (a * (t %ₘ b) + C matrix.det * q) = 0
  rw [map_add, map_mul, map_mul, hrep, hsol, AdjoinRoot.mk_C]
  simp [target, Algebra.smul_def]

private theorem eval_map_constants {F : Type*} [Field F] (z : F) (g : F[X]) :
    (g.map (C : F →+* F[X])).map (evalRingHom z) = g := by
  have hc : (evalRingHom z).comp (C : F →+* F[X]) = RingHom.id F :=
    RingHom.ext fun x => eval_C
  rw [Polynomial.map_map, hc, Polynomial.map_id]

/-- Solve for the multiplier of the other block in the CRT contribution.
Including that block in the multiplication matrix preserves regularity because
its class in the target quotient is a unit at every seed. -/
private theorem blockContribution {h : ℕ} (D : PoleData h) (i : Fin 2) :
    ∃ (d : L[X]) (N : Polynomial L[X]),
      d ≠ 0 ∧ N.degree < (2 * h : ℕ) ∧
      (D.block (otherBlock i)).map C ∣ N ∧
      (D.block i).map C ∣
        ((D.constant i).map C + C (Polynomial.X (R := L)) * (D.slope i).map C) * N +
          C (d * Polynomial.X (R := L)) * (D.offset i).map C ∧
      ∀ z, IsCoprime (D.constant i + C z * D.slope i) (D.block i) → d.eval z ≠ 0 := by
  let b := (D.block i).map (C : L →+* L[X])
  let e := (D.block (otherBlock i)).map (C : L →+* L[X])
  let amplitude := (D.constant i).map (C : L →+* L[X]) +
    C (Polynomial.X (R := L)) * (D.slope i).map (C : L →+* L[X])
  let a := amplitude * e
  let q := C (Polynomial.X (R := L)) * (D.offset i).map (C : L →+* L[X])
  have hb : b.Monic := (D.monic i).map _
  have he : e.Monic := (D.monic (otherBlock i)).map _
  have hbd : b.natDegree = h := ((D.monic i).natDegree_map _).trans (D.degree i)
  have hed : e.natDegree = h :=
    ((D.monic (otherBlock i)).natDegree_map _).trans (D.degree (otherBlock i))
  have hcop : IsCoprime (D.block (otherBlock i)) (D.block i) := by
    fin_cases i
    · exact D.coprime.symm
    · exact D.coprime
  let d := (mulMatrix hb hbd a).det
  have hregular (z : L) (hz : IsCoprime (D.constant i + C z * D.slope i) (D.block i)) :
      d.eval z ≠ 0 := by
    have hmapa : a.map (evalRingHom z) =
        (D.constant i + C z * D.slope i) * D.block (otherBlock i) := by
      simp only [a, amplitude, e, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        eval_map_constants, coe_evalRingHom, eval_X]
    change (evalRingHom z) (mulMatrix hb hbd a).det ≠ 0
    rw [mulMatrix_specialize (evalRingHom z) hb hbd (D.monic i) (D.degree i)
      (eval_map_constants z (D.block i)) hmapa]
    exact mulMatrix_det_ne_zero _ _ (hz.mul_left hcop)
  have hd : d ≠ 0 := by
    have hc : IsCoprime (D.constant i) (D.block i) := (D.determinant i).of_mul_left_right
    intro hd
    exact hregular 0 (by simpa using hc) (by simp [hd])
  obtain ⟨t, ht, hdiv⟩ := clearedSolution hb hbd a q
  refine ⟨d, e * t, hd, ?_, dvd_mul_right _ _, ?_, hregular⟩
  · by_cases ht0 : t = 0
    · rw [ht0, mul_zero, degree_zero]
      exact WithBot.bot_lt_coe _
    have htn : t.natDegree < h := by
      rw [degree_eq_natDegree ht0, degree_eq_natDegree hb.ne_zero, hbd, Nat.cast_lt] at ht
      exact ht
    apply (degree_mul_le e t).trans_lt
    rw [degree_eq_natDegree he.ne_zero, degree_eq_natDegree ht0, hed, ← Nat.cast_add, Nat.cast_lt]
    omega
  · change b ∣ amplitude * (e * t) + C (d * Polynomial.X (R := L)) * (D.offset i).map C
    simpa only [a, q, ← mul_assoc, ← map_mul] using hdiv

set_option maxHeartbeats 800000 in
theorem proof : CRTReady := by
  intro h _ _ D
  choose d N hN using blockContribution D
  exact ⟨⟨d, N, fun i => (hN i).1, fun i => (hN i).2.1, fun i => (hN i).2.2.1,
    fun i => (hN i).2.2.2.1, fun i => (hN i).2.2.2.2⟩⟩

end
end HighSource6921.CRT
end PackSource_K1_14_1_1Proof
section HighSourceContactNecessary
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace HighSource6921.Necessary
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_2 Polynomial
open scoped BigOperators

/-- Cancel the poles at all nodes and apply the multiplicity degree test. -/
theorem zero_of_poles_and_hits {h : ℕ} {D : PoleData h}
    (hnode : ∀ i k, (D.block i).eval (nodeL k) ≠ 0)
    {s : Shape} {W : ℕ} {Q : L[X]}
    (hdeg : Q.natDegree ≤ W+(s.B+s.J)*(2*h))
    (hpole : poleProduct D ^ (s.B+s.J) ∣ Q)
    (hits : Finset I) (hcard : 180130 ≤ hits.card)
    (hcontact : ∀ k ∈ hits, (Polynomial.X-C (nodeL k)) ^ s.m ∣ Q)
    (hW : W < s.m*180130) : Q = 0 := by
  by_contra hne
  obtain ⟨T, hT⟩ := hpole
  have hTne : T ≠ 0 := by intro he; simp [hT, he] at hne
  have hmonic : (poleProduct D).Monic := (D.monic 0).mul (D.monic 1)
  have hDdeg : (poleProduct D).natDegree = 2*h := by
    rw [poleProduct, natDegree_mul (D.monic 0).ne_zero (D.monic 1).ne_zero, D.degree, D.degree]
    omega
  have hTdeg : T.natDegree ≤ W := by
    rw [hT, natDegree_mul (pow_ne_zero _ hmonic.ne_zero) hTne, natDegree_pow, hDdeg] at hdeg
    omega
  have hroot (k : I) : IsCoprime (Polynomial.X-C (nodeL k)) (poleProduct D) := by
    refine (irreducible_X_sub_C _).coprime_iff_not_dvd.mpr ?_
    rw [dvd_iff_isRoot]
    simpa [IsRoot, poleProduct] using mul_ne_zero (hnode 0 k) (hnode 1 k)
  have hcontacts (k : I) (hk : k ∈ hits) : (Polynomial.X-C (nodeL k)) ^ s.m ∣ T :=
    ((hroot k).pow.dvd_of_dvd_mul_left (hT ▸ hcontact k hk))
  have hinj : Function.Injective nodeL := (algebraMap K L).injective.comp node.injective
  have hh := K1_11.eq_zero_of_many_contacts hits nodeL hinj s.m T hcontacts
    (hTdeg.trans_lt (hW.trans_le (Nat.mul_le_mul_left _ hcard)))
  exact hTne hh
theorem proof : ContactNecessary := by
  intro h _ _ D Crt word hnode z S hres hdeg hits hcard hhits s W hW P hP
  apply span_vanish z S _ hP
  intro Q hQ
  obtain ⟨⟨ha, hc⟩, hp⟩ := hQ
  exact zero_of_poles_and_hits hnode (composed_degree ha _ _ hdeg)
    (specialized_poles Crt hres hp) hits hcard
    (fun k hk => composed_contact hc _ _ k (hhits k hk)) hW

end
end HighSource6921.Necessary
end HighSourceContactNecessary
section PackSource_K1_14_1_3Split
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace HighSource6921.Hasse

noncomputable section

open K1 K1_14 K1_14_1 K1_14_1_3 Polynomial
open scoped Polynomial

private def evaluatedHasse (i : Fin 2) (r : ℕ) : Jet →ₗ[FX] Jet :=
  mapCoeffs (mapCoeffs (seedCoeff i r))

private theorem evaluatedHasse_eq (i : Fin 2) (r : ℕ) (P : Jet) :
    evaluatedHasse i r P = seedHasse i r P := rfl

private theorem translation_natural {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (i : Fin 2) (P : MvPolynomial (Fin 2) R) :
    (translation i P).map (MvPolynomial.map f) = translation i (MvPolynomial.map f P) := by
  let a := (Polynomial.mapRingHom (MvPolynomial.map f)).comp (translation (R := R) i).toRingHom
  let b := (translation (R := S) i).toRingHom.comp (MvPolynomial.map f)
  have hab : a = b := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [a, b, translation, MvPolynomial.algebraMap_eq]
    · intro j
      by_cases hj : j = i <;> simp [a, b, translation, hj]
  exact DFunLike.congr_fun hab P

private theorem seedCoeff_natural {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (i : Fin 2) (r : ℕ) (P : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (seedCoeff i r P) = seedCoeff i r (MvPolynomial.map f P) := by
  change MvPolynomial.map f ((translation i P).coeff r) =
    (translation i (MvPolynomial.map f P)).coeff r
  rw [← coeff_map, translation_natural]

private def ξ : FX := algebraMap (Polynomial L) FX (Polynomial.X (R := L))

private def centerBase : SeedPoly[X] →ₐ[L] Seeds :=
  eval₂AlgHom (MvPolynomial.mapAlgHom (Algebra.ofId L FX))
    (MvPolynomial.C ξ) (fun _ => Commute.all _ _)

private theorem centerBase_hasse (i : Fin 2) (r : ℕ) (Q : SeedPoly[X]) :
    centerBase (mapCoeffs (seedCoeff i r) Q) = seedCoeff i r (centerBase Q) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hp hq =>
    rw [map_add, map_add, map_add, map_add, hp, hq]
  | monomial n a =>
    rw [mapCoeffs_monomial]
    change (monomial n (seedCoeff i r a)).eval₂ (MvPolynomial.map (algebraMap L FX))
      (MvPolynomial.C ξ) = seedCoeff i r
      ((monomial n a).eval₂ (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C ξ))
    rw [eval₂_monomial, eval₂_monomial, ← map_pow]
    simp only [mul_comm _ (MvPolynomial.C (ξ ^ n)), ← MvPolynomial.smul_eq_C_mul,
      map_smul, seedCoeff_natural]

private theorem centerEval_hasse (i : Fin 2) (r : ℕ) (Q : Source) :
    centerEval (sourceHasse i r Q) = evaluatedHasse i r (centerEval Q) := by
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro k
  change ((Polynomial.mapAlgHom (Polynomial.mapAlgHom centerBase)
    (sourceHasse i r Q)).coeff j).coeff k =
      ((evaluatedHasse i r (Polynomial.mapAlgHom (Polynomial.mapAlgHom centerBase) Q)).coeff j).coeff k
  simp only [sourceHasse, evaluatedHasse, coeff_mapAlgHom_apply, mapCoeffs_coeff]
  exact centerBase_hasse i r ((Q.coeff j).coeff k)

private theorem centerBase_sourceX (E : L[X]) :
    centerBase (sourceX E) = MvPolynomial.C (algebraMap L[X] FX E) := by
  change (E.map MvPolynomial.C).eval₂ (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C ξ) = _
  rw [eval₂_map]
  have hc : (MvPolynomial.map (algebraMap L FX)).comp
      (MvPolynomial.C : L →+* SeedPoly) = MvPolynomial.C.comp (algebraMap L FX) := by
    ext a
    simp
  rw [hc]
  exact eval₂_algebraMap_X E
    ((IsScalarTower.toAlgHom L FX Seeds).comp (IsScalarTower.toAlgHom L L[X] FX))

private theorem centerEval_clear {h : ℕ} (D : PoleData h) (i : Fin 2) (r : ℕ) (Q : Source) :
    centerEval (cleared D i r Q) =
      (algebraMap L[X] FX (D.block i ^ (2*r))) • evaluatedHasse i r (centerEval Q) := by
  rw [cleared, map_mul, centerEval_hasse]
  change Polynomial.map (Polynomial.mapRingHom centerBase.toRingHom)
    (C (C (sourceX (D.block i ^ (2*r))))) * _ = _
  rw [Polynomial.map_C]
  change C (Polynomial.map centerBase.toRingHom (C (sourceX (D.block i ^ (2*r))))) * _ = _
  rw [Polynomial.map_C]
  change C (C (centerBase (sourceX (D.block i ^ (2*r))))) * _ = _
  rw [centerBase_sourceX, Algebra.smul_def]
  rfl

theorem proof : HasseClosed := by
  intro h _ _ D Crt word s W P hP i r
  have h₁ := K1_14_1_3_1.proof
  have h₂ := K1_14_1_3_2.proof
  let target := evaluated Crt word s (W+2*h*r)
  have hsub : evaluated Crt word s W ≤ target.comap (evaluatedHasse i r) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨Q, hQ, rfl⟩
      change evaluatedHasse i r (centerEval Q) ∈ target
      have hmem : cleared D i r Q ∈ complete Crt word s (W+2*h*r) :=
        ⟨⟨ambient_cleared D hQ.1.1 i r, h₁ h D word s Q hQ.1.2 i r⟩,
          h₂ h D Crt s Q hQ.2 i r⟩
      have he : centerEval (cleared D i r Q) ∈ target :=
        Submodule.subset_span ⟨cleared D i r Q, hmem, rfl⟩
      rw [centerEval_clear] at he
      have hn : algebraMap L[X] FX (D.block i ^ (2*r)) ≠ 0 := by
        rw [← map_zero (algebraMap L[X] FX)]
        exact (IsFractionRing.injective L[X] FX).ne (pow_ne_zero (2*r) (D.monic i).ne_zero)
      exact (target.smul_mem_iff hn).mp he)
  rw [← evaluatedHasse_eq]
  exact hsub hP

end
end HighSource6921.Hasse
end PackSource_K1_14_1_3Split
section PackSource_K1_14_1_6Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1200000

namespace HighSource6921.Physical

noncomputable section

open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators Polynomial

private abbrev sx : Source := Polynomial.C (Polynomial.C (Polynomial.X (R := SeedPoly)))
private abbrev sy : Source := Polynomial.C (Polynomial.X (R := SeedPoly[X]))
private abbrev sv : Source := Polynomial.X
private abbrev shiftedY : Source := sy + sx * sv
private abbrev seedC : SeedPoly →+* Source := C.comp (C.comp C)

private theorem physical_x (x r : L) : atPhysical x r sx = sx + algebraMap L Source x := by
  change Polynomial.eval₂ _ _ (Polynomial.C (Polynomial.C (Polynomial.X (R := SeedPoly)))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (Polynomial.C (Polynomial.X (R := SeedPoly))) = _
  rw [eval₂_C]
  change (algebraMap SeedPoly[X] Source) (Polynomial.eval₂ _ _ (Polynomial.X (R := SeedPoly))) = _
  rw [eval₂_X, map_add]
  rfl

private theorem physical_y (x r : L) :
    atPhysical x r sy = shiftedY + algebraMap L Source r := by
  change Polynomial.eval₂ _ _ (Polynomial.C (Polynomial.X (R := SeedPoly[X]))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (Polynomial.X (R := SeedPoly[X])) = _
  rw [eval₂_X]
  change algebraMap L Source r + sx * sv + sy = shiftedY + algebraMap L Source r
  dsimp only [shiftedY]
  ac_rfl

private theorem physical_v (x r : L) : atPhysical x r sv = sv := by
  change Polynomial.eval₂ _ _ (Polynomial.X : Source) = _
  rw [eval₂_X]

private theorem physical_seed (x r : L) (p : SeedPoly) :
    atPhysical x r (seedC p) = seedC p := by
  change Polynomial.eval₂ _ _ (C (C (C p))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (C (C p)) = _
  rw [eval₂_C]
  change (algebraMap SeedPoly[X] Source) (Polynomial.eval₂ _ _ (C p)) = _
  rw [eval₂_C]
  rfl

private theorem product_eq_monomial (p : SeedPoly) (a b j : ℕ) :
    seedC p * sx^a * sy^b * sv^j =
      monomial j (monomial b (monomial a p)) := by
  simp only [seedC, RingHom.comp_apply, sx, sy, sv, ← map_pow, ← map_mul,
    C_mul_X_pow_eq_monomial]

private theorem seed_scalar (e : Fin 2 →₀ ℕ) (c : L) :
    seedC (MvPolynomial.monomial e c) = c • seedC (MvPolynomial.monomial e 1) := by
  rw [Algebra.smul_def]
  change _ = seedC (MvPolynomial.C c) * _
  rw [← map_mul, MvPolynomial.C_mul_monomial, mul_one]

private theorem mem_of_monomials (M : Submodule L Source) (P : Source)
    (H : ∀ j b a e, coeffAt P j b a e ≠ 0 →
      monomial j (monomial b (monomial a (MvPolynomial.monomial e
        (coeffAt P j b a e)))) ∈ M) : P ∈ M := by
  rw [P.as_sum_support]
  apply M.sum_mem
  intro j _
  rw [show monomial j (P.coeff j) =
      monomial j (∑ b ∈ (P.coeff j).support, monomial b ((P.coeff j).coeff b)) from
    congrArg _ (P.coeff j).as_sum_support, map_sum]
  apply M.sum_mem
  intro b _
  let p := (P.coeff j).coeff b
  change monomial j (monomial b p) ∈ M
  rw [show p = ∑ a ∈ p.support, monomial a (p.coeff a) from p.as_sum_support]
  simp only [map_sum]
  apply M.sum_mem
  intro a _
  rw [show monomial a (p.coeff a) =
      monomial a (∑ e ∈ (p.coeff a).support, MvPolynomial.monomial e ((p.coeff a).coeff e)) from
    congrArg _ (p.coeff a).as_sum]
  simp only [map_sum]
  apply M.sum_mem
  intro e he
  exact H j b a e (MvPolynomial.mem_support_iff.mp he)

private theorem mul_add_pow_mem (M : Submodule L Source) (p u v : Source)
    (n : ℕ) (H : ∀ k ≤ n, p * u^k * v^(n-k) ∈ M) :
    p * (u+v)^n ∈ M := by
  rw [add_pow u v n, Finset.mul_sum]
  apply M.sum_mem
  intro k hk
  have h := M.smul_mem (n.choose k : L) (H k (by simpa using hk))
  rw [Algebra.smul_def, map_natCast] at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

private theorem mul_shift_pow_mem (M : Submodule L Source) (p u : Source)
    (r : L) (n : ℕ) (H : ∀ k ≤ n, p * u^k ∈ M) :
    p * (u + algebraMap L Source r)^n ∈ M := by
  apply mul_add_pow_mem
  intro k hk
  rw [mul_comm (p * u^k), ← map_pow, ← Algebra.smul_def]
  exact M.smul_mem _ (H k hk)

private structure Low (m : ℕ) where
  j : ℕ
  b : ℕ
  a : ℕ
  e : Fin 2 →₀ ℕ
  low : a + 2*b < m

/-- Keep the coefficients below contact order at an already translated node. -/
private def cut (s : Shape) : Source →ₗ[L] (Low s.m → L) where
  toFun P z := coeffAt P z.j z.b z.a z.e
  map_add' P Q := by
    funext z
    simp [coeffAt]
  map_smul' c P := by
    funext z
    simp [coeffAt, Polynomial.coeff_smul]

private abbrev SeedIdx (U : ℕ) := Σ a : Fin (U+1), Fin (U+1-a.val)

private def seedExp {U : ℕ} (i : SeedIdx U) : Fin 2 →₀ ℕ :=
  (finTwoArrowEquiv' ℕ).symm (i.1.val, i.2.val)

private theorem exists_seedIdx {U : ℕ} {e : Fin 2 →₀ ℕ} (he : seedWeight e ≤ U) :
    ∃ i : SeedIdx U, seedExp i = e := by
  let pair := finTwoArrowEquiv' ℕ e
  have hw : pair.1 + pair.2 ≤ U := by
    simpa only [pair, seedWeight, Equiv.symm_apply_apply, ← finTwoArrowEquiv'_sum_eq (d := pair)]
      using he
  refine ⟨⟨⟨pair.1, by omega⟩, ⟨pair.2, ?_⟩⟩, ?_⟩
  · change pair.2 < U+1-pair.1
    omega
  · exact (finTwoArrowEquiv' ℕ).symm_apply_apply e

private theorem seed_card (U : ℕ) : Fintype.card (SeedIdx U) = triangle U := by
  simp only [SeedIdx, Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_eq_sum_range]
  calc
    (∑ a ∈ Finset.range (U+1), (U+1-a)) = (∑ a ∈ Finset.range (U+1), (a+1)) := by
      rw [← Finset.sum_range_reflect (fun a => U+1-a) (U+1)]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [Finset.mem_range] at ha
      omega
    _ = (∑ a ∈ Finset.range (U+2), a) := by
      simpa only [Nat.add_zero] using (Finset.sum_range_succ' (fun a : ℕ => a) (U+1)).symm
    _ = triangle U := by
      rw [Finset.sum_range_id, triangle, show U+2-1 = U+1 by omega, Nat.mul_comm]

/-- Index the adapted generators that can have a nonzero truncation. -/
private abbrev GenIdx (s : Shape) :=
  (Σ q : Fin (s.B+1), Σ k : Fin (min q.val s.J+1),
    Fin (s.m + min q.val s.J - (q.val + 2*k.val))) × SeedIdx s.U

private theorem gen_card (s : Shape) :
    Fintype.card (GenIdx s) =
      shapeSum s (fun q k => s.m + min q s.J - (q + 2*k)) * triangle s.U := by
  unfold GenIdx
  rw [Fintype.card_prod, seed_card, shapeSum]
  congr 1
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range
    (fun q : ℕ => ∑ k : Fin (min q s.J+1), (s.m + min q s.J - (q + 2*k.val)))]
  refine Finset.sum_congr rfl ?_
  intro q _
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => s.m + min q s.J - (q + 2*k)) (min q s.J+1)

/-- Grade q, capped V-degree d, and k surviving factors of η. -/
private def localGen (q d k a : ℕ) (e : Fin 2 →₀ ℕ) : Source :=
  seedC (MvPolynomial.monomial e 1) * sx^a * sy^k * sv^(d-k) * shiftedY^(q-d)

private def generators (s : Shape) (i : GenIdx s) : Low s.m → L :=
  cut s (localGen i.1.1.val (min i.1.1.val s.J) i.1.2.1.val i.1.2.2.val (seedExp i.2))

private def localSpan (s : Shape) : Submodule L (Low s.m → L) :=
  Submodule.span L (Set.range (generators s))

private abbrev preimage (s : Shape) : Submodule L Source := (localSpan s).comap (cut s)

private theorem high_mono (s : Shape) (e : Fin 2 →₀ ℕ) (a b j : ℕ)
    (h : s.m ≤ a+2*b) :
    seedC (MvPolynomial.monomial e 1) * sx^a * sy^b * sv^j ∈ LinearMap.ker (cut s) := by
  apply LinearMap.mem_ker.mpr
  funext z
  change coeffAt _ z.j z.b z.a z.e = 0
  rw [product_eq_monomial]
  have hz := z.low
  by_cases hj : j = z.j
  · by_cases hb : b = z.b
    · by_cases ha : a = z.a
      · omega
      · simp [coeffAt, Polynomial.coeff_monomial, hj, hb, ha]
    · simp [coeffAt, Polynomial.coeff_monomial, hj, hb]
  · simp [coeffAt, Polynomial.coeff_monomial, hj]

private theorem collect_powers {R : Type*} [CommMonoid R] (c x y v : R)
    (a k j t n : ℕ) :
    (c * x^a * y^k * v^j) * y^t * (x*v)^n = c * x^(a+n) * y^(k+t) * v^(j+n) := by
  simp only [pow_add, mul_pow]
  ac_rfl

private theorem collect_adapted {R : Type*} [CommMonoid R] (c x y v A : R)
    (a j k n : ℕ) :
    (c * x^a * v^j * A) * y^k * (x*v)^n = c * x^(a+n) * y^k * v^(j+n) * A := by
  simp only [pow_add, mul_pow]
  ac_rfl

private theorem move_v {R : Type*} [CommMonoid R] (c v x y : R) :
    c * v * x * y = c * x * y * v := by ac_rfl

private theorem high_gen (s : Shape) (q d k a : ℕ) (e : Fin 2 →₀ ℕ)
    (h : s.m ≤ a+(q-d)+2*k) : localGen q d k a e ∈ LinearMap.ker (cut s) := by
  unfold localGen
  change _ * (sy + sx * sv)^(q-d) ∈ _
  apply mul_add_pow_mem
  intro t ht
  have ht' := high_mono s e (a+(q-d-t)) (k+t) (d-k+(q-d-t)) (by omega)
  rw [collect_powers]
  exact ht'

private theorem gen_mem (s : Shape) (q k a : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : q ≤ s.B) (hk : k ≤ min q s.J) (he : seedWeight e ≤ s.U) :
    localGen q (min q s.J) k a e ∈ preimage s := by
  change cut s _ ∈ localSpan s
  have hd : min q s.J ≤ q := min_le_left _ _
  by_cases ha : a < s.m + min q s.J - (q+2*k)
  · obtain ⟨i, rfl⟩ := exists_seedIdx he
    exact Submodule.subset_span
      ⟨(⟨⟨q, Nat.lt_succ_of_le hq⟩, ⟨⟨k, Nat.lt_succ_of_le hk⟩, ⟨a, ha⟩⟩⟩, i), rfl⟩
  · rw [LinearMap.mem_ker.mp (high_gen s q (min q s.J) k a e (by omega))]
    exact (localSpan s).zero_mem

private theorem shifted_mono_mem (s : Shape) (a b j : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : b+j ≤ s.B) (hj : j ≤ s.J) (he : seedWeight e ≤ s.U) :
    seedC (MvPolynomial.monomial e 1) * sx^a * shiftedY^b * sv^j ∈ preimage s := by
  let q := b+j
  let d := min q s.J
  have hd : d ≤ q := min_le_left _ _
  have hjd : j ≤ d := le_min (Nat.le_add_left _ _) hj
  let p := seedC (MvPolynomial.monomial e 1) * sx^a * sv^j * shiftedY^(q-d)
  have hpow : shiftedY^b = shiftedY^(q-d) * shiftedY^(d-j) := by
    rw [← pow_add, show q-d+(d-j) = b by dsimp only [q] at *; omega]
  have hexpand : p * (sy + sx*sv)^(d-j) ∈ preimage s := by
    apply mul_add_pow_mem
    intro k hk
    have hV : d-k = j+(d-j-k) := by omega
    have hgen := gen_mem s q k (a+(d-j-k)) e hq (by omega) he
    change localGen q d k (a+(d-j-k)) e ∈ _ at hgen
    rw [localGen, hV] at hgen
    dsimp only [p]
    rw [collect_adapted]
    exact hgen
  dsimp only [p] at hexpand
  change (seedC (MvPolynomial.monomial e 1) * sx^a * sv^j * shiftedY^(q-d)) *
    shiftedY^(d-j) ∈ preimage s at hexpand
  rw [move_v (seedC (MvPolynomial.monomial e 1) * sx^a), mul_assoc
    (seedC (MvPolynomial.monomial e 1) * sx^a), ← hpow] at hexpand
  exact hexpand

private theorem translated_mono_mem (s : Shape) (x r : L) (a b j : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : b+j ≤ s.B) (hj : j ≤ s.J) (he : seedWeight e ≤ s.U) :
    seedC (MvPolynomial.monomial e 1) * (sx + algebraMap L Source x)^a *
      (shiftedY + algebraMap L Source r)^b * sv^j ∈ preimage s := by
  let p := seedC (MvPolynomial.monomial e 1) * sv^j
  have h : (p * (shiftedY + algebraMap L Source r)^b) *
      (sx + algebraMap L Source x)^a ∈ preimage s := by
    apply mul_shift_pow_mem
    intro t _
    have h' : (p * sx^t) * (shiftedY + algebraMap L Source r)^b ∈ preimage s := by
      apply mul_shift_pow_mem
      intro k hk
      dsimp only [p]
      rw [move_v]
      exact shifted_mono_mem s t k j e (by omega) hj he
    rw [mul_right_comm]
    exact h'
  rw [mul_right_comm p] at h
  dsimp only [p] at h
  rw [move_v] at h
  exact h

private theorem atPhysical_mem (h : ℕ) (s : Shape) (W : ℕ) (x r : L)
    (P : ambient h s W) : cut s (atPhysical x r P.val) ∈ localSpan s := by
  change P.val ∈ (preimage s).comap (atPhysical x r).toLinearMap
  apply mem_of_monomials
  intro j b a e hne
  have hel : trueEligible h s W j b a e := by
    by_contra hn
    exact hne (P.property j b a e hn)
  obtain ⟨hq, hj, he, _⟩ := hel
  change atPhysical x r _ ∈ preimage s
  rw [← product_eq_monomial, seed_scalar, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, map_smul]
  apply (preimage s).smul_mem
  simp only [map_mul, map_pow, physical_x, physical_y, physical_v, physical_seed]
  exact translated_mono_mem s x r a b j e hq hj he

private def nodeMap (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) (i : I) :
    ambient h s W →ₗ[L] localSpan s :=
  LinearMap.codRestrict (localSpan s)
    (((cut s).comp (atPhysical (nodeL i) (word i)).toLinearMap).domRestrict (ambient h s W))
    (atPhysical_mem h s W (nodeL i) (word i))

private theorem localSpan_finrank (s : Shape) :
    Module.finrank L (localSpan s) ≤
      shapeSum s (fun q k => s.m + min q s.J - (q + 2*k)) * triangle s.U := by
  rw [← gen_card]
  exact finrank_range_le_card (R := L) (generators s)

theorem proof : ContactRank := by
  classical
  intro h _ _ word s W
  by_cases hzero : Module.finrank L (ambient h s W) = 0
  · simp [hzero]
  have : Module.Finite L (ambient h s W) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hzero)
  have : Module.Finite L (localSpan s) :=
    Module.Finite.span_of_finite L (Set.finite_range (generators s))
  let f : ambient h s W →ₗ[L] (I → localSpan s) :=
    LinearMap.pi (nodeMap h word s W)
  let g : LinearMap.ker f →ₗ[L] contacted h word s W :=
    LinearMap.codRestrict (contacted h word s W)
      ((ambient h s W).subtype.comp (LinearMap.ker f).subtype) (by
        intro P
        refine ⟨P.val.property, ?_⟩
        intro i a b j e hab
        have hz := LinearMap.mem_ker.mp P.property
        exact congrArg (fun z : I → localSpan s => (z i).val ⟨j, b, a, e, hab⟩) hz)
  have hg : Function.Injective g := by
    intro P Q hPQ
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun R : contacted h word s W => R.val) hPQ
  have hle : contacted h word s W ≤ ambient h s W := inf_le_left
  have : Module.Finite L (contacted h word s W) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hker := LinearMap.finrank_le_finrank_of_injective hg
  have hnull := f.finrank_range_add_finrank_ker
  have htarget : Module.finrank L (I → localSpan s) ≤ physicalDebit s := by
    rw [Module.finrank_pi_fintype]
    calc
      (∑ _ : I, Module.finrank L (localSpan s)) ≤
          ∑ _ : I, (shapeSum s (fun q k => s.m + min q s.J - (q + 2*k))) * triangle s.U :=
        Finset.sum_le_sum (fun _ _ => localSpan_finrank s)
      _ = physicalDebit s := by
        rw [Finset.sum_const, Finset.card_univ, ProximityPrize.Benchmark.IRSProfile.card_index,
          smul_eq_mul, physicalDebit]
        ac_rfl
  have hrange := (LinearMap.range f).finrank_le.trans htarget
  omega

end

end HighSource6921.Physical
end PackSource_K1_14_1_6Proof
