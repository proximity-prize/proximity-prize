import ProximityPrize.SubmissionLower.MovingSourceThickClearing6814

/-! Apply the primary-thickening lemma to actual Source helper identities,
then show that removing the clearing gcd preserves the SAME thickness. -/
namespace ProximityPrize.SubmissionLower.MovingSourceThickCuts6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open RCN136 RCN207 RCN313 SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetClearedHelper
open MovingFiberThreeSources6811 MovingSourceClearing6814 MovingSourceThickClearing6814

theorem cleared_change_degree_mem_primary
    {R : Type*} [CommRing R] (J : Ideal R) [J.IsMaximal]
    (surface A B : R) (d n m : ℕ) (P : Polynomial R)
    (hn : P.natDegree≤n) (hm : P.natDegree≤m) (hA : A∉J)
    (hmem : cleared P n A B∈Ideal.span {surface} ⊔ J^d) :
    cleared P m A B∈Ideal.span {surface} ⊔ J^d := by
  let I := Ideal.span {surface} ⊔ J^d
  let q := Ideal.Quotient.mk I
  obtain ⟨u,hu⟩ := unit_mod_thickening J surface d A hA
  change (↑u : R ⧸ I)=q A at hu
  let y : R ⧸ I := (↑u⁻¹ : R ⧸ I)*q B
  have hy : q A*y=q B := by simp [y,←hu,←mul_assoc]
  have hz : q (cleared P n A B)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_cleared,cleared_eval _ _ (Polynomial.natDegree_map_le.trans hn) _ _ y hy] at hz
  have he := ((unit_mod_thickening J surface d A hA).pow n).mul_left_cancel
    (hz.trans (mul_zero _).symm)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (cleared P m A B)=0
  rw [map_cleared,cleared_eval _ _ (Polynomial.natDegree_map_le.trans hm) _ _ y hy,he,mul_zero]

theorem source_cut_mem_primary
    {K Ω R : Type} [Field K] [CharP K 2130706433] [Field Ω] [CommRing R]
    (phi : Polynomial K →+* Ω) (ev : MvPolynomial (Fin 3) Ω →+* R)
    (F : MvPolynomial (Fin 4) K) (S : Source F)
    (Q A : MvPolynomial (Fin 3) Ω) (target : Ω)
    (J : Ideal R) [J.IsMaximal] (surface : R) (d : ℕ)
    (hd : d≤S.d) (hchar : d≤2130706433)
    (hF : ev (surfaceMap phi F)∈Ideal.span {surface})
    (hH : ev (surfaceMap phi (2*polyH K F))∉J) (hA : ev (2*A)∉J)
    (hM : ev (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)∈J) :
    ev (movingCut phi S.P S.s Q A target)∈Ideal.span {surface} ⊔ J^d := by
  let psi := ev.comp (surfaceMap phi)
  let P := (asS S.P).map psi
  have hdegree : P.natDegree≤S.s := Polynomial.natDegree_map_le.trans (by
    simpa using SecondJetHelperWeights.asS_derivative_degree S.P S.s 0 S.hS)
  have hhelpers (j : ℕ) (hj : j<d) :
      cleared ((Polynomial.derivative)^[j] P) (S.s-j) (psi (2*polyH K F)) (psi (polyG K F))∈Ideal.span {surface} := by
    have hjk : j≤S.k := by change d≤S.k+1 at hd; omega
    have hm := (Ideal.span {surface}).mem_of_dvd (map_dvd psi (S.hdiv j hjk)) hF
    simpa only [helper,map_cleared,asS_iterate,Polynomial.iterate_derivative_map,P] using hm
  have hf (j : ℕ) (hj : j<d) : IsUnit (j.factorial : R) := by
    have hk : IsUnit (j.factorial : K) := isUnit_iff_ne_zero.mpr
      (SecondJetOwnShape.factorial_ne j (by omega))
    simpa only [map_natCast] using hk.map (psi.comp MvPolynomial.C)
  have hm : psi (2*polyH K F)*ev (MvPolynomial.C target-Q)-ev (2*A)*psi (polyG K F)∈J := by
    have he : psi (2*polyH K F)*ev (MvPolynomial.C target-Q)-ev (2*A)*psi (polyG K F)=
        2*ev (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) := by
      simp only [psi,RingHom.comp_apply,movingEquation,map_sub,map_mul,map_ofNat]
      ring
    rw [he]
    exact J.mul_mem_left _ hM
  have hh := cleared_mem_primary_of_helpers J surface (psi (2*polyH K F)) (psi (polyG K F))
    (ev (2*A)) (ev (MvPolynomial.C target-Q)) S.s d P hdegree hH hA hm hf hhelpers
  simpa only [movingCut,map_cleared,coefficients,Polynomial.map_map,P,psi] using hh

/-- A Source may store a conservative S-degree cap. Removing the extra
clearing powers is legitimate on this primary piece, so the sharp
ordinary factor flags do not need an equality assumption on that cap. -/
theorem source_cut_at_degree_mem_primary
    {K Ω R : Type} [Field K] [CharP K 2130706433] [Field Ω] [CommRing R]
    (phi : Polynomial K →+* Ω) (ev : MvPolynomial (Fin 3) Ω →+* R)
    (F : MvPolynomial (Fin 4) K) (S : Source F)
    (Q A : MvPolynomial (Fin 3) Ω) (target : Ω)
    (J : Ideal R) [J.IsMaximal] (surface : R) (d n : ℕ)
    (hn : S.P.degreeOf 1≤n) (hd : d≤S.d) (hchar : d≤2130706433)
    (hF : ev (surfaceMap phi F)∈Ideal.span {surface})
    (hH : ev (surfaceMap phi (2*polyH K F))∉J) (hA : ev (2*A)∉J)
    (hM : ev (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)∈J) :
    ev (movingCut phi S.P n Q A target)∈Ideal.span {surface} ⊔ J^d := by
  have hfull := source_cut_mem_primary phi ev F S Q A target J surface d hd hchar hF hH hA hM
  have hn' : ((coefficients phi S.P).map ev).natDegree≤n :=
    Polynomial.natDegree_map_le.trans (Polynomial.natDegree_map_le.trans
      ((MovingSourceNativeFactor6814.asS_natDegree S.P).trans_le hn))
  have hs' : ((coefficients phi S.P).map ev).natDegree≤S.s :=
    Polynomial.natDegree_map_le.trans (Polynomial.natDegree_map_le.trans (by
      simpa using SecondJetHelperWeights.asS_derivative_degree S.P S.s 0 S.hS))
  simp only [movingCut,map_cleared] at hfull ⊢
  exact cleared_change_degree_mem_primary J surface _ _ d S.s n _ hs' hn' hA hfull

section Normalization
variable {A : Type*} [CommRing A] [IsDomain A]
  [GCDMonoid (Polynomial A)] [NormalizationMonoid (Polynomial A)]
  [UniqueFactorizationMonoid (Polynomial A)]

/-- Removing the common clearing gcd loses neither membership nor local
multiplicity: the gcd is a unit modulo the primary thickening. -/
theorem normalized_pair_mem_primary
    (P Q : Polynomial A) (n m : ℕ) (h q : A)
    (hP : P≠0) (hn : P.natDegree≤n) (hm : Q.natDegree≤m) (hh : h≠0) (hrel : IsRelPrime P Q)
    {R : Type*} [CommRing R] (ev : Polynomial A →+* R)
    (J : Ideal R) [J.IsMaximal] (surface : R) (d : ℕ)
    (hden : ev (Polynomial.C h)∉J)
    (hleft : ev (targetPolynomial P n h q)∈Ideal.span {surface} ⊔ J^d)
    (hright : ev (targetPolynomial Q m h q)∈Ideal.span {surface} ⊔ J^d) :
    ev (RCN259.leftGCDQuotient (targetPolynomial P n h q) (targetPolynomial Q m h q))∈
        Ideal.span {surface} ⊔ J^d ∧
    ev (RCN259.rightGCDQuotient (targetPolynomial P n h q) (targetPolynomial Q m h q))∈
        Ideal.span {surface} ⊔ J^d := by
  let B := targetPolynomial P n h q
  let C := targetPolynomial Q m h q
  let I := Ideal.span {surface} ⊔ J^d
  let red := Ideal.Quotient.mk I
  let evJ := (Ideal.Quotient.mk J).comp ev
  letI : Field (R ⧸ J) := Ideal.Quotient.field J
  have hnz : evJ (Polynomial.C h)≠0 := by
    intro hz
    exact hden (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hg : ev (gcd B C)∉J := by
    intro hmem
    exact MovingSourceSaturation6814.cleared_gcd_nonzero_at P Q n m h q hP hn hm hh hrel evJ hnz
      (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have hu : IsUnit (red (ev (gcd B C))) := unit_mod_thickening J surface d _ hg
  have htransfer (N T : Polynomial A) (heq : T=gcd B C*N) (hT : ev T∈I) : ev N∈I := by
    have hz : red (ev T)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hT
    rw [heq,map_mul,map_mul] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hu.mul_left_cancel (hz.trans (mul_zero _).symm))
  exact ⟨htransfer _ B (RCN259.left_eq_gcd_mul_leftGCDQuotient B C) hleft,
    htransfer _ C (RCN259.right_eq_gcd_mul_rightGCDQuotient B C) hright⟩
end Normalization

#print axioms source_cut_mem_primary
#print axioms source_cut_at_degree_mem_primary
#print axioms normalized_pair_mem_primary
end
end ProximityPrize.SubmissionLower.MovingSourceThickCuts6814
