import ProximityPrize.SubmissionLower.MergedInfra6815_32
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.MovingSourceThickClearing6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open Polynomial SecondJetClearedHelper

theorem eval_zero_of_nilpotent_difference
    {R : Type*} [CommRing R] (P : Polynomial R) (x y : R) (d : ℕ)
    (hunit : ∀ j<d, IsUnit (j.factorial : R))
    (hderiv : ∀ j<d, ((Polynomial.derivative)^[j] P).eval x=0)
    (hdiff : (y-x)^d=0) : P.eval y=0 := by
  have hcoeff (j : ℕ) (hj : j<d) : (Polynomial.taylor x P).coeff j=0 := by
    rw [Polynomial.taylor_coeff]
    have he0 := congrFun (Polynomial.factorial_smul_hasseDeriv (R:=R) (k:=j)) P
    change j.factorial • (Polynomial.hasseDeriv j P)=((Polynomial.derivative)^[j] P) at he0
    have he := congrArg (fun Q : Polynomial R => Q.eval x) he0
    simp only [nsmul_eq_mul,Polynomial.eval_mul,Polynomial.eval_natCast,hderiv j hj] at he
    exact (hunit j hj).mul_left_cancel (he.trans (mul_zero _).symm)
  obtain ⟨Q,hQ⟩ := Polynomial.X_pow_dvd_iff.mpr hcoeff
  have he := congrArg (fun Q : Polynomial R => Q.eval (y-x)) hQ
  rw [Polynomial.taylor_eval_sub,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,hdiff,zero_mul] at he
  exact he

theorem unit_mod_thickening
    {R : Type*} [CommRing R] (J : Ideal R) [J.IsMaximal]
    (surface : R) (d : ℕ) (h : R) (hh : h∉J) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {surface} ⊔ J^d) h) := by
  have hu := Ideal.Quotient.isUnit_mk_pow_of_notMem J (n:=d) hh
  have hm := hu.map (Ideal.Quotient.factor (show J^d≤Ideal.span {surface} ⊔ J^d from le_sup_right))
  simpa only [Ideal.Quotient.factor_mk] using hm

theorem cleared_mem_primary_of_helpers
    {R : Type*} [CommRing R] (J : Ideal R) [J.IsMaximal]
    (surface H G A B : R) (s d : ℕ) (P : Polynomial R)
    (hdegree : P.natDegree≤s)
    (hH : H∉J) (hA : A∉J) (hM : H*B-A*G∈J)
    (hfact : ∀ j<d, IsUnit (j.factorial : R))
    (hhelpers : ∀ j<d, cleared ((Polynomial.derivative)^[j] P) (s-j) H G∈Ideal.span {surface}) :
    cleared P s A B∈Ideal.span {surface} ⊔ J^d := by
  let I := Ideal.span {surface} ⊔ J^d
  let q := Ideal.Quotient.mk I
  obtain ⟨u,hu⟩ := unit_mod_thickening J surface d H hH
  obtain ⟨v,hv⟩ := unit_mod_thickening J surface d A hA
  change (↑u : R ⧸ I)=q H at hu
  change (↑v : R ⧸ I)=q A at hv
  let x : R ⧸ I := (↑u⁻¹ : R ⧸ I)*q G
  let y : R ⧸ I := (↑v⁻¹ : R ⧸ I)*q B
  have hx : q H*x=q G := by simp [x,←hu,←mul_assoc]
  have hy : q A*y=q B := by simp [y,←hv,←mul_assoc]
  have hh : ∀ j<d, ((Polynomial.derivative)^[j] (P.map q)).eval x=0 := by
    intro j hj
    have hm : cleared ((Polynomial.derivative)^[j] P) (s-j) H G∈I :=
      (show Ideal.span {surface}≤I from le_sup_left) (hhelpers j hj)
    have he : q (cleared ((Polynomial.derivative)^[j] P) (s-j) H G)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hm
    rw [map_cleared] at he
    have hdeg : (((Polynomial.derivative)^[j] P).map q).natDegree≤s-j :=
      Polynomial.natDegree_map_le.trans ((Polynomial.natDegree_iterate_derivative P j).trans
        (Nat.sub_le_sub_right hdegree j))
    rw [cleared_eval _ _ hdeg _ _ x hx,←Polynomial.iterate_derivative_map] at he
    exact ((unit_mod_thickening J surface d H hH).pow (s-j)).mul_left_cancel
      (he.trans (mul_zero _).symm)
  have hdiff : (y-x)^d=0 := by
    have hpow : (H*B-A*G)^d∈I :=
      (show J^d≤I from le_sup_right) (Ideal.pow_mem_pow hM d)
    have he : q (H*B-A*G)^d=0 := by
      rw [←map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hpow
    have hrel : q H*q A*(y-x)=q (H*B-A*G) := by
      rw [map_sub,map_mul,map_mul]
      calc
        _=q H*(q A*y)-q A*(q H*x) := by ring
        _=_ := by rw [hy,hx]
    rw [←hrel,mul_pow] at he
    exact (((unit_mod_thickening J surface d H hH).mul
      (unit_mod_thickening J surface d A hA)).pow d).mul_left_cancel
      (he.trans (mul_zero _).symm)
  have hf (j : ℕ) (hj : j<d) : IsUnit (j.factorial : R ⧸ I) := by
    simpa only [map_natCast] using (hfact j hj).map q
  have hz := eval_zero_of_nilpotent_difference (P.map q) x y d hf hh hdiff
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (cleared P s A B)=0
  rw [map_cleared,cleared_eval _ _ (Polynomial.natDegree_map_le.trans hdegree) _ _ y hy,hz,mul_zero]

end
end ProximityPrize.SubmissionLower.MovingSourceThickClearing6814
end MergedPart0
section MergedPart1
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

end
end ProximityPrize.SubmissionLower.MovingSourceThickCuts6814
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.MovingSourcePairPrimary6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN225 RCN307 RCN309

def thickPiece {R I : Type*} [CommRing R]
    (surface : I → R) (relation : I → Ideal R) (d : I → ℕ) (i : I) : Ideal R :=
  Ideal.span {surface i} ⊔ relation i^d i

theorem thickPieces_coprime {R I : Type*} [CommRing R]
    (surface : I → R) (relation : I → Ideal R) (d : I → ℕ)
    (hcop : Pairwise fun i j => IsCoprime (relation i) (relation j)) :
    Pairwise fun i j => IsCoprime (thickPiece surface relation d i) (thickPiece surface relation d j) := by
  intro i j hij
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply top_unique
  rw [←Ideal.pow_sup_pow_eq_top (hcop hij).sup_eq (m:=d i) (n:=d j)]
  exact sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right)

section Certificates
variable {R I : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] [Fintype I]

def sourcePairCertificate
    (P Q : Polynomial R) (surface : I → Polynomial R)
    [∀ i,(Ideal.span {surface i}).IsPrime]
    (relation : I → Ideal (Polynomial R))
    (relationBar : ∀ i, Ideal (SurfaceQuotient (surface i)))
    [∀ i,(relationBar i).IsMaximal]
    [∀ i,IsNoetherianRing (SurfaceQuotient (surface i))]
    (hbar : ∀ i, relationBar i=Ideal.map (Ideal.Quotient.mk (Ideal.span {surface i})) (relation i))
    (hbarNe : ∀ i,relationBar i≠⊥)
    [∀ i,IsLocalHom (algebraMap R (Localization.AtPrime (relationBar i)))]
    [∀ i,FiniteDimensional (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime (relationBar i)))]
    (d : I → ℕ)
    (hP : ∀ i,P∈thickPiece surface relation d i)
    (hQ : ∀ i,Q∈thickPiece surface relation d i)
    (hcop : Pairwise fun i j => IsCoprime (relation i) (relation j)) :
    PrimaryPiecesCertificate P Q (fun i => d i*Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime (relationBar i)))) where
  pieces := thickPiece surface relation d
  coprime := thickPieces_coprime surface relation d hcop
  contains i := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · exact hx ▸ hP i
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hQ i
  length_le i := exponent_mul_residueDegree_le_length_span_surface_sup_relation_pow
    (R:=R) (surface i) (relation i) (relationBar i) (hbar i) (hbarNe i) (d i)

theorem thickPiece_finite
    (surface : I → Polynomial R) (relation : I → Ideal (Polynomial R)) (d : I → ℕ)
    (hmonic : ∀ i, ∃ M : Polynomial R, M.Monic ∧ M∈relation i) (i : I) :
    Module.Finite R (Polynomial R ⧸ thickPiece surface relation d i) := by
  obtain ⟨M,hM,hmem⟩ := hmonic i
  exact moduleFinite_quotient_of_monic_mem (thickPiece surface relation d i)
    (M^d i) (hM.pow _) ((show relation i^d i≤thickPiece surface relation d i from le_sup_right)
      (Ideal.pow_mem_pow hmem (d i)))

def swapCertificate {P Q : Polynomial R} {d : I → ℕ} (C : PrimaryPiecesCertificate P Q d) :
    PrimaryPiecesCertificate Q P d where
  pieces := C.pieces
  coprime := C.coprime
  contains i := by simpa only [intersectionIdeal,Set.pair_comm] using C.contains i
  length_le := C.length_le
end Certificates

end
end ProximityPrize.SubmissionLower.MovingSourcePairPrimary6814
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingSourcePairResultant6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN143 RCN307 MovingSourcePairPrimary6814
variable {Base : Type} [Field Base]
local instance : DecidableEq Base := Classical.decEq Base

theorem coprime_resultant_ne_zero
    (P Q : Polynomial (Polynomial Base)) (hP : P≠0) (hcop : IsRelPrime P Q) :
    Polynomial.resultant P Q P.natDegree Q.natDegree≠0 := by
  let R := Polynomial Base
  let E := FractionRing R
  let f : R →+* E := algebraMap R E
  letI : Algebra (Polynomial R) (Polynomial E) := Polynomial.algebra R E
  letI : IsLocalization ((nonZeroDivisors R).map (Polynomial.C : R →+* Polynomial R).toMonoidHom)
      (Polynomial E) := Polynomial.isLocalization (nonZeroDivisors R) E
  letI : Module.Flat (Polynomial R) (Polynomial E) := IsLocalization.flat _
    ((nonZeroDivisors R).map (Polynomial.C : R →+* Polynomial R).toMonoidHom)
  have hinj : Function.Injective f := IsFractionRing.injective R E
  have hrel : IsRelPrime (P.map f) (Q.map f) :=
    MovingSourceFlatBaseChange6814.map_isRelPrime_of_flat (A:=Polynomial R) (B:=Polynomial E)
      (Polynomial.map_injective f hinj) P Q hP hcop
  have hr := Polynomial.resultant_ne_zero (P.map f) (Q.map f) hrel.isCoprime
  rw [Polynomial.natDegree_map_eq_of_injective hinj,Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.resultant_map_map] at hr
  intro hz
  exact hr (by rw [hz,map_zero])

theorem C_dvd_of_local_residue_zero
    (I : Ideal (Polynomial Base)) [I.IsPrime] (f : Polynomial Base) (hI : I=Ideal.span {f})
    (P : Polynomial (Polynomial Base))
    (hz : (P.map (algebraMap (Polynomial Base) (LocalBase I))).map (IsLocalRing.residue (LocalBase I))=0) :
    Polynomial.C f∣P := by
  apply (Polynomial.C_dvd_iff_dvd_coeff f P).mpr
  intro n
  have he := congrArg (fun Q : Polynomial (IsLocalRing.ResidueField (LocalBase I)) => Q.coeff n) hz
  simp only [Polynomial.coeff_map,Polynomial.coeff_zero] at he
  have hm : algebraMap (Polynomial Base) (LocalBase I) (P.coeff n)∈IsLocalRing.maximalIdeal (LocalBase I) := by
    rw [←IsLocalRing.ker_residue]
    exact he
  have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff (LocalBase I) I (P.coeff n)).mp hm
  rw [hI,Ideal.mem_span_singleton] at hmem
  exact hmem

theorem some_local_residue_ne_zero
    (I : Ideal (Polynomial Base)) [I.IsPrime] (f : Polynomial Base)
    (hI : I=Ideal.span {f}) (hf : Irreducible f)
    (P Q : Polynomial (Polynomial Base)) (hcop : IsRelPrime P Q) :
    (P.map (algebraMap (Polynomial Base) (LocalBase I))).map (IsLocalRing.residue (LocalBase I))≠0 ∨
    (Q.map (algebraMap (Polynomial Base) (LocalBase I))).map (IsLocalRing.residue (LocalBase I))≠0 := by
  by_cases hp : (P.map (algebraMap (Polynomial Base) (LocalBase I))).map (IsLocalRing.residue (LocalBase I))=0
  · right
    intro hq
    exact hf.not_isUnit (Polynomial.isUnit_C.mp (hcop
      (C_dvd_of_local_residue_zero I f hI P hp) (C_dvd_of_local_residue_zero I f hI Q hq)))
  · exact Or.inl hp

theorem grouped_pair_power_dvd
    (I : Ideal (Polynomial Base)) [I.IsPrime] (f : Polynomial Base)
    (hI : I=Ideal.span {f}) (hf : Irreducible f) (hfmonic : f.Monic)
    (P Q : Polynomial (Polynomial Base)) (m n : ℕ)
    (hP : P.natDegree≤m) (hQ : Q.natDegree≤n)
    (hcop : IsRelPrime P Q) (hres : Polynomial.resultant P Q m n≠0)
    {A : Type*} [Fintype A] (weight : A → ℕ)
    (C : PrimaryPiecesCertificate
      (P.map (algebraMap (Polynomial Base) (LocalBase I)))
      (Q.map (algebraMap (Polynomial Base) (LocalBase I))) weight)
    [Module.Finite (LocalBase I) (∀ a, Polynomial (LocalBase I) ⧸ C.pieces a)] :
    f^(∑ a, weight a)∣Polynomial.resultant P Q m n := by
  rcases some_local_residue_ne_zero I f hI hf P Q hcop with hp | hq
  · exact grouped_resultant_power_dvd_of_primary_pieces_of_surface_mod_ne_zero
      I f weight hI hf hfmonic P Q m n _ _ rfl rfl
      (Polynomial.natDegree_map_le.trans hP) (Polynomial.natDegree_map_le.trans hQ) hres hp C
  · have hr : Polynomial.resultant Q P n m≠0 := by
      rw [Polynomial.resultant_comm]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hres
    letI : Module.Finite (LocalBase I)
        (∀ a, Polynomial (LocalBase I) ⧸ (swapCertificate C).pieces a) :=
      (inferInstance : Module.Finite (LocalBase I) (∀ a, Polynomial (LocalBase I) ⧸ C.pieces a))
    have hb := grouped_resultant_power_dvd_of_primary_pieces_of_surface_mod_ne_zero
      I f weight hI hf hfmonic Q P n m _ _ rfl rfl
      (Polynomial.natDegree_map_le.trans hQ) (Polynomial.natDegree_map_le.trans hP)
      hr hq (swapCertificate C)
    rw [Polynomial.resultant_comm P Q m n]
    exact dvd_mul_of_dvd_right hb _

end
end ProximityPrize.SubmissionLower.MovingSourcePairResultant6814
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.MovingSourceExtendedCoefficients6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 20000
open MvPolynomial RCN135 RCN136
open MovingSourceClearing6814 MovingSourceGenericField6814 MovingSourceFlatBaseChange6814
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K E : Type} [Field K] [Field E]

def codeMap (f : GenericField K →+* E) : Polynomial K →+* E :=
  f.comp (polynomialEmbedding K)

theorem codeMap_injective (f : GenericField K →+* E) : Function.Injective (codeMap f) :=
  f.injective.comp (polynomialEmbedding_injective K)

theorem extended_sourceMap (f : GenericField K →+* E) (P : WholeSpaceCube6814.Poly (K:=K)) :
    sourceMap K (codeMap f) P=MvPolynomial.map f (genericSourceMap K P) := by
  simp only [sourceMap,genericSourceMap,codeMap,RingHom.comp_apply,MvPolynomial.map_map]

theorem extended_coefficients_ne_zero (f : GenericField K →+* E)
    (P : WholeSpaceCube6814.Poly (K:=K)) (hP : P≠0) : coefficients (codeMap f) P≠0 := by
  intro hz
  apply hP
  apply (SecondJetCoefficients.asS (K:=K)).injective
  apply Polynomial.map_injective (surfaceMap (codeMap f))
    (surfaceMap_injective (codeMap f) (codeMap_injective f))
  simpa only [coefficients,map_zero,Polynomial.map_zero] using hz

theorem extended_coefficients_degree (f : GenericField K →+* E)
    (P : WholeSpaceCube6814.Poly (K:=K)) :
    (coefficients (codeMap f) P).natDegree≤P.degreeOf 1 := by
  exact Polynomial.natDegree_map_le.trans_eq (MovingSourceNativeFactor6814.asS_natDegree P)

theorem extended_coefficients_relPrime (f : GenericField K →+* E)
    (P Q : WholeSpaceCube6814.Poly (K:=K)) (hP : P≠0) (hrel : IsRelPrime P Q) :
    IsRelPrime (coefficients (codeMap f) P) (coefficients (codeMap f) Q) := by
  letI : Algebra (GenericField K) E := f.toAlgebra
  letI : Module.Flat (MvPolynomial (Fin 4) (GenericField K)) (MvPolynomial (Fin 4) E) := coefficient_map_flat
  have hsource : genericSourceMap K P≠0 := by
    intro hz
    have hv := view_sourceMap K (polynomialEmbedding K) P
    change MvPolynomial.finSuccEquiv (GenericField K) 3 (genericSourceMap K P)=
      coefficients (polynomialEmbedding K) P at hv
    rw [hz,map_zero] at hv
    exact MovingSourceCoprimeCuts6814.generic_coefficients_ne_zero K P hP hv.symm
  have hc := map_isRelPrime_of_flat
    (MvPolynomial.map_injective (algebraMap (GenericField K) E) (algebraMap (GenericField K) E).injective)
    (genericSourceMap K P) (genericSourceMap K Q) hsource (genericSourceMap_relPrime K P Q hP hrel)
  have hc' : IsRelPrime (sourceMap K (codeMap f) P) (sourceMap K (codeMap f) Q) := by
    rw [extended_sourceMap,extended_sourceMap]
    exact hc
  have hv := isRelPrime_equiv (MvPolynomial.finSuccEquiv E 3).toRingEquiv _ _ hc'
  change IsRelPrime (MvPolynomial.finSuccEquiv E 3 (sourceMap K (codeMap f) P))
    (MvPolynomial.finSuccEquiv E 3 (sourceMap K (codeMap f) Q)) at hv
  simpa only [view_sourceMap] using hv

end
end ProximityPrize.SubmissionLower.MovingSourceExtendedCoefficients6814
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.MovingSourceExtendedThickPair6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open MvPolynomial RCN095 RCN135 RCN136 RCN207 RCN259
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceClearing6814 MovingSourceCoprimeCuts6814 MovingSourceGenericCuts6814
open MovingSourceCoupledClearing6814 MovingSourceThickCuts6814
open MovingSourceExtendedCoefficients6814

variable {K E : Type} [Field K] [CharP K 2130706433] [Field E]
variable (f : GenericField K →+* E)
local notation "Omega" => E
local notation "OmegaT" => GenericField E
local notation "Poly3" => MvPolynomial (Fin 3) E
local notation "Poly3T" => MvPolynomial (Fin 3) OmegaT
local notation "phi" => RingHom.comp (coefficientEmbedding E) (codeMap f)
local notation "lift" => MvPolynomial.map (coefficientEmbedding E)

def extendedCarrier (F : MvPolynomial (Fin 4) K) : Poly3T := surfaceMap phi F
def extendedEquation (F : MvPolynomial (Fin 4) K) (Q A : Poly3) : Poly3T :=
  movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F))
    (lift Q) (lift A) (initialCoordinate E)
def extendedDenominator (F : MvPolynomial (Fin 4) K) (A : Poly3) : Poly3T :=
  surfaceMap phi (2*RCN313.polyH K F)*lift (2*A)

theorem extendedCarrier_injective : Function.Injective (extendedCarrier f) :=
  surfaceMap_injective phi ((coefficientEmbedding E).injective.comp (codeMap_injective f))

theorem extendedCarrier_derivative_nonzero
    (F : MvPolynomial (Fin 4) K) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433) :
    MvPolynomial.pderiv (1 : Fin 3) (extendedCarrier f F)≠0 := by
  rw [extendedCarrier,RCN267.surfaceMap_pderiv_R]
  intro hz
  apply RCN267.R_derivative_nonzero F 2130706433 hpos hsmall
  apply extendedCarrier_injective f
  simpa only [extendedCarrier,map_zero] using hz

theorem extended_target_ordinaryFlag
    (J : WholeSpaceCube6814.Poly (K:=K)) (Q A : Poly3)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag (ordinaryFlag J)
      (genericTargetMap E (targetPolynomial (coefficients (codeMap f) J) (order J) (2*A) Q)) := by
  rw [generic_target_is_movingCut]
  exact movingCut_ordinaryFlag phi J (lift Q) (lift A) (initialCoordinate E)
    (inFlag_map _ hQ) (inFlag_map _ hA)

theorem exists_extended_thick_pair
    (F : MvPolynomial (Fin 4) K) (S T : Source F) (hcop : IsRelPrime S.P T.P)
    (d : ℕ) (hS : d≤S.d) (hT : d≤T.d) (hchar : d≤2130706433)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    ∃ B C : Poly3T, B≠0 ∧ C≠0 ∧ IsRelPrime B C ∧
      PolynomialInFlag (ordinaryFlag S.P) B ∧ PolynomialInFlag (ordinaryFlag T.P) C ∧
      ∀ (R : Type) [CommRing R] (ev : Poly3T →+* R) (J : Ideal R) [J.IsMaximal] (surface : R),
        ev (extendedCarrier f F)∈Ideal.span {surface} →
        ev (surfaceMap phi (2*RCN313.polyH K F))∉J →
        ev (lift (2*A))∉J → ev (extendedEquation f F Q A)∈J →
        ev B∈Ideal.span {surface} ⊔ J^d ∧ ev C∈Ideal.span {surface} ⊔ J^d := by
  letI : StrongNormalizationMonoid (Polynomial Poly3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  letI : NormalizedGCDMonoid (Polynomial Poly3) := UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  let P := coefficients (codeMap f) S.P
  let U := coefficients (codeMap f) T.P
  let rawP := targetPolynomial P (order S.P) (2*A) Q
  let rawU := targetPolynomial U (order T.P) (2*A) Q
  let B0 := leftGCDQuotient rawP rawU
  let C0 := rightGCDQuotient rawP rawU
  have hp : P≠0 := extended_coefficients_ne_zero f S.P (source_nonzero F S)
  have hu : U≠0 := extended_coefficients_ne_zero f T.P (source_nonzero F T)
  have hnp : P.natDegree≤order S.P := extended_coefficients_degree f S.P
  have hnu : U.natDegree≤order T.P := extended_coefficients_degree f T.P
  have hPU : IsRelPrime P U := extended_coefficients_relPrime f
    S.P T.P (source_nonzero F S) hcop
  have hrawP : rawP≠0 := MovingSourceProperness6814.targetPolynomial_ne_zero P _ (2*A) Q hp hnp hden
  have hrawU : rawU≠0 := MovingSourceProperness6814.targetPolynomial_ne_zero U _ (2*A) Q hu hnu hden
  have hPB : rawP=gcd rawP rawU*B0 := left_eq_gcd_mul_leftGCDQuotient rawP rawU
  have hUC : rawU=gcd rawP rawU*C0 := right_eq_gcd_mul_rightGCDQuotient rawP rawU
  have hB0 : B0≠0 := fun hz => hrawP (by rw [hPB,hz,mul_zero])
  have hC0 : C0≠0 := fun hz => hrawU (by rw [hUC,hz,mul_zero])
  have hBdiv : B0∣rawP := ⟨gcd rawP rawU,hPB.trans (mul_comm _ _)⟩
  have hCdiv : C0∣rawU := ⟨gcd rawP rawU,hUC.trans (mul_comm _ _)⟩
  have hmapne {V : Polynomial Poly3} (hV : V≠0) : genericTargetMap Omega V≠0 :=
    fun hz => hV (genericTargetMap_injective Omega (by simpa only [map_zero] using hz))
  refine ⟨genericTargetMap Omega B0,genericTargetMap Omega C0,hmapne hB0,hmapne hC0,
    genericTargetMap_relPrime Omega B0 C0 hB0 (gcdQuotients_isRelPrime hrawP),?_,?_,?_⟩
  · exact flag_of_dvd OmegaT _ _ _ (map_dvd (genericTargetMap Omega) hBdiv)
      (hmapne hrawP) (extended_target_ordinaryFlag f S.P Q A hQ hA)
  · exact flag_of_dvd OmegaT _ _ _ (map_dvd (genericTargetMap Omega) hCdiv)
      (hmapne hrawU) (extended_target_ordinaryFlag f T.P Q A hQ hA)
  · intro R _ ev J _ surface hF hH hdenJ hM
    let ev0 := ev.comp (genericTargetMap Omega)
    have hden0 : ev0 (Polynomial.C (2*A))∉J := by
      simpa only [ev0,RingHom.comp_apply,genericTargetMap_C] using hdenJ
    have hAprime : ev (2*lift A)∉J := by
      simpa only [map_mul,map_ofNat] using hdenJ
    have hleft := source_cut_at_degree_mem_primary phi ev F S (lift Q) (lift A)
      (initialCoordinate Omega) J surface d (order S.P) le_rfl hS hchar hF hH hAprime hM
    have hright := source_cut_at_degree_mem_primary phi ev F T (lift Q) (lift A)
      (initialCoordinate Omega) J surface d (order T.P) le_rfl hT hchar hF hH hAprime hM
    have hl : ev0 rawP∈Ideal.span {surface} ⊔ J^d := by
      simpa only [ev0,rawP,P,RingHom.comp_apply,generic_target_is_movingCut] using hleft
    have hr : ev0 rawU∈Ideal.span {surface} ⊔ J^d := by
      simpa only [ev0,rawU,U,RingHom.comp_apply,generic_target_is_movingCut] using hright
    exact normalized_pair_mem_primary P U _ _ (2*A) Q hp hnp hnu hden hPU ev0 J surface d hden0 hl hr

end
end ProximityPrize.SubmissionLower.MovingSourceExtendedThickPair6814
end MergedPart5
