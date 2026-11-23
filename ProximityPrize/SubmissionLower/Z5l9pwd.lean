import ProximityPrize.SubmissionLower.ZEe4bHc
import ProximityPrize.SubmissionLower.ZxKiVod
import ProximityPrize.SubmissionLower.Z1qPXJc
import ProximityPrize.SubmissionLower.ZEdS9yd
import ProximityPrize.SubmissionLower.ZpWrDCd
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import ProximityPrize.SubmissionLower.ZkEhKoc
import ProximityPrize.SubmissionLower.ZL8fo3b
import ProximityPrize.SubmissionLower.ZnTmQ9b
import ProximityPrize.SubmissionLower.ZWB9BUc
import ProximityPrize.SubmissionLower.Zm2Uhnd
import ProximityPrize.SubmissionLower.Zt62ONe
import ProximityPrize.SubmissionLower.Z0sgnhc
import ProximityPrize.SubmissionLower.ZMb1iHd
import ProximityPrize.SubmissionLower.ZmglaUa
import ProximityPrize.SubmissionLower.Z0aQQAb
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.IsSeparable → zw7, Algebra.mul_smul_comm → zqW, CommRing → za6, Field → zrb, Finset.range → z4x, Fintype.card → zhP, Fintype.card_fin → zgY, Function.Injective → zq4, Function.Surjective → zpX, Ideal.Quotient.field → zxv, Ideal.mem_span_singleton → zxV, IsFractionRing → z0o, IsFractionRing.injective → zxb, LinearMap.ker → z83, Matrix → z30, Matrix.isUnit_iff_isUnit_det → zTR, Matrix.rank_eq_finrank_span_cols → z0e, Matrix.rank_transpose → zZo, Module.Finite → zAa, Module.IsTorsionFree → zYo, Module.finrank → zsE, Module.finrank_eq_card_basis → zdK, MvPolynomial.C → znf, MvPolynomial.eval → zY9, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.rename → zHw, MvPolynomial.ringHom_ext → zXT, MvPolynomial.totalDegree_C → ziW, MvPolynomial.totalDegree_finsetSum_le → zTw, MvPolynomial.totalDegree_mul → zhM, Nat.add_sub_of_le → zp3, Nat.pos_of_ne_zero → zOl, Nat.sub_add_cancel → zxt, Polynomial.C → z1z, Polynomial.mapRingHom → zhd, Polynomial.map_add → zS4, Polynomial.map_map → zoi, Polynomial.map_mul → zNl, Polynomial.map_one → zP0, Polynomial.map_pow → z5m, Polynomial.map_sum → zWe, PowerSeries → zpm, PowerSeries.C → zMG, PowerSeries.X → zWv, PowerSeries.constantCoeff → zbO, RingHom.comp_apply → zQb
open _root_ renaming RingHom.ext → zz4, RingHom.map_det → zov
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P5_7_3_3_4_1_3_1_1
noncomputable section
open Polynomial IsDedekindDomain IsLocalRing WithZero
open scoped WithZero
open qwQWGra (extension)
open q9r9FBa (valuationDVR adicBase centerPlace exponent_eq)
open private local_degree_bounds from ProximityPrize.SubmissionLower.ZR3mCBd
open private bounded adic_separable from ProximityPrize.SubmissionLower.Zi7X5ad
open private small_iff residue_zero tangent_uniformizer tangent_ideal log_of_tangent from ProximityPrize.SubmissionLower.ZxKiVod
variable {p:ℕ}
private theorem separable_of_degree {F E :Type} [zrb F] [zrb E] [zZE F E]
    [zAa F E] [CharP F p] (h:zsE F E<p) :
    Algebra.IsSeparable F E := by
  constructor
  intro x
  have hi:=Algebra.IsIntegral.isIntegral (R:=F) x
  let m:=minpoly F x
  have hpos :0< m.natDegree :=minpoly.natDegree_pos hi
  have hlt:m.natDegree<p:=(minpoly.natDegree_le (A:=F) x).trans_lt h
  have hcast: (m.natDegree :F)≠0:= fun he =>
    hlt.not_ge (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff F p _).mp he))
  change m.Separable
  apply (separable_iff_derivative_ne_zero (minpoly.irreducible hi)).mpr
  intro hz
  have he :=coeff_derivative m (m.natDegree - 1)
  rw [hz,coeff_zero,← Nat.cast_succ,zxt hpos,
    show (m.natDegree - 1).succ=m.natDegree by omega] at he
  exact (mul_ne_zero (leadingCoeff_ne_zero.mpr (minpoly.ne_zero hi)) hcast) he.symm
variable {K M:Type} [zrb K] [zrb M] [zZE K M]
variable (v :Valuation K ℤᵐ⁰) (w:Valuation M ℤᵐ⁰)
local notation "O" => v.valuationSubring
local notation "V" => w.valuationSubring
local notation "N" => integralClosure O M
private theorem local_data [zAa K M] [CharP K p] (e :ℕ) (he :0<e)
    (hv :zpX v) (hw:zpX w)
    (h : ∀ z,w (algebraMap K M z)=v z^e) (hd:zsE K M<p)
    (D:Derivation ℤ M M) (hD : ∀ z,v z≤1→w (D (algebraMap K M z))≤1) :
    letI:=extension v w e he h
    e<p∧zw7 (ResidueField O) (ResidueField V) ∧
      ∃ B:ℤᵐ⁰,1≤B ∧ ∀ x :M,w x≤1→w (D x)≤B:= by
  classical
  let:=extension v w e he h
  let:IsDiscreteValuationRing O:=valuationDVR v hv
  let:zw7 K M:=separable_of_degree hd
  let:IsDedekindDomain N :=integralClosure.isDedekindDomain O K M
  let:z0o N M:=IsIntegralClosure.isFractionRing_of_finite_extension O K M N
  let:zAa O N :=IsIntegralClosure.finite O K M N
  let:zYo O M := .trans_faithfulSMul O K M
  let:zYo O N :=IsIntegralClosure.isTorsionFree O M
  let:Module.Free O N :=IsIntegralClosure.module_free O K M N
  obtain ⟨q,hqOver,hq⟩:=centerPlace v w hw he h
  let P:=IsDiscreteValuationRing.maximalIdeal O
  let m:=maximalIdeal O
  let:q.asIdeal.LiesOver P.asIdeal:=hqOver
  let:q.asIdeal.LiesOver m:=hqOver
  let:q.asIdeal.IsMaximal:=q.isMaximal
  have hrank :zsE O N=zsE K M:=IsIntegralClosure.rank O K M N
  have ⟨_,he',hf'⟩:=local_degree_bounds (A:=O) q
  have hram:q.asIdeal.ramificationIdx O=e := by
    apply exponent_eq v hv
    intro x
    calc
      v x^q.asIdeal.ramificationIdx O =
          P.valuation K x^P.asIdeal.ramificationIdx' q.asIdeal:= by
        rw [adicBase v hv,Ideal.ramificationIdx'_eq_ramificationIdx P.asIdeal q.asIdeal P.ne_bot]
      _=w (algebraMap K M x) := by rw [P.valuation_liesOver M q,hq]
      _=v x^e :=h x
  have reg (a :O) :w (algebraMap O M a)≤1 :=
    (Valuation.HasExtension.val_map_le_one_iff v w _).mpr a.property
  have hel:e<p:=hram ▸ he'.trans_lt (hrank.symm ▸ hd)
  refine ⟨hel,?_,
    bounded v w reg q hq D (fun a=>hD a a.property)⟩
  let:zrb (O ⧸ m) :=zxv m
  let:zrb (N ⧸ q.asIdeal) :=zxv q.asIdeal
  let:zAa (O ⧸ m) (N ⧸ q.asIdeal) :=inferInstance
  have hres :zsE (O ⧸ m) (N ⧸ q.asIdeal)<p:= by
    rw [← Ideal.inertiaDeg_eq_of_isMaximal m q.asIdeal]
    exact hf'.trans_lt (hrank.symm ▸ hd)
  let:CharP O p:=(ValuationSubring.subtype O).charP Subtype.val_injective p
  let:CharP (O ⧸ m) p :=
    CharP.of_ringHom_of_ne_zero (Ideal.Quotient.mk m) p (he.trans hel).ne'
  exact adic_separable v w q hq (separable_of_degree hres)
private theorem unit_nat [CharP M p] {e :ℕ} (he :0<e) (hp:e<p) :
    w (e :M)=1 := by
  let:CharP V p:=(ValuationSubring.subtype V).charP Subtype.val_injective p
  let:CharP (ResidueField V) p :=
    CharP.of_ringHom_of_ne_zero (residue V) p (he.trans hp).ne'
  have hn: (e :ResidueField V)≠0:= fun hz =>
    hp.not_ge (Nat.le_of_dvd he ((CharP.cast_eq_zero_iff _ _ _).mp hz))
  have hu:IsUnit (e :V) :=(residue_ne_zero_iff_isUnit _).mp (by rwa [map_natCast])
  exact (Valuation.valuationSubring.integers w).one_of_isUnit hu
theorem log_le_one [zAa K M] [CharP K p] (hd:zsE K M<p)
    (e :ℕ) (D₀:Derivation ℤ K K) (D:Derivation ℤ M M)
    (hv :zpX v) (hw:zpX w) (he :0<e)
    (hval : ∀ z,w (algebraMap K M z)=v z^e)
    (hD : ∀ z,D (algebraMap K M z)=algebraMap K M (D₀ z))
    (hreg : ∀ z,v z≤1→v (D₀ z)≤1)
    (ht : ∀ z,v z<1→v (D₀ z)<1) (x :M) (hx :x≠0) :
    w (D x/x)≤1 := by
  let:v.HasExtension w:=extension v w e he hval
  let:CharP M p:=charP_of_injective_ringHom (algebraMap K M).injective p
  have hm (z :K) (hz :v z≤1) :w (D (algebraMap K M z))≤1 := by
    rw [hD,hval]
    exact pow_le_one₀ zero_le (hreg z hz)
  obtain ⟨hp,hsep,B,hB,hb⟩:=local_data v w e he hv hw hval hd D hm
  let:zw7 (ResidueField v.valuationSubring)
      (ResidueField w.valuationSubring) :=hsep
  obtain ⟨π,hπ⟩:=hv (exp (-1 :ℤ))
  obtain ⟨τ,hτ⟩:=hw (exp (-1 :ℤ))
  have hτpos :0<w τ:= by rw [hτ]; exact exp_pos
  have hτlt:w τ<1 := by rw [hτ,← exp_zero,exp_lt_exp]; decide
  have hπτ:v π=w τ:=hπ.trans hτ.symm
  let a :=algebraMap K M π
  have ha :w a=w τ^e :=(hval π).trans (congrArg (· ^ e) hπτ)
  have heunit :w (e :M)=1 :=unit_nat w he hp
  have htang:w (D a)≤w τ^e := by
    change w (D (algebraMap K M π))≤_
    rw [hD,hval]
    apply pow_le_pow_left₀ zero_le
    rw [hτ]
    exact small_iff.mp (ht π (hπτ.trans_lt hτlt))
  let S (n:ℕ) :=τ^n•D
  let good (n:ℕ) := ∀ z,w z≤1→w (S n z)≤1
  have hS (n:ℕ) (z :M) :w (S n z)=w τ^n*w (D z) := by
    change w (τ^n*D z)= _
    rw [map_mul,map_pow]
  have hex : ∃ n,good n:= by
    have hBp:0<B:=zero_lt_one.trans_le hB
    obtain ⟨n,hn⟩:=exists_exp_neg_natCast_lt (inv_ne_zero hBp.ne')
    have hs :w τ^n≤B⁻¹:= by
      rw [hτ,← exp_nsmul]
      simpa using hn.le
    refine ⟨n,fun z hz => ?_⟩
    rw [hS]
    exact (mul_le_mul' hs (hb z hz)).trans_eq (inv_mul_cancel₀ hBp.ne')
  classical
  have hu:good 0:= by
    let n:=Nat.find hex
    have hn:good n:=Nat.find_spec hex
    by_cases hn0:n=0
    · exact hn0 ▸ hn
    have hs :w τ^n≤w τ:= by
      obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero hn0
      rw [hk,pow_succ]
      exact mul_le_of_le_one_left' (pow_le_one₀ zero_le hτlt.le)
    have hstay :w (S n a)≤w τ^e := by
      rw [hS]
      exact (mul_le_mul' (hs.trans hτlt.le) htang).trans_eq (one_mul _)
    have hSt:w (S n τ)≤w τ :=
      tangent_uniformizer w (S n) hτpos ha he heunit hn hstay
    have hz :=residue_zero v w (S n) hn (tangent_ideal w hτ (S n) hn hSt) (by
      intro b
      rw [hS]
      exact ((mul_le_mul' hs (hm b b.property)).trans_eq (mul_one _)).trans_lt hτlt)
    have hn1 :n - 1+1=n:=zxt (zOl hn0)
    have hg:good (n - 1) := by
      intro z hzr
      have hh:=small_iff.mp (hz z hzr)
      rw [← hτ] at hh
      have heq :w (S n z)=w τ*w (S (n - 1) z) := by
        rw [hS,hS,← mul_assoc,← pow_succ',hn1]
      rw [heq] at hh
      exact (mul_le_mul_iff_right₀ hτpos).mp (by simpa only [mul_one] using hh)
    exact (Nat.find_min hex (show n - 1<n by omega) hg).elim
  have hUp (z :M) (hz :w z≤1) :w (D z)≤1 := by
    simpa only [hS,pow_zero,one_mul] using hu z hz
  exact log_of_tangent w hτ hx D hUp (tangent_uniformizer w D hτpos ha he heunit hUp htang)
end
end P5_7_3_3_4_1_3_1_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P5_7_3_3_4_1_3_1_1
noncomputable section
open Polynomial IsDedekindDomain IsLocalRing
open qAjZDhd (Lv)
open q85rTDe (aNu extend_derivation)
private theorem integral_log {R K E :Type} [za6 R] [IsDomain R]
    [IsDiscreteValuationRing R] [zrb K] [zrb E] [zZE R K] [z0o R K]
    [zZE K E] [zZE R E] [IsScalarTower R K E]
    [zAa K E] [zw7 K E] {p:ℕ} [CharP K p]
    (hd:zsE K E<p) (d:Derivation ℤ K K) (D:Derivation ℤ E E)
    (hD : ∀ b,D (algebraMap K E b)=algebraMap K E (d b))
    (π:R) (hπ:Irreducible π)
    (hreg : ∀ b:R,∃ c:R,d (algebraMap R K b)=algebraMap R K c)
    (ht : ∃ b:R,d (algebraMap R K π)=algebraMap R K (π*b))
    (x :E) (hx :x≠0) :IsIntegral R (D x/x) := by
  let P:=IsDiscreteValuationRing.maximalIdeal R
  let v :=P.valuation K
  have hreg' (z :K) (hz :v z≤1) :v (d z)≤1 := by
    obtain ⟨a,rfl⟩:=IsDiscreteValuationRing.exists_lift_of_le_one hz
    obtain ⟨b,hb⟩:=hreg a
    rw [hb]
    exact P.valuation_le_one b
  have ht' (z :K) (hz :v z<1) :v (d z)<1 := by
    obtain ⟨a,rfl⟩:=IsDiscreteValuationRing.exists_lift_of_le_one hz.le
    have ha :=(P.valuation_lt_one_iff_mem a).mp hz
    change a∈maximalIdeal R at ha
    rw [hπ.maximalIdeal_eq,zxV] at ha
    obtain ⟨b,rfl⟩:=ha
    obtain ⟨c,hc⟩:=hreg b
    obtain ⟨t,ht⟩:=ht
    rw [show d (algebraMap R K (π*b))=algebraMap R K (π*(c+b*t)) by
      simp only [map_mul,d.leibniz,smul_eq_mul,hc,ht,map_add,mul_add,mul_left_comm]]
    apply (P.valuation_lt_one_iff_mem _).mpr
    change _∈maximalIdeal R
    rw [hπ.maximalIdeal_eq,zxV]
    exact dvd_mul_right π _
  let B:=integralClosure R E
  let:IsDedekindDomain B:=integralClosure.isDedekindDomain R K E
  let:z0o B E :=integralClosure.isFractionRing_of_finite_extension K E
  let:Algebra.IsIntegral R B:=IsIntegralClosure.isIntegral_algebra R E
  let:zYo R E := .trans_faithfulSMul R K E
  let:zYo R B:=IsIntegralClosure.isTorsionFree R E
  have hvals (q:HeightOneSpectrum B) :q.valuation E (D x/x)≤1 := by
    let:q.asIdeal.LiesOver P.asIdeal :=
      ⟨(IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q.asIdeal)).symm⟩
    let e :=P.asIdeal.ramificationIdx' q.asIdeal
    have he :0<e :=zOl
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q.asIdeal P.ne_bot)
    exact log_le_one v (q.valuation E) hd e d D (P.valuation_surjective K)
      (q.valuation_surjective E) he (fun z=>(P.valuation_liesOver E q z).symm)
      hD hreg' ht' x hx
  obtain ⟨b,hb⟩:=HeightOneSpectrum.mem_integers_of_valuation_le_one E _ hvals
  rw [← hb]
  exact b.property
theorem proof :qaJ7jxd.c1 := by
  intro R K L _ _ _ _ _ _ _ _ _ _ p _ d π hπ hreg ht f a y hf hd ha hy hya
  have hroot :aeval y f=0:=hy
  have hdiv :=minpoly.dvd K y hroot
  have hysep:IsSeparable K y :=hf.of_dvd hdiv
  let E :=IntermediateField.adjoin K ({y} : Set L)
  let z :E :=⟨y,IntermediateField.mem_adjoin_simple_self _ _⟩
  let j:=algebraMap K E
  let i:E →+* L:=E.val.toRingHom
  let:zZE R E :=(j.comp (algebraMap R K)).toAlgebra
  let:IsScalarTower R K E :=IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  let:zw7 K E :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr hysep
  let:zAa K E :=IntermediateField.adjoin.finiteDimensional hysep.isIntegral
  have hsmall:zsE K E<p:= by
    rw [IntermediateField.adjoin.finrank hysep.isIntegral]
    exact (natDegree_le_of_dvd hdiv hf.ne_zero).trans_lt hd
  have heval (g:K[X]) :i (g.eval₂ j z)=g.eval₂ (algebraMap K L) y :=
    (hom_eval₂ g j i z).trans rfl
  have hz :f.eval₂ j z=0:=i.injective (by rw [heval,hy,map_zero])
  have hs :f.derivative.eval₂ j z≠0 :=
    hf.aeval_derivative_ne_zero (show aeval z f=0 from hz)
  have hza :z - j a≠0:=sub_ne_zero.mpr (fun h=>hya (congrArg i h))
  obtain ⟨D,hD⟩:=extend_derivation (E :=E) d
  have hc:=aNu D j z f (Lv d f) (fun n=>hD (f.coeff n))
  rw [hz,map_zero] at hc
  have hq:D z = -(Lv d f).eval₂ j z/f.derivative.eval₂ j z := by
    apply (eq_div_iff hs).mpr
    linear_combination -hc
  have hdiff :D (z - j a)=D z := by rw [map_sub,hD,ha,map_zero,sub_zero]
  have h:=(integral_log hsmall d D hD π hπ hreg ht _ hza).map E.val
  change IsIntegral R (i (D (z - j a)/(z - j a))) at h
  rw [hdiff,hq,div_div,map_div₀,map_neg,heval,map_mul,heval,map_sub] at h
  exact h
end
end P5_7_3_3_4_1_3_1_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P5_7_3_3_4_1_7R_1
noncomputable section
open Polynomial qL2osVa Cu
open cu (L)
open P5 (p)
open P5_7_3_3_4_1_7 (targetDen targetNum det)
open P5_7_3_3_4_1_7R (normalized normalized_degree)
open private ef5 from ProximityPrize.SubmissionLower.A
private def projective {R:Type*} [za6 R]
    (f :R[X]) (g:ℕ) (d n a :R) :R[X] :=
  let v :=1+Polynomial.C a*Polynomial.X
  ∑ i∈z4x (g+1),z1z (f.coeff i) *
    (z1z n*v+Polynomial.X)^i*(z1z d*v)^(g-i)
private theorem hom_value {F:Type*} [zrb F] (f :F[X]) {g:ℕ}
    (hf :f.natDegree≤g) {d n y :F} (h:n=y*d) :
    (∑ i∈z4x (g+1),f.coeff i*n^i*d^(g-i))=d^g*f.eval y := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hf),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i≤g:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [h,mul_pow,mul_assoc (f.coeff i),mul_assoc (y^i),← pow_add,zp3 hi']
  ring
private theorem projective_coeff {F:Type*} [zrb F] (f :F[X]) {g:ℕ}
    (hf :f.natDegree≤g) {d n a :F} (hd:d≠0) (ha :a≠0) :
    (projective f g d n a).coeff g=(d*a)^g*f.eval ((n+a⁻¹)/d) := by
  let v :F[X] :=1+Polynomial.C a*Polynomial.X
  let N :=z1z n*v+Polynomial.X
  let D:=z1z d*v
  have hv :v.natDegree≤1 :=
    (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp)))
  have hN :N.natDegree≤1 :=
    (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hv) (by simp))
  have hD:D.natDegree≤1 :=(natDegree_C_mul_le _ _).trans hv
  have hterm (i:ℕ) (hi:i≤g) :
      (z1z (f.coeff i)*N^i*D^(g-i)).coeff g =
        f.coeff i*(n*a+1)^i*(d*a)^(g-i) := by
    have hpow {B:F[X]} (hB:B.natDegree≤1) (j:ℕ) :
        (B^j).coeff j=B.coeff 1^j:= by
      simpa only [mul_one] using (coeff_pow_of_natDegree_le (m:=j) hB)
    have hprod:=coeff_mul_add_eq_of_natDegree_le
      ((natDegree_C_mul_le (f.coeff i) _).trans (by simpa only [mul_one] using natDegree_pow_le_of_le i hN))
      (by simpa only [mul_one] using natDegree_pow_le_of_le (g-i) hD)
    rw [zp3 hi,coeff_C_mul,hpow hN,hpow hD] at hprod
    simpa [N,D,v,coeff_add,coeff_C_mul,coeff_X,coeff_one] using hprod
  change (∑ i∈z4x (g+1),z1z (f.coeff i)*N^i*D^(g-i)).coeff g= _
  rw [finsetSum_coeff,← hom_value f hf (d:=d*a) (n:=n*a+1) (y :=(n+a⁻¹)/d) (by
    field_simp [hd,ha])]
  exact Finset.sum_congr rfl fun i hi=>hterm i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
private theorem projective_map {R S:Type*} [za6 R] [za6 S]
    (e :R →+* S) (f :R[X]) (g:ℕ) (d n a :R) :
    (projective f g d n a).map e=projective (f.map e) g (e d) (e n) (e a) := by
  simp only [projective,zWe,zNl,z5m,
    zS4,zP0,Polynomial.map_X,Polynomial.map_C,coeff_map]
private theorem projective_split_separable {F:Type*} [zrb F] (f :F[X]) {g:ℕ}
    {d n a :F} (hd:d≠0) (ha :a≠0) (hf :f.Separable) (hdeg:f.natDegree=g)
    (hs :f.Splits) (hq: (projective f g d n a).natDegree=g)
    (hqs : (projective f g d n a).Splits)
    (havoid :f.eval ((n+a⁻¹)/d)≠0) :
    (projective f g d n a).Separable := by
  classical
  let q:=projective f g d n a
  let B (y :F) :=d*y-n
  let W (y :F) :=1-a*B y
  let U (y :F) :=B y/W y
  have hW (y :F) (hy :y∈f.roots.toFinset) :W y≠0:= by
    intro h
    have hy' : y=(n+a⁻¹)/d:= by
      change 1-a*(d*y-n)=0 at h
      field_simp [hd,ha]
      linear_combination -h
    exact havoid (hy' ▸ ((mem_roots hf.ne_zero).mp (Multiset.mem_toFinset.mp hy)))
  have hV (y :F) (hy :y∈f.roots.toFinset) :1+a*U y=(W y)⁻¹:= by
    have hw:=hW y hy
    change 1+a*(B y/W y)=(W y)⁻¹
    field_simp [hw]
    dsimp only [W]
    ring
  have hN (y :F) (hy :y∈f.roots.toFinset) :
      n*(1+a*U y)+U y=y*(d*(1+a*U y)) := by
    rw [hV y hy]
    simp only [U,B,div_eq_mul_inv]
    ring
  have hRecover (y :F) (hy :y∈f.roots.toFinset) :
      y=(n*(1+a*U y)+U y)/(d*(1+a*U y)) :=
    (eq_div_iff (mul_ne_zero hd (by rw [hV y hy]; exact inv_ne_zero (hW y hy)))).mpr
      (hN y hy).symm
  have hq0:q≠0:= by
    intro h
    have htop:=projective_coeff f hdeg.le (n:=n) hd ha
    change q.coeff g= _ at htop
    rw [h,coeff_zero] at htop
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hd ha)) havoid htop.symm
  have hMaps :Set.MapsTo U (↑f.roots.toFinset :Set F) (↑q.roots.toFinset :Set F) := by
    intro y hy
    change y∈f.roots.toFinset at hy
    change U y∈q.roots.toFinset
    rw [Multiset.mem_toFinset,mem_roots hq0,IsRoot.def]
    simp only [q,projective,eval_finsetSum,eval_C,eval_mul,eval_add,eval_X,eval_one,eval_pow]
    rw [hom_value f hdeg.le (hN y hy),show f.eval y=0 from
      (mem_roots hf.ne_zero).mp (Multiset.mem_toFinset.mp hy),mul_zero]
  have hInj:Set.InjOn U (↑f.roots.toFinset :Set F) := by
    intro y hy z hz he
    rw [hRecover y hy,hRecover z hz,he]
  have hc:=Finset.card_le_card_of_injOn U hMaps hInj
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hf),← hs.natDegree_eq_card_roots,hdeg] at hc
  apply (nodup_roots_iff_of_splits hq0 hqs).mp
  apply Multiset.toFinset_card_eq_card_iff_nodup.mp
  apply le_antisymm (Multiset.toFinset_card_le _)
  rw [← hqs.natDegree_eq_card_roots,hq]
  exact hc
private theorem projective_separable {F:Type*} [zrb F] (f :F[X]) {g:ℕ}
    {d n a :F} (hd:d≠0) (ha :a≠0) (hf :f.Separable) (hdeg:f.natDegree=g)
    (hq: (projective f g d n a).natDegree=g)
    (havoid :f.eval ((n+a⁻¹)/d)≠0) :
    (projective f g d n a).Separable := by
  let e :=algebraMap F (AlgebraicClosure F)
  apply (separable_map e).mp
  rw [projective_map]
  refine projective_split_separable (f.map e) (by simpa only [map_zero] using e.injective.ne hd)
    (by simpa only [map_zero] using e.injective.ne ha) hf.map
    (by rwa [natDegree_map]) (IsAlgClosed.splits _) (by rwa [← projective_map,natDegree_map])
    (IsAlgClosed.splits _) ?_
  have h:=e.injective.ne havoid
  simpa only [map_zero,← eval_map_apply,map_div₀,map_add,map_inv₀] using h
private theorem centre_shift {R:Type*} [za6 R] (x :R) :
    (evalRingHom 0).comp (taylorAlgHom x).toRingHom=evalRingHom x := by
  apply zz4
  intro q
  change (q.taylor x).eval 0=q.eval x
  rw [taylor_eval,zero_add]
private def backshift {R S:Type*} [za6 R] [za6 S]
    (e :R[X] →+* S) (x :R) :R[X] →+* S :=
  e.comp (taylorAlgHom (-x)).toRingHom
private theorem backshift_cancel {R S:Type*} [za6 R] [za6 S]
    (e :R[X] →+* S) (x :R) :
    (backshift e x).comp (taylorAlgHom x).toRingHom=e := by
  apply zz4
  intro q
  change e (taylor (-x) (taylor x q))=e q
  rw [taylor_taylor,neg_add_cancel,taylor_zero]
private theorem backshift_injective {R S:Type*} [za6 R] [za6 S]
    (e :R[X] →+* S) (he :zq4 e) (x :R) :
    zq4 (backshift e x) :=
  he.comp (taylor_injective (-x))
private theorem backshift_C {R S:Type*} [za6 R] [za6 S]
    (e :R[X] →+* S) (x a :R) :backshift e x (z1z a)=e (z1z a) := by
  change e (taylor (-x) (z1z a))= _
  rw [taylor_C]
variable {C₀:sQ} [Fact (Irreducible C₀)]
private def bY (C:MarkedSheet C₀) : ((oO C₀)[X])[X] :=
  C.sheet.bY.equation.map (mapRingHom C.genericParam)
private theorem chart_eq (C:MarkedSheet C₀) :
    bY C=z1z (z1z (C.sheet.bY.scale :oO C₀)) *
      C.sheet.root.equation :=C.sheet.bY.generic_eq
private theorem adr (C:MarkedSheet C₀) : (bY C).natDegree=C.g:= by
  rw [chart_eq,natDegree_C_mul (by simp [C.sheet.bY.scale.ne_zero]),C.sheet.root.degree]
private theorem chart_centre (C:MarkedSheet C₀) (x :oO C₀) :
    (bY C).map (evalRingHom x)≠0:= by
  intro h
  let R:=C.sheet.root
  apply not_isUnit_X_sub_C x
  apply R.primitive
  apply (C_dvd_iff_dvd_coeff _ _).mpr
  intro i
  apply dvd_iff_isRoot.mpr
  have hi:=congrArg (fun f : (oO C₀)[X]=>f.coeff i) h
  rw [coeff_zero,coeff_map,chart_eq,coeff_C_mul] at hi
  change eval x (z1z (C.sheet.bY.scale :oO C₀)*R.equation.coeff i)=0 at hi
  rw [eval_mul,eval_C] at hi
  exact (mul_eq_zero.mp hi).resolve_left C.sheet.bY.scale.ne_zero
private theorem normalized_map (C:MarkedSheet C₀) (x :L) (r :Target) (a :L)
    {S:Type*} [za6 S] (e : (oO C₀)[X] →+* S) :
    (normalized C x r a).map (e.comp (mapRingHom C.bee)) =
      projective ((bY C).map (e.comp (taylorAlgHom (zT C₀ x)).toRingHom))
        C.g (e (z1z (C.bee (targetDen r))))
        (e (z1z (C.bee (targetNum r)))) (e (z1z (zT C₀ a))) := by
  have hrename (u:DQ.DT C.sheet.n) :
      C.bee (zHw Sum.inr u)=C.genericParam u:= by
    dsimp only [MarkedSheet.bee,MarkedSheet.genericParam]
    rw [MvPolynomial.eval₂Hom_rename]
    rfl
  have hc (b:L) :C.bee (znf b)=zT C₀ b :=
    zTv _ _ _
  have hm:C.bee.comp
      (zHw (Sum.inr :Fin C.sheet.n→Fin 2 ⊕ Fin C.sheet.n)).toRingHom=C.genericParam :=
    zz4 hrename
  have he (u: (DQ.DT C.sheet.n)[X]) :
      ((taylorAlgHom (znf (σ:=Fin 2 ⊕ Fin C.sheet.n) x)).toRingHom
        (u.map (zHw Sum.inr).toRingHom)).map C.bee =
      (taylorAlgHom (zT C₀ x)).toRingHom (u.map C.genericParam) := by
    change (taylor _ (u.map _)).map _=taylor _ _
    rw [map_taylor,hc,zoi,hm]
  simp only [normalized,projective,zWe,zNl,z5m,
    zS4,zP0,Polynomial.map_X,Polynomial.map_C,
    zQb,coe_mapRingHom,coeff_map,bY,hc,he]
private theorem choose_parameter {E F:Type*} [zrb E] [Infinite E] [zrb F]
    (k :E →+* F) (f :F[X]) (hf :f≠0) {d n:F} (hd:d≠0) :
    ∃ a :E,a≠0∧f.eval ((n+(k a)⁻¹)/d)≠0:= by
  classical
  let b (a :E) :=(n+(k a)⁻¹)/d
  have hb:zq4 b:= fun _ _ h =>
    k.injective (inv_injective (add_left_cancel ((div_left_inj' hd).mp h)))
  have ht: (b ⁻¹' (↑f.roots.toFinset :Set F)).Finite :=
    f.roots.toFinset.finite_toSet.preimage hb.injOn
  obtain ⟨a,ha⟩:=(ht.insert 0).exists_notMem
  refine ⟨a,fun hz=>ha (by simp [hz]),?_⟩
  intro h
  exact ha (Set.mem_insert_of_mem _ (Multiset.mem_toFinset.mpr ((mem_roots hf).mpr h)))
private theorem choose_lead (C:MarkedSheet C₀) (x :L) (r :Target)
    (hD:C.bee (targetDen r)≠0) :
    ∃ a :L,zT C₀ a≠0 ∧
      C.bee (((normalized C x r a).coeff C.g).coeff 0)≠0:= by
  let x' := zT C₀ x
  let d:=C.bee (targetDen r)
  let n:=C.bee (targetNum r)
  let F:=bY C
  let fc:=F.map (evalRingHom x')
  have hfc:fc.natDegree≤C.g:=natDegree_map_le.trans (adr C).le
  obtain ⟨a,ha,havoid⟩:=choose_parameter (zT C₀) fc (chart_centre C x') (n:=n) hD
  let a' := zT C₀ a
  have ha' : a' ≠ 0:= by simpa only [map_zero] using (zT C₀).injective.ne ha
  let G:=normalized C x r a
  let j:=mapRingHom C.bee
  let e₀:=evalRingHom (0:oO C₀)
  have hcenter :G.map (e₀.comp j)=projective fc C.g d n a' := by
    change (normalized C x r a).map (e₀.comp j)= _
    rw [normalized_map,show e₀.comp (taylorAlgHom x').toRingHom=evalRingHom x' from centre_shift x']
    simp only [e₀,coe_evalRingHom,eval_C,d,n,a',fc,F,x']
  have htop: (G.map (e₀.comp j)).coeff C.g≠0:= by
    rw [hcenter,projective_coeff _ hfc hD ha']
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hD ha')) havoid
  refine ⟨a,ha',?_⟩
  simpa only [coeff_map,zQb,e₀,j,coe_evalRingHom,coe_mapRingHom,
    ← coeff_zero_eq_eval_zero] using htop
private theorem det_proper (C:MarkedSheet C₀) (x a :L) (r :Target)
    (hg:0<C.g) (hp:C.g<p) (hD:C.bee (targetDen r)≠0)
    (ha :zT C₀ a≠0)
    (hlead:C.bee (((normalized C x r a).coeff C.g).coeff 0)≠0) :
    (det (normalized C x r a) C.g).map C.bee≠0:= by
  let e :=backshift (F5 C₀) (zT C₀ x)
  let j:=mapRingHom C.bee
  let G:=normalized C x r a
  let F:=bY C
  have he :zq4 e :=
    backshift_injective (F5 C₀)
      (zxb (oO C₀)[X] (y7 C₀)) _
  let Q:=G.map (e.comp j)
  let f :=F.map (F5 C₀)
  let d' := Mu C₀ (C.bee (targetDen r))
  let n' := Mu C₀ (C.bee (targetNum r))
  let a'' := Mu C₀ (zT C₀ a)
  have hd' : d' ≠ 0:= by simpa only [map_zero] using (Mu C₀).injective.ne hD
  have ha'' : a'' ≠ 0:= by simpa only [map_zero] using (Mu C₀).injective.ne ha
  have hfield :Q=projective f C.g d' n' a'' := by
    change (normalized C x r a).map ((backshift (F5 C₀) (zT C₀ x)).comp j)= _
    rw [normalized_map,backshift_cancel]
    simp only [backshift_C,d',n',a'',Mu,zQb,f,F]
  have hqcoeff :Q.coeff C.g≠0:= by
    intro h
    have hJ:j (G.coeff C.g)=0:=he (by simpa only [Q,coeff_map,zQb,map_zero] using h)
    have hz :=congrArg (fun u: (oO C₀)[X]=>u.coeff 0) hJ
    exact hlead (by simpa only [j,coe_mapRingHom,coeff_map,coeff_zero] using hz)
  have hqg:Q.natDegree=C.g :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_map_le.trans (normalized_degree C x r a)) hqcoeff
  have hfg:f.natDegree=C.g :=
    (natDegree_map_eq_of_injective
      (zxb (oO C₀)[X] (y7 C₀)) F).trans (adr C)
  have hfs :f.Separable := by
    change ((bY C).map (F5 C₀)).Separable
    rw [chart_eq,zNl,map_C]
    exact (ef5 C.sheet.root hg hp).unit_mul
      (C.sheet.bY.scale.isUnit.map (Polynomial.C.comp (Mu C₀)))
  have hfavoid :f.eval ((n'+(a'')⁻¹)/d')≠0:= by
    intro h
    apply hqcoeff
    rw [hfield,projective_coeff _ hfg.le hd' ha'',h,mul_zero]
  have hsep:Q.Separable :=
    hfield.symm ▸ projective_separable f hd' ha'' hfs hfg (hfield ▸ hqg) hfavoid
  have hres :=resultant_derivative_ne_zero_of_separable Q hsep
  rw [hqg,show Q=G.map (e.comp j) from rfl,derivative_map,resultant_map_map] at hres
  intro hz
  apply hres
  change e ((det G C.g).map C.bee)=0
  rw [hz,map_zero]
theorem proof :P5_7_3_3_4_1_7R.c1 := by
  intro C₀ inst C x r hg hp hD
  obtain ⟨a,ha,hlead⟩:=choose_lead C x r hD
  exact ⟨a,hlead,det_proper C x a r (by omega) hp hD ha hlead⟩
end
end P5_7_3_3_4_1_7R_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_4
noncomputable section
open Polynomial
open cu (L)
open DQ (DT)
open Cu
open qL2osVa
open scoped BigOperators
private def Bound {n:ℕ} (f : (DT n)[X]) (b:ℕ) :Prop :=
  ∀ i,(f.coeff i).totalDegree≤b
private theorem bb6 {n b:ℕ} {a :DT n} (h:a.totalDegree≤b) :
    Bound (C a) b:= by
  intro i
  rw [coeff_C]
  split_ifs <;> simp_all
private theorem cDk {n b:ℕ} {ι:Type*} (s :Finset ι) (f :ι→(DT n)[X])
    (hf : ∀ i∈s,Bound (f i) b) :Bound (∑ i∈s,f i) b:= by
  intro j
  rw [finsetSum_coeff]
  exact zTw (fun i hi=>hf i hi j)
private theorem bBM {n a b:ℕ} {f g: (DT n)[X]}
    (hf :Bound f a) (hg:Bound g b) :Bound (f*g) (a+b) := by
  intro i
  rw [coeff_mul]
  apply zTw
  exact fun j _=>(zhM _ _).trans (Nat.add_le_add (hf _) (hg _))
private theorem dzK {n b:ℕ} {ι:Type*} (s :Finset ι) (f :ι→(DT n)[X])
    (hf : ∀ i∈s,Bound (f i) b) :Bound (∏ i∈s,f i) (s.card*b) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using (bb6 (n:=n) (b:=0) (a :=1) (by simp))
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.add_mul,Nat.one_mul,add_comm]
    exact bBM (hf i (Finset.mem_insert_self ..))
      (ih fun j hj=>hf j (Finset.mem_insert_of_mem hj))
theorem cr3 {R:Type*} [za6 R] {f g:R[X]} {m n:ℕ} {P:R→Prop}
    (h0:P 0) (hf : ∀ i,P (f.coeff i)) (hg : ∀ i,P (g.coeff i))
    (i j:Fin (m+n)) :P (f.sylvester g m n i j) := by
  cases j using Fin.addCases with
  | left j =>
    simp only [sylvester,Matrix.of_apply,Fin.addCases_left]
    split_ifs <;> first | exact hg _ | exact h0
  | right j =>
    simp only [sylvester,Matrix.of_apply,Fin.addCases_right]
    split_ifs <;> first | exact hf _ | exact h0
private theorem bound_det {n d b:ℕ} (M:z30 (Fin d) (Fin d) ((DT n)[X]))
    (hM : ∀ i j,Bound (M i j) b) :Bound M.det (d*b) := by
  classical
  rw [Matrix.det_apply]
  apply cDk
  intro σ _
  have h:=dzK Finset.univ (fun i=>M (σ i) i) (fun i _=>hM (σ i) i)
  intro k
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simpa [hs,coeff_neg,MvPolynomial.totalDegree_neg] using h k
theorem a3u {n d b:ℕ} (M:z30 (Fin d) (Fin d) (DT n))
    (hM : ∀ i j,(M i j).totalDegree≤b) :M.det.totalDegree≤d*b:= by
  have h:=bound_det ((z1z (R:=DT n)).mapMatrix M)
    (fun i j=>bb6 (hM i j)) 0
  rw [← zov,coeff_C_zero] at h
  exact h
theorem derivative_param_degree {n b:ℕ} {f : (DT n)[X]}
    (hf : ∀ i,(f.coeff i).totalDegree≤b) (i:ℕ) :
    (f.derivative.coeff i).totalDegree≤b:= by
  have hcast: ((i:DT n)+1)=znf ((i:L)+1) := by simp
  rw [coeff_derivative,hcast]
  refine (zhM _ _).trans ?_
  rw [ziW,add_zero]
  exact hf (i+1)
theorem branch_coeff_degree {C₀:sQ} [Fact (Irreducible C₀)]
    (S:MarkedSheet C₀) (a :L) (i:ℕ) : ((S.branchEquation a).coeff i).totalDegree≤2*S.g:= by
  let f :=S.sheet.bY.equation
  have hf : ∀ j,Bound (f.coeff j) 1 :=S.sheet.bY.degree.2
  have hd (j) :Bound (f.derivative.coeff j) 1 := by
    have hcast: (↑j+1 : (DT S.sheet.n)[X])=C (znf ((j:L)+1)) := by simp
    rw [coeff_derivative,hcast]
    exact bBM (hf (j+1)) (bb6 (n:=S.sheet.n) (a :=znf ((j:L)+1))
      (b:=0) (by rw [ziW]))
  have hr :Bound (f.resultant f.derivative S.g (S.g-1)) ((S.g+(S.g-1))*1) := by
    exact bound_det _ (cr3 (P:= fun x=>Bound x 1) (fun j=> by simp) hf hd)
  have he :Bound (f.eval (C (znf a))) 1 := by
    rw [eval_eq_sum,Polynomial.sum]
    apply cDk
    intro j _
    rw [← map_pow C,← map_pow znf]
    exact bBM (hf j) (bb6 (n:=S.sheet.n) (a :=znf (a^j))
      (b:=0) (by rw [ziW]))
  have h:=irreducible_degree_pos S.sheet.root.irreducible
  rw [natDegree_map_eq_of_injective (f :=F5 C₀) (zxb (oO C₀)[X]
    (y7 C₀)),S.sheet.root.degree] at h
  simpa only [MarkedSheet.branchEquation,f,show (S.g+(S.g-1))*1+1=2*S.g by omega] using
    bBM hr he i
end
end P5_7_3_3_4_1_4
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_4
noncomputable section
open Polynomial EuclideanDomain Matrix
private theorem mem_mul_degreeLT {F:Type*} [zrb F] {a b:ℕ} {f t:F[X]}
    (hf :f.natDegree=a) (ht:t∈degreeLT F b) :f*t∈degreeLT F (a+b) := by
  by_cases h:t=0
  · simp [h]
  have ht' := (natDegree_lt_iff_degree_lt h).mpr (mem_degreeLT.mp ht)
  by_cases hft:f*t=0
  · simp [hft]
  apply mem_degreeLT.mpr
  apply (natDegree_lt_iff_degree_lt hft).mp
  exact (natDegree_mul_le.trans_lt (by omega))
theorem sylvester_rank {F:Type*} [zrb F] [DecidableEq F]
    (f g:F[X]) (hf :f≠0) (hg:g≠0) :
    (f.sylvester g f.natDegree g.natDegree).rank =
      f.natDegree+g.natDegree-(EuclideanDomain.gcd f g).natDegree := by
  let d:=EuclideanDomain.gcd f g
  obtain ⟨u,hu⟩:=EuclideanDomain.gcd_dvd_left f g
  obtain ⟨v,hv⟩:=EuclideanDomain.gcd_dvd_right f g
  change f=d*u at hu
  change g=d*v at hv
  have hd:d≠0:=left_ne_zero_of_mul (hu ▸ hf)
  have hu0:u≠0:=right_ne_zero_of_mul (hu ▸ hf)
  have hv0:v≠0:=right_ne_zero_of_mul (hv ▸ hg)
  have hdu:d.natDegree+u.natDegree=f.natDegree :=(natDegree_mul hd hu0).symm.trans (congrArg natDegree hu.symm)
  have hdv :d.natDegree+v.natDegree=g.natDegree :=(natDegree_mul hd hv0).symm.trans (congrArg natDegree hv.symm)
  have hc:IsCoprime u v := by
    let a :=gcdA f g
    let b:=gcdB f g
    refine ⟨a,b,mul_left_cancel₀ hd ?_⟩
    have h:d=f*a+g*b:=gcd_eq_gcd_ab f g
    rw [hu,hv] at h
    linear_combination -h
  let S:=sylvesterMap f g (le_refl f.natDegree) (le_refl g.natDegree)
  let T:degreeLT F d.natDegree →ₗ[F] degreeLT F f.natDegree×degreeLT F g.natDegree :=
    { toFun:= fun t =>
        (⟨-(u*t),by
          rw [mem_degreeLT,degree_neg,← mem_degreeLT]
          rw [← hdu,add_comm]
          exact mem_mul_degreeLT rfl t.property⟩,
        ⟨v*t,by rw [← hdv,add_comm]; exact mem_mul_degreeLT rfl t.property⟩)
      map_add' := by
        intro s t
        apply Prod.ext <;> apply Subtype.ext
        · change -(u*((s :F[X])+t)) = -(u*s)+-(u*t)
          rw [mul_add]
          abel
        · exact mul_add _ _ _
      map_smul' := by
        intro c t
        apply Prod.ext <;> apply Subtype.ext
        · change -(u*(c•(t:F[X])))=c • -(u*t)
          rw [zqW,smul_neg]
        · exact zqW _ _ _ }
  have hST : ∀ t,T t∈z83 S:= by
    intro t
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change f*(v*t)+g*(-(u*t))=0
    rw [hu,hv]
    ring
  let Tk :=T.codRestrict (z83 S) hST
  have hInj:zq4 Tk := by
    intro s t h
    apply Subtype.ext
    exact mul_left_cancel₀ hv0 (congrArg (fun x :z83 S=>(x.val.2 :F[X])) h)
  have hSurj:zpX Tk := by
    rintro ⟨⟨a,b⟩,hab⟩
    have h:f*(b:F[X])+g*(a :F[X])=0:=congrArg Subtype.val (LinearMap.mem_ker.mp hab)
    have h₀:=(congrArg₂ (fun i j:F[X]=>i*(b:F[X])+j*(a :F[X])) hu hv).symm.trans h
    have h' : u*(b:F[X])+v*(a :F[X])=0:= by
      apply (mul_eq_zero.mp ?_).resolve_left hd
      linear_combination h₀
    have hb:v∣(b:F[X]) := by
      apply hc.symm.dvd_of_dvd_mul_left
      rw [show u*(b:F[X]) = -(v*(a :F[X])) by linear_combination h',dvd_neg]
      exact dvd_mul_right _ _
    obtain ⟨t,ht⟩:=hb
    have ha : (a :F[X]) = -(u*t) := by
      apply mul_left_cancel₀ hv0
      rw [ht] at h'
      linear_combination h'
    have htd:t∈degreeLT F d.natDegree := by
      by_cases ht0:t=0
      · simp [ht0]
      have hb0: (b:F[X])≠0:=ht ▸ mul_ne_zero hv0 ht0
      have hb' := (natDegree_lt_iff_degree_lt hb0).mpr (mem_degreeLT.mp b.property)
      rw [ht,natDegree_mul hv0 ht0] at hb'
      exact mem_degreeLT.mpr ((natDegree_lt_iff_degree_lt ht0).mp (by omega))
    exact ⟨⟨t,htd⟩,Subtype.ext (Prod.ext (Subtype.ext ha.symm) (Subtype.ext ht.symm))⟩
  have hker :zsE F (z83 S)=d.natDegree :=
    (LinearEquiv.ofBijective Tk ⟨hInj,hSurj⟩).finrank_eq.symm.trans
      (by rw [zdK (degreeLT.basis F _),zgY])
  rw [Matrix.rank_eq_finrank_range_toLin _ (degreeLT.basis F _)
      (((degreeLT.basis F _).prod (degreeLT.basis F _)).reindex finSumFinEquiv),
    ← toMatrix_sylvesterMap' f g (le_refl _) (le_refl _),Matrix.toLin_toMatrix]
  have h:=S.finrank_range_add_finrank_ker
  rw [hker,zdK
    (((degreeLT.basis F _).prod (degreeLT.basis F _)).reindex finSumFinEquiv),zgY] at h
  change zsE F (LinearMap.range S)= _
  change _ = _ - d.natDegree
  omega
private theorem rank_columns {F M N :Type*} [zrb F] [Fintype N]
    (A:z30 M N F) : ∃ c:Fin A.rank→N,(A.submatrix id c).rank=A.rank := by
  classical
  obtain ⟨κ,a,hai,has,hal⟩:=exists_linearIndependent' F A.col
  let:Finite κ:=Finite.of_injective a hai
  let:=Fintype.ofFinite κ
  have hcard:zhP κ=A.rank := by
    rw [z0e,← has,finrank_span_eq_card hal]
  let e :=Fintype.equivFinOfCardEq hcard
  refine ⟨a ∘ e.symm,?_⟩
  rw [z0e]
  change zsE F (Submodule.span F (Set.range ((A.col ∘ a) ∘ e.symm)))= _
  rw [e.symm.surjective.range_comp,has,z0e]
theorem rank_minor {F M N :Type*} [zrb F] [Fintype M] [Fintype N] (A:z30 M N F) :
    ∃ r :Fin A.rank→M,∃ c:Fin A.rank→N,(A.submatrix r c).det≠0:= by
  classical
  obtain ⟨c,hc⟩:=rank_columns A
  let B:=A.submatrix id c
  have hB:Bᵀ.rank=A.rank :=(zZo B).trans hc
  obtain ⟨r,hr⟩:=rank_columns Bᵀ
  let r' := r ∘ finCongr hB.symm
  have he : ((A.submatrix r' c)ᵀ).rank=A.rank := by
    change (Bᵀ.submatrix id r').rank= _
    change ((Bᵀ.submatrix id r).submatrix (Equiv.refl _) (finCongr hB.symm)).rank= _
    rw [Matrix.rank_submatrix,hr,hB]
  refine ⟨r',c,?_⟩
  rw [zZo] at he
  let Fm:=(A.submatrix r' c).mulVecLin
  have h:=Fm.finrank_range_add_finrank_ker
  change zsE F (LinearMap.range Fm)=A.rank at he
  rw [he,Module.finrank_pi,zgY] at h
  have hf :zq4 Fm:=LinearMap.ker_eq_bot.mp
    (Submodule.finrank_eq_zero.mp (by omega))
  intro hzero
  obtain ⟨v,hv,hz⟩:=Matrix.exists_mulVec_eq_zero_iff.mpr hzero
  exact hv (hf (by simpa [Fm] using hz))
end
end P5_7_3_3_4_1_4
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_4
noncomputable section
open Matrix
open scoped BigOperators
theorem det_order {F:Type*} [zrb F] {n:ℕ} (M:z30 (Fin n) (Fin n) (zpm F)) :
    (zWv:zpm F)^(n-(PowerSeries.constantCoeff.mapMatrix M).rank)∣M.det:= by
  classical
  let ρ:zpm F →+* F:=zbO
  let M₀:=ρ.mapMatrix M
  obtain ⟨V,U,e,hV,hU,he⟩:=M₀.exists_rank_normal_form
  let c:=zMG (R:=F)
  let N :=Matrix.reindex e e (c.mapMatrix V*M*c.mapMatrix U)
  have hzero (i:Fin M₀.rank ⊕ Fin (zhP (Fin n)-M₀.rank)) (j) :
      ρ (N i (.inr j))=0:= by
    change ρ ((c.mapMatrix V*M*c.mapMatrix U) (e.symm i) (e.symm (.inr j)))=0
    have hcomp (W:z30 (Fin n) (Fin n) F) :ρ.mapMatrix (c.mapMatrix W)=W:= by
      ext k l
      exact PowerSeries.constantCoeff_C _
    change (ρ.mapMatrix (c.mapMatrix V*M*c.mapMatrix U)) _ _=0
    rw [map_mul,map_mul,hcomp,hcomp]
    change (V*M₀*U) _ _=0
    rw [he]
    cases i <;> simp
  have hdiv :zWv ^(n-M₀.rank)∣N.det:= by
    rw [Matrix.det_apply']
    apply Finset.dvd_sum
    intro σ _
    apply dvd_mul_of_dvd_right
    rw [Fintype.prod_sum_type]
    apply dvd_mul_of_dvd_right
    have hh:=Finset.prod_dvd_prod_of_dvd
      (s :=(Finset.univ :Finset (Fin (zhP (Fin n)-M₀.rank))))
      (fun _=>(zWv:zpm F)) (fun j=>N (σ (.inr j)) (.inr j))
      (fun j _=>PowerSeries.X_dvd_iff.mpr (hzero _ j))
    simpa only [Finset.prod_const,Finset.card_univ,zgY] using hh
  rw [show N.det=(c.mapMatrix V).det*M.det*(c.mapMatrix U).det by
    rw [Matrix.det_reindex_self,Matrix.det_mul,Matrix.det_mul]] at hdiv
  have hu:IsUnit (c.mapMatrix U).det:=(zTR _).mp (hU.map c.mapMatrix)
  have hv :IsUnit (c.mapMatrix V).det:=(zTR _).mp (hV.map c.mapMatrix)
  exact hv.dvd_mul_left.mp (hu.dvd_mul_right.mp hdiv)
end
end P5_7_3_3_4_1_4
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace P5_7_3_3_4_1_4
noncomputable section
open Polynomial UniqueFactorizationMonoid
open P5 (K p)
open cu (L)
open DQ (DT)
open Cu (sQ oO zT)
open qL2osVa
variable {C₀:sQ} [Fact (Irreducible C₀)] {S:MarkedSheet C₀}
  {A:ArcFamily S} {m:ℕ}
private def arcEval {γ:K} (a :Arc S γ) :DT S.sheet.n →+* Series :=
  zOD zMG a.parameter
private theorem arcEval_mark {γ:K} (a :Arc S γ) :
    PowerSeries.constantCoeff.comp (arcEval a)=zY9 (S.sheet.parameter γ) := by
  apply zXT
  · intro u
    simp [arcEval]
  · intro j
    simpa [arcEval] using a.parameter_value j
private theorem arcEval_generic {γ:K} (a :Arc S γ) :
    (algebraMap Series SeriesField).comp (arcEval a)=a.embedding.comp S.genericParam:= by
  apply zXT
  · intro u
    simpa [arcEval,MarkedSheet.genericParam] using (a.constant_eq u).symm
  · intro j
    simpa [arcEval,MarkedSheet.genericParam] using (a.parameter_eq j).symm
private theorem lift_monic (B:Branch S A m) {γ:K} (h:γ∈B.keep) :
    (B.lift γ).Monic :=
  monic_of_injective (zxb Series SeriesField)
    (by rw [B.lift_eq γ h]; exact B.monic.map _)
private theorem atMark_degree (B:Branch S A m) {γ:K} (h:γ∈B.keep) :
    (B.yq γ).natDegree=(S.radicalBranch B.reference).natDegree := by
  have hl:=lift_monic B h
  rw [Branch.yq,hl.natDegree_map,← hl.natDegree_map (algebraMap Series SeriesField),
    B.lift_eq γ h,B.monic.natDegree_map]
private theorem radical_power {F:Type} [zrb F] {f :F[X]} (hf :f≠0) :
    ∃ e,f∣monicRadical f^e := by
  classical
  exact exists_dvd_radical_self_pow hf
private theorem reduced_radical_le {F:Type} [zrb F] (f r : (zpm F)[X])
    (hr :r.Monic) (hf :f.map zbO≠0)
    (hn: (f.map zbO).natDegree=f.natDegree) (e :ℕ)
    (hd:f.map (algebraMap _ (FractionRing (zpm F))) ∣
      (r.map (algebraMap _ (FractionRing (zpm F))))^e) :
    (monicRadical (f.map zbO)).natDegree ≤
      (monicRadical (r.map zbO)).natDegree := by
  classical
  let i:=algebraMap (zpm F) (FractionRing (zpm F))
  let ρ:zpm F →+* F:=zbO
  have hl:ρ f.leadingCoeff=(f.map ρ).leadingCoeff := by
    simp only [leadingCoeff,show (f.map ρ).natDegree=f.natDegree from hn,coeff_map]
  have hu:IsUnit f.leadingCoeff :=PowerSeries.isUnit_iff_constantCoeff.mpr
    (isUnit_iff_ne_zero.mpr (hl.symm ▸ leadingCoeff_ne_zero.mpr hf))
  let u: (zpm F)[X] :=z1z (↑(hu.unit⁻¹) :zpm F)
  have huu:IsUnit u:=(hu.unit⁻¹).isUnit.map z1z
  have hm: (f*u).Monic:= by
    simpa only [u,Units.smul_def,smul_eq_C_mul,mul_comm] using
      monic_of_isUnit_leadingCoeff_inv_smul hu
  have hiu:IsUnit (u.map i) :=huu.map (zhd i)
  have hd' : f∣r^e :=huu.mul_right_dvd.mp
    ((Polynomial.map_dvd_map i (zxb _ _) hm).mp
      (by rw [zNl,z5m,hiu.mul_right_dvd]; exact hd))
  have hred:f.map ρ∣(r.map ρ)^e := by
    simpa only [coe_mapRingHom,z5m] using map_dvd (zhd ρ) hd'
  have hrad:=(exists_dvd_pow_iff_radical_dvd hf).mp ⟨e,hred⟩
  exact natDegree_le_of_dvd
    ((dvd_radical_iff isRadical_radical (hr.map ρ).ne_zero).mpr hrad) radical_ne_zero
private theorem marked_radical_le (B:Branch S A m) {γ:K} (h:γ∈B.keep) :
    (monicRadical (S.markedBranch B.reference γ)).natDegree ≤
      (monicRadical (B.yq γ)).natDegree := by
  let a :=A ⟨γ,B.subset h⟩
  let i:=algebraMap Series SeriesField
  let f :=(S.branchEquation B.reference).map (arcEval a)
  have hf :f.map i=(S.genericBranch B.reference).map a.embedding:= by
    simp only [f,MarkedSheet.genericBranch,zoi]
    rw [show i.comp (arcEval a)=a.embedding.comp S.genericParam from arcEval_generic a]
  have hf₀:f.map zbO=S.markedBranch B.reference γ:= by
    dsimp only [f]
    rw [zoi,arcEval_mark]
    rfl
  have hdeg: (f.map zbO).natDegree=f.natDegree := by
    rw [hf₀,← natDegree_map_eq_of_injective (zxb Series SeriesField) f,
      hf,natDegree_map_eq_of_injective a.embedding.injective]
    exact B.degree_at_mark γ h
  obtain ⟨e,he⟩:=radical_power B.proper
  have hd:f.map i∣((B.lift γ).map i)^e := by
    rw [hf,B.lift_eq γ h,← z5m]
    exact map_dvd (zhd a.embedding) he
  rw [← hf₀]
  exact reduced_radical_le f _ (lift_monic B h) (hf₀.symm ▸ B.nonzero_at_mark γ h) hdeg e hd
theorem proof :qL2osVa.c4 := by
  classical
  intro C₀ inst S A m B hm
  let:DecidableEq L:=Classical.decEq _
  let:DecidableEq (oO C₀) :=Classical.decEq _
  let f :=S.branchEquation B.reference
  let F:=S.genericBranch B.reference
  let n:=F.natDegree
  have hn:n≤ m:=B.degree
  have hnp:n<p:=hn.trans_lt hm
  have hr : (S.radicalBranch B.reference).natDegree≤n:=natDegree_radical_le
  let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
  let:CharP (oO C₀) p:=charP_of_injective_ringHom (zT C₀).injective p
  by_cases hn0:n=0
  · refine ⟨1,by simp,by simp,fun γ h=>⟨B.subset h,?_⟩⟩
    have ht:=atMark_degree B h
    have hp:B.yq γ≠0:=((lift_monic B h).map PowerSeries.constantCoeff).ne_zero
    have hd:=natDegree_le_of_dvd
      (EuclideanDomain.gcd_dvd_left (B.yq γ) (B.yq γ).derivative) hp
    intro j hj
    change j<(EuclideanDomain.gcd (B.yq γ) (B.yq γ).derivative).natDegree at hj
    omega
  have hder :=bD9 (f :=F) (zOl hn0) hnp
  let M:=f.sylvester f.derivative n (n-1)
  let N :=S.genericParam.mapMatrix M
  have hN :N=F.sylvester F.derivative n (n-1) := by
    change _=(f.map S.genericParam).sylvester (f.map S.genericParam).derivative _ _
    rw [derivative_map,sylvester_map_map]
  have hNr :N.rank=n+(n-1)-(EuclideanDomain.gcd F F.derivative).natDegree := by
    rw [hN,← hder.2,sylvester_rank F F.derivative B.proper hder.1]
  obtain ⟨r,c,hcut⟩:=rank_minor N
  let q:=(M.submatrix r c).det
  refine ⟨q,?_,?_,?_⟩
  · dsimp only [q]
    rw [zov]
    exact hcut
  · have hb : ∀ j,(f.coeff j).totalDegree≤2*S.g:=branch_coeff_degree S B.reference
    have hzero : (0:DT S.sheet.n).totalDegree≤2*S.g:= by simp
    have hQ:q.totalDegree≤N.rank*(2*S.g) :=
      a3u _ fun i j=>cr3
        (P:= fun x :DT S.sheet.n=>x.totalDegree≤2*S.g) hzero hb (derivative_param_degree hb) (r i) (c j)
    have hle :=N.rank_le_height
    exact hQ.trans (by rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega))
  · intro γ h
    let a :=A ⟨γ,B.subset h⟩
    let E :=S.markedBranch B.reference γ
    let M₀:=(zY9 (S.sheet.parameter γ)).mapMatrix M
    have hE :E.natDegree=n:=B.degree_at_mark γ h
    have hEp:E.natDegree<p:=hE.symm ▸ hnp
    have hder₀:=bD9 (by omega :0<E.natDegree) hEp
    have hM₀:M₀=E.sylvester E.derivative n (n-1) := by
      let ev :=zY9 (S.sheet.parameter γ)
      change _=(f.map ev).sylvester (f.map ev).derivative _ _
      rw [derivative_map,sylvester_map_map]
    have hR₀:M₀.rank=n+(n-1)-(EuclideanDomain.gcd E E.derivative).natDegree := by
      rw [hM₀,← hE,← hder₀.2,sylvester_rank E E.derivative (B.nonzero_at_mark γ h) hder₀.1]
    have hred:=marked_radical_le B h
    have hd:=atMark_degree B h
    have hb: (B.yq γ).natDegree<p:= by omega
    have hgen:=gcd_degree F B.proper hnp
    have hmark :=gcd_degree E (B.nonzero_at_mark γ h) hEp
    have hrad:=gcd_degree (B.yq γ) ((lift_monic B h).map zbO).ne_zero hb
    have hs :=Matrix.rank_submatrix_le M₀ r c
    have hdrop:B.DG γ≤N.rank-(M₀.submatrix r c).rank := by
      unfold Branch.DG
      change (EuclideanDomain.gcd F F.derivative).natDegree +
        (S.radicalBranch B.reference).natDegree=n at hgen
      change (radical E).natDegree≤(radical (B.yq γ)).natDegree at hred
      omega
    let M' := (arcEval a).mapMatrix (M.submatrix r c)
    have hM' : PowerSeries.constantCoeff.mapMatrix M' = M₀.submatrix r c:= by
      ext i j
      exact DFunLike.congr_fun (arcEval_mark a) _
    refine ⟨B.subset h,?_⟩
    change ∀ j<B.DG γ,PowerSeries.coeff j (arcEval a q)=0
    dsimp only [q]
    rw [zov]
    apply PowerSeries.X_pow_dvd_iff.mp
    have hdiv :=det_order M'
    rw [hM'] at hdiv
    exact (pow_dvd_pow _ hdrop).trans hdiv
end
end P5_7_3_3_4_1_4
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
namespace P5_7_3_3_4_1_2
noncomputable section
open Finset Polynomial UniqueFactorizationMonoid
open P5 (K p)
open quN7Z4a (physicalWeight)
open qL2osVa
open cu (L j9)

open Cu
open private ef5 from ProximityPrize.SubmissionLower.A
open scoped BigOperators
private theorem map_branch {R S:Type} [za6 R] [za6 S] (e :R →+* S)
    (f :R[X]) (g:ℕ) (a :R) :
    e (f.resultant f.derivative g (g-1)*f.eval a) =
    (f.map e).resultant (f.map e).derivative g (g-1)*(f.map e).eval (e a) := by
  rw [map_mul,eval_map_apply,derivative_map,resultant_map_map]
variable {C₀:sQ} [Fact (Irreducible C₀)] (C:MarkedSheet C₀)
private theorem generic_branch (hg:2≤C.g) (hp:C.g<p) (a :L) :
    C.genericBranch a≠0 ∧
      (C.genericBranch a).natDegree ≤
        2*C.g*physicalWeight C.D C.sheet.root.equation - C.g*C.g*C.D:= by
  let R:=C.sheet.root
  let s :=C.sheet.bY.scale
  let e :=mapRingHom C.genericParam
  let f :=C.sheet.bY.equation.map e
  have heq :f=z1z (z1z (s :oO C₀))*R.equation :=
    C.sheet.bY.generic_eq
  have hmap :f.map (F5 C₀) =
      z1z (Mu C₀ (s :oO C₀))*R.equation.map (F5 C₀) := by
    rw [heq,zNl,map_C]
    rfl
  have hd:f.natDegree=C.g:= by
    rw [heq,natDegree_C_mul (by simp [s.ne_zero]),R.degree]
  have hi:zq4 (F5 C₀) :=
    zxb (oO C₀)[X] (y7 C₀)
  have hxd: (f.map (F5 C₀)).natDegree=C.g :=
    (natDegree_map_eq_of_injective hi f).trans hd
  have hf : ∀ i,f.coeff i≠0→(f.coeff i).natDegree+C.D*i≤physicalWeight C.D R.equation := by
    intro i hi
    rw [heq,coeff_C_mul] at hi ⊢
    rw [natDegree_C_mul s.ne_zero,Nat.mul_comm C.D i]
    exact Finset.le_sup (f := fun j=>(R.equation.coeff j).natDegree+j*C.D)
        (mem_support_iff.mpr (right_ne_zero_of_mul hi))
  have hsep: (f.map (F5 C₀)).Separable := by
    rw [hmap]
    exact (ef5 R (by omega) hp).unit_mul
      (s.isUnit.map (Polynomial.C.comp (Mu C₀)))
  have hres :=resultant_derivative_ne_zero_of_separable _ hsep
  rw [hxd,derivative_map,resultant_map_map] at hres
  have ha :f.eval (z1z (zT C₀ a))≠0:= by
    intro h
    have hEval :=congrArg (F5 C₀) h
    rw [← eval_map_apply,map_zero,hmap,eval_mul,eval_C] at hEval
    have hdeg: (R.equation.map (F5 C₀)).natDegree≠1 := by
      rw [natDegree_map_eq_of_injective hi,R.degree]
      omega
    have hs :Mu C₀ (s :oO C₀)≠0 :=
      (s.isUnit.map (Mu C₀)).ne_zero
    exact R.irreducible.not_isRoot_of_natDegree_ne_one hdeg ((mul_eq_zero.mp hEval).resolve_left hs)
  have hB:C.genericBranch a =
      f.resultant f.derivative C.g (C.g-1)*f.eval (z1z (zT C₀ a)) := by
    change e (_ *_)= _
    rw [map_branch]
    simp only [e,coe_mapRingHom,map_C,MarkedSheet.genericParam,zTv]
    rfl
  rw [hB]
  exact ⟨mul_ne_zero (fun hz=>hres (by rw [hz,map_zero])) ha,
    branch_degree (by omega) hd hf _⟩
private theorem radical_monic {F:Type} [zrb F] (B:F[X]) : (monicRadical B).Monic:= by
  classical
  change (radical B).Monic
  unfold radical
  apply monic_prod_of_monic
  intro q hq
  have h:=mem_primeFactors.mp hq
  exact (normalize_eq_self_iff_monic (irreducible_of_normalized_factor q h).ne_zero).mp
    (normalize_normalized_factor q h)
private theorem polynomial_lift {F:Type} [zrb F] (B:F[X]) (j:F →+* SeriesField)
    (S:Series[X]) (hS:S.map (algebraMap Series SeriesField)=B.map j)
    (hu:IsUnit S.leadingCoeff) :
    ∃ P:Series[X],P.map (algebraMap Series SeriesField)=(monicRadical B).map j:= by
  classical
  let i:=algebraMap Series SeriesField
  obtain ⟨u,hu⟩:=hu
  let Q:=S*z1z (↑u⁻¹:Series)
  let G:=(monicRadical B).map j
  have hQ:Q.Monic:= by
    change (S*z1z (↑u⁻¹:Series)).leadingCoeff=1
    rw [leadingCoeff_mul,leadingCoeff_C,← hu]
    exact Units.mul_inv u
  have hG:G.Monic:=(radical_monic B).map j
  have hdiv :G∣Q.map i:= by
    dsimp only [Q]
    rw [zNl,hS]
    refine dvd_mul_of_dvd_left (Polynomial.map_dvd j ?_) _
    exact UniqueFactorizationMonoid.radical_dvd_self
  obtain ⟨P,hP⟩:=IsIntegrallyClosed.eq_map_mul_C_of_dvd SeriesField hQ hdiv
  exact ⟨P,by simpa only [show G.leadingCoeff=1 from hG,C_1,mul_one] using hP⟩
private theorem lift_at (a :L) (γ:K) (A:Arc C γ)
    (hγ: (C.markedBranch a γ).coeff (C.genericBranch a).natDegree≠0) :
    ∃ P:Series[X],P.map (algebraMap Series SeriesField) =
      (C.radicalBranch a).map A.embedding:= by
  let e :=zOD zMG A.parameter
  let i:=algebraMap Series SeriesField
  let S:=(C.branchEquation a).map e
  have he :i.comp e=A.embedding.comp C.genericParam:= by
    apply zXT
    · intro a
      simpa only [e,MarkedSheet.genericParam,zQb,zTv] using
        (A.constant_eq a).symm
    · intro k
      simpa only [e,MarkedSheet.genericParam,zQb,MvPolynomial.eval₂Hom_X'] using
        (A.parameter_eq k).symm
  have hspec :PowerSeries.constantCoeff.comp e=zY9 (C.sheet.parameter γ) := by
    apply zXT
    · intro a
      simp [e]
    · intro k
      simpa [e] using A.parameter_value k
  have hS:S.map i=(C.genericBranch a).map A.embedding:= by
    dsimp only [S]
    rw [MarkedSheet.genericBranch,zoi,zoi,he]
  have hmark :S.map zbO=C.markedBranch a γ:= by
    dsimp only [S]
    rw [MarkedSheet.markedBranch,zoi,hspec]
  have hd:S.natDegree=(C.genericBranch a).natDegree := by
    rw [← natDegree_map_eq_of_injective (zxb Series SeriesField) S,hS,natDegree_map]
  refine polynomial_lift _ _ S hS (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr ?_))
  rw [← coeff_natDegree,hd,← coeff_map,hmark]
  exact hγ
theorem proof :qL2osVa.c2 := by
  classical
  intro C₀ inst C A m hg hp _ hw
  obtain ⟨a,ha⟩:=Infinite.exists_notMem_finset (C.T.image fun γ=>(j9 (C.s γ)).coeff 0)
  have hdif (γ:K) (hγ:γ∈C.T) :j9 (C.s γ)≠z1z a := by
    intro h
    exact ha (mem_image.mpr ⟨γ,hγ,by rw [h,coeff_C_zero]⟩)
  obtain ⟨hB,hb⟩:=generic_branch C hg hp a
  let N :=(C.genericBranch a).natDegree
  let q:=(C.branchEquation a).coeff N
  let keep:=C.smoothMarks.filter fun γ=>zY9 (C.sheet.parameter γ) q≠0
  have hsub:keep⊆C.smoothMarks :=filter_subset _ _
  have smooth_sub:C.smoothMarks⊆C.T:=filter_subset _ _
  have hq:C.genericParam q≠0:= by
    rw [← coeff_map]
    exact leadingCoeff_ne_zero.mpr hB
  have hbd: (C.smoothMarks \ keep).card≤2*C.g*C.H := by
    refine (qRoCwuc.dSG C.sheet C.injective q hq _ ?_ ?_).trans ?_
    · exact sdiff_subset.trans smooth_sub
    · intro γ h
      obtain ⟨hγ,hn⟩:=mem_sdiff.mp h
      by_contra hq
      exact hn (mem_filter.mpr ⟨hγ,hq⟩)
    · exact Nat.mul_le_mul_right _ (branch_height C.sheet.bY.degree (by omega) a N)
  have hcoef (γ:K) (hγ:γ∈keep) : (C.markedBranch a γ).coeff N≠0:= by
    rw [MarkedSheet.markedBranch,coeff_map]
    exact (mem_filter.mp hγ).2
  have hdeg (γ:K) (hγ:γ∈keep) : (C.markedBranch a γ).natDegree=N := by
    refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr ?_) (hcoef γ hγ)
    intro i hi
    rw [MarkedSheet.markedBranch,coeff_map]
    apply qRoCwuc.marked_zero C.sheet _ _ (smooth_sub (hsub hγ))
    change C.genericParam ((C.branchEquation a).coeff i)=0
    rw [← coeff_map]
    exact coeff_eq_zero_of_natDegree_lt hi
  have hs (γ:K) (hγ:γ∈keep) :C.simple γ:= by
    let e :=mapRingHom (zY9 (C.sheet.parameter γ))
    have hn:C.markedBranch a γ≠0:= fun h=>hcoef γ hγ (by rw [h,coeff_zero])
    have hr :e (C.sheet.bY.equation.resultant C.sheet.bY.equation.derivative C.g (C.g-1))≠0:= by
      intro h
      apply hn
      change e (_ *_)=0
      rw [map_mul,h,zero_mul]
    exact eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero e _
      C.sheet.bY.degree.1 (by omega) hr _ (C.sheet.identity γ (smooth_sub (hsub hγ)))
  have hLift (γ:K) (hγ:γ∈keep) :=lift_at C a γ (A ⟨γ,hsub hγ⟩) (hcoef γ hγ)
  let lift (γ:K) :Series[X] :=if hγ:γ∈keep then Classical.choose (hLift γ hγ) else 0
  refine ⟨⟨a,hdif,hB,hb.trans hw,radical_monic _,keep,hsub,hbd,
    (fun γ hγ h=>hcoef γ hγ (by rw [h,coeff_zero])),hdeg,hs,lift,?_⟩⟩
  intro γ hγ
  simpa only [lift,dite_eq_left hγ] using Classical.choose_spec (hLift γ hγ)
end
end P5_7_3_3_4_1_2
end
section
set_option autoImplicit true
namespace qrpmzhd
theorem proof :qWEQiwd.c1 :=
  qL2osVa.of_children P5_7_3_3_4_1_1.proof P5_7_3_3_4_1_2.proof
    (qAjZDhd.of_children
      (qaJ7jxd.of_children P5_7_3_3_4_1_3_1_1.proof P5_7_3_3_4_1_3_1_2.proof)
      (P5_7_3_3_4_1_3_2.of_children P5_7_3_3_4_1_3_2_1.proof P5_7_3_3_4_1_3_2_2.proof))
    P5_7_3_3_4_1_4.proof qISdf9a.proof
    (P5_7_3_3_4_1_6.of_children
      (P5_7_3_3_4_1_6_1.of_children P5_7_3_3_4_1_6_1_1.proof P5_7_3_3_4_1_6_1_2.proof)
      P5_7_3_3_4_1_6_2.proof)
    (P5_7_3_3_4_1_7R.of_children P5_7_3_3_4_1_7R_1.proof P5_7_3_3_4_1_7R_2.proof
      P5_7_3_3_4_1_7R_3.proof
      (P5_7_3_3_4_1_7_2.of_children P5_7_3_3_4_1_7_2_1.proof P5_7_3_3_4_1_7_2_2.proof))
end qrpmzhd
end
