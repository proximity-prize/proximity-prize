import Mathlib.RingTheory.PowerSeries.Expand
import ProximityPrize.SubmissionLower.ZpWrDCd
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import ProximityPrize.SubmissionLower.ZiH02Bd
import ProximityPrize.SubmissionLower.ZKzStyc
import ProximityPrize.SubmissionLower.ZPlZTHb
import ProximityPrize.SubmissionLower.ZE3M1Qc
import ProximityPrize.SubmissionLower.ZEe4bHc
import ProximityPrize.SubmissionLower.ZxKiVod
set_option Elab.async false
open _root_ renaming Algebra.IsSeparable → zw7, CommRing → za6, Field → zrb, Ideal.Quotient.field → zxv, Ideal.Quotient.mk → zVv, Module.Finite → zAa, Module.IsTorsionFree → zYo, Module.finrank → zsE, Nat.eq_zero_of_le_zero → za7, Nat.le_of_dvd → zTm, Nat.sub_add_cancel → zxt, Nat.sub_le_sub_right → zIu, Polynomial.X → z7y, Polynomial.map_map → zoi, Polynomial.map_mul → zNl, Polynomial.map_prod → zeg, Polynomial.map_sub → z3A, PowerSeries → zpm, PowerSeries.C → zMG, PowerSeries.X → zWv, PowerSeries.coeff → z2o, PowerSeries.constantCoeff → zbO, PowerSeries.constantCoeff_C → zr8, PowerSeries.ext → zub, PowerSeries.map → zS4
section
set_option autoImplicit true
namespace P5_7_3_3_4_1_7_2_1
abbrev SeriesPolynomial (E :Type) [Semiring E] :=Polynomial (zpm E)
noncomputable abbrev expandRing {E :Type} [za6 E] (n:ℕ) (hn:n≠0) :
    zpm E →+* zpm E :=
  (PowerSeries.expand n hn).toRingHom
end P5_7_3_3_4_1_7_2_1
end
section
set_option autoImplicit true
namespace P5_7_3_3_4_1_7_2_1
noncomputable section
open Polynomial
open scoped Polynomial
variable {E :Type} [zrb E]
theorem cEo {q n:ℕ} [CharP E q] (hn:0<n) (hq:n<q) : (n:E)≠0 :=
  fun h=>hq.not_ge (zTm hn ((CharP.cast_eq_zero_iff E q n).mp h))
theorem depress {R:Type} [za6 R] (f :R[X]) (hf :f.Monic)
    (hpos :0<f.natDegree) (hu:IsUnit (f.natDegree :R)) :
    ∃ r :R,(f.taylor r).nextCoeff=0:= by
  let n:=f.natDegree - 1
  have hn:n+1=f.natDegree :=zxt hpos
  have hbound: (f.hasseDeriv n).natDegree≤1 := by
    apply (natDegree_hasseDeriv_le _ _).trans
    omega
  have heq :f.hasseDeriv n =
      C f.nextCoeff+C (f.natDegree :R)*Polynomial.X:= by
    ext (_ | _ | i)
    · simp [hasseDeriv_coeff,nextCoeff_of_natDegree_pos hpos,n]
    · rw [hasseDeriv_coeff,add_comm 1 n,hn,← hn,Nat.choose_succ_self_right,
        hn,coeff_natDegree,hf.leadingCoeff,mul_one]
      simp
    · rw [coeff_eq_zero_of_natDegree_lt (hbound.trans_lt (by omega))]
      simp
  refine ⟨-((↑(hu.unit⁻¹) :R)*f.nextCoeff),?_⟩
  rw [nextCoeff_of_natDegree_pos (by simpa using hpos),natDegree_taylor,taylor_coeff,heq]
  simp only [eval_add,eval_C,eval_mul,eval_X,mul_neg,← mul_assoc,
    IsUnit.mul_val_inv hu,one_mul,add_neg_cancel]
theorem residual_factors [IsSepClosed E] {q:ℕ} [CharP E q] {f :E[X]}
    (hm:f.Monic) (hpos :0<f.natDegree) (hq:f.natDegree<q)
    (hnext:f.nextCoeff=0) (hpow:f≠z7y ^f.natDegree) :
    ∃ (r :E) (e :ℕ) (b:E[X]),0<e∧0<b.natDegree∧b.eval r≠0 ∧
      f=(z7y - C r)^e*b:= by
  have hn : ¬ IsUnit f := fun hu=>(natDegree_eq_zero_of_isUnit hu).not_gt hpos
  obtain ⟨l,hl,hlf⟩:=WfDvdMonoid.exists_irreducible_factor hn hm.ne_zero
  have hsmall:=(natDegree_le_of_dvd hlf hm.ne_zero).trans_lt hq
  have hsep:=(separable_iff_derivative_ne_zero hl).mpr
    (P5_7_3_3_4_1_4.bD9
      (P5_7_3_3_4_1_4.irreducible_degree_pos hl) hsmall).1
  obtain ⟨r,hr⟩:=IsSepClosed.exists_root l
    (ne_of_gt (degree_pos_of_irreducible hl)) hsep
  let t:E[X] :=z7y - C r
  have ht:t.Monic:=monic_X_sub_C r
  have htd:t.natDegree=1 :=natDegree_X_sub_C r
  have hti:Irreducible t:=irreducible_X_sub_C r
  have htf :t∣f :=(dvd_iff_isRoot.mpr hr).trans hlf
  obtain ⟨e,b,hb,hf⟩:=WfDvdMonoid.max_power_factor hm.ne_zero hti
  have he :0<e := by
    by_contra! hn
    apply hb
    have hfb:f=b:= by simpa [za7 hn] using hf
    exact hfb ▸ htf
  have hbm:b.Monic:=(ht.pow e).of_mul_monic_left (hf ▸ hm)
  have ha : (t^e).natDegree=e := by simp [htd]
  have hbp:0<b.natDegree := by
    by_contra! h
    have hb1 :b=1 :=hbm.natDegree_eq_zero.mp (za7 h)
    have hf' : f=t^e := by simpa [hb1] using hf
    have hd:f.natDegree=e :=hf' ▸ ha
    have hne : (e :E)≠0:=cEo he (hd ▸ hq)
    have hz : (e :E) * -r=0:= by
      simpa only [hf',ht.nextCoeff_pow,t,nextCoeff_X_sub_C,nsmul_eq_mul] using hnext
    have hr0:r=0:=neg_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hne)
    exact hpow (by simpa [hd,t,hr0] using hf')
  exact ⟨r,e,b,he,hbp,fun hz=>hb (dvd_iff_isRoot.mpr hz),hf⟩
end
end P5_7_3_3_4_1_7_2_1
end
section
set_option autoImplicit true
namespace P5_7_3_3_4_1_7_2_1
noncomputable section
open Polynomial
open scoped Polynomial
variable {E :Type} [zrb E]
theorem newton (f :SeriesPolynomial E) (hm:f.Monic)
    (hnc:f.nextCoeff=0) (hpow:f≠z7y ^f.natDegree) :
    ∃ (n a :ℕ) (hn:n≠0) (Q:SeriesPolynomial E),
      Q.Monic∧Q.nextCoeff=0∧Q.map zbO≠z7y ^Q.natDegree ∧
      Q.scaleRoots (zWv ^a)=f.map (expandRing n hn) := by
  classical
  let d:=f.natDegree
  let S:=(Finset.range d).filter (fun i=>f.coeff i≠0)
  have hS:S.Nonempty := by
    by_contra! hz
    apply hpow
    apply Polynomial.ext
    intro i
    rw [coeff_X_pow]
    rcases lt_trichotomy i d with hi | rfl | hi
    · rw [ite_eq_right hi.ne]
      by_contra hn
      have hmem:i∈S:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hn⟩
      simp [hz] at hmem
    · simp only [d,coeff_natDegree,hm.leadingCoeff,ite_true]
    · rw [ite_eq_right hi.ne',coeff_eq_zero_of_natDegree_lt hi]
  let o (i:ℕ) :=(f.coeff i).order.toNat
  let slope (i:ℕ) :ℚ:=(o i:ℚ)/((d - i:ℕ) :ℚ)
  obtain ⟨j,hj,hjmin⟩:=S.exists_min_image slope hS
  have hjs :=Finset.mem_filter.mp hj
  have hjd:=Finset.mem_range.mp hjs.1
  let n:=d - j
  let a :=o j
  have hn:n≠0:=Nat.sub_ne_zero_of_lt hjd
  let e :zpm E →+* zpm E :=expandRing n hn
  have hdiv (i:ℕ) : (zWv:zpm E)^(a*(d-i))∣e (f.coeff i) := by
    by_cases hdi:d≤ i
    · simp [Nat.sub_eq_zero_of_le hdi]
    by_cases hi:f.coeff i=0
    · simp [hi]
    have hin:i<d:=lt_of_not_ge hdi
    have hle :=hjmin i (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin,hi⟩)
    have hle' : a*(d-i)≤n*o i:= by
      change (a :ℚ)/(n:ℚ)≤(o i:ℚ)/((d - i:ℕ) :ℚ) at hle
      rw [div_le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)
        (by exact_mod_cast Nat.sub_pos_of_lt hin)] at hle
      rw [mul_comm n]
      exact_mod_cast hle
    have hv :=map_dvd e (PowerSeries.X_pow_order_dvd (φ:=f.coeff i))
    have heX:e zWv=zWv ^n:=PowerSeries.expand_X n hn
    rw [map_pow,heX,← pow_mul] at hv
    exact (pow_dvd_pow _ hle').trans hv
  choose B hB using hdiv
  let Q:SeriesPolynomial E :=Polynomial.ofFn (d+1) (fun i=>B i.val)
  have hQ (i:ℕ) (hi:i≤d) :Q.coeff i=B i :=
    ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_of_le hi)
  have hQtop:Q.coeff d = 1 := by
    have he :=hB d
    rw [Nat.sub_self,mul_zero,pow_zero,one_mul,show d=f.natDegree from rfl,
      coeff_natDegree,hm.leadingCoeff,map_one] at he
    exact (hQ d le_rfl).trans he.symm
  have hQd:Q.natDegree=d :=
    natDegree_eq_of_le_of_coeff_ne_zero
      (Nat.le_of_lt_succ (ofFn_natDegree_lt (Nat.succ_pos d) _)) (by simp [hQtop])
  have hQm:Q.Monic:= by rw [Monic,leadingCoeff,hQd,hQtop]
  have hscale :Q.scaleRoots (zWv ^a)=f.map e := by
    ext i
    rw [coeff_scaleRoots,hQd,← pow_mul,coeff_map,mul_comm]
    by_cases hi:i≤d
    · rw [hQ i hi,← hB i]
    · have hdi:=lt_of_not_ge hi
      rw [coeff_eq_zero_of_natDegree_lt (hQd ▸ hdi),coeff_eq_zero_of_natDegree_lt hdi,
        map_zero,mul_zero]
  have hnQ:Q.nextCoeff=0:= by
    have hz :=congrArg (fun F:SeriesPolynomial E=>F.nextCoeff) hscale
    rw [nextCoeff_map_of_leadingCoeff_ne_zero _ (by simp [hm.leadingCoeff]),hnc,map_zero] at hz
    have hpos :0<d:=Nat.zero_lt_of_lt hjd
    have hqc:Q.nextCoeff= Q.coeff (d - 1) := by
      rw [nextCoeff_of_natDegree_pos (hQd ▸ hpos),hQd]
    rw [nextCoeff_of_natDegree_pos (by simpa [hQd] using hpos),natDegree_scaleRoots,
      coeff_scaleRoots,hQd,← hqc] at hz
    exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ (pow_ne_zero _ PowerSeries.X_ne_zero))
  have hrQ:Q.map zbO≠z7y ^Q.natDegree := by
    intro h
    have hc:=congrArg (fun F:E[X]=>F.coeff j) h
    rw [coeff_map,hQ j hjd.le,hQd,coeff_X_pow,ite_eq_right hjd.ne] at hc
    have he :=congrArg (z2o (0+n*a) (R:=E)) (hB j)
    have hmul :a*(d - j)=n*a :=mul_comm a n
    rw [hmul,PowerSeries.coeff_X_pow_mul,PowerSeries.coeff_zero_eq_constantCoeff_apply,hc] at he
    change (PowerSeries.expand n hn (f.coeff j)).coeff (0+n*a)=0 at he
    rw [zero_add,PowerSeries.coeff_expand_mul] at he
    exact PowerSeries.coeff_order hjs.2 he
  exact ⟨n,a,hn,Q,hQm,hnQ,hrQ,hscale⟩
end
end P5_7_3_3_4_1_7_2_1
end
section
set_option autoImplicit true
namespace P5_7_3_3_4_1_7_2_1
noncomputable section
open Polynomial
open scoped Polynomial
open IsLocalRing (ResidueField residue maximalIdeal)
variable {E :Type} [zrb E]
theorem lift_factor (F:SeriesPolynomial E) (hF:F.Monic)
    (r :E) (k :ℕ) (b:E[X]) (hb:b.eval r≠0)
    (hred:F.map zbO=(z7y - C r)^k*b) :
    ∃ A B:SeriesPolynomial E,A.Monic∧B.Monic∧F=A*B∧A.natDegree=k := by
  let R:=zpm E
  let:IsAdicComplete (maximalIdeal R) R:= by
    change IsAdicComplete (maximalIdeal (zpm E)) (zpm E)
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  let φ:E →+* ResidueField R:=(residue R).comp zMG
  have hφ:φ.comp zbO=residue R:= by
    apply RingHom.ext
    intro x
    change residue R (zMG (zbO x))=residue R x
    rw [← sub_eq_zero,← map_sub,IsLocalRing.residue_eq_zero_iff]
    change _∈maximalIdeal (zpm E)
    rw [← PowerSeries.ker_coeff_eq_max_ideal,RingHom.mem_ker,map_sub,
      zr8,sub_self]
  let s :R:=zMG r
  let G:=F.taylor s
  have hG:G.Monic:=hF.comp_X_add_C s
  have hGred:G.map (residue R)=z7y ^k*(b.taylor r).map φ:= by
    have hlin: ((z7y - C r).taylor r)=Polynomial.X:= by
      simp [taylor_apply,sub_comp]
    rw [← hφ,← zoi]
    change ((F.taylor s).map zbO).map φ= _
    rw [map_taylor,show zbO s=r from zr8 r,
      hred,taylor_mul,taylor_pow,hlin,zNl,Polynomial.map_pow,map_X]
  have hne : (G:zpm R).map (residue R)≠0:= by
    rw [← polynomial_map_coe]
    exact fun h=>(hG.map _).ne_zero (Polynomial.coe_eq_zero_iff.mp h)
  have hord: ((G:zpm R).map (residue R)).order=k := by
    rw [← polynomial_map_coe,hGred,Polynomial.coe_mul,Polynomial.coe_pow,Polynomial.coe_X,
      PowerSeries.order_mul,PowerSeries.order_X_pow]
    have h0: (((b.taylor r).map φ: (ResidueField R)[X]) :
        zpm (ResidueField R)).order=0:= by
      by_contra h
      have :=PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp h
      rw [Polynomial.constantCoeff_coe,coeff_map,taylor_coeff_zero] at this
      exact hb (φ.injective (this.trans (map_zero φ).symm))
    rw [h0,add_zero]
  obtain ⟨A,U,hU⟩:=PowerSeries.exists_isWeierstrassFactorization hne
  have hAm:A.Monic:=hU.isDistinguishedAt.monic
  have hAd:A.natDegree=k := by
    rw [hU.natDegree_eq_toNat_order_map,hord,ENat.toNat_natCast]
  have hdiv :A∣G:= by
    apply (modByMonic_eq_zero_iff_dvd hAm).mp
    have hR: (G %ₘ A).degree <
        ((A:zpm R).map (zVv (maximalIdeal R))).order.toNat := by
      rw [← polynomial_map_coe,hU.isDistinguishedAt.map_eq_X_pow,Polynomial.coe_pow,
        Polynomial.coe_X,PowerSeries.order_X_pow,ENat.toNat_natCast,
        ← degree_eq_natDegree hAm.ne_zero]
      exact degree_modByMonic_lt _ hAm
    have heq : (A:zpm R)*(U - ↑(G /ₘ A)) = ↑(G %ₘ A) := by
      rw [mul_sub,← hU.eq_mul,← Polynomial.coe_mul,← Polynomial.coe_sub,
        modByMonic_eq_sub_mul_div]
    exact (hU.isDistinguishedAt.isWeierstrassDivisorAt'.eq_zero_of_mul_eq hR heq).2
  obtain ⟨B,hB⟩:=hdiv
  have hBm:B.Monic:=hAm.of_mul_monic_left (hB ▸ hG)
  refine ⟨A.taylor (-s),B.taylor (-s),hAm.comp_X_add_C _,hBm.comp_X_add_C _,?_,
    (natDegree_taylor _ _).trans hAd⟩
  have h:=congrArg (fun T:R[X]=>T.taylor (-s)) hB
  change (taylor (-s)) (taylor s F)=(taylor (-s)) (A*B) at h
  rw [taylor_taylor,neg_add_cancel,taylor_zero,taylor_mul] at h
  exact h
end
end P5_7_3_3_4_1_7_2_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_7_2_1
noncomputable section
open Polynomial
open scoped Polynomial
open P5_7_3_3_4_1_7_2 (aQ jz ramify SplitAt)
open P5 (K p)
open cu (L)
variable {E :Type} [zrb E]
private theorem map_expand_mul (F:SeriesPolynomial E) (n m:ℕ) (hn:n≠0) (hm:m≠0) :
    (F.map (expandRing n hn)).map (expandRing m hm) =
      F.map (expandRing (m*n) (mul_ne_zero hm hn)) := by
  rw [zoi]
  congr 1
  exact congrArg AlgHom.toRingHom (PowerSeries.expand_mul_eq_comp m hm n hn).symm
private theorem combine {F G:SeriesPolynomial E} {m n:ℕ} {hm:m≠0} {hn:n≠0}
    (hF: (F.map (expandRing m hm)).Splits) (hG: (G.map (expandRing n hn)).Splits) :
    ((F*G).map (expandRing (m*n) (mul_ne_zero hm hn))).Splits := by
  have hF' := hF.map (expandRing n hn)
  rw [map_expand_mul] at hF'
  have hG' := hG.map (expandRing m hm)
  rw [map_expand_mul] at hG'
  rw [zNl]
  exact (by simpa only [Nat.mul_comm n m] using hF' :
    (F.map (expandRing (m*n) (mul_ne_zero hm hn))).Splits).mul hG'
private theorem split_monic [IsSepClosed E] {q:ℕ} [CharP E q] :
    ∀ d<q,∀ F:SeriesPolynomial E,F.Monic→F.natDegree=d →
      ∃ (n:ℕ) (hn:n≠0),(F.map (expandRing n hn)).Splits := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd F hF hdF
    by_cases hsmall:d≤1
    · exact ⟨1,one_ne_zero,(Splits.of_natDegree_le_one_of_monic (hdF ▸ hsmall) hF).map _⟩
    have hpos :0<F.natDegree := by omega
    have hu:IsUnit (F.natDegree :zpm E) := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      simpa only [map_natCast] using
        (isUnit_iff_ne_zero.mpr (cEo hpos (hdF ▸ hd) : (F.natDegree :E)≠0))
    obtain ⟨r,hr⟩:=depress F hF hpos hu
    let f :=F.taylor r
    have hfm:f.Monic:=hF.comp_X_add_C r
    have hfd:f.natDegree=d:=(natDegree_taylor F r).trans hdF
    have htranslate {n:ℕ} (hn:n≠0) (hs : (f.map (expandRing n hn)).Splits) :
        (F.map (expandRing n hn)).Splits := by
      have ht:=hs.taylor (-(expandRing n hn r))
      change (((F.taylor r).map (expandRing n hn)).taylor (-(expandRing n hn r))).Splits at ht
      simpa only [map_taylor,taylor_taylor,neg_add_cancel,taylor_zero] using ht
    by_cases hf :f=z7y ^f.natDegree
    · have hs :f.Splits := by
        exact (congrArg Polynomial.Splits hf).mpr (Splits.X_pow _)
      exact ⟨1,one_ne_zero,htranslate one_ne_zero (hs.map _)⟩
    obtain ⟨n,a,hn,Q,hQ,hQn,hQ0,hscale⟩:=newton f hfm hr hf
    have hQd:Q.natDegree=d:= by
      rw [← natDegree_scaleRoots Q (zWv ^a),hscale,hfm.natDegree_map,hfd]
    let q₀:= Q.map zbO
    have hq₀m:q₀.Monic:=hQ.map _
    have hq₀d:q₀.natDegree=d:=(hQ.natDegree_map _).trans hQd
    have hq₀n:q₀.nextCoeff=0:= by
      change (Q.map zbO).nextCoeff=0
      rw [nextCoeff_map_of_leadingCoeff_ne_zero _ (by simp [hQ.leadingCoeff]),hQn,map_zero]
    obtain ⟨z,k,b,hkp,hbp,hb,heq⟩:=residual_factors hq₀m
      (by omega) (hq₀d ▸ hd) hq₀n (by simpa only [hq₀d,hQd] using hQ0)
    obtain ⟨U,V,hUm,hVm,hUV,hUd⟩:=lift_factor Q hQ z k b hb heq
    have hredDegree :k+b.natDegree=d:= by
      have hb0:b≠0:= fun h=> by simp [h] at hbp
      have hd' := congrArg natDegree heq
      simpa [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero _)) hb0,hq₀d] using hd'.symm
    have hsum:U.natDegree+V.natDegree=d :=
      (hUm.natDegree_mul hVm).symm.trans (hUV ▸ hQd)
    obtain ⟨s,hs,hUs⟩:=ih U.natDegree (by omega) (by omega) U hUm rfl
    obtain ⟨t,ht,hVt⟩:=ih V.natDegree (by omega) (by omega) V hVm rfl
    have hsplit : (Q.map (expandRing (s*t) (mul_ne_zero hs ht))).Splits := by
      rw [hUV]
      exact combine hUs hVt
    let e :=expandRing (s*t) (mul_ne_zero hs ht) (E :=E)
    have heq' : (Q.map e).scaleRoots (e (zWv ^a)) =
        (f.map (expandRing n hn)).map e := by
      rw [← map_scaleRoots _ _ _ (by simp [hQ.leadingCoeff]),hscale]
    have hfinal: ((f.map (expandRing n hn)).map e).Splits :=
      heq' ▸ hsplit.scaleRoots _
    rw [show e=expandRing (s*t) (mul_ne_zero hs ht) from rfl,map_expand_mul] at hfinal
    exact ⟨(s*t)*n,mul_ne_zero (mul_ne_zero hs ht) hn,htranslate _ hfinal⟩
private theorem enumerate {R:Type} [za6 R] [IsDomain R] {F:R[X]} {g:ℕ}
    (hm:F.Monic) (hs :F.Splits) (hd:F.natDegree=g) :
    ∃ b:Fin g→R,F = ∏ i,(z7y - C (b i)) := by
  let l:=F.roots.toList
  have hl:l.length=g:=(Multiset.length_toList _).trans (hs.natDegree_eq_card_roots.symm.trans hd)
  rw [← hl]
  refine ⟨l.get,?_⟩
  have hp (l:List R) : (∏ i:Fin l.length,(z7y - C (l.get i))) =
      (Multiset.map (fun x=>z7y - C x) (l:Multiset R)).prod:= by
    rw [← List.prod_ofFn]
    change (List.ofFn ((fun x=>z7y - C x) ∘ l.get)).prod= _
    rw [← List.map_ofFn,List.ofFn_get]
    rfl
  rw [hp l]
  simpa only [l,Multiset.coe_toList] using hs.eq_prod_roots_of_monic hm
theorem proof :P5_7_3_3_4_1_7_2.c1 := by
  intro f g _ hg hdeg hu
  have hfd:f.natDegree=g:=natDegree_eq_of_le_of_coeff_ne_zero hdeg hu.ne_zero
  have hul:IsUnit f.leadingCoeff := by rwa [leadingCoeff,hfd]
  let u:=hul.unit
  let F:=C (↑(u⁻¹) :P5_7_3_3_4_1_7.DoubleSeries)*f
  have hFm:F.Monic:= by
    simpa only [Units.smul_def,smul_eq_C_mul] using monic_of_isUnit_leadingCoeff_inv_smul hul
  have hFd:F.natDegree=g:=(natDegree_C_mul (u⁻¹).ne_zero).trans hfd
  have hF:f=C (f.coeff g)*F:= by
    have he : (f.coeff g) * ↑(u⁻¹)=1 := by
      simpa only [u,leadingCoeff,hfd] using IsUnit.mul_val_inv hul
    change f=C (f.coeff g)*(C (↑(u⁻¹) :P5_7_3_3_4_1_7.DoubleSeries)*f)
    rw [← mul_assoc,← C_mul,he,C_1,one_mul]
  let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
  let:CharP aQ p :=
    charP_of_injective_ringHom (jz.comp zMG).injective p
  let G:=F.map (zS4 jz)
  have hG:=hFm.map (zS4 jz)
  have hGd:=(hFm.natDegree_map (zS4 jz)).trans hFd
  obtain ⟨n,hn,hs⟩:=split_monic g hg G hG hGd
  rw [show G=F.map (zS4 jz) from rfl,zoi] at hs
  obtain ⟨b,hb⟩:=enumerate (hFm.map (ramify jz n hn)) hs
    ((hFm.natDegree_map _).trans hFd)
  refine ⟨n,hn,b,?_⟩
  unfold SplitAt
  dsimp only
  exact (congrArg (fun Q=>Q.map (ramify jz n hn)) hF).trans
    (by rw [zNl,map_C,hb])
end
end P5_7_3_3_4_1_7_2_1
end
section
set_option autoImplicit true
set_option Elab.async false
namespace P5_7_1_5Q
theorem c4321 :qZfVj1b.c1 :=qxblDlc.curve_field
theorem c4322 :qZfVj1b.c2 :=qw8MfCe.proof
theorem c434521 :qnSUPza.c1 :=quQ0Dxa.directions
theorem c434522 :qnSUPza.c2 :=quQ0Dxa.lifts
theorem c43464 :qZn79Eb.c4 :=qeBKasb.vertical
end P5_7_1_5Q
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
namespace P5_7_3_3_4_1_3_2_2
noncomputable section
open IsLocalRing IsDedekindDomain WithZero Polynomial
open scoped WithZero
open q9r9FBa (valuationDVR adicBase)
open private bounded adic_separable from ProximityPrize.SubmissionLower.Zi7X5ad
open private small_iff residue_zero tangent_uniformizer tangent_ideal log_of_tangent from ProximityPrize.SubmissionLower.ZxKiVod
open private local_degree_bounds from ProximityPrize.SubmissionLower.ZR3mCBd
private theorem separable_small {K L:Type} [zrb K] [zrb L] [Algebra K L]
    [zAa K L] (p:ℕ) [CharP K p] (h:zsE K L<p) :
    Algebra.IsSeparable K L:= by
  constructor
  intro x
  have hi:=Algebra.IsIntegral.isIntegral (R:=K) x
  let f :=minpoly K x
  have hir :Irreducible f :=minpoly.irreducible hi
  have hn:0<f.natDegree :=natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hir)
  have hnp:f.natDegree<p:=(minpoly.natDegree_le (A:=K) x).trans_lt h
  apply (separable_iff_derivative_ne_zero hir).mpr
  intro hd
  have hc:=congrArg (fun g:K[X]=>g.coeff (f.natDegree - 1)) hd
  have hidx :f.natDegree - 1+1=f.natDegree := by omega
  rw [coeff_derivative,hidx,(minpoly.monic hi).coeff_natDegree,one_mul,coeff_zero] at hc
  have hz : (f.natDegree :K)=0:= by rw [← hidx,Nat.cast_add,Nat.cast_one]; exact hc
  exact (not_le_of_gt hnp) (zTm hn ((CharP.cast_eq_zero_iff K p _).1 hz))
private theorem unit_nat {E :Type} [zrb E] (w:Valuation E ℤᵐ⁰)
    (p:ℕ) [CharP E p] {e :ℕ} (he :0<e) (hp:e<p) :w (e :E)=1 := by
  let W:=w.valuationSubring
  let:CharP W p:=(ValuationSubring.subtype W).charP Subtype.val_injective p
  let:CharP (ResidueField W) p :=
    CharP.of_ringHom_of_ne_zero (residue W) p (he.trans hp).ne'
  have hn: (e :ResidueField W)≠0:= fun hz =>
    hp.not_ge (zTm he ((CharP.cast_eq_zero_iff _ _ _).mp hz))
  have hu:IsUnit (e :W) :=(residue_ne_zero_iff_isUnit _).mp (by rwa [map_natCast])
  exact (Valuation.valuationSubring.integers w).one_of_isUnit hu
private theorem adic_log {F E :Type} [zrb F] [zrb E] [Algebra F E]
    (v :Valuation F ℤᵐ⁰) (w:Valuation E ℤᵐ⁰) [v.HasExtension w]
    [zw7 (ResidueField v.valuationSubring) (ResidueField w.valuationSubring)]
    (d:Derivation ℤ E E) (hbase : ∀ a :v.valuationSubring,w (d (algebraMap F E a))≤1)
    {t π:E} (hπ:w π=exp (-1 :ℤ)) {e :ℕ} (he :0<e) (heunit :w (e :E)=1)
    (ht:w t=w π^e) (hdt:w (d t)≤w t)
    {C:ℤᵐ⁰} (hC:1≤C) (hb : ∀ x,w x≤1→w (d x)≤C)
    (z :E) (hz :z≠0) :w (d z/z)≤1 := by
  have hπpos :0<w π:= by rw [hπ]; exact exp_pos
  have hπlt:w π<1 := by rw [hπ,exp_lt_one_iff]; decide
  let nY (n:ℕ) :=π^n•d
  let good (n:ℕ) := ∀ x,w x≤1→w (nY n x)≤1
  have hscale (n:ℕ) (x :E) :w (nY n x)=w π^n*w (d x) := by
    change w (π^n*d x)= _
    rw [map_mul,map_pow]
  have hex : ∃ n,good n:= by
    have hCpos :0<C:=zero_lt_one.trans_le hC
    obtain ⟨n,hn⟩:=exists_exp_neg_natCast_lt (inv_ne_zero hCpos.ne')
    have hn' : w π^n≤C⁻¹:= by rw [hπ,← exp_nsmul]; simpa using hn.le
    refine ⟨n,fun x hx => ?_⟩
    rw [hscale]
    exact (mul_le_mul' hn' (hb x hx)).trans_eq (inv_mul_cancel₀ hCpos.ne')
  classical
  have hreg:good 0:= by
    let n:=Nat.find hex
    have hn:good n:=Nat.find_spec hex
    by_cases hn0:n=0
    · exact hn0 ▸ hn
    have hn1 :n - 1+1=n:=zxt (Nat.pos_of_ne_zero hn0)
    have hs :w π^n≤w π:= by
      conv_lhs=>rw [← hn1,pow_succ]
      exact mul_le_of_le_one_left' (pow_le_one₀ zero_le hπlt.le)
    have hstay :w (nY n t)≤w π^e := by
      rw [hscale]
      exact (mul_le_of_le_one_left' (hs.trans hπlt.le)).trans (hdt.trans_eq ht)
    have hπD:=tangent_uniformizer w (nY n) hπpos ht he heunit hn hstay
    have hres :=residue_zero v w (nY n) hn (tangent_ideal w hπ (nY n) hn hπD) (by
      intro a
      rw [hscale]
      exact ((mul_le_of_le_one_right' (hbase a)).trans hs).trans_lt hπlt)
    have hprev :good (n - 1) := by
      intro x hx
      have hh:=small_iff.mp (hres x hx)
      rw [hscale,← hπ,← hn1,pow_succ] at hh
      rw [hscale]
      have hmul :w π^(n - 1)*w π*w (d x)=w π*(w π^(n - 1)*w (d x)) := by ac_rfl
      apply (mul_le_mul_iff_right₀ hπpos).mp
      simpa only [hmul,mul_one] using hh
    exact (Nat.find_min hex (show n - 1<n by omega) hprev).elim
  have hreg' (x :E) (hx :w x≤1) :w (d x)≤1 := by
    simpa only [hscale,pow_zero,one_mul] using hreg x hx
  exact log_of_tangent w hπ hz d hreg'
    (tangent_uniformizer w d hπpos ht he heunit hreg' (hdt.trans_eq ht))
theorem proof :P5_7_3_3_4_1_3_2.c2 := by
  intro F E _ _ _ _ _ _ iE p _ hdeg v hv D d hd hD z hz
  have hiE :iE=Ring.toIntAlgebra E :=Subsingleton.elim _ _
  subst iE
  let A:=v.valuationSubring
  let B:=integralClosure A E
  let:IsDiscreteValuationRing A:=valuationDVR v hv
  let:IsScalarTower A B E :=IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  let:zYo A E := .trans_faithfulSMul A F E
  let:zYo A B:=IsIntegralClosure.isTorsionFree A E
  let:Module.Free A B:=IsIntegralClosure.module_free A F E B
  let:zAa A B:=IsIntegralClosure.finite A F E B
  let:IsDedekindDomain B:=IsIntegralClosure.isDedekindDomain A F E B
  let:IsFractionRing B E :=IsIntegralClosure.isFractionRing_of_finite_extension A F E B
  let:Algebra.IsIntegral A B:=IsIntegralClosure.isIntegral_algebra A E
  let m:=IsDiscreteValuationRing.maximalIdeal A
  have hB:zsE A B<p:=(IsIntegralClosure.rank A F E B).symm ▸ hdeg
  have hp:p≠0:=(Nat.zero_le _).trans_lt hdeg |>.ne'
  let:CharP A p:=(ValuationSubring.subtype A).charP Subtype.val_injective p
  let:CharP E p:=charP_of_injective_ringHom (algebraMap F E).injective p
  obtain ⟨t,ht⟩:=hv (exp (-1 :ℤ))
  have hvals (q:HeightOneSpectrum B) :q.valuation E (d z/z)≤1 := by
    let w:=q.valuation E
    let:q.asIdeal.LiesOver (maximalIdeal A) :=
      ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q.asIdeal)).symm⟩
    let:q.asIdeal.LiesOver m.asIdeal:=inferInstanceAs (q.asIdeal.LiesOver (maximalIdeal A))
    let:q.asIdeal.IsMaximal:=q.isMaximal
    let e :=q.asIdeal.ramificationIdx A
    obtain ⟨he,hram,hf⟩:=local_degree_bounds (A:=A) q
    have hval (x :F) :w (algebraMap F E x)=v x^e := by
      change q.valuation E (algebraMap F E x)= _
      rw [← m.valuation_liesOver E q x,adicBase v hv,
        Ideal.ramificationIdx'_eq_ramificationIdx _ _ m.ne_bot]
    let:v.HasExtension w:=qwQWGra.extension v w e he hval
    let:zrb (A ⧸ maximalIdeal A) :=zxv (maximalIdeal A)
    let:zrb (B ⧸ q.asIdeal) :=zxv q.asIdeal
    let:zAa (A ⧸ maximalIdeal A) (B ⧸ q.asIdeal) :=inferInstance
    let:CharP (A ⧸ maximalIdeal A) p :=
      CharP.of_ringHom_of_ne_zero (zVv _) p hp
    have hres :zsE (A ⧸ maximalIdeal A) (B ⧸ q.asIdeal)<p:= by
      rw [← Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) q.asIdeal]
      exact hf.trans_lt hB
    let:zw7 (ResidueField A) (ResidueField w.valuationSubring) :=
      adic_separable v w q rfl (separable_small p hres)
    have hreg (a :A) :w (algebraMap A E a)≤1 := by
      change w (algebraMap F E (a :F))≤1
      rw [hval]
      exact pow_le_one₀ zero_le a.property
    have htan (a :F) :w (d (algebraMap F E a))≤w (algebraMap F E a) := by
      rw [hd,hval,hval]
      exact pow_le_pow_left₀ zero_le (hD a) _
    have hbase (a :A) :w (d (algebraMap A E a))≤1 :=(htan a).trans (hreg a)
    obtain ⟨C,hC,hb⟩:=bounded v w hreg q rfl d hbase
    obtain ⟨π,hπ⟩:=q.valuation_exists_uniformizer E
    exact adic_log v w d hbase hπ he (unit_nat w p he (hram.trans_lt hB))
      ((hval t).trans (congrArg (· ^ e) (ht.trans hπ.symm))) (htan t) hC hb z hz
  obtain ⟨b,hb⟩:=HeightOneSpectrum.mem_integers_of_valuation_le_one (R:=B) E _ hvals
  rw [← hb]
  exact b.property
end
end P5_7_3_3_4_1_3_2_2
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_7_2_2
noncomputable section
open Polynomial P5_7_3_3_4_1_7 P5_7_3_3_4_1_7_2
abbrev R:=zpm aQ
def delta (D:aQ →+ aQ) (a :R) :R :=
  PowerSeries.mk fun k=>D (z2o k a)
@[simp] theorem coeff_delta (D:aQ →+ aQ) (a :R) (k :ℕ) :
    z2o k (delta D a)=D (z2o k a) :=
  PowerSeries.coeff_mk _ _
private def deltaAdd (D:aQ →+ aQ) :R →+ R where
  toFun:=delta D
  map_zero' := by apply zub; simp
  map_add' a b:= by apply zub; simp
private def deltaDer (D:aQ →+ aQ) (hD:ExtendsSeed D) :Derivation ℤ R R :=
  Derivation.mk' (deltaAdd D).toIntLinearMap (by
    intro a b
    change delta D (a*b)=a*delta D b+b*delta D a
    apply zub
    intro i
    simp only [coeff_delta,map_add,PowerSeries.coeff_mul,map_sum,hD.1,
      Finset.sum_add_distrib]
    congr 1
    exact Finset.Nat.sum_antidiagonal_swap
      (f := fun p=>z2o p.1 b*D (z2o p.2 a)))
private theorem delta_ramify (D:aQ →+ aQ) (hD:ExtendsSeed D)
    (n:ℕ) (hn:n≠0) (a :DoubleSeries) :
    delta D (ramify jz n hn a)=ramify jz n hn (Lv a) := by
  apply zub
  intro i
  rw [coeff_delta]
  change D (z2o i (PowerSeries.expand n hn (zS4 jz a))) =
    z2o i (PowerSeries.expand n hn (zS4 jz (Lv a)))
  simp only [PowerSeries.coeff_expand,PowerSeries.coeff_map,Lv,PowerSeries.coeff_mk]
  split_ifs with hi
  · exact hD.2 _
  · exact map_zero _
private theorem dMp (f :LocalEquation) (k :ℕ) :
    (jetDerivative f).coeff k=Lv (f.coeff k) := by
  unfold jetDerivative
  change (AddMonoidAlgebra.map _ f.toFinsupp).coeff k= _
  rw [AddMonoidAlgebra.coeff_map,Finsupp.mapRange_apply,toFinsupp_apply]
  rfl
theorem jet_degree (f :LocalEquation) : (jetDerivative f).natDegree≤f.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [dMp,coeff_eq_zero_of_natDegree_lt hi]
  apply zub
  intro k
  simp [Lv]
theorem zD (D:aQ →+ aQ) (hD:ExtendsSeed D)
    (n:ℕ) (hn:n≠0) (f :LocalEquation) (b:R)
    (hb: (f.map (ramify jz n hn)).eval b=0) :
    ((jetDerivative f).map (ramify jz n hn)).eval b +
      (f.map (ramify jz n hn)).derivative.eval b*delta D b=0:= by
  let e :=ramify jz n hn
  let δ:=deltaDer D hD
  have h:=δ.apply_eval_eq b (f.map e)
  change (f.map e).eval b=0 at hb
  rw [hb,map_zero,smul_eq_mul] at h
  have hm:PolynomialModule.equivPolynomial (δ.mapCoeffs (f.map e)) =
      (jetDerivative f).map e := by
    apply Polynomial.ext
    intro i
    change δ ((f.map e).coeff i)=((jetDerivative f).map e).coeff i
    rw [coeff_map,coeff_map,dMp]
    exact delta_ramify D hD n hn _
  have he : ((jetDerivative f).map e).eval b =
      PolynomialModule.eval b (δ.mapCoeffs (f.map e)) := by
    rw [← hm]
    change aeval b (PolynomialModule.equivPolynomial (δ.mapCoeffs (f.map e)))= _
    simp [PolynomialModule.aeval_equivPolynomial]
  rw [he]
  exact h.symm
end
end P5_7_3_3_4_1_7_2_2
end
section
set_option autoImplicit true
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_7_2_2
noncomputable section
open Polynomial P5_7_3_3_4_1_7 P5_7_3_3_4_1_7_2
open q1kuFjb (mapTwice)
def lineRoot {A:Type*} [za6 A] (a v :A) :A[X] :=
  C a+Polynomial.X*C v
def tiltedProd {g:ℕ} (D:aQ →+ aQ) (b:Fin g→R) :R[X][X] :=
  ∏ i,(z7y - C (lineRoot (b i) (delta D (b i))))
private theorem res_split {A:Type*} [za6 A] [Nontrivial A]
    {f :A[X]} (B:A[X]) {a :A} {g n:ℕ} {b:Fin g→A}
    (hf :f=C a * ∏ i,(z7y - C (b i))) (hB:B.natDegree≤n) :
    f.resultant B g n=a^n * ∏ i,B.eval (b i) := by
  let L (i:Fin g) :=z7y - C (b i)
  have hd: (∏ i,L i).natDegree=g:= by
    rw [natDegree_prod_of_monic _ _ (fun _ _=>monic_X_sub_C _)]
    simp [L]
  have hp:=resultant_prod_left Finset.univ L B n (by simp [L,(monic_X_sub_C _).leadingCoeff]) hB
  rw [hd] at hp
  rw [hf,resultant_C_mul_left]
  congr 1
  simpa only [L,natDegree_X_sub_C,resultant_X_sub_C_left _ _ _ hB] using hp
private theorem map_embed {A B:Type} [za6 A] [za6 B] (e :A →+* B) (f :A[X]) :
    (f.map embed).map (mapTwice e)=(f.map e).map embed:= by
  rw [zoi,zoi]
  congr 1
  exact RingHom.ext fun a=> by simp [mapTwice,embed]
private theorem cutter_map {A B:Type} [za6 A] [za6 B] (e :A →+* B) (f q:A[X]) :
    (an1 f q).map (mapTwice e)=an1 (f.map e) (q.map e) := by
  dsimp only [an1]
  simp only [Polynomial.map_add,zNl,z3A,derivative_map,
    map_embed,map_C,map_X]
  simp [mapTwice]
private theorem cutter_degree {A:Type} [za6 A] (f q:A[X]) {g:ℕ}
    (hg:0<g) (hf :f.natDegree≤g) (hq:q.natDegree≤g) :
    (an1 f q).natDegree≤g:= by
  dsimp only [an1]
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · have hd:=(natDegree_derivative_le (f.map embed)).trans
      (zIu (natDegree_map_le.trans hf) 1)
    have hz : (C (z7y:A[X][X])-Polynomial.X).natDegree≤1 :=
      (natDegree_sub_le _ _).trans (max_le (by simp) natDegree_X_le)
    exact natDegree_mul_le.trans ((Nat.add_le_add hd hz).trans (by omega))
  · exact (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hq)
theorem factorization (f :LocalEquation) {g:ℕ} (hg:0<g) (hf :f.natDegree≤g)
    (n:ℕ) (hn:n≠0) (b:Fin g→R) (D:aQ →+ aQ)
    (hb:SplitAt f g n hn b) (hD:ExtendsSeed D) :
    let e :=ramify jz n hn
    mapTwice e (numerator f g)=embed (e (denominator f g))*tiltedProd D b:= by
  let e :=ramify jz n hn
  let F:=f.map e
  let Q:=(jetDerivative f).map e
  let a :=e (f.coeff g)
  let B:=an1 F Q
  let ι:R →+* R[X][X] :=embed
  change F=C a * ∏ i,(z7y - C (b i)) at hb
  have hF:F.natDegree≤g:=natDegree_map_le.trans hf
  have hQ:Q.natDegree≤g:=natDegree_map_le.trans ((jet_degree f).trans hf)
  have hd:F.derivative.natDegree≤g - 1 :=
    (natDegree_derivative_le F).trans (zIu hF 1)
  have hB:B.natDegree≤g:=cutter_degree F Q hg hF hQ
  have hb' : F.map ι=C (ι a) * ∏ i,(z7y - C (ι (b i))) := by
    rw [hb,zNl,zeg,map_C]
    simp only [z3A,map_X,map_C]
  have hroot (i:Fin g) :F.eval (b i)=0:= by
    rw [hb,eval_mul,eval_prod]
    simp only [eval_sub,eval_X,eval_C]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _),mul_zero]
  have ht (i:Fin g) :B.eval (ι (b i))=ι (F.derivative.eval (b i)) *
      (z7y - C (lineRoot (b i) (delta D (b i)))) := by
    have he :Q.eval (b i)+F.derivative.eval (b i)*delta D (b i)=0 :=
      zD D hD n hn f _ (hroot i)
    have hq:Q.eval (b i) = -(F.derivative.eval (b i)*delta D (b i)) :=
      eq_neg_of_add_eq_zero_left he
    change (an1 F Q).eval (embed (b i))=embed (F.derivative.eval (b i))*_
    dsimp only [an1]
    simp only [derivative_map,eval_add,eval_sub,eval_mul,eval_C,eval_X,
      eval_map_apply,hq,map_neg,map_mul,lineRoot]
    simp only [embed,RingHom.comp_apply,map_add,map_mul]
    ring
  have hnum :mapTwice e (numerator f g)=(F.map ι).resultant B g g:= by
    rw [numerator,← resultant_map_map,cutter_map,map_embed]
  have hdet:e (det f g)=a^(g - 1) * ∏ i,F.derivative.eval (b i) := by
    rw [det,← resultant_map_map,← derivative_map]
    exact res_split F.derivative hb hd
  change mapTwice e (numerator f g)=ι (e (denominator f g))*tiltedProd D b
  rw [hnum,res_split B hb' hB,denominator,map_mul,hdet]
  simp only [ht,Finset.prod_mul_distrib,map_mul,map_pow,map_prod,tiltedProd]
  change _=ι a*(ι a^(g - 1)*_)*_
  rw [← mul_assoc (ι a),← pow_succ',zxt hg,mul_assoc]
end
end P5_7_3_3_4_1_7_2_2
end
section
set_option autoImplicit true
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_7_2_2
noncomputable section
open Polynomial P5_7_3_3_4_1_7 P5_7_3_3_4_1_7_2
open q1kuFjb (mapTwice)
private theorem centre (f :LocalEquation) {g d j:ℕ} (h:LocalGuard f g d j)
    (n:ℕ) (hn:n≠0) (b:Fin g→R) (D:aQ →+ aQ)
    (hb:SplitAt f g n hn b) :
    CentreShape (mapTwice zbO (tiltedProd D b)) j
      (jz (physicalCentre (f.coeff g))) (jz (physicalCentre (f.coeff j))) := by
  classical
  let e :=ramify jz n hn
  let u (i:Fin g) :=zbO (b i)
  let a :=jz (physicalCentre (f.coeff g))
  let L (i:Fin g) :aQ[X][X] :=z7y - C (lineRoot (u i) (D (u i)))
  let P := ∏ i,L i
  have hm:mapTwice zbO (tiltedProd D b)=P:= by
    simp [mapTwice,tiltedProd,P,L,lineRoot,u,
      ← PowerSeries.coeff_zero_eq_constantCoeff]
  have hmap : (f.map e).map zbO =
      C a*P.map (Polynomial.constantCoeff :aQ[X] →+* aQ) := by
    change f.map e=C (e (f.coeff g)) * ∏ i,(z7y - C (b i)) at hb
    rw [hb]
    simp [P,L,lineRoot,a,u,e,zeg]
  have ha (i:ℕ) :a*(P.coeff i).eval 0=jz (physicalCentre (f.coeff i)) := by
    have hi:=congrArg (fun G:aQ[X]=>G.coeff i) hmap
    simpa only [coeff_map,coeff_C_mul,constantCoeff_apply,coeff_zero_eq_eval_zero,e,centre_ramify] using hi.symm
  let S:=Finset.univ.filter (fun i:Fin g=>u i=0)
  let U:=Finset.univ.filter (fun i:Fin g=>u i≠0)
  let Q := ∏ i∈U,L i
  have hp:P=z7y ^S.card*Q:= by
    have hz (i:Fin g) (hi:i∈S) :L i=Polynomial.X:= by
      have h0:=(Finset.mem_filter.mp hi).2
      simp [L,lineRoot,h0]
    calc
      P=(∏ i∈S,L i)*Q:=(Finset.prod_filter_mul_prod_filter_not
        Finset.univ (fun i=>u i=0) L).symm
      _ = _:= by rw [Finset.prod_congr rfl hz,Finset.prod_const]
  have hl (i:ℕ) (hi:i<S.card) :P.coeff i=0 :=
    Polynomial.X_pow_dvd_iff.mp ⟨Q,hp⟩ i hi
  have hnz : (P.coeff S.card).eval 0≠0:= by
    have hc:=coeff_X_pow_mul Q S.card 0
    simp only [Nat.zero_add] at hc
    rw [hp,hc]
    change ((∏ i∈U,L i).coeff 0).eval 0≠0
    rw [coeff_zero_prod]
    simp only [eval_prod,L,coeff_sub,coeff_X_zero,coeff_C_zero,zero_sub,
      eval_neg,lineRoot,eval_add,eval_C,eval_mul,eval_X,zero_mul,add_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i hi=>neg_ne_zero.mpr (Finset.mem_filter.mp hi).2
  have ha0:a≠0:=(h.2.1.map (jz.comp physicalCentre)).ne_zero
  have hj:S.card=j:= by
    apply le_antisymm
    · by_contra! hc
      have hh:=ha j
      rw [hl _ hc,eval_zero,mul_zero] at hh
      exact (h.2.2.2.2.map jz).ne_zero hh.symm
    · by_contra! hc
      exact (mul_ne_zero ha0 hnz) (by rw [ha,h.2.2.2.1 _ hc,map_zero])
  rw [hm]
  exact ⟨fun i hi=>hl i (hj.symm ▸ hi),ha j⟩
theorem proof :P5_7_3_3_4_1_7_2.c2 := by
  intro f g d j hg h n hn b D hb hD
  change mapTwice (ramify jz n hn) (numerator f g) =
    embed (ramify jz n hn (denominator f g))*tiltedProd D b ∧
    (tiltedProd D b).Monic∧CentreShape (mapTwice zbO (tiltedProd D b)) j
      (jz (physicalCentre (f.coeff g))) (jz (physicalCentre (f.coeff j)))
  exact ⟨factorization f (by omega) h.1 n hn b D hb hD,
    monic_prod_X_sub_C _ _,centre f h n hn b D hb⟩
end
end P5_7_3_3_4_1_7_2_2
end
