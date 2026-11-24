import ProximityPrize.SubmissionLower.ZQTNHBe
import ProximityPrize.SubmissionLower.Z3swOYa
import ProximityPrize.SubmissionLower.Z4EMMWa
import ProximityPrize.SubmissionLower.ZVbskte
import ProximityPrize.SubmissionLower.ZGcgEBb
import ProximityPrize.SubmissionLower.ZxMkGTa
import ProximityPrize.SubmissionLower.Zmk5EEe
import ProximityPrize.SubmissionLower.ZULJdud
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZGggfqb
import ProximityPrize.SubmissionLower.ZnTmQ9b
set_option Elab.async false
open _root_ renaming Algebra → zZE, CommRing → za6, Function.Surjective → zpX, Ideal.Quotient.factor_surjective → zuo, Ideal.Quotient.factorₐ → z5F, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, Ideal.pow_le_pow_right → zdr, Ideal.pow_mem_pow → z2s, Ideal.span → zye, LinearIndependent → z14, Module.Finite → zAa, Module.Finite.of_surjective → zIU, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.map → zDK, Polynomial.X → z7y, Polynomial.mapRingHom → zhd, RingHom.comp_apply → zQb
set_option maxHeartbeats 800000
section
section
set_option autoImplicit true
namespace qB4SPFa
theorem proof :qb1WXKc.c1 :=
 qPfoxUd.proof
end qB4SPFa
end
section
namespace qxDtRld
noncomputable section
open Polynomial Finset q82zwcd
open P5 (K I)
open cu (L)
open Cu (sQ)
open E7 (CurvePlace axV poleOrder KB)
open qb0hmCe (cLN)
open qFD8jve (sheetPole aaD polarResultant)
open scoped Classical WithZero
local notation "siteGuard" => qFD8jve.guard
variable {E :Type} [Field E]
theorem guard_scaled {a :E} (ha :a≠0) {G:E[X][X]} (hd:0<G.natDegree) :
   siteGuard (nY a G)=a^(2*G.natDegree)*siteGuard G:= by
 have hd' : (nY a G).natDegree=G.natDegree :=natDegree_C_mul (C_ne_zero.mpr ha)
 have hr :polarResultant (nY a G) =
     C (a^(G.natDegree-1+G.natDegree))*polarResultant G:= by
   unfold polarResultant
   rw [hd',derivative_C_mul,resultant_C_mul_left,resultant_C_mul_right,← mul_assoc,
     ← pow_add,← map_pow]
 have hc:aaD (nY a G)=C a*aaD G:= by
   simp only [aaD,nY,Polynomial.map_mul,Polynomial.map_C,coe_evalRingHom,eval_C]
 unfold qFD8jve.guard
 rw [hr,hc,trailingCoeff_mul,trailingCoeff_mul]
 simp only [trailingCoeff,natTrailingDegree_C,coeff_C_zero]
 rw [mul_mul_mul_comm,← pow_succ,show G.natDegree-1+G.natDegree+1=2*G.natDegree by omega]
theorem log_unscale (v :Valuation E ℤᵐ⁰) {a g:E} {m B:ℕ}
  (ha :a≠0) (hg:g≠0) (haB : -(B:ℤ)≤WithZero.log (v a))
  (h:v (a^m*g)<1) :WithZero.log (v g)<((m*B:ℕ) :ℤ) := by
 have hv :=v.ne_zero_iff.mpr ha
 have hw:=v.ne_zero_iff.mpr hg
 have hh:=(WithZero.log_lt_log (v.ne_zero_iff.mpr (mul_ne_zero (pow_ne_zero _ ha) hg))
  (by simp : (1 :ℤᵐ⁰)≠0)).mpr h
 rw [map_mul,map_pow,WithZero.log_mul (pow_ne_zero _ hv) hw,WithZero.log_pow,
  nsmul_eq_mul,WithZero.log_one] at hh
 have hb:=mul_le_mul_of_nonneg_left haB (Int.natCast_nonneg m)
 rw [Int.mul_neg] at hb
 rw [Nat.cast_mul]
 linarith only [hb,hh]
theorem scale_log {D:ℕ} {w:I→K} {U:Finset K} {s :K→K[X]}
   {z :K→K} {q:sQ} {J:WordChart D w U s} (F:DualSheet J q z)
   {γ:K} (hγ:γ∈U) :
   -(sheetPole (F.place γ).value F.f :ℤ) ≤
     WithZero.log ((F.place γ).value (F.scale γ:F.curve.E)) := by
 let a :=F.atPlace γ hγ
 let u:F.curve.E :=F.scale γ
 let v :=(F.place γ).value
 let r :=cLN a 0 (nY u F.f)
 have hex : ∃ i j,(r.coeff i).coeff j≠0:= by
   by_contra! h
   apply F.reduction_ne γ hγ
   apply Polynomial.ext
   intro i
   apply Polynomial.ext
   intro j
   simpa only [coeff_zero] using h i j
 obtain ⟨i,j,hh⟩:=hex
 let c:=(F.f.coeff i).coeff j
 change ((cLN a 0 (nY u F.f)).coeff i).coeff j≠0 at hh
 rw [q1kuFjb.expansion_coeff,coeff_C_mul,coeff_C_mul] at hh
 change (a (u*c)).coeff 0≠0 at hh
 have hin:v (u*c)≤1 :=F.integral γ hγ i j
 have he :v (u*c)=1 := by
   by_contra! hn
   have hlt:=lt_of_le_of_ne hin hn
   rw [F.value γ hγ] at hlt
   have hne : (a (u*c))≠0:= fun hz=>hh (by simp [hz])
   have hnz :=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰).ne_zero_iff.mpr hne
   have hlog:=(WithZero.log_lt_log hnz (by simp : (1 :ℤᵐ⁰)≠0)).mpr hlt
   rw [WithZero.log_one] at hlog
   exact hh ((LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero L hnz).mp le_rfl 0 (by omega))
 have huc:v (u*c)≠0:= by simp [he]
 have hu:=(v.ne_zero_iff.mpr (Units.ne_zero (F.scale γ)) :v u≠0)
 have hc:v c≠0:= fun hz=>huc (by rw [map_mul,hz,mul_zero])
 have hb:=(WithZero.log_le_iff_le_exp hc).mpr (qrezXJe.sheet_bound v F.f i j)
 rw [map_mul,← WithZero.exp_log hu,← WithZero.exp_log hc,← WithZero.exp_add,
   WithZero.exp_eq_one] at he
 change -(sheetPole v F.f :ℤ)≤WithZero.log (v u)
 omega
theorem divisor_count [zZE L E] (hdiv :axV L E)
   (T:Finset K) (place :K→CurvePlace L E) (hinj:Set.InjOn place (T:Set K))
   {g:E} (B:CurvePlace L E→ℕ) (hB:B.HasFiniteSupport)
   (hb : ∀ v,WithZero.log (v.value g)≤(B v :ℤ))
   (ht : ∀ γ∈T,WithZero.log ((place γ).value g)<(B (place γ) :ℤ)) :
   T.card ≤ ∑ᶠ v,B v := by
 obtain ⟨hp,hz,he,_⟩:=hdiv g
 let A (v :CurvePlace L E) :ℕ:=if v∈T.image place then 1 else 0
 have hAsub:Function.support A ⊆ ↑(T.image place) := by
   intro v hv
   by_contra hn
   exact hv (ite_eq_right hn)
 have hA:A.HasFiniteSupport:=(T.image place).finite_toSet.subset hAsub
 have hcard: (∑ᶠ v,A v)=T.card:= by
   rw [finsum_eq_finsetSum_of_support_subset _ hAsub,← card_image_of_injOn hinj]
   calc
     _ = ∑ _∈T.image place,(1 :ℕ) :=sum_congr rfl (fun _ hv=>ite_eq_left hv)
     _ = _:= by simp
 have hlocal (v :CurvePlace L E) :poleOrder v.value g+A v≤B v+KB v.value g:= by
   have hh:=hb v
   unfold A poleOrder KB
   split
   · obtain ⟨γ,hγ,rfl⟩:=mem_image.mp ‹v∈T.image place›
     have h:=ht γ hγ
     omega
   · omega
 have h:=finsum_le_finsum (hp.add hA) (hB.add hz) hlocal
 change (∑ᶠ v :CurvePlace L E,(poleOrder v.value g+A v)) ≤
   (∑ᶠ v :CurvePlace L E,(B v+KB v.value g)) at h
 rw [finsum_add_distrib hp hA,finsum_add_distrib hB hz,hcard,← he] at h
 omega
end
end qxDtRld
end
section
namespace qG0wqGe
def c1 :Prop :=qoCymac.c2
def c2 :Prop :=qoCymac.c4
def c3:Prop :=qoCymac.c6
theorem of_children (specialize :c1) (normalize :c2) (valuation :c3) :
  qJOpoVa.c3 :=
 qoCymac.of_children q5eiIAb.proof specialize
  qvOlzpd.proof normalize qpI7nyd.proof valuation
end qG0wqGe
end
section
namespace q2tSkEc
noncomputable section
open Polynomial qNu3xvc
open P5_7_1_7_4_3_4 (Pencil)
open qfbIfsd
open cu (L)
abbrev caps (b s :ℕ) :Fin 3→ℕ := ![b,b+s+1,b]
abbrev orders (d:ℕ) :Fin 3→ℕ := ![d,d,d-1]
abbrev bzm (s b d:ℕ) :=Vars s (caps b s) (orders d)
def top {M:Type} [CommSemiring M] {s b d:ℕ}
    (a :bzm s b d→M) (t:Fin 3) (x :M) :M :=
  ∑ i:Slot s (caps b s t) (orders d t),
    if i.1.val=orders d t then a ⟨t,i⟩*x^i.2.val else 0
def L4 {M:Type} [za6 M] {s b d:ℕ}
    (a :bzm s b d→M) (x y :M) :M :=
  form a 2 x y+((d:M)*top a 0 x - top a 2 x)*y ^(d-1)
def DetectsValue {s b d:ℕ} (R:z3y (bzm s b d) L) :Prop :=
  ∀ {M:Type} [Field M] (m:L →+* M) (a :bzm s b d→M) (x y :M),
    form a 0 x y=0→form a 1 x y=0→L4 a x y=0→R.eval₂ m a=0
variable {E :Type} [Field E] [zZE L E] {A:Equation E}
theorem actual_top (C:Pencil A) (hd:2≤A.d) (j:Fin (A.b+1)) :
  actual C ⟨2,⟨⟨A.d-1,Nat.lt_succ_self _⟩,⟨j,by simpa using j.isLt⟩⟩⟩ =
   const₂ (A.d:E)*actual C ⟨0,⟨⟨A.d,Nat.lt_succ_self _⟩,⟨j,by simpa using j.isLt⟩⟩⟩:= by
 have hg: (gaugeForm C.tilt A.d).coeff (A.d-1)=0:= by
  apply coeff_eq_zero_of_natDegree_lt
  have h: (1+Polynomial.C C.tilt*z7y).natDegree≤1 :=
   (natDegree_add_le _ _).trans (by simpa using natDegree_C_mul_le C.tilt z7y)
  exact (natDegree_pow_le_of_le (A.d-2) h).trans_lt (by omega)
 have he :A.d-1+1=A.d:= by omega
 have hc: (A.f.derivative.coeff (A.d-1)).coeff j=(A.f.coeff A.d).coeff j*(A.d:E) := by
  rw [coeff_derivative,← Nat.cast_succ,← C_eq_natCast,coeff_mul_C,Nat.succ_eq_add_one,he]
 change const₂ ((A.f.derivative.coeff (A.d-1)).coeff j) -
  const₂ (algebraMap L E (if j.val=0 then (gaugeForm C.tilt A.d).coeff (A.d-1) else 0)) *
   z7y=const₂ (A.d:E)*const₂ ((A.f.coeff A.d).coeff j)
 simp only [hg,ite_self,map_zero,zero_mul,sub_zero,hc,map_mul,mul_comm]
end
end q2tSkEc
end
section
set_option backward.isDefEq.respectTransparency false
namespace q2tSkEc
noncomputable section
open Polynomial qNu3xvc

open P5_7_1_7_4_3_4 (Pencil elimDegree relativePolar bix)
open qfbIfsd
open qJOpoVa (relativeRate)
open cu (L)
open scoped WithZero
open private actual_le deform_le coeff_le_gauss₃ strip from ProximityPrize.SubmissionLower.ZxMkGTa
open private coeff_le_gauss₂ from ProximityPrize.SubmissionLower.ZhEC96c
def c1 :Prop :=
  ∀ (s b d:ℕ),2≤d →
    ∃ R:z3y (bzm s b d) L,R≠0 ∧
      R.totalDegree≤kK s (caps b s) (orders d)-(2*b+s+1)∧DetectsValue R
def c2 :Prop :=
  ∀ {E :Type} [Field E] [zZE L E] (A:Equation E),2≤A.d → ∀ C:Pencil A,
    C.tilt≠0 → ∀ R:z3y (Index A) L,R≠0→DetectsValue R →
    ∃ (z :Index A→L) (n:ℕ),
      let P:=(deform R (actual C) z).coeff n
      P≠0∧bix C.base (relativePolar C) C.finite ∣
        P.map (algebraMap E[X] (RatFunc E))
private theorem rate {E :Type} [Field E] [zZE L E] (A:Equation E) (hd:2≤A.d) :
  elimDegree A=polarRate A:= by
 have h1:1≤A.d:= by omega
 have h2:2≤6*A.d:= by omega
 have h3:1≤3*A.d*A.d:=Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)
 have h4:1≤2*A.d:= by omega
 unfold elimDegree P5_7_1_7_4_3_4.pairDegree polarRate
 zify [h1,h2,h3,h4]
 ring
private theorem degree_eq {E :Type} [Field E] [zZE L E] (A:Equation E) (hd:2≤A.d) :
   kK A.s (caps A.b A.s) (orders A.d)-(2*A.b+A.s+1)=relativeRate A:= by
 have h₁:4≤6*A.d:= by omega
 have h₂:2≤3*A.d*A.d:= by
   simpa only [one_mul] using Nat.mul_le_mul (show 1≤3*A.d by omega) hd
 have h₃:2≤2*A.d:= by omega
 have he :relativeRate A+(2*A.b+A.s+1)=polarRate A:= by
   unfold relativeRate polarRate
   zify [h₁,h₂,h₃,show 2≤6*A.d by omega,show 1≤3*A.d*A.d by omega,
     show 1≤2*A.d by omega]
   ring
 change elimDegree A-(2*A.b+A.s+1)=relativeRate A
 rw [rate A hd,← he,Nat.add_sub_cancel]
theorem of_children (detector :c1) (specialize :c2) :qJOpoVa.c5:= by
 intro E _ _ A hd C htilt
 obtain ⟨R,hR,hdR,hdetect⟩:=detector A.s A.b A.d hd
 rw [degree_eq A hd] at hdR
 obtain ⟨z,n,hP,hdvd⟩:=specialize A hd C htilt R hR hdetect
 obtain ⟨Q,hQ,hQdvd,hcoeff⟩:=strip C _ hP hdvd
 refine ⟨Q,hQ,hQdvd,fun w i j => ?_⟩
 rw [hcoeff]
 let P:=deform R (actual C) z
 change w.value (((P.coeff n).coeff (i+(P.coeff n).natTrailingDegree)).coeff j)≤_
 exact ((coeff_le_gauss₂ w.value (P.coeff n) _ j).trans
   (coeff_le_gauss₃ w.value P n)).trans
     (deform_le R w (actual C) z _ _ (actual_le C w) hdR)
end
end q2tSkEc
end
end
section
section
set_option synthInstance.maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency false
namespace q6CrDDe
noncomputable section
open Polynomial Finset
open P5 (K)
open cu (L FX)
open gT (kM)
open Cu
open qBajpRb
private theorem power_length {B:Type} [za6 B] [IsDomain B] [IsNoetherianRing B]
    [zZE L B] (m:Ideal B) (hm:m ≠ ⊥) (ht:m ≠ ⊤)
    [zAa L (B ⧸ m)] (q:ℕ) (hq:0<q) :
    zAa L (B ⧸ m^q)∧q≤zsE L (B ⧸ m^q) := by
  have hle :m^q≤ m:=Ideal.pow_le_self hq.ne'
  let f :=z5F L hle
  let:zAa L (B ⧸ m^q) := by
    refine Module.finite_of_surjective_of_ker_le_nilradical f
      (zuo hle) ?_ (IsNoetherian.noetherian _)
    intro x hx
    obtain ⟨a,rfl⟩:=zld x
    have ha :a∈m:=Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp hx)
    exact mem_nilradical.mpr ⟨q,by
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (z2s ha q)⟩
  refine ⟨inferInstance,?_⟩
  have hstrict (n:ℕ) :m^(n+1)< m^n:= by
    refine lt_of_le_of_ne (zdr (Nat.le_succ _)) ?_
    intro he
    have hi:m^n≤ m•m^n:= by
      rw [Ideal.smul_eq_mul,← pow_succ',he]
    obtain ⟨a,ha,hz⟩:=Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
      (m^n) (IsNoetherian.noetherian _) hi
    have ha0:a≠0:= by
      intro e
      apply ht
      apply Ideal.eq_top_of_isUnit_mem m _ (isUnit_one.neg)
      simpa [e] using ha
    obtain ⟨x,hx,hx0⟩:=Submodule.exists_mem_ne_zero_of_ne_bot hm
    exact (pow_ne_zero n hx0) ((mul_eq_zero.mp (hz (x^n) (z2s hx n))).resolve_left ha0)
  have hl (n:ℕ) (hn:n≤q) :n≤zsE L (B ⧸ m^n) := by
    let hdown:m^q≤ m^n:=zdr hn
    let:zAa L (B ⧸ m^n) :=zIU
      (z5F L hdown).toLinearMap (zuo hdown)
    induction n with
    | zero=>exact Nat.zero_le _
    | succ n ih =>
      let le :m^(n+1)≤ m^n:=(hstrict n).le
      let π:=(z5F L le).toLinearMap
      have hsur :zpX π:=zuo le
      obtain ⟨a,ha,ha'⟩:=SetLike.exists_of_lt (hstrict n)
      have hnz :LinearMap.ker π ≠ ⊥ := by
        intro he
        have hz :zVv _ a=0 :=
          show zVv _ a∈(⊥ : Submodule L (B ⧸ m^(n+1))) from
            he ▸ (LinearMap.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr ha))
        exact ha' (Ideal.Quotient.eq_zero_iff_mem.mp hz)
      have hdim:=π.finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr hsur,finrank_top] at hdim
      have hp:=Submodule.one_le_finrank_iff.mpr hnz
      have hi:=ih ((Nat.le_succ _).trans hn)
      omega
  exact hl q le_rfl
theorem marks_length
    {C₀:sQ} [hC:Fact (Irreducible C₀)] {J:Ideal kM}
    {g n:ℕ} {R:wJ C₀ J g} (A:yI R n)
    (T:Finset K) (z :K→K) (t:K→Fin n→L)
    (hT : ∀ γ∈T,aCn (z γ) (t γ)∈MvPolynomial.zeroLocus FX (EF A))
    (hz :Set.InjOn z (T:Set K)) (q:ℕ) (hq:0<q) :
    zAa L (CurveRing A ⧸ thickMarks A T z t hT q) ∧
    q*T.card≤zsE L (CurveRing A ⧸ thickMarks A T z t hT q) := by
  classical
  let B:=CurveRing A
  let φ (γ : ↥T) :=yq A (z γ) (t γ) (hT γ γ.property)
  let m (γ : ↥T) :=RingHom.ker (φ γ).toRingHom
  let mQ (γ : ↥T) :=m γ^q
  have hs (γ : ↥T) :zpX (φ γ) :=
    fun x=>⟨algebraMap L B x,(φ γ).commutes x⟩
  have hmax (γ : ↥T) : (m γ).IsMaximal:=RingHom.ker_isMaximal_of_surjective _ (hs γ)
  have hker (γ : ↥T) :m γ ≠ ⊥ := by
    intro h
    let f :=(φ γ).toLinearMap.comp (u7 A C₀.totalDegree).subtype
    have hi:Function.Injective (φ γ) :=(RingHom.injective_iff_ker_eq_bot _).mpr h
    have hb:=LinearMap.finrank_le_finrank_of_injective (f :=f) (hi.comp Subtype.val_injective)
    rw [Module.finrank_self] at hb
    have hd:=aqd.ddg C₀ hC.out
    have hdQ: (0:ℚ)<C₀.totalDegree := by exact_mod_cast hd
    have hr :=lower_rank A (k :=C₀.totalDegree) rfl hd
    have hbQ: (zsE L (u7 A C₀.totalDegree) :ℚ)≤1 := by
      exact_mod_cast hb
    nlinarith only [hr,hbQ,hdQ,mul_pos hdQ hdQ]
  have hloc (γ : ↥T) :zAa L (B ⧸ mQ γ)∧q≤zsE L (B ⧸ mQ γ) := by
    let e :=Ideal.quotientKerAlgEquivOfSurjective (hs γ)
    let:zAa L (B ⧸ m γ) :=zIU e.symm.toLinearMap e.symm.surjective
    exact power_length (m γ) (hker γ) (hmax γ).ne_top q hq
  have hcop:Pairwise (fun γ δ=>IsCoprime (mQ γ) (mQ δ)) := by
    intro γ δ hne
    apply IsCoprime.pow
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply (hmax γ).coprime_of_ne (hmax δ)
    intro he
    let x :=cls A (MvPolynomial.X (Sum.inl 0))
    let a :=algebraMap L B ((φ γ) x)
    have ha :x-a∈m δ:= by
      rw [← he]
      exact RingHom.mem_ker.mpr (by
        change (φ γ) (x-a)=0
        rw [map_sub,show (φ γ) a=(φ γ) x from (φ γ).commutes _,sub_self])
    have hv : (φ δ) x=(φ γ) x := by
      have h:=RingHom.mem_ker.mp ha
      change (φ δ) (x-a)=0 at h
      rw [map_sub,sub_eq_zero] at h
      exact h.trans ((φ δ).commutes _)
    have ht (i : ↥T) : (φ i) x=algebraMap K L (z i) := by
      change yq A (z i) (t i) (hT i i.property) (cls A (MvPolynomial.X (Sum.inl 0)))= _
      rw [atMark_cls,MvPolynomial.eval_X]
      rfl
    rw [ht,ht] at hv
    exact hne (Subtype.ext (hz γ.property δ.property ((algebraMap K L).injective hv.symm)))
  let e :=Ideal.quotientInfRingEquivPiQuotient mQ hcop
  let eL: (B ⧸ thickMarks A T z t hT q) ≃ₐ[L] (∀ γ : ↥T,B ⧸ mQ γ) :=
    { e with commutes' := fun _=>rfl }
  let (γ : ↥T) :zAa L (B ⧸ mQ γ) :=(hloc γ).1
  let (γ : ↥T) :Module.Free L (B ⧸ mQ γ) :=Module.Free.of_divisionRing L _
  have hlen:=Finset.sum_le_sum (s :=Finset.univ) (fun γ _=>(hloc γ).2)
  refine ⟨zIU eL.symm.toLinearMap eL.symm.surjective,?_⟩
  rw [eL.toLinearEquiv.finrank_eq,Module.finrank_pi_fintype]
  simpa [Nat.mul_comm] using hlen
end
end q6CrDDe
end
section
set_option backward.isDefEq.respectTransparency false
namespace q6CrDDe
noncomputable section
open Polynomial

open cu (L)
open gT (kM)
open Cu
open quN7Z4a (compressionWidth)
open qBajpRb
def c1 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (J:Ideal kM)
    (g n H :ℕ) (R:wJ C₀ J g) (A:yI R n),
    a9K (EF A) H → ∀ (j:ℕ) (f :CurveRing A),f∈tuple A j→f≠0 →
    zAa L (CurveRing A ⧸ zye {f}) ∧
    zsE L (CurveRing A ⧸ zye {f})≤j*H
def c2 :Prop :=
  ∀ (B:Type) [za6 B] [IsDomain B] [zZE L B]
    (V W:Submodule L B) [zAa L V] [zAa L W]
    (D:ℕ) (F:B[X][X]),
    0<D→F≠0→F.natDegree≤2 →
    (∀ i a,(F.coeff i).coeff a∈W) →
    zsE L (V*W)<4*zsE L V →
    ∃ G:B[X][X],G≠0∧G.natDegree≤2 ∧
      (∀ i a,(G.coeff i).coeff a∈V*W) ∧
      (∀ i a,(G.coeff i).coeff a≠0→a+i*D <compressionWidth D 2) ∧
      ∀ (Q:Type) [za6 Q] (φ:B →+* Q) (u:Q[X]),u.natDegree≤D →
        (F.map (zhd φ)).eval u=0 →
        (G.map (zhd φ)).eval u=0
end
end q6CrDDe
end
section
set_option backward.isDefEq.respectTransparency false
namespace q978Lma
noncomputable section
open cu (L FX)
open gT (kM)
open Cu
open akS (tu)
open qBajpRb (CurveRing incl incl_injective ek)
open private constant_base from ProximityPrize.SubmissionLower.ZJbAGBd
variable {C₀:sQ} [Fact (Irreducible C₀)] {J:Ideal kM}
 {g n:ℕ} {R:wJ C₀ J g} (A:yI R n)
def intoBase :CurveRing A →ₐ[L] tu (EF A) :=
  Ideal.quotientMapₐ _ (MvPolynomial.mapAlgHom (Algebra.ofId L FX)) (by
    intro q hq
    change ((W8 A).comp (zDK (algebraMap L FX))) q=0
    rw [constant_base,zQb,RingHom.mem_ker.mp hq,map_zero])
private def baseIncl:tu (EF A) →+* y7 C₀ :=
 RingHom.kerLift (W8 A)
private theorem baseIncl_intoBase (v :CurveRing A) :
  baseIncl A (intoBase A v)=Mu C₀ (incl A v) := by
 obtain ⟨q,rfl⟩:=zld v
 exact DFunLike.congr_fun (constant_base A) q
private theorem baseIncl_scalar (c:FX) :
  baseIncl A (algebraMap FX (tu (EF A)) c)=Mr C₀ c:= by
 change W8 A (MvPolynomial.C c)= _
 exact zTv _ _ c
private theorem incl_scalar (c:L) :
  incl A (algebraMap L (CurveRing A) c)=zT C₀ c:= by
 change ek A (MvPolynomial.C c)= _
 exact zTv _ _ c
private theorem map_sum_smul {F B Q ι:Type} [za6 F] [za6 B] [za6 Q]
  [zZE F B] [Fintype ι] (u:B →+* Q) (c:ι→F) (v :ι→B) :
  u (∑ t,c t•v t) = ∑ t,u (algebraMap F B (c t))*u (v t) := by
 simp only [Algebra.smul_def,map_sum,map_mul]
theorem independent_intoBase {ι:Type} [Fintype ι] {v :ι→CurveRing A}
  (hv :z14 L v) :
  z14 FX (fun i=>intoBase A (v i)) := by
 classical
 refine Fintype.linearIndependent_iff.mpr fun c hc => ?_
 have hq:=congrArg (baseIncl A) hc
 rw [map_sum_smul (baseIncl A) c (fun i=>intoBase A (v i)),map_zero] at hq
 simp only [baseIncl_scalar,baseIncl_intoBase,Mu,zQb,F5] at hq
 exact qISdf9a.clear_abscissa_relation
  (zT C₀) (incl A) (incl_injective A) (incl_scalar A) v hv c hq
end
end q978Lma
end
section
set_option backward.isDefEq.respectTransparency false
namespace q978Lma
noncomputable section
open cu (L FX)

open Cu
open akS
open scoped akS
open qBajpRb (CurveRing cls)
open MvPolynomial
open private qISdf9a.bHQ from ProximityPrize.SubmissionLower.Z6B1Brd
open private growth_count from ProximityPrize.SubmissionLower.ZGggfqb
private theorem bHQ {F B:Type} [Field F] [za6 B] [zZE F B]
  [IsDomain B] {r :ℕ} {w:Fin r→B} {f :B} (hf :f≠0)
  (hw:z14 F (fun i=>zVv (zye {f}) (w i)))
  (k :ℕ) :
  z14 F (fun ij:Fin (k+1)×Fin r=>f^(ij.1 :ℕ)*w ij.2) := by
 let π:=Ideal.Quotient.mkₐ F (zye {f})
 have hπ:π f=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
 exact qISdf9a.bHQ π.toLinearMap w f hf
  (fun x=> by change π (f*x)=0; rw [map_mul,hπ,zero_mul]) hw k
private theorem bound_powers {n H j r :ℕ} (B:Ideal (Gc n))
  (hB:B.IsPrime) (hH :a9K B H)
  (q:N4 n) (hq:q.totalDegree≤j) (w:Fin r→tu B)
  (hw : ∀ k :ℕ,z14 FX (fun ij:Fin (k+1)×Fin r =>
    (zVv B (aa4 n q))^(ij.1 :ℕ)*w ij.2)) :
  r≤j*H := by
 exact (by simpa using growth_count B hB hH q w hw:r≤q.totalDegree*H).trans
  (Nat.mul_le_mul_right H hq)
theorem proof :q6CrDDe.c1 := by
 classical
 intro C₀ hC J g n H R A hH j f hf hf0
 obtain ⟨q,hq,hqf⟩:=Submodule.mem_map.mp hf
 have hqf' : cls A (rename Sum.inr q)=f :=hqf
 let B:=EF A
 let q' := zDK (algebraMap L FX) q
 have hf' : intoBase A f=zVv B (aa4 n q') := by
   rw [← hqf']
   change zVv B (zDK (algebraMap L FX) (rename Sum.inr q))= _
   rw [map_rename]
   rfl
 have hq' : q'.totalDegree≤j:= by
   have h:q'.totalDegree≤q.totalDegree :=Finset.sup_mono (support_map_subset _ _)
   exact h.trans ((mem_restrictTotalDegree _ _ _).mp hq)
 let Q:=CurveRing A ⧸ zye {f}
 have bound {r :ℕ} (v :Fin r→Q) (hv :z14 L v) :r≤j*H := by
   choose w hw using fun i=>zld (v i)
   have hpow:=bHQ (w:=w) hf0 (by simpa only [hw] using hv)
   apply bound_powers B (RingHom.ker_isPrime _) hH q' hq' (fun i=>intoBase A (w i))
   intro k
   simpa only [map_mul,map_pow,hf'] using independent_intoBase A (hpow k)
 have hrank :Module.rank L Q≤(j*H :ℕ) := by
   by_contra! h
   obtain ⟨v,hv⟩:=exists_linearIndependent_of_le_rank (R:=L) (M:= Q)
     (n:=j*H+1) (by exact_mod_cast (Cardinal.add_one_le_of_lt h))
   exact Nat.not_succ_le_self _ (bound v hv)
 exact ⟨Module.rank_lt_aleph0_iff.mp (hrank.trans_lt Cardinal.natCast_lt_aleph0),
   by simpa [zsE] using Cardinal.toNat_le_toNat hrank Cardinal.natCast_lt_aleph0⟩
end
end q978Lma
end
end
