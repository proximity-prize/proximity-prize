import ProximityPrize.SubmissionLower.V
import ProximityPrize.SubmissionLower.CC
import ProximityPrize.SubmissionLower.Z3EWiUc
import ProximityPrize.SubmissionLower.ZFFuWqa
import ProximityPrize.SubmissionLower.ZGlW6Oc
import ProximityPrize.SubmissionLower.ZgdIx1d
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.EssFiniteType → zl5, Algebra.EssFiniteType.comp → zQi, Algebra.EssFiniteType.of_comp → z9q, Algebra.EssFiniteType.of_isLocalization → zrU, Algebra.FiniteType → zUK, Algebra.FiniteType.quotient → zrZ, Algebra.IsAlgebraic → zjH, Algebra.IsAlgebraic.isAlgebraic → zgs, Algebra.IsIntegral → zVK, Algebra.TensorProduct.includeRight → zgi, Algebra.Transcendental → za8, Algebra.adjoin → zum, Algebra.algebraMapSubmonoid → zTz, Algebra.finite_of_essFiniteType_of_isAlgebraic → zNf, Algebra.trdeg → zls, CommRing → za6, Field → zrb, Finset.le_sup → zZi, Finset.sup'_eq_sup → zWa, Finset.sup_le → zf9, Function.Injective → zq4, Function.Surjective → zpX, Ideal → znc, Ideal.IsPrime.comap → zCL, Ideal.Quotient.lift → zP2, Ideal.Quotient.lift_mk → z0R, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_algebraMap → zOY, Ideal.Quotient.mk_surjective → zld, Ideal.Quotient.mkₐ → zvR, Ideal.map_le_iff_le_comap → zo0, Ideal.map_map → z0L, Ideal.map_span → zlN, Ideal.mem_map_of_mem → z7X, Ideal.mem_span_singleton_self → z5J, Ideal.quotientEquivAlgOfEq → z9k, Ideal.span → zye, Ideal.span_singleton_le_iff_mem → zvl, Ideal.subset_span → zCn, Int.toNat_le_toNat → z0Z, IsDomain → ztn, IsFractionRing → z0o, IsFractionRing.injective → zxb, IsFractionRing.lift → zIj, IsFractionRing.lift_algebraMap → zoc, IsLocalization → zNo, IsLocalization.isAlgebraic → zyQ
open _root_ renaming IsScalarTower → zsf, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.of_algebraMap_eq → zsL, IsScalarTower.toAlgHom → zE2, LinearIndependent → z14, Module.Finite → zAa, Module.IsTorsionFree → zYo, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, MvPolynomial.eval₂ → zSZ, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.map → zDK, MvPolynomial.map_C → zpw, MvPolynomial.map_X → z7N, MvPolynomial.ringHom_ext → zXT, Nat.add_le_add → z9f, Nat.add_le_add_right → zlr, Nat.eq_zero_of_le_zero → za7, Nat.le_add_right → z8K, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.sub_le_sub_right → zIu, Nat.zero_le → zD0, Polynomial → zM1, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.aeval → zEU, Polynomial.aeval_C → z8q, Polynomial.aeval_X → zw0, Polynomial.algEquivOfTranscendental → zjm, Polynomial.coe_eval₂RingHom → z4Q, Polynomial.coeff_map → z0b, Polynomial.coeff_mul → zMz, Polynomial.eval₂RingHom → zqf, Polynomial.eval₂_C → zJU, Polynomial.hom_eval₂ → zly, Polynomial.mapRingHom → zhd, Polynomial.map_C → zrL, Polynomial.map_injective → zTo, Polynomial.map_map → zoi, Polynomial.ringHom_ext → z86, Polynomial.support_C → zy1, RingHom.comap_ker → zEW, RingHom.comp_apply → zQb
open _root_ renaming RingHom.congr_fun → zLs, RingHom.ext → zz4, RingHom.ker → zdq, Set.image_singleton → zyk, Set.range → zxp
set_option autoImplicit true
section
set_option maxSynthPendingDepth 8
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace YZ
noncomputable section
open K1 cu qQ Polynomial
open scoped BigOperators Classical
def c1 :Prop :=
  ∀ (q:zI) (P:Jet) (k :ℕ),N5 q→k<p →
    (∀ a b:ℕ,a+b<k→A5 1 b (A5 0 a P)∈q.asIdeal) →
    wU q P k
end
end YZ
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace aeF
noncomputable section
open cu qQ Polynomial
open scoped BigOperators RatFunc
section FunctionField
variable (k :Type) {F:Type} [zrb k] [zrb F] [zZE k F]
def aB6 (t:F) :Prop :=
  Transcendental k t ∧
    FiniteDimensional (IntermediateField.adjoin k ({t} : Set F)) F ∧
    Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F
def FZ (x :F) :ℕ:= by
  classical
  exact if IsAlgebraic k x then 0 else
    zsE (IntermediateField.adjoin k ({x} : Set F)) F
@[instance_reducible]
def Os :zZE (RatFunc k) (RatFunc F) :=
  (RatFunc.mapRingHom (zhd (algebraMap k F))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (zTo _ (algebraMap k F).injective))).toAlgebra
def ajJ (y v :F) :ℕ :=
  letI:=Os k (F:=F)
  FZ (RatFunc k)
    (algebraMap F (RatFunc F) y+RatFunc.X*algebraMap F (RatFunc F) v)
end FunctionField
section AffineCurve
def toFunction {A:Type} [za6 A] [ztn A] (a :A) :FractionRing A :=
 algebraMap A (FractionRing A) a
variable (k A:Type) [zrb k] [za6 A] [ztn A] [zZE k A]
end AffineCurve
end
end aeF
end
section
set_option backward.isDefEq.respectTransparency false
namespace czE
noncomputable section
open scoped TensorProduct
variable {k E σ:Type} [zrb k] [zrb E] [zZE k E]
def aPw (I:znc (z3y σ k)) :
    E ⊗[k] (z3y σ k ⧸ I) ≃ₐ[E]
      (z3y σ E ⧸ I.map (zDK (algebraMap k E))) := by
  let e :E ⊗[k] z3y σ k ≃ₐ[E] z3y σ E :=
    MvPolynomial.algebraTensorAlgEquiv k E
  let i:z3y σ k →+* E ⊗[k] z3y σ k :=
    (zgi (A:=E) (R:=k)).toRingHom
  have hmap :e.toAlgHom.toRingHom.comp i=zDK (algebraMap k E) := by
    apply zz4
    intro p
    change e (1 ⊗ₜ[k] p)=zDK (algebraMap k E) p
    simpa only [e,one_smul] using MvPolynomial.algebraTensorAlgEquiv_tmul k E 1 p
  exact (Algebra.TensorProduct.tensorQuotientEquiv E (z3y σ k) E I).trans
    (Ideal.quotientEquivAlg (I.map i) _ e (by
      change _=(I.map i).map e.toAlgHom.toRingHom
      rw [z0L,hmap]))
end
end czE
end
section
namespace K1_14_2_2_7_3_3
noncomputable section
open gT ac4
open aeF (FZ toFunction ajJ)
abbrev coord {k :Type} [zrb k] (H :znc (z3y (Fin 4) k))
  (i:Fin 4) :gk H :=
 zVv H (z9v i)
abbrev zL {k :Type} [zrb k] (H :znc (z3y (Fin 4) k))
  (i:Fin 2) :gk H :=
 coord H (Fin.castLE (by decide :2≤4) i)
abbrev a3d {k :Type} [zrb k] (H :znc (z3y (Fin 4) k))
  (G:zM1 (z3y (Fin 2) k)) :gk H :=
 zVv H (aMp G)
structure bbe (k A:Type) [zrb k] [za6 A] [ztn A] [zZE k A]
  (x y :A) where
 places :ℕ
 weight:Fin places→ℕ
 order :Fin places→A→ℕ
 scalar : ∀ p c,order p (algebraMap k A c)=0
 add : ∀ p f g,order p (f+g)≤ max (order p f) (order p g)
 mul : ∀ p f g,order p (f * g)≤order p f+order p g
 degree_eq : ∀ f,(∑ p,weight p*order p f)=FZ k (toFunction f)
 pencil_eq : (∑ p,weight p*max (order p x) (order p y)) =
  ajJ k (toFunction x) (toFunction y)
end
end K1_14_2_2_7_3_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000
namespace K1_14_2_2_7_3_3
noncomputable section
open Algebra Polynomial
open aeF (FZ toFunction)
open scoped BigOperators Polynomial nonZeroDivisors IntermediateField.algebraAdjoinAdjoin
theorem c5o {k A:Type} [zrb k] [za6 A] [ztn A]
  [zZE k A] [zUK k A] (hdim:ringKrullDim A=1) {f :A}
  (hf :f≠0) :zAa k (A ⧸ zye {f}) := by
 let I:znc A:=zye {f}
 let:zUK k (A ⧸ I) :=zrZ k I
 apply (Module.finite_iff_krullDimLE_zero k (A ⧸ I)).mpr
 apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
 intro P hP
 let:P.IsPrime :=hP.isPrime
 have hfP:f∈P:=hP.le (z5J f)
 have hne :P ≠ ⊥ := fun h=>hf (by simpa [h] using hfP)
 have hlow:1≤P.height :=
  Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hne)
 have hu: (P.height:WithBot ℕ∞)≤1 :=
  hdim ▸ Ideal.height_le_ringKrullDim_of_isPrime (I:=P)
 let:FiniteRingKrullDim A :=
  finiteRingKrullDim_iff_ne_bot_and_top.mpr (by rw [hdim]; exact ⟨by decide,by decide⟩)
 apply Ideal.isMaximal_of_height_eq_ringKrullDim
 rw [hdim]
 exact le_antisymm hu (WithBot.coe_le_coe.mpr hlow)
private theorem bx2 {k A:Type} [zrb k] [za6 A] [ztn A] [zZE k A]
  [zUK k A] (hdim:ringKrullDim A=1) :zls k A≤1 := by
 obtain ⟨d,f,hf,hfint⟩:=exists_finite_inj_algHom_of_fg k A
 let B:=z3y (Fin d) k
 let:zZE B A:=f.toRingHom.toAlgebra
 let:zsf k B A:=IsScalarTower.of_algHom f
 let:zAa B A:=hfint
 let:zVK B A:=Algebra.IsIntegral.of_finite B A
 let:FaithfulSMul B A:=(faithfulSMul_iff_algebraMap_injective B A).mpr hf
 have hdB:ringKrullDim B=(d:WithBot ℕ∞) := by
  simp [B,MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,ringKrullDim_eq_zero_of_field]
 obtain ⟨l,hlen⟩:=Order.le_krullDim_iff.mp hdB.ge
 have :=l.head.isPrime
 have hle : (⊥ : znc A).under B≤l.head.asIdeal:= by
  change Ideal.comap (algebraMap B A) ⊥ ≤ l.head.asIdeal
  have hinj:=FaithfulSMul.algebraMap_injective B A
  rw [← RingHom.ker_eq_comap_bot,(RingHom.injective_iff_ker_eq_bot _).mp hinj]
  exact bot_le
 obtain ⟨P,_,hP,hPhead⟩ :=
  Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : znc A) hle
 let:P.IsPrime :=hP
 let:P.LiesOver l.head.asIdeal:=⟨hPhead.symm⟩
 obtain ⟨L,hL,_,_⟩:=Ideal.exists_ltSeries_of_hasGoingUp l P
 have hle : (d:WithBot ℕ∞)≤ ringKrullDim A :=
  Order.le_krullDim_iff.mpr ⟨L,hL.trans hlen⟩
 rw [hdim] at hle
 have hd:d≤1 := by exact_mod_cast hle
 have ht:=trdeg_add_eq k B (A:=A)
 rw [trdeg_eq_zero (R:=B) (A:=A),add_zero] at ht
 rw [← ht]
 change zls k (z3y (Fin d) k)≤1
 rw [MvPolynomial.trdeg_of_isDomain]
 simpa using (Nat.cast_le.mpr hd: (d:Cardinal.{0})≤(1 :ℕ))
theorem bGB {k A:Type} [zrb k] [za6 A] [ztn A] [zZE k A]
  [zUK k A] (hdim:ringKrullDim A=1) {z :FractionRing A}
  (hz :Transcendental k z) :
  zAa (IntermediateField.adjoin k ({z} : Set (FractionRing A))) (FractionRing A) := by
 let F:=FractionRing A
 let R:=zum k ({z} : Set F)
 let B:=IntermediateField.adjoin k ({z} : Set F)
 have :zjH A F:=zyQ _ A⁰
 have ht:=trdeg_add_eq k A (A:=F)
 rw [trdeg_eq_zero (R:=A) (A:=F),add_zero] at ht
 have htr :zls k F≤1 :=ht.symm ▸ bx2 hdim
 let x :Fin 1→F:= fun _=>z
 have hi:AlgebraicIndependent k x :=algebraicIndependent_unique_type_iff.mpr hz
 have hx :=hi.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
 have hrange :zxp x = {z} := by simp [x]
 have hR:=hx.isAlgebraic
 rw [hrange] at hR
 let:zjH R F:=hR
 have :zjH B F :=
  Algebra.IsAlgebraic.extendScalars (zxb R B)
 have :zl5 A F:=zrU F A⁰
 have :zl5 k F:=zQi k A F
 have :zl5 B F:=z9q k B F
 exact zNf
private theorem cci {k A:Type} [zrb k] [za6 A] [ztn A] [zZE k A]
   {ι:Type} [Fintype ι] {f :A} (hf :f≠0) (b:ι→A)
   (hb:z14 k (fun i=>zVv (zye {f}) (b i)))
   (P:ι→k[X]) (hP: (∑ i,aeval f (P i)*b i)=0) : ∀ i,P i=0:= by
 classical
 by_contra hn
 push Not at hn
 obtain ⟨i,hi⟩:=hn
 have hex : ∃ n,∃ j,(P j).coeff n≠0 :=
   ⟨(P i).natTrailingDegree,i,coeff_natTrailingDegree_ne_zero.mpr hi⟩
 let n:=Nat.find hex
 have hdiv (j:ι) : (z7y (R:=k))^n∣P j :=
   X_pow_dvd_iff.mpr fun d hd=> by
     by_contra hc
     exact (Nat.find_min hex hd) ⟨j,hc⟩
 choose Q hQ using hdiv
 have hscaled:f^n*(∑ i,aeval f (Q i)*b i)=0:= by
   simpa only [hQ,aeval_mul,aeval_X_pow,mul_assoc,Finset.mul_sum] using hP
 have hrel :=(mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero n hf)
 let q:=zvR k (zye {f})
 have hqf :q f=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (z5J f)
 have hred:=congrArg q hrel
 simp only [map_sum,map_mul,← aeval_algHom_apply q,hqf,← coeff_zero_eq_aeval_zero',
   map_zero,← Algebra.smul_def] at hred
 have hzero :=Fintype.linearIndependent_iff.mp hb _ hred
 obtain ⟨j,hj⟩:=Nat.find_spec hex
 apply hj
 have heq : (P j).coeff n=(Q j).coeff 0:= by
   rw [hQ j]
   simpa using (coeff_X_pow_mul (Q j) n 0)
 exact heq.trans (hzero j)
private theorem ewy {k A:Type} [zrb k] [za6 A] [ztn A] [zZE k A]
   {ι:Type} [Fintype ι] {f :A} (hf :f≠0) (hz :Transcendental k (toFunction f))
   (b:ι→A) (hb:z14 k (fun i=>zVv (zye {f}) (b i))) :
   z14 (IntermediateField.adjoin k ({toFunction f} : Set (FractionRing A)))
     (fun i=>toFunction (b i)) := by
 let F:=FractionRing A
 let z :=toFunction f
 let R:=zum k ({z} : Set F)
 let B:=IntermediateField.adjoin k ({z} : Set F)
 apply LinearIndependent.localization (R:=R) B R⁰
 rw [Fintype.linearIndependent_iff]
 intro c hc i
 let e :=zjm k z hz
 let P (j:ι) :=e.symm (c j)
 let incl:A →ₐ[k] F:=zE2 k A F
 have he (j:ι) :incl (aeval f (P j))=(c j:F) := by
   rw [← aeval_algHom_apply incl]
   change aeval z (P j)=(c j:F)
   rw [← aeval_subalgebra_coe (P j) R ⟨z,Algebra.self_mem_adjoin_singleton k z⟩]
   change (e (P j) :F)=(c j:F)
   rw [show e (P j)=c j from e.apply_symm_apply (c j)]
 have hp: (∑ j,aeval f (P j)*b j)=0:= by
   apply zxb A F
   change incl (∑ j,aeval f (P j)*b j)=incl 0
   change (∑ j,(c j:F)*incl (b j))=0 at hc
   simpa only [map_sum,map_mul,map_zero,he] using hc
 exact e.symm.injective (by simpa [P] using cci hf b hb P hp i)
theorem eOy {k A:Type} [zrb k] [za6 A] [ztn A] [zZE k A]
    [zUK k A] (hdim:ringKrullDim A=1) {f :A} (hf :f≠0) :
    zsE k (A ⧸ zye {f})≤FZ k (toFunction f) := by
  classical
  by_cases h:IsAlgebraic k (toFunction f)
  · have hfalg:IsAlgebraic k f :=
      (isAlgebraic_algebraMap_iff (zxb A (FractionRing A))).mp h
    have htop: (zye {f} : znc A) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (z5J f) (hfalg.isIntegral.isUnit hf)
    rw [htop,Module.finrank_zero_of_subsingleton]
    exact zD0 _
  · unfold FZ
    rw [ite_eq_right h]
    let:zAa k (A ⧸ zye {f}) :=c5o hdim hf
    let:zAa (IntermediateField.adjoin k ({toFunction f} : Set (FractionRing A)))
        (FractionRing A) :=bGB hdim h
    let b:=Module.finBasis k (A ⧸ zye {f})
    choose lift hlift using fun i=>zld (b i)
    have hlin:z14 k (fun i=>zVv (zye {f}) (lift i)) :=
      (funext hlift).symm ▸ b.linearIndependent
    simpa only [Fintype.card_fin] using (ewy hf h lift hlin).fintype_card_le_finrank
end
end K1_14_2_2_7_3_3
end
section
set_option maxHeartbeats 400000
set_option maxSynthPendingDepth 8
namespace czl
noncomputable section
open gT WJ MM Polynomial
open scoped Polynomial WithZero
private theorem d3v {k K:Type} [zrb k] [zrb K]
  (v :Valuation K ℤᵐ⁰) (ι:k →+* K) (hι : ∀ c,v (ι c)≤1)
  {r t:K} (ht:v t≤1) (hrt:v (r - t)<1)
  (p:k[X]) (hp:v (p.eval₂ ι t)=1) :
  v (p.eval₂ ι r)=1 := by
 let O:=v.valuationSubring
 have hr :v r≤1 := by
  have h:=v.map_add_le hrt.le ht
  rwa [sub_add_cancel] at h
 let a :O:=⟨r,hr⟩
 let b:O:=⟨t,ht⟩
 let j:k →+* O:=ι.codRestrict O.toSubring hι
 let ρ:=IsLocalRing.residue O
 have hab:ρ a=ρ b:= by
  apply sub_eq_zero.mp
  rw [← map_sub,IsLocalRing.residue_eq_zero_iff,v.mem_maximalIdeal_iff]
  exact hrt
 let z (x :O) :=p.eval₂ j x
 have hz (x :O) : (z x :K)=p.eval₂ ι (x :K) :=
  zly p j O.subtype x
 have hres :ρ (z a)=ρ (z b) := by
  dsimp only [z]
  simp only [zly,hab]
 have hb:ρ (z b)≠0:= by
  rw [ne_eq,IsLocalRing.residue_eq_zero_iff,v.mem_maximalIdeal_iff,hz,show (b:K)=t from rfl,hp]
  exact lt_irrefl 1
 rw [← show (a :K)=r from rfl,← hz]
 refine le_antisymm (z a).2 (le_of_not_gt fun hlt=>hb ?_)
 rw [← hres,IsLocalRing.residue_eq_zero_iff,v.mem_maximalIdeal_iff]
 exact hlt
private theorem eET {k A:Type} [zrb k] [za6 A]
   [ztn A] [zZE k A] [zUK k A]
   (hdim:ringKrullDim A=1) (v :Valuation (FractionRing A) ℤᵐ⁰)
   (r y :FractionRing A) (hpoly : ∀ p:k[X],p≠0→v (aeval r p)=1) :
   v y≤1 := by
 have hr :Transcendental k r := by
   rintro ⟨p,hp,hzero⟩
   have h:=hpoly p hp
   rw [hzero,map_zero] at h
   exact zero_ne_one h
 let E :=IntermediateField.adjoin k {r}
 let:zAa E (FractionRing A) :=
   K1_14_2_2_7_3_3.bGB hdim hr
 let:v.IsTrivialOn E :=⟨by
   intro x hx
   have hx' : (x :FractionRing A)≠0:= fun h=>hx (Subtype.ext h)
   obtain ⟨p,q,hpq⟩ :=
     (IntermediateField.mem_adjoin_simple_iff k (x :FractionRing A)).mp x.2
   have hp:p≠0:= fun h=>hx' (by simp [hpq,h])
   have hq:q≠0:= fun h=>hx' (by simp [hpq,h])
   change v (x :FractionRing A)=1
   rw [hpq,v.map_div,hpoly p hp,hpoly q hq,div_self one_ne_zero]⟩
 by_contra! h
 have hy :y≠0:= by
   intro hy
   simp [hy] at h
 exact (v.transcendental_of_ne_one E y hy h.ne')
   (zgs y)
private theorem ey7 {L K:Type} [zrb L] [zrb K]
  (e :L →+* K) (x y :L) (t:K) (hy :e y≠0) :
  e (-x/y) - t = -(e x+t*e y)/e y := by
 rw [map_div₀,map_neg,neg_add,← sub_eq_add_neg,sub_div,mul_div_cancel_right₀ _ hy]
variable {k :Type} [zrb k] (D:znc (yT k))
private theorem cTH :ajC k≠0 :=
 (map_ne_zero_iff _ (zxb (zM1 k) (e7 k))).mpr
   Polynomial.X_ne_zero
private theorem bwb :
    LX D =Je D (some 0) +
      algebraMap (e7 k) (CurveField D) (ajC k)*Je D (some 1) := by
  have hC (c:e7 k) :
      algebraMap (Cz D) (CurveField D)
        (zVv (Z9 D) (znf c)) =
        algebraMap (e7 k) (CurveField D) c :=
    (zG3 (e7 k) (Cz D) (CurveField D) c).symm
  let f :yT (e7 k) →+* CurveField D :=
    (algebraMap (Cz D) (CurveField D)).comp (zVv (Z9 D))
  have hX (i:Option (Fin 2)) :Je D i=f (z9v i) := by
    change f (zDK (algebraMap k (e7 k)) (z9v i))= _
    rw [z7N]
  change f (z9v (some 0)+MvPolynomial.C (ajC k)*z9v (some 1))= _
  rw [hX,hX,f.map_add,f.map_mul]
  exact congrArg (fun c=>f (z9v (some 0))+c*f (z9v (some 1))) (hC _)
variable [ztn (Cz D)]
private theorem gni (hprime :D.IsPrime)
    (hdim:ringKrullDim (gk D)=1)
    (w:zZ (e7 k) (CurveField D))
    (hy :1<w.val (Je D (some 1))) :
    w.val (Je D (some 1))≤w.val (LX D) := by
  by_contra! hcancel
  let:ztn (gk D) :=(Ideal.Quotient.isDomain_iff_prime D).mpr hprime
  let F:=e7 k
  let K:=CurveField D
  let A:=gk D
  let L:=FractionRing A
  let ι:k →+* K:=(algebraMap F K).comp (algebraMap k F)
  let t:K:=algebraMap F K (ajC k)
  let g:A →+* K:=zP2 D (an9 D) fun f hf=> by
    change algebraMap (Cz D) K (zVv (Z9 D) (Qe k f))=0
    have hf' : Qe k f∈Z9 D:=z7X (Qe k) hf
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf',map_zero]
  have hg:zq4 g:=(injective_iff_map_eq_zero g).mpr fun a ha=> by
    obtain ⟨f,rfl⟩:=zld a
    change an9 D f=0 at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Classical.byContradiction fun hf =>
      cRU hf ha)
  let e :L →+* K:=zIj hg
  have he (f :yT k) :
      e (algebraMap A L (zVv D f))=an9 D f :=
    zoc hg _
  have heC:e.comp (algebraMap k L)=ι:= by
    apply zz4
    intro c
    change e (algebraMap k L c)=ι c
    rw [zG3 k A L]
    change e (algebraMap A L (zVv D (znf c)))=ι c
    rw [he]
    simp only [an9,Qe,zQb,zpw]
    exact (zG3 F (Cz D) K (algebraMap k F c)).symm
  let x :=algebraMap A L (zVv D (z9v (some 0)))
  let y :=algebraMap A L (zVv D (z9v (some 1)))
  let r := -x/y
  have hx' : e x=Je D (some 0) :=he _
  have hy' : e y=Je D (some 1) :=he _
  have hvy :1<w.val (e y) := by simpa only [hy'] using hy
  have hy0:e y≠0:= by
    intro hz
    simp [hz] at hvy
  have hdiff :e r - t = -LX D /e y := by
    rw [bwb,← hx',← hy']
    exact ey7 e x y t hy0
  have hclose :w.val (e r - t)<1 := by
    rw [hdiff,w.val.map_div,w.val.map_neg,div_lt_one₀ (w.val.pos_iff.mpr hy0)]
    simpa only [hy'] using hcancel
  have htv :w.val t≤1 :=(w.trivial _ cTH).le
  have hι (c:k) :w.val (ι c)≤1 := by
    change w.val (algebraMap F K (algebraMap k F c))≤1
    by_cases hc:algebraMap k F c=0
    · simp [hc]
    · exact (w.trivial _ hc).le
  have hTpoly (p:k[X]) (hp:p≠0) :w.val (p.eval₂ ι t)=1 := by
    let j:zM1 k →+* K :=
      (algebraMap F K).comp (algebraMap (zM1 k) F)
    have hj:j.comp z1z=ι:= by
      apply zz4
      intro c
      change algebraMap F K (algebraMap (zM1 k) F (z1z c)) =
        algebraMap F K (algebraMap k F c)
      rw [zG3 k (zM1 k) F]
      rfl
    have heval :=zly p z1z j z7y
    rw [Polynomial.eval₂_C_X,hj] at heval
    change j p=p.eval₂ ι t at heval
    rw [← heval]
    exact w.trivial _ (fun hz=>hp ((zxb (zM1 k) F)
      (hz.trans (map_zero _).symm)))
  have hpoly (p:k[X]) (hp:p≠0) : (w.val.comap e) (aeval r p)=1 := by
    change w.val (e (p.eval₂ (algebraMap k L) r))=1
    rw [zly,heC]
    exact d3v w.val ι hι htv hclose p (hTpoly p hp)
  exact (not_le_of_gt hvy) (eET hdim (w.val.comap e) r y hpoly)
private theorem a6G {F K:Type} [zrb F] [zrb K] [zZE F K]
   (w:zZ F K) {a b:K} (h:w.val a≤w.val b) :poleOrder w a≤poleOrder w b:= by
 by_cases ha :w.val a=0
 · simp [poleOrder,ha]
 have hb:w.val b≠0:=ne_of_gt ((zero_lt_iff.mpr ha).trans_le h)
 exact z0Z ((WithZero.log_le_log ha hb).mpr h)
theorem proof :MM.c4 := by
  intro k _ D _ hprime hdim w
  let x :=Je D (some 0)
  let y :=Je D (some 1)
  let t:=algebraMap (e7 k) (CurveField D) (ajC k)
  have hty :w.val (t*y)=w.val y := by
    rw [map_mul,w.trivial _ cTH,one_mul]
  change max (poleOrder w x) (poleOrder w y)≤poleOrder w (LX D)
  rcases lt_trichotomy (w.val x) (w.val y) with hlt | heq | hgt
  · have hs :w.val (LX D)=w.val y := by
      rw [bwb,show w.val (x+t*y)=w.val (t*y) from
        w.val.map_add_eq_of_lt_right (hty ▸ hlt),hty]
    exact max_le (a6G w (hs ▸ hlt.le)) (a6G w hs.ge)
  · by_cases hy :1<w.val y
    · have hs :=gni D hprime hdim w hy
      exact max_le (a6G w (heq.trans_le hs)) (a6G w hs)
    · have hzero :poleOrder w y=0:= by
        by_cases hy0:w.val y=0
        · simp [poleOrder,hy0]
        · rw [poleOrder,Int.toNat_eq_zero]
          exact (WithZero.log_le_iff_le_exp hy0).mpr (by simpa using le_of_not_gt hy)
      have hxzero :=(a6G w heq.le).trans (le_of_eq hzero)
      exact (max_le hxzero (le_of_eq hzero)).trans (zD0 _)
  · have hs :w.val (LX D)=w.val x := by
      rw [bwb]
      exact w.val.map_add_eq_of_lt_left (hty ▸ hgt)
    exact max_le (a6G w hs.ge) (a6G w (hs ▸ hgt.le))
end
end czl
end
section
namespace XX
noncomputable section
open E7 (CurvePlace poleOrder)
open scoped BigOperators Polynomial WithZero nonZeroDivisors
variable {k F:Type} [zrb k] [zrb F] [zZE k F]
abbrev EO (p:CurvePlace k F) :=IsLocalRing.ResidueField p.value.valuationSubring
def aoG (p:CurvePlace k F) :k →+* p.value.valuationSubring :=
  (algebraMap k F).codRestrict p.value.valuationSubring.toSubring (fun a=> by
    change p.value (algebraMap k F a)≤1
    obtain rfl | ha :=eq_or_ne a 0
    · simp
    · rw [p.on_constants _ ha])
instance gRu (p:CurvePlace k F) :zZE k (EO p) :=
 ((IsLocalRing.residue _).comp (aoG p)).toAlgebra
def placeWeight (p:CurvePlace k F) :ℕ :=
 zsE k (EO p)
@[instance_reducible]
def adp (u:F) :zZE k[X] F :=
 (zEU u).toRingHom.toAlgebra
abbrev ach (x :F) :=
 letI:=adp (k :=k) x⁻¹
 integralClosure k[X] F
def aFr (x :F) :ℕ :=
 ∑ᶠ p:CurvePlace k F,placeWeight p*poleOrder p.value x
theorem ad4 (P:k[X]) :
   letI:=aeF.Os k (F:=F)
   algebraMap (RatFunc k) (RatFunc F) (algebraMap k[X] (RatFunc k) P) =
     algebraMap F[X] (RatFunc F) (P.map (algebraMap k F)) := by
 let f :=zhd (algebraMap k F)
 let hf :k[X]⁰≤F[X]⁰.comap f :=
   nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
     (zTo _ (algebraMap k F).injective)
 change RatFunc.map f hf (algebraMap k[X] _ P)=algebraMap F[X] _ (f P)
 simpa only [map_one,div_one] using RatFunc.map_apply_div f hf P 1
def OG [zZE (RatFunc k) (RatFunc F)]
    (p:CurvePlace k F) (q:CurvePlace (RatFunc k) (RatFunc F)) :Prop :=
  ∀ P:F[X],q.value (algebraMap F[X] (RatFunc F) P) =
    P.support.sup (fun i=>p.value (P.coeff i))
end
end XX
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace aZc
noncomputable section
open Polynomial IntermediateField
open scoped nonZeroDivisors
variable {k F:Type} [zrb k] [zrb F] [zZE k F]
abbrev origin (k :Type) [zrb k] :znc k[X] :=zye {z7y}
instance eH7: (origin k).IsMaximal :=
 PrincipalIdealRing.isMaximal_of_irreducible irreducible_X
def caN : (k[X] ⧸ origin k) ≃ₐ[k] k := by
 rw [show origin k=zye {z7y - C (0:k)} by simp]
 exact quotientSpanXSubCAlgEquiv 0
abbrev FO (u:F) :=IntermediateField.adjoin k ({u} : Set F)
theorem cE4 (x :F) :FO (k :=k) x⁻¹=FO (k :=k) x := by
 apply le_antisymm <;> apply IntermediateField.adjoin_le_iff.mpr
 · exact Set.singleton_subset_iff.mpr (IntermediateField.inv_mem _ (mem_adjoin_simple_self k x))
 · apply Set.singleton_subset_iff.mpr
   change x∈FO (k :=k) x⁻¹
   simpa only [inv_inv] using
    (FO (k :=k) x⁻¹).inv_mem (mem_adjoin_simple_self k x⁻¹)
section Chart
variable [zZE k[X] F] [zsf k k[X] F]
def coordinate (k :Type) [zrb k] (F:Type) [zrb F] [zZE k[X] F] :F :=
 algebraMap k[X] F z7y
abbrev DR (k :Type) [zrb k] (F:Type) [zrb F] [zZE k[X] F] :=
 integralClosure k[X] F
private theorem bm1 (f :k[X]) :algebraMap k[X] F f=aeval (coordinate k F) f := by
 have h:zE2 k k[X] F=aeval (coordinate k F) :=
  Polynomial.algHom_ext (by simp [coordinate])
 exact DFunLike.congr_fun h f
private theorem cFm (h:Transcendental k (coordinate k F)) :
  zq4 (algebraMap k[X] F) := by
 intro p q hpq
 apply (transcendental_iff_injective.mp h)
 rwa [← bm1 (F:=F) p,← bm1 (F:=F) q]
theorem c1K (h:Transcendental k (coordinate k F)) :
  zYo k[X] (DR k F) := by
 have :zYo k[X] F :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (cFm h)
 exact IsIntegralClosure.isTorsionFree k[X] F
local instance gPh:zZE k[X] (FO (k :=k) (coordinate k F)) :=
 (aeval (AdjoinSimple.gen k (coordinate k F))).toRingHom.toAlgebra
local instance gPi:zsf k[X] (FO (k :=k) (coordinate k F)) F :=
  zsL fun f=> by
    rw [bm1 (F:=F) f]
    exact aeval_algHom_apply (FO (k :=k) (coordinate k F)).val
      (AdjoinSimple.gen k (coordinate k F)) f
private theorem bWT (h:Transcendental k (coordinate k F)) :
   z0o k[X] (FO (k :=k) (coordinate k F)) := by
 let K:=FO (k :=k) (coordinate k F)
 have :FaithfulSMul k[X] K:=(faithfulSMul_iff_algebraMap_injective k[X] K).mpr
   (fun _ _ e=>cFm h (by
     rw [IsScalarTower.algebraMap_eq k[X] K F]
     exact congrArg (algebraMap K F) e))
 apply IsFractionRing.of_field
 intro z
 obtain ⟨p,q,hpq⟩:=(mem_adjoin_simple_iff k (z :F)).mp z.property
 refine ⟨p,q,(algebraMap K F).injective ?_⟩
 rw [map_div₀,← zG3 k[X] K F,
   ← zG3 k[X] K F,bm1 (F:=F) p,bm1 (F:=F) q]
 exact hpq
theorem eFk (h:Transcendental k (coordinate k F))
  [FiniteDimensional (FO (k :=k) (coordinate k F)) F] :
  z0o (DR k F) F:= by
 have :=bWT h
 exact integralClosure.isFractionRing_of_finite_extension
  (FO (k :=k) (coordinate k F)) F
theorem bJK (h:Transcendental k (coordinate k F))
    [FiniteDimensional (FO (k :=k) (coordinate k F)) F]
    [zAa k[X] (DR k F)] :
    IsDedekindDomain (DR k F) := by
  let B:=DR k F
  have :=bWT h
  exact
    { isNoetherianRing_iff.mpr (isNoetherian_of_tower k[X] (show IsNoetherian k[X] B from inferInstance)),
      Ring.DimensionLEOne.of_isIntegral k[X] B,
      integralClosure.isIntegrallyClosedOfFiniteExtension
        (FO (k :=k) (coordinate k F)) with }
theorem eFm (h:Transcendental k (coordinate k F))
   [FiniteDimensional (FO (k :=k) (coordinate k F)) F]
   [zAa k[X] (DR k F)] :
   zsE k[X] (DR k F) =
     zsE (FO (k :=k) (coordinate k F)) F:= by
 let K:=FO (k :=k) (coordinate k F)
 let B:=DR k F
 have :z0o k[X] K:=bWT h
 have :zYo k[X] B:=c1K h
 have :zNo (zTz B k[X]⁰) F :=
   IsIntegralClosure.isLocalization k[X] K F B
 let b:=Module.Basis.localizationLocalization K k[X]⁰ F (Module.Free.chooseBasis k[X] B)
 rw [Module.finrank_eq_card_chooseBasisIndex,Module.finrank_eq_card_basis b]
end Chart
end
end aZc
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000
namespace K1_14_2_2_7_3_3
noncomputable section
open gT ac4
open aeF (FZ toFunction ajJ)
open scoped BigOperators
def c1 :Prop :=
  ∀ (k A:Type) [zrb k] [za6 A] [ztn A] [zZE k A]
    [zUK k A],ringKrullDim A=1 →
    ∀ (x y :A),Nonempty (bbe k A x y)
def c2 :Prop :=
  ∀ (k :Type) [zrb k] (H :znc (z3y (Fin 4) k)) [H.IsPrime],
    ringKrullDim (gk H)=1 →
    zAa (CS k) (W1 H) →
    zAa (CS k) (adm H) →
    zsE (CS k) (W1 H) =
      ajJ k (toFunction (coord H 0)) (toFunction (coord H 1)) ∧
    zsE (CS k) (adm H) =
      FZ k (toFunction (coord H 3))
section Estimates
variable {k A:Type} [zrb k] [za6 A] [ztn A] [zZE k A]
 {x y :A} (D:bbe k A x y) (p:Fin D.places)
private theorem c4F {ι:Type} (S:Finset ι) (f :ι→A) (d:ℕ)
   (h : ∀ i∈S,D.order p (f i)≤d) :D.order p (∑ i∈S,f i)≤d:= by
 classical
 induction S using Finset.induction_on with
 | empty =>
   simpa using (D.scalar p 0).le.trans (zD0 d)
 | @insert i S hi ih =>
   rw [Finset.sum_insert hi]
   exact (D.add p _ _).trans (max_le (h i (Finset.mem_insert_self _ _))
     (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj))))
private theorem cca (f :A) (n:ℕ) :D.order p (f^n)≤n*D.order p f := by
 induction n with
 | zero=>simpa using (D.scalar p 1).le
 | succ n ih =>
   rw [pow_succ,Nat.succ_mul]
   exact (D.mul p _ _).trans (zlr ih _)
private theorem go8 (z :Fin 2→A) (f :z3y (Fin 2) k) :
    D.order p (zSZ (algebraMap k A) z f) ≤
      f.totalDegree*max (D.order p (z 0)) (D.order p (z 1)) := by
  classical
  rw [MvPolynomial.eval₂_eq']
  apply c4F D p
  intro e he
  have hdeg:=MvPolynomial.le_totalDegree he
  rw [Finsupp.sum_fintype _ _ (fun _=>rfl),Fin.sum_univ_two] at hdeg
  rw [Fin.prod_univ_two]
  apply (D.mul p _ _).trans
  rw [D.scalar,zero_add]
  apply (D.mul p _ _).trans
  calc
    _≤e 0*max (D.order p (z 0)) (D.order p (z 1)) +
        e 1*max (D.order p (z 0)) (D.order p (z 1)) :=
      z9f
        ((cca D p _ _).trans (zBI _ (le_max_left _ _)))
        ((cca D p _ _).trans (zBI _ (le_max_right _ _)))
    _≤_:= by rw [← Nat.add_mul]; exact ztf _ hdeg
end Estimates
private theorem dSP {k :Type} [zrb k] (H :znc (z3y (Fin 4) k))
    (G:zM1 (z3y (Fin 2) k)) :
    a3d H G =
      ∑ j∈G.support,zSZ (algebraMap k (gk H)) (zL H)
        (G.coeff j)*coord H 3^j:= by
  let q:=zVv H
  let r :z3y (Fin 2) k →+* z3y (Fin 4) k :=
    (MvPolynomial.rename (Fin.castLE (by decide :2≤4))).toRingHom
  have heval :q.comp r=zOD (algebraMap k (gk H)) (zL H) := by
    apply zXT
    · intro a
      simp only [zQb,r,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        MvPolynomial.rename_C,zTv]
      exact (zOY (R₁:=k) H a).symm
    · intro i
      simp [q,r,zL,coord]
  change q (G.eval₂ r (z9v 3))= _
  rw [zly,heval,Polynomial.eval₂_eq_sum]
  rfl
private theorem dSL {k :Type} [zrb k] (H :znc (z3y (Fin 4) k))
    [H.IsPrime] (D:bbe k (gk H) (coord H 0) (coord H 1))
    {G:zM1 (z3y (Fin 2) k)} {U J:ℕ} (hJ:G.natDegree≤J)
    (hU : ∀ j,(G.coeff j).totalDegree≤U) :
    FZ k (toFunction (a3d H G)) ≤
      U*ajJ k (toFunction (coord H 0)) (toFunction (coord H 1)) +
      J*FZ k (toFunction (coord H 3)) := by
  classical
  have hbound (p:Fin D.places) :
      D.order p (a3d H G) ≤
        U*max (D.order p (coord H 0)) (D.order p (coord H 1)) +
        J*D.order p (coord H 3) := by
    rw [dSP]
    apply c4F D p
    intro j hj
    have hdeg:=(Polynomial.le_natDegree_of_mem_supp j hj).trans hJ
    apply (D.mul p _ _).trans
    apply z9f
    · exact (go8 D p (zL H) (G.coeff j)).trans
        (ztf _ (hU j))
    · exact (cca D p _ j).trans (ztf _ hdeg)
  rw [← D.degree_eq (a3d H G),← D.pencil_eq,← D.degree_eq (coord H 3)]
  calc
    _ ≤ ∑ p,D.weight p *
        (U*max (D.order p (coord H 0)) (D.order p (coord H 1)) +
          J*D.order p (coord H 3)) :=
      Finset.sum_le_sum fun p _=>zBI _ (hbound p)
    _ = _:= by
      simp only [Nat.mul_add,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_left_comm]
private def bDI {k :Type} [zrb k] (H :znc (z3y (Fin 4) k))
   (G:zM1 (z3y (Fin 2) k)) :
   (gk H ⧸ zye {a3d H G}) ≃ₐ[k]
     gk (H ⊔ zye {aMp G}) := by
 let I:znc (z3y (Fin 4) k) :=zye {aMp G}
 have hmap :I.map (zvR k H)=zye {a3d H G} := by
   dsimp only [I]
   rw [zlN,zyk]
   rfl
 exact (z9k k hmap.symm).trans (DoubleQuot.quotQuotEquivQuotSupₐ k H I)
theorem of_children (h1 :c1) (h2 :c2) :ac4.c3:= by
 intro k _ H U J G hprime hdim hseed hv hJ hU hG
 let:H.IsPrime :=hprime
 let:zUK k (gk H) :=zrZ k H
 have hne :a3d H G≠0 :=
  fun hz=>hG (Ideal.Quotient.eq_zero_iff_mem.mp hz)
 have hfin:=c5o (k :=k) hdim hne
 obtain ⟨D⟩:=h1 k (gk H) hdim (coord H 0) (coord H 1)
 obtain ⟨hseedDegree,hvDegree⟩:=h2 k H hdim hseed hv
 have hlength:=(eOy (k :=k) hdim hne).trans (dSL H D hJ hU)
 let e :=(bDI H G).toLinearEquiv
 let:=hfin
 exact ⟨Module.Finite.equiv e,by rwa [← e.finrank_eq,hseedDegree,hvDegree]⟩
end
end K1_14_2_2_7_3_3
end
section
set_option backward.isDefEq.respectTransparency false
namespace XX
noncomputable section
open E7 (CurvePlace)
open aeF (Os)
open scoped Polynomial WithZero nonZeroDivisors
variable {k F:Type} [zrb k] [zrb F] [zZE k F]
private def adG (w:Valuation F ℤᵐ⁰) (P:F[X]) :ℤᵐ⁰ :=
 P.support.sup (fun n=>w (P.coeff n))
private theorem aMX (w:Valuation F ℤᵐ⁰) (P:F[X]) (n:ℕ) :
   w (P.coeff n)≤adG w P:= by
 by_cases hn:P.coeff n=0
 · simp [hn]
 · exact zZi (f := fun i=>w (P.coeff i))
     (Polynomial.mem_support_iff.mpr hn)
private theorem cTA (w:Valuation F ℤᵐ⁰) (a :F) :
   adG w (z1z a)=w a := by
 by_cases ha :a=0
 · simp [ha,adG]
 · simp [adG,zy1 ha]
private theorem b4t (w:Valuation F ℤᵐ⁰) {P:F[X]} (hp:P≠0) :
  adG w P≠0:= by
 obtain ⟨n,hn⟩:=Polynomial.support_nonempty.mpr hp
 have hv :0<w (P.coeff n) :=
  WithZero.pos_iff_ne_zero.mpr (w.zero_iff.not.mpr (Polynomial.mem_support_iff.mp hn))
 exact (hv.trans_le (aMX w P n)).ne'
private theorem cNC (w:Valuation F ℤᵐ⁰) (P:F[X]) (hp:P≠0) :
   ∃ i,w (P.coeff i)=adG w P ∧
     ∀ n< i,w (P.coeff n)<adG w P:= by
 classical
 have hs :=Polynomial.support_nonempty.mpr hp
 obtain ⟨i,_,hi⟩:=Finset.exists_mem_eq_sup' hs (fun n=>w (P.coeff n))
 rw [zWa] at hi
 have hex : ∃ n,w (P.coeff n)=adG w P:=⟨i,hi.symm⟩
 exact ⟨Nat.find hex,Nat.find_spec hex,fun n hn =>
   lt_of_le_of_ne (aMX w P n) (Nat.find_min hex hn)⟩
private theorem efd (w:Valuation F ℤᵐ⁰) (P Q:F[X]) :
    adG w (P*Q)=adG w P*adG w Q:= by
  apply le_antisymm
  · apply zf9
    intro n _
    rw [zMz]
    apply w.map_sum_le
    intro a _
    rw [map_mul]
    exact mul_le_mul' (aMX w P a.1) (aMX w Q a.2)
  obtain rfl | hp:=eq_or_ne P 0
  · simp [adG]
  obtain rfl | hq:=eq_or_ne Q 0
  · simp [adG]
  obtain ⟨i,hi,hi_min⟩:=cNC w P hp
  obtain ⟨j,hj,hj_min⟩:=cNC w Q hq
  have hvp:=WithZero.pos_iff_ne_zero.mpr (b4t w hp)
  have hvq:=WithZero.pos_iff_ne_zero.mpr (b4t w hq)
  have hdominant:w ((P*Q).coeff (i+j))=adG w P*adG w Q:= by
    rw [zMz]
    rw [w.map_sum_eq_of_lt (j:=(i,j)) (by simp)]
    · simp only [map_mul,hi,hj]
    intro a ha
    obtain ⟨hamem,hane⟩:=Finset.mem_sdiff.mp ha
    have hsum:a.1+a.2=i+j:=Finset.HasAntidiagonal.mem_antidiagonal.mp hamem
    simp only [map_mul,hi,hj]
    have hindex :a.1< i∨a.2<j:= by
      by_contra! h
      apply hane
      apply Finset.mem_singleton.mpr
      exact Prod.ext (by omega) (by omega)
    rcases hindex with h | h
    · exact (mul_le_mul' le_rfl (aMX w Q a.2)).trans_lt
        (mul_lt_mul_of_pos_right (hi_min _ h) hvq)
    · exact (mul_le_mul' (aMX w P a.1) le_rfl).trans_lt
        (mul_lt_mul_of_pos_left (hj_min _ h) hvp)
  rw [← hdominant]
  exact aMX w (P*Q) (i+j)
private def efc (w:Valuation F ℤᵐ⁰) :Valuation F[X] ℤᵐ⁰ where
 toFun:=adG w
 map_zero' := by simp [adG]
 map_one' := by simpa using cTA w 1
 map_mul' := efd w
 map_add_le_max' P Q:= by
  apply zf9
  intro n _
  rw [Polynomial.coeff_add]
  exact (w.map_add _ _).trans (max_le_max (aMX w P n) (aMX w Q n))
private def b4s (w:Valuation F ℤᵐ⁰) :Valuation (RatFunc F) ℤᵐ⁰ :=
 (efc w).extendToLocalization (S:=F[X]⁰)
   (fun _ h=>b4t w (nonZeroDivisors.ne_zero h)) (RatFunc F)
private theorem bHf (w:Valuation F ℤᵐ⁰) (P:F[X]) :
  b4s w (algebraMap F[X] (RatFunc F) P)=adG w P :=
 Valuation.extendToLocalization_apply_map_apply _ _ _ _
private theorem cTB (p:CurvePlace k F) (P:k[X]) (hp:P≠0) :
  adG p.value (P.map (algebraMap k F))=1 := by
 have hmap :P.map (algebraMap k F)≠0:= fun h =>
  hp ((zTo _ (algebraMap k F).injective) (by simpa using h))
 unfold adG
 rw [← zWa (Polynomial.support_nonempty.mpr hmap)]
 apply Finset.sup'_eq_of_forall
 intro i hi
 rw [z0b]
 apply p.on_constants
 intro hc
 exact (Polynomial.mem_support_iff.mp hi) (by simp [hc])
theorem bdy (p:CurvePlace k F) :
    letI:=Os k (F:=F)
    ∃ q:CurvePlace (RatFunc k) (RatFunc F),OG p q:= by
  let _:zZE (RatFunc k) (RatFunc F) :=Os k (F:=F)
  let q:CurvePlace (RatFunc k) (RatFunc F) := {
    value :=b4s p.value
    normalized:= by
      intro a
      obtain ⟨x,hx⟩:=p.normalized a
      exact ⟨RatFunc.C x,(bHf p.value (z1z x)).trans
        ((cTA p.value x).trans hx)⟩
    on_constants := by
      intro a
      induction a using RatFunc.induction_on with
      | _ P Q hQ =>
        intro ha
        have hP:P≠0:= by
          intro h
          exact ha (by simp [h])
        rw [map_div₀,(b4s p.value).map_div,ad4,
          ad4,bHf,bHf,
          cTB p P hP,cTB p Q hQ,div_one] }
  exact ⟨q,bHf p.value⟩
end
end XX
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
namespace aZc
noncomputable section
open E7 (CurvePlace poleOrder)
open XX (aoG)
open Polynomial WithZero IsDedekindDomain
open scoped WithZero nonZeroDivisors
variable {k F:Type} [zrb k] [zrb F] [zZE k F]
private theorem c4D {v :Valuation F ℤᵐ⁰} {x :F} (hx :x≠0) :
  poleOrder v x≠0↔v x⁻¹<1 := by
 have hv :v x≠0:=(v.ne_zero_iff).mpr hx
 have hlog:0<log (v x)↔1<v x := by
  simpa only [log_one] using (log_lt_log (x :=1) one_ne_zero hv)
 rw [map_inv₀,inv_lt_one₀ (zero_lt_iff.mpr hv),← hlog,poleOrder]
 omega
private theorem cW9 {v :ℤᵐ⁰} (h:1<v) :exp (1 :ℤ)≤v := by
 apply le_log_iff_exp_le (zero_lt_one.trans h).ne' |>.mp
 have :0<log v := by
  simpa only [log_one] using (log_lt_log one_ne_zero (zero_lt_one.trans h).ne').mpr h
 omega
private theorem eFr {v w:Valuation F ℤᵐ⁰}
   (hv :zpX v) (hw:zpX w) (h:v.IsEquiv w) :v=w:= by
 obtain ⟨a,ha⟩:=hv (exp 1)
 obtain ⟨b,hb⟩:=hw (exp 1)
 have hap:1<w a :=h.one_lt_iff_one_lt.mp (by simp [ha])
 have hbp:1<v b:=h.one_lt_iff_one_lt.mpr (by simp [hb])
 have haw:w a=exp 1 :=
   le_antisymm (hb ▸ (h a b).mp (ha ▸ cW9 hbp)) (cW9 hap)
 ext z
 obtain rfl | hz :=eq_or_ne z 0
 · simp
 let n:=log (v z)
 have he (t:Valuation F ℤᵐ⁰) (ht:t a=exp 1) :t (a^n)=exp n:= by
   rw [map_zpow₀,ht,← exp_zsmul]
   simp
 have hvz :v z=v (a^n) := by
   rw [he v ha,exp_log ((v.ne_zero_iff).mpr hz)]
 exact hvz.trans ((he v ha).trans ((he w haw).symm.trans (h.eq_iff.mp hvz).symm))
section B6
variable [zZE k[X] F] [zsf k k[X] F]
abbrev aBi (k F:Type) [zrb k] [zrb F] [zZE k[X] F] :=
 (origin k).primesOver (DR k F)
abbrev bkT (k F:Type) [zrb k] [zrb F] [zZE k F] (x :F) :=
 {p:CurvePlace k F // poleOrder p.value x≠0}
private theorem aMQ (p:CurvePlace k F) (hu:p.value (coordinate k F)<1)
   (f :k[X]) :algebraMap k[X] F f∈p.value.valuationSubring := by
 let u:p.value.valuationSubring :=⟨coordinate k F,hu.le⟩
 let g:k[X] →+* p.value.valuationSubring :=eval₂RingHom (aoG p) u
 have hg:p.value.valuationSubring.toSubring.subtype.comp g=algebraMap k[X] F:= by
   apply z86
   · intro a
     change ((g (C a) :p.value.valuationSubring) :F)=algebraMap k[X] F (C a)
     rw [show g (C a)=aoG p a from eval₂_C _ _]
     exact zG3 k k[X] F a
   · change ((g z7y:p.value.valuationSubring) :F)=coordinate k F
     rw [show g z7y=u from eval₂_X _ _]
 rw [← hg]
 exact (g f).property
private def b9T (p:CurvePlace k F) (hu:p.value (coordinate k F)<1) :
   DR k F →+* p.value.valuationSubring :=
 let V:=p.value.valuationSubring.toSubring
 have :z0o V F:=inferInstanceAs (z0o p.value.valuationSubring F)
 have :IsIntegrallyClosedIn V F :=
   (isIntegrallyClosed_iff_isIntegrallyClosedIn F).mp
     (inferInstanceAs (IsIntegrallyClosed p.value.valuationSubring))
 let h:=Subring.integralClosure_le_iff.mpr (aMQ p hu)
 (integralClosure k[X] F).val.toRingHom.codRestrict V (fun b=>h b.property)
private def center (p:CurvePlace k F) (hu:p.value (coordinate k F)<1) :
   znc (DR k F) :=
 (IsLocalRing.maximalIdeal p.value.valuationSubring).comap (b9T p hu)
private theorem bsx (p:CurvePlace k F) (hu:p.value (coordinate k F)<1)
  (b:DR k F) :b∈center p hu↔p.value (b:F)<1 :=
 p.value.mem_maximalIdeal_iff (a :=b9T p hu b)
private def bmN (p:CurvePlace k F) (hu:p.value (coordinate k F)<1) :
  aBi k F:= by
 let Q:=center p hu
 have hQ:Q.IsPrime :=zCL _
 have hX:algebraMap k[X] (DR k F) z7y∈Q :=
  (bsx p hu _).mpr hu
 have hle :origin k≤Q.under k[X] :=(zvl _).mpr hX
 have hproper :Q.under k[X] ≠ ⊤ := (zCL (algebraMap k[X] _) (K:= Q)).ne_top
 exact ⟨Q,hQ,⟨(eH7 (k :=k)).eq_of_le hproper hle⟩⟩
variable [IsDedekindDomain (DR k F)] [z0o (DR k F) F]
def aI6 (hcoord:coordinate k F≠0) (P:aBi k F) :
    HeightOneSpectrum (DR k F) where
  asIdeal:=P.val
  isPrime :=P.property.1
  ne_bot:= by
    have :P.val.LiesOver (origin k) :=P.property.2
    have hX:=(P.val.mem_of_liesOver (origin k) z7y).mp (zCn (by simp))
    intro h
    rw [h,Ideal.mem_bot] at hX
    apply hcoord
    rw [coordinate,zG3 k[X] (DR k F) F,hX,map_zero]
private def bt3 (hcoord:coordinate k F≠0) (P:aBi k F) :CurvePlace k F where
 value :=(aI6 hcoord P).valuation F
 normalized:=(aI6 hcoord P).valuation_surjective F
 on_constants a ha := by
  let B:=DR k F
  rw [zG3 k k[X] F,
   zG3 k[X] B F]
  apply (aI6 hcoord P).valuation_eq_one_iff_notMem.mpr
  have :P.val.IsPrime :=P.property.1
  exact P.val.notMem_of_isUnit
   (((isUnit_iff_ne_zero.mpr ha).map (algebraMap k k[X])).map (algebraMap k[X] B))
private theorem eN6 (hcoord:coordinate k F≠0) (P:aBi k F) :
  (bt3 hcoord P).value (coordinate k F)<1 := by
 have :P.val.LiesOver (origin k) :=P.property.2
 change (aI6 hcoord P).valuation F (algebraMap k[X] F z7y)<1
 rw [zG3 k[X] (DR k F) F]
 exact ((aI6 hcoord P).valuation_lt_one_iff_mem _).mpr
  ((P.val.mem_of_liesOver (origin k) z7y).mp (zCn (by simp)))
private theorem bci (hcoord:coordinate k F≠0) (p:CurvePlace k F)
   (hu:p.value (coordinate k F)<1) :
   (bt3 hcoord (bmN p hu)).value=p.value := by
 let Q:=aI6 hcoord (bmN p hu)
 have hle :Q.valuationSubringAtPrime F≤p.value.valuationSubring := by
   rintro z ⟨a,b,hb,rfl⟩
   change p.value ((a :F)*(b:F)⁻¹)≤1
   have hb' : ¬ p.value (b:F)<1 := fun h=>hb ((bsx p hu b).mpr h)
   have hbound (c:DR k F) :p.value (c:F)≤1 :=
     (b9T p hu c).property
   have hval :p.value (b:F)=1 :=le_antisymm (hbound b) (not_lt.mp hb')
   rw [map_mul,map_inv₀,hval,inv_one,mul_one]
   exact hbound a
 have hproper :p.value.valuationSubring ≠ ⊤ := by
   intro ht
   obtain ⟨a,ha⟩:=p.normalized (exp 1)
   have hm:a∈p.value.valuationSubring := by rw [ht]; trivial
   exact (not_le_of_gt (show 1<p.value a by simp [ha])) hm
 have h:=ValuationSubring.eq_of_le_of_ne_top _ hle hproper
 rw [Q.valuationSubringAtPrime_eq_valuationSubring] at h
 exact eFr (Q.valuation_surjective F) p.normalized
   ((Valuation.isEquiv_iff_valuationSubring _ _).mpr h)
def aEh (x :F) (hx :x≠0) (hu:coordinate k F=x⁻¹)
    (P:aBi k F) :bkT k F x :=
  let hcoord:coordinate k F≠0:=hu ▸ inv_ne_zero hx
  ⟨bt3 hcoord P,(c4D hx).mpr (hu ▸ eN6 hcoord P)⟩
theorem eN7 (x :F) (hx :x≠0) (hu:coordinate k F=x⁻¹) :
   Function.Bijective (aEh x hx hu) := by
 let hcoord:coordinate k F≠0:=hu ▸ inv_ne_zero hx
 constructor
 · intro P Q h
   apply Subtype.ext
   have hv : (aI6 hcoord P).valuation F=(aI6 hcoord Q).valuation F :=
     congrArg (fun p:bkT k F x=>p.val.value) h
   exact congrArg HeightOneSpectrum.asIdeal (HeightOneSpectrum.valuation_injective F hv)
 · rintro ⟨p,hp⟩
   have hsmall:p.value (coordinate k F)<1 :=hu.symm ▸ (c4D hx).mp hp
   refine ⟨bmN p hsmall,Subtype.ext ?_⟩
   have h:=bci hcoord p hsmall
   change bt3 hcoord (bmN p hsmall)=p
   generalize bt3 hcoord (bmN p hsmall)=q at h ⊢
   cases q
   cases p
   cases h
   rfl
theorem eN8 (x :F) (hx :x≠0) (hu:coordinate k F=x⁻¹)
  (P:aBi k F) :
  poleOrder (aEh x hx hu P).val.value x=P.val.ramificationIdx k[X] := by
 let hcoord:coordinate k F≠0:=hu ▸ inv_ne_zero hx
 let Q:=aI6 hcoord P
 let B:=DR k F
 let b:=algebraMap k[X] B z7y
 have hb:b≠0:= by
  intro hb
  apply hcoord
  rw [coordinate,zG3 k[X] B F]
  change algebraMap B F b=0
  rw [hb,map_zero]
 have hspan: (origin k).map (algebraMap k[X] B)=zye {b} := by
  rw [origin,zlN,zyk]
 have :P.val.IsPrime :=P.property.1
 have :P.val.LiesOver (origin k) :=P.property.2
 have he :=Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (origin k) P.val (by
  rw [hspan,Ne,Ideal.span_singleton_eq_bot]
  exact hb)
 rw [hspan] at he
 change poleOrder (Q.valuation F) x= _
 have hx' : x=(algebraMap B F b)⁻¹:= by
  rw [← zG3 k[X] B F,← coordinate,hu,inv_inv]
 rw [hx',poleOrder,map_inv₀,Q.valuation_of_algebraMap,Q.intValuation_eq_exp_neg_multiplicity hb]
 simp only [log_inv,log_exp,neg_neg,Int.toNat_natCast]
 change multiplicity P.val (zye {b})= _
 exact he.symm
end B6
end
end aZc
end
section
set_option backward.isDefEq.respectTransparency false
namespace axk
noncomputable section
open Algebra
open E7 (CurveField)
open K1_14_2_2_7_3_3 (bGB)
open aeF (Os toFunction)
open XX (ad4)
open scoped Polynomial nonZeroDivisors IntermediateField.algebraAdjoinAdjoin
theorem affine_curve_field {k A:Type} [zrb k] [za6 A] [ztn A]
  [zZE k A] [zUK k A] (hdim:ringKrullDim A=1) :
  CurveField k (FractionRing A) := by
 have h:za8 k A:= by
  rw [Algebra.transcendental_iff_not_isAlgebraic]
  intro h
  let:zVK k A:=⟨fun a=>(h.1 a).isIntegral⟩
  have hf :IsField A:=isField_of_isIntegral_of_isField' (Field.toIsField k)
  exact zero_ne_one ((ringKrullDim_eq_zero_of_isField hf).symm.trans hdim)
 obtain ⟨a,ha⟩:=h.transcendental
 have ht:Transcendental k (toFunction a) :=
  (transcendental_algebraMap_iff (zxb A (FractionRing A))).2 ha
 exact ⟨toFunction a,ht,bGB hdim ht⟩
variable {k F:Type} [zrb k] [zrb F] [zZE k F]
private theorem bZj (h:CurveField k F) :trdeg k F=1 := by
 obtain ⟨t,ht,hfin⟩:=h
 let B:=zum k ({t} : Set F)
 let T:=IntermediateField.adjoin k ({t} : Set F)
 let:zAa T F:=hfin
 have hB:zjH B F:=Algebra.IsAlgebraic.trans B T F
 have hi:AlgebraicIndependent k (fun _:Unit=>t) :=
   (algebraicIndependent_singleton_iff ()).2 ht
 have hb:=hi.isTranscendenceBasis_iff_isAlgebraic.mpr
   (show zjH (zum k (zxp (fun _:Unit=>t))) F by
     rwa [Set.range_const])
 simpa using hb.cardinalMk_eq_trdeg.symm
private theorem dR2 [zl5 k F] (h:trdeg k F=1) :
  CurveField k F:= by
 have htrans :za8 k F :=
  trdeg_ne_zero_iff.mp (h.trans_ne one_ne_zero)
 obtain ⟨t,ht⟩:=htrans.transcendental
 have hi:AlgebraicIndependent k (fun _:Unit=>t) :=
  (algebraicIndependent_singleton_iff ()).2 ht
 have hb:=hi.isTranscendenceBasis_of_trdeg_le_of_finite (by simp [h])
 let E :=IntermediateField.adjoin k ({t} : Set F)
 have hrange :zxp (fun _:Unit=>t) = {t} := Set.range_const
 let:zjH E F:=Eq.mp
  (congrArg (fun s=>zjH (IntermediateField.adjoin k s) F) hrange)
  hb.isAlgebraic_field
 have :zl5 E F:=z9q k E F
 exact ⟨t,ht,zNf⟩
private theorem cew (E :Type) [zrb E] :trdeg E (RatFunc E)=1 := by
 have :zjH E[X] (RatFunc E) :=
  zyQ _ E[X]⁰
 have :FaithfulSMul E[X] (RatFunc E) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (zxb _ _)
 simpa [Polynomial.trdeg_of_isDomain,trdeg_eq_zero (R:=E[X]) (A:=RatFunc E)] using
  (trdeg_add_eq (A:=RatFunc E) E E[X]).symm
private theorem fTu (E :Type) [zrb E] :
  zl5 E (RatFunc E) := by
 let:zl5 E[X] (RatFunc E) :=
  zrU (RatFunc E) E[X]⁰
 exact zQi E E[X] (RatFunc E)
attribute [local instance] Polynomial.algebra
theorem eKW (h:CurveField k F) :
    letI:=Os k (F:=F)
    CurveField (RatFunc k) (RatFunc F) := by
  let:zZE (RatFunc k) (RatFunc F) :=Os k (F:=F)
  have :zsf k (RatFunc k) (RatFunc F) :=
    zsL fun a=> by
      simp only [zG3 k k[X] (RatFunc k),
        zG3 k F (RatFunc F),
        zG3 F F[X] (RatFunc F),
        ad4]
      change algebraMap F[X] (RatFunc F) (z1z (algebraMap k F a)) =
        algebraMap F[X] (RatFunc F) ((z1z a).map (algebraMap k F))
      rw [zrL]
  have htr :=bZj h
  obtain ⟨t,_,hfin⟩:=h
  let T:=IntermediateField.adjoin k ({t} : Set F)
  let:zAa T F:=hfin
  have :zl5 k T:=IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton t))
  have :zl5 k F:=zQi k T F
  have :=fTu F
  have :zl5 k (RatFunc F) :=zQi k F (RatFunc F)
  have :zl5 (RatFunc k) (RatFunc F) :=
    z9q k (RatFunc k) (RatFunc F)
  have hrank :trdeg k (RatFunc F)=(1 :Cardinal)+1 := by
    rw [← trdeg_add_eq (A:=RatFunc F) k F,htr,cew F]
  apply dR2
  apply Cardinal.add_one_inj.mp
  rw [add_comm (trdeg (RatFunc k) (RatFunc F)),← cew k,
    trdeg_add_eq (A:=RatFunc F) k (RatFunc k),hrank,cew k]
end
end axk
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace XX
noncomputable section
open aeF (aB6 FZ Os)
open E7 (CurvePlace poleOrder)
open scoped BigOperators Polynomial WithZero
def c1 :Prop :=
  ∀ (k F:Type) [zrb k] [zrb F] [zZE k F] (t x :F),
    aB6 k t→Transcendental k x →
    FiniteDimensional (IntermediateField.adjoin k {x}) F ∧
      zAa k[X] (ach (k :=k) x)
def c2 :Prop :=
  ∀ (k F:Type) [zrb k] [zrb F] [zZE k F] (x :F),
    Transcendental k x→FiniteDimensional (IntermediateField.adjoin k {x}) F →
    zAa k[X] (ach (k :=k) x) →
    (fun p:CurvePlace k F=>poleOrder p.value x).HasFiniteSupport ∧
      (∀ p:CurvePlace k F,poleOrder p.value x≠0 →
        FiniteDimensional k (EO p)) ∧
      aFr (k :=k) x=FZ k x
def c3:Prop :=
  ∀ (k F:Type) [zrb k] [zrb F] [zZE k F] (t:F),
    aB6 k t →
    letI:=Os k (F:=F)
    aB6 (RatFunc k) (RatFunc.C t)
def c4 :Prop :=
  ∀ (k F:Type) [zrb k] [zrb F] [zZE k F] (p:CurvePlace k F),
    FiniteDimensional k (EO p) →
    letI:=Os k (F:=F)
    ∀ q:CurvePlace (RatFunc k) (RatFunc F),OG p q →
      placeWeight q=placeWeight p
def c5:Prop :=
  ∀ (k F:Type) [zrb k] [zrb F] [zZE k F],
    (∀ p:CurvePlace k F,FiniteDimensional k (EO p)) →
    letI:=Os k (F:=F)
    ∀ q:CurvePlace (RatFunc k) (RatFunc F),
      (∀ x :F,q.value (RatFunc.C x)≤1) ∨ ∃ p:CurvePlace k F,OG p q
section ak7
variable {k F:Type} [zrb k] [zrb F] [zZE k F]
end ak7
section Pencil
variable {k F:Type} [zrb k] [zrb F] [zZE k F]
local instance :zZE (RatFunc k) (RatFunc F) :=Os k (F:=F)
end Pencil
end
end XX
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace baB
noncomputable section
open gT ac4
open scoped nonZeroDivisors
abbrev Parameters (k :Type) [zrb k] :=z3y (Fin 2) k
abbrev Ambient (R:Type) [za6 R] :=z3y (Fin 4) R
variable {k :Type} [zrb k]
def Yn (H :znc (Ambient k)) (g h:Ambient k) :zM1 (gk H) :=
 z1z (zVv H g)+Polynomial.X*z1z (zVv H h)
def pD (H :znc (Ambient k)) (g h:Ambient k) :
    Parameters k →+* zM1 (gk H) :=
  zOD (Polynomial.C.comp (algebraMap k (gk H)))
    ![z7y,Yn H g h]
@[simp] theorem btq (H :znc (Ambient k)) (g h:Ambient k) (a :k) :
   pD H g h (znf a)=z1z (algebraMap k (gk H) a) := by
  simp [pD]
@[simp] theorem cbh (H :znc (Ambient k)) (g h:Ambient k) :
   pD H g h (z9v 0)=Polynomial.X:= by simp [pD]
@[simp] theorem bKf (H :znc (Ambient k)) (g h:Ambient k) :
   pD H g h (z9v 1)=Yn H g h:= by simp [pD]
def a3W {R:Type} [za6 R] (f :k →+* R) (s t:R) (g h:Ambient k) :
    Ambient R :=
  zDK f g+MvPolynomial.C s*zDK f h-MvPolynomial.C t
def TY (H :znc (Ambient k)) (g h:Ambient k) :znc (Ambient (CS k)) :=
  H.map (Cl k) ⊔ zye
    {a3W (algebraMap k (CS k)) (arW k 0) (arW k 1) g h}
private def CV:Ambient k →+* Ambient (Parameters k) :=
 zDK znf
private def aum (H :znc (Ambient k)) (g h:Ambient k) :
  znc (Ambient (Parameters k)) :=
 H.map CV ⊔ zye
  {a3W znf (z9v 0) (z9v 1) g h}
private def wW (H :znc (Ambient k)) (g h:Ambient k) :
  Ambient (Parameters k) →+* zM1 (gk H) :=
 zOD (pD H g h)
  (fun i=>z1z (zVv H (z9v i)))
private theorem ax8 (H :znc (Ambient k)) (g h:Ambient k) :
   (wW H g h).comp CV=Polynomial.C.comp (zVv H) := by
 apply zXT
 · intro a
   simp [CV,wW]
   rfl
 · intro i
   simp [CV,wW]
private theorem a1C (H :znc (Ambient k)) (g h:Ambient k) :
   zpX (wW H g h) := by
 intro p
 induction p using Polynomial.induction_on' with
 | add p q hp hq =>
   obtain ⟨p',rfl⟩:=hp
   obtain ⟨q',rfl⟩:=hq
   exact ⟨p' + q',map_add _ _ _⟩
 | monomial n a =>
   obtain ⟨b,rfl⟩:=zld (I:=H) a
   refine ⟨CV b*znf (z9v 0)^n,?_⟩
   rw [map_mul,map_pow,← zQb,ax8,zQb]
   rw [show wW H g h (znf (z9v 0))=z7y by
    simp [wW],Polynomial.C_mul_X_pow_eq_monomial]
private theorem bb3 (H :znc (Ambient k)) (g h:Ambient k) :
    aum H g h=zdq (wW H g h) := by
  let D:=aum H g h
  let q:=zVv D
  have hD:D ≤zdq (wW H g h) := by
    apply sup_le
    · rw [zo0,zEW,ax8]
      intro p hp
      exact RingHom.mem_ker.mpr (by simp [Ideal.Quotient.eq_zero_iff_mem.mpr hp])
    · apply (zvl _).mpr
      apply RingHom.mem_ker.mpr
      have he (p:Ambient k) :wW H g h (CV p) =
          z1z (zVv H p) :=zLs (ax8 H g h) p
      simp only [a3W,map_sub,map_add,map_mul,← show CV=zDK
        (znf:k →+* Parameters k) from rfl,he]
      rw [show wW H g h (znf (z9v 0))=z7y by
          simp [wW],
        show wW H g h (znf (z9v 1))=Yn H g h by
          simp [wW],Yn,sub_self]
  let u:gk H →+* Ambient (Parameters k) ⧸ D :=
    zP2 H (q.comp CV)
      (fun a ha=>Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_left (z7X CV ha)))
  let v :zM1 (gk H) →+* Ambient (Parameters k) ⧸ D :=
    zqf u (q (znf (z9v 0)))
  have hrel :
      q (CV g)+q (znf (z9v 0))*q (CV h) =
        q (znf (z9v 1)) := by
    apply sub_eq_zero.mp
    simp only [← map_mul,← map_add,← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_right (z5J _))
  have he :v.comp (wW H g h)=q:= by
    apply zXT
    · have hC: (v.comp (wW H g h)).comp znf=q.comp MvPolynomial.C:= by
        apply zXT
        · intro a
          simp only [zQb,wW,zTv,btq,
            v,z4Q,zJU]
          rw [← zOY (R₁:=k) H a]
          simp only [u,z0R,zQb,CV,
            MvPolynomial.algebraMap_eq,zpw]
        · intro i
          simp only [zQb,wW,zTv]
          fin_cases i
          · change v (pD H g h (z9v 0))= _
            simp [v]
          · change v (pD H g h (z9v 1))= _
            simp only [bKf,Yn,map_add,map_mul,v,
              z4Q,zJU,Polynomial.eval₂_X,u,
              z0R,zQb]
            exact hrel
      exact zLs hC
    · intro i
      simp only [zQb,wW,MvPolynomial.eval₂Hom_X',v,
        z4Q,zJU,u,z0R,
        CV,z7N]
  refine le_antisymm hD fun a ha=>Ideal.Quotient.eq_zero_iff_mem.mp ?_
  have ha' := zLs he a
  rw [zQb,RingHom.mem_ker.mp ha,map_zero] at ha'
  exact ha'.symm
attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem bse (H :znc (Ambient k)) (g h:Ambient k) :
    (aum H g h).map
        (algebraMap (Ambient (Parameters k)) (Ambient (CS k)))=TY H g h:= by
  rw [aum,Ideal.map_sup,z0L,zlN,zyk]
  change H.map ((zDK (algebraMap (Parameters k) (CS k))).comp CV) ⊔
      zye {zDK (algebraMap (Parameters k) (CS k))
        (a3W znf (z9v 0) (z9v 1) g h)} = _
  rw [TY]
  have hcomp: (zDK (algebraMap (Parameters k) (CS k))).comp CV =
      Cl k := by
    apply zXT <;> intro a <;> simp [CV,Cl]
    rfl
  rw [hcomp]
  simp only [a3W,map_sub,map_add,map_mul,zpw,arW,
    MvPolynomial.map_map]
  rfl
abbrev cbk (H :znc (Ambient k)) (g h:Ambient k) :ℕ :=
 @zsE (Parameters k) (zM1 (gk H)) _ _
   (pD H g h).toAlgebra.toModule
set_option backward.isDefEq.respectTransparency true in
theorem cRS (H :znc (Ambient k)) (g h:Ambient k) :
   zsE (CS k) (gk (TY H g h)) =
     cbk H g h:= by
 let R:=Parameters k
 let S:=CS k
 let D:=zM1 (gk H)
 let B:=gk (TY H g h)
 let f :=wW H g h
 let q:=zVv (TY H g h)
 let:zZE (Ambient R) (Ambient S) :=MvPolynomial.algebraMvPolynomial
 let M:Submonoid (Ambient R) :=R⁰.map znf
 let:zNo M (Ambient S) :=MvPolynomial.isLocalization R⁰ S
 let aRD:zZE R D:=(pD H g h).toAlgebra
 let:Module R D:=aRD.toModule
 let:SMul R D:=aRD.toSMul
 have hk :zdq q=(zdq f).map (algebraMap (Ambient R) (Ambient S)) := by
   rw [Ideal.mk_ker,← bb3 H g h,bse]
 let q' : { p:Ambient R →+* B // zdq f≤zdq p } :=
   ⟨q.comp (algebraMap (Ambient R) (Ambient S)),by
     rw [← zEW,hk]
     exact Ideal.le_comap_map⟩
 let φ:D →+* B:=f.liftOfSurjective (a1C H g h) q'
 have hφ:φ.comp f=q.comp (algebraMap (Ambient R) (Ambient S)) :=
   f.liftOfSurjective_comp (a1C H g h) q'
 let aDB:zZE D B:=φ.toAlgebra
 let:SMul D B:=aDB.toSMul
 let aRB:zZE R B:=((algebraMap S B).comp (algebraMap R S)).toAlgebra
 let:Module R B:=aRB.toModule
 let:SMul R B:=aRB.toSMul
 let:zsf R S B:=zsL fun _=>rfl
 let:zsf R D B:=zsL fun a=> by
   change q (znf (algebraMap R S a))=φ (pD H g h a)
   have ht:=zLs hφ (znf a)
   change φ (wW H g h (znf a)) =
     q (zDK (algebraMap R S) (znf a)) at ht
   simpa only [wW,zTv,zpw] using ht.symm
 have hloc:zNo (M.map f) B :=
   IsLocalization.of_surjective M (Ambient S) f (a1C H g h) q
     zld hφ.symm hk.le
 have hparams : (M.map f)=zTz D R⁰:= by
   change (R⁰.map (znf (σ:=Fin 4)).toMonoidHom).map f.toMonoidHom =
     R⁰.map (pD H g h).toMonoidHom
   rw [Submonoid.map_map]
   congr 1
   apply MonoidHom.ext
   intro a
   exact zTv _ _ _
 let:zNo (zTz D R⁰) B:=hparams ▸ hloc
 exact (IsFractionRing.finrank_right_eq R S B).trans
   (IsLocalizedModule.finrank_eq R⁰ (zE2 R D B).toLinearMap le_rfl)
end
end baB
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace cy8
open cu gT OH aiM MvPolynomial
open scoped Polynomial RatFunc TensorProduct
noncomputable section
attribute [local instance] Polynomial.algebra
private abbrev E :=RatFunc aQ
private abbrev D:=z3y (Fin 2) E
private abbrev B:=zM1 aQ
private def bc0:E :=RatFunc.C (ek 1) - RatFunc.C (ek 0)*RatFunc.X
private def aXB:aZ →+* zM1 aZ :=
 eval₂Hom (Polynomial.C.comp C)
  ![z1z (z9v 1)-Polynomial.C (z9v 0)*z7y,z7y]
private def cqj:zM1 aZ →+* aZ :=
 zqf (eval₂Hom C ![0,z9v 0]) (z9v 1)
private theorem gow:zq4 aXB:= by
 have h:cqj.comp aXB=RingHom.id aZ:= by
  apply zXT
  · intro a
    simp [aXB,cqj]
  · intro i
    fin_cases i <;> simp [aXB,cqj]
 exact Function.LeftInverse.injective (zLs h)
private def bNL:aZ →+* E :=
 (algebraMap B E).comp ((zhd (algebraMap aZ aQ)).comp aXB)
private def IL:aQ →+* E :=
 zIj (g:=bNL) ((zxb B E).comp
  ((zTo _ (zxb aZ aQ)).comp
    gow))
private theorem coW (c:FX) :
  IL (algebraMap FX aQ c)=RatFunc.C (algebraMap FX aQ c) := by
 change IL (algebraMap aZ aQ (C c))= _
 rw [IL,zoc]
 simp [bNL,aXB,RatFunc.algebraMap_C]
 rfl
private theorem gn0:IL (ek 0)=bc0:= by
 rw [ek,IL,zoc]
 simp [bNL,aXB,bc0,ek,RatFunc.algebraMap_C,
  RatFunc.algebraMap_X]
private theorem gnZ:IL (ek 1)=RatFunc.X:= by
 rw [ek,IL,zoc]
 simp [bNL,aXB,RatFunc.algebraMap_X]
private def beb:Ambient →+* D:=(zDK IL).comp Dk
private def ajs :N8 →+* D :=
 eval₂Hom (C.comp RatFunc.C) ![C bc0,C RatFunc.X,z9v 0,z9v 1]
private theorem cIW:ajs.comp Q6=beb:= by
 apply zXT
 · intro c
   simp [ajs,Q6,beb,Dk,coW]
 · intro i
   fin_cases i <;> simp [ajs,Q6,beb,Dk,
    gn0,gnZ]
private theorem dSp:ajs (B4 0 1)=0:= by
 simp [ajs,B4,bc0,map_sub,map_mul,map_add,sub_add_cancel]
private abbrev TY (I:znc Ambient) :znc D:=I.map beb
private abbrev aiB (I:znc Ambient) :=D ⧸ TY I
private abbrev F (I:znc Ambient) :=Gd aQ (rM I) (zL I 1)
private local instance gRr (I:znc Ambient) :zZE B (rM I) :=
 (zEU (zL I 1) :B →ₐ[aQ] rM I).toRingHom.toAlgebra
private local instance gAB (I:znc Ambient) :zZE B (aiB I) :=
 Algebra.compHom (aiB I) (algebraMap B E)
private local instance gRT (I:znc Ambient) :
  @zsf B E (aiB I) (show zZE B E from inferInstance).toSMul
    (show zZE E (aiB I) from inferInstance).toSMul (gAB I).toSMul :=
 IsScalarTower.of_algebraMap_eq' rfl
private def bhX (I:znc Ambient) :rM I →+* aiB I :=
 zP2 (Cr I) ((zVv (TY I)).comp ajs) <| by
  change Cr I≤zdq _
  apply sup_le
  · rw [zo0]
    intro a ha
    change zVv (TY I) ((ajs.comp Q6) a)=0
    rw [zLs cIW a]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (z7X _ ha)
  · rw [zvl]
    change zVv (TY I) (ajs (B4 0 1))=0
    rw [dSp,map_zero]
private theorem cts (I:znc Ambient) (p:N8) :
  bhX I (zVv (Cr I) p)=zVv (TY I) (ajs p) :=
 rfl
private def dhk (I:znc Ambient) :rM I →ₐ[B] aiB I :=
  { bhX I with
    commutes' := by
      have h: (bhX I).comp (algebraMap B (rM I))=algebraMap B (aiB I) := by
        apply z86
        · intro c
          change bhX I (zEU (zL I 1) (z1z c)) =
            algebraMap E (aiB I) (algebraMap B E (z1z c))
          rw [z8q,RatFunc.algebraMap_C]
          change bhX I (zVv (Cr I) (C c))= _
          rw [cts]
          simp only [ajs,eval₂Hom_C,zQb]
          rfl
        · change bhX I (zEU (zL I 1) z7y) =
            algebraMap E (aiB I) (algebraMap B E z7y)
          rw [zw0,RatFunc.algebraMap_X,zL,cts]
          simp only [ajs,eval₂Hom_X']
          rfl
      exact zLs h }
private def bOW (I:znc Ambient) :F I →ₐ[E] aiB I :=
 AlgHom.liftEquiv B E (rM I) (aiB I) (dhk I)
private def inc (I:znc Ambient) :N8 →+* F I :=
 (zgi (R:=B) (A:=E) (B:=rM I)).toRingHom.comp
   (zVv (Cr I))
private theorem cU0 (I:znc Ambient) (p:N8) (hp:p∈Cr I) :
  inc I p=0:= by
 let right:=zgi (R:=B) (A:=E) (B:=rM I)
 change right (zVv (Cr I) p)=0
 rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp,map_zero]
private theorem cUY (I:znc Ambient) (c:aQ) :
  inc I (C c)=algebraMap E (F I) (RatFunc.C c) := by
 let right:=zgi (R:=B) (A:=E) (B:=rM I)
 have h:=right.commutes (z1z c)
 change right (zEU (zL I 1) (z1z c)) =
  algebraMap E (F I) (algebraMap B E (z1z c)) at h
 rw [z8q,RatFunc.algebraMap_C] at h
 exact h
private theorem cUZ (I:znc Ambient) :inc I (z9v 1)=algebraMap E (F I) RatFunc.X:= by
 let right:=zgi (R:=B) (A:=E) (B:=rM I)
 have h:=right.commutes (z7y:B)
 change right (zEU (zL I 1) z7y) =
  algebraMap E (F I) (algebraMap B E z7y) at h
 rw [zw0,RatFunc.algebraMap_X] at h
 exact h
private theorem enT (I:znc Ambient) :inc I (z9v 0)=algebraMap E (F I) bc0:= by
 have hle :zye {B4 0 1} ≤ Cr I:=le_sup_right
 have h:=cU0 I (B4 0 1) (hle (zCn (by simp)))
 simp only [B4,map_sub,map_add,map_mul,cUY,cUZ] at h
 rw [bc0,map_sub,map_mul,eq_sub_iff_add_eq,← sub_eq_zero]
 exact h
private def yZ (I:znc Ambient) :D →ₐ[E] F I :=
 aeval ![inc I (z9v 2),inc I (z9v 3)]
private theorem cVO (I:znc Ambient) :
   (yZ I).toRingHom.comp ajs=inc I:= by
 apply zXT
 · intro c
   simp [ajs,yZ,cUY]
 · intro i
   fin_cases i <;>
     simp [ajs,yZ,enT,cUZ]
private def bG2 (I:znc Ambient) :aiB I →ₐ[E] F I :=
 { zP2 (TY I) (yZ I).toRingHom (by
    change I.map beb≤zdq (yZ I).toRingHom
    rw [zo0]
    intro p hp
    change yZ I (beb p)=0
    rw [← zLs cIW p]
    change ((yZ I).toRingHom.comp ajs) (Q6 p)=0
    rw [cVO]
    have hle :I.map Q6≤Cr I:=le_sup_left
    exact cU0 I (Q6 p) (hle (z7X _ hp))) with
   commutes' := fun c=>(yZ I).commutes c }
private theorem cTf (I:znc Ambient) (p:D) :
  bG2 I (zVv (TY I) p)=yZ I p :=
 rfl
private theorem dhl (I:znc Ambient) (p:N8) :
  bOW I (inc I p)=zVv (TY I) (ajs p) := by
 have h:=AlgHom.congr_fun
  ((AlgHom.liftEquiv B E (rM I) (aiB I)).left_inv (dhk I))
  (zVv (Cr I) p)
 exact h.trans (cts I p)
private def bp4 (I:znc Ambient) :F I ≃ₐ[E] aiB I :=
 AlgEquiv.ofAlgHom (bOW I) (bG2 I) (by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j <;>
    simp [cTf,yZ,dhl,ajs]) (by
  apply AlgHom.coe_ringHom_injective
  apply Algebra.TensorProduct.ringHom_ext (R:=B) (A:=E) (B:=rM I)
  · apply zz4
    intro c
    exact ((bG2 I).comp (bOW I)).commutes c
  · apply Ideal.Quotient.ringHom_ext
    apply zz4
    intro p
    change bG2 I (bOW I (inc I p))=inc I p
    rw [dhl,cTf]
    exact zLs (cVO I) p)
theorem proof :aiM.c1 := by
 intro I
 let:zZE aQ E :=IL.toAlgebra
 let e :E ⊗[aQ] Y0 I ≃ₐ[E] aiB I :=
   (czE.aPw (E :=E) (I.map Dk)).trans
     (z9k E (z0L _ _))
 exact (bp4 I).toLinearEquiv.finrank_eq.trans
   (e.toLinearEquiv.finrank_eq.symm.trans Module.finrank_baseChange)
end
end cy8
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
namespace bzU
noncomputable section
open OH (ak7 aHf bfe)
open aeF (aB6 ajJ Os)
open XX (c1 c2 c3 c4 c5 OG EO bdy placeWeight
 aFr ad4)
open E7 (CurvePlace poleOrder)
open scoped BigOperators Polynomial RatFunc WithZero
attribute [local instance] Polynomial.algebra
section Degrees
variable {k F:Type} [zrb k] [zrb F] [zZE k F]
private theorem cJV (a :F) :
  OH.FZ k F a=aeF.FZ k a := by
 classical
 by_cases h:IsAlgebraic k a <;>
  simp [OH.FZ,aeF.FZ,Transcendental,h]
private theorem gpN (ell:ℕ) [CharP k ell] (a :F)
   (hpos :0<OH.FZ k F a)
   (hsmall:OH.FZ k F a<ell) :
   aB6 k a := by
 classical
 have htr :Transcendental k a := by
   by_contra h
   simp [OH.FZ,h] at hpos
 rw [OH.FZ,ite_eq_left htr] at hpos hsmall
 let E :=IntermediateField.adjoin k ({a} : Set F)
 let:FiniteDimensional E F:=Module.finite_of_finrank_pos hpos
 let:CharP E ell:=charP_of_injective_ringHom (algebraMap k E).injective ell
 have hell:0<ell:=hpos.trans hsmall
 let:Fact ell.Prime :=⟨(CharP.char_is_prime_or_zero E ell).resolve_right hell.ne'⟩
 refine ⟨htr,inferInstanceAs (FiniteDimensional E F),?_⟩
 obtain ⟨n,hn⟩:=finInsepDegree_eq_pow E F ell
 apply (isSeparable_iff_finInsepDegree_eq_one E F).mpr
 cases n with
 | zero=>simpa using hn
 | succ n =>
   have hle :ell≤ell^(n+1) := by
     rw [pow_succ']
     exact Nat.le_mul_of_pos_right _ (pow_pos hell _)
   have hdvd:ell^(n+1)∣zsE E F:= by
     rw [← hn,← Field.finSepDegree_mul_finInsepDegree E F]
     exact dvd_mul_left _ _
   exact (not_lt_of_ge (hle.trans (Nat.le_of_dvd hpos hdvd)) hsmall).elim
private theorem bPm:Monotone (fun a :ℤᵐ⁰=>(WithZero.log a).toNat) := by
 intro a b hab
 by_cases ha :a=0
 · simp [ha]
 · exact z0Z ((WithZero.log_le_log ha
    (ne_of_gt ((WithZero.pos_iff_ne_zero.mpr ha).trans_le hab))).mpr hab)
private theorem pole_add (p:CurvePlace k F) (a b:F) :
  poleOrder p.value (a+b)≤ max (poleOrder p.value a) (poleOrder p.value b) := by
 unfold poleOrder
 exact (bPm (p.value.map_add a b)).trans bPm.map_max.le
private theorem pole_mul (p:CurvePlace k F) (a b:F) :
   poleOrder p.value (a*b)≤poleOrder p.value a+poleOrder p.value b:= by
 unfold poleOrder
 obtain rfl | ha :=eq_or_ne a 0
 · simp
 obtain rfl | hb:=eq_or_ne b 0
 · simp
 rw [map_mul,WithZero.log_mul (by simpa using ha) (by simpa using hb)]
 omega
private theorem pole_scalar (p:CurvePlace k F) (c:k) :
   poleOrder p.value (algebraMap k F c)=0:= by
 obtain rfl | hc:=eq_or_ne c 0
 · simp [poleOrder]
 · simp [poleOrder,p.on_constants c hc]
private theorem eMP (p:CurvePlace k F) {a :F} (ha :p.value a≤1) :
  poleOrder p.value a=0 :=
 za7 (by simpa [poleOrder] using bPm ha)
private theorem poles_and_degree (h1 :c1) (h2 :c2) (t:F)
    (ht:aB6 k t) (a :F) :
    (fun p:CurvePlace k F=>poleOrder p.value a).HasFiniteSupport ∧
      (∀ p:CurvePlace k F,poleOrder p.value a≠0→FiniteDimensional k (EO p)) ∧
      aFr (k :=k) a=aeF.FZ k a := by
  by_cases ha :IsAlgebraic k a
  · have hp (p:CurvePlace k F) :poleOrder p.value a=0:= by
      let:p.value.IsTrivialOn k :=⟨p.on_constants⟩
      obtain rfl | hne :=eq_or_ne a 0
      · simp [poleOrder]
      · have hv :p.value a=1 := by
          by_contra h
          exact (Valuation.transcendental_of_ne_one k a hne h) ha
        simp [poleOrder,hv]
    refine ⟨?_,fun p h=>(h (hp p)).elim,?_⟩
    · simp [Function.HasFiniteSupport,Function.support,hp]
    · simp [aFr,aeF.FZ,ha,hp]
  · obtain ⟨hfinite,hchart⟩:=h1 k F t a ht ha
    exact h2 k F a ha hfinite hchart
private theorem bu6 (h1 :c1) (h2 :c2) (t:F)
  (ht:aB6 k t) (p:CurvePlace k F) :
  FiniteDimensional k (EO p) := by
 obtain ⟨a,ha⟩:=p.normalized (WithZero.exp 1)
 exact (poles_and_degree h1 h2 t ht a).2.1 p (by simp [poleOrder,ha])
end Degrees
section Pencil
variable {k F:Type} [zrb k] [zrb F] [zZE k F]
private theorem eKT :
    Os k (F:=F)=(inferInstance :zZE (RatFunc k) (RatFunc F)) := by
  apply Algebra.algebra_ext
  intro f
  have hpoly (P:k[X]) :
      @algebraMap (RatFunc k) (RatFunc F) _ _ (Os k (F:=F))
        (algebraMap k[X] (RatFunc k) P) =
      algebraMap (RatFunc k) (RatFunc F) (algebraMap k[X] (RatFunc k) P) := by
    rw [ad4,← zG3 k[X] (RatFunc k)
      (RatFunc F),zG3 k[X] F[X] (RatFunc F)]
    rfl
  induction f using RatFunc.induction_on with
  | _ P Q hQ =>
    change @algebraMap (RatFunc k) (RatFunc F) _ _ (Os k (F:=F)) _ =
      algebraMap (RatFunc k) (RatFunc F) _
    rw [map_div₀,map_div₀,hpoly,hpoly]
private theorem ewR {A:Type} [za6 A] [ztn A] [zZE k A] (y v :A) :
   bfe k A y v =
     ajJ k (algebraMap A (FractionRing A) y) (algebraMap A (FractionRing A) v) := by
 unfold bfe ajJ
 rw [eKT]
 exact cJV _
local instance :zZE (RatFunc k) (RatFunc F) :=Os k (F:=F)
private theorem bqw {p:CurvePlace k F} {q:CurvePlace (RatFunc k) (RatFunc F)}
   (h:OG p q) (a :F) :q.value (RatFunc.C a)=p.value a := by
 obtain rfl | ha :=eq_or_ne a 0
 · simp
 · simpa [zy1 ha] using h (z1z a)
private theorem btE {p q:CurvePlace k F} (h:p.value=q.value) :p=q:= by
 cases p
 cases q
 cases h
 rfl
private theorem b4w {p:CurvePlace k F} {q r :CurvePlace (RatFunc k) (RatFunc F)}
   (hq:OG p q) (hr :OG p r) :q=r := by
 apply btE
 apply Valuation.ext
 intro a
 induction a using RatFunc.induction_on with
 | _ P Q hQ=>rw [q.value.map_div,r.value.map_div,hq P,hq Q,hr P,hr Q]
private def qW (y v :F) :RatFunc F:=RatFunc.C y+RatFunc.X*RatFunc.C v
private theorem b4v {p:CurvePlace k F} {q:CurvePlace (RatFunc k) (RatFunc F)}
    (h:OG p q) (y v :F) :
    poleOrder q.value (qW y v)=max (poleOrder p.value y) (poleOrder p.value v) := by
  let P:F[X] :=z1z y+Polynomial.X*z1z v
  have hP:algebraMap F[X] (RatFunc F) P=qW y v := by
    simp only [P,qW,map_add,map_mul,RatFunc.algebraMap_C,RatFunc.algebraMap_X]
  have hc0:P.coeff 0=y := by simp [P]
  have hc1 :P.coeff 1=v := by simp [P]
  have hrest (i:ℕ) (hi:2≤ i) :P.coeff i=0:= by
    obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le hi
    simp [P,add_comm]
  have hmax :P.support.sup (fun i=>p.value (P.coeff i))=max (p.value y) (p.value v) := by
    apply le_antisymm
    · apply zf9
      intro i hi
      by_cases h0:i=0
      · simp [h0,hc0]
      by_cases h1 :i=1
      · simp [h1,hc1]
      · simp [hrest i (by omega)]
    · apply max_le
      · by_cases hy :y=0
        · simp [hy]
        · exact hc0 ▸ (zZi (f := fun i=>p.value (P.coeff i))
            (Polynomial.mem_support_iff.mpr (hc0.symm ▸ hy)))
      · by_cases hv :v=0
        · simp [hv]
        · exact hc1 ▸ (zZi (f := fun i=>p.value (P.coeff i))
            (Polynomial.mem_support_iff.mpr (hc1.symm ▸ hv)))
  unfold poleOrder
  rw [← hP,h P,hmax,bPm.map_max]
private theorem pencil_pole_degree (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5)
    (t:F) (ht:aB6 k t) (y v :F) :
    (∑ᶠ p:CurvePlace k F,placeWeight p*max (poleOrder p.value y) (poleOrder p.value v)) =
      ajJ k y v := by
  classical
  let lift (p:CurvePlace k F) :=(bdy p).choose
  have hlift (p:CurvePlace k F) :OG p (lift p) :=(bdy p).choose_spec
  have hinj:zq4 lift:= by
    intro p r he
    apply btE
    apply Valuation.ext
    intro a
    rw [← bqw (hlift p),← bqw (hlift r),he]
  let g (q:CurvePlace (RatFunc k) (RatFunc F)) :=placeWeight q*poleOrder q.value (qW y v)
  have hoff (q:CurvePlace (RatFunc k) (RatFunc F)) (hq:q∉zxp lift) :g q=0:= by
    rcases h5 k F (bu6 h1 h2 t ht) q with htriv | ⟨p,hp⟩
    · have hX:q.value (RatFunc.X:RatFunc F)=1 := by
        have halg:algebraMap (RatFunc k) (RatFunc F) RatFunc.X=RatFunc.X:= by
          simpa only [Polynomial.map_X,RatFunc.algebraMap_X] using
            (ad4 (k :=k) (F:=F) z7y)
        rw [← halg]
        exact q.on_constants _ RatFunc.X_ne_zero
      have hle :q.value (qW y v)≤1 := by
        unfold qW
        apply (q.value.map_add _ _).trans
        rw [map_mul,hX,one_mul]
        exact max_le (htriv y) (htriv v)
      simp [g,eMP q hle]
    · exact (hq ⟨p,b4w (hlift p) hp⟩).elim
  have hsupp:Function.support g⊆zxp lift:= by
    intro q hq
    by_contra h
    exact hq (hoff q h)
  have hsum: (∑ᶠ q,g q) = ∑ᶠ q∈zxp lift,g q:= by
    rw [← finsum_mem_support g]
    apply finsum_mem_inter_support_eq'
    intro q hq
    simp [hq,hsupp hq]
  calc
    _ = ∑ᶠ p,g (lift p) := by
      apply finsum_congr
      intro p
      simp only [g,b4v (hlift p),h4 k F p (bu6 h1 h2 t ht p) _ (hlift p)]
    _ = ∑ᶠ q∈zxp lift,g q:=(finsum_mem_range hinj).symm
    _=aFr (k :=RatFunc k) (qW y v) :=hsum.symm
    _=ajJ k y v :=(poles_and_degree h1 h2 _ (h3 k F t ht) _).2.2
end Pencil
theorem eFW (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) :
    OH.c3:= by
  classical
  intro ell k A _ _ _ _ _ hfinite _ x y v hx hsmall
  let F:=FractionRing A
  let f :A →+* F:=algebraMap A F
  let t:=f x
  have ht:aB6 k t:=gpN ell t hx hsmall
  have hdegree (a :A) :=poles_and_degree h1 h2 t ht (f a)
  let order (p:CurvePlace k F) (a :A) :=poleOrder p.value (f a)
  obtain ⟨generators,hgen⟩:=hfinite.out
  let S:=generators.biUnion (fun a=>(hdegree a).1.toFinset)
  have hz (p:CurvePlace k F) (hp:p∉S) (a :A) :order p a=0:= by
    have ha :a∈zum k (↑generators :Set A) := by
      rw [hgen]
      trivial
    induction ha using Algebra.adjoin_induction with
    | mem b hb =>
      have h:p∉(hdegree b).1.toFinset := fun h =>
        hp (Finset.mem_biUnion.mpr ⟨b,hb,h⟩)
      simpa [order,Function.mem_support] using h
    | algebraMap c =>
      simpa [order,f,zG3 k A F] using pole_scalar (F:=F) p c
    | add a b _ _ ha hb =>
      have hab:order p (a+b)≤ max (order p a) (order p b) := by
        simpa only [order,map_add] using pole_add p (f a) (f b)
      exact za7 (by simpa [ha,hb] using hab)
    | mul a b _ _ ha hb =>
      have hab:order p (a*b)≤order p a+order p b:= by
        simpa only [order,map_mul] using pole_mul p (f a) (f b)
      exact za7 (by simpa [ha,hb] using hab)
  let e :=S.equivFin.symm
  have hsum (g:CurvePlace k F→ℕ) (hg : ∀ p∉S,g p=0) :
      (∑ i,g (e i)) = ∑ᶠ p,g p:= by
    rw [e.sum_comp (fun p:S=>g p),Finset.sum_coe_sort]
    exact (finsum_eq_finsetSum_of_support_subset _ (fun p hp=> by
      by_contra h
      exact hp (hg p h))).symm
  let orders (p:CurvePlace k F) :ak7 k A :=
    { order :=order p
      constant:= fun c=> by
        simpa [order,f,zG3 k A F] using pole_scalar (F:=F) p c
      add_le := fun a b=> by simpa only [order,map_add] using pole_add p (f a) (f b)
      mul_le := fun a b=> by simpa only [order,map_mul] using pole_mul p (f a) (f b) }
  refine ⟨{
    count:=S.card
    place := fun i=>orders (e i)
    QZ:= fun i=>placeWeight (e i:CurvePlace k F)
    degree_eq := fun a => ?_
    line_eq := ?_ }⟩
  · change aHf k A a = ∑ i,order (e i) a*placeWeight (e i:CurvePlace k F)
    calc
      _=aFr (k :=k) (f a) := by
        exact (cJV (f a)).trans (hdegree a).2.2.symm
      _ = ∑ i,placeWeight (e i:CurvePlace k F)*order (e i) a :=
        (hsum (fun p=>placeWeight p*order p a) (fun p hp=> by
          rw [hz p hp a,Nat.mul_zero])).symm
      _ = _:=Finset.sum_congr rfl (fun _ _=>Nat.mul_comm _ _)
  · change bfe k A y v =
      ∑ i,max (order (e i) y) (order (e i) v)*placeWeight (e i:CurvePlace k F)
    calc
      _ = ∑ᶠ p:CurvePlace k F,placeWeight p*max (order p y) (order p v) :=
        (ewR y v).trans (pencil_pole_degree h1 h2 h3 h4 h5 t ht (f y) (f v)).symm
      _ = ∑ i,placeWeight (e i:CurvePlace k F)*max (order (e i) y) (order (e i) v) :=
        (hsum (fun p=>placeWeight p*max (order p y) (order p v))
          (fun p hp=> by rw [hz p hp y,hz p hp v,max_self,Nat.mul_zero])).symm
      _ = _:=Finset.sum_congr rfl (fun _ _=>Nat.mul_comm _ _)
end
end bzU
end
section
set_option backward.isDefEq.respectTransparency false
namespace bRM
noncomputable section
open E7 (CurvePlace)
open aeF (Os)
open XX
open Polynomial
open scoped Polynomial WithZero
attribute [local instance] Polynomial.algebra
open scoped RatFunc in
private theorem eba {K E G:Type}
    [zrb K] [zrb E] [zrb G] [zZE K E] [zZE (RatFunc K) G]
    [FiniteDimensional K E] (f :RatFunc E →+* G) (hf :zpX f)
    (h : ∀ P:K[X],f (algebraMap E[X] (RatFunc E) (P.map (algebraMap K E))) =
      algebraMap (RatFunc K) G (algebraMap K[X] (RatFunc K) P)) :
    zsE (RatFunc K) G=zsE K E := by
  have hP (P:K[X]) :
      f (algebraMap (RatFunc K) (RatFunc E) (algebraMap K[X] (RatFunc K) P)) =
        algebraMap (RatFunc K) G (algebraMap K[X] (RatFunc K) P) := by
    rw [← zG3 K[X] (RatFunc K) (RatFunc E),
      zG3 K[X] E[X] (RatFunc E)]
    exact h P
  have hcomm (a :RatFunc K) :
      f (algebraMap (RatFunc K) (RatFunc E) a)=algebraMap (RatFunc K) G a := by
    induction a using RatFunc.induction_on with
    | _ P Q _=>simp only [map_div₀,hP]
  let e :RatFunc E →ₐ[RatFunc K] G := { f with commutes' := hcomm }
  let E' := AlgEquiv.ofBijective e ⟨f.injective,hf⟩
  exact E'.toLinearEquiv.finrank_eq.symm.trans (RatFunc.finrank_ratFunc_ratFunc K E)
variable {k F:Type} [zrb k] [zrb F] [zZE k F]
variable {p:CurvePlace k F}
local notation "aiT" => p.value.valuationSubring
local notation "ι" => p.value.valuationSubring.toSubring.subtype
local notation "j" => algebraMap F[X] (RatFunc F)
section ResidueMap
variable [zZE (RatFunc k) (RatFunc F)]
variable {q:CurvePlace (RatFunc k) (RatFunc F)}
local notation "VI" => q.value.valuationSubring
private theorem efe (h:OG p q) (a :F) :
   q.value (RatFunc.C a)=p.value a := by
 obtain rfl | ha :=eq_or_ne a 0
 · simp
 · simpa [zy1 ha] using h (z1z a)
private theorem cVr (h:OG p q) (P:F[X]) :
   q.value (j P)≤1 ↔ ∀ n,p.value (P.coeff n)≤1 := by
 rw [h P,Finset.sup_le_iff]
 refine ⟨fun hP n => ?_,fun hP n _=>hP n⟩
 by_cases hn:P.coeff n=0
 · simp [hn]
 · exact hP n (Polynomial.mem_support_iff.mpr hn)
private theorem small_iff (h:OG p q) (P:F[X]) :
   q.value (j P)<1 ↔ ∀ n,p.value (P.coeff n)<1 := by
 rw [h P,Finset.sup_lt_iff (show (⊥ : ℤᵐ⁰)<1 from zero_lt_one)]
 refine ⟨fun hP n => ?_,fun hP n _=>hP n⟩
 by_cases hn:P.coeff n=0
 · simp [hn]
 · exact hP n (Polynomial.mem_support_iff.mpr hn)
private def aok (h:OG p q) :aiT[X] →+* VI :=
 ((j).comp (zhd ι)).codRestrict (VI).toSubring
   (fun P=> by
     change q.value (j (P.map ι))≤1
     apply (cVr h _).mpr
     intro n
     rw [z0b]
     exact (P.coeff n).property)
private theorem eoC (h:OG p q) (P:aiT[X]) :
 (aok h P:RatFunc F)=j (P.map ι) :=rfl
private theorem c8A (h:OG p q) (P:aiT[X]) :
   IsLocalRing.residue VI (aok h P)=0 ↔
     P.map (IsLocalRing.residue aiT)=0:= by
 rw [IsLocalRing.residue_eq_zero_iff,q.value.mem_maximalIdeal_iff,
   eoC,small_iff h,Polynomial.ext_iff]
 simp only [z0b,Polynomial.coeff_zero,IsLocalRing.residue_eq_zero_iff,
   p.value.mem_maximalIdeal_iff]
 rfl
private def c8v (h:OG p q) :EO p →+* EO q :=
 zP2 (IsLocalRing.maximalIdeal aiT)
  ((IsLocalRing.residue VI).comp ((aok h).comp z1z))
  (fun a ha=> by
    change IsLocalRing.residue VI (aok h (z1z a))=0
    apply (c8A h _).mpr
    rw [zrL,(IsLocalRing.residue_eq_zero_iff a).mpr ha,Polynomial.C_0])
private theorem fWJ (h:OG p q) (a :aiT) :
 c8v h (IsLocalRing.residue aiT a) =
  IsLocalRing.residue VI (aok h (z1z a)) :=rfl
private def bgJ (h:OG p q) : (EO p)[X] →+* EO q :=
 zqf (c8v h)
  (IsLocalRing.residue VI (aok h z7y))
private theorem c8w (h:OG p q) (P:aiT[X]) :
    bgJ h (P.map (IsLocalRing.residue aiT)) =
      IsLocalRing.residue VI (aok h P) := by
  have heq : (bgJ h).comp (zhd (IsLocalRing.residue aiT)) =
      (IsLocalRing.residue VI).comp (aok h) := by
    apply z86
    · intro a
      simp only [zQb,Polynomial.coe_mapRingHom,zrL,
        bgJ,z4Q,zJU]
      exact fWJ h a
    · simp [bgJ]
  exact zLs heq P
private theorem c8x (h:OG p q) :
  zq4 (bgJ h) := by
 apply (injective_iff_map_eq_zero (bgJ h)).mpr
 intro P hP
 obtain ⟨P,rfl⟩:=Polynomial.map_surjective (IsLocalRing.residue aiT)
  IsLocalRing.residue_surjective P
 rw [c8w] at hP
 exact (c8A h P).mp hP
private def bLq (h:OG p q) :RatFunc (EO p) →+* EO q :=
 zIj (c8x h)
private theorem cfj (h:OG p q) (P:aiT[X]) :
    bLq h
      (algebraMap (EO p)[X] (RatFunc (EO p))
        (P.map (IsLocalRing.residue aiT))) =
      IsLocalRing.residue VI (aok h P) :=
  (zoc (c8x h) _).trans
    (c8w h P)
private theorem cVo (h:OG p q) {P:F[X]}
  (hP:q.value (j P)≤1) :
  ∃ A:aiT[X],(aok h A:RatFunc F)=j P:= by
 have hrange :P∈(zhd ι).range := by
  apply (Polynomial.mem_map_range _).mpr
  intro n
  exact ⟨⟨P.coeff n,(cVr h P).mp hP n⟩,rfl⟩
 obtain ⟨A,hA⟩:=hrange
 exact ⟨A,congrArg j hA⟩
private theorem fWN (h:OG p q) :
   zpX (bLq h) := by
 intro z
 obtain ⟨z,rfl⟩:=IsLocalRing.residue_surjective z
 obtain ⟨P,Q,hQ,hz⟩ : ∃ P Q:F[X],Q≠0∧(z :RatFunc F)=j P/j Q:= by
   induction (z :RatFunc F) using RatFunc.induction_on with
   | _ P Q hQ=>exact ⟨P,Q,hQ,rfl⟩
 have hjQ:j Q≠0:=RatFunc.algebraMap_ne_zero hQ
 have hvQ:q.value (j Q)≠0:=q.value.zero_iff.not.mpr hjQ
 obtain ⟨a,ha⟩:=p.normalized (q.value (j Q))
 let D:F[X] :=z1z a⁻¹
 have hvD:q.value (j D)=(q.value (j Q))⁻¹:= by
   rw [show j D =RatFunc.C a⁻¹ from RatFunc.algebraMap_C _,efe h,map_inv₀,ha]
 have hQ' : q.value (j (D *Q))=1 := by
   rw [map_mul,map_mul,hvD,inv_mul_cancel₀ hvQ]
 have hprod: (z :RatFunc F)*j (D *Q)=j (D *P) := by
   rw [map_mul,map_mul,mul_left_comm,(eq_div_iff hjQ).mp hz]
 have hP' : q.value (j (D *P))≤1 := by
   rw [← hprod,map_mul,hQ',mul_one]
   exact z.property
 obtain ⟨A,hA⟩:=cVo h hP'
 obtain ⟨B,hB⟩:=cVo h hQ'.le
 have hmul :z*aok h B=aok h A:= by
   apply Subtype.ext
   change (z :RatFunc F)*(aok h B:RatFunc F)= _
   rw [hA,hB,hprod]
 have hden:IsLocalRing.residue VI (aok h B)≠0:= by
   rw [ne_eq,IsLocalRing.residue_eq_zero_iff,q.value.mem_maximalIdeal_iff,hB,hQ']
   exact lt_irrefl 1
 refine ⟨algebraMap (EO p)[X] (RatFunc (EO p))
     (A.map (IsLocalRing.residue aiT)) /
   algebraMap (EO p)[X] (RatFunc (EO p))
     (B.map (IsLocalRing.residue aiT)),?_⟩
 rw [map_div₀,cfj,cfj,div_eq_iff hden]
 exact (congrArg (IsLocalRing.residue VI) hmul).symm.trans (map_mul _ _ _)
end ResidueMap
private theorem fWM (P:k[X]) :
    letI:=Os k (F:=F)
    ∀ (q:CurvePlace (RatFunc k) (RatFunc F)) (h:OG p q),
      bLq h (algebraMap (EO p)[X] (RatFunc (EO p))
        (P.map (algebraMap k (EO p)))) =
        algebraMap (RatFunc k) (EO q) (algebraMap k[X] (RatFunc k) P) := by
  let:=Os k (F:=F)
  intro q h
  have hred:P.map (algebraMap k (EO p)) =
      (P.map (aoG p)).map (IsLocalRing.residue aiT) :=
    (zoi _ _ _).symm
  rw [hred,cfj]
  change IsLocalRing.residue q.value.valuationSubring
    (aok h (P.map (aoG p))) =
    IsLocalRing.residue q.value.valuationSubring
      (aoG q (algebraMap k[X] (RatFunc k) P))
  congr 1
  apply Subtype.ext
  change j ((P.map (aoG p)).map ι) =
    algebraMap (RatFunc k) (RatFunc F) (algebraMap k[X] (RatFunc k) P)
  rw [zoi,ad4]
  rfl
theorem proof :XX.c4 := by
 intro k F _ _ _ p hp
 let:FiniteDimensional k (EO p) :=hp
 let:=Os k (F:=F)
 change ∀ q:CurvePlace (RatFunc k) (RatFunc F),OG p q →
  placeWeight q=placeWeight p
 intro q h
 exact eba (bLq h) (fWN h)
  (fun P=>fWM P q h)
end
end bRM
end
section
namespace aKx
open IntermediateField
open XX (adp)
open scoped Polynomial algebraAdjoinAdjoin
variable {k F:Type} [zrb k] [zrb F] [zZE k F]
theorem b3a {t x :F} (ht:Transcendental k t)
   (hfin:zAa (IntermediateField.adjoin k {t}) F)
   (hx :Transcendental k x) :zAa (IntermediateField.adjoin k {x}) F:= by
 let:=hfin
 have ht' : IsAlgebraic (IntermediateField.adjoin k {x}) t :=
   isAlgebraic_adjoin_iff.mpr (.adjoin_singleton ht hx
     (isAlgebraic_adjoin_iff.mp (zgs x)))
 let Kxt:=restrictScalars k (IntermediateField.adjoin (IntermediateField.adjoin k {x}) {t})
 let Ktx :=restrictScalars k (IntermediateField.adjoin (IntermediateField.adjoin k {t}) {x})
 let:zZE (IntermediateField.adjoin k {x}) Kxt :=
   (IntermediateField.adjoin (IntermediateField.adjoin k {x}) {t}).algebra
 let:Module (IntermediateField.adjoin k {x}) Kxt:=Algebra.toModule
 let:SMul (IntermediateField.adjoin k {x}) Kxt:=Algebra.toSMul
 let:zZE (IntermediateField.adjoin k {t}) Ktx :=
   (IntermediateField.adjoin (IntermediateField.adjoin k {t}) {x}).algebra
 let:Module (IntermediateField.adjoin k {t}) Ktx :=Algebra.toModule
 let:SMul (IntermediateField.adjoin k {t}) Ktx :=Algebra.toSMul
 have :zAa (IntermediateField.adjoin k {x}) Kxt :=
   IntermediateField.adjoin.finiteDimensional ht'.isIntegral
 have :zAa Kxt F:= by
   unfold Kxt
   rw [adjoin_simple_comm]
   have :zsf (IntermediateField.adjoin k {t}) Ktx F:=isScalarTower_mid' _
   exact .right (IntermediateField.adjoin k {t}) Ktx F
 have :zsf (IntermediateField.adjoin k {x}) Kxt F:=isScalarTower_mid' _
 exact Module.Finite.trans Kxt F
theorem adjoin_inv (x :F) :
   IntermediateField.adjoin k ({x⁻¹} : Set F)=IntermediateField.adjoin k {x} := by
 apply le_antisymm <;> apply IntermediateField.adjoin_le_iff.mpr
 · exact Set.singleton_subset_iff.mpr (IntermediateField.inv_mem _ (mem_adjoin_simple_self k x))
 · apply Set.singleton_subset_iff.mpr
   change x∈IntermediateField.adjoin k ({x⁻¹} : Set F)
   simpa only [inv_inv] using
    (IntermediateField.adjoin k ({x⁻¹} : Set F)).inv_mem (mem_adjoin_simple_self k x⁻¹)
@[instance_reducible]
noncomputable def bql (u:F) (hu:Transcendental k u) :
   zZE k[X] (IntermediateField.adjoin k {u}) :=
 ((algebraMap (zum k {u}) (IntermediateField.adjoin k {u})).comp
   (zjm k u hu).toRingHom).toAlgebra
theorem bqn {u:F} (hu:Transcendental k u) :
   let K:=IntermediateField.adjoin k {u}
   letI:zZE k[X] F:=adp u
   letI:zZE k[X] K:=bql u hu
   z0o k[X] K∧zsf k[X] K F:= by
 let R:=zum k ({u} : Set F)
 let K:=IntermediateField.adjoin k ({u} : Set F)
 let e :=zjm k u hu
 let:zZE k[X] F:=adp u
 let:zZE k[X] K:=bql u hu
 constructor
 · exact (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (S:=K) e.symm.toRingEquiv).mp
     (inferInstance :z0o R K)
 · apply zsL
   intro P
   change zEU u P=((e P:R) :F)
   rw [Polynomial.algEquivOfTranscendental_apply,Polynomial.aeval_subalgebra_coe]
end aKx
end
section
namespace aKx
open XX (adp)
open scoped Polynomial
theorem proof :XX.c1 := by
 intro k F _ _ _ t x ht hx
 have hfin:=b3a ht.1 ht.2.1 hx
 refine ⟨hfin,?_⟩
 have hxi:Transcendental k x⁻¹:= fun h=>hx (IsAlgebraic.inv_iff.mp h)
 let K:=IntermediateField.adjoin k ({x⁻¹} : Set F)
 let:zZE k[X] F:=adp x⁻¹
 let:zZE k[X] K:=bql x⁻¹ hxi
 have :z0o k[X] K:=(bqn hxi).1
 have :zsf k[X] K F:=(bqn hxi).2
 have :FiniteDimensional K F:= by
  change zAa (IntermediateField.adjoin k ({x⁻¹} : Set F)) F
  rw [adjoin_inv]
  exact hfin
 exact b29 k[X] K F (cch k)
end aKx
end
section
end
section
set_option maxHeartbeats 0
set_option maxRecDepth 50000
namespace acY
open acY.Compact
private def p0:Chunk 3162 4 487238266 :=
 cert _ _ _ 0x238f8282230f228ea20e0da18d0ca10c018b8b208a810a09a0090088800586ab960317838707b299841b048506083637086a813eebf54f9b9302644a393f56b1248e94b38f12d18203f1f05043e1e3d1d3c1c1b3b1a193a18031716391502141338120111000b0d5c2c062f070e0f64330836090a0c6d103d8dcf03baa049aafd71a884dc98142a9a49fb2d8925b4a59c7b6e9390ea95028214942a13a993291281922891811128108090002786ad96831703af07b19a041a848506083637086a4326abf54f9b9302644a393f56b1248e94b38f6dd001d4e2a050429284d274c264b2503244a23022249210120000b5a592d062e070e6266340835090a0c106c6e781dd5024d57ea9f372604c89473dead62296d36263e78a083b (by decide +kernel) (by decide +kernel)
private def p4 :Chunk 3166 4 497513376 :=
 cert _ _ _ 0x8e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae580c5e0e1c1eca66106c12141820207b1b8435409356b6884dc98142a9a49fab326e5b4a59c7b728ed05f8f82821f0f1e8e9e0e0d9d8d0c9d0c018b8b1c8a810a099c090088800586ae160317838707b219841b048506368c99b5dc21a775209f75fea7cdc98132251c9fb2d26e474a59c7b729250aa95028214942a13a993291281922891811128108090002786ad96831703af07b19a041a84850608081ec6e10d5024d57fb8d442604c89473decb62496d36263e25a0b3b9c540a0852509a4e984c964a064894460444924202400016b4b25a0c5c0e1cc4cc68106a12141820207b053c869dd5024d57fa21372604c894727ecb62496d29671e25a193c (by decide +kernel) (by decide +kernel)
private def p8:Chunk 3170 4 507103137 :=
 cert _ _ _ 0x8e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae580c5e0e1c1eca66106c12141820327b1b9e0775209f76b780cc099128e4fd599c123a52ce3cf547082fc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002c3570b018bc1c383d90cc20d8242831b5c040f6370869dd4824d727a21302644a39ef5664dcb69b138f3d521a1552a0504292854275326522503245123022250210120004f0d5b2d062e075e0f63340835090a0c10193d8dcf03baa049ab5b4426e4c099128e4fd599c123a52ce3cf34267938a81410a4a1349d30992c940c91288c088924840480002d6964b418b81c398998d020d42428304040f6370869dd4827dd7fa9f372604c894727ecb49b96d36271e79a163c (by decide +kernel) (by decide +kernel)
private def zF:Chunk 3174 4 517353169 :=
 cert _ _ _ 0x471f0504461e451d441c1b431a194218031716411502141340120111000b0d572c062f070e0f65330836090a0c1070193d829e434eea4126ad6edea1528e7be7c9372da6c4e3cfd47682fc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002c3570b018bc1c383d90cc20d8242831b445f8081ec6e10d3ba9049ab5b9f6644a393f9f27048e94b38f3dd21a1552a0504292854275326522503245123022250210120004f0d5b2d062e075e0f63340835090a0c1070193d8dcf03ba904fbb5bb76644a393f566704b69b138f3dd029dce2a050429284d274c264b2503244a23022249210120000b5a592d062e070e6266340835090a0c1070103d8dc21a775209356b76ecc0a154d24fd599372da52e7ba083b (by decide +kernel) (by decide +kernel)
private def TF:Chunk 3178 4 527675991 :=
 cert _ _ _ 0x471f0504461e451d441c1b431a194218031716411502141340120111000b0d572c062f070e0f65330836090a0c10117e03266d770869dd4824d57fa6b28ec84989c123a52e7fa30407e3e0a087c3c7a3a7838367634327430062e2c722a0428267024022200161ab8580c5e0e1c1ec866106c121418da31a45f8081ec6e781e34ce7dd7fb0128e4fc989372da6c4e3dbf4808554a81410a4a1509d4c9948940c91448c088940840480013c356cb418b81d783d8cd020d42428304045f80c9ec14f21a775209356b6d753493f9f24dcb694bb7e800ea715028214942693a6132592819225118111249080900005ad2c968317038731331a041a8485060808bf0103d8dc21a775339f75fed750a94727f3e4e091d29671e7ea133c (by decide +kernel) (by decide +kernel)
private def WU:Chunk 3182 4 538132627 :=
 cert _ _ _ 0x471f0504461e451d441c1b431a194218031716411502141340120111000b0d572c062f070e0f65330836090a0c101c322fc040f6370869dd4ce7dd7ea6d5f2c85229372da6c4e3c4d48684fc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002c3570b018bc1c383d90cc20d8242831b48bcc6917327b1b9e078d339355feafd7c93f2627048e94b89a8e106a95028214942a13a993291281922891811128108090002786ad96831703af07b19a041a848506080e1917e0207b1b8434eea673eebfd359476424c4e091d297135041dce2a050429284d274c264b2503244a23022249210120000b5a592d062e070e6266340835090a0c1018d22fc040f6373c0f1a6726abfd3594727e4c49b96d36271e7fa103c (by decide +kernel) (by decide +kernel)
private def p24 :Chunk 3186 4 548627072 :=
 cert _ _ _ 0x238f8282230f228ea20e0da18d0ca10c018b8b208a810a09a0090088800586ab960317838707b299841b048506081e89c322fc040f6373c0f1a6726abf560b2139e4c4e091d29740d20213f1f05043e1e3d1d3c1c1b3b1a193a18031716391502141338120111000b0d5c2c062f070e0f64330836090a0c6d3d145e63780c9ec14f21a78d4c9f75faa157cb2f39e9149b96d36340d28a1d52a0504292854275326522503245123022250210120004f0d5b2d062e075e0f63340835090a0c103d138645f8081ec6e10d3ba99c9aaff4dabe5909cf2624dcb69b138f405149f4e2a050429284d274c264b2503244a23022249210120000b5a592d062e070e6266340835090a0c1022f31bc064f6373c0f1a993eebf542af965e73c989c123a52e80a103c (by decide +kernel) (by decide +kernel)
private def p28:Chunk 3190 4 559083761 :=
 cert _ _ _ 0x11c7c14111879147510706d0c686508600c5c59045408504d00480444002c355cb018bc1c383d94cc20d824283040f451198d22fc040f6373c0f1a993eeaf52994d39e9149b96d36341d25a1bf1f05043e1e3d1d3c1c1b3b1a193a18031716391502141338120111000b0d5c2c062f070e0f64330836090a0c6d50946245f80c99b5dc21a78d4c9355fa9be2796f2624dcb69b1a0e9190aa95028214942a13a993291281922891811128108090002786ad96831703af07b19a041a848506081e8a2338645f8081ec6e781e35327dd7eac15f2cbce7931382474a5d0544c7d38a81410a4a1349d30992c940c91288c088924840480002d6964b418b81c398998d020d424283040f451898de0327b053c869e35327dd5ea6f65e73d229372da6c682a163c (by decide +kernel) (by decide +kernel)
private def p32 :Chunk 3194 4 569946396 :=
 cert _ _ _ 0x471f0504461e451d441c1b431a194218031716411502141340120111000b0d572c062f070e0f65330836090a0c1050945e63780c9ec14f21a78d4c93557a91ca696f2624dcb69b1a1a91909f8f82821f0f1e8e9e0e0d9d8d0c9d0c018b8b1c8a810a099c090088800586ae160317838707b219841b04850636a859c322fc040f6370869e35ea7dd5ea5389e5bc989c123a52de9a4342aa540a085250a84ea64ca44a0648a2460444a0420240009e1ab65a0c5c0ebc1ec668106a12141820a1288cc6917e0207b1b9e078d4c9f757a94ca696f2624dcb69b17a686cf6715028214942693a6132592819225118111249080900005ad2c968317038731331a041a84850608284a3122fc040f6370869e35ea7dd5ea5389e5bc989c123a6c5e9a133c (by decide +kernel) (by decide +kernel)
private def p36:Chunk 3198 4 580860862 :=
 cert _ _ _ 0x471f0504461e451d441c1b431a194218031716411502141340120111000b0d572c062f070e0f65330836090a0c1050b45e63780c9ec14f21a78d7a935492aed23c4f29a5bc989c123a6c688a5c447e3e0a087c3c7a3a7838367634327430062e2c722a0428267024022200161ab8580c5e0e1c1ec866106c121418da7aa70c8bf0103d8dcf02a2bd49aabd48e57ca696f2624dcb69b1a1e92d0ea95028214942a13a993291281922891811128108090002786ad96831703af07b19a041a84850608285a2f31bc064f60a790d3c6bd4fbabd4a713ca696f2627048e9b1a1e884f6715028214942693a6132592819225118111249080900005ad2c968317038731331a041a848506082859c322fc040f6370869e35ea7dd5da4764673d229372da6c686a133c (by decide +kernel) (by decide +kernel)
private def p40:Chunk 3202 4 591542798 :=
 cert _ _ _ 0x8e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae580c5e0e1c1eca66106c121418207aa8c48bf0103d8dc21a78d7ab31492aed2a9bb2be534b793126e5b503d154c88afc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002c3570b018bc1c383d90cc20d8242831b4f55119c322fc040f6373c0a8935492aed2a95f29a5bc989c123a6c689a5644aa540a085250a84ea64ca44a0648a2460444a0420240009e1ab65a0c5c0ebc1ec668106a121418207aa8c4c6f019336bb8434f1af526a9255da4737657ca69cf48a4dcb6a07a268dcfe715028214942693a6132592819225118111249080900005ad2c968317038731331a041a848506081ea9c322fc040f6373c0a8af526aaed2a95f29a5bc989372da6c688a1b3d (by decide +kernel) (by decide +kernel)
private def p44 :Chunk 3206 4 602620127 :=
 cert _ _ _ 0x238f8282230f228ea20e0da18d0ca10c018b8b208a810a09a0090088800586ab960317838707b299841b0485060828b9c322fc040f6373c0a8b31606bed12a272be534b7931382474d8c514ac88fc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002c3570b018bc1c383d90cc20d8242831b545d1198d22e64f60a790d2a2cc581afb4aacd4dd95f29a73d229372da81e28a6a45aa540a085250a84ea64ca44a0648a2460444a0420240009e1ab65a0c5c0ebc1ec668106a12141820a2e8c48bf0103d8dcf02a24d524abb4aa89caf94d2de4c4e091d40f145131f4e2a050429284d274c264b2503244a23022249210120000b5a592d062e070e6266340835090a0c103d54466348bf0103d829e434a8935492bed129bb64673d2293723a6c68aa2c3e (by decide +kernel) (by decide +kernel)
private def p48:Chunk 3210 4 614063765 :=
 cert _ _ _ 0x11c7c14111879147510706d0c686508600c5c59045408504d00480444002c355cb018bc1c383d94cc20d824283040f5ce1917e0207b1b9e0545acac344ae45c79bb2be534b793126e5b503dc14c28afc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002c3570b018bc1c383d90cc20d8242831b4f5d1798de03266d770869516b2c0d7da25c0a89caf94d2de4c4e091d40f70533a2d52a0504292854275326522503245123022250210120004f0d5b2d062e075e0f63340835090a0c103d738645f8081ec6e78151662c0d7da2566a6ed919cf48a4dc8e9b1a32898fa715028214942693a6132592819225118111249080900005ad2c968317038731331a041a8485060828ba2f31bc064f60a790d2a2cc524afb44ae3cdd95f29a5bc989372da81e8ca373f (by decide +kernel) (by decide +kernel)
private def c:Chunk 3162 52 7141761347 :=
 add p0 <| add p4 <| add p8 <| add zF <| add TF <| add WU <| add p24 <| add p28 <| add p32 <| add p36 <| add p40 <| add p44 <| p48
end acY
end
section
namespace lB
noncomputable section
open Polynomial MvPolynomial aR Ex dN wH
open Sr.Weight
local notation "W" => MvPolynomial.weightedTotalDegree
private def denominator (L:ℕ) (g:af 4) :af 4 :=
 separant g^(2*L)
private def numerator (L:ℕ) (g:af 4) (i:AK) :af 4 :=
 if hi:i.val<4 then z9v ⟨i.val,hi⟩*denominator L g
 else
   znf (z1z (↑i.val.factorial:ao)⁻¹) *
     (separant g^(2*(L - i.val))*su g i.val)
private def a83 (L:ℕ) (g:af 4) :TaylorChart where
 denom:=bC (denominator L g)
 numerator i:=bC (numerator L g i)
 initial i:= by
  unfold numerator bC
  have hi: (i.castLE (by decide :4≤bf)).val<4 :=i.isLt
  rw [dite_eq_left hi,map_mul,z7N]
  rfl
private theorem ZB (L:ℕ) (w:Fin 4→ℕ) {g:af 4} {B:ℕ} (hg:W w g≤B) :
   W w (denominator L g)≤2*L*(B - w 3) :=
 (weightedTotalDegree_pow_le _ _ _).trans
   (zBI _ ((aAA w g).trans (zIu hg _)))
private theorem Vi {L:ℕ} (hL:bf≤L) (w:Fin 4→ℕ) (Δ d₀:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ) (hw : ∀ i,w i≤d₀)
    {g:af 4} {B:ℕ} (hB:w 3≤B) (hg:W w g≤B) (i:AK) :
    W w (numerator L g i)≤d₀+2*L*(B - w 3)+L*Δ:= by
  have hi:i.val≤L:=i.isLt.le.trans hL
  unfold numerator
  split_ifs with hinit
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((z9f ((abx w _).trans (hw _)) (ZB L w hg)).trans
        (z8K _ _))
  · have hp:=(weightedTotalDegree_pow_le w (separant g) (2*(L - i.val))).trans
      (zBI _ ((aAA w g).trans (zIu hg _)))
    apply (Po _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _≤2*(L - i.val)*(B - w 3)+(w 0+i.val*(2*(B - w 3)+Δ)) :=
        z9f hp (avh w Δ hshift hB hg i.val)
      _=w 0+2*(i.val+(L - i.val))*(B - w 3)+i.val*Δ:= by ring
      _≤_:= by
        rw [Nat.add_sub_of_le hi]
        exact z9f (zlr (hw 0) _) (ztf Δ hi)
private theorem aGY {L:ℕ} (hL:bf≤L) (g:af 4) (p:Shape) (hB:aO (shape g) p)
    (hp:bF p) (ht:0<p.t) :
    (a83 L g).dM (bY L p) := by
  have hb:1≤p.b:= by have :=hp.1; have :=hp.2; omega
  have hj:3≤p.j:= by have :=hp.2; omega
  have h₁:W 1 g≤p.b:= by simpa only [shape,weightedTotalDegree_one] using hB.1
  have h₂:W Fin.val g≤p.j:= by simpa only [shape,C6] using hB.2.1
  let w:Fin 4→ℕ:=Pi.single 3 1
  have h₃:W w g≤p.t:= by simpa only [w,shape,weightedTotalDegree_piSingle] using hB.2.2
  have hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+1 := by
    intro i
    fin_cases i <;> decide
  have hw : ∀ i,w i≤1 := by
    intro i
    fin_cases i <;> decide
  have hw3:w 3=1 := by decide
  have pkg (P:af 4) (hb' : W 1 P≤1+2*L*(p.b - 1))
      (hj' : W Fin.val P≤2*L*(p.j-3)+L+3)
      (ht' : W w P≤2*L*(p.t - 1)+L+1) :
      yy (bC P) (bY L p) := by
    apply abr
    refine ⟨?_,?_,?_⟩
    · change P.totalDegree≤ max _ _
      exact (by simpa only [weightedTotalDegree_one] using hb' :
        P.totalDegree≤1+2*L*(p.b - 1)).trans (le_max_left _ _)
    · change qE P≤_
      rwa [C6]
    · change P.degreeOf 3≤ min _ _
      apply le_min
      · simpa only [w,weightedTotalDegree_piSingle] using ht'
      · have h:=(a9d P).trans hj'
        omega
  constructor
  · apply pkg
    · exact (ZB L _ h₁).trans (Nat.le_add_left _ _)
    · exact (ZB L _ h₂).trans ((z8K _ _).trans (z8K _ _))
    · have h:=ZB L w h₃
      rw [hw3] at h
      exact h.trans (by omega)
  · intro i
    apply pkg
    · have h:=Vi hL 1 0 1 (fun _=> by simp) (fun _=>le_rfl) hb h₁ i
      change W 1 (numerator L g i)≤1+2*L*(p.b - 1)+L*0 at h
      simpa only [mul_zero,add_zero] using h
    · have h:=Vi hL Fin.val 1 3 (fun _=> by rfl)
        (fun j:Fin 4=>Nat.le_of_lt_succ j.isLt) hj h₂ i
      change W Fin.val (numerator L g i)≤3+2*L*(p.j-3)+L*1 at h
      simpa only [mul_one,Nat.add_left_comm,Nat.add_comm,Nat.add_assoc] using h
    · have hwle :w 3≤p.t:=hw3.symm ▸ ht
      have h:=Vi hL w 1 1 hshift hw hwle h₃ i
      simpa only [hw3,mul_one,Nat.add_left_comm,Nat.add_comm,Nat.add_assoc] using h
private theorem ajW (S:ao[X]) (n:ℕ) :
  derivative^[n] S=z1z (n.factorial:ao)*hasseDeriv n S:= by
 ext m
 rw [coeff_iterate_derivative,Polynomial.coeff_C_mul,hasseDeriv_coeff,
  Nat.descFactorial_eq_factorial_mul_choose]
 simp only [nsmul_eq_mul,Nat.cast_mul,mul_assoc]
theorem afz (S:ao[X]) (P:af 4) :
  An S (bC P)=j8 (cK P S) := by
 exact (MvPolynomial.map_eval j8 (jet S) P).symm
private theorem a2o {L:ℕ} (hL:bf≤L) (g:af 4) (S:ao[X])
    (hg:cK g S=0) (hr :qg g S) : (a83 L g).aay S:= by
  have hp:cK (separant g) S≠0:=hr
  have hden:cK (denominator L g) S=cK (separant g) S^(2*L) :=
    map_pow (zY9 (jet S:Fin 4→ao[X])) _ _
  constructor
  · change An S (bC (denominator L g))≠0
    rw [afz]
    apply (map_ne_zero_iff _ SZ).mpr
    rw [hden]
    exact pow_ne_zero _ hp
  · intro i
    change An S (bC (numerator L g i)) =
      An S (bC (denominator L g))*j8 (hasseDeriv i.val S)
    rw [afz,afz,← map_mul]
    apply congrArg j8
    unfold numerator
    split_ifs with hinit
    · unfold cK
      rw [map_mul,MvPolynomial.eval_X,mul_comm]
      rfl
    · let E :=zY9 (jet S:Fin 4→ao[X])
      change E (_ *(_^_ *_))= _
      rw [map_mul,map_mul,map_pow,MvPolynomial.eval_C]
      change _ *(cK (separant g) S^(2*(L - i.val)) *
        cK (su g i.val) S)= _
      rw [arh _ _ hg,ajW]
      have hinv :z1z (↑i.val.factorial:ao)⁻¹*z1z (↑i.val.factorial:ao)=1 := by
        rw [← map_mul,inv_mul_cancel₀ (ahA
          (i.isLt.trans (by decide :bf<K1.p))),map_one]
      have hpow:2*(L - i.val)+2*i.val = 2*L:= by
        have hi:i.val≤L:=i.isLt.le.trans hL
        rw [← Nat.mul_add,Nat.sub_add_cancel hi]
      calc
        _=(z1z (↑i.val.factorial:ao)⁻¹*z1z (↑i.val.factorial:ao)) *
            ((cK (separant g) S^(2*(L - i.val))*cK (separant g) S^(2*i.val)) *
              hasseDeriv i.val S) := by ring
        _ = _:= by
          rw [hinv,one_mul,← pow_add,hpow,hden]
theorem d34 (g:af 4) (p:Shape) (hB:aO (shape g) p)
   (hp:bF p) (ht:0<p.t) :
   ∃ C:TaylorChart,C.dM (bY (bf+4) p) ∧
     ∀ S:ao[X],cK g S=0→qg g S→C.aay S :=
 ⟨a83 (bf+4) g,aGY (z8K _ _) g p hB hp ht,
   a2o (z8K _ _) g⟩
end
end lB
end
section
namespace aqa
open wH
abbrev Local (q:PrimeSpectrum Lower) :=Localization.AtPrime q.asIdeal
def K7 {R ι:Type*} [za6 R] (f :ι→R) (i:ι) :znc R :=
 zye (f '' {j | j≠i})
end aqa
end
section
namespace aiJ
noncomputable section
open aR oR we
open scoped Polynomial
abbrev dF:=FractionRing cH[X]
abbrev nW:=z3y (Fin 3) dF
abbrev mK:=z3y (Fin bf) dF
abbrev aYJ:=znc nW
def adE :dF:=algebraMap cH[X] dF z7y
def a4j:ao[X] →+* dF :=
  (algebraMap cH[X] dF).comp
    (zhd (algebraMap ao cH))
def GZ (g:af 3) :nW:=zDK a4j g
def aHZ (f :af 3) :aYJ:=zye {GZ f}
def cS6 (f :af 3) :aYJ :=
 aHZ f ⊔ zye {GZ (Dm f)}
def gN (Q:Bk) :znc mK :=
 Q.map (zDK (algebraMap cH dF))
def tO:nW →ₐ[dF] mK :=
 MvPolynomial.aeval fun j=>B7.KT adE j.val
def lA (Q:Bk) :aYJ:=(gN Q).comap tO
def asY (Q:Bk) :Prop :=
  ∀ j:Fin bf,∃ u v :nW,
    v∉lA Q ∧
      tO v*z9v j - tO u∈gN Q
structure XP (f :af 3) (Q:Bk) :Prop where
 extended_prime : (gN Q).IsPrime
 on_divisor :cS6 f≤lA Q
 regular :GZ (separant f)∉lA Q
 birational:asY Q
end
end aiJ
end
section
namespace agP
open aR dN Rl
def bz9 (f :af 4) (q:af 3) (aI:znc GeoJets)
    (hp:aI.IsPrime) :Prop :=
  letI:=hp
  let A:=Localization.AtPrime aI
  (kC f (He q)).map (algebraMap GeoJets A)=IsLocalRing.maximalIdeal A
end agP
end
