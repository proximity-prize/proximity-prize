import ProximityPrize.SubmissionLower.Z1qPXJc
set_option Elab.async false
open _root_ renaming Algebra → zZE, CommRing → za6, Field → zrb, Function.Injective → zq4, Ideal.span → zye, IsFractionRing → z0o, IsFractionRing.injective → zxb, IsLocalization.map_units → z0j, IsLocalization.surj → zg4, IsScalarTower → zsf, IsScalarTower.algebraMap_apply → zG3, Nat.pos_of_ne_zero → zOl, Nat.sub_le_sub_right → zIu, Polynomial.X → z7y, Polynomial.ext → zXJ, Polynomial.map_injective → zTo, Polynomial.map_mul → zNl, Polynomial.map_sub → z3A, Polynomial.ringHom_ext → z86, PowerSeries → zpm, PowerSeries.C → zMG, PowerSeries.X → zWv, PowerSeries.coeff → z2o, PowerSeries.coeff_map → zVO, PowerSeries.coeff_zero_eq_constantCoeff_apply → zW1, PowerSeries.constantCoeff → zbO, PowerSeries.ext → zub, PowerSeries.map → zS4, RingHom.comp_apply → zQb, RingHom.ext → zz4
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_3_1_2
noncomputable section
open Polynomial qAjZDhd qaJ7jxd
open scoped nonZeroDivisors
private theorem fraction_derivation {A K:Type} [za6 A] [zrb K] [zZE A K]
    [z0o A K] (D:Derivation ℤ A A) :
    ∃ d:Derivation ℤ K K,∀ a,d (algebraMap A K a)=algebraMap A K (D a) := by
  let j:=algebraMap A K
  let F:A →+* DualNumber K :=
    { toFun:= fun a=>⟨j a,j (D a)⟩
      map_zero' := by ext <;> simp
      map_one' := by ext <;> simp
      map_add' := by intros; ext <;> simp
      map_mul' := fun a b=> by ext <;> simp [D.leibniz,smul_eq_mul,mul_comm] }
  have hU (a :A⁰) :IsUnit (F a) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (z0j K a)
  let G:K →+* DualNumber K:=IsLocalization.lift hU
  have he (a :A) :G (j a)=F a :=IsLocalization.lift_eq hU a
  have hfst: (TrivSqZeroExt.fstHom ℤ K K).toRingHom.comp G=RingHom.id K:= by
    apply IsLocalization.ringHom_ext A⁰
    exact zz4 fun a=>congrArg TrivSqZeroExt.fst (he a)
  have hf (a :K) : (G a).fst=a :=RingHom.congr_fun hfst a
  let d:K →+ K :=
    { toFun:= fun a=>(G a).snd
      map_zero' := by simp
      map_add' := by intros; simp }
  refine ⟨Derivation.mk' d.toIntLinearMap (fun a b => ?_),fun a =>
    congrArg TrivSqZeroExt.snd (he a)⟩
  change (G (a*b)).snd=a*(G b).snd+b*(G a).snd
  rw [map_mul,DualNumber.snd_mul,hf,hf,mul_comm (G a).snd b]
private def Bd {F:Type} [za6 F] (d:Derivation ℤ F F) (r :F[X])
    (b:Bool) :Derivation ℤ F[X] F[X] :=
  if b then r.derivative•Lv d -
    Lv d r•(Polynomial.derivative' (R:=F)).restrictScalars ℤ
  else r•Lv d
private theorem flow_map {A F:Type} [za6 A] [za6 F]
    (j:A →+* F) (d:Derivation ℤ A A) (D:Derivation ℤ F F)
    (h : ∀ a,D (j a)=j (d a)) (r z :A[X]) (b:Bool) :
    Bd D (r.map j) b (z.map j)=(Bd d r b z).map j:= by
  have hc (u:A[X]) :Lv D (u.map j)=(Lv d u).map j:= by
    ext i:1
    change D ((u.map j).coeff i)=((Lv d u).map j).coeff i
    rw [coeff_map,coeff_map,h]
    rfl
  cases b <;>
    simp only [Bd,Bool.false_eq_true,ite_false,ite_true,Derivation.smul_apply,
      Derivation.sub_apply,Derivation.restrictScalars_apply,derivative'_apply,
      smul_eq_mul,zNl,z3A,derivative_map,hc]
private theorem dvd_of_kills {F:Type} [zrb F] {p:ℕ} [CharP F p]
    (D:Derivation ℤ F[X] F[X]) {r q:F[X]} (hr :r≠0) (hdeg:r.natDegree<p)
    (hq:Irreducible q) (hqr :q∣r) (hD:D r=0) :q∣D q:= by
  have hqdeg:0<q.natDegree := by
    simpa only [degree_eq_natDegree hq.ne_zero,Nat.cast_pos] using degree_pos_of_irreducible hq
  have hle (m:ℕ) (hm:q^m∣r) :m≤ r.natDegree := by
    have h:=natDegree_le_of_dvd hm hr
    rw [natDegree_pow] at h
    exact (Nat.le_mul_of_pos_right _ hqdeg).trans h
  have hf :FiniteMultiplicity q r :=⟨r.natDegree,fun h=> by have :=hle _ h; omega⟩
  obtain ⟨s,hs,hqs⟩:=hf.exists_eq_pow_mul_and_not_dvd
  let n:=multiplicity q r
  change r=q^n*s at hs
  have hn:n≠0:= by
    intro h
    exact hqs (by simpa only [hs,h,pow_zero,one_mul] using hqr)
  have hnp:n<p:=(hle n ⟨s,hs⟩).trans_lt hdeg
  have hnU:IsUnit (n:F[X]) := by
    have h: (n:F)≠0:= fun hz =>
      (not_le_of_gt hnp) (Nat.le_of_dvd (zOl hn)
        ((CharP.cast_eq_zero_iff F p n).mp hz))
    simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr h).map
      (Polynomial.C:F →+* F[X])
  have hzero :q^(n-1)*((n:F[X])*s*D q+q*D s)=0:= by
    have hpw:q^n=q^(n-1)*q:= by
      conv_lhs=>rw [← Nat.sub_add_cancel (zOl hn),pow_succ]
    have h:=hD
    rw [hs,D.leibniz,D.leibniz_pow] at h
    simp only [smul_eq_mul,nsmul_eq_mul,hpw] at h
    linear_combination h
  have hsum:=(mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hq.ne_zero)
  have hdiv :q∣((n:F[X])*s)*D q:=⟨-D s,by linear_combination hsum⟩
  refine (hq.prime.dvd_mul.mp hdiv).resolve_left (fun h => ?_)
  exact (hq.prime.dvd_mul.mp h).elim
    (fun h=>hq.not_isUnit (isUnit_of_dvd_unit h hnU)) hqs
local instance (k :Type) [zrb k] :zZE ℤ (zpm k) :=Ring.toIntAlgebra _
local instance (k :Type) [zrb k] :zZE ℤ (kq k) :=Ring.toIntAlgebra _
local instance (k :Type) [zrb k] :zZE ℤ (Generic k) :=Ring.toIntAlgebra _
variable {k :Type} [zrb k] {p:ℕ}
private def asInt {S A:Type} [za6 S] [za6 A] [zZE S A]
    (d:Derivation S A A) :Derivation ℤ A A :=
  Derivation.mk' d.toLinearMap.toAddMonoidHom.toIntLinearMap
    (fun a b=>d.leibniz a b)
private abbrev seed :=asInt (PowerSeries.derivative (R:=k))
private theorem flow_reference (M:LocalMark k p) (b:Bool) :
    Bd seed M.r b (reference M.a)=0:= by
  have h:Lv (seed (k :=k)) (reference M.a)=0:= by
    ext i:1
    change PowerSeries.derivative ((reference M.a).coeff i)= _
    simp only [reference,coeff_C,coeff_zero]
    split_ifs <;> simp [PowerSeries.derivative_C]
  have h' : (reference M.a).derivative=0:=derivative_C
  cases b <;> simp [Bd,h,h']
private theorem flow_numerator (M:LocalMark k p) (b:Bool) (i:ℕ) :
    Bd seed M.r b (M.f.coeff i) = - (M.numerator b).coeff i:= by
  cases b <;>
    simp only [Bd,LocalMark.numerator,Bool.false_eq_true,ite_false,ite_true,
      Derivation.smul_apply,Derivation.sub_apply,Derivation.restrictScalars_apply,
      derivative'_apply,smul_eq_mul,coeff_add,← C_neg,coeff_C_mul]
  · change M.r*seedDeriv (M.f.coeff i) = -(-M.r*seedDeriv (M.f.coeff i))
    ring
  · change M.r.derivative*seedDeriv (M.f.coeff i) -
      seedDeriv M.r*(M.f.coeff i).derivative =
      -(-M.r.derivative*seedDeriv (M.f.coeff i) +
        seedDeriv M.r*(M.f.coeff i).derivative)
    ring
theorem operators [CharP k p] (M:LocalMark k p) (b:Bool)
    (q: (kq k)[X]) (hq:Irreducible q) (hqr :q∣toFrac M.r) :
    ∃ (D:Derivation ℤ (kq k)[X] (kq k)[X])
      (d:Derivation ℤ (Generic k) (Generic k)),
      (∀ z,d (algebraMap (kq k)[X] (Generic k) z) =
        algebraMap (kq k)[X] (Generic k) (D z)) ∧
      q∣D q∧d (ek (reference M.a))=0 ∧
      ∀ i,d (ek (M.f.coeff i)) = -ek ((M.numerator b).coeff i) := by
  let j:=algebraMap (zpm k) (kq k)
  obtain ⟨δ,hδ⟩:=fraction_derivation (K:=kq k) (seed (k :=k))
  let r :=toFrac M.r
  let D:=Bd δ r b
  obtain ⟨d,hd⟩:=fraction_derivation (K:=Generic k) D
  have hmap (z :Physical k) :d (ek z)=ek (Bd seed M.r b z) := by
    change d (algebraMap (kq k)[X] (Generic k) (z.map j))= _
    rw [hd]
    exact congrArg (algebraMap (kq k)[X] (Generic k)) (flow_map j seed δ hδ M.r z b)
  refine ⟨D,d,hd,?_,by rw [hmap,flow_reference,map_zero],fun i=> by
    rw [hmap,flow_numerator,map_neg]⟩
  cases b
  · change q∣r*Lv δ q
    exact dvd_mul_of_dvd_left hqr _
  · have hchar :CharP (kq k) p :=
      charP_of_injective_ringHom (f :=j.comp zMG)
        ((zxb (zpm k) (kq k)).comp PowerSeries.C_injective) p
    have hm:r.Monic:=M.monic.map j
    apply dvd_of_kills (p:=p) D hm.ne_zero ((M.monic.natDegree_map j).trans_lt M.physical_tame)
      hq hqr
    change r.derivative*Lv δ r - Lv δ r*r.derivative=0
    rw [mul_comm r.derivative,sub_self]
end
end P5_7_3_3_4_1_3_1_2
end
section
set_option autoImplicit true
set_option maxHeartbeats 600000
namespace P5_7_3_3_4_1_3_1_2
noncomputable section
open Polynomial qAjZDhd qaJ7jxd
private theorem preserves_localization {U R K:Type} [za6 U] [za6 R]
    [zrb K] [zZE U R] [zZE U K] [zZE R K] [zsf U R K]
    (S:Submonoid U) [IsLocalization S R]
    (D:Derivation ℤ U U) (d:Derivation ℤ K K)
    (h : ∀ x,d (algebraMap U K x)=algebraMap U K (D x)) (x :R) :
    ∃ y :R,d (algebraMap R K x)=algebraMap R K y := by
  let j:=algebraMap R K
  let l:=algebraMap U R
  let t:=algebraMap U K
  have ht (z :U) :t z=j (l z) :=zG3 U R K z
  obtain ⟨⟨a,s⟩,hs⟩:=zg4 S x
  let u:=(z0j R s).unit
  have hu: (u:R)=l s :=(z0j R s).unit_spec
  have hunit :IsUnit (t s) := by
    rw [ht]
    exact (z0j R s).map j
  have hsK:j (x*l s)=j (l a) :=congrArg j hs
  rw [map_mul,← ht,← ht] at hsK
  have hx :j x=t a/t s :=(eq_div_iff hunit.ne_zero).mpr hsK
  have hinv :j (↑u⁻¹:R)=(t s)⁻¹:= by
    apply eq_inv_of_mul_eq_one_left
    rw [ht,← map_mul,← hu,Units.inv_mul,map_one]
  refine ⟨(↑u⁻¹:R)^2*(l s*l (D a)-l a*l (D s)),?_⟩
  change d (j x)=j _
  rw [hx,d.leibniz_div,map_mul,map_pow,map_sub,map_mul,map_mul,hinv]
  rw [show d (t a)=t (D a) from h a,show d (t s)=t (D s) from h s]
  simp only [smul_eq_mul,← ht]
private theorem integral_product {R L:Type} [za6 R] [zrb L] [zZE R L]
    (ys :Multiset L) (v :L→L) (h : ∀ y∈ys,IsIntegral R (v y)) (i:ℕ) :
    IsIntegral R (((ys.map fun y=>(z7y:L[X])-Polynomial.C (v y)).prod).coeff i) := by
  classical
  rw [Multiset.prod_eq_prod_coe]
  apply Polynomial.isIntegral_coeff_prod
  rintro ⟨f,⟨n,hn⟩⟩ - j
  obtain ⟨y,hy,rfl⟩:=Multiset.mem_map.mp (Multiset.count_pos.mp (n.zero_le.trans_lt hn))
  simp [coeff_X,coeff_C,IsIntegral.sub,apply_ite (IsIntegral R),
    isIntegral_one,isIntegral_zero,h y hy]
local instance (k :Type) [zrb k] :zZE ℤ (Generic k) :=Ring.toIntAlgebra _
private theorem b4F {k :Type} [zrb k] :
    zq4 (ek (k :=k)) :=
  (zxb (kq k)[X] (Generic k)).comp
    (zTo _ (zxb (zpm k) (kq k)))
private theorem generic_denom_ne_zero {k :Type} [zrb k] {p:ℕ} [CharP k p]
    (M:LocalMark k p) :ek (denom M)≠0:= by
  apply (map_ne_zero_iff _ b4F).mpr
  rw [denom_eq]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (fun h =>
    M.branch_nonzero (by rw [h,map_zero]))
private theorem integral_normalized {k R:Type} [zrb k] [za6 R] [IsDomain R]
    [IsDiscreteValuationRing R] [zZE R (Generic k)] [z0o R (Generic k)]
    {p:ℕ} [CharP k p] (tame :TameLog) (M:LocalMark k p) (b:Bool)
    (d:Derivation ℤ (Generic k) (Generic k)) (π:R) (hπ:Irreducible π)
    (hreg : ∀ x :R,∃ y :R,d (algebraMap R (Generic k) x)=algebraMap R (Generic k) y)
    (htan : ∃ x :R,d (algebraMap R (Generic k) π)=algebraMap R (Generic k) (π*x))
    (ha :d (ek (reference M.a))=0)
    (hc : ∀ n,d (ek (M.f.coeff n)) = -ek ((M.numerator b).coeff n))
    (i:ℕ) :IsIntegral R (ek ((Fr M b).coeff i)/ek (denom M)) := by
  let K:=Generic k
  let L:=AlgebraicClosure K
  let ψ:=algebraMap K L
  have hgen:=b4F (k :=k)
  let:CharP K p:=charP_of_injective_ringHom
    (f :=ek.comp (Polynomial.C.comp zMG))
    (hgen.comp (Polynomial.C_injective.comp PowerSeries.C_injective)) p
  have hb:branchPoly M.f M.g M.a≠0:= fun h =>
    M.branch_nonzero (by rw [h,map_zero])
  have hden:bL9 (denom M)≠0 :=
    (map_ne_zero ψ).mpr (generic_denom_ne_zero M)
  let F:=M.f.map ek
  let a :=ek (reference M.a)
  change M.f.resultant M.f.derivative M.g (M.g - 1)*M.f.eval (reference M.a)≠0 at hb
  obtain ⟨hbR,hbA⟩:=mul_ne_zero_iff.mp hb
  have hres :ek (M.f.resultant M.f.derivative M.g (M.g - 1))≠0:= fun h =>
    hbR (hgen (h.trans (map_zero (ek (k :=k))).symm))
  have hg:0<M.g:=(by decide :0<2).trans_le M.two_le
  have hsep:F.Separable :=
    separable_map_of_resultant_derivative_padded_ne_zero (m:=M.g)
      (ek (k :=k)) M.f M.degree.le hg hres
  have hdeg:F.natDegree<p :=
    (natDegree_map_eq_of_injective hgen M.f).trans_lt (M.degree.trans_lt M.tame)
  have hEval (P:Equation k) (y :L) : (P.map ek).eval₂ ψ y=(P.map bL9).eval y := by
    rw [eval₂_map,eval_map]
    rfl
  have href : (M.f.map bL9).eval (ψ a)≠0:= by
    change (M.f.map bL9).eval (bL9 (reference M.a))≠0
    rw [eval_map_apply]
    exact fun h=>hbA (splitMap_injective (h.trans (map_zero (bL9 (k :=k))).symm))
  have hf :M.f.map bL9≠0:= by
    intro h
    exact href (by rw [h,eval_zero])
  have hC:Lv d F = - (M.numerator b).map ek := by
    ext n:1
    change d ((M.f.map ek).coeff n)= _
    rw [coeff_map,coeff_neg,coeff_map,hc]
  let v (y :L) :=((M.numerator b).map bL9).eval y/(M.denominator.map bL9).eval y
  have hv (y :L) (hy :y∈(M.f.map bL9).roots) :IsIntegral R (v y) := by
    have hy' : F.eval₂ ψ y=0:=(hEval M.f y).trans ((mem_roots hf).mp hy)
    have hya :y≠ψ a := fun e=>href (e ▸ (mem_roots hf).mp hy)
    have h:=tame R (Generic k) (AlgebraicClosure (Generic k)) p d π
      hπ hreg htan F a y hsep hdeg ha hy' hya
    have hn : - (Lv d F).eval₂ ψ y=((M.numerator b).map bL9).eval y := by
      rw [hC,eval₂_neg,neg_neg,hEval]
    have he :F.derivative.eval₂ ψ y*(y-ψ a)=(M.denominator.map bL9).eval y := by
      change (M.f.map ek).derivative.eval₂ ψ y*(y-ψ a)= _
      rw [derivative_map,hEval]
      simp only [LocalMark.denominator,zNl,z3A,map_X,map_C,
        eval_mul,eval_sub,eval_X,eval_C]
      rfl
    rw [hn,he] at h
    exact h
  let Q:=((M.f.map bL9).roots.map fun y=>(z7y:L[X])-Polynomial.C (v y)).prod
  have hQi:IsIntegral R (Q.coeff i) :=integral_product _ v hv i
  let V:=ek ((Fr M b).coeff i)/ek (denom M)
  have hscaled:ψ (ek ((Fr M b).coeff i)) =
      ψ (ek (denom M))*Q.coeff i:= by
    have h:=congrArg (fun P:L[X]=>P.coeff i) (scaled_product M b hden)
    change bL9 ((Fr M b).coeff i)=bL9 (denom M)*Q.coeff i
    simpa only [Q,v,coeff_map,coeff_C_mul] using h
  have hV:ψ V= Q.coeff i:= by
    change ψ (_/_)= _
    rw [map_div₀]
    exact (div_eq_iff hden).mpr (hscaled.trans (mul_comm _ _))
  have hI:IsIntegral R (ψ V) :=hV.symm ▸ hQi
  exact (isIntegral_algebraMap_iff (R:=R) (A:=Generic k)
    (B:=AlgebraicClosure (Generic k))).mp hI
private theorem aG3 {U R K:Type} [za6 U] [za6 R] [zrb K]
    [zZE U R] [zZE U K] [zZE R K] [zsf U R K]
    [z0o U K] [z0o R K] [IsIntegrallyClosed R]
    (S:Submonoid U) [IsLocalization S R] (n m:U) (hm:algebraMap U K m≠0)
    (h:IsIntegral R (algebraMap U K n/algebraMap U K m)) :
    ∃ e :S,m∣(e :U)*n:= by
  let t:=algebraMap U K
  let j:=algebraMap R K
  let V:=t n/t m
  have ht (z :U) :j (algebraMap U R z)=t z :=(zG3 U R K z).symm
  obtain ⟨c,hce :j c=V⟩:=IsIntegrallyClosed.isIntegral_iff.mp h
  obtain ⟨⟨u,e⟩,he⟩:=zg4 S c
  have hh:j (c*algebraMap U R e)=j (algebraMap U R u) :=congrArg j he
  rw [map_mul,ht,ht,hce] at hh
  have hv :V*t m=t n:=div_mul_cancel₀ _ hm
  refine ⟨e,u,zxb U K ?_⟩
  change t ((e :U)*n)=t (m*u)
  rw [map_mul,map_mul,← hh,← hv]
  ring
private theorem descend_at_prime {U K:Type} [za6 U] [IsDedekindDomain U]
    [zrb K] [zZE U K] [z0o U K]
    (q:U) (hq:Prime q) (D:Derivation ℤ U U) (d:Derivation ℤ K K)
    (hd : ∀ x,d (algebraMap U K x)=algebraMap U K (D x)) (htD:q∣D q)
    (n m:U) (hm:algebraMap U K m≠0)
    (H : ∀ (R:Type) [za6 R] [IsDomain R] [IsDiscreteValuationRing R]
      [zZE R K] [z0o R K] (π:R),
      Irreducible π →
      (∀ x :R,∃ y :R,d (algebraMap R K x)=algebraMap R K y) →
      (∃ y :R,d (algebraMap R K π)=algebraMap R K (π*y)) →
      IsIntegral R (algebraMap U K n/algebraMap U K m)) :
    ∃ e :U,¬q∣e∧m∣e*n:= by
  let t:=algebraMap U K
  let J:Ideal U:=zye ({q} : Set U)
  let:J.IsPrime :=Ideal.isPrime_span_singleton_of_prime hq
  let R:=Localization.AtPrime J
  let l:=algebraMap U R
  let:zZE R K:=IsLocalization.localizationAlgebraOfSubmonoidLe R K J.primeCompl
    (nonZeroDivisors U) J.primeCompl_le_nonZeroDivisors
  let:zsf U R K:=IsLocalization.localization_isScalarTower_of_submonoid_le R K
    J.primeCompl (nonZeroDivisors U) J.primeCompl_le_nonZeroDivisors
  let j:=algebraMap R K
  let:z0o R K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization J.primeCompl R K
  let:IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain U (P:=J)
      (fun h=>hq.ne_zero (Ideal.span_singleton_eq_bot.mp h)) R
  have ht (z :U) :t z=j (l z) :=zG3 U R K z
  have hπ:Irreducible (l q) := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I:=J)]
    change (zye ({q} : Set U)).map l=zye {l q}
    rw [Ideal.map_span,Set.image_singleton]
  obtain ⟨z,hz⟩:=htD
  have htan : ∃ a :R,d (j (l q))=j (l q*a) := by
    refine ⟨l z,?_⟩
    rw [← ht,show d (t q)=t (D q) from hd q,hz,map_mul,map_mul,← ht,← ht]
  have hInt:=H R (l q) hπ (preserves_localization J.primeCompl D d hd) htan
  obtain ⟨e,he⟩:=aG3 J.primeCompl n m hm hInt
  exact ⟨e,fun h=>e.prop (Ideal.mem_span_singleton.mpr h),he⟩
theorem proof :qaJ7jxd.c2 := by
  intro tame k _ p _ M b q hq hqr i
  obtain ⟨D,d,hd,hD,ha,hc⟩:=operators M b q hq hqr
  refine descend_at_prime q hq.prime D d hd hD
    _ _ (generic_denom_ne_zero M) ?_
  intro R _ _ _ _ _ π hπ hreg htan
  exact integral_normalized tame M b d π hπ hreg htan ha hc i
end
end P5_7_3_3_4_1_3_1_2
end
section
set_option autoImplicit true
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P5_7_3_3_4_1_7_2
noncomputable section
open Polynomial P5_7_3_3_4_1_7
open qL2osVa (Series)
open q1kuFjb (mapTwice)
theorem seedEmbedding_injective :zq4 jz :=
  (algebraMap (FractionRing Series) aQ).injective.comp (zxb _ _)
private theorem coeff_ramify (n:ℕ) (hn:n≠0) (a :DoubleSeries) (i:ℕ) :
    z2o (n*i) (ramify jz n hn a) =
      jz (z2o i a) := by
  simp [ramify]
private theorem ramify_injective (n:ℕ) (hn:n≠0) :
    zq4 (ramify jz n hn) := by
  intro a b h
  apply zub
  intro i
  exact seedEmbedding_injective (by
    simpa only [coeff_ramify] using congrArg (z2o (n*i)) h)
@[simp] theorem centre_ramify (n:ℕ) (hn:n≠0) (a :DoubleSeries) :
    zbO (ramify jz n hn a) =
      jz (physicalCentre a) := by
  simp [ramify,physicalCentre,← PowerSeries.coeff_zero_eq_constantCoeff]
@[simp] theorem coeff_mapTwice {R S:Type} [za6 R] [za6 S] (e :R →+* S)
    (T:R[X][X]) (i k :ℕ) : ((mapTwice e T).coeff i).coeff k=e ((T.coeff i).coeff k) := by
  simp [mapTwice]
theorem mapTwice_injective {R S:Type} [za6 R] [za6 S] {e :R →+* S}
    (he :zq4 e) :zq4 (mapTwice e) :=
  zTo _ (zTo _ he)
private theorem ramify_div (n:ℕ) (hn:n≠0) {a :DoubleSeries} {d:ℕ}
    (u:DoubleSeriesˣ) {b:zpm aQ}
    (h:ramify jz n hn a =
      ramify jz n hn ((zWv:DoubleSeries)^d*(u:DoubleSeries))*b) :
    ∃ c:DoubleSeries,ramify jz n hn c=b:= by
  let e :=ramify jz n hn
  have hx :e (zWv:DoubleSeries)=zWv ^n:= by simp [e,ramify]
  have hdvd: (zWv:DoubleSeries)^d∣a := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro i hi
    apply seedEmbedding_injective
    have hl:n*i<n*d:=Nat.mul_lt_mul_of_pos_left hi (zOl hn)
    have hh:e a=zWv ^(n*d)*(e u*b) := by
      change e a=e ((zWv:DoubleSeries)^d*(u:DoubleSeries))*b at h
      simpa only [map_mul,map_pow,hx,← pow_mul,mul_assoc] using h
    have hc:=congrArg (z2o (n*i)) hh
    rw [show z2o (n*i) (e a)= _ from coeff_ramify n hn a i,
      PowerSeries.coeff_X_pow_mul',ite_eq_right (Nat.not_le_of_lt hl)] at hc
    simpa using hc
  obtain ⟨q,hq⟩:=hdvd
  refine ⟨↑u⁻¹*q,?_⟩
  change e (↑u⁻¹*q)=b
  have hne :e (zWv ^d*(u:DoubleSeries))≠0:= by
    exact (map_ne_zero_iff _ (ramify_injective n hn)).mpr
      (mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) u.ne_zero)
  apply mul_left_cancel₀ hne
  calc
    e (zWv ^d*(u:DoubleSeries))*e (↑u⁻¹*q)=e a := by
      rw [← map_mul,hq]
      congr 1
      rw [mul_assoc,← mul_assoc (u:DoubleSeries),Units.mul_inv,one_mul]
    _ = _:=h
theorem descend {f :LocalEquation} {g d j n:ℕ} (hn:n≠0)
    (h:LocalGuard f g d j) (T: (zpm aQ)[X][X])
    (hT:mapTwice (ramify jz n hn) (numerator f g) =
      C (C (ramify jz n hn (denominator f g)))*T)
    (hm:T.Monic)
    (hc:CentreShape (mapTwice zbO T) j
      (jz (physicalCentre (f.coeff g))) (jz (physicalCentre (f.coeff j)))) :
    ∃ Q:DoubleSeries[X][X],numerator f g=C (C (denominator f g))*Q∧Q.Monic ∧
      CentreShape (mapTwice physicalCentre Q) j (physicalCentre (f.coeff g))
        (physicalCentre (f.coeff j)) := by
  let e :=ramify jz n hn
  obtain ⟨u,hu,hd⟩:=h.2.2.1
  obtain ⟨v,hv⟩:=h.2.1.mul hu
  have he :denominator f g=zWv ^d*(v :DoubleSeries) := by
    rw [denominator,hd,hv]
    ac_rfl
  have hb (i k :ℕ) : ((T.coeff i).coeff k)∈Set.range e := by
    apply ramify_div n hn v
    have hh:=congrArg (fun F: (zpm aQ)[X][X]=>(F.coeff i).coeff k) hT
    simpa only [coeff_mapTwice,coeff_C_mul,he] using hh
  have hl:T∈lifts (mapRingHom e) := by
    apply (lifts_iff_coeff_lifts T).mpr
    intro i
    exact (lifts_iff_set_range _).mp ((lifts_iff_coeff_lifts _).mpr (hb i))
  obtain ⟨Q,hQ⟩:=(mem_lifts _).mp hl
  change mapTwice e Q=T at hQ
  have heinj:=ramify_injective n hn
  have hrs :mapTwice jz (mapTwice physicalCentre Q) =
      mapTwice zbO T:= by
    rw [← hQ]
    apply zXJ
    intro i
    apply zXJ
    intro k
    simp only [coeff_mapTwice,e,centre_ramify]
  have hMQ: (mapTwice e Q).Monic:=hQ.symm ▸ hm
  refine ⟨Q,mapTwice_injective heinj ?_,
    monic_of_injective (zTo _ heinj) hMQ,?_,?_⟩
  · rw [map_mul,hQ]
    have hC:mapTwice e (C (C (denominator f g)))=C (C (e (denominator f g))) := by
      simp [mapTwice]
    rw [hC]
    exact hT
  · intro i hi
    apply zTo _ seedEmbedding_injective
    have HH :=congrArg (fun F:aQ[X][X]=>F.coeff i) hrs
    change (mapTwice jz (mapTwice physicalCentre Q)).coeff i =
      (mapTwice zbO T).coeff i at HH
    rw [hc.1 i hi] at HH
    simpa [mapTwice] using HH
  · apply seedEmbedding_injective
    have HH :=congrArg (fun F:aQ[X][X]=>(F.coeff j).eval 0) hrs
    have ce :=hc.2
    rw [← HH] at ce
    simpa [mapTwice,map_mul] using ce
end
end P5_7_3_3_4_1_7_2
end
section
set_option autoImplicit true
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P5_7_3_3_4_1_7_2
noncomputable section
open Polynomial P5_7_3_3_4_1_7
open qL2osVa (Series)
abbrev pO:DoubleSeries →+* Series :=zS4 zbO
@[simp] theorem coeff_mapAdd {R S:Type} [Semiring R] [Semiring S] (D:R →+ S)
    (f :R[X]) (i:ℕ) : (mapAdd D f).coeff i=D (f.coeff i) := by
  change (AddMonoidAlgebra.map D f.toFinsupp).coeff i=D (f.toFinsupp.coeff i)
  rw [AddMonoidAlgebra.coeff_map,Finsupp.mapRange_apply]
variable {R:Type} [za6 R]
@[simp] theorem coeff_jetDerivative (f : (zpm (zpm R))[X]) (i:ℕ) :
    (jetDerivative f).coeff i=Lv (f.coeff i) :=coeff_mapAdd _ _ _
theorem deg_jetDerivative (f : (zpm (zpm R))[X]) :
    (jetDerivative f).natDegree≤f.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_jetDerivative,coeff_eq_zero_of_natDegree_lt hi]
  apply zub
  intro n
  simp [Lv]
private def first (a :zpm (zpm R)) :zpm R :=
  PowerSeries.mk fun i=>z2o 1 (z2o i a)
theorem seed_first (f : (zpm (zpm R))[X]) (s :zpm R) :
    ((jetDerivative f).map (zS4 zbO)).eval s =
      first (f.eval (zS4 zMG s)) := by
  let e :zpm R →+* zpm (zpm R) :=zS4 zMG
  have ha (a b:zpm (zpm R)) :first (a+b)=first a+first b:= by
    ext n
    simp [first]
  have hm (a :zpm (zpm R)) (b:zpm R) :first (a*e b)=first a*b:= by
    apply zub
    intro n
    simp only [first,PowerSeries.coeff_mk]
    change _=z2o n (first a*b)
    rw [PowerSeries.coeff_mul n a (e b),map_sum,PowerSeries.coeff_mul n (first a) b]
    apply Finset.sum_congr rfl
    intro i _
    simp only [PowerSeries.coeff_one_mul,e,zVO,PowerSeries.constantCoeff_C,
      PowerSeries.coeff_C,one_ne_zero,ite_false,zero_mul,add_zero,first,PowerSeries.coeff_mk]
  have hc (a :zpm (zpm R)) :
      zS4 zbO (Lv a)=first a := by
    ext n
    simp [Lv,first,← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_derivative]
  change _=first (f.eval (e s))
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    have he :jetDerivative (f+g)=jetDerivative f+jetDerivative g:= by
      apply zXJ
      intro i
      simp only [coeff_jetDerivative,coeff_add]
      apply zub
      intro n
      simp [Lv]
    simp only [he,Polynomial.map_add,eval_add,ha,hf,hg]
  | monomial i a =>
    have he :jetDerivative (monomial i a)=monomial i (Lv a) := by
      apply zXJ
      intro n
      by_cases h:i=n
      · simp [h]
      · simp only [coeff_jetDerivative,coeff_monomial,h,ite_false]
        apply zub
        intro k
        simp [Lv]
    rw [he,map_monomial,eval_monomial,eval_monomial,← map_pow,hm,hc]
end
end P5_7_3_3_4_1_7_2
end
section
set_option autoImplicit true
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P5_7_3_3_4_1_7_2
noncomputable section
open Polynomial P5_7_3_3_4_1_7
open qL2osVa (Series)
private theorem common_root_resultant {R:Type} [za6 R] {F G:R[X]} {m n:ℕ}
    (hm:F.natDegree≤ m) (hn:G.natDegree≤n) (hpos :m≠0) (s :R)
    (hf :F.eval s=0) (hg:G.eval s=0) :F.resultant G m n=0:= by
  obtain ⟨a,b,_,_,hab⟩:=exists_mul_add_mul_eq_C_resultant F G hm hn (Or.inl hpos)
  simpa [hf,hg] using (congrArg (eval s) hab).symm
private theorem seedDet_ne {f :LocalEquation} {g d j:ℕ} (h:LocalGuard f g d j) :
    pO (det f g)≠0:= by
  obtain ⟨u,hu,hdet⟩:=h.2.2.1
  rw [hdet,map_mul,map_pow,PowerSeries.map_X]
  exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (hu.map pO).ne_zero
theorem seedSeparant_ne {f :LocalEquation} {g d j:ℕ} (hg:2≤g)
    (h:LocalGuard f g d j) {s :Series} (hs : (seedFibre f).eval s=0) :
    (seedFibre f).derivative.eval s≠0:= by
  have hd: (seedFibre f).natDegree≤g:=natDegree_map_le.trans h.1
  intro hz
  apply seedDet_ne h
  rw [det,← resultant_map_map,← derivative_map]
  exact common_root_resultant hd ((natDegree_derivative_le _).trans (zIu hd 1))
    (by omega) s hs hz
private theorem cutter_degree {R:Type} [za6 R]
    (f q:R[X]) {g:ℕ} (hg:2≤g) (hf :f.natDegree≤g) (hq:q.natDegree≤g) :
    (an1 f q).natDegree≤g:= by
  have ha : (f.map (embed:R →+* R[X][X])).derivative.natDegree≤g - 1 :=
    (natDegree_derivative_le _).trans (zIu (natDegree_map_le.trans hf) _)
  have hz : (C (z7y:R[X][X])-(z7y:R[X][X][X])).natDegree≤1 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) natDegree_X_le)
  have hw: (C (C (z7y:R[X])) :R[X][X][X]).natDegree=0:=natDegree_C _
  unfold an1
  dsimp only
  apply natDegree_add_le_of_degree_le
  · exact natDegree_mul_le.trans ((Nat.add_le_add ha hz).trans (by omega))
  · exact natDegree_mul_le.trans (by rw [hw,zero_add]; exact natDegree_map_le.trans hq)
private theorem resultant_root {R A:Type} [za6 R] [za6 A] (e :R →+* A)
    (f q:R[X]) {g:ℕ} (hg:2≤g) (hf :f.natDegree≤g) (hq:q.natDegree≤g)
    (w z s :A) (hs :f.eval₂ e s=0)
    (hv :f.derivative.eval₂ e s*(z - s)+w*q.eval₂ e s=0) :
    eval₂RingHom (eval₂RingHom e w) z ((f.map embed).resultant (an1 f q) g g)=0:= by
  let E :=eval₂RingHom (eval₂RingHom e w) z
  have hl:E.comp embed=e := by
    apply zz4
    intro a
    simp [E,embed]
  have hZ:E (z7y:R[X][X])=z :=eval₂_X _ _
  have hW:E (C (z7y:R[X]))=w:= by simp [E]
  have hF: (f.map embed).eval₂ E s=0:= by rwa [eval₂_map,hl]
  have hG: (an1 f q).eval₂ E s=0:= by
    simpa only [an1,derivative_map,eval₂_add,eval₂_mul,eval₂_sub,eval₂_C,
      eval₂_X,hZ,hW,eval₂_map,hl] using hv
  obtain ⟨a,b,_,_,hab⟩:=exists_mul_add_mul_eq_C_resultant (f.map embed)
    (an1 f q) (natDegree_map_le.trans hf) (cutter_degree f q hg hf hq) (Or.inl (by omega))
  change E ((f.map embed).resultant (an1 f q) g g)=0
  simpa only [map_add,map_mul,coe_eval₂RingHom,eval₂_C,hF,hG,zero_mul,zero_add]
    using (congrArg (eval₂RingHom E s) hab).symm
theorem normRoot {A:Type} [za6 A] [IsDomain A]
    {f :LocalEquation} {g d j:ℕ} (hg:2≤g) (h:LocalGuard f g d j)
    {Q:DoubleSeries[X][X]} (hq:numerator f g=C (C (denominator f g))*Q)
    {s :Series} (hs : (seedFibre f).eval s=0)
    (e :Series →+* A) (he :zq4 e) (w v :A)
    (hv :e (((jetDerivative f).map pO).eval s) +
      e ((seedFibre f).derivative.eval s)*v=0) :
    Q.eval₂ (eval₂RingHom (e.comp pO) w) (e s+w*v)=0:= by
  let φ:=e.comp pO
  let z :=e s+w*v
  let E :=eval₂RingHom (eval₂RingHom φ w) z
  have hEval (F:LocalEquation) :F.eval₂ φ (e s)=e ((F.map pO).eval s) := by
    rw [eval_map,hom_eval₂]
  have hf :f.eval₂ φ (e s)=0:= by
    rw [hEval]
    change e ((seedFibre f).eval s)=0
    rw [hs,map_zero]
  have hj:f.derivative.eval₂ φ (e s)*(z-e s) +
      w*(jetDerivative f).eval₂ φ (e s)=0:= by
    simp only [hEval,z,add_sub_cancel_left,← derivative_map]
    change e ((seedFibre f).derivative.eval s)*(w*v) +
      w*e (((jetDerivative f).map pO).eval s)=0
    calc
      _=w*(e (((jetDerivative f).map pO).eval s) +
          e ((seedFibre f).derivative.eval s)*v) := by ring
      _=0:= by rw [hv,mul_zero]
  have hz :=resultant_root φ f (jetDerivative f) hg h.1
    ((deg_jetDerivative f).trans h.1) w z (e s) hf hj
  change E (numerator f g)=0 at hz
  rw [hq,map_mul] at hz
  have hne :E (C (C (denominator f g)))≠0:= by
    simp only [E,coe_eval₂RingHom,eval₂_C,φ,zQb]
    apply (map_ne_zero_iff e he).mpr
    rw [denominator,map_mul]
    exact mul_ne_zero (h.2.1.map pO).ne_zero (seedDet_ne h)
  exact (mul_eq_zero.mp hz).resolve_left hne
end
end P5_7_3_3_4_1_7_2
end
section
set_option autoImplicit true
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P5_7_3_3_4_1_7_2
noncomputable section
open Polynomial P5_7_3_3_4_1_7
open qL2osVa (Series SeriesField)
open q1kuFjb (mapTwice)
open cu (L)
theorem specialize {f :LocalEquation} {g d j:ℕ} (hg:2≤g) (h:LocalGuard f g d j)
    {Q:DoubleSeries[X][X]} (hq:numerator f g=C (C (denominator f g))*Q)
    (hm:Q.Monic)
    (hc:CentreShape (mapTwice physicalCentre Q) j (physicalCentre (f.coeff g))
      (physicalCentre (f.coeff j))) {s :Series} (hs0:zbO s=0)
    (hs : (seedFibre f).eval s=0) : ∃ v :Series,ZeroJet f s v := by
  let e :=algebraMap Series SeriesField
  let a :=(seedFibre f).derivative.eval s
  let b:=((jetDerivative f).map pO).eval s
  let u := -e b/e a
  have he :zq4 e :=zxb _ _
  have hne :e a≠0:=(map_ne_zero_iff e he).mpr (seedSeparant_ne hg h hs)
  have hu:e b+e a*u=0:= by
    change e b+e a*(-e b/e a)=0
    rw [mul_comm (e a),neg_div,neg_mul,div_mul_cancel₀ _ hne,add_neg_cancel]
  let S:= Q.map (eval₂RingHom pO 1)
  have hS:IsIntegral Series (e s+u) := by
    refine ⟨S,hm.map _,?_⟩
    have hm1 :e.comp (eval₂RingHom pO 1)=eval₂RingHom (e.comp pO) 1 := by
      apply z86 <;> simp
    change (Q.map (eval₂RingHom pO 1)).eval₂ e (e s+u)=0
    rw [eval₂_map,hm1]
    simpa only [one_mul] using normRoot hg h hq hs e he 1 u hu
  obtain ⟨y,hy⟩:=IsIntegrallyClosed.algebraMap_eq_of_integral hS
  let v :=y - s
  have hv :e v=u:= by
    change e (y - s)=u
    rw [map_sub,hy,add_sub_cancel_left]
  have hj:b+a*v=0:= by
    apply he
    simpa only [map_add,map_mul,hv,map_zero] using hu
  have hjetC:C b+C a*C v=(0:Series[X]) := by
    rw [← map_mul,← map_add,hj,map_zero]
  have hline :=normRoot hg h hq hs (C:Series →+* Series[X]) C_injective z7y (C v) hjetC
  let B:=mapTwice physicalCentre Q
  let k :Series →+* L:=zbO
  have hcomp:k.comp pO=k.comp physicalCentre := by
    apply zz4
    intro w
    change zbO (pO w)=k (physicalCentre w)
    rw [← zW1 (pO w),zVO,
      zW1 w]
    rfl
  have hE : (mapRingHom k).comp (eval₂RingHom ((C:Series →+* Series[X]).comp pO)
          z7y)=(mapRingHom k).comp (mapRingHom physicalCentre) := by
    apply z86
    · intro x
      simp only [zQb,coe_eval₂RingHom,eval₂_C,coe_mapRingHom,map_C]
      exact congrArg C (DFunLike.congr_fun hcomp x)
    · simp
  have hred:B.eval₂ (mapRingHom k) (z7y*C (k v))=0:= by
    have H :=congrArg (mapRingHom k) hline
    rw [hom_eval₂,map_zero,hE] at H
    have hs0' : k s=0:=hs0
    simp only [map_add,map_mul,coe_mapRingHom,Polynomial.map_C,Polynomial.map_X,
      hs0',C_0,zero_add] at H
    change (Q.map (mapRingHom physicalCentre)).eval₂ _ _=0
    rw [eval₂_map]
    exact H
  have hshape : (z7y:L[X][X])^j∣B.map (mapRingHom k) := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro i hi
    have hi' : B.coeff i=0:=hc.1 i hi
    simp [hi']
  refine ⟨v,?_,?_⟩
  · change k v=0
    by_contra hnv
    obtain ⟨H,hH⟩:=hshape
    have hz :=hred
    rw [← eval_map,hH,eval_mul,eval_pow,eval_X] at hz
    have hx : (z7y:L[X])*C (k v)≠0:=mul_ne_zero X_ne_zero (C_ne_zero.mpr hnv)
    have hz' := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hx)
    have hzero : (H.coeff 0).eval 0=0:= by
      let m:=evalRingHom (0:L)
      have hm0:m ((z7y:L[X])*C (k v))=0:= by simp [m]
      have ht:=congrArg m hz'
      change m (H.eval ((z7y:L[X])*C (k v)))=m 0 at ht
      rw [← eval_map_apply,hm0,eval_zero_map,map_zero] at ht
      simpa only [m,coe_evalRingHom,← coeff_zero_eq_eval_zero] using ht
    have hj' : ((B.map (mapRingHom k)).coeff j).eval 0=(H.coeff 0).eval 0:= by
      rw [hH]
      exact congrArg (eval 0) (by simpa only [zero_add] using coeff_X_pow_mul H j 0)
    have hc' : k (physicalCentre (f.coeff g)) *
        ((B.map (mapRingHom k)).coeff j).eval 0=k (physicalCentre (f.coeff j)) := by
      simpa only [map_mul,coeff_map,coe_mapRingHom,eval_zero_map] using congrArg k hc.2
    rw [hj',hzero,mul_zero] at hc'
    exact ((h.2.2.2.2.map k).ne_zero) hc'.symm
  · have hh:=seed_first f s
    change b=seedFirst (f.eval (zS4 zMG s)) at hh
    rw [← hh]
    exact hj
end
end P5_7_3_3_4_1_7_2
end
