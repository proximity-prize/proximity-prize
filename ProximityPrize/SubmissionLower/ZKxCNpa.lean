import ProximityPrize.SubmissionLower.ZZpExZa
import ProximityPrize.SubmissionLower.ZgoWlLc
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.IsSeparable → zw7, CommRing → za6, Field → zrb, Function.Injective → zq4, IsFractionRing → z0o, IsFractionRing.injective → zxb, IsLocalization → zNo, IsLocalization.mk' → zzm, IsScalarTower → zsf, LinearMap.toSpanSingleton → zZj, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.map_injective → zTo, Polynomial.ringHom_ext → z86, RingHom.IsIntegralElem → zPI, RingHom.congr_fun → zLs
section
namespace qCtoYwb
noncomputable section
open Polynomial
open cu (L)
open qqV3gre
abbrev tu:=aQ[X]
abbrev Simple (y :EC) :=IntermediateField.adjoin PhysicalField ({y} : Set EC)
abbrev point (y :EC) :Simple y :=⟨y,IntermediateField.mem_adjoin_simple_self _ _⟩
def baseIn (y :EC) :tu →+* Simple y :=
 (algebraMap PhysicalField (Simple y)).comp (algebraMap tu PhysicalField)
theorem baseIn_injective (y :EC) :zq4 (baseIn y) :=
 (algebraMap PhysicalField (Simple y)).injective.comp (zxb _ _)
def scalar (u:L) :tu:=C (algebraMap L aQ u)
def reference (f :tu[X]) (u:L) :tu:=f.eval (scalar u)
def ratio (y :EC) (u v :L) :Simple y :=
 (point y - baseIn y (scalar u))/(point y - baseIn y (scalar v))
abbrev primeIdeal (π:tu) :Ideal tu:=Ideal.span {π}
instance (π:tu) [h:Fact (Irreducible π)] : (primeIdeal π).IsPrime :=
 (Ideal.span_singleton_prime h.out.ne_zero).mpr h.out.prime
def aDm (π:tu) [h:Fact (Irreducible π)] :IsDedekindDomain.HeightOneSpectrum tu :=
 ⟨primeIdeal π,inferInstance,Ideal.span_singleton_eq_bot.not.mpr h.out.ne_zero⟩
abbrev Local (π:tu) [Fact (Irreducible π)] :=(aDm π).valuationSubringAtPrime PhysicalField
instance (π:tu) [Fact (Irreducible π)] :zNo (primeIdeal π).primeCompl (Local π) :=
 inferInstanceAs (zNo (aDm π).asIdeal.primeCompl
  ((aDm π).valuationSubringAtPrime PhysicalField))
def localIn (π:tu) [Fact (Irreducible π)] (y :EC) :Local π →+* Simple y :=
 (algebraMap PhysicalField (Simple y)).comp (algebraMap (Local π) PhysicalField)
def IntegralAt (π:tu) [Fact (Irreducible π)] (y :EC) (w:Simple y) :Prop :=
 ∃ Q: (Local π)[X],Q.Monic∧Q.eval₂ (localIn π y) w=0
def PreservesLocal (π:tu) [Fact (Irreducible π)] (y :EC)
    (D:Derivation ℤ (Simple y) (Simple y)) :Prop :=
  ∀ a :Local π,∃ b:Local π,D (localIn π y a)=localIn π y b
def TangentAt (π:tu) [Fact (Irreducible π)] (y :EC)
    (D:Derivation ℤ (Simple y) (Simple y)) :Prop :=
  ∃ b:Local π,D (baseIn y π)=baseIn y π*localIn π y b
end
end qCtoYwb
end
section
namespace q0n1P7d
noncomputable section
open Polynomial qqV3gre
open cu (L)
open scoped WithZero nonZeroDivisors
open private efc adG aMX b4t from ProximityPrize.SubmissionLower.Y
abbrev seedVal:Valuation aQ ℤᵐ⁰:=Valued.v
abbrev coeffField:aQ[X] →+* PhysicalField:=algebraMap _ _
def gauss :Valuation PhysicalField ℤᵐ⁰ :=
  (efc seedVal).extendToLocalization (S:=aQ[X]⁰)
    (fun _ h=>b4t seedVal (nonZeroDivisors.ne_zero h)) PhysicalField
abbrev GaussRing:=gauss.integer
def gaussCoeff :GaussRing →+* EC :=
 (algebraMap PhysicalField EC).comp (algebraMap GaussRing PhysicalField)
theorem base_val (g:aQ[X]) :gauss (coeffField g)=adG seedVal g :=
 Valuation.extendToLocalization_apply_map_apply _ _ _ _
theorem gauss_le (g:aQ[X]) (h : ∀ j,seedVal (g.coeff j)≤1) :
   gauss (coeffField g)≤1 :=
 (base_val g).trans_le (Finset.sup_le fun j _=>h j)
theorem base_unit {g:aQ[X]} (h:gauss (coeffField g)≤1)
  {j:ℕ} (hj:seedVal (g.coeff j)=1) :gauss (coeffField g)=1 :=
 le_antisymm h ((hj.symm.trans_le (aMX seedVal g j)).trans_eq (base_val g).symm)
private theorem integral_intersection {A B C F M:Type*} [za6 A]
  [za6 B] [IsDomain B] [IsIntegrallyClosed B]
  [za6 C] [IsDomain C] [IsIntegrallyClosed C] [zrb F] [zrb M]
  [zZE B F] [z0o B F] [zZE C F] [z0o C F]
  [zZE F M] [zZE B M] [zZE C M] [zsf B F M] [zsf C F M]
  (ι:A →+* B) (hι:zq4 ι)
  (hlift : ∀ b:B,∀ c:C,algebraMap B F b=algebraMap C F c→b∈ι.rangeS)
  {x :M} (hx :IsIntegral B x) (hy :IsIntegral C x) :
  ((algebraMap B M).comp ι).IsIntegralElem x := by
 have he : (minpoly B x).map (algebraMap B F)=(minpoly C x).map (algebraMap C F) :=
  (minpoly.isIntegrallyClosed_eq_field_fractions' F hx).symm.trans
    (minpoly.isIntegrallyClosed_eq_field_fractions' F hy)
 have hm:minpoly B x∈(mapRingHom ι).rangeS:= by
  rw [mem_map_rangeS]
  intro j
  apply hlift _ ((minpoly C x).coeff j)
  simpa only [coeff_map] using congrArg (fun f :F[X]=>f.coeff j) he
 obtain ⟨P,hP⟩:=hm
 change P.map ι=minpoly B x at hP
 have hmon : (P.map ι).Monic:=hP.symm ▸ minpoly.monic hx
 exact ⟨P,hι.monic_map_iff.2 hmon,by rw [← eval₂_map,hP]; exact minpoly.aeval B x⟩
private abbrev AH :PowerSeries L →+* aQ:=algebraMap _ _
private theorem lift_bounded (g:aQ[X]) (h:gauss (coeffField g)≤1) :
  g∈(mapRingHom AH).rangeS:= by
 rw [mem_map_rangeS]
 intro j
 have hj:=(aMX seedVal g j).trans ((base_val g).symm.trans_le h)
 exact (LaurentSeries.val_le_one_iff_eq_coe L _).1 hj
theorem descend {x :EC} (hx :physicalCoeff.IsIntegralElem x)
   (hv :gaussCoeff.IsIntegralElem x) :integralCoeff.IsIntegralElem x := by
 let:zZE GaussRing EC:=gaussCoeff.toAlgebra
 let:SMul GaussRing EC:=Algebra.toSMul
 let:zsf GaussRing PhysicalField EC:=IsScalarTower.of_algebraMap_eq' rfl
 let:z0o GaussRing PhysicalField:=(Valuation.integer.integers gauss).isFractionRing
 have hb:algebraMap aQ[X] EC=physicalCoeff :=
   IsScalarTower.algebraMap_eq aQ[X] PhysicalField EC
 have hx' : IsIntegral aQ[X] x := by
   change (algebraMap aQ[X] EC).IsIntegralElem x
   rwa [hb]
 change (physicalCoeff.comp (mapRingHom AH)).IsIntegralElem x
 rw [← hb]
 apply integral_intersection (F:=PhysicalField) (C:=GaussRing) (mapRingHom AH)
   (zTo AH
     (FaithfulSMul.algebraMap_injective (PowerSeries L) aQ))
   _ hx' (show IsIntegral GaussRing x from hv)
 intro b c he
 exact lift_bounded b (he.symm ▸ c.property)
end
end q0n1P7d
end
section
set_option backward.isDefEq.respectTransparency false
namespace qCtoYwb
noncomputable section
open Polynomial TrivSqZeroExt
open cu (L)
open qqV3gre
open qnyP9Da (coeff_by aNu)
open scoped nonZeroDivisors
private abbrev Dual (E :Type) :=TrivSqZeroExt E E
section
open HahnSeries
private def JE (a :aQ) :aQ :=
 ⟨fun i=>(i:L)*a.coeff i,a.isPWO_support.mono (fun i hi ha=>hi (by simp [ha]))⟩
private theorem euler_support (a :aQ) : (JE a).support⊆a.support :=
 fun i hi ha=>hi (by simp [JE,ha])
private theorem euler_mul (a b:aQ) :JE (a*b)=a*JE b+JE a*b:= by
 apply HahnSeries.ext
 funext i
 change (i:L)*(a*b).coeff i=(a*JE b+JE a*b).coeff i
 rw [HahnSeries.coeff_add,coeff_mul_right' b.isPWO_support (euler_support b),
  coeff_mul_left' a.isPWO_support (euler_support a),HahnSeries.coeff_mul,Finset.mul_sum,← Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro j hj
 rw [← (Finset.mem_antidiagonal.mp hj).2.2,Int.cast_add]
 change ((j.1 :L)+(j.2 :L))*(a.coeff j.1*b.coeff j.2) =
  a.coeff j.1*((j.2 :L)*b.coeff j.2)+((j.1 :L)*a.coeff j.1)*b.coeff j.2
 ring
private theorem seed_mul (a b:aQ) :
  LaurentSeries.derivative L (a*b) =
   a*LaurentSeries.derivative L b+LaurentSeries.derivative L a*b:= by
 have h (c:aQ) :LaurentSeries.derivative L c=single (-1) 1*JE c:= by
  apply HahnSeries.ext
  funext i
  rw [coeff_single_mul,LaurentSeries.derivative_apply,LaurentSeries.hasseDeriv_coeff,
   Ring.choose_one_right,one_mul]
  change (i+(1 :ℤ))•c.coeff (i+1)=((i - -1 :ℤ) :L)*c.coeff (i - -1)
  rw [sub_neg_eq_add,zsmul_eq_mul]
 simp only [h,euler_mul,mul_add]
 ring
end
private theorem seed_const (u:L) :
  LaurentSeries.derivative L (algebraMap L aQ u)=0:= by
 rw [LaurentSeries.algebraMap_apply,HahnSeries.C_apply,LaurentSeries.derivative_apply,
  LaurentSeries.hasseDeriv_single]
 simp
private def aih {E :Type} [zrb E] (j:aQ →+* E) (a :E) :
  aQ →+* Dual E where
 toFun x :=inl (j x)+inr (a*j (LaurentSeries.derivative L x))
 map_zero' := by ext <;> simp
 map_one' := by
  have h:LaurentSeries.derivative L (1 :aQ)=0:= by simpa using seed_const 1
  ext <;> simp [h]
 map_add' x y := by ext <;> simp [mul_add]
 map_mul' x y := by
  ext
  · simp
  · simp [-LaurentSeries.derivative_apply,seed_mul,smul_eq_mul,mul_add]
    ring
private theorem extendDual {A E :Type} [zrb A] [zrb E] [zZE A E]
    [zw7 A E] (b:A →+* Dual E)
    (hb : ∀ a,(b a).fst=algebraMap A E a) :
    ∃ D:Derivation ℤ E E,∀ a,D (algebraMap A E a)=(b a).snd:= by
  let:zZE A (Dual E) :=b.toAlgebra
  let π:Dual E →ₐ[A] E := { (fstHom ℤ E E).toRingHom with commutes' := hb }
  have hs :Function.Surjective π:= fun a=>⟨inl a,rfl⟩
  have hk :IsNilpotent (RingHom.ker π.toRingHom) := by
    refine ⟨2,?_⟩
    let I:=RingHom.ker π.toRingHom
    change I ^(2 :ℕ) = ⊥
    have hm:I* I ≤ ⊥ := by
      apply Ideal.mul_le.mpr
      intro a ha c hc
      change a.fst=0 at ha
      change c.fst=0 at hc
      rw [Ideal.mem_bot]
      ext <;> simp [ha,hc]
    exact (pow_two I).trans (le_antisymm hm bot_le)
  let:Algebra.FormallyEtale A E :=Algebra.FormallyEtale.of_isSeparable _ _
  let f :=Algebra.FormallySmooth.liftOfSurjective (AlgHom.id A E) π hs hk
  have hf (a :E) : (f a).fst=a :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id A E) π hs hk a
  let d:E →+ E :=
    { toFun:= fun a=>(f a).snd,map_zero' := by simp,map_add' := fun a c=> by simp }
  let D:Derivation ℤ E E :=
    { toFun:=d
      map_add' := d.map_add
      map_smul' := fun n a=>d.map_zsmul n a
      map_one_eq_zero' := by change (f 1).snd=0; simp
      leibniz' := fun a c=> by
        change (f (a*c)).snd=a•(f c).snd+c•(f a).snd
        simp [hf,mul_comm] }
  exact ⟨D,fun a=>congrArg snd (f.commutes a)⟩
theorem coeff_seedDiff (f :tu) (i:ℕ) :
  (seedDiff f).coeff i=LaurentSeries.derivative L (f.coeff i) :=
 coeff_by _ (map_zero (LaurentSeries.derivative L)) _ _
theorem seedDiff_scalar (u:L) :seedDiff (scalar u)=0:= by
 apply Polynomial.ext
 intro i
 rw [coeff_seedDiff,Polynomial.coeff_zero]
 by_cases h:i=0
 · subst i
   simpa only [scalar,coeff_C_zero] using seed_const u
 · simp [scalar,coeff_C,h]
private theorem extension (E :Type) [zrb E] [zZE PhysicalField E]
   [zw7 PhysicalField E] (a :aQ) (b:tu)
   (j:tu →+* E) (hj:j=(algebraMap PhysicalField E).comp (algebraMap tu PhysicalField)) :
   ∃ D:Derivation ℤ E E,∀ q:tu,
     D (j q)=j (z1z a*seedDiff q+b*q.derivative) := by
 have hji:zq4 j :=
   hj.symm ▸ (algebraMap PhysicalField E).injective.comp (zxb _ _)
 let m:aQ →+* E :=j.comp z1z
 let x :Dual E :=inl (j z7y)+inr (j b)
 let g:tu →+* Dual E :=eval₂RingHom (aih m (m a)) x
 have gC (c:aQ) :g (z1z c)=aih m (m a) c:=eval₂_C _ _
 have gX:g z7y=x :=eval₂_X _ _
 let aug:Dual E →+* E :=(fstHom ℤ E E).toRingHom
 have hg:aug.comp g=j:= by
   apply z86
   · intro c
     change (g (z1z c)).fst=j (z1z c)
     rw [gC]
     change (inl (m c)+inr (m a*m (LaurentSeries.derivative L c)) :Dual E).fst=m c
     simp only [fst_add,fst_inl,fst_inr,add_zero]
   · change (g z7y).fst=j z7y
     rw [gX]
     simp only [x,fst_add,fst_inl,fst_inr,add_zero]
 have hu (q:tu⁰) :IsUnit (g q) := by
   rw [isUnit_iff_isUnit_fst,show (g q).fst=j q from zLs hg q]
   exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff j hji).mpr
     (nonZeroDivisors.ne_zero q.property))
 let h:PhysicalField →+* Dual E :=IsLocalization.lift hu
 have hbase (q:tu) :h (algebraMap tu PhysicalField q)=g q :=
   IsLocalization.lift_eq hu q
 have hh:aug.comp h=algebraMap PhysicalField E := by
   apply IsLocalization.ringHom_ext tu⁰
   apply RingHom.ext
   intro q
   change aug (h (algebraMap tu PhysicalField q)) =
     algebraMap PhysicalField E (algebraMap tu PhysicalField q)
   rw [hbase]
   exact (zLs hg q).trans (zLs hj q)
 obtain ⟨D,hD⟩:=extendDual h (zLs hh)
 have hDg (q:tu) :D (j q)=(g q).snd:= by
   have hq:j q=algebraMap PhysicalField E (algebraMap tu PhysicalField q) :=
     zLs hj q
   rw [hq,hD,hbase]
 have hq:eval₂RingHom m (j z7y)=j:= by
   apply z86
   · intro c
     exact eval₂_C _ _
   · exact eval₂_X _ _
 have he (q:tu) :q.eval₂ m (j z7y)=j q:=zLs hq q
 refine ⟨D,fun q => ?_⟩
 have hX:D (j z7y)=j b:= by
   rw [hDg,gX]
   simp only [x,snd_add,snd_inl,snd_inr,zero_add]
 have h:=aNu D m (j z7y) q (z1z a*seedDiff q) (fun i=> by
   rw [show m (q.coeff i)=j (z1z (q.coeff i)) from rfl,hDg,gC]
   change (inl (m (q.coeff i)) +
     inr (m a*m (LaurentSeries.derivative L (q.coeff i))) :Dual E).snd= _
   simp only [snd_add,snd_inl,snd_inr,zero_add,coeff_C_mul,coeff_seedDiff,map_mul])
 simpa only [he,hX,map_add,map_mul,mul_comm (j q.derivative) (j b)] using h
theorem exists_derivation (y :EC) (hy :IsSeparable PhysicalField y)
   (a :aQ) (b:tu) :
   ∃ D:Derivation ℤ (Simple y) (Simple y),∀ q:tu,
     D (baseIn y q)=baseIn y (z1z a*seedDiff q+b*q.derivative) := by
 let:zw7 PhysicalField (Simple y) :=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hy
 exact extension (Simple y) a b (baseIn y) rfl
end
end qCtoYwb
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace qCtoYwb
noncomputable section
open Polynomial
open P5 (p)
open cu (L)
open qqV3gre
open qziIa4d (seedDerivative)
open qnyP9Da (coeff_by aNu)
open q14iMuc (discr_map discr_ne)
def c1 :Prop :=
  ∀ (π:tu) [Fact (Irreducible π)] (f :tu[X]) (u v :L) (y :EC),
    0<f.natDegree→f.natDegree<p→u≠v→f.eval₂ physicalCoeff y=0 →
    ¬ π∣f.discr*reference f u*reference f v →
    let j:=localIn π y
    let w:=ratio y u v
    ∃ Q: (Local π)[X],Q.Monic∧Q.eval₂ j w=0 ∧
      IntegralAt π y w⁻¹∧Q.derivative.eval₂ j w≠0 ∧
      IntegralAt π y (Q.derivative.eval₂ j w)⁻¹
def c2 :Prop :=
  ∀ (π:tu) [Fact (Irreducible π)] (y :EC),
    π.Separable→ IsSeparable PhysicalField y→Module.finrank PhysicalField (Simple y)<p →
    ∀ D:Derivation ℤ (Simple y) (Simple y),PreservesLocal π y D→TangentAt π y D →
      ∀ w:Simple y,w≠0→ IntegralAt π y (D w/w)
private abbrev inc (y :EC) :Simple y →+* EC:=(Simple y).val.toRingHom
private theorem inc_eval (y :EC) (f :tu[X]) :
  inc y (f.eval₂ (baseIn y) (point y))=f.eval₂ physicalCoeff y :=
 hom_eval₂ f (baseIn y) (inc y) (point y)
private theorem physicalCoeff_injective :zq4 physicalCoeff :=
 (algebraMap PhysicalField EC).injective.comp (zxb _ _)
private theorem local_base (π:tu) [Fact (Irreducible π)] (y :EC) (a :tu) :
   localIn π y (algebraMap tu (Local π) a)=baseIn y a := by
 change algebraMap PhysicalField (Simple y) (algebraMap (Local π) PhysicalField
     (algebraMap tu (Local π) a))=algebraMap PhysicalField (Simple y) (algebraMap tu PhysicalField a)
 rw [← IsScalarTower.algebraMap_apply tu (Local π) PhysicalField]
private theorem preserves_loc {R A E :Type} [za6 R] [za6 A] [zrb E] [zZE R A]
  (M:Submonoid R) [zNo M A] (j:R →+* E) (k :A →+* E)
  (hk : ∀ a,k (algebraMap R A a)=j a) (hM : ∀ b:M,j b≠0)
  (D:Derivation ℤ E E) (δ:R→R) (hD : ∀ a,D (j a)=j (δ a)) :
  ∀ a :A,∃ b:A,D (k a)=k b:= by
 have image (a :R) (b:M) :k (zzm A a b)=j a/j b:= by
  have he :=congrArg k (IsLocalization.mk'_spec A a b)
  rw [map_mul,hk,hk] at he
  exact (eq_div_iff (hM b)).2 he
 intro x
 obtain ⟨⟨a,b⟩,rfl⟩:=IsLocalization.mk'_surjective M x
 refine ⟨zzm A ((b:R)*δ a-a*δ b) (b^2),?_⟩
 simp only [image]
 rw [D.leibniz_div,hD,hD,show ((b^2 :M) :R)=(b:R)^2 from rfl]
 simp only [smul_eq_mul,map_sub,map_mul,map_pow,div_eq_mul_inv,inv_pow]
 exact mul_comm _ _
private theorem preserves {y :EC} (D:Derivation ℤ (Simple y) (Simple y))
  (δ:tu→tu) (hD : ∀ a,D (baseIn y a)=baseIn y (δ a))
  (π:tu) [Fact (Irreducible π)] :PreservesLocal π y D :=
 preserves_loc ((primeIdeal π).primeCompl) (baseIn y) (localIn π y) (local_base π y)
  (fun b=>(map_ne_zero_iff _ (baseIn_injective y)).2
    (fun h=>b.property (h.symm ▸ (primeIdeal π).zero_mem))) D δ hD
private theorem integral_of_clearing {E :Type} [zrb E] [zZE tu E] (w:E)
  (h : ∀ (π:tu),Irreducible π → ∃ b:tu,¬ π∣b∧IsIntegral tu (b•w)) :
  IsIntegral tu w:= by
 let I:Ideal tu:=(integralClosure tu E).toSubmodule.comap (zZj tu E w)
 have hclear (π:tu) [hπ:Fact (Irreducible π)] : ∃ b:tu,¬ π∣b∧b∈I :=
  h π hπ.out
 let:Fact (Irreducible (z7y:tu)) :=⟨irreducible_X⟩
 obtain ⟨a,ha,haI⟩:=hclear z7y
 have hI:I ≠ ⊥ := fun hI=>ha (by rw [hI,Ideal.mem_bot] at haI; rw [haI]; exact dvd_zero _)
 by_contra hn
 let m:=Submodule.IsPrincipal.generator I
 have hm0:m≠0:= fun hm=>hI ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr hm)
 have hmn : ¬ IsUnit m:= by
  intro hm
  have ht:=I.eq_top_of_isUnit_mem (Submodule.IsPrincipal.generator_mem I) hm
  have h1 : (1 :tu)∈I:=ht ▸ trivial
  have hw:IsIntegral tu (zZj tu E w 1) :=h1
  rw [LinearMap.toSpanSingleton_apply_one] at hw
  exact hn hw
 obtain ⟨π,hπ,hd⟩:=WfDvdMonoid.exists_irreducible_factor hmn hm0
 let:Fact (Irreducible π) :=⟨hπ⟩
 obtain ⟨b,hpb,hbI⟩:=hclear π
 exact hpb (hd.trans ((Submodule.IsPrincipal.mem_iff_generator_dvd I).mp hbI))
private theorem integral_of_local {y :EC} (w:Simple y)
  (h : ∀ (π:tu) [Fact (Irreducible π)],IntegralAt π y w) :
  (baseIn y).IsIntegralElem w:= by
 let:zZE tu (Simple y) :=(baseIn y).toAlgebra
 change IsIntegral tu w
 apply integral_of_clearing w
 intro π hπ
 let:Fact (Irreducible π) :=⟨hπ⟩
 let:zZE (Local π) (Simple y) :=(localIn π y).toAlgebra
 let:zsf tu (Local π) (Simple y) :=
  IsScalarTower.of_algebraMap_eq (fun b=>(local_base π y b).symm)
 have hw:IsIntegral (Local π) w:=h π
 obtain ⟨b,hb⟩:=IsIntegral.exists_multiple_integral_of_isLocalization
  (M:=(primeIdeal π).primeCompl) w hw
 exact ⟨b,fun hπ=>b.property (Ideal.mem_span_singleton.mpr hπ),hb⟩
private theorem etale_log {A E :Type} [za6 A] [zrb E] [zZE A E]
   (D:Derivation ℤ E E) (hD : ∀ a :A,∃ b:A,D (algebraMap A E a)=algebraMap A E b)
   (w:E) (Q:A[X]) (hm:Q.Monic)
   (hw:aeval w Q=0) (hi:IsIntegral A w⁻¹)
   (hd:aeval w Q.derivative≠0) (hj:IsIntegral A (aeval w Q.derivative)⁻¹) :
   IsIntegral A (D w/w) := by
 classical
 let j:=algebraMap A E
 let d (a :A) :=if a=0 then 0 else Classical.choose (hD a)
 have hzero :d 0=0:= by simp [d]
 have hact (a :A) :D (j a)=j (d a) := by
   by_cases ha :a=0
   · simp [ha,hzero]
   · rw [show d a=Classical.choose (hD a) from ite_eq_right ha]
     exact Classical.choose_spec (hD a)
 let P:= Q.sum fun i a=>monomial i (d a)
 have h:=aNu D j w Q P (fun i=> by
   rw [show P.coeff i=d (Q.coeff i) from coeff_by d hzero Q i]
   exact hact _)
 rw [show Q.eval₂ j w=0 from hw,map_zero] at h
 have hq:D w = -(P.eval₂ j w)*(Q.derivative.eval₂ j w)⁻¹:= by
   have hn:Q.derivative.eval₂ j w≠0:=hd
   apply (eq_mul_inv_iff_mul_eq₀ hn).2
   linear_combination -h
 let B:=integralClosure A E
 have hB:Algebra.adjoin A ({w} : Set E)≤B :=
   Algebra.adjoin_le (Set.singleton_subset_iff.mpr (show w∈B from ⟨Q,hm,hw⟩))
 have hp:IsIntegral A (P.eval₂ j w) :=hB (Polynomial.aeval_mem_adjoin_singleton A w (p:=P))
 rw [div_eq_mul_inv,hq]
 exact (hp.neg.mul hj).mul hi
private theorem root_data {f :tu[X]} (hp:0<f.natDegree) (hdeg:f.natDegree<p)
    (hdis :f.discr≠0) {y :EC} (hy :f.eval₂ physicalCoeff y=0) :
    IsSeparable PhysicalField y∧Module.finrank PhysicalField (Simple y)<p ∧
      f.derivative.eval₂ physicalCoeff y≠0:= by
  let j:=algebraMap tu PhysicalField
  let g:=f.map j
  have hg:g.natDegree=f.natDegree :=natDegree_map_eq_of_injective (zxb _ _) _
  have hpos :0<g.natDegree :=hg ▸ hp
  have hroot :aeval y g=0:= by simpa only [g,aeval_def,eval₂_map,physicalCoeff] using hy
  let r :=g.resultant g.derivative g.natDegree (g.natDegree - 1)
  have hr :r≠0:= by
    unfold r g
    rw [derivative_map,hg,resultant_map_map,resultant_deriv (natDegree_pos_iff_degree_pos.mp hp)]
    exact (map_ne_zero_iff j (zxb _ _)).2
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hp))) hdis)
  obtain ⟨a,b,_,_,hab⟩:=exists_mul_add_mul_eq_C_resultant g g.derivative le_rfl
    (natDegree_derivative_le g) (Or.inl hpos.ne')
  have hs :g.Separable := by
    refine ⟨C r⁻¹*a,C r⁻¹*b,?_⟩
    rw [mul_assoc,mul_assoc,← mul_add,mul_comm a g,mul_comm b g.derivative,
      hab,← C_mul,inv_mul_cancel₀ hr,C_1]
  have hm:=minpoly.dvd PhysicalField y hroot
  refine ⟨hs.of_dvd hm,?_,?_⟩
  · rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral y)]
    exact (natDegree_le_of_dvd hm hs.ne_zero).trans_lt (hg.symm ▸ hdeg)
  · simpa only [g,derivative_map,aeval_def,eval₂_map,physicalCoeff]
      using hs.aeval_derivative_ne_zero hroot
private theorem log_div {E :Type} [zrb E] (D:Derivation ℤ E E)
  {a b:E} (ha :a≠0) (hb:b≠0) (h:D a=D b) :
  D (a/b)/(a/b)=D a*(a⁻¹ - b⁻¹) := by
 rw [D.leibniz_div,← h]
 simp only [smul_eq_mul]
 field_simp [ha,hb]
private theorem log_eq {y :EC} {f :tu[X]} {u v :L} {a b:tu}
    (D:Derivation ℤ (Simple y) (Simple y))
    (hD : ∀ q,D (baseIn y q)=baseIn y (a*seedDiff q+b*q.derivative))
    (hy :f.eval₂ physicalCoeff y=0) (hder :f.derivative.eval₂ physicalCoeff y≠0)
    (hu:point y - baseIn y (scalar u)≠0) (hv :point y - baseIn y (scalar v)≠0) :
    inc y (D (ratio y u v)/ratio y u v) =
      physicalCoeff a*(-((seedDerivative f).eval₂ physicalCoeff y /
        f.derivative.eval₂ physicalCoeff y)) *
          ((y - constant u)⁻¹-(y - constant v)⁻¹) +
      physicalCoeff b*(-((physicalDerivative f).eval₂ physicalCoeff y /
        f.derivative.eval₂ physicalCoeff y))*((y - constant u)⁻¹-(y - constant v)⁻¹) := by
  let j:=baseIn y
  let Q:=z1z a*seedDerivative f+Polynomial.C b*physicalDerivative f
  have h:=aNu D j (point y) f Q (fun i=> by
    rw [hD,show Q.coeff i=a*seedDiff (f.coeff i)+b*(f.coeff i).derivative by
      simp only [Q,coeff_add,coeff_C_mul]
      congr 2
      · exact coeff_by seedDiff (by simp [seedDiff]) f i
      · exact coeff_by (fun q:tu=>q.derivative) derivative_zero f i])
  have hf :f.eval₂ j (point y)=0:=(inc y).injective (by rw [inc_eval,hy,map_zero])
  rw [hf,map_zero] at h
  have h' := congrArg (inc y) h
  simp only [map_zero,map_add,map_mul,inc_eval,j,Q,eval₂_add,eval₂_mul,eval₂_C] at h'
  have hd:inc y (D (point y)) =
      physicalCoeff a*(-((seedDerivative f).eval₂ physicalCoeff y /
        f.derivative.eval₂ physicalCoeff y)) +
      physicalCoeff b*(-((physicalDerivative f).eval₂ physicalCoeff y /
        f.derivative.eval₂ physicalCoeff y)) := by
    change 0=physicalCoeff a*(seedDerivative f).eval₂ physicalCoeff y +
      physicalCoeff b*(physicalDerivative f).eval₂ physicalCoeff y +
      f.derivative.eval₂ physicalCoeff y*inc y (D (point y)) at h'
    field_simp
    linear_combination -h'
  have hz (r :L) :D (j (scalar r))=0:= by
    rw [hD,seedDiff_scalar,show (scalar r).derivative=0 from derivative_C]
    simp only [mul_zero,add_zero,map_zero]
  have hs (r :L) :D (point y - j (scalar r))=D (point y) := by
    rw [map_sub,hz,sub_zero]
  have hl:D (ratio y u v)/ratio y u v =
      D (point y)*((point y - j (scalar u))⁻¹-(point y - j (scalar v))⁻¹) := by
    have huj:point y - j (scalar u)≠0:=hu
    have hvj:point y - j (scalar v)≠0:=hv
    exact (log_div D huj hvj ((hs u).trans (hs v).symm)).trans (by rw [hs u])
  rw [hl,map_mul,hd]
  have hc (r :L) :inc y (j (scalar r))=constant r :=rfl
  simp only [map_sub,map_inv₀,hc,show inc y (point y)=y from rfl]
  ring
private theorem ref_ne {f :tu[X]} {u:L} {y :EC} (hy :f.eval₂ physicalCoeff y=0)
  (hr :reference f u≠0) :point y - baseIn y (scalar u)≠0:= by
 intro h
 have hz :y=constant u:=congrArg (inc y) (sub_eq_zero.mp h)
 apply hr (physicalCoeff_injective ?_)
 rw [map_zero,reference,← eval₂_id,hom_eval₂,RingHom.comp_id]
 change f.eval₂ physicalCoeff (constant u)=0
 rwa [← hz]
private theorem integrals (bY:c1) (tame :c2) {f :tu[X]} {t:tu} {u v :L}
    (hp:0<f.natDegree) (hn:f.natDegree<p) (hdisc:f.discr≠0)
    (hu:reference f u≠0) (hv :reference f v≠0) (huv :u≠v)
    (hs :t.Separable) (hsupp : ∃ n:ℕ,f.discr*reference f u*reference f v∣t^n) :
    integralLogs physicalCoeff f t u v := by
  intro y hy
  obtain ⟨hsep,hdeg,hder⟩:=root_data hp hn hdisc hy
  obtain ⟨Ds,hs'⟩:=exists_derivation y hsep 1 0
  obtain ⟨Dx,hx'⟩:=exists_derivation y hsep 0 1
  let j:=baseIn y
  have hsD (q:tu) :Ds (j q)=j (seedDiff q) := by simpa using hs' q
  have hxD (q:tu) :Dx (j q)=j q.derivative := by simpa using hx' q
  have hmul (q r :tu) :seedDiff (q*r)=q*seedDiff r+seedDiff q*r := by
    apply baseIn_injective y
    rw [← hsD,map_mul,Ds.leibniz,hsD,hsD,map_add,map_mul,map_mul]
    change j q*j (seedDiff r)+j r*j (seedDiff q) =
      j q*j (seedDiff r)+j (seedDiff q)*j r
    rw [mul_comm (j r)]
  have hu' := ref_ne hy hu
  have hv' := ref_ne hy hv
  have hlog (a b:tu)
      (htan : ∀ π:tu,π∣t→π∣a*seedDiff π+b*π.derivative) :
      physicalCoeff.IsIntegralElem
        (physicalCoeff a*(-((seedDerivative f).eval₂ physicalCoeff y /
          f.derivative.eval₂ physicalCoeff y))*((y - constant u)⁻¹-(y - constant v)⁻¹) +
        physicalCoeff b*(-((physicalDerivative f).eval₂ physicalCoeff y /
          f.derivative.eval₂ physicalCoeff y))*((y - constant u)⁻¹-(y - constant v)⁻¹)) := by
    let D:=j a•Ds+j b•Dx
    have hD (q:tu) :D (j q)=j (a*seedDiff q+b*q.derivative) := by
      simp only [D,Derivation.add_apply,Derivation.smul_apply,smul_eq_mul,hsD,hxD,map_add,map_mul]
    let w:=ratio y u v
    have h:=integral_of_local (D w/w) (fun π inst=> by
      let:=inst
      have hreg:=preserves D _ hD π
      by_cases ht:π∣t
      · obtain ⟨c,hc⟩:=htan π ht
        have htang:TangentAt π y D:=⟨algebraMap tu (Local π) c,by rw [local_base,hD,hc,map_mul]⟩
        exact tame π y (hs.of_dvd ht) hsep hdeg D hreg htang w (div_ne_zero hu' hv')
      · obtain ⟨n,hpow⟩:=hsupp
        have hunit : ¬ π∣f.discr*reference f u*reference f v :=
          fun hd=>ht (inst.out.prime.dvd_of_dvd_pow (hd.trans hpow))
        obtain ⟨Q,hm,hQ,hwi,hne,hdi⟩:=bY π f u v y hp hn huv hy hunit
        let:zZE (Local π) (Simple y) :=(localIn π y).toAlgebra
        exact etale_log (A:=Local π) D hreg w Q hm hQ hwi hne hdi)
    have hall:physicalCoeff.IsIntegralElem (inc y (D w/w)) :=h.map (inc y)
    simpa only [w,log_eq D hD hy hder hu' hv'] using hall
  have h0:=hlog t 0 (fun π hπ=> by simpa using dvd_mul_of_dvd_left hπ (seedDiff π))
  have h1 :=hlog t.derivative (-seedDiff t) (fun π hπ=> by
    obtain ⟨r,rfl⟩:=hπ
    refine ⟨r.derivative*seedDiff π - seedDiff r*π.derivative,?_⟩
    rw [derivative_mul,hmul]
    ring)
  refine ⟨?_,?_⟩
  · simpa only [zPI,logCuts,map_zero,zero_mul,add_zero,mul_assoc] using h0
  · simpa only [zPI,logCuts,map_neg,neg_mul,sub_eq_add_neg,mul_assoc] using h1
theorem of_children (bY:c1) (tame :c2) :qqV3gre.c1 := by
 intro q Cq z S F V D W A t hn ht γ hγ hg
 let a :=F.atPlace γ (V.Bp hγ)
 let f :=arcEquation a F.f
 let ι:=mapRingHom a.toRingHom
 have hi:zq4 ι:=zTo _ a.injective
 have hd:f.natDegree=F.d:=natDegree_map_eq_of_injective hi F.f
 have hdisc:f.discr=ι F.f.discr :=discr_map ι hi F.f F.positive
 have hf (u:L) :reference f u=ι (qxPDCsa.finiteRef F u) := by
   have hval :ι (z1z (algebraMap L Cq.E u))=scalar u:= by
     change (z1z (algebraMap L Cq.E u)).map a.toRingHom=scalar u
     rw [Polynomial.map_C]
     exact congrArg z1z (a.commutes u)
   unfold reference qxPDCsa.finiteRef
   rw [show f=F.f.map ι from rfl,← eval₂_id,eval₂_map,RingHom.id_comp,
     ← eval₂_id,hom_eval₂,RingHom.comp_id,hval]
 apply integrals bY tame (hd ▸ F.positive) (hd ▸ hn)
   (hdisc.symm ▸ (map_ne_zero_iff ι hi).2 (discr_ne F.f F.irreducible F.positive hn))
   ((hf _).symm ▸ (map_ne_zero_iff ι hi).2 (A.finite_ne 0))
   ((hf _).symm ▸ (map_ne_zero_iff ι hi).2 (A.finite_ne 1))
   (fun h=>(by decide : (0:Fin 2)≠1) (A.finite_distinct h)) (ht.separable.map (f :=a.toRingHom))
 obtain ⟨n,hp⟩:=ht.power
 refine ⟨n,?_⟩
 change _∣ι t^n
 rw [hdisc,hf,hf,← map_mul,← map_mul,← map_pow]
 exact map_dvd ι hp
end
end qCtoYwb
end
