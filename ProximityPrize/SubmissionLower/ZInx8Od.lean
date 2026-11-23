import ProximityPrize.SubmissionLower.Z3aw2hc
set_option Elab.async false
section
set_option backward.isDefEq.respectTransparency false
namespace qymFiQe
noncomputable section
open Polynomial qps5rle
open P5 (K p)
open cu (L)
open scoped WithZero
private abbrev Dual (E :Type) :=TrivSqZeroExt E E
open TrivSqZeroExt in
private def liftMap {A E :Type} [Field A] [Field E] [Algebra ℤ A] [Algebra A E]
  (D:Derivation ℤ A A) :A →+* Dual E where
 toFun a :=inl (algebraMap A E a)+inr (algebraMap A E (D a))
 map_one' := by ext <;> simp
 map_zero' := by ext <;> simp
 map_add' a b:= by ext <;> simp [Algebra.smul_def]
 map_mul' a b:= by ext <;> simp [D.leibniz,smul_eq_mul,Algebra.smul_def,mul_comm,add_comm]
open TrivSqZeroExt in
private theorem extendDerivation {A E :Type} [Field A] [Field E] [Algebra ℤ A] [Algebra A E]
    [Algebra.IsSeparable A E] (D:Derivation ℤ A A) :
    ∃ D' : Derivation ℤ E E,∀ a,D' (algebraMap A E a)=algebraMap A E (D a) := by
  let:Algebra A (Dual E) :=(liftMap (E :=E) D).toAlgebra
  let π:Dual E →ₐ[A] E :=
    { (fstHom ℤ E E).toRingHom with commutes' := fun a=> by change (_+_:Dual E).fst= _; simp }
  have hs :Function.Surjective π:= fun a=>⟨inl a,rfl⟩
  have hk :IsNilpotent (RingHom.ker π.toRingHom) := by
    refine ⟨2,?_⟩
    let I:=RingHom.ker π.toRingHom
    change I ^(2 :ℕ) = ⊥
    have hm:I* I ≤ ⊥ := by
      apply Ideal.mul_le.mpr
      intro a ha b hb
      change a.fst=0 at ha
      change b.fst=0 at hb
      rw [Ideal.mem_bot]
      ext <;> simp [ha,hb]
    exact (pow_two I).trans (le_antisymm hm bot_le)
  let:Algebra.FormallyEtale A E :=Algebra.FormallyEtale.of_isSeparable _ _
  let f :=Algebra.FormallySmooth.liftOfSurjective (AlgHom.id A E) π hs hk
  have hf (a :E) : (f a).fst=a :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id A E) π hs hk a
  let d:E →+ E :=
    { toFun:= fun a=>(f a).snd
      map_zero' := by simp
      map_add' := fun a b=> by simp }
  let D' : Derivation ℤ E E :=
    { toFun:=d
      map_add' := d.map_add
      map_smul' := fun n a=>d.map_zsmul n a
      map_one_eq_zero' := by change (f 1).snd=0; simp
      leibniz' := fun a b=> by
        change (f (a*b)).snd=a•(f b).snd+b•(f a).snd
        simp [hf,mul_comm] }
  refine ⟨D',fun a => ?_⟩
  have h:=congrArg snd (f.commutes a)
  change (f (algebraMap A E a)).snd=(liftMap (E :=E) D a).snd at h
  simpa [liftMap,D',d,Algebra.smul_def] using h
theorem extendSimple (D:Derivation ℤ F F) (w:Roots) (hw:IsSeparable F w) :
   ∃ D' : Derivation ℤ (Simple w) (Simple w),
     ∀ a,D' (algebraMap F (Simple w) a)=algebraMap F (Simple w) (D a) := by
 let:Algebra.IsSeparable F (Simple w) :=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hw
 exact extendDerivation D
theorem killConstants (D:Derivation ℤ F F) (w:Roots)
   (D' : Derivation ℤ (Simple w) (Simple w))
   (hD' : ∀ a,D' (algebraMap F (Simple w) a)=algebraMap F (Simple w) (D a))
   (a :smallConstants D w) :D' a=0:= by
 let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let _:CharP SeedSeries p:=charP_of_injective_ringHom (algebraMap L SeedSeries).injective p
 let _:CharP F p:=charP_of_injective_ringHom (algebraMap SeedSeries F).injective p
 let _:CharP (Simple w) p:=charP_of_injective_ringHom (algebraMap F (Simple w)).injective p
 have hc:smallConstants D w≤ constants D' := by
   apply sup_le
   · rintro _ ⟨b,hb,rfl⟩
     change D b=0 at hb
     change D' (algebraMap F (Simple w) b)=0
     simp [hD',hb]
   · rw [Subfield.closure_le]
     rintro _ ⟨b,rfl⟩
     change D' (b^p)=0
     rw [D'.leibniz_pow,← Nat.cast_smul_eq_nsmul (Simple w),CharP.cast_eq_zero,zero_smul]
 exact hc a.property
theorem integral_mem {A E :Type} [CommRing A] [Field E] [Algebra A E]
  (V:ValuationSubring E) (hV : ∀ b:A,algebraMap A E b∈V)
  {a :E} (ha :IsIntegral A a) :a∈V:= by
 let:IsIntegrallyClosedIn V.toSubring E :=inferInstanceAs (IsIntegrallyClosedIn V E)
 exact (Subring.integralClosure_le_iff.mpr hV: (integralClosure A E).toSubring≤V.toSubring) ha
theorem integralOfValuations (w:Roots) (a :Simple w)
   (ha : ∀ V:ValuationSubring (Simple w),
     (∀ b:IntegerRing,algebraMap IntegerRing (Simple w) b∈V)→a∈V) :
   IsIntegral IntegerRing a := by
 let B:=integralClosure IntegerRing (Simple w)
 by_contra h
 have hb:a∉B.toSubring :=h
 obtain ⟨V,hV,hn⟩:=B.toSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn hb
 exact hn (ha V (fun b=>hV (B.algebraMap_mem b)))
theorem aNu {R E :Type} [CommRing R] [Field E] [Algebra ℤ E] (D:Derivation ℤ E E)
   (f :R →+* E) (a :E) (P Q:R[X])
   (hc : ∀ i,D (f (P.coeff i))=f (Q.coeff i)) :
   D (P.eval₂ f a)= Q.eval₂ f a+P.derivative.eval₂ f a*D a := by
 let n:=max P.natDegree Q.natDegree+1
 have hP:P.natDegree<n:=Nat.lt_succ_of_le (le_max_left _ _)
 have hQ:Q.natDegree<n:=Nat.lt_succ_of_le (le_max_right _ _)
 have hd:P.derivative.eval₂ f a =
     ∑ i∈Finset.range n,f (P.coeff i)*(i:E)*a^(i-1) := by
   simp_rw [derivative_apply,eval₂_sum,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X,map_mul,map_natCast]
   exact P.sum_over_range' (fun i=> by simp) n hP
 rw [eval₂_eq_sum_range' f hP,eval₂_eq_sum_range' f hQ,hd,map_sum,
   Finset.sum_mul,← Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro i _
 rw [D.leibniz,D.leibniz_pow,hc]
 simp only [smul_eq_mul,nsmul_eq_mul]
 ring
end
end qymFiQe
end
section
set_option backward.isDefEq.respectTransparency false
namespace qymFiQe
noncomputable section
open qps5rle
open cu (L)
open HahnSeries
private def JE (a :SeedSeries) :SeedSeries :=
 ⟨fun i=>(i:L)*a.coeff i,a.isPWO_support.mono (fun i hi ha=>hi (by simp [ha]))⟩
private theorem euler_support (a :SeedSeries) : (JE a).support⊆a.support :=
 fun i hi ha=>hi (by simp [JE,ha])
private theorem euler_mul (a b:SeedSeries) :JE (a*b)=a*JE b+JE a*b:= by
 apply HahnSeries.ext
 funext i
 change (i:L)*(a*b).coeff i=(a*JE b+JE a*b).coeff i
 rw [HahnSeries.coeff_add,coeff_mul_right' b.isPWO_support (euler_support b),
  coeff_mul_left' a.isPWO_support (euler_support a),coeff_mul,Finset.mul_sum,← Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro j hj
 have h:=(Finset.mem_antidiagonal.mp hj).2.2
 rw [← h,Int.cast_add]
 change ((j.1 :L)+(j.2 :L))*(a.coeff j.1*b.coeff j.2) =
  a.coeff j.1*((j.2 :L)*b.coeff j.2)+((j.1 :L)*a.coeff j.1)*b.coeff j.2
 ring
private theorem seed_derivative_mul (a b:SeedSeries) :
  LaurentSeries.derivative L (a*b)=a*LaurentSeries.derivative L b +
   LaurentSeries.derivative L a*b:= by
 have h (c:SeedSeries) :LaurentSeries.derivative L c=single (-1) 1*JE c:= by
  apply HahnSeries.ext
  funext i
  rw [coeff_single_mul,LaurentSeries.derivative_apply,LaurentSeries.hasseDeriv_coeff,
   Ring.choose_one_right,one_mul]
  change (i+(1 :ℤ))•c.coeff (i+1)=((i - -1 :ℤ) :L)*c.coeff (i - -1)
  rw [sub_neg_eq_add,zsmul_eq_mul]
 simp only [h,euler_mul,mul_add]
 ring
private abbrev seedAdd:SeedSeries →+ SeedSeries :=(LaurentSeries.derivative L).toAddMonoidHom
private def physicalAdd:F →+ F where
 toFun a :=a.map seedAdd
 map_zero' := by
  apply HahnSeries.ext
  funext i
  exact map_zero seedAdd
 map_add' a b:=HahnSeries.map_add seedAdd
theorem base_derivation : ∃ D:Derivation ℤ F F,coefficientwise D:= by
  let D:Derivation ℤ F F :=
    { toFun:=physicalAdd
      map_add' := physicalAdd.map_add
      map_smul' := fun n a=> by
        change physicalAdd ((Algebra.toModule :Module ℤ F).smul n a)=n•physicalAdd a
        exact (congrArg physicalAdd (int_smul_eq_zsmul (Algebra.toModule :Module ℤ F) n a)).trans
          (physicalAdd.map_zsmul n a)
      map_one_eq_zero' := by
        apply HahnSeries.ext
        funext i
        change seedAdd ((1 :F).coeff i)=(0:F).coeff i
        rw [HahnSeries.coeff_one,HahnSeries.coeff_zero]
        split
        · change LaurentSeries.derivative L (single 0 1)=0
          rw [LaurentSeries.derivative_apply,LaurentSeries.hasseDeriv_single]
          simp
        · exact map_zero seedAdd
      leibniz' := fun a b=> by
        apply HahnSeries.ext
        funext i
        change seedAdd ((a*b).coeff i)=(a*b.map seedAdd+b*a.map seedAdd).coeff i
        have hsup (c:F) : (c.map seedAdd).support⊆c.support :=
          Function.support_comp_subset (map_zero seedAdd) _
        rw [mul_comm b,HahnSeries.coeff_add,coeff_mul_right' b.isPWO_support (hsup b),
          coeff_mul_left' a.isPWO_support (hsup a),coeff_mul,map_sum,← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _=>seed_derivative_mul (a.coeff j.1) (b.coeff j.2)) }
  exact ⟨D,fun _ _=>rfl⟩
end
end qymFiQe
end
section
namespace qG7TGJa
noncomputable section
open cu (L)
open qZu9hjc (atPair gauge)
open q8Z6NHc (jo Generic genericF genericG)
abbrev aFB (d s a :ℕ) :=FractionRing (jo d s a)
abbrev Zk (d s a :ℕ) :=
 {q:Generic d s a×Generic d s a //
   atPair (RingHom.id _) q.1 q.2 (genericF d s a)=0 ∧
   atPair (RingHom.id _) q.1 q.2 (genericG d s a)=0}
def value {d s a :ℕ} (b c:L) (q:Generic d s a×Generic d s a) :Generic d s a :=
 atPair (RingHom.id _) q.1 q.2 (genericF d s a).derivative/gauge b c q.2^(d-2)
end
end qG7TGJa
end
