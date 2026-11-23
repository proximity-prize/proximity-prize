import ProximityPrize.SubmissionLower.ZXswmNd
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.IsSeparable → zw7, CommRing → za6, Field → zrb, Ideal.Quotient.field → zxv, Ideal.Quotient.mk → zVv, Ideal.span → zye, IsDomain → ztn, IsFractionRing → z0o, IsFractionRing.injective → zxb, IsLocalization.AtPrime.equivQuotMaximalIdeal → zx7, IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk → zaW, Module.finrank → zsE, Polynomial.X → z7y, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs, Set.image_singleton → zyk
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace qcuqT2c
noncomputable section
open Polynomial TrivSqZeroExt
open cu (L)
open qbjv5ec (aQ lN EC)
open scoped nonZeroDivisors
private abbrev Dual (E :Type) :=TrivSqZeroExt E E
private def aug (E :Type) [zrb E] :Dual E →+* E :=(fstHom ℤ E E).toRingHom
private theorem units {R F E :Type} [za6 R] [ztn R] [zrb F] [zrb E]
  [zZE R F] [z0o R F] (f :R →+* Dual E) (j:F →+* E)
  (h: (aug E).comp f=j.comp (algebraMap R F)) (a :R⁰) :IsUnit (f a) := by
 rw [isUnit_iff_isUnit_fst,show (f a).fst=j (algebraMap R F a) from zLs h a]
 exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff j j.injective).mpr
  ((map_ne_zero_iff _ (zxb R F)).mpr (nonZeroDivisors.ne_zero a.prop)))
private def dualLift {R F E :Type} [za6 R] [ztn R] [zrb F] [zrb E]
  [zZE R F] [z0o R F] (f :R →+* Dual E) (j:F →+* E)
  (h: (aug E).comp f=j.comp (algebraMap R F)) :F →+* Dual E :=
 IsLocalization.lift (units f j h)
private theorem lift_on {R F E :Type} [za6 R] [ztn R] [zrb F] [zrb E]
  [zZE R F] [z0o R F] (f :R →+* Dual E) (j:F →+* E)
  (h: (aug E).comp f=j.comp (algebraMap R F)) (a :R) :
  dualLift f j h (algebraMap R F a)=f a :=
 IsLocalization.lift_eq (units f j h) a
private theorem aug_lift {R F E :Type} [za6 R] [ztn R] [zrb F] [zrb E]
  [zZE R F] [z0o R F] (f :R →+* Dual E) (j:F →+* E)
  (h: (aug E).comp f=j.comp (algebraMap R F)) :
  (aug E).comp (dualLift f j h)=j:= by
 apply IsLocalization.ringHom_ext R⁰
 ext a
 rw [zQb,zQb,lift_on]
 exact zLs h a
private theorem aug_eval {R E :Type} [za6 R] [zrb E]
   (f :R →+* Dual E) (a b:E) :
   (aug E).comp (eval₂RingHom f (inl a+inr b)) =
     eval₂RingHom ((aug E).comp f) a := by
 apply ringHom_ext
 · intro r
   simp
 · simp [aug,fst_add]
private def Xm (E :Type) [zrb E] [zZE lN E] :
   {g:lN →+* Dual E //
     (aug E).comp g=algebraMap lN E ∧
     (∀ a :L,g (constant a)=inl (algebraMap lN E (constant a))) ∧
     g seed=inl (algebraMap lN E seed)+inr 1 ∧
     g amm=inl (algebraMap lN E amm)} := by
 let j:=algebraMap lN E
 let k :aQ →+* E :=j.comp ((algebraMap aQ[X] lN).comp C)
 let q:L →+* E :=k.comp ((algebraMap L[X] aQ).comp C)
 let f :L[X] →+* Dual E :=
   eval₂RingHom ((inlHom E E).comp q) (inl (j seed)+inr 1)
 have hf : (aug E).comp f=k.comp (algebraMap L[X] aQ) := by
   rw [show f= _ from rfl,aug_eval]
   apply ringHom_ext
   · intro a
     simp [aug,q]
   · simp [k,j,seed]
 let f' : aQ →+* Dual E :=dualLift f k hf
 let g:aQ[X] →+* Dual E :=eval₂RingHom f' (inl (j amm)+inr 0)
 have hg: (aug E).comp g=j.comp (algebraMap aQ[X] lN) := by
   rw [show g= _ from rfl,aug_eval,show (aug E).comp f' = k from aug_lift f k hf]
   apply ringHom_ext
   · intro b
     simp [k]
   · simp only [coe_eval₂RingHom,eval₂_X,zQb,amm]
 refine ⟨dualLift g j hg,aug_lift g j hg,?_,?_,?_⟩
 · intro a
   rw [constant,lift_on]
   change (C (algebraMap L[X] aQ (C a))).eval₂ f' _ = _
   rw [eval₂_C,lift_on f k hf]
   change (C a).eval₂ ((inlHom E E).comp q) _ = _
   rw [eval₂_C]
   rfl
 · rw [seed,lift_on]
   change (C (algebraMap L[X] aQ (z7y (R:=L)))).eval₂ f' _ = _
   rw [eval₂_C,lift_on f k hf]
   exact eval₂_X _ _
 · rw [amm,lift_on]
   change (z7y (R:=aQ)).eval₂ f' _ = _
   simp only [eval₂_X,inr_zero,add_zero,amm,j]
private theorem extension (E :Type) [zrb E] [zZE lN E]
    [zw7 lN E] :
    ∃ D:Derivation ℤ E E,
      (∀ a :L,D (algebraMap lN E (constant a))=0) ∧
      D (algebraMap lN E seed)=1∧D (algebraMap lN E amm)=0:= by
  let b:=Xm E
  let:zZE lN (Dual E) :=b.val.toAlgebra
  let π:Dual E →ₐ[lN] E :=
    { aug E with commutes' := fun a=>zLs b.property.1 a }
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
  let:Algebra.FormallyEtale lN E :=Algebra.FormallyEtale.of_isSeparable _ _
  let f :=Algebra.FormallySmooth.liftOfSurjective (AlgHom.id lN E) π hs hk
  have hf (a :E) : (f a).fst=a :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id lN E) π hs hk a
  let d:E →+ E :=
    { toFun:= fun a=>(f a).snd
      map_zero' := by simp
      map_add' := fun a b=> by simp }
  let D:Derivation ℤ E E :=
    { toFun:=d
      map_add' := d.map_add
      map_smul' := fun n a=>d.map_zsmul n a
      map_one_eq_zero' := by change (f 1).snd=0; simp
      leibniz' := fun a b=> by
        change (f (a*b)).snd=a•(f b).snd+b•(f a).snd
        simp [hf,mul_comm] }
  have hb (a :lN) :D (algebraMap lN E a)=(b.val a).snd :=
    congrArg snd (f.commutes a)
  refine ⟨D,fun a => ?_,?_,?_⟩
  · rw [hb,b.property.2.1]
    rfl
  · rw [hb,b.property.2.2.1]
    simp
  · rw [hb,b.property.2.2.2]
    rfl
theorem exists_derivation (y :EC) (hy :IsSeparable lN y) :
   ∃ D:Derivation ℤ (Simple y) (Simple y),
     (∀ a :L,D (cIn y a)=0)∧D (zIn y)=1∧D (xIn y)=0:= by
 let:zw7 lN (Simple y) :=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hy
 exact extension (Simple y)
end
end qcuqT2c
end
section
set_option backward.isDefEq.respectTransparency false
namespace qGA3mAd
noncomputable section
open Polynomial IsDedekindDomain IsLocalRing
open cu (L)
open qbjv5ec
open scoped WithZero
abbrev nodeParameter (x :L) :NodeRing x :=algebraMap aQ[X] (NodeRing x) (uniformizer x)
abbrev seedScalar :aQ:=algebraMap L[X] aQ (z7y (R:=L))
abbrev nodeSeed (x :L) :NodeRing x :=
 algebraMap aQ[X] (NodeRing x) (C seedScalar)
theorem nodeDvr (x :L) :IsDiscreteValuationRing (NodeRing x) :=
 IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain aQ[X]
  (physicalPrime x).ne_bot (NodeRing x)
theorem nodeMaximal (x :L) :maximalIdeal (NodeRing x)=zye {nodeParameter x} := by
 rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (physicalPrime x).asIdeal (NodeRing x)]
 change Ideal.map _ (zye {uniformizer x})= _
 rw [Ideal.map_span,zyk]
theorem nodeParameter_ne_zero (x :L) :nodeParameter x≠0:= by
 intro h
 have he :=congrArg (algebraMap (NodeRing x) lN) h
 rw [map_zero,← IsScalarTower.algebraMap_apply] at he
 exact (map_ne_zero_iff _ (zxb aQ[X] lN)).2
  (prime_X_sub_C _).ne_zero he
theorem nodeSeed_isUnit (x :L) :IsUnit (nodeSeed x) :=
 IsUnit.map ((algebraMap aQ[X] (NodeRing x)).comp C)
  (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (zxb L[X] aQ)).mpr X_ne_zero))
private theorem seed_not_power {n:ℕ} (hn:1<n) (b:aQ) :b^n≠seedScalar := by
 let q:HeightOneSpectrum L[X] :=
   ⟨zye {z7y},(Ideal.span_singleton_prime X_ne_zero).mpr prime_X,
     Ideal.span_singleton_eq_bot.not.mpr X_ne_zero⟩
 have hq:q.valuation aQ seedScalar=WithZero.exp (-1 :ℤ) := by
   rw [q.valuation_of_algebraMap]
   exact q.intValuation_singleton X_ne_zero rfl
 intro h
 have he :=congrArg (fun a=>WithZero.log (q.valuation aQ a)) h
 simp only [map_pow,hq,WithZero.log_pow,WithZero.log_exp,nsmul_eq_mul] at he
 have hd: (n:ℤ)∣(-1 :ℤ) :=⟨WithZero.log (q.valuation aQ b),he.symm⟩
 have hd' : n∣1 := by simpa using Int.natAbs_dvd_natAbs.mpr hd
 exact (not_le_of_gt hn) (Nat.le_of_dvd Nat.one_pos hd')
private abbrev nodeCoordinate (x :L) :aQ:=algebraMap L[X] aQ (C x)
private def nodeResidue (x :L) :ResidueField (NodeRing x) ≃+* aQ :=
 (zx7 (physicalPrime x).asIdeal (NodeRing x)).symm.trans
   (quotientSpanXSubCAlgEquiv (nodeCoordinate x)).toRingEquiv
theorem nodeSeed_not_power (x :L) {n:ℕ} (hn:1<n)
    (b:ResidueField (NodeRing x)) :b^n≠residue _ (nodeSeed x) := by
  have h:nodeResidue x (residue _ (nodeSeed x))=seedScalar := by
    unfold nodeResidue
    change (quotientSpanXSubCAlgEquiv (nodeCoordinate x))
      ((zx7 (physicalPrime x).asIdeal (NodeRing x)).symm
        (zVv _ (algebraMap aQ[X] (NodeRing x) (C seedScalar))))= _
    rw [← zaW (physicalPrime x).asIdeal (NodeRing x),
      RingEquiv.symm_apply_apply]
    exact (quotientSpanXSubCAlgEquiv_mk (nodeCoordinate x) (C seedScalar)).trans (eval_C ..)
  intro he
  exact seed_not_power hn (nodeResidue x b) (by simpa only [map_pow,h] using congrArg (nodeResidue x) he)
end
end qGA3mAd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qGA3mAd
noncomputable section
open Polynomial IsDedekindDomain IsLocalRing
open P5 (p)
open qcuqT2c (TamePlace)
open scoped WithZero
section Adic
variable {B E :Type} [za6 B] [IsDedekindDomain B] [zrb E]
 [zZE B E] [z0o B E] (q:HeightOneSpectrum B)
private def adicResidue : (B ⧸ q.asIdeal) ≃+* ResidueField (q.valuation E).valuationSubring := by
 letI:q.asIdeal.IsMaximal:=q.isMaximal
 let e :q.valuationSubringAtPrime E ≃+* (q.valuation E).valuationSubring :=
   RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
     (q.valuationSubringAtPrime_eq_valuationSubring (K:=E)))
 exact (zx7 q.asIdeal (q.valuationSubringAtPrime E)).trans
   (ResidueField.mapEquiv e)
private theorem adicResidue_mk (z :B) (hz :q.valuation E (algebraMap B E z)≤1) :
   adicResidue q (zVv q.asIdeal z) =
     residue (q.valuation E).valuationSubring ⟨algebraMap B E z,hz⟩:= by
 unfold adicResidue
 rw [RingEquiv.trans_apply,zaW]
 change ResidueField.map _ (residue _ (algebraMap B (q.valuationSubringAtPrime E) z))= _
 rw [ResidueField.map_residue]
 rfl
end Adic
private theorem no_new_root {F G:Type} [zrb F] [zrb G] [zZE F G] [Module.Finite F G]
   {n:ℕ} {z :F} (hn:n.Prime) (h:zsE F G<n) (hz : ∀ c:F,c^n≠z)
   (d:G) :d^n≠algebraMap F G z := by
 intro hd
 have hm:z7y ^n-Polynomial.C z=minpoly F d :=
   minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hn hz)
     (by simpa only [map_sub,aeval_X_pow,aeval_C,sub_eq_zero] using hd)
     (monic_X_pow_sub_C z hn.ne_zero)
 have hmin:=minpoly.natDegree_le (A:=F) d
 rw [← hm,natDegree_X_pow_sub_C] at hmin
 exact (not_lt_of_ge hmin) h
section Bounds
variable {A B E :Type} [za6 A] [ztn A] [IsLocalRing A]
 [za6 B] [IsDedekindDomain B] [zZE A B] [Module.Finite A B] [Module.Flat A B]
 [zrb E] [zZE B E] [z0o B E]
private theorem local_degree_bounds (q:HeightOneSpectrum B)
   [q.asIdeal.LiesOver (maximalIdeal A)] :
   0<q.asIdeal.ramificationIdx A∧q.asIdeal.ramificationIdx A≤zsE A B ∧
   q.asIdeal.inertiaDeg A≤zsE A B:= by
 classical
 let m:=maximalIdeal A
 let Q:m.primesOver B:=⟨q.asIdeal,q.isPrime,inferInstance⟩
 have he :0<q.asIdeal.ramificationIdx A:=q.asIdeal.ramificationIdx_pos A
 have hf :0<q.asIdeal.inertiaDeg A:=q.asIdeal.inertiaDeg_pos A
 have h:q.asIdeal.ramificationIdx A*q.asIdeal.inertiaDeg A≤zsE A B:= by
   rw [← Ideal.sum_ramification_inertia_eq_finrank m B]
   exact Finset.single_le_sum (f := fun P:m.primesOver B =>
     P.val.ramificationIdx A*P.val.inertiaDeg A) (fun _ _=>Nat.zero_le _) (Finset.mem_univ Q)
 exact ⟨he,(Nat.le_mul_of_pos_right _ hf).trans h,(Nat.le_mul_of_pos_left _ he).trans h⟩
theorem tame_of_adic (q:HeightOneSpectrum B) [q.asIdeal.LiesOver (maximalIdeal A)]
   {z t:A} (ht:maximalIdeal A=zye {t}) (ht0:algebraMap A B t≠0)
   (hz :IsUnit z) (hp:p.Prime) (hdeg:zsE A B<p)
   (hn : ∀ b:ResidueField A,b^p≠residue A z) :
   TamePlace (q.valuation E) (algebraMap B E (algebraMap A B z))
     (algebraMap B E (algebraMap A B t)) := by
 have ⟨he,hram,hf⟩:=local_degree_bounds (A:=A) q
 have hzv :q.valuation E (algebraMap B E (algebraMap A B z))=1 := by
   rw [q.valuation_of_algebraMap,HeightOneSpectrum.intValuation_eq_one_iff]
   exact fun hm=>q.isPrime.ne_top (q.asIdeal.eq_top_of_isUnit_mem hm (hz.map (algebraMap A B)))
 refine ⟨q.valuation_surjective E,⟨q.asIdeal.ramificationIdx A,he,hram.trans_lt hdeg,?_⟩,hzv,?_⟩
 · have hspan:Ideal.map (algebraMap A B) (maximalIdeal A)=zye {algebraMap A B t} := by
     rw [ht,Ideal.map_span,zyk]
   have hmap :Ideal.map (algebraMap A B) (maximalIdeal A) ≠ ⊥ := by
     rwa [hspan,ne_eq,Ideal.span_singleton_eq_bot]
   rw [q.valuation_of_algebraMap,q.intValuation_eq_exp_neg_multiplicity ht0,
     Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (maximalIdeal A) q.asIdeal hmap,hspan]
 · let m:=maximalIdeal A
   let:zrb (A ⧸ m) :=zxv m
   let:zrb (B ⧸ q.asIdeal) :=zxv q.asIdeal
   have hres :zsE (A ⧸ m) (B ⧸ q.asIdeal)<p :=
     (Ideal.inertiaDeg_eq_of_isMaximal m q.asIdeal) ▸ hf.trans_lt hdeg
   let e :=adicResidue (E :=E) q
   intro b hb
   obtain ⟨d,rfl⟩:=e.surjective b
   have hd:d^p=algebraMap (A ⧸ m) (B ⧸ q.asIdeal) (zVv m z) := by
     apply e.injective
     rw [map_pow,Ideal.Quotient.algebraMap_mk_of_liesOver,adicResidue_mk q _ hzv.le]
     exact hb
   exact no_new_root hp hres hn d hd
end Bounds
end
end qGA3mAd
end
