import ProximityPrize.SubmissionLower.Z8rcaBc
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, Ideal → znc, Ideal.IsPrime.comap → zCL, Ideal.Quotient.mk → zVv, Ideal.comap_comap → zg6, Ideal.comap_map_of_surjective → zEk, Ideal.map_isPrime_of_surjective → zHO, Ideal.map_map → z0L, Ideal.quotientEquiv → z9x, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.map_X → z7N, MvPolynomial.rename → zHw, MvPolynomial.renameEquiv → zGY, MvPolynomial.ringHom_ext → zXT, Nat.add_le_add → z9f, Nat.mul_le_mul_right → ztf, Polynomial.eval₂RingHom → zqf, Polynomial.eval₂_eq_sum → zI6, Polynomial.ringHom_ext → z86, RingHom.comp_apply → zQb, RingHom.comp_assoc → zxS, RingHom.congr_fun → zLs, RingHom.injective_iff_ker_eq_bot → zli, RingHom.ker → zdq, RingHom.ker_eq_comap_bot → zPx, Set.image_singleton → zyk
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qgscZIa
noncomputable section
open Polynomial
open P6_7_1 (Input Poles Rectangle rectBank)
open q3rjQGe (AxisSection)
open cu (FX aZ Jet)

open gT (Ambient aQ ek Pp iJ A7 pZ oi)
open pI (oU)
open OH (ak7 Q6)
open ac4 (Hr btg Cl)
open private a2f dGs from ProximityPrize.SubmissionLower.Z
open private cRR i9 extend from ProximityPrize.SubmissionLower.U
open private ak7.sum_le ak7.pow_le ep8 from ProximityPrize.SubmissionLower.U
open scoped BigOperators
theorem rect_exp {x :Input} {P:Poles x} {s :Rectangle} {W:ℕ} {g:Jet}
    (hg:g∈rectBank P s W) {j i:ℕ} {e :Fin 2 →₀ ℕ}
    (he : ((g.coeff j).coeff i).coeff e≠0) :
    e 0≤ s.z∧e 1≤ s.t:= by
  by_contra h
  have hbad:s.z<e 0∨s.t<e 1 := by omega
  have hspan:rectBank P s W≤LinearMap.ker (a2f j i e) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨Q,hQ,rfl⟩
    apply LinearMap.mem_ker.mpr
    exact dGs Q j i e (fun b=>hQ.2 j i b e hbad)
  exact he (LinearMap.mem_ker.mp (hspan hg))
theorem axis_finite (q:znc Ambient) [q.IsPrime]
    (hd:ringKrullDim (gT.gk q)=1) (a :Fin 2) :
    Module.Finite aQ (AxisSection q a) := by
  have h:i9 q (z9v (fixedAxis a)) 0=axisIdeal q a := by
    simp only [i9,extend,axisIdeal,Q6,map_zero,mul_zero,add_zero,
      z7N,Pp]
  change Module.Finite aQ ((MvPolynomial (Fin 4) aQ) ⧸ axisIdeal q a)
  rw [← h]
  exact cRR q (z9v (fixedAxis a)) 0 hd
theorem axis_localization (q:znc Ambient) (a :Fin 2) [q.IsPrime] :
    axisIdeal q a = ⊤ ∨ ((axisIdeal q a).IsPrime∧(axisIdeal q a).comap Q6=q) := by
  classical
  let σ:=Equiv.swap (fixedAxis a) (2 :Fin 4)
  let e :=zGY FX σ
  let E :=zGY aQ σ
  let Q:=q.map e.toRingEquiv.toRingHom
  have hk :zdq e.toRingEquiv.toRingHom = ⊥ :=
    (zli _).mp e.injective
  have hQ:Q.IsPrime :=zHO e.surjective (hk ▸ bot_le)
  have hcomm:E.toRingEquiv.toRingHom.comp Q6 =
      (Cl FX).comp e.toRingEquiv.toRingHom:= by
    apply zXT
    · intro c
      simp [Q6,Cl,e,E,zGY,zQb]
    · intro i
      simp [Q6,Cl,e,E,zGY,zQb]
  have hspan:E (Pp (fixedAxis a))=Pp (2 :Fin 4) := by
    change zHw σ (Pp (fixedAxis a))= _
    simp [Pp,σ]
  have hmap : (axisIdeal q a).map E.toRingEquiv.toRingHom=Hr Q:= by
    rw [axisIdeal,Ideal.map_sup,z0L,hcomm,← z0L,Ideal.map_span,
      zyk]
    exact congrArg (fun f=>Q.map (Cl FX) ⊔ Ideal.span {f}) hspan
  have hkE :zdq E.toRingEquiv.toRingHom = ⊥ :=
    (zli _).mp E.injective
  have hback : (Hr Q).comap E.toRingEquiv.toRingHom=axisIdeal q a := by
    rw [← hmap,zEk E.toRingEquiv.toRingHom E.surjective,
      ← zPx,hkE,sup_bot_eq]
  obtain ⟨hdom,hnodom⟩:=btg Q hQ
  by_cases h:zq4
      ((zVv Q).comp pI.F7)
  · obtain ⟨hp,hc⟩:=hdom h
    have : (Hr Q).IsPrime :=hp
    refine Or.inr ⟨hback ▸ zCL E.toRingEquiv.toRingHom,?_⟩
    rw [← hback,zg6,hcomm,← zg6,hc]
    change (q.map e.toRingEquiv.toRingHom).comap e.toRingEquiv.toRingHom=q
    rw [zEk e.toRingEquiv.toRingHom e.surjective,
      ← zPx,hk,sup_bot_eq]
  · exact Or.inl (hback.symm.trans ((congrArg (Ideal.comap E.toRingEquiv.toRingHom)
      (hnodom h)).trans Ideal.comap_top))
private theorem axis_fixed (q:znc Ambient) (a :Fin 2) :
    axisCoord q a (fixedAxis a)=algebraMap aQ (AxisSection q a) (ek 1) := by
  have h:zVv (axisIdeal q a) (Pp (fixedAxis a))=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  change zVv (axisIdeal q a)
    (z9v (fixedAxis a)-MvPolynomial.C (ek 1))=0 at h
  rw [map_sub,sub_eq_zero] at h
  change zVv (axisIdeal q a) (z9v (fixedAxis a)) =
    zVv (axisIdeal q a) (znf (ek 1))
  exact h
private def XD (q:znc Ambient) (a :Fin 2) :aZ →+* AxisSection q a :=
  MvPolynomial.eval₂Hom
    ((algebraMap aQ (AxisSection q a)).comp (algebraMap FX aQ))
    (fun k=>axisCoord q a (freeAxis k))
private theorem axis_eval (q:znc Ambient) (a :Fin 2) (g:Jet) :
    axisRestrict q a (iJ g) =
      g.eval₂ (zqf (XD q a) (axisCoord q a 2)) (axisCoord q a 3) := by
  let r :=axisRestrict q a
  have hx (i:Fin 4) :r (z9v i)=axisCoord q a i:= by
    change zVv (axisIdeal q a) (Q6 (z9v i))= _
    rw [Q6,z7N]
    rfl
  have hbase :r.comp znf =
      (algebraMap aQ (AxisSection q a)).comp (algebraMap FX aQ) := by
    apply RingHom.ext
    intro d
    change zVv (axisIdeal q a) (Q6 (znf d))= _
    rw [Q6,MvPolynomial.map_C,← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap]
    rfl
  have hseed : (r.comp oi).comp pZ=XD q a := by
    apply zXT
    · intro d
      simpa [pZ,oi,XD] using zLs hbase d
    · intro i
      fin_cases i
      · simp [pZ,oi,XD,hx]
      · simp [pZ,oi,XD,hx]; rfl
  have hroot : (r.comp oi).comp A7 =
      zqf (XD q a) (axisCoord q a 2) := by
    apply z86
    · intro f
      simpa [A7] using zLs hseed f
    · simp [A7,oi,hx]
  change r (g.eval₂ _ _)= _
  rw [Polynomial.hom_eval₂,← zxS,hroot,hx]
private theorem seed_order (q:znc Ambient) (a :Fin 2)
    (d:ak7 aQ (AxisSection q a)) (f :aZ) {U:ℕ}
    (hf : ∀ e∈f.support,e a≤U) :
    d.order (XD q a f)≤U*d.order (axisCoord q a (freeAxis a)) := by
  classical
  change d.order (f.eval₂ _ _)≤_
  rw [MvPolynomial.eval₂_eq']
  apply ak7.sum_le d
  intro e he
  rw [Fin.prod_univ_two]
  have h:=hf e he
  have hs (i:Fin 2) :d.order (axisCoord q a (freeAxis i)^e i) ≤
      e i*d.order (axisCoord q a (freeAxis i)) :=ak7.pow_le d _ _
  refine (d.mul_le _ _).trans ?_
  simp only [zQb,d.constant,zero_add]
  refine ((d.mul_le _ _).trans (z9f (hs 0) (hs 1))).trans ?_
  fin_cases a
  · change e 0*d.order (axisCoord q 0 (freeAxis 0)) +
      e 1*d.order (axisCoord q 0 (fixedAxis 0))≤U*d.order (axisCoord q 0 (freeAxis 0))
    change ak7 aQ (AxisSection q (0:Fin 2)) at d
    rw [axis_fixed q 0,d.constant,mul_zero,add_zero]
    exact ztf _ h
  · change e 0*d.order (axisCoord q 1 (fixedAxis 1)) +
      e 1*d.order (axisCoord q 1 (freeAxis 1))≤U*d.order (axisCoord q 1 (freeAxis 1))
    change ak7 aQ (AxisSection q (1 :Fin 2)) at d
    rw [axis_fixed q 1,d.constant,mul_zero,zero_add]
    exact ztf _ h
theorem row_axis_poles {x :Input} {P:Poles x} {s :Rectangle} {W:ℕ} {g:Jet}
    (hg:g∈rectBank P s W) (hJ:s.J≤ s.B) (hc:oU g s.box)
    (q:znc Ambient) (a :Fin 2) (d:ak7 aQ (AxisSection q a)) :
    d.order (axisRestrict q a (iJ g)) ≤
      (if a=0 then s.z else s.t)*d.order (axisCoord q a (freeAxis a)) +
      (s.B - s.J)*d.order (axisCoord q a 2) +
      s.J*max (d.order (axisCoord q a 2)) (d.order (axisCoord q a 3)) := by
  let U:=if a=0 then s.z else s.t
  let z :=d.order (axisCoord q a (freeAxis a))
  let y :=d.order (axisCoord q a 2)
  let v :=d.order (axisCoord q a 3)
  change _≤U*z+(s.B-s.J)*y+s.J*max y v
  rw [axis_eval,zI6,Polynomial.sum]
  apply ak7.sum_le d
  intro j _
  rw [Polynomial.coe_eval₂RingHom,zI6,Polynomial.sum,Finset.sum_mul]
  apply ak7.sum_le d
  intro i hi
  obtain ⟨hij,hj,_⟩:=hc j i (Polynomial.mem_support_iff.mp hi)
  have hseed (e) (he :e∈((g.coeff j).coeff i).support) :e a≤U:= by
    obtain ⟨hz,ht⟩:=rect_exp hg (MvPolynomial.mem_support_iff.mp he)
    fin_cases a <;> first | exact hz | exact ht
  calc
    _≤(d.order (XD q a ((g.coeff j).coeff i)) +
          d.order (axisCoord q a 2^i))+d.order (axisCoord q a 3^j) :=
      (d.mul_le _ _).trans (Nat.add_le_add_right (d.mul_le _ _) _)
    _≤(U*z+i*y)+j*v :=z9f
      (z9f (seed_order q a d _ hseed) (ak7.pow_le d _ _)) (ak7.pow_le d _ _)
    _≤_:= by
      rw [Nat.add_assoc,Nat.add_assoc]
      exact Nat.add_le_add_left (ep8 hJ hij hj) _
end
end qgscZIa
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qJVcWac
noncomputable section
open q3rjQGe (AxisSection)
open qgscZIa (axisIdeal fixedAxis)
open cu (FX)
open gT (Ambient aQ gk oi pZ Pp)
open pI (xN F7)
open OH (Q6)
open ac4 (Hr btg Cl)
open private co5 from ProximityPrize.SubmissionLower.G
theorem axis_geometry (q:znc Ambient) (a :Fin 2) (hq:xN q) :
    (axisIdeal q a).IsPrime∧ringKrullDim (AxisSection q a)=1 := by
  let σ:=Equiv.swap (fixedAxis a) (2 :Fin 4)
  let e :=zGY FX σ
  let E :=zGY aQ σ
  let Q:=q.map e.toRingEquiv.toRingHom
  let b:Fin 2 :=if a=0 then 1 else 0
  let j:=Polynomial.toMvPolynomial (R:=FX) b
  have hb:Fin.castLE (by decide :3≤4) (Fin.castLE (by decide :2≤3) b) =
      fixedAxis a := by fin_cases a <;> rfl
  have hk :zdq e.toRingEquiv.toRingHom = ⊥ :=
    (zli _).mp e.injective
  let:q.IsPrime :=hq.prime
  have hQ:Q.IsPrime :=zHO e.surjective (hk ▸ bot_le)
  let u:=z9x q Q e.toRingEquiv rfl
  have hu:u.toRingHom.comp (zVv q) =
      (zVv Q).comp e.toRingEquiv.toRingHom:=rfl
  have hj:e.toRingEquiv.toRingHom.comp ((oi.comp pZ).comp j.toRingHom) =
      F7:= by
    apply z86
    · intro c
      simp [j,oi,pZ,F7,e,zGY]
    · simp [j,oi,pZ,F7,e,zGY,σ,hb]
  have hdom:zq4 ((zVv Q).comp F7) := by
    rw [← hj,← zxS,← hu]
    exact u.injective.comp ((co5 hq).comp (Polynomial.toMvPolynomial_injective b))
  have hcomm:E.toRingEquiv.toRingHom.comp Q6 =
      (Cl FX).comp e.toRingEquiv.toRingHom:= by
    apply zXT
    · intro c
      simp [Q6,Cl,e,E,zGY,zQb]
    · intro i
      simp [Q6,Cl,e,E,zGY,zQb]
  have hmap : (axisIdeal q a).map E.toRingEquiv.toRingHom=Hr Q:= by
    rw [axisIdeal,Ideal.map_sup,z0L,hcomm,← z0L,Ideal.map_span,
      zyk]
    have hspan:E (Pp (fixedAxis a))=Pp (2 :Fin 4) := by
      change zHw σ (Pp (fixedAxis a))= _
      simp [Pp,σ]
    exact congrArg (fun f=>Q.map (Cl FX) ⊔ Ideal.span {f}) hspan
  let: (Hr Q).IsPrime :=((btg Q hQ).1 hdom).1
  have hkE :zdq E.toRingEquiv.toRingHom = ⊥ :=
    (zli _).mp E.injective
  have hback : (Hr Q).comap E.toRingEquiv.toRingHom=axisIdeal q a := by
    rw [← hmap,zEk E.toRingEquiv.toRingHom E.surjective,
      ← zPx,hkE,sup_bot_eq]
  refine ⟨hback ▸ zCL E.toRingEquiv.toRingHom,?_⟩
  calc
    ringKrullDim (AxisSection q a)=ringKrullDim (gk (Hr Q)) :=
      (z9x (axisIdeal q a) (Hr Q) E.toRingEquiv hmap.symm).ringKrullDim
    _=1 :=czb.proof Q hQ (u.ringKrullDim.symm.trans hq.dimension) hdom
end
end qJVcWac
end
