import ProximityPrize.SubmissionLower.ZVQ2TVd
import ProximityPrize.SubmissionLower.Z84uvqb
import ProximityPrize.SubmissionLower.ZrU0ida
import ProximityPrize.SubmissionLower.ZJb37yc
import ProximityPrize.SubmissionLower.ZUucocd
import ProximityPrize.SubmissionLower.ZjjMFxd
import ProximityPrize.SubmissionLower.ZnAYdcb
import ProximityPrize.SubmissionLower.CmpCSum
import ProximityPrize.SubmissionLower.Z7Epuse
import ProximityPrize.SubmissionLower.ZCuFj9c
import ProximityPrize.SubmissionLower.ZjZ6ihd
import ProximityPrize.SubmissionLower.ZZekYUb
set_option Elab.async false
open _root_ renaming Fintype.sum_option → zy6, Function.Injective → zq4, MvPolynomial → z3y, MvPolynomial.optionEquivLeft → zpj, MvPolynomial.optionEquivLeft_coeff_some_coeff_none → zL1, MvPolynomial.uniqueAlgEquiv → zpe, Nat.add_zero → zXY, Nat.lt_of_not_ge → znR, Nat.lt_succ_of_le → zB1, Nat.mul_one → zMo, Nat.mul_zero → zvM, Nat.succ_le_of_lt → zxX, Polynomial.X → z7y, Polynomial.coeff_map → z0b, Polynomial.ext → zXJ, Polynomial.induction_on' → zCU, Polynomial.mapEquiv → zNc
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
section
set_option autoImplicit true
namespace qoK3iCb
open P5 (p)
open P5_7_2 (fO)
open q7F2qKe (wX weakAgreement scalarWitness aSz originCount afterFree)
open qB9xHGe (StopRates)
private def wB (b:fO) :Bool:=(List.range 52).all fun i=>scalarCheck b (i+3) (extra b (i+3)) (copies b (i+3))
private theorem wit_of {b:fO} (h:wB b=true) :BandWitness b:=
 witness_of_checks fun i=>List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
private def fB (b:fO) :Bool:=
 decide (0≤num (uq b 36) 36) &&
 decide ((1-floorRate/graphRate 1)*(1+3*262144/((weakAgreement-wX b:ℕ) :ℚ)) ≤ aoF uq b 0) &&
 decide ((13+8*262144/((weakAgreement-wX b:ℕ) :ℚ))*(graphRate 2-floorRate)/(graphRate 2-16)≤aoF uq b 0) &&
 (List.range 52).all fun g=>decide (FloorGrade uq b (g+3))
private theorem flo_of {b:fO} (h:fB b=true) :FloorOK uq b := by
 unfold fB at h
 rw [Bool.and_eq_true,Bool.and_eq_true,Bool.and_eq_true] at h
 obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩:=h
 exact ⟨of_decide_eq_true h1,of_decide_eq_true h2,of_decide_eq_true h3,
  fun g=>of_decide_eq_true (List.all_eq_true.mp h4 g.val (List.mem_range.mpr g.isLt))⟩
private def sB (b:fO) :Bool:=
 (List.range (originCount b)).all fun o=>(List.range (afterFree b)).all fun j=>rowCheck b o (j+1) && fastCheck uq b o (j+1)
private theorem sto_of {b:fO} (hw:BandWitness b) (hf:FloorOK uq b) (h:sB b=true) :BandStops b := by
 intro o j
 have h1:=List.all_eq_true.mp (List.all_eq_true.mp h o.val (List.mem_range.mpr o.isLt)) j.val (List.mem_range.mpr j.isLt)
 rw [Bool.and_eq_true] at h1
 exact stop_of_checks hw hf h1.1 h1.2
end qoK3iCb
end
section
set_option autoImplicit true
namespace qoK3iCb
private abbrev b6:P5_7_2.fO:=⟨6,by decide⟩
private theorem w6:BandWitness b6:=wit_of (by decide +kernel)
private theorem f6:FloorOK uq b6:=flo_of (by decide +kernel)
theorem r6:BandStops b6:=sto_of w6 f6 (by decide +kernel)
private abbrev b7:P5_7_2.fO:=⟨7,by decide⟩
private theorem w7:BandWitness b7:=wit_of (by decide +kernel)
private theorem f7:FloorOK uq b7:=flo_of (by decide +kernel)
theorem r7:BandStops b7:=sto_of w7 f7 (by decide +kernel)
end qoK3iCb
end
section
set_option autoImplicit true
namespace qoK3iCb
private abbrev b4 :P5_7_2.fO:=⟨4,by decide⟩
private theorem w4 :BandWitness b4 :=wit_of (by decide +kernel)
private theorem f4 :FloorOK uq b4 :=flo_of (by decide +kernel)
theorem r4 :BandStops b4 :=sto_of w4 f4 (by decide +kernel)
private abbrev b5:P5_7_2.fO:=⟨5,by decide⟩
private theorem w5:BandWitness b5:=wit_of (by decide +kernel)
private theorem f5:FloorOK uq b5:=flo_of (by decide +kernel)
theorem r5:BandStops b5:=sto_of w5 f5 (by decide +kernel)
end qoK3iCb
end
section
set_option autoImplicit true
namespace qoK3iCb
private abbrev b2 :P5_7_2.fO:=⟨2,by decide⟩
private theorem w2 :BandWitness b2 :=wit_of (by decide +kernel)
private theorem f2 :FloorOK uq b2 :=flo_of (by decide +kernel)
theorem r2 :BandStops b2 :=sto_of w2 f2 (by decide +kernel)
private abbrev b3:P5_7_2.fO:=⟨3,by decide⟩
private theorem w3:BandWitness b3:=wit_of (by decide +kernel)
private theorem f3:FloorOK uq b3:=flo_of (by decide +kernel)
theorem r3:BandStops b3:=sto_of w3 f3 (by decide +kernel)
end qoK3iCb
end
section
set_option autoImplicit true
namespace qoK3iCb
private abbrev b8:P5_7_2.fO:=⟨8,by decide⟩
private theorem w8:BandWitness b8:=wit_of (by decide +kernel)
private theorem f8:FloorOK uq b8:=flo_of (by decide +kernel)
theorem r8:BandStops b8:=sto_of w8 f8 (by decide +kernel)
private abbrev b9:P5_7_2.fO:=⟨9,by decide⟩
private theorem w9:BandWitness b9:=wit_of (by decide +kernel)
private theorem f9:FloorOK uq b9:=flo_of (by decide +kernel)
theorem r9:BandStops b9:=sto_of w9 f9 (by decide +kernel)
end qoK3iCb
end
section
set_option autoImplicit true
namespace qoK3iCb
private abbrev b0:P5_7_2.fO:=⟨0,by decide⟩
private theorem w0:BandWitness b0:=wit_of (by decide +kernel)
private theorem f0:FloorOK uq b0:=flo_of (by decide +kernel)
theorem r0:BandStops b0:=sto_of w0 f0 (by decide +kernel)
private abbrev b1 :P5_7_2.fO:=⟨1,by decide⟩
private theorem w1 :BandWitness b1 :=wit_of (by decide +kernel)
private theorem f1 :FloorOK uq b1 :=flo_of (by decide +kernel)
theorem r1 :BandStops b1 :=sto_of w1 f1 (by decide +kernel)
end qoK3iCb
end
section
set_option autoImplicit true
namespace qoK3iCb
private abbrev b10 :P5_7_2.fO:=⟨10,by decide⟩
private theorem w10 :BandWitness b10 :=wit_of (by decide +kernel)
private theorem Zd:FloorOK uq b10 :=flo_of (by decide +kernel)
theorem dz :BandStops b10 :=sto_of w10 Zd (by decide +kernel)
private abbrev b11 :P5_7_2.fO:=⟨11,by decide⟩
private theorem XL:BandWitness b11 :=wit_of (by decide +kernel)
private theorem Zp:FloorOK uq b11 :=flo_of (by decide +kernel)
theorem dD:BandStops b11 :=sto_of XL Zp (by decide +kernel)
end qoK3iCb
end
section
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q81Yhob
noncomputable section
open Polynomial
open scoped Classical
open cu (L)
open P5_7_7 (Dg)
open qZCRTge (Boxed cf coeff_pack boxed_pack pack)
open private boxed_bounds from ProximityPrize.SubmissionLower.Z84uvqb
private theorem bOH {A:Type*} [CommSemiring A] (P:A[X][X]) (i j:ℕ) :
   ((Bivariate.swap P).coeff i).coeff j=(P.coeff j).coeff i:= by
 induction P using zCU with
 | add P Q hp hq=>simp only [map_add,coeff_add,hp,hq]
 | monomial n P =>
   induction P using zCU with
   | add P Q hp hq=>simp only [map_add,coeff_add,hp,hq]
   | monomial m c =>
     rw [Bivariate.swap_monomial_monomial]
     by_cases hi:m=i <;> by_cases hj:n=j <;> simp [coeff_monomial,hi,hj]
private def view:Dg ≃+* Dg :=
 (mapEquiv (Bivariate.swap (R:=L)).toRingEquiv).trans
   (Bivariate.swap (R:=L[X])).toRingEquiv
private theorem bPK (P:Dg) (i j k :ℕ) :
  (((view P).coeff k).coeff i).coeff j=cf P i j k := by
 change (((Bivariate.swap (P.map (Bivariate.swap (R:=L)).toRingHom)).coeff k).coeff i).coeff j= _
 rw [bOH,coeff_map]
 exact bOH _ _ _
private theorem view_modulus (a :L) (M:ℕ) :
  view (C (C (((z7y:L[X]) - C a)^M)))=(z7y - C (C (C a)))^M:= by
 change Bivariate.swap ((C (C (((z7y:L[X]) - C a)^M)) :Dg).map
  (Bivariate.swap (R:=L)).toRingHom)= _
 rw [map_C,Bivariate.swap_C]
 change (Bivariate.swap (R:=L) (C (((z7y:L[X]) - C a)^M))).map C= _
 rw [Bivariate.swap_C]
 simp only [Polynomial.map_pow,Polynomial.map_sub,map_X,map_C]
private theorem fresh {F:Dg} (hF:view F≠0) :
  ∃ a :L,¬ (view F).IsRoot (C (C a)) := by
 by_contra! h
 let f :L→ L[X][X] := fun a=>C (C a)
 have hf :zq4 f :=C_injective.comp C_injective
 exact (Set.infinite_range_of_injective hf)
  ((finite_setOfPred_isRoot hF).subset (Set.range_subset_iff.mpr h))
private theorem nondivisible {H F:Dg} {a :L} {M:ℕ}
  (hH :view H≠0) (hF:view F≠0) (ha : ¬ (view F).IsRoot (C (C a)))
  (hdeg: (view H).natDegree<M) :
  ¬ C (C (((z7y:L[X]) - C a)^M))∣H*F:= by
 intro hd
 have hd' := _root_.map_dvd view hd
 rw [map_mul,view_modulus] at hd'
 have hz :=mul_ne_zero hH hF
 have hm:=(le_rootMultiplicity_iff hz).mpr hd'
 rw [rootMultiplicity_mul hz,rootMultiplicity_eq_zero ha,add_zero] at hm
 have hb:=natDegree_le_of_dvd ((le_rootMultiplicity_iff hH).mp hm) hH
 rw [(monic_X_sub_C _).natDegree_pow,natDegree_X_sub_C,mul_one] at hb
 exact (not_le_of_gt hdeg) hb
private theorem gLc {H :Dg} {g v M:ℕ} (hM:0<M)
  (hb:Boxed H g v (fun _=>M)) : (view H).natDegree<M:= by
 suffices (view H).natDegree≤M-1 by omega
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro k hk
 apply zXJ; intro i
 apply zXJ; intro j
 rw [coeff_zero,coeff_zero,bPK]
 by_contra hn
 have h:=(hb i j k hn).2.2
 change k<M at h
 omega
private def lift (e T:ℕ) (t:L[X] →ₗ[L] L[X]) :Dg →ₗ[L] Dg :=
  ((ofFn (e+1)).restrictScalars L).comp (LinearMap.pi fun i =>
    ((ofFn (T+1)).restrictScalars L).comp (LinearMap.pi fun j =>
      t.comp (((lcoeff (L[X]) j).restrictScalars L).comp
        ((lcoeff (L[X][X]) i).restrictScalars L))))
private theorem cXH (e T:ℕ) (t:L[X] →ₗ[L] L[X]) (P:Dg) (i j:ℕ) :
    ((lift e T t P).coeff i).coeff j =
      if i≤e∧j≤T then t ((P.coeff i).coeff j) else 0:= by
  change ((ofFn (e+1) fun x=>ofFn (T+1) fun y=>t ((P.coeff x).coeff y)).coeff i).coeff j= _
  by_cases hi:i≤e
  · rw [ofFn_coeff_eq_val_of_lt _ (zB1 hi)]
    by_cases hj:j≤T
    · rw [ofFn_coeff_eq_val_of_lt _ (zB1 hj),ite_eq_left ⟨hi,hj⟩]
    · rw [ofFn_coeff_eq_zero_of_ge _ (zxX (znR hj)),
        ite_eq_right fun ht=>hj ht.2]
  · rw [ofFn_coeff_eq_zero_of_ge _ (zxX (znR hi)),coeff_zero,
      ite_eq_right fun ht=>hi ht.1]
private theorem cXJ (e T:ℕ) (t:L[X] →ₗ[L] L[X]) (P:Dg) :
  (lift e T t P).natDegree≤e :=
 Nat.le_of_lt_succ (ofFn_natDegree_lt (Nat.zero_lt_succ e) _)
private theorem seed_mul {H F:Dg} {v h:ℕ}
  (hH : ∀ i,(H.coeff i).natDegree≤v) (hF : ∀ i,(F.coeff i).natDegree≤h)
  (i:ℕ) : ((H*F).coeff i).natDegree≤v+h:= by
 rw [coeff_mul]
 apply natDegree_sum_le_of_forall_le
 intro x _
 exact natDegree_mul_le.trans (Nat.add_le_add (hH x.1) (hF x.2))
theorem proof :qZCRTge.c1 := by
  intro F g h v M hF hM hseed
  have hvF:view F≠0:= fun hz=>hF (view.injective (hz.trans (map_zero view).symm))
  obtain ⟨a,ha⟩:=fresh hvF
  let D:=((z7y:L[X]) - C a)^M
  let e :=F.natDegree+g
  let T:=v+h
  let A:=(LinearMap.mulRight L F).comp (pack g v (fun _=>M))
  let R:=(lift e T (modByMonicHom D)).comp A
  let Q:=(lift e T (divByMonicHom D)).comp A
  have hD:D.Monic:=(monic_X_sub_C a).pow M
  have hd:D.natDegree=M:= by
    change (((z7y:L[X]) - C a)^M).natDegree=M
    rw [(monic_X_sub_C a).natDegree_pow,natDegree_X_sub_C,mul_one]
  have hd1 :D ≠1 := fun hz=>hM.ne' (hd.symm.trans (by rw [hz,natDegree_one]))
  have decomp (q:_) :A q=R q+C (C D)*Q q:= by
    obtain ⟨hg,hv⟩:=boxed_bounds (boxed_pack q)
    have he : (A q).natDegree≤e := by
      change (pack g v (fun _=>M) q*F).natDegree≤F.natDegree+g
      apply natDegree_mul_le.trans
      omega
    have ht : ∀ i,((A q).coeff i).natDegree≤T:=seed_mul hv hseed
    apply zXJ; intro i
    apply zXJ; intro j
    simp only [R,Q,LinearMap.comp_apply,coeff_add,coeff_C_mul,cXH]
    by_cases hij:i≤e∧j≤T
    · simp only [ite_eq_left hij]
      exact (modByMonic_add_div (((A q).coeff i).coeff j) D).symm
    · simp only [ite_eq_right hij,mul_zero,add_zero]
      by_cases hi:i≤e
      · exact coeff_eq_zero_of_natDegree_lt ((ht i).trans_lt
          (znR (fun hj=>hij ⟨hi,hj⟩)))
      · rw [coeff_eq_zero_of_natDegree_lt (he.trans_lt (znR hi)),coeff_zero]
  refine ⟨a,R,?_,?_⟩
  · apply (injective_iff_map_eq_zero R).mpr
    intro q hq
    let H :=pack g v (fun _=>M) q
    have hH :H=0:= by
      by_contra hn
      apply nondivisible (fun hz=>hn (view.injective (hz.trans (map_zero view).symm)))
        hvF ha (gLc hM (boxed_pack q))
      refine ⟨Q q,?_⟩
      change A q=C (C D)*Q q
      rw [decomp q,hq,zero_add]
    funext r
    rw [← coeff_pack q r,show pack g v (fun _=>M) q=0 from hH]
    simp only [cf,coeff_zero,Pi.zero_apply]
  · intro q
    refine ⟨?_,Q q,cXJ _ _ _ _,decomp q⟩
    intro i j k hn
    change (((lift e T (modByMonicHom D) (A q)).coeff i).coeff j).coeff k≠0 at hn
    rw [cXH] at hn
    by_cases hij:i≤e∧j≤T
    · rw [ite_eq_left hij] at hn
      have hrem:=natDegree_modByMonic_lt (((A q).coeff i).coeff j) hD hd1
      rw [hd] at hrem
      exact ⟨hij.1,hij.2,(le_natDegree_of_ne_zero hn).trans_lt hrem⟩
    · exact (hn (by rw [ite_eq_right hij,coeff_zero])).elim
end
end q81Yhob
end
section
namespace qCAunta
noncomputable section
open Polynomial
open cu (L FX)
open P5_7_7 (Dg ek embed)
open qZCRTge (cf)
open private generic_irred from ProximityPrize.SubmissionLower.ZsWhgLc
open scoped nonZeroDivisors
private abbrev UR:=L[X][X]
private abbrev aQ:=FractionRing FX[X]
attribute [local instance] Polynomial.algebra
local instance :IsFractionRing UR aQ:= by
  let S:Submonoid UR:=(L[X])⁰.map (C:L[X] →+* UR)
  have :IsLocalization S FX[X] :=Polynomial.isLocalization (L[X])⁰ FX
  have hinj:zq4 (algebraMap UR FX[X]) :=
    Polynomial.map_injective _ (IsFractionRing.injective L[X] FX)
  have he : (FX[X]⁰).comap (algebraMap UR FX[X])=UR⁰:= by
    ext f
    rw [Submonoid.mem_comap,mem_nonZeroDivisors_iff_ne_zero,
      mem_nonZeroDivisors_iff_ne_zero,map_ne_zero_iff _ hinj]
  rw [IsFractionRing,← he]
  exact IsLocalization.localization_localization_isLocalization_of_has_all_units S
    (FX[X]⁰) aQ (fun _ h=>h.mem_nonZeroDivisors)
private theorem raw_map (F:Dg) :
  F.map (algebraMap UR aQ)=ek (embed F) := by
 rw [IsScalarTower.algebraMap_eq UR FX[X] aQ]
 exact (Polynomial.map_map _ _ _).symm
private theorem raw_dvd {F G:Dg} (hf :Irreducible F)
  (he :Irreducible (embed F)) (hl:0<F.natDegree)
  (hn : ¬ IsCoprime (ek (embed F)) (ek (embed G))) :F∣G:= by
 let _:StrongNormalizationMonoid UR:=UniqueFactorizationMonoid.strongNormalizationMonoid
 let _:NormalizedGCDMonoid UR:=UniqueFactorizationMonoid.toNormalizedGCDMonoid _
 have hd:=((generic_irred he hl).isCoprime_or_dvd (ek (embed G))).resolve_left hn
 rw [← raw_map,← raw_map] at hd
 exact (hf.isPrimitive hl.ne').dvd_of_fraction_map_dvd_fraction_map hd
private abbrev Vars :=Option (Option Unit)
private def bg6:z3y (Option Unit) L ≃+* UR :=
 (zpj L Unit).toRingEquiv.trans
   (zNc (zpe L Unit).toRingEquiv)
private def expand:Dg ≃+* z3y Vars L :=
 (zNc bg6.symm).trans
   (zpj L (Option Unit)).toRingEquiv.symm
private theorem coeff_seed (f :z3y (Option Unit) L) (v :Option Unit →₀ ℕ) :
  ((bg6 f).coeff (v none)).coeff (v.some ())=f.coeff v := by
 change (((zpj L Unit f).map
  (zpe L Unit).toRingHom).coeff _).coeff _ = _
 rw [z0b]
 change ((zpe L Unit)
  ((zpj L Unit f).coeff _)).coeff _ = _
 rw [MvPolynomial.coeff_uniqueAlgEquiv,← Finsupp.unique_single v.some,
  zL1]
private theorem coeff_expand (F:Dg) (v :Vars →₀ ℕ) :
   (expand F).coeff v=cf F (v none) (v.some none) (v.some.some ()) := by
 have he : (zpj L (Option Unit)) (expand F) =
     F.map bg6.symm.toRingHom :=
   (zpj L (Option Unit)).toRingEquiv.apply_symm_apply _
 rw [← zL1,he,z0b]
 change (bg6.symm (F.coeff (v none))).coeff v.some= _
 simpa only [RingEquiv.apply_symm_apply] using
   (coeff_seed (bg6.symm (F.coeff (v none))) v.some).symm
private def weights (a b c:ℕ) :Vars→ℕ
 | none=>a
 | some none=>b
 | some (some _)=>c
private theorem c0Q (a b c:ℕ) (v :Vars →₀ ℕ) :
  Finsupp.weight (weights a b c) v=v none*a+v.some none*b+v.some.some ()*c:= by
 rw [Finsupp.weight_eq_sum,zy6,zy6]
 simp [weights,Finsupp.some_apply,smul_eq_mul,add_assoc]
private def deg (a b c:ℕ) (F:Dg) :ℕ :=
 (expand F).weightedTotalDegree (weights a b c)
private theorem le_deg {F:Dg} {i j k :ℕ} (h:cf F i j k≠0)
  (a b c:ℕ) :i*a+j*b+k*c≤deg a b c F:= by
 let v :Vars →₀ ℕ:=((Finsupp.single () k).optionElim j).optionElim i
 have hv : (expand F).coeff v≠0:= by simpa [coeff_expand,v] using h
 simpa [c0Q,v,deg] using
  MvPolynomial.le_weightedTotalDegree (weights a b c) (MvPolynomial.mem_support_iff.mpr hv)
private theorem deg_attained {F:Dg} (hF:F≠0) (a b c:ℕ) :
  ∃ i j k,cf F i j k≠0∧deg a b c F=i*a+j*b+k*c:= by
 have hn:expand F≠0:=(map_ne_zero_iff _ expand.injective).mpr hF
 obtain ⟨v,hv,he⟩:=Finset.exists_mem_eq_sup _ (MvPolynomial.support_nonempty.mpr hn)
  (Finsupp.weight (weights a b c))
 exact ⟨v none,v.some none,v.some.some (),
  (coeff_expand F v) ▸ MvPolynomial.mem_support_iff.mp hv,
  he.trans (c0Q a b c v)⟩
private theorem deg_mul {F Q:Dg} (hF:F≠0) (hQ:Q≠0) (a b c:ℕ) :
  deg a b c (F*Q)=deg a b c F+deg a b c Q:= by
 unfold deg
 rw [map_mul,MvPolynomial.weightedTotalDegree_mul _ _ _
  ((map_ne_zero_iff _ expand.injective).mpr hF) ((map_ne_zero_iff _ expand.injective).mpr hQ)]
theorem proof :qZCRTge.c2 := by
 intro F G g T u s W M hf he hl hlarge hordinate hseed hnarrow hcop
 by_cases hG:G=0
 · subst G
   exact ⟨0,(mul_zero _).symm,fun i j k h=>(h (by simp [cf])).elim⟩
 obtain ⟨Q,rfl⟩:=raw_dvd hf he hl hcop
 have hQ:=right_ne_zero_of_mul hG
 refine ⟨Q,rfl,?_⟩
 have hqOrd:Q.natDegree≤g:= by
   rw [natDegree_mul hf.ne_zero hQ] at hordinate
   omega
 have hqSeed :deg 0 1 0 Q≤T:= by
   obtain ⟨i,j,k,h,hj⟩:=deg_attained hG 0 1 0
   have hbound:=(le_natDegree_of_ne_zero (p:=(F*Q).coeff i)
     (show ((F*Q).coeff i).coeff j≠0 from fun hz=>h (by simp [cf,hz]))).trans (hseed i)
   simp only [zvM,zMo,Nat.zero_add,zXY] at hj
   rw [deg_mul hf.ne_zero hQ] at hj
   omega
 have hdegF:W<deg s 0 1 F+F.natDegree*u:= by
   obtain ⟨i,j,h,hw⟩:=hlarge
   have hterm :cf F i j (((F.coeff i).coeff j).natDegree)≠0 :=
     leadingCoeff_ne_zero.mpr h
   have hle :=le_deg hterm s 0 1
   simp only [zvM,zMo,zXY] at hle
   omega
 have hdegG:deg s 0 1 (F*Q)+(F.natDegree+g)*u<M:= by
   obtain ⟨i,j,k,h,hk⟩:=deg_attained hG s 0 1
   have hne : ((F*Q).coeff i).coeff j≠0:= fun hz=>h (by simp [cf,hz])
   have hle :=le_natDegree_of_ne_zero h
   have hb:=hnarrow i j hne
   simp only [zvM,zMo,zXY] at hk
   omega
 rw [deg_mul hf.ne_zero hQ,Nat.add_mul] at hdegG
 intro i j k h
 have hi:=(le_natDegree_of_ne_zero (p:= Q)
   (show Q.coeff i≠0 from fun hz=>h (by simp [cf,hz]))).trans hqOrd
 have hj:=(le_deg h 0 1 0).trans hqSeed
 have hk :=le_deg h s 0 1
 simp only [zvM,zMo,Nat.zero_add,zXY] at hj hk
 refine ⟨hi,hj,?_⟩
 change k<M-(W+1)-(g*u+i*s)
 omega
end
end qCAunta
end
section
set_option autoImplicit true
namespace qoK3iCb
open P5_7_2 (fO)
private theorem allStops (b:fO) :BandStops b:= by
 fin_cases b
 · exact r0
 · exact r1
 · exact r2
 · exact r3
 · exact r4
 · exact r5
 · exact r6
 · exact r7
 · exact r8
 · exact r9
 · exact dz
 · exact dD
 · exact dK
 · exact e8
theorem proof :qB9xHGe.c1 := by
 intro b o ho j _ hj hfree
 obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
 exact allStops b ⟨o,Finset.mem_range.mp ho⟩ ⟨i,by omega⟩
end qoK3iCb
end
section
set_option autoImplicit true
namespace q5oHm3d
open P5_7_2 (fO)
open q7F2qKe
def c1 :Prop := ∀ (b:fO),b.val<7 → ∀ o∈origins b,∀ j∈stops b,
 afterFree b<j→dqs b o j
def c2 :Prop := ∀ (b:fO),7≤b.val→b.val<12 → ∀ o∈origins b,∀ j∈stops b,
 afterFree b<j→dqs b o j
def c3:Prop := ∀ (b:fO),12≤b.val → ∀ o∈origins b,∀ j∈stops b,
 afterFree b<j→dqs b o j
end q5oHm3d
end
end
