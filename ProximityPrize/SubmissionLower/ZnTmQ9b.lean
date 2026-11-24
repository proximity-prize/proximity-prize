import ProximityPrize.SubmissionLower.ZtyYfOe
import ProximityPrize.SubmissionLower.ZpWrDCd
import ProximityPrize.SubmissionLower.ZH0Zvwe
import ProximityPrize.SubmissionLower.Zmk5EEe
import ProximityPrize.SubmissionLower.ZGDv7Ub
import ProximityPrize.SubmissionLower.ZkEhKoc
import ProximityPrize.SubmissionLower.ZX8w26c
import ProximityPrize.SubmissionLower.ZfbLZnc
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.IsSeparable → zw7, DFunLike.congr_fun → zmU, Field → zrb, Function.Injective → zq4, Ideal.Quotient.eq_zero_iff_mem → z1Q, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, IsFractionRing.injective → zxb, IsScalarTower.algebraMap_apply → zG3, MvPolynomial.X → z9v, MvPolynomial.ringHom_ext → zXT, Polynomial.X → z7y, PowerSeries → zpm, PowerSeries.C → zMG, PowerSeries.coeff → z2o, PowerSeries.coeff_X → zhV, PowerSeries.coeff_zero_eq_constantCoeff_apply → zW1, PowerSeries.constantCoeff → zbO, PowerSeries.isUnit_iff_constantCoeff → zRV, RingHom.comp_apply → zQb, RingHom.comp_assoc → zxS, RingHom.ker → zdq
section
section
set_option backward.isDefEq.respectTransparency false
namespace qJm9rWb
noncomputable section
open Polynomial TrivSqZeroExt
open qLXroAb (tu dx evalXY)
open private aug aug_eval dualLift aug_lift lift_on from ProximityPrize.SubmissionLower.ZR3mCBd
open private aNu from ProximityPrize.SubmissionLower.ZH0Zvwe
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
theorem pencil_derivation {E M:Type} [zrb E] [zrb M]
    [zZE E M] [zZE (tu E) M] [IsScalarTower E (tu E) M]
    [zw7 (tu E) M] :
    ∃ D:Derivation ℤ M M,(∀ a :E,D (algebraMap E M a)=0) ∧
      D (algebraMap (tu E) M (algebraMap E[X] (tu E) z7y))=1 := by
  let j:=algebraMap (tu E) M
  let u:=j (algebraMap E[X] (tu E) z7y)
  let k :=(inlHom M M).comp (algebraMap E M)
  let f :=eval₂RingHom k (inl u+inr 1)
  have hC (a :E) :j (algebraMap E[X] (tu E) (C a))=algebraMap E M a := by
    rw [Polynomial.C_eq_algebraMap,← zG3 E E[X] (tu E),
      ← zG3 E (tu E) M]
  have hf : (aug M).comp f=j.comp (algebraMap E[X] (tu E)) := by
    dsimp only [f]
    rw [aug_eval]
    apply Polynomial.ringHom_ext
    · intro a
      simpa [aug,k] using (hC a).symm
    · simp [u]
  let b:=dualLift f j hf
  let:zZE (tu E) (TrivSqZeroExt M M) :=b.toAlgebra
  let π:TrivSqZeroExt M M →ₐ[tu E] M :=
    { aug M with commutes' := fun a=>RingHom.congr_fun (aug_lift f j hf) a }
  have hs :Function.Surjective π:= fun a=>⟨inl a,rfl⟩
  have hk :IsNilpotent (zdq π.toRingHom) := by
    refine ⟨2,?_⟩
    let I:=zdq π.toRingHom
    change I ^(2 :ℕ) = ⊥
    have hm:I* I ≤ ⊥ := by
      apply Ideal.mul_le.mpr
      intro a ha b hb
      change a.fst=0 at ha
      change b.fst=0 at hb
      rw [Ideal.mem_bot]
      ext <;> simp [ha,hb]
    exact (pow_two I).trans (le_antisymm hm bot_le)
  let:Algebra.FormallyEtale (tu E) M:=Algebra.FormallyEtale.of_isSeparable _ _
  let g:=Algebra.FormallySmooth.liftOfSurjective (AlgHom.id (tu E) M) π hs hk
  have hg (a :M) : (g a).fst=a :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id (tu E) M) π hs hk a
  let d:M →+ M :=
    { toFun:= fun a=>(g a).snd
      map_zero' := by simp
      map_add' := fun a b=> by simp }
  let D:Derivation ℤ M M :=
    { toFun:=d
      map_add' := d.map_add
      map_smul' := fun n a=>d.map_zsmul n a
      map_one_eq_zero' := by change (g 1).snd=0; simp
      leibniz' := fun a b=> by
        change (g (a*b)).snd=a•(g b).snd+b•(g a).snd
        simp [hg,mul_comm] }
  have hb (a :E[X]) :D (j (algebraMap E[X] (tu E) a))=(f a).snd:= by
    have h:=congrArg snd (g.commutes (algebraMap E[X] (tu E) a))
    change _=(b (algebraMap E[X] (tu E) a)).snd at h
    rw [show b (algebraMap E[X] (tu E) a)=f a from lift_on f j hf a] at h
    exact h
  refine ⟨D,fun a => ?_,?_⟩
  · rw [← hC a,hb]
    simp [f,k]
  · rw [hb]
    simp [f]
theorem bXI {E :Type} [zrb E] (f :E[X][X]) (i:ℕ) :
  (dx f).coeff i=(f.coeff i).derivative :=
 sum_coeff derivative derivative_zero f i
theorem directional {E M:Type} [zrb E] [zrb M] [zZE E M]
   (D:Derivation ℤ M M) (h : ∀ a :E,D (algebraMap E M a)=0)
   (x y :M) (f :E[X][X]) :
   D (evalXY f x y)=evalXY (dx f) x y*D x+evalXY f.derivative x y*D y := by
 let j:=eval₂RingHom (algebraMap E M) x
 have hinner (p:E[X]) :D (j p)=j p.derivative*D x := by
   simpa [j,h] using
     (aNu D (algebraMap E M) x p 0 (fun i=> by simp [h]))
 have hc (i:ℕ) :D ((f.map j).coeff i)=((dx f).map j*C (D x)).coeff i:= by
   rw [coeff_mul_C,coeff_map,coeff_map,bXI]
   exact hinner _
 have hr :=aNu D (RingHom.id M) y (f.map j) ((dx f).map j*C (D x))
   (fun i=>hc i)
 rw [derivative_map] at hr
 simpa [evalXY,j,eval₂_map] using hr
open scoped Classical in
theorem charpoly_embeddings {B M Ω:Type} [zrb B] [zrb M] [zrb Ω]
   [zZE B M] [Module.Finite B M] [zw7 B M] [Infinite B]
   [zZE B Ω] [IsAlgClosed Ω] (q:M) :
   (Algebra.lmul B M q).charpoly.map (algebraMap B Ω) =
     ∏ σ:M →ₐ[B] Ω,(z7y - C (σ q)) := by
 apply Polynomial.eq_of_infinite_eval_eq
 refine (Set.infinite_range_of_injective (algebraMap B Ω).injective).mono ?_
 rintro _ ⟨t,rfl⟩
 change Polynomial.eval (algebraMap B Ω t) _ = _
 rw [Polynomial.eval_map_algebraMap,Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
   LinearMap.eval_charpoly,← (Algebra.lmul B M).commutes t,← map_sub,← Algebra.norm_apply,
   Algebra.norm_eq_prod_embeddings B Ω]
 simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
   map_sub,AlgHom.commutes]
end
end qJm9rWb
end
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace qU1uHGd
noncomputable section
open Polynomial
open P5 (p)
open qziIa4d (SeedSeries seedDerivative TameDerivative)
open qFD8jve (polarResultant)
open private product from ProximityPrize.SubmissionLower.ZXswmNd
open private common_resultant from ProximityPrize.SubmissionLower.ZATKiYa
abbrev PhysicalSeries :=LaurentSeries SeedSeries
abbrev Roots :=AlgebraicClosure PhysicalSeries
private def toRoots :zpm SeedSeries →+* Roots :=
 (algebraMap PhysicalSeries Roots).comp (HahnSeries.ofPowerSeries ℤ SeedSeries)
private def embed:SeedSeries[X] →+* Roots :=
 toRoots.comp coeToPowerSeries.ringHom
private theorem embed_inj:zq4 embed :=
 (algebraMap PhysicalSeries Roots).injective.comp
   (HahnSeries.ofPowerSeries_injective.comp (Polynomial.coe_injective SeedSeries))
private theorem valuation_of_polynomial (V:ValuationSubring Roots) (e :zpm SeedSeries →+* V)
  (he : ∀ s,((e s :V) :Roots)=toRoots s) [IsLocalHom e]
  (g:SeedSeries[X]) (hg:g≠0) :
  V.valuation (embed g)=V.valuation (embed (z7y:SeedSeries[X]))^g.natTrailingDegree := by
 obtain ⟨t,ht⟩:=X_pow_dvd_iff.mpr (fun _ hj=>coeff_eq_zero_of_lt_natTrailingDegree (p:=g) hj)
 have hz :t.coeff 0≠0:= by
  have h:=congrArg (fun f :SeedSeries[X]=>f.coeff g.natTrailingDegree) ht
  simp only [coeff_X_pow_mul',le_refl,ite_eq_left,Nat.sub_self] at h
  rw [← h]
  exact trailingCoeff_nonzero_iff_nonzero.mpr hg
 have hv :V.valuation (embed t)=1 := by
  change V.valuation (toRoots (t:zpm SeedSeries))=1
  rw [← he,← V.valuation_eq_one_iff,isUnit_map_iff e,
    zRV,Polynomial.constantCoeff_coe,isUnit_iff_ne_zero]
  exact hz
 conv_lhs=>rw [ht,map_mul,map_pow,map_mul,map_pow,hv,mul_one]
private theorem product_bound {M:Type*} [zrb M] (V:ValuationSubring M)
   (s :Multiset M) (a :M→M) (h : ∀ y∈s,V.valuation (a y)≤1) (i:ℕ) :
   V.valuation (((s.map fun y=>1+Polynomial.X*C (a y)).prod:M[X]).coeff i)≤1 := by
 induction s using Multiset.induction_on generalizing i with
 | empty=>by_cases hi:i=0 <;> simp [coeff_one,hi]
 | cons y s ih =>
   rw [Multiset.map_cons,Multiset.prod_cons,coeff_mul]
   apply V.valuation.map_sum_le
   intro j _
   rw [map_mul,← mul_one (1 :V.ValueGroup)]
   apply mul_le_mul'
   · have hy :=h y (Multiset.mem_cons_self y s)
     cases j.1 with
     | zero=>simp
     | succ k=>cases k <;> simp [coeff_one,hy]
   · exact ih (fun z hz=>h z (Multiset.mem_cons_of_mem hz)) j.2
theorem bEl (ht:TameDerivative) (F:SeedSeries[X][X]) (n:ℕ)
   (hd:0<F.natDegree) (hp:F.natDegree<p) (hl:F.leadingCoeff.coeff 0≠0)
   (hsep:polarResultant F≠0) (hn: (z7y:SeedSeries[X])^n∣polarResultant F) :
   C ((z7y:SeedSeries[X])^n)∣qW F (seedDerivative F) F.natDegree := by
 classical
 obtain ⟨V,hv,hel⟩:=IsLocalRing.exists_factor_valuationRing toRoots
 let e :=toRoots.codRestrict V.toSubring hv
 have :IsLocalHom e :=hel
 have he (s :zpm SeedSeries) : ((e s :V) :Roots)=toRoots s :=rfl
 have hx :V.valuation (embed (z7y:SeedSeries[X]))<1 := by
   change V.valuation (toRoots ((z7y:SeedSeries[X]) :zpm SeedSeries))<1
   rw [Polynomial.coe_X,← he,← V.valuation_lt_one_iff,IsLocalRing.mem_maximalIdeal]
   change ¬ IsUnit (e PowerSeries.X)
   rw [isUnit_map_iff e,zRV,PowerSeries.constantCoeff_X]
   exact not_isUnit_zero
 have hc (s :SeedSeries) (hs :s≠0) :V.valuation (embed (C s))=1 := by
   change V.valuation (toRoots ((C s :SeedSeries[X]) :zpm SeedSeries))=1
   rw [Polynomial.coe_C,← he,← V.valuation_eq_one_iff,isUnit_map_iff e,
     zRV,PowerSeries.constantCoeff_C]
   exact hs.isUnit
 let f :=F.map embed
 let D:=seedDerivative F
 let g:=D.map embed
 let d:=F.natDegree
 let R:=qW F D d
 have hdf :f.natDegree=d:=natDegree_map_eq_of_injective embed_inj _
 have hD:D.natDegree≤d:= by
   apply natDegree_le_iff_coeff_eq_zero.mpr
   intro i hi
   apply Polynomial.ext
   intro j
   rw [seedDerivative_coeff,coeff_eq_zero_of_natDegree_lt (p:=F) hi,coeff_zero,map_zero]
 have hf :f≠0:= fun h=>hd.ne' (hdf.symm.trans (by rw [h,natDegree_zero]))
 have hroot (y :Roots) (hy :y∈f.roots) :F.eval₂ embed y=0:= by
   simpa only [IsRoot,f,eval_map] using isRoot_of_mem_roots hy
 have hsimple (y :Roots) (hy :y∈f.roots) :F.derivative.eval₂ embed y≠0:= by
   intro hz
   have h:=common_resultant F F.derivative le_rfl (natDegree_derivative_le F) hd.ne'
     embed y (hroot y hy) hz
   exact hsep (embed_inj (h.trans (map_zero embed).symm))
 have hdv (y :Roots) (hy :y∈f.roots) :f.derivative.eval y≠0:= by
   simpa only [f,derivative_map,eval_map] using hsimple y hy
 have hprod:=product f f.derivative g d (IsAlgClosed.splits f)
   ((natDegree_derivative_le f).trans (by omega)) (natDegree_map_le.trans hD) hf hdv
 rw [hdf] at hprod
 change (qW f g d).coeff 0≠0 ∧
   qW f g d=C ((qW f g d).coeff 0) *
     (f.roots.map fun y=>1+Polynomial.X*C (g.eval y/f.derivative.eval y)).prod at hprod
 rw [← show R.map embed=qW f g d from mapped embed F D d] at hprod
 have hvQ (y :Roots) (hy :y∈f.roots) :
     V.valuation (g.eval y/f.derivative.eval y)≤1 := by
   have h:=ht V.valuation embed embed_inj hc hx F y hd hp hl (hroot y hy) (hsimple y hy)
   simpa only [g,D,f,derivative_map,eval_map,neg_div,Valuation.map_neg] using h
 have hR0:R.coeff 0≠0:= fun h=>hprod.1 (by rw [coeff_map,h,map_zero])
 have hdiv0: (z7y:SeedSeries[X])^n∣R.coeff 0:= by
   rw [constant_pencil F D d hd rfl]
   exact dvd_mul_of_dvd_right hn _
 have hx0:0<V.valuation (embed (z7y:SeedSeries[X])) :=
   V.valuation.pos_iff.mpr ((map_ne_zero_iff embed embed_inj).mpr X_ne_zero)
 apply (C_dvd_iff_dvd_coeff _ _).mpr
 intro i
 by_cases hi:R.coeff i=0
 · rw [hi]; exact dvd_zero _
 have h:=congrArg (fun P:Roots[X]=>P.coeff i) hprod.2
 rw [coeff_map,coeff_C_mul,coeff_map] at h
 have hle :V.valuation (embed (R.coeff i))≤V.valuation (embed (R.coeff 0)) := by
   rw [h,map_mul]
   exact mul_le_of_le_one_right' (product_bound V _ _ hvQ i)
 rw [valuation_of_polynomial V e he _ hi,valuation_of_polynomial V e he _ hR0] at hle
 have hl' := (pow_le_pow_iff_right_of_lt_one₀ hx0 hx).mp hle
 have hn' : n≤(R.coeff 0).natTrailingDegree := by
   by_contra! hz
   exact (trailingCoeff_nonzero_iff_nonzero.mpr hR0) ((X_pow_dvd_iff.mp hdiv0) _ hz)
 exact X_pow_dvd_iff.mpr (fun j hj =>
   coeff_eq_zero_of_lt_natTrailingDegree (hj.trans_le (hn'.trans hl')))
end
end qU1uHGd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qU1uHGd
noncomputable section
open Polynomial
open cu (L)
open qb0hmCe (cLN zD)
open q1kuFjb (mapTwice)
open qFD8jve (polarResultant)
open q2TwyLa (i5 integral lift diff)
open qziIa4d (SeedSeries seedDerivative)
open scoped WithZero
theorem proof :qziIa4d.c4 := by
 intro ht E _ _ a G
 dsimp only
 intro hd hp hl hs hb hg Q _ hr hsimple
 have hi:integral a G:= fun i j=> by
   simpa only [Valuation.comap_apply,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,
     Nat.cast_zero,WithZero.exp_zero] using hb i j
 let F:=lift a G hi
 let H :=diff F
 let f :=mapTwice incl F
 let d:=G.natDegree
 let n:=(polarResultant G).natTrailingDegree
 let R:=qW F H d
 let e :=mapRingHom incl
 let g:=mapRingHom a.toRingHom
 let e₀:i5[X] →+* L[X] :=mapRingHom zbO
 have hfm:f=mapTwice a.toRingHom G:=lift_embed a G hi
 have hdf :f.natDegree=d:= by rw [hfm,degree_mapTwice a.injective]
 have hF:F.natDegree=d:=(degree_mapTwice HahnSeries.ofPowerSeries_injective F).symm.trans hdf
 have hgInj:zq4 g:=Polynomial.map_injective _ a.injective
 have hlf :f.leadingCoeff.coeff 0≠0:= by
   rw [hfm]
   change (G.map g).leadingCoeff.coeff 0≠0
   rw [leadingCoeff_map_of_injective hgInj]
   change (G.leadingCoeff.map a.toRingHom).coeff 0≠0
   rw [coeff_map]
   exact (map_ne_zero a).mpr hl
 have hpol:polarResultant f=g (polarResultant G) := by
   rw [polarResultant,hdf,hfm]
   change (G.map g).resultant (G.map g).derivative d (d-1) =
     g (G.resultant G.derivative d (d-1))
   rw [derivative_map,resultant_map_map]
 have hpol0:polarResultant f≠0:= by
   rw [hpol]
   exact (map_ne_zero_iff g hgInj).mpr hs
 have hx : (z7y:SeedSeries[X])^n∣polarResultant f := by
   apply X_pow_dvd_iff.mpr
   intro j hj
   rw [hpol]
   change ((polarResultant G).map a.toRingHom).coeff j=0
   rw [coeff_map,coeff_eq_zero_of_lt_natTrailingDegree hj,map_zero]
 have hem:R.map e=qW f (seedDerivative f) f.natDegree := by
   rw [hdf,show R=qW F H d from rfl,mapped]
   exact congrArg (fun J=>qW f J d) (diff_embed F)
 have hdiv :=bEl ht f n (by simpa only [hdf] using hd) (by simpa only [hdf] using hp) hlf hpol0 hx
 rw [← hem] at hdiv
 have hdivR:C ((z7y:i5[X])^n)∣R:= by
   apply (C_dvd_iff_dvd_coeff _ _).mpr
   intro i
   apply X_pow_dvd_iff.mpr
   intro j hj
   have hz :=X_pow_dvd_iff.mp ((C_dvd_iff_dvd_coeff _ _).mp hdiv i) j hj
   rw [coeff_map,show e (R.coeff i)=(R.coeff i).map incl from rfl,coeff_map] at hz
   exact HahnSeries.ofPowerSeries_injective (hz.trans (map_zero incl).symm)
 obtain ⟨T,hT⟩:=hdivR
 have ht0:zbO ((T.coeff 0).coeff 0)≠0:= by
   have heq :=congrArg (fun J:i5[X][X]=>(J.coeff 0).coeff n) hT
   simp only [coeff_C_mul,coeff_X_pow_mul',le_refl,ite_eq_left,Nat.sub_self] at heq
   rw [← heq]
   exact guard_residue a G hi hd hl hg
 have hjet:=lift_jet a G hi
 have hT₀:qW (cLN a 0 G) (cLN a 1 G) d =
     C ((z7y:L[X])^n)*T.map e₀:= by
   have h:=congrArg (fun J:i5[X][X]=>J.map e₀) hT
   change (qW F H d).map e₀= _ at h
   rw [mapped,show F.map e₀=cLN a 0 G from hjet.1,
     show H.map e₀=cLN a 1 G from hjet.2,Polynomial.map_mul,map_C,map_pow,
     show e₀ (z7y:i5[X])=z7y from map_X _] at h
   exact h
 have hdeg₀: (cLN a 0 G).natDegree≤d:= by
   rw [← hjet.1,← hF]
   exact natDegree_map_le
 have hdeg₁ : (cLN a 1 G).natDegree≤d:= by
   rw [← hjet.2,← hF]
   exact natDegree_map_le.trans (q2TwyLa.diff_degree F)
 unfold zD
 exact regular hd.ne' hdeg₀ hdeg₁ hT₀ (by
   rw [coeff_map,show e₀ (T.coeff 0)=(T.coeff 0).map zbO from rfl,coeff_map]
   exact ht0) hr hsimple Q
end
end qU1uHGd
end
section
set_option autoImplicit true
namespace q8iJfvb
def c1 :Prop :=qziIa4d.c1
def c2 :Prop :=qziIa4d.c2
def c3:Prop :=qziIa4d.c3
def c4 :Prop :=qziIa4d.c4
theorem of_children (bY:c1) (transport:c2) (tame :c3) (local_test :c4) :
  qYdH9sc.c3 :=
 qziIa4d.of_children bY transport tame local_test
end q8iJfvb
end
section
set_option autoImplicit true
namespace qJnk13b
theorem proof :qYdH9sc.c5:=qGzrWfb.proof
end qJnk13b
end
end
section
set_option autoImplicit true
namespace P5_7_3_3_4_1_1
noncomputable section
open cu (L)
open Cu
open qL2osVa (Series SeriesField)
open MvPolynomial
open private arc_kernel from ProximityPrize.SubmissionLower.ZfbLZnc
abbrev toField (q:sQ) :sQ →+* oO q :=
  (algebraMap (abz q) (oO q)).comp (zVv _)
structure SeedArc (q:sQ) (z :Fin 2→L) (j:Fin 2) where
  embedding:oO q →+* SeriesField
  seed :Fin 2→Series
  compatible :embedding.comp (toField q) =
    (algebraMap Series SeriesField).comp (eval₂Hom zMG seed)
  residue : ∀ i,zbO (seed i)=z i
  free :seed j=zMG (z j)+PowerSeries.X
def shift (z :Fin 2→L) (i:Fin 2) :sQ:=z9v i - C (z i)
variable {q:sQ} {z :Fin 2→L} {j:Fin 2}
abbrev SeedArc.m8 (A:SeedArc q z j) :sQ →+* Series :=
  eval₂Hom zMG A.seed
theorem SeedArc.evaluate_residue (A:SeedArc q z j) (f :sQ) :
    zbO (A.m8 f)=eval z f := by
  have e :PowerSeries.constantCoeff.comp A.m8=eval z := by
    apply zXT
    · simp
    · simp [A.residue]
  exact zmU e f
theorem SeedArc.evaluate_shift (A:SeedArc q z j) :A.m8 (shift z j)=PowerSeries.X:= by
  simp [shift,A.free]
theorem SeedArc.apply_generic (A:SeedArc q z j) (f :sQ) :
    A.embedding (toField q f)=algebraMap Series SeriesField (A.m8 f) :=
  zmU A.compatible f
private theorem extend_quotient {R F:Type*} [CommRing R] [zrb F]
    (I:Ideal R) [I.IsPrime] (e :R →+* F) (hk :zdq e=I) :
    ∃ w:FractionRing (R ⧸ I) →+* F,
      w.comp ((algebraMap (R ⧸ I) (FractionRing (R ⧸ I))).comp (zVv I))=e := by
  let b: (R ⧸ I) →+* F:=Ideal.Quotient.lift I e (fun f h=>RingHom.mem_ker.mp (hk.symm ▸ h))
  have hb:zq4 b:= by
    apply (injective_iff_map_eq_zero' b).mpr
    intro x
    obtain ⟨f,rfl⟩:=zld x
    change e f=0↔zVv I f=0
    rw [← RingHom.mem_ker,hk,z1Q]
  exact ⟨IsFractionRing.lift hb,RingHom.ext fun f =>
    IsFractionRing.lift_algebraMap hb (zVv I f)⟩
private theorem evaluate_laurent (a :Fin 2→Series) :
    (algebraMap Series (LaurentSeries L)).comp (eval₂Hom zMG a) =
      (aeval (fun l=>(a l:LaurentSeries L))).toRingHom:= by
  apply zXT
  · intro c
    simp only [zQb,eval₂Hom_C]
    change ((zMG c:Series) :LaurentSeries L)=(aeval (fun k=>(a k :LaurentSeries L))) (C c)
    rw [aeval_C,PowerSeries.coe_C,LaurentSeries.algebraMap_apply]
  · intro l
    simp only [zQb,eval₂Hom_X']
    change (a l:LaurentSeries L)=(aeval (fun k=>(a k :LaurentSeries L))) (z9v l)
    rw [aeval_X]
private def compareFields :LaurentSeries L ≃ₐ[Series] SeriesField :=
  IsLocalization.algEquiv (nonZeroDivisors Series) (LaurentSeries L) SeriesField
theorem seedArc [hq:Fact (Irreducible q)] {i:Fin 2} (hij:j≠i)
    (hz :eval z q=0) (hd:eval z (pderiv i q)≠0) :Nonempty (SeedArc q z j) := by
  obtain ⟨a,ha,hq0,hf⟩:=qz11UBb.formalLift q z i hz hd
  have hj:z2o 1 (a j)≠0:= by
    simp [hf j hij,zhV]
  let e :sQ →+* LaurentSeries L:=(aeval (fun k=>(a k :LaurentSeries L))).toRingHom
  have hk :zdq e=auG q:=arc_kernel hq.out a hq0 hj
  obtain ⟨w,hw⟩:=extend_quotient (auG q) e hk
  let k :=compareFields.toAlgHom.toRingHom
  have hk' : k.comp (algebraMap Series (LaurentSeries L))=algebraMap Series SeriesField :=
    RingHom.ext compareFields.commutes
  refine ⟨⟨k.comp w,a,?_,ha,hf j hij⟩⟩
  change (k.comp w).comp (toField q)=(algebraMap Series SeriesField).comp _
  rw [zxS,show w.comp (toField q)=e from hw,
    show e= _ from (evaluate_laurent a).symm,← zxS,hk']
end
end P5_7_3_3_4_1_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_1
noncomputable section
open cu (L)
open Cu MvPolynomial
open qL2osVa (Series SeriesField)
private theorem gI (z :Fin 2→L) (i:Fin 2) (a b:Fin 2→sQ)
    (hab : ∀ k,k≠i→a k=b k) (ha : ∀ k,eval z (a k)=z k)
    (hb : ∀ k,eval z (b k)=z k) (f :sQ) :
    ∃ d,eval₂Hom C a f-eval₂Hom C b f=(a i - b i)*d ∧
      eval z d=eval z (pderiv i f) := by
  let u:=eval₂Hom C a
  let v :=eval₂Hom C b
  have hv : (eval z).comp v=eval z := by
    apply zXT
    · simp [v]
    · simp [v,hb]
  change ∃ d,u f - v f= _∧_
  induction f using MvPolynomial.induction_on with
  | C c=>exact ⟨0,by simp [u,v],by simp⟩
  | add f g hf hg =>
    obtain ⟨d,hd,hd'⟩:=hf
    obtain ⟨e,he,he'⟩:=hg
    refine ⟨d+e,?_,by simp [hd',he']⟩
    simp only [map_add]
    rw [show u f+u g-(v f+v g)=(u f-v f)+(u g-v g) by ring,hd,he,mul_add]
  | mul_X f k hf =>
    obtain ⟨d,hd,hd'⟩:=hf
    have he (k :Fin 2) :u (z9v k)=a k :=eval₂Hom_X' _ _ _
    have he' (k :Fin 2) :v (z9v k)=b k :=eval₂Hom_X' _ _ _
    have hvf :eval z (v f)=eval z f :=zmU hv f
    by_cases hk :k=i
    · subst k
      refine ⟨d*a i+v f,?_,by simp [hd',ha,hvf,add_comm,mul_comm]⟩
      simp only [map_mul,he,he']
      calc
        _=(u f - v f)*a i+(a i-b i)*v f := by ring
        _ = _:= by rw [hd]; ring
    · refine ⟨d*a k,?_,by simp [pderiv_X_of_ne hk,hd',ha,mul_comm]⟩
      simp only [map_mul,he,he',← hab k hk,← sub_mul,hd,mul_assoc]
private theorem two_differences (z :Fin 2→L) (i j:Fin 2) (hij:j≠i)
    (f :sQ) :
    ∃ d b,f=C (eval z f)+shift z i*d+shift z j*b ∧
      eval z d=eval z (pderiv i f) := by
  let a :Fin 2→sQ:= fun k=>if k=i then C (z k) else z9v k
  have ha (k :Fin 2) :eval z (a k)=z k := by
    by_cases hk :k=i <;> simp [a,hk]
  obtain ⟨d,hd,hd'⟩:=gI z i MvPolynomial.X a (fun k hk=> by simp [a,hk])
    (fun k=>eval_X k) ha f
  have hrev (k :Fin 2) (hk :k≠j) :k=i:= by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  obtain ⟨b,hb,_⟩:=gI z j a (C ∘ z)
    (fun k hk=> by simp [a,hrev k hk]) ha (fun k=>eval_C (z k)) f
  have h1 :eval₂Hom C z9v=RingHom.id sQ:= by
    apply zXT <;> simp
  have h2 :eval₂Hom C (C ∘ z)=(C:L →+* sQ).comp (eval z) := by
    apply zXT <;> simp
  rw [h1,RingHom.id_apply,show z9v i-a i=shift z i by simp [a,shift]] at hd
  rw [h2,zQb,show a j-(C ∘ z) j=shift z j by simp [a,hij,shift]] at hb
  exact ⟨d,b,by linear_combination hd+hb,hd'⟩
private theorem division_identity {R F:Type*} [CommRing R] [CommRing F] (e :R →+* F)
    {q f a d τ b v w:R} (hq0:e q=0) (hq:q=a*d+τ*b) (hf :f=a*v+τ*w) :
    e f*e d=e τ*e (w*d-b*v) := by
  rw [hq,map_add,map_mul,map_mul] at hq0
  rw [hf,map_add,map_sub,map_mul,map_mul,map_mul,map_mul]
  linear_combination e v*hq0
variable {q:sQ} {z :Fin 2→L} {i j:Fin 2}
local notation "G" => toField q
local notation "E" => eval z
local notation "t" => shift z j
private theorem quotient_step (hij:j≠i) (hz :E q=0) (hd:E (pderiv i q)≠0) :
    ∃ d,E d≠0 ∧ ∀ f,E f=0 → ∃ b,G f*G d=G t*G b:= by
  have hq:G q=0:= by
    change algebraMap (abz q) (oO q)
      (zVv (auG q) q)=0
    rw [(z1Q).mpr (Ideal.mem_span_singleton_self q),map_zero]
  obtain ⟨d,b,h,he⟩:=two_differences z i j hij q
  refine ⟨d,he ▸ hd,fun f hf => ?_⟩
  obtain ⟨v,w,hg,_⟩:=two_differences z i j hij f
  rw [hz,map_zero,zero_add] at h
  rw [hf,map_zero,zero_add] at hg
  exact ⟨w*d-b*v,division_identity G hq h hg⟩
private theorem factor (A:SeedArc q z j)
    (d:sQ) (hd:E d≠0) (step : ∀ f,E f=0 → ∃ b,G f*G d=G t*G b)
    (n:ℕ) (f :sQ) (hf : (A.m8 f).order=n) :
    ∃ u v,E u≠0∧E v≠0∧G f*G v=G t^n*G u:= by
  induction n generalizing f with
  | zero =>
    have hn:A.m8 f≠0:= by intro e; rw [e,PowerSeries.order_zero] at hf; simp at hf
    have h0:=PowerSeries.coeff_order hn
    rw [hf] at h0
    change z2o 0 (A.m8 f)≠0 at h0
    rw [zW1,A.evaluate_residue] at h0
    exact ⟨f,1,h0,by simp,by simp⟩
  | succ n ih =>
    have h0:=PowerSeries.coeff_of_lt_order 0 (φ:=A.m8 f) (by rw [hf]; simp)
    rw [zW1,A.evaluate_residue] at h0
    obtain ⟨b,hb⟩:=step f h0
    have he :A.m8 f*A.m8 d=PowerSeries.X*A.m8 b:= by
      apply zxb Series SeriesField
      have h:=congrArg A.embedding hb
      simp only [map_mul,A.apply_generic,A.evaluate_shift] at h
      simpa only [map_mul] using h
    have hdo: (A.m8 d).order=0:=PowerSeries.order_zero_of_isUnit
      (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr (by rwa [A.evaluate_residue])))
    have hfn :A.m8 f≠0:= by
      intro e
      rw [e,PowerSeries.order_zero] at hf
      exact ENat.natCast_ne_top (n+1) hf.symm
    have hdn:A.m8 d≠0:= fun e=>hd (by rw [← A.evaluate_residue,e,map_zero])
    have hbn:A.m8 b≠0:= fun e=>(mul_ne_zero hfn hdn) (by rw [he,e,mul_zero])
    have hbo: (A.m8 b).order=n:= by
      have hc:=congrArg PowerSeries.order he
      rw [PowerSeries.order_mul,PowerSeries.order_mul,hf,hdo,add_zero,
        PowerSeries.order_X,← PowerSeries.coe_toNat_order hbn] at hc
      have h:n+1=1+(A.m8 b).order.toNat := by exact_mod_cast hc
      rw [← PowerSeries.coe_toNat_order hbn,show (A.m8 b).order.toNat=n by omega]
    obtain ⟨u,v,hu,hv,eq⟩:=ih b hbo
    refine ⟨u,d*v,hu,by simpa using mul_ne_zero hd hv,?_⟩
    calc
      _=(G f*G d)*G v := by rw [map_mul,mul_assoc]
      _=G t*(G b*G v) := by rw [hb,mul_assoc]
      _ = _:= by rw [eq,pow_succ']; ring
theorem regular_or_pole [Fact (Irreducible q)] (A:SeedArc q z j) (hij:j≠i)
    (hz :E q=0) (hd:E (pderiv i q)≠0) (c:oO q) :
    (∃ f d,E d≠0∧G d*c=G f)∨(∃ f d,E d=0∧E f≠0∧G d*c=G f) := by
  by_cases hc:c=0
  · exact Or.inl ⟨0,1,by simp,by simp [hc]⟩
  obtain ⟨x,y,hy,hxy⟩:=IsFractionRing.div_surjective (abz q) c
  obtain ⟨f,rfl⟩:=zld x
  obtain ⟨r,rfl⟩:=zld y
  change G f/G r=c at hxy
  have hr :G r≠0:=IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (R:=abz q) hy
  have hf :G f≠0:= fun h=>hc (by simpa [h] using hxy.symm)
  have hfr :G r*c=G f := by rw [← hxy,mul_div_cancel₀ _ hr]
  have hEval (s :sQ) (hs :G s≠0) :A.m8 s≠0:= by
    intro h
    exact hs (A.embedding.injective (by rw [A.apply_generic,h,map_zero,map_zero]))
  have ht:G t≠0:= by
    intro h
    have he :=A.apply_generic t
    rw [h,map_zero,A.evaluate_shift] at he
    exact PowerSeries.X_ne_zero (zxb Series SeriesField (he.symm.trans (map_zero _).symm))
  obtain ⟨d,hd',hstep⟩:=quotient_step hij hz hd
  obtain ⟨u,v,hu,hv,eqf⟩:=factor A d hd' hstep _ f (PowerSeries.coe_toNat_order (hEval f hf)).symm
  obtain ⟨a,b,ha,hb,eqr⟩:=factor A d hd' hstep _ r (PowerSeries.coe_toNat_order (hEval r hr)).symm
  let n:=(A.m8 f).order.toNat
  let m:=(A.m8 r).order.toNat
  have afu:G t^m*(G (a*v)*c)=G t^n*G (u*b) := by
    simp only [map_mul]
    calc
      _=(G t^m*G a)*(G v*c) := by ring
      _=(G r*G b)*(G v*c) := by rw [eqr]
      _=(G r*c)*G v*G b:= by ring
      _=(G t^n*G u)*G b:= by rw [hfr,eqf]
      _ = _:= by ring
  have he :E t=0:= by simp [shift]
  by_cases h:m≤n
  · refine Or.inl ⟨t^(n-m)*(u*b),a*v,by simpa using mul_ne_zero ha hv,?_⟩
    apply mul_left_cancel₀ (pow_ne_zero m ht)
    calc
      _=G t^n*G (u*b) :=afu
      _ = _:= by
        rw [map_mul (toField q) (t^(n-m)),map_pow,← mul_assoc,← pow_add,Nat.add_sub_of_le h]
  · have h' : n≤ m:= by omega
    refine Or.inr ⟨u*b,t^(m-n)*(a*v),by simp [he,show m-n≠0 by omega],
      by simpa using mul_ne_zero hu hb,?_⟩
    apply mul_left_cancel₀ (pow_ne_zero n ht)
    calc
      _=G t^m*(G (a*v)*c) := by
        rw [map_mul (toField q) (t^(m-n)),map_pow,← mul_assoc (G t^n),
          ← mul_assoc (G t^n),← pow_add,Nat.add_sub_of_le h']
        ring
      _ = _:=afu
end
end P5_7_3_3_4_1_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_1
noncomputable section
open P5 (K)
open cu (L FX jz)
open Cu MvPolynomial
open quN7Z4a (Z7 Smooth)
open qL2osVa (MarkedSheet Series SeriesField)
open private b1t from ProximityPrize.SubmissionLower.ZgdIx1d
private theorem map_seed_pair (z :K) (n:ℕ) (k :Fin 2) :
    (![jz z,(jz z)^n] :Fin 2→FX) k =
      algebraMap L FX ((![algebraMap K L z,(algebraMap K L z)^n] :Fin 2→L) k) := by
  fin_cases k
  · rfl
  · exact (map_pow (algebraMap L FX) (algebraMap K L z) n).symm
variable {q:sQ} [Fact (Irreducible q)] (C₀:MarkedSheet q) {γ:K}
private theorem marked_relation (hγ:γ∈C₀.T) (i:Fin C₀.sheet.n) (f d:sQ)
    (h:toField q d*C₀.sheet.bY.coordinate i=toField q f) :
    eval (Z7 (C₀.z γ)) d*C₀.sheet.parameter γ i=eval (Z7 (C₀.z γ)) f := by
  let a :=algebraMap L FX
  let lift:sQ →+* Gc C₀.sheet.n :=
    (rename Sum.inl).toRingHom.comp (MvPolynomial.map a)
  let v :Gc C₀.sheet.n:=z9v (Sum.inr i)
  let pt:=aCn (C₀.z γ) (C₀.sheet.parameter γ)
  let e :=W8 C₀.sheet.bY
  have hg:e.comp lift=(Mu q).comp (toField q) := by
    apply zXT
    · intro c
      change e (lift (C c))=Mu q (zT q c)
      simpa [e,lift,W8] using b1t q c
    · intro k
      change e (lift (z9v k))=Mu q (Wt q k)
      simp [e,lift,W8]
  have hs (k :Fin 2) :pt (Sum.inl k)=a (Z7 (C₀.z γ) k) :=
    map_seed_pair (C₀.z γ) K1.p k
  have hm: (eval pt).comp lift=a.comp (eval (Z7 (C₀.z γ))) := by
    apply zXT
    · intro c
      simp [lift]
    · intro k
      simpa [lift] using hs k
  have hg' (b:sQ) :e (lift b)=Mu q (toField q b) :=
    zmU hg b
  have hm' (b:sQ) :eval pt (lift b)=a (eval (Z7 (C₀.z γ)) b) :=
    zmU hm b
  have hv :e v=Mu q (C₀.sheet.bY.coordinate i) := by simp [e,v,W8]
  have hv' : eval pt v=a (C₀.sheet.parameter γ i) := by simp [v,pt,aCn,a]
  have hP:lift d*v-lift f∈EF C₀.sheet.bY:= by
    apply RingHom.mem_ker.mpr
    change e (lift d*v-lift f)=0
    rw [map_sub,map_mul,hv,hg' d,hg' f,← map_mul,h,sub_self]
  have hM:=C₀.sheet.onBase γ hγ _ hP
  change aeval pt (lift d*v-lift f)=0 at hM
  rw [aeval_eq_eval] at hM
  rw [map_sub,map_mul,hv',hm' d,hm' f,← map_mul,sub_eq_zero] at hM
  exact a.injective hM
private theorem lift_coordinate (hγ:γ∈C₀.T) {j i:Fin 2}
    (A:SeedArc q (Z7 (C₀.z γ)) j) (hij:j≠i)
    (hd:eval (Z7 (C₀.z γ)) (pderiv i q)≠0) (k :Fin C₀.sheet.n) :
    ∃ F:Series,A.embedding (C₀.sheet.bY.coordinate k)=algebraMap Series SeriesField F ∧
      zbO F=C₀.sheet.parameter γ k := by
  let z :=Z7 (C₀.z γ)
  let c:=C₀.sheet.bY.coordinate k
  rcases regular_or_pole A hij (C₀.sheet.onSeed γ hγ) hd c with ⟨f,d,hn,he⟩ | ⟨f,d,hz,hn,he⟩
  · have hm:=marked_relation C₀ hγ k f d he
    have hu:IsUnit (A.m8 d) :=PowerSeries.isUnit_iff_constantCoeff.mpr
      (isUnit_iff_ne_zero.mpr (by rwa [A.evaluate_residue]))
    obtain ⟨u,hu⟩:=hu
    let F:Series :=A.m8 f*(↑u⁻¹:Series)
    have hF:A.m8 d*F=A.m8 f := by
      change A.m8 d*(A.m8 f*(↑u⁻¹:Series))=A.m8 f
      rw [← hu,mul_left_comm (↑u:Series),Units.mul_inv,mul_one]
    refine ⟨F,?_,?_⟩
    · have hi:=zxb Series SeriesField
      apply mul_left_cancel₀ (map_ne_zero_iff _ hi |>.mpr (hu ▸ u.ne_zero))
      rw [← map_mul,hF,← A.apply_generic,← A.apply_generic,← map_mul,he]
    · apply mul_left_cancel₀ hn
      have h:=congrArg (zbO (R:=L)) hF
      rw [map_mul,A.evaluate_residue,A.evaluate_residue] at h
      exact h.trans hm.symm
  · exact (hn (by simpa only [hz,zero_mul] using (marked_relation C₀ hγ k f d he).symm)).elim
theorem proof :qL2osVa.c1 := by
  classical
  intro q hq C γ hγ
  have hm:γ∈C.T∧Smooth q (Z7 (C.z γ)) :=Finset.mem_filter.mp hγ
  obtain ⟨i,hi⟩:=hm.2
  let j:Fin 2 :=if i=0 then 1 else 0
  have hij:j≠i:= by fin_cases i <;> decide
  obtain ⟨A⟩:=seedArc hij (C.sheet.onSeed γ hm.1) hi
  choose parameter he hv using lift_coordinate C hm.1 A hij hi
  refine ⟨⟨A.embedding,A.seed,parameter,?_,?_,he,A.residue,hv,⟨j,?_⟩⟩⟩
  · intro c
    change A.embedding (toField q (MvPolynomial.C c))= _
    rw [A.apply_generic,eval₂Hom_C]
  · intro k
    change A.embedding (toField q (z9v k))= _
    rw [A.apply_generic,eval₂Hom_X']
  · rw [A.free]
    simp [zhV]
end
end P5_7_3_3_4_1_1
end
