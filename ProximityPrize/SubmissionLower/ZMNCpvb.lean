import ProximityPrize.SubmissionLower.ZxrVYla
import ProximityPrize.SubmissionLower.ZOAcvWb
import ProximityPrize.SubmissionLower.ZkL5N7c
set_option Elab.async false
open _root_ renaming AlgHom.id → zhD, Algebra → zZE, Algebra.TensorProduct.map → zv2, Algebra.TensorProduct.map_tmul → zH0, Algebra.ofId → zNX, Algebra.smul_def → zd5, CommRing → za6, Field → zrb, Finset.sum_congr → zUo, Function.Injective → zq4, Ideal.Quotient.mk → zVv, IsFractionRing.injective → zxb, LinearIndependent → z14, LinearIndependent.of_comp → zCu, LinearMap.mulLeft → zzN, Module.Finite → zAa, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.eval₂ → zSZ, MvPolynomial.eval₂Hom_X' → zrD, MvPolynomial.rename → zHw, Polynomial.map_map → zoi, TensorProduct.inductionOn → z2P
set_option maxHeartbeats 450000
section
set_option backward.isDefEq.respectTransparency false
namespace qWY4iub
noncomputable section
open Polynomial
open P5 (K)
open cu (L j9)
open gT (kM)

open Cu
open E7 (CurvePlace Tq Gb)
open agN (b27 a6F)
open quN7Z4a (Sheet physicalWeight)
open qBajpRb (CurveRing cls incl yq atMark_cls equation equation_generic equation_mark)
open qX9S3Pd (gRK principal seed_bounds)
open qBd5KZd (MarkedCurve Allowance mass avoids bounded roots sections small weight)
open private mark_place incl_constant from ProximityPrize.SubmissionLower.ZIAMiic
open private eval_bound from ProximityPrize.SubmissionLower.ZxrVYla
open scoped WithZero
attribute [local instance] gRK
private theorem regular_of_mark {E B:Type} [zrb E] [zZE L E]
  [za6 B] [zZE L B] (v :CurvePlace L E) (j:B →+* E) (φ:B →ₐ[L] L)
  (hj : ∀ c:L,j (algebraMap L B c)=algebraMap L E c)
  (h : ∀ q,φ q=0↔v.value (j q)<1) (q:B) :v.value (j q)≤1 := by
 let c:=φ q
 have hd:φ (q-algebraMap L B c)=0:= by simp [c]
 have hc:v.value (j (algebraMap L B c))≤1 := by
  rw [hj]
  by_cases hz :c=0
  · simp [hz]
  · exact (v.on_constants c hz).le
 rw [← sub_add_cancel q (algebraMap L B c),map_add]
 exact (v.value.map_add _ _).trans (max_le ((h _).mp hd).le hc)
private theorem order_one {E :Type} [zrb E] [zZE L E] (v :CurvePlace L E) {x :E}
   (h:v.value x<1) :small v (-(1 :ℤ)) x := by
 by_cases hx :x=0
 · simp [small,hx]
 have hv :=v.value.ne_zero_iff.mpr hx
 have hl:=(WithZero.log_lt_log hv one_ne_zero).mpr h
 rw [WithZero.log_one] at hl
 exact (WithZero.log_le_iff_le_exp hv).mp (by omega)
private theorem scaled_weight {E :Type} [zrb E] (D:ℕ) {u:E} (hu:u≠0)
  (f :E[X][X]) :weight D (C (C u)*f)=weight D f := by
 have hs : (C (C u)*f).support=f.support := by
  ext i
  simp [Polynomial.mem_support_iff,coeff_C_mul,hu]
 simp only [weight,hs,coeff_C_mul,natDegree_C_mul hu]
variable {Q:sQ} [Fact (Irreducible Q)] {J:Ideal kM}
 {e H :ℕ} {T:Finset K} {z :K→K} {s :K→K[X]}
theorem bY (F:Sheet Q J e H T z s) (hz :Set.InjOn z (T:Set K))
    (hH :Gb L (oO Q) F.bY.coordinate≤H) :
    ∃ (C:MarkedCurve T) (f :C.E[X][X]) (A:Allowance C.E),
      f.IsPrimitive∧Irreducible (f.map (algebraMap _ (FractionRing C.E[X]))) ∧
      f.natDegree=e∧(∀ D,weight D f=physicalWeight D F.root.equation) ∧
      mass A≤H∧avoids C A∧bounded A f∧roots C (sections C s) 1 f := by
  classical
  let B:=F.bY
  let E :=oO Q
  obtain ⟨⟨i,hi⟩,hc,_⟩:=seed_bounds Q
  let φ (t:T) :=yq B (z t) (F.parameter t) (F.onBase t t.property)
  choose v hv using fun t:T=>mark_place B hc hi (F.onBase t t.property)
  have hvi:zq4 v := by
    intro t u he
    let x :=cls B (z9v (Sum.inl (0:Fin 2)))
    let q:=x-algebraMap L (CurveRing B) (φ t x)
    have ht:φ t q=0:= by simp [q]
    have hu:φ u q=0:=(hv u q).mpr (he ▸ (hv t q).mp ht)
    have h:φ u x=φ t x :=sub_eq_zero.mp (by simpa [q] using hu)
    have hfirst (a :T) :φ a x=algebraMap K L (z a) := by
      rw [show φ a x= _ from atMark_cls B _,MvPolynomial.eval_X]
      rfl
    rw [hfirst,hfirst] at h
    exact Subtype.ext (hz t.property u.property ((algebraMap K L).injective h.symm))
  let C₀:MarkedCurve T:=⟨E,hc,⟨v,hvi⟩⟩
  let f :=C (C (B.scale :E))*F.root.equation
  let a (w:CurvePlace L E) :=Tq w.value B.coordinate
  let ha :a.HasFiniteSupport:=b27 (principal hc) B.coordinate
  let A:Allowance E :=Finsupp.ofSupportFinite a ha
  have hmass :mass A=Gb L E B.coordinate := by
    rw [mass,Finsupp.liftAddHom_apply]
    exact (finsum_eq_sum_of_support_subset a (by
      rw [Finsupp.ofSupportFinite_support,Set.Finite.coe_toFinset])).symm
  have hreg (t:T) (q:CurveRing B) : (v t).value (incl B q)≤1 :=
    regular_of_mark (v t) (incl B) (φ t) (incl_constant B) (hv t) q
  have hmap : (equation B).map (mapRingHom (incl B))=f :=equation_generic B
  have hu:IsUnit (C (B.scale :E)) :=B.scale.isUnit.map C
  refine ⟨C₀,f,A,?_,?_,?_,fun D =>scaled_weight D B.scale.ne_zero _,hmass ▸ hH,?_,?_,?_⟩
  · exact (isPrimitive_of_dvd isPrimitive_one (isUnit_iff_dvd_one.mp (hu.map C))).mul F.root.primitive
  · rw [show f=C (C (B.scale :E))*F.root.equation from rfl,Polynomial.map_mul,Polynomial.map_C]
    exact (irreducible_isUnit_mul (hu.map ((C:FractionRing E[X] →+* (FractionRing E[X])[X]).comp
      (algebraMap E[X] (FractionRing E[X]))))).mpr F.root.irreducible
  · exact (natDegree_C_mul (C_ne_zero.mpr B.scale.ne_zero)).trans F.root.degree
  · intro t
    change Tq (v t).value B.coordinate=0
    apply Finset.sup_eq_bot_iff _ _ |>.mpr
    intro j _
    apply (a6F _ _).mpr
    exact (show (v t).value (B.coordinate j)≤1 from by
      have h:=hreg t (cls B (z9v (Sum.inr j)))
      rw [qBajpRb.incl_cls,qBajpRb.ek,zrD] at h
      exact h)
  · intro i j w
    change w.value ((f.coeff i).coeff j)≤WithZero.exp (a w:ℤ)
    have hf :=congrArg (fun g:E[X][X]=>(g.coeff i).coeff j) B.generic_eq
    rw [← hf,coeff_map,coe_mapRingHom,coeff_map]
    change w.value (zSZ (algebraMap L E) B.coordinate _)≤_
    simpa only [a,Nat.one_mul] using
      eval_bound (E :=E) w B.coordinate ((B.equation.coeff i).coeff j) (B.degree.2 i j)
  · intro t j
    let S:=(j9 (s t)).map (algebraMap L (CurveRing B))
    let r :=(equation B).eval S
    have hφ:r.map (φ t).toRingHom=0:= by
      rw [show r.map (φ t).toRingHom =
        ((equation B).map (mapRingHom (φ t).toRingHom)).eval (S.map (φ t).toRingHom) from
        (eval_map_apply (mapRingHom (φ t).toRingHom) S).symm]
      rw [equation_mark B (F.onBase t t.property)]
      have hS:S.map (φ t).toRingHom=j9 (s t) := by
        rw [zoi,show (φ t).toRingHom.comp (algebraMap L (CurveRing B)) =
          RingHom.id L from RingHom.ext (φ t).commutes,Polynomial.map_id]
      rw [hS]
      exact F.identity t t.property
    have hr :r.map (incl B)=f.eval (sections C₀ s t) := by
      rw [show r.map (incl B)=((equation B).map (mapRingHom (incl B))).eval
        (S.map (incl B)) from (eval_map_apply (mapRingHom (incl B)) S).symm,hmap]
      congr 1
      rw [zoi,show (incl B).comp (algebraMap L (CurveRing B))=algebraMap L E
        from RingHom.ext (incl_constant B)]
      exact zoi _ _ _
    have hzero :φ t (r.coeff j)=0:= by
      change (φ t).toRingHom (r.coeff j)=0
      simpa only [coeff_map,coeff_zero] using congrArg (fun f :L[X]=>f.coeff j) hφ
    apply order_one (v t)
    rw [← hr,coeff_map]
    exact (hv t _).mp hzero
end
end qWY4iub
end
section
set_option backward.isDefEq.respectTransparency false
namespace qWY4iub
noncomputable section
open Polynomial
open cu (L FX)
open gT (kM)
open Cu
open akS (tu)
open E7 (CurveField CurvePlace Gb poleOrder)
open agN (O7 d4p
 gDD bGE)

open qX9S3Pd (gRK principal sectionValue IndependentPowers)
open qISdf9a (clear_abscissa_relation)
open private constant_base from ProximityPrize.SubmissionLower.ZJbAGBd
open private Ep from ProximityPrize.SubmissionLower.ZtyYfOe
open private b1t from ProximityPrize.SubmissionLower.ZgdIx1d
attribute [local instance] gRK
private theorem powers_independent {E ι:Type} [zrb E] [zZE L E] [Fintype ι]
    {x :E} (hx :Transcendental L x) {v :ι→E}
    (hv :z14 (IntermediateField.adjoin L {x}) v) (m:ℕ) :
    z14 L (fun i:Fin (m+1)×ι=>x^(i.1 :ℕ)*v i.2) := by
  classical
  let U:=IntermediateField.adjoin L {x}
  let x₀:U:=⟨x,IntermediateField.mem_adjoin_simple_self L x⟩
  apply Fintype.linearIndependent_iff.mpr
  intro b hb
  let c (j:ι) :L[X] := ∑ i:Fin (m+1),monomial (i:ℕ) (b (i,j))
  have he (j:ι) : (aeval x (c j) :E) = ∑ i:Fin (m+1),algebraMap L E (b (i,j))*x^(i:ℕ) := by
    simp [c,aeval_monomial]
  have hval (j:ι) : ((aeval x₀ (c j) :U) :E)=aeval x (c j) :=
    (aeval_algHom_apply U.val x₀ (c j)).symm
  have hz : (∑ j,(aeval x₀ (c j) :U)•v j)=0:= by
    calc
      _ = ∑ j,(aeval x (c j) :E)*v j:= by
        refine zUo rfl fun j _ => ?_
        change ((aeval x₀ (c j) :U) :E)*v j= _
        rw [hval]
      _=0:= by
        simp_rw [he,Finset.sum_mul]
        rw [Finset.sum_comm]
        simpa only [Fintype.sum_prod_type,zd5,mul_assoc] using hb
  have hz' (j:ι) :c j=0:= by
    apply (transcendental_iff_injective.mp hx)
    rw [map_zero,← hval,(Fintype.linearIndependent_iff.mp hv) _ hz j]
    rfl
  intro i
  obtain ⟨i,j⟩:=i
  have h:=congrArg (fun P:L[X]=>P.coeff (i:ℕ)) (hz' j)
  simpa [c,finsetSum_coeff,coeff_monomial,Fin.val_inj] using h
set_option backward.isDefEq.respectTransparency true in
theorem seed_graph {Q:sQ} [Fact (Irreducible Q)] {J:Ideal kM}
    {e n:ℕ} {R:wJ Q J e} (B:yI R n)
    (hF:CurveField L (oO Q)) :
    ∃ (a :Fin n→FX)
      (w:Fin (Gb L (oO Q) B.coordinate)→tu (EF B)),
      IndependentPowers (EF B) a w:= by
  classical
  let E :=oO Q
  let r :=Gb L E B.coordinate
  by_cases hr :r=0
  · rw [show Gb L E B.coordinate=0 from hr]
    exact ⟨0,Fin.elim0,fun _=>linearIndependent_empty_type⟩
  let hdiv :=principal hF
  obtain ⟨a,ha,_⟩:=d4p hdiv B.coordinate
  let x :=O7 a B.coordinate
  have hsum: (∑ᶠ v :CurvePlace L E,poleOrder v.value x)=r :=finsum_congr ha
  have hx :Transcendental L x :=gDD (hsum.symm ▸ Nat.pos_of_ne_zero hr)
  let U:=IntermediateField.adjoin L {x}
  let:zAa U E :=bGE hF hx
  have hd:r=Module.finrank U E :=hsum.symm.trans ((hdiv x).2.2.2 hx)
  let:Module.Free U E :=Module.Free.of_divisionRing U E
  let b:Module.Basis (Fin r) U E :=(Module.finBasis U E).reindex (finCongr hd.symm)
  obtain ⟨c,hc⟩:=IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (abz Q)) b
  choose d hd' using hc
  let h:=algebraMap (abz Q) E
  have hcn:h c≠0 :=
    (map_ne_zero_iff h (zxb (abz Q) E)).mpr
      (nonZeroDivisors.ne_zero c.property)
  have hd'' (j:Fin r) :h (d j)=h c*b j:= by
    simpa only [zd5] using hd' j
  have hLI:z14 U (h ∘ d) := by
    have hLI' := b.linearIndependent.map' (zzN U (h c))
      (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hcn))
    simpa only [LinearMap.mulLeft_apply,Function.comp_def,hd''] using hLI'
  choose q hq using fun i=>Ideal.Quotient.mk_surjective (d i)
  let w (i:Fin r) :tu (EF B) :=zVv (EF B)
    (MvPolynomial.map (algebraMap L FX) (zHw Sum.inl (q i)))
  let j:tu (EF B) →+* y7 Q:=RingHom.kerLift (W8 B)
  have hj (i:Fin r) :j (w i)=Mu Q (h (d i)) := by
    change ((W8 B).comp (MvPolynomial.map (algebraMap L FX)))
      (zHw Sum.inl (q i))= _
    rw [constant_base,RingHom.comp_apply]
    congr 1
    have he :=DFunLike.congr_fun (Ep B) (q i)
    change qBajpRb.ek B (zHw Sum.inl (q i)) =
      h (zVv (auG Q) (q i)) at he
    rw [he,hq]
  have hcX (a :FX) :j (algebraMap FX (tu (EF B)) a)=Mr Q a :=
    MvPolynomial.eval₂Hom_C _ _ _
  have hx' : j (sectionValue (EF B) (algebraMap L FX ∘ a))=Mu Q x := by
    dsimp only [x,O7]
    rw [sectionValue,map_sum j,map_sum (Mu Q)]
    refine zUo rfl fun i _ => ?_
    rw [zd5 (R:=FX) (A:=tu (EF B)),zd5 (R:=L) (A:=E),
      j.map_mul,(Mu Q).map_mul,
      hcX,Function.comp_apply,b1t,
      show j (zVv (EF B) (z9v (Sum.inr i))) =
        Mu Q (B.coordinate i) from zrD _ _ _]
    rfl
  refine ⟨algebraMap L FX ∘ a,w,fun m => ?_⟩
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have he :=congrArg j hc
  rw [map_sum j,j.map_zero] at he
  have hterm (i:Fin (m+1)×Fin r) :
      j (c i•(sectionValue (EF B) (algebraMap L FX ∘ a)^(i.1 :ℕ)*w i.2)) =
        Mr Q (c i)*Mu Q (x^(i.1 :ℕ)*h (d i.2)) := by
    rw [zd5 (R:=FX) (A:=tu (EF B)),j.map_mul,hcX,
      j.map_mul,j.map_pow,hx',hj,
      (Mu Q).map_mul,(Mu Q).map_pow]
  simp only [hterm] at he
  exact clear_abscissa_relation (zT Q) (RingHom.id E) Function.injective_id
    (fun _=>rfl) (fun i:Fin (m+1)×Fin r=>x^(i.1 :ℕ)*h (d i.2))
    (powers_independent hx hLI m) c he
end
end qWY4iub
end
section
set_option backward.isDefEq.respectTransparency false
namespace qWY4iub
noncomputable section
open cu (FX)
open Cu
open akS
open qX9S3Pd (IndependentPowers)
open scoped TensorProduct akS

private def specialize {F R B:Type} [zrb F] [za6 R] [za6 B]
  [zZE F R] [zZE F B] (ev :R →ₐ[F] F) :R ⊗[F] B →ₐ[F] B :=
 Algebra.TensorProduct.lift ((zNX F B).comp ev) (zhD F B)
  (fun _ _=>Commute.all _ _)
private theorem specialize_tmul {F R B:Type} [zrb F] [za6 R] [za6 B]
  [zZE F R] [zZE F B] (ev :R →ₐ[F] F) (u:R) (b:B) :
  specialize ev (u ⊗ₜ[F] b)=ev u•b :=
 calc
  _=algebraMap F B (ev u)*b:=Algebra.TensorProduct.lift_tmul
    ((zNX F B).comp ev) (zhD F B) (fun _ _=>Commute.all _ _) u b
  _ = _:=(zd5 _ _).symm
private def EG {F B R:Type} [zrb F] [za6 B] [za6 R]
   [zZE F B] [zZE F R] (l:B →ₗ[F] F) :R ⊗[F] B →ₗ[R] R :=
 ((zNX F R).toLinearMap.comp l).liftBaseChange R
private theorem specialize_independent {F R S B ι:Type} [zrb F] [za6 R] [zrb S]
    [za6 B] [zZE F R] [zZE F S] [zZE F B] [Fintype ι]
    (ev :R →ₐ[F] F) (f :R →ₐ[F] S) (hf :zq4 f)
    (p:ι→R ⊗[F] B) (h:z14 F (fun i=>specialize ev (p i))) :
    z14 S (fun i=>zv2 f (zhD F B) (p i)) := by
  classical
  let u:=Fintype.linearCombination F (fun i=>specialize ev (p i))
  have hu:LinearMap.ker u = ⊥ :=
    LinearMap.ker_eq_bot.mpr (linearIndependent_iff_injective_fintypeLinearCombination.mp h)
  let l (i:ι) :B →ₗ[F] F:=(LinearMap.proj i).comp u.leftInverse
  have hl (i j:ι) :l i (specialize ev (p j))=(1 :Matrix ι ι F) i j:= by
    have he :=congrFun (u.leftInverse_apply_of_inj hu (Pi.single j (1 :F))) i
    simpa [l,u,Fintype.linearCombination_apply_single,Pi.single_apply,Matrix.one_apply,eq_comm] using he
  let M:Matrix ι ι R:= fun i j=>EG (l i) (p j)
  let Mf :Matrix ι ι S:=M.map f
  have hmap {A:Type} [za6 A] [zZE F A] (g:R →ₐ[F] A) (i:ι) (x :R ⊗[F] B) :
      g (EG (l i) x) =
        EG (l i) (zv2 g (zhD F B) x) := by
    induction x using z2P with
    | tmul a b=>simp [EG,AlgHom.commutes]
    | add a b ha hb=>simp [ha,hb]
  have hev (i:ι) (x :R ⊗[F] B) :
      ev (EG (l i) x)=l i (specialize ev x) := by
    induction x using z2P with
    | tmul a b =>
      rw [specialize_tmul,map_smul,smul_eq_mul]
      change ev (a*algebraMap F R (l i b))=ev a*l i b
      rw [map_mul,ev.commutes,Algebra.algebraMap_self_apply]
    | add a b ha hb=>simp [ha,hb]
  have hm:ev.mapMatrix M=1 := by
    ext i j
    exact (hev i (p j)).trans (hl i j)
  have hd:M.det≠0:= by
    intro h0
    have he :=ev.map_det M
    rw [hm,Matrix.det_one,h0,map_zero] at he
    exact zero_ne_one he
  have hdf :Mf.det≠0:= by
    rw [show Mf.det=f M.det from (f.map_det M).symm]
    simpa only [map_zero] using hf.ne hd
  let ψ:S ⊗[F] B →ₗ[S] (ι→S) :=LinearMap.pi (fun i=>EG (l i))
  apply zCu ψ
  convert Matrix.linearIndependent_cols_of_det_ne_zero hdf using 1
  ext j i
  exact (hmap f i (p j)).symm
private theorem c48 {S B:Type} [zrb S] [za6 B] [zZE S B]
    (a :B) (W:Submodule S B) {w:B} (hw:w∈W) {i k :ℕ} (hi:i≤k) :
    a^i*w∈abb a W k := by
  induction k generalizing i with
  | zero=>simpa [Nat.eq_zero_of_le_zero hi,abb] using hw
  | succ k ih =>
    change _∈W ⊔ (abb a W k).map (zzN S a)
    cases i with
    | zero=>simpa only [pow_zero,one_mul] using
        (le_sup_left:W≤W ⊔ (abb a W k).map (zzN S a)) hw
    | succ i =>
      rw [pow_succ',mul_assoc]
      exact (le_sup_right: (abb a W k).map (zzN S a) ≤
        W ⊔ (abb a W k).map (zzN S a))
        ⟨_,ih (Nat.le_of_succ_le_succ hi),rfl⟩
private theorem generic_powers {F B:Type} [zrb F] [za6 B] [zZE F B]
    {n m r :ℕ} (x :Fin n→B) (a :Fin n→F) (w:Fin r→B)
    (h:z14 F (fun i:Fin (m+1)×Fin r =>
      (∑ j,a j•x j)^(i.1 :ℕ)*w i.2)) :
    z14 (FractionRing (z3y (Fin n) F))
      (fun i:Fin (m+1)×Fin r =>
        (∑ j,algebraMap (z3y (Fin n) F) (FractionRing (z3y (Fin n) F))
          (z9v j)•((1 :FractionRing (z3y (Fin n) F)) ⊗ₜ[F] x j)) ^
          (i.1 :ℕ)*((1 :FractionRing (z3y (Fin n) F)) ⊗ₜ[F] w i.2)) := by
  let R:=z3y (Fin n) F
  let S:=FractionRing R
  let f :R →ₐ[F] S:=IsScalarTower.toAlgHom F R S
  let ev :R →ₐ[F] F:=MvPolynomial.aeval a
  let g:R ⊗[F] B := ∑ i,z9v i ⊗ₜ[F] x i
  have hg:zv2 f (zhD F B) g =
      ∑ j,algebraMap R S (z9v j)•((1 :S) ⊗ₜ[F] x j) := by
    simp only [g,map_sum,zH0,AlgHom.id_apply]
    apply zUo rfl
    intro i _
    rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    rfl
  have he :specialize (B:=B) ev g = ∑ i,a i•x i:= by
    simp only [g,map_sum,specialize_tmul]
    apply zUo rfl
    intro i _
    rw [show ev (z9v i)=a i from MvPolynomial.aeval_X a i]
  let p (i:Fin (m+1)×Fin r) :=g^(i.1 :ℕ)*(1 ⊗ₜ[F] w i.2)
  have hp:z14 F (fun i=>specialize (B:=B) ev (p i)) := by
    simpa only [p,map_mul,map_pow,specialize_tmul,map_one,one_smul,he] using h
  have hfinj:zq4 f := by
    change zq4 (algebraMap R S)
    exact zxb R S
  have hq:=specialize_independent (F:=F) (R:=R) (S:=S) (B:=B) ev f hfinj p hp
  simpa only [p,map_mul,map_pow,hg,zH0,map_one,
    AlgHom.id_apply] using hq
theorem rank_bound {n r H :ℕ} (B:Ideal (Gc n)) (hB:B.IsPrime)
   (hH :a9K B H) (a :Fin n→FX) (w:Fin r→tu B)
   (hw:IndependentPowers B a w) :r≤H := by
 classical
 let S:=e7 n
 let U:=Submodule.span S (Set.range (ajy B ∘ w))
 have hU:zAa S U:=Module.Finite.span_of_finite S (Set.finite_range _)
 obtain ⟨d,hd⟩:=aR1.proof n H B hB hH U hU
 let:zAa S U:=hU
 have hli:z14 S (fun i:Fin (d+1)×Fin r =>
     aoe B^(i.1 :ℕ)*ajy B (w i.2)) := by
   exact generic_powers (F:=FX) (B:=tu B) (m:=d)
     (fun j=>zVv B (z9v (Sum.inr j))) a w (hw d)
 let W:=abb (F:=e7 n) (aoe B) U d
 have hm (j:Fin r) :ajy B (w j)∈U :=
   Submodule.subset_span (Set.mem_range_self j)
 let u (i:Fin (d+1)×Fin r) :W :=
   ⟨aoe B^(i.1 :ℕ)*ajy B (w i.2),
     c48 (S:=e7 n) (aoe B) U (hm i.2) (Nat.le_of_lt_succ i.1.isLt)⟩
 have hli' : z14 S u:=zCu W.subtype hli
 have hr :Fintype.card (Fin (d+1)×Fin r)≤d+d*H :=
   hli'.fintype_card_le_finrank.trans (hd d)
 rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin] at hr
 by_contra! hh
 have hbad:=Nat.mul_le_mul_left (d+1) (Nat.succ_le_of_lt hh)
 simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one] at hbad hr
 omega
end
end qWY4iub
end
section
set_option autoImplicit true
namespace qWY4iub
open cu (L)
open gT (kM)
open Cu
open E7 (CurveField Gb)
open qX9S3Pd (gRK seed_bounds)
attribute [local instance] gRK
theorem height_le {Q:sQ} [Fact (Irreducible Q)] {J:Ideal kM}
  {e n H :ℕ} {R:wJ Q J e} (B:yI R n)
  (hH :a9K (EF B) H) (hF:CurveField L (oO Q)) :
  Gb L (oO Q) B.coordinate≤H := by
 obtain ⟨a,w,hw⟩:=seed_graph B hF
 exact rank_bound _ (RingHom.ker_isPrime _) hH a w hw
theorem proof :qBd5KZd.c1 := by
 intro Q _ J T z s e H F hz
 have hc:=(seed_bounds Q).2.1
 obtain ⟨C,f,A,hp,hI,he,hw,hm,ha,hb,hr⟩ :=
  bY F hz (height_le F.bY F.height hc)
 exact ⟨C,f,A,hp,hI,he,hw _,hm,ha,hb,hr⟩
end qWY4iub
end
section
namespace qtxrZka
theorem proof :qa9Ovbd.c1 := by
 intro Q _ J T z s g H S hz
 have hc:=(qX9S3Pd.seed_bounds Q).2.1
 exact qWY4iub.bY S hz (qWY4iub.height_le S.bY S.height hc)
end qtxrZka
end
section
namespace qw8MfCe
noncomputable section
open Finset Polynomial
open cu (L)

open DQ (DT)
open Cu
open E7
open agN (b27)
open qZfVj1b (gRK)
open qb0hmCe (coeffHeight)
open private eval_bound from ProximityPrize.SubmissionLower.ZxrVYla
open scoped WithZero
attribute [local instance] gRK
private theorem pole_balance {E :Type} [zrb E] (v :Valuation E ℤᵐ⁰)
   {b:E} (hb:b≠0) (x :E) (M:ℕ) (h:v (b*x)≤WithZero.exp (M:ℤ))
   (hB:v b≤WithZero.exp (M:ℤ)) :poleOrder v x+poleOrder v b≤M+KB v b:= by
 have hvb:=v.ne_zero_iff.mpr hb
 have hlog:=(WithZero.log_le_iff_le_exp hvb).mpr hB
 by_cases hx :x=0
 · simp only [hx,poleOrder,map_zero,WithZero.log_zero,Int.toNat_zero,zero_add,KB]
   omega
 have hmul :=(WithZero.log_le_iff_le_exp (v.ne_zero_iff.mpr (mul_ne_zero hb hx))).mpr h
 rw [map_mul,WithZero.log_mul hvb (v.ne_zero_iff.mpr hx)] at hmul
 unfold poleOrder KB
 omega
private theorem height_le_of_scale {E σ τ:Type} [zrb E] [zZE L E]
   [Fintype σ] [Fintype τ] (hdiv :axV L E) (u:σ→E) (r :τ→E)
   {b:E} (hb:b≠0)
   (hB : ∀ v :CurvePlace L E,v.value b≤WithZero.exp (Tq v.value r :ℤ))
   (hu : ∀ (v :CurvePlace L E) i,v.value (b*u i)≤WithZero.exp (Tq v.value r :ℤ)) :
   Gb L E u≤Gb L E r := by
 let T (v :CurvePlace L E) :=Tq v.value u
 let M (v :CurvePlace L E) :=Tq v.value r
 let po (v :CurvePlace L E) :=poleOrder v.value b
 let zo (v :CurvePlace L E) :=KB v.value b
 have hlocal (v :CurvePlace L E) :T v+po v≤M v+zo v := by
   have hb' : po v≤M v := by
     have h:=(WithZero.log_le_iff_le_exp (v.value.ne_zero_iff.mpr hb)).mpr (hB v)
     simpa only [po,poleOrder,Int.toNat_natCast] using Int.toNat_le_toNat h
   have hT:T v≤M v+zo v - po v := by
     apply Finset.sup_le
     intro i _
     have h:=pole_balance v.value hb (u i) (M v) (hu v i) (hB v)
     change poleOrder v.value (u i)+po v≤M v+zo v at h
     omega
   omega
 obtain ⟨hpo,hzo,heq,_⟩:=hdiv b
 have hT:T.HasFiniteSupport:=b27 hdiv u
 have hM:M.HasFiniteSupport:=b27 hdiv r
 have hsum:=finsum_le_finsum (hT.add hpo) (hM.add hzo) hlocal
 change (∑ᶠ v,(T v+po v))≤(∑ᶠ v,(M v+zo v)) at hsum
 have he : (∑ᶠ v,po v)=(∑ᶠ v,zo v) :=heq
 rw [finsum_add_distrib hT (show po.HasFiniteSupport from hpo),
   finsum_add_distrib hM (show zo.HasFiniteSupport from hzo),← he] at hsum
 exact Nat.le_of_add_le_add_right hsum
theorem proof :qxblDlc.c1 := by
  intro Q _ J e n H R A hF hH
  let E :=oO Q
  let a :=R.equation.leadingCoeff.leadingCoeff
  let b:E :=(A.scale :E)*a
  let ev :DT n →+* E :=MvPolynomial.eval₂Hom (zT Q) A.coordinate
  have ha :a≠0:=leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr fun hz =>
    R.irreducible.ne_zero (by rw [hz,Polynomial.map_zero]))
  have hg (i j:ℕ) :ev ((A.equation.coeff i).coeff j) =
      (A.scale :E)*(R.equation.coeff i).coeff j:= by
    have h:=congrArg (fun f :E[X][X]=>(f.coeff i).coeff j) A.generic_eq
    simpa only [coeff_map,coe_mapRingHom,coeff_C_mul,ev] using h
  have hv (v :CurvePlace L E) (i j:ℕ) :
      v.value (ev ((A.equation.coeff i).coeff j))≤WithZero.exp (Tq v.value A.coordinate :ℤ) := by
    change v.value (zSZ (algebraMap L E) A.coordinate
      ((A.equation.coeff i).coeff j))≤_
    simpa only [one_mul] using eval_bound v A.coordinate _ (A.degree.2 i j)
  have hscaled (i j:ℕ) :
      b*(((qZfVj1b.normalize R.equation).coeff i).coeff j) =
        ev ((A.equation.coeff i).coeff j) := by
    rw [hg,qZfVj1b.normalize,coeff_C_mul,coeff_C_mul]
    change ((A.scale :E)*a)*(a⁻¹*(R.equation.coeff i).coeff j)= _
    rw [mul_assoc (A.scale :E),← mul_assoc a,mul_inv_cancel₀ ha,one_mul]
  have hb (v :CurvePlace L E) :v.value b≤WithZero.exp (Tq v.value A.coordinate :ℤ) := by
    simpa only [hg,coeff_natDegree,b,a] using
      hv v R.equation.natDegree R.equation.leadingCoeff.natDegree
  apply le_trans _ (qWY4iub.height_le A hH hF)
  unfold coeffHeight
  refine height_le_of_scale (qX9S3Pd.principal hF) _ A.coordinate
    (mul_ne_zero A.scale.ne_zero ha) hb (fun v i => ?_)
  rw [hscaled]
  exact hv v _ _
end
end qw8MfCe
end
