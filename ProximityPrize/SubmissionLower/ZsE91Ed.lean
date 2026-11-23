import ProximityPrize.SubmissionLower.Zqop1Ec
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, IsFractionRing.injective → zxb, IsFractionRing.lift → zIj, IsFractionRing.lift_algebraMap → zoc, IsFractionRing.ringEquivOfRingEquiv → zDt, IsFractionRing.ringEquivOfRingEquiv_algebraMap → zNB, Polynomial.X → z7y, Polynomial.ringHom_ext → z86, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs
set_option maxRecDepth 4000
section
set_option backward.isDefEq.respectTransparency false
namespace qrKC9pb
noncomputable section
open Polynomial Finset
open P5 (p)
open cu (L)
open qGnV2ac (Sections)
open scoped BigOperators Classical
open private budgets from ProximityPrize.SubmissionLower.ZATKiYa
def c2 :Prop :=
 ∀ J:Input,horizontalDegree J<p→NoHorizontalPole J
def c3:Prop :=
  ∀ (J:Input) (S:Sections J.F),NoHorizontalPole J →
    ∀ γ∈S.CF,∀ x∈(S.B γ).roots.toFinset,
      ∃ (r :Bool) (D:GraphPrime J r),
        Over J D (algebraMap P5.K L (S.seed γ)) x ∧
          (S.B γ).rootMultiplicity x≤polarOrder D
def c4 :Prop :=
  ∀ (J:Input) (ι:Type) [Fintype ι] (a x :ι→L) (r :ι→Bool)
    (D : ∀ i,GraphPrime J (r i)),
    zq4 (fun i=>(a i,x i))→(∀ i,Over J (D i) (a i) (x i)) →
      (∑ i,polarOrder (D i))≤polarBudget J
private theorem finite_budget (charge :c3) (degree :c4) (J:Input) (S:Sections J.F)
    (hor :NoHorizontalPole J) :finitePoles S≤polarBudget J:= by
  classical
  let U:=S.CF.sigma fun γ=>(S.B γ).roots.toFinset
  let a (i : ↥U) :=algebraMap P5.K L (S.seed i.val.1)
  let x (i : ↥U) :=i.val.2
  have ha :zq4 (fun i=>(a i,x i)) := by
    intro i j hh
    have hg:=(algebraMap P5.K L).injective (congrArg Prod.fst hh)
    have hi:=(Finset.mem_sigma.mp i.prop).1
    have hj:=(Finset.mem_sigma.mp j.prop).1
    exact Subtype.ext (Sigma.ext (S.injective hi hj hg) (heq_of_eq (congrArg Prod.snd hh)))
  have hc (i : ↥U) :
      ∃ (r :Bool) (D:GraphPrime J r),Over J D (a i) (x i) ∧
        (S.B i.val.1).rootMultiplicity (x i)≤polarOrder D:= by
    obtain ⟨hγ,hx⟩:=Finset.mem_sigma.mp i.prop
    exact charge J S hor _ hγ _ hx
  choose r D hD hle using hc
  calc
    finitePoles S = ∑ i : ↥U,(S.B i.val.1).rootMultiplicity (x i) := by
      change finitePoles S = ∑ i∈U.attach,(S.B i.val.1).rootMultiplicity i.val.2
      rw [Finset.sum_attach U (fun i=>(S.B i.1).rootMultiplicity i.2)]
      unfold U finitePoles
      rw [Finset.sum_sigma]
      refine sum_congr rfl fun γ _ => ?_
      rw [← IsAlgClosed.card_roots_eq_natDegree,← Multiset.toFinset_sum_count_eq]
      exact sum_congr rfl fun _ _=>Polynomial.count_roots _
    _ ≤ ∑ i,polarOrder (D i) :=sum_le_sum fun i _=>hle i
    _≤polarBudget J:=degree J _ a x r D ha hD
theorem of_children (h1 :q7kdBxd.c1) (h2 :c2) (h3:c3) (h4 :c4) :qGnV2ac.c2 := by
 intro F l h u s L₀ W H hw hW hf hchar S
 obtain ⟨hb,hm,hn⟩:=budgets l u s L₀ W H.two_le hw hW
 let J:Input :=⟨F,l,h,s,W-l*u-l*s,H,hb.symm ▸ hf⟩
 have hJ:horizontalDegree J<p:= by
  change (2*l-2)*(W-l*u-l*s)+l*(l-1)*s<p
  rwa [hm]
 obtain ⟨G,T,hl,hh,hs,hb',ht⟩:=h1 J S
 have hm' : horizontalDegree G=horizontalDegree J:= by simp only [horizontalDegree,hl,hs,hb']
 have hn' : polarBudget G=polarBudget J:= by simp only [polarBudget,hl,hh,hs,hb']
 have hB:=finite_budget h3 h4 G T (h2 G (hm'.symm ▸ hJ))
 rw [hn'] at hB
 exact ht.trans (hB.trans (Nat.mul_le_mul_right h hn))
end
end qrKC9pb
end
section
namespace qWIOgVd
noncomputable section
open Polynomial Finset
open cu (L FX)
open P5_7_7 (phys)
open qGnV2ac (Sections)
theorem phys_inj:zq4 phys :=zxb L[X] FX
theorem phys_ne {q:L[X]} (hq:q≠0) :phys q≠0 :=
 (map_ne_zero_iff _ phys_inj).mpr hq
theorem x_ne :x≠0:=phys_ne X_ne_zero
private def invEval :L[X] →+* FX :=
 eval₂RingHom (phys.comp C) x⁻¹
private theorem reflect_phys (q:L[X]) (n:ℕ) (hq:q.natDegree≤n) :
   phys (q.reflect n)=x^n*invEval q:= by
 let:Invertible x⁻¹:=invertibleOfNonzero (inv_ne_zero x_ne)
 have h:=eval₂_reflect_mul_pow (phys.comp C) x⁻¹ n q hq
 rw [invOf_eq_inv,inv_inv,← hom_eval₂,eval₂_C_X] at h
 calc
   _=x^n*(phys (q.reflect n)*(x⁻¹)^n) := by
     rw [mul_left_comm,← mul_pow,mul_inv_cancel₀ x_ne,one_pow,mul_one]
   _ = _:=congrArg (x^n * ·) h
private theorem invEval_inj:zq4 invEval :=
 (injective_iff_map_eq_zero _).mpr fun q h=> by
   simpa [h,map_eq_zero_iff _ phys_inj,reflect_eq_zero_iff] using
    reflect_phys q q.natDegree le_rfl
private def invHom:FX →+* FX:=zIj invEval_inj
private theorem invHom_phys (q:L[X]) :invHom (phys q)=invEval q :=
 zoc invEval_inj q
private theorem invHom_C (a :L) :invHom (phys (C a))=phys (C a) := by
 rw [invHom_phys]
 simp [invEval]
private theorem invHom_X:invHom x=x⁻¹:= by
 rw [show x=phys z7y from rfl,invHom_phys]
 simp [invEval]
private theorem invHom_invol:Function.Involutive invHom:= by
  have h:invHom.comp invHom=RingHom.id FX:= by
    apply IsFractionRing.ringHom_ext (A:=L[X])
    change ∀ q,((invHom.comp invHom).comp phys) q=((RingHom.id FX).comp phys) q
    apply zLs
    apply z86
    · intro a
      simp only [zQb,RingHom.id_apply,invHom_C]
    · simp only [zQb,RingHom.id_apply,show phys z7y=x from rfl,
        invHom_X,map_inv₀,inv_inv]
  exact zLs h
private def invertX:FX ≃+* FX :=
 RingEquiv.ofBijective invHom invHom_invol.bijective
def bY (a :L) :Chart a where
  changeX:=(zDt (K:=FX) (L:=FX)
    (taylorEquiv a).toRingEquiv).trans invertX
  constant:= fun c=> by
    change invHom (zDt (taylorEquiv a).toRingEquiv
      (algebraMap L[X] FX (C c)))=phys (C c)
    rw [zNB]
    change invHom (phys ((C c).taylor a))=phys (C c)
    rw [taylor_C,invHom_C]
  CJ:= fun q n hq=> by
    change phys (rev a n q)=x^n*invHom
      (zDt (taylorEquiv a).toRingEquiv
        (algebraMap L[X] FX q))
    rw [zNB,← show
      phys (q.taylor a)=algebraMap L[X] FX ((taylorEquiv a).toRingEquiv q) from rfl,invHom_phys]
    exact reflect_phys _ _ ((natDegree_taylor q a).trans_le hq)
theorem width_bound (s :ℕ) (P Q:L[X]) :
  P.natDegree≤width s P Q+s∧Q.natDegree≤width s P Q:= by
 unfold width
 exact ⟨by have :=le_max_right Q.natDegree (P.natDegree - s); omega,le_max_left _ _⟩
theorem fresh {F:P5_7_7.Dg} (S:Sections F) :
  ∃ a :L,∀ γ∈S.CF,(S.B γ).eval a≠0:= by
 classical
 obtain ⟨a,ha⟩:=Infinite.exists_notMem_finset
  (S.CF.biUnion fun γ=>(S.B γ).roots.toFinset)
 exact ⟨a,fun γ hγ hz=>ha (mem_biUnion.mpr ⟨γ,hγ,Multiset.mem_toFinset.mpr
  ((mem_roots (S.pole_denominator γ hγ)).mpr hz)⟩)⟩
end
end qWIOgVd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qU3xjYb
noncomputable section
open Polynomial q7kdBxd qrzQ9fc

open cu (L)
open scoped WithZero
private abbrev Coeff :=L[X][X]
private def coeffRoot (J:Input) :Coeff →+* EC J:=(a7W J).comp C
private theorem coeffRoot_inj (J:Input) :zq4 (coeffRoot J) :=
 (zxb (AdjoinRoot J.F) (EC J)).comp
   (AdjoinRoot.of.injective_of_degree_ne_zero (fun e=> by
     have hat :J.F.natDegree=0:= by simp [degree_eq_natDegree J.Ca.irreducible.ne_zero] at e; exact e
     have :=J.Ca.two_le
     rw [J.Ca.jU] at hat
     omega))
private theorem seed_eq (J:Input) :
   Wu J=(coeffRoot J).comp (mapRingHom (C:L →+* L[X])) := by
 apply z86
 · intro a
   simp [Wu,constantMap,coeffRoot,a7W]
 · simp [Wu,seed,coeffRoot]
private theorem seed_inj (J:Input) :zq4 (Wu J) := by
 rw [seed_eq]
 exact (coeffRoot_inj J).comp (map_injective _ C_injective)
scoped instance rootAlgebra (J:Input) :Algebra aQ (EC J) :=
 (zIj (K:=aQ) (seed_inj J)).toAlgebra
theorem root_seed (J:Input) (a :L[X]) :
  algebraMap aQ (EC J) (algebraMap L[X] aQ a)=Wu J a :=
 zoc (seed_inj J) a
abbrev PhysField (J:Input) :=IntermediateField.adjoin aQ ({amm J} : Set (EC J))
private def swapped:Coeff →+* aQ[X] :=
 (mapRingHom (algebraMap L[X] aQ)).comp Bivariate.swap.toRingHom
private def coeffIn (J:Input) :Coeff →+* PhysField J :=
 (eval₂RingHom (algebraMap aQ (PhysField J))
   ⟨amm J,IntermediateField.mem_adjoin_simple_self aQ _⟩).comp swapped
private theorem coeffIn_eq (J:Input) :
    (PhysField J).val.toRingHom.comp (coeffIn J)=coeffRoot J:= by
  let e :=(PhysField J).val.toRingHom.comp (coeffIn J)
  have he (a :Coeff) :e a=(swapped a).eval₂ (algebraMap aQ (EC J)) (amm J) :=
    hom_eval₂ _ _ (PhysField J).val.toRingHom _
  have hswap:e.comp Bivariate.swap.toRingHom=(coeffRoot J).comp Bivariate.swap.toRingHom:= by
    apply z86
    · intro a
      change e (Bivariate.swap (C a))=coeffRoot J (Bivariate.swap (C a))
      rw [he,show swapped (Bivariate.swap (C a))=C (algebraMap L[X] aQ a) by
        change (Bivariate.swap (Bivariate.swap (C a))).map _ = _
        rw [Bivariate.swap_swap_apply,map_C],eval₂_C,root_seed]
      rw [seed_eq,Bivariate.swap_C]
      rfl
    · change e (Bivariate.swap (z7y:Coeff))=coeffRoot J (Bivariate.swap (z7y:Coeff))
      rw [he,show swapped (Bivariate.swap (z7y:Coeff))=z7y by
        change (Bivariate.swap (Bivariate.swap (z7y:Coeff))).map _ = _
        rw [Bivariate.swap_swap_apply,map_X],eval₂_X,Bivariate.swap_Y]
      rfl
  exact RingHom.ext fun a=> by
    have ha :=zLs hswap (Bivariate.swap a)
    change e (Bivariate.swap (Bivariate.swap a))=coeffRoot J (Bivariate.swap (Bivariate.swap a)) at ha
    simpa only [Bivariate.swap_swap_apply] using ha
end
end qU3xjYb
end
section
set_option maxHeartbeats 600000
namespace qqi5QRb
noncomputable section
open Polynomial WithZero
open scoped Classical
open P5 (K)
open cu (L FX)
open P5_7_7 (phys)
open qGnV2ac (Sections)
open q7kdBxd
open IsDedekindDomain.HeightOneSpectrum (valuation_of_algebraMap)
variable {J:Input} {S:Sections J.F} {γ:K} {x :L} {r :Bool}
private def integerMap (T:MarkChart J S γ x r) :
  Chart J r →+* (pointVal x).valuationSubring :=
 T.map.toRingHom.codRestrict (pointVal x).valuationSubring.toSubring T.regular
private def markCenter (T:MarkChart J S γ x r) :Ideal (Chart J r) :=
 (IsLocalRing.maximalIdeal (pointVal x).valuationSubring).comap (integerMap T)
private instance (T:MarkChart J S γ x r) : (markCenter T).IsPrime := by
 unfold markCenter
 infer_instance
private theorem val_poly_lt (x :L) (f :L[X]) :
  pointVal x (phys f)<1↔f.IsRoot x := by
 change (pointPrime x).valuation FX (algebraMap L[X] FX f)<1↔f.IsRoot x
 rw [(pointPrime x).valuation_lt_one_iff_mem,show (pointPrime x).asIdeal =
  Ideal.span {z7y - C x} from rfl,Ideal.mem_span_singleton,dvd_iff_isRoot]
private theorem exp_uniformizer_pow (m:ℕ) :exp (-1 :ℤ)^m=exp (-(m:ℤ)) := by
 rw [← exp_nsmul,smul_neg,nsmul_one]
private theorem val_uniformizer (x :L) :
  pointVal x (phys (z7y - C x))=exp (-1 :ℤ) := by
 change (pointPrime x).valuation FX (algebraMap L[X] FX _)= _
 rw [valuation_of_algebraMap]
 exact (pointPrime x).intValuation_singleton (X_sub_C_ne_zero x) rfl
private theorem val_poly (x :L) (f :L[X]) (hf :f≠0) :
  pointVal x (phys f)=exp (-(f.rootMultiplicity x :ℤ)) := by
 obtain ⟨q,he,hq⟩:=f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf x
 have hqv :pointVal x (phys q)=1 := by
  change (pointPrime x).valuation FX (algebraMap L[X] FX q)=1
  exact (pointPrime x).valuation_eq_one_iff_notMem.mpr (Ideal.mem_span_singleton.not.mpr hq)
 conv_lhs=>rw [he]
 rw [phys.map_mul,phys.map_pow,map_mul,map_pow,val_uniformizer,hqv,mul_one,
  exp_uniformizer_pow]
private theorem small_value {v :ℤᵐ⁰} (h:v<1) :v≤exp (-1 :ℤ) := by
 apply (lt_mul_exp_iff_le (y :=exp (-1 :ℤ)) exp_ne_zero).mp
 simpa only [← exp_add,neg_add_cancel,exp_zero] using h
end
end qqi5QRb
end
