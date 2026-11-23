import ProximityPrize.SubmissionLower.Zeo5Ibd
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace qazuAoe
noncomputable section
open Polynomial qrKC9pb
open cu (L)
open P5_7_7 (Dg)
open qrzQ9fc (aQ)
open scoped qU3xjYb nonZeroDivisors
open private coeffIn coeffIn_eq from ProximityPrize.SubmissionLower.ZsE91Ed
local notation "E" => aQ
local notation "e" => algebraMap L[X] E
local notation "U" => qNu3xvc.Equation
def swapCoeff :L[X][X] →+* E[X] :=
 (mapRingHom e).comp Bivariate.swap.toRingHom
def move :Dg →+* E[X][X] :=mapRingHom swapCoeff
theorem move_inj:Function.Injective move :=
 Polynomial.map_injective _ ((Polynomial.map_injective _ (IsFractionRing.injective L[X] E)).comp
  Bivariate.swap.injective)
theorem move_degree (F:Dg) : (move F).natDegree=F.natDegree := by
 change (F.map swapCoeff).natDegree= _
 exact natDegree_map_eq_of_injective
  ((Polynomial.map_injective _ (IsFractionRing.injective L[X] E)).comp Bivariate.swap.injective) F
theorem bOH (f :L[X][X]) (i j:ℕ) :
    ((Bivariate.swap f).coeff i).coeff j=(f.coeff j).coeff i:= by
  induction f using Polynomial.induction_on' with
  | add f g hf hg=>simp only [map_add,coeff_add,hf,hg]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb=>simp only [map_add,coeff_add,ha,hb]
    | monomial m a =>
      by_cases hn:n=j <;> by_cases hm:m=i <;>
        simp [Bivariate.swap_monomial_monomial,coeff_monomial,hn,hm]
theorem move_coeff (F:Dg) (i j:ℕ) :
  ((move F).coeff i).coeff j=e ((Bivariate.swap (F.coeff i)).coeff j) := by
 change ((F.map swapCoeff).coeff i).coeff j= _
 rw [coeff_map]
 exact coeff_map _ _
private def S:Dg ≃+* Dg :=
 Polynomial.mapEquiv (Bivariate.swap (R:=L)).toRingEquiv
private def M:Submonoid L[X][X] :=(L[X])⁰.map (C:L[X] →+* L[X][X])
private def N :Submonoid Dg:=M.map (C:L[X][X] →+* Dg)
local instance :Algebra L[X][X] E[X] :=Polynomial.algebra L[X] E
local instance :Algebra Dg E[X][X] :=Polynomial.algebra L[X][X] E[X]
local instance :IsLocalization (R:=L[X][X]) M (Polynomial E) :=Polynomial.isLocalization (L[X])⁰ E
local instance :IsLocalization (R:=Dg) N (Polynomial (Polynomial E)) :=Polynomial.isLocalization M (Polynomial E)
private theorem loc_move (Q:Dg) :
  mapRingHom (mapRingHom e) (S Q)=move Q:= by
 change (Q.map (Bivariate.swap (R:=L)).toRingHom).map (mapRingHom e)= _
 exact Polynomial.map_map _ _ _
private theorem move_irreducible (J:Input) :Irreducible (move J.F) := by
 let f :=IsLocalization.toLocalizationMap (R:=Dg) N E[X][X]
 have he :f (S J.F)=move J.F:=loc_move J.F
 have hi:Irreducible (S J.F) :=
   (MulEquiv.irreducible_iff S.toMulEquiv).mpr J.Ca.irreducible
 have hn:move J.F≠0 :=
   (map_ne_zero_iff move move_inj).mpr J.Ca.irreducible.ne_zero
 have hu : ¬ IsUnit (move J.F) := fun h=> by
   have hz :=natDegree_eq_zero_of_isUnit h
   rw [move_degree,J.Ca.jU] at hz
   exact (by decide : ¬ 2≤0) (hz ▸ J.Ca.two_le)
 have hp:Prime (f (S J.F)) :=
   @Submonoid.LocalizationMap.map_prime Dg E[X][X] _ _ N f
     (S J.F) hi.prime (he.symm ▸ hn) (he.symm ▸ hu)
 rw [he] at hp
 exact hp.irreducible
def equation (J:Input) :U E :=
  ⟨move J.F,move_irreducible J,by
    rw [move_degree,J.Ca.jU]
    exact Nat.zero_lt_of_lt J.Ca.two_le,J.s,J.b,fun i=> by
    classical
    by_cases hz : (move J.F).coeff i=0
    · exact Or.inr hz
    · left
      have hcap : ∀ j,(((move J.F).coeff i).coeff j)≠0→j+i*J.s≤J.b+J.l*J.s := by
        intro j hj
        rw [move_coeff] at hj
        have hn: (Bivariate.swap (J.F.coeff i)).coeff j≠0:= fun h=>hj (by rw [h,map_zero])
        obtain ⟨k,hk⟩ : ∃ k,((Bivariate.swap (J.F.coeff i)).coeff j).coeff k≠0:= by
          by_contra! h
          exact hn (Polynomial.ext fun k=>(h k).trans (coeff_zero k).symm)
        rw [bOH] at hk
        have hq: (J.F.coeff i).coeff k≠0:= fun h=>hk (by rw [h,coeff_zero])
        exact (Nat.add_le_add_right (le_natDegree_of_ne_zero hk) _).trans (J.weight i k hq)
      rw [move_degree,J.Ca.jU]
      have htop:=hcap _ (leadingCoeff_ne_zero.mpr hz)
      exact htop⟩
theorem equation_degree (J:Input) : (equation J).d=J.l :=
 (move_degree J.F).trans J.Ca.jU
def baseToRoot (J:Input) :E[X] →+* EC J :=
 eval₂RingHom (algebraMap E (EC J)) (amm J)
theorem base_bridge (J:Input) (a :L[X][X]) :
  baseToRoot J (swapCoeff a)=a7W J (C a) := by
 have h:=RingHom.congr_fun (coeffIn_eq J) a
 change (qU3xjYb.PhysField J).val.toRingHom (coeffIn J a)=a7W J (C a) at h
 rw [← h]
 let P:=qU3xjYb.PhysField J
 let x :P:=⟨amm J,IntermediateField.mem_adjoin_simple_self E _⟩
 exact (hom_eval₂ (swapCoeff a) (algebraMap E P) P.val.toRingHom x).symm
private def y (J:Input) :EC J:=jU J false
private theorem eval_move (J:Input) (t:EC J) (Q:Dg) :
   (move Q).eval₂ (baseToRoot J) t= Q.eval₂ ((a7W J).comp C) t :=
 (eval₂_map _ _ _).trans (eval₂_congr (RingHom.ext (base_bridge J)) rfl rfl)
private def liftRoot (J:Input) :AdjoinRoot (equation J).f →+* EC J :=
 AdjoinRoot.lift (baseToRoot J) (y J) (by
  rw [show (equation J).f=move J.F from rfl,eval_move]
  exact chart_root J false)
private theorem liftRoot_inj (J:Input) :Function.Injective (liftRoot J) := by
 apply (injective_iff_map_eq_zero (liftRoot J)).mpr
 intro u hu
 obtain ⟨Q,rfl⟩:=AdjoinRoot.mk_surjective u
 obtain ⟨⟨B,d⟩,h⟩:=IsLocalization.surj (R:=Dg) N Q
 let R:=S.symm B
 let t:=mapRingHom (mapRingHom e) (d:Dg)
 have hb:Q*t=move R:= by
   rw [← loc_move,show S R=B from S.apply_symm_apply B]
   exact h
 have hzero :a7W J R=0:= by
   have he :=congrArg (fun q=>liftRoot J (AdjoinRoot.mk (equation J).f q)) hb
   change liftRoot J (AdjoinRoot.mk (equation J).f (Q*t)) =
     liftRoot J (AdjoinRoot.mk (equation J).f (move R)) at he
   rw [map_mul,map_mul,hu,zero_mul] at he
   rw [liftRoot,AdjoinRoot.lift_mk,eval_move] at he
   rw [← chartEval_false J]
   exact he.symm
 have hdiv : (equation J).f∣Q*t:= by
   rw [hb]
   exact map_dvd move ((rootMap_eq_zero_iff J R).mp hzero)
 refine AdjoinRoot.mk_eq_zero.mpr (((equation J).irreducible.prime.dvd_mul.mp hdiv).resolve_right ?_)
 have hunit :IsUnit t :=
   @IsLocalization.map_units Dg _ N (Polynomial (Polynomial E)) _ _ _ d
 exact fun hd=>(equation J).irreducible.not_isUnit (isUnit_of_dvd_unit hd hunit)
def back (J:Input) :qNu3xvc.EC (equation J) →+* EC J :=
 IsFractionRing.lift (liftRoot_inj J)
theorem back_root (J:Input) (Q:E[X][X]) :
   back J (qNu3xvc.a7W (equation J) Q)= Q.eval₂ (baseToRoot J) (y J) :=
 (IsFractionRing.lift_algebraMap (liftRoot_inj J) _).trans (AdjoinRoot.lift_mk _ _)
theorem back_move (J:Input) (Q:Dg) :
  back J (qNu3xvc.a7W (equation J) (move Q))=a7W J Q:= by
 rw [back_root,eval_move]
 change KM J false Q= _
 rw [chartEval_false]
theorem back_surj (J:Input) :Function.Surjective (back J) := by
 intro a
 obtain ⟨b,c,_,rfl⟩:=IsFractionRing.div_surjective (AdjoinRoot J.F) a
 obtain ⟨B,rfl⟩:=AdjoinRoot.mk_surjective b
 obtain ⟨C',rfl⟩:=AdjoinRoot.mk_surjective c
 exact ⟨qNu3xvc.a7W (equation J) (move B) /
  qNu3xvc.a7W (equation J) (move C'),by rw [map_div₀,back_move,back_move]; rfl⟩
theorem back_seed (J:Input) (a :E) :
  back J (qNu3xvc.seed (equation J) a)=algebraMap E (EC J) a := by
 change back J (qNu3xvc.a7W (equation J) (C (C a)))= _
 rw [back_root,eval₂_C]
 exact eval₂_C _ _
theorem back_physical (J:Input) :
  back J (qNu3xvc.amm (equation J))=amm J:= by
 change back J (qNu3xvc.a7W (equation J) (C (Polynomial.X:E[X])))= _
 rw [back_root,eval₂_C]
 exact eval₂_X _ _
theorem back_ordinate (J:Input) (r :Bool) :
   back J (qNu3xvc.jU (equation J) r)=jU J r := by
 cases r
 · exact (back_root J Polynomial.X).trans (eval₂_X _ _)
 · exact (map_inv₀ _ _).trans (congrArg Inv.inv ((back_root J Polynomial.X).trans (eval₂_X _ _)))
theorem back_eval (J:Input) (r :Bool) (Q:Dg) :
  back J (qNu3xvc.KM (equation J) r (move Q))=KM J r Q:= by
 change back J ((move Q).eval₂ _ _)= _
 rw [hom_eval₂,back_ordinate]
 simp only [move,coe_mapRingHom,eval₂_map]
 apply eval₂_congr _ rfl rfl
 apply RingHom.ext
 intro a
 change back J (qNu3xvc.a7W (equation J) (C (swapCoeff a)))=a7W J (C a)
 rw [back_root,eval₂_C,base_bridge]
end
end qazuAoe
