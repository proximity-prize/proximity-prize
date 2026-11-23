import ProximityPrize.SubmissionLower.ZN2gA7a
import ProximityPrize.SubmissionLower.ZQ2Yete
import ProximityPrize.SubmissionLower.Ziv4Lwe
import ProximityPrize.SubmissionLower.ZeoK8Ne
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace qazuAoe
noncomputable section
open Polynomial qrKC9pb
open cu (L)
open P5 (p)
open P5_7_7 (Dg seedDerivative)
open qGnV2ac (coeff_seedDerivative)
open qrzQ9fc (aQ constantMap Wu)
open qU3xjYb (root_seed)
open scoped qU3xjYb WithZero nonZeroDivisors
open private mapCoeff mapCoeff_coeff from ProximityPrize.SubmissionLower.ZeoK8Ne
local notation "E" => aQ
local notation "e" => algebraMap L[X] E
private theorem extend_seed_deriv :
  ∃ δ:Derivation L E E,∀ q:L[X],δ (e q)=e q.derivative := by
 let:Algebra.FormallyEtale L[X] E :=Algebra.FormallyEtale.of_isLocalization (L[X])⁰
 let d:Derivation L L[X] L[X] :=Polynomial.derivative'
 let f :=(Algebra.linearMap L[X] E).comp d.liftKaehlerDifferential
 let g:=(f.liftBaseChange E).comp
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale L L[X] E).symm.toLinearMap
 refine ⟨g.compDer (KaehlerDifferential.D L E),fun q => ?_⟩
 change g (KaehlerDifferential.D L E (e q))= _
 simp [g,f,d,KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
private theorem chart_move (J:Input) (r :Bool) :
   qNu3xvc.chartEq (equation J) r=move (chartEq J r) := by
 cases r
 · rfl
 · change (move J.F).reflect (move J.F).natDegree=move (J.F.reflect J.F.natDegree)
   rw [move_degree]
   exact reflect_map swapCoeff J.F _
private theorem move_derivative (Q:Dg) :
 (move Q).derivative=move Q.derivative :=derivative_map _ _
private theorem physical_coeff (Q:Dg) (i j:ℕ) :
  ((physicalDerivative Q).coeff i).coeff j=((Q.coeff i).coeff j).derivative := by
 change ((mapCoeff Q (fun _ a=>mapCoeff a fun _ b=>b.derivative)).coeff i).coeff j= _
 have hz (k :ℕ) :mapCoeff (0:L[X][X]) (fun _ b=>b.derivative)=0:= by
  simp [mapCoeff]
 rw [mapCoeff_coeff Q (fun _ a=>mapCoeff a fun _ b=>b.derivative) hz i,
  mapCoeff_coeff (Q.coeff i) (fun _ b=>b.derivative) (fun _=>derivative_zero) j]
private theorem move_physical (Q:Dg) :
  qNu3xvc.physicalDerivative (move Q)=move (physicalDerivative Q) := by
 apply Polynomial.ext
 intro i
 change (mapCoeff (move Q) (fun _ a=>a.derivative)).coeff i= _
 rw [mapCoeff_coeff _ _ (fun _=>derivative_zero)]
 apply Polynomial.ext
 intro j
 rw [coeff_derivative,move_coeff,move_coeff]
 have hcast: (j:E)+1=e (C ((j:L)+1)) := by simp
 rw [hcast,← map_mul]
 congr 1
 apply Polynomial.ext
 intro k
 rw [coeff_mul_C,bOH,bOH,physical_coeff,coeff_derivative]
private theorem move_seed (δ:Derivation L E E)
  (hδ : ∀ q:L[X],δ (e q)=e q.derivative) (Q:Dg) :
  qNu3xvc.seedDerivative δ (move Q)=move (seedDerivative Q) := by
 apply Polynomial.ext
 intro i
 change (mapCoeff (move Q) (fun _ a=>mapCoeff a fun _ b=>δ b)).coeff i= _
 have hz (k :ℕ) :mapCoeff (0:E[X]) (fun _ b=>δ b)=0:= by
  simp [mapCoeff]
 rw [mapCoeff_coeff (move Q) (fun _ a=>mapCoeff a fun _ b=>δ b) hz i]
 apply Polynomial.ext
 intro j
 rw [mapCoeff_coeff ((move Q).coeff i) (fun _ b=>δ b) (fun _=>δ.map_zero) j,
  move_coeff,hδ,move_coeff]
 congr 1
 apply Polynomial.ext
 intro k
 rw [coeff_derivative,bOH,bOH,coeff_seedDerivative,coeff_derivative]
 rw [show (k :L[X])+1=C ((k :L)+1) by simp,coeff_mul_C]
private theorem back_polar (J:Input) (r :Bool) :
  back J (qNu3xvc.polar (equation J) r)=polar J r := by
 rw [qNu3xvc.polar,chart_move,move_derivative,back_eval]
 rfl
private theorem back_jet (J:Input) (r :Bool) :
  back J (qNu3xvc.jet (equation J) r)=jet J r := by
 rw [qNu3xvc.jet,map_div₀,map_neg,chart_move,move_physical,back_eval,back_polar]
 rfl
private theorem back_variation (J:Input) (r :Bool) (δ:Derivation L E E)
  (hδ : ∀ q:L[X],δ (e q)=e q.derivative) :
  back J (qNu3xvc.variation (equation J) r δ)=variation J r := by
 rw [qNu3xvc.variation,map_div₀,map_neg,chart_move,move_seed δ hδ,back_eval,back_polar]
 rfl
private theorem const_le {J:Input} {r :Bool} (D:GraphPrime J r) (a :L) :
   D.val (constant J a)≤1 := by
 by_cases ha :a=0
 · simp [ha,constant]
 · exact (D.constants a ha).le
private theorem seed_units {J:Input} {r :Bool} (D:GraphPrime J r)
   (h : ¬ ResidueConstant J D.val (seed J)) (q:L[X]) (hq:q≠0) :
   D.val (Wu J q)=1 := by
 have hlin (a :L) :D.val (Wu J ((Polynomial.X:L[X]) - C a))=1 := by
   rw [map_sub]
   simp only [Wu,coe_eval₂RingHom,eval₂_X,eval₂_C]
   change D.val (seed J - constant J a)=1
   exact le_antisymm (D.val.map_sub_le (D.regular 1) (const_le D a))
     (le_of_not_gt fun ha=>h ⟨a,ha⟩)
 have hprod (A:Multiset L) :
     D.val (Wu J (A.map fun a=>(Polynomial.X:L[X]) - C a).prod)=1 := by
   induction A using Multiset.induction_on with
   | empty=>simp
   | cons a A ih=>simp only [Multiset.map_cons,Multiset.prod_cons,map_mul,hlin,ih,mul_one]
 conv_lhs=>rw [(IsAlgClosed.splits q).eq_prod_roots,map_mul,map_mul]
 rw [show Wu J (C q.leadingCoeff)=constant J q.leadingCoeff by
   simp [Wu,constantMap,constant]]
 rw [D.constants _ (leadingCoeff_ne_zero.mpr hq),hprod,mul_one]
private def graph (J:Input) (r :Bool) (D:GraphPrime J r) :qNu3xvc.GraphVal (equation J) r where
 val :=D.val.comap (back J)
 normalized:=D.normalized.comp (back_surj J)
 constants a ha := by
  change D.val (back J (qNu3xvc.seed (equation J) (algebraMap L E a)))=1
  rw [back_seed,show algebraMap L E a=e (C a) from rfl,root_seed]
  exact (congrArg D.val (eval₂_C (constantMap J) (seed J))).trans (D.constants a ha)
 base_regular := by
  change D.val (back J (qNu3xvc.amm (equation J)))≤1
  rw [back_physical]
  exact D.regular 0
 ordinate_regular := by
  change D.val (back J (qNu3xvc.jU (equation J) r))≤1
  rw [back_ordinate]
  exact D.regular 2
 jet_regular := by
  change D.val (back J (qNu3xvc.jet (equation J) r))≤1
  rw [back_jet]
  exact D.regular 3
theorem proof :qrKC9pb.c2 := by
 intro J hm r D hp
 by_contra hn
 obtain ⟨δ,hδ⟩:=extend_seed_deriv
 let A:=equation J
 let G:=graph J r D
 have hG:qypA4Sc.Horizontal G:= by
   intro a ha
   obtain ⟨b,c,hc,rfl⟩:=IsFractionRing.div_surjective L[X] a
   have hb:b≠0:= fun hz=>ha (by simp [hz])
   change D.val (back J (qNu3xvc.seed A (e b/e c)))=1
   rw [back_seed,map_div₀,D.val.map_div,root_seed,root_seed,
     seed_units D hn b hb,seed_units D hn c (nonZeroDivisors.ne_zero hc),div_one]
 have hd:2≤A.d:=equation_degree J ▸ J.Ca.two_le
 have ht:A.d<p:=equation_degree J ▸ J.Ca.tame
 have hh:qNu3xvc.horizontalDegree A<p:= by
   change (2*A.d-2)*J.b+A.d*(A.d-1)*J.s<p
   rw [show A.d=J.l from equation_degree J]
   exact hm
 have H :=qypA4Sc.of_children qWnROxa.proof
   qlcyGcd.proof qrrOjma.proof A hd ht hh r G δ hG
 change D.val (back J (qNu3xvc.variation A r δ))≤1 at H
 rw [back_variation J r δ hδ] at H
 exact (not_le_of_gt hp) H
end
end qazuAoe
