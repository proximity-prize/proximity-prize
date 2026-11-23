import ProximityPrize.SubmissionLower.Z3vxfLe
import ProximityPrize.SubmissionLower.Zu4k70a
import ProximityPrize.SubmissionLower.Z3gZttb
import ProximityPrize.SubmissionLower.ZUCbske
import ProximityPrize.SubmissionLower.ZGAUtmc
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace P6_3_1
noncomputable section
open MvPolynomial wT gR
open P6 (K I e9 node p blockLength dw twist DY B5)
open Rv (lK)
open P6_3 (EJ)
open bjY (bhY bOZ)
open aez (awZ denominator numerator aEc bgd GA)
open private cF7 ayD c77 from ProximityPrize.SubmissionLower.B3
open private bNf from ProximityPrize.SubmissionLower.AH
private theorem a5H {u:e9} {γ:K} (M:B5 u γ) :
    M.decoder.natDegree≤131071 := by
  apply Polynomial.natDegree_le_of_degree_le
  exact Order.le_of_lt_succ (show M.decoder.degree<(131072 :ℕ) from M.degree)
private theorem bYQ {u:e9} {deleted:Finset I} (P:N7 deleted)
    {γ:K} (M:B5 u γ) :
    a2W u P M.decoder (M.decoder.map twist) γ (γ^p) (arB P M.support) := by
  intro i hi
  have h:=M.lg (P.index i) ((aVT P M.support i).mp hi)
  refine ⟨h,?_⟩
  change (M.decoder.map twist).eval (node (P.index i)) =
    u 0 (P.index i)^p+γ^p*u 1 (P.index i)^p
  rw [kL.aC4 twist M.decoder _ (Native.ahU (P.index i)),h]
  simp only [map_add,map_mul,P0.twist,frobenius_def]
private theorem fVR {u:e9} {deleted:Finset I} {h:ℕ}
    {U V:Fin 2→Polynomial K} (W:lK u deleted h U V) (P:N7 deleted)
    (hdeg: (aEc U V W.output).weightedTotalDegree (vO 131071 0)≤131071+h)
    (hcapacity :131071+h<dw) (Q Q' : Polynomial K) (hq:Q.natDegree≤131071)
    (hq' : Q'.natDegree≤131071) (s t:K) (S:Finset (Fin P.N)) (hS:dw≤S.card)
    (hc:a2W u P Q Q' s t S) :
    aeval (aju Q Q' s t) (aEc U V W.output)=0:= by
  apply aHG S P.nodes aV4 1
  · intro j hj
    rw [pow_one,Polynomial.dvd_iff_isRoot,Polynomial.IsRoot.def,c77]
    have hi:P.index j∉deleted:=(P.Z1 _).mp ⟨j,rfl⟩
    have hcj:=hc j hj
    change Q.eval (node (P.index j))=u 0 (P.index j)+s*u 1 (P.index j) ∧
      Q'.eval (node (P.index j))=u 0 (P.index j)^p+t*u 1 (P.index j)^p at hcj
    simp only [N7.nodes,Polynomial.eval_sub,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_C,hcj.1,hcj.2]
    linear_combination W.nodes _ hi 0 0+s*W.nodes _ hi 1 0 +
      t*W.nodes _ hi 0 1+(s*t)*W.nodes _ hi 1 1
  · have hd:=bc5 131071 (131071+h) _ hdeg Q Q' hq hq' s t
    simpa only [Nat.one_mul] using (hd.trans_lt hcapacity).trans_le hS
theorem proof :P6_3.c1 := by
  intro aV u deleted h U V W _ hh hs
  have hheight:h≤33561 := by
    have hh' : h+deleted.card≤DY:=hh
    change h+deleted.card≤33561 at hh'
    omega
  have hdegree :=Nat.add_le_add_left hheight 131071
  have hfit :131071+h≤EJ:=hdegree.trans (by decide)
  have hbelow:131071+h<dw:=hdegree.trans_lt (by decide)
  let P:=c1h deleted
  let L:=aEc U V W.output
  let a :=numerator U W.output
  let b:=denominator V
  have hb:b≠0:=ayD W.V_ne
  have hview:xx L=Polynomial.C b*Polynomial.X-Polynomial.C a :=
    bgd U V W.output
  have hdeg : ∀ j,L.weightedTotalDegree (vO 131071 j)=GA h j :=
    cxG.proof u deleted h U V W
  have hl:L≠0:= by
    intro hz
    have hpos :=hdeg 1
    simp [hz,GA,weightedTotalDegree] at hpos
  let C:awZ P.N L :=
    ⟨P.nodes,fun i=>u 0 (P.index i),fun i=>u 1 (P.index i),
      fun i=>u 0 (P.index i)^p,fun i=>u 1 (P.index i)^p,
      fun i=>cxH.proof u deleted h U V W (P.index i) ((P.Z1 _).mp ⟨i,rfl⟩)⟩
  have hN :P.N=blockLength - deleted.card:= by
    have hsize :P.N+deleted.card=blockLength:=P.size
    omega
  obtain ⟨G,hnot,hcontacts⟩:=bKY aV C hdeg hl hfit (hN ▸ hs)
  let Q:=aP3 5 G.val a b
  have hne :Q≠0:=bNc EJ 131071 5 aV.first aV.second
    G.val L G.property hnot a b hb hview (cxI.proof u deleted h U V W)
  have hLsource :L∈filtered (vO 131071) (A6 (131071+h) 1 1 1) := by
    apply (Wb _ _ _).mpr
    intro j
    rw [hdeg j]
    rfl
  obtain ⟨haY,hbY,haS,hbS,haT,hbT⟩:=cF7 L a b _ hLsource hview hb
  obtain ⟨hY,hS,hT⟩:=bgg
    EJ 131071 5 aV.first aV.second G.val G.property
  have hy :Q.weightedTotalDegree Qb≤5 :=
    aTD Qb 5 5 1 1 0 (xx G.val) a b
      (by simpa using hY) haY hbY (by decide)
  have hs' : Q.weightedTotalDegree ME≤aV.first+5 :=
    aTD ME 5 aV.first 0 1 1 (xx G.val) a b
      (by simpa using hS) haS hbS (by decide)
  have ht' : Q.weightedTotalDegree MD ≤aV.second :=
    aTD MD 5 aV.second 1 1 0 (xx G.val) a b
      (by simpa using hT) haT hbT (by decide)
  have htotal:Q.weightedTotalDegree LV≤42 :=
    (bNf Q _ _ hs' ht').trans (by cases aV <;> decide)
  refine ⟨bhY Q hne hy hs' ht' htotal,?_⟩
  intro γ M hdis
  rw [bOZ]
  let S:=arB P M.support
  have hS' : dw≤S.card:= by
    rw [beB P M.support
      (fun i hi hid=>Finset.disjoint_left.mp hdis hi hid)]
    exact M.dw
  have hd:=a5H M
  have hd' : (M.decoder.map twist).natDegree≤131071 :=Polynomial.natDegree_map_le.trans hd
  have hcorrect :=bYQ P M
  have hrel :=fVR W P (le_of_eq (hdeg 0)) hbelow
    _ _ hd hd' γ (γ^p) S hS' hcorrect
  apply bNb EJ 131071 5 aV.first aV.second
    G.val L G.property a b hview M.decoder (M.decoder.map twist) γ (γ^p) hrel
  apply aHG S P.nodes aV4 4
  · intro i hi
    obtain ⟨R,hR⟩:=hcontacts i
    exact bDX 4 _ _ _ _ _ γ (γ^p) _ _ G.val L R.val
      (hcorrect i hi).1 (hcorrect i hi).2 hrel hR
  · have hdG:=bc5 131071 EJ G.val
      ((Wb _ _ _).mp G.property 0) _ _ hd hd' γ (γ^p)
    have hcut:EJ<4*dw:= by decide
    omega
end
end P6_3_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace P6_3_2
noncomputable section
open P6 MvPolynomial
open bAi (b9O)
open P6_3 (arz)
open agK (ae8 ayE bC OT)
open scoped Polynomial
open private bUh from ProximityPrize.SubmissionLower.AY
open private D4 bFt from ProximityPrize.SubmissionLower.A0
open private bD8 agK.aC5 from ProximityPrize.SubmissionLower.A0
theorem proof :P6_3.c2 := by
  classical
  intro aV u A Γ hΓ
  let F:UJ u Γ:= fun γ hγ=>Classical.choose (hΓ γ hγ).2
  have hF (γ:K) (hγ:γ∈Γ) :
      A.auh γ≠0∧A.aSV γ (F γ hγ).decoder=0 :=
    ⟨(hΓ γ hγ).1,Classical.choose_spec (hΓ γ hγ).2⟩
  obtain ⟨g,hg,hassign⟩:=bUh A Γ (fun γ hγ=>(F γ hγ).decoder) hF
  let charts (j:Fin 5) :=Γ.filter fun γ =>
    ∃ hγ:γ∈Γ,ae8 (ayE g j) γ (F γ hγ).decoder
  have hsub (j:Fin 5) :charts j⊆Γ:=Finset.filter_subset _ _
  have hcover :Γ⊆Finset.univ.biUnion charts := by
    intro γ hγ
    obtain ⟨j,hj⟩:=hassign γ hγ
    exact Finset.mem_biUnion.mpr
      ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hγ,hγ,hj⟩⟩
  have hchart (j:Fin 5) : ((charts j).card:ℚ)≤42*arz^2 := by
    rcases (charts j).eq_empty_or_nonempty with hempty | ⟨γ₀,hγ₀⟩
    · simp only [hempty,Finset.card_empty,Nat.cast_zero]
      positivity
    let G:=ayE g j
    let M:UJ u (charts j) := fun γ hγ=>F γ (hsub j hγ)
    have hregular (γ:K) (hγ:γ∈charts j) :ae8 G γ (M γ hγ).decoder := by
      obtain ⟨_,hr⟩:=(Finset.mem_filter.mp hγ).2
      exact hr
    have hG:G.totalDegree≤42 :=(bD8 g j).trans hg
    let C:blb M :=
      ⟨D4 u G,b9O u G hG,fun γ hγ i =>
        bFt u G γ (M γ hγ).decoder (hregular γ hγ) (M γ hγ).degree i⟩
    have hinj:=IsFractionRing.injective K[X] kB
    have hGne :G≠0:= by
      intro h
      exact (hregular γ₀ hγ₀).2 (by simp [h,OT])
    have hgne :bC G≠0:= by
      intro h
      exact hGne (MvPolynomial.map_injective (algebraMap K[X] kB) hinj
        (by simpa [bC] using h))
    have hgd: (bC G).totalDegree≤42 := by
      simpa only [bC,totalDegree,support_map_of_injective G hinj] using hG
    apply cIr M C (bC G) (bC (MvPolynomial.pderiv 0 G)) hgne hgd
    intro γ hγ
    obtain ⟨hr,hs⟩:=hregular γ hγ
    rw [agK.aC5,agK.aC5,hr,map_zero]
    exact ⟨rfl,by simpa only [map_zero] using hinj.ne hs⟩
  have hnat :Γ.card ≤ ∑ j:Fin 5,(charts j).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrat : (Γ.card:ℚ)≤5*42*arz^2 := by
    calc
      (Γ.card:ℚ) ≤ ∑ j:Fin 5,((charts j).card:ℚ) := by exact_mod_cast hnat
      _ ≤ ∑ _j:Fin 5,(42*arz^2 :ℚ) :=
        Finset.sum_le_sum fun j _=>hchart j
      _ = _:= by simp; ring
  have hrounded: (Γ.card:ℚ)≤(P6_3.aPP:ℚ) := by
    unfold P6_3.aPP
    apply hrat.trans
    rw [show (5:ℚ)*42=((210 :ℕ) :ℚ) by norm_num]
    exact Nat.le_ceil _
  exact_mod_cast hrounded
end
end P6_3_2
end
section
set_option autoImplicit true
namespace qeUg7Fa
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
local notation "r!" z "," p=>asA (v :=z) (by rfl) p
private theorem xL6fc0:total 2655 4=0xb64cf295950:=r! 0x2daca50a490,r! 0x2d9bb4b9800,r! 0x2d8ac1687b0,r! 0x2d79d769510,rfl
private theorem xL6fc1:total 2659 4=0xb53e58a37c0:=r! 0x2d68eb505b0,r! 0x2d5806db560,r! 0x2d4721868f0,r! 0x2d3644f13c0,rfl
private theorem xL6fc2:total 2663 4=0xb4308cdac50:=r! 0x2d2564bcd70,r! 0x2d148e7c350,r! 0x2d03b4a7af0,r! 0x2cf2e4fa0a0,rfl
private theorem r1:total 2655 12=0x21fbbd813d60:=total_append xL6fc0 (total_append xL6fc1 xL6fc2)
private theorem xL6fc3:total 2667 4=0xb3239214460:=r! 0x2ce2128bbf0,r! 0x2cd14878ef0,r! 0x2cc07ca7f70,r! 0x2cafba67a10,rfl
private theorem xL6fc4:total 2671 4=0xb21765ad050:=r! 0x2c9ef3be790,r! 0x2c8e37d3580,r! 0x2c7d77d90b0,r! 0x2c6cc242290,rfl
private theorem xL6fc5:total 2675 4=0xb10c05e9ce0:=r! 0x2c5c098fdb0,r! 0x2c4b59b64e0,r! 0x2c3aa79ee60,r! 0x2c29fb04bf0,rfl
private theorem r2:total 2667 12=0x21646fdab190:=total_append xL6fc3 (total_append xL6fc4 xL6fc5)
private theorem xL6fc6:total 2679 4=0xb0017613220:=r! 0x2c1952b70e0,r! 0x2c08ac58ff0,r! 0x2bf80bec200,r! 0x2be76b16f50,rfl
private theorem xL6fc7:total 2683 4=0xaef7bacec60:=r! 0x2bd6d102f30,r! 0x2bc636e4860,r! 0x2bb5a2d9f30,r! 0x2ba5100d5a0,rfl
private theorem xL6fc8:total 2687 3=0x828be763880:=r! 0x2b9482041a0,r! 0x2b83f5dd560,r! 0x2b736f82180,rfl
private theorem r3:total 2679 11=0x1e1851845700:=total_append xL6fc6 (total_append xL6fc7 xL6fc8)
theorem YE :total 2655 35=0x61787ee045f0 :=
  (total_append r1 (total_append r2 r3))
end qeUg7Fa
end
section
set_option autoImplicit true
namespace qxJEhle
theorem proof :P6_6_8.c1 := by
  refine ⟨boundary1,?_⟩
  intro j hlo hhi
  interval_cases j
  · exact boundary2
  · exact boundary3
  · exact boundary4
  · exact boundary5
  · exact boundary6
end qxJEhle
end
