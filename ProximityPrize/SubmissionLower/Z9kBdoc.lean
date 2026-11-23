import ProximityPrize.SubmissionLower.Z9Zvicc
set_option Elab.async false
open _root_ renaming Ideal → znc, Nat.cast_le → z9h, Nat.cast_sum → zCt, Nat.le_of_lt_succ → zeh, Nat.le_of_not_gt → zqB, Nat.mul_le_mul_left → zBI, Nat.zero_le → zD0, Polynomial.uniqueFactorizationMonoid → zV6
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace qwX0f2d
noncomputable section
open Finset
open P6_7_3 (Input OriginCover IntroIndex introductions introCap wD)
open qehP9ee (asShape kK mixedCols)
open qUrGXob (originShape originBox lastOrigin initialBound resourceBill)
open cu (Jet Shape)
open pI (oU mass)
open TD (J2)
open akZ (btm bKa caQ aHP cfi)
open scoped Classical
open private tariff_cast cast_fold from ProximityPrize.SubmissionLower.Zc1KtHb
open private a8m from ProximityPrize.SubmissionLower.CR
open private b6z from ProximityPrize.SubmissionLower.D7
variable {x :Input} {anchorRow :Jet} (O:OriginCover x anchorRow)
theorem spend_cap {f :Jet} (hf :f∈O.factors) (j:Fin 3) :
    wD f j≤ introCap (O.origin f).val j :=
  (single_le_sum (fun _ _=>zD0 _) (f := fun g=>wD g j)
    (show f∈O.factors.filter (fun g=>(O.origin f).val≤(O.origin g).val) from
      mem_filter.mpr ⟨hf,le_rfl⟩)).trans
    (O.nested _ (zeh (O.origin f).isLt) j)
theorem line_last {f :Jet} (hf :f∈O.factors) (hl:O.line f=true) :
    O.origin f=lastOrigin := by
  apply Fin.ext
  refine (zeh (O.origin f).isLt).antisymm (zqB ?_)
  intro hs
  have h:=O.cut_caps f hf
  rw [dite_eq_left hs,hl] at h
  exact Bool.noConfusion h.1
private theorem origin_eq_box (o:IntroIndex) :originShape o=qFOgTpd.box o:= by
  unfold originShape qFOgTpd.box
  split <;> rename_i h
  · rfl
  · have he :o.val=introductions.length :=
      le_antisymm (zeh o.isLt) (zqB h)
    rw [he]
    rfl
theorem origin_J (o:IntroIndex) : (originShape o).J≤(originShape o).B:= by
  rw [origin_eq_box]
  exact qFOgTpd.box_J o
theorem cut_caps {f :Jet} (hf :f∈O.factors) :
    oU (O.cut f) (originShape (O.origin f)) ∧
    oU (O.cut f) (if O.line f then asShape (wD f) else originShape (O.origin f)) := by
  have h:=O.cut_caps f hf
  split at h
  · rename_i hs
    obtain ⟨hl,hc⟩:=h
    rw [hl,ite_eq_right (by decide :false≠true),originShape,dite_eq_left hs]
    exact ⟨hc,hc⟩
  · rename_i hs
    have he : (O.origin f).val=introductions.length :=
      le_antisymm (zeh (O.origin f).isLt) (zqB hs)
    rw [origin_eq_box,qFOgTpd.box,dite_eq_right hs]
    have hcap (j) :wD f j≤ introCap introductions.length j:= by
      rw [← he]
      exact spend_cap O hf j
    by_cases hl:O.line f=true
    · rw [ite_eq_left hl] at h ⊢
      exact ⟨qFOgTpd.enclose_last hcap true h,h⟩
    · rw [ite_eq_right hl] at h ⊢
      have hc:=qFOgTpd.enclose_last hcap false h
      exact ⟨hc,hc⟩
private theorem assigned_J {f :Jet} (hf :f∈O.factors) :
    (if O.line f then asShape (wD f) else originShape (O.origin f)).J ≤
    (if O.line f then asShape (wD f) else originShape (O.origin f)).B:= by
  split
  · exact caQ (O.proper f hf).1.ne_zero
  · exact origin_J _
open q54LkTb (tD)
private theorem mass_cut {f :Jet} (hf :f∈O.factors) (k :Fin 4)
    {s :Shape} (hs :s.J≤ s.B) (hc:oU (O.cut f) s) :
    mass (O.parents f) k≤aHP s k f := by
  have hp:=O.proper f hf
  obtain ⟨_,hm⟩:=a8m f (O.cut f) (b6z hp.1 hp.2.2)
    (btm f) s (caQ hp.1.ne_zero) hs (bKa f) hc (O.parents f) (fun I hI=> by
      obtain ⟨ha,_,hp,hq⟩:=O.geometric f hf I hI
      exact ⟨ha.prime,ha.dimension,hp,hq⟩)
  exact (hm k).trans_eq (cfi f s hs k)
theorem mass_assigned {f :Jet} (hf :f∈O.factors) (k :Fin 4) :
    J2 (O.parents f) k ≤
      kK (wD f) (if O.line f then asShape (wD f) else originShape (O.origin f)) k :=
  ((z9h (α:=ℚ)).mpr (mass_cut O hf k (assigned_J O hf)
    (cut_caps O hf).2)).trans_eq (tariff_cast _ _ _)
theorem mass_origin_spend {f :Jet} (hf :f∈O.factors) (k :Fin 4) :
    J2 (O.parents f) k≤kK (wD f) (originShape (O.origin f)) k :=
  ((z9h (α:=ℚ)).mpr (mass_cut O hf k (origin_J _) (cut_caps O hf).1)).trans_eq
    (tariff_cast _ _ _)
theorem mass_origin {f :Jet} (hf :f∈O.factors) (k :Fin 4) :
    J2 (O.parents f) k≤originBox (O.origin f) k :=
  (mass_origin_spend O hf k).trans (tD (spend_cap O hf) _ _)
private def oldN (v :IntroIndex→ℕ) (i:ℕ) :ℕ :=
  ((List.ofFn v).take i).foldl max 0
private def billN (k :Fin 4) (j:Fin 3) :ℕ :=
  ∑ i:IntroIndex,
    let v := fun o=>mixedCols (originShape o) k j
    (max (v i) (oldN v i.val) - oldN v i.val)*introCap i.val j
private theorem old_cast (v :IntroIndex→Fin 3→ℕ) (i:ℕ) (j:Fin 3) :
    (((List.ofFn (fun o l=>(v o l:ℚ))).take i).foldl (fun n w=>max n (w j)) 0) =
    (oldN (fun o=>v o j) i:ℚ) := by
  rw [List.ofFn_comp' v (fun w l=>(w l:ℚ)),← List.map_take,← Nat.cast_zero,← cast_fold]
  unfold oldN
  rw [List.ofFn_comp' v (fun w=>w j),← List.map_take,List.foldl_map]
private theorem bill_cast (k :Fin 4) :
    resourceBill (fun o j=>mixedCols (originShape o) k j) = ∑ j,(billN k j:ℚ) := by
  unfold resourceBill billN
  simp only [old_cast,zCt,Nat.cast_mul,Nat.cast_sub (le_max_right _ _),Nat.cast_max]
  exact sum_comm
private def billCols :Fin 4→Fin 3→ℕ :=
  ![![4749,3634,0],![0,66675,45019],![320858,0,205021],![0,0,3146577]]
private theorem bill_value (k :Fin 4) (j:Fin 3) :billN k j=billCols k j:= by
  fin_cases k <;> fin_cases j <;> decide
private theorem initial_value (k :Fin 4) :initialBound k=(qFOgTpd.massCap k :ℚ) := by
  rw [initialBound,bill_cast]
  simp only [bill_value,← zCt,← Nat.cast_add]
  apply congrArg (fun n:ℕ=>(n:ℚ))
  fin_cases k <;> decide
theorem mass_initial (k :Fin 4) : (∑ f∈O.factors,J2 (O.parents f) k)≤ initialBound k := by
  have h (f :Jet) (hf :f∈O.factors) :
      mass (O.parents f) k≤aHP (qFOgTpd.box (O.origin f)) k f := by
    rw [← origin_eq_box]
    exact mass_cut O hf k (origin_J _) (cut_caps O hf).1
  have ht:=(sum_le_sum h).trans (qFOgTpd.charge O.factors O.origin O.nested k)
  rw [initial_value]
  simpa only [J2,zCt] using (z9h (α:=ℚ)).mpr ht
end
end qwX0f2d
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace qwX0f2d
noncomputable section
open Finset
open P6 (p)
open P6_7_3 (Input Poles Picks afa OriginCover movingOrder emz hi buffer cutoff)
open qUrGXob
open q54LkTb (le_folds)
open cu (Jet Shape)
open DP (d3q d3r)
open gT (Ambient CG iJ)
open pI (xN dual O9 pN mass)
open ac2 (bp3 dLt aVL)
open TD (J2 bfw)
open scoped Classical
open private mass_fold from ProximityPrize.SubmissionLower.Zc1KtHb
open private dfc ddV from ProximityPrize.SubmissionLower.U
private theorem cDK {x :Input} (P:Poles x) {s :Shape} {r :ℕ}
    (hroom:2*hi*r≤ cutoff s) (hr :r<p) {I:znc Ambient}
    (ha :xN I) (hd:dual I) (hv :inBank P.rows s I)
    {Q:Jet} (hQ:Q∈P.rows s (buffer x.h r s)) :
    O9 I Q (r+1) := by
  have hcut:=(Nat.sub_add_cancel ((Nat.mul_le_mul_right r
    (zBI 2 (emz x).2)).trans hroom)).le
  have hs :qQ.bk4 x.h P.rows s :=
    fun _ _ h i a=>atp.d3s P.crt x.word h i a
  have hc:bp3 (I.map CG) (CG (iJ Q)) r := by
    rw [aVL]
    intro t ht
    rw [← dfc]
    apply Ideal.mem_map_of_mem
    apply hv
    exact d3q P.crt x.word rfl rfl rfl le_rfl
      ((Nat.add_le_add_left (zBI _ ht) _).trans hcut) (ddV hs hQ t)
  exact dLt hd (cy0.proof I ha.prime ha.jet_finite hd ha.jet_lt _ r hr hc)
private theorem stage_buffer (i:afa) :
    (stage i).dI<p∧2*hi*(stage i).dI≤ cutoff (stage i).free ∧
      2*hi*(stage i).dI≤ cutoff (stage i).moving:= by
  fin_cases i <;> decide
theorem free_order {x :Input} (P:Poles x) (pick :Picks x.h P.rows) (i:afa)
    {I:znc Ambient} (ha :xN I) (hd:dual I) (hv :inBank P.rows (stage i).free I) :
    O9 I (pick.main i).free ((stage i).dI+1) :=
  cDK P (stage_buffer i).2.1 (stage_buffer i).1 ha hd hv (pick.main i).free_mem
theorem moving_order {x :Input} (P:Poles x) (pick :Picks x.h P.rows) (i:afa)
    {I:znc Ambient} (ha :xN I) (hd:dual I) (hv :inBank P.rows (stage i).moving I) :
    O9 I (pick.main i).moving ((stage i).dI+1) :=
  cDK P (stage_buffer i).2.2 (stage_buffer i).1 ha hd hv (pick.main i).moving_mem
theorem moving_guards (j:Fin movingOrder.length) :
    let i:=movingStage j
    let s :=stage i
    0<s.dI∧s.dI<p∧s.free.B<p∧s.moving.B<p ∧
      s.free.U<p∧s.moving.U<p∧s.free.J≤ s.free.B∧s.moving.J≤ s.moving.B:= by
  fin_cases j <;> decide
private def movingSlot (j:Fin movingOrder.length) :Trial :=
  ⟨7+j.val,by have :=j.isLt; change j.val<4 at this; omega⟩
private theorem moving_trial (j:Fin movingOrder.length) :
    trialKind (movingSlot j)=TrialKind.moving (movingStage j) := by
  fin_cases j <;> rfl
abbrev freeStages :List afa :=([1,2,3,4,5,6,7] :List (Fin 8))
theorem free_slot {i:afa} (hi:i∈freeStages) :
    ∃ t:Trial,t.val<7∧trialKind t=TrialKind.free i:= by
  fin_cases i <;> first
    | exact ⟨0,by decide,rfl⟩
    | exact ⟨1,by decide,rfl⟩
    | exact ⟨2,by decide,rfl⟩
    | exact ⟨3,by decide,rfl⟩
    | exact ⟨4,by decide,rfl⟩
    | exact ⟨5,by decide,rfl⟩
    | exact ⟨6,by decide,rfl⟩
    | exact ((show ¬ (⟨0,by decide⟩:afa)∈freeStages by decide) hi).elim
theorem moving_index {t:Trial} {i:afa} (h:trialKind t=TrialKind.moving i) :
    ∃ j:Fin movingOrder.length,t.val = 7+j.val∧i=movingStage j:= by
  fin_cases t <;> cases h <;> first
    | exact ⟨⟨0,by decide⟩,rfl,rfl⟩
    | exact ⟨⟨1,by decide⟩,rfl,rfl⟩
    | exact ⟨⟨2,by decide⟩,rfl,rfl⟩
    | exact ⟨⟨3,by decide⟩,rfl,rfl⟩
variable {x :Input} (P:Poles x) (pick :Picks x.h P.rows)
  (R:bQX pick) (O:OriginCover x (pick.main ⟨0,by decide⟩).free)
theorem parent_mass {f :Jet} {I:znc Ambient} (hI:I∈O.parents f) (k :Fin 4) :
    (pN I k :ℚ)≤J2 (O.parents f) k :=
  Nat.cast_le.mpr (YX.evL hI k)
theorem history_mass (s :bAL) (k :Fin 4) :
    (∑ f∈O.factors,J2 (QV R O f s) k)≤bAW s k := by
  let S:=O.factors.biUnion fun f=>QV R O f s
  have hdis : (O.factors :Set Jet).PairwiseDisjoint (fun f=>QV R O f s) := by
    intro f hf g hg hne
    exact (O.disjoint f hf g hg hne).mono (filter_subset _ _) (filter_subset _ _)
  have he :J2 S k = ∑ f∈O.factors,J2 (QV R O f s) k := by
    simp only [S,J2,mass,sum_biUnion hdis,zCt]
  rw [← he,bAW,mass_fold]
  apply le_folds
  · rw [he]
    exact (sum_le_sum fun f _=>bfw (filter_subset _ _) k).trans (mass_initial O k)
  · intro a ha
    obtain ⟨n,hn,hget⟩:=List.mem_iff_getElem.mp ha
    have hlen:n< min (s.val - moveStart.val) movingOrder.length:= by
      simpa only [List.length_take,List.length_ofFn] using hn
    obtain ⟨hs,hn'⟩:=lt_min_iff.mp hlen
    let j:Fin movingOrder.length:=⟨n,hn'⟩
    have hj:stage (movingStage j)=a := by
      simpa only [List.getElem_take,List.getElem_ofFn] using hget
    rw [← hj]
    let i:=movingStage j
    let pair :=pick.main i
    have ht: (movingSlot j).val+1<s.val := by
      change n<s.val-8 at hs
      change 7+n+1<s.val
      omega
    obtain ⟨hpos,hr,hB,hB',hU,hU',hJ,hJ'⟩:=moving_guards j
    exact aZC.proof _ _ _ true pair.free pair.moving hpos hr hB hB' hU hU' hJ hJ'
      pair.free_ne pair.moving_ne (d3r P.crt x.word pair.free_mem)
      (d3r P.crt x.word pair.moving_mem) pair.no_moving (R.free i) (R.moving i) S
      (fun _ I hI=> by
        obtain ⟨f,_,hI⟩:=mem_biUnion.mp hI
        exact (mem_filter.mp hI).2.2.1 (by omega))
      (fun I hI=> by
        obtain ⟨f,hf,hI⟩:=mem_biUnion.mp hI
        obtain ⟨hI,hc,hd,hp⟩:=mem_filter.mp hI
        have ha :=(O.geometric f hf I hI).1
        have hm:=hp (movingSlot j) ht
        simp only [passes,moving_trial] at hm
        exact ⟨ha,hm.2.2,(hc j).1,(hc j).2,free_order P pick i ha (hd (by omega)) hm.1,
          moving_order P pick i ha (hd (by omega)) hm.2.1⟩) k
end
end qwX0f2d
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace qwX0f2d
noncomputable section
open Finset Polynomial
open P6_7_3 (Input Poles Picks afa OriginCover IntroIndex introductions introCap wD)
open qUrGXob
open qehP9ee (kK)
open q54LkTb (le_folds tD)
open cu (Jet)
open DP (d3r)
open gT (Ambient iJ)
open pI (xN dual oU pN mass)
open XY (ag6)
open TD (J2 bfw)
open akZ (bCj yE cN4 caQ)
open scoped Classical
open private b6z from ProximityPrize.SubmissionLower.D7
open private positive_spend b9i from ProximityPrize.SubmissionLower.Zc1KtHb
open private stage_guards from ProximityPrize.SubmissionLower.ZIe8dlc
private theorem ref_J (o:IntroIndex) : (refShape o).J≤(refShape o).B:= by
  have h:introCap o.val 1≤ introCap o.val 0:= by fin_cases o <;> decide
  exact max_le_max h (origin_J o)
private theorem free_nonneg (o:IntroIndex) (i:afa) (k :Fin 4) :0≤freeBound o i k :=
  div_nonneg (b9i _ _ _) (add_nonneg (Nat.cast_nonneg _) zero_le_one)
private theorem spend_ref {o:IntroIndex} {F:Jet} (h : ∀ j,wD F j≤ introCap o.val j) :
    oU F (refShape o) :=
  (bCj _ _).mpr fun j=>(h j).trans (by fin_cases j <;> exact le_max_left _ _)
private theorem cut_ref {o:IntroIndex} {G:Jet} (h:oU G (originShape o)) :
    oU G (refShape o) :=
  (bCj _ _).mpr fun j=>((bCj _ _).mp h j).trans
    (by fin_cases j <;> exact le_max_right _ _)
variable {x :Input} (P:Poles x) (pick :Picks x.h P.rows) (R:bQX pick)
  (O:OriginCover x (pick.main ⟨0,by decide⟩).free)
private theorem free_mass (pick :Picks x.h P.rows) (i:afa) (o:IntroIndex)
    {F G:Jet} (hproper :ag6 F G) (hF:oU F (refShape o)) (hG:oU G (refShape o))
    (S:Finset (znc Ambient))
    (hS : ∀ I∈S,xN I∧dual I∧iJ F∈I∧iJ G∈I∧inBank P.rows (stage i).free I)
    (k :Fin 4) :J2 S k≤freeBound o i k := by
  let Q:=pick.main i
  have hc:=d3r P.crt x.word Q.free_mem
  have h:=q41fOQb.proof _ _ _ _ _ S _ (Nat.succ_pos _) Q.free_ne hproper (stage_guards i).1 (ref_J o)
    (fun j i hj=>hc j i hj) hF hG (fun I hI=> by
      obtain ⟨ha,hd,hf,hg,hb⟩:=hS I hI
      exact ⟨ha,hd,hf,hg,free_order P pick i ha hd hb⟩) k
  simpa only [freeBound,Nat.cast_succ] using h
private theorem free_member_mass {f :Jet} (hf :f∈O.factors) (i:afa)
    (S:Finset (znc Ambient))
    (hS : ∀ I∈S,I∈O.parents f∧dual I∧inBank P.rows (stage i).free I) (k :Fin 4) :
    J2 S k≤freeBound (O.origin f) i k :=
  free_mass P pick i _ (b6z (O.proper f hf).1 (O.proper f hf).2.2)
    (spend_ref (spend_cap O hf)) (cut_ref (cut_caps O hf).1) S
    (fun I hI=> by
      obtain ⟨hI,hd,hb⟩:=hS I hI
      obtain ⟨ha,_,hp,hq⟩:=O.geometric f hf I hI
      exact ⟨ha,hd,hp,hq,hb⟩) k
private theorem passed_free {f :Jet} {I:znc Ambient} (hI:I∈QV R O f moveStart)
    {i:afa} (hi:i∈freeStages) :inBank P.rows (stage i).free I:= by
  obtain ⟨t,ht,he⟩:=free_slot hi
  have hb:=(mem_filter.mp hI).2.2.2 t (by
    change t.val+1<8
    omega)
  simpa only [passes,he] using hb
private def bin (o:IntroIndex) :Finset Jet:=O.factors.filter fun f=>O.origin f=o
private theorem bin_spend (o:IntroIndex) (j:Fin 3) :
    (∑ f∈bin P pick O o,wD f j)≤ introCap o.val j:= by
  refine (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _=>zD0 _)).trans
    (O.nested _ (zeh o.isLt) j)
  intro f hf
  obtain ⟨hf,he⟩:=mem_filter.mp hf
  exact mem_filter.mpr ⟨hf,he.ge⟩
private theorem bin_origin (o:IntroIndex) (k :Fin 4) :
    (∑ f∈bin P pick O o,J2 (QV R O f moveStart) k)≤originBox o k := by
  calc
    _ ≤ ∑ f∈bin P pick O o,kK (wD f) (originShape o) k := by
      apply sum_le_sum
      intro f hf
      obtain ⟨hf,he⟩:=mem_filter.mp hf
      rw [← he]
      exact (bfw (filter_subset _ _) k).trans (mass_origin_spend O hf k)
    _=kK (fun j => ∑ f∈bin P pick O o,wD f j) (originShape o) k := by
      simp only [kK,zCt,sum_mul]
      exact sum_comm
    _≤_:=tD (bin_spend P pick O o) _ _
private theorem early_free (o:IntroIndex) (ho:o.val< introductions.length)
    (i:afa) (hi:i∈freeStages) (k :Fin 4) :
    (∑ f∈bin P pick O o,J2 (QV R O f moveStart) k)≤freeBound o i k := by
  let D:=bin P pick O o
  by_cases he :D.Nonempty
  · obtain ⟨f,hf⟩:=he
    let F:Jet := ∏ g∈D,g
    let S:=D.biUnion fun g=>QV R O g moveStart
    have hcuts (g:Jet) (hg:g∈D) :O.cut g=O.cut f := by
      obtain ⟨hg,hgo⟩:=mem_filter.mp hg
      obtain ⟨hf,hfo⟩:=mem_filter.mp hf
      exact O.shared_cut g hg f hf (hgo.symm ▸ ho) (hgo.trans hfo.symm)
    have hn (g:Jet) (hg:g∈D) :g≠0:=(O.proper g (mem_filter.mp hg).1).1.ne_zero
    have hproper :ag6 F (O.cut f) := by
      let:UniqueFactorizationMonoid cu.aZ:=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
      let:UniqueFactorizationMonoid cu.Equation :=zV6 (D:=cu.aZ)
      let:UniqueFactorizationMonoid Jet:=zV6 (D:=cu.Equation)
      have hrel :IsRelPrime F (O.cut f) :=IsRelPrime.prod_left fun g hg =>
        let hp:=O.proper g (mem_filter.mp hg).1
        hp.1.isRelPrime_iff_not_dvd.mpr (hcuts g hg ▸ hp.2.2)
      have hp:=O.proper f (mem_filter.mp hf).1
      exact ⟨Finset.prod_ne_zero_iff.mpr hn,(b6z hp.1 hp.2.2).right_ne,
        fun _ hH hF hC=>hH.not_isUnit (hrel hF hC)⟩
    have hF:oU F (refShape o) :=spend_ref (fun j=> by
      change yE (∏ g∈D,g) j≤ introCap o.val j
      rw [cN4 (S:=D) (f := fun g:Jet=>g) hn]
      exact bin_spend P pick O o j)
    have hG:oU (O.cut f) (refShape o) :=
      cut_ref ((mem_filter.mp hf).2 ▸ (cut_caps O (mem_filter.mp hf).1).1)
    have hd: (D:Set Jet).PairwiseDisjoint (fun g=>QV R O g moveStart) := by
      intro g hg g' hg' hn
      exact (O.disjoint g (mem_filter.mp hg).1 g' (mem_filter.mp hg').1 hn).mono
        (filter_subset _ _) (filter_subset _ _)
    have hg:=free_mass P pick i o hproper hF hG S (fun I hI=> by
      obtain ⟨g,hg,hI⟩:=mem_biUnion.mp hI
      obtain ⟨ha,_,haF,haG⟩:=O.geometric g (mem_filter.mp hg).1 I (mem_filter.mp hI).1
      exact ⟨ha,(mem_filter.mp hI).2.2.1 (by decide),
        I.mem_of_dvd (map_dvd iJ (dvd_prod_of_mem (fun a=>a) hg)) haF,
        hcuts g hg ▸ haG,passed_free P pick R O hI hi⟩) k
    simpa only [S,D,J2,mass,sum_biUnion hd,zCt] using hg
  · rw [show bin P pick O o = ∅ from not_nonempty_iff_eq_empty.mp he,sum_empty]
    exact free_nonneg o i k
private theorem bin_card (o:IntroIndex) : (bin P pick O o).card ≤ ∑ j,introCap o.val j:= by
  calc
    _ = ∑ f∈bin P pick O o,(1 :ℕ) := by simp
    _ ≤ ∑ f∈bin P pick O o,∑ j,wD f j :=
      sum_le_sum fun f hf=>positive_spend (O.proper f (mem_filter.mp hf).1).1
    _ = ∑ j,∑ f∈bin P pick O o,wD f j:=sum_comm
    _≤_:=sum_le_sum fun j _=>bin_spend P pick O o j
private theorem prefree_bound (o:IntroIndex) (k :Fin 4) :
    (∑ f∈bin P pick O o,J2 (QV R O f moveStart) k)≤preMoving o k := by
  let v :=freeStages.foldl (fun a i=>min a (freeBound o i k)) (originBox o k)
  change _≤ if o=lastOrigin then v*(∑ j,introCap o.val j:ℕ) else v
  by_cases ho:o=lastOrigin
  · rw [ite_eq_left ho]
    have hv : ∀ f∈bin P pick O o,J2 (QV R O f moveStart) k≤v := by
      intro f hf
      obtain ⟨hf,he⟩:=mem_filter.mp hf
      apply le_folds
      · rw [← he]
        exact (bfw (filter_subset _ _) k).trans (mass_origin O hf k)
      · intro i hi
        rw [← he]
        exact free_member_mass P pick O hf i _ (fun I hI =>
          let hm:=mem_filter.mp hI
          ⟨hm.1,hm.2.2.1 (by decide),passed_free P pick R O hI hi⟩) k
    have hn:0≤v :=le_folds _ freeStages _ _
      (b9i (introCap o.val) (originShape o) k) (fun i _=>free_nonneg o i k)
    calc
      _ ≤ ∑ f∈bin P pick O o,v :=sum_le_sum hv
      _=v*((bin P pick O o).card:ℚ) := by rw [sum_const,nsmul_eq_mul,mul_comm]
      _≤_:=mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (bin_card P pick O o)) hn
  · rw [ite_eq_right ho]
    have hlt:o.val< introductions.length:= by
      have h:=zeh o.isLt
      by_contra! hb
      exact ho (Fin.ext (le_antisymm h hb))
    exact le_folds _ _ _ _ (bin_origin P pick R O o k) fun i hi =>
      early_free P pick R O o hlt i hi k
theorem proof :qUrGXob.c1 := by
  intro x P pick R O
  have hs (f :Jet) (hf :f∈O.factors) (s :bAL) (I:znc Ambient) (hI:I∈QV R O f s) :
      I∈O.parents f∧xN I :=
    ⟨(mem_filter.mp hI).1,(O.geometric f hf I (mem_filter.mp hI).1).1⟩
  have hist:=history_mass P pick R O
  refine ⟨fun f hf=>caQ (O.proper f hf).1.ne_zero,fun f=>line_last O,
    ?_,hist,prefree_bound P pick R O,?_,?_⟩
  · intro f hf k
    have h:=tail_mass R O (f :=f) 0 k
    simp only [show ∀ s :bAL,(0:bAL)≤ s from fun _=>zD0 _,ite_true] at h
    exact (h.trans (bfw (filter_subset _ _) k)).trans (mass_assigned O hf k)
  · intro f hf I hI k
    have h:=parent_mass P pick O (hs f hf 0 I (stopped_sub R O 0 hI)).1 k
    exact le_min (h.trans (mass_origin O hf k))
      (h.trans ((single_le_sum (fun g _=>TD.cZV (O.parents g) k) hf).trans
        (mass_initial O k)))
  · intro f hf t I hI
    obtain ⟨ho,ha⟩:=hs f hf t.succ I hI
    obtain ⟨_,hc,hd,hp⟩:=mem_filter.mp hI
    have hdual:=hd (Nat.succ_pos _)
    refine ⟨fun k=>le_min ((parent_mass P pick O ho k).trans (mass_origin O hf k)) ?_,?_⟩
    · have hi: (pN I k :ℚ)≤J2 (QV R O f t.succ) k :=
        Nat.cast_le.mpr (YX.evL hI k)
      exact hi.trans ((single_le_sum (f := fun g=>J2 (QV R O g t.succ) k)
        (fun _ _=>TD.cZV _ k) hf).trans (hist t.succ k))
    · intro j hj
      have hpass :=hp j (Nat.add_lt_add_right hj 1)
      cases he :trialKind j with
      | free i =>
        simp only [passes,he] at hpass
        intro k
        have h:=free_member_mass P pick O hf i {I} (fun J hJ=> by
          rw [mem_singleton.mp hJ]
          exact ⟨ho,hdual,hpass⟩) k
        simpa only [J2,mass,sum_singleton] using h
      | terminal=>trivial
      | moving i =>
        obtain ⟨a,_,rfl⟩:=moving_index he
        simp only [passes,he] at hpass
        obtain ⟨_,_,hB,_,hU,_,_,_⟩:=moving_guards a
        let i:=movingStage a
        let pair :=pick.main i
        have hf :=d3r P.crt x.word pair.free_mem
        have hm:=d3r P.crt x.word pair.moving_mem
        exact qp73k1b.proof _ pair.free pair.moving (R.free i) (R.moving i) I hB hU pair.free_ne pair.moving_ne
          (fun j y hj=>hf j y hj) (fun j y hj=>hm j y hj) pair.no_moving ha hdual
          hpass.2.2 (hc a).1 (hc a).2 (free_order P pick i ha hdual hpass.1)
          (moving_order P pick i ha hdual hpass.2.1)
end
end qwX0f2d
end
