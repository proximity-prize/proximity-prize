import ProximityPrize.SubmissionLower.Z3ozsyb
import ProximityPrize.SubmissionLower.ZBMOaEd
import ProximityPrize.SubmissionLower.ZqKag5d
import ProximityPrize.SubmissionLower.ZMwIPwd
import ProximityPrize.SubmissionLower.ZRqikKa
set_option Elab.async false
set_option maxHeartbeats 1000000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qkrKkqa
noncomputable section
open Finset
open scoped BigOperators Classical
open P6 (jG)
open q6nKpZc (Input aAT Pass Timeline)
open P5_7_2 (A fO)
open q7F2qKe (origins stops afterFree stopCount partMass freeCap originFreeCap SS
  BC globalCap projectionCap pointFee Individual dot_mass)
open q3soobb (pointShapes cut_shape_bounds)
open cu (Shape)
open gT (Ambient)
open pI (xN acW b1w pN)
open TD (GM J2 bfw FP a3x dYl bBx)
open private crE from ProximityPrize.SubmissionLower.ZHSmgre
def c1 :Prop :=
  ∀ (b:fO),2≤b.val → ∀ u del (M:jG u del) Γ (F:P1.bje A M Γ)
    (x :Input b M F) (C:aAT F b x) (o:ℕ),o∈origins b →
    (∀ f∈C.factors o,∀ j∈stops b,∀ I∈QV C o f j,∀ k,
      (pN I k :ℚ)≤freeCap b o j k) ∧
    (∀ k,partMass C.factors (QV C) o (afterFree b) k≤originFreeCap b o k)
def c2 :Prop :=
  ∀ (b:fO),2≤b.val → ∀ u del (M:jG u del) Γ (F:P1.bje A M Γ)
    (x :Input b M F) (j:ℕ),j∈stops b→0<j → ∀ I:Ideal Ambient,
      xN I → ¬ Pass x j I → ∃ Q:acW,@CutOK b u del M Γ F j I Q
variable {b u del M Γ F} {x : @Input b u del M Γ F} {C:aAT F b x}
private def cutBook (h2 :c2) (hb:2≤b.val) (x :Input b M F) (j:ℕ) (I:Ideal Ambient) :acW :=
  if h:j∈stops b∧0<j∧xN I ∧ ¬ Pass x j I then
    Classical.choose (h2 b hb u del M Γ F x j h.1 h.2.1 I h.2.2.1 h.2.2.2)
  else b1w
private theorem cutBook_ok (h2 :c2) (hb:2≤b.val) {o f j I}
    (ho:o∈origins b) (hf :f∈C.factors o) (hj:j∈stops b) (hp:0<j)
    (hI:I∈stopped C o f j) : @CutOK b u del M Γ F j I (cutBook h2 hb x j I) := by
  have hm:=stopped_mem hI
  have h:j∈stops b∧0<j∧xN I ∧ ¬ Pass x j I :=
    ⟨hj,hp,(C.DN o ho f hf I hm.1).1,hm.2.1⟩
  rw [cutBook,dite_eq_left h]
  exact Classical.choose_spec (h2 b hb u del M Γ F x j h.1 h.2.1 I h.2.2.1 h.2.2.2)
abbrev positiveStops (b:fO) :=(stops b).filter (0 < ·)
private theorem projection_reindex (b:fO) (v :ℕ→ℚ) :
    (∑ j∈positiveStops b,v j) = ∑ i∈range (stopCount b-1),v (i+1) := by
  let e :ℕ ↪ ℕ:=⟨Nat.succ,Nat.succ_injective⟩
  have he : (range (stopCount b-1)).map e=positiveStops b:= by
    ext j
    simp only [e,mem_map,Function.Embedding.coeFn_mk,mem_range,mem_filter,stops]
    exact ⟨fun ⟨i,hi,h⟩=> by omega,fun hj=>⟨j-1,by omega,by omega⟩⟩
  rw [← he,sum_map]
  rfl
private def pointWeightNat (b:fO) :Fin 4→ℕ :=
  ![0,0,((pointShapes b).map Shape.U).foldl max 0,
    ((pointShapes b).map (fun s=>s.B-s.J)).foldl max 0+((pointShapes b).map Shape.J).foldl max 0]
private def pointWeight (b:fO) :GM:= fun k=>pointWeightNat b k
private theorem point_weight (hj:0<j) (k :Fin 4) :SS b j 2 k≤pointWeight b k := by
  obtain ⟨_,hu,hB⟩:=cut_shape_bounds (b:=b) hj
  fin_cases k
  · exact le_rfl
  · exact le_rfl
  · exact (Nat.cast_le (α:=ℚ)).mpr hu
  · exact (Nat.cast_le (α:=ℚ)).mpr hB
section
variable (h2 :c2) (hb:2≤b.val) (C)
private theorem total_projection :
    (∑ o∈origins b,∑ f∈C.factors o,∑ j∈positiveStops b,
      ∑ I∈stopped C o f j,((cutBook h2 hb x j I).cost 0:ℚ))≤projectionCap b:= by
  let jX j:=SS b j 0
  calc
    _ ≤ ∑ o∈origins b,∑ f∈C.factors o,∑ j∈positiveStops b,
        FP (jX j) (J2 (stopped C o f j)) := by
      refine sum_le_sum fun o ho=>sum_le_sum fun f hf=>sum_le_sum fun j hj => ?_
      rw [← dot_mass]
      exact sum_le_sum fun I hI=>(cutBook_ok h2 hb ho hf (mem_filter.mp hj).1 (mem_filter.mp hj).2 hI).cost 0
    _ = ∑ j∈positiveStops b,FP (jX j) (J2 (globalLost C j)) := by
      have hs (o:ℕ) :
          (∑ f∈C.factors o,∑ j∈positiveStops b,FP (jX j) (J2 (stopped C o f j))) =
          ∑ j∈positiveStops b,∑ f∈C.factors o,FP (jX j) (J2 (stopped C o f j)) :=sum_comm
      simp only [hs]
      rw [sum_comm (s :=origins b) (t:=positiveStops b)]
      apply sum_congr rfl
      intro j _
      simp only [crE]
      apply congrArg (FP (jX j))
      funext k
      exact (global_lost_mass C j k).symm
    _≤_:= by
      rw [projection_reindex]
      exact bBx (stopCount b-1) (fun i=>jX (i+1)) (fun i=>globalCap b (i+1))
        (fun i=>globalLive C (i+1)) (fun i=>globalLost C (i+1))
        (fun i _=>global_live_anti C (Nat.le_succ (i+1)))
        (fun i _=>global_lost_sdiff C (i+1)) (fun i _=>global_cap C (i+1))
private theorem total_points :
    (∑ o∈origins b,∑ f∈C.factors o,∑ j∈positiveStops b,
      ∑ I∈stopped C o f j,(cutBook h2 hb x j I).direct.card)≤pointFee b:= by
  apply (Nat.cast_le (α:=ℚ)).mp
  push_cast
  let w:=pointWeight b
  calc
    _ ≤ ∑ o∈origins b,∑ f∈C.factors o,∑ j∈positiveStops b,
        FP w (J2 (stopped C o f j)) := by
      refine sum_le_sum fun o ho=>sum_le_sum fun f hf=>sum_le_sum fun j hj => ?_
      have hp:=(mem_filter.mp hj).2
      rw [← dot_mass]
      refine sum_le_sum fun I hI=>((cutBook_ok h2 hb ho hf (mem_filter.mp hj).1 hp hI).cost 2).trans ?_
      exact dYl (fun k=>Nat.cast_nonneg (pN I k)) (point_weight hp)
    _=FP w (fun k => ∑ o∈origins b,∑ f∈C.factors o,∑ j∈positiveStops b,
          J2 (stopped C o f j) k) := by simp only [crE]
    _≤FP w (fun k=>BC b k) := by
      apply a3x
      · exact fun k=>Nat.cast_nonneg (pointWeightNat b k)
      · intro k
        refine (sum_le_sum fun o _=>sum_le_sum fun f _ => ?_).trans (C.mass_cap k)
        simpa only [live_zero] using sum_stopped_le C o f (positiveStops b) (fun j _=>Nat.zero_le j) k
    _=(pointFee b:ℚ) := by
      let a :=((pointShapes b).map Shape.U).foldl max 0
      let d:=((pointShapes b).map (fun s=>s.B-s.J)).foldl max 0 +
        ((pointShapes b).map Shape.J).foldl max 0
      rw [FP,Fin.sum_univ_four]
      change (0:ℚ)*BC b 0+0*BC b 1+(a :ℚ)*BC b 2 +
        (d:ℚ)*BC b 3=((a*BC b 2+d*BC b 3:ℕ) :ℚ)
      simp only [zero_mul,zero_add,Nat.cast_add,Nat.cast_mul]
end
private theorem individual_of (h1 :c1) (hb:2≤b.val) {o f j I} (ho:o∈origins b)
    (hf :f∈C.factors o) (hj:j∈stops b) (hI:I∈stopped C o f j) :
    Individual b o j fun k=>pN I k := by
  have hl:=(mem_filter.mp hI).1
  have hm:=live_mem hl
  have ha :=(C.DN o ho f hf I hm.1).1
  refine ⟨(Nat.cast_pos (α:=ℚ)).mpr ha.seed_size.1,fun k=>⟨Nat.cast_nonneg _,le_min ?_ ?_⟩,?_⟩
  · have hg:I∈globalLive C j:=(dNW C).mpr ⟨o,ho,f,hf,hl⟩
    have hsingle : ({I} : Finset _)⊆globalLive C j:=singleton_subset_iff.mpr hg
    have h:=(bfw hsingle k).trans (global_cap C j k)
    simpa [J2,pI.mass] using h
  · exact (h1 b hb u del M Γ F x C o ho).1 f hf j hj I hl k
  · exact fun n hn=>moving_fit C ho hf hl hn
private theorem timeline (C:aAT F b x) (h1 :c1) (h2 :c2) (hb:2≤b.val) :
    Nonempty (Timeline C) := by
  refine ⟨{
    stopped :=stopped C
    Bp:= fun o f=>QV C o f (stopCount b)
    cuts := fun _ _=>cutBook h2 hb x
    stopped_at := fun _ _ _ _ _ _ _ h=>stopped_mem h
    kept_at := ?_
    exhaust:= fun _ _ _ _ _ h=>qkrKkqa.exhaust C h
    aNI := ?_
    global_bound:= fun i _ k=>qkrKkqa.global_bound C i k
    free_bound:= fun o ho k=>(lossTail_le C o _ k).trans ((h1 b hb u del M Γ F x C o ho).2 k)
    individual:= fun _ ho _ hf _ hj _ hI=>individual_of (C:=C) h1 hb ho hf hj hI
    cut_cost:= fun _ ho _ hf _ hj hp _ hI=>(cutBook_ok (C:=C) h2 hb ho hf hj hp hI).cost
    cut_cover := fun _ ho _ hf _ hj hp _ hI=>(cutBook_ok (C:=C) h2 hb ho hf hj hp hI).Eh
    total_projection :=total_projection C h2 hb
    total_points :=total_points C h2 hb }⟩
  · intro o _ f _ I hI
    have hpos :0<stopCount b:= by unfold stopCount; omega
    exact ⟨(live_mem hI).1,live_dual C hI hpos,terminal_pass.mp
      ((live_mem hI).2 _ (by omega :stopCount b-1<stopCount b))⟩
  · intro o ho f hf k
    refine (sum_stopped_le C o f (stops b) (fun j _=>Nat.zero_le j) k).trans ?_
    rw [live_zero]
    exact C.factor_cap o ho f hf k
theorem of_children (h1 :c1) (h2 :c2) :q6nKpZc.c3 :=
  fun b hb u del M Γ F x C => @timeline b u del M Γ F x C h1 h2 hb
end
end qkrKkqa
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q4V2ihd
noncomputable section
open P6 (K p jG)
open P5_7_2 (A fO Window)
open q7F2qKe (wX weakAgreement)
open qxRSHvb (gap linearRate persistentRate)
open cu (L)
open DQ (Ag)
open axI (c7Q)
open private OF.distinct OF.degree OF.lg q9NbxKa.rho aaM gAN from ProximityPrize.SubmissionLower.ZogIzOe
open private ceY band_degrees from ProximityPrize.SubmissionLower.ZRqikKa
open private bd0 from ProximityPrize.SubmissionLower.ZqKag5d
open private cK1 cK2 cK3 from ProximityPrize.SubmissionLower.CR
open Finset Polynomial
open scoped Classical
private theorem degree_max (b:fO) :wX b≤133774 :=
  Nat.add_le_add_left (band_degrees b).2 131071
theorem persistent {b:fO} {u del} {M:jG u del} {Γ}
    {F:P1.bje A M Γ} (hw:Window b M.iF) {T J Q g H}
    (hg:0<g) (hm:DescendedMarks F T J Q g H) :
    (T.card:ℚ)≤persistentRate b g*H+g:= by
  have hgp:g<p:=(Nat.le_mul_of_pos_left g hm.plane_pos).trans_lt hm.seed_lt
  obtain ⟨U,hU,hexc,n,⟨bY⟩⟩:=c7Q T M.label F.scalar J g H hg hgp
    hm.curve (fun _ _ _ _ h=>sub_left_inj.mp h) hm.marks
  have hword:=bd0 F hw (hU.trans hm.subset)
  have hreg:=ceY bY hword hg (Nat.le_add_right _ _) (degree_max b)
  have hgQ: (1 :ℚ)≤g:= by exact_mod_cast hg
  have hexcQ: ((T \ U).card:ℚ)≤(Ag g:ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card:ℚ)=((T \ U).card:ℚ)+(U.card:ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _≤(Ag g:ℚ)*H +
        ((2*aaM*wX b*(Ag g:ℚ)+q9NbxKa.rho (wX b))*H+1) :=
      add_le_add hexcQ hreg
    _≤_:=add_le_add le_rfl (add_le_add le_rfl hgQ)
    _=persistentRate b g*H+g:= by
      rw [gAN hg]
      unfold persistentRate q9NbxKa.rho aaM gap
      ring
theorem linear {b:fO} {u del} {M:jG u del} {Γ} {F:P1.bje A M Γ}
    (hw:Window b M.iF) {T J Q H} (hm:DescendedMarks F T J Q 1 H) :
    (T.card:ℚ)≤linearRate b*H+1 := by
  have hf :=bd0 F hw hm.subset
  have hd:wX b≤qWdRihc.d:=degree_max b
  have hz :Set.InjOn M.label (T:Set K) := fun _ _ _ _ e=>sub_left_inj.mp e
  let W:qWdRihc.UJ :=
    ⟨T,algebraMap K L ∘ M.label,F.scalar,M.word,
      fun _ hγ _ hη e=>hz hγ hη ((algebraMap K L).injective e),
      OF.distinct hf,fun γ hγ=>(OF.degree hf γ hγ).trans hd,
      OF.lg hf⟩
  obtain ⟨hJ,C₀,hC₀,hseed,hsf,hs,hyf,hy⟩:=hm.curve
  let:Fact (Irreducible C₀) :=⟨hC₀⟩
  obtain ⟨R⟩:=cK1 C₀ J 1 hJ hseed hsf hs Nat.one_pos
  obtain ⟨n,B,t,hbase,_,hroots⟩:=cK2 C₀ J 1 R T M.label F.scalar hm.marks
  have hh:=cK3 C₀ J 1 H n R B Nat.one_pos hyf hy
  have hsite :qWdRihc.asT W T H := by
    intro i
    have he :T.filter (fun γ=>W.hit γ i) =
        T.filter (fun γ=>P5_7_7.hit M.word F.scalar γ i) :=
      filter_congr (fun _ _=>Iff.rfl)
    have hn:T.filter (fun γ => ¬ W.hit γ i) =
        T.filter (fun γ => ¬ P5_7_7.hit M.word F.scalar γ i) :=
      filter_congr (fun _ _=>Iff.rfl)
    rw [he,hn]
    exact qo38hre.sections B hh hz hbase hroots M.word i
  have hc: (T.card:ℚ)≤6*H+1 := by
    exact_mod_cast qWdRihc.exceptional_count W T (Subset.rfl :T⊆T) H hsite
  have hg: (0:ℚ)<(gap b:ℚ) :=Nat.cast_pos.mpr
    (Nat.sub_pos_of_lt (hd.trans_lt (by decide :qWdRihc.d<weakAgreement)))
  have hsmall:gap b≤48669:=Nat.sub_le_sub_left (Nat.le_add_right _ _) weakAgreement
  have hratio: (5:ℚ)≤3*262144/(gap b:ℚ) := by
    apply (le_div_iff₀ hg).mpr
    exact_mod_cast (show 5*gap b≤3*262144 by omega)
  have hr : (6:ℚ)≤linearRate b:= calc
    (6:ℚ)=1+5:= by norm_num
    _≤_:=add_le_add le_rfl hratio
  exact hc.trans (add_le_add (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg H)) le_rfl)
end
end q4V2ihd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q4V2ihd
noncomputable section
open P6 (p jG)
open P5_7_2 (A fO)
open q6nKpZc (Input I0 aHl)
open q7F2qKe (aSz scalarWitness)
open qxRSHvb (quadraticRate nativeSlope)
open cu (qD)
open gT (Ambient)
open pI (by6)
open YY (bAG xg Si by9 aef a9E)
open private cag c2p c0U ddj b1I diE from ProximityPrize.SubmissionLower.G
open private mix mix_zero from ProximityPrize.SubmissionLower.ZzWMDba
open Finset
open scoped Classical
def c1 :Prop :=
  ∀ {b:fO} {u del} {M:jG u del} {Γ} {F:P1.bje A M Γ},
    2≤b.val→ Input b M F → ∀ {T J Q H},DescendedMarks F T J Q 2 H →
    (T.card:ℚ)≤16*(2*(Q.totalDegree :ℚ))+quadraticRate b*H+2
def c2 :Prop :=
  ∀ {b:fO} {u del} {M:jG u del} {Γ} {F:P1.bje A M Γ},
    2≤b.val→ Input b M F → ∀ {T J Q g H},DescendedMarks F T J Q g H →
    3≤g→ g≤54 → ∀ v :ℚ,scalarWitness b g false v →
    (T.card:ℚ)≤nativeSlope Q.totalDegree g false*((g:ℚ)*Q.totalDegree)+v*H+g
def c3:Prop :=
  ∀ {b:fO} {u del} {M:jG u del} {Γ} {F:P1.bje A M Γ},
    2≤b.val→ Input b M F → ∀ {T J Q g H},DescendedMarks F T J Q g H →
    3≤g→ g≤54 → ∀ v :ℚ,scalarWitness b g true v →
    (T.card:ℚ)≤nativeSlope Q.totalDegree g true*((g:ℚ)*Q.totalDegree)+v*H+g
private abbrev graphRate (g:ℕ) :ℚ:=((p+1 :ℕ) :ℚ)/g
private theorem sixteen_le : (16:ℚ)≤graphRate 55:= by
  apply (le_div_iff₀ (by norm_num : (0:ℚ)<(55:ℕ))).mpr
  exact_mod_cast (by decide :16*55≤p+1)
private theorem rated_descended (h1 :c1) (h2 :c2) (h3:c3)
    {b u del M Γ F} (hb:2≤b.val) (x : @Input b u del M Γ F) {T J Q g H}
    (hm:DescendedMarks F T J Q g H) (hg:0<g)
    {dm a h:ℚ} (rate :aSz b dm a h) (hd: (Q.totalDegree :ℚ)≤dm)
    (direct : (T.card:ℚ)≤((p+1 :ℕ) :ℚ)*Q.totalDegree) :
    (T.card:ℚ)≤a*((g:ℚ)*Q.totalDegree)+h*H+g:= by
  have ha :0≤a :=rate.1.trans rate.2.1
  have hgQ:0<(g:ℚ) :=Nat.cast_pos.mpr hg
  have hH : (0:ℚ)≤H :=Nat.cast_nonneg _
  have hmass :0≤(g:ℚ)*Q.totalDegree :=mul_nonneg hgQ.le (Nat.cast_nonneg _)
  have hdir : (T.card:ℚ)≤graphRate g*((g:ℚ)*Q.totalDegree) := by
    rw [← mul_assoc,graphRate,div_mul_cancel₀ _ hgQ.ne']
    exact direct
  by_cases hl:a<graphRate g
  · have hgsmall:g≤54 := by
      by_contra! hn
      have hgn: (55:ℚ)≤g:= by exact_mod_cast Nat.succ_le_of_lt hn
      have hr :graphRate g≤graphRate 55 :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) hgn
      exact (not_lt_of_ge (hr.trans rate.2.2.1)) hl
    rcases rate.2.2.2.2 g hg hgsmall hl with hr | ⟨rfl,hr⟩ | ⟨rfl,hr⟩ | ⟨hg3,k,v,h0,hw,hr⟩
    · exact mix_zero ha hl hH hgQ.le hdir (persistent x.vo hg hm) hr
    · exact mix_zero ha hl hH hgQ.le hdir (linear x.vo hm) hr
    · exact mix (sixteen_le.trans rate.2.2.1) hl hH hgQ.le hdir (h1 hb x hm) hr
    · have hs :nativeSlope Q.totalDegree g k≤nativeSlope dm g k := by
        unfold nativeSlope
        gcongr
      have hc: (T.card:ℚ) ≤
          nativeSlope Q.totalDegree g k*((g:ℚ)*Q.totalDegree)+v*H+g:= by
        cases k
        · exact h2 hb x hm hg3 hgsmall v hw
        · exact h3 hb x hm hg3 hgsmall v hw
      have hc' := hc.trans (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_right hs hmass) le_rfl) le_rfl)
      exact mix h0 hl hH hgQ.le hdir hc' hr
  · exact hdir.trans ((mul_le_mul_of_nonneg_right (le_of_not_gt hl) hmass).trans
      ((le_add_of_nonneg_right (mul_nonneg rate.2.2.2.1 hH)).trans
        (le_add_of_nonneg_right hgQ.le)))
private theorem ePj:YY.c2 :=
  aBb.of_children czq.proof bzX.proof
private theorem fTy (h1 :c1) (h2 :c2) (h3:c3)
    {b u del M Γ F} (hb:2≤b.val) (x : @Input b u del M Γ F) {I:Ideal Ambient}
    (geom:by6 I) {dm a h:ℚ} (rate :aSz b dm a h)
    (hdm: (aef I:ℚ)≤dm) (hp:aef I<p) :
    ((Γ.filter (I0 F I)).card:ℚ)≤a*aef I+h*a9E I+aef I:= by
  let T:=Γ.filter (I0 F I)
  have ha :0≤a :=rate.1.trans rate.2.1
  have slice :bAG I:=⟨geom.1,geom.2.1,geom.2.2.1,geom.2.2.2.1⟩
  obtain ⟨f,hf,he,hpos,hd⟩:=GK.proof I slice
  have hdQ: (f.totalDegree :ℚ)≤aef I:=Nat.cast_le.mpr hd
  have hlabels : ∀ z∈T.image M.label,qD z f=0:= by
    intro z hz
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hz
    apply c2p (mem_filter.mp hγ).2
    rw [he]
    exact Ideal.mem_span_singleton_self f
  have hcard: (T.image M.label).card=T.card :=
    card_image_of_injective _ (fun _ _ hab=>sub_left_inj.mp hab)
  by_cases hconst:by9 (xg I)
  · obtain ⟨Q,hQ,hIQ⟩:=hconst
    have hdeg:=b1I f hf.ne_zero Q (he.symm.trans hIQ)
    obtain ⟨g,hg,hroot,hmass⟩:=ePj I Q slice geom.2.2.2.2 hQ hIQ
    have hmarks :DescendedMarks F T (Si I) Q g (a9E I) :=
      ⟨filter_subset _ _,hroot,hQ,hIQ,hdeg ▸ hpos,hmass.trans_lt hp,
        fun _ hz=>cag (mem_filter.mp hz).2⟩
    have hdir :=ddj f hf.ne_zero (hd.trans_lt hp) (T.image M.label) hlabels
    rw [hcard,hdeg] at hdir
    have htotal:=rated_descended h1 h2 h3 hb x hmarks hg rate
      ((show (Q.totalDegree :ℚ)≤aef I from hdeg ▸ hdQ).trans hdm) (by exact_mod_cast hdir)
    have hmassQ: (g:ℚ)*Q.totalDegree≤aef I:= by
      rw [mul_comm]
      exact_mod_cast hmass
    have hgQ: (g:ℚ)≤aef I :=
      Nat.cast_le.mpr ((Nat.le_mul_of_pos_left g hmarks.plane_pos).trans hmass)
    exact htotal.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hmassQ ha) le_rfl) hgQ)
  · have hm:=c0U p f hf (he ▸ hconst) (T.image M.label) hlabels
    rw [hcard] at hm
    have hq: (T.card:ℚ)≤(f.totalDegree :ℚ)^2 := by exact_mod_cast hm
    calc
      _≤(f.totalDegree :ℚ)^2 :=hq
      _≤a*(aef I:ℚ) := by
        rw [pow_two]
        exact mul_le_mul ((hdQ.trans hdm).trans rate.2.1) hdQ (Nat.cast_nonneg _) ha
      _≤_:=(le_add_of_nonneg_right (mul_nonneg rate.2.2.2.1 (Nat.cast_nonneg _))).trans
        (le_add_of_nonneg_right (Nat.cast_nonneg _))
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :q6nKpZc.c4 := by
  intro b hb u del M Γ F x dm a h rate C hdm hp
  have hmarks :aHl F C=C.qv.biUnion (fun I=>Γ.filter (I0 F I)) := by
    ext γ
    simp only [aHl,mem_filter,mem_biUnion]
    exact ⟨fun ⟨hγ,I,hI,hm⟩=>⟨I,hI,hγ,hm⟩,
      fun ⟨I,hI,hγ,hm⟩=>⟨hγ,I,hI,hm⟩⟩
  have hsum : ∑ I∈C.qv,aef I=C.cost 0:=rfl
  have hsumH : ∑ I∈C.qv,a9E I=C.cost 1 :=rfl
  rw [hmarks]
  calc
    _ ≤ ∑ I∈C.qv,((Γ.filter (I0 F I)).card:ℚ) :=diE _ _
    _ ≤ ∑ I∈C.qv,(a*(aef I:ℚ)+h*(a9E I:ℚ)+aef I) := by
      apply sum_le_sum
      intro I hI
      have hD:aef I≤C.cost 0 :=
        hsum ▸ single_le_sum (fun _ _=>Nat.zero_le _) hI
      exact fTy h1 h2 h3 hb x (C.geometric I hI) rate
        ((Nat.cast_le.mpr hD).trans hdm) (hD.trans_lt hp)
    _ = _:= by simp only [sum_add_distrib,← mul_sum,← Nat.cast_sum,hsum,hsumH]
end
end q4V2ihd
end
