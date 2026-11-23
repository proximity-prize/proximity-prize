import ProximityPrize.SubmissionLower.Z67mtTa
import ProximityPrize.SubmissionLower.ZPoi06c
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qUrGXob
noncomputable section
open Finset Polynomial
open P6 (dw)
open P5_7_1 (Ls)
open qehP9ee (a3D)
open private bKS from ProximityPrize.SubmissionLower.ZPoi06c
open P6_7_3 (Input Poles Picks afa OriginCover cutoff terminal necessary)
open cu (vP Jet Shape rD)
open DP (d3r)
open gT (Ambient iJ aNB)
open pI (xN dual mass pN acW)
open qQ (oU)
open TD (J2)
open scoped Classical BigOperators
private theorem stage_guards (i:afa) :
    (stage i).free.J≤(stage i).free.B∧(stage i).moving.J≤(stage i).moving.B ∧
    0<(stage i).free.m*dw∧0<(stage i).moving.m*dw ∧
    0<(stage i).moving.J:= by
  fin_cases i <;> decide
private theorem d1m {s :Ls} {G:Jet} (hj:s.free.J≤ s.free.B)
    (hk :s.moving.J≤ s.moving.B)
    (hc:oU G s.free∨oU G s.moving) :oU G (a3D s) := by
  have hB:s.free.B≤(a3D s).B :=
    (Nat.sub_add_cancel hj).symm.trans_le
      (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))
  have hC:s.moving.B≤(a3D s).B :=
    (Nat.sub_add_cancel hk).symm.trans_le
      (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))
  intro j i hi
  rcases hc with h | h
  · obtain ⟨h₁,h₂,h₃⟩:=h j i hi
    exact ⟨h₁.trans hB,h₂.trans (le_max_left _ _),h₃.trans (le_max_left _ _)⟩
  · obtain ⟨h₁,h₂,h₃⟩:=h j i hi
    exact ⟨h₁.trans hC,h₂.trans (le_max_right _ _),h₃.trans (le_max_right _ _)⟩
private theorem b2N {x :Input} (P:Poles x) {s :Shape} {I:Ideal Ambient}
    (hs :0<s.m*dw) (h : ¬ inBank P.rows s I) :
    ∃ G:Jet,oU G s∧iJ G∉I ∧
      ∀ γ∈x.Γ,rD G (x.M.label γ) (x.F.scalar γ)=0:= by
  unfold inBank at h
  push Not at h
  obtain ⟨G,hG,hproper⟩:=h
  have hw:cutoff s<s.m*dw:= by unfold cutoff; omega
  exact ⟨G,d3r P.crt x.word hG,hproper,fun _ hγ=>necessary P hw hG hγ⟩
private theorem trial_cutter {x :Input} (P:Poles x) (pick :Picks x.h P.rows)
    (t:Trial) {I:Ideal Ambient} (hf : ¬ passes pick t I) :
    ∃ G:Jet,oU G (aHp t)∧iJ G∉I ∧
      ∀ γ∈x.Γ,onMark x I γ→ rD G (x.M.label γ) (x.F.scalar γ)=0:= by
  cases ht:trialKind t with
  | free i =>
    simp only [passes,ht] at hf
    obtain ⟨G,hc,hp,hz⟩:=b2N P (stage_guards i).2.2.1 hf
    rw [aHp,ht]
    exact ⟨G,hc,hp,fun _ hγ _=>hz _ hγ⟩
  | terminal =>
    simp only [passes,ht] at hf
    obtain ⟨G,hc,hp,hz⟩:=b2N P (s :=terminal) (by decide) hf
    rw [aHp,ht]
    exact ⟨G,hc,hp,fun _ hγ _=>hz _ hγ⟩
  | moving i =>
    simp only [passes,ht] at hf
    rw [aHp,ht]
    obtain ⟨hj,hk,hm,hn,hpos⟩:=stage_guards i
    by_cases hP:inBank P.rows (stage i).free I
    · by_cases hQ:inBank P.rows (stage i).moving I
      · have h : ¬ aFX.aTw (pick.main i).free (pick.main i).moving I :=
          fun hc=>hf ⟨hP,hQ,hc⟩
        unfold aFX.aTw at h
        push Not at h
        obtain ⟨f,_,_,_,hdiv,hmem,g,a,hclear,hproper⟩:=h
        have hc:=YZ.bWO (pick.main i).moving_ne
          (d3r P.crt x.word (pick.main i).moving_mem) hpos hdiv hclear
        refine ⟨YZ.alD g,d1m hj hk (Or.inr hc),hproper,?_⟩
        intro γ _ hγ
        apply YZ.bWP hclear
        have hz :=RingHom.mem_ker.mp (hγ hmem)
        simpa only [aNB,rD,eval₂_C,coe_eval₂RingHom,cu.yq] using hz
      · obtain ⟨G,hc,hp,hz⟩:=b2N P hn hQ
        exact ⟨G,d1m hj hk (Or.inr hc),hp,fun _ hγ _=>hz _ hγ⟩
    · obtain ⟨G,hc,hp,hz⟩:=b2N P hm hP
      exact ⟨G,d1m hj hk (Or.inl hc),hp,fun _ hγ _=>hz _ hγ⟩
theorem cut_at_failure {x :Input} (P:Poles x) (pick :Picks x.h P.rows)
    (t:Trial) {I:Ideal Ambient} (ha :xN I) (hf : ¬ passes pick t I) :
    ∃ C:acW,(∀ j,(C.cost j:ℚ)≤TD.FP (SS j t)
      (fun k=>pN I k)) ∧
      ∀ γ∈x.Γ,onMark x I γ→γ∈C.direct∨γ∈onCurves x C:= by
  have hj: (aHp t).J≤(aHp t).B:= by
    cases ht:trialKind t with
    | free i=>simpa only [aHp,ht] using (stage_guards i).1
    | moving i=>simpa only [aHp,ht,a3D] using
        (Nat.le_add_left _ _:max (stage i).free.J (stage i).moving.J≤_)
    | terminal=>rw [aHp,ht]; decide
  obtain ⟨G,hG,hp,hz⟩:=trial_cutter P pick t hf
  let F:=P6_7.weakenFamily x.F (show P5_7.farAgreement≤dw by decide)
  obtain ⟨C,hC,hcover⟩:=bKS F (aHp t) hj ha hG hp
  refine ⟨C,fun j => ?_,fun γ hγ hn => ?_⟩
  · simpa only [TD.FP,pI.dot,SS,Nat.cast_sum,Nat.cast_mul] using
      (Nat.cast_le (α:=ℚ)).mpr (hC j)
  · rcases hcover γ hγ hn (hz γ hγ hn) with h | ⟨Q,hQ,hon⟩
    · exact Or.inl h
    · exact Or.inr (mem_filter.mpr ⟨hγ,Q,hQ,hon⟩)
def chooseFixed {x :Input} (P:Poles x) (pick :Picks x.h P.rows) :
    bQX pick :=
  ⟨fun i=>Classical.choice (bRI.proof _ _ (pick.main i).free_ne
      (d3r P.crt x.word (pick.main i).free_mem)),
    fun i=>Classical.choice (bRI.proof _ _ (pick.main i).moving_ne
      (d3r P.crt x.word (pick.main i).moving_mem))⟩
variable {x :Input} {rows :vP} {pick :Picks x.h rows}
  (R:bQX pick) {anchorRow :Jet} (O:OriginCover x anchorRow) {f :Jet}
theorem stopped_zero :
    stopped R O f 0=(QV R O f 0).filter (fun I => ¬ dual I) :=rfl
theorem stopped_succ (t:Trial) :
    stopped R O f t.succ=(QV R O f t.succ).filter (fun I => ¬ passes pick t I) :=rfl
theorem stopped_sub (s :bAL) :stopped R O f s⊆QV R O f s := by
  induction s using Fin.cases with
  | zero=>rw [stopped_zero]; exact filter_subset _ _
  | succ t=>rw [stopped_succ]; exact filter_subset _ _
private theorem live_anti {s s' : bAL} (h:s≤ s') :QV R O f s' ⊆ QV R O f s := by
  intro I hI
  obtain ⟨hp,hc,hd,ht⟩:=mem_filter.mp hI
  have hh:s.val≤ s'.val :=h
  exact mem_filter.mpr ⟨hp,hc,fun h₀=>hd (by omega),fun t h₀=>ht t (by omega)⟩
private theorem earlier_disjoint {s s' : bAL} (h:s<s') :
    Disjoint (stopped R O f s) (stopped R O f s') := by
  have hh:s.val<s'.val :=h
  apply disjoint_left.mpr
  intro I hi hj
  obtain ⟨_,_,hd,ht⟩:=mem_filter.mp (stopped_sub R O s' hj)
  induction s using Fin.cases with
  | zero =>
    rw [stopped_zero] at hi
    exact (mem_filter.mp hi).2 (hd (by omega))
  | succ t =>
    rw [stopped_succ] at hi
    exact (mem_filter.mp hi).2 (ht t (by simpa only [Fin.val_succ] using hh))
theorem tail_mass (s :bAL) (k :Fin 4) :
    (∑ j:bAL,if s≤j then J2 (stopped R O f j) k else 0)≤J2 (QV R O f s) k := by
  rw [← sum_filter]
  let A:Finset bAL:=univ.filter fun j=>s≤j
  have hd: (A:Set bAL).PairwiseDisjoint (stopped R O f) := by
    intro i _ j _ hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact earlier_disjoint R O h
    · exact (earlier_disjoint R O h).symm
  have hu:A.biUnion (stopped R O f)⊆QV R O f s := by
    intro I hI
    obtain ⟨j,hj,hIj⟩:=mem_biUnion.mp hI
    exact live_anti R O (mem_filter.mp hj).2 (stopped_sub R O j hIj)
  have hb:=TD.bfw hu k
  simp only [J2,mass,Nat.cast_sum,sum_biUnion hd] at hb
  simpa only [J2,mass,Nat.cast_sum] using hb
theorem placed {I:Ideal Ambient} (hI:I∈O.parents f) (hc:clean R I) :
    (∃ s,I∈stopped R O f s)∨I∈final R O f := by
  by_cases hd:dual I
  · by_cases h : ∃ t:Trial,¬ passes pick t I
    · have hn : ∃ n,∃ t:Trial,t.val=n ∧ ¬ passes pick t I:= by
        obtain ⟨j,hj⟩:=h
        exact ⟨j.val,j,rfl,hj⟩
      obtain ⟨t,ht,hfail⟩:=Nat.find_spec hn
      left
      refine ⟨t.succ,?_⟩
      rw [stopped_succ]
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨hI,hc,fun _=>hd,?_⟩,hfail⟩
      intro j hj
      by_contra hbad
      exact Nat.find_min hn (by simpa only [Fin.val_succ,Nat.add_lt_add_iff_right,ht] using hj)
        ⟨j,rfl,hbad⟩
    · right
      exact mem_filter.mpr ⟨hI,hc,hd,fun t=>by_contra fun ht=>h ⟨t,ht⟩⟩
  · left
    refine ⟨0,?_⟩
    rw [stopped_zero]
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hI,hc,fun h=>(Nat.not_lt_zero _ h).elim,
      fun _ h=>(Nat.not_lt_zero _ h).elim⟩,hd⟩
def Az (G:Geometry R O) :aAU where
  factors :=O.factors
  origin :=O.origin
  line :=O.line
  stops f s :=J2 (stopped R O f s)
  nonneg _ _ _ _:=Nat.cast_nonneg _
  spend_order :=G.spend_order
  line_ok f hf hl:=⟨G.line_ok f hf hl,O.line_pos f hf hl⟩
  nested i j:=O.nested i.val (Nat.le_of_lt_succ i.isLt) j
  initial :=G.initial
  V8 s k :=(sum_le_sum fun _ _=>tail_mass R O s k).trans (G.V8 s k)
  prefree o k :=(sum_le_sum fun _ _=>tail_mass R O moveStart k).trans (G.prefree o k)
end
end qUrGXob
