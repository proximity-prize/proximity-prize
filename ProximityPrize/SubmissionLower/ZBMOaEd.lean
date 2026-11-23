import ProximityPrize.SubmissionLower.ZTipoSd
import ProximityPrize.SubmissionLower.ZTbQzvb
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace qkrKkqa
noncomputable section
open Finset
open scoped BigOperators Classical
open P6 (p)
open P6_7_4 (wordLift)
open q6nKpZc
open P5_7_2 (Ls ChosenRow stages movingOrder terminal anM O2)
open q7F2qKe (agA chosen_mem nV afterFree stopCount origins partMass lossTail globalCap MovingFit)
open q7F2qKe (kK)
open q3soobb (shapes_ok selected_ok cqz after_free_pos)
open cu (Shape)
open DP (d3q d3r)
open gT (Ambient aQ iJ)
open pI (xN dual O9 pN)
open ac2
open aFX (aTw)
open TD (J2 bfw bCb auN arC)
open private dfc ddV from ProximityPrize.SubmissionLower.U
variable {b u del M Γ F} {x : @Input b u del M Γ F}
theorem moving_before {j n:ℕ} (h:n∈(movingOrder b).take (j-afterFree b)) :
    ∃ t,afterFree b+t<j∧(movingOrder b)[t]? = some n:= by
  obtain ⟨t,ht⟩:=List.mem_iff_getElem?.mp h
  have hl:=(List.getElem?_eq_some_iff.mp ht).choose
  rw [List.length_take] at hl
  have hlt:=hl.trans_le (Nat.min_le_left _ _)
  exact ⟨t,by omega,(List.getElem?_take_of_lt hlt).symm.trans ht⟩
theorem terminal_pass {b u del M Γ F} {x : @Input b u del M Γ F}
    {I:Ideal gT.Ambient} :
    Pass x (stopCount b - 1) I↔agA x.banks (terminal b).shape I:= by
  have hp:=after_free_pos b
  have he :stopCount b - 1=afterFree b+(movingOrder b).length:= by
    simp [stopCount]
  rw [he,Pass,ite_eq_right (by omega),ite_eq_right (by omega)]
  simp
theorem moving_pass {b u del M Γ F} {x : @Input b u del M Γ F} {t n I}
    (h: (movingOrder b)[t]? = some n) (hs :nV b n∈stages b) :
    Pass x (afterFree b+t) I↔agA x.banks (nV b n).free I ∧
      agA x.banks (nV b n).moving I ∧
      aTw (x.donors.staged _ hs).free.jet (x.donors.staged _ hs).moving.jet I:= by
  have hp:=after_free_pos b
  rw [Pass,ite_eq_right (by omega),ite_eq_right (by omega),
    show afterFree b+t-afterFree b=t by omega,h]
  exact ⟨fun ⟨_,hh⟩=>hh,fun hh=>⟨hs,hh⟩⟩
theorem chosen_order {r s} (R:ChosenRow x.crt (wordLift M) r s) {I:Ideal Ambient}
    (hr :r<p) (ha :xN I) (hd:dual I) (hv :agA x.banks s I) :
    O9 I R.jet (r+1) := by
  have hc:bp3 (I.map (Ih (algebraMap cu.aZ aQ)))
      (Ih (algebraMap cu.aZ aQ) (iJ R.jet)) r := by
    intro t ht
    rw [← dfc]
    apply Ideal.mem_map_of_mem
    apply hv
    have hs :qQ.bk4 M.iF.toNat x.banks s :=
      fun _ _ h i a=>atp.d3s x.crt (wordLift M) h i a
    apply d3q x.crt (wordLift M) rfl rfl rfl le_rfl _ (ddV hs (chosen_mem R) t)
    have hspend:=Nat.mul_le_mul_left (2*M.iF.toNat) ht
    have hroom:=R.cfw
    unfold anM O2
    omega
  rw [← aVL] at hc
  exact dLt hd (cy0.proof I ha.prime ha.jet_finite hd ha.jet_lt _ r hr hc)
variable (C:aAT F b x)
theorem live_dual {o f j I} (hI:I∈QV C o f j) (h:0<j) :dual I:= by
  have hp:=(live_mem hI).2 0 h
  rwa [Pass,ite_eq_left (show (0:ℕ)=0 from rfl)] at hp
abbrev globalLive (j:ℕ) :=combine C fun o f=>QV C o f j
abbrev globalLost (j:ℕ) :=combine C fun o f=>stopped C o f j
theorem global_live_anti {i j:ℕ} (h:i≤j) :globalLive C j⊆globalLive C i:= by
  intro I hI
  obtain ⟨o,ho,f,hf,hI⟩:=(dNW C).mp hI
  exact (dNW C).mpr ⟨o,ho,f,hf,live_anti h hI⟩
theorem global_lost_sdiff (j:ℕ) :globalLost C j⊆globalLive C j \ globalLive C (j+1) := by
  intro I hI
  obtain ⟨o,ho,f,hf,hI⟩:=(dNW C).mp hI
  refine mem_sdiff.mpr ⟨(dNW C).mpr ⟨o,ho,f,hf,(mem_filter.mp hI).1⟩,?_⟩
  intro h
  obtain ⟨v,hv,g,hg,h⟩:=(dNW C).mp h
  exact (stopped_mem hI).2.1 ((live_mem h).2 j (Nat.lt_succ_self j))
theorem global_live_mass (j:ℕ) (k :Fin 4) :
    J2 (globalLive C j) k = ∑ o∈origins b,partMass C.factors (QV C) o j k :=
  mass_combine C (fun _ _ _ _ _ h=>(live_mem h).1) k
theorem global_lost_mass (j:ℕ) (k :Fin 4) :
    J2 (globalLost C j) k = ∑ o∈origins b,partMass C.factors (stopped C) o j k :=
  mass_combine C (fun _ _ _ _ _ h=>(stopped_mem h).1) k
private theorem cap_fold {v :ℚ} {a :TD.GM} {L:List ℕ} {g:ℕ→TD.GM}
    {k :Fin 4} (ha :v≤a k) (hg : ∀ n∈L,v≤g n k) :
    v≤(L.foldl (fun a n=>bCb a (g n)) a) k := by
  induction L generalizing a with
  | nil=>exact ha
  | cons n L ih =>
    exact ih (le_min ha (hg n (List.mem_cons_self ..))) fun m hm=>hg m (List.mem_cons_of_mem _ hm)
theorem global_cap (j:ℕ) (k :Fin 4) :J2 (globalLive C j) k≤globalCap b j k := by
  apply cap_fold
  · rw [global_live_mass]
    refine le_trans (sum_le_sum fun o _=>sum_le_sum fun f _ => ?_) (C.mass_cap k)
    exact bfw (filter_subset _ _) k
  · intro n hn
    obtain ⟨t,ht,he⟩:=moving_before hn
    have hg:=selected_ok b n (List.mem_iff_getElem?.mpr ⟨_,he⟩)
    let s :=nV b n
    have hs :s∈stages b:=cqz hg.2.1
    let pair :=x.donors.staged s hs
    let fixed:=C.fixed s hs
    obtain ⟨ga,gb⟩:=shapes_ok b s hs
    exact aZC.proof s.free s.moving s.dI true pair.free.jet pair.moving.jet
      hg.2.2.1 hg.2.2.2 ga.2.2.2.1 gb.2.2.2.1 ga.2.2.2.2 gb.2.2.2.2 ga.2.2.1 gb.2.2.1
      pair.free.nonzero pair.moving.nonzero
      (d3r x.crt (wordLift M) (chosen_mem pair.free))
      (d3r x.crt (wordLift M) (chosen_mem pair.moving))
      pair.no_moving fixed.free fixed.moving (globalLive C j)
      (fun _ _ hI=> by
        obtain ⟨o,ho,f,hf,hI⟩:=(dNW C).mp hI
        exact live_dual C hI ((after_free_pos b).trans_le (by omega)))
      (fun _ hI=> by
        obtain ⟨o,ho,f,hf,hI⟩:=(dNW C).mp hI
        obtain ⟨hm,hp⟩:=live_mem hI
        have ⟨ha,_,_,_,hfixed⟩:=C.DN o ho f hf _ hm
        obtain ⟨hf,hg',hc⟩:=(moving_pass he hs).mp (hp _ ht)
        have hd:=live_dual C hI ((after_free_pos b).trans_le (by omega))
        exact ⟨ha,hc,(hfixed s hs).1,(hfixed s hs).2,
          chosen_order pair.free hg.2.2.2 ha hd hf,chosen_order pair.moving hg.2.2.2 ha hd hg'⟩) k
theorem global_bound (i:ℕ) (k :Fin 4) :
    (∑ o∈origins b,lossTail b C.factors (stopped C) o i k)≤globalCap b i k := by
  refine (sum_le_sum fun o _=>lossTail_le C o i k).trans ?_
  rw [← global_live_mass]
  exact global_cap C i k
private theorem mixed_cast (s t:Shape) (k :Fin 4) :
    qehP9ee.kK (P5_7_1.bgK s) t k =
      (kK (auN s) t k :ℚ) := by
  simp only [qehP9ee.kK,kK,Nat.cast_sum,Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm ((auN s j:ℕ) :ℚ) (arC t k j:ℚ)
private theorem moving_of_box (s :Ls) (v :Fin 4→ℕ)
    (hS:s.free.J≤ s.free.B) (hT:s.moving.J≤ s.moving.B)
    (h:qehP9ee.MovingBox ⟨s.dI,s.free,s.moving⟩ v) :
    MovingFit s fun k=>v k := by
  let m:=s.dI+1
  rcases h with h | ⟨n,e,u,hn,hm,he,hB,hU,hg,hr⟩
  · left
    intro k
    have hk :=h k
    change (v k :ℚ)≤qehP9ee.kK
      (P5_7_1.bgK (qehP9ee.aea s.free 0 0 0))
      (qehP9ee.aea s.moving 0 0 0) k/((m - 0:ℕ) :ℚ)^2 at hk
    simpa only [mixed_cast,qehP9ee.aea,Nat.zero_mul,Nat.sub_zero,
      min_eq_left hS,min_eq_left hT,Nat.cast_pow,m,kK,auN,arC] using hk
  · right
    refine ⟨n,e,u,hn,hm,he,hB,hU,fun k=>Nat.cast_le.mpr (hg k),?_⟩
    intro hlt k
    have hk :=hr hlt k
    change (v k :ℚ)≤qehP9ee.kK
      (P5_7_1.bgK (qehP9ee.aea s.free n e u))
      (qehP9ee.aea s.moving n e u) k/((m - n:ℕ) :ℚ)^2 at hk
    simpa only [mixed_cast,qehP9ee.aea,Nat.cast_pow,m] using hk
theorem moving_fit {o f j I n} (ho:o∈origins b) (hf :f∈C.factors o)
    (hI:I∈QV C o f j) (hn:n∈(movingOrder b).take (j-afterFree b)) :
    MovingFit (nV b n) fun k=>pN I k := by
  obtain ⟨t,ht,he⟩:=moving_before hn
  have hg:=selected_ok b n (List.mem_iff_getElem?.mpr ⟨_,he⟩)
  let s :=nV b n
  have hs :s∈stages b:=cqz hg.2.1
  let rows :=x.donors.staged s hs
  let fixed:=C.fixed s hs
  obtain ⟨hm,hp⟩:=live_mem hI
  obtain ⟨hP,hQ,hc⟩:=(moving_pass he hs).mp (hp _ ht)
  obtain ⟨ha,_,_,_,hfixed⟩:=C.DN o ho f hf I hm
  obtain ⟨hfixP,hfixQ⟩:=hfixed s hs
  obtain ⟨hfree,hmove⟩:=shapes_ok b s hs
  have hd:=live_dual C hI ((after_free_pos b).trans_le (by omega))
  have hr :=hg.2.2.2
  apply moving_of_box s _ hfree.2.2.1 hmove.2.2.1
  exact qp73k1b.proof ⟨s.dI,s.free,s.moving⟩ rows.free.jet rows.moving.jet
    fixed.free fixed.moving I hfree.2.2.2.1 hfree.2.2.2.2 rows.free.nonzero rows.moving.nonzero
    (d3r x.crt (wordLift M) (chosen_mem rows.free))
    (d3r x.crt (wordLift M) (chosen_mem rows.moving))
    rows.no_moving ha hd hc hfixP hfixQ
    (chosen_order rows.free hr ha hd hP) (chosen_order rows.moving hr ha hd hQ)
end
end qkrKkqa
