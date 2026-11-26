import ProximityPrize.SubmissionLower.R6966ProofPadeFiltered

set_option Elab.async false

namespace Research6966.PadeCutoff
open Polynomial Finset Module
open K1_14 (Shape Jet L FX shapeSum)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent ProjectedProduct SeedClosure)
open KoalaRect (area rectCapacity rectDebit rectPower)
open scoped Polynomial
noncomputable section

/-- At each physical weight the bank obeys both the old ordinate-only
capacity and the independent graph restriction. -/
def capacity (A h e a n:ℕ) (s:Shape) (U:Fin 2→ℕ) (W:ℕ) : ℕ :=
  let step:=131071-h
  let k:=rectPower A h s W
  let b:=min s.B ((s.m*A-2*h*k)/step)
  let gain:=PadeRank.gain a n k (b+1) (s.J+1)
  min (rectCapacity A h s e U (fun _=>0) W)
    (((PadeFiltered.physicalWindow s.B s.J step W).card-gain)*area U)

/-- A strict inequality here is sufficient to exclude a graph of degree
a through n actual sheets. Every term is a natural-number expression. -/
def excluded (A h e a n:ℕ) (s:Shape) (U:Fin 2→ℕ) (nodes moment:ℕ) : Prop :=
  rectDebit h nodes moment U + ∑ W∈range (s.m*A),capacity A h e a n s U W <
    area U * shapeSum s (fun q j=>s.m*A+j-q*(131071-h))

theorem not_excluded {h A e:ℕ} (hp:0<h) (hl:h≤131070) (hc:h<K1.p) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) {s envelope:Shape} (U:Fin 2→ℕ)
    (fits:TerminalBanks.inside s envelope) (top:0<s.m*A) (small:s.m*A<K1.p)
    (hbox:U 0+U 1≤s.U) (bs:s.B<K1.p) (width:s.B*(131071-h)≤s.m*A)
    {nodes moment:ℕ} (nodeCap:P1_7_1.nodeRows s≤nodes) (poleCap:P1_7_1.groupedPoleMoment s.B s.J≤moment)
    {parents:Finset Surface} (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q)
    {f:K1_14.Equation} (prod:ProjectedProduct parents f) (ep:0<e) (deg:e≤f.natDegree)
    (ys:Finset SeedClosure) (v:SeedClosure→SeedClosure) {G:Pade.Row SeedClosure} (gp:G.primitive)
    (sheets:∀ y∈ys,(∃ q∈parents,K1_14_3.OnSeedFibre q y (v y)) ∧ G.err v y=0) :
    ¬excluded A h e G.graphDegree ys.card s U nodes moment := by
  classical
  let N:=s.m*A
  have recover:N-1+1=N:=by dsimp [N];omega
  have shapeWidth:K1_14_1.rawWidthCond h s (N-1) := by
    intro q hq j _
    rw [recover]
    exact (Nat.mul_le_mul_right _ hq).trans (width.trans (by dsimp [N];omega))
  have floor:=KoalaRect.rectRankFloor hp hl hc Crt word s (N-1) U hbox bs shapeWidth nodeCap poleCap
  rw [recover] at floor
  have bounds (W:ℕ) (win:W∈range N) :
      finrank FX (KoalaRect.rectEvaluated Crt word s W U) ≤ capacity A h e G.graphDegree ys.card s U W := by
    have inside:W<s.m*A:=mem_range.mp win
    let r:=(s.m*A-1-W)/(2*h)
    have rd:r* (2*h)≤s.m*A-1-W:=Nat.div_mul_le_self _ _
    have psmall:r+1<K1.p:=by
      have le:r≤s.m*A-1-W:=Nat.div_le_self _ _
      omega
    have enough:W+2*h*r<s.m*A:=by rw [Nat.mul_comm (2*h) r];omega
    let low:=s.m*A-2*h*(1+r)
    have low_le:low≤W := by
      have split:=Nat.mod_add_div (s.m*A-1-W) (2*h)
      have rem:=Nat.mod_lt (s.m*A-1-W) (by omega : 0<2*h)
      change (s.m*A-1-W)%(2*h)+2*h*r=s.m*A-1-W at split
      dsimp only [low]
      rw [Nat.mul_add,Nat.mul_one]
      omega
    let b:=min s.B (low/(131071-h))
    have bw:(131071-h)*b≤W := by
      rw [Nat.mul_comm]
      exact (Nat.mul_le_mul_right _ (min_le_right ..)).trans ((Nat.div_mul_le_self low _).trans low_le)
    have rank:=PadeFiltered.graph_rank hp hl Crt word U fits psmall enough (min_le_left ..) bw
      geo pass ys v gp sheets
    apply le_min
    · apply KoalaRect.rectCutoff_finrank_le _ _ _ _ _ _ _ _ prod.primitive.ne_zero deg (by omega) ep
      · intro P hP;exact K1_14_1.evaluated_shape Crt word (KoalaRect.rectEvaluated_le Crt word s W U hP)
      · intro P hP;exact KoalaRect.rectEvaluated_axis Crt word hP
      · intro P hP hn;exact P0_10_1.leading_bound hp hl Crt word s W P (KoalaRect.rectEvaluated_le Crt word s W U hP) hn
      · intro P hP hn
        exact KoalaRect.rectDivides hp Crt word A s U small geo (fun q hq=>pass q hq s fits) prod inside hP hn
      · intro z
        simpa [KoalaRect.rectSlots,KoalaRect.area] using
          KoalaRect.rectSlots_antitone U (KoalaRect.axisDegree f) (Nat.zero_le z)
    · change _≤((PadeFiltered.physicalWindow s.B s.J (131071-h) W).card-
        PadeRank.gain G.graphDegree ys.card (1+r) (b+1) (s.J+1))*area U
      rw [Nat.sub_mul,Nat.add_comm 1 r]
      exact Nat.le_sub_of_add_le rank
  have sum:=Finset.sum_le_sum (s:=range N) bounds
  unfold excluded
  exact Nat.not_lt_of_ge (floor.trans (Nat.add_le_add_left sum _))


/-- Exhaustive graph classification for the production parents. Both receipt
families are tested at their minimum number of distinct ordinates. -/
theorem counted_packet {h A e c amax:ℕ} (hp:0<h) (hl:h≤131070) (hc:h<K1.p) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) {s envelope:Shape} (U:Fin 2→ℕ)
    (fits:TerminalBanks.inside s envelope) (top:0<s.m*A) (small:s.m*A<K1.p)
    (hbox:U 0+U 1≤s.U) (bs:s.B<K1.p) (width:s.B*(131071-h)≤s.m*A)
    {nodes moment:ℕ} (nodeCap:P1_7_1.nodeRows s≤nodes) (poleCap:P1_7_1.groupedPoleMoment s.B s.J≤moment)
    (parents:Finset Surface) (nonempty:parents.Nonempty) (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q) (large:2≤e) (gap:2*c<e)
    (partialPrice:∀ a,amax<a → a≤c → excluded A h e a (e-c+a) s U nodes moment)
    (full:∀ a,e+1-(e+1)/2≤a → a≤e-c → excluded A h e a e s U nodes moment) :
    ∃ f:K1_14.Equation, ProjectedProduct parents f ∧
      (f.natDegree<e ∨ ∃ G:Pade.Row K1_14_3.SeedField,G.primitive ∧
        G.graphDegree≤amax ∧ Pade.Controls (G.map (algebraMap _ Pade.Native.Sep))
          (Pade.Native.sheets parents) c) := by
  classical
  obtain ⟨f,pf,alts⟩:=Pade.Native.packet_cases parents nonempty geo e c amax large gap
  refine ⟨f,pf,?_⟩
  by_cases low:f.natDegree<e
  · exact Or.inl low
  rcases alts with tooSmall|spread|graph
  · exact False.elim (low tooSmall)
  · obtain ⟨G,S,v,gp,onSheet,kind⟩:=spread
    have take : ∃ n,n≤S.card ∧ excluded A h e G.graphDegree n s U nodes moment := by
      rcases kind with ⟨lo,hi,count⟩|⟨lo,hi,count⟩
      · exact ⟨_,count,partialPrice _ lo hi⟩
      · exact ⟨_,count,full _ lo hi⟩
    obtain ⟨n,le,price⟩:=take
    obtain ⟨T,sub,size⟩:=exists_subset_card_eq le
    let emb:Pade.Native.Sep→+*SeedClosure:=(separableClosure K1_14_3.SeedField SeedClosure).val.toRingHom
    let pts:=T.image emb
    let slope (z:SeedClosure):=if H:∃ y∈T,emb y=z then emb (v H.choose) else 0
    have atPoint (y) (hy:y∈T) : slope (emb y)=emb (v y) := by
      have H:∃ z∈T,emb z=emb y:=⟨y,hy,rfl⟩
      simp only [slope,dite_eq_left H,emb.injective H.choose_spec.2]
    have kept:pts.card=n:=(card_image_of_injective _ emb.injective).trans size
    have prohibited:=not_excluded hp hl hc Crt word U fits top small hbox bs width nodeCap poleCap
      geo pass pf (by omega : 0<e) (by omega : e≤f.natDegree) pts slope ((G.primitive_map emb).mpr gp) (by
        intro y hy
        obtain ⟨z,hz,rfl⟩:=mem_image.mp hy
        rw [atPoint z hz]
        obtain ⟨sheet,hit⟩:=onSheet z (sub hz)
        refine ⟨(Pade.Native.sheets_iff ..).mp sheet,?_⟩
        change (G.a.map emb).eval (emb z)*slope (emb z)-(G.b.map emb).eval (emb z)=0
        rw [atPoint z hz]
        simpa only [Pade.Row.err,map_sub,map_mul,eval_map_apply,map_zero] using congrArg emb hit)
    exact False.elim (prohibited (by rwa [Pade.Row.degree_map,kept]))
  · exact Or.inr graph

end
end Research6966.PadeCutoff
