import ProximityPrize.SubmissionLower.R6966ProofPadeChart
import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false

namespace Research6966.PadeFiltered
open Polynomial Finset Module
open K1_14 (Jet Shape Seeds FX L)
open K1_14_3 (SeedField SeedClosure fibreRow Parent Surface)
open K1_14_1 (PoleData CRTLift jetConstant)
open K1_14_1_4 (specialized rawPosition doubleMap substitute)
open PadeRank (Plane box positions)
open PadeChart (chart window)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

private abbrev E:=SeedClosure

theorem base_change {A K M:Type*} [CommSemiring A] [Field K] [Field M]
    (g:A→+*K) (f:K→+*M) (a b u d:K) :
    (chart (f a) (f b) (f u) (f d)).toRingHom.comp (doubleMap (f.comp g)) =
    (doubleMap f).comp (substitute g (C (C a*Polynomial.X+C b))
      (C (C a)*Polynomial.X+C (C u*Polynomial.X+C d))) := by
  change (substitute (RingHom.id M) _ _).comp _ = _
  rw [K1_14_1_4.map_substitute,K1_14_1_4.substitute_map]
  simp only [RingHom.id_comp,doubleMap,coe_mapRingHom,Polynomial.map_C,Polynomial.map_X,map_add,map_mul]

/-- The two-dimensional physical window, including its partial top diagonal. -/
def physicalWindow (B J step W:ℕ) : Finset (ℕ×ℕ) :=
  (positions (B+1) (J+1)).filter (fun t=>step*t.2+(step-1)*t.1≤W)

private theorem compatibility {h} {D:PoleData h} (Crt:CRTLift D) :
    ∃ a b u d:E, a≠0 ∧ ∀ P:Jet,chart a b u d (fibreRow P)=
      doubleMap (algebraMap SeedField E) (specialized Crt P) := by
  obtain ⟨a,b,u,d,ne,form⟩:=K1_14_1_4.specialized_affine_form Crt
  let f:=algebraMap SeedField E
  refine ⟨f a,f b,f u,f d,(map_ne_zero f).mpr ne,?_⟩
  intro P
  change (chart _ _ _ _).toRingHom.comp (doubleMap (f.comp (algebraMap Seeds SeedField))) P =
    (doubleMap f).comp (specialized Crt).toRingHom P
  rw [form,base_change]

private theorem inject_chart (a b u d:E) (ne:a≠0) : Function.Injective (chart a b u d) := by
  apply (injective_iff_map_eq_zero (chart a b u d).toRingHom).mpr
  intro P hz
  by_contra pn
  exact (K1_14_1_4.affine_leading (RingHom.id E) Function.injective_id ne
    (b:=b) (C u*Polynomial.X+C d) pn).2.2 hz

private theorem window_rows {h W:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (s:Shape) (U:Fin 2→ℕ) (a b₀ u d:E)
    (commute:∀ P:Jet,chart a b₀ u d (fibreRow P)=doubleMap (algebraMap SeedField E) (specialized Crt P)) :
    PadeBankRank.rows Crt word s W U ≤ (window E (physicalWindow s.B s.J (131071-h) W)).comap
      (chart a b₀ u d).toLinearMap := by
  let H:=PadeBankRank.rows Crt word s W U
  apply Submodule.span_le.mpr
  rintro _ ⟨P,hP,rfl⟩ j i outside
  have inH:PadeBankRank.fibre P∈H:=Submodule.subset_span ⟨P,hP,rfl⟩
  have after:=PadeChart.chart_box a b₀ u d _ _ (PadeBankRank.rows_shape Crt word s W U inH)
  by_cases pos:(j,i)∈positions (s.B+1) (s.J+1)
  · have heavy:W<(131071-h)*i+(131071-h-1)*j := by
      by_contra! valid
      exact outside (mem_filter.mpr ⟨pos,valid⟩)
    have zero:=P0_10_1.rawPosition_zero hp hl Crt word
      (KoalaRect.rectEvaluated_le Crt word s W U hP) j i heavy
    change ((chart a b₀ u d (fibreRow P)).coeff j).coeff i=0
    rw [commute]
    simp only [doubleMap,coe_mapRingHom,coeff_map]
    change algebraMap SeedField E (rawPosition Crt j i P)=0
    rw [zero,map_zero]
  · exact after j i pos

/-- A normalized physical row fits the same total-degree cap even in
native coordinates over the algebraic closure. The full triangular box
is invariant under the invertible affine chart. -/
theorem rows_weighted_degree {h W:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (s:Shape) (U:Fin 2→ℕ) :
    PadeBankRank.rows Crt word s W U ≤
      box E (min s.B ((W+s.J)/(131071-h))+1) (s.J+1) := by
  classical
  obtain ⟨a,b,u,d,ne,commute⟩:=compatibility Crt
  let B:=min s.B ((W+s.J)/(131071-h))+1
  let M:=box E B (s.J+1)
  let T:Plane E→ₗ[E]Plane E:=(chart a b u d).toLinearMap
  have preserve:∀ Q∈M,T Q∈M:=fun Q hQ=>PadeChart.chart_box a b u d _ _ hQ
  let F:↥M→ₗ[E]M := T.restrict preserve
  have inj:Function.Injective F:=fun x y eq=>Subtype.ext (inject_chart a b u d ne (congrArg Subtype.val eq))
  have onto:Function.Surjective F:=LinearMap.surjective_of_injective inj
  intro Q hQ
  have phys:=window_rows hp hl Crt word s U a b u d commute hQ
  have fit:T Q∈M := by
    intro j i outside
    apply phys j i
    intro yes
    obtain ⟨pos,weight⟩:=mem_filter.mp yes
    have pos': j≤s.J ∧ i+j≤s.B := by simp [positions] at pos;omega
    change (131071-h)*i+(131071-h-1)*j≤W at weight
    have sum:(i+j)*(131071-h)≤W+j := by
      have off: (131071-h-1)*j+j = (131071-h)*j := by rw [←Nat.succ_mul];congr 1;omega
      rw [Nat.add_mul,Nat.mul_comm i _,Nat.mul_comm j _];omega
    have raw:i+j≤(W+s.J)/(131071-h) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    apply outside
    simp [positions,B];omega
  obtain ⟨R,eq⟩:=onto ⟨T Q,fit⟩
  have id:R.val=Q:=inject_chart a b u d ne (congrArg Subtype.val eq)
  exact id ▸ R.property

/-- Exact rectangular-bank bound for a graph on retained sheets. All support,
seed-axis and order hypotheses are obtained here from the benchmark's bank. -/
theorem graph_rank {h A W r b:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) {s envelope:Shape} (U:Fin 2→ℕ)
    (fits:TerminalBanks.inside s envelope) (small:r+1<K1.p) (cut:W+2*h*r<s.m*A)
    (innerShape:b≤s.B) (innerWeight:(131071-h)*b≤W)
    {parents:Finset Surface} (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q)
    (ys:Finset E) (v:E→E) {G:Pade.Row E} (gp:G.primitive)
    (sheets:∀ y∈ys,(∃ q∈parents,K1_14_3.OnSeedFibre q y (v y)) ∧ G.err v y=0) :
    finrank FX (KoalaRect.rectEvaluated Crt word s W U) +
      PadeRank.gain G.graphDegree ys.card (r+1) (b+1) (s.J+1)*KoalaRect.area U ≤
      (physicalWindow s.B s.J (131071-h) W).card*KoalaRect.area U := by
  classical
  obtain ⟨a,b₀,u,d,ne,commute⟩:=compatibility Crt
  let H:=PadeBankRank.rows Crt word s W U
  let S:=physicalWindow s.B s.J (131071-h) W
  let T:=chart a b₀ u d
  have inner:box E (b+1) (s.J+1) ≤ (window E S).comap T.toLinearMap := by
    intro Q bound j i outside
    have after:=PadeChart.chart_box a b₀ u d _ _ bound
    apply after j i
    intro hit
    have hi:i+j≤b ∧ j≤s.J := by simp [positions] at hit;omega
    apply outside
    have wt := Nat.mul_le_mul_left (131071-h) hi.1
    have lt:=Nat.mul_le_mul_right j (Nat.sub_le (131071-h) 1)
    rw [Nat.mul_add] at wt
    exact Finset.mem_filter.mpr ⟨by simp [positions];omega,by dsimp only;omega⟩
  have bank:=window_rows hp hl Crt word s U a b₀ u d commute (W:=W)
  have dim := PadeChart.filtered_gain gp ys v (fun y hy=>(sheets y hy).2)
    (r+1) (b+1) (s.J+1) S H T.toLinearMap (inject_chart _ _ _ _ ne) bank inner (by
      intro R mem y hy
      exact PadeBankRank.rows_contact Crt word U fits small cut geo pass (sheets y hy).1 R mem)
  have mult:=Nat.mul_le_mul_right (KoalaRect.area U) dim
  rw [Nat.add_mul] at mult
  exact (Nat.add_le_add_right (PadeBankRank.bank_dimension Crt word s W U) _).trans mult

#print axioms rows_weighted_degree
#print axioms graph_rank

/-- The exact rounded graph power is forced on the evaluated bank at
its physical cutoff before applying the integral divisibility theorem. -/
theorem forced_bank_layers {h W A r:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) {s envelope:Shape} (U:Fin 2→ℕ)
    (fits:TerminalBanks.inside s envelope) (small:r+1<K1.p) (cut:W+2*h*r<s.m*A)
    {parents:Finset Surface} (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q)
    (ys:Finset E) (v:E→E) {G:Pade.Row E} (gp:G.primitive)
    (sheets:∀ y∈ys,(∃ q∈parents,K1_14_3.OnSeedFibre q y (v y)) ∧ G.err v y=0)
    (many:2*G.graphDegree-1<ys.card) (b:ℕ) (bound:min s.B ((W+s.J)/(131071-h))≤b)
    {Q:Plane E} (mem:Q∈PadeBankRank.rows Crt word s W U) :
    G.polynomial^(Pade.layers G.graphDegree ys.card b s.J (r+1))∣Q := by
  by_cases zero:Q=0
  · rw [zero];exact dvd_zero _
  have boxMem:=rows_weighted_degree hp hl Crt word s U mem
  obtain ⟨degree,slope⟩:=(PadeRank.mem_box zero).mp boxMem
  apply Pade.forced_layers gp ys v (fun y hy=>(sheets y hy).2) Q _ _ _
    ((Nat.le_of_lt_succ degree).trans bound) (Nat.le_of_lt_succ slope) _ many
  intro y hy
  exact PadeBankRank.rows_contact Crt word U fits small cut geo pass (sheets y hy).1 Q mem

#print axioms forced_bank_layers

end
end Research6966.PadeFiltered
