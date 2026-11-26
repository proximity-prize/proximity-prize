import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.High6966Main13200
import ProximityPrize.SubmissionLower.R6960ChartGlobalTests
import ProximityPrize.SubmissionLower.R6960CollisionMarkedMonicFibre
import ProximityPrize.SubmissionLower.R6960Low6960Gates
import ProximityPrize.SubmissionLower.R6966ProofFarRetained

section Merged6967_R6966ProofFarTerminalCount
set_option Elab.async false





set_option Elab.async false

namespace Research6966.FarTerminalCount
open Polynomial Finset
open K1 (K)
open K1_14 (Equation L atMark jetAt)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open K1_14_3 (Surface Parent ProjectedProduct)
open KoalaRect (axisDegree rectGain rectDebit rectSlots)
open KoalaRectAxes (swap)
open Lower6960
open FarRescueGeometry (Model Family SurfacePass terminalShape word)
open FarTerminalReceipts (terminalBank witness bank_checked positive)
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

private theorem reject {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I→L)
    (lo : 2523≤h) (hi : h≤33697) {S : Finset Surface}
    (parents : ∀ q∈S, Parent q ∧ SurfacePass Crt w q)
    {f : Equation} (product : ProjectedProduct S f) (e : ℕ)
    (ep : 0<e) (en : e≤f.natDegree) (U d : Fin 2→ℕ)
    (box : U 0+U 1≤terminalShape.U)
    (gain : rectDebit h terminalBank.nodeRows terminalBank.poleMoment U <
      rectGain 179759 h terminalShape e U d)
    (slots : ∀ r,rectSlots U (axisDegree f) r≤rectSlots U d r) : False := by
  have width : terminalShape.B*(131071-h)≤terminalShape.m*179759 :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lo 131071)).trans (by decide +kernel)
  exact (not_le_of_gt gain) (KoalaRect.rectLoss (h:=h) (by omega) (by omega)
    (lt_of_le_of_lt hi (by decide)) Crt w 179759 terminalShape U d (by decide) (by decide)
    box bank_checked.moment.2 width bank_checked.nodes.le bank_checked.moment.1 ep
    (fun q hq=>(parents q hq).1) (fun q hq=>(parents q hq).2.original)
    product.primitive.ne_zero en product slots)

private theorem box_guard (i : Fin 41) : (witness i.val).U 0+(witness i.val).U 1≤terminalShape.U := by
  fin_cases i <;> decide +kernel

private theorem one_sided (i : Fin 41) : (witness i.val).order 0=0 := by
  fin_cases i <;> decide +kernel

theorem degrees {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I→L)
    (lo : 2523≤h) (hi : h≤33697) {S : Finset Surface}
    (parents : ∀ q∈S, Parent q ∧ SurfacePass Crt w q) {f : Equation} (product : ProjectedProduct S f) :
    f.natDegree<40 ∧ ∀ j : Fin 2, axisDegree f j<(witness f.natDegree).order 1 := by
  have rule (i : Fin 41) (ip : 0 < i.val) (e : i.val≤f.natDegree) :
      ¬(∀ r,rectSlots (witness i.val).U (axisDegree f) r≤
        rectSlots (witness i.val).U (witness i.val).order r) :=
    reject Crt w lo hi parents product i.val ip e _ _ (box_guard i) (positive lo hi i ip)
  have rev (i : Fin 41) (ip : 0 < i.val) (e : i.val≤f.natDegree) :
      ¬(∀ r,rectSlots (swap (witness i.val).U) (axisDegree f) r≤
        rectSlots (swap (witness i.val).U) (swap (witness i.val).order) r) := by
    apply reject Crt w lo hi parents product i.val ip e
    · simpa [Nat.add_comm] using box_guard i
    · rw [KoalaRectAxes.debit_swap,KoalaRectAxes.gain_swap]
      exact positive lo hi i ip
  have grade : f.natDegree<40 := by
    by_contra! big
    apply rule 40 (by decide) (by simpa using big)
    intro r
    change (_+1-r*axisDegree f 0)*(_+1-r*axisDegree f 1) ≤ (_+1-r*0)*(_+1-r*0)
    simp only [Nat.mul_zero,Nat.sub_zero]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  refine ⟨grade,?_⟩
  let i : Fin 41 := ⟨f.natDegree,by omega⟩
  let t:=witness f.natDegree
  have ip : 0 < i.val := product.positive
  have z0 : t.order 0=0 := one_sided i
  intro j
  by_contra! bad
  fin_cases j
  · apply rev i ip le_rfl
    intro r
    apply Nat.mul_le_mul (Nat.sub_le_sub_left (Nat.mul_le_mul_left r bad) _)
    change _≤_+1-r*t.order 0
    rw [z0,Nat.mul_zero,Nat.sub_zero]; exact Nat.sub_le _ _
  · apply rule i ip le_rfl
    intro r
    apply Nat.mul_le_mul _ (Nat.sub_le_sub_left (Nat.mul_le_mul_left r bad) _)
    change _≤_+1-r*t.order 0
    rw [z0,Nat.mul_zero,Nat.sub_zero]; exact Nat.sub_le _ _

/-- The unchanged far-bank producer and its far-band terminal price
give the count for the actual family at every height 2523 through 33697. -/
theorem count {u deleted} (M : P1.ModelAt 33697 u deleted) {Γ : Finset K} (F : P1.FamilyAt 179759 M Γ)
    (lo : 2523≤M.overhead) (hi : M.overhead≤33697) :
    Γ.card≤274785163470757553 := by
  classical
  have hlo : 2523≤M.overhead.toNat := by omega
  have hhi : M.overhead.toNat≤33697 := by omega
  obtain ⟨D,⟨Crt⟩,regular,residues⟩ := FarPoleChart.of_family M F
  obtain ⟨paid,S,fee,geom,prod,cover⟩ := FarMainGeometry.combined_prefix F Crt hlo hhi regular residues
  by_cases surfaces : S.Nonempty
  · obtain ⟨f,project⟩ := prod surfaces
    obtain ⟨grade,axes⟩ := degrees Crt (word M) hlo hhi geom project
    let T := Γ\paid
    have sub : T⊆Γ := sdiff_subset
    have words : RetainedShortening.Word 179759 164768 M.word F.scalar T := by
      refine ⟨F.distinct.mono sub,?_,?_⟩
      · intro γ hγ
        rcases (F.mark γ (sub hγ)).scalar_degree with zero|degree
        · simp [zero]
        · change ((F.scalar γ).natDegree:ℤ)≤131071+M.overhead at degree
          omega
      · intro γ hγ
        let mark:=F.mark γ (sub hγ)
        exact ⟨mark.bad.support,mark.bad.agreement,mark.scalar_hits⟩
    have remain := FarRetained.count words M.label (FarRescueGeometry.label_injective M) f
      project.positive grade project.separable axes (by
        intro γ hγ
        obtain ⟨mem,out⟩ := mem_sdiff.mp hγ
        obtain ⟨q,hq,on⟩ := (cover γ mem).resolve_left out
        simpa only [jetAt,eval₂_C,coe_eval₂RingHom,atMark] using on _ (project.vanishes q hq))
    have sizes := card_sdiff_add_card_inter Γ paid
    have left : (Γ∩paid).card≤paid.card := card_le_card inter_subset_right
    change T.card+(Γ∩paid).card=Γ.card at sizes
    have final := Nat.add_le_add remain (left.trans fee)
    rw [sizes] at final
    exact final.trans (by decide +kernel)
  · have contain : Γ⊆paid := by
      intro γ hγ
      exact (cover γ hγ).resolve_right (fun ⟨q,hq,_⟩=>surfaces ⟨q,hq⟩)
    exact (card_le_card contain).trans (fee.trans (by decide +kernel))

#print axioms degrees
#print axioms count
end Research6966.FarTerminalCount

end Merged6967_R6966ProofFarTerminalCount

section Merged6967_R6966ProofNearBook
set_option Elab.async false



set_option Elab.async false

namespace Research6966.NearBook
open Finset
open K1 (K)
open K1_14 (Jet Equation)
open K1_14_1 (CRTLift PoleData)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (Active mass mass_mono sectionDegree)
open K1_14_3 (Surface Parent ProjectedProduct)
open Lower6960.Rescue6966 (Model Family word SurfacePass OnSurface)
open KoalaRect (axisDegree axisDegree_le_iff)
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure Packet {u deleted} (M:Model u deleted) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) where
  paid : Finset K
  parents : Finset Surface
  sources : Finset (Ideal Ambient)
  active : ∀ J∈sources,Active J
  geo : ∀ q∈parents,Parent q ∧ SurfacePass Crt (word M) q
  origin : ∀ q∈parents,∃ J∈sources,q.asIdeal=J.comap toJet

variable {u deleted} {M:Model u deleted} {D:PoleData M.overhead.toNat} {Crt:CRTLift D}

def empty : Packet M Crt := ⟨∅,∅,∅,by simp,by simp,by simp⟩

structure Paid (b:Packet M Crt) (fee credit seed degree:ℕ) : Prop where
  price : b.paid.card+credit*mass b.sources 1≤fee
  seedCap : mass b.sources 1≤seed
  degreeCap : mass b.sources 0≤degree

theorem empty_paid : Paid (empty:Packet M Crt) 0 0 0 0 :=
  ⟨by simp [empty],by simp [empty,mass],by simp [empty,mass]⟩

def parents (b c:Packet M Crt) := b.parents∪c.parents
def sources (b c:Packet M Crt) := b.sources∪c.sources

theorem parents_geo (b c:Packet M Crt) {q} (hq:q∈parents b c) :
    Parent q ∧ SurfacePass Crt (word M) q :=
  (mem_union.mp hq).elim (b.geo q) (c.geo q)

theorem sources_active (b c:Packet M Crt) {J} (h:J∈sources b c) : Active J :=
  (mem_union.mp h).elim (b.active J) (c.active J)

theorem origin (b c:Packet M Crt) {q} (h:q∈parents b c) :
    ∃ J∈sources b c,q.asIdeal=J.comap toJet := by
  rcases mem_union.mp h with left|right
  · obtain ⟨J,hJ,eq⟩:=b.origin q left
    exact ⟨J,mem_union_left _ hJ,eq⟩
  · obtain ⟨J,hJ,eq⟩:=c.origin q right
    exact ⟨J,mem_union_right _ hJ,eq⟩

theorem mass_union (b c:Packet M Crt) (k:Fin 4) :
    mass (sources b c) k≤mass b.sources k+mass c.sources k :=
  K1_14_2_2.sum_union_le (fun J=>sectionDegree J k) _ _

theorem projected_cap (b c:Packet M Crt) {S:Finset Surface} (sub:S⊆parents b c)
    {f:Equation} (pr:ProjectedProduct S f) :
    f.natDegree≤mass b.sources 0+mass c.sources 0 :=
  (NativeOrdinateMass.projected_degree pr (sources b c) (fun _=>sources_active b c)
    (fun _ h=>origin b c (sub h))).trans (mass_union b c 0)

def owning (G:Jet) (S:Finset Surface) := S.filter (fun q=>G∈q.asIdeal)
def outside (G:Jet) (S:Finset Surface) := S.filter (fun q=>G∉q.asIdeal)
def ownerSources (G:Jet) (J:Finset (Ideal Ambient)) := J.filter (fun j=>toJet G∈j)
def otherSources (G:Jet) (J:Finset (Ideal Ambient)) := J.filter (fun j=>toJet G∉j)

theorem split_mass (G:Jet) (J:Finset (Ideal Ambient)) (k:Fin 4) :
    mass (ownerSources G J) k+mass (otherSources G J) k=mass J k :=
  sum_filter_add_sum_filter_not .. 

theorem owner_cap (b c:Packet M Crt) (G:Jet) {f:Equation}
    (pr:ProjectedProduct (owning G (parents b c)) f) (i:ℕ) :
    (f.coeff i).totalDegree≤mass (ownerSources G (sources b c)) 1 := by
  apply NativeSeedDegree.projected_seed pr _ _ _ i
  · intro J h;exact sources_active b c (mem_filter.mp h).1
  · intro q h
    obtain ⟨J,hJ,eq⟩:=origin b c (mem_filter.mp h).1
    exact ⟨J,mem_filter.mpr ⟨hJ,by
      have own: G∈q.asIdeal:=(mem_filter.mp h).2
      rwa [eq] at own⟩,eq⟩

theorem outside_cap (b c:Packet M Crt) (G:Jet) {f:Equation}
    (pr:ProjectedProduct (outside G (parents b c)) f) (i:ℕ) :
    (f.coeff i).totalDegree≤mass (otherSources G (sources b c)) 1 := by
  apply NativeSeedDegree.projected_seed pr _ _ _ i
  · intro J h;exact sources_active b c (mem_filter.mp h).1
  · intro q h
    obtain ⟨J,hJ,eq⟩:=origin b c (mem_filter.mp h).1
    exact ⟨J,mem_filter.mpr ⟨hJ,by
      have off:G∉q.asIdeal:=(mem_filter.mp h).2
      rwa [eq] at off⟩,eq⟩

theorem axis_total {f:Equation} {d:ℕ} (cap:∀ i,(f.coeff i).totalDegree≤d) (z:Fin 2) :
    axisDegree f z≤d := (axisDegree_le_iff ..).mpr (fun i=>(MvPolynomial.degreeOf_le_totalDegree ..).trans (cap i))

theorem marks_roots {Γ T:Finset K} (F:Family M Γ) {S:Finset Surface} {f:Equation}
    (pr:ProjectedProduct S f) (owns:∀γ∈T,∃q∈S,OnSurface F q γ) :
    ∀γ∈T,(f.map (K1_14.graphEval (M.label γ))).eval (K1_14.atX (F.scalar γ))=0 := by
  intro γ h
  obtain ⟨q,hq,on⟩:=owns γ h
  have zero:=on _ (pr.vanishes q hq)
  simpa only [K1_14.jetAt,Polynomial.eval₂_C,Polynomial.coe_eval₂RingHom,Polynomial.eval_map] using zero

#print axioms projected_cap
#print axioms owner_cap
#print axioms outside_cap
#print axioms marks_roots
end
end Research6966.NearBook

end Merged6967_R6966ProofNearBook
