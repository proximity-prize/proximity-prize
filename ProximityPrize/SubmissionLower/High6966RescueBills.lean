import ProximityPrize.SubmissionLower.High6966RescueGeometry

set_option Elab.async false

-- merged module High6966RescueCaps
section Merged_High6966RescueCaps

namespace Lower6960.Rescue6966
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2 (mass mass_mono)
open Rescue6966Source (data bank reserve)
theorem Run.terminal_cap {u deleted} {M:Model u deleted} {Γ} {F:Family M Γ}
    {D:PoleData M.overhead.toNat} {Crt:CRTLift D} {G:Jet} (R:Run F Crt G) (k:Fin 2) :
    mass R.final (Fin.castLE (by decide : 2≤4) k) ≤ (data R.rect).bound k := by
  classical
  let route:=data R.rect
  let i:=route.pivot k
  let c:=Fin.castLE (by decide : 2≤4) k
  have hit:=R.cap i 17 i.isLt c
  have small:=route.tight k
  have sub : R.final⊆R.kept 17:=Finset.filter_subset _ _
  have paid := (Nat.mul_le_mul_left (reserve R.rect i+1) (mass_mono sub c)).trans hit
  have cost : (reserve R.rect i+1)*mass R.final c<(reserve R.rect i+1)*(route.bound k+1) :=
    paid.trans_lt small
  exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left cost)

theorem Run.terminal_ordinate {u deleted} {M:Model u deleted} {Γ} {F:Family M Γ}
    {D:PoleData M.overhead.toNat} {Crt:CRTLift D} {G:Jet} (R:Run F Crt G) :
    mass R.final 0 ≤154 :=
  (R.terminal_cap 0).trans (data R.rect).degree_cap
#print axioms Run.terminal_cap
#print axioms Run.terminal_ordinate
end Lower6960.Rescue6966

end Merged_High6966RescueCaps

-- merged module High6966RescueBills
section Merged_High6966RescueBills
section Merged_R6960Rescue6966Bills
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
namespace Lower6960.Rescue6966
open Finset Polynomial
open K1 (I K)
open K1_14 (Shape Jet atX jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass weight dot CutCover emptyCut mass_mono)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent)
open Rescue6966Source (bank reserve)
open P1_7_4 (Mass massQ dotQ massQ_mono weightedBill bill_bound)
open scoped Classical
def cutWeight (rect : Fin 54) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (cutShape rect i) fee k
def seedLimit (rect : Fin 54) : ℚ := weightedBill 17 (cutWeight rect 0) (history rect)
def pointLimit (rect : Fin 54) : ℚ := weightedBill 17 (cutWeight rect 2) (fun _ => initialMass rect)
def initialSeedLimit (rect : Fin 54) : ℕ := (K1.p+1)*initialCap rect 2+initialCap rect 3
theorem seed_limit_small (rect : Fin 54) : seedLimit rect < (K1.p : ℚ) := by
  fin_cases rect <;> decide +kernel
def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 54} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>ini.seeds.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 54} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>atX (F.scalar γ)∈ini.ordinates)
theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 54} (ini : Initial F G Q₀ rect) :
    ini.seedMarks.card ≤ initialSeedLimit rect := by
  have bound := K1_14_3.seed_count (T := ini.seedMarks) (label_injective M).injOn ini.seeds
    (ini.seed_degree.trans_lt (initial_small rect 2)) (fun _ hγ => (mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_degree) ini.seed_points)
theorem Initial.ordinate_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 54} (ini : Initial F G Q₀ rect) :
    ini.ordinateMarks.card ≤ initialCap rect 0 := by
  refine (card_le_card_of_injOn (fun γ=>atX (F.scalar γ)) (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_card
  intro γ hγ δ hδ eq
  exact F.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1 (K1_14_3.scalar_atX_injective eq)
structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) where
  cover : ℕ→CutCover
  cost : ∀ i<17,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))
  covers : ∀ i<17,∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark F Q γ
theorem Run.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks R) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<17 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
    by_cases hi : i<17
    · obtain ⟨C,cap,cover⟩ := R.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩
theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) {i : ℕ} (hi : i<17) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight R.rect fee i) (massQ (R.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound
theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (∑ i∈range 17,((C.cover i).cost 0 : ℚ))≤seedLimit R.rect :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 17 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>R.live_history hi))
def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : Finset K := (range 17).biUnion fun i=>(C.cover i).direct
theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (C.pointMarks.card : ℚ) ≤ pointLimit R.rect := by
  calc
    _ ≤ ∑ i∈range 17,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 17,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 17,dotQ (cutWeight R.rect 2 i) (massQ (R.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 17 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>R.live_initial hi)
def beforeCuts (first : Mass) (rest : ℕ → Mass) : ℕ → Mass
  | 0 => first
  | i+1 => rest i
private def Run.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit∪R.initial.parents
  | i+1 => R.live i
private def Run.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit
  | i+1 => R.lost i
theorem Run.joint_bill_with_final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (R.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) 18) (massQ R.final) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect)) := by
  have bill := P1_7_4.bill_bound_with_final 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect))
    R.jointLive R.jointLost ?_ ?_ ?_
  · rw [show 18=17+1 by decide,sum_range_succ'] at bill
    have final : R.jointLive 18 = R.final := by simp [Run.jointLive,Run.live]
    simpa only [beforeCuts,Run.jointLost,final,add_comm] using bill
  · intro i hi
    cases i with
    | zero => simpa only [Run.jointLive,R.live_start] using
        (subset_union_right : R.initial.parents⊆ R.initial.rankExit∪R.initial.parents)
    | succ i => exact R.next_sub (by omega)
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem,?_⟩
      rw [Run.jointLive,R.live_start]
      exact fun h=>(disjoint_left.mp R.initial.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α:=ℚ)).mpr (R.initial.fits k)
    | succ i => exact R.live_history (by omega) k
theorem Run.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (R.lost i))) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect)) :=
  (le_add_of_nonneg_right (P1_7_4.final_credit_nonneg 18 (beforeCuts rank cut) R.final)).trans
    (R.joint_bill_with_final rank cut)

#print axioms Run.joint_bill_with_final
end Lower6960.Rescue6966
end
end Merged_R6960Rescue6966Bills

end Merged_High6966RescueBills
