import ProximityPrize.SubmissionLower.R6961LoRescueGeometryCuts

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6961.Lo.RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (Shape Jet atX jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass weight dot CutCover emptyCut mass_mono)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent)
open RescueSource (bank reserve)
open Lower6961.RescueGeometry (Model Family word OnMark label_injective OnSurface)
open P1_7_4 (Mass massQ dotQ massQ_mono weightedBill bill_bound)
open scoped Classical

def initialMass (rect : Fin 10) : Mass := fun k => initialCap rect k

def history (rect : Fin 10) : ℕ → Mass
  | 0 => initialMass rect
  | n+1 => fun k =>
    if hn : n+1<17 then
      let i : Fin 17 := ⟨n+1,hn⟩
      min (history rect n k)
        ((pairCap (primeShape rect) (bank rect i).shape k : ℚ)/(reserve i+1))
    else history rect n k

theorem Run.initial_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) (k : Fin 4) : massQ (R.kept n) k ≤ initialMass R.rect k := by
  have sub : R.kept n ⊆ R.initial.parents := by
    simpa only [R.start] using (R.antitone (Nat.zero_le n) : R.kept n⊆R.kept 0)
  exact (Nat.cast_le (α:=ℚ)).mpr ((mass_mono (sub.trans subset_union_right) k).trans (R.initial.fits k))

theorem Run.history_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i n : ℕ} (hi : i<17) (prior : i<n) (k : Fin 4) :
    massQ (R.kept n) k ≤ history R.rect i k := by
  induction i with
  | zero => exact R.initial_cap n k
  | succ i ih =>
    simp only [history,dite_eq_left hi]
    apply le_min (ih (by omega) (by omega))
    let j : Fin 17 := ⟨i+1,hi⟩
    change massQ (R.kept n) k ≤ (pairCap (primeShape R.rect) (bank R.rect j).shape k : ℚ) / (reserve j+1)
    have pos : (0 : ℚ)<reserve j+1 := by positivity
    apply (le_div_iff₀ pos).mpr
    have bound := R.cap j n prior k
    rw [Nat.mul_comm] at bound
    unfold massQ
    exact_mod_cast bound

theorem Run.live_history {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (R.live i) k ≤ history R.rect i k := by
  rw [Run.live,ite_eq_left hi]
  exact R.history_cap hi (Nat.lt_succ_self _) k

theorem Run.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (R.live i) k ≤ initialMass R.rect k := by
  rw [Run.live,ite_eq_left hi]
  exact R.initial_cap _ k

def cutWeight (rect : Fin 10) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (cutShape rect i) fee k

def seedLimit (rect : Fin 10) : ℚ := weightedBill 17 (cutWeight rect 0) (history rect)

def pointLimit (rect : Fin 10) : ℚ := weightedBill 17 (cutWeight rect 2) (fun _ => initialMass rect)

def initialSeedLimit (rect : Fin 10) : ℕ := (K1.p+1)*initialCap rect 2+initialCap rect 3

theorem seed_limit_small (rect : Fin 10) : seedLimit rect < (K1.p : ℚ) := by
  fin_cases rect <;> decide +kernel

theorem point_limit_bound (rect : Fin 10) : pointLimit rect ≤ 93730050640 := by
  fin_cases rect <;> decide +kernel

def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 10} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>ini.seeds.Covers (M.label γ))

def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 10} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>atX (F.scalar γ)∈ini.ordinates)

theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 10} (ini : Initial F G Q₀ rect) :
    ini.seedMarks.card ≤ initialSeedLimit rect := by
  have bound := K1_14_3.seed_count (T := ini.seedMarks) (label_injective M).injOn ini.seeds
    (ini.seed_degree.trans_lt (initial_small rect 2)) (fun _ hγ => (mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_degree) ini.seed_points)

theorem Initial.ordinate_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 10} (ini : Initial F G Q₀ rect) :
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

/-- The rank exit and the seventeen cut bins spend a single weighted
history, starting from the mass of the initial proper cover. -/
theorem Run.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (R.lost i))) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect)) := by
  have bill := bill_bound 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect))
    R.jointLive R.jointLost ?_ ?_ ?_
  · rw [show 18=17+1 by decide,sum_range_succ'] at bill
    simpa only [beforeCuts,Run.jointLost,add_comm] using bill
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

/-- The source receipts, geometric inventory, and cut charges from a given Stage-0 row `Q₀`. -/
theorem inventory_with_Q0 {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2327≤M.overhead.toNat) (hi : M.overhead.toNat≤2449)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (irr : Irreducible G) (rect : Fin 10)
    (capsG : K1_14_2_2.RowCaps G (primeShape rect))
    (Q₀ : Jet) (avoid0 : ¬ G ∣ Q₀) (capsQ0 : K1_14_2_2.RowCaps Q₀ (bank rect 0).shape)
    (zero0 : ∀ γ∈Γ, jetAt Q₀ (M.label γ) (F.scalar γ) = 0)
    (rows_later : ∀ (i : Fin 17), i ≠ 0 →
      ∃ Q ∈ K1_14_1.evaluated Crt (word M) (bank rect i).shape (RescueSource.cutoff M.overhead.toNat rect i), ¬ G∣Q) :
    ∃ (R : Run F Crt G) (C : CutBooks R) (S : Finset Surface),
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
        γ∈R.initial.seedMarks ∨ γ∈R.initial.ordinateMarks ∨
        (∃ J∈R.initial.rankExit,OnMark F J γ) ∨ γ∈C.pointMarks ∨
        (∃ i<17,∃ Q∈(C.cover i).curves,OnMark F Q γ) ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R⟩ := prepare_with_Q0 F Crt lo hi noPole residues irr rect capsG Q₀ avoid0 capsQ0 zero0 rows_later
  obtain ⟨C⟩ := R.cutBooks noPole residues
  obtain ⟨S,geom,pass⟩ := R.terminal_surfaces
  refine ⟨R,C,S,geom,?_⟩
  intro γ hγ zero
  rcases R.initial.covers γ hγ zero with seed | ordinate | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_filter.mpr ⟨hγ,seed⟩)
  · exact Or.inr (Or.inl (mem_filter.mpr ⟨hγ,ordinate⟩))
  · exact Or.inr (Or.inr (Or.inl rank))
  · rcases R.retained_or_lost mem with final | ⟨i,hi,lost⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pass γ hγ ⟨J,final,on⟩)))))
    · rcases C.covers i hi γ hγ ⟨J,lost,on⟩ with point | curve
      · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_biUnion.mpr ⟨i,mem_range.mpr hi,point⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,hi,curve⟩))))

end Lower6961.Lo.RescueGeometry
