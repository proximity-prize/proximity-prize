import ProximityPrize.SubmissionLower.R6960RescueGeometryInvoice

set_option Elab.async false

-- merged module R6960RescueGeometryFee
section Merged_R6960RescueGeometryFee
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.RescueGeometry
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL evaluated)
open K1_14_2 (Ambient ODE)
open K1_14_2_2 (mass mass_mono ODECaps)
open K1_14_3 (Surface Parent)
open P1_7_4 (ODEGuard Mass massQ dotQ dotQ_mono_mass massQ_mono dotQ_scale_add)
open P1_7_4_3 (mix)
open HighCore82268JointRank (fixed_fee_linear)
open Lower6960.RescueGeometry (persistentTotal persistentTop siteRatio density)
open scoped Classical BigOperators
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>∃ J∈ini.rankExit,OnMark F J γ)
theorem fixedFee_eq (B J : ℕ) :
    fixedFee B J = (mix B J (mu+2*lambda*(B-1 : ℕ))
      (min (mu+2*lambda*(B-1 : ℕ)) (lambda*(2*J-1 : ℕ)))).ceil.toNat+B^2 := by
  have he : 2*density*(endpointDegree : ℚ)=2*lambda := by unfold lambda density; ring
  have hl : density*(endpointDegree : ℚ)=lambda := rfl
  have hm : siteRatio endpointDegree=mu := rfl
  unfold fixedFee persistentTop persistentTotal
  rw [he,hl,hm]
theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) (hi : M.overhead.toNat≤33579) :
    (ini.rankMarks.card : ℚ)≤dotQ (rankWeight rect) (massQ ini.rankExit)+rankRound rect := by
  let S := ini.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E,caps,roots⟩ := ini.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ initialCap rect k :=
    (mass_mono (subset_union_left : S⊆ini.rankExit∪ini.parents) k).trans (ini.fits k)
  have hBm : B≤mass S 2+2 := max_le (by omega) (by omega)
  have hJm : J≤mass S 1+1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B≤rankB rect := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J≤rankJ rect := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hB2 : 2≤B := le_max_left _ _
  have hJ1 : 1≤J := le_max_left _ _
  have hJB : J≤B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree≤B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree≠0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1,(le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  obtain ⟨small,cJ,cB⟩ := rank_guard rect
  have guard : ODEGuard B J := ⟨hB2,hJ1,hJB,hB.trans_lt small⟩
  have count : ini.rankMarks.card≤fixedFee B J :=
    fixed_count F hi guard E ocaps (filter_subset _ _)
      (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau (pivot rect) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤
      rankWeight rect 1 * J + rankWeight rect 2 * B + 2*lambda*pivot rect^2+1 := by
    rw [fixedFee_eq]
    exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ (rankWeight rect) (massQ ini.rankExit) =
      rankWeight rect 1 * (mass S 1 : ℚ)+rankWeight rect 2 * (mass S 2 : ℚ) := by
    simp [dotQ,rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,rankRound]
  linarith only [hjfee,hbfee]
private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)
theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hiM : M.overhead.toNat≤33579) {i : ℕ} (hi : i<17) :
    ((curveMarks F (C.cover i)).card : ℚ)≤
      dotQ (lossWeight R.rect i) (massQ (R.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit R.rect :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0))
      (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight R.rect 0 i) (history R.rect i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (R.live_history hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt (seed_limit_small R.rect)
  obtain ⟨ok,degree⟩ := rate_spec R.rect hi
  have count := rated_curve_count F (curve_tariff F hiM) ok (C.cover i)
    global ((min_le_min le_rfl localCap).trans degree) prime
  calc
    _ ≤ (degreeRate R.rect i : ℚ)*((C.cover i).cost 0 : ℚ) +
          (heightRate R.rect i : ℚ)*((C.cover i).cost 1 : ℚ)+((C.cover i).cost 0 : ℚ) := count
    _ ≤ (degreeRate R.rect i : ℚ)*dotQ (cutWeight R.rect 0 i) (massQ (R.lost i)) +
          (heightRate R.rect i : ℚ)*dotQ (cutWeight R.rect 1 i) (massQ (R.lost i)) +
          ((C.cover i).cost 0 : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (C.costQ hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (C.costQ hi 1) (Nat.cast_nonneg _))) le_rfl
    _ = _ := by rw [dotQ_scale_add]; rfl
def CutBooks.lossMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G} (C : CutBooks R) :
    Finset K := R.initial.rankMarks ∪ (range 17).biUnion (fun i=>curveMarks F (C.cover i))
theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hi : M.overhead.toNat≤33579) : C.lossMarks.card ≤ (lossLimit R.rect).ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (R.initial.rankMarks.card : ℚ) +
      ∑ i∈range 17,((curveMarks F (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ R.initial.rankMarks.card +
      ∑ i∈range 17,(curveMarks F (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem))
    (s:=range 17)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (R.initial.rank_count hi) sum_cuts
  have joint := R.joint_bill (rankWeight R.rect) (lossWeight R.rect)
  have seed := C.seed_bill
  have total := cum.trans both
  unfold lossLimit
  linarith only [total,joint,seed]
def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G} (C : CutBooks R) :
    Finset K := ((C.lossMarks ∪ C.pointMarks) ∪ R.initial.seedMarks) ∪ R.initial.ordinateMarks
theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hi : M.overhead.toNat≤33579) : C.paid.card≤rescueFee R.rect := by
  have h1 := card_union_le ((C.lossMarks∪C.pointMarks)∪R.initial.seedMarks) R.initial.ordinateMarks
  have h2 := card_union_le (C.lossMarks∪C.pointMarks) R.initial.seedMarks
  have h3 := card_union_le C.lossMarks C.pointMarks
  have rate := C.loss_count hi
  have points := card_round C.point_bill
  have seeds := R.initial.seed_count
  have ordinates := R.initial.ordinate_count
  unfold rescueFee CutBooks.paid
  omega
theorem exceptional_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2359≤M.overhead.toNat) (hi : M.overhead.toNat≤33579)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (common : PrefixRows.Common
      (evaluated Crt (word M) HelperSource.helperBank.shape (HelperSource.helperCutoff M.overhead.toNat)) G) :
    ∃ (paid : Finset K) (S : Finset Surface),
      paid.card ≤ 118460744183568976 ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R,C,S,geom,cover⟩ := inventory F Crt lo hi noPole residues common
  refine ⟨C.paid,S,(C.paid_count hi).trans (rescue_fee_bound R.rect),geom,?_⟩
  intro γ hγ zero
  rcases cover γ hγ zero with seed | ordinate | rank | point | ⟨i,hi,curve,mem,on⟩ | retained
  · exact Or.inl (mem_union_left _ (mem_union_right _ seed))
  · exact Or.inl (mem_union_right _ ordinate)
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_union_left _ (mem_filter.mpr ⟨hγ,rank⟩)))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ point)))
  · have cuts : γ∈(range 17).biUnion (fun i=>curveMarks F (C.cover i)) :=
      mem_biUnion.mpr ⟨i,mem_range.mpr hi,mem_curveMarks (F:=F) hγ mem on⟩
    exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ cuts))))
  · exact Or.inr retained
#print axioms exceptional_prefix
end Lower6960.RescueGeometry

end
end Merged_R6960RescueGeometryFee

-- merged module R6960MainGeometry
section Merged_R6960MainGeometry

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6960.MainGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt seedHasse)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual orderOn FixedPart)
open K1_14_2_2R (chainCompatible)
open HelperPrefix (timesShape)
open HelperSource (helperBank helperCutoff)
open MainPrefixSource (copies hasse_at_mark)
open FreeSource (bank reserve cutoff)
open RescueGeometry (Model Family word OnMark terminalShape contact_at_mark zero_of_contact reserve_small)
open DifferentialContact (Native)
open PrefixRows (Prepared)
open P1_7_4 (ODEGuard degreeVector introJump introWeight)
open scoped Classical

def freeShape (i : Fin 17) : Shape := (bank i).shape

def movingShape (i : Fin 17) : Shape := timesShape (copies i) helperBank.shape

def stage (i : Fin 17) : P1_7.Stage := ⟨reserve i,bank i,⟨movingShape i,0,0⟩⟩

def cutShape (i : ℕ) : Shape :=
  if hi : i+1<17 then HighCore82258_3.envelope (stage ⟨i+1,hi⟩) else terminalShape

theorem cutShape_fit (i : ℕ) : (cutShape i).J≤(cutShape i).B := by
  unfold cutShape
  split
  · exact Nat.le_add_left _ _
  · decide

def introIndices : List (Fin 17) := [1,2,3,4,5,6,7,8,9,10,11,12]

def introAccount (k : Fin 4) : List (Fin 17) → (Fin 3→ℕ) → (Fin 3→ℕ) → ℕ
  | [], cap, old =>
      introJump cap old (movingShape 0) k +
        K1_14_2_2_2.ordinaryBudget (cap 2) (cap 0) k
  | i::rest, cap, old =>
      let s := freeShape i
      introJump cap old s k + introAccount k rest
        (fun j=>min (cap j) (degreeVector s j/(reserve i+1)))
        (fun j=>max (old j) (introWeight s k j))

def initialCap (k : Fin 4) : ℕ :=
  introAccount k introIndices (degreeVector (freeShape 0)) (fun _=>0)

theorem initial_small (k : Fin 4) : initialCap k < K1.p := by
  fin_cases k <;> decide +kernel

theorem free_ode_guard (i : Fin 17) : ODEGuard (freeShape i).B (freeShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem moving_ode_guard (i : Fin 17) : ODEGuard (movingShape i).B (movingShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem free_seed_small (i : Fin 17) : (freeShape i).U<K1.p :=
  (FreeSource.shape_guards i).2.2.2.1

theorem moving_seed_small (i : Fin 17) : (movingShape i).U<K1.p := by
  fin_cases i <;> decide +kernel

theorem reserve_pos {i : Fin 17} (hi : 0 < i.val) : 0<reserve i := by
  have checks (j : Fin 17) : (j.val=0) ∨ 0<reserve j := by
    fin_cases j <;> decide +kernel
  exact (checks i).resolve_left (by omega)

/-- The main branch retains the single preparation object, including the
original helper, its one possible exception, and the 17 stripped free rows. -/
structure Rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) where
  source : Fin 17→Jet
  out : Prepared source freeShape copies
    (evaluated Crt (word M) helperBank.shape (helperCutoff M.overhead.toNat)) helperBank.shape
  contact : ∀ i γ, γ∈Γ → jetAt out.exception (M.label γ) (F.scalar γ)≠0 →
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.helper^copies i)
  fixedFree : ∀ i, FixedPart (out.free i) (freeShape i)
  fixedMoving : ∀ i, FixedPart (out.helper^copies i) (movingShape i)

theorem rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2359≤M.overhead.toNat) (hi : M.overhead.toNat≤33579)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Nonempty (Rows F Crt) := by
  obtain ⟨P,out,_,inside,_⟩ := MainPrefixSource.rows Crt (word M) lo hi
  refine ⟨⟨P,out,?_,?_,?_⟩⟩
  · intro i γ mem regular
    have fit : reserve i+1 ≤ copies i*11 := by unfold copies; omega
    refine out.contacts i _ (RingHom.ker_isPrime _) ?_ (reserve i+1) 11 fit ?_ ?_
    · intro van
      apply regular
      simpa only [K1_14_2.eval_toJet] using RingHom.mem_ker.mp van
    · exact contact_at_mark F Crt noPole residues (inside i) (FreeSource.cutoff_fit lo hi i) γ mem
    · intro H hm
      have wh := HelperSource.helper_width lo hi
      have width : helperCutoff M.overhead.toNat+2*M.overhead.toNat*10 < helperBank.shape.m*179818 :=
        FreeSource.buffered_fit helperBank 179818 _ 10 wh
      exact contact_at_mark F Crt noPole residues hm width γ mem
  · intro i
    exact Classical.choice (K1_14_2_2_1.proof _ _ (out.free_ne i) (out.free_caps i))
  · intro i
    exact Classical.choice (K1_14_2_2_1.proof _ _ (pow_ne_zero _ out.helper_ne) (out.moving_caps i))

def Rows.marks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Finset K :=
  Γ.filter (fun γ=>jetAt R.out.exception (M.label γ) (F.scalar γ)≠0)

def Rows.family {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Family M R.marks :=
  ⟨F.scalar,fun γ hγ=>F.mark γ (mem_filter.mp hγ).1,F.distinct.mono (filter_subset _ _)⟩

theorem Rows.main_contact {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 17) (γ : K) (mem : γ∈R.marks) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.helper^copies i) :=
  R.contact i γ (mem_filter.mp mem).1 (mem_filter.mp mem).2

theorem Rows.intro_tests {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 17) (j : Fin 2) (a : ℕ) (ha : a≤reserve i) (γ : K) (mem : γ∈R.marks) :
    jetAt (seedHasse j a (R.out.free i)) (M.label γ) (R.family.scalar γ)=0 :=
  hasse_at_mark (R.main_contact i γ mem).1 j a ha (ha.trans_lt (reserve_small i))

def Rows.Passes {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 17) (J : Ideal Ambient) : Prop :=
  orderOn J (R.out.free i) (reserve i+1) ∧
  orderOn J (R.out.helper^copies i) (reserve i+1) ∧ chainCompatible (R.out.free i) (R.out.helper^copies i) J

theorem Rows.failed_cut {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 17) {J : Ideal Ambient} (active : Active J) (dualJ : dual J) (fail : ¬R.Passes i J) :
    ∃ C : Jet,(RowCaps C (freeShape i) ∨ RowCaps C (movingShape i)) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  rcases PrefixStage.order_or_cut active dualJ (reserve_small i) (R.out.free_caps i) (R.out.moving_caps i)
    (pow_ne_zero _ R.out.helper_ne) (moving_ode_guard i).jpos with passes | ⟨C,cap,proper,zero⟩
  · exact (fail passes).elim
  · refine ⟨C,cap,proper,?_⟩
    intro γ hγ on
    obtain ⟨free,moving⟩ := R.main_contact i γ hγ
    exact zero _ _ on free moving

#print axioms rows
#print axioms Rows.failed_cut
end Lower6960.MainGeometry

end
end Merged_R6960MainGeometry

-- merged module R6960MainGeometryIntro
section Merged_R6960MainGeometryIntro

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.MainGeometry
open Finset Polynomial
open K1 (K)
open K1_14 (Shape Jet Seeds FX jetAt graphEval seedHasse atX)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient OnJet ODE fixedAt)
open K1_14_2_2 (RowCaps Active dual Fits FixedPart fixedOn mass sectionDegree sum_union_le ordinateIncl ODECaps)
open K1_14_2_2_2 (ordinaryBudget ordinate_eq length_le_mass)
open K1_14_3 (NoMovingCommon SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open P1_7_4 (degreeVector introJump introWeight)
open P1_7_4_1 (SectionGeometry IntroFactors factorDegree factorMass factorMass_mono factorTariff
  weightedDegree tariff_step ordinary_charge residual_tariff collect proper_cover own_J_le_B own_caps retained_mass
  Stripped initial_factors strip)
open RescueGeometry (Model Family OnMark label_injective zero_of_contact)
open FreeSource (reserve)
open MainPrefixSource (copies)
open P1_7_4_1 (irreducible_cut terminal_piece)
open P0_10R_1 (seed_projection)
open scoped Classical BigOperators

private theorem intro_components
    {P Q : Jet} (hQ : Q ≠ 0) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q (movingShape 0)) (later : Fin 17 → Jet)
    (rows : ∀ i, later i ≠ 0 ∧ RowCaps (later i) (freeShape i)) :
    ∀ (is : List (Fin 17)),
    ∀ (D : Finset Jet) (cap : Fin 3 → ℕ), IntroFactors P D → (∀ j, factorMass D j ≤ cap j) →
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      (∀ k old, mass S k ≤ introAccount k is cap old + weightedDegree old D) ∧
      ∀ z R, (∀ i ∈ is, ∀ j a, a ≤ reserve i →
        jetAt (seedHasse j a (later i)) z R = 0) →
        jetAt Q z R = 0 → (∃ f ∈ D, jetAt f z R = 0) → ∃ I ∈ S, OnJet I z R := by
  classical
  intro is
  induction is with
  | nil =>
    intro D cap hD hcap
    let t := movingShape 0
    have gt := moving_ode_guard 0
    obtain ⟨S, hG, hS, hC⟩ := collect D
      (fun f k => factorTariff t k f + ordinaryBudget (factorDegree f 2) (factorDegree f 0) k)
      (fun f z R => jetAt f z R = 0 ∧ jetAt Q z R = 0)
      (terminal_piece hD hnc hQc gt.jb gt.small hQ)
    refine ⟨S, hG, ?_, ?_⟩
    · intro k old
      have hstep := tariff_step (Finset.empty_subset D) cap old t k hcap
      simp only [Finset.sdiff_empty, weightedDegree, factorMass, Finset.sum_empty,
        mul_zero, Finset.sum_const_zero, Nat.add_zero] at hstep
      have hsum := Nat.add_le_add hstep (ordinary_charge D cap hcap k)
      calc
        _ ≤ ∑ f ∈ D, (factorTariff t k f +
            ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) := hS k
        _ ≤ (weightedDegree old D + introJump cap old t k) +
            ordinaryBudget (cap 2) (cap 0) k := by
          rw [Finset.sum_add_distrib]
          exact hsum
        _ = _ := by
          simp only [introAccount]
          ac_rfl
    · intro z R _ hq ⟨f, hf, hz⟩
      exact hC f hf z R ⟨hz, hq⟩
  | cons i is ih =>
    intro D cap hD hcap
    let s := freeShape i
    let r := reserve i
    let T := D.filter fun f => ∀ j a, a ≤ r → f ∣ seedHasse j a (later i)
    have hT : T ⊆ D := Finset.filter_subset _ _
    have gt := free_ode_guard i
    obtain ⟨hrow, hc⟩ := rows i
    have hTcap (j : Fin 3) :
        factorMass T j ≤ min (cap j) (degreeVector s j / (r+1)) :=
      le_min ((factorMass_mono hT j).trans (hcap j))
        (retained_mass (hD.mono hT) hrow hc (free_seed_small i) r
          (fun f hf => (Finset.mem_filter.mp hf).2) j)
    obtain ⟨laterCover, hLaterGeom, hLaterCap, hLater⟩ :=
      ih T _ (hD.mono hT) hTcap
    obtain ⟨discard, hDiscardGeom, hDiscardCap, hDiscard⟩ :=
      collect (D \ T) (fun f k => factorTariff s k f)
        (fun f z R => jetAt f z R = 0 ∧
          ∀ j a, a ≤ r → jetAt (seedHasse j a (later i)) z R = 0) (by
        intro f hf
        obtain ⟨hfD, hfT⟩ := Finset.mem_sdiff.mp hf
        have hn : ¬ ∀ j a, a ≤ r → f ∣ seedHasse j a (later i) :=
          fun hall => hfT (Finset.mem_filter.mpr ⟨hfD, hall⟩)
        push Not at hn
        obtain ⟨j, a, ha, hd⟩ := hn
        have hirr := (hD.factors f hfD).1
        obtain ⟨S, hG, hF, hC⟩ := proper_cover (irreducible_cut hirr hd)
          (own_J_le_B hirr.ne_zero) gt.jb (own_caps f) (P1_7_4_1_2.proof s (later i) hc j a)
        exact ⟨S, hG, fun k => (hF k).trans_eq (residual_tariff f s gt.jb k),
          fun z R hr => hC z R hr.1 (hr.2 j a ha)⟩)
    refine ⟨discard ∪ laterCover, ?_, ?_, ?_⟩
    · intro I hI
      exact (Finset.mem_union.mp hI).elim (hDiscardGeom I) (hLaterGeom I)
    · intro k old
      let w := fun j => max (old j) (introWeight s k j)
      let newCap := fun j => min (cap j) (degreeVector s j / (r+1))
      have hstep := tariff_step hT cap old s k hcap
      calc
        _ ≤ mass discard k + mass laterCover k := sum_union_le (fun I => sectionDegree I k) _ _
        _ ≤ (∑ f ∈ D \ T, factorTariff s k f) +
            (introAccount k is newCap w + weightedDegree w T) :=
          Nat.add_le_add (hDiscardCap k) (hLaterCap k w)
        _ = introAccount k is newCap w +
            ((∑ f ∈ D \ T, factorTariff s k f) + weightedDegree w T) := by ac_rfl
        _ ≤ introAccount k is newCap w + (weightedDegree old D + introJump cap old s k) :=
          Nat.add_le_add_left hstep _
        _ = _ := by
          change _ = (introJump cap old s k + introAccount k is newCap w) + weightedDegree old D
          ac_rfl
    · intro z R hder hq ⟨f, hf, hz⟩
      by_cases h : f ∈ T
      · obtain ⟨I, hI, hMark⟩ := hLater z R
          (fun l hl => hder l (List.mem_cons_of_mem _ hl)) hq ⟨f, h, hz⟩
        exact ⟨I, Finset.mem_union_right _ hI, hMark⟩
      · obtain ⟨I, hI, hMark⟩ := hDiscard f (Finset.mem_sdiff.mpr ⟨hf, h⟩) z R
          ⟨hz, hder i (List.mem_cons_self ..)⟩
        exact ⟨I, Finset.mem_union_left _ hI, hMark⟩

def Rows.fixedMarksOf {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (G : ODE) : Finset K :=
  R.marks.filter (fun γ=>fixedAt G (R.family.scalar γ)=0)

def Rows.fixedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Finset K :=
  (univ : Finset (Fin 17)).biUnion (fun i=>
    R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation)

theorem Rows.mem_fixed_free {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 17)
    (root : fixedAt (R.fixedFree i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_left _ (mem_filter.mpr ⟨mark,root⟩)⟩

theorem Rows.mem_fixed_moving {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 17)
    (root : fixedAt (R.fixedMoving i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_right _ (mem_filter.mpr ⟨mark,root⟩)⟩

def Rows.Clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (J : Ideal Ambient) : Prop :=
  ∀ i, ¬ fixedOn (R.fixedFree i).equation J ∧ ¬ fixedOn (R.fixedMoving i).equation J

private theorem Rows.fixed_of_not_clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {J : Ideal Ambient} {γ : K} (mark : γ∈R.marks) (on : OnMark R.family J γ)
    (bad : ¬R.Clean J) : γ∈R.fixedMarks := by
  by_contra absent
  apply bad
  intro i
  constructor
  · intro h
    apply absent (R.mem_fixed_free mark i ?_)
    simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on h)
  · intro h
    apply absent (R.mem_fixed_moving mark i ?_)
    simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on h)

private theorem Rows.sections {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) :
    ∃ S : Finset (Ideal Ambient),SectionGeometry S ∧ Fits S initialCap ∧
      ∃ content : Seeds, content≠0 ∧ content.totalDegree≤(freeShape 0).U ∧
      ∀ γ∈R.marks,γ∈R.fixedMarks ∨ graphEval (M.label γ) content=0 ∨ ∃ J∈S,OnMark R.family J γ := by
  obtain ⟨a⟩ := strip (R.out.free_ne 0) (R.out.free_caps 0) (R.fixedFree 0)
  obtain ⟨A,hA,hcap,hroot⟩ := initial_factors a
  obtain ⟨S,geom,fit,cover⟩ := intro_components (pow_ne_zero _ R.out.helper_ne)
    (R.out.no_moving 0) (R.out.moving_caps 0) R.out.free
    (fun i=>⟨R.out.free_ne i,R.out.free_caps i⟩) introIndices A _ hA hcap
  refine ⟨S,geom,?_,a.content,a.content_ne,a.content_le,?_⟩
  · intro k
    simpa only [initialCap,weightedDegree,zero_mul,Finset.sum_const_zero,Nat.add_zero] using fit k (fun _=>0)
  · intro γ hγ
    obtain ⟨p,q⟩ := R.main_contact 0 γ hγ
    rcases a.covers _ _ (zero_of_contact p) with hs | hf | hp
    · exact Or.inr (Or.inl hs)
    · exact Or.inl (R.mem_fixed_free hγ 0 hf)
    · exact Or.inr (Or.inr (cover _ _ (fun i _ j r hr=>R.intro_tests i j r hr γ hγ)
        (zero_of_contact q) (hroot _ _ hp)))

structure Initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) where
  seed : SeedCover
  seed_cap : seed.curve.totalDegree ≤ initialCap 2
  seed_points : seed.points.card ≤ initialCap 3
  ordinates : Finset FX
  ordinate_cap : ordinates.card ≤ initialCap 0
  content : Seeds
  content_ne : content≠0
  content_cap : content.totalDegree≤(freeShape 0).U
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  fits : Fits (rankExit∪parents) initialCap
  disjoint : Disjoint rankExit parents
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ R.Clean J
  covers : ∀ γ∈R.marks,γ∈R.fixedMarks ∨ graphEval (M.label γ) content=0 ∨
    seed.Covers (M.label γ) ∨ atX (R.family.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark R.family J γ) ∨ ∃ J∈parents,OnMark R.family J γ

/-- Form the initial affine section cover, remove fixed-factor marks, and
split the remaining active parents at the actual rank-exit index zero. -/
theorem Rows.initial_cover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) :
    Nonempty (Initial R) := by
  obtain ⟨S,geom,fit,content,cn,cc,cover⟩ := R.sections
  let noSeeds := S.filter (fun J=>sectionDegree J 0=0)
  let constY := S.filter (fun J=>0<sectionDegree J 0 ∧
    ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := S.filter (fun J=>0<sectionDegree J 0 ∧
    Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>R.Clean J ∧ ¬dual J)
  let parents := active.filter (fun J=>R.Clean J ∧ dual J)
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (initial_small k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,
      ⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z T,OnJet J z T → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧
        (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z T,OnJet J z T → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) :=
    (R.marks.filter (OnMark R.family J)).image fun γ=>atX (R.family.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos
    apply card_le_one.mpr
    intro y hy z hz
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy
    obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,content,cn,cc,
    rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _))
      ((filter_subset _ _).trans (filter_subset _ _))
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2.2 (mem_filter.mp b).2.2
  · intro J mem
    exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2.2⟩
  · intro J mem
    obtain ⟨hin,c,d⟩ := mem_filter.mp mem
    obtain ⟨act,ht⟩ := geomActive J hin
    exact ⟨act,d,ht,c⟩
  · intro γ hγ
    rcases cover γ hγ with fixed | seed | ⟨J,hin,on⟩
    · exact Or.inl fixed
    · exact Or.inr (Or.inl seed)
    · by_cases z : sectionDegree J 0=0
      · have mem : J∈noSeeds := mem_filter.mpr ⟨hin,z⟩
        exact Or.inr (Or.inr (Or.inl (joinCovers_covers mem ((seed_spec J mem).2.2 _ _ on))))
      · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
        · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
          by_cases clean : R.Clean J
          · by_cases d : dual J
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,clean,d⟩,on⟩))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,clean,d⟩,on⟩))))
          · exact Or.inl (R.fixed_of_not_clean hγ on clean)
        · have mem : J∈constY := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
          exact Or.inr (Or.inr (Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem,
            mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))))

theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ E : ODE, ODECaps E (mass ini.rankExit 2) (mass ini.rankExit 1) ∧
      ∀ γ∈R.marks,(∃ J∈ini.rankExit,OnMark R.family J γ) → fixedAt E (R.family.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation ini.rankExit ini.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))

#print axioms Rows.initial_cover
#print axioms Initial.rank_ode
end Lower6960.MainGeometry

end
end Merged_R6960MainGeometryIntro

-- merged module R6960MainGeometryProcess
section Merged_R6960MainGeometryProcess

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.MainGeometry
open Finset Polynomial
open K1 (K)
open K1_14 (Shape Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated evaluated_shape nodeL)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (RowCaps Active dual mass mass_mono sectionDegree CutCover weight dot
  emptyCut joinCuts joinCuts_cost sum_dot)
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open P1_7_4 (Mass massQ massQ_mono pairedCap)
open RescueGeometry (Model Family OnMark OnSurface SurfacePass TerminalPass word terminalShape terminalCutoff
  contact_at_mark zero_of_contact reserve_small)
open MainPrefixSource (copies)
open FreeSource (reserve)
open HighCore82258_3 (envelope_caps)
open Lower6960.RescueGeometry (proper_cut)
open scoped Classical BigOperators

def Initial.kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) :=
  ini.parents.filter (fun J=>∀ i : Fin 17,0 < i.val → i.val≤n → R.Passes i J)

theorem Initial.kept_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.kept 0=ini.parents := by
  ext J
  constructor
  · exact fun h=>(mem_filter.mp h).1
  · intro h
    apply mem_filter.mpr
    refine ⟨h,fun i pos zero=>?_⟩
    omega

theorem Initial.kept_anti {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    Antitone ini.kept := by
  intro m n le J mem
  obtain ⟨p,pass⟩ := mem_filter.mp mem
  exact mem_filter.mpr ⟨p,fun i hi hm=>pass i hi (hm.trans le)⟩

theorem Initial.kept_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈ini.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ R.Clean J :=
  ini.parent_geom J (mem_filter.mp mem).1

def Initial.final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    Finset (Ideal Ambient) :=
  (ini.kept 16).filter (TerminalPass Crt (word M))

def Initial.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := if n<17 then ini.kept n else ini.final

def Initial.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := ini.live n \ ini.live (n+1)

theorem Initial.live_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.live 0=ini.parents := by
  rw [Initial.live,ite_eq_left (by decide : 0<17),ini.kept_zero]

theorem Initial.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<17) : ini.live (i+1)⊆ini.live i := by
  by_cases hn : i+1<17
  · simp only [Initial.live,ite_eq_left hi,ite_eq_left hn]
    exact ini.kept_anti (Nat.le_succ _)
  · have eq : i=16 := by omega
    subst i
    exact filter_subset _ _

theorem Initial.stage_mass {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (i : Fin 17) (hi : 0 < i.val) {n : ℕ} (step : i.val≤n) (k : Fin 4) :
    massQ (ini.kept n) k≤pairedCap (freeShape i) (movingShape i) (reserve i) true k := by
  have s := free_ode_guard i
  have t := moving_ode_guard i
  apply P1_7_4_2.proof (freeShape i) (movingShape i) (reserve i) true (R.out.free i)
    (R.out.helper^copies i) (reserve_pos hi) (reserve_small i) s.small t.small
    (free_seed_small i) (moving_seed_small i) s.jb t.jb (R.out.free_ne i)
    (pow_ne_zero _ R.out.helper_ne) (R.out.free_caps i) (R.out.moving_caps i)
    (R.out.no_moving i) (R.fixedFree i) (R.fixedMoving i)
  · intro _ J mem
    exact (ini.kept_geom mem).2.1
  · intro J mem
    have geom := ini.kept_geom mem
    have pass := (mem_filter.mp mem).2 i hi step
    have clean := geom.2.2.2 i
    exact ⟨geom.1,pass.2.2,clean.1,clean.2,pass.1,pass.2.1⟩

/-- Every failing parent has a marked cutter with the exact stage envelope.
The terminal failure uses a row of the common full bank. -/
theorem Initial.marked_cutter {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} {J : Ideal Ambient} (hi : i<17) (mem : J∈ini.lost i) :
    ∃ C : Jet,RowCaps C (cutShape i) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Initial.live,ite_eq_left hi] at prev
  by_cases hn : i+1<17
  · let j : Fin 17 := ⟨i+1,hn⟩
    have hf : ¬R.Passes j J := by
      intro p
      apply lost
      rw [Initial.live,ite_eq_left hn]
      apply mem_filter.mpr
      refine ⟨(mem_filter.mp prev).1,?_⟩
      intro z hz ht
      by_cases same : z.val=i+1
      · exact (Fin.ext same : z=j) ▸ p
      · exact (mem_filter.mp prev).2 z hz (by omega)
    have geom := ini.kept_geom prev
    obtain ⟨C,cap,proper,zero⟩ := R.failed_cut j geom.1 geom.2.1 hf
    refine ⟨C,?_,proper,zero⟩
    rw [cutShape,dite_eq_left hn]
    exact envelope_caps (s:=stage j) (free_ode_guard j).jb (moving_ode_guard j).jb cap
  · have eq : i=16 := by omega
    subst i
    have hf : ¬ TerminalPass Crt (word M) J := fun p =>
      lost (mem_filter.mpr ⟨prev,p⟩)
    obtain ⟨s,C,sm,inside,cap,proper⟩ := RescueGeometry.terminal_failure Crt (word M) hf
    refine ⟨C,cap,proper,?_⟩
    intro γ hγ _
    apply zero_of_contact (r:=0)
    exact contact_at_mark R.family Crt noPole
      (fun δ hd=>residues δ (mem_filter.mp hd).1) inside
      (by simpa only [Nat.mul_zero,Nat.add_zero] using Nat.sub_lt (Nat.mul_pos sm (by decide : 0<179818)) (by decide : 0<1)) γ hγ

theorem Initial.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<17) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
  have oneCut (J : Ideal Ambient) (mem : J∈ini.lost i) :
      ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈R.marks,OnMark R.family J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    obtain ⟨P,cap,proper,zero⟩ := ini.marked_cutter noPole residues hi mem
    have prev := (mem_sdiff.mp mem).1
    rw [Initial.live,ite_eq_left hi] at prev
    let sub := R.marks.filter (OnMark R.family J)
    let G : Family M sub :=
      ⟨R.family.scalar,fun γ hγ=>R.family.mark γ (mem_filter.mp hγ).1,
        R.family.distinct.mono (filter_subset _ _)⟩
    obtain ⟨C,cost,cover⟩ := proper_cut G (cutShape i) (cutShape_fit i)
      (ini.kept_geom prev).1 cap proper
      (fun γ hγ=>zero γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
    exact ⟨C,cost,fun γ hγ on=>cover γ (mem_filter.mpr ⟨hγ,on⟩) on⟩
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈ini.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈ini.lost i) :
      (∀ fee,(C J).cost fee≤dot (weight (cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈R.marks,OnMark R.family J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves,OnMark R.family Q γ := by
    simpa only [C,dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (ini.lost i) C,?_,?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J,mem,on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q,hQ,hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J,mem,point⟩)
    · exact Or.inr ⟨Q,mem_biUnion.mpr ⟨J,mem,hQ⟩,hmark⟩

theorem Initial.retained_or_lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {J : Ideal Ambient} (mem : J∈ini.parents) :
    J∈ini.final ∨ ∃ i<17,J∈ini.lost i := by
  by_cases h : ∃ i<17,J∈ini.lost i
  · exact Or.inr h
  · have alive : ∀ n≤17,J∈ini.live n := by
      intro n hn
      induction n with
      | zero => exact ini.live_zero.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Initial.live] using alive 17 le_rfl)

theorem Initial.terminal_surfaces_with_origins {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S,∃ J∈ini.final,q.asIdeal=J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks,(∃ J∈ini.final,OnMark R.family J γ) → ∃ q∈S,OnSurface F q γ := by
  let geom (J : ini.final) := ini.kept_geom (mem_filter.mp J.property).1
  let surface (J : ini.final) := surfaceOf J.val (geom J).1.prime
  let S := ini.final.attach.image surface
  refine ⟨S,?_,?_,?_⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩ := mem_image.mp hq
    have hJ := geom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1,(mem_filter.mp J.property).2⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩:=mem_image.mp hq
    exact ⟨J.val,J.property,rfl⟩
  · rintro γ _ ⟨J,hJ,on⟩
    let q : ini.final := ⟨J,hJ⟩
    refine ⟨surface q,mem_image.mpr ⟨q,mem_attach _ _,rfl⟩,?_⟩
    intro P mem
    rw [←K1_14_2.eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

theorem Initial.terminal_surfaces {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈R.marks,(∃ J∈ini.final,OnMark R.family J γ) → ∃ q∈S,OnSurface F q γ := by
  obtain ⟨S,geom,_,marks⟩:=ini.terminal_surfaces_with_origins
  exact ⟨S,geom,marks⟩

#print axioms Initial.stage_mass
#print axioms Initial.cutCover
#print axioms Initial.terminal_surfaces
end Lower6960.MainGeometry

end
end Merged_R6960MainGeometryProcess

-- merged module R6960MainGeometryBills
section Merged_R6960MainGeometryBills

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

namespace Lower6960.MainGeometry
open Finset Polynomial
open K1 (K)
open K1_14 (Jet atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass mass_mono weight dot CutCover emptyCut)
open P1_7_4 (Mass massQ massQ_mono dotQ pairedCap weightedBill bill_bound)
open RescueGeometry (Model Family OnMark label_injective beforeCuts fixedFee fixed_count)
open FreeSource (reserve)
open scoped Classical BigOperators

def initialMass : Mass := fun k=>initialCap k

private def historyTable : List Mass :=
  [
    ![10597, 106674, 492190, 2145993],
    ![5756, 165809/2, 375084, 1980456],
    ![22349/9, 351832/9, 375084, 1915456],
    ![13715/8, 390915/16, 1775816/9, 9168368/9],
    ![5216/5, 407313/25, 130626, 734373],
    ![4699/6, 145283/12, 248109/2, 2772225/4],
    ![34803/64, 501165/64, 80446, 1016044/3],
    ![39209/121, 579508/121, 2652560/49, 259081],
    ![39209/121, 579508/121, 48147, 259081],
    ![39209/121, 579508/121, 48147, 1006009/4],
    ![11153/40, 865023/200, 1943756/49, 216225],
    ![253791/961, 3699363/961, 4120626/121, 15944049/100],
    ![38497/150, 3699363/961, 4115580/121, 15944049/100],
    ![38497/150, 3699363/961, 4115580/121, 15944049/100],
    ![1173662/4761, 5666773/1587, 8407560/289, 99765932/729],
    ![1140713/5184, 17363647/5184, 141744/5, 99765932/729],
    ![1140713/5184, 17363647/5184, 3051745/108, 48750750/361]
  ]

def history (i : ℕ) : Mass := historyTable.getD i initialMass

theorem history_zero (k : Fin 4) : history 0 k=initialMass k := by
  fin_cases k <;> decide +kernel

theorem history_step (i : Fin 16) (k : Fin 4) :
    let j : Fin 17 := ⟨i.val+1,by have := i.isLt; omega⟩
    history (i.val+1) k =
      min (history i.val k) (pairedCap (freeShape j) (movingShape j) (reserve j) true k) := by
  fin_cases i <;> fin_cases k <;> decide +kernel

theorem Initial.cap_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) (k : Fin 4) : massQ (ini.kept n) k ≤ initialMass k := by
  exact (Nat.cast_le (α:=ℚ)).mpr ((mass_mono
    ((filter_subset _ _).trans subset_union_right) k).trans (ini.fits k))

theorem Initial.cap_kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (ini.kept i) k≤history i k := by
  induction i with
  | zero => rw [history_zero]; exact ini.cap_initial _ _
  | succ i ih =>
    have hl : i<16 := by omega
    have hstep := history_step ⟨i,hl⟩ k
    dsimp only at hstep
    rw [hstep]
    exact le_min ((massQ_mono (ini.kept_anti (Nat.le_succ i)) k).trans (ih (by omega)))
      (ini.stage_mass ⟨i+1,hi⟩ (Nat.succ_pos _) le_rfl k)

theorem Initial.cap_live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (ini.live i) k≤history i k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_kept hi k

theorem Initial.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (ini.live i) k ≤ initialMass k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_initial _ k

def cutWeight (fee : Fin 3) (i : ℕ) : Mass := fun k=>weight (cutShape i) fee k

def seedLimit : ℚ := weightedBill 17 (cutWeight 0) history

def pointLimit : ℚ := weightedBill 17 (cutWeight 2) (fun _=>initialMass)

def initialSeedLimit : ℕ := (K1.p+1)*initialCap 2+initialCap 3

def contentLimit : ℕ := (K1.p+1)*(freeShape 0).U

def fixedLimit : ℕ :=
  ∑ i : Fin 17, (fixedFee (freeShape i).B (freeShape i).J+fixedFee (movingShape i).B (movingShape i).J)

theorem seed_limit_small : seedLimit < (K1.p : ℚ) := by decide +kernel

theorem Initial.ordinary_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)).card ≤ initialCap 0 := by
  apply (card_le_card_of_injOn (fun γ=>atX (R.family.scalar γ))
    (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_cap
  intro γ hγ δ hδ eq
  exact R.family.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1
    (K1_14_3.scalar_atX_injective eq)

theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))).card ≤ initialSeedLimit := by
  have bound := K1_14_3.seed_count
    (T:=R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))) (label_injective M).injOn ini.seed
    (ini.seed_cap.trans_lt (initial_small 2)) (fun _ hγ=>(mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_cap) ini.seed_points)

theorem Initial.content_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)).card≤contentLimit := by
  let C : K1_14_3.SeedCover := ⟨ini.content,ini.content_ne,∅⟩
  have bound := K1_14_3.seed_count
    (T:=R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)) (label_injective M).injOn C
    (ini.content_cap.trans_lt (free_seed_small 0)) (fun _ hγ=>Or.inl (mem_filter.mp hγ).2)
  exact (by simpa only [C,card_empty,Nat.add_zero] using bound :
    (R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)).card≤(K1.p+1)*ini.content.totalDegree)
    |>.trans (Nat.mul_le_mul_left _ ini.content_cap)

theorem Rows.fixed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (hi : M.overhead.toNat≤33579) :
    R.fixedMarks.card≤fixedLimit := by
  calc
    _ ≤ ∑ i : Fin 17, (R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation).card :=
      card_biUnion_le
    _ ≤ _ := sum_le_sum fun i _=>(card_union_le _ _).trans (Nat.add_le_add
      (RescueGeometry.fixed_count R.family hi (free_ode_guard i) _ (R.fixedFree i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2))
      (RescueGeometry.fixed_count R.family hi (moving_ode_guard i) _ (R.fixedMoving i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2)))

structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) where
  cover : ℕ→CutCover
  cost : ∀ i<17,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))
  covers : ∀ i<17,∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark R.family Q γ

theorem Initial.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks ini) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<17 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    by_cases hi : i<17
    · obtain ⟨C,cap,cover⟩ := ini.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩

theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) {i : ℕ} (hi : i<17) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight fee i) (massQ (ini.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound

theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (∑ i∈range 17,((C.cover i).cost 0 : ℚ))≤seedLimit :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 17 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.cap_live hi))

def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K := (range 17).biUnion fun i=>(C.cover i).direct

theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (C.pointMarks.card : ℚ) ≤ pointLimit := by
  calc
    _ ≤ ∑ i∈range 17,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 17,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 17,dotQ (cutWeight 2 i) (massQ (ini.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 17 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.live_initial hi)

private def Initial.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit∪ini.parents
  | i+1 => ini.live i

private def Initial.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit
  | i+1 => ini.lost i

/-- The rank exit and the seventeen cut bins spend a single weighted
history, starting from the mass of the initial proper cover. -/
theorem Initial.joint_bill_with_final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (ini.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) 18) (massQ ini.final) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass) (history)) := by
  have bill := P1_7_4.bill_bound_with_final 18 (beforeCuts rank cut) (beforeCuts (initialMass) (history))
    ini.jointLive ini.jointLost ?_ ?_ ?_
  · rw [show 18=17+1 by decide,sum_range_succ'] at bill
    have final : ini.jointLive 18 = ini.final := by simp [Initial.jointLive,Initial.live]
    simpa only [beforeCuts,Initial.jointLost,final,add_comm] using bill
  · intro i hi
    cases i with
    | zero => simpa only [Initial.jointLive,ini.live_zero] using
        (subset_union_right : ini.parents⊆ ini.rankExit∪ini.parents)
    | succ i => exact ini.next_sub (by omega)
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem,?_⟩
      rw [Initial.jointLive,ini.live_zero]
      exact fun h=>(disjoint_left.mp ini.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α:=ℚ)).mpr (ini.fits k)
    | succ i => exact ini.cap_live (by omega) k


#print axioms history_step
#print axioms Rows.fixed_count
theorem Initial.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (ini.lost i))) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts initialMass history) :=
  (le_add_of_nonneg_right (P1_7_4.final_credit_nonneg 18 (beforeCuts rank cut) ini.final)).trans
    (ini.joint_bill_with_final rank cut)

#print axioms Initial.joint_bill
#print axioms CutBooks.point_bill
end Lower6960.MainGeometry

end
end Merged_R6960MainGeometryBills

-- merged module R6960MainGeometryInvoice
section Merged_R6960MainGeometryInvoice

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.MainGeometry
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open RescueGeometry (RateOK beforeCuts lambda mu tau)
open Lower6960.RescueGeometry (heightBound height_spec)
open scoped Classical BigOperators

def degreeRates : List ℕ :=
  [155997388, 155997388, 155997388, 155997388, 155997388, 155997388, 155997388, 80403997, 41020580, 80403997, 118503960, 41707115, 117383052, 94698036, 94698036, 132932404, 218921550]

def heightRates : List ℕ :=
  [3042427, 3042427, 3042427, 3042427, 3042427, 3042427, 3042427, 6114031, 12228062, 6114031, 4076021, 12022955, 4114661, 5152695, 5152695, 3606887, 2100971]

def degreeRate (i : ℕ) : ℕ := degreeRates.getD i 0

def heightRate (i : ℕ) : ℕ := heightRates.getD i 0

private theorem checked_rates (i : Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate i.val : ℚ) ∧
      min seedLimit (dotQ (cutWeight 0 i.val) (history i.val)) ≤ (degreeRate i.val : ℚ) ∧
      heightBound (degreeRate i.val) ≤ (heightRate i.val : ℚ) := by
  fin_cases i <;> decide +kernel

theorem rate_spec {i : ℕ} (hi : i<17) :
    RateOK (degreeRate i) (heightRate i) ∧
      min seedLimit (dotQ (cutWeight 0 i) (history i)) ≤ degreeRate i := by
  obtain ⟨base,degree,height⟩ := checked_rates ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def rankB : ℕ := initialCap 2+2

def rankJ : ℕ := initialCap 1+1

def pivot : ℚ := min (47843/5) (tau*rankB)

def rankWeight : Mass :=
  ![0,4*lambda*rankB*tau+mu-4*lambda*pivot,4*lambda*rankJ*(1-tau)+rankB,0]

def rankRound : ℚ := rankWeight 1+2*rankWeight 2+2*lambda*pivot^2+1

def lossWeight (i : ℕ) : Mass :=
  fun k=>(degreeRate i : ℚ)*cutWeight 0 i k+(heightRate i : ℚ)*cutWeight 1 i k

def lossLimit : ℚ :=
  weightedBill 18 (beforeCuts rankWeight lossWeight) (beforeCuts initialMass history)+seedLimit+rankRound

def mainFee : ℕ := lossLimit.ceil.toNat+pointLimit.ceil.toNat+initialSeedLimit+initialCap 0+
  fixedLimit+contentLimit

theorem main_fee_bound : mainFee ≤ 116835760512599839 := by decide +kernel

theorem rank_guard : rankB<p ∧ 0≤rankWeight 1 ∧ 0≤rankWeight 2 := by decide +kernel

#print axioms main_fee_bound
#print axioms rate_spec
end Lower6960.MainGeometry

end
end Merged_R6960MainGeometryInvoice
