import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.R6970Height2313Rates

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source0584
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969Main
noncomputable section

open K1_14 (Jet Shape)
open K1_14_1 (PoleData CRTLift evaluated)
open P1_7_4 (ODEGuard Mass degreeVector introJump introWeight pairedCap)
open HelperPrefix (timesShape)
open HelperSource (cutoffCount WidthGuard)
open Research6969
open Research6969.PhysicalWindow
open Research6966

abbrev terminalShape : Shape := ⟨3000, 4184, 900, 530820⟩

structure Plan where
  last : ℕ
  reserve : Fin (last + 1) → ℕ
  bank : Fin (last + 1) → P1_7.Bank
  head : Request
  introIndices : List (Fin (last + 1))
  historyValues : List Mass

namespace Plan

abbrev count (s : Plan) : ℕ := s.last+1

def copies (s : Plan) (i : Fin s.count) : ℕ :=
  (s.reserve i + (s.head.reserve+1)) / (s.head.reserve+1)

def freeShape (s : Plan) (i : Fin s.count) : Shape := (s.bank i).shape

def movingShape (s : Plan) (i : Fin s.count) : Shape := timesShape (s.copies i) s.head.bank.shape

def stage (s : Plan) (i : Fin s.count) : P1_7.Stage :=
  ⟨s.reserve i, s.bank i, ⟨s.movingShape i, 0, 0⟩⟩

def cutShape (s : Plan) (i : ℕ) : Shape :=
  if hi : i+1 < s.count then HighCore82258_3.envelope (s.stage ⟨i+1,hi⟩) else terminalShape

theorem cutShape_fit (s : Plan) (i : ℕ) : (s.cutShape i).J ≤ (s.cutShape i).B := by
  unfold cutShape
  split
  · exact Nat.le_add_left _ _
  · decide

def introAccount (s : Plan) (k : Fin 4) : List (Fin s.count) → (Fin 3→ℕ) → (Fin 3→ℕ) → ℕ
  | [], cap, old => introJump cap old (s.movingShape 0) k +
      K1_14_2_2_2.ordinaryBudget (cap 2) (cap 0) k
  | i::rest, cap, old =>
      let r := s.freeShape i
      introJump cap old r k + s.introAccount k rest
        (fun j => min (cap j) (degreeVector r j/(s.reserve i+1)))
        (fun j => max (old j) (introWeight r k j))

def initialCap (s : Plan) (k : Fin 4) : ℕ :=
  s.introAccount k s.introIndices (degreeVector (s.freeShape 0)) (fun _ => 0)

def initialMass (s : Plan) : Mass := fun k => s.initialCap k

def history (s : Plan) (i : ℕ) : Mass := s.historyValues.getD i s.initialMass

def freeCutoff (s : Plan) (h : ℕ) (i : Fin s.count) : ℕ :=
  cutoffCount (s.bank i).shape 179730 h (s.reserve i) - 1

abbrev helperCutoff (s : Plan) (h : ℕ) : ℕ := s.head.top h - 1

structure Valid (s : Plan) : Prop where
  reserve_pos : ∀ i : Fin s.count, 0 < i.val → 0 < s.reserve i
  reserve_small : ∀ i, s.reserve i < K1.p
  free_ode_guard : ∀ i, ODEGuard (s.freeShape i).B (s.freeShape i).J
  moving_ode_guard : ∀ i, ODEGuard (s.movingShape i).B (s.movingShape i).J
  free_seed_small : ∀ i, (s.freeShape i).U < K1.p
  moving_seed_small : ∀ i, (s.movingShape i).U < K1.p
  initial_small : ∀ k, s.initialCap k < K1.p
  history_zero : ∀ k, s.history 0 k = s.initialMass k
  history_step : ∀ (i : Fin s.last) k,
    let j : Fin s.count := ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩
    s.history (i.val+1) k = min (s.history i.val k)
      (pairedCap (s.freeShape j) (s.movingShape j) (s.reserve j) true k)

structure Sources (s : Plan) (first last : ℕ) (outer : P1_7.Bank) (extra a low floor : ℕ) : Prop where
  free : ∀ i, TransitionSources.Free first (s.reserve i) (s.bank i)
  rank : P3_7_1.BankOK s.head.bank
  width : WidthGuard s.head.bank 179730 first s.head.reserve
  reserve_fit : 2*s.head.reserve ≤ s.head.bank.shape.B
  narrow : s.head.bank.shape.J < 131071-last
  seed_small : s.head.bank.shape.U < K1.p
  same_m : s.head.bank.shape.m = outer.shape.m
  same_ord : s.head.bank.shape.B = outer.shape.B
  same_slope : s.head.bank.shape.J = outer.shape.J
  seed_le : s.head.bank.shape.U ≤ outer.shape.U
  reserve_le : 10 ≤ s.head.reserve
  level : s.head.jet = a+1
  slope : s.head.slope = 2
  weight : s.head.weight = floor + extra
  seed : s.head.seed = low+1
  extra_fit : extra ≤ 131071-last-1
  degree : 0 < a
  physical : ∃ ends, Cover (Triangular s.head) last first ends

end Plan

end
end Lower6960.Prefix6969Main
end Z6969Source0584


section Z6969Source0585
set_option autoImplicit true
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969Main
noncomputable section

variable {sched : Plan}
local notation "freeShape" => (Plan.freeShape sched)
local notation "movingShape" => (Plan.movingShape sched)
local notation "copies" => (Plan.copies sched)
local notation "reserve" => (Plan.reserve sched)
local notation "introAccount" => (Plan.introAccount sched)
local notation "introIndices" => (Plan.introIndices sched)
local notation "initialCap" => (Plan.initialCap sched)
local notation "cutShape" => (Plan.cutShape sched)
local notation "stage" => (Plan.stage sched)
local notation "cutShape_fit" => (Plan.cutShape_fit sched)

open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt seedHasse)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual orderOn FixedPart)
open K1_14_2_2R (chainCompatible)
open HelperPrefix (timesShape)
open MainPrefixSource (hasse_at_mark)
open Far6969RescueGeometry (Model Family word OnMark contact_at_mark zero_of_contact)
open DifferentialContact (Native)
open PrefixRows (Prepared)
open P1_7_4 (ODEGuard degreeVector introJump introWeight)
open scoped Classical

structure Rows (sched : Plan) {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) where
  valid : sched.Valid
  source : Fin sched.count→Jet
  out : Prepared source sched.freeShape sched.copies
    (evaluated Crt (word M) sched.head.bank.shape (sched.helperCutoff M.overhead.toNat)) sched.head.bank.shape
  contact : ∀ i γ, γ∈Γ → jetAt out.exception (M.label γ) (F.scalar γ)≠0 →
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (sched.reserve i+1) (out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (sched.reserve i+1) (out.helper^sched.copies i)
  fixedFree : ∀ i, FixedPart (out.free i) (sched.freeShape i)
  fixedMoving : ∀ i, FixedPart (out.helper^sched.copies i) (sched.movingShape i)


theorem rows_from_prepared {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (valid : sched.Valid)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    (P : Fin sched.count → Jet)
    (inside : ∀ i, P i ∈ evaluated Crt (word M) (freeShape i) (sched.freeCutoff M.overhead.toNat i))
    (free_width : ∀ i, sched.freeCutoff M.overhead.toNat i + 2*M.overhead.toNat*reserve i <
      (freeShape i).m*179730)
    (head_width : sched.helperCutoff M.overhead.toNat+2*M.overhead.toNat*sched.head.reserve <
      sched.head.bank.shape.m*179730)
    (out : Prepared P freeShape copies
      (evaluated Crt (word M) sched.head.bank.shape (sched.helperCutoff M.overhead.toNat))
      sched.head.bank.shape) :
    ∃ R : Rows sched F Crt, R.out.exception = out.exception := by
  refine ⟨⟨valid,P,out,?_,?_,?_⟩, rfl⟩
  · intro i γ mem regular
    have modulus : 0 < sched.head.reserve+1 := by omega
    have fit : reserve i+1 ≤ copies i*(sched.head.reserve+1) := by
      dsimp only [Plan.copies]
      have div := Nat.mod_add_div (reserve i + (sched.head.reserve+1)) (sched.head.reserve+1)
      have bound := Nat.mod_lt (reserve i + (sched.head.reserve+1)) modulus
      rw [Nat.mul_comm]
      omega
    refine out.contacts i _ (RingHom.ker_isPrime _) ?_ (reserve i+1) (sched.head.reserve+1) fit ?_ ?_
    · intro van
      apply regular
      simpa only [K1_14_2.eval_toJet] using RingHom.mem_ker.mp van
    · exact contact_at_mark F Crt noPole residues (inside i) (free_width i) γ mem
    · intro H hm
      exact contact_at_mark F Crt noPole residues hm head_width γ mem
  · intro i
    exact Classical.choice (K1_14_2_2_1.proof _ _ (out.free_ne i) (out.free_caps i))
  · intro i
    exact Classical.choice (K1_14_2_2_1.proof _ _ (pow_ne_zero _ out.helper_ne) (out.moving_caps i))

def Rows.marks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt) : Finset K :=
  Γ.filter (fun γ=>jetAt R.out.exception (M.label γ) (F.scalar γ)≠0)

def Rows.family {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt) : Family M R.marks :=
  ⟨F.scalar,fun γ hγ=>F.mark γ (mem_filter.mp hγ).1,F.distinct.mono (filter_subset _ _)⟩

theorem Rows.main_contact {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt)
    (i : Fin sched.count) (γ : K) (mem : γ∈R.marks) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.helper^copies i) :=
  R.contact i γ (mem_filter.mp mem).1 (mem_filter.mp mem).2

theorem Rows.intro_tests {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt)
    (i : Fin sched.count) (j : Fin 2) (a : ℕ) (ha : a≤reserve i) (γ : K) (mem : γ∈R.marks) :
    jetAt (seedHasse j a (R.out.free i)) (M.label γ) (R.family.scalar γ)=0 :=
  hasse_at_mark (R.main_contact i γ mem).1 j a ha (ha.trans_lt (R.valid.reserve_small i))

def Rows.Passes {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt)
    (i : Fin sched.count) (J : Ideal Ambient) : Prop :=
  orderOn J (R.out.free i) (reserve i+1) ∧
  orderOn J (R.out.helper^copies i) (reserve i+1) ∧ chainCompatible (R.out.free i) (R.out.helper^copies i) J

theorem Rows.failed_cut {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt)
    (i : Fin sched.count) {J : Ideal Ambient} (active : Active J) (dualJ : dual J) (fail : ¬R.Passes i J) :
    ∃ C : Jet,(RowCaps C (freeShape i) ∨ RowCaps C (movingShape i)) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  rcases PrefixStage.order_or_cut active dualJ (R.valid.reserve_small i) (R.out.free_caps i) (R.out.moving_caps i)
    (pow_ne_zero _ R.out.helper_ne) (R.valid.moving_ode_guard i).jpos with passes | ⟨C,cap,proper,zero⟩
  · exact (fail passes).elim
  · refine ⟨C,cap,proper,?_⟩
    intro γ hγ on
    obtain ⟨free,moving⟩ := R.main_contact i γ hγ
    exact zero _ _ on free moving




set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

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
open Far6969RescueGeometry (Model Family OnMark label_injective zero_of_contact)
open P1_7_4_1 (irreducible_cut terminal_piece)
open P0_10R_1 (seed_projection)
open scoped Classical BigOperators

private theorem intro_components (good : sched.Valid)
    {P Q : Jet} (hQ : Q ≠ 0) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q (movingShape 0)) (later : Fin sched.count → Jet)
    (rows : ∀ i, later i ≠ 0 ∧ RowCaps (later i) (freeShape i)) :
    ∀ (is : List (Fin sched.count)),
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
    have gt := good.moving_ode_guard 0
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
          simp only [Plan.introAccount]
          ac_rfl
    · intro z R _ hq ⟨f, hf, hz⟩
      exact hC f hf z R ⟨hz, hq⟩
  | cons i is ih =>
    intro D cap hD hcap
    let s := freeShape i
    let r := reserve i
    let T := D.filter fun f => ∀ j a, a ≤ r → f ∣ seedHasse j a (later i)
    have hT : T ⊆ D := Finset.filter_subset _ _
    have gt := good.free_ode_guard i
    obtain ⟨hrow, hc⟩ := rows i
    have hTcap (j : Fin 3) :
        factorMass T j ≤ min (cap j) (degreeVector s j / (r+1)) :=
      le_min ((factorMass_mono hT j).trans (hcap j))
        (retained_mass (hD.mono hT) hrow hc (good.free_seed_small i) r
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
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt) (G : ODE) : Finset K :=
  R.marks.filter (fun γ=>fixedAt G (R.family.scalar γ)=0)

def Rows.fixedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt) : Finset K :=
  (univ : Finset (Fin sched.count)).biUnion (fun i=>
    R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation)

theorem Rows.mem_fixed_free {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin sched.count)
    (root : fixedAt (R.fixedFree i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_left _ (mem_filter.mpr ⟨mark,root⟩)⟩

theorem Rows.mem_fixed_moving {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin sched.count)
    (root : fixedAt (R.fixedMoving i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_right _ (mem_filter.mpr ⟨mark,root⟩)⟩

def Rows.Clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt) (J : Ideal Ambient) : Prop :=
  ∀ i, ¬ fixedOn (R.fixedFree i).equation J ∧ ¬ fixedOn (R.fixedMoving i).equation J

private theorem Rows.fixed_of_not_clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt)
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
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt) :
    ∃ S : Finset (Ideal Ambient),SectionGeometry S ∧ Fits S initialCap ∧
      ∃ content : Seeds, content≠0 ∧ content.totalDegree≤(freeShape 0).U ∧
      ∀ γ∈R.marks,γ∈R.fixedMarks ∨ graphEval (M.label γ) content=0 ∨ ∃ J∈S,OnMark R.family J γ := by
  obtain ⟨a⟩ := strip (R.out.free_ne 0) (R.out.free_caps 0) (R.fixedFree 0)
  obtain ⟨A,hA,hcap,hroot⟩ := initial_factors a
  obtain ⟨S,geom,fit,cover⟩ := intro_components R.valid (pow_ne_zero _ R.out.helper_ne)
    (R.out.no_moving 0) (R.out.moving_caps 0) R.out.free
    (fun i=>⟨R.out.free_ne i,R.out.free_caps i⟩) introIndices A _ hA hcap
  refine ⟨S,geom,?_,a.content,a.content_ne,a.content_le,?_⟩
  · intro k
    simpa only [Plan.initialCap,weightedDegree,zero_mul,Finset.sum_const_zero,Nat.add_zero] using fit k (fun _=>0)
  · intro γ hγ
    obtain ⟨p,q⟩ := R.main_contact 0 γ hγ
    rcases a.covers _ _ (zero_of_contact p) with hs | hf | hp
    · exact Or.inr (Or.inl hs)
    · exact Or.inl (R.mem_fixed_free hγ 0 hf)
    · exact Or.inr (Or.inr (cover _ _ (fun i _ j r hr=>R.intro_tests i j r hr γ hγ)
        (zero_of_contact q) (hroot _ _ hp)))

structure Initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt) where
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
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt) :
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
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (R.valid.initial_small k))
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
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) :
    ∃ E : ODE, ODECaps E (mass ini.rankExit 2) (mass ini.rankExit 1) ∧
      ∀ γ∈R.marks,(∃ J∈ini.rankExit,OnMark R.family J γ) → fixedAt E (R.family.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation ini.rankExit ini.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))




set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

open Finset Polynomial
open K1 (K I)
open K1_14 (L Shape Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated evaluated_shape nodeL)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (RowCaps Active dual mass mass_mono sectionDegree CutCover weight dot
  emptyCut joinCuts joinCuts_cost sum_dot)
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open P1_7_4 (Mass massQ massQ_mono pairedCap)
open Far6969RescueGeometry (Model Family OnMark OnSurface word contact_at_mark zero_of_contact)
open HighCore82258_3 (envelope_caps)
open Lower6960.Far6969RescueGeometry (proper_cut)
open scoped Classical BigOperators

def terminalCutoff : ℕ := terminalShape.m*179730-1
def TerminalFits (s : Shape) : Prop :=
  0<s.m ∧ s.B≤terminalShape.B ∧ s.J≤terminalShape.J ∧ s.U≤terminalShape.U
def TerminalPass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (J : Ideal Ambient) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179730-1),toJet P∈J

/-- A parent that fails any terminal bank provides a proper row inside
the single envelope used by the geometric cut bill. -/
theorem terminal_failure {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L)
    {J : Ideal Ambient} (failed : ¬ TerminalPass Crt w J) :
    ∃ (s : Shape) (P : Jet), 0<s.m ∧ P∈evaluated Crt w s (s.m*179730-1) ∧
      RowCaps P terminalShape ∧ toJet P∉J := by
  classical
  unfold TerminalPass at failed
  push Not at failed
  obtain ⟨s,⟨sm,sb,sj,su⟩,P,inside,proper⟩ := failed
  refine ⟨s,P,sm,inside,?_,proper⟩
  intro j i nz
  obtain ⟨b,v,u⟩ := evaluated_shape Crt w inside j i nz
  exact ⟨b.trans sb,v.trans sj,u.trans su⟩

def SurfacePass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (q : Surface) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179730-1),P∈q.asIdeal

theorem SurfacePass.original {h : ℕ} {D : PoleData h} {Crt : CRTLift D} {w : I→L}
    {q : Surface} (pass : SurfacePass Crt w q) :
    ∀ P∈evaluated Crt w terminalShape terminalCutoff,P∈q.asIdeal :=
  pass terminalShape ⟨by decide,le_rfl,le_rfl,le_rfl⟩
def Initial.kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) :=
  ini.parents.filter (fun J=>∀ i : Fin sched.count,0 < i.val → i.val≤n → R.Passes i J)

theorem Initial.kept_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) :
    ini.kept 0=ini.parents := by
  ext J
  constructor
  · exact fun h=>(mem_filter.mp h).1
  · intro h
    apply mem_filter.mpr
    refine ⟨h,fun i pos zero=>?_⟩
    omega

theorem Initial.kept_anti {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) :
    Antitone ini.kept := by
  intro m n le J mem
  obtain ⟨p,pass⟩ := mem_filter.mp mem
  exact mem_filter.mpr ⟨p,fun i hi hm=>pass i hi (hm.trans le)⟩

theorem Initial.kept_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈ini.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ R.Clean J :=
  ini.parent_geom J (mem_filter.mp mem).1

def Initial.final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) :
    Finset (Ideal Ambient) :=
  (ini.kept sched.last).filter (TerminalPass Crt (word M))

def Initial.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := if n<sched.count then ini.kept n else ini.final

def Initial.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := ini.live n \ ini.live (n+1)

theorem Initial.live_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) :
    ini.live 0=ini.parents := by
  rw [Initial.live,ite_eq_left (Nat.zero_lt_succ _ : 0<sched.count),ini.kept_zero]

theorem Initial.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<sched.count) : ini.live (i+1)⊆ini.live i := by
  by_cases hn : i+1<sched.count
  · simp only [Initial.live,ite_eq_left hi,ite_eq_left hn]
    exact ini.kept_anti (Nat.le_succ _)
  · have eq : i=sched.last := by
      change i < sched.last+1 at hi
      change ¬ i+1 < sched.last+1 at hn
      omega
    subst i
    have hnow : sched.last < sched.count := Nat.lt_succ_self _
    have hnext : ¬ sched.last+1 < sched.count := Nat.lt_irrefl _
    simpa only [Initial.live, ite_eq_left hnow, ite_eq_right hnext, Initial.final] using
      (filter_subset (TerminalPass Crt (word M)) (ini.kept sched.last))

theorem Initial.stage_mass {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    (i : Fin sched.count) (hi : 0 < i.val) {n : ℕ} (step : i.val≤n) (k : Fin 4) :
    massQ (ini.kept n) k≤pairedCap (freeShape i) (movingShape i) (reserve i) true k := by
  have s := R.valid.free_ode_guard i
  have t := R.valid.moving_ode_guard i
  apply P1_7_4_2.proof (freeShape i) (movingShape i) (reserve i) true (R.out.free i)
    (R.out.helper^copies i) (R.valid.reserve_pos i hi) (R.valid.reserve_small i) s.small t.small
    (R.valid.free_seed_small i) (R.valid.moving_seed_small i) s.jb t.jb (R.out.free_ne i)
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
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} {J : Ideal Ambient} (hi : i<sched.count) (mem : J∈ini.lost i) :
    ∃ C : Jet,RowCaps C (cutShape i) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Initial.live,ite_eq_left hi] at prev
  by_cases hn : i+1<sched.count
  · let j : Fin sched.count := ⟨i+1,hn⟩
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
    rw [Plan.cutShape,dite_eq_left hn]
    exact envelope_caps (s:=stage j) (R.valid.free_ode_guard j).jb (R.valid.moving_ode_guard j).jb cap
  · have eq : i=sched.last := by
      change i < sched.last+1 at hi
      change ¬ i+1 < sched.last+1 at hn
      omega
    subst i
    have hf : ¬ TerminalPass Crt (word M) J := fun p =>
      by
        apply lost
        change J ∈ (if sched.last+1 < sched.count then ini.kept (sched.last+1) else ini.final)
        rw [ite_eq_right (Nat.lt_irrefl _)]
        exact mem_filter.mpr ⟨prev,p⟩
    obtain ⟨s,C,sm,inside,cap,proper⟩ := terminal_failure Crt (word M) hf
    have sized : RowCaps C (cutShape sched.last) := by
      simpa only [Plan.cutShape, dif_neg (Nat.lt_irrefl _)] using cap
    refine ⟨C,sized,proper,?_⟩
    intro γ hγ _
    apply zero_of_contact (r:=0)
    exact contact_at_mark R.family Crt noPole
      (fun δ hd=>residues δ (mem_filter.mp hd).1) inside
      (by simpa only [Nat.mul_zero,Nat.add_zero] using Nat.sub_lt (Nat.mul_pos sm (by decide : 0<179730)) (by decide : 0<1)) γ hγ

theorem Initial.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<sched.count) :
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
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    {J : Ideal Ambient} (mem : J∈ini.parents) :
    J∈ini.final ∨ ∃ i<sched.count,J∈ini.lost i := by
  by_cases h : ∃ i<sched.count,J∈ini.lost i
  · exact Or.inr h
  · have alive : ∀ n≤sched.count,J∈ini.live n := by
      intro n hn
      induction n with
      | zero => exact ini.live_zero.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Initial.live] using alive sched.count le_rfl)

theorem Initial.terminal_surfaces_with_origins {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) :
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
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈R.marks,(∃ J∈ini.final,OnMark R.family J γ) → ∃ q∈S,OnSurface F q γ := by
  obtain ⟨S,geom,_,marks⟩:=ini.terminal_surfaces_with_origins
  exact ⟨S,geom,marks⟩





end
end Lower6960.Prefix6969Main
end Z6969Source0585


section Z6969Source0609
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969Main
noncomputable section
variable {sched : Plan}

local notation "freeShape" => (Plan.freeShape sched)
local notation "movingShape" => (Plan.movingShape sched)
local notation "reserve" => (Plan.reserve sched)
local notation "initialCap" => (Plan.initialCap sched)
local notation "cutShape" => (Plan.cutShape sched)

open Finset Polynomial
open K1 (K)
open K1_14 (Jet atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass mass_mono weight dot CutCover emptyCut)
open P1_7_4 (Mass massQ massQ_mono dotQ pairedCap weightedBill bill_bound)
open Far6969RescueGeometry (Model Family OnMark label_injective beforeCuts)
open scoped Classical BigOperators


local notation "initialMass" => (Plan.initialMass sched)
local notation "history" => (Plan.history sched)

theorem Initial.cap_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    (n : ℕ) (k : Fin 4) : massQ (ini.kept n) k ≤ initialMass k := by
  exact (Nat.cast_le (α:=ℚ)).mpr ((mass_mono
    ((filter_subset _ _).trans subset_union_right) k).trans (ini.fits k))

theorem Initial.cap_kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<sched.count) (k : Fin 4) : massQ (ini.kept i) k≤history i k := by
  induction i with
  | zero => rw [R.valid.history_zero]; exact ini.cap_initial _ _
  | succ i ih =>
    have hl : i < sched.last := Nat.lt_of_succ_lt_succ hi
    have hstep := R.valid.history_step ⟨i,hl⟩ k
    dsimp only at hstep
    rw [hstep]
    exact le_min ((massQ_mono (ini.kept_anti (Nat.le_succ i)) k).trans (ih (by omega)))
      (ini.stage_mass ⟨i+1,hi⟩ (Nat.succ_pos _) le_rfl k)

theorem Initial.cap_live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<sched.count) (k : Fin 4) : massQ (ini.live i) k≤history i k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_kept hi k

theorem Initial.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<sched.count) (k : Fin 4) : massQ (ini.live i) k ≤ initialMass k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_initial _ k


def Plan.cutWeight (s : Plan) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (s.cutShape i) fee k

def Plan.seedLimit (s : Plan) : ℚ := weightedBill s.count (s.cutWeight 0) s.history
def Plan.pointLimit (s : Plan) : ℚ := weightedBill s.count (s.cutWeight 2) (fun _ => s.initialMass)
def Plan.initialSeedLimit (s : Plan) : ℕ := (K1.p+1)*s.initialCap 2+s.initialCap 3
def Plan.contentLimit (s : Plan) : ℕ := (K1.p+1)*(s.freeShape 0).U
def Plan.fixedLimit (s : Plan) (band : Band) : ℕ :=
  ∑ i : Fin s.count, (band.fixedFee (s.freeShape i).B (s.freeShape i).J +
    band.fixedFee (s.movingShape i).B (s.movingShape i).J)

local notation "cutWeight" => (Plan.cutWeight sched)
local notation "seedLimit" => (Plan.seedLimit sched)
local notation "pointLimit" => (Plan.pointLimit sched)
local notation "initialSeedLimit" => (Plan.initialSeedLimit sched)
local notation "contentLimit" => (Plan.contentLimit sched)

theorem Initial.ordinary_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)).card ≤ initialCap 0 := by
  apply (card_le_card_of_injOn (fun γ=>atX (R.family.scalar γ))
    (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_cap
  intro γ hγ δ hδ eq
  exact R.family.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1
    (K1_14_3.scalar_atX_injective eq)

theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))).card ≤ initialSeedLimit := by
  have bound := K1_14_3.seed_count
    (T:=R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))) (label_injective M).injOn ini.seed
    (ini.seed_cap.trans_lt (R.valid.initial_small 2)) (fun _ hγ=>(mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_cap) ini.seed_points)

theorem Initial.content_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)).card≤contentLimit := by
  let C : K1_14_3.SeedCover := ⟨ini.content,ini.content_ne,∅⟩
  have bound := K1_14_3.seed_count
    (T:=R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)) (label_injective M).injOn C
    (ini.content_cap.trans_lt (R.valid.free_seed_small 0)) (fun _ hγ=>Or.inl (mem_filter.mp hγ).2)
  exact (by simpa only [C,card_empty,Nat.add_zero] using bound :
    (R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)).card≤(K1.p+1)*ini.content.totalDegree)
    |>.trans (Nat.mul_le_mul_left _ ini.content_cap)

theorem Rows.fixed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt) (band : Band) (hi : M.overhead.toNat≤band.last) :
    R.fixedMarks.card≤sched.fixedLimit band := by
  calc
    _ ≤ ∑ i : Fin sched.count, (R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation).card :=
      card_biUnion_le
    _ ≤ _ := sum_le_sum fun i _=>(card_union_le _ _).trans (Nat.add_le_add
      (band.fixed_count R.family hi (R.valid.free_ode_guard i) _ (R.fixedFree i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2))
      (band.fixed_count R.family hi (R.valid.moving_ode_guard i) _ (R.fixedMoving i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2)))

structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) where
  cover : ℕ→CutCover
  cost : ∀ i<sched.count,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))
  covers : ∀ i<sched.count,∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark R.family Q γ

theorem Initial.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks ini) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<sched.count →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    by_cases hi : i<sched.count
    · obtain ⟨C,cap,cover⟩ := ini.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩

theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} {ini : Initial R}
    (C : CutBooks ini) {i : ℕ} (hi : i<sched.count) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight fee i) (massQ (ini.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [Plan.cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound

theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} {ini : Initial R}
    (C : CutBooks ini) : (∑ i∈range sched.count,((C.cover i).cost 0 : ℚ))≤seedLimit :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound sched.count _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.cap_live hi))

def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K := (range sched.count).biUnion fun i=>(C.cover i).direct

theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} {ini : Initial R}
    (C : CutBooks ini) : (C.pointMarks.card : ℚ) ≤ pointLimit := by
  calc
    _ ≤ ∑ i∈range sched.count,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range sched.count,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range sched.count,dotQ (cutWeight 2 i) (massQ (ini.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound sched.count _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.live_initial hi)

private def Initial.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) :
    ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit∪ini.parents
  | i+1 => ini.live i

private def Initial.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) :
    ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit
  | i+1 => ini.lost i

/-- The rank exit and the seventeen cut bins spend a single weighted
history, starting from the mass of the initial proper cover. -/
theorem Initial.joint_bill_with_final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range sched.count,dotQ (cut i) (massQ (ini.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) (sched.count+1)) (massQ ini.final) ≤
      weightedBill (sched.count+1) (beforeCuts rank cut) (beforeCuts (initialMass) (history)) := by
  have bill := P1_7_4.bill_bound_with_final (sched.count+1) (beforeCuts rank cut) (beforeCuts (initialMass) (history))
    ini.jointLive ini.jointLost ?_ ?_ ?_
  · rw [sum_range_succ'] at bill
    have final : ini.jointLive (sched.count+1) = ini.final := by simp [Initial.jointLive,Initial.live]
    simp only [beforeCuts,Initial.jointLost,final] at bill
    linarith only [bill]
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


theorem Initial.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range sched.count,dotQ (cut i) (massQ (ini.lost i))) ≤
      weightedBill (sched.count+1) (beforeCuts rank cut) (beforeCuts initialMass history) :=
  (le_add_of_nonneg_right (P1_7_4.final_credit_nonneg (sched.count+1) (beforeCuts rank cut) ini.final)).trans
    (ini.joint_bill_with_final rank cut)


end
end Lower6960.Prefix6969Main
end Z6969Source0609


section Z6969Source0610
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969Main
noncomputable section

open Finset
open K1 (p)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass)
open P1_7_4 (Mass dotQ weightedBill running)
open Far6969RescueGeometry (beforeCuts)
open scoped BigOperators

structure Pricing where
  tau : ℚ
  pivotScale : ℚ
  degreeRates : List ℕ
  heightRates : List ℕ
  retainedCredit : Fin 4 → ℕ
  fee : ℕ

namespace Pricing

def degreeRate (x : Pricing) (i : ℕ) : ℕ := x.degreeRates.getD i 0
def heightRate (x : Pricing) (i : ℕ) : ℕ := x.heightRates.getD i 0

def rankB (s : Plan) : ℕ := s.initialCap 2+2
def rankJ (s : Plan) : ℕ := s.initialCap 1+1
def pivot (x : Pricing) (s : Plan) : ℚ := min (x.pivotScale * rankJ s) (x.tau*rankB s)

def rankWeight (x : Pricing) (s : Plan) (b : Band) : Mass :=
  ![0,4*b.lambda*rankB s*x.tau+b.mu-4*b.lambda*x.pivot s,
    4*b.lambda*rankJ s*(1-x.tau)+rankB s,0]

def rankRound (x : Pricing) (s : Plan) (b : Band) : ℚ :=
  x.rankWeight s b 1 + 2*x.rankWeight s b 2 + 2*b.lambda*(x.pivot s)^2 + 1

def lossWeight (x : Pricing) (s : Plan) (i : ℕ) : Mass :=
  fun k => (x.degreeRate i : ℚ)*s.cutWeight 0 i k+(x.heightRate i : ℚ)*s.cutWeight 1 i k

def lossLimit (x : Pricing) (s : Plan) (b : Band) : ℚ :=
  weightedBill (s.count+1) (beforeCuts (x.rankWeight s b) (x.lossWeight s))
    (beforeCuts s.initialMass s.history)+s.seedLimit+x.rankRound s b

def mainFee (x : Pricing) (s : Plan) (b : Band) : ℕ :=
  (x.lossLimit s b).ceil.toNat+s.pointLimit.ceil.toNat+s.initialSeedLimit+s.initialCap 0+
    s.fixedLimit b+s.contentLimit

def charge (x : Pricing) (S : Finset (Ideal Ambient)) : ℕ :=
  ∑ k : Fin 4, x.retainedCredit k * mass S k

private def heightTerms (b : Band) (a : ℕ) : List ℚ :=
  (List.range 80).map (fun i : ℕ =>
    let g := i+1
    max 0 (1-(a : ℚ)*(g : ℚ)/((p+1 : ℕ) : ℚ))*b.curveUnit g)

def heightBound (b : Band) (a : ℕ) : ℚ := (heightTerms b a).foldr max 0

private theorem le_max_fold {q : ℚ} {terms : List ℚ} (mem : q∈terms) :
    q ≤ terms.foldr max 0 := by
  induction terms with
  | nil => simp at mem
  | cons a rest ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | h
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem height_spec (b : Band) (a g : ℕ) (pos : 0<g) (small : g≤80) :
    max 0 (1-(a : ℚ)*g/((p+1 : ℕ) : ℚ))*b.curveUnit g ≤ heightBound b a := by
  apply le_max_fold
  unfold heightTerms
  apply List.mem_map.mpr
  refine ⟨g-1,List.mem_range.mpr (by omega),?_⟩
  dsimp only
  rw [Nat.sub_add_cancel (by omega : 1≤g)]

/-- These are closed arithmetic checks of the saved schedule, not geometric conditions. -/
structure Valid (x : Pricing) (s : Plan) (b : Band) : Prop where
  seed_limit_small : s.seedLimit < (p : ℚ)
  tau_nonneg : 0 ≤ x.tau
  tau_le_one : x.tau ≤ 1
  rank_guard : rankB s<p ∧ 0≤x.rankWeight s b 1 ∧ 0≤x.rankWeight s b 2
  rates : ∀ i : Fin s.count,
    ((p+1 : ℕ) : ℚ)/81 ≤ (x.degreeRate i.val : ℚ) ∧
      min s.seedLimit (dotQ (s.cutWeight 0 i.val) (s.history i.val)) ≤ (x.degreeRate i.val : ℚ) ∧
      heightBound b (x.degreeRate i.val) ≤ (x.heightRate i.val : ℚ)
  retained : ∀ k, (x.retainedCredit k : ℚ) ≤
    running (beforeCuts (x.rankWeight s b) (x.lossWeight s)) (s.count+1) k
  fee_bound : x.mainFee s b ≤ x.fee

theorem Valid.rate_spec {x s b} (v : Valid x s b) {i : ℕ} (hi : i<s.count) :
    b.RateOK (x.degreeRate i) (x.heightRate i) ∧
      min s.seedLimit (dotQ (s.cutWeight 0 i) (s.history i)) ≤ x.degreeRate i := by
  obtain ⟨base,degree,height⟩ := v.rates ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg => (height_spec b _ g hp hg).trans height⟩,degree⟩

end Pricing

end
end Lower6960.Prefix6969Main
end Z6969Source0610


section Z6969Source0611
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969Main
noncomputable section

open Finset
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated evaluated_mono evaluated_shape nodeL)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open PrefixRows (Common)
open _root_.Lower6960.Prefix6969KnownHelper
open Research6969.PhysicalWindow
open Research6966

/-- A bank-indexed schedule produces the same named helper on either verified height band. -/
theorem rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (sched : Plan) (valid : sched.Valid) {first last extra a low floor : ℕ} {outer : P1_7.Bank}
    (source : sched.Sources first last outer extra a low floor)
    (firstPos : 0 < first) (lastSafe : last ≤ 131070)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ last)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G)
    (known : Common (evaluated Crt (word M) outer.shape
      (HelperSource.cutoffCount outer.shape 179730 M.overhead.toNat 10-1)) G)
    (degree : a ≤ jetDegree G) (seed : low ≤ seedDegree G)
    (physical : floor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ R : Rows sched F Crt, R.out.exception = G := by
  classical
  have hh := firstPos.trans_le lo
  have hm := hi.trans lastSafe
  let h := M.overhead.toNat
  have shape : sched.head = ⟨sched.head.bank, sched.head.reserve, a+1, 2, floor+extra, low+1⟩ := by
    rw [← source.level, ← source.slope, ← source.weight, ← source.seed]
  have hw := HelperSource.width_at_height _ 179730 first h _ lo (by omega) source.reserve_fit source.width
  obtain ⟨ends, cover⟩ := source.physical
  obtain ⟨left, right, hlo, hhi, rmax, cert⟩ := covered cover lo hi
  have narrow := source.narrow.trans_le (Nat.sub_le_sub_left rmax 131071)
  have nz := restricted_nonzero sched.head hh hm hlo hhi narrow
    (show 0 < sched.head.slope from source.slope.symm ▸ by decide) cert source.rank hw Crt (word M)
  have above : restricted sched.head Crt (word M) ≤ evaluated Crt (word M) outer.shape
      (HelperSource.cutoffCount outer.shape 179730 h 10-1) := by
    intro P hp
    refine evaluated_mono Crt (word M) (s := sched.head.bank.shape) (s' := outer.shape)
      source.same_m source.same_ord source.same_slope source.seed_le ?_ hp
    change sched.helperCutoff h ≤ HelperSource.cutoffCount outer.shape 179730 h 10-1
    change sched.head.bank.shape.m * 179730 - 2*h*sched.head.reserve - 1 ≤
      outer.shape.m * 179730 - 2*h*10 - 1
    rw [source.same_m]
    exact Nat.sub_le_sub_right
      (Nat.sub_le_sub_left (Nat.mul_le_mul_left (2*h) source.reserve_le) _) 1
  have common := common_of_le above known
  have unique : ∀ Q₁ Q₂, Common (restricted sched.head Crt (word M)) Q₁ →
      Common (restricted sched.head Crt (word M)) Q₂ → IsRelPrime Q₁ Q₂ → False := by
    have extraBound : extra ≤ 131071-h-1 :=
      source.extra_fit.trans (Nat.sub_le_sub_right (Nat.sub_le_sub_left hi _) _)
    exact known_unique sched.head.bank sched.head.reserve a floor low extra hh hm hlo hhi narrow
      source.rank source.seed_small hw (shape ▸ cert) Crt (word M) phys
      (shape ▸ common) degree physical seed extraBound
  have free (i : Fin sched.count) : ∃ Q ∈ evaluated Crt (word M) (sched.freeShape i)
      (sched.freeCutoff h i), Q ≠ 0 := (source.free i).row Crt (word M) hh lo hm
  choose P inside nonzero using free
  obtain ⟨out, eq⟩ := prepare_known P sched.freeShape sched.copies _ _ common nonzero
    (fun i => evaluated_shape Crt (word M) (inside i)) nz
    (fun _ mem => evaluated_shape Crt (word M) mem) unique
  have fw (i : Fin sched.count) : sched.freeCutoff h i + 2*h*sched.reserve i <
      (sched.freeShape i).m*179730 := by
    have w := HelperSource.width_at_height _ 179730 first h _ lo (by omega)
      (source.free i).reserve_fit (source.free i).width
    exact FreeSource.buffered_fit _ 179730 h _ w
  obtain ⟨R, outEq⟩ := rows_from_prepared F Crt valid noPole residues P inside fw
    (FreeSource.buffered_fit _ 179730 h _ hw) out
  exact ⟨R, outEq.trans eq⟩

end
end Lower6960.Prefix6969Main
end Z6969Source0611


section Z6969Source0612
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969Main
noncomputable section

variable {sched : Plan} {band : Band} {price : Pricing}

local notation "freeShape" => (Plan.freeShape sched)
local notation "movingShape" => (Plan.movingShape sched)
local notation "initialCap" => (Plan.initialCap sched)
local notation "history" => (Plan.history sched)
local notation "cutWeight" => (Plan.cutWeight sched)
local notation "seedLimit" => (Plan.seedLimit sched)
local notation "pointLimit" => (Plan.pointLimit sched)
local notation "initialSeedLimit" => (Plan.initialSeedLimit sched)
local notation "contentLimit" => (Plan.contentLimit sched)
local notation "rankB" => (Pricing.rankB sched)
local notation "rankJ" => (Pricing.rankJ sched)
local notation "rankWeight" => (Pricing.rankWeight price sched band)
local notation "rankRound" => (Pricing.rankRound price sched band)
local notation "lossWeight" => (Pricing.lossWeight price sched)
local notation "degreeRate" => (Pricing.degreeRate price)
local notation "heightRate" => (Pricing.heightRate price)
local notation "lossLimit" => (Pricing.lossLimit price sched band)
local notation "mainFee" => (Pricing.mainFee price sched band)
local notation "retainedCharge" => (Pricing.charge price)
local notation "tau" => (Pricing.tau price)
local notation "pivot" => (Pricing.pivot price sched)
local notation "lambda" => (Band.lambda band)
local notation "mu" => (Band.mu band)

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient ODE)
open K1_14_2_2 (mass mass_mono ODECaps)
open K1_14_3 (Surface Parent)
open P1_7_4 (ODEGuard Mass massQ dotQ dotQ_mono_mass massQ_mono dotQ_scale_add)
open HighCore82268JointRank (fixed_fee_linear)
open Far6969RescueGeometry (Model Family OnMark OnSurface word beforeCuts)
open P1_7_4_3 (mix)
open scoped Classical BigOperators
open Research6970.Height2313.Lower6960.Prefix6969Rates (curveMarks mem_curveMarks)
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>∃ J∈ini.rankExit,OnMark R.family J γ)
theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) (checked : price.Valid sched band) (hi : M.overhead.toNat≤band.last) :
    (ini.rankMarks.card : ℚ)≤dotQ rankWeight (massQ ini.rankExit)+rankRound := by
  let S := ini.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E,caps,roots⟩ := ini.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ initialCap k :=
    (mass_mono (subset_union_left : S⊆ini.rankExit∪ini.parents) k).trans (ini.fits k)
  have hBm : B≤mass S 2+2 := max_le (by omega) (by omega)
  have hJm : J≤mass S 1+1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B≤rankB := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J≤rankJ := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
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
  obtain ⟨small,cJ,cB⟩ := checked.rank_guard
  have guard : ODEGuard B J := ⟨hB2,hJ1,hJB,hB.trans_lt small⟩
  have count : ini.rankMarks.card≤band.fixedFee B J :=
    band.fixed_count R.family hi guard E ocaps (filter_subset _ _)
      (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau pivot band.lambda_nonneg band.mu_nonneg
    checked.tau_nonneg checked.tau_le_one hJB hB hJ
  have fee : (band.fixedFee B J : ℚ) ≤
      rankWeight 1 * J + rankWeight 2 * B + 2*lambda*pivot^2+1 := by
    rw [band.fixedFee_eq]
    exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ rankWeight (massQ ini.rankExit) =
      rankWeight 1 * (mass S 1 : ℚ)+rankWeight 2 * (mass S 2 : ℚ) := by
    simp [dotQ,Pricing.rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,Pricing.rankRound]
  linarith only [hjfee,hbfee]
private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)
theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} {ini : Initial R}
    (C : CutBooks ini) (checked : price.Valid sched band) (hiM : M.overhead.toNat≤band.last) {i : ℕ} (hi : i<sched.count) :
    ((curveMarks R.family (C.cover i)).card : ℚ)≤
      dotQ (lossWeight i) (massQ (ini.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0))
      (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight 0 i) (history i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (ini.cap_live hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt checked.seed_limit_small
  obtain ⟨ok,degree⟩ := checked.rate_spec hi
  have count := band.curve_count R.family hiM ok (C.cover i)
    global ((min_le_min le_rfl localCap).trans degree) prime
  calc
    _ ≤ (degreeRate i : ℚ)*((C.cover i).cost 0 : ℚ) +
          (heightRate i : ℚ)*((C.cover i).cost 1 : ℚ)+((C.cover i).cost 0 : ℚ) := count
    _ ≤ (degreeRate i : ℚ)*dotQ (cutWeight 0 i) (massQ (ini.lost i)) +
          (heightRate i : ℚ)*dotQ (cutWeight 1 i) (massQ (ini.lost i)) +
          ((C.cover i).cost 0 : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (C.costQ hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (C.costQ hi 1) (Nat.cast_nonneg _))) le_rfl
    _ = _ := by rw [dotQ_scale_add]; rfl
def CutBooks.lossMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} {ini : Initial R} (C : CutBooks ini) :
    Finset K := ini.rankMarks ∪ (range sched.count).biUnion (fun i=>curveMarks R.family (C.cover i))
theorem retainedCharge_cast_le (checked : price.Valid sched band) (S : Finset (Ideal Ambient)) :
    (retainedCharge S : ℚ) ≤
      dotQ (P1_7_4.running (beforeCuts rankWeight lossWeight) (sched.count+1)) (massQ S) := by
  unfold Pricing.charge dotQ massQ
  push_cast
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
    (checked.retained k) (Nat.cast_nonneg _))

theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} {ini : Initial R}
    (C : CutBooks ini) (checked : price.Valid sched band) (hi : M.overhead.toNat≤band.last) : C.lossMarks.card + retainedCharge ini.final ≤ (lossLimit).ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (ini.rankMarks.card : ℚ) +
      ∑ i∈range sched.count,((curveMarks R.family (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ ini.rankMarks.card +
      ∑ i∈range sched.count,(curveMarks R.family (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count checked hi (mem_range.mp mem))
    (s:=range sched.count)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (ini.rank_count checked hi) sum_cuts
  have joint := ini.joint_bill_with_final rankWeight lossWeight
  have seed := C.seed_bill
  have total := cum.trans both
  have retained := retainedCharge_cast_le checked ini.final
  push_cast
  unfold Pricing.lossLimit
  linarith only [total, joint, seed, retained]
def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)
def Initial.contentMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)
def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K :=
  (C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks) ∪ (R.fixedMarks ∪ ini.contentMarks)
theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows sched F Crt} {ini : Initial R}
    (C : CutBooks ini) (checked : price.Valid sched band) (hi : M.overhead.toNat≤band.last) : C.paid.card + retainedCharge ini.final ≤ mainFee := by
  have combined := card_union_le
    ((C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks)) (R.fixedMarks ∪ ini.contentMarks)
  have left := card_union_le (C.lossMarks ∪ C.pointMarks) (ini.seedMarks ∪ ini.ordinateMarks)
  have cuts := card_union_le C.lossMarks C.pointMarks
  have low := card_union_le ini.seedMarks ini.ordinateMarks
  have fixed := card_union_le R.fixedMarks ini.contentMarks
  have loss := C.loss_count checked hi
  have points := card_round C.point_bill
  have seeds : ini.seedMarks.card ≤ initialSeedLimit := ini.seed_count
  have ordinates : ini.ordinateMarks.card ≤ initialCap 0 := ini.ordinary_count
  have content : ini.contentMarks.card ≤ contentLimit := ini.content_count
  have fixedCard := R.fixed_count band hi
  unfold Pricing.mainFee CutBooks.paid
  omega
theorem Rows.main_prefix {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt)
    (checked : price.Valid sched band) (hi : M.overhead.toNat≤band.last) (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (ini : Initial R) (C : CutBooks ini) (S : Finset Surface),
      C.paid.card + retainedCharge ini.final ≤ price.fee ∧
      (∀ k, massQ ini.final k ≤ history sched.last k) ∧
      (∀ q∈S, Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S, ∃ J∈ini.final, q.asIdeal = J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks, γ∈C.paid ∨ ∃ q∈S, OnSurface F q γ := by
  obtain ⟨ini⟩ := R.initial_cover
  obtain ⟨C⟩ := ini.cutBooks noPole residues
  obtain ⟨S, geom, origin, surface⟩ := ini.terminal_surfaces_with_origins
  refine ⟨ini, C, S, (C.paid_count checked hi).trans checked.fee_bound, ?_, geom, origin, ?_⟩
  intro k
  exact (massQ_mono (filter_subset _ _) k).trans (ini.cap_kept (Nat.lt_succ_self sched.last) k)
  intro γ hγ
  rcases ini.covers γ hγ with fixed | content | seed | ord | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_union_right _ (mem_union_left _ fixed))
  · exact Or.inl (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,content⟩)))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hγ,seed⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,ord⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_union_left _ (mem_filter.mpr ⟨hγ,rank⟩)))))
  · rcases ini.retained_or_lost mem with final | ⟨i,hi,lost⟩
    · exact Or.inr (surface γ hγ ⟨J,final,on⟩)
    · rcases C.covers i hi γ hγ ⟨J,lost,on⟩ with point | ⟨Q,hQ,hmark⟩
      · have mark : γ∈C.pointMarks := mem_biUnion.mpr ⟨i,mem_range.mpr hi,point⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ mark)))
      · have mark : γ∈(range sched.count).biUnion (fun i=>curveMarks R.family (C.cover i)) :=
          mem_biUnion.mpr ⟨i,mem_range.mpr hi,mem_curveMarks (F:=R.family) hγ hQ hmark⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ mark))))

end
end Lower6960.Prefix6969Main
end Z6969Source0612


section Z6969Source0613
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969Main
noncomputable section

open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated nodeL)
open K1_14_2 (toJet)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open P1_7_4 (massQ)
open Far6969RescueGeometry (Model Family word OnSurface)
open PrefixRows (Common)
open Research6966

/-- The shared main endpoint constructs the real rows, surfaces and finite paid set
from a schedule of verified physical banks and checked numerical data. -/
theorem main_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (sched : Plan) (valid : sched.Valid) (band : Band) (price : Pricing)
    (priced : price.Valid sched band)
    {first extra a low floor : ℕ} {outer : P1_7.Bank}
    (source : sched.Sources first band.last outer extra a low floor)
    (firstPos : 0 < first)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ band.last)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G)
    (known : Common (evaluated Crt (word M) outer.shape
      (HelperSource.cutoffCount outer.shape 179730 M.overhead.toNat 10-1)) G)
    (degree : a ≤ jetDegree G) (seed : low ≤ seedDegree G)
    (physical : floor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ (R : Rows sched F Crt) (ini : Initial R) (C : CutBooks ini) (S : Finset Surface),
      R.out.exception = G ∧ C.paid.card + price.charge ini.final ≤ price.fee ∧
      (∀ k, massQ ini.final k ≤ sched.history sched.last k) ∧
      (∀ q∈S, Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S, ∃ J∈ini.final, q.asIdeal = J.comap toJet) ∧
      ∀ γ∈R.marks, γ∈C.paid ∨ ∃ q∈S, OnSurface F q γ := by
  have safe : band.last ≤ 131070 := by cases band <;> decide
  obtain ⟨R, identity⟩ := rows F Crt sched valid source firstPos safe lo hi noPole residues phys known degree seed physical
  obtain ⟨ini, C, S, paid, massCap, regular, origins, covered⟩ :=
    R.main_prefix priced hi noPole residues
  exact ⟨R, ini, C, S, identity, paid, massCap, regular, origins, covered⟩

end
end Lower6960.Prefix6969Main
end Z6969Source0613


section Z6969Source0690
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace Lower6960.Prefix6969Main.Pricing
noncomputable section

open K1 (p)

private def ratio (a : ℕ) : ℚ := (a : ℚ) / ((p+1 : ℕ) : ℚ)
private def slope (b : Band) : ℚ := 2*(1+2*b.lambda)
private def constant (b : Band) : ℚ := b.mu-(1+2*b.lambda)

def quadratic (b : Band) (a : ℕ) : ℚ := ratio a * slope b
def linear (b : Band) (a : ℕ) : ℚ := slope b - ratio a * constant b

private def raw (b : Band) (a : ℕ) (g : ℚ) : ℚ :=
  (1-ratio a*g)*(slope b*g+constant b)

private theorem unit_eq (b : Band) (g : ℕ) :
    b.curveUnit g = slope b*(g : ℚ)+constant b := by
  cases b
  · change (2*(g:ℚ)-1)*(1+2*Prefix6969Rates.density*Prefix6969Rates.endpointDegree)+
      Band.mu .near = _
    unfold slope constant Band.lambda Band.mu Prefix6969Rates.density
    norm_num [Band.last, Prefix6969Rates.endpointDegree, Prefix6969Rates.siteRatio]; ring
  · change (2*(g:ℚ)-1)*(1+2*Prefix6969MiddleRates.density*Prefix6969MiddleRates.endpointDegree)+
      Prefix6969Middle.mu = _
    unfold slope constant Band.lambda Band.mu Prefix6969MiddleRates.density
    norm_num [Band.last, Prefix6969MiddleRates.endpointDegree, Prefix6969Middle.mu, Prefix6969MiddleRates.siteRatio]; ring

private theorem unit_nonneg (b : Band) {g : ℕ} (pg : 0 < g) :
    0 ≤ b.curveUnit g := by
  rw [unit_eq]
  have h : (1 : ℚ) ≤ g := by exact_mod_cast pg
  have l : 0 ≤ 1 + 2*b.lambda := by linarith [b.lambda_nonneg]
  unfold slope constant
  have m : 0 ≤ (2*(g:ℚ)-1)*(1+2*b.lambda) :=
    mul_nonneg (by linarith only [h]) l
  linarith only [m, b.mu_nonneg]

private theorem raw_difference (b : Band) (a : ℕ) (g k : ℚ) :
    raw b a g - raw b a k = (g-k)*(linear b a - quadratic b a*(g+k)) := by
  unfold raw linear quadratic
  ring

private theorem fold_bound {r : ℚ} (hr : 0 ≤ r) (l : List ℚ) (h : ∀ z∈l,z ≤ r) :
    l.foldr max 0 ≤ r := by
  induction l with
  | nil => exact hr
  | cons a l ih =>
    exact max_le (h _ (List.mem_cons_self ..)) (ih (fun z hz => h z (List.mem_cons_of_mem _ hz)))

/-- Three scalar inequalities at the discrete maximum bound all 80 rates. -/
theorem height_from_critical (b : Band) (a k h : ℕ)
    (pk : 0 < k) (_kl : k ≤ 80)
    (left : k=1 ∨ 0 ≤ linear b a - quadratic b a*(2*(k:ℚ)-1))
    (right : k=80 ∨ linear b a - quadratic b a*(2*(k:ℚ)+1) ≤ 0)
    (top : max 0 (1-(a:ℚ)*k/((p+1:ℕ):ℚ)) * b.curveUnit k ≤ h) :
    heightBound b a ≤ h := by
  have qa : 0 ≤ quadratic b a := by
    unfold quadratic ratio slope
    have l := b.lambda_nonneg
    positivity
  have rawTop : raw b a k ≤ h := by
    have q := mul_le_mul_of_nonneg_right
      (le_max_right 0 (1-(a:ℚ)*k/((p+1:ℕ):ℚ))) (unit_nonneg b pk)
    rw [unit_eq] at q
    apply le_trans _ (q.trans (by simpa only [unit_eq] using top))
    unfold raw ratio
    rw [div_mul_eq_mul_div]
  have point (g : ℕ) (pg : 0 < g) (hg : g ≤ 80) : raw b a g ≤ raw b a k := by
    have nd : raw b a g - raw b a k ≤ 0 := by
      rw [raw_difference]
      rcases lt_trichotomy g k with gl | eq | gr
      · have glq : (g:ℚ) ≤ (k:ℚ)-1 := by
          have gnext : g+1 ≤ k := gl
          have gn : (g:ℚ)+1 ≤ k := by exact_mod_cast gnext
          linarith
        have before := left.resolve_left (by omega)
        refine mul_nonpos_of_nonpos_of_nonneg (by linarith) ?_
        have m := mul_le_mul_of_nonneg_left (show (g:ℚ)+k ≤ 2*(k:ℚ)-1 by linarith) qa
        linarith only [m, before]
      · rw [eq, sub_self, zero_mul]
      · have grq : (k:ℚ)+1 ≤ (g:ℚ) := by exact_mod_cast (show k+1 ≤ g from gr)
        have after := right.resolve_left (by omega)
        refine mul_nonpos_of_nonneg_of_nonpos (by linarith) ?_
        have m := mul_le_mul_of_nonneg_left (show 2*(k:ℚ)+1 ≤ (g:ℚ)+k by linarith) qa
        linarith only [m, after]
    linarith only [nd]
  unfold heightBound
  refine fold_bound (Nat.cast_nonneg _) _ ?_
  intro g mem
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp mem
  have ip : 0 < i+1 := Nat.succ_pos _
  have il : i+1 ≤ 80 := List.mem_range.mp hi
  have nonneg := unit_nonneg b ip
  change max 0 (1-(a:ℚ)*(i+1:ℕ)/((p+1:ℕ):ℚ)) * b.curveUnit (i+1) ≤ h
  rw [max_mul_of_nonneg _ _ nonneg, zero_mul]
  apply max_le (Nat.cast_nonneg _)
  have cmp := (point _ ip il).trans rawTop
  unfold raw ratio at cmp
  rw [div_mul_eq_mul_div] at cmp
  simpa only [unit_eq] using cmp


end
end Lower6960.Prefix6969Main.Pricing
end Z6969Source0690


end Research6970.Height2313
