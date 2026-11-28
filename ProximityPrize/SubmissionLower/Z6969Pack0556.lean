import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.R6966ProofHelperKnownPrime

set_option Elab.async false

-- Source: Research6969.PrefixKnownHelper
section Z6969Source0583
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

namespace Lower6960.Prefix6969KnownHelper
noncomputable section

open Finset Polynomial
open K1_14 (Jet Seeds Equation FX L Shape)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (divisor_caps jetDegree seedDegree)
open PrefixRows (Common Prepared power_caps)
open Research6969.PhysicalWindow
open Research6966
open DifferentialContact (Native native_power native_strip)
open scoped Classical

def restricted (q : Request) {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I → L) :
    Submodule FX Jet :=
  evaluated Crt w q.shape (q.top h - 1)

theorem common_of_le {V W : Submodule FX Jet} {G : Jet} (sub : V ≤ W) (known : Common W G) :
    Common V G :=
  ⟨known.1, known.2.1, known.2.2.1, fun Q₁ hX => known.2.2.2 Q₁ (sub hX)⟩

/-- A positive conditioned physical certificate contains a nonzero actual source row. -/
theorem restricted_nonzero (q : Request) {h lo hi : ℕ} (hh : 0 < h) (hmax : h ≤ 131070)
    (hlo : lo ≤ h) (hhi : h ≤ hi) (narrow : q.shape.J < 131071 - hi)
    (slope : 0 < q.slope) (certificate : Triangular q lo hi) (rank : P3_7_1.BankOK q.bank)
    (wide : HelperSource.WidthGuard q.bank 179730 h q.reserve)
    {D : PoleData h} (Crt : CRTLift D) (w : K1.I → L) :
    ∃ P ∈ restricted q Crt w, P ≠ 0 := by
  have gain := triangle_positive q hh hlo hhi narrow slope certificate
  apply FreeSource.nonzero_row Crt w q.bank 179730 q.reserve hh hmax rank wide
  exact (Nat.le_add_right _ _).trans_lt gain

theorem known_unique (bank : P1_7.Bank) (reserve degree weight seed otherWeight : ℕ)
    {h lo hi : ℕ} (hh : 0 < h) (hmax : h ≤ 131070) (hlo : lo ≤ h) (hhi : h ≤ hi)
    (narrow : bank.shape.J < 131071 - hi) (rank : P3_7_1.BankOK bank)
    (charU : bank.shape.U < K1.p) (wide : HelperSource.WidthGuard bank 179730 h reserve)
    (certificate : Triangular ⟨bank, reserve, degree+1, 2, weight+otherWeight, seed+1⟩ lo hi)
    {D : PoleData h} (Crt : CRTLift D) (w : K1.I → L) {G : Jet}
    (phys : HelperPhysicalModel.Model Crt G)
    (known : Common (restricted ⟨bank, reserve, degree+1, 2, weight+otherWeight, seed+1⟩ Crt w) G)
    (jd : degree ≤ jetDegree G)
    (wd : weight ≤ RawPhysicalDegree.weight (131071 - h) (131071 - h - 1) phys.raw)
    (ud : seed ≤ seedDegree G) (other : otherWeight ≤ 131071 - h - 1) :
    ∀ Q₁ Q₂,
      Common (restricted ⟨bank, reserve, degree+1, 2, weight+otherWeight, seed+1⟩ Crt w) Q₁ →
      Common (restricted ⟨bank, reserve, degree+1, 2, weight+otherWeight, seed+1⟩ Crt w) Q₂ →
      IsRelPrime Q₁ Q₂ → False := by
  apply HelperKnownPrime.unique_from_known known
  intro H common cop
  have gain := triangle_positive ⟨bank, reserve, degree+1, 2, weight+otherWeight, seed+1⟩
    hh hlo hhi narrow (by decide : 0 < (2 : ℕ)) certificate
  exact HelperKnownPrime.not_coprime hh hmax Crt w bank known common cop phys other jd wd ud
    charU rank.moment.2 ((Nat.zero_le _).trans_lt wide) wide.le rank.nodes rank.moment.1 gain

/-- Strip the named common prime, retaining its identity for the rescue branch. -/
theorem prepare_known {ι : Type*} [Fintype ι] (P : ι → Jet) (s : ι → Shape) (ks : ι → ℕ)
    (V : Submodule FX Jet) (hs : Shape) {G : Jet} (known : Common V G)
    (proper : ∀ i, P i ≠ 0) (caps : ∀ i, RowCaps (P i) (s i))
    (nonzero : ∃ H∈V, H ≠ 0) (vcaps : ∀ H∈V, RowCaps H hs)
    (unique : ∀ Q₁ Q₂, Common V Q₁ → Common V Q₂ → IsRelPrime Q₁ Q₂ → False) :
    ∃ out : Prepared P s ks V hs, out.exception = G := by
  classical
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D := Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D := Equation)
  choose free eq avoid using fun i =>
    (FiniteMultiplicity.of_prime_left known.1.prime (proper i)).exists_eq_pow_mul_and_not_dvd
  have fac (i : ι) : ∃ n : ℕ, P i = G ^ n * free i := ⟨_, eq i⟩
  have nf (i : ι) : free i ≠ 0 := right_ne_zero_of_mul (eq i ▸ proper i)
  have choose_helper (i : ι) (Q₁ : Jet) (irr : Irreducible Q₁) (dvd : Q₁ ∣ free i)
      (pos : 0 < Q₁.natDegree) (seed : K1_14_2.UsesSeed Q₁) :
      ∃ H∈V, ¬ Q₁ ∣ H := by
    by_contra! all
    have x : Common V Q₁ := ⟨irr, pos, seed, all⟩
    by_cases same : G ∣ Q₁
    · exact avoid i (same.trans dvd)
    · exact unique G Q₁ known x (known.1.isRelPrime_iff_not_dvd.mpr same)
  obtain ⟨H, mem, nh, noMove⟩ := HelperPrefix.one_helper free ks V nonzero nf choose_helper
  refine ⟨⟨G, Or.inr known, free, H, mem, nh, nf, fac, ?_,
    fun i => power_caps nh (vcaps H mem) _, noMove, ?_⟩, rfl⟩
  · intro i
    exact divisor_caps (proper i) (caps i)
      ((dvd_mul_left (free i) (G ^ _)).trans (dvd_of_eq (eq i).symm))
  · intro i J prime regular r a fit hp hc
    rw [eq i] at hp
    have unit : toJet (G ^ multiplicity G (P i)) ∉ J := by
      rw [map_pow]
      exact fun bad => regular (prime.mem_of_pow_mem _ bad)
    exact ⟨native_strip prime r unit hp, native_power (hc H mem) fit⟩

end
end Lower6960.Prefix6969KnownHelper
end Z6969Source0583

-- Source: Research6969.PrefixMainPlan
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

-- Source: Research6969.PrefixMainGeometry
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
