import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.High6966FreeSources
import ProximityPrize.SubmissionLower.High6966RescueGeometry

section Merged6967_High6966Main13200
set_option Elab.async false




set_option Elab.async false
section Merged_R6960MainGeometry

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6960.High6966Main13200
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt seedHasse)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual orderOn FixedPart)
open K1_14_2_2R (chainCompatible)
open HelperPrefix (timesShape)

open MainPrefixSource (hasse_at_mark)
open Free6966 (bank reserve cutoff)
open Rescue6966 (Model Family word OnMark terminalShape contact_at_mark zero_of_contact)
open DifferentialContact (Native)
open PrefixRows (Prepared)
open P1_7_4 (ODEGuard degreeVector introJump introWeight)
open scoped Classical

def helperBank : P1_7.Bank := ⟨⟨382,531,115,8418⟩,1691195277312,2213398351⟩
def helperCutoff (h:ℕ) := helperBank.shape.m*179759-2*h*10-1
def copies (i:Fin 17) := (reserve i+11)/11
theorem reserve_small (i:Fin 17) : reserve i<K1.p := by fin_cases i <;> decide
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
  (Free6966.shape_guards i).2.2.2.1

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
    (lo : 2317≤M.overhead.toNat) (hi : M.overhead.toNat≤33697)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) 
    (nonzero : ∃ H∈evaluated Crt (word M) helperBank.shape (helperCutoff M.overhead.toNat), H≠0)
    (unique : ∀ G H, PrefixRows.Common (evaluated Crt (word M) helperBank.shape (helperCutoff M.overhead.toNat)) G →
      PrefixRows.Common (evaluated Crt (word M) helperBank.shape (helperCutoff M.overhead.toNat)) H →
      IsRelPrime G H → False) :
    Nonempty (Rows F Crt) := by
  choose P inside ne using Free6966.free_rows Crt (word M) lo hi
  obtain ⟨out⟩ := PrefixRows.prepare P freeShape copies _ _ ne
    (fun i => evaluated_shape Crt (word M) (inside i)) nonzero
    (fun Q hQ => evaluated_shape Crt (word M) hQ) unique
  refine ⟨⟨P,out,?_,?_,?_⟩⟩
  · intro i γ mem regular
    have fit : reserve i+1 ≤ copies i*11 := by unfold copies; omega
    refine out.contacts i _ (RingHom.ker_isPrime _) ?_ (reserve i+1) 11 fit ?_ ?_
    · intro van
      apply regular
      simpa only [K1_14_2.eval_toJet] using RingHom.mem_ker.mp van
    · exact contact_at_mark F Crt noPole residues (inside i) (Free6966.cutoff_fit lo hi i) γ mem
    · intro H hm
      have width : helperCutoff M.overhead.toNat+2*M.overhead.toNat*10 < helperBank.shape.m*179759 := by
        change 382*179759-2*M.overhead.toNat*10-1+2*M.overhead.toNat*10<382*179759
        omega
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
end Lower6960.High6966Main13200

end
end Merged_R6960MainGeometry

-- merged module R6960MainGeometryIntro
section Merged_R6960MainGeometryIntro

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.High6966Main13200
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
open Rescue6966 (Model Family OnMark label_injective zero_of_contact)
open Free6966 (reserve)
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
end Lower6960.High6966Main13200

end
end Merged_R6960MainGeometryIntro

-- merged module R6960MainGeometryProcess
section Merged_R6960MainGeometryProcess

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.High6966Main13200
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
open Rescue6966 (Model Family OnMark OnSurface SurfacePass TerminalPass word terminalShape terminalCutoff
  contact_at_mark zero_of_contact)
open MainPrefixSource (copies)
open Free6966 (reserve)
open HighCore82258_3 (envelope_caps)
open Lower6960.Rescue6966 (proper_cut)
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
    obtain ⟨s,C,sm,inside,cap,proper⟩ := Rescue6966.terminal_failure Crt (word M) hf
    refine ⟨C,cap,proper,?_⟩
    intro γ hγ _
    apply zero_of_contact (r:=0)
    exact contact_at_mark R.family Crt noPole
      (fun δ hd=>residues δ (mem_filter.mp hd).1) inside
      (by simpa only [Nat.mul_zero,Nat.add_zero] using Nat.sub_lt (Nat.mul_pos sm (by decide : 0<179759)) (by decide : 0<1)) γ hγ

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
end Lower6960.High6966Main13200

end
end Merged_R6960MainGeometryProcess

-- merged module R6960MainGeometryBills
section Merged_R6960MainGeometryBills

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

namespace Lower6960.High6966Main13200
open Finset Polynomial
open K1 (K)
open K1_14 (Jet atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass mass_mono weight dot CutCover emptyCut)
open P1_7_4 (Mass massQ massQ_mono dotQ pairedCap weightedBill bill_bound)
open Rescue6966 (Model Family OnMark label_injective)
open Free6966 (reserve)
open scoped Classical BigOperators

def initialMass : Mass := fun k=>initialCap k

private def historyTable : List Mass := [
  ![11571, 145906, 677513, 3740083],
  ![7468, 458551/4, 2085687/4, 6923805/2],
  ![32615/9, 499330/9, 2085687/4, 3168400],
  ![8897/4, 533669/16, 811675/3, 5216354/3],
  ![38331/25, 574908/25, 184815, 4204791/4],
  ![6434/7, 648439/49, 2963499/25, 715530],
  ![11133/20, 155043/20, 627183/8, 19773882/49],
  ![11133/20, 155043/20, 627183/8, 19773882/49],
  ![151714/289, 2106432/289, 262865/4, 368989],
  ![63549/128, 2106432/289, 262865/4, 368989],
  ![15209/36, 2106432/289, 262865/4, 368989],
  ![15209/36, 2106432/289, 262865/4, 91293210/289],
  ![309869/961, 5378142/961, 2600800/49, 91293210/289],
  ![309869/961, 5010507/961, 11188701/242, 5154012/23],
  ![89249/350, 5010507/961, 11188701/242, 5154012/23],
  ![89249/350, 118859934/26645, 24425192/625, 53259283/243],
  ![917478/3721, 118859934/26645, 24425192/625, 53259283/243]]
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

#print axioms Initial.cap_kept
end Lower6960.High6966Main13200
end
end Merged_R6960MainGeometryBills

end Merged6967_High6966Main13200

section Merged6967_High6966RescueCharge
set_option Elab.async false



set_option Elab.async false

-- merged module High6966RescueInvoice
section Merged_High6966RescueInvoice
noncomputable section
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 6000000
namespace Lower6960.Rescue6966
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open scoped Classical BigOperators

def degreeRates : List (List ℕ) := [[240581199, 166357446, 147594620, 141830813, 115868702, 125040083, 103653343, 85414642, 85978443, 107329102, 82412706, 104242841, 105573452, 110977224, 88658648, 120644258, 120806993], [231122934, 168483436, 139647913, 126953956, 116516030, 119684134, 104720145, 95265895, 83206231, 106205943, 114903361, 91768258, 128485925, 87539581, 126628628, 118039010, 113384579], [216220392, 146886458, 147501596, 127488378, 117024193, 111216792, 93306694, 97163094, 79452612, 111137166, 106833765, 84725969, 83609060, 114844052, 68512025, 103578534, 118175595], [172254134, 131086446, 123201469, 112202432, 103063160, 100707981, 84305447, 72122785, 67075006, 76231167, 91737976, 69063215, 98947613, 93113252, 97658014, 101068002, 98759530], [111073384, 91439732, 94152711, 87012268, 83314048, 78748356, 70214047, 65559695, 59330040, 76249651, 67622778, 61897396, 87378744, 93848511, 89923191, 118564911, 97371588], [53638752, 56818838, 56818838, 61869402, 60185882, 54688133, 51136955, 50479329, 52610036, 65657325, 52610036, 32881272, 42535214, 26305018, 26305018, 26305018, 72997247], [50479329, 47822522, 49716483, 45770730, 42614128, 45770730, 42614128, 48059267, 31566022, 47875132, 43087619, 42719349, 45770730, 41035828, 39773187, 36169399, 32944604], [50505635, 55240538, 51557835, 55240538, 51978715, 49979534, 50479329, 49979534, 39457527, 55240538, 48979943, 50505635, 59659781, 53662237, 52083936, 41844707, 31513077], [55240538, 52610036, 53662237, 50479329, 52610036, 52610036, 58449750, 49979534, 39457527, 57871040, 49979534, 35215843, 45139411, 52610036, 26568068, 39062952, 30934702], [104101051, 94018204, 88951997, 88876944, 82043678, 75171651, 57812562, 82644006, 56587866, 77027907, 55769061, 72749776, 65788440, 54860298, 54860298, 54860298, 100379580], [104842227, 90899544, 80108217, 83160782, 73435154, 84080296, 74974570, 60454892, 57473456, 49096806, 78894372, 49125276, 57208615, 53742457, 53742457, 53742457, 98783699], [95261265, 94692853, 84474435, 87278841, 81612824, 78907092, 58834403, 81373834, 52610036, 70213384, 64133172, 58767765, 52845227, 53103612, 53549861, 61979006, 97844981], [77629162, 78473534, 69261461, 74755702, 78892494, 61867214, 75801347, 65990984, 35906349, 51777851, 59219222, 45764629, 59060365, 39458742, 39458742, 44391085, 89957846], [61732569, 62206528, 65657325, 62500723, 62500723, 55240538, 66420170, 55792943, 39852102, 60185882, 47822522, 34525336, 47591826, 27817936, 27817936, 55635872, 80095962], [53662237, 49979534, 49716483, 45770730, 42614128, 45770730, 48059267, 45455071, 36892787, 53136136, 50479329, 32552459, 45139411, 42088029, 47980353, 49979534, 54862146], [47822522, 49979534, 46875542, 46875542, 46875542, 42259011, 43771550, 53136136, 32881272, 46402051, 43837313, 42088029, 56818839, 42259011, 41035827, 33210085, 34938498], [49979534, 47980353, 52610036, 49479739, 47980353, 50505635, 47822522, 49979534, 32881272, 45455071, 57450160, 56818839, 47822522, 47822522, 32881272, 37879226, 31738253], [52610036, 55240538, 52610036, 49979534, 52610036, 60185882, 52610036, 49979534, 39852102, 58449750, 45455071, 34870589, 45139411, 52610036, 39457527, 40601795, 30934702], [57148932, 61553742, 60606761, 56818838, 45770730, 45770731, 41430403, 57450160, 32881272, 49242993, 40601795, 28172674, 41035828, 44648022, 43936748, 40708413, 63858507], [57253215, 54714437, 55556198, 58002564, 48822114, 50347805, 54924877, 49979534, 42614129, 63132043, 52610036, 51557835, 73864491, 55220104, 37199887, 41604891, 63756218], [55768221, 54714437, 55556198, 56818838, 45770730, 45770730, 45770730, 49716483, 26568068, 40246677, 40601795, 34870589, 48296013, 40470769, 40086106, 49372554, 63365418], [52887627, 55556198, 55240538, 59028461, 57450160, 52610036, 62474418, 55792943, 34196523, 49242993, 62500723, 39062951, 51136955, 53136136, 51557835, 50717988, 57938533], [55792943, 53136136, 49979534, 49979534, 49979534, 57292330, 55240538, 47822522, 47349032, 61869402, 58449750, 40246678, 59659781, 42259011, 36169399, 46402051, 55654268], [49979534, 51557835, 49716483, 45770731, 42969247, 43771550, 50979125, 52083936, 34525336, 47822522, 57871040, 36531093, 48296013, 43837313, 52610036, 45455071, 47619466], [45455071, 47980353, 46954457, 45770730, 42614128, 45770730, 41956503, 44744835, 27620269, 40246677, 51136955, 45770731, 42535214, 52610036, 32881272, 41430403, 35691768], [47822522, 52083936, 49979534, 52610036, 50479329, 49979534, 50505635, 43837313, 59186290, 51136955, 41844707, 42088029, 51136955, 41844707, 42508909, 49242993, 32087266], [50479329, 50479329, 49979534, 53662237, 50479329, 49979534, 55240538, 49979534, 39457527, 55240538, 55240538, 33210085, 43837313, 45139411, 40483423, 37484651, 30486697], [45455071, 47980353, 46033781, 45770730, 39062951, 41035827, 45770730, 49716483, 26305018, 40246677, 31861952, 31566022, 40049390, 27896472, 26831118, 29889076, 48799239], [45455071, 47980353, 45573443, 40049390, 36531093, 37616175, 42614129, 45455071, 26305018, 35511774, 47822522, 26305018, 39457527, 49479739, 51557835, 41844707, 45331660], [49979534, 47822522, 46954457, 48059267, 42614128, 41035827, 43482195, 39062952, 39457527, 45455071, 52610036, 48979943, 31566022, 49979534, 31237208, 49979534, 47957466], [49979534, 49979534, 47875132, 45770730, 41956503, 41035827, 45770730, 46494119, 26305018, 38142276, 39062951, 36616586, 41193658, 57871040, 56818839, 39457527, 46768528], [48979943, 49479739, 45573443, 45770730, 42614128, 41035827, 45770730, 36531093, 31566022, 38984037, 51978715, 49242993, 40601795, 52610036, 39457527, 50505635, 45218875], [47349032, 47349032, 47875132, 42614128, 42614128, 42614128, 45770730, 46875542, 27357219, 39062951, 49242993, 48059267, 37859498, 53030916, 67472371, 52610036, 43372400], [45455071, 45455071, 45573443, 42614128, 41035828, 45770731, 44271346, 45139411, 32881272, 40246678, 52610036, 52610036, 41430403, 49979534, 32881272, 37879226, 35640193], [47822522, 49979534, 48979943, 48979943, 54135727, 49479739, 46402051, 52610036, 26305018, 42259011, 47822522, 45770731, 49242993, 43403280, 46494119, 40601795, 32644154], [47980353, 48979943, 49979534, 48979943, 49979534, 57871040, 52610036, 59659781, 27620269, 49242993, 37287363, 31566022, 45770730, 35215843, 34091304, 37484651, 30539235], [37287363, 34091304, 32039512, 31250362, 31237208, 35215843, 41035827, 42614128, 26305018, 39062951, 27357219, 26305018, 28935520, 40601795, 34870589, 41035827, 40563262], [37287363, 36616586, 33565203, 31861952, 30934702, 32881272, 38668375, 47875132, 26305018, 41035827, 29297214, 32881272, 39457527, 44271346, 39457527, 49479739, 40891544], [42259011, 41035827, 39062951, 37287363, 34870589, 41035827, 37616175, 27620269, 27357219, 31861952, 41430403, 37195295, 26305018, 40246678, 26305018, 42088029, 41573326], [41844707, 41035827, 41956503, 39062951, 37287363, 35215843, 39062951, 35906349, 36827025, 41035827, 26568068, 26305018, 30185008, 36734958, 40404508, 52610036, 40950142], [39457527, 39457526, 39062951, 36616586, 33565203, 33736185, 36892787, 39852101, 26305018, 30513821, 33538897, 28935520, 37859498, 52610036, 51557835, 54688133, 41608229], [47822522, 45455071, 45573443, 42614128, 41035827, 45770730, 45770730, 44271346, 27357219, 39062951, 46875542, 26305018, 34091304, 51136955, 39852102, 52610036, 40892676], [47349032, 47349032, 47875132, 45770730, 41035827, 39062951, 42614128, 38984037, 31566022, 45455071, 49479739, 26305018, 33144323, 36169399, 36090484, 45770731, 34737374], [47980353, 47980353, 49979534, 49979534, 47980353, 47822522, 52610036, 47980353, 39457527, 46402051, 52610036, 52610036, 41430403, 35215843, 34091304, 43482195, 34093874], [49979534, 47980353, 47980353, 51557835, 55240538, 50479329, 50479329, 47349032, 39457527, 55240538, 46402051, 33210085, 43837313, 37859498, 37879225, 49242993, 30641255], [34196523, 34091304, 31250362, 33210085, 30934702, 33565203, 32881272, 39062951, 27620269, 37616175, 26305018, 26305018, 36734958, 52610036, 52610036, 49979534, 37728967], [35215843, 34091304, 31250362, 31250362, 30513821, 31237208, 36892787, 31566021, 28935520, 38668375, 31549580, 28356810, 39457526, 27620269, 26568068, 36222009, 38569608], [35906349, 34091304, 31250362, 29829891, 29889076, 34870589, 39062951, 36531093, 28409419, 42614128, 32881272, 26568068, 34870589, 34180083, 32881272, 44271346, 39881796], [35906349, 34091304, 31250362, 31250362, 29514230, 33736185, 31237208, 44271346, 26305018, 39062951, 31861952, 32881272, 44271346, 29829891, 29829891, 36932245, 38784518], [47349032, 47980353, 46033781, 45770730, 41035827, 45770730, 45770730, 36531093, 28725080, 41035827, 41430403, 26305018, 28725080, 41035828, 34525336, 45139411, 37631018], [42259011, 40246678, 42614128, 42614128, 41956503, 41956503, 42614128, 42614128, 28409419, 41035827, 39457527, 46954457, 46494119, 35215843, 34091304, 45770731, 38097807], [42508909, 45455071, 44192430, 45770730, 41035827, 45770730, 45770730, 37859498, 26305018, 35511774, 49479739, 42969247, 49242993, 41016099, 38300106, 26305018, 34516271], [45455071, 47980353, 47980353, 50479329, 49479739, 45455071, 49979534, 49979534, 39457527, 52610036, 39457527, 33210085, 45139411, 44271346, 34525336, 53030916, 34763640], [49479739, 52610036, 52610036, 50479329, 49979534, 46402051, 55240538, 49479739, 39457527, 57871040, 50479329, 33210085, 43837313, 49979534, 72338800, 69050672, 32396793]]

def heightRates : List (List ℕ) := [[1526997, 2296958, 2609193, 2732231, 3382002, 3125396, 3803847, 4664611, 4631102, 3674007, 4843023, 3781239, 3735007, 3547252, 4486964, 3248387, 3243834], [1604830, 2261580, 2780134, 3071848, 3363891, 3275250, 3764655, 4158157, 4795862, 3713031, 3410838, 4330016, 3028985, 4543445, 3080950, 3321279, 3463608], [1727464, 2621289, 2610741, 3056895, 3349673, 3538928, 4252368, 4078014, 5028170, 3541695, 3691217, 4705540, 4771921, 3412899, 5864604, 3807007, 3317458], [2207049, 2968009, 3176839, 3504682, 3828778, 3928268, 4730533, 5562347, 5994946, 5250851, 4331544, 5814609, 4002630, 4262132, 4057107, 3913059, 4010576], [3543911, 4346597, 4209668, 4570060, 4789454, 5076851, 5714183, 6132395, 6802150, 5249573, 5945261, 6508109, 4551563, 4225022, 4423140, 3306565, 4069206], [7545060, 7112240, 7112240, 6510981, 6703550, 7395378, 7923731, 8027274, 7691794, 6123534, 7691794, 12428812, 9563872, 15585622, 15585622, 15585622, 5492785], [8027274, 8482476, 8153879, 8871683, 9546194, 8871683, 9546194, 8440568, 12956270, 8472518, 9440125, 9522623, 8871683, 9921115, 10242871, 11281538, 12403970], [8023133, 7316584, 7857463, 7316584, 7791196, 8108372, 8027274, 8108372, 10325475, 7316584, 8281296, 8023133, 6764161, 7541710, 7774628, 9724974, 12978325], [7316584, 7691794, 7541710, 8027274, 7691794, 7691794, 6903566, 8108372, 10325475, 6976972, 8108372, 11590237, 9001909, 7691794, 15428804, 10429379, 13223534], [3786166, 4216457, 4472158, 4475946, 4864955, 5324089, 6984490, 4829276, 7141933, 5195776, 7247196, 5512471, 6111642, 7370821, 7370821, 7370821, 3942140], [3760413, 4373862, 4982851, 4798563, 5457950, 4743914, 5337713, 6672558, 7028084, 8261079, 5066758, 8256154, 7062131, 7530268, 7530268, 7530268, 4009555], [4158352, 4182406, 4720489, 4556605, 4890562, 5065879, 6859251, 4904766, 7691794, 5714236, 6278742, 6866928, 7658247, 7621391, 7557739, 6499737, 4049209], [5154215, 5095848, 5796628, 5352903, 5066888, 6511206, 5280562, 6093270, 11366681, 7822822, 6814917, 8872942, 6833218, 10325157, 10325157, 9156272, 4421391], [6525360, 6476396, 6123534, 6446214, 6446214, 7316584, 6054342, 7244126, 10222220, 6703550, 8482476, 11829018, 8526139, 14725931, 14725931, 7264318, 4983699], [7541710, 8108372, 8153879, 8871683, 9546194, 8871683, 8440568, 8936796, 11057458, 7616752, 8027274, 12557791, 9001909, 9665972, 8454219, 8108372, 7370558], [8482476, 8108372, 8661710, 8661710, 8661710, 9625746, 9286915, 7616752, 12428812, 8751328, 9272183, 9665972, 7112240, 9625746, 9921115, 12303983, 11686145], [8108372, 8454219, 7691794, 8194834, 8454219, 8023133, 8482476, 8108372, 12428812, 8936796, 7031079, 7112240, 8482476, 8482476, 12428812, 10762738, 12884522], [7691794, 7316584, 7691794, 8108372, 7691794, 6703550, 7691794, 8108372, 10222220, 6903566, 8936796, 11709628, 9001909, 7691794, 10325475, 10026361, 13223534], [7069804, 6545962, 6655062, 7112240, 8871683, 8871683, 9825436, 7031079, 12428812, 8235790, 10026361, 14540087, 9921115, 9103271, 9249991, 10000508, 6306920], [7056398, 7391626, 7274561, 6960064, 8308599, 8047983, 7361610, 8108372, 9546194, 6381447, 7691794, 7857463, 5423797, 7319499, 10964627, 9783126, 6317413], [7247304, 7391626, 7274561, 7112240, 8871683, 8871683, 8871683, 8153879, 15428804, 10118966, 10026361, 11709628, 8399612, 10060324, 10160985, 8213377, 6357505], [7652199, 7274561, 7316584, 6836894, 7031079, 7691794, 6448913, 7244126, 11942724, 8235790, 6446214, 10429379, 7923731, 7616752, 7857463, 7989697, 6968295], [7244126, 7616752, 8108372, 8108372, 8108372, 7051369, 7316584, 8482476, 8572093, 6510981, 6903566, 10118965, 6764161, 9625746, 11281538, 8751328, 7261953], [8108372, 7857463, 8153879, 8871683, 9466642, 9286915, 7948581, 7774628, 11829018, 8482476, 6976972, 11166792, 8399612, 9272183, 7691794, 8936796, 8520908], [8936796, 8454219, 8646774, 8871683, 9546194, 8871683, 9697865, 9083301, 14834481, 10118966, 7923731, 8871683, 9563872, 7691794, 12428812, 9825436, 11436136], [8482476, 7774628, 8108372, 7691794, 8027274, 8108372, 8023133, 9272183, 6818711, 7923731, 9724974, 9665972, 7923731, 9724974, 9569765, 8235790, 12740265], [8027274, 8027274, 8108372, 7541710, 8027274, 8108372, 7316584, 8108372, 10325475, 7316584, 7316584, 12303983, 9272183, 9001909, 10057013, 10878548, 13421386], [8936796, 8454219, 8821030, 8871683, 10429379, 9921115, 8871683, 8153879, 15585622, 10118966, 12832992, 12956270, 10170593, 14684037, 15276796, 13693917, 8312557], [8936796, 8454219, 8912379, 10170593, 11166792, 10838790, 9546194, 8936796, 15585622, 11494397, 8482476, 15585622, 10325475, 8194834, 7857463, 9724974, 8962253], [8108372, 8482476, 8646774, 8440568, 9546194, 9921115, 9351734, 10429379, 10325475, 8936796, 7691794, 8281296, 12956270, 8108372, 13093246, 8108372, 8458179], [8108372, 8108372, 8472518, 8871683, 9697865, 9921115, 8871683, 8733902, 15585622, 10688658, 10429379, 11140949, 9882843, 6976972, 7112240, 10325475, 8681965], [8281296, 8194834, 8912379, 8871683, 9546194, 9921115, 8871683, 11166792, 12956270, 10451603, 7791196, 8235790, 10026361, 7691794, 10325475, 8023133, 8985518], [8572093, 8572093, 8472518, 9546194, 9546194, 9546194, 8871683, 8661710, 14978937, 10429379, 8235790, 8440568, 10768294, 7631760, 5958904, 7691794, 9376330], [8936796, 8936796, 8912379, 9546194, 9921115, 8871683, 9180971, 9001909, 12428812, 10118965, 7691794, 7691794, 9825436, 8108372, 12428812, 10762738, 11452830], [8482476, 8108372, 8281296, 8281296, 7474172, 8194834, 8751328, 7691794, 15585622, 9625746, 8482476, 8871683, 8235790, 9369413, 8733902, 10026361, 12521823], [8454219, 8281296, 8108372, 8281296, 8108372, 6976972, 7691794, 6764161, 14834481, 8235790, 10938185, 12956270, 8871683, 11590237, 11979109, 10878548, 13398184], [10938185, 11979109, 12759025, 13087766, 13093246, 11590237, 9921115, 9546194, 15585622, 10429379, 14978937, 15585622, 14151648, 10026361, 11709628, 9921115, 10036120], [10938185, 11140949, 12173064, 12832992, 13223534, 12428812, 10540499, 8472518, 15585622, 9921115, 13972997, 12428812, 10325475, 9180971, 10325475, 8194834, 9956101], [9625746, 9921115, 10429379, 10938185, 11709628, 9921115, 10838790, 14834481, 14978937, 12832992, 9825436, 10966015, 15585622, 10118965, 15585622, 9665972, 9790780], [9724974, 9921115, 9697865, 10429379, 10938185, 11590237, 10429379, 11366681, 11077337, 9921115, 15428804, 15585622, 13555595, 11105167, 10077664, 7691794, 9941892], [10325475, 10325475, 10429379, 11140949, 12173064, 12110029, 11057458, 10222221, 15585622, 13409407, 12182762, 14151648, 10768294, 7691794, 7857463, 7395378, 9782316], [8482476, 8936796, 8912379, 9546194, 9921115, 8871683, 8871683, 9180971, 14978937, 10429379, 8661710, 15585622, 11979109, 7923731, 10222220, 7691794, 9955827], [8572093, 8572093, 8472518, 8871683, 9921115, 10429379, 9546194, 10451603, 12956270, 8936796, 8194834, 15585622, 12328227, 11281538, 11307081, 8871683, 11755694], [8454219, 8454219, 8108372, 8108372, 8454219, 8482476, 7691794, 8454219, 10325475, 8751328, 7691794, 7691794, 9825436, 11590237, 11979109, 9351734, 11978220], [8108372, 8454219, 8454219, 7857463, 7316584, 8027274, 8027274, 8572093, 10325475, 7316584, 8751328, 12303983, 9272183, 10768294, 10762739, 8235790, 13353129], [11942724, 11979109, 13087766, 12303983, 13223534, 12173064, 12428812, 10429379, 14834481, 10838790, 15585622, 15585622, 11105167, 7691794, 7691794, 8108372, 10805054], [11590237, 11979109, 13087766, 13087766, 13409407, 13093246, 11057458, 12956270, 14151648, 10540499, 12963119, 14444119, 10325475, 14834481, 15428804, 11264509, 10568314], [11366681, 11979109, 13087766, 13721581, 13693917, 11709628, 10429379, 11166792, 14416700, 9546194, 12428812, 15428804, 11709628, 11948409, 12428812, 9180971, 10214450], [11366681, 11979109, 13087766, 13087766, 13869126, 12110029, 13093246, 9180971, 15585622, 10429379, 12832992, 12428812, 9180971, 13721581, 13721581, 11045531, 10507791], [8572093, 8454219, 8821030, 8871683, 9921115, 8871683, 8871683, 11166792, 14255591, 9921115, 9825436, 15585622, 14255591, 9921115, 11829018, 9001909, 10834304], [9625746, 10118965, 9546194, 9546194, 9697865, 9697865, 9546194, 9546194, 14416700, 9921115, 10325475, 8646774, 8733902, 11590237, 11979109, 8871683, 10701182], [9569765, 8936796, 9197249, 8871683, 9921115, 8871683, 8871683, 10768294, 15585622, 11494397, 8194834, 9466642, 8235790, 9925899, 10644211, 15585622, 11832153], [8936796, 8454219, 8454219, 8027274, 8194834, 8936796, 8108372, 8108372, 10325475, 7691794, 10325475, 12303983, 9001909, 9180971, 11829018, 7631760, 11746611], [8194834, 7691794, 7691794, 8027274, 8108372, 8751328, 7316584, 8194834, 10325475, 6976972, 8027274, 12303983, 9272183, 8108372, 5545163, 5815747, 12618851]]

def degreeRate (rect : Fin 54) (i : ℕ) : ℕ := (degreeRates.getD rect.val []).getD i 0

def heightRate (rect : Fin 54) (i : ℕ) : ℕ := (heightRates.getD rect.val []).getD i 0

private def heightTerms (a : ℕ) : List ℚ :=
  (List.range 80).map (fun i : ℕ =>
    let g := i+1
    max 0 (1-(a : ℚ)*(g : ℚ)/((p+1 : ℕ) : ℚ))*curveUnit g)

def heightBound (a : ℕ) : ℚ := (heightTerms a).foldr max 0

private theorem le_max_fold {q : ℚ} {terms : List ℚ} (mem : q∈terms) :
    q ≤ terms.foldr max 0 := by
  induction terms with
  | nil => simp at mem
  | cons a rest ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | h
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem height_spec (a g : ℕ) (pos : 0<g) (small : g≤80) :
    max 0 (1-(a : ℚ)*g/((p+1 : ℕ) : ℚ))*curveUnit g≤heightBound a := by
  apply le_max_fold
  unfold heightTerms
  apply List.mem_map.mpr
  refine ⟨g-1,List.mem_range.mpr (by omega),?_⟩
  dsimp only
  rw [Nat.sub_add_cancel (by omega : 1≤g)]

private theorem rate0 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 0 i.val : ℚ) ∧
    min (seedLimit 0) (dotQ (cutWeight 0 0 i.val) (history 0 i.val)) ≤ (degreeRate 0 i.val : ℚ) ∧
    heightBound (degreeRate 0 i.val) ≤ (heightRate 0 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate1 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 1 i.val : ℚ) ∧
    min (seedLimit 1) (dotQ (cutWeight 1 0 i.val) (history 1 i.val)) ≤ (degreeRate 1 i.val : ℚ) ∧
    heightBound (degreeRate 1 i.val) ≤ (heightRate 1 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate2 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 2 i.val : ℚ) ∧
    min (seedLimit 2) (dotQ (cutWeight 2 0 i.val) (history 2 i.val)) ≤ (degreeRate 2 i.val : ℚ) ∧
    heightBound (degreeRate 2 i.val) ≤ (heightRate 2 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate3 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 3 i.val : ℚ) ∧
    min (seedLimit 3) (dotQ (cutWeight 3 0 i.val) (history 3 i.val)) ≤ (degreeRate 3 i.val : ℚ) ∧
    heightBound (degreeRate 3 i.val) ≤ (heightRate 3 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate4 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 4 i.val : ℚ) ∧
    min (seedLimit 4) (dotQ (cutWeight 4 0 i.val) (history 4 i.val)) ≤ (degreeRate 4 i.val : ℚ) ∧
    heightBound (degreeRate 4 i.val) ≤ (heightRate 4 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate5 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 5 i.val : ℚ) ∧
    min (seedLimit 5) (dotQ (cutWeight 5 0 i.val) (history 5 i.val)) ≤ (degreeRate 5 i.val : ℚ) ∧
    heightBound (degreeRate 5 i.val) ≤ (heightRate 5 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate6 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 6 i.val : ℚ) ∧
    min (seedLimit 6) (dotQ (cutWeight 6 0 i.val) (history 6 i.val)) ≤ (degreeRate 6 i.val : ℚ) ∧
    heightBound (degreeRate 6 i.val) ≤ (heightRate 6 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate7 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 7 i.val : ℚ) ∧
    min (seedLimit 7) (dotQ (cutWeight 7 0 i.val) (history 7 i.val)) ≤ (degreeRate 7 i.val : ℚ) ∧
    heightBound (degreeRate 7 i.val) ≤ (heightRate 7 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate8 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 8 i.val : ℚ) ∧
    min (seedLimit 8) (dotQ (cutWeight 8 0 i.val) (history 8 i.val)) ≤ (degreeRate 8 i.val : ℚ) ∧
    heightBound (degreeRate 8 i.val) ≤ (heightRate 8 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate9 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 9 i.val : ℚ) ∧
    min (seedLimit 9) (dotQ (cutWeight 9 0 i.val) (history 9 i.val)) ≤ (degreeRate 9 i.val : ℚ) ∧
    heightBound (degreeRate 9 i.val) ≤ (heightRate 9 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate10 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 10 i.val : ℚ) ∧
    min (seedLimit 10) (dotQ (cutWeight 10 0 i.val) (history 10 i.val)) ≤ (degreeRate 10 i.val : ℚ) ∧
    heightBound (degreeRate 10 i.val) ≤ (heightRate 10 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate11 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 11 i.val : ℚ) ∧
    min (seedLimit 11) (dotQ (cutWeight 11 0 i.val) (history 11 i.val)) ≤ (degreeRate 11 i.val : ℚ) ∧
    heightBound (degreeRate 11 i.val) ≤ (heightRate 11 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate12 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 12 i.val : ℚ) ∧
    min (seedLimit 12) (dotQ (cutWeight 12 0 i.val) (history 12 i.val)) ≤ (degreeRate 12 i.val : ℚ) ∧
    heightBound (degreeRate 12 i.val) ≤ (heightRate 12 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate13 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 13 i.val : ℚ) ∧
    min (seedLimit 13) (dotQ (cutWeight 13 0 i.val) (history 13 i.val)) ≤ (degreeRate 13 i.val : ℚ) ∧
    heightBound (degreeRate 13 i.val) ≤ (heightRate 13 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate14 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 14 i.val : ℚ) ∧
    min (seedLimit 14) (dotQ (cutWeight 14 0 i.val) (history 14 i.val)) ≤ (degreeRate 14 i.val : ℚ) ∧
    heightBound (degreeRate 14 i.val) ≤ (heightRate 14 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate15 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 15 i.val : ℚ) ∧
    min (seedLimit 15) (dotQ (cutWeight 15 0 i.val) (history 15 i.val)) ≤ (degreeRate 15 i.val : ℚ) ∧
    heightBound (degreeRate 15 i.val) ≤ (heightRate 15 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate16 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 16 i.val : ℚ) ∧
    min (seedLimit 16) (dotQ (cutWeight 16 0 i.val) (history 16 i.val)) ≤ (degreeRate 16 i.val : ℚ) ∧
    heightBound (degreeRate 16 i.val) ≤ (heightRate 16 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate17 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 17 i.val : ℚ) ∧
    min (seedLimit 17) (dotQ (cutWeight 17 0 i.val) (history 17 i.val)) ≤ (degreeRate 17 i.val : ℚ) ∧
    heightBound (degreeRate 17 i.val) ≤ (heightRate 17 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate18 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 18 i.val : ℚ) ∧
    min (seedLimit 18) (dotQ (cutWeight 18 0 i.val) (history 18 i.val)) ≤ (degreeRate 18 i.val : ℚ) ∧
    heightBound (degreeRate 18 i.val) ≤ (heightRate 18 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate19 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 19 i.val : ℚ) ∧
    min (seedLimit 19) (dotQ (cutWeight 19 0 i.val) (history 19 i.val)) ≤ (degreeRate 19 i.val : ℚ) ∧
    heightBound (degreeRate 19 i.val) ≤ (heightRate 19 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate20 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 20 i.val : ℚ) ∧
    min (seedLimit 20) (dotQ (cutWeight 20 0 i.val) (history 20 i.val)) ≤ (degreeRate 20 i.val : ℚ) ∧
    heightBound (degreeRate 20 i.val) ≤ (heightRate 20 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate21 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 21 i.val : ℚ) ∧
    min (seedLimit 21) (dotQ (cutWeight 21 0 i.val) (history 21 i.val)) ≤ (degreeRate 21 i.val : ℚ) ∧
    heightBound (degreeRate 21 i.val) ≤ (heightRate 21 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate22 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 22 i.val : ℚ) ∧
    min (seedLimit 22) (dotQ (cutWeight 22 0 i.val) (history 22 i.val)) ≤ (degreeRate 22 i.val : ℚ) ∧
    heightBound (degreeRate 22 i.val) ≤ (heightRate 22 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate23 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 23 i.val : ℚ) ∧
    min (seedLimit 23) (dotQ (cutWeight 23 0 i.val) (history 23 i.val)) ≤ (degreeRate 23 i.val : ℚ) ∧
    heightBound (degreeRate 23 i.val) ≤ (heightRate 23 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate24 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 24 i.val : ℚ) ∧
    min (seedLimit 24) (dotQ (cutWeight 24 0 i.val) (history 24 i.val)) ≤ (degreeRate 24 i.val : ℚ) ∧
    heightBound (degreeRate 24 i.val) ≤ (heightRate 24 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate25 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 25 i.val : ℚ) ∧
    min (seedLimit 25) (dotQ (cutWeight 25 0 i.val) (history 25 i.val)) ≤ (degreeRate 25 i.val : ℚ) ∧
    heightBound (degreeRate 25 i.val) ≤ (heightRate 25 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate26 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 26 i.val : ℚ) ∧
    min (seedLimit 26) (dotQ (cutWeight 26 0 i.val) (history 26 i.val)) ≤ (degreeRate 26 i.val : ℚ) ∧
    heightBound (degreeRate 26 i.val) ≤ (heightRate 26 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate27 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 27 i.val : ℚ) ∧
    min (seedLimit 27) (dotQ (cutWeight 27 0 i.val) (history 27 i.val)) ≤ (degreeRate 27 i.val : ℚ) ∧
    heightBound (degreeRate 27 i.val) ≤ (heightRate 27 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate28 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 28 i.val : ℚ) ∧
    min (seedLimit 28) (dotQ (cutWeight 28 0 i.val) (history 28 i.val)) ≤ (degreeRate 28 i.val : ℚ) ∧
    heightBound (degreeRate 28 i.val) ≤ (heightRate 28 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate29 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 29 i.val : ℚ) ∧
    min (seedLimit 29) (dotQ (cutWeight 29 0 i.val) (history 29 i.val)) ≤ (degreeRate 29 i.val : ℚ) ∧
    heightBound (degreeRate 29 i.val) ≤ (heightRate 29 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate30 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 30 i.val : ℚ) ∧
    min (seedLimit 30) (dotQ (cutWeight 30 0 i.val) (history 30 i.val)) ≤ (degreeRate 30 i.val : ℚ) ∧
    heightBound (degreeRate 30 i.val) ≤ (heightRate 30 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate31 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 31 i.val : ℚ) ∧
    min (seedLimit 31) (dotQ (cutWeight 31 0 i.val) (history 31 i.val)) ≤ (degreeRate 31 i.val : ℚ) ∧
    heightBound (degreeRate 31 i.val) ≤ (heightRate 31 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate32 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 32 i.val : ℚ) ∧
    min (seedLimit 32) (dotQ (cutWeight 32 0 i.val) (history 32 i.val)) ≤ (degreeRate 32 i.val : ℚ) ∧
    heightBound (degreeRate 32 i.val) ≤ (heightRate 32 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate33 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 33 i.val : ℚ) ∧
    min (seedLimit 33) (dotQ (cutWeight 33 0 i.val) (history 33 i.val)) ≤ (degreeRate 33 i.val : ℚ) ∧
    heightBound (degreeRate 33 i.val) ≤ (heightRate 33 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate34 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 34 i.val : ℚ) ∧
    min (seedLimit 34) (dotQ (cutWeight 34 0 i.val) (history 34 i.val)) ≤ (degreeRate 34 i.val : ℚ) ∧
    heightBound (degreeRate 34 i.val) ≤ (heightRate 34 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate35 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 35 i.val : ℚ) ∧
    min (seedLimit 35) (dotQ (cutWeight 35 0 i.val) (history 35 i.val)) ≤ (degreeRate 35 i.val : ℚ) ∧
    heightBound (degreeRate 35 i.val) ≤ (heightRate 35 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate36 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 36 i.val : ℚ) ∧
    min (seedLimit 36) (dotQ (cutWeight 36 0 i.val) (history 36 i.val)) ≤ (degreeRate 36 i.val : ℚ) ∧
    heightBound (degreeRate 36 i.val) ≤ (heightRate 36 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate37 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 37 i.val : ℚ) ∧
    min (seedLimit 37) (dotQ (cutWeight 37 0 i.val) (history 37 i.val)) ≤ (degreeRate 37 i.val : ℚ) ∧
    heightBound (degreeRate 37 i.val) ≤ (heightRate 37 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate38 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 38 i.val : ℚ) ∧
    min (seedLimit 38) (dotQ (cutWeight 38 0 i.val) (history 38 i.val)) ≤ (degreeRate 38 i.val : ℚ) ∧
    heightBound (degreeRate 38 i.val) ≤ (heightRate 38 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate39 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 39 i.val : ℚ) ∧
    min (seedLimit 39) (dotQ (cutWeight 39 0 i.val) (history 39 i.val)) ≤ (degreeRate 39 i.val : ℚ) ∧
    heightBound (degreeRate 39 i.val) ≤ (heightRate 39 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate40 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 40 i.val : ℚ) ∧
    min (seedLimit 40) (dotQ (cutWeight 40 0 i.val) (history 40 i.val)) ≤ (degreeRate 40 i.val : ℚ) ∧
    heightBound (degreeRate 40 i.val) ≤ (heightRate 40 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate41 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 41 i.val : ℚ) ∧
    min (seedLimit 41) (dotQ (cutWeight 41 0 i.val) (history 41 i.val)) ≤ (degreeRate 41 i.val : ℚ) ∧
    heightBound (degreeRate 41 i.val) ≤ (heightRate 41 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate42 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 42 i.val : ℚ) ∧
    min (seedLimit 42) (dotQ (cutWeight 42 0 i.val) (history 42 i.val)) ≤ (degreeRate 42 i.val : ℚ) ∧
    heightBound (degreeRate 42 i.val) ≤ (heightRate 42 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate43 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 43 i.val : ℚ) ∧
    min (seedLimit 43) (dotQ (cutWeight 43 0 i.val) (history 43 i.val)) ≤ (degreeRate 43 i.val : ℚ) ∧
    heightBound (degreeRate 43 i.val) ≤ (heightRate 43 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate44 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 44 i.val : ℚ) ∧
    min (seedLimit 44) (dotQ (cutWeight 44 0 i.val) (history 44 i.val)) ≤ (degreeRate 44 i.val : ℚ) ∧
    heightBound (degreeRate 44 i.val) ≤ (heightRate 44 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate45 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 45 i.val : ℚ) ∧
    min (seedLimit 45) (dotQ (cutWeight 45 0 i.val) (history 45 i.val)) ≤ (degreeRate 45 i.val : ℚ) ∧
    heightBound (degreeRate 45 i.val) ≤ (heightRate 45 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate46 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 46 i.val : ℚ) ∧
    min (seedLimit 46) (dotQ (cutWeight 46 0 i.val) (history 46 i.val)) ≤ (degreeRate 46 i.val : ℚ) ∧
    heightBound (degreeRate 46 i.val) ≤ (heightRate 46 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate47 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 47 i.val : ℚ) ∧
    min (seedLimit 47) (dotQ (cutWeight 47 0 i.val) (history 47 i.val)) ≤ (degreeRate 47 i.val : ℚ) ∧
    heightBound (degreeRate 47 i.val) ≤ (heightRate 47 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate48 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 48 i.val : ℚ) ∧
    min (seedLimit 48) (dotQ (cutWeight 48 0 i.val) (history 48 i.val)) ≤ (degreeRate 48 i.val : ℚ) ∧
    heightBound (degreeRate 48 i.val) ≤ (heightRate 48 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate49 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 49 i.val : ℚ) ∧
    min (seedLimit 49) (dotQ (cutWeight 49 0 i.val) (history 49 i.val)) ≤ (degreeRate 49 i.val : ℚ) ∧
    heightBound (degreeRate 49 i.val) ≤ (heightRate 49 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate50 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 50 i.val : ℚ) ∧
    min (seedLimit 50) (dotQ (cutWeight 50 0 i.val) (history 50 i.val)) ≤ (degreeRate 50 i.val : ℚ) ∧
    heightBound (degreeRate 50 i.val) ≤ (heightRate 50 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate51 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 51 i.val : ℚ) ∧
    min (seedLimit 51) (dotQ (cutWeight 51 0 i.val) (history 51 i.val)) ≤ (degreeRate 51 i.val : ℚ) ∧
    heightBound (degreeRate 51 i.val) ≤ (heightRate 51 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate52 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 52 i.val : ℚ) ∧
    min (seedLimit 52) (dotQ (cutWeight 52 0 i.val) (history 52 i.val)) ≤ (degreeRate 52 i.val : ℚ) ∧
    heightBound (degreeRate 52 i.val) ≤ (heightRate 52 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem rate53 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 53 i.val : ℚ) ∧
    min (seedLimit 53) (dotQ (cutWeight 53 0 i.val) (history 53 i.val)) ≤ (degreeRate 53 i.val : ℚ) ∧
    heightBound (degreeRate 53 i.val) ≤ (heightRate 53 i.val : ℚ) := by
  fin_cases i <;> decide +kernel
private theorem checked_rates (rect : Fin 54) (i : Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate rect i.val : ℚ) ∧
    min (seedLimit rect) (dotQ (cutWeight rect 0 i.val) (history rect i.val)) ≤ (degreeRate rect i.val : ℚ) ∧
    heightBound (degreeRate rect i.val) ≤ (heightRate rect i.val : ℚ) := by
  fin_cases rect
  · exact rate0 i
  · exact rate1 i
  · exact rate2 i
  · exact rate3 i
  · exact rate4 i
  · exact rate5 i
  · exact rate6 i
  · exact rate7 i
  · exact rate8 i
  · exact rate9 i
  · exact rate10 i
  · exact rate11 i
  · exact rate12 i
  · exact rate13 i
  · exact rate14 i
  · exact rate15 i
  · exact rate16 i
  · exact rate17 i
  · exact rate18 i
  · exact rate19 i
  · exact rate20 i
  · exact rate21 i
  · exact rate22 i
  · exact rate23 i
  · exact rate24 i
  · exact rate25 i
  · exact rate26 i
  · exact rate27 i
  · exact rate28 i
  · exact rate29 i
  · exact rate30 i
  · exact rate31 i
  · exact rate32 i
  · exact rate33 i
  · exact rate34 i
  · exact rate35 i
  · exact rate36 i
  · exact rate37 i
  · exact rate38 i
  · exact rate39 i
  · exact rate40 i
  · exact rate41 i
  · exact rate42 i
  · exact rate43 i
  · exact rate44 i
  · exact rate45 i
  · exact rate46 i
  · exact rate47 i
  · exact rate48 i
  · exact rate49 i
  · exact rate50 i
  · exact rate51 i
  · exact rate52 i
  · exact rate53 i

theorem rate_spec (rect : Fin 54) {i : ℕ} (hi : i<17) :
    RateOK (degreeRate rect i) (heightRate rect i) ∧
      min (seedLimit rect) (dotQ (cutWeight rect 0 i) (history rect i)) ≤ degreeRate rect i := by
  obtain ⟨base,degree,height⟩ := checked_rates rect ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def lambda : ℚ := ((262144 : ℚ)/179759)*endpointDegree

def mu : ℚ := ((262144-endpointDegree : ℕ) : ℚ)/(179759-endpointDegree : ℕ)

def rankB (rect : Fin 54) : ℕ := initialCap rect 2+2

def rankJ (rect : Fin 54) : ℕ := initialCap rect 1+1

def tau : ℚ := 49/100

def rescueTau : Fin 54 → ℚ := ![0,0,0,0,0,107/625,33/200,331/1000,1909/5000,1211/5000,367/5000,659/2500,177/625,667/2500,937/5000,1109/5000,61/200,2187/5000,93/250,1413/5000,349/1250,186/625,587/2500,611/2500,1231/5000,189/500,1137/2500,191/625,411/1250,231/1250,847/5000,359/2500,63/250,643/2500,1901/5000,307/625,1537/5000,157/500,747/5000,181/1250,184/625,307/1250,659/2500,397/1000,2303/5000,881/2500,1601/5000,893/2500,809/2500,431/1250,184/625,191/500,1093/2500,613/1250]

def pivot (rect : Fin 54) : ℚ := (![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : Fin 54 → ℚ) rect

def rankWeight (rect : Fin 54) : Mass :=
  ![0,4*lambda*rankB rect*rescueTau rect+mu-4*lambda*pivot rect,
    4*lambda*rankJ rect*(1-rescueTau rect)+rankB rect,0]

def rankRound (rect : Fin 54) : ℚ :=
  rankWeight rect 1+2*rankWeight rect 2+2*lambda*pivot rect^2+1

def lossWeight (rect : Fin 54) (i : ℕ) : Mass :=
  fun k=>(degreeRate rect i : ℚ)*cutWeight rect 0 i k+(heightRate rect i : ℚ)*cutWeight rect 1 i k

def lossLimit (rect : Fin 54) : ℚ :=
  weightedBill 18 (beforeCuts (rankWeight rect) (lossWeight rect))
    (beforeCuts (initialMass rect) (history rect))+seedLimit rect+rankRound rect

def rescueFee (rect : Fin 54) : ℕ :=
  (lossLimit rect).ceil.toNat+(pointLimit rect).ceil.toNat+initialSeedLimit rect+initialCap rect 0

def paidCap : Fin 54 → ℕ := ![92610100963243990,90358823570671163,80170586702262012,61477414510372506,39295831866046273,15435969365880012,7214451125046820,6925828274602807,6306077059444644,35584831410235196,34124913332834259,32502133044203653,26841347699298545,19480561896717531,11121008686898504,6610284632259213,6671188754944467,6214698061610365,14136796512309709,13861532961091914,13649275768198341,12135845243725455,10535562518662936,8314232654019483,6128988906181846,6464571108244754,6249291093054034,8031123563385117,8209405599410345,8191924590225481,7839533479327399,7388062104987402,6810926732396973,5760174439848498,6127778983546109,6281101399543713,5617505585440675,5736751793132154,5928548349122789,5926936009212281,5961556271662637,5910531335684274,5489428533286829,5801510946411699,6149126784953953,4621585997943819,4673141435185573,4761783281351884,4926075113228897,5151670333708823,5384337433737958,5207160863916676,5577081789534753,5847153368777549]
def retainedCredit : Fin 54 → ℕ := ![1966757126305,2089493088750,1997341293528,2330068544742,2288329059737,2753396683095,5639420798540,5887582817645,5993674230270,2186532478300,2209399385115,2222849828685,2353141367710,2558999450370,3505727704210,5330167548730,5847015485405,5993674230270,3073985113195,3078184974930,3094232072930,3341015152205,3461089144180,3983573602410,5222716650680,5784640056410,6079358164345,3896447414015,4169057408100,3957266785410,4051190490280,4178869240875,4343902164000,5229885936305,5690312204290,6069310057475,4623871063870,4589862163440,4519614574510,4583824528670,4516018072165,4589745745260,5360095826990,5455853097490,6049798050175,4952080442295,4850890833080,4699883025460,4825021524430,4964608685930,4907682509695,5392997627335,5356187234400,5732210930305]
theorem rescue_fee_bound (r : Fin 54) : rescueFee r≤paidCap r := by
  fin_cases r <;> decide +kernel
theorem credit_guard (r : Fin 54) : (retainedCredit r:ℚ)≤
    P1_7_4.running (beforeCuts (rankWeight r) (lossWeight r)) 18 1 := by
  fin_cases r <;> decide +kernel
theorem rank_guard (rect : Fin 54) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel

#print axioms rate_spec
#print axioms rescue_fee_bound
#print axioms credit_guard

end Lower6960.Rescue6966

end
end Merged_High6966RescueInvoice

-- merged module High6966Credit
section Merged_High6966Credit

namespace Lower6960.Rescue6966
open P1_7_4 (Mass running dotQ massQ)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass)
theorem credit_one (v : ℕ → Mass) (n C : ℕ) (S : Finset (Ideal Ambient))
    (h : (C:ℚ)≤running v n 1) : (C:ℚ)*(mass S 1:ℚ)≤dotQ (running v n) (massQ S) := by
  have nonneg (i : ℕ) (k : Fin 4) : 0≤running v i k := by
    induction i with
    | zero => rfl
    | succ i ih => exact ih.trans (le_max_left _ _)
  exact (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)).trans
    (Finset.single_le_sum (f:=fun k => running v n k * massQ S k)
      (fun k _ => mul_nonneg (nonneg _ _) (Nat.cast_nonneg _)) (Finset.mem_univ 1))
#print axioms credit_one
end Lower6960.Rescue6966

end Merged_High6966Credit

-- merged module High6966RescueCharge
section Merged_High6966RescueCharge
section Merged_R6960Rescue6966Fee
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.Rescue6966
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
open Lower6960.Rescue6966 (persistentTotal persistentTop siteRatio density)
open scoped Classical BigOperators
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 54} (ini : Initial F G Q₀ rect) : Finset K :=
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
    {G Q₀ : Jet} {rect : Fin 54} (ini : Initial F G Q₀ rect) (hi : M.overhead.toNat≤2522) :
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
  have lin := fixed_fee_linear lambda mu (rescueTau rect) (pivot rect) (by decide +kernel) (by decide +kernel)
    (by fin_cases rect <;> decide +kernel) (by fin_cases rect <;> decide +kernel) hJB hB hJ
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
    (C : CutBooks R) (hiM : M.overhead.toNat≤2522) {i : ℕ} (hi : i<17) :
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
    (C : CutBooks R) (hi : M.overhead.toNat≤2522) : C.lossMarks.card + (retainedCredit R.rect)*K1_14_2_2.mass R.final 1 ≤ (lossLimit R.rect).ceil.toNat := by
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
  have joint := R.joint_bill_with_final (rankWeight R.rect) (lossWeight R.rect)
  have seed := C.seed_bill
  have total := cum.trans both
  have keep:=Lower6960.Rescue6966.credit_one (beforeCuts (rankWeight R.rect) (lossWeight R.rect)) 18 ((retainedCredit R.rect)) R.final (credit_guard R.rect)
  push_cast
  unfold lossLimit
  linarith only [total,joint,seed,keep]
def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G} (C : CutBooks R) :
    Finset K := ((C.lossMarks ∪ C.pointMarks) ∪ R.initial.seedMarks) ∪ R.initial.ordinateMarks
theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hi : M.overhead.toNat≤2522) : C.paid.card+(retainedCredit R.rect)*K1_14_2_2.mass R.final 1≤rescueFee R.rect := by
  have h1 := card_union_le ((C.lossMarks∪C.pointMarks)∪R.initial.seedMarks) R.initial.ordinateMarks
  have h2 := card_union_le (C.lossMarks∪C.pointMarks) R.initial.seedMarks
  have h3 := card_union_le C.lossMarks C.pointMarks
  have rate := C.loss_count hi
  have points := card_round C.point_bill
  have seeds := R.initial.seed_count
  have ordinates := R.initial.ordinate_count
  unfold rescueFee CutBooks.paid
  omega
theorem Run.paid_packet {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (C : CutBooks R) (S : Finset Surface),
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S,∃ J∈R.final,q.asIdeal=J.comap K1_14_2.toJet) ∧
      ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → γ∈C.paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨C⟩:=R.cutBooks noPole residues
  obtain ⟨S,geo,orig,surf⟩:=R.terminal_surfaces_with_origins
  refine ⟨C,S,geo,orig,?_⟩
  intro γ hγ zero
  rcases R.initial.covers γ hγ zero with seed | ordinate | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hγ,seed⟩)))
  · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨hγ,ordinate⟩))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hγ,rank⟩)))))
  · rcases R.retained_or_lost mem with final | ⟨i,hi,lost⟩
    · exact Or.inr (surf γ hγ ⟨J,final,on⟩)
    · rcases C.covers i hi γ hγ ⟨J,lost,on⟩ with point | ⟨Q,hQ,on⟩
      · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨i,mem_range.mpr hi,point⟩))))
      · have part : γ∈(range 17).biUnion (fun j => curveMarks F (C.cover j)) :=
          mem_biUnion.mpr ⟨i,mem_range.mpr hi,mem_curveMarks (F:=F) hγ hQ on⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ part))))
#print axioms CutBooks.paid_count
#print axioms Run.paid_packet
end Lower6960.Rescue6966
end
end Merged_R6960Rescue6966Fee

end Merged_High6966RescueCharge

end Merged6967_High6966RescueCharge
