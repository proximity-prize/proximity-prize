import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0556
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowPrefix
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PrefixMiddleGeometry
section Z6969Source0606
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960MainGeometry

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969Middle
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt seedHasse)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual orderOn FixedPart)
open K1_14_2_2R (chainCompatible)
open HelperPrefix (timesShape)
open Prefix6969Helper (helperBank helperCutoff)
open MainPrefixSource (hasse_at_mark)
open Far6969RescueGeometry (Model Family word OnMark contact_at_mark zero_of_contact)
open DifferentialContact (Native)
open PrefixRows (Prepared)
open P1_7_4 (ODEGuard degreeVector introJump introWeight)
open scoped Classical

def terminalShape : Shape := ⟨3000, 4184, 900, 530820⟩

def copies (i : Fin count) : ℕ := (reserve i + 11) / 11

theorem reserve_small (i : Fin count) : reserve i < K1.p := by
  fin_cases i <;> decide +kernel

def freeShape (i : Fin 14) : Shape := (bank i).shape

def movingShape (i : Fin 14) : Shape := timesShape (copies i) helperBank.shape

def stage (i : Fin 14) : P1_7.Stage := ⟨reserve i,bank i,⟨movingShape i,0,0⟩⟩

def cutShape (i : ℕ) : Shape :=
  if hi : i+1<14 then HighCore82258_3.envelope (stage ⟨i+1,hi⟩) else terminalShape

theorem cutShape_fit (i : ℕ) : (cutShape i).J≤(cutShape i).B := by
  unfold cutShape
  split
  · exact Nat.le_add_left _ _
  · decide

def introIndices : List (Fin 14) := [1,2,3,4,5,6,7,8,9]

def introAccount (k : Fin 4) : List (Fin 14) → (Fin 3→ℕ) → (Fin 3→ℕ) → ℕ
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

theorem free_ode_guard (i : Fin 14) : ODEGuard (freeShape i).B (freeShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem moving_ode_guard (i : Fin 14) : ODEGuard (movingShape i).B (movingShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem free_seed_small (i : Fin 14) : (freeShape i).U<K1.p := by
  fin_cases i <;> decide +kernel

theorem moving_seed_small (i : Fin 14) : (movingShape i).U<K1.p := by
  fin_cases i <;> decide +kernel

theorem reserve_pos {i : Fin 14} (hi : 0 < i.val) : 0<reserve i := by
  have checks (j : Fin 14) : (j.val=0) ∨ 0<reserve j := by
    fin_cases j <;> decide +kernel
  exact (checks i).resolve_left (by omega)

/-- The main branch retains the single preparation object, including the
original helper, its one possible exception, and the 14 stripped free rows. -/
structure Rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) where
  source : Fin 14→Jet
  out : Prepared source freeShape copies
    (evaluated Crt (word M) helperBank.shape (helperCutoff M.overhead.toNat)) helperBank.shape
  contact : ∀ i γ, γ∈Γ → jetAt out.exception (M.label γ) (F.scalar γ)≠0 →
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.helper^copies i)
  fixedFree : ∀ i, FixedPart (out.free i) (freeShape i)
  fixedMoving : ∀ i, FixedPart (out.helper^copies i) (movingShape i)

theorem rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2412≤M.overhead.toNat) (hi : M.overhead.toNat≤2557)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Nonempty (Rows F Crt) := by
  have loAll : 2314 ≤ M.overhead.toNat := (by decide : 2314 ≤ 2412).trans lo
  have hiAll : M.overhead.toNat ≤ 33755 := hi.trans (by decide)
  choose P inside nz using free_rows Crt (word M) lo hi
  obtain ⟨out⟩ := PrefixRows.prepare P freeShape copies _ _ nz
    (fun i => evaluated_shape Crt (word M) (inside i))
    (Prefix6969Helper.helper_nonzero Crt (word M) loAll hiAll)
    (fun Q hQ => evaluated_shape Crt (word M) hQ)
    (fun _ _ g h cop => Prefix6969Helper.helper_not_two Crt (word M) loAll hiAll
      g.1 h.1 cop g.2.1 h.2.1 g.2.2.1 h.2.2.1 g.2.2.2 h.2.2.2)
  refine ⟨⟨P,out,?_,?_,?_⟩⟩
  · intro i γ mem regular
    have fit : reserve i+1 ≤ copies i*11 := by
      change reserve i+1≤((reserve i+11)/11)*11
      omega
    refine out.contacts i _ (RingHom.ker_isPrime _) ?_ (reserve i+1) 11 fit ?_ ?_
    · intro van
      apply regular
      simpa only [K1_14_2.eval_toJet] using RingHom.mem_ker.mp van
    · exact contact_at_mark F Crt noPole residues (inside i) (cutoff_fit lo hi i) γ mem
    · intro H hm
      have wh := Prefix6969Helper.helper_width loAll hiAll
      have width : helperCutoff M.overhead.toNat+2*M.overhead.toNat*10 < helperBank.shape.m*179730 :=
        FreeSource.buffered_fit helperBank 179730 _ 10 wh
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
    (i : Fin 14) (γ : K) (mem : γ∈R.marks) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.helper^copies i) :=
  R.contact i γ (mem_filter.mp mem).1 (mem_filter.mp mem).2

theorem Rows.intro_tests {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 14) (j : Fin 2) (a : ℕ) (ha : a≤reserve i) (γ : K) (mem : γ∈R.marks) :
    jetAt (seedHasse j a (R.out.free i)) (M.label γ) (R.family.scalar γ)=0 :=
  hasse_at_mark (R.main_contact i γ mem).1 j a ha (ha.trans_lt (reserve_small i))

def Rows.Passes {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 14) (J : Ideal Ambient) : Prop :=
  orderOn J (R.out.free i) (reserve i+1) ∧
  orderOn J (R.out.helper^copies i) (reserve i+1) ∧ chainCompatible (R.out.free i) (R.out.helper^copies i) J

theorem Rows.failed_cut {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 14) {J : Ideal Ambient} (active : Active J) (dualJ : dual J) (fail : ¬R.Passes i J) :
    ∃ C : Jet,(RowCaps C (freeShape i) ∨ RowCaps C (movingShape i)) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  rcases PrefixStage.order_or_cut active dualJ (reserve_small i) (R.out.free_caps i) (R.out.moving_caps i)
    (pow_ne_zero _ R.out.helper_ne) (moving_ode_guard i).jpos with passes | ⟨C,cap,proper,zero⟩
  · exact (fail passes).elim
  · refine ⟨C,cap,proper,?_⟩
    intro γ hγ on
    obtain ⟨free,moving⟩ := R.main_contact i γ hγ
    exact zero _ _ on free moving

end Lower6960.Prefix6969Middle

end
end Merged_R6960MainGeometry

section Merged_R6960MainGeometryIntro

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969Middle
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

private theorem intro_components
    {P Q : Jet} (hQ : Q ≠ 0) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q (movingShape 0)) (later : Fin 14 → Jet)
    (rows : ∀ i, later i ≠ 0 ∧ RowCaps (later i) (freeShape i)) :
    ∀ (is : List (Fin 14)),
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
  (univ : Finset (Fin 14)).biUnion (fun i=>
    R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation)

theorem Rows.mem_fixed_free {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 14)
    (root : fixedAt (R.fixedFree i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_left _ (mem_filter.mpr ⟨mark,root⟩)⟩

theorem Rows.mem_fixed_moving {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 14)
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

end Lower6960.Prefix6969Middle

end
end Merged_R6960MainGeometryIntro

section Merged_R6960MainGeometryProcess

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969Middle
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
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) :=
  ini.parents.filter (fun J=>∀ i : Fin 14,0 < i.val → i.val≤n → R.Passes i J)

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
  (ini.kept 13).filter (TerminalPass Crt (word M))

def Initial.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := if n<14 then ini.kept n else ini.final

def Initial.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := ini.live n \ ini.live (n+1)

theorem Initial.live_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.live 0=ini.parents := by
  rw [Initial.live,ite_eq_left (by decide : 0<14),ini.kept_zero]

theorem Initial.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<14) : ini.live (i+1)⊆ini.live i := by
  by_cases hn : i+1<14
  · simp only [Initial.live,ite_eq_left hi,ite_eq_left hn]
    exact ini.kept_anti (Nat.le_succ _)
  · have eq : i=13 := by omega
    subst i
    exact filter_subset _ _

theorem Initial.stage_mass {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (i : Fin 14) (hi : 0 < i.val) {n : ℕ} (step : i.val≤n) (k : Fin 4) :
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
    {i : ℕ} {J : Ideal Ambient} (hi : i<14) (mem : J∈ini.lost i) :
    ∃ C : Jet,RowCaps C (cutShape i) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Initial.live,ite_eq_left hi] at prev
  by_cases hn : i+1<14
  · let j : Fin 14 := ⟨i+1,hn⟩
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
  · have eq : i=13 := by omega
    subst i
    have hf : ¬ TerminalPass Crt (word M) J := fun p =>
      lost (mem_filter.mpr ⟨prev,p⟩)
    obtain ⟨s,C,sm,inside,cap,proper⟩ := terminal_failure Crt (word M) hf
    refine ⟨C,cap,proper,?_⟩
    intro γ hγ _
    apply zero_of_contact (r:=0)
    exact contact_at_mark R.family Crt noPole
      (fun δ hd=>residues δ (mem_filter.mp hd).1) inside
      (by simpa only [Nat.mul_zero,Nat.add_zero] using Nat.sub_lt (Nat.mul_pos sm (by decide : 0<179730)) (by decide : 0<1)) γ hγ

theorem Initial.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<14) :
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
    J∈ini.final ∨ ∃ i<14,J∈ini.lost i := by
  by_cases h : ∃ i<14,J∈ini.lost i
  · exact Or.inr h
  · have alive : ∀ n≤14,J∈ini.live n := by
      intro n hn
      induction n with
      | zero => exact ini.live_zero.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Initial.live] using alive 14 le_rfl)

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

end Lower6960.Prefix6969Middle

end
end Merged_R6960MainGeometryProcess

section Merged_R6960MainGeometryBills

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969Middle
open Finset Polynomial
open K1 (K)
open K1_14 (Jet atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass mass_mono weight dot CutCover emptyCut)
open P1_7_4 (Mass massQ massQ_mono dotQ pairedCap weightedBill bill_bound)
open Far6969RescueGeometry (Model Family OnMark label_injective beforeCuts)
open Prefix6969MiddleRates (fixedFee fixed_count)
open scoped Classical BigOperators

def initialMass : Mass := fun k=>initialCap k

private abbrev historyTable := suppliedHistory

def history (i : ℕ) : Mass := historyTable.getD i initialMass

theorem history_zero (k : Fin 4) : history 0 k=initialMass k := by
  fin_cases k <;> decide +kernel

theorem history_step (i : Fin 13) (k : Fin 4) :
    let j : Fin 14 := ⟨i.val+1,by have := i.isLt; omega⟩
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
    {i : ℕ} (hi : i<14) (k : Fin 4) : massQ (ini.kept i) k≤history i k := by
  induction i with
  | zero => rw [history_zero]; exact ini.cap_initial _ _
  | succ i ih =>
    have hl : i<13 := by omega
    have hstep := history_step ⟨i,hl⟩ k
    dsimp only at hstep
    rw [hstep]
    exact le_min ((massQ_mono (ini.kept_anti (Nat.le_succ i)) k).trans (ih (by omega)))
      (ini.stage_mass ⟨i+1,hi⟩ (Nat.succ_pos _) le_rfl k)

theorem Initial.cap_live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<14) (k : Fin 4) : massQ (ini.live i) k≤history i k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_kept hi k

theorem Initial.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<14) (k : Fin 4) : massQ (ini.live i) k ≤ initialMass k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_initial _ k

def cutWeight (fee : Fin 3) (i : ℕ) : Mass := fun k=>weight (cutShape i) fee k

def seedLimit : ℚ := weightedBill 14 (cutWeight 0) history

def pointLimit : ℚ := weightedBill 14 (cutWeight 2) (fun _=>initialMass)

def initialSeedLimit : ℕ := (K1.p+1)*initialCap 2+initialCap 3

def contentLimit : ℕ := (K1.p+1)*(freeShape 0).U

def fixedLimit : ℕ :=
  ∑ i : Fin 14, (fixedFee (freeShape i).B (freeShape i).J+fixedFee (movingShape i).B (movingShape i).J)

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
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (hi : M.overhead.toNat≤2557) :
    R.fixedMarks.card≤fixedLimit := by
  calc
    _ ≤ ∑ i : Fin 14, (R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation).card :=
      card_biUnion_le
    _ ≤ _ := sum_le_sum fun i _=>(card_union_le _ _).trans (Nat.add_le_add
      (Prefix6969MiddleRates.fixed_count R.family hi (free_ode_guard i) _ (R.fixedFree i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2))
      (Prefix6969MiddleRates.fixed_count R.family hi (moving_ode_guard i) _ (R.fixedMoving i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2)))

structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) where
  cover : ℕ→CutCover
  cost : ∀ i<14,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))
  covers : ∀ i<14,∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark R.family Q γ

theorem Initial.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks ini) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<14 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    by_cases hi : i<14
    · obtain ⟨C,cap,cover⟩ := ini.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩

theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) {i : ℕ} (hi : i<14) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight fee i) (massQ (ini.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound

theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (∑ i∈range 14,((C.cover i).cost 0 : ℚ))≤seedLimit :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 14 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.cap_live hi))

def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K := (range 14).biUnion fun i=>(C.cover i).direct

theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (C.pointMarks.card : ℚ) ≤ pointLimit := by
  calc
    _ ≤ ∑ i∈range 14,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 14,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 14,dotQ (cutWeight 2 i) (massQ (ini.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 14 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
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
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 14,dotQ (cut i) (massQ (ini.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) 15) (massQ ini.final) ≤
      weightedBill 15 (beforeCuts rank cut) (beforeCuts (initialMass) (history)) := by
  have bill := P1_7_4.bill_bound_with_final 15 (beforeCuts rank cut) (beforeCuts (initialMass) (history))
    ini.jointLive ini.jointLost ?_ ?_ ?_
  · rw [show 15=14+1 by decide,sum_range_succ'] at bill
    have final : ini.jointLive 15 = ini.final := by simp [Initial.jointLive,Initial.live]
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


theorem Initial.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 14,dotQ (cut i) (massQ (ini.lost i))) ≤
      weightedBill 15 (beforeCuts rank cut) (beforeCuts initialMass history) :=
  (le_add_of_nonneg_right (P1_7_4.final_credit_nonneg 15 (beforeCuts rank cut) ini.final)).trans
    (ini.joint_bill_with_final rank cut)

end Lower6960.Prefix6969Middle

end
end Merged_R6960MainGeometryBills

section Merged_R6960MainGeometryInvoice

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969Middle
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open Far6969RescueGeometry (beforeCuts)
open Prefix6969MiddleRates (RateOK curveUnit endpointDegree)
open scoped Classical BigOperators

abbrev degreeRates := suppliedDegreeRates
abbrev heightRates := suppliedHeightRates

def lambda : ℚ := ((262144 : ℚ) / 179730) * endpointDegree
def mu : ℚ := ((262144 - endpointDegree : ℕ) : ℚ) / (179730 - endpointDegree : ℕ)
def tau : ℚ := 1 / 2

def degreeRate (i : ℕ) : ℕ := degreeRates.getD i 0

def heightRate (i : ℕ) : ℕ := heightRates.getD i 0

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

private theorem checked_rates (i : Fin 14) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate i.val : ℚ) ∧
      min seedLimit (dotQ (cutWeight 0 i.val) (history i.val)) ≤ (degreeRate i.val : ℚ) ∧
      heightBound (degreeRate i.val) ≤ (heightRate i.val : ℚ) := by
  fin_cases i <;> decide +kernel

theorem rate_spec {i : ℕ} (hi : i<14) :
    RateOK (degreeRate i) (heightRate i) ∧
      min seedLimit (dotQ (cutWeight 0 i) (history i)) ≤ degreeRate i := by
  obtain ⟨base,degree,height⟩ := checked_rates ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def rankB : ℕ := initialCap 2+2

def rankJ : ℕ := initialCap 1+1

def pivot : ℚ := min ((1/2 : ℚ) * rankJ) (tau*rankB)

def rankWeight : Mass :=
  ![0,4*lambda*rankB*tau+mu-4*lambda*pivot,4*lambda*rankJ*(1-tau)+rankB,0]

def rankRound : ℚ := rankWeight 1+2*rankWeight 2+2*lambda*pivot^2+1

def lossWeight (i : ℕ) : Mass :=
  fun k=>(degreeRate i : ℚ)*cutWeight 0 i k+(heightRate i : ℚ)*cutWeight 1 i k

def lossLimit : ℚ :=
  weightedBill 15 (beforeCuts rankWeight lossWeight) (beforeCuts initialMass history)+seedLimit+rankRound

def mainFee : ℕ := lossLimit.ceil.toNat+pointLimit.ceil.toNat+initialSeedLimit+initialCap 0+
  fixedLimit+contentLimit

theorem main_fee_exact : mainFee = prefixCap := by decide +kernel

theorem retained_credit_guard (k : Fin 4) :
    (retainedCredit k : ℚ) ≤ P1_7_4.running (beforeCuts rankWeight lossWeight) 15 k := by
  fin_cases k <;> decide +kernel

theorem rank_guard : rankB<p ∧ 0≤rankWeight 1 ∧ 0≤rankWeight 2 := by decide +kernel

end Lower6960.Prefix6969Middle

end
end Merged_R6960MainGeometryInvoice
end Z6969Source0606

-- Source: Research6969.PrefixMiddle
section Z6969Source0607
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960MainGeometryFee
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.Prefix6969Middle
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
open Prefix6969MiddleRates (curveMarks mem_curveMarks curve_tariff rated_curve_count fixedFee fixed_count
  persistentTotal persistentTop siteRatio density endpointDegree)
open P1_7_4_3 (mix)
open scoped Classical BigOperators
theorem fixedFee_eq (B J : ℕ) :
    fixedFee B J = (mix B J (mu+2*lambda*(B-1 : ℕ))
      (min (mu+2*lambda*(B-1 : ℕ)) (lambda*(2*J-1 : ℕ)))).ceil.toNat+B^2 := by
  have he : 2*density*(endpointDegree : ℚ)=2*lambda := by unfold lambda density; ring
  have hl : density*(endpointDegree : ℚ)=lambda := rfl
  have hm : siteRatio endpointDegree=mu := rfl
  unfold fixedFee persistentTop persistentTotal
  rw [he,hl,hm]
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>∃ J∈ini.rankExit,OnMark R.family J γ)
theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) (hi : M.overhead.toNat≤2557) :
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
  obtain ⟨small,cJ,cB⟩ := rank_guard
  have guard : ODEGuard B J := ⟨hB2,hJ1,hJB,hB.trans_lt small⟩
  have count : ini.rankMarks.card≤fixedFee B J :=
    Prefix6969MiddleRates.fixed_count R.family hi guard E ocaps (filter_subset _ _)
      (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau pivot (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤
      rankWeight 1 * J + rankWeight 2 * B + 2*lambda*pivot^2+1 := by
    rw [fixedFee_eq]
    exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ rankWeight (massQ ini.rankExit) =
      rankWeight 1 * (mass S 1 : ℚ)+rankWeight 2 * (mass S 2 : ℚ) := by
    simp [dotQ,rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,rankRound]
  linarith only [hjfee,hbfee]
private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)
theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hiM : M.overhead.toNat≤2557) {i : ℕ} (hi : i<14) :
    ((curveMarks R.family (C.cover i)).card : ℚ)≤
      dotQ (lossWeight i) (massQ (ini.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0))
      (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight 0 i) (history i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (ini.cap_live hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt seed_limit_small
  obtain ⟨ok,degree⟩ := rate_spec hi
  have count := rated_curve_count R.family (curve_tariff R.family hiM) ok (C.cover i)
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
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R} (C : CutBooks ini) :
    Finset K := ini.rankMarks ∪ (range 14).biUnion (fun i=>curveMarks R.family (C.cover i))
/-- The retained weight is charged on every component of the terminal parent mass. -/
def retainedCharge (S : Finset (Ideal Ambient)) : ℕ :=
  ∑ k : Fin 4, retainedCredit k * mass S k

theorem retainedCharge_cast_le (S : Finset (Ideal Ambient)) :
    (retainedCharge S : ℚ) ≤
      dotQ (P1_7_4.running (beforeCuts rankWeight lossWeight) 15) (massQ S) := by
  unfold retainedCharge dotQ massQ
  push_cast
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
    (retained_credit_guard k) (Nat.cast_nonneg _))

theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤2557) : C.lossMarks.card + retainedCharge ini.final ≤ lossLimit.ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (ini.rankMarks.card : ℚ) +
      ∑ i∈range 14,((curveMarks R.family (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ ini.rankMarks.card +
      ∑ i∈range 14,(curveMarks R.family (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem))
    (s:=range 14)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (ini.rank_count hi) sum_cuts
  have joint := ini.joint_bill_with_final rankWeight lossWeight
  have seed := C.seed_bill
  have total := cum.trans both
  have retained := retainedCharge_cast_le ini.final
  push_cast
  unfold lossLimit
  linarith only [total, joint, seed, retained]
def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)
def Initial.contentMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)
def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K :=
  (C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks) ∪ (R.fixedMarks ∪ ini.contentMarks)
theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤2557) : C.paid.card + retainedCharge ini.final ≤ mainFee := by
  have combined := card_union_le
    ((C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks)) (R.fixedMarks ∪ ini.contentMarks)
  have left := card_union_le (C.lossMarks ∪ C.pointMarks) (ini.seedMarks ∪ ini.ordinateMarks)
  have cuts := card_union_le C.lossMarks C.pointMarks
  have low := card_union_le ini.seedMarks ini.ordinateMarks
  have fixed := card_union_le R.fixedMarks ini.contentMarks
  have loss := C.loss_count hi
  have points := card_round C.point_bill
  have seeds : ini.seedMarks.card ≤ initialSeedLimit := ini.seed_count
  have ordinates : ini.ordinateMarks.card ≤ initialCap 0 := ini.ordinary_count
  have content : ini.contentMarks.card ≤ contentLimit := ini.content_count
  have fixedCard := R.fixed_count hi
  unfold mainFee CutBooks.paid
  omega
theorem Rows.main_prefix {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (hi : M.overhead.toNat≤2557) (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (ini : Initial R) (C : CutBooks ini) (S : Finset Surface),
      C.paid.card + retainedCharge ini.final ≤ prefixCap ∧
      (∀ k, massQ ini.final k ≤ history 13 k) ∧
      (∀ q∈S, Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S, ∃ J∈ini.final, q.asIdeal = J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks, γ∈C.paid ∨ ∃ q∈S, OnSurface F q γ := by
  obtain ⟨ini⟩ := R.initial_cover
  obtain ⟨C⟩ := ini.cutBooks noPole residues
  obtain ⟨S, geom, origin, surface⟩ := ini.terminal_surfaces_with_origins
  refine ⟨ini, C, S, main_fee_exact ▸ C.paid_count hi, ?_, geom, origin, ?_⟩
  intro k
  exact (massQ_mono (filter_subset _ _) k).trans (ini.cap_kept (by decide) k)
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
      · have mark : γ∈(range 14).biUnion (fun i=>curveMarks R.family (C.cover i)) :=
          mem_biUnion.mpr ⟨i,mem_range.mpr hi,mem_curveMarks (F:=R.family) hγ hQ hmark⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ mark))))
/-- Construct the actual wide prefix from the model's CRT data and the verified banks. -/
theorem main_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2412 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2557)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (R : Rows F Crt) (ini : Initial R) (C : CutBooks ini) (S : Finset Surface),
      C.paid.card + retainedCharge ini.final ≤ prefixCap ∧
      (∀ k, massQ ini.final k ≤ history 13 k) ∧
      (∀ q∈S, Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S, ∃ J∈ini.final, q.asIdeal = J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks, γ∈C.paid ∨ ∃ q∈S, OnSurface F q γ := by
  obtain ⟨R⟩ := rows F Crt lo hi noPole residues
  obtain ⟨ini, C, S, paid, massCap, regular, origins, covered⟩ :=
    R.main_prefix hi noPole residues
  exact ⟨R, ini, C, S, paid, massCap, regular, origins, covered⟩

end Lower6960.Prefix6969Middle

end
end Merged_R6960MainGeometryFee
end Z6969Source0607

-- Source: Research6969.PrefixMainBand
section Z6969Source0608
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969Main
noncomputable section

open Finset
open K1 (K p)
open K1_14_2 (ODE fixedAt)
open K1_14_2_2 (ODECaps CutCover)
open P1_7_4 (ODEGuard)
open P1_7_4_3 (mix)
open Far6969RescueGeometry (Model Family)

inductive Band
  | near
  | middle

namespace Band

def last : Band → ℕ
  | near => 2411
  | middle => 2557

def lambda (b : Band) : ℚ := ((262144 : ℚ) / 179730) * (131071+b.last : ℕ)
def mu (b : Band) : ℚ := ((262144 - (131071+b.last) : ℕ) : ℚ) / (179730 - (131071+b.last) : ℕ)

def fixedFee : Band → ℕ → ℕ → ℕ
  | near => Prefix6969Rates.fixedFee
  | middle => Prefix6969MiddleRates.fixedFee

theorem fixedFee_eq (b : Band) (B J : ℕ) :
    b.fixedFee B J = (mix B J (b.mu+2*b.lambda*(B-1 : ℕ))
      (min (b.mu+2*b.lambda*(B-1 : ℕ)) (b.lambda*(2*J-1 : ℕ)))).ceil.toNat+B^2 := by
  cases b
  · exact Prefix6969Wide.fixedFee_eq B J
  · exact Prefix6969Middle.fixedFee_eq B J

theorem lambda_nonneg (b : Band) : 0 ≤ b.lambda := by cases b <;> decide +kernel
theorem mu_nonneg (b : Band) : 0 ≤ b.mu := by cases b <;> decide +kernel

theorem fixed_count (b : Band) {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat ≤ b.last) {B J : ℕ} (guard : ODEGuard B J)
    (G : ODE) (caps : ODECaps G B J) {T : Finset K} (hT : T⊆Γ)
    (roots : ∀ γ∈T, fixedAt G (F.scalar γ)=0) : T.card ≤ b.fixedFee B J := by
  cases b
  · exact Prefix6969Rates.fixed_count F hi guard G caps hT roots
  · exact Prefix6969MiddleRates.fixed_count F hi guard G caps hT roots

def curveUnit : Band → ℕ → ℚ
  | near => Prefix6969Rates.curveUnit
  | middle => Prefix6969MiddleRates.curveUnit

structure RateOK (b : Band) (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ)/81 ≤ a
  height : 0 ≤ h
  interpolation : ∀ g : ℕ, 0 < g → g ≤ 80 →
    max 0 (1-a*g/((p+1 : ℕ) : ℚ))*b.curveUnit g ≤ h

theorem curve_count (b : Band) {u del} {M : Model u del} {Γ}
    (F : Family M Γ) (hi : M.overhead.toNat ≤ b.last)
    {a h globalCap : ℚ} (hu : b.RateOK a h) (C : CutCover)
    (hglobal : (C.cost 0 : ℚ) ≤ globalCap)
    (hdegree : min globalCap (C.cost 0 : ℚ) ≤ a) (hp : C.cost 0 < p) :
    ((Prefix6969Rates.curveMarks F C).card : ℚ) ≤ a*(C.cost 0 : ℚ)+h*(C.cost 1 : ℚ)+C.cost 0 := by
  cases b
  · exact Prefix6969Rates.rated_curve_count F (Prefix6969Rates.curve_tariff F hi)
      ⟨hu.degree, hu.height, hu.interpolation⟩ C hglobal hdegree hp
  · exact Prefix6969MiddleRates.rated_curve_count F (Prefix6969MiddleRates.curve_tariff F hi)
      ⟨hu.degree, hu.height, hu.interpolation⟩ C hglobal hdegree hp

end Band

end
end Lower6960.Prefix6969Main
end Z6969Source0608

-- Source: Research6969.PrefixMainBills
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

-- Source: Research6969.PrefixMainPricing
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

-- Source: Research6969.PrefixMainSource
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
open Prefix6969KnownHelper
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

-- Source: Research6969.PrefixMainInvoice
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
open Prefix6969Rates (curveMarks mem_curveMarks)
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

-- Source: Research6969.PrefixMainProducer
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

-- Source: Research6969.PrefixRescue
section Z6969Source0614
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969Rescue

noncomputable section

open Finset Polynomial
open K1 (I K)
open K1_14 (L FX Shape Jet jetAt atX liftPoly triangle shapeSum)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom UsesSeed ODE)
open K1_14_2_2 (RowCaps Active dual Fits mass sectionDegree ordinateIncl ODECaps fixedOn)
open K1_14_2_2_2 (length_le_mass ordinate_eq)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open Far6969RescueGeometry (Model Family word OnMark contact_at_mark zero_of_contact)
open DifferentialContact (Native)
open P0_10R_1 (seed_projection section_bound component_height)
open P1_7_4_1 (irreducible_cut)
open Research6966
open Research6966.HelperAvoidance (debitAt triSlots)
open scoped Classical BigOperators

structure Plan where
  count : ℕ
  positive : 0 < count
  primeShape : Shape
  bank : Fin count → P1_7.Bank
  reserve : Fin count → ℕ
  reserve_zero : reserve ⟨0, positive⟩ = 0
  reserve_small : ∀ i, reserve i < K1.p
  prime_fit : primeShape.J ≤ primeShape.B
  stage_fit : ∀ i, (bank i).shape.J ≤ (bank i).shape.B
  initial_small : ∀ k, pairCap primeShape (bank ⟨0, positive⟩).shape k < K1.p
  degree : ℕ
  slopeFloor : ℕ
  physicalFloor : ℕ
  seedFloor : ℕ

namespace Plan

def first (plan : Plan) : Fin plan.count := ⟨0, plan.positive⟩

def initialCap (plan : Plan) : Fin 4 → ℕ :=
  pairCap plan.primeShape (plan.bank plan.first).shape

def top (plan : Plan) (h : ℕ) (i : Fin plan.count) : ℕ :=
  HelperSource.cutoffCount (plan.bank i).shape 179730 h (plan.reserve i)

def cutoff (plan : Plan) (h : ℕ) (i : Fin plan.count) : ℕ :=
  plan.top h i - 1

def surplus (plan : Plan) (h : ℕ) (i : Fin plan.count) : Prop :=
  let bank := plan.bank i
  let W := plan.top h i
  P1_7.debit h bank +
    (∑ d ∈ range W, debitAt bank.shape h W d plan.degree plan.slopeFloor plan.physicalFloor
      (triSlots bank.shape.U plan.seedFloor)) <
    triangle bank.shape.U * shapeSum bank.shape
      (fun q j => W + j - q * (131071 - h))

structure Ready (plan : Plan) (h : ℕ) : Prop where
  hpos : 0 < h
  hmax : h ≤ 131070
  rank : ∀ i, P3_7_1.BankOK (plan.bank i)
  seed_small : ∀ i, (plan.bank i).shape.U < K1.p
  wide : ∀ i, HelperSource.WidthGuard (plan.bank i) 179730 h (plan.reserve i)
  margin : ∀ i, plan.surplus h i

theorem Ready.avoid {plan : Plan} {h : ℕ} (ready : plan.Ready h)
    {D : PoleData h} (Crt : CRTLift D) (w : I → L) {G : Jet}
    (phys : HelperPhysicalModel.Model Crt G) (irr : Irreducible G)
    (slope : 0 < G.natDegree) (seeded : UsesSeed G)
    (degree : plan.degree ≤ jetDegree G) (slopeFloor : plan.slopeFloor ≤ G.natDegree)
    (physicalFloor : plan.physicalFloor ≤ RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw)
    (seedFloor : plan.seedFloor ≤ seedDegree G) (i : Fin plan.count) :
    ∃ Q ∈ evaluated Crt w (plan.bank i).shape (plan.cutoff h i), ¬ G ∣ Q := by
  have wide := ready.wide i
  exact Research6966.HelperAvoidance.triangle_avoiding ready.hpos ready.hmax Crt w
    (plan.bank i) phys irr slope seeded (ready.seed_small i) degree slopeFloor physicalFloor
    seedFloor (ready.rank i).moment.2 ((Nat.zero_le _).trans_lt wide) wide.le
    (ready.rank i).nodes (ready.rank i).moment.1 (ready.margin i)

end Plan

private theorem initial_sections {G Q : Jet} {s t : Shape} (irr : Irreducible G)
    (avoid : ¬G∣Q) (gs : RowCaps G s) (qs : RowCaps Q t) (js : s.J≤s.B) (jt : t.J≤t.B) :
    ∃ A : Finset (Ideal Ambient), P1_7_4_1.SectionGeometry A ∧ Fits A (pairCap s t) ∧
      (∀ J∈A,toJet G∈J ∧ toJet Q∈J) ∧
      ∀ z S,jetAt G z S=0 → jetAt Q z S=0 → ∃ J∈A,OnJet J z S := by
  have proper := irreducible_cut irr avoid
  obtain ⟨A,geom,cover⟩ := K1_14_2_2_2_3.proof _ _ proper
  obtain ⟨finite,fit⟩ := section_bound _ _ proper s t js jt gs qs A geom
  refine ⟨A,?_,fit,fun J mem=>(geom J mem).2.2,cover⟩
  intro J mem
  obtain ⟨prime,dim,g,q⟩ := geom J mem
  exact ⟨prime,dim,component_height proper prime dim g q,finite J mem⟩
structure Initial {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (G Q₀ : Jet) (plan : Plan) where
  seeds : SeedCover
  seed_degree : seeds.curve.totalDegree ≤ plan.initialCap 2
  seed_points : seeds.points.card ≤ plan.initialCap 3
  ordinates : Finset FX
  ordinate_card : ordinates.card ≤ plan.initialCap 0
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet Q₀∈J
  disjoint : Disjoint rankExit parents
  fits : Fits (rankExit∪parents) (plan.initialCap)
  covers : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
    seeds.Covers (M.label γ) ∨ atX (F.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark F J γ) ∨ ∃ J∈parents,OnMark F J γ
private theorem classify {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {plan : Plan} {A : Finset (Ideal Ambient)}
    (geom : P1_7_4_1.SectionGeometry A) (fit : Fits A (plan.initialCap))
    (rows : ∀ J∈A,toJet G∈J ∧ toJet Q₀∈J)
    (cover : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → ∃ J∈A,OnMark F J γ) :
    Nonempty (Initial F G Q₀ plan) := by
  classical
  let noSeeds := A.filter (fun J=>sectionDegree J 0=0)
  let constY := A.filter (fun J=>0<sectionDegree J 0 ∧
    ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := A.filter (fun J=>0<sectionDegree J 0 ∧
    Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>¬dual J)
  let parents := active.filter dual
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (plan.initial_small k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,
      ⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧
        (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) := (Γ.filter (OnMark F J)).image fun γ=>atX (F.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos
    apply card_le_one.mpr
    intro y hy z hz
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy
    obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · intro J mem
    exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2⟩
  · intro J mem
    obtain ⟨hin,d⟩ := mem_filter.mp mem
    obtain ⟨act,ht⟩ := geomActive J hin
    exact ⟨act,d,ht,rows J (mem_filter.mp hin).1⟩
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2 (mem_filter.mp b).2
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _))
      ((filter_subset _ _).trans (filter_subset _ _))
  · intro γ hγ zero
    obtain ⟨J,hin,on⟩ := cover γ hγ zero
    by_cases z : sectionDegree J 0=0
    · have mem : J∈noSeeds := mem_filter.mpr ⟨hin,z⟩
      exact Or.inl (joinCovers_covers mem ((seed_spec J mem).2.2 _ _ on))
    · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
      · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        by_cases d : dual J
        · exact Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
      · have mem : J∈constY := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        exact Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem,
          mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))
theorem initial_cover {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {plan : Plan} (irr : Irreducible G) (avoid : ¬G∣Q₀)
    (capsG : RowCaps G (plan.primeShape)) (capsQ : RowCaps Q₀ (plan.bank plan.first).shape)
    (zero : ∀ γ∈Γ,jetAt Q₀ (M.label γ) (F.scalar γ)=0) :
    Nonempty (Initial F G Q₀ plan) := by
  obtain ⟨A,geom,fit,rows,cover⟩ := initial_sections irr avoid capsG capsQ (plan.prime_fit)
    (plan.stage_fit plan.first)
  exact classify F geom fit rows (fun γ hγ hG => cover _ _ hG (zero γ hγ))
theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {plan : Plan} (initial : Initial F G Q₀ plan) :
    ∃ E : ODE, ODECaps E (mass initial.rankExit 2) (mass initial.rankExit 1) ∧
      ∀ γ∈Γ,(∃ J∈initial.rankExit,OnMark F J γ) → K1_14_2.fixedAt E (F.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation initial.rankExit initial.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))

theorem history_from_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G : Jet} {plan : Plan} (irr : Irreducible G) (capsG : RowCaps G (plan.primeShape))
    (Q : Fin plan.count→Jet) (init : Initial F G (Q plan.first) plan) (avoid : ∀ i,¬G∣Q i)
    (caps : ∀ i,RowCaps (Q i) (plan.bank i).shape)
    (contact : ∀ i γ,γ∈Γ → Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ)))
      (plan.reserve i+1) (Q i)) :
    ∃ kept : ℕ→Finset (Ideal Ambient),
      kept 0=init.parents ∧ kept 1=init.parents ∧ Antitone kept ∧
      (∀ i : Fin plan.count,∀ n,i.val<n → ∀ J∈kept n,Native J (plan.reserve i+1) (Q i)) ∧
      (∀ i : Fin plan.count,∀ n,i.val<n → ∀ c : Fin 4,
        (plan.reserve i+1)*mass (kept n) c≤pairCap (plan.primeShape) (plan.bank i).shape c) ∧
      ∀ i : Fin plan.count,∀ J∈kept i.val,J∉kept (i.val+1) →
        ∃ C : Jet,RowCaps C (plan.bank i).shape ∧ toJet C∉J ∧
          ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  have on (J : Ideal Ambient) (mem : J∈init.parents) : Active J ∧ dual J ∧ toJet G∈J :=
    let h := init.parent_geom J mem
    ⟨h.1,h.2.1,h.2.2.2.1⟩
  choose S sub pass bound cut using fun i =>
    ExceptionalStage.filter irr (avoid i) capsG (caps i) plan.prime_fit
      (plan.stage_fit i) init.parents on (plan.reserve i) (plan.reserve_small i)
  let selected (i : Fin plan.count) := if i = plan.first then init.parents else S i
  have first : selected plan.first=init.parents := by simp [selected]
  have rzero : plan.reserve plan.first=0 := plan.reserve_zero
  have contact_zero (J : Ideal Ambient) (mem : J∈init.parents) : Native J (plan.reserve plan.first+1) (Q plan.first) := by
    intro w hw
    have hz : w.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp hz]
    exact (init.parent_geom J mem).2.2.2.2
  have sel_pass (i : Fin plan.count) (J : Ideal Ambient) (mem : J∈selected i) :
      Native J (plan.reserve i+1) (Q i) := by
    by_cases zi : i = plan.first
    · subst i; exact contact_zero J (first ▸ mem)
    · exact pass i J (by simpa only [selected,ite_eq_right zi] using mem)
  have sel_bound (i : Fin plan.count) (c : Fin 4) :
      (plan.reserve i+1)*mass (selected i) c≤pairCap (plan.primeShape) (plan.bank i).shape c := by
    by_cases zi : i = plan.first
    · subst i
      rw [rzero, Nat.zero_add, first, one_mul]
      exact K1_14_2_2.mass_mono (subset_union_right (s₁:=init.rankExit) (s₂:=init.parents)) c
        |>.trans (init.fits c)
    · simpa only [selected,ite_eq_right zi] using bound i c
  let kept (n : ℕ) := init.parents.filter (fun J=>∀ i : Fin plan.count,i.val<n → J∈selected i)
  have spec {J n} : J∈kept n ↔ J∈init.parents ∧ ∀ i : Fin plan.count,i.val<n → J∈selected i := mem_filter
  refine ⟨kept,?_,?_,?_,?_,?_,?_⟩
  · ext J; simp [kept]
  · ext J
    refine ⟨fun h=>(spec.mp h).1,fun h=>spec.mpr ⟨h,?_⟩⟩
    intro i hi
    have zi : i = plan.first := Fin.ext (by change i.val = 0; omega)
    subst i
    exact first.symm ▸ h
  · intro n m h J mem
    exact spec.mpr ⟨(spec.mp mem).1,fun i hi=>(spec.mp mem).2 i (hi.trans_le h)⟩
  · intro i n hi J mem
    exact sel_pass i J ((spec.mp mem).2 i hi)
  · intro i n hi c
    have hsub : kept n⊆selected i := fun _ mem=>(spec.mp mem).2 i hi
    exact (Nat.mul_le_mul_left _ (K1_14_2_2.mass_mono hsub c)).trans (sel_bound i c)
  · intro i J prev lost
    obtain ⟨root,prior⟩ := spec.mp prev
    have fail : J∉selected i := by
      intro pass
      apply lost (spec.mpr ⟨root,?_⟩)
      intro j hj
      by_cases same : j=i
      · exact same ▸ pass
      · apply prior
        have diff : j.val≠i.val := fun h=>same (Fin.ext h)
        omega
    have nz : i ≠ plan.first := by
      intro z
      subst i
      exact fail (first.symm ▸ root)
    obtain ⟨C,cap,proper,zero⟩ := cut i J root (by simpa only [selected,ite_eq_right nz] using fail)
    exact ⟨C,cap,proper,fun γ hγ=>zero _ _ (contact i γ hγ)⟩

structure Run {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (G : Jet) (plan : Plan) where
  row : Fin plan.count → Jet
  row_mem : ∀ i, row i ∈ evaluated Crt (word M) (plan.bank i).shape (plan.cutoff M.overhead.toNat i)
  avoids : ∀ i, ¬ G ∣ row i
  initial : Initial F G (row plan.first) plan
  kept : ℕ → Finset (Ideal Ambient)
  start : kept 0 = initial.parents
  intro_pass : kept 1 = initial.parents
  antitone : Antitone kept
  passed : ∀ (i : Fin plan.count) n, i.val < n → ∀ J ∈ kept n, Native J (plan.reserve i+1) (row i)
  cap : ∀ (i : Fin plan.count) n, i.val < n → ∀ k : Fin 4,
    (plan.reserve i+1)*mass (kept n) k ≤ pairCap plan.primeShape (plan.bank i).shape k
  cut : ∀ (i : Fin plan.count), ∀ J ∈ kept i.val, J ∉ kept (i.val+1) →
    ∃ C : Jet, RowCaps C (plan.bank i).shape ∧ toJet C ∉ J ∧
      ∀ γ∈Γ, jetAt C (M.label γ) (F.scalar γ) = 0

theorem prepare {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (plan : Plan)
    (ready : plan.Ready M.overhead.toNat)
    (noPole : ∀ j i,(D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (irr : Irreducible G)
    (slope : 0 < G.natDegree) (seeded : UsesSeed G) (capsG : RowCaps G plan.primeShape)
    (degree : plan.degree ≤ jetDegree G) (slopeFloor : plan.slopeFloor ≤ G.natDegree)
    (physicalFloor : plan.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) (seedFloor : plan.seedFloor ≤ seedDegree G) :
    Nonempty (Run F Crt G plan) := by
  choose Q inside avoid using ready.avoid Crt (word M) phys irr slope seeded degree
    slopeFloor physicalFloor seedFloor
  have caps (i : Fin plan.count) : RowCaps (Q i) (plan.bank i).shape :=
    evaluated_shape Crt (word M) (inside i)
  have contact (i : Fin plan.count) (γ : K) (hγ : γ∈Γ) :
      Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (plan.reserve i+1) (Q i) :=
    contact_at_mark F Crt noPole residues (inside i)
      (FreeSource.buffered_fit (plan.bank i) 179730 _ (plan.reserve i) (ready.wide i)) γ hγ
  obtain ⟨ini⟩ := initial_cover F irr (avoid plan.first) capsG (caps plan.first)
    (fun γ hγ => zero_of_contact (contact plan.first γ hγ))
  obtain ⟨kept, start, intro_pass, anti, passed, cap, cut⟩ :=
    history_from_initial irr capsG Q ini avoid caps contact
  exact ⟨⟨Q, inside, avoid, ini, kept, start, intro_pass, anti, passed, cap, cut⟩⟩

theorem Run.parent_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan} (R : Run F Crt G plan)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈R.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet (R.row plan.first)∈J :=
  R.initial.parent_geom J (R.start ▸ R.antitone (Nat.zero_le n) mem)


end
end Lower6960.Prefix6969Rescue
end Z6969Source0614

-- Source: Research6969.PrefixRescueStop
section Z6969Source0615
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

namespace Lower6960.Prefix6969Rescue
noncomputable section

open Finset
open K1 (K)
open K1_14 (Shape Jet jetAt atX)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (CutCover RowCaps Active emptyCut joinCuts joinCuts_cost mass mass_mono
  weight dot sectionDegree sum_dot)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open P1_7_4 (Mass massQ massQ_mono dotQ weightedBill bill_bound_with_final)
open Far6969RescueGeometry (Model Family OnMark OnSurface proper_cut beforeCuts)
open scoped BigOperators Classical

def Plan.cutShape (plan : Plan) (i : ℕ) : Shape :=
  if hi : i + 1 < plan.count then (plan.bank ⟨i + 1, hi⟩).shape else ⟨0, 0, 0, 0⟩

def Plan.history (plan : Plan) : ℕ → Mass
  | 0 => fun k => plan.initialCap k
  | i + 1 =>
    if hi : i + 1 < plan.count then
      let j : Fin plan.count := ⟨i + 1, hi⟩
      fun k => min (plan.history i k)
        ((pairCap plan.primeShape (plan.bank j).shape k : ℚ) / (plan.reserve j + 1 : ℕ))
    else plan.history i

section Run

variable {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}
variable (R : Run F Crt G plan)

/-- Stage zero introduces the parent set, so the cut list starts at stage one. -/
def Run.live (i : ℕ) : Finset (Ideal Ambient) := R.kept (i + 1)

def Run.lost (i : ℕ) : Finset (Ideal Ambient) := R.live i \ R.live (i + 1)

theorem Run.live_start : R.live 0 = R.initial.parents := R.intro_pass

theorem Run.next_sub (i : ℕ) : R.live (i + 1) ⊆ R.live i :=
  R.antitone (Nat.le_succ (i + 1))

theorem Run.live_mass (i : ℕ) (hi : i < plan.count) (k : Fin 4) :
    massQ (R.live i) k ≤ plan.history i k := by
  induction i with
  | zero =>
    rw [R.live_start]
    exact (Nat.cast_le (α := ℚ)).mpr
      ((mass_mono (subset_union_right : R.initial.parents ⊆ R.initial.rankExit ∪ R.initial.parents)
        k).trans (R.initial.fits k))
  | succ i ih =>
    rw [Plan.history, dite_eq_left hi]
    apply le_min
    · exact (massQ_mono (R.next_sub i) k).trans (ih (by omega))
    · let j : Fin plan.count := ⟨i + 1, hi⟩
      have hcap := R.cap j (i + 1 + 1) (by change i+1 < i+1+1; omega) k
      apply (le_div_iff₀ (by positivity : (0 : ℚ) < ((plan.reserve j + 1 : ℕ) : ℚ))).mpr
      have h : mass (R.live (i + 1)) k * (plan.reserve j + 1) ≤
          pairCap plan.primeShape (plan.bank j).shape k := by
        simpa only [Run.live, Nat.mul_comm] using hcap
      change (mass (R.live (i + 1)) k : ℚ) * ((plan.reserve j + 1 : ℕ) : ℚ) ≤
        (pairCap plan.primeShape (plan.bank j).shape k : ℚ)
      exact_mod_cast h

theorem Run.cut_cover {i : ℕ} (hi : i + 1 < plan.count) :
    ∃ C : CutCover,
      (∀ fee, C.cost fee ≤ dot (weight (plan.cutShape i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ, (∃ J∈R.lost i, OnMark F J γ) →
        γ ∈ C.direct ∨ ∃ Q∈C.curves, OnMark F Q γ := by
  let j : Fin plan.count := ⟨i + 1, hi⟩
  have shape : plan.cutShape i = (plan.bank j).shape := by
    rw [Plan.cutShape, dite_eq_left hi]
  have oneCut (J : Ideal Ambient) (mem : J∈R.lost i) :
      ∃ C : CutCover, (∀ fee, C.cost fee ≤
        dot (weight (plan.cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ, OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves, OnMark F Q γ := by
    obtain ⟨present, absent⟩ := mem_sdiff.mp mem
    obtain ⟨P, caps, proper, roots⟩ := R.cut j J present absent
    rw [shape]
    exact proper_cut F _ (plan.stage_fit j) (R.parent_geom present).1 caps proper roots
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈R.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈R.lost i) :
      (∀ fee, (C J).cost fee ≤ dot (weight (plan.cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ, OnMark F J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves, OnMark F Q γ := by
    simpa only [C, dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (R.lost i) C, ?_, ?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans
      ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J, mem, on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q, hQ, hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J, mem, point⟩)
    · exact Or.inr ⟨Q, mem_biUnion.mpr ⟨J, mem, hQ⟩, hmark⟩

theorem Run.retained_or_lost (stop : ℕ) {J : Ideal Ambient} (mem : J∈R.initial.parents) :
    J∈R.live stop ∨ ∃ i < stop, J∈R.lost i := by
  by_cases h : ∃ i < stop, J∈R.lost i
  · exact Or.inr h
  · left
    have live : ∀ n ≤ stop, J∈R.live n := by
      intro n hn
      induction n with
      | zero => exact R.live_start.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n, by omega, mem_sdiff.mpr ⟨ih (by omega), absent⟩⟩
    exact live stop le_rfl

private def Run.jointLive : ℕ → Finset (Ideal Ambient)
  | 0 => R.initial.rankExit ∪ R.initial.parents
  | i + 1 => R.live i

private def Run.jointLost : ℕ → Finset (Ideal Ambient)
  | 0 => R.initial.rankExit
  | i + 1 => R.lost i

/-- Stopping before terminal interpolation keeps the complete final credit. -/
theorem Run.early_bill (stop : ℕ) (stop_ok : stop < plan.count) (rank : Mass) (cut : ℕ → Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range stop, dotQ (cut i) (massQ (R.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) (stop + 1)) (massQ (R.live stop)) ≤
      weightedBill (stop + 1) (beforeCuts rank cut)
        (beforeCuts (fun k => plan.initialCap k) plan.history) := by
  have bill := bill_bound_with_final (stop + 1) (beforeCuts rank cut)
    (beforeCuts (fun k => plan.initialCap k) plan.history) R.jointLive R.jointLost ?_ ?_ ?_
  · rw [sum_range_succ'] at bill
    simpa only [beforeCuts, Run.jointLost, Run.jointLive, add_comm] using bill
  · intro i hi
    cases i with
    | zero => simpa only [Run.jointLive, R.live_start] using
        (subset_union_right : R.initial.parents ⊆ R.initial.rankExit ∪ R.initial.parents)
    | succ i => exact R.next_sub i
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem, ?_⟩
      rw [Run.jointLive, R.live_start]
      exact fun h => (disjoint_left.mp R.initial.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α := ℚ)).mpr (R.initial.fits k)
    | succ i => exact R.live_mass i (by omega) k

theorem Run.stop_surfaces (stop : ℕ) :
    ∃ S : Finset Surface,
      (∀ q∈S, Parent q ∧ ∃ J∈R.live stop, q.asIdeal = J.comap toJet) ∧
      ∀ γ∈Γ, (∃ J∈R.live stop, OnMark F J γ) → ∃ q∈S, OnSurface F q γ := by
  let getGeom (J : R.live stop) := R.parent_geom J.property
  let surface (J : R.live stop) := surfaceOf J.val (getGeom J).1.prime
  let S := (R.live stop).attach.image surface
  refine ⟨S, ?_, ?_⟩
  · intro q hq
    obtain ⟨J, _, rfl⟩ := mem_image.mp hq
    have hJ := getGeom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1, J.val, J.property, rfl⟩
  · rintro γ _ ⟨J, hJ, on⟩
    let q : R.live stop := ⟨J, hJ⟩
    refine ⟨surface q, mem_image.mpr ⟨q, mem_attach _ _, rfl⟩, ?_⟩
    intro P mem
    rw [← K1_14_2.eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

theorem Run.stop_books (stop : ℕ) (stop_ok : stop < plan.count) :
    ∃ C : ℕ → CutCover,
      (∀ i < stop, ∀ fee, (C i).cost fee ≤
        dot (weight (plan.cutShape i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0 →
        R.initial.seeds.Covers (M.label γ) ∨ atX (F.scalar γ) ∈ R.initial.ordinates ∨
        (∃ J∈R.initial.rankExit, OnMark F J γ) ∨
        (∃ i < stop, γ ∈ (C i).direct ∨ ∃ Q∈(C i).curves, OnMark F Q γ) ∨
        ∃ J∈R.live stop, OnMark F J γ := by
  have pick (i : ℕ) : ∃ C : CutCover, i < stop →
      (∀ fee, C.cost fee ≤ dot (weight (plan.cutShape i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ, (∃ J∈R.lost i, OnMark F J γ) →
        γ∈C.direct ∨ ∃ Q∈C.curves, OnMark F Q γ := by
    by_cases hi : i < stop
    · obtain ⟨C, fee, covers⟩ := R.cut_cover (i := i) (by omega)
      exact ⟨C, fun _ => ⟨fee, covers⟩⟩
    · exact ⟨emptyCut, fun h => (hi h).elim⟩
  choose C valid using pick
  refine ⟨C, fun i h => (valid i h).1, ?_⟩
  intro γ hγ hG
  rcases R.initial.covers γ hγ hG with seed | ordinate | rank | ⟨J, parent, marked⟩
  · exact Or.inl seed
  · exact Or.inr (Or.inl ordinate)
  · exact Or.inr (Or.inr (Or.inl rank))
  · rcases R.retained_or_lost stop parent with live | ⟨i, hi, lost⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨J, live, marked⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, (valid i hi).2 γ hγ ⟨J,lost,marked⟩⟩)))

end Run


end
end Lower6960.Prefix6969Rescue
end Z6969Source0615

-- Source: Research6969.PrefixRescueSources
section Z6969Source0616
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969Rescue
noncomputable section

open Research6969.PhysicalWindow
open Research6966
open Far6969RescueGeometry (Model Family)
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)

def Plan.request (plan : Plan) (i : Fin plan.count) : Request :=
  ⟨plan.bank i, plan.reserve i, plan.degree, plan.slopeFloor, plan.physicalFloor, plan.seedFloor⟩

structure Plan.Sources (plan : Plan) (first last : ℕ) : Prop where
  first_pos : 0 < first
  last_safe : last ≤ 131070
  slope_pos : 0 < plan.slopeFloor
  rank : ∀ i, P3_7_1.BankOK (plan.bank i)
  reserve_fit : ∀ i, 2 * plan.reserve i ≤ (plan.bank i).shape.B
  seed_small : ∀ i, (plan.bank i).shape.U < K1.p
  narrow : ∀ i, (plan.bank i).shape.J < 131071-last
  width : ∀ i, HelperSource.WidthGuard (plan.bank i) 179730 first (plan.reserve i)
  covers : ∀ i, ∃ ends, Cover (Triangular (plan.request i)) last first ends

theorem Plan.Sources.ready {plan : Plan} {first last h : ℕ} (S : plan.Sources first last)
    (lo : first ≤ h) (hi : h ≤ last) : plan.Ready h := by
  refine ⟨S.first_pos.trans_le lo, hi.trans S.last_safe, S.rank, S.seed_small, ?_, ?_⟩
  · intro i
    exact HelperSource.width_at_height (plan.bank i) 179730 first h (plan.reserve i) lo
      (hi.trans (S.last_safe.trans (by decide))) (S.reserve_fit i) (S.width i)
  · intro i
    obtain ⟨ends, cov⟩ := S.covers i
    obtain ⟨left,right,hlo,hhi,high,cert⟩ := covered cov lo hi
    exact triangle_positive (plan.request i) (S.first_pos.trans_le lo) hlo hhi
      ((S.narrow i).trans_le (Nat.sub_le_sub_left high 131071)) S.slope_pos cert

/-- Instantiate the single physical rescue producer from a bank/height receipt. -/
theorem Plan.Sources.run {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    {plan : Plan} {first last : ℕ} (S : plan.Sources first last)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ last)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : plan.slopeFloor ≤ G.natDegree) (seeded : UsesSeed G) (caps : RowCaps G plan.primeShape)
    (degree : plan.degree ≤ jetDegree G) (seed : plan.seedFloor ≤ seedDegree G)
    (physical : plan.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) : Nonempty (Run F Crt G plan) :=
  Prefix6969Rescue.prepare F Crt plan (S.ready lo hi) noPole residues phys prime.irreducible
    (S.slope_pos.trans_le slope) seeded caps degree slope physical seed


end
end Lower6960.Prefix6969Rescue
end Z6969Source0616

-- Source: Research6969.PrefixRescueBook
section Z6969Source0617
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace Lower6960.Prefix6969Rescue
noncomputable section

open Finset Polynomial
open K1 (K)
open K1_14 (Jet Shape atX jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (CutCover emptyCut joinCuts joinCuts_cost mass mass_mono weight dot
  sectionDegree sum_dot)
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open P1_7_4 (Mass massQ massQ_mono dotQ weightedBill bill_bound bill_bound_with_final)
open Far6969RescueGeometry (Model Family OnMark OnSurface word contact_at_mark zero_of_contact
  proper_cut beforeCuts)
open Prefix6969Wide (terminalShape TerminalPass SurfacePass terminal_failure)
open scoped BigOperators Classical

variable {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}

structure Book (R : Run F Crt G plan) where
  steps : ℕ
  live : ℕ → Finset (Ideal Ambient)
  shape : ℕ → Shape
  capacity : ℕ → Mass
  start : live 0 = R.initial.parents
  next : ∀ i < steps, live (i + 1) ⊆ live i
  bound : ∀ i < steps, ∀ k, massQ (live i) k ≤ capacity i k
  initial_bound : ∀ i < steps, ∀ k, massQ (live i) k ≤ (plan.initialCap k : ℚ)
  cut : ℕ → CutCover
  cut_cost : ∀ i < steps, ∀ fee,
    (cut i).cost fee ≤ dot (weight (shape i) fee) (mass (live i \ live (i + 1)))
  cut_cover : ∀ i < steps, ∀ γ ∈ Γ,
    (∃ J ∈ live i \ live (i + 1), OnMark F J γ) →
    γ ∈ (cut i).direct ∨ ∃ J ∈ (cut i).curves, OnMark F J γ

variable (R : Run F Crt G plan)

def Book.lost {R : Run F Crt G plan} (B : Book R) (i : ℕ) := B.live i \ B.live (i + 1)
def Book.final {R : Run F Crt G plan} (B : Book R) := B.live B.steps

theorem Book.early (stop : ℕ) (fits : stop < plan.count) :
    ∃ B : Book R, B.steps = stop ∧ B.final = R.live stop ∧
      B.shape = plan.cutShape ∧ B.capacity = plan.history := by
  have pick (i : ℕ) : ∃ C : CutCover, i < stop →
      (∀ fee, C.cost fee ≤ dot (weight (plan.cutShape i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ, (∃ J∈R.lost i, OnMark F J γ) →
        γ∈C.direct ∨ ∃ J∈C.curves, OnMark F J γ := by
    by_cases hi : i < stop
    · obtain ⟨C, cost, cover⟩ := R.cut_cover (i := i) (by omega)
      exact ⟨C, fun _ => ⟨cost, cover⟩⟩
    · exact ⟨emptyCut, fun h => (hi h).elim⟩
  choose C valid using pick
  have initialCap (i : ℕ) (k : Fin 4) :
      massQ (R.live i) k ≤ (plan.initialCap k : ℚ) := by
    have sub : R.live i ⊆ R.initial.rankExit ∪ R.initial.parents := by
      rw [← R.start]
      exact (R.antitone (Nat.zero_le _)).trans subset_union_right
    exact (Nat.cast_le (α := ℚ)).mpr ((mass_mono sub k).trans (R.initial.fits k))
  exact ⟨⟨stop, R.live, plan.cutShape, plan.history, R.live_start, fun i _ => R.next_sub i,
    fun i hi k => R.live_mass i (hi.trans fits) k, fun i _ k => initialCap i k, C,
    fun i h => (valid i h).1, fun i h => (valid i h).2⟩, rfl, rfl, rfl, rfl⟩

def Run.terminal (R : Run F Crt G plan) : Finset (Ideal Ambient) :=
  (R.live (plan.count - 1)).filter (TerminalPass Crt (word M))

private theorem Run.terminal_cut
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ C : CutCover,
      (∀ fee, C.cost fee ≤ dot (weight terminalShape fee) (mass (R.live (plan.count - 1) \ R.terminal))) ∧
      ∀ γ∈Γ, (∃ J ∈ R.live (plan.count - 1) \ R.terminal, OnMark F J γ) →
        γ∈C.direct ∨ ∃ J∈C.curves, OnMark F J γ := by
  let lost := R.live (plan.count - 1) \ R.terminal
  have oneCut (J : Ideal Ambient) (mem : J∈lost) :
      ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight terminalShape fee) (sectionDegree J)) ∧
        ∀ γ∈Γ, OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves, OnMark F Q γ := by
    obtain ⟨present, absent⟩ := mem_sdiff.mp mem
    have hfail : ¬ TerminalPass Crt (word M) J :=
      fun pass => absent (mem_filter.mpr ⟨present, pass⟩)
    obtain ⟨s, P, multiplicity, inside, cap, avoids⟩ := terminal_failure Crt (word M) hfail
    have zero (γ : K) (hit : γ ∈ Γ) : jetAt P (M.label γ) (F.scalar γ) = 0 := by
      apply zero_of_contact (r := 0)
      apply contact_at_mark F Crt noPole residues inside _ γ hit
      simpa only [Nat.mul_zero, Nat.add_zero] using
        Nat.sub_lt (Nat.mul_pos multiplicity (by decide : 0 < 179730)) (by decide : 0 < 1)
    exact proper_cut F _ (by decide) (R.parent_geom present).1 cap avoids zero
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈lost then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈lost) :
      (∀ fee, (C J).cost fee ≤ dot (weight terminalShape fee) (sectionDegree J)) ∧
        ∀ γ∈Γ, OnMark F J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves, OnMark F Q γ := by
    simpa only [C, dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts lost C, ?_, ?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans
      ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J, mem, on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q, hQ, hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J, mem, point⟩)
    · exact Or.inr ⟨Q, mem_biUnion.mpr ⟨J, mem, hQ⟩, hmark⟩

def Plan.normalShape (plan : Plan) (i : ℕ) : Shape :=
  if i + 1 < plan.count then plan.cutShape i else terminalShape

/-- The final cut is the actual terminal-bank test, with its own envelope. -/
theorem Book.normal
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ B : Book R, B.steps = plan.count ∧ B.final = R.terminal ∧
      B.shape = plan.normalShape ∧ B.capacity = plan.history := by
  obtain ⟨Cₜ, cₜ, hₜ⟩ := R.terminal_cut noPole residues
  let live (i : ℕ) := if i < plan.count then R.live i else R.terminal
  let shape := plan.normalShape
  have step (i : ℕ) (hi : i < plan.count) : live (i + 1) ⊆ live i := by
    by_cases next : i + 1 < plan.count
    · simpa only [live, ite_eq_left hi, ite_eq_left next] using R.next_sub i
    · have eq : i = plan.count - 1 := by omega
      have old : live i = R.live (plan.count - 1) := by rw [show live i = R.live i from if_pos hi, eq]
      have new : live (i + 1) = R.terminal := by simp only [live, ite_eq_right next]
      rw [old, new]
      exact filter_subset _ _
  have pick (i : ℕ) : ∃ C : CutCover, i < plan.count →
      (∀ fee, C.cost fee ≤ dot (weight (shape i) fee) (mass (live i \ live (i+1)))) ∧
      ∀ γ∈Γ, (∃ J ∈ live i \ live (i+1), OnMark F J γ) →
        γ∈C.direct ∨ ∃ J∈C.curves, OnMark F J γ := by
    by_cases hn : i < plan.count
    · by_cases next : i+1 < plan.count
      · obtain ⟨C, c, hC⟩ := R.cut_cover next
        exact ⟨C, fun _ => by simpa only [shape, Plan.normalShape, live, ite_eq_left hn, ite_eq_left next,
          Run.lost] using And.intro c hC⟩
      · have eq : i = plan.count - 1 := by omega
        have old : live i = R.live (plan.count - 1) := by rw [show live i = R.live i from if_pos hn, eq]
        have new : live (i + 1) = R.terminal := by simp only [live, ite_eq_right next]
        have last : shape i = terminalShape := by simp only [shape, Plan.normalShape, ite_eq_right next]
        exact ⟨Cₜ, fun _ => by simpa only [last, old, new] using And.intro cₜ hₜ⟩
    · exact ⟨emptyCut, fun h => (hn h).elim⟩
  choose C valid using pick
  have initialCap (i : ℕ) (hi : i < plan.count) (k : Fin 4) :
      massQ (live i) k ≤ (plan.initialCap k : ℚ) := by
    simp only [live, ite_eq_left hi]
    have sub : R.live i ⊆ R.initial.rankExit ∪ R.initial.parents := by
      rw [← R.start]
      exact (R.antitone (Nat.zero_le _)).trans subset_union_right
    exact (Nat.cast_le (α := ℚ)).mpr ((mass_mono sub k).trans (R.initial.fits k))
  refine ⟨⟨plan.count, live, shape, plan.history, ?_, step,
    fun i hi k => by simpa only [live, ite_eq_left hi] using R.live_mass i hi k,
    initialCap, C, fun i h => (valid i h).1, fun i h => (valid i h).2⟩, rfl, ?_, rfl, rfl⟩
  · simpa only [live, ite_eq_left plan.positive] using R.live_start
  · change live plan.count = R.terminal
    simp only [live, Nat.lt_irrefl, ite_false]

variable {R} (B : Book R)

theorem Book.retained_or_lost {J : Ideal Ambient} (mem : J∈R.initial.parents) :
    J∈B.final ∨ ∃ i < B.steps, J∈B.lost i := by
  by_cases h : ∃ i < B.steps, J∈B.lost i
  · exact Or.inr h
  · left
    have live : ∀ n ≤ B.steps, J∈B.live n := by
      intro n hn
      induction n with
      | zero => exact B.start.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n, by omega, mem_sdiff.mpr ⟨ih (by omega), absent⟩⟩
    exact live B.steps le_rfl

theorem Book.cut_marks {γ : K} (hγ : γ ∈ Γ)
    (roots : jetAt G (M.label γ) (F.scalar γ) = 0) :
    R.initial.seeds.Covers (M.label γ) ∨ atX (F.scalar γ) ∈ R.initial.ordinates ∨
    (∃ J∈R.initial.rankExit, OnMark F J γ) ∨
    (∃ i < B.steps, γ ∈ (B.cut i).direct ∨ ∃ Q∈(B.cut i).curves, OnMark F Q γ) ∨
    ∃ J∈B.final, OnMark F J γ := by
  rcases R.initial.covers γ hγ roots with seed | ordinate | rank | ⟨J, parent, marked⟩
  · exact Or.inl seed
  · exact Or.inr (Or.inl ordinate)
  · exact Or.inr (Or.inr (Or.inl rank))
  · rcases B.retained_or_lost parent with live | ⟨i, hi, lost⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨J, live, marked⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, B.cut_cover i hi γ hγ ⟨J,lost,marked⟩⟩)))

private def Book.jointLive : ℕ → Finset (Ideal Ambient)
  | 0 => R.initial.rankExit ∪ R.initial.parents
  | i + 1 => B.live i

private def Book.jointLost : ℕ → Finset (Ideal Ambient)
  | 0 => R.initial.rankExit
  | i + 1 => B.lost i

theorem Book.joint_bill (rank : Mass) (cut : ℕ → Mass) :
    dotQ rank (massQ R.initial.rankExit) +
      (∑ i∈range B.steps, dotQ (cut i) (massQ (B.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) (B.steps + 1)) (massQ B.final) ≤
      weightedBill (B.steps + 1) (beforeCuts rank cut)
        (beforeCuts (fun k => plan.initialCap k) B.capacity) := by
  have bill := bill_bound_with_final (B.steps + 1) (beforeCuts rank cut)
    (beforeCuts (fun k => plan.initialCap k) B.capacity) B.jointLive B.jointLost ?_ ?_ ?_
  · rw [sum_range_succ'] at bill
    simp only [beforeCuts, Book.jointLost, Book.jointLive, Book.final] at bill ⊢
    linarith only [bill]
  · intro i hi
    cases i with
    | zero => simpa only [Book.jointLive, B.start] using
        (subset_union_right : R.initial.parents ⊆ R.initial.rankExit ∪ R.initial.parents)
    | succ i => exact B.next i (by omega)
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem, ?_⟩
      rw [Book.jointLive, B.start]
      exact fun h => (disjoint_left.mp R.initial.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α := ℚ)).mpr (R.initial.fits k)
    | succ i => exact B.bound i (by omega) k

end


end Lower6960.Prefix6969Rescue
end Z6969Source0617
