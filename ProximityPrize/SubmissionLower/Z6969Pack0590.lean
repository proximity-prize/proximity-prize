import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.R6966ProofHelperWeightCap
import ProximityPrize.SubmissionLower.R6966ProofNativeAffineTariff
import ProximityPrize.SubmissionLower.R6966ProofPhysicalHelperTariff
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- Source: Research6969.PrefixMiddleRefitSchedule
section Z6969Source0680
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000

namespace Lower6960.Prefix6969MiddleRefit

open Research6969
open Research6969.TransitionBanks
open K1_14 (L)
open K1_14_1 (PoleData CRTLift evaluated)
open Lower6960.HelperSource
open P1_7_4 (Mass)

abbrev count : ℕ := 21
abbrev firstHeight : ℕ := 2412
abbrev lastHeight : ℕ := 2557
abbrev agreement : ℕ := 179730

def reserve (i : Fin count) : ℕ := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 21, 21, 36, 41, 41, 65, 76, 76, 76, 76] i
def bank (i : Fin count) : P1_7.Bank :=
  ![bank2 1121, bank8 1238, bank14 1349, bank21 1459, bank32 1683, bank41 2155, bank42 2862, bank48 1930, bank61 2044, bank73 3927, bank85 2394, bank74 4330, bank116 3050, bank132 6342, bank148 5351, bank117 13588, bank198 7884, bank207 9165, bank179 23197, bank173 27639, bank169 29097] i

theorem free_checked (i : Fin count) : TransitionSources.Free firstHeight (reserve i) (bank i) := by
  fin_cases i
  · exact free2_1
  · exact free8_1
  · exact free14_1
  · exact free21_1
  · exact free32_1
  · exact free41_1
  · exact free42_6
  · exact free48_1
  · exact free61_1
  · exact free73_1
  · exact free85_1
  · exact free74_5
  · exact free116_3
  · exact free132_1
  · exact free148_1
  · exact free117_1
  · exact free198_1
  · exact free207_1
  · exact free179_1
  · exact free173_1
  · exact free169_1

def cutoff (h : ℕ) (i : Fin count) : ℕ :=
  cutoffCount (bank i).shape agreement h (reserve i) - 1

theorem cutoff_fit {h : ℕ} (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) (i : Fin count) :
    cutoff h i + 2 * h * reserve i < (bank i).shape.m * agreement := by
  have cert := free_checked i
  have hw := width_at_height _ _ _ _ _ lo (hi.trans (by decide)) cert.reserve_fit cert.width
  exact Lower6960.FreeSource.buffered_fit (bank i) agreement h (reserve i) hw

theorem free_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) (i : Fin count) :
    ∃ P ∈ evaluated Crt word (bank i).shape (cutoff h i), P ≠ 0 :=
  (free_checked i).row Crt word ((by decide : 0 < firstHeight).trans_le lo) lo (hi.trans (by decide))

def suppliedHistory : List Mass :=
  [![13965, 132038, 617429, 2575787],
   ![23965/2, 117225, 530602, 2285348],
   ![17372/3, 56658, 464056, 1819801],
   ![7059/2, 275387/8, 2507156/9, 10773256/9],
   ![16211/9, 316579/18, 721709/4, 2832489/4],
   ![24292/27, 757702/81, 860801/9, 3978130/9],
   ![73478/121, 885276/121, 3989008/49, 21133008/49],
   ![73478/121, 885276/121, 3989008/49, 3562780/9],
   ![73478/121, 871744/121, 79672, 261121],
   ![77324/147, 2631610/441, 2892938/49, 261121],
   ![77324/147, 2631610/441, 2892938/49, 261121],
   ![61324/121, 2631610/441, 12193984/225, 261121],
   ![61324/121, 714731/121, 12193984/225, 9302500/49],
   ![61324/121, 714731/121, 8979376/169, 9302500/49],
   ![61324/121, 8541656/1681, 38410064/841, 39511784/225],
   ![1322245/3362, 8541656/1681, 38410064/841, 39511784/225],
   ![1322245/3362, 893488/189, 21080676/529, 349292736/2209],
   ![1322245/3362, 12482743/2738, 3717935/96, 349292736/2209],
   ![470505/1369, 12482743/2738, 3717935/96, 349292736/2209],
   ![461692/1369, 12482743/2738, 3717935/96, 349292736/2209],
   ![459151/1369, 12482743/2738, 3717935/96, 349292736/2209]]

def suppliedDegreeRates : List ℕ := [287567366, 388126102, 388260904, 388304270, 386845787, 389010179, 388311592, 388691591, 162716559, 163566869, 163638726, 163457698, 81970807, 80817237, 79023214, 82363343, 87671467, 115428840, 148643765, 100000000, 227860168]
def suppliedHeightRates : List ℕ := [1255575, 883934, 883564, 883445, 887447, 881508, 883425, 882382, 2358545, 2344389, 2343193, 2346206, 4871348, 4939936, 5059993, 4848009, 4538710, 3395746, 2592831, 3959851, 1632370]
def retainedCredit (i : Fin 4) : ℕ := ![120952734377760, 1614589970072, 205074151200, 5399834440] i
abbrev prefixCap : ℕ := 166093892126631894

end Lower6960.Prefix6969MiddleRefit
end Z6969Source0680

-- Source: Research6969.PrefixMiddleRefitGeometry
section Z6969Source0681
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960MainGeometry

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969MiddleRefit
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt seedHasse)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual orderOn FixedPart)
open K1_14_2_2R (chainCompatible)
open HelperPrefix (timesShape)
open Prefix6969MiddleHelper (helperBank helperCutoff)
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

def freeShape (i : Fin 21) : Shape := (bank i).shape

def movingShape (i : Fin 21) : Shape := timesShape (copies i) helperBank.shape

def stage (i : Fin 21) : P1_7.Stage := ⟨reserve i,bank i,⟨movingShape i,0,0⟩⟩

def cutShape (i : ℕ) : Shape :=
  if hi : i+1<21 then HighCore82258_3.envelope (stage ⟨i+1,hi⟩) else terminalShape

theorem cutShape_fit (i : ℕ) : (cutShape i).J≤(cutShape i).B := by
  unfold cutShape
  split
  · exact Nat.le_add_left _ _
  · decide

def introIndices : List (Fin 21) := [1,2,3,4,5,6,7,8,9,10,11,12,13,14]

def introAccount (k : Fin 4) : List (Fin 21) → (Fin 3→ℕ) → (Fin 3→ℕ) → ℕ
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

theorem free_ode_guard (i : Fin 21) : ODEGuard (freeShape i).B (freeShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem moving_ode_guard (i : Fin 21) : ODEGuard (movingShape i).B (movingShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem free_seed_small (i : Fin 21) : (freeShape i).U<K1.p := by
  fin_cases i <;> decide +kernel

theorem moving_seed_small (i : Fin 21) : (movingShape i).U<K1.p := by
  fin_cases i <;> decide +kernel

theorem reserve_pos {i : Fin 21} (hi : 0 < i.val) : 0<reserve i := by
  have checks (j : Fin 21) : (j.val=0) ∨ 0<reserve j := by
    fin_cases j <;> decide +kernel
  exact (checks i).resolve_left (by omega)

/-- The main branch retains the single preparation object, including the
original helper, its one possible exception, and the 21 stripped free rows. -/
structure Rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) where
  source : Fin 21→Jet
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
  have hiAll : M.overhead.toNat ≤ 33755 := hi.trans (by decide)
  choose P inside nz using free_rows Crt (word M) lo hi
  obtain ⟨out⟩ := PrefixRows.prepare P freeShape copies _ _ nz
    (fun i => evaluated_shape Crt (word M) (inside i))
    (Prefix6969MiddleHelper.helper_nonzero Crt (word M) lo hiAll)
    (fun Q hQ => evaluated_shape Crt (word M) hQ)
    (fun _ _ g h cop => Prefix6969MiddleHelper.helper_not_two Crt (word M) lo hiAll
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
      have wh := Prefix6969MiddleHelper.helper_width lo hiAll
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
    (i : Fin 21) (γ : K) (mem : γ∈R.marks) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.helper^copies i) :=
  R.contact i γ (mem_filter.mp mem).1 (mem_filter.mp mem).2

theorem Rows.intro_tests {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 21) (j : Fin 2) (a : ℕ) (ha : a≤reserve i) (γ : K) (mem : γ∈R.marks) :
    jetAt (seedHasse j a (R.out.free i)) (M.label γ) (R.family.scalar γ)=0 :=
  hasse_at_mark (R.main_contact i γ mem).1 j a ha (ha.trans_lt (reserve_small i))

def Rows.Passes {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 21) (J : Ideal Ambient) : Prop :=
  orderOn J (R.out.free i) (reserve i+1) ∧
  orderOn J (R.out.helper^copies i) (reserve i+1) ∧ chainCompatible (R.out.free i) (R.out.helper^copies i) J

theorem Rows.failed_cut {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 21) {J : Ideal Ambient} (active : Active J) (dualJ : dual J) (fail : ¬R.Passes i J) :
    ∃ C : Jet,(RowCaps C (freeShape i) ∨ RowCaps C (movingShape i)) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  rcases PrefixStage.order_or_cut active dualJ (reserve_small i) (R.out.free_caps i) (R.out.moving_caps i)
    (pow_ne_zero _ R.out.helper_ne) (moving_ode_guard i).jpos with passes | ⟨C,cap,proper,zero⟩
  · exact (fail passes).elim
  · refine ⟨C,cap,proper,?_⟩
    intro γ hγ on
    obtain ⟨free,moving⟩ := R.main_contact i γ hγ
    exact zero _ _ on free moving

end Lower6960.Prefix6969MiddleRefit

end
end Merged_R6960MainGeometry

section Merged_R6960MainGeometryIntro

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969MiddleRefit
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
    (hQc : RowCaps Q (movingShape 0)) (later : Fin 21 → Jet)
    (rows : ∀ i, later i ≠ 0 ∧ RowCaps (later i) (freeShape i)) :
    ∀ (is : List (Fin 21)),
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
  (univ : Finset (Fin 21)).biUnion (fun i=>
    R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation)

theorem Rows.mem_fixed_free {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 21)
    (root : fixedAt (R.fixedFree i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_left _ (mem_filter.mpr ⟨mark,root⟩)⟩

theorem Rows.mem_fixed_moving {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 21)
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

end Lower6960.Prefix6969MiddleRefit

end
end Merged_R6960MainGeometryIntro

section Merged_R6960MainGeometryProcess

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969MiddleRefit
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
  ini.parents.filter (fun J=>∀ i : Fin 21,0 < i.val → i.val≤n → R.Passes i J)

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
  (ini.kept 20).filter (TerminalPass Crt (word M))

def Initial.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := if n<21 then ini.kept n else ini.final

def Initial.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := ini.live n \ ini.live (n+1)

theorem Initial.live_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.live 0=ini.parents := by
  rw [Initial.live,ite_eq_left (by decide : 0<21),ini.kept_zero]

theorem Initial.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<21) : ini.live (i+1)⊆ini.live i := by
  by_cases hn : i+1<21
  · simp only [Initial.live,ite_eq_left hi,ite_eq_left hn]
    exact ini.kept_anti (Nat.le_succ _)
  · have eq : i=20 := by omega
    subst i
    exact filter_subset _ _

theorem Initial.stage_mass {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (i : Fin 21) (hi : 0 < i.val) {n : ℕ} (step : i.val≤n) (k : Fin 4) :
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
    {i : ℕ} {J : Ideal Ambient} (hi : i<21) (mem : J∈ini.lost i) :
    ∃ C : Jet,RowCaps C (cutShape i) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Initial.live,ite_eq_left hi] at prev
  by_cases hn : i+1<21
  · let j : Fin 21 := ⟨i+1,hn⟩
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
  · have eq : i=20 := by omega
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
    {i : ℕ} (hi : i<21) :
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
    J∈ini.final ∨ ∃ i<21,J∈ini.lost i := by
  by_cases h : ∃ i<21,J∈ini.lost i
  · exact Or.inr h
  · have alive : ∀ n≤21,J∈ini.live n := by
      intro n hn
      induction n with
      | zero => exact ini.live_zero.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Initial.live] using alive 21 le_rfl)

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

end Lower6960.Prefix6969MiddleRefit

end
end Merged_R6960MainGeometryProcess

section Merged_R6960MainGeometryBills

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969MiddleRefit
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

theorem history_step (i : Fin 20) (k : Fin 4) :
    let j : Fin 21 := ⟨i.val+1,by have := i.isLt; omega⟩
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
    {i : ℕ} (hi : i<21) (k : Fin 4) : massQ (ini.kept i) k≤history i k := by
  induction i with
  | zero => rw [history_zero]; exact ini.cap_initial _ _
  | succ i ih =>
    have hl : i<20 := by omega
    have hstep := history_step ⟨i,hl⟩ k
    dsimp only at hstep
    rw [hstep]
    exact le_min ((massQ_mono (ini.kept_anti (Nat.le_succ i)) k).trans (ih (by omega)))
      (ini.stage_mass ⟨i+1,hi⟩ (Nat.succ_pos _) le_rfl k)

theorem Initial.cap_live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<21) (k : Fin 4) : massQ (ini.live i) k≤history i k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_kept hi k

theorem Initial.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<21) (k : Fin 4) : massQ (ini.live i) k ≤ initialMass k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_initial _ k

def cutWeight (fee : Fin 3) (i : ℕ) : Mass := fun k=>weight (cutShape i) fee k

def seedLimit : ℚ := weightedBill 21 (cutWeight 0) history

def pointLimit : ℚ := weightedBill 21 (cutWeight 2) (fun _=>initialMass)

def initialSeedLimit : ℕ := (K1.p+1)*initialCap 2+initialCap 3

def contentLimit : ℕ := (K1.p+1)*(freeShape 0).U

def fixedLimit : ℕ :=
  ∑ i : Fin 21, (fixedFee (freeShape i).B (freeShape i).J+fixedFee (movingShape i).B (movingShape i).J)

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
    _ ≤ ∑ i : Fin 21, (R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation).card :=
      card_biUnion_le
    _ ≤ _ := sum_le_sum fun i _=>(card_union_le _ _).trans (Nat.add_le_add
      (Prefix6969MiddleRates.fixed_count R.family hi (free_ode_guard i) _ (R.fixedFree i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2))
      (Prefix6969MiddleRates.fixed_count R.family hi (moving_ode_guard i) _ (R.fixedMoving i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2)))

structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) where
  cover : ℕ→CutCover
  cost : ∀ i<21,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))
  covers : ∀ i<21,∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark R.family Q γ

theorem Initial.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks ini) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<21 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    by_cases hi : i<21
    · obtain ⟨C,cap,cover⟩ := ini.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩

theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) {i : ℕ} (hi : i<21) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight fee i) (massQ (ini.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound

theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (∑ i∈range 21,((C.cover i).cost 0 : ℚ))≤seedLimit :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 21 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.cap_live hi))

def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K := (range 21).biUnion fun i=>(C.cover i).direct

theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (C.pointMarks.card : ℚ) ≤ pointLimit := by
  calc
    _ ≤ ∑ i∈range 21,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 21,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 21,dotQ (cutWeight 2 i) (massQ (ini.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 21 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
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
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 21,dotQ (cut i) (massQ (ini.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) 22) (massQ ini.final) ≤
      weightedBill 22 (beforeCuts rank cut) (beforeCuts (initialMass) (history)) := by
  have bill := P1_7_4.bill_bound_with_final 22 (beforeCuts rank cut) (beforeCuts (initialMass) (history))
    ini.jointLive ini.jointLost ?_ ?_ ?_
  · rw [show 22=21+1 by decide,sum_range_succ'] at bill
    have final : ini.jointLive 22 = ini.final := by simp [Initial.jointLive,Initial.live]
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
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 21,dotQ (cut i) (massQ (ini.lost i))) ≤
      weightedBill 22 (beforeCuts rank cut) (beforeCuts initialMass history) :=
  (le_add_of_nonneg_right (P1_7_4.final_credit_nonneg 22 (beforeCuts rank cut) ini.final)).trans
    (ini.joint_bill_with_final rank cut)

end Lower6960.Prefix6969MiddleRefit

end
end Merged_R6960MainGeometryBills

section Merged_R6960MainGeometryInvoice

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969MiddleRefit
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

private theorem checked_rates (i : Fin 21) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate i.val : ℚ) ∧
      min seedLimit (dotQ (cutWeight 0 i.val) (history i.val)) ≤ (degreeRate i.val : ℚ) ∧
      heightBound (degreeRate i.val) ≤ (heightRate i.val : ℚ) := by
  fin_cases i <;> decide +kernel

theorem rate_spec {i : ℕ} (hi : i<21) :
    RateOK (degreeRate i) (heightRate i) ∧
      min seedLimit (dotQ (cutWeight 0 i) (history i)) ≤ degreeRate i := by
  obtain ⟨base,degree,height⟩ := checked_rates ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def rankB : ℕ := initialCap 2+2

def rankJ : ℕ := initialCap 1+1

def pivot : ℚ := min ((3/5 : ℚ) * rankJ) (tau*rankB)

def rankWeight : Mass :=
  ![0,4*lambda*rankB*tau+mu-4*lambda*pivot,4*lambda*rankJ*(1-tau)+rankB,0]

def rankRound : ℚ := rankWeight 1+2*rankWeight 2+2*lambda*pivot^2+1

def lossWeight (i : ℕ) : Mass :=
  fun k=>(degreeRate i : ℚ)*cutWeight 0 i k+(heightRate i : ℚ)*cutWeight 1 i k

def lossLimit : ℚ :=
  weightedBill 22 (beforeCuts rankWeight lossWeight) (beforeCuts initialMass history)+seedLimit+rankRound

def mainFee : ℕ := lossLimit.ceil.toNat+pointLimit.ceil.toNat+initialSeedLimit+initialCap 0+
  fixedLimit+contentLimit

theorem main_fee_exact : mainFee = prefixCap := by decide +kernel

theorem retained_credit_guard (k : Fin 4) :
    (retainedCredit k : ℚ) ≤ P1_7_4.running (beforeCuts rankWeight lossWeight) 22 k := by
  fin_cases k <;> decide +kernel

theorem rank_guard : rankB<p ∧ 0≤rankWeight 1 ∧ 0≤rankWeight 2 := by decide +kernel

end Lower6960.Prefix6969MiddleRefit

end
end Merged_R6960MainGeometryInvoice
end Z6969Source0681

-- Source: Research6969.PrefixMiddleRefit
section Z6969Source0682
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960MainGeometryFee
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.Prefix6969MiddleRefit
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
    (C : CutBooks ini) (hiM : M.overhead.toNat≤2557) {i : ℕ} (hi : i<21) :
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
    Finset K := ini.rankMarks ∪ (range 21).biUnion (fun i=>curveMarks R.family (C.cover i))
/-- The retained weight is charged on every component of the terminal parent mass. -/
def retainedCharge (S : Finset (Ideal Ambient)) : ℕ :=
  ∑ k : Fin 4, retainedCredit k * mass S k

theorem retainedCharge_cast_le (S : Finset (Ideal Ambient)) :
    (retainedCharge S : ℚ) ≤
      dotQ (P1_7_4.running (beforeCuts rankWeight lossWeight) 22) (massQ S) := by
  unfold retainedCharge dotQ massQ
  push_cast
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
    (retained_credit_guard k) (Nat.cast_nonneg _))

theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤2557) : C.lossMarks.card + retainedCharge ini.final ≤ lossLimit.ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (ini.rankMarks.card : ℚ) +
      ∑ i∈range 21,((curveMarks R.family (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ ini.rankMarks.card +
      ∑ i∈range 21,(curveMarks R.family (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem))
    (s:=range 21)
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
      (∀ k, massQ ini.final k ≤ history 20 k) ∧
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
      · have mark : γ∈(range 21).biUnion (fun i=>curveMarks R.family (C.cover i)) :=
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
      (∀ k, massQ ini.final k ≤ history 20 k) ∧
      (∀ q∈S, Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S, ∃ J∈ini.final, q.asIdeal = J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks, γ∈C.paid ∨ ∃ q∈S, OnSurface F q γ := by
  obtain ⟨R⟩ := rows F Crt lo hi noPole residues
  obtain ⟨ini, C, S, paid, massCap, regular, origins, covered⟩ :=
    R.main_prefix hi noPole residues
  exact ⟨R, ini, C, S, paid, massCap, regular, origins, covered⟩

end Lower6960.Prefix6969MiddleRefit

end
end Merged_R6960MainGeometryFee
end Z6969Source0682

-- Source: Research6969.PrefixMiddleOuter
section Z6969Source0683
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969MiddleOuter
noncomputable section

open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated nodeL)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

/-- Split using the actual outer prefix, and derive the native physical
baseline of every nontrivial exception at the middle endpoint. -/
theorem split {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2412 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2557)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ R : Prefix6969MiddleRefit.Rows F Crt, R.out.exception = 1 ∨
      ∃ phys : HelperPhysicalModel.Model Crt R.out.exception,
        PrefixRows.Common (evaluated Crt (word M) Prefix6969MiddleHelper.helperBank.shape
          (Prefix6969MiddleHelper.helperCutoff M.overhead.toNat)) R.out.exception ∧
        R.out.exception.natDegree = 1 ∧
        1 ≤ jetDegree R.out.exception ∧ jetDegree R.out.exception ≤ 7 ∧
        1 ≤ seedDegree R.out.exception ∧ seedDegree R.out.exception ≤ 61 ∧
        (2 ≤ jetDegree R.out.exception → seedDegree R.out.exception ≤ 56) ∧
        jetDegree R.out.exception * 128514 - 1 ≤ RawPhysicalDegree.weight
          (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw := by
  obtain ⟨R⟩ := Prefix6969MiddleRefit.rows F Crt lo hi noPole residues
  refine ⟨R, ?_⟩
  rcases R.out.kind with unit | common
  · exact Or.inl unit
  have hiAll : M.overhead.toNat ≤ 33755 := hi.trans (by decide)
  obtain ⟨line, jd, jmax, sd, smax, nonlinear⟩ :=
    Prefix6969MiddleHelper.helper_common_caps Crt (word M) lo hiAll
      common.1 common.2.2.1 common.2.1 common.2.2.2
  obtain ⟨phys⟩ := HelperPhysicalModel.exists_model Crt common.1 common.2.1
  have hraw : 0 < 131071-M.overhead.toNat := by omega
  have lower := HelperWeightCap.weight_lower phys common.1.ne_zero _ hraw
  have endpoint : 128514 ≤ 131071-M.overhead.toNat := by omega
  have m := Nat.mul_le_mul_left (jetDegree R.out.exception) endpoint
  rw [Nat.mul_comm (jetDegree R.out.exception) (131071-M.overhead.toNat)] at m
  rw [line] at lower
  exact Or.inr ⟨phys, common, line, jd, jmax, sd, smax, nonlinear, by omega⟩

end
end Lower6960.Prefix6969MiddleOuter
end Z6969Source0683

-- Source: Research6969.PrefixMiddleTransfer
section Z6969Source0684
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969MiddleTransfer
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet Equation jetAt)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (Ambient toJet UsesSeed)
open K1_14_2_2 (Active RowCaps mass)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open Far6969RescueGeometry (Model Family OnSurface word)
open Prefix6969Main (Pricing Band)
open Prefix6969Rescue (EarlyPrice graphShape)
open Research6969 Research6966
open scoped Classical BigOperators

abbrev fee : ℕ := 231373953658241386
abbrev ordCredit : ℕ := 131528572298280
abbrev seedCredit : ℕ := 1592972508796
abbrev grade : ℕ := 342
abbrev width : ℕ := 6105

structure Packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) where
  paid : Finset K
  parents : Finset Surface
  projected : Equation
  project : JointProjection.Product parents projected
  geo : ∀ q∈parents,Parent q
  terminal : ∀ q∈parents,TerminalBanks.Pass Crt (word M) 179730 Research6969.SpreadCatalogue.shape q
  degree_cap : projected.natDegree ≤ grade
  seed_cap : K1_14_4.seedDegree projected ≤ width
  bill : paid.card+ordCredit*projected.natDegree+seedCredit*K1_14_4.seedDegree projected≤fee
  cover : ∀ z∈Γ,z∈paid ∨ ∃q∈parents,OnSurface F q z

private theorem cap_nat {n k : ℕ} {q : ℚ}
    (cap : (n : ℚ) ≤ q) (rounded : q < (k : ℚ)+1) : n ≤ k := by
  apply Nat.le_of_lt_succ
  exact_mod_cast cap.trans_lt rounded

structure Budget (mp : Pricing) (rp : EarlyPrice) where
  mDegree : ℕ
  mWidth : ℕ
  rDegree : ℕ
  rWidth : ℕ
  marked : Bool

def Budget.extra {mp rp} (b : Budget mp rp) : ℕ :=
  if b.marked then
    (JointLedger.coefficient b.rDegree-rp.credit 1)*b.rWidth+2*b.rDegree^2
  else
    (JointRouted.seedWeight 133628 rp.seed^2-rp.credit 0)*b.rDegree+
    (2*JointRouted.seedWeight 133628 rp.seed*JointRouted.ordWeight 133628 (rp.degree-1)-rp.credit 1)*b.rWidth

def Budget.adjust {mp rp} (b : Budget mp rp) : ℕ :=
  (ordCredit-mp.retainedCredit 0)*b.mDegree+(seedCredit-mp.retainedCredit 1)*b.mWidth

structure Budget.Valid {mp rp} (b : Budget mp rp) (main : Prefix6969Main.Plan)
    (rescue : Prefix6969Rescue.Plan) : Prop where
  mDegree : main.history main.last 0 < (b.mDegree : ℚ)+1
  mWidth : main.history main.last 1 < (b.mWidth : ℚ)+1
  rDegree : rescue.history rp.stop 0 < (b.rDegree : ℚ)+1
  rWidth : rescue.history rp.stop 1 < (b.rWidth : ℚ)+1
  grade : b.mDegree ≤ grade
  width : b.mWidth ≤ width
  tame : b.marked=true → b.rDegree<64 ∧ (2*b.rDegree-1)*b.rWidth<p
  fee : mp.fee+rp.fee+b.extra+b.adjust≤fee

theorem settle {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    {main : Prefix6969Main.Plan} {mp : Pricing}
    (mainValid : main.Valid) (mainPrice : mp.Valid main Band.middle)
    {extra a low floor : ℕ}
    (mainSource : main.Sources 2412 2557 Prefix6969MiddleHelper.helperBank extra a low floor)
    {rescue : Prefix6969Rescue.Plan} {rp : EarlyPrice}
    (rescueSource : rescue.Sources 2412 2557) (rescuePrice : rp.Valid rescue Band.middle)
    (b : Budget mp rp) (checks : b.Valid main rescue)
    (lo : 2412 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2557)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G rescue.primeShape)
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969MiddleHelper.helperBank.shape
      (Prefix6969MiddleHelper.helperCutoff M.overhead.toNat)) G)
    (nonlinear : 2 ≤ jetDegree G)
    (mainDegree : a ≤ jetDegree G) (mainSeed : low ≤ seedDegree G)
    (mainFloor : floor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (rescueDegree : rescue.degree ≤ jetDegree G) (rescueSeed : rescue.seedFloor ≤ seedDegree G)
    (rescueFloor : rescue.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (Packet F Crt) := by
  obtain ⟨R,J,Q,B,paid,A,S,_,pay,ms,rs,mg,mo,rg,covered⟩ :=
    Prefix6969Pair.produce F Crt mainValid mainPrice mainSource rescueSource rescuePrice (by decide)
      lo hi noPole residues phys prime slope seeded caps known mainDegree mainSeed mainFloor
      rescueDegree rescueSeed rescueFloor
  have ma (P) (mem : P∈J.final) : Active P := (J.kept_geom (mem_filter.mp mem).1).1
  have ra (P) (mem : P∈B.final) : Active P :=
    (Q.parent_geom (Prefix6969Rescue.Invoice.Book.final_initial B mem)).1
  let T := Γ.filter (fun γ => jetAt G (M.label γ) (F.scalar γ)=0 ∧
    Prefix6969Rescue.regular G (M.label γ) (F.scalar γ) ∧ ∃q∈S,OnSurface F q γ)
  have tr : T⊆Γ := filter_subset _ _
  have rgeo : ∀ q∈S,Parent q := fun q h => (rg q h).1
  have rorigin : ∀ q∈S,∃P∈B.final,q.asIdeal=P.comap toJet := fun q h => (rg q h).2.2
  have ton : ∀γ∈T,∃q∈S,OnSurface F q γ := fun _ h => (mem_filter.mp h).2.2.2
  have rd := cap_nat (rs 0) checks.rDegree
  have rw := cap_nat (rs 1) checks.rWidth
  have exit : T.card ≤ Prefix6969Rescue.Invoice.charge B rp.credit+b.extra := by
    cases hm : b.marked
    · have cc : RowCaps G (graphShape rp.degree rp.seed) := rescuePrice.graph_shape ▸ caps
      have ph : 131071+M.overhead≤(133628:ℤ) := by omega
      simpa only [Budget.extra,hm,Bool.false_eq_true,ite_false,Prefix6969Rescue.Invoice.charge,add_assoc] using
        Prefix6969Early.graph_exit F tr prime slope nonlinear rescuePrice.seed_pos cc ph
          (by decide) (by decide) (by decide) rgeo B.final ra rorigin ton
          (fun _ h => (mem_filter.mp h).2.1) (fun _ h => (mem_filter.mp h).2.2.1) rp.credit rd rw
    · obtain ⟨small,char⟩ := checks.tame hm
      simpa only [Budget.extra,hm,ite_true,Prefix6969Rescue.Invoice.charge,add_assoc] using
        Prefix6969Early.marked_exit F tr hi rgeo B.final ra rorigin ton rp.credit rd rw small char
  obtain ⟨f,project⟩ := JointProjection.exists_product A (fun q h => (mg q h).1)
  have measures := JointProjection.measures project J.final ma mo
  have md := cap_nat (ms 0) checks.mDegree
  have mv := cap_nat (ms 1) checks.mWidth
  have cov0 := Prefix6969Early.compensate ordCredit (mp.retainedCredit 0) (mass J.final 0) b.mDegree md
  have cov1 := Prefix6969Early.compensate seedCredit (mp.retainedCredit 1) (mass J.final 1) b.mWidth mv
  have adj : ordCredit*f.natDegree+seedCredit*K1_14_4.seedDegree f ≤ mp.charge J.final+b.adjust := by
    have pr0 := Nat.mul_le_mul_left ordCredit measures.1
    have pr1 := Nat.mul_le_mul_left seedCredit measures.2
    unfold Pricing.charge Budget.adjust
    simp only [Fin.sum_univ_four]
    omega
  refine ⟨⟨paid∪T,A,f,project,fun q h=>(mg q h).1,fun q h=>(mg q h).2,
    (measures.1.trans md).trans checks.grade,(measures.2.trans mv).trans checks.width,?_,?_⟩⟩
  · have union := card_union_le paid T
    have total := checks.fee
    omega
  · intro γ mem
    rcases covered γ mem with taken|⟨_,q,hq,on⟩|resc
    · exact Or.inl (mem_union_left _ taken)
    · exact Or.inr ⟨q,hq,on⟩
    · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨mem,resc⟩))

end
end Lower6960.Prefix6969MiddleTransfer
end Z6969Source0684

-- Source: Research6969.PrefixMiddleOrdinary
section Z6969Source0685
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969MiddleTransfer
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (toJet)
open K1_14_2_2 (Active mass)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open Far6969RescueGeometry (Model Family OnSurface word)
open Research6969 Research6966
open scoped Classical BigOperators Differential

abbrev affineFee : ℕ :=
  p*61+(3*(133628*61)^2*(262144-133628)^3)/(179730-133628)^3

private theorem affine_roots {u deleted} {M : Model u deleted} {Γ T : Finset K}
    (F : Family M Γ) (sub : T⊆Γ) (hi : M.overhead.toNat≤2557)
    {G : Jet} (prime : Prime G) (slope : G.natDegree=1) (affine : jetDegree G=1)
    (width : seedDegree G≤61) (roots : ∀γ∈T,jetAt G (M.label γ) (F.scalar γ)=0) :
    T.card≤affineFee := by
  obtain ⟨graph,N,gp,eq,deg⟩ := HelperGraph.of_prime prime slope
  let ev (γ : K) := eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
    (atX (F.scalar γ).derivative)
  let q (γ : K) : Surface := ⟨RingHom.ker (ev γ), RingHom.ker_isPrime _⟩
  have own : NativeAffineRows.Owned F T (T.image q) N := by
    intro z hz
    refine ⟨q z,mem_image.mpr ⟨z,hz,rfl⟩,?_,fun _ h=>h⟩
    rw [eq]
    exact roots z hz
  have cap j i : (N.poly.coeff j).coeff i ∈ MvPolynomial.restrictWeightAtMost (fun _=>1) 61 := by
    rw [eq]
    apply MvPolynomial.mem_restrictWeightAtMost.mpr
    intro m hm
    rw [←Finsupp.degree_eq_weight_one]
    exact (MvPolynomial.le_totalDegree hm).trans ((K1_14_2_2_2_1.seedDegree_le G 61).mp width j i)
  exact NativeAffineTariff.price_floor F sub N gp (deg.trans affine) 61 (by decide) cap
    (by decide) 133628 (by omega) (by decide) (by decide) (by decide) (by decide) own

/-- The refitted actual main packet transfers when the outer exception is
a unit or its affine zero marks have been paid. -/
theorem ordinary {u del} {M : Model u del} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D}
    (R : Prefix6969MiddleRefit.Rows F Crt)
    (hi : M.overhead.toNat≤2557)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    (mode : R.out.exception=1 ∨ Prime R.out.exception ∧ R.out.exception.natDegree=1 ∧
      jetDegree R.out.exception=1 ∧ seedDegree R.out.exception≤61) :
    Nonempty (Packet F Crt) := by
  obtain ⟨J,C,A,pay,ms,mg,mo,covered⟩:=R.main_prefix hi noPole residues
  let T := Γ.filter (fun γ=>jetAt R.out.exception (M.label γ) (F.scalar γ)=0)
  have affinePay : T.card≤affineFee := by
    rcases mode with unit | ⟨prime,slope,affine,width⟩
    · have empty : T=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro γ mem
        have root := (mem_filter.mp mem).2
        simpa [unit,jetAt] using root
      simp [empty]
    · exact affine_roots F (filter_subset _ _) hi prime slope affine width
        (fun _ h=>(mem_filter.mp h).2)
  have ma (P) (mem : P∈J.final) : Active P := (J.kept_geom (mem_filter.mp mem).1).1
  obtain ⟨f,project⟩ := JointProjection.exists_product A (fun q h => (mg q h).1)
  have measures := JointProjection.measures project J.final ma mo
  have md : mass J.final 0≤335 := by
    apply Nat.le_of_lt_succ
    have q := ms 0
    change (mass J.final 0:ℚ)≤459151/1369 at q
    exact_mod_cast q.trans_lt (by decide +kernel : (459151:ℚ)/1369<336)
  have mv : mass J.final 1≤4559 := by
    apply Nat.le_of_lt_succ
    have q := ms 1
    change (mass J.final 1:ℚ)≤12482743/2738 at q
    exact_mod_cast q.trans_lt (by decide +kernel : (12482743:ℚ)/2738<4560)
  let w := Prefix6969MiddleRefit.retainedCredit
  let adjust := (ordCredit-w 0)*335+(seedCredit-w 1)*4559
  have adj : ordCredit*f.natDegree+seedCredit*K1_14_4.seedDegree f ≤
      Prefix6969MiddleRefit.retainedCharge J.final+adjust := by
    have cov0 := Prefix6969Early.compensate ordCredit (w 0) (mass J.final 0) 335 md
    have cov1 := Prefix6969Early.compensate seedCredit (w 1) (mass J.final 1) 4559 mv
    have pr0 := Nat.mul_le_mul_left ordCredit measures.1
    have pr1 := Nat.mul_le_mul_left seedCredit measures.2
    unfold Prefix6969MiddleRefit.retainedCharge adjust
    change _ ≤ (∑k,w k*mass J.final k)+_
    simp only [Fin.sum_univ_four]
    omega
  have total : Prefix6969MiddleRefit.prefixCap+adjust+affineFee≤fee := by decide +kernel
  refine ⟨⟨C.paid∪T,A,f,project,fun q h=>(mg q h).1,fun q h=>(mg q h).2,
    (measures.1.trans md).trans (by decide),(measures.2.trans mv).trans (by decide),?_,?_⟩⟩
  · have union := card_union_le C.paid T
    omega
  · intro γ mem
    by_cases root : jetAt R.out.exception (M.label γ) (F.scalar γ)=0
    · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨mem,root⟩))
    · rcases covered γ (mem_filter.mpr ⟨mem,root⟩) with paid | surface
      · exact Or.inl (mem_union_left _ paid)
      · exact Or.inr surface

end
end Lower6960.Prefix6969MiddleTransfer
end Z6969Source0685

-- Source: Research6969.PrefixMiddleCases
section Z6969Source0686
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969MiddleTransfer
noncomputable section

open Finset Polynomial
open K1_14 (Jet Seeds Equation)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Prefix6969Main (Band)
open Prefix6969Rescue (graphShape)
open Research6966

/-- All fields are closed bank, interval and fee certificates from an actual saved event. -/
structure Case (a l u : ℕ) where
  main : Prefix6969Main.Plan
  mp : Prefix6969Main.Pricing
  valid : main.Valid
  mainPrice : mp.Valid main Band.middle
  mainSource : main.Sources 2412 2557 Prefix6969MiddleHelper.helperBank 128513 a l (a*128514-1)
  rescue : Prefix6969Rescue.Plan
  rp : Prefix6969Rescue.EarlyPrice
  rescueSource : rescue.Sources 2412 2557
  rescuePrice : rp.Valid rescue Band.middle
  rdegree : rescue.degree=a
  rshape : rescue.primeShape=graphShape a u
  rseed : rescue.seedFloor=l
  rfloor : rescue.physicalFloor=a*128514-1
  budget : Budget mp rp
  checks : budget.Valid main rescue

theorem prime_of_irred {G : Jet} (irr : Irreducible G) : Prime G := by
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D:=Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D:=Equation)
  exact irr.prime

theorem Case.run {a l u : ℕ} (c : Case a l u)
    {u₀ del} {M : Model u₀ del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2412 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2557)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G)
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969MiddleHelper.helperBank.shape
      (Prefix6969MiddleHelper.helperCutoff M.overhead.toNat)) G)
    (slope : G.natDegree=1) (degree : jetDegree G=a) (nonlinear : 2≤a)
    (seed : l≤seedDegree G) (upper : seedDegree G≤u)
    (floor : a*128514-1≤RawPhysicalDegree.weight
      (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (Packet F Crt) := by
  have caps : RowCaps G c.rescue.primeShape := by
    rw [c.rshape]
    intro j i hn
    have h : G.coeff j ≠ 0 := fun eq => hn (by simp [eq])
    exact ⟨(K1_14_2_2_2_1.jetDegree_le G a).mp degree.le j i hn,
      (le_natDegree_of_ne_zero h).trans slope.le,
      (K1_14_2_2_2_1.seedDegree_le G u).mp upper j i⟩
  exact settle F Crt c.valid c.mainPrice c.mainSource c.rescueSource c.rescuePrice
    c.budget c.checks lo hi noPole residues phys (prime_of_irred known.1) slope known.2.2.1 caps known
    (degree.symm ▸ nonlinear) degree.ge seed floor
    (c.rdegree.symm ▸ degree.ge) (c.rseed.symm ▸ seed) (c.rfloor.symm ▸ floor)

end
end Lower6960.Prefix6969MiddleTransfer
end Z6969Source0686

-- Source: Research6969.PrefixNearEarlyCases
section Z6969Source0687
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969Early
noncomputable section

open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Prefix6969Main (Band)
open Prefix6969Rescue (graphShape)
open Far6969RescueGeometry (Model Family word)
open Research6966

structure NearCase (a l u w : ℕ) where
  main : Prefix6969Main.Plan
  mp : Prefix6969Main.Pricing
  valid : main.Valid
  mainPrice : mp.Valid main Band.near
  mainSource : main.Sources 2314 2411 Prefix6969Helper.helperBank 128659 a l w
  rescue : Prefix6969Rescue.Plan
  rp : Prefix6969Rescue.EarlyPrice
  rescueSource : rescue.Sources 2314 2411
  rescuePrice : rp.Valid rescue Band.near
  rdegree : rescue.degree=a
  rshape : rescue.primeShape=graphShape a u
  rseed : rescue.seedFloor=l
  rfloor : rescue.physicalFloor=w
  exit : Exit
  checks : exit.Valid main rescue rp

def NearCase.fee {a l u w} (c : NearCase a l u w) : ℕ :=
  c.mp.fee+c.rp.fee+c.exit.extra Band.near c.rp

theorem NearCase.run {a l u w : ℕ} (c : NearCase a l u w)
    {u₀ del} {M : Model u₀ del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G)
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (slope : G.natDegree=1) (degree : jetDegree G=a) (nonlinear : 2≤a)
    (seed : l≤seedDegree G) (upper : seedDegree G≤u)
    (floor : w≤RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (Packet F Crt c.fee (c.mp.retainedCredit 0) (c.mp.retainedCredit 1+c.mp.retainedCredit 2)
      c.exit.mDegree c.exit.mWidth) := by
  have caps : RowCaps G c.rescue.primeShape := by
    rw [c.rshape]
    intro j i hn
    have h : G.coeff j ≠ 0 := fun eq => hn (by simp [eq])
    exact ⟨(K1_14_2_2_2_1.jetDegree_le G a).mp degree.le j i hn,
      (le_natDegree_of_ne_zero h).trans slope.le,
      (K1_14_2_2_2_1.seedDegree_le G u).mp upper j i⟩
  exact settle F Crt c.valid c.mainPrice c.mainSource c.rescueSource c.rescuePrice
    c.exit c.checks (by decide) lo hi noPole residues phys
    (Prefix6969MiddleTransfer.prime_of_irred known.1) slope known.2.2.1 caps known
    (degree.symm ▸ nonlinear) degree.ge seed floor
    (c.rdegree.symm ▸ degree.ge) (c.rseed.symm ▸ seed) (c.rfloor.symm ▸ floor)

end
end Lower6960.Prefix6969Early
end Z6969Source0687

-- Source: Research6969.PrefixNearLowWeight
section Z6969Source0688
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969Early
noncomputable section

open Finset Polynomial
open K1 (K I p)
open K1_14 (Jet jetAt L)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct nodeL)
open Far6969RescueGeometry (Model Family)
open Research6966

abbrev lowFee : ℕ := 21000000000000000
abbrev seed (i : Fin 56) : ℕ := i.val+1
def threshold (i : Fin 56) : ℕ :=
  ![308387,308378,308364,308344,308319,308288,308251,308209,
    308161,308107,308048,307983,307912,307836,307754,307664,
    307566,307462,307353,307237,307116,306989,306855,306716,
    306571,306420,306263,306100,305932,305757,305576,305390,
    305197,304999,304795,304585,304368,304146,303918,303684,
    303445,303199,302947,302690,302426,302157,301881,301600,
    301313,301020,300721,300416,300105,299788,299466,299137] i
private def votes (i : Fin 56) : ℕ := 179730-(threshold i-1-128659)
private def bad (i : Fin 56) : ℕ := 3*(seed i+p*seed i)
private def upper (i : Fin 56) : ℕ :=
  ((262144-179730)*((2*133482-1)*seed i)+179730)^2/(179730-133482)^2

private theorem receipt (i : Fin 56) :
    0<votes i ∧ bad i≤lowFee ∧ 262144*upper i≤(lowFee-bad i)*votes i := by
  fin_cases i <;> decide +kernel

private theorem per_node {d : ℕ} (hd : d≤133482) (i : Fin 56) :
    ((262144-179730)*((2*d-1)*seed i)+(179730-d))^2/(179730-d)^2≤upper i := by
  have power:(2*d-1)*seed i≤(2*133482-1)*seed i:=Nat.mul_le_mul_right _ (by omega)
  have top:(262144-179730)*((2*d-1)*seed i)+(179730-d)≤
      (262144-179730)*((2*133482-1)*seed i)+179730 :=
    Nat.add_le_add (Nat.mul_le_mul_left _ power) (Nat.sub_le ..)
  have bottom:(179730-133482)^2≤(179730-d)^2:=Nat.pow_le_pow_left (by omega) 2
  exact (Nat.div_le_div_right (Nat.pow_le_pow_left top 2)).trans
    (Nat.div_le_div_left bottom (by decide))

/-- Count all marks of the original quadratic helper in the low physical
weight interval directly on the production word family. -/
theorem low_quadratic_count {u del} {M : Model u del} {Γ T : Finset K}
    (F : Family M Γ) (sub : T⊆Γ)
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D}
    (lo : 2314≤M.overhead.toNat) (hi : M.overhead.toNat≤2411)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈T,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (ns : G.natDegree=1) (quad : K1_14_2_2_2_1.jetDegree G=2) (i : Fin 56)
    (cap : K1_14_2_2_2_1.seedDegree G≤seed i)
    (low : RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw<threshold i)
    (root : ∀ γ∈T,jetAt G (M.label γ) (F.scalar γ)=0) :
    T.card≤lowFee := by
  let h := M.overhead.toNat
  let d : ℕ := 131071+h
  let W := RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw
  let v := 179730-(W-(131071-h-1))
  have hp : 0<h := by omega
  have hs : h≤131070 := by omega
  have hd : d≤133482 := by dsimp [d,h]; omega
  have sw : seed i≤56 := by have := i.isLt; dsimp [seed]; omega
  have nodes (j : I) : (poleProduct D).eval (algebraMap K L (K1.node j))≠0 := by
    rw [poleProduct,eval_mul]
    exact mul_ne_zero (noPole 0 j) (noPole 1 j)
  have height : 131071+M.overhead≤(d:ℤ) := by dsimp [d,h]; push_cast; omega
  have cnt := PhysicalHelperTariff.price F sub hp hs phys prime ns quad (seed i) d
    ((K1_14_2_2_2_1.seedDegree_le G (seed i)).mp cap) (by change 3*seed i<2130706433; omega)
    height le_rfl (hd.trans_lt (by decide)) (hd.trans_lt (by decide)) nodes residues root
  rw [show Fintype.card I=262144 from Fintype.card_fin (2^18)] at cnt
  change T.card*v≤bad i*v+262144*
    (((262144-179730)*((2*d-1)*seed i)+(179730-d))^2/(179730-d)^2) at cnt
  have vv : votes i≤v := by
    unfold votes v W
    dsimp [h]
    omega
  obtain ⟨pos,feeFit,paid⟩ := receipt i
  have bill : 262144*(((262144-179730)*((2*d-1)*seed i)+(179730-d))^2/(179730-d)^2)
      ≤(lowFee-bad i)*v :=
    (Nat.mul_le_mul_left _ (per_node hd i)).trans
      (paid.trans (Nat.mul_le_mul_left _ vv))
  apply Nat.le_of_mul_le_mul_right _ (pos.trans_le vv)
  apply cnt.trans
  calc
   _ ≤ bad i*v+(lowFee-bad i)*v := Nat.add_le_add_left bill _
   _ = _ := by rw [←Nat.add_mul,Nat.add_sub_of_le feeFit]

end
end Lower6960.Prefix6969Early
end Z6969Source0688

-- Source: Research6969.PrefixNearLightSource
section Z6969Source0689
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src900000 : Request := ⟨⟨⟨556,772,170,8941⟩,5255817068544,9968090926⟩,10,3,2,385978,2⟩
private theorem shift900000_2314 : (PhysicalWindow.Triangular src900000) 2314 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift900000_2319 : (PhysicalWindow.Triangular src900000) 2319 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift900000_2335 : (PhysicalWindow.Triangular src900000) 2335 2385 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift900000_2386 : (PhysicalWindow.Triangular src900000) 2386 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover900000 : PhysicalWindow.Cover (PhysicalWindow.Triangular src900000) 2411 2314 [2318, 2334, 2385, 2411] := by
  exact ⟨by decide, by decide, shift900000_2314, by decide, by decide, shift900000_2319, by decide, by decide, shift900000_2335, by decide, by decide, shift900000_2386, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source0689

-- Source: Research6969.PrefixMainHeightFast
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
      Prefix6969Wide.mu = _
    unfold slope constant Band.lambda Band.mu Prefix6969Rates.density
    norm_num [Band.last, Prefix6969Rates.endpointDegree, Prefix6969Wide.mu, Prefix6969Rates.siteRatio]; ring
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


def CriticalHeight (b : Band) (a k h : ℕ) : Prop :=
  0 < k ∧ k ≤ 80 ∧
    (k = 1 ∨ 0 ≤ linear b a - quadratic b a * (2*(k:ℚ)-1)) ∧
    (k = 80 ∨ linear b a - quadratic b a * (2*(k:ℚ)+1) ≤ 0) ∧
    max 0 (1-(a:ℚ)*k/((p+1:ℕ):ℚ)) * b.curveUnit k ≤ h

instance (b : Band) (a k h : ℕ) : Decidable (CriticalHeight b a k h) := by
  unfold CriticalHeight
  infer_instance

def CriticalTable (b : Band) (x : Pricing) (s : Plan) (ks : List ℕ) : Prop :=
  ∀ i : Fin s.count, CriticalHeight b (x.degreeRate i) (ks.getD i 0) (x.heightRate i)

instance (b : Band) (x : Pricing) (s : Plan) (ks : List ℕ) :
    Decidable (CriticalTable b x s ks) := by
  unfold CriticalTable
  infer_instance

theorem height_from_table (b : Band) (x : Pricing) (s : Plan) (ks : List ℕ)
    (h : CriticalTable b x s ks) (i : Fin s.count) :
    heightBound b (x.degreeRate i) ≤ (x.heightRate i : ℚ) := by
  obtain ⟨lo, hi, left, right, top⟩ := h i
  exact height_from_critical _ _ _ _ lo hi left right top

end
end Lower6960.Prefix6969Main.Pricing
end Z6969Source0690

-- Source: Research6969.PrefixMainDataNearLight0
section Z6969Source0691
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.NearLight0
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 21, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank2 1529, bank8 1694, bank14 1831, bank23 1898, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank61 2536, bank73 5660, bank85 2903, bank74 6544, bank113 3716, bank140 3997, bank145 7920, bank119 41691, bank198 9780, bank212 10770, bank180 62680, bank174 148759, bank169 292467] i
  head := src900000
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14057, 174605, 816979, 4523341],
    ![23965/2, 600915/4, 1360223/2, 7573027/2],
    ![17372/3, 651028/9, 629864, 3352561],
    ![3599, 349091/8, 1054682/3, 16970018/9],
    ![16211/9, 267179/12, 3653911/16, 20054663/16],
    ![24292/27, 982003/81, 4462289/36, 26724649/36],
    ![73478/121, 1256654/121, 5668925/49, 26724649/36],
    ![73478/121, 1256654/121, 5668925/49, 11095781/18],
    ![73478/121, 1065931/121, 4774207/49, 401956],
    ![77324/147, 55722/7, 7704513/98, 401956],
    ![77324/147, 55722/7, 7704513/98, 401956],
    ![61324/121, 55722/7, 152557/2, 401956],
    ![61324/121, 853367/121, 14785796/225, 13808656/49],
    ![61324/121, 853367/121, 14785796/225, 13808656/49],
    ![1640767/3362, 10805516/1681, 48418840/841, 13808656/49],
    ![1330489/3362, 10805516/1681, 48418840/841, 13808656/49],
    ![1330489/3362, 7652644/1323, 51592497/1058, 239121],
    ![1330489/3362, 30778769/5476, 762875/16, 134812398/605],
    ![25627/74, 30778769/5476, 762875/16, 134812398/605],
    ![462882/1369, 30778769/5476, 762875/16, 134812398/605],
    ![459151/1369, 30778769/5476, 762875/16, 134812398/605]]

theorem valid : plan.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 1 257319 := by
  refine ⟨?_, rank154 8941, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover900000⟩⟩
  · intro i; fin_cases i
    · exact free2_0
    · exact free8_0
    · exact free14_0
    · exact free23_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free61_0
    · exact free73_0
    · exact free85_0
    · exact free74_2
    · exact free113_0
    · exact free140_0
    · exact free145_0
    · exact free119_0
    · exact free198_0
    · exact free212_0
    · exact free180_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨50/100, 60/100, [369682277, 369214345, 369708050, 369420357, 367979526, 369140742, 369184540, 369213117, 161390450, 162265921, 162320967, 162127482, 70659054, 79794220, 77671543, 103172481, 113643319, 113407496, 131941167, 179312344, 239402518], [933526, 934809, 933456, 934244, 938194, 935011, 934891, 934813, 2378021, 2363462, 2362547, 2365764, 5674981, 5001205, 5147836, 3821599, 3452305, 3460493, 2947278, 2120440, 1535667],
  ![127079644604760, 1601180678072, 215462266200, 4117078700], 208711235514694319⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,7,7,7,15,14,14,11,10,10,8,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 30778769/5476, 762875/16, 134812398/605] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.NearLight0
end Z6969Source0691
