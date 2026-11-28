import ProximityPrize.SubmissionLower.R6970Height2312Wide0

open _root_.Lower6960 _root_.Research6969
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960MainGeometry

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Research6970.Height2313.Lower6960.Prefix6969Wide
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt seedHasse)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual orderOn FixedPart)
open K1_14_2_2R (chainCompatible)
open HelperPrefix (timesShape)
open _root_.Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank helperCutoff)
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
    (lo : 2305≤M.overhead.toNat) (hi : M.overhead.toNat≤2411)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Nonempty (Rows F Crt) := by
  have hiAll : M.overhead.toNat ≤ 33755 := hi.trans (by decide)
  choose P inside nz using free_rows Crt (word M) lo hi
  obtain ⟨out⟩ := PrefixRows.prepare P freeShape copies _ _ nz
    (fun i => evaluated_shape Crt (word M) (inside i))
    (Research6970.Height2313.Lower6960.Prefix6969Helper.helper_nonzero Crt (word M) lo hiAll)
    (fun Q hQ => evaluated_shape Crt (word M) hQ)
    (fun _ _ g h cop => Research6970.Height2313.Lower6960.Prefix6969Helper.helper_not_two Crt (word M) lo hiAll
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
      have wh := Research6970.Height2313.Lower6960.Prefix6969Helper.helper_width lo hiAll
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

end Research6970.Height2313.Lower6960.Prefix6969Wide

end
end Merged_R6960MainGeometry
