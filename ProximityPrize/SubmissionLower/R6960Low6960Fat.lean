import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
import ProximityPrize.SubmissionLower.Final50Order
import ProximityPrize.SubmissionLower.R6960Low6960FatBanks
import ProximityPrize.SubmissionLower.R6960Low6960FatFactors
import ProximityPrize.SubmissionLower.R6960Low6960FatContacts
import ProximityPrize.SubmissionLower.R6960Low6960FatPadding

-- merged module ModelExactPole
section Merged_ModelExactPole

set_option Elab.async false
namespace ModelExactPole
noncomputable section
open P1 (I K node)
open K1_13 (Geom embed extend)
open Polynomial
open scoped Polynomial

/-- A common shift by a multiple of the pole preserves all labeled residues. -/
theorem exists_shifted {cap u del Γ A n} (M : P1.ModelAt cap u del) (F : P1.FamilyAt A M Γ)
    (T : (Polynomial K)) (multiple : M.E ∣ T) (positive : 1 ≤ n) (small : n ≤ 2600)
    (available : n ≤ M.E.natDegree) (degree : ∀ γ ∈ Γ, (F.scalar γ - T).natDegree ≤ 131071 + n) :
    ∃ P : K1_13.PoleData Γ (fun γ => F.scalar γ - T), P.H.natDegree = n := by
  have hmax : n ≤ (extend M.E).natDegree := by simpa only [extend, natDegree_map] using available
  obtain ⟨H, hm, hd, hdiv⟩ := K1_13.trim_divisor _ (M.E_monic.map embed) _ hmax
  let z := fun γ => embed (M.label γ)
  have unit {P : (Polynomial K)} (hp : IsCoprime P M.E) : IsCoprime (extend P) H :=
    (hp.map (Polynomial.mapRingHom embed)).of_isCoprime_of_dvd_right hdiv
  have amp (γ : K) : extend (M.amplitude γ) = extend M.A₀ + C (z γ) * extend M.A₁ := by
    simp [P1.ModelAt.amplitude, z]
  refine ⟨⟨H, hm, ?_, ?_, ?_, z, ?_, extend M.factor, extend M.Q, extend M.A₀,
    extend M.A₁, unit M.coprime_factor.symm, unit M.offset_reduced,
    unit M.first_amplitude_unit, ?_, ?_⟩, ?_⟩
  · rw [hd]
    exact ⟨positive, small⟩
  · intro i hz
    obtain ⟨U, hU⟩ := hdiv
    have he : (extend M.E).eval (embed (node i)) ≠ 0 := by
      rw [Polynomial.eval_map_apply]
      exact (map_ne_zero embed).mpr (M.E_nodes i)
    apply he
    change (M.E.map embed).eval _ = 0
    rw [hU, Polynomial.eval_mul, hz, zero_mul]
  · intro γ hγ
    rw [hd]
    exact degree γ hγ
  · intro a b hab
    exact sub_left_inj.mp (embed.injective hab)
  · intro γ hγ
    rw [← amp]
    exact unit (F.mark γ hγ).pole_unit
  · intro γ hγ
    have eqn := (F.mark γ hγ).identity
    have orig : M.factor * M.amplitude γ * F.scalar γ + C (M.label γ) * M.Q =
        M.E * M.decoder (F.mark γ hγ).bad := by rw [← eqn]; ring
    have mapped := congrArg (Polynomial.map embed) orig
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at mapped
    rw [← amp]
    have residue := mapped ▸ hdiv.trans (dvd_mul_right (extend M.E) (extend (M.decoder (F.mark γ hγ).bad)))
    have shift := hdiv.trans (Polynomial.map_dvd embed multiple)
    have sub := dvd_sub residue (shift.mul_left (extend M.factor * extend (M.amplitude γ)))
    simpa only [extend, Polynomial.map_sub, mul_sub, sub_add_eq_add_sub] using sub
  · exact hd

/-- Trim the pole to the actual overhead without changing any marked residue. -/
theorem exists_pole {cap u D Γ A} (M : P1.ModelAt cap u D) (F : P1.FamilyAt A M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2600) :
    ∃ P : K1_13.PoleData Γ F.scalar, P.H.natDegree = M.overhead.toNat := by
  have hmax : M.overhead.toNat ≤ (extend M.E).natDegree := by
    rw [Polynomial.natDegree_map]
    change M.overhead.toNat ≤ M.E.natDegree
    unfold P1.ModelAt.overhead
    omega
  have degree : ∀ γ ∈ Γ, (F.scalar γ - 0).natDegree ≤ 131071 + M.overhead.toNat := by
    intro γ hg
    rw [sub_zero]
    rcases (F.mark γ hg).scalar_degree with zero | h
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at h
      omega
  let HasPole (s : K → (Polynomial K)) : Prop :=
    ∃ P : K1_13.PoleData Γ s, P.H.natDegree = M.overhead.toNat
  have eq : (fun γ => F.scalar γ - 0) = F.scalar := funext fun γ => sub_zero _
  apply (congrArg HasPole eq).mp
  exact exists_shifted M F 0 (dvd_zero _) (by omega : 1 ≤ M.overhead.toNat)
    (by omega) (by simpa only [extend, natDegree_map] using hmax) degree

#print axioms exists_shifted
#print axioms exists_pole
end
end ModelExactPole

end Merged_ModelExactPole

-- merged module R6960Low6960Primary
section Merged_R6960Low6960Primary

noncomputable section
set_option Elab.async false
namespace Lower6960.Low
open P3 (I K node)
open K1_13 (Row Geom Shape shape InBox Contact)
open Wide50EulerPrimary (primary_family sourceRank layerNeed)
open scoped Polynomial

abbrev agreement : ℕ := 179818
abbrev physicalDegree : ℕ := 133429
abbrev primaryCutoff : ℕ := 3000*agreement-1
abbrev primaryRank : ℕ := sourceRank agreement physicalDegree
abbrev need : ℕ := layerNeed agreement physicalDegree

theorem certified_layers : need = 20767888279330 := by decide +kernel

/-- The common endpoint supplies all physical degree and agreement data
for every actual low-height mark. -/
theorem messages_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179818 M Γ) (hi : M.overhead ≤ 2358) :
    Set.InjOn F.scalar (Γ : Set K) ∧
      (∀ γ∈Γ,(F.scalar γ).natDegree≤physicalDegree) ∧
      ∀ γ∈Γ,∃ T : Finset I,agreement≤T.card ∧ ∀ i∈T,(F.scalar γ).eval (node i)=M.word i := by
  refine ⟨F.distinct,?_,?_⟩
  · intro γ hγ
    rcases (F.mark γ hγ).scalar_degree with zero | deg
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at deg
      change (F.scalar γ).natDegree≤133429
      omega
  · intro γ hγ
    let Mγ := F.mark γ hγ
    exact ⟨Mγ.bad.support,Mγ.bad.agreement,Mγ.scalar_hits⟩

/-- The native generic primary producer instantiated at the concrete 69.60
low endpoint. -/
theorem primary_at_endpoint (word : I→K) :
    ∃ e : Fin primaryRank→Row 4,LinearIndependent Geom e ∧
      ∀ i,InBox (shape (e i)) PrimaryTaper.primaryBox ∧
        PrimaryTaper.TrueWeightLE physicalDegree (e i) primaryCutoff ∧
        PrimaryTaper.JetsBounded (e i) ∧ Contact word (e i) :=
  primary_family agreement physicalDegree (by decide) (by decide) (by decide +kernel) word le_rfl

#print axioms certified_layers
#print axioms primary_at_endpoint
end Lower6960.Low

end
end Merged_R6960Low6960Primary

-- merged module R6960Low6960Fat
section Merged_R6960Low6960Fat


set_option Elab.async false
section
namespace Low6960Fat
noncomputable section
open K1 K1_13
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open P0_9_4 (clear_denominators)
open scoped Polynomial BigOperators
open P3_6_4 (eval_cleared order_cleared)
set_option maxRecDepth 2400 in
/-- Fat equations through height 2,358 at 179,818 agreements. -/
theorem fat_equations : Equations := by
  have h1 := Low6960FatBanks.proof
  have h2 := Low6960FatFactors.proof
  have h3 := Low6960FatContacts.proof
  intro w Γ s _ hhits P hheight
  have hw : Messages w Γ s := ⟨hhits⟩
  obtain ⟨L⟩ := K1_13_4_1.proof Γ s P
  obtain ⟨⟨F, neF, hF⟩, rank2⟩ := h1 w Γ s P L hheight
  obtain ⟨vanishes1, vanishes2⟩ := h3 w Γ s hw P L hheight
  obtain ⟨G, hG, ⟨D⟩⟩ := h2 w Γ s P L F neF ⟨hF.1.1, hF.2⟩ rank2
  have hOrders : ∀ γ ∈ Γ, PairOrders (toGeneric F) (toGeneric G)
      (inclConst (P.z γ)) (trajectory (extend (s γ))) := fun γ hγ =>
    ⟨vanishes1 F hF γ hγ, vanishes2 G hG γ hγ⟩
  obtain ⟨book, Q, hcard, hQ, htQ, hiQ, hcover⟩ :=
    eliminate_common Γ P.z (fun γ => extend (s γ)) P.injective D hOrders
  obtain ⟨J⟩ := padded27 D.left_ne D.right_ne D.proper D.left_caps D.right_caps
  let R := seedResultant27 (pad D.left J.a) (pad D.right J.b)
  obtain ⟨_, Q', _, suppQ, mapQ⟩ := clear_denominators Q
  obtain ⟨_, R', _, suppR, mapR⟩ := clear_denominators R
  have neQ : Q' ≠ 0 := by
    intro h
    rw [h, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at suppQ
    exact hQ suppQ
  have neR : R' ≠ 0 := by
    intro h
    rw [h, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at suppR
    exact J.nonzero suppR
  have totalQ : Q'.totalDegree ≤ 2502 := by
    simpa only [MvPolynomial.totalDegree, suppQ] using htQ
  have indexQ : indexDegree Q' ≤ 811 := by
    simpa only [K1_13.indexDegree, lowerIndex, suppQ] using hiQ
  have totalR : R'.totalDegree ≤ 367443000 := by
    have htR : R.totalDegree ≤ 367443000 := J.total
    simpa only [MvPolynomial.totalDegree, suppR] using htR
  have indexR : indexDegree R' ≤ 124200000 := by
    have hiR : lowerIndex R ≤ 124200000 := J.index
    simpa only [K1_13.indexDegree, lowerIndex, suppR] using hiR
  refine ⟨book, ⟨Q', R', neQ, neR, totalQ, indexQ, totalR, indexR⟩, hcard, ?_⟩
  intro γ hγ hb
  rcases hcover γ hγ hb with he | ho
  · exact Or.inl (eval_cleared mapQ _ he)
  · refine Or.inr (order_cleared mapR _ ?_)
    have hres : LowerOrder R (trajectory (extend (s γ))) 23893 :=
      resultant_order (pad D.left J.a) (pad D.right J.b) (inclConst (P.z γ)) _
        J.degree_left.le J.degree_right.le ⟨mixedOrder_pad J.a ho.1, mixedOrder_pad J.b ho.2⟩
    exact hres
end
end Low6960Fat
end

#print axioms Low6960Fat.fat_equations

namespace Lower6960.Low
open K1_13 (extend)
open Low6960Fat (Holds)

/-- The actual low family supplies common and resultant equations with the
revised resultant order. -/
theorem fat_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179818 M Γ) (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2358) :
    ∃ (book : Finset P1.K) (E : Low6960Fat.FatEquations), book.card≤140000 ∧
      ∀ γ∈Γ,γ∉book → Holds E (extend (F.scalar γ)) := by
  obtain ⟨_,deg,hits⟩ := messages_of_family M F hi
  obtain ⟨pole,hpole⟩ := ModelExactPole.exists_pole M F lo (hi.trans (by decide))
  have small : pole.H.natDegree≤2358 := by rw [hpole]; omega
  exact Low6960Fat.fat_equations M.word Γ F.scalar deg hits pole small

#print axioms fat_of_family
end Lower6960.Low

end Merged_R6960Low6960Fat
