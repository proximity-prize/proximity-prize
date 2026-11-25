import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
import ProximityPrize.SubmissionLower.Final50Order
import ProximityPrize.SubmissionLower.Fat6966Factors
import ProximityPrize.SubmissionLower.Fat6966Contacts
import ProximityPrize.SubmissionLower.Fat6966Padding
import ProximityPrize.SubmissionLower.Wide50EulerPrimaryFamily

set_option Elab.async false

-- merged module Fat6966Family
section Merged_Fat6966Family

-- merged module ModelExactPole6966
section Merged_ModelExactPole6966

set_option Elab.async false
namespace ModelExactPole6966
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
end ModelExactPole6966

end Merged_ModelExactPole6966

-- merged module R6960Low6960Primary
section Merged_R6960Low6960Primary

noncomputable section
set_option Elab.async false
namespace LowProfile6966
open P3 (I K node)
open K1_13 (Row Geom Shape shape InBox Contact)
open Wide50EulerPrimary (primary_family sourceRank layerNeed)
open scoped Polynomial

abbrev agreement : ℕ := 179769
abbrev physicalDegree : ℕ := 133400
abbrev primaryCutoff : ℕ := 3000*agreement-1
abbrev primaryRank : ℕ := sourceRank agreement physicalDegree
abbrev need : ℕ := layerNeed agreement physicalDegree

theorem certified_layers : need = 20088974187454 := by decide +kernel

/-- The common endpoint supplies all physical degree and agreement data
for every actual low-height mark. -/
theorem messages_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179769 M Γ) (hi : M.overhead ≤ 2329) :
    Set.InjOn F.scalar (Γ : Set K) ∧
      (∀ γ∈Γ,(F.scalar γ).natDegree≤physicalDegree) ∧
      ∀ γ∈Γ,∃ T : Finset I,agreement≤T.card ∧ ∀ i∈T,(F.scalar γ).eval (node i)=M.word i := by
  refine ⟨F.distinct,?_,?_⟩
  · intro γ hγ
    rcases (F.mark γ hγ).scalar_degree with zero | deg
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at deg
      change (F.scalar γ).natDegree≤133400
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
end LowProfile6966

end
end Merged_R6960Low6960Primary

-- merged module R6960Low6966Fat
section Merged_R6960Low6966Fat


set_option Elab.async false
section
namespace Low6966Fat
noncomputable section
open K1 K1_13
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open P0_9_4 (clear_denominators)
open scoped Polynomial BigOperators
open P3_6_4 (eval_cleared order_cleared)
set_option maxRecDepth 2400 in
/-- Fat equations through height 2,358 at 179,818 agreements. -/
theorem fat_equations : Equations := by
  have h1 := Low6966FatBanks.proof
  have h2 := Low6966FatFactors.proof
  have h3 := Low6966FatContacts.proof
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
  have totalQ : Q'.totalDegree ≤ 2945 := by
    simpa only [MvPolynomial.totalDegree, suppQ] using htQ
  have indexQ : indexDegree Q' ≤ 954 := by
    simpa only [K1_13.indexDegree, lowerIndex, suppQ] using hiQ
  have totalR : R'.totalDegree ≤ 380928000 := by
    have htR : R.totalDegree ≤ 380928000 := J.total
    simpa only [MvPolynomial.totalDegree, suppR] using htR
  have indexR : indexDegree R' ≤ 128800000 := by
    have hiR : lowerIndex R ≤ 128800000 := J.index
    simpa only [K1_13.indexDegree, lowerIndex, suppR] using hiR
  refine ⟨book, ⟨Q', R', neQ, neR, totalQ, indexQ, totalR, indexR⟩, hcard, ?_⟩
  intro γ hγ hb
  rcases hcover γ hγ hb with he | ho
  · exact Or.inl (eval_cleared mapQ _ he)
  · refine Or.inr (order_cleared mapR _ ?_)
    have hres : LowerOrder R (trajectory (extend (s γ))) 22533 :=
      resultant_order (pad D.left J.a) (pad D.right J.b) (inclConst (P.z γ)) _
        J.degree_left.le J.degree_right.le ⟨mixedOrder_pad J.a ho.1, mixedOrder_pad J.b ho.2⟩
    exact hres
end
end Low6966Fat
end

#print axioms Low6966Fat.fat_equations

namespace LowProfile6966
open K1_13 (extend)
open Low6966Fat (Holds)

/-- The actual low family supplies common and resultant equations with the
revised resultant order. -/
theorem fat_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179769 M Γ) (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2329) :
    ∃ (book : Finset P1.K) (E : Low6966Fat.FatEquations), book.card≤56000 ∧
      ∀ γ∈Γ,γ∉book → Holds E (extend (F.scalar γ)) := by
  obtain ⟨_,deg,hits⟩ := messages_of_family M F hi
  obtain ⟨pole,hpole⟩ := ModelExactPole6966.exists_pole M F lo (hi.trans (by decide))
  have small : pole.H.natDegree≤2329 := by rw [hpole]; omega
  exact Low6966Fat.fat_equations M.word Γ F.scalar deg hits pole small

#print axioms fat_of_family
end LowProfile6966

end Merged_R6960Low6966Fat

end Merged_Fat6966Family

-- merged module Low6966Order
section Merged_Low6966Order

-- merged module R6960Low6966Profile
section Merged_R6960Low6966Profile

set_option Elab.async false

namespace LowProfile6966
open P3 (I K node)
open K1_13 (Row Shape InBox shape OrderAt extend)
open scoped Polynomial BigOperators

abbrev layerWidth : ℕ := agreement-physicalDegree+3
abbrev layerCount : ℕ := 1+primaryCutoff/layerWidth
abbrev TrueWeightLE {n : ℕ} (P : Row n) (T : ℕ) := PrimaryTaper.TrueWeightLE physicalDegree P T

structure Messages (w : I→K) (Γ : Finset K) (s : K→(Polynomial K)) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ∈Γ,(s γ).natDegree≤physicalDegree
  hits : ∀ γ∈Γ,∃ T : Finset I,agreement≤T.card ∧ ∀ i∈T,(s γ).eval (node i)=w i

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ⊆Γ) : Messages w Δ s :=
  ⟨h.distinct.mono hΔ,fun γ mem=>h.degree γ (hΔ mem),fun γ mem=>h.hits γ (hΔ mem)⟩

def ProperCut (f : Row 4) (Γ : Finset K) (s : K→(Polynomial K)) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬f∣Q) ∧ InBox (shape Q) PrimaryTaper.primaryBox ∧ TrueWeightLE Q primaryCutoff ∧
    Final50Price.ActiveFits Q 5164 ∧ ∀ γ∈Γ,OrderAt Q (extend (s γ)) l

def LayerBudget {n : ℕ} (a : Fin n→Shape) (l : Fin n→ℕ) : Prop :=
  need ≤ ∑ r∈Finset.range layerCount,
    Final50Price.remaining (∑ i,(r+1-l i)*(a i).b) (∑ i,(r+1-l i)*(a i).j)
end LowProfile6966

end Merged_R6960Low6966Profile

-- merged module R6960Low6966Order
section Merged_R6960Low6966Order
set_option Elab.async false
namespace Low6966Order
noncomputable section
open K1_13 (Geom Row shape InBox Contact)
open P3 (I K)
abbrev TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) := LowProfile6966.TrueWeightLE P D
abbrev physicalDegree := LowProfile6966.physicalDegree
abbrev agreement := LowProfile6966.agreement
abbrev primaryBox := PrimaryTaper.primaryBox
abbrev primaryCutoff := LowProfile6966.primaryCutoff
abbrev sourceRank := Wide50EulerPrimary.sourceRank agreement physicalDegree
abbrev layerWidth := LowProfile6966.layerWidth
abbrev layerNeed := LowProfile6966.need
abbrev Messages := LowProfile6966.Messages
abbrev ProperCut := LowProfile6966.ProperCut
abbrev LayerBudget := @LowProfile6966.LayerBudget
theorem sourceRank_eq : sourceRank = 931565911020602571 := by decide
theorem certified_layers : sourceRank / layerWidth + 1 = 20088974187454 := by decide
def PrimaryRank (w : I → K) : Prop :=
  ∃ e : Fin sourceRank → Row 4, LinearIndependent Geom e ∧
    ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE (e i) primaryCutoff ∧
      PrimaryTaper.JetsBounded (e i) ∧ Contact w (e i)
end
end Low6966Order
section
namespace Low6966OrderProof
noncomputable section
open P3 (I K)
open Low6966Order (TrueWeightLE primaryBox primaryCutoff layerWidth)
open K1_13 (Row InBox shape Contact)
def requiredOrder (T : ℕ) : ℕ :=
  (primaryCutoff - T) / layerWidth + 1
def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧
    PrimaryTaper.JetsBounded P ∧ Contact w P
end
end Low6966OrderProof
end
section
namespace Low6966OrderProof
noncomputable section
open Polynomial
open P3 (I K node)
open Low6966Order (agreement)
open Low6966Order (Messages ProperCut TrueWeightLE physicalDegree primaryBox
  PrimaryRank primaryCutoff layerWidth layerNeed sourceRank)
open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open scoped BigOperators
open P0_9_3 (exists_fresh specialization_bounds sum_by_layer)
def c1 : Prop :=
  ∀ (w : I → K) (T : ℕ) (P : Row 4), T ≤ primaryCutoff → BankRow w T P →
    ∀ S : (Polynomial Geom), S.natDegree ≤ physicalDegree →
      (∃ H : Finset I, agreement ≤ H.card ∧
        ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) →
      OrderAt P S (requiredOrder T)
def c2 : Prop :=
  ∀ (f P : Row 4) (Γ : Finset K) (s : K → (Polynomial K)) (d a : ℕ),
    Irreducible f → 0 < (shape f).t → (shape f).t < K1.p →
    InBox (shape P) primaryBox → TrueWeightLE P primaryCutoff →
    Final50Price.ActiveFits P 5164 →
    (∀ γ ∈ Γ, OrderAt P (extend (s γ)) d) →
    a < d → f ^ a ∣ P → (¬ f ^ (a + 1) ∣ P) →
    ProperCut f Γ s (d - a)
def c3 : Prop :=
  ∀ (w : I → K) (x : Geom), PrimaryRank w →
    (∀ i : I, x ≠ embed (node i)) →
    ∃ r : ℕ → ℕ, sourceRank ≤ ∑ T ∈ Finset.range (primaryCutoff + 1), r T ∧
      ∀ T ≤ primaryCutoff, ∃ e : Fin (r T) → Row 4,
        (∀ i, BankRow w T (e i)) ∧
        LinearIndependent Geom (fun i => symbolAt x (e i))
private theorem exists_availability (hc : c1) (hd : c2)
    {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} (hm : Messages w Γ s)
    {f : Row 4} (hirr : Irreducible f) (hpos : 0 < (shape f).t) (htop : (shape f).t < K1.p) :
    ∃ l : ℕ, (∀ T ≤ primaryCutoff, ∀ P, BankRow w T P → f ^ (requiredOrder T - l) ∣ P) ∧
      (0 < l → ProperCut f Γ s l) := by
  classical
  let admissible (l : ℕ) : Prop :=
    ∀ T ≤ primaryCutoff, ∀ P, BankRow w T P → f ^ (requiredOrder T - l) ∣ P
  have hex : ∃ l, admissible l := by
    refine ⟨primaryCutoff / layerWidth + 1, fun T _ P _ => ?_⟩
    have hle : requiredOrder T ≤ primaryCutoff / layerWidth + 1 :=
      Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le _ _)) _
    rw [Nat.sub_eq_zero_of_le hle, pow_zero]
    exact one_dvd P
  let l := Nat.find hex
  have hl : admissible l := Nat.find_spec hex
  refine ⟨l, hl, fun hlpos => ?_⟩
  have hbad : ¬ admissible (l - 1) := Nat.find_min hex (by omega)
  dsimp only [admissible] at hbad
  push Not at hbad
  obtain ⟨T, hT, P, hP, hnext⟩ := hbad
  have hle : l ≤ requiredOrder T := by
    by_contra! hlt
    have heq : requiredOrder T - (l - 1) = 0 := by omega
    exact hnext (by rw [heq, pow_zero]; exact one_dvd P)
  have hstep : requiredOrder T - (l - 1) = (requiredOrder T - l) + 1 := by omega
  have horder : ∀ γ ∈ Γ, OrderAt P (extend (s γ)) (requiredOrder T) := by
    intro γ hγ
    apply hc w T P hT hP
    · simpa only [extend, natDegree_map_eq_of_injective (RingHom.injective embed)] using
        hm.degree γ hγ
    · obtain ⟨H, hcard, hH⟩ := hm.hits γ hγ
      refine ⟨H, hcard, fun i hi => ?_⟩
      rw [extend, eval_map, eval₂_at_apply, hH i hi]
  have hweight : TrueWeightLE P primaryCutoff := fun m hm => (hP.2.1 m hm).trans hT
  have hactive : Final50Price.ActiveFits P 5164 :=
    fun m hm => (PrimaryTaperActive.of_jets hP.2.2.1 m hm).trans (by decide)
  have hcut := hd f P Γ s (requiredOrder T) (requiredOrder T - l) hirr hpos htop hP.1
    hweight hactive horder (by omega) (hl T hT P hP) (by rwa [hstep] at hnext)
  have heq : requiredOrder T - (requiredOrder T - l) = l := by omega
  rwa [heq] at hcut
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3)
    {w Γ s n} {f : Fin n → Row 4} (hm : Messages w Γ s) (hr : PrimaryRank w)
    (hirr : ∀ i, Irreducible (f i)) (hpos : ∀ i, 0 < (shape (f i)).t)
    (htop : ∀ i, (shape (f i)).t < K1.p)
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) :
    ∃ l : Fin n → ℕ, Low6966Order.LayerBudget (fun i => shape (f i)) l ∧
      ∀ i, 0 < l i → ProperCut (f i) Γ s (l i) := by
  classical
  choose l hl hcut using fun i => exists_availability h1 h2 hm (hirr i) (hpos i) (htop i)
  obtain ⟨x, hx, hsup⟩ := exists_fresh f
  obtain ⟨r, hrank, hfamilies⟩ := h3 w x hr hx
  have hnz : ∀ i, symbolAt x (f i) ≠ 0 := by
    intro i hz
    have hzero := hsup i
    rw [hz, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at hzero
    exact (hirr i).ne_zero hzero
  let cost (k : ℕ) :=
    Final50Price.remaining (∑ i, (k + 1 - l i) * (shape (f i)).b)
      (∑ i, (k + 1 - l i) * (shape (f i)).j)
  have hcost : ∀ T ≤ primaryCutoff, r T ≤ cost ((primaryCutoff - T) / layerWidth) := by
    intro T hT
    obtain ⟨e, he, hei⟩ := hfamilies T hT
    let a (i : Fin n) := requiredOrder T - l i
    have hdiv (i : Fin (r T)) : (∏ j, f j ^ a j) ∣ e i := by
      apply Fintype.prod_dvd_of_isRelPrime
      · intro j k hjk
        have hj := hirr j
        have hk := hirr k
        exact (hj.isRelPrime_iff_not_dvd.mpr
          (fun h => hdiff j k hjk (hj.associated_of_dvd hk h))).pow
      · intro j
        exact hl j T hT (e i) (he i)
    have hbound := cofactor_rank n (fun i => symbolAt x (f i)) a hnz (r T)
      (fun i => symbolAt x (e i)) hei (fun i => by
        obtain ⟨hb, hj⟩ := specialization_bounds x (e i) (he i).1
        exact ⟨hb, hj, by simpa only [map_prod, map_pow] using map_dvd (symbolAt x) (hdiv i)⟩)
    have hb (i : Fin n) : (symbolAt x (f i)).totalDegree = (shape (f i)).b := by
      change (symbolAt x (f i)).totalDegree = (f i).totalDegree
      unfold MvPolynomial.totalDegree
      rw [hsup]
    have hj (i : Fin n) : symbolIndex (symbolAt x (f i)) = (shape (f i)).j := by
      change symbolIndex (symbolAt x (f i)) = indexDegree (f i)
      unfold symbolIndex indexDegree
      rw [hsup]
    have hs : r T ≤ Final50Price.symbolCount :=
      PrimaryTaper.symbol_rank x e (fun i => (he i).2.2.1) hei
    dsimp only [cost, Final50Price.remaining]
    apply le_min hs
    simpa only [a, requiredOrder, hb, hj] using hbound
  have hsum : sourceRank ≤ layerWidth * ∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k :=
    hrank.trans ((Finset.sum_le_sum fun T hT =>
      hcost T (Nat.le_of_lt_succ (Finset.mem_range.mp hT))).trans (sum_by_layer primaryCutoff layerWidth (by decide) cost))
  refine ⟨l, ?_, hcut⟩
  change layerNeed ≤ ∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k
  have hceil : layerWidth * (layerNeed - 1) < sourceRank := by decide
  by_contra! hsmall
  have hpred : (∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k) ≤
      layerNeed - 1 := by omega
  exact (not_le_of_gt hceil) (hsum.trans (Nat.mul_le_mul_left layerWidth hpred))
end
end Low6966OrderProof
end
section
set_option maxRecDepth 12000
namespace Low6966OrderProof_1
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P3 (I K node)
open Low6966Order (agreement)
open Low6966Order (TrueWeightLE physicalDegree primaryCutoff layerWidth)
open Low6966OrderProof (BankRow requiredOrder)
open K1_13 (Geom embed Row jet Contact)
open K1_13_3_1 (line)
open scoped BigOperators
open K1_13_3_1 (eval_line line_contacts_zero)
open K1_13_3_1 (order_of_locator_lines)
private def Bounded (Q : Polynomial (Polynomial Geom)) (b : ℕ) : Prop :=
  ∀ j, (Q.coeff j).natDegree ≤ b + layerWidth * j
private theorem bounded_mul {F G : Polynomial (Polynomial Geom)} {a b : ℕ}
    (hF : Bounded F a) (hG : Bounded G b) : Bounded (F * G) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega
private theorem bounded_C (f : (Polynomial Geom)) {a : ℕ} (hf : f.natDegree ≤ a) :
    Bounded (Polynomial.C f) a := by
  intro j
  by_cases h : j = 0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C, h]
private theorem bounded_prod {ι : Type*} (A : Finset ι)
    (f : ι → Polynomial (Polynomial Geom)) (b : ι → ℕ) (hf : ∀ i ∈ A, Bounded (f i) (b i)) :
    Bounded (∏ i ∈ A, f i) (∑ i ∈ A, b i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bounded_C (1 : (Polynomial Geom)) (a := 0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
private theorem bounded_pow {f : Polynomial (Polynomial Geom)} {b : ℕ} (hf : Bounded f b) (n : ℕ) :
    Bounded (f ^ n) (b * n) := by
  induction n with
  | zero => simpa using bounded_C (1 : (Polynomial Geom)) (a := 0) (by simp)
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact bounded_mul ih hf
private theorem line_degree (P : Row 4) (S U : (Polynomial Geom)) (T : ℕ)
    (hP : TrueWeightLE P T) (hS : S.natDegree ≤ physicalDegree)
    (hU : U.natDegree ≤ agreement + 3) (j : ℕ) :
    ((line P S U).coeff j).natDegree ≤ T + layerWidth * j := by
  let b (i : Fin 4) : ℕ := physicalDegree - i.val
  let F (i : Fin 4) : Polynomial (Polynomial Geom) :=
    Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 4) : Bounded (F i) (b i) := by
    intro k
    have hs : (jet S i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le S i.val).trans (Nat.sub_le_sub_right hS _)
    have hu : (jet U i).natDegree ≤ b i + layerWidth := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi : i.val ≤ physicalDegree := (Nat.le_of_lt_succ i.isLt).trans (by decide)
      have hwidth : agreement + 3 = layerWidth + physicalDegree := by decide
      change agreement + 3 - i.val ≤ (physicalDegree - i.val) + layerWidth
      rw [hwidth, Nat.add_sub_assoc hi, Nat.add_comm layerWidth]
    change ((Polynomial.C (jet S i) + Polynomial.C (jet U i) *
      Polynomial.X).coeff k).natDegree ≤ b i + layerWidth * k
    rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
    by_cases h0 : k = 0
    · simpa [h0] using hs
    · by_cases h1 : k = 1
      · simpa [h1] using hu
      · simp [h0, h1]
  unfold line
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have hterm := bounded_mul (bounded_C (P.coeff m) le_rfl)
    (bounded_prod m.support (fun i => F i ^ m i) (fun i => b i * m i)
      (fun i _ => bounded_pow (hF i) (m i))) j
  exact hterm.trans (Nat.add_le_add_right (hP m hm) _)
private theorem line_coeff_zero (w : I → K) (T : ℕ) (P : Row 4) (S : (Polynomial Geom))
    (hw : TrueWeightLE P T) (hc : Contact w P) (hS : S.natDegree ≤ physicalDegree)
    (A : Finset I) (hA : A.card = agreement)
    (hhit : ∀ i ∈ A, S.eval (embed (node i)) = embed (w i))
    (V : (Polynomial Geom)) (hV : V.natDegree ≤ 3) (j : ℕ)
    (hj : T + layerWidth * j ≤ primaryCutoff) :
    (line P S (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ agreement + 3 := by
    exact natDegree_mul_le.trans (by rw [locator_natDegree, hA]; exact Nat.add_le_add_left hV _)
  let Q := line P S U
  have hcontact (i : I) (hi : i ∈ A) (c : Geom) :
      (Polynomial.X - C (x i)) ^ 3000 ∣ Q.eval (C c) := by
    rw [show Q = line P S U from rfl, eval_line]
    apply hc
    have hL : L.eval (x i) = 0 := locator_eval_zero x A i hi
    have hU0 : U.eval (x i) = 0 := by simp [U, hL]
    simpa [x, eval_smul, hU0] using hhit i hi
  have hx : Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  have hb := (line_degree P S U T hw hS hU j).trans hj
  have hdegree : (Q.coeff j).natDegree < 3000 * A.card := by
    rw [hA]
    exact hb.trans_lt (Nat.sub_lt (Nat.mul_pos (by decide) (by decide)) (by decide))
  exact line_contacts_zero Q A x hx 3000 hcontact j hdegree
theorem order_of_contact (w : I → K) (P : Row 4) {T : ℕ} (hT : T ≤ primaryCutoff)
    (hw : TrueWeightLE P T) (hc : Contact w P) {S : (Polynomial Geom)} (hS : S.natDegree ≤ physicalDegree)
    {H : Finset I} (hH : agreement ≤ H.card)
    (hits : ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) :
    K1_13.OrderAt P S (requiredOrder T) := by
  obtain ⟨A, hAH, hA⟩ := Finset.exists_subset_card_eq hH
  let x (i : I) := embed (node i)
  apply order_of_locator_lines P S (locator x A) (locator_monic x A).ne_zero
  intro V hV j hj
  apply line_coeff_zero w T P S hw hc hS A hA (fun i hi => hits i (hAH hi)) V hV j
  have hj' : j ≤ (primaryCutoff - T) / layerWidth := Nat.lt_succ_iff.mp hj
  have hq := Nat.div_mul_le_self (primaryCutoff - T) layerWidth
  rw [Nat.mul_comm _ layerWidth] at hq
  calc
    T + layerWidth * j ≤ T + layerWidth * ((primaryCutoff - T) / layerWidth) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left layerWidth hj') T
    _ ≤ T + (primaryCutoff - T) := Nat.add_le_add_left hq T
    _ = primaryCutoff := Nat.add_sub_of_le hT
theorem proof : Low6966OrderProof.c1 := by
  intro w T P hT hP S hS hits
  obtain ⟨H, hH, hhits⟩ := hits
  exact order_of_contact w P hT hP.2.1 hP.2.2.2 hS hH hhits
end
end Low6966OrderProof_1
end
section
namespace Low6966OrderProof_2
noncomputable section
open Polynomial
open Low6966Order (TrueWeightLE physicalDegree primaryBox primaryCutoff)
open K1_13 (Geom embed extend Row Shape shape InBox indexDegree)
open P0_9_3_2 (translateTop topHasse topHasse_coeff source_support sum_add_top total_add_top apply_add_top erase_top_add topHasse_order topHasse_zero exact_hasse_not_dvd)
private theorem topHasse_bounds (box : Shape) (T a : ℕ) (P : Row 4)
    (hb : InBox (shape P) box) (hw : TrueWeightLE P T) :
    InBox (shape (topHasse a P)) box ∧ TrueWeightLE (topHasse a P) T := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change (topHasse a P).totalDegree ≤ box.b
    apply Finset.sup_le
    intro m hm
    have hp := (MvPolynomial.le_totalDegree (source_support hm)).trans hb.1
    rw [total_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change indexDegree (topHasse a P) ≤ box.j
    apply Finset.sup_le
    intro m hm
    have hp := (Finset.le_sup (f := fun u : Fin 4 →₀ ℕ => u.sum (fun i k => i.val * k))
      (source_support hm)).trans hb.2.1
    rw [sum_add_top Fin.val] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change (topHasse a P).degreeOf 3 ≤ box.t
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have hp := (MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)).trans hb.2.2
    rw [apply_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · intro m hm
    have hp := hw _ (source_support hm)
    rw [sum_add_top (fun i => physicalDegree - i.val)] at hp
    rw [topHasse_coeff]
    have hc := Polynomial.natDegree_mul_le
      (p := (↑((m 3 + a).choose a) : (Polynomial Geom))) (q := P.coeff (m + Finsupp.single 3 a))
    rw [Polynomial.natDegree_natCast, zero_add] at hc
    exact (Nat.add_le_add_right hc _).trans ((Nat.add_le_add_left (Nat.le_add_right _ _) _).trans hp)
private theorem topHasse_one_not_dvd (f : Row 4) (hf : Irreducible f)
    (hpos : 0 < f.degreeOf 3) (hsmall : f.degreeOf 3 < K1.p) : ¬ f ∣ topHasse 1 f := by
  classical
  have hdeg : (topHasse 1 f).degreeOf 3 ≤ f.degreeOf 3 - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have h := MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)
    rw [apply_add_top] at h
    omega
  have hnz : topHasse 1 f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m (3 : Fin 4)) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    rw [← MvPolynomial.degreeOf_eq_sup] at htop
    have hupos : 0 < u 3 := hpos.trans_le htop
    have hult : u 3 < K1.p := (MvPolynomial.le_degreeOf_of_mem_support 3 hu).trans_lt hsmall
    let m := u.erase 3 + Finsupp.single 3 (u 3 - 1)
    have hsum : m + Finsupp.single 3 1 = u := by
      dsimp [m]
      rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel hupos, erase_top_add]
    have hm : m 3 + 1 = u 3 := by
      rw [← apply_add_top, hsum]
    have hc : (↑(u 3) : (Polynomial Geom)) ≠ 0 := by
      have : CharP Geom K1.p :=
        charP_of_injective_ringHom (RingHom.injective embed) K1.p
      intro hz
      have hz' : (↑(u 3) : Geom) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg (Polynomial.evalRingHom (0 : Geom)) hz
      exact (not_le_of_gt hult)
        (Nat.le_of_dvd hupos ((CharP.cast_eq_zero_iff Geom K1.p _).mp hz'))
    have hcoeff : (topHasse 1 f).coeff m ≠ 0 := by
      rw [topHasse_coeff, hm, hsum, Nat.choose_one_right]
      exact mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hu)
    intro hz
    exact hcoeff (by rw [hz]; rfl)
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    exact hnz (by rw [hg, h, mul_zero])
  have h := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.ne_zero hg0
  rw [hg, h] at hdeg
  omega
theorem proof : Low6966OrderProof.c2 := by
  intro f P Γ s d a hirr hpos htop hb hw ha hord _ hdiv hexact
  obtain ⟨hbox, hweight⟩ := topHasse_bounds primaryBox primaryCutoff a P hb hw
  have hp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hproper : ¬ f ∣ topHasse a P :=
    exact_hasse_not_dvd translateTop topHasse_zero f P a hp
      (topHasse_one_not_dvd f hirr hpos htop) hdiv hexact
  have hactive : Final50Price.ActiveFits (topHasse a P) 5164 := by
    intro m hm
    have hh := ha _ (source_support hm)
    simp [Finsupp.add_apply] at hh
    omega
  exact ⟨topHasse a P, hproper, hbox, hweight, hactive, fun γ hγ =>
    topHasse_order a d P (extend (s γ)) (hord γ hγ)⟩
end
end Low6966OrderProof_2
end
section
namespace Low6966OrderProof_3
noncomputable section
open Polynomial
open P3 (I K node)
open Low6966Order (TrueWeightLE physicalDegree primaryCutoff)
open Low6966OrderProof (BankRow)
open K1_13 (Geom embed Row InBox shape indexDegree Contact atJet)
open K1_13_3 (Symbol symbolAt)
open P0_9_3 (jetEval jetEval_apply dvd_smul_poly coefficientArray symbolLinear linearFactor linearFactor_ne linearFactor_degree divide_specialization support_linear_mul)
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent := Fin 4 →₀ ℕ
private def jetWeight (m : Exponent) : ℕ :=
  m.sum (fun i a => (physicalDegree - i.val) * a)
private theorem bankRow_iff {w : I → K} {T : ℕ} {P : Row 4} :
    BankRow w T P ↔
      (∀ m ∈ P.support, m.sum (fun _ a => a) ≤ 4012 ∧
        m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
        (P.coeff m).natDegree + jetWeight m ≤ T ∧ m ∈ TaperColumns.jetExponents) ∧ Contact w P := by
  simp only [BankRow, InBox, shape, indexDegree, MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff, Finset.sup_le_iff, TrueWeightLE, PrimaryTaper.JetsBounded]
  constructor
  · rintro ⟨⟨hb, hj, ht⟩, hT, hs, hc⟩
    exact ⟨fun m hm => ⟨hb m hm, hj m hm, ht m hm, hT m hm, hs m hm⟩, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2.1, fun m hm => (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2.1, fun m hm => (h m hm).2.2.2.2, hc⟩
private def bank (w : I → K) (T : ℕ) : Submodule Geom (Row 4) where
  carrier := {P | BankRow w T P}
  zero_mem' := by
    apply bankRow_iff.mpr
    simp [Contact, atJet]
  add_mem' {P Q} hP hQ := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    obtain ⟨hQ, hq⟩ := bankRow_iff.mp hQ
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      have hor := Finset.mem_union.mp (MvPolynomial.support_add hm)
      have bounds :
          m.sum (fun _ a => a) ≤ 4012 ∧ m.sum (fun i a => i.val * a) ≤ 1650 ∧
            m 3 ≤ 550 ∧ jetWeight m ≤ T ∧ m ∈ TaperColumns.jetExponents := by
        rcases hor with h | h
        · obtain ⟨hb, hj, ht, hw, hjets⟩ := hP m h
          exact ⟨hb, hj, ht, by omega, hjets⟩
        · obtain ⟨hb, hj, ht, hw, hjets⟩ := hQ m h
          exact ⟨hb, hj, ht, by omega, hjets⟩
      obtain ⟨hb, hj, ht, hw, hjets⟩ := bounds
      refine ⟨hb, hj, ht, ?_, hjets⟩
      have hsum : ((P + Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m) + (Q.coeff m)).natDegree ≤ _
        exact natDegree_add_le _ _
      have hdegree (R : Row 4) (hR : m ∈ R.support → (R.coeff m).natDegree + jetWeight m ≤ T) :
          (R.coeff m).natDegree ≤ T - jetWeight m := by
        by_cases h : m ∈ R.support
        · have := hR h
          omega
        · have hz : R.coeff m = 0 := by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz, natDegree_zero]
          exact Nat.zero_le _
      have hp' := hdegree P (fun h => (hP m h).2.2.2.1)
      have hq' := hdegree Q (fun h => (hQ m h).2.2.2.1)
      have := hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← jetEval_apply, map_add, jetEval_apply, jetEval_apply]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      obtain ⟨hb, hj, ht, hw, hjets⟩ := hP m (MvPolynomial.support_smul hm)
      refine ⟨hb, hj, ht, ?_, hjets⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h : jetEval S (c • P) = c • jetEval S P := (jetEval S).map_smul c P
      rw [jetEval_apply, jetEval_apply] at h
      rw [h]
      exact dvd_smul_poly _ _ c (hp i S hS)
private instance finiteBank (w : I → K) (T : ℕ) : Module.Finite Geom (bank w T) := by
  classical
  let f : bank w T →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
    (coefficientArray T).comp (bank w T).subtype
  have hzero (Q : bank w T) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨P, hP⟩ := Q
    change BankRow w T P at hP
    apply Subtype.ext
    change P = 0
    apply MvPolynomial.ext
    intro m
    change _ = 0
    by_contra hnz
    have hm := MvPolynomial.mem_support_iff.mpr hnz
    have hT : (P.coeff m).natDegree ≤ T := (Nat.le_add_right _ _).trans (hP.2.1 m hm)
    let u : Fin 4 → Fin 4013 := fun i => ⟨m i, Nat.lt_succ_of_le <|
      (MvPolynomial.le_degreeOf_of_mem_support i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < T + 1
    · have hval := congrFun hQ (u, ⟨k, hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i => (u i).val))).coeff k = 0 at hval
      have heq : Finsupp.equivFunOnFinite.symm (fun i => (u i).val) = m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz := f.map_sub P Q
  rw [h, sub_self] at hz
  exact hzero (P - Q) hz
private def bankEval (w : I → K) (x : Geom) (T : ℕ) : bank w T →ₗ[Geom] Symbol :=
  (symbolLinear x).comp (bank w T).subtype
private theorem mul_cutoff_iff (w : I → K) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) (P : Row 4) :
    BankRow w (T + 1) (MvPolynomial.C (linearFactor x) * P) ↔ BankRow w T P := by
  rw [bankRow_iff, bankRow_iff, support_linear_mul]
  apply and_congr
  · refine forall_congr' fun m => forall_congr' fun hm => ?_
    rw [MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x)
      (MvPolynomial.mem_support_iff.mp hm), linearFactor_degree]
    constructor <;> rintro ⟨hb, hj, ht, hw, hJets⟩ <;>
      exact ⟨hb, hj, ht, by omega, hJets⟩
  · simp only [Contact, atJet, map_mul, MvPolynomial.eval_C]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro S
    apply forall_congr'
    intro hS
    generalize (3000 : ℕ) = m
    have hc : IsCoprime (linearFactor (embed (node i))) (linearFactor x) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hx i).symm).isUnit
    have hd : IsCoprime (linearFactor (embed (node i)) ^ m) (linearFactor x) := hc.pow_left
    exact hd.dvd_mul_left_iff
private theorem zero_cutoff_kernel (w : I → K) (x : Geom) :
    LinearMap.ker (bankEval w x 0) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro P hP
  change symbolAt x P.val = 0 at hP
  obtain ⟨Q, hQ⟩ := divide_specialization P.val x hP
  have hp : TrueWeightLE P.val 0 := P.property.2.1
  apply Subtype.ext
  change P.val = 0
  rw [← hQ]
  suffices Q = 0 by simp [this]
  apply MvPolynomial.ext
  intro m
  change _ = 0
  by_contra hnz
  have hm : m ∈ P.val.support := by
    rw [← hQ, support_linear_mul]
    exact MvPolynomial.mem_support_iff.mpr hnz
  have h := hp m hm
  rw [← hQ, MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x) hnz,
    linearFactor_degree] at h
  omega
private theorem kernel_finrank (w : I → K) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) : Module.finrank Geom (LinearMap.ker (bankEval w x (T + 1))) =
      Module.finrank Geom (bank w T) := by
  let L : bank w T →ₗ[Geom] (LinearMap.ker (bankEval w x (T + 1))) :=
    LinearMap.codRestrict _ (LinearMap.codRestrict (bank w (T + 1))
      ((LinearMap.mulLeft Geom (MvPolynomial.C (linearFactor x))).comp (bank w T).subtype)
      (fun P => (mul_cutoff_iff w x hx T P.val).mpr P.property)) (fun P => by
        rw [LinearMap.mem_ker]
        simp only [bankEval, LinearMap.comp_apply, Submodule.subtype_apply,
          LinearMap.codRestrict_apply, LinearMap.mulLeft_apply]
        change symbolAt x (MvPolynomial.C (linearFactor x) * P.val) = 0
        have h0 : symbolAt x (MvPolynomial.C (linearFactor x)) = 0 := by
          simp only [symbolAt, linearFactor, MvPolynomial.map_C, Polynomial.coe_evalRingHom,
            Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, map_zero]
        rw [RingHom.map_mul, h0, zero_mul])
  have hL : Function.Bijective L := by
    have hnz : (MvPolynomial.C (linearFactor x) : Row 4) ≠ 0 := by
      simpa only [ne_eq, MvPolynomial.C_eq_zero] using linearFactor_ne x
    constructor
    · intro P Q h
      apply Subtype.ext
      have heq := congrArg (fun V : LinearMap.ker (bankEval w x (T + 1)) => V.val.val) h
      change MvPolynomial.C (linearFactor x) * P.val = MvPolynomial.C (linearFactor x) * Q.val at heq
      exact mul_left_cancel₀ hnz heq
    · intro P
      have h : symbolAt x P.val.val = 0 := LinearMap.mem_ker.mp P.property
      obtain ⟨Q, hQ⟩ := divide_specialization P.val.val x h
      have hmem : BankRow w (T + 1) (MvPolynomial.C (linearFactor x) * Q) := by
        rw [hQ]
        exact P.val.property
      refine ⟨⟨Q, (mul_cutoff_iff w x hx T Q).mp hmem⟩, Subtype.ext (Subtype.ext hQ)⟩
  exact (LinearEquiv.ofBijective L hL).finrank_eq.symm
theorem proof : Low6966OrderProof.c3 := by
  classical
  intro w x hr hx
  let r (T : ℕ) := Module.finrank Geom (LinearMap.range (bankEval w x T))
  refine ⟨r, ?_, fun T _ => ?_⟩
  · have heq (T : ℕ) : Module.finrank Geom (bank w T) =
        ∑ V ∈ Finset.range (T + 1), r V := by
      induction T with
      | zero =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w 0) (V₂ := Symbol) (bankEval w x 0)
        rw [zero_cutoff_kernel, finrank_bot, Nat.add_zero] at h
        simpa only [Nat.zero_add, Finset.sum_range_one] using h.symm
      | succ T ih =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w (T + 1)) (V₂ := Symbol) (bankEval w x (T + 1))
        rw [kernel_finrank w x hx, ih, Nat.add_comm] at h
        rw [Finset.sum_range_succ]
        exact h.symm
    obtain ⟨e, he, hmem⟩ := hr
    have hi : LinearIndependent Geom (fun i => (⟨e i, hmem i⟩ : bank w primaryCutoff)) :=
      LinearIndependent.of_comp (bank w primaryCutoff).subtype he
    rw [← heq]
    simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank
  · let b := Module.finBasis Geom (LinearMap.range (bankEval w x T))
    choose e he using fun i : Fin (r T) => LinearMap.mem_range.mp (b i).property
    refine ⟨fun i => (e i).val, fun i => (e i).property, ?_⟩
    have h : LinearIndependent Geom (fun i => (b i).val) :=
      b.linearIndependent.map' (LinearMap.range (bankEval w x T)).subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i => symbolAt x (e i).val) = fun i => (b i).val := funext he
    rwa [heq]
end
end Low6966OrderProof_3
end
namespace Low6966Order
noncomputable section
open K1_13 (Row shape)
open P3 (K)
open scoped Polynomial
export Low6966OrderProof (BankRow requiredOrder)
export Low6966OrderProof_1 (order_of_contact)
theorem messages_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt agreement M Γ) (hh : M.overhead ≤ 2329) :
    Messages M.word Γ F.scalar := by
  refine ⟨F.distinct, ?_, ?_⟩
  · intro γ hγ
    obtain hz | hd := (F.mark γ hγ).scalar_degree
    · simp [hz]
    · change ((F.scalar γ).natDegree : ℤ) ≤ (131072 : ℤ) - 1 + M.overhead at hd
      change (F.scalar γ).natDegree ≤ 133400
      omega
  · intro γ hγ
    let m := F.mark γ hγ
    exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩
theorem proper_layers_of_rank {w Γ s n} {f : Fin n → Row 4}
    (hm : Messages w Γ s) (hr : PrimaryRank w)
    (hirr : ∀ i, Irreducible (f i)) (hpos : ∀ i, 0 < (shape (f i)).t)
    (htop : ∀ i, (shape (f i)).t < K1.p)
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) :
    ∃ l : Fin n → ℕ, LayerBudget (fun i => shape (f i)) l ∧
      ∀ i, 0 < l i → ProperCut (f i) Γ s (l i) :=
  Low6966OrderProof.of_children Low6966OrderProof_1.proof
    Low6966OrderProof_2.proof Low6966OrderProof_3.proof
    hm hr hirr hpos htop hdiff
theorem primary_rank (w : P3.I → K) : PrimaryRank w :=
  Wide50EulerPrimary.primary_family agreement physicalDegree (by decide) (by decide)
    (by decide) w (n := sourceRank) le_rfl
theorem symbol_families : Low6966OrderProof.c3 := Low6966OrderProof_3.proof
theorem proper_layers {w Γ s n} {f : Fin n → Row 4}
    (hm : Messages w Γ s)
    (hirr : ∀ i, Irreducible (f i)) (hpos : ∀ i, 0 < (shape (f i)).t)
    (htop : ∀ i, (shape (f i)).t < K1.p)
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) :
    ∃ l : Fin n → ℕ, LayerBudget (fun i => shape (f i)) l ∧
      ∀ i, 0 < l i → ProperCut (f i) Γ s (l i) :=
  proper_layers_of_rank hm (primary_rank w) hirr hpos htop hdiff
end
end Low6966Order

end Merged_R6960Low6966Order

end Merged_Low6966Order
