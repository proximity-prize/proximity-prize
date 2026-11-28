import ProximityPrize.SubmissionLower.R6970Height2313Main

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Research6970.Height2313.Lower6960.Prefix6969Main

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL evaluated)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (ODECaps mass mass_mono)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open P1_7_4 (Mass massQ massQ_mono dotQ running weightedBill ODEGuard)
open _root_.Lower6960.Far6969RescueGeometry (Model Family word OnMark OnSurface)
open Research6970.Height2313.Lower6960.Prefix6969Rates (curveMarks mem_curveMarks)
open _root_.Lower6960 _root_.Research6969
open Research6966
open PrefixRows (Common)
open scoped Classical BigOperators

noncomputable section

namespace RankBill

inductive Certificate where
  | leaf
  | splitOrdinate (point : ℕ) (lower upper : Certificate)
  | splitMixed (point : ℕ) (lower upper : Certificate)

def capsAfter (s : Plan) (ordinate mixed i : ℕ) (k : Fin 4) : ℚ :=
  if k = 1 then min (s.history i k) (s.initialCap k - ordinate : ℕ)
  else if k = 2 then min (s.history i k) (s.initialCap k - mixed : ℕ)
  else s.history i k

def chargedWeight (s : Plan) (x : Pricing) (i : ℕ) (k : Fin 4) : ℚ :=
  if i + 1 = s.count then max (x.lossWeight s i k) (x.retainedCredit k)
  else x.lossWeight s i k

def cellLoss (s : Plan) (x : Pricing) (band : Band)
    (jmin jmax bmin bmax : ℕ) : ℕ :=
  ((band.fixedFee (bmax+2) (min (jmax+1) (bmax+2)) : ℚ) +
    weightedBill s.count (chargedWeight s x) (capsAfter s jmin bmin) + s.seedLimit).ceil.toNat

def fee (s : Plan) (band : Band) (lossCap : ℕ) : ℕ :=
  lossCap + s.pointLimit.ceil.toNat + s.initialSeedLimit + s.initialCap 0 +
    s.fixedLimit band + s.contentLimit

def checked (s : Plan) (x : Pricing) (band : Band) (lossCap : ℕ) :
    Certificate → ℕ → ℕ → ℕ → ℕ → Prop
  | .leaf, jl, ju, bl, bu => cellLoss s x band jl ju bl bu ≤ lossCap
  | .splitOrdinate mid low high, jl, ju, bl, bu =>
      (jl ≤ mid ∧ mid < ju) ∧ checked s x band lossCap low jl mid bl bu ∧
        checked s x band lossCap high (mid+1) ju bl bu
  | .splitMixed mid low high, jl, ju, bl, bu =>
      (bl ≤ mid ∧ mid < bu) ∧ checked s x band lossCap low jl ju bl mid ∧
        checked s x band lossCap high jl ju (mid+1) bu

def Sufficient (s : Plan) (x : Pricing) (band : Band) (cert : Certificate) (lossCap : ℕ) : Prop :=
  checked s x band lossCap cert 0 (s.initialCap 1) 0 (s.initialCap 2)

private theorem checked_cell {s : Plan} {x : Pricing} {band : Band} {lossCap : ℕ}
    (cert : Certificate) {j b jl ju bl bu : ℕ}
    (jLower : jl ≤ j) (jUpper : j ≤ ju) (bLower : bl ≤ b) (bUpper : b ≤ bu)
    (check : checked s x band lossCap cert jl ju bl bu) :
    ∃ p q r t : ℕ, p ≤ j ∧ j ≤ q ∧ r ≤ b ∧ b ≤ t ∧
      t ≤ bu ∧ cellLoss s x band p q r t ≤ lossCap := by
  induction cert generalizing jl ju bl bu with
  | leaf => exact ⟨jl,ju,bl,bu,jLower,jUpper,bLower,bUpper,le_rfl,check⟩
  | splitOrdinate mid left right ihLeft ihRight =>
    simp only [checked] at check
    by_cases h : j ≤ mid
    · exact ihLeft jLower h bLower bUpper check.2.1
    · exact ihRight (by omega) jUpper bLower bUpper check.2.2
  | splitMixed mid left right ihLeft ihRight =>
    simp only [checked] at check
    by_cases h : b ≤ mid
    · obtain ⟨p,q,r,t,a,d,c,e,f,g⟩ := ihLeft jLower jUpper bLower h check.2.1
      exact ⟨p,q,r,t,a,d,c,e,f.trans check.1.2.le,g⟩
    · exact ihRight jLower jUpper (by omega) bUpper check.2.2

private theorem round_card {a : ℕ} {q : ℚ} (bound : (a : ℚ) ≤ q) : a ≤ q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)

end RankBill

variable {s : Plan} {band : Band} {price : Pricing}
variable {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows s F Crt}
variable (ini : Initial R)

private theorem rank_mass_fit (k : Fin 4) :
    mass ini.rankExit k + mass ini.parents k ≤ s.initialCap k := by
  have h : mass (ini.rankExit ∪ ini.parents) k = mass ini.rankExit k + mass ini.parents k :=
    sum_union ini.disjoint
  rw [← h]
  exact ini.fits k

private theorem rank_fee_in_cell (checked : price.Valid s band) (hi : M.overhead.toNat ≤ band.last)
    {jmax bmax : ℕ} (ord : mass ini.rankExit 1 ≤ jmax) (mixed : mass ini.rankExit 2 ≤ bmax)
    (size : bmax ≤ s.initialCap 2) :
    ini.rankMarks.card ≤ band.fixedFee (bmax+2) (min (jmax+1) (bmax+2)) := by
  let B := bmax+2
  let J := min (jmax+1) B
  obtain ⟨E,caps,roots⟩ := ini.rank_ode
  have limit : ∀ j i, (E.coeff j).coeff i ≠ 0 → i+j ≤ B :=
    fun j i h => (caps.2.2 j i h).trans (by change mass ini.rankExit 2 ≤ bmax+2; omega)
  have degree : E.natDegree ≤ B := by
    have head : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr head
    exact (Nat.le_add_left _ _).trans (limit _ _ hn)
  have ocaps : ODECaps E B J :=
    ⟨caps.1, le_min (caps.2.1.trans (by omega)) degree, limit⟩
  have guard : ODEGuard B J :=
    ⟨by dsimp [B]; omega, by dsimp [J,B]; omega, min_le_right _ _,
      (Nat.add_le_add_right size 2).trans_lt checked.rank_guard.1⟩
  exact band.fixed_count R.family hi guard E ocaps (filter_subset _ _)
    (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)

private theorem cap_after_rank {jl bl i : ℕ} (hi : i < s.count)
    (ord : jl ≤ mass ini.rankExit 1) (mixed : bl ≤ mass ini.rankExit 2) (k : Fin 4) :
    massQ (ini.live i) k ≤ RankBill.capsAfter s jl bl i k := by
  have subset : ini.live i ⊆ ini.parents := by
    rw [Initial.live, ite_eq_left hi]
    exact filter_subset _ _
  have main := ini.cap_live hi k
  have massCap (v : ℕ) (h : v ≤ mass ini.rankExit k) :
      massQ (ini.live i) k ≤ (s.initialCap k-v : ℕ) := by
    have q := rank_mass_fit ini k
    have m := mass_mono subset k
    change (mass (ini.live i) k : ℚ) ≤ _
    exact_mod_cast (show mass (ini.live i) k ≤ s.initialCap k-v by omega)
  unfold RankBill.capsAfter
  split
  · rename_i hk
    subst k
    exact le_min main (massCap jl ord)
  · split
    · rename_i hk
      subst k
      exact le_min main (massCap bl mixed)
    · exact main

private theorem retained_running (k : Fin 4) :
    (price.retainedCredit k : ℚ) ≤ running (RankBill.chargedWeight s price) s.count k := by
  have h : s.count - 1 + 1 = s.count := by change (s.last+1)-1+1=s.last+1; omega
  calc
    _ ≤ RankBill.chargedWeight s price (s.count-1) k := by
      rw [RankBill.chargedWeight, ite_eq_left h]
      exact le_max_right _ _
    _ ≤ _ := by rw [← h, running]; exact le_max_right _ _

theorem CutBooks.rank_cell_loss (C : CutBooks ini) (checked : price.Valid s band)
    (hi : M.overhead.toNat ≤ band.last)
    {jl ju bl bu lossCap : ℕ}
    (ordLo : jl ≤ mass ini.rankExit 1) (ordHi : mass ini.rankExit 1 ≤ ju)
    (mixLo : bl ≤ mass ini.rankExit 2) (mixHi : mass ini.rankExit 2 ≤ bu)
    (size : bu ≤ s.initialCap 2)
    (fee : RankBill.cellLoss s price band jl ju bl bu ≤ lossCap) :
    C.lossMarks.card + price.charge ini.final ≤ lossCap := by
  have rank := rank_fee_in_cell ini checked hi ordHi mixHi size
  have cum : (C.lossMarks.card : ℚ) ≤ (ini.rankMarks.card : ℚ) +
      ∑ i∈range s.count, ((curveMarks R.family (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ ini.rankMarks.card +
      ∑ i∈range s.count, (curveMarks R.family (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have cuts := sum_le_sum (fun i (mem : i∈range s.count) => by
    have raw := C.curve_bin_count checked hi (mem_range.mp mem)
    have mono : dotQ (price.lossWeight s i) (massQ (ini.lost i)) ≤
        dotQ (RankBill.chargedWeight s price i) (massQ (ini.lost i)) := by
      apply P1_7_4.dotQ_mono_weight (P1_7_4.massQ_nonneg _)
      intro k
      unfold RankBill.chargedWeight
      split
      · exact le_max_left _ _
      · exact le_rfl
    exact raw.trans (add_le_add mono le_rfl))
  rw [sum_add_distrib] at cuts
  have joint := P1_7_4.bill_bound_with_final s.count (RankBill.chargedWeight s price)
    (RankBill.capsAfter s jl bl) ini.live ini.lost (fun _ hi => ini.next_sub hi)
    (fun _ _ => subset_rfl) (fun _ hi k => cap_after_rank ini hi ordLo mixLo k)
  have final : ini.live s.count = ini.final := by simp [Initial.live]
  rw [final] at joint
  have credit : (price.charge ini.final : ℚ) ≤
      dotQ (running (RankBill.chargedWeight s price) s.count) (massQ ini.final) := by
    unfold Pricing.charge dotQ massQ
    push_cast
    exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (retained_running k) (Nat.cast_nonneg _)
  have seed := C.seed_bill
  have rankQ : (ini.rankMarks.card : ℚ) ≤ (band.fixedFee (bu+2) (min (ju+1) (bu+2)) : ℕ) := by
    exact_mod_cast rank
  apply le_trans _ fee
  unfold RankBill.cellLoss
  apply RankBill.round_card
  push_cast
  linarith only [cum,cuts,joint,credit,seed,rankQ]

theorem CutBooks.rank_bounded_loss (C : CutBooks ini) (checked : price.Valid s band)
    (hi : M.overhead.toNat ≤ band.last) {cert : RankBill.Certificate} {lossCap : ℕ}
    (fits : RankBill.Sufficient s price band cert lossCap) :
    C.lossMarks.card + price.charge ini.final ≤ lossCap := by
  have jUpper : mass ini.rankExit 1 ≤ s.initialCap 1 := by have h := rank_mass_fit ini 1; omega
  have bUpper : mass ini.rankExit 2 ≤ s.initialCap 2 := by have h := rank_mass_fit ini 2; omega
  obtain ⟨jl,ju,bl,bu,ordLo,ordHi,mixLo,mixHi,size,fee⟩ :=
    RankBill.checked_cell cert (Nat.zero_le _) jUpper (Nat.zero_le _) bUpper fits
  exact C.rank_cell_loss ini checked hi ordLo ordHi mixLo mixHi size fee

theorem CutBooks.paid_from_rank_loss (C : CutBooks ini)
    (hi : M.overhead.toNat ≤ band.last) {lossCap : ℕ}
    (loss : C.lossMarks.card + price.charge ini.final ≤ lossCap) :
    C.paid.card + price.charge ini.final ≤ RankBill.fee s band lossCap := by
  have combined := card_union_le
    ((C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks)) (R.fixedMarks ∪ ini.contentMarks)
  have left := card_union_le (C.lossMarks ∪ C.pointMarks) (ini.seedMarks ∪ ini.ordinateMarks)
  have cuts := card_union_le C.lossMarks C.pointMarks
  have low := card_union_le ini.seedMarks ini.ordinateMarks
  have fixed := card_union_le R.fixedMarks ini.contentMarks
  have points := RankBill.round_card C.point_bill
  have seeds : ini.seedMarks.card ≤ s.initialSeedLimit := ini.seed_count
  have ordinates : ini.ordinateMarks.card ≤ s.initialCap 0 := ini.ordinary_count
  have content : ini.contentMarks.card ≤ s.contentLimit := ini.content_count
  have fixedCard := R.fixed_count band hi
  unfold RankBill.fee CutBooks.paid
  omega


theorem CutBooks.rank_bounded_paid (C : CutBooks ini) (checked : price.Valid s band)
    (hi : M.overhead.toNat ≤ band.last) {cert : RankBill.Certificate} {lossCap : ℕ}
    (fits : RankBill.Sufficient s price band cert lossCap) :
    C.paid.card + price.charge ini.final ≤ RankBill.fee s band lossCap :=
  C.paid_from_rank_loss ini hi (C.rank_bounded_loss ini checked hi fits)

variable {sched : Plan} in
theorem Rows.main_prefix_with_rank_payment {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows sched F Crt)
    {lossCap : ℕ}
    (pay : ∀ (ini : Initial R) (C : CutBooks ini),
      C.paid.card + price.charge ini.final ≤ RankBill.fee sched band lossCap) (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (ini : Initial R) (C : CutBooks ini) (S : Finset Surface),
      C.paid.card + price.charge ini.final ≤ RankBill.fee sched band lossCap ∧
      (∀ k, massQ ini.final k ≤ sched.history sched.last k) ∧
      (∀ q∈S, Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S, ∃ J∈ini.final, q.asIdeal = J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks, γ∈C.paid ∨ ∃ q∈S, OnSurface F q γ := by
  obtain ⟨ini⟩ := R.initial_cover
  obtain ⟨C⟩ := ini.cutBooks noPole residues
  obtain ⟨S, geom, origin, surface⟩ := ini.terminal_surfaces_with_origins
  refine ⟨ini, C, S, pay ini C, ?_, geom, origin, ?_⟩
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


theorem main_prefix_with_rank_payment {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (sched : Plan) (valid : sched.Valid) (band : Band) (price : Pricing)
    {first extra a low floor : ℕ} {outer : P1_7.Bank}
    (source : sched.Sources first band.last outer extra a low floor)
    {lossCap : ℕ}
    (pay : ∀ (R : Rows sched F Crt) (ini : Initial R) (C : CutBooks ini),
      C.paid.card + price.charge ini.final ≤ RankBill.fee sched band lossCap)
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
      R.out.exception = G ∧ C.paid.card + price.charge ini.final ≤ RankBill.fee sched band lossCap ∧
      (∀ k, massQ ini.final k ≤ sched.history sched.last k) ∧
      (∀ q∈S, Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S, ∃ J∈ini.final, q.asIdeal = J.comap toJet) ∧
      ∀ γ∈R.marks, γ∈C.paid ∨ ∃ q∈S, OnSurface F q γ := by
  have safe : band.last ≤ 131070 := by cases band <;> decide
  obtain ⟨R, identity⟩ := rows F Crt sched valid source firstPos safe lo hi noPole residues phys known degree seed physical
  obtain ⟨ini, C, S, paid, massCap, regular, origins, covered⟩ :=
    R.main_prefix_with_rank_payment (band:=band) (price:=price) (pay R) noPole residues
  exact ⟨R, ini, C, S, identity, paid, massCap, regular, origins, covered⟩

theorem main_prefix_rank_bounded {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (sched : Plan) (valid : sched.Valid) (band : Band) (price : Pricing)
    (priced : price.Valid sched band)
    {first extra a low floor : ℕ} {outer : P1_7.Bank}
    (source : sched.Sources first band.last outer extra a low floor)
    {cert : RankBill.Certificate} {lossCap : ℕ}
    (bill : RankBill.Sufficient sched price band cert lossCap)
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
      R.out.exception = G ∧ C.paid.card + price.charge ini.final ≤ RankBill.fee sched band lossCap ∧
      (∀ k, massQ ini.final k ≤ sched.history sched.last k) ∧
      (∀ q∈S, Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S, ∃ J∈ini.final, q.asIdeal = J.comap toJet) ∧
      ∀ γ∈R.marks, γ∈C.paid ∨ ∃ q∈S, OnSurface F q γ :=
  main_prefix_with_rank_payment F Crt sched valid band price source
    (fun _ ini C => C.rank_bounded_paid ini priced hi bill)
    firstPos lo hi noPole residues phys known degree seed physical

end
end Research6970.Height2313.Lower6960.Prefix6969Main
