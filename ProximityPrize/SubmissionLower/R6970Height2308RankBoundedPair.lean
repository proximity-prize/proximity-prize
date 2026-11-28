import ProximityPrize.SubmissionLower.R6970PrimaryRankBill
import ProximityPrize.SubmissionLower.R6970TransferRescuePlan

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Research6970.Height2308

open _root_.Lower6960 _root_.Research6969

noncomputable section

open Finset Polynomial
open K1 (K)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated nodeL)
open K1_14_2 (UsesSeed toJet)
open K1_14_2_2 (Active RowCaps mass)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Parent)
open Research6970.Height2313.Lower6960
open _root_.Research6969.TransitionPacket (Pair)
open _root_.Lower6960.Far6969RescueGeometry (Model Family word OnSurface)
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)
open PrefixRows (Common)
open Research6966
open scoped Classical BigOperators

/-- The four price fields are matched against the public joint ledger, and
the actual rational history yields its integral seed and ordinate caps. -/
structure RankBoundedNormalBounds (main : Research6970.Height2313.Lower6960.Prefix6969Main.Plan) (mp : Research6970.Height2313.Lower6960.Prefix6969Main.Pricing)
    (rescue : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan) (rp : Research6970.Height2313.Lower6960.Prefix6969Rescue.TransferPrice)
    (m r : JointLedger.Book) (lossCap : ℕ) where
  main_fee : Prefix6969Main.RankBill.fee main .near lossCap ≤ m.fee
  rescue_fee : rp.fee ≤ r.fee
  mainOrd : m.ordinateCredit = mp.retainedCredit 0
  mainSeed : m.seedCredit = mp.retainedCredit 1 + mp.retainedCredit 2
  rescueOrd : r.ordinateCredit = rp.credit 0
  rescueSeed : r.seedCredit = rp.credit 1 + rp.credit 2
  mainMass : main.history main.last 1 < (m.seedMass : ℚ)+1
  rescueMass : rescue.history (rescue.count-1) 1 < (r.seedMass : ℚ)+1
  mainGrade : ℕ
  rescueGrade : ℕ
  mainDegree : main.history main.last 0 < (mainGrade : ℚ)+1
  rescueDegree : rescue.history (rescue.count-1) 0 < (rescueGrade : ℚ)+1

private theorem cap_nat {n k : ℕ} {q : ℚ}
    (cap : (n : ℚ) ≤ q) (rounded : q < (k : ℚ)+1) : n ≤ k := by
  apply Nat.le_of_lt_succ
  exact_mod_cast cap.trans_lt rounded

/-- Produce the native normal pair, pay both real prefixes and filter the
main parent set by exclusion of the original exceptional jet. -/
theorem of_rank_bounded_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    {main : Research6970.Height2313.Lower6960.Prefix6969Main.Plan} {mp : Research6970.Height2313.Lower6960.Prefix6969Main.Pricing}
    (mainValid : main.Valid) (mainPrice : mp.Valid main Band.near)
    {first extra low floor : ℕ} {outer : P1_7.Bank}
    {rankCert : Prefix6969Main.RankBill.Certificate} {lossCap : ℕ}
    (mainSource : main.Sources first 2313 outer extra 2 low floor)
    {rescue : Research6970.Height2313.Lower6960.Prefix6969Rescue.Plan} {rp : Research6970.Height2313.Lower6960.Prefix6969Rescue.TransferPrice}
    (rescueSource : rescue.Sources first 2313) (rescuePrice : rp.Valid rescue)
    (mainBill : Prefix6969Main.RankBill.Sufficient main mp .near rankCert lossCap)
    {m r : JointLedger.Book} (checked : RankBoundedNormalBounds main mp rescue rp m r lossCap)
    (firstPos : 0 < first)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2313)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G rescue.primeShape)
    (known : Common (evaluated Crt (word M) outer.shape
      (HelperSource.cutoffCount outer.shape 179730 M.overhead.toNat 10-1)) G)
    (mainDegree : 2 ≤ jetDegree G) (mainSeed : low ≤ seedDegree G)
    (mainFloor : floor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (rescueDegree : rescue.degree ≤ jetDegree G) (rescueSeed : rescue.seedFloor ≤ seedDegree G)
    (rescueFloor : rescue.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : Pair F Crt G m r, P.mainGrade=checked.mainGrade ∧ P.rescueGrade=checked.rescueGrade := by
  classical
  obtain ⟨R, I, C, A, identity, mainCount, mainMass, mainGeom, mainOrigin, mainCover⟩ :=
    Research6970.Height2313.Lower6960.Prefix6969Main.main_prefix_rank_bounded F Crt main mainValid Band.near mp mainPrice mainSource mainBill firstPos lo hi
      noPole residues phys known mainDegree mainSeed mainFloor
  have subRes : ∀ γ∈Research6970.Height2313.Lower6960.Prefix6969Pair.zeros F G,
      MarkResidues D (M.label γ) ((Research6970.Height2313.Lower6960.Prefix6969Pair.zeros_family F G).scalar γ) :=
    fun γ hγ => residues γ (mem_filter.mp hγ).1
  have roots : ∀ γ∈Research6970.Height2313.Lower6960.Prefix6969Pair.zeros F G,
      jetAt G (M.label γ) ((Research6970.Height2313.Lower6960.Prefix6969Pair.zeros_family F G).scalar γ) = 0 :=
    fun γ hγ => (mem_filter.mp hγ).2
  obtain ⟨Q, B, S, _, rescueCount, rescueMass, rescueGeom, rescueCover⟩ :=
    Research6970.Height2313.Lower6960.Prefix6969Rescue.normal_prefix_transferred (Research6970.Height2313.Lower6960.Prefix6969Pair.zeros_family F G) (Crt := Crt)
      rescueSource rescuePrice lo hi noPole subRes phys prime slope seeded caps
      rescueDegree rescueSeed rescueFloor roots
  let keep := A.filter (fun q => G∉q.asIdeal)
  have activeM (J) (mem : J∈I.final) : Active J := (I.kept_geom (mem_filter.mp mem).1).1
  have activeR (J) (mem : J∈B.final) : Active J :=
    (Q.parent_geom (Research6970.Height2313.Lower6960.Prefix6969Rescue.Invoice.Book.final_initial B mem)).1
  refine ⟨⟨C.paid ∪ Research6970.Height2313.Lower6960.Prefix6969Rescue.Invoice.paid B, keep, S, I.final, B.final, activeM, activeR,
    ?_, ?_, fun q h => mainOrigin q (mem_filter.mp h).1, fun q h => (rescueGeom q h).2.2.2,
    mp.retainedCredit, rp.credit, checked.mainOrd, checked.mainSeed, checked.rescueOrd, checked.rescueSeed,
    ?_, cap_nat (mainMass 1) checked.mainMass, cap_nat (rescueMass 1) checked.rescueMass,
    checked.mainGrade, checked.rescueGrade, cap_nat (mainMass 0) checked.mainDegree,
    cap_nat (rescueMass 0) checked.rescueDegree, ?_⟩, rfl, rfl⟩
  · intro q h
    have parent := mainGeom q (mem_filter.mp h).1
    exact ⟨parent.1, parent.2, (mem_filter.mp h).2⟩
  · intro q h
    have parent := rescueGeom q h
    exact ⟨parent.1, parent.2.1, parent.2.2.1⟩
  · have union := card_union_le C.paid (Research6970.Height2313.Lower6960.Prefix6969Rescue.Invoice.paid B)
    have mainPaid := mainCount.trans checked.main_fee
    have rescuePaid := rescueCount.trans checked.rescue_fee
    change (C.paid ∪ Research6970.Height2313.Lower6960.Prefix6969Rescue.Invoice.paid B).card +
      mp.charge I.final + Research6970.Height2313.Lower6960.Prefix6969Rescue.Invoice.charge B rp.credit ≤ m.fee+r.fee
    omega
  · intro γ hγ
    by_cases root : jetAt G (M.label γ) (F.scalar γ) = 0
    · rcases rescueCover γ (mem_filter.mpr ⟨hγ,root⟩) with paid | ⟨reg,on⟩
      · exact Or.inl (mem_union_right _ paid)
      · exact Or.inr (Or.inr ⟨root,reg,on⟩)
    · have inMain : γ∈R.marks := mem_filter.mpr ⟨hγ, by simpa only [identity] using root⟩
      rcases mainCover γ inMain with paid | ⟨q,mem,on⟩
      · exact Or.inl (mem_union_left _ paid)
      · exact Or.inr (Or.inl ⟨root,q,mem_filter.mpr ⟨mem,fun owns => root (on G owns)⟩,on⟩)

end
end Research6970.Height2308
