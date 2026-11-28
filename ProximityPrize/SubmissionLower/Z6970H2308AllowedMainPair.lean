import ProximityPrize.SubmissionLower.R6970Height2313Rescue
import ProximityPrize.SubmissionLower.R6970PrimaryPointwiseBill

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 22000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Lower6960.Prefix6969Pair
noncomputable section

open _root_.Lower6960 _root_.Research6969
open Finset Polynomial
open K1 (K)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated nodeL)
open K1_14_2 (UsesSeed toJet)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open P1_7_4 (massQ)
open Far6969RescueGeometry (Model Family OnSurface word)
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)
open PrefixRows (Common)
open Research6966
open scoped Classical

inductive MainAllowance (plan : Prefix6969Main.Plan) (price : Prefix6969Main.Pricing)
    (band : Band) : ℕ → Prop
  | standard : MainAllowance plan price band price.fee
  | pointwise (lossCap : ℕ)
      (checked : Prefix6969Main.RankBill.Pointwise plan price band lossCap) :
    MainAllowance plan price band (Prefix6969Main.RankBill.fee plan band lossCap)

theorem produce_allowed {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    {first extra a low floor : ℕ} {outer : P1_7.Bank} {band : Band}
    {main : Prefix6969Main.Plan} {mp : Prefix6969Main.Pricing}
    (mainValid : main.Valid) (mainPrice : mp.Valid main band)
    {fee : ℕ} (allowance : MainAllowance main mp band fee)
    (mainSource : main.Sources first band.last outer extra a low floor)
    {rescue : Prefix6969Rescue.Plan} {rp : Prefix6969Rescue.EarlyPrice}
    (rescueSource : rescue.Sources first band.last) (rescuePrice : rp.Valid rescue band)
    (firstPos : 0 < first)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ band.last)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G)
    (caps : RowCaps G rescue.primeShape)
    (known : Common (evaluated Crt (word M) outer.shape
      (HelperSource.cutoffCount outer.shape 179730 M.overhead.toNat 10-1)) G)
    (mainDegree : a ≤ jetDegree G) (mainSeed : low ≤ seedDegree G)
    (mainFloor : floor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (rescueDegree : rescue.degree ≤ jetDegree G) (rescueSeed : rescue.seedFloor ≤ seedDegree G)
    (rescueFloor : rescue.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ (R : Prefix6969Main.Rows main F Crt) (I : Prefix6969Main.Initial R)
      (Q : Prefix6969Rescue.Run (zeros_family F G) Crt G rescue)
      (B : Prefix6969Rescue.Book Q) (paid : Finset K) (A S : Finset Surface),
      B.final=Q.live rp.stop ∧
      paid.card + mp.charge I.final + Prefix6969Rescue.Invoice.charge B rp.credit ≤ fee+rp.fee ∧
      (∀ k, massQ I.final k ≤ main.history main.last k) ∧
      (∀ k, massQ B.final k ≤ rescue.history rp.stop k) ∧
      (∀ q∈A, Parent q ∧ Prefix6969Main.SurfacePass Crt (word M) q) ∧
      (∀ q∈A, ∃ J∈I.final, q.asIdeal=J.comap toJet) ∧
      (∀ q∈S, Parent q ∧ G∈q.asIdeal ∧ ∃ J∈B.final, q.asIdeal=J.comap toJet) ∧
      ∀ γ∈Γ, γ∈paid ∨ (jetAt G (M.label γ) (F.scalar γ) ≠ 0 ∧ ∃ q∈A, OnSurface F q γ) ∨
        (jetAt G (M.label γ) (F.scalar γ) = 0 ∧ Prefix6969Rescue.regular G (M.label γ) (F.scalar γ) ∧
          ∃ q∈S, OnSurface F q γ) := by
  cases allowance with
  | standard =>
    exact produce F Crt mainValid mainPrice mainSource rescueSource rescuePrice firstPos lo hi
      noPole residues phys prime slope seeded caps known mainDegree mainSeed mainFloor
      rescueDegree rescueSeed rescueFloor
  | pointwise lossCap checked =>
    obtain ⟨R, I, C, A, identity, mainCount, mainMass, mainGeom, mainOrigin, mainCover⟩ :=
      Prefix6969Main.main_prefix_rank_pointwise F Crt main mainValid band mp mainPrice mainSource checked firstPos lo hi
        noPole residues phys known mainDegree mainSeed mainFloor
    have subRes : ∀ γ∈zeros F G, MarkResidues D (M.label γ) ((zeros_family F G).scalar γ) :=
      fun γ hγ => residues γ (mem_filter.mp hγ).1
    have roots : ∀ γ∈zeros F G, jetAt G (M.label γ) ((zeros_family F G).scalar γ) = 0 :=
      fun γ hγ => (mem_filter.mp hγ).2
    obtain ⟨Q, B, S, bend, rescueCount, rescueMass, rescueGeom, rescueCover⟩ :=
      Prefix6969Rescue.early_prefix (zeros_family F G) (Crt := Crt) rescueSource rescuePrice lo hi noPole subRes
        phys prime slope seeded caps rescueDegree rescueSeed rescueFloor roots
    refine ⟨R, I, Q, B, C.paid ∪ Prefix6969Rescue.Invoice.paid B, A, S, bend,
      ?_, mainMass, rescueMass, mainGeom, mainOrigin, rescueGeom, ?_⟩
    · have union := card_union_le C.paid (Prefix6969Rescue.Invoice.paid B)
      omega
    · intro γ hγ
      by_cases root : jetAt G (M.label γ) (F.scalar γ) = 0
      · rcases rescueCover γ (mem_filter.mpr ⟨hγ, root⟩) with paid | ⟨reg, on⟩
        · exact Or.inl (mem_union_right _ paid)
        · exact Or.inr (Or.inr ⟨root, reg, on⟩)
      · have inMain : γ∈R.marks := mem_filter.mpr ⟨hγ, by simpa only [identity] using root⟩
        rcases mainCover γ inMain with paid | on
        · exact Or.inl (mem_union_left _ paid)
        · exact Or.inr (Or.inl ⟨root, on⟩)

end
end Research6970.Height2313.Lower6960.Prefix6969Pair
