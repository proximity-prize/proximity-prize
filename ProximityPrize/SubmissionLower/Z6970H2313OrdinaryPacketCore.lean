import ProximityPrize.SubmissionLower.Z6970H2308AllowedMainPair
import ProximityPrize.SubmissionLower.R6970Height2313Helper
import ProximityPrize.SubmissionLower.R6970Height2313Rescue
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0632

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace Research6970.Height2313.Lower6960.Prefix6969Early
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet Equation jetAt)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (Ambient toJet UsesSeed)
open K1_14_2_2 (Active RowCaps mass)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open Lower6960.Far6969RescueGeometry (Model Family OnSurface word)
open Research6970.Height2313.Lower6960.Prefix6969Main (Pricing Band)
open Research6970.Height2313.Lower6960.Prefix6969Rescue (EarlyPrice graphShape)
open _root_.Lower6960 _root_.Research6969 Research6966
open scoped Classical BigOperators

private theorem cap_nat {n k : ℕ} {q : ℚ}
    (cap : (n : ℚ) ≤ q) (rounded : q < (k : ℚ)+1) : n ≤ k := by
  apply Nat.le_of_lt_succ
  exact_mod_cast cap.trans_lt rounded

structure Exit where
  mDegree : ℕ
  mWidth : ℕ
  rDegree : ℕ
  rWidth : ℕ
  marked : Bool

def Exit.extra (x : Exit) (band : Band) (rp : EarlyPrice) : ℕ :=
  let d := 131071+band.last
  if x.marked then
    (JointLedger.coefficient x.rDegree-rp.credit 1)*x.rWidth+2*x.rDegree^2
  else
    (JointRouted.seedWeight d rp.seed^2-rp.credit 0)*x.rDegree+
    (2*JointRouted.seedWeight d rp.seed*JointRouted.ordWeight d (rp.degree-1)-rp.credit 1)*x.rWidth

structure Exit.Valid (x : Exit) (main : Prefix6969Main.Plan)
    (rescue : Prefix6969Rescue.Plan) (rp : EarlyPrice) : Prop where
  mDegree : main.history main.last 0 < (x.mDegree : ℚ)+1
  mWidth : main.history main.last 1 < (x.mWidth : ℚ)+1
  rDegree : rescue.history rp.stop 0 < (x.rDegree : ℚ)+1
  rWidth : rescue.history rp.stop 1 < (x.rWidth : ℚ)+1
  tame : x.marked=true → x.rDegree<64 ∧ (2*x.rDegree-1)*x.rWidth<p

theorem settle {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    {main : Prefix6969Main.Plan} {mp : Pricing} {band : Band}
    (mainValid : main.Valid) (mainPrice : mp.Valid main band)
    {mainFee : ℕ} (mainBill : Prefix6969Pair.MainAllowance main mp band mainFee)
    {first extra a low floor : ℕ} {outer : P1_7.Bank}
    (mainSource : main.Sources first band.last outer extra a low floor)
    {rescue : Prefix6969Rescue.Plan} {rp : EarlyPrice}
    (rescueSource : rescue.Sources first band.last) (rescuePrice : rp.Valid rescue band)
    (x : Exit) (checks : x.Valid main rescue rp) (firstPositive : 0<first)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ band.last)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G rescue.primeShape)
    (known : PrefixRows.Common (evaluated Crt (word M) outer.shape
      (HelperSource.cutoffCount outer.shape 179730 M.overhead.toNat 10-1)) G)
    (nonlinear : 2 ≤ jetDegree G)
    (mainDegree : a ≤ jetDegree G) (mainSeed : low ≤ seedDegree G)
    (mainFloor : floor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (rescueDegree : rescue.degree ≤ jetDegree G) (rescueSeed : rescue.seedFloor ≤ seedDegree G)
    (rescueFloor : rescue.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (_root_.Lower6960.Prefix6969Early.Packet F Crt (mainFee+rp.fee+x.extra band rp) (mp.retainedCredit 0)
      (mp.retainedCredit 1+mp.retainedCredit 2) x.mDegree x.mWidth) := by
  obtain ⟨R,J,Q,B,paid,A,S,_,pay,ms,rs,mg,mo,rg,covered⟩ :=
    Prefix6969Pair.produce_allowed F Crt mainValid mainPrice mainBill mainSource rescueSource rescuePrice firstPositive
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
  have hiAll : M.overhead.toNat≤2557 := hi.trans (by cases band <;> decide)
  have exit : T.card ≤ Prefix6969Rescue.Invoice.charge B rp.credit+x.extra band rp := by
    cases hm : x.marked
    · have cc : RowCaps G (graphShape rp.degree rp.seed) := rescuePrice.graph_shape ▸ caps
      have ph : 131071+M.overhead≤((131071+band.last:ℕ):ℤ) := by
        push_cast
        omega
      simpa only [Exit.extra,hm,Bool.false_eq_true,ite_false,Prefix6969Rescue.Invoice.charge,add_assoc] using
        graph_exit F tr prime slope nonlinear rescuePrice.seed_pos cc ph
          (by cases band <;> decide) (by cases band <;> decide) (by cases band <;> decide)
          rgeo B.final ra rorigin ton
          (fun _ h => (mem_filter.mp h).2.1) (fun _ h => (mem_filter.mp h).2.2.1) rp.credit rd rw
    · obtain ⟨small,char⟩ := checks.tame hm
      simpa only [Exit.extra,hm,ite_true,Prefix6969Rescue.Invoice.charge,add_assoc] using
        marked_exit F tr hiAll rgeo B.final ra rorigin ton rp.credit rd rw small char
  obtain ⟨f,project⟩ := JointProjection.exists_product A (fun q h => (mg q h).1)
  have measures := JointProjection.measures project J.final ma mo
  have credit := JointProjection.credit project J.final ma mo mp.retainedCredit
    (e:=f.natDegree) (v:=K1_14_4.seedDegree f) le_rfl le_rfl
  change _ ≤ mp.charge J.final at credit
  refine ⟨⟨paid∪T,A,f,project,fun q h=>(mg q h).1,fun q h=>(mg q h).2,
    measures.1.trans (cap_nat (ms 0) checks.mDegree),
    measures.2.trans (cap_nat (ms 1) checks.mWidth),?_,?_⟩⟩
  · have union := card_union_le paid T
    omega
  · intro γ mem
    rcases covered γ mem with taken|⟨_,q,hq,on⟩|resc
    · exact Or.inl (mem_union_left _ taken)
    · exact Or.inr ⟨q,hq,on⟩
    · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨mem,resc⟩))

theorem extra_eq (x : Exit) (band : Prefix6969Main.Band) (rp : Prefix6969Rescue.EarlyPrice)
    (hd : 131071 + band.last < 179730) :
    x.extra band rp =
      if x.marked then
        (JointLedger.coefficient x.rDegree - rp.credit 1) * x.rWidth + 2 * x.rDegree ^ 2
      else
        (((2 * 262144 * (131071 + band.last) * rp.seed + 179730 - 1) / 179730 + 4) ^ 2 - rp.credit 0) * x.rDegree +
          (2 * ((2 * 262144 * (131071 + band.last) * rp.seed + 179730 - 1) / 179730 + 4) *
              ((((2 * 262144 * (131071 + band.last) * (rp.degree - 1) * (179730 - (131071 + band.last)) +
                  (262144 - (131071 + band.last)) * 179730 : ℕ)) + 179730 * (179730 - (131071 + band.last)) - 1) /
                (179730 * (179730 - (131071 + band.last))) + 4) - rp.credit 1) * x.rWidth := by
  unfold Exit.extra
  dsimp only
  rw [JointRouted.seedWeight_eq, JointRouted.ordWeight_eq _ _ hd]


structure NearCase (a l u w : ℕ) where
  main : Prefix6969Main.Plan
  mp : Prefix6969Main.Pricing
  valid : main.Valid
  mainPrice : mp.Valid main Band.near
  mainSource : main.Sources 2308 2313 Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 a l w
  rescue : Prefix6969Rescue.Plan
  rp : Prefix6969Rescue.EarlyPrice
  rescueSource : rescue.Sources 2308 2313
  rescuePrice : rp.Valid rescue Band.near
  rdegree : rescue.degree=a
  rshape : rescue.primeShape=graphShape a u
  rseed : rescue.seedFloor=l
  rfloor : rescue.physicalFloor ≤ max w ((131071-2313)*a-1)
  exit : Exit
  checks : exit.Valid main rescue rp
  mainFee : ℕ
  mainBill : Prefix6969Pair.MainAllowance main mp Band.near mainFee

def NearCase.fee {a l u w} (c : NearCase a l u w) : ℕ :=
  c.mainFee+c.rp.fee+c.exit.extra Band.near c.rp

theorem NearCase.run {a l u w : ℕ} (c : NearCase a l u w)
    {u₀ del} {M : Model u₀ del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2308 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2313)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G)
    (known : PrefixRows.Common (evaluated Crt (word M) Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank.shape
      (Research6970.Height2313.Lower6960.Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (slope : G.natDegree=1) (degree : jetDegree G=a) (nonlinear : 2≤a)
    (seed : l≤seedDegree G) (upper : seedDegree G≤u)
    (floor : w≤RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (_root_.Lower6960.Prefix6969Early.Packet F Crt c.fee (c.mp.retainedCredit 0) (c.mp.retainedCredit 1+c.mp.retainedCredit 2)
      c.exit.mDegree c.exit.mWidth) := by
  have caps : RowCaps G c.rescue.primeShape := by
    rw [c.rshape]
    intro j i hn
    have h : G.coeff j ≠ 0 := fun eq => hn (by simp [eq])
    exact ⟨(K1_14_2_2_2_1.jetDegree_le G a).mp degree.le j i hn,
      (le_natDegree_of_ne_zero h).trans slope.le,
      (K1_14_2_2_2_1.seedDegree_le G u).mp upper j i⟩
  have base := HelperWeightCap.weight_lower phys known.1.ne_zero (131071-M.overhead.toNat) (by omega)
  rw [degree, slope] at base
  have endpoint : 128758 ≤ 131071-M.overhead.toNat := by omega
  have mul := Nat.mul_le_mul_right a endpoint
  have nativeFloor : (131071-2313)*a-1 ≤ RawPhysicalDegree.weight
      (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw := by
    omega
  exact settle F Crt c.valid c.mainPrice c.mainBill c.mainSource c.rescueSource c.rescuePrice
    c.exit c.checks (by decide) lo hi noPole residues phys
    (_root_.Lower6960.Prefix6969MiddleTransfer.prime_of_irred known.1) slope known.2.2.1 caps known
    (degree.symm ▸ nonlinear) degree.ge seed floor
    (c.rdegree.symm ▸ degree.ge) (c.rseed.symm ▸ seed) (c.rfloor.trans (max_le floor nativeFloor))

def NearCase.uniform {a l u w : ℕ} (c : NearCase a l u w) : Prop :=
  c.exit.mDegree≤_root_.Lower6960.Prefix6969Early.nearGrade ∧ c.exit.mWidth≤6143 ∧
    c.fee+(_root_.Lower6960.Prefix6969Early.nearOrd-c.mp.retainedCredit 0)*c.exit.mDegree+
      (1810000000000-(c.mp.retainedCredit 1+c.mp.retainedCredit 2))*c.exit.mWidth≤237500000000000000

def UniformAllowed (a u : ℕ) : Prop :=
  (a=2 → 20≤u) ∧ (a=3 → u≤40) ∧ (a=5 → u≤25 ∨ 41≤u)

instance (a u : ℕ) : Decidable (UniformAllowed a u) := by
  unfold UniformAllowed
  infer_instance

end
end Lower6960.Prefix6969Early
