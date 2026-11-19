/- Apache-2.0. Build the cumulative support and global coefficient box on the
   very same irreducible used in the KoalaBear 68.36 partition calculation. -/
import ProximityPrize.SubmissionLower.Night6836RawGate
import ProximityPrize.SubmissionLower.Night6836RawMono
namespace ProximityPrize.SubmissionLower.Raw6836
open scoped Classical
open RCN081 RCN095 RCN130 RCN156 RCN167 RCN174 RCN234 RCN238 RCN266 RCN275 RCN286 RCN313
open LocatorLowQuotient LocatorHybridCells LocatorFactorAggregate LocatorBatchProductRoute Koala6831Moving Koala6831MovingPaid K6833Residual
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I:Type} [Field K] [Fintype I] [CharP K 2130706433]

structure Original (x:I ↪ K) (H:MvPolynomial (Fin 4) K) (S:Finset K) (sel:K→Polynomial K)
    (u v:I→K) (D:ℕ) : Prop where
  hn : Fintype.card I=262144
  dlow : 131072≤D
  dhigh : D<2130706433
  ne : H≠0
  box : ∃ t y r, H∈nestedCoefficientBox K D 131071 t y r
  deg : ∀ g∈S,(sel g).natDegree≤131071
  hits : ∀ g∈S,181039≤(Finset.univ.filter fun i => (sel g).eval (x i) = u i+g*v i).card
  pencil : NoLargeSelectedPencil sel S 131071 81105

def trueEnv (r e z:ℕ) : Envelope := ⟨r,r+e,r+e+z⟩
private theorem own_below {p:FlagDegree} {r e z:ℕ} (h:p=⟨z,e,r⟩) :
    Below p (trueEnv r e z).flag := by
  subst p
  simp only [Below,trueEnv,Envelope.flag,middle,total]
  omega

theorem regular_row {x:I ↪ K} {H:MvPolynomial (Fin 4) K} {S:Finset K} {sel:K→Polynomial K}
    {u v:I→K} {D:ℕ} (A:Original x H S sel u v D)
    (F:RegularIndex H) {r e z:ℕ} (eq:contactFlag F.1=⟨z,e,r⟩)
    (cap:r≤18 ∧ r+e≤76 ∧ r+e+z≤9352) :
    (regularFiber H S sel F).card≤rowRaw r e z ∧
    F.1∈globalCoefficientBox K D 131071 ((trueEnv r e z).pad 0).total ((trueEnv r e z).pad 0).slope := by
  obtain ⟨t₀,y₀,r₀,box⟩ := A.box
  have fEq : originalCumulativeFlag F.1=⟨z,e,r⟩ := eq
  have shape : (trueEnv r e z).slope≤(trueEnv r e z).middle ∧ (trueEnv r e z).middle≤(trueEnv r e z).total :=
    ⟨Nat.le_add_right ..,Nat.le_add_right ..⟩
  have below := own_below fEq
  have priced := regular_raw A.ne A.dlow A.dhigh box S u v sel A.hn A.deg A.hits A.pencil F
    (trueEnv r e z) shape cap below (pad_gate _)
  rw [fEq] at priced
  exact ⟨priced,factor_global_box A.ne F box (residual_support_of_endpoint F.1 _ shape below)⟩
end
end ProximityPrize.SubmissionLower.Raw6836
#print axioms ProximityPrize.SubmissionLower.Raw6836.regular_row
