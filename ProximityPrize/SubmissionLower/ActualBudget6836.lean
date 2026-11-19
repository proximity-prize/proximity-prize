/- Apache-2.0. Bome2017. Connect the finite incidence and partition certificates
   to the original KoalaBear hard family. Built on Lucieno and BitWonka. -/
import ProximityPrize.SubmissionLower.PartitionFamily
import ProximityPrize.SubmissionLower.PhysicalCap
import ProximityPrize.SubmissionLower.Night6836VerifiedGrid
import ProximityPrize.SubmissionLower.Night6836ActualFactor
import ProximityPrize.SubmissionLower.Night6836PrimaryShell
namespace ProximityPrize.SubmissionLower.KoalaOriginal6836
open ProximityPrize.Benchmark Genuine6969
open RCN095 RCN130 RCN156 RCN238 RCN266 RCN319
open Koala6831Moving Koala6831MovingPaid Left6836Ready
open Night6836FlowSources LocatorFactorAggregate LocatorBatchProductRoute
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 30000
def PhysicalFactorPrices : Prop :=
  ∀ {H : MvPolynomial (Fin 4) F} {Γ : Finset F} {sel : F → Polynomial F}
    {u v : IRSProfile.Index → F} {D : ℕ}, Raw6836.Original Dmn H Γ sel u v D →
    ∀ (p : RegularIndex H) {r e z : ℕ}, 0 < r → contactFlag p.1 = ⟨z,e,r⟩ →
    r ≤ 18 ∧ r+e ≤ 76 ∧ r+e+z ≤ 9352 →
    (regularFiber H Γ sel p).card ≤ Koala6836.Tables.oneUnits r e (z/100)*10000000000000 ∧
    (r+e+z ≤ Koala6836.Room.maxTotal r e →
      (regularFiber H Γ sel p).card ≤ Koala6836.Room.budget r e (r+e+z))

def OriginalSlabStatement : Prop :=
  ∀(original : Finset F) (R : Ready Dmn original) (H : MvPolynomial (Fin 4) F), H≠0 →
    H∈LocatorLowQuotient.nestedCoefficientBox F Stage.primary.cutoff 131071 83491 444 99 →
    ∀(Γ : Finset F), Γ⊆R.seeds → ∀(A : Finset (RegularIndex H)), A.Nonempty →
    let f := contactFlag (regularProduct H A)
    f.all≤18 → f.all+(middle f-f.all)≤76 →
    total f≤min 9352 (Koala6836.Room.maxTotal f.all (middle f-f.all)) →
    (A.biUnion (regularFiber H Γ R.selected)).card≤Koala6836.Room.budget f.all (middle f-f.all) (total f)

theorem family_of_prices (price : PhysicalFactorPrices) : OriginalSlabStatement := by
  classical
  intro original R H nz box Γ subset A occupied f rCap yCap tCap
  let _ : CharP F 2130706433 := Koala6831BenchmarkField.characteristic
  let live : Raw6836.Original Dmn H Γ R.selected R.u₀ R.u₁ Stage.primary.cutoff :=
    ⟨R.nodes_card,by decide +kernel,by decide +kernel,nz,⟨83491,444,99,box⟩,
      fun g hg=>R.degree g (subset hg),fun g hg=>R.agreement g (subset hg),
      RCN243.noLargeSelectedPencil_mono R.selected R.seeds Γ 131071 81105 subset R.pencil⟩
  have sub : middle f-f.all=f.yz := by change f.yz+f.all-f.all=f.yz; omega
  change f.all+(middle f-f.all)≤76 at yCap
  change total f≤min 9352 (Koala6836.Room.maxTotal f.all (middle f-f.all)) at tCap
  change _≤Koala6836.Room.budget f.all (middle f-f.all) (total f)
  rw [sub] at yCap tCap ⊢
  let old : DecidableEq F := inferInstance
  change (@Finset.biUnion _ F old A (regularFiber H Γ R.selected)).card ≤
    Koala6836.Room.budget f.all f.yz (total f)
  rw [show old = Classical.decEq F from Subsingleton.elim _ _]
  refine NightPhysicalPartition.combined H Γ R.selected A occupied Koala6836.Bound.one Koala6836.Bound.all
    Koala6836.Bound.many (Koala6836.Bound.physical_certificate (fun r e h j v =>
      (Koala6836.Fast.numeric r e h j v).1)) ?_ Koala6836.Bound.room rCap ?_ tCap
  · intro p d pr pm pt
    have pos : 0<d.all := regularCumulativeFlag_positive H p
    have he : contactFlag p.1=⟨d.zOnly,d.yz,d.all⟩ := rfl
    obtain ⟨a,b⟩ := price live p pos he ⟨pr,pm,pt⟩
    have good:=Koala6836.Fast.numeric d.all d.yz pos pr pm
    have small : d.zOnly/100<94 := by change d.all+d.yz+d.zOnly≤9352 at pt; omega
    exact ⟨a.trans (Koala6836.Bound.one_round _ _ _ good.2 small),b⟩
  · change f.yz+f.all≤76
    omega
#print axioms family_of_prices
end
end ProximityPrize.SubmissionLower.KoalaOriginal6836
