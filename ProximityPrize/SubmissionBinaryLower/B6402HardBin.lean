import ProximityPrize.SubmissionBinaryLower.B6402HardAuxiliary
import ProximityPrize.SubmissionBinaryLower.B6402ResidualGap
import ProximityPrize.SubmissionBinaryLower.B6402CapSound
import ProximityPrize.SubmissionBinaryLower.B6401FactorBound

/-! An actual hard factor at one of the new 6402 price cells. The numerical
inputs are its graded budget, load, gap and native cap witness. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402HardBin
open Polynomial ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open B6401Params hiding A
open B6402HybridP64 (A linePow BadOn6402)
open B6401ContactKerD B6401QuotInterp B6401ResLineOrd B6402MixedDegree B6402SeedCoordinates
open B6402HardAuxiliary B6402InterpolationPrice B6402DimensionBudget B6402LocatorDivision
open B6402ResidualGap B6402IntFarkas P64Caps.Weighted P64LineOrder BCHKSSubstitutionVanish
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
local notation "K" => BinaryIRSProfile.Field
local notation "I" => BinaryIRSProfile.Index

theorem labels {W WF s q T H m b J WP B delta gapLimit cap : ℕ}
    (u₀ u₁ : I → K) (hq : q=1 ∨ q=2) (hs : 1≤s) (hH : H≤T)
    (hJ : W/(wY-1)≤J) (hJ2 : 2≤J) (hmJ : 2*m≤J+s) (hb : b≤m)
    (globalCap : q*(W/(wY-1))≤T-H+1) (localCap : q*(s+2*m)≤T-H+1)
    (k : I → ℕ) (fc : KerDIdx wY WF 1 → K[X]) (F : ContactPoly (Polynomial K))
    (heq : F=∑ e,cC (fc e)*kerDBasisPoly e.1)
    (hfw : wdeg wY F=WF) (hWL : wY-1≤WF) (hh : mixed q F=H) (slope : F.natDegree=1) (dF : contactDeriv F=0)
    (hirr : Irreducible F) (hirrK : Irreducible (liftCRat F)) (fdeg : ∀ j,(F.coeff j).natDegree≤5)
    (f4 : (F.coeff 1).natDegree=4)
    (ord : ∀ i,twOrdGE (B6402PrimarySystem.localized (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) fc) (k i))
    (exactOrd : ∀ i,∃ a b,a+b=k i ∧ twCoeff (B6402PrimarySystem.localized (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) fc) a b≠0)
    (budget : (∑ i,(localSize (mi m b (k i)) s q T-localSize (mi m b (k i)-k i) (s-1) q (T-H)))+
      ((regular k BinaryIRSProfile.domain F).card:ℤ)*(regularCost J s m b*(T+s*H+1):ℕ)+
      ((exceptional k BinaryIRSProfile.domain F).card:ℤ)*(exceptionalCost s b*(T+1+(J+16*b+2)*H):ℕ) <
      sourceSize wY W s q T-sourceSize wY (W-WF) (s-1) q (T-H))
    (load : W<2*((m-b)*A+b*(marked k).card))
    (weightBound : W+s*(WF-(wY-1))≤WP+2*b*(regular k BinaryIRSProfile.domain F).card)
    (yb : WP/wY≤B) (gapBound : gapLimit+2*b*(exceptional k BinaryIRSProfile.domain F).card≤delta)
    (witness : CapWitness) (checked : Binary6402NativeCaps.allowance (m-b) B WP delta q (T+s*H) cap witness=true)
    (S : Finset K) (P : K → K[X]) (Az : K → Finset I)
    (hp : ∀ z∈S,(P z).natDegree≤wY) (hcard : ∀ z∈S,A≤(Az z).card)
    (hmatch : ∀ z∈S,∀ i,i∈Az z ↔ (P z).eval (BinaryIRSProfile.domain i)=u₀ i+z^q*u₁ i)
    (onF : ∀ z∈S,evalContact (evalZContact F z) (P z)=0) (hbad : ∀ z∈S,BadOn6402 u₀ u₁ (Az z))
    (gap : ∀ z∈S,(s:ℤ)*((WF:ℤ)-(wY-1:ℕ)-(∑ i∈Az z,charge (k i)))≤gapLimit) :
    S.card≤cap+(regular k BinaryIRSProfile.domain F).card*H := by
  classical
  let x := BinaryIRSProfile.domain
  let y := linePow u₀ u₁ q
  let good := regular k x F
  obtain ⟨u,E,hE,hp0,hOrd,hLoc,hV⟩ := auxiliary (by decide : 1<wY) hs hH hJ hJ2 hmJ hb globalCap localCap
    x y (B6402HybridP64.linePow_natDegree_le u₀ u₁ q) k fc F heq hfw hh slope dF hirr hirrK fdeg f4 ord exactOrd budget
  let G := source q T u
  let p := resultant F G 1 s
  obtain ⟨r,hr,eq⟩ := factored x good b p hp0 hLoc
  have gb := source_bounds (by decide : 0<wY) u
  have before : weightedSupportDegree p wY≤W+s*(WF-(wY-1)) := by
    have h := weightedSupportDegree_resultant_le F G wY WF W 1 s hfw.le gb.2.2.1 (by simpa using hWL)
    simpa only [one_mul] using h
  have after : weightedSupportDegree r wY≤WP := by
    have hh' := before
    rw [eq,weightedSupportDegree_mul _ _ _ (loc_ne x good b) hr,weighted_locator] at hh'
    change W+s*(WF-(wY-1))≤WP+2*b*good.card at weightBound
    omega
  have hbR : r.natDegree≤B := by
    have ht := coeffWeight_le_of_ne r wY r.natDegree (by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hr)
    apply le_trans _ yb
    apply (Nat.le_div_iff_mul_le (by decide : 0<wY)).mpr
    rw [Nat.mul_comm r.natDegree wY]; omega
  have hseed : ∀ j a,((r.coeff j).coeff a).natDegree≤T+s*H := by
    apply quotient_seed p _ r hp0 eq
    intro j a; by_cases hz : (p.coeff j).coeff a=0
    · simp [hz]
    · have hn := coeff_natDegree (p:=(p.coeff j).coeff a)
      have hne := leadingCoeff_ne_zero.mpr hz
      have hh' := B6402RegularSystem.resultant_weight F G q H T s hh.le gb.2.2.2 a j ((p.coeff j).coeff a).natDegree (by
        change ((p.coeff j).coeff a).coeff ((p.coeff j).coeff a).natDegree≠0
        rw [hn]; exact hne)
      simp only [zero_mul,zero_add,one_mul] at hh'; omega
  let clean := S \ E
  have memS {z} (h : z∈clean) : z∈S := (Finset.mem_sdiff.mp h).1
  have curve z (hz : z∈clean) : BCHKSSubstitutionVanish.triEval r z (P z)=0 := by
    have hfit i : i∈Az z ↔ (P z).eval (x i)=(y i).eval z := by
      simpa only [x,y,B6402HybridP64.eval_linePow] using hmatch z (memS hz) i
    have cnt := Nat.mul_le_mul_left (m-b) (hcard z (memS hz))
    have hload := load.trans_le (Nat.mul_le_mul_left 2 (Nat.add_le_add_right cnt _))
    have hcur := hV z (Finset.mem_sdiff.mp hz).2 (P z) (Az z) (hp z (memS hz)) hfit (onF z (memS hz)) hload
    change BCHKSSubstitutionVanish.triEval p z (P z)=0 at hcur
    rw [eq,P64Cofactor.triEval_mul] at hcur
    exact (mul_eq_zero.mp hcur).resolve_left (curve_ne x good b z (P z))
  have gapR z (hz : z∈clean) := cleaned_gap x y k F p r hr m b s wY A W WF gapLimit hb (by decide) hWL
    eq (Az z) hOrd before load (gap z (memS hz))
  have bound := B6402CapSound.priced_labels u₀ u₁ (m-b) B (T+s*H) WP delta q cap witness hq checked r hr
    after hbR hseed clean P Az (fun z hz => hp z (memS hz)) curve (fun z hz => hcard z (memS hz))
    (fun z hz => hmatch z (memS hz)) (fun z hz => hbad z (memS hz))
    (fun z hz => (gapR z hz).trans (by exact_mod_cast gapBound))
  have sub : S ⊆ clean∪E := by intro z h; by_cases he : z∈E <;> simp [clean,h,he]
  have hc : clean.card≤cap := by exact_mod_cast bound
  exact (Finset.card_le_card sub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hc hE))

#print axioms labels
end ProximityPrize.SubmissionBinaryLower.B6402HardBin
