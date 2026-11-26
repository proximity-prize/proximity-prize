import ProximityPrize.SubmissionBinaryLower.B6402ScalarEquation
import ProximityPrize.SubmissionBinaryLower.B6402HardBin

namespace ProximityPrize.SubmissionBinaryLower.B6402HardScalar
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

theorem scalar {W WF s q T H m b J : ℕ}
    (u₀ : I → K) (hs : 1≤s) (hH : H≤T)
    (hJ : W/(wY-1)≤J) (hJ2 : 2≤J) (hmJ : 2*m≤J+s) (hb : b≤m)
    (globalCap : q*(W/(wY-1))≤T-H+1) (localCap : q*(s+2*m)≤T-H+1)
    (k : I → ℕ) (fc : KerDIdx wY WF 1 → K[X]) (F : ContactPoly (Polynomial K))
    (heq : F=∑ e,cC (fc e)*kerDBasisPoly e.1)
    (hfw : wdeg wY F=WF) (hWL : wY-1≤WF) (hh : mixed q F=H) (slope : F.natDegree=1) (dF : contactDeriv F=0)
    (hirr : Irreducible F) (hirrK : Irreducible (liftCRat F)) (fdeg : ∀ j,(F.coeff j).natDegree≤5)
    (f4 : (F.coeff 1).natDegree=4)
    (ord : ∀ i,twOrdGE (B6402PrimarySystem.localized (BinaryIRSProfile.domain i) (C (u₀ i)) fc) (k i))
    (exactOrd : ∀ i,∃ a b,a+b=k i ∧ twCoeff (B6402PrimarySystem.localized (BinaryIRSProfile.domain i) (C (u₀ i)) fc) a b≠0)
    (budget : (∑ i,(localSize (mi m b (k i)) s q T-localSize (mi m b (k i)-k i) (s-1) q (T-H)))+
      ((regular k BinaryIRSProfile.domain F).card:ℤ)*(regularCost J s m b*(T+s*H+1):ℕ)+
      ((exceptional k BinaryIRSProfile.domain F).card:ℤ)*(exceptionalCost s b*(T+1+(J+16*b+2)*H):ℕ) <
      sourceSize wY W s q T-sourceSize wY (W-WF) (s-1) q (T-H))
    (load : W<2*((m-b)*A+b*(marked k).card))
    (room : (regular k BinaryIRSProfile.domain F).card*H+(T+s*H)<Fintype.card K)
    (list : Finset (K[X])) (fits : K[X] → Finset I)
    (hP : ∀ P∈list,P.natDegree≤wY) (hA : ∀ P∈list,A≤(fits P).card)
    (hit : ∀ P∈list,∀ i,i∈fits P ↔ P.eval (BinaryIRSProfile.domain i)=u₀ i)
    (onF : ∀ z (P : K[X]),P∈list → evalContact (evalZContact F z) P=0) :
    list.card≤J+4*s := by
  classical
  let x := BinaryIRSProfile.domain
  let y (i : I) := C (u₀ i)
  obtain ⟨v,E,hE,hp,_,_,all⟩ := auxiliary (by decide : 1<wY) hs hH hJ hJ2 hmJ hb globalCap localCap
    x y (fun i => by simp [y]) k fc F heq hfw hh slope dF hirr hirrK fdeg f4 ord exactOrd budget
  let G := source q T v
  let eqn := resultant F G 1 s
  have gb := source_bounds (by decide : 0<wY) v
  have hc : ∀ j a,((eqn.coeff j).coeff a).natDegree≤T+s*H := by
    intro j a
    by_cases ha : (eqn.coeff j).coeff a=0
    · simp [ha]
    · have hne := leadingCoeff_ne_zero.mpr ha
      have e := B6402RegularSystem.resultant_weight F G q H T s hh.le gb.2.2.2 a j ((eqn.coeff j).coeff a).natDegree (by
        change ((eqn.coeff j).coeff a).coeff ((eqn.coeff j).coeff a).natDegree≠0
        rw [coeff_natDegree]; exact hne)
      simp only [zero_mul,zero_add,one_mul] at e; omega
  have hroot : ∀ z∉E,∀ P∈list,BCHKSSubstitutionVanish.triEval eqn z P=0 := by
    intro z hz P hP'
    have bnd := Nat.mul_le_mul_left (m-b) (hA P hP')
    apply all z hz P (fits P) (hP P hP') _ (onF z P hP')
      (load.trans_le (Nat.mul_le_mul_left 2 (Nat.add_le_add_right bnd _)))
    intro i; simpa only [x,y,eval_C] using hit P hP' i
  have c := B6402ScalarEquation.count eqn hp _ hc E ((Nat.add_le_add_right hE _).trans_lt room) list hroot
  exact c.trans (B6402RegularLocator.ordinate_cap (by decide : 1<wY) hJ F G gb.2.2.1 (fdeg 0) f4.le)

#print axioms scalar
end ProximityPrize.SubmissionBinaryLower.B6402HardScalar
