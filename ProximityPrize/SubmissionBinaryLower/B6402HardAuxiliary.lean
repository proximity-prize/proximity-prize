import ProximityPrize.SubmissionBinaryLower.B6402MissedInterpolation
import ProximityPrize.SubmissionBinaryLower.B6402DimensionBudget
import ProximityPrize.SubmissionBinaryLower.B6402OrderTwoFibres
import ProximityPrize.SubmissionBinaryLower.B6402RegularExceptions
import ProximityPrize.SubmissionBinaryLower.B6402WitnessRootLoad

/-! The actual order-two profile of a slope-linear invariant factor supplies
both types of local equations. Every retained original label is handled by
the same properly intersecting auxiliary, regardless of its agreement set. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402HardAuxiliary
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd
open B6402SeedCoordinates B6402QuotientSpace B6402PrimarySystem B6402MixedDegree B6402RegularSystem
open B6402ExceptionalSystem B6402ExceptionalQuartic B6402InterpolationPrice B6402DimensionBudget
open B6402RegularWitness B6402FibreSlice B6402RegularLocator P64LineOrder
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type} [Field K] [CharP K 2] {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def marked (k : I → ℕ) := Finset.univ.filter fun i => k i=2
noncomputable def regular (k : I → ℕ) (x : I ↪ K) (F : ContactPoly (Polynomial K)) :=
  (marked k).filter fun i => evalXAt (F.coeff 1) (x i)≠0
noncomputable def exceptional (k : I → ℕ) (x : I ↪ K) (F : ContactPoly (Polynomial K)) :=
  (marked k).filter fun i => evalXAt (F.coeff 1) (x i)=0

def mi (m b : ℕ) (k : ℕ) := if k=2 then m else m-b

theorem auxiliary {w W WF s q T H m b J : ℕ} (hw : 1<w) (hs : 1≤s) (hH : H≤T)
    (hJ : W/(w-1)≤J) (hJ2 : 2≤J) (hmJ : 2*m≤J+s) (hb : b≤m)
    (globalCap : q*(W/(w-1))≤T-H+1) (localCap : q*(s+2*m)≤T-H+1)
    (x : I ↪ K) (y : I → K[X]) (hy : ∀ i,(y i).natDegree≤q) (k : I → ℕ)
    (fc : KerDIdx w WF 1 → K[X]) (F : ContactPoly (Polynomial K)) (heq : F=∑ e,cC (fc e)*kerDBasisPoly e.1)
    (hfw : wdeg w F=WF) (hh : mixed q F=H) (slope : F.natDegree=1) (dF : contactDeriv F=0)
    (hirr : Irreducible F) (hirrK : Irreducible (liftCRat F)) (fdeg : ∀ j,(F.coeff j).natDegree≤5)
    (f4 : (F.coeff 1).natDegree=4)
    (ord : ∀ i,twOrdGE (localized (x i) (y i) fc) (k i))
    (exactOrd : ∀ i,∃ a b,a+b=k i ∧ twCoeff (localized (x i) (y i) fc) a b≠0)
    (budget : (∑ i,(localSize (mi m b (k i)) s q T-localSize (mi m b (k i)-k i) (s-1) q (T-H)))+
      ((regular k x F).card:ℤ)*(regularCost J s m b*(T+s*H+1):ℕ)+
      ((exceptional k x F).card:ℤ)*(exceptionalCost s b*(T+1+(J+16*b+2)*H):ℕ) <
      sourceSize w W s q T-sourceSize w (W-WF) (s-1) q (T-H)) :
    ∃ (u : Global K w W s q T) (E : Finset K),
      let G:=source q T u
      E.card≤(regular k x F).card*H ∧ resultant F G 1 s≠0 ∧
      (∀ i,OrdGE (resultant F G 1 s) (x i) (y i)
        (if k i=0 then 2*mi m b (k i)-s else 2*mi m b (k i)+s*(2*k i-1))) ∧
      (∀ i∈regular k x F,C ((Polynomial.X : (Polynomial K)[X])-C (C (x i)))^(2*b) ∣ resultant F G 1 s) ∧
      (∀ z∉E,∀ (P : K[X]) (fits : Finset I),P.natDegree≤w →
        (∀ i,i∈fits ↔ P.eval (x i)=(y i).eval z) → evalContact (evalZContact F z) P=0 →
        W<2*((m-b)*fits.card+b*(marked k).card) → BCHKSSubstitutionVanish.triEval (resultant F G 1 s) z P=0) := by
  classical
  let R := ↥(regular k x F)
  let B := ↥(exceptional k x F)
  let f0 (i : I) := (localized (x i) (y i) fc).coeff 0
  let L (i : B) := tail (f0 i.val)
  have bad (i : B) := Finset.mem_filter.mp i.property
  have good (i : R) := Finset.mem_filter.mp i.property
  have mark (i : I) (hi : i∈marked k) : k i=2 := (Finset.mem_filter.mp hi).2
  have ord2 (i : I) (hi : i∈marked k) := (mark i hi) ▸ ord i
  have bl (i : B) := B6402OrderTwoFibres.bad_site (by omega : 0<w) (x i.val) (y i.val) (hy i.val)
    fc F heq hirr slope hh.le fdeg (ord2 i.val (bad i).1) (bad i).2
  have cLocal i : q*(s+2*mi m b (k i))≤T-H+1 := by
    have le : mi m b (k i)≤m := by unfold mi; split <;> omega
    exact (Nat.mul_le_mul_left q (by omega)).trans localCap
  have paid := B6402DimensionBudget.surplus (R:=R) (B:=B) w W WF s q T H m b J
    (fun i => mi m b (k i)) k hw hH globalCap cLocal hJ2 hmJ hb
    (by simpa only [R,B,Fintype.card_coe] using budget)
  have cube := B6402ExceptionalQuartic.ordinate_cube (K:=K)
  obtain ⟨u,v,proper,pr,regTests,badTests,inv,deg,weight,height⟩ :=
    B6402MissedInterpolation.exists_interpolant hw hs hH (fun i => mi m b (k i)) k x y hy
      (fun i : R => i.val) (fun i : B => i.val) fc F heq hh.le fdeg hirr slope dF hirrK ord exactOrd
      m b J hJ (fun _ => (Polynomial.X : Fibre K)^3) L (fun _=>2) (fun _=>hJ2)
      (fun i => (bl i).2.1) (fun _ => cube) (fun i => (bl i).2.2) (by simpa only [hfw,hh] using paid)
  let G := source q T u
  have hf1 : F.coeff 1≠0 := by rw [←slope,coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hirr.ne_zero
  have orderR (i : I) : OrdGE (resultant F G 1 s) (x i) (y i)
      (if k i=0 then 2*mi m b (k i)-s else 2*mi m b (k i)+s*(2*k i-1)) := by
    rw [heq]
    exact ordGE_resultant_deg1_ge (by omega) hs (x i) (y i) fc (decode (width q T) u)
      (decode (localWidth q (T-H)) (v i)) (heq ▸ hf1) (ord i) (pr i)
  have qForm (i : I) (hi : i∈regular k x F) :=
    B6402OrderTwoFibres.form (by omega : 0<w) (x i) (y i) fc F heq (ord2 i (Finset.mem_filter.mp hi).1) slope dF f4.le
  have quart (i : I) (hi : i∈regular k x F) :
      ordinateHom (x i) (y i) (F.coeff 1)=monomial 4 (quartic F (x i)) := by
    simpa only [top F (x i) (y i) f4.le] using qForm i hi
  have ex := B6402RegularExceptions.excluded F q H hh.le x (regular k x F)
    (fun i hi => B6402RegularExceptions.nonzero_quartic F (x i) (y i) (Finset.mem_filter.mp hi).2 (quart i hi))
  obtain ⟨E,hE,heE⟩ := ex
  have loc (i : I) (hi : i∈regular k x F) : C ((Polynomial.X : (Polynomial K)[X])-C (C (x i)))^(2*b) ∣ resultant F G 1 s := by
    apply regular_locator F G (x i) (y i) m b s J slope.le deg dF inv
    · intro h
      have hiF := (Finset.mem_filter.mp hi).2
      obtain ⟨a,ha⟩ := h
      apply hiF
      simp [evalXAt,ha]
    · exact ordinate_cap hw hJ F G weight (fdeg 0) f4.le
    · have ho := orderR i
      simpa only [mark i (Finset.mem_filter.mp hi).1,mi,ite_true,show (2:ℕ)≠0 by decide,ite_false,show 2*2-1=3 by decide,Nat.mul_comm s 3] using ho
    · exact regTests ⟨i,hi⟩
  refine ⟨u,E,hE,proper,orderR,loc,?_⟩
  intro z hz P fits hp hfit onF load
  apply (B6402WitnessRootLoad.witness_vanish (d:=1) (by omega : 1≤w) x y z P hp fc (decode (width q T) u)
    (fun i => multiplier (decode (localWidth q (T-H)) (v i))) F G heq rfl slope le_rfl deg weight (marked k) fits m b hb
    (fun i => by simpa only [mi,marked,Finset.mem_filter,Finset.mem_univ,true_and] using pr i)
    onF (fun i hi => (hfit i).mp hi) ?_ load).2
  intro i hi hm
  have miss : P.eval (x i)≠(y i).eval z := fun h => hm ((hfit i).mpr h)
  by_cases hgood : evalXAt (F.coeff 1) (x i)≠0
  · have hiR : i∈regular k x F := Finset.mem_filter.mpr ⟨hi,hgood⟩
    exact regular_miss F G (x i) (y i) z P s b slope.le deg onF (quart i hiR) (heE z hz i hiR) miss (loc i hiR)
  · let r : B := ⟨i,Finset.mem_filter.mpr ⟨hi,not_ne_iff.mp hgood⟩⟩
    exact B6402MissWitness.exceptional_miss (x i) (y i) z P fc (decode (width q T) u) 3 b (L r)
      (bl r).1 (badTests r) (heq ▸ onF) miss

#print axioms auxiliary
end ProximityPrize.SubmissionBinaryLower.B6402HardAuxiliary
