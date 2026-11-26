import ProximityPrize.SubmissionBinaryLower.B6402FibreSlice
import ProximityPrize.SubmissionBinaryLower.B6402QuarticProfile

/-! At a site of order two the translated slope coefficient is a single
quartic monomial. If it vanishes, w³ times a nonzero degree-two factor
describes the entire spatial fibre. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402OrderTwoFibres
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd
open B6402FibreSlice B6402PrimarySystem B6402MixedDegree B6402LocalInput B6402ExceptionalQuartic
open B6402ExceptionalSystem B6402ExceptionalSupport P64LineOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {K : Type*} [Field K] [CharP K 2]
noncomputable local instance : CommRing (Polynomial K) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial K)) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Fibre K) := AddMonoidAlgebra.commRing

theorem lower_slices {w WF : ℕ} (hw : 0<w) (x : K) (y : K[X])
    (fc : KerDIdx w WF 1 → K[X]) (F : ContactPoly (Polynomial K))
    (he : F=∑ e,cC (fc e)*kerDBasisPoly e.1) (hord : twOrdGE (localized x y fc) 2) :
    ∀ j<3,(ordinateHom x y (F.coeff 0)).coeff j=0 ∧ (ordinateHom x y (F.coeff 1)).coeff j=0 := by
  have h := biOrdGE_sf0_sf1_of_twOrdGE (k:=2) hw x y fc hord
  intro j hj
  rw [he,ordinate_coeff,ordinate_coeff]
  exact ⟨h.1 0 j (by omega),h.2 0 j (by omega)⟩

theorem form {w WF : ℕ} (hw : 0<w) (x : K) (y : K[X]) (fc : KerDIdx w WF 1 → K[X])
    (F : ContactPoly (Polynomial K)) (he : F=∑ e,cC (fc e)*kerDBasisPoly e.1)
    (hord : twOrdGE (localized x y fc) 2) (slope : F.natDegree=1) (dF : contactDeriv F=0)
    (hd4 : (F.coeff 1).natDegree≤4) :
    let p := ordinateHom x y (F.coeff 1)
    p=monomial 4 (p.coeff 4) := by
  intro p
  have hf2 : F.coeff 2=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have dz : dXBi (0 : BiPoly (Polynomial K))=0 := by apply Polynomial.ext; intro j; simp [coeff_dXBi]
  have hf1 : (F.coeff 1).derivative=0 := by
    have h := congrArg (fun g : ContactPoly (Polynomial K) => g.coeff 2) dF
    simpa [coeff_contactDeriv,hf2,dz] using h
  have dp : p.derivative=0 := by
    change (taylor y ((F.coeff 1).map (evalRingHom (C x)))).derivative=0
    rw [←taylor_derivative,derivative_map,hf1,Polynomial.map_zero,map_zero]
  have h3 : p.coeff 3=0 := by
    have hz := congrArg (fun h : Polynomial (Polynomial K) => h.coeff 2) dp
    have three : (3 : Polynomial K)=1 := by
      have two : (2 : Polynomial K)=0 := CharTwo.two_eq_zero
      calc (3:Polynomial K)=2+1 := by norm_num
           _ = _ := by rw [two,zero_add]
    have hcoef : p.coeff 3*((2:Polynomial K)+1)=0 := by simpa only [coeff_derivative,Nat.cast_ofNat,coeff_zero] using hz
    rwa [CharTwo.two_eq_zero,zero_add,mul_one] at hcoef
  have hdeg : p.natDegree≤4 := by
    change (taylor y ((F.coeff 1).map (evalRingHom (C x)))).natDegree≤4
    rw [natDegree_taylor]; exact natDegree_map_le.trans hd4
  apply Polynomial.ext; intro j
  rw [coeff_monomial,Finsupp.single_apply]
  by_cases hj : 4=j
  · subst j; simp
  · rw [if_neg hj]
    by_cases big : 4<j
    · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt big)
    by_cases low : j<3
    · exact (lower_slices hw x y fc F he hord j low).2
    · have e : j=3 := by omega
      exact e ▸ h3

theorem bad_site {w WF q H : ℕ} (hw : 0<w) (x : K) (y : K[X]) (hy : y.natDegree≤q)
    (fc : KerDIdx w WF 1 → K[X]) (F : ContactPoly (Polynomial K))
    (he : F=∑ e,cC (fc e)*kerDBasisPoly e.1) (hirr : Irreducible F) (hs : F.natDegree=1)
    (height : mixed q F≤H) (ordeg : ∀ j,(F.coeff j).natDegree≤5)
    (hord : twOrdGE (localized x y fc) 2) (bad : evalXAt (F.coeff 1) x=0) :
    let p := (localized x y fc).coeff 0
    p=(Polynomial.X : Fibre K)^3*tail p ∧ tail p≠0 ∧ Bounds (tail p) 0 2 H := by
  intro p
  have h0 : ordinateHom x y (F.coeff 1)=0 := by
    change taylor y (evalXAt (F.coeff 1) x)=0
    rw [bad,map_zero]
  have ep : p=(ordinateHom x y (F.coeff 0)).map C := by
    change (localized x y fc).coeff 0=_
    rw [localized_slice,←he,linear_slice _ _ F hs.le,h0,Polynomial.map_zero,zero_mul,add_zero]
  have hn : p≠0 := by
    rw [ep]; exact (Polynomial.map_ne_zero_iff C_injective).mpr (nonzero_slice x y F hirr hs bad)
  have st := factor_series hw x y hy fc F he height ordeg 0
  have hsl : P64Found.WtLE 1 0 0 0 p := by
    intro a b l hh
    by_cases ha : a=0
    · simp [ha]
    · exfalso; apply hh
      rw [ep]; simp [P64Found.c3,coeff_map,coeff_C,ha]
  apply B6402ExceptionalQuartic.factor p H hn ⟨hsl,st.ordinate,st.seed⟩
  intro j hj
  have hz := (lower_slices hw x y fc F he hord j hj).1
  rw [ep,coeff_map,hz,map_zero]

#print axioms form
#print axioms bad_site
end ProximityPrize.SubmissionBinaryLower.B6402OrderTwoFibres
