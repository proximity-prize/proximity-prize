import ProximityPrize.SubmissionBinaryLower.B6402Cofactor
import Mathlib.RingTheory.Polynomial.Basic

/-! Finite seed coordinate spaces for the 6402 interpolation. The degreeLT
equivalence uses the coefficients of the actual polynomial in Z. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402SeedCoordinates

open Polynomial B6401ContactKerD B6401QuotInterp B6402MixedDegree B6402Cofactor
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {K : Type*} [Field K]

abbrev Indices {ι : Type*} (width : ι → ℕ) := Σ i, Fin (width i)

noncomputable def decode {ι : Type*} (width : ι → ℕ) (u : Indices width → K) (i : ι) : K[X] :=
  ((degreeLTEquiv K (width i)).symm (fun j => u ⟨i,j⟩)).val

theorem decode_coeff {ι : Type*} (width : ι → ℕ) (u : Indices width → K) (i : ι) (j : Fin (width i)) :
    (decode width u i).coeff j = u ⟨i,j⟩ := by
  exact congrFun ((degreeLTEquiv K (width i)).apply_symm_apply (fun j => u ⟨i,j⟩)) j

theorem decode_add {ι : Type*} (width : ι → ℕ) (a b : Indices width → K) (i : ι) :
    decode width (a+b) i = decode width a i + decode width b i := by
  unfold decode
  let fa : Fin (width i) → K := fun j => a ⟨i,j⟩
  let fb : Fin (width i) → K := fun j => b ⟨i,j⟩
  change ((degreeLTEquiv K (width i)).symm (fa+fb)).val = _
  rw [map_add]; rfl

theorem decode_smul {ι : Type*} (width : ι → ℕ) (t : K) (a : Indices width → K) (i : ι) :
    decode width (t • a) i = C t * decode width a i := by
  unfold decode
  let fa : Fin (width i) → K := fun j => a ⟨i,j⟩
  change ((degreeLTEquiv K (width i)).symm (t • fa)).val = _
  rw [map_smul]; exact Polynomial.smul_eq_C_mul _

theorem decode_of_polynomials {ι : Type*} (width : ι → ℕ) (f : ι → K[X])
    (h : ∀ i, (f i).degree < (width i : WithBot ℕ)) (i : ι) :
    decode width (fun j => (f j.1).coeff j.2.val) i = f i := by
  let p : degreeLT K (width i) := ⟨f i,mem_degreeLT.mpr (h i)⟩
  exact congrArg Subtype.val ((degreeLTEquiv K (width i)).symm_apply_apply p)

def grade (e : ℕ × ℕ × ℕ × ℕ) := 2*e.2.2.1+e.2.1+e.1
def width {wY W s : ℕ} (q T : ℕ) (e : KerDIdx wY W s) := T+1-q*grade e.1

noncomputable def source {wY W s : ℕ} (q T : ℕ) (u : Indices (width (wY:=wY) (W:=W) (s:=s) q T) → K) :
    ContactPoly (Polynomial K) :=
  ∑ e : KerDIdx wY W s, cC (decode (width q T) u e)*kerDBasisPoly e.1

theorem decode_with_grade {ι : Type*} (weight : ι → ℕ) (T : ℕ)
    (u : Indices (fun i => T+1-weight i) → K) (i : ι)
    (hn : decode (fun i => T+1-weight i) u i ≠ 0) :
    (decode (fun i => T+1-weight i) u i).natDegree + weight i ≤ T := by
  let w (j:ι) := T+1-weight j
  have h : (decode w u i).degree < (w i : WithBot ℕ) :=
    mem_degreeLT.mp ((degreeLTEquiv K (w i)).symm (fun j => u ⟨i,j⟩)).property
  rw [degree_eq_natDegree hn] at h
  have hh := WithBot.coe_lt_coe.mp h
  dsimp [w] at hh; omega

noncomputable def coord {wY W s : ℕ} (p : ContactPoly (Polynomial K)) (e : KerDIdx wY W s) : K[X] :=
    (((p.coeff e.1.1).coeff (2*e.1.2.2.1+e.1.2.1)).coeff (2*e.1.2.2.2))

theorem coord_sum {wY W s : ℕ} (hw : 0<wY) (f : KerDIdx wY W s → K[X]) (e : KerDIdx wY W s) :
    coord (∑ a : KerDIdx wY W s, cC (f a)*kerDBasisPoly a.1) e=f e := by
  rcases e with ⟨⟨k,r,b,a⟩,he⟩
  have hr := ((mem_kerDIdxFinset_iff wY W s hw k r b a).mp he).1
  unfold coord
  rcases (show r=0 ∨ r=1 by omega) with rfl|rfl
  · simpa only [Nat.add_zero] using (show (((∑ e : KerDIdx wY W s, cC (f e)*kerDBasisPoly e.1).coeff k).coeff (2*b)).coeff (2*a) = f ⟨(k,0,b,a),he⟩ by
      rw [coeff_sum_kerDBasisPoly hw]; simp [he])
  · rw [coeff_sum_kerDBasisPoly hw]
    have h1 : (2*b+1)%2=1 := by omega
    have h2 : (2*a)%2=0 := by omega
    have h3 : (2*b+1)/2=b := by omega
    have h4 : 2*a/2=a := by omega
    simp [h1,h2,h3,h4,he]

theorem source_add {wY W s q T : ℕ} (a b : Indices (width (wY:=wY) (W:=W) (s:=s) q T) → K) :
    source q T (a+b)=source q T a + source q T b := by
  simp only [source,decode_add,cC,map_add,add_mul,Finset.sum_add_distrib]

theorem source_smul {wY W s q T : ℕ} (t : K)
    (a : Indices (width (wY:=wY) (W:=W) (s:=s) q T) → K) :
    source q T (t • a)=cC (C t)*source q T a := by
  simp only [source,decode_smul,cC,map_mul,mul_assoc,Finset.mul_sum]

theorem source_bounds [CharP K 2] {wY W s q T : ℕ} (hw : 0<wY)
    (a : Indices (width (wY:=wY) (W:=W) (s:=s) q T) → K) :
    contactDeriv (source q T a)=0 ∧ (source q T a).natDegree≤s ∧ wdeg wY (source q T a)≤W ∧
    mixed q (source q T a)≤T := by
  have h1 : contactDeriv (source q T a)=0 ∧ (source q T a).natDegree≤s ∧ wdeg wY (source q T a)≤W := by
    apply (mem_kerD_iff_exists_unique_coords hw _).mpr
    refine ⟨decode (width q T) a,rfl,?_⟩
    intro f hf; funext i
    have he := congrArg (fun t => coord t i) hf
    simpa only [source,coord_sum hw] using he.symm
  refine ⟨h1.1,h1.2.1,h1.2.2,?_⟩
  apply sum_bound hw
  intro e hn
  exact decode_with_grade (fun v : KerDIdx wY W s => q*grade v.1) T a e hn

theorem source_spans [CharP K 2] {wY W s q T : ℕ} (hw : 0<wY) (p : ContactPoly (Polynomial K))
    (hf : contactDeriv p=0) (hs : p.natDegree≤s) (hW : wdeg wY p≤W) (hm : mixed q p≤T) :
    ∃ u : Indices (width (wY:=wY) (W:=W) (s:=s) q T) → K, source q T u=p := by
  obtain ⟨f,he,_⟩ := (mem_kerD_iff_exists_unique_coords hw p).mp ⟨hf,hs,hW⟩
  have hfc := coordinate_bound hw f (he ▸ hm)
  have hdeg (i : KerDIdx wY W s) : (f i).degree < (width q T i : WithBot ℕ) := by
    by_cases hz : f i=0
    · simp [hz]
    · rw [degree_eq_natDegree hz]
      have hi:=hfc i hz
      have bound : (f i).natDegree < width q T i := by unfold width grade; omega
      exact_mod_cast bound
  refine ⟨fun i => (f i.1).coeff i.2.val,?_⟩
  unfold source
  simp_rw [decode_of_polynomials (width q T) f hdeg]
  exact he.symm

#print axioms source_bounds
#print axioms source_spans
end ProximityPrize.SubmissionBinaryLower.B6402SeedCoordinates
