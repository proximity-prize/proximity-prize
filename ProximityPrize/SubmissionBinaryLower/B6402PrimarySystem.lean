import ProximityPrize.SubmissionBinaryLower.B6402PrimaryContact
import ProximityPrize.SubmissionBinaryLower.B6402QuotientSpace

/-! The primary quotient interpolation matrix, including the local multiplier
columns and every tested seed coefficient at each site. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402PrimarySystem
open Polynomial B6401ContactKerD B6401QuotInterp B6402SeedCoordinates
open B6402FilteredJets B6402ProductJets B6402PrimaryContact B6402QuotientSpace
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K]

def localWidth {m s : ℕ} (q T : ℕ) (j : LocalBasisIdx m s) := T+1-q*localWeight j.1

abbrev Seeds (m s q T : ℕ) := Indices (localWidth (m:=m) (s:=s) q T)
abbrev Global (K : Type*) (w W s q T : ℕ) := Slots w W s q T → K
abbrev Aux (K : Type*) {ι : Type*} (m k : ι → ℕ) (s d q T H : ℕ) :=
  (i : ι) → Seeds (m i-k i) (s-d) q (T-H) → K
abbrev Rows (K : Type*) {ι : Type*} (m : ι → ℕ) (s q T : ℕ) :=
  (i : ι) → Seeds (m i) s q T → K

noncomputable def pairing {α : Type*} [Fintype α] (l : α → ℕ) (entry : α → K[X]) :
    (Indices l → K) →ₗ[K] K[X] where
  toFun u := ∑ j, decode l u j * entry j
  map_add' u v := by simp only [decode_add,add_mul,Finset.sum_add_distrib]
  map_smul' c u := by simp only [decode_smul,mul_assoc,← Finset.mul_sum,Polynomial.smul_eq_C_mul]; rfl

variable {ι : Type*} {w W WF s d q T H : ℕ}
variable (m k : ι → ℕ) (x : ι → K) (y : ι → K[X]) (fc : KerDIdx w WF d → K[X])

noncomputable def primary :
    (Global K w W s q T × Aux K m k s d q T H) →ₗ[K] Rows K m s q T :=
  LinearMap.pi fun i => LinearMap.pi fun r =>
    (lcoeff K r.2.val).comp
      (((pairing (width q T) (fun e : KerDIdx w W s => kerDLocalNF (m i) s (C (x i)) (y i) e.1 r.1)).comp
          (LinearMap.fst K _ _)) -
       ((pairing (localWidth q (T-H)) (fun a : LocalBasisIdx (m i-k i) (s-d) =>
          prodLocalNF (C (x i)) (y i) fc a.1 r.1)).comp
          ((LinearMap.proj i).comp (LinearMap.snd K _ _))))

noncomputable def localized {l t : ℕ} (x : K) (y : K[X])
    (p : KerDIdx w l t → K[X]) : LocalPoly (Polynomial K) :=
  ∑ e, locC (p e) * kerDLocalPoly (C x) y e.1

noncomputable def multiplier {m s : ℕ} (p : LocalBasisIdx m s → K[X]) : LocalPoly (Polynomial K) :=
  ∑ j, locC (p j)*localBasisElem j.1

theorem kernel_contact [CharP K 2] (hw : 0<w) (hd : d≤s) (hH : H≤T)
    (hy : ∀ i, (y i).natDegree≤q)
    (hf : B6402MixedDegree.mixed q (∑ e, cC (fc e)*kerDBasisPoly e.1) ≤ H)
    (u : Global K w W s q T × Aux K m k s d q T H)
    (hu : primary m k x y fc u=0) (i : ι) :
    twOrdGE (localized (x i) (y i) (decode (width q T) u.1) -
      localized (x i) (y i) fc * multiplier (decode (localWidth q (T-H)) (u.2 i))) (m i) := by
  apply congruence_of_filtered_rows hw hd (x i) (y i) (hy i) hH fc _ _ hf
  · exact fun e => decode_with_grade (fun j : KerDIdx w W s => q*grade j.1) T u.1 e
  · exact fun e => decode_with_grade (fun j : LocalBasisIdx (m i-k i) (s-d) => q*localWeight j.1) (T-H) (u.2 i) e
  · intro j n hn
    have hn' : n < localWidth q T j := by unfold localWidth; omega
    exact congrFun (congrFun hu i) ⟨j,n,hn'⟩

theorem decode_zero {α : Type*} (l : α → ℕ) (i : α) : decode (K:=K) l 0 i = 0 := by
  unfold decode
  change ((degreeLTEquiv K (l i)).symm 0).val=0
  simp

theorem zero_aux [CharP K 2] (hw : 0<w) (hd : d≤s) (hH : H≤T)
    (hy : ∀ i, (y i).natDegree≤q)
    (hf : B6402MixedDegree.mixed q (∑ e, cC (fc e)*kerDBasisPoly e.1) ≤ H)
    (ord : ∀ i, twOrdGE (localized (x i) (y i) fc) (k i))
    (exactOrd : ∀ i, ∃ a b, a+b=k i ∧ twCoeff (localized (x i) (y i) fc) a b ≠ 0)
    (u : Global K w W s q T × Aux K m k s d q T H)
    (hu : primary m k x y fc u=0) (hz : u.1=0) : u.2=0 := by
  funext i r
  have hc := kernel_contact m k x y fc hw hd hH hy hf u hu i
  rw [hz] at hc
  have hg : localized (x i) (y i) (decode (width (wY:=w) (W:=W) (s:=s) q T) (0 : Slots w W s q T → K))=0 := by
    simp [localized,decode_zero,locC]
  rw [hg] at hc
  have hprod := twOrdGE_sub (twOrdGE_of_zero (A:=Polynomial K) (m i)) hc
  rw [sub_sub_cancel (G:=LocalPoly (Polynomial K))] at hprod
  have h := multiplier_unique (decode (localWidth q (T-H)) (u.2 i)) (ord i) (exactOrd i) hprod r.1
  have hz' := congrArg (fun p : K[X] => p.coeff r.2.val) h
  cases r
  simpa only [decode_coeff,coeff_zero,Pi.zero_apply] using hz'

#print axioms kernel_contact
#print axioms zero_aux
end ProximityPrize.SubmissionBinaryLower.B6402PrimarySystem
