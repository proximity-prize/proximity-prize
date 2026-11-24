import ProximityPrize.SubmissionLower.Z3vxfLe
set_option Elab.async false
set_option autoImplicit true
namespace qhonTAe
open qHde8fc MvPolynomial
open fP (cF)
open GN (Interpolant ord weights b9 mC BD)
open private B C₂ F nY sO GN.const_mem mul_bounded B0 y4 lU abl aEi from ProximityPrize.SubmissionLower.B0
open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
set_option maxHeartbeats 1000000
private def u7:Interpolant:=C 168 - C 3*B - C 2*C₂-F
private def n7 (t:ℕ) :Interpolant:=C₂+C 2*B+C ((t:Ground) - 112)
private def ur (t:ℕ) :Interpolant:=C (168-(t:Ground)) - C 3*B - C 2*C₂
private theorem zA:u7∈Bounded 3:= by
  have ⟨hb,hc,hf⟩:=lU
  exact (Bounded 3).sub_mem
    ((Bounded 3).sub_mem ((Bounded 3).sub_mem (GN.const_mem _ _)
      (restrictWeightedDegree_mono weights (by decide :1≤3) (abl 3 hb)))
      (restrictWeightedDegree_mono weights (by decide :2≤3) (abl 2 hc))) hf
private theorem value_mem (t:ℕ) :n7 t∈Bounded 2 := by
  exact (Bounded 2).add_mem ((Bounded 2).add_mem lU.2.1
    (restrictWeightedDegree_mono weights (by decide :1≤2) (abl 2 lU.1)))
    (GN.const_mem _ _)
private theorem top_mem (t:ℕ) :ur t∈Bounded 2 := by
  exact (Bounded 2).sub_mem ((Bounded 2).sub_mem (GN.const_mem _ _)
    (restrictWeightedDegree_mono weights (by decide :1≤2) (abl 3 lU.1)))
    (abl 2 lU.2.1)
private theorem Ep (e :aY) :b9 e.val u7=(ord e.val :Ground) := by
  have h:=e.property
  rw [cF] at h
  have hc:=congrArg (fun n:ℕ=>(n:Ground)) h
  push_cast at hc ⊢
  simp [u7,B,C₂,F,ord]
  linear_combination -3*hc
private theorem E4 (e :aY) {t:ℕ} (ht:ord e.val=t) :
    b9 e.val (n7 t)=(e.val 0:Ground) := by
  have h:=e.property
  rw [cF] at h
  have hc:=congrArg (fun n:ℕ=>(n:Ground)) h
  have ht' := congrArg (fun n:ℕ=>(n:Ground)) ht
  simp only [ord] at ht'
  push_cast at hc ht'
  simp [n7,B,C₂]
  linear_combination 2*hc - ht'
private theorem Da (e :aY) {t:ℕ} (ht:ord e.val=t) :
    b9 e.val (ur t)=(e.val 3:Ground) := by
  have h:=e.property
  rw [cF] at h
  have hc:=congrArg (fun n:ℕ=>(n:Ground)) h
  have ht' := congrArg (fun n:ℕ=>(n:Ground)) ht
  simp only [ord] at ht'
  push_cast at hc ht'
  simp [ur,B,C₂]
  linear_combination -3*hc+ht'
theorem interpolate (e :aY) (ht:ord e.val≤56) :
    ∃ P:Interpolant,
      P∈Bounded (cutBudget e)∧Ak e P:= by
  classical
  let t:=ord e.val
  let a :=e.val 0
  let f :=e.val 3
  let d:=e.val 2/2
  let A:=C (d:Ground)-(B - C (e.val 1 :Ground))
  let H :=C (d:Ground)-(ur t - C (f :Ground))
  let L := ∏ i∈Finset.Ioc t 56,(u7 - C (i:Ground))
  let M := ∏ i∈Finset.range a,(n7 t - C (i:Ground))
  let P:=L*M*sO A H d
  have hd:d≤56:= by have :=Finsupp.le_degree 2 e.val; omega
  have ha :a≤56:= by have :=Finsupp.le_degree 0 e.val; omega
  have hA:A∈Bounded 1 :=
    (Bounded 1).sub_mem (GN.const_mem _ _) ((Bounded 1).sub_mem lU.1 (GN.const_mem _ _))
  have hH :H∈Bounded 2 :=
    (Bounded 2).sub_mem (GN.const_mem _ _) ((Bounded 2).sub_mem (top_mem t) (GN.const_mem _ _))
  have hL:L∈Bounded (3*(56 - t)) := by
    simpa only [L,Nat.card_Ioc,Nat.mul_comm] using
      aEi 3 (Finset.Ioc t 56) _ (fun i _=>(Bounded 3).sub_mem zA (GN.const_mem _ _))
  have hM:M∈Bounded (2*a) := by
    simpa only [M,Finset.card_range,Nat.mul_comm] using aEi 2 (Finset.range a) _
      (fun i _=>(Bounded 2).sub_mem (value_mem t) (GN.const_mem _ _))
  refine ⟨P,mul_bounded (mul_bounded hL hM) (B0 hA hH d),?_,?_⟩
  · have hL' : b9 e.val L≠0:= by
      simp only [L,map_prod,map_sub,mC,Ep,Finset.prod_ne_zero_iff]
      exact fun i hi=>sub_ne_zero.mpr (cEo ht (Finset.mem_Ioc.mp hi).2
        (Nat.ne_of_lt (Finset.mem_Ioc.mp hi).1))
    have hM' : b9 e.val M≠0:= by
      simp only [M,map_prod,map_sub,mC,E4 e (t:=t) rfl,Finset.prod_ne_zero_iff]
      exact fun i hi=>sub_ne_zero.mpr (cEo ha ((Finset.mem_range.mp hi).le.trans ha)
        (Nat.ne_of_gt (Finset.mem_range.mp hi)))
    have hr :=y4 A H e.val d 0
      (by simp [A,B]) (by simp [H,Da e (t:=t) rfl,f]) d
    rw [show b9 e.val P=b9 e.val L*b9 e.val M *
      b9 e.val (sO A H d) by simp [P],hr]
    exact mul_ne_zero (mul_ne_zero hL' hM') (by simpa [nY,Polynomial.coeff_one_add_X_pow] using factorial_ne_zero hd)
  · intro v hvLive hkey
    have htop:=((abJ _).mp hvLive).1
    have he :=e.property
    have hv :=v.property
    rw [cF] at he hv
    have nS (w:aY) :dZ w =
        (((56+ord w.val)*57+w.val 3)*57+w.val 2)*57+w.val 1 := by
      simp only [dZ,show cP (aD w.val)=56+ord w.val from nG w]
    rw [nS,nS] at hkey
    have ht' : t≤ord v.val := by omega
    by_cases h:t<ord v.val
    · have hL' : b9 v.val L=0:= by
        simp only [L,map_prod]
        apply Finset.prod_eq_zero (i:=ord v.val) (Finset.mem_Ioc.mpr ⟨h,htop⟩)
        simp only [map_sub,mC,Ep,sub_self]
      simp [P,hL']
    have ht' : ord v.val=t:= by omega
    by_cases hal:v.val 0<a
    · have hM' : b9 v.val M=0:= by
        simp only [M,map_prod]
        apply Finset.prod_eq_zero (i:=v.val 0) (Finset.mem_range.mpr hal)
        simp only [map_sub,mC,E4 v ht',sub_self]
      simp [P,hM']
    have hf :f<v.val 3:= by dsimp [t,a,f,ord] at *; omega
    let u:=v.val 0-a
    let j:=v.val 3 - f
    have huj:u+j≤d:= by dsimp [u,j,d,t,a,f,ord] at *; omega
    let s :=d-(u+j)
    have hb: (v.val 1 :Ground)-(e.val 1 :Ground)=2*(u:Ground)+j:= by
      have eq :v.val 1=e.val 1+2*u+j:= by dsimp [u,j,t,a,f,ord] at *; omega
      rw [eq]
      push_cast
      ring
    have hj: (v.val 3:Ground)-(f :Ground)=(j:Ground) := by
      rw [Nat.cast_sub hf.le]
    have hs : (d:Ground)=(s :Ground)+u+j:= by
      dsimp [s]
      rw [Nat.cast_sub huj,Nat.cast_add]
      ring
    have hr :=y4 A H v.val s u
      (by
        simp only [A,B,map_sub,mC,BD]
        change (d:Ground)-((v.val 1 :Ground)-(e.val 1 :Ground))= _
        rw [hb,hs]
        ring)
      (by simp only [H,map_sub,mC,Da v ht']; rw [hj,hs]; ring) d
    have hlt:s+u<d:= by dsimp [s,j] at *; omega
    have hz :nY ((1+Polynomial.X)^s*(1-Polynomial.X)^u) d=0:= by
      apply mul_eq_zero.mpr
      right
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      calc
        _≤ s*(1+Polynomial.X:Polynomial Ground).natDegree +
            u*(1-Polynomial.X:Polynomial Ground).natDegree :=
          (Polynomial.natDegree_mul_le).trans (Nat.add_le_add
            (Polynomial.natDegree_pow_le ..) (Polynomial.natDegree_pow_le ..))
        _≤ s+u:= by
          have hp: (1+Polynomial.X:Polynomial Ground).natDegree≤1 :=
            (Polynomial.natDegree_add_le 1 Polynomial.X).trans (by simp)
          have hm: (1-Polynomial.X:Polynomial Ground).natDegree≤1 :=
            (Polynomial.natDegree_sub_le 1 Polynomial.X).trans (by simp)
          simpa using Nat.add_le_add (Nat.mul_le_mul_left s hp) (Nat.mul_le_mul_left u hm)
        _<d:=hlt
    simp only [P,map_mul,hr,hz,mul_zero]
end
end qhonTAe
