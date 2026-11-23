import ProximityPrize.SubmissionLower.B0
set_option Elab.async false
open _root_ renaming Int.cast_mul → zkl, Int.cast_natCast → z0T, Int.cast_one → z2d, Nat.mul_le_mul_left → zBI, Polynomial → zM1, Polynomial.natDegree_add_le → zbE, Polynomial.natDegree_pow_le → zQ8, Polynomial.natDegree_sub_le → z9w
set_option autoImplicit true
namespace qDoysbd
open vF MvPolynomial
open GN (Interpolant weights)
open scoped BigOperators
open private aEi GN.const_mem nY a8i aP5 from ProximityPrize.SubmissionLower.B0
noncomputable section
private def cU {R:Type*} [CommRing R] (n:ℕ) (x :R) :R :=
  ∏ i∈Finset.range n,(x-(i:R))
private theorem vT {R:Type*} [CommRing R] {n i:ℕ} (hi:i<n) :
    cU n (i:R)=0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr hi) (sub_self _)
private theorem fall_bound {w:ℕ} {p:Interpolant}
    (h:p∈restrictWeightedDegree weights w) (n:ℕ) :
    cU n p∈restrictWeightedDegree weights (n*w) := by
  unfold cU
  simpa only [Finset.card_range] using aEi w (Finset.range n)
    (fun i=>p-(i:Interpolant)) (fun i _=>(restrictWeightedDegree weights w).sub_mem h
      (by simpa only [map_natCast] using GN.const_mem w (i:Ground)))
private theorem ajh (n i:ℕ) : (n.descFactorial i:Ground)=cU i (n:Ground) := by
  by_cases hi:i≤n
  · rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod,cU]
    exact Finset.prod_congr rfl fun j hj=>Nat.cast_sub (by have :=Finset.mem_range.mp hj; omega)
  · have hlt:n< i:= by omega
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt,Nat.cast_zero,vT hlt]
private theorem Nm (φ:Interpolant →ₐ[Ground] Ground) (i:ℕ) (Q:Interpolant) :
    φ (cU i Q)=cU i (φ Q) := by simp [cU]
end
private def aaJ (s u:ℕ) :ℕ→ℤ×ℤ
  | 0=>(1,(s :ℤ) - u)
  | n+1 =>
    let (a,b) :=aaJ s u n
    (b,((s :ℤ) - u)*b+((n:ℤ)-(s+u:ℕ))*(n+1)*a)
noncomputable section
private theorem avN (s u:ℕ) (n:ℕ) :
    let Q:zM1 Ground :=(1+Polynomial.X)^s*(1-Polynomial.X)^u
    ((aaJ s u n).1 :Ground)=nY Q n ∧
      ((aaJ s u n).2 :Ground)=nY Q (n+1) := by
  induction n with
  | zero =>
    have h:=aP5 s u
    simp only [aaJ,z2d,Int.cast_sub,z0T]
    exact ⟨h.1.symm,h.2.symm⟩
  | succ n ih =>
    change _∧_ at ih
    rcases hp:aaJ s u n with ⟨a,b⟩
    rw [hp] at ih
    simp only [aaJ,hp,Int.cast_add,Int.cast_sub,zkl,z2d,
      z0T,Nat.cast_add]
    refine ⟨ih.2,?_⟩
    rw [ih.1,ih.2,a8i s u n]
private theorem aEI {s u k :ℕ} (h:s+u<k) :
    nY ((1+Polynomial.X)^s*(1-Polynomial.X)^u:zM1 Ground) k=0:= by
  rw [nY,Polynomial.coeff_eq_zero_of_natDegree_lt,mul_zero]
  calc
    _≤ s*(1+Polynomial.X:zM1 Ground).natDegree +
        u*(1-Polynomial.X:zM1 Ground).natDegree :=
      Polynomial.natDegree_mul_le.trans (Nat.add_le_add
        (zQ8 ..) (zQ8 ..))
    _≤ s+u:= by
      have hp: (1+Polynomial.X:zM1 Ground).natDegree≤1 :=
        (zbE 1 Polynomial.X).trans (by simp)
      have hm: (1-Polynomial.X:zM1 Ground).natDegree≤1 :=
        (z9w 1 Polynomial.X).trans (by simp)
      simpa using Nat.add_le_add (zBI s hp) (zBI u hm)
    _<k :=h
end
private def factorials :ℕ:=0x8eeae81b84c7f27e080fde64ff052540000000000392ac33e351cc7659cd325c1ff9ba8800000000001774015499125eee9c3c5e4275fe380000000000009e0008f68df506477ada0f38fff4000000000000044530acb7ba83a111287cf3b3e4000000000000001e5dcbe8a8bc8b95cf58cde1710000000000000000de1bc4d19efcac82445da75b00000000000000000688589cc0e9505e2f2fee5580000000000000000032ad5a155c6748ac18b9a580000000000000000001956ad0aae33a4560c5cd2c0000000000000000000d13f6370f96865df5dd54000000000000000000006f99461a1e9e1432dcb60000000000000000000003d925ba47ad2cd59dae0000000000000000000000232f0fcbb3e62c33588000000000000000000000014d9849ea37eeac918000000000000000000000000cd4a0619fb0907bc000000000000000000000000083629343d3dcd1c0000000000000000000000000057970cd7e293368000000000000000000000000003ceea4c2b3e0d80000000000000000000000000002c5077d36b8c4000000000000000000000000000021c3677c82b4000000000000000000000000000001b02b93068900000000000000000000000000000016beecca7300000000000000000000000000000001437eeecd800000000000000000000000000000001307777580000000000000000000000000000000013077775800000000000000000000000000000000144c3b2800000000000000000000000000000000017328cc00000000000000000000000000000000001c8cfc0000000000000000000000000000000000026115000000000000000000000000000000000000375f0000000000000000000000000000000000000589800000000000000000000000000000000000009d8000000000000000000000000000000000000013b000000000000000000000000000000000000002d0000000000000000000000000000000000000007800000000000000000000000000000000000000180000000000000000000000000000000000000006000000000000000000000000000000000000000200000000000000000000000000000000000000010000000000000000000000000000000000000001
private def fastFact (n:ℕ) :ℕ :=
  if n≤40 then (factorials >>> (160*n)) % 2^160 else n.factorial
private theorem fastFact_eq (n:ℕ) :fastFact n=n.factorial:= by
  by_cases h:n≤40
  · interval_cases n <;> rfl
  · exact ite_eq_right h
private def fastFall (n i:ℕ) :ℕ :=
  if i≤n then fastFact n/fastFact (n-i) else 0
private theorem fastFall_eq (n i:ℕ) :fastFall n i=n.descFactorial i:= by
  by_cases h:i≤n
  · simp only [fastFall,ite_eq_left h,fastFact_eq,Nat.descFactorial_eq_div h]
  · simp only [fastFall,ite_eq_right h,Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge h)]
private def bG5 (s u k :ℕ) :ℤ :=
  let j:=s+u - k
  if j≤k then (-1)^u*(↑(fastFact k/fastFact j) :ℤ)*(aaJ s u j).1
  else (aaJ s u k).1
noncomputable section
private theorem bgG {P:zM1 Ground} (h:P.natDegree≤1) (n:ℕ) :
    (P^n).reflect n=P.reflect 1^n:= by
  induction n with
  | zero=>simp
  | succ n ih =>
    rw [pow_succ,Polynomial.reflect_mul _ _ (by simpa using Polynomial.natDegree_pow_le_of_le n h) h,
      ih,pow_succ]
private theorem fVl (s u k :ℕ) (hk :k≤ s+u) :
    let Q:zM1 Ground :=(1+Polynomial.X)^s*(1-Polynomial.X)^u
    Q.coeff k=(-1 :Ground)^u*Q.coeff (s+u-k) := by
  let P:zM1 Ground :=1+Polynomial.X
  let R:zM1 Ground :=1-Polynomial.X
  have hp:P.natDegree≤1 :=(zbE _ _).trans (by simp)
  have hr :R.natDegree≤1 :=(z9w _ _).trans (by simp)
  have hP:P.reflect 1=P:= by simp [P,add_comm]
  have hR:R.reflect 1 = -R:= by simp [R,neg_sub]
  have he : (P^s*R^u).reflect (s+u)=Polynomial.C ((-1 :Ground)^u)*(P^s*R^u) := by
    rw [Polynomial.reflect_mul _ _ (by simpa using Polynomial.natDegree_pow_le_of_le s hp)
      (by simpa using Polynomial.natDegree_pow_le_of_le u hr),bgG hp,bgG hr,
      hP,hR,neg_eq_neg_one_mul,mul_pow,map_pow,map_neg,map_one]
    ring
  have hh:=congrArg (fun Q:zM1 Ground=>Q.coeff (s+u-k)) he
  rw [Polynomial.coeff_reflect,Polynomial.revAt_le (Nat.sub_le ..),
    show s+u-(s+u-k)=k by omega,Polynomial.coeff_C_mul] at hh
  exact hh
private theorem eer (s u k :ℕ) (hk :k≤ s+u) :
    let Q:zM1 Ground :=(1+Polynomial.X)^s*(1-Polynomial.X)^u
    (bG5 s u k :Ground)=nY Q k := by
  let j:=s+u-k
  let Q:zM1 Ground :=(1+Polynomial.X)^s*(1-Polynomial.X)^u
  change (bG5 s u k :Ground)=nY Q k
  unfold bG5
  by_cases hj:j≤k
  · rw [ite_eq_left hj,fastFact_eq k,fastFact_eq j,zkl,zkl,Int.cast_pow,Int.cast_neg,
      z2d,z0T,(avN s u j).1]
    have he : (↑(k.factorial/j.factorial) :Ground)*(j.factorial:Ground)=(k.factorial:Ground) := by
      rw [← Nat.cast_mul,Nat.div_mul_cancel (Nat.factorial_dvd_factorial hj)]
    unfold nY
    rw [show ((1+Polynomial.X)^s*(1-Polynomial.X)^u:zM1 Ground)= Q from rfl,
      fVl s u k hk]
    linear_combination ((-1 :Ground)^u*Q.coeff j)*he
  · rw [ite_eq_right hj,(avN s u k).1]
end
end qDoysbd
