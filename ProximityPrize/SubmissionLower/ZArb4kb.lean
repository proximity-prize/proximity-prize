import ProximityPrize.SubmissionLower.ZCIcQjc
import ProximityPrize.SubmissionLower.ZzOuVbd
import ProximityPrize.SubmissionLower.ZFx6vEd
set_option Elab.async false
set_option autoImplicit true
set_option maxHeartbeats 1000000
namespace qXTnXJe
noncomputable section
open P6 (K node)
open P6_6 (Messages gZ mW)
open P6_6_5 (Fb a5C)
open aR (ao embed extend bf)
open oR (qg ang Rr)
open B7 (jo Gp GZ)
open rW (rV bxh dVb)
open Finset MvPolynomial
open scoped BigOperators Polynomial
open private bqq from ProximityPrize.SubmissionLower.I
open private b9N from ProximityPrize.SubmissionLower.I
open private cbH from ProximityPrize.SubmissionLower.ZFx6vEd
private theorem gxH {w Γ s} {d:ℕ} (h:Messages w Γ s) {P:Ideal jo}
    (hP:P.IsPrime) (hdim: (affineHilbertPolynomial P).natDegree=2)
    (hpoints : ∀ γ∈Γ,Gp (extend (s γ))∈zeroLocus ao P)
    (hd:2*affineDegree P≤(d:ℚ)) :
    ang w Γ s d:= by
  classical
  have hdegree (γ:K) (hγ:γ∈Γ) : (s γ).natDegree<bf :=
    (h.degree γ hγ).trans_lt (by decide :gZ<bf)
  have hinj:Set.InjOn (rV s) (Γ:Set K) := by
    intro γ hγ η hη heq
    apply h.distinct hγ hη
    apply Polynomial.ext
    intro j
    by_cases hj:j<bf
    · have hcoeff :=congrFun heq ⟨j,hj⟩
      exact embed.injective (by
        simpa only [rV,rW.Gp,Polynomial.coeff_map] using hcoeff)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hdegree γ hγ).trans_le (le_of_not_gt hj)),
        Polynomial.coeff_eq_zero_of_natDegree_lt ((hdegree η hη).trans_le (le_of_not_gt hj))]
  have hs :=bxh hP hdim hdegree hinj hpoints
  apply b9N
  intro i hi
  obtain ⟨C,hC,hc,hpos,hdeg⟩:=hs (node i) (w i) hi
  have hH :=h.mono (filter_subset (fun γ=>(s γ).eval (node i)=w i) Γ)
  have hcount:=(card_le_card hC).trans (cbH C hH hc hpos)
  have hcap:2*C.total≤d:= by
    exact_mod_cast (mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr hdeg).trans
      (dVb P)) (by decide : (0:ℚ)≤2)).trans hd
  exact hcount.trans hcap
theorem proof :P6_6_5.c2 := by
  classical
  intro w Γ s hm v _ n f hf hcover
  let part (i:Fin n) :=Γ.filter fun γ=>qg 2 (f i) (extend (s γ))∧Fb (f i)
  let cap (i:Fin n) :=gZ*(f i).totalDegree
  have hsub (i:Fin n) :part i⊆Γ:=filter_subset _ _
  have hlocal (i:Fin n) :ang w (part i) s (cap i) := by
    by_cases hi:Fb (f i)
    · have htop: (f i).degreeOf 2<K1.p :=
        ((single_le_sum (f := fun j=>(f j).degreeOf 2) (fun _ _=>Nat.zero_le _)
          (mem_univ i)).trans (hf.top.trans (a5C v))).trans_lt (by decide :28<K1.p)
      obtain ⟨P,hp,hsupport,hall⟩:=dIK _ (hf.irreducible i) (hf.positive i) htop (hf.weight i) hi
      obtain ⟨hdim,hdeg⟩:=adr _ _ _ hp hsupport
      apply gxH (hm.mono (hsub i)) hp.prime hdim
      · intro γ hγ
        have hγΓ:=hsub i hγ
        exact hall _ (Polynomial.natDegree_map_le.trans (hm.degree γ hγΓ))
          (mem_filter.mp hγ).2.1
      · have hle : ((GZ (f i)).totalDegree :ℚ)≤((f i).totalDegree :ℚ) :=
          Nat.cast_le.mpr (bqq (f i))
        simpa only [cap,Nat.cast_mul,Nat.cast_ofNat] using
          hdeg.trans (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg gZ))
    · have hempty :part i = ∅ := by simp [part,hi]
      rw [hempty]
      exact ⟨∅,by simp,by simp⟩
  let C:Rr w Γ s :=⟨n,part,cap,hsub,hlocal⟩
  refine ⟨C,?_,?_,?_⟩
  · intro γ hγ
    obtain ⟨i,hi,hwhole⟩:=hcover γ hγ
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨hγ,hi,hwhole⟩⟩
  · change n≤(mW v).b
    calc
      n = ∑ _i:Fin n,1 := by simp
      _ ≤ ∑ i,(f i).totalDegree :=sum_le_sum fun i _ =>
        (hf.positive i).trans_le (degreeOf_le_totalDegree _ _)
      _≤(mW v).b:=hf.total
  · change (∑ i,gZ*(f i).totalDegree)≤gZ*(mW v).b
    rw [← mul_sum]
    exact Nat.mul_le_mul_left _ hf.total
end
end qXTnXJe
