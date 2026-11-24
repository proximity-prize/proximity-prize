import ProximityPrize.SubmissionLower.ZREcUaa
import ProximityPrize.SubmissionLower.ZN0wDed
import ProximityPrize.SubmissionLower.ZY18Mqc
import ProximityPrize.SubmissionLower.ZpWezjb
set_option Elab.async false
set_option autoImplicit true
set_option maxHeartbeats 1000000
namespace qnODzma
noncomputable section
open P6 (K)
open P6_6 (Messages gZ)
open P6_6_7 qAzl5me Finset
open aR (ao Shape embed bf)
open dN (kC bC)
open agL (BV EY)
open rW MvPolynomial
open scoped Polynomial
open private cbH from ProximityPrize.SubmissionLower.ZFx6vEd
open private surface_degree from ProximityPrize.SubmissionLower.ZN0wDed
private theorem mark_capacity {w:P6.I→K} {Γ:Finset K} {s :K→K[X]}
    (hm:Messages w Γ s) {B:kT} {f :aR.af 4} (hf :aYK f B)
    (hd:dimension B=2) (hpoints : ∀ γ∈Γ,rV s γ∈zeroLocus ao B)
    (hpositive :1≤affineDegree (lA B)) :
    (Γ.card:ℚ)≤2*(gZ:ℚ)*affineDegree (lA B) := by
  classical
  have hdeg (γ:K) (hγ:γ∈Γ) : (s γ).natDegree<bf :=
    (hm.degree γ hγ).trans_lt (by decide :gZ<bf)
  have hinj:Set.InjOn (rV s) (Γ:Set K) := by
    intro γ hγ δ hδ heq
    apply hm.distinct hγ hδ
    apply Polynomial.ext
    intro j
    by_cases hj:j<bf
    · exact embed.injective (by
        simpa only [rV,Gp,Polynomial.coeff_map] using congrFun heq ⟨j,hj⟩)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hdeg γ hγ).trans_le (le_of_not_gt hj)),
        Polynomial.coeff_eq_zero_of_natDegree_lt ((hdeg δ hδ).trans_le (le_of_not_gt hj))]
  have hs :=bxh hf.prime hd hdeg hinj hpoints
  have hcap:=P6_6_5.bv5 hm (2*aaL B) (fun i hi=> by
    obtain ⟨D,hcover,hcurves,hpos,htotal⟩:=hs (P6.node i) (w i) hi
    exact (card_le_card hcover).trans
      ((cbH D (hm.mono (filter_subset _ _)) hcurves hpos).trans
        (Nat.mul_le_mul_left 2 htotal)))
  have hdegree :=surface_degree B hf.prime hf.extended_prime hd hf.birational
  have hd₀: (82317:ℚ)*133671+46402≤46402*(2*(gZ:ℚ)) := by
    exact_mod_cast (show 82317*133671+46402≤46402*(2*gZ) by decide)
  let d:=affineDegree (lA B)
  have hd₁:2*(aaL B:ℚ)≤133671*d :=
    (mul_le_mul_of_nonneg_left (dVb B) (by norm_num)).trans hdegree
  apply le_of_mul_le_mul_left _ (by norm_num : (0:ℚ)<46402)
  calc
    _≤82317*(2*(aaL B:ℚ))+46402 := by exact_mod_cast hcap
    _≤82317*(133671*d)+46402*d :=
      add_le_add (mul_le_mul_of_nonneg_left hd₁ (by norm_num))
        (le_mul_of_one_le_right (by norm_num) hpositive)
    _=(82317*133671+46402)*d:= by ring
    _≤(46402*(2*(gZ:ℚ)))*d :=
      mul_le_mul_of_nonneg_right hd₀ (affineDegree_nonneg _)
    _ = _:=mul_assoc ..
private theorem same_family {C:Context} {B D:kT} {i j:Fin C.n}
    (hB:aYK (C.f i) B) (hD:aYK (C.f j) D)
    (he :lA B=lA D) :B=D:= by
  obtain ⟨a,hg,hs⟩:=hB.regular
  exact P0_9_6_3.freshImage_injective (C.f i) ⟨hB.prime,⟨a,hg,hs⟩⟩
    ⟨hD.prime,⟨a,he ▸ hg,he ▸ hs⟩⟩ he
private theorem scale (r q:Shape) {x :ℕ} (h:x≤2*gZ*r.b*q.b) :
    (feeScale :ℤ)*x≤fresh32 r q:= by
  have hi: (x :ℤ)≤2*(gZ:ℤ)*r.b*q.b:= by exact_mod_cast h
  unfold fresh32
  calc
    _≤(feeScale :ℤ)*(2*(gZ:ℤ)*r.b*q.b) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _:= by simp only [Nat.cast_mul,Nat.cast_ofNat]; ring
private def Witness (C:Context) (R G:aR.af 4) (ell:ℕ)
    (A:SurfaceAssignment C R G) (γ:K) (D:kT) :Prop :=
  (∃ i,Family C i γ D)∧dimension D =2∧(kC R G).IsMinimalPrime (lA D) ∧
    (∀ a,EY a<genericOrder R (A.aI γ)→bC (BV a R)∈lA D) ∧
    (∀ a,EY a<ell→bC (BV a G)∈lA D)
theorem proof :qAzl5me.c4 := by
  classical
  intro C R G ell cs h A T hT hw
  let J:=kC R G
  have hsub:T⊆C.Δ:= fun γ hγ=>(mem_filter.mp (hT hγ)).1
  have hR₀:=WI.agr h.factor.1.ne_zero
  have hrel :=lB.amo R G h.factor.1 h.proper
  have hex (γ:K) (hγ:γ∈T) : ∃ D,Witness C R G ell A γ D:= by
    obtain ⟨i,_,D,_,hf,hd,hp,hR,hG⟩:=hw γ hγ
    exact ⟨D,⟨i,hf⟩,hd,hp,hR,hG⟩
  let B (γ:K) :kT:=if hγ:γ∈T then Classical.choose (hex γ hγ) else ⊥
  have hb (γ:K) (hγ:γ∈T) :Witness C R G ell A γ (B γ) := by
    simpa only [B,dite_eq_left hγ] using Classical.choose_spec (hex γ hγ)
  let L:=T.image B
  let RS (D:kT) :=T.filter (fun γ=>B γ=D)
  let weight (P:n8) :=(Yg J P:ℚ)*affineDegree P
  have local_le (D:kT) (hD:D∈L) :
      ∑ γ∈RS D,((ell*genericOrder R (A.aI γ) :ℕ) :ℚ) ≤
        (2*(gZ:ℚ))*weight (lA D) := by
    obtain ⟨γ₀,hγ₀,he⟩:=mem_image.mp hD
    obtain ⟨⟨i,hm,_,_⟩,hd,hp,_,_⟩:=hb γ₀ hγ₀
    rw [he] at hm hd hp
    have hpos :=WI.cJU _ hp.isPrime.ne_top
      (Dr.aQG hR₀ hrel hp)
    have hΓ:RS D⊆C.Δ:=(filter_subset _ _).trans hsub
    have hcard:=mark_capacity (C.messages.mono hΓ) hm hd
      (fun γ hγ=> by
        obtain ⟨hγ,hEq⟩:=mem_filter.mp hγ
        obtain ⟨_,_,_,hx⟩:=(hb γ hγ).1
        exact hEq ▸ hx) hpos
    let m:=Yg J (lA D)
    have hprod (γ:K) (hγ:γ∈RS D) :
        ell*genericOrder R (A.aI γ)≤ m:= by
      obtain ⟨hγ,hEq⟩:=mem_filter.mp hγ
      obtain ⟨_,_,hp',hR,hG⟩:=hb γ hγ
      rw [hEq] at hp' hR hG
      exact dlP hR₀ hrel hp' hR hG
    have hm0: (0:ℚ)≤ m:= by positivity
    calc
      _ ≤ ∑ γ∈RS D,(m:ℚ) :=sum_le_sum fun γ hγ=> by exact_mod_cast hprod γ hγ
      _=((RS D).card:ℚ)*m:= by simp
      _≤(2*(gZ:ℚ)*affineDegree (lA D))*m :=
        mul_le_mul_of_nonneg_right hcard hm0
      _ = _:= by dsimp only [weight,m]; ring
  have hinj (D:kT) (hD:D∈L) (E :kT) (hE :E∈L)
      (he :lA D =lA E) :D =E := by
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hD
    obtain ⟨δ,hδ,rfl⟩:=mem_image.mp hE
    obtain ⟨_,hB,_⟩:=(hb γ hγ).1
    obtain ⟨_,hD,_⟩:=(hb δ hδ).1
    exact same_family hB hD he
  have hbudget: (∑ γ∈T,ell*genericOrder R (A.aI γ) :ℕ) ≤
      2*gZ*(firstSlot C R cs).b*(cutterBody C ell).b:= by
    suffices hq : ∑ γ∈T,((ell*genericOrder R (A.aI γ) :ℕ) :ℚ) ≤
        2*(gZ:ℚ)*(firstSlot C R cs).b*(cutterBody C ell).b by
      exact_mod_cast hq
    calc
      _ = ∑ D∈L,∑ γ∈RS D,((ell*genericOrder R (A.aI γ) :ℕ) :ℚ) :=
        (sum_fiberwise_of_maps_to (fun _ hγ=>mem_image_of_mem B hγ) _).symm
      _ ≤ ∑ D∈L,(2*(gZ:ℚ))*weight (lA D) :=
        sum_le_sum local_le
      _=(2*(gZ:ℚ)) * ∑ P∈L.image lA,weight P:= by
        rw [mul_sum,sum_image (fun D hD E hE=>hinj D hD E hE)]
      _≤(2*(gZ:ℚ)) * ∑ P∈J.minimalPrimesFinset,weight P:= by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum_of_subset_of_nonneg
        · intro P hP
          obtain ⟨_,hD,rfl⟩:=mem_image.mp hP
          obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hD
          exact Ideal.mem_minimalPrimesFinset.mpr (hb γ hγ).2.2.1
        · exact fun P _ _=>mul_nonneg (by positivity) (affineDegree_nonneg P)
      _≤_:= by
        rw [mul_assoc (2*(gZ:ℚ))]
        exact mul_le_mul_of_nonneg_left (cycle_budget h) (by positivity)
  simpa only [aid,Nat.cast_sum,Nat.cast_mul,← mul_sum,mul_assoc] using
    scale (firstSlot C R cs) (cutterBody C ell) hbudget
end
end qnODzma
