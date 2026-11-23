import ProximityPrize.SubmissionLower.ZucFfdd
import ProximityPrize.SubmissionLower.ZU4mhUb
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
namespace q7twcKc
noncomputable section
open Finset MvPolynomial
open P6_6 (mV)
open P6_6_7
open qAzl5me (active aid curveCap memberDegree)
open aR (extend embed)
open rW (kT dimension rV Gp aaL aT4
  dVb cIN P6)
open scoped BigOperators
private theorem count {C:Context} {F:Finset P6.K} {B:kT}
    (hm:F⊆C.Δ) (hp:B.IsPrime) (hd:dimension B=1) (hn:F.Nonempty)
    (hpt : ∀ γ∈F,Gp (extend (C.s γ))∈zeroLocus aR.ao B) :
    (mV:ℚ)*F.card≤((P6.t:ℚ)+mV)*affineDegree B:= by
  have h:=C.messages.mono hm
  have hde (γ:P6.K) (hγ:γ∈F) : (C.s γ).natDegree<aR.bf :=
    (Nat.lt_succ_of_le (h.degree γ hγ)).trans (by decide)
  have hi:Set.InjOn (rV C.s) (F:Set P6.K) := by
    intro α ha β hb he
    apply h.distinct ha hb
    apply Polynomial.ext
    intro n
    by_cases hn:n<aR.bf
    · have hcoord:=congrFun he ⟨n,hn⟩
      exact embed.injective (by simpa only [rV,Gp,Polynomial.coeff_map] using hcoord)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hde α ha).trans_le (Nat.le_of_not_lt hn)),
        Polynomial.coeff_eq_zero_of_natDegree_lt ((hde β hb).trans_le (Nat.le_of_not_lt hn))]
  have hc:=P6_6_5.bv5 h (aaL B) fun j =>
    cIN hp hd hde hi hpt (P6.node j) (C.w j)
  obtain ⟨γ,hγ⟩:=hn
  have hpos :=aT4 hp ⟨γ,P6.mpr ⟨hγ,hpt γ hγ⟩⟩
  have hb:46402*F.card≤(82317+46402)*aaL B:= by omega
  change (46402 :ℚ)*F.card≤(82317+46402)*affineDegree B
  exact (by exact_mod_cast hb: (46402 :ℚ)*F.card ≤
    (82317+46402)*(aaL B:ℚ)).trans
      (mul_le_mul_of_nonneg_left (dVb B) (by positivity))
theorem proof :qAzl5me.c3:= by
  classical
  intro C R G ell cs h A T ha hT
  have hw (γ:T) : ∃ B,bQG C cs (A.aI γ.val) γ.val B:= by
    obtain ⟨i,a,B,hs,hf,hd,hc,hpoint,_⟩:=hT γ.val γ.property
    exact ⟨B,i,a,hs,hf,hd,hc,hpoint⟩
  let B:T→kT:= fun γ=>Classical.choose (hw γ)
  let F:=T.attach.image B
  let part:= fun D =>T.attach.filter (fun γ=>B γ=D)
  let u:= fun γ:P6.K=>ell*genericOrder R (A.aI γ)
  have hsrc {D:kT} {γ:T} (hγ:γ∈part D) :
      bQG C cs (A.aI γ.val) γ.val D :=
    (Finset.mem_filter.mp hγ).2 ▸ Classical.choose_spec (hw γ)
  have hmax (D:kT) (hD:D∈F) :
      ∃ γ∈part D,∀ δ∈part D,u δ.val≤u γ.val := by
    obtain ⟨δ,hδ,hDB⟩:=Finset.mem_image.mp hD
    obtain ⟨γ,hγ,he⟩:=(part D).exists_mem_eq_sup
      ⟨δ,Finset.mem_filter.mpr ⟨hδ,hDB⟩⟩ (u ∘ Subtype.val)
    refine ⟨γ,hγ,fun e he' => ?_⟩
    have hw:=Finset.le_sup (f :=u ∘ Subtype.val) he'
    rw [he] at hw
    exact hw
  let rep:= fun D =>if hD:D∈F then (Classical.choose (hmax D hD)).val else (0:P6.K)
  have hrep (D:kT) (hD:D∈F) :
      rep D∈active C R G ell cs A∧bQG C cs (A.aI (rep D)) (rep D) D:= by
    rw [show rep D =(Classical.choose (hmax D hD)).val by simp [rep,hD]]
    exact ⟨ha (Classical.choose (hmax D hD)).property,hsrc (Classical.choose_spec (hmax D hD)).1⟩
  have hfiber (D:kT) (hD:D∈F) :
      (∑ γ∈part D,(mV:ℚ)*(u γ.val :ℚ)) ≤
        ((P6.t:ℚ)+mV)*((u (rep D) :ℚ)*affineDegree D) := by
    let L:=(part D).image Subtype.val
    have hm:L⊆C.Δ:= by
      intro γ hγ
      obtain ⟨δ,_,rfl⟩:=Finset.mem_image.mp hγ
      exact (Finset.mem_filter.mp (ha δ.property)).1
    have hn:L.Nonempty :=
      ⟨rep D,Finset.mem_image.mpr ⟨Classical.choose (hmax D hD),
        (Classical.choose_spec (hmax D hD)).1,by simp [rep,hD]⟩⟩
    obtain ⟨_,_,_,hf,hd,_⟩:=(hrep D hD).2
    have hc:=count hm hf.1.prime hd hn (by
      intro γ hγ
      obtain ⟨δ,hδ,rfl⟩:=Finset.mem_image.mp hγ
      obtain ⟨_,_,_,hh,_⟩:=hsrc hδ
      exact hh.2.2)
    calc
      _ ≤ ∑ γ∈part D,(mV:ℚ)*(u (rep D) :ℚ) := by
        apply Finset.sum_le_sum
        intro γ hγ
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hle :=(Classical.choose_spec (hmax D hD)).2 γ hγ
        simp only [rep,dite_eq_left hD]
        exact_mod_cast hle
      _=(u (rep D) :ℚ)*((mV:ℚ)*L.card) := by
        rw [Finset.sum_const,nsmul_eq_mul,Finset.card_image_of_injective _ Subtype.val_injective]
        ring
      _≤_:= by
        rw [mul_left_comm ((P6.t:ℚ)+mV)]
        exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hgeom:=membership_sum h A F rep hrep
  have hsum: (mV:ℚ) * ∑ γ∈T,(u γ:ℚ) ≤
      ((P6.t:ℚ)+mV)*(((firstSlot C R cs).b*(cutterBody C ell).b *
        (P6_6.weightedChart (P6_6.bf+1) (chartBody C R cs)).b:ℕ) :ℚ) := by
    calc
      _ = ∑ γ∈T.attach,(mV:ℚ)*(u γ.val :ℚ) := by
        rw [Finset.mul_sum]
        exact (Finset.sum_attach T (fun γ=>(mV:ℚ)*(u γ:ℚ))).symm
      _ = ∑ D∈F,∑ γ∈part D,(mV:ℚ)*(u γ.val :ℚ) :=
        (Finset.sum_fiberwise_of_maps_to (fun γ hγ=>Finset.mem_image_of_mem B hγ) _).symm
      _ ≤ ∑ D∈F,((P6.t:ℚ)+mV)*((u (rep D) :ℚ)*affineDegree D) :=
        Finset.sum_le_sum hfiber
      _≤_:= by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hgeom (by positivity)
  have hi: (mV:ℤ) * ∑ γ∈T,(u γ:ℤ) ≤
      ((P6.t:ℤ)+mV)*memberDegree (chartBody C R cs) (firstSlot C R cs) (cutterBody C ell) := by
    unfold memberDegree
    exact_mod_cast hsum
  simpa only [aid,feeScale,curveCap,u,Nat.cast_mul,Nat.cast_ofNat,
    ← Finset.mul_sum,mul_assoc] using mul_le_mul_of_nonneg_left hi (show (0:ℤ)≤32 by decide)
end
end q7twcKc
