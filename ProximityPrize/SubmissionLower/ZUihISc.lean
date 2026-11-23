import ProximityPrize.SubmissionLower.ZikYn6c
import ProximityPrize.SubmissionLower.ZvIWsYa
set_option Elab.async false
open _root_ renaming Fintype.linearCombination_apply → zGl, LinearMap.ker → z83, LinearMap.range → zWl, Module.finrank → zsE, Module.finrank_fintype_fun_eq_card → zvt, Submodule.smul_mem → zc2, Submodule.sum_mem → zo3
set_option autoImplicit true
namespace qnnEPee
noncomputable section
open aR (ao)
open xE (Flag U1 gd oldCount)
open akL (MI KP aDd ahV arP aWa
  Oq alM eAc)
open P6_6_2 (pT oppositeBound latticeAllowance)
open MvPolynomial
open private fTs from ProximityPrize.SubmissionLower.AR
def c1 :Prop :=
  ∀ F:Flag,0<F.lower→F.lower≤1710 →
    z83 (momentMap F (momentColumns F))≤z83 (debitMap F)
def c2 :Prop :=
  ∀ F:Flag,0<F.order→0<F.lower →
    z83 (momentMap F (reducedColumns F)) ≤
      z83 (momentMap F (momentColumns F))
private theorem tail_card (F:Flag) :
    ((tailColumns F).card:ℤ) =
      U1 F.degree F.upper F.cap -
        U1 F.degree (min F.upper (F.order - 1)) F.cap:= by
  have he :tailColumns F=aWa { F with lower :=F.order } := by
    ext e
    simp only [tailColumns,Finset.mem_filter,eAc,arP,
      Set.mem_ofPred_eq,relaxed]
    constructor
    · rintro ⟨⟨hd,_,hu,ht⟩,ho⟩
      exact ⟨hd,ho,hu,ht⟩
    · rintro ⟨hd,ho,hu,ht⟩
      exact ⟨⟨hd,Int.natCast_nonneg _,hu,ht⟩,ho⟩
  rw [he,bjv.proof aw7.proof]
  rfl
private theorem ker_embed (F:Flag) :
    zsE ao (z83 (debitMap F)) ≤
      zsE ao (z83 (KP F)) := by
  let p:=(tailMap F).comp (z83 (debitMap F)).subtype
  have hp (x :z83 (debitMap F)) :p x∈ahV F:= by
    have hrel :p x∈ahV (relaxed F) := by
      show tailMap F x.val∈_
      rw [tailMap,zGl]
      exact zo3 _ fun e _=>zc2 _ _ (tailMonomial_support F e).1
    have hmin:p x∈restrictWeightedOrder Oq F.lower.toNat :=
      (weightedTruncation_eq_zero_iff _ _ _).mp (LinearMap.mem_ker.mp x.2)
    intro e he
    obtain ⟨hd,_,hu,ht⟩:=hrel he
    have hl:=mem_restrictWeightedOrder.mp hmin e he
    exact ⟨hd,by omega,hu,ht⟩
  let g:=p.codRestrict (ahV F) hp
  let f :=g.codRestrict (z83 (KP F)) fun x=> by
    apply LinearMap.mem_ker.mpr
    apply (weightedTruncation_eq_zero_iff _ _ _).mpr
    show alM (tailMap F x.val)∈_
    rw [tailMap,zGl,map_sum]
    exact zo3 _ fun e _=> by
      rw [map_smul]
      exact zc2 _ _ (tailMonomial_support F e).2
  exact LinearMap.finrank_le_finrank_of_injective (f :=f) <| fun a b hab =>
    Subtype.ext (tailMap_injective F
      (congrArg (fun z :z83 (KP F)=>(z.val :MI)) hab))
private theorem rank_le_of_ker_le {V W U:Type} [AddCommGroup V] [AddCommGroup W]
    [AddCommGroup U] [Module ao V] [Module ao W] [Module ao U] [Module.Finite ao V]
    {f :V →ₗ[ao] W} {g:V →ₗ[ao] U} (h:z83 g≤z83 f) :
    zsE ao (zWl f)≤zsE ao (zWl g) := by
  have hker :=Submodule.finrank_mono h
  have hf :=f.finrank_range_add_finrank_ker
  have hg:=g.finrank_range_add_finrank_ker
  omega
private theorem lower_zero (F:Flag) (hl:F.lower≤0) :
    debitMap F=0:= by
  apply LinearMap.ext
  intro a
  change weightedTruncation Oq F.lower.toNat (tailMap F a)=0
  apply (weightedTruncation_eq_zero_iff _ _ _).mpr
  simp [Int.toNat_of_nonpos hl]
private theorem full_count (F:Flag) (hl:F.lower≤0) :
    oldCount F=U1 F.degree F.upper F.cap:= by
  have h:min F.upper (F.lower - 1)<0:=lt_of_le_of_lt (min_le_right _ _) (by omega)
  by_cases hc:F.cap<0
  · simp [oldCount,U1,hc]
  · have h' : min F.upper (F.lower - 1)-3*(F.cap+1)<0:= by omega
    simp [oldCount,U1,gd,hc,h,h']
theorem of_children (h1 :c1) (h2 :c2) :P6_6_2.c2 := by
  intro q r
  let F:=pT q.val r
  change zsE ao (zWl (KP F))≤oppositeBound F
  by_cases ho:F.order≤0
  · simpa [oppositeBound,ho] using le_of_eq (fTs F ho)
  have hker :=ker_embed F
  have hn:=(KP F).finrank_range_add_finrank_ker
  rw [aDd] at hn
  have hc:=bjv.proof aw7.proof F
  have hd:=(debitMap F).finrank_range_add_finrank_ker
  rw [zvt,Fintype.card_coe] at hd
  have ht:=tail_card F
  let below:=U1 F.degree (min F.upper (F.order - 1)) F.cap
  let tail:=U1 F.degree F.upper F.cap - below
  change ((tailColumns F).card:ℤ)=tail at ht
  have hr : (zsE ao (zWl (KP F)) :ℤ) ≤
      oldCount F - tail+(zsE ao (zWl (debitMap F)) :ℤ) := by omega
  unfold oppositeBound
  rw [ite_eq_right ho]
  change _≤(if F.lower≤0 then below.toNat else
    (oldCount F - tail+min (latticeAllowance F) tail).toNat)
  by_cases hl:F.lower≤0
  · rw [ite_eq_left hl]
    have hz :zsE ao (zWl (debitMap F))=0:= by
      simp [lower_zero F hl]
    have he :oldCount F - tail=below:= by
      rw [full_count F hl]
      dsimp [tail]
      omega
    omega
  · rw [ite_eq_right hl]
    have hguard :F.lower≤1710 := by
      change -((r.val :ℤ) - 1710)≤1710
      omega
    let D:=zsE ao (zWl (debitMap F))
    have h₀:D ≤(reducedColumns F).card:= calc
      _≤zsE ao (zWl (momentMap F (momentColumns F))) :=
        rank_le_of_ker_le (h1 F (by omega) hguard)
      _≤zsE ao (zWl (momentMap F (reducedColumns F))) :=
        rank_le_of_ker_le (h2 F (by omega) (by omega))
      _≤_:= by
        simpa only [zvt,Fintype.card_coe] using
          Submodule.finrank_le (zWl (momentMap F (reducedColumns F)))
    have h₁: (D:ℤ)≤latticeAllowance F:= by rw [← reduced_card F]; exact_mod_cast h₀
    have h₂: (D:ℤ)≤tail:= by
      rw [← ht]
      dsimp [D]
      omega
    have hm:=le_min h₁ h₂
    change _≤oldCount F - tail+(D:ℤ) at hr
    omega
end
end qnnEPee
