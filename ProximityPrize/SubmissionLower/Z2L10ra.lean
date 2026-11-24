import ProximityPrize.SubmissionLower.Z0SRqJa
set_option Elab.async false
section
set_option autoImplicit true
namespace qzM5sEd
noncomputable section
open aR (ao)
open Rj (adf)
open qlc9qed (Bank)
open qPQ4nYa (iO Bb cappedCumulative)
open Finset MvPolynomial
open private aEg c0e cEi exponent cxO.exponent_injective eLR eLT from ProximityPrize.SubmissionLower.A3
private def HX (d C:ℕ) (w:ℤ) :Finset (ℕ×ℕ) :=
  (aEg d w).filter fun p=>p.1≤C
private theorem aVQ (d C:ℕ) (w:ℤ) (p:ℕ×ℕ) :
    p∈HX d C w↔(p.1+p.2≤d∧(p.2 :ℤ)+2*p.1≤w)∧p.1≤C:= by
  simp only [HX,mem_filter,c0e]
private theorem cEd (d C:ℕ) (w:ℤ) :
    ((HX d C w).card:ℤ)=cappedCumulative d C w:= by
  by_cases hC:C<d
  · let shift:ℕ×ℕ→ℕ×ℕ:= fun p=>(p.1+(C+1),p.2)
    have hi:Function.Injective shift:= by
      intro p r h
      have h₁:=congrArg Prod.fst h
      have h₂:=congrArg Prod.snd h
      exact Prod.ext (Nat.add_right_cancel h₁) h₂
    have hx : ((aEg d w).filter fun p => ¬ p.1≤C) =
        (aEg (d-(C+1)) (w - 2*((C:ℤ)+1))).image shift:= by
      ext p
      simp only [mem_filter,mem_image,c0e]
      constructor
      · intro hp
        refine ⟨(p.1-(C+1),p.2),?_,?_⟩
        · dsimp
          omega
        · apply Prod.ext
          · dsimp [shift]
            omega
          · rfl
      · rintro ⟨r,hr,rfl⟩
        dsimp [shift]
        omega
    have h:=congrArg (fun n:ℕ=>(n:ℤ))
      (card_filter_add_card_filter_not (s :=aEg d w) fun p=>p.1≤C)
    simp only [Nat.cast_add,hx,card_image_of_injective _ hi,cEi] at h
    simpa only [HX,cappedCumulative,hC,ite_true] using eq_sub_of_add_eq h
  · have h:HX d C w=aEg d w:= by
      ext p
      simp only [aVQ,c0e]
      omega
    simp [h,cappedCumulative,hC,cEi]
private def vo (d C:ℕ) (J g:ℤ) :Finset (ℕ×ℕ) :=
  HX d C J \ HX d C (min J (-g - 1))
private theorem dFD (d C:ℕ) (J g:ℤ) :
    ((vo d C J g).card:ℤ)=cappedCumulative d C J - cappedCumulative d C (min J (-g - 1)) := by
  have hs :HX d C (min J (-g - 1))⊆HX d C J:= by
    intro p hp
    rw [aVQ] at hp ⊢
    omega
  have h:=congrArg (fun n:ℕ=>(n:ℤ)) (card_sdiff_add_card_eq_card hs)
  simp only [Nat.cast_add] at h
  have h' : ((vo d C J g).card:ℤ) =
      ((HX d C J).card:ℤ)-((HX d C (min J (-g - 1))).card:ℤ) :=eq_sub_of_add_eq h
  simpa only [cEd] using h'
private theorem bnD (b:Bank) (q:ℕ) (g:ℤ) :
    (↑((vo (iO b q) b.box.t b.box.j g).image (exponent (iO b q))) :
      Set adf)=cbQ b q g:= by
  ext e
  simp only [mem_coe,mem_image,vo,mem_sdiff,aVQ]
  change _↔e.weight (fun _=>1)=iO b q ∧
    -g≤(e.weight Fin.val :ℤ)∧e.weight Fin.val≤b.box.j∧e 2≤b.box.t
  rw [eLR,eLT]
  constructor
  · rintro ⟨p,hp,rfl⟩
    simp [exponent]
    omega
  · intro he
    refine ⟨(e 2,e 1),?_,?_⟩
    · dsimp
      omega
    · ext j
      fin_cases j <;> simp [exponent]
      omega
theorem gte (b:Bank) (q:ℕ) (g:ℤ) :
    (Module.finrank ao (aqz b q g) :ℤ)=Bb b q g:= by
  unfold aqz Bb
  rw [← bnD b q g,finrank_restrictSupport_finset,
    card_image_of_injective _ (cxO.exponent_injective _),dFD]
end
end qzM5sEd
end
section
set_option autoImplicit true
namespace qzM5sEd
noncomputable section
open aR (ao)
open qlc9qed (Bank)
open qPQ4nYa (iO pT K6 D8)
open MvPolynomial
open Rj (lK kJ yE Jd m5)
open baj (alQ aIL aJM aT5
  a9V bAa bqh cJ1 ezV ec2)
open scoped BigOperators
open private gGU diD eQh eQi from ProximityPrize.SubmissionLower.C
open private product b2K d5V cN8 cEp aIu from ProximityPrize.SubmissionLower.C
private theorem eIi (b:Bank) {q:ℕ} {g:ℤ} {f :lK}
    (hd:f.IsWeightedHomogeneous alQ (iO b q))
    (hf :bAa (pT b q g) f) :
    ∃ hsrc :f∈aqz b q g,(⟨f,hsrc⟩:aqz b q g) ∈
      LinearMap.ker (aPi b q g) := by
  have hP:f∈restrictWeightedOrder Fin.val (-g).toNat := by
    rw [← gGU f]
    apply bind₁_mem_restrictWeightedOrder _ (hf 0).2
    intro i
    fin_cases i <;> apply X_mem_restrictWeightedOrder <;> decide
  have hQo:f∈restrictWeightedOrder eQh ((iO b q:ℤ) - b.box.t).toNat := by
    rw [← diD f]
    apply bind₁_mem_restrictWeightedOrder _ (hf 1).1
    intro i
    fin_cases i <;> apply X_mem_restrictWeightedOrder <;> decide
  have hQw:f∈restrictWeightedOrder eQi (2*(iO b q:ℤ) - b.box.j).toNat := by
    rw [← diD f]
    apply bind₁_mem_restrictWeightedOrder _ (hf 1).2
    intro i
    fin_cases i <;> apply X_mem_restrictWeightedOrder <;> decide
  have hsrc :f∈aqz b q g:= by
    apply (mem_restrictSupport_iff ao).mpr
    intro e he
    have hdeg:=hd (mem_support_iff.mp he)
    have hn:=mem_restrictWeightedOrder.mp hP e he
    have ho:=mem_restrictWeightedOrder.mp hQo e he
    have hw:=mem_restrictWeightedOrder.mp hQw e he
    change e.weight alQ=iO b q ∧ -g≤(e.weight Fin.val :ℤ) ∧
      e.weight Fin.val≤b.box.j∧e 2≤b.box.t
    rw [aT5] at hdeg
    simp [Finsupp.weight_eq_sum,Fin.sum_univ_three,smul_eq_mul,Nat.mul_comm] at hn ho hw ⊢
    omega
  refine ⟨hsrc,LinearMap.mem_ker.mpr ?_⟩
  apply (weightedTruncation_eq_zero_iff _ _ _).mpr
  exact (hf 2).2
private theorem eO0 (b:Bank) (q:ℕ) (p:kJ) {f :lK}
    (hn:0≤K6 b q p)
    (hf :f.IsWeightedHomogeneous alQ (K6 b q p).toNat) :
    (product p*f).IsWeightedHomogeneous alQ (iO b q) := by
  have hp: (product p).IsWeightedHomogeneous alQ (∑ j,p j*(yE j).toNat) := by
    apply IsWeightedHomogeneous.prod
    intro j _
    simpa only [Nat.nsmul_eq_mul] using (d5V j).pow (p j)
  have hc:=cEp p yE (by intro j; unfold yE; split <;> decide)
  have hsum: (∑ j,p j*(yE j).toNat)+(K6 b q p).toNat =
      iO b q:= by
    unfold K6 at hn ⊢
    omega
  rw [← hsum]
  exact hp.mul hf
private theorem eO1 (b:Bank) (q:ℕ) (g:ℤ) (p:kJ) {f :lK}
    (hf :bAa (D8 b q g p) f) :bAa (pT b q g) (product p*f) := by
  intro i
  exact ⟨aIu p i aIL (pT b q g i).iy
      (fun j=>(Jd j i).iy)
      (by intro j; fin_cases j <;> fin_cases i <;> decide)
      (fun j=>(cN8 j i).1) (hf i).1,
    aIu p i aJM (pT b q g i).HE
      (fun j=>(Jd j i).HE)
      (by intro j; fin_cases j <;> fin_cases i <;> decide)
      (fun j=>(cN8 j i).2) (hf i).2⟩
private theorem ewc (b:Bank) (q:ℕ) (g:ℤ) (p:kJ) (hn:0≤K6 b q p) :
    Module.finrank ao (LinearMap.ker (bqh (K6 b q p).toNat (D8 b q g p))) ≤
      Module.finrank ao (LinearMap.ker (aPi b q g)) := by
  let S:=LinearMap.ker (bqh (K6 b q p).toNat (D8 b q g p))
  have h (f :S) :=eIi b (q:=q) (g:=g)
    (eO0 b q p hn (cJ1 f.val))
    (eO1 b q g p (ezV f))
  let L:S →ₗ[ao] lK :=
    (LinearMap.mulLeft ao (product p)).comp
      (((a9V (K6 b q p).toNat).subtype).comp S.subtype)
  let M:=L.codRestrict (aqz b q g) (fun f=>(h f).choose)
  let N :=M.codRestrict (LinearMap.ker (aPi b q g)) (fun f=>(h f).choose_spec)
  apply LinearMap.finrank_le_finrank_of_injective (f :=N)
  intro f f' hff'
  apply Subtype.ext
  apply Subtype.ext
  have hp:product p≠0 :=
    Finset.prod_ne_zero_iff.mpr fun j _=>pow_ne_zero _ (b2K j)
  exact mul_left_cancel₀ hp (congrArg (fun a=>(a.val :lK)) hff')
theorem plane_kernel_lower (b:Bank) (q:ℕ) (g:ℤ) (p:kJ) :
    m5 (K6 b q p) (D8 b q g p) ≤
      (Module.finrank ao (LinearMap.ker (aPi b q g)) :ℤ) := by
  let d:=K6 b q p
  by_cases hn:K6 b q p<0
  · simp [m5,hn]
  have hnonneg:0≤d:=le_of_not_gt hn
  have hres :=ec2 d.toNat (D8 b q g p)
  rw [Int.toNat_of_nonneg hnonneg] at hres
  have hl:=ewc b q g p hnonneg
  simp only [m5,hn,ite_false]
  exact hres.trans (by exact_mod_cast hl)
end
end qzM5sEd
end
