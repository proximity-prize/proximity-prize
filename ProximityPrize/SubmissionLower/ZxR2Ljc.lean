import ProximityPrize.SubmissionLower.Zzm95ae
import ProximityPrize.SubmissionLower.ZCYrWLb
import ProximityPrize.SubmissionLower.ZeKVyCb
set_option Elab.async false
set_option autoImplicit true
namespace qOrl4se
noncomputable section
open qK9H6va q1jcGec qaTCFjd MvPolynomial
open P1_6_1_3 (Target adjacentProduct)
open P1_6_1_3_2 (adjacent original bind_adjacent_monomial bind_original
  original_homogeneous adjacent_order)
open fP (lP m9 cF xH qI)
open private step step_coeff step_adjacent from ProximityPrize.SubmissionLower.Zzm95ae
open private sum_target_monomial from ProximityPrize.SubmissionLower.ZNjr9pa
open private adjacent_coeff_zero from ProximityPrize.SubmissionLower.ZcG5Ygd
open private rU from ProximityPrize.SubmissionLower.ZZBDV9b
open private triangle sum_congr bOz bxa from ProximityPrize.SubmissionLower.Z0omYcd
open scoped BigOperators Matrix
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
local notation "F" => ZMod P1.p
local notation "Exp" => (Fin 4 →₀ ℕ)
private def witness (e s :Exp) :F :=
  ((e.weight m9:F) - 56)*(bind₁ original (monomial s 1)).coeff e
private theorem witness_sum {q:ℕ} (s :Exp) (hs :s.degree=q) :
    (∑ e :Target q,witness e.val s•bind₁ adjacent (monomial e.val 1)) =
      step 56 (monomial s 1) := by
  have hP:=original_homogeneous (R:=F) (m:=s)
  rw [hs] at hP
  calc
    _ = ∑ e :Target q,step 56 (bind₁ adjacent
        (monomial e.val ((bind₁ original (monomial s 1)).coeff e.val))) := by
      refine Finset.sum_congr rfl fun e _ => ?_
      have he (a :F) :bind₁ adjacent (monomial e.val a) =
          a•bind₁ adjacent (monomial e.val 1) := by
        simp only [bind_adjacent_monomial,one_smul]
      rw [he ((bind₁ original (monomial s 1)).coeff e.val),map_smul,step_adjacent,smul_smul]
      simp [witness,mul_comm]
    _=step 56 (bind₁ adjacent
        (∑ e :Target q,monomial e.val ((bind₁ original (monomial s 1)).coeff e.val))) := by
      simp only [map_sum]
    _ = _:= by rw [sum_target_monomial hP,bind_original]
private theorem discarded (e s m:Exp) (hm:m.weight lP≤56)
    (ht:m 3≤16) (he : ¬(e 0≤16∧e.weight m9<56)) :
    witness e s*(bind₁ adjacent (monomial e 1)).coeff m=0:= by
  by_cases hh:56<e.weight m9
  · apply mul_eq_zero_of_right
    by_contra hn
    exact (not_le_of_gt (hm.trans_lt hh))
      (mem_restrictWeightedOrder.mp (adjacent_order (R:=F) e) m (mem_support_iff.mpr hn))
  by_cases hw:e.weight m9<56
  · have htop:m 3<e 0:=lt_of_le_of_lt ht (Nat.lt_of_not_ge fun h=>he ⟨h,hw⟩)
    rw [bind_adjacent_monomial,one_smul]
    exact mul_eq_zero_of_right _ (adjacent_coeff_zero e m htop)
  · have hz :e.weight m9=56:= by omega
    simp [witness,hz]
private theorem recover {q:ℕ} (s m:Exp) (hs :s.degree=q)
    (hm:m.weight lP≤56) (ht:m 3≤16) :
    (∑ e :AdjacentRow q,(adjacentProduct e.val.val).coeff m*witness e.val.val s) =
      (step 56 (monomial s 1)).coeff m:= by
  classical
  rw [← witness_sum s hs]
  simp only [coeff_sum,coeff_smul,smul_eq_mul]
  let f (e :Target q) :=witness e.val s*(bind₁ adjacent (monomial e.val 1)).coeff m
  trans ∑ e :AdjacentRow q,f e.val
  · simp only [f,bind_adjacent_monomial,one_smul,adjacentProduct,mul_comm]
  rw [← Finset.sum_subtype (Finset.univ.filter keep) (by simp) f]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e _ he
  exact discarded e.val s m hm ht (by simpa [keep] using he)
private def Bo:Fin 7→ℕ×ℕ×ℕ :=
  ![(0,0,0),(1,0,0),(2,0,0),(0,1,0),(3,0,0),(1,1,0),(0,0,1)]
private def weight (i:Fin 7) :ℕ :=
  (Bo i).1+2*(Bo i).2.1+3*(Bo i).2.2
private def seed (q:ℕ) (i:Fin 7) :Exp :=
  let j:=Bo i
  rU (q-(j.1+j.2.1+j.2.2)) j.1 j.2.1 j.2.2
private theorem seed_degree {q:ℕ} (hq:3≤q) (i:Fin 7) :
    (seed q i).degree=q:= by
  have h:=(by decide : ∀ j:Fin 7,(Bo j).1+(Bo j).2.1+(Bo j).2.2≤3) i
  rw [cF]
  change q-((Bo i).1+(Bo i).2.1+(Bo i).2.2) +
    (Bo i).1+(Bo i).2.1+(Bo i).2.2=q
  omega
private theorem bwf (q:ℕ) (i:Fin 7) : (seed q i).weight lP=weight i:= by
  rw [xH]
  rfl
private theorem seed_inj (q:ℕ) :Function.Injective (seed q) := by
  have h : ∀ i j:Fin 7,Bo i=Bo j→i=j:= by decide
  intro i j he
  exact h i j (congrArg (fun m:Exp=>(m 1,m 2,m 3)) he)
private theorem diagonal_ne_zero {n:ℕ} (hn:n≤3) : (n:F) - 56≠0:= by
  have hp:56<P1.p:= by decide
  change (n:F)-((56:ℕ) :F)≠0
  intro h
  have hmod:=(ZMod.natCast_eq_natCast_iff' n 56 P1.p).mp (sub_eq_zero.mp h)
  rw [Nat.mod_eq_of_lt (by omega :n<P1.p),Nat.mod_eq_of_lt hp] at hmod
  omega
private theorem saving_at (q r n:ℕ) (hlo:3≤q) (hhi:q≤56)
    (hn:n≤7) (hc:q+r=99)
    (hgap : ∀ i:Fin 7,i.val<n→weight i+3<56 - r) :
    (Gy q (offset r)).rank+n≤bve q 56:= by
  classical
  let lift (i:Fin n) :Fin 7:=⟨i.val,i.isLt.trans_le hn⟩
  let s (i:Fin n) :=seed q (lift i)
  have hd (i:Fin n) : (s i).degree=q:=seed_degree hlo (lift i)
  have hw (i:Fin n) : (s i).weight lP≤3 :=
    (bwf q (lift i)).trans_le ((by decide : ∀ j:Fin 7,weight j≤3) (lift i))
  have ht (i:Fin n) :s i 3≤16 :=
    (by decide : ∀ j:Fin 7,(Bo j).2.2≤16) (lift i)
  let W:Matrix (AdjacentRow q) (Fin n) F:= fun e i=>witness e.val.val (s i)
  have hker : (adjacentMatrix q r)ᵀ*W=0:= by
    ext m i
    rw [Matrix.mul_apply]
    change (∑ e :AdjacentRow q,(adjacentProduct e.val.val).coeff m.val *
      witness e.val.val (s i))=0
    have hlow:=m.property.2.1
    unfold offset at hlow
    have hhigh:m.val.weight lP≤56:= by exact_mod_cast m.property.2.2.1
    have hg:=hgap (lift i) i.isLt
    rw [← bwf q (lift i)] at hg
    change (s i).weight lP+3<56 - r at hg
    have hs : (s i).weight lP+3< m.val.weight lP:= by omega
    rw [recover _ _ (hd i) hhigh m.property.2.2.2,
      step_coeff _ _ _ (Or.inr hs),ite_eq_right (by intro he; rw [he] at hs; omega)]
  let R:Matrix (Fin n) (AdjacentRow q) F:= fun i e=>(adjacentProduct e.val.val).coeff (s i)
  let T:=R*W
  have hT (i j:Fin n) :T i j=(step 56 (monomial (s j) 1)).coeff (s i) := by
    change (R*W) i j= _
    rw [Matrix.mul_apply]
    exact recover _ _ (hd j) ((hw i).trans (by decide)) (ht i)
  have htri:T.IsLowerTriangular := by
    intro i j hij
    change i<j at hij
    have hm : ∀ a b:Fin 7,a≤b→weight a≤weight b:= by decide
    have hi: (s i).weight lP≤(s j).weight lP :=
      (bwf q (lift i)).trans_le ((hm (lift i) (lift j) hij.le).trans_eq
        (bwf q (lift j)).symm)
    have hne :s j≠s i:= fun he=>hij.ne (Fin.ext (congrArg Fin.val (seed_inj q he)).symm)
    rw [hT,step_coeff _ _ _ (Or.inl hi),ite_eq_right hne]
  have hdet:T.det≠0:= by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    rw [hT,step_coeff _ _ _ (Or.inl le_rfl),ite_eq_left rfl]
    exact diagonal_ne_zero (hw i)
  have hrank :=Matrix.rank_of_det_ne_zero hdet
  rw [Fintype.card_fin] at hrank
  have hwRank :=hrank.ge.trans (Matrix.rank_mul_le_right R W)
  have h:=Matrix.rank_add_rank_le_card_of_mul_eq_zero hker
  rw [Matrix.rank_transpose] at h
  have hdeg:iO q=q:= by
    rw [iO,P6_6_1.asu,ite_eq_left (by omega :q≤111),min_eq_left hhi]
  have hcut: (Vm q (offset r)).toNat=56:= by
    rw [aq6,DV,hc]
  exact (Nat.add_le_add (rank_le_adjacent hdeg hcut) hwRank).trans
    (h.trans (adjacent_card_le q))
private def shortCount (q:ℕ) :ℕ :=
  qI (q+1) fun t =>
    let x :=56 - 2*t
    let k :=min 17 (t+1)
    let u:=q - t+1
    (triangle x - triangle (x - u))-(triangle (x - k) - triangle (x - k - u))
private theorem shortCount_eq (q:ℕ) :bve q 56=shortCount q:= by
  unfold bve shortCount
  refine sum_congr _ fun t => ?_
  let u:=q - t+1
  let x :=56 - 2*t
  let k :=min 17 (t+1)
  have hs : (qI u fun c=>min 17 (aiW.aOx t c 56)) +
      (qI u fun c=>x - k - c)=qI u (fun c=>x - c) := by
    rw [← bOz]
    exact sum_congr _ fun c=> by unfold aiW.aOx; dsimp [x,k]; omega
  rw [bxa,bxa] at hs
  exact Nat.eq_sub_of_add_eq hs
private theorem checked (q r n cap:ℕ) (hlo:3≤q) (hhi:q≤56)
    (hn:n≤7) (hc:q+r=99)
    (hgap : ∀ i:Fin 7,i.val<n→weight i+3<56 - r)
    (hcap:shortCount q≤ cap+n) :KC q r cap:= by
  have hs :=saving_at q r n hlo hhi hn hc hgap
  rw [shortCount_eq] at hs
  unfold KC
  omega
local notation "u9" q "," r "," n "," cap =>
  checked q r n cap (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem proof :qaTCFjd.c1 :=
  ⟨u9 47,52,1,5473,u9 48,51, 2,5492,
    u9 49,50,4,5506,u9 50,49,7,5515⟩
end
end qOrl4se
