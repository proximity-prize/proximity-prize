import ProximityPrize.SubmissionLower.Z3vxfLe
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 50000
set_option maxRecDepth 256
namespace P6_6_8_3
open aR (Shape aO)
open yi (bF tD)
open nZ (j0 Jg DC A9 ZT)
open P6_6
open private bhj from ProximityPrize.SubmissionLower.CH
theorem caps_chamber (i:Box) :bF (caps i) := by
  cases i <;> exact ⟨by decide,by decide⟩
theorem caps_top (i:Box) : (caps i).t=(caps i).j/3:= by cases i <;> rfl
theorem remaining_fits (v :Shape) :
    aO (remainingChart v) m6∧bF (remainingChart v) := by
  let q:=rawResidual m6 v
  change aO (literalBody q).iU m6∧bF (literalBody q).iU
  have hb:q.b≤ m6.b:=Nat.sub_le _ _
  have hj: (literalBody q).j≤ m6.j :=
    (min_le_left _ _).trans (Nat.sub_le _ _)
  have ht: (literalBody q).t≤ m6.t :=
    (min_le_left _ _).trans (Nat.sub_le _ _)
  have htch:3*(literalBody q).t≤(literalBody q).j:= by
    change 3*min q.t (min q.b ((min q.j (3*q.b))/3))≤ min q.j (3*q.b)
    rw [← min_assoc]
    exact ZT _ _
  exact ⟨⟨max_le hb (hj.trans (by decide)),hj,ht⟩,Jg _ htch⟩
private theorem chartFits (l:ℕ) (a :Shape) :bF (weightedChart l a) := by
  unfold weightedChart
  split
  · exact ⟨le_max_right _ _,ZT _ _⟩
  · exact A9 _ _
private theorem chartLe (l:ℕ) {a A:Shape} (h:aO a A)
    (ht:a.t=1↔A.t=1) :aO (weightedChart l a) (weightedChart l A) := by
  by_cases ha :a.t=1
  · simp only [weightedChart,ite_eq_left ha,ite_eq_left (ht.mp ha)]
    obtain ⟨hb,hj,_⟩:=h
    refine ⟨?_,?_,?_⟩ <;> dsimp <;> gcongr
  · have hA:A.t≠1 := fun he=>ha (ht.mpr he)
    simpa only [weightedChart,ite_eq_right ha,ite_eq_right hA] using DC l h
private theorem join_fits {a p:Shape} (ha :bF a) (hp:bF p) :
    bF (joinBody a p) := by
  refine ⟨max_le_max ha.1 hp.1,?_⟩
  change 3*max a.t p.t≤ max a.j p.j
  rcases le_total a.t p.t with h | h
  · rw [max_eq_right h]
    exact hp.2.trans (le_max_right _ _)
  · rw [max_eq_left h]
    exact ha.2.trans (le_max_left _ _)
private theorem join_le {a p A P:Shape} (ha :aO a A) (hp:aO p P) :
    aO (joinBody a p) (joinBody A P) :=
  ⟨max_le_max ha.1 hp.1,max_le_max ha.2.1 hp.2.1,max_le_max ha.2.2 hp.2.2⟩
private theorem mixed_le (x :Shape) (hx :bF x)
    {p q r P Q R:Shape} (hp:aO p P) (hq:aO q Q) (hr :aO r R)
    (hpc:bF p) (hqc:bF q) (hrc :bF r)
    (hPc:bF P) (hQc:bF Q) (hRc:bF R) :
    wP x p q r≤wP x P Q R:= by
  rw [← bhj x p q r hpc hqc hrc,← bhj x P Q R hPc hQc hRc]
  exact Int.ofNat_le.mpr (tD (j0 x) hp hq hr hx hPc hQc hpc hqc hrc)
end P6_6_8_3
end
section
set_option autoImplicit true
namespace P6_6_8_3
open aR (Shape)
open P6_6
open P6_6_8 (pS dNb aUJ)
open private WC bP5 aEH byM from ProximityPrize.SubmissionLower.E6
open scoped BigOperators
def layerMass (v r :Shape) (ell i:ℕ) :ℕ :=
  pS ((v.scale (i+1)).plus (r.scale (i+2 - ell)))
private theorem mass_anti (v r :Shape) (ell:ℕ) :Antitone (layerMass v r ell) := by
  intro i j hij
  simp only [layerMass,aUJ]
  apply dNb
  apply nZ.zK
  · exact ⟨Nat.mul_le_mul_right _ (by omega),Nat.mul_le_mul_right _ (by omega),
      Nat.mul_le_mul_right _ (by omega)⟩
  · exact ⟨Nat.mul_le_mul_right _ (by omega),Nat.mul_le_mul_right _ (by omega),
      Nat.mul_le_mul_right _ (by omega)⟩
abbrev sampleMass (v r :Shape) (ell start:ℕ) (xF:List ℕ) :ℕ :=
  aEH (layerMass v r ell) start xF
def ay (v r :Shape) (ell start:ℕ) :List (List ℕ×ℕ)→Prop
  | []=>True
  | (xF,value) :: rest =>
    sampleMass v r ell start xF=value∧ay v r ell (start + xF.sum) rest
private def width :List (List ℕ×ℕ)→ℕ
  | []=>0
  | (ws,_) :: rows=>ws.sum+width rows
private def total:List (List ℕ×ℕ)→ℕ
  | []=>0
  | (_,n) :: rows=>n+total rows
private theorem checked_bound (v r :Shape) (ell:ℕ) (chunks :List (List ℕ×ℕ))
    (start:ℕ) (h:ay v r ell start chunks) :
    WC (layerMass v r ell) start (width chunks)≤total chunks := by
  induction chunks generalizing start with
  | nil=>simp [WC,width,total]
  | cons chunk rest ih =>
    rcases chunk with ⟨ws,value⟩
    rw [width,total,bP5]
    exact Nat.add_le_add
      ((byM (mass_anti v r ell) ws start).trans_eq h.1)
      (ih _ h.2)
theorem reject {v r :Shape} {ell len value :ℕ} {chunks :List (List ℕ×ℕ)}
    (h:ay v r ell 0 chunks) (hlen:width chunks=len)
    (hval :total chunks=value) (hz :layerMass v r ell len=0) (hn:value<gG) :
    CompanionTest v r ell:= by
  have hb:=checked_bound v r ell chunks 0 h
  rw [hlen,hval] at hb
  unfold CompanionTest
  simp_rw [← aUJ]
  change (∑ i∈Finset.range ack,layerMass v r ell i)<gG
  rw [FI.aQD _ len (fun i hi =>
    Nat.eq_zero_of_le_zero (((mass_anti v r ell) hi).trans_eq hz))]
  exact ((Finset.sum_le_sum_of_subset (Finset.range_mono (min_le_right _ _))).trans
    (by simpa only [WC,Nat.zero_add] using hb)).trans_lt hn
end P6_6_8_3
end
section
set_option autoImplicit true
namespace qCfmNSd
open aR (Shape aO)
open P6_6_8 (Lw)
open P6_6_8_3 (Box retainedBox bgt)
abbrev dM (v :Shape) :Prop :=aO (bgt (retainedBox v)) (Lw v)
private theorem rates_top (i:Box) : (bgt i).t=0:= by
  cases i <;> rfl
theorem row {v :Shape} {b j:ℕ}
    (hb: (Lw v).b=b) (hj: (Lw v).j=j)
    (hB: (bgt (retainedBox v)).b≤b) (hJ: (bgt (retainedBox v)).j≤j) :dM v := by
  exact ⟨hb.symm ▸ hB,hj.symm ▸ hJ,(rates_top _).symm ▸ Nat.zero_le _⟩
end qCfmNSd
end
