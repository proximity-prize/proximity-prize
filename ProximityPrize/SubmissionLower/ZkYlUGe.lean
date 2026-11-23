import ProximityPrize.SubmissionLower.Z2dBXLe
import ProximityPrize.SubmissionLower.ZzeWNbd
import ProximityPrize.SubmissionLower.DR
import ProximityPrize.SubmissionLower.ZELw4Ka
set_option Elab.async false
open _root_ renaming Finset.sum_congr → zUo, Fintype.card → zhP, Fintype.card_le_of_injective → zWJ, Fintype.sum_sigma → zla, Nat.cast_mul → z2R, Nat.choose_eq_zero_of_lt → zsx, Nat.strong_induction_on → z0n, Set.mem_range_self → zWL, Set.range → zxp, Submodule.span → zLD, Submodule.subset_span → zBO
section
set_option autoImplicit true
namespace qwzqCne
open qK9H6va (XN iO Gy Vm)
open qxuyiwe (profileCutoff)
open fP (lP m9 cF oG)
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
theorem Sj (e :aY) :cP (aD e.val)=54+e.val.weight m9:= by
  have hd:=e.property
  rw [cF] at hd
  rw [oG]
  simp only [aD,cP]
  omega
private theorem d0t {e v :aY} (h:dZ v<dZ e) :
    cP (aD v.val)≤ cP (aD e.val) := by
  have he :=e.property
  rw [cF] at he
  unfold dZ at h
  omega
private theorem EI {ι κ σ:Type*} (f :κ→ι) (v :σ→ι→Ground)
    (x :ι→Ground) (S:Submodule Ground (κ→Ground))
    (hx :x∈zLD Ground (zxp v))
    (hv : ∀ j,(v j) ∘ f∈S) :x ∘ f∈S:= by
  let L: (ι→Ground) →ₗ[Ground] (κ→Ground) :=
    LinearMap.pi fun j=>LinearMap.proj (f j)
  exact (Submodule.map_span_le _ _ _).mpr
    (by rintro _ ⟨j,rfl⟩; exact hv j) (Submodule.mem_map_of_mem (f :=L) hx)
private def cGT (q:ℕ) (g:ℤ) (cut:ℕ) (hd:iO q=54)
    (hcut:cut≤(-g).toNat) :XN q g→ gU cut:= fun m =>
  ⟨m.val,m.property.1.trans hd,by
    have hlo:=m.property.2.1
    have hn:0≤(m.val.weight lP:ℤ) := by omega
    omega,m.property.2.2⟩
theorem fTj (head:aGq 54 (tailCost - 1))
    (tail : ∀ cut:ℕ,tailCost - 98≤ cut →
      zhP (gU cut)≤zhP (bk9 cut))
    (q:ℕ) (g:ℤ) (hd:iO q=54) :
    (Gy q g).rank≤zhP (PrefixPivot g (profileCutoff q 54 g)) := by
  classical
  let w:=profileCutoff q 54 g
  let ell:=(-g).toNat
  have hw' : w=153 - q - g:= by dsimp [w,profileCutoff,Vm]; omega
  have hq:=hd.symm.trans_le (min_le_left q (P6_6_1.asu q))
  change (Gy q g).rank≤zhP (PrefixPivot g w)
  by_cases hwide : (tailCost:ℤ)<w
  · have hcut:tailCost - 98≤ell:= by dsimp only [ell]; omega
    let f :=cGT q g ell hd le_rfl
    have hf :Function.Injective f := fun _ _ h =>
      Subtype.ext (congrArg (fun m:gU ell=>m.val) h)
    let addPivot (j:bk9 ell) :PrefixPivot g w :=
      ⟨j.val,by have h:=j.property.1; omega,by
        have h:=j.property.2
        dsimp only [ell] at h
        omega⟩
    have hinj:Function.Injective addPivot:= fun _ _ h =>
      Subtype.ext (congrArg (fun j:PrefixPivot g w=>j.val) h)
    exact (Gy q g).rank_le_card_width.trans
      ((Fintype.card_le_of_injective f hf).trans
        ((tail ell hcut).trans (Fintype.card_le_of_injective addPivot hinj)))
  let v (j:PrefixPivot g w) :=yv (κ:=XN q g) Subtype.val (Ug j.val)
  let S:=zLD Ground (zxp v)
  have hrows : ∀ n (e :aY),dZ e=n →
      (cP (aD e.val) :ℤ)<w →
      yv (κ:=XN q g) Subtype.val (aD e.val)∈S:= by
    intro n
    induction n using z0n with
    | h n ih =>
      intro e he hweight
      let R:=cP (aD e.val)
      have hRlo:54≤R:= by dsimp only [R]; rw [Sj]; omega
      change (R:ℤ)<w at hweight
      have hRhi:R≤tailCost - 1 := by omega
      have hRcut:R<99+ell:= by dsimp only [ell]; omega
      obtain ⟨cut,hsmall,hdep⟩:=head e hRlo hRhi
      by_cases hcut:cut≤ell
      · exact EI (cGT q g cut hd hcut)
          (fun a :iw e=>cE cut (aD a.val.val)) _ S hdep (by
            intro a
            have hlt:=a.property.trans_le he.le
            have hle :=d0t a.property
            exact ih _ hlt a.val rfl (by omega))
      · rcases hsmall with hsmall | ⟨j,hj,hc,hik⟩
        · change cut≤R-98 at hsmall
          omega
        · have heng : -g≤(Nx j:ℤ) := by
            have hcut' := Nat.lt_of_not_ge hcut
            dsimp only [ell] at hcut'
            omega
          have hmem:=zBO (R:=Ground)
            (zWL (f :=v) (⟨j,by rwa [hc],heng⟩:PrefixPivot g w))
          change yv _ (Ug j)∈S at hmem
          simpa only [hj] using hmem
  rw [Matrix.rank_eq_finrank_span_row]
  refine (Submodule.finrank_mono (show zLD Ground (zxp (Gy q g).row)≤S
    from Submodule.span_le.mpr ?_)).trans (finrank_range_le_card v)
  rintro _ ⟨e,rfl⟩
  let E :aY:=⟨e.val,e.property.1.trans hd⟩
  have hw:=e.property.2
  change e.val.weight m9<(99-(q:ℤ) - g).toNat at hw
  exact hrows _ E rfl (by
    rw [Sj]
    change ((54+e.val.weight m9:ℕ) :ℤ)<w
    omega)
end
end qwzqCne
end
section
set_option autoImplicit true
namespace qwzqCne
open fP (qI Qg)
open qxuyiwe (h54 FF PivotIndex)
open scoped BigOperators
noncomputable section
private theorem gapCard (g:ℕ) (hg:g<99) :
    qI 57 (groupCount g)=h54[g]'(by exact hg) := by
  interval_cases g <;> rfl
private def gapEquiv :Fin 99 ≃ Fin h54.length:=finCongr rfl
private def Tg:Pivot ≃ qxuyiwe.Pivot h54 :=
  Equiv.sigmaCongr gapEquiv fun g=>finSigmaFinEquiv.trans <| finCongr <| by
    rw [← Qg]
    exact gapCard g.val g.isLt
def ix :PivotIndex h54 := fun j=>(Tg.symm j).2.1
theorem card_le_eligible (g w:ℤ) :
    zhP (PrefixPivot g w)≤zhP (FF ix g w) := by
  let f (j:PrefixPivot g w) :FF ix g w:=⟨Tg j.val,by
    have hg: (Tg j.val).1.val=j.val.1.val :=rfl
    have hi: (ix (Tg j.val)).val=Nx j.val := by
      exact congrArg (fun p:Pivot=>p.2.1.val) (Tg.symm_apply_apply j.val)
    refine ⟨?_,?_⟩
    · rw [hg,hi]
      simpa only [c37,Nat.cast_add] using j.property.1
    · rw [hi]
      exact j.property.2⟩
  exact zWJ f fun _ _ h =>
    Subtype.ext (Tg.injective (congrArg Subtype.val h))
end
end qwzqCne
end
section
set_option autoImplicit true
namespace qwzqCne
open fP (lP xH cF qI Qg)
open scoped BigOperators
noncomputable section
private def secondLo (i f :ℕ) :ℕ:=i-(54+2*f)
private def fiberCount (i f :ℕ) :ℕ:=(i-3*f)/2+1 - secondLo i f
private abbrev bi8 (cut:ℕ) :=
  Σ i:Fin 57,Σ f :Fin (min 16 (i.val/3)+1),
    Fin (if cut≤ i.val then fiberCount i.val f.val else 0)
private def dNG (cut:ℕ) (m:gU cut) :bi8 cut:= by
  have hlo:=m.property.2.1
  have hhi:=m.property.2.2.1
  have htop:=m.property.2.2.2
  have hd:=m.property.1
  rw [cF] at hd
  let i:=m.val.weight lP
  have hj:i=m.val 1+2*m.val 2 + 3*m.val 3:=xH _
  change (cut:ℤ)≤(i:ℤ) at hlo
  change (i:ℤ)≤56 at hhi
  have hcut:cut≤ i:= by omega
  have hf :m.val 3< min 16 (i/3)+1 := by omega
  refine ⟨⟨i,by omega⟩,⟨m.val 3,hf⟩,⟨m.val 2 - secondLo i (m.val 3),?_⟩⟩
  change m.val 2 - secondLo i (m.val 3)<(if cut≤ i then fiberCount i (m.val 3) else 0)
  rw [ite_eq_left hcut]
  unfold fiberCount secondLo
  omega
private theorem dNH (cut:ℕ) :Function.Injective (dNG cut) := by
  intro m n h
  have hi:m.val.weight lP=n.val.weight lP :=
    congrArg (fun s :bi8 cut=>s.1.val) h
  have hf :m.val 3=n.val 3:=congrArg (fun s :bi8 cut=>s.2.1.val) h
  have hc:=congrArg (fun s :bi8 cut=>s.2.2.val) h
  change m.val 2 - secondLo (m.val.weight lP) (m.val 3) =
    n.val 2 - secondLo (n.val.weight lP) (n.val 3) at hc
  rw [hi,hf] at hc
  have hm:=m.property.1
  have hn:=n.property.1
  rw [cF] at hm hn
  unfold secondLo at hc
  rw [xH] at hc
  rw [xH,xH] at hi
  have hc' : m.val 2=n.val 2 := by omega
  have hb:m.val 1=n.val 1 := by omega
  have ha :m.val 0=n.val 0:= by omega
  apply Subtype.ext
  apply Finsupp.ext
  intro j
  fin_cases j
  · exact ha
  · exact hb
  · exact hc'
  · exact hf
private def bnB (i:ℕ) :ℕ :=
  qI (min 16 (i/3)+1) (fiberCount i)
private theorem dNB (cut:ℕ) :
    zhP (gU cut) ≤
      ∑ i:Fin 57,if cut≤ i.val then bnB i.val else 0:= by
  refine (zWJ _ (dNH cut)).trans_eq ?_
  simp only [bi8,Fintype.card_sigma,Fintype.card_fin]
  refine zUo rfl fun i _ => ?_
  by_cases hi:cut≤ i.val
  · simp only [hi,ite_true,bnB,Qg]
  · simp [hi]
private def pivotCounts (i:ℕ) :ℕ :=
  qI 99 fun k=>if k+i<tailCost then groupCount k i else 0
private theorem pivotCounts_eq (i:ℕ) (hlo:tailCost - 98≤ i) (hhi:i≤56) :
    pivotCounts i=bnB i:= by
  unfold tailCost at hlo
  interval_cases i <;> rfl
private theorem tail_card (cut:ℕ) :
    zhP (bk9 cut) =
      ∑ i:Fin 57,if cut≤ i.val then pivotCounts i.val else 0:= by
  classical
  calc
    _ = ∑ p:Pivot,if c37 p<tailCost∧cut≤Nx p then 1 else 0:= by
      simp only [bk9,Fintype.card_subtype,Finset.sum_boole,Nat.cast_id]
    _ = ∑ k :Fin 99,∑ i:Fin 57,
          if cut≤ i.val∧k.val+i.val<tailCost then groupCount k.val i.val else 0:= by
      rw [zla]
      refine zUo rfl fun k _ => ?_
      rw [zla]
      refine zUo rfl fun i _ => ?_
      simp only [c37,Nx]
      by_cases hi:cut≤ i.val <;> by_cases hk :k.val+i.val<tailCost <;> simp [hi,hk]
    _ = _:= by
      rw [Finset.sum_comm]
      refine zUo rfl fun i _ => ?_
      by_cases hi:cut≤ i.val <;> simp [hi,pivotCounts,Qg]
theorem tailWitness (cut:ℕ) (hlo:tailCost - 98≤ cut) :
    zhP (gU cut)≤zhP (bk9 cut) := by
  classical
  refine (dNB cut).trans_eq ?_
  rw [tail_card]
  refine zUo rfl fun i _ => ?_
  by_cases hi:cut≤ i.val
  · simp only [hi,ite_true,pivotCounts_eq i.val (hlo.trans hi) (by omega)]
  · simp [hi]
end
end qwzqCne
end
section
set_option autoImplicit true
namespace q1racBe
open qwzqCne
def jZ (e :aY) (cut:ℕ) :Prop :=
  cE cut (aD e.val) ∈
    zLD Ground (zxp fun v :iw e=>cE cut (aD v.val.val))
end q1racBe
end
section
set_option autoImplicit true
namespace qokB5pc
open qHde8fc
open fP (cF oG)
def second (w f a :ℕ) :ℕ:=w-(56+3*a+2*f)
def aS (w f a :ℕ) :Triple :=
  let c:=second w f a
  (56-(a+c+f),c,f)
theorem nG (e :aY) :
    cP (aD e.val)=56+(3*e.val 0+e.val 2+2*e.val 3) := by
  rw [Sj,oG]
theorem amG (e :aY) {w:ℕ} (he :cP (aD e.val)=w) :
    aD e.val=aS w (e.val 3) (e.val 0) := by
  have h:=nG e
  have hd:=e.property
  rw [cF] at hd
  have hc:second w (e.val 3) (e.val 0)=e.val 2 := by unfold second; omega
  change (e.val 1,e.val 2,e.val 3)=(56-(e.val 0+second w (e.val 3) (e.val 0)+e.val 3),
    second w (e.val 3) (e.val 0),e.val 3)
  rw [hc,show 56-(e.val 0+e.val 2+e.val 3)=e.val 1 by omega]
def b8 (s cut j k :ℕ) :Prop :=
  3*(57 - cut)+j+2*k≤ s+2
abbrev gP (s cut:ℕ) :=
  {m:gU cut // ¬ b8 s cut (m.val 2) (m.val 3)}
def cZ (s cut:ℕ) (v :Triple) (m:gP s cut) :Ground :=
  cE cut v m.val
abbrev jZ (e :aY) (cut:ℕ) :=
  zLD Ground (zxp fun v :iw e=>cE cut (aD v.val.val))
def fG (s :ℕ) (e :aY) (cut:ℕ) :Prop :=
  cZ s cut (aD e.val) ∈
    zLD Ground (zxp fun v :iw e =>
      cZ s cut (aD v.val.val))
def OC (s cut:ℕ) (e :aY) :Prop :=
  b8 s cut (e.val 2) (min (e.val 3) 16)
end qokB5pc
end
section
set_option autoImplicit true
namespace qokB5pc
open qHde8fc
open fP (Ew cF xH)
open scoped BigOperators
open private bGN from ProximityPrize.SubmissionLower.ZELw4Ka
open private bm8 from ProximityPrize.SubmissionLower.DR
open private exp from ProximityPrize.SubmissionLower.AZ
open private R0 from ProximityPrize.SubmissionLower.DR
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem factorial_ne_zero {m:ℕ} (hm:m≤56) :
    (m.factorial:Ground)≠0:= by
  induction m with
  | zero=>simp
  | succ m ih =>
    rw [Nat.factorial_succ,z2R]
    refine mul_ne_zero ?_ (ih (by omega))
    intro h
    have hp:=(CharP.cast_eq_zero_iff Ground P1.p (m+1)).mp h
    have hle :=Nat.le_of_dvd (Nat.succ_pos m) hp
    change 0x7f000001≤ m+1 at hle
    omega
private theorem choose_ne_zero {n k :ℕ} (hn:n≤56) (hk :k≤n) :
    (n.choose k :Ground)≠0:= by
  intro h
  have he :=congrArg (fun m:ℕ=>(m:Ground)) (Nat.choose_mul_factorial_mul_factorial hk)
  simp only [z2R,h,zero_mul] at he
  exact factorial_ne_zero hn he.symm
theorem SX (n U w:ℕ) (hn:n≤56) (hU:U≤n) (hw:w≤U + 1)
    (v :Fin w→Ground) :
    ∃ c:Fin w→Ground,∀ j:Fin w,
      (∑ i:Fin w,c i*((n - i.val).choose (U - j.val) :Ground))=v j:= by
  let δ (j:Fin w) :Ground :=(n.choose (U - j.val) :Ground)
  obtain ⟨a,ha⟩:=bGN w (n-U) (fun j=>v j/δ j)
  refine ⟨fun i=>a i*(n.choose i.val :Ground),?_⟩
  intro j
  have hz :δ j≠0:=choose_ne_zero hn (by omega)
  calc
    _ = ∑ i:Fin w,(a i*((n-U + j.val).choose i.val :Ground))*δ j:= by
      apply zUo rfl
      intro i _
      have h:=congrArg (fun m:ℕ=>(m:Ground)) (bm8 n i.val (U - j.val))
      have he :n-(U - j.val)=n-U + j.val := by omega
      simp only [z2R,he] at h
      dsimp only [δ]
      rw [mul_assoc,h]
      ac_rfl
    _=v j:= by rw [← Finset.sum_mul,ha,div_mul_cancel₀ _ hz]
private theorem aNn {e v :aY}
    (h:cP (aD v.val)<cP (aD e.val)) :
    dZ v<dZ e := by
  have hd:=v.property
  rw [cF] at hd
  unfold dZ
  omega
private theorem i7 {cut:ℕ} (m:gU cut) :
    cut≤ m.val 1+2*m.val 2 + 3*m.val 3 ∧
      m.val 1+2*m.val 2 + 3*m.val 3≤56:= by
  obtain ⟨_,hl,hu,_⟩:=m.property
  rw [xH] at hl hu
  exact ⟨by exact_mod_cast hl,by exact_mod_cast hu⟩
private theorem a2O {cut:ℕ} {m n:gU cut}
    (hb:m.val 1=n.val 1) (hc:m.val 2=n.val 2) (hf :m.val 3=n.val 3) :
    m=n:= by
  have hm:=m.property.1
  have hn:=n.property.1
  rw [cF] at hm hn
  apply Subtype.ext
  apply Finsupp.ext
  intro j
  fin_cases j
  · change m.val 0=n.val 0
    omega
  · exact hb
  · exact hc
  · exact hf
private theorem iN {cut b c f :ℕ} (m:gU cut)
    (h:c< m.val 2∨f< m.val 3) :cE cut (b,c,f) m=0:= by
  rcases h with h | h
  · simp [cE,yv,zsx h]
  · simp [cE,yv,zsx h]
private def width (cut j k :ℕ) :ℕ:=57 - max cut (2*j+3*k)
private def BS (cut j k :ℕ) (htop:k≤16)
    (i:Fin (width cut j k)) :gU cut:= by
  let b:=56-(2*j+3*k) - i.val
  have hpos :=i.isLt
  unfold width at hpos
  refine ⟨exp (56-(b+j+k)) b j k,?_⟩
  simp only [Ew,cF,xH]
  change 56-(b+j+k)+b+j+k=56 ∧
    (cut:ℤ)≤(b+2*j+3*k :ℕ) ∧
    ((b+2*j+3*k :ℕ) :ℤ)≤56∧k≤16
  constructor
  · dsimp only [b]
    omega
  · refine ⟨?_,?_,htop⟩ <;> dsimp only [b] <;> omega
private theorem SP (cut j k :ℕ) (htop:k≤16)
    (i:Fin (width cut j k)) :
    (BS cut j k htop i).val 1=56-(2*j+3*k) - i.val :=rfl
private theorem Ir (cut j k :ℕ) (htop:k≤16)
    (i:Fin (width cut j k)) :
    (BS cut j k htop i).val 2=j:=rfl
private theorem GX (cut j k :ℕ) (htop:k≤16)
    (i:Fin (width cut j k)) :
    (BS cut j k htop i).val 3=k :=rfl
private theorem auE {cut j k :ℕ} (htop:k≤16)
    (m:gU cut) (h₂:m.val 2=j) (h₃:m.val 3=k) :
    ∃ i,BS cut j k htop i=m:= by
  obtain ⟨hlo,hhi⟩:=i7 m
  rw [h₂,h₃] at hlo hhi
  let i:Fin (width cut j k) :=⟨56-(m.val 1+2*j+3*k),by
    unfold width
    omega⟩
  refine ⟨i,a2O ?_ h₂.symm h₃.symm⟩
  rw [SP]
  dsimp only [i]
  omega
private def R7 (e :aY) {s :ℕ} (hs :s≤56) (he :cP (aD e.val)=56+s)
    (j k i:ℕ) (h:3*i+j+2*k<s) :iw e := by
  let u:aY:=⟨exp i (56 - j - k - i) j k,by
    rw [cF]
    change i+(56 - j - k - i)+j+k=56
    omega⟩
  refine ⟨u,aNn ?_⟩
  rw [nG,he]
  change 56+(3*i+j+2*k)<56+s
  omega
private theorem R8 (e :aY) {s :ℕ} (hs :s≤56) (he :cP (aD e.val)=56+s)
    (j k i:ℕ) (h:3*i+j+2*k<s) :
    aD (R7 e hs he j k i h).val.val=(56 - j - k - i,j,k) :=rfl
private theorem singleton_mem (e :aY) {s :ℕ} (hs :s≤56) (he :cP (aD e.val)=56+s)
    (cut:ℕ) (m:gU cut) (hm:b8 s cut (m.val 2) (m.val 3)) :
    Pi.single m (1 :Ground)∈jZ e cut:= by
  classical
  let S:=jZ e cut
  let key (m:gU cut) :=m.val 2+m.val 3
  have hsingle (n:ℕ) : ∀ m:gU cut,key m=n →
      b8 s cut (m.val 2) (m.val 3)→Pi.single m (1 :Ground)∈S:= by
    induction n using z0n with
    | h n ih =>
      intro m hm hcovered
      let j:=m.val 2
      let k :=m.val 3
      obtain ⟨_,hhi⟩:=i7 m
      have htop:=m.property.2.2.2
      have hjk :2*j+3*k≤56:= by dsimp only [j,k]; omega
      have hi_cost (i:Fin (width cut j k)) :3*i.val+j+2*k<s := by
        have hi:=i.isLt
        change 3*(57 - cut)+j+2*k≤ s+2 at hcovered
        unfold width at hi
        omega
      let atCol:=BS cut j k htop
      let v (i:Fin (width cut j k)) :iw e :=R7 e hs he j k i.val (hi_cost i)
      let target (i:Fin (width cut j k)) :Ground :=
        Pi.single (M:= fun _:gU cut=>Ground) m 1 (atCol i)
      obtain ⟨coef,hcoef⟩:=SX (56 - j - k) (56-(2*j+3*k))
        (width cut j k) (by omega) (by omega) (by unfold width; omega) target
      let g:gU cut→Ground :=
        ∑ i:Fin (width cut j k),coef i•cE cut (aD (v i).val.val)
      have hg:g∈S:= by
        apply Submodule.sum_mem
        intro i _
        exact S.smul_mem _ (zBO ⟨v i,rfl⟩)
      have hbox (z :gU cut) (hz :j<z.val 2∨k<z.val 3) :g z=0:= by
        simp only [g,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,v,R8]
        apply Finset.sum_eq_zero
        intro i _
        rw [iN z hz,mul_zero]
      have hfit (z :gU cut) (h₂:z.val 2=j) (h₃:z.val 3=k) :
          g z=Pi.single (M:= fun _:gU cut=>Ground) m 1 z := by
        obtain ⟨i,hi⟩:=auE htop z h₂ h₃
        subst z
        change g (atCol i)=target i
        rw [← hcoef i]
        simp only [g,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,v,R8,
          cE,yv,atCol,SP,Ir,GX,
          Nat.choose_self,Nat.cast_one,mul_one]
      have hrest:g-Pi.single m (1 :Ground)∈S:= by
        apply R0
        intro z hz
        have hsmall:z.val 2≤j∧z.val 3≤k := by
          by_contra! ho
          have hne :z≠m:= by
            rintro rfl
            dsimp [j,k] at ho
            omega
          have hor :j<z.val 2∨k<z.val 3:= by omega
          exact hz (by rw [Pi.sub_apply,hbox z hor,Pi.single_eq_of_ne hne,sub_zero])
        have hlt:key z<n:= by
          by_contra! hle
          dsimp only [key] at hle hm
          have hmatch :z.val 2=j∧z.val 3=k := by dsimp only [j,k] at hsmall ⊢; omega
          exact hz (by rw [Pi.sub_apply,hfit z hmatch.1 hmatch.2,sub_self])
        have hzcovered:b8 s cut (z.val 2) (z.val 3) := by
          unfold b8 at *
          change z.val 2≤ m.val 2∧z.val 3≤ m.val 3 at hsmall
          omega
        exact ih _ hlt z rfl hzcovered
      simpa only [sub_sub_cancel] using S.sub_mem hg hrest
  exact hsingle _ m rfl hm
theorem amN (e :aY) {s :ℕ} (hs :s≤56) (he :cP (aD e.val)=56+s)
    (cut:ℕ) (h:fG s e cut) :
    cE cut (aD e.val) ∈
      zLD Ground (zxp fun v :iw e =>
        cE cut (aD v.val.val)) := by
  classical
  let S:=jZ e cut
  let L: (gU cut→Ground) →ₗ[Ground] (gP s cut→Ground) :=
    LinearMap.pi fun m=>LinearMap.proj m.val
  have hspan:zLD Ground (zxp fun v :iw e =>
      cZ s cut (aD v.val.val))≤S.map L:= by
    apply Submodule.span_le.mpr
    rintro _ ⟨v,rfl⟩
    exact ⟨_,zBO (zWL v),rfl⟩
  obtain ⟨w,hw,hm⟩:=hspan h
  have hrest:cE cut (aD e.val) - w∈S:= by
    apply R0
    intro m hn
    apply singleton_mem e hs he
    by_contra hcovered
    have hm' := congrFun hm (⟨m,hcovered⟩:gP s cut)
    change w m=cE cut (aD e.val) m at hm'
    exact hn (by rw [Pi.sub_apply,hm',sub_self])
  simpa only [sub_add_cancel] using S.add_mem hrest hw
theorem bu3 {s cut:ℕ} {e :aY}
    (h:OC s cut e) :fG s e cut:= by
  have hz :cZ s cut (aD e.val)=0:= by
    funext m
    change cE cut (e.val 1,e.val 2,e.val 3) m.val=0
    apply iN
    by_contra! hle
    exact m.property (by
      have htop:=m.val.property.2.2.2
      unfold OC b8 at h
      unfold b8
      omega)
  unfold fG
  rw [hz]
  exact Submodule.zero_mem _
end
end qokB5pc
end
