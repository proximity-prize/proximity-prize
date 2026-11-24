import ProximityPrize.SubmissionLower.Zs9cP0a
set_option Elab.async false
open _root_ renaming Finset.sum_congr → zUo, Finset.sum_range_succ → zpB, Fintype.card → zhP, Fintype.card_le_of_injective → zWJ, Fintype.card_sigma → zTU, Fintype.sum_sigma → zla, Function.Injective → zq4, Set.range → zxp, Submodule.span → zLD
section
set_option autoImplicit true
namespace qHde8fc
open scoped BigOperators
private def counts (n:ℕ) :ℕ :=
  ∑ j∈Finset.range n,JL j
private def HE (n:ℕ) :ℕ :=
  ∑ j∈Finset.range n,JL j*(n - j)
private theorem cwU (n:ℕ) :HE (n+1)=HE n+counts (n+1) := by
  rw [HE,HE,counts,zpB,zpB
    (f :=JL)]
  rw [← add_assoc,← Finset.sum_add_distrib]
  simp only [Nat.add_sub_cancel_left,mul_one]
  congr 1
  apply zUo rfl
  intro j hj
  have h:=Finset.mem_range.mp hj
  rw [Nat.succ_sub (Nat.le_of_lt h),Nat.succ_eq_add_one,Nat.mul_succ]
private theorem ccQ (q:ℕ) (hq:56≤q) :
    aPq q=HE (155-q) := by
  unfold aPq HE
  rw [Fin.sum_univ_eq_sum_range (fun j:ℕ=>JL j*(155 - q - j))]
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j _ hj
    have h:155 - q - j=0:= by
      simp only [Finset.mem_range] at hj
      omega
    rw [h,mul_zero]
private def gxo:Array (ℕ×ℕ) := #[
  (0,0),(1,1),(2,3),(4,7),(6,13),
  (10,23),(14,37),(20,57),(26,83),(35,118),
  (44,162),(56,218),(68,286),(84,370),(100,470),
  (120,590),(140,730),(165,895),(190,1085),(220,1305),
  (250,1555),(286,1841),(322,2163),(364, 2527),(406,2933),
  (455, 3388),(504,3892),(560,4452),(616,5068),(680,5748),
  (742,6490),(812,7302),(879,8181),(954,9135),(1026,10161),
  (1103,11264),(1178,12442),(1257,13699),(1334,15033),(1415,16448),
  (1494,17942),(1576,19518),(1658,21176),(1741, 22917),(1825,24742),
  (1909,26651),(1996,28647),(2080,30727),(2168,32895),(2254,35149),
  (2342,37491),(2429,39920),(2517,42437),(2605,45042),(2694,47736),
  (2781,50517),(2871,53388),(2958,56346),(3048,59394),(3135,62529),
  (3224,65753),(3312,69065),(3400,72465),(3487,75952),(3575,79527),
  (3661,83188),(3749,86937),(3833,90770),(3920,94690),(4004,98694),
  (4088,102782),(4171,106953),(4253,111206),(4335,115541),(4414,119955),
  (4495,124450),(4572,129022),(4651,133673),(4726,138399),(4803,143202),
  (4875,148077),(4950,153027),(5017,158044),(5087,163131),(5149,168280),
  (5213,173493),(5269,178762),(5325,184087),(5374,189461),(5423,194884),
  (5465,200349),(5507,205856),(5543,211399),(5579,216978),(5609,222587),
  (5639,228226),(5664, 233890),(5689,239579),(5709,245288),(5729,251017)]
private def bbD (n:ℕ) :ℕ×ℕ:=gxo[n]?.getD (0,0)
private theorem duW (n:ℕ) (hn:n<99) :
    bbD (n+1)=((bbD n).1+JL n,(bbD n).2+((bbD n).1+JL n)) := by
  interval_cases n <;> rfl
private theorem duQ (n:ℕ) (hn:n≤99) : (counts n,HE n)=bbD n:= by
  induction n with
  | zero=>rfl
  | succ n ih =>
    have h:=ih (by omega)
    have hcnt:counts (n+1)=counts n+JL n:= by
      exact zpB _ _
    rw [duW n (by omega),← h,cwU,hcnt]
private theorem duP (q:ℕ) (hlo:56≤q) (hhi:q≤111) :
    (bbD (155 - q)).2=qK9H6va.Ni q:= by
  interval_cases q <;> rfl
theorem c5v (q:ℕ) (hlo:56≤q) (hhi:q≤111) :
    aPq q=qK9H6va.Ni q:= by
  rw [ccQ q hlo]
  exact (congrArg Prod.snd (duQ (155 - q) (by omega))).trans (duP q hlo hhi)
end qHde8fc
end
section
set_option autoImplicit true
namespace qHde8fc
noncomputable section
open qK9H6va (XN iO Gy Oi offset)
open fP (lP m9 cF oG Qg)
open scoped BigOperators
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
theorem bu2 (q:ℕ) (hlo:56≤q) (hhi:q≤111) :
    iO q=56:= by
  unfold iO P6_6_1.asu
  split <;> omega
theorem Sj (e :aY) :cP (aD e.val)=56+e.val.weight m9:= by
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
  have hmap : (zLD Ground (zxp v)).map L≤S :=
    (Submodule.map_span_le _ _ _).mpr (by
      rintro _ ⟨j,rfl⟩
      exact hv j)
  exact hmap (Submodule.mem_map_of_mem (f :=L) hx)
private abbrev FF (q:ℕ) (g:ℤ) :=
  {j:Pivot // (c37 j:ℤ)<155 - q - g ∧ -g≤Nx j}
private def cGT (q:ℕ) (g:ℤ) (cut:ℕ) (hd:iO q=56)
    (hcut:cut≤(-g).toNat) :XN q g→ gU cut:= fun m =>
  ⟨m.val,m.property.1.trans hd,by
    have hlo:=m.property.2.1
    have hn:0≤(m.val.weight lP:ℤ) := by omega
    omega,m.property.2.2⟩
private theorem fTj (head:aGq 56 (tailCost - 1)) (tail:bTF)
    (q:ℕ) (g:ℤ) (hq:56≤q) (hq' : q≤111) :
    (Gy q g).rank≤zhP (FF q g) := by
  classical
  let v (j:FF q g) :=yv (κ:=XN q g) Subtype.val (Ug j.val)
  let S:=zLD Ground (zxp v)
  let ell:=(-g).toNat
  have hd:=bu2 q hq hq'
  by_cases hwide : (tailCost:ℤ)<155 - q - g
  · have hcut:tailCost - 98≤ell:= by dsimp only [ell]; omega
    by_cases hell:ell≤56
    · let f :=cGT q g ell hd le_rfl
      have hf :Function.Injective f := fun _ _ h =>
        Subtype.ext (congrArg (fun m:gU ell=>m.val) h)
      let addPivot (j:bk9 ell) :FF q g :=
        ⟨j.val,by
          have hc:=j.property.1
          omega,by
          have hj:=j.property.2
          dsimp only [ell] at hj
          omega⟩
      have hinj:Function.Injective addPivot:= fun _ _ h =>
        Subtype.ext (congrArg (fun j:FF q g=>j.val) h)
      exact (Gy q g).rank_le_card_width.trans
        ((Fintype.card_le_of_injective f hf).trans
          ((tail ell hcut hell).trans (Fintype.card_le_of_injective addPivot hinj)))
    · have hnot (m:XN q g) :False := by
        have hlo:=m.property.2.1
        have hhi:=m.property.2.2.1
        dsimp only [ell] at hell
        omega
      let:IsEmpty (XN q g) :=⟨hnot⟩
      exact (Gy q g).rank_le_card_width.trans (by simp)
  have hrows : ∀ n (e :aY),dZ e=n →
      (cP (aD e.val) :ℤ)<155 - q - g →
      yv (κ:=XN q g) Subtype.val (aD e.val)∈S:= by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro e he hweight
      let R:=cP (aD e.val)
      have hRlo:56≤R:= by dsimp only [R]; rw [Sj]; omega
      change (R:ℤ)<155 - q - g at hweight
      have hRhi:R≤tailCost - 1 := by omega
      have hRcut:R<99+ell:= by
        dsimp only [ell]
        omega
      obtain ⟨cut,hsmall,hdep⟩:=head e hRlo hRhi
      by_cases hcut:cut≤ell
      · exact EI (cGT q g cut hd hcut)
          (fun a :iw e=>cE cut (aD a.val.val)) _ S hdep (by
            intro a
            have hlt:=a.property.trans_le he.le
            have hle :=d0t a.property
            exact ih _ hlt a.val rfl (by omega))
      · rcases hsmall with hsmall | ⟨j,hj,hw,hik⟩
        · omega
        · have heng : -g≤Nx j:= by
            have hcut' : ell<cut:=Nat.lt_of_not_ge hcut
            dsimp only [ell] at hcut'
            omega
          have hmem:=Submodule.subset_span (R:=Ground)
            (Set.mem_range_self (f :=v) (⟨j,by rwa [hw],heng⟩:FF q g))
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
    change ((56+e.val.weight m9:ℕ) :ℤ)<155-(q:ℤ) - g
    omega)
private def eF3 (q:ℕ) (a :Σ r :Fin 155,FF q (offset r)) :
    Σ j:Pivot,Fin (155 - q - j.1.val) :=
  ⟨a.2.val,⟨(offset a.1+Nx a.2.val).toNat,by
    have hlo:=a.2.property.2
    have hhi:=a.2.property.1
    unfold Nx c37 at *
    omega⟩⟩
private theorem eF4 (q:ℕ) :zq4 (eF3 q) := by
  rintro ⟨r,j,hj⟩ ⟨s,k,hk⟩ h
  have hjk :j=k :=congrArg Sigma.fst h
  subst k
  have hval :=congrArg (fun t:Σ j:Pivot,Fin (155 - q - j.1.val)=>t.2.val) h
  change (offset r+Nx j).toNat=(offset s+Nx j).toNat at hval
  have hr :=hj.2
  have hs :=hk.2
  have hrs :r=s := by
    apply Fin.ext
    unfold offset at hr hs hval
    omega
  subst s
  rfl
theorem eiF (head:aGq 56 (tailCost - 1)) (tail:bTF)
    (q:ℕ) (hq:56≤q) (hq' : q≤111) :
    Oi q≤aPq q:= by
  classical
  calc
    _ ≤ ∑ r :Fin 155,zhP (FF q (offset r)) :=
      Finset.sum_le_sum fun r _=>fTj head tail q (offset r) hq hq'
    _=zhP (Σ r :Fin 155,FF q (offset r)) :=Fintype.card_sigma.symm
    _≤zhP (Σ j:Pivot,Fin (155 - q - j.1.val)) :=
      zWJ _ (eF4 q)
    _=aPq q:= by
      rw [zTU]
      simp only [Fintype.card_fin]
      unfold aPq
      rw [zla]
      refine zUo rfl fun k _ => ?_
      rw [zla,JL,Qg,Finset.sum_mul]
      simp [Finset.sum_const]
end
end qHde8fc
end
section
set_option autoImplicit true
namespace qHde8fc
open fP (lP xH cF qI Qg)
open scoped BigOperators
noncomputable section
private abbrev bi8 (cut:ℕ) :=
  Σ i:Fin 57,Σ f :Fin (min 16 (i.val/3)+1),
    Fin (if cut≤ i.val then (i.val-3*f.val)/2+1 else 0)
private def dNG (cut:ℕ) (m:gU cut) :bi8 cut:= by
  have hlo:=m.property.2.1
  have hhi:=m.property.2.2.1
  have htop:=m.property.2.2.2
  let i:=m.val.weight lP
  have hj:i=m.val 1+2*m.val 2 + 3*m.val 3:=xH _
  change (cut:ℤ)≤(i:ℤ) at hlo
  change (i:ℤ)≤56 at hhi
  have hcut:cut≤ i:= by omega
  have hf :m.val 3< min 16 (i/3)+1 := by omega
  refine ⟨⟨i,by omega⟩,⟨m.val 3,hf⟩,⟨m.val 2,?_⟩⟩
  change m.val 2<(if cut≤ i then (i-3*m.val 3)/2+1 else 0)
  rw [ite_eq_left hcut]
  omega
private theorem dNH (cut:ℕ) :zq4 (dNG cut) := by
  intro m n h
  have hi:m.val.weight lP=n.val.weight lP :=
    congrArg (fun s :bi8 cut=>s.1.val) h
  have hf :m.val 3=n.val 3:=congrArg (fun s :bi8 cut=>s.2.1.val) h
  have hc:m.val 2=n.val 2 :=congrArg (fun s :bi8 cut=>s.2.2.val) h
  rw [xH,xH] at hi
  have hm:=m.property.1
  have hn:=n.property.1
  rw [cF] at hm hn
  have hb:m.val 1=n.val 1 := by omega
  have ha :m.val 0=n.val 0:= by omega
  apply Subtype.ext
  apply Finsupp.ext
  intro j
  fin_cases j
  · exact ha
  · exact hb
  · exact hc
  · exact hf
private def bnB (i:ℕ) :ℕ :=
  qI (min 16 (i/3)+1) fun f=>(i-3*f)/2+1
private theorem dNB (cut:ℕ) :
    zhP (gU cut) ≤
      ∑ i:Fin 57,if cut≤ i.val then bnB i.val else 0:= by
  refine (zWJ _ (dNH cut)).trans_eq ?_
  simp only [bi8,zTU,Fintype.card_fin]
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
    _ = ∑ p:Pivot,if c37 p<tailCost∧(cut:ℤ)≤Nx p then 1 else 0:= by
      simp only [bk9,Fintype.card_subtype,Finset.sum_boole,Nat.cast_id]
    _ = ∑ k :Fin 99,∑ i:Fin 57,
          if cut≤ i.val∧k.val+i.val<tailCost then groupCount k.val i.val else 0:= by
      rw [zla]
      refine zUo rfl fun k _ => ?_
      rw [zla]
      refine zUo rfl fun i _ => ?_
      have hcast: ((cut:ℤ)≤(i.val :ℤ))↔cut≤ i.val := by omega
      simp only [c37,Nx,hcast]
      by_cases hi:cut≤ i.val <;> by_cases hk :k.val+i.val<tailCost <;> simp [hi,hk]
    _ = _:= by
      rw [Finset.sum_comm]
      refine zUo rfl fun i _ => ?_
      by_cases hi:cut≤ i.val <;> simp [hi,pivotCounts,Qg]
theorem tailWitness :bTF:= by
  classical
  intro cut hlo _
  refine (dNB cut).trans_eq ?_
  rw [tail_card]
  refine zUo rfl fun i _ => ?_
  by_cases hi:cut≤ i.val
  · simp only [hi,ite_true,pivotCounts_eq i.val (hlo.trans hi) (by omega)]
  · simp [hi]
end
end qHde8fc
end
section
set_option autoImplicit true
namespace qKhY0Ke
open qHde8fc
private def cNJ (g a f :ℕ) :Triple :=
  let c:=g-(4*a+2*f)
  (56-(a+c+f),c,f)
private theorem lookup (g a f :ℕ) (hg:g≤36) (hlo:4*a+2*f≤g)
    (hhi:g≤27+a) :
    f<groupCount g (56-a)∧ZX g (56-a) f=cNJ g a f := by
  have hal:g - 27≤a := by omega
  have hau:a≤g/4 := by omega
  have hfu:f≤(g-4*a)/2 := by omega
  clear hlo hhi
  interval_cases g <;> interval_cases a <;> interval_cases f <;> exact ⟨by decide,rfl⟩
theorem eLq (a b c f :ℕ) (hd:a+b+c+f=56) (h:3*a+c+2*f≤27) :
    ∃ j:Pivot,Ug j=(b,c,f)∧Nx j=(56-a :ℕ) ∧
      c37 j=56+(3*a+c+2*f) := by
  let g:=4*a+c+2*f
  have hg:g≤36:= by dsimp only [g]; omega
  have hj:=lookup g a f hg (by dsimp only [g]; omega) (by dsimp only [g]; omega)
  let j:Pivot:=⟨⟨g,by omega⟩,⟨⟨56-a,by omega⟩,⟨f,hj.1⟩⟩⟩
  have hrow:Ug j=(b,c,f) := by
    change ZX g (56-a) f=(b,c,f)
    rw [hj.2]
    have hc:g-(4*a+2*f)=c:= by dsimp only [g]; omega
    have hb:56-(a+c+f)=b:= by omega
    simp only [cNJ,hc,hb]
  refine ⟨j,hrow,rfl,?_⟩
  change g+(56-a)= _
  dsimp only [g]
  omega
end qKhY0Ke
end
