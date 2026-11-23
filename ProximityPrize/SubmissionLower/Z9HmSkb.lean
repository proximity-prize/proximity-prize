import ProximityPrize.SubmissionLower.Z3gZttb
import ProximityPrize.SubmissionLower.ZJHC8Rc
import ProximityPrize.SubmissionLower.ZCqrzHc
import ProximityPrize.SubmissionLower.AZ
import ProximityPrize.SubmissionLower.ZGSvmVd
import ProximityPrize.SubmissionLower.ZXrG2Fd
set_option Elab.async false
open _root_ renaming Finset.card_union_le → z2s, Finset.filter_subset → zT0, Finset.mem_union_left → zDk, Finset.mem_union_right → zMj, Finset.sum_apply → zpH, MvPolynomial.eval → zY9, Nat.add_le_add → z9f, Nat.add_le_add_right → zlr, Nat.choose_eq_zero_of_lt → zsx
section
set_option autoImplicit true
namespace qeUg7Fa
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
local notation "r!" z "," p=>asA (v :=z) (by rfl) p
private theorem r1 :total 2795 12=0x1b6c8adbde60 :=
  r! 0x24e3d8681a0,r! 0x24d4aa7b0e0,r! 0x24c58e7dcd0,r! 0x24b664c27f0,
  r! 0x24a74f36fc0,r! 0x24982ee22c0,r! 0x24891d419c0,r! 0x247a03aaad0,
  r! 0x246af8992a0,r! 0x245be5c4db0,r! 0x244ce504750,r! 0x243dd532870,
  rfl
private theorem r2 :total 2807 12=0x1ae570482ae0 :=
  r! 0x242edadea50,r! 0x241fd3bd4c0,r! 0x2410de0d460,r! 0x2401dea4840,
  r! 0x23f2ee92290,r! 0x23e3f5ec7f0,r! 0x23d50f047e0,r! 0x23c61a87bf0,
  r! 0x23b73b77e10,r! 0x23a84e55de0,r! 0x239973da6d0,r! 0x238a8d81e20,
  rfl
private theorem r3:total 2819 11=0x18322aeb4b00 :=
  r! 0x237bb9953c0,r! 0x236cdb32980,r! 0x235e0f53520,r! 0x234f3510660,
  r! 0x23406fa34d0,r! 0x23319e25210,r! 0x2322deec2e0,r! 0x231412a2020,
  r! 0x23055cb9790,r! 0x22f69479a20,r! 0x22e7e4ff6b0,rfl
theorem asc:total 2795 35=0x4e84260f5440 :=
  (total_append r1 (total_append r2 r3))
end qeUg7Fa
end
section
set_option autoImplicit true
namespace qYFuqQa
theorem proof :q8kxiJa.c1 := by
  intro J p boxes hlen hp hboxes hdim D hD hreg
  exact bau.proof J p boxes hp hboxes (hlen.trans (by decide)) hdim D hD hreg
end qYFuqQa
end
section
set_option autoImplicit true
namespace qWT1c9b
theorem proof :q8kxiJa.c3:= by
  intro R r q b h hR hr hq hb hh
  have hbound:=qZqYIua.literal_bound R r q b h hR hr hq hb hh
  simpa only [mul_comm (32 :ℚ)] using
    (le_div_iff₀ (by norm_num : (0:ℚ)<32)).mp hbound
end qWT1c9b
end
section
set_option autoImplicit true
namespace qtt0Wue
open qwzqCne
open fP (cF xH oG)
open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem cast_ne_zero {n:ℕ} (hn:0<n) (h:n≤56) :
    (n:Ground)≠0:= by
  intro hz
  have hn' : n<P1.p:=h.trans_lt (by decide)
  have hv :=congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt hn',ZMod.val_zero] at hv
  omega
private theorem shifted_pascal_span (k l s a :ℕ) (hl:k≤l) (h:l+s+a≤50+k)
    (hsize :l+s+a≤57) (y :Fin a→Ground) :
    ∃ u:Fin a→Ground,∀ j:Fin a,
      (∑ i:Fin a,u i*((l+s+i.val).choose (l+j.val) :Ground))=y j:= by
  induction k generalizing l y with
  | zero=>exact bAj.a6t l s a (by omega) y
  | succ k ih =>
    cases l with
    | zero=>omega
    | succ l =>
      let C (i:Fin a) :Ground :=(l+s+i.val+1 :ℕ)
      let D (j:Fin a) :Ground :=(l+j.val+1 :ℕ)
      have hC (i:Fin a) :C i≠0 :=
        cast_ne_zero (n:=l+s+i.val+1) (by omega) (by omega)
      have hD (j:Fin a) :D j≠0 :=
        cast_ne_zero (n:=l+j.val+1) (by omega) (by omega)
      have hscale (i j:Fin a) :
          ((l.succ+s+i.val).choose (l.succ+j.val) :Ground)*D j =
            C i*((l+s+i.val).choose (l+j.val) :Ground) := by
        have hc:=congrArg (fun n:ℕ=>(n:Ground))
          (Nat.add_one_mul_choose_eq (l+s+i.val) (l+j.val))
        simp only [Nat.cast_mul] at hc
        rw [show l.succ+s+i.val=l+s+i.val+1 by omega,
          show l.succ+j.val=l+j.val+1 by omega]
        exact hc.symm
      obtain ⟨w,hw⟩:=ih l (by omega) (by omega) (by omega) (fun j=>y j*D j)
      refine ⟨fun i=>w i/C i,fun j=>mul_right_cancel₀ (hD j) ?_⟩
      rw [Finset.sum_mul,← hw j]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc,hscale,← mul_assoc,div_mul_cancel₀ _ (hC i)]
private def exponent (b c f :ℕ) :Exponent :=
  Finsupp.equivFunOnFinite.symm ![54-(b+c+f),b,c,f]
@[simp] private theorem ayO (b c f :ℕ) (j:Fin 4) :
    exponent b c f j = ![54-(b+c+f),b,c,f] j:= by
  simp [exponent]
private def kg (b c f :ℕ) (h:b+c+f≤54) :aY :=
  ⟨exponent b c f,by simp [cF]; omega⟩
private theorem aNn {e v :aY}
    (h:cP (aD v.val)<cP (aD e.val)) :
    dZ v<dZ e := by
  have hd:=v.property
  rw [cF] at hd
  unfold dZ
  omega
private theorem i7 {cut:ℕ} (m:gU cut) :
    cut≤ m.val 1+2*m.val 2 + 3*m.val 3 ∧
      m.val 1+2*m.val 2 + 3*m.val 3≤54+min 2 (m.val 2+2*m.val 3) := by
  obtain ⟨hd,hl,hu,_⟩:=m.property
  rw [cF] at hd
  rw [xH] at hl hu
  have h56:m.val 1+2*m.val 2 + 3*m.val 3≤56:= by exact_mod_cast hu
  exact ⟨by exact_mod_cast hl,by omega⟩
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
private theorem R0 {ι:Type*} [Fintype ι] [DecidableEq ι]
    (S:Submodule Ground (ι→Ground)) (v :ι→Ground)
    (h : ∀ m,v m≠0→Pi.single m (1 :Ground)∈S) :v∈S:= by
  have hsum: (∑ m,v m•Pi.single m (1 :Ground))=v := by
    funext n
    simp [zpH,Pi.single_apply,smul_eq_mul,mul_ite]
  rw [← hsum]
  apply S.sum_mem
  intro m _
  by_cases hm:v m=0
  · simp [hm]
  · exact S.smul_mem _ (h m hm)
private theorem iN {cut b c f :ℕ} (m:gU cut)
    (h:c< m.val 2∨f< m.val 3) :cE cut (b,c,f) m=0:= by
  rcases h with h | h
  · simp [cE,yv,zsx h]
  · simp [cE,yv,zsx h]
private theorem c5k (e :aY)
    (hweight:3*e.val 0+e.val 2+2*e.val 3≤28) :
    cE (55+min 2 (e.val 2+2*e.val 3)-e.val 0) (aD e.val) ∈
      Submodule.span Ground (Set.range fun v :iw e =>
        cE (55+min 2 (e.val 2+2*e.val 3)-e.val 0) (aD v.val.val)) := by
  classical
  let a :=e.val 0
  let s₀:=e.val 2+2*e.val 3
  let k₀:=min 2 s₀
  let cut:=55+k₀-a
  let S:=Submodule.span Ground
    (Set.range fun v :iw e=>cE cut (aD v.val.val))
  change cE cut (aD e.val)∈S
  replace hweight:3*a+s₀≤28:= by dsimp only [a,s₀]; omega
  have hcut:cut+a=55+k₀:= by dsimp only [cut]; omega
  have hbox :2*e.val 2 + 3*e.val 3≤ cut:= by
    dsimp only [k₀,s₀] at hcut hweight
    omega
  have abO (r :ℕ) : ∀ m:gU cut,m.val 2+m.val 3=r →
      m.val 2≤e.val 2→m.val 3≤e.val 3→Pi.single m (1 :Ground)∈S:= by
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro m hr hc hf
      let c:=m.val 2
      let f :=m.val 3
      let s :=c+2*f
      let k :=min 2 s
      let l:=cut - (2*c+3*f)
      let A:=55+k - cut
      have hs :s≤ s₀:= by dsimp only [s,s₀,c,f]; omega
      have hk :k≤k₀:=min_le_min_left _ hs
      have hks :k≤ s :=min_le_right _ _
      have hl:l+2*c+3*f=cut:= by dsimp only [l,c,f]; omega
      have hA:cut+A=55+k := by
        have hm:=(i7 m).1.trans (i7 m).2
        change cut≤54+k at hm
        dsimp only [A]
        omega
      have hls :l+(s - k)+A+c+f=55:= by dsimp only [s] at hs ⊢; omega
      let w (i:Fin A) :aY:=kg (l+(s - k)+i.val) c f (by omega)
      have hw (i:Fin A) :aD (w i).val=(l+(s - k)+i.val,c,f) := by
        simp [w,kg,aD]
      have hwEarlier (i:Fin A) :dZ (w i)<dZ e := by
        apply aNn
        rw [Sj,Sj,oG,oG]
        change 54+(3*(54-(l+(s - k)+i.val+c+f))+c+2*f) <
          54+(3*a+e.val 2+2*e.val 3)
        dsimp only [s,s₀] at hs
        omega
      let y (j:Fin A) :Ground :=if l+j.val=m.val 1 then 1 else 0
      let shift:=5-(c+f)
      have hshift:shift≤l:= by dsimp only [s] at hs; dsimp only [shift]; omega
      obtain ⟨u,hu⟩:=shifted_pascal_span shift l (s - k) A hshift
        (by dsimp only [shift]; omega) (by omega) y
      let W := ∑ i:Fin A,u i•cE cut (l+(s - k)+i.val,c,f)
      have hW:W∈S:= by
        apply S.sum_mem
        intro i _
        apply S.smul_mem
        have hi:cE cut (aD (w i).val)∈S :=
          Submodule.subset_span ⟨⟨w i,hwEarlier i⟩,rfl⟩
        rwa [hw i] at hi
      have hOutside (n:gU cut) (hn:c<n.val 2∨f<n.val 3) :
          W n=0:= by
        simp [W,zpH,iN n hn]
      let δ:gU cut→Ground :=Pi.single m (1 :Ground)
      have hMatch (n:gU cut) (hnc:n.val 2=c) (hnf :n.val 3=f) :
          W n=δ n:= by
        obtain ⟨hlo,hhi⟩:=i7 n
        rw [hnc,hnf] at hlo hhi
        change n.val 1+2*c+3*f≤54+k at hhi
        let j:Fin A:=⟨n.val 1-l,by omega⟩
        have hj:l+j.val=n.val 1 := by dsimp [j]; omega
        have hvalue :W n=y j:= by
          simpa [W,zpH,cE,yv,hnc,hnf,← hj,smul_eq_mul] using hu j
        rw [hvalue]
        change (if l+j.val=m.val 1 then 1 else 0)= _
        rw [hj]
        by_cases hnm:n=m
        · subst n
          simp [δ]
        · have hfirst:n.val 1≠m.val 1 := fun h =>
            hnm (a2O h hnc hnf)
          simp [hfirst,δ,hnm]
      let rem:=δ-W
      have hrem:rem∈S:= by
        apply R0 S
        intro n hn
        have hinside :n.val 2≤ c∧n.val 3≤f := by
          by_contra hnle
          have hout:c<n.val 2∨f<n.val 3:= by omega
          have hnm:n≠m:= by
            intro h
            subst n
            simp [c,f] at hout
          apply hn
          change δ n-W n=0
          rw [hOutside n hout]
          simp [δ,hnm]
        have hlt:n.val 2+n.val 3< r := by
          by_contra hlt
          have hnc:n.val 2=c:= by omega
          have hnf :n.val 3=f := by omega
          apply hn
          change δ n-W n=0
          rw [hMatch n hnc hnf,sub_self]
        exact ih _ hlt n rfl (hinside.1.trans hc) (hinside.2.trans hf)
      have hsum:=S.add_mem hrem hW
      change δ-W+W∈S at hsum
      rwa [sub_add_cancel] at hsum
  apply R0 S
  intro m hm
  have hle :m.val 2≤e.val 2∧m.val 3≤e.val 3:= by
    by_contra hn
    exact hm (iN m (by omega))
  exact abO _ m rfl hle.1 hle.2
private def cNJ (w a f :ℕ) :Triple :=
  let c:=w-(54+3*a+2*f)
  (54-(a+c+f),c,f)
private theorem lookup_edge (a k :ℕ) (ha :a≤9) (hk :k<2) :
    0<groupCount (4*a) (54+k-a) ∧
      ZX (4*a) (54+k-a) 0=(54-(a+k),k,0) := by
  interval_cases a <;> interval_cases k <;> exact ⟨by decide,rfl⟩
private theorem lookup_main (g a f :ℕ) (hg:g≤34) (hl:4*a≤g)
    (hf :4*a+2*f≤g+2) (hh:g≤26+a) :
    f<groupCount g (56-a)∧ZX g (56-a) f=cNJ (g+(56-a)) a f := by
  have hal:g - 26≤a := by omega
  have hau:a≤g/4 := by omega
  have hfu:f≤(g+2 - 4*a)/2 := by omega
  clear hl hf hh
  interval_cases g <;> interval_cases a <;> interval_cases f <;> exact ⟨by decide,rfl⟩
private theorem eLq (a b c f :ℕ) (hd:a+b+c+f=54)
    (h:3*a+c+2*f≤28) :
    ∃ j:Pivot,Ug j=(b,c,f) ∧
      Nx j=(54+min 2 (c+2*f)-a :ℕ) ∧
      c37 j=54+(3*a+c+2*f) := by
  let k :=min 2 (c+2*f)
  let i:=54+k-a
  let g:=4*a+c+2*f - k
  have hi:i+a=54+k := by dsimp only [i]; omega
  have hk :k≤ c+2*f :=min_le_right _ _
  have hcost:g+i=54+(3*a+c+2*f) := by dsimp only [g]; omega
  have hj:f<groupCount g i∧ZX g i f=(b,c,f) := by
    by_cases hs :2≤ c+2*f
    · have hk2 :k=2 :=min_eq_left hs
      have he :i=56-a := by simp [i,hk2]
      have hg:g≤34 := by dsimp only [g]; omega
      obtain ⟨hn,hr⟩:=lookup_main g a f hg
        (by dsimp only [g]; omega) (by dsimp only [g]; omega) (by dsimp only [g]; omega)
      rw [← he] at hn hr
      have hc:g+i-(54+3*a+2*f)=c:= by omega
      refine ⟨hn,hr.trans ?_⟩
      simp only [cNJ,hc,show 54-(a+c+f)=b by omega]
    · have hkc:k=c:= by dsimp only [k]; omega
      have hf :f=0:= by omega
      have he :g=4*a := by dsimp only [g]; omega
      obtain ⟨hn,hr⟩:=lookup_edge a k (by omega) (by omega)
      rw [he,hf]
      exact ⟨hn,by
        change ZX (4*a) (54+k-a) 0=(b,c,0)
        rw [hr,hkc]
        simp only [show 54-(a+c)=b by omega]⟩
  let j:Pivot:=⟨⟨g,by dsimp only [g]; omega⟩,⟨⟨i,by dsimp only [k] at hi; omega⟩,⟨f,hj.1⟩⟩⟩
  exact ⟨j,hj.2,rfl,hcost⟩
theorem proof :qwzqCne.c1 := by
  intro e _ hhi
  let a :=e.val 0
  let b:=e.val 1
  let c:=e.val 2
  let f :=e.val 3
  have hd:a+b+c+f=54 := by simpa only [cF] using e.property
  have hcost:cP (aD e.val)=54+(3*a+c+2*f) := by
    rw [Sj,oG]
  have hweight:3*a+c+2*f≤28:= by omega
  obtain ⟨j,hj,hi,hw⟩:=eLq a b c f hd hweight
  refine ⟨55+min 2 (c+2*f)-a,Or.inr ⟨j,hj,hw.trans hcost.symm,?_⟩,
    c5k e hweight⟩
  rw [hi]
  omega
end
end qtt0Wue
end
section
set_option autoImplicit true
set_option Elab.async false
namespace P6_6_6
noncomputable section
open aR wH axh Polynomial
open jA (qV H9 Qu jW)
open P6_6 (aPr aWz mu tau)
open private bCl bJE bCk c5L from ProximityPrize.SubmissionLower.E5
theorem dDO (E :P6_6.aw1) :
    ∃ D P Q:af 3,D ≠0∧Gh D Kq.b Kq.j ∧
      Gh P IG.b IG.j∧Gh Q IG.b IG.j ∧
      bbj P Q ∧ ∀ S:ao[X],E.bqU S →
        cK D S=0∨(wU P S mu∧wU Q S Fw) := by
  let R:=MvPolynomial.map qV E.residual
  have hsR:E.residual.support=R.support :=(crY _).symm
  have hnR:R≠0:=(map_ne_zero_iff _ (MvPolynomial.map_injective _ al5)).mpr E.residual_ne
  have hbR:R.totalDegree≤aPr := by
    simpa only [MvPolynomial.totalDegree,hsR] using E.residual_total
  have hjR:H9 R≤aWz := by
    simpa only [H9,qE,hsR] using E.residual_index
  obtain ⟨H,A,P,hnH,hnP,heq,hdiv,hbH,hjH,hbP,hjP,hlow⟩ :=
    cyO.proof R hnR aPr aWz tau (by decide) hbR hjR
  obtain ⟨Q,hnQ,hbQ,hjQ,hrel,horderQ⟩:=ePB P hnP hbP hjP hlow
  obtain ⟨dH,H',_,hsH,hmH⟩:=afo H
  obtain ⟨dP,P',hdP,hsP,hmP⟩:=afo P
  obtain ⟨dQ,Q',hdQ,hsQ,hmQ⟩:=afo Q
  have hnH' := bJE hsH hnH
  have hcap:Gh (E.common*H') Kq.b Kq.j :=
    bCk E.common_ne hnH' ⟨E.common_total,E.common_index⟩
      (bCl hsH hbH hjH)
  refine ⟨E.common*H',P',Q',mul_ne_zero E.common_ne hnH',hcap,
    bCl hsP hbP hjP,bCl hsQ hbQ hjQ,
    ⟨bJE hsP hnP,bJE hsQ hnQ,c5L hnP hnQ hrel hdP hdQ hmP hmQ⟩,?_⟩
  intro S hS
  by_cases hd:cK (E.common*H') S=0
  · exact Or.inl hd
  right
  have hc:cK E.common S≠0:= fun h=>hd (by
    simp [cK,show zY9 (jet S) E.common=0 from h])
  have hHval :zY9 (jW S) H≠0:= by
    intro hz
    have hh:=aC5 H' S
    rw [hmH,map_mul,hz,mul_zero] at hh
    have hz' : cK H' S=0:=al5 (hh.symm.trans (map_zero _).symm)
    exact hd (by simp [cK,show zY9 (jet S) H' = 0 from hz'])
  have hAval :zY9 (jW S) A≠0:= by
    have hh:=map_dvd (zY9 (jW S)) hdiv
    rw [map_pow] at hh
    intro hz
    exact pow_ne_zero _ hHval (zero_dvd_iff.mp (hz ▸ hh))
  have hRord:Qu R (jW S) mu :=
    (c2I E.residual S _).mpr (hS.resolve_left hc)
  rw [heq] at hRord
  have hPord:=aIJ hAval hRord
  exact ⟨c2B hdP hmP S hPord,c2B hdQ hmQ S (horderQ _ hPord)⟩
end
end P6_6_6
end
section
set_option autoImplicit true
set_option Elab.async false
namespace P6_6_6
noncomputable section
open Polynomial
open P6 (K)
open P6_6 (Messages wm acX)
open aR (af cK embed extend Dd shape)
open wH (qg Gh bbj Ud cY3)
def c1 :Prop :=
  ∀ w Γ s,Messages w Γ s → ∀ f,wm f→acX (shape f) →
    (∀ γ∈Γ,Dd f (extend (s γ)) ∧ ¬ qg f (extend (s γ))) →
    Γ.card≤bwr (shape f)
def c2 :Prop :=
  ∀ w Γ s,Messages w Γ s → ∀ f,wm f→acX (shape f) →
    (∀ γ∈Γ,Dd f (extend (s γ))∧qg f (extend (s γ))) →
    ∀ D:af 3,D ≠0→Gh D Kq.b Kq.j →
      (∀ γ∈Γ,cK D (extend (s γ))=0)→Γ.card≤bHL (shape f)
def c3:Prop :=
  ∀ w Γ s,Messages w Γ s → ∀ f,wm f→acX (shape f) →
    (∀ γ∈Γ,Dd f (extend (s γ))∧qg f (extend (s γ))) →
    ∀ P Q:af 3,bbj P Q →
      Gh P IG.b IG.j→Gh Q IG.b IG.j →
      (∀ γ∈Γ,bac P Q (Ud (extend (s γ)))) →
      Γ.card≤bHH (shape f)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :P6_6.c6:= by
  classical
  intro w Γ s hmsg f hf hon helig E hE
  obtain ⟨D,P,Q,hD,hDb,hPb,hQb,hpq,hres⟩:=dDO E
  obtain ⟨R,hRb,hstrata⟩:=fWI P Q hpq hPb hQb
  let S:K→aR.ao[X] := fun γ=>extend (s γ)
  let singular :=Γ.filter (fun γ => ¬ qg f (S γ))
  let divisors :=Γ.filter (fun γ=>qg f (S γ)∧cK D (S γ)=0)
  let qv :=Γ.filter (fun γ=>qg f (S γ)∧bac P Q (Ud (S γ)))
  let isolated:=Γ.filter (fun γ=>bzn P Q R (Ud (S γ)))
  have hsingular :singular.card≤bwr (shape f) :=
    h1 w singular s (hmsg.mono (zT0 _ _)) f hf helig
      (fun γ hγ=>⟨hon γ (Finset.mem_filter.mp hγ).1,(Finset.mem_filter.mp hγ).2⟩)
  have hdivisors :divisors.card≤bHL (shape f) :=
    h2 w divisors s (hmsg.mono (zT0 _ _)) f hf helig
      (fun γ hγ=>⟨hon γ (Finset.mem_filter.mp hγ).1,(Finset.mem_filter.mp hγ).2.1⟩)
      D hD hDb (fun _ hγ=>(Finset.mem_filter.mp hγ).2.2)
  have hcurves :qv.card≤bHH (shape f) :=
    h3 w qv s (hmsg.mono (zT0 _ _)) f hf helig
      (fun γ hγ=>⟨hon γ (Finset.mem_filter.mp hγ).1,(Finset.mem_filter.mp hγ).2.1⟩)
      P Q hpq hPb hQb (fun _ hγ=>(Finset.mem_filter.mp hγ).2.2)
  have hisolated:isolated.card≤brg:= by
    let points :=isolated.image (fun γ=>Ud (S γ))
    have hinj:Set.InjOn (fun γ=>Ud (S γ)) (isolated:Set K) := by
      intro a ha b hb hab
      exact hmsg.distinct (zT0 _ _ ha) (zT0 _ _ hb)
        (Polynomial.map_injective embed embed.injective (cY3 hab))
    have hcard:points.card=isolated.card:=Finset.card_image_of_injOn hinj
    rw [← hcard]
    apply epf P Q R hPb hQb hRb points
    intro y hy
    obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hγ).2
  have hcover :Γ⊆divisors∪singular∪qv∪isolated:= by
    intro γ hγ
    by_cases hr :qg f (S γ)
    · rcases hres (S γ) (hE γ hγ) with hd | ⟨hp,hq⟩
      · exact zDk _ (zDk _
          (zDk _ (Finset.mem_filter.mpr ⟨hγ,hr,hd⟩)))
      · rcases hstrata (S γ) hp hq with hc | hi
        · exact zDk _ (zMj _
            (Finset.mem_filter.mpr ⟨hγ,hr,hc⟩))
        · exact zMj _ (Finset.mem_filter.mpr ⟨hγ,hi⟩)
    · exact zDk _ (zDk _
        (zMj _ (Finset.mem_filter.mpr ⟨hγ,hr⟩)))
  rw [d9C]
  calc
    Γ.card≤(divisors∪singular∪qv∪isolated).card:=Finset.card_le_card hcover
    _≤(divisors∪singular∪qv).card+isolated.card:=z2s _ _
    _≤(divisors∪singular).card+qv.card+isolated.card :=
      zlr (z2s _ _) _
    _≤divisors.card+singular.card+qv.card+isolated.card :=
      zlr (zlr (z2s _ _) _) _
    _≤_:=z9f (z9f (z9f hdivisors hsingular) hcurves) hisolated
end
end P6_6_6
end
