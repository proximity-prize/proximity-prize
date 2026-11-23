import ProximityPrize.SubmissionLower.ZCYrWLb
set_option Elab.async false
set_option autoImplicit true
namespace qQkHZQd
open qK9H6va qaTCFjd
open UO (bAQ)
open a0C (F Im RA HD size index z entry b1F aNl
  sumZero dfN dh8 weight glJ)
open fP (Ew cF xH oG
  qI Qg)
open private rU OZ from ProximityPrize.SubmissionLower.ZZBDV9b
open private order from ProximityPrize.SubmissionLower.CG
open scoped BigOperators Matrix
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
set_option maxRecDepth 3000
set_option maxHeartbeats 2500000
private def cV (s :Bool) :ℕ:=if s then 118 else 119
private def cap (s :Bool) :ℕ:=if s then 871 else 821
private def base (s :Bool) :ℕ:=if s then 16 else 19
private def top (s :Bool) :ℕ:=if s then 3 else 1
private def threshold (s :Bool) :=base s+2*top s
private def height (s :Bool) :=threshold s+12
private def U (s :Bool) (z f :ℕ) :Prop :=threshold s≤z∧top s≤f
private instance (s :Bool) (z f :ℕ) :Decidable (U s z f) :=
  inferInstanceAs (Decidable (_≤_∧_≤_))
private theorem upward (s :Bool) :bAQ (U s) := by
  intro z f z' f' hz _ hf h
  exact ⟨h.1.trans hz,h.2.trans hf⟩
private theorem degree_eq (s :Bool) :iO (cV s)=48:= by cases s <;> decide
private theorem cutoff (s :Bool) :DV (cV s) 3=height s := by cases s <;> decide
private theorem b6N (s :Bool) :2*base s+3*top s=41 := by cases s <;> decide
private abbrev R (s :Bool) :=ait (cV s) (offset 3)
private abbrev C (s :Bool) :=XN (cV s) (offset 3)
private abbrev B (s :Bool) :=Gy (cV s) (offset 3)
private abbrev P (s :Bool) :=ajZ (cV s) 3 (U s)
private abbrev Q (s :Bool) :=ajY (cV s) 3 (U s)
private abbrev PR (s :Bool) := {e // P s e}
private def terms (s :Bool) :RA:=if s then
  [((26,16,3),0x7efb3afe),((27,16,3),0x7e982544),((28,16,3),0x597d1a46),((29,16,3),0x7e4b56f9),
   ((25,17,3),44226),((26,17,3),2359044),((27,17,3),11517840),((28,17,3),0x36fd5432),
   ((24,18,3),0x7efff494),((25,18,3),0x7ef6da2d),((26,18,3),0x7eb21705),((27,18,3),0x7ea3189b),
   ((24,19,3),0x785274b7),((25,19,3),1769040),((26,19,3),3197394),((23,20,3),0x42d766c0),
   ((24,20,3),0x3f78d62a),((25,20,3),0x4c1e82f1),((22,21,3),0x17df4997),((23,21,3),0x3c29d49b),
   ((24,21,3),0x3f870547),((22,22,3),0x6aef6a1),((23,22,3),0x6af0a56a),((21,23,3),0x3c28701f),
   ((22,23,3),0x71a212bf),((20,24,3),0x4cde50aa),((21,24,3),0x281ae322),((20,25,3),0x5639f184),
   ((19,26,3),0x6af284e),((18,27,3),1)]
  else
  [((25,19,1),0x56cadb77),((26,19,1),0x68f0edd8),((27,19,1),0x657cb4fc),((28,19,1),0x5cfa56b3),
   ((24,20,1),0x2ecd48c9),((25,20,1),0x748271c),((26,20,1),0x66e70255),((27,20,1),0x5b12f660),
   ((23,21,1),0x49868e21),((24,21,1),0xd3cb56e),((25,21,1),0x55e1652f),((26,21,1),0x3b0f035b),
   ((23,22,1),0x3e0040c6),((24,22,1),0x68d29d94),((25,22,1),0x73f58128),((22,23,1),0x609d839f),
   ((23,23,1),0x1c8aaa8d),((24,23,1),0x67b8b833),((21,24,1),0x6af2e3c),((22,24,1),0x171a6916),
   ((23,24,1),0x7483b338),((21,25,1),0x281a90de),((22,25,1),0x7efc9e15),((20,26,1),0x6af2fef),
   ((21,26,1),0x42d83299),((19,27,1),74761558),((20,27,1),0x5d942032),((19,28,1),0x6f674e76),
   ((18,29,1),0x54aaaa8a),((17,30,1),1)]
private def pivot (s :Bool) :Im:=if s then (18,27,3) else (17,30,1)
private def agg (s :Bool) (t:Im) :Prop :=
  size t≤48∧3*(48 - size t)+z t<height s ∧
    56+(48 - size t)+3*(t.2.2 - 16)≤48+z t+3∧U s (z t) t.2.2
private instance (s :Bool) (t:Im) :Decidable (agg s t) := by
  unfold agg
  infer_instance
private theorem terms_ok (s :Bool) (a :Im×ℕ) (ha :a∈terms s) :
    agg s a.1∧a.1.2.2=top s := by
  have h: (terms s).all (fun a=>decide (agg s a.1∧a.1.2.2=top s))=true := by
    cases s <;> rfl
  exact of_decide_eq_true (List.all_eq_true.mp h a ha)
private theorem pivot_ok (s :Bool) :agg s (pivot s) := by cases s <;> decide
private theorem eLw (s :Bool) :weight (terms s) (pivot s)=1 := by cases s <;> rfl
private theorem row_real (s :Bool) {t:Im} (ht:agg s t) :
    ∃ a :PR s,HD a.val.val=t:= by
  obtain ⟨hs,hw,hr,hu⟩:=ht
  let e :=rU (48 - size t) t.1 t.2.1 t.2.2
  have hd:e.degree=iO (cV s) := by
    rw [cF,degree_eq]
    simp only [e,OZ]
    change (48 - size t)+t.1+t.2.1+t.2.2=48
    unfold size at hs ⊢
    omega
  have hrow:e.weight fP.m9<(Vm (cV s) (offset 3)).toNat := by
    rw [oG,aq6,cutoff]
    simpa [e,z,Nat.add_assoc] using hw
  let x :R s :=⟨e,hd,hrow⟩
  have hp:P s x := by
    change 56+e 0+3*(e 3 - 16)≤ iO (cV s)+order e+3 ∧
      U s (order e) (e 3)
    simpa [e,order,z,degree_eq] using And.intro hr hu
  exact ⟨⟨x,hp⟩,by simp [x,e,HD]⟩
private theorem zero_at (s :Bool) (j k :ℕ) (hj:j<8) (hk :k<4)
    (hjk :2*j≤12+k) :
    aNl (terms s) (12+k - 2*j,base s+j,top s)=0:= by
  cases s <;> interval_cases j <;> interval_cases k <;> rfl
private theorem brG (s :Bool) (m:C s) (hm : ¬ Q s m) :
    aNl (terms s) (HD m.val)=0:= by
  let t:=HD m.val
  change aNl (terms s) t=0
  by_cases h:t.2.2=top s∧base s≤t.2.1∧z t<height s
  · obtain ⟨hf,hb,_⟩:=h
    have hs :=m.property
    simp only [Ew,xH,show -offset 3=(53:ℤ) by decide] at hs
    have hlo:53≤ index t:= by exact_mod_cast hs.2.1
    have hhi:index t≤56:= by exact_mod_cast hs.2.2.1
    let j:=t.2.1 - base s
    let k :=index t - 53
    have hb' : t.2.1=base s+j:= by dsimp [j]; omega
    have hk' : index t=53+k := by dsimp [k]; omega
    have ht:=b6N s
    have hsum:t.1+2*j=12+k := by unfold index at hk'; omega
    have he :t=(12+k - 2*j,base s+j,top s) :=
      Prod.ext (by omega) (Prod.ext hb' hf)
    rw [he]
    exact zero_at s j k (by omega) (by omega) (by omega)
  · unfold aNl
    rw [sumZero _ _ (fun a ha => ?_),Nat.zero_mod]
    by_contra hn
    have hne :entry a.1 t≠0:= fun he=>hn (by rw [he,zero_mul])
    obtain ⟨_,hb,hf⟩:=b1F hne
    obtain ⟨hrow,htop⟩:=terms_ok s a ha
    have hw:=hrow.2.1
    have hz :z t<height s := by unfold z at hw ⊢; omega
    have hu:U s (z t) t.2.2 := by
      by_contra! hu
      apply hm
      change order m.val<DV (cV s) 3 ∧ ¬ U s (z t) t.2.2
      exact ⟨(cutoff s).symm ▸ hz,hu⟩
    obtain ⟨hth,hf'⟩:=hu
    exact h ⟨by omega,by unfold threshold at hth; unfold z at hth; omega,hz⟩
private def counts (s :Bool) :List ℕ:=if s then
  [0,0,0,0,0,3,8,12,20,20,24,24,28,28,32,32,36,36,40,40,44,44,48,48,52,42,45,44,30,25,26,13,14,14]
  else [0,0,0,0,0,3,8,12,20,20,24,24,28,28,32,32,36,36,40,40,44,44,48,48,40,40,43,29,29,28,15,15,16]
private def fiber (s :Bool) (z :ℕ) :ℕ :=
  qI (z/2+1) fun f =>
    if U s z f then aEG 48 (height s) 3 z f else aHb 48 3 z f
private theorem fiber_count (s :Bool) (z :ℕ) (hz :z<height s) :
    fiber s z=(counts s)[z]?.getD 0:= by
  cases s
  · change z<33 at hz
    interval_cases z <;> rfl
  · change z<34 at hz
    interval_cases z <;> rfl
private theorem cover_eq (s :Bool) :
    aht (iO (cV s)) (DV (cV s) 3) 3 (U s)=cap s+1 := by
  rw [degree_eq,cutoff]
  change qI (height s) (fiber s)= _
  calc
    _=qI (height s) (fun z=>(counts s)[z]?.getD 0) := by
      simp only [Qg]
      exact Finset.sum_congr rfl fun z _=>fiber_count s z z.isLt
    _ = _:= by cases s <;> rfl
private theorem wq (s :Bool) (e :R s) (m:C s) :
    (entry (HD e.val) (HD m.val) :F)=B s e m:= by
  simp only [B,Gy,prefixMatrix,HD,entry,Nat.cast_mul,ju.n9,
    Nat.choose_eq_descFactorial_div_factorial]
private theorem block (s :Bool) :KC (cV s) 3 (cap s) := by
  classical
  obtain ⟨p,hp⟩:=row_real s (pivot_ok s)
  let v :Matrix (PR s) (Fin 1) F:= fun a _=>weight (terms s) (HD a.val.val)
  have hv :v.submatrix (fun _:Fin 1=>p) id = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    change (weight (terms s) (HD p.val.val) :F)=(1 :Matrix (Fin 1) (Fin 1) F) 0 0
    rw [hp,eLw]
    simp
  let g:PR s→Fin 4 →₀ ℕ:= fun a=>a.val.val
  have hi:=dh8 g (Subtype.val_injective.comp Subtype.val_injective)
    (iO (cV s)) (fun a=>a.val.property.1)
  have hrel (m:C s) (hm : ¬ Q s m) (i:Fin 1) :
      (∑ a :PR s,B s a.val m*v a i)=0:= by
    have hsum:=dfN (HD ∘ g) hi (fun t=>entry t (HD m.val)) (terms s)
      (fun a ha=>row_real s (terms_ok s a ha).1)
    change _=(aNl (terms s) (HD m.val) :F) at hsum
    rw [brG s m hm,Nat.cast_zero] at hsum
    simpa only [g,Function.comp_apply,wq,v] using hsum
  have h:=glJ (B s) (P s) (Q s) (aEb (cV s) 3 _ (upward s)) v
    (fun _=>p) hv hrel
  exact Nat.le_of_add_le_add_right ((h.trans (aHj (cV s) 3 (U s))).trans_eq (cover_eq s))
theorem proof :qaTCFjd.c4 :=⟨block true,block false⟩
end
end qQkHZQd
