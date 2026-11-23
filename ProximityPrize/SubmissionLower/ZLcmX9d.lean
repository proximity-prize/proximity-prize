import ProximityPrize.SubmissionLower.Zx0Npsd
import ProximityPrize.SubmissionLower.ZxJP4ta
import ProximityPrize.SubmissionLower.ZikYn6c
import ProximityPrize.SubmissionLower.ZF5THYd
import ProximityPrize.SubmissionLower.ZXxMpWa
import ProximityPrize.SubmissionLower.ZzeWNbd
import ProximityPrize.SubmissionLower.Z7T9FDe
set_option Elab.async false
section
set_option autoImplicit true
namespace q1jcGec
open qK9H6va
set_option maxRecDepth 4000
private theorem checked (q u cols rows budget:ℕ) (hq:q≤46) (hu:u≤155)
    (hc:bC5 q u=cols) (hr :bvj q q u=rows) (hb:Ni q=budget)
    (h:cols+rows≤budget) :Oi q≤Ni q:= by
  have hd:iO q=q:= by
    unfold iO P6_6_1.asu
    rw [ite_eq_left (show q≤111 by omega)]
    exact min_eq_left (by omega)
  have hcaps :=eiM q u hu
  rw [hd,hc,hr] at hcaps
  rw [hb]
  exact hcaps.trans h
local notation "az" q "," u "," c "," r "," b =>
  checked q u c r b (by decide) (by decide) (by decide) (by decide) rfl (by decide)
theorem proof :qK9H6va.c1 := by
  intro q hq
  interval_cases q
  · exact az 0,56,0,99,99
  · exact az 1,56,6,386,392
  · exact az 2,56,30,940,970
  · exact az 3,56,90,1830,1920
  · exact az 4,56,210,3115, 3325
  · exact az 5, 56,420,4844,5264
  · exact az 6,56,756,7056,7812
  · exact az 7,56,1260,9780,11040
  · exact az 8,56,1980,13035,15015
  · exact az 9,56,2970,16830,19800
  · exact az 10,56,4290,21164, 25454
  · exact az 11,56,6006,26026,32032
  · exact az 12,56,8190,31395, 39585
  · exact az 13,56,10920,37240,48160
  · exact az 14,56,14280,43520,57800
  · exact az 15, 56,18360,50184,68544
  · exact az 16,56,23256,57171,80427
  · exact az 17,56,29019,64379,93398
  · exact az 18,56,35700,71706,107406
  · exact az 19,56,43350,79050,122400
  · exact az 20,79,92293,46036,138329
  · exact az 21,78,105281,49627,154908
  · exact az 22,77,118723,53064,171787
  · exact az 23,76,132316,56316,188632
  · exact az 24,75,145765, 59360,205125
  · exact az 25,74,158783,62181, 220964
  · exact az 26,73,171165,64771, 235936
  · exact az 27,72,182638,67130,249768
  · exact az 28,71,193009,69265,262274
  · exact az 29,70,202090,71190,273280
  · exact az 30,69,209981,72919,282900
  · exact az 31,68,216710,74466,291176
  · exact az 32,67,222373,75844, 298217
  · exact az 33,66,226996,77066,304062
  · exact az 34,65,230671,78144,308815
  · exact az 35,64, 233422,79090,312512
  · exact az 36,63,235337,79915, 315252
  · exact az 37,62,236438,80630,317068
  · exact az 38,61, 236809,81245, 318054
  · exact az 39,60,236470,81770,318240
  · exact az 40,59,235501,82214,317715
  · exact az 41,58,233920,82586,316506
  · exact az 42,57,231803,82894,314697
  · exact az 43,56,229166,83146,312312
  · exact az 44,55,226082,83349,309431
  · exact az 45, 54, 222565,83510,306075
  · exact az 46,53,218684,83635, 302319
end q1jcGec
end
section
set_option autoImplicit true
namespace qxuyiwe
open qK9H6va
open scoped BigOperators
private theorem charge_eq_sum (n:ℕ) (hist:List ℕ) :
    (∑ i:Fin hist.length,hist[i.val]*(n - i.val))=charge n hist:= by
  induction hist generalizing n with
  | nil=>simp [charge]
  | cons c cs ih =>
    simp only [List.length_cons,Fin.sum_univ_succ,Fin.val_zero,List.getElem_cons_zero,
      Nat.sub_zero,Fin.val_succ,List.getElem_cons_succ,charge,← ih]
    congr 1
    exact Finset.sum_congr rfl fun i _=>congrArg (fun k=>cs[i.val]*k) (by omega)
private def eF3 {hist:List ℕ} (ix :PivotIndex hist) (q d:ℕ)
    (a :Σ r :Fin 155,FF ix (offset r) (profileCutoff q d (offset r))) :
    Σ j:Pivot hist,Fin (99+d - q - j.1.val) :=
  ⟨a.2.val,⟨(offset a.1+(ix a.2.val).val).toNat,by
    have hlo:=a.2.property.2
    have hhi:=a.2.property.1
    unfold profileCutoff Vm at hhi
    omega⟩⟩
private theorem eF4 {hist:List ℕ} (ix :PivotIndex hist) (q d:ℕ) :
    Function.Injective (eF3 ix q d) := by
  rintro ⟨r,j,hj⟩ ⟨s,k,hk⟩ h
  have hjk :j=k :=congrArg Sigma.fst h
  subst k
  have hval :=congrArg (fun t:Σ j:Pivot hist,Fin (99+d - q - j.1.val)=>t.2.val) h
  change (offset r+(ix j).val).toNat=(offset s+(ix j).val).toNat at hval
  have hr :=hj.2
  have hs :=hk.2
  have hrs :r=s := by
    apply Fin.ext
    unfold offset at hr hs hval
    omega
  subst s
  rfl
theorem grade_le_charge {d q:ℕ} {hist:List ℕ} (h:Profile d hist)
    (hd:iO q=d) :Oi q≤ charge (99+d - q) hist:= by
  obtain ⟨ix,hix⟩:=h
  calc
    _ ≤ ∑ r :Fin 155,Fintype.card (FF ix (offset r) (profileCutoff q d (offset r))) :=
      Finset.sum_le_sum fun r _=>hix q hd r
    _=Fintype.card (Σ r :Fin 155,FF ix (offset r) (profileCutoff q d (offset r))) :=
      Fintype.card_sigma.symm
    _≤Fintype.card (Σ j:Pivot hist,Fin (99+d - q - j.1.val)) :=
      Fintype.card_le_of_injective _ (eF4 ix q d)
    _ = _:= by
      simp only [Fintype.card_sigma,Fintype.card_fin,Fintype.sum_sigma,
        Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      exact charge_eq_sum _ _
end qxuyiwe
end
section
set_option autoImplicit true
namespace qxuyiwe
open qK9H6va (iO Oi Ni)
def c1 :Prop :=Profile 51 h51
def c2 :Prop :=Profile 52 h52
def c3:Prop :=Profile 53 h53
def c4 :Prop :=Profile 54 h54
def c5:Prop :=Profile 55 h55
private theorem grade_cases (q:ℕ) (hq₁:q≤131)
    (hd₀:51≤ iO q) (hd₁:iO q≤55) :
    51≤q∧q≤55∨112≤q∧q≤115:= by
  unfold iO P6_6_1.asu at hd₀ hd₁
  by_cases hb:q≤111
  · simp only [if_pos hb] at hd₀ hd₁
    omega
  · by_cases ht:q≤129
    · simp only [if_neg hb,if_pos ht] at hd₀
      omega
    · simp only [if_neg hb,if_neg ht] at hd₀
      omega
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) :
    qK9H6va.c4 := by
  intro q _ hq hd₀ hd₁
  have bound {q d:ℕ} {hist:List ℕ} (h:Profile d hist)
      (hd:iO q=d) (hb:charge (99+d - q) hist=Ni q) :
      Oi q≤Ni q:=(grade_le_charge h hd).trans_eq hb
  rcases grade_cases q hq hd₀ hd₁ with ⟨hlo,hhi⟩ | ⟨hlo,hhi⟩
  · interval_cases q
    · exact bound h1 rfl charge51
    · exact bound h2 rfl charge52
    · exact bound h3 rfl charge53
    · exact bound h4 rfl charge54
    · exact bound h5 rfl charge55
  · interval_cases q
    · exact bound h4 rfl charge112
    · exact bound h4 rfl charge113
    · exact bound h2 rfl charge114
    · exact bound h2 rfl charge115
end qxuyiwe
end
section
set_option autoImplicit true
namespace qwbsesc
def c1 :Prop :=aak 1291 1710 0x4eedb11a7429
def c2 :Prop :=aak 1710 2150 0x3c4eceda6f99
def c3:Prop :=aak 2150 2550 0x23a2868838a6
def c4 :Prop :=aak 2550 2900 0x12e3a5fb6b7a
def c5:Prop :=aak 2900 3307 0xb597dac2fd5
def c6:Prop :=aak 3307 3678 0x3e5517e58e3
def c7:Prop :=aak 3678 4020 0x9c0871ed56
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5)
    (h6:c6) (h7:c7) :P6_6_2.c3:= by
  have r0:=aGH (by decide) (by decide) saturated_cap shoulder_cap
  have r1 :=aGH (by decide) (by decide) r0 h1
  have r2 :=aGH (by decide) (by decide) r1 h2
  have r3:=aGH (by decide) (by decide) r2 h3
  have r4 :=aGH (by decide) (by decide) r3 h4
  have r5:=aGH (by decide) (by decide) r4 h5
  have r6:=aGH (by decide) (by decide) r5 h6
  have r7:=aGH (by decide) (by decide) r6 h7
  obtain ⟨p,hp⟩:=aGH (by decide) (by decide) r7 tail_cap
  exact ⟨p,hp.trans (by decide)⟩
end qwbsesc
end
section
set_option autoImplicit true
namespace q90NBie
noncomputable section
open Polynomial P6_6_7
open aR (af ao shape jet wU Z8)
open dN (GeoJets j8 bC)
open agL (EY BV Uz taylor_coeff bft afc)
private abbrev Exp:=Fin 4 →₀ ℕ
private theorem order_add (a b:Exp) :EY (a+b)=EY a+EY b:= by
  simp [EY,Finsupp.sum_fintype,Finsupp.add_apply,Finset.sum_add_distrib]
private theorem order_pos_of_ne {a :Exp} (ha :a≠0) :0<EY a := by
  obtain ⟨i,hi⟩ : ∃ i,a i≠0:= by
    by_contra! h
    exact ha (Finsupp.ext h)
  unfold EY
  rw [Finsupp.sum_fintype _ _ (fun _=>rfl)]
  exact (Nat.pos_of_ne_zero hi).trans_le
    (Finset.single_le_sum (f := fun i=>a i) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i))
private theorem choose_prod_zero {a v :Exp} (h : ¬ a≤v) :
    (∏ i:Fin 4,((v i).choose (a i) :ao[X]))=0:= by
  obtain ⟨i,hi⟩ : ∃ i,v i<a i:= by simpa [Finsupp.le_def,not_forall] using h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.choose_eq_zero_of_lt hi])
private theorem gqf (S:ao[X]) (F:af 4) (a :Exp) :
    Z8 (BV a F) S=BV a (Z8 F S) := by
  let σ:af 4 →+* af 4 :=
    MvPolynomial.eval₂Hom MvPolynomial.C (fun i=>MvPolynomial.X i+MvPolynomial.C (jet S i))
  have h: (MvPolynomial.map σ).comp Uz=Uz.comp σ:= by
    apply MvPolynomial.ringHom_ext <;> intro x
    · simp [σ,Uz]
    · simp only [RingHom.comp_apply,σ,Uz,MvPolynomial.eval₂Hom_X',
        map_add,MvPolynomial.eval₂Hom_C,MvPolynomial.map_C,MvPolynomial.map_X]
      ac_rfl
  have hc:=congrArg (fun P:MvPolynomial (Fin 4) (af 4)=>P.coeff a)
    (RingHom.congr_fun h F)
  change σ (BV a F)=BV a (σ F)
  simpa only [RingHom.comp_apply,MvPolynomial.coeff_map,agL.taylor_coeff] using hc
theorem cUA (F:af 4) (S:ao[X]) (a :Exp) (d:ℕ) (hF:wU F S d) :
    wU (BV a F) S (d-EY a) := by
  classical
  intro m hm
  change m∈(Z8 (BV a F) S).support at hm
  rw [gqf] at hm
  change d-EY a≤EY m
  by_contra! hd
  apply (MvPolynomial.mem_support_iff.mp hm)
  unfold BV
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro v hv
  rw [MvPolynomial.coeff_monomial]
  split_ifs with he
  · by_cases ha :a≤v
    · have hvd:d≤EY v :=hF v hv
      have hv' : a+m=v :=he ▸ add_tsub_cancel_of_le ha
      rw [← hv',order_add] at hvd
      omega
    · rw [choose_prod_zero ha,mul_zero]
  · rfl
private theorem top_partial {F:af 4} (hF:F≠0) :
    ∃ a :Exp,EY a=(shape F).b∧BV a F=MvPolynomial.C (F.coeff a)∧F.coeff a≠0:= by
  classical
  have hs :F.support.Nonempty :=Finset.nonempty_iff_ne_empty.mpr (by simpa using hF)
  obtain ⟨a,hamem,ha⟩:=Finset.exists_mem_eq_sup F.support hs EY
  have ha' : EY a=(shape F).b:=ha.symm
  refine ⟨a,ha',?_,MvPolynomial.mem_support_iff.mp hamem⟩
  unfold BV
  rw [Finset.sum_eq_single_of_mem a hamem]
  · simp [MvPolynomial.monomial_zero']
  · intro v hv hne
    have hn : ¬ a≤v := by
      intro hle
      have hv' := add_tsub_cancel_of_le hle
      have hp:0<EY (v-a) :=order_pos_of_ne (by
        intro hz
        rw [hz,add_zero] at hv'
        exact hne hv'.symm)
      have hd:EY v≤(shape F).b:=MvPolynomial.le_totalDegree hv
      rw [← hv',order_add,ha'] at hd
      omega
    rw [choose_prod_zero hn,mul_zero,MvPolynomial.monomial_zero]
theorem low_partials {F:af 4} {z :Ideal GeoJets} {a :Exp}
    (ha :EY a<genericOrder F z) :bC (BV a F)∈z := by
  classical
  exact Nat.findGreatest_spec
    (P:= fun d => ∀ a,EY a<d→bC (BV a F)∈z)
    (Nat.zero_le _) (fun _ h=>(Nat.not_lt_zero _ h).elim) a ha
theorem ePB {F:af 4} {z :Ideal GeoJets} (hF:F≠0) (hZ:z.IsPrime) :
    ∃ a :Exp,EY a=genericOrder F z∧bC (BV a F)∉z := by
  classical
  have hle :genericOrder F z≤(shape F).b:=Nat.findGreatest_le _
  by_cases h:genericOrder F z=(shape F).b
  · obtain ⟨a,ha,hp,hn⟩:=top_partial hF
    refine ⟨a,ha.trans h.symm,?_⟩
    rw [hp]
    change MvPolynomial.map j8 (MvPolynomial.C _)∉z
    rw [MvPolynomial.map_C]
    exact fun hm=>hZ.ne_top (Ideal.eq_top_of_isUnit_mem _ hm
      ((isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ lB.SZ).mpr hn)).map
        MvPolynomial.C))
  · have hg:genericOrder F z+1≤(shape F).b:= by omega
    by_contra! hx
    have hnext:genericOrder F z+1≤genericOrder F z := by
      apply Nat.le_findGreatest hg
      intro a ha
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ ha) with hlt | he
      · exact low_partials hlt
      · exact hx a he
    omega
private theorem hasse_zero (F:af 4) :BV (0:Exp) F=F:= by
  unfold BV
  simp only [tsub_zero,Finsupp.zero_apply,Nat.choose_zero_right,Nat.cast_one,
    Finset.prod_const_one,mul_one]
  exact (MvPolynomial.as_sum F).symm
theorem generic_positive {F:af 4} {z :Ideal GeoJets} (hF:F≠0) (hZ:z.IsPrime)
    (hmem:bC F∈z) :0<genericOrder F z := by
  obtain ⟨a,ha,hp⟩:=ePB hF hZ
  have hn:a≠0:= by
    intro hz
    rw [hz,hasse_zero] at hp
    exact hp hmem
  exact ha ▸ order_pos_of_ne hn
theorem generic_vanishesTo (F:af 4) (z :Ideal GeoJets) [z.IsPrime] :
    afc z (bC F) (genericOrder F z) := by
  apply bRn.gK5
  intro a ha
  change BV a (MvPolynomial.map j8 F)∈z
  rw [← bft]
  exact low_partials ha
end
end q90NBie
end
section
set_option autoImplicit true
namespace qHde8fc

def c1 :Prop :=aGq 56 83
def c2 :Prop :=aGq 84 92
def c3:Prop :=aGq 93 99
def c4 :Prop :=aGq 100 103
def c5:Prop :=aGq 104 106
def c6:Prop :=aGq 107 109
def c7:Prop :=aGq 110 112
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5)
    (h6:c6) (h7:c7) :qK9H6va.c5:= by
  have head:aGq 56 (tailCost - 1) := by
    intro e hlo hhi
    let R:=cP (aD e.val)
    change 56≤R at hlo
    change R≤112 at hhi
    by_cases h83:R≤83
    · exact h1 e hlo h83
    by_cases h92 :R≤92
    · exact h2 e (by omega) h92
    by_cases h99:R≤99
    · exact h3 e (by omega) h99
    by_cases h103:R≤103
    · exact h4 e (by omega) h103
    by_cases h106:R≤106
    · exact h5 e (by omega) h106
    by_cases h109:R≤109
    · exact h6 e (by omega) h109
    · exact h7 e (by omega) hhi
  intro q _ _ hd _
  have hlo:=hd.trans (min_le_left q (P6_6_1.asu q))
  have hhi:q≤111 := by
    have ht:=hd.trans (min_le_right q (P6_6_1.asu q))
    unfold P6_6_1.asu at ht
    split at ht <;> (try split at ht) <;> omega
  exact (eiF head tailWitness q hlo hhi).trans_eq (c5v q hlo hhi)
end qHde8fc
end
section
set_option autoImplicit true
namespace q1yhP8b
open Finset
open aR (ao Shape)
open NR (ay8)
open aFN (Slot)
open qzLARrc (derivativeIndex flagMatrix flagRank windowBudget)
open qYzmxYc (dga gxl)
open private slot_idx sum_indicator full_le from ProximityPrize.SubmissionLower.Z7T9FDe
open scoped BigOperators
private def key {a :Shape} {q:ℕ} (s :Slot a q) :ℕ :=
  s.1.val*(q+1)+s.2.val
private theorem top_lt_key {a :Shape} {q:ℕ} {r s :Slot a q}
    (h:r.1.val<s.1.val) :key r<key s := by
  have hr :=r.2.isLt
  change r.2.val< min (q - r.1.val) (a.j - 2*r.1.val)+1 at hr
  have hb:r.2.val≤q:= by omega
  have hm:=Nat.mul_le_mul_right (q+1) (Nat.succ_le_of_lt h)
  rw [Nat.succ_mul] at hm
  unfold key
  omega
private theorem etW (a :Shape) (q:ℕ) :
    Function.Injective (key :Slot a q→ℕ) := by
  rintro ⟨r,b⟩ ⟨s,c⟩ h
  have hc:r=s :=Fin.ext (by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hg
    · exact (ne_of_lt (top_lt_key (r :=⟨r,b⟩) (s :=⟨s,c⟩) hl)) h
    · exact (ne_of_gt (top_lt_key (r :=⟨s,c⟩) (s :=⟨r,b⟩) hg)) h)
  subst s
  change r.val*(q+1)+b.val=r.val*(q+1)+c.val at h
  exact congrArg (Sigma.mk r) (Fin.ext (Nat.add_left_cancel h))
private theorem tri_zero {a :Shape} {q i:ℕ} {r s :Slot a q}
    (h:key s<key r) :flagMatrix a q ((i:ℤ)-a.j) q r s=0:= by
  unfold flagMatrix
  split
  next hm =>
    have hle :=hm.2.2.2.1
    have he :r.1.val=s.1.val := by
      by_contra hne
      exact (not_lt_of_gt h) (top_lt_key (lt_of_le_of_ne hle hne))
    have hb:s.2.val< r.2.val := by
      have he' := congrArg (fun n=>n*(q+1)) he
      unfold key at h
      omega
    have hn:s.1.val - r.1.val=0:= by omega
    simp only [hn,Nat.sub_zero,Nat.choose_eq_zero_of_lt hb,Nat.cast_zero,mul_zero]
  next=>rfl
private abbrev UD (a :Shape) (q i:ℕ) (s :Slot a q) :Prop :=
  a.j - derivativeIndex s≤ i∧i<a.b+2*a.j - q - derivativeIndex s
private theorem visible_le (a :Shape) (q i:ℕ) :
    ((univ :Finset (Slot a q)).filter (UD a q i)).card ≤
      flagRank a q ((i:ℤ)-a.j) q:= by
  classical
  let S:=(univ :Finset (Slot a q)).filter (UD a q i)
  let M:=flagMatrix a q ((i:ℤ)-a.j) q
  let A:=M.submatrix (fun s :S=>s.val) (fun s :S=>s.val)
  have ht:A.BlockTriangular (fun s :S=>key s.val) := fun r s h=>tri_zero h
  have hd (s :S) :A s s=1 := by
    have hs :UD a q i s.val :=(mem_filter.mp s.property).2
    have hi:=slot_idx s.val
    unfold UD at hs
    have h₁:0≤(i:ℤ)-a.j+(derivativeIndex s.val :ℤ) := by omega
    have h₂: (i:ℤ)-a.j+q+(derivativeIndex s.val :ℤ) <
        ((a.b+a.j:ℕ) :ℤ) := by omega
    have hw:q - s.val.1.val - s.val.2.val≤q:= by omega
    have hvalid :=And.intro hw (And.intro h₁ (And.intro h₂ (And.intro (le_refl s.val.1.val)
      (show s.val.1.val - s.val.1.val≤ s.val.2.val by omega))))
    change flagMatrix a q ((i:ℤ)-a.j) q s.val s.val=1
    rw [flagMatrix,ite_eq_left hvalid]
    simp only [Nat.sub_self,Nat.sub_zero,Nat.choose_self,Nat.cast_one,mul_one]
  have hdet:A.det=1 := by
    rw [ht.det]
    apply prod_eq_one
    intro k _
    have he :A.toSquareBlock (fun s :S=>key s.val) k=1 := by
      ext s t
      have heq :s=t:=Subtype.ext (Subtype.ext
        (etW a q (s.property.trans t.property.symm)))
      subst t
      rw [Matrix.toSquareBlock_def,Matrix.of_apply,Matrix.one_apply_eq,hd]
    rw [he,Matrix.det_one]
  have hr :A.rank=S.card:= by
    rw [Matrix.rank_of_det_ne_zero (hdet.symm ▸ (one_ne_zero : (1 :ao)≠0)),Fintype.card_coe]
  change S.card≤M.rank
  rw [← hr]
  exact Matrix.rank_submatrix_le _ _ _
private theorem full_eq (a :Shape) (q:ℕ) (hq:q≤a.b) :
    (∑ i∈range (a.b+2*a.j),flagRank a q ((i:ℤ)-a.j) q) =
      (a.b+a.j - q)*ay8 a q:= by
  refine le_antisymm (full_le a q hq) ?_
  refine (show _ = ∑ i∈range (a.b+2*a.j),
    ((univ :Finset (Slot a q)).filter (UD a q i)).card from ?_).le.trans
    (sum_le_sum fun i _=>visible_le a q i)
  simp only [sum_indicator]
  rw [sum_comm]
  have h (s :Slot a q) :
      (∑ i∈range (a.b+2*a.j),if UD a q i s then 1 else 0) =
        a.b+a.j - q:= by
    have hi:=slot_idx s
    unfold UD
    rw [gxl,min_eq_right (by omega)]
    omega
  simp only [h,sum_const,nsmul_eq_mul]
  rw [mul_comm]
  congr 1
  rw [card_eq_sum_ones,dga a q (fun _ _=>(1 :ℕ))]
  simp [ay8]
def slope (a :Shape) :ℕ :=
  ∑ q∈range (a.b+1),(a.b+a.j - q)*ay8 a q
theorem bP5 (a :Shape) (U d:ℕ) (hU:a.b≤U) :
    windowBudget a (U + d)=windowBudget a U + d*slope a := by
  unfold windowBudget slope
  rw [mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  have hq:=Nat.lt_succ_iff.mp (mem_range.mp hq)
  rw [← full_eq a q hq,mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  dsimp only
  rw [show U + d+a.b+1 - 2*q=(U + a.b+1 - 2*q)+d by omega,
    Nat.add_mul]
  exact Nat.add_right_comm _ _ _
end q1yhP8b
end
