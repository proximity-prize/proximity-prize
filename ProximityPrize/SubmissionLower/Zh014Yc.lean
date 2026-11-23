import ProximityPrize.SubmissionLower.Z3f26Sd
import ProximityPrize.SubmissionLower.ZCYrWLb
import ProximityPrize.SubmissionLower.ZU4mhUb
import ProximityPrize.SubmissionLower.ZUHlXra
import ProximityPrize.SubmissionLower.ZYvV56c
set_option Elab.async false
set_option maxRecDepth 3500
set_option maxHeartbeats 2000000
section
set_option autoImplicit true
namespace q8v7MVc
open qK9H6va qaTCFjd
open P1_6_1_5_1 (RelationRow Relation Ug rank_with_pattern dO)
open fP (Ew cF xH oG qI aAr)
open scoped BigOperators Matrix
open private order from ProximityPrize.SubmissionLower.CG
open private piece_cast from ProximityPrize.SubmissionLower.Z3f26Sd
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private def upper (b u z f :ℕ) :Prop :=b+2*u≤z∧u≤f
private instance (b u z f :ℕ) :Decidable (upper b u z f) :=
  inferInstanceAs (Decidable (_∧_))
private theorem upper_upward (b u:ℕ) :UO.bAQ (upper b u) := by
  intro z f z' f' hz _ hf h
  exact ⟨h.1.trans hz,h.2.trans hf⟩
private noncomputable def rowExponent (d b u a x :ℕ) :Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a,d - u - b-a - x,b + x,u]
@[simp] private theorem II (d b u a x :ℕ) :rowExponent d b u a x 0=a := by
  simp [rowExponent]
@[simp] private theorem lI (d b u a x :ℕ) :
    rowExponent d b u a x 1=d - u - b-a - x := by simp [rowExponent]
@[simp] private theorem lV (d b u a x :ℕ) :
    rowExponent d b u a x 2=b + x := by simp [rowExponent]
@[simp] private theorem pG (d b u a x :ℕ) :rowExponent d b u a x 3=u:= by
  simp [rowExponent]
private theorem support {q:ℕ} {e :ait q (offset 3)} {m:XN q (offset 3)}
    (h:Gy q (offset 3) e m≠0) :m.val 2≤e.val 2∧m.val 3≤e.val 3:= by
  constructor
  · by_contra! hn
    exact h (by simp [Gy,prefixMatrix,Nat.choose_eq_zero_of_lt hn])
  · by_contra! hn
    exact h (by simp [Gy,prefixMatrix,Nat.choose_eq_zero_of_lt hn])
private theorem block (q d b u cap:ℕ) (c:ℕ→ℕ→ℕ)
    (hd:iO q=d) (hh:DV q 3=b+2*u+12)
    (_hbox :b+u+11≤d) (hreach:56≤d+(b+2*u))
    (hu:u≤16) (hband:2*b+3 * u=41) (hp:c 3 2=1)
    (hrel :Relation (d - u - b) b c)
    (hcount:aht d (b+2*u+12) 3 (upper b u)≤ cap+1) :
    KC q 3 cap:= by
  classical
  let P:=ajZ q 3 (upper b u)
  let Q:=ajY q 3 (upper b u)
  have hcontact : (Vm q (offset 3)).toNat=b+2*u+12 :=
    (aq6 q 3).trans hh
  let row (i:RelationRow) : {e // P e} := by
    let a :=i.1.val
    let x :=i.2.val
    have ha :a<4 :=i.1.isLt
    have hx :x<12 - 3*a :=i.2.isLt
    refine ⟨⟨rowExponent d b u a x,?_,?_⟩,?_⟩
    · rw [cF,hd]
      simp only [II,lI,lV,pG]
      omega
    · rw [oG,hcontact]
      simp only [II,lV,pG]
      omega
    · change ajZ q 3 (upper b u) _
      unfold ajZ order upper
      simp only [II,lV,pG,hd,Nat.sub_eq_zero_of_le hu]
      omega
  have hrow:Function.Injective row:= by
    intro i j hij
    have ha :=congrArg (fun e : {e // P e} => e.val.val 0) hij
    have hx :=congrArg (fun e : {e // P e} => e.val.val 2) hij
    simp only [row,II] at ha
    simp only [row,lV,Nat.add_left_cancel_iff] at hx
    rcases i with ⟨a,x⟩
    rcases j with ⟨a',x'⟩
    have he :a=a' := Fin.ext ha
    subst a'
    have he' : x=x' := Fin.ext hx
    subst x'
    rfl
  have hrel' (m:XN q (offset 3)) (hq : ¬ Q m) :
      (∑ i:RelationRow,
        Gy q (offset 3) (row i).val m*(c i.1.val i.2.val :ZMod P1.p))=0:= by
    by_cases H :m.val 3=u∧b≤ m.val 2
    · obtain ⟨hc,hb⟩:=H
      have hm:=m.property
      simp only [Ew,xH,offset] at hm
      have hlo:12≤ m.val 1+2*(m.val 2 - b) := by omega
      have hhi:m.val 1+2*(m.val 2 - b)≤15:= by omega
      have he :b+(m.val 2 - b)=m.val 2 := by omega
      simpa only [Gy,prefixMatrix,row,lI,lV,pG,hc,he,
        Nat.choose_self,Nat.cast_one,mul_one] using hrel (m.val 1) (m.val 2 - b) hlo hhi
    · apply Finset.sum_eq_zero
      intro i _
      suffices hz :Gy q (offset 3) (row i).val m=0 by rw [hz,zero_mul]
      by_contra hn
      obtain ⟨hle₂,hle₃⟩:=support hn
      have hr :=(row i).val.property.2
      rw [oG] at hr
      simp only [row,II,lV,pG] at hr hle₂ hle₃
      rw [hcontact] at hr
      have hm:order m.val<DV q 3:= by
        unfold order
        rw [hh]
        omega
      have hmupper :upper b u (order m.val) (m.val 3) := by
        by_contra hn
        exact hq ⟨hm,hn⟩
      unfold upper order at hmupper
      exact H (by omega)
  have hr :=rank_with_pattern (Gy q (offset 3)) P Q
    (aEb q 3 _ (upper_upward b u)) row hrow
    (fun i=>(c i.1.val i.2.val :ZMod P1.p)) Ug
    (by change (c 3 2 :ZMod P1.p)=1; rw [hp,Nat.cast_one]) hrel'
  have hcard:=aHj q 3 (upper b u)
  have hbound:aht (iO q) (DV q 3) 3 (upper b u)≤ cap+1 := by
    rw [hd,hh]
    exact hcount
  exact Nat.le_of_add_le_add_right ((hr.trans hcard).trans hbound)
private def aTU (d h b u start len:ℕ) :ℕ :=
  qI len fun i=>qI ((i+start)/2+1) fun f =>
    if upper b u (i+start) f then aEG d h 3 (i+start) f else aHb d 3 (i+start) f
private theorem bY4 (d h b u tail a s t v cap:ℕ) (hh:h=24+tail)
    (h₀:aTU d h b u 0 8=a) (h₁:aTU d h b u 8 8=s)
    (h₂:aTU d h b u 16 8=t) (h₃:aTU d h b u 24 tail=v)
    (hcap:a+s+t+v≤ cap) :aht d h 3 (upper b u)≤ cap:= by
  let f z :=qI (z/2+1) fun j =>
    if upper b u z j then aEG d h 3 z j else aHb d 3 z j
  change qI h f≤ cap
  conv_lhs=>rw [hh,aAr 24 tail,aAr 16 8,aAr 8 8]
  change aTU d h b u 0 8+aTU d h b u 8 8 +
    aTU d h b u 16 8+aTU d h b u 24 tail≤ cap
  rwa [h₀,h₁,h₂,h₃]
private def columnSum (D b:ℕ) (c:ℕ→ℕ→ℕ) (m y :ℕ) :ℕ :=
  dO D b c m y 0+dO D b c m y 1+dO D b c m y 2+dO D b c m y 3
private theorem dot_of_check (D b:ℕ) (c:ℕ→ℕ→ℕ) (m y :ℕ)
    (hz :columnSum D b c m y % P1.p=0) :
    (∑ i:RelationRow,((D - i.1.val - i.2.val).choose m:ZMod P1.p) *
        ((b+i.2.val).choose (b+y) :ZMod P1.p)*(c i.1.val i.2.val :ZMod P1.p))=0:= by
  rw [Fintype.sum_sigma,Fin.sum_univ_four]
  simp only [← piece_cast]
  change (dO D b c m y 0:ZMod P1.p)+(dO D b c m y 1 :ZMod P1.p) +
    (dO D b c m y 2 :ZMod P1.p)+(dO D b c m y 3:ZMod P1.p)=0
  rw [← Nat.cast_add,← Nat.cast_add,← Nat.cast_add]
  change (columnSum D b c m y :ZMod P1.p)=0
  rw [← ZMod.natCast_mod,hz,Nat.cast_zero]
private def c116 (a x :ℕ) :ℕ :=
  let rows :List (List ℕ) :=
    [[0x6e42936c,0x3caec3f,0x254b8d46,0x555cd394,0x236b6cfc,0x6cdb68f8,0x3f8001be,0x71ed2cb1,0x380787a2,0x2184f419,0x51fad92b,0x37eac53d],
     [0x6b9c81ab,0x72b597e4,0x5e97e379,0x1d4ebe15,0x53bc7e56,0x61b13a62,0x1fc00022,0x38078784,0x27387879],
     [0x42413bcf,0x364dabb0,0x4ed3ddd8,0x1d4ec4a2,0x61b13b20,0x4a3f03f0],
     [0x4fb41561,0x1ea7b957,1]]
  (rows.getD a []).getD x 0
private def c117 (a x :ℕ) :ℕ :=
  let rows :List (List ℕ) :=
    [[0x18b8e99d,0x10e953f5,0x10442b56,0x5dcd97b1,0x7565215a,0x5b83c1a9,0x192a0c0,0x31521474,0x2b2370e,0x70caf8f3,0x3b29831b,0x2c0adbe2],
     [0x4bb86007,0x3c0f0b64,0x348d4988,0x5f3ffb44,0x63eb4cc2,0x3bc3c36f,0x16371574,0x6360e442,0x55fb62d9],
     [0x64b969bf,0x5ab6d7e4,0x48924a34,0x6f1fffc9,0x1a25a5ad,0x4591e1e2],
     [0x348d3e18,0x366db6cf,1]]
  (rows.getD a []).getD x 0
private theorem relation116:Relation 33 10 c116:= by
  intro m y hlo hhi
  have hy :y<8:= by omega
  have hmlo:12 - 2*y≤ m:= by omega
  have hmhi:m<16 - 2*y := by omega
  interval_cases y <;> interval_cases m <;> exact dot_of_check 33 10 c116 _ _ rfl
private theorem relation117:Relation 32 13 c117:= by
  intro m y hlo hhi
  have hy :y<8:= by omega
  have hmlo:12 - 2*y≤ m:= by omega
  have hmhi:m<16 - 2*y := by omega
  interval_cases y <;> interval_cases m <;> exact dot_of_check 32 13 c117 _ _ rfl
theorem proof :qaTCFjd.c2 :=
  ⟨block 116 50 10 7 979 c116 rfl rfl (by decide) (by decide) (by decide) rfl rfl relation116
     (bY4 50 36 10 7 12 49 208 336 387 980 rfl rfl rfl rfl rfl (by decide)),
   block 117 50 13 5 941 c117 rfl rfl (by decide) (by decide) (by decide) rfl rfl relation117
     (bY4 50 35 13 5 11 49 208 336 349 942 rfl rfl rfl rfl rfl (by decide))⟩
end q8v7MVc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qQCYsrb

open P6_6 P6_6_8 q2w4Sxc
open private g2 g3 g4 from ProximityPrize.SubmissionLower.ZBG70hc
local notation "m!" n "," x "," w =>
  segment (len:=n) (cost:=x) (word:=w) rfl rfl
local notation "o!" g "," h=>strict g (by decide) h rfl (by decide)
local notation "z!" h =>
  transport ⟨by decide,by decide,by decide⟩ ⟨by decide,by decide,by decide⟩ (by decide) h
local notation "b!" m "," x "," y=>Certificate.splitB m (Certificate.trim x) (Certificate.trim y)
local notation "j!" m "," x "," y=>Certificate.rK m (Certificate.trim x) (Certificate.trim y)
local notation "t!" m "," x "," y=>Certificate.splitT m (Certificate.trim x) (Certificate.trim y)
local notation "p!" vk "," vf "," h "," hc =>
  regular (k :=vk) (f :=vf) (by decide) h (by decide) (by decide) hc rfl (by decide)
private theorem r1 :Order 2 33 2 6 2 :=o! g3,(m! 110,0x6a4b3399789,0x2b0e0c0c0a0a09)
private theorem r2 :Order 2 64 1 13 1 :=o! g4,(joinTail (m! 12,0x1c1515a2cfa,0x201020102010201) (joinTail (m! 17,0x1351a93f457,0x302020302020201) (m! 40,0x71b2e34b1b,0xb06050505040202)))
private theorem r3:Order 2 64 81 3 1 :=o! g4,(m! 45,0x35dbb0f18f3,0x8070b05050504)
private theorem r4 :Order 2 16 1 3 1 :=o! g24a,(joinTail (m! 21,0x5559db928a5,0x403020203020203) (joinTail (m! 33,0x5015246dbe8,0x504040404040404) (joinTail (m! 38,0x267b403bf66,0x505050405040505) (m! 79,0xb878f29302,0x1b0f070706050606))))
private theorem q2_1 :Lw ⟨2,6,1⟩=⟨0x17c2f1f3578eb,0x9d18fbc4f1552,0x15a3e05eebfb⟩:=rfl
private theorem q2_2 :Lw ⟨2,6,2⟩=⟨0x17b95739436a8,0x9bf296c04b0cc,0x413391683d18⟩:=rfl
theorem s2 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨2,6,t⟩ ⟨1,3,1⟩ (cap ⟨2,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (b! 80,(j! 12,(t! 1,(p! 16,0x1d604ad7a8a84d,(.inl r4),q2_1),(p! 29,0x3bac77d8dff9ec,(.inl (z! r1)),q2_1)),(Certificate.prune r2)),(Certificate.prune r3))
  · exact .trim (b! 80,(j! 12,(t! 1,(p! 16,0x1d604ad7a8a84d,(.inl (bO4 r4)),q2_2),(p! 29,0x3bac77d8dff9ec,(.inl (z! r1)),q2_2)),(Certificate.prune (bO4 r2))),(Certificate.prune (bO4 r3)))
private theorem r5:Order 3 66 73 3 1 :=o! g4,(joinTail (m! 27,0x31735bfa7e2,0x603030503020302) (m! 24,0x74f65f5ef8,0xa070403))
private theorem q3_1 :Lw ⟨3,6,1⟩=⟨0x17c2d44f999b9,0x9aef70fe6e456,0x153d23c01f8c⟩:=rfl
private theorem q3_2 :Lw ⟨3,6,2⟩=⟨0x17b91ca86a1fa,0x99cd7fd21b6e4,0x3ffdb8a9b583⟩:=rfl
theorem s3 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨3,6,t⟩ ⟨1,3,1⟩ (cap ⟨3,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (b! 72,(j! 12,(t! 1,(p! 14,0x1e48c809f30f07,(.inl (z! r4)),q3_1),(p! 26,0x3c85ff93410738,(.inl (z! r1)),q3_1)),(Certificate.prune (z! r2))),(Certificate.prune (z! r5)))
  · exact .trim (b! 72,(j! 12,(t! 1,(p! 14,0x1e48c809f30f07,(.inl (z! r4)),q3_2),(p! 26,0x3c85ff93410738,(.inl (z! r1)),q3_2)),(Certificate.prune (z! r2))),(Certificate.prune (z! r5)))
private theorem r6:Order 4 19 1 3 1 :=o! g2,(joinTail (m! 27,0x5951436bdde,0x403040304030303) (joinTail (m! 33,0x38f7560870a,0x504050404040403) (m! 104,0x201dc649d79,0x1b0f0d0b0b0a0908)))
private theorem r7:Order 4 68 1 13 1 :=o! g68a,(joinTail (m! 12,0x194e0a4cddb,0x102010201020102) (joinTail (m! 18,0x118d5a2b3ec,0x203020203020202) (m! 37,0x56b25e774c,0xa060505050402)))
private theorem q4_1 :Lw ⟨4,6,1⟩=⟨0x16d6e4c9d645c,0x934f2c8093c55,0x142e6dae3f3a⟩:=rfl
private theorem q4_2 :Lw ⟨4,6,2⟩=⟨0x16cd56c1f6ace,0x923a4bc87214c,0x3ccd835c6ffb⟩:=rfl
theorem s4 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨4,6,t⟩ ⟨1,3,1⟩ (cap ⟨4,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (b! 72,(j! 12,(t! 1,(p! 15,0x1c343b65e18fd0,(.inl (z! r6)),q4_1),(p! 27,0x3a12bf5a714bd1,(.inl (z! r1)),q4_1)),(Certificate.prune (z! r7))),(Certificate.prune (z! r5)))
  · exact .trim (b! 72,(j! 12,(t! 1,(p! 15,0x1c343b65e18fd0,(.inl (z! r6)),q4_2),(p! 27,0x3a12bf5a714bd1,(.inl (z! r1)),q4_2)),(Certificate.prune (z! r7))),(Certificate.prune (z! r5)))
private theorem r8:Order 5 68 65 3 1 :=o! g67a,(m! 52,0x35c8b068898,0xa08070606050505)
private theorem q5_1 :Lw ⟨5,6,1⟩=⟨0x15f8c14cf9bab,0x8c13dce038a29,0x13299d4a4020⟩:=rfl
private theorem q5_2 :Lw ⟨5,6,2⟩=⟨0x15ef5b6debce1,0x8b0b9bcc71a31,0x39bb2eb051cd⟩:=rfl
theorem s5 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨5,6,t⟩ ⟨1,3,1⟩ (cap ⟨5,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (b! 64,(j! 13,(t! 1,(p! 17,0x1a1e220004b6bb,(.inl (z! r6)),q5_1),(p! 31,0x35bf477e0ab5e0,(.inl (z! r1)),q5_1)),(Certificate.prune (z! r7))),(Certificate.prune r8))
  · exact .trim (b! 64,(j! 13,(t! 1,(p! 17,0x1a1e220004b6bb,(.inl (z! r6)),q5_2),(p! 31,0x35bf477e0ab5e0,(.inl (z! r1)),q5_2)),(Certificate.prune (z! r7))),(Certificate.prune (bO4 r8)))
private theorem r9:Order 6 69 1 11 1 :=o! g71a,(joinTail (m! 19,0x1f71ffffa7e,0x202030303030201) (joinTail (m! 30,0xdd6747bc07,0x505040404040202) (m! 24,0xd0fe0e89d,0xb0706)))
private theorem q6_1 :Lw ⟨6,6,1⟩=⟨0x158e61a3dcbbb,0x8790012d658b6,0x12773ec4d33a⟩:=rfl
private theorem q6_2 :Lw ⟨6,6,2⟩=⟨0x1584f51dd99fa,0x868fe154b4145,0x37a148519a66⟩:=rfl
theorem s6 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨6,6,t⟩ ⟨1,3,1⟩ (cap ⟨6,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (j! 10,(t! 1,(p! 19,0x1a1736711eeff7,(.inl (z! r6)),q6_1),(p! 33,0x34c7a89cf382a2,(.inl (z! r1)),q6_1)),(Certificate.prune r9))
  · exact .trim (j! 10,(t! 1,(p! 19,0x1a1736711eeff7,(.inl (z! r6)),q6_2),(p! 33,0x34c7a89cf382a2,(.inl (z! r1)),q6_2)),(Certificate.prune (bO4 r9)))
end qQCYsrb
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qQCYsrb
open aR (Shape)
open P6_6 P6_6_8 q2w4Sxc
theorem proof :q2w4Sxc.c5:= by
  intro v hv hj
  rcases v with ⟨b,j,t⟩
  change j=6 at hj
  subst j
  rcases hv with hv | ⟨hv,hb⟩
  · have hx :=congrArg Shape.j hv
    change 6=0 at hx
    omega
  change 1≤t∧3*t≤6∧6≤3*b at hv
  change b≤16 at hb
  have h₁:2≤b:= by omega
  have ht:t=1∨t=2 := by omega
  interval_cases b
  · exact s2 t ht
  · exact s3 t ht
  · exact s4 t ht
  · exact s5 t ht
  · exact s6 t ht
  · exact s7 t ht
  · exact s8 t ht
  · exact s9 t ht
  · exact s10 t ht
  · exact s11 t ht
  · exact s12 t ht
  · exact s13 t ht
  · exact s14 t ht
  · exact s15 t ht
  · exact s16 t ht
end qQCYsrb
end
section
set_option autoImplicit true
set_option Elab.async false
namespace q7F4Ild
open P6_6 P6_6_8 q2w4Sxc
local notation "B!" z "," m "," l "," r=>cI z m l r rfl rfl
local notation "J!" z "," m "," l "," r=>bV z m l r rfl rfl
local notation "T!" z "," m "," l "," r=>dSy z m l r rfl rfl
local notation "R!" z "," h=>root z h rfl
local notation "F!" x "," k "," q "," c "," h =>
  C8 (z :=x) k q c (by decide) (by decide) (by decide) (Or.inl h) rfl rfl
local notation "O!" x "," q "," c =>
  C8 (z :=x) 1 q c (by decide) (by decide) (by decide) (Or.inr rfl) rfl rfl
open private g1 g2 g3 g4 from ProximityPrize.SubmissionLower.ZBHfNie
local notation "g0" => q33KzTa.base_zero 5
local notation "M!" z "," m "," h "," p =>
  companion z m (Hw h (by decide)) (by decide) rfl p rfl (by decide)
local notation "G!" p=>And.intro rfl (And.intro rfl (And.intro rfl (And.intro rfl p)))
local notation "P!" x "," k "," h=>prune (z :=x) k h
section
local notation "V" => state 2
private theorem cf2 :Lw V=⟨0x1e837603b6bc7,0xbfbe5668a6b89,0x2725b1c15823⟩:=rfl
private theorem e2 :sharedOrder V=56:=rfl
theorem QE :Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfce0c4301,(T! 0xfce0c4301,1,(J! 0x1ce0c4301,14,(B! 0x13a0c4301,11,(B! 0x1382c4301,1,(O! 0x10c044301,0x35,cf2),(F!
    0x1382c4302,3,0x232,cf2,(M!
    0x2503801920600f8418048e0401b561009c504035ce10084382025f8080ad68203138080de68203e8408117e8204e060815aa0205fea081a740207460081fe78208a840825ac820c59b,0x161810000000,g0,(G!
    (G! (G! (G! (G! ⟨rfl,rfl,.intro⟩)))))))),(F! 0x13a0c430c,19,0x731,cf2,(M!
    0x580c005181802068400ed01002ad0200da808044a820154c0806870201fac0809848202d5c080d688203efa08125d820552e08188f02070b608202d020925208296a820bad8083458020e9f008411a822065a,0x161822490a30,g1,(G!
    (G! (G! (G! (G! (G! ⟨rfl,.intro⟩))))))))),(P! 0x1ce0c4f07,e2,(M! 0x170a000d0100078040039c1001710400160,0x16160d9530de,g3,(G!
    ⟨rfl,.intro⟩)))),(J! 0xfce0c8602,14,(B! 0x43a0c8602,15,(F! 0x4383c8602,8,0x233,cf2,(M!
    0x288000414000a9,0x160000000000,g0,⟨rfl,rfl,.intro⟩)),(F! 0x43a0c8610,39,0xcb1,cf2,(M!
    0x210e0028c200152860065410026f0400e5010024b0200ada0806d1840025e,0x16180131fbc5,g2,(G! (G! ⟨rfl,.intro⟩))))),(P!
    0xfce0c8f02,e2,(M! 0x28a88020f810154a040adf01020c1820aa2c0830c502001da,0x1618299530de,g3,(G! ⟨rfl,rfl,rfl,.intro⟩)))))
end
section
local notation "V" => state 3
private theorem cf3:Lw V=⟨0x1de12258baff9,0xb9966891eb4b5,0x24d9c4fdecbd⟩:=rfl
private theorem e3:sharedOrder V=57:=rfl
theorem at3:Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfce084301,(T! 0xfce084301,1,(J! 0x1ce084301,13,(B! 0x136084301,9,(F! 0x134244301,3,0x35,cf3,(M!
    0x4a0e0053420027d0600b3a10041a84017021007cb04012f808056a82018980806f20201f3c0808be02026fc080ad30202fec080d378203a26080ff102045360812d3820c55c,0x161810000000,g0,(G!
    (G! (G! (G! (G! ⟨rfl,.intro⟩))))))),(F! 0x13608430a,18,0x332,cf3,(M!
    0x598e006aa200367860102410062804023fa100caf0401fba08093b0202ab8080c4a820384a08100a02048cc0814918205ca20819fb02073f808202b02184db,0x16182ea59b37,g1,(G!
    (G! (G! (G! ⟨rfl,rfl,rfl,.intro⟩))))))),(P! 0x1ce084e07,e3,(M!
    0xc22000b184002e208011f02006960802520200c9e08042c0201572080600020029d,0x16180357ac7a,g3,(G! (G! ⟨rfl,rfl,.intro⟩))))),(J!
    0xfce088602,14,(B! 0x43a088602,14,(F! 0x438388602,7,0x1230,cf3,(M! 0x288000394000a9,0x140000000000,g0,⟨rfl,rfl,.intro⟩)),(F!
    0x43a08860f,41,0xb5,cf3,(M!
    0x3e0a006d01803530401b3c1005368201b8e0808ed0202d7c080e4582046ba0815a702068fa081f830209616082c55820cf8008388d820045a,0x1618177b0933,g2,(G!
    (G! (G! (G! ⟨rfl,.intro⟩))))))),(P! 0xfce088f02,e3,(M! 0x2e280022040015c1000b0840021208016f04001a0,0x16158357ac7a,g3,(G!
    ⟨rfl,rfl,.intro⟩)))))
end
section
local notation "V" => state 4
private theorem cf4 :Lw V=⟨0x1d4435b427000,0xb39461805e67a,0x240db480f13f⟩:=rfl
private theorem e4 :sharedOrder V=58:=rfl
theorem at4 :Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfce044301,(T! 0xfce044301,1,(J! 0x1ce044301,13,(B! 0x136044301,8,(F! 0x134204301,3,0x35,cf4,(M!
    0xc12000d428006d880024c1800e3860033c100106840051e10019284007a210024984002e0,0x161800000000,g0,(G! (G!
    ⟨rfl,rfl,rfl,.intro⟩)))),(F! 0x136044309,19,0xb4,cf4,(M!
    0x5c0e004041801760400a1c1004118400afa08035a82010380804db82017160806ce0201fe00809458202ae6080c570203880081018820490c0814a28205cea0819fb02073e808203502205db,0x1617d3022c3e,g1,(G!
    (G! (G! (G! (G! ⟨rfl,rfl,rfl,.intro⟩)))))))),(P! 0x1ce044e07,e4,(M!
    0x2170a013ca100ba704025b4080ccc020439c082d8e04001db,0x1618191a2816,g3,(G! ⟨rfl,rfl,rfl,.intro⟩)))),(J! 0xfce048602,14,(B!
    0x43a048602,13,(F! 0x438348602,8,0x36,cf4,(M! 0x288000394000a9,0x140000000000,g0,⟨rfl,rfl,.intro⟩)),(F!
    0x43a04860e,42,0x1730,cf4,(M!
    0xa638008c86003721001900400a6e1001cb82008e40802b80200d2e0803f482012d408058f02019e00806fd820039d,0x161775c416a1,g2,(G! (G! (G!
    ⟨rfl,rfl,.intro⟩)))))),(P! 0xfce048f02,e4,(M! 0x60a0009418004084001e21000b60400161,0x1613f91a2816,g3,(G! ⟨rfl,.intro⟩)))))
end
section
local notation "V" => state 5
private theorem cf5:Lw V=⟨0x1c1a2781f3787,0xaa74bbf4783bd,0x21b8a8bed15c⟩:=rfl
private theorem e5:sharedOrder V=60:=rfl
theorem at5:Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfce004301,(T! 0xfce004301,1,(J! 0x1ce004301,13,(B! 0x136004301,7,(F! 0x1341c4301,3,0x35,cf5,(M!
    0x4e180044c30023e8a00d042003a086013dc18069b06001df,0x161680000000,g0,(G! ⟨rfl,rfl,rfl,.intro⟩))),(F!
    0x136004308,20,0x5b1,cf5,(M!
    0xba28007004004461000e302004e80801a782008b60802d08200e4a08047882016180806be820209c0809c38202e62080dab020400008129c82056180818c202071580820488209264082948020b9b2083403820e84a08405f823071a,0x1618175ebd45,g1,(G!
    (G! (G! (G! (G! (G! (G! (.intro))))))))))),(P! 0x1ce004e07,e5,(M!
    0x2d88003761000fc020066e0802740200e3e0804f78201ad60808d38202b34080b9d02002dc,0x16182edca3b2,g3,(G! (G!
    ⟨rfl,rfl,rfl,.intro⟩))))),(J! 0xfce008602,14,(B! 0x43a008602,13,(F! 0x438348602,8,0x36,cf5,(M!
    0x288000394000a9,0x140000000000,g0,⟨rfl,rfl,.intro⟩)),(F! 0x43a00860e,44,0x2b3,cf5,(M!
    0xa83000ba06004f610025e84007020802450200b900803a102011fe0805828201aba0808070202642080b4f02033ba080dd3820041c,0x1618000d240f,g2,(G!
    (G! (G! (G! (.intro)))))))),(P! 0xfce008f02,e5,(M! 0x78a0004e10002f840009c08003502001180800b484001e1,0x16176edca3b2,g3,(G!
    ⟨rfl,rfl,rfl,.intro⟩)))))
end
section
local notation "V" => state 6
private theorem cf6:Lw V=⟨0x1c1a04a18d4fd,0xa81710bf0e956,0x21195b10cf85⟩:=rfl
private theorem e6:sharedOrder V=60:=rfl
theorem at6:Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcdfc4301,(T! 0xfcdfc4301,1,(J! 0x1cdfc4301,12,(B! 0x131fc4301,5,(F! 0x12c144301,2,0x35,cf6,(M!
    0xb9e0009238003c0a001b02800868800163,0x161000000000,g0,(G! ⟨rfl,.intro⟩))),(F! 0x131fc4306,18,0x531,cf6,(M!
    0x22a4801a08800b6e18054f06015b8100781840286c100d4f84044d0100a330202dd8080cd60203950080ff1820039c,0x1617d3bb4e4c,g1,(G! (G! (G!
    ⟨rfl,rfl,.intro⟩)))))),(P! 0x1cdfc4d06,e6,(M!
    0x26200023040018410005402001dc0800a2020035e080117820054c08016d820029f,0x1617e49f1f4e,g3,(G! (G! ⟨rfl,rfl,.intro⟩))))),(J!
    0xfcdfc8602,13,(B! 0x435fc8602,7,(F! 0x4341c8602,6,0x831,cf6,(M! 0xb03600064,0x161000000000,g0,⟨rfl,.intro⟩)),(F!
    0x435fc8608,42,0x1330,cf6,(M! 0xc638011088009141802bb84010cc10062a0400fc60804a802015d4080d3a042429d,0x1617aa56317d,g2,(G! (G!
    ⟨rfl,rfl,.intro⟩))))),(P! 0xfcdfc8e02,e6,(M! 0x1228001c06000c810005f04001160800b184001a1,0x1616e49f1f4e,g3,(G!
    ⟨rfl,rfl,.intro⟩)))))
end
section
local notation "V" => state 7
private theorem cf7:Lw V=⟨0x1b02f352818a0,0x9f81d9794535d,0x202fb559fb65⟩:=rfl
private theorem e7:sharedOrder V=62 :=rfl
theorem at7:Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcdf84301,(T! 0xfcdf84301,1,(J! 0x1cdf84301,12,(B! 0x131f84301,4,(O! 0x124104301,0x1b2,cf7),(F! 0x131f84305,20,0x4b1,cf7,(M!
    0x660e0045418018d0400a9e10043c0400b5c08037502010aa0804f982017920806ed820205a0809628202b4e080c6d02038c2081022020490c0814978205c880819d202072f8081fd202205db,0x16182817df53,g1,(G!
    (G! (G! (G! (G! ⟨rfl,rfl,rfl,.intro⟩)))))))),(P! 0x1cdf84d06,e7,(M!
    0x6860012e10006a020030208013d020079e0802c80200f9c08054c8201c0808090f82029cc080b35023435c,0x1617ea619aea,g3,(G! (G! (G!
    ⟨rfl,.intro⟩)))))),(J! 0xfcdf88602,13,(B! 0x435f88602,7,(F! 0x4341c8602,7,0x3b2,cf7,(M!
    0xb03600064,0x161000000000,g0,⟨rfl,.intro⟩)),(F! 0x435f88608,44,0x1230,cf7,(M!
    0xce38011388009241802c004010ee1006390400ff00804b6020161c080d24840029d,0x1618049f3eeb,g2,(G! (G! ⟨rfl,rfl,.intro⟩))))),(P!
    0xfcdf88e02,e7,(M! 0x50a0003a100024840012610003782001200800ae04001e1,0x16165a619aea,g3,(G! ⟨rfl,rfl,rfl,.intro⟩)))))
end
section
local notation "V" => state 8
private theorem cf8:Lw V=⟨0x19fd65b95c0f6,0x976c67818cc53,0x1e080d43b51e⟩:=rfl
private theorem e8:sharedOrder V=64 :=rfl
theorem at8:Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcdf44301,(T! 0xfcdf44301,1,(J! 0x1cdf44301,12,(B! 0x131f44301,4,(O! 0x124104301,0x1b2,cf8),(F! 0x131f44305,21,0x232,cf8,(M!
    0x8b94009782803780601916180652040229a100b8f8403c881013768406296101e7f84182dc,0x16182c74705a,g1,(G! (G!
    ⟨rfl,rfl,rfl,.intro⟩))))),(P! 0x1cdf44d06,e8,(M!
    0x2104003660803010201d84080ed202068e6082a8502102b6085db68220ab608b0aa823a33e0927820251cbe09602c82403d7,0x16182e241686,g3,(G! (G!
    (G! ⟨rfl,rfl,rfl,.intro⟩)))))),(J! 0xfcdf48602,13,(B! 0x435f48602,6,(F! 0x434188602,7,0x3b2,cf8,(M!
    0x53600069,0x160000000000,g0,⟨rfl,.intro⟩)),(F! 0x435f48607,46,0x442e,cf8,(M!
    0xe03800a986003f41001bb8400b421004510400b54080366820102e0804c70201668080cf5042431d,0x1617bee84c59,g2,(G! (G! (G!
    (.intro))))))),(P! 0xfcdf48e02,e8,(M! 0x32a0a0202a10137f0409afe101cf402093da0855aa04001da,0x161828241686,g3,(G!
    ⟨rfl,rfl,rfl,.intro⟩)))))
end
section
local notation "V" => state 9
private theorem cf9:Lw V=⟨0x19806d7717e84,0x92669ff753e9c,0x1d498570dc83⟩:=rfl
private theorem e9:sharedOrder V=65:=rfl
theorem at9:Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcdf04301,(T! 0xfcdf04301,1,(J! 0x1cdf04301,12,(B! 0x131f04301,3,(O! 0x11c0c4301,0x34,cf9),(F! 0x131f04304,22,0x10af,cf9,(M!
    0x4694004c42801bd8600c9218032a04011521005c90401e481009bc040314c100f4004142dd,0x1617c8d10161,g1,(G! (G!
    ⟨rfl,rfl,rfl,.intro⟩))))),(P! 0x1cdf04d06,e9,(M! 0x50a0006c18002e040015c10003f8200161,0x16127174c235,g4,(G! ⟨rfl,.intro⟩)))),(J!
    0xfcdf08602,12,(F! 0x431f08602,45,0x731,cf9,(M!
    0x1fa3801758600f441804a98401cd8100a9d8403c161009660202bbe08198e042829c,0x1617f93159c7,g2,(G! (G! ⟨rfl,rfl,.intro⟩)))),(P!
    0xfcdf08d02,e9,(M! 0xb0a0006e10004284000da08004a820018a08008002001e0,0x16167174c235,g4,(G! ⟨rfl,rfl,rfl,.intro⟩)))))
end
end q7F4Ild
end
section
set_option autoImplicit true
set_option Elab.async false
namespace q7F4Ild
open P6_6 P6_6_8 q2w4Sxc
local notation "B!" z "," m "," l "," r=>cI z m l r rfl rfl
local notation "J!" z "," m "," l "," r=>bV z m l r rfl rfl
local notation "T!" z "," m "," l "," r=>dSy z m l r rfl rfl
local notation "R!" z "," h=>root z h rfl
local notation "F!" x "," k "," q "," c "," h =>
  C8 (z :=x) k q c (by decide) (by decide) (by decide) (Or.inl h) rfl rfl
local notation "O!" x "," q "," c =>
  C8 (z :=x) 1 q c (by decide) (by decide) (by decide) (Or.inr rfl) rfl rfl
open private g1 g2 g4 g5 g7 g9 g12 g15 g18 from ProximityPrize.SubmissionLower.ZBHfNie
local notation "g0" => q33KzTa.base_zero 5
local notation "M!" z "," m "," h "," p =>
  companion z m (Hw h (by decide)) (by decide) rfl p rfl (by decide)
local notation "G!" p=>And.intro rfl (And.intro rfl (And.intro rfl (And.intro rfl p)))
local notation "P!" x "," k "," h=>prune (z :=x) k h
section
local notation "V" => state 10
private theorem cf10 :Lw V=⟨0x1892020f72d79,0x8af6e67c4e0a5,0x1b4200f0249a⟩:=rfl
private theorem e10 :sharedOrder V=67:=rfl
theorem at10 :Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcdec4301,(T! 0xfcdec4301,1,(J! 0x1cdec4301,12,(B! 0x131ec4301,2,(O! 0x114084301,0x34,cf10),(F!
    0x131ec4303,24,0xf2f,cf10,(M!
    0x16c4801d78a00b5c18054886015a8100780040287e100d5e840454c100a4a0202e50080cfc0203a0c080fbf821439c,0x1617f52d9268,g1,(G! (G! (G!
    ⟨rfl,rfl,.intro⟩)))))),(P! 0x1cdec4d06,e10,(M! 0x64300058060021a1000ed0400120,0x1615d3243998,g4,(G! (.intro))))),(J!
    0xfcdec8602,12,(F! 0x431ec8602,47,0xdb0,cf10,(M!
    0x80e0009e20004f860017610008d040032e10011c04002be0801948400260,0x1616d37a6735,g2,(G! (G! ⟨rfl,.intro⟩)))),(P!
    0xfcdec8d02,e10,(M! 0x3228001e0400118100089840019808008382001a0,0x1615d3243998,g4,(G! ⟨rfl,rfl,.intro⟩)))))
end
section
local notation "V" => state 11
private theorem cf11 :Lw V=⟨0x181fd7238ac10,0x8645e20196a09,0x1a88c69dd869⟩:=rfl
private theorem e11 :sharedOrder V=68:=rfl
theorem at11 :Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcde84301,(T! 0xfcde84301,1,(J! 0x1cde84301,11,(F! 0x12de84301,23,0x331,cf11,(M!
    0x2694002862800e8060067818019d84008ca1002eb8400f361004de0400b7a0803360200e540803ee020035e,0x1617618a236f,g1,(G! (G! (G!
    ⟨rfl,.intro⟩))))),(P! 0x1cde84c06,e11,(M! 0x22a38018406008c01003b8840011e,0x1617b4d3b0fb,g4,(G! (.intro))))),(J!
    0xfcde88602,11,(F! 0x32de88602,40,0xd30,cf11,(M! 0x26480023690240a1,0x1617adc374a3,g2,⟨rfl,rfl,.intro⟩)),(P! 0xfcde88c02,e11,(M!
    0x12628016d860099e10047a0400d00080417820019d,0x1617f4d3b0fb,g4,(G! ⟨rfl,rfl,.intro⟩)))))
end
section
local notation "V" => state 12
private theorem cf12 :Lw V=⟨0x17459aa3dbbf8,0x7f667874b7cf4,0x189d96d85323⟩:=rfl
private theorem e12 :sharedOrder V=70:=rfl
theorem at12 :Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcde44301,(T! 0xfcde44301,1,(J! 0x1cde44301,10,(F! 0x129e44301,19,0x192e,cf12,(M!
    0x5cc8005cf100237628103a8a1411e,0x1617dde6b476,g1,(G! (.intro)))),(P! 0x1cde44b05,e12,(M!
    0x3628002184001461000a604001f80800a60200358080104820021f,0x16169683285e,g4,(G! (G! (.intro)))))),(J! 0xfcde48602,11,(F!
    0x32de48602,41,0x32ae,cf12,(M! 0x1c80002512000a5,0x1607880c8211,g2,⟨rfl,rfl,.intro⟩)),(P! 0xfcde48c02,e12,(M!
    0x28c00030180013840009210003c0400162,0x16159683285e,g4,(G! ⟨rfl,.intro⟩)))))
end
section
local notation "V" => state 13
private theorem cf13:Lw V=⟨0x167750cf4edce,0x78d9b6f51bb5f,0x16c685410e61⟩:=rfl
private theorem e13:sharedOrder V=72 :=rfl
theorem at13:Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcde04301,(T! 0xfcde04301,1,(J! 0x1cde04301,9,(F! 0x125e04301,16,0xb3,cf13,(M!
    0x1090000e100006c3000290a00125,0x160000000000,g0,(G! (.intro)))),(P! 0x1cde04a05,e13,(M!
    0x1418003a840014e08009a8200412080199020098608036882012e208065c0202182080ad182036f0080fe5024839b,0x161830329fc1,g4,(G! (G! (G!
    ⟨rfl,rfl,.intro⟩)))))),(J! 0xfcde08602,10,(F! 0x329e08602,35,0xb4,cf13,(M!
    0x280000410000a8,0x15b962558f7f,g2,⟨rfl,rfl,.intro⟩)),(P! 0xfcde08b02,e13,(M!
    0x4630004c86001fc1000ec04002ae0801e0040019f,0x161778329fc1,g4,(G! ⟨rfl,rfl,.intro⟩)))))
end
section
local notation "V" => state 14
private theorem cf14 :Lw V=⟨0x14fb30c7bf034,0x6eae7473ae13e,0x14e9b7471945⟩:=rfl
private theorem e14 :sharedOrder V=76:=rfl
theorem at14 :Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcddc4301,(T! 0xfcddc4301,1,(J! 0x1cddc4301,10,(F! 0x129dc4301,22,0x2b1,cf14,(M!
    0x11fa601304480a540e180df,0x1617d69fd684,g1,⟨rfl,rfl,rfl,.intro⟩)),(P! 0x1cddc4b05,e14,(M!
    0x2c38002086000c21000560400121,0x1616ed519687,g5,(G! (.intro))))),(J! 0xfcddc8602,10,(F! 0x329dc8602,38,0x2b2,cf14,(M!
    0x880000810000a7,0x15ab3c9e9ced,g2,⟨rfl,rfl,.intro⟩)),(P! 0xfcddc8b02,e14,(M!
    0x1628001e06000d0100064040012808005f82001a0,0x1616ed519687,g5,(G! ⟨rfl,rfl,.intro⟩)))))
end
section
local notation "V" => state 15
private theorem cf15:Lw V=⟨0x13f7224398386,0x6727e17a594c5,0x1333a3075642⟩:=rfl
private theorem e15:sharedOrder V=79:=rfl
theorem at15:Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcdd84301,(T! 0xfcdd84301,1,(J! 0x1cdd84301,9,(F! 0x125d84301,18,0xa2f,cf15,(M!
    0x2a6000284800120c000e6,0x15ddd2fc678b,g1,⟨rfl,rfl,rfl,.intro⟩)),(P! 0x1cdd84a05,e15,(M!
    0x78c0007c18003384001821000a60400160,0x1617d90a94a1,g7,(G! ⟨rfl,.intro⟩)))),(J! 0xfcdd88602,9,(F!
    0x325d88602,31,0x2952a,cf15,(M! 0x288000292000a9,0x15ddd2fc678b,g1,⟨rfl,rfl,.intro⟩)),(P! 0xfcdd88a02,e15,(M!
    0x3c280028840019c1000d7840029a0800dd020047e08016f820021e,0x1618190a94a1,g7,(G! (G! (.intro)))))))
end
section
local notation "V" => state 16
private theorem cf16:Lw V=⟨0x1305fa62bba9d,0x601aed2009dbf,0x1192014d1cf0⟩:=rfl
private theorem e16:sharedOrder V=82 :=rfl
theorem at16:Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcdd44301,(T! 0xfcdd44301,1,(J! 0x1cdd44301,8,(F! 0x121d44301,15,0x4b0,cf16,(M!
    0x1aa0001848000d0e000e7,0x160000000000,g0,⟨rfl,rfl,rfl,.intro⟩)),(P! 0x1cdd44904,e16,(M!
    0x138e0010018006404002da100132040015f,0x1617b5754194,g9,(G! ⟨rfl,.intro⟩)))),(J! 0xfcdd48602,8,(F!
    0x221d48602,25,0x132f,cf16,(M! 0x403400065,0x15f9cf58f892,g1,⟨rfl,.intro⟩)),(P! 0xfcdd48902,e16,(M!
    0x1228001b86000ce100067840013a08006702002140800a8820021f,0x161735754194,g9,(G! (G! (.intro)))))))
end
section
local notation "V" => state 17
private theorem cf17:Lw V=⟨0x1198d860be842,0x5693306bf3377,0xf24aca40db8⟩:=rfl
private theorem e17:sharedOrder V=87:=rfl
theorem at17:Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcdd04301,(T! 0xfcdd04301,1,(J! 0x1cdd04301,7,(F! 0x11dd04301,12,0x430,cf17,(M!
    0x3cc8004818000a5,0x160000000000,g0,⟨rfl,rfl,.intro⟩)),(P! 0x1cdd04804,e17,(M!
    0x2638002486000f4100074040032410008d820019f,0x1617a826b4af,g12,(G! ⟨rfl,rfl,.intro⟩)))),(J! 0xfcdd08602,7,(F!
    0x21dd08602,20,0x431,cf17,(M! 0x3b200069,0x15d5cbb58999,g1,⟨rfl,.intro⟩)),(P! 0xfcdd08802,e17,(M!
    0x228a001be10013e84004780801a0020092408032002010b20805768201c1c0808e702002db,0x16180826b4af,g12,(G! (G!
    ⟨rfl,rfl,rfl,.intro⟩))))))
end
section
local notation "V" => state 18
private theorem cf18:Lw V=⟨0x10160471cbf0b,0x4cb58190d9c9f,0xcedb215f841⟩:=rfl
private theorem e18:sharedOrder V=93:=rfl
theorem at18:Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcdcc4301,(T! 0xfcdcc4301,1,(B! 0x1cdcc4301,12,(F! 0x164304301,34,0x3b0,cf18,(M!
    0x20a8002514000a5,0x15f2a5c2d2a5,g2,⟨rfl,rfl,.intro⟩)),(P! 0x1cdcc430d,e18,(M!
    0x7880006410003904001aa10004c820018608007982001df,0x1617929c3940,g15,(G! ⟨rfl,rfl,rfl,.intro⟩)))),(B! 0xfcdcc8602,4,(F!
    0x430108602,10,0x3b1,cf18,(M! 0x53600069,0x160000000000,g0,⟨rfl,.intro⟩)),(P! 0xfcdcc8605,e18,(M!
    0x6030007986003861000ba020040608015c82007360802580200bfc0803c7020029c,0x1618029c3940,g15,(G! (G! ⟨rfl,rfl,.intro⟩))))))
end
section
local notation "V" => state 19
private theorem cf19:Lw V=⟨0xdc3e02e36dee,0x3ebcf72049ceb,0xa526be72be0⟩:=rfl
private theorem e19:sharedOrder V=104 :=rfl
theorem at19:Certificate V ⟨1,3,1⟩ (cap V) :=
  R! 0xfcdc84301,(T! 0xfcdc84301,1,(B! 0x1cdc84301,6,(F! 0x134184301,7,0xb2,cf19,(M!
    0x2b8000416000a9,0x160000000000,g0,⟨rfl,rfl,.intro⟩)),(P! 0x1cdc84307,e19,(M!
    0x13fc2016ba040ebe81075850415e400871530223f9e08b3cf826b216,0x161830a67470,g18,(G! (G! (.intro)))))),(P! 0xfcdc88602,e19,(M!
    0x3100002218000d04000601000280400161,0x1617c5a67470,g18,(G! ⟨rfl,.intro⟩))))
end
end q7F4Ild
end
