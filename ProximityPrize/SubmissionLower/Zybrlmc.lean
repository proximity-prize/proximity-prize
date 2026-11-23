import ProximityPrize.SubmissionLower.Zytxfqb
import ProximityPrize.SubmissionLower.ZXTI5ee
import ProximityPrize.SubmissionLower.Z3ot3Tc
import ProximityPrize.SubmissionLower.Zqzexic
import ProximityPrize.SubmissionLower.ZDDH92a
import ProximityPrize.SubmissionLower.ZyiSCyc
import ProximityPrize.SubmissionLower.ZR6GwKc
import ProximityPrize.SubmissionLower.ZdLgyGe
import ProximityPrize.SubmissionLower.Z35X4Rc
import ProximityPrize.SubmissionLower.ZMkA5De
import ProximityPrize.SubmissionLower.ZUTKOhd
import ProximityPrize.SubmissionLower.ZfXbQ1a
import ProximityPrize.SubmissionLower.ZPxXJge
import ProximityPrize.SubmissionLower.ZdBkMOd
import ProximityPrize.SubmissionLower.Z07A6ec
import ProximityPrize.SubmissionLower.ZkMhvdb
import ProximityPrize.SubmissionLower.Z7iuxgb
import ProximityPrize.SubmissionLower.ZnGdvBe
import ProximityPrize.SubmissionLower.ZAJiURc
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace qKlO94b
private def d:=0xb992d1a008a8dd00a4b0003387dfa8027a234030ec000defc9ba00b093d00e2b0003b21ca280302bb40406c000f71c25a00ced9d0120b0003fc624a8036c53404fec00104d96fa00e55fd015eb000422eef2803b6eb405f6c0010b1b95c00f421ac19c880043127e1803e125606dd80010cb5ef600fa5a181ca60004333499803ec3b607558000f38ec9500e38eb41ac48002a92fe00027c70004ae0000645bc80005dc4000b0800008be06000082b0000f60
local notation "q!" k:arg n:arg=>block 136 30 (0+8*k) n=unpack (d >>> (90*k))
private theorem b0:q! 0 8:=rfl
private theorem b1 :q! 1 8:=rfl
private theorem b2 :q! 2 8:=rfl
private theorem b3:q! 3 8:=rfl
private theorem b4 :q! 4 8:=rfl
private theorem b5:q! 5 8:=rfl
private theorem b6:q! 6 8:=rfl
private theorem b7:q! 7 8:=rfl
private theorem b8:q! 8 8:=rfl
private theorem b9:q! 9 8:=rfl
private theorem b10 :q! 10 8:=rfl
private theorem b11 :q! 11 8:=rfl
private theorem b12 :q! 12 8:=rfl
private theorem b13:q! 13 8:=rfl
private theorem b14 :q! 14 8:=rfl
private theorem b15:q! 15 8:=rfl
theorem p1_1 :block 136 30 0 128=sumPacked d 16:=join b0 (join b1 (join b2 (join b3 (join b4 (join b5 (join b6 (join b7 (join b8 (join b9 (join b10 (join b11 (join b12 (join b13 (join b14 (b15)))))))))))))))
end qKlO94b
end
section
set_option autoImplicit true
set_option maxRecDepth 4096
namespace qKlO94b
private def finish {B J n:ℕ} {v :Totals}
    (h:block B J 0 n=v) (hl:n=B+2*J) (w:Totals) (hv :v=w) :cL B J :=
  cL.ofEq ((hl ▸ h).trans hv)
def r1 :cL 136 30 :=
  let h:=join p1_1 (p1_2)
  finish h (by decide) ⟨0x53dd7,0x36311e5,0xff27992c⟩ rfl
def r2 :cL 171 38 :=
  let h:=join p2_1 (p2_2)
  finish h (by decide) ⟨0xa6ad4,0x8743999,0x31f72bff5⟩ rfl
def r3:cL 324 70 :=
  let h:=join p3_1 (join p3_2 (join p3_3 (join p3_4 (p3_5))))
  finish h (by decide) ⟨0x439e69,0x68052070,0x48a00bd68a⟩ rfl
def r4 :cL 327 71 :=
  let h:=join p4_1 (join p4_2 (join p4_3 (join p4_4 (p4_5))))
  finish h (by decide) ⟨0x45e3d0,0x6c798274,0x4c6dcf08c4⟩ rfl
end qKlO94b
end
section
set_option autoImplicit true
namespace qKlO94b
open Finset
open cu (Shape ku triangle)
open DP (bga azS)
open P5_7_2 (Aux)
open qMNIwTb (aL4 fullCap O3)
open qBZoH8d (paddedRank)
open agU (arY)

open private total asB from ProximityPrize.SubmissionLower.Z07A6ec
open private row aJm level cck from ProximityPrize.SubmissionLower.E7
open private bid from ProximityPrize.SubmissionLower.CN
open private origin aso amv gq1 biN gMy physical_eq nodes credit_eq gain_eq mode from ProximityPrize.SubmissionLower.ZkMhvdb
private theorem affine_total (s :Shape) (x y z :ℤ) (hj:s.J≤ s.B+1) :
    total s (2*x) (2*y) z =
      12*(∑ q∈range (s.B+1),∑ j∈range (min q s.J+1),(x+y*q+z*j)) := by
  rw [asB _ _ _ _ hj,mul_sum,mul_sum]
  apply sum_congr rfl
  intro q _
  unfold row
  rw [show (12 :ℤ)=6*2 by decide,mul_assoc (6:ℤ) 2 _,bid]
  ring
private def source (s :Shape) (r :ℕ) (h:ℤ) :ℤ :=
  total s (2*origin s r h) (-2*(131071-h)) 1
private def iL (s :Shape) :ℤ:=total s (2*((s.B:ℤ)+s.J)) (-2) 0
private theorem gtf (s :Shape) (r h:ℕ) (hh:h≤131071) (hj:s.J≤ s.B+1) :
    source s r h≤12*(ku s (amv h r s) :ℤ) := by
  rw [source,show -2*(131071-(h:ℤ))=2*(-(131071-h)) by ring,affine_total _ _ _ _ hj]
  unfold ku
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by decide)
  refine sum_le_sum fun q _=>sum_le_sum fun j _ => ?_
  simpa only [aso,Nat.cast_zero,mul_zero,zero_mul,sub_zero,Nat.zero_mul,Nat.sub_zero,
    one_mul,neg_mul,← sub_eq_add_neg] using gq1 s r h 0 q j hh
private theorem credit_total (s :Shape) (hj:s.J≤ s.B+1) :
    iL s=12*(arY s :ℤ) := by
  rw [iL,show (-2 :ℤ)=2*(-1) by decide,affine_total _ _ _ _ hj]
  unfold arY ku
  push_cast
  congr 1
  refine sum_congr rfl fun q hq=>sum_congr rfl fun _ _ => ?_
  rw [Nat.cast_sub (show q≤ s.B+s.J by have :=mem_range.mp hq; omega)]
  push_cast
  ring
private def x5 (s :Shape) (r cap:ℕ) (h:ℤ) :ℤ :=
  (triangle s.U:ℤ)*(source s r h - 2*nodes s+2*h*iL s) - 24*h*cap
def Check (lo hi:ℕ) (a :Aux) (cap:ℕ) :Bool :=
  let s :=a.shape
  let r :=a.dI
  decide (hi≤131071) && decide (s.J≤ s.B+1) &&
    decide (2*s.J≤ s.m) && decide (s.m+s.J≤ s.B+1) &&
    decide (0<biN s r lo) && decide (0<biN s r hi) &&
    decide (0<x5 s r cap lo) && decide (0<x5 s r cap hi)
def Good (lo hi:ℕ) (a :Aux) :Prop :=
  ∀ h,lo≤h→h≤hi→aL4 h a ∧
    bga a.shape+2*h*paddedRank a.shape <
      azS h a.shape+O3 h a (fullCap a.shape) false
theorem checked {lo hi:ℕ} {a :Aux} {cap:ℕ} (hr :paddedRank a.shape≤ cap)
    (hc:Check lo hi a cap=true) :Good lo hi a := by
  rcases a with ⟨r,s⟩
  simp only [Check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hk,hj⟩,hm⟩,hB⟩,hw₀⟩,hw₁⟩,hz₀⟩,hz₁⟩:=hc
  intro h hl hu
  have hh:=hu.trans hk
  have hlz :=Int.ofNat_le.mpr hl
  have huz :=Int.ofNat_le.mpr hu
  have hw (z :ℤ) :biN s r z=biN s r lo+(z-lo)*((s.B:ℤ)-2*r) := by
    unfold biN origin
    ring
  rw [hw] at hw₁
  refine ⟨gMy s r h hh ((hw _).symm ▸ cck hlz huz hw₀ hw₁),?_⟩
  have hz (z :ℤ) :x5 s r cap z=x5 s r cap lo +
      (z-lo)*(x5 s r cap (lo+1)-x5 s r cap lo) := by
    unfold x5 source origin total aJm level
    ring
  rw [hz] at hz₁
  have hpos :=(hz (h:ℤ)).symm ▸ cck hlz huz hz₀ hz₁
  have hs :=mul_le_mul_of_nonneg_left (gtf s r h hh hj)
    (Int.natCast_nonneg (triangle s.U))
  have hp:=physical_eq s hm hB
  have hhcap:=mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr hr) (show 0≤(h:ℤ) by positivity)
  unfold x5 at hpos
  rw [credit_total _ hj] at hpos
  apply Int.ofNat_lt.mp
  push_cast only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
  change (bga s :ℤ)+2*(h:ℤ)*(paddedRank s :ℤ) <
    (azS h s :ℤ)+(O3 h ⟨r,s⟩ (fullCap s) false :ℤ)
  rw [credit_eq,gain_eq]
  simp only [mode,Bool.false_eq_true,ite_false,Nat.zero_mul,Nat.sub_zero]
  nlinarith only [hpos,hp,hs,hhcap]
end qKlO94b
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qKlO94b
open P5_7_2 (Aux fO introduction jX stages)
open qMNIwTb (CJ)
private instance (b:fO) (a :Aux) :Decidable (CJ b false a) := by
  unfold CJ
  infer_instance
private def requests (b:fO) :List Aux :=
  (introduction b ++ (stages b).map (fun s=>Aux.mk s.dI s.free)).filter
    (fun a=>decide (CJ b false a))
private def a1 (u:ℕ) :Aux :=⟨6,⟨98,136,30,u⟩⟩
private def a2 (u:ℕ) :Aux :=⟨10,⟨123,171,38,u⟩⟩
private def a3 (u:ℕ) :Aux :=⟨24,⟨233,324,70,u⟩⟩
private def a4 (u:ℕ) :Aux :=⟨24,⟨235,327,71,u⟩⟩
private def GoodList (lo hi:ℕ) (as :List Aux) :Prop :=
  ∀ a∈as,Good lo hi a
private theorem good_cons {lo hi:ℕ} {a :Aux} {as :List Aux}
    (h:Good lo hi a) (hs :GoodList lo hi as) :GoodList lo hi (a::as) :=
  List.forall_mem_cons.mpr ⟨h,hs⟩
private theorem good_nil (lo hi:ℕ) :GoodList lo hi [] := by
  intro a ha
  exact (List.not_mem_nil ha).elim
private theorem good_row (lo hi:ℕ) (a :Aux)
    (r :cL a.shape.B a.shape.J) (hU:a.shape.B≤a.shape.U)
    (hc:Check lo hi a (r.cap a.shape.U)=true) :Good lo hi a :=
  checked (r.bound a.shape hU) hc
private theorem transfer {b:fO} {lo hi:ℕ} {as :List Aux}
    (h:GoodList lo hi as) (hlo: (jX b).lo=lo) (hhi: (jX b).hi=hi)
    (ha :requests b=as) :GoodList (jX b).lo (jX b).hi (requests b) := by
  rw [hlo,hhi,ha]
  exact h
set_option quotPrecheck false in
local notation "c!" l:arg h:arg a:arg r:arg t:arg =>
  good_cons (good_row l h a r (by decide) rfl) t
local notation "bVi" l:arg h:arg u4:arg u3:arg u1:arg u2:arg =>
  c! l h (a4 u4) r4
    (c! l h (a3 u3) r3 (c! l h (a1 u1) r1 (c! l h (a2 u2) r2 (good_nil l h))))
set_option maxHeartbeats 2000000 in
private theorem Ig (b:fO) (hb:2≤b.val) (hsmall:b.val<7) :
    GoodList (jX b).lo (jX b).hi (requests b) := by
  fin_cases b
  all_goals try first
    | exact (Nat.not_lt_of_ge hb (by decide)).elim
    | exact (Nat.not_lt_of_ge (by decide) hsmall).elim
  · exact transfer (bVi 2535 2535 6668 7225 16878 20092) rfl rfl rfl
  · exact transfer (bVi 2536 2536 6632 7182 16244 19415) rfl rfl rfl
  · exact transfer (bVi 2537 2537 6596 7140 15655 18782) rfl rfl rfl
  · exact transfer (bVi 2538 2538 6561 7098 15108 18190) rfl rfl rfl
  · exact transfer (bVi 2539 2541 6526 7057 14598 17634) rfl rfl rfl
theorem proof :P6_7_4.c3:= by
  intro b hb h hlo hhi a ha hp
  have hsmall:b.val<7:=hp.1
  have ha' : a∈requests b:= by
    apply List.mem_filter.mpr
    refine ⟨List.mem_append.mpr ?_,decide_eq_true hp⟩
    rcases ha with ⟨_,hm⟩ | ⟨s,hs,rfl⟩
    · exact Or.inl hm
    · exact Or.inr (List.mem_map.mpr ⟨s,hs,rfl⟩)
  exact Ig b hb hsmall a ha' h hlo hhi
end qKlO94b
end
section
set_option autoImplicit true
namespace qjA4dna
def c1 :Prop :=qbjv5ec.c1
def c2 :Prop :=qbjv5ec.c2
theorem of_children (h1 :c1) (h2 :c2) :P6_7_8.c1 :=
  qbjv5ec.of_children h1 h2
end qjA4dna
end
section
set_option autoImplicit true
namespace q5aZ59c
theorem proof :P6_7_8.c2 :=
  qrKC9pb.of_children
    qWIOgVd.proof
    qazuAoe.proof
    (qyUzJvd.of_children
      qnCt0Qc.proof qc2iTLd.proof q6lciJe.proof)
    (qj0Yp9c.of_children
      (qO4AyGb.of_children qWz9F7b.proof qW0d9ye.proof)
      qBTXDtb.proof)
end q5aZ59c
end
