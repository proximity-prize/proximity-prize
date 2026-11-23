import ProximityPrize.SubmissionLower.AY
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.E6
set_option Elab.async false
set_option autoImplicit true
section
namespace cS
open aR (Shape ceilDiv)
open bJ (Bank sC x5 oL dJ lY aIx aPd)
open wV (a9P zN C8 pS)
open scoped BigOperators
def yF (count:a9P) (b:Bank) (x :Shape) :ℕ :=
 ceilDiv (x5 b - sC*zN count b x) (sC*count b oL)
abbrev order :=yF pS
def ye (l:ℕ) (x :Shape) :ℕ :=
  let s :=order .dB x
  C8 l (dJ x gW.Bank.ag.box l)
    (C8 s (dJ x gW.Bank.dB.box s) (lY x))
def j3 (t:ℕ) :ℕ:=aIx t+aPd
def xQ (x :Shape) :Prop :=
  x.t=2 ∧
    ((x.j=6∧12≤x.b∧x.b≤15) ∨
      (x.j=7∧(x.b=3∨x.b=8)))
end cS
end
section
namespace cS
open aR (Shape ceilDiv)
open bJ (Bank H6 Xd W5 Ix YK can EW)
open private ceil_le_iff from ProximityPrize.SubmissionLower.E1
private theorem gvg (a r t:ℕ) :Monotone (YK a r t) := by
 intro l m hlm
 by_cases hr :r=a
 · simp only [YK,ite_eq_left hr]
   exact Nat.add_le_add_left hlm _
 simp only [YK,ite_eq_right hr]
 apply max_le_max le_rfl
 apply Finset.sup_le
 intro s hs
 have hceil:ceilDiv l s≤ ceilDiv m s :=
   Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right hlm s) 1)
 by_cases h:r*(s - 1)<ceilDiv l s
 · have h' := h.trans_le hceil
   simp only [ite_eq_left h]
   exact (Nat.sub_le_sub_right (Nat.add_le_add_left hceil _) _).trans
    (Finset.le_sup_of_le hs (by simp only [ite_eq_left h',le_refl]))
 · simp only [ite_eq_right h,Nat.zero_le]
theorem bpY {b:Bank} {x :Shape} {v a r l D:ℕ}
   (hr :r≤a) (hl:1≤l)
   (ha :W5 (Xd a r) x (H6 b x a r)<v)
   (hm:Ix x (H6 b x a r) ≤
     (v-W5 (Xd a r) x (H6 b x a r))*l)
   (hd:YK a r x.t l - 1≤D) :
   EW b x v a≤D:= by
 unfold EW
 rw [Finset.fold_min_le]
 right
 refine ⟨r,Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hr),?_⟩
 unfold can
 simp only [ite_eq_left ha]
 have hc:=(ceil_le_iff (Nat.sub_pos_of_lt ha)).mpr hm
 exact (Nat.sub_le_sub_right (gvg a r x.t (max_le hl hc)) 1).trans hd
end cS
end
section
namespace cS
open aR (Shape)
open bJ (EW YK Ix H6 Xd W5)

open scoped BigOperators
private abbrev x :Shape :=⟨125,51,13⟩
private abbrev v :ℕ:=0x3a25a1bb63397c6
private def D (a :ℕ) :ℕ:=if a<26 then 54 else 58
private theorem fZm {a r l m h:ℕ}
  (hr :r≤a) (hl:1≤l)
  (hm:Ix x (H6 .ag x a r)=m)
  (hh:W5 (Xd a r) x (H6 .ag x a r)=h)
  (hv :h<v) (hml:m≤(v - h)*l)
  (hd:YK a r x.t l - 1≤D a) :
  EW .ag x v a≤D a :=
 bpY hr hl (hh.symm ▸ hv) (hm.symm ▸ hh.symm ▸ hml) hd
local notation "az" av "," rv "," lv "," mv "," hv =>
 fZm (a :=av) (r :=rv) (l:=lv) (m:=mv) (h:=hv) (by decide) (by decide)
  rfl rfl (by decide) (by decide) (by decide)
end cS
end
section
namespace cS



open scoped BigOperators
def kW:ℕ→ℕ
 | 0=>0x4c867f3a9f09e0
 | 1=>0x444f4de9de0c82
 | 2=>0x3c850584275490
 | 3=>0x3529f9f61dd465
 | 4=>0x2e3fcf99bf4638
 | 5=>0x27c8c43ebc5a65
 | 6=>0x21c690d6303589
 | 7=>0x1c3b5fdba018c2
 | 8=>0x1728fc02548098
 | 9=>0x12917f52c09124
 | 10=>0xe76c355178ce1
 | 11=>0xadad498264c96
 | 12=>0x7bf987375c745
 | 13=>0x527110deadb8b
 | _=>0
end cS
end
