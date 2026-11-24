import ProximityPrize.SubmissionLower.ZUt8KUb
import ProximityPrize.SubmissionLower.Z6jV1pb
import ProximityPrize.SubmissionLower.ZyrUiId
set_option Elab.async false
private theorem bothR {p q:Bool} {C:Prop} (h:(p && q)=true) (f:p=true → q=true → C) :C:= by
  simp only [Bool.and_eq_true] at h
  exact f h.1 h.2
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
section
section
set_option autoImplicit true
namespace qK9VCOd
open Finset
open P5_7_2 (TopRow)
open q7F2qKe (weakAgreement)
open q7IA62d (ama width)
open scoped BigOperators
def residual (t:TopRow) (d:ℕ) :ℕ :=
 ama t (fun q c j=>width t q c j-3*d*c)
private theorem reindex (t:TopRow) (f :ℕ→ℕ→ℕ→ℕ) (hc:2*t.YM≤t.shape.J) :
    ama t f = ∑ c∈range (t.YM+1),∑ j∈range (t.shape.J-2*c+1),
      ∑ q∈Ico (c+j) (t.shape.B+1),f q c j:= by
  classical
  calc
    _ = ∑ q∈range (t.shape.B+1),∑ c∈range (t.YM+1),
          ∑ j∈range (t.shape.J-2*c+1),if c+j≤q then f q c j else 0:= by
      unfold ama
      refine sum_congr rfl fun q _ => ?_
      have hcap:min t.YM (t.shape.J/2)=t.YM:=min_eq_left (by omega)
      rw [hcap]
      trans ∑ c∈range (min q t.YM+1),∑ j∈range (t.shape.J-2*c+1),
        if c+j≤q then f q c j else 0
      · refine sum_congr rfl fun c hc' => ?_
        rw [← sum_filter]
        have hf : (range (t.shape.J-2*c+1)).filter (fun j=>c+j≤q) =
            range (min (q-c) (t.shape.J-2*c)+1) := by
          ext j
          simp only [mem_filter,mem_range] at *
          omega
        rw [hf]
      · refine sum_subset (range_mono (by omega)) fun c hc' hq => ?_
        rw [mem_range] at hc' hq
        apply sum_eq_zero
        intro j _
        have hn : ¬ c+j≤q:= by omega
        simp [hn]
    _ = _:= by
      rw [sum_comm]
      refine sum_congr rfl fun c _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      rw [← sum_filter]
      congr 1
      ext q
      simp only [mem_filter,mem_range,mem_Ico,and_comm]
private def ahB (n x :ℕ) :ℕ :=
 let k :=min n (x/131071+1)
 k*x - 131071*(k*(k-1)/2)
private theorem falling_eq (n x :ℕ) :
  (∑ q∈range n,(x-131071*q))=ahB n x := by
 let k :=min n (x/131071+1)
 have hcut: (∑ q∈range k,(x-131071*q)) = ∑ q∈range n,(x-131071*q) := by
  refine sum_subset (range_mono (min_le_left _ _)) fun q hq hnk => ?_
  simp only [mem_range,k] at hq hnk
  omega
 have hk (q:ℕ) (hq:q∈range k) :131071*q≤x := by
  simp only [mem_range,k] at hq
  omega
 rw [← hcut,sum_tsub_distrib _ hk,sum_const,card_range,smul_eq_mul,
  ← mul_sum,sum_range_id]
 rfl
private def O0 (m B d c j:ℕ) :ℕ :=
 ahB (B+1-(c+j)) (m*weakAgreement+j+2*c-3*d*c-131071*(c+j))
private theorem oB (m B d c j:ℕ) :
   (∑ q∈Ico (c+j) (B+1),(m*weakAgreement+j+2*c-131071*q-3*d*c)) =
     O0 m B d c j:= by
 rw [sum_Ico_eq_sum_range,O0,← falling_eq]
 refine sum_congr rfl fun q _ => ?_
 rw [Nat.mul_add]
 omega
private def addRange (f :ℕ→ℕ) :ℕ→ℕ
 | 0=>0
 | n+1=>addRange f n+f n
private theorem addRange_eq (f :ℕ→ℕ) (n:ℕ) :
   addRange f n = ∑ j∈range n,f j:= by
 induction n with
 | zero=>simp [addRange]
 | succ n ih=>rw [addRange,sum_range_succ,ih]
private abbrev row (m B J d c:ℕ) :ℕ :=
 addRange (O0 m B d c) (J-2*c+1)
private abbrev rows (m B J d n:ℕ) :ℕ:=addRange (row m B J d) n
private theorem reduce {t:TopRow} {m B J C d a :ℕ}
  (hm:t.shape.m=m) (hB:t.shape.B=B) (hJ:t.shape.J=J) (hC:t.YM=C)
  (hc:2*C≤J) (ha :rows m B J d (C+1)=a) :residual t d=a := by
 unfold residual
 rw [reindex _ _ (by rwa [hC,hJ]),hC,hB,hJ]
 simp only [width,hm,oB,← addRange_eq]
 exact ha
private theorem start (m B J d:ℕ) :rows m B J d 0=0:=rfl
private theorem checked {m B J d n a b:ℕ} (hs :rows m B J d n=a)
  (hr :row m B J d n=b) :rows m B J d (n+1)=a+b:= by
 change rows m B J d n+row m B J d n=a+b
 rw [hs,hr]
set_option quotPrecheck false in
local notation:65 h:65 " +! " v:66=>checked (b:=v) h (by decide +kernel)
private theorem r1 :rows 64 87 27 0 13=0x11da33a12a :=
 start 64 87 27 0
  +! 0x26a8006c2 +! 0x23d68585b +! 0x21084a87c +! 0x1e3d0f72b +! 0x1b749446e
  +! 0x18ae9904b +! 0x15eaddac8 +! 0x1329223eb +! 0x106926bba +! 0xdaaab23b
  +! 0xaed6f774 +! 0x83133b6b +! 0x575b7e26
theorem value1 {t:TopRow} (hm:t.shape.m=64) (hB:t.shape.B=87)
  (hJ:t.shape.J=27) (hC:t.YM=12) :residual t 0=0x11da33a12a :=
 reduce hm hB hJ hC (by decide) r1
private theorem r2 :rows 120 164 50 2541 20=0xbf8b00636a :=
 start 120 164 50 2541
  +! 0xf6f1314af +! 0xecdd2e886 +! 0xe2d35dcea +! 0xd8d37f1e1 +! 0xcedd52771
  +! 0xc4f097da0 +! 0xbb0d0f474 +! 0xb13278bf3 +! 0xa76094423 +! 0x9d9721d0a
  +! 0x93d5f86af +! 0x8a1cde8c6 +! 0x806b6f48e +! 0x76c16aa0d +! 0x6d1e90949
  +! 0x6382a1248 +! 0x59ed5c510 +! 0x505e821a7 +! 0x46d5d2813 +! 0x3d530d85a
theorem value2 {t:TopRow} (hm:t.shape.m=120) (hB:t.shape.B=164)
  (hJ:t.shape.J=50) (hC:t.YM=19) :residual t 2541=0xbf8b00636a :=
 reduce hm hB hJ hC (by decide) r2
private theorem r3:rows 128 174 52 2703 23=0xf4950f7f08 :=
 start 128 174 52 2703
  +! 0x12642fc423 +! 0x11ab64cacf +! 0x10f3498d52 +! 0x103bda0bb2 +! 0xf851245f5
  +! 0xeceee3c21 +! 0xe1969ee3c +! 0xd64815c4c +! 0xcb0308657 +! 0xbfc736c63
  +! 0xb49460e76 +! 0xa96a46c96 +! 0x9e48a86c9 +! 0x932f45d15 +! 0x881ddef80
  +! 0x7d1433e10 +! 0x7212048cb +! 0x671710fb7 +! 0x5c23192da +! 0x5135dd23a
  +! 0x464f1cddd +! 0x3b6e985c9 +! 0x30940fa04
theorem value3 {t:TopRow} (hm:t.shape.m=128) (hB:t.shape.B=174)
  (hJ:t.shape.J=52) (hC:t.YM=22) :residual t 2703=0xf4950f7f08 :=
 reduce hm hB hJ hC (by decide) r3
end qK9VCOd
end
section
set_option autoImplicit true
namespace qB9xHGe
open Finset
open scoped BigOperators
open P5_7_2 (fO)
open q7F2qKe
open TD (GM FP)
def bookGlobal (b:fO) (i:ℕ) :GM:= fun k=>(multiplierNum b i k :ℚ)/ 1000
def bookFree (b:fO) (o:ℕ) :GM:= fun k=>(multiplierNum b (16+o) k :ℚ)/ 1000
def bookResidual (b:fO) (o:ℕ) :GM:= fun k=>(residualNum b o k :ℚ)/0x8000000
def ng (b:fO) (o j:ℕ) (k :Fin 4) :ℚ :=
 sumPrefix (bookGlobal b) j k+(if afterFree b≤j then bookFree b o k else 0)+bookResidual b o k
structure StopRates (b:fO) (o j:ℕ) where
 dm:ℚ
 a :ℚ
 h:ℚ
 bgt:aSz b dm a h
 individual : ∀ x :GM,Individual b o j x →
   min (projectionCap b) (FP (SS b j 0) x)≤dm
 gH : ∀ k,a*SS b j 0 k+h*SS b j 1 k≤ng b o j k
noncomputable def Ya (b:fO) :ℚ :=
 ((earlyFee b+pointFee b+(projectionCap b).ceil.toNat :ℕ) :ℚ) +
   (∑ i∈stops b,FP (bookGlobal b i) (globalCap b i)) +
   (∑ o∈origins b,FP (bookFree b o) (originFreeCap b o))+factorBill b (bookResidual b)
def lineCredit (b:fO) (o:ℕ) (q:Fin 3) :ℚ :=
  factorUnit (bookResidual b o) (originCutter b o) q -
    factorUnit (bookResidual b o) (aur (originBudget b o)) q
end qB9xHGe
end
section
set_option autoImplicit true
namespace qgVOTOa
open qMHqmcc (GG receipt test)
set_option quotPrecheck false in
local notation "r!" n:arg=>bothR (by decide +kernel) (receipt (b:=b8) (x :=test b8 n) 2545 rfl)
theorem wQf0:GG b8 11 1:=⟨r! 11,True.intro⟩
theorem wQf1:GG b8 10 1:=⟨r! 10,True.intro⟩
theorem wQf2:GG b8 9 1:=⟨r! 9,True.intro⟩
theorem wQf3:GG b8 8 1:=⟨r! 8,True.intro⟩
theorem wQf4:GG b8 7 1:=⟨r! 7,True.intro⟩
theorem wQf5:GG b8 6 1:=⟨r! 6,True.intro⟩
theorem wQf6:GG b8 5 1:=⟨r! 5,True.intro⟩
theorem wQf7:GG b8 4 1:=⟨r! 4,True.intro⟩
theorem wQf8:GG b8 3 1:=⟨r! 3,True.intro⟩
theorem wQf9:GG b8 2 1:=⟨r! 2,True.intro⟩
theorem wQf10:GG b8 1 1:=⟨r! 1,True.intro⟩
theorem wQf11:GG b8 0 1:=⟨r! 0,True.intro⟩
theorem a:GG b8 0 12 :=⟨wQf0.1,wQf1.1,wQf2.1,wQf3.1,wQf4.1,wQf5.1,wQf6.1,wQf7.1,wQf8.1,wQf9.1,wQf10.1,wQf11.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
namespace qgVOTOa
open qMHqmcc (GG receipt test)
set_option quotPrecheck false in
local notation "r!" n:arg=>bothR (by decide +kernel) (receipt (b:=b8) (x :=test b8 n) 2545 rfl)
theorem wQf12:GG b8 23 1:=⟨r! 23,True.intro⟩
theorem wQf13:GG b8 22 1:=⟨r! 22,True.intro⟩
theorem wQf14:GG b8 21 1:=⟨r! 21,True.intro⟩
theorem wQf15:GG b8 20 1:=⟨r! 20,True.intro⟩
theorem wQf16:GG b8 19 1:=⟨r! 19,True.intro⟩
theorem wQf17:GG b8 18 1:=⟨r! 18,True.intro⟩
theorem wQf18:GG b8 17 1:=⟨r! 17,True.intro⟩
theorem wQf19:GG b8 16 1:=⟨r! 16,True.intro⟩
theorem wQf20:GG b8 15 1:=⟨r! 15,True.intro⟩
theorem wQf21:GG b8 14 1:=⟨r! 14,True.intro⟩
theorem wQf22:GG b8 13 1:=⟨r! 13,True.intro⟩
theorem wQf23:GG b8 12 1:=⟨r! 12,True.intro⟩
theorem b:GG b8 12 12 :=⟨wQf12.1,wQf13.1,wQf14.1,wQf15.1,wQf16.1,wQf17.1,wQf18.1,wQf19.1,wQf20.1,wQf21.1,wQf22.1,wQf23.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
namespace qgVOTOa
open qMHqmcc (GG receipt test)
set_option quotPrecheck false in
local notation "r!" n:arg=>bothR (by decide +kernel) (receipt (b:=b8) (x :=test b8 n) 2545 rfl)
theorem wQf24:GG b8 35 1:=⟨r! 35,True.intro⟩
theorem wQf25:GG b8 34 1:=⟨r! 34,True.intro⟩
theorem wQf26:GG b8 33 1:=⟨r! 33,True.intro⟩
theorem wQf27:GG b8 32 1:=⟨r! 32,True.intro⟩
theorem wQf28:GG b8 31 1:=⟨r! 31,True.intro⟩
theorem wQf29:GG b8 30 1:=⟨r! 30,True.intro⟩
theorem wQf30:GG b8 29 1:=⟨r! 29,True.intro⟩
theorem wQf31:GG b8 28 1:=⟨r! 28,True.intro⟩
theorem wQf32:GG b8 27 1:=⟨r! 27,True.intro⟩
theorem wQf33:GG b8 26 1:=⟨r! 26,True.intro⟩
theorem wQf34:GG b8 25 1:=⟨r! 25,True.intro⟩
theorem wQf35:GG b8 24 1:=⟨r! 24,True.intro⟩
theorem c:GG b8 24 12 :=⟨wQf24.1,wQf25.1,wQf26.1,wQf27.1,wQf28.1,wQf29.1,wQf30.1,wQf31.1,wQf32.1,wQf33.1,wQf34.1,wQf35.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
namespace qgVOTOa
open qMHqmcc (GG receipt test)
set_option quotPrecheck false in
local notation "r!" n:arg=>bothR (by decide +kernel) (receipt (b:=b8) (x :=test b8 n) 2545 rfl)
theorem wQf36:GG b8 47 1:=⟨r! 47,True.intro⟩
theorem wQf37:GG b8 46 1:=⟨r! 46,True.intro⟩
theorem wQf38:GG b8 45 1:=⟨r! 45,True.intro⟩
theorem wQf39:GG b8 44 1:=⟨r! 44,True.intro⟩
theorem wQf40:GG b8 43 1:=⟨r! 43,True.intro⟩
theorem wQf41:GG b8 42 1:=⟨r! 42,True.intro⟩
theorem wQf42:GG b8 41 1:=⟨r! 41,True.intro⟩
theorem wQf43:GG b8 40 1:=⟨r! 40,True.intro⟩
theorem wQf44:GG b8 39 1:=⟨r! 39,True.intro⟩
theorem wQf45:GG b8 38 1:=⟨r! 38,True.intro⟩
theorem wQf46:GG b8 37 1:=⟨r! 37,True.intro⟩
theorem wQf47:GG b8 36 1:=⟨r! 36,True.intro⟩
theorem d:GG b8 36 12 :=⟨wQf36.1,wQf37.1,wQf38.1,wQf39.1,wQf40.1,wQf41.1,wQf42.1,wQf43.1,wQf44.1,wQf45.1,wQf46.1,wQf47.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
namespace qgVOTOa
open qMHqmcc (GG receipt test)
set_option quotPrecheck false in
local notation "r!" n:arg=>bothR (by decide +kernel) (receipt (b:=b8) (x :=test b8 n) 2545 rfl)
theorem wQf48:GG b8 59 1:=⟨r! 59,True.intro⟩
theorem wQf49:GG b8 58 1:=⟨r! 58,True.intro⟩
theorem wQf50:GG b8 57 1:=⟨r! 57,True.intro⟩
theorem wQf51:GG b8 56 1:=⟨r! 56,True.intro⟩
theorem wQf52:GG b8 55 1:=⟨r! 55,True.intro⟩
theorem wQf53:GG b8 54 1:=⟨r! 54,True.intro⟩
theorem wQf54:GG b8 53 1:=⟨r! 53,True.intro⟩
theorem wQf55:GG b8 52 1:=⟨r! 52,True.intro⟩
theorem wQf56:GG b8 51 1:=⟨r! 51,True.intro⟩
theorem wQf57:GG b8 50 1:=⟨r! 50,True.intro⟩
theorem wQf58:GG b8 49 1:=⟨r! 49,True.intro⟩
theorem wQf59:GG b8 48 1:=⟨r! 48,True.intro⟩
theorem e:GG b8 48 12 :=⟨wQf48.1,wQf49.1,wQf50.1,wQf51.1,wQf52.1,wQf53.1,wQf54.1,wQf55.1,wQf56.1,wQf57.1,wQf58.1,wQf59.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
namespace qgVOTOa
open qMHqmcc (GG receipt test)
set_option quotPrecheck false in
local notation "r!" n:arg=>bothR (by decide +kernel) (receipt (b:=b8) (x :=test b8 n) 2545 rfl)
theorem wQf60:GG b8 71 1:=⟨r! 71,True.intro⟩
theorem wQf61:GG b8 70 1:=⟨r! 70,True.intro⟩
theorem wQf62:GG b8 69 1:=⟨r! 69,True.intro⟩
theorem wQf63:GG b8 68 1:=⟨r! 68,True.intro⟩
theorem wQf64:GG b8 67 1:=⟨r! 67,True.intro⟩
theorem wQf65:GG b8 66 1:=⟨r! 66,True.intro⟩
theorem wQf66:GG b8 65 1:=⟨r! 65,True.intro⟩
theorem wQf67:GG b8 64 1:=⟨r! 64,True.intro⟩
theorem wQf68:GG b8 63 1:=⟨r! 63,True.intro⟩
theorem wQf69:GG b8 62 1:=⟨r! 62,True.intro⟩
theorem wQf70:GG b8 61 1:=⟨r! 61,True.intro⟩
theorem wQf71:GG b8 60 1:=⟨r! 60,True.intro⟩
theorem f:GG b8 60 12 :=⟨wQf60.1,wQf61.1,wQf62.1,wQf63.1,wQf64.1,wQf65.1,wQf66.1,wQf67.1,wQf68.1,wQf69.1,wQf70.1,wQf71.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
namespace qgVOTOa
open qMHqmcc (GG receipt test)
set_option quotPrecheck false in
local notation "r!" n:arg=>bothR (by decide +kernel) (receipt (b:=b8) (x :=test b8 n) 2545 rfl)
theorem wQf72:GG b8 83 1:=⟨r! 83,True.intro⟩
theorem wQf73:GG b8 82 1:=⟨r! 82,True.intro⟩
theorem wQf74:GG b8 81 1:=⟨r! 81,True.intro⟩
theorem wQf75:GG b8 80 1:=⟨r! 80,True.intro⟩
theorem wQf76:GG b8 79 1:=⟨r! 79,True.intro⟩
theorem wQf77:GG b8 78 1:=⟨r! 78,True.intro⟩
theorem wQf78:GG b8 77 1:=⟨r! 77,True.intro⟩
theorem wQf79:GG b8 76 1:=⟨r! 76,True.intro⟩
theorem wQf80:GG b8 75 1:=⟨r! 75,True.intro⟩
theorem wQf81:GG b8 74 1:=⟨r! 74,True.intro⟩
theorem wQf82:GG b8 73 1:=⟨r! 73,True.intro⟩
theorem wQf83:GG b8 72 1:=⟨r! 72,True.intro⟩
theorem g:GG b8 72 12 :=⟨wQf72.1,wQf73.1,wQf74.1,wQf75.1,wQf76.1,wQf77.1,wQf78.1,wQf79.1,wQf80.1,wQf81.1,wQf82.1,wQf83.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
namespace qgVOTOa
open qMHqmcc (GG receipt test)
set_option quotPrecheck false in
local notation "r!" n:arg=>bothR (by decide +kernel) (receipt (b:=b8) (x :=test b8 n) 2545 rfl)
theorem wQf84:GG b8 95 1:=⟨r! 95,True.intro⟩
theorem wQf85:GG b8 94 1:=⟨r! 94,True.intro⟩
theorem wQf86:GG b8 93 1:=⟨r! 93,True.intro⟩
theorem wQf87:GG b8 92 1:=⟨r! 92,True.intro⟩
theorem wQf88:GG b8 91 1:=⟨r! 91,True.intro⟩
theorem wQf89:GG b8 90 1:=⟨r! 90,True.intro⟩
theorem wQf90:GG b8 89 1:=⟨r! 89,True.intro⟩
theorem wQf91:GG b8 88 1:=⟨r! 88,True.intro⟩
theorem wQf92:GG b8 87 1:=⟨r! 87,True.intro⟩
theorem wQf93:GG b8 86 1:=⟨r! 86,True.intro⟩
theorem wQf94:GG b8 85 1:=⟨r! 85,True.intro⟩
theorem wQf95:GG b8 84 1:=⟨r! 84,True.intro⟩
theorem h:GG b8 84 12 :=⟨wQf84.1,wQf85.1,wQf86.1,wQf87.1,wQf88.1,wQf89.1,wQf90.1,wQf91.1,wQf92.1,wQf93.1,wQf94.1,wQf95.1,True.intro⟩
end qgVOTOa
end
end
section
section
set_option autoImplicit true
namespace q3UL7Tb
open qMHqmcc (GG receipt test appendGrades)
set_option quotPrecheck false in
local notation "r!" i:arg =>
  bothR (by decide +kernel) (@receipt b4 (test b4 i) 2537 rfl)
private theorem r0:GG b4 0 4 :=⟨r! 3,r! 2,r! 1,r! 0,True.intro⟩
private theorem r4 :GG b4 4 4 :=⟨r! 7,r! 6,r! 5,r! 4,True.intro⟩
private theorem r8:GG b4 8 4 :=⟨r! 11,r! 10,r! 9,r! 8,True.intro⟩
theorem b4a :GG b4 0 12 :=appendGrades (appendGrades r0 r4) r8
end q3UL7Tb
end
section
set_option autoImplicit true
namespace q3UL7Tb
open qMHqmcc (GG receipt test appendGrades)
set_option quotPrecheck false in
local notation "r!" i:arg =>
  bothR (by decide +kernel) (@receipt b4 (test b4 i) 2537 rfl)
private theorem dK:GG b4 12 4 :=⟨r! 15,r! 14,r! 13,r! 12,True.intro⟩
private theorem iu:GG b4 16 4 :=⟨r! 19,r! 18,r! 17,r! 16,True.intro⟩
private theorem jV:GG b4 20 4 :=⟨r! 23,r! 22,r! 21,r! 20,True.intro⟩
private theorem nJ:GG b4 24 4 :=⟨r! 27,r! 26,r! 25,r! 24,True.intro⟩
private theorem qH :GG b4 28 4 :=⟨r! 31,r! 30,r! 29,r! 28,True.intro⟩
theorem b4b:GG b4 12 20 :=
  appendGrades (appendGrades (appendGrades (appendGrades dK iu) jV) nJ) qH
end q3UL7Tb
end
section
set_option autoImplicit true
namespace q3UL7Tb
open qMHqmcc (GG receipt test appendGrades)
set_option quotPrecheck false in
local notation "r!" i:arg =>
  bothR (by decide +kernel) (@receipt b4 (test b4 i) 2537 rfl)
private theorem r32 :GG b4 32 4 :=⟨r! 35,r! 34,r! 33,r! 32,True.intro⟩
private theorem EZ:GG b4 36 4 :=⟨r! 39,r! 38,r! 37,r! 36,True.intro⟩
private theorem Hz :GG b4 40 4 :=⟨r! 43,r! 42,r! 41,r! 40,True.intro⟩
private theorem Xv :GG b4 44 4 :=⟨r! 47,r! 46,r! 45,r! 44,True.intro⟩
private theorem zB:GG b4 48 4 :=⟨r! 51,r! 50,r! 49,r! 48,True.intro⟩
theorem b4c:GG b4 32 20 :=
  appendGrades (appendGrades (appendGrades (appendGrades r32 EZ) Hz) Xv) zB
end q3UL7Tb
end
section
set_option autoImplicit true
namespace q3UL7Tb
open qMHqmcc (GG receipt test appendGrades)
set_option quotPrecheck false in
local notation "r!" i:arg =>
  bothR (by decide +kernel) (@receipt b4 (test b4 i) 2537 rfl)
private theorem De :GG b4 52 4 :=⟨r! 55,r! 54,r! 53,r! 52,True.intro⟩
private theorem LH :GG b4 56 4 :=⟨r! 59,r! 58,r! 57,r! 56,True.intro⟩
private theorem OL:GG b4 60 4 :=⟨r! 63,r! 62,r! 61,r! 60,True.intro⟩
private theorem r64 :GG b4 64 4 :=⟨r! 67,r! 66,r! 65,r! 64,True.intro⟩
private theorem r68:GG b4 68 4 :=⟨r! 71,r! 70,r! 69,r! 68,True.intro⟩
theorem b4d:GG b4 52 20 :=
  appendGrades (appendGrades (appendGrades (appendGrades De LH) OL) r64) r68
end q3UL7Tb
end
section
set_option autoImplicit true
namespace q3UL7Tb
open qMHqmcc (GG receipt test appendGrades)
set_option quotPrecheck false in
local notation "r!" i:arg =>
  bothR (by decide +kernel) (@receipt b4 (test b4 i) 2537 rfl)
private theorem Vo:GG b4 72 4 :=⟨r! 75,r! 74,r! 73,r! 72,True.intro⟩
private theorem r76:GG b4 76 4 :=⟨r! 79,r! 78,r! 77,r! 76,True.intro⟩
private theorem Xe :GG b4 80 4 :=⟨r! 83,r! 82,r! 81,r! 80,True.intro⟩
private theorem r84 :GG b4 84 4 :=⟨r! 87,r! 86,r! 85,r! 84,True.intro⟩
private theorem r88:GG b4 88 4 :=⟨r! 91,r! 90,r! 89,r! 88,True.intro⟩
theorem b4e :GG b4 72 20 :=
  appendGrades (appendGrades (appendGrades (appendGrades Vo r76) Xe) r84) r88
end q3UL7Tb
end
section
set_option autoImplicit true
namespace q3UL7Tb
open qMHqmcc (GG receipt test appendGrades)
set_option quotPrecheck false in
local notation "r!" i:arg =>
  bothR (by decide +kernel) (@receipt b4 (test b4 i) 2537 rfl)
private theorem r92 :GG b4 92 4 :=⟨r! 95,r! 94,r! 93,r! 92,True.intro⟩
private theorem r96:GG b4 96 4 :=⟨r! 99,r! 98,r! 97,r! 96,True.intro⟩
private theorem eWB:GG b4 100 4 :=⟨r! 103,r! 102,r! 101,r! 100,True.intro⟩
private theorem abK:GG b4 104 4 :=⟨r! 107,r! 106,r! 105,r! 104,True.intro⟩
private theorem cc9:GG b4 108 4 :=⟨r! 111,r! 110,r! 109,r! 108,True.intro⟩
private theorem anO:GG b4 112 3:=⟨r! 114,r! 113,r! 112,True.intro⟩
theorem b4f :GG b4 92 23 :=
  appendGrades (appendGrades (appendGrades (appendGrades (appendGrades r92 r96) eWB) abK) cc9) anO
end q3UL7Tb
end
end
section
section
set_option autoImplicit true
namespace q9NbxKa
noncomputable section
open P5 (K p)
open P5_7_1 (Input)

open cu (L)
open gT (kM bbt aSf)
open YY (U7)
structure DescendedMarks (x :Input) (T:Finset K) (J:Ideal kM)
  (Q:MvPolynomial (Fin 2) L) (e H :ℕ) :Prop where
 subset :T⊆x.Γ
 curve :bbt J e H
 irreducible :Irreducible Q
 projection :J.comap gT.pZ=Ideal.span {MvPolynomial.map U7 Q}
 plane_pos :0<Q.totalDegree
 seed_lt:Q.totalDegree*e<p
 marks : ∀ γ∈T,aSf J (x.M.label γ) (x.F.scalar γ)
abbrev nativeSlope (d:ℚ) (e :ℕ) :ℚ:=d/(3*(e :ℚ))+4*e+8
end
end q9NbxKa
end
section
set_option autoImplicit true
section
section
namespace qJeTDGe
noncomputable section
open P5_7_1 (IntroIndex)
open qehP9ee

open scoped BigOperators
def digit (width packed i:ℕ) :ℕ:=(packed >>> (width*i)) % 2^width
def degreeDigit (o:IntroIndex) (t:Trial) :ℕ :=
 digit 29 0x88cf45a347c323958ffaf28c4271834f5fd004c14d902be721a203bfe31a254ba01fd1e1c0f8d508065912b8bd8b0536099b295fd94c68f13177360500804f23a002c88b24204672619fe862020ef818103d24806907c38fe5d24382681898ed1b9aa22157e3d38ced0568522432d5aba259f55b1ea83b58245e4c811a070e0742a655b5f1b21b1d345ca3c8f48428a18f1921ce502153cc41538f8a104f0db0d8cc6780e3ece806b345602da4a0481c6f3958af430821375234d9d5013f604901ac767410ce5360cd4d2d0aa03d780b692800565af60248a3d80e9fbd307c236578a7afe98f0f0639c701c048d9f103183e62271b02f20ee28e01f97ccc0e79ad80657db18db2b6b3703e4c570ea990960239038a3b4305309a943113bfe2427ba91d62d208235fab8113792a070f2277cdbb1e2e67ebbd37e76f27eb56f52fdbdb184074e4c2ac7f682131cd41bb5bb581c38c6c0d2b08e05a809a8362dbe3094ddc12438c1c76da8fb2cdf2d30460adbc29209a41dfbcfe183adbb01e231f00ec9cdc0602646762c766aafcce7d23cda34767b6eb2cc29ed0423ab5c2d8fc9a239384b1dca28081db52e00dc886a05f52df6efbea4253beed4e13df205b787de228dc19840eee2826d3b481c8be0c172d32d01c134b80daf6c4059a1107f81ee22b6568dd04d66b86a1c99c280ee2a0578b6082ba0ff021bf8131a8f73902615f241336354079238080bb5562e9679ed16363be716195c2ac61ff867f165c3133b8c1fd8f281b5af10033a02f81b342600a3687f65854061e5dbc40b7566684a7e2ce1c22774848ed9f4248cb561cab8e820ac6828392fbac227bc3019eeac0 (o.val*12+t.val)
def heightDigit (o:IntroIndex) (t:Trial) :ℕ :=
 digit 18 0x3d1c1827086f830fb1454244549127245984b5be434690d0a431f03a601703082ac2f6413a8244679129245994c2ea434d90d2a43240378415740685425f80fa5a4494913c6320f37e76436290d6e433507b044e1820ab4c01c512de434f90e1e44129146a42db90b5a42ca0baf876da3212927a47d8e2432790d4643bd9122e42ca90b1a42bc044301b9b074bc29ce115ba4440913860a7630f3e434590cd6431f038b4164a079182b7711fde447f9136e45f83c81e435c90d5a4330047d01df20a1ec3acb1882a440d9123a45b0439ba433090c96430e041f81b7f0b6b042271b93a442f911ea456156f82433c90ce6431704dc021f70b72c42861bb5e4418912c245ea3b02a433990cb24316057c42c13123346a632cbee44109117a453d5ea0e432f90cae430d0457021520dfe8511221f22449a9126645bd49366436c90dba433d044581dbe0c68447d61e16244ff91376458e453d643bf90f42437d065a83f8f1a8009ba941a7644419110a454031a6e43e1910a644fd (o.val*12+t.val)
def d (o:IntroIndex) (t:Trial) :ℚ:=degreeDigit o t
def a (o:IntroIndex) (t:Trial) :ℚ:=max (graphRate 55) (d o t)
def b (o:IntroIndex) (t:Trial) :ℚ:=(heightDigit o t:ℚ)/32
def bbD {n m:ℕ} (w:Fin n→Fin m→ℚ) (s :Fin n) (k :Fin m) :ℚ :=
 ∑ i:Fin n,if i≤ s then w i k else 0
end
end qJeTDGe
end
section
namespace qJeTDGe
noncomputable section
open Finset qehP9ee

open scoped BigOperators
private theorem tail_swap {n:ℕ} (w x :Fin n→ℚ) :
   (∑ j,(∑ i,if i≤j then w i else 0)*x j) =
     ∑ i,w i*(∑ j,if i≤j then x j else 0) := by
 simp only [sum_mul,mul_sum]
 rw [sum_comm]
 apply sum_congr rfl
 intro i _
 apply sum_congr rfl
 intro j _
 split <;> simp_all
theorem c44 {α:Type*} {n m:ℕ} (S:Finset α)
  (w:Fin n→Fin m→ℚ) (x :α→Fin n→Fin m→ℚ) (h:Fin n→Fin m→ℚ)
  (hw : ∀ i k,0≤w i k)
  (hx : ∀ i k,(∑ f∈S,∑ j,if i≤j then x f j k else 0)≤h i k) :
  (∑ f∈S,∑ j,∑ k,bbD w j k*x f j k) ≤ ∑ i,∑ k,w i k*h i k := by
 calc
  _ = ∑ j,∑ k,bbD w j k*(∑ f∈S,x f j k) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    rw [sum_comm]
    simp only [mul_sum]
  _ = ∑ k,∑ i,w i k*(∑ j,if i≤j then ∑ f∈S,x f j k else 0) := by
    rw [sum_comm]
    exact sum_congr rfl fun k _=>tail_swap (fun i=>w i k) _
  _≤_:= by
    rw [sum_comm]
    refine sum_le_sum fun i _=>sum_le_sum fun k _=>mul_le_mul_of_nonneg_left ?_ (hw i k)
    convert hx i k using 1
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    by_cases hij:i≤j <;> simp [hij]
end
end qJeTDGe
end
namespace qJeTDGe
noncomputable section
open Finset qehP9ee
open P5_7_1 (IntroIndex)


open scoped Classical BigOperators
end
end qJeTDGe
end
namespace qJeTDGe
noncomputable section
open qehP9ee

end
end qJeTDGe
end
end
