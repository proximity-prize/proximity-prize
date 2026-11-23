import ProximityPrize.SubmissionLower.Z3ozsyb
set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 3000
set_option maxHeartbeats 1200000
namespace qcuQADa
open P6_7 (RectTail)
open P6_7_2 (jJ Bs seedCap)
open qXdgDRd (gap width Witness jX Guards)
open P5_7 (NativeWitness)
private def witnessCode :ℕ :=
  0x8a4b0894a487c9886c8c854808447482c6881c5c804507ec447eb847d37a7c3707ab6679b5c7835276b4875b3e743347332a71b2070b166f30c6db026caf86b2ee6a2e468ada672d0662c664abc63ab2622a86129e5fa945e28a5d2805ba765aa6c5926257a5856a4e561d0551c8539c0521b8511b04f9a84e1a04d1984b9904a188491804797846170451684396042958411503f9483e9403d1383b9303a92839120379183691035108348c0330ba320b4308ae2f0a82d8a22c89c2b096298902808a268842587e24078228722185a200551e8501d84b1c0461a8411903c1802c1682815024138201201c110120f80f0e00c0d0060c00400000
private def witness (b:RectTail) (e :ℕ) :NativeWitness :=
  let code :=witnessCode >>> (20*(e-1))
  let g:=code % 2048
  let c:=(code >>> 11) % 512
  let B:=width (degree b)
  let E :=e+g
  let m:=(g+1)*c
  let j:=m/(c+1)
  let W:=max (e*B) (max ((c+1)*(B*E*(E+1)/2+B*j*(j+1)/2)/m-j*B) ((E-j)*B))
  ⟨g,c,j,W⟩
private def rate (b:RectTail) (e :ℕ) :ℕ :=
  if e=0 then gap (degree b) else jX (degree b) e (witness b e)
private def Check (b:RectTail) (i:ℕ) :Prop :=
  if h:i<(Bs b).ordinateCap then
    rate b i≤ rate b (i+1)∧(i+1=1∨Witness (degree b) (i+1) (witness b (i+1))) ∧
      Ya b (i+1) (seedCap (⟨i,h⟩:jJ b)) (rate b (i+1))
  else True
private instance (b:RectTail) (i:ℕ) :Decidable (Check b i) := by
  unfold Check Witness
  infer_instance
private abbrev LR (e :ℕ) :Prop :=
  Check .pruned e∧Check .tailOne e∧Check .tailTwo e∧Check .tailThree e
private inductive dG:ℕ→ℕ→Prop
  | nil (e :ℕ) :dG e 0
  | cons {e n:ℕ} (head:LR e) (tail:dG (e+1) n) :dG e (n+1)
private theorem dG.get {e n:ℕ} (rows :dG e n) {l:ℕ} (ha :e≤l) (hb:l<e+n) :
    LR l:= by
  induction rows with
  | nil e=>omega
  | @cons e n h t ih =>
    by_cases he :l=e
    · exact he.symm ▸ h
    · exact ih (by omega) (by omega)
set_option quotPrecheck false in
local notation "r!" "[" idx "]" t=>dG.cons (e :=idx) (by decide) t
private theorem b80:dG 80 20 :=
  r![80] r![81] r![82] r![83] r![84]
  r![85] r![86] r![87] r![88] r![89]
  r![90] r![91] r![92] r![93] r![94]
  r![95] r![96] r![97] r![98] r![99]
  dG.nil 100
private theorem b60:dG 60 40 :=
  r![60] r![61] r![62] r![63] r![64]
  r![65] r![66] r![67] r![68] r![69]
  r![70] r![71] r![72] r![73] r![74]
  r![75] r![76] r![77] r![78] r![79]
  b80
private theorem b40:dG 40 60 :=
  r![40] r![41] r![42] r![43] r![44]
  r![45] r![46] r![47] r![48] r![49]
  r![50] r![51] r![52] r![53] r![54]
  r![55] r![56] r![57] r![58] r![59]
  b60
private theorem b20:dG 20 80 :=
  r![20] r![21] r![22] r![23] r![24]
  r![25] r![26] r![27] r![28] r![29]
  r![30] r![31] r![32] r![33] r![34]
  r![35] r![36] r![37] r![38] r![39]
  b40
private theorem b0:dG 0 100 :=
  r![0] r![1] r![2] r![3] r![4]
  r![5] r![6] r![7] r![8] r![9]
  r![10] r![11] r![12] r![13] r![14]
  r![15] r![16] r![17] r![18] r![19]
  b20
private theorem checked (b:RectTail) (i:ℕ) (hi:i<(Bs b).ordinateCap) :
    rate b i≤ rate b (i+1)∧(i+1=1∨Witness (degree b) (i+1) (witness b (i+1))) ∧
      Ya b (i+1) (seedCap (⟨i,hi⟩:jJ b)) (rate b (i+1)) := by
  have cap_le (b:RectTail) : (Bs b).ordinateCap≤100:= by cases b <;> decide
  have h:=b0.get (l:=i) (Nat.zero_le _) (hi.trans_le (cap_le b))
  have hc:Check b i:= by
    cases b
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  simpa only [Check,dite_eq_left hi] using hc
private theorem increases (b:RectTail) {l e :ℕ} (hl:l≤e)
    (he :e≤(Bs b).ordinateCap) :rate b l≤ rate b e := by
  induction e with
  | zero=>simpa only [Nat.eq_zero_of_le_zero hl] using Nat.le_refl (rate b 0)
  | succ e ih =>
    by_cases h:l≤e
    · have hp:=ih h (Nat.le_of_succ_le he)
      exact hp.trans (checked b e he).1
    · rw [show l=e+1 by omega]
theorem grade_certificate {b:RectTail} (i:jJ b) :
    ∃ r,Guards (degree b) (i.val+1) r∧Ya b (i.val+1) (seedCap i) r := by
  have hi:i.val+1≤(Bs b).ordinateCap:=i.isLt
  have hr :=checked b i.val i.isLt
  have hfirst:gap (degree b)≤ rate b (i.val+1) :=increases b (Nat.zero_le _) hi
  refine ⟨rate b (i.val+1),⟨hfirst,?_⟩,?_⟩
  · intro l hl hle
    cases l with
    | zero=>omega
    | succ j =>
      refine ⟨witness b (j+1),(checked b j (hle.trans hi)).2.1,?_⟩
      have hv :=increases b hle hi
      simpa only [rate,ite_eq_right (Nat.succ_ne_zero j)] using hv
  · exact hr.2.2
end qcuQADa
