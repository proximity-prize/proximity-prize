import ProximityPrize.SubmissionLower.ZjlUeKe
import ProximityPrize.SubmissionLower.ZnTmQ9b
import ProximityPrize.SubmissionLower.ZJBzH3c
import ProximityPrize.SubmissionLower.Z9971Pd
import ProximityPrize.SubmissionLower.ZmJja2a
import ProximityPrize.SubmissionLower.Zc6ZBRc
set_option Elab.async false
section
set_option autoImplicit true
namespace q3puXVa
theorem proof :qkBU02c.c1 :=
  qziIa4d.of_children qOj34lc.proof qJ69aaa.proof
    (qnyP9Da.of_children q3zqDZc.proof qJQ0Sxd.proof
      qDhaEec.proof) qU1uHGd.proof
end q3puXVa
end
section
set_option autoImplicit true
namespace qVqCanc
theorem proof :qTplN5b.c3 :=
  q3puXVa.proof
end qVqCanc
end
section
set_option autoImplicit true
namespace qpVOZ2b
open P6 (p)
open P6_7 (RectTail)
open P6_7_2_3
open qVWQWJa
set_option maxRecDepth 6000
private def projectionCode :RectTail→ℕ
  | .pruned=>0x85a48e0f38a5b7e83ed25f165936fb2cff91643ae25e89954e4b168cae120f8a6fb996aa48c92d38ec2d22e047c2dfb2baa8b441152b3fc9a2bc59f3ba28c52d3d7f8c15e2893d7a472b4f1e99787d2c7ddd90a94011a6c210987751d284fb28f24652dce45d07c6a0ad7d1bb4394fd425e4a56f0e7b7e3a5334c226c2ab214199bf5e9196a1f3cb8
  | .tailOne=>0x92a3467310b8ea1ab1929c2343aa538c43a14b4bf5f20e5daff23c1ba613ca1682099938f3fdbc3e5b17430c4fd00e2da6e933a3be1b9d5b25e13af397a152aecb1d950425e65d0511b050324904899b66d2ecbcb12c486a4277289d1acd25d52846ecddc212c8a73704e11e70707d0e2a3126dec381a4633442caea55847160e1b0b749c55ed2950
  | .tailTwo=>0x881a24a494ade282846a6c87719ffb54b5c6bb7b18f9249e2ef57cd96552549a3dc117a28f684e39bc9e90da4abc41f2c6b1aa39f44362a50a048a2a59a736ade14b71866321dee80dad5346e4877f961252dcb0ab16d27a175558d39a9fa342edf66956449bc81b7423919c35bbed3b27770aef6a74508b4a32b57be58df5471cb3f349a9386805d
  | .tailThree=>0x78705c625895055bb952171ede39b2c36b535b29a19268d98c80728cf3902437662e141cf9835232c2de33f83f7640d13a6488f69fe2ea156c9dc8c9254ee94b8b6ed1cb1ef655bba6269fdb65926d97d2acfc91d792f959db7f223ae24231435a25ae8bab7b06f538bcdb181ec536432066697b705ce1fb5a3889fb63b7f91f6744a60168daf762a
private def witnessCode :RectTail→ℕ
  | .pruned=>0x2aab61c6b7288346bda4265bf5b39b243162aa8c22073fa1791fdb1797741dadf68e621b7f09845c194f127b4b171bc9714414e787673c12afb55e2e10737d54270e33a14a200bee79401809a050370f0743d12d0a
  | .tailOne=>0x2aac48c6b72883f6bda5265c50b491243212aa8d2207f7a1791fdbc297751dae968e621b7f9d845c194f9a7b4b171c46714414e7f8673c12b0195e2e10734954280e33e94a210beeb9401809a084370f0743f82d0a
  | .tailTwo=>0x2aacdac6b7288481bda5265cd3b49124328eaa8d2207fda17a1fdc2f97751daefc8e621b7ff8845d194ff17b4b171c4c714514e83f673c12af5b5e2f10738254280e34194a210beee2401809a0a5370f0744112d0a
  | .tailThree=>0x2aad6dc6b72884eabda6265ceab492243302aa8e220872a17a1fdc9d97751daeeb8e631b8056845d1950487b4b171c9b714514e887673c12af9c5e2f1073ba54280e344a4a210bef0b401809a0c6370f07442a2d0a
private abbrev axisNum (b:RectTail) (o:Origin) :=
  (projectionCode b >>> (78*o.val)) % 2^39
private abbrev planeNum (b:RectTail) (o:Origin) :=
  (projectionCode b >>> (78*o.val+39)) % 2^39
private abbrev wit (b:RectTail) (g:ℕ) :=
  witnessCode b >>> (40*(g-3))
private abbrev extra (b:RectTail) (g:ℕ) :=wit b g % 256
private abbrev coeff (b:RectTail) (g:ℕ) :=(wit b g >>> 8) % 256
private abbrev width (b:RectTail) (g:ℕ) :=(wit b g >>> 16) % 2^24
private abbrev modulus (b:RectTail) (g:ℕ) :=
  width b g+1+((extra b g+1)*coeff b g/(coeff b g+1))*degree b
private theorem witness (b:RectTail) (i:Fin 17) :
    NativeOK (degree b) (i.val+3) (extra b (i.val+3)) (coeff b (i.val+3))
      (width b (i.val+3)) (modulus b (i.val+3)) := by
  unfold NativeOK
  cases b <;> fin_cases i <;> decide
private theorem projections (b:RectTail) (o:Origin) :
    terminalProjection b o 1=(axisNum b o:ℚ)/1275 ∧
    min (terminalProjection b o 2) (2*terminalProjection b o 1)=(planeNum b o:ℚ)/1275:= by
  simp only [terminalProjection,projectionBound,TD.FP,
    Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  cases b <;> fin_cases o <;> exact ⟨by with_unfolding_all rfl,by with_unfolding_all rfl⟩
private def PN (b:RectTail) (d z a h g:ℕ) :Bool :=
  if p≤a*g then true
  else if z=2 then decide (GF a h g (persistNum (degree b) g) (oldAgreement*gap (degree b)) 0 1)
  else if g=1 then decide (GF a h g (gap (degree b)+3*262144) (gap (degree b)) 0 1)
  else if g=2 then decide (16≤ min z a ∧
    GF a h g (13*gap (degree b)+8*262144) (gap (degree b)) 16 1)
  else decide (thresholdNum d g≤ min z a*thresholdDen g ∧
    GF a h g (heightNum (degree b) g (extra b g) (coeff b g) (width b g)) (gap (degree b))
      (thresholdNum d g) (thresholdDen g))
private def checks (b:RectTail) (d z a h:ℕ) :ℕ→Bool
  | 0=>true
  | k+1=>checks b d z a h k && PN b d z a h (k+1)
private theorem get_cell {b d z a h k g} (hg:0<g) (hle :g≤k)
    (hc:checks b d z a h k=true) :PN b d z a h g=true := by
  induction k with
  | zero=>omega
  | succ k ih =>
    simp only [checks,Bool.and_eq_true] at hc
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact hc.2
    · exact ih (Nat.le_of_lt_succ hlt) hc.1
private abbrev Header (x d z a :ℕ) :Prop :=
  d<p*1275∧0<a∧2*x≤a*1275∧a<p∧2≤z∧p≤a*20
set_option exponentiation.threshold 128 in
private theorem checked (b:RectTail) (o:Origin) :
    Header (axisNum b o) (planeNum b o) (terminalZNT b o) (terminalSeedN b o) ∧
      checks b (planeNum b o) (terminalZNT b o) (terminalSeedN b o) (terminalHeightN b o) 19=true := by
  cases b <;> fin_cases o <;> exact ⟨by decide,by decide⟩
private theorem terminal {b:RectTail} {o:Origin} {x d z a h:ℕ}
    (hx :terminalProjection b o 1=(x :ℚ)/1275)
    (hd:min (terminalProjection b o 2) (2*terminalProjection b o 1)=(d:ℚ)/1275)
    (H :Header x d z a) (hc:checks b d z a h 19=true) :
    TerminalOK b o z a h:= by
  rcases H with ⟨hdp,ha,ha2,hap,hz,hcut⟩
  have hk :0<gap (degree b) := by cases b <;> decide
  unfold TerminalOK
  dsimp only
  rw [hd,hx]
  refine ⟨by positivity,?_,by exact_mod_cast ha,?_,by exact_mod_cast hap,
    by exact_mod_cast hz,Nat.cast_nonneg _,?_⟩
  · exact (div_lt_iff₀ (by norm_num)).2 (by exact_mod_cast hdp)
  · rw [← mul_div_assoc]
    exact (div_le_iff₀ (by norm_num)).2 (by exact_mod_cast ha2)
  intro g hg hq
  have hgq: (0:ℚ)<g:= by exact_mod_cast hg
  have hpg:a*g<p:= by exact_mod_cast (lt_div_iff₀ hgq).mp hq
  have h19:g≤19:= by
    by_contra! h
    exact (not_lt_of_ge (hcut.trans (Nat.mul_le_mul_left a h))) hpg
  have hcell:=get_cell hg h19 hc
  rw [PN,ite_eq_right (not_le.mpr hpg)] at hcell
  by_cases hZ:z=2
  · rw [ite_eq_left hZ] at hcell
    exact persistent hg hk hq (of_decide_eq_true hcell)
  rw [ite_eq_right hZ] at hcell
  by_cases h1 :g=1
  · subst g
    rw [ite_eq_left rfl] at hcell
    exact linear hk hq (of_decide_eq_true hcell)
  rw [ite_eq_right h1] at hcell
  by_cases h2 :g=2
  · subst g
    rw [ite_eq_left rfl] at hcell
    obtain ⟨hmin,hfee⟩:=of_decide_eq_true hcell
    exact quadratic hk hq hmin hfee
  rw [ite_eq_right h2] at hcell
  have h3:3≤g:= by omega
  let i:Fin 17:=⟨g-3,by omega⟩
  have hi:i.val+3=g:=Nat.sub_add_cancel h3
  obtain ⟨hmin,hfee⟩:=of_decide_eq_true hcell
  exact native h3 hk hq (by simpa only [hi] using witness b i) hmin hfee
theorem proof :qVWQWJa.c2 := fun b o =>
  terminal (projections b o).1 (projections b o).2 (checked b o).1 (checked b o).2
end qpVOZ2b
end
section
set_option autoImplicit true
namespace qwx47gd
theorem proof :qxtWb5a.c3 :=
  qziIa4d.of_children qOj34lc.proof qJ69aaa.proof
    (qnyP9Da.of_children q3zqDZc.proof qJQ0Sxd.proof
      qDhaEec.proof) qU1uHGd.proof
end qwx47gd
end
section
set_option autoImplicit true
namespace qwRB2oc
noncomputable section
open Finset
open P6_7_2_3 (marks)
open q6hAhQd (DescendedMarks)
open YY (Si a9E)
open private cag from ProximityPrize.SubmissionLower.G
def c1 :Prop :=qxtWb5a.c1
def c2 :Prop :=qxtWb5a.c2
def c3:Prop :=qxtWb5a.c3
def c4 :Prop :=qxtWb5a.c4
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :qu56FMb.c8:= by
  classical
  intro b x I C g A hp hg e c W M hok
  have hT:DescendedMarks x (marks x I) (Si I) C g (a9E I) :=
    ⟨filter_subset _ _,A.root,A.irreducible,A.projection,A.plane_pos,hp,
      fun _ hγ=>cag (mem_filter.mp hγ).2⟩
  have h:=qxtWb5a.of_children h1 h2 h3 h4 hT hg e c W M hok
  simpa only [mul_comm (g:ℚ) (C.totalDegree :ℚ)] using h
end
end qwRB2oc
end
