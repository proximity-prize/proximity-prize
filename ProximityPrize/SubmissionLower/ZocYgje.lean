import ProximityPrize.SubmissionLower.ZYvV56c
import ProximityPrize.SubmissionLower.ZJHC8Rc
import ProximityPrize.SubmissionLower.ZG1muKa
import ProximityPrize.SubmissionLower.ZLcmX9d
import ProximityPrize.SubmissionLower.ZnhmZEa
import ProximityPrize.SubmissionLower.ZyePCwc
import ProximityPrize.SubmissionLower.Z66HSdc
import ProximityPrize.SubmissionLower.Z36nWNc
set_option Elab.async false
open _root_ renaming Ideal → znc, Ideal.subset_span → zCn, Int.natCast_nonneg → zbO, MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one → zdH, Nat.cast_nonneg → zqJ, Nat.mul_le_mul_left → zBI
section
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 800000
namespace qMiJnMd
noncomputable section
open Finset P6_6 P6_6_7 q8NBBre
open P6 (K)
open aR (af Shape shape aO cK extend wU iH)
open dN (GeoJets bC separant Ch kC AX
  YR Invariant oA j8 An)
open BO (Ue bfW bsq Uy bhO pN)
open agL (BV bft a4A a4B)
open akM (a1n bc7 bhQ)
open GJ (vE Ux bf6 bZi)
open aKp (bDo)
open vS (JV bTT)
open Dr
open wH (qg)
open lB (bF Tn amo abr)
open P6_6_7_3 (cDD agr local_weight order_mem an0 curveCharge)
open q8kxiJa (local_order_le)
open qbRvrcc (d40)
open private active_spec choose_cuts first_order from ProximityPrize.SubmissionLower.ZwiFoca
open private branch_valid from ProximityPrize.SubmissionLower.ZJHC8Rc
open private bnH bnG chartChamber degree_nonneg from ProximityPrize.SubmissionLower.ZPedZjc
open private eMr blq from ProximityPrize.SubmissionLower.E4
open private bhj from ProximityPrize.SubmissionLower.CH
open private bwp from ProximityPrize.SubmissionLower.T
open private combine from ProximityPrize.SubmissionLower.ZIrsLvc
open private bYX bYY taylor_simplex uq from ProximityPrize.SubmissionLower.Z66HSdc
open private c5M cAI b4b BP cTh from ProximityPrize.SubmissionLower.B5
private theorem pair_mixed32 {C:Context} {R:af 4} (h:Input C R)
    {S:Finset (znc GeoJets)} {b1 b2 :Shape} (hb1 :ChamberBox b1) (hb2 :ChamberBox b2)
    (hS : ∀ z∈S,(kC R (an1 C)).IsMinimalPrime z) :
    32*(∑ z∈S,(AN (kC R (an1 C)) z :ℚ)*tW z [b1,b2]) ≤
      (wP (cap R) (remainingChart C.v) b1 b2 :ℚ) := by
  have hp:=aM8 h
  have h1 :=(pair_chain h hb1 hb2 hS).trans (blq aiK.proof (first_chamber h) hp hb1 hb2)
  have he : (iH (cap R) (remainingChart C.v) b1 b2 :ℚ) =
      (wP (cap R) (remainingChart C.v) b1 b2 :ℚ) := by
    exact_mod_cast bhj (cap R) (remainingChart C.v) b1 b2 ⟨hp.1,hp.2.1⟩ ⟨hb1.1,hb1.2.1⟩ ⟨hb2.1,hb2.2.1⟩
  rw [← he,mul_comm]; exact (le_div_iff₀ (by norm_num : (0:ℚ)<32)).mp h1
private theorem point_count {C:Context} {T:znc GeoJets} {M:Finset K} {D:af 4}
    {a :Shape} (ha :ChamberBox a) (hD:aO (shape D) a)
    (hT:T.IsPrime) (hd:dimension T=1) (hproper :bC D∉T)
    (hM:M⊆C.Δ) (hon : ∀ γ∈M,T≤Ch (extend (C.s γ)))
    (n:K→ℕ) (horder : ∀ γ∈M,wU D (extend (C.s γ)) (n γ)) :
    (∑ γ∈M,(n γ:ℚ))≤tW T [a] := by
  classical
  let J:=AX T D; let N :=M.filter fun γ=>0<n γ
  let P (γ:K) :=oF (JV (extend (C.s γ)))
  have hreg:=aPQ hT hproper
  have hJ:dimension J=0:=Nat.eq_zero_of_le_zero (by
    simpa only [J,AX,hd,Nat.sub_self] using aCR hreg)
  have hmin (γ) (hγ:γ∈N) :J.IsMinimalPrime (P γ) := by
    obtain ⟨hm,hj⟩:=mem_filter.mp hγ
    exact eMr hJ _ (sup_le (hon γ hm)
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ue.mpr (bfW hj (horder γ hm)))))
  have hinj:Set.InjOn P (N :Set K) := fun γ hγ δ hδ he =>
    C.messages.distinct (hM (filter_subset _ _ hγ)) (hM (filter_subset _ _ hδ))
      (Polynomial.map_injective aR.embed aR.embed.injective (bTT (btI he)))
  calc _ = ∑ γ∈N,(n γ:ℚ) := by
        simp only [N,sum_filter]
        exact sum_congr rfl fun γ _=> by
          by_cases hn:0<n γ
          · simp [hn]
          · simp [Nat.eq_zero_of_not_pos hn]
    _ ≤ ∑ γ∈N,(AN J (P γ) :ℚ)*tW (P γ) [] :=sum_le_sum fun γ hγ=> by
        have hm:=filter_subset _ _ hγ
        have hlt:T<P γ:=lt_of_le_of_ne (hon γ hm) fun he=> by
          rw [he,eMn] at hd; exact Nat.zero_ne_one hd
        rw [bge,mul_one]; let _:=(hmin γ hγ).isPrime
        exact_mod_cast qmQUdWa.evJ hT hlt (hmin γ hγ)
          (bRn.gK5 (bC D) (P γ) (n γ) fun b hb=> by
            change BV b (MvPolynomial.map j8 D)∈Ch (extend (C.s γ))
            rw [← bft]; exact Ue.mpr (a4A hb (horder γ hm)))
    _ = ∑ U∈N.image P,(AN J U:ℚ)*tW U [] :=
        (sum_image (f := fun U=>(AN J U:ℚ)*tW U [])
          (fun _ hγ _ hδ he=>hinj hγ hδ he)).symm
    _≤tW J [] :=bnG J [] (by simp) (by simp [hJ]) _ (fun U hU=> by
        obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hU; exact hmin γ hγ)
    _≤tW T [a] :=bnH T a [] ha (by simp) (by simp [hd]) _ (bHn hD) hreg
theorem excess_bound {C:Context} {R:af 4} (hi:Input C R) (A:Charts C R) :
    let a :=cap R; let p:=remainingChart C.v
    (feeScale :ℤ)*DG A≤ curve32 a a p a+point32 a p a := by
  classical
  intro a p
  let M:=C.Δ.filter (xN C R)
  have hsum0:DG A = ∑ γ∈M,(ord C R γ - genericOrder R (A.aI γ)) := by
    simp only [M,sum_filter,DG]
  rw [hsum0]
  by_cases hn:M.Nonempty
  · let D:Context :=
      { C with
        Δ:=M
        nonempty :=hn
        messages :=C.messages.mono (filter_subset _ _)
        marks :=⟨C.marks.factors,C.marks.different,fun γ hγ=>C.marks.Eh γ (filter_subset _ _ hγ),
          fun γ hγ=>C.marks.leading γ (filter_subset _ _ hγ)⟩ }
    have hi' : Input D R := { hi with order := fun γ hγ=>hi.order γ (filter_subset _ _ hγ) }
    let B:SurfaceAssignment D R (an1 D) :=⟨A.aI,fun γ hγ _=> by
      obtain ⟨hm,ha⟩:=mem_filter.mp (show γ∈M from hγ)
      exact ⟨(A.valid γ hm ha).1,(A.valid γ hm ha).2.1⟩⟩
    have hf : ∀ γ∈D.Δ,thirdFiber R (extend (D.s γ))≠0:= fun γ hγ=>(mem_filter.mp hγ).2.2
    obtain ⟨F⟩:=choose_cuts B hi'.factor.1.ne_zero
    let w:=weightedChart bf a
    have hsum: (∑ br∈F.branches,∑ γ∈F.marks br,(excessAt B γ:ℚ)) =
        (P6_6_7.DG D R (an1 D) B:ℚ) := by
      unfold Cuts.branches Cuts.marks
      rw [sum_fiberwise_of_maps_to (fun γ hγ=>mem_image_of_mem F.tag hγ) (fun γ=>(excessAt B γ:ℚ))]
      change (∑ γ∈D.Δ.filter (fun γ=>0<excessAt B γ),(excessAt B γ:ℚ))=(↑(∑ γ∈D.Δ,excessAt B γ) :ℚ)
      rw [sum_filter,Nat.cast_sum]
      exact sum_congr rfl fun γ _=> by by_cases h:0<excessAt B γ <;> simp [h,Nat.eq_zero_of_not_pos]
    have hbranch (br :Branch) (hbr :br∈F.branches) :
        (mV:ℚ)*(∑ γ∈F.marks br,(excessAt B γ:ℚ)) ≤
          (P6.t:ℚ)*((F.order br :ℚ)*tW br.2 [w]) +
          3*(mV:ℚ)*((F.order br :ℚ)*tW br.2 [a]) := by
      obtain ⟨hz,hU,hT⟩:=branch_valid F hbr; let _:=hz.isPrime
      have hzdim:=aQG (agr hi'.factor.1.ne_zero)
        (amo R (an1 D) hi'.factor.1 hi'.proper) hz
      have hd:dimension br.2=1 := by
        have hd:=zdH hU hT
        change dimension br.2+1=dimension br.1 at hd; omega
      have hRT:bC R∈br.2 :=hT.le (Ideal.mem_sup_left (hz.le (zCn (by simp))))
      have hUt:bC (F.polynomial br)∈br.2 :=hT.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      have hne :F.polynomial br≠0:= fun h=>hU (by simp [h,bC])
      have he :1≤F.order br :=generic_positive hT.isPrime hne hUt
      have hMd:F.marks br⊆D.Δ:= fun _ hγ=>(active_spec (mem_filter.mp hγ).1).1
      have hneM: (F.marks br).Nonempty := by
        obtain ⟨γ,hγ,htag⟩:=mem_image.mp hbr; exact ⟨γ,mem_filter.mpr ⟨hγ,htag⟩⟩
      have hmark (γ) (hγ:γ∈F.marks br) :br.2≤Ch (extend (D.s γ)) := by
        obtain ⟨hm,heq⟩:=mem_filter.mp hγ; rw [← heq]; exact (F.valid γ hm).2.2.2
      have hcurve :=dRZ hi' hT.isPrime hd hMd hneM hRT hmark (fun γ hγ=>hf γ (hMd hγ))
      obtain ⟨j,hj,hproper⟩:=cSn (F.polynomial br) br.2 hT.isPrime hne
      have hpoint :=point_count (first_chamber hi') (a4B j (a4B (F.first br.1) (first_box R)))
        hT.isPrime hd hproper hMd hmark (F.a4Q br) (fun γ hγ=> by
          obtain ⟨hm,heq⟩:=mem_filter.mp hγ
          have h1 :wU (F.polynomial br) (extend (D.s γ)) (excessAt B γ) := by
            rw [← heq]; exact first_order (active_spec hm).2.1 _ (F.valid γ hm).1
          simpa only [Cuts.a4Q,Cuts.order,Cuts.polynomial,hj] using cUA _ _ j _ h1)
      let e :ℚ:=F.order br; let J:ℚ := ∑ γ∈F.marks br,(F.a4Q br γ:ℚ)
      have he' : (1 :ℚ)≤e := by dsimp only [e]; exact_mod_cast he
      have hJ:J≤e*tW br.2 [a] :=
        (le_mul_of_one_le_left (sum_nonneg fun _ _=>zqJ _) he').trans
          (mul_le_mul_of_nonneg_left hpoint (zqJ _))
      have hsp: (∑ γ∈F.marks br,(excessAt B γ:ℚ))≤e*(F.marks br).card+J:= by
        calc _ ≤ ∑ γ∈F.marks br,(e+(F.a4Q br γ:ℚ)) :=sum_le_sum fun γ _=> by
              dsimp only [e]
              exact_mod_cast (show excessAt B γ≤F.order br+F.a4Q br γ by unfold Cuts.a4Q; omega)
          _ = _:= by rw [sum_add_distrib,sum_const,nsmul_eq_mul,mul_comm ((F.marks br).card:ℚ)]
      have hg: (0:ℚ)≤ mV:=zqJ _
      have h1 :=mul_le_mul_of_nonneg_left hsp hg
      have h2 :=mul_le_mul_of_nonneg_left hcurve (zqJ (F.order br))
      have h3:=mul_le_mul_of_nonneg_left hJ hg
      nlinarith only [h1,h2,h3]
    have hbudget: (mV:ℚ)*(P6_6_7.DG D R (an1 D) B:ℚ) ≤
        (P6.t:ℚ)*F.degree w+3*(mV:ℚ)*F.degree a := by
      rw [← hsum,mul_sum]; unfold Cuts.degree; simp only [mul_sum,← sum_add_distrib]
      exact sum_le_sum fun br hbr=> by simpa only [mul_sum] using hbranch br hbr
    have hdeg (s :Shape) (hs :ChamberBox s) :32*F.degree s≤(wP a p a s :ℚ) := by
      let S:=F.branches.image Prod.fst; let J:=kC R (an1 D)
      have hfib (z) (hz :z∈S) :J.IsMinimalPrime z ∧
          (∑ br∈F.branches.filter (fun br=>br.1=z),(F.order br :ℚ)*tW br.2 [s]) ≤
            (AN J z :ℚ)*tW z [a,s] := by
        let U:=BV (F.first z) R; let H :=AX z U
        obtain ⟨ref,href,heq⟩:=mem_image.mp hz; obtain ⟨hZ,hU,_⟩:=branch_valid F href
        have hbase :J.IsMinimalPrime z :=heq ▸ hZ
        have hu:bC U∉z := by simpa only [U,Cuts.polynomial,heq] using hU
        have hd:=aQG (agr hi'.factor.1.ne_zero)
          (amo R (an1 D) hi'.factor.1 hi'.proper) hbase
        have hreg:=aPQ hbase.isPrime hu
        have hdim:dimension H≤1 := by simpa only [H,AX,hd] using aCR hreg
        let V:=F.branches.filter (fun br=>br.1=z)
        have hb (br :Branch) (hbr :br∈V) :H.IsMinimalPrime br.2 := by
          obtain ⟨h1,h2⟩:=mem_filter.mp hbr; simpa only [H,U,Cuts.polynomial,h2] using (branch_valid F h1).2.2
        have hboxes : ∀ q∈[a,s],ChamberBox q:= by simp [first_chamber hi',hs,a]
        have hn0:0≤tW z [a,s] := by
          simpa only [sum_empty] using bnG z [a,s] hboxes (by simp [hd]) ∅ (by simp)
        refine ⟨hbase,?_⟩
        calc (∑ br∈V,(F.order br :ℚ)*tW br.2 [s])
              ≤ ∑ br∈V,(AN H br.2 :ℚ)*tW br.2 [s] :=sum_le_sum fun br hbr=> by
                have hb' := hb br hbr
                have hd' := (MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le hb'.le).trans hdim
                have hn' : 0≤tW br.2 [s] := by
                  simpa only [sum_empty] using bnG br.2 [s] (by simpa using hs) (by simpa using hd') ∅ (by simp)
                exact mul_le_mul_of_nonneg_right (by
                  exact_mod_cast (show F.order br≤AN H br.2 by
                    simpa only [Cuts.order,Cuts.polynomial,(mem_filter.mp hbr).2,U] using
                      local_order_le hbase.isPrime hu hb')) hn'
          _ = ∑ T∈V.image Prod.snd,(AN H T:ℚ)*tW T [s] :=
              (sum_image (f := fun T=>(AN H T:ℚ)*tW T [s]) fun b1 h1 b2 h2 h12 =>
                Prod.ext ((mem_filter.mp h1).2.trans (mem_filter.mp h2).2.symm) h12).symm
          _≤tW H [s] :=bnG H [s] (by simpa using hs) (by simpa using hdim) _
              (fun T hT=> by obtain ⟨br,hbr,rfl⟩:=mem_image.mp hT; exact hb br hbr)
          _≤tW z [a,s] :=bnH z a [s] (first_chamber hi') (by simpa using hs)
              (by simp [hd]) _ (bHn (a4B _ (first_box R))) hreg
          _≤_:=le_mul_of_one_le_left hn0 (by exact_mod_cast Nat.succ_le_of_lt (aFq hbase))
      have hfdeg:F.degree s ≤ ∑ z∈S,(AN J z :ℚ)*tW z [a,s] := by
        unfold Cuts.degree
        rw [← sum_fiberwise_of_maps_to (fun _ hbr=>mem_image_of_mem Prod.fst hbr)]
        exact sum_le_sum fun z hz=>(hfib z hz).2
      exact (mul_le_mul_of_nonneg_left hfdeg (by norm_num)).trans
        (pair_mixed32 hi' (first_chamber hi') hs fun z hz=>(hfib z hz).1)
    have hm:=mul_le_mul_of_nonneg_left hbudget (by norm_num : (0:ℚ)≤32)
    have h1 :=mul_le_mul_of_nonneg_left (hdeg w (chartChamber (by decide))) (zqJ P6.t)
    have h2 :=mul_le_mul_of_nonneg_left (hdeg a (first_chamber hi'))
      (mul_nonneg (by norm_num : (0:ℚ)≤3) (zqJ mV))
    have heq :P6_6_7.DG D R (an1 D) B = ∑ γ∈M,(ord C R γ - genericOrder R (A.aI γ)) := by
      unfold P6_6_7.DG; refine sum_congr rfl fun γ hγ => ?_
      change ord C R γ-(if 0<ord C R γ then genericOrder R (A.aI γ) else 0)= _
      rw [ite_eq_left (mem_filter.mp hγ).2.1]
    rw [← heq]
    have hcast: (↑((feeScale :ℤ)*P6_6_7.DG D R (an1 D) B) :ℚ) ≤
        (↑(curve32 a a p a+point32 a p a) :ℚ) := by
      simp only [curve32,point32,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat,
        show (feeScale :ℚ)=32*(mV:ℚ) by simp [feeScale]]
      linear_combination hm+h1+h2
    exact_mod_cast hcast
  · rw [not_nonempty_iff_eq_empty.mp hn,sum_empty,Nat.cast_zero,mul_zero]
    have ha :=first_chamber hi; have hp:=aM8 hi
    have hw:=chartChamber (p:=a) (L:=bf) (by decide)
    have hc:=bwp a p a (weightedChart bf a) ⟨hp.1,hp.2.1⟩ ⟨ha.1,ha.2.1⟩ ⟨hw.1,hw.2.1⟩
    have hpt:=bwp a p a a ⟨hp.1,hp.2.1⟩ ⟨ha.1,ha.2.1⟩ ⟨ha.1,ha.2.1⟩
    change 0≤ curve32 a a p a+point32 a p a
    exact add_nonneg (add_nonneg (mul_nonneg (zbO _) hc)
      (mul_nonneg (mul_nonneg (by decide) (zbO _)) hpt)) (mul_nonneg (zbO _) hpt)
theorem dzP {C:Context} {R:af 4} (h:Input C R) (A:Charts C R) :
    let a :=cap R; let p:=remainingChart C.v
    (feeScale :ℤ)*weight A .boundary≤ curve32 a a p a := by
  classical
  intro a p
  let adP (z :znc GeoJets) :=separant ((separant^[A.index z]) R)
  let M:=C.Δ.filter fun γ=>xN C R γ∧stratum A γ = .boundary
  have spec (γ) (hγ:γ∈M) :=A.valid γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2.1
  have sel (γ) (hγ:γ∈M) :
      ∃ D,(AX (A.aI γ) (adP (A.aI γ))).IsMinimalPrime D ∧
        D ≤Ch (extend (C.s γ)) := by
    apply bsq (spec γ hγ).2.1; by_contra hn
    have hb:=(mem_filter.mp hγ).2.2
    have hn' : cK (separant (chartAt A γ)) (extend (C.s γ))≠0:=hn
    simp only [stratum,ite_eq_right hn'] at hb; split_ifs at hb
  let curve (γ) :znc GeoJets :=if hγ:γ∈M then (sel γ hγ).choose else ⊥
  have ch (γ) (hγ:γ∈M) :
      (AX (A.aI γ) (adP (A.aI γ))).IsMinimalPrime (curve γ) ∧
        curve γ≤Ch (extend (C.s γ)) := by
    simpa only [curve,dite_eq_left hγ] using (sel γ hγ).choose_spec
  let S:=M.image A.aI
  let N (z :znc GeoJets) :=M.filter (fun γ=>A.aI γ=z)
  let T (z :znc GeoJets) :=(N z).image curve
  let L (z D:znc GeoJets) :=(N z).filter (fun γ=>curve γ=D)
  have hs (z) (hz :z∈S) : (kC R (an1 C)).IsMinimalPrime z∧bC (adP z)∉z := by
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hz; exact ⟨(spec γ hγ).1,(spec γ hγ).2.2.2.2⟩
  have hT (z D) (hD:D∈T z) : (AX z (adP z)).IsMinimalPrime D:= by
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hD
    simpa only [(mem_filter.mp hγ).2] using (ch γ (mem_filter.mp hγ).1).1
  have hR:=agr h.factor.1.ne_zero
  have hrel :=amo R (an1 C) h.factor.1 h.proper
  have cdim {z D:znc GeoJets} (hz :z.IsPrime) (hd:dimension z=2) (hu:bC (adP z)∉z)
      (hD: (AX z (adP z)).IsMinimalPrime D) :dimension D =1 := by
    have :=hz
    have he :=zdH hu hD
    change dimension D + 1=dimension z at he; omega
  have ha :=first_chamber h; let q:=weightedChart bf a; have hq:ChamberBox q:=chartChamber (by decide)
  have hsum:weight A .boundary = ∑ z∈S,genericOrder R z * ∑ D∈T z,(L z D).card:= by
    calc _ = ∑ γ∈M,genericOrder R (A.aI γ) := by rw [weight,sum_filter]
      _ = ∑ z∈S,∑ γ∈N z,genericOrder R (A.aI γ) :=
          (sum_fiberwise_of_maps_to (fun γ hγ=>mem_image_of_mem A.aI hγ) _).symm
      _ = _:=sum_congr rfl fun z _=> by
          have hc : ∑ D∈T z,(L z D).card=(N z).card:= by
            simpa [T,L] using (sum_fiberwise_of_maps_to (fun γ hγ=>mem_image_of_mem curve hγ) (fun _=>(1 :ℕ)))
          rw [hc]; calc _ = ∑ γ∈N z,genericOrder R z :=sum_congr rfl fun γ hγ=> by rw [(mem_filter.mp hγ).2]
            _ = _:= by simp [Nat.mul_comm]
  let amt (s :Shape) := ∑ z∈S,(genericOrder R z :ℚ) * ∑ D∈T z,tW D [s]
  have hcount: (mV:ℚ)*weight A .boundary≤(P6.t:ℚ)*amt q+2*(mV:ℚ)*amt a := by
    rw [hsum]; push_cast; simp only [amt,← mul_assoc,mul_sum,← sum_add_distrib]
    refine sum_le_sum fun z hz=>sum_le_sum fun D hD => ?_
    obtain ⟨hz',hu⟩:=hs z hz; have hmin:=hT z D hD
    have hmem:bC R∈D:=(le_sup_left.trans hmin.le) (hz'.le (zCn (by simp)))
    obtain ⟨γ,hγ,he⟩:=mem_image.mp hD
    have pop:=dRZ h (M:=L z D) hmin.isPrime (cdim hz'.isPrime (aQG hR hrel hz') hu hmin)
      (fun γ hγ=>(mem_filter.mp (mem_filter.mp (mem_filter.mp hγ).1).1).1) ⟨γ,mem_filter.mpr ⟨hγ,he⟩⟩
      hmem (fun γ hγ=>(mem_filter.mp hγ).2 ▸ (ch γ (mem_filter.mp (mem_filter.mp hγ).1).1).2)
      (fun γ hγ=>(mem_filter.mp (mem_filter.mp (mem_filter.mp hγ).1).1).2.1.2)
    have hmul :=mul_le_mul_of_nonneg_left pop (zqJ (genericOrder R z))
    linarith only [hmul]
  have bnd (s :Shape) (hs' : ChamberBox s) :32*amt s≤(wP a p a s :ℚ) := by
    have h1 :amt s ≤ ∑ z∈S,(AN (kC R (an1 C)) z :ℚ)*tW z [a,s] :=
      sum_le_sum fun z hz=> by
        obtain ⟨hz',hu⟩:=hs z hz
        have hcut:aO (shape (adP z)) a := by
          simpa only [adP,Function.iterate_succ_apply' separant (A.index z) R] using
            bc7 R (A.index z).succ
        have hd:=aQG hR hrel hz'; have hr :=aPQ hz'.isPrime hu
        have hj:dimension (AX z (adP z))≤1 := by
          simpa only [AX,hd] using aCR hr
        have hn (D) (hD:D∈T z) :=degree_nonneg (cdim hz'.isPrime hd hu (hT z D hD)) hs'
        have hsdeg : ∑ D∈T z,tW D [s]≤tW z [a,s] := calc
          _ ≤ ∑ D∈T z,(AN (AX z (adP z)) D:ℚ)*tW D [s] :=
              sum_le_sum fun D hD =>le_mul_of_one_le_left (hn D hD)
                (by exact_mod_cast Nat.succ_le_of_lt (aFq (hT z D hD)))
          _≤tW (AX z (adP z)) [s] :=
              bnG _ [s] (by simpa using hs') (by simpa using hj) (T z) (hT z)
          _≤_:=bnH z a [s] ha (by simpa using hs') (by simp [hd]) _ (bHn hcut) hr
        exact mul_le_mul (by exact_mod_cast (gH h hz').1) hsdeg (sum_nonneg hn) (zqJ _)
    exact (mul_le_mul_of_nonneg_left h1 (by norm_num)).trans
      (pair_mixed32 h ha hs' fun z hz=>(hs z hz).1)
  have hrat : (↑((feeScale :ℤ)*weight A .boundary) :ℚ)≤(↑(curve32 a a p a) :ℚ) := by
    simp only [feeScale,curve32,Nat.cast_mul,Int.cast_mul,Int.cast_add,Int.cast_natCast,
      Int.cast_ofNat,Nat.cast_ofNat]
    have h0:=mul_le_mul_of_nonneg_left hcount (by norm_num : (0:ℚ)≤32)
    have h1 :=mul_le_mul_of_nonneg_left (bnd q hq) (zqJ P6.t)
    have h2 :=mul_le_mul_of_nonneg_left (bnd a ha) (mul_nonneg (by norm_num : (0:ℚ)≤2) (zqJ mV))
    linarith only [h0,h1,h2]
  exact_mod_cast hrat
theorem aFc {C:Context} {R:af 4} (h:Input C R) (A:Charts C R) :
    let a :=cap R; let p:=remainingChart C.v
    (feeScale :ℤ)*weight A .zD ≤
      curve32 a a p (joinBody a p)+2*((shape R).t:ℤ)*curve32 a a p a := by
  classical
  intro a p
  let Γ:=C.Δ.filter fun γ=>xN C R γ∧stratum A γ = .zD
  let zs :=Γ.image A.aI; let u:=weightedChart bf a; let i:=genericOrder R
  have tmark {γ} (ht:stratum A γ = .zD) :
      qg (chartAt A γ) (extend (C.s γ)) ∧ ¬ Invariant (chartAt A γ) (A.aI γ) := by
    by_cases hsep:cK (separant (chartAt A γ)) (extend (C.s γ))=0
    · simp [stratum,hsep] at ht
    · refine ⟨hsep,fun hinv => ?_⟩
      by_cases hj:bC (memTest (chartAt A γ))∈A.aI γ <;> simp [stratum,hsep,hinv,hj] at ht
  let gu (z :znc GeoJets) (v d:ℕ) (F:af 4) :Prop :=
    (∃ hz : (kC R (an1 C)).IsMinimalPrime z,
      oA (kC R (an1 C)) z hz.isPrime=(v :ℕ∞)) ∧
    (bC F∉z∧aO (shape F) ((joinBody a p).plus (a.scale (2*d))) ∧
      i z≤v∧i z*d≤(shape R).t*v) ∧
    ∀ γ∈Γ,A.aI γ=z→cK F (extend (C.s γ))=0
  have exCut (z :znc GeoJets) : ∃ v d F,z∈zs→ gu z v d F:= by
    by_cases hz :z∈zs
    · obtain ⟨γ₀,h₀,he⟩:=mem_image.mp hz
      obtain ⟨hΔ,ha0,htan⟩:=mem_filter.mp h₀
      obtain ⟨hZ,_,hcan⟩:=he ▸ A.valid γ₀ hΔ ha0
      let G:=an1 C; let b:=joinBody a p; let g:=(separant^[A.index z]) R
      have hi : ¬ Invariant g z := by simpa only [chartAt,he,g] using (tmark htan).2
      have hj:0< i z :=q90NBie.generic_positive h.factor.1.ne_zero hZ.isPrime (hZ.le (zCn (by simp)))
      have hG0:G≠0:= fun e=>h.proper (show R∣G from e.symm ▸ dvd_zero R)
      have hG1 :1≤genericOrder G z :=q90NBie.generic_positive hG0 hZ.isPrime (hZ.le (zCn (by simp [G])))
      obtain ⟨v,hv,hlen,hbase⟩:=local_weight h.factor.1 h.proper hZ hG1; rw [one_mul] at hbase
      have hGb: (shape G).b≤133:=h.H6.1.trans
        (max_le (Nat.sub_le ..) ((min_le_left _ _).trans ((Nat.sub_le ..).trans (by decide :56≤133))))
      have hvp:=(hv.trans (Nat.mul_le_mul h.ahD.1 hGb)).trans_lt (by decide :4025*133<K1.p)
      obtain ⟨H,d,_,hd,hH,hF⟩:=qOuMLEd.proof R G R z hZ 1 v (A.index z)
        h.factor.1 h.proper Nat.zero_lt_one hj hG1 hlen hvp hcan hi
      rw [min_eq_right (show 1≤ i z from hj),one_mul] at hd
      have htop:=qOdMfWd.proof R G R z (A.index z) h.factor.1 h.proper
        (h.ahD.1.trans_lt (by decide :4025<K1.p)) hZ hcan
      rw [max_eq_right (Nat.succ_le_iff.mpr h.positive)] at htop
      have hm (γ) (hγ:γ∈Γ) (he :A.aI γ=z) :z≤Ch (extend (C.s γ)) :=
        he ▸ (A.valid γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2.1).2.1
      have hpart:aO (shape H) b ∧ ∀ γ∈Γ,A.aI γ=z→cK H (extend (C.s γ))=0:= by
        rcases hH with ⟨u',hu',rfl⟩ | ⟨u',hu',rfl⟩
        · exact ⟨a4B u' (cDD (a1n R) ⟨le_max_left _ _,le_max_left _ _,le_max_left _ _⟩),
            fun γ hγ he=>Ue.mp (hm γ hγ he (order_mem R z hu'))⟩
        · exact ⟨a4B u' (cDD h.H6 ⟨le_max_right _ _,le_max_right _ _,le_max_right _ _⟩),
            fun γ hγ he=>Ue.mp (hm γ hγ he (order_mem G z (hu'.trans_le hG1)))⟩
      have haj:0<a.j:=(Nat.mul_pos (by decide :0<3) h.positive).trans_le (Tn R).2
      exact ⟨v,d,Uy g H d,fun _=>⟨⟨hZ,hlen⟩,⟨hF,
        bhQ (b:=a) (g:=g) h.positive haj (bc7 R (A.index z)) hpart.1 d,
        hbase,Nat.mul_le_mul htop hd⟩,fun γ hγ he =>
          bhO g H _ d (Ue.mp (hm γ hγ he (hcan.2.1 _ le_rfl))) (hpart.2 γ hγ he)⟩⟩
    · exact ⟨0,0,0,fun hh=>(hz hh).elim⟩
  choose v d F hf using exCut
  have haF:vE a :=⟨Tn R,h.positive⟩
  have hpC:bF p:=(P6_6_8_3.remaining_fits C.v).2
  have huF:vE u:= by
    unfold u weightedChart; split
    · refine ⟨⟨le_max_right _ _,(zBI 3 (min_le_right _ _)).trans (Nat.mul_div_le _ _)⟩,
        lt_min (by decide) (Nat.div_pos (Nat.le_add_right ..) (by decide))⟩
    · exact cTh _ (by decide) _
  have hW:weight A .zD = ∑ z∈zs,(Γ.filter fun γ=>A.aI γ=z).card*i z := by
    change (∑ γ∈C.Δ,if xN C R γ∧stratum A γ = .zD then i (A.aI γ) else 0)= _
    rw [← sum_filter,← sum_fiberwise_of_maps_to' (fun γ hγ=>mem_image_of_mem A.aI hγ)]; simp [zs,Γ]
  let wD (q:Shape) := ∑ z∈zs,i z*an0 q z (F z)
  have hcount:6*mV*weight A .zD ≤P6.t*wD u+2*mV*wD a := by
    rw [hW]; simp only [wD,mul_sum,← sum_add_distrib]
    refine sum_le_sum fun z hz => ?_
    obtain ⟨⟨hZ,_⟩,⟨hF,_,_,_⟩,hv⟩:=hf z hz
    let M:=Γ.filter fun γ=>A.aI γ=z
    let ds :=(AX z (F z)).minimalPrimesFinset
    let mks (D:znc GeoJets) :=M.filter fun γ=>D ≤Ch (extend (C.s γ))
    have hon (γ) (hγ:γ∈M) :z≤Ch (extend (C.s γ)) := by
      obtain ⟨hγ,he⟩:=mem_filter.mp hγ; exact he ▸ (A.valid γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2.1).2.1
    have hcov :M⊆ds.biUnion mks := fun γ hγ=> by
      obtain ⟨hγ',he⟩:=mem_filter.mp hγ
      obtain ⟨D,hD,hm⟩:=bsq (hon γ hγ) (hv γ hγ' he)
      exact mem_biUnion.mpr ⟨D,Ideal.mem_minimalPrimesFinset.mpr hD,mem_filter.mpr ⟨hγ,hm⟩⟩
    have hdim:=bf6 (agr h.factor.1.ne_zero)
      (amo R (an1 C) h.factor.1 h.proper) hZ
    have hcc:6*mV*M.card≤P6.t*an0 u z (F z)+2*mV*an0 a z (F z) := by
      calc _≤6*mV * ∑ D∈ds,(mks D).card :=
            Nat.mul_le_mul_left _ ((card_le_card hcov).trans card_biUnion_le)
        _ = ∑ D∈ds,6*mV*(mks D).card:=mul_sum ..
        _ ≤ ∑ D∈ds,curveCharge a D:=sum_le_sum fun D hD => by
            have hd:=bZi hZ.isPrime hdim
              (hZ.le (Ideal.subset_span (by simp)) :bC R∈z) hF (Ideal.mem_minimalPrimesFinset.mp hD)
            let L:=bf
            have h4 :4≤L:= by decide
            have hL:L≤K1.p:= by decide
            have hsub:mks D⊆C.Δ:= fun γ hγ=>(mem_filter.mp (mem_filter.mp (mem_filter.mp hγ).1).1).1
            have hmsg :=C.messages.mono hsub
            let deg:=pN D ((weightedChart L a).scale 6)
            have hsec:mV*(mks D).card≤P6.t*(deg/6)+mV:= by
              apply P6_6_5.bv5 hmsg; intro j hmiss
              obtain ⟨V,hV,hval⟩:=d40 h4 hL (bc7 R (A.index z)) haF.1 haF.2 (P6.node j) (C.w j)
              have on (γ) (hγ:γ∈mks D) :An (extend (C.s γ)) V=0↔(C.s γ).eval (P6.node j)=C.w j:= by
                obtain ⟨hM,_⟩:=mem_filter.mp hγ; obtain ⟨hγ',he⟩:=mem_filter.mp hM
                obtain ⟨hΔ,ha',ht'⟩:=mem_filter.mp hγ'
                have hc:YR R z (A.index z) :=he ▸ (A.valid γ hΔ ha').2.2
                exact hval _ (Nat.lt_succ_of_le (hmsg.degree γ hγ))
                  (Ue.mp (hon γ hM (hc.2.1 _ le_rfl))) (by simpa only [chartAt,he] using (tmark ht').1)
              have hpr :V∉D:= by
                obtain ⟨γ,hγ,hne⟩:=hmiss; exact fun hv=>hne ((on γ hγ).mp ((mem_filter.mp hγ).2 hv))
              let H :=(mks D).filter fun γ=>(C.s γ).eval (P6.node j)=C.w j
              have hc:=bYX hd.prime hd.dim (taylor_simplex h4 a) hV hpr
                (hmsg.distinct.mono (filter_subset _ _))
                (fun γ hγ=>⟨(mem_filter.mp (filter_subset _ _ hγ)).2,(on γ (filter_subset _ _ hγ)).mpr (mem_filter.mp hγ).2⟩)
              exact (Nat.le_div_iff_mul_le (by decide :0<6)).mpr (by simpa only [Nat.mul_comm] using hc)
            have hu1 :aO ⟨1,3,1⟩ a := by
              obtain ⟨⟨hb,hj⟩,ht⟩:=haF; change 1≤a.b∧3≤a.j∧1≤a.t; omega
            obtain ⟨x,U,hx,hU,hpr,hval⟩:=bDo hd.prime hd.dim
            have he :6≤pN D (a.scale 6) := by
              simpa using bYY D a hd.prime hd.dim hu1 U
                ⟨hU.1.trans hu1.1,hU.2.1.trans hu1.2.1,hU.2.2.trans hu1.2.2⟩ hpr {x}
                (fun y hy=> by rw [mem_singleton.mp hy]; exact ⟨hx,hval⟩)
            simpa only [curveCharge,deg,L,Nat.add_zero] using uq hsec (Nat.mul_div_le deg 6)
              (show 6*0≤pN D (a.scale 6) by simp) he
        _ = _:= by rw [an0,an0,mul_sum,mul_sum,← sum_add_distrib]; rfl
    calc _=i z*(6*mV*M.card) := by ac_rfl
      _≤ i z*(P6.t*an0 u z (F z)+2*mV*an0 a z (F z)) :=Nat.mul_le_mul_left _ hcc
      _ = _:= by ring
  have hdg (q:Shape) (hq:vE q) :
      (32 :ℤ)*(wD q:ℤ)≤6*(wP a p (joinBody a p) q+2*((shape R).t:ℤ)*wP a p a q) := by
    let b:=joinBody a p; let k :=(shape R).t
    let B z :=Ux z (b.scale 6) (q.scale 6); let E z :=Ux z (a.scale 6) (q.scale 6)
    have hb:vE b:=⟨⟨max_le_max haF.1.1 hpC.1,by
      change 3*max a.t p.t≤ max a.j p.j; rw [← Nat.mul_max_mul_left]; exact max_le_max haF.1.2 hpC.2⟩,
      haF.2.trans_le (le_max_left _ _)⟩
    have hrel :=amo R (an1 C) h.factor.1 h.proper
    have hsum:6*wD q≤(∑ z∈zs,v z*B z)+(2*k)*(∑ z∈zs,v z*E z) := by
      dsimp only [wD]; simp only [mul_sum,← sum_add_distrib]
      refine sum_le_sum fun z hz => ?_
      obtain ⟨⟨hZ,_⟩,⟨hF,hfbox,hi,hd'⟩,_⟩:=hf z hz
      have hdim:=bf6 (agr h.factor.1.ne_zero) hrel hZ
      have hone :6*an0 q z (F z)≤B z+2*d z*E z := by
        have he :=c5M z (bC (F z)) _ q hZ.isPrime hdim
          (b4b hb (BP haF.1 (2*d z))) hq hF (abr hfbox)
        have hadd:=cAI z b a q 1 (2*d z) hZ.isPrime hdim hb haF hq Nat.zero_lt_one
        rw [show b.scale 1=b by cases b; simp [Shape.scale],one_mul] at hadd; exact he.trans hadd
      calc _=i z*(6*an0 q z (F z)) := by ring
        _≤ i z*(B z+2*d z*E z) :=Nat.mul_le_mul_left _ hone
        _=i z*B z+(2*(i z*d z))*E z := by ring
        _≤v z*B z+(2*(k*v z))*E z :=Nat.add_le_add (Nat.mul_le_mul_right _ hi)
            (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hd'))
        _ = _:= by ring
    have hB:=aSm.dl4 a p b q h.factor.1 h.proper haF hpC hb hq (a1n R) h.H6 zs v
      (fun z hz=>(hf z hz).1)
    have hE :=aSm.dl4 a p a q h.factor.1 h.proper haF hpC haF hq (a1n R) h.H6 zs v
      (fun z hz=>(hf z hz).1)
    change 32*(∑ z∈zs,v z*B z)≤36*iH a p b q at hB
    change 32*(∑ z∈zs,v z*E z)≤36*iH a p a q at hE
    have hn:32*wD q≤6*(iH a p b q+2*k*iH a p a q) := by
      nlinarith only [zBI 32 hsum,hB,zBI (2*k) hE]
    have hz : (32 :ℤ)*wD q≤6*((iH a p b q:ℤ)+2*(k :ℤ)*(iH a p a q:ℤ)) := by exact_mod_cast hn
    rwa [bhj a p b q hpC hb.1 hq.1,bhj a p a q hpC haF.1 hq.1] at hz
  have hb:=combine hcount (hdg u huF) (hdg a haF)
  simp only [curve32,feeScale,Nat.cast_mul,Nat.cast_ofNat]
  dsimp only [u] at hb; convert hb using 1; ring
end
end qMiJnMd
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qMiJnMd
noncomputable section
open P6_6 P6_6_7
open aR (shape)
private theorem Az (d x e b t u f E J P B F z w:ℤ) {r :ℕ}
    (h:x=e+b+t+u+f) (he :d*e≤E+P) (hb:d*b≤E)
    (ht:d*t≤J+2*(r :ℤ)*E) (hu:d*u≤z+B∧d*u≤w+B)
    (hf :d*f≤F) :
    d*x≤ min z w+B+(2+2*(r :ℤ))*E+J+P+F:= by
  have hm:d*u≤ min z w+B:= by
    rcases le_total z w with hw | hw
    · simpa only [min_eq_left hw] using hu.1
    · simpa only [min_eq_right hw] using hu.2
  rw [h]
  nlinarith only [he,hb,ht,hm,hf]
theorem proof :P6_6_7.c6:= by
  intro C R l ell hR hg ht
  have inp:=input_of_guard hR hg ht
  obtain ⟨A⟩:=charts_exist inp
  let a :=(shape R).iU; let p:=remainingChart C.v; let g:ℤ:=mV
  have hg0:0≤g:= by positivity
  have hmul :min (g*pair32 false a a p) (g*pair32 true a a p) =
      g*min (pair32 false a a p) (pair32 true a a p) := by
    rcases le_total (pair32 false a a p) (pair32 true a a p) with h | h
    · rw [min_eq_left h,min_eq_left (mul_le_mul_of_nonneg_left h hg0)]
    · rw [min_eq_right h,min_eq_right (mul_le_mul_of_nonneg_left h hg0)]
  let B:ℤ:=32*((P6.t:ℤ)+2*g)*a.b*p.b*(weightedChart (bf+1) a).b
  have h:=Az (feeScale :ℤ) (smallMarks C R false) (DG A) (weight A .boundary)
    (weight A .zD) (weight A .taylor) (weight A .fresh) (curve32 a a p a)
    (curve32 a a p (joinBody a p)) (point32 a p a) B (fresh32 (shape R) p)
    (g*pair32 false a a p) (g*pair32 true a a p)
    (by exact_mod_cast sum_strata A)
    (excess_bound inp A) (dzP inp A) (aFc inp A)
    ⟨taylor_bound inp A false,taylor_bound inp A true⟩ (fresh_bound inp A)
  rw [hmul] at h
  exact h
end
end qMiJnMd
end
