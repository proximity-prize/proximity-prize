import ProximityPrize.SubmissionLower.AI
import ProximityPrize.SubmissionLower.M
import ProximityPrize.SubmissionLower.B4
set_option Elab.async false
set_option maxHeartbeats 1200000
open _root_ renaming Algebra.algebraMap→c9,Ideal→lz,IsSeparable→cy,MvPolynomial.X→lI,Polynomial.ringHom_ext'→nI,Polynomial.uniqueFactorizationMonoid→n5,RingHom.comap_ker→nX,RingHom.ker→mD,UniqueFactorizationMonoid→nq,gT.Ambient→aU,right_ne_zero_of_mul→lV,ringKrullDim→lJ
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace ac6.Bridge
noncomputable section
open Polynomial
open cu (Jet aZ FX)
open gT (iJ Dk CG ek)
open pI (xN dual)
open qQ (zI N5 HR aQ tJ aiF IW aif bHX Ng)
open Qr (PW)
open private aqH bOX from ProximityPrize.SubmissionLower.AH
open private b2Y pO JH dcQ zq from ProximityPrize.SubmissionLower.A0
open private co4 cty ctD ctC aJQ adO a4i
 b4B b4D b4C bNC from ProximityPrize.SubmissionLower.A0
def aQF (I:lz aU) (hI:I.IsPrime) :zI :=
 ⟨I.comap iJ,hI.comap _⟩
private theorem ecT (a b:HR) :
   (PW a b).comp (iJ.comp Ng) =
     aif.comp adO.symm.toRingHom:= by
 have hV: ((PW a b).comp (iJ.comp Ng)) (Polynomial.X (R:=FX[X])) =
     (aif.comp adO.symm.toRingHom) Polynomial.X:= by
   simp [Ng,b4C,ctC,PW,aif,ek]
 apply nI _ hV
 have hY: (((PW a b).comp (iJ.comp Ng)).comp C)
     (Polynomial.X (R:=FX)) =
     ((aif.comp adO.symm.toRingHom).comp C) Polynomial.X:= by
   simp [Ng,b4D,ctD,PW,aif,ek]
 apply nI _ hY
 ext x
 simp [Ng,b4B,cty,PW,bNC]
private theorem gxF {I:lz aU} (hI:I.IsPrime) (hh:I.height=2) :
  (aQF I hI).asIdeal.height=2 := by
 change (I.comap iJ).height=2
 rw [bOX]
 exact (aqH.symm.height_comap I).trans hh
private theorem gpe {I:lz aU} (hI:xN I) :
   ∃ y v,qQ.aF5 (aQF I hI.prime) y v ∧
     cy aQ y∧cy aQ v := by
 obtain ⟨f,hf,hsep⟩ := @b2Y Dk _ pO I hI.prime
   hI.bg9 hI.seed_size.1 hI.seed_size.2
 refine ⟨f (lI 0),f (lI 1),?_,hsep _,hsep _⟩
 unfold qQ.aF5
 rw [← co4,← nX ,dcQ,hf]
 rfl
private theorem ep9 {I:lz aU} (hI:I.IsPrime)
   (a b:HR) (hjker :mD (PW a b)=I)
   (ha :cy aQ a) (hb:cy aQ b) :
   ∃ g:Jet →+* aiF,
     g.comp Ng=bHX∧mD g=(aQF I hI).asIdeal ∧
     ∀ i:Fin 2,cy tJ (g (C (C (lI i)))) := by
 let e :=a4i.symm
 let top:tJ →+* aiF:=c9 tJ aiF
 let:Algebra aQ aiF:=(top.comp e.toRingHom).toAlgebra
 let l:HR →ₐ[aQ] aiF :=
   IsAlgClosed.lift (R:=aQ) (S:=HR) (M:=aiF)
 let F:=l.toRingHom.comp ((PW a b).comp iJ)
 have hscalar (x :aQ) :
     l (c9 aQ HR x)=c9 tJ aiF (e x) := by
   exact l.commutes x
 refine ⟨F,?_,?_,?_⟩
 · apply RingHom.ext
   intro x
   change l ((PW a b).comp (iJ.comp Ng) x)= _
   rw [ecT,RingHom.comp_apply]
   change l (c9 aQ HR (c9 aZ aQ
     (adO.symm x)))= _
   rw [hscalar]
   change top (e (c9 aZ aQ (adO.symm x))) =
     top (c9 IW tJ x)
   apply congrArg top
   apply a4i.injective
   rw [RingEquiv.apply_symm_apply]
   exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap (A:=IW)
     (K:=tJ) (B:=aZ) (L:=aQ) adO.symm x).symm
 · change mD (l.toRingHom.comp ((PW a b).comp iJ))= _
   rw [RingHom.ker_comp_of_injective _ l.injective,← nX ,hjker]
   rfl
 · have hs (x :HR) (hx :cy aQ x) :cy tJ (l x) := by
     have hx' : (minpoly aQ x).Separable :=hx
     apply (hx'.map (f :=e.toRingHom)).of_dvd
     apply minpoly.dvd
     rw [aeval_def,Polynomial.eval₂_map]
     change (minpoly aQ x).eval₂ (c9 aQ aiF) (l x)=0
     rw [← aeval_def,aeval_algHom_apply l,minpoly.aeval,map_zero]
   intro i
   fin_cases i
   · change cy tJ (l ((PW a b) (iJ (C (C (lI 0))))))
     rw [aJQ]
     simpa [PW] using hs a ha
   · change cy tJ (l ((PW a b) (iJ (C (C (lI 1))))))
     rw [aJQ]
     simpa [PW] using hs b hb
theorem cbq {I:lz aU} (hI:xN I) (hh:I.height=2) (hj:dual I) :
  N5 (aQF I hI.prime) := by
 obtain ⟨g,hg,hsep⟩ := @b2Y CG _ JH I hI.prime hI.jet_finite hj hI.jet_lt
 have hker :mD (PW (g (lI 0)) (g (lI 1)))=I:= by
  rw [zq,hg]
 exact ⟨gxF hI.prime hh,gpe hI,
  ep9 hI.prime _ _ hker (hsep _) (hsep _)⟩
end
end ac6.Bridge
end
section
namespace ac6.Bridge
private theorem dXK:OH.c1 :=
 cy7.proof
private theorem dXM:aiM.c1 :=
 cy8.proof
private theorem dXN :aiM.c2 :=
 baA.proof
private theorem dXO:aiM.c3 :=
 bzT.proof
private theorem dXL:OH.c2 :=
 aiM.of_children dXM dXN dXO
private theorem dXP:OH.c3 :=
 bzU.proof
private theorem dXQ:OH.c4 :=
 cy9.proof
private theorem dXR:OH.c5 :=
 cza.proof
theorem dS4 :ac3.c2 :=
 OH.of_children dXK dXL dXP dXQ dXR
private theorem dXS:ac4.c1 :=
 czb.proof
private theorem dXW:ac4.c2 :=
 czc.proof
private theorem dX2 :axk.c1 :=
 czd.proof
private theorem dX3:axk.c2 :=
 cze.proof
private theorem dX4 :axk.c3 :=
 czf.proof
private theorem dX5:axk.c4 :=
 czg.proof
private theorem dX1 :K1_14_2_2_7_3_3.c1 :=
 axk.of_children dX2 dX3 dX4 dX5
private theorem dX6:K1_14_2_2_7_3_3.c2 :=
 baB.proof
private theorem dX0:ac4.c3 :=
 K1_14_2_2_7_3_3.of_children dX1 dX6
theorem dSZ:ac3.c3 :=
 ac4.of_children dXS dXW dX0
private theorem dX7:WJ.c1 :=
 bzV.proof
private theorem dX8:WJ.c2 :=
 czh.proof
private theorem dX9:WJ.c3 :=
 czi.proof
private theorem dYb:MM.c1 :=
 bzW.proof
private theorem dYc:MM.c2 :=
 czj.proof
private theorem dYd:MM.c3 :=
 czk.proof
private theorem dYe :MM.c4 :=
 czl.proof
private theorem dYf :MM.c5 :=
 czm.proof
private theorem dYg:MM.c6 :=
 baC.proof
private theorem dYi:axl.c1 :=
 czn.proof
private theorem dYj:axl.c2 :=
 czo.proof
private theorem dYh:MM.c7 :=
 axl.of_children dYi dYj
private theorem dYk :MM.c8 :=
 czp.proof
private theorem dYa :WJ.c4 :=
 MM.of_children
  dYb dYc dYd dYe dYf dYg dYh dYk
theorem dSJ:ac3.c4 :=
 WJ.of_children dX7 dX8 dX9 dYa
end ac6.Bridge
end
section
namespace ac6.Bridge
private theorem dXt:aqd.c1 :=
 bRL.proof
private theorem dXu:aqd.c2 :=
 bzY.proof
private theorem cK1 :Cu.c1 :=
 aqd.of_children dXt dXu
private theorem dXv :UI.c1 :=
 czr.proof
private theorem dXw:UI.c2 :=
 czs.proof
private theorem cK2 :Cu.c2 :=
 UI.of_children dXv dXw
private theorem dXx :XW.c1 :=
 bzZ.proof
private theorem dXz :aFZ.c1 :=
 czt.proof
private theorem dXA:aFZ.c2 :=
 czu.proof
private theorem dXy :XW.c2 :=
 aFZ.of_children dXz dXA
private theorem dXC:aiN.c1 :=
 bz0.proof
private theorem dXD:aiN.c2 :=
 czv.proof
private theorem dXE :aiN.c3 :=
 bz1.proof
private theorem dXB:XW.c3 :=
 aiN.of_children dXC dXD dXE
private theorem cK3:Cu.c3 :=
 XW.of_children dXx dXy dXB
private theorem dXF:aiO.c1 :=
 czw.proof
private theorem dXG:aiO.c2 :=
 czx.proof
private theorem dXH :aiO.c3 :=
 czy.proof
private theorem cK4 :Cu.c4 :=
 aiO.of_children dXF dXG dXH
private theorem dXI:akS.c1 :=
 bz2.proof
private theorem dXJ:akS.c2 :=
 aR1.proof
private theorem cK5:Cu.c5 :=
 akS.of_children dXI dXJ
private theorem dXT:aqe.c1 :=
 czz.proof
private theorem dXU:aqe.c2 :=
 czA.proof
private theorem dXV:ane.c1 :=
 aqe.of_children dXT dXU
private theorem dXX:aqf.c1 :=
 czB.proof
private theorem dXY:aqf.c2 :=
 czC.proof
private theorem dXZ:ane.c2 :=
 aqf.of_children dXX dXY
theorem fXY:DQ.c3 :=
 ane.of_children dXV dXZ
end ac6.Bridge
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace dnF
noncomputable section
open P0 (p)
open cu gT pI YX XY Polynomial
open scoped BigOperators Classical
open private aRY.S5 beL from ProximityPrize.SubmissionLower.T
open private c5I from ProximityPrize.SubmissionLower.B4
private theorem a8m:YX.c4 :=
 aeE.of_children cyW.proof cyX.proof cyY.proof
private theorem ddo:YX.c6 :=
 aRZ.of_children aKw.proof cyZ.proof
private theorem height_le {I:lz aU} (hI:I.IsPrime)
   (hdim:lJ (gk I)=2) :I.height≤2 := by
 let x :PrimeSpectrum Ambient:=⟨I,hI⟩
 have hc:Order.coheight x=2 := by
   rw [ringKrullDim_quotient] at hdim
   change Order.krullDim (Set.Ici x)=2 at hdim
   rw [← Order.coheight_eq_krullDim_Ici] at hdim
   exact WithBot.coe_injective hdim
 have hd:lJ aU=4 := by simp [ringKrullDim_eq_zero_of_field]
 have hh: (↑(Order.height x+Order.coheight x) :WithBot ℕ∞)≤ lJ Ambient:= by
   rw [lJ,Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
   exact WithBot.coe_le_coe.mpr (le_iSup (fun y :PrimeSpectrum aU =>
     Order.height y+Order.coheight y) x)
 rw [hc,← x.height_eq_orderHeight,hd] at hh
 have hh' : I.height+2≤(2 :ℕ∞)+2 :=WithBot.coe_le_coe.mp hh
 exact (ENat.add_le_add_iff_right (by simp : (2 :ℕ∞) ≠ ⊤)).mp hh'
private theorem bYs {P Q:Jet} {I:lz aU} (hp:ag6 P Q)
  (hI:I.IsPrime) (hdim:lJ (gk I)=2)
  (hP:iJ P∈I) (hQ:iJ Q∈I) :I.height=2 := by
 let J:=I.comap aRY.S5.toRingHom
 let:J.IsPrime :=hI.comap _
 have hP' : P∈J:= by change aRY.S5 P∈I; rwa [beL]
 have hQ' : Q∈J:= by change aRY.S5 Q∈I; rwa [beL]
 exact le_antisymm (height_le hI hdim)
  ((aRY.S5.height_comap I) ▸ c5I hp J hP' hQ')
private theorem c2M (f :Equation) (hi:Irreducible f) (hd:0<f.natDegree)
    (hp:f.natDegree<p) :
    ∃ S:Finset (lz aU),
      (∀ I∈S,I.IsPrime∧lJ (gk I)=2∧I.height=2 ∧
        bjf I∧iJ (C f)∈I) ∧
      dM S (af1 (My f) f.natDegree) ∧
      ∀ z R,yq f z R=0 → ∃ I∈S,IZ I z R:= by
  obtain ⟨g,a,hclear,hproper,hfCaps,hgCaps⟩:=czG.proof f hi hd hp
  obtain ⟨S,hS,hcover⟩:=aRY.proof _ _ hproper
  obtain ⟨hfinite,hfits⟩:=a8m _ _ hproper
    ⟨0,f.natDegree,0,My f⟩ ⟨0,f.natDegree,1,My f⟩
    (Nat.zero_le _) hd hfCaps hgCaps S hS
  refine ⟨S,?_,?_,?_⟩
  · intro I hI
    obtain ⟨hprime,hdim,hrow,hcut⟩:=hS I hI
    exact ⟨hprime,hdim,bYs hproper hprime hdim hrow hcut,hfinite I hI,hrow⟩
  · intro k
    have h:=hfits k
    fin_cases k <;> simpa [aJh,af1,two_mul,Nat.add_mul] using h
  · intro z R hz
    exact hcover z R (by simpa [rD,yq] using hz) (YZ.bWP hclear hz)
end
end dnF
end
section
set_option backward.isDefEq.respectTransparency false
namespace bR0
noncomputable section
open cu gT pI Ty Polynomial
open private aUy c1e b1e
 bOX aqH from ProximityPrize.SubmissionLower.AH
structure bTx {P Q:Jet} {s t:Shape} (A:NO P s) (B:NO Q t) where
 iy :Equation
 left:Jet
 right:Jet
 ordinary_ne :iy≠0
 left_ne :left≠0
 right_ne :right≠0
 left_factor :P=Gw A.equation*(C iy*left)
 right_factor :Q=Gw B.equation*(C iy*right)
 relativelyPrime :IsRelPrime (iJ left) (iJ right)
 acI:gY iy≤ s.U
 ordinate_le :iy.natDegree≤ s.B
 left_caps :oU left (aea s (gY iy) iy.natDegree)
 right_caps :oU right (aea t (gY iy) iy.natDegree)
theorem gp3 {P Q:Jet} {s t:Shape} (A:NO P s) (B:NO Q t)
   (hP:P≠0) (hQ:Q≠0) (hPs :oU P s) (hQs :oU Q t)
   (hno:qQ.aeH P Q) :Nonempty (bTx A B) := by
 let:nq aZ:=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
 let:nq Equation :=n5 (D:=aZ)
 let:nq Jet:=n5 (D:=Equation)
 let gcdJet:GCDMonoid Jet:=UniqueFactorizationMonoid.toGCDMonoid Jet
 let D:Jet:=gcdJet.gcd A.residual B.residual
 obtain ⟨L,R,hL,hR,hrel⟩ := @extract_gcd Jet _ gcdJet A.residual B.residual
 change A.residual=D *L at hL
 change B.residual=D *R at hR
 have hF:P=Gw A.equation*(D *L) :=
   A.factorization.trans (congrArg (Gw A.equation * ·) hL)
 have hG:Q=Gw B.equation*(D *R) :=
   B.factorization.trans (congrArg (Gw B.equation * ·) hR)
 have hFL:=lV (hF ▸ hP)
 have hGR:=lV (hG ▸ hQ)
 have hDne :=left_ne_zero_of_mul hFL
 have hDdeg:D.natDegree=0:= by
   apply c1e
   intro F hIrr hfd
   by_contra hpos
   have hleft:=hfd.trans (gcdJet.gcd_dvd_left A.residual B.residual)
   have hright:=hfd.trans (gcdJet.gcd_dvd_right A.residual B.residual)
   obtain ⟨G,hG⟩:=hno F hIrr (b1e A hleft)
     (b1e B hright) (Nat.pos_of_ne_zero hpos)
   exact A.Ra G (hG ▸ hIrr) (hG ▸ hleft)
 let H :=D.coeff 0
 have hD:D =C H :=eq_C_of_natDegree_eq_zero hDdeg
 have hH :H≠0:= fun hz=>hDne (by rw [hD,hz,map_zero])
 rw [hD] at hF hG
 obtain ⟨hFu,hFb,hLc⟩:=aUy hP hH hPs hF
 obtain ⟨_,_,hRc⟩:=aUy hQ hH hQs hG
 have hprime :IsRelPrime (iJ L) (iJ R) := by
   have hr :=(@gcd_isUnit_iff_isRelPrime Jet _ gcdJet L R).mp hrel
   rw [bOX]
   intro E hEL hER
   have h1 :aqH E∣L:= by
     simpa using map_dvd aqH.toRingHom hEL
   have h2 :aqH E∣R:= by
     simpa using map_dvd aqH.toRingHom hER
   simpa using (hr h1 h2).map aqH.symm.toRingHom
 exact ⟨⟨H,L,R,hH,lV hFL,lV hGR,
   hF,hG,hprime,hFu,hFb,hLc,hRc⟩⟩
end
end bR0
end
