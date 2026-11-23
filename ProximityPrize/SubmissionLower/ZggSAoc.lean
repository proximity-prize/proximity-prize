import ProximityPrize.SubmissionLower.ZiWgK3c
import ProximityPrize.SubmissionLower.ZIBb1mb
import ProximityPrize.SubmissionLower.ZY18Mqc
set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace q5l8jMe
noncomputable section
open Polynomial
open aR (af extend)
open dN hiding ZV
open BO (Ue)
open agL (BV EY)
open Dr (aQG)
open rW
open as6 (epq)
open lB (amo)
open P6_6 (M8 aWx)
open P6_6_7 qAzl5me
open P6_6_7_3 (charter char_fits local_weight order_mem agr)
open private hasse_weight from ProximityPrize.SubmissionLower.ZiWgK3c
open private b3Z from ProximityPrize.SubmissionLower.V
open private b30 bGZ cKK b0I from ProximityPrize.SubmissionLower.V
private theorem classify {R G:af 4} {P J:n8} (hp:P.IsPrime) (hJ:J.IsPrime)
    (hcycle : ∀ T,(kC R G).IsMinimalPrime T→dimension T=2)
    (hdP:1≤dimension P) (hcontain:kC R G≤J) (hold:J≤P) :
    (dimension J=1∧J=P)∨(dimension J=2∧(kC R G).IsMinimalPrime J) := by
  let _:=hJ
  obtain ⟨T,hT,hTJ⟩:=Ideal.exists_minimalPrimes_le hcontain
  have hupper :dimension J≤dimension T:=MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le hTJ
  have hlower :dimension P≤dimension J:=MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le hold
  have hdT:=hcycle T hT
  by_cases hd1 :dimension J=1
  · refine Or.inl ⟨hd1,?_⟩
    by_contra hne
    have :=b0I hJ hp (lt_of_le_of_ne hold hne)
    omega
  · have hd2 :dimension J=2 := by omega
    have heq :T=J:= by
      by_contra hne
      have :=b0I hT.isPrime hJ (lt_of_le_of_ne hTJ hne)
      omega
    exact Or.inr ⟨hd2,heq ▸ hT⟩
theorem proof :qAzl5me.c2 := by
  intro C R G ell cs h A γ hγ i a hi hc
  classical
  obtain ⟨hΔ,ho,hell,_⟩:=Finset.mem_filter.mp hγ
  let aI:=A.aI γ
  let g:=chartRow C i a
  let message :=extend (C.s γ)
  obtain ⟨hZ,hmark⟩:=A.valid γ hΔ ho
  have hS:message.natDegree<aR.bf := by
    rw [show message.natDegree=(C.s γ).natDegree from natDegree_map _]
    exact (Nat.lt_succ_of_le (C.messages.degree γ hΔ)).trans_le (by decide)
  have hfg:=(C.marks.factors i (charter h hi.index_mem)).2.2.2
  have hfw:P6_6.tB (C.f i) aWx :=
    fun m hm=>(hfg m hm).trans (by decide :M8≤aWx)
  have hW:=epq (c2l hfw) a
  have hcycle (T:n8) (hT: (kC R G).IsMinimalPrime T) :
      dimension T=2 :=
    aQG (agr h.factor.1.ne_zero)
      (amo R G h.factor.1 h.proper) hT
  have regular {P:n8} (hm:P≤Ch message) :bC (separant g)∉P :=
    fun hp=>hi.regular (Ue.mp (hm hp))
  have finish (P:n8) (hp:P.IsPrime) (hle :aI≤P)
      (hpoint :P≤Ch message) (hI:Invariant g P) (hE :bC (memberTest g)∈P)
      (hbranch :P=aI ∨ ∃ hm:MemberCurve g aI P,hm.simple∧bC (ZV g)∈P) :
      CurveWitness C cs aI γ∨SurfaceWitness C R G ell cs aI γ:= by
    let _:=hp
    have hs :=regular hpoint
    have hg:bC g∈P:=hle (hi.canonical.2.1 a le_rfl)
    obtain ⟨U,hU,hshort,hcont⟩ :=
      integrate h.factor.2.2 h.cutterWeight hW (hZ.le.trans hle) hg hs hE hI
    let B:=Zv (CX P) U
    have hB:B.IsPrime :=RingHom.ker_isPrime _
    obtain ⟨hext,hd,_⟩:=bRp.proof B hB
    obtain ⟨hcontain,hold,hBg,hBs⟩:=bas.gDB hU hs
    have hdim:=(cKK bRq.proof hB hext hBg hBs).trans hd
    have hfamily :Family C i γ B:= by
      refine ⟨⟨hB,hext,⟨a,hBg,hBs⟩,
        bGZ bRq.proof hB hext hBg hBs⟩,?_,
        hU.specializes message hS hpoint hi.regular⟩
      intro j hj
      change MvPolynomial.eval₂Hom (CX P)
        (fun k :Fin aR.bf=>U.coeff k.val) (MvPolynomial.X j)=0
      rw [MvPolynomial.eval₂Hom_X']
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (hshort.trans_le hj)
    have hlower :1≤dimension P:= by
      rcases hbranch with heq | ⟨hm,_,_⟩
      · rw [heq,hcycle aI hZ]
        decide
      · let _:=hZ.isPrime
        have hc:=MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hm.proper hm.minimal
        change dimension P+1=dimension aI at hc
        rw [hcycle aI hZ] at hc
        omega
    rcases classify hp (b30 hext) hcycle hlower hcontain hold with ⟨hd1,heq⟩ | ⟨hd2,hmin⟩
    · rcases hbranch with hPZ | ⟨hm,hone,hnext⟩
      · rw [heq,hPZ,hcycle aI hZ] at hd1
        contradiction
      · refine Or.inl ⟨i,a,B,hi,hfamily,hdim.symm.trans hd1,?_⟩
        rw [heq]
        exact ⟨hm,hpoint,hone,hnext⟩
    · have transfer (H :af 4) (hH :P6_6.tB H aWx)
          {u:Fin 4 →₀ ℕ} (hu:EY u<genericOrder H aI) :
          bC (BV u H)∈lA B :=
        b3Z _ hU.degree _
          (hcont _ (hasse_weight _ hH) (hle (order_mem H aI hu)))
      exact Or.inr ⟨i,a,B,hi,hfamily,hdim.symm.trans hd2,hmin,
        fun _ hu=>transfer R h.factor.2.2 hu,
        fun _ hu=>transfer G h.cutterWeight (hu.trans_le hell)⟩
  rcases hc with hE | ⟨P,hm,hpoint,hone,hnext⟩
  · exact finish aI hZ.isPrime le_rfl hmark hi.invariant hE (Or.inl rfl)
  · obtain ⟨v,hv,hlen,_⟩:=local_weight h.factor.1 h.proper hZ hell
    have hb:=char_fits h
    have hsmall:oA (kC R G) aI hZ.isPrime<(K1.p:ℕ∞) := by
      have hvp:=(hv.trans (Nat.mul_le_mul hb.1 hb.2)).trans_lt (by decide :4025*4025<K1.p)
      rw [hlen]
      exact_mod_cast hvp
    have hI:=invariant_of_simple hZ hsmall hi.invariant hm hone (regular hpoint) hnext
    exact finish P hm.minimal.isPrime (le_sup_left.trans hm.minimal.le) hpoint hI
      (hm.minimal.le (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)))
      (Or.inr ⟨hm,hone,hnext⟩)
end
end q5l8jMe
