import ProximityPrize.SubmissionLower.AI
import ProximityPrize.SubmissionLower.B5
set_option Elab.async false
set_option autoImplicit true
section
namespace czT
theorem bOc:lB.c1 :=
 YV.of_children
  (XT.of_children
    (aA8.of_children cyB.proof cyC.proof)
    (as7.of_children cyD.proof bRB.proof))
  cyE.proof
theorem bOG:lB.c2 :=
 YW.of_children cyF.proof
  (akP.of_children
    (aFV.of_children bzG.proof cyG.proof)
    (as8.of_children cyH.proof cyI.proof))
end czT
end
section
namespace dnL
noncomputable section
open aR dN wH Rl agP bzH
open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial
open private top dhD dhB dhz from ProximityPrize.SubmissionLower.L
private theorem cYz (f :af 4) (q:af 3)
    (hq:Squarefree (fW q)) (aI:Ideal GeoJets)
    (h:aqk f q aI) :bz9 f q aI h.minimal.isPrime := by
  let:aI.IsPrime :=h.minimal.isPrime
  let A:=Localization.AtPrime aI
  let l:GeoJets →+* A:=algebraMap GeoJets A
  let J:=kC f (He q)
  let e :GeoJets ≃ₐ[GeoField] Lower[X] :=top
  let F:=e (bC f)
  have hlower (u:af 3) :e (bC (He u))=Polynomial.C (fW u) := by
    change top (MvPolynomial.map j8 (MvPolynomial.rename Fin.castSucc u))= _
    rw [MvPolynomial.map_rename,dhD]
    rfl
  have hlead:e (bC (He (Ex.X7 f)))=Polynomial.C F.leadingCoeff := by
    rw [hlower]
    congr 1
    change MvPolynomial.map j8 (top f).leadingCoeff =
      (top (MvPolynomial.map j8 f)).leadingCoeff
    have hinj:Function.Injective j8 :=
      (algebraMap lN GeoField).injective.comp
        (IsFractionRing.injective (Polynomial ao) lN)
    rw [dhB,Polynomial.leadingCoeff_map_of_injective (MvPolynomial.map_injective _ hinj)]
  have hsep:e (bC (separant f))=F.derivative := by
    change top (MvPolynomial.map j8 (MvPolynomial.pderiv 3 f)) =
      (top (MvPolynomial.map j8 f)).derivative
    rw [← MvPolynomial.pderiv_map,dhz]
  have hJ:J.map e.toRingHom=Ideal.span {F,Polynomial.C (fW q)} := by
    change (Ideal.span {bC f,bC (He q)}).map e.toRingHom= _
    rw [Ideal.map_span,Set.image_pair]
    change Ideal.span {F,e (bC (He q))} = _
    rw [hlower]
  have hqrad: (Ideal.span ({fW q} : Set Lower)).IsRadical :=
    isRadical_iff_span_singleton.mp (isRadical_iff_squarefree_or_zero.mpr (Or.inl hq))
  have hrad: (J.map l).radical≤J.map l:= by
    rw [← IsLocalization.map_radical aI.primeCompl A J]
    apply Ideal.map_le_iff_le_comap.mpr
    intro g hg
    obtain ⟨n,hn⟩:=Ideal.mem_radical_iff.mp hg
    have hn' : e g^n∈Ideal.span {F,Polynomial.C (fW q)} := by
      rw [← hJ,← map_pow]
      exact Ideal.mem_map_of_mem e.toRingHom hn
    obtain ⟨k,hk⟩:=dLw F (e g) hqrad hn'
    let u:=bC (He (Ex.X7 f))^k*bC (separant f)
    have hu:u∉aI:=h.minimal.isPrime.mul_notMem
      (fun hm=>h.leading (h.minimal.isPrime.mem_of_pow_mem _ hm)) h.regular
    have humem:u*g∈J:= by
      have hc: (J.map e.toRingHom).comap e.toRingHom=J :=
        Ideal.comap_map_of_bijective e.toRingHom e.bijective
      rw [← hc,Ideal.mem_comap,hJ]
      change e (u*g)∈_
      simpa only [u,map_mul,map_pow,hlead,hsep,mul_assoc] using hk
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff aI.primeCompl A J g).mpr
      ⟨u,hu,humem⟩
  change J.map l=IsLocalRing.maximalIdeal A
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal aI A,
      ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes A aI J h.minimal]
  exact le_antisymm Ideal.le_radical hrad
end
end dnL
end
section
namespace bR7
noncomputable section
open Polynomial aR wH lB Tx aKu XU
open scoped BigOperators Pointwise
private theorem cHe :XU.c1 :=
 aRW.of_children cyP.proof cyQ.proof
private theorem deY:XU.c3 :=
 VG.of_children bjD.proof
  (axi.of_children bzN.proof bzO.proof)
  (aA9.of_children cyR.proof bzP.proof)
  baw.proof
end
end bR7
end
section
namespace bR7
noncomputable section
open Polynomial Finset K1 aR wH Tx lB
open scoped BigOperators
open private cr2 bOF dgk bdx from ProximityPrize.SubmissionLower.J
private theorem cFB {f :af 4} (ht:0<(shape f).t)
  {r :PrimeSpectrum gQ} {y :oe} (h:r.asIdeal<Ol y) :
  ∃ F:gQ,Supported (shape f).iU F∧F∉r.asIdeal ∧
    r.asIdeal≤Ol y∧MvPolynomial.eval y F=0:= by
 obtain ⟨i,hi⟩:=bdx h
 obtain ⟨hb,hj⟩:=Tn f
 have hj' : 3≤(shape f).iU.j:= by
  have htop:0<(shape f).iU.t:=ht
  omega
 have hb' : 1≤(shape f).iU.b:=(by decide :1≤3).trans (hj'.trans hb)
 exact ⟨MvPolynomial.X i-MvPolynomial.C (y i),
  cr2 (dgk hb' hj' ht i) (bOF _ _),hi,h.le,by simp⟩
end
end bR7
end
