import ProximityPrize.SubmissionLower.CT
import ProximityPrize.SubmissionLower.B7
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace dn2
noncomputable section
open aR (ao embed af)
open oR (separant)
open B7 ac1
open scoped Polynomial
private theorem ddz (f :af 3) (hf :Irreducible f) (hd:0<f.degreeOf 2)
  (hmax :f.degreeOf 2<K1.p) :GZ (separant f)∉Jy f := by
 change separant f∉(Jy f).comap Bu
 rw [cFe f hf hd]
 have :CharP ao K1.p:=charP_of_injective_ringHom embed.injective K1.p
 have :CharP ao[X] K1.p :=
  charP_of_injective_ringHom Polynomial.C_injective K1.p
 have hcast: (f.degreeOf 2 :ao[X])≠0:= by
  intro h
  have hp:=(CharP.cast_eq_zero_iff ao[X] K1.p (f.degreeOf 2)).mp h
  exact (not_le_of_gt hmax) (Nat.le_of_dvd hd hp)
 have hsep:separant f≠0:=MvPolynomial.pderiv_ne_zero_of_natCast_ne_zero 2 f hcast
 intro hmem
 obtain ⟨g,hg⟩:=Ideal.mem_span_singleton.mp hmem
 have hgn:g≠0:= by
  intro he
  exact hsep (by simpa [he] using hg)
 have hdeg:=MvPolynomial.degreeOf_pderiv_le_sub_one 2 f
 have h:=congrArg (MvPolynomial.degreeOf (2 :Fin 3)) hg
 rw [MvPolynomial.degreeOf_mul_eq hf.ne_zero hgn] at h
 change (separant f).degreeOf 2≤f.degreeOf 2 - 1 at hdeg
 omega
end
end dn2
end
