import ProximityPrize.SubmissionLower.ZL1G0Rc
import ProximityPrize.SubmissionLower.AU
import ProximityPrize.SubmissionLower.AW
import ProximityPrize.SubmissionLower.ZUCbske
import ProximityPrize.SubmissionLower.C3
set_option Elab.async false
set_option autoImplicit true
section
open private a0F.u a0F.v from ProximityPrize.SubmissionLower.ZL1G0Rc
namespace By
open aR (Shape)
open Jt (fQ)

open bJ (Valid)


private theorem b7q {r :fQ} {a :Shape} (h:r.dY a)
  (hv :Valid a) :be3 r≤a.b:= by
 obtain ⟨hb,_,hj,_⟩:=h
 have hvalid :=hv.2.2
 exact max_le hb (by omega)
private theorem oJ {r u v :fQ} {a b c:Shape}
  (ha :r.dY a) (hb:u.dY b) (hc:v.dY c)
  (va :Valid a) (vb:Valid b) (vc:Valid c)
  (hB:a.b+b.b+c.b≤125) (hJ:a.j+b.j+c.j≤51) :
  (clip r u v).dY a := by
 have haB₀:=b7q ha va
 obtain ⟨_,haB,haJ,haJ'⟩:=ha
 have hbB:=b7q hb vb
 have hcB:=b7q hc vc
 have hbJ:=hb.2.2.1
 have hcJ:=hc.2.2.1
 have hcap:a.b≤ min r.upperB (125-(be3 u+be3 v)) :=le_min haB (by omega)
 have hvalid :=va.2.2
 exact ⟨haB₀,hcap,haJ,le_min haJ' (le_min (by omega) (by omega))⟩
theorem bYH {r :Cell} {p x y :Shape}
  (h:r.dY p x y) (hp:Path p x y) : (XH r).dY p x y := by
 have hb:p.b + x.b+y.b≤125:=hp.fits.1
 have hj:p.j + x.j+y.j≤51 :=hp.fits.2.1
 obtain ⟨h₁,h₂,h₃⟩:=h
 exact ⟨oJ h₁ h₂ h₃ hp.vp hp.vx hp.vy hb hj,
  oJ h₂ h₁ h₃ hp.vx hp.vp hp.vy (by omega) (by omega),
  oJ h₃ h₁ h₂ hp.vy hp.vp hp.vx (by omega) (by omega)⟩
private theorem bYG {r :fQ} {a :Shape} (h:r.dY a)
   (index :Bool) (k :ℕ) :
   (half r index false k).dY a∨(half r index true k).dY a := by
 obtain ⟨hb,hb',hj,hj'⟩:=h
 cases index
 · by_cases h:a.b≤k
   · exact Or.inl ⟨hb,h,hj,hj'⟩
   · exact Or.inr ⟨show k+1≤a.b by omega,hb',hj,hj'⟩
 · by_cases h:a.j≤k
   · exact Or.inl ⟨hb,hb',hj,h⟩
   · exact Or.inr ⟨hb,hb',show k+1≤a.j by omega,hj'⟩
theorem split {r :Cell} (i:Position) (index :Bool) (k :ℕ)
   (h₁:ay (XH (branch r i index false k)))
   (h₂:ay (XH (branch r i index true k))) :ay r := by
 intro p x y hp hm
 suffices h: (branch r i index false k).dY p x y ∨
     (branch r i index true k).dY p x y by
   rcases h with h | h
   · exact h₁ p x y hp (bYH h hp)
   · exact h₂ p x y hp (bYH h hp)
 obtain ⟨ha,hb,hc⟩:=hm
 cases i with
 | first=>exact (bYG ha index k).imp (fun h=>⟨h,hb,hc⟩) (fun h=>⟨h,hb,hc⟩)
 | middle=>exact (bYG hb index k).imp (fun h=>⟨ha,h,hc⟩) (fun h=>⟨ha,h,hc⟩)
 | last=>exact (bYG hc index k).imp (fun h=>⟨ha,hb,h⟩) (fun h=>⟨ha,hb,h⟩)
end By
end
