import ProximityPrize.SubmissionLower.AS
set_option Elab.async false
set_option autoImplicit true
section
namespace dnZ
open fP (qI)
open private triangle sum_congr bOz bxa from ProximityPrize.SubmissionLower.Z0omYcd
set_option maxRecDepth 4000
private theorem dfV (u k x :ℕ) :
    (qI u fun r=>k-(x - r)) =
      u*k-((triangle x - triangle (x - u)) -
        (triangle (x - k) - triangle (x - k - u))) := by
  have he : (qI u fun r=>k-(x - r)) +
      ((qI u fun r=>x - r)-(qI u fun r=>x - k - r))=u*k := by
    have hmin: (qI u fun r=>min k (x - r))+(qI u fun r=>x - k - r) =
        qI u (fun r=>x - r) := by
      rw [← bOz]
      exact sum_congr _ fun r=> by omega
    rw [← hmin,Nat.add_sub_cancel]
    rw [← bOz]
    trans qI u (fun _=>k)
    · exact sum_congr _ fun r=> by omega
    · simp [fP.aAs]
  rw [bxa,bxa] at he
  omega
end dnZ
end
