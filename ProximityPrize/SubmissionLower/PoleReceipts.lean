import ProximityPrize.SubmissionLower.PoleDebitDefs
import ProximityPrize.SubmissionLower.PoleMoments
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000
namespace PoleReceipts
open K1_14 FourGrid PoleGrid
open scoped BigOperators

private def runSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => runSum f n + f n

private theorem sum_run (f : ℕ → ℕ) (n : ℕ) : ∑ k ∈ Finset.range n, f k = runSum f n := by
  induction n with
  | zero => simp [runSum]
  | succ n ih => rw [Finset.sum_range_succ,ih,runSum]

private theorem specialize_extra (s : Shape) (M C : ℕ)
    (hm : shapeSum s (fun q _ => (s.B+s.J-q)*(s.B-q)) = M)
    (hc : gridCoefficient s.B s.J = C) :
    BankDebit.extra s = (s.U+1)*M - (s.U-s.B+1)*C := by
  unfold BankDebit.extra
  rw [hm,hc]

theorem coeff_76_16 : gridCoefficient 76 16 = 468027 := by
  have hr (i : Fin 4) : rowSum 76 16 (offsetHi 76 16 i) = ![918,527,156,1] i := by
    fin_cases i <;> rw [PoleMoments.rowSum_eq _ _ _ (by decide)] <;> decide +kernel
  have hc (i : Fin 4) : colSum 76 16 (gradeLo 76 i) = ![1172,969,646,323] i := by
    fin_cases i <;> rw [PoleMoments.colSum_eq] <;> decide +kernel
  unfold gridCoefficient
  simp_rw [hr,hc]
  decide +kernel

theorem mass_76_16 (m u : ℕ) :
    shapeSum (⟨m,76,16,u⟩ : Shape) (fun q _ => (76+16-q)*(76-q)) = 2490602 := by
  change (∑ q ∈ Finset.range (76+1), ∑ _k ∈ Finset.range (min q 16+1), (76+16-q)*(76-q)) = _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, sum_run]
  decide +kernel

theorem debit_76_16_1299 : BankDebit.extra ⟨55,76,16,1299⟩ = 2664917552 := by
  exact (specialize_extra ⟨55,76,16,1299⟩ 2490602 468027 (mass_76_16 55 1299) coeff_76_16).trans (by decide +kernel)

theorem coeff_222_46 : gridCoefficient 222 46 = 31247527 := by
  have hr (i : Fin 4) : rowSum 222 46 (offsetHi 222 46 i) = ![7332,4183,1190,1] i := by
    fin_cases i <;> rw [PoleMoments.rowSum_eq _ _ _ (by decide)] <;> decide +kernel
  have hc (i : Fin 4) : colSum 222 46 (gradeLo 222 i) = ![9399,7849,5217,2632] i := by
    fin_cases i <;> rw [PoleMoments.colSum_eq] <;> decide +kernel
  unfold gridCoefficient
  simp_rw [hr,hc]
  decide +kernel

theorem mass_222_46 (m u : ℕ) :
    shapeSum (⟨m,222,46,u⟩ : Shape) (fun q _ => (222+46-q)*(222-q)) = 169342880 := by
  change (∑ q ∈ Finset.range (222+1), ∑ _k ∈ Finset.range (min q 46+1), (222+46-q)*(222-q)) = _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, sum_run]
  decide +kernel

theorem debit_222_46_7106 : BankDebit.extra ⟨160,222,46,7106⟩ = 988380624765 := by
  exact (specialize_extra ⟨160,222,46,7106⟩ 169342880 31247527 (mass_222_46 160 7106) coeff_222_46).trans (by decide +kernel)

theorem coeff_126_27 : gridCoefficient 126 27 = 3445232 := by
  have hr (i : Fin 4) : rowSum 126 27 (offsetHi 126 27 i) = ![2492,1428,420,1] i := by
    fin_cases i <;> rw [PoleMoments.rowSum_eq _ _ _ (by decide)] <;> decide +kernel
  have hc (i : Fin 4) : colSum 126 27 (gradeLo 126 i) = ![3177,2660,1764,896] i := by
    fin_cases i <;> rw [PoleMoments.colSum_eq] <;> decide +kernel
  unfold gridCoefficient
  simp_rw [hr,hc]
  decide +kernel

theorem mass_126_27 (m u : ℕ) :
    shapeSum (⟨m,126,27,u⟩ : Shape) (fun q _ => (126+27-q)*(126-q)) = 18524478 := by
  change (∑ q ∈ Finset.range (126+1), ∑ _k ∈ Finset.range (min q 27+1), (126+27-q)*(126-q)) = _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, sum_run]
  decide +kernel

theorem debit_126_27_1931 : BankDebit.extra ⟨91,126,27,1931⟩ = 29567202504 := by
  exact (specialize_extra ⟨91,126,27,1931⟩ 18524478 3445232 (mass_126_27 91 1931) coeff_126_27).trans (by decide +kernel)

theorem coeff_369_77 : gridCoefficient 369 77 = 236478060 := by
  have hr (i : Fin 4) : rowSum 369 77 (offsetHi 369 77 i) = ![20202,11466,3249,1] i := by
    fin_cases i <;> rw [PoleMoments.rowSum_eq _ _ _ (by decide)] <;> decide +kernel
  have hc (i : Fin 4) : colSum 369 77 (gradeLo 369 i) = ![25856,21606,14430,7254] i := by
    fin_cases i <;> rw [PoleMoments.colSum_eq] <;> decide +kernel
  unfold gridCoefficient
  simp_rw [hr,hc]
  decide +kernel

theorem mass_369_77 (m u : ℕ) :
    shapeSum (⟨m,369,77,u⟩ : Shape) (fun q _ => (369+77-q)*(369-q)) = 1286500592 := by
  change (∑ q ∈ Finset.range (369+1), ∑ _k ∈ Finset.range (min q 77+1), (369+77-q)*(369-q)) = _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, sum_run]
  decide +kernel

theorem debit_369_77_11028 : BankDebit.extra ⟨266,369,77,11028⟩ = 11667958909568 := by
  exact (specialize_extra ⟨266,369,77,11028⟩ 1286500592 236478060 (mass_369_77 266 11028) coeff_369_77).trans (by decide +kernel)

theorem coeff_319_66 : gridCoefficient 319 66 = 131727360 := by
  have hr (i : Fin 4) : rowSum 319 66 (offsetHi 319 66 i) = ![15008,8576,2450,1] i := by
    fin_cases i <;> rw [PoleMoments.rowSum_eq _ _ _ (by decide)] <;> decide +kernel
  have hc (i : Fin 4) : colSum 319 66 (gradeLo 319 i) = ![19228,16080,10720,5360] i := by
    fin_cases i <;> rw [PoleMoments.colSum_eq] <;> decide +kernel
  unfold gridCoefficient
  simp_rw [hr,hc]
  decide +kernel

theorem mass_319_66 (m u : ℕ) :
    shapeSum (⟨m,319,66,u⟩ : Shape) (fun q _ => (319+66-q)*(319-q)) = 714691010 := by
  change (∑ q ∈ Finset.range (319+1), ∑ _k ∈ Finset.range (min q 66+1), (319+66-q)*(319-q)) = _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, sum_run]
  decide +kernel

theorem debit_319_66_3650 : BankDebit.extra ⟨230,319,66,3650⟩ = 2170421313990 := by
  exact (specialize_extra ⟨230,319,66,3650⟩ 714691010 131727360 (mass_319_66 230 3650) coeff_319_66).trans (by decide +kernel)

theorem coeff_837_168 : gridCoefficient 837 168 = 5970134898 := by
  have hr (i : Fin 4) : rowSum 837 168 (offsetHi 837 168 i) = ![99203,56784,16129,1] i := by
    fin_cases i <;> rw [PoleMoments.rowSum_eq _ _ _ (by decide)] <;> decide +kernel
  have hc (i : Fin 4) : colSum 837 168 (gradeLo 837 i) = ![127425,106132,70811,35490] i := by
    fin_cases i <;> rw [PoleMoments.colSum_eq] <;> decide +kernel
  unfold gridCoefficient
  simp_rw [hr,hc]
  decide +kernel

theorem mass_837_168 (m u : ℕ) :
    shapeSum (⟨m,837,168,u⟩ : Shape) (fun q _ => (837+168-q)*(837-q)) = 32496696843 := by
  change (∑ q ∈ Finset.range (837+1), ∑ _k ∈ Finset.range (min q 168+1), (837+168-q)*(837-q)) = _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, sum_run]
  decide +kernel

theorem debit_837_168_25167 : BankDebit.extra ⟨600,837,168,25167⟩ = 672617513941386 := by
  exact (specialize_extra ⟨600,837,168,25167⟩ 32496696843 5970134898 (mass_837_168 600 25167) coeff_837_168).trans (by decide +kernel)

theorem coeff_2845_600 : gridCoefficient 2845 600 = 827576412222 := by
  have hr (i : Fin 4) : rowSum 2845 600 (offsetHi 2845 600 i) = ![1192985,675524,186624,1] i := by
    fin_cases i <;> rw [PoleMoments.rowSum_eq _ _ _ (by decide)] <;> decide +kernel
  have hc (i : Fin 4) : colSum 2845 600 (gradeLo 2845 i) = ![1530145,1282534,855223,427912] i := by
    fin_cases i <;> rw [PoleMoments.colSum_eq] <;> decide +kernel
  unfold gridCoefficient
  simp_rw [hr,hc]
  decide +kernel

theorem mass_2845_600 (m u : ℕ) :
    shapeSum (⟨m,2845,600,u⟩ : Shape) (fun q _ => (2845+600-q)*(2845-q)) = 4523988852695 := by
  change (∑ q ∈ Finset.range (2845+1), ∑ _k ∈ Finset.range (min q 600+1), (2845+600-q)*(2845-q)) = _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, sum_run]
  decide +kernel

theorem debit_2845_600_75000 : BankDebit.extra ⟨2048,2845,600,75000⟩ = 279589084340687063 := by
  exact (specialize_extra ⟨2048,2845,600,75000⟩ 4523988852695 827576412222 (mass_2845_600 2048 75000) coeff_2845_600).trans (by decide +kernel)

theorem coeff_500_105 : gridCoefficient 500 105 = 798299250 := by
  have hr (i : Fin 4) : rowSum 500 105 (offsetHi 500 105 i) = ![37100,21094,5929,1] i := by
    fin_cases i <;> rw [PoleMoments.rowSum_eq _ _ _ (by decide)] <;> decide +kernel
  have hc (i : Fin 4) : colSum 500 105 (gradeLo 500 i) = ![47540,39750,26500,13250] i := by
    fin_cases i <;> rw [PoleMoments.colSum_eq] <;> decide +kernel
  unfold gridCoefficient
  simp_rw [hr,hc]
  decide +kernel

theorem mass_500_105 (m u : ℕ) :
    shapeSum (⟨m,500,105,u⟩ : Shape) (fun q _ => (500+105-q)*(500-q)) = 4343593800 := by
  change (∑ q ∈ Finset.range (500+1), ∑ _k ∈ Finset.range (min q 105+1), (500+105-q)*(500-q)) = _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, sum_run]
  decide +kernel

theorem debit_500_105_6798 : BankDebit.extra ⟨358,500,105,6798⟩ = 24503607270450 := by
  exact (specialize_extra ⟨358,500,105,6798⟩ 4343593800 798299250 (mass_500_105 358 6798) coeff_500_105).trans (by decide +kernel)

theorem debit_500_105_4860 : BankDebit.extra ⟨358,500,105,4860⟩ = 17632826432550 := by
  exact (specialize_extra ⟨358,500,105,4860⟩ 4343593800 798299250 (mass_500_105 358 4860) coeff_500_105).trans (by decide +kernel)

theorem debit_500_105_3913 : BankDebit.extra ⟨358,500,105,3913⟩ = 14275432493700 := by
  exact (specialize_extra ⟨358,500,105,3913⟩ 4343593800 798299250 (mass_500_105 358 3913) coeff_500_105).trans (by decide +kernel)

theorem debit_500_105_66251 : BankDebit.extra ⟨358,500,105,66251⟩ = 235282004151600 := by
  exact (specialize_extra ⟨358,500,105,66251⟩ 4343593800 798299250 (mass_500_105 358 66251) coeff_500_105).trans (by decide +kernel)
end PoleReceipts
