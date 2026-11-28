import ProximityPrize.SubmissionLower.R6970Height2313CompressedCore
import ProximityPrize.SubmissionLower.R6970Height2313GradeArithmetic

set_option Elab.async false

namespace Research6970.Height2313.Research6969.ExtendedJointBills
open _root_.Research6969
open JointLedger JointRouted _root_.Research6970.Height2313.Research6969.BookView

theorem bill1 : ∀ a b : Fin 22, a.val + b.val ≤ 21 →
    Pass (mainBook (0:Fin 18)) (rescueBook (0:Fin 18))
      (seedWeight 133384 1) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 1 = 389097 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill1


theorem bill2 : ∀ a b : Fin 23, a.val + b.val ≤ 22 →
    Pass (mainBook (1:Fin 18)) (rescueBook (1:Fin 18))
      (seedWeight 133384 2) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 2 = 778190 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill2

theorem counted2 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 22) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (1:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 22 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill2

theorem bill3 : ∀ a b : Fin 23, a.val + b.val ≤ 22 →
    Pass (mainBook (2:Fin 18)) (rescueBook (2:Fin 18))
      (seedWeight 133384 3) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 3 = 1167283 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill3

theorem counted3 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 22) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (2:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 22 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill3

theorem bill4 : ∀ a b : Fin 23, a.val + b.val ≤ 22 →
    Pass (mainBook (3:Fin 18)) (rescueBook (3:Fin 18))
      (seedWeight 133384 4) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 4 = 1556375 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill4

theorem counted4 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 22) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (3:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 22 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill4

theorem bill5 : ∀ a b : Fin 24, a.val + b.val ≤ 23 →
    Pass (mainBook (4:Fin 18)) (rescueBook (4:Fin 18))
      (seedWeight 133384 5) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 5 = 1945468 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill5

theorem counted5 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 23) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (4:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 23 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill5

theorem bill6 : ∀ a b : Fin 25, a.val + b.val ≤ 24 →
    Pass (mainBook (5:Fin 18)) (rescueBook (5:Fin 18))
      (seedWeight 133384 6) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 6 = 2334561 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill6

theorem counted6 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 24) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 24 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill6

theorem bill7 : ∀ a b : Fin 25, a.val + b.val ≤ 24 →
    Pass (mainBook (6:Fin 18)) (rescueBook (6:Fin 18))
      (seedWeight 133384 7) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 7 = 2723653 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill7

theorem counted7 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 24) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (6:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 24 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill7

theorem bill8 : ∀ a b : Fin 25, a.val + b.val ≤ 24 →
    Pass (mainBook (7:Fin 18)) (rescueBook (7:Fin 18))
      (seedWeight 133384 8) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 8 = 3112746 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill8

theorem counted8 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 24) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (7:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 24 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill8

theorem bill9 : ∀ a b : Fin 27, a.val + b.val ≤ 26 →
    Pass (mainBook (8:Fin 18)) (rescueBook (8:Fin 18))
      (seedWeight 133384 9) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 9 = 3501839 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill9

theorem counted9 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 26) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (8:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 26 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill9

theorem bill10 : ∀ a b : Fin 28, a.val + b.val ≤ 27 →
    Pass (mainBook (9:Fin 18)) (rescueBook (9:Fin 18))
      (seedWeight 133384 10) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 10 = 3890931 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill10

theorem counted10 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 27) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (9:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 27 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill10

theorem bill11 : ∀ a b : Fin 28, a.val + b.val ≤ 27 →
    Pass (mainBook (10:Fin 18)) (rescueBook (10:Fin 18))
      (seedWeight 133384 11) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 11 = 4280024 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill11

theorem counted11 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 27) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (10:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 27 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill11

theorem bill12 : ∀ a b : Fin 28, a.val + b.val ≤ 27 →
    Pass (mainBook (11:Fin 18)) (rescueBook (11:Fin 18))
      (seedWeight 133384 12) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 12 = 4669117 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill12

theorem counted12 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 27) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (11:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 27 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill12

theorem bill13 : ∀ a b : Fin 28, a.val + b.val ≤ 27 →
    Pass (mainBook (12:Fin 18)) (rescueBook (12:Fin 18))
      (seedWeight 133384 13) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 13 = 5058210 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill13

theorem counted13 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 27) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (12:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 27 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill13

theorem bill14 : ∀ a b : Fin 28, a.val + b.val ≤ 27 →
    Pass (mainBook (13:Fin 18)) (rescueBook (13:Fin 18))
      (seedWeight 133384 14) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 14 = 5447302 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill14

theorem counted14 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 27) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (13:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 27 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill14

theorem bill15 : ∀ a b : Fin 28, a.val + b.val ≤ 27 →
    Pass (mainBook (14:Fin 18)) (rescueBook (14:Fin 18))
      (seedWeight 133384 15) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 15 = 5836395 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill15

theorem counted15 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 27) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (14:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 27 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill15

theorem bill16 : ∀ a b : Fin 28, a.val + b.val ≤ 27 →
    Pass (mainBook (15:Fin 18)) (rescueBook (15:Fin 18))
      (seedWeight 133384 16) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 16 = 6225488 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill16

theorem counted16 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 27) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (15:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 27 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill16

theorem bill17 : ∀ a b : Fin 28, a.val + b.val ≤ 27 →
    Pass (mainBook (16:Fin 18)) (rescueBook (16:Fin 18))
      (seedWeight 133384 17) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 17 = 6614580 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill17

theorem counted17 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 27) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (16:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 27 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill17

theorem bill18 : ∀ a b : Fin 33, a.val + b.val ≤ 32 →
    Pass (mainBook (17:Fin 18)) (rescueBook (17:Fin 18))
      (seedWeight 133384 18) (ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val := by
  have x : seedWeight 133384 18 = 7003673 := by rw [seedWeight_eq]
  have y : ordWeight 133384 1 = 389100 := by rw [FastHeight.ordinate_eq _ _ (by decide)]; decide
  rw [x, y]
  exact _root_.Research6970.Height2313.Research6969.GradeArithmetic.bill18

theorem counted18 (r : _root_.Research6970.Height2313.Research6969.NormalRoute.Region) (grade : r.gradeHi ≤ 32) :
    _root_.Research6970.Height2313.Research6969.NormalRoute.Done (17:Fin 18) r := by
  apply _root_.Research6970.Height2313.Research6969.NormalRoute.small r 32 grade (by decide) (by decide +kernel) (by decide +kernel)
  exact bill18

end Research6970.Height2313.Research6969.ExtendedJointBills
