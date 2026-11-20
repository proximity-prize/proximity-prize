/- Apache-2.0. Bome2017. Physical formulas are those of Lucieno, BitWonka and the 68.33 accepted construction. -/
import ProximityPrize.SubmissionLower.Night6836PureSteps
namespace Koala6836.PureOffers
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem e0 : rowOK 16 0=true := by decide +kernel
private theorem e1 : rowOK 16 1=true := by decide +kernel
private theorem e2 : rowOK 16 2=true := by decide +kernel
private theorem e3 : rowOK 16 3=true := by decide +kernel
private theorem e4 : rowOK 16 4=true := by decide +kernel
private theorem e5 : rowOK 16 5=true := by decide +kernel
private theorem e6 : rowOK 16 6=true := by decide +kernel
private theorem e7 : rowOK 16 7=true := by decide +kernel
private theorem e8 : rowOK 16 8=true := by decide +kernel
private theorem e9 : rowOK 16 9=true := by decide +kernel
private theorem e10 : rowOK 16 10=true := by decide +kernel
private theorem e11 : rowOK 16 11=true := by decide +kernel
private theorem e12 : rowOK 16 12=true := by decide +kernel
private theorem e13 : rowOK 16 13=true := by decide +kernel
private theorem e14 : rowOK 16 14=true := by decide +kernel
private theorem e15 : rowOK 16 15=true := by decide +kernel
private theorem e16 : rowOK 16 16=true := by decide +kernel
private theorem e17 : rowOK 16 17=true := by decide +kernel
private theorem e18 : rowOK 16 18=true := by decide +kernel
private theorem e19 : rowOK 16 19=true := by decide +kernel
private theorem e20 : rowOK 16 20=true := by decide +kernel
private theorem e21 : rowOK 16 21=true := by decide +kernel
private theorem e22 : rowOK 16 22=true := by decide +kernel
private theorem e23 : rowOK 16 23=true := by decide +kernel
private theorem e24 : rowOK 16 24=true := by decide +kernel
private theorem e25 : rowOK 16 25=true := by decide +kernel
private theorem e26 : rowOK 16 26=true := by decide +kernel
private theorem e27 : rowOK 16 27=true := by decide +kernel
private theorem e28 : rowOK 16 28=true := by decide +kernel
private theorem e29 : rowOK 16 29=true := by decide +kernel
private theorem e30 : rowOK 16 30=true := by decide +kernel
private theorem e31 : rowOK 16 31=true := by decide +kernel
private theorem e32 : rowOK 16 32=true := by decide +kernel
private theorem e33 : rowOK 16 33=true := by decide +kernel
private theorem e34 : rowOK 16 34=true := by decide +kernel
private theorem e35 : rowOK 16 35=true := by decide +kernel
private theorem e36 : rowOK 16 36=true := by decide +kernel
private theorem e37 : rowOK 16 37=true := by decide +kernel
private theorem e38 : rowOK 16 38=true := by decide +kernel
private theorem e39 : rowOK 16 39=true := by decide +kernel
private theorem e40 : rowOK 16 40=true := by decide +kernel
private theorem e41 : rowOK 16 41=true := by decide +kernel
private theorem e42 : rowOK 16 42=true := by decide +kernel
private theorem e43 : rowOK 16 43=true := by decide +kernel
private theorem e44 : rowOK 16 44=true := by decide +kernel
private theorem e45 : rowOK 16 45=true := by decide +kernel
private theorem e46 : rowOK 16 46=true := by decide +kernel
private theorem e47 : rowOK 16 47=true := by decide +kernel
private theorem e48 : rowOK 16 48=true := by decide +kernel
private theorem e49 : rowOK 16 49=true := by decide +kernel
private theorem e50 : rowOK 16 50=true := by decide +kernel
private theorem e51 : rowOK 16 51=true := by decide +kernel
private theorem e52 : rowOK 16 52=true := by decide +kernel
private theorem e53 : rowOK 16 53=true := by decide +kernel
private theorem e54 : rowOK 16 54=true := by decide +kernel
private theorem e55 : rowOK 16 55=true := by decide +kernel
private theorem e56 : rowOK 16 56=true := by decide +kernel
private theorem e57 : rowOK 16 57=true := by decide +kernel
private theorem e58 : rowOK 16 58=true := by decide +kernel
private theorem e59 : rowOK 16 59=true := by decide +kernel
private theorem e60 : rowOK 16 60=true := by decide +kernel
private theorem upto12 : ∀e,e<12→rowOK 16 e=true := advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (empty) e0) e1) e2) e3) e4) e5) e6) e7) e8) e9) e10) e11
private theorem upto24 : ∀e,e<24→rowOK 16 e=true := advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (upto12) e12) e13) e14) e15) e16) e17) e18) e19) e20) e21) e22) e23
private theorem upto36 : ∀e,e<36→rowOK 16 e=true := advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (upto24) e24) e25) e26) e27) e28) e29) e30) e31) e32) e33) e34) e35
private theorem upto48 : ∀e,e<48→rowOK 16 e=true := advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (upto36) e36) e37) e38) e39) e40) e41) e42) e43) e44) e45) e46) e47
private theorem upto60 : ∀e,e<60→rowOK 16 e=true := advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (upto48) e48) e49) e50) e51) e52) e53) e54) e55) e56) e57) e58) e59
private theorem upto61 : ∀e,e<61→rowOK 16 e=true := advance (upto60) e60
theorem ok16 : ∀e,e<61→rowOK 16 e=true := upto61
end Koala6836.PureOffers
