/- Apache-2.0. Bome2017. Physical formulas are those of Lucieno, BitWonka and the 68.33 accepted construction. -/
import ProximityPrize.SubmissionLower.Night6836PureSteps
namespace Koala6836.PureOffers
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem e0 : rowOK 13 0=true := by decide +kernel
private theorem e1 : rowOK 13 1=true := by decide +kernel
private theorem e2 : rowOK 13 2=true := by decide +kernel
private theorem e3 : rowOK 13 3=true := by decide +kernel
private theorem e4 : rowOK 13 4=true := by decide +kernel
private theorem e5 : rowOK 13 5=true := by decide +kernel
private theorem e6 : rowOK 13 6=true := by decide +kernel
private theorem e7 : rowOK 13 7=true := by decide +kernel
private theorem e8 : rowOK 13 8=true := by decide +kernel
private theorem e9 : rowOK 13 9=true := by decide +kernel
private theorem e10 : rowOK 13 10=true := by decide +kernel
private theorem e11 : rowOK 13 11=true := by decide +kernel
private theorem e12 : rowOK 13 12=true := by decide +kernel
private theorem e13 : rowOK 13 13=true := by decide +kernel
private theorem e14 : rowOK 13 14=true := by decide +kernel
private theorem e15 : rowOK 13 15=true := by decide +kernel
private theorem e16 : rowOK 13 16=true := by decide +kernel
private theorem e17 : rowOK 13 17=true := by decide +kernel
private theorem e18 : rowOK 13 18=true := by decide +kernel
private theorem e19 : rowOK 13 19=true := by decide +kernel
private theorem e20 : rowOK 13 20=true := by decide +kernel
private theorem e21 : rowOK 13 21=true := by decide +kernel
private theorem e22 : rowOK 13 22=true := by decide +kernel
private theorem e23 : rowOK 13 23=true := by decide +kernel
private theorem e24 : rowOK 13 24=true := by decide +kernel
private theorem e25 : rowOK 13 25=true := by decide +kernel
private theorem e26 : rowOK 13 26=true := by decide +kernel
private theorem e27 : rowOK 13 27=true := by decide +kernel
private theorem e28 : rowOK 13 28=true := by decide +kernel
private theorem e29 : rowOK 13 29=true := by decide +kernel
private theorem e30 : rowOK 13 30=true := by decide +kernel
private theorem e31 : rowOK 13 31=true := by decide +kernel
private theorem e32 : rowOK 13 32=true := by decide +kernel
private theorem e33 : rowOK 13 33=true := by decide +kernel
private theorem e34 : rowOK 13 34=true := by decide +kernel
private theorem e35 : rowOK 13 35=true := by decide +kernel
private theorem e36 : rowOK 13 36=true := by decide +kernel
private theorem e37 : rowOK 13 37=true := by decide +kernel
private theorem e38 : rowOK 13 38=true := by decide +kernel
private theorem e39 : rowOK 13 39=true := by decide +kernel
private theorem e40 : rowOK 13 40=true := by decide +kernel
private theorem e41 : rowOK 13 41=true := by decide +kernel
private theorem e42 : rowOK 13 42=true := by decide +kernel
private theorem e43 : rowOK 13 43=true := by decide +kernel
private theorem e44 : rowOK 13 44=true := by decide +kernel
private theorem e45 : rowOK 13 45=true := by decide +kernel
private theorem e46 : rowOK 13 46=true := by decide +kernel
private theorem e47 : rowOK 13 47=true := by decide +kernel
private theorem e48 : rowOK 13 48=true := by decide +kernel
private theorem e49 : rowOK 13 49=true := by decide +kernel
private theorem e50 : rowOK 13 50=true := by decide +kernel
private theorem e51 : rowOK 13 51=true := by decide +kernel
private theorem e52 : rowOK 13 52=true := by decide +kernel
private theorem e53 : rowOK 13 53=true := by decide +kernel
private theorem e54 : rowOK 13 54=true := by decide +kernel
private theorem e55 : rowOK 13 55=true := by decide +kernel
private theorem e56 : rowOK 13 56=true := by decide +kernel
private theorem e57 : rowOK 13 57=true := by decide +kernel
private theorem e58 : rowOK 13 58=true := by decide +kernel
private theorem e59 : rowOK 13 59=true := by decide +kernel
private theorem e60 : rowOK 13 60=true := by decide +kernel
private theorem e61 : rowOK 13 61=true := by decide +kernel
private theorem e62 : rowOK 13 62=true := by decide +kernel
private theorem e63 : rowOK 13 63=true := by decide +kernel
private theorem upto12 : ∀e,e<12→rowOK 13 e=true := advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (empty) e0) e1) e2) e3) e4) e5) e6) e7) e8) e9) e10) e11
private theorem upto24 : ∀e,e<24→rowOK 13 e=true := advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (upto12) e12) e13) e14) e15) e16) e17) e18) e19) e20) e21) e22) e23
private theorem upto36 : ∀e,e<36→rowOK 13 e=true := advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (upto24) e24) e25) e26) e27) e28) e29) e30) e31) e32) e33) e34) e35
private theorem upto48 : ∀e,e<48→rowOK 13 e=true := advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (upto36) e36) e37) e38) e39) e40) e41) e42) e43) e44) e45) e46) e47
private theorem upto60 : ∀e,e<60→rowOK 13 e=true := advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (advance (upto48) e48) e49) e50) e51) e52) e53) e54) e55) e56) e57) e58) e59
private theorem upto64 : ∀e,e<64→rowOK 13 e=true := advance (advance (advance (advance (upto60) e60) e61) e62) e63
theorem ok13 : ∀e,e<64→rowOK 13 e=true := upto64
end Koala6836.PureOffers
