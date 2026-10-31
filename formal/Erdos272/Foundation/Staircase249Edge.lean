import Erdos272.Foundation.Staircase249Data

namespace JSP233.Staircase249Data
open JSP233.StaircaseCertificate
open JSP233.Staircase249Counts
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem leftCertificate : LeftCertificate 250 Left := by constructor <;> decide
theorem base : ∀ h : Fin 251, Score 0 h ≤ Potential 0 h := by decide
theorem terminal : ∀ h : Fin 251, Potential 249 h ≤ 1 := by decide

#print axioms leftCertificate
#print axioms base
#print axioms terminal
end JSP233.Staircase249Data
