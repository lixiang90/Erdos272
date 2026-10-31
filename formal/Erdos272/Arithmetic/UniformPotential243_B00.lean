import Erdos272.Arithmetic.UniformPotentialData208
namespace JSP233.UniformPotential208
open UniformQuery208 UniformEnvelope208 UniformSourceQueries208
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 65536
private theorem row243_0 : Facts243 0 := by decide +kernel

private theorem row243_1 : Facts243 1 := by decide +kernel

private theorem row243_2 : Facts243 2 := by decide +kernel

private theorem row243_3 : Facts243 3 := by decide +kernel

private theorem row243_4 : Facts243 4 := by decide +kernel

private theorem row243_5 : Facts243 5 := by decide +kernel

private theorem row243_6 : Facts243 6 := by decide +kernel

private theorem row243_7 : Facts243 7 := by decide +kernel

private theorem row243_8 : Facts243 8 := by decide +kernel

private theorem row243_9 : Facts243 9 := by decide +kernel

private theorem row243_10 : Facts243 10 := by decide +kernel

private theorem row243_11 : Facts243 11 := by decide +kernel

private theorem row243_12 : Facts243 12 := by decide +kernel

private theorem row243_13 : Facts243 13 := by decide +kernel

private theorem row243_14 : Facts243 14 := by decide +kernel

private theorem row243_15 : Facts243 15 := by decide +kernel

theorem facts243_B00 : ∀ i : Fin 16,Facts243 (0+i.val) := by
  exact (Fin.cases row243_0 (Fin.cases row243_1 (Fin.cases row243_2 (Fin.cases row243_3 (Fin.cases row243_4 (Fin.cases row243_5 (Fin.cases row243_6 (Fin.cases row243_7 (Fin.cases row243_8 (Fin.cases row243_9 (Fin.cases row243_10 (Fin.cases row243_11 (Fin.cases row243_12 (Fin.cases row243_13 (Fin.cases row243_14 (Fin.cases row243_15 (fun i => Fin.elim0 i)))))))))))))))))
#print axioms facts243_B00
end JSP233.UniformPotential208
