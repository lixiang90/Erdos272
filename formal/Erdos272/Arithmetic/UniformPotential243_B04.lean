import Erdos272.Arithmetic.UniformPotentialData208
namespace JSP233.UniformPotential208
open UniformQuery208 UniformEnvelope208 UniformSourceQueries208
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 65536
private theorem row243_64 : Facts243 64 := by decide +kernel

private theorem row243_65 : Facts243 65 := by decide +kernel

private theorem row243_66 : Facts243 66 := by decide +kernel

private theorem row243_67 : Facts243 67 := by decide +kernel

private theorem row243_68 : Facts243 68 := by decide +kernel

private theorem row243_69 : Facts243 69 := by decide +kernel

private theorem row243_70 : Facts243 70 := by decide +kernel

private theorem row243_71 : Facts243 71 := by decide +kernel

private theorem row243_72 : Facts243 72 := by decide +kernel

private theorem row243_73 : Facts243 73 := by decide +kernel

private theorem row243_74 : Facts243 74 := by decide +kernel

private theorem row243_75 : Facts243 75 := by decide +kernel

private theorem row243_76 : Facts243 76 := by decide +kernel

private theorem row243_77 : Facts243 77 := by decide +kernel

private theorem row243_78 : Facts243 78 := by decide +kernel

private theorem row243_79 : Facts243 79 := by decide +kernel

theorem facts243_B04 : ∀ i : Fin 16,Facts243 (64+i.val) := by
  exact (Fin.cases row243_64 (Fin.cases row243_65 (Fin.cases row243_66 (Fin.cases row243_67 (Fin.cases row243_68 (Fin.cases row243_69 (Fin.cases row243_70 (Fin.cases row243_71 (Fin.cases row243_72 (Fin.cases row243_73 (Fin.cases row243_74 (Fin.cases row243_75 (Fin.cases row243_76 (Fin.cases row243_77 (Fin.cases row243_78 (Fin.cases row243_79 (fun i => Fin.elim0 i)))))))))))))))))
#print axioms facts243_B04
end JSP233.UniformPotential208
