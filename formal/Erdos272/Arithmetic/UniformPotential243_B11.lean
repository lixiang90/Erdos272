import Erdos272.Arithmetic.UniformPotentialData208
namespace JSP233.UniformPotential208
open UniformQuery208 UniformEnvelope208 UniformSourceQueries208
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 65536
private theorem row243_176 : Facts243 176 := by decide +kernel

private theorem row243_177 : Facts243 177 := by decide +kernel

private theorem row243_178 : Facts243 178 := by decide +kernel

private theorem row243_179 : Facts243 179 := by decide +kernel

private theorem row243_180 : Facts243 180 := by decide +kernel

private theorem row243_181 : Facts243 181 := by decide +kernel

private theorem row243_182 : Facts243 182 := by decide +kernel

private theorem row243_183 : Facts243 183 := by decide +kernel

theorem facts243_B11 : ∀ i : Fin 8,Facts243 (176+i.val) := by
  exact (Fin.cases row243_176 (Fin.cases row243_177 (Fin.cases row243_178 (Fin.cases row243_179 (Fin.cases row243_180 (Fin.cases row243_181 (Fin.cases row243_182 (Fin.cases row243_183 (fun i => Fin.elim0 i)))))))))
#print axioms facts243_B11
end JSP233.UniformPotential208
