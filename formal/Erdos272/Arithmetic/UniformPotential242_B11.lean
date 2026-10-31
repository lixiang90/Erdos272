import Erdos272.Arithmetic.UniformPotentialData208
namespace JSP233.UniformPotential208
open UniformQuery208 UniformEnvelope208 UniformSourceQueries208
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 65536
private theorem row242_176 : Facts242 176 := by decide +kernel

private theorem row242_177 : Facts242 177 := by decide +kernel

private theorem row242_178 : Facts242 178 := by decide +kernel

private theorem row242_179 : Facts242 179 := by decide +kernel

private theorem row242_180 : Facts242 180 := by decide +kernel

private theorem row242_181 : Facts242 181 := by decide +kernel

private theorem row242_182 : Facts242 182 := by decide +kernel

theorem facts242_B11 : ∀ i : Fin 7,Facts242 (176+i.val) := by
  exact (Fin.cases row242_176 (Fin.cases row242_177 (Fin.cases row242_178 (Fin.cases row242_179 (Fin.cases row242_180 (Fin.cases row242_181 (Fin.cases row242_182 (fun i => Fin.elim0 i))))))))
#print axioms facts242_B11
end JSP233.UniformPotential208
