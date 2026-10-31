import Erdos272.Arithmetic.UniformPotentialData208
namespace JSP233.UniformPotential208
open UniformQuery208 UniformEnvelope208 UniformSourceQueries208
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 65536
private theorem row243_128 : Facts243 128 := by decide +kernel

private theorem row243_129 : Facts243 129 := by decide +kernel

private theorem row243_130 : Facts243 130 := by decide +kernel

private theorem row243_131 : Facts243 131 := by decide +kernel

private theorem row243_132 : Facts243 132 := by decide +kernel

private theorem row243_133 : Facts243 133 := by decide +kernel

private theorem row243_134 : Facts243 134 := by decide +kernel

private theorem row243_135 : Facts243 135 := by decide +kernel

private theorem row243_136 : Facts243 136 := by decide +kernel

private theorem row243_137 : Facts243 137 := by decide +kernel

private theorem row243_138 : Facts243 138 := by decide +kernel

private theorem row243_139 : Facts243 139 := by decide +kernel

private theorem row243_140 : Facts243 140 := by decide +kernel

private theorem row243_141 : Facts243 141 := by decide +kernel

private theorem row243_142 : Facts243 142 := by decide +kernel

private theorem row243_143 : Facts243 143 := by decide +kernel

theorem facts243_B08 : ∀ i : Fin 16,Facts243 (128+i.val) := by
  exact (Fin.cases row243_128 (Fin.cases row243_129 (Fin.cases row243_130 (Fin.cases row243_131 (Fin.cases row243_132 (Fin.cases row243_133 (Fin.cases row243_134 (Fin.cases row243_135 (Fin.cases row243_136 (Fin.cases row243_137 (Fin.cases row243_138 (Fin.cases row243_139 (Fin.cases row243_140 (Fin.cases row243_141 (Fin.cases row243_142 (Fin.cases row243_143 (fun i => Fin.elim0 i)))))))))))))))))
#print axioms facts243_B08
end JSP233.UniformPotential208
