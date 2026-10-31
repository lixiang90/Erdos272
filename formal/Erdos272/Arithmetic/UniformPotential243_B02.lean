import Erdos272.Arithmetic.UniformPotentialData208
namespace JSP233.UniformPotential208
open UniformQuery208 UniformEnvelope208 UniformSourceQueries208
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 65536
private theorem row243_32 : Facts243 32 := by decide +kernel

private theorem row243_33 : Facts243 33 := by decide +kernel

private theorem row243_34 : Facts243 34 := by decide +kernel

private theorem row243_35 : Facts243 35 := by decide +kernel

private theorem row243_36 : Facts243 36 := by decide +kernel

private theorem row243_37 : Facts243 37 := by decide +kernel

private theorem row243_38 : Facts243 38 := by decide +kernel

private theorem row243_39 : Facts243 39 := by decide +kernel

private theorem row243_40 : Facts243 40 := by decide +kernel

private theorem row243_41 : Facts243 41 := by decide +kernel

private theorem row243_42 : Facts243 42 := by decide +kernel

private theorem row243_43 : Facts243 43 := by decide +kernel

private theorem row243_44 : Facts243 44 := by decide +kernel

private theorem row243_45 : Facts243 45 := by decide +kernel

private theorem row243_46 : Facts243 46 := by decide +kernel

private theorem row243_47 : Facts243 47 := by decide +kernel

theorem facts243_B02 : ∀ i : Fin 16,Facts243 (32+i.val) := by
  exact (Fin.cases row243_32 (Fin.cases row243_33 (Fin.cases row243_34 (Fin.cases row243_35 (Fin.cases row243_36 (Fin.cases row243_37 (Fin.cases row243_38 (Fin.cases row243_39 (Fin.cases row243_40 (Fin.cases row243_41 (Fin.cases row243_42 (Fin.cases row243_43 (Fin.cases row243_44 (Fin.cases row243_45 (Fin.cases row243_46 (Fin.cases row243_47 (fun i => Fin.elim0 i)))))))))))))))))
#print axioms facts243_B02
end JSP233.UniformPotential208
