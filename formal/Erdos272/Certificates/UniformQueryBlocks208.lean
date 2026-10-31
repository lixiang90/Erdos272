import Erdos272.Arithmetic.UniformQuery208

namespace JSP233.UniformQueryBlocks208
open UniformQuery208
set_option Elab.async false

theorem checked_append {xs ys : List Query}
    (hx : checkAll xs = true) (hy : checkAll ys = true) :
    checkAll (xs ++ ys) = true := by
  simpa only [checkAll, List.all_append, Bool.and_eq_true_iff] using And.intro hx hy

#print axioms checked_append
end JSP233.UniformQueryBlocks208
