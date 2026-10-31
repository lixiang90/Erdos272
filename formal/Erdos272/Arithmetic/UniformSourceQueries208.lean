import Erdos272.Arithmetic.UniformSourceQueries208_B00
import Erdos272.Arithmetic.UniformSourceQueries208_B01
import Erdos272.Arithmetic.UniformSourceQueries208_B02
import Erdos272.Arithmetic.UniformSourceQueries208_B03
import Erdos272.Arithmetic.UniformSourceQueries208_B04
import Erdos272.Arithmetic.UniformSourceQueries208_B05
import Erdos272.Arithmetic.UniformSourceQueries208_B06

namespace JSP233.UniformSourceQueries208
open UniformQuery208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
def queries : List Query := UniformSourceQueries208_B00.queries ++ UniformSourceQueries208_B01.queries ++ UniformSourceQueries208_B02.queries ++ UniformSourceQueries208_B03.queries ++ UniformSourceQueries208_B04.queries ++ UniformSourceQueries208_B05.queries ++ UniformSourceQueries208_B06.queries
theorem checked : checkAll queries=true := by
  simp only [queries,checkAll,List.all_append,Bool.and_eq_true_iff]
  exact ⟨⟨⟨⟨⟨⟨UniformSourceQueries208_B00.checked,UniformSourceQueries208_B01.checked⟩,UniformSourceQueries208_B02.checked⟩,UniformSourceQueries208_B03.checked⟩,UniformSourceQueries208_B04.checked⟩,UniformSourceQueries208_B05.checked⟩,UniformSourceQueries208_B06.checked⟩
theorem query_sound {a : Query} (ha : a∈queries) : UniformEnvelope208.Decision (a.M : ℝ) a.T a.z a.q := checkAll_sound checked ha
#print axioms checked
#print axioms query_sound
end JSP233.UniformSourceQueries208
