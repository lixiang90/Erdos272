import Erdos272.Arithmetic.UniformDecision208

namespace JSP233.UniformQuery208
open UniformDecision208 UniformEnvelope208
set_option maxHeartbeats 0
structure Query where
  M : ℕ
  T : ℕ
  z : ℕ
  q : ℚ
  deriving DecidableEq, Repr
def valid (a : Query) : Bool := check a.M a.T a.z a.q
def checkAll (as : List Query) : Bool := as.all valid
theorem checkAll_sound {as : List Query} (hc : checkAll as=true) {a : Query} (ha : a∈as) :
    Decision (a.M : ℝ) a.T a.z a.q := by
  have hv : valid a=true := List.all_eq_true.mp hc a ha
  simpa only [Rat.cast_natCast] using check_sound hv
#print axioms checkAll_sound
end JSP233.UniformQuery208
