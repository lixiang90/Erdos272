module

public import Erdos272.Counting.N82427.CorrelatedChord82427

@[expose] public section

namespace JSP233.CorrelatedChecks65172
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def plan004 : CorrelatedChord82427.Plan := ⟨78,9,12393,10⟩

theorem checked004 : CorrelatedChord82427.Conditions plan004 := by decide +kernel
#print axioms checked004

def plan007 : CorrelatedChord82427.Plan := ⟨78,15,17265,16⟩

theorem checked007 : CorrelatedChord82427.Conditions plan007 := by decide +kernel
#print axioms checked007

end
end JSP233.CorrelatedChecks65172
