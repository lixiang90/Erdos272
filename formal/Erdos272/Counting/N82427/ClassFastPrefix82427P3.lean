module

public import Erdos272.Arithmetic.N82427.ClassFastNumeric82427

@[expose] public section

namespace JSP233.ClassFastPrefix82427P3
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem correct : ClassFastNumeric82427.PrefixFacts 3 := by decide +kernel

#print axioms correct
end JSP233.ClassFastPrefix82427P3
