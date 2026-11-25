module

public import Erdos272.Core.N82427.ClassFastCore82427
public import Erdos272.Counting.N82427.ClassFastPrefix82427P2
public import Erdos272.Counting.N82427.ClassFastPrefix82427P3
public import Erdos272.Counting.N82427.ClassFastPrefix82427P5
public import Erdos272.Counting.N82427.ClassFastPrefix82427P7
public import Erdos272.Counting.N82427.ClassFastPrefix82427P11

@[expose] public section

namespace JSP233.ClassFast82427
set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev check := ClassFastNumeric82427.check

theorem sound {p n b : ℕ} (hp : p∈({2,3,5,7,11} : Finset ℕ))
    (hc : check p n b=true) : ClassCount158375.Certificate p n b := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ClassFastCore82427.sound ClassFastPrefix82427P2.correct hc
  · exact ClassFastCore82427.sound ClassFastPrefix82427P3.correct hc
  · exact ClassFastCore82427.sound ClassFastPrefix82427P5.correct hc
  · exact ClassFastCore82427.sound ClassFastPrefix82427P7.correct hc
  · exact ClassFastCore82427.sound ClassFastPrefix82427P11.correct hc

#print axioms sound
end JSP233.ClassFast82427
