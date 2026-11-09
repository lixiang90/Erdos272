module

public import Erdos272.Arithmetic.CleanupEval208

@[expose] public section
namespace JSP233.CleanupPilot208
open CleanupEval208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
def row : Row := ⟨1000000000000,659000,705097,100,[⟨242,100,338,71,95,118,126,133⟩,⟨338,79,484,181,220,240,246,252⟩,⟨484,63,726,359,390,406,411,415⟩,⟨726,51,1210,625,650,663,667,670⟩,⟨1210,39,2420,1133,1152,1162,1165,1168⟩,⟨2420,28,7744,2365,2379,2386,2388,2390⟩,⟨7744,16,247808,7713,7721,7725,7726,7727⟩]⟩
def expected : Totals := ⟨1180973943199638,746282249342,9877449482966,1171842775966014,1880399973⟩
theorem checked : checkChunk row 1 128 expected=true := by decide +kernel
theorem facts : ChunkFacts row 1 128 expected := check_sound checked
#print axioms checked
#print axioms facts
end JSP233.CleanupPilot208
