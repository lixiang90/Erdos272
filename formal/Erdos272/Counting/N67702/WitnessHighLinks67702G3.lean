module

public import Erdos272.Arithmetic.N67702.WitnessHighSoundData67702

@[expose] public section

namespace JSP233.WitnessHighLinks67702G3
open WitnessHighSoundData67702
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem links {k : ℕ} (hlo : 24 ≤ k) (hhi : k < 32) : Links k (by omega) := by
  interval_cases k <;> refine ⟨rfl,rfl,?_⟩ <;> intro b <;> fin_cases b <;> rfl
#print axioms links
end
end JSP233.WitnessHighLinks67702G3
