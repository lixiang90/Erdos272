module

public import Erdos272.Resources.BandCredit208

@[expose] public section

namespace JSP233.PhaseDefs82427
open ShiftedBlocks208 BandLabels208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- The coordinates are `(block, phase)`, with phase in `Icc 1 d`. -/
def Cap (N d E B V : ℕ) (i : ℕ × ℕ) : ℕ :=
  min V ((N-i.2)/d-i.1*B+E)

def Price (N d T E B V : ℕ) : ℕ :=
  ∑ i ∈ LightPhases208.Indices N d (T-E) B, Cap N d E B V i

def Heavy (N d B U E : ℕ) (F : Finset (Finset ℤ)) (start : Finset ℤ → ℕ) :
    Finset (ℕ × ℕ) :=
  (F.image (fun S => Code d B (start S))).filter (fun q =>
    Cap N d E B (U+B-3) (Swap q) < (BandSystem208.Fiber F d B start q).card)

end
end JSP233.PhaseDefs82427
