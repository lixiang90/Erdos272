module

public import Erdos272.Counting.N80470.StrictRunFiveContracts80470

@[expose] public section

namespace JSP233.SourceStrictRunContracts80470
open SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def run (i : ℕ) (_hi : i < 5) : CertifiedContract :=
  match i with
  | 0 => StrictRunFiveContracts80470.run00
  | 1 => StrictRunFiveContracts80470.run01
  | 2 => StrictRunFiveContracts80470.run02
  | 3 => StrictRunFiveContracts80470.run03
  | 4 => StrictRunFiveContracts80470.run04
  | _ => StrictRunFiveContracts80470.run00

end
end JSP233.SourceStrictRunContracts80470
