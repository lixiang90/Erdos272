module

public import Erdos272.Arithmetic.LowFactorSound209
public import Erdos272.Arithmetic.SigmaBaseCorrect209

@[expose] public section
namespace JSP233.SigmaBaseActual209
set_option maxHeartbeats 0

theorem correct (n : Nat) (hn : n≤32753) :
    SigmaBaseData209.value n=SigmaSieve209.sigmaOne n :=
  SigmaBaseCorrect209.correct LowFactorSound209.sound n hn
#print axioms correct
end JSP233.SigmaBaseActual209
