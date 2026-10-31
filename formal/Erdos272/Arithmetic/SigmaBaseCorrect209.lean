import Erdos272.Arithmetic.SigmaBaseBlock209_00002
import Erdos272.Arithmetic.SigmaBaseBlock209_04098
import Erdos272.Arithmetic.SigmaBaseBlock209_08194
import Erdos272.Arithmetic.SigmaBaseBlock209_12290
import Erdos272.Arithmetic.SigmaBaseBlock209_16386
import Erdos272.Arithmetic.SigmaBaseBlock209_20482
import Erdos272.Arithmetic.SigmaBaseBlock209_24578
import Erdos272.Arithmetic.SigmaBaseBlock209_28674
namespace JSP233.SigmaBaseCorrect209
set_option maxHeartbeats 0
theorem step (n : Nat) (hn : 2≤n) (hnH : n≤32753) :
    SigmaSieve209.Step SigmaBaseData209.value FactorFullData209.factor n := by
  by_cases h_2 : n<4098
  · have hh := @ComputedSigma209.checkSteps_sound SigmaBaseData209.value FactorFullData209.factor 2 4096 n SigmaBaseBlock209_00002.checked (by omega) h_2
    exact hh
  by_cases h_4098 : n<8194
  · have hh := @ComputedSigma209.checkSteps_sound SigmaBaseData209.value FastFullLookup209.factor 4098 4096 n SigmaBaseBlock209_04098.checked (by omega) h_4098
    simpa only [SigmaSieve209.Step,FastFullLookup209.factor_eq] using hh
  by_cases h_8194 : n<12290
  · have hh := @ComputedSigma209.checkSteps_sound SigmaBaseData209.value FastFullLookup209.factor 8194 4096 n SigmaBaseBlock209_08194.checked (by omega) h_8194
    simpa only [SigmaSieve209.Step,FastFullLookup209.factor_eq] using hh
  by_cases h_12290 : n<16386
  · have hh := @ComputedSigma209.checkSteps_sound SigmaBaseData209.value FastFullLookup209.factor 12290 4096 n SigmaBaseBlock209_12290.checked (by omega) h_12290
    simpa only [SigmaSieve209.Step,FastFullLookup209.factor_eq] using hh
  by_cases h_16386 : n<20482
  · have hh := @ComputedSigma209.checkSteps_sound SigmaBaseData209.value FastFullLookup209.factor 16386 4096 n SigmaBaseBlock209_16386.checked (by omega) h_16386
    simpa only [SigmaSieve209.Step,FastFullLookup209.factor_eq] using hh
  by_cases h_20482 : n<24578
  · have hh := @ComputedSigma209.checkSteps_sound SigmaBaseData209.value FastFullLookup209.factor 20482 4096 n SigmaBaseBlock209_20482.checked (by omega) h_20482
    simpa only [SigmaSieve209.Step,FastFullLookup209.factor_eq] using hh
  by_cases h_24578 : n<28674
  · have hh := @ComputedSigma209.checkSteps_sound SigmaBaseData209.value FastFullLookup209.factor 24578 4096 n SigmaBaseBlock209_24578.checked (by omega) h_24578
    simpa only [SigmaSieve209.Step,FastFullLookup209.factor_eq] using hh
  by_cases h_28674 : n<32754
  · have hh := @ComputedSigma209.checkSteps_sound SigmaBaseData209.value FastFullLookup209.factor 28674 4080 n SigmaBaseBlock209_28674.checked (by omega) h_28674
    simpa only [SigmaSieve209.Step,FastFullLookup209.factor_eq] using hh
  omega

theorem correct
    (hfactor : ∀ n,2≤n → n≤32753 →
      (FactorFullData209.factor n=0 → n.Prime) ∧
      (FactorFullData209.factor n≠0 → (FactorFullData209.factor n).Prime ∧ FactorFullData209.factor n∣n))
    (n : Nat) (hn : n≤32753) : SigmaBaseData209.value n=SigmaSieve209.sigmaOne n :=
  SigmaSieve209.correct SigmaBaseData209.zero SigmaBaseData209.one hfactor step n hn
#print axioms step
#print axioms correct
end JSP233.SigmaBaseCorrect209
