module

public import Erdos272.Certificates.SigmaSteps209
public import Erdos272.Arithmetic.SigmaBaseData209

@[expose] public section
namespace JSP233.SigmaBaseBlock209_00002
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem chunk_2 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 2 256=true := by decide +kernel

private theorem chunk_258 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 258 256=true := by decide +kernel

private theorem chunk_514 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 514 256=true := by decide +kernel

private theorem chunk_770 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 770 256=true := by decide +kernel

private theorem chunk_1026 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 1026 256=true := by decide +kernel

private theorem chunk_1282 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 1282 256=true := by decide +kernel

private theorem chunk_1538 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 1538 256=true := by decide +kernel

private theorem chunk_1794 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 1794 256=true := by decide +kernel

private theorem chunk_2050 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 2050 256=true := by decide +kernel

private theorem chunk_2306 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 2306 256=true := by decide +kernel

private theorem chunk_2562 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 2562 256=true := by decide +kernel

private theorem chunk_2818 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 2818 256=true := by decide +kernel

private theorem chunk_3074 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 3074 256=true := by decide +kernel

private theorem chunk_3330 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 3330 256=true := by decide +kernel

private theorem chunk_3586 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 3586 256=true := by decide +kernel

private theorem chunk_3842 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 3842 256=true := by decide +kernel

theorem checked : ComputedSigma209.checkSteps SigmaBaseData209.value FactorFullData209.factor 2 4096=true := by
  exact (SigmaSteps209.fast_factor_checked (SigmaSteps209.checked_append chunk_2 (SigmaSteps209.checked_append chunk_258 (SigmaSteps209.checked_append chunk_514 (SigmaSteps209.checked_append chunk_770 (SigmaSteps209.checked_append chunk_1026 (SigmaSteps209.checked_append chunk_1282 (SigmaSteps209.checked_append chunk_1538 (SigmaSteps209.checked_append chunk_1794 (SigmaSteps209.checked_append chunk_2050 (SigmaSteps209.checked_append chunk_2306 (SigmaSteps209.checked_append chunk_2562 (SigmaSteps209.checked_append chunk_2818 (SigmaSteps209.checked_append chunk_3074 (SigmaSteps209.checked_append chunk_3330 (SigmaSteps209.checked_append chunk_3586 chunk_3842))))))))))))))))
#print axioms checked
end JSP233.SigmaBaseBlock209_00002
