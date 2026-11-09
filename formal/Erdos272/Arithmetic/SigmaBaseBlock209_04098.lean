module

public import Erdos272.Certificates.SigmaSteps209
public import Erdos272.Arithmetic.SigmaBaseData209
public import Erdos272.Arithmetic.FastFullLookup209

@[expose] public section
namespace JSP233.SigmaBaseBlock209_04098
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem chunk_4098 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 4098 256=true := by decide +kernel

private theorem chunk_4354 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 4354 256=true := by decide +kernel

private theorem chunk_4610 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 4610 256=true := by decide +kernel

private theorem chunk_4866 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 4866 256=true := by decide +kernel

private theorem chunk_5122 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 5122 256=true := by decide +kernel

private theorem chunk_5378 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 5378 256=true := by decide +kernel

private theorem chunk_5634 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 5634 256=true := by decide +kernel

private theorem chunk_5890 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 5890 256=true := by decide +kernel

private theorem chunk_6146 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 6146 256=true := by decide +kernel

private theorem chunk_6402 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 6402 256=true := by decide +kernel

private theorem chunk_6658 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 6658 256=true := by decide +kernel

private theorem chunk_6914 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 6914 256=true := by decide +kernel

private theorem chunk_7170 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 7170 256=true := by decide +kernel

private theorem chunk_7426 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 7426 256=true := by decide +kernel

private theorem chunk_7682 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 7682 256=true := by decide +kernel

private theorem chunk_7938 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 7938 256=true := by decide +kernel

theorem checked : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 4098 4096=true := by
  exact (SigmaSteps209.checked_append chunk_4098 (SigmaSteps209.checked_append chunk_4354 (SigmaSteps209.checked_append chunk_4610 (SigmaSteps209.checked_append chunk_4866 (SigmaSteps209.checked_append chunk_5122 (SigmaSteps209.checked_append chunk_5378 (SigmaSteps209.checked_append chunk_5634 (SigmaSteps209.checked_append chunk_5890 (SigmaSteps209.checked_append chunk_6146 (SigmaSteps209.checked_append chunk_6402 (SigmaSteps209.checked_append chunk_6658 (SigmaSteps209.checked_append chunk_6914 (SigmaSteps209.checked_append chunk_7170 (SigmaSteps209.checked_append chunk_7426 (SigmaSteps209.checked_append chunk_7682 chunk_7938)))))))))))))))
#print axioms checked
end JSP233.SigmaBaseBlock209_04098

