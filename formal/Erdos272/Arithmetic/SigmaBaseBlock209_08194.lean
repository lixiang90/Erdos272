module

public import Erdos272.Certificates.SigmaSteps209
public import Erdos272.Arithmetic.SigmaBaseData209
public import Erdos272.Arithmetic.FastFullLookup209

@[expose] public section
namespace JSP233.SigmaBaseBlock209_08194
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem chunk_8194 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 8194 256=true := by decide +kernel

private theorem chunk_8450 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 8450 256=true := by decide +kernel

private theorem chunk_8706 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 8706 256=true := by decide +kernel

private theorem chunk_8962 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 8962 256=true := by decide +kernel

private theorem chunk_9218 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 9218 256=true := by decide +kernel

private theorem chunk_9474 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 9474 256=true := by decide +kernel

private theorem chunk_9730 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 9730 256=true := by decide +kernel

private theorem chunk_9986 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 9986 256=true := by decide +kernel

private theorem chunk_10242 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 10242 256=true := by decide +kernel

private theorem chunk_10498 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 10498 256=true := by decide +kernel

private theorem chunk_10754 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 10754 256=true := by decide +kernel

private theorem chunk_11010 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 11010 256=true := by decide +kernel

private theorem chunk_11266 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 11266 256=true := by decide +kernel

private theorem chunk_11522 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 11522 256=true := by decide +kernel

private theorem chunk_11778 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 11778 256=true := by decide +kernel

private theorem chunk_12034 : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 12034 256=true := by decide +kernel

theorem checked : ComputedSigma209.checkSteps SigmaBaseData209.value FastFullLookup209.factor 8194 4096=true := by
  exact (SigmaSteps209.checked_append chunk_8194 (SigmaSteps209.checked_append chunk_8450 (SigmaSteps209.checked_append chunk_8706 (SigmaSteps209.checked_append chunk_8962 (SigmaSteps209.checked_append chunk_9218 (SigmaSteps209.checked_append chunk_9474 (SigmaSteps209.checked_append chunk_9730 (SigmaSteps209.checked_append chunk_9986 (SigmaSteps209.checked_append chunk_10242 (SigmaSteps209.checked_append chunk_10498 (SigmaSteps209.checked_append chunk_10754 (SigmaSteps209.checked_append chunk_11010 (SigmaSteps209.checked_append chunk_11266 (SigmaSteps209.checked_append chunk_11522 (SigmaSteps209.checked_append chunk_11778 chunk_12034)))))))))))))))
#print axioms checked
end JSP233.SigmaBaseBlock209_08194

