module

public meta import Erdos272.Certificates.CoprimeBlock
public import Erdos272.Arithmetic.PrimorialValue47

@[expose] public section
namespace JSP233.FiniteAffine47
open AffineWitness47 PrimorialValue47 PrimorialPrefix46 AffineTrace46
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem block_04 : BlockEstimate 7858321551080267055879090 8 65536 16384 2139 0 := coprimeBlock 7858321551080267055879090 8 65536 256 64
#print axioms block_04
theorem block_05 : BlockEstimate 7858321551080267055879090 8 81920 16384 2138 8 := coprimeBlock 7858321551080267055879090 8 81920 256 64
#print axioms block_05
theorem block_06 : BlockEstimate 7858321551080267055879090 8 98304 16384 2136 16 := coprimeBlock 7858321551080267055879090 8 98304 256 64
#print axioms block_06
theorem block_07 : BlockEstimate 7858321551080267055879090 8 114688 16384 2143 10 := coprimeBlock 7858321551080267055879090 8 114688 256 64
#print axioms block_07
end JSP233.FiniteAffine47
