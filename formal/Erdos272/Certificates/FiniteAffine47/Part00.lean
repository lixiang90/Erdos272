module

public meta import Erdos272.Certificates.CoprimeBlock
public import Erdos272.Arithmetic.PrimorialValue47

@[expose] public section
namespace JSP233.FiniteAffine47
open AffineWitness47 PrimorialValue47 PrimorialPrefix46 AffineTrace46
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem block_00 : BlockEstimate 7858321551080267055879090 8 0 16384 2068 62 := coprimeBlock 7858321551080267055879090 8 0 256 64
#print axioms block_00
theorem block_01 : BlockEstimate 7858321551080267055879090 8 16384 16384 2093 44 := coprimeBlock 7858321551080267055879090 8 16384 256 64
#print axioms block_01
theorem block_02 : BlockEstimate 7858321551080267055879090 8 32768 16384 2124 2 := coprimeBlock 7858321551080267055879090 8 32768 256 64
#print axioms block_02
theorem block_03 : BlockEstimate 7858321551080267055879090 8 49152 16384 2129 6 := coprimeBlock 7858321551080267055879090 8 49152 256 64
#print axioms block_03
end JSP233.FiniteAffine47
