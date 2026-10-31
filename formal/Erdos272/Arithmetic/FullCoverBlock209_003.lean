import Erdos272.Arithmetic.FastLookupBridge209
import Erdos272.Arithmetic.SplitChecks209
namespace JSP233.FullCoverBlock209_003
open FastFullLookup209
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem checked_191_2_part_0 : MarkerSieve209.checkMultiples marked 191 (191 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_191_2_part_0
theorem checked_191_2_part_8192 : MarkerSieve209.checkMultiples marked 191 (191 * 8194) 550 = true := by
  decide +kernel
#print axioms checked_191_2_part_8192
theorem checked_191_2 : MarkerSieve209.checkMultiples marked 191 (191 * 2) 8742 = true := by
  exact (SplitChecks209.marked_join marked 191 (191 * 2) 8192 550 checked_191_2_part_0 checked_191_2_part_8192)
#print axioms checked_191_2
theorem checked_193_2_part_0 : MarkerSieve209.checkMultiples marked 193 (193 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_193_2_part_0
theorem checked_193_2_part_8192 : MarkerSieve209.checkMultiples marked 193 (193 * 8194) 459 = true := by
  decide +kernel
#print axioms checked_193_2_part_8192
theorem checked_193_2 : MarkerSieve209.checkMultiples marked 193 (193 * 2) 8651 = true := by
  exact (SplitChecks209.marked_join marked 193 (193 * 2) 8192 459 checked_193_2_part_0 checked_193_2_part_8192)
#print axioms checked_193_2
theorem checked_197_2_part_0 : MarkerSieve209.checkMultiples marked 197 (197 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_197_2_part_0
theorem checked_197_2_part_8192 : MarkerSieve209.checkMultiples marked 197 (197 * 8194) 284 = true := by
  decide +kernel
#print axioms checked_197_2_part_8192
theorem checked_197_2 : MarkerSieve209.checkMultiples marked 197 (197 * 2) 8476 = true := by
  exact (SplitChecks209.marked_join marked 197 (197 * 2) 8192 284 checked_197_2_part_0 checked_197_2_part_8192)
#print axioms checked_197_2
theorem checked_199_2_part_0 : MarkerSieve209.checkMultiples marked 199 (199 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_199_2_part_0
theorem checked_199_2_part_8192 : MarkerSieve209.checkMultiples marked 199 (199 * 8194) 198 = true := by
  decide +kernel
#print axioms checked_199_2_part_8192
theorem checked_199_2 : MarkerSieve209.checkMultiples marked 199 (199 * 2) 8390 = true := by
  exact (SplitChecks209.marked_join marked 199 (199 * 2) 8192 198 checked_199_2_part_0 checked_199_2_part_8192)
#print axioms checked_199_2
theorem checked_211_2 : MarkerSieve209.checkMultiples marked 211 (211 * 2) 7913 = true := by
  decide +kernel
#print axioms checked_211_2
theorem checked_223_2 : MarkerSieve209.checkMultiples marked 223 (223 * 2) 7487 = true := by
  decide +kernel
#print axioms checked_223_2
theorem checked_227_2 : MarkerSieve209.checkMultiples marked 227 (227 * 2) 7355 = true := by
  decide +kernel
#print axioms checked_227_2
theorem checked_229_2 : MarkerSieve209.checkMultiples marked 229 (229 * 2) 7291 = true := by
  decide +kernel
#print axioms checked_229_2
theorem checked_233_2 : MarkerSieve209.checkMultiples marked 233 (233 * 2) 7166 = true := by
  decide +kernel
#print axioms checked_233_2
theorem checked_239_2 : MarkerSieve209.checkMultiples marked 239 (239 * 2) 6986 = true := by
  decide +kernel
#print axioms checked_239_2
theorem checked_241_2 : MarkerSieve209.checkMultiples marked 241 (241 * 2) 6928 = true := by
  decide +kernel
#print axioms checked_241_2
theorem checked_251_2 : MarkerSieve209.checkMultiples marked 251 (251 * 2) 6652 = true := by
  decide +kernel
#print axioms checked_251_2
theorem checked_257_2 : MarkerSieve209.checkMultiples marked 257 (257 * 2) 6497 = true := by
  decide +kernel
#print axioms checked_257_2
theorem checked_263_2 : MarkerSieve209.checkMultiples marked 263 (263 * 2) 6348 = true := by
  decide +kernel
#print axioms checked_263_2
theorem checked_269_2 : MarkerSieve209.checkMultiples marked 269 (269 * 2) 6207 = true := by
  decide +kernel
#print axioms checked_269_2
theorem checked_271_2 : MarkerSieve209.checkMultiples marked 271 (271 * 2) 6161 = true := by
  decide +kernel
#print axioms checked_271_2
end JSP233.FullCoverBlock209_003
