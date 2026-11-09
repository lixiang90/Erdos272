module

public import Erdos272.Arithmetic.CleanupMachine208

@[expose] public section
namespace JSP233.CleanupGroupPilot208
open CleanupMachine208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
def row : Row := ⟨1000000000000,659000,705097,100,[⟨242,100,338,71,95,118,126,133⟩,⟨338,79,484,181,220,240,246,252⟩,⟨484,63,726,359,390,406,411,415⟩,⟨726,51,1210,625,650,663,667,670⟩,⟨1210,39,2420,1133,1152,1162,1165,1168⟩,⟨2420,28,7744,2365,2379,2386,2388,2390⟩,⟨7744,16,247808,7713,7721,7725,7726,7727⟩]⟩
def expected01 : Totals := ⟨133276280795618,534749623156,2908121859046,130902908559728,1415917201⟩
theorem checked01 : checkChunk row 129 128 expected01=true := by decide +kernel
#print axioms checked01
def expected02 : Totals := ⟨67960393339882,447647953550,1951444976507,66456596316925,1202565604⟩
theorem checked02 : checkChunk row 257 128 expected02=true := by decide +kernel
#print axioms checked02
def expected03 : Totals := ⟨41239469648491,386494690743,1479938219491,40146026119743,1085722601⟩
theorem checked03 : checkChunk row 385 128 expected03=true := by decide +kernel
#print axioms checked03
def expected04 : Totals := ⟨27239536486729,336874053180,1195290859098,26381119680811,969198660⟩
theorem checked04 : checkChunk row 513 128 expected04=true := by decide +kernel
#print axioms checked04
def expected05 : Totals := ⟨17488524798399,287253415617,897320509092,16878457704924,853368870⟩
theorem checked05 : checkChunk row 641 128 expected05=true := by decide +kernel
#print axioms checked05
def expected06 : Totals := ⟨13896620170021,269954477751,839212192160,13327362455612,821155042⟩
theorem checked06 : checkChunk row 769 128 expected06=true := by decide +kernel
#print axioms checked06
def expected07 : Totals := ⟨9796002199252,232473445708,706419115639,9322056529321,745631778⟩
theorem checked07 : checkChunk row 897 128 expected07=true := by decide +kernel
#print axioms checked07
def expected08 : Totals := ⟨6358264956749,190895296802,531767968536,6017392285015,644801458⟩
theorem checked08 : checkChunk row 1025 128 expected08=true := by decide +kernel
#print axioms checked08
def expected09 : Totals := ⟨4576431854232,165250380141,452547662804,4289134571569,604127997⟩
theorem checked09 : checkChunk row 1153 128 expected09=true := by decide +kernel
#print axioms checked09
def expected10 : Totals := ⟨3734867949809,152655539414,423243893320,3464279595903,592461272⟩
theorem checked10 : checkChunk row 1281 128 expected10=true := by decide +kernel
#print axioms checked10
def expected11 : Totals := ⟨2831176103894,131866464961,369688141524,2593354427331,551952550⟩
theorem checked11 : checkChunk row 1409 128 expected11=true := by decide +kernel
#print axioms checked11
def expected12 : Totals := ⟨2403965482801,123672231235,345572310692,2182065403344,535910087⟩
theorem checked12 : checkChunk row 1537 128 expected12=true := by decide +kernel
#print axioms checked12
def expected13 : Totals := ⟨1136747382593,86798179468,217178628866,1006366933195,394448096⟩
theorem checked13 : checkChunk row 1665 128 expected13=true := by decide +kernel
#print axioms checked13
def expected14 : Totals := ⟨1094790829333,81790592191,202420375772,974161045752,387187961⟩
theorem checked14 : checkChunk row 1793 128 expected14=true := by decide +kernel
#print axioms checked14
def expected15 : Totals := ⟨884061117295,76176024638,189721413816,770515728117,375797207⟩
theorem checked15 : checkChunk row 1921 128 expected15=true := by decide +kernel
#print axioms checked15
def expected16 : Totals := ⟨735480027317,69954476809,175649591108,629784913018,362207103⟩
theorem checked16 : checkChunk row 2049 128 expected16=true := by decide +kernel
#print axioms checked16
end JSP233.CleanupGroupPilot208
