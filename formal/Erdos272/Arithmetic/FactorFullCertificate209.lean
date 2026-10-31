import Erdos272.Arithmetic.FullCoverage209
import Erdos272.Arithmetic.FullDivBlock209_000
import Erdos272.Arithmetic.FullDivBlock209_001
import Erdos272.Arithmetic.FullDivBlock209_002
import Erdos272.Arithmetic.FullDivBlock209_003
import Erdos272.Arithmetic.FullDivBlock209_004
import Erdos272.Arithmetic.FullDivBlock209_005
import Erdos272.Arithmetic.FullDivBlock209_006
import Erdos272.Arithmetic.FullDivBlock209_007
import Erdos272.Arithmetic.FullDivBlock209_008
import Erdos272.Arithmetic.FullDivBlock209_009
import Erdos272.Arithmetic.FullDivBlock209_010
import Erdos272.Arithmetic.FullDivBlock209_011
import Erdos272.Arithmetic.FullDivBlock209_012
import Erdos272.Arithmetic.FactorSoundBridge209
namespace JSP233.FactorFullCertificate209
open FactorFullData209
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem divides (n : Nat) (hn : 32753 < n) (hnH : n ≤ Limit) (hp : factor n ≠ 0) : factor n ∣ n := by
  unfold Limit at hnH
  by_cases hn_32754 : n < 65522
  · exact FastLookupBridge209.divides_of_check 32754 32768 n FullDivBlock209_000.checked_32754 (by omega) hn_32754 hp
  by_cases hn_65522 : n < 98290
  · exact FastLookupBridge209.divides_of_check 65522 32768 n FullDivBlock209_000.checked_65522 (by omega) hn_65522 hp
  by_cases hn_98290 : n < 131058
  · exact FastLookupBridge209.divides_of_check 98290 32768 n FullDivBlock209_000.checked_98290 (by omega) hn_98290 hp
  by_cases hn_131058 : n < 163826
  · exact FastLookupBridge209.divides_of_check 131058 32768 n FullDivBlock209_000.checked_131058 (by omega) hn_131058 hp
  by_cases hn_163826 : n < 196594
  · exact FastLookupBridge209.divides_of_check 163826 32768 n FullDivBlock209_001.checked_163826 (by omega) hn_163826 hp
  by_cases hn_196594 : n < 229362
  · exact FastLookupBridge209.divides_of_check 196594 32768 n FullDivBlock209_001.checked_196594 (by omega) hn_196594 hp
  by_cases hn_229362 : n < 262130
  · exact FastLookupBridge209.divides_of_check 229362 32768 n FullDivBlock209_001.checked_229362 (by omega) hn_229362 hp
  by_cases hn_262130 : n < 294898
  · exact FastLookupBridge209.divides_of_check 262130 32768 n FullDivBlock209_001.checked_262130 (by omega) hn_262130 hp
  by_cases hn_294898 : n < 327666
  · exact FastLookupBridge209.divides_of_check 294898 32768 n FullDivBlock209_002.checked_294898 (by omega) hn_294898 hp
  by_cases hn_327666 : n < 360434
  · exact FastLookupBridge209.divides_of_check 327666 32768 n FullDivBlock209_002.checked_327666 (by omega) hn_327666 hp
  by_cases hn_360434 : n < 393202
  · exact FastLookupBridge209.divides_of_check 360434 32768 n FullDivBlock209_002.checked_360434 (by omega) hn_360434 hp
  by_cases hn_393202 : n < 425970
  · exact FastLookupBridge209.divides_of_check 393202 32768 n FullDivBlock209_002.checked_393202 (by omega) hn_393202 hp
  by_cases hn_425970 : n < 458738
  · exact FastLookupBridge209.divides_of_check 425970 32768 n FullDivBlock209_003.checked_425970 (by omega) hn_425970 hp
  by_cases hn_458738 : n < 491506
  · exact FastLookupBridge209.divides_of_check 458738 32768 n FullDivBlock209_003.checked_458738 (by omega) hn_458738 hp
  by_cases hn_491506 : n < 524274
  · exact FastLookupBridge209.divides_of_check 491506 32768 n FullDivBlock209_003.checked_491506 (by omega) hn_491506 hp
  by_cases hn_524274 : n < 557042
  · exact FastLookupBridge209.divides_of_check 524274 32768 n FullDivBlock209_003.checked_524274 (by omega) hn_524274 hp
  by_cases hn_557042 : n < 589810
  · exact FastLookupBridge209.divides_of_check 557042 32768 n FullDivBlock209_004.checked_557042 (by omega) hn_557042 hp
  by_cases hn_589810 : n < 622578
  · exact FastLookupBridge209.divides_of_check 589810 32768 n FullDivBlock209_004.checked_589810 (by omega) hn_589810 hp
  by_cases hn_622578 : n < 655346
  · exact FastLookupBridge209.divides_of_check 622578 32768 n FullDivBlock209_004.checked_622578 (by omega) hn_622578 hp
  by_cases hn_655346 : n < 688114
  · exact FastLookupBridge209.divides_of_check 655346 32768 n FullDivBlock209_004.checked_655346 (by omega) hn_655346 hp
  by_cases hn_688114 : n < 720882
  · exact FastLookupBridge209.divides_of_check 688114 32768 n FullDivBlock209_005.checked_688114 (by omega) hn_688114 hp
  by_cases hn_720882 : n < 753650
  · exact FastLookupBridge209.divides_of_check 720882 32768 n FullDivBlock209_005.checked_720882 (by omega) hn_720882 hp
  by_cases hn_753650 : n < 786418
  · exact FastLookupBridge209.divides_of_check 753650 32768 n FullDivBlock209_005.checked_753650 (by omega) hn_753650 hp
  by_cases hn_786418 : n < 819186
  · exact FastLookupBridge209.divides_of_check 786418 32768 n FullDivBlock209_005.checked_786418 (by omega) hn_786418 hp
  by_cases hn_819186 : n < 851954
  · exact FastLookupBridge209.divides_of_check 819186 32768 n FullDivBlock209_006.checked_819186 (by omega) hn_819186 hp
  by_cases hn_851954 : n < 884722
  · exact FastLookupBridge209.divides_of_check 851954 32768 n FullDivBlock209_006.checked_851954 (by omega) hn_851954 hp
  by_cases hn_884722 : n < 917490
  · exact FastLookupBridge209.divides_of_check 884722 32768 n FullDivBlock209_006.checked_884722 (by omega) hn_884722 hp
  by_cases hn_917490 : n < 950258
  · exact FastLookupBridge209.divides_of_check 917490 32768 n FullDivBlock209_006.checked_917490 (by omega) hn_917490 hp
  by_cases hn_950258 : n < 983026
  · exact FastLookupBridge209.divides_of_check 950258 32768 n FullDivBlock209_007.checked_950258 (by omega) hn_950258 hp
  by_cases hn_983026 : n < 1015794
  · exact FastLookupBridge209.divides_of_check 983026 32768 n FullDivBlock209_007.checked_983026 (by omega) hn_983026 hp
  by_cases hn_1015794 : n < 1048562
  · exact FastLookupBridge209.divides_of_check 1015794 32768 n FullDivBlock209_007.checked_1015794 (by omega) hn_1015794 hp
  by_cases hn_1048562 : n < 1081330
  · exact FastLookupBridge209.divides_of_check 1048562 32768 n FullDivBlock209_007.checked_1048562 (by omega) hn_1048562 hp
  by_cases hn_1081330 : n < 1114098
  · exact FastLookupBridge209.divides_of_check 1081330 32768 n FullDivBlock209_008.checked_1081330 (by omega) hn_1081330 hp
  by_cases hn_1114098 : n < 1146866
  · exact FastLookupBridge209.divides_of_check 1114098 32768 n FullDivBlock209_008.checked_1114098 (by omega) hn_1114098 hp
  by_cases hn_1146866 : n < 1179634
  · exact FastLookupBridge209.divides_of_check 1146866 32768 n FullDivBlock209_008.checked_1146866 (by omega) hn_1146866 hp
  by_cases hn_1179634 : n < 1212402
  · exact FastLookupBridge209.divides_of_check 1179634 32768 n FullDivBlock209_008.checked_1179634 (by omega) hn_1179634 hp
  by_cases hn_1212402 : n < 1245170
  · exact FastLookupBridge209.divides_of_check 1212402 32768 n FullDivBlock209_009.checked_1212402 (by omega) hn_1212402 hp
  by_cases hn_1245170 : n < 1277938
  · exact FastLookupBridge209.divides_of_check 1245170 32768 n FullDivBlock209_009.checked_1245170 (by omega) hn_1245170 hp
  by_cases hn_1277938 : n < 1310706
  · exact FastLookupBridge209.divides_of_check 1277938 32768 n FullDivBlock209_009.checked_1277938 (by omega) hn_1277938 hp
  by_cases hn_1310706 : n < 1343474
  · exact FastLookupBridge209.divides_of_check 1310706 32768 n FullDivBlock209_009.checked_1310706 (by omega) hn_1310706 hp
  by_cases hn_1343474 : n < 1376242
  · exact FastLookupBridge209.divides_of_check 1343474 32768 n FullDivBlock209_010.checked_1343474 (by omega) hn_1343474 hp
  by_cases hn_1376242 : n < 1409010
  · exact FastLookupBridge209.divides_of_check 1376242 32768 n FullDivBlock209_010.checked_1376242 (by omega) hn_1376242 hp
  by_cases hn_1409010 : n < 1441778
  · exact FastLookupBridge209.divides_of_check 1409010 32768 n FullDivBlock209_010.checked_1409010 (by omega) hn_1409010 hp
  by_cases hn_1441778 : n < 1474546
  · exact FastLookupBridge209.divides_of_check 1441778 32768 n FullDivBlock209_010.checked_1441778 (by omega) hn_1441778 hp
  by_cases hn_1474546 : n < 1507314
  · exact FastLookupBridge209.divides_of_check 1474546 32768 n FullDivBlock209_011.checked_1474546 (by omega) hn_1474546 hp
  by_cases hn_1507314 : n < 1540082
  · exact FastLookupBridge209.divides_of_check 1507314 32768 n FullDivBlock209_011.checked_1507314 (by omega) hn_1507314 hp
  by_cases hn_1540082 : n < 1572850
  · exact FastLookupBridge209.divides_of_check 1540082 32768 n FullDivBlock209_011.checked_1540082 (by omega) hn_1540082 hp
  by_cases hn_1572850 : n < 1605618
  · exact FastLookupBridge209.divides_of_check 1572850 32768 n FullDivBlock209_011.checked_1572850 (by omega) hn_1572850 hp
  by_cases hn_1605618 : n < 1638386
  · exact FastLookupBridge209.divides_of_check 1605618 32768 n FullDivBlock209_012.checked_1605618 (by omega) hn_1605618 hp
  exact FastLookupBridge209.divides_of_check 1638386 31615 n FullDivBlock209_012.checked_1638386 (by omega) (by omega) hp
theorem factor_sound (n : Nat) (hn : 32753 < n) (hnH : n ≤ Limit) :
    (factor n = 0 → n.Prime) ∧
    (factor n ≠ 0 → (factor n).Prime ∧ factor n ∣ n) := by
  exact FactorSoundBridge209.factor_sound FullCoverage209.rows divides n hn hnH
theorem fast_factor_sound (n : Nat) (hn : 32753 < n) (hnH : n ≤ Limit) :
    (FastFullLookup209.factor n = 0 → n.Prime) ∧
    (FastFullLookup209.factor n ≠ 0 → (FastFullLookup209.factor n).Prime ∧ FastFullLookup209.factor n ∣ n) := by
  simpa only [FastFullLookup209.factor_eq] using factor_sound n hn hnH
def phi (n : Nat) : Nat := FactorSoundBridge209.value n
theorem phi_correct (n : Nat) (hn : n ≤ Limit) : phi n = Nat.totient n := by
  exact FactorSoundBridge209.phi_correct FullCoverage209.rows divides n hn
#print axioms phi_correct
end JSP233.FactorFullCertificate209
