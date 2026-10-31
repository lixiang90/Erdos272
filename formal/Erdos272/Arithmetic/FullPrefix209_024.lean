import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_023
namespace JSP233.FullPrefix209_024
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_786432 : DualFrontier209.checkFrom FactorFullCertificate209.phi 786432 1024 478093528257690593 187994104135 478716001280778051 188483955733 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_787456 : DualFrontier209.checkFrom FactorFullCertificate209.phi 787456 1024 478716001280778051 188483955733 479338638286676759 188974573991 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_788480 : DualFrontier209.checkFrom FactorFullCertificate209.phi 788480 1024 479338638286676759 188974573991 479961079210974418 189465675145 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_789504 : DualFrontier209.checkFrom FactorFullCertificate209.phi 789504 1024 479961079210974418 189465675145 480583584367198285 189957464383 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_790528 : DualFrontier209.checkFrom FactorFullCertificate209.phi 790528 1024 480583584367198285 189957464383 481206287810126903 190450048001 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_791552 : DualFrontier209.checkFrom FactorFullCertificate209.phi 791552 1024 481206287810126903 190450048001 481828458440065837 190942847165 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_792576 : DualFrontier209.checkFrom FactorFullCertificate209.phi 792576 1024 481828458440065837 190942847165 482450989484256831 191436569099 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_793600 : DualFrontier209.checkFrom FactorFullCertificate209.phi 793600 1024 482450989484256831 191436569099 483073915329220336 191931242235 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_786432 : DualFrontier209.checkFrom FactorFullCertificate209.phi 786432 8192 478093528257690593 187994104135 483073915329220336 191931242235 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 786432 478093528257690593 187994104135 478716001280778051 188483955733 7168 483073915329220336 191931242235 checked_small_786432 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 787456 478716001280778051 188483955733 479338638286676759 188974573991 6144 483073915329220336 191931242235 checked_small_787456 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 788480 479338638286676759 188974573991 479961079210974418 189465675145 5120 483073915329220336 191931242235 checked_small_788480 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 789504 479961079210974418 189465675145 480583584367198285 189957464383 4096 483073915329220336 191931242235 checked_small_789504 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 790528 480583584367198285 189957464383 481206287810126903 190450048001 3072 483073915329220336 191931242235 checked_small_790528 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 791552 481206287810126903 190450048001 481828458440065837 190942847165 2048 483073915329220336 191931242235 checked_small_791552 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 792576 481828458440065837 190942847165 482450989484256831 191436569099 1024 483073915329220336 191931242235 checked_small_792576 checked_small_793600)))))))
#print axioms checked_part_786432
private theorem checked_small_794624 : DualFrontier209.checkFrom FactorFullCertificate209.phi 794624 1024 483073915329220336 191931242235 483696095483268132 192425960365 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_795648 : DualFrontier209.checkFrom FactorFullCertificate209.phi 795648 1024 483696095483268132 192425960365 484318633609848592 192921600445 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_796672 : DualFrontier209.checkFrom FactorFullCertificate209.phi 796672 1024 484318633609848592 192921600445 484941255672407728 193417944979 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_797696 : DualFrontier209.checkFrom FactorFullCertificate209.phi 797696 1024 484941255672407728 193417944979 485563742134836779 193914818881 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_798720 : DualFrontier209.checkFrom FactorFullCertificate209.phi 798720 1024 485563742134836779 193914818881 486186244923079231 194412343235 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_799744 : DualFrontier209.checkFrom FactorFullCertificate209.phi 799744 1024 486186244923079231 194412343235 486808848810169804 194910585969 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_800768 : DualFrontier209.checkFrom FactorFullCertificate209.phi 800768 1024 486808848810169804 194910585969 487431187695815579 195409253861 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_801792 : DualFrontier209.checkFrom FactorFullCertificate209.phi 801792 1024 487431187695815579 195409253861 488053634935739867 195908645839 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_794624 : DualFrontier209.checkFrom FactorFullCertificate209.phi 794624 8192 483073915329220336 191931242235 488053634935739867 195908645839 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 794624 483073915329220336 191931242235 483696095483268132 192425960365 7168 488053634935739867 195908645839 checked_small_794624 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 795648 483696095483268132 192425960365 484318633609848592 192921600445 6144 488053634935739867 195908645839 checked_small_795648 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 796672 484318633609848592 192921600445 484941255672407728 193417944979 5120 488053634935739867 195908645839 checked_small_796672 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 797696 484941255672407728 193417944979 485563742134836779 193914818881 4096 488053634935739867 195908645839 checked_small_797696 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 798720 485563742134836779 193914818881 486186244923079231 194412343235 3072 488053634935739867 195908645839 checked_small_798720 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 799744 486186244923079231 194412343235 486808848810169804 194910585969 2048 488053634935739867 195908645839 checked_small_799744 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 800768 486808848810169804 194910585969 487431187695815579 195409253861 1024 488053634935739867 195908645839 checked_small_800768 checked_small_801792)))))))
#print axioms checked_part_794624
private theorem checked_small_802816 : DualFrontier209.checkFrom FactorFullCertificate209.phi 802816 1024 488053634935739867 195908645839 488676444351225354 196408966265 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_803840 : DualFrontier209.checkFrom FactorFullCertificate209.phi 803840 1024 488676444351225354 196408966265 489298888391998959 196909630667 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_804864 : DualFrontier209.checkFrom FactorFullCertificate209.phi 804864 1024 489298888391998959 196909630667 489921328296173777 197410929043 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_805888 : DualFrontier209.checkFrom FactorFullCertificate209.phi 805888 1024 489921328296173777 197410929043 490543918606995250 197912986079 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_806912 : DualFrontier209.checkFrom FactorFullCertificate209.phi 806912 1024 490543918606995250 197912986079 491166325148319334 198415532253 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_807936 : DualFrontier209.checkFrom FactorFullCertificate209.phi 807936 1024 491166325148319334 198415532253 491788815012066675 198918783063 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_808960 : DualFrontier209.checkFrom FactorFullCertificate209.phi 808960 1024 491788815012066675 198918783063 492411614903915002 199422922395 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_809984 : DualFrontier209.checkFrom FactorFullCertificate209.phi 809984 1024 492411614903915002 199422922395 493033922202477432 199927300261 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_802816 : DualFrontier209.checkFrom FactorFullCertificate209.phi 802816 8192 488053634935739867 195908645839 493033922202477432 199927300261 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 802816 488053634935739867 195908645839 488676444351225354 196408966265 7168 493033922202477432 199927300261 checked_small_802816 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 803840 488676444351225354 196408966265 489298888391998959 196909630667 6144 493033922202477432 199927300261 checked_small_803840 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 804864 489298888391998959 196909630667 489921328296173777 197410929043 5120 493033922202477432 199927300261 checked_small_804864 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 805888 489921328296173777 197410929043 490543918606995250 197912986079 4096 493033922202477432 199927300261 checked_small_805888 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 806912 490543918606995250 197912986079 491166325148319334 198415532253 3072 493033922202477432 199927300261 checked_small_806912 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 807936 491166325148319334 198415532253 491788815012066675 198918783063 2048 493033922202477432 199927300261 checked_small_807936 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 808960 491788815012066675 198918783063 492411614903915002 199422922395 1024 493033922202477432 199927300261 checked_small_808960 checked_small_809984)))))))
#print axioms checked_part_802816
private theorem checked_small_811008 : DualFrontier209.checkFrom FactorFullCertificate209.phi 811008 1024 493033922202477432 199927300261 493656427617832945 200432476033 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_812032 : DualFrontier209.checkFrom FactorFullCertificate209.phi 812032 1024 493656427617832945 200432476033 494279121264270585 200938442277 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_813056 : DualFrontier209.checkFrom FactorFullCertificate209.phi 813056 1024 494279121264270585 200938442277 494901372304046780 201444686029 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_814080 : DualFrontier209.checkFrom FactorFullCertificate209.phi 814080 1024 494901372304046780 201444686029 495524003141990008 201951876265 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_815104 : DualFrontier209.checkFrom FactorFullCertificate209.phi 815104 1024 495524003141990008 201951876265 496146613988057058 202459687875 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_816128 : DualFrontier209.checkFrom FactorFullCertificate209.phi 816128 1024 496146613988057058 202459687875 496769003372738062 202967956169 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_817152 : DualFrontier209.checkFrom FactorFullCertificate209.phi 817152 1024 496769003372738062 202967956169 497391505235086911 203476953685 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_818176 : DualFrontier209.checkFrom FactorFullCertificate209.phi 818176 1024 497391505235086911 203476953685 498014225086146402 203986767209 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_811008 : DualFrontier209.checkFrom FactorFullCertificate209.phi 811008 8192 493033922202477432 199927300261 498014225086146402 203986767209 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 811008 493033922202477432 199927300261 493656427617832945 200432476033 7168 498014225086146402 203986767209 checked_small_811008 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 812032 493656427617832945 200432476033 494279121264270585 200938442277 6144 498014225086146402 203986767209 checked_small_812032 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 813056 494279121264270585 200938442277 494901372304046780 201444686029 5120 498014225086146402 203986767209 checked_small_813056 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 814080 494901372304046780 201444686029 495524003141990008 201951876265 4096 498014225086146402 203986767209 checked_small_814080 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 815104 495524003141990008 201951876265 496146613988057058 202459687875 3072 498014225086146402 203986767209 checked_small_815104 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 816128 496146613988057058 202459687875 496769003372738062 202967956169 2048 498014225086146402 203986767209 checked_small_816128 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 817152 496769003372738062 202967956169 497391505235086911 203476953685 1024 498014225086146402 203986767209 checked_small_817152 checked_small_818176)))))))
#print axioms checked_part_811008
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 786432 32768 478093528257690593 187994104135 498014225086146402 203986767209 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 786432 478093528257690593 187994104135 483073915329220336 191931242235 24576 498014225086146402 203986767209 checked_part_786432 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 794624 483073915329220336 191931242235 488053634935739867 195908645839 16384 498014225086146402 203986767209 checked_part_794624 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 802816 488053634935739867 195908645839 493033922202477432 199927300261 8192 498014225086146402 203986767209 checked_part_802816 checked_part_811008)))
theorem block_sound :
    (498014225086146402 = FrontierCheck209.massFloor FactorFullCertificate209.phi 819200 ∧
     203986767209 = FrontierCheck209.triangle FactorFullCertificate209.phi 819200) ∧
    ∀ t, 786432 < t → t ≤ 819200 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 786432 478093528257690593 187994104135 498014225086146402 203986767209 FullPrefix209_023.endpoint.1 FullPrefix209_023.endpoint.2 checked
theorem endpoint :
    498014225086146402 = FrontierCheck209.massFloor FactorFullCertificate209.phi 819200 ∧
    203986767209 = FrontierCheck209.triangle FactorFullCertificate209.phi 819200 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 819200) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 786432
  · exact FullPrefix209_023.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_024
