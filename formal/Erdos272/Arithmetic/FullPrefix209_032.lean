import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_031
namespace JSP233.FullPrefix209_032
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1048576 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1048576 1024 637457902838043309 334211599245 638080556288863969 334864817715 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1049600 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1049600 1024 638080556288863969 334864817715 638702908622443526 335518357555 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1050624 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1050624 1024 638702908622443526 335518357555 639325464111362250 336172748171 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1051648 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1051648 1024 639325464111362250 336172748171 639948256907183157 336828026127 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1052672 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1052672 1024 639948256907183157 336828026127 640570413543224653 337483271787 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1053696 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1053696 1024 640570413543224653 337483271787 641192971861050380 338139577825 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1054720 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1054720 1024 641192971861050380 338139577825 641815809039546523 338796815813 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1055744 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1055744 1024 641815809039546523 338796815813 642438141117988983 339454158139 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1048576 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1048576 8192 637457902838043309 334211599245 642438141117988983 339454158139 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1048576 637457902838043309 334211599245 638080556288863969 334864817715 7168 642438141117988983 339454158139 checked_small_1048576 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1049600 638080556288863969 334864817715 638702908622443526 335518357555 6144 642438141117988983 339454158139 checked_small_1049600 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1050624 638702908622443526 335518357555 639325464111362250 336172748171 5120 642438141117988983 339454158139 checked_small_1050624 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1051648 639325464111362250 336172748171 639948256907183157 336828026127 4096 642438141117988983 339454158139 checked_small_1051648 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1052672 639948256907183157 336828026127 640570413543224653 337483271787 3072 642438141117988983 339454158139 checked_small_1052672 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1053696 640570413543224653 337483271787 641192971861050380 338139577825 2048 642438141117988983 339454158139 checked_small_1053696 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1054720 641192971861050380 338139577825 641815809039546523 338796815813 1024 642438141117988983 339454158139 checked_small_1054720 checked_small_1055744)))))))
#print axioms checked_part_1048576
private theorem checked_small_1056768 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1056768 1024 642438141117988983 339454158139 643060615646553487 340112288227 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1057792 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1057792 1024 643060615646553487 340112288227 643683157048495403 340771126495 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1058816 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1058816 1024 643683157048495403 340771126495 644305515544703491 341430408413 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1059840 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1059840 1024 644305515544703491 341430408413 644928215854607706 342090690081 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1060864 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1060864 1024 644928215854607706 342090690081 645550753361786344 342751436707 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1061888 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1061888 1024 645550753361786344 342751436707 646173194525279095 343412718427 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1062912 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1062912 1024 646173194525279095 343412718427 646795702821710006 344074708877 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1063936 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1063936 1024 646795702821710006 344074708877 647418336880133693 344737470693 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1056768 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1056768 8192 642438141117988983 339454158139 647418336880133693 344737470693 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1056768 642438141117988983 339454158139 643060615646553487 340112288227 7168 647418336880133693 344737470693 checked_small_1056768 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1057792 643060615646553487 340112288227 643683157048495403 340771126495 6144 647418336880133693 344737470693 checked_small_1057792 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1058816 643683157048495403 340771126495 644305515544703491 341430408413 5120 647418336880133693 344737470693 checked_small_1058816 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1059840 644305515544703491 341430408413 644928215854607706 342090690081 4096 647418336880133693 344737470693 checked_small_1059840 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1060864 644928215854607706 342090690081 645550753361786344 342751436707 3072 647418336880133693 344737470693 checked_small_1060864 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1061888 645550753361786344 342751436707 646173194525279095 343412718427 2048 647418336880133693 344737470693 checked_small_1061888 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1062912 646173194525279095 343412718427 646795702821710006 344074708877 1024 647418336880133693 344737470693 checked_small_1062912 checked_small_1063936)))))))
#print axioms checked_part_1056768
private theorem checked_small_1064960 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1064960 1024 647418336880133693 344737470693 648040810344192383 345400699015 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1065984 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1065984 1024 648040810344192383 345400699015 648663226601252945 346064503665 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1067008 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1067008 1024 648663226601252945 346064503665 649285940561709802 346729263523 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1068032 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1068032 1024 649285940561709802 346729263523 649908222760448600 347394199663 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1069056 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1069056 1024 649908222760448600 347394199663 650530735751596734 348060019751 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1070080 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1070080 1024 650530735751596734 348060019751 651153547536616267 348726797321 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1071104 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1071104 1024 651153547536616267 348726797321 651775762764578034 349393573361 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1072128 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1072128 1024 651775762764578034 349393573361 652398306270360008 350061338545 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1064960 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1064960 8192 647418336880133693 344737470693 652398306270360008 350061338545 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1064960 647418336880133693 344737470693 648040810344192383 345400699015 7168 652398306270360008 350061338545 checked_small_1064960 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1065984 648040810344192383 345400699015 648663226601252945 346064503665 6144 652398306270360008 350061338545 checked_small_1065984 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1067008 648663226601252945 346064503665 649285940561709802 346729263523 5120 652398306270360008 350061338545 checked_small_1067008 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1068032 649285940561709802 346729263523 649908222760448600 347394199663 4096 652398306270360008 350061338545 checked_small_1068032 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1069056 649908222760448600 347394199663 650530735751596734 348060019751 3072 652398306270360008 350061338545 checked_small_1069056 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1070080 650530735751596734 348060019751 651153547536616267 348726797321 2048 652398306270360008 350061338545 checked_small_1070080 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1071104 651153547536616267 348726797321 651775762764578034 349393573361 1024 652398306270360008 350061338545 checked_small_1071104 checked_small_1072128)))))))
#print axioms checked_part_1064960
private theorem checked_small_1073152 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1073152 1024 652398306270360008 350061338545 653021036021061566 350729941295 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1074176 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1074176 1024 653021036021061566 350729941295 653643335188297708 351398718973 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1075200 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1075200 1024 653643335188297708 351398718973 654265921365563426 352068442547 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1076224 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1076224 1024 654265921365563426 352068442547 654888608993545336 352738913005 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1077248 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1077248 1024 654888608993545336 352738913005 655511004928637547 353409706749 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1078272 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1078272 1024 655511004928637547 353409706749 656133382976913603 354081118403 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1079296 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1079296 1024 656133382976913603 354081118403 656756093968866753 354753526915 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1080320 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1080320 1024 656756093968866753 354753526915 657378556047990272 355426304111 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1073152 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1073152 8192 652398306270360008 350061338545 657378556047990272 355426304111 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1073152 652398306270360008 350061338545 653021036021061566 350729941295 7168 657378556047990272 355426304111 checked_small_1073152 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1074176 653021036021061566 350729941295 653643335188297708 351398718973 6144 657378556047990272 355426304111 checked_small_1074176 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1075200 653643335188297708 351398718973 654265921365563426 352068442547 5120 657378556047990272 355426304111 checked_small_1075200 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1076224 654265921365563426 352068442547 654888608993545336 352738913005 4096 657378556047990272 355426304111 checked_small_1076224 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1077248 654888608993545336 352738913005 655511004928637547 353409706749 3072 657378556047990272 355426304111 checked_small_1077248 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1078272 655511004928637547 353409706749 656133382976913603 354081118403 2048 657378556047990272 355426304111 checked_small_1078272 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1079296 656133382976913603 354081118403 656756093968866753 354753526915 1024 657378556047990272 355426304111 checked_small_1079296 checked_small_1080320)))))))
#print axioms checked_part_1073152
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1048576 32768 637457902838043309 334211599245 657378556047990272 355426304111 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1048576 637457902838043309 334211599245 642438141117988983 339454158139 24576 657378556047990272 355426304111 checked_part_1048576 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1056768 642438141117988983 339454158139 647418336880133693 344737470693 16384 657378556047990272 355426304111 checked_part_1056768 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1064960 647418336880133693 344737470693 652398306270360008 350061338545 8192 657378556047990272 355426304111 checked_part_1064960 checked_part_1073152)))
theorem block_sound :
    (657378556047990272 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1081344 ∧
     355426304111 = FrontierCheck209.triangle FactorFullCertificate209.phi 1081344) ∧
    ∀ t, 1048576 < t → t ≤ 1081344 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1048576 637457902838043309 334211599245 657378556047990272 355426304111 FullPrefix209_031.endpoint.1 FullPrefix209_031.endpoint.2 checked
theorem endpoint :
    657378556047990272 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1081344 ∧
    355426304111 = FrontierCheck209.triangle FactorFullCertificate209.phi 1081344 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1081344) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1048576
  · exact FullPrefix209_031.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_032
