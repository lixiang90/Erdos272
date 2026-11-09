module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_022

@[expose] public section
namespace JSP233.FullPrefix209_023
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_753664 : DualFrontier209.checkFrom FactorFullCertificate209.phi 753664 1024 458172948572179690 172654295365 458795611009824046 173123892687 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_754688 : DualFrontier209.checkFrom FactorFullCertificate209.phi 754688 1024 458795611009824046 173123892687 459417959258807411 173593890325 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_755712 : DualFrontier209.checkFrom FactorFullCertificate209.phi 755712 1024 459417959258807411 173593890325 460040472152497090 174064649673 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_756736 : DualFrontier209.checkFrom FactorFullCertificate209.phi 756736 1024 460040472152497090 174064649673 460663061912395942 174536104721 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_757760 : DualFrontier209.checkFrom FactorFullCertificate209.phi 757760 1024 460663061912395942 174536104721 461285634769544737 175008184547 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_758784 : DualFrontier209.checkFrom FactorFullCertificate209.phi 758784 1024 461285634769544737 175008184547 461908007752218915 175480750075 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_759808 : DualFrontier209.checkFrom FactorFullCertificate209.phi 759808 1024 461908007752218915 175480750075 462530790790620419 175954264747 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_760832 : DualFrontier209.checkFrom FactorFullCertificate209.phi 760832 1024 462530790790620419 175954264747 463153007420634441 176427985897 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_753664 : DualFrontier209.checkFrom FactorFullCertificate209.phi 753664 8192 458172948572179690 172654295365 463153007420634441 176427985897 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 753664 458172948572179690 172654295365 458795611009824046 173123892687 7168 463153007420634441 176427985897 checked_small_753664 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 754688 458795611009824046 173123892687 459417959258807411 173593890325 6144 463153007420634441 176427985897 checked_small_754688 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 755712 459417959258807411 173593890325 460040472152497090 174064649673 5120 463153007420634441 176427985897 checked_small_755712 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 756736 460040472152497090 174064649673 460663061912395942 174536104721 4096 463153007420634441 176427985897 checked_small_756736 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 757760 460663061912395942 174536104721 461285634769544737 175008184547 3072 463153007420634441 176427985897 checked_small_757760 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 758784 461285634769544737 175008184547 461908007752218915 175480750075 2048 463153007420634441 176427985897 checked_small_758784 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 759808 461908007752218915 175480750075 462530790790620419 175954264747 1024 463153007420634441 176427985897 checked_small_759808 checked_small_760832)))))))
#print axioms checked_part_753664
private theorem checked_small_761856 : DualFrontier209.checkFrom FactorFullCertificate209.phi 761856 1024 463153007420634441 176427985897 463775570437637975 176902608143 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_762880 : DualFrontier209.checkFrom FactorFullCertificate209.phi 762880 1024 463775570437637975 176902608143 464398219874975156 177377933961 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_763904 : DualFrontier209.checkFrom FactorFullCertificate209.phi 763904 1024 464398219874975156 177377933961 465020713124042616 177853778029 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_764928 : DualFrontier209.checkFrom FactorFullCertificate209.phi 764928 1024 465020713124042616 177853778029 465643093991858527 178330173429 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_765952 : DualFrontier209.checkFrom FactorFullCertificate209.phi 765952 1024 465643093991858527 178330173429 466265658006424943 178807346473 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_766976 : DualFrontier209.checkFrom FactorFullCertificate209.phi 766976 1024 466265658006424943 178807346473 466888145977359241 179285098669 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_768000 : DualFrontier209.checkFrom FactorFullCertificate209.phi 768000 1024 466888145977359241 179285098669 467510824238711033 179763634601 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_769024 : DualFrontier209.checkFrom FactorFullCertificate209.phi 769024 1024 467510824238711033 179763634601 468133396490626039 180242726691 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_761856 : DualFrontier209.checkFrom FactorFullCertificate209.phi 761856 8192 463153007420634441 176427985897 468133396490626039 180242726691 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 761856 463153007420634441 176427985897 463775570437637975 176902608143 7168 468133396490626039 180242726691 checked_small_761856 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 762880 463775570437637975 176902608143 464398219874975156 177377933961 6144 468133396490626039 180242726691 checked_small_762880 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 763904 464398219874975156 177377933961 465020713124042616 177853778029 5120 468133396490626039 180242726691 checked_small_763904 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 764928 465020713124042616 177853778029 465643093991858527 178330173429 4096 468133396490626039 180242726691 checked_small_764928 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 765952 465643093991858527 178330173429 466265658006424943 178807346473 3072 468133396490626039 180242726691 checked_small_765952 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 766976 466265658006424943 178807346473 466888145977359241 179285098669 2048 468133396490626039 180242726691 checked_small_766976 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 768000 466888145977359241 179285098669 467510824238711033 179763634601 1024 468133396490626039 180242726691 checked_small_768000 checked_small_769024)))))))
#print axioms checked_part_761856
private theorem checked_small_770048 : DualFrontier209.checkFrom FactorFullCertificate209.phi 770048 1024 468133396490626039 180242726691 468755634606336330 180722198707 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_771072 : DualFrontier209.checkFrom FactorFullCertificate209.phi 771072 1024 468755634606336330 180722198707 469378169854639376 181202537021 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_772096 : DualFrontier209.checkFrom FactorFullCertificate209.phi 772096 1024 469378169854639376 181202537021 470000921135530573 181683679849 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_773120 : DualFrontier209.checkFrom FactorFullCertificate209.phi 773120 1024 470000921135530573 181683679849 470623374870410160 182165230273 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_774144 : DualFrontier209.checkFrom FactorFullCertificate209.phi 774144 1024 470623374870410160 182165230273 471245817198083511 182647409177 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_775168 : DualFrontier209.checkFrom FactorFullCertificate209.phi 775168 1024 471245817198083511 182647409177 471868512813877775 183130421991 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_776192 : DualFrontier209.checkFrom FactorFullCertificate209.phi 776192 1024 471868512813877775 183130421991 472490851723559546 183613795391 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_777216 : DualFrontier209.checkFrom FactorFullCertificate209.phi 777216 1024 472490851723559546 183613795391 473113264301953492 184097863209 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_770048 : DualFrontier209.checkFrom FactorFullCertificate209.phi 770048 8192 468133396490626039 180242726691 473113264301953492 184097863209 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 770048 468133396490626039 180242726691 468755634606336330 180722198707 7168 473113264301953492 184097863209 checked_small_770048 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 771072 468755634606336330 180722198707 469378169854639376 181202537021 6144 473113264301953492 184097863209 checked_small_771072 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 772096 469378169854639376 181202537021 470000921135530573 181683679849 5120 473113264301953492 184097863209 checked_small_772096 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 773120 470000921135530573 181683679849 470623374870410160 182165230273 4096 473113264301953492 184097863209 checked_small_773120 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 774144 470623374870410160 182165230273 471245817198083511 182647409177 3072 473113264301953492 184097863209 checked_small_774144 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 775168 471245817198083511 182647409177 471868512813877775 183130421991 2048 473113264301953492 184097863209 checked_small_775168 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 776192 471868512813877775 183130421991 472490851723559546 183613795391 1024 473113264301953492 184097863209 checked_small_776192 checked_small_777216)))))))
#print axioms checked_part_770048
private theorem checked_small_778240 : DualFrontier209.checkFrom FactorFullCertificate209.phi 778240 1024 473113264301953492 184097863209 473735987549902574 184582810369 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_779264 : DualFrontier209.checkFrom FactorFullCertificate209.phi 779264 1024 473735987549902574 184582810369 474358368768386369 185068128527 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_780288 : DualFrontier209.checkFrom FactorFullCertificate209.phi 780288 1024 474358368768386369 185068128527 474980942938354969 185554234625 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_781312 : DualFrontier209.checkFrom FactorFullCertificate209.phi 781312 1024 474980942938354969 185554234625 475603524293324584 186040983907 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_782336 : DualFrontier209.checkFrom FactorFullCertificate209.phi 782336 1024 475603524293324584 186040983907 476225921230779582 186528226319 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_783360 : DualFrontier209.checkFrom FactorFullCertificate209.phi 783360 1024 476225921230779582 186528226319 476848540297920489 187016280177 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_784384 : DualFrontier209.checkFrom FactorFullCertificate209.phi 784384 1024 476848540297920489 187016280177 477471053797919252 187504888783 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_785408 : DualFrontier209.checkFrom FactorFullCertificate209.phi 785408 1024 477471053797919252 187504888783 478093528257690593 187994104135 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_778240 : DualFrontier209.checkFrom FactorFullCertificate209.phi 778240 8192 473113264301953492 184097863209 478093528257690593 187994104135 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 778240 473113264301953492 184097863209 473735987549902574 184582810369 7168 478093528257690593 187994104135 checked_small_778240 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 779264 473735987549902574 184582810369 474358368768386369 185068128527 6144 478093528257690593 187994104135 checked_small_779264 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 780288 474358368768386369 185068128527 474980942938354969 185554234625 5120 478093528257690593 187994104135 checked_small_780288 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 781312 474980942938354969 185554234625 475603524293324584 186040983907 4096 478093528257690593 187994104135 checked_small_781312 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 782336 475603524293324584 186040983907 476225921230779582 186528226319 3072 478093528257690593 187994104135 checked_small_782336 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 783360 476225921230779582 186528226319 476848540297920489 187016280177 2048 478093528257690593 187994104135 checked_small_783360 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 784384 476848540297920489 187016280177 477471053797919252 187504888783 1024 478093528257690593 187994104135 checked_small_784384 checked_small_785408)))))))
#print axioms checked_part_778240
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 753664 32768 458172948572179690 172654295365 478093528257690593 187994104135 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 753664 458172948572179690 172654295365 463153007420634441 176427985897 24576 478093528257690593 187994104135 checked_part_753664 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 761856 463153007420634441 176427985897 468133396490626039 180242726691 16384 478093528257690593 187994104135 checked_part_761856 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 770048 468133396490626039 180242726691 473113264301953492 184097863209 8192 478093528257690593 187994104135 checked_part_770048 checked_part_778240)))
theorem block_sound :
    (478093528257690593 = FrontierCheck209.massFloor FactorFullCertificate209.phi 786432 ∧
     187994104135 = FrontierCheck209.triangle FactorFullCertificate209.phi 786432) ∧
    ∀ t, 753664 < t → t ≤ 786432 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 753664 458172948572179690 172654295365 478093528257690593 187994104135 FullPrefix209_022.endpoint.1 FullPrefix209_022.endpoint.2 checked
theorem endpoint :
    478093528257690593 = FrontierCheck209.massFloor FactorFullCertificate209.phi 786432 ∧
    187994104135 = FrontierCheck209.triangle FactorFullCertificate209.phi 786432 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 786432) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 753664
  · exact FullPrefix209_022.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_023
