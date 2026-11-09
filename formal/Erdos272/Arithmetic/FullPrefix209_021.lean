module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_020

@[expose] public section
namespace JSP233.FullPrefix209_021
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_688128 : DualFrontier209.checkFrom FactorFullCertificate209.phi 688128 1024 418331783688948533 143932949127 418954357018753402 144361678183 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_689152 : DualFrontier209.checkFrom FactorFullCertificate209.phi 689152 1024 418954357018753402 144361678183 419576928543638456 144791043557 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_690176 : DualFrontier209.checkFrom FactorFullCertificate209.phi 690176 1024 419576928543638456 144791043557 420199425572701179 145220995017 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_691200 : DualFrontier209.checkFrom FactorFullCertificate209.phi 691200 1024 420199425572701179 145220995017 420821914582195936 145651578345 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_692224 : DualFrontier209.checkFrom FactorFullCertificate209.phi 692224 1024 420821914582195936 145651578345 421444602218125836 146082936759 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_693248 : DualFrontier209.checkFrom FactorFullCertificate209.phi 693248 1024 421444602218125836 146082936759 422066926601309948 146514680791 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_694272 : DualFrontier209.checkFrom FactorFullCertificate209.phi 694272 1024 422066926601309948 146514680791 422689428175769096 146947185077 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_695296 : DualFrontier209.checkFrom FactorFullCertificate209.phi 695296 1024 422689428175769096 146947185077 423312037832522132 147380402055 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_688128 : DualFrontier209.checkFrom FactorFullCertificate209.phi 688128 8192 418331783688948533 143932949127 423312037832522132 147380402055 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 688128 418331783688948533 143932949127 418954357018753402 144361678183 7168 423312037832522132 147380402055 checked_small_688128 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 689152 418954357018753402 144361678183 419576928543638456 144791043557 6144 423312037832522132 147380402055 checked_small_689152 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 690176 419576928543638456 144791043557 420199425572701179 145220995017 5120 423312037832522132 147380402055 checked_small_690176 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 691200 420199425572701179 145220995017 420821914582195936 145651578345 4096 423312037832522132 147380402055 checked_small_691200 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 692224 420821914582195936 145651578345 421444602218125836 146082936759 3072 423312037832522132 147380402055 checked_small_692224 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 693248 421444602218125836 146082936759 422066926601309948 146514680791 2048 423312037832522132 147380402055 checked_small_693248 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 694272 422066926601309948 146514680791 422689428175769096 146947185077 1024 423312037832522132 147380402055 checked_small_694272 checked_small_695296)))))))
#print axioms checked_part_688128
private theorem checked_small_696320 : DualFrontier209.checkFrom FactorFullCertificate209.phi 696320 1024 423312037832522132 147380402055 423934580034573432 147814209637 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_697344 : DualFrontier209.checkFrom FactorFullCertificate209.phi 697344 1024 423934580034573432 147814209637 424557033158602376 148248592517 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_698368 : DualFrontier209.checkFrom FactorFullCertificate209.phi 698368 1024 424557033158602376 148248592517 425179635537951097 148683717115 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_699392 : DualFrontier209.checkFrom FactorFullCertificate209.phi 699392 1024 425179635537951097 148683717115 425801938714368076 149119269781 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_700416 : DualFrontier209.checkFrom FactorFullCertificate209.phi 700416 1024 425801938714368076 149119269781 426424457183138839 149555610483 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_701440 : DualFrontier209.checkFrom FactorFullCertificate209.phi 701440 1024 426424457183138839 149555610483 427047223207342141 149992762543 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_702464 : DualFrontier209.checkFrom FactorFullCertificate209.phi 702464 1024 427047223207342141 149992762543 427669573372949493 150430260013 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_703488 : DualFrontier209.checkFrom FactorFullCertificate209.phi 703488 1024 427669573372949493 150430260013 428292124131088355 150868535921 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_696320 : DualFrontier209.checkFrom FactorFullCertificate209.phi 696320 8192 423312037832522132 147380402055 428292124131088355 150868535921 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 696320 423312037832522132 147380402055 423934580034573432 147814209637 7168 428292124131088355 150868535921 checked_small_696320 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 697344 423934580034573432 147814209637 424557033158602376 148248592517 6144 428292124131088355 150868535921 checked_small_697344 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 698368 424557033158602376 148248592517 425179635537951097 148683717115 5120 428292124131088355 150868535921 checked_small_698368 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 699392 425179635537951097 148683717115 425801938714368076 149119269781 4096 428292124131088355 150868535921 checked_small_699392 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 700416 425801938714368076 149119269781 426424457183138839 149555610483 3072 428292124131088355 150868535921 checked_small_700416 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 701440 426424457183138839 149555610483 427047223207342141 149992762543 2048 428292124131088355 150868535921 checked_small_701440 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 702464 427047223207342141 149992762543 427669573372949493 150430260013 1024 428292124131088355 150868535921 checked_small_702464 checked_small_703488)))))))
#print axioms checked_part_696320
private theorem checked_small_704512 : DualFrontier209.checkFrom FactorFullCertificate209.phi 704512 1024 428292124131088355 150868535921 428914702289078359 151307468681 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_705536 : DualFrontier209.checkFrom FactorFullCertificate209.phi 705536 1024 428914702289078359 151307468681 429537059053961210 151746882603 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_706560 : DualFrontier209.checkFrom FactorFullCertificate209.phi 706560 1024 429537059053961210 151746882603 430159719356079254 152187148429 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_707584 : DualFrontier209.checkFrom FactorFullCertificate209.phi 707584 1024 430159719356079254 152187148429 430782377229634794 152628050283 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_708608 : DualFrontier209.checkFrom FactorFullCertificate209.phi 708608 1024 430782377229634794 152628050283 431404521826383545 153069225645 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_709632 : DualFrontier209.checkFrom FactorFullCertificate209.phi 709632 1024 431404521826383545 153069225645 432027150314830446 153511381585 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_710656 : DualFrontier209.checkFrom FactorFullCertificate209.phi 710656 1024 432027150314830446 153511381585 432649914127167717 153954271511 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_711680 : DualFrontier209.checkFrom FactorFullCertificate209.phi 711680 1024 432649914127167717 153954271511 433272311897960573 154397538523 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_704512 : DualFrontier209.checkFrom FactorFullCertificate209.phi 704512 8192 428292124131088355 150868535921 433272311897960573 154397538523 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 704512 428292124131088355 150868535921 428914702289078359 151307468681 7168 433272311897960573 154397538523 checked_small_704512 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 705536 428914702289078359 151307468681 429537059053961210 151746882603 6144 433272311897960573 154397538523 checked_small_705536 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 706560 429537059053961210 151746882603 430159719356079254 152187148429 5120 433272311897960573 154397538523 checked_small_706560 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 707584 430159719356079254 152187148429 430782377229634794 152628050283 4096 433272311897960573 154397538523 checked_small_707584 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 708608 430782377229634794 152628050283 431404521826383545 153069225645 3072 433272311897960573 154397538523 checked_small_708608 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 709632 431404521826383545 153069225645 432027150314830446 153511381585 2048 433272311897960573 154397538523 checked_small_709632 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 710656 432027150314830446 153511381585 432649914127167717 153954271511 1024 433272311897960573 154397538523 checked_small_710656 checked_small_711680)))))))
#print axioms checked_part_704512
private theorem checked_small_712704 : DualFrontier209.checkFrom FactorFullCertificate209.phi 712704 1024 433272311897960573 154397538523 433894666474776240 154841411921 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_713728 : DualFrontier209.checkFrom FactorFullCertificate209.phi 713728 1024 433894666474776240 154841411921 434517460104971325 155286236259 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_714752 : DualFrontier209.checkFrom FactorFullCertificate209.phi 714752 1024 434517460104971325 155286236259 435139734797558969 155731327177 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_715776 : DualFrontier209.checkFrom FactorFullCertificate209.phi 715776 1024 435139734797558969 155731327177 435762256345836405 156177231999 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_716800 : DualFrontier209.checkFrom FactorFullCertificate209.phi 716800 1024 435762256345836405 156177231999 436385078576586738 156623990127 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_717824 : DualFrontier209.checkFrom FactorFullCertificate209.phi 717824 1024 436385078576586738 156623990127 437007353351692981 157070992799 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_718848 : DualFrontier209.checkFrom FactorFullCertificate209.phi 718848 1024 437007353351692981 157070992799 437629947344522619 157518862233 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_719872 : DualFrontier209.checkFrom FactorFullCertificate209.phi 719872 1024 437629947344522619 157518862233 438252410682460218 157967275095 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_712704 : DualFrontier209.checkFrom FactorFullCertificate209.phi 712704 8192 433272311897960573 154397538523 438252410682460218 157967275095 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 712704 433272311897960573 154397538523 433894666474776240 154841411921 7168 438252410682460218 157967275095 checked_small_712704 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 713728 433894666474776240 154841411921 434517460104971325 155286236259 6144 438252410682460218 157967275095 checked_small_713728 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 714752 434517460104971325 155286236259 435139734797558969 155731327177 5120 438252410682460218 157967275095 checked_small_714752 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 715776 435139734797558969 155731327177 435762256345836405 156177231999 4096 438252410682460218 157967275095 checked_small_715776 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 716800 435762256345836405 156177231999 436385078576586738 156623990127 3072 438252410682460218 157967275095 checked_small_716800 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 717824 436385078576586738 156623990127 437007353351692981 157070992799 2048 438252410682460218 157967275095 checked_small_717824 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 718848 437007353351692981 157070992799 437629947344522619 157518862233 1024 438252410682460218 157967275095 checked_small_718848 checked_small_719872)))))))
#print axioms checked_part_712704
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 688128 32768 418331783688948533 143932949127 438252410682460218 157967275095 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 688128 418331783688948533 143932949127 423312037832522132 147380402055 24576 438252410682460218 157967275095 checked_part_688128 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 696320 423312037832522132 147380402055 428292124131088355 150868535921 16384 438252410682460218 157967275095 checked_part_696320 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 704512 428292124131088355 150868535921 433272311897960573 154397538523 8192 438252410682460218 157967275095 checked_part_704512 checked_part_712704)))
theorem block_sound :
    (438252410682460218 = FrontierCheck209.massFloor FactorFullCertificate209.phi 720896 ∧
     157967275095 = FrontierCheck209.triangle FactorFullCertificate209.phi 720896) ∧
    ∀ t, 688128 < t → t ≤ 720896 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 688128 418331783688948533 143932949127 438252410682460218 157967275095 FullPrefix209_020.endpoint.1 FullPrefix209_020.endpoint.2 checked
theorem endpoint :
    438252410682460218 = FrontierCheck209.massFloor FactorFullCertificate209.phi 720896 ∧
    157967275095 = FrontierCheck209.triangle FactorFullCertificate209.phi 720896 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 720896) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 688128
  · exact FullPrefix209_020.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_021
