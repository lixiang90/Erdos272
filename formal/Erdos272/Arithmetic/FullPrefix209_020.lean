module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_019

@[expose] public section
namespace JSP233.FullPrefix209_020
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_655360 : DualFrontier209.checkFrom FactorFullCertificate209.phi 655360 1024 398411321728698376 130551492759 399033935359721912 130959847877 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_656384 : DualFrontier209.checkFrom FactorFullCertificate209.phi 656384 1024 399033935359721912 130959847877 399656310461838349 131368683841 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_657408 : DualFrontier209.checkFrom FactorFullCertificate209.phi 657408 1024 399656310461838349 131368683841 400278809557626045 131778238613 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_658432 : DualFrontier209.checkFrom FactorFullCertificate209.phi 658432 1024 400278809557626045 131778238613 400901385217924390 132188481293 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_659456 : DualFrontier209.checkFrom FactorFullCertificate209.phi 659456 1024 400901385217924390 132188481293 401523798385028173 132599254231 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_660480 : DualFrontier209.checkFrom FactorFullCertificate209.phi 660480 1024 401523798385028173 132599254231 402146504079767338 133010857915 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_661504 : DualFrontier209.checkFrom FactorFullCertificate209.phi 661504 1024 402146504079767338 133010857915 402769052197335843 133422995049 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_662528 : DualFrontier209.checkFrom FactorFullCertificate209.phi 662528 1024 402769052197335843 133422995049 403391364740627922 133835613387 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_655360 : DualFrontier209.checkFrom FactorFullCertificate209.phi 655360 8192 398411321728698376 130551492759 403391364740627922 133835613387 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 655360 398411321728698376 130551492759 399033935359721912 130959847877 7168 403391364740627922 133835613387 checked_small_655360 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 656384 399033935359721912 130959847877 399656310461838349 131368683841 6144 403391364740627922 133835613387 checked_small_656384 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 657408 399656310461838349 131368683841 400278809557626045 131778238613 5120 403391364740627922 133835613387 checked_small_657408 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 658432 400278809557626045 131778238613 400901385217924390 132188481293 4096 403391364740627922 133835613387 checked_small_658432 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 659456 400901385217924390 132188481293 401523798385028173 132599254231 3072 403391364740627922 133835613387 checked_small_659456 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 660480 401523798385028173 132599254231 402146504079767338 133010857915 2048 403391364740627922 133835613387 checked_small_660480 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 661504 402146504079767338 133010857915 402769052197335843 133422995049 1024 403391364740627922 133835613387 checked_small_661504 checked_small_662528)))))))
#print axioms checked_part_655360
private theorem checked_small_663552 : DualFrontier209.checkFrom FactorFullCertificate209.phi 663552 1024 403391364740627922 133835613387 404013779648325829 134248936793 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_664576 : DualFrontier209.checkFrom FactorFullCertificate209.phi 664576 1024 404013779648325829 134248936793 404636551031023691 134663134711 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_665600 : DualFrontier209.checkFrom FactorFullCertificate209.phi 665600 1024 404636551031023691 134663134711 405258953698825410 135077724817 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_666624 : DualFrontier209.checkFrom FactorFullCertificate209.phi 666624 1024 405258953698825410 135077724817 405881373743861152 135492963749 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_667648 : DualFrontier209.checkFrom FactorFullCertificate209.phi 667648 1024 405881373743861152 135492963749 406504175524461871 135909095191 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_668672 : DualFrontier209.checkFrom FactorFullCertificate209.phi 668672 1024 406504175524461871 135909095191 407126460831518642 136325518799 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_669696 : DualFrontier209.checkFrom FactorFullCertificate209.phi 669696 1024 407126460831518642 136325518799 407748908049210942 136742687985 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_670720 : DualFrontier209.checkFrom FactorFullCertificate209.phi 670720 1024 407748908049210942 136742687985 408371718797674177 137160738683 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_663552 : DualFrontier209.checkFrom FactorFullCertificate209.phi 663552 8192 403391364740627922 133835613387 408371718797674177 137160738683 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 663552 403391364740627922 133835613387 404013779648325829 134248936793 7168 408371718797674177 137160738683 checked_small_663552 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 664576 404013779648325829 134248936793 404636551031023691 134663134711 6144 408371718797674177 137160738683 checked_small_664576 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 665600 404636551031023691 134663134711 405258953698825410 135077724817 5120 408371718797674177 137160738683 checked_small_665600 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 666624 405258953698825410 135077724817 405881373743861152 135492963749 4096 408371718797674177 137160738683 checked_small_666624 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 667648 405881373743861152 135492963749 406504175524461871 135909095191 3072 408371718797674177 137160738683 checked_small_667648 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 668672 406504175524461871 135909095191 407126460831518642 136325518799 2048 408371718797674177 137160738683 checked_small_668672 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 669696 407126460831518642 136325518799 407748908049210942 136742687985 1024 408371718797674177 137160738683 checked_small_669696 checked_small_670720)))))))
#print axioms checked_part_663552
private theorem checked_small_671744 : DualFrontier209.checkFrom FactorFullCertificate209.phi 671744 1024 408371718797674177 137160738683 408994128724669253 137579157781 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_672768 : DualFrontier209.checkFrom FactorFullCertificate209.phi 672768 1024 408994128724669253 137579157781 409616570484677537 137998235563 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_673792 : DualFrontier209.checkFrom FactorFullCertificate209.phi 673792 1024 409616570484677537 137998235563 410239260089829064 138418117901 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_674816 : DualFrontier209.checkFrom FactorFullCertificate209.phi 674816 1024 410239260089829064 138418117901 410861590081747346 138838395007 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_675840 : DualFrontier209.checkFrom FactorFullCertificate209.phi 675840 1024 410861590081747346 138838395007 411484223946903840 139259514869 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_676864 : DualFrontier209.checkFrom FactorFullCertificate209.phi 676864 1024 411484223946903840 139259514869 412106703759518408 139681167993 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_677888 : DualFrontier209.checkFrom FactorFullCertificate209.phi 677888 1024 412106703759518408 139681167993 412729164379969499 140103445475 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_678912 : DualFrontier209.checkFrom FactorFullCertificate209.phi 678912 1024 412729164379969499 140103445475 413351686526438501 140526402133 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_671744 : DualFrontier209.checkFrom FactorFullCertificate209.phi 671744 8192 408371718797674177 137160738683 413351686526438501 140526402133 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 671744 408371718797674177 137160738683 408994128724669253 137579157781 7168 413351686526438501 140526402133 checked_small_671744 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 672768 408994128724669253 137579157781 409616570484677537 137998235563 6144 413351686526438501 140526402133 checked_small_672768 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 673792 409616570484677537 137998235563 410239260089829064 138418117901 5120 413351686526438501 140526402133 checked_small_673792 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 674816 410239260089829064 138418117901 410861590081747346 138838395007 4096 413351686526438501 140526402133 checked_small_674816 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 675840 410861590081747346 138838395007 411484223946903840 139259514869 3072 413351686526438501 140526402133 checked_small_675840 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 676864 411484223946903840 139259514869 412106703759518408 139681167993 2048 413351686526438501 140526402133 checked_small_676864 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 677888 412106703759518408 139681167993 412729164379969499 140103445475 1024 413351686526438501 140526402133 checked_small_677888 checked_small_678912)))))))
#print axioms checked_part_671744
private theorem checked_small_679936 : DualFrontier209.checkFrom FactorFullCertificate209.phi 679936 1024 413351686526438501 140526402133 413974292091614525 140950053055 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_680960 : DualFrontier209.checkFrom FactorFullCertificate209.phi 680960 1024 413974292091614525 140950053055 414596832514631125 141374297193 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_681984 : DualFrontier209.checkFrom FactorFullCertificate209.phi 681984 1024 414596832514631125 141374297193 415219240496730495 141799088375 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_683008 : DualFrontier209.checkFrom FactorFullCertificate209.phi 683008 1024 415219240496730495 141799088375 415841997833643070 142224755769 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_684032 : DualFrontier209.checkFrom FactorFullCertificate209.phi 684032 1024 415841997833643070 142224755769 416464185777564638 142650671039 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_685056 : DualFrontier209.checkFrom FactorFullCertificate209.phi 685056 1024 416464185777564638 142650671039 417086728495600462 143077466495 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_686080 : DualFrontier209.checkFrom FactorFullCertificate209.phi 686080 1024 417086728495600462 143077466495 417709467059035603 143505034033 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_687104 : DualFrontier209.checkFrom FactorFullCertificate209.phi 687104 1024 417709467059035603 143505034033 418331783688948533 143932949127 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_679936 : DualFrontier209.checkFrom FactorFullCertificate209.phi 679936 8192 413351686526438501 140526402133 418331783688948533 143932949127 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 679936 413351686526438501 140526402133 413974292091614525 140950053055 7168 418331783688948533 143932949127 checked_small_679936 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 680960 413974292091614525 140950053055 414596832514631125 141374297193 6144 418331783688948533 143932949127 checked_small_680960 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 681984 414596832514631125 141374297193 415219240496730495 141799088375 5120 418331783688948533 143932949127 checked_small_681984 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 683008 415219240496730495 141799088375 415841997833643070 142224755769 4096 418331783688948533 143932949127 checked_small_683008 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 684032 415841997833643070 142224755769 416464185777564638 142650671039 3072 418331783688948533 143932949127 checked_small_684032 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 685056 416464185777564638 142650671039 417086728495600462 143077466495 2048 418331783688948533 143932949127 checked_small_685056 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 686080 417086728495600462 143077466495 417709467059035603 143505034033 1024 418331783688948533 143932949127 checked_small_686080 checked_small_687104)))))))
#print axioms checked_part_679936
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 655360 32768 398411321728698376 130551492759 418331783688948533 143932949127 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 655360 398411321728698376 130551492759 403391364740627922 133835613387 24576 418331783688948533 143932949127 checked_part_655360 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 663552 403391364740627922 133835613387 408371718797674177 137160738683 16384 418331783688948533 143932949127 checked_part_663552 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 671744 408371718797674177 137160738683 413351686526438501 140526402133 8192 418331783688948533 143932949127 checked_part_671744 checked_part_679936)))
theorem block_sound :
    (418331783688948533 = FrontierCheck209.massFloor FactorFullCertificate209.phi 688128 ∧
     143932949127 = FrontierCheck209.triangle FactorFullCertificate209.phi 688128) ∧
    ∀ t, 655360 < t → t ≤ 688128 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 655360 398411321728698376 130551492759 418331783688948533 143932949127 FullPrefix209_019.endpoint.1 FullPrefix209_019.endpoint.2 checked
theorem endpoint :
    418331783688948533 = FrontierCheck209.massFloor FactorFullCertificate209.phi 688128 ∧
    143932949127 = FrontierCheck209.triangle FactorFullCertificate209.phi 688128 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 688128) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 655360
  · exact FullPrefix209_019.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_020
