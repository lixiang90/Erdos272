module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_025

@[expose] public section
namespace JSP233.FullPrefix209_026
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_851968 : DualFrontier209.checkFrom FactorFullCertificate209.phi 851968 1024 517934589095626439 220631912747 518557289930169635 221162753005 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_852992 : DualFrontier209.checkFrom FactorFullCertificate209.phi 852992 1024 518557289930169635 221162753005 519179559299797002 221693862619 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_854016 : DualFrontier209.checkFrom FactorFullCertificate209.phi 854016 1024 519179559299797002 221693862619 519802149975453068 222225883909 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_855040 : DualFrontier209.checkFrom FactorFullCertificate209.phi 855040 1024 519802149975453068 222225883909 520424858436325211 222758643643 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_856064 : DualFrontier209.checkFrom FactorFullCertificate209.phi 856064 1024 520424858436325211 222758643643 521047195451222893 223291722863 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_857088 : DualFrontier209.checkFrom FactorFullCertificate209.phi 857088 1024 521047195451222893 223291722863 521669670084826291 223825557261 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_858112 : DualFrontier209.checkFrom FactorFullCertificate209.phi 858112 1024 521669670084826291 223825557261 522292282516601430 224360147417 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_859136 : DualFrontier209.checkFrom FactorFullCertificate209.phi 859136 1024 522292282516601430 224360147417 522914688697039891 224895197817 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_851968 : DualFrontier209.checkFrom FactorFullCertificate209.phi 851968 8192 517934589095626439 220631912747 522914688697039891 224895197817 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 851968 517934589095626439 220631912747 518557289930169635 221162753005 7168 522914688697039891 224895197817 checked_small_851968 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 852992 518557289930169635 221162753005 519179559299797002 221693862619 6144 522914688697039891 224895197817 checked_small_852992 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 854016 519179559299797002 221693862619 519802149975453068 222225883909 5120 522914688697039891 224895197817 checked_small_854016 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 855040 519802149975453068 222225883909 520424858436325211 222758643643 4096 522914688697039891 224895197817 checked_small_855040 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 856064 520424858436325211 222758643643 521047195451222893 223291722863 3072 522914688697039891 224895197817 checked_small_856064 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 857088 521047195451222893 223291722863 521669670084826291 223825557261 2048 522914688697039891 224895197817 checked_small_857088 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 858112 521669670084826291 223825557261 522292282516601430 224360147417 1024 522914688697039891 224895197817 checked_small_858112 checked_small_859136)))))))
#print axioms checked_part_851968
private theorem checked_small_860160 : DualFrontier209.checkFrom FactorFullCertificate209.phi 860160 1024 522914688697039891 224895197817 523537296981921100 225431059501 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_861184 : DualFrontier209.checkFrom FactorFullCertificate209.phi 861184 1024 523537296981921100 225431059501 524159925140219318 225967575965 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_862208 : DualFrontier209.checkFrom FactorFullCertificate209.phi 862208 1024 524159925140219318 225967575965 524782325244133915 226504533239 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_863232 : DualFrontier209.checkFrom FactorFullCertificate209.phi 863232 1024 524782325244133915 226504533239 525404760291796841 227042157941 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_864256 : DualFrontier209.checkFrom FactorFullCertificate209.phi 864256 1024 525404760291796841 227042157941 526027420429328721 227580614695 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_865280 : DualFrontier209.checkFrom FactorFullCertificate209.phi 865280 1024 526027420429328721 227580614695 526649945109520604 228119591849 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_866304 : DualFrontier209.checkFrom FactorFullCertificate209.phi 866304 1024 526649945109520604 228119591849 527272311570685290 228659069251 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_867328 : DualFrontier209.checkFrom FactorFullCertificate209.phi 867328 1024 527272311570685290 228659069251 527895034004076037 229199492909 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_860160 : DualFrontier209.checkFrom FactorFullCertificate209.phi 860160 8192 522914688697039891 224895197817 527895034004076037 229199492909 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 860160 522914688697039891 224895197817 523537296981921100 225431059501 7168 527895034004076037 229199492909 checked_small_860160 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 861184 523537296981921100 225431059501 524159925140219318 225967575965 6144 527895034004076037 229199492909 checked_small_861184 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 862208 524159925140219318 225967575965 524782325244133915 226504533239 5120 527895034004076037 229199492909 checked_small_862208 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 863232 524782325244133915 226504533239 525404760291796841 227042157941 4096 527895034004076037 229199492909 checked_small_863232 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 864256 525404760291796841 227042157941 526027420429328721 227580614695 3072 527895034004076037 229199492909 checked_small_864256 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 865280 526027420429328721 227580614695 526649945109520604 228119591849 2048 527895034004076037 229199492909 checked_small_865280 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 866304 526649945109520604 228119591849 527272311570685290 228659069251 1024 527895034004076037 229199492909 checked_small_866304 checked_small_867328)))))))
#print axioms checked_part_860160
private theorem checked_small_868352 : DualFrontier209.checkFrom FactorFullCertificate209.phi 868352 1024 527895034004076037 229199492909 528517331586185359 229740185089 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_869376 : DualFrontier209.checkFrom FactorFullCertificate209.phi 869376 1024 528517331586185359 229740185089 529139853832717656 230281709823 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_870400 : DualFrontier209.checkFrom FactorFullCertificate209.phi 870400 1024 529139853832717656 230281709823 529762549975263579 230824023557 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_871424 : DualFrontier209.checkFrom FactorFullCertificate209.phi 871424 1024 529762549975263579 230824023557 530384930065978484 231366699385 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_872448 : DualFrontier209.checkFrom FactorFullCertificate209.phi 872448 1024 530384930065978484 231366699385 531007481696349806 231910162223 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_873472 : DualFrontier209.checkFrom FactorFullCertificate209.phi 873472 1024 531007481696349806 231910162223 531630035539956307 232454264523 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_874496 : DualFrontier209.checkFrom FactorFullCertificate209.phi 874496 1024 531630035539956307 232454264523 532252463508765820 232998894157 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_875520 : DualFrontier209.checkFrom FactorFullCertificate209.phi 875520 1024 532252463508765820 232998894157 532875167379444484 233544402897 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_868352 : DualFrontier209.checkFrom FactorFullCertificate209.phi 868352 8192 527895034004076037 229199492909 532875167379444484 233544402897 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 868352 527895034004076037 229199492909 528517331586185359 229740185089 7168 532875167379444484 233544402897 checked_small_868352 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 869376 528517331586185359 229740185089 529139853832717656 230281709823 6144 532875167379444484 233544402897 checked_small_869376 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 870400 529139853832717656 230281709823 529762549975263579 230824023557 5120 532875167379444484 233544402897 checked_small_870400 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 871424 529762549975263579 230824023557 530384930065978484 231366699385 4096 532875167379444484 233544402897 checked_small_871424 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 872448 530384930065978484 231366699385 531007481696349806 231910162223 3072 532875167379444484 233544402897 checked_small_872448 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 873472 531007481696349806 231910162223 531630035539956307 232454264523 2048 532875167379444484 233544402897 checked_small_873472 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 874496 531630035539956307 232454264523 532252463508765820 232998894157 1024 532875167379444484 233544402897 checked_small_874496 checked_small_875520)))))))
#print axioms checked_part_868352
private theorem checked_small_876544 : DualFrontier209.checkFrom FactorFullCertificate209.phi 876544 1024 532875167379444484 233544402897 533497703744934034 234090402481 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_877568 : DualFrontier209.checkFrom FactorFullCertificate209.phi 877568 1024 533497703744934034 234090402481 534119930121378631 234636767215 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_878592 : DualFrontier209.checkFrom FactorFullCertificate209.phi 878592 1024 534119930121378631 234636767215 534742484306453052 235184057151 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_879616 : DualFrontier209.checkFrom FactorFullCertificate209.phi 879616 1024 534742484306453052 235184057151 535365198726898030 235732125727 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_880640 : DualFrontier209.checkFrom FactorFullCertificate209.phi 880640 1024 535365198726898030 235732125727 535987627021615728 236280579899 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_881664 : DualFrontier209.checkFrom FactorFullCertificate209.phi 881664 1024 535987627021615728 236280579899 536610083974965091 236829696641 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_882688 : DualFrontier209.checkFrom FactorFullCertificate209.phi 882688 1024 536610083974965091 236829696641 537232849769059195 237379723643 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_883712 : DualFrontier209.checkFrom FactorFullCertificate209.phi 883712 1024 537232849769059195 237379723643 537855150376802392 237929977045 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_876544 : DualFrontier209.checkFrom FactorFullCertificate209.phi 876544 8192 532875167379444484 233544402897 537855150376802392 237929977045 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 876544 532875167379444484 233544402897 533497703744934034 234090402481 7168 537855150376802392 237929977045 checked_small_876544 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 877568 533497703744934034 234090402481 534119930121378631 234636767215 6144 537855150376802392 237929977045 checked_small_877568 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 878592 534119930121378631 234636767215 534742484306453052 235184057151 5120 537855150376802392 237929977045 checked_small_878592 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 879616 534742484306453052 235184057151 535365198726898030 235732125727 4096 537855150376802392 237929977045 checked_small_879616 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 880640 535365198726898030 235732125727 535987627021615728 236280579899 3072 537855150376802392 237929977045 checked_small_880640 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 881664 535987627021615728 236280579899 536610083974965091 236829696641 2048 537855150376802392 237929977045 checked_small_881664 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 882688 536610083974965091 236829696641 537232849769059195 237379723643 1024 537855150376802392 237929977045 checked_small_882688 checked_small_883712)))))))
#print axioms checked_part_876544
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 851968 32768 517934589095626439 220631912747 537855150376802392 237929977045 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 851968 517934589095626439 220631912747 522914688697039891 224895197817 24576 537855150376802392 237929977045 checked_part_851968 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 860160 522914688697039891 224895197817 527895034004076037 229199492909 16384 537855150376802392 237929977045 checked_part_860160 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 868352 527895034004076037 229199492909 532875167379444484 233544402897 8192 537855150376802392 237929977045 checked_part_868352 checked_part_876544)))
theorem block_sound :
    (537855150376802392 = FrontierCheck209.massFloor FactorFullCertificate209.phi 884736 ∧
     237929977045 = FrontierCheck209.triangle FactorFullCertificate209.phi 884736) ∧
    ∀ t, 851968 < t → t ≤ 884736 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 851968 517934589095626439 220631912747 537855150376802392 237929977045 FullPrefix209_025.endpoint.1 FullPrefix209_025.endpoint.2 checked
theorem endpoint :
    537855150376802392 = FrontierCheck209.massFloor FactorFullCertificate209.phi 884736 ∧
    237929977045 = FrontierCheck209.triangle FactorFullCertificate209.phi 884736 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 884736) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 851968
  · exact FullPrefix209_025.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_026
