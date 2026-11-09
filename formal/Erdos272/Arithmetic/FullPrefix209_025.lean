module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_024

@[expose] public section
namespace JSP233.FullPrefix209_025
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_819200 : DualFrontier209.checkFrom FactorFullCertificate209.phi 819200 1024 498014225086146402 203986767209 498636705473038196 204497022185 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_820224 : DualFrontier209.checkFrom FactorFullCertificate209.phi 820224 1024 498636705473038196 204497022185 499259116635342748 205007857687 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_821248 : DualFrontier209.checkFrom FactorFullCertificate209.phi 821248 1024 499259116635342748 205007857687 499881761504806242 205519522611 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_822272 : DualFrontier209.checkFrom FactorFullCertificate209.phi 822272 1024 499881761504806242 205519522611 500504000402665018 206031491015 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_823296 : DualFrontier209.checkFrom FactorFullCertificate209.phi 823296 1024 500504000402665018 206031491015 501126510826094565 206544320127 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_824320 : DualFrontier209.checkFrom FactorFullCertificate209.phi 824320 1024 501126510826094565 206544320127 501749305518504989 207058021303 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_825344 : DualFrontier209.checkFrom FactorFullCertificate209.phi 825344 1024 501749305518504989 207058021303 502371654804657282 207571992433 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_826368 : DualFrontier209.checkFrom FactorFullCertificate209.phi 826368 1024 502371654804657282 207571992433 502994258138575402 208086810873 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_819200 : DualFrontier209.checkFrom FactorFullCertificate209.phi 819200 8192 498014225086146402 203986767209 502994258138575402 208086810873 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 819200 498014225086146402 203986767209 498636705473038196 204497022185 7168 502994258138575402 208086810873 checked_small_819200 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 820224 498636705473038196 204497022185 499259116635342748 205007857687 6144 502994258138575402 208086810873 checked_small_820224 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 821248 499259116635342748 205007857687 499881761504806242 205519522611 5120 502994258138575402 208086810873 checked_small_821248 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 822272 499881761504806242 205519522611 500504000402665018 206031491015 4096 502994258138575402 208086810873 checked_small_822272 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 823296 500504000402665018 206031491015 501126510826094565 206544320127 3072 502994258138575402 208086810873 checked_small_823296 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 824320 501126510826094565 206544320127 501749305518504989 207058021303 2048 502994258138575402 208086810873 checked_small_824320 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 825344 501749305518504989 207058021303 502371654804657282 207571992433 1024 502994258138575402 208086810873 checked_small_825344 checked_small_826368)))))))
#print axioms checked_part_819200
private theorem checked_small_827392 : DualFrontier209.checkFrom FactorFullCertificate209.phi 827392 1024 502994258138575402 208086810873 503616794736981387 208602211665 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_828416 : DualFrontier209.checkFrom FactorFullCertificate209.phi 828416 1024 503616794736981387 208602211665 504239133891274282 209118086187 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_829440 : DualFrontier209.checkFrom FactorFullCertificate209.phi 829440 1024 504239133891274282 209118086187 504861858721264627 209634918093 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_830464 : DualFrontier209.checkFrom FactorFullCertificate209.phi 830464 1024 504861858721264627 209634918093 505484332358464568 210152179013 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_831488 : DualFrontier209.checkFrom FactorFullCertificate209.phi 831488 1024 505484332358464568 210152179013 506106755165952145 210670034985 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_832512 : DualFrontier209.checkFrom FactorFullCertificate209.phi 832512 1024 506106755165952145 210670034985 506729257867689474 211188594817 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_833536 : DualFrontier209.checkFrom FactorFullCertificate209.phi 833536 1024 506729257867689474 211188594817 507351923451761090 211707928011 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_834560 : DualFrontier209.checkFrom FactorFullCertificate209.phi 834560 1024 507351923451761090 211707928011 507974274940932230 212227636517 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_827392 : DualFrontier209.checkFrom FactorFullCertificate209.phi 827392 8192 502994258138575402 208086810873 507974274940932230 212227636517 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 827392 502994258138575402 208086810873 503616794736981387 208602211665 7168 507974274940932230 212227636517 checked_small_827392 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 828416 503616794736981387 208602211665 504239133891274282 209118086187 6144 507974274940932230 212227636517 checked_small_828416 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 829440 504239133891274282 209118086187 504861858721264627 209634918093 5120 507974274940932230 212227636517 checked_small_829440 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 830464 504861858721264627 209634918093 505484332358464568 210152179013 4096 507974274940932230 212227636517 checked_small_830464 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 831488 505484332358464568 210152179013 506106755165952145 210670034985 3072 507974274940932230 212227636517 checked_small_831488 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 832512 506106755165952145 210670034985 506729257867689474 211188594817 2048 507974274940932230 212227636517 checked_small_832512 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 833536 506729257867689474 211188594817 507351923451761090 211707928011 1024 507974274940932230 212227636517 checked_small_833536 checked_small_834560)))))))
#print axioms checked_part_827392
private theorem checked_small_835584 : DualFrontier209.checkFrom FactorFullCertificate209.phi 835584 1024 507974274940932230 212227636517 508596753686844647 212748088603 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_836608 : DualFrontier209.checkFrom FactorFullCertificate209.phi 836608 1024 508596753686844647 212748088603 509219570913314446 213269461591 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_837632 : DualFrontier209.checkFrom FactorFullCertificate209.phi 837632 1024 509219570913314446 213269461591 509841729989250895 213790920691 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_838656 : DualFrontier209.checkFrom FactorFullCertificate209.phi 838656 1024 509841729989250895 213790920691 510464370903274247 214313421103 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_839680 : DualFrontier209.checkFrom FactorFullCertificate209.phi 839680 1024 510464370903274247 214313421103 511087117699536879 214836648243 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_840704 : DualFrontier209.checkFrom FactorFullCertificate209.phi 840704 1024 511087117699536879 214836648243 511709494718299832 215360202057 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_841728 : DualFrontier209.checkFrom FactorFullCertificate209.phi 841728 1024 511709494718299832 215360202057 512331911914487732 215884426903 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_842752 : DualFrontier209.checkFrom FactorFullCertificate209.phi 842752 1024 512331911914487732 215884426903 512954597835576959 216409515743 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_835584 : DualFrontier209.checkFrom FactorFullCertificate209.phi 835584 8192 507974274940932230 212227636517 512954597835576959 216409515743 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 835584 507974274940932230 212227636517 508596753686844647 212748088603 7168 512954597835576959 216409515743 checked_small_835584 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 836608 508596753686844647 212748088603 509219570913314446 213269461591 6144 512954597835576959 216409515743 checked_small_836608 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 837632 509219570913314446 213269461591 509841729989250895 213790920691 5120 512954597835576959 216409515743 checked_small_837632 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 838656 509841729989250895 213790920691 510464370903274247 214313421103 4096 512954597835576959 216409515743 checked_small_838656 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 839680 510464370903274247 214313421103 511087117699536879 214836648243 3072 512954597835576959 216409515743 checked_small_839680 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 840704 511087117699536879 214836648243 511709494718299832 215360202057 2048 512954597835576959 216409515743 checked_small_840704 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 841728 511709494718299832 215360202057 512331911914487732 215884426903 1024 512954597835576959 216409515743 checked_small_841728 checked_small_842752)))))))
#print axioms checked_part_835584
private theorem checked_small_843776 : DualFrontier209.checkFrom FactorFullCertificate209.phi 843776 1024 512954597835576959 216409515743 513576940815975470 216934952673 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_844800 : DualFrontier209.checkFrom FactorFullCertificate209.phi 844800 1024 513576940815975470 216934952673 514199485587817294 217461197383 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_845824 : DualFrontier209.checkFrom FactorFullCertificate209.phi 845824 1024 514199485587817294 217461197383 514822157997735584 217988187697 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_846848 : DualFrontier209.checkFrom FactorFullCertificate209.phi 846848 1024 514822157997735584 217988187697 515444597543574609 218515618345 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_847872 : DualFrontier209.checkFrom FactorFullCertificate209.phi 847872 1024 515444597543574609 218515618345 516067070714303913 219043714839 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_848896 : DualFrontier209.checkFrom FactorFullCertificate209.phi 848896 1024 516067070714303913 219043714839 516689610706884307 219572505489 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_849920 : DualFrontier209.checkFrom FactorFullCertificate209.phi 849920 1024 516689610706884307 219572505489 517312171290095703 220101951165 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_850944 : DualFrontier209.checkFrom FactorFullCertificate209.phi 850944 1024 517312171290095703 220101951165 517934589095626439 220631912747 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_843776 : DualFrontier209.checkFrom FactorFullCertificate209.phi 843776 8192 512954597835576959 216409515743 517934589095626439 220631912747 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 843776 512954597835576959 216409515743 513576940815975470 216934952673 7168 517934589095626439 220631912747 checked_small_843776 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 844800 513576940815975470 216934952673 514199485587817294 217461197383 6144 517934589095626439 220631912747 checked_small_844800 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 845824 514199485587817294 217461197383 514822157997735584 217988187697 5120 517934589095626439 220631912747 checked_small_845824 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 846848 514822157997735584 217988187697 515444597543574609 218515618345 4096 517934589095626439 220631912747 checked_small_846848 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 847872 515444597543574609 218515618345 516067070714303913 219043714839 3072 517934589095626439 220631912747 checked_small_847872 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 848896 516067070714303913 219043714839 516689610706884307 219572505489 2048 517934589095626439 220631912747 checked_small_848896 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 849920 516689610706884307 219572505489 517312171290095703 220101951165 1024 517934589095626439 220631912747 checked_small_849920 checked_small_850944)))))))
#print axioms checked_part_843776
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 819200 32768 498014225086146402 203986767209 517934589095626439 220631912747 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 819200 498014225086146402 203986767209 502994258138575402 208086810873 24576 517934589095626439 220631912747 checked_part_819200 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 827392 502994258138575402 208086810873 507974274940932230 212227636517 16384 517934589095626439 220631912747 checked_part_827392 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 835584 507974274940932230 212227636517 512954597835576959 216409515743 8192 517934589095626439 220631912747 checked_part_835584 checked_part_843776)))
theorem block_sound :
    (517934589095626439 = FrontierCheck209.massFloor FactorFullCertificate209.phi 851968 ∧
     220631912747 = FrontierCheck209.triangle FactorFullCertificate209.phi 851968) ∧
    ∀ t, 819200 < t → t ≤ 851968 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 819200 498014225086146402 203986767209 517934589095626439 220631912747 FullPrefix209_024.endpoint.1 FullPrefix209_024.endpoint.2 checked
theorem endpoint :
    517934589095626439 = FrontierCheck209.massFloor FactorFullCertificate209.phi 851968 ∧
    220631912747 = FrontierCheck209.triangle FactorFullCertificate209.phi 851968 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 851968) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 819200
  · exact FullPrefix209_024.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_025
