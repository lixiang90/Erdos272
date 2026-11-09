module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_029

@[expose] public section
namespace JSP233.FullPrefix209_030
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_983040 : DualFrontier209.checkFrom FactorFullCertificate209.phi 983040 1024 597616831487308745 293740710159 598239409304091049 294353048025 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_984064 : DualFrontier209.checkFrom FactorFullCertificate209.phi 984064 1024 598239409304091049 294353048025 598862023891887591 294966059697 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_985088 : DualFrontier209.checkFrom FactorFullCertificate209.phi 985088 1024 598862023891887591 294966059697 599484373992598499 295579448209 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_986112 : DualFrontier209.checkFrom FactorFullCertificate209.phi 986112 1024 599484373992598499 295579448209 600106857048581677 296193605081 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_987136 : DualFrontier209.checkFrom FactorFullCertificate209.phi 987136 1024 600106857048581677 296193605081 600729567425228182 296808623969 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_988160 : DualFrontier209.checkFrom FactorFullCertificate209.phi 988160 1024 600729567425228182 296808623969 601351949955456563 297423956411 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_989184 : DualFrontier209.checkFrom FactorFullCertificate209.phi 989184 1024 601351949955456563 297423956411 601974407220432465 298040000043 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_990208 : DualFrontier209.checkFrom FactorFullCertificate209.phi 990208 1024 601974407220432465 298040000043 602597143753257378 298656957823 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_983040 : DualFrontier209.checkFrom FactorFullCertificate209.phi 983040 8192 597616831487308745 293740710159 602597143753257378 298656957823 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 983040 597616831487308745 293740710159 598239409304091049 294353048025 7168 602597143753257378 298656957823 checked_small_983040 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 984064 598239409304091049 294353048025 598862023891887591 294966059697 6144 602597143753257378 298656957823 checked_small_984064 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 985088 598862023891887591 294966059697 599484373992598499 295579448209 5120 602597143753257378 298656957823 checked_small_985088 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 986112 599484373992598499 295579448209 600106857048581677 296193605081 4096 602597143753257378 298656957823 checked_small_986112 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 987136 600106857048581677 296193605081 600729567425228182 296808623969 3072 602597143753257378 298656957823 checked_small_987136 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 988160 600729567425228182 296808623969 601351949955456563 297423956411 2048 602597143753257378 298656957823 checked_small_988160 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 989184 601351949955456563 297423956411 601974407220432465 298040000043 1024 602597143753257378 298656957823 checked_small_989184 checked_small_990208)))))))
#print axioms checked_part_983040
private theorem checked_small_991232 : DualFrontier209.checkFrom FactorFullCertificate209.phi 991232 1024 602597143753257378 298656957823 603219389994454707 299274067017 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_992256 : DualFrontier209.checkFrom FactorFullCertificate209.phi 992256 1024 603219389994454707 299274067017 603841852098611903 299892027523 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_993280 : DualFrontier209.checkFrom FactorFullCertificate209.phi 993280 1024 603841852098611903 299892027523 604464675958378448 300510985073 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_994304 : DualFrontier209.checkFrom FactorFullCertificate209.phi 994304 1024 604464675958378448 300510985073 605087009805202333 301130092979 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_995328 : DualFrontier209.checkFrom FactorFullCertificate209.phi 995328 1024 605087009805202333 301130092979 605709590015014489 301750083437 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_996352 : DualFrontier209.checkFrom FactorFullCertificate209.phi 996352 1024 605709590015014489 301750083437 606332109249567914 302370650667 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_997376 : DualFrontier209.checkFrom FactorFullCertificate209.phi 997376 1024 606332109249567914 302370650667 606954530866261203 302991757893 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_998400 : DualFrontier209.checkFrom FactorFullCertificate209.phi 998400 1024 606954530866261203 302991757893 607577204088389718 303613753841 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_991232 : DualFrontier209.checkFrom FactorFullCertificate209.phi 991232 8192 602597143753257378 298656957823 607577204088389718 303613753841 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 991232 602597143753257378 298656957823 603219389994454707 299274067017 7168 607577204088389718 303613753841 checked_small_991232 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 992256 603219389994454707 299274067017 603841852098611903 299892027523 6144 607577204088389718 303613753841 checked_small_992256 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 993280 603841852098611903 299892027523 604464675958378448 300510985073 5120 607577204088389718 303613753841 checked_small_993280 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 994304 604464675958378448 300510985073 605087009805202333 301130092979 4096 607577204088389718 303613753841 checked_small_994304 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 995328 605087009805202333 301130092979 605709590015014489 301750083437 3072 607577204088389718 303613753841 checked_small_995328 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 996352 605709590015014489 301750083437 606332109249567914 302370650667 2048 607577204088389718 303613753841 checked_small_996352 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 997376 606332109249567914 302370650667 606954530866261203 302991757893 1024 607577204088389718 303613753841 checked_small_997376 checked_small_998400)))))))
#print axioms checked_part_991232
private theorem checked_small_999424 : DualFrontier209.checkFrom FactorFullCertificate209.phi 999424 1024 607577204088389718 303613753841 608199691712900824 304236201889 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1000448 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1000448 1024 608199691712900824 304236201889 608822148829445149 304859256785 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1001472 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1001472 1024 608822148829445149 304859256785 609444601171284110 305482944221 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1002496 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1002496 1024 609444601171284110 305482944221 610067253293894223 306107469463 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1003520 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1003520 1024 610067253293894223 306107469463 610689799533705108 306732526081 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1004544 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1004544 1024 610689799533705108 306732526081 611312198164220534 307358071783 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1005568 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1005568 1024 611312198164220534 307358071783 611934950034806401 307984610269 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1006592 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1006592 1024 611934950034806401 307984610269 612557164279309075 308611244971 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_999424 : DualFrontier209.checkFrom FactorFullCertificate209.phi 999424 8192 607577204088389718 303613753841 612557164279309075 308611244971 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 999424 607577204088389718 303613753841 608199691712900824 304236201889 7168 612557164279309075 308611244971 checked_small_999424 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1000448 608199691712900824 304236201889 608822148829445149 304859256785 6144 612557164279309075 308611244971 checked_small_1000448 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1001472 608822148829445149 304859256785 609444601171284110 305482944221 5120 612557164279309075 308611244971 checked_small_1001472 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1002496 609444601171284110 305482944221 610067253293894223 306107469463 4096 612557164279309075 308611244971 checked_small_1002496 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1003520 610067253293894223 306107469463 610689799533705108 306732526081 3072 612557164279309075 308611244971 checked_small_1003520 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1004544 610689799533705108 306732526081 611312198164220534 307358071783 2048 612557164279309075 308611244971 checked_small_1004544 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1005568 611312198164220534 307358071783 611934950034806401 307984610269 1024 612557164279309075 308611244971 checked_small_1005568 checked_small_1006592)))))))
#print axioms checked_part_999424
private theorem checked_small_1007616 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1007616 1024 612557164279309075 308611244971 613179717925837500 309238858845 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1008640 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1008640 1024 613179717925837500 309238858845 613802510469547576 309867351455 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1009664 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1009664 1024 613802510469547576 309867351455 614424785374082949 310495958915 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1010688 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1010688 1024 614424785374082949 310495958915 615047293724932602 311125439517 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1011712 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1011712 1024 615047293724932602 311125439517 615670034116831145 311755792551 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1012736 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1012736 1024 615670034116831145 311755792551 616292387752896658 312386391427 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1013760 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1013760 1024 616292387752896658 312386391427 616914892652720613 313017780925 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1014784 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1014784 1024 616914892652720613 313017780925 617537433467868508 313649844337 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1007616 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1007616 8192 612557164279309075 308611244971 617537433467868508 313649844337 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1007616 612557164279309075 308611244971 613179717925837500 309238858845 7168 617537433467868508 313649844337 checked_small_1007616 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1008640 613179717925837500 309238858845 613802510469547576 309867351455 6144 617537433467868508 313649844337 checked_small_1008640 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1009664 613802510469547576 309867351455 614424785374082949 310495958915 5120 617537433467868508 313649844337 checked_small_1009664 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1010688 614424785374082949 310495958915 615047293724932602 311125439517 4096 617537433467868508 313649844337 checked_small_1010688 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1011712 615047293724932602 311125439517 615670034116831145 311755792551 3072 617537433467868508 313649844337 checked_small_1011712 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1012736 615670034116831145 311755792551 616292387752896658 312386391427 2048 617537433467868508 313649844337 checked_small_1012736 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1013760 616292387752896658 312386391427 616914892652720613 313017780925 1024 617537433467868508 313649844337 checked_small_1013760 checked_small_1014784)))))))
#print axioms checked_part_1007616
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 983040 32768 597616831487308745 293740710159 617537433467868508 313649844337 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 983040 597616831487308745 293740710159 602597143753257378 298656957823 24576 617537433467868508 313649844337 checked_part_983040 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 991232 602597143753257378 298656957823 607577204088389718 303613753841 16384 617537433467868508 313649844337 checked_part_991232 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 999424 607577204088389718 303613753841 612557164279309075 308611244971 8192 617537433467868508 313649844337 checked_part_999424 checked_part_1007616)))
theorem block_sound :
    (617537433467868508 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1015808 ∧
     313649844337 = FrontierCheck209.triangle FactorFullCertificate209.phi 1015808) ∧
    ∀ t, 983040 < t → t ≤ 1015808 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 983040 597616831487308745 293740710159 617537433467868508 313649844337 FullPrefix209_029.endpoint.1 FullPrefix209_029.endpoint.2 checked
theorem endpoint :
    617537433467868508 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1015808 ∧
    313649844337 = FrontierCheck209.triangle FactorFullCertificate209.phi 1015808 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1015808) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 983040
  · exact FullPrefix209_029.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_030
