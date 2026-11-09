module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_037

@[expose] public section
namespace JSP233.FullPrefix209_038
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1245184 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1245184 1024 756981283659662639 471290605451 757603921466576667 472066223131 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1246208 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1246208 1024 757603921466576667 472066223131 758226342448047727 472842208079 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1247232 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1247232 1024 758226342448047727 472842208079 758848791691539697 473618865565 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1248256 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1248256 1024 758848791691539697 473618865565 759471494399796657 474396477015 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1249280 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1249280 1024 759471494399796657 474396477015 760093940248699020 475174405151 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1250304 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1250304 1024 760093940248699020 475174405151 760716291141767941 475952851775 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1251328 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1251328 1024 760716291141767941 475952851775 761339054367680615 476732451909 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1252352 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1252352 1024 761339054367680615 476732451909 761961248278745844 477511976439 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1245184 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1245184 8192 756981283659662639 471290605451 761961248278745844 477511976439 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1245184 756981283659662639 471290605451 757603921466576667 472066223131 7168 761961248278745844 477511976439 checked_small_1245184 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1246208 757603921466576667 472066223131 758226342448047727 472842208079 6144 761961248278745844 477511976439 checked_small_1246208 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1247232 758226342448047727 472842208079 758848791691539697 473618865565 5120 761961248278745844 477511976439 checked_small_1247232 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1248256 758848791691539697 473618865565 759471494399796657 474396477015 4096 761961248278745844 477511976439 checked_small_1248256 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1249280 759471494399796657 474396477015 760093940248699020 475174405151 3072 761961248278745844 477511976439 checked_small_1249280 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1250304 760093940248699020 475174405151 760716291141767941 475952851775 2048 761961248278745844 477511976439 checked_small_1250304 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1251328 760716291141767941 475952851775 761339054367680615 476732451909 1024 761961248278745844 477511976439 checked_small_1251328 checked_small_1252352)))))))
#print axioms checked_part_1245184
private theorem checked_small_1253376 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1253376 1024 761961248278745844 477511976439 762583806833311750 478292595177 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1254400 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1254400 1024 762583806833311750 478292595177 763206654225604788 479074214067 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1255424 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1255424 1024 763206654225604788 479074214067 763829007435636853 479855850171 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1256448 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1256448 1024 763829007435636853 479855850171 764451589796515780 480638411551 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1257472 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1257472 1024 764451589796515780 480638411551 765074045513334583 481421451141 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1258496 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1258496 1024 765074045513334583 481421451141 765696459243613820 482205075173 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1259520 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1259520 1024 765696459243613820 482205075173 766319129992167312 482989660439 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1260544 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1260544 1024 766319129992167312 482989660439 766941640744306721 483774681629 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1253376 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1253376 8192 761961248278745844 477511976439 766941640744306721 483774681629 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1253376 761961248278745844 477511976439 762583806833311750 478292595177 7168 766941640744306721 483774681629 checked_small_1253376 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1254400 762583806833311750 478292595177 763206654225604788 479074214067 6144 766941640744306721 483774681629 checked_small_1254400 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1255424 763206654225604788 479074214067 763829007435636853 479855850171 5120 766941640744306721 483774681629 checked_small_1255424 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1256448 763829007435636853 479855850171 764451589796515780 480638411551 4096 766941640744306721 483774681629 checked_small_1256448 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1257472 764451589796515780 480638411551 765074045513334583 481421451141 3072 766941640744306721 483774681629 checked_small_1257472 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1258496 765074045513334583 481421451141 765696459243613820 482205075173 2048 766941640744306721 483774681629 checked_small_1258496 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1259520 765696459243613820 482205075173 766319129992167312 482989660439 1024 766941640744306721 483774681629 checked_small_1259520 checked_small_1260544)))))))
#print axioms checked_part_1253376
private theorem checked_small_1261568 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1261568 1024 766941640744306721 483774681629 767564032605991946 484560190159 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1262592 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1262592 1024 767564032605991946 484560190159 768186542743420154 485346485341 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1263616 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1263616 1024 768186542743420154 485346485341 768809176477013691 486133574269 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1264640 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1264640 1024 768809176477013691 486133574269 769431671762353847 486921125669 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1265664 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1265664 1024 769431671762353847 486921125669 770054103308083625 487709233739 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1266688 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1266688 1024 770054103308083625 487709233739 770676867720894223 488498401069 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1267712 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1267712 1024 770676867720894223 488498401069 771299045079877962 489287461549 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1268736 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1268736 1024 771299045079877962 489287461549 771921672473852429 490077730225 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1261568 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1261568 8192 766941640744306721 483774681629 771921672473852429 490077730225 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1261568 766941640744306721 483774681629 767564032605991946 484560190159 7168 771921672473852429 490077730225 checked_small_1261568 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1262592 767564032605991946 484560190159 768186542743420154 485346485341 6144 771921672473852429 490077730225 checked_small_1262592 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1263616 768186542743420154 485346485341 768809176477013691 486133574269 5120 771921672473852429 490077730225 checked_small_1263616 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1264640 768809176477013691 486133574269 769431671762353847 486921125669 4096 771921672473852429 490077730225 checked_small_1264640 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1265664 769431671762353847 486921125669 770054103308083625 487709233739 3072 771921672473852429 490077730225 checked_small_1265664 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1266688 770054103308083625 487709233739 770676867720894223 488498401069 2048 771921672473852429 490077730225 checked_small_1266688 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1267712 770676867720894223 488498401069 771299045079877962 489287461549 1024 771921672473852429 490077730225 checked_small_1267712 checked_small_1268736)))))))
#print axioms checked_part_1261568
private theorem checked_small_1269760 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1269760 1024 771921672473852429 490077730225 772544440619528580 490868815449 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1270784 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1270784 1024 772544440619528580 490868815449 773166781117931312 491659994763 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1271808 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1271808 1024 773166781117931312 491659994763 773789137988393910 492451832005 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1272832 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1272832 1024 773789137988393910 492451832005 774411781587983279 493244671631 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1273856 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1273856 1024 774411781587983279 493244671631 775034237963812711 494037910283 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1274880 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1274880 1024 775034237963812711 494037910283 775656826024112129 494831954291 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1275904 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1275904 1024 775656826024112129 494831954291 776279434328287466 495626661747 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1276928 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1276928 1024 776279434328287466 495626661747 776901735500523078 496421614345 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1269760 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1269760 8192 771921672473852429 490077730225 776901735500523078 496421614345 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1269760 771921672473852429 490077730225 772544440619528580 490868815449 7168 776901735500523078 496421614345 checked_small_1269760 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1270784 772544440619528580 490868815449 773166781117931312 491659994763 6144 776901735500523078 496421614345 checked_small_1270784 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1271808 773166781117931312 491659994763 773789137988393910 492451832005 5120 776901735500523078 496421614345 checked_small_1271808 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1272832 773789137988393910 492451832005 774411781587983279 493244671631 4096 776901735500523078 496421614345 checked_small_1272832 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1273856 774411781587983279 493244671631 775034237963812711 494037910283 3072 776901735500523078 496421614345 checked_small_1273856 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1274880 775034237963812711 494037910283 775656826024112129 494831954291 2048 776901735500523078 496421614345 checked_small_1274880 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1275904 775656826024112129 494831954291 776279434328287466 495626661747 1024 776901735500523078 496421614345 checked_small_1275904 checked_small_1276928)))))))
#print axioms checked_part_1269760
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1245184 32768 756981283659662639 471290605451 776901735500523078 496421614345 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1245184 756981283659662639 471290605451 761961248278745844 477511976439 24576 776901735500523078 496421614345 checked_part_1245184 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1253376 761961248278745844 477511976439 766941640744306721 483774681629 16384 776901735500523078 496421614345 checked_part_1253376 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1261568 766941640744306721 483774681629 771921672473852429 490077730225 8192 776901735500523078 496421614345 checked_part_1261568 checked_part_1269760)))
theorem block_sound :
    (776901735500523078 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1277952 ∧
     496421614345 = FrontierCheck209.triangle FactorFullCertificate209.phi 1277952) ∧
    ∀ t, 1245184 < t → t ≤ 1277952 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1245184 756981283659662639 471290605451 776901735500523078 496421614345 FullPrefix209_037.endpoint.1 FullPrefix209_037.endpoint.2 checked
theorem endpoint :
    776901735500523078 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1277952 ∧
    496421614345 = FrontierCheck209.triangle FactorFullCertificate209.phi 1277952 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1277952) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1245184
  · exact FullPrefix209_037.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_038
