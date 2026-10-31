import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_040
namespace JSP233.FullPrefix209_041
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1343488 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1343488 1024 816742972594356337 548642329997 817365587875152992 549479125193 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1344512 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1344512 1024 817365587875152992 549479125193 817987859976898578 550316096289 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1345536 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1345536 1024 817987859976898578 550316096289 818610387217210480 551154047901 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1346560 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1346560 1024 818610387217210480 551154047901 819233151321028711 551992956189 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1347584 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1347584 1024 819233151321028711 551992956189 819855553299096494 552832014069 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1348608 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1348608 1024 819855553299096494 552832014069 820478039069779755 553671822263 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1349632 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1349632 1024 820478039069779755 553671822263 821100710218413873 554512518237 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1350656 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1350656 1024 821100710218413873 554512518237 821722966132621159 555353290713 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1343488 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1343488 8192 816742972594356337 548642329997 821722966132621159 555353290713 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1343488 816742972594356337 548642329997 817365587875152992 549479125193 7168 821722966132621159 555353290713 checked_small_1343488 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1344512 817365587875152992 549479125193 817987859976898578 550316096289 6144 821722966132621159 555353290713 checked_small_1344512 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1345536 817987859976898578 550316096289 818610387217210480 551154047901 5120 821722966132621159 555353290713 checked_small_1345536 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1346560 818610387217210480 551154047901 819233151321028711 551992956189 4096 821722966132621159 555353290713 checked_small_1346560 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1347584 819233151321028711 551992956189 819855553299096494 552832014069 3072 821722966132621159 555353290713 checked_small_1347584 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1348608 819855553299096494 552832014069 820478039069779755 553671822263 2048 821722966132621159 555353290713 checked_small_1348608 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1349632 820478039069779755 553671822263 821100710218413873 554512518237 1024 821722966132621159 555353290713 checked_small_1349632 checked_small_1350656)))))))
#print axioms checked_part_1343488
private theorem checked_small_1351680 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1351680 1024 821722966132621159 555353290713 822345612131046750 556195227777 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1352704 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1352704 1024 822345612131046750 556195227777 822968272789754044 557037822415 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1353728 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1353728 1024 822968272789754044 557037822415 823590619484148568 557880629455 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1354752 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1354752 1024 823590619484148568 557880629455 824213126127415444 558724290461 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1355776 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1355776 1024 824213126127415444 558724290461 824835808899228670 559568827871 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1356800 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1356800 1024 824835808899228670 559568827871 825458307461646325 560413752955 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1357824 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1357824 1024 825458307461646325 560413752955 826080704008414543 561259176835 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1358848 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1358848 1024 826080704008414543 561259176835 826703398473734369 562105643055 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1351680 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1351680 8192 821722966132621159 555353290713 826703398473734369 562105643055 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1351680 821722966132621159 555353290713 822345612131046750 556195227777 7168 826703398473734369 562105643055 checked_small_1351680 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1352704 822345612131046750 556195227777 822968272789754044 557037822415 6144 826703398473734369 562105643055 checked_small_1352704 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1353728 822968272789754044 557037822415 823590619484148568 557880629455 5120 826703398473734369 562105643055 checked_small_1353728 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1354752 823590619484148568 557880629455 824213126127415444 558724290461 4096 826703398473734369 562105643055 checked_small_1354752 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1355776 824213126127415444 558724290461 824835808899228670 559568827871 3072 826703398473734369 562105643055 checked_small_1355776 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1356800 824835808899228670 559568827871 825458307461646325 560413752955 2048 826703398473734369 562105643055 checked_small_1356800 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1357824 825458307461646325 560413752955 826080704008414543 561259176835 1024 826703398473734369 562105643055 checked_small_1357824 checked_small_1358848)))))))
#print axioms checked_part_1351680
private theorem checked_small_1359872 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1359872 1024 826703398473734369 562105643055 827325690661502091 562952199641 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1360896 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1360896 1024 827325690661502091 562952199641 827948231372228404 563799731687 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1361920 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1361920 1024 827948231372228404 563799731687 828570968569401671 564648169047 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1362944 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1362944 1024 828570968569401671 564648169047 829193304392711955 565496696849 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1363968 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1363968 1024 829193304392711955 565496696849 829815855367340998 566346155413 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1364992 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1364992 1024 829815855367340998 566346155413 830438315723700374 567196127721 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1366016 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1366016 1024 830438315723700374 567196127721 831060803194556198 568046774439 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1367040 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1367040 1024 831060803194556198 568046774439 831683355490887838 568898147235 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1359872 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1359872 8192 826703398473734369 562105643055 831683355490887838 568898147235 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1359872 826703398473734369 562105643055 827325690661502091 562952199641 7168 831683355490887838 568898147235 checked_small_1359872 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1360896 827325690661502091 562952199641 827948231372228404 563799731687 6144 831683355490887838 568898147235 checked_small_1360896 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1361920 827948231372228404 563799731687 828570968569401671 564648169047 5120 831683355490887838 568898147235 checked_small_1361920 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1362944 828570968569401671 564648169047 829193304392711955 565496696849 4096 831683355490887838 568898147235 checked_small_1362944 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1363968 829193304392711955 565496696849 829815855367340998 566346155413 3072 831683355490887838 568898147235 checked_small_1363968 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1364992 829815855367340998 566346155413 830438315723700374 567196127721 2048 831683355490887838 568898147235 checked_small_1364992 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1366016 830438315723700374 567196127721 831060803194556198 568046774439 1024 831683355490887838 568898147235 checked_small_1366016 checked_small_1367040)))))))
#print axioms checked_part_1359872
private theorem checked_small_1368064 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1368064 1024 831683355490887838 568898147235 832305929045270187 569750186663 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1369088 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1369088 1024 832305929045270187 569750186663 832928330934921006 570602628467 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1370112 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1370112 1024 832928330934921006 570602628467 833550903898675473 571455942059 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1371136 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1371136 1024 833550903898675473 571455942059 834173590595515154 572310049281 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1372160 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1372160 1024 834173590595515154 572310049281 834795955743592881 573164352763 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1373184 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1373184 1024 834795955743592881 573164352763 835418400403587636 574019402659 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1374208 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1374208 1024 835418400403587636 574019402659 836041105006838213 574875447347 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1375232 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1375232 1024 836041105006838213 574875447347 836663332666487581 575731473479 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1368064 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1368064 8192 831683355490887838 568898147235 836663332666487581 575731473479 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1368064 831683355490887838 568898147235 832305929045270187 569750186663 7168 836663332666487581 575731473479 checked_small_1368064 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1369088 832305929045270187 569750186663 832928330934921006 570602628467 6144 836663332666487581 575731473479 checked_small_1369088 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1370112 832928330934921006 570602628467 833550903898675473 571455942059 5120 836663332666487581 575731473479 checked_small_1370112 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1371136 833550903898675473 571455942059 834173590595515154 572310049281 4096 836663332666487581 575731473479 checked_small_1371136 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1372160 834173590595515154 572310049281 834795955743592881 573164352763 3072 836663332666487581 575731473479 checked_small_1372160 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1373184 834795955743592881 573164352763 835418400403587636 574019402659 2048 836663332666487581 575731473479 checked_small_1373184 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1374208 835418400403587636 574019402659 836041105006838213 574875447347 1024 836663332666487581 575731473479 checked_small_1374208 checked_small_1375232)))))))
#print axioms checked_part_1368064
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1343488 32768 816742972594356337 548642329997 836663332666487581 575731473479 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1343488 816742972594356337 548642329997 821722966132621159 555353290713 24576 836663332666487581 575731473479 checked_part_1343488 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1351680 821722966132621159 555353290713 826703398473734369 562105643055 16384 836663332666487581 575731473479 checked_part_1351680 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1359872 826703398473734369 562105643055 831683355490887838 568898147235 8192 836663332666487581 575731473479 checked_part_1359872 checked_part_1368064)))
theorem block_sound :
    (836663332666487581 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1376256 ∧
     575731473479 = FrontierCheck209.triangle FactorFullCertificate209.phi 1376256) ∧
    ∀ t, 1343488 < t → t ≤ 1376256 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1343488 816742972594356337 548642329997 836663332666487581 575731473479 FullPrefix209_040.endpoint.1 FullPrefix209_040.endpoint.2 checked
theorem endpoint :
    836663332666487581 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1376256 ∧
    575731473479 = FrontierCheck209.triangle FactorFullCertificate209.phi 1376256 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1376256) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1343488
  · exact FullPrefix209_040.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_041
