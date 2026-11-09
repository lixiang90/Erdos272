module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_041

@[expose] public section
namespace JSP233.FullPrefix209_042
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1376256 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1376256 1024 836663332666487581 575731473479 837285878876001202 576588575209 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1377280 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1377280 1024 837285878876001202 576588575209 837908769801958700 577446789575 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1378304 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1378304 1024 837908769801958700 577446789575 838531088953435002 578304853497 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1379328 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1379328 1024 838531088953435002 578304853497 839153544542580503 579163742805 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1380352 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1380352 1024 839153544542580503 579163742805 839776059538124401 580023351507 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1381376 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1381376 1024 839776059538124401 580023351507 840398625117547909 580883667585 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1382400 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1382400 1024 840398625117547909 580883667585 841021161953145915 581744581457 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1383424 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1383424 1024 841021161953145915 581744581457 841643735908314619 582606184221 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1376256 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1376256 8192 836663332666487581 575731473479 841643735908314619 582606184221 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1376256 836663332666487581 575731473479 837285878876001202 576588575209 7168 841643735908314619 582606184221 checked_small_1376256 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1377280 837285878876001202 576588575209 837908769801958700 577446789575 6144 841643735908314619 582606184221 checked_small_1377280 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1378304 837908769801958700 577446789575 838531088953435002 578304853497 5120 841643735908314619 582606184221 checked_small_1378304 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1379328 838531088953435002 578304853497 839153544542580503 579163742805 4096 841643735908314619 582606184221 checked_small_1379328 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1380352 839153544542580503 579163742805 839776059538124401 580023351507 3072 841643735908314619 582606184221 checked_small_1380352 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1381376 839776059538124401 580023351507 840398625117547909 580883667585 2048 841643735908314619 582606184221 checked_small_1381376 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1382400 840398625117547909 580883667585 841021161953145915 581744581457 1024 841643735908314619 582606184221 checked_small_1382400 checked_small_1383424)))))))
#print axioms checked_part_1376256
private theorem checked_small_1384448 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1384448 1024 841643735908314619 582606184221 842266156814812898 583468212519 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1385472 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1385472 1024 842266156814812898 583468212519 842888694226710319 584331039601 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1386496 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1386496 1024 842888694226710319 584331039601 843511282536098989 585194574803 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1387520 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1387520 1024 843511282536098989 585194574803 844133678938943022 586058481143 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1388544 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1388544 1024 844133678938943022 586058481143 844756157423909220 586923138755 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1389568 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1389568 1024 844756157423909220 586923138755 845378841590932055 587788719759 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1390592 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1390592 1024 845378841590932055 587788719759 846001208632615951 588654497247 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1391616 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1391616 1024 846001208632615951 588654497247 846623738968417464 589521139293 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1384448 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1384448 8192 841643735908314619 582606184221 846623738968417464 589521139293 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1384448 841643735908314619 582606184221 842266156814812898 583468212519 7168 846623738968417464 589521139293 checked_small_1384448 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1385472 842266156814812898 583468212519 842888694226710319 584331039601 6144 846623738968417464 589521139293 checked_small_1385472 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1386496 842888694226710319 584331039601 843511282536098989 585194574803 5120 846623738968417464 589521139293 checked_small_1386496 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1387520 843511282536098989 585194574803 844133678938943022 586058481143 4096 846623738968417464 589521139293 checked_small_1387520 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1388544 844133678938943022 586058481143 844756157423909220 586923138755 3072 846623738968417464 589521139293 checked_small_1388544 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1389568 844756157423909220 586923138755 845378841590932055 587788719759 2048 846623738968417464 589521139293 checked_small_1389568 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1390592 845378841590932055 587788719759 846001208632615951 588654497247 1024 846623738968417464 589521139293 checked_small_1390592 checked_small_1391616)))))))
#print axioms checked_part_1384448
private theorem checked_small_1392640 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1392640 1024 846623738968417464 589521139293 847246587623797730 590388862461 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1393664 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1393664 1024 847246587623797730 590388862461 847868807888146806 591256347355 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1394688 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1394688 1024 847868807888146806 591256347355 848491378378851145 592124957907 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1395712 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1395712 1024 848491378378851145 592124957907 849113909977068302 592994151709 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1396736 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1396736 1024 849113909977068302 592994151709 849736221814546428 593863675817 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1397760 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1397760 1024 849736221814546428 593863675817 850358988406650915 594734473069 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1398784 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1398784 1024 850358988406650915 594734473069 850981484674145966 595605529885 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1399808 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1399808 1024 850981484674145966 595605529885 851603939950952617 596477166691 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1392640 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1392640 8192 846623738968417464 589521139293 851603939950952617 596477166691 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1392640 846623738968417464 589521139293 847246587623797730 590388862461 7168 851603939950952617 596477166691 checked_small_1392640 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1393664 847246587623797730 590388862461 847868807888146806 591256347355 6144 851603939950952617 596477166691 checked_small_1393664 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1394688 847868807888146806 591256347355 848491378378851145 592124957907 5120 851603939950952617 596477166691 checked_small_1394688 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1395712 848491378378851145 592124957907 849113909977068302 592994151709 4096 851603939950952617 596477166691 checked_small_1395712 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1396736 849113909977068302 592994151709 849736221814546428 593863675817 3072 851603939950952617 596477166691 checked_small_1396736 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1397760 849736221814546428 593863675817 850358988406650915 594734473069 2048 851603939950952617 596477166691 checked_small_1397760 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1398784 850358988406650915 594734473069 850981484674145966 595605529885 1024 851603939950952617 596477166691 checked_small_1398784 checked_small_1399808)))))))
#print axioms checked_part_1392640
private theorem checked_small_1400832 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1400832 1024 851603939950952617 596477166691 852226300334256138 597349307803 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1401856 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1401856 1024 852226300334256138 597349307803 852849089798403872 598222688005 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1402880 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1402880 1024 852849089798403872 598222688005 853471540785050213 599096231029 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1403904 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1403904 1024 853471540785050213 599096231029 854093946880052480 599970348305 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1404928 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1404928 1024 854093946880052480 599970348305 854716625346815828 600845485755 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1405952 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1405952 1024 854716625346815828 600845485755 855338996495554253 601720828607 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1406976 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1406976 1024 855338996495554253 601720828607 855961423121867120 602596886727 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1408000 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1408000 1024 855961423121867120 602596886727 856584120161432895 603473963141 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1400832 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1400832 8192 851603939950952617 596477166691 856584120161432895 603473963141 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1400832 851603939950952617 596477166691 852226300334256138 597349307803 7168 856584120161432895 603473963141 checked_small_1400832 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1401856 852226300334256138 597349307803 852849089798403872 598222688005 6144 856584120161432895 603473963141 checked_small_1401856 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1402880 852849089798403872 598222688005 853471540785050213 599096231029 5120 856584120161432895 603473963141 checked_small_1402880 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1403904 853471540785050213 599096231029 854093946880052480 599970348305 4096 856584120161432895 603473963141 checked_small_1403904 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1404928 854093946880052480 599970348305 854716625346815828 600845485755 3072 856584120161432895 603473963141 checked_small_1404928 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1405952 854716625346815828 600845485755 855338996495554253 601720828607 2048 856584120161432895 603473963141 checked_small_1405952 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1406976 855338996495554253 601720828607 855961423121867120 602596886727 1024 856584120161432895 603473963141 checked_small_1406976 checked_small_1408000)))))))
#print axioms checked_part_1400832
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1376256 32768 836663332666487581 575731473479 856584120161432895 603473963141 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1376256 836663332666487581 575731473479 841643735908314619 582606184221 24576 856584120161432895 603473963141 checked_part_1376256 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1384448 841643735908314619 582606184221 846623738968417464 589521139293 16384 856584120161432895 603473963141 checked_part_1384448 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1392640 846623738968417464 589521139293 851603939950952617 596477166691 8192 856584120161432895 603473963141 checked_part_1392640 checked_part_1400832)))
theorem block_sound :
    (856584120161432895 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1409024 ∧
     603473963141 = FrontierCheck209.triangle FactorFullCertificate209.phi 1409024) ∧
    ∀ t, 1376256 < t → t ≤ 1409024 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1376256 836663332666487581 575731473479 856584120161432895 603473963141 FullPrefix209_041.endpoint.1 FullPrefix209_041.endpoint.2 checked
theorem endpoint :
    856584120161432895 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1409024 ∧
    603473963141 = FrontierCheck209.triangle FactorFullCertificate209.phi 1409024 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1409024) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1376256
  · exact FullPrefix209_041.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_042
