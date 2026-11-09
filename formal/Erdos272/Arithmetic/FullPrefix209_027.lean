module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_026

@[expose] public section
namespace JSP233.FullPrefix209_027
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_884736 : DualFrontier209.checkFrom FactorFullCertificate209.phi 884736 1024 537855150376802392 237929977045 538477583781808708 238480985093 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_885760 : DualFrontier209.checkFrom FactorFullCertificate209.phi 885760 1024 538477583781808708 238480985093 539100429008698216 239032995621 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_886784 : DualFrontier209.checkFrom FactorFullCertificate209.phi 886784 1024 539100429008698216 239032995621 539722773562927705 239585199777 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_887808 : DualFrontier209.checkFrom FactorFullCertificate209.phi 887808 1024 539722773562927705 239585199777 540345313302184453 240138214523 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_888832 : DualFrontier209.checkFrom FactorFullCertificate209.phi 888832 1024 540345313302184453 240138214523 540967776175219405 240691798369 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_889856 : DualFrontier209.checkFrom FactorFullCertificate209.phi 889856 1024 540967776175219405 240691798369 541590214381653746 241245997597 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_890880 : DualFrontier209.checkFrom FactorFullCertificate209.phi 890880 1024 541590214381653746 241245997597 542212913817418996 241801067105 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_891904 : DualFrontier209.checkFrom FactorFullCertificate209.phi 891904 1024 542212913817418996 241801067105 542835384842087337 242356570487 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_884736 : DualFrontier209.checkFrom FactorFullCertificate209.phi 884736 8192 537855150376802392 237929977045 542835384842087337 242356570487 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 884736 537855150376802392 237929977045 538477583781808708 238480985093 7168 542835384842087337 242356570487 checked_small_884736 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 885760 538477583781808708 238480985093 539100429008698216 239032995621 6144 542835384842087337 242356570487 checked_small_885760 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 886784 539100429008698216 239032995621 539722773562927705 239585199777 5120 542835384842087337 242356570487 checked_small_886784 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 887808 539722773562927705 239585199777 540345313302184453 240138214523 4096 542835384842087337 242356570487 checked_small_887808 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 888832 540345313302184453 240138214523 540967776175219405 240691798369 3072 542835384842087337 242356570487 checked_small_888832 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 889856 540967776175219405 240691798369 541590214381653746 241245997597 2048 542835384842087337 242356570487 checked_small_889856 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 890880 541590214381653746 241245997597 542212913817418996 241801067105 1024 542835384842087337 242356570487 checked_small_890880 checked_small_891904)))))))
#print axioms checked_part_884736
private theorem checked_small_892928 : DualFrontier209.checkFrom FactorFullCertificate209.phi 892928 1024 542835384842087337 242356570487 543457796847359204 242912658475 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_893952 : DualFrontier209.checkFrom FactorFullCertificate209.phi 893952 1024 543457796847359204 242912658475 544080226467713110 243469399469 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_894976 : DualFrontier209.checkFrom FactorFullCertificate209.phi 894976 1024 544080226467713110 243469399469 544702922572914661 244027016509 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_896000 : DualFrontier209.checkFrom FactorFullCertificate209.phi 896000 1024 544702922572914661 244027016509 545325410135366653 244585084307 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_897024 : DualFrontier209.checkFrom FactorFullCertificate209.phi 897024 1024 545325410135366653 244585084307 545947886384074919 245143779345 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_898048 : DualFrontier209.checkFrom FactorFullCertificate209.phi 898048 1024 545947886384074919 245143779345 546570635139496346 245703356755 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_899072 : DualFrontier209.checkFrom FactorFullCertificate209.phi 899072 1024 546570635139496346 245703356755 547192865137476338 246263105169 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_900096 : DualFrontier209.checkFrom FactorFullCertificate209.phi 900096 1024 547192865137476338 246263105169 547815313732558585 246823687437 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_892928 : DualFrontier209.checkFrom FactorFullCertificate209.phi 892928 8192 542835384842087337 242356570487 547815313732558585 246823687437 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 892928 542835384842087337 242356570487 543457796847359204 242912658475 7168 547815313732558585 246823687437 checked_small_892928 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 893952 543457796847359204 242912658475 544080226467713110 243469399469 6144 547815313732558585 246823687437 checked_small_893952 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 894976 544080226467713110 243469399469 544702922572914661 244027016509 5120 547815313732558585 246823687437 checked_small_894976 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 896000 544702922572914661 244027016509 545325410135366653 244585084307 4096 547815313732558585 246823687437 checked_small_896000 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 897024 545325410135366653 244585084307 545947886384074919 245143779345 3072 547815313732558585 246823687437 checked_small_897024 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 898048 545947886384074919 245143779345 546570635139496346 245703356755 2048 547815313732558585 246823687437 checked_small_898048 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 899072 546570635139496346 245703356755 547192865137476338 246263105169 1024 547815313732558585 246823687437 checked_small_899072 checked_small_900096)))))))
#print axioms checked_part_892928
private theorem checked_small_901120 : DualFrontier209.checkFrom FactorFullCertificate209.phi 901120 1024 547815313732558585 246823687437 548438139620779199 247385247389 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_902144 : DualFrontier209.checkFrom FactorFullCertificate209.phi 902144 1024 548438139620779199 247385247389 549060459239402422 247946988187 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_903168 : DualFrontier209.checkFrom FactorFullCertificate209.phi 903168 1024 549060459239402422 247946988187 549682918097333929 248509491939 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_904192 : DualFrontier209.checkFrom FactorFullCertificate209.phi 904192 1024 549682918097333929 248509491939 550305617745169951 249072850997 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_905216 : DualFrontier209.checkFrom FactorFullCertificate209.phi 905216 1024 550305617745169951 249072850997 550928075298448540 249636628487 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_906240 : DualFrontier209.checkFrom FactorFullCertificate209.phi 906240 1024 550928075298448540 249636628487 551550600243114459 250201104457 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_907264 : DualFrontier209.checkFrom FactorFullCertificate209.phi 907264 1024 551550600243114459 250201104457 552173217110078156 250766301391 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_908288 : DualFrontier209.checkFrom FactorFullCertificate209.phi 908288 1024 552173217110078156 250766301391 552795560239708427 251331887067 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_901120 : DualFrontier209.checkFrom FactorFullCertificate209.phi 901120 8192 547815313732558585 246823687437 552795560239708427 251331887067 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 901120 547815313732558585 246823687437 548438139620779199 247385247389 7168 552795560239708427 251331887067 checked_small_901120 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 902144 548438139620779199 247385247389 549060459239402422 247946988187 6144 552795560239708427 251331887067 checked_small_902144 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 903168 549060459239402422 247946988187 549682918097333929 248509491939 5120 552795560239708427 251331887067 checked_small_903168 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 904192 549682918097333929 248509491939 550305617745169951 249072850997 4096 552795560239708427 251331887067 checked_small_904192 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 905216 550305617745169951 249072850997 550928075298448540 249636628487 3072 552795560239708427 251331887067 checked_small_905216 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 906240 550928075298448540 249636628487 551550600243114459 250201104457 2048 552795560239708427 251331887067 checked_small_906240 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 907264 551550600243114459 250201104457 552173217110078156 250766301391 1024 552795560239708427 251331887067 checked_small_907264 checked_small_908288)))))))
#print axioms checked_part_901120
private theorem checked_small_909312 : DualFrontier209.checkFrom FactorFullCertificate209.phi 909312 1024 552795560239708427 251331887067 553418043508596339 251898237417 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_910336 : DualFrontier209.checkFrom FactorFullCertificate209.phi 910336 1024 553418043508596339 251898237417 554040750943667130 252465429457 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_911360 : DualFrontier209.checkFrom FactorFullCertificate209.phi 911360 1024 554040750943667130 252465429457 554663151146750226 253032979023 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_912384 : DualFrontier209.checkFrom FactorFullCertificate209.phi 912384 1024 554663151146750226 253032979023 555285643690617792 253601250153 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_913408 : DualFrontier209.checkFrom FactorFullCertificate209.phi 913408 1024 555285643690617792 253601250153 555908256145349322 254170268347 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_914432 : DualFrontier209.checkFrom FactorFullCertificate209.phi 914432 1024 555908256145349322 254170268347 556530601807902920 254739679957 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_915456 : DualFrontier209.checkFrom FactorFullCertificate209.phi 915456 1024 556530601807902920 254739679957 557153183613558964 255309945099 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_916480 : DualFrontier209.checkFrom FactorFullCertificate209.phi 916480 1024 557153183613558964 255309945099 557775833787990876 255880910551 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_909312 : DualFrontier209.checkFrom FactorFullCertificate209.phi 909312 8192 552795560239708427 251331887067 557775833787990876 255880910551 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 909312 552795560239708427 251331887067 553418043508596339 251898237417 7168 557775833787990876 255880910551 checked_small_909312 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 910336 553418043508596339 251898237417 554040750943667130 252465429457 6144 557775833787990876 255880910551 checked_small_910336 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 911360 554040750943667130 252465429457 554663151146750226 253032979023 5120 557775833787990876 255880910551 checked_small_911360 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 912384 554663151146750226 253032979023 555285643690617792 253601250153 4096 557775833787990876 255880910551 checked_small_912384 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 913408 555285643690617792 253601250153 555908256145349322 254170268347 3072 557775833787990876 255880910551 checked_small_913408 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 914432 555908256145349322 254170268347 556530601807902920 254739679957 2048 557775833787990876 255880910551 checked_small_914432 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 915456 556530601807902920 254739679957 557153183613558964 255309945099 1024 557775833787990876 255880910551 checked_small_915456 checked_small_916480)))))))
#print axioms checked_part_909312
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 884736 32768 537855150376802392 237929977045 557775833787990876 255880910551 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 884736 537855150376802392 237929977045 542835384842087337 242356570487 24576 557775833787990876 255880910551 checked_part_884736 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 892928 542835384842087337 242356570487 547815313732558585 246823687437 16384 557775833787990876 255880910551 checked_part_892928 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 901120 547815313732558585 246823687437 552795560239708427 251331887067 8192 557775833787990876 255880910551 checked_part_901120 checked_part_909312)))
theorem block_sound :
    (557775833787990876 = FrontierCheck209.massFloor FactorFullCertificate209.phi 917504 ∧
     255880910551 = FrontierCheck209.triangle FactorFullCertificate209.phi 917504) ∧
    ∀ t, 884736 < t → t ≤ 917504 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 884736 537855150376802392 237929977045 557775833787990876 255880910551 FullPrefix209_026.endpoint.1 FullPrefix209_026.endpoint.2 checked
theorem endpoint :
    557775833787990876 = FrontierCheck209.massFloor FactorFullCertificate209.phi 917504 ∧
    255880910551 = FrontierCheck209.triangle FactorFullCertificate209.phi 917504 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 917504) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 884736
  · exact FullPrefix209_026.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_027
