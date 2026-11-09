module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_007

@[expose] public section
namespace JSP233.FullPrefix209_008
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_262144 : DualFrontier209.checkFrom FactorFullCertificate209.phi 262144 1024 159364627132252140 20888264643 159987236632844513 21051797001 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_263168 : DualFrontier209.checkFrom FactorFullCertificate209.phi 263168 1024 159987236632844513 21051797001 160609623844218061 21215908279 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_264192 : DualFrontier209.checkFrom FactorFullCertificate209.phi 264192 1024 160609623844218061 21215908279 161232089442437066 21380677539 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_265216 : DualFrontier209.checkFrom FactorFullCertificate209.phi 265216 1024 161232089442437066 21380677539 161854756855703893 21546137883 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_266240 : DualFrontier209.checkFrom FactorFullCertificate209.phi 266240 1024 161854756855703893 21546137883 162477249797057084 21712189365 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_267264 : DualFrontier209.checkFrom FactorFullCertificate209.phi 267264 1024 162477249797057084 21712189365 163099739060568350 21878877255 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_268288 : DualFrontier209.checkFrom FactorFullCertificate209.phi 268288 1024 163099739060568350 21878877255 163722374696953293 22046241975 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_269312 : DualFrontier209.checkFrom FactorFullCertificate209.phi 269312 1024 163722374696953293 22046241975 164344631172231104 22214141889 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_262144 : DualFrontier209.checkFrom FactorFullCertificate209.phi 262144 8192 159364627132252140 20888264643 164344631172231104 22214141889 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 262144 159364627132252140 20888264643 159987236632844513 21051797001 7168 164344631172231104 22214141889 checked_small_262144 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 263168 159987236632844513 21051797001 160609623844218061 21215908279 6144 164344631172231104 22214141889 checked_small_263168 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 264192 160609623844218061 21215908279 161232089442437066 21380677539 5120 164344631172231104 22214141889 checked_small_264192 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 265216 161232089442437066 21380677539 161854756855703893 21546137883 4096 164344631172231104 22214141889 checked_small_265216 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 266240 161854756855703893 21546137883 162477249797057084 21712189365 3072 164344631172231104 22214141889 checked_small_266240 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 267264 162477249797057084 21712189365 163099739060568350 21878877255 2048 164344631172231104 22214141889 checked_small_267264 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 268288 163099739060568350 21878877255 163722374696953293 22046241975 1024 164344631172231104 22214141889 checked_small_268288 checked_small_269312)))))))
#print axioms checked_part_262144
private theorem checked_small_270336 : DualFrontier209.checkFrom FactorFullCertificate209.phi 270336 1024 164344631172231104 22214141889 164967142372918901 22382747849 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_271360 : DualFrontier209.checkFrom FactorFullCertificate209.phi 271360 1024 164967142372918901 22382747849 165589963902078579 22552075785 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_272384 : DualFrontier209.checkFrom FactorFullCertificate209.phi 272384 1024 165589963902078579 22552075785 166212292689057102 22721907073 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_273408 : DualFrontier209.checkFrom FactorFullCertificate209.phi 273408 1024 166212292689057102 22721907073 166834826170842867 22892431617 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_274432 : DualFrontier209.checkFrom FactorFullCertificate209.phi 274432 1024 166834826170842867 22892431617 167457493408041681 23063630497 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_275456 : DualFrontier209.checkFrom FactorFullCertificate209.phi 275456 1024 167457493408041681 23063630497 168079777754300857 23235361277 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_276480 : DualFrontier209.checkFrom FactorFullCertificate209.phi 276480 1024 168079777754300857 23235361277 168702389604271210 23407819919 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_277504 : DualFrontier209.checkFrom FactorFullCertificate209.phi 277504 1024 168702389604271210 23407819919 169325016375020190 23580920375 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_270336 : DualFrontier209.checkFrom FactorFullCertificate209.phi 270336 8192 164344631172231104 22214141889 169325016375020190 23580920375 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 270336 164344631172231104 22214141889 164967142372918901 22382747849 7168 169325016375020190 23580920375 checked_small_270336 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 271360 164967142372918901 22382747849 165589963902078579 22552075785 6144 169325016375020190 23580920375 checked_small_271360 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 272384 165589963902078579 22552075785 166212292689057102 22721907073 5120 169325016375020190 23580920375 checked_small_272384 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 273408 166212292689057102 22721907073 166834826170842867 22892431617 4096 169325016375020190 23580920375 checked_small_273408 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 274432 166834826170842867 22892431617 167457493408041681 23063630497 3072 169325016375020190 23580920375 checked_small_274432 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 275456 167457493408041681 23063630497 168079777754300857 23235361277 2048 169325016375020190 23580920375 checked_small_275456 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 276480 168079777754300857 23235361277 168702389604271210 23407819919 1024 169325016375020190 23580920375 checked_small_276480 checked_small_277504)))))))
#print axioms checked_part_270336
private theorem checked_small_278528 : DualFrontier209.checkFrom FactorFullCertificate209.phi 278528 1024 169325016375020190 23580920375 169947333766760511 23754572021 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_279552 : DualFrontier209.checkFrom FactorFullCertificate209.phi 279552 1024 169947333766760511 23754572021 170569902109043512 23928931129 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_280576 : DualFrontier209.checkFrom FactorFullCertificate209.phi 280576 1024 170569902109043512 23928931129 171192575379552852 24103957345 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_281600 : DualFrontier209.checkFrom FactorFullCertificate209.phi 281600 1024 171192575379552852 24103957345 171815049592298051 24279565071 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_282624 : DualFrontier209.checkFrom FactorFullCertificate209.phi 282624 1024 171815049592298051 24279565071 172437413350172168 24455778845 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_283648 : DualFrontier209.checkFrom FactorFullCertificate209.phi 283648 1024 172437413350172168 24455778845 173060136197631312 24632731981 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_284672 : DualFrontier209.checkFrom FactorFullCertificate209.phi 284672 1024 173060136197631312 24632731981 173682442576412943 24810204011 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_285696 : DualFrontier209.checkFrom FactorFullCertificate209.phi 285696 1024 173682442576412943 24810204011 174304939135905264 24988367595 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_278528 : DualFrontier209.checkFrom FactorFullCertificate209.phi 278528 8192 169325016375020190 23580920375 174304939135905264 24988367595 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 278528 169325016375020190 23580920375 169947333766760511 23754572021 7168 174304939135905264 24988367595 checked_small_278528 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 279552 169947333766760511 23754572021 170569902109043512 23928931129 6144 174304939135905264 24988367595 checked_small_279552 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 280576 170569902109043512 23928931129 171192575379552852 24103957345 5120 174304939135905264 24988367595 checked_small_280576 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 281600 171192575379552852 24103957345 171815049592298051 24279565071 4096 174304939135905264 24988367595 checked_small_281600 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 282624 171815049592298051 24279565071 172437413350172168 24455778845 3072 174304939135905264 24988367595 checked_small_282624 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 283648 172437413350172168 24455778845 173060136197631312 24632731981 2048 174304939135905264 24988367595 checked_small_283648 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 284672 173060136197631312 24632731981 173682442576412943 24810204011 1024 174304939135905264 24988367595 checked_small_284672 checked_small_285696)))))))
#print axioms checked_part_278528
private theorem checked_small_286720 : DualFrontier209.checkFrom FactorFullCertificate209.phi 286720 1024 174304939135905264 24988367595 174927752071877803 25167259633 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_287744 : DualFrontier209.checkFrom FactorFullCertificate209.phi 287744 1024 174927752071877803 25167259633 175550075230590289 25346648309 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_288768 : DualFrontier209.checkFrom FactorFullCertificate209.phi 288768 1024 175550075230590289 25346648309 176172661028503467 25526750149 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_289792 : DualFrontier209.checkFrom FactorFullCertificate209.phi 289792 1024 176172661028503467 25526750149 176795103724580749 25707447973 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_290816 : DualFrontier209.checkFrom FactorFullCertificate209.phi 290816 1024 176795103724580749 25707447973 177417568886026089 25888789655 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_291840 : DualFrontier209.checkFrom FactorFullCertificate209.phi 291840 1024 177417568886026089 25888789655 178040128721558846 26070796413 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_292864 : DualFrontier209.checkFrom FactorFullCertificate209.phi 292864 1024 178040128721558846 26070796413 178662737580206045 26253455127 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_293888 : DualFrontier209.checkFrom FactorFullCertificate209.phi 293888 1024 178662737580206045 26253455127 179285133607726030 26436688727 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_286720 : DualFrontier209.checkFrom FactorFullCertificate209.phi 286720 8192 174304939135905264 24988367595 179285133607726030 26436688727 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 286720 174304939135905264 24988367595 174927752071877803 25167259633 7168 179285133607726030 26436688727 checked_small_286720 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 287744 174927752071877803 25167259633 175550075230590289 25346648309 6144 179285133607726030 26436688727 checked_small_287744 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 288768 175550075230590289 25346648309 176172661028503467 25526750149 5120 179285133607726030 26436688727 checked_small_288768 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 289792 176172661028503467 25526750149 176795103724580749 25707447973 4096 179285133607726030 26436688727 checked_small_289792 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 290816 176795103724580749 25707447973 177417568886026089 25888789655 3072 179285133607726030 26436688727 checked_small_290816 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 291840 177417568886026089 25888789655 178040128721558846 26070796413 2048 179285133607726030 26436688727 checked_small_291840 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 292864 178040128721558846 26070796413 178662737580206045 26253455127 1024 179285133607726030 26436688727 checked_small_292864 checked_small_293888)))))))
#print axioms checked_part_286720
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 262144 32768 159364627132252140 20888264643 179285133607726030 26436688727 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 262144 159364627132252140 20888264643 164344631172231104 22214141889 24576 179285133607726030 26436688727 checked_part_262144 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 270336 164344631172231104 22214141889 169325016375020190 23580920375 16384 179285133607726030 26436688727 checked_part_270336 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 278528 169325016375020190 23580920375 174304939135905264 24988367595 8192 179285133607726030 26436688727 checked_part_278528 checked_part_286720)))
theorem block_sound :
    (179285133607726030 = FrontierCheck209.massFloor FactorFullCertificate209.phi 294912 ∧
     26436688727 = FrontierCheck209.triangle FactorFullCertificate209.phi 294912) ∧
    ∀ t, 262144 < t → t ≤ 294912 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 262144 159364627132252140 20888264643 179285133607726030 26436688727 FullPrefix209_007.endpoint.1 FullPrefix209_007.endpoint.2 checked
theorem endpoint :
    179285133607726030 = FrontierCheck209.massFloor FactorFullCertificate209.phi 294912 ∧
    26436688727 = FrontierCheck209.triangle FactorFullCertificate209.phi 294912 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 294912) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 262144
  · exact FullPrefix209_007.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_008
