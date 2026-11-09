module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_006

@[expose] public section
namespace JSP233.FullPrefix209_007
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_229376 : DualFrontier209.checkFrom FactorFullCertificate209.phi 229376 1024 139444106035683565 15992590767 140066513073125636 16135674841 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_230400 : DualFrontier209.checkFrom FactorFullCertificate209.phi 230400 1024 140066513073125636 16135674841 140689183836082721 16279457175 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_231424 : DualFrontier209.checkFrom FactorFullCertificate209.phi 231424 1024 140689183836082721 16279457175 141311782744584362 16423860581 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_232448 : DualFrontier209.checkFrom FactorFullCertificate209.phi 232448 1024 141311782744584362 16423860581 141934043541219925 16568822675 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_233472 : DualFrontier209.checkFrom FactorFullCertificate209.phi 233472 1024 141934043541219925 16568822675 142556520306546828 16714472349 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_234496 : DualFrontier209.checkFrom FactorFullCertificate209.phi 234496 1024 142556520306546828 16714472349 143179304324343321 16860831757 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_235520 : DualFrontier209.checkFrom FactorFullCertificate209.phi 235520 1024 143179304324343321 16860831757 143801713568795079 17007740523 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_236544 : DualFrontier209.checkFrom FactorFullCertificate209.phi 236544 1024 143801713568795079 17007740523 144424101384233661 17155281433 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_229376 : DualFrontier209.checkFrom FactorFullCertificate209.phi 229376 8192 139444106035683565 15992590767 144424101384233661 17155281433 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 229376 139444106035683565 15992590767 140066513073125636 16135674841 7168 144424101384233661 17155281433 checked_small_229376 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 230400 140066513073125636 16135674841 140689183836082721 16279457175 6144 144424101384233661 17155281433 checked_small_230400 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 231424 140689183836082721 16279457175 141311782744584362 16423860581 5120 144424101384233661 17155281433 checked_small_231424 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 232448 141311782744584362 16423860581 141934043541219925 16568822675 4096 144424101384233661 17155281433 checked_small_232448 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 233472 141934043541219925 16568822675 142556520306546828 16714472349 3072 144424101384233661 17155281433 checked_small_233472 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 234496 142556520306546828 16714472349 143179304324343321 16860831757 2048 144424101384233661 17155281433 checked_small_234496 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 235520 143179304324343321 16860831757 143801713568795079 17007740523 1024 144424101384233661 17155281433 checked_small_235520 checked_small_236544)))))))
#print axioms checked_part_229376
private theorem checked_small_237568 : DualFrontier209.checkFrom FactorFullCertificate209.phi 237568 1024 144424101384233661 17155281433 145046876917829428 17303552047 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_238592 : DualFrontier209.checkFrom FactorFullCertificate209.phi 238592 1024 145046876917829428 17303552047 145669133085710808 17452336197 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_239616 : DualFrontier209.checkFrom FactorFullCertificate209.phi 239616 1024 145669133085710808 17452336197 146291695996055202 17601831083 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_240640 : DualFrontier209.checkFrom FactorFullCertificate209.phi 240640 1024 146291695996055202 17601831083 146914351408589323 17751985877 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_241664 : DualFrontier209.checkFrom FactorFullCertificate209.phi 241664 1024 146914351408589323 17751985877 147536776704792134 17902722559 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_242688 : DualFrontier209.checkFrom FactorFullCertificate209.phi 242688 1024 147536776704792134 17902722559 148159348946689519 18054132325 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_243712 : DualFrontier209.checkFrom FactorFullCertificate209.phi 243712 1024 148159348946689519 18054132325 148781963586794014 18206190037 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_244736 : DualFrontier209.checkFrom FactorFullCertificate209.phi 244736 1024 148781963586794014 18206190037 149404339210705720 18358826667 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_237568 : DualFrontier209.checkFrom FactorFullCertificate209.phi 237568 8192 144424101384233661 17155281433 149404339210705720 18358826667 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 237568 144424101384233661 17155281433 145046876917829428 17303552047 7168 149404339210705720 18358826667 checked_small_237568 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 238592 145046876917829428 17303552047 145669133085710808 17452336197 6144 149404339210705720 18358826667 checked_small_238592 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 239616 145669133085710808 17452336197 146291695996055202 17601831083 5120 149404339210705720 18358826667 checked_small_239616 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 240640 146291695996055202 17601831083 146914351408589323 17751985877 4096 149404339210705720 18358826667 checked_small_240640 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 241664 146914351408589323 17751985877 147536776704792134 17902722559 3072 149404339210705720 18358826667 checked_small_241664 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 242688 147536776704792134 17902722559 148159348946689519 18054132325 2048 149404339210705720 18358826667 checked_small_242688 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 243712 148159348946689519 18054132325 148781963586794014 18206190037 1024 149404339210705720 18358826667 checked_small_243712 checked_small_244736)))))))
#print axioms checked_part_237568
private theorem checked_small_245760 : DualFrontier209.checkFrom FactorFullCertificate209.phi 245760 1024 149404339210705720 18358826667 150026982557723639 18512166533 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_246784 : DualFrontier209.checkFrom FactorFullCertificate209.phi 246784 1024 150026982557723639 18512166533 150649463914263344 18666103973 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_247808 : DualFrontier209.checkFrom FactorFullCertificate209.phi 247808 1024 150649463914263344 18666103973 151271893594731598 18820665935 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_248832 : DualFrontier209.checkFrom FactorFullCertificate209.phi 248832 1024 151271893594731598 18820665935 151894316657951294 18975863521 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_249856 : DualFrontier209.checkFrom FactorFullCertificate209.phi 249856 1024 151894316657951294 18975863521 152516991309376818 19131761493 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_250880 : DualFrontier209.checkFrom FactorFullCertificate209.phi 250880 1024 152516991309376818 19131761493 153139538862596020 19288265229 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_251904 : DualFrontier209.checkFrom FactorFullCertificate209.phi 251904 1024 153139538862596020 19288265229 153761945294997856 19445370785 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_252928 : DualFrontier209.checkFrom FactorFullCertificate209.phi 252928 1024 153761945294997856 19445370785 154384749572560955 19603214613 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_245760 : DualFrontier209.checkFrom FactorFullCertificate209.phi 245760 8192 149404339210705720 18358826667 154384749572560955 19603214613 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 245760 149404339210705720 18358826667 150026982557723639 18512166533 7168 154384749572560955 19603214613 checked_small_245760 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 246784 150026982557723639 18512166533 150649463914263344 18666103973 6144 154384749572560955 19603214613 checked_small_246784 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 247808 150649463914263344 18666103973 151271893594731598 18820665935 5120 154384749572560955 19603214613 checked_small_247808 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 248832 151271893594731598 18820665935 151894316657951294 18975863521 4096 154384749572560955 19603214613 checked_small_248832 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 249856 151894316657951294 18975863521 152516991309376818 19131761493 3072 154384749572560955 19603214613 checked_small_249856 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 250880 152516991309376818 19131761493 153139538862596020 19288265229 2048 154384749572560955 19603214613 checked_small_250880 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 251904 153139538862596020 19288265229 153761945294997856 19445370785 1024 154384749572560955 19603214613 checked_small_251904 checked_small_252928)))))))
#print axioms checked_part_245760
private theorem checked_small_253952 : DualFrontier209.checkFrom FactorFullCertificate209.phi 253952 1024 154384749572560955 19603214613 155006888950725613 19761526951 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_254976 : DualFrontier209.checkFrom FactorFullCertificate209.phi 254976 1024 155006888950725613 19761526951 155629490167537138 19920594203 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_256000 : DualFrontier209.checkFrom FactorFullCertificate209.phi 256000 1024 155629490167537138 19920594203 156252212581115721 20080330231 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_257024 : DualFrontier209.checkFrom FactorFullCertificate209.phi 257024 1024 156252212581115721 20080330231 156874507569495383 20240593849 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_258048 : DualFrontier209.checkFrom FactorFullCertificate209.phi 258048 1024 156874507569495383 20240593849 157497011950358272 20401548711 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_259072 : DualFrontier209.checkFrom FactorFullCertificate209.phi 259072 1024 157497011950358272 20401548711 158119686507934158 20563185267 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_260096 : DualFrontier209.checkFrom FactorFullCertificate209.phi 260096 1024 158119686507934158 20563185267 158742072633307798 20725384289 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_261120 : DualFrontier209.checkFrom FactorFullCertificate209.phi 261120 1024 158742072633307798 20725384289 159364627132252140 20888264643 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_253952 : DualFrontier209.checkFrom FactorFullCertificate209.phi 253952 8192 154384749572560955 19603214613 159364627132252140 20888264643 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 253952 154384749572560955 19603214613 155006888950725613 19761526951 7168 159364627132252140 20888264643 checked_small_253952 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 254976 155006888950725613 19761526951 155629490167537138 19920594203 6144 159364627132252140 20888264643 checked_small_254976 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 256000 155629490167537138 19920594203 156252212581115721 20080330231 5120 159364627132252140 20888264643 checked_small_256000 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 257024 156252212581115721 20080330231 156874507569495383 20240593849 4096 159364627132252140 20888264643 checked_small_257024 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 258048 156874507569495383 20240593849 157497011950358272 20401548711 3072 159364627132252140 20888264643 checked_small_258048 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 259072 157497011950358272 20401548711 158119686507934158 20563185267 2048 159364627132252140 20888264643 checked_small_259072 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 260096 158119686507934158 20563185267 158742072633307798 20725384289 1024 159364627132252140 20888264643 checked_small_260096 checked_small_261120)))))))
#print axioms checked_part_253952
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 229376 32768 139444106035683565 15992590767 159364627132252140 20888264643 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 229376 139444106035683565 15992590767 144424101384233661 17155281433 24576 159364627132252140 20888264643 checked_part_229376 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 237568 144424101384233661 17155281433 149404339210705720 18358826667 16384 159364627132252140 20888264643 checked_part_237568 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 245760 149404339210705720 18358826667 154384749572560955 19603214613 8192 159364627132252140 20888264643 checked_part_245760 checked_part_253952)))
theorem block_sound :
    (159364627132252140 = FrontierCheck209.massFloor FactorFullCertificate209.phi 262144 ∧
     20888264643 = FrontierCheck209.triangle FactorFullCertificate209.phi 262144) ∧
    ∀ t, 229376 < t → t ≤ 262144 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 229376 139444106035683565 15992590767 159364627132252140 20888264643 FullPrefix209_006.endpoint.1 FullPrefix209_006.endpoint.2 checked
theorem endpoint :
    159364627132252140 = FrontierCheck209.massFloor FactorFullCertificate209.phi 262144 ∧
    20888264643 = FrontierCheck209.triangle FactorFullCertificate209.phi 262144 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 262144) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 229376
  · exact FullPrefix209_006.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_007
