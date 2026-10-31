import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_035
namespace JSP233.FullPrefix209_036
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1179648 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1179648 1024 717140127776494276 422986540117 717762702628649643 423721278225 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1180672 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1180672 1024 717762702628649643 423721278225 718385289924551677 424456668607 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1181696 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1181696 1024 718385289924551677 424456668607 719007640405615196 425192416509 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1182720 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1182720 1024 719007640405615196 425192416509 719630196931893179 425929045437 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1183744 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1183744 1024 719630196931893179 425929045437 720252913272244421 426666501243 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1184768 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1184768 1024 720252913272244421 426666501243 720875273122559811 427404172189 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1185792 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1185792 1024 720875273122559811 427404172189 721497751479943962 428142620915 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1186816 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1186816 1024 721497751479943962 428142620915 722120407257364266 428881917767 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1179648 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1179648 8192 717140127776494276 422986540117 722120407257364266 428881917767 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1179648 717140127776494276 422986540117 717762702628649643 423721278225 7168 722120407257364266 428881917767 checked_small_1179648 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1180672 717762702628649643 423721278225 718385289924551677 424456668607 6144 722120407257364266 428881917767 checked_small_1180672 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1181696 718385289924551677 424456668607 719007640405615196 425192416509 5120 722120407257364266 428881917767 checked_small_1181696 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1182720 719007640405615196 425192416509 719630196931893179 425929045437 4096 722120407257364266 428881917767 checked_small_1182720 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1183744 719630196931893179 425929045437 720252913272244421 426666501243 3072 722120407257364266 428881917767 checked_small_1183744 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1184768 720252913272244421 426666501243 720875273122559811 427404172189 2048 722120407257364266 428881917767 checked_small_1184768 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1185792 720875273122559811 427404172189 721497751479943962 428142620915 1024 722120407257364266 428881917767 checked_small_1185792 checked_small_1186816)))))))
#print axioms checked_part_1179648
private theorem checked_small_1187840 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1187840 1024 722120407257364266 428881917767 722742879631505200 429621634317 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1188864 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1188864 1024 722742879631505200 429621634317 723365289276106220 430361913597 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1189888 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1189888 1024 723365289276106220 430361913597 723988106543463316 431103315551 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1190912 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1190912 1024 723988106543463316 431103315551 724610290242383075 431844600403 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1191936 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1191936 1024 724610290242383075 431844600403 725232906873102941 432587038503 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1192960 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1192960 1024 725232906873102941 432587038503 725855525755050994 433330116951 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1193984 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1193984 1024 725855525755050994 433330116951 726477907088614749 434073549193 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1195008 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1195008 1024 726477907088614749 434073549193 727100442778499716 434817803227 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1187840 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1187840 8192 722120407257364266 428881917767 727100442778499716 434817803227 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1187840 722120407257364266 428881917767 722742879631505200 429621634317 7168 727100442778499716 434817803227 checked_small_1187840 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1188864 722742879631505200 429621634317 723365289276106220 430361913597 6144 727100442778499716 434817803227 checked_small_1188864 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1189888 723365289276106220 430361913597 723988106543463316 431103315551 5120 727100442778499716 434817803227 checked_small_1189888 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1190912 723988106543463316 431103315551 724610290242383075 431844600403 4096 727100442778499716 434817803227 checked_small_1190912 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1191936 724610290242383075 431844600403 725232906873102941 432587038503 3072 727100442778499716 434817803227 checked_small_1191936 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1192960 725232906873102941 432587038503 725855525755050994 433330116951 2048 727100442778499716 434817803227 checked_small_1192960 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1193984 725855525755050994 433330116951 726477907088614749 434073549193 1024 727100442778499716 434817803227 checked_small_1193984 checked_small_1195008)))))))
#print axioms checked_part_1187840
private theorem checked_small_1196032 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1196032 1024 727100442778499716 434817803227 727722967365652493 435562681467 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1197056 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1197056 1024 727722967365652493 435562681467 728345412541636165 436308102039 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1198080 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1198080 1024 728345412541636165 436308102039 728968112073408355 437054464917 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1199104 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1199104 1024 728968112073408355 437054464917 729590698706203015 437801330139 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1200128 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1200128 1024 729590698706203015 437801330139 730212927774122794 438548403469 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1201152 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1201152 1024 730212927774122794 438548403469 730835450891353437 439296467161 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1202176 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1202176 1024 730835450891353437 439296467161 731458229656464304 440045475923 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1203200 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1203200 1024 731458229656464304 440045475923 732080711217562172 440794764775 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1196032 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1196032 8192 727100442778499716 434817803227 732080711217562172 440794764775 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1196032 727100442778499716 434817803227 727722967365652493 435562681467 7168 732080711217562172 440794764775 checked_small_1196032 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1197056 727722967365652493 435562681467 728345412541636165 436308102039 6144 732080711217562172 440794764775 checked_small_1197056 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1198080 728345412541636165 436308102039 728968112073408355 437054464917 5120 732080711217562172 440794764775 checked_small_1198080 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1199104 728968112073408355 437054464917 729590698706203015 437801330139 4096 732080711217562172 440794764775 checked_small_1199104 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1200128 729590698706203015 437801330139 730212927774122794 438548403469 3072 732080711217562172 440794764775 checked_small_1200128 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1201152 730212927774122794 438548403469 730835450891353437 439296467161 2048 732080711217562172 440794764775 checked_small_1201152 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1202176 730835450891353437 439296467161 731458229656464304 440045475923 1024 732080711217562172 440794764775 checked_small_1202176 checked_small_1203200)))))))
#print axioms checked_part_1196032
private theorem checked_small_1204224 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1204224 1024 732080711217562172 440794764775 732703012697908567 441544473973 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1205248 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1205248 1024 732703012697908567 441544473973 733325737744163415 442295331129 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1206272 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1206272 1024 733325737744163415 442295331129 733948078271107455 443046361929 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1207296 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1207296 1024 733948078271107455 443046361929 734570510105810727 443798140157 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1208320 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1208320 1024 734570510105810727 443798140157 735193298769729176 444550987201 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1209344 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1209344 1024 735193298769729176 444550987201 735815602121790441 445303884851 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1210368 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1210368 1024 735815602121790441 445303884851 736438134012350812 446057696373 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1211392 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1211392 1024 736438134012350812 446057696373 737060773908577479 446812276329 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1204224 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1204224 8192 732080711217562172 440794764775 737060773908577479 446812276329 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1204224 732080711217562172 440794764775 732703012697908567 441544473973 7168 737060773908577479 446812276329 checked_small_1204224 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1205248 732703012697908567 441544473973 733325737744163415 442295331129 6144 737060773908577479 446812276329 checked_small_1205248 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1206272 733325737744163415 442295331129 733948078271107455 443046361929 5120 737060773908577479 446812276329 checked_small_1206272 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1207296 733948078271107455 443046361929 734570510105810727 443798140157 4096 737060773908577479 446812276329 checked_small_1207296 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1208320 734570510105810727 443798140157 735193298769729176 444550987201 3072 737060773908577479 446812276329 checked_small_1208320 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1209344 735193298769729176 444550987201 735815602121790441 445303884851 2048 737060773908577479 446812276329 checked_small_1209344 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1210368 735815602121790441 445303884851 736438134012350812 446057696373 1024 737060773908577479 446812276329 checked_small_1210368 checked_small_1211392)))))))
#print axioms checked_part_1204224
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1179648 32768 717140127776494276 422986540117 737060773908577479 446812276329 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1179648 717140127776494276 422986540117 722120407257364266 428881917767 24576 737060773908577479 446812276329 checked_part_1179648 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1187840 722120407257364266 428881917767 727100442778499716 434817803227 16384 737060773908577479 446812276329 checked_part_1187840 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1196032 727100442778499716 434817803227 732080711217562172 440794764775 8192 737060773908577479 446812276329 checked_part_1196032 checked_part_1204224)))
theorem block_sound :
    (737060773908577479 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1212416 ∧
     446812276329 = FrontierCheck209.triangle FactorFullCertificate209.phi 1212416) ∧
    ∀ t, 1179648 < t → t ≤ 1212416 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1179648 717140127776494276 422986540117 737060773908577479 446812276329 FullPrefix209_035.endpoint.1 FullPrefix209_035.endpoint.2 checked
theorem endpoint :
    737060773908577479 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1212416 ∧
    446812276329 = FrontierCheck209.triangle FactorFullCertificate209.phi 1212416 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1212416) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1179648
  · exact FullPrefix209_035.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_036
