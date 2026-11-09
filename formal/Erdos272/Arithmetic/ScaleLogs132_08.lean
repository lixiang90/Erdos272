module

public import Erdos272.Arithmetic.PrefixTable132

@[expose] public section
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_2353 : (77634461043/5000000000:ℝ)≤Real.log ((2353:ℝ)^2) ∧ Real.log ((2353:ℝ)^2)≤(38817232913/2500000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have he : Real.log ((2353:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((2353:ℝ)^2)=2*Real.log (2353:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (181:ℝ)) := by
           rw [show (2353:ℝ)=(13:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h181.1,h181.2]

theorem scale_2363 : (19419217487/1250000000:ℝ)≤Real.log ((2363:ℝ)^2) ∧ Real.log ((2363:ℝ)^2)≤(77676874689/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have he : Real.log ((2363:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((2363:ℝ)^2)=2*Real.log (2363:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (139:ℝ)) := by
           rw [show (2363:ℝ)=(17:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h139.1,h139.2]

theorem scale_2369 : (77702229249/5000000000:ℝ)≤Real.log ((2369:ℝ)^2) ∧ Real.log ((2369:ℝ)^2)≤(9712779241/625000000:ℝ) := by
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((2369:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((2369:ℝ)^2)=2*Real.log (2369:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (103:ℝ)) := by
           rw [show (2369:ℝ)=(23:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h103.1,h103.2,h23.1,h23.2]

theorem scale_2407 : (77861361629/5000000000:ℝ)≤Real.log ((2407:ℝ)^2) ∧ Real.log ((2407:ℝ)^2)≤(9732670779/625000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((2407:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((2407:ℝ)^2)=2*Real.log (2407:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (83:ℝ)) := by
           rw [show (2407:ℝ)=(29:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h29.1,h29.2]

theorem scale_2413 : (77886257839/5000000000:ℝ)≤Real.log ((2413:ℝ)^2) ∧ Real.log ((2413:ℝ)^2)≤(15577252513/1000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((2413:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((2413:ℝ)^2)=2*Real.log (2413:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (127:ℝ)) := by
           rw [show (2413:ℝ)=(19:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h127.1,h127.2]

theorem scale_2419 : (38955545409/2500000000:ℝ)≤Real.log ((2419:ℝ)^2) ∧ Real.log ((2419:ℝ)^2)≤(608680453/39062500:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have he : Real.log ((2419:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((2419:ℝ)^2)=2*Real.log (2419:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (59:ℝ)) := by
           rw [show (2419:ℝ)=(41:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h59.1,h59.2]

theorem scale_2449 : (15606869567/1000000000:ℝ)≤Real.log ((2449:ℝ)^2) ∧ Real.log ((2449:ℝ)^2)≤(78034352413/5000000000:ℝ) := by
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((2449:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((2449:ℝ)^2)=2*Real.log (2449:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (79:ℝ)) := by
           rw [show (2449:ℝ)=(31:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h79.1,h79.2,h31.1,h31.2]

theorem scale_2461 : (39041613853/2500000000:ℝ)≤Real.log ((2461:ℝ)^2) ∧ Real.log ((2461:ℝ)^2)≤(15616646479/1000000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((2461:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((2461:ℝ)^2)=2*Real.log (2461:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (107:ℝ)) := by
           rw [show (2461:ℝ)=(23:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h23.1,h23.2]

theorem scale_2479 : (78156101453/5000000000:ℝ)≤Real.log ((2479:ℝ)^2) ∧ Real.log ((2479:ℝ)^2)≤(39078053959/2500000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((2479:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((2479:ℝ)^2)=2*Real.log (2479:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (67:ℝ)) := by
           rw [show (2479:ℝ)=(37:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h37.1,h37.2]

theorem scale_2483 : (15634445001/1000000000:ℝ)≤Real.log ((2483:ℝ)^2) ∧ Real.log ((2483:ℝ)^2)≤(78172229799/5000000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have he : Real.log ((2483:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((2483:ℝ)^2)=2*Real.log (2483:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (191:ℝ)) := by
           rw [show (2483:ℝ)=(13:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h191.1,h191.2]

theorem scale_2489 : (19549090051/1250000000:ℝ)≤Real.log ((2489:ℝ)^2) ∧ Real.log ((2489:ℝ)^2)≤(15639272987/1000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have he : Real.log ((2489:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((2489:ℝ)^2)=2*Real.log (2489:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (131:ℝ)) := by
           rw [show (2489:ℝ)=(19:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h131.1,h131.2]

theorem scale_2491 : (39102195281/2500000000:ℝ)≤Real.log ((2491:ℝ)^2) ∧ Real.log ((2491:ℝ)^2)≤(9775549779/625000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((2491:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((2491:ℝ)^2)=2*Real.log (2491:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (53:ℝ)) := by
           rw [show (2491:ℝ)=(47:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h47.1,h47.2]

theorem scale_2501 : (7824445499/500000000:ℝ)≤Real.log ((2501:ℝ)^2) ∧ Real.log ((2501:ℝ)^2)≤(611284861/39062500:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((2501:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((2501:ℝ)^2)=2*Real.log (2501:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (61:ℝ)) := by
           rw [show (2501:ℝ)=(41:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h61.1,h61.2]

theorem scale_2507 : (78268418181/5000000000:ℝ)≤Real.log ((2507:ℝ)^2) ∧ Real.log ((2507:ℝ)^2)≤(626147383/40000000:ℝ) := by
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((2507:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((2507:ℝ)^2)=2*Real.log (2507:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (109:ℝ)) := by
           rw [show (2507:ℝ)=(23:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h109.1,h109.2,h23.1,h23.2]

theorem scale_2509 : (19569098153/1250000000:ℝ)≤Real.log ((2509:ℝ)^2) ∧ Real.log ((2509:ℝ)^2)≤(2446137419/156250000:ℝ) := by
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((2509:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((2509:ℝ)^2)=2*Real.log (2509:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (193:ℝ)) := by
           rw [show (2509:ℝ)=(13:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h193.1,h193.2,h13.1,h13.2]

theorem scale_2533 : (78371593669/5000000000:ℝ)≤Real.log ((2533:ℝ)^2) ∧ Real.log ((2533:ℝ)^2)≤(78371598421/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((2533:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((2533:ℝ)^2)=2*Real.log (2533:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (149:ℝ)) := by
           rw [show (2533:ℝ)=(17:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h149.1,h149.2]

theorem scale_2537 : (78387371129/5000000000:ℝ)≤Real.log ((2537:ℝ)^2) ∧ Real.log ((2537:ℝ)^2)≤(78387378593/5000000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have he : Real.log ((2537:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((2537:ℝ)^2)=2*Real.log (2537:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (59:ℝ)) := by
           rw [show (2537:ℝ)=(43:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h43.1,h43.2]

theorem scale_2561 : (9810191001/625000000:ℝ)≤Real.log ((2561:ℝ)^2) ∧ Real.log ((2561:ℝ)^2)≤(78481532809/5000000000:ℝ) := by
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((2561:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((2561:ℝ)^2)=2*Real.log (2561:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (197:ℝ)) := by
           rw [show (2561:ℝ)=(13:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h197.1,h197.2,h13.1,h13.2]

theorem scale_2567 : (78504928977/5000000000:ℝ)≤Real.log ((2567:ℝ)^2) ∧ Real.log ((2567:ℝ)^2)≤(78504933731/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((2567:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((2567:ℝ)^2)=2*Real.log (2567:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (151:ℝ)) := by
           rw [show (2567:ℝ)=(17:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h151.1,h151.2]

theorem scale_2573 : (78528275373/5000000000:ℝ)≤Real.log ((2573:ℝ)^2) ∧ Real.log ((2573:ℝ)^2)≤(39264139989/2500000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((2573:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((2573:ℝ)^2)=2*Real.log (2573:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (83:ℝ)) := by
           rw [show (2573:ℝ)=(31:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h31.1,h31.2]

theorem scale_2581 : (7855931923/500000000:ℝ)≤Real.log ((2581:ℝ)^2) ∧ Real.log ((2581:ℝ)^2)≤(9819915483/625000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((2581:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((2581:ℝ)^2)=2*Real.log (2581:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (89:ℝ)) := by
           rw [show (2581:ℝ)=(29:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h29.1,h29.2]

theorem scale_2587 : (78582538967/5000000000:ℝ)≤Real.log ((2587:ℝ)^2) ∧ Real.log ((2587:ℝ)^2)≤(7858254377/500000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have he : Real.log ((2587:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((2587:ℝ)^2)=2*Real.log (2587:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (199:ℝ)) := by
           rw [show (2587:ℝ)=(13:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h199.1,h199.2]

theorem scale_2599 : (78628817541/5000000000:ℝ)≤Real.log ((2599:ℝ)^2) ∧ Real.log ((2599:ℝ)^2)≤(19657205561/1250000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((2599:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((2599:ℝ)^2)=2*Real.log (2599:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (113:ℝ)) := by
           rw [show (2599:ℝ)=(23:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h23.1,h23.2]

theorem scale_2603 : (39322098113/2500000000:ℝ)≤Real.log ((2603:ℝ)^2) ∧ Real.log ((2603:ℝ)^2)≤(78644200967/5000000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((2603:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((2603:ℝ)^2)=2*Real.log (2603:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (137:ℝ)) := by
           rw [show (2603:ℝ)=(19:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h19.1,h19.2]

theorem scale_2623 : (78720735301/5000000000:ℝ)≤Real.log ((2623:ℝ)^2) ∧ Real.log ((2623:ℝ)^2)≤(78720742817/5000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((2623:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((2623:ℝ)^2)=2*Real.log (2623:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (61:ℝ)) := by
           rw [show (2623:ℝ)=(43:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h61.1,h61.2]

theorem scale_2627 : (39367986999/2500000000:ℝ)≤Real.log ((2627:ℝ)^2) ∧ Real.log ((2627:ℝ)^2)≤(78735980517/5000000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((2627:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((2627:ℝ)^2)=2*Real.log (2627:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (71:ℝ)) := by
           rw [show (2627:ℝ)=(37:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h71.1,h71.2]

theorem scale_2641 : (39394563149/2500000000:ℝ)≤Real.log ((2641:ℝ)^2) ∧ Real.log ((2641:ℝ)^2)≤(78789131041/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have he : Real.log ((2641:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((2641:ℝ)^2)=2*Real.log (2641:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (139:ℝ)) := by
           rw [show (2641:ℝ)=(19:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h139.1,h139.2]

theorem scale_2669 : (78894588659/5000000000:ℝ)≤Real.log ((2669:ℝ)^2) ∧ Real.log ((2669:ℝ)^2)≤(78894593421/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((2669:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((2669:ℝ)^2)=2*Real.log (2669:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (157:ℝ)) := by
           rw [show (2669:ℝ)=(17:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h157.1,h157.2]

theorem scale_2701 : (39506884813/2500000000:ℝ)≤Real.log ((2701:ℝ)^2) ∧ Real.log ((2701:ℝ)^2)≤(79013776167/5000000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((2701:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((2701:ℝ)^2)=2*Real.log (2701:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (73:ℝ)) := by
           rw [show (2701:ℝ)=(37:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h37.1,h37.2]

theorem scale_2747 : (79182642473/5000000000:ℝ)≤Real.log ((2747:ℝ)^2) ∧ Real.log ((2747:ℝ)^2)≤(79182649807/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have he : Real.log ((2747:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((2747:ℝ)^2)=2*Real.log (2747:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (67:ℝ)) := by
           rw [show (2747:ℝ)=(41:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h67.1,h67.2]

theorem scale_2759 : (39613116487/2500000000:ℝ)≤Real.log ((2759:ℝ)^2) ∧ Real.log ((2759:ℝ)^2)≤(7922623761/500000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((2759:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((2759:ℝ)^2)=2*Real.log (2759:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (89:ℝ)) := by
           rw [show (2759:ℝ)=(31:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h31.1,h31.2]

theorem scale_2771 : (7926963261/500000000:ℝ)≤Real.log ((2771:ℝ)^2) ∧ Real.log ((2771:ℝ)^2)≤(79269637379/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have he : Real.log ((2771:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((2771:ℝ)^2)=2*Real.log (2771:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (163:ℝ)) := by
           rw [show (2771:ℝ)=(17:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h163.1,h163.2]

theorem scale_2773 : (79276845733/5000000000:ℝ)≤Real.log ((2773:ℝ)^2) ∧ Real.log ((2773:ℝ)^2)≤(79276853623/5000000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((2773:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((2773:ℝ)^2)=2*Real.log (2773:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (59:ℝ)) := by
           rw [show (2773:ℝ)=(47:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h47.1,h47.2]

theorem scale_2813 : (79420065299/5000000000:ℝ)≤Real.log ((2813:ℝ)^2) ∧ Real.log ((2813:ℝ)^2)≤(39710034983/2500000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((2813:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((2813:ℝ)^2)=2*Real.log (2813:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (97:ℝ)) := by
           rw [show (2813:ℝ)=(29:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h29.1,h29.2]

theorem scale_2831 : (79483850019/5000000000:ℝ)≤Real.log ((2831:ℝ)^2) ∧ Real.log ((2831:ℝ)^2)≤(79483854773/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((2831:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((2831:ℝ)^2)=2*Real.log (2831:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (149:ℝ)) := by
           rw [show (2831:ℝ)=(19:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h149.1,h149.2]

theorem scale_2839 : (19878017181/1250000000:ℝ)≤Real.log ((2839:ℝ)^2) ∧ Real.log ((2839:ℝ)^2)≤(79512073497/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have he : Real.log ((2839:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((2839:ℝ)^2)=2*Real.log (2839:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (167:ℝ)) := by
           rw [show (2839:ℝ)=(17:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h167.1,h167.2]

theorem scale_2867 : (15922041981/1000000000:ℝ)≤Real.log ((2867:ℝ)^2) ∧ Real.log ((2867:ℝ)^2)≤(79610217847/5000000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((2867:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((2867:ℝ)^2)=2*Real.log (2867:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (61:ℝ)) := by
           rw [show (2867:ℝ)=(47:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h47.1,h47.2]

theorem scale_2869 : (79617185327/5000000000:ℝ)≤Real.log ((2869:ℝ)^2) ∧ Real.log ((2869:ℝ)^2)≤(79617190083/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((2869:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((2869:ℝ)^2)=2*Real.log (2869:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (151:ℝ)) := by
           rw [show (2869:ℝ)=(19:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h151.1,h151.2]

theorem scale_2881 : (2489341337/156250000:ℝ)≤Real.log ((2881:ℝ)^2) ∧ Real.log ((2881:ℝ)^2)≤(4978683151/312500000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have he : Real.log ((2881:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((2881:ℝ)^2)=2*Real.log (2881:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (67:ℝ)) := by
           rw [show (2881:ℝ)=(43:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h43.1,h43.2]

theorem scale_2911 : (39881257509/2500000000:ℝ)≤Real.log ((2911:ℝ)^2) ∧ Real.log ((2911:ℝ)^2)≤(39881261203/2500000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((2911:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((2911:ℝ)^2)=2*Real.log (2911:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (71:ℝ)) := by
           rw [show (2911:ℝ)=(41:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h71.1,h71.2]

theorem scale_2921 : (19949202551/1250000000:ℝ)≤Real.log ((2921:ℝ)^2) ∧ Real.log ((2921:ℝ)^2)≤(39898407467/2500000000:ℝ) := by
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((2921:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((2921:ℝ)^2)=2*Real.log (2921:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (127:ℝ)) := by
           rw [show (2921:ℝ)=(23:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h127.1,h127.2,h23.1,h23.2]

theorem scale_2923 : (79803653709/5000000000:ℝ)≤Real.log ((2923:ℝ)^2) ∧ Real.log ((2923:ℝ)^2)≤(39901830151/2500000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((2923:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((2923:ℝ)^2)=2*Real.log (2923:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (79:ℝ)) := by
           rw [show (2923:ℝ)=(37:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h79.1,h79.2]

theorem scale_2929 : (19956040169/1250000000:ℝ)≤Real.log ((2929:ℝ)^2) ∧ Real.log ((2929:ℝ)^2)≤(15964833071/1000000000:ℝ) := by
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((2929:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((2929:ℝ)^2)=2*Real.log (2929:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (101:ℝ)) := by
           rw [show (2929:ℝ)=(29:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h101.1,h101.2,h29.1,h29.2]

theorem scale_2941 : (39932523271/2500000000:ℝ)≤Real.log ((2941:ℝ)^2) ∧ Real.log ((2941:ℝ)^2)≤(79865051321/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have he : Real.log ((2941:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((2941:ℝ)^2)=2*Real.log (2941:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (173:ℝ)) := by
           rw [show (2941:ℝ)=(17:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h173.1,h173.2]

theorem scale_2983 : (80006845009/5000000000:ℝ)≤Real.log ((2983:ℝ)^2) ∧ Real.log ((2983:ℝ)^2)≤(80006849773/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((2983:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((2983:ℝ)^2)=2*Real.log (2983:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (157:ℝ)) := by
           rw [show (2983:ℝ)=(19:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h157.1,h157.2]

theorem scale_2987 : (80020245387/5000000000:ℝ)≤Real.log ((2987:ℝ)^2) ∧ Real.log ((2987:ℝ)^2)≤(10002531259/625000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((2987:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((2987:ℝ)^2)=2*Real.log (2987:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (103:ℝ)) := by
           rw [show (2987:ℝ)=(29:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h29.1,h29.2,h103.1,h103.2]

theorem scale_2993 : (40020155323/2500000000:ℝ)≤Real.log ((2993:ℝ)^2) ∧ Real.log ((2993:ℝ)^2)≤(10005039757/625000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have he : Real.log ((2993:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((2993:ℝ)^2)=2*Real.log (2993:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (73:ℝ)) := by
           rw [show (2993:ℝ)=(41:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h41.1,h41.2]

theorem scale_3007 : (80086979043/5000000000:ℝ)≤Real.log ((3007:ℝ)^2) ∧ Real.log ((3007:ℝ)^2)≤(2502718241/156250000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((3007:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((3007:ℝ)^2)=2*Real.log (3007:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (97:ℝ)) := by
           rw [show (3007:ℝ)=(31:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h31.1,h31.2]

theorem scale_3013 : (80106912569/5000000000:ℝ)≤Real.log ((3013:ℝ)^2) ∧ Real.log ((3013:ℝ)^2)≤(10013364663/625000000:ℝ) := by
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((3013:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((3013:ℝ)^2)=2*Real.log (3013:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (131:ℝ)) := by
           rw [show (3013:ℝ)=(23:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h131.1,h131.2,h23.1,h23.2]

theorem scale_3043 : (40102994327/2500000000:ℝ)≤Real.log ((3043:ℝ)^2) ∧ Real.log ((3043:ℝ)^2)≤(80205993439/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have he : Real.log ((3043:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((3043:ℝ)^2)=2*Real.log (3043:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (179:ℝ)) := by
           rw [show (3043:ℝ)=(17:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h179.1,h179.2]

#print axioms scale_2353
#print axioms scale_2363
#print axioms scale_2369
#print axioms scale_2407
#print axioms scale_2413
#print axioms scale_2419
#print axioms scale_2449
#print axioms scale_2461
#print axioms scale_2479
#print axioms scale_2483
#print axioms scale_2489
#print axioms scale_2491
#print axioms scale_2501
#print axioms scale_2507
#print axioms scale_2509
#print axioms scale_2533
#print axioms scale_2537
#print axioms scale_2561
#print axioms scale_2567
#print axioms scale_2573
#print axioms scale_2581
#print axioms scale_2587
#print axioms scale_2599
#print axioms scale_2603
#print axioms scale_2623
#print axioms scale_2627
#print axioms scale_2641
#print axioms scale_2669
#print axioms scale_2701
#print axioms scale_2747
#print axioms scale_2759
#print axioms scale_2771
#print axioms scale_2773
#print axioms scale_2813
#print axioms scale_2831
#print axioms scale_2839
#print axioms scale_2867
#print axioms scale_2869
#print axioms scale_2881
#print axioms scale_2911
#print axioms scale_2921
#print axioms scale_2923
#print axioms scale_2929
#print axioms scale_2941
#print axioms scale_2983
#print axioms scale_2987
#print axioms scale_2993
#print axioms scale_3007
#print axioms scale_3013
#print axioms scale_3043
end
end JSP233.ScaleLogs132
