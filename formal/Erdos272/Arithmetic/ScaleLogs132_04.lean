module

public import Erdos272.Arithmetic.PrefixTable132

@[expose] public section
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_543 : (1574277259/125000000:ℝ)≤Real.log ((543:ℝ)^2) ∧ Real.log ((543:ℝ)^2)≤(62971095133/5000000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have he : Real.log ((543:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((543:ℝ)^2)=2*Real.log (543:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (181:ℝ)) := by
           rw [show (543:ℝ)=(3:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h181.1,h181.2]

theorem scale_545 : (15751963789/1250000000:ℝ)≤Real.log ((545:ℝ)^2) ∧ Real.log ((545:ℝ)^2)≤(7875982479/625000000:ℝ) := by
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((545:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((545:ℝ)^2)=2*Real.log (545:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (109:ℝ)) := by
           rw [show (545:ℝ)=(5:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h109.1,h109.2,h5.1,h5.2]

theorem scale_551 : (12623469613/1000000000:ℝ)≤Real.log ((551:ℝ)^2) ∧ Real.log ((551:ℝ)^2)≤(63117348119/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((551:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (29:ℝ)) := by
    calc Real.log ((551:ℝ)^2)=2*Real.log (551:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (29:ℝ)) := by
           rw [show (551:ℝ)=(19:ℝ)*(29:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h29.1,h29.2]

theorem scale_553 : (63153577293/5000000000:ℝ)≤Real.log ((553:ℝ)^2) ∧ Real.log ((553:ℝ)^2)≤(63153581847/5000000000:ℝ) := by
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((553:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((553:ℝ)^2)=2*Real.log (553:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (79:ℝ)) := by
           rw [show (553:ℝ)=(7:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h79.1,h79.2,h7.1,h7.2]

theorem scale_559 : (39538433/3125000:ℝ)≤Real.log ((559:ℝ)^2) ∧ Real.log ((559:ℝ)^2)≤(1976921751/156250000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((559:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (43:ℝ)) := by
    calc Real.log ((559:ℝ)^2)=2*Real.log (559:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (43:ℝ)) := by
           rw [show (559:ℝ)=(13:ℝ)*(43:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h13.1,h13.2]

theorem scale_565 : (15842063629/1250000000:ℝ)≤Real.log ((565:ℝ)^2) ∧ Real.log ((565:ℝ)^2)≤(63368259201/5000000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((565:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((565:ℝ)^2)=2*Real.log (565:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (113:ℝ)) := by
           rw [show (565:ℝ)=(5:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h5.1,h5.2]

theorem scale_573 : (31754427161/2500000000:ℝ)≤Real.log ((573:ℝ)^2) ∧ Real.log ((573:ℝ)^2)≤(31754429553/2500000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have he : Real.log ((573:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((573:ℝ)^2)=2*Real.log (573:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (191:ℝ)) := by
           rw [show (573:ℝ)=(3:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h191.1,h191.2]

theorem scale_579 : (63613021929/5000000000:ℝ)≤Real.log ((579:ℝ)^2) ∧ Real.log ((579:ℝ)^2)≤(12722605343/1000000000:ℝ) := by
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((579:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((579:ℝ)^2)=2*Real.log (579:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (193:ℝ)) := by
           rw [show (579:ℝ)=(3:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h193.1,h193.2,h3.1,h3.2]

theorem scale_581 : (63647504831/5000000000:ℝ)≤Real.log ((581:ℝ)^2) ∧ Real.log ((581:ℝ)^2)≤(15911877353/1250000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((581:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((581:ℝ)^2)=2*Real.log (581:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (83:ℝ)) := by
           rw [show (581:ℝ)=(7:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h7.1,h7.2]

theorem scale_583 : (63681869447/5000000000:ℝ)≤Real.log ((583:ℝ)^2) ∧ Real.log ((583:ℝ)^2)≤(63681873489/5000000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((583:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((583:ℝ)^2)=2*Real.log (583:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (53:ℝ)) := by
           rw [show (583:ℝ)=(11:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h53.1,h53.2]

theorem scale_589 : (63784261809/5000000000:ℝ)≤Real.log ((589:ℝ)^2) ∧ Real.log ((589:ℝ)^2)≤(12756852373/1000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((589:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (31:ℝ)) := by
    calc Real.log ((589:ℝ)^2)=2*Real.log (589:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (31:ℝ)) := by
           rw [show (589:ℝ)=(19:ℝ)*(31:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h31.1,h31.2]

theorem scale_591 : (2552726293/200000000:ℝ)≤Real.log ((591:ℝ)^2) ∧ Real.log ((591:ℝ)^2)≤(15954540529/1250000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have he : Real.log ((591:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((591:ℝ)^2)=2*Real.log (591:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (197:ℝ)) := by
           rw [show (591:ℝ)=(3:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h197.1,h197.2]

theorem scale_597 : (15979792071/1250000000:ℝ)≤Real.log ((597:ℝ)^2) ∧ Real.log ((597:ℝ)^2)≤(63919173077/5000000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have he : Real.log ((597:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((597:ℝ)^2)=2*Real.log (597:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (199:ℝ)) := by
           rw [show (597:ℝ)=(3:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h199.1,h199.2]

theorem scale_611 : (16037741851/1250000000:ℝ)≤Real.log ((611:ℝ)^2) ∧ Real.log ((611:ℝ)^2)≤(32075485531/2500000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((611:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((611:ℝ)^2)=2*Real.log (611:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (47:ℝ)) := by
           rw [show (611:ℝ)=(13:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h47.1,h47.2]

theorem scale_623 : (2010795701/156250000:ℝ)≤Real.log ((623:ℝ)^2) ∧ Real.log ((623:ℝ)^2)≤(16086366761/1250000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((623:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((623:ℝ)^2)=2*Real.log (623:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (89:ℝ)) := by
           rw [show (623:ℝ)=(7:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h7.1,h7.2]

theorem scale_629 : (64441311333/5000000000:ℝ)≤Real.log ((629:ℝ)^2) ∧ Real.log ((629:ℝ)^2)≤(32220656701/2500000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((629:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (37:ℝ)) := by
    calc Real.log ((629:ℝ)^2)=2*Real.log (629:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (37:ℝ)) := by
           rw [show (629:ℝ)=(17:ℝ)*(37:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h37.1,h37.2]

theorem scale_635 : (64536247179/5000000000:ℝ)≤Real.log ((635:ℝ)^2) ∧ Real.log ((635:ℝ)^2)≤(64536251891/5000000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((635:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((635:ℝ)^2)=2*Real.log (635:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (127:ℝ)) := by
           rw [show (635:ℝ)=(5:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h127.1,h127.2]

theorem scale_649 : (32377162309/2500000000:ℝ)≤Real.log ((649:ℝ)^2) ∧ Real.log ((649:ℝ)^2)≤(809429111/62500000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((649:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((649:ℝ)^2)=2*Real.log (649:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (59:ℝ)) := by
           rw [show (649:ℝ)=(11:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h11.1,h11.2]

theorem scale_655 : (8105793693/625000000:ℝ)≤Real.log ((655:ℝ)^2) ∧ Real.log ((655:ℝ)^2)≤(64846354261/5000000000:ℝ) := by
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((655:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((655:ℝ)^2)=2*Real.log (655:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (131:ℝ)) := by
           rw [show (655:ℝ)=(5:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h131.1,h131.2,h5.1,h5.2]

theorem scale_667 : (6502790043/500000000:ℝ)≤Real.log ((667:ℝ)^2) ∧ Real.log ((667:ℝ)^2)≤(8128487561/625000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((667:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (29:ℝ)) := by
    calc Real.log ((667:ℝ)^2)=2*Real.log (667:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (29:ℝ)) := by
           rw [show (667:ℝ)=(23:ℝ)*(29:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h29.1,h29.2,h23.1,h23.2]

theorem scale_671 : (6508768879/500000000:ℝ)≤Real.log ((671:ℝ)^2) ∧ Real.log ((671:ℝ)^2)≤(4067980819/312500000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((671:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((671:ℝ)^2)=2*Real.log (671:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (61:ℝ)) := by
           rw [show (671:ℝ)=(11:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h61.1,h61.2]

theorem scale_679 : (65206208501/5000000000:ℝ)≤Real.log ((679:ℝ)^2) ∧ Real.log ((679:ℝ)^2)≤(32603106573/2500000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((679:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((679:ℝ)^2)=2*Real.log (679:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (97:ℝ)) := by
           rw [show (679:ℝ)=(7:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h7.1,h7.2]

theorem scale_685 : (32647092783/2500000000:ℝ)≤Real.log ((685:ℝ)^2) ∧ Real.log ((685:ℝ)^2)≤(65294190293/5000000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((685:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((685:ℝ)^2)=2*Real.log (685:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (137:ℝ)) := by
           rw [show (685:ℝ)=(5:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h5.1,h5.2]

theorem scale_689 : (16338102573/1250000000:ℝ)≤Real.log ((689:ℝ)^2) ∧ Real.log ((689:ℝ)^2)≤(510565737/39062500:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((689:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((689:ℝ)^2)=2*Real.log (689:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (53:ℝ)) := by
           rw [show (689:ℝ)=(13:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h13.1,h13.2]

theorem scale_695 : (32719557819/2500000000:ℝ)≤Real.log ((695:ℝ)^2) ∧ Real.log ((695:ℝ)^2)≤(65439120367/5000000000:ℝ) := by
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((695:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((695:ℝ)^2)=2*Real.log (695:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (139:ℝ)) := by
           rw [show (695:ℝ)=(5:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h139.1,h139.2,h5.1,h5.2]

theorem scale_697 : (65467852353/5000000000:ℝ)≤Real.log ((697:ℝ)^2) ∧ Real.log ((697:ℝ)^2)≤(65467855291/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have he : Real.log ((697:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (41:ℝ)) := by
    calc Real.log ((697:ℝ)^2)=2*Real.log (697:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (41:ℝ)) := by
           rw [show (697:ℝ)=(17:ℝ)*(41:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h41.1,h41.2]

theorem scale_703 : (65553567683/5000000000:ℝ)≤Real.log ((703:ℝ)^2) ∧ Real.log ((703:ℝ)^2)≤(32776784877/2500000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((703:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (37:ℝ)) := by
    calc Real.log ((703:ℝ)^2)=2*Real.log (703:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (37:ℝ)) := by
           rw [show (703:ℝ)=(19:ℝ)*(37:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h37.1,h37.2]

theorem scale_707 : (32805151939/2500000000:ℝ)≤Real.log ((707:ℝ)^2) ∧ Real.log ((707:ℝ)^2)≤(13122061707/1000000000:ℝ) := by
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((707:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((707:ℝ)^2)=2*Real.log (707:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (101:ℝ)) := by
           rw [show (707:ℝ)=(7:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h101.1,h101.2,h7.1,h7.2]

theorem scale_713 : (32847407087/2500000000:ℝ)≤Real.log ((713:ℝ)^2) ∧ Real.log ((713:ℝ)^2)≤(32847407117/2500000000:ℝ) := by
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((713:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (31:ℝ)) := by
    calc Real.log ((713:ℝ)^2)=2*Real.log (713:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (31:ℝ)) := by
           rw [show (713:ℝ)=(23:ℝ)*(31:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h31.1,h31.2,h23.1,h23.2]

theorem scale_721 : (65806388589/5000000000:ℝ)≤Real.log ((721:ℝ)^2) ∧ Real.log ((721:ℝ)^2)≤(16451598313/1250000000:ℝ) := by
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((721:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((721:ℝ)^2)=2*Real.log (721:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (103:ℝ)) := by
           rw [show (721:ℝ)=(7:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h103.1,h103.2,h7.1,h7.2]

theorem scale_731 : (8243016583/625000000:ℝ)≤Real.log ((731:ℝ)^2) ∧ Real.log ((731:ℝ)^2)≤(659441359/50000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have he : Real.log ((731:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (43:ℝ)) := by
    calc Real.log ((731:ℝ)^2)=2*Real.log (731:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (43:ℝ)) := by
           rw [show (731:ℝ)=(17:ℝ)*(43:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h43.1,h43.2]

theorem scale_737 : (66025876273/5000000000:ℝ)≤Real.log ((737:ℝ)^2) ∧ Real.log ((737:ℝ)^2)≤(66025880703/5000000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((737:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((737:ℝ)^2)=2*Real.log (737:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (67:ℝ)) := by
           rw [show (737:ℝ)=(11:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h11.1,h11.2]

theorem scale_745 : (66133839359/5000000000:ℝ)≤Real.log ((745:ℝ)^2) ∧ Real.log ((745:ℝ)^2)≤(66133844099/5000000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((745:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((745:ℝ)^2)=2*Real.log (745:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (149:ℝ)) := by
           rw [show (745:ℝ)=(5:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h149.1,h149.2]

theorem scale_749 : (33093693523/2500000000:ℝ)≤Real.log ((749:ℝ)^2) ∧ Real.log ((749:ℝ)^2)≤(66187391719/5000000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((749:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((749:ℝ)^2)=2*Real.log (749:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (107:ℝ)) := by
           rw [show (749:ℝ)=(7:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h7.1,h7.2]

theorem scale_755 : (66267174667/5000000000:ℝ)≤Real.log ((755:ℝ)^2) ∧ Real.log ((755:ℝ)^2)≤(66267179409/5000000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((755:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((755:ℝ)^2)=2*Real.log (755:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (151:ℝ)) := by
           rw [show (755:ℝ)=(5:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h151.1,h151.2]

theorem scale_763 : (66372577521/5000000000:ℝ)≤Real.log ((763:ℝ)^2) ∧ Real.log ((763:ℝ)^2)≤(66372582199/5000000000:ℝ) := by
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((763:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((763:ℝ)^2)=2*Real.log (763:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (109:ℝ)) := by
           rw [show (763:ℝ)=(7:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h109.1,h109.2,h7.1,h7.2]

theorem scale_767 : (66424865463/5000000000:ℝ)≤Real.log ((767:ℝ)^2) ∧ Real.log ((767:ℝ)^2)≤(66424869727/5000000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((767:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((767:ℝ)^2)=2*Real.log (767:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (59:ℝ)) := by
           rw [show (767:ℝ)=(13:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h13.1,h13.2]

theorem scale_779 : (66580108703/5000000000:ℝ)≤Real.log ((779:ℝ)^2) ∧ Real.log ((779:ℝ)^2)≤(66580111643/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((779:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (41:ℝ)) := by
    calc Real.log ((779:ℝ)^2)=2*Real.log (779:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (41:ℝ)) := by
           rw [show (779:ℝ)=(19:ℝ)*(41:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h19.1,h19.2]

theorem scale_781 : (33302874409/2500000000:ℝ)≤Real.log ((781:ℝ)^2) ∧ Real.log ((781:ℝ)^2)≤(33302876651/2500000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((781:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((781:ℝ)^2)=2*Real.log (781:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (71:ℝ)) := by
           rw [show (781:ℝ)=(11:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h71.1,h71.2]

theorem scale_785 : (66656834349/5000000000:ℝ)≤Real.log ((785:ℝ)^2) ∧ Real.log ((785:ℝ)^2)≤(66656839099/5000000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((785:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((785:ℝ)^2)=2*Real.log (785:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (157:ℝ)) := by
           rw [show (785:ℝ)=(5:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h157.1,h157.2]

theorem scale_791 : (66732976881/5000000000:ℝ)≤Real.log ((791:ℝ)^2) ∧ Real.log ((791:ℝ)^2)≤(1042702837/78125000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((791:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((791:ℝ)^2)=2*Real.log (791:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (113:ℝ)) := by
           rw [show (791:ℝ)=(7:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h7.1,h7.2]

theorem scale_793 : (13351645927/1000000000:ℝ)≤Real.log ((793:ℝ)^2) ∧ Real.log ((793:ℝ)^2)≤(66758233951/5000000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((793:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((793:ℝ)^2)=2*Real.log (793:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (61:ℝ)) := by
           rw [show (793:ℝ)=(13:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h13.1,h13.2]

theorem scale_799 : (16708401817/1250000000:ℝ)≤Real.log ((799:ℝ)^2) ∧ Real.log ((799:ℝ)^2)≤(6683361093/500000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((799:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((799:ℝ)^2)=2*Real.log (799:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (47:ℝ)) := by
           rw [show (799:ℝ)=(17:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h47.1,h47.2]

theorem scale_803 : (33441772223/2500000000:ℝ)≤Real.log ((803:ℝ)^2) ∧ Real.log ((803:ℝ)^2)≤(8360443619/625000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((803:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((803:ℝ)^2)=2*Real.log (803:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (73:ℝ)) := by
           rw [show (803:ℝ)=(11:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h11.1,h11.2]

theorem scale_815 : (670318783/50000000:ℝ)≤Real.log ((815:ℝ)^2) ∧ Real.log ((815:ℝ)^2)≤(67031883057/5000000000:ℝ) := by
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((815:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((815:ℝ)^2)=2*Real.log (815:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (163:ℝ)) := by
           rw [show (815:ℝ)=(5:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h163.1,h163.2,h5.1,h5.2]

theorem scale_817 : (33528194507/2500000000:ℝ)≤Real.log ((817:ℝ)^2) ∧ Real.log ((817:ℝ)^2)≤(16764098063/1250000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((817:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (43:ℝ)) := by
    calc Real.log ((817:ℝ)^2)=2*Real.log (817:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (43:ℝ)) := by
           rw [show (817:ℝ)=(19:ℝ)*(43:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h19.1,h19.2]

theorem scale_835 : (33637157207/2500000000:ℝ)≤Real.log ((835:ℝ)^2) ∧ Real.log ((835:ℝ)^2)≤(2690972767/200000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have he : Real.log ((835:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((835:ℝ)^2)=2*Real.log (835:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (167:ℝ)) := by
           rw [show (835:ℝ)=(5:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h167.1,h167.2]

theorem scale_851 : (4216507503/312500000:ℝ)≤Real.log ((851:ℝ)^2) ∧ Real.log ((851:ℝ)^2)≤(67464122123/5000000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((851:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (37:ℝ)) := by
    calc Real.log ((851:ℝ)^2)=2*Real.log (851:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (37:ℝ)) := by
           rw [show (851:ℝ)=(23:ℝ)*(37:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h23.1,h23.2]

theorem scale_865 : (8453411529/625000000:ℝ)≤Real.log ((865:ℝ)^2) ∧ Real.log ((865:ℝ)^2)≤(67627296999/5000000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have he : Real.log ((865:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((865:ℝ)^2)=2*Real.log (865:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (173:ℝ)) := by
           rw [show (865:ℝ)=(5:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h173.1,h173.2]

theorem scale_869 : (67673428529/5000000000:ℝ)≤Real.log ((869:ℝ)^2) ∧ Real.log ((869:ℝ)^2)≤(67673433087/5000000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((869:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((869:ℝ)^2)=2*Real.log (869:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (79:ℝ)) := by
           rw [show (869:ℝ)=(11:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h79.1,h79.2]

#print axioms scale_543
#print axioms scale_545
#print axioms scale_551
#print axioms scale_553
#print axioms scale_559
#print axioms scale_565
#print axioms scale_573
#print axioms scale_579
#print axioms scale_581
#print axioms scale_583
#print axioms scale_589
#print axioms scale_591
#print axioms scale_597
#print axioms scale_611
#print axioms scale_623
#print axioms scale_629
#print axioms scale_635
#print axioms scale_649
#print axioms scale_655
#print axioms scale_667
#print axioms scale_671
#print axioms scale_679
#print axioms scale_685
#print axioms scale_689
#print axioms scale_695
#print axioms scale_697
#print axioms scale_703
#print axioms scale_707
#print axioms scale_713
#print axioms scale_721
#print axioms scale_731
#print axioms scale_737
#print axioms scale_745
#print axioms scale_749
#print axioms scale_755
#print axioms scale_763
#print axioms scale_767
#print axioms scale_779
#print axioms scale_781
#print axioms scale_785
#print axioms scale_791
#print axioms scale_793
#print axioms scale_799
#print axioms scale_803
#print axioms scale_815
#print axioms scale_817
#print axioms scale_835
#print axioms scale_851
#print axioms scale_865
#print axioms scale_869
end
end JSP233.ScaleLogs132
