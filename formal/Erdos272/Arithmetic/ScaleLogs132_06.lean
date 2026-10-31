import Erdos272.Arithmetic.PrefixTable132
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_1261 : (35698300291/2500000000:ℝ)≤Real.log ((1261:ℝ)^2) ∧ Real.log ((1261:ℝ)^2)≤(71396605233/5000000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((1261:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((1261:ℝ)^2)=2*Real.log (1261:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (97:ℝ)) := by
           rw [show (1261:ℝ)=(13:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h13.1,h13.2]

theorem scale_1267 : (35722034481/2500000000:ℝ)≤Real.log ((1267:ℝ)^2) ∧ Real.log ((1267:ℝ)^2)≤(71444073739/5000000000:ℝ) := by
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((1267:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((1267:ℝ)^2)=2*Real.log (1267:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (181:ℝ)) := by
           rw [show (1267:ℝ)=(7:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h181.1,h181.2,h7.1,h7.2]

theorem scale_1271 : (1429511819/100000000:ℝ)≤Real.log ((1271:ℝ)^2) ∧ Real.log ((1271:ℝ)^2)≤(35737796951/2500000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((1271:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (41:ℝ)) := by
    calc Real.log ((1271:ℝ)^2)=2*Real.log (1271:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (41:ℝ)) := by
           rw [show (1271:ℝ)=(31:ℝ)*(41:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h31.1,h31.2]

theorem scale_1273 : (17872828333/1250000000:ℝ)≤Real.log ((1273:ℝ)^2) ∧ Real.log ((1273:ℝ)^2)≤(7149131777/500000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((1273:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((1273:ℝ)^2)=2*Real.log (1273:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (67:ℝ)) := by
           rw [show (1273:ℝ)=(19:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h19.1,h19.2]

theorem scale_1313 : (71800695959/5000000000:ℝ)≤Real.log ((1313:ℝ)^2) ∧ Real.log ((1313:ℝ)^2)≤(35900350311/2500000000:ℝ) := by
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((1313:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((1313:ℝ)^2)=2*Real.log (1313:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (101:ℝ)) := by
           rw [show (1313:ℝ)=(13:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h101.1,h101.2,h13.1,h13.2]

theorem scale_1333 : (71951871261/5000000000:ℝ)≤Real.log ((1333:ℝ)^2) ∧ Real.log ((1333:ℝ)^2)≤(71951874511/5000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((1333:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (43:ℝ)) := by
    calc Real.log ((1333:ℝ)^2)=2*Real.log (1333:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (43:ℝ)) := by
           rw [show (1333:ℝ)=(31:ℝ)*(43:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h31.1,h31.2]

theorem scale_1337 : (17995458231/1250000000:ℝ)≤Real.log ((1337:ℝ)^2) ∧ Real.log ((1337:ℝ)^2)≤(4498864857/312500000:ℝ) := by
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((1337:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((1337:ℝ)^2)=2*Real.log (1337:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (191:ℝ)) := by
           rw [show (1337:ℝ)=(7:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h191.1,h191.2,h7.1,h7.2]

theorem scale_1339 : (7199678067/500000000:ℝ)≤Real.log ((1339:ℝ)^2) ∧ Real.log ((1339:ℝ)^2)≤(71996785339/5000000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((1339:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((1339:ℝ)^2)=2*Real.log (1339:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (103:ℝ)) := by
           rw [show (1339:ℝ)=(13:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h103.1,h103.2]

theorem scale_1343 : (36013304619/2500000000:ℝ)≤Real.log ((1343:ℝ)^2) ∧ Real.log ((1343:ℝ)^2)≤(36013306901/2500000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((1343:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((1343:ℝ)^2)=2*Real.log (1343:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (79:ℝ)) := by
           rw [show (1343:ℝ)=(17:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h79.1,h79.2]

theorem scale_1349 : (72071185877/5000000000:ℝ)≤Real.log ((1349:ℝ)^2) ∧ Real.log ((1349:ℝ)^2)≤(72071190369/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((1349:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((1349:ℝ)^2)=2*Real.log (1349:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (71:ℝ)) := by
           rw [show (1349:ℝ)=(19:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h71.1,h71.2]

theorem scale_1351 : (72086000531/5000000000:ℝ)≤Real.log ((1351:ℝ)^2) ∧ Real.log ((1351:ℝ)^2)≤(72086005321/5000000000:ℝ) := by
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((1351:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((1351:ℝ)^2)=2*Real.log (1351:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (193:ℝ)) := by
           rw [show (1351:ℝ)=(7:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h193.1,h193.2,h7.1,h7.2]

theorem scale_1357 : (36065157021/2500000000:ℝ)≤Real.log ((1357:ℝ)^2) ∧ Real.log ((1357:ℝ)^2)≤(18032579579/1250000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((1357:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((1357:ℝ)^2)=2*Real.log (1357:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (59:ℝ)) := by
           rw [show (1357:ℝ)=(23:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h23.1,h23.2]

theorem scale_1363 : (72174432121/5000000000:ℝ)≤Real.log ((1363:ℝ)^2) ∧ Real.log ((1363:ℝ)^2)≤(14434887159/1000000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((1363:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((1363:ℝ)^2)=2*Real.log (1363:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (47:ℝ)) := by
           rw [show (1363:ℝ)=(29:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h29.1,h29.2,h47.1,h47.2]

theorem scale_1379 : (72291135927/5000000000:ℝ)≤Real.log ((1379:ℝ)^2) ∧ Real.log ((1379:ℝ)^2)≤(36145570361/2500000000:ℝ) := by
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((1379:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((1379:ℝ)^2)=2*Real.log (1379:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (197:ℝ)) := by
           rw [show (1379:ℝ)=(7:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h197.1,h197.2,h7.1,h7.2]

theorem scale_1387 : (14469796301/1000000000:ℝ)≤Real.log ((1387:ℝ)^2) ∧ Real.log ((1387:ℝ)^2)≤(72348986019/5000000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((1387:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((1387:ℝ)^2)=2*Real.log (1387:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (73:ℝ)) := by
           rw [show (1387:ℝ)=(19:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h19.1,h19.2]

theorem scale_1391 : (72377779127/5000000000:ℝ)≤Real.log ((1391:ℝ)^2) ∧ Real.log ((1391:ℝ)^2)≤(36188891903/2500000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((1391:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((1391:ℝ)^2)=2*Real.log (1391:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (107:ℝ)) := by
           rw [show (1391:ℝ)=(13:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h13.1,h13.2]

theorem scale_1393 : (36196073443/2500000000:ℝ)≤Real.log ((1393:ℝ)^2) ∧ Real.log ((1393:ℝ)^2)≤(72392151683/5000000000:ℝ) := by
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((1393:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((1393:ℝ)^2)=2*Real.log (1393:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (199:ℝ)) := by
           rw [show (1393:ℝ)=(7:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h199.1,h199.2,h7.1,h7.2]

theorem scale_1397 : (3621041039/250000000:ℝ)≤Real.log ((1397:ℝ)^2) ∧ Real.log ((1397:ℝ)^2)≤(36210412749/2500000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((1397:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((1397:ℝ)^2)=2*Real.log (1397:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (127:ℝ)) := by
           rw [show (1397:ℝ)=(11:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h127.1,h127.2]

theorem scale_1403 : (36231839107/2500000000:ℝ)≤Real.log ((1403:ℝ)^2) ∧ Real.log ((1403:ℝ)^2)≤(3623184127/250000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((1403:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((1403:ℝ)^2)=2*Real.log (1403:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (61:ℝ)) := by
           rw [show (1403:ℝ)=(23:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h23.1,h23.2]

theorem scale_1411 : (9065067097/625000000:ℝ)≤Real.log ((1411:ℝ)^2) ∧ Real.log ((1411:ℝ)^2)≤(72520541367/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have he : Real.log ((1411:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((1411:ℝ)^2)=2*Real.log (1411:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (83:ℝ)) := by
           rw [show (1411:ℝ)=(17:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h83.1,h83.2]

theorem scale_1417 : (36281484801/2500000000:ℝ)≤Real.log ((1417:ℝ)^2) ∧ Real.log ((1417:ℝ)^2)≤(36281487143/2500000000:ℝ) := by
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((1417:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((1417:ℝ)^2)=2*Real.log (1417:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (109:ℝ)) := by
           rw [show (1417:ℝ)=(13:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h109.1,h109.2,h13.1,h13.2]

theorem scale_1441 : (14546184629/1000000000:ℝ)≤Real.log ((1441:ℝ)^2) ∧ Real.log ((1441:ℝ)^2)≤(18182731967/1250000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have he : Real.log ((1441:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((1441:ℝ)^2)=2*Real.log (1441:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (131:ℝ)) := by
           rw [show (1441:ℝ)=(11:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h131.1,h131.2]

theorem scale_1457 : (14568269173/1000000000:ℝ)≤Real.log ((1457:ℝ)^2) ∧ Real.log ((1457:ℝ)^2)≤(72841349541/5000000000:ℝ) := by
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((1457:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((1457:ℝ)^2)=2*Real.log (1457:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (47:ℝ)) := by
           rw [show (1457:ℝ)=(31:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h47.1,h47.2,h31.1,h31.2]

theorem scale_1469 : (36461684481/2500000000:ℝ)≤Real.log ((1469:ℝ)^2) ∧ Real.log ((1469:ℝ)^2)≤(14584674731/1000000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((1469:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((1469:ℝ)^2)=2*Real.log (1469:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (113:ℝ)) := by
           rw [show (1469:ℝ)=(13:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h13.1,h13.2]

theorem scale_1501 : (18284716397/1250000000:ℝ)≤Real.log ((1501:ℝ)^2) ∧ Real.log ((1501:ℝ)^2)≤(36569435077/2500000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((1501:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((1501:ℝ)^2)=2*Real.log (1501:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (79:ℝ)) := by
           rw [show (1501:ℝ)=(19:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h79.1,h79.2]

theorem scale_1507 : (73178759167/5000000000:ℝ)≤Real.log ((1507:ℝ)^2) ∧ Real.log ((1507:ℝ)^2)≤(731787639/50000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((1507:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((1507:ℝ)^2)=2*Real.log (1507:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (137:ℝ)) := by
           rw [show (1507:ℝ)=(11:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h11.1,h11.2]

theorem scale_1513 : (73218494377/5000000000:ℝ)≤Real.log ((1513:ℝ)^2) ∧ Real.log ((1513:ℝ)^2)≤(73218498999/5000000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have he : Real.log ((1513:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((1513:ℝ)^2)=2*Real.log (1513:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (89:ℝ)) := by
           rw [show (1513:ℝ)=(17:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h17.1,h17.2]

theorem scale_1517 : (9155612103/625000000:ℝ)≤Real.log ((1517:ℝ)^2) ∧ Real.log ((1517:ℝ)^2)≤(73244901791/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((1517:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (41:ℝ)) := by
    calc Real.log ((1517:ℝ)^2)=2*Real.log (1517:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (41:ℝ)) := by
           rw [show (1517:ℝ)=(37:ℝ)*(41:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h37.1,h37.2]

theorem scale_1529 : (73323689239/5000000000:ℝ)≤Real.log ((1529:ℝ)^2) ∧ Real.log ((1529:ℝ)^2)≤(36661846987/2500000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have he : Real.log ((1529:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((1529:ℝ)^2)=2*Real.log (1529:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (139:ℝ)) := by
           rw [show (1529:ℝ)=(11:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h139.1,h139.2]

theorem scale_1537 : (73375875009/5000000000:ℝ)≤Real.log ((1537:ℝ)^2) ∧ Real.log ((1537:ℝ)^2)≤(73375879069/5000000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((1537:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((1537:ℝ)^2)=2*Real.log (1537:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (53:ℝ)) := by
           rw [show (1537:ℝ)=(29:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h29.1,h29.2]

theorem scale_1541 : (73401865697/5000000000:ℝ)≤Real.log ((1541:ℝ)^2) ∧ Real.log ((1541:ℝ)^2)≤(73401870139/5000000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((1541:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((1541:ℝ)^2)=2*Real.log (1541:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (67:ℝ)) := by
           rw [show (1541:ℝ)=(23:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h23.1,h23.2]

theorem scale_1577 : (36816396563/2500000000:ℝ)≤Real.log ((1577:ℝ)^2) ∧ Real.log ((1577:ℝ)^2)≤(73632797719/5000000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((1577:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((1577:ℝ)^2)=2*Real.log (1577:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (83:ℝ)) := by
           rw [show (1577:ℝ)=(19:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h19.1,h19.2]

theorem scale_1591 : (14744235427/1000000000:ℝ)≤Real.log ((1591:ℝ)^2) ∧ Real.log ((1591:ℝ)^2)≤(46075739/3125000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((1591:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (43:ℝ)) := by
    calc Real.log ((1591:ℝ)^2)=2*Real.log (1591:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (43:ℝ)) := by
           rw [show (1591:ℝ)=(37:ℝ)*(43:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h37.1,h37.2]

theorem scale_1633 : (36990869121/2500000000:ℝ)≤Real.log ((1633:ℝ)^2) ∧ Real.log ((1633:ℝ)^2)≤(36990871369/2500000000:ℝ) := by
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((1633:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((1633:ℝ)^2)=2*Real.log (1633:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (71:ℝ)) := by
           rw [show (1633:ℝ)=(23:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h71.1,h71.2,h23.1,h23.2]

theorem scale_1639 : (462615081/31250000:ℝ)≤Real.log ((1639:ℝ)^2) ∧ Real.log ((1639:ℝ)^2)≤(37009208853/2500000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((1639:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((1639:ℝ)^2)=2*Real.log (1639:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (149:ℝ)) := by
           rw [show (1639:ℝ)=(11:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h149.1,h149.2]

theorem scale_1643 : (74042788753/5000000000:ℝ)≤Real.log ((1643:ℝ)^2) ∧ Real.log ((1643:ℝ)^2)≤(14808558563/1000000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((1643:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((1643:ℝ)^2)=2*Real.log (1643:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (53:ℝ)) := by
           rw [show (1643:ℝ)=(31:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h31.1,h31.2]

theorem scale_1649 : (37039620223/2500000000:ℝ)≤Real.log ((1649:ℝ)^2) ∧ Real.log ((1649:ℝ)^2)≤(74079245101/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have he : Real.log ((1649:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((1649:ℝ)^2)=2*Real.log (1649:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (97:ℝ)) := by
           rw [show (1649:ℝ)=(17:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h97.1,h97.2]

theorem scale_1651 : (592730893/40000000:ℝ)≤Real.log ((1651:ℝ)^2) ∧ Real.log ((1651:ℝ)^2)≤(14818273269/1000000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((1651:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((1651:ℝ)^2)=2*Real.log (1651:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (127:ℝ)) := by
           rw [show (1651:ℝ)=(13:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h127.1,h127.2]

theorem scale_1661 : (18537937067/1250000000:ℝ)≤Real.log ((1661:ℝ)^2) ∧ Real.log ((1661:ℝ)^2)≤(9268969127/625000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((1661:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((1661:ℝ)^2)=2*Real.log (1661:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (151:ℝ)) := by
           rw [show (1661:ℝ)=(11:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h151.1,h151.2]

theorem scale_1679 : (7425953387/500000000:ℝ)≤Real.log ((1679:ℝ)^2) ∧ Real.log ((1679:ℝ)^2)≤(18564884597/1250000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((1679:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((1679:ℝ)^2)=2*Real.log (1679:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (73:ℝ)) := by
           rw [show (1679:ℝ)=(23:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h23.1,h23.2]

theorem scale_1691 : (74330750727/5000000000:ℝ)≤Real.log ((1691:ℝ)^2) ∧ Real.log ((1691:ℝ)^2)≤(74330755351/5000000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((1691:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((1691:ℝ)^2)=2*Real.log (1691:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (89:ℝ)) := by
           rw [show (1691:ℝ)=(19:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h19.1,h19.2]

theorem scale_1703 : (7440146399/500000000:ℝ)≤Real.log ((1703:ℝ)^2) ∧ Real.log ((1703:ℝ)^2)≤(14880293743/1000000000:ℝ) := by
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((1703:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((1703:ℝ)^2)=2*Real.log (1703:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (131:ℝ)) := by
           rw [show (1703:ℝ)=(13:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h131.1,h131.2,h13.1,h13.2]

theorem scale_1711 : (3722416509/250000000:ℝ)≤Real.log ((1711:ℝ)^2) ∧ Real.log ((1711:ℝ)^2)≤(3722416723/250000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((1711:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((1711:ℝ)^2)=2*Real.log (1711:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (59:ℝ)) := by
           rw [show (1711:ℝ)=(29:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h29.1,h29.2]

theorem scale_1717 : (74483335823/5000000000:ℝ)≤Real.log ((1717:ℝ)^2) ∧ Real.log ((1717:ℝ)^2)≤(7448334049/500000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((1717:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((1717:ℝ)^2)=2*Real.log (1717:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (101:ℝ)) := by
           rw [show (1717:ℝ)=(17:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h101.1,h101.2]

theorem scale_1727 : (1490828159/100000000:ℝ)≤Real.log ((1727:ℝ)^2) ∧ Real.log ((1727:ℝ)^2)≤(37270706353/2500000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((1727:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((1727:ℝ)^2)=2*Real.log (1727:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (157:ℝ)) := by
           rw [show (1727:ℝ)=(11:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h157.1,h157.2]

theorem scale_1739 : (74610651739/5000000000:ℝ)≤Real.log ((1739:ℝ)^2) ∧ Real.log ((1739:ℝ)^2)≤(7461065743/500000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((1739:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((1739:ℝ)^2)=2*Real.log (1739:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (47:ℝ)) := by
           rw [show (1739:ℝ)=(37:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h47.1,h47.2]

theorem scale_1751 : (37339710267/2500000000:ℝ)≤Real.log ((1751:ℝ)^2) ∧ Real.log ((1751:ℝ)^2)≤(74679425207/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((1751:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((1751:ℝ)^2)=2*Real.log (1751:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (103:ℝ)) := by
           rw [show (1751:ℝ)=(17:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h103.1,h103.2]

theorem scale_1763 : (14949543631/1000000000:ℝ)≤Real.log ((1763:ℝ)^2) ∧ Real.log ((1763:ℝ)^2)≤(74747724289/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have he : Real.log ((1763:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (43:ℝ)) := by
    calc Real.log ((1763:ℝ)^2)=2*Real.log (1763:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (43:ℝ)) := by
           rw [show (1763:ℝ)=(41:ℝ)*(43:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h43.1,h43.2]

theorem scale_1769 : (4673855897/312500000:ℝ)≤Real.log ((1769:ℝ)^2) ∧ Real.log ((1769:ℝ)^2)≤(18695424671/1250000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((1769:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((1769:ℝ)^2)=2*Real.log (1769:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (61:ℝ)) := by
           rw [show (1769:ℝ)=(29:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h29.1,h29.2]

theorem scale_1781 : (18712325003/1250000000:ℝ)≤Real.log ((1781:ℝ)^2) ∧ Real.log ((1781:ℝ)^2)≤(74849304747/5000000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((1781:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((1781:ℝ)^2)=2*Real.log (1781:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (137:ℝ)) := by
           rw [show (1781:ℝ)=(13:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h13.1,h13.2]

#print axioms scale_1261
#print axioms scale_1267
#print axioms scale_1271
#print axioms scale_1273
#print axioms scale_1313
#print axioms scale_1333
#print axioms scale_1337
#print axioms scale_1339
#print axioms scale_1343
#print axioms scale_1349
#print axioms scale_1351
#print axioms scale_1357
#print axioms scale_1363
#print axioms scale_1379
#print axioms scale_1387
#print axioms scale_1391
#print axioms scale_1393
#print axioms scale_1397
#print axioms scale_1403
#print axioms scale_1411
#print axioms scale_1417
#print axioms scale_1441
#print axioms scale_1457
#print axioms scale_1469
#print axioms scale_1501
#print axioms scale_1507
#print axioms scale_1513
#print axioms scale_1517
#print axioms scale_1529
#print axioms scale_1537
#print axioms scale_1541
#print axioms scale_1577
#print axioms scale_1591
#print axioms scale_1633
#print axioms scale_1639
#print axioms scale_1643
#print axioms scale_1649
#print axioms scale_1651
#print axioms scale_1661
#print axioms scale_1679
#print axioms scale_1691
#print axioms scale_1703
#print axioms scale_1711
#print axioms scale_1717
#print axioms scale_1727
#print axioms scale_1739
#print axioms scale_1751
#print axioms scale_1763
#print axioms scale_1769
#print axioms scale_1781
end
end JSP233.ScaleLogs132
