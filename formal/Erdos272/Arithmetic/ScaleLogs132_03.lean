import Erdos272.Arithmetic.PrefixTable132
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_329 : (57960575323/5000000000:ℝ)≤Real.log ((329:ℝ)^2) ∧ Real.log ((329:ℝ)^2)≤(2318423159/200000000:ℝ) := by
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((329:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((329:ℝ)^2)=2*Real.log (329:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (47:ℝ)) := by
           rw [show (329:ℝ)=(7:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h47.1,h47.2,h7.1,h7.2]

theorem scale_334 : (7263925887/625000000:ℝ)≤Real.log ((334:ℝ)^2) ∧ Real.log ((334:ℝ)^2)≤(29055705927/2500000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have he : Real.log ((334:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((334:ℝ)^2)=2*Real.log (334:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (167:ℝ)) := by
           rw [show (334:ℝ)=(2:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h167.1,h167.2]

theorem scale_335 : (3633831417/312500000:ℝ)≤Real.log ((335:ℝ)^2) ∧ Real.log ((335:ℝ)^2)≤(7267663387/625000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((335:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((335:ℝ)^2)=2*Real.log (335:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (67:ℝ)) := by
           rw [show (335:ℝ)=(5:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h5.1,h5.2]

theorem scale_339 : (58259998279/5000000000:ℝ)≤Real.log ((339:ℝ)^2) ∧ Real.log ((339:ℝ)^2)≤(29130001481/2500000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((339:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((339:ℝ)^2)=2*Real.log (339:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (113:ℝ)) := by
           rw [show (339:ℝ)=(3:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h3.1,h3.2]

theorem scale_341 : (233275299/20000000:ℝ)≤Real.log ((341:ℝ)^2) ∧ Real.log ((341:ℝ)^2)≤(29159412399/2500000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((341:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (31:ℝ)) := by
    calc Real.log ((341:ℝ)^2)=2*Real.log (341:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (31:ℝ)) := by
           rw [show (341:ℝ)=(11:ℝ)*(31:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h31.1,h31.2]

theorem scale_346 : (29232192457/2500000000:ℝ)≤Real.log ((346:ℝ)^2) ∧ Real.log ((346:ℝ)^2)≤(29232194839/2500000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have he : Real.log ((346:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((346:ℝ)^2)=2*Real.log (346:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (173:ℝ)) := by
           rw [show (346:ℝ)=(2:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h173.1,h173.2]

theorem scale_355 : (58721175217/5000000000:ℝ)≤Real.log ((355:ℝ)^2) ∧ Real.log ((355:ℝ)^2)≤(11744235939/1000000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((355:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((355:ℝ)^2)=2*Real.log (355:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (71:ℝ)) := by
           rw [show (355:ℝ)=(5:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h71.1,h71.2]

theorem scale_358 : (29402663513/2500000000:ℝ)≤Real.log ((358:ℝ)^2) ∧ Real.log ((358:ℝ)^2)≤(14701332949/1250000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have he : Real.log ((358:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((358:ℝ)^2)=2*Real.log (358:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (179:ℝ)) := by
           rw [show (358:ℝ)=(2:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h179.1,h179.2]

theorem scale_362 : (58916439279/5000000000:ℝ)≤Real.log ((362:ℝ)^2) ∧ Real.log ((362:ℝ)^2)≤(58916444051/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have he : Real.log ((362:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((362:ℝ)^2)=2*Real.log (362:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (181:ℝ)) := by
           rw [show (362:ℝ)=(2:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h181.1,h181.2]

theorem scale_365 : (11799794169/1000000000:ℝ)≤Real.log ((365:ℝ)^2) ∧ Real.log ((365:ℝ)^2)≤(11799795069/1000000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((365:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((365:ℝ)^2)=2*Real.log (365:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (73:ℝ)) := by
           rw [show (365:ℝ)=(5:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h5.1,h5.2]

theorem scale_371 : (59162018211/5000000000:ℝ)≤Real.log ((371:ℝ)^2) ∧ Real.log ((371:ℝ)^2)≤(59162022249/5000000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((371:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((371:ℝ)^2)=2*Real.log (371:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (53:ℝ)) := by
           rw [show (371:ℝ)=(7:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h7.1,h7.2]

theorem scale_377 : (59322451851/5000000000:ℝ)≤Real.log ((377:ℝ)^2) ∧ Real.log ((377:ℝ)^2)≤(59322451899/5000000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((377:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (29:ℝ)) := by
    calc Real.log ((377:ℝ)^2)=2*Real.log (377:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (29:ℝ)) := by
           rw [show (377:ℝ)=(13:ℝ)*(29:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h29.1,h29.2,h13.1,h13.2]

theorem scale_381 : (29713995471/2500000000:ℝ)≤Real.log ((381:ℝ)^2) ∧ Real.log ((381:ℝ)^2)≤(14856998913/1250000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((381:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((381:ℝ)^2)=2*Real.log (381:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (127:ℝ)) := by
           rw [show (381:ℝ)=(3:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h127.1,h127.2]

theorem scale_382 : (59454203241/5000000000:ℝ)≤Real.log ((382:ℝ)^2) ∧ Real.log ((382:ℝ)^2)≤(7431776003/625000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have he : Real.log ((382:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((382:ℝ)^2)=2*Real.log (382:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (191:ℝ)) := by
           rw [show (382:ℝ)=(2:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h191.1,h191.2]

theorem scale_386 : (1861199089/156250000:ℝ)≤Real.log ((386:ℝ)^2) ∧ Real.log ((386:ℝ)^2)≤(59558375633/5000000000:ℝ) := by
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have he : Real.log ((386:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((386:ℝ)^2)=2*Real.log (386:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (193:ℝ)) := by
           rw [show (386:ℝ)=(2:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h193.1,h193.2,h2.1,h2.2]

theorem scale_391 : (59687075577/5000000000:ℝ)≤Real.log ((391:ℝ)^2) ∧ Real.log ((391:ℝ)^2)≤(59687075623/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((391:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (23:ℝ)) := by
    calc Real.log ((391:ℝ)^2)=2*Real.log (391:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (23:ℝ)) := by
           rw [show (391:ℝ)=(17:ℝ)*(23:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h23.1,h23.2]

theorem scale_393 : (59738093307/5000000000:ℝ)≤Real.log ((393:ℝ)^2) ∧ Real.log ((393:ℝ)^2)≤(29869049011/2500000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have he : Real.log ((393:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((393:ℝ)^2)=2*Real.log (393:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (131:ℝ)) := by
           rw [show (393:ℝ)=(3:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h131.1,h131.2]

theorem scale_394 : (14940876561/1250000000:ℝ)≤Real.log ((394:ℝ)^2) ∧ Real.log ((394:ℝ)^2)≤(29881755517/2500000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have he : Real.log ((394:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((394:ℝ)^2)=2*Real.log (394:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (197:ℝ)) := by
           rw [show (394:ℝ)=(2:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h197.1,h197.2]

theorem scale_395 : (3736803433/312500000:ℝ)≤Real.log ((395:ℝ)^2) ∧ Real.log ((395:ℝ)^2)≤(1494721487/125000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((395:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((395:ℝ)^2)=2*Real.log (395:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (79:ℝ)) := by
           rw [show (395:ℝ)=(5:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h79.1,h79.2]

theorem scale_398 : (59864517203/5000000000:ℝ)≤Real.log ((398:ℝ)^2) ∧ Real.log ((398:ℝ)^2)≤(11972904399/1000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have he : Real.log ((398:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((398:ℝ)^2)=2*Real.log (398:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (199:ℝ)) := by
           rw [show (398:ℝ)=(2:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h199.1,h199.2]

theorem scale_403 : (11997873119/1000000000:ℝ)≤Real.log ((403:ℝ)^2) ∧ Real.log ((403:ℝ)^2)≤(11997873129/1000000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((403:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (31:ℝ)) := by
    calc Real.log ((403:ℝ)^2)=2*Real.log (403:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (31:ℝ)) := by
           rw [show (403:ℝ)=(13:ℝ)*(31:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h31.1,h31.2]

theorem scale_407 : (938877041/78125000:ℝ)≤Real.log ((407:ℝ)^2) ∧ Real.log ((407:ℝ)^2)≤(60088132687/5000000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((407:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (37:ℝ)) := by
    calc Real.log ((407:ℝ)^2)=2*Real.log (407:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (37:ℝ)) := by
           rw [show (407:ℝ)=(11:ℝ)*(37:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h37.1,h37.2]

theorem scale_411 : (60185929329/5000000000:ℝ)≤Real.log ((411:ℝ)^2) ∧ Real.log ((411:ℝ)^2)≤(30092967027/2500000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((411:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((411:ℝ)^2)=2*Real.log (411:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (137:ℝ)) := by
           rw [show (411:ℝ)=(3:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h3.1,h3.2]

theorem scale_413 : (30117236691/2500000000:ℝ)≤Real.log ((413:ℝ)^2) ∧ Real.log ((413:ℝ)^2)≤(1505861941/125000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((413:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((413:ℝ)^2)=2*Real.log (413:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (59:ℝ)) := by
           rw [show (413:ℝ)=(7:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h7.1,h7.2]

theorem scale_415 : (30141391233/2500000000:ℝ)≤Real.log ((415:ℝ)^2) ∧ Real.log ((415:ℝ)^2)≤(12056557409/1000000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((415:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((415:ℝ)^2)=2*Real.log (415:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (83:ℝ)) := by
           rw [show (415:ℝ)=(5:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h5.1,h5.2]

theorem scale_417 : (60330859401/5000000000:ℝ)≤Real.log ((417:ℝ)^2) ∧ Real.log ((417:ℝ)^2)≤(117833719/9765625:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have he : Real.log ((417:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((417:ℝ)^2)=2*Real.log (417:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (139:ℝ)) := by
           rw [show (417:ℝ)=(3:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h139.1,h139.2]

theorem scale_427 : (30283918777/2500000000:ℝ)≤Real.log ((427:ℝ)^2) ∧ Real.log ((427:ℝ)^2)≤(7570980233/625000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((427:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((427:ℝ)^2)=2*Real.log (427:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (61:ℝ)) := by
           rw [show (427:ℝ)=(7:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h7.1,h7.2]

theorem scale_437 : (60799331927/5000000000:ℝ)≤Real.log ((437:ℝ)^2) ∧ Real.log ((437:ℝ)^2)≤(2431973279/200000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((437:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (23:ℝ)) := by
    calc Real.log ((437:ℝ)^2)=2*Real.log (437:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (23:ℝ)) := by
           rw [show (437:ℝ)=(19:ℝ)*(23:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h23.1,h23.2]

theorem scale_445 : (60980740067/5000000000:ℝ)≤Real.log ((445:ℝ)^2) ∧ Real.log ((445:ℝ)^2)≤(60980744677/5000000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((445:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((445:ℝ)^2)=2*Real.log (445:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (89:ℝ)) := by
           rw [show (445:ℝ)=(5:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h5.1,h5.2]

theorem scale_447 : (30512791561/2500000000:ℝ)≤Real.log ((447:ℝ)^2) ∧ Real.log ((447:ℝ)^2)≤(3051279393/250000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((447:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((447:ℝ)^2)=2*Real.log (447:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (149:ℝ)) := by
           rw [show (447:ℝ)=(3:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h149.1,h149.2]

theorem scale_451 : (15278667911/1250000000:ℝ)≤Real.log ((451:ℝ)^2) ∧ Real.log ((451:ℝ)^2)≤(3819667161/312500000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((451:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (41:ℝ)) := by
    calc Real.log ((451:ℝ)^2)=2*Real.log (451:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (41:ℝ)) := by
           rw [show (451:ℝ)=(11:ℝ)*(41:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h11.1,h11.2]

theorem scale_453 : (6115891843/500000000:ℝ)≤Real.log ((453:ℝ)^2) ∧ Real.log ((453:ℝ)^2)≤(6115892317/500000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((453:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((453:ℝ)^2)=2*Real.log (453:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (151:ℝ)) := by
           rw [show (453:ℝ)=(3:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h151.1,h151.2]

theorem scale_469 : (61506025037/5000000000:ℝ)≤Real.log ((469:ℝ)^2) ∧ Real.log ((469:ℝ)^2)≤(61506029463/5000000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((469:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((469:ℝ)^2)=2*Real.log (469:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (67:ℝ)) := by
           rw [show (469:ℝ)=(7:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h7.1,h7.2]

theorem scale_471 : (961696533/78125000:ℝ)≤Real.log ((471:ℝ)^2) ∧ Real.log ((471:ℝ)^2)≤(3077429143/250000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((471:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((471:ℝ)^2)=2*Real.log (471:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (157:ℝ)) := by
           rw [show (471:ℝ)=(3:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h157.1,h157.2]

theorem scale_473 : (12318190391/1000000000:ℝ)≤Real.log ((473:ℝ)^2) ∧ Real.log ((473:ℝ)^2)≤(12318191037/1000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((473:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (43:ℝ)) := by
    calc Real.log ((473:ℝ)^2)=2*Real.log (473:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (43:ℝ)) := by
           rw [show (473:ℝ)=(11:ℝ)*(43:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h11.1,h11.2]

theorem scale_481 : (61758671469/5000000000:ℝ)≤Real.log ((481:ℝ)^2) ∧ Real.log ((481:ℝ)^2)≤(30879336767/2500000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((481:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (37:ℝ)) := by
    calc Real.log ((481:ℝ)^2)=2*Real.log (481:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (37:ℝ)) := by
           rw [show (481:ℝ)=(13:ℝ)*(37:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h13.1,h13.2]

theorem scale_485 : (7730185767/625000000:ℝ)≤Real.log ((485:ℝ)^2) ∧ Real.log ((485:ℝ)^2)≤(61841490779/5000000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((485:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((485:ℝ)^2)=2*Real.log (485:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (97:ℝ)) := by
           rw [show (485:ℝ)=(5:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h5.1,h5.2]

theorem scale_489 : (61923622063/5000000000:ℝ)≤Real.log ((489:ℝ)^2) ∧ Real.log ((489:ℝ)^2)≤(30961813409/2500000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have he : Real.log ((489:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((489:ℝ)^2)=2*Real.log (489:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (163:ℝ)) := by
           rw [show (489:ℝ)=(3:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h163.1,h163.2]

theorem scale_493 : (12401018343/1000000000:ℝ)≤Real.log ((493:ℝ)^2) ∧ Real.log ((493:ℝ)^2)≤(62005091767/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((493:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (29:ℝ)) := by
    calc Real.log ((493:ℝ)^2)=2*Real.log (493:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (29:ℝ)) := by
           rw [show (493:ℝ)=(17:ℝ)*(29:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h29.1,h29.2]

theorem scale_497 : (31042948791/2500000000:ℝ)≤Real.log ((497:ℝ)^2) ∧ Real.log ((497:ℝ)^2)≤(31042951031/2500000000:ℝ) := by
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((497:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((497:ℝ)^2)=2*Real.log (497:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (71:ℝ)) := by
           rw [show (497:ℝ)=(7:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h71.1,h71.2,h7.1,h7.2]

theorem scale_501 : (62166058177/5000000000:ℝ)≤Real.log ((501:ℝ)^2) ∧ Real.log ((501:ℝ)^2)≤(7770757867/625000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have he : Real.log ((501:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((501:ℝ)^2)=2*Real.log (501:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (167:ℝ)) := by
           rw [show (501:ℝ)=(3:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h167.1,h167.2]

theorem scale_505 : (62245581513/5000000000:ℝ)≤Real.log ((505:ℝ)^2) ∧ Real.log ((505:ℝ)^2)≤(7780698271/625000000:ℝ) := by
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((505:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((505:ℝ)^2)=2*Real.log (505:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (101:ℝ)) := by
           rw [show (505:ℝ)=(5:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h101.1,h101.2,h5.1,h5.2]

theorem scale_511 : (6236369321/500000000:ℝ)≤Real.log ((511:ℝ)^2) ∧ Real.log ((511:ℝ)^2)≤(3897731107/312500000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((511:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((511:ℝ)^2)=2*Real.log (511:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (73:ℝ)) := by
           rw [show (511:ℝ)=(7:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h7.1,h7.2]

theorem scale_515 : (3902604139/312500000:ℝ)≤Real.log ((515:ℝ)^2) ∧ Real.log ((515:ℝ)^2)≤(12488334177/1000000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((515:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((515:ℝ)^2)=2*Real.log (515:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (103:ℝ)) := by
           rw [show (515:ℝ)=(5:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h103.1,h103.2]

theorem scale_517 : (62480426559/5000000000:ℝ)≤Real.log ((517:ℝ)^2) ∧ Real.log ((517:ℝ)^2)≤(12496086043/1000000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((517:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((517:ℝ)^2)=2*Real.log (517:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (47:ℝ)) := by
           rw [show (517:ℝ)=(11:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h47.1,h47.2]

theorem scale_519 : (12503807199/1000000000:ℝ)≤Real.log ((519:ℝ)^2) ∧ Real.log ((519:ℝ)^2)≤(1562976019/125000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have he : Real.log ((519:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((519:ℝ)^2)=2*Real.log (519:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (173:ℝ)) := by
           rw [show (519:ℝ)=(3:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h173.1,h173.2]

theorem scale_527 : (62672005459/5000000000:ℝ)≤Real.log ((527:ℝ)^2) ∧ Real.log ((527:ℝ)^2)≤(62672005513/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((527:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (31:ℝ)) := by
    calc Real.log ((527:ℝ)^2)=2*Real.log (527:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (31:ℝ)) := by
           rw [show (527:ℝ)=(17:ℝ)*(31:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h31.1,h31.2]

theorem scale_533 : (62785212489/5000000000:ℝ)≤Real.log ((533:ℝ)^2) ∧ Real.log ((533:ℝ)^2)≤(62785215423/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((533:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (41:ℝ)) := by
    calc Real.log ((533:ℝ)^2)=2*Real.log (533:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (41:ℝ)) := by
           rw [show (533:ℝ)=(13:ℝ)*(41:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h13.1,h13.2]

theorem scale_535 : (62822664681/5000000000:ℝ)≤Real.log ((535:ℝ)^2) ∧ Real.log ((535:ℝ)^2)≤(7852833669/625000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((535:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((535:ℝ)^2)=2*Real.log (535:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (107:ℝ)) := by
           rw [show (535:ℝ)=(5:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h5.1,h5.2]

theorem scale_537 : (62859978107/5000000000:ℝ)≤Real.log ((537:ℝ)^2) ∧ Real.log ((537:ℝ)^2)≤(31429991439/2500000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have he : Real.log ((537:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((537:ℝ)^2)=2*Real.log (537:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (179:ℝ)) := by
           rw [show (537:ℝ)=(3:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h179.1,h179.2]

#print axioms scale_329
#print axioms scale_334
#print axioms scale_335
#print axioms scale_339
#print axioms scale_341
#print axioms scale_346
#print axioms scale_355
#print axioms scale_358
#print axioms scale_362
#print axioms scale_365
#print axioms scale_371
#print axioms scale_377
#print axioms scale_381
#print axioms scale_382
#print axioms scale_386
#print axioms scale_391
#print axioms scale_393
#print axioms scale_394
#print axioms scale_395
#print axioms scale_398
#print axioms scale_403
#print axioms scale_407
#print axioms scale_411
#print axioms scale_413
#print axioms scale_415
#print axioms scale_417
#print axioms scale_427
#print axioms scale_437
#print axioms scale_445
#print axioms scale_447
#print axioms scale_451
#print axioms scale_453
#print axioms scale_469
#print axioms scale_471
#print axioms scale_473
#print axioms scale_481
#print axioms scale_485
#print axioms scale_489
#print axioms scale_493
#print axioms scale_497
#print axioms scale_501
#print axioms scale_505
#print axioms scale_511
#print axioms scale_515
#print axioms scale_517
#print axioms scale_519
#print axioms scale_527
#print axioms scale_533
#print axioms scale_535
#print axioms scale_537
end
end JSP233.ScaleLogs132
