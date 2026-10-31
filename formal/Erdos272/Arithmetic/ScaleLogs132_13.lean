import Erdos272.Arithmetic.PrefixTable132
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_7031 : (88580836753/5000000000:ℝ)≤Real.log ((7031:ℝ)^2) ∧ Real.log ((7031:ℝ)^2)≤(88580845899/5000000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((7031:ℝ)^2)=2*(Real.log (79:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((7031:ℝ)^2)=2*Real.log (7031:ℝ) := Real.log_pow _ _
         _=2*(Real.log (79:ℝ)+Real.log (89:ℝ)) := by
           rw [show (7031:ℝ)=(79:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h79.1,h79.2]

theorem scale_7067 : (4431595467/250000000:ℝ)≤Real.log ((7067:ℝ)^2) ∧ Real.log ((7067:ℝ)^2)≤(88631916167/5000000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have he : Real.log ((7067:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((7067:ℝ)^2)=2*Real.log (7067:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (191:ℝ)) := by
           rw [show (7067:ℝ)=(37:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h191.1,h191.2]

theorem scale_7081 : (88651698739/5000000000:ℝ)≤Real.log ((7081:ℝ)^2) ∧ Real.log ((7081:ℝ)^2)≤(44325853933/2500000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have he : Real.log ((7081:ℝ)^2)=2*(Real.log (73:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((7081:ℝ)^2)=2*Real.log (7081:ℝ) := Real.log_pow _ _
         _=2*(Real.log (73:ℝ)+Real.log (97:ℝ)) := by
           rw [show (7081:ℝ)=(73:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h97.1,h97.2]

theorem scale_7093 : (88668632033/5000000000:ℝ)≤Real.log ((7093:ℝ)^2) ∧ Real.log ((7093:ℝ)^2)≤(8866863971/500000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have he : Real.log ((7093:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((7093:ℝ)^2)=2*Real.log (7093:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (173:ℝ)) := by
           rw [show (7093:ℝ)=(41:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h173.1,h173.2]

theorem scale_7097 : (88674269383/5000000000:ℝ)≤Real.log ((7097:ℝ)^2) ∧ Real.log ((7097:ℝ)^2)≤(88674277759/5000000000:ℝ) := by
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((7097:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((7097:ℝ)^2)=2*Real.log (7097:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (151:ℝ)) := by
           rw [show (7097:ℝ)=(47:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h151.1,h151.2,h47.1,h47.2]

theorem scale_7141 : (88736076947/5000000000:ℝ)≤Real.log ((7141:ℝ)^2) ∧ Real.log ((7141:ℝ)^2)≤(1386501309/78125000:ℝ) := by
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((7141:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((7141:ℝ)^2)=2*Real.log (7141:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (193:ℝ)) := by
           rw [show (7141:ℝ)=(37:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h193.1,h193.2,h37.1,h37.2]

theorem scale_7169 : (88775209111/5000000000:ℝ)≤Real.log ((7169:ℝ)^2) ∧ Real.log ((7169:ℝ)^2)≤(8877521819/500000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have he : Real.log ((7169:ℝ)^2)=2*(Real.log (67:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((7169:ℝ)^2)=2*Real.log (7169:ℝ) := Real.log_pow _ _
         _=2*(Real.log (67:ℝ)+Real.log (107:ℝ)) := by
           rw [show (7169:ℝ)=(67:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h67.1,h67.2]

theorem scale_7171 : (11097249811/625000000:ℝ)≤Real.log ((7171:ℝ)^2) ∧ Real.log ((7171:ℝ)^2)≤(17755601521/1000000000:ℝ) := by
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((7171:ℝ)^2)=2*(Real.log (71:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((7171:ℝ)^2)=2*Real.log (7171:ℝ) := Real.log_pow _ _
         _=2*(Real.log (71:ℝ)+Real.log (101:ℝ)) := by
           rw [show (7171:ℝ)=(71:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h101.1,h101.2,h71.1,h71.2]

theorem scale_7181 : (44395967263/2500000000:ℝ)≤Real.log ((7181:ℝ)^2) ∧ Real.log ((7181:ℝ)^2)≤(17758388499/1000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have he : Real.log ((7181:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((7181:ℝ)^2)=2*Real.log (7181:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (167:ℝ)) := by
           rw [show (7181:ℝ)=(43:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h167.1,h167.2]

theorem scale_7261 : (8890272317/500000000:ℝ)≤Real.log ((7261:ℝ)^2) ∧ Real.log ((7261:ℝ)^2)≤(88902731917/5000000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((7261:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((7261:ℝ)^2)=2*Real.log (7261:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (137:ℝ)) := by
           rw [show (7261:ℝ)=(53:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h53.1,h53.2]

theorem scale_7289 : (88941212343/5000000000:ℝ)≤Real.log ((7289:ℝ)^2) ∧ Real.log ((7289:ℝ)^2)≤(88941219177/5000000000:ℝ) := by
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((7289:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((7289:ℝ)^2)=2*Real.log (7289:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (197:ℝ)) := by
           rw [show (7289:ℝ)=(37:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h197.1,h197.2,h37.1,h37.2]

theorem scale_7303 : (44480199793/2500000000:ℝ)≤Real.log ((7303:ℝ)^2) ∧ Real.log ((7303:ℝ)^2)≤(8896040867/500000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have he : Real.log ((7303:ℝ)^2)=2*(Real.log (67:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((7303:ℝ)^2)=2*Real.log (7303:ℝ) := Real.log_pow _ _
         _=2*(Real.log (67:ℝ)+Real.log (109:ℝ)) := by
           rw [show (7303:ℝ)=(67:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h109.1,h109.2]

theorem scale_7313 : (88974083199/5000000000:ℝ)≤Real.log ((7313:ℝ)^2) ∧ Real.log ((7313:ℝ)^2)≤(44487046161/2500000000:ℝ) := by
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((7313:ℝ)^2)=2*(Real.log (71:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((7313:ℝ)^2)=2*Real.log (7313:ℝ) := Real.log_pow _ _
         _=2*(Real.log (71:ℝ)+Real.log (103:ℝ)) := by
           rw [show (7313:ℝ)=(71:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h103.1,h103.2,h71.1,h71.2]

theorem scale_7339 : (17801914829/1000000000:ℝ)≤Real.log ((7339:ℝ)^2) ∧ Real.log ((7339:ℝ)^2)≤(22252395457/1250000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have he : Real.log ((7339:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((7339:ℝ)^2)=2*Real.log (7339:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (179:ℝ)) := by
           rw [show (7339:ℝ)=(41:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h179.1,h179.2]

theorem scale_7363 : (44521111651/2500000000:ℝ)≤Real.log ((7363:ℝ)^2) ∧ Real.log ((7363:ℝ)^2)≤(44521115069/2500000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have he : Real.log ((7363:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((7363:ℝ)^2)=2*Real.log (7363:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (199:ℝ)) := by
           rw [show (7363:ℝ)=(37:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h199.1,h199.2]

theorem scale_7367 : (44523826621/2500000000:ℝ)≤Real.log ((7367:ℝ)^2) ∧ Real.log ((7367:ℝ)^2)≤(89047661991/5000000000:ℝ) := by
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((7367:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((7367:ℝ)^2)=2*Real.log (7367:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (139:ℝ)) := by
           rw [show (7367:ℝ)=(53:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h139.1,h139.2,h53.1,h53.2]

theorem scale_7373 : (22263948529/1250000000:ℝ)≤Real.log ((7373:ℝ)^2) ∧ Real.log ((7373:ℝ)^2)≤(17811160651/1000000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((7373:ℝ)^2)=2*(Real.log (73:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((7373:ℝ)^2)=2*Real.log (7373:ℝ) := Real.log_pow _ _
         _=2*(Real.log (73:ℝ)+Real.log (101:ℝ)) := by
           rw [show (7373:ℝ)=(73:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h101.1,h101.2]

theorem scale_7379 : (17812785813/1000000000:ℝ)≤Real.log ((7379:ℝ)^2) ∧ Real.log ((7379:ℝ)^2)≤(89063937449/5000000000:ℝ) := by
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((7379:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((7379:ℝ)^2)=2*Real.log (7379:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (157:ℝ)) := by
           rw [show (7379:ℝ)=(47:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h157.1,h157.2,h47.1,h47.2]

theorem scale_7387 : (89074764291/5000000000:ℝ)≤Real.log ((7387:ℝ)^2) ∧ Real.log ((7387:ℝ)^2)≤(11134346683/625000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have he : Real.log ((7387:ℝ)^2)=2*(Real.log (83:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((7387:ℝ)^2)=2*Real.log (7387:ℝ) := Real.log_pow _ _
         _=2*(Real.log (83:ℝ)+Real.log (89:ℝ)) := by
           rw [show (7387:ℝ)=(83:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h83.1,h83.2]

theorem scale_7421 : (44560343199/2500000000:ℝ)≤Real.log ((7421:ℝ)^2) ∧ Real.log ((7421:ℝ)^2)≤(89120694083/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have he : Real.log ((7421:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((7421:ℝ)^2)=2*Real.log (7421:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (181:ℝ)) := by
           rw [show (7421:ℝ)=(41:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h181.1,h181.2]

theorem scale_7439 : (11143114043/625000000:ℝ)≤Real.log ((7439:ℝ)^2) ∧ Real.log ((7439:ℝ)^2)≤(89144920319/5000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have he : Real.log ((7439:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((7439:ℝ)^2)=2*Real.log (7439:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (173:ℝ)) := by
           rw [show (7439:ℝ)=(43:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h173.1,h173.2]

theorem scale_7493 : (44608619977/2500000000:ℝ)≤Real.log ((7493:ℝ)^2) ∧ Real.log ((7493:ℝ)^2)≤(44608624453/2500000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((7493:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((7493:ℝ)^2)=2*Real.log (7493:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (127:ℝ)) := by
           rw [show (7493:ℝ)=(59:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h127.1,h127.2]

theorem scale_7519 : (89251878827/5000000000:ℝ)≤Real.log ((7519:ℝ)^2) ∧ Real.log ((7519:ℝ)^2)≤(22312971993/1250000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((7519:ℝ)^2)=2*(Real.log (73:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((7519:ℝ)^2)=2*Real.log (7519:ℝ) := Real.log_pow _ _
         _=2*(Real.log (73:ℝ)+Real.log (103:ℝ)) := by
           rw [show (7519:ℝ)=(73:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h103.1,h103.2]

theorem scale_7571 : (44660399473/2500000000:ℝ)≤Real.log ((7571:ℝ)^2) ∧ Real.log ((7571:ℝ)^2)≤(89320808039/5000000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have he : Real.log ((7571:ℝ)^2)=2*(Real.log (67:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((7571:ℝ)^2)=2*Real.log (7571:ℝ) := Real.log_pow _ _
         _=2*(Real.log (67:ℝ)+Real.log (113:ℝ)) := by
           rw [show (7571:ℝ)=(67:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h67.1,h67.2]

theorem scale_7597 : (11169385207/625000000:ℝ)≤Real.log ((7597:ℝ)^2) ∧ Real.log ((7597:ℝ)^2)≤(89355090789/5000000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((7597:ℝ)^2)=2*(Real.log (71:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((7597:ℝ)^2)=2*Real.log (7597:ℝ) := Real.log_pow _ _
         _=2*(Real.log (71:ℝ)+Real.log (107:ℝ)) := by
           rw [show (7597:ℝ)=(71:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h71.1,h71.2]

theorem scale_7661 : (11179871627/625000000:ℝ)≤Real.log ((7661:ℝ)^2) ∧ Real.log ((7661:ℝ)^2)≤(89438981407/5000000000:ℝ) := by
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((7661:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((7661:ℝ)^2)=2*Real.log (7661:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (163:ℝ)) := by
           rw [show (7661:ℝ)=(47:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h163.1,h163.2,h47.1,h47.2]

theorem scale_7663 : (44720791411/2500000000:ℝ)≤Real.log ((7663:ℝ)^2) ∧ Real.log ((7663:ℝ)^2)≤(89441592001/5000000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((7663:ℝ)^2)=2*(Real.log (79:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((7663:ℝ)^2)=2*Real.log (7663:ℝ) := Real.log_pow _ _
         _=2*(Real.log (79:ℝ)+Real.log (97:ℝ)) := by
           rw [show (7663:ℝ)=(79:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h79.1,h79.2]

theorem scale_7697 : (11185731807/625000000:ℝ)≤Real.log ((7697:ℝ)^2) ∧ Real.log ((7697:ℝ)^2)≤(89485862437/5000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have he : Real.log ((7697:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((7697:ℝ)^2)=2*Real.log (7697:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (179:ℝ)) := by
           rw [show (7697:ℝ)=(43:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h179.1,h179.2]

theorem scale_7729 : (89527342319/5000000000:ℝ)≤Real.log ((7729:ℝ)^2) ∧ Real.log ((7729:ℝ)^2)≤(22381837819/1250000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have he : Real.log ((7729:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((7729:ℝ)^2)=2*Real.log (7729:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (131:ℝ)) := by
           rw [show (7729:ℝ)=(59:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h131.1,h131.2]

theorem scale_7739 : (89540272131/5000000000:ℝ)≤Real.log ((7739:ℝ)^2) ∧ Real.log ((7739:ℝ)^2)≤(89540281269/5000000000:ℝ) := by
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((7739:ℝ)^2)=2*(Real.log (71:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((7739:ℝ)^2)=2*Real.log (7739:ℝ) := Real.log_pow _ _
         _=2*(Real.log (71:ℝ)+Real.log (109:ℝ)) := by
           rw [show (7739:ℝ)=(71:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h109.1,h109.2,h71.1,h71.2]

theorem scale_7747 : (44775302063/2500000000:ℝ)≤Real.log ((7747:ℝ)^2) ∧ Real.log ((7747:ℝ)^2)≤(8955061313/500000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((7747:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((7747:ℝ)^2)=2*Real.log (7747:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (127:ℝ)) := by
           rw [show (7747:ℝ)=(61:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h127.1,h127.2]

theorem scale_7783 : (89596966709/5000000000:ℝ)≤Real.log ((7783:ℝ)^2) ∧ Real.log ((7783:ℝ)^2)≤(22399243673/1250000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have he : Real.log ((7783:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((7783:ℝ)^2)=2*Real.log (7783:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (181:ℝ)) := by
           rw [show (7783:ℝ)=(43:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h181.1,h181.2]

theorem scale_7811 : (22408219321/1250000000:ℝ)≤Real.log ((7811:ℝ)^2) ∧ Real.log ((7811:ℝ)^2)≤(89632886439/5000000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have he : Real.log ((7811:ℝ)^2)=2*(Real.log (73:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((7811:ℝ)^2)=2*Real.log (7811:ℝ) := Real.log_pow _ _
         _=2*(Real.log (73:ℝ)+Real.log (107:ℝ)) := by
           rw [show (7811:ℝ)=(73:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h107.1,h107.2]

theorem scale_7831 : (2241461259/125000000:ℝ)≤Real.log ((7831:ℝ)^2) ∧ Real.log ((7831:ℝ)^2)≤(11207307257/625000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have he : Real.log ((7831:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((7831:ℝ)^2)=2*Real.log (7831:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (191:ℝ)) := by
           rw [show (7831:ℝ)=(41:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h191.1,h191.2]

theorem scale_7849 : (8968140913/500000000:ℝ)≤Real.log ((7849:ℝ)^2) ∧ Real.log ((7849:ℝ)^2)≤(3587256701/200000000:ℝ) := by
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((7849:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((7849:ℝ)^2)=2*Real.log (7849:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (167:ℝ)) := by
           rw [show (7849:ℝ)=(47:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h167.1,h167.2,h47.1,h47.2]

theorem scale_7897 : (89742376963/5000000000:ℝ)≤Real.log ((7897:ℝ)^2) ∧ Real.log ((7897:ℝ)^2)≤(89742385723/5000000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((7897:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((7897:ℝ)^2)=2*Real.log (7897:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (149:ℝ)) := by
           rw [show (7897:ℝ)=(53:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h149.1,h149.2]

theorem scale_7913 : (89762617967/5000000000:ℝ)≤Real.log ((7913:ℝ)^2) ∧ Real.log ((7913:ℝ)^2)≤(17952525133/1000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have he : Real.log ((7913:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((7913:ℝ)^2)=2*Real.log (7913:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (193:ℝ)) := by
           rw [show (7913:ℝ)=(41:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h193.1,h193.2]

theorem scale_7957 : (89818067759/5000000000:ℝ)≤Real.log ((7957:ℝ)^2) ∧ Real.log ((7957:ℝ)^2)≤(89818076919/5000000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have he : Real.log ((7957:ℝ)^2)=2*(Real.log (73:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((7957:ℝ)^2)=2*Real.log (7957:ℝ) := Real.log_pow _ _
         _=2*(Real.log (73:ℝ)+Real.log (109:ℝ)) := by
           rw [show (7957:ℝ)=(73:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h109.1,h109.2]

theorem scale_7979 : (89845678199/5000000000:ℝ)≤Real.log ((7979:ℝ)^2) ∧ Real.log ((7979:ℝ)^2)≤(8984568739/500000000:ℝ) := by
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((7979:ℝ)^2)=2*(Real.log (79:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((7979:ℝ)^2)=2*Real.log (7979:ℝ) := Real.log_pow _ _
         _=2*(Real.log (79:ℝ)+Real.log (101:ℝ)) := by
           rw [show (7979:ℝ)=(79:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h101.1,h101.2,h79.1,h79.2]

theorem scale_7991 : (89860706491/5000000000:ℝ)≤Real.log ((7991:ℝ)^2) ∧ Real.log ((7991:ℝ)^2)≤(179721431/10000000:ℝ) := by
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((7991:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((7991:ℝ)^2)=2*Real.log (7991:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (131:ℝ)) := by
           rw [show (7991:ℝ)=(61:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h131.1,h131.2,h61.1,h61.2]

theorem scale_8003 : (89875712271/5000000000:ℝ)≤Real.log ((8003:ℝ)^2) ∧ Real.log ((8003:ℝ)^2)≤(89875721033/5000000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((8003:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((8003:ℝ)^2)=2*Real.log (8003:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (151:ℝ)) := by
           rw [show (8003:ℝ)=(53:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h151.1,h151.2]

theorem scale_8023 : (89900671491/5000000000:ℝ)≤Real.log ((8023:ℝ)^2) ∧ Real.log ((8023:ℝ)^2)≤(44950340319/2500000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((8023:ℝ)^2)=2*(Real.log (71:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((8023:ℝ)^2)=2*Real.log (8023:ℝ) := Real.log_pow _ _
         _=2*(Real.log (71:ℝ)+Real.log (113:ℝ)) := by
           rw [show (8023:ℝ)=(71:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h71.1,h71.2]

theorem scale_8051 : (2248387759/125000000:ℝ)≤Real.log ((8051:ℝ)^2) ∧ Real.log ((8051:ℝ)^2)≤(44967759783/2500000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have he : Real.log ((8051:ℝ)^2)=2*(Real.log (83:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((8051:ℝ)^2)=2*Real.log (8051:ℝ) := Real.log_pow _ _
         _=2*(Real.log (83:ℝ)+Real.log (97:ℝ)) := by
           rw [show (8051:ℝ)=(83:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h83.1,h83.2]

theorem scale_8077 : (89967753363/5000000000:ℝ)≤Real.log ((8077:ℝ)^2) ∧ Real.log ((8077:ℝ)^2)≤(44983880533/2500000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have he : Real.log ((8077:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((8077:ℝ)^2)=2*Real.log (8077:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (197:ℝ)) := by
           rw [show (8077:ℝ)=(41:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h197.1,h197.2]

theorem scale_8083 : (89975178341/5000000000:ℝ)≤Real.log ((8083:ℝ)^2) ∧ Real.log ((8083:ℝ)^2)≤(22493796827/1250000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have he : Real.log ((8083:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((8083:ℝ)^2)=2*Real.log (8083:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (137:ℝ)) := by
           rw [show (8083:ℝ)=(59:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h59.1,h59.2]

theorem scale_8131 : (22508596737/1250000000:ℝ)≤Real.log ((8131:ℝ)^2) ∧ Real.log ((8131:ℝ)^2)≤(90034395349/5000000000:ℝ) := by
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((8131:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((8131:ℝ)^2)=2*Real.log (8131:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (173:ℝ)) := by
           rw [show (8131:ℝ)=(47:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h173.1,h173.2,h47.1,h47.2]

theorem scale_8137 : (9004176291/500000000:ℝ)≤Real.log ((8137:ℝ)^2) ∧ Real.log ((8137:ℝ)^2)≤(90041772107/5000000000:ℝ) := by
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((8137:ℝ)^2)=2*(Real.log (79:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((8137:ℝ)^2)=2*Real.log (8137:ℝ) := Real.log_pow _ _
         _=2*(Real.log (79:ℝ)+Real.log (103:ℝ)) := by
           rw [show (8137:ℝ)=(79:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h103.1,h103.2,h79.1,h79.2]

theorem scale_8159 : (45034382161/2500000000:ℝ)≤Real.log ((8159:ℝ)^2) ∧ Real.log ((8159:ℝ)^2)≤(90068772027/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have he : Real.log ((8159:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((8159:ℝ)^2)=2*Real.log (8159:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (199:ℝ)) := by
           rw [show (8159:ℝ)=(41:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h199.1,h199.2]

theorem scale_8201 : (90120108413/5000000000:ℝ)≤Real.log ((8201:ℝ)^2) ∧ Real.log ((8201:ℝ)^2)≤(45060058691/2500000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have he : Real.log ((8201:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((8201:ℝ)^2)=2*Real.log (8201:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (139:ℝ)) := by
           rw [show (8201:ℝ)=(59:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h139.1,h139.2]

theorem scale_8213 : (90134730671/5000000000:ℝ)≤Real.log ((8213:ℝ)^2) ∧ Real.log ((8213:ℝ)^2)≤(18026947733/1000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have he : Real.log ((8213:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((8213:ℝ)^2)=2*Real.log (8213:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (191:ℝ)) := by
           rw [show (8213:ℝ)=(43:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h191.1,h191.2]

#print axioms scale_7031
#print axioms scale_7067
#print axioms scale_7081
#print axioms scale_7093
#print axioms scale_7097
#print axioms scale_7141
#print axioms scale_7169
#print axioms scale_7171
#print axioms scale_7181
#print axioms scale_7261
#print axioms scale_7289
#print axioms scale_7303
#print axioms scale_7313
#print axioms scale_7339
#print axioms scale_7363
#print axioms scale_7367
#print axioms scale_7373
#print axioms scale_7379
#print axioms scale_7387
#print axioms scale_7421
#print axioms scale_7439
#print axioms scale_7493
#print axioms scale_7519
#print axioms scale_7571
#print axioms scale_7597
#print axioms scale_7661
#print axioms scale_7663
#print axioms scale_7697
#print axioms scale_7729
#print axioms scale_7739
#print axioms scale_7747
#print axioms scale_7783
#print axioms scale_7811
#print axioms scale_7831
#print axioms scale_7849
#print axioms scale_7897
#print axioms scale_7913
#print axioms scale_7957
#print axioms scale_7979
#print axioms scale_7991
#print axioms scale_8003
#print axioms scale_8023
#print axioms scale_8051
#print axioms scale_8077
#print axioms scale_8083
#print axioms scale_8131
#print axioms scale_8137
#print axioms scale_8159
#print axioms scale_8201
#print axioms scale_8213
end
end JSP233.ScaleLogs132
