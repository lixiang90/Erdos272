module

public import Erdos272.Arithmetic.PrefixTable132

@[expose] public section
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_8249 : (90178467119/5000000000:ℝ)≤Real.log ((8249:ℝ)^2) ∧ Real.log ((8249:ℝ)^2)≤(352259673/19531250:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have he : Real.log ((8249:ℝ)^2)=2*(Real.log (73:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((8249:ℝ)^2)=2*Real.log (8249:ℝ) := Real.log_pow _ _
         _=2*(Real.log (73:ℝ)+Real.log (113:ℝ)) := by
           rw [show (8249:ℝ)=(73:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h113.1,h113.2]

theorem scale_8299 : (45119449139/2500000000:ℝ)≤Real.log ((8299:ℝ)^2) ∧ Real.log ((8299:ℝ)^2)≤(45119453137/2500000000:ℝ) := by
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have he : Real.log ((8299:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((8299:ℝ)^2)=2*Real.log (8299:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (193:ℝ)) := by
           rw [show (8299:ℝ)=(43:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h193.1,h193.2,h43.1,h43.2]

theorem scale_8321 : (90265371953/5000000000:ℝ)≤Real.log ((8321:ℝ)^2) ∧ Real.log ((8321:ℝ)^2)≤(90265380723/5000000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((8321:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((8321:ℝ)^2)=2*Real.log (8321:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (157:ℝ)) := by
           rw [show (8321:ℝ)=(53:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h157.1,h157.2]

theorem scale_8357 : (90308542513/5000000000:ℝ)≤Real.log ((8357:ℝ)^2) ∧ Real.log ((8357:ℝ)^2)≤(22577137883/1250000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((8357:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((8357:ℝ)^2)=2*Real.log (8357:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (137:ℝ)) := by
           rw [show (8357:ℝ)=(61:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h61.1,h61.2]

theorem scale_8383 : (90339605737/5000000000:ℝ)≤Real.log ((8383:ℝ)^2) ∧ Real.log ((8383:ℝ)^2)≤(18067922991/1000000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((8383:ℝ)^2)=2*(Real.log (83:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((8383:ℝ)^2)=2*Real.log (8383:ℝ) := Real.log_pow _ _
         _=2*(Real.log (83:ℝ)+Real.log (101:ℝ)) := by
           rw [show (8383:ℝ)=(83:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h101.1,h101.2]

theorem scale_8413 : (4518766453/250000000:ℝ)≤Real.log ((8413:ℝ)^2) ∧ Real.log ((8413:ℝ)^2)≤(90375337467/5000000000:ℝ) := by
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((8413:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((8413:ℝ)^2)=2*Real.log (8413:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (179:ℝ)) := by
           rw [show (8413:ℝ)=(47:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h179.1,h179.2,h47.1,h47.2]

theorem scale_8453 : (90422761367/5000000000:ℝ)≤Real.log ((8453:ℝ)^2) ∧ Real.log ((8453:ℝ)^2)≤(45211385287/2500000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((8453:ℝ)^2)=2*(Real.log (79:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((8453:ℝ)^2)=2*Real.log (8453:ℝ) := Real.log_pow _ _
         _=2*(Real.log (79:ℝ)+Real.log (107:ℝ)) := by
           rw [show (8453:ℝ)=(79:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h79.1,h79.2]

theorem scale_8471 : (45222016837/2500000000:ℝ)≤Real.log ((8471:ℝ)^2) ∧ Real.log ((8471:ℝ)^2)≤(3617761667/200000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have he : Real.log ((8471:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((8471:ℝ)^2)=2*Real.log (8471:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (197:ℝ)) := by
           rw [show (8471:ℝ)=(43:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h197.1,h197.2]

theorem scale_8479 : (18090694517/1000000000:ℝ)≤Real.log ((8479:ℝ)^2) ∧ Real.log ((8479:ℝ)^2)≤(45226740803/2500000000:ℝ) := by
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((8479:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((8479:ℝ)^2)=2*Real.log (8479:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (139:ℝ)) := by
           rw [show (8479:ℝ)=(61:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h139.1,h139.2,h61.1,h61.2]

theorem scale_8507 : (90486441313/5000000000:ℝ)≤Real.log ((8507:ℝ)^2) ∧ Real.log ((8507:ℝ)^2)≤(45243224861/2500000000:ℝ) := by
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((8507:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((8507:ℝ)^2)=2*Real.log (8507:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (181:ℝ)) := by
           rw [show (8507:ℝ)=(47:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h181.1,h181.2,h47.1,h47.2]

theorem scale_8509 : (90488791609/5000000000:ℝ)≤Real.log ((8509:ℝ)^2) ∧ Real.log ((8509:ℝ)^2)≤(90488800729/5000000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((8509:ℝ)^2)=2*(Real.log (67:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((8509:ℝ)^2)=2*Real.log (8509:ℝ) := Real.log_pow _ _
         _=2*(Real.log (67:ℝ)+Real.log (127:ℝ)) := by
           rw [show (8509:ℝ)=(67:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h127.1,h127.2]

theorem scale_8549 : (5658480653/312500000:ℝ)≤Real.log ((8549:ℝ)^2) ∧ Real.log ((8549:ℝ)^2)≤(11316962459/625000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((8549:ℝ)^2)=2*(Real.log (83:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((8549:ℝ)^2)=2*Real.log (8549:ℝ) := Real.log_pow _ _
         _=2*(Real.log (83:ℝ)+Real.log (103:ℝ)) := by
           rw [show (8549:ℝ)=(83:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h103.1,h103.2]

theorem scale_8557 : (90545044633/5000000000:ℝ)≤Real.log ((8557:ℝ)^2) ∧ Real.log ((8557:ℝ)^2)≤(22636263159/1250000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have he : Real.log ((8557:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((8557:ℝ)^2)=2*Real.log (8557:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (199:ℝ)) := by
           rw [show (8557:ℝ)=(43:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h199.1,h199.2]

theorem scale_8611 : (45303975921/2500000000:ℝ)≤Real.log ((8611:ℝ)^2) ∧ Real.log ((8611:ℝ)^2)≤(45303980527/2500000000:ℝ) := by
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((8611:ℝ)^2)=2*(Real.log (79:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((8611:ℝ)^2)=2*Real.log (8611:ℝ) := Real.log_pow _ _
         _=2*(Real.log (79:ℝ)+Real.log (109:ℝ)) := by
           rw [show (8611:ℝ)=(79:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h109.1,h109.2,h79.1,h79.2]

theorem scale_8633 : (90633467961/5000000000:ℝ)≤Real.log ((8633:ℝ)^2) ∧ Real.log ((8633:ℝ)^2)≤(45316738599/2500000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have he : Real.log ((8633:ℝ)^2)=2*(Real.log (89:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((8633:ℝ)^2)=2*Real.log (8633:ℝ) := Real.log_pow _ _
         _=2*(Real.log (89:ℝ)+Real.log (97:ℝ)) := by
           rw [show (8633:ℝ)=(89:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h97.1,h97.2]

theorem scale_8639 : (2832512997/156250000:ℝ)≤Real.log ((8639:ℝ)^2) ∧ Real.log ((8639:ℝ)^2)≤(90640424681/5000000000:ℝ) := by
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((8639:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((8639:ℝ)^2)=2*Real.log (8639:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (163:ℝ)) := by
           rw [show (8639:ℝ)=(53:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h163.1,h163.2,h53.1,h53.2]

theorem scale_8777 : (45399446987/2500000000:ℝ)≤Real.log ((8777:ℝ)^2) ∧ Real.log ((8777:ℝ)^2)≤(90798903099/5000000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have he : Real.log ((8777:ℝ)^2)=2*(Real.log (67:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((8777:ℝ)^2)=2*Real.log (8777:ℝ) := Real.log_pow _ _
         _=2*(Real.log (67:ℝ)+Real.log (131:ℝ)) := by
           rw [show (8777:ℝ)=(67:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h131.1,h131.2]

theorem scale_8791 : (45407416067/2500000000:ℝ)≤Real.log ((8791:ℝ)^2) ∧ Real.log ((8791:ℝ)^2)≤(45407420557/2500000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((8791:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((8791:ℝ)^2)=2*Real.log (8791:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (149:ℝ)) := by
           rw [show (8791:ℝ)=(59:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h149.1,h149.2]

theorem scale_8851 : (45441426009/2500000000:ℝ)≤Real.log ((8851:ℝ)^2) ∧ Real.log ((8851:ℝ)^2)≤(90882860799/5000000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have he : Real.log ((8851:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((8851:ℝ)^2)=2*Real.log (8851:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (167:ℝ)) := by
           rw [show (8851:ℝ)=(53:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h167.1,h167.2]

theorem scale_8881 : (18183337781/1000000000:ℝ)≤Real.log ((8881:ℝ)^2) ∧ Real.log ((8881:ℝ)^2)≤(90916698139/5000000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have he : Real.log ((8881:ℝ)^2)=2*(Real.log (83:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((8881:ℝ)^2)=2*Real.log (8881:ℝ) := Real.log_pow _ _
         _=2*(Real.log (83:ℝ)+Real.log (107:ℝ)) := by
           rw [show (8881:ℝ)=(83:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h83.1,h83.2]

theorem scale_8909 : (45474083721/2500000000:ℝ)≤Real.log ((8909:ℝ)^2) ∧ Real.log ((8909:ℝ)^2)≤(11368522053/625000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((8909:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((8909:ℝ)^2)=2*Real.log (8909:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (151:ℝ)) := by
           rw [show (8909:ℝ)=(59:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h151.1,h151.2]

theorem scale_8927 : (45484175601/2500000000:ℝ)≤Real.log ((8927:ℝ)^2) ∧ Real.log ((8927:ℝ)^2)≤(90968360423/5000000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((8927:ℝ)^2)=2*(Real.log (79:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((8927:ℝ)^2)=2*Real.log (8927:ℝ) := Real.log_pow _ _
         _=2*(Real.log (79:ℝ)+Real.log (113:ℝ)) := by
           rw [show (8927:ℝ)=(79:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h79.1,h79.2]

theorem scale_8977 : (3640968211/200000000:ℝ)≤Real.log ((8977:ℝ)^2) ∧ Real.log ((8977:ℝ)^2)≤(18204842739/1000000000:ℝ) := by
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((8977:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((8977:ℝ)^2)=2*Real.log (8977:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (191:ℝ)) := by
           rw [show (8977:ℝ)=(47:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h191.1,h191.2,h47.1,h47.2]

theorem scale_8989 : (45518781669/2500000000:ℝ)≤Real.log ((8989:ℝ)^2) ∧ Real.log ((8989:ℝ)^2)≤(91037572587/5000000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((8989:ℝ)^2)=2*(Real.log (89:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((8989:ℝ)^2)=2*Real.log (8989:ℝ) := Real.log_pow _ _
         _=2*(Real.log (89:ℝ)+Real.log (101:ℝ)) := by
           rw [show (8989:ℝ)=(89:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h101.1,h101.2]

theorem scale_9017 : (45534332077/2500000000:ℝ)≤Real.log ((9017:ℝ)^2) ∧ Real.log ((9017:ℝ)^2)≤(5691792083/312500000:ℝ) := by
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((9017:ℝ)^2)=2*(Real.log (71:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((9017:ℝ)^2)=2*Real.log (9017:ℝ) := Real.log_pow _ _
         _=2*(Real.log (71:ℝ)+Real.log (127:ℝ)) := by
           rw [show (9017:ℝ)=(71:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h127.1,h127.2,h71.1,h71.2]

theorem scale_9047 : (4555093969/250000000:ℝ)≤Real.log ((9047:ℝ)^2) ∧ Real.log ((9047:ℝ)^2)≤(91101888619/5000000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have he : Real.log ((9047:ℝ)^2)=2*(Real.log (83:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((9047:ℝ)^2)=2*Real.log (9047:ℝ) := Real.log_pow _ _
         _=2*(Real.log (83:ℝ)+Real.log (109:ℝ)) := by
           rw [show (9047:ℝ)=(83:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h109.1,h109.2]

theorem scale_9071 : (45564186441/2500000000:ℝ)≤Real.log ((9071:ℝ)^2) ∧ Real.log ((9071:ℝ)^2)≤(11391047663/625000000:ℝ) := by
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((9071:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((9071:ℝ)^2)=2*Real.log (9071:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (193:ℝ)) := by
           rw [show (9071:ℝ)=(47:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h193.1,h193.2,h47.1,h47.2]

theorem scale_9089 : (45574098153/2500000000:ℝ)≤Real.log ((9089:ℝ)^2) ∧ Real.log ((9089:ℝ)^2)≤(45574102669/2500000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((9089:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((9089:ℝ)^2)=2*Real.log (9089:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (149:ℝ)) := by
           rw [show (9089:ℝ)=(61:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h149.1,h149.2]

theorem scale_9167 : (91233648049/5000000000:ℝ)≤Real.log ((9167:ℝ)^2) ∧ Real.log ((9167:ℝ)^2)≤(11404207163/625000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((9167:ℝ)^2)=2*(Real.log (89:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((9167:ℝ)^2)=2*Real.log (9167:ℝ) := Real.log_pow _ _
         _=2*(Real.log (89:ℝ)+Real.log (103:ℝ)) := by
           rw [show (9167:ℝ)=(89:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h103.1,h103.2]

theorem scale_9169 : (22808957459/1250000000:ℝ)≤Real.log ((9169:ℝ)^2) ∧ Real.log ((9169:ℝ)^2)≤(91235838623/5000000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have he : Real.log ((9169:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((9169:ℝ)^2)=2*Real.log (9169:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (173:ℝ)) := by
           rw [show (9169:ℝ)=(53:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h173.1,h173.2]

theorem scale_9179 : (22811682499/1250000000:ℝ)≤Real.log ((9179:ℝ)^2) ∧ Real.log ((9179:ℝ)^2)≤(91246739131/5000000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have he : Real.log ((9179:ℝ)^2)=2*(Real.log (67:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((9179:ℝ)^2)=2*Real.log (9179:ℝ) := Real.log_pow _ _
         _=2*(Real.log (67:ℝ)+Real.log (137:ℝ)) := by
           rw [show (9179:ℝ)=(67:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h67.1,h67.2]

theorem scale_9211 : (45640765807/2500000000:ℝ)≤Real.log ((9211:ℝ)^2) ∧ Real.log ((9211:ℝ)^2)≤(11410192581/625000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((9211:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((9211:ℝ)^2)=2*Real.log (9211:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (151:ℝ)) := by
           rw [show (9211:ℝ)=(61:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h151.1,h151.2]

theorem scale_9259 : (45666754139/2500000000:ℝ)≤Real.log ((9259:ℝ)^2) ∧ Real.log ((9259:ℝ)^2)≤(18266703341/1000000000:ℝ) := by
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((9259:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((9259:ℝ)^2)=2*Real.log (9259:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (197:ℝ)) := by
           rw [show (9259:ℝ)=(47:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h197.1,h197.2,h47.1,h47.2]

theorem scale_9263 : (22834456781/1250000000:ℝ)≤Real.log ((9263:ℝ)^2) ∧ Real.log ((9263:ℝ)^2)≤(45668918057/2500000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((9263:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((9263:ℝ)^2)=2*Real.log (9263:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (157:ℝ)) := by
           rw [show (9263:ℝ)=(59:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h157.1,h157.2]

theorem scale_9271 : (45673229891/2500000000:ℝ)≤Real.log ((9271:ℝ)^2) ∧ Real.log ((9271:ℝ)^2)≤(45673234489/2500000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((9271:ℝ)^2)=2*(Real.log (73:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((9271:ℝ)^2)=2*Real.log (9271:ℝ) := Real.log_pow _ _
         _=2*(Real.log (73:ℝ)+Real.log (127:ℝ)) := by
           rw [show (9271:ℝ)=(73:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h127.1,h127.2]

theorem scale_9301 : (91378766519/5000000000:ℝ)≤Real.log ((9301:ℝ)^2) ∧ Real.log ((9301:ℝ)^2)≤(45689387849/2500000000:ℝ) := by
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((9301:ℝ)^2)=2*(Real.log (71:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((9301:ℝ)^2)=2*Real.log (9301:ℝ) := Real.log_pow _ _
         _=2*(Real.log (71:ℝ)+Real.log (131:ℝ)) := by
           rw [show (9301:ℝ)=(71:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h131.1,h131.2,h71.1,h71.2]

theorem scale_9313 : (22847915017/1250000000:ℝ)≤Real.log ((9313:ℝ)^2) ∧ Real.log ((9313:ℝ)^2)≤(18278333841/1000000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have he : Real.log ((9313:ℝ)^2)=2*(Real.log (67:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((9313:ℝ)^2)=2*Real.log (9313:ℝ) := Real.log_pow _ _
         _=2*(Real.log (67:ℝ)+Real.log (139:ℝ)) := by
           rw [show (9313:ℝ)=(67:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h139.1,h139.2]

theorem scale_9353 : (91434519237/5000000000:ℝ)≤Real.log ((9353:ℝ)^2) ∧ Real.log ((9353:ℝ)^2)≤(45717263833/2500000000:ℝ) := by
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((9353:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((9353:ℝ)^2)=2*Real.log (9353:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (199:ℝ)) := by
           rw [show (9353:ℝ)=(47:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h199.1,h199.2,h47.1,h47.2]

theorem scale_9379 : (4573113937/250000000:ℝ)≤Real.log ((9379:ℝ)^2) ∧ Real.log ((9379:ℝ)^2)≤(22865571997/1250000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have he : Real.log ((9379:ℝ)^2)=2*(Real.log (83:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((9379:ℝ)^2)=2*Real.log (9379:ℝ) := Real.log_pow _ _
         _=2*(Real.log (83:ℝ)+Real.log (113:ℝ)) := by
           rw [show (9379:ℝ)=(83:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h83.1,h83.2]

theorem scale_9487 : (22894192987/1250000000:ℝ)≤Real.log ((9487:ℝ)^2) ∧ Real.log ((9487:ℝ)^2)≤(91576780741/5000000000:ℝ) := by
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((9487:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((9487:ℝ)^2)=2*Real.log (9487:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (179:ℝ)) := by
           rw [show (9487:ℝ)=(53:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h179.1,h179.2,h53.1,h53.2]

theorem scale_9523 : (45807323253/2500000000:ℝ)≤Real.log ((9523:ℝ)^2) ∧ Real.log ((9523:ℝ)^2)≤(91614655771/5000000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have he : Real.log ((9523:ℝ)^2)=2*(Real.log (89:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((9523:ℝ)^2)=2*Real.log (9523:ℝ) := Real.log_pow _ _
         _=2*(Real.log (89:ℝ)+Real.log (107:ℝ)) := by
           rw [show (9523:ℝ)=(89:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h107.1,h107.2]

theorem scale_9563 : (91656562147/5000000000:ℝ)≤Real.log ((9563:ℝ)^2) ∧ Real.log ((9563:ℝ)^2)≤(22914142837/1250000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have he : Real.log ((9563:ℝ)^2)=2*(Real.log (73:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((9563:ℝ)^2)=2*Real.log (9563:ℝ) := Real.log_pow _ _
         _=2*(Real.log (73:ℝ)+Real.log (131:ℝ)) := by
           rw [show (9563:ℝ)=(73:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h131.1,h131.2]

theorem scale_9577 : (358090591/19531250:ℝ)≤Real.log ((9577:ℝ)^2) ∧ Real.log ((9577:ℝ)^2)≤(45835600169/2500000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((9577:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((9577:ℝ)^2)=2*Real.log (9577:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (157:ℝ)) := by
           rw [show (9577:ℝ)=(61:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h157.1,h157.2]

theorem scale_9593 : (91687884201/5000000000:ℝ)≤Real.log ((9593:ℝ)^2) ∧ Real.log ((9593:ℝ)^2)≤(22921973249/1250000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have he : Real.log ((9593:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((9593:ℝ)^2)=2*Real.log (9593:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (181:ℝ)) := by
           rw [show (9593:ℝ)=(53:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h181.1,h181.2]

theorem scale_9617 : (3668514843/200000000:ℝ)≤Real.log ((9617:ℝ)^2) ∧ Real.log ((9617:ℝ)^2)≤(11464110009/625000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have he : Real.log ((9617:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((9617:ℝ)^2)=2*Real.log (9617:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (163:ℝ)) := by
           rw [show (9617:ℝ)=(59:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h163.1,h163.2]

theorem scale_9701 : (91799836981/5000000000:ℝ)≤Real.log ((9701:ℝ)^2) ∧ Real.log ((9701:ℝ)^2)≤(91799846251/5000000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have he : Real.log ((9701:ℝ)^2)=2*(Real.log (89:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((9701:ℝ)^2)=2*Real.log (9701:ℝ) := Real.log_pow _ _
         _=2*(Real.log (89:ℝ)+Real.log (109:ℝ)) := by
           rw [show (9701:ℝ)=(89:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h109.1,h109.2]

theorem scale_9727 : (91826602541/5000000000:ℝ)≤Real.log ((9727:ℝ)^2) ∧ Real.log ((9727:ℝ)^2)≤(9182661173/500000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((9727:ℝ)^2)=2*(Real.log (71:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((9727:ℝ)^2)=2*Real.log (9727:ℝ) := Real.log_pow _ _
         _=2*(Real.log (71:ℝ)+Real.log (137:ℝ)) := by
           rw [show (9727:ℝ)=(71:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h71.1,h71.2]

theorem scale_9797 : (91898309407/5000000000:ℝ)≤Real.log ((9797:ℝ)^2) ∧ Real.log ((9797:ℝ)^2)≤(91898318689/5000000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((9797:ℝ)^2)=2*(Real.log (97:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((9797:ℝ)^2)=2*Real.log (9797:ℝ) := Real.log_pow _ _
         _=2*(Real.log (97:ℝ)+Real.log (101:ℝ)) := by
           rw [show (9797:ℝ)=(97:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h101.1,h101.2]

theorem scale_9853 : (91955307189/5000000000:ℝ)≤Real.log ((9853:ℝ)^2) ∧ Real.log ((9853:ℝ)^2)≤(9195531619/500000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have he : Real.log ((9853:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((9853:ℝ)^2)=2*Real.log (9853:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (167:ℝ)) := by
           rw [show (9853:ℝ)=(59:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h167.1,h167.2]

theorem scale_9869 : (91971532613/5000000000:ℝ)≤Real.log ((9869:ℝ)^2) ∧ Real.log ((9869:ℝ)^2)≤(22992885451/1250000000:ℝ) := by
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((9869:ℝ)^2)=2*(Real.log (71:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((9869:ℝ)^2)=2*Real.log (9869:ℝ) := Real.log_pow _ _
         _=2*(Real.log (71:ℝ)+Real.log (139:ℝ)) := by
           rw [show (9869:ℝ)=(71:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h139.1,h139.2,h71.1,h71.2]

#print axioms scale_8249
#print axioms scale_8299
#print axioms scale_8321
#print axioms scale_8357
#print axioms scale_8383
#print axioms scale_8413
#print axioms scale_8453
#print axioms scale_8471
#print axioms scale_8479
#print axioms scale_8507
#print axioms scale_8509
#print axioms scale_8549
#print axioms scale_8557
#print axioms scale_8611
#print axioms scale_8633
#print axioms scale_8639
#print axioms scale_8777
#print axioms scale_8791
#print axioms scale_8851
#print axioms scale_8881
#print axioms scale_8909
#print axioms scale_8927
#print axioms scale_8977
#print axioms scale_8989
#print axioms scale_9017
#print axioms scale_9047
#print axioms scale_9071
#print axioms scale_9089
#print axioms scale_9167
#print axioms scale_9169
#print axioms scale_9179
#print axioms scale_9211
#print axioms scale_9259
#print axioms scale_9263
#print axioms scale_9271
#print axioms scale_9301
#print axioms scale_9313
#print axioms scale_9353
#print axioms scale_9379
#print axioms scale_9487
#print axioms scale_9523
#print axioms scale_9563
#print axioms scale_9577
#print axioms scale_9593
#print axioms scale_9617
#print axioms scale_9701
#print axioms scale_9727
#print axioms scale_9797
#print axioms scale_9853
#print axioms scale_9869
end
end JSP233.ScaleLogs132
