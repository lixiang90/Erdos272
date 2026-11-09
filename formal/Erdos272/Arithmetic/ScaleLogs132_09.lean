module

public import Erdos272.Arithmetic.PrefixTable132

@[expose] public section
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_3053 : (80238795329/5000000000:ℝ)≤Real.log ((3053:ℝ)^2) ∧ Real.log ((3053:ℝ)^2)≤(16047760603/1000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((3053:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((3053:ℝ)^2)=2*Real.log (3053:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (71:ℝ)) := by
           rw [show (3053:ℝ)=(43:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h71.1,h71.2]

theorem scale_3071 : (80297581247/5000000000:ℝ)≤Real.log ((3071:ℝ)^2) ∧ Real.log ((3071:ℝ)^2)≤(80297587867/5000000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((3071:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((3071:ℝ)^2)=2*Real.log (3071:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (83:ℝ)) := by
           rw [show (3071:ℝ)=(37:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h37.1,h37.2]

theorem scale_3077 : (80317100907/5000000000:ℝ)≤Real.log ((3077:ℝ)^2) ∧ Real.log ((3077:ℝ)^2)≤(40158552847/2500000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have he : Real.log ((3077:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((3077:ℝ)^2)=2*Real.log (3077:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (181:ℝ)) := by
           rw [show (3077:ℝ)=(17:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h181.1,h181.2]

theorem scale_3097 : (251193403/15625000:ℝ)≤Real.log ((3097:ℝ)^2) ∧ Real.log ((3097:ℝ)^2)≤(80381893731/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have he : Real.log ((3097:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((3097:ℝ)^2)=2*Real.log (3097:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (163:ℝ)) := by
           rw [show (3097:ℝ)=(19:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h163.1,h163.2]

theorem scale_3103 : (20100310961/1250000000:ℝ)≤Real.log ((3103:ℝ)^2) ∧ Real.log ((3103:ℝ)^2)≤(80401248539/5000000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((3103:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((3103:ℝ)^2)=2*Real.log (3103:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (107:ℝ)) := by
           rw [show (3103:ℝ)=(29:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h29.1,h29.2]

theorem scale_3127 : (80478288621/5000000000:ℝ)≤Real.log ((3127:ℝ)^2) ∧ Real.log ((3127:ℝ)^2)≤(80478296897/5000000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((3127:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((3127:ℝ)^2)=2*Real.log (3127:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (59:ℝ)) := by
           rw [show (3127:ℝ)=(53:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h53.1,h53.2]

theorem scale_3131 : (4024553721/250000000:ℝ)≤Real.log ((3131:ℝ)^2) ∧ Real.log ((3131:ℝ)^2)≤(80491079101/5000000000:ℝ) := by
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((3131:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((3131:ℝ)^2)=2*Real.log (3131:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (101:ℝ)) := by
           rw [show (3131:ℝ)=(31:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h101.1,h101.2,h31.1,h31.2]

theorem scale_3139 : (80516590957/5000000000:ℝ)≤Real.log ((3139:ℝ)^2) ∧ Real.log ((3139:ℝ)^2)≤(16103319733/1000000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have he : Real.log ((3139:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((3139:ℝ)^2)=2*Real.log (3139:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (73:ℝ)) := by
           rw [show (3139:ℝ)=(43:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h43.1,h43.2]

theorem scale_3149 : (20137099347/1250000000:ℝ)≤Real.log ((3149:ℝ)^2) ∧ Real.log ((3149:ℝ)^2)≤(40274202723/2500000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((3149:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((3149:ℝ)^2)=2*Real.log (3149:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (67:ℝ)) := by
           rw [show (3149:ℝ)=(47:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h47.1,h47.2]

theorem scale_3151 : (80554748591/5000000000:ℝ)≤Real.log ((3151:ℝ)^2) ∧ Real.log ((3151:ℝ)^2)≤(10069344167/625000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((3151:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((3151:ℝ)^2)=2*Real.log (3151:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (137:ℝ)) := by
           rw [show (3151:ℝ)=(23:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h23.1,h23.2]

theorem scale_3161 : (80586434319/5000000000:ℝ)≤Real.log ((3161:ℝ)^2) ∧ Real.log ((3161:ℝ)^2)≤(80586439019/5000000000:ℝ) := by
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((3161:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((3161:ℝ)^2)=2*Real.log (3161:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (109:ℝ)) := by
           rw [show (3161:ℝ)=(29:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h109.1,h109.2,h29.1,h29.2]

theorem scale_3173 : (40312162537/2500000000:ℝ)≤Real.log ((3173:ℝ)^2) ∧ Real.log ((3173:ℝ)^2)≤(80624329849/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have he : Real.log ((3173:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((3173:ℝ)^2)=2*Real.log (3173:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (167:ℝ)) := by
           rw [show (3173:ℝ)=(19:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h167.1,h167.2]

theorem scale_3193 : (80687159131/5000000000:ℝ)≤Real.log ((3193:ℝ)^2) ∧ Real.log ((3193:ℝ)^2)≤(40343581909/2500000000:ℝ) := by
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((3193:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((3193:ℝ)^2)=2*Real.log (3193:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (103:ℝ)) := by
           rw [show (3193:ℝ)=(31:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h103.1,h103.2,h31.1,h31.2]

theorem scale_3197 : (80699678663/5000000000:ℝ)≤Real.log ((3197:ℝ)^2) ∧ Real.log ((3197:ℝ)^2)≤(8069968341/500000000:ℝ) := by
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((3197:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((3197:ℝ)^2)=2*Real.log (3197:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (139:ℝ)) := by
           rw [show (3197:ℝ)=(23:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h139.1,h139.2,h23.1,h23.2]

theorem scale_3233 : (80811652793/5000000000:ℝ)≤Real.log ((3233:ℝ)^2) ∧ Real.log ((3233:ℝ)^2)≤(80811661121/5000000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((3233:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((3233:ℝ)^2)=2*Real.log (3233:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (61:ℝ)) := by
           rw [show (3233:ℝ)=(53:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h53.1,h53.2]

theorem scale_3239 : (80830194729/5000000000:ℝ)≤Real.log ((3239:ℝ)^2) ∧ Real.log ((3239:ℝ)^2)≤(80830202191/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((3239:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((3239:ℝ)^2)=2*Real.log (3239:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (79:ℝ)) := by
           rw [show (3239:ℝ)=(41:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h79.1,h79.2]

theorem scale_3247 : (80854864869/5000000000:ℝ)≤Real.log ((3247:ℝ)^2) ∧ Real.log ((3247:ℝ)^2)≤(80854869667/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have he : Real.log ((3247:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((3247:ℝ)^2)=2*Real.log (3247:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (191:ℝ)) := by
           rw [show (3247:ℝ)=(17:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h191.1,h191.2]

theorem scale_3277 : (80946833679/5000000000:ℝ)≤Real.log ((3277:ℝ)^2) ∧ Real.log ((3277:ℝ)^2)≤(20236709597/1250000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((3277:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((3277:ℝ)^2)=2*Real.log (3277:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (113:ℝ)) := by
           rw [show (3277:ℝ)=(29:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h29.1,h29.2]

theorem scale_3281 : (20239758119/1250000000:ℝ)≤Real.log ((3281:ℝ)^2) ∧ Real.log ((3281:ℝ)^2)≤(20239759319/1250000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have he : Real.log ((3281:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((3281:ℝ)^2)=2*Real.log (3281:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (193:ℝ)) := by
           rw [show (3281:ℝ)=(17:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h193.1,h193.2]

theorem scale_3287 : (20244325723/1250000000:ℝ)≤Real.log ((3287:ℝ)^2) ∧ Real.log ((3287:ℝ)^2)≤(80977307673/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have he : Real.log ((3287:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((3287:ℝ)^2)=2*Real.log (3287:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (173:ℝ)) := by
           rw [show (3287:ℝ)=(19:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h173.1,h173.2]

theorem scale_3293 : (2531110589/156250000:ℝ)≤Real.log ((3293:ℝ)^2) ∧ Real.log ((3293:ℝ)^2)≤(80995545499/5000000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((3293:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((3293:ℝ)^2)=2*Real.log (3293:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (89:ℝ)) := by
           rw [show (3293:ℝ)=(37:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h37.1,h37.2]

theorem scale_3317 : (20267039397/1250000000:ℝ)≤Real.log ((3317:ℝ)^2) ∧ Real.log ((3317:ℝ)^2)≤(16213632457/1000000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((3317:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((3317:ℝ)^2)=2*Real.log (3317:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (107:ℝ)) := by
           rw [show (3317:ℝ)=(31:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h31.1,h31.2]

theorem scale_3337 : (81128269933/5000000000:ℝ)≤Real.log ((3337:ℝ)^2) ∧ Real.log ((3337:ℝ)^2)≤(16225655609/1000000000:ℝ) := by
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((3337:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((3337:ℝ)^2)=2*Real.log (3337:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (71:ℝ)) := by
           rw [show (3337:ℝ)=(47:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h71.1,h71.2,h47.1,h47.2]

theorem scale_3349 : (1268190123/78125000:ℝ)≤Real.log ((3349:ℝ)^2) ∧ Real.log ((3349:ℝ)^2)≤(81164172677/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have he : Real.log ((3349:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((3349:ℝ)^2)=2*Real.log (3349:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (197:ℝ)) := by
           rw [show (3349:ℝ)=(17:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h197.1,h197.2]

theorem scale_3379 : (81253348063/5000000000:ℝ)≤Real.log ((3379:ℝ)^2) ∧ Real.log ((3379:ℝ)^2)≤(16250670553/1000000000:ℝ) := by
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((3379:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((3379:ℝ)^2)=2*Real.log (3379:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (109:ℝ)) := by
           rw [show (3379:ℝ)=(31:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h109.1,h109.2,h31.1,h31.2]

theorem scale_3383 : (81265178831/5000000000:ℝ)≤Real.log ((3383:ℝ)^2) ∧ Real.log ((3383:ℝ)^2)≤(40632591819/2500000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have he : Real.log ((3383:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((3383:ℝ)^2)=2*Real.log (3383:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (199:ℝ)) := by
           rw [show (3383:ℝ)=(17:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h199.1,h199.2]

theorem scale_3397 : (508165469/31250000:ℝ)≤Real.log ((3397:ℝ)^2) ∧ Real.log ((3397:ℝ)^2)≤(203266207/12500000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((3397:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((3397:ℝ)^2)=2*Real.log (3397:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (79:ℝ)) := by
           rw [show (3397:ℝ)=(43:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h79.1,h79.2]

theorem scale_3401 : (20329561251/1250000000:ℝ)≤Real.log ((3401:ℝ)^2) ∧ Real.log ((3401:ℝ)^2)≤(81318249791/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have he : Real.log ((3401:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((3401:ℝ)^2)=2*Real.log (3401:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (179:ℝ)) := by
           rw [show (3401:ℝ)=(19:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h179.1,h179.2]

theorem scale_3403 : (81324122267/5000000000:ℝ)≤Real.log ((3403:ℝ)^2) ∧ Real.log ((3403:ℝ)^2)≤(20331032439/1250000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have he : Real.log ((3403:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((3403:ℝ)^2)=2*Real.log (3403:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (83:ℝ)) := by
           rw [show (3403:ℝ)=(41:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h83.1,h83.2]

theorem scale_3427 : (5087150149/312500000:ℝ)≤Real.log ((3427:ℝ)^2) ∧ Real.log ((3427:ℝ)^2)≤(40697203571/2500000000:ℝ) := by
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((3427:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((3427:ℝ)^2)=2*Real.log (3427:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (149:ℝ)) := by
           rw [show (3427:ℝ)=(23:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h149.1,h149.2,h23.1,h23.2]

theorem scale_3431 : (81406065561/5000000000:ℝ)≤Real.log ((3431:ℝ)^2) ∧ Real.log ((3431:ℝ)^2)≤(16281214739/1000000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((3431:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((3431:ℝ)^2)=2*Real.log (3431:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (73:ℝ)) := by
           rw [show (3431:ℝ)=(47:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h47.1,h47.2]

theorem scale_3439 : (81429357257/5000000000:ℝ)≤Real.log ((3439:ℝ)^2) ∧ Real.log ((3439:ℝ)^2)≤(40714681023/2500000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have he : Real.log ((3439:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((3439:ℝ)^2)=2*Real.log (3439:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (181:ℝ)) := by
           rw [show (3439:ℝ)=(19:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h181.1,h181.2]

theorem scale_3473 : (20381934423/1250000000:ℝ)≤Real.log ((3473:ℝ)^2) ∧ Real.log ((3473:ℝ)^2)≤(20381935613/1250000000:ℝ) := by
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((3473:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((3473:ℝ)^2)=2*Real.log (3473:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (151:ℝ)) := by
           rw [show (3473:ℝ)=(23:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h151.1,h151.2,h23.1,h23.2]

theorem scale_3503 : (81613747423/5000000000:ℝ)≤Real.log ((3503:ℝ)^2) ∧ Real.log ((3503:ℝ)^2)≤(40806876067/2500000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((3503:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((3503:ℝ)^2)=2*Real.log (3503:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (113:ℝ)) := by
           rw [show (3503:ℝ)=(31:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h31.1,h31.2]

theorem scale_3551 : (20437460069/1250000000:ℝ)≤Real.log ((3551:ℝ)^2) ∧ Real.log ((3551:ℝ)^2)≤(1021873109/62500000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((3551:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((3551:ℝ)^2)=2*Real.log (3551:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (67:ℝ)) := by
           rw [show (3551:ℝ)=(53:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h53.1,h53.2]

theorem scale_3569 : (40900201289/2500000000:ℝ)≤Real.log ((3569:ℝ)^2) ∧ Real.log ((3569:ℝ)^2)≤(16360082073/1000000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have he : Real.log ((3569:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((3569:ℝ)^2)=2*Real.log (3569:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (83:ℝ)) := by
           rw [show (3569:ℝ)=(43:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h43.1,h43.2]

theorem scale_3589 : (81856284917/5000000000:ℝ)≤Real.log ((3589:ℝ)^2) ∧ Real.log ((3589:ℝ)^2)≤(81856291601/5000000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((3589:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((3589:ℝ)^2)=2*Real.log (3589:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (97:ℝ)) := by
           rw [show (3589:ℝ)=(37:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h37.1,h37.2]

theorem scale_3599 : (20471026991/1250000000:ℝ)≤Real.log ((3599:ℝ)^2) ∧ Real.log ((3599:ℝ)^2)≤(2558878641/156250000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((3599:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((3599:ℝ)^2)=2*Real.log (3599:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (61:ℝ)) := by
           rw [show (3599:ℝ)=(59:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h61.1,h61.2]

theorem scale_3611 : (40958698687/2500000000:ℝ)≤Real.log ((3611:ℝ)^2) ∧ Real.log ((3611:ℝ)^2)≤(40958701071/2500000000:ℝ) := by
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((3611:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((3611:ℝ)^2)=2*Real.log (3611:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (157:ℝ)) := by
           rw [show (3611:ℝ)=(23:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h157.1,h157.2,h23.1,h23.2]

theorem scale_3629 : (81967121219/5000000000:ℝ)≤Real.log ((3629:ℝ)^2) ∧ Real.log ((3629:ℝ)^2)≤(81967126019/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have he : Real.log ((3629:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((3629:ℝ)^2)=2*Real.log (3629:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (191:ℝ)) := by
           rw [show (3629:ℝ)=(19:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h191.1,h191.2]

theorem scale_3649 : (20505519967/1250000000:ℝ)≤Real.log ((3649:ℝ)^2) ∧ Real.log ((3649:ℝ)^2)≤(20505521847/1250000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have he : Real.log ((3649:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((3649:ℝ)^2)=2*Real.log (3649:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (89:ℝ)) := by
           rw [show (3649:ℝ)=(41:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h41.1,h41.2]

theorem scale_3667 : (41035644413/2500000000:ℝ)≤Real.log ((3667:ℝ)^2) ∧ Real.log ((3667:ℝ)^2)≤(20517823407/1250000000:ℝ) := by
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((3667:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((3667:ℝ)^2)=2*Real.log (3667:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (193:ℝ)) := by
           rw [show (3667:ℝ)=(19:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h193.1,h193.2,h19.1,h19.2]

theorem scale_3683 : (41057413171/2500000000:ℝ)≤Real.log ((3683:ℝ)^2) ∧ Real.log ((3683:ℝ)^2)≤(41057415539/2500000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((3683:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((3683:ℝ)^2)=2*Real.log (3683:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (127:ℝ)) := by
           rw [show (3683:ℝ)=(29:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h29.1,h29.2,h127.1,h127.2]

theorem scale_3713 : (20548987411/1250000000:ℝ)≤Real.log ((3713:ℝ)^2) ∧ Real.log ((3713:ℝ)^2)≤(8219595783/500000000:ℝ) := by
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((3713:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((3713:ℝ)^2)=2*Real.log (3713:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (79:ℝ)) := by
           rw [show (3713:ℝ)=(47:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h79.1,h79.2,h47.1,h47.2]

theorem scale_3737 : (41130190147/2500000000:ℝ)≤Real.log ((3737:ℝ)^2) ∧ Real.log ((3737:ℝ)^2)≤(8226038699/500000000:ℝ) := by
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((3737:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((3737:ℝ)^2)=2*Real.log (3737:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (101:ℝ)) := by
           rw [show (3737:ℝ)=(37:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h101.1,h101.2,h37.1,h37.2]

theorem scale_3743 : (41138212111/2500000000:ℝ)≤Real.log ((3743:ℝ)^2) ∧ Real.log ((3743:ℝ)^2)≤(82276429029/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have he : Real.log ((3743:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((3743:ℝ)^2)=2*Real.log (3743:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (197:ℝ)) := by
           rw [show (3743:ℝ)=(19:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h197.1,h197.2]

theorem scale_3749 : (3291697653/200000000:ℝ)≤Real.log ((3749:ℝ)^2) ∧ Real.log ((3749:ℝ)^2)≤(822924461/50000000:ℝ) := by
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((3749:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((3749:ℝ)^2)=2*Real.log (3749:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (163:ℝ)) := by
           rw [show (3749:ℝ)=(23:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h163.1,h163.2,h23.1,h23.2]

theorem scale_3763 : (82329712821/5000000000:ℝ)≤Real.log ((3763:ℝ)^2) ∧ Real.log ((3763:ℝ)^2)≤(82329721319/5000000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((3763:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((3763:ℝ)^2)=2*Real.log (3763:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (71:ℝ)) := by
           rw [show (3763:ℝ)=(53:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h71.1,h71.2]

theorem scale_3781 : (82377435181/5000000000:ℝ)≤Real.log ((3781:ℝ)^2) ∧ Real.log ((3781:ℝ)^2)≤(8237743999/500000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have he : Real.log ((3781:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((3781:ℝ)^2)=2*Real.log (3781:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (199:ℝ)) := by
           rw [show (3781:ℝ)=(19:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h199.1,h199.2]

theorem scale_3799 : (82424928707/5000000000:ℝ)≤Real.log ((3799:ℝ)^2) ∧ Real.log ((3799:ℝ)^2)≤(10303116681/625000000:ℝ) := by
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((3799:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((3799:ℝ)^2)=2*Real.log (3799:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (131:ℝ)) := by
           rw [show (3799:ℝ)=(29:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h131.1,h131.2,h29.1,h29.2]

#print axioms scale_3053
#print axioms scale_3071
#print axioms scale_3077
#print axioms scale_3097
#print axioms scale_3103
#print axioms scale_3127
#print axioms scale_3131
#print axioms scale_3139
#print axioms scale_3149
#print axioms scale_3151
#print axioms scale_3161
#print axioms scale_3173
#print axioms scale_3193
#print axioms scale_3197
#print axioms scale_3233
#print axioms scale_3239
#print axioms scale_3247
#print axioms scale_3277
#print axioms scale_3281
#print axioms scale_3287
#print axioms scale_3293
#print axioms scale_3317
#print axioms scale_3337
#print axioms scale_3349
#print axioms scale_3379
#print axioms scale_3383
#print axioms scale_3397
#print axioms scale_3401
#print axioms scale_3403
#print axioms scale_3427
#print axioms scale_3431
#print axioms scale_3439
#print axioms scale_3473
#print axioms scale_3503
#print axioms scale_3551
#print axioms scale_3569
#print axioms scale_3589
#print axioms scale_3599
#print axioms scale_3611
#print axioms scale_3629
#print axioms scale_3649
#print axioms scale_3667
#print axioms scale_3683
#print axioms scale_3713
#print axioms scale_3737
#print axioms scale_3743
#print axioms scale_3749
#print axioms scale_3763
#print axioms scale_3781
#print axioms scale_3799
end
end JSP233.ScaleLogs132
