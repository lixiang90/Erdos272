import Erdos272.Arithmetic.PrefixTable132
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_3811 : (16491293001/1000000000:ℝ)≤Real.log ((3811:ℝ)^2) ∧ Real.log ((3811:ℝ)^2)≤(82456471707/5000000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((3811:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((3811:ℝ)^2)=2*Real.log (3811:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (103:ℝ)) := by
           rw [show (3811:ℝ)=(37:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h103.1,h103.2]

theorem scale_3827 : (82498360179/5000000000:ℝ)≤Real.log ((3827:ℝ)^2) ∧ Real.log ((3827:ℝ)^2)≤(82498367997/5000000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have he : Real.log ((3827:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((3827:ℝ)^2)=2*Real.log (3827:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (89:ℝ)) := by
           rw [show (3827:ℝ)=(43:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h43.1,h43.2]

theorem scale_3841 : (82534877439/5000000000:ℝ)≤Real.log ((3841:ℝ)^2) ∧ Real.log ((3841:ℝ)^2)≤(41267441109/2500000000:ℝ) := by
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((3841:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((3841:ℝ)^2)=2*Real.log (3841:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (167:ℝ)) := by
           rw [show (3841:ℝ)=(23:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h167.1,h167.2,h23.1,h23.2]

theorem scale_3869 : (82607508449/5000000000:ℝ)≤Real.log ((3869:ℝ)^2) ∧ Real.log ((3869:ℝ)^2)≤(82607516969/5000000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((3869:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((3869:ℝ)^2)=2*Real.log (3869:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (73:ℝ)) := by
           rw [show (3869:ℝ)=(53:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h53.1,h53.2]

theorem scale_3901 : (41344938591/2500000000:ℝ)≤Real.log ((3901:ℝ)^2) ∧ Real.log ((3901:ℝ)^2)≤(16537977079/1000000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((3901:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((3901:ℝ)^2)=2*Real.log (3901:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (83:ℝ)) := by
           rw [show (3901:ℝ)=(47:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h47.1,h47.2]

theorem scale_3937 : (41390870043/2500000000:ℝ)≤Real.log ((3937:ℝ)^2) ∧ Real.log ((3937:ℝ)^2)≤(10347718103/625000000:ℝ) := by
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((3937:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((3937:ℝ)^2)=2*Real.log (3937:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (127:ℝ)) := by
           rw [show (3937:ℝ)=(31:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h127.1,h127.2,h31.1,h31.2]

theorem scale_3953 : (82822295447/5000000000:ℝ)≤Real.log ((3953:ℝ)^2) ∧ Real.log ((3953:ℝ)^2)≤(82822304111/5000000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have he : Real.log ((3953:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((3953:ℝ)^2)=2*Real.log (3953:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (67:ℝ)) := by
           rw [show (3953:ℝ)=(59:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h59.1,h59.2]

theorem scale_3959 : (41418731731/2500000000:ℝ)≤Real.log ((3959:ℝ)^2) ∧ Real.log ((3959:ℝ)^2)≤(41418735087/2500000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((3959:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((3959:ℝ)^2)=2*Real.log (3959:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (107:ℝ)) := by
           rw [show (3959:ℝ)=(37:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h37.1,h37.2]

theorem scale_3973 : (82872764729/5000000000:ℝ)≤Real.log ((3973:ℝ)^2) ∧ Real.log ((3973:ℝ)^2)≤(2071819237/125000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((3973:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((3973:ℝ)^2)=2*Real.log (3973:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (137:ℝ)) := by
           rw [show (3973:ℝ)=(29:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h29.1,h29.2]

theorem scale_3977 : (82882825937/5000000000:ℝ)≤Real.log ((3977:ℝ)^2) ∧ Real.log ((3977:ℝ)^2)≤(8288283349/500000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have he : Real.log ((3977:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((3977:ℝ)^2)=2*Real.log (3977:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (97:ℝ)) := by
           rw [show (3977:ℝ)=(41:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h97.1,h97.2]

theorem scale_3979 : (82887855257/5000000000:ℝ)≤Real.log ((3979:ℝ)^2) ∧ Real.log ((3979:ℝ)^2)≤(41443930021/2500000000:ℝ) := by
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((3979:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((3979:ℝ)^2)=2*Real.log (3979:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (173:ℝ)) := by
           rw [show (3979:ℝ)=(23:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h173.1,h173.2,h23.1,h23.2]

theorem scale_4031 : (83017694801/5000000000:ℝ)≤Real.log ((4031:ℝ)^2) ∧ Real.log ((4031:ℝ)^2)≤(41508849777/2500000000:ℝ) := by
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((4031:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((4031:ℝ)^2)=2*Real.log (4031:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (139:ℝ)) := by
           rw [show (4031:ℝ)=(29:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h139.1,h139.2,h29.1,h29.2]

theorem scale_4033 : (83022653937/5000000000:ℝ)≤Real.log ((4033:ℝ)^2) ∧ Real.log ((4033:ℝ)^2)≤(41511330327/2500000000:ℝ) := by
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((4033:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((4033:ℝ)^2)=2*Real.log (4033:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (109:ℝ)) := by
           rw [show (4033:ℝ)=(37:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h109.1,h109.2,h37.1,h37.2]

theorem scale_4061 : (83091842451/5000000000:ℝ)≤Real.log ((4061:ℝ)^2) ∧ Real.log ((4061:ℝ)^2)≤(41545923597/2500000000:ℝ) := by
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((4061:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((4061:ℝ)^2)=2*Real.log (4061:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (131:ℝ)) := by
           rw [show (4061:ℝ)=(31:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h131.1,h131.2,h31.1,h31.2]

theorem scale_4087 : (83155659619/5000000000:ℝ)≤Real.log ((4087:ℝ)^2) ∧ Real.log ((4087:ℝ)^2)≤(16631133667/1000000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((4087:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((4087:ℝ)^2)=2*Real.log (4087:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (67:ℝ)) := by
           rw [show (4087:ℝ)=(61:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h61.1,h61.2]

theorem scale_4117 : (83228797369/5000000000:ℝ)≤Real.log ((4117:ℝ)^2) ∧ Real.log ((4117:ℝ)^2)≤(1040360027/62500000:ℝ) := by
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((4117:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((4117:ℝ)^2)=2*Real.log (4117:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (179:ℝ)) := by
           rw [show (4117:ℝ)=(23:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h179.1,h179.2,h23.1,h23.2]

theorem scale_4141 : (41643460657/2500000000:ℝ)≤Real.log ((4141:ℝ)^2) ∧ Real.log ((4141:ℝ)^2)≤(83286928879/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((4141:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((4141:ℝ)^2)=2*Real.log (4141:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (101:ℝ)) := by
           rw [show (4141:ℝ)=(41:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h101.1,h101.2]

theorem scale_4163 : (41669954811/2500000000:ℝ)≤Real.log ((4163:ℝ)^2) ∧ Real.log ((4163:ℝ)^2)≤(16667982883/1000000000:ℝ) := by
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((4163:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((4163:ℝ)^2)=2*Real.log (4163:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (181:ℝ)) := by
           rw [show (4163:ℝ)=(23:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h181.1,h181.2,h23.1,h23.2]

theorem scale_4171 : (10419888281/625000000:ℝ)≤Real.log ((4171:ℝ)^2) ∧ Real.log ((4171:ℝ)^2)≤(83359114099/5000000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have he : Real.log ((4171:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((4171:ℝ)^2)=2*Real.log (4171:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (97:ℝ)) := by
           rw [show (4171:ℝ)=(43:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h43.1,h43.2]

theorem scale_4181 : (83383053297/5000000000:ℝ)≤Real.log ((4181:ℝ)^2) ∧ Real.log ((4181:ℝ)^2)≤(83383060023/5000000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((4181:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((4181:ℝ)^2)=2*Real.log (4181:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (113:ℝ)) := by
           rw [show (4181:ℝ)=(37:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h37.1,h37.2]

theorem scale_4183 : (83387834783/5000000000:ℝ)≤Real.log ((4183:ℝ)^2) ∧ Real.log ((4183:ℝ)^2)≤(83387843027/5000000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((4183:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((4183:ℝ)^2)=2*Real.log (4183:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (89:ℝ)) := by
           rw [show (4183:ℝ)=(47:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h47.1,h47.2]

theorem scale_4187 : (20849348133/1250000000:ℝ)≤Real.log ((4187:ℝ)^2) ∧ Real.log ((4187:ℝ)^2)≤(5212337569/312500000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((4187:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((4187:ℝ)^2)=2*Real.log (4187:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (79:ℝ)) := by
           rw [show (4187:ℝ)=(53:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h79.1,h79.2]

theorem scale_4189 : (10425270999/625000000:ℝ)≤Real.log ((4189:ℝ)^2) ∧ Real.log ((4189:ℝ)^2)≤(8340217671/500000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((4189:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((4189:ℝ)^2)=2*Real.log (4189:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (71:ℝ)) := by
           rw [show (4189:ℝ)=(59:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h71.1,h71.2]

theorem scale_4223 : (3339320241/200000000:ℝ)≤Real.log ((4223:ℝ)^2) ∧ Real.log ((4223:ℝ)^2)≤(20870753399/1250000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((4223:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((4223:ℝ)^2)=2*Real.log (4223:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (103:ℝ)) := by
           rw [show (4223:ℝ)=(41:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h103.1,h103.2]

theorem scale_4247 : (83539678473/5000000000:ℝ)≤Real.log ((4247:ℝ)^2) ∧ Real.log ((4247:ℝ)^2)≤(41769841613/2500000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((4247:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((4247:ℝ)^2)=2*Real.log (4247:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (137:ℝ)) := by
           rw [show (4247:ℝ)=(31:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h31.1,h31.2]

theorem scale_4307 : (4183998181/250000000:ℝ)≤Real.log ((4307:ℝ)^2) ∧ Real.log ((4307:ℝ)^2)≤(2091999309/125000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have he : Real.log ((4307:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((4307:ℝ)^2)=2*Real.log (4307:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (73:ℝ)) := by
           rw [show (4307:ℝ)=(59:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h59.1,h59.2]

theorem scale_4309 : (16736921709/1000000000:ℝ)≤Real.log ((4309:ℝ)^2) ∧ Real.log ((4309:ℝ)^2)≤(836846133/50000000:ℝ) := by
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((4309:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((4309:ℝ)^2)=2*Real.log (4309:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (139:ℝ)) := by
           rw [show (4309:ℝ)=(31:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h139.1,h139.2,h31.1,h31.2]

theorem scale_4321 : (41856209261/2500000000:ℝ)≤Real.log ((4321:ℝ)^2) ∧ Real.log ((4321:ℝ)^2)≤(41856211643/2500000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((4321:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((4321:ℝ)^2)=2*Real.log (4321:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (149:ℝ)) := by
           rw [show (4321:ℝ)=(29:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h29.1,h29.2,h149.1,h149.2]

theorem scale_4331 : (20933883041/1250000000:ℝ)≤Real.log ((4331:ℝ)^2) ∧ Real.log ((4331:ℝ)^2)≤(41867770467/2500000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((4331:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((4331:ℝ)^2)=2*Real.log (4331:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (71:ℝ)) := by
           rw [show (4331:ℝ)=(61:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h71.1,h71.2]

theorem scale_4343 : (670105613/40000000:ℝ)≤Real.log ((4343:ℝ)^2) ∧ Real.log ((4343:ℝ)^2)≤(5235200593/312500000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((4343:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((4343:ℝ)^2)=2*Real.log (4343:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (101:ℝ)) := by
           rw [show (4343:ℝ)=(43:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h101.1,h101.2]

theorem scale_4379 : (8384575383/500000000:ℝ)≤Real.log ((4379:ℝ)^2) ∧ Real.log ((4379:ℝ)^2)≤(20961439649/1250000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((4379:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((4379:ℝ)^2)=2*Real.log (4379:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (151:ℝ)) := by
           rw [show (4379:ℝ)=(29:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h29.1,h29.2,h151.1,h151.2]

theorem scale_4387 : (41932002241/2500000000:ℝ)≤Real.log ((4387:ℝ)^2) ∧ Real.log ((4387:ℝ)^2)≤(83864012063/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have he : Real.log ((4387:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((4387:ℝ)^2)=2*Real.log (4387:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (107:ℝ)) := by
           rw [show (4387:ℝ)=(41:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h107.1,h107.2]

theorem scale_4393 : (5242354599/312500000:ℝ)≤Real.log ((4393:ℝ)^2) ∧ Real.log ((4393:ℝ)^2)≤(20969419597/1250000000:ℝ) := by
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((4393:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((4393:ℝ)^2)=2*Real.log (4393:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (191:ℝ)) := by
           rw [show (4393:ℝ)=(23:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h191.1,h191.2,h23.1,h23.2]

theorem scale_4399 : (8389132007/500000000:ℝ)≤Real.log ((4399:ℝ)^2) ∧ Real.log ((4399:ℝ)^2)≤(83891328669/5000000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((4399:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((4399:ℝ)^2)=2*Real.log (4399:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (83:ℝ)) := by
           rw [show (4399:ℝ)=(53:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h53.1,h53.2]

theorem scale_4429 : (1311863849/78125000:ℝ)≤Real.log ((4429:ℝ)^2) ∧ Real.log ((4429:ℝ)^2)≤(16791858841/1000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((4429:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((4429:ℝ)^2)=2*Real.log (4429:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (103:ℝ)) := by
           rw [show (4429:ℝ)=(43:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h103.1,h103.2]

theorem scale_4439 : (83981841191/5000000000:ℝ)≤Real.log ((4439:ℝ)^2) ∧ Real.log ((4439:ℝ)^2)≤(83981845997/5000000000:ℝ) := by
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((4439:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((4439:ℝ)^2)=2*Real.log (4439:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (193:ℝ)) := by
           rw [show (4439:ℝ)=(23:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h193.1,h193.2,h23.1,h23.2]

theorem scale_4453 : (5250832987/312500000:ℝ)≤Real.log ((4453:ℝ)^2) ∧ Real.log ((4453:ℝ)^2)≤(10501667073/625000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((4453:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((4453:ℝ)^2)=2*Real.log (4453:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (73:ℝ)) := by
           rw [show (4453:ℝ)=(61:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h61.1,h61.2]

theorem scale_4469 : (84049194957/5000000000:ℝ)≤Real.log ((4469:ℝ)^2) ∧ Real.log ((4469:ℝ)^2)≤(84049202543/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have he : Real.log ((4469:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((4469:ℝ)^2)=2*Real.log (4469:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (109:ℝ)) := by
           rw [show (4469:ℝ)=(41:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h109.1,h109.2]

theorem scale_4531 : (84186976587/5000000000:ℝ)≤Real.log ((4531:ℝ)^2) ∧ Real.log ((4531:ℝ)^2)≤(42093490699/2500000000:ℝ) := by
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((4531:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((4531:ℝ)^2)=2*Real.log (4531:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (197:ℝ)) := by
           rw [show (4531:ℝ)=(23:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h197.1,h197.2,h23.1,h23.2]

theorem scale_4553 : (10529426689/625000000:ℝ)≤Real.log ((4553:ℝ)^2) ∧ Real.log ((4553:ℝ)^2)≤(42117709143/2500000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((4553:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((4553:ℝ)^2)=2*Real.log (4553:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (157:ℝ)) := by
           rw [show (4553:ℝ)=(29:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h29.1,h29.2,h157.1,h157.2]

theorem scale_4559 : (21062145213/1250000000:ℝ)≤Real.log ((4559:ℝ)^2) ∧ Real.log ((4559:ℝ)^2)≤(84248589129/5000000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((4559:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((4559:ℝ)^2)=2*Real.log (4559:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (97:ℝ)) := by
           rw [show (4559:ℝ)=(47:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h47.1,h47.2]

theorem scale_4577 : (42143993773/2500000000:ℝ)≤Real.log ((4577:ℝ)^2) ∧ Real.log ((4577:ℝ)^2)≤(84287992359/5000000000:ℝ) := by
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((4577:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((4577:ℝ)^2)=2*Real.log (4577:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (199:ℝ)) := by
           rw [show (4577:ℝ)=(23:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h199.1,h199.2,h23.1,h23.2]

theorem scale_4601 : (84340284793/5000000000:ℝ)≤Real.log ((4601:ℝ)^2) ∧ Real.log ((4601:ℝ)^2)≤(1317817073/78125000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have he : Real.log ((4601:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((4601:ℝ)^2)=2*Real.log (4601:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (107:ℝ)) := by
           rw [show (4601:ℝ)=(43:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h43.1,h43.2]

theorem scale_4619 : (42189666133/2500000000:ℝ)≤Real.log ((4619:ℝ)^2) ∧ Real.log ((4619:ℝ)^2)≤(10547417129/625000000:ℝ) := by
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((4619:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((4619:ℝ)^2)=2*Real.log (4619:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (149:ℝ)) := by
           rw [show (4619:ℝ)=(31:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h149.1,h149.2,h31.1,h31.2]

theorem scale_4633 : (84409594317/5000000000:ℝ)≤Real.log ((4633:ℝ)^2) ∧ Real.log ((4633:ℝ)^2)≤(10551200239/625000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have he : Real.log ((4633:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((4633:ℝ)^2)=2*Real.log (4633:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (113:ℝ)) := by
           rw [show (4633:ℝ)=(41:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h113.1,h113.2]

theorem scale_4661 : (84469847703/5000000000:ℝ)≤Real.log ((4661:ℝ)^2) ∧ Real.log ((4661:ℝ)^2)≤(16893971299/1000000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((4661:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((4661:ℝ)^2)=2*Real.log (4661:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (79:ℝ)) := by
           rw [show (4661:ℝ)=(59:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h79.1,h79.2]

theorem scale_4681 : (42256333787/2500000000:ℝ)≤Real.log ((4681:ℝ)^2) ∧ Real.log ((4681:ℝ)^2)≤(42256336171/2500000000:ℝ) := by
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((4681:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((4681:ℝ)^2)=2*Real.log (4681:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (151:ℝ)) := by
           rw [show (4681:ℝ)=(31:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h151.1,h151.2,h31.1,h31.2]

theorem scale_4687 : (21131368817/1250000000:ℝ)≤Real.log ((4687:ℝ)^2) ∧ Real.log ((4687:ℝ)^2)≤(5282842697/312500000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have he : Real.log ((4687:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((4687:ℝ)^2)=2*Real.log (4687:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (109:ℝ)) := by
           rw [show (4687:ℝ)=(43:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h109.1,h109.2]

theorem scale_4699 : (2113776149/125000000:ℝ)≤Real.log ((4699:ℝ)^2) ∧ Real.log ((4699:ℝ)^2)≤(84551052713/5000000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((4699:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((4699:ℝ)^2)=2*Real.log (4699:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (127:ℝ)) := by
           rw [show (4699:ℝ)=(37:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h127.1,h127.2]

theorem scale_4717 : (84589277671/5000000000:ℝ)≤Real.log ((4717:ℝ)^2) ∧ Real.log ((4717:ℝ)^2)≤(84589286301/5000000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((4717:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((4717:ℝ)^2)=2*Real.log (4717:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (89:ℝ)) := by
           rw [show (4717:ℝ)=(53:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h53.1,h53.2]

#print axioms scale_3811
#print axioms scale_3827
#print axioms scale_3841
#print axioms scale_3869
#print axioms scale_3901
#print axioms scale_3937
#print axioms scale_3953
#print axioms scale_3959
#print axioms scale_3973
#print axioms scale_3977
#print axioms scale_3979
#print axioms scale_4031
#print axioms scale_4033
#print axioms scale_4061
#print axioms scale_4087
#print axioms scale_4117
#print axioms scale_4141
#print axioms scale_4163
#print axioms scale_4171
#print axioms scale_4181
#print axioms scale_4183
#print axioms scale_4187
#print axioms scale_4189
#print axioms scale_4223
#print axioms scale_4247
#print axioms scale_4307
#print axioms scale_4309
#print axioms scale_4321
#print axioms scale_4331
#print axioms scale_4343
#print axioms scale_4379
#print axioms scale_4387
#print axioms scale_4393
#print axioms scale_4399
#print axioms scale_4429
#print axioms scale_4439
#print axioms scale_4453
#print axioms scale_4469
#print axioms scale_4531
#print axioms scale_4553
#print axioms scale_4559
#print axioms scale_4577
#print axioms scale_4601
#print axioms scale_4619
#print axioms scale_4633
#print axioms scale_4661
#print axioms scale_4681
#print axioms scale_4687
#print axioms scale_4699
#print axioms scale_4717
end
end JSP233.ScaleLogs132
