module

public import Erdos272.Arithmetic.PrefixTable132

@[expose] public section
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_1 : 0≤Real.log ((1:ℝ)^2) ∧ Real.log ((1:ℝ)^2)≤0 := by
  norm_num

theorem scale_2 : (6931471803/5000000000:ℝ)≤Real.log ((2:ℝ)^2) ∧ Real.log ((2:ℝ)^2)≤(108304247/78125000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have he : Real.log ((2:ℝ)^2)=2*(Real.log (2:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h2.1,h2.2]

theorem scale_3 : (2746530721/1250000000:ℝ)≤Real.log ((3:ℝ)^2) ∧ Real.log ((3:ℝ)^2)≤(1098612289/500000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((3:ℝ)^2)=2*(Real.log (3:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h3.1,h3.2]

theorem scale_5 : (16094379121/5000000000:ℝ)≤Real.log ((5:ℝ)^2) ∧ Real.log ((5:ℝ)^2)≤(16094379129/5000000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((5:ℝ)^2)=2*(Real.log (5:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h5.1,h5.2]

theorem scale_6 : (17917594687/5000000000:ℝ)≤Real.log ((6:ℝ)^2) ∧ Real.log ((6:ℝ)^2)≤(8958797349/2500000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((6:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (3:ℝ)) := by
    calc Real.log ((6:ℝ)^2)=2*Real.log (6:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (3:ℝ)) := by
           rw [show (6:ℝ)=(2:ℝ)*(3:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h3.1,h3.2]

theorem scale_7 : (9729550743/2500000000:ℝ)≤Real.log ((7:ℝ)^2) ∧ Real.log ((7:ℝ)^2)≤(2432387687/625000000:ℝ) := by
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((7:ℝ)^2)=2*(Real.log (7:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h7.1,h7.2]

theorem scale_10 : (5756462731/1250000000:ℝ)≤Real.log ((10:ℝ)^2) ∧ Real.log ((10:ℝ)^2)≤(23025850937/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((10:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (5:ℝ)) := by
    calc Real.log ((10:ℝ)^2)=2*Real.log (10:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (5:ℝ)) := by
           rw [show (10:ℝ)=(2:ℝ)*(5:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h5.1,h5.2]

theorem scale_11 : (11989476361/2500000000:ℝ)≤Real.log ((11:ℝ)^2) ∧ Real.log ((11:ℝ)^2)≤(749342273/156250000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((11:ℝ)^2)=2*(Real.log (11:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h11.1,h11.2]

theorem scale_13 : (25649493567/5000000000:ℝ)≤Real.log ((13:ℝ)^2) ∧ Real.log ((13:ℝ)^2)≤(25649493583/5000000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((13:ℝ)^2)=2*(Real.log (13:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h13.1,h13.2]

theorem scale_14 : (26390573289/5000000000:ℝ)≤Real.log ((14:ℝ)^2) ∧ Real.log ((14:ℝ)^2)≤(3298821663/625000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((14:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (7:ℝ)) := by
    calc Real.log ((14:ℝ)^2)=2*Real.log (14:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (7:ℝ)) := by
           rw [show (14:ℝ)=(2:ℝ)*(7:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h7.1,h7.2]

theorem scale_15 : (5416100401/1000000000:ℝ)≤Real.log ((15:ℝ)^2) ∧ Real.log ((15:ℝ)^2)≤(27080502019/5000000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((15:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (5:ℝ)) := by
    calc Real.log ((15:ℝ)^2)=2*Real.log (15:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (5:ℝ)) := by
           rw [show (15:ℝ)=(3:ℝ)*(5:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h5.1,h5.2]

theorem scale_17 : (28332133431/5000000000:ℝ)≤Real.log ((17:ℝ)^2) ∧ Real.log ((17:ℝ)^2)≤(28332133451/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have he : Real.log ((17:ℝ)^2)=2*(Real.log (17:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h17.1,h17.2]

theorem scale_19 : (29444389781/5000000000:ℝ)≤Real.log ((19:ℝ)^2) ∧ Real.log ((19:ℝ)^2)≤(29444389803/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((19:ℝ)^2)=2*(Real.log (19:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h19.1,h19.2]

theorem scale_21 : (3044522437/500000000:ℝ)≤Real.log ((21:ℝ)^2) ∧ Real.log ((21:ℝ)^2)≤(15222612193/2500000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((21:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (7:ℝ)) := by
    calc Real.log ((21:ℝ)^2)=2*Real.log (21:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (7:ℝ)) := by
           rw [show (21:ℝ)=(3:ℝ)*(7:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h7.1,h7.2]

theorem scale_22 : (1236416981/200000000:ℝ)≤Real.log ((22:ℝ)^2) ∧ Real.log ((22:ℝ)^2)≤(965950767/156250000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((22:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (11:ℝ)) := by
    calc Real.log ((22:ℝ)^2)=2*Real.log (22:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (11:ℝ)) := by
           rw [show (22:ℝ)=(2:ℝ)*(11:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h11.1,h11.2]

theorem scale_23 : (15677471073/2500000000:ℝ)≤Real.log ((23:ℝ)^2) ∧ Real.log ((23:ℝ)^2)≤(7838735543/1250000000:ℝ) := by
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((23:ℝ)^2)=2*(Real.log (23:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h23.1,h23.2]

theorem scale_26 : (3258096537/500000000:ℝ)≤Real.log ((26:ℝ)^2) ∧ Real.log ((26:ℝ)^2)≤(32580965391/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((26:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (13:ℝ)) := by
    calc Real.log ((26:ℝ)^2)=2*Real.log (26:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (13:ℝ)) := by
           rw [show (26:ℝ)=(2:ℝ)*(13:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h13.1,h13.2]

theorem scale_29 : (8418239571/1250000000:ℝ)≤Real.log ((29:ℝ)^2) ∧ Real.log ((29:ℝ)^2)≤(8418239579/1250000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((29:ℝ)^2)=2*(Real.log (29:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h29.1,h29.2]

theorem scale_30 : (2125748363/312500000:ℝ)≤Real.log ((30:ℝ)^2) ∧ Real.log ((30:ℝ)^2)≤(34011973827/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((30:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (3:ℝ)+Real.log (5:ℝ)) := by
    calc Real.log ((30:ℝ)^2)=2*Real.log (30:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (3:ℝ)+Real.log (5:ℝ)) := by
           rw [show (30:ℝ)=(2:ℝ)*(3:ℝ)*(5:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num),Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h3.1,h3.2,h5.1,h5.2]

theorem scale_31 : (8584968007/1250000000:ℝ)≤Real.log ((31:ℝ)^2) ∧ Real.log ((31:ℝ)^2)≤(17169936031/2500000000:ℝ) := by
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((31:ℝ)^2)=2*(Real.log (31:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h31.1,h31.2]

theorem scale_33 : (17482537803/2500000000:ℝ)≤Real.log ((33:ℝ)^2) ∧ Real.log ((33:ℝ)^2)≤(17482537813/2500000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((33:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (11:ℝ)) := by
    calc Real.log ((33:ℝ)^2)=2*Real.log (33:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (11:ℝ)) := by
           rw [show (33:ℝ)=(3:ℝ)*(11:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h3.1,h3.2]

theorem scale_34 : (17631802617/2500000000:ℝ)≤Real.log ((34:ℝ)^2) ∧ Real.log ((34:ℝ)^2)≤(35263605259/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have he : Real.log ((34:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (17:ℝ)) := by
    calc Real.log ((34:ℝ)^2)=2*Real.log (34:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (17:ℝ)) := by
           rw [show (34:ℝ)=(2:ℝ)*(17:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h2.1,h2.2]

theorem scale_35 : (35553480607/5000000000:ℝ)≤Real.log ((35:ℝ)^2) ∧ Real.log ((35:ℝ)^2)≤(56885569/8000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((35:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (7:ℝ)) := by
    calc Real.log ((35:ℝ)^2)=2*Real.log (35:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (7:ℝ)) := by
           rw [show (35:ℝ)=(5:ℝ)*(7:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h7.1,h7.2]

theorem scale_37 : (18054588951/2500000000:ℝ)≤Real.log ((37:ℝ)^2) ∧ Real.log ((37:ℝ)^2)≤(36109179951/5000000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((37:ℝ)^2)=2*(Real.log (37:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h37.1,h37.2]

theorem scale_38 : (2273491349/312500000:ℝ)≤Real.log ((38:ℝ)^2) ∧ Real.log ((38:ℝ)^2)≤(36375861611/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((38:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (19:ℝ)) := by
    calc Real.log ((38:ℝ)^2)=2*Real.log (38:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (19:ℝ)) := by
           rw [show (38:ℝ)=(2:ℝ)*(19:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h19.1,h19.2]

theorem scale_39 : (36635616451/5000000000:ℝ)≤Real.log ((39:ℝ)^2) ∧ Real.log ((39:ℝ)^2)≤(36635616473/5000000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((39:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (13:ℝ)) := by
    calc Real.log ((39:ℝ)^2)=2*Real.log (39:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (13:ℝ)) := by
           rw [show (39:ℝ)=(3:ℝ)*(13:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h13.1,h13.2]

theorem scale_41 : (18567859461/2500000000:ℝ)≤Real.log ((41:ℝ)^2) ∧ Real.log ((41:ℝ)^2)≤(464196523/62500000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have he : Real.log ((41:ℝ)^2)=2*(Real.log (41:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h41.1,h41.2]

theorem scale_42 : (37376696173/5000000000:ℝ)≤Real.log ((42:ℝ)^2) ∧ Real.log ((42:ℝ)^2)≤(18688348097/2500000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((42:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (3:ℝ)+Real.log (7:ℝ)) := by
    calc Real.log ((42:ℝ)^2)=2*Real.log (42:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (3:ℝ)+Real.log (7:ℝ)) := by
           rw [show (42:ℝ)=(2:ℝ)*(3:ℝ)*(7:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num),Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h3.1,h3.2,h7.1,h7.2]

theorem scale_43 : (37611999233/5000000000:ℝ)≤Real.log ((43:ℝ)^2) ∧ Real.log ((43:ℝ)^2)≤(37612002449/5000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have he : Real.log ((43:ℝ)^2)=2*(Real.log (43:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h43.1,h43.2]

theorem scale_46 : (38286413949/5000000000:ℝ)≤Real.log ((46:ℝ)^2) ∧ Real.log ((46:ℝ)^2)≤(1914320699/250000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((46:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (23:ℝ)) := by
    calc Real.log ((46:ℝ)^2)=2*Real.log (46:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (23:ℝ)) := by
           rw [show (46:ℝ)=(2:ℝ)*(23:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h23.1,h23.2]

theorem scale_47 : (38501473837/5000000000:ℝ)≤Real.log ((47:ℝ)^2) ∧ Real.log ((47:ℝ)^2)≤(38501477479/5000000000:ℝ) := by
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((47:ℝ)^2)=2*(Real.log (47:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h47.1,h47.2]

theorem scale_51 : (7863651263/1000000000:ℝ)≤Real.log ((51:ℝ)^2) ∧ Real.log ((51:ℝ)^2)≤(39318256341/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((51:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (17:ℝ)) := by
    calc Real.log ((51:ℝ)^2)=2*Real.log (51:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (17:ℝ)) := by
           rw [show (51:ℝ)=(3:ℝ)*(17:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h3.1,h3.2]

theorem scale_53 : (1588116669/200000000:ℝ)≤Real.log ((53:ℝ)^2) ∧ Real.log ((53:ℝ)^2)≤(39702920753/5000000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((53:ℝ)^2)=2*(Real.log (53:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h53.1,h53.2]

theorem scale_55 : (40073331843/5000000000:ℝ)≤Real.log ((55:ℝ)^2) ∧ Real.log ((55:ℝ)^2)≤(8014666373/1000000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((55:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (11:ℝ)) := by
    calc Real.log ((55:ℝ)^2)=2*Real.log (55:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (11:ℝ)) := by
           rw [show (55:ℝ)=(5:ℝ)*(11:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h5.1,h5.2]

theorem scale_57 : (8086102533/1000000000:ℝ)≤Real.log ((57:ℝ)^2) ∧ Real.log ((57:ℝ)^2)≤(40430512693/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((57:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (19:ℝ)) := by
    calc Real.log ((57:ℝ)^2)=2*Real.log (57:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (19:ℝ)) := by
           rw [show (57:ℝ)=(3:ℝ)*(19:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h3.1,h3.2]

theorem scale_58 : (40604430087/5000000000:ℝ)≤Real.log ((58:ℝ)^2) ∧ Real.log ((58:ℝ)^2)≤(10151107531/1250000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((58:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (29:ℝ)) := by
    calc Real.log ((58:ℝ)^2)=2*Real.log (58:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (29:ℝ)) := by
           rw [show (58:ℝ)=(2:ℝ)*(29:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h29.1,h29.2]

theorem scale_59 : (5096921487/625000000:ℝ)≤Real.log ((59:ℝ)^2) ∧ Real.log ((59:ℝ)^2)≤(2548461009/312500000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have he : Real.log ((59:ℝ)^2)=2*(Real.log (59:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h59.1,h59.2]

theorem scale_61 : (10277184017/1250000000:ℝ)≤Real.log ((61:ℝ)^2) ∧ Real.log ((61:ℝ)^2)≤(2569296273/312500000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((61:ℝ)^2)=2*(Real.log (61:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h61.1,h61.2]

theorem scale_62 : (41271343831/5000000000:ℝ)≤Real.log ((62:ℝ)^2) ∧ Real.log ((62:ℝ)^2)≤(4127134387/500000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((62:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (31:ℝ)) := by
    calc Real.log ((62:ℝ)^2)=2*Real.log (62:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (31:ℝ)) := by
           rw [show (62:ℝ)=(2:ℝ)*(31:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h31.1,h31.2]

theorem scale_65 : (2608992043/312500000:ℝ)≤Real.log ((65:ℝ)^2) ∧ Real.log ((65:ℝ)^2)≤(5217984089/625000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((65:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (13:ℝ)) := by
    calc Real.log ((65:ℝ)^2)=2*Real.log (65:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (13:ℝ)) := by
           rw [show (65:ℝ)=(5:ℝ)*(13:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h5.1,h5.2]

theorem scale_67 : (42046923551/5000000000:ℝ)≤Real.log ((67:ℝ)^2) ∧ Real.log ((67:ℝ)^2)≤(42046927967/5000000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have he : Real.log ((67:ℝ)^2)=2*(Real.log (67:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h67.1,h67.2]

theorem scale_69 : (4234106503/500000000:ℝ)≤Real.log ((69:ℝ)^2) ∧ Real.log ((69:ℝ)^2)≤(21170532531/2500000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((69:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (23:ℝ)) := by
    calc Real.log ((69:ℝ)^2)=2*Real.log (69:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (23:ℝ)) := by
           rw [show (69:ℝ)=(3:ℝ)*(23:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h23.1,h23.2]

theorem scale_70 : (4248495241/500000000:ℝ)≤Real.log ((70:ℝ)^2) ∧ Real.log ((70:ℝ)^2)≤(42484952433/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((70:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (5:ℝ)+Real.log (7:ℝ)) := by
    calc Real.log ((70:ℝ)^2)=2*Real.log (70:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (5:ℝ)+Real.log (7:ℝ)) := by
           rw [show (70:ℝ)=(2:ℝ)*(5:ℝ)*(7:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num),Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h5.1,h5.2,h7.1,h7.2]

theorem scale_71 : (666043689/78125000:ℝ)≤Real.log ((71:ℝ)^2) ∧ Real.log ((71:ℝ)^2)≤(21313400283/2500000000:ℝ) := by
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((71:ℝ)^2)=2*(Real.log (71:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h71.1,h71.2]

theorem scale_73 : (10726147931/1250000000:ℝ)≤Real.log ((73:ℝ)^2) ∧ Real.log ((73:ℝ)^2)≤(5363074527/625000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have he : Real.log ((73:ℝ)^2)=2*(Real.log (73:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h73.1,h73.2]

theorem scale_74 : (8608129941/1000000000:ℝ)≤Real.log ((74:ℝ)^2) ∧ Real.log ((74:ℝ)^2)≤(43040651759/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((74:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (37:ℝ)) := by
    calc Real.log ((74:ℝ)^2)=2*Real.log (74:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (37:ℝ)) := by
           rw [show (74:ℝ)=(2:ℝ)*(37:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h37.1,h37.2]

theorem scale_77 : (678719597/78125000:ℝ)≤Real.log ((77:ℝ)^2) ∧ Real.log ((77:ℝ)^2)≤(5429756779/625000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((77:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (11:ℝ)) := by
    calc Real.log ((77:ℝ)^2)=2*Real.log (77:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (11:ℝ)) := by
           rw [show (77:ℝ)=(7:ℝ)*(11:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h7.1,h7.2]

theorem scale_79 : (43694475807/5000000000:ℝ)≤Real.log ((79:ℝ)^2) ∧ Real.log ((79:ℝ)^2)≤(43694480351/5000000000:ℝ) := by
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((79:ℝ)^2)=2*(Real.log (79:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h79.1,h79.2]

theorem scale_82 : (1762687629/200000000:ℝ)≤Real.log ((82:ℝ)^2) ∧ Real.log ((82:ℝ)^2)≤(2754199603/312500000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have he : Real.log ((82:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (41:ℝ)) := by
    calc Real.log ((82:ℝ)^2)=2*Real.log (82:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (41:ℝ)) := by
           rw [show (82:ℝ)=(2:ℝ)*(41:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h2.1,h2.2]

theorem scale_83 : (8837680669/1000000000:ℝ)≤Real.log ((83:ℝ)^2) ∧ Real.log ((83:ℝ)^2)≤(11047101979/1250000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have he : Real.log ((83:ℝ)^2)=2*(Real.log (83:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h83.1,h83.2]

#print axioms scale_1
#print axioms scale_2
#print axioms scale_3
#print axioms scale_5
#print axioms scale_6
#print axioms scale_7
#print axioms scale_10
#print axioms scale_11
#print axioms scale_13
#print axioms scale_14
#print axioms scale_15
#print axioms scale_17
#print axioms scale_19
#print axioms scale_21
#print axioms scale_22
#print axioms scale_23
#print axioms scale_26
#print axioms scale_29
#print axioms scale_30
#print axioms scale_31
#print axioms scale_33
#print axioms scale_34
#print axioms scale_35
#print axioms scale_37
#print axioms scale_38
#print axioms scale_39
#print axioms scale_41
#print axioms scale_42
#print axioms scale_43
#print axioms scale_46
#print axioms scale_47
#print axioms scale_51
#print axioms scale_53
#print axioms scale_55
#print axioms scale_57
#print axioms scale_58
#print axioms scale_59
#print axioms scale_61
#print axioms scale_62
#print axioms scale_65
#print axioms scale_67
#print axioms scale_69
#print axioms scale_70
#print axioms scale_71
#print axioms scale_73
#print axioms scale_74
#print axioms scale_77
#print axioms scale_79
#print axioms scale_82
#print axioms scale_83
end
end JSP233.ScaleLogs132
