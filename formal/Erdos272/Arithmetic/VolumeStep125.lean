import Erdos272.Arithmetic.VolumeLower125

namespace JSP233.VolumeStep125
open VolumeLower125 SimplexMoment57
open scoped Classical BigOperators
open Set MeasureTheory intervalIntegral
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem count_step (k : ℕ) (V W : ℝ→ℝ)
    (hmono : MonotoneOn V (Ici (1:ℝ))) (hV1 : V 1=0)
    (hlower : ∀x:ℝ,1≤x→V x≤(DivCount k (Nat.floor x):ℝ))
    (hint : ∀x:ℝ,1≤x→(∫t in (1:ℝ)..x,V (x/t))=W x)
    {x : ℝ} (hx : 1≤x) : W x≤(DivCount (k+1) (Nat.floor x):ℝ) := by
  have hqx : ((Nat.floor x):ℝ)≤x := Nat.floor_le (by linarith only [hx])
  have hq1 : 1≤Nat.floor x := (Nat.one_le_floor_iff x).mpr hx
  have hqpos : (0:ℝ)<Nat.floor x := Nat.cast_pos.mpr (by omega)
  have hquot : (1:ℝ)≤x/(Nat.floor x) := (one_le_div hqpos).mpr hqx
  have hf : AntitoneOn (fun t:ℝ=>V (x/t)) (Icc 1 x) := by
    intro u hu v hv huv
    have hu0 : 0<u := lt_of_lt_of_le zero_lt_one hu.1
    have hv0 : 0<v := lt_of_lt_of_le zero_lt_one hv.1
    have hqu : 1≤x/u := (one_le_div hu0).mpr hu.2
    have hqv : 1≤x/v := (one_le_div hv0).mpr hv.2
    exact hmono hqv hqu (div_le_div_of_nonneg_left (by linarith only [hx]) hu0 huv)
  have hfq : 0≤V (x/(Nat.floor x)) := by
    have h := hmono (by norm_num : (1:ℝ)∈Ici 1) hquot hquot
    rwa [hV1] at h
  have hi := integral_le_sum_floor hx (fun t:ℝ=>V (x/t)) hf hfq
  rw [hint x hx] at hi
  have hs : (∑a∈Finset.Icc 1 (Nat.floor x),V (x/(a:ℝ)))≤
      ∑a∈Finset.Icc 1 (Nat.floor x),(DivCount k (Nat.floor (x/(a:ℝ))):ℝ) := by
    apply Finset.sum_le_sum
    intro a ha
    obtain ⟨ha1,haq⟩ := Finset.mem_Icc.mp ha
    have ha0 : (0:ℝ)<a := Nat.cast_pos.mpr ha1
    have hax : (a:ℝ)≤x := (Nat.cast_le.mpr haq).trans hqx
    exact hlower (x/(a:ℝ)) ((one_le_div ha0).mpr hax)
  have he : (∑a∈Finset.Icc 1 (Nat.floor x),(DivCount k (Nat.floor (x/(a:ℝ))):ℝ))=
      (DivCount (k+1) (Nat.floor x):ℝ) := by
    simp only [DivCount,Nat.cast_sum,Nat.floor_div_natCast]
  exact hi.trans (hs.trans he.le)

theorem integral_v1 {x : ℝ} (hx : 1≤x) :
    (∫t in (1:ℝ)..x,V1 (x/t))=V2 x := by
  have h0 : IntervalIntegrable (LogKernel x 0) volume 1 x :=
    (log_kernel_continuous hx 0).intervalIntegrable_of_Icc hx
  have he : (∫t in (1:ℝ)..x,V1 (x/t))=
      ∫t in (1:ℝ)..x,(x*LogKernel x 0 t-1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [V1,LogKernel]
    ring
  rw [he,intervalIntegral.integral_sub (h0.const_mul x) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,log_kernel_integral hx 0,intervalIntegral.integral_const]
  norm_num
  dsimp only [V2]
  ring

theorem integral_v2 {x : ℝ} (hx : 1≤x) :
    (∫t in (1:ℝ)..x,V2 (x/t))=V3 x := by
  have h0 : IntervalIntegrable (LogKernel x 0) volume 1 x :=
    (log_kernel_continuous hx 0).intervalIntegrable_of_Icc hx
  have h1 : IntervalIntegrable (LogKernel x 1) volume 1 x :=
    (log_kernel_continuous hx 1).intervalIntegrable_of_Icc hx
  have he : (∫t in (1:ℝ)..x,V2 (x/t))=
      ∫t in (1:ℝ)..x,(x*LogKernel x 1 t-x*LogKernel x 0 t+1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx] at ht
    have hx0 : x≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
    have ht0 : t≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    dsimp only [V2,LogKernel]
    rw [Real.log_div hx0 ht0]
    ring
  rw [he,intervalIntegral.integral_add ((h1.const_mul x).sub (h0.const_mul x)) intervalIntegrable_const,
    intervalIntegral.integral_sub (h1.const_mul x) (h0.const_mul x),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    log_kernel_integral hx 1,log_kernel_integral hx 0,intervalIntegral.integral_const]
  norm_num
  dsimp only [V3]
  ring

theorem integral_v3 {x : ℝ} (hx : 1≤x) :
    (∫t in (1:ℝ)..x,V3 (x/t))=V4 x := by
  have h0 : IntervalIntegrable (LogKernel x 0) volume 1 x :=
    (log_kernel_continuous hx 0).intervalIntegrable_of_Icc hx
  have h1 : IntervalIntegrable (LogKernel x 1) volume 1 x :=
    (log_kernel_continuous hx 1).intervalIntegrable_of_Icc hx
  have h2 : IntervalIntegrable (LogKernel x 2) volume 1 x :=
    (log_kernel_continuous hx 2).intervalIntegrable_of_Icc hx
  have he : (∫t in (1:ℝ)..x,V3 (x/t))=
      ∫t in (1:ℝ)..x,((x/2)*LogKernel x 2 t-x*LogKernel x 1 t+x*LogKernel x 0 t-1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx] at ht
    have hx0 : x≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
    have ht0 : t≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    dsimp only [V3,LogKernel]
    rw [Real.log_div hx0 ht0]
    ring
  rw [he,intervalIntegral.integral_sub (((h2.const_mul (x/2)).sub (h1.const_mul x)).add (h0.const_mul x)) intervalIntegrable_const,
    intervalIntegral.integral_add ((h2.const_mul (x/2)).sub (h1.const_mul x)) (h0.const_mul x),
    intervalIntegral.integral_sub (h2.const_mul (x/2)) (h1.const_mul x),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    log_kernel_integral hx 2,log_kernel_integral hx 1,log_kernel_integral hx 0,intervalIntegral.integral_const]
  norm_num
  dsimp only [V4]
  ring

theorem actual_v1_lower {x : ℝ} (_hx : 1≤x) : V1 x≤(DivCount 0 (Nat.floor x):ℝ) := by
  have h := Nat.lt_floor_add_one x
  dsimp only [V1,DivCount]
  linarith only [h]

theorem actual_v2_lower {x : ℝ} (hx : 1≤x) : V2 x≤(DivCount 1 (Nat.floor x):ℝ) := by
  exact count_step 0 V1 V2 v1_monotone (by norm_num [V1])
    (fun _ hz=>actual_v1_lower hz) (fun _ hz=>integral_v1 hz) hx

theorem actual_v3_lower {x : ℝ} (hx : 1≤x) : V3 x≤(DivCount 2 (Nat.floor x):ℝ) := by
  exact count_step 1 V2 V3 v2_monotone (by norm_num [V2])
    (fun _ hz=>actual_v2_lower hz) (fun _ hz=>integral_v2 hz) hx

theorem actual_v4_lower {x : ℝ} (hx : 1≤x) : V4 x≤(DivCount 3 (Nat.floor x):ℝ) := by
  exact count_step 2 V3 V4 v3_monotone (by norm_num [V3])
    (fun _ hz=>actual_v3_lower hz) (fun _ hz=>integral_v3 hz) hx

#print axioms count_step
#print axioms integral_v1
#print axioms integral_v2
#print axioms integral_v3
#print axioms actual_v1_lower
#print axioms actual_v2_lower
#print axioms actual_v3_lower
#print axioms actual_v4_lower
end
end JSP233.VolumeStep125
