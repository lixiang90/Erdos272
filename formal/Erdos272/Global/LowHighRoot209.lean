import Erdos272.Global.HybridGlobal208
import Erdos272.Global.IntegerGlobalCases209

namespace JSP233.LowHighRoot209
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39
open PrivateFinset IntrinsicTriples208 SevenFamily208 SevenPrices208 GlobalSeven208
open HarmonicAbel29 ActualRecoveryChain208 RecoveryPrefix208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_high_false {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 659912≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hT : T∈Avoiders (SparseCrooked N 11 F) c)
    (hmin : ∀S∈Avoiders (SparseCrooked N 11 F) c,T.card≤S.card)
    (hlow : 4*242≤T.card) : False := by
  let G:=SparseCrooked N 11 F
  have hG:=actual_sparse_legal (r := 11) hF
  have hbad : ∀S∈G,¬IsAP S := fun S hS=>(actual_sparse_membership.mp hS).2.1
  have hsparse : ∀S∈G,11*S.card≤N := fun S hS=>(actual_sparse_membership.mp hS).2.2
  have hn : (659912 : ℝ)≤N := by exact_mod_cast hN
  have hhi : (N : ℝ)≤705097 := by exact_mod_cast hhigh
  obtain ⟨j,hj,hl,hu⟩:=IntegerHighRoot209.actual_scale (by decide : 0<242) hlow
  obtain ⟨hTG,hTc⟩ := Finset.mem_filter.mp hT
  have hsp := hsparse T hTG
  have hj8 := RootQuadratic208.actual207_scale_index hhigh (by nlinarith only [hl,hsp])
  obtain ⟨hK,hKsize,hD⟩ := HybridPrices209.minimum_size j hj hj8
  have hAL : Legal (Ground N) (Avoiders G c) :=
    ⟨fun S hS=>hG.1 S (Finset.mem_filter.mp hS).1,
      fun S hS R hR hSR=>hG.2 S (Finset.mem_filter.mp hS).1 R (Finset.mem_filter.mp hR).1 hSR⟩
  have hA := NearLocalized209.actual_family_normalized hAL hK (by omega : 0<N)
    (hhigh.trans_lt (HybridPrices209.level_cutoff j hj hj8))
    (fun S hS=>hbad S (Finset.mem_filter.mp hS).1)
    (fun S hS=>hKsize.trans (hl.trans (hmin S hS)))
  have hH := (harmonic_cap (by omega : 100000≤N) hhigh).trans (by norm_num [HCap] : HCap≤(141/10 : ℝ))
  have hN0 : (0 : ℝ)<N := by linarith only [hn]
  have hHpay := mul_le_mul_of_nonneg_left hH
    (show (0 : ℝ)≤(7/2 : ℝ)*(HybridPrices209.Levels j : ℝ)/(N : ℝ) by positivity)
  have hHpay' : (7/2 : ℝ)*(HybridPrices209.Levels j : ℝ)*Harmonic N/N≤
      (7/2 : ℝ)*(HybridPrices209.Levels j : ℝ)*(141/10 : ℝ)/N := by
    simpa only [div_mul_eq_mul_div] using hHpay
  have hApaid : ((Avoiders G c).card : ℝ)/(N : ℝ)^2≤
      (2303/200 : ℝ)/(HybridPrices209.K j : ℝ)+
      2*(N : ℝ)/((HybridPrices209.K j : ℝ)*((5*HybridPrices209.K j/3 : ℕ) : ℝ)^2)+
      (7/2 : ℝ)*(HybridPrices209.Levels j : ℝ)*(141/10 : ℝ)/N := by
    linarith only [hA,hHpay']
  have hr : ((RootPart G c).card : ℝ)/(N : ℝ)^2≤
      if j≤6 then ((2*(2^j : ℕ)*242 : ℕ) : ℝ)/N else Beta := by
    by_cases hj6 : j≤6
    · rw [if_pos hj6]
      have hdegree := actual_degree_from_omitter hG hbad hTG hTc
      have hlinear : DegreeBudget N T.card≤T.card*N := by
        unfold DegreeBudget
        calc
          _≤∑_i∈Finset.range T.card,N := Finset.sum_le_sum (fun i hi=>by omega)
          _=_ := by simp [mul_comm]
      have hnat := (hdegree.trans hlinear).trans (Nat.mul_le_mul_right N hu)
      have hnat' : (RootPart G c).card≤(2*(2^j : ℕ)*242)*N := by nlinarith only [hnat]
      have hnatR : ((RootPart G c).card : ℝ)≤((2*(2^j : ℕ)*242 : ℕ) : ℝ)*N := by exact_mod_cast hnat'
      apply (div_le_iff₀ (sq_pos_of_pos hN0)).mpr
      have he : (((2*(2^j : ℕ)*242 : ℕ) : ℝ)/(N : ℝ))*(N : ℝ)^2=
          ((2*(2^j : ℕ)*242 : ℕ) : ℝ)*N := by field_simp
      rw [he]
      exact hnatR
    · rw [if_neg hj6]
      have hq := RootQuadratic208.actual_root_scale_envelope (by omega : 4≤N)
        hG hbad hTG hTc hu hsp
      have hqm := RootQuadratic208.q_mono
        (min_le_right (2*(242 : ℝ)*((2^j : ℕ) : ℝ)/(N : ℝ)) (1/11 : ℝ))
        (by norm_num : (1/11 : ℝ)≤1)
      have he : RootQuadratic208.Q (1/11 : ℝ)=Beta := by norm_num [RootQuadratic208.Q,Beta]
      rw [he] at hqm
      exact hq.trans hqm
  have hpartition := RootQuadratic208.actual_partition_payment hr hApaid
  have he : (if j≤6 then ((2*(2^j : ℕ)*242 : ℕ) : ℝ)/(N : ℝ) else Beta)+
      ((2303/200 : ℝ)/(HybridPrices209.K j : ℝ)+
      2*(N : ℝ)/((HybridPrices209.K j : ℝ)*((5*HybridPrices209.K j/3 : ℕ) : ℝ)^2)+
      (7/2 : ℝ)*(HybridPrices209.Levels j : ℝ)*(141/10 : ℝ)/N)+Loss/N=
      HybridPrices209.High j N := by
    unfold HybridPrices209.High ReciprocalPrice208.Price
    split_ifs <;> ring
  have hprice := HybridPrices209.high_window j hj hj8 hn hhi
  have hp : (G.card : ℝ)/(N : ℝ)^2≤Budget-Loss/N := by
    linarith only [hpartition,he,hprice]
  have hd := actual_sparse_density hN hhigh hF hcard
  have hpaid := (div_le_iff₀ (sq_pos_of_pos hN0)).mp hp
  have hcancel : (Budget-Loss/(N : ℝ))*(N : ℝ)^2=Budget*(N : ℝ)^2-Loss*N := by field_simp
  rw [hcancel] at hpaid
  have hb := mul_le_mul_of_nonneg_right (show Budget≤(71/800 : ℝ) by norm_num [Budget]) (sq_nonneg (N : ℝ))
  change _<(G.card : ℝ) at hd
  nlinarith only [hd,hpaid,hb]

#print axioms actual_high_false
end
end JSP233.LowHighRoot209
