module

public import Erdos272.Global.GlobalSeven208
public import Erdos272.Arithmetic.HybridPrices209
public import Erdos272.Counting.NearLocalized209
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.HybridGlobal208
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39
open PrivateFinset IntrinsicTriples208 SevenFamily208 SevenPrices208 GlobalSeven208
open HarmonicAbel29 ActualRecoveryChain208 RecoveryPrefix208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

structure UnitNearFees (N : ℕ) (G : Finset (Finset ℤ)) : Prop where
  unit242 : ∀A⊆G,(∀S∈A,242≤S.card)→UnitNearObligation N A G242 U242 Eta242 Light242
  unit243 : ∀A⊆G,(∀S∈A,243≤S.card)→UnitNearObligation N A G243 U243 Eta243 Light243

theorem actual_common_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hfees : UnitNearFees N (SparseCrooked N 11 F)) :
    ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S := by
  let G := SparseCrooked N 11 F
  have hGF : G⊆F := actual_sparse_subset N 11 F
  have hG := actual_sparse_legal (r := 11) hF
  have hbad : ∀S∈G,¬IsAP S := fun S hS=>(actual_sparse_membership.mp hS).2.1
  have hsparse : ∀S∈G,11*S.card≤N := fun S hS=>(actual_sparse_membership.mp hS).2.2
  have htwo : 2≤G.card := actual_sparse_two hN hhigh hF hcard
  have hn : (659912 : ℝ)≤N := by exact_mod_cast hN
  have hhi : (N : ℝ)≤705097 := by exact_mod_cast hhigh
  by_cases hk : (Kernel (Ground N) G).Nonempty
  · obtain ⟨c,hc⟩ := hk
    obtain ⟨hcN,hroot⟩ := Finset.mem_filter.mp hc
    exact ⟨c,hcN,fun S hS hbad=>hroot S (Finset.mem_filter.mpr ⟨hS,hbad⟩)⟩
  · have hke : Kernel (Ground N) G=∅ := Finset.not_nonempty_iff_eq_empty.mp hk
    have hc := actual_cases hG hbad htwo hke
    have hscale := APCoupling208.actual207_source_range hhigh
    have hunit242 : ∀A⊆G,(∀S∈A,242≤S.card)→
        (A.card : ℝ)≤6*G242*(∑S∈F,((Pool S).card : ℝ))+U242*(N : ℝ)^2+Eta242*N+Light242 := by
      intro A hAG hlow
      exact actual_unit_source (hAG.trans hGF) (by norm_num [G242]) (hfees.unit242 A hAG hlow)
    have hunit243 : ∀A⊆G,(∀S∈A,243≤S.card)→
        (A.card : ℝ)≤6*G243*(∑S∈F,((Pool S).card : ℝ))+U243*(N : ℝ)^2+Eta243*N+Light243 := by
      intro A hAG hlow
      exact actual_unit_source (hAG.trans hGF) (by norm_num [G243]) (hfees.unit243 A hAG hlow)
    have hhighPaid : ∀c∈Ground N,∀T∈Avoiders G c,
        (∀S∈Avoiders G c,T.card≤S.card)→∀j : ℕ,2≤j→
        242*2^j≤T.card→T.card≤2*242*2^j→False := by
      intro c hc T hT hmin j hj hl hu
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
    exfalso
    cases hc with
    | single T hT hmin hsmall hkernel hpattern =>
      exact actual_small_branch_false hN hhigh hF hcard (actual_small_payment hG hbad htwo hT hsmall hkernel)
    | multiple T hT hmin hsmall hkernel hpattern =>
      exact actual_small_branch_false hN hhigh hF hcard (actual_small_payment hG hbad htwo hT hsmall hkernel)
    | whole hlow =>
      apply actual_unit_branch_false (g := G242) (u := U242) (eta := Eta242)
        (light := Light242) (root := 0) hN hhigh hF hcard (by norm_num [G242]) _ _
        (by simpa only [Whole,add_zero] using (SevenPrices208.whole_window hn hhi))
      · simpa only [G242,div_eq_mul_inv,one_mul,mul_comm] using hscale.2.1
      · have hs := hunit242 G (fun S hS=>hS) hlow
        simpa only [add_zero,zero_mul] using hs
    | root_exact c hc T hT hmin he =>
      obtain ⟨hTG,hTc⟩ := Finset.mem_filter.mp hT
      have hs := hunit242 (Avoiders G c) (Finset.filter_subset _ _) (by intro S hS;have hh:=hmin S hS;omega)
      have hr := SparseSmall39.actual_degree_from_omitter hG hbad hTG hTc
      have hrL : ((RootPart G c).card : ℝ)≤242*(N : ℝ) := by
        have hb : DegreeBudget N T.card≤T.card*N := by
          unfold DegreeBudget
          calc
            _≤∑_i∈Finset.range T.card,N := Finset.sum_le_sum (fun i hi=>by omega)
            _=_ := by simp [mul_comm]
        have hh := hr.trans hb
        rw [he] at hh
        exact_mod_cast hh
      have hpart : ((RootPart G c).card : ℝ)+(Avoiders G c).card=G.card := by exact_mod_cast root_avoider_card_partition G c
      apply actual_unit_branch_false (g := G242) (u := U242) (eta := Eta242)
        (light := Light242) (root := 242) hN hhigh hF hcard (by norm_num [G242]) _ _
        (SevenPrices208.rootexact_window hn hhi)
      · simpa only [G242,div_eq_mul_inv,one_mul,mul_comm] using hscale.2.1
      · nlinarith only [hs,hrL,hpart]
    | root_tail c hc T hT hmin hl hu =>
      obtain ⟨hTG,hTc⟩ := Finset.mem_filter.mp hT
      have hs := hunit243 (Avoiders G c) (Finset.filter_subset _ _) (by intro S hS;exact hl.trans (hmin S hS))
      have hr := actual_degree_from_omitter hG hbad hTG hTc
      have hrL : ((RootPart G c).card : ℝ)≤483*(N : ℝ) := by
        have hb : DegreeBudget N T.card≤T.card*N := by
          unfold DegreeBudget
          calc
            _≤∑_i∈Finset.range T.card,N := Finset.sum_le_sum (fun i hi=>by omega)
            _=_ := by simp [mul_comm]
        have hh := (hr.trans hb).trans (Nat.mul_le_mul_right N hu)
        exact_mod_cast hh
      have hpart : ((RootPart G c).card : ℝ)+(Avoiders G c).card=G.card := by exact_mod_cast root_avoider_card_partition G c
      apply actual_unit_branch_false (g := G243) (u := U243) (eta := Eta243)
        (light := Light243) (root := 483) hN hhigh hF hcard (by norm_num [G243]) _ _
        (SevenPrices208.roottail_window hn hhi)
      · simpa only [G243,div_eq_mul_inv,one_mul,mul_comm] using hscale.2.2.2
      · nlinarith only [hs,hrL,hpart]
    | root_two c hc T hT hmin hl hu =>
      obtain ⟨hTG,hTc⟩ := Finset.mem_filter.mp hT
      have hs := hunit242 (Avoiders G c) (Finset.filter_subset _ _) (by intro S hS;have hh:=hmin S hS;norm_num at hl;omega)
      have hr := actual_degree_from_omitter hG hbad hTG hTc
      have hrL : ((RootPart G c).card : ℝ)≤968*(N : ℝ) := by
        have hb : DegreeBudget N T.card≤T.card*N := by
          unfold DegreeBudget
          calc
            _≤∑_i∈Finset.range T.card,N := Finset.sum_le_sum (fun i hi=>by omega)
            _=_ := by simp [mul_comm]
        have ht : T.card≤968 := by norm_num at hu;exact hu
        have hh := (hr.trans hb).trans (Nat.mul_le_mul_right N ht)
        exact_mod_cast hh
      have hpart : ((RootPart G c).card : ℝ)+(Avoiders G c).card=G.card := by exact_mod_cast root_avoider_card_partition G c
      apply actual_unit_branch_false (g := G242) (u := U242) (eta := Eta242)
        (light := Light242) (root := 968) hN hhigh hF hcard (by norm_num [G242]) _ _
        (HybridPrices209.root_two_window hn hhi)
      · simpa only [G242,div_eq_mul_inv,one_mul,mul_comm] using hscale.2.1
      · nlinarith only [hs,hrL,hpart]
    | root_high c hc T hT hmin j hj hl hu => exact hhighPaid c hc T hT hmin j hj hl hu

theorem actual_original_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F)
    (hfees : UnitNearFees N (SparseCrooked N 11 F)) : F.card≤B N := by
  by_cases hc : B N≤F.card
  · exact RootedWindow209.actual_original_upper_of_root11 hN hhigh hF
      (actual_common_root hN hhigh hF hc hfees)
  · omega

#print axioms actual_common_root
#print axioms actual_original_upper
end
end JSP233.HybridGlobal208
