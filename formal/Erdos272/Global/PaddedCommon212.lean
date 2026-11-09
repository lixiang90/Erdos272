module

public import Erdos272.Resources.PaddedUnit212
public import Erdos272.Global.TruncatedGlobal209
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
namespace JSP233.PaddedCommon212
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39
open PrivateFinset IntrinsicTriples208 SevenFamily208 SevenPrices208 GlobalSeven208
open HarmonicAbel29 ActualRecoveryChain208 RecoveryPrefix208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_sparse_density {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 100000≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    (71/800 : ℝ)*(N : ℝ)^2-Loss*N<((SparseCrooked N 11 F).card : ℝ) := by
  have hAP := actual_flat_AP (by omega : 1≤N) hF
  have hlow := original_lower hcard
  have hd := DenseDeletion208.actual_deleted11_affine (by omega : 10902≤N) hF
  have hdR : ((Deleted N 11 F).card : ℝ)≤121*(N : ℝ)+968 := by exact_mod_cast hd
  have hp := actual_original_three_part_partition N 11 F
  have hpR : ((APPart F).card : ℝ)+(SparseCrooked N 11 F).card+(Deleted N 11 F).card=F.card :=
    by exact_mod_cast hp
  have hh := mul_le_mul_of_nonneg_right (harmonic_cap (by omega : 100000≤N) hhigh)
    (Nat.cast_nonneg (α := ℝ) N)
  have hn : (100000 : ℝ)≤N := by exact_mod_cast hN
  have hmargin : (HCap+122-Loss)*(N : ℝ)+968<0 := by
    norm_num [HCap,Loss]
    linarith only [hn]
  nlinarith only [hAP,hlow,hdR,hpR,hh,hmargin]

theorem actual_sparse_two {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 100000≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    2≤(SparseCrooked N 11 F).card := by
  have hd := actual_sparse_density hN hhigh hF hcard
  have hn : (100000 : ℝ)≤N := by exact_mod_cast hN
  have hs := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg (α := ℝ) N)
  by_contra hh
  have hc : ((SparseCrooked N 11 F).card : ℝ)≤1 := by exact_mod_cast (by omega : (SparseCrooked N 11 F).card≤1)
  norm_num [Loss] at hd
  nlinarith only [hd,hs,hn,hc]

theorem actual_low_false {N : ℕ} {F : Finset (Finset ℤ)} {g u eta light : ℝ}
    (hN : 100000≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hg : 0≤g) (hT : g*N≤TruncatedAPResponse209.T)
    (hsource : ((SparseCrooked N 11 F).card : ℝ)≤
      6*g*(∑S∈F,((Pool S).card : ℝ))+u*(N : ℝ)^2+eta*N+light+968*N)
    (hprice : ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*g) u
      (eta+968+Loss) (-light) N≤(71/800 : ℝ)) : False := by
  have hfull : ((F.filter fun S=>¬IsAP S).card : ℝ)≤
      6*g*(∑S∈F,((Pool S).card : ℝ))+
        (u*(N : ℝ)^2+eta*N+light+968*N+(Deleted N 11 F).card) := by
    rw [crooked_partition N F]
    linarith only [hsource]
  have hj:=TruncatedAPResponse209.actual_joint_any_AP (by omega : 2≤N) hF hg hT hfull
  have hlow:=original_lower hcard
  have hd:=DenseDeletion208.actual_deleted11_affine (by omega : 10902≤N) hF
  have hdR : ((Deleted N 11 F).card : ℝ)≤121*(N : ℝ)+968 := by exact_mod_cast hd
  have hn : (100000 : ℝ)≤N := by exact_mod_cast hN
  have hn0 : (N : ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hpaid:=mul_le_mul_of_nonneg_right hprice (sq_nonneg (N : ℝ))
  have he : ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*g) u
      (eta+968+Loss) (-light) N*(N : ℝ)^2=
      TruncatedAPResponse209.Kappa*g*(N : ℝ)^3+u*(N : ℝ)^2+(eta+968+Loss)*N+light := by
    unfold ReciprocalPrice208.Price
    field_simp
    ring
  rw [he] at hpaid
  have hh:=mul_le_mul_of_nonneg_right (harmonic_cap (by omega : 100000≤N) hhigh)
    (Nat.cast_nonneg (α := ℝ) N)
  have hmargin : (HCap+122-Loss)*(N : ℝ)+968<0 := by
    norm_num [HCap,Loss]
    linarith only [hn]
  nlinarith only [hj,hlow,hdR,hpaid,hh,hmargin]

theorem high_window {n : ℝ} (j : ℕ) (hj : 2≤j) (hjhi : j≤8)
    (hl : 638202≤n) (hu : n≤705097) : HybridPrices209.High j n≤Budget := by
  interval_cases j
  all_goals
    unfold HybridPrices209.High
    apply ReciprocalPrice208.window (by norm_num) hl hu
  all_goals norm_num [ReciprocalPrice208.Price,HybridPrices209.K,HybridPrices209.Levels,Budget,Loss,Beta]

theorem actual_high_false {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 638202≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hT : T∈Avoiders (SparseCrooked N 11 F) c)
    (hmin : ∀S∈Avoiders (SparseCrooked N 11 F) c,T.card≤S.card)
    (hlow : 4*242≤T.card) : False := by
  let G:=SparseCrooked N 11 F
  have hG:=actual_sparse_legal (r := 11) hF
  have hbad : ∀S∈G,¬IsAP S := fun S hS=>(actual_sparse_membership.mp hS).2.1
  have hsparse : ∀S∈G,11*S.card≤N := fun S hS=>(actual_sparse_membership.mp hS).2.2
  have hn : (638202 : ℝ)≤N := by exact_mod_cast hN
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
  have hprice := high_window j hj hj8 hn hhi
  have hp : (G.card : ℝ)/(N : ℝ)^2≤Budget-Loss/N := by
    linarith only [hpartition,he,hprice]
  have hd := actual_sparse_density (by omega : 100000≤N) hhigh hF hcard
  have hpaid := (div_le_iff₀ (sq_pos_of_pos hN0)).mp hp
  have hcancel : (Budget-Loss/(N : ℝ))*(N : ℝ)^2=Budget*(N : ℝ)^2-Loss*N := by field_simp
  rw [hcancel] at hpaid
  have hb := mul_le_mul_of_nonneg_right (show Budget≤(71/800 : ℝ) by norm_num [Budget]) (sq_nonneg (N : ℝ))
  change _<(G.card : ℝ) at hd
  nlinarith only [hd,hpaid,hb]

theorem actual_small_false {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 655996≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hsmall : (SparseCrooked N 11 F).card≤58081*N) : False := by
  have hd := actual_sparse_density (by omega : 100000≤N) hhigh hF hcard
  have hn : (655996 : ℝ)≤N := by exact_mod_cast hN
  have hs : (58081+Loss : ℝ)≤(71/800 : ℝ)*N := by norm_num [Loss];linarith only [hn]
  have hp := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N)
  have hc : ((SparseCrooked N 11 F).card : ℝ)≤58081*(N : ℝ) := by exact_mod_cast hsmall
  nlinarith only [hd,hp,hc]

theorem actual_common_root {N : ℕ} {F : Finset (Finset ℤ)} {g u eta light : ℝ}
    (hN : 655996≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hg : 0≤g) (hfees : TruncatedGlobal209.NearFees N (SparseCrooked N 11 F) g u eta light)
    (hT : g*N≤TruncatedAPResponse209.T)
    (hprice : ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*g) u
      (eta+968+Loss) (-light) N≤(71/800 : ℝ)) :
    ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S := by
  let G:=SparseCrooked N 11 F
  have hGF : G⊆F:=actual_sparse_subset N 11 F
  have hG:=actual_sparse_legal (r := 11) hF
  have hbad : ∀S∈G,¬IsAP S:=fun S hS=>(actual_sparse_membership.mp hS).2.1
  have htwo:=actual_sparse_two (by omega : 100000≤N) hhigh hF hcard
  have hpay : ∀A⊆G,(∀S∈A,242≤S.card)→
      ((G.card : ℝ)≤A.card+968*(N : ℝ))→False := by
    intro A hAG hsize hcover
    have hs:=actual_unit_source (hAG.trans hGF) hg (hfees A hAG hsize)
    apply actual_low_false (by omega : 100000≤N) hhigh hF hcard hg hT _ hprice
    linarith only [hs,hcover]
  cases IntegerGlobalCases209.actual_cases (N := N) (G := G) (by decide : 0<242) with
  | common c hc hall =>
    exact ⟨c,hc,fun S hS hbad=>hall S (Finset.mem_filter.mpr ⟨hS,hbad⟩)⟩
  | small T hT hsize hkernel =>
    have hp:=IntegerWindowEndpoints209.actual_coarse_small_payment hG hbad htwo hT hsize hkernel
    have hp' : G.card≤58081*N:=by norm_num at hp;exact hp
    exact False.elim (actual_small_false hN hhigh hF hcard hp')
  | whole hlow =>
    exact False.elim (hpay G (le_refl G) hlow (le_add_of_nonneg_right (by positivity)))
  | root_low c hc T hT hmin hlow hhighT =>
    obtain ⟨hTG,hTc⟩:=Finset.mem_filter.mp hT
    have hr:=actual_degree_from_omitter hG hbad hTG hTc
    have hb : DegreeBudget N T.card≤T.card*N := by
      unfold DegreeBudget
      calc
        _≤∑_i∈Finset.range T.card,N := Finset.sum_le_sum (fun i hi=>by omega)
        _=_ := by simp [mul_comm]
    have hnat:=(hr.trans hb).trans (Nat.mul_le_mul_right N hhighT.le)
    have hroot : ((RootPart G c).card : ℝ)≤968*(N : ℝ) := by exact_mod_cast hnat
    have hpart : ((RootPart G c).card : ℝ)+(Avoiders G c).card=G.card :=
      by exact_mod_cast root_avoider_card_partition G c
    have hcover : (G.card : ℝ)≤(Avoiders G c).card+968*(N : ℝ) := by linarith only [hroot,hpart]
    exact False.elim (hpay (Avoiders G c) (Finset.filter_subset _ _)
      (fun S hS=>hlow.trans (hmin S hS)) hcover)
  | root_high c hc T hT hmin hlow =>
    exact False.elim (actual_high_false (by omega : 638202≤N) hhigh hF hcard hT hmin hlow)

theorem actual_closed_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 655996≤N) (hhi : N≤659912) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S := by
  have hp := PaddedUnit212.actual_price (by omega : 638202≤N) hhi
  exact actual_common_root hN (by omega) hF hcard
    TruncatedUnitPrices209.nonneg.1 (PaddedUnit212.actual_fees hhi hF) hp.1
    (by simpa only [zero_add] using hp.2)

#print axioms actual_sparse_density
#print axioms actual_sparse_two
#print axioms actual_low_false
#print axioms high_window
#print axioms actual_high_false
#print axioms actual_small_false
#print axioms actual_common_root
#print axioms actual_closed_root
end
end JSP233.PaddedCommon212
