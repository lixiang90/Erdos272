module

public import Erdos272.Resources.SevenFamily208
public import Erdos272.Resources.RootedWindow209
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.GlobalSeven208
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39
open PrivateFinset IntrinsicTriples208 SevenFamily208 SevenPrices208
open HarmonicAbel29 ActualRecoveryChain208 RecoveryPrefix208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- These are weighted cardinalities of actual resource-deficiency families.
No bound on the original or sparse family's cardinality is a field. -/
structure NearFees (N : ℕ) (G : Finset (Finset ℤ)) : Prop where
  unit242 : ∀A⊆G,(∀S∈A,242≤S.card)→UnitNearObligation N A G242 U242 Eta242 Light242
  unit243 : ∀A⊆G,(∀S∈A,243≤S.card)→UnitNearObligation N A G243 U243 Eta243 Light243
  uniform : ∀c∈Ground N,∀j : ℕ,1≤j→j≤8→
    (∀S∈Avoiders G c,242*2^j≤S.card)→
    UniformNearObligation N (Avoiders G c) ((2 : ℝ)^j) UniformG UniformU UniformEta

theorem original_lower {N : ℕ} {F : Finset (Finset ℤ)} (hcard : B N≤F.card) :
    (N : ℝ)^2/2-(N : ℝ)+1≤F.card := by
  have hc : N.choose 2+1≤F.card := by unfold B at hcard;omega
  have hr : (N.choose 2 : ℝ)+1≤F.card := by exact_mod_cast hc
  rw [Nat.cast_choose_two] at hr
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  nlinarith only [hr,hN0]

theorem actual_flat_AP {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1≤N) (hF : Legal (Ground N) F) :
    ((APPart F).card : ℝ)≤(329/800 : ℝ)*(N : ℝ)^2+(N : ℝ)*Harmonic N+1 := by
  have hG := actual_AP_part_legal hF
  have hh := APTail208.actual_AP_profile_sharp hN (le_refl N) hG
    (fun S hS=>(Finset.mem_filter.mp hS).2) (by
      intro S hS
      simpa only [ground_card] using Finset.card_le_card (hG.1 S hS))
  have hn : (N : ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  norm_num [APCoupling208.APCoefficient,div_self hn] at hh
  exact hh

theorem actual_sparse_density {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
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
  have hn : (659912 : ℝ)≤N := by exact_mod_cast hN
  have hmargin : (HCap+122-Loss)*(N : ℝ)+968<0 := by
    norm_num [HCap,Loss]
    linarith only [hn]
  nlinarith only [hAP,hlow,hdR,hpR,hh,hmargin]

theorem actual_sparse_two {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    2≤(SparseCrooked N 11 F).card := by
  have hd := actual_sparse_density hN hhigh hF hcard
  have hn : (659912 : ℝ)≤N := by exact_mod_cast hN
  have hs := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg (α := ℝ) N)
  by_contra hh
  have hc : ((SparseCrooked N 11 F).card : ℝ)≤1 := by exact_mod_cast (by omega : (SparseCrooked N 11 F).card≤1)
  norm_num [Loss] at hd
  nlinarith only [hd,hs,hn,hc]

theorem actual_joint_any_AP {N : ℕ} {F : Finset (Finset ℤ)} {g fee : ℝ}
    (hN : 2≤N) (hF : Legal (Ground N) F) (hg : 0≤g) (hT : g*N≤APCoupling208.T)
    (hsource : ((F.filter fun S=>¬IsAP S).card : ℝ)≤6*g*(∑S∈F,((Pool S).card : ℝ))+fee) :
    (F.card : ℝ)≤(329/800 : ℝ)*(N : ℝ)^2+APCoupling208.Kappa*g*(N : ℝ)^3+
      (N : ℝ)*Harmonic N+1+fee := by
  by_cases hn : (F.filter IsAP).Nonempty
  · obtain ⟨P,hP,hmax⟩ := Finset.exists_max_image (F.filter IsAP) Finset.card hn
    obtain ⟨hPF,hPAP⟩ := Finset.mem_filter.mp hP
    exact APJoint208.actual_original_joint_payment (by omega) hF hPF hPAP
      (fun S hS hAP=>hmax S (Finset.mem_filter.mpr ⟨hS,hAP⟩)) hg hT hsource
  · have he : F.filter IsAP=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hp := Finset.card_filter_add_card_filter_not (s := F) IsAP
    rw [he,Finset.card_empty,zero_add] at hp
    have hpR : ((F.filter fun S=>¬IsAP S).card : ℝ)=F.card := by exact_mod_cast hp
    rw [hpR] at hsource
    have hpool := mul_le_mul_of_nonneg_left (UniformCapacity208.actual_triple_cube hF)
      (show 0≤6*g by positivity)
    have ht := mul_le_mul_of_nonneg_right hT (sq_nonneg (N : ℝ))
    have hH0 := harmonic_nonneg N
    have hNH : (0 : ℝ)≤(N : ℝ)*Harmonic N := mul_nonneg (Nat.cast_nonneg _) hH0
    norm_num [APCoupling208.T,APCoupling208.Kappa] at ht ⊢
    nlinarith only [hsource,hpool,ht,hNH,sq_nonneg (N : ℝ)]

theorem crooked_partition (N : ℕ) (F : Finset (Finset ℤ)) :
    ((F.filter fun S=>¬IsAP S).card : ℝ)=
      (SparseCrooked N 11 F).card+(Deleted N 11 F).card := by
  have hp := actual_original_three_part_partition N 11 F
  have hq := Finset.card_filter_add_card_filter_not (s := F) IsAP
  change (APPart F).card+(F.filter fun S=>¬IsAP S).card=F.card at hq
  exact_mod_cast (show (F.filter fun S=>¬IsAP S).card=(SparseCrooked N 11 F).card+(Deleted N 11 F).card by omega)

theorem actual_unit_branch_false {N : ℕ} {F : Finset (Finset ℤ)} {g u eta light root : ℝ}
    (hN : 659912≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hg : 0≤g) (hT : g*N≤APCoupling208.T)
    (hsource : ((SparseCrooked N 11 F).card : ℝ)≤
      6*g*(∑S∈F,((Pool S).card : ℝ))+u*(N : ℝ)^2+eta*N+light+root*N)
    (hprice : ReciprocalPrice208.Price (APCoupling208.Kappa*g) u (eta+root+Loss) (-light) N≤Budget) :
    False := by
  have hfull : ((F.filter fun S=>¬IsAP S).card : ℝ)≤
      6*g*(∑S∈F,((Pool S).card : ℝ))+
        (u*(N : ℝ)^2+eta*N+light+root*N+(Deleted N 11 F).card) := by
    rw [crooked_partition N F]
    linarith only [hsource]
  have hj := actual_joint_any_AP (by omega : 2≤N) hF hg hT hfull
  have hlow := original_lower hcard
  have hd := DenseDeletion208.actual_deleted11_affine (by omega : 10902≤N) hF
  have hdR : ((Deleted N 11 F).card : ℝ)≤121*(N : ℝ)+968 := by exact_mod_cast hd
  have hn : (659912 : ℝ)≤N := by exact_mod_cast hN
  have hn0 : (N : ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hpaid := mul_le_mul_of_nonneg_right hprice (sq_nonneg (N : ℝ))
  have he : ReciprocalPrice208.Price (APCoupling208.Kappa*g) u (eta+root+Loss) (-light) N*(N : ℝ)^2=
      APCoupling208.Kappa*g*(N : ℝ)^3+u*(N : ℝ)^2+(eta+root+Loss)*N+light := by
    unfold ReciprocalPrice208.Price
    field_simp
    <;> ring
  rw [he] at hpaid
  have hbudget : Budget≤(71/800 : ℝ) := by norm_num [Budget]
  have hb := mul_le_mul_of_nonneg_right hbudget (sq_nonneg (N : ℝ))
  have hh := mul_le_mul_of_nonneg_right (harmonic_cap (by omega : 100000≤N) hhigh)
    (Nat.cast_nonneg (α := ℝ) N)
  have hmargin : (HCap+122-Loss)*(N : ℝ)+968<0 := by
    norm_num [HCap,Loss]
    linarith only [hn]
  nlinarith only [hj,hlow,hdR,hpaid,hb,hh,hmargin]

theorem actual_small_branch_false {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hsmall : (SparseCrooked N 11 F).card≤58081*N) : False := by
  have hd := actual_sparse_density hN hhigh hF hcard
  have hn : (659912 : ℝ)≤N := by exact_mod_cast hN
  have hs : (58081+Loss : ℝ)≤(71/800 : ℝ)*N := by norm_num [Loss];linarith only [hn]
  have hp := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N)
  have hc : ((SparseCrooked N 11 F).card : ℝ)≤58081*(N : ℝ) := by exact_mod_cast hsmall
  nlinarith only [hd,hp,hc]

theorem actual_common_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hfees : NearFees N (SparseCrooked N 11 F)) :
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
    have huniform : ∀c∈Ground N,∀T∈Avoiders G c,
        (∀S∈Avoiders G c,T.card≤S.card)→∀j : ℕ,1≤j→
        242*2^j≤T.card→T.card≤2*242*2^j→False := by
      intro c hc T hT hmin j hj hl hu
      obtain ⟨hTG,hTc⟩ := Finset.mem_filter.mp hT
      have hsp := hsparse T hTG
      have hj8 := RootQuadratic208.actual207_scale_index hhigh (by nlinarith only [hl,hsp])
      have hlow : ∀S∈Avoiders G c,242*2^j≤S.card := fun S hS=>hl.trans (hmin S hS)
      have ha := actual_uniform_source (by omega : 2≤N) (by positivity : (0 : ℝ)<(2 : ℝ)^j)
        hG (Finset.filter_subset _ _) (hfees.uniform c hc j hj hj8 hlow)
      have hn0 : (0 : ℝ)<N := by linarith only [hn]
      have havoid : ((Avoiders G c).card : ℝ)/(N : ℝ)^2≤
          UniformG*N/((2 : ℝ)^j)^3+UniformU/(2 : ℝ)^j+UniformEta/N := by
        apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
        have he : (UniformG*N/((2 : ℝ)^j)^3+UniformU/(2 : ℝ)^j+UniformEta/N)*(N : ℝ)^2=
            UniformG*(N : ℝ)^3/((2 : ℝ)^j)^3+UniformU*(N : ℝ)^2/(2 : ℝ)^j+UniformEta*N := by
          field_simp
          <;> ring
        rw [he]
        exact ha
      have hp := RootPaid208.actual_uniform_root_paid hN hhigh hj hG hbad hTG hTc hl hu hsp havoid
      have hd := actual_sparse_density hN hhigh hF hcard
      have hpaid := (div_le_iff₀ (sq_pos_of_pos hn0)).mp hp
      have he : (Budget-Loss/(N : ℝ))*(N : ℝ)^2=Budget*(N : ℝ)^2-Loss*N := by
        field_simp
        <;> ring
      rw [he] at hpaid
      have hb := mul_le_mul_of_nonneg_right (show Budget≤(71/800 : ℝ) by norm_num [Budget])
        (sq_nonneg (N : ℝ))
      change (G.card : ℝ)≤_ at hpaid
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
    | root_two c hc T hT hmin hl hu => exact huniform c hc T hT hmin 1 (by decide) hl hu
    | root_high c hc T hT hmin j hj hl hu => exact huniform c hc T hT hmin j (by omega) hl hu

theorem actual_original_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F)
    (hfees : NearFees N (SparseCrooked N 11 F)) : F.card≤B N := by
  by_cases hc : B N≤F.card
  · exact RootedWindow209.actual_original_upper_of_root11 hN hhigh hF
      (actual_common_root hN hhigh hF hc hfees)
  · omega

#print axioms actual_flat_AP
#print axioms actual_sparse_density
#print axioms actual_joint_any_AP
#print axioms actual_unit_branch_false
#print axioms actual_common_root
#print axioms actual_original_upper
end
end JSP233.GlobalSeven208
