module

public import Erdos272.Resources.APJoint208
public import Erdos272.Resources.UniformCapacity208
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! A stronger response on the smaller, explicitly checked source interval.
All AP/triple counting below uses the same original family and actual AP. -/
namespace JSP233.StrongAPResponse209
open StarCompletion IntrinsicTriples208 APResidual208 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def T : ℝ := 9/125
def Kappa : ℝ := 23/100
def Gap (a t : ℝ) : ℝ := (1-a)^2/2-t*(1-Kappa-a^3)

theorem endpoint_sos (a : ℝ) :
    Gap a T=T*a*(a-17/20)^2+(389/625 : ℝ)*(a-52601/62240)^2+
      76239/6224000000 := by
  norm_num [Gap,T,Kappa]
  ring

theorem endpoint_gap_pos {a : ℝ} (ha : 0≤a) : 0<Gap a T := by
  rw [endpoint_sos]
  have hc := mul_nonneg (mul_nonneg (show (0 : ℝ)≤T by norm_num [T]) ha)
    (sq_nonneg (a-17/20))
  have hq := mul_nonneg (show (0 : ℝ)≤389/625 by norm_num)
    (sq_nonneg (a-52601/62240))
  linarith only [hc,hq]

theorem gap_interpolation (a t : ℝ) :
    T*Gap a t=t*Gap a T+(T-t)*Gap a 0 := by unfold Gap; ring

theorem gap_nonneg {a t : ℝ} (ha : 0≤a) (ht : 0≤t) (hT : t≤T) : 0≤Gap a t := by
  have hp := (endpoint_gap_pos ha).le
  have hz : 0≤Gap a 0 := by simp only [Gap,zero_mul,sub_zero]; positivity
  have hs := add_nonneg (mul_nonneg ht hp) (mul_nonneg (sub_nonneg.mpr hT) hz)
  rw [←gap_interpolation] at hs
  exact nonneg_of_mul_nonneg_right hs (by norm_num [T])

theorem common_response {a t : ℝ} (ha : 0≤a) (ht : 0≤t) (hT : t≤T) :
    APCoupling208.APCoefficient a+t*(1-a^3)≤1/4+Kappa*t := by
  unfold APCoupling208.APCoefficient
  split_ifs with hh
  · have hsq : a^2≤(1/4 : ℝ) := by
      have hm := mul_nonneg (sub_nonneg.mpr hh)
        (show (0 : ℝ)≤1/2+a by linarith only [ha])
      nlinarith only [hm]
    have hc := mul_nonneg ht (pow_nonneg ha 3)
    norm_num [T,Kappa] at hT ⊢
    nlinarith only [hsq,hc,hT,ht]
  · have hg := gap_nonneg ha ht hT
    dsimp only [Gap] at hg
    linarith only [hg]

theorem actual_original_joint_payment {N : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ}
    {g fee : ℝ} (hN : 1≤N) (hF : Legal (Ground N) F)
    (hP : P∈F) (hAP : IsAP P) (hmax : ∀S∈F,IsAP S→S.card≤P.card)
    (hg : 0≤g) (hT : g*N≤T)
    (hsource : ((F.filter fun S=>¬IsAP S).card : ℝ)≤
      6*g*(∑S∈F,((Pool S).card : ℝ))+fee) :
    (F.card : ℝ)≤(329/800 : ℝ)*N^2+Kappa*g*N^3+(N : ℝ)*Harmonic N+1+fee := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast hN
  have hcount := APTail208.actual_AP_members_profile hN hF hP hAP hmax
  have hres := actual_residual_cubic hF hP hAP
  simp only [ground_card] at hres
  have hmass := mul_le_mul_of_nonneg_left hres (show 0≤6*g by positivity)
  have hnonAP : ((F.filter fun S=>¬IsAP S).card : ℝ)≤
      g*((N : ℝ)^3-(P.card : ℝ)^3)+fee := by nlinarith only [hsource,hmass]
  have hjoint := mul_le_mul_of_nonneg_left
    (common_response (by positivity : (0 : ℝ)≤(P.card : ℝ)/N)
      (show 0≤g*N by positivity) hT) (sq_nonneg (N : ℝ))
  have he : (N : ℝ)^2*(((P.card : ℝ)/N)^3*(g*N))=g*(P.card : ℝ)^3 := by
    field_simp
  have hbudget : (N : ℝ)^2*APCoupling208.APCoefficient ((P.card : ℝ)/N)+
      g*((N : ℝ)^3-(P.card : ℝ)^3)≤(N : ℝ)^2/4+Kappa*g*N^3 := by
    nlinarith only [hjoint,he]
  have hp := Finset.card_filter_add_card_filter_not (s := F) IsAP
  have hpR : ((F.filter IsAP).card : ℝ)+(F.filter fun S=>¬IsAP S).card=F.card := by
    exact_mod_cast hp
  nlinarith only [hcount,hnonAP,hbudget,hpR]

theorem actual_joint_any_AP {N : ℕ} {F : Finset (Finset ℤ)} {g fee : ℝ}
    (hN : 2≤N) (hF : Legal (Ground N) F) (hg : 0≤g) (hT : g*N≤T)
    (hsource : ((F.filter fun S=>¬IsAP S).card : ℝ)≤
      6*g*(∑S∈F,((Pool S).card : ℝ))+fee) :
    (F.card : ℝ)≤(329/800 : ℝ)*(N : ℝ)^2+Kappa*g*(N : ℝ)^3+
      (N : ℝ)*Harmonic N+1+fee := by
  by_cases hn : (F.filter IsAP).Nonempty
  · obtain ⟨P,hP,hmax⟩ := Finset.exists_max_image (F.filter IsAP) Finset.card hn
    obtain ⟨hPF,hPAP⟩ := Finset.mem_filter.mp hP
    exact actual_original_joint_payment (by omega : 1≤N) hF hPF hPAP
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
    norm_num [T,Kappa] at ht ⊢
    nlinarith only [hsource,hpool,ht,hNH,sq_nonneg (N : ℝ)]

#print axioms common_response
#print axioms actual_original_joint_payment
#print axioms actual_joint_any_AP
end
end JSP233.StrongAPResponse209
