module

public import Erdos272.Resources.ProfileArms118
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! The same complete actual endpoint profile pays both physical arm gates
for width369/10 with6000-scaled physical arm slack. The actual dense11 minimum and a real short source justify every subtraction. -/
namespace JSP233.ProfileArms140
open StarCompletion APGeometry DenseDeletion40 LongTerminal35
open RawEndpoint112 RawEndpoint115 ProfileArms117
open ThinFringe33
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem profile_linear_bound {N L x a b q : ℝ} (hN : 0≤N) (hq : 0≤q)
    (hc : 0≤(40000*a^2+51600*a*b+23359*b^2)/3359)
    (hco : ((40000*a^2+51600*a*b+23359*b^2)/3359)*DeficitCoeff/(369/10:ℝ)^2≤q^2)
    (hp : ProfileDeficit L x≤DeficitCoeff/(369/10:ℝ)^2*N^2) : a*L+b*x≤q*N := by
  have hr := ProfileArms118.profile_linear_rayleigh a b L x
  have hm := mul_le_mul_of_nonneg_left hp hc
  have hn := mul_le_mul_of_nonneg_right hco (sq_nonneg N)
  have hs : (a*L+b*x)^2≤(q*N)^2 := by
    calc
      _≤((40000*a^2+51600*a*b+23359*b^2)/3359)*ProfileDeficit L x := hr
      _≤((40000*a^2+51600*a*b+23359*b^2)/3359)*(DeficitCoeff/(369/10:ℝ)^2*N^2) := hm
      _=(((40000*a^2+51600*a*b+23359*b^2)/3359)*DeficitCoeff/(369/10:ℝ)^2)*N^2 := by ring
      _≤q^2*N^2 := hn
      _=(q*N)^2 := by ring
  by_cases h : 0≤a*L+b*x
  · exact (sq_le_sq₀ h (mul_nonneg hq hN)).mp hs
  · have hz := mul_nonneg hq hN
    linarith only [h,hz]

theorem bad13_nontruncated_arm_margins {N L R m : ℕ}
    (hN : 2000000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hm : N<11*m) (hcap : m≤(L+N-R)+(R-L+1)/13)
    (hprofile : ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      DeficitCoeff/(369/10:ℝ)^2*(N:ℝ)^2) :
    6000*((L+N-R)+(R-L+1)/13-m)+(L+N-R)≤6000*(L-1) ∧
      6000*((L+N-R)+(R-L+1)/13-m)+(L+N-R)≤6000*(N-R) := by
  let w := L+N-R
  let M := R-L+1
  let b := w+M/13-m
  have hMw : M+w=N+1 := by dsimp only [M,w];omega
  have hdiv := Nat.mul_div_le M 13
  have hsub : b+m=w+M/13 := Nat.sub_add_cancel hcap
  have hd : 143*b+2*N+2≤132*w := by nlinarith only [hsub,hdiv,hMw,hm]
  have hdR : (2:ℝ)*N+143*(b:ℝ)+2≤132*(w:ℝ) := by
    exact_mod_cast (show 2*N+143*b+2≤132*w by omega)
  have hwr : (w:ℝ)=(L:ℝ)+((N-R:ℕ):ℝ) := by
    exact_mod_cast (show w=L+(N-R) by dsimp only [w];omega)
  have hLm1 : ((L-1:ℕ):ℝ)=(L:ℝ)-1 := by
    rw [Nat.cast_sub hL];norm_num
  have hn : (2000000:ℝ)≤N := by exact_mod_cast hN
  have hlinR := profile_linear_bound (a:=(792143/6000:ℝ)) (b:=(-65857/6000:ℝ))
    (q:=(1999/1000:ℝ)) (Nat.cast_nonneg N) (by norm_num) (by norm_num)
    (by norm_num [DeficitCoeff]) hprofile
  have hlinL := profile_linear_bound (a:=(-65857/6000:ℝ)) (b:=(792143/6000:ℝ))
    (q:=(1999/1000:ℝ)) (Nat.cast_nonneg N) (by norm_num) (by norm_num)
    (by norm_num [DeficitCoeff]) hprofile
  change 6000*b+w≤6000*(L-1) ∧ 6000*b+w≤6000*(N-R)
  constructor
  · by_contra hh
    have hf : (6000:ℝ)*((L-1:ℕ):ℝ)<6000*(b:ℝ)+(w:ℝ) := by
      exact_mod_cast (show 6000*(L-1)<6000*b+w by omega)
    have hg : (2:ℝ)*N < -(65857/6000:ℝ)*L+(792143/6000:ℝ)*((N-R:ℕ):ℝ)+141 := by
      nlinarith only [hdR,hf,hwr,hLm1]
    nlinarith only [hg,hlinL,hn]
  · by_contra hh
    have hf : (6000:ℝ)*((N-R:ℕ):ℝ)<6000*(b:ℝ)+(w:ℝ) := by
      exact_mod_cast (show 6000*(N-R)<6000*b+w by omega)
    have hg : (2:ℝ)*N < (792143/6000:ℝ)*L-(65857/6000:ℝ)*((N-R:ℕ):ℝ) := by
      nlinarith only [hdR,hf,hwr]
    nlinarith only [hg,hlinR,hn]

theorem actual_bad13_nonempty_arm_margins {N L R m : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 2000000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hF : Legal (Ground N) F) (hEF : E⊆F) (hne : E.Nonempty)
    (hminimum : ∀S∈E,m≤S.card) (hm : N<11*m)
    (hshort : ∀S∈E,(S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤(R-L+1)/13+1)
    (hprofile : ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      DeficitCoeff/(369/10:ℝ)^2*(N:ℝ)^2) :
    6000*((L+N-R)+(R-L+1)/13-m)+(L+N-R)≤6000*(L-1) ∧
      6000*((L+N-R)+(R-L+1)/13-m)+(L+N-R)≤6000*(N-R) := by
  obtain ⟨S,hSE⟩ := hne
  have hcap := ProfileArms117.actual_short_source_minimum_cap hL hLR hRN
    (hF.1 S (hEF hSE)) (hminimum S hSE) (hshort S hSE)
  exact bad13_nontruncated_arm_margins hN hL hLR hRN hm hcap hprofile


#print axioms profile_linear_bound
#print axioms bad13_nontruncated_arm_margins
#print axioms actual_bad13_nonempty_arm_margins
end
end JSP233.ProfileArms140
