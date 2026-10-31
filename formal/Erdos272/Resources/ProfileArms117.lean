import Erdos272.Resources.RawEndpoint116
import Erdos272.Retention.CrossBad116

/-! The full endpoint profile forces quantitative room on both actual arms.
The normalized profile hypothesis is paid from the independent bootstrap
profile and its scalar log gate; it is not a supplied slot-capacity premise.
Actual short sources justify the nontruncated minimum-size branch internally.
-/
namespace JSP233.ProfileArms117
open StarCompletion APGeometry DenseDeletion40 LongTerminal35
open RawEndpoint112 RawEndpoint115 RawEndpoint116
open ThinFringe33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem profile_right_rayleigh (L x : ℝ) :
    ((6743/50:ℝ)*L-(407/50:ℝ)*x)^2≤
      (1680980263391/8397500:ℝ)*ProfileDeficit L x := by
  have he : (1680980263391/8397500:ℝ)*ProfileDeficit L x-
      ((6743/50:ℝ)*L-(407/50:ℝ)*x)^2=
      (80000/3359:ℝ)*(-(164462287/4000000:ℝ)*L+(1296097/20000:ℝ)*x)^2 := by
    dsimp only [ProfileDeficit];ring
  have hs : 0≤(80000/3359:ℝ)*(-(164462287/4000000:ℝ)*L+(1296097/20000:ℝ)*x)^2 := by
    positivity
  linarith only [he,hs]

theorem profile_left_rayleigh (L x : ℝ) :
    (-(407/50:ℝ)*L+(6743/50:ℝ)*x)^2≤
      (927103024991/8397500:ℝ)*ProfileDeficit L x := by
  have he : (927103024991/8397500:ℝ)*ProfileDeficit L x-
      (-(407/50:ℝ)*L+(6743/50:ℝ)*x)^2=
      (80000/3359:ℝ)*(-(147009137/4000000:ℝ)*L+(788447/20000:ℝ)*x)^2 := by
    dsimp only [ProfileDeficit];ring
  have hs : 0≤(80000/3359:ℝ)*(-(147009137/4000000:ℝ)*L+(788447/20000:ℝ)*x)^2 := by
    positivity
  linarith only [he,hs]

theorem profile_linear_bounds {N L x : ℝ} (hN : 0≤N)
    (hprofile : ProfileDeficit L x≤DeficitCoeff/40^2*N^2) :
    (6743/50:ℝ)*L-(407/50:ℝ)*x≤(39/20:ℝ)*N ∧
      -(407/50:ℝ)*L+(6743/50:ℝ)*x≤(39/20:ℝ)*N := by
  have hr := profile_right_rayleigh L x
  have hl := profile_left_rayleigh L x
  have hmulr := mul_le_mul_of_nonneg_left hprofile
    (by norm_num : (0:ℝ)≤1680980263391/8397500)
  have hmull := mul_le_mul_of_nonneg_left hprofile
    (by norm_num : (0:ℝ)≤927103024991/8397500)
  have hcr : (1680980263391/8397500:ℝ)*(DeficitCoeff/40^2)≤(39/20:ℝ)^2 := by
    norm_num [DeficitCoeff]
  have hcl : (927103024991/8397500:ℝ)*(DeficitCoeff/40^2)≤(39/20:ℝ)^2 := by
    norm_num [DeficitCoeff]
  have hcrN := mul_le_mul_of_nonneg_right hcr (sq_nonneg N)
  have hclN := mul_le_mul_of_nonneg_right hcl (sq_nonneg N)
  have hsr : ((6743/50:ℝ)*L-(407/50:ℝ)*x)^2≤((39/20:ℝ)*N)^2 := by
    nlinarith only [hr,hmulr,hcrN]
  have hsl : (-(407/50:ℝ)*L+(6743/50:ℝ)*x)^2≤((39/20:ℝ)*N)^2 := by
    nlinarith only [hl,hmull,hclN]
  constructor
  · by_cases h : 0≤(6743/50:ℝ)*L-(407/50:ℝ)*x
    · exact (sq_le_sq₀ h (by positivity)).mp hsr
    · have hh : 0≤(39/20:ℝ)*N := by positivity
      linarith only [h,hh]
  · by_cases h : 0≤-(407/50:ℝ)*L+(6743/50:ℝ)*x
    · exact (sq_le_sq₀ h (by positivity)).mp hsl
    · have hh : 0≤(39/20:ℝ)*N := by positivity
      linarith only [h,hh]

theorem bad13_nontruncated_arm_margins {N L R m : ℕ}
    (hN : 3000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hm : N<11*m) (hcap : m≤(L+N-R)+(R-L+1)/13)
    (hprofile : ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      DeficitCoeff/40^2*(N:ℝ)^2) :
    50*((L+N-R)+(R-L+1)/13-m)+(L+N-R)≤50*(L-1) ∧
      50*((L+N-R)+(R-L+1)/13-m)+(L+N-R)≤50*(N-R) := by
  let w := L+N-R
  let M := R-L+1
  let b := w+M/13-m
  have hMw : M+w=N+1 := by dsimp only [M,w];omega
  have hdiv := Nat.mul_div_le M 13
  have hcap' : m≤w+M/13 := hcap
  have hsub : b+m=w+M/13 := Nat.sub_add_cancel hcap'
  have hd : 143*b+2*N+2≤132*w := by nlinarith only [hsub,hdiv,hMw,hm]
  have hdR : (2:ℝ)*N+143*(b:ℝ)+2≤132*(w:ℝ) := by
    exact_mod_cast (show 2*N+143*b+2≤132*w by omega)
  have hwr : (w:ℝ)=(L:ℝ)+((N-R:ℕ):ℝ) := by
    exact_mod_cast (show w=L+(N-R) by dsimp only [w];omega)
  have hLm1 : ((L-1:ℕ):ℝ)=(L:ℝ)-1 := by
    rw [Nat.cast_sub hL]
    norm_num
  have hn : (3000:ℝ)≤N := by exact_mod_cast hN
  have hlin := profile_linear_bounds (Nat.cast_nonneg N) hprofile
  change 50*b+w≤50*(L-1) ∧ 50*b+w≤50*(N-R)
  constructor
  · by_contra hh
    have hf : (50:ℝ)*((L-1:ℕ):ℝ)<50*(b:ℝ)+(w:ℝ) := by
      exact_mod_cast (show 50*(L-1)<50*b+w by omega)
    have hg : (2:ℝ)*N < -(407/50:ℝ)*L+(6743/50:ℝ)*((N-R:ℕ):ℝ)+141 := by
      nlinarith only [hdR,hf,hwr,hLm1]
    nlinarith only [hg,hlin.2,hn]
  · by_contra hh
    have hf : (50:ℝ)*((N-R:ℕ):ℝ)<50*(b:ℝ)+(w:ℝ) := by
      exact_mod_cast (show 50*(N-R)<50*b+w by omega)
    have hg : (2:ℝ)*N < (6743/50:ℝ)*L-(407/50:ℝ)*((N-R:ℕ):ℝ) := by
      nlinarith only [hdR,hf,hwr]
    nlinarith only [hg,hlin.1,hn]

theorem actual_short_source_minimum_cap {N L R m : ℕ} {S : Finset ℤ}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hS : S⊆Ground N)
    (hm : m≤S.card)
    (hshort : (S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤(R-L+1)/13+1) :
    m≤(L+N-R)+(R-L+1)/13 := by
  let I := Finset.Icc (L:ℤ) (R:ℤ)
  let O := Ground N\I
  have hs := Finset.card_sdiff_add_card_inter S I
  have hsub : S\I⊆O := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hS (Finset.mem_sdiff.mp hx).1,(Finset.mem_sdiff.mp hx).2⟩
  have hc := Finset.card_le_card hsub
  have hext := ground_interval_exterior_card N (by exact_mod_cast hL : (1:ℤ)≤L)
    (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
  have hOc : O.card+1=L+N-R := by dsimp only [O,I];omega
  change (S∩I).card≤(R-L+1)/13+1 at hshort
  omega

theorem actual_bad13_nonempty_arm_margins {N L R m : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 3000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hF : Legal (Ground N) F) (hEF : E⊆F) (hne : E.Nonempty)
    (hminimum : ∀S∈E,m≤S.card) (hm : N<11*m)
    (hshort : ∀S∈E,(S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤(R-L+1)/13+1)
    (hprofile : ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      DeficitCoeff/40^2*(N:ℝ)^2) :
    50*((L+N-R)+(R-L+1)/13-m)+(L+N-R)≤50*(L-1) ∧
      50*((L+N-R)+(R-L+1)/13-m)+(L+N-R)≤50*(N-R) := by
  obtain ⟨S,hSE⟩ := hne
  have hcap := actual_short_source_minimum_cap hL hLR hRN (hF.1 S (hEF hSE))
    (hminimum S hSE) (hshort S hSE)
  exact bad13_nontruncated_arm_margins hN hL hLR hRN hm hcap hprofile

#print axioms profile_right_rayleigh
#print axioms profile_left_rayleigh
#print axioms profile_linear_bounds
#print axioms bad13_nontruncated_arm_margins
#print axioms actual_short_source_minimum_cap
#print axioms actual_bad13_nonempty_arm_margins
end
end JSP233.ProfileArms117
