module

public import Erdos272.Resources.ProfileArms117
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! The same complete actual endpoint profile pays both physical arm gates
for the rational width 399/10. The p12 branch retains its stronger actual
minimum-size premise; a real short source justifies every subtraction. -/
namespace JSP233.ProfileArms118
open StarCompletion APGeometry DenseDeletion40 LongTerminal35
open RawEndpoint112 RawEndpoint115 ProfileArms117
open ThinFringe33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem profile_linear_rayleigh (a b L x : ℝ) :
    (a*L+b*x)^2≤((40000*a^2+51600*a*b+23359*b^2)/3359)*ProfileDeficit L x := by
  have he : ((40000*a^2+51600*a*b+23359*b^2)/3359)*ProfileDeficit L x-(a*L+b*x)^2=
      (1/(80000*3359):ℝ)*((-25800*a-23359*b)*L+(40000*a+25800*b)*x)^2 := by
    dsimp only [ProfileDeficit];ring
  have hs : 0≤(1/(80000*3359):ℝ)*((-25800*a-23359*b)*L+(40000*a+25800*b)*x)^2 := by positivity
  linarith only [he,hs]

theorem profile_linear_bound {N L x a b q : ℝ} (hN : 0≤N) (hq : 0≤q)
    (hc : 0≤(40000*a^2+51600*a*b+23359*b^2)/3359)
    (hco : ((40000*a^2+51600*a*b+23359*b^2)/3359)*DeficitCoeff/(399/10:ℝ)^2≤q^2)
    (hp : ProfileDeficit L x≤DeficitCoeff/(399/10:ℝ)^2*N^2) : a*L+b*x≤q*N := by
  have hr := profile_linear_rayleigh a b L x
  have hm := mul_le_mul_of_nonneg_left hp hc
  have hn := mul_le_mul_of_nonneg_right hco (sq_nonneg N)
  have hs : (a*L+b*x)^2≤(q*N)^2 := by
    calc
      _≤((40000*a^2+51600*a*b+23359*b^2)/3359)*ProfileDeficit L x := hr
      _≤((40000*a^2+51600*a*b+23359*b^2)/3359)*(DeficitCoeff/(399/10:ℝ)^2*N^2) := hm
      _=(((40000*a^2+51600*a*b+23359*b^2)/3359)*DeficitCoeff/(399/10:ℝ)^2)*N^2 := by ring
      _≤q^2*N^2 := hn
      _=(q*N)^2 := by ring
  by_cases h : 0≤a*L+b*x
  · exact (sq_le_sq₀ h (mul_nonneg hq hN)).mp hs
  · have hz := mul_nonneg hq hN
    linarith only [h,hz]

theorem bad13_nontruncated_arm_margins {N L R m : ℕ}
    (hN : 3000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hm : N<11*m) (hcap : m≤(L+N-R)+(R-L+1)/13)
    (hprofile : ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      DeficitCoeff/(399/10:ℝ)^2*(N:ℝ)^2) :
    50*((L+N-R)+(R-L+1)/13-m)+(L+N-R)≤50*(L-1) ∧
      50*((L+N-R)+(R-L+1)/13-m)+(L+N-R)≤50*(N-R) := by
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
  have hn : (3000:ℝ)≤N := by exact_mod_cast hN
  have hlinR := profile_linear_bound (a:=(6743/50:ℝ)) (b:=(-407/50:ℝ))
    (q:=(39/20:ℝ)) (Nat.cast_nonneg N) (by norm_num) (by norm_num)
    (by norm_num [DeficitCoeff]) hprofile
  have hlinL := profile_linear_bound (a:=(-407/50:ℝ)) (b:=(6743/50:ℝ))
    (q:=(39/20:ℝ)) (Nat.cast_nonneg N) (by norm_num) (by norm_num)
    (by norm_num [DeficitCoeff]) hprofile
  change 50*b+w≤50*(L-1) ∧ 50*b+w≤50*(N-R)
  constructor
  · by_contra hh
    have hf : (50:ℝ)*((L-1:ℕ):ℝ)<50*(b:ℝ)+(w:ℝ) := by
      exact_mod_cast (show 50*(L-1)<50*b+w by omega)
    have hg : (2:ℝ)*N < -(407/50:ℝ)*L+(6743/50:ℝ)*((N-R:ℕ):ℝ)+141 := by
      nlinarith only [hdR,hf,hwr,hLm1]
    nlinarith only [hg,hlinL,hn]
  · by_contra hh
    have hf : (50:ℝ)*((N-R:ℕ):ℝ)<50*(b:ℝ)+(w:ℝ) := by
      exact_mod_cast (show 50*(N-R)<50*b+w by omega)
    have hg : (2:ℝ)*N < (6743/50:ℝ)*L-(407/50:ℝ)*((N-R:ℕ):ℝ) := by
      nlinarith only [hdR,hf,hwr]
    nlinarith only [hg,hlinR,hn]

theorem actual_bad13_nonempty_arm_margins {N L R m : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 3000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hF : Legal (Ground N) F) (hEF : E⊆F) (hne : E.Nonempty)
    (hminimum : ∀S∈E,m≤S.card) (hm : N<11*m)
    (hshort : ∀S∈E,(S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤(R-L+1)/13+1)
    (hprofile : ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      DeficitCoeff/(399/10:ℝ)^2*(N:ℝ)^2) :
    50*((L+N-R)+(R-L+1)/13-m)+(L+N-R)≤50*(L-1) ∧
      50*((L+N-R)+(R-L+1)/13-m)+(L+N-R)≤50*(N-R) := by
  obtain ⟨S,hSE⟩ := hne
  have hcap := ProfileArms117.actual_short_source_minimum_cap hL hLR hRN
    (hF.1 S (hEF hSE)) (hminimum S hSE) (hshort S hSE)
  exact bad13_nontruncated_arm_margins hN hL hLR hRN hm hcap hprofile

theorem actual_short12_source_minimum_cap {N L R m : ℕ} {S : Finset ℤ}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hS : S⊆Ground N)
    (hm : m≤S.card)
    (hshort : (S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤(R-L+1)/12+1) :
    m≤(L+N-R)+(R-L+1)/12 := by
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
  change (S∩I).card≤(R-L+1)/12+1 at hshort
  omega

theorem bad12_nontruncated_arm_margins {N L R m : ℕ}
    (hN : 5000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hm : 97*N<1000*m) (hcap : m≤(L+N-R)+(R-L+1)/12)
    (hprofile : ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      DeficitCoeff/(399/10:ℝ)^2*(N:ℝ)^2) :
    50*((L+N-R)+(R-L+1)/12-m)+(L+N-R)≤50*(L-1) ∧
      50*((L+N-R)+(R-L+1)/12-m)+(L+N-R)≤50*(N-R) := by
  let w := L+N-R
  let M := R-L+1
  let b := w+M/12-m
  have hMw : M+w=N+1 := by dsimp only [M,w];omega
  have hdiv := Nat.mul_div_le M 12
  have hsub : b+m=w+M/12 := Nat.sub_add_cancel hcap
  have hd : 3000*b+41*N≤2750*w+250 := by nlinarith only [hsub,hdiv,hMw,hm]
  have hdR : (3000:ℝ)*b+41*N≤2750*(w:ℝ)+250 := by exact_mod_cast hd
  have hwr : (w:ℝ)=(L:ℝ)+((N-R:ℕ):ℝ) := by
    exact_mod_cast (show w=L+(N-R) by dsimp only [w];omega)
  have hLm1 : ((L-1:ℕ):ℝ)=(L:ℝ)-1 := by
    rw [Nat.cast_sub hL];norm_num
  have hn : (5000:ℝ)≤N := by exact_mod_cast hN
  have hlinR := profile_linear_bound (a:=(2810:ℝ)) (b:=(-190:ℝ))
    (q:=(40:ℝ)) (Nat.cast_nonneg N) (by norm_num) (by norm_num)
    (by norm_num [DeficitCoeff]) hprofile
  have hlinL := profile_linear_bound (a:=(-190:ℝ)) (b:=(2810:ℝ))
    (q:=(40:ℝ)) (Nat.cast_nonneg N) (by norm_num) (by norm_num)
    (by norm_num [DeficitCoeff]) hprofile
  change 50*b+w≤50*(L-1) ∧ 50*b+w≤50*(N-R)
  constructor
  · by_contra hh
    have hf : (50:ℝ)*((L-1:ℕ):ℝ)<50*(b:ℝ)+(w:ℝ) := by
      exact_mod_cast (show 50*(L-1)<50*b+w by omega)
    have hg : (41:ℝ)*N < -(190:ℝ)*L+(2810:ℝ)*((N-R:ℕ):ℝ)+3250 := by
      nlinarith only [hdR,hf,hwr,hLm1]
    nlinarith only [hg,hlinL,hn]
  · by_contra hh
    have hf : (50:ℝ)*((N-R:ℕ):ℝ)<50*(b:ℝ)+(w:ℝ) := by
      exact_mod_cast (show 50*(N-R)<50*b+w by omega)
    have hg : (41:ℝ)*N < (2810:ℝ)*L-(190:ℝ)*((N-R:ℕ):ℝ)+250 := by
      nlinarith only [hdR,hf,hwr]
    nlinarith only [hg,hlinR,hn]

theorem actual_bad12_nonempty_arm_margins {N L R m : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 5000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hF : Legal (Ground N) F) (hEF : E⊆F) (hne : E.Nonempty)
    (hminimum : ∀S∈E,m≤S.card) (hm : 97*N<1000*m)
    (hshort : ∀S∈E,(S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤(R-L+1)/12+1)
    (hprofile : ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      DeficitCoeff/(399/10:ℝ)^2*(N:ℝ)^2) :
    50*((L+N-R)+(R-L+1)/12-m)+(L+N-R)≤50*(L-1) ∧
      50*((L+N-R)+(R-L+1)/12-m)+(L+N-R)≤50*(N-R) := by
  obtain ⟨S,hSE⟩ := hne
  have hcap := actual_short12_source_minimum_cap hL hLR hRN
    (hF.1 S (hEF hSE)) (hminimum S hSE) (hshort S hSE)
  exact bad12_nontruncated_arm_margins hN hL hLR hRN hm hcap hprofile

#print axioms profile_linear_rayleigh
#print axioms profile_linear_bound
#print axioms bad13_nontruncated_arm_margins
#print axioms actual_bad13_nonempty_arm_margins
#print axioms actual_short12_source_minimum_cap
#print axioms bad12_nontruncated_arm_margins
#print axioms actual_bad12_nonempty_arm_margins
end
end JSP233.ProfileArms118
