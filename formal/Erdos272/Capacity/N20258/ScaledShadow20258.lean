module

public import Erdos272.Capacity.N88404.SevenShadow88404
public import Erdos272.Arithmetic.HarmonicSharp39

@[expose] public section
namespace JSP233.ScaledShadow20258
open StarCompletion HarmonicAbel29 IntrinsicTriples208 SieveConstants88404
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- The same seven-stride estimate works at every multiplier 1/(kN) with k ≥ 3. -/
theorem actual {N : ℕ} {F : Finset (Finset ℤ)} {k : ℝ}
    (lo : 1000 ≤ N) (hi : N < 2^16) (hk : 3 ≤ k) (legal : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ)+6*(1/(k*(N : ℝ)))*(∑ S ∈ F, ((Pool S).card : ℝ)) ≤
      (129/800+(Alpha 1/k+k^2/(432*(Alpha 1)^2)))*(N : ℝ)^2+(61/5+3/k)*N := by
  let n : ℝ := N
  let g := 1/(k*n)
  have hn : (1 : ℝ) ≤ n := by
    change (1 : ℝ) ≤ (N : ℝ)
    exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : 0 < n := by linarith
  have hk0 : 0 < k := by linarith
  have hg : 0 < g := by dsimp [g]; positivity
  have scale : k*g*n=1 := by dsimp [g]; field_simp
  have cap : 3*g*(n-1) ≤ 1 := by
    nlinarith only [scale,hg.le,mul_nonneg (sub_nonneg.mpr hk) (mul_nonneg hg.le hn0.le)]
  have J := SevenShadow88404.actual_joint lo hg cap legal
  have harm : Harmonic N ≤ 61/5 := by
    have h := HarmonicSharp39.actual_harmonic_seven_tenths N 16 hi
    norm_num at h ⊢
    exact h
  have hcube := pow_le_pow_left₀ (by linarith : 0 ≤ n-1) (by linarith : n-1 ≤ n) 3
  have halpha := (alpha_range (by simp [Steps] : 1 ∈ Steps)).1
  have cubic := mul_le_mul_of_nonneg_left hcube (mul_nonneg halpha.le hg.le)
  have linear := mul_le_mul_of_nonneg_left harm hn0.le
  have eqn : (129/800+3*g)*n^2+n*(61/5)+Alpha 1*g*n^3+1/(432*(Alpha 1*g)^2) =
      (129/800+(Alpha 1/k+k^2/(432*(Alpha 1)^2)))*n^2+(61/5+3/k)*n := by
    dsimp only [g]
    field_simp [hk0.ne',hn0.ne',halpha.ne']
    ring
  change _+6*g*_ ≤ (129/800+3*g)*n^2+n*Harmonic N+Alpha 1*g*(n-1)^3+1/(432*(Alpha 1*g)^2) at J
  linarith only [J,cubic,linear,eqn]

#print axioms actual
end
end JSP233.ScaledShadow20258
