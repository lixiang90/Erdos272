module

public import Erdos272.Capacity.N20258.ResidueJoint20258

@[expose] public section
namespace JSP233.FiveSixths20258
open StarCompletion APClasses88404 IntrinsicTriples208 ResidueCapacity20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- Coefficients of the class response at triple price 5(N-1)/6.
Replacing the grid length by (N-1)/d leaves three constant sums. -/
def squareCoeff (d : ℕ) : ℚ :=
  if d=1 then 25/(432*(beta d)^2) else 1/(4*(d : ℚ)^2)-beta d/(5*(d : ℚ)^3)

def linearCoeff (d : ℕ) : ℚ := 1/(d : ℚ)
def constantCoeff (d : ℕ) : ℚ := beta d/(5*(d : ℚ))

private def polynomial (n a w : ℝ) := w+(a*w-a*w^3)/(5*n)+w^2/4

private theorem polynomial_mono {n a u w : ℝ} (hn : 0<n) (ha : 0≤a) (ha' : a≤1)
    (hw : 0≤w) (wu : w≤u) (size : u+w≤n) : polynomial n a w ≤ polynomial n a u := by
  have hu : 0≤u := hw.trans wu
  have square : 0≤u^2+u*w+w^2 := by positivity
  have cubic := mul_le_mul_of_nonneg_right ha' square
  have limit := mul_le_mul_of_nonneg_right size (add_nonneg hu hw)
  have slope : 0 ≤ 20*n+4*a+5*n*(u+w)-4*a*(u^2+u*w+w^2) := by
    nlinarith only [cubic,limit,hn,ha,mul_nonneg hu hw,mul_nonneg hn.le (add_nonneg hu hw)]
  have rise := mul_nonneg (sub_nonneg.mpr wu) slope
  have expand (t : ℝ) : 20*n*polynomial n a t=20*n*t+4*a*t-4*a*t^3+5*n*t^2 := by
    unfold polynomial
    field_simp [hn.ne'] <;> ring
  apply (mul_le_mul_iff_right₀ (show 0<20*n by positivity)).mp
  rw [expand,expand]
  nlinarith only [rise]

private theorem class_bound {N d : ℕ} (hN : 2≤N) (hd : d ∈ steps) :
    let n : ℝ := ((N-1 : ℕ) : ℝ)
    ResidueJoint20258.response N d (5*n/6) ≤
      (squareCoeff d : ℝ)*n^2+(linearCoeff d : ℝ)*n+(constantCoeff d : ℝ) := by
  dsimp only
  let n : ℝ := ((N-1 : ℕ) : ℝ)
  let a : ℝ := (beta d : ℝ)
  have hn : 0<n := by dsimp only [n]; exact_mod_cast (show 0<N-1 by omega)
  have hdpos := positive hd
  have dp : 0<(d : ℝ) := by exact_mod_cast hdpos
  obtain ⟨alo,aup⟩ := ResidueJoint20258.beta_range hd
  have al : 0<a := by dsimp only [a]; exact_mod_cast alo
  have au : a≤1 := by dsimp only [a]; exact_mod_cast aup
  by_cases unit : d=1
  · subst d
    simp only [ResidueJoint20258.response,squareCoeff,linearCoeff,constantCoeff,ite_true,
      Nat.div_one,Nat.cast_one,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_one]
    change n+a*n/(6*(5*n/6))+(5*n/6)^2/(12*a^2) ≤
      25/(432*a^2)*n^2+1/1*n+a/(5*1)
    apply le_of_eq
    field_simp [al.ne',hn.ne']
    <;> ring
  · let w : ℝ := (((N-1)/d : ℕ) : ℝ)
    let u : ℝ := n/d
    have hw : 0≤w := Nat.cast_nonneg _
    have wu : w≤u := (le_div_iff₀ dp).mpr (by dsimp only [w,n]; exact_mod_cast Nat.div_mul_le_self (N-1) d)
    have two : (2 : ℝ)≤d := by exact_mod_cast (show 2≤d by omega)
    have twice : u≤n/2 := by
      dsimp only [u]
      exact div_le_div_of_nonneg_left hn.le (by norm_num) two
    have mono := polynomial_mono hn al.le au hw wu (by linarith : u+w≤n)
    simp only [ResidueJoint20258.response,squareCoeff,linearCoeff,constantCoeff,if_neg unit,
      Rat.cast_sub,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_one,Rat.cast_natCast]
    change w+a*w/(6*(5*n/6))+(w^2/4-a*w^3/(6*(5*n/6))) ≤
      (1/(4*(d : ℝ)^2)-a/(5*(d : ℝ)^3))*n^2+1/(d : ℝ)*n+a/(5*(d : ℝ))
    calc
      _ = polynomial n a w := by unfold polynomial; field_simp [hn.ne'] <;> ring
      _ ≤ polynomial n a u := mono
      _ = _ := by unfold polynomial u; field_simp [dp.ne',hn.ne'] <;> ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem coefficients :
    (∑ d ∈ steps, squareCoeff d) + 1/5 ≤ (362323/1000000 : ℚ) ∧
    (∑ d ∈ steps, linearCoeff d) + 594/5000 ≤ (2834/1000 : ℚ) ∧
    (∑ d ∈ steps, constantCoeff d) ≤ (51/100 : ℚ) := by decide +kernel

/-- On every ground the nineteen selected classes and the private triple pools
obey the same quadratic bound, with no ground-specific sieve table. -/
theorem actual {N : ℕ} {F : Finset (Finset ℤ)} (hN : 62≤N) (legal : Legal (Ground N) F) :
    let n : ℝ := ((N-1 : ℕ) : ℝ)
    (∑ d ∈ steps, ((StepAP F d).card : ℝ))+(∑ S ∈ F, ((Pool S).card : ℝ))/(5*n/6) ≤
      (362323/1000000 : ℝ)*n^2+(2834/1000 : ℝ)*n+1 := by
  dsimp only
  let n : ℝ := ((N-1 : ℕ) : ℝ)
  have hn : 1≤n := by dsimp only [n]; exact_mod_cast (show 1≤N-1 by omega)
  have hp : 0<n := by linarith
  have eqN : (N : ℝ) = n+1 := by dsimp only [n]; exact_mod_cast (show N=N-1+1 by omega)
  have priced := ResidueJoint20258.priced_classes (by omega : 1≤N) (by positivity : 0<5*n/6)
    (by linarith : (N : ℝ)-1 ≤ 2*(5*n/6)) legal
  have sum := Finset.sum_le_sum fun d hd => class_bound (N := N) (by omega) hd
  simp only [Finset.sum_add_distrib,←Finset.sum_mul] at sum
  obtain ⟨q,l,c⟩ := coefficients
  have qr := (Rat.cast_le (K := ℝ)).mpr q
  have lr := (Rat.cast_le (K := ℝ)).mpr l
  have cr := (Rat.cast_le (K := ℝ)).mpr c
  push_cast at qr lr cr
  have quad := mul_le_mul_of_nonneg_right qr (sq_nonneg n)
  have lin := mul_le_mul_of_nonneg_right lr hp.le
  have choose : (N.choose 3 : ℝ)=(n^3-n)/6 := by
    rw [APResidual208.cast_choose_three,eqN]
    ring
  rw [choose,eqN] at priced
  have fee : ((n^3-n)/6+(99*(n+1-1)^2+210*(n+1-1)+120)/1000)/(5*n/6) ≤
      n^2/5+(594/5000)*n+49/100 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hn]
  change (∑ d ∈ steps, ResidueJoint20258.response N d (5*n/6)) ≤
    (∑ d ∈ steps, (squareCoeff d : ℝ))*n^2+
    (∑ d ∈ steps, (linearCoeff d : ℝ))*n+∑ d ∈ steps, (constantCoeff d : ℝ) at sum
  linarith only [priced,sum,fee,quad,lin,cr]

#print axioms actual
end
end JSP233.FiveSixths20258
