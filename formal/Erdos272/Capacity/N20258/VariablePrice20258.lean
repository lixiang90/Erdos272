module

public import Erdos272.Capacity.N20258.ResidueJoint20258

@[expose] public section
namespace JSP233.VariablePrice20258
open StarCompletion APClasses88404 IntrinsicTriples208 ResidueCapacity20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- After multiplication by the price, the response is cubic in the ground
width and the price. Its five coefficients work for every ground and price. -/
def bound {K : Type*} [Field K] (n x : K) : K :=
  112321/1000000*n^2*x + 2714/1000*n*x + 120406/1000000*x^3 +
  138655/1000000*n^3 + 99/1000*n^2 + 63/100*n + 1

private def quadratic (d : ℕ) : ℚ := if d=1 then 0 else 1/(4*(d:ℚ)^2)
private def linear (d : ℕ) : ℚ := 1/(d:ℚ)
private def peak (d : ℕ) : ℚ := if d=1 then 1/(12*(beta d)^2) else 0
private def cubic (d : ℕ) : ℚ := if d=1 then 0 else -(beta d)/(6*(d:ℚ)^3)
private def fringe (d : ℕ) : ℚ := beta d/(6*(d:ℚ))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem coefficients :
    (∑ d ∈ steps, quadratic d) ≤ (112321/1000000:ℚ) ∧
    (∑ d ∈ steps, linear d) ≤ (2714/1000:ℚ) ∧
    (∑ d ∈ steps, peak d) ≤ (120406/1000000:ℚ) ∧
    (∑ d ∈ steps, cubic d)+1/6 ≤ (138655/1000000:ℚ) ∧
    (∑ d ∈ steps, fringe d) ≤ (42/100:ℚ) := by decide +kernel

private theorem grid_mono {w u x a : ℝ} (hw : 0≤w) (wu : w≤u) (ux : u≤x)
    (ha : 0≤a) (au : a≤1) :
    w*x+a*w/6+w^2*x/4-a*w^3/6 ≤ u*x+a*u/6+u^2*x/4-a*u^3/6 := by
  have hu := hw.trans wu
  have hx := hu.trans ux
  have sq : 0≤u^2+u*w+w^2 := by positivity
  have weight := mul_le_mul_of_nonneg_right au sq
  have u2 := mul_le_mul_of_nonneg_right ux hu
  have w2 := mul_le_mul_of_nonneg_right (wu.trans ux) hw
  have uw := mul_le_mul_of_nonneg_right ux hw
  have uw' := mul_le_mul_of_nonneg_right (wu.trans ux) hu
  have slope : 0≤12*x+2*a+3*x*(u+w)-2*a*(u^2+u*w+w^2) := by
    nlinarith only [weight,u2,w2,uw,uw',hx,ha]
  nlinarith only [mul_nonneg (sub_nonneg.mpr wu) slope]

private theorem class_bound {N d : ℕ} {x : ℝ} (lo : 2≤N) (hd : d∈steps)
    (hx : 0<x) (span : ((N-1 : ℕ) : ℝ)≤2*x) :
    let n : ℝ := ((N-1 : ℕ) : ℝ)
    ResidueJoint20258.response N d x*x ≤
      (quadratic d : ℝ)*(n^2*x)+(linear d : ℝ)*(n*x)+(peak d : ℝ)*x^3+
      (cubic d : ℝ)*n^3+(fringe d : ℝ)*n := by
  dsimp only
  let n : ℝ := ((N-1 : ℕ) : ℝ)
  let a : ℝ := (beta d : ℝ)
  have hn : 0≤n := Nat.cast_nonneg _
  have dp : 0<(d:ℝ) := by exact_mod_cast positive hd
  obtain ⟨low,high⟩ := ResidueJoint20258.beta_range hd
  have al : 0<a := by dsimp only [a]; exact_mod_cast low
  have au : a≤1 := by dsimp only [a]; exact_mod_cast high
  by_cases unit : d=1
  · subst d
    simp only [ResidueJoint20258.response,quadratic,linear,peak,cubic,fringe,ite_true,
      Nat.div_one,Nat.cast_one,Rat.cast_zero,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,
      Rat.cast_one,Rat.cast_mul]
    change (n+a*n/(6*x)+x^2/(12*a^2))*x ≤ _
    change _ ≤ 0*(n^2*x)+1/1*(n*x)+1/(12*a^2)*x^3+0*n^3+a/(6*1)*n
    apply le_of_eq
    field_simp [al.ne',hx.ne'] <;> ring
  · let w : ℝ := (((N-1)/d : ℕ) : ℝ)
    let u : ℝ := n/d
    have wu : w≤u := (le_div_iff₀ dp).mpr (by dsimp only [w,n]; exact_mod_cast Nat.div_mul_le_self (N-1) d)
    have two : (2:ℝ)≤d := by exact_mod_cast (show 2≤d by have := positive hd; omega)
    have ux : u≤x := (div_le_div_of_nonneg_left hn (by norm_num : (0:ℝ)<2) two).trans
      (by change n≤2*x at span; linarith only [span])
    have mo := grid_mono (Nat.cast_nonneg _ : 0≤w) wu ux al.le au
    simp only [ResidueJoint20258.response,quadratic,linear,peak,cubic,fringe,if_neg unit,
      Rat.cast_zero,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast,
      Rat.cast_one,Rat.cast_mul,Rat.cast_neg,zero_mul,add_zero]
    change (w+a*w/(6*x)+(w^2/4-a*w^3/(6*x)))*x ≤
      1/(4*(d:ℝ)^2)*(n^2*x)+1/(d:ℝ)*(n*x)+ -a/(6*(d:ℝ)^3)*n^3+a/(6*(d:ℝ))*n
    calc
      _ = w*x+a*w/6+w^2*x/4-a*w^3/6 := by field_simp [hx.ne'] <;> ring
      _ ≤ _ := mo
      _ = _ := by dsimp only [u]; field_simp [dp.ne'] <;> ring

/-- Pay all private triples and the nineteen selected AP classes with one
polynomial, including when a previously proved geometric bank fixes the price. -/
theorem actual {N : ℕ} {F : Finset (Finset ℤ)} {x : ℝ} (lo : 62≤N) (hx : 0<x)
    (span : ((N-1 : ℕ) : ℝ)≤2*x) (legal : Legal (Ground N) F) :
    (∑ d ∈ steps, ((StepAP F d).card : ℝ))*x+(∑ S ∈ F, ((Pool S).card : ℝ)) ≤
      bound ((N-1 : ℕ) : ℝ) x := by
  let n : ℝ := ((N-1 : ℕ) : ℝ)
  have hn : 0≤n := Nat.cast_nonneg _
  have eqN : (N:ℝ)=n+1 := by dsimp only [n]; exact_mod_cast (show N=N-1+1 by omega)
  have paid := ResidueJoint20258.priced_classes (by omega : 1≤N) hx (by linarith only [span,eqN]) legal
  have choose : (N.choose 3 : ℝ)=(n^3-n)/6 := by rw [APResidual208.cast_choose_three,eqN]; ring
  rw [choose,eqN] at paid
  have mul := mul_le_mul_of_nonneg_right paid hx.le
  rw [add_mul,add_mul,div_mul_cancel₀ _ hx.ne',div_mul_cancel₀ _ hx.ne'] at mul
  have sum := Finset.sum_le_sum (fun d hd => class_bound (by omega : 2≤N) hd hx span)
  simp only [Finset.sum_add_distrib,←Finset.sum_mul] at sum
  change (∑ d ∈ steps, ResidueJoint20258.response N d x)*x ≤
    (∑ d ∈ steps, (quadratic d : ℝ))*(n^2*x)+(∑ d ∈ steps, (linear d : ℝ))*(n*x)+
    (∑ d ∈ steps, (peak d : ℝ))*x^3+(∑ d ∈ steps, (cubic d : ℝ))*n^3+
    (∑ d ∈ steps, (fringe d : ℝ))*n at sum
  obtain ⟨q,l,p,c,f⟩ := coefficients
  have qr := (Rat.cast_le (K := ℝ)).mpr q
  have lr := (Rat.cast_le (K := ℝ)).mpr l
  have pr := (Rat.cast_le (K := ℝ)).mpr p
  have cr := (Rat.cast_le (K := ℝ)).mpr c
  have fr := (Rat.cast_le (K := ℝ)).mpr f
  push_cast at qr lr pr cr fr
  have qh := mul_le_mul_of_nonneg_right qr (show 0≤n^2*x by positivity)
  have lh := mul_le_mul_of_nonneg_right lr (mul_nonneg hn hx.le)
  have ph := mul_le_mul_of_nonneg_right pr (pow_nonneg hx.le 3)
  have ch := mul_le_mul_of_nonneg_right cr (pow_nonneg hn 3)
  have fh := mul_le_mul_of_nonneg_right fr hn
  change _ ≤ bound n x
  unfold bound
  nlinarith only [mul,sum,qh,lh,ph,ch,fh,hn]

#print axioms actual
end
end JSP233.VariablePrice20258
