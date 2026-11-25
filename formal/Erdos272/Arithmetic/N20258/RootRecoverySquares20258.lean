module

public import Mathlib.Basic.Real.Basic
public import Erdos272.Foundation.ProofTactics

@[expose] public section
namespace JSP233.RootRecoverySquares20258
noncomputable section
set_option autoImplicit false

/-- Lower bound for a quadratic polynomial in the two fringe lengths. -/
private theorem rectangle (A B Z X Y K l b : ℝ)
    (pos : 0 < A) (det : 0 < A*Z-B^2)
    (cost : Z*X^2-2*B*X*Y+A*Y^2 ≤ 4*(A*Z-B^2)*K) :
    -K ≤ A*l^2+2*B*l*b+Z*b^2-X*l-Y*b := by
  by_contra! h
  have diff := mul_lt_mul_of_pos_left h (show 0 < 4*A*(A*Z-B^2) by positivity)
  have s := mul_nonneg det.le (sq_nonneg (2*A*l+2*B*b-X))
  have t := sq_nonneg (2*(A*Z-B^2)*b+B*X-A*Y)
  have c := mul_le_mul_of_nonneg_left cost pos.le
  nlinarith only [diff,s,t,c]

/-- The remaining root coordinate varies over a closed interval. -/
private theorem root_interval {base slope q c L : ℝ}
    (q0 : 0 ≤ q) (c0 : 0 ≤ c) (cl : c ≤ L)
    (left : 0 < base) (right : 0 < base+slope*L-q*L^2) :
    0 < base+slope*c-q*c^2 := by
  have chord := mul_nonneg q0 (mul_nonneg c0 (sub_nonneg.mpr cl))
  by_cases h : 0 ≤ slope-q*L
  · nlinarith only [left,chord,mul_nonneg c0 h]
  · have step := mul_nonneg (sub_nonneg.mpr cl) (show 0 ≤ q*L-slope by linarith only [h])
    nlinarith only [right,chord,step]

def profile (l b : ℝ) := (23359/80000)*l^2-(129/200)*l*b+b^2/2

/-- The smaller grounds admit the fifteenth dyadic harmonic cap. -/
def rate (n : ℝ) : ℝ := if n < 20000 then 584/25 else 49/2

private def balance (d m k rate n : ℝ) :=
  d*n^2-(44+m*rate)*n-(k+872*m)

private theorem increasing {d m k r a n : ℝ} (lo : a ≤ n) (dp : 0 ≤ d)
    (derivative : 0 ≤ 2*d*a-(44+m*r)) :
    balance d m k r a ≤ balance d m k r n := by
  have square := mul_nonneg dp (sq_nonneg (n-a))
  have line := mul_nonneg derivative (sub_nonneg.mpr lo)
  unfold balance
  nlinarith only [square,line]

private theorem lower_balance {d m k lower n : ℝ} (lo : 19227 ≤ n) (dp : 0 ≤ d)
    (early : lower < balance d m k (584/25) 19227)
    (later : lower < balance d m k (49/2) 20000)
    (earlySlope : 0 ≤ 2*d*19227-(44+m*(584/25)))
    (laterSlope : 0 ≤ 2*d*20000-(44+m*(49/2))) :
    lower < balance d m k (rate n) n := by
  by_cases h : n < 20000
  · simpa only [rate,if_pos h] using early.trans_le (increasing lo dp earlySlope)
  · simpa only [rate,if_neg h] using later.trans_le (increasing (le_of_not_gt h) dp laterSlope)

/-- The nonunit omitter obstruction is impossible throughout the full range
of the coarse raw profile. Both endpoint squares use the same multiplier. -/
theorem no_nonunit {n l b c : ℝ} (lo : 19227 ≤ n) (c0 : 0 ≤ c) (cl : c ≤ l)
    (raw : profile l b ≤ rate n*n+71*l+12*b+872)
    (obstruction : (1/8-1/242)*n^2 ≤ 44*n+
      2*((31/20)*l*b-c*b+3*(l+b)+10)+(109/50)*c^2+207*c+9100) : False := by
  let A : ℝ := 42*(23359/80000)
  let B : ℝ := (-42*(129/200)-31/10)/2
  let X : ℝ := 42*71+6
  let Y : ℝ := 42*12+6
  let t := balance (1/8-1/242) 42 9120 (rate n) n
  have t0 : 5100000 < t := lower_balance lo (by norm_num)
    (by norm_num [balance]) (by norm_num [balance]) (by norm_num) (by norm_num)
  have z := rectangle A B 21 X Y 5100000 l b
    (by norm_num [A]) (by norm_num [A,B]) (by norm_num [A,B,X,Y])
  have h := rectangle (A-109/50) (B+1) 21 (X+207) Y 5100000 l b
    (by norm_num [A]) (by norm_num [A,B]) (by norm_num [A,B,X,Y])
  let base := t+A*l^2+2*B*l*b+21*b^2-X*l-Y*b
  have pos := root_interval (base := base) (slope := 2*b-207) (q := 109/50)
    (by norm_num) c0 cl (by dsimp [base]; linarith only [t0,z])
    (by dsimp [base]; linarith only [t0,h])
  dsimp only [base,t,A,B,X,Y,balance] at pos
  unfold profile at raw
  linarith only [pos,obstruction,raw]

/-- Once the avoiders are intervals, a second pair of squares rules out
every omitted member of size at most two thirds of the ground set. -/
theorem no_two_thirds {n l b c : ℝ} (lo : 19227 ≤ n) (c0 : 0 ≤ c) (cl : c ≤ l)
    (raw : profile l b ≤ rate n*n+71*l+12*b+872)
    (obstruction : (1/18-1/242)*n^2 ≤ 44*n+
      2*((l-c)*(b+1))+(109/50)*c^2+207*c+9100) : False := by
  let A : ℝ := 31*(23359/80000)
  let B : ℝ := (-31*(129/200)-2)/2
  let X : ℝ := 31*71+2
  let Y : ℝ := 31*12
  let t := balance (1/18-1/242) 31 9100 (rate n) n
  have t0 : 4200000 < t := lower_balance lo (by norm_num)
    (by norm_num [balance]) (by norm_num [balance]) (by norm_num) (by norm_num)
  have z := rectangle A B (31/2) X Y 4200000 l b
    (by norm_num [A]) (by norm_num [A,B]) (by norm_num [A,B,X,Y])
  have h := rectangle (A-109/50) (B+1) (31/2) (X+207) Y 4200000 l b
    (by norm_num [A]) (by norm_num [A,B]) (by norm_num [A,B,X,Y])
  let base := t+A*l^2+2*B*l*b+(31/2)*b^2-X*l-Y*b
  have pos := root_interval (base := base) (slope := 2*b-207) (q := 109/50)
    (by norm_num) c0 cl (by dsimp [base]; linarith only [t0,z])
    (by dsimp [base]; linarith only [t0,h])
  dsimp only [base,t,A,B,X,Y,balance] at pos
  unfold profile at raw
  linarith only [pos,obstruction,raw,c0]

#print axioms no_nonunit
#print axioms no_two_thirds
end
end JSP233.RootRecoverySquares20258
