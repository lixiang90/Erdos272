module

public import Erdos272.Certificates.EndpointFinite208.Block039

@[expose] public section
namespace JSP233.SquareEndpoint208
open HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped BigOperators
noncomputable section
set_option autoImplicit false

private theorem succH (n : ℕ) : Harmonic (n+1)=Harmonic n+1/((n:ℝ)+1) := by
  unfold Harmonic
  rw [Finset.sum_Icc_succ_top (by omega : 1≤n+1)]
  push_cast
  rfl

/-- Pair the first and last reciprocal around their arithmetic mean. -/
private theorem paired (a k : ℕ) :
    (2*(k:ℝ)+1)/((a:ℝ)+k+1)≤Harmonic (a+2*k+1)-Harmonic a := by
  induction k generalizing a with
  | zero => simp [succH]
  | succ k ih =>
    have inner := ih (a+1)
    push_cast at inner ⊢
    have left : (0:ℝ)<(a:ℝ)+1 := by positivity
    have right : (0:ℝ)<(a:ℝ)+2*k+3 := by positivity
    have mid : (0:ℝ)<(a:ℝ)+k+2 := by positivity
    have ends : 2/((a:ℝ)+k+2)≤1/((a:ℝ)+1)+1/((a:ℝ)+2*k+3) := by
      field_simp
      nlinarith only [sq_nonneg ((k:ℝ)+1)]
    rw [show a+2*(k+1)+1=(a+1+2*k+1)+1 by omega,succH]
    rw [succH a] at inner
    push_cast
    rw [show (a:ℝ)+1+k+1=(a:ℝ)+k+2 by ring] at inner
    have result : (2*((k:ℝ)+1)+1)/((a:ℝ)+k+2)≤
        Harmonic (a+1+2*k+1)+1/((a:ℝ)+2*k+3)-Harmonic a := by
      rw [show (2*((k:ℝ)+1)+1)/((a:ℝ)+k+2)=
        (2*k+1)/((a:ℝ)+k+2)+2/((a:ℝ)+k+2) by ring]
      linarith only [inner,ends]
    convert result using 1 <;> ring_nf

theorem square_step (r : ℕ) (pos : 1≤r) :
    2*Harmonic (r+1)-Harmonic ((r+1)^2)≤2*Harmonic r-Harmonic (r^2) := by
  have shell := paired (r^2) r
  rw [show r^2+2*r+1=(r+1)^2 by ring] at shell
  push_cast at shell
  have gain : 2/((r:ℝ)+1)≤(2*r+1)/((r:ℝ)^2+r+1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [show (1:ℝ)≤r by exact_mod_cast pos]
  rw [succH]
  rw [show 2/((r:ℝ)+1)=2*(1/((r:ℝ)+1)) by ring] at gain
  linarith only [shell,gain]

private theorem scaled_upper (G n : ℕ) :
    (G:ℝ)*Harmonic n≤(FastDivSum G n:ℝ)+n := by
  induction n with
  | zero => simp [Harmonic,FastDivSum]
  | succ n ih =>
    have pos : (0:ℝ)<(n:ℝ)+1 := by positivity
    have divi : (G:ℝ)/((n:ℝ)+1)≤(G/(n+1):ℕ)+1 := by
      apply (div_le_iff₀ pos).mpr
      have h := (Nat.lt_mul_div_succ G (show 0<n+1 by omega)).le
      rw [mul_comm] at h
      exact_mod_cast h
    rw [succH,FastDivSum,mul_add,mul_one_div]
    push_cast
    linarith only [ih,divi]

set_option maxRecDepth 3000 in
private theorem anchor : 2*Harmonic 359-Harmonic (359^2)≤29/50 := by
  have finish := (EndpointFinite208.sound039 EndpointFinite208.prefix039).2
  have advance := fast_div_sum_add 1000000000000 128881 80
  simp only [show (128881+80:ℕ)=128961 by decide,show (128881+1:ℕ)=128882 by decide,
    show FastIntervalSum 1000000000000 128882 80=620532630 by decide +kernel] at advance
  have known : 12344484790341=FastDivSum 1000000000000 128881+620532630 := finish.trans advance
  have saved : FastDivSum 1000000000000 128881=12343864257711 := by omega
  have upper := scaled_upper 1000000000000 359
  have lower := scaled_harmonic_le 1000000000000 128881
  rw [show FastDivSum 1000000000000 359=6461930164315 by decide +kernel] at upper
  rw [saved] at lower
  change 2*Harmonic 359-Harmonic 128881≤29/50
  norm_num only [Nat.cast_ofNat] at upper lower
  linarith only [upper,lower]

private theorem tailH {a n U : ℕ} (an : a≤n) (nu : n≤U) :
    (n:ℝ)-a≤(U:ℝ)*(Harmonic n-Harmonic a) := by
  induction n,an using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have prev := ih (by omega)
    have inc : (1:ℝ)≤(U:ℝ)*(1/((n:ℝ)+1)) := by
      rw [mul_one_div,le_div_iff₀ (by positivity),one_mul]
      exact_mod_cast nu
    rw [succH]
    push_cast
    linarith only [prev,inc]

private theorem from_anchor {r : ℕ} (high : 359≤r) :
    2*Harmonic r-Harmonic (r^2)≤29/50 := by
  induction r,high using Nat.le_induction with
  | base => exact anchor
  | succ j hj ih => exact (square_step j (by omega)).trans ih

/-- Above the last finite block, one harmonic difference controls every
integer up to the next square. This argument has no upper ground cutoff. -/
theorem payment {U : ℕ} (big : 128961≤U) : (EndpointCount (U-1):ℝ)≤Payment U := by
  let t := U-1
  let r := Nat.sqrt t
  have tu : t+1=U := by dsimp [t]; omega
  have tR : (t:ℝ)+1=U := by exact_mod_cast tu
  have square : r^2≤t := by simpa only [r,pow_two] using Nat.sqrt_le t
  have next : t<(r+1)^2 := by simpa only [r,pow_two] using Nat.lt_succ_sqrt' t
  have high : 359≤r := by
    by_contra! small
    have := Nat.pow_le_pow_left (show r+1≤359 by omega) 2
    dsimp only [t] at next
    omega
  have mono := from_anchor high
  have extra := tailH (a:=r^2) (n:=U) (show r^2≤U by omega) le_rfl
  have hyp := Hyperbola131.actual_hyperbola_nat square next
  rw [←endpoint_divisor_identity,←fast_div_sum_eq] at hyp
  have exactCount : (EndpointCount t:ℝ)+t+(t/2:ℕ)+(r:ℝ)^2=2*(FastDivSum t r:ℝ) := by
    exact_mod_cast hyp
  have half : (t:ℝ)≤2*(t/2:ℕ)+1 := by exact_mod_cast (show t≤2*(t/2)+1 by omega)
  have divs := scaled_harmonic_le t r
  have scaled := mul_le_mul_of_nonneg_left mono (Nat.cast_nonneg (α:=ℝ) U)
  push_cast at extra
  change (EndpointCount t:ℝ)≤(U:ℝ)*(Harmonic U-48/25)+11
  nlinarith only [extra,exactCount,half,divs,scaled,HarmonicAbel29.harmonic_nonneg r,tR,
    congrArg (fun z : ℝ => z*Harmonic r) tR]

#print axioms square_step
#print axioms payment
end
end JSP233.SquareEndpoint208
