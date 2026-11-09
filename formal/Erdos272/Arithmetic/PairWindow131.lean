module

public import Erdos272.Arithmetic.PrefixState131
public import Erdos272.Arithmetic.CompleteSeven129
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace JSP233.PairWindow131
open PairWeighted131 PrefixState131 SimplexMoment57
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

structure Coeff where
  a : ℝ
  b : ℝ
  s : ℝ
  f : ℝ

def eval (c : Coeff) (N : ℕ) : ℝ :=
  (N:ℝ)*(c.a*Real.log N+c.b)+Real.sqrt N*c.s+c.f

def aL (G : ℕ) (s : State) : ℝ := (s.aLo:ℝ)/G
def aU (G : ℕ) (s : State) : ℝ := (s.aHi:ℝ)/G
def jL (G : ℕ) (s : State) : ℝ := (s.jLo:ℝ)/G
def jU (G : ℕ) (s : State) : ℝ := (s.jHi:ℝ)/G
def sU (G : ℕ) (s : State) : ℝ := (s.sHi:ℝ)/G

def chooseUpper (v al ah : ℝ) : ℝ := if 0≤v then ah else al
def chooseLower (v al ah : ℝ) : ℝ := if 0≤v then al else ah

def upperCut (G : ℕ) (sm sk : State) (r : ℕ) (ld : ℝ) : Coeff :=
  let v : ℝ := 39/250-ld
  ⟨2*aU G sm/(r:ℝ)^2,
    2*(v*chooseUpper v (aL G sm) (aU G sm)-jL G sm)/(r:ℝ)^2,
    4*sU G sm/(r:ℝ),-(sk.t:ℝ)^2⟩

def lowerCut (G : ℕ) (sm : State) (r : ℕ) (ld : ℝ) : Coeff :=
  let v : ℝ := 77/500-ld
  ⟨2*aL G sm/(r:ℝ)^2,
    2*(v*chooseLower v (aL G sm) (aU G sm)-jU G sm)/(r:ℝ)^2,
    -(4*sU G sm/(r:ℝ)),-(sm.t:ℝ)^2-9*(sm.t:ℝ)⟩

theorem valid_caps {G M : ℕ} {s : State} (hG : 0<G) (hs : Valid G M s) :
    aL G s≤A M ∧ A M≤aU G s ∧ jL G s≤J M ∧ J M≤jU G s ∧ S M≤sU G s ∧
      s.t=DivCount 1 M := by
  obtain ⟨_hll,_hlh,hal,hah,hjl,hjh,hsh,htt⟩ := hs
  have hp : (0:ℝ)<G := Nat.cast_pos.mpr hG
  dsimp only [aL,aU,jL,jU,sU]
  exact ⟨(div_le_iff₀ hp).mpr (by nlinarith only [hal]),
    (le_div_iff₀ hp).mpr (by nlinarith only [hah]),
    (div_le_iff₀ hp).mpr (by nlinarith only [hjl]),
    (le_div_iff₀ hp).mpr (by nlinarith only [hjh]),
    (le_div_iff₀ hp).mpr (by nlinarith only [hsh]),htt⟩

theorem a_nonnegative (M : ℕ) : 0≤A M := by
  dsimp only [A]
  positivity

theorem choose_upper_mul {a al ah v : ℝ} (hl : al≤a) (hu : a≤ah) :
    v*a≤v*chooseUpper v al ah := by
  by_cases hv : 0≤v
  · simpa only [chooseUpper,if_pos hv] using mul_le_mul_of_nonneg_left hu hv
  · simpa only [chooseUpper,if_neg hv] using mul_le_mul_of_nonpos_left hl (le_of_not_ge hv)

theorem choose_lower_mul {a al ah v : ℝ} (hl : al≤a) (hu : a≤ah) :
    v*chooseLower v al ah≤v*a := by
  by_cases hv : 0≤v
  · simpa only [chooseLower,if_pos hv] using mul_le_mul_of_nonneg_left hl hv
  · simpa only [chooseLower,if_neg hv] using mul_le_mul_of_nonpos_left hu (le_of_not_ge hv)

theorem actual_upper_cut {G N K M r : ℕ} {sm sk : State} {ld : ℝ}
    (hN : 1≤N) (hG : 0<G) (hm : Valid G M sm) (hk : Valid G K sk) (hr : 0<r)
    (hKM : K≤M) (hK : K^2*r^2≤N) (hM : N≤M^2*r^2)
    (hlog : ld≤Real.log ((r:ℝ)^2)) :
    (DivCount 3 (N/r^2):ℝ)≤eval (upperCut G sm sk r ld) N := by
  obtain ⟨hal,hah,hjl,_hjh,hsh,_htt⟩ := valid_caps hG hm
  obtain ⟨_hll,_hlh,_hkaL,_hkaH,_hkjL,_hkjH,_hks,hkt⟩ := hk
  have hrR : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hNp : (0:ℝ)<N := by linarith only [hN1]
  have hr2 : (0:ℝ)<(r:ℝ)^2 := sq_pos_of_pos hrR
  have hx : (0:ℝ)<(N:ℝ)/(r:ℝ)^2 := div_pos hNp hr2
  have hKx : (K:ℝ)^2≤(N:ℝ)/(r:ℝ)^2 := (le_div_iff₀ hr2).mpr (by exact_mod_cast hK)
  have hMx : (N:ℝ)/(r:ℝ)^2≤(M:ℝ)^2 := (div_le_iff₀ hr2).mpr (by exact_mod_cast hM)
  have hw := actual_weighted_upper_sharp hx hKM hKx hMx
  have hfloor : Nat.floor ((N:ℝ)/(r:ℝ)^2)=N/r^2 := by
    rw [←Nat.cast_pow,Nat.floor_div_natCast,Nat.floor_natCast]
  rw [hfloor] at hw
  dsimp only [Upper] at hw
  rw [Real.log_div hNp.ne' (pow_ne_zero 2 hrR.ne'),Real.sqrt_div hNp.le,Real.sqrt_sq hrR.le,←hkt] at hw
  have hlogA := mul_le_mul_of_nonneg_left hah (Real.log_nonneg hN1)
  have hv := mul_le_mul_of_nonneg_right (sub_le_sub_left hlog (39/250:ℝ)) (a_nonnegative M)
  have hsel := choose_upper_mul (v:=39/250-ld) hal hah
  have hcore : (Real.log N-Real.log ((r:ℝ)^2)+39/250)*A M-J M≤
      aU G sm*Real.log N+(39/250-ld)*chooseUpper (39/250-ld) (aL G sm) (aU G sm)-jL G sm := by
    nlinarith only [hlogA,hv,hsel,hjl]
  have hcore' := mul_le_mul_of_nonneg_left hcore (show (0:ℝ)≤2*(N:ℝ)/(r:ℝ)^2 by positivity)
  have hs' := mul_le_mul_of_nonneg_left hsh (show (0:ℝ)≤4*Real.sqrt N/(r:ℝ) by positivity)
  apply hw.trans
  calc
    _=(2*(N:ℝ)/(r:ℝ)^2)*((Real.log N-Real.log ((r:ℝ)^2)+39/250)*A M-J M)+
        (4*Real.sqrt N/(r:ℝ))*S M-(sk.t:ℝ)^2 := by ring
    _≤(2*(N:ℝ)/(r:ℝ)^2)*(aU G sm*Real.log N+
        (39/250-ld)*chooseUpper (39/250-ld) (aL G sm) (aU G sm)-jL G sm)+
        (4*Real.sqrt N/(r:ℝ))*sU G sm-(sk.t:ℝ)^2 :=
      sub_le_sub_right (add_le_add hcore' hs') _
    _=eval (upperCut G sm sk r ld) N := by dsimp only [eval,upperCut];ring

theorem actual_lower_cut {G N M r : ℕ} {sm : State} {ld : ℝ}
    (hN : 1≤N) (hG : 0<G) (hm : Valid G M sm) (hr : 0<r)
    (hlog : Real.log ((r:ℝ)^2)≤ld) :
    eval (lowerCut G sm r ld) N≤(DivCount 3 (N/r^2):ℝ) := by
  obtain ⟨hal,hah,_hjl,hjh,hsh,htt⟩ := valid_caps hG hm
  have hrR : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hNp : (0:ℝ)<N := by linarith only [hN1]
  have hr2 : (0:ℝ)<(r:ℝ)^2 := sq_pos_of_pos hrR
  have hx : (0:ℝ)<(N:ℝ)/(r:ℝ)^2 := div_pos hNp hr2
  have hw := actual_weighted_lower_sharp hx M
  have hfloor : Nat.floor ((N:ℝ)/(r:ℝ)^2)=N/r^2 := by
    rw [←Nat.cast_pow,Nat.floor_div_natCast,Nat.floor_natCast]
  rw [hfloor] at hw
  dsimp only [Lower] at hw
  rw [Real.log_div hNp.ne' (pow_ne_zero 2 hrR.ne'),Real.sqrt_div hNp.le,Real.sqrt_sq hrR.le,←htt] at hw
  have hlogA := mul_le_mul_of_nonneg_left hal (Real.log_nonneg hN1)
  have hv := mul_le_mul_of_nonneg_right (sub_le_sub_left hlog (77/500:ℝ)) (a_nonnegative M)
  have hsel := choose_lower_mul (v:=77/500-ld) hal hah
  have hcore : aL G sm*Real.log N+(77/500-ld)*chooseLower (77/500-ld) (aL G sm) (aU G sm)-jU G sm≤
      (Real.log N-Real.log ((r:ℝ)^2)+77/500)*A M-J M := by
    nlinarith only [hlogA,hv,hsel,hjh]
  have hcore' := mul_le_mul_of_nonneg_left hcore (show (0:ℝ)≤2*(N:ℝ)/(r:ℝ)^2 by positivity)
  have hs' := mul_le_mul_of_nonneg_left hsh (show (0:ℝ)≤4*Real.sqrt N/(r:ℝ) by positivity)
  apply le_trans _ hw
  calc
    eval (lowerCut G sm r ld) N=
        (2*(N:ℝ)/(r:ℝ)^2)*(aL G sm*Real.log N+
          (77/500-ld)*chooseLower (77/500-ld) (aL G sm) (aU G sm)-jU G sm)-
          (4*Real.sqrt N/(r:ℝ))*sU G sm-(sm.t:ℝ)^2-9*(sm.t:ℝ) := by
      dsimp only [eval,lowerCut];ring
    _≤(2*(N:ℝ)/(r:ℝ)^2)*((Real.log N-Real.log ((r:ℝ)^2)+77/500)*A M-J M)-
        (4*Real.sqrt N/(r:ℝ))*S M-(sm.t:ℝ)^2-9*(sm.t:ℝ) := by
      exact sub_le_sub_right (sub_le_sub_right (sub_le_sub hcore' hs') _) _
    _=_ := by ring

def combine (u1 u6 u10 u14 u15 u21 u35 u210 l2 l3 l5 l7 l30 l42 l70 l105 : Coeff) : Coeff :=
  ⟨(u1.a+u6.a+u10.a+u14.a+u15.a+u21.a+u35.a+u210.a)-(l2.a+l3.a+l5.a+l7.a+l30.a+l42.a+l70.a+l105.a),
    (u1.b+u6.b+u10.b+u14.b+u15.b+u21.b+u35.b+u210.b)-(l2.b+l3.b+l5.b+l7.b+l30.b+l42.b+l70.b+l105.b),
    (u1.s+u6.s+u10.s+u14.s+u15.s+u21.s+u35.s+u210.s)-(l2.s+l3.s+l5.s+l7.s+l30.s+l42.s+l70.s+l105.s),
    (u1.f+u6.f+u10.f+u14.f+u15.f+u21.f+u35.f+u210.f)-(l2.f+l3.f+l5.f+l7.f+l30.f+l42.f+l70.f+l105.f)⟩

theorem actual_m2_of_cuts (N : ℕ) (u1 u6 u10 u14 u15 u21 u35 u210 l2 l3 l5 l7 l30 l42 l70 l105 : Coeff)
    (hu1 : (DivCount 3 N:ℝ)≤eval u1 N)
    (hu6 : (DivCount 3 (N/36):ℝ)≤eval u6 N)
    (hu10 : (DivCount 3 (N/100):ℝ)≤eval u10 N)
    (hu14 : (DivCount 3 (N/196):ℝ)≤eval u14 N)
    (hu15 : (DivCount 3 (N/225):ℝ)≤eval u15 N)
    (hu21 : (DivCount 3 (N/441):ℝ)≤eval u21 N)
    (hu35 : (DivCount 3 (N/1225):ℝ)≤eval u35 N)
    (hu210 : (DivCount 3 (N/44100):ℝ)≤eval u210 N)
    (hl2 : eval l2 N≤(DivCount 3 (N/4):ℝ))
    (hl3 : eval l3 N≤(DivCount 3 (N/9):ℝ))
    (hl5 : eval l5 N≤(DivCount 3 (N/25):ℝ))
    (hl7 : eval l7 N≤(DivCount 3 (N/49):ℝ))
    (hl30 : eval l30 N≤(DivCount 3 (N/900):ℝ))
    (hl42 : eval l42 N≤(DivCount 3 (N/1764):ℝ))
    (hl70 : eval l70 N≤(DivCount 3 (N/4900):ℝ))
    (hl105 : eval l105 N≤(DivCount 3 (N/11025):ℝ))
    : (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)≤eval (combine u1 u6 u10 u14 u15 u21 u35 u210 l2 l3 l5 l7 l30 l42 l70 l105) N := by
  have hm := CompleteSeven129.actual_divisor_second_moment_seven N
  have he : eval (combine u1 u6 u10 u14 u15 u21 u35 u210 l2 l3 l5 l7 l30 l42 l70 l105) N=
    (eval u1 N+eval u6 N+eval u10 N+eval u14 N+eval u15 N+eval u21 N+eval u35 N+eval u210 N)-
    (eval l2 N+eval l3 N+eval l5 N+eval l7 N+eval l30 N+eval l42 N+eval l70 N+eval l105 N) := by
    dsimp only [eval,combine]
    ring
  rw [he]
  linarith only [hm,hu1,hu6,hu10,hu14,hu15,hu21,hu35,hu210,hl2,hl3,hl5,hl7,hl30,hl42,hl70,hl105]

#print axioms valid_caps
#print axioms a_nonnegative
#print axioms choose_upper_mul
#print axioms choose_lower_mul
#print axioms actual_upper_cut
#print axioms actual_lower_cut
#print axioms actual_m2_of_cuts
end
end JSP233.PairWindow131
