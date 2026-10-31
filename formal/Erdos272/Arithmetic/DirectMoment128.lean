import Erdos272.Arithmetic.CompleteFive128
import Erdos272.Arithmetic.ExclusionTangent126
import Erdos272.Arithmetic.PrefixSuper127

namespace JSP233.DirectMoment128
open SimplexMoment57 DivisorMoment122 VolumeLower125 HarmonicAbel29
open TwoSidedMoment62 StarCompletion RestrictedWitness44
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def F (L : ℝ) : ℝ := L^3/6-L^2/2+L-1
def E (L : ℝ) : ℝ :=
  F (L-Real.log 4)/4+F (L-Real.log 9)/9+F (L-Real.log 25)/25+
    F (L-Real.log 900)/900-Q3 (L-Real.log 36)/36-
      Q3 (L-Real.log 100)/100-Q3 (L-Real.log 225)/225

def H (x : ℝ) : ℝ :=
  V4 (x/4)+V4 (x/9)+V4 (x/25)+V4 (x/900)-
    (x/36)*Q3 (Real.log (x/36))-(x/100)*Q3 (Real.log (x/100))-
      (x/225)*Q3 (Real.log (x/225))

def FiveLo : ℝ := 160943791233/100000000000
def FiveHi : ℝ := 160943791253/100000000000
def ELower (L : ℝ) : ℝ :=
  F (L-2*LogThree126.TwoHi)/4+F (L-2*LogThree126.ThreeHi)/9+
    F (L-2*FiveHi)/25+
      F (L-(2*LogThree126.TwoHi+2*LogThree126.ThreeHi+2*FiveHi))/900-
        Q3 (L-(2*LogThree126.TwoLo+2*LogThree126.ThreeLo))/36-
          Q3 (L-(2*LogThree126.TwoLo+2*FiveLo))/100-
            Q3 (L-(2*LogThree126.ThreeLo+2*FiveLo))/225

def PBase (L : ℝ) : ℝ := L^3/6+(291/100)*L^2+(151581/10000)*L+149641/4000
def P (L : ℝ) : ℝ :=
  (8/75)*L^3+(3428213/1000000)*L^2+(13405041/1000000)*L+7951327/200000

theorem direct_polynomial_upper {L : ℝ} (hL : 0≤L) : PBase L-ELower L≤P L := by
  dsimp only [PBase,P,ELower,F,Q3,LogThree126.TwoLo,LogThree126.TwoHi,
    LogThree126.ThreeLo,LogThree126.ThreeHi,FiveLo,FiveHi]
  nlinarith only [hL,sq_nonneg L]

theorem F_monotone : Monotone F := by
  intro x y hxy
  have hq : 0≤(x^2+x*y+y^2)/6-(x+y)/2+1 := by
    nlinarith only [sq_nonneg (x+y-2),sq_nonneg (x-y)]
  have hp := mul_nonneg (sub_nonneg.mpr hxy) hq
  dsimp only [F]
  nlinarith only [hp]

theorem Q3_monotone : Monotone Q3 := by
  intro x y hxy
  have hq : 0≤(x^2+x*y+y^2)/6+(91/100)*(x+y)+18181/10000 := by
    nlinarith only [sq_nonneg (x+y+91/25),sq_nonneg (x-y)]
  have hp := mul_nonneg (sub_nonneg.mpr hxy) hq
  dsimp only [Q3]
  nlinarith only [hp]

theorem log_five_window : FiveLo≤Real.log 5 ∧ Real.log 5≤FiveHi := by
  have h := abs_le.mp Real.log_five_near_10
  constructor <;> dsimp only [FiveLo,FiveHi] <;> linarith only [h.1,h.2]

theorem scale_log_windows :
    Real.log 4≤2*LogThree126.TwoHi ∧ Real.log 9≤2*LogThree126.ThreeHi ∧
      Real.log 25≤2*FiveHi ∧
        Real.log 900≤2*LogThree126.TwoHi+2*LogThree126.ThreeHi+2*FiveHi ∧
          2*LogThree126.TwoLo+2*LogThree126.ThreeLo≤Real.log 36 ∧
            2*LogThree126.TwoLo+2*FiveLo≤Real.log 100 ∧
              2*LogThree126.ThreeLo+2*FiveLo≤Real.log 225 := by
  have h4 : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.log_pow]
    norm_num
  have h9 : Real.log 9=2*Real.log 3 := by
    rw [show (9:ℝ)=(3:ℝ)^2 by norm_num,Real.log_pow]
    norm_num
  have h25 : Real.log 25=2*Real.log 5 := by
    rw [show (25:ℝ)=(5:ℝ)^2 by norm_num,Real.log_pow]
    norm_num
  have h900 : Real.log 900=2*Real.log 2+2*Real.log 3+2*Real.log 5 := by
    rw [show (900:ℝ)=((2:ℝ)*3*5)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (2:ℝ)*3≠0) (by norm_num : (5:ℝ)≠0),
      Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (3:ℝ)≠0)]
    ring
  have h36 : Real.log 36=2*Real.log 2+2*Real.log 3 := by
    rw [show (36:ℝ)=((2:ℝ)*3)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (3:ℝ)≠0)]
    ring
  have h100 : Real.log 100=2*Real.log 2+2*Real.log 5 := by
    rw [show (100:ℝ)=((2:ℝ)*5)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (5:ℝ)≠0)]
    ring
  have h225 : Real.log 225=2*Real.log 3+2*Real.log 5 := by
    rw [show (225:ℝ)=((3:ℝ)*5)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (3:ℝ)≠0) (by norm_num : (5:ℝ)≠0)]
    ring
  obtain ⟨h2l,h2u⟩ := LogThree126.log_two_window
  obtain ⟨h3l,h3u⟩ := LogThree126.log_three_window
  obtain ⟨h5l,h5u⟩ := log_five_window
  rw [h4,h9,h25,h900,h36,h100,h225]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [h2l,h2u,h3l,h3u,h5l,h5u]

theorem ELower_le_E (L : ℝ) : ELower L≤E L := by
  obtain ⟨h4,h9,h25,h900,h36,h100,h225⟩ := scale_log_windows
  have p4 := F_monotone (sub_le_sub_left h4 L)
  have p9 := F_monotone (sub_le_sub_left h9 L)
  have p25 := F_monotone (sub_le_sub_left h25 L)
  have p900 := F_monotone (sub_le_sub_left h900 L)
  have q36 := Q3_monotone (sub_le_sub_left h36 L)
  have q100 := Q3_monotone (sub_le_sub_left h100 L)
  have q225 := Q3_monotone (sub_le_sub_left h225 L)
  dsimp only [E,ELower]
  linarith only [p4,p9,p25,p900,q36,q100,q225]

theorem actual_moment_H {N : ℕ} (hN : 900≤N) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+H N≤(DivCount 3 N:ℝ) := by
  have hn : (900:ℝ)≤N := by exact_mod_cast hN
  have hv4 := VolumeStep125.actual_v4_lower (show (1:ℝ)≤(N:ℝ)/4 by linarith only [hn])
  have hv9 := VolumeStep125.actual_v4_lower (show (1:ℝ)≤(N:ℝ)/9 by linarith only [hn])
  have hv25 := VolumeStep125.actual_v4_lower (show (1:ℝ)≤(N:ℝ)/25 by linarith only [hn])
  have hv900 := VolumeStep125.actual_v4_lower (show (1:ℝ)≤(N:ℝ)/900 by linarith only [hn])
  have hu36 := ExclusionTangent126.div_count3_real_upper (show (1:ℝ)≤(N:ℝ)/36 by linarith only [hn])
  have hu100 := ExclusionTangent126.div_count3_real_upper (show (1:ℝ)≤(N:ℝ)/100 by linarith only [hn])
  have hu225 := ExclusionTangent126.div_count3_real_upper (show (1:ℝ)≤(N:ℝ)/225 by linarith only [hn])
  simp only [Nat.floor_div_ofNat,Nat.floor_natCast] at hv4 hv9 hv25 hv900 hu36 hu100 hu225
  have hm := CompleteFive128.actual_divisor_second_moment_five N
  dsimp only [H]
  linarith only [hm,hv4,hv9,hv25,hv900,hu36,hu100,hu225]

theorem volume_E_identity {x : ℝ} (hx : x≠0) : H x=x*E (Real.log x)+4 := by
  dsimp only [H,E,F,V4]
  rw [Real.log_div hx (by norm_num : (4:ℝ)≠0),Real.log_div hx (by norm_num : (9:ℝ)≠0),
    Real.log_div hx (by norm_num : (25:ℝ)≠0),Real.log_div hx (by norm_num : (900:ℝ)≠0),
    Real.log_div hx (by norm_num : (36:ℝ)≠0),Real.log_div hx (by norm_num : (100:ℝ)≠0),
    Real.log_div hx (by norm_num : (225:ℝ)≠0)]
  ring

theorem actual_moment_E {N : ℕ} (hN : 900≤N) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)≤
      (N:ℝ)*(Q3 (Real.log N)-E (Real.log N))-4 := by
  have hn : 1≤N := by omega
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hm := actual_moment_H hN
  rw [volume_E_identity hN0] at hm
  have hu := div_count_three_prefix hn
  nlinarith only [hm,hu]

theorem actual_exception_E {N : ℕ} {c : ℤ} (hN : 900≤N) (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      (N:ℝ)*(Q3 (Real.log N)-E (Real.log N)+2*Harmonic N)-4 := by
  have hm := actual_moment_E hN
  have hf := actual_divisor_first_moment N
  calc
    _≤PrefixException N := PrefixSuper127.actual_exception_whole_prefix hc
    _≤_ := by
      dsimp only [PrefixException]
      nlinarith only [hm,hf]

theorem actual_moment_E_lower {N : ℕ} (hN : 900≤N) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)≤
      (N:ℝ)*(Q3 (Real.log N)-ELower (Real.log N))-4 := by
  have hm := actual_moment_E hN
  have hp := mul_le_mul_of_nonneg_left (ELower_le_E (Real.log N)) (Nat.cast_nonneg (α:=ℝ) N)
  nlinarith only [hm,hp]

theorem actual_exception_E_lower {N : ℕ} {c : ℤ} (hN : 900≤N) (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      (N:ℝ)*(Q3 (Real.log N)-ELower (Real.log N)+2*Harmonic N)-4 := by
  have hm := actual_exception_E hN hc
  have hp := mul_le_mul_of_nonneg_left (ELower_le_E (Real.log N)) (Nat.cast_nonneg (α:=ℝ) N)
  nlinarith only [hm,hp]

#print axioms direct_polynomial_upper
#print axioms F_monotone
#print axioms Q3_monotone
#print axioms log_five_window
#print axioms scale_log_windows
#print axioms ELower_le_E
#print axioms actual_moment_H
#print axioms volume_E_identity
#print axioms actual_moment_E
#print axioms actual_exception_E
#print axioms actual_moment_E_lower
#print axioms actual_exception_E_lower
end
end JSP233.DirectMoment128
