module

public import Erdos272.Arithmetic.CompleteSeven129
public import Erdos272.Arithmetic.DirectMoment128
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section
namespace JSP233.DirectMoment129
open SimplexMoment57 DivisorMoment122 VolumeLower125 HarmonicAbel29
open TwoSidedMoment62 StarCompletion RestrictedWitness44
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def F (L : ℝ) : ℝ := L^3/6-L^2/2+L-1
def FiveLo : ℝ := 160943791233/100000000000
def FiveHi : ℝ := 160943791253/100000000000
def SevenLo : ℝ := 19459101487/10000000000
def SevenHi : ℝ := 19459101494/10000000000
def E (L : ℝ) : ℝ :=
  F (L-Real.log 4)/4+F (L-Real.log 9)/9+F (L-Real.log 25)/25+F (L-Real.log 49)/49+F (L-Real.log 900)/900+F (L-Real.log 1764)/1764+F (L-Real.log 4900)/4900+F (L-Real.log 11025)/11025-Q3 (L-Real.log 36)/36-Q3 (L-Real.log 100)/100-Q3 (L-Real.log 196)/196-Q3 (L-Real.log 225)/225-Q3 (L-Real.log 441)/441-Q3 (L-Real.log 1225)/1225-Q3 (L-Real.log 44100)/44100

def ELower (L : ℝ) : ℝ :=
  F (L-(2*LogThree126.TwoHi))/4+F (L-(2*LogThree126.ThreeHi))/9+F (L-(2*FiveHi))/25+F (L-(2*SevenHi))/49+F (L-(2*LogThree126.TwoHi+2*LogThree126.ThreeHi+2*FiveHi))/900+F (L-(2*LogThree126.TwoHi+2*LogThree126.ThreeHi+2*SevenHi))/1764+F (L-(2*LogThree126.TwoHi+2*FiveHi+2*SevenHi))/4900+F (L-(2*LogThree126.ThreeHi+2*FiveHi+2*SevenHi))/11025-Q3 (L-(2*LogThree126.TwoLo+2*LogThree126.ThreeLo))/36-Q3 (L-(2*LogThree126.TwoLo+2*FiveLo))/100-Q3 (L-(2*LogThree126.TwoLo+2*SevenLo))/196-Q3 (L-(2*LogThree126.ThreeLo+2*FiveLo))/225-Q3 (L-(2*LogThree126.ThreeLo+2*SevenLo))/441-Q3 (L-(2*FiveLo+2*SevenLo))/1225-Q3 (L-(2*LogThree126.TwoLo+2*LogThree126.ThreeLo+2*FiveLo+2*SevenLo))/44100

def H (x : ℝ) : ℝ :=
  V4 (x/4)+V4 (x/9)+V4 (x/25)+V4 (x/49)+V4 (x/900)+V4 (x/1764)+V4 (x/4900)+V4 (x/11025)-(x/36)*Q3 (Real.log (x/36))-(x/100)*Q3 (Real.log (x/100))-(x/196)*Q3 (Real.log (x/196))-(x/225)*Q3 (Real.log (x/225))-(x/441)*Q3 (Real.log (x/441))-(x/1225)*Q3 (Real.log (x/1225))-(x/44100)*Q3 (Real.log (x/44100))

def PBase (L : ℝ) : ℝ := L^3/6+(291/100)*L^2+(151581/10000)*L+149641/4000
def P (L : ℝ) : ℝ := (128/1225)*L^3+(1733023/500000)*L^2+(6590329/500000)*L+20113033/500000

theorem log_seven_window : SevenLo≤Real.log 7 ∧ Real.log 7≤SevenHi := by
  have ht := Real.abs_log_sub_add_sum_range_le (x:=(1/8:ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at ht
  have htl := (abs_le.mp ht).1
  have htu := (abs_le.mp ht).2
  have he : (7:ℝ)=(2:ℝ)^3*(7/8:ℝ) := by norm_num
  rw [he,Real.log_mul (by positivity) (by norm_num),Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  obtain ⟨h2l,h2u⟩ := LogThree126.log_two_window
  dsimp only [LogThree126.TwoLo,LogThree126.TwoHi] at h2l h2u
  constructor <;> dsimp only [SevenLo,SevenHi] <;> linarith only [htl,htu,h2l,h2u]

theorem scale_log_windows :
    Real.log 4≤(2*LogThree126.TwoHi) ∧
      Real.log 9≤(2*LogThree126.ThreeHi) ∧
      Real.log 25≤(2*FiveHi) ∧
      Real.log 49≤(2*SevenHi) ∧
      Real.log 900≤(2*LogThree126.TwoHi+2*LogThree126.ThreeHi+2*FiveHi) ∧
      Real.log 1764≤(2*LogThree126.TwoHi+2*LogThree126.ThreeHi+2*SevenHi) ∧
      Real.log 4900≤(2*LogThree126.TwoHi+2*FiveHi+2*SevenHi) ∧
      Real.log 11025≤(2*LogThree126.ThreeHi+2*FiveHi+2*SevenHi) ∧
      (2*LogThree126.TwoLo+2*LogThree126.ThreeLo)≤Real.log 36 ∧
      (2*LogThree126.TwoLo+2*FiveLo)≤Real.log 100 ∧
      (2*LogThree126.TwoLo+2*SevenLo)≤Real.log 196 ∧
      (2*LogThree126.ThreeLo+2*FiveLo)≤Real.log 225 ∧
      (2*LogThree126.ThreeLo+2*SevenLo)≤Real.log 441 ∧
      (2*FiveLo+2*SevenLo)≤Real.log 1225 ∧
      (2*LogThree126.TwoLo+2*LogThree126.ThreeLo+2*FiveLo+2*SevenLo)≤Real.log 44100 := by
  have h4 : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=((2:ℝ))^2 by norm_num,Real.log_pow]
    ring
  have h9 : Real.log 9=2*Real.log 3 := by
    rw [show (9:ℝ)=((3:ℝ))^2 by norm_num,Real.log_pow]
    ring
  have h25 : Real.log 25=2*Real.log 5 := by
    rw [show (25:ℝ)=((5:ℝ))^2 by norm_num,Real.log_pow]
    ring
  have h49 : Real.log 49=2*Real.log 7 := by
    rw [show (49:ℝ)=((7:ℝ))^2 by norm_num,Real.log_pow]
    ring
  have h900 : Real.log 900=2*Real.log 2+2*Real.log 3+2*Real.log 5 := by
    rw [show (900:ℝ)=((2:ℝ)*3*5)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (2:ℝ)*3≠0) (by norm_num : (5:ℝ)≠0),
      Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (3:ℝ)≠0)]
    ring
  have h1764 : Real.log 1764=2*Real.log 2+2*Real.log 3+2*Real.log 7 := by
    rw [show (1764:ℝ)=((2:ℝ)*3*7)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (2:ℝ)*3≠0) (by norm_num : (7:ℝ)≠0),
      Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (3:ℝ)≠0)]
    ring
  have h4900 : Real.log 4900=2*Real.log 2+2*Real.log 5+2*Real.log 7 := by
    rw [show (4900:ℝ)=((2:ℝ)*5*7)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (2:ℝ)*5≠0) (by norm_num : (7:ℝ)≠0),
      Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (5:ℝ)≠0)]
    ring
  have h11025 : Real.log 11025=2*Real.log 3+2*Real.log 5+2*Real.log 7 := by
    rw [show (11025:ℝ)=((3:ℝ)*5*7)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (3:ℝ)*5≠0) (by norm_num : (7:ℝ)≠0),
      Real.log_mul (by norm_num : (3:ℝ)≠0) (by norm_num : (5:ℝ)≠0)]
    ring
  have h36 : Real.log 36=2*Real.log 2+2*Real.log 3 := by
    rw [show (36:ℝ)=((2:ℝ)*3)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (3:ℝ)≠0)]
    ring
  have h100 : Real.log 100=2*Real.log 2+2*Real.log 5 := by
    rw [show (100:ℝ)=((2:ℝ)*5)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (5:ℝ)≠0)]
    ring
  have h196 : Real.log 196=2*Real.log 2+2*Real.log 7 := by
    rw [show (196:ℝ)=((2:ℝ)*7)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (7:ℝ)≠0)]
    ring
  have h225 : Real.log 225=2*Real.log 3+2*Real.log 5 := by
    rw [show (225:ℝ)=((3:ℝ)*5)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (3:ℝ)≠0) (by norm_num : (5:ℝ)≠0)]
    ring
  have h441 : Real.log 441=2*Real.log 3+2*Real.log 7 := by
    rw [show (441:ℝ)=((3:ℝ)*7)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (3:ℝ)≠0) (by norm_num : (7:ℝ)≠0)]
    ring
  have h1225 : Real.log 1225=2*Real.log 5+2*Real.log 7 := by
    rw [show (1225:ℝ)=((5:ℝ)*7)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (5:ℝ)≠0) (by norm_num : (7:ℝ)≠0)]
    ring
  have h44100 : Real.log 44100=2*Real.log 2+2*Real.log 3+2*Real.log 5+2*Real.log 7 := by
    rw [show (44100:ℝ)=((2:ℝ)*3*5*7)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num : (2:ℝ)*3*5≠0) (by norm_num : (7:ℝ)≠0),
      Real.log_mul (by norm_num : (2:ℝ)*3≠0) (by norm_num : (5:ℝ)≠0),
      Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (3:ℝ)≠0)]
    ring
  obtain ⟨h2l,h2u⟩ := LogThree126.log_two_window
  obtain ⟨h3l,h3u⟩ := LogThree126.log_three_window
  obtain ⟨h5l,h5u⟩ := DirectMoment128.log_five_window
  change FiveLo≤Real.log 5 at h5l
  change Real.log 5≤FiveHi at h5u
  obtain ⟨h7l,h7u⟩ := log_seven_window
  rw [h4,h9,h25,h49,h900,h1764,h4900,h11025,h36,h100,h196,h225,h441,h1225,h44100]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [h2l,h2u,h3l,h3u,h5l,h5u,h7l,h7u]

theorem ELower_le_E (L : ℝ) : ELower L≤E L := by
  obtain ⟨h4,h9,h25,h49,h900,h1764,h4900,h11025,h36,h100,h196,h225,h441,h1225,h44100⟩ := scale_log_windows
  have p4 : F (L-(2*LogThree126.TwoHi))≤F (L-Real.log 4) :=
    DirectMoment128.F_monotone (sub_le_sub_left h4 L)
  have p9 : F (L-(2*LogThree126.ThreeHi))≤F (L-Real.log 9) :=
    DirectMoment128.F_monotone (sub_le_sub_left h9 L)
  have p25 : F (L-(2*FiveHi))≤F (L-Real.log 25) :=
    DirectMoment128.F_monotone (sub_le_sub_left h25 L)
  have p49 : F (L-(2*SevenHi))≤F (L-Real.log 49) :=
    DirectMoment128.F_monotone (sub_le_sub_left h49 L)
  have p900 : F (L-(2*LogThree126.TwoHi+2*LogThree126.ThreeHi+2*FiveHi))≤F (L-Real.log 900) :=
    DirectMoment128.F_monotone (sub_le_sub_left h900 L)
  have p1764 : F (L-(2*LogThree126.TwoHi+2*LogThree126.ThreeHi+2*SevenHi))≤F (L-Real.log 1764) :=
    DirectMoment128.F_monotone (sub_le_sub_left h1764 L)
  have p4900 : F (L-(2*LogThree126.TwoHi+2*FiveHi+2*SevenHi))≤F (L-Real.log 4900) :=
    DirectMoment128.F_monotone (sub_le_sub_left h4900 L)
  have p11025 : F (L-(2*LogThree126.ThreeHi+2*FiveHi+2*SevenHi))≤F (L-Real.log 11025) :=
    DirectMoment128.F_monotone (sub_le_sub_left h11025 L)
  have q36 := DirectMoment128.Q3_monotone (sub_le_sub_left h36 L)
  have q100 := DirectMoment128.Q3_monotone (sub_le_sub_left h100 L)
  have q196 := DirectMoment128.Q3_monotone (sub_le_sub_left h196 L)
  have q225 := DirectMoment128.Q3_monotone (sub_le_sub_left h225 L)
  have q441 := DirectMoment128.Q3_monotone (sub_le_sub_left h441 L)
  have q1225 := DirectMoment128.Q3_monotone (sub_le_sub_left h1225 L)
  have q44100 := DirectMoment128.Q3_monotone (sub_le_sub_left h44100 L)
  dsimp only [E,ELower]
  linarith only [p4,p9,p25,p49,p900,p1764,p4900,p11025,q36,q100,q196,q225,q441,q1225,q44100]

theorem direct_polynomial_upper {L : ℝ} (hL : 0≤L) : PBase L-ELower L≤P L := by
  dsimp only [PBase,P,ELower,F,Q3,LogThree126.TwoLo,LogThree126.TwoHi,
    LogThree126.ThreeLo,LogThree126.ThreeHi,FiveLo,FiveHi,SevenLo,SevenHi]
  nlinarith only [hL,sq_nonneg L]

theorem actual_moment_H {N : ℕ} (hN : 44100≤N) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+H N≤(DivCount 3 N:ℝ) := by
  have hn : (44100:ℝ)≤N := by exact_mod_cast hN
  have hv4 := VolumeStep125.actual_v4_lower (show (1:ℝ)≤(N:ℝ)/4 by linarith only [hn])
  have hv9 := VolumeStep125.actual_v4_lower (show (1:ℝ)≤(N:ℝ)/9 by linarith only [hn])
  have hv25 := VolumeStep125.actual_v4_lower (show (1:ℝ)≤(N:ℝ)/25 by linarith only [hn])
  have hv49 := VolumeStep125.actual_v4_lower (show (1:ℝ)≤(N:ℝ)/49 by linarith only [hn])
  have hv900 := VolumeStep125.actual_v4_lower (show (1:ℝ)≤(N:ℝ)/900 by linarith only [hn])
  have hv1764 := VolumeStep125.actual_v4_lower (show (1:ℝ)≤(N:ℝ)/1764 by linarith only [hn])
  have hv4900 := VolumeStep125.actual_v4_lower (show (1:ℝ)≤(N:ℝ)/4900 by linarith only [hn])
  have hv11025 := VolumeStep125.actual_v4_lower (show (1:ℝ)≤(N:ℝ)/11025 by linarith only [hn])
  have hu36 := ExclusionTangent126.div_count3_real_upper (show (1:ℝ)≤(N:ℝ)/36 by linarith only [hn])
  have hu100 := ExclusionTangent126.div_count3_real_upper (show (1:ℝ)≤(N:ℝ)/100 by linarith only [hn])
  have hu196 := ExclusionTangent126.div_count3_real_upper (show (1:ℝ)≤(N:ℝ)/196 by linarith only [hn])
  have hu225 := ExclusionTangent126.div_count3_real_upper (show (1:ℝ)≤(N:ℝ)/225 by linarith only [hn])
  have hu441 := ExclusionTangent126.div_count3_real_upper (show (1:ℝ)≤(N:ℝ)/441 by linarith only [hn])
  have hu1225 := ExclusionTangent126.div_count3_real_upper (show (1:ℝ)≤(N:ℝ)/1225 by linarith only [hn])
  have hu44100 := ExclusionTangent126.div_count3_real_upper (show (1:ℝ)≤(N:ℝ)/44100 by linarith only [hn])
  simp only [Nat.floor_div_ofNat,Nat.floor_natCast] at hv4 hv9 hv25 hv49 hv900 hv1764 hv4900 hv11025 hu36 hu100 hu196 hu225 hu441 hu1225 hu44100
  have hm := CompleteSeven129.actual_divisor_second_moment_seven N
  dsimp only [H]
  linarith only [hm,hv4,hv9,hv25,hv49,hv900,hv1764,hv4900,hv11025,hu36,hu100,hu196,hu225,hu441,hu1225,hu44100]

theorem volume_E_identity {x : ℝ} (hx : x≠0) : H x=x*E (Real.log x)+8 := by
  dsimp only [H,E,F,V4]
  rw [Real.log_div hx (by norm_num : (4:ℝ)≠0),Real.log_div hx (by norm_num : (9:ℝ)≠0),Real.log_div hx (by norm_num : (25:ℝ)≠0),Real.log_div hx (by norm_num : (49:ℝ)≠0),Real.log_div hx (by norm_num : (900:ℝ)≠0),Real.log_div hx (by norm_num : (1764:ℝ)≠0),Real.log_div hx (by norm_num : (4900:ℝ)≠0),Real.log_div hx (by norm_num : (11025:ℝ)≠0),Real.log_div hx (by norm_num : (36:ℝ)≠0),Real.log_div hx (by norm_num : (100:ℝ)≠0),Real.log_div hx (by norm_num : (196:ℝ)≠0),Real.log_div hx (by norm_num : (225:ℝ)≠0),Real.log_div hx (by norm_num : (441:ℝ)≠0),Real.log_div hx (by norm_num : (1225:ℝ)≠0),Real.log_div hx (by norm_num : (44100:ℝ)≠0)]
  ring

theorem actual_moment_E {N : ℕ} (hN : 44100≤N) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)≤
      (N:ℝ)*(Q3 (Real.log N)-E (Real.log N))-8 := by
  have hn : 1≤N := by omega
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hm := actual_moment_H hN
  rw [volume_E_identity hN0] at hm
  have hu := div_count_three_prefix hn
  nlinarith only [hm,hu]

theorem actual_exception_E {N : ℕ} {c : ℤ} (hN : 44100≤N) (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      (N:ℝ)*(Q3 (Real.log N)-E (Real.log N)+2*Harmonic N)-8 := by
  have hm := actual_moment_E hN
  have hf := actual_divisor_first_moment N
  calc
    _≤PrefixException N := PrefixSuper127.actual_exception_whole_prefix hc
    _≤_ := by
      dsimp only [PrefixException]
      nlinarith only [hm,hf]

theorem actual_moment_E_lower {N : ℕ} (hN : 44100≤N) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)≤
      (N:ℝ)*(Q3 (Real.log N)-ELower (Real.log N))-8 := by
  have hm := actual_moment_E hN
  have hp := mul_le_mul_of_nonneg_left (ELower_le_E (Real.log N)) (Nat.cast_nonneg (α:=ℝ) N)
  nlinarith only [hm,hp]

theorem actual_exception_E_lower {N : ℕ} {c : ℤ} (hN : 44100≤N) (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      (N:ℝ)*(Q3 (Real.log N)-ELower (Real.log N)+2*Harmonic N)-8 := by
  have hm := actual_exception_E hN hc
  have hp := mul_le_mul_of_nonneg_left (ELower_le_E (Real.log N)) (Nat.cast_nonneg (α:=ℝ) N)
  nlinarith only [hm,hp]

#print axioms log_seven_window
#print axioms scale_log_windows
#print axioms ELower_le_E
#print axioms direct_polynomial_upper
#print axioms actual_moment_H
#print axioms volume_E_identity
#print axioms actual_moment_E
#print axioms actual_exception_E
#print axioms actual_moment_E_lower
#print axioms actual_exception_E_lower
end
end JSP233.DirectMoment129
