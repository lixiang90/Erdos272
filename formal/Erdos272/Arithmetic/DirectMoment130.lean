import Erdos272.Arithmetic.DirectMoment129
import Erdos272.Arithmetic.TrapezoidStep130
namespace JSP233.DirectMoment130
open SimplexMoment57 DivisorMoment122 VolumeLower125 HarmonicAbel29
open TrapezoidStep130
open TwoSidedMoment62 StarCompletion RestrictedWitness44
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Fstrong (L : ℝ) : ℝ := L^3/6+L^2/4+L/4-1/8
def FiveLo : ℝ := 160943791233/100000000000
def FiveHi : ℝ := 160943791253/100000000000
def SevenLo : ℝ := 19459101487/10000000000
def SevenHi : ℝ := 19459101494/10000000000
def E (L : ℝ) : ℝ :=
  Fstrong (L-Real.log 4)/4+Fstrong (L-Real.log 9)/9+Fstrong (L-Real.log 25)/25+Fstrong (L-Real.log 49)/49+Fstrong (L-Real.log 900)/900+Fstrong (L-Real.log 1764)/1764+Fstrong (L-Real.log 4900)/4900+Fstrong (L-Real.log 11025)/11025-Q3 (L-Real.log 36)/36-Q3 (L-Real.log 100)/100-Q3 (L-Real.log 196)/196-Q3 (L-Real.log 225)/225-Q3 (L-Real.log 441)/441-Q3 (L-Real.log 1225)/1225-Q3 (L-Real.log 44100)/44100

def ELower (L : ℝ) : ℝ :=
  Fstrong (L-(2*LogThree126.TwoHi))/4+Fstrong (L-(2*LogThree126.ThreeHi))/9+Fstrong (L-(2*FiveHi))/25+Fstrong (L-(2*SevenHi))/49+Fstrong (L-(2*LogThree126.TwoHi+2*LogThree126.ThreeHi+2*FiveHi))/900+Fstrong (L-(2*LogThree126.TwoHi+2*LogThree126.ThreeHi+2*SevenHi))/1764+Fstrong (L-(2*LogThree126.TwoHi+2*FiveHi+2*SevenHi))/4900+Fstrong (L-(2*LogThree126.ThreeHi+2*FiveHi+2*SevenHi))/11025-Q3 (L-(2*LogThree126.TwoLo+2*LogThree126.ThreeLo))/36-Q3 (L-(2*LogThree126.TwoLo+2*FiveLo))/100-Q3 (L-(2*LogThree126.TwoLo+2*SevenLo))/196-Q3 (L-(2*LogThree126.ThreeLo+2*FiveLo))/225-Q3 (L-(2*LogThree126.ThreeLo+2*SevenLo))/441-Q3 (L-(2*FiveLo+2*SevenLo))/1225-Q3 (L-(2*LogThree126.TwoLo+2*LogThree126.ThreeLo+2*FiveLo+2*SevenLo))/44100

def H (x : ℝ) : ℝ :=
  W4 (x/4)+W4 (x/9)+W4 (x/25)+W4 (x/49)+W4 (x/900)+W4 (x/1764)+W4 (x/4900)+W4 (x/11025)-(x/36)*Q3 (Real.log (x/36))-(x/100)*Q3 (Real.log (x/100))-(x/196)*Q3 (Real.log (x/196))-(x/225)*Q3 (Real.log (x/225))-(x/441)*Q3 (Real.log (x/441))-(x/1225)*Q3 (Real.log (x/1225))-(x/44100)*Q3 (Real.log (x/44100))

def PBase (L : ℝ) : ℝ := L^3/6+(291/100)*L^2+(151581/10000)*L+149641/4000
def P (L : ℝ) : ℝ := (128/1225)*L^3+(3148427/1000000)*L^2+(14718173/1000000)*L+37860977/1000000

theorem Fstrong_derivative (x : ℝ) :
    HasDerivAt Fstrong (x^2/2+x/2+1/4) x := by
  have hd := (((((hasDerivAt_id x).pow 3).div_const 6).add
    (((hasDerivAt_id x).pow 2).div_const 4)).add ((hasDerivAt_id x).div_const 4)).sub_const (1/8)
  convert hd using 1 <;> first | rfl | (simp only [id_eq];ring)

theorem Fstrong_derivative_pos (x : ℝ) : 0<x^2/2+x/2+1/4 := by
  nlinarith only [sq_nonneg (x+1/2)]

theorem Fstrong_monotone : Monotone Fstrong := by
  intro x y hxy
  have hq : 0≤(x^2+x*y+y^2)/6+(x+y)/4+1/4 := by
    nlinarith only [sq_nonneg (x+y+1),sq_nonneg (x-y)]
  have hp := mul_nonneg (sub_nonneg.mpr hxy) hq
  dsimp only [Fstrong]
  nlinarith only [hp]

theorem ELower_le_E (L : ℝ) : ELower L≤E L := by
  obtain ⟨h4,h9,h25,h49,h900,h1764,h4900,h11025,h36,h100,h196,h225,h441,h1225,h44100⟩ := DirectMoment129.scale_log_windows
  have p4 : Fstrong (L-(2*LogThree126.TwoHi))≤Fstrong (L-Real.log 4) :=
    Fstrong_monotone (sub_le_sub_left h4 L)
  have p9 : Fstrong (L-(2*LogThree126.ThreeHi))≤Fstrong (L-Real.log 9) :=
    Fstrong_monotone (sub_le_sub_left h9 L)
  have p25 : Fstrong (L-(2*FiveHi))≤Fstrong (L-Real.log 25) :=
    Fstrong_monotone (sub_le_sub_left h25 L)
  have p49 : Fstrong (L-(2*SevenHi))≤Fstrong (L-Real.log 49) :=
    Fstrong_monotone (sub_le_sub_left h49 L)
  have p900 : Fstrong (L-(2*LogThree126.TwoHi+2*LogThree126.ThreeHi+2*FiveHi))≤Fstrong (L-Real.log 900) :=
    Fstrong_monotone (sub_le_sub_left h900 L)
  have p1764 : Fstrong (L-(2*LogThree126.TwoHi+2*LogThree126.ThreeHi+2*SevenHi))≤Fstrong (L-Real.log 1764) :=
    Fstrong_monotone (sub_le_sub_left h1764 L)
  have p4900 : Fstrong (L-(2*LogThree126.TwoHi+2*FiveHi+2*SevenHi))≤Fstrong (L-Real.log 4900) :=
    Fstrong_monotone (sub_le_sub_left h4900 L)
  have p11025 : Fstrong (L-(2*LogThree126.ThreeHi+2*FiveHi+2*SevenHi))≤Fstrong (L-Real.log 11025) :=
    Fstrong_monotone (sub_le_sub_left h11025 L)
  have q36 := DirectMoment128.Q3_monotone (sub_le_sub_left h36 L)
  have q100 := DirectMoment128.Q3_monotone (sub_le_sub_left h100 L)
  have q196 := DirectMoment128.Q3_monotone (sub_le_sub_left h196 L)
  have q225 := DirectMoment128.Q3_monotone (sub_le_sub_left h225 L)
  have q441 := DirectMoment128.Q3_monotone (sub_le_sub_left h441 L)
  have q1225 := DirectMoment128.Q3_monotone (sub_le_sub_left h1225 L)
  have q44100 := DirectMoment128.Q3_monotone (sub_le_sub_left h44100 L)
  dsimp only [E,ELower,FiveLo,FiveHi,SevenLo,SevenHi,
    DirectMoment129.FiveLo,DirectMoment129.FiveHi,DirectMoment129.SevenLo,DirectMoment129.SevenHi] at *
  linarith only [p4,p9,p25,p49,p900,p1764,p4900,p11025,q36,q100,q196,q225,q441,q1225,q44100]

theorem direct_polynomial_upper {L : ℝ} (hL : 0≤L) : PBase L-ELower L≤P L := by
  dsimp only [PBase,P,ELower,Fstrong,Q3,LogThree126.TwoLo,LogThree126.TwoHi,
    LogThree126.ThreeLo,LogThree126.ThreeHi,FiveLo,FiveHi,SevenLo,SevenHi]
  nlinarith only [hL,sq_nonneg L]

theorem actual_moment_H {N : ℕ} (hN : 44100≤N) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+H N≤(DivCount 3 N:ℝ) := by
  have hn : (44100:ℝ)≤N := by exact_mod_cast hN
  have hv4 := TrapezoidStep130.actual_w4_lower (show (1:ℝ)≤(N:ℝ)/4 by linarith only [hn])
  have hv9 := TrapezoidStep130.actual_w4_lower (show (1:ℝ)≤(N:ℝ)/9 by linarith only [hn])
  have hv25 := TrapezoidStep130.actual_w4_lower (show (1:ℝ)≤(N:ℝ)/25 by linarith only [hn])
  have hv49 := TrapezoidStep130.actual_w4_lower (show (1:ℝ)≤(N:ℝ)/49 by linarith only [hn])
  have hv900 := TrapezoidStep130.actual_w4_lower (show (1:ℝ)≤(N:ℝ)/900 by linarith only [hn])
  have hv1764 := TrapezoidStep130.actual_w4_lower (show (1:ℝ)≤(N:ℝ)/1764 by linarith only [hn])
  have hv4900 := TrapezoidStep130.actual_w4_lower (show (1:ℝ)≤(N:ℝ)/4900 by linarith only [hn])
  have hv11025 := TrapezoidStep130.actual_w4_lower (show (1:ℝ)≤(N:ℝ)/11025 by linarith only [hn])
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

theorem volume_E_identity {x : ℝ} (hx : x≠0) : H x=x*E (Real.log x)+1 := by
  dsimp only [H,E,Fstrong,W4,V1,V2,V3,V4]
  rw [Real.log_div hx (by norm_num : (4:ℝ)≠0),Real.log_div hx (by norm_num : (9:ℝ)≠0),Real.log_div hx (by norm_num : (25:ℝ)≠0),Real.log_div hx (by norm_num : (49:ℝ)≠0),Real.log_div hx (by norm_num : (900:ℝ)≠0),Real.log_div hx (by norm_num : (1764:ℝ)≠0),Real.log_div hx (by norm_num : (4900:ℝ)≠0),Real.log_div hx (by norm_num : (11025:ℝ)≠0),Real.log_div hx (by norm_num : (36:ℝ)≠0),Real.log_div hx (by norm_num : (100:ℝ)≠0),Real.log_div hx (by norm_num : (196:ℝ)≠0),Real.log_div hx (by norm_num : (225:ℝ)≠0),Real.log_div hx (by norm_num : (441:ℝ)≠0),Real.log_div hx (by norm_num : (1225:ℝ)≠0),Real.log_div hx (by norm_num : (44100:ℝ)≠0)]
  ring

theorem actual_moment_E {N : ℕ} (hN : 44100≤N) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)≤
      (N:ℝ)*(Q3 (Real.log N)-E (Real.log N))-1 := by
  have hn : 1≤N := by omega
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hm := actual_moment_H hN
  rw [volume_E_identity hN0] at hm
  have hu := div_count_three_prefix hn
  nlinarith only [hm,hu]

theorem actual_witness_E {N : ℕ} {c : ℤ} (hN : 44100≤N) (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      (N:ℝ)*(Q3 (Real.log N)-E (Real.log N)+2*Harmonic N)-1 := by
  have hm := actual_moment_E hN
  have hf := actual_divisor_first_moment N
  calc
    _≤PrefixException N := PrefixSuper127.actual_exception_whole_prefix hc
    _≤_ := by
      dsimp only [PrefixException]
      nlinarith only [hm,hf]

theorem actual_moment_Elower {N : ℕ} (hN : 44100≤N) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)≤
      (N:ℝ)*(Q3 (Real.log N)-ELower (Real.log N))-1 := by
  have hm := actual_moment_E hN
  have hp := mul_le_mul_of_nonneg_left (ELower_le_E (Real.log N)) (Nat.cast_nonneg (α:=ℝ) N)
  nlinarith only [hm,hp]

theorem actual_witness_Elower {N : ℕ} {c : ℤ} (hN : 44100≤N) (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      (N:ℝ)*(Q3 (Real.log N)-ELower (Real.log N)+2*Harmonic N)-1 := by
  have hm := actual_witness_E hN hc
  have hp := mul_le_mul_of_nonneg_left (ELower_le_E (Real.log N)) (Nat.cast_nonneg (α:=ℝ) N)
  nlinarith only [hm,hp]

#print axioms Fstrong_derivative
#print axioms Fstrong_derivative_pos
#print axioms Fstrong_monotone
#print axioms ELower_le_E
#print axioms direct_polynomial_upper
#print axioms actual_moment_H
#print axioms volume_E_identity
#print axioms actual_moment_E
#print axioms actual_witness_E
#print axioms actual_moment_Elower
#print axioms actual_witness_Elower
end
end JSP233.DirectMoment130
