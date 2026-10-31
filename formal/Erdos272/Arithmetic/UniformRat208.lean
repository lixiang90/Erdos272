import Erdos272.Resources.UniformScale208
import Mathlib.Data.Rat.Floor

/-! Executable rational formulas cast exactly to the continuous source. -/
namespace JSP233.UniformRat208
open UniformSourceCore208 UniformActual208 UniformScale208 NeighborMass208
open scoped BigOperators
set_option maxHeartbeats 0

def RDelta : ℚ := 76/125
def RSigma : ℚ := 1644934067/1000000000
def RStep (s m : ℚ) : ℕ := Nat.floor (s/m)
def RH2 (D : ℕ) : ℚ := ∑ d ∈ Finset.Icc 1 D,1/(d : ℚ)^2
def Rw (s m : ℚ) : ℚ := (RStep s m : ℚ)*s*m-(RStep s m : ℚ)*((RStep s m : ℚ)+1)*m^2/2
def RI (s m : ℚ) : ℚ := (RStep s m : ℚ)*s*m^2/2-
  (RStep s m : ℚ)*((RStep s m : ℚ)+1)*m^3/6+s^3/6*(RSigma-RH2 (RStep s m))
def RJ (s e : ℚ) : ℚ := s^3/6-RDelta*RI s (s-e)+RDelta/2*Rw s (s-e)-11/80*s^2-2014/625*s
def RQ (s e t : ℚ) : ℚ := e*(s-1-t)+max (3*e-s-1) 0/2*max (s-2-2*t) 0+
  max (5*e-2*s-2) 0/3*max (s-3-3*t) 0
def RP (y z M : ℚ) : ℚ := RQ y z (7*M/25)+160/M*RJ y z
def RB (y z M : ℚ) : ℚ := z*(y-1-7*M/25)

@[simp] theorem delta_cast : (RDelta : ℝ)=Delta := by norm_num [RDelta,Delta]
@[simp] theorem sigma_cast : (RSigma : ℝ)=UniformSourceCore208.Sigma := by norm_num [RSigma,UniformSourceCore208.Sigma]

@[simp] theorem step_cast (s m : ℚ) : Step (s : ℝ) (m : ℝ)=RStep s m := by
  unfold Step RStep
  rw [← Rat.cast_div,← Int.floor_toNat,Rat.floor_cast,Int.floor_toNat]

@[simp] theorem H2_cast (D : ℕ) : (RH2 D : ℝ)=H2 D := by
  simp only [RH2,H2,Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast]

@[simp] theorem w_cast (s m : ℚ) : (Rw s m : ℝ)=w (s : ℝ) m := by
  simp only [Rw,w,step_cast,Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_div,
    Rat.cast_pow,Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat]

@[simp] theorem I_cast (s m : ℚ) : (RI s m : ℝ)=I (s : ℝ) m := by
  simp only [RI,I,step_cast,Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_div,
    Rat.cast_pow,Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat,sigma_cast,H2_cast]

@[simp] theorem J_cast (s e : ℚ) : (RJ s e : ℝ)=Jstar (s : ℝ) e := by
  simp only [RJ,Jstar,Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_div,
    Rat.cast_pow,Rat.cast_ofNat,delta_cast]
  rw [I_cast,w_cast]
  push_cast
  rfl

@[simp] theorem Q_cast (s e t : ℚ) : (RQ s e t : ℝ)=Q (s : ℝ) e t := by
  simp only [RQ,Q,Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_div,
    Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_max]

@[simp] theorem P_cast (y z M : ℚ) : (RP y z M : ℝ)=P (y : ℝ) z M := by
  simp only [RP,P,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Q_cast,J_cast]

@[simp] theorem B_cast (y z M : ℚ) : (RB y z M : ℝ)=Baseline (y : ℝ) z M := by
  simp only [RB,Baseline,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]

#print axioms step_cast
#print axioms P_cast
end JSP233.UniformRat208
