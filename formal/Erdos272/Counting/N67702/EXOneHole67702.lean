module

public import Erdos272.Geometry.N67702.EXGeometry67702

@[expose] public section

namespace JSP233.EXOneHole67702
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Numerator (k : Fin 2) : ℕ := if k=0 then 23 else 11
def Denominator (k : Fin 2) : ℕ := if k=0 then 200 else 100
def Gamma (k : Fin 2) : ℕ := Denominator k-Numerator k
def WidthCap (k : Fin 2) : ℝ := (Numerator k : ℝ)/Denominator k
def Truncate (N : ℕ) (k : Fin 2) : ℕ := Numerator k*N/Denominator k
def Lower (N : ℕ) : ℕ := (N-1)/4+1
def Upper (N : ℕ) (k : Fin 2) : ℕ := (Gamma k*N-1)/(3*Denominator k)
def Hole (N : ℕ) (k : Fin 2) : Finset ℕ := Finset.Icc (Lower N) (Upper N k)

theorem parameter_bounds (k : Fin 2) :
    0<Denominator k ∧ 0<Numerator k ∧ Numerator k<Denominator k := by
  fin_cases k <;> norm_num [Numerator,Denominator]

theorem truncate_bounds {N : ℕ} (hN : 2000≤N) (k : Fin 2) :
    1≤Truncate N k ∧ Truncate N k≤(N-1)/3 := by
  fin_cases k <;> norm_num [Truncate,Numerator,Denominator] <;> omega

theorem hole_bounds {N d : ℕ} (hN : 2000≤N) (k : Fin 2) (hd : d∈Hole N k) :
    2≤d ∧ Truncate N k<d ∧ d≤(N-1)/3 ∧ N-1<4*d ∧
      (3*Denominator k)*d<Gamma k*N := by
  fin_cases k <;>
    norm_num [Hole,Lower,Upper,Truncate,Gamma,Numerator,Denominator,Finset.mem_Icc] at * <;>
    omega

theorem hole_count_integer {N : ℕ} (hN : 2000≤N) (k : Fin 2) :
    (4*Gamma k-3*Denominator k)*N≤12*Denominator k*(Hole N k).card+9*Denominator k := by
  fin_cases k <;>
    norm_num [Hole,Lower,Upper,Gamma,Numerator,Denominator,Nat.card_Icc] <;>
    omega

theorem hole_below_span {N L R d : ℕ} (hN : 2000≤N) (hLR : L≤R) (hRN : R≤N)
    (k : Fin 2) (hw : Denominator k*(L+N-R)≤Numerator k*N) (hd : d∈Hole N k) :
    3*d<R-L := by
  have hb := (hole_bounds hN k hd).2.2.2.2
  fin_cases k <;> norm_num [Gamma,Numerator,Denominator] at * <;> omega

#print axioms parameter_bounds
#print axioms truncate_bounds
#print axioms hole_bounds
#print axioms hole_count_integer
#print axioms hole_below_span
end
end JSP233.EXOneHole67702
