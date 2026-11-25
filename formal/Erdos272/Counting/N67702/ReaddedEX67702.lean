module

public import Erdos272.Counting.N67702.EXCap67702
public import Erdos272.Resources.N291012.RootModel291012

@[expose] public section

namespace JSP233.ReaddedEX67702
open StarCompletion APGeometry APPrepare49 PreparedClasses50 RootModel291012
open HarmonicAbel29
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem actual_prepared_global {N c L R : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (hN : 2000≤N) (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hG : Legal (Ground N) G)
    (hP : P∈G) (hLP : ∀z∈P,(L : ℤ)≤z)
    (hout : ∀S∈G,(c : ℤ)∉S→(∃u∈S,u≤(L : ℤ))∧∃v∈S,(R : ℤ)≤v) :
    ((EX (PreparedAP G c L) R).card : ℝ)≤(129/200 : ℝ)*L*((N : ℝ)-R)+
      ((L : ℝ)+((N : ℝ)-R))*(Harmonic N-10493/5000)+(N : ℝ)/3 := by
  have hm := fun S hS=>actual_EX_endpoints hG hcL hP hLP hout (S:=S) hS
  have hsub : EX (PreparedAP G c L) R⊆G := fun S hS=>(hm S hS).1
  have hlegal : Legal (Ground N) (EX (PreparedAP G c L) R) :=
    ⟨fun S hS=>hG.1 S (hsub hS),fun S hS T hT hne=>hG.2 S (hsub hS) T (hsub hT) hne⟩
  exact EXGlobal67702.actual_four_width hN hLR hRN hlegal
    (fun S hS=>(hm S hS).2.1) (fun S hS=>(hm S hS).2.2.1)
    (fun S hS=>(hm S hS).2.2.2.1) (fun S hS=>(hm S hS).2.2.2.2)

theorem actual_prepared_cap {N c L R : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (hN : 2000≤N) (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hG : Legal (Ground N) G)
    (hP : P∈G) (hLP : ∀z∈P,(L : ℤ)≤z)
    (hout : ∀S∈G,(c : ℤ)∉S→(∃u∈S,u≤(L : ℤ))∧∃v∈S,(R : ℤ)≤v)
    (k : Fin 2) (hw : ((L : ℝ)+((N : ℝ)-R))≤EXOneHole67702.WidthCap k*N) :
    ((EX (PreparedAP G c L) R).card : ℝ)≤(129/200 : ℝ)*L*((N : ℝ)-R)+
      ((L : ℝ)+((N : ℝ)-R))*(Harmonic N-EXLog67702.Beta k)+(29/100 : ℝ)*N+1 := by
  have hm := fun S hS=>actual_EX_endpoints hG hcL hP hLP hout (S:=S) hS
  have hsub : EX (PreparedAP G c L) R⊆G := fun S hS=>(hm S hS).1
  have hlegal : Legal (Ground N) (EX (PreparedAP G c L) R) :=
    ⟨fun S hS=>hG.1 S (hsub hS),fun S hS T hT hne=>hG.2 S (hsub hS) T (hsub hT) hne⟩
  exact EXCap67702.actual_cap_width hN hLR hRN k hw hlegal
    (fun S hS=>(hm S hS).2.1) (fun S hS=>(hm S hS).2.2.1)
    (fun S hS=>(hm S hS).2.2.2.1) (fun S hS=>(hm S hS).2.2.2.2)

#print axioms actual_prepared_global
#print axioms actual_prepared_cap
end
end JSP233.ReaddedEX67702
