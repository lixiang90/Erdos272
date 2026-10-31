import Erdos272.Counting.FringeCount218

/-! All five actual density ranks pay their own complete aligned/off plan.
The terminal width remains the physical native width 29. -/
namespace JSP233.TerminalRanks218
open StarCompletion APGeometry OffResidue44 AlignedPlans212 FringeCount218
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def TerminalP (k : ℕ) : ℕ := match k with
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 7
  | _ => 9

def Coefficient (k : ℕ) : ℝ :=
  Slope (Finset.Icc 1 (k-1)) (fun _ => TerminalP k)+(TerminalP k : ℝ)-1

def Offset (k : ℕ) : ℝ :=
  Constant (Finset.Icc 1 (k-1)) (fun _ => TerminalP k)-(TerminalP k : ℝ)+1

theorem actual_terminal_count {N L R k : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 642498≤N) (hk2 : 2≤k) (hk6 : k≤6)
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hF : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hdense : ∀S∈E,(N : ℝ)<(k : ℝ)*S.card)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ)⊆H)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/29) :
    (E.card : ℝ)≤Coefficient k*((L : ℝ)+(N-R))+Offset k := by
  have hn : (642498 : ℝ)≤N := by exact_mod_cast hN
  have hp : 2≤TerminalP k := by interval_cases k <;> norm_num [TerminalP]
  have hplan : ∀d∈Finset.Icc 1 (k-1), d<TerminalP k ∧
      GateConstant d (TerminalP k)<(N : ℝ)*GateCoefficient k 29 d (TerminalP k) := by
    intro d hd
    obtain ⟨hd1,hdk⟩ := Finset.mem_Icc.mp hd
    interval_cases k <;> interval_cases d <;>
      norm_num [TerminalP,GateConstant,GateCoefficient] <;> linarith only [hn]
  have hoff : ((TerminalP k : ℝ)-1)*((TerminalP k : ℝ)-2)/2<
      (N : ℝ)*((TerminalP k : ℝ)/(k : ℝ)-1-((TerminalP k : ℝ)-1)/29) := by
    interval_cases k <;> norm_num [TerminalP] <;> linarith only [hn]
  have hh := actual_fringe_count (k := k) (p := TerminalP k) (u := 29)
    (fun _ => TerminalP k) hk2 hp hL hLR hRN hF hEF hbad hdense hcore hwidth hplan hoff
  exact hh

theorem all_rank_native_gate {N k : ℕ} {s w e : ℝ}
    (hN : 642498≤N) (hk2 : 2≤k) (hk6 : k≤6)
    (hs : s≤(N : ℝ)/(k-1 : ℕ)) (hw : w<(N : ℝ)/29)
    (he : e≤Coefficient k*w+Offset k) : 4*s+4*w+4*e<5*N := by
  have hn : (642498 : ℝ)≤N := by exact_mod_cast hN
  interval_cases k <;>
    norm_num [Coefficient,Offset,TerminalP,Slope,Constant,Finset.sum_Icc_succ_top] at hs he ⊢ <;>
    nlinarith only [hn,hs,hw,he]

#print axioms actual_terminal_count
#print axioms all_rank_native_gate
end
end JSP233.TerminalRanks218
