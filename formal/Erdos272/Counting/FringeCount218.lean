module

public import Erdos272.Resources.AlignedPlans212
public import Erdos272.Resources.ActualGrid212
public import Erdos272.Counting.TerminalDeficit51
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace JSP233.FringeCount218
open StarCompletion APGeometry DenseDeletion40 OffResidue44
open Aligned208 AlignedPlans212 ActualGrid212 ThinFringe33
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_aligned_count {N L R k : ℕ} {u : ℝ} {E : Finset (Finset ℤ)}
    (plan : ℕ→ℕ) (d : Finset ℤ→ℕ) (a : Finset ℤ→ℤ)
    (hk : 2≤k) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hlegal : Legal (Ground N) E) (hbad : ∀S∈E,¬IsAP S)
    (htrace : ∀S∈E,APAt (d S : ℤ) (a S) (S∩Finset.Icc (L : ℤ) (R : ℤ)))
    (halign : ∀S∈E,∀y∈S,(d S : ℤ)∣y-a S)
    (hdense : ∀S∈E,(N : ℝ)<(k : ℝ)*S.card)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/u)
    (hplan : ∀e∈Finset.Icc 1 (k-1),e<plan e ∧
      GateConstant e (plan e)<(N : ℝ)*GateCoefficient k u e (plan e)) :
    (E.card : ℝ)≤Slope (Finset.Icc 1 (k-1)) plan*((L : ℝ)+(N-R))+
      Constant (Finset.Icc 1 (k-1)) plan := by
  have hsteps : ∀S∈E,d S∈Finset.Icc 1 (k-1) := by
    intro S hS
    have hd : 0<d S := by exact_mod_cast (htrace S hS).1
    have hlt := actual_aligned_modulus_lt hd (hlegal.1 S hS) (hbad S hS)
      (hdense S hS) (halign S hS)
    have hltN : d S<k := by exact_mod_cast hlt
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hc := actual_count_from_gates (Finset.Icc 1 (k-1)) plan d a hL hLR hRN
    (by exact_mod_cast (show 0<k by omega) : (0 : ℝ)<k) hlegal hbad
    (fun e he => by have hh := (Finset.mem_Icc.mp he).1; omega)
    (fun e he => (hplan e he).1) hsteps htrace halign hdense
    (by simpa only [add_sub_assoc] using hwidth)
    (fun e he => by simpa only [GateConstant,GateCoefficient] using (hplan e he).2)
  rw [sum_cost_linear] at hc
  simpa only [add_sub_assoc] using hc

theorem actual_fringe_count {N L R k p : ℕ} {u : ℝ}
    {F E : Finset (Finset ℤ)} (plan : ℕ→ℕ)
    (hk : 2≤k) (hp : 2≤p) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hF : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hdense : ∀S∈E,(N : ℝ)<(k : ℝ)*S.card)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ)⊆H)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/u)
    (hplan : ∀e∈Finset.Icc 1 (k-1),e<plan e ∧
      GateConstant e (plan e)<(N : ℝ)*GateCoefficient k u e (plan e))
    (hoff : ((p : ℝ)-1)*((p : ℝ)-2)/2<
      (N : ℝ)*((p : ℝ)/(k : ℝ)-1-((p : ℝ)-1)/u)) :
    (E.card : ℝ)≤(Slope (Finset.Icc 1 (k-1)) plan+(p : ℝ)-1)*((L : ℝ)+(N-R))+
      (Constant (Finset.Icc 1 (k-1)) plan-(p : ℝ)+1) := by
  have hE : Legal (Ground N) E :=
    ⟨fun S hS => hF.1 S (hEF hS),fun S hS T hT hST => hF.2 S (hEF hS) T (hEF hT) hST⟩
  obtain ⟨H,hHF,hHAP,hIH⟩ := hcore
  have hcoords : ∀S,∃d : ℕ,∃a : ℤ,S∈E→APAt (d : ℤ) a (S∩Finset.Icc (L : ℤ) (R : ℤ)) := by
    intro S
    by_cases hS : S∈E
    · have hSH : S≠H := by intro he; exact hbad S hS (he.symm ▸ hHAP)
      have hpair := hF.2 S (hEF hS) H hHF hSH
      obtain ⟨d,a,hAP⟩ := apAt_interval_trace hpair hIH
      refine ⟨d.toNat,a,fun _ => ?_⟩
      simpa only [Int.toNat_of_nonneg hAP.1.le] using hAP
    · exact ⟨1,0,fun hh => False.elim (hS hh)⟩
  choose d a htrace using hcoords
  let A := E.filter fun S => ∀y∈S,(d S : ℤ)∣y-a S
  have hAE : A⊆E := Finset.filter_subset _ _
  have hA : Legal (Ground N) A :=
    ⟨fun S hS => hE.1 S (hAE hS),fun S hS T hT hST => hE.2 S (hAE hS) T (hAE hT) hST⟩
  have ha := actual_aligned_count plan d a hk hL hLR hRN hA
    (fun S hS => hbad S (hAE hS)) (fun S hS => htrace S (hAE hS))
    (fun S hS => (Finset.mem_filter.mp hS).2)
    (fun S hS => hdense S (hAE hS)) hwidth hplan
  have ho := actual_off_residue_width (p := p) (k := (k : ℝ)) (u := u)
    E (fun S => (d S : ℤ)) a hL hLR hRN hp
    (by exact_mod_cast (show 0<k by omega)) hE htrace hdense hwidth hoff
  have hoffset : E.filter (fun S => ¬∀y∈S,(d S : ℤ)∣y-a S)=OffMembers E (fun S => (d S : ℤ)) a := by
    ext S
    simp only [Finset.mem_filter,OffMembers]
    push Not
    rfl
  have hcard := Finset.card_filter_add_card_filter_not (s := E)
    (fun S => ∀y∈S,(d S : ℤ)∣y-a S)
  rw [hoffset] at hcard
  have hcardR : (A.card : ℝ)+(OffMembers E (fun S => (d S : ℤ)) a).card=E.card := by exact_mod_cast hcard
  nlinarith only [ha,ho,hcardR]

def PrepPlan (d : ℕ) : ℕ := if d=1 then 9 else 7

theorem actual_preparation {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 642498≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hF : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hdense : ∀S∈E,(N : ℝ)<6*S.card)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ)⊆H)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/(37/2)) :
    (E.card : ℝ)≤(1117/60 : ℝ)*((L : ℝ)+(N-R))-197/20 := by
  have hn : (642498 : ℝ)≤N := by exact_mod_cast hN
  have hplan : ∀e∈Finset.Icc 1 (6-1),e<PrepPlan e ∧
      GateConstant e (PrepPlan e)<(N : ℝ)*GateCoefficient 6 (37/2) e (PrepPlan e) := by
    intro e he
    obtain ⟨he1,he5⟩ := Finset.mem_Icc.mp he
    interval_cases e <;> norm_num [PrepPlan,GateConstant,GateCoefficient] <;> linarith only [hn]
  have hoff : ((9 : ℝ)-1)*((9 : ℝ)-2)/2<
      (N : ℝ)*((9 : ℝ)/6-1-((9 : ℝ)-1)/(37/2)) := by
    norm_num
    linarith only [hn]
  have h := actual_fringe_count (k := 6) (p := 9) PrepPlan (by decide) (by decide)
    hL hLR hRN hF hEF hbad hdense hcore hwidth hplan hoff
  norm_num [Slope,Constant,PrepPlan,Finset.sum_Icc_succ_top] at h
  linarith only [h]

#print axioms actual_aligned_count
#print axioms actual_fringe_count
#print axioms actual_preparation
end
end JSP233.FringeCount218
