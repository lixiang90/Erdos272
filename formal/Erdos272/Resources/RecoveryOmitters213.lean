import Erdos272.Resources.RecoveryOmitters212
import Erdos272.Resources.AlignedPlans213
namespace JSP233.RecoveryOmitters213
open StarCompletion APGeometry DenseDeletion40
open OffResidue44 AlignedPlans212 ActualGrid212 ThinFringe33
open RecoveryOmitters212 (PreparationP)
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem preparation_off_gate {r : ℕ} (hr1 : 1≤r) (hr3 : r≤3) :
    0 < ((PreparationP r : ℝ)/11-1-((PreparationP r : ℝ)-1)/PreparationWidth r) ∧
    ((PreparationP r : ℝ)-1)*((PreparationP r : ℝ)-2)/2 <
      646000*((PreparationP r : ℝ)/11-1-((PreparationP r : ℝ)-1)/PreparationWidth r) := by
  interval_cases r <;> norm_num [PreparationP,PreparationWidth]

theorem actual_preparation_omission_count {N c L R r : ℕ} {F : Finset (Finset ℤ)}
    (hN : 646000≤N) (hr1 : 1≤r) (hr3 : r≤3)
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hF : Legal (Ground N) F)
    (hcore : ∃H ∈ Retained N 11 F, Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hwidth : (L : ℝ)+(N-R) < (N : ℝ)/PreparationWidth r) :
    ((TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card : ℝ) ≤
      (PreparationA r+(PreparationP r : ℝ)-1)*((L : ℝ)+(N-R))+
      (PreparationB r-(PreparationP r : ℝ)+1) := by
  let E := TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)
  have hEF : E ⊆ F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have hE : Legal (Ground N) E := ⟨fun S hS => hF.1 S (hEF hS),
    fun S hS T hT hST => hF.2 S (hEF hS) T (hEF hT) hST⟩
  have hbad : ∀S∈E, ¬IsAP S := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  have hdense : ∀S∈E, (N : ℝ)<11*S.card := by
    intro S hS
    have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
    exact_mod_cast hh
  obtain ⟨H,hH,hIH⟩ := hcore
  have hHF : H ∈ F := (Finset.mem_sdiff.mp hH).1
  have hcoords : ∀S, ∃d : ℕ, ∃a : ℤ, S∈E → APAt (d : ℤ) a (S∩Finset.Icc (L : ℤ) (R : ℤ)) := by
    intro S
    by_cases hS : S∈E
    · have hSH : S≠H := by
        intro heq
        subst S
        exact (Finset.mem_sdiff.mp hH).2 (Finset.mem_filter.mp hS).1
      have hpair := hF.2 S (hEF hS) H hHF hSH
      obtain ⟨d,a,hAP⟩ := apAt_interval_trace hpair hIH
      refine ⟨d.toNat,a,fun _ => ?_⟩
      simpa only [Int.toNat_of_nonneg hAP.1.le] using hAP
    · exact ⟨1,0,fun hh => False.elim (hS hh)⟩
  choose d a htrace using hcoords
  let A := E.filter (fun S => ∀y∈S, (d S : ℤ) ∣ y-a S)
  have hAE : A ⊆ E := Finset.filter_subset _ _
  have hA : Legal (Ground N) A := ⟨fun S hS => hE.1 S (hAE hS),
    fun S hS T hT hST => hE.2 S (hAE hS) T (hAE hT) hST⟩
  have ha := AlignedPlans213.actual_preparation_count d a (by omega : 640000≤N) hr1 hr3 hL hLR hRN hA
    (fun S hS => hbad S (hAE hS)) (fun S hS => htrace S (hAE hS))
    (fun S hS => (Finset.mem_filter.mp hS).2) (fun S hS => hdense S (hAE hS))
    (by linarith only [hwidth])
  have hgate := preparation_off_gate hr1 hr3
  have hnR : (646000 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : 2 ≤ PreparationP r := by interval_cases r <;> norm_num [PreparationP]
  have ho := actual_off_residue_width (p := PreparationP r) (k := 11) (u := PreparationWidth r)
    E (fun S => (d S : ℤ)) a hL hLR hRN hp (by norm_num) hE htrace hdense hwidth
    (hgate.2.trans_le (mul_le_mul_of_nonneg_right hnR hgate.1.le))
  have hoff : E.filter (fun S => ¬∀y∈S, (d S : ℤ) ∣ y-a S) =
      OffMembers E (fun S => (d S : ℤ)) a := by
    ext S
    simp only [Finset.mem_filter, OffMembers]
    push_neg
    rfl
  have hc := Finset.card_filter_add_card_filter_not (s := E)
    (fun S => ∀y∈S, (d S : ℤ) ∣ y-a S)
  rw [hoff] at hc
  have hcR : (A.card : ℝ)+(OffMembers E (fun S => (d S : ℤ)) a).card=E.card := by exact_mod_cast hc
  change (E.card : ℝ) ≤ _
  nlinarith only [ha,ho,hcR]


#print axioms preparation_off_gate
#print axioms actual_preparation_omission_count
end
end JSP233.RecoveryOmitters213
