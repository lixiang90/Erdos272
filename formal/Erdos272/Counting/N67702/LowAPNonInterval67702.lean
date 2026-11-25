module

public import Erdos272.Counting.N67702.LowAPCount67702
public import Erdos272.Global.NonInterval53

@[expose] public section

namespace JSP233.LowAPNonInterval67702
open StarCompletion APGeometry APCount41 NonInterval53 NonIntervalAP47
open DenseDeletion40 RestrictedWitness44 HarmonicAbel29 PrivatePairExistence
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_noninterval_family_count {N c L : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (hL : 1≤L) (hhalf : 2*L≤N)
    (hF : Legal (Ground N) G) (hroot : ∀ S∈G,¬IsAP S→(c : ℤ)∈S)
    (hcL : c≤L) (hLN : L≤N)
    (hlow : ∀ S∈Avoiders G (c : ℤ),∃ a∈S,a≤(L : ℤ))
    (hP : P∈G) (hcP : (c : ℤ)∉P) (hno : ¬IsInterval P) :
    (G.card : ℝ)≤3*(N : ℝ)^2/8+(329/200 : ℝ)*L*((N : ℝ)-L)+
      (N : ℝ)*Harmonic N+N+(WitnessException (Ground N) c : ℝ)+1 := by
  have hAP : IsAP P := by
    by_contra hh
    exact hcP (hroot P hP hh)
  have hC := NonInterval53.actual_crooked_half_avoider hF hroot hP hcP
    (NonInterval53.actual_noninterval_card (hF.1 P hP) hAP hno)
  let A := G.filter IsAP
  have hAG : A⊆G := Finset.filter_subset _ _
  have hAAP : ∀ S∈A,IsAP S := fun S hS=>(Finset.mem_filter.mp hS).2
  have hA := LowAPCount67702.actual_AP_low_weak hL hhalf
    (show Legal (Ground N) A from
      ⟨fun S hS=>hF.1 S (hAG hS),fun S hS T hT hne=>hF.2 S (hAG hS) T (hAG hT) hne⟩)
    hAAP (by
      intro S hS
      have hn := isAP_nonempty (hAAP S hS)
      by_cases hcS : (c : ℤ)∈S
      · exact ((low_spec hn).2 c hcS).trans (by exact_mod_cast hcL)
      · obtain ⟨a,ha,haL⟩ := hlow S (Finset.mem_filter.mpr ⟨hAG hS,hcS⟩)
        exact ((low_spec hn).2 a ha).trans haL)
  have hp : (A.card : ℝ)+(CrookedMembers G).card=G.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s:=G) IsAP
  linarith only [hC,hA,hp]

#print axioms actual_noninterval_family_count
end
end JSP233.LowAPNonInterval67702
