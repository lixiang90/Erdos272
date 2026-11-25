module

public import Erdos272.Retention.N67702.RetainedIntervals67702
public import Erdos272.Counting.N80470.RootedProfile80470

@[expose] public section

namespace JSP233.SmallRoot67702
open StarCompletion APGeometry APPrepare49 LongTerminal35 DenseDeletion40 RootModel291012
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_small_root {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 56400≤N) (hhigh : N≤88403)
    (hleft : (L : ℝ)<(1/15 : ℝ)*N) (hspan : L+3≤R) :
    ∀ S∈SmallAP (GenericRecovery291012.Readded N 12 F (c : ℤ)),(c : ℤ)∈S := by
  have hi := RetainedIntervals67702.actual_avoiders_intervals g hN hhigh hleft
  have ha := TerminalDeficit51.actual_avoider_readdition N 12 F (c : ℤ)
  change Avoiders (GenericRecovery291012.Readded N 12 F (c : ℤ)) (c : ℤ)=_ at ha
  intro S hS
  by_contra hcS
  have hm := APPrepare49.actual_small_AP_member hS
  have hv : S∈Avoiders (GenericRecovery291012.Readded N 12 F (c : ℤ)) (c : ℤ) :=
    Finset.mem_filter.mpr ⟨hm.1,hcS⟩
  rw [ha] at hv
  obtain ⟨a,b,_hca,haL,hRb,_hbN,hrep⟩ := hi S hv
  have hI : Finset.Icc (L : ℤ) (R : ℤ)⊆S := by
    rw [hrep]
    intro z hz
    obtain ⟨hLz,hzR⟩ := Finset.mem_Icc.mp hz
    change z∈Finset.Icc (a : ℤ) (b : ℤ)
    exact Finset.mem_Icc.mpr
      ⟨(by exact_mod_cast haL : (a : ℤ)≤L).trans hLz,
       hzR.trans (by exact_mod_cast hRb : (R : ℤ)≤b)⟩
  have hcount := Finset.card_le_card hI
  have hfour : 4≤(Finset.Icc (L : ℤ) (R : ℤ)).card := by
    simp only [Int.card_Icc]
    omega
  omega

#print axioms actual_small_root
end
end JSP233.SmallRoot67702
