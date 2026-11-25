module

public import Erdos272.Geometry.N82427.PhaseSlope82427
public import Erdos272.Geometry.N82427.PhaseFamily82427

@[expose] public section

namespace JSP233.PhaseActualLight82427
open CrossBandCredit208 CrossBandCleanup208 CleanupEval208 ActualCleanupEval208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_light_le_row {s : System} (r : Row) (hlen : r.bands.length=7) {n : ℕ}
    (hDn : s.D ≤ n)
    (hmatch : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : CrossBandCredit208.Band,
      (At r hlen b).T=s.T d b ∧ (At r hlen b).E=s.E d b ∧
      (At r hlen b).U=s.U d b ∧ block (At r hlen b) d=s.B d b)
    (hB : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : CrossBandCredit208.Band, 3 ≤ block (At r hlen b) d) :
    (∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band, PhaseSystem82427.Light s d b) ≤
      (PhaseSlope82427.RowLight r hlen n s.N : ℝ) := by
  have hpoint : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : CrossBandCredit208.Band,
      PhaseSystem82427.Light s d b=(PhaseSlope82427.BandCost s.N d (At r hlen b) : ℝ) := by
    intro d hd b
    have hb : 3 ≤ s.B d b := by simpa only [(hmatch d hd b).2.2.2] using hB d hd b
    dsimp only [PhaseSystem82427.Light,PhaseSlope82427.BandCost]
    rw [(hmatch d hd b).1,(hmatch d hd b).2.1,
      (hmatch d hd b).2.2.1,(hmatch d hd b).2.2.2]
    by_cases he : s.E d b ≤ 1
    · simp only [if_pos he,Nat.cast_zero]
    · have href : PhaseSystem82427.Refined s d b := ⟨by omega,hb⟩
      simp only [if_neg he,if_pos href]
  have heq : (∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band, PhaseSystem82427.Light s d b)=
      ∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band, (PhaseSlope82427.BandCost s.N d (At r hlen b) : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    exact Finset.sum_congr rfl (fun b _ => hpoint d hd b)
  rw [heq]
  have hsub : Finset.Icc 1 s.D ⊆ Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hDn⟩
  unfold PhaseSlope82427.RowLight
  push_cast
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)

#print axioms actual_light_le_row
end
end JSP233.PhaseActualLight82427
