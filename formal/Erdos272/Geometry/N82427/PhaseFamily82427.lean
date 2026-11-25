module

public import Erdos272.Geometry.N82427.PhasePhysical82427

@[expose] public section

namespace JSP233.PhaseFamily82427
open CrossBandCredit208 CrossBandCleanup208 PhaseSystem82427
open CleanupEval208 ActualCleanupEval208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_family_bound_with_light {s : System} (v : Valid s)
    (r : Row) (hlen : r.bands.length=7) {n : ℕ} {out : Totals}
    (hf : ChunkFacts r 1 n out) (hDn : s.D ≤ n)
    (hmatch : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : CrossBandCredit208.Band,
      (At r hlen b).T=s.T d b ∧ (At r hlen b).E=s.E d b ∧
      (At r hlen b).U=s.U d b ∧ block (At r hlen b) d=s.B d b)
    (hgrid : 0 < r.grid) (hlow : 0 < r.low) (hlN : r.low ≤ s.N)
    (hNh : s.N ≤ r.high) (hei : s.e ≤ r.i) {light : ℝ}
    (hlight : (∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band, Light s d b) ≤ light) :
    (s.F.card : ℝ) ≤ (s.N : ℝ)^2*ResidualAggregate208.Price s.e (ResidualTwoCensus208.H s.M)+
      (253/35 : ℝ)*s.N+light+(s.N : ℝ)*((out.net : ℝ)/r.grid) := by
  have hsub : Finset.Icc 1 s.D ⊆ Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hDn⟩
  have hg : ∀ d ∈ Finset.Icc 1 s.D, (step r d).good=true :=
    fun d hd => CleanupRowBounds208.good_Icc hf (hsub hd)
  have hc := PhaseSystem82427.credit_sum s v.step_range
    (fun d hd b => PhaseCleanup82427.piece_credit v hd b)
  have hp := PhaseCleanup82427.actual_heavy_cleanup s v (PhaseBand82427.RawWindows s)
    (by intros; exact le_rfl)
  have hN : (0 : ℝ) < s.N := by exact_mod_cast (show 0 < s.N by omega)
  have hid := PhasePhysical82427.net_identity s hN.ne'
  have hnet := Finset.sum_le_sum (fun d (hd : d ∈ Finset.Icc 1 s.D) =>
    PhasePhysical82427.actual_step v hd r hlen (hmatch d hd) (hg d hd) hlN hNh hei)
  have hmore : (∑ d ∈ Finset.Icc 1 s.D, ((step r d).totals.net : ℝ)/r.grid) ≤
      ∑ d ∈ Finset.Icc 1 n, ((step r d).totals.net : ℝ)/r.grid :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  have hrow := CleanupRowBounds208.normalized_row_bound hf
    (fun d => ((step r d).totals.net : ℝ)/r.grid) (by intros; exact le_rfl)
  have hpay := mul_le_mul_of_nonneg_left (hnet.trans (hmore.trans hrow)) hN.le
  linarith only [hc, hp, hid, hpay, hlight]

#print axioms actual_family_bound_with_light
end
end JSP233.PhaseFamily82427
