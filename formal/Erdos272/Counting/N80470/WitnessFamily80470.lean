module

public import Erdos272.Geometry.N82427.PhasePhysical82427

@[expose] public section

namespace JSP233.WitnessFamily80470
open CrossBandCredit208 CrossBandCleanup208 PhaseSystem82427
open CleanupEval208 ActualCleanupEval208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem credit_sum (s : System) (light : ℕ → CrossBandCredit208.Band → ℝ)
    (hstep : ∀ S ∈ s.F, s.step S ∈ Finset.Icc 1 s.D)
    (hcredit : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : CrossBandCredit208.Band,
      ((s.Piece d b).card : ℝ) + (s.T d b : ℝ) * (Heavy s d b).card ≤
        light d b + (HeavyPiece s d b).card) :
    (s.F.card : ℝ) +
        (∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band, (s.T d b : ℝ) * (Heavy s d b).card) ≤
      (∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band, light d b) + (G s).card := by
  have hp := s.card_partition hstep
  have hg := g_card_partition s hstep
  have hh := Finset.sum_le_sum (fun d (hd : d ∈ Finset.Icc 1 s.D) =>
    Finset.sum_le_sum (s := (Finset.univ : Finset CrossBandCredit208.Band)) (fun b hb => hcredit d hd b))
  have hpR : (s.F.card : ℝ) =
      ∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band, ((s.Piece d b).card : ℝ) := by
    exact_mod_cast hp
  have hgR : ((G s).card : ℝ) =
      ∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band, ((HeavyPiece s d b).card : ℝ) := by
    exact_mod_cast hg
  simp only [Finset.sum_add_distrib] at hh
  rw [← hpR, ← hgR] at hh
  exact hh

theorem actual_family_bound {s : System} (v : Valid s)
    (r : Row) (hlen : r.bands.length = 7) {n : ℕ} {out : Totals}
    (hf : ChunkFacts r 1 n out) (hDn : s.D ≤ n)
    (hmatch : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : CrossBandCredit208.Band,
      (At r hlen b).T = s.T d b ∧ (At r hlen b).E = s.E d b ∧
      (At r hlen b).U = s.U d b ∧ block (At r hlen b) d = s.B d b)
    (hgrid : 0 < r.grid) (hlow : 0 < r.low) (hlN : r.low ≤ s.N)
    (hNh : s.N ≤ r.high) (hei : s.e ≤ r.i)
    (pieceLight : ℕ → CrossBandCredit208.Band → ℝ) {light : ℝ}
    (hcredit : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : CrossBandCredit208.Band,
      ((s.Piece d b).card : ℝ) + (s.T d b : ℝ) * (Heavy s d b).card ≤
        pieceLight d b + (HeavyPiece s d b).card)
    (hlight : (∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band,
        pieceLight d b) ≤ light) :
    (s.F.card : ℝ) ≤
      (s.N : ℝ)^2 * ResidualAggregate208.Price s.e (ResidualTwoCensus208.H s.M) +
        (253 / 35 : ℝ) * s.N + light + (s.N : ℝ) * ((out.net : ℝ) / r.grid) := by
  have hsub : Finset.Icc 1 s.D ⊆ Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hDn⟩
  have hg : ∀ d ∈ Finset.Icc 1 s.D, (step r d).good = true :=
    fun d hd => CleanupRowBounds208.good_Icc hf (hsub hd)
  have hc := credit_sum s pieceLight v.step_range hcredit
  have hp := PhaseCleanup82427.actual_heavy_cleanup s v (PhaseBand82427.RawWindows s)
    (by intros; exact le_rfl)
  have hN : (0 : ℝ) < s.N := by exact_mod_cast (show 0 < s.N by omega)
  have hid := PhasePhysical82427.net_identity s hN.ne'
  have hnet := Finset.sum_le_sum (fun d (hd : d ∈ Finset.Icc 1 s.D) =>
    PhasePhysical82427.actual_step v hd r hlen (hmatch d hd) (hg d hd) hlN hNh hei)
  have hmore : (∑ d ∈ Finset.Icc 1 s.D, ((step r d).totals.net : ℝ) / r.grid) ≤
      ∑ d ∈ Finset.Icc 1 n, ((step r d).totals.net : ℝ) / r.grid :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  have hrow := CleanupRowBounds208.normalized_row_bound hf
    (fun d => ((step r d).totals.net : ℝ) / r.grid) (by intros; exact le_rfl)
  have hpay := mul_le_mul_of_nonneg_left (hnet.trans (hmore.trans hrow)) hN.le
  linarith only [hc, hp, hid, hpay, hlight]

#print axioms credit_sum
#print axioms actual_family_bound
end
end JSP233.WitnessFamily80470
