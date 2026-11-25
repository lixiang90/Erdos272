module

public import Erdos272.Counting.N80470.WitnessPieceBound80470
public import Erdos272.Counting.N80470.WitnessFamily80470

@[expose] public section

namespace JSP233.WitnessActualFamily80470
open StarCompletion APGeometry SourceBridge208
open CrossBandCredit208 CrossBandCleanup208 CleanupEval208 ActualCleanupEval208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def RowLight (r : Row) (hlen : r.bands.length=7) (n W : ℕ) : ℕ :=
  ∑ b : CrossBandCredit208.Band, if (At r hlen b).E ≤ 1 then 0 else
    ∑ d ∈ Finset.Icc 1 n,
      WitnessPieceBound80470.Bound r.high d (At r hlen b).T (At r hlen b).E
        (block (At r hlen b) d) (At r hlen b).U W

theorem row_light_eq (r : Row) (hlen : r.bands.length=7) (n W : ℕ) :
    RowLight r hlen n W = ∑ d ∈ Finset.Icc 1 n, ∑ b : CrossBandCredit208.Band,
      WitnessPieceBound80470.Bound r.high d (At r hlen b).T (At r hlen b).E
        (block (At r hlen b) d) (At r hlen b).U W := by
  unfold RowLight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs with he
  · symm
    apply Finset.sum_eq_zero
    intro d hd
    exact if_pos he
  · rfl

theorem actual_family_bound {s : System} (v : Valid s)
    (r : Row) (hlen : r.bands.length=7) {n W L : ℕ} {out : Totals}
    (hf : ChunkFacts r 1 n out) (hDn : s.D ≤ n)
    (hmatch : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : CrossBandCredit208.Band,
      (At r hlen b).T=s.T d b ∧ (At r hlen b).E=s.E d b ∧
      (At r hlen b).U=s.U d b ∧ block (At r hlen b) d=s.B d b)
    (hgrid : 0 < r.grid) (hlow : 0 < r.low) (hlN : r.low ≤ s.N)
    (hNh : s.N ≤ r.high) (hei : s.e ≤ r.i)
    {F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlegal : Legal (Ground s.N) F) (hsub : s.F ⊆ F)
    (hA : A₀ ∈ F) (hW : A₀.card ≤ W)
    (hlight : RowLight r hlen n W ≤ L) :
    (s.F.card : ℝ) ≤
      (s.N : ℝ)^2*ResidualAggregate208.Price s.e (ResidualTwoCensus208.H s.M)+
        (253/35 : ℝ)*s.N+(L : ℝ)+(s.N : ℝ)*((out.net : ℝ)/r.grid) := by
  let pieceLight : ℕ → CrossBandCredit208.Band → ℝ := fun d b =>
    WitnessPieceBound80470.Bound r.high d (s.T d b) (s.E d b) (s.B d b) (s.U d b) W
  have hcredit : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : CrossBandCredit208.Band,
      ((s.Piece d b).card : ℝ)+(s.T d b : ℝ)*(PhaseSystem82427.Heavy s d b).card ≤
        pieceLight d b+(PhaseSystem82427.HeavyPiece s d b).card := by
    intro d hd b
    exact WitnessPieceBound80470.actual_piece_bound v hd b hNh hlegal hsub hA hW
  have hsum : (∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band,
      pieceLight d b) ≤ (L : ℝ) := by
    have hm : (∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band,
        WitnessPieceBound80470.Bound r.high d (s.T d b) (s.E d b)
          (s.B d b) (s.U d b) W) ≤ RowLight r hlen n W := by
      calc
        _ = ∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band,
            WitnessPieceBound80470.Bound r.high d (At r hlen b).T (At r hlen b).E
              (block (At r hlen b) d) (At r hlen b).U W := by
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro b hb
          obtain ⟨hT,hE,hU,hB⟩ := hmatch d hd b
          rw [hT,hE,hU,hB]
        _ ≤ _ := by
          rw [row_light_eq]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro d hd
            exact Finset.mem_Icc.mpr
              ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hDn⟩
          · intros
            exact Nat.zero_le _
    have hh := hm.trans hlight
    dsimp only [pieceLight]
    exact_mod_cast hh
  exact WitnessFamily80470.actual_family_bound v r hlen hf hDn hmatch
    hgrid hlow hlN hNh hei pieceLight hcredit hsum

#print axioms row_light_eq
#print axioms actual_family_bound
end
end JSP233.WitnessActualFamily80470
