module

public import Erdos272.Resources.ActualCleanupEval208
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! The light cap is an actual ground upper bound, independent of the
low/high window used by the coupled cleanup count and normalization. -/
namespace JSP233.LightCap216
open StarCompletion APGeometry NearAP36
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208
open CrossBandMenu208 CrossBandNormalize208 CleanupEval208 ActualBandEval208
open ActualCleanupEval208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def PieceLight (s : System) (cap d : ℕ) (b : CrossBandCredit208.Band) : ℕ :=
  if s.E d b ≤ 1 then 0 else
    LightPrice208.Closed cap d (s.T d b) (s.E d b) (s.B d b) (s.U d b+s.B d b-3)

theorem actual_piece_light_cap {s : System} (v : Valid s) {cap d : ℕ}
    (hcap : s.N ≤ cap) (hd : d∈Finset.Icc 1 s.D) (b : CrossBandCredit208.Band) :
    ((s.Piece d b).card : ℝ)+(s.T d b : ℝ)*(s.Heavy d b).card ≤
      PieceLight s cap d b+(s.HeavyPiece d b).card := by
  by_cases hE1 : s.E d b≤1
  · have hp := actual_piece_empty v hd b hE1
    have hh : s.Heavy d b=∅ := by
      simp only [System.Heavy,BandSystem208.Heavy,hp,Finset.image_empty,Finset.filter_empty]
    have hhp : s.HeavyPiece d b=∅ := by simp only [System.HeavyPiece,hp,Finset.filter_empty]
    simp only [PieceLight,if_pos hE1,hp,hh,hhp,Finset.card_empty,Nat.cast_zero,mul_zero,zero_add,le_refl]
  · have hc := v.piece_credit hd b
    have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1;omega
    have hB2 := v.B_two d hd b
    have hET := v.ET d hd b
    have hTV : s.T d b≤s.U d b+s.B d b-3 := by
      have hTU := v.TU d hd b
      omega
    have hm := closed_mono hcap hd0 (by omega : 0<s.B d b) hET.le hTV
    have hmR : s.Light d b≤(PieceLight s cap d b : ℝ) := by
      simp only [PieceLight,if_neg hE1]
      change (LightPrice208.Closed s.N d (s.T d b) (s.E d b) (s.B d b)
        (s.U d b+s.B d b-3) : ℝ)≤_
      exact_mod_cast hm
    linarith only [hc,hmR]

theorem actual_eval_credit_cap {s : System} (v : Valid s) {cap : ℕ}
    (hcap : s.N ≤ cap) :
    (s.F.card : ℝ)+(∑d∈Finset.Icc 1 s.D,∑b : CrossBandCredit208.Band,
      (s.T d b : ℝ)*(s.Heavy d b).card) ≤
      (∑d∈Finset.Icc 1 s.D,∑b : CrossBandCredit208.Band,(PieceLight s cap d b : ℝ))+
        (s.G.card : ℝ) := by
  have hh := Finset.sum_le_sum (fun d (hd : d∈Finset.Icc 1 s.D)=>
    Finset.sum_le_sum (s := (Finset.univ : Finset CrossBandCredit208.Band))
      (fun b _ => actual_piece_light_cap v hcap hd b))
  have hp : (s.F.card : ℝ)=∑d∈Finset.Icc 1 s.D,∑b : CrossBandCredit208.Band,
      ((s.Piece d b).card : ℝ) := by exact_mod_cast s.card_partition v.step_range
  have hg : (s.G.card : ℝ)=∑d∈Finset.Icc 1 s.D,∑b : CrossBandCredit208.Band,
      ((s.HeavyPiece d b).card : ℝ) := by exact_mod_cast s.g_card_partition v.step_range
  simp only [Finset.sum_add_distrib] at hh
  rw [←hp,←hg] at hh
  exact hh

/-- A numeric light-sum certificate is separate from the full actual coupled
cleanup ChunkFacts. Neither one can stand in for the other. -/
theorem actual_family_bound_cap {s : System} (v : Valid s) (r : Row)
    (hlen : r.bands.length=7) {n cap light : ℕ} {out : Totals}
    (hf : ChunkFacts r 1 n out) (hDn : s.D≤n)
    (hmatch : ∀d∈Finset.Icc 1 s.D,∀b : CrossBandCredit208.Band,
      (At r hlen b).T=s.T d b ∧ (At r hlen b).E=s.E d b ∧
      (At r hlen b).U=s.U d b ∧ block (At r hlen b) d=s.B d b)
    (hgrid : 0<r.grid) (hlow : 0<r.low) (hlN : r.low≤s.N)
    (hNh : s.N≤r.high) (hei : s.e≤r.i) (hcap : s.N≤cap)
    (hlight : (∑d∈Finset.Icc 1 s.D,∑b : CrossBandCredit208.Band,PieceLight s cap d b)≤light) :
    (s.F.card : ℝ)≤(s.N : ℝ)^2*ResidualAggregate208.Price s.e (ResidualTwoCensus208.H s.M)+
      (253/35 : ℝ)*s.N+light+(s.N : ℝ)*((out.net : ℝ)/r.grid) := by
  have hsub : Finset.Icc 1 s.D⊆Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hDn⟩
  have hg : ∀d∈Finset.Icc 1 s.D,(step r d).good=true :=
    fun d hd=>CleanupRowBounds208.good_Icc hf (hsub hd)
  have hc := actual_eval_credit_cap v hcap
  have hp := actual_heavy_cleanup s v (RawWindows s) (by intros;exact le_rfl)
  have hN : (0 : ℝ)<s.N := by exact_mod_cast (show 0<s.N by omega)
  have hid := physical_net_identity s hN.ne'
  have hnet := Finset.sum_le_sum (fun d (hd : d∈Finset.Icc 1 s.D)=>
    actual_step v hd r hlen (hmatch d hd) (hg d hd) hlN hNh hei)
  have hnetmore : (∑d∈Finset.Icc 1 s.D,((step r d).totals.net : ℝ)/r.grid)≤
      ∑d∈Finset.Icc 1 n,((step r d).totals.net : ℝ)/r.grid :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros;positivity)
  have hrow := CleanupRowBounds208.normalized_row_bound hf
    (fun d=>((step r d).totals.net : ℝ)/r.grid) (by intros;exact le_rfl)
  have hpay := mul_le_mul_of_nonneg_left (hnet.trans (hnetmore.trans hrow)) hN.le
  have hlR : (∑d∈Finset.Icc 1 s.D,∑b : CrossBandCredit208.Band,
      (PieceLight s cap d b : ℝ))≤(light : ℝ) := by exact_mod_cast hlight
  linarith only [hc,hp,hid,hpay,hlR]

#print axioms actual_piece_light_cap
#print axioms actual_eval_credit_cap
#print axioms actual_family_bound_cap
end
end JSP233.LightCap216
