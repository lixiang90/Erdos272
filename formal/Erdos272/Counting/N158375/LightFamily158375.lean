module

public import Erdos272.Resources.ActualCleanupEval208

@[expose] public section

namespace JSP233.LightFamily158375
open StarCompletion APGeometry NearAP36
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208
open CrossBandMenu208 CrossBandNormalize208 CleanupEval208 ActualBandEval208
open ActualCleanupEval208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def ActiveLight (s : System) (d : ℕ) (b : CrossBandCredit208.Band) : ℝ :=
  if s.E d b ≤ 1 then 0 else s.Light d b

theorem actual_piece_dynamic {s : System} (v : Valid s) {d : ℕ}
    (hd : d ∈ Finset.Icc 1 s.D) (b : CrossBandCredit208.Band) :
    ((s.Piece d b).card : ℝ)+(s.T d b : ℝ)*(s.Heavy d b).card ≤
      ActiveLight s d b+(s.HeavyPiece d b).card := by
  by_cases he : s.E d b ≤ 1
  · have hp := actual_piece_empty v hd b he
    have hh : s.Heavy d b = ∅ := by
      simp only [System.Heavy, BandSystem208.Heavy, hp, Finset.image_empty, Finset.filter_empty]
    have hhp : s.HeavyPiece d b = ∅ := by
      simp only [System.HeavyPiece, hp, Finset.filter_empty]
    simp only [ActiveLight, if_pos he, hp, hh, hhp, Finset.card_empty,
      Nat.cast_zero, mul_zero, add_zero, zero_add, le_refl]
  · simpa only [ActiveLight, if_neg he] using v.piece_credit hd b

theorem actual_credit_sum {s : System} (v : Valid s) :
    (s.F.card : ℝ)+(∑ d ∈ Finset.Icc 1 s.D,
      ∑ b : CrossBandCredit208.Band, (s.T d b : ℝ)*(s.Heavy d b).card) ≤
      (∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band, ActiveLight s d b)+s.G.card := by
  have hh := Finset.sum_le_sum (fun d (hd : d ∈ Finset.Icc 1 s.D) =>
    Finset.sum_le_sum (s := (Finset.univ : Finset CrossBandCredit208.Band))
      (fun b _ => actual_piece_dynamic v hd b))
  have hp : (s.F.card : ℝ) = ∑ d ∈ Finset.Icc 1 s.D,
      ∑ b : CrossBandCredit208.Band, ((s.Piece d b).card : ℝ) := by
    exact_mod_cast s.card_partition v.step_range
  have hg : (s.G.card : ℝ) = ∑ d ∈ Finset.Icc 1 s.D,
      ∑ b : CrossBandCredit208.Band, ((s.HeavyPiece d b).card : ℝ) := by
    exact_mod_cast s.g_card_partition v.step_range
  simp only [Finset.sum_add_distrib] at hh
  rw [←hp, ←hg] at hh
  exact hh

theorem actual_family_bound_with_light {s : System} (v : Valid s)
    (r : Row) (hlen : r.bands.length=7) {n : ℕ} {out : Totals}
    (hf : ChunkFacts r 1 n out) (hDn : s.D ≤ n)
    (hmatch : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : CrossBandCredit208.Band,
      (At r hlen b).T=s.T d b ∧ (At r hlen b).E=s.E d b ∧
      (At r hlen b).U=s.U d b ∧ block (At r hlen b) d=s.B d b)
    (hgrid : 0 < r.grid) (hlow : 0 < r.low) (hlN : r.low ≤ s.N)
    (hNh : s.N ≤ r.high) (hei : s.e ≤ r.i) {light : ℝ}
    (hlight : (∑ d ∈ Finset.Icc 1 s.D,
      ∑ b : CrossBandCredit208.Band, ActiveLight s d b) ≤ light) :
    (s.F.card : ℝ) ≤ (s.N : ℝ)^2*ResidualAggregate208.Price s.e (ResidualTwoCensus208.H s.M)+
      (253/35 : ℝ)*s.N+light+(s.N : ℝ)*((out.net : ℝ)/r.grid) := by
  have hsub : Finset.Icc 1 s.D ⊆ Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hDn⟩
  have hg : ∀ d ∈ Finset.Icc 1 s.D, (step r d).good=true :=
    fun d hd => CleanupRowBounds208.good_Icc hf (hsub hd)
  have hc := actual_credit_sum v
  have hp := actual_heavy_cleanup s v (RawWindows s) (by intros; exact le_rfl)
  have hN : (0 : ℝ) < s.N := by exact_mod_cast (show 0 < s.N by omega)
  have hid := physical_net_identity s hN.ne'
  have hnet := Finset.sum_le_sum (fun d (hd : d ∈ Finset.Icc 1 s.D) =>
    actual_step v hd r hlen (hmatch d hd) (hg d hd) hlN hNh hei)
  have hnetmore : (∑ d ∈ Finset.Icc 1 s.D, ((step r d).totals.net : ℝ)/r.grid) ≤
      ∑ d ∈ Finset.Icc 1 n, ((step r d).totals.net : ℝ)/r.grid :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  have hrow := CleanupRowBounds208.normalized_row_bound hf
    (fun d => ((step r d).totals.net : ℝ)/r.grid) (by intros; exact le_rfl)
  have hpay := mul_le_mul_of_nonneg_left (hnet.trans (hnetmore.trans hrow)) hN.le
  linarith only [hc, hp, hid, hpay, hlight]

def BandCost (N d : ℕ) (b : CleanupEval208.Band) : ℕ :=
  if b.E ≤ 1 then 0 else LightPrice208.Closed N d b.T b.E (block b d) (b.U+block b d-3)

def RowLight (r : Row) (hlen : r.bands.length=7) (D N : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 D, ∑ b : CrossBandCredit208.Band, BandCost N d (At r hlen b)

theorem high_light_total {r : Row} {hlen : r.bands.length=7} {n : ℕ} {out : Totals}
    (hf : ChunkFacts r 1 n out) : RowLight r hlen n r.high = out.light := by
  unfold RowLight
  rw [CleanupRowBounds208.light_eq_Icc hf]
  apply Finset.sum_congr rfl
  intro d hd
  change (∑ b : CrossBandCredit208.Band, BandCost r.high d (At r hlen b)) =
    (foldBands r d r.bands).value.light
  calc
    _ = ∑ b : CrossBandCredit208.Band, (bandValue r d (At r hlen b)).light := by
      apply Finset.sum_congr rfl
      intro b hb
      unfold BandCost bandValue
      split_ifs <;> rfl
    _ = _ := fold_at BandValue.light rfl (fun a b => rfl) r d hlen

theorem actual_light_le_row {s : System} (r : Row) (hlen : r.bands.length=7) {n : ℕ}
    (hDn : s.D ≤ n)
    (hmatch : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : CrossBandCredit208.Band,
      (At r hlen b).T=s.T d b ∧ (At r hlen b).E=s.E d b ∧
      (At r hlen b).U=s.U d b ∧ block (At r hlen b) d=s.B d b) :
    (∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band, ActiveLight s d b) ≤
      (RowLight r hlen n s.N : ℝ) := by
  have hmatchLight : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : CrossBandCredit208.Band,
      ActiveLight s d b = (BandCost s.N d (At r hlen b) : ℝ) := by
    intro d hd b
    dsimp only [ActiveLight, BandCost]
    rw [(hmatch d hd b).1, (hmatch d hd b).2.1,
      (hmatch d hd b).2.2.1, (hmatch d hd b).2.2.2]
    split_ifs
    · simp only [Nat.cast_zero]
    · rfl
  have heq : (∑ d ∈ Finset.Icc 1 s.D,
      ∑ b : CrossBandCredit208.Band, ActiveLight s d b) =
      ∑ d ∈ Finset.Icc 1 s.D,
      ∑ b : CrossBandCredit208.Band, (BandCost s.N d (At r hlen b) : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    exact Finset.sum_congr rfl (fun b _ => hmatchLight d hd b)
  rw [heq]
  have hsub : Finset.Icc 1 s.D ⊆ Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hDn⟩
  unfold RowLight
  push_cast
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)

#print axioms actual_piece_dynamic
#print axioms actual_credit_sum
#print axioms actual_family_bound_with_light
#print axioms high_light_total
#print axioms actual_light_le_row
end
end JSP233.LightFamily158375
