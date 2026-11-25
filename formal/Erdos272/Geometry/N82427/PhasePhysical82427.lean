module

public import Erdos272.Geometry.N82427.PhaseBand82427
public import Erdos272.Geometry.N82427.PhaseCleanup82427

@[expose] public section

namespace JSP233.PhasePhysical82427
open CrossBandCredit208 CrossBandCleanup208 PhaseSystem82427
open CleanupEval208 ActualCleanupEval208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_step {s : System} (v : Valid s) {d : ℕ}
    (hd : d ∈ Finset.Icc 1 s.D) (r : Row) (hlen : r.bands.length=7)
    (hmatch : ∀ b : CrossBandCredit208.Band, (At r hlen b).T=s.T d b ∧
      (At r hlen b).E=s.E d b ∧ (At r hlen b).U=s.U d b ∧ block (At r hlen b) d=s.B d b)
    (hg : (step r d).good=true) (hlN : r.low ≤ s.N) (hNh : s.N ≤ r.high) (hei : s.e ≤ r.i) :
    (∑ b : CrossBandCredit208.Band, ((Heavy s d b).card : ℝ)*
      (((min s.N (∑ a : CrossBandCredit208.Band, PhaseBand82427.RawWindows s d a)+(s.e-1) : ℕ) : ℝ)/s.N-
        (s.T d b : ℝ)/s.N)) ≤ ((step r d).totals.net : ℝ)/r.grid := by
  rcases step_good hg with ⟨hgood, hG, hL, hLH, hD⟩
  let z : CrossBandCredit208.Band → ℕ := fun b => (bandValue r d (At r hlen b)).windows
  let H : CrossBandCredit208.Band → ℕ := fun b => (bandValue r d (At r hlen b)).count
  have hband : ∀ b : CrossBandCredit208.Band, BandGood r d (At r hlen b) (bandValue r d (At r hlen b)) :=
    fun b => hgood _ (List.getElem_mem (by rw [hlen]; exact b.isLt))
  have hbounds : ∀ b : CrossBandCredit208.Band, (Heavy s d b).card ≤ H b ∧
      (PhaseBand82427.RawWindows s d b : ℝ)/s.N ≤ (z b : ℝ)/r.grid := by
    intro b
    exact PhaseBand82427.actual_band_value v hd b r (At r hlen b) (hmatch b).1 (hmatch b).2.1
      (hmatch b).2.2.1 (hmatch b).2.2.2 (hband b) hG hL hlN hNh
  have hown : ∀ b : CrossBandCredit208.Band, 0 < H b →
      (s.T d b-s.E d b+1)*r.grid ≤ min r.grid (z b)*r.high := by
    intro b
    have hh := (hband b).2.2.2.2.2.2.2.2
    simpa only [(hmatch b).1, (hmatch b).2.1] using hh
  have hh := CrossBandNormalize208.actual_normalized_net Finset.univ (s.T d) (s.E d)
    (PhaseBand82427.RawWindows s d) z H (fun b => (Heavy s d b).card) hG hL hlN hNh hei
    (fun b hb => (v.ET d hd b).le) (fun b hb => (v.E_le d hd b).trans hei)
    (fun b hb => (hbounds b).2) (fun b hb => hown b) (fun b hb => (hbounds b).1)
  have hz : (∑ b : CrossBandCredit208.Band, z b)=(foldBands r d r.bands).value.windows :=
    fold_at BandValue.windows rfl (fun a b => rfl) r d hlen
  have hn : (∑ b : CrossBandCredit208.Band, H b)=(foldBands r d r.bands).value.count :=
    fold_at BandValue.count rfl (fun a b => rfl) r d hlen
  have hc : (∑ b : CrossBandCredit208.Band, H b*(s.T d b*r.grid/r.high))=(foldBands r d r.bands).value.credit := by
    rw [←fold_at BandValue.credit rfl (fun a b => rfl) r d hlen]
    apply Finset.sum_congr rfl
    intro b hb
    rw [CleanupChecked208.band_credit_eq, (hmatch b).1]
  have he : CrossBandNormalize208.IntegerNet r.grid r.low r.high r.i (s.T d) z H=
      (step r d).totals.net := by
    simp only [CrossBandNormalize208.IntegerNet, hz, hn, hc, CleanupEval208.step, Nat.mul_add]
  change _ ≤ (CrossBandNormalize208.IntegerNet r.grid r.low r.high r.i (s.T d) z H : ℝ)/r.grid at hh
  rw [he] at hh
  exact hh

theorem net_identity (s : System) (hN : (s.N : ℝ) ≠ 0) :
    (s.N : ℝ)*(∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band, ((Heavy s d b).card : ℝ)*
      (((min s.N (∑ a : CrossBandCredit208.Band, PhaseBand82427.RawWindows s d a)+(s.e-1) : ℕ) : ℝ)/s.N-
        (s.T d b : ℝ)/s.N))=
      ((∑ d ∈ Finset.Icc 1 s.D, (∑ b : CrossBandCredit208.Band, (Heavy s d b).card)*
        (min s.N (∑ a : CrossBandCredit208.Band, PhaseBand82427.RawWindows s d a)+(s.e-1)) : ℕ) : ℝ)-
      (∑ d ∈ Finset.Icc 1 s.D, ∑ b : CrossBandCredit208.Band, (s.T d b : ℝ)*(Heavy s d b).card) := by
  rw [Finset.mul_sum]
  simp only [Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  field_simp [hN]
  <;> ring

#print axioms actual_step
#print axioms net_identity
end
end JSP233.PhasePhysical82427
