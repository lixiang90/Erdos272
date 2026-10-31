import Erdos272.Resources.ActualBandEval208
import Erdos272.Resources.CleanupRowBounds208

namespace JSP233.ActualCleanupEval208
open StarCompletion APGeometry NearAP36
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208 CrossBandMenu208 CrossBandNormalize208
open CleanupEval208 ActualBandEval208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 200000

def At (r : Row) (hlen : r.bands.length=7) (b : CrossBandCredit208.Band) : CleanupEval208.Band :=
  r.bands[b.val]'(by rw [hlen];exact b.isLt)

theorem fold_at (field : BandValue→ℕ) (hz : field bandZero=0)
    (ha : ∀a b,field (bandAdd a b)=field a+field b) (r : Row) (d : ℕ) (hlen : r.bands.length=7) :
    (∑b : CrossBandCredit208.Band,field (bandValue r d (At r hlen b)))=
      field (foldBands r d r.bands).value := by
  rw [CleanupChecked208.fold_sum field hz ha]
  exact Fintype.sum_equiv (finCongr hlen).symm _ _ (by intro b;rfl)

theorem actual_step {s : System} (v : Valid s) {d : ℕ}
    (hd : d∈Finset.Icc 1 s.D) (r : Row) (hlen : r.bands.length=7)
    (hmatch : ∀b : CrossBandCredit208.Band,(At r hlen b).T=s.T d b ∧
      (At r hlen b).E=s.E d b ∧ (At r hlen b).U=s.U d b ∧ block (At r hlen b) d=s.B d b)
    (hg : (step r d).good=true) (hlN : r.low≤s.N) (hNh : s.N≤r.high) (hei : s.e≤r.i) :
    (∑b : CrossBandCredit208.Band,((s.Heavy d b).card : ℝ)*
      (((min s.N (∑a : CrossBandCredit208.Band,RawWindows s d a)+(s.e-1) : ℕ) : ℝ)/s.N-(s.T d b : ℝ)/s.N))≤
      ((step r d).totals.net : ℝ)/r.grid := by
  rcases step_good hg with ⟨hgood,hG,hL,hLH,hD⟩
  let z : CrossBandCredit208.Band→ℕ := fun b=>(bandValue r d (At r hlen b)).windows
  let H : CrossBandCredit208.Band→ℕ := fun b=>(bandValue r d (At r hlen b)).count
  have hband : ∀b : CrossBandCredit208.Band,BandGood r d (At r hlen b) (bandValue r d (At r hlen b)) := by
    intro b
    exact hgood _ (List.getElem_mem (by rw [hlen];exact b.isLt))
  have hb : ∀b : CrossBandCredit208.Band,(s.Heavy d b).card≤H b ∧
      (RawWindows s d b : ℝ)/s.N≤(z b : ℝ)/r.grid := by
    intro b
    exact actual_band_value v hd b r (At r hlen b) (hmatch b).1 (hmatch b).2.1
      (hmatch b).2.2.1 (hmatch b).2.2.2 (hband b) hG hL hlN hNh
  have hown : ∀b : CrossBandCredit208.Band,0<H b→
      (s.T d b-s.E d b+1)*r.grid≤min r.grid (z b)*r.high := by
    intro b
    have hh := (hband b).2.2.2.2.2.2.2.2
    simpa only [(hmatch b).1,(hmatch b).2.1] using hh
  have hh := actual_step_normalized s v hd hG hL hlN hNh hei z H
    (fun b=>(hb b).2) hown (fun b=>(hb b).1)
  have hz : (∑b : CrossBandCredit208.Band,z b)=(foldBands r d r.bands).value.windows :=
    fold_at BandValue.windows rfl (fun a b=>rfl) r d hlen
  have hn : (∑b : CrossBandCredit208.Band,H b)=(foldBands r d r.bands).value.count :=
    fold_at BandValue.count rfl (fun a b=>rfl) r d hlen
  have hc : (∑b : CrossBandCredit208.Band,H b*(s.T d b*r.grid/r.high))=(foldBands r d r.bands).value.credit := by
    rw [←fold_at BandValue.credit rfl (fun a b=>rfl) r d hlen]
    apply Finset.sum_congr rfl
    intro b hb
    rw [CleanupChecked208.band_credit_eq,(hmatch b).1]
  have he : IntegerNet r.grid r.low r.high r.i (s.T d) z H=(step r d).totals.net := by
    simp only [IntegerNet,hz,hn,hc,CleanupEval208.step,Nat.mul_add]
  rw [he] at hh
  exact hh

theorem physical_net_identity (s : System) (hN : (s.N : ℝ)≠0) :
    (s.N : ℝ)*(∑d∈Finset.Icc 1 s.D,∑b : CrossBandCredit208.Band,((s.Heavy d b).card : ℝ)*
      (((min s.N (∑a : CrossBandCredit208.Band,RawWindows s d a)+(s.e-1) : ℕ) : ℝ)/s.N-(s.T d b : ℝ)/s.N))=
      ((∑d∈Finset.Icc 1 s.D,(∑b : CrossBandCredit208.Band,(s.Heavy d b).card)*
        (min s.N (∑a : CrossBandCredit208.Band,RawWindows s d a)+(s.e-1)) : ℕ) : ℝ)-
      (∑d∈Finset.Icc 1 s.D,∑b : CrossBandCredit208.Band,(s.T d b : ℝ)*(s.Heavy d b).card) := by
  rw [Finset.mul_sum]
  simp only [Nat.cast_sum,Nat.cast_mul,Finset.sum_mul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  field_simp [hN]
  <;> ring

theorem actual_eval_credit {s : System} (v : Valid s) (r : Row) (hlen : r.bands.length=7)
    (hmatch : ∀d∈Finset.Icc 1 s.D,∀b : CrossBandCredit208.Band,
      (At r hlen b).T=s.T d b ∧ (At r hlen b).E=s.E d b ∧
      (At r hlen b).U=s.U d b ∧ block (At r hlen b) d=s.B d b)
    (hg : ∀d∈Finset.Icc 1 s.D,(step r d).good=true) (hNh : s.N≤r.high) :
    (s.F.card : ℝ)+(∑d∈Finset.Icc 1 s.D,∑b : CrossBandCredit208.Band,(s.T d b : ℝ)*(s.Heavy d b).card)≤
      (∑d∈Finset.Icc 1 s.D,((step r d).totals.light : ℝ))+(s.G.card : ℝ) := by
  have hh := Finset.sum_le_sum (fun d (hd : d∈Finset.Icc 1 s.D)=>
    Finset.sum_le_sum (s := (Finset.univ : Finset CrossBandCredit208.Band)) (fun b hb=>
      actual_piece_eval_credit v hd b r (At r hlen b) (hmatch d hd b).1
        (hmatch d hd b).2.1 (hmatch d hd b).2.2.1 (hmatch d hd b).2.2.2
        ((step_good (hg d hd)).1 _ (List.getElem_mem (by rw [hlen];exact b.isLt))) hNh))
  have hp : (s.F.card : ℝ)=∑d∈Finset.Icc 1 s.D,∑b : CrossBandCredit208.Band,((s.Piece d b).card : ℝ) := by
    exact_mod_cast s.card_partition v.step_range
  have hgR : (s.G.card : ℝ)=∑d∈Finset.Icc 1 s.D,∑b : CrossBandCredit208.Band,((s.HeavyPiece d b).card : ℝ) := by
    exact_mod_cast s.g_card_partition v.step_range
  have hl : ∀d,(∑b : CrossBandCredit208.Band,((bandValue r d (At r hlen b)).light : ℝ))=((step r d).totals.light : ℝ) := by
    intro d
    have hn := fold_at BandValue.light rfl (fun a b=>rfl) r d hlen
    exact_mod_cast hn
  simp only [Finset.sum_add_distrib] at hh
  simp_rw [hl] at hh
  rw [←hp,←hgR] at hh
  exact hh

/-- A whole actual near family is paid by one global remainder bill and the
kernel-checked row totals.  The empty E≤1 pieces pay zero light cost. -/
theorem actual_family_bound {s : System} (v : Valid s) (r : Row) (hlen : r.bands.length=7)
    {n : ℕ} {out : Totals} (hf : ChunkFacts r 1 n out) (hDn : s.D≤n)
    (hmatch : ∀d∈Finset.Icc 1 s.D,∀b : CrossBandCredit208.Band,
      (At r hlen b).T=s.T d b ∧ (At r hlen b).E=s.E d b ∧
      (At r hlen b).U=s.U d b ∧ block (At r hlen b) d=s.B d b)
    (hgrid : 0<r.grid) (hlow : 0<r.low) (hlN : r.low≤s.N) (hNh : s.N≤r.high) (hei : s.e≤r.i) :
    (s.F.card : ℝ)≤(s.N : ℝ)^2*ResidualAggregate208.Price s.e (ResidualTwoCensus208.H s.M)+
      (253/35 : ℝ)*s.N+out.light+(s.N : ℝ)*((out.net : ℝ)/r.grid) := by
  have hsub : Finset.Icc 1 s.D⊆Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hDn⟩
  have hg : ∀d∈Finset.Icc 1 s.D,(step r d).good=true := fun d hd=>CleanupRowBounds208.good_Icc hf (hsub hd)
  have hc := actual_eval_credit v r hlen hmatch hg hNh
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
  have hlNat : (∑d∈Finset.Icc 1 s.D,(step r d).totals.light)≤out.light := by
    rw [CleanupRowBounds208.light_eq_Icc hf]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros;exact Nat.zero_le _)
  have hlR : (∑d∈Finset.Icc 1 s.D,((step r d).totals.light : ℝ))≤(out.light : ℝ) := by exact_mod_cast hlNat
  linarith only [hc,hp,hid,hpay,hlR]

#print axioms fold_at
#print axioms actual_step
#print axioms physical_net_identity
#print axioms actual_eval_credit
#print axioms actual_family_bound
end
end JSP233.ActualCleanupEval208
