module

public import Erdos272.Geometry.N82427.PhaseSlope82427
public import Erdos272.Geometry.N82427.PhaseRamp82427

@[expose] public section

namespace JSP233.PhaseRampSlope82427
open PhaseSlope82427 ClassCount158375 CleanupEval208 ActualCleanupEval208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

structure RampTerm where
  p : ℕ
  count : ℕ
  deriving DecidableEq, Repr

def RampA (b : CleanupEval208.Band) : ℕ := b.T-b.E+1
def RampV (b : CleanupEval208.Band) (p : ℕ) : ℕ := b.U+OwnerBlock b p-3
def RampC (b : CleanupEval208.Band) (p : ℕ) : ℕ := RampV b p-b.E+1
def RampLength (low : ℕ) (b : CleanupEval208.Band) (p : ℕ) : ℕ :=
  low*(RampV b p-b.T)/(RampA b*RampC b p)

def RampFacts (high D : ℕ) (b : CleanupEval208.Band) (rs : Finset RampTerm) : Prop :=
  (b.E ≤ 1 → rs=∅) ∧
  (∀ t ∈ rs, ∀ u ∈ rs, t.p=u.p → t=u) ∧
  ∀ t ∈ rs, b.E ≤ b.T ∧ b.T ≤ RampV b t.p ∧ high/RampA b ≤ D

def RampSelected (N : ℕ) (b : CleanupEval208.Band) (rs : Finset RampTerm) : Finset ℕ :=
  rs.biUnion (fun t => PhaseRamp82427.Steps N (RampA b) (RampC b t.p) t.p)

def BandRampSlope (rs : Finset RampTerm) : ℕ := ∑ t ∈ rs, t.count

theorem ramp_selected_subset {N high D : ℕ} {b : CleanupEval208.Band} {rs : Finset RampTerm}
    (hN : N ≤ high) (hf : RampFacts high D b rs) : RampSelected N b rs ⊆ Finset.Icc 1 D := by
  intro d hd
  obtain ⟨t,ht,hd⟩ := Finset.mem_biUnion.mp hd
  have hp := hf.2.2 t ht
  have hm := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1)
  have hdpos : 1 ≤ d := (Nat.succ_pos _).trans_le hm.1
  exact Finset.mem_Icc.mpr ⟨hdpos,hm.2.trans ((Nat.div_le_div_right hN).trans hp.2.2)⟩

theorem ramp_count_lower {N low high D : ℕ} {b : CleanupEval208.Band} {rs : Finset RampTerm}
    (hlo : low ≤ N) (hf : RampFacts high D b rs)
    (hc : ∀ t ∈ rs, Certificate t.p (RampLength low b t.p) t.count) :
    BandRampSlope rs ≤ (RampSelected N b rs).card := by
  have hdis : (rs : Set RampTerm).PairwiseDisjoint
      (fun t => PhaseRamp82427.Steps N (RampA b) (RampC b t.p) t.p) := by
    intro t ht u hu hne
    apply Finset.disjoint_left.mpr
    intro d hdt hdu
    have htgate := (Finset.mem_filter.mp hdt).2
    have hugate := (Finset.mem_filter.mp hdu).2
    exact hne (hf.2.1 t ht u hu (htgate.symm.trans hugate))
  unfold BandRampSlope RampSelected
  rw [Finset.card_biUnion hdis]
  apply Finset.sum_le_sum
  intro t ht
  have hp := hf.2.2 t ht
  have hA : 0 < RampA b := by unfold RampA; omega
  have hAC : RampA b ≤ RampC b t.p := by unfold RampA RampC; omega
  have hdelta : RampC b t.p-RampA b=RampV b t.p-b.T := by unfold RampA RampC; omega
  have hh := PhaseRamp82427.physical_count (N:=N) hA hAC hlo
    (by simpa only [hdelta,RampLength] using hc t ht)
  exact hh

theorem ramp_at_step {N high D d : ℕ} {b : CleanupEval208.Band} {rs : Finset RampTerm}
    (hf : RampFacts high D b rs) (hd : d ∈ RampSelected N b rs) :
    ¬b.E ≤ 1 ∧ 0 < d ∧ b.T-b.E+1 ≤ N/d ∧ N/d+b.E ≤ b.U+block b d-3 := by
  obtain ⟨t,ht,hd⟩ := Finset.mem_biUnion.mp hd
  have hp := hf.2.2 t ht
  have hA : 0 < RampA b := by unfold RampA; omega
  have hAC : RampA b ≤ RampC b t.p := by unfold RampA RampC; omega
  obtain ⟨hdpos,hl,hh,hgate⟩ := PhaseRamp82427.mem_steps hA hAC hd
  have hb : block b d=OwnerBlock b t.p := by
    change OwnerBlock b (StepClass208.PrimeGate d)=OwnerBlock b t.p
    rw [hgate]
  refine ⟨?_,hdpos,hl,?_⟩
  · intro he
    rw [hf.1 he] at ht
    exact Finset.notMem_empty t ht
  · rw [hb]
    change N/d+b.E ≤ RampV b t.p
    unfold RampC at hh
    omega

theorem joint_selected_increment {N high D d : ℕ} {b : CleanupEval208.Band}
    {ts : Finset Term} {rs : Finset RampTerm}
    (hf : BandFacts high D b ts) (hr : RampFacts high D b rs)
    (hd : d ∈ Selected N ts) (hdr : d ∈ RampSelected N b rs) :
    BandCost N d b+b.T+1 ≤ BandCost (N+1) d b := by
  obtain ⟨he,hdpos,hlo,hhi⟩ := ramp_at_step hr hdr
  obtain ⟨t,ht,hd⟩ := Finset.mem_biUnion.mp hd
  have hterm := hf.2.2.2 t ht
  obtain ⟨_,hdq,hgate⟩ := ClassCount158375.mem_steps hterm.1 hd
  have hb : block b d=OwnerBlock b t.p := by
    change OwnerBlock b (StepClass208.PrimeGate d)=OwnerBlock b t.p
    rw [hgate]
  obtain ⟨hB,hET,hTV⟩ := shape_block hf.1 d
  have hq : b.T-b.E+((t.q-(b.T-b.E))/OwnerBlock b t.p)*block b d=N/d := by
    rw [hb]
    exact hterm.2.2.symm.trans hdq.symm
  simpa only [BandCost,if_neg he] using
    PhaseRamp82427.price_joint_increment hdpos hB hET hTV hq hlo hhi

theorem band_increment {N low high D : ℕ} {b : CleanupEval208.Band}
    {ts : Finset Term} {rs : Finset RampTerm}
    (hlo : low ≤ N) (hhi : N ≤ high) (hf : BandFacts high D b ts)
    (hr : RampFacts high D b rs)
    (hc : ∀ t ∈ ts, Certificate t.p (low/(t.q*(t.q+1))) t.count)
    (hcr : ∀ t ∈ rs, Certificate t.p (RampLength low b t.p) t.count) :
    (∑ d ∈ Finset.Icc 1 D, BandCost N d b)+(BandSlope b ts+BandRampSlope rs) ≤
      ∑ d ∈ Finset.Icc 1 D, BandCost (N+1) d b := by
  have hp : ∀ d ∈ Finset.Icc 1 D,
      BandCost N d b+(if d ∈ Selected N ts then b.T else 0)+
        (if d ∈ RampSelected N b rs then 1 else 0) ≤ BandCost (N+1) d b := by
    intro d hd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    by_cases hs : d ∈ Selected N ts
    · by_cases hsr : d ∈ RampSelected N b rs
      · simpa only [if_pos hs,if_pos hsr] using joint_selected_increment hf hr hs hsr
      · simpa only [if_pos hs,if_neg hsr,Nat.add_zero] using selected_increment hf hs
    · by_cases hsr : d ∈ RampSelected N b rs
      · obtain ⟨he,_,hl,hh⟩ := ramp_at_step hr hsr
        have h := PhaseRamp82427.price_ramp_increment (B:=block b d) hdpos hf.1.1 hl hh
        simpa only [if_neg hs,if_pos hsr,Nat.add_zero,BandCost,if_neg he] using h
      · simpa only [if_neg hs,if_neg hsr,Nat.add_zero] using band_cost_mono (by omega) hdpos hf.1
  have hsum := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib] at hsum
  have hs := selected_subset hhi hf
  have hrs := ramp_selected_subset hhi hr
  have heq : (Finset.Icc 1 D).filter (fun d => d ∈ Selected N ts)=Selected N ts := by
    ext d
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hs h,h⟩⟩
  have her : (Finset.Icc 1 D).filter (fun d => d ∈ RampSelected N b rs)=RampSelected N b rs := by
    ext d
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hrs h,h⟩⟩
  have hextra : (∑ d ∈ Finset.Icc 1 D,if d ∈ Selected N ts then b.T else 0)=b.T*(Selected N ts).card := by
    rw [←Finset.sum_filter,heq]
    simp [Nat.mul_comm]
  have hextrar : (∑ d ∈ Finset.Icc 1 D,if d ∈ RampSelected N b rs then 1 else 0)=(RampSelected N b rs).card := by
    rw [←Finset.sum_filter,her]
    simp
  rw [hextra,hextrar] at hsum
  have hc' := Nat.mul_le_mul_left b.T (selected_card_lower hlo hf hc)
  have hcr' := ramp_count_lower hlo hr hcr
  unfold BandSlope
  omega

def RowSlope (r : Row) (hlen : r.bands.length=7)
    (terms : CrossBandCredit208.Band → Finset Term)
    (ramps : CrossBandCredit208.Band → Finset RampTerm) : ℕ :=
  ∑ b : CrossBandCredit208.Band, (BandSlope (At r hlen b) (terms b)+BandRampSlope (ramps b))

theorem row_increment {r : Row} {hlen : r.bands.length=7} {D N : ℕ}
    {terms : CrossBandCredit208.Band → Finset Term}
    {ramps : CrossBandCredit208.Band → Finset RampTerm}
    (hlo : r.low ≤ N) (hhi : N ≤ r.high)
    (hf : ∀ b, BandFacts r.high D (At r hlen b) (terms b))
    (hr : ∀ b, RampFacts r.high D (At r hlen b) (ramps b))
    (hc : ∀ b, ∀ t ∈ terms b, Certificate t.p (r.low/(t.q*(t.q+1))) t.count)
    (hcr : ∀ b, ∀ t ∈ ramps b, Certificate t.p (RampLength r.low (At r hlen b) t.p) t.count) :
    RowLight r hlen D N+RowSlope r hlen terms ramps ≤ RowLight r hlen D (N+1) := by
  rw [row_light_eq_sum_band,row_light_eq_sum_band]
  unfold RowSlope
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun b _ => band_increment hlo hhi (hf b) (hr b) (hc b) (hcr b))

theorem row_affine {r : Row} {hlen : r.bands.length=7} {D N : ℕ}
    {terms : CrossBandCredit208.Band → Finset Term}
    {ramps : CrossBandCredit208.Band → Finset RampTerm}
    (hlo : r.low ≤ N) (hhi : N ≤ r.high)
    (hf : ∀ b, BandFacts r.high D (At r hlen b) (terms b))
    (hr : ∀ b, RampFacts r.high D (At r hlen b) (ramps b))
    (hc : ∀ b, ∀ t ∈ terms b, Certificate t.p (r.low/(t.q*(t.q+1))) t.count)
    (hcr : ∀ b, ∀ t ∈ ramps b, Certificate t.p (RampLength r.low (At r hlen b) t.p) t.count) :
    RowLight r hlen D N+RowSlope r hlen terms ramps*(r.high-N) ≤ RowLight r hlen D r.high := by
  have hk : ∀ k, N+k ≤ r.high →
      RowLight r hlen D N+RowSlope r hlen terms ramps*k ≤ RowLight r hlen D (N+k) := by
    intro k
    induction k with
    | zero => intro h; simp
    | succ k ih =>
        intro h
        have hp := ih (by omega)
        have hs := row_increment (by omega : r.low ≤ N+k) (by omega : N+k ≤ r.high) hf hr hc hcr
        have he : N+k.succ=(N+k)+1 := by omega
        rw [he,Nat.mul_succ]
        nlinarith only [hp,hs]
  have h := hk (r.high-N) (by omega)
  simpa only [Nat.add_sub_of_le hhi] using h

#print axioms ramp_selected_subset
#print axioms ramp_count_lower
#print axioms ramp_at_step
#print axioms joint_selected_increment
#print axioms band_increment
#print axioms row_increment
#print axioms row_affine
end
end JSP233.PhaseRampSlope82427
