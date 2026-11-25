module

public import Erdos272.Counting.N158375.ClassCount158375
public import Erdos272.Counting.N158375.LightIncrement158375
public import Erdos272.Counting.N158375.LightFamily158375

@[expose] public section

namespace JSP233.LightSlope158375
open StepClass208 ClassCount158375 CleanupEval208 ActualCleanupEval208 LightFamily158375
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

structure Term where
  p : ℕ
  q : ℕ
  count : ℕ
  deriving DecidableEq, Repr

def OwnerBlock (b : CleanupEval208.Band) (p : ℕ) : ℕ :=
  match p with
  | 2 => b.b2 | 3 => b.b3 | 5 => b.b5 | 7 => b.b7 | _ => b.b11

def Shape (b : CleanupEval208.Band) : Prop :=
  b.E ≤ b.T ∧ b.T < b.U ∧ 2 ≤ b.b2 ∧ 2 ≤ b.b3 ∧ 2 ≤ b.b5 ∧
    2 ≤ b.b7 ∧ 2 ≤ b.b11

def TermFacts (high D : ℕ) (b : CleanupEval208.Band) (t : Term) : Prop :=
  0 < t.q ∧ high/t.q ≤ D ∧
    t.q = b.T-b.E+((t.q-(b.T-b.E))/OwnerBlock b t.p)*OwnerBlock b t.p

def BandFacts (high D : ℕ) (b : CleanupEval208.Band) (ts : Finset Term) : Prop :=
  Shape b ∧ (b.E ≤ 1 → ts=∅) ∧
    (∀ t ∈ ts, ∀ u ∈ ts, t.p=u.p → t.q=u.q → t=u) ∧
    ∀ t ∈ ts, TermFacts high D b t

def Selected (N : ℕ) (ts : Finset Term) : Finset ℕ :=
  ts.biUnion (fun t => Steps N t.q t.p)

def BandSlope (b : CleanupEval208.Band) (ts : Finset Term) : ℕ :=
  b.T*(∑ t ∈ ts, t.count)

def RowSlope (r : Row) (hlen : r.bands.length=7)
    (terms : CrossBandCredit208.Band → Finset Term) : ℕ :=
  ∑ b : CrossBandCredit208.Band, BandSlope (At r hlen b) (terms b)

theorem shape_block {b : CleanupEval208.Band} (h : Shape b) (d : ℕ) :
    0 < block b d ∧ b.E ≤ b.T ∧ b.T ≤ b.U+block b d-3 := by
  rcases h with ⟨hET, hTU, h2, h3, h5, h7, h11⟩
  have hp := primeGate_range d
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with hp | hp | hp | hp | hp <;> simp only [block, hp] <;> omega

theorem band_cost_mono {N H d : ℕ} {b : CleanupEval208.Band}
    (hNH : N ≤ H) (hd : 0 < d) (h : Shape b) :
    BandCost N d b ≤ BandCost H d b := by
  unfold BandCost
  split_ifs
  · exact le_refl 0
  · obtain ⟨hB, hET, hTV⟩ := shape_block h d
    exact ActualBandEval208.closed_mono hNH hd hB hET hTV

theorem selected_subset {N high D : ℕ} {b : CleanupEval208.Band} {ts : Finset Term}
    (hN : N ≤ high) (hf : BandFacts high D b ts) : Selected N ts ⊆ Finset.Icc 1 D := by
  intro d hd
  obtain ⟨t, ht, hd⟩ := Finset.mem_biUnion.mp hd
  have hterm := hf.2.2.2 t ht
  have hmem := mem_steps hterm.1 hd
  have hright := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
  exact Finset.mem_Icc.mpr ⟨by omega,
    hright.trans ((Nat.div_le_div_right (c := t.q) hN).trans hterm.2.1)⟩

theorem selected_card_lower {N low high D : ℕ} {b : CleanupEval208.Band}
    {ts : Finset Term} (hlo : low ≤ N) (hf : BandFacts high D b ts)
    (hc : ∀ t ∈ ts, Certificate t.p (low/(t.q*(t.q+1))) t.count) :
    (∑ t ∈ ts, t.count) ≤ (Selected N ts).card := by
  have hdis : (ts : Set Term).PairwiseDisjoint (fun t => Steps N t.q t.p) := by
    intro t ht u hu hne
    apply Finset.disjoint_left.mpr
    intro d hdt hdu
    have htmem := mem_steps (hf.2.2.2 t ht).1 hdt
    have humem := mem_steps (hf.2.2.2 u hu).1 hdu
    exact hne (hf.2.2.1 t ht u hu (htmem.2.2.symm.trans humem.2.2)
      (htmem.2.1.symm.trans humem.2.1))
  unfold Selected
  rw [Finset.card_biUnion hdis]
  exact Finset.sum_le_sum (fun t ht => physical_interval_count (hf.2.2.2 t ht).1 hlo (hc t ht))

theorem selected_increment {N high D d : ℕ} {b : CleanupEval208.Band} {ts : Finset Term}
    (hf : BandFacts high D b ts) (hd : d ∈ Selected N ts) :
    BandCost N d b+b.T ≤ BandCost (N+1) d b := by
  obtain ⟨t, ht, hd⟩ := Finset.mem_biUnion.mp hd
  have hterm := hf.2.2.2 t ht
  obtain ⟨hdpos, hdq, hgate⟩ := mem_steps hterm.1 hd
  have hactive : ¬b.E ≤ 1 := by
    intro he
    rw [hf.2.1 he] at ht
    exact Finset.notMem_empty t ht
  have hb : block b d = OwnerBlock b t.p := by
    change OwnerBlock b (PrimeGate d) = OwnerBlock b t.p
    rw [hgate]
  obtain ⟨hB, hET, hTV⟩ := shape_block hf.1 d
  have hq : b.T-b.E+((t.q-(b.T-b.E))/OwnerBlock b t.p)*block b d = N/d := by
    rw [hb]
    exact hterm.2.2.symm.trans hdq.symm
  simpa only [BandCost, if_neg hactive] using
    LightIncrement158375.closed_increment hdpos hB hET hTV hq

theorem band_increment {N low high D : ℕ} {b : CleanupEval208.Band} {ts : Finset Term}
    (hlo : low ≤ N) (hhi : N ≤ high) (hf : BandFacts high D b ts)
    (hc : ∀ t ∈ ts, Certificate t.p (low/(t.q*(t.q+1))) t.count) :
    (∑ d ∈ Finset.Icc 1 D, BandCost N d b)+BandSlope b ts ≤
      ∑ d ∈ Finset.Icc 1 D, BandCost (N+1) d b := by
  have hpoint : ∀ d ∈ Finset.Icc 1 D,
      BandCost N d b+(if d ∈ Selected N ts then b.T else 0) ≤ BandCost (N+1) d b := by
    intro d hd
    by_cases hs : d ∈ Selected N ts
    · simpa only [if_pos hs] using selected_increment hf hs
    · simpa only [if_neg hs, Nat.add_zero] using
        band_cost_mono (Nat.le_succ N) (by have h := (Finset.mem_Icc.mp hd).1; omega) hf.1
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib] at hsum
  have hsub := selected_subset hhi hf
  have heq : (Finset.Icc 1 D).filter (fun d => d ∈ Selected N ts) = Selected N ts := by
    ext d
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have hextra : (∑ d ∈ Finset.Icc 1 D, if d ∈ Selected N ts then b.T else 0) =
      b.T*(Selected N ts).card := by
    rw [← Finset.sum_filter, heq]
    simp [Nat.mul_comm]
  rw [hextra] at hsum
  have hcount := Nat.mul_le_mul_left b.T (selected_card_lower hlo hf hc)
  unfold BandSlope
  nlinarith only [hsum, hcount]

theorem row_light_eq_sum_band (r : Row) (hlen : r.bands.length=7) (D N : ℕ) :
    RowLight r hlen D N = ∑ b : CrossBandCredit208.Band,
      ∑ d ∈ Finset.Icc 1 D, BandCost N d (At r hlen b) := by
  unfold RowLight
  exact Finset.sum_comm

theorem row_increment {r : Row} {hlen : r.bands.length=7} {D N : ℕ}
    {terms : CrossBandCredit208.Band → Finset Term} (hlo : r.low ≤ N) (hhi : N ≤ r.high)
    (hf : ∀ b, BandFacts r.high D (At r hlen b) (terms b))
    (hc : ∀ b, ∀ t ∈ terms b, Certificate t.p (r.low/(t.q*(t.q+1))) t.count) :
    RowLight r hlen D N+RowSlope r hlen terms ≤ RowLight r hlen D (N+1) := by
  rw [row_light_eq_sum_band, row_light_eq_sum_band]
  unfold RowSlope
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun b _ => band_increment hlo hhi (hf b) (hc b))

theorem row_affine {r : Row} {hlen : r.bands.length=7} {D N : ℕ}
    {terms : CrossBandCredit208.Band → Finset Term} (hlo : r.low ≤ N) (hhi : N ≤ r.high)
    (hf : ∀ b, BandFacts r.high D (At r hlen b) (terms b))
    (hc : ∀ b, ∀ t ∈ terms b, Certificate t.p (r.low/(t.q*(t.q+1))) t.count) :
    RowLight r hlen D N+RowSlope r hlen terms*(r.high-N) ≤ RowLight r hlen D r.high := by
  have hk : ∀ k, N+k ≤ r.high →
      RowLight r hlen D N+RowSlope r hlen terms*k ≤ RowLight r hlen D (N+k) := by
    intro k
    induction k with
    | zero => intro h; simp
    | succ k ih =>
        intro h
        have hp := ih (by omega)
        have hs := row_increment (by omega : r.low ≤ N+k) (by omega : N+k ≤ r.high) hf hc
        have he : N+k.succ = (N+k)+1 := by omega
        rw [he, Nat.mul_succ]
        nlinarith only [hp, hs]
  have h := hk (r.high-N) (by omega)
  simpa only [Nat.add_sub_of_le hhi] using h

theorem row_light_bound {r : Row} {hlen : r.bands.length=7} {D N : ℕ} {out : Totals}
    {terms : CrossBandCredit208.Band → Finset Term} (hlo : r.low ≤ N) (hhi : N ≤ r.high)
    (hf : ∀ b, BandFacts r.high D (At r hlen b) (terms b))
    (hc : ∀ b, ∀ t ∈ terms b, Certificate t.p (r.low/(t.q*(t.q+1))) t.count)
    (hchecked : ChunkFacts r 1 D out) :
    RowLight r hlen D N+RowSlope r hlen terms*(r.high-N) ≤ out.light := by
  simpa only [high_light_total hchecked] using row_affine hlo hhi hf hc

#print axioms shape_block
#print axioms band_cost_mono
#print axioms selected_subset
#print axioms selected_card_lower
#print axioms selected_increment
#print axioms band_increment
#print axioms row_light_eq_sum_band
#print axioms row_increment
#print axioms row_affine
#print axioms row_light_bound
end
end JSP233.LightSlope158375
