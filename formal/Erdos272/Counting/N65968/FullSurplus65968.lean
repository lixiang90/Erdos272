module

public import Erdos272.Counting.N80470.WitnessClosed80470
public import Erdos272.Counting.N80470.WitnessWindows80470

@[expose] public section

-- Generic finite sums for the next increment; separate from the actual family.
namespace JSP233.FullSurplus65968
open LightClosed208 WitnessClosed80470
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Surplus (q T E B V W : ℕ) : ℕ :=
  CappedSum q T E B V-CappedSum q T E B (min V W)

theorem term_difference (z V W : ℕ) :
    min V z-W=min V z-min (min V W) z := by
  omega

theorem surplus_sum {q T E B V W : ℕ} (hB : 0<B) :
    (∑ k∈Finset.range (Count q (T-E) B), (min V (q-k*B+E)-W))=
      Surplus q T E B V W := by
  have hbound : ∀ k∈Finset.range (Count q (T-E) B),
      min (min V W) (q-k*B+E)≤min V (q-k*B+E) := by
    intro k _hk
    exact min_le_min_right _ (min_le_left _ _)
  rw [Finset.sum_congr rfl (fun k _hk => term_difference (q-k*B+E) V W),
    Finset.sum_tsub_distrib _ hbound,
    capped_weight_sum hB,capped_weight_sum hB]
  rfl

theorem weighted_hits {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (window : ι→Finset ℤ) (A₀ : Finset ℤ)
    (weight : ι→ℕ) {W cap : ℕ} (hW : A₀.card≤W)
    (hpoint : ∀ x∈A₀, (∑ i∈I.filter (fun i => x∈window i), weight i)≤cap) :
    (∑ i∈I, if ((window i)∩A₀).Nonempty then weight i else 0)≤W*cap := by
  have hsingle : ∀ i∈I,
      (if ((window i)∩A₀).Nonempty then weight i else 0)≤
        ∑ x∈A₀, if x∈window i then weight i else 0 := by
    intro i _hi
    by_cases hh : ((window i)∩A₀).Nonempty
    · rw [if_pos hh]
      obtain ⟨x,hx⟩ := hh
      obtain ⟨hxw,hxA⟩ := Finset.mem_inter.mp hx
      have hs := Finset.single_le_sum
        (s:=A₀) (f:=fun y => if y∈window i then weight i else 0)
        (by intros; exact Nat.zero_le _) hxA
      simpa only [if_pos hxw] using hs
    · simp only [if_neg hh]
      exact Nat.zero_le _
  calc
    _≤∑ i∈I, ∑ x∈A₀, if x∈window i then weight i else 0 :=
      Finset.sum_le_sum hsingle
    _=∑ x∈A₀, ∑ i∈I, if x∈window i then weight i else 0 := Finset.sum_comm
    _≤∑ _x∈A₀, cap := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [←Finset.sum_filter] using hpoint x hx
    _=A₀.card*cap := by simp [Nat.mul_comm]
    _≤W*cap := Nat.mul_le_mul_right _ hW

theorem point_surplus {N high d T E B V W : ℕ} {I : Finset (ℕ×ℕ)}
    (θ : (ℕ×ℕ)→ℕ) (hd : 0<d) (hB : 0<B)
    (hres : ∀ q∈I, q.1<d)
    (hfeasible : ∀ q∈I, T-E+q.2*B≤high/d)
    (hupper : ∀ q∈I, θ q≤min V (high/d-q.2*B+E)) (x : ℤ) :
    (∑ q∈I.filter (fun q => x∈ClippedWindows208.Window N d B V q), (θ q-W))≤
      Surplus (high/d) T E B V W := by
  let H := I.filter (fun q => x∈ClippedWindows208.Window N d B V q)
  have hHI : H⊆I := Finset.filter_subset _ _
  have hx : ∀ q∈H, x∈ClippedWindows208.Window N d B V q :=
    fun q hq => (Finset.mem_filter.mp hq).2
  have hinj : Set.InjOn Prod.snd (H : Set (ℕ×ℕ)) := by
    intro q hq r hr he
    exact ClippedWindows208.fixed_block_window_eq hd
      (hres q (hHI hq)) (hres r (hHI hr)) rfl he.symm
      ⟨x,Finset.mem_inter.mpr ⟨hx q hq,hx r hr⟩⟩
  have hmap : H.image Prod.snd⊆Finset.range (Count (high/d) (T-E) B) := by
    intro k hk
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr ((lt_count hB).mpr (hfeasible q (hHI hq)))
  calc
    _≤∑ q∈H, (min V (high/d-q.2*B+E)-W) :=
      Finset.sum_le_sum (fun q hq => Nat.sub_le_sub_right (hupper q (hHI hq)) W)
    _=∑ k∈H.image Prod.snd, (min V (high/d-k*B+E)-W) :=
      (Finset.sum_image
        (f:=fun k => min V (high/d-k*B+E)-W)
        (fun q hq r hr he => hinj hq hr he)).symm
    _≤∑ k∈Finset.range (Count (high/d) (T-E) B),
        (min V (high/d-k*B+E)-W) :=
      Finset.sum_le_sum_of_subset_of_nonneg hmap (by intros; exact Nat.zero_le _)
    _=Surplus (high/d) T E B V W := surplus_sum hB

theorem cost_sum_surplus {N high d T E B V W : ℕ}
    {I : Finset (ℕ×ℕ)} {A₀ : Finset ℤ} (θ : (ℕ×ℕ)→ℕ)
    (hd : 0<d) (hB : 0<B) (hW : A₀.card≤W)
    (hres : ∀ q∈I, q.1<d)
    (hfeasible : ∀ q∈I, T-E+q.2*B≤high/d)
    (hupper : ∀ q∈I, θ q≤min V (high/d-q.2*B+E)) :
    (∑ q∈I, WitnessCredit80470.Cost (θ q) W
        (((ClippedWindows208.Window N d B V q)∩A₀).Nonempty))≤
      (∑ q∈I, min (θ q) W)+W*Surplus (high/d) T E B V W := by
  have hh := weighted_hits I (ClippedWindows208.Window N d B V) A₀
    (fun q => θ q-W) hW (by
      intro x _hx
      exact point_surplus θ hd hB hres hfeasible hupper x)
  have heq : (∑ q∈I, WitnessCredit80470.Cost (θ q) W
      (((ClippedWindows208.Window N d B V q)∩A₀).Nonempty))=
      (∑ q∈I, min (θ q) W)+
        (∑ q∈I, if (((ClippedWindows208.Window N d B V q)∩A₀).Nonempty)
          then θ q-W else 0) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    by_cases hit : (((ClippedWindows208.Window N d B V q)∩A₀).Nonempty)
    · simp only [WitnessCredit80470.Cost,if_pos hit]
    · simp only [WitnessCredit80470.Cost,if_neg hit]
  rw [heq]
  exact Nat.add_le_add_left hh _

#print axioms term_difference
#print axioms surplus_sum
#print axioms weighted_hits
#print axioms point_surplus
#print axioms cost_sum_surplus
end
end JSP233.FullSurplus65968
