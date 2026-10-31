import Erdos272.Resources.WindowRatio208

namespace JSP233.BandWindowRatio208
open StarCompletion ClippedWindows208 HeavyMenu208 WindowRatio208 CleanupNet208
open WindowCounts208 WindowSums208 RightWindows208 LightClosed208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 200000

def OrdinaryGrid (grid low high d B V K : ℕ) : ℕ :=
  let ordinary:=min ((V-1)/B+1) (Count (high/d) K B)
  let C:=V+(ordinary-1)*B
  if 0<ordinary then min (Ceil (min C low*grid) low) (Ceil grid d+Ceil grid low) else 0

def RightGrid (grid low high d A J B : ℕ) : ℕ :=
  min (Ceil (min (maximum_sum A J B (low/d) (high/d)) low*grid) low)
    (maximum A J B (low/d) (high/d)*(Ceil grid d+Ceil grid low))

theorem ordinary_ratio {N d B V K grid low high : ℕ} {H : Finset (ℕ×ℕ)}
    (hd : 0<d) (hB : 0<B) (hV : 0<V) (hgrid : 0<grid) (hlow : 0<low)
    (hlN : low≤N) (hNh : N≤high)
    (hres : ∀q∈H,q.1<d) (hord : ∀q∈H,K+q.2*B≤N/d)
    (hpair : ∀q∈H,∀t∈H,(Window N d B V q∩Window N d B V t).Nonempty) :
    ((H.biUnion (Window N d B V)).card : ℝ)/N≤(OrdinaryGrid grid low high d B V K : ℝ)/grid := by
  let c:=min ((V-1)/B+1) (Count (high/d) K B)
  let C:=V+(c-1)*B
  have ho := actual_ordinary hd hB hV hres hord hpair
  have hqh := Nat.div_le_div_right (c := d) hNh
  have hCount := count_mono (A := K) hB hqh
  have hoc : OrdinaryCount (N/d) B V K≤c := by
    by_cases hK : K≤N/d
    · rw [OrdinaryCount,if_pos hK]
      simpa only [c,Count,if_pos hK] using min_le_min_left ((V-1)/B+1) hCount
    · simp only [OrdinaryCount,if_neg hK,Nat.zero_le]
  by_cases hc : 0<c
  · have hw : (H.biUnion (Window N d B V)).card≤C ∧
        (H.biUnion (Window N d B V)).card≤N/d+1 := by
      by_cases hK : K≤N/d
      · have hu := ho.2
        rw [OrdinaryUnion,if_pos hK] at hu
        have hm : min ((V-1)/B) ((N/d-K)/B)+1≤c := by
          apply le_min
          · omega
          · have hh : min ((V-1)/B) ((N/d-K)/B)+1≤Count (N/d) K B := by
              rw [Count,if_pos hK]
              omega
            exact hh.trans hCount
        have hspan : V+min ((V-1)/B) ((N/d-K)/B)*B≤C := by
          have hh := Nat.mul_le_mul_right B (show min ((V-1)/B) ((N/d-K)/B)≤c-1 by omega)
          dsimp only [C]
          omega
        exact ⟨(hu.trans (min_le_left _ _)).trans hspan,hu.trans (min_le_right _ _)⟩
      · have hu := ho.2
        rw [OrdinaryUnion,if_neg hK] at hu
        exact ⟨hu.trans (Nat.zero_le C),hu.trans (Nat.zero_le (N/d+1))⟩
    have hcap := capped_ratio hlow hgrid hlN hw.1 (window_union_ground H)
    have hrecip : ((H.biUnion (Window N d B V)).card : ℝ)/N≤
        ((Ceil grid d+Ceil grid low : ℕ) : ℝ)/grid := by
      simpa only [Nat.cast_add,Nat.cast_one,one_mul] using
        (reciprocal_ratio (count := 1) hd hlow hgrid hlN (by simpa only [one_mul] using hw.2))
    have hh := min_ratio hcap hrecip
    change _≤((if 0<c then min (Ceil (min C low*grid) low) (Ceil grid d+Ceil grid low) else 0 : ℕ) : ℝ)/grid
    simpa only [if_pos hc] using hh
  · have hzero : H=∅ := Finset.card_eq_zero.mp (by have hh:=ho.1.trans hoc;omega)
    simp only [hzero,Finset.biUnion_empty,Finset.card_empty,Nat.cast_zero,zero_div]
    positivity

theorem right_ratio {N d A J B V grid low high : ℕ} {H : Finset (ℕ×ℕ)}
    (hd : 0<d) (hB : 0<B) (hgrid : 0<grid) (hlow : 0<low)
    (hlN : low≤N) (hNh : N≤high) (hAJ : A≤J) (hAq : A≤N/d)
    (hinj : Set.InjOn Prod.snd (H : Set (ℕ×ℕ)))
    (hindex : ∀q∈H,q.2∈Finset.Icc (RightLeft (N/d) J B) ((N/d-A)/B)) :
    ((H.biUnion (Window N d B V)).card : ℝ)/N≤(RightGrid grid low high d A J B : ℝ)/grid := by
  have hql := Nat.div_le_div_right (c := d) hlN
  have hqh := Nat.div_le_div_right (c := d) hNh
  have hu := actual_right_union (N := N) (B := B) (V := V) (E := 1) hd (by decide) hinj hindex
  have hs := actual_Icc_sum_bound (V := V) hB hAJ hAq hql hqh
  have htotal := hu.trans hs
  have hcount := code_census hinj hindex
  have he : (N/d-A)/B+1-RightLeft (N/d) J B=rightIndexCount (N/d) A J B := by
    simp only [rightIndexCount,Count,if_pos hAq]
  rw [he] at hcount
  have hnum := hcount.trans (maximum_bound hB hql hqh)
  have hmany := (window_union_count (N := N) (B := B) (V := V) hd H).trans
    (Nat.mul_le_mul_right (N/d+1) hnum)
  have hcap := capped_ratio hlow hgrid hlN htotal (window_union_ground H)
  have hrecip : ((H.biUnion (Window N d B V)).card : ℝ)/N≤
      ((maximum A J B (low/d) (high/d)*(Ceil grid d+Ceil grid low) : ℕ) : ℝ)/grid := by
    simpa only [Nat.cast_mul,Nat.cast_add] using reciprocal_ratio hd hlow hgrid hlN hmany
  exact min_ratio hcap hrecip

theorem actual_window_ratio {N d A B V E grid low high : ℕ} {H : Finset (ℕ×ℕ)}
    (hp : BandSystem208.Properties N d A B V E H)
    (hd : 0<d) (hB : 0<B) (hV : 0<V) (hEV : E<V) (hAJ : A≤V-E-1)
    (hgrid : 0<grid) (hlow : 0<low) (hlN : low≤N) (hNh : N≤high) :
    ((H.biUnion (Window N d B V)).card : ℝ)/N≤
      ((OrdinaryGrid grid low high d B V (V-E)+RightGrid grid low high d A (V-E-1) B : ℕ) : ℝ)/grid := by
  by_cases hAq : A≤N/d
  · let O:=H.filter fun q=>V-E+q.2*B≤N/d
    let R:=H.filter fun q=>¬V-E+q.2*B≤N/d
    have hOH : O⊆H := Finset.filter_subset _ _
    have hRH : R⊆H := Finset.filter_subset _ _
    have ho := ordinary_ratio hd hB hV hgrid hlow hlN hNh
      (fun q hq=>hp.residue q (hOH hq)) (fun q hq=>(Finset.mem_filter.mp hq).2)
      (fun q hq t ht=>hp.ordinary_pair q (hOH hq) (Finset.mem_filter.mp hq).2
        t (hOH ht) (Finset.mem_filter.mp ht).2)
    have hindex : ∀q∈R,q.2∈Finset.Icc (RightLeft (N/d) (V-E-1) B) ((N/d-A)/B) := by
      intro q hq
      have hs := hp.feasible q (hRH hq)
      have hn := (Finset.mem_filter.mp hq).2
      apply Finset.mem_Icc.mpr
      exact (right_index_iff hB hAq).mp ⟨hs,by omega⟩
    have hr := right_ratio (V := V) hd hB hgrid hlow hlN hNh hAJ hAq
      (fun q hq t ht he=>hp.injective (hRH hq) (hRH ht) he) hindex
    have hsplit : H=O∪R := by
      ext q
      simp only [O,R,Finset.mem_union,Finset.mem_filter]
      tauto
    have hcard : (H.biUnion (Window N d B V)).card≤
        (O.biUnion (Window N d B V)).card+(R.biUnion (Window N d B V)).card := by
      rw [hsplit,Finset.union_biUnion]
      exact Finset.card_union_le _ _
    have hcardR : ((H.biUnion (Window N d B V)).card : ℝ)≤
        (O.biUnion (Window N d B V)).card+(R.biUnion (Window N d B V)).card := by exact_mod_cast hcard
    have hN : (0 : ℝ)≤N := Nat.cast_nonneg _
    have hdivide := div_le_div_of_nonneg_right hcardR hN
    simp only [Nat.cast_add,add_div] at hdivide ⊢
    linarith only [ho,hr,hdivide]
  · have he : H=∅ := actual_extinction hp.feasible (by omega : N/d<A)
    simp only [he,Finset.biUnion_empty,Finset.card_empty,Nat.cast_zero,zero_div]
    positivity

#print axioms ordinary_ratio
#print axioms right_ratio
#print axioms actual_window_ratio
end
end JSP233.BandWindowRatio208
