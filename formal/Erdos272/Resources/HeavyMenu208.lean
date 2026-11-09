module

public import Erdos272.Resources.BandGeometry208

@[expose] public section

namespace JSP233.HeavyMenu208
open StarCompletion APGeometry NearAP36 ClippedWindows208 OrdinaryTruncate208 RightWindows208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def OrdinaryCount (q B V K : ℕ) : ℕ :=
  if K ≤ q then min ((V-1)/B+1) ((q-K)/B+1) else 0

def OrdinaryUnion (q B V K : ℕ) : ℕ :=
  if K ≤ q then min (V+min ((V-1)/B) ((q-K)/B)*B) (q+1) else 0

theorem actual_extinction {H : Finset (ℕ × ℕ)} {A B q : ℕ}
    (hsource : ∀ c ∈ H, A+c.2*B ≤ q) (hsmall : q < A) : H=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  have := hsource c hc
  omega

theorem actual_ordinary {N d B V K : ℕ} {H : Finset (ℕ × ℕ)}
    (hd : 0 < d) (hB : 0 < B) (hV : 0 < V)
    (hres : ∀ c ∈ H, c.1 < d)
    (hord : ∀ c ∈ H, K+c.2*B ≤ N/d)
    (hpair : ∀ c ∈ H, ∀ t ∈ H,
      (Window N d B V c ∩ Window N d B V t).Nonempty) :
    H.card ≤ OrdinaryCount (N/d) B V K ∧
      (H.biUnion (Window N d B V)).card ≤ OrdinaryUnion (N/d) B V K := by
  by_cases hk : K ≤ N/d
  · have hblock : ∀ c ∈ H, c.2 ≤ (N/d-K)/B := by
      intro c hc
      apply (Nat.le_div_iff_mul_le hB).mpr
      have := hord c hc
      omega
    exact ⟨by simpa only [OrdinaryCount,if_pos hk] using actual_block_census hd hB hV hres hblock hpair,
      by simpa only [OrdinaryUnion,if_pos hk] using actual_union_truncate hd hB hV hres hblock hpair⟩
  · have he : H=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      have := hord c hc
      omega
    subst H
    simp [OrdinaryCount,OrdinaryUnion,hk]

theorem actual_menu {N d A B V E : ℕ} {H : Finset (ℕ × ℕ)}
    (hd : 0 < d) (hB : 0 < B) (hV : 0 < V) (hEV : E < V)
    (hAq : A ≤ N/d) (hres : ∀ c ∈ H, c.1 < d)
    (hsource : ∀ c ∈ H, A+c.2*B ≤ N/d)
    (hinj : Set.InjOn Prod.snd (H : Set (ℕ × ℕ)))
    (hpair : ∀ c ∈ H, V-E+c.2*B ≤ N/d → ∀ t ∈ H, V-E+t.2*B ≤ N/d →
      (Window N d B V c ∩ Window N d B V t).Nonempty) :
    let lo := (N/d-(V-E-1)+B-1)/B
    let hi := (N/d-A)/B
    H.card ≤ OrdinaryCount (N/d) B V (V-E)+(hi+1-lo) ∧
      (H.biUnion (Window N d B V)).card ≤
        OrdinaryUnion (N/d) B V (V-E)+
          ∑ r ∈ Finset.Icc lo hi, min V (N/d-r*B+1) := by
  dsimp only
  let O := H.filter (fun c => V-E+c.2*B ≤ N/d)
  let R := H.filter (fun c => ¬ V-E+c.2*B ≤ N/d)
  have hOH : O ⊆ H := Finset.filter_subset _ _
  have hRH : R ⊆ H := Finset.filter_subset _ _
  have ho := actual_ordinary hd hB hV (fun c hc => hres c (hOH hc))
    (fun c hc => (Finset.mem_filter.mp hc).2)
    (fun c hc t ht => hpair c (hOH hc) (Finset.mem_filter.mp hc).2
      t (hOH ht) (Finset.mem_filter.mp ht).2)
  have hrange : ∀ c ∈ R, c.2 ∈ Finset.Icc
      ((N/d-(V-E-1)+B-1)/B) ((N/d-A)/B) := by
    intro c hc
    have hs := hsource c (hRH hc)
    have hn := (Finset.mem_filter.mp hc).2
    have hb : N/d ≤ V-E-1+c.2*B := by omega
    exact Finset.mem_Icc.mpr ((right_index_iff hB hAq).mp ⟨hs,hb⟩)
  have hinjR : Set.InjOn Prod.snd (R : Set (ℕ × ℕ)) :=
    fun c hc t ht he => hinj (hRH hc) (hRH ht) he
  have hr := code_census hinjR hrange
  have hru := actual_right_union (N := N) (B := B) (V := V) (E := 1) hd (by decide) hinjR hrange
  have hcard : O.card+R.card=H.card :=
    Finset.card_filter_add_card_filter_not (s := H) (fun c => V-E+c.2*B ≤ N/d)
  have hsplit : H=O∪R := by
    ext c
    simp only [O,R,Finset.mem_union,Finset.mem_filter]
    tauto
  have hu : (H.biUnion (Window N d B V)).card ≤
      (O.biUnion (Window N d B V)).card+(R.biUnion (Window N d B V)).card := by
    rw [hsplit,Finset.union_biUnion]
    exact Finset.card_union_le _ _
  constructor <;> omega

#print axioms actual_extinction
#print axioms actual_ordinary
#print axioms actual_menu
end
end JSP233.HeavyMenu208
