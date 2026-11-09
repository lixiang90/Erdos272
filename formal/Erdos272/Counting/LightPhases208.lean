module

public import Erdos272.Counting.PotentialPhases208
public import Erdos272.Counting.HeavyCredit208

@[expose] public section

namespace JSP233.LightPhases208
open StarCompletion APGeometry NearAP36 ShiftedBlocks208 PotentialPhases208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Indices (N d A B : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N+1)).product (Finset.Icc 1 d)).filter
    (fun i => i.2+(A+i.1*B)*d ≤ N)

def Cap (N d E B V : ℕ) (r : ℕ) : ℕ := min V (N/d-r*B+E)

def Price (N d T E B V : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (N+1), min d (N-(T-E+r*B)*d)*Cap N d E B V r

def Label (a : Finset ℤ → ℕ) (d B : ℕ) (S : Finset ℤ) : ℕ × ℕ :=
  ((Code d B (a S)).2,(Code d B (a S)).1+1)

theorem index_sum (N d T E B V : ℕ) :
    (∑ i ∈ Indices N d (T-E) B,Cap N d E B V i.1)=Price N d T E B V := by
  rw [Indices,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r hr
  have hh : (∑ x ∈ Phases N d (T-E+r*B),Cap N d E B V r)=
      min d (N-(T-E+r*B)*d)*Cap N d E B V r := by
    rw [Finset.sum_const,potential_phase_count]
    simp
  simpa only [Phases,Finset.sum_filter] using hh

theorem actual_label {N d T E B : ℕ} {F : Finset (Finset ℤ)}
    (a m e : Finset ℤ → ℕ) (hd : 0<d) (hB : 0<B)
    (hsize : ∀ S ∈ F,T≤S.card) (hTE : E<T) (hoff : ∀ S ∈ F,e S<E)
    (hcard : ∀ S ∈ F,S.card=m S+e S)
    (hsub : ∀ S ∈ F,Grid (a S) d (m S) ⊆ S)
    (hground : ∀ S ∈ F,S ⊆ Ground N) :
    ∀ S ∈ F,Label a d B S ∈ Indices N d (T-E) B := by
  intro S hS
  have hm : T-E+1≤m S := by have :=hsize S hS;have :=hoff S hS;have :=hcard S hS;omega
  have hp := actual_code_phase hd hB hm (hsub S hS) (hground S hS)
  obtain ⟨hphase,hsum⟩ := Finset.mem_filter.mp hp
  have hprod : (T-E+(Code d B (a S)).2*B)*d≤N := by omega
  have hq := (Nat.le_div_iff_mul_le hd).mpr hprod
  have hb : (Code d B (a S)).2≤(Code d B (a S)).2*B := by
    nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hB)]
  have hn := Nat.div_le_self N d
  change ((Code d B (a S)).2,(Code d B (a S)).1+1) ∈ Indices N d (T-E) B
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),hphase⟩,hsum⟩

theorem actual_cap {N d T E B V : ℕ} {F : Finset (Finset ℤ)}
    (a m e : Finset ℤ → ℕ) (hd : 0<d) (hB : 0<B)
    (hsize : ∀ S ∈ F,T≤S.card) (hTE : E<T)
    (hoff : ∀ S ∈ F,e S<E) (hcard : ∀ S ∈ F,S.card=m S+e S)
    (hsub : ∀ S ∈ F,Grid (a S) d (m S) ⊆ S)
    (hground : ∀ S ∈ F,S ⊆ Ground N) (hupper : ∀ S ∈ F,S.card≤V) :
    ∀ S ∈ F,T≤Cap N d E B V (Label a d B S).1 := by
  intro S hS
  have hm : 0<m S := by have :=hsize S hS;have :=hoff S hS;have :=hcard S hS;omega
  have hh := actual_source_cap hd hB hm (hoff S hS) (hcard S hS) (hsub S hS) (hground S hS)
  exact le_min ((hsize S hS).trans (hupper S hS)) ((hsize S hS).trans hh)

def Heavy (N d T E B V : ℕ) (F : Finset (Finset ℤ)) (a : Finset ℤ → ℕ) : Finset (ℕ × ℕ) :=
  (Indices N d (T-E) B).filter (fun i => Cap N d E B V i.1 < (F.filter (fun S=>Label a d B S=i)).card)

theorem actual_light_credit {N d T E B V : ℕ} {F : Finset (Finset ℤ)}
    (a m e : Finset ℤ → ℕ) (hd : 0<d) (hB : 0<B)
    (hsize : ∀ S ∈ F,T≤S.card) (hTE : E<T)
    (hoff : ∀ S ∈ F,e S<E) (hcard : ∀ S ∈ F,S.card=m S+e S)
    (hsub : ∀ S ∈ F,Grid (a S) d (m S) ⊆ S)
    (hground : ∀ S ∈ F,S ⊆ Ground N) (hupper : ∀ S ∈ F,S.card≤V) :
    F.card+T*(Heavy N d T E B V F a).card ≤ Price N d T E B V+
      (F.filter (fun S=>Label a d B S∈Heavy N d T E B V F a)).card := by
  have hmap := actual_label a m e hd hB hsize hTE hoff hcard hsub hground
  have hcap := actual_cap a m e hd hB hsize hTE hoff hcard hsub hground hupper
  have hh := HeavyCredit208.actual_light_credit (Label a d B) (Indices N d (T-E) B)
    (Heavy N d T E B V F a) (fun i=>Cap N d E B V i.1) (fun _=>T) hmap
    (by
      intro i hi hnot
      have hnot' : ¬Cap N d E B V i.1 < (F.filter (fun S=>Label a d B S=i)).card := by
        intro h;exact hnot (Finset.mem_filter.mpr ⟨hi,h⟩)
      omega)
    (by
      intro i hi hheavy
      have hh := (Finset.mem_filter.mp hheavy).2
      obtain ⟨S,hS⟩ := Finset.card_pos.mp (by omega : 0<(F.filter (fun S=>Label a d B S=i)).card)
      obtain ⟨hSF,hSi⟩ := Finset.mem_filter.mp hS
      simpa only [hSi] using hcap S hSF)
  rw [index_sum] at hh
  have ht : (∑ i∈Indices N d (T-E) B,if i∈Heavy N d T E B V F a then T else 0)=
      T*(Heavy N d T E B V F a).card := by
    have he : (Indices N d (T-E) B).filter (fun i=>i∈Heavy N d T E B V F a)=
        Heavy N d T E B V F a := by
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun h=>h.2,fun h=>⟨(Finset.mem_filter.mp h).1,h⟩⟩
    rw [←Finset.sum_filter]
    rw [he]
    simp [Nat.mul_comm]
  rw [ht] at hh
  exact hh

#print axioms index_sum
#print axioms actual_label
#print axioms actual_light_credit
end
end JSP233.LightPhases208
