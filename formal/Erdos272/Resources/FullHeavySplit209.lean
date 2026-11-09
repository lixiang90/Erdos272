module

public import Erdos272.Counting.HeavyCredit208
public import Erdos272.Resources.CleanupWindowBounds208
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.FullHeavySplit209
open StarCompletion APGeometry NearAP36
open BandSystem208 LightClosed208 WindowCounts208 RightWindows208 ClippedWindows208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 200000

def Full {ι : Type*} [DecidableEq ι] (F : Finset (Finset ℤ))
    (label : Finset ℤ→ι) (I : Finset ι) (V : ℕ) : Finset ι :=
  I.filter fun i=>V<(F.filter fun S=>label S=i).card

def Middle {ι : Type*} [DecidableEq ι] (F : Finset (Finset ℤ))
    (label : Finset ℤ→ι) (I : Finset ι) (V : ℕ) (W : ι→ℕ) : Finset ι :=
  I.filter fun i=>W i<(F.filter fun S=>label S=i).card ∧ (F.filter fun S=>label S=i).card≤V

/-- The truncated light price is preserved. Only middle fibers between the
truncated cap and V pay an additional linear correction. -/
theorem actual_credit_split {ι : Type*} [DecidableEq ι] {F : Finset (Finset ℤ)}
    (label : Finset ℤ→ι) (I : Finset ι) (W : ι→ℕ) (T V : ℕ)
    (hmap : ∀S∈F,label S∈I) (hW : ∀i∈I,W i≤V)
    (hT : ∀i∈I,V<(F.filter fun S=>label S=i).card→T≤W i) :
    F.card+T*(Full F label I V).card≤
      (∑i∈I,W i)+(∑i∈Middle F label I V W,(V-W i))+
        (F.filter fun S=>label S∈Full F label I V).card := by
  let H:=Full F label I V
  let R:=Middle F label I V W
  let W' : ι→ℕ := fun i=>W i+(if i∈R then V-W i else 0)
  have hh:=HeavyCredit208.actual_light_credit label I H W' (fun _=>T) hmap
    (by
      intro i hi hnot
      have hn : (F.filter fun S=>label S=i).card≤V := by
        by_contra h
        exact hnot (Finset.mem_filter.mpr ⟨hi,by omega⟩)
      by_cases hsmall : (F.filter fun S=>label S=i).card≤W i
      · exact hsmall.trans (Nat.le_add_right _ _)
      · have hr : i∈R := Finset.mem_filter.mpr ⟨hi,by omega,hn⟩
        dsimp only [W']
        rw [if_pos hr]
        have hw:=hW i hi
        omega)
    (by
      intro i hi hfull
      have hs:=(Finset.mem_filter.mp hfull).2
      exact (hT i hi hs).trans (Nat.le_add_right _ _))
  have hIF : I.filter (fun i=>i∈H)=H := by
    ext i
    simp only [H,Full,Finset.mem_filter]
    tauto
  have hIR : I.filter (fun i=>i∈R)=R := by
    ext i
    simp only [R,Middle,Finset.mem_filter]
    tauto
  have ht : (∑i∈I,if i∈H then T else 0)=T*H.card := by
    rw [←Finset.sum_filter,hIF]
    simp [Nat.mul_comm]
  have hr : (∑i∈I,if i∈R then V-W i else 0)=∑i∈R,(V-W i) := by
    rw [←Finset.sum_filter,hIR]
  simp only [W',Finset.sum_add_distrib,ht,hr] at hh
  exact hh

theorem middle_extra {ι : Type*} [DecidableEq ι] (R : Finset ι) (W : ι→ℕ) {T V : ℕ}
    (hT : ∀i∈R,T≤W i) : (∑i∈R,(V-W i))≤R.card*(V-T) := by
  calc
    _≤∑_i∈R,(V-T) := Finset.sum_le_sum (fun i hi=>Nat.sub_le_sub_left (hT i hi) V)
    _=_ := by simp

/-- The real right-middle labels inherit the injective code map, and the
entire right transition contains at most Count(V-E-1,A,B) blocks. -/
theorem right_middle_count {N d A B V E : ℕ} {H R : Finset (ℕ×ℕ)}
    (hp : Properties N d A B V E H) (hB : 0<B) (hEV : E<V) (hRH : R⊆H)
    (hright : ∀q∈R,¬V-E+q.2*B≤N/d) :
    R.card≤Count (V-E-1) A B := by
  by_cases hAq : A≤N/d
  · have hindex : ∀q∈R,q.2∈Finset.Icc (RightLeft (N/d) (V-E-1) B) ((N/d-A)/B) := by
      intro q hq
      apply Finset.mem_Icc.mpr
      apply (right_index_iff hB hAq).mp
      have hf:=hp.feasible q (hRH hq)
      have hr:=hright q hq
      exact ⟨hf,by omega⟩
    have hc:=code_census (fun q hq t ht he=>hp.injective (hRH hq) (hRH ht) he) hindex
    have he : (N/d-A)/B+1-RightLeft (N/d) (V-E-1) B=rightIndexCount (N/d) A (V-E-1) B := by
      simp only [rightIndexCount,Count,if_pos hAq]
    rw [he] at hc
    exact hc.trans (rightCount_le_period hB)
  · have he : H=∅ := HeavyMenu208.actual_extinction hp.feasible (by omega : N/d<A)
    have hr : R=∅ := Finset.eq_empty_iff_forall_notMem.mpr (by intro q hq;simpa only [he,Finset.notMem_empty] using hRH hq)
    simp only [hr,Finset.card_empty,Nat.zero_le]

/-- A full-heavy family really has pairwise clipped windows, unlike the
larger family defined by a varying truncated threshold. -/
theorem actual_full_geometry {N d B V : ℕ} {H : Finset (ℕ×ℕ)}
    (hd : 0<d) (hB : 0<B) (hV : 0<V)
    (family : (ℕ×ℕ)→Finset (Finset ℤ)) (core : Finset ℤ→Finset ℤ)
    (hres : ∀q∈H,q.1<d)
    (hcore : ∀q∈H,∀S∈family q,core S⊆Window N d B V q)
    (hdis : ∀q∈H,∀S∈family q,∀T∈family q,S≠T→Disjoint (S\core S) (T\core T))
    (hcross : ∀q∈H,∀t∈H,∀S∈family q,∀T∈family t,(S∩T).Nonempty)
    (hsmall : ∀q∈H,∀S∈family q,S.card≤V)
    (hheavy : ∀q∈H,V<(family q).card) :
    H.card≤(V-1)/B+1 ∧
      (H.biUnion (Window N d B V)).card≤min (V+(V-1)/B*B) (N/d+1) := by
  have hpair : ∀q∈H,∀t∈H,(Window N d B V q∩Window N d B V t).Nonempty := by
    intro q hq t ht
    have hw : (Window N d B V q).card≤V := (actual_clipped_card hd q).trans (min_le_left _ _)
    exact heavy_core_pools_intersect core (hcore q hq) (hcore t ht) (hdis q hq) (hdis t ht)
      (hcross q hq t ht) (hsmall t ht) (hheavy q hq) (hw.trans_lt (hheavy t ht))
  have hu:=OrdinaryUnion208.actual_union_window_bound hd hB hV hres hpair
  have hcount:=OrdinaryTruncate208.actual_block_census hd hB hV hres
    (R := (H.sup Prod.snd)) (fun q hq=>Finset.le_sup hq) hpair
  exact ⟨hcount.trans (min_le_left _ _),hu⟩

#print axioms actual_credit_split
#print axioms middle_extra
#print axioms right_middle_count
#print axioms actual_full_geometry
end
end JSP233.FullHeavySplit209
