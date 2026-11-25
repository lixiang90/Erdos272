module

public import Erdos272.Geometry.AffineLine30
public import Mathlib.Data.Int.Interval

@[expose] public section
namespace JSP233.ExteriorPrefix20258
open StarCompletion APGeometry AffineLine30
open scoped Classical
noncomputable section
set_option autoImplicit false

/-- An oriented core with endpoints `c,c+m`, with a single point before it. -/
def shape (m c t : ℤ) : Finset ℤ := insert (c-t) (Finset.Icc c (c+m))

private theorem mem_shape {m c t z : ℤ} :
    z ∈ shape m c t ↔ z=c-t ∨ c≤z ∧ z≤c+m := by simp [shape]

/-- Two consecutive common core points force the intersection to be an interval.
The later exterior point would leave a hole just before its own core. -/
theorem outside_separate {m c e t u : ℤ} (ord : c≤e) (overlap : e+1≤c+m)
    (gap : 2≤u) (ap : IsAP (shape m c t ∩ shape m e u)) : e-u ∉ shape m c t := by
  intro inside
  let I := shape m c t ∩ shape m e u
  have first : e∈I := Finset.mem_inter.mpr
    ⟨mem_shape.mpr (Or.inr ⟨ord,by omega⟩),mem_shape.mpr (Or.inr ⟨le_rfl,by omega⟩)⟩
  have next : e+1∈I := Finset.mem_inter.mpr
    ⟨mem_shape.mpr (Or.inr ⟨by omega,overlap⟩),mem_shape.mpr (Or.inr ⟨by omega,by omega⟩)⟩
  have outer : e-u∈I := Finset.mem_inter.mpr ⟨inside,mem_shape.mpr (Or.inl rfl)⟩
  obtain ⟨d,p,frame,_⟩ := (isAP_iff_exists_APAt I).mp ap
  have divides : d ∣ 1 := by simpa using apAt_dvd_sub frame first next
  have pos := frame.1
  have unit : d=1 := by have := Int.le_of_dvd (by decide : (0:ℤ)<1) divides; omega
  have missing : e-1∈I := apAt_fill frame outer first (by omega) (by omega) (by rw [unit]; exact one_dvd _)
  have left := mem_shape.mp (Finset.mem_inter.mp missing).2
  omega

private theorem block {α : Type*} {D : Finset α} {m : ℤ} {T : ℕ}
    {c t : α → ℤ} (gaps : ∀ i∈D, 2≤t i ∧ t i≤T)
    (width : ∀ i∈D, ∀ j∈D, c j+1≤c i+m)
    (ap : ∀ i∈D, ∀ j∈D, i≠j → IsAP (shape m (c i) (t i) ∩ shape m (c j) (t j))) :
    D.card≤T := by
  classical
  by_cases ne : D.Nonempty
  · obtain ⟨a,ha,least⟩ := Finset.exists_min_image D c ne
    let out (i : α) := c i-t i
    have maps (i : α) (hi : i∈D) : out i∈Finset.Icc (c a-T) (c a-1) := by
      have lo := least i hi
      have gap := gaps i hi
      have close := width a ha i hi
      apply Finset.mem_Icc.mpr
      dsimp only [out]
      refine ⟨by omega,?_⟩
      by_cases eqn : a=i
      · subst i; omega
      · have h := outside_separate lo close gap.1 (ap a ha i hi eqn)
        by_contra! no
        exact h (mem_shape.mpr (Or.inr ⟨by omega,by omega⟩))
    have diff (i : α) (hi : i∈D) (j : α) (hj : j∈D) (ord : c i≤c j) (neq : i≠j) :
        out i ≠ out j := by
      intro eqn
      exact outside_separate ord (width i hi j hj) (gaps j hj).1 (ap i hi j hj neq)
        (mem_shape.mpr (Or.inl eqn.symm))
    have count := Finset.card_le_card_of_injOn out maps (fun i hi j hj eqn => by
      by_contra neq
      rcases le_total (c i) (c j) with h|h
      · exact diff i hi j hj h neq eqn
      · exact diff j hj i hi h (Ne.symm neq) eqn.symm)
    rw [Int.card_Icc] at count
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp ne]

/-- The two blocks of core starts leave a possible extra slot only at full gap. -/
def oneSide (m T : ℕ) := if T<2 then 0 else 2*T + if T=m then 1 else 0

/-- Count a finite collection in one oriented, normalized residue class.
The labels may be actual family members with any one of their representations chosen. -/
theorem normalized {α : Type*} {D : Finset α} {m T : ℕ} {c t : α → ℤ}
    (top : T≤m) (gaps : ∀ i∈D, 2≤t i ∧ t i≤T)
    (ap : ∀ i∈D, ∀ j∈D, i≠j → IsAP (shape m (c i) (t i) ∩ shape m (c j) (t j))) :
    D.card≤oneSide m T := by
  classical
  by_cases ne : D.Nonempty
  · obtain ⟨a,ha,least⟩ := Finset.exists_min_image D c ne
    have two : 2≤T := by have := gaps a ha; omega
    have reach (i : α) (hi : i∈D) : c i≤c a+(m:ℤ)+t i := by
      have gt := gaps i hi
      by_cases same : a=i
      · subst i; omega
      · obtain ⟨z,hz⟩ := isAP_nonempty (ap a ha i hi same)
        have l := mem_shape.mp (Finset.mem_inter.mp hz).1
        have r := mem_shape.mp (Finset.mem_inter.mp hz).2
        have ga := gaps a ha
        omega
    let A := D.filter fun i => c i<c a+(m:ℤ)
    let R := D.filter fun i => ¬c i<c a+(m:ℤ)
    let B := R.filter fun i => c i<c a+2*(m:ℤ)
    let E := R.filter fun i => ¬c i<c a+2*(m:ℤ)
    have part₁ : A.card+R.card=D.card := Finset.card_filter_add_card_filter_not _
    have part₂ : B.card+E.card=R.card := Finset.card_filter_add_card_filter_not _
    have small (I : Finset α) (sub : I⊆D) (w : ∀ i∈I, ∀ j∈I, c j+1≤c i+(m:ℤ)) :
        I.card≤T := block (fun i hi => gaps i (sub hi)) w
          (fun i hi j hj => ap i (sub hi) j (sub hj))
    have lenA := small A (Finset.filter_subset _ _) (by
      intro i hi j hj
      have low := least i (Finset.mem_filter.mp hi).1
      have high := (Finset.mem_filter.mp hj).2
      omega)
    have lenB := small B ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)) (by
      intro i hi j hj
      have low := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
      have high := (Finset.mem_filter.mp hj).2
      omega)
    have extreme (i : α) (hi : i∈E) : i∈D ∧ c i=c a+2*(m:ℤ) ∧ t i=m ∧ T=m := by
      have inD := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
      have low := (Finset.mem_filter.mp hi).2
      have high := reach i inD
      have gt := gaps i inD
      exact ⟨inD,by omega,by omega,by omega⟩
    have lenE : E.card ≤ (if T=m then 1 else 0) := by
      split_ifs with eqn
      · apply Finset.card_le_one.mpr
        intro i hi j hj
        obtain ⟨ih,ic,it,_⟩ := extreme i hi
        obtain ⟨jh,jc,jt,_⟩ := extreme j hj
        by_contra neq
        have gap := gaps j jh
        have sep := outside_separate (by omega : c i≤c j)
          (by omega : c j+1≤c i+(m:ℤ)) gap.1 (ap i ih j jh neq)
        exact sep (mem_shape.mpr (Or.inl (by omega)))
      · have empty : E=∅ := Finset.eq_empty_iff_forall_notMem.mpr
          (fun i hi => eqn (extreme i hi).2.2.2)
        simp [empty]
    unfold oneSide
    rw [if_neg (by omega : ¬T<2)]
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp ne]

#print axioms normalized
end
end JSP233.ExteriorPrefix20258
