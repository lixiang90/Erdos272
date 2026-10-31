import Erdos272.Core.FarAssembly37
import Mathlib.Data.Nat.Choose.Cast

/-! Actual witness-graph incidence and the 71q/7 candidate geometry. -/
namespace JSP233.GraphDegree51
open StarCompletion LongTerminal35 TraceWitnessCodes36 FarCore37 FarAssembly37 Reflect37
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 3000000

def InternalPairs (S M : Finset ℤ) (c : ℤ) : Finset (Finset ℤ) :=
  (StructuralPairs c S).filter (fun Q=>Q⊆M)

theorem actual_neighbor_incidence (S M : Finset ℤ) (c : ℤ) :
    (∑p∈M,(WitnessNeighbors S c p).card)≤
      ∑Q∈StructuralPairs c S,(Q∩M).card := by
  let A := M.sigma (WitnessNeighbors S c)
  let B := (StructuralPairs c S).sigma (fun Q=>Q∩M)
  let f : (Σ _:ℤ,ℤ)→(Σ _:Finset ℤ,ℤ) := fun q=>⟨{q.1,q.2},q.1⟩
  have hs : ∀q∈A,IntrinsicPair c S {q.1,q.2} := by
    intro q hq
    exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hq).2).2
  have hmaps : Set.MapsTo f (A:Set (Σ _:ℤ,ℤ)) (B:Set (Σ _:Finset ℤ,ℤ)) := by
    intro q hq
    exact Finset.mem_sigma.mpr ⟨structural_pair_mem.mpr (hs q hq),
      Finset.mem_inter.mpr ⟨by simp [f],(Finset.mem_sigma.mp hq).1⟩⟩
  have hinj : Set.InjOn f (A:Set (Σ _:ℤ,ℤ)) := by
    rintro ⟨p,x⟩ hx ⟨q,y⟩ hy heq
    have hpq : p=q := congrArg (fun z:(Σ _:Finset ℤ,ℤ)=>z.2) heq
    subst q
    have hpairs : ({p,x}:Finset ℤ)={p,y} := congrArg Sigma.fst heq
    have hpx : p≠x := by
      intro hh
      have hcard := (hs ⟨p,x⟩ hx).1
      simp [hh] at hcard
    have hxmem : x∈({p,y}:Finset ℤ) := by rw [←hpairs];simp
    have hxy : x=y := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hxmem
      exact hxmem.resolve_left hpx.symm
    subst y
    rfl
  simpa only [A,B,Finset.card_sigma] using Finset.card_le_card_of_injOn f hmaps hinj

theorem actual_internal_pairs_count (S M : Finset ℤ) (c : ℤ) :
    (InternalPairs S M c).card≤M.card.choose 2 := by
  have hs : InternalPairs S M c⊆M.powersetCard 2 := by
    intro Q hQ
    obtain ⟨hQW,hQM⟩ := Finset.mem_filter.mp hQ
    exact Finset.mem_powersetCard.mpr ⟨hQM,(structural_pair_mem.mp hQW).1⟩
  simpa only [Finset.card_powersetCard] using Finset.card_le_card hs

theorem actual_refined_neighbors_sum (S M : Finset ℤ) (c : ℤ) :
    (∑p∈M,(WitnessNeighbors S c p).card)≤(StructuralPairs c S).card+M.card.choose 2 := by
  have hpair : ∀Q∈StructuralPairs c S,(Q∩M).card≤1+if Q⊆M then 1 else 0 := by
    intro Q hQ
    have hcard := (structural_pair_mem.mp hQ).1
    by_cases hQM : Q⊆M
    · rw [if_pos hQM]
      have hh := Finset.card_le_card (Finset.inter_subset_left (s₁:=Q) (s₂:=M))
      omega
    · rw [if_neg hQM]
      by_contra hn
      have hh : Q∩M=Q := Finset.eq_of_subset_of_card_le
        (Finset.inter_subset_left) (by omega)
      exact hQM (by rw [←hh];exact Finset.inter_subset_right)
  have hsum := Finset.sum_le_sum hpair
  have hsecond : (∑Q∈StructuralPairs c S,if Q⊆M then 1 else 0)=(InternalPairs S M c).card := by
    rw [Finset.sum_boole]
    rfl
  rw [Finset.sum_add_distrib,hsecond] at hsum
  have hconst : (∑_Q∈StructuralPairs c S,(1:ℕ))=(StructuralPairs c S).card := by simp
  rw [hconst] at hsum
  exact (actual_neighbor_incidence S M c).trans (hsum.trans
    (Nat.add_le_add_left (actual_internal_pairs_count S M c) _))

theorem actual_high_neighbor_sum {S M : Finset ℤ} {c : ℤ} {q : ℕ}
    (hhigh : ∀p∈M,q<(WitnessNeighbors S c p).card) :
    M.card*(q+1)≤(StructuralPairs c S).card+M.card.choose 2 := by
  have hsum := Finset.sum_le_sum (fun p hp=>Nat.succ_le_iff.mpr (hhigh p hp))
  have hlo : M.card*(q+1)≤∑p∈M,(WitnessNeighbors S c p).card := by simpa using hsum
  exact hlo.trans (actual_refined_neighbors_sum S M c)

theorem actual_fourteen_high_numerator {S M : Finset ℤ} {c : ℤ} {q : ℕ}
    (hcard : 14*M.card=q) (hhigh : ∀p∈M,q<(WitnessNeighbors S c p).card) :
    27*q^2+42*q≤392*(StructuralPairs c S).card := by
  have hh := actual_high_neighbor_sum hhigh
  have hr : (M.card:ℝ)*((q:ℝ)+1)≤(StructuralPairs c S).card+(M.card.choose 2:ℝ) := by
    exact_mod_cast hh
  have hm : (M.card:ℝ)=(q:ℝ)/14 := by
    have he : 14*(M.card:ℝ)=(q:ℝ) := by exact_mod_cast hcard
    linarith only [he]
  rw [Nat.cast_choose_two ℝ,hm] at hr
  have hresult : 27*(q:ℝ)^2+42*q≤392*(StructuralPairs c S).card := by nlinarith only [hr]
  exact_mod_cast hresult

theorem actual_fourteen_high_bound {S M : Finset ℤ} {c : ℤ} {q : ℕ}
    (hcard : 14*M.card=q) (hhigh : ∀p∈M,q<(WitnessNeighbors S c p).card) :
    (q:ℝ)^2≤(392/27:ℝ)*(StructuralPairs c S).card := by
  have hh : 27*(q:ℝ)^2+42*q≤392*(StructuralPairs c S).card := by
    exact_mod_cast actual_fourteen_high_numerator hcard hhigh
  nlinarith only [hh,Nat.cast_nonneg (α:=ℝ) q]

theorem actual_fourteen_middle_block {T : Finset ℤ} {k : ℕ} (hcard : 71*k≤T.card) :
    ∃M:Finset ℤ,M⊆T ∧ M.card=k ∧ ∀p∈M,
      28*k≤(T.filter (fun x=>x≤p)).card ∧ 42*k≤(T.filter (fun x=>p≤x)).card := by
  let f := T.orderEmbOfFin rfl
  let mid : Fin k→ℤ := fun i=>f ⟨28*k+i.val,by omega⟩
  have hinj : Function.Injective mid := by
    intro i j hij
    have hv := congrArg Fin.val (f.injective hij)
    apply Fin.ext
    change 28*k+i.val=28*k+j.val at hv
    omega
  refine ⟨Finset.univ.image mid,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact T.orderEmbOfFin_mem rfl _
  · rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    constructor
    · let lo : Fin (28*k)→ℤ := fun j=>f ⟨j.val,by omega⟩
      have hlo : Function.Injective lo := by
        intro a b hab
        have hh := congrArg Fin.val (f.injective hab)
        apply Fin.ext
        change a.val=b.val at hh
        exact hh
      have hmaps : Set.MapsTo lo ((Finset.univ:Finset (Fin (28*k))):Set (Fin (28*k))) (T.filter (fun x=>x≤mid i):Set ℤ) := by
        intro j _
        refine Finset.mem_filter.mpr ⟨T.orderEmbOfFin_mem rfl _,?_⟩
        apply f.monotone
        change j.val≤28*k+i.val
        omega
      simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card_of_injOn lo hmaps hlo.injOn
    · let hi : Fin (42*k)→ℤ := fun j=>f ⟨29*k+j.val,by omega⟩
      have hhi : Function.Injective hi := by
        intro a b hab
        have hh := congrArg Fin.val (f.injective hab)
        apply Fin.ext
        change 29*k+a.val=29*k+b.val at hh
        omega
      have hmaps : Set.MapsTo hi ((Finset.univ:Finset (Fin (42*k))):Set (Fin (42*k))) (T.filter (fun x=>mid i≤x):Set ℤ) := by
        intro j _
        refine Finset.mem_filter.mpr ⟨T.orderEmbOfFin_mem rfl _,?_⟩
        apply f.monotone
        change 28*k+i.val≤29*k+j.val
        omega
      simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card_of_injOn hi hmaps hhi.injOn

theorem actual_fourteen_right_dichotomy {S : Finset ℤ} {c : ℤ} {k : ℕ}
    (hright : 71*k≤(S.filter (fun z=>c<z)).card) :
    (27*(14*k)^2+42*(14*k)≤392*(StructuralPairs c S).card) ∨
      ∃p∈S,c<p ∧ 28*k≤(S∩Finset.Icc c p).card ∧
        42*k≤(S.filter (fun z=>p≤z)).card ∧ (WitnessNeighbors S c p).card≤14*k := by
  obtain ⟨M,hMT,hMcard,hmiddle⟩ := actual_fourteen_middle_block hright
  by_cases hex : ∃p∈M,(WitnessNeighbors S c p).card≤14*k
  · obtain ⟨p,hpM,hdegree⟩ := hex
    obtain ⟨hpS,hcp⟩ := Finset.mem_filter.mp (hMT hpM)
    have hhead : 28*k≤(S∩Finset.Icc c p).card := (hmiddle p hpM).1.trans
      (Finset.card_le_card (by
        intro z hz
        obtain ⟨hzT,hzp⟩ := Finset.mem_filter.mp hz
        obtain ⟨hzS,hcz⟩ := Finset.mem_filter.mp hzT
        exact Finset.mem_inter.mpr ⟨hzS,Finset.mem_Icc.mpr ⟨hcz.le,hzp⟩⟩))
    have htail : 42*k≤(S.filter (fun z=>p≤z)).card := (hmiddle p hpM).2.trans
      (Finset.card_le_card (by
        intro z hz
        obtain ⟨hzT,hpz⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzT).1,hpz⟩))
    exact Or.inr ⟨p,hpS,hcp,hhead,htail,hdegree⟩
  · exact Or.inl (actual_fourteen_high_numerator (by rw [hMcard])
      (fun p hp=>by by_contra hn;exact hex ⟨p,hp,by omega⟩))

theorem actual_fourteen_member_dichotomy {S : Finset ℤ} {c : ℤ} {k : ℕ}
    (hc : c∈S) (hsize : 142*k+1≤S.card) :
    (27*(14*k)^2+42*(14*k)≤392*(StructuralPairs c S).card) ∨
      ∃T:Finset ℤ,∃r:ℤ,((T=S ∧ r=c) ∨ (T=Reflect S ∧ r= -c)) ∧
        ∃p∈T,r<p ∧ 28*k≤(T∩Finset.Icc r p).card ∧
          42*k≤(T.filter (fun z=>p≤z)).card ∧ (WitnessNeighbors T r p).card≤14*k := by
  by_cases hright : 71*k≤(S.filter (fun z=>c<z)).card
  · rcases actual_fourteen_right_dichotomy hright with hh|hlow
    · exact Or.inl hh
    · exact Or.inr ⟨S,c,Or.inl ⟨rfl,rfl⟩,hlow⟩
  · have hleft : 71*k≤(S.filter (fun z=>z<c)).card := by
      have hh := actual_side_card_partition hc
      omega
    have hright' : 71*k≤((Reflect S).filter (fun z=> -c<z)).card := by
      simpa only [reflect_right_card] using hleft
    rcases actual_fourteen_right_dichotomy hright' with hh|hlow
    · exact Or.inl (by simpa only [structural_reflect_card] using hh)
    · exact Or.inr ⟨Reflect S,-c,Or.inr ⟨rfl,rfl⟩,hlow⟩

theorem actual_low_candidate_remainder {S H : Finset ℤ} {p : ℤ} {k : ℕ}
    (htail : 42*k≤(S.filter (fun z=>p≤z)).card) (hH : H.card≤28*k) :
    14*k≤((S.filter (fun z=>p≤z))\H).card := by
  have hh := Finset.card_sdiff_add_card_inter (S.filter (fun z=>p≤z)) H
  have hi := Finset.card_le_card (Finset.inter_subset_right (s₁:=S.filter (fun z=>p≤z)) (s₂:=H))
  omega

#print axioms actual_neighbor_incidence
#print axioms actual_internal_pairs_count
#print axioms actual_refined_neighbors_sum
#print axioms actual_high_neighbor_sum
#print axioms actual_fourteen_high_numerator
#print axioms actual_fourteen_high_bound
#print axioms actual_fourteen_middle_block
#print axioms actual_fourteen_right_dichotomy
#print axioms actual_fourteen_member_dichotomy
#print axioms actual_low_candidate_remainder
end
end JSP233.GraphDegree51
