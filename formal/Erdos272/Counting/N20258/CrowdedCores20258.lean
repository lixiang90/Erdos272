module

public import Erdos272.Counting.N20258.TwoTransversals20258
public import Erdos272.Resources.MaximumCore208

@[expose] public section
namespace JSP233.CrowdedCores20258
open StarCompletion PrivatePairExistence NearAP36 SourceBridge208
open scoped Classical BigOperators
set_option autoImplicit false

private def trimmed (a d len h : ℕ) :=
  (Finset.Ico (h-1) len).image (fun i : ℕ => (a:ℤ)+(i:ℤ)*d)

private theorem trim_size {a d len h : ℕ} (pos : 0<d) :
    (trimmed a d len h).card=len-(h-1) := by
  rw [trimmed,Finset.card_image_of_injOn,Nat.card_Ico]
  intro i _ j _ eq
  have hd : (d:ℤ)≠0 := by exact_mod_cast pos.ne'
  have ij : (i:ℤ)*d=(j:ℤ)*d := add_left_cancel eq
  exact_mod_cast mul_right_cancel₀ hd ij

private theorem before {a d len h i : ℕ} {x : ℤ} (hx : x∈trimmed a d len h) (hi : i<h) :
    x-(i:ℤ)*d∈Grid a d len := by
  obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp hx
  obtain ⟨base,stop⟩ := Finset.mem_Ico.mp hj
  apply (mem_grid ..).mpr
  refine ⟨j-i,by omega,?_⟩
  rw [Nat.cast_sub (by omega : i≤j),←eq]
  ring

private theorem overlap {a b d len size h : ℕ} {x : ℤ} (pos : 0<d)
    (first : x∈trimmed a d len h) (second : x∈trimmed b d size h) :
    h≤(Grid a d len∩Grid b d size).card := by
  let f (i : ℕ) := x-(i:ℤ)*d
  have maps (i : ℕ) (hi : i∈Finset.range h) : f i∈Grid a d len∩Grid b d size :=
    Finset.mem_inter.mpr ⟨before first (Finset.mem_range.mp hi),before second (Finset.mem_range.mp hi)⟩
  have inj : Set.InjOn f (Finset.range h : Set ℕ) := by
    intro i _ j _ eq
    have hd : (d:ℤ)≠0 := by exact_mod_cast pos.ne'
    have ij : (i:ℤ)*d=(j:ℤ)*d := by dsimp only [f] at eq; omega
    exact_mod_cast mul_right_cancel₀ hd ij
  simpa using Finset.card_le_card_of_injOn f maps inj

/-- Above a population level, two short members cannot have a medium
intersection. After deleting h-1 initial core sites the cores of a fixed
stride are disjoint, regardless of the positions of their exterior sites. -/
theorem actual {N m v L a b h : ℕ} {F G : Finset (Finset ℤ)}
    (legal : Legal (Ground N) F) (sub : G⊆F) (ground : 2≤N) (room : m+1≤N)
    (omits : ∀ x∈Ground N,∃ S∈CrookedMembers F,x∉S ∧ S.card≤m)
    (many : L*(N-2)<(CrookedMembers F).card) (short : ∀ S∈G,S.card≤v)
    (small : 1≤h) (fits : h≤a) (two : 2≤a)
    (core : ∀ S∈G,a≤MaxAPSize S ∧ MaxAPSize S≤b)
    (blocked : ∀ i : ℕ, (h ≤ i) → (i ≤ b) → i*m+(v-i)*(v-i)≤L) :
    G.card≤((N-1)/(a-1))*(N/(a+1-h)) := by
  classical
  have forbidden (S : Finset ℤ) (hs : S∈G) (T : Finset ℤ) (ht : T∈G) (ne : S≠T) :
      (S∩T).card<h := by
    by_contra! large
    have law := legal.2 S (sub hs) T (sub ht) ne
    have upper := (AP_card_le_max law Finset.inter_subset_left).trans (core S hs).2
    have disS := Finset.card_sdiff_add_card_inter S T
    have disT := Finset.card_sdiff_add_card_inter T S
    rw [Finset.inter_comm T S] at disT
    have ss := short S hs
    have ts := short T ht
    have pair := Nat.mul_le_mul (show (S\T).card≤v-(S∩T).card by omega)
      (show (T\S).card≤v-(S∩T).card by omega)
    have meet := isAP_nonempty law
    have cap := TwoTransversals20258.actual_two ground room legal (sub hs) (meet.mono Finset.inter_subset_left)
      (sub ht) (meet.mono Finset.inter_subset_right) omits
    have cut := blocked _ large upper
    have cpay := Nat.mul_le_mul_left (S∩T).card (Nat.sub_le (m*(N-2)) (m.choose 2))
    apply (not_le_of_gt many)
    calc
      _ ≤ _ := cap
      _ ≤ (S∩T).card*(m*(N-2))+((v-(S∩T).card)*(v-(S∩T).card))*(N-2) :=
        Nat.add_le_add cpay (Nat.mul_le_mul_right (N-2) pair)
      _ = ((S∩T).card*m+(v-(S∩T).card)*(v-(S∩T).card))*(N-2) := by ring
      _ ≤ L*(N-2) := Nat.mul_le_mul_right _ cut
  have chooseGrid (S : Finset ℤ) : ∃ start d : ℕ,S∈G →
      0<d ∧ Grid start d (MaxAPSize S)⊆S := by
    by_cases hs : S∈G
    · obtain ⟨start,d,hd,inc,_⟩ := MaximumCore208.actual_maximum_core
        (two.trans ((core S hs).1.trans (maxAPSize_le_card S))) (legal.1 S (sub hs))
      exact ⟨start,d,fun _ => ⟨hd,inc⟩⟩
    · exact ⟨0,0,fun h => False.elim (hs h)⟩
  choose start step data using chooseGrid
  let D := Finset.Icc 1 ((N-1)/(a-1))
  have maps (S : Finset ℤ) (hs : S∈G) : step S∈D := by
    obtain ⟨hd,inc⟩ := data S hs
    let j := a-1
    have member (i : ℕ) (lt : i<MaxAPSize S) :
        (start S:ℤ)+(i:ℤ)*(step S:ℤ)∈Ground N :=
      legal.1 S (sub hs) (inc ((mem_grid ..).mpr ⟨i,lt,rfl⟩))
    have len := (core S hs).1
    have left := (mem_ground _ _).mp (member 0 (by omega))
    have right := (mem_ground _ _).mp (member j (by dsimp only [j]; omega))
    have prod : j*step S≤N-1 := by
      have inequality : (j:ℤ)*step S≤(N:ℤ)-1 := by simp only [Nat.cast_zero,zero_mul,add_zero] at left; omega
      exact_mod_cast (show (j:ℤ)*step S≤((N-1:ℕ):ℤ) by rw [Nat.cast_sub (by omega : 1≤N)]; exact inequality)
    exact Finset.mem_Icc.mpr ⟨hd,(Nat.le_div_iff_mul_le (by omega : 0<a-1)).mpr (by simpa only [j,Nat.mul_comm] using prod)⟩
  rw [Finset.card_eq_sum_card_fiberwise maps]
  have per (d : ℕ) (hd : d∈D) : (G.filter (fun S => step S=d)).card≤N/(a+1-h) := by
    let A := G.filter (fun S => step S=d)
    let pieces (S : Finset ℤ) := trimmed (start S) d (MaxAPSize S) h
    have pos := (Finset.mem_Icc.mp hd).1
    have inc (S : Finset ℤ) (hs : S∈A) : Grid (start S) d (MaxAPSize S)⊆S := by
      obtain ⟨mem,eq⟩ := Finset.mem_filter.mp hs
      rw [←eq]; exact (data S mem).2
    have dis : (A : Set (Finset ℤ)).PairwiseDisjoint pieces := by
      intro S hs T ht ne
      apply Finset.disjoint_left.mpr
      intro x xs xt
      have bad := overlap (a:=start S) (b:=start T) pos xs xt
      have inST := Finset.card_le_card (Finset.inter_subset_inter (inc S hs) (inc T ht))
      exact (not_le_of_gt (forbidden S (Finset.mem_filter.mp hs).1 T (Finset.mem_filter.mp ht).1 ne)) (bad.trans inST)
    have included : A.biUnion pieces⊆Ground N := by
      intro x hx
      obtain ⟨S,hs,xs⟩ := Finset.mem_biUnion.mp hx
      have mark := before xs (by omega : 0<h)
      simp only [Nat.cast_zero,zero_mul,sub_zero] at mark
      exact legal.1 S (sub (Finset.mem_filter.mp hs).1) (inc S hs mark)
    apply (Nat.le_div_iff_mul_le (by omega : 0<a+1-h)).mpr
    calc
      _ = ∑ _S∈A,(a+1-h) := by simp only [Finset.sum_const,smul_eq_mul,A]
      _ ≤ ∑ S∈A,(pieces S).card := Finset.sum_le_sum (fun S hs => by
        rw [show (pieces S).card=MaxAPSize S-(h-1) from trim_size pos]
        have := (core S (Finset.mem_filter.mp hs).1).1; omega)
      _ = (A.biUnion pieces).card := (Finset.card_biUnion dis).symm
      _ ≤ N := (Finset.card_le_card included).trans_eq (ground_card N)
  simpa only [Finset.sum_const,smul_eq_mul,D,Nat.card_Icc,Nat.add_sub_cancel] using Finset.sum_le_sum per

#print axioms actual
end JSP233.CrowdedCores20258
