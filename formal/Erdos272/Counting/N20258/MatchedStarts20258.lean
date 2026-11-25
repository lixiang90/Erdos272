module

public import Erdos272.Counting.N20258.TwoTransversals20258
public import Erdos272.Counting.N20258.ProgressionTail20258

@[expose] public section
namespace JSP233.MatchedStarts20258
open StarCompletion PrivatePairExistence APCount41 AffineLine30 APClasses88404 APClassFrame88404
open ProgressionLengths20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- Among the first two blocks of j starts, each matched pair leaves one hole. -/
theorem window (Z : Finset ℤ) (a : ℤ) (W j : ℕ) (width : 2*j ≤ W)
    (inBox : Z ⊆ Finset.Ico a (a+(W : ℤ)))
    (gap : ∀ b ∈ Z, b+(j : ℤ) ∉ Z) : Z.card+j ≤ W := by
  let hole (i : ℕ) : ℤ := if a+(i : ℤ) ∈ Z then a+i+j else a+i
  have facts (i : ℕ) (hi : i ∈ Finset.range j) :
      hole i ∈ Finset.Ico a (a+(W : ℤ)) \ Z ∧
        (hole i = a+i ∨ hole i = a+i+j) := by
    have small := Finset.mem_range.mp hi
    by_cases h : a+(i : ℤ) ∈ Z
    · have notin := gap _ h
      simp only [hole, ite_eq_left h, Finset.mem_sdiff, Finset.mem_Ico]
      exact ⟨⟨⟨by omega,by omega⟩,notin⟩,Or.inr trivial⟩
    · simp only [hole, ite_eq_right h, Finset.mem_sdiff, Finset.mem_Ico]
      exact ⟨⟨⟨by omega,by omega⟩,h⟩,Or.inl trivial⟩
  have inj : Set.InjOn hole (↑(Finset.range j)) := by
    intro i hi k hk eqn
    have hi' := Finset.mem_range.mp hi
    have hk' := Finset.mem_range.mp hk
    rcases (facts i hi).2 with h|h <;> rcases (facts k hk).2 with h'|h' <;> omega
  have count := Finset.card_le_card_of_injOn hole (fun i hi => (facts i hi).1) inj
  rw [Finset.card_range,Finset.card_sdiff_of_subset inBox,Int.card_Ico] at count
  have sub := Finset.card_le_card inBox
  rw [Int.card_Ico] at sub
  omega

private theorem written {V : Finset ℤ} {z : ℤ} {t : ℕ} (hz : z ∈ V)
    (hi : ∃ a b : ℤ, V = Finset.Icc a b) (ht : V.card=t) :
    V = Finset.Icc (Low V) (Low V+(t : ℤ)-1) := by
  obtain ⟨a,b,rfl⟩ := hi
  have hab := (Finset.mem_Icc.mp hz).1.trans (Finset.mem_Icc.mp hz).2
  have spec := low_spec (show (Finset.Icc a b).Nonempty from ⟨z,hz⟩)
  have low : Low (Finset.Icc a b)=a :=
    le_antisymm (spec.2 a (Finset.mem_Icc.mpr ⟨le_rfl,hab⟩)) (Finset.mem_Icc.mp spec.1).1
  have size := Int.card_Icc_of_le (a := a) (b := b) (by omega)
  rw [ht] at size
  rw [low,show a+(t : ℤ)-1=b by omega]

/-- On a real stride of the original family, two t-term starts j apart
would bound the entire crooked family by ((t-j)m+j²)(N-2). -/
theorem actual_layer {N m t d j L : ℕ} {F G : Finset (Finset ℤ)}
    (hN : 2 ≤ N) (hm : m+1 ≤ N) (hd : 0 < d) (hj : 0 < j) (jt : 2*j ≤ t)
    (wide : t+2*j ≤ (N-1)/d+2) (fits : (t-j)*m+j*j ≤ L)
    (legal : Legal (Ground N) F) (sub : G ⊆ CrookedMembers F) (many : L*(N-2) < G.card)
    (omits : ∀ x ∈ Ground N, ∃ Q ∈ CrookedMembers F, x ∉ Q ∧ Q.card ≤ m) :
    ((StepAP F d).filter (fun S => S.card=t)).card+j ≤ starts ((N-1)/d) t := by
  obtain ⟨f⟩ := frame_nonempty (by omega : 1 ≤ N) hd legal
  have dz : (0 : ℤ) < d := by exact_mod_cast hd
  let V := f.family.filter fun S => S.card=t
  let Z := V.image Low
  have mem (S : Finset ℤ) (hS : S ∈ V) := (Finset.mem_filter.mp hS).1
  have sz (S : Finset ℤ) (hS : S ∈ V) := (Finset.mem_filter.mp hS).2
  have repr (S : Finset ℤ) (hS : S ∈ V) :=
    written (f.common_root S (mem S hS)) (f.intervals S (mem S hS)) (sz S hS)
  have orig (S : Finset ℤ) (hS : S ∈ f.family) : mapSet f.offset (d : ℤ) S ∈ StepAP F d := by
    exact (Finset.ext_iff.mp f.mapped _).mp (Finset.mem_image.mpr ⟨S,hS,rfl⟩)
  have eqV : mapFamily f.offset (d : ℤ) V = (StepAP F d).filter (fun S => S.card=t) := by
    ext P
    constructor
    · intro h
      obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨orig S (mem S hS),(mapSet_card _ _ dz S).trans (sz S hS)⟩
    · intro h
      obtain ⟨hP,card⟩ := Finset.mem_filter.mp h
      rw [←f.mapped] at hP
      obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hP
      exact Finset.mem_image.mpr ⟨S,Finset.mem_filter.mpr ⟨hS,(mapSet_card _ _ dz S).symm.trans card⟩,rfl⟩
  have zcard : Z.card=V.card := by
    apply Finset.card_image_of_injOn
    intro S hS T hT eqn
    exact (repr S hS).trans ((by rw [eqn] : Finset.Icc (Low S) (Low S+(t : ℤ)-1) =
      Finset.Icc (Low T) (Low T+(t : ℤ)-1)).trans (repr T hT).symm)
  have avoid (b : ℤ) (hb : b ∈ Z) (hit : b+(j : ℤ) ∈ Z) : False := by
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨T,hT,shift⟩ := Finset.mem_image.mp hit
    have inter : S ∩ T = Finset.Icc (Low T) (Low S+(t : ℤ)-1) := by
      ext x
      simp only [Finset.mem_inter]
      have s := Finset.ext_iff.mp (repr S hS) x
      have u := Finset.ext_iff.mp (repr T hT) x
      rw [s,u]
      simp only [Finset.mem_Icc]
      omega
    have bs := orig S (mem S hS)
    have bt := orig T (mem T hT)
    let P := mapSet f.offset (d : ℤ) S
    let Q := mapSet f.offset (d : ℤ) T
    have pc : P.card=t := (mapSet_card _ _ dz S).trans (sz S hS)
    have qc : Q.card=t := (mapSet_card _ _ dz T).trans (sz T hT)
    have ic : (P ∩ Q).card=t-j := by
      have e : P ∩ Q = mapSet f.offset (d : ℤ) (S ∩ T) :=
        (Finset.image_inter S T (affine_injective _ _ dz)).symm
      rw [e,mapSet_card _ _ dz,inter,Int.card_Icc]
      omega
    have u := Finset.card_sdiff_add_card_inter P Q
    have v := Finset.card_sdiff_add_card_inter Q P
    rw [Finset.inter_comm Q P] at v
    have bp : (P \ Q).card=j := by omega
    have bq : (Q \ P).card=j := by omega
    have h := TwoTransversals20258.actual_two hN hm legal (APClasses88404.subset F d bs)
      (Finset.card_pos.mp (by omega : 0<P.card)) (APClasses88404.subset F d bt)
      (Finset.card_pos.mp (by omega : 0<Q.card)) omits
    rw [ic,bp,bq] at h
    have coarse := Nat.mul_le_mul_left (t-j) (Nat.sub_le (m*(N-2)) (m.choose 2))
    have lim := Nat.mul_le_mul_right (N-2) fits
    rw [Nat.add_mul] at lim
    have H := Finset.card_le_card sub
    simp only [Nat.mul_assoc] at coarse lim h
    omega
  have span : f.size-1 ≤ (N-1)/d := by
    apply (Nat.le_div_iff_mul_le hd).mpr
    have hR : (((f.size-1)*d : ℕ) : ℝ) ≤ ((N-1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub f.size_positive,Nat.cast_sub (by omega : 1 ≤ N)]
      linarith only [f.span,mul_comm (d : ℝ) ((f.size : ℝ)-1)]
    exact_mod_cast hR
  have bounds (b : ℤ) (h : b ∈ Z) : 1 ≤ b ∧ b ≤ f.root ∧ f.root ≤ b+(t : ℤ)-1 ∧
      b+(t : ℤ)-1 ≤ f.size := by
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp h
    have hr := f.common_root S (mem S hS)
    have root := Finset.mem_Icc.mp ((Finset.ext_iff.mp (repr S hS) f.root).mp hr)
    have G := f.ground S (mem S hS)
    have le := (mem_ground f.size _).mp (G (low_spec ⟨f.root,hr⟩).1)
    have endp := (mem_ground f.size _).mp (G ((Finset.ext_iff.mp (repr S hS) _).mpr
      (Finset.mem_Icc.mpr ⟨root.1.trans root.2,le_rfl⟩)))
    exact ⟨le.1,root.1,root.2,endp.2⟩
  have one := window Z (f.root-(t : ℤ)+1) t j jt (by
    intro b hb
    have := bounds b hb
    apply Finset.mem_Ico.mpr
    omega) avoid
  have two := window Z 1 ((N-1)/d+2-t) j (by omega) (by
    intro b hb
    have := bounds b hb
    have := f.size_positive
    apply Finset.mem_Ico.mpr
    omega) avoid
  rw [←eqV,mapFamily_card _ _ dz,←zcard]
  exact le_min one two

#print axioms actual_layer
end
end JSP233.MatchedStarts20258
