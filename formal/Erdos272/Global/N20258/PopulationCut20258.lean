module

public import Erdos272.Global.N20258.ConcentratedCut20258

@[expose] public section
namespace JSP233.PopulationCut20258
open StarCompletion PrivatePairExistence APClasses88404 IntrinsicTriples208 PaddedSource20258
open FirstSparseCut20258 SparseSmall39 Density41 ResidueCapacity20258 ConcentratedCut20258
open scoped Classical BigOperators
set_option autoImplicit false

def total (b : Block) (U head fee : ℕ) :=
  (1+tail b)*b.price+fee+head*(b.upperCut*(b.hi-2))+(b.price-head)*(U*(b.hi-2))

/-- A population lower bound can lengthen every nontrivial progression;
the upper bound pays only the difference of the two triple prices. -/
def Valid (b : Block) (L U minimum head fee : ℕ) : Prop :=
  161≤b.lo ∧ b.lo≤b.hi ∧ b.hi<2^16 ∧ 2≤b.lowerCut ∧
  (b.length=1 ∨ 5000*((b.upperCut-1)*b.length+17)≤443*b.lo ∨ (b.upperCut-1)*b.length+1≤L) ∧
  minimum≤max b.lowerCut (b.length+1) ∧ 0<b.price ∧ head≤b.price ∧
  b.hi-1≤2*b.price ∧ 387679*b.price≤138655*(3*(b.lo-1))+99000 ∧
  (total b U head fee:ℚ)≤PriceChord20258.allowance ((b.lo-1:ℕ):ℚ) (b.price:ℚ) ∧
  (total b U head fee:ℚ)≤PriceChord20258.allowance ((b.hi-1:ℕ):ℚ) (b.price:ℚ)

instance (b : Block) (L U s h v : ℕ) : Decidable (Valid b L U s h v) := by unfold Valid; infer_instance

theorem upper {N m s h v L U : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ} {b : Block}
    (lo : b.lo≤N) (hi : N≤b.hi) (lcut : b.lowerCut≤m) (ucut : m≤b.upperCut)
    (legal : Legal (Ground N) F) (cut : Cut N F m c T) (valid : Valid b L U s h v)
    (many : L*(N-2)<(CrookedMembers F).card) (few : (CrookedMembers F).card≤U*(N-2))
    (source : ∀ A : Finset (Finset ℤ), A⊆CrookedMembers F → (∀ S∈A,s≤S.card) →
      h*A.card≤(∑ S∈A,(Pool S).card)+v) : F.card≤B N := by
  classical
  by_contra! counter
  obtain ⟨ground,range,cap,two,length,minima,xpos,covered,span,bend,left,right⟩ := valid
  have sparse := cut.sparse
  let H := CrookedMembers F
  let A := H.filter (fun S => c∉S)
  have hsub : H⊆F := Finset.filter_subset _ _
  have asub : A⊆H := Finset.filter_subset _ _
  have padded : Legal (Ground b.hi) F := by
    refine ⟨fun S hs y hy => ?_,legal.2⟩
    obtain ⟨l,u⟩ := (mem_ground N y).mp (legal.1 S hs hy)
    exact (mem_ground b.hi y).mpr ⟨l,u.trans (by exact_mod_cast hi)⟩
  have long {S : Finset ℤ} (hs : S∈F) (size : 2≤S.card) : b.length<S.card := by
    by_contra! short
    have product := Nat.mul_le_mul (Nat.sub_le_sub_right ucut 1) short
    rcases length with first|harmonic|dense
    · omega
    · have due := (Nat.mul_le_mul_left 5000 (Nat.add_le_add_right product 17)).trans
        (harmonic.trans (Nat.mul_le_mul_left 443 lo))
      exact (not_lt_of_ge (FortyFourFamily20258.of_member (by omega) (by omega) legal hs cut.crooked due)) counter
    · have limited := TwoTransversals20258.actual_member (by omega : 2≤N) (by omega : m+1≤N)
        legal hs (Finset.card_pos.mp (by omega)) cut.crooked
      exact (not_le_of_gt many) (limited.trans (Nat.mul_le_mul_right _ ((Nat.add_le_add_right product 1).trans dense)))
  have sizeA (S : Finset ℤ) (hs : S∈A) : s≤S.card := by
    obtain ⟨mem,miss⟩ := Finset.mem_filter.mp hs
    obtain ⟨inside,bad⟩ := Finset.mem_filter.mp mem
    have sc : m≤S.card := by
      by_cases sp : 12*S.card≤N
      · exact cut.minimum S (actual_sparse_membership.mpr ⟨inside,bad,sp⟩) miss
      · omega
    have spanS := long inside (by omega)
    omega
  have pay := source A asub sizeA
  have mass : (∑ S∈A,(Pool S).card)≤∑ S∈F,(Pool S).card :=
    Finset.sum_le_sum_of_subset_of_nonneg (asub.trans hsub) (fun _ _ _ => Nat.zero_le _)
  have countN : H.card≤U*(b.hi-2) := few.trans (Nat.mul_le_mul_left U (Nat.sub_le_sub_right hi 2))
  have degree := MixedOmitter20258.actual_degree legal (actual_sparse_membership.mp cut.omitter).1 cut.misses
  rw [cut.size] at degree
  have standard := degreeBudget_closed N m (by omega) (by omega)
  have rooted : (RootPart H c).card≤b.upperCut*(b.hi-2) := degree.trans
    (((Nat.le_add_right _ _).trans standard.le).trans (Nat.mul_le_mul ucut (Nat.sub_le_sub_right hi 2)))
  have parts : (RootPart H c).card+A.card=H.card := Finset.card_filter_add_card_filter_not (s:=H) _
  have expense : b.price*H.card≤(∑ S∈F,(Pool S).card)+v+h*(b.upperCut*(b.hi-2))+
      (b.price-h)*(U*(b.hi-2)) := by
    have mix : b.price*H.card=h*(RootPart H c).card+h*A.card+(b.price-h)*H.card := by
      rw [←Nat.mul_add,parts,←Nat.add_mul,Nat.add_sub_of_le covered]
    rw [mix]
    have base := pay.trans (Nat.add_le_add_right mass v)
    have paidRoot := Nat.mul_le_mul_left h rooted
    have paidCount := Nat.mul_le_mul_left (b.price-h) countN
    omega
  have width := ResidueJoint20258.steps_in_ground (by omega : 62≤b.hi)
  have aps := ProgressionPartition20258.actual_AP_partition (by omega : 1≤b.hi) padded steps width
    (fun d _ S hs => long (subset F d hs) (card_two hs))
  have teq : tail b=ProgressionPartition20258.offTail (b.hi-1) b.length steps :=
    StrideQuotients20258.compact_tail_eq (by omega) width
  rw [←teq] at aps
  have apR : ((F.filter IsAP).card:ℝ)≤1+(∑ d∈steps,((StepAP F d).card:ℝ))+(tail b:ℝ) := by exact_mod_cast aps
  have split : ((F.filter IsAP).card:ℝ)+(H.card:ℝ)=F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s:=F) IsAP
  let x : ℝ := b.price
  have xp : 0<x := by dsimp only [x]; exact_mod_cast xpos
  have spanN : ((N-1:ℕ):ℝ)≤2*x := by dsimp only [x]; exact_mod_cast (show N-1≤2*b.price by omega)
  have joint := VariablePrice20258.actual (by omega : 62≤N) xp spanN legal
  have cast_end (t : ℕ) (e : (total b U h v:ℚ)≤PriceChord20258.allowance (t:ℚ) (b.price:ℚ)) :
      (total b U h v:ℝ)≤PriceChord20258.allowance (t:ℝ) x := by
    have z := (Rat.cast_le (K:=ℝ)).mpr e
    unfold PriceChord20258.allowance PriceChord20258.target VariablePrice20258.bound at z ⊢
    push_cast at z; exact z
  have mid := PriceChord20258.between (by exact_mod_cast Nat.sub_le_sub_right lo 1 :
      ((b.lo-1:ℕ):ℝ)≤((N-1:ℕ):ℝ)) (by exact_mod_cast Nat.sub_le_sub_right hi 1 :
      ((N-1:ℕ):ℝ)≤((b.hi-1:ℕ):ℝ)) (x:=x) (K:=(total b U h v:ℝ)) (by
    dsimp only [x]
    exact_mod_cast (show 387679*b.price≤138655*((b.lo-1)+(N-1)+(b.hi-1))+99000 by omega))
    (cast_end _ left) (cast_end _ right)
  have target := mul_le_mul_of_nonneg_right (PriceChord20258.target_le (show 1≤N by omega)) xp.le
  have bill : x*(H.card:ℝ)≤(∑ S∈F,((Pool S).card:ℝ))+v+(h:ℝ)*(b.upperCut*((b.hi-2:ℕ):ℝ))+
      (x-h)*(U*((b.hi-2:ℕ):ℝ)) := by dsimp only [x]; exact_mod_cast expense
  have scaled := mul_le_mul_of_nonneg_right apR xp.le
  have sum := congrArg (fun a : ℝ => a*x) split
  unfold PriceChord20258.allowance total at mid
  push_cast [Nat.cast_sub covered] at mid
  have final : (F.card:ℝ)*x≤(B N:ℝ)*x := by
    dsimp only [x] at *
    nlinarith only [mid,joint,bill,scaled,sum,target]
  exact (not_lt_of_ge (by exact_mod_cast le_of_mul_le_mul_right final xp : F.card≤B N)) counter

#print axioms upper
end JSP233.PopulationCut20258
