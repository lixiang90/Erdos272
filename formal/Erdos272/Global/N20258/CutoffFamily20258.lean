module

public import Erdos272.Global.N20258.CutoffMass20258
public import Erdos272.Global.N20258.FirstEmptyKernel20258
public import Erdos272.Global.N20258.SmallAnchor20258
public import Erdos272.Geometry.N20258.CutoffTranslation20258
public import Erdos272.Core.N67702.FixedAnchorSmall67702

@[expose] public section
namespace JSP233.CutoffFamily20258
open StarCompletion PrivatePairExistence SmallKernel112 SparseSmall39 AnchorCompletion38
open scoped Classical
noncomputable section
set_option autoImplicit false

/-- The cap uses the size of a real anchor and the first empty-kernel cutoff. -/
def fixedCap (N a m : ℕ) : ℝ :=
  (FixedSmallScalars82427.Coefficient (a-1) (m-1) : ℝ)*N-
    FixedSmallScalars82427.Credit (a-1) (m-1)

theorem fixed_cap {N m a : ℕ} {F : Finset (Finset ℤ)} (legal : Legal (Ground N) F)
    (hm : 2 ≤ m) (ha : a ≤ m) (size : 2*m+1 ≤ N) (room : m+1+(m-1)^2/4 ≤ N)
    (anchor : ∃ P ∈ CrookedMembers F, P.card ≤ a)
    (omits : ∀ x ∈ Ground N, ∃ T ∈ CrookedMembers F, x ∉ T ∧ T.card ≤ m) :
    ((CrookedMembers F).card : ℝ) ≤ fixedCap N a m := by
  let H := CrookedMembers F
  have sub : H ⊆ F := Finset.filter_subset _ _
  have hl : Legal (Ground N) H :=
    ⟨fun S hS => legal.1 S (sub hS),fun S hS T hT => legal.2 S (sub hS) T (sub hT)⟩
  obtain ⟨P,hP,pc⟩ := anchor
  apply FixedAnchorSmall67702.actual_fixed_anchor_small_credit hm ha size room hl
    (fun _ hS => (Finset.mem_filter.mp hS).2) ⟨P,Finset.mem_filter.mpr ⟨hP,pc⟩⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hground,all⟩ := Finset.mem_filter.mp hx
  obtain ⟨T,hT,miss,sz⟩ := omits x hground
  exact miss (all T (Finset.mem_filter.mpr ⟨hT,sz⟩))

/-- The minimum-size anchor, a root, and a size-m omitter all belong to
the original family. The same witnesses give the total and rooted caps. -/
theorem actual {N : ℕ} {F : Finset (Finset ℤ)} (lo : 20258 ≤ N) (hi : N ≤ 21000)
    (legal : Legal (Ground N) F) (counter : B N < F.card) :
    ∃ m : ℕ, 44 ≤ m ∧ m ≤ 196 ∧
      (∀ x ∈ Ground N, ∃ S ∈ CrookedMembers F, x ∉ S ∧ S.card ≤ m) ∧
      ∃ P ∈ CrookedMembers F, ∃ c ∈ Ground N, ∃ T ∈ CrookedMembers F,
        c ∉ T ∧ T.card=m ∧ P.card ≤ m ∧
        (∀ S ∈ CrookedMembers F, P.card ≤ S.card) ∧
        (∀ S ∈ CrookedMembers F, c ∉ S → m ≤ S.card) ∧
        ((CrookedMembers F).card : ℝ) ≤ fixedCap N P.card m ∧
        (RootPart (CrookedMembers F) c).card ≤ DegreeBudget N m ∧
        (P.card=m ∨ (P.card<m ∧ c∈P)) := by
  obtain ⟨m,_,top,omits,⟨c,hc,T,hT,miss,sz,all⟩,_⟩ := FirstEmptyKernel20258.actual lo hi legal counter
  have floor := SmallFortyOne20258.first_at_least_44 lo hi legal counter omits
  have ceiling := CutoffMass20258.below_197 (by omega : 20000 ≤ N) hi legal counter top hT miss sz
    (fun S hS hcS => le_of_not_gt (fun small => hcS (all S hS small)))
  obtain ⟨P,hP,minimal⟩ := Finset.exists_min_image (CrookedMembers F) Finset.card ⟨T,hT⟩
  have pm : P.card ≤ m := sz ▸ minimal T hT
  have sq := Nat.pow_le_pow_left (show m-1 ≤ 264 by omega) 2
  have room : m+1+(m-1)^2/4 ≤ N := by omega
  have cap := fixed_cap legal (by omega : 2 ≤ m) pm (by omega : 2*m+1 ≤ N) room ⟨P,hP,le_rfl⟩ omits
  have root := MixedOmitter20258.actual_degree legal (Finset.mem_filter.mp hT).1 miss
  rw [sz] at root
  refine ⟨m,floor,ceiling,omits,P,hP,c,hc,T,hT,miss,sz,pm,minimal,?_,cap,root,?_⟩
  · intro S hS no
    exact le_of_not_gt (fun small => no (all S hS small))
  · rcases eq_or_lt_of_le pm with eq | lt
    · exact Or.inl eq
    · exact Or.inr ⟨lt,all P hP lt⟩

#print axioms fixed_cap
#print axioms actual

/-- Choose the cutoff on the original ground once. These witnesses survive every
padding used by a paid source. The two smallest cutoff exits need no table. -/
theorem actual_padded {N : ℕ} {F : Finset (Finset ℤ)} (lo : 20258 ≤ N) (hi : N ≤ 21000)
    (legal : Legal (Ground N) F) (counter : B N < F.card) :
    ∃ m : ℕ, 44 ≤ m ∧ m ≤ 196 ∧ ∃ (P : Finset ℤ) (c : ℤ) (T : Finset ℤ),
      CutoffTranslation20258.Witnesses N F m P c T ∧
      ((CrookedMembers F).card : ℝ) ≤ fixedCap N P.card m ∧
      (RootPart (CrookedMembers F) c).card ≤ DegreeBudget N m ∧
      (P.card=m ∨ (P.card<m ∧ c∈P)) ∧
      (m ≤ 45 → ∀ S ∈ F, 43 ≤ S.card) ∧
      (m=44 → (∀ S ∈ F, 44 ≤ S.card) ∧
        ((CrookedMembers F).filter (fun S => S.card=44)).card ≤ 44*N) ∧
      ∀ U j : ℕ, j+N ≤ U → CutoffTranslation20258.Witnesses U (AffineLine30.mapFamily j 1 F)
        m (AffineLine30.mapSet j 1 P) (AffineLine30.affine j 1 c) (AffineLine30.mapSet j 1 T) := by
  obtain ⟨m,low,high,covers,P,hP,c,hc,T,hT,miss,sz,_,minimal,rooted,cap,degree,side⟩ :=
    actual lo hi legal counter
  have w : CutoffTranslation20258.Witnesses N F m P c T :=
    ⟨hc,hP,hT,miss,sz,minimal,rooted,covers⟩
  refine ⟨m,low,high,P,c,T,w,cap,degree,side,?_,?_,fun _ _ fits =>
    CutoffTranslation20258.translate fits legal w⟩
  · intro small S hS
    by_contra! short
    have h := Nat.mul_le_mul (show m-1 ≤ 44 by omega) (show S.card ≤ 42 by omega)
    exact (not_lt_of_ge (SmallAnchor20258.of_member lo (by omega) legal small covers hS (by omega))) counter
  · rintro rfl
    exact SmallAnchor20258.at_44 lo (by omega) legal counter covers

#print axioms actual_padded
end
end JSP233.CutoffFamily20258
