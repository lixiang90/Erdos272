module

public import Erdos272.Geometry.AnchorHalf136
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

@[expose] public section
namespace JSP233.CoreShellHalf136
open StarCompletion APGeometry FarSlot112 FarCapacity112 FarJoint112 LongTerminal35
open AnchorHalf136
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def IntrinsicCodes (S:Finset ℤ) (C:Finset (ℕ×(ℤ×ℤ))) : Finset (ℕ×(ℤ×ℤ)) :=
  C.filter (fun q=>IntrinsicPair q.2.1 S {q.2.1+(q.1:ℤ),q.2.2})

theorem core_shell_intrinsic_fiber {S P:Finset ℤ} {d:ℕ} {x:ℤ} (hx:x∈S\P) :
    (IntrinsicCodes S (CoreShellCodes S P d)).bipartiteAbove (fun x q=>q.2.2=x) x=
      (IntrinsicEdges S P (d:ℤ) x).image (fun a=>(d,(a,x))) := by
  ext q
  rcases q with ⟨e,a,y⟩
  constructor
  · intro h
    obtain ⟨hG,hyx⟩:=Finset.mem_filter.mp h
    obtain ⟨hC,hI⟩:=Finset.mem_filter.mp hG
    obtain ⟨he,ha,hb,_hy⟩:=mem_coreShellCodes.mp hC
    change e=d at he
    obtain rfl:=he
    change y=x at hyx
    obtain rfl:=hyx
    exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨ha,hb⟩,hI⟩,rfl⟩
  · intro h
    obtain ⟨b,hb,he⟩:=Finset.mem_image.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl,rfl,rfl⟩:=he
    obtain ⟨hE,hI⟩:=Finset.mem_filter.mp hb
    obtain ⟨ha,had⟩:=Finset.mem_filter.mp hE
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨mem_coreShellCodes.mpr ⟨rfl,ha,had,hx⟩,hI⟩,rfl⟩

theorem core_shell_intrinsic_fiber_card {S P:Finset ℤ} {d:ℕ} {x:ℤ} (hx:x∈S\P) :
    ((IntrinsicCodes S (CoreShellCodes S P d)).bipartiteAbove (fun x q=>q.2.2=x) x).card=
      (IntrinsicEdges S P (d:ℤ) x).card := by
  rw [core_shell_intrinsic_fiber hx]
  apply Finset.card_image_of_injective
  intro a b h
  exact congrArg (fun q:ℕ×(ℤ×ℤ)=>q.2.1) h

theorem core_shell_half_intrinsic {S P:Finset ℤ} {d:ℕ} {p:ℤ}
    (hmax:MaximumAPCore S P) (hAt:APAt (d:ℤ) p P) :
    (CoreShellCodes S P d).card≤2*(IntrinsicCodes S (CoreShellCodes S P d)).card := by
  let E:=CoreEdges P (d:ℤ)
  let X:=S\P
  let G:=IntrinsicCodes S (CoreShellCodes S P d)
  let rel:ℤ→(ℕ×(ℤ×ℤ))→Prop:=fun x q=>q.2.2=x
  let m:ℕ:=(E.card+1)/2
  have hc:=Finset.card_mul_le_card_mul (s:=X) (t:=G) (r:=rel) (m:=m) (n:=1)
    (by
      intro x hx
      have hh:=at_least_half_intrinsic_core_edges hmax hAt hx
      rw [core_shell_intrinsic_fiber_card hx]
      dsimp only [m,E] at *
      omega)
    (by
      intro q _hq
      apply Finset.card_le_one.mpr
      intro x hx y hy
      obtain ⟨_hx,hqx⟩:=Finset.mem_filter.mp hx
      obtain ⟨_hy,hqy⟩:=Finset.mem_filter.mp hy
      change q.2.2=x at hqx
      change q.2.2=y at hqy
      exact hqx.symm.trans hqy)
  have hcount:m*X.card≤G.card:=by simpa only [Nat.mul_one,Nat.one_mul,Nat.mul_comm] using hc
  have hceil:E.card≤2*m:=by dsimp only [m];omega
  have he:(CoreShellCodes S P d).card=E.card*X.card:=by
    rw [coreShellCodes_card hAt (isAP_nonempty hmax.2.1),coreEdges_card hAt (isAP_nonempty hmax.2.1)]
  calc
    _=E.card*X.card:=he
    _≤(2*m)*X.card:=Nat.mul_le_mul_right X.card hceil
    _=2*(m*X.card):=by ring
    _≤2*G.card:=Nat.mul_le_mul_left 2 hcount

theorem short_codes_all_intrinsic (N D:ℕ) (S:Finset ℤ) :
    IntrinsicCodes S (IntrinsicSlotCodes N D S)=IntrinsicSlotCodes N D S := by
  apply Finset.filter_eq_self.mpr
  intro q hq
  exact (mem_intrinsicSlotCodes.mp hq).2.2

theorem actual_joint_half_intrinsic {N D:ℕ} {S:Finset ℤ}
    (core:Finset ℤ→Finset ℤ) (step:Finset ℤ→ℕ) (short:Finset ℤ→Prop)
    (hmax:MaximumAPCore S (core S)) (hAt:∃p,APAt (step S:ℤ) p (core S)) :
    (JointCodes N D core step short S).card≤
      2*(IntrinsicCodes S (JointCodes N D core step short S)).card := by
  by_cases hs:short S
  · simp only [JointCodes,if_pos hs,short_codes_all_intrinsic]
    omega
  · simp only [JointCodes,if_neg hs]
    obtain ⟨p,hp⟩:=hAt
    exact core_shell_half_intrinsic hmax hp

#print axioms core_shell_intrinsic_fiber
#print axioms core_shell_intrinsic_fiber_card
#print axioms core_shell_half_intrinsic
#print axioms short_codes_all_intrinsic
#print axioms actual_joint_half_intrinsic
end
end JSP233.CoreShellHalf136
