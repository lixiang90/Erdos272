module

public import Erdos272.Geometry.N20258.ExteriorFarPool20258
public import Erdos272.Counting.N20258.ExteriorStrides20258
public import Erdos272.Core.SinglePrivate32

@[expose] public section
namespace JSP233.ExteriorDichotomy20258
open StarCompletion APGeometry AffineLine30 SourceBridge208 IntrinsicTriples208
open ExteriorPrefix20258 ExteriorStrides20258
open scoped Classical
noncomputable section
set_option autoImplicit false

private theorem grids (p d : ℤ) (m : ℕ) :
    let P := (Finset.range (m+1)).image (fun i : ℕ => p+d*(i:ℤ))
    mapSet p d (Finset.Icc 0 (m:ℤ))=P ∧
    mapSet (p+d*m) (-d) (Finset.Icc 0 (m:ℤ))=P := by
  dsimp only
  constructor
  · ext z
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨l,u⟩ := Finset.mem_Icc.mp hi
      exact Finset.mem_image.mpr ⟨i.toNat,Finset.mem_range.mpr (by omega),by simp [affine,Int.toNat_of_nonneg l]⟩
    · intro h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      have := Finset.mem_range.mp hi
      exact Finset.mem_image.mpr ⟨i,Finset.mem_Icc.mpr (by omega),rfl⟩
  · ext z
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨l,u⟩ := Finset.mem_Icc.mp hi
      refine Finset.mem_image.mpr ⟨((m:ℤ)-i).toNat,Finset.mem_range.mpr (by omega),?_⟩
      rw [Int.toNat_of_nonneg (by omega)]
      dsimp [affine]; ring
    · intro h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      have := Finset.mem_range.mp hi
      exact Finset.mem_image.mpr ⟨(m:ℤ)-i,Finset.mem_Icc.mpr (by omega),by dsimp [affine]; ring⟩

private theorem adjacent (a d : ℤ) (m : ℕ) (hd : d≠0) :
    IsAP (mapSet a d (shape m 0 1)) := by
  apply SinglePrivate32.affine_isAP_of_ne_zero a d hd
  refine ⟨1,0,by decide,-1,m,?_,?_⟩
  · intro z
    simp only [shape,Finset.mem_insert,Finset.mem_Icc,one_dvd,and_true]
    omega
  · exact Finset.mem_insert_of_mem (Finset.mem_Icc.mpr (by omega))

private theorem near_or_far {S P : Finset ℤ} {m : ℕ} {p d k x : ℤ}
    (hd : 0<d) (grid : P=(Finset.range (m+1)).image (fun i : ℕ => p+d*(i:ℤ)))
    (point : x=p+d*k) (out : x∉P) (eqn : S=insert x P) (bad : ¬IsAP S) :
    P.card.choose 2≤(Pool S).card ∨ ∃ e : ℕ, 0<e ∧ (fits S m m e ∨ fits S m m (-(e:ℤ))) := by
  obtain ⟨left,right⟩ := grids p d m
  rw [←grid] at left right
  have bounds : P⊆Finset.Icc p (p+d*m) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (grid ▸ hz)
    have hi' := Finset.mem_range.mp hi
    have l := mul_nonneg hd.le (Nat.cast_nonneg (α:=ℤ) i)
    have u := mul_le_mul_of_nonneg_left (by omega : (i:ℤ)≤m) hd.le
    exact Finset.mem_Icc.mpr ⟨by linarith,by linarith⟩
  have dcast : (d.toNat:ℤ)=d := Int.toNat_of_nonneg hd.le
  have dpos : 0<d.toNat := by omega
  have outside : k<0 ∨ (m:ℤ)<k := by
    by_contra! mid
    apply out
    rw [←left,point]
    exact Finset.mem_image.mpr ⟨k,Finset.mem_Icc.mpr (by omega),rfl⟩
  have produce (a e : ℤ) (t : ℕ) (en : e≠0) (pos : 0<t) (top : t≤m)
      (core : mapSet a e (Finset.Icc 0 (m:ℤ))=P) (loc : affine a e (0-(t:ℤ))=x) :
      fits S m m e := by
    have rep : S=mapSet a e (shape m 0 t) := by
      unfold shape
      rw [zero_add,mapSet_insert,loc,core,eqn]
    refine ⟨a,t,?_,top,rep⟩
    by_contra! tiny
    have one : t=1 := by omega
    exact bad (rep ▸ one ▸ adjacent a e m en)
  rcases outside with h|h
  · let t := (-k).toNat
    have tc : (t:ℤ) = -k := Int.toNat_of_nonneg (by omega)
    by_cases top : t≤m
    · exact Or.inr ⟨d.toNat,dpos,Or.inl (dcast ▸ produce p d t hd.ne' (by omega) top left
        (by dsimp [affine]; rw [tc,point]; ring))⟩
    · have gap := mul_lt_mul_of_pos_left (show (m:ℤ)< -k by omega) hd
      rw [eqn]
      exact Or.inl (ExteriorFarPool20258.actual bounds (Or.inl (by rw [point]; linarith only [gap])) out)
  · let t := (k-m).toNat
    have tc : (t:ℤ)=k-m := Int.toNat_of_nonneg (by omega)
    by_cases top : t≤m
    · exact Or.inr ⟨d.toNat,dpos,Or.inr (dcast ▸ produce (p+d*m) (-d) t (by omega) (by omega) top right
        (by dsimp [affine]; rw [tc,point]; ring))⟩
    · have gap := mul_lt_mul_of_pos_left (show (m:ℤ)<k-m by omega) hd
      rw [eqn]
      exact Or.inl (ExteriorFarPool20258.actual bounds (Or.inr (by rw [point]; linarith only [gap])) out)

/-- A one-point defect pays the midpoint lower bound except for one of the
near oriented shapes counted by the physical stride theorem. -/
theorem actual {S : Finset ℤ} (sz : 3≤S.card) (bad : ¬IsAP S) (one : Defect S=1) :
    (S.card-1).choose 2-(S.card-1)/2≤(Pool S).card ∨
      ∃ e : ℕ, 0<e ∧ (fits S (S.card-2) (S.card-2) e ∨ fits S (S.card-2) (S.card-2) (-(e:ℤ))) := by
  obtain ⟨P,d,p,hd,sub,pc,_,ap,grid⟩ := ActualCorePairs200000.actual_source_core (by omega : 2≤S.card)
  have total := maxAPSize_le_card S
  unfold Defect at one
  have psize : P.card=S.card-1 := by omega
  have meq : MaxAPSize S=(S.card-2)+1 := by omega
  rw [meq] at grid
  have gone : (S\P).card=1 := by rw [Finset.card_sdiff_of_subset sub]; omega
  obtain ⟨x,single⟩ := Finset.card_eq_one.mp gone
  have hx := Finset.mem_sdiff.mp (show x∈S\P by rw [single]; simp)
  have eqn : S=insert x P := by
    ext y
    constructor
    · intro h
      by_cases hp : y∈P
      · exact Finset.mem_insert_of_mem hp
      · have hxy : y∈({x}:Finset ℤ) := single ▸ Finset.mem_sdiff.mpr ⟨h,hp⟩
        exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hxy))
    · intro h
      exact (Finset.mem_insert.mp h).elim (fun he => he ▸ hx.1) (fun hp => sub hp)
  have phase (y : ℤ) (hy : y∈P) : d∣y-p := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (grid ▸ hy)
    exact ⟨i,by ring⟩
  by_cases dg : d∣x-p
  · obtain ⟨k,hk⟩ := dg
    exact (near_or_far hd grid (by linarith only [hk] : x=p+d*k) hx.2 eqn bad).imp
      (fun h => by rw [psize] at h; omega) id
  · left
    rw [←psize]
    exact OffGridPool20258.actual_pool_bound sub hx.1 phase (fun y hy yx =>
      phase y ((Finset.mem_insert.mp (eqn ▸ hy)).resolve_left yx)) dg

#print axioms actual
end
end JSP233.ExteriorDichotomy20258
