module

public import Erdos272.Arithmetic.SimplexMoment57
public import Mathlib.Data.Nat.Sqrt

@[expose] public section
namespace JSP233.Hyperbola131
open SimplexMoment57
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Pairs (N B:ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter (fun p=>p.1*p.2≤N)
def Left (N B M:ℕ) := (Pairs N B).filter (fun p=>p.1≤M)
def Right (N B M:ℕ) := (Pairs N B).filter (fun p=>p.2≤M)

theorem row_eq {N B a:ℕ} (hNB:N≤B) (ha:a∈Finset.Icc 1 B) :
    (Pairs N B).filter (fun p=>p.1=a)=(Finset.Icc 1 (N/a)).image (fun b=>(a,b)) := by
  obtain ⟨ha0,haB⟩ := Finset.mem_Icc.mp ha
  ext p
  constructor
  · intro hp
    obtain ⟨hpP,he⟩ := Finset.mem_filter.mp hp
    obtain ⟨hprod,hN⟩ := Finset.mem_filter.mp hpP
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hprod
    refine Finset.mem_image.mpr ⟨p.2,Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp2).1,?_⟩,?_⟩
    · apply (Nat.le_div_iff_mul_le ha0).mpr
      simpa only [he,Nat.mul_comm] using hN
    · exact Prod.ext he.symm rfl
  · intro hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hb0,hba⟩ := Finset.mem_Icc.mp hb
    have hbB : b≤B := hba.trans ((Nat.div_le_self N a).trans hNB)
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha0,haB⟩,Finset.mem_Icc.mpr ⟨hb0,hbB⟩⟩
    · simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha0).mp hba

theorem row_card {N B a:ℕ} (hNB:N≤B) (ha:a∈Finset.Icc 1 B) :
    ((Pairs N B).filter (fun p=>p.1=a)).card=N/a := by
  rw [row_eq hNB ha,Finset.card_image_of_injective _ (by intro u v h;exact congrArg Prod.snd h)]
  simp

theorem pairs_card {N B:ℕ} (hNB:N≤B) : (Pairs N B).card=DivCount 1 N := by
  rw [Finset.card_eq_sum_card_fiberwise (f:=Prod.fst) (t:=Finset.Icc 1 B)
    (by intro p hp;exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)]
  calc
    _=∑a∈Finset.Icc 1 B,N/a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact row_card hNB ha
    _=DivCount 1 N := by simpa only [DivCount] using div_count_extend hNB 0

theorem left_card {N B M:ℕ} (hNB:N≤B) (hMB:M≤B) :
    (Left N B M).card=∑a∈Finset.Icc 1 M,N/a := by
  rw [Finset.card_eq_sum_card_fiberwise (f:=Prod.fst) (t:=Finset.Icc 1 M)
    (by
      intro p hp
      obtain ⟨hp,hM⟩ := Finset.mem_filter.mp hp
      have hp0 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1).1
      exact Finset.mem_Icc.mpr ⟨hp0,hM⟩)]
  apply Finset.sum_congr rfl
  intro a ha
  have har := Finset.mem_Icc.mp ha
  have he : (Left N B M).filter (fun p=>p.1=a)=(Pairs N B).filter (fun p=>p.1=a) := by
    ext p
    simp only [Left,Finset.mem_filter]
    constructor
    · tauto
    · rintro ⟨hp,he⟩
      exact ⟨⟨hp,he ▸ har.2⟩,he⟩
  rw [he,row_card hNB (Finset.mem_Icc.mpr ⟨har.1,har.2.trans hMB⟩)]

theorem swap_mem {N B:ℕ} (p:ℕ×ℕ) : p.swap∈Pairs N B↔p∈Pairs N B := by
  simp only [Pairs,Finset.mem_filter,Finset.mem_product,Prod.fst_swap,Prod.snd_swap]
  constructor <;> rintro ⟨⟨h1,h2⟩,h3⟩ <;> exact ⟨⟨h2,h1⟩,by simpa only [Nat.mul_comm] using h3⟩

theorem right_card (N B M:ℕ) : (Right N B M).card=(Left N B M).card := by
  apply Finset.card_bij (fun p _=>p.swap)
  · intro p hp
    exact Finset.mem_filter.mpr ⟨(swap_mem p).mpr (Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2⟩
  · intro p hp q hq he
    exact congrArg Prod.swap he
  · intro p hp
    refine ⟨p.swap,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨(swap_mem p).mpr (Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2⟩
    · rfl

theorem union_eq {N B M:ℕ} (hN:N<(M+1)^2) :
    Left N B M∪Right N B M=Pairs N B := by
  ext p
  simp only [Left,Right,Finset.mem_union,Finset.mem_filter]
  constructor
  · tauto
  · intro hp
    by_cases h1:p.1≤M
    · exact Or.inl ⟨hp,h1⟩
    · right
      refine ⟨hp,?_⟩
      by_contra h2
      have hmul := (Finset.mem_filter.mp hp).2
      have ha : M+1≤p.1 := by omega
      have hb : M+1≤p.2 := by omega
      have hge := Nat.mul_le_mul ha hb
      nlinarith only [hN,hmul,hge]

theorem inter_eq {N B M:ℕ} (hMB:M≤B) (hM:M^2≤N) :
    Left N B M∩Right N B M=((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp1,hp2⟩ := Finset.mem_inter.mp hp
    obtain ⟨hp1,hM1⟩ := Finset.mem_filter.mp hp1
    obtain ⟨_,hM2⟩ := Finset.mem_filter.mp hp2
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp1).1
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1,hM1⟩,
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hb).1,hM2⟩⟩
  · intro hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    obtain ⟨ha0,haM⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hb0,hbM⟩ := Finset.mem_Icc.mp hb
    have hprod : p∈Pairs N B := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨ha0,haM.trans hMB⟩,Finset.mem_Icc.mpr ⟨hb0,hbM.trans hMB⟩⟩,?_⟩
      exact (Nat.mul_le_mul haM hbM).trans (by simpa only [pow_two] using hM)
    exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hprod,haM⟩,Finset.mem_filter.mpr ⟨hprod,hbM⟩⟩

theorem actual_hyperbola_nat {N M:ℕ} (hM:M^2≤N) (hN:N<(M+1)^2) :
    DivCount 1 N+M^2=2*∑a∈Finset.Icc 1 M,N/a := by
  have h := Finset.card_union_add_card_inter (Left N (N+M) M) (Right N (N+M) M)
  rw [union_eq hN,inter_eq (by omega : M≤N+M) hM,pairs_card (by omega : N≤N+M),
    Finset.card_product,right_card,left_card (by omega : N≤N+M) (by omega : M≤N+M)] at h
  simpa only [Nat.card_Icc,Nat.add_sub_cancel,pow_two,two_mul] using h

theorem actual_hyperbola_real {N M:ℕ} (hM:M^2≤N) (hN:N<(M+1)^2) :
    (DivCount 1 N:ℝ)=2*(∑a∈Finset.Icc 1 M,((N/a:ℕ):ℝ))-(M:ℝ)^2 := by
  have h : (DivCount 1 N:ℝ)+(M:ℝ)^2=2*(∑a∈Finset.Icc 1 M,((N/a:ℕ):ℝ)) := by
    exact_mod_cast actual_hyperbola_nat hM hN
  linarith only [h]

#print axioms row_eq
#print axioms row_card
#print axioms pairs_card
#print axioms left_card
#print axioms swap_mem
#print axioms right_card
#print axioms union_eq
#print axioms inter_eq
#print axioms actual_hyperbola_nat
#print axioms actual_hyperbola_real
end
end JSP233.Hyperbola131
