module

public import Erdos272.Arithmetic.UniformPotential242_B00
public import Erdos272.Arithmetic.UniformPotential242_B01
public import Erdos272.Arithmetic.UniformPotential242_B02
public import Erdos272.Arithmetic.UniformPotential242_B03
public import Erdos272.Arithmetic.UniformPotential242_B04
public import Erdos272.Arithmetic.UniformPotential242_B05
public import Erdos272.Arithmetic.UniformPotential242_B06
public import Erdos272.Arithmetic.UniformPotential242_B07
public import Erdos272.Arithmetic.UniformPotential242_B08
public import Erdos272.Arithmetic.UniformPotential242_B09
public import Erdos272.Arithmetic.UniformPotential242_B10
public import Erdos272.Arithmetic.UniformPotential242_B11
public import Erdos272.Arithmetic.UniformPotential243_B00
public import Erdos272.Arithmetic.UniformPotential243_B01
public import Erdos272.Arithmetic.UniformPotential243_B02
public import Erdos272.Arithmetic.UniformPotential243_B03
public import Erdos272.Arithmetic.UniformPotential243_B04
public import Erdos272.Arithmetic.UniformPotential243_B05
public import Erdos272.Arithmetic.UniformPotential243_B06
public import Erdos272.Arithmetic.UniformPotential243_B07
public import Erdos272.Arithmetic.UniformPotential243_B08
public import Erdos272.Arithmetic.UniformPotential243_B09
public import Erdos272.Arithmetic.UniformPotential243_B10
public import Erdos272.Arithmetic.UniformPotential243_B11

@[expose] public section
namespace JSP233.UniformPotential208
open UniformQuery208 UniformEnvelope208 UniformSourceQueries208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
theorem facts242 (i : Fin 183) : Facts242 i.val := by
  by_cases h0 : i.val < 16
  · have hk : (0 : ℕ)+(i.val-0)=i.val := by omega
    have hh := facts242_B00 ⟨i.val-0,by omega⟩
    simpa only [hk] using hh
  by_cases h1 : i.val < 32
  · have hk : (16 : ℕ)+(i.val-16)=i.val := by omega
    have hh := facts242_B01 ⟨i.val-16,by omega⟩
    simpa only [hk] using hh
  by_cases h2 : i.val < 48
  · have hk : (32 : ℕ)+(i.val-32)=i.val := by omega
    have hh := facts242_B02 ⟨i.val-32,by omega⟩
    simpa only [hk] using hh
  by_cases h3 : i.val < 64
  · have hk : (48 : ℕ)+(i.val-48)=i.val := by omega
    have hh := facts242_B03 ⟨i.val-48,by omega⟩
    simpa only [hk] using hh
  by_cases h4 : i.val < 80
  · have hk : (64 : ℕ)+(i.val-64)=i.val := by omega
    have hh := facts242_B04 ⟨i.val-64,by omega⟩
    simpa only [hk] using hh
  by_cases h5 : i.val < 96
  · have hk : (80 : ℕ)+(i.val-80)=i.val := by omega
    have hh := facts242_B05 ⟨i.val-80,by omega⟩
    simpa only [hk] using hh
  by_cases h6 : i.val < 112
  · have hk : (96 : ℕ)+(i.val-96)=i.val := by omega
    have hh := facts242_B06 ⟨i.val-96,by omega⟩
    simpa only [hk] using hh
  by_cases h7 : i.val < 128
  · have hk : (112 : ℕ)+(i.val-112)=i.val := by omega
    have hh := facts242_B07 ⟨i.val-112,by omega⟩
    simpa only [hk] using hh
  by_cases h8 : i.val < 144
  · have hk : (128 : ℕ)+(i.val-128)=i.val := by omega
    have hh := facts242_B08 ⟨i.val-128,by omega⟩
    simpa only [hk] using hh
  by_cases h9 : i.val < 160
  · have hk : (144 : ℕ)+(i.val-144)=i.val := by omega
    have hh := facts242_B09 ⟨i.val-144,by omega⟩
    simpa only [hk] using hh
  by_cases h10 : i.val < 176
  · have hk : (160 : ℕ)+(i.val-160)=i.val := by omega
    have hh := facts242_B10 ⟨i.val-160,by omega⟩
    simpa only [hk] using hh
  have hk : (176 : ℕ)+(i.val-176)=i.val := by omega
  have hh := facts242_B11 ⟨i.val-176,by omega⟩
  simpa only [hk] using hh
theorem table242 (i : Fin 183) (j : Fin 7) :
    rowQuery242 i j=⟨242,(edges242[i.val]!)[j.val]!, (cuts242[i.val]!)[j.val]!,heights242[i.val+1]!⟩ := ((facts242 i).1 j).1
theorem steps242 (i : Fin 183) : heights242[i.val]! ≤ heights242[i.val+1]! := (facts242 i).2.1
theorem phi242_mono : Monotone phi242 := capped_monotone _ _ steps242
theorem real_phi242_mono : Monotone (fun n=>(phi242 n : ℝ)) := by
  intro a b hab
  change (phi242 a : ℝ)≤(phi242 b : ℝ)
  exact_mod_cast phi242_mono hab
theorem first_band242 (i : Fin 183) : (edges242[i.val]!)[0]! = 242 ∧ (cuts242[i.val]!)[0]! = i.val+1 := (facts242 i).2.2
theorem row_domain242 (i : Fin 183) (j : Fin 7) :
    242≤(edges242[i.val]!)[j.val]! ∧ (cuts242[i.val]!)[j.val]! ≤ i.val+1 ∧
      5*(cuts242[i.val]!)[j.val]! ≤ 4*242 := ((facts242 i).1 j).2
theorem source242 (i : Fin 183) (j : Fin 7) :
    Decision 242 ((edges242[i.val]!)[j.val]! : ℝ) ((cuts242[i.val]!)[j.val]! : ℝ) (heights242[i.val+1]! : ℝ) := by
  have hh := rowQuery242_sound i.isLt j.isLt
  rw [table242 i j] at hh
  exact hh
theorem base_source242 (i : Fin 183) :
    Decision 242 242 ((i.val+1 : ℕ) : ℝ) (phi242 (i.val+1) : ℝ) := by
  have hh := source242 i ⟨0,by decide⟩
  rw [(first_band242 i).1,(first_band242 i).2] at hh
  simpa only [phi242,min_eq_left (by omega : i.val+1≤183),Nat.cast_ofNat] using hh
#print axioms table242
#print axioms phi242_mono
#print axioms source242
#print axioms base_source242
theorem facts243 (i : Fin 184) : Facts243 i.val := by
  by_cases h0 : i.val < 16
  · have hk : (0 : ℕ)+(i.val-0)=i.val := by omega
    have hh := facts243_B00 ⟨i.val-0,by omega⟩
    simpa only [hk] using hh
  by_cases h1 : i.val < 32
  · have hk : (16 : ℕ)+(i.val-16)=i.val := by omega
    have hh := facts243_B01 ⟨i.val-16,by omega⟩
    simpa only [hk] using hh
  by_cases h2 : i.val < 48
  · have hk : (32 : ℕ)+(i.val-32)=i.val := by omega
    have hh := facts243_B02 ⟨i.val-32,by omega⟩
    simpa only [hk] using hh
  by_cases h3 : i.val < 64
  · have hk : (48 : ℕ)+(i.val-48)=i.val := by omega
    have hh := facts243_B03 ⟨i.val-48,by omega⟩
    simpa only [hk] using hh
  by_cases h4 : i.val < 80
  · have hk : (64 : ℕ)+(i.val-64)=i.val := by omega
    have hh := facts243_B04 ⟨i.val-64,by omega⟩
    simpa only [hk] using hh
  by_cases h5 : i.val < 96
  · have hk : (80 : ℕ)+(i.val-80)=i.val := by omega
    have hh := facts243_B05 ⟨i.val-80,by omega⟩
    simpa only [hk] using hh
  by_cases h6 : i.val < 112
  · have hk : (96 : ℕ)+(i.val-96)=i.val := by omega
    have hh := facts243_B06 ⟨i.val-96,by omega⟩
    simpa only [hk] using hh
  by_cases h7 : i.val < 128
  · have hk : (112 : ℕ)+(i.val-112)=i.val := by omega
    have hh := facts243_B07 ⟨i.val-112,by omega⟩
    simpa only [hk] using hh
  by_cases h8 : i.val < 144
  · have hk : (128 : ℕ)+(i.val-128)=i.val := by omega
    have hh := facts243_B08 ⟨i.val-128,by omega⟩
    simpa only [hk] using hh
  by_cases h9 : i.val < 160
  · have hk : (144 : ℕ)+(i.val-144)=i.val := by omega
    have hh := facts243_B09 ⟨i.val-144,by omega⟩
    simpa only [hk] using hh
  by_cases h10 : i.val < 176
  · have hk : (160 : ℕ)+(i.val-160)=i.val := by omega
    have hh := facts243_B10 ⟨i.val-160,by omega⟩
    simpa only [hk] using hh
  have hk : (176 : ℕ)+(i.val-176)=i.val := by omega
  have hh := facts243_B11 ⟨i.val-176,by omega⟩
  simpa only [hk] using hh
theorem table243 (i : Fin 184) (j : Fin 7) :
    rowQuery243 i j=⟨243,(edges243[i.val]!)[j.val]!, (cuts243[i.val]!)[j.val]!,heights243[i.val+1]!⟩ := ((facts243 i).1 j).1
theorem steps243 (i : Fin 184) : heights243[i.val]! ≤ heights243[i.val+1]! := (facts243 i).2.1
theorem phi243_mono : Monotone phi243 := capped_monotone _ _ steps243
theorem real_phi243_mono : Monotone (fun n=>(phi243 n : ℝ)) := by
  intro a b hab
  change (phi243 a : ℝ)≤(phi243 b : ℝ)
  exact_mod_cast phi243_mono hab
theorem first_band243 (i : Fin 184) : (edges243[i.val]!)[0]! = 243 ∧ (cuts243[i.val]!)[0]! = i.val+1 := (facts243 i).2.2
theorem row_domain243 (i : Fin 184) (j : Fin 7) :
    243≤(edges243[i.val]!)[j.val]! ∧ (cuts243[i.val]!)[j.val]! ≤ i.val+1 ∧
      5*(cuts243[i.val]!)[j.val]! ≤ 4*243 := ((facts243 i).1 j).2
theorem source243 (i : Fin 184) (j : Fin 7) :
    Decision 243 ((edges243[i.val]!)[j.val]! : ℝ) ((cuts243[i.val]!)[j.val]! : ℝ) (heights243[i.val+1]! : ℝ) := by
  have hh := rowQuery243_sound i.isLt j.isLt
  rw [table243 i j] at hh
  exact hh
theorem base_source243 (i : Fin 184) :
    Decision 243 243 ((i.val+1 : ℕ) : ℝ) (phi243 (i.val+1) : ℝ) := by
  have hh := source243 i ⟨0,by decide⟩
  rw [(first_band243 i).1,(first_band243 i).2] at hh
  simpa only [phi243,min_eq_left (by omega : i.val+1≤184),Nat.cast_ofNat] using hh
#print axioms table243
#print axioms phi243_mono
#print axioms source243
#print axioms base_source243
end JSP233.UniformPotential208
