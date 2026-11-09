module

public import Erdos272.Arithmetic.LightValues209_000
public import Erdos272.Arithmetic.LightValues209_001
public import Erdos272.Arithmetic.LightValues209_002
public import Erdos272.Arithmetic.LightValues209_003
public import Erdos272.Arithmetic.LightValues209_004
public import Erdos272.Arithmetic.LightValues209_005
public import Erdos272.Arithmetic.LightValues209_006
public import Erdos272.Arithmetic.LightValues209_007
public import Erdos272.Arithmetic.LightValues209_008
public import Erdos272.Arithmetic.LightValues209_009
public import Erdos272.Arithmetic.LightValues209_010
public import Erdos272.Arithmetic.LightValues209_011
public import Erdos272.Arithmetic.LightValues209_012
public import Erdos272.Arithmetic.LightValues209_013
public import Erdos272.Arithmetic.LightValues209_014

@[expose] public section
namespace JSP233.LightValues209
open LightAnalytic209 ResidualCeil208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := LightValues209_000.data++(LightValues209_001.data++(LightValues209_002.data++(LightValues209_003.data++(LightValues209_004.data++(LightValues209_005.data++(LightValues209_006.data++(LightValues209_007.data++(LightValues209_008.data++(LightValues209_009.data++(LightValues209_010.data++(LightValues209_011.data++(LightValues209_012.data++(LightValues209_013.data++(LightValues209_014.data))))))))))))))
theorem length : data.length=907 := by decide +kernel
def Good (as : List (ℕ×ℕ×ℕ×ℕ×ℕ)) : Prop := ∀a∈as,
  Alpha a.1 a.2.1 a.2.2.1 a.2.2.2.1 128≤(a.2.2.2.2 : ℝ)/(Grid : ℝ)
theorem good_append {as bs : List (ℕ×ℕ×ℕ×ℕ×ℕ)} (ha : Good as) (hb : Good bs) : Good (as++bs) := by
  intro a h
  rcases List.mem_append.mp h with h | h
  · exact ha a h
  · exact hb a h
theorem good : Good data := by
  have h0 : Good LightValues209_000.data := by intro a ha;exact LightValues209_000.bound ha
  have h1 : Good LightValues209_001.data := by intro a ha;exact LightValues209_001.bound ha
  have h2 : Good LightValues209_002.data := by intro a ha;exact LightValues209_002.bound ha
  have h3 : Good LightValues209_003.data := by intro a ha;exact LightValues209_003.bound ha
  have h4 : Good LightValues209_004.data := by intro a ha;exact LightValues209_004.bound ha
  have h5 : Good LightValues209_005.data := by intro a ha;exact LightValues209_005.bound ha
  have h6 : Good LightValues209_006.data := by intro a ha;exact LightValues209_006.bound ha
  have h7 : Good LightValues209_007.data := by intro a ha;exact LightValues209_007.bound ha
  have h8 : Good LightValues209_008.data := by intro a ha;exact LightValues209_008.bound ha
  have h9 : Good LightValues209_009.data := by intro a ha;exact LightValues209_009.bound ha
  have h10 : Good LightValues209_010.data := by intro a ha;exact LightValues209_010.bound ha
  have h11 : Good LightValues209_011.data := by intro a ha;exact LightValues209_011.bound ha
  have h12 : Good LightValues209_012.data := by intro a ha;exact LightValues209_012.bound ha
  have h13 : Good LightValues209_013.data := by intro a ha;exact LightValues209_013.bound ha
  have h14 : Good LightValues209_014.data := by intro a ha;exact LightValues209_014.bound ha

  exact good_append h0 (good_append h1 (good_append h2 (good_append h3 (good_append h4 (good_append h5 (good_append h6 (good_append h7 (good_append h8 (good_append h9 (good_append h10 (good_append h11 (good_append h12 (good_append h13 (h14))))))))))))))
theorem bound {A B V E u : ℕ} (ha : (A,B,V,E,u)∈data) :
    Alpha A B V E 128≤(u : ℝ)/(Grid : ℝ) := good _ ha
#print axioms bound
end
end JSP233.LightValues209
