module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source121
public import Erdos272.Arithmetic.N20258.Sources.Source122
public import Erdos272.Arithmetic.N20258.Sources.Source123
public import Erdos272.Arithmetic.N20258.Sources.Source124

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests72_121_0 : ∀ z∈source121.plan.table,z.1.Valid 72 0 := by decide +kernel
private theorem fee72_121_24300 :
    PopulationFees20258.bill (n:=24300) (PopulationFees20258.tabulate (24300-1) 256) source121.plan.table+
      4*24300*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*259808834369 := by decide +kernel
private theorem range72From20258To2543 : Segment 72 20258 24300 0 2543 :=
  paid (pc:=57) (v:=259808834369) (by decide) source121_valid tests72_121_0 fee72_121_24300 (by decide +kernel)

private theorem tests72_121_2543 : ∀ z∈source121.plan.table,z.1.Valid 72 2543 := by decide +kernel
private theorem range72From20258To2698 : Segment 72 20258 24300 2543 2698 :=
  paid (pc:=55) (v:=259808834369) (by decide) source121_valid tests72_121_2543 fee72_121_24300 (by decide +kernel)

private theorem tests72_121_2698 : ∀ z∈source121.plan.table,z.1.Valid 72 2698 := by decide +kernel
private theorem range72From20258To2748 : Segment 72 20258 24300 2698 2748 :=
  paid (pc:=55) (v:=259808834369) (by decide) source121_valid tests72_121_2698 fee72_121_24300 (by decide +kernel)

private theorem tests72_121_2748 : ∀ z∈source121.plan.table,z.1.Valid 72 2748 := by decide +kernel
private theorem range72From20258To2775 : Segment 72 20258 24300 2748 2775 :=
  paid (pc:=54) (v:=259808834369) (by decide) source121_valid tests72_121_2748 fee72_121_24300 (by decide +kernel)

private theorem tests72_121_2775 : ∀ z∈source121.plan.table,z.1.Valid 72 2775 := by decide +kernel
private theorem range72From20258To5113 : Segment 72 20258 24300 2775 5113 :=
  paid (pc:=53) (v:=259808834369) (by decide) source121_valid tests72_121_2775 fee72_121_24300 (by decide +kernel)

private theorem range72From20258 : Win 72 20258 24300 :=
  complete (by decide) (by decide) (join_population (join_population range72From20258To2543 range72From20258To2698) (join_population range72From20258To2748 (join_population range72From20258To2775 range72From20258To5113)))

private theorem tests72_123_0 : ∀ z∈source123.plan.table,z.1.Valid 72 0 := by decide +kernel
private theorem fee72_123_29070 :
    PopulationFees20258.bill (n:=29070) (PopulationFees20258.tabulate (29070-1) 256) source123.plan.table+
      4*29070*NaturalPopulation20258.weights source123.extras≤source123.plan.scale*717667556919 := by decide +kernel
private theorem range72From24301To5113 : Segment 72 24301 29070 0 5113 :=
  paid (pc:=65) (v:=717667556919) (by decide) source123_valid tests72_123_0 fee72_123_29070 (by decide +kernel)

private theorem range72From24301 : Win 72 24301 29070 :=
  complete (by decide) (by decide) range72From24301To5113

private theorem fee72_123_33517 :
    PopulationFees20258.bill (n:=33517) (PopulationFees20258.tabulate (33517-1) 256) source123.plan.table+
      4*33517*NaturalPopulation20258.weights source123.extras≤source123.plan.scale*924995008074 := by decide +kernel
private theorem range72From29071To3770 : Segment 72 29071 33517 0 3770 :=
  paid (pc:=60) (v:=924995008074) (by decide) source123_valid tests72_123_0 fee72_123_33517 (by decide +kernel)

private theorem tests72_123_3770 : ∀ z∈source123.plan.table,z.1.Valid 72 3770 := by decide +kernel
private theorem range72From29071To4025 : Segment 72 29071 33517 3770 4025 :=
  paid (pc:=58) (v:=924995008074) (by decide) source123_valid tests72_123_3770 fee72_123_33517 (by decide +kernel)

private theorem tests72_123_4025 : ∀ z∈source123.plan.table,z.1.Valid 72 4025 := by decide +kernel
private theorem range72From29071To4115 : Segment 72 29071 33517 4025 4115 :=
  paid (pc:=58) (v:=924995008074) (by decide) source123_valid tests72_123_4025 fee72_123_33517 (by decide +kernel)

private theorem tests72_123_4115 : ∀ z∈source123.plan.table,z.1.Valid 72 4115 := by decide +kernel
private theorem range72From29071To4144 : Segment 72 29071 33517 4115 4144 :=
  paid (pc:=58) (v:=924995008074) (by decide) source123_valid tests72_123_4115 fee72_123_33517 (by decide +kernel)

private theorem tests72_123_4144 : ∀ z∈source123.plan.table,z.1.Valid 72 4144 := by decide +kernel
private theorem range72From29071To4198 : Segment 72 29071 33517 4144 4198 :=
  paid (pc:=57) (v:=924995008074) (by decide) source123_valid tests72_123_4144 fee72_123_33517 (by decide +kernel)

private theorem tests72_122_4198 : ∀ z∈source122.plan.table,z.1.Valid 72 4198 := by decide +kernel
private theorem fee72_122_33517 :
    PopulationFees20258.bill (n:=33517) (PopulationFees20258.tabulate (33517-1) 256) source122.plan.table+
      4*33517*NaturalPopulation20258.weights source122.extras≤source122.plan.scale*905197378840 := by decide +kernel
private theorem range72From29071To5113 : Segment 72 29071 33517 4198 5113 :=
  paid (pc:=56) (v:=905197378840) (by decide) source122_valid tests72_122_4198 fee72_122_33517 (by decide +kernel)

private theorem range72From29071 : Win 72 29071 33517 :=
  complete (by decide) (by decide) (join_population (join_population range72From29071To3770 (join_population range72From29071To4025 range72From29071To4115)) (join_population range72From29071To4144 (join_population range72From29071To4198 range72From29071To5113)))

private theorem fee72_123_37288 :
    PopulationFees20258.bill (n:=37288) (PopulationFees20258.tabulate (37288-1) 256) source123.plan.table+
      4*37288*NaturalPopulation20258.weights source123.extras≤source123.plan.scale*1121110720073 := by decide +kernel
private theorem range72From33518To4205 : Segment 72 33518 37288 0 4205 :=
  paid (pc:=65) (v:=1121110720073) (by decide) source123_valid tests72_123_0 fee72_123_37288 (by decide +kernel)

private theorem tests72_122_4205 : ∀ z∈source122.plan.table,z.1.Valid 72 4205 := by decide +kernel
private theorem fee72_122_37288 :
    PopulationFees20258.bill (n:=37288) (PopulationFees20258.tabulate (37288-1) 256) source122.plan.table+
      4*37288*NaturalPopulation20258.weights source122.extras≤source122.plan.scale*1098147429539 := by decide +kernel
private theorem range72From33518To4386 : Segment 72 33518 37288 4205 4386 :=
  paid (pc:=64) (v:=1098147429539) (by decide) source122_valid tests72_122_4205 fee72_122_37288 (by decide +kernel)

private theorem tests72_122_4386 : ∀ z∈source122.plan.table,z.1.Valid 72 4386 := by decide +kernel
private theorem range72From33518To4393 : Segment 72 33518 37288 4386 4393 :=
  paid (pc:=64) (v:=1098147429539) (by decide) source122_valid tests72_122_4386 fee72_122_37288 (by decide +kernel)

private theorem tests72_124_4393 : ∀ z∈source124.plan.table,z.1.Valid 72 4393 := by decide +kernel
private theorem fee72_124_37288 :
    PopulationFees20258.bill (n:=37288) (PopulationFees20258.tabulate (37288-1) 256) source124.plan.table+
      4*37288*NaturalPopulation20258.weights source124.extras≤source124.plan.scale*943957011183 := by decide +kernel
private theorem range72From33518To5113 : Segment 72 33518 37288 4393 5113 :=
  paid (pc:=59) (v:=943957011183) (by decide) source124_valid tests72_124_4393 fee72_124_37288 (by decide +kernel)

private theorem range72From33518 : Win 72 33518 37288 :=
  complete (by decide) (by decide) (join_population (join_population range72From33518To4205 range72From33518To4386) (join_population range72From33518To4393 range72From33518To5113))

private theorem fee72_123_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source123.plan.table+
      4*39999*NaturalPopulation20258.weights source123.extras≤source123.plan.scale*1273573311943 := by decide +kernel
private theorem range72From37289To4945 : Segment 72 37289 39999 0 4945 :=
  paid (pc:=68) (v:=1273573311943) (by decide) source123_valid tests72_123_0 fee72_123_39999 (by decide +kernel)

private theorem tests72_124_4945 : ∀ z∈source124.plan.table,z.1.Valid 72 4945 := by decide +kernel
private theorem fee72_124_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source124.plan.table+
      4*39999*NaturalPopulation20258.weights source124.extras≤source124.plan.scale*1073167307727 := by decide +kernel
private theorem range72From37289To5113 : Segment 72 37289 39999 4945 5113 :=
  paid (pc:=66) (v:=1073167307727) (by decide) source124_valid tests72_124_4945 fee72_124_39999 (by decide +kernel)

private theorem range72From37289 : Win 72 37289 39999 :=
  complete (by decide) (by decide) (join_population range72From37289To4945 range72From37289To5113)

theorem cut72From20258 : Win 72 20258 39999 :=
  (join_ground (join_ground range72From20258 range72From24301) (join_ground range72From29071 (join_ground range72From33518 range72From37289)))

end JSP233.FiniteCutRanges20258
