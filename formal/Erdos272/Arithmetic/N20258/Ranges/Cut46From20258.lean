module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source001
public import Erdos272.Arithmetic.N20258.Sources.Source002

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests46_001_0 : ∀ z∈source001.plan.table,z.1.Valid 46 0 := by decide +kernel
private theorem fee46_001_20664 :
    PopulationFees20258.bill (n:=20664) (PopulationFees20258.tabulate (20664-1) 256) source001.plan.table+
      4*20664*NaturalPopulation20258.weights source001.extras≤source001.plan.scale*78923797467 := by decide +kernel
private theorem range46From20258To1980 : Segment 46 20258 20664 0 1980 :=
  paid (pc:=80) (v:=78923797467) (by decide) source001_valid tests46_001_0 fee46_001_20664 (by decide +kernel)

private theorem tests46_001_1980 : ∀ z∈source001.plan.table,z.1.Valid 46 1980 := by decide +kernel
private theorem range46From20258To1984 : Segment 46 20258 20664 1980 1984 :=
  paid (pc:=80) (v:=78923797467) (by decide) source001_valid tests46_001_1980 fee46_001_20664 (by decide +kernel)

private theorem tests46_002_1984 : ∀ z∈source002.plan.table,z.1.Valid 46 1984 := by decide +kernel
private theorem fee46_002_20664 :
    PopulationFees20258.bill (n:=20664) (PopulationFees20258.tabulate (20664-1) 256) source002.plan.table+
      4*20664*NaturalPopulation20258.weights source002.extras≤source002.plan.scale*140909678950 := by decide +kernel
private theorem range46From20258To2069 : Segment 46 20258 20664 1984 2069 :=
  paid (pc:=79) (v:=140909678950) (by decide) source002_valid tests46_002_1984 fee46_002_20664 (by decide +kernel)

private theorem tests46_002_2069 : ∀ z∈source002.plan.table,z.1.Valid 46 2069 := by decide +kernel
private theorem range46From20258To2071 : Segment 46 20258 20664 2069 2071 :=
  paid (pc:=79) (v:=140909678950) (by decide) source002_valid tests46_002_2069 fee46_002_20664 (by decide +kernel)

private theorem range46From20258 : Win 46 20258 20664 :=
  complete (by decide) (by decide) (join_population (join_population range46From20258To1980 range46From20258To1984) (join_population range46From20258To2069 range46From20258To2071))

private theorem fee46_001_21182 :
    PopulationFees20258.bill (n:=21182) (PopulationFees20258.tabulate (21182-1) 256) source001.plan.table+
      4*21182*NaturalPopulation20258.weights source001.extras≤source001.plan.scale*82741300517 := by decide +kernel
private theorem range46From20665To1989 : Segment 46 20665 21182 0 1989 :=
  paid (pc:=79) (v:=82741300517) (by decide) source001_valid tests46_001_0 fee46_001_21182 (by decide +kernel)

private theorem tests46_002_1989 : ∀ z∈source002.plan.table,z.1.Valid 46 1989 := by decide +kernel
private theorem fee46_002_21182 :
    PopulationFees20258.bill (n:=21182) (PopulationFees20258.tabulate (21182-1) 256) source002.plan.table+
      4*21182*NaturalPopulation20258.weights source002.extras≤source002.plan.scale*147644404901 := by decide +kernel
private theorem range46From20665To2070 : Segment 46 20665 21182 1989 2070 :=
  paid (pc:=79) (v:=147644404901) (by decide) source002_valid tests46_002_1989 fee46_002_21182 (by decide +kernel)

private theorem tests46_002_2070 : ∀ z∈source002.plan.table,z.1.Valid 46 2070 := by decide +kernel
private theorem range46From20665To2071 : Segment 46 20665 21182 2070 2071 :=
  paid (pc:=79) (v:=147644404901) (by decide) source002_valid tests46_002_2070 fee46_002_21182 (by decide +kernel)

private theorem range46From20665 : Win 46 20665 21182 :=
  complete (by decide) (by decide) (join_population range46From20665To1989 (join_population range46From20665To2070 range46From20665To2071))

private theorem fee46_001_21852 :
    PopulationFees20258.bill (n:=21852) (PopulationFees20258.tabulate (21852-1) 256) source001.plan.table+
      4*21852*NaturalPopulation20258.weights source001.extras≤source001.plan.scale*87774253921 := by decide +kernel
private theorem range46From21183To1999 : Segment 46 21183 21852 0 1999 :=
  paid (pc:=79) (v:=87774253921) (by decide) source001_valid tests46_001_0 fee46_001_21852 (by decide +kernel)

private theorem tests46_002_1999 : ∀ z∈source002.plan.table,z.1.Valid 46 1999 := by decide +kernel
private theorem fee46_002_21852 :
    PopulationFees20258.bill (n:=21852) (PopulationFees20258.tabulate (21852-1) 256) source002.plan.table+
      4*21852*NaturalPopulation20258.weights source002.extras≤source002.plan.scale*156518099570 := by decide +kernel
private theorem range46From21183To2070 : Segment 46 21183 21852 1999 2070 :=
  paid (pc:=78) (v:=156518099570) (by decide) source002_valid tests46_002_1999 fee46_002_21852 (by decide +kernel)

private theorem range46From21183To2071 : Segment 46 21183 21852 2070 2071 :=
  paid (pc:=78) (v:=156518099570) (by decide) source002_valid tests46_002_2070 fee46_002_21852 (by decide +kernel)

private theorem range46From21183 : Win 46 21183 21852 :=
  complete (by decide) (by decide) (join_population range46From21183To1999 (join_population range46From21183To2070 range46From21183To2071))

private theorem fee46_001_22726 :
    PopulationFees20258.bill (n:=22726) (PopulationFees20258.tabulate (22726-1) 256) source001.plan.table+
      4*22726*NaturalPopulation20258.weights source001.extras≤source001.plan.scale*94554870611 := by decide +kernel
private theorem range46From21853To2010 : Segment 46 21853 22726 0 2010 :=
  paid (pc:=78) (v:=94554870611) (by decide) source001_valid tests46_001_0 fee46_001_22726 (by decide +kernel)

private theorem tests46_002_2010 : ∀ z∈source002.plan.table,z.1.Valid 46 2010 := by decide +kernel
private theorem fee46_002_22726 :
    PopulationFees20258.bill (n:=22726) (PopulationFees20258.tabulate (22726-1) 256) source002.plan.table+
      4*22726*NaturalPopulation20258.weights source002.extras≤source002.plan.scale*168480692001 := by decide +kernel
private theorem range46From21853To2069 : Segment 46 21853 22726 2010 2069 :=
  paid (pc:=78) (v:=168480692001) (by decide) source002_valid tests46_002_2010 fee46_002_22726 (by decide +kernel)

private theorem range46From21853To2071 : Segment 46 21853 22726 2069 2071 :=
  paid (pc:=78) (v:=168480692001) (by decide) source002_valid tests46_002_2069 fee46_002_22726 (by decide +kernel)

private theorem range46From21853 : Win 46 21853 22726 :=
  complete (by decide) (by decide) (join_population range46From21853To2010 (join_population range46From21853To2069 range46From21853To2071))

private theorem fee46_001_23880 :
    PopulationFees20258.bill (n:=23880) (PopulationFees20258.tabulate (23880-1) 256) source001.plan.table+
      4*23880*NaturalPopulation20258.weights source001.extras≤source001.plan.scale*103856465133 := by decide +kernel
private theorem range46From22727To2025 : Segment 46 22727 23880 0 2025 :=
  paid (pc:=78) (v:=103856465133) (by decide) source001_valid tests46_001_0 fee46_001_23880 (by decide +kernel)

private theorem tests46_002_2025 : ∀ z∈source002.plan.table,z.1.Valid 46 2025 := by decide +kernel
private theorem fee46_002_23880 :
    PopulationFees20258.bill (n:=23880) (PopulationFees20258.tabulate (23880-1) 256) source002.plan.table+
      4*23880*NaturalPopulation20258.weights source002.extras≤source002.plan.scale*184863771263 := by decide +kernel
private theorem range46From22727To2070 : Segment 46 22727 23880 2025 2070 :=
  paid (pc:=77) (v:=184863771263) (by decide) source002_valid tests46_002_2025 fee46_002_23880 (by decide +kernel)

private theorem range46From22727To2071 : Segment 46 22727 23880 2070 2071 :=
  paid (pc:=77) (v:=184863771263) (by decide) source002_valid tests46_002_2070 fee46_002_23880 (by decide +kernel)

private theorem range46From22727 : Win 46 22727 23880 :=
  complete (by decide) (by decide) (join_population range46From22727To2025 (join_population range46From22727To2070 range46From22727To2071))

private theorem range46From23881 : Win 46 23881 39999 :=
  short (by decide) (by decide)

theorem cut46From20258 : Win 46 20258 39999 :=
  (join_ground (join_ground range46From20258 (join_ground range46From20665 range46From21183)) (join_ground range46From21853 (join_ground range46From22727 range46From23881)))

end JSP233.FiniteCutRanges20258
